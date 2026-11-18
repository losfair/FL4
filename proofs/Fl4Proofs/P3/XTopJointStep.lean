/-
P3 (DESIGN.md §9), CSpace: **`JAtZ` across the primitive steps, and the
CSpace side's cap leaves with `JAt` after** (the fold's family-level
preservation, in the shape of the SC family's `sched_controlJ_step`).

* `JAtZ.cs_frame`: a step that keeps the ghost sets, P1's heap and the cores
  (the MDB ghost `G` may change) and the kernel-state base keeps the sets'
  fields (`thT`, `ip`, `zH`, `c0`, `bound`, `ks`, `nk`) and, when every
  object's kind is kept (`KBack`), the spec objects' cover (`cover`, `obj`);
  the CSpace fields (`JCs`: `DelInv`, `UtInv`, `FinM`, `SpecFree`) and the
  rest (`JRest`) are its premises.
* `JCs.same`: a step keeping every slot (`SlotsSame`) and the objects' sizes
  (`KSz`) keeps the CSpace fields (`DelInv.of_same`, `UtInv.of_same`,
  `FinM.of_capV`, `SpecFree.frame`).
* `stepClosed_jat`, `Steps.jat`: `JAtZ` across a run of primitive steps
  (StepSem's `StepClosed`), from `JStepHyps`, the per-kind named premise:
  for each kind, at the step's post, `JRest` (and `JCs` for the kinds
  changing slots: an insertion, a CNode-only step; a notification cap's
  deletion owes, besides, its MDB ghost with `XTopAt` and `KBack`).
  Discharged here: the restart, a
  kernel-state step and a scheduler step keep every slot (the TCB state
  word, the kernel-state block, the scheduler's words are outside the slots)
  and the objects' kinds and sizes, so `JCs` and the covers; the insertion
  and the CNode-only step keep the kinds (`KeepC`), so the covers.
* `decode_invocation_{irq_control, ioport_control, irq_handler}J_step`: the
  three `Steps`-producing cap leaves, `JAt` after (`XCap` at `JAt`), the
  decode errors at the start's `JAtZ`.
* `XCap.jat` and `decode_invocation_{cnode, thread, ioport}J_step`: the
  leaves whose post is not a `Steps` run, with the per-op named premise
  `JPostHyp` (at the decode's post, over the spec's outcome: `JAt`),
  the unchanged states (decode errors) discharged by the start's `JAtZ`.
-/
import Fl4Proofs.P3.XTopJoint
import Fl4Proofs.P3.ScJointFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## The objects' kinds kept -/

section Spec
open Fl4Spec

/-- **Every object after was one of the same kind before** (for the kinds
the covers read). -/
def KBack (σ σ' : State Unit) : Prop :=
  ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧
    ((∃ x, ko' = .notification x) → ∃ x, ko = .notification x) ∧
    ((∃ x, ko' = .endpoint x) → ∃ x, ko = .endpoint x) ∧ ((∃ x, ko' = .reply x) → ∃ x, ko = .reply x) ∧
    ((∃ x, ko' = .tcb x) → ∃ x, ko = .tcb x) ∧ ((∃ x n, ko' = .schedContext x n) → ∃ x n, ko = .schedContext x n) ∧
    ((∃ x, ko' = .archObj x) → ∃ x, ko = .archObj x)

theorem KBack.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : KBack σ σ' := by
  intro o ko' ho
  rw [h] at ho
  exact ⟨ko', ho, id, id, id, id, id, id⟩

theorem KBack.of_keepC {σ σ' : State Unit} (h : KeepC σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h o with e | ⟨r, cs, cs', h1, h2⟩
  · rw [e] at ho; exact ⟨ko', ho, id, id, id, id, id, id⟩
  · rw [h2] at ho; cases ho
    refine ⟨_, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- A TCB replaced by a TCB, the rest of the heap kept. -/
theorem kback_ksz_upd {σ σ' : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (he : σ'.kheap = Function.update σ.kheap p (some (.tcb y))) : KBack σ σ' ∧ KSz σ σ' := by
  refine ⟨fun o ko' ho => ?_, fun o ko' ho => ?_⟩
  · rw [he] at ho
    by_cases e : o = p
    · subst e; rw [Function.update_self] at ho; cases ho
      refine ⟨_, hk, ?_, ?_, ?_, fun _ => ⟨x, rfl⟩, ?_, ?_⟩ <;> simp
    · rw [Function.update_of_ne e] at ho; exact ⟨ko', ho, id, id, id, id, id, id⟩
  · rw [he] at ho
    by_cases e : o = p
    · subst e; rw [Function.update_self] at ho; cases ho; exact ⟨_, hk, rfl⟩
    · rw [Function.update_of_ne e] at ho; exact ⟨ko', ho, rfl⟩

theorem Sched.SpecCover.kback {H : P1.Heap} {σ σ' : State Unit} (h : Sched.SpecCover H σ) (hK : KBack σ σ') :
    Sched.SpecCover H σ' := by
  refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun y k ho => ?_, fun o ao ho => ?_⟩
  · obtain ⟨ko, hk, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ntfn o x0 hk
  · obtain ⟨ko, hk, -, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ep o x0 hk
  · obtain ⟨ko, hk, -, -, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.reply o x0 hk
  · obtain ⟨ko, hk, -, -, -, -, h1, -⟩ := hK _ _ ho
    obtain ⟨y0, k0, rfl⟩ := h1 ⟨y, k, rfl⟩; exact h.sc0 y0 k0 hk
  · obtain ⟨ko, hk, -, -, -, -, -, h1⟩ := hK _ _ ho
    obtain ⟨a0, rfl⟩ := h1 ⟨ao, rfl⟩; exact h.arch o a0 hk

theorem Sched.ObjCover.kback {N T E R C : Set U64} {σ σ' : State Unit} (h : Sched.ObjCover N T E R C σ)
    (hK : KBack σ σ') : Sched.ObjCover N T E R C σ' := by
  refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o y k ho => ?_⟩
  · obtain ⟨ko, hk, -, -, -, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.tcb o x0 hk
  · obtain ⟨ko, hk, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ntfn o x0 hk
  · obtain ⟨ko, hk, -, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ep o x0 hk
  · obtain ⟨ko, hk, -, -, h1, -⟩ := hK o _ ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.reply o x0 hk
  · obtain ⟨ko, hk, -, -, -, -, h1, -⟩ := hK o _ ho
    obtain ⟨y0, k0, rfl⟩ := h1 ⟨y, k, rfl⟩; exact h.sc o y0 k0 hk

end Spec

/-! ## The frame -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The CSpace fields of `JAtZ`** at a state. -/
structure JCs (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  del : DelInv Z.th (L.mem s)
  ut : UtInv (L.mem s) Z.G
  finM : ∀ G, MdbLinks Z.th (L.mem s) G → FinM (L.mem s) G
  sfree : Sched.SpecFree (L.mem s) Z.G σ

variable (arI) in
/-- **The fields of `JAtZ` a step re-establishes** (the per-kind and per-op
named premises' conclusion): the call stacks, yield, MCP, buffer words,
reply placement, slots apart, `JPlaced`, the dead set, `JKern`, the untyped
caps' facts, the scheduler invariants (`CurInv` unless a reschedule is
pending, `CurOwn`, the sorted IPC queues; `SchedValid` and the spec's links
rebuilt, `schedValid_rebuild`, `scLink_rebuild`), P1's `BlkOK`. -/
structure JRest (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop where
  call : Sched.CallRel (L.mem s) Z.R Z.C σ Lst
  rfree : Sched.RFree (L.mem s) Z.R Z.C σ Lst
  yld : Sched.YieldRel Z.T Z.C (L.mem s) σ
  mcp : Sched.McpRel Z.T (L.mem s) σ
  buf : BufWordRel Z.T (L.mem s) σ
  rp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s σ
  apart : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s σ
  jpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s σ
  jcov : Sched.JCovD (L := L) Z.th H Z.G D Cs s
  kern : JKern (L := L) H Cs D Z.th s σ
  utc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    Sched.UtCapP3 (L := L) arI Z.th s σ Z.G sl p sb fi
  nsc : Sched.NSC Z.N Z.C σ
  inv : Sched.Inv σ
  cur : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ
  own : Sched.CurOwnW Z.T Z.C σ
  off : Sched.OffOK σ
  act : Sched.ActIdle σ
  bsa : Sched.BlockedScActive σ
  isorted : Sched.IpcSorted σ
  curRun : CurRunM σ
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` across a CSpace-shaped step** (module docstring). -/
theorem JAtZ.cs_frameV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : Set U64 × Set U64 × Set U64 × Set U64 × Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hkb : KBack σ σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ') :
    JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' :=
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.kback hkb) R.blk J.hset.2.1 R.jpl J.c0
  ⟨hX, R.call, R.rfree, R.yld, R.mcp, R.buf, by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, R.rp, R.apart,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, R.jpl, J.cover.kback hkb, J.obj.kback hkb, J.zH, hC.sfree, J.hset, R.jcov,
    R.kern, hC.del, hC.ut, J.bound, hC.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act, J.c0, R.bsa,
    schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.kback hkb) R.blk J.hset.1 J.hset.2.1 R.call R.yld J.c0 R.inv
      hsl, R.isorted, hsl, R.curRun, R.blk, by rw [hks]; exact J.intL⟩

/-- `cs_frameV` at the same VSpace sets. -/
theorem JAtZ.cs_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR { Z with G := G' } s' a' σ') (hkb : KBack σ σ')
    (hC : JCs (L := L) { Z with G := G' } s' σ') (R : JRest (L := L) arI { Z with G := G' } H Cs Ac' Lst' D' s' σ') :
    JAtZ (L := L) arI AR { Z with G := G' } H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameV (V' := Z.vs) hks hX hkb hC R

/-- **The CSpace fields across a step keeping every slot and the objects'
sizes** (module docstring). -/
theorem JCs.same {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hk : KSz σ σ') : JCs (L := L) Z s' σ' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  refine ⟨J.del.of_same hSS, UtInv.of_same hM J.ut hSS, fun G hG => ?_, ?_⟩
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', d, ?_, le_rfl⟩) hk
    rw [← hSS.capV (hsl x' hx')]; exact hc

end

/-! ## The step closure -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What a step keeping the MDB ghost owes** (the per-kind premise's
shape): at the step's post, for every `JAtZ` before at the typed heap and
`XTopAt` after at the same sets, `JRest` after. -/
def JOwes (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR Z s' a' σ' →
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JRest (L := L) arI Z H Cs Ac' Lst' D' s' σ'

/-- `JOwes` for a step with the MDB ghost `G'` after, with the CSpace fields
(the kinds changing slots). -/
def JOwesCs (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (G' : MdbGhost) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR { Z with G := G' } s' a' σ' →
    JCs (L := L) { Z with G := G' } s' σ' ∧
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JRest (L := L) arI { Z with G := G' } H Cs Ac' Lst' D' s' σ'

/-- **The per-kind named premise of `JAtZ`'s step closure** [W]: for each
primitive step (StepSem's `StepClosed`), what it owes (`JOwes`; with the
CSpace fields, `JOwesCs`, for an insertion and a CNode-only step). A
notification cap's deletion owes all of `JAtZ` but the kept fields: an MDB
ghost after with `XTopAt` (as `XDelNtfnHyp`, `xDelNtfnHyp_of`), the
kernel-state base and the objects' kinds kept, `JCs` and `JRest`. -/
structure JStepHyps (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  restart : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (ct : U64) (x : Fl4Spec.Tcb) (s1 : S),
    σ.curThread = ct.bv → σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    Fl4Spec.runnable x.tcbState = true → sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    JOwes (L := L) arI AR th s a σ s1 a (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)
  ks : ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit), P1.WritesIn st s s' (KsW (L.ksb s)) → KsStep σ σ' →
    DK4 (L := L) s s' → σ'.domainList = σ.domainList → σ'.domainStartIndex = σ.domainStartIndex →
    (IrqRel (L.mem s) (L.ksb s) σ → IrqRel (L.mem s') (L.ksb s) σ') →
    (IoRel (L.mem s) (L.ksb s) σ → IoRel (L.mem s') (L.ksb s) σ') →
    ArchIrqStep arI a a' → JOwes (L := L) arI AR th s a σ s' a' σ'
  slot : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G' : MdbGhost) (c : Fl4Spec.Cap) (ps pd : U64)
    (rs rd : Nat) (idxs idxd : List Bool), th ps = some (.cnode rs) → th pd = some (.cnode rd) →
    Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) →
    idxd.length = rd → (∀ y, IsSlot th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y) →
    capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null →
    (∀ p sb fi d, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Untyped p sb fi d) →
    P1.WritesIn st s s' (InSlot th) → CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' →
    MdbOKV (L.ksb s) (L.mem s') G' →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) →
    TypedKept th (L.mem s) (L.mem s') →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3)) →
    DestLive th (L.mem s) (L.ksb s) pd →
    (DelInv th (L.mem s) → DelInv th (L.mem s')) → JOwesCs (L := L) arI AR th G' s a σ s' a σ'
  sched : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit), SchedStep (L := L) th s σ s' σ' →
    JOwes (L := L) arI AR th s a σ s' a σ'
  cslot : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G' : MdbGhost), Ipc.CnK σ σ' →
    (∀ p, σ'.kheap p = σ.kheap p ∨
      ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) →
    CoverKept th (L.mem s) (L.mem s') → UtKept th (L.mem s) (L.mem s') →
    (∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot th sl) →
    P1.WritesIn st s s' (InSlot th) → CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' →
    MdbOKV (L.ksb s) (L.mem s') G' →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) →
    TypedKept th (L.mem s) (L.mem s') →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3)) →
    KSz σ σ' → (DelInv th (L.mem s) → DelInv th (L.mem s')) → ∀ W : List Fl4Spec.CslotPtr,
    (∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ th p = some (.cnode r) ∧ sl.2.length = r ∧ DestLive th (L.mem s) (L.ksb s) p) →
    (∀ y, IsSlot th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y) →
    (∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W) →
    UtSrc th (L.mem s) (L.mem s') σ σ' → JOwesCs (L := L) arI AR th G' s a σ s' a σ'
  del : ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
    AbsSlot th sl → (∃ q, sl.1 = q.bv ∧ th q = some (.cnode sl.2.length)) →
    capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
    cdt.delete_one st arI s a (cslotAddr sl) = ok (s', a') → ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → ∃ (G' : MdbGhost) (V' : XVs),
        XTopAt (L := L) AR (Z.mv G' V') s' a' σ' ∧ L.ksb s' = L.ksb s ∧ KBack σ σ' ∧
        JCs (L := L) (Z.mv G' V') s' σ' ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ'

/-- **`JAtZ`'s instance of `StepClosed`**: the ghost sets, P1's heap and the
cores kept, the MDB ghost, the active SCs, the call stacks and the dead set
chosen after. -/
def QJ (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ'

theorem schW_oobj {Z : XSets} {s : S} {σ : Fl4Spec.State Unit} (hT : P1.TcbPlaced Z.T) {b : U64}
    (h : SchW (L := L) Z.T Z.c s b) : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b := by
  rcases h with h | h | h
  · exact sfootI_oobj hT (Or.inl h)
  · exact sfootI_oobj hT (Or.inr h)
  · have := domKW_val h
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)

set_option maxHeartbeats 4000000 in
/-- **`JAtZ` is closed under the primitive steps** (module docstring). -/
theorem stepClosed_jat {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (hJ : JStepHyps (L := L) arI AR th) :
    StepClosed (L := L) arI th (QJ (L := L) arI AR th) := by
  refine ⟨fun s1 a1 σ1 s2 a2 σ2 s3 a3 σ3 h1 h2 Z H Cs Ac Lst D hth J => ?_,
    fun s a σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D hth J => ?_,
    fun s s' a a' σ σ' hw hO hdk hdl hds hirq hio harch Z H Cs Ac Lst D hth J => ?_,
    fun s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw hCR hFI hMO hTS hTK hT3 hDL hDl Z H Cs Ac Lst D hth J => ?_,
    fun s s' a σ σ' hS Z H Cs Ac Lst D hth J => ?_,
    fun s s' a σ σ' G' hcn hkc hCK hUK horig hw hCR hFI hMO hTS hTK hT3 hkz hDl W hW hcW hoW hUS Z H Cs Ac Lst D hth J => ?_,
    fun s s' a a' σ σ' sl p b w r hA hcn hc hd hm Z H Cs Ac Lst D hth J => ?_⟩
  · obtain ⟨G1, V1, Ac1, Lst1, D1, J1⟩ := h1 Z H Cs Ac Lst D hth J
    obtain ⟨G2, V2, Ac2, Lst2, D2, J2⟩ := h2 (Z.mv G1 V1) H Cs Ac1 Lst1 D1 hth J1
    exact ⟨G2, V2, Ac2, Lst2, D2, J2⟩
  · -- the restart: the TCB state word
    subst hth
    have hX := J.xtop
    have h := XTopAt.restart hX hcur hk hrun
    rw [hs1, WP.spec_ok] at h
    obtain ⟨hX1, hSS, hk1⟩ := h
    obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
      (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
    obtain ⟨Ac', Lst', D', R⟩ := hJ.restart s a σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D rfl J hX1
    exact ⟨Z.G, Z.vs, Ac', Lst', D', J.cs_frame hk1 hX1 hkb (JCs.same J hSS hkz) R⟩
  · -- a kernel-state step: the kernel-state block's words
    subst hth
    have hX := J.xtop
    have hD := hX.rel.2.2.2.1
    have hAR := hX.fin.1.1.2.2.2.2.2.2
    have hX1 : XTopAt (L := L) AR Z s' a' σ' := XTopAt.ksStep hX J.ks hw hO (hirq hX.fin.1.1.2.2.2.1)
      (hio hX.fin.1.1.2.2.2.2.1) (hD.frame (fun o ho => hdk.2 o ho) hdl hds)
      (by rw [hO.cr3]; exact hAM _ _ _ hAR harch)
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
      hX.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    obtain ⟨Ac', Lst', D', R⟩ := hJ.ks s s' a a' σ σ' hw hO hdk hdl hds hirq hio harch Z H Cs Ac Lst D rfl J hX1
    exact ⟨Z.G, Z.vs, Ac', Lst', D', J.cs_frame hw.1 hX1 (KBack.of_kheap hO.kh) (JCs.same J hSS (KSz.of_kheap hO.kh)) R⟩
  · -- an insertion
    subst hth
    have hX := J.xtop
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [hci]; rfl
    have hcn := capInsert_nkn c _ _ σ _ hmem
    have hSt := hX.rel.2.1.1
    have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko c _ _ σ _ hmem) (by
      rintro p (rfl | hp)
      · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
    have hPl := hX.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    have hX1 := XTopAt.slotStep hX hw' hcn hkc hCR hFI hMO hTS
    obtain ⟨hC, Ac', Lst', D', R⟩ :=
      hJ.slot s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw hCR hFI hMO hTS hTK hT3 hDL hDl Z H Cs Ac Lst D rfl J hX1
    exact ⟨G', Z.vs, Ac', Lst', D', J.cs_frame hw.1 hX1 (KBack.of_keepC hkc) hC R⟩
  · -- a scheduler step: the scheduler's words
    subst hth
    have hX := J.xtop
    have hX1 := hX.schedStep J.ks J.thT hS
    have hW := (hS.2.1 Z.N Z.T Z.C Z.c J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
      hX.slotsSame_of hW fun b hb => schW_oobj hX.fin.1.1.1.placed.tcb hb
    obtain ⟨Ac', Lst', D', R⟩ := hJ.sched s s' a σ σ' hS Z H Cs Ac Lst D rfl J hX1
    exact ⟨Z.G, Z.vs, Ac', Lst', D', J.cs_frame hW.1 hX1 (KBack.of_kheap hS.1.kh)
      (JCs.same J hSS (KSz.of_kheap hS.1.kh)) R⟩
  · -- a CNode-only step
    subst hth
    have hX := J.xtop
    have hPl := hX.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    have hX1 := XTopAt.slotStep hX hw' hcn hkc hCR hFI hMO hTS
    obtain ⟨hC, Ac', Lst', D', R⟩ := hJ.cslot s s' a σ σ' G' hcn hkc hCK hUK horig hw hCR hFI hMO hTS hTK hT3 hkz hDl W hW hcW hoW hUS Z H Cs Ac Lst D rfl J hX1
    exact ⟨G', Z.vs, Ac', Lst', D', J.cs_frame hw.1 hX1 (KBack.of_keepC hkc) hC R⟩
  · -- a notification cap's deletion
    obtain ⟨G', V', hX1, hks, hkb, hC, Ac', Lst', D', R⟩ := hJ.del s s' a a' σ σ' sl p b w r hA hcn hc hd hm Z H Cs Ac Lst D
      hth J
    exact ⟨G', V', Ac', Lst', D', J.cs_frameV hks hX1 hkb hC R⟩

/-- **`JAtZ` after a run of primitive steps.** -/
theorem Steps.jat {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (hJ : JStepHyps (L := L) arI AR th) {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (h : Steps (L := L) arI th s a σ s' a' σ') {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (hth : Z.th = th)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JAt (L := L) arI AR s' a' σ' :=
  let ⟨_, _, Ac', Lst', D', J'⟩ := h _ (stepClosed_jat arI hAM hJ) Z H Cs Ac Lst D hth J
  ⟨_, H, Cs, Ac', Lst', D', J'⟩

theorem JAt.xtop {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JAt (L := L) arI AR s a σ) : XTop (L := L) AR s a σ :=
  let ⟨Z, _, _, _, _, _, J⟩ := h
  ⟨Z, J.xtop⟩

/-! ## The `Steps`-producing cap leaves, `JAt` after -/

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The IRQ control cap, `JAt` after** (`decode_invocation_irq_controlJAt`'s
premises and `JStepHyps` [W]). -/
theorem decode_invocation_irq_controlJ_step (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hHA : HandlersActive (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact decode_invocation_irq_controlXS arI Z.th s ar σ Z.G (hG.lay Z s ar σ rfl hX).1 hHA lbl slbl hlbl hrm length
    buf ct hct args hlen hargs hcur J.kern.act hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA
    (maskIrq_total arI hT) hAR rfl rfl hX (J.curRun.run hni) _ ⟨Z, H, Cs, Ac, Lst, D, J⟩
    (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J) (fun _ _ _ h => JAt.xtop arI h)
    blk call don fp ci buffer

set_option maxHeartbeats 4000000 in
/-- **The IO port control cap, `JAt` after**
(`decode_invocation_ioport_controlJAt`'s premises and `JStepHyps` [W]). -/
theorem decode_invocation_ioport_controlJ_step (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact decode_invocation_ioport_controlXS arI Z.th s ar σ Z.G (hG.lay Z s ar σ rfl hX).2 hPA lbl slbl hlbl length
    buf ct hct args hlen hargs hcur J.kern.act hact3 extra x0 hx0 excaps hex hps hls hsrcC rfl rfl hX (J.curRun.run hni) _
    ⟨Z, H, Cs, Ac, Lst, D, J⟩ (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J)
    (fun _ _ _ h => JAt.xtop arI h) blk call don fp ci buffer

set_option maxHeartbeats 4000000 in
/-- **An IRQ handler cap, `JAt` after** (`decode_invocation_irq_handlerJAt`'s
premises and `JStepHyps` [W]). -/
theorem decode_invocation_irq_handlerJ_step (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hO : FinObjHyp (L := L) arI Z.th) (hPD : PostDelHyp (L := L) arI Z.th) (hK : NtfnKeepHyp (L := L) arI Z.th)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (irq : U64) (hsc : capV (L.mem s) (cslotAddr sl) = .IrqHandler irq)
    (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel Z.th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) Z.th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    (length buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IrqHandler irq) blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hirq : irq.val < 128 := (slot_cap_wf hX hAs hsc).1
  exact decode_invocation_irq_handlerXS arI Z.th hX.rel.1 hO hPD hK s ar σ Z.G J.dstate (hG.lay Z s ar σ rfl hX).1
    hX.fin.1.1.2.2.2.1 lbl slbl hlbl ct hct hcur (hX.curTcb hcur).1 J.kern.act (maskIrq_total arI hT) irq hirq hok
    extra x0 hx0 excaps hex hxn hX.rel.2.2.2.2.1 hD hP1 rfl hX (J.curRun.run hni) _ ⟨Z, H, Cs, Ac, Lst, D, J⟩
    (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J) (fun _ _ _ h => JAt.xtop arI h)
    length (cslotAddr sl) buf blk call don fp args ci sl buffer

/-! ## The other cap leaves: the per-op named premise -/

/-- **The spec's state after a decode and its invocation** (the outcomes of
`TopPostDMX`/`TopPostRMX`, for FL4's outcome `r` from `s`): unchanged when
FL4's decode fails (the FL4 state kept), or after the restart and the
invocation, with the reply's tail. -/
def SpecOut (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (blk call don : Bool) (ct : U64) (s : S)
    (r : core.result.Result Unit error.Exc × S × A) (σ σ' : Fl4Spec.State Unit) : Prop :=
  ((∃ e, r.1 = .Err e) ∧ r.2.1 = s ∧ σ' = σ) ∨ ∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ((∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, y.2 = σ') ∨
      ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1 ∧
        ∃ z ∈ (specTail call ct.bv rr σy).1, z.2 = σ')

/-- **The per-op named premise** [W] (the uniform shape of
`sched_controlJ_step`'s `hRest`): at the decode's post, every spec outcome
(`SpecOut`) related by `XTop` and differing from the start has `JAt`. -/
def JPostHyp (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r => ∀ σ',
    SpecOut (specDec fp slbl args ci sl c excaps buffer) blk call don ct s r σ σ' → XTop (L := L) AR r.2.1 r.2.2 σ' →
    ¬ (r.2.1 = s ∧ r.2.2 = ar ∧ σ' = σ) → JAt (L := L) arI AR r.2.1 r.2.2 σ' ⦄

theorem jat_of_post {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    {P : Fl4Spec.State Unit → Prop} {r : core.result.Result Unit error.Exc × S × A}
    (hr : ∀ σ', P σ' → XTop (L := L) AR r.2.1 r.2.2 σ' → ¬ (r.2.1 = s ∧ r.2.2 = ar ∧ σ' = σ) →
      JAt (L := L) arI AR r.2.1 r.2.2 σ')
    {σ' : Fl4Spec.State Unit} (hP : P σ') (hX : XTop (L := L) AR r.2.1 r.2.2 σ') : JAt (L := L) arI AR r.2.1 r.2.2 σ' := by
  by_cases e : r.2.1 = s ∧ r.2.2 = ar ∧ σ' = σ
  · obtain ⟨e1, e2, e3⟩ := e
    rw [e1, e2, e3]; exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
  · exact hr σ' hP hX e

/-- **`XCap` at `XTop` gives it at `JAt`** with the per-op premise
(`JPostHyp`), the unchanged states by the start's `JAtZ`. -/
theorem XCap.jat {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps
      buffer ct) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps
      buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono (WP.spec_and h hR) ?_)
    rintro r ⟨hq, hr⟩
    rcases hq with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
    · exact Or.inl ⟨e, h1, h2, h3, jat_of_post arI J hr (Or.inl ⟨⟨e, h1⟩, h2, rfl⟩) h4⟩
    · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, h3,
        jat_of_post arI J hr (Or.inr ⟨inv, h1, σ1, h2, Or.inl ⟨y, hy, rfl⟩⟩) h4⟩
  · refine Or.inr (WP.spec_mono (WP.spec_and h hR) ?_)
    rintro r ⟨hq, hr⟩
    rcases hq with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
    · exact Or.inl ⟨e, h1, h2, h3, jat_of_post arI J hr (Or.inl ⟨⟨e, h1⟩, h2, rfl⟩) h4⟩
    · exact Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6,
        jat_of_post arI J hr (Or.inr ⟨inv, h3, σ1, h4, Or.inr ⟨rr, σy, h5, z, hz, rfl⟩⟩) h7⟩

set_option maxHeartbeats 4000000 in
/-- **`decode_invocation_cnodeJAt`, `JAt` after**, with the per-op premise (`JPostHyp` [W]). -/
theorem decode_invocation_cnodeJ_step [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hrun : ∀ xt, σ.kheap ct.bv = some (.tcb xt) → tsCode xt.tcbState < 3)
    (hZ : ∀ Z' : XSets, XTopAt (L := L) AR Z' s ar σ → KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s) ∧
      BufWordRel Z'.T (L.mem s) σ ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hQ : ∀ e, Sched.EpQPre σ e)
    (hE : ∀ (Z' : XSets) (e b : U64) (sl : Fl4Spec.CslotPtr), XTopAt (L := L) AR Z' s ar σ → AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z'.E)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct :=
  XCap.jat arI (decode_invocation_cnodeJAt arI s ar σ J hni hG hARI hT lbl slbl hlbl length buf ct hct args hlen hargs sl hAs p r gs g hsc extra x0 x1 hx0 hx1 excaps hex hrun hZ hQ hE blk call don fp ci buffer) J hR


set_option maxHeartbeats 4000000 in
/-- **The domain cap, `JAt` after**: its decode's scheduler and kernel-state
steps (`decode_invocation_domainXS`, `DomSetHyp`/`DomResHyp` from `XTopAt`,
`ActReady` from `Inv`), `Steps.jat` with `JStepHyps`; the kernel-state
words' placement as `decode_invocation_domainXT`'s. -/
theorem decode_invocation_domainJ_step (hcfg : DomConfig) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hJ : JStepHyps (L := L) arI AR Z.th)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel Z.th (L.mem s) x0 excs)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hP := hX.fin.1.2
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hC := J.curRun.run hni
  have hA : Notif.ActReady σ := J.inv.actReady
  exact decode_invocation_domainXS arI hcfg Z.th hX.rel.1 s ar σ Z.G hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 ct hct
    hcur (hX.curTcb hcur).1 J.kern.act hkf hP.vs.ksb_al hksO hactK lbl slbl hlbl length buf args hlen hargs extra x0
    hx0 excs hex (domSetHyp_of hX J.thT hC hA hcur) (domResHyp_of hX J.ks J.thT hC hA hcur)
    (domStallHyp_of arI hX.fin.1.1.1 J.thT) hC ⟨Z, H, Cs, Ac, Lst, D, J⟩ (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J) (fun _ _ _ h => JAt.xtop arI h)
    slot blk call don fp ci sl buffer

set_option maxHeartbeats 4000000 in
/-- **`decode_invocation_threadJAt`, `JAt` after**, with the per-op premise (`JPostHyp` [W]). -/
theorem decode_invocation_threadJ_step [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hOK : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ')
    (hBC : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ')
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (hFl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ')
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFpu : FpuRelXHyp (L := L) arI AR Z.th p ct)
    (hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don)
    (hFr : ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass true offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset))
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct :=
  XCap.jat arI (decode_invocation_threadJAt arI s ar σ J hni hG hARI hT hA hBT hOK hBC hBPl hFl lbl length p blk call don fp buf extra ct hct slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hstall' hNative hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0 hcapC hA5 hGb hFpu hI hFr) J hR

set_option maxHeartbeats 4000000 in
/-- **`decode_invocation_ioportJAt`, `JAt` after**, with the per-op premise (`JPostHyp` [W]). -/
theorem decode_invocation_ioportJ_step [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (first last : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .IoPort first last 0#u64) (call : Bool)
    (hval : call = true → PortInVal arI)
    (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hR : JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct :=
  XCap.jat arI (decode_invocation_ioportJAt arI s ar σ J hni hG hARI hT lbl slbl hlbl length buf ct hct args hlen hargs sl hAs first last hsc call hval blk don fp extra ci excaps buffer) J hR

set_option maxHeartbeats 4000000 in
/-- **An IO port cap, `JAt` after**: `Out`, the errors and the other labels by
their primitive steps (`decode_invocation_ioportXS`, `Steps.jat` with
`JStepHyps`), the per-op premise (`JPostHyp` [W]) only at `In` (64..66,
whose reply writes the caller's message words). -/
theorem decode_invocation_ioportJ_steps [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hJ : JStepHyps (L := L) arI AR Z.th)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (first last : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .IoPort first last 0#u64) (call : Bool)
    (hval : call = true → PortInVal arI)
    (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hR : 64 ≤ lbl.val ∧ lbl.val ≤ 66 → JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl)
      (.IoPort first last 0#u64) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hI : 64 ≤ lbl.val ∧ lbl.val ≤ 66
  · exact XCap.jat arI (decode_invocation_ioportJAt arI s ar σ J hni hG hARI hT lbl slbl hlbl length buf ct hct args
      hlen hargs sl hAs first last hsc call hval blk don fp extra ci excaps buffer) J (hR hI)
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨⟨-, hl, hfl⟩, -⟩ := slot_cap_wf hX hAs hsc
  have hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a' := by
    intro a p z d
    obtain ⟨a', h, -⟩ := spec_exists (hT.port_out a p z d)
    exact ⟨a', h⟩
  exact decode_invocation_ioportXS arI Z.th hX.rel.1 s ar σ lbl slbl hlbl length buf ct hct args hlen hargs hcur
    (hX.curTcb hcur).1 J.kern.act first last hfl (by simpa using hl) call hout rfl hX (J.curRun.run hni)
    ⟨Z, H, Cs, Ac, Lst, D, J⟩ (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J) (fun _ _ _ h => JAt.xtop arI h)
    (cslotAddr sl) blk don fp extra ci sl excaps buffer (fun h => absurd h hI)

end

end

end Fl4Proofs.P3
