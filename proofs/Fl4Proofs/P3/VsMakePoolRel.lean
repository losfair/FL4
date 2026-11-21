/-
P3 (DESIGN.md §9), VSpace: **ASIDControl `MakePool` refines l4v**
(`perform_asid_control_invocation`, after `decode_asid_control_invocation`).

FL4 (after the decode checks): `set_thread_state Restart`, the untyped cap's
free index set to its size, the frame zeroed, the pool cap linked as the
untyped cap's child (`cdt::insert`), the ASID-table entry set. l4v:
`set_thread_state Restart`, `delete_objects` of the frame, the untyped cap's
free index set to its size, `retype_region` of an empty `ASIDPool`,
`cap_insert`, the table entry.

* `delete_objects` is matched by restricting the ghost typed heap to outside
  the frame (`restrictTh`, `detype_rel`), as for the untyped reset; the
  untyped cap has no children (the decode checked), and the hypotheses on
  the frame are the reset's (no CNode, linked slot or straddling object in
  it) plus: the ASID table, the pools and the page tables are outside it, and
  their words outside the typed heap's objects.
* the CSpace relations and `MdbInv` (`InsACtx.inv`) and `UtInv`
  (`utinv_pool`) for the grown ghost tree; the ASID relation with the new
  pool (`VsRel.add_pool`); the page-table relation unchanged.
* the rest of the state relation, `SR`, is kept by `MakePool`'s writes
  (`MpW`: slot words, the frame, the table word; `insert_frame2`) and spec
  change (`MpStep`: an `OStep` with the frame as region, memory outside the
  frame kept; `deleteObjects_mem`), given what `SR` needs of the frame
  (`RegOK`): hypothesis `mpSR`, discharged for the composite relation in
  VsTop (`mpSR_top`).

`mp_perform_rel` is the perform from the state after the decode checks;
`makepool_rel` the whole decode and perform.
-/
import Fl4Proofs.P3.VsMakePoolSpec
import Fl4Proofs.P3.VsMakePoolMdb
import Fl4Proofs.P3.IntFrame
import Fl4Proofs.P3.VsInsFrame
import Fl4Proofs.P3.UntypedPml4
import Fl4Proofs.P3.VsMdb
import Fl4Proofs.P3.FinFrame
import Fl4Proofs.P3.VsFrameInv
import Fl4Proofs.P3.VsCapOps
import Fl4Proofs.P3.VsMdbInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

/-! ## Spec steps that keep the other subsystems' state -/

section OSpec
open Fl4Spec

/-- A heap cell the other subsystems' relations do not read: free, a CNode
or an arch object. -/
def Passive (o : Option KernelObject) : Prop :=
  o = none ∨ (∃ r cs, o = some (.cnode r cs)) ∨ (∃ ao, o = some (.archObj ao))

/-- A spec step that keeps what the other subsystems' relations read, but in
a region `Rg` of the heap. -/
structure OStep (Rg : ObjRef → Prop) (σ σ' : State Unit) : Prop where
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  act : σ'.schedulerAction = σ.schedulerAction
  csc : σ'.curSc = σ.curSc
  ctime : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  repr : σ'.reprogramTimer = σ.reprogramTimer
  cdom : σ'.curDomain = σ.curDomain
  dtime : σ'.domainTime = σ.domainTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  ist : σ'.interruptStates = σ.interruptStates
  inode : σ'.interruptIrqNode = σ.interruptIrqNode
  io : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts
  gpml4 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4
  kh : ∀ q, σ'.kheap q ≠ σ.kheap q → (Rg q ∨ Passive (σ.kheap q)) ∧ Passive (σ'.kheap q)

theorem OStep.keep {Rg : ObjRef → Prop} {σ σ' : State Unit} (h : OStep Rg σ σ') {q : ObjRef}
    (hq : ¬ Rg q) (hp : ¬ Passive (σ.kheap q)) : σ'.kheap q = σ.kheap q := by
  by_contra e
  rcases (h.kh q e).1 with h1 | h1
  · exact hq h1
  · exact hp h1

theorem OStep.keep' {Rg : ObjRef → Prop} {σ σ' : State Unit} (h : OStep Rg σ σ') {q : ObjRef}
    (hp : ¬ Passive (σ'.kheap q)) : σ'.kheap q = σ.kheap q := by
  by_contra e
  exact hp (h.kh q e).2

theorem OStep.trans {Rg Rg' : ObjRef → Prop} {σ1 σ2 σ3 : State Unit} (h1 : OStep Rg σ1 σ2) (h2 : OStep Rg' σ2 σ3) :
    OStep (fun q => Rg q ∨ Rg' q) σ1 σ3 := by
  refine ⟨h2.rq.trans h1.rq, h2.rel.trans h1.rel, h2.ct.trans h1.ct, h2.act.trans h1.act, h2.csc.trans h1.csc,
    h2.ctime.trans h1.ctime, h2.cons.trans h1.cons, h2.repr.trans h1.repr, h2.cdom.trans h1.cdom,
    h2.dtime.trans h1.dtime, h2.idle.trans h1.idle, h2.isc.trans h1.isc, h2.ist.trans h1.ist, h2.inode.trans h1.inode,
    h2.io.trans h1.io, h2.gpml4.trans h1.gpml4, fun q hq => ?_⟩
  by_cases e1 : σ2.kheap q = σ1.kheap q
  · have e2 : σ3.kheap q ≠ σ2.kheap q := by rw [e1]; exact hq
    obtain ⟨a, b⟩ := h2.kh q e2
    rw [e1] at a
    exact ⟨a.imp Or.inr id, b⟩
  · obtain ⟨a, b⟩ := h1.kh q e1
    refine ⟨a.imp Or.inl id, ?_⟩
    by_cases e2 : σ3.kheap q = σ2.kheap q
    · rw [e2]; exact b
    · exact (h2.kh q e2).2

theorem OStep.mono {Rg Rg' : ObjRef → Prop} {σ σ' : State Unit} (h : OStep Rg σ σ') (hr : ∀ q, Rg q → Rg' q) :
    OStep Rg' σ σ' :=
  ⟨h.rq, h.rel, h.ct, h.act, h.csc, h.ctime, h.cons, h.repr, h.cdom, h.dtime, h.idle, h.isc, h.ist, h.inode, h.io, h.gpml4,
    fun q hq => ⟨(h.kh q hq).1.imp (hr q) id, (h.kh q hq).2⟩⟩

theorem passive_tcb {x : Tcb} : ¬ Passive (some (.tcb x)) := by
  rintro (h | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h
theorem passive_ep {x : Endpoint} : ¬ Passive (some (.endpoint x)) := by
  rintro (h | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h
theorem passive_ntfn {x : Notification} : ¬ Passive (some (.notification x)) := by
  rintro (h | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h
theorem passive_reply {x : Reply} : ¬ Passive (some (.reply x)) := by
  rintro (h | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h
theorem passive_sc {x : SchedContext} {n : Nat} : ¬ Passive (some (.schedContext x n)) := by
  rintro (h | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h

theorem OStep.cnode {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    (hk : σ.kheap p = some (.cnode r cs)) (idx : List Bool) (a : Fl4Spec.Cap) :
    OStep (fun _ => False) σ (setCnodeSlot σ p r cs idx a) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q hq => ?_⟩
  by_cases e : q = p
  · subst e
    exact ⟨Or.inr (Or.inr (Or.inl ⟨r, cs, hk⟩)), Or.inr (Or.inl ⟨r, Function.update cs idx (some a), by simp [setCnodeSlot]⟩)⟩
  · exact absurd (by simp [setCnodeSlot, e]) hq

theorem OStep.arch {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} (hk : Passive (σ.kheap p))
    (ao' : Fl4Spec.ArchKernelObj) :
    OStep (fun _ => False) σ (updK σ p (.archObj ao')) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q hq => ?_⟩
  by_cases e : q = p
  · subst e
    exact ⟨Or.inr hk, Or.inr (Or.inr ⟨ao', by simp⟩)⟩
  · exact absurd (by simp [e]) hq

theorem OStep.table {σ : Fl4Spec.State Unit} (t : Fl4Spec.AsidHighIndex → Option Fl4Spec.ObjRef) :
    OStep (fun _ => False) σ { σ with archState := { σ.archState with x64AsidTable := t } } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ hq => absurd rfl hq⟩

end OSpec

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The words `MakePool` writes: slot words of the typed heap, the pool's
frame `[p, p + 4096)`, and the ASID-table word `hi`. -/
def MpW (th : TypedHeap) (p ksb hi : U64) (b : U64) : Prop :=
  (∃ x k, IsSlot th x ∧ Off k ∧ b = wordOf x k) ∨ (p.val ≤ b.val ∧ b.val < p.val + 4096) ∨ b = atA ksb hi

/-- The spec change of `MakePool`: an `OStep` with the frame as region, the
memory outside the frame unchanged. -/
def MpStep (p : U64) (σ σ' : Fl4Spec.State Unit) : Prop :=
  OStep (fun q => q ∈ regionSet p.bv 12) σ σ' ∧
    (∀ x : Fl4Spec.Word, (x.toNat < p.val ∨ p.val + 4096 ≤ x.toNat) →
      σ'.machineState.underlyingMemory x = σ.machineState.underlyingMemory x) ∧
    σ'.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3

/-- The hypotheses of `MakePool` (see the module docstring). `RegOK s σ p`:
what `SR` needs of the frame (that it holds none of the other subsystems'
objects). -/
structure VsMpHyps (A : Type) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (RegOK : S → Fl4Spec.State Unit → U64 → Prop) : Prop where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), SR s a σ → VsRel P (L.mem s) (L.ksb s) σ →
    PtRel L4 L3 L2 L1 (L.mem s) σ → ct.bv = σ.curThread → σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      L.cpu s' = L.cpu s ∧
      ∀ p, RegOK s σ p → RegOK s' (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) p ⦄
  mpSR : ∀ s s' a σ σ' (p hi : U64), hi.val < 2048 → SR s a σ → RegOK s σ p → L.ksb s' = L.ksb s →
    L.cpu s' = L.cpu s → (∀ b, Aligned b → ¬ MpW th p (L.ksb s) hi b → L.mem s' b = L.mem s b) →
    MpStep p σ σ' → SR s' a σ'

end Hyps


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]


/-- The hypotheses on the pool's frame `[p, p + 4096)` (see the module
docstring): aligned, not wrapping, non-null; no object straddling it, no
linked slot and no CNode in it; the ASID pools, the page tables and the ASID
table outside it. -/
structure MpRegion (th : TypedHeap) (G : MdbGhost) (P L4 L3 L2 L1 : Set U64) (ksb p : U64) : Prop where
  pal : p.val % 4096 = 0
  pfit : p.val + 4096 ≤ 2 ^ 64
  p0 : p ≠ 0#u64
  nstr : NoStraddle th p.val (p.val + 4096)
  nslot : ∀ y ∈ G.chains.flatten, y.val < p.val ∨ p.val + 4096 ≤ y.val
  ncn : ∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096)
  pools : ∀ q ∈ P, q.val + 4096 ≤ p.val ∨ p.val + 4096 ≤ q.val
  tables : ∀ q, (q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q.val + 4096 ≤ p.val ∨ p.val + 4096 ≤ q.val
  atab : p.val + 4096 ≤ ksb.val + 288000 ∨ ksb.val + 288000 + 16384 ≤ p.val

/-- **What `MakePool`'s perform exports for the joint invariant**
(XTopJointMakePool): the state `s1` after the restart, the words written
since (`MpW`), the spec's step from the restart's state (`MpStep`, the heap
changed at the pool's cell, the region's cells and two CNodes, the CDT and
the original bits at the destination only), the source's and destination's
caps after, the other slots' caps kept, `DelInv` kept, and the destination's
CNode reached from the root cap `rc` (`CnRef`). -/
def MpMid {A : Type} (th0 : TypedHeap) (s0 : S) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (p : U64)
    (dest ps : Fl4Spec.CslotPtr) (σ' : Fl4Spec.State Unit) (th' : TypedHeap)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ (s1 : S) (ct hi : U64) (σ1 : Fl4Spec.State Unit),
    sched.set_thread_state st s0 ct sched.TS_RESTART = ok s1 ∧ ct.bv = σ.curThread ∧
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    hi.val < 2048 ∧ L.ksb res.2.1 = L.ksb s1 ∧ L.cpu res.2.1 = L.cpu s1 ∧
    (∀ b, Aligned b → ¬ MpW th0 p (L.ksb s1) hi b → L.mem res.2.1 b = L.mem s1 b) ∧
    (∀ w : U64, Aligned w → p.val ≤ w.val → w.val < p.val + 4096 → L.mem res.2.1 w = 0#u64) ∧
    (L.mem res.2.1 (atA (L.ksb s1) hi) = p) ∧
    MpStep p σ1 σ' ∧
    σ'.kheap p.bv = some (.archObj (.asidPool fun _ => none)) ∧
    (∀ o, o ≠ p.bv → σ'.kheap o = σ1.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ σ'.kheap o = none) ∨
      ∃ r cs cs', σ1.kheap o = some (.cnode r cs) ∧ σ'.kheap o = some (.cnode r cs')) ∧
    σ'.cdt = Function.update σ1.cdt dest (some ps) ∧
    (∀ sl, sl ≠ dest → σ'.isOriginalCap sl = σ1.isOriginalCap sl) ∧
    capV (L.mem res.2.1) (cslotAddr ps) = .Untyped p fl4_abi.consts.bits.ASID_POOL 4096#u64 false ∧
    (∃ b, capV (L.mem res.2.1) (cslotAddr dest) = .AsidPool p b) ∧
    (∀ b, capV (L.mem res.2.1) (cslotAddr dest) = .AsidPool p b → b.val % 512 = 0 ∧ b.val < 2 ^ 20) ∧
    (∀ y, IsSlot th' y → y ≠ cslotAddr ps → y ≠ cslotAddr dest → capV (L.mem res.2.1) y = capV (L.mem s0) y) ∧
    (DelInv th' (L.mem s0) → DelInv th' (L.mem res.2.1)) ∧
    (∃ (pp : U64) (rs : Nat) (idx : List Bool) (fi0 : U64), ps = (pp.bv, idx) ∧ th0 pp = some (.cnode rs) ∧
      idx.length = rs ∧ capAt (L.mem s0) (cslotAddr ps) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false) ∧
      ¬ ∃ sl, σ.cdt sl = some ps) ∧
    ∃ (pd : U64) (rd : Nat) (idxd : List Bool), dest = (pd.bv, idxd) ∧ th0 pd = some (.cnode rd) ∧
      idxd.length = rd ∧ capAt (L.mem s0) (cslotAddr dest) = ok .Null ∧ CnRef th0 (L.mem s0) rc pd

/-- The post of `MakePool`'s perform. -/
def MpPost {A : Type} (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (th0 : TypedHeap) (k0 : U64)
    (m0 : U64 → U64) (G0 : MdbGhost) (s0 : S) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (p : U64)
    (dest ps : Fl4Spec.CslotPtr) (base : Fl4Spec.Asid)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' th' G', ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      Fl4Spec.performAsidControlInvocation (.makePool p.bv dest ps base)) σ).1 ∧
    ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      Fl4Spec.performAsidControlInvocation (.makePool p.bv dest ps base)) σ).2 ∧
    Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
    MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
    UtInv (L.mem res.2.1) G' ∧ VsRel (insert p P) (L.mem res.2.1) (L.ksb res.2.1) σ' ∧
    PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
    Vs.FrameInv (L.mem res.2.1) G' ∧
    (∀ P' L4' L3' L2' L1' : Set U64, Vs.VsCapsIn P' L4' L3' L2' L1' m0 G0 →
      Vs.VsCapsIn (insert p P') L4' L3' L2' L1' (L.mem res.2.1) G') ∧
    MdbStep m0 G0 (L.mem res.2.1) G' ∧
    (∀ ksb : U64, Vs.VsMdbInv ksb m0 G0 → Vs.VsMdbInv ksb (L.mem res.2.1) G') ∧
    σ'.curThread = σ.curThread ∧
    /- what the joint placement invariant needs of the step (`MpPlacedHyp`) -/
    th' = restrictTh th0 p.val (p.val + 4096) ∧ L.ksb res.2.1 = k0 ∧
    (∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n)) ∧
    MpRegion th0 G0 P L4 L3 L2 L1 k0 p ∧
    (∃ x fi, x ∈ G0.chains.flatten ∧ capV m0 x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false ∧
      ∀ y, ¬ Mdb.Desc G0.par y x) ∧
    (∀ L4' : Set U64, Vs.PoolsIn P L4' m0 → Vs.PoolsIn (insert p P) L4' (L.mem res.2.1)) ∧
    MpMid (L := L) th0 s0 rc σ p dest ps σ' th' res

theorem spec_eq_mp {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : m ⦃ v => m = ok v ∧ P v ⦄ := by
  cases m <;> simp_all [WP.spec_ok]

theorem delInv_same_mp {th0 : TypedHeap} {m m' : U64 → U64} (hD : DelInv th0 m) (hS : SlotsSame th0 m m') :
    DelInv th0 m' :=
  DelInv.of_kept hD id (fun y hy p zt n h => ⟨hy, by show capV m y = _; rw [← hS.capV hy]; exact h⟩)
    (fun _ _ _ _ hne _ _ _ _ _ _ _ _ => hne)
    (fun y hy h => by rw [hS.prevOf hy, hS.nextOf hy]; exact hD.nc y hy (by rw [← hS.capV hy]; exact h))

/-- **`MpMid` without the restart**: the words written since `s0` (`MpW`),
the spec's step from `σ` (`MpStep`), the source's and destination's caps
after, the other slots' caps kept, `DelInv` kept, the decode's facts at
`s0`. -/
def MpMidB {A : Type} (th0 : TypedHeap) (s0 : S) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (p : U64)
    (dest ps : Fl4Spec.CslotPtr) (σ' : Fl4Spec.State Unit) (th' : TypedHeap)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ (hi : U64), hi.val < 2048 ∧ L.ksb res.2.1 = L.ksb s0 ∧ L.cpu res.2.1 = L.cpu s0 ∧
    (∀ b, Aligned b → ¬ MpW th0 p (L.ksb s0) hi b → L.mem res.2.1 b = L.mem s0 b) ∧
    (∀ w : U64, Aligned w → p.val ≤ w.val → w.val < p.val + 4096 → L.mem res.2.1 w = 0#u64) ∧
    (L.mem res.2.1 (atA (L.ksb s0) hi) = p) ∧
    MpStep p σ σ' ∧
    σ'.kheap p.bv = some (.archObj (.asidPool fun _ => none)) ∧
    (∀ o, o ≠ p.bv → σ'.kheap o = σ.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ σ'.kheap o = none) ∨
      ∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ σ'.kheap o = some (.cnode r cs')) ∧
    σ'.cdt = Function.update σ.cdt dest (some ps) ∧
    (∀ sl, sl ≠ dest → σ'.isOriginalCap sl = σ.isOriginalCap sl) ∧
    capV (L.mem res.2.1) (cslotAddr ps) = .Untyped p fl4_abi.consts.bits.ASID_POOL 4096#u64 false ∧
    (∃ b, capV (L.mem res.2.1) (cslotAddr dest) = .AsidPool p b) ∧
    (∀ b, capV (L.mem res.2.1) (cslotAddr dest) = .AsidPool p b → b.val % 512 = 0 ∧ b.val < 2 ^ 20) ∧
    (∀ y, IsSlot th' y → y ≠ cslotAddr ps → y ≠ cslotAddr dest → capV (L.mem res.2.1) y = capV (L.mem s0) y) ∧
    (DelInv th' (L.mem s0) → DelInv th' (L.mem res.2.1)) ∧
    (∃ (pp : U64) (rs : Nat) (idx : List Bool) (fi0 : U64), ps = (pp.bv, idx) ∧ th0 pp = some (.cnode rs) ∧
      idx.length = rs ∧ capAt (L.mem s0) (cslotAddr ps) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false) ∧
      ¬ ∃ sl, σ.cdt sl = some ps) ∧
    ∃ (pd : U64) (rd : Nat) (idxd : List Bool), dest = (pd.bv, idxd) ∧ th0 pd = some (.cnode rd) ∧
      idxd.length = rd ∧ capAt (L.mem s0) (cslotAddr dest) = ok .Null

/-- The post of `MakePool`'s perform without the restart (`mp_perform_relB`). -/
def MpPostB {A : Type} (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (th0 : TypedHeap) (k0 : U64)
    (m0 : U64 → U64) (G0 : MdbGhost) (s0 : S) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (p : U64)
    (dest ps : Fl4Spec.CslotPtr) (base : Fl4Spec.Asid)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' th' G', ((), σ') ∈ ((Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv dest ps base)) σ).1 ∧
    ¬ ((Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv dest ps base)) σ).2 ∧
    Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
    MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
    UtInv (L.mem res.2.1) G' ∧ VsRel (insert p P) (L.mem res.2.1) (L.ksb res.2.1) σ' ∧
    PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
    Vs.FrameInv (L.mem res.2.1) G' ∧
    (∀ P' L4' L3' L2' L1' : Set U64, Vs.VsCapsIn P' L4' L3' L2' L1' m0 G0 →
      Vs.VsCapsIn (insert p P') L4' L3' L2' L1' (L.mem res.2.1) G') ∧
    MdbStep m0 G0 (L.mem res.2.1) G' ∧
    (∀ ksb : U64, Vs.VsMdbInv ksb m0 G0 → Vs.VsMdbInv ksb (L.mem res.2.1) G') ∧
    σ'.curThread = σ.curThread ∧
    /- what the joint placement invariant needs of the step (`MpPlacedHyp`) -/
    th' = restrictTh th0 p.val (p.val + 4096) ∧ L.ksb res.2.1 = k0 ∧
    (∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n)) ∧
    MpRegion th0 G0 P L4 L3 L2 L1 k0 p ∧
    (∃ x fi, x ∈ G0.chains.flatten ∧ capV m0 x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false ∧
      ∀ y, ¬ Mdb.Desc G0.par y x) ∧
    (∀ L4' : Set U64, Vs.PoolsIn P L4' m0 → Vs.PoolsIn (insert p P) L4' (L.mem res.2.1)) ∧
    MpMidB (L := L) th0 s0 rc σ p dest ps σ' th' res

set_option maxHeartbeats 4000000 in
/-- **`MakePool`'s perform without the restart refines l4v**: `mp_perform_rel`
from the state itself (after the restart), against the spec's
`perform_asid_control_invocation` from `σ` (`MpPostB`). -/
theorem mp_perform_relB {A : Type} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} (hsb : sb = fl4_abi.consts.bits.ASID_POOL)
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx))
    {pd : U64} {rd : Nat} (hpd : th pd = some (.cnode rd)) {idxd : List Bool} (hidxd : idxd.length = rd)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    {i base : U64} (hi : i.val < 2048) (hbase : base.val = i.val * 512)
    (hRg : MpRegion th G P L4 L3 L2 L1 (L.ksb s) p) (hRO : RegOK s σ p)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b) (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) {rc : capability.Cap} :
    (do
      let i1 ← lift (sb &&& 63#u64)
      let i2 ← 1#u64 <<< i1
      let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s (capability.Cap.Untyped p sb i2 false)
      let s3 ← st.clear_free s2 p 4096#u64
      let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
      let s5 ← vspace.set_asid_table st s4 i p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = a ∧ MpPostB (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G s rc σ p (pd.bv, idxd) (pp.bv, idx) base.bv res ⦄ := by
  obtain ⟨hpal, hpfit, hp0, hN, hns, hcn, hPo, hLo, hTo⟩ := hRg
  set x := cslotAddr (pp.bv, idx) with hxdef
  set val := cslotAddr (pd.bv, idxd) with hvaldef
  have hsbv : sb.val = 12 := by rw [hsb]; unfold fl4_abi.consts.bits.ASID_POOL; rfl
  have h2sb : 2 ^ sb.val = 4096 := by rw [hsbv]; rfl
  set th' := restrictTh th p.val (p.val + 2 ^ sb.val) with hth'
  have hP' : Placed th' := hPl.restrict
  have hN' : NoStraddle th p.val (p.val + 2 ^ sb.val) := by rw [h2sb]; exact hN
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hidxd] using hpd)⟩
  have hxs : IsSlot th x := hAs.isSlot
  have hvs : IsSlot th val := hAd.isSlot
  have hpp' : th' pp = some (.cnode rs) := by
    rw [hth', restrictTh_out (by rw [h2sb]; exact hcn pp rs hpp)]; exact hpp
  have hpd' : th' pd = some (.cnode rd) := by
    rw [hth', restrictTh_out (by rw [h2sb]; exact hcn pd rd hpd)]; exact hpd
  have hAs' : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp')⟩
  have hAd' : AbsSlot th' (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hidxd] using hpd')⟩
  have hxs' : IsSlot th' x := hAs'.isSlot
  have hvs' : IsSlot th' val := hAd'.isSlot
  have hxv : x ≠ val := by
    intro e; rw [e, hdst] at hcap; cases eq_of_ok_eq hcap
  -- no restart: the body starts at the state itself
  have hKT1 : KTyped th σ := hFI.kt
  have hSS : SlotsSame th (L.mem s) (L.mem s) := SlotsSame.refl _ _
  -- the free index
  have hl : (lift (sb &&& 63#u64) : Result U64) = ok sb := by subst hsb; unfold fl4_abi.consts.bits.ASID_POOL; rfl
  have hsh : (1#u64 <<< sb : Result U64) = ok 4096#u64 := by subst hsb; unfold fl4_abi.consts.bits.ASID_POOL; rfl
  rw [hl]; simp only [bind_ok]; rw [hsh]; simp only [bind_ok]
  -- the region and the spec's state without it
  have hpfit' : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by rw [h2sb]; exact hpfit
  have hreg : ∀ q : U64, q.bv ∈ Fl4Proofs.P3.regionSet p.bv 12 ↔ p.val ≤ q.val ∧ q.val < p.val + 4096 :=
    fun q => regionSet_iff p q 12 (by decide) hpfit
  have hxm : x ∈ G.chains.flatten := (hM.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hnd : ∀ y, ¬ Mdb.Desc G.par y x := nodesc_of_cdt hPl hC hAs hnch
  have hcx1 : capV (L.mem s) x = .Untyped p sb fi false := capV_of_capAt hcap
  have hdel_rel : ∀ τd : Fl4Spec.State Unit, KSame (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ) τd →
      ResetRel th' G x p sb false (L.mem s) τd fi := by
    intro τd hD
    obtain ⟨r1, r2, r3, r4⟩ := detype_rel (σ := σ) (σd := τd) hSt hSV hPl hM hC hI hU hxm hcx1 hnd hN'
      (by rw [h2sb]; exact hns) (fun q hq => by
        rw [hD.1]; simp only [Fl4Spec.detype]
        split_ifs with h
        · exact absurd ((hreg q).1 h) (by rw [← h2sb]; exact hq)
        · rfl)
      (by rw [hD.2.1]; rfl) (by rw [hD.2.2.1]; rfl)
    exact ⟨r1, r2, r3, r4, hI, hU, hcx1⟩
  have hf' : (4096#u64 : U64).val ≤ 2 ^ sb.val := by rw [h2sb]; decide
  have hset := fun τd hD => reset_set_step (L := L) hPl hpp' hidx (hdel_rel τd hD) hnd 4096#u64 hf'
  obtain ⟨s2, hs2, -⟩ := spec_exists (hset _ (KSame.refl _))
  rw [hs2]; simp only [bind_ok]
  have hset2 : ∀ τd, KSame (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ) τd → ∃ cs,
      τd.kheap pp.bv = some (.cnode rs cs) ∧ Fl4Spec.wellFormedCnodeN rs cs ∧
      ResetRel th' G x p sb false (L.mem s2)
        (setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv sb.val (4096#u64 : U64).val)) 4096#u64 ∧
      (∀ w : U64, P1.Aligned w → w.val ≠ x.val → w.val ≠ x.val + 8 → L.mem s2 w = L.mem s w) ∧
      (∀ y, IsSlot th' y → y ≠ x → capV (L.mem s2) y = capV (L.mem s) y) ∧
      LinksKeep th' (L.mem s) (L.mem s2) := by
    intro τd hD
    have := hset τd hD
    rw [hs2, WP.spec_ok] at this
    obtain ⟨cs, h1, h2, h3, h4, h5, h6⟩ := this
    exact ⟨cs, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨cs0, -, -, RR2, hfr2, hco2, hLK2⟩ := hset2 _ (KSame.refl _)
  -- the zeroing
  rw [L.clear_free_eq]; simp only [bind_ok]
  set s3 := L.zr s2 p 4096#u64 with hs3
  have hpA : P1.Aligned p := by unfold P1.Aligned; omega
  have hzero : ∀ τ f, ResetRel th' G x p sb false (L.mem s2) τ f → ResetRel th' G x p sb false (L.mem s3) τ f ∧
      ∀ w : U64, P1.Aligned w → L.mem s3 w = if p.val ≤ w.val ∧ w.val < p.val + 4096 then 0#u64 else L.mem s2 w :=
    fun τ f h => reset_zero_step (L := L) hPl hN' h hxs' p 4096#u64 hpA (by decide) le_rfl
      (by rw [h2sb]; rfl) hpfit'
  obtain ⟨RR3, hz3⟩ := hzero _ _ RR2
  have hSS3 : SlotsSame th' (L.mem s2) (L.mem s3) :=
    slotsSame_out hP' (fun b hb => hb.restrict_words hPl hN') (fun w hw ho => by
      rw [hz3 w hw, if_neg (by rw [h2sb] at ho; omega)])
  -- the insertion
  have he0 : EncWf (capability.Cap.Untyped p sb fi false) := by rw [capAt_words] at hcap; exact decode_encWf hcap
  have heA : EncWf (capability.Cap.AsidPool p base) := he0.1
  have hsrc3 : capAt (L.mem s3) x = ok (.Untyped p sb 4096#u64 false) := by rw [capAt_capV, RR3.cap]
  have hdst3 : capAt (L.mem s3) val = ok .Null := by
    rw [capAt_capV, hSS3.capV hvs', hco2 val hvs' (Ne.symm hxv), ← capAt_capV, hdst]
  have hnx : nextOf (L.mem s3) x = 0#u64 ∨
      (IsSlot th' (nextOf (L.mem s3) x) ∧ nextOf (L.mem s3) x ≠ val ∧ nextOf (L.mem s3) x ≠ x) := by
    have hvm : val ∉ G.chains.flatten := by
      intro h; obtain ⟨-, c0, h0, hn⟩ := (RR3.M.members val).1 h
      rw [hdst3] at h0; exact hn (eq_of_ok_eq h0).symm
    rcases RR3.M.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨((RR3.M.members _).1 h1).1, fun e => hvm (e ▸ h1), h2⟩
  have hnx' : nextOf (L.mem s3) x = 0#u64 ∨ IsSlot th' (nextOf (L.mem s3) x) := by
    rcases hnx with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hvm0 : val ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (RR3.M.members val).1 h
    rw [hdst3] at h0; exact hn (eq_of_ok_eq h0).symm
  obtain ⟨s4, hs4, hdi4, hW4, hF4, hF2⟩ := spec_exists (WP.spec_and
    (insert_delinv_imp (L := L) hP' s3 G RR3.M hxm hvs' hvm0 hsrc3 (.AsidPool p base) heA (by simp) rfl) <| WP.spec_and
    (insert_mem (L := L) hP' s3 (.AsidPool p base) x val hxs' hvs' hxv _ hsrc3 hnx)
    (WP.spec_and (insert_frame (L := L) hP' s3 (.AsidPool p base) x val hxs' hvs' _ hsrc3 hnx')
      (insert_frame2 (L := L) hP' s3 (.AsidPool p base) x val hxs' hvs' _ hsrc3 hnx')))
  rw [hs4]; simp only [bind_ok]
  refine WP.spec_bind (set_asid_table_spec s4 i p) ?_
  rintro s5 rfl
  refine (WP.spec_ok _).2 ⟨rfl, rfl, ?_⟩
  show MpPostB (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G s rc σ p (pd.bv, idxd) (pp.bv, idx) base.bv
    (.Ok (), L.wr s4 (atA (L.ksb s4) (i &&& 2047#u64)) p, a)
  -- FL4: the kernel-state base and the words
  have hksb2 : L.ksb s2 = L.ksb s := by
    have := set_cap_spec (L := L) x s (.Untyped p sb 4096#u64 false)
    rw [hs2, WP.spec_ok] at this; rw [this]; simp
  have hksb4 : L.ksb s4 = L.ksb s := by rw [hF4.1, hs3, L.ksb_zr, hksb2]
  set K := L.ksb s with hK
  rw [hksb4, and2047_of_lt hi]
  set s5 := L.wr s4 (atA K i) p with hs5
  have hksb5 : L.ksb s5 = K := by rw [hs5, L.ksb_wr, hksb4]
  have hAt : P1.Aligned (atA K i) := by
    show _ % 8 = 0; rw [atA_val hVP.ksb_fit hi]; have := hVP.ksb_al; omega
  have hAtv := atA_val hVP.ksb_fit hi
  have hAtO : OutsideObjects th (atA K i) := hVO _ (Or.inl ⟨i, hi, rfl⟩)
  have hslo : ∀ b, OutsideObjects th b → ∀ y, IsSlot th y → ¬ (y.val ≤ b.val ∧ b.val < y.val + 32) := by
    intro b hb y hy hin
    obtain ⟨q, k, hq, h1, h2, -⟩ := slot_in_object hPl hy
    exact hb.2 q k hq ⟨by omega, by omega⟩
  have hO' : ∀ b, OutsideObjects th b → OutsideObjects th' b :=
    fun b hb => ⟨hb.1, fun q k h => hb.2 q k (restrictTh_some h).1⟩
  have hmem41 : ∀ b, P1.Aligned b → OutsideObjects th b → ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) →
      L.mem s4 b = L.mem s b := by
    intro b hb ho hr
    have h1 := hslo b ho x hxs
    rw [hF4.2 b (hO' b ho), hz3 b hb, if_neg hr, hfr2 b hb (by omega) (by omega)]
  have hmemR : ∀ b, P1.Aligned b → p.val ≤ b.val → b.val < p.val + 4096 → L.mem s4 b = 0#u64 := by
    intro b hb h1 h2
    have hob : OutsideObjects th' b := ⟨hb, fun q k hq hin => by
      have := RegionFree.restrict hN' q k hq
      rw [h2sb] at this; omega⟩
    rw [hF4.2 b hob, hz3 b hb, if_pos ⟨h1, h2⟩]
  have hm54 : ∀ b, P1.Aligned b → b.val ≠ (atA K i).val → L.mem s5 b = L.mem s4 b :=
    fun b hb hne => L.mem_wr_ne hAt hb (Ne.symm hne)
  have hSS5 : SlotsSame th' (L.mem s4) (L.mem s5) :=
    slotsSame_wr hP' s4 p hAt (fun y hy => hslo _ hAtO y hy.of_restrict)
  have hvm : val ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (RR3.M.members val).1 h
    rw [hdst3] at h0; exact hn (eq_of_ok_eq h0).symm
  have hbv : base.bv.toNat = i.bv.toNat * 512 := hbase
  have hlow : Fl4Spec.asidLowBitsOf base.bv = 0 := base_low hbv
  have hhigh : Fl4Spec.asidHighBitsOf base.bv = Fl4Spec.ucast 11 i.bv := base_high hi hbv
  have hpq : ∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096) → q.bv ≠ p.bv := by
    intro q hq e
    have : q.val = p.val := congrArg BitVec.toNat e
    omega
  have hp0bv : Fl4Spec.ptrAdd p.bv (0 * 2 ^ 12) = p.bv := by simp [Fl4Spec.ptrAdd]
  set A : Fl4Spec.Cap := .archObjectCap (.asidPoolCap p.bv base.bv) with hA
  set G' := insG G x val true with hG'
  -- the spec, after `delete_objects`
  have key : ∀ τd : Fl4Spec.State Unit, KSame (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ) τd →
      ∃ τf, mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv τd = ({((), τf)}, False) ∧
        StateRel th' (L.mem s5) τf ∧ SlotsValid th' (L.mem s5) ∧ MdbLinks th' (L.mem s4) G' ∧
        MdbLinks th' (L.mem s5) G' ∧ CdtRel th' (L.mem s5) τf G' ∧ (∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096) →
          ∀ ao, σ.kheap q.bv = some (.archObj ao) → τf.kheap q.bv = σ.kheap q.bv) ∧
        τf.kheap p.bv = some (.archObj (.asidPool fun _ => none)) ∧
        τf.archState.x64AsidTable =
          Function.update σ.archState.x64AsidTable (Fl4Spec.ucast 11 i.bv) (some p.bv) ∧
        OStep (fun _ => False) τd τf ∧ τf.machineState = τd.machineState ∧
        τf.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3 ∧ KTyped th' τf ∧
        (∀ o, o ≠ p.bv → τf.kheap o = σ.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ τf.kheap o = none) ∨
          ∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ τf.kheap o = some (.cnode r cs')) ∧
        τf.cdt = Function.update σ.cdt (pd.bv, idxd) (some (pp.bv, idx)) ∧
        (∀ sl, sl ≠ (pd.bv, idxd) → τf.isOriginalCap sl = σ.isOriginalCap sl) := by
    intro τd hD
    obtain ⟨cs, hkpp, hwf, RR2τ, -, -, -⟩ := hset2 τd hD
    have hτs : setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv sb.val (4096#u64 : U64).val) =
        setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv 12 4096) := by rw [hsbv]; rfl
    rw [hτs] at RR2τ
    have RR3τ := (hzero _ _ RR2τ).1
    set τs := setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv 12 4096) with hτsdef
    set τr := mpRegion τd pp.bv rs cs idx p.bv with hτr
    have hgc : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) τd = ({(.untypedCap false p.bv 12 fi.val, τd)}, False) := by
      obtain ⟨c, a', hc, hca, hg⟩ := (hdel_rel τd hD).R.slot_cap (s := s) (sl := (pp.bv, idx)) (p := pp) rfl
        (by simpa [hidx] using hpp')
      rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
      rw [hg, hca.abs]; simp [absCap, hsbv]
    have hkr : ∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096) → τr.kheap q.bv = τs.kheap q.bv := by
      intro q hq
      simp only [hτr, mpRegion, regionHeap]
      rw [foldr_update_apply, if_neg]
      simp only [regionPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton]
      rw [hp0bv]; exact hpq q hq
    have hR3r : StateRel th' (L.mem s3) τr := StateRel.of_agree RR3τ.R (fun q kd hq _ => hkr q (by
      have := (restrictTh_some hq).2; rw [h2sb] at this; exact this))
    have hC3r : CdtRel th' (L.mem s3) τr G := CdtRel.of_cdt RR3τ.C rfl rfl
    -- `cap_insert`
    obtain ⟨cS, aS, hcS, hcaS, hgs⟩ := hR3r.slot_cap (s := s3) (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp')
    rw [hsrc3] at hcS; have := eq_of_ok_eq hcS; subst this
    obtain ⟨cD, aD, hcD, hcaD, hgd⟩ := hR3r.slot_cap (s := s3) (sl := (pd.bv, idxd)) (p := pd) rfl
      (by simpa [hidxd] using hpd')
    rw [hdst3] at hcD; have := eq_of_ok_eq hcD; subst this
    rw [hcaS.abs] at hgs; rw [hcaD.abs] at hgd
    obtain ⟨csd, hkpd, hwfd, -⟩ := hR3r.cnode pd rd hpd'
    have hsetd := setCap_cnode (Z := Unit) A hkpd hwfd hidxd
    have hci := capInsert_eq hgs hgd (setUntyped_skip (by simp [Fl4Spec.isUntypedCap, hA])) hsetd rfl rfl
    set τi := capInsertState τr (setCnodeSlot τr pd.bv rd csd idxd A) A
      (absCap (.Untyped p sb 4096#u64 false)) (pp.bv, idx) (pd.bv, idxd) with hτi
    have hperf := mpPerf_eq hkpp hwf hidx hgc hci hlow
    have hins := insert_refines' (L := L) th' s3 τr G hR3r RR3τ.V hP' RR3τ.M hC3r hpp' hpd' hidx hidxd hsrc3
      (by simp) hdst3 (.AsidPool p base) A ⟨trivial, rfl⟩ trivial heA (by simp) trivial
    rw [hs4, WP.spec_ok] at hins
    obtain ⟨τi', G'', hci', hR4, hV4, hM4, hC4, hG''⟩ := hins (fun _ => hnd)
    have e1 : τi' = τi := by
      rw [hci] at hci'
      have := congrArg Prod.fst hci'
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    rw [e1] at hR4 hC4
    have hio : τr.isOriginalCap (pp.bv, idx) = true := by
      rw [hC3r.orig (pp.bv, idx) hAs']; exact RR3.I.utrev x hxm (by rw [RR3.cap]; rfl)
    have hb : decide (Fl4Spec.shouldBeParentOf (absCap (.Untyped p sb 4096#u64 false))
        (τr.isOriginalCap (pp.bv, idx)) A
        (decide (Fl4Spec.isCapRevocable A (absCap (.Untyped p sb 4096#u64 false))))) = true := by
      rw [hio]; simp only [absCap, hsbv]
      exact decide_eq_true (sbp_pool hpfit base.bv _ _)
    rw [hb] at hG''
    subst hG''
    have hpdq : ∀ q : U64, ∀ ao, σ.kheap q.bv = some (.archObj ao) → q.bv ≠ pd.bv ∧ q.bv ≠ pp.bv := by
      intro q ao hq
      obtain ⟨c1, hk1, -⟩ := hSt.cnode pd rd hpd
      obtain ⟨c2, hk2, -⟩ := hSt.cnode pp rs hpp
      exact ⟨fun e => (by rw [e, hk1] at hq; cases hq), fun e => (by rw [e, hk2] at hq; cases hq)⟩
    have hpd_out : ¬ (p.val ≤ pd.val ∧ pd.val < p.val + 4096) := hcn pd rd hpd
    have hpp_out : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 4096) := hcn pp rs hpp
    have hpdp : p.bv ≠ pd.bv := fun e => hpq pd hpd_out e.symm
    have hppp : p.bv ≠ pp.bv := fun e => hpq pp hpp_out e.symm
    refine ⟨mpTable τi p.bv base.bv, hperf, (hR4.of_kheap (σ' := mpTable τi p.bv base.bv) rfl).of_caps (fun y hy => hSS5.capAt hy),
      Fl4Proofs.P3.SlotsValid.of_caps hV4 (fun y hy => hSS5.capAt hy), hM4, hM4.of_same hSS5,
      hC4.of_same hSS5 rfl rfl, fun q hq ao hqa => ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hpdq q ao hqa
      show (Function.update τr.kheap pd.bv _) q.bv = _
      rw [Function.update_of_ne h1, hkr q hq]
      show (Function.update τd.kheap pp.bv _) q.bv = _
      rw [Function.update_of_ne h2, hD.1]
      simp only [Fl4Spec.detype]
      split_ifs with h
      · exact absurd ((hreg q).1 h) hq
      · rfl
    · show (Function.update τr.kheap pd.bv _) p.bv = _
      rw [Function.update_of_ne hpdp]
      simp only [hτr, mpRegion, regionHeap]
      rw [foldr_update_apply, if_pos]
      simp only [regionPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton]
      exact hp0bv.symm
    · show Function.update τi.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv) (some p.bv) = _
      rw [hhigh]
      have : τi.archState = σ.archState := hD.2.2.2
      rw [this]
    · -- the other subsystems' state: only CNodes, the pool's cell, the CDT and the table change
      have hpd0 : τd.kheap p.bv = none := by
        rw [hD.1]; simp only [Fl4Spec.detype]
        rw [if_pos ((hreg p).2 ⟨le_refl _, by omega⟩)]
      have h1 := OStep.cnode hkpp idx (.untypedCap false p.bv 12 4096)
      have hτr' : τr = updK τs p.bv (.archObj (.asidPool fun _ => none)) := by
        simp only [hτr, mpRegion, regionHeap, regionPtrs, List.range_one, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, hp0bv]; rfl
      have h2 : OStep (fun _ => False) τs τr := by
        rw [hτr']
        refine OStep.arch (Or.inl ?_) _
        show (Function.update τd.kheap pp.bv _) p.bv = none
        rw [Function.update_of_ne hppp, hpd0]
      have h3 := OStep.cnode hkpd idxd A
      have h4 : OStep (fun _ => False) (setCnodeSlot τr pd.bv rd csd idxd A) τi :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ hq => absurd rfl hq⟩
      have h5 := OStep.table (σ := τi) (Function.update τi.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv)
        (some p.bv))
      exact ((((h1.trans h2).trans h3).trans h4).trans h5).mono (fun q h => by simp at h)
    · show τi.archState.x64CurrentCr3 = _
      rw [show τi.archState = σ.archState from hD.2.2.2]
    · -- the spec's CNodes and TCBs are the restricted heap's
      have hτr' : τr = updK τs p.bv (.archObj (.asidPool fun _ => none)) := by
        simp only [hτr, mpRegion, regionHeap, regionPtrs, List.range_one, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, hp0bv]; rfl
      have hkh : ∀ o, (mpTable τi p.bv base.bv).kheap o = Function.update (Function.update
          (Function.update τd.kheap pp.bv (some (.cnode rs (Function.update cs idx
            (some (.untypedCap false p.bv 12 4096)))))) p.bv (some (.archObj (.asidPool fun _ => none)))) pd.bv
          (some (.cnode rd (Function.update csd idxd (some A)))) o := by
        intro o; show (Function.update τr.kheap pd.bv _) o = _; rw [hτr']; rfl
      have hout : ∀ o : Fl4Spec.ObjRef, o ∉ Fl4Proofs.P3.regionSet p.bv 12 → th' ⟨o⟩ = th ⟨o⟩ := by
        intro o ho
        rw [hth', restrictTh_out]
        intro hin; apply ho; rw [show o = (⟨o⟩ : U64).bv from rfl, hreg]; rw [h2sb] at hin; exact hin
      have hd0 : ∀ o, τd.kheap o = (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ).kheap o := by
        intro o; rw [hD.1]
      intro o
      refine ⟨fun r' cs' hc hw => ?_, fun t ht => ?_⟩ <;> rw [hkh] at *
      · by_cases e1 : o = pd.bv
        · subst e1; rw [Function.update_self] at hc; cases hc; exact hpd'
        rw [Function.update_of_ne e1] at hc
        by_cases e2 : o = p.bv
        · subst e2; rw [Function.update_self] at hc; cases hc
        rw [Function.update_of_ne e2] at hc
        by_cases e3 : o = pp.bv
        · subst e3; rw [Function.update_self] at hc; cases hc; exact hpp'
        rw [Function.update_of_ne e3, hd0] at hc
        simp only [Fl4Spec.detype] at hc
        split_ifs at hc with h4
        rw [hout o h4]; exact (hKT1 o).1 r' cs' hc hw
      · by_cases e1 : o = pd.bv
        · subst e1; rw [Function.update_self] at ht; cases ht
        rw [Function.update_of_ne e1] at ht
        by_cases e2 : o = p.bv
        · subst e2; rw [Function.update_self] at ht; cases ht
        rw [Function.update_of_ne e2] at ht
        by_cases e3 : o = pp.bv
        · subst e3; rw [Function.update_self] at ht; cases ht
        rw [Function.update_of_ne e3, hd0] at ht
        simp only [Fl4Spec.detype] at ht
        split_ifs at ht with h4
        rw [hout o h4]; exact (hKT1 o).2 t ht
    · -- the heap: the pool's cell, the region's cells and two CNodes change
      have hτr' : τr = updK τs p.bv (.archObj (.asidPool fun _ => none)) := by
        simp only [hτr, mpRegion, regionHeap, regionPtrs, List.range_one, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, hp0bv]; rfl
      have hkh : ∀ o, (mpTable τi p.bv base.bv).kheap o = Function.update (Function.update
          (Function.update τd.kheap pp.bv (some (.cnode rs (Function.update cs idx
            (some (.untypedCap false p.bv 12 4096)))))) p.bv (some (.archObj (.asidPool fun _ => none)))) pd.bv
          (some (.cnode rd (Function.update csd idxd (some A)))) o := by
        intro o; show (Function.update τr.kheap pd.bv _) o = _; rw [hτr']; rfl
      intro o hop
      rw [hkh]
      obtain ⟨c1, hk1, -⟩ := hSt.cnode pd rd hpd
      obtain ⟨c2, hk2, -⟩ := hSt.cnode pp rs hpp
      by_cases e1 : o = pd.bv
      · subst e1; rw [Function.update_self]
        exact Or.inr (Or.inr ⟨rd, c1, _, hk1, rfl⟩)
      rw [Function.update_of_ne e1, Function.update_of_ne hop]
      by_cases e3 : o = pp.bv
      · subst e3; rw [Function.update_self]
        exact Or.inr (Or.inr ⟨rs, c2, _, hk2, rfl⟩)
      rw [Function.update_of_ne e3, hD.1]
      simp only [Fl4Spec.detype]
      split_ifs with h4
      · exact Or.inr (Or.inl ⟨h4, rfl⟩)
      · exact Or.inl rfl
    · -- the CDT
      show Function.update τr.cdt (pd.bv, idxd) (if _ = true then _ else _) = _
      rw [if_pos hb]
      have : τr.cdt = σ.cdt := hD.2.1
      rw [this]
    · -- the original bits
      intro sl hsl
      show Function.update τr.isOriginalCap (pd.bv, idxd) _ sl = _
      rw [Function.update_of_ne hsl]
      exact congrFun hD.2.2.1 sl
  -- the MDB invariants after the insertion
  have heU : EncWf (capability.Cap.Untyped p sb 4096#u64 false) := ⟨he0.1, he0.2⟩
  have hNc : Canonical (nextOf (L.mem s3) x) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP'
  have hbA : baseF (.AsidPool p base) = baseF (capV (L.mem s3) x) := by
    rw [RR3.cap]; unfold baseF; rw [ptrF_ap, ptrF_ut]
  have htA : topF (.AsidPool p base) = topF (capV (L.mem s3) x) := by
    rw [RR3.cap]; unfold topF; rw [ptrF_ap, ptrF_ut, sizeF_ap, sizeF_ut, hsb]
  obtain ⟨tx1, tx2⟩ := topF_ut p sb 4096#u64 false (by omega) hpfit'
  have hctx : InsACtx th' (L.mem s3) (L.mem s4) G x val p base :=
    { hM := RR3.M, hI := RR3.I, hsrc := hxm, hd := hvs', hdest := hvm
      hnext := fun y hy => hW4.nextOf' hP' hy hvs' hxv hNc
      hcap := fun y hy => by
        have h := hW4.capAt' hy heA heU hsrc3
        rw [capAt_capV] at h
        by_cases h1 : y = val
        · rw [if_pos h1] at h ⊢; exact eq_of_ok_eq h
        · rw [if_neg h1] at h ⊢
          by_cases h2 : y = x
          · rw [if_pos h2] at h; subst h2; rw [RR3.cap]; exact eq_of_ok_eq h
          · rw [if_neg h2, capAt_capV] at h; exact eq_of_ok_eq h
      hrev := fun y hy => by rw [hW4.revOf' hy hxv]; rfl
      hfb := fun y hy => by rw [InsWords.fbOf' hW4 hy hxv]; rfl
      hut := by rw [RR3.cap]; rfl
      hcr := by rw [hbA, htA, RR3.cap, tx1, tx2]; have := Nat.one_le_two_pow (n := sb.val); omega
      hcin := by unfold Within; rw [hbA, htA]; exact ⟨le_refl _, le_refl _⟩
      hreg := RR3.U.reg
      hno := fun y hy hp => by
        by_cases hyx : y = x
        · right; rw [hyx, RR3.cap]; exact ⟨rfl, le_refl _, le_refl _⟩
        · by_cases hdj : Disj (capV (L.mem s3) y) (capV (L.mem s3) x)
          · left; unfold Disj at hdj ⊢; rw [hbA, htA]; exact hdj
          · rcases RR3.U.drange x hxm p sb 4096#u64 false RR3.cap y hy hyx hp hdj with h | h
            · exact absurd h (hnd y)
            · right
              have h0 := RR3.I.desc y x h
              unfold isPM isPF at h0
              simp only [Bool.and_eq_true] at h0
              obtain ⟨⟨-, h2⟩, -⟩ := h0
              rw [RR3.cap] at h2
              have hU' := srB_to_ut h2
              rw [← RR3.cap] at h2
              exact ⟨hU', ((srB_ut_iff hU' _).1 h2).2.1⟩
      hdd := fun y hy => absurd hy (hnd y) }
  have hI4 : MdbInv (L.mem s4) G' := hctx.inv
  have hU4 : UtInv (L.mem s4) G' := utinv_pool RR3.M RR3.U hxm RR3.cap (by rw [h2sb]; rfl) hnd hvm hctx.cd
    hbA htA (fun y hy => hctx.cz hy)
  -- the spec run
  have hDel := deleteObjects_nsat (Z := Unit) (a := p.bv) (show p.val % 8 = 0 by omega) 12 σ
  have hrun : (Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ =
      (Fl4Spec.deleteObjects p.bv 12 >>= fun _ => mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) σ := rfl
  have hall : NSat (Fl4Spec.deleteObjects p.bv 12 >>= fun _ => mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) σ
      (fun _ => True) :=
    nsat_bind (hDel.1.mono fun y hy => by
      obtain ⟨τf, he, -⟩ := key y.2 ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2⟩
      exact nsat_det he trivial)
  obtain ⟨y, hy, hPy⟩ := hDel.2
  obtain ⟨τf, he, hR5, hV5, hM4, hM5, hC5, hkq, hkp, htab, hOf, hmsf, hcrf, hKTf, hkhf, hcdtf, horf⟩ := key y.2 ⟨hPy.1, hPy.2.1, hPy.2.2.1, hPy.2.2.2⟩
  have hmem : ((), τf) ∈ ((Fl4Spec.deleteObjects p.bv 12 >>= fun _ =>
      mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) σ).1 := by
    obtain ⟨r, hr, hre⟩ := nhas_bind (m := Fl4Spec.deleteObjects (Z := Unit) p.bv 12)
      (f := fun _ => mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) (s := σ) (P := fun r => r = ((), τf))
      ⟨y, hy, nhas_det he rfl⟩
    rw [← hre]; exact hr
  -- the ASID and page-table relations
  have hVout : ∀ b, VsWrite P K b → ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) := by
    rintro b (⟨hi', hh, rfl⟩ | ⟨q, hq, lo, hl, rfl⟩) hin
    · rw [atA_val hVP.ksb_fit hh] at hin; omega
    · obtain ⟨-, qf⟩ := hVP.pal q hq
      rw [peA_val qf hl] at hin; have := hPo q hq; omega
  have hR1' : VsRel P (L.mem s) K σ := hR
  have hVs4 : VsRel P (L.mem s4) K σ := VsRel.frame hR1'
    (fun b hb => hmem41 b (VsWrite.aligned hVP hb) (hVO b hb) (hVout b hb)) rfl (fun _ _ => rfl)
  have hpP : p ∉ P := fun h => by have := hPo p h; omega
  have hVP' : VsPlaced (insert p P) K := by
    refine ⟨hVP.ksb_al, hVP.ksb_fit, fun q hq => ?_, fun q hq => ?_⟩
    · rcases hq with rfl | hq
      · exact ⟨hpal, hpfit⟩
      · exact hVP.pal q hq
    · rcases hq with rfl | hq
      · exact hTo
      · exact hVP.ptab q hq
  have hpne : ∀ b : U64, b ≠ atA K i → b.val ≠ (atA K i).val := fun b h e => h (UScalar.eq_of_val_eq e)
  have hz5 : ∀ lo : U64, lo.val < 512 → L.mem s5 (peA p lo) = 0#u64 := fun lo hl => by
      have hv := peA_val hpfit hl
      have hal : P1.Aligned (peA p lo) := by show _ % 8 = 0; rw [hv]; omega
      rw [hm54 _ hal (by rw [hv, hAtv]; omega), hmemR _ hal (by omega) (by omega)]
  have hVs5 : VsRel (insert p P) (L.mem s5) K τf := VsRel.add_pool hVP' hVs4 hpP hi hp0
    (fun b hb hne _ => hm54 b hb (hpne b hne))
    hz5
    (L.mem_wr_same hAt) hkp (fun q hq => by
      obtain ⟨f, hf, -⟩ := hVs4.pool q hq
      have := hPo q hq
      rw [hkq q (by omega) _ hf]) htab
  have hPt5 : PtRel L4 L3 L2 L1 (L.mem s5) τf := PtRel.frame hPt
    (fun b hb => by
      have hal := PtWAll.aligned hPP hb
      have hnv : b ≠ atA K i := fun e => hPV b hb (e ▸ Or.inl ⟨i, hi, rfl⟩)
      rw [hm54 b hal (hpne b hnv)]
      refine hmem41 b hal (hPO b hb) ?_
      obtain ⟨q, hq, j, hj, rfl⟩ := hb
      have hqa := hPP q hq
      rw [peA_val (tbl_fit hqa) hj]; have := hLo q hq; omega)
    (fun q hq => by
      obtain ⟨ao, hao⟩ := hPt.arch hq
      have hqa := hPP q hq
      have := hLo q hq
      exact hkq q (by omega) ao hao)
  -- the rest of the state relation
  have hcpu5 : L.cpu s5 = L.cpu s := by
    have h2 : L.cpu s2 = L.cpu s := by
      have := set_cap_spec (L := L) x s (.Untyped p sb 4096#u64 false)
      rw [hs2, WP.spec_ok] at this; rw [this]; simp
    rw [hs5, L.cpu_wr, hF2.2.1, hs3, L.cpu_zr, h2]
  have hMp : MpStep p σ τf := by
    obtain ⟨ms, hy2, hum⟩ := deleteObjects_mem (by decide) (by decide) (show p.bv.toNat % 8 = 0 by
      show p.val % 8 = 0; omega) (show p.bv.toNat + 2 ^ 12 ≤ 2 ^ 64 from hpfit) hy
    have hO1 : OStep (fun q => q ∈ Fl4Proofs.P3.regionSet p.bv 12) σ y.2 := by
      rw [hy2]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q hq => ?_⟩
      simp only [Fl4Spec.detype] at hq ⊢
      split_ifs at hq ⊢ with h
      · exact ⟨Or.inl h, Or.inl rfl⟩
      · exact absurd rfl hq
    refine ⟨(hO1.trans hOf).mono (fun q h => h.elim id False.elim), fun x hx => ?_, hcrf⟩
    rw [hmsf, hy2]
    exact hum x hx
  have hW5 : ∀ b, P1.Aligned b → ¬ MpW th p (L.ksb s) i b → L.mem s5 b = L.mem s b := (fun b hb hn => by
      have hr : ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) := fun h => hn (Or.inr (Or.inl h))
      have hnv : b ≠ atA K i := fun e => hn (Or.inr (Or.inr (by rw [e])))
      have hns : ¬ ∃ x' k, IsSlot th' x' ∧ Off k ∧ b = wordOf x' k :=
        fun ⟨x', k, hx', hk, e⟩ => hn (Or.inl ⟨x', k, hx'.of_restrict, hk, e⟩)
      rw [hm54 b hb (hpne b hnv), hF2.2.2 b hb hns, hz3 b hb, if_neg hr]
      refine hfr2 b hb (fun e => hn (Or.inl ⟨x, 0#u64, hxs, off0, ?_⟩)) (fun e => hn (Or.inl ⟨x, 8#u64, hxs, off8, ?_⟩))
      · rw [wordOf_zero]; exact UScalar.eq_of_val_eq e
      · apply UScalar.eq_of_val_eq; rw [e, wordOf_val (show x.val + (8#u64).val < 2 ^ 64 by
        have := hxs.fit hPl; simp; omega)]; rfl)
  have hSR5 : SR s5 a τf := hH.mpSR s s5 a σ τf p i hi hS hRO
    (by rw [hksb5]) hcpu5 hW5 hMp
  -- `DelInv`
  have hDI : DelInv th' (L.mem s) → DelInv th' (L.mem s5) := by
    intro D0
    have D1 := delInv_same_mp D0 (fun a ha => hSS a ha.of_restrict)
    have D2 : DelInv th' (L.mem s2) := DelInv.of_kept D1 id (fun y hy p0 zt n h => ⟨hy, by
        show capV _ y = _
        by_cases e : y = x
        · rw [e, RR2.cap] at h; cases h
        · rw [← hco2 y hy e]; exact h⟩) (fun _ _ _ _ hne _ _ _ _ _ _ _ _ => hne)
      (fun y hy h => by
        by_cases e : y = x
        · rw [e, RR2.cap] at h; cases h
        · obtain ⟨l1, l2⟩ := hLK2 y hy
          have := D1.nc y hy (by rw [← hco2 y hy e]; exact h)
          unfold prevOf nextOf at this ⊢; rw [l1, l2]; exact this)
    exact delInv_same_mp (hdi4 (delInv_same_mp D2 hSS3)) hSS5
  have hMid : MpMidB (L := L) th s rc σ p (pd.bv, idxd) (pp.bv, idx) τf th' ((.Ok () : core.result.Result Unit error.Exc), s5, a) := by
    refine ⟨i, hi, by show L.ksb s5 = L.ksb s; rw [hksb5],
      hcpu5, hW5, fun w hw h1 h2 => by
        rw [hm54 w hw (by rw [hAtv]; rcases hTo with e | e <;> omega), hmemR w hw h1 h2],
      L.mem_wr_same hAt, hMp, hkp, hkhf, hcdtf, horf, ?_, ⟨base, ?_⟩, ?_, ?_, hDI, ⟨pp, rs, idx, fi, rfl, hpp, hidx, by rw [← hsb]; exact hcap, hnch⟩,
      pd, rd, idxd, rfl, hpd, hidxd, hdst⟩
    · show capV (L.mem s5) x = _
      rw [hSS5.capV hxs', hctx.cz hxm, RR3.cap, hsb]
    · show capV (L.mem s5) val = _
      rw [hSS5.capV hvs', hctx.cd]
    · intro b hb
      have e : capV (L.mem s5) val = .AsidPool p base := by rw [hSS5.capV hvs', hctx.cd]
      have e2 : capV (L.mem s5) (cslotAddr (pd.bv, idxd)) = .AsidPool p b := hb
      rw [show cslotAddr (pd.bv, idxd) = val from rfl, e] at e2
      cases e2
      exact ⟨by rw [hbase]; omega, by rw [hbase]; omega⟩
    · intro y hy h1 h2
      show capV (L.mem s5) y = _
      rw [hSS5.capV hy, hctx.hcap y hy, if_neg h2, hSS3.capV hy, hco2 y hy h1, hSS.capV hy.of_restrict]
  -- `FinInv`
  have hnd0 := hM.tree.nodup
  have F1 : FinM (L.mem s) G := hFI.fm.of_caps hnd0 (fun z hz => hSS.capV ((hM.members z).1 hz).1)
  have F2 : FinM (L.mem s2) G := F1.recap hnd0 x (by rw [RR2.cap, hcx1]; exact MdbLike.capSim ⟨rfl, rfl, rfl, rfl⟩)
    (fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne)
  have F3 : FinM (L.mem s3) G := F2.of_caps hnd0 (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
  have hfr4 : ∀ w ∈ G.chains.flatten,
      ¬ Ovl (absCap (capV (L.mem s4) val)) (absCap (capV (L.mem s4) w)) ∧
      (isFrame (capV (L.mem s4) val) = true → srB (capV (L.mem s4) val) (capV (L.mem s4) w) = false) ∧
      (isFrame (capV (L.mem s4) w) = true → srB (capV (L.mem s4) w) (capV (L.mem s4) val) = false) := by
    intro w hw
    have hov := not_ovl_pool (q := p) (b := base) (hctx.hreg w hw)
      (fun h => (hctx.hno w hw h).imp id And.left) hctx.hcr
    refine ⟨?_, ?_, ?_⟩
    · rw [hctx.cd, hctx.cz hw]; exact hov
    · intro h; rw [hctx.cd] at h; cases h
    · intro hf
      rw [hctx.cd]
      cases hs : srB (capV (L.mem s4) w) (.AsidPool p base)
      · rfl
      · exact absurd (srB_frame_frame hf hs) (by simp [isFrame])
  have F4 : FinM (L.mem s4) G' := F3.fresh_ins hxm hvm true hM4.tree.nodup (fun z hz => hctx.cz hz) hfr4
  have F5 : FinM (L.mem s5) G' := F4.of_caps hM4.tree.nodup (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  -- `FrameInv`
  have FR1 : Vs.FrameInv (L.mem s) G := hFR.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1)
  have FR2 : Vs.FrameInv (L.mem s2) G := FR1.recap x (by rw [RR2.cap, hcx1]; exact ⟨rfl, rfl, rfl, rfl⟩)
    (fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne)
  have FR3 : Vs.FrameInv (L.mem s3) G := FR2.of_caps (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
  have FR4 : Vs.FrameInv (L.mem s4) G' := FR3.insert_fresh hxm hvm true hctx.cd
    (by rw [hctx.cz hxm]; exact MdbLike.refl _) (fun z hz _ => hctx.cz hz) (fun _ _ _ _ _ _ h => by cases h)
    (fun y hy _ _ _ _ _ _ hc q h1 h2 => Vs.pool_out hc (hctx.hreg y hy)
      (fun h => (hctx.hno y hy h).imp id And.left) hctx.hcr q h1 h2)
  have FR5 : Vs.FrameInv (L.mem s5) G' := FR4.of_caps (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  have VC : ∀ P' L4' L3' L2' L1' : Set U64, Vs.VsCapsIn P' L4' L3' L2' L1' (L.mem s) G →
      Vs.VsCapsIn (insert p P') L4' L3' L2' L1' (L.mem s5) G' := fun P' L4' L3' L2' L1' hVC => by
    have V1 := hVC.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1)
    have V2 := V1.recap x (by rw [RR2.cap]; trivial) (fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne)
    have V3 := V2.of_caps (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
    have V4 := V3.insert_fresh (P' := insert p P') (L4' := L4') (L3' := L3') (L2' := L2') (L1' := L1')
      (Set.subset_insert _ _) subset_rfl subset_rfl subset_rfl subset_rfl hxm true
      (by rw [hctx.cd]; exact Vs.vcap_pool hbase hi hp0) (by rw [hctx.cz hxm]; exact id) (fun z hz _ _ => hctx.cz hz)
    exact V4.of_caps (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  -- the MDB step and the VSpace MDB invariant
  have hrv2 : ∀ z ∈ G.chains.flatten, revOf (L.mem s2) z = revOf (L.mem s) z := fun z hz => by
    have hzs := ((hM.members z).1 hz).1
    have a1 := hzs.align hPl; have f1 := hzs.fit hPl; have a2 := hxs.align hPl; have f2 := hxs.fit hPl
    have hv : (wordOf z 24#u64).val = z.val + 24 := wordOf_val (by simp; omega)
    unfold revOf
    rw [hfr2 (wordOf z 24#u64) (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
  have hco2' : ∀ z ∈ G.chains.flatten, z ≠ x → capV (L.mem s2) z = capV (L.mem s) z :=
    fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne
  have hrv4 : ∀ z ∈ G.chains.flatten, revOf (L.mem s4) z = revOf (L.mem s3) z := fun z hz => by
    rw [hctx.hrev z ((RR3.M.members z).1 hz).1, if_neg (fun e : z = val => hvm (e ▸ hz))]
  have hf4 : (4096#u64 : U64).val = 2 ^ sb.val := by rw [h2sb]; rfl
  have MS : MdbStep (L.mem s) G (L.mem s5) G' :=
    (MdbStep.of_same hM hSS).trans <|
    (MdbStep.setFi hM hI hxm hcx1 RR2.cap hf' (Or.inr hnd) hco2' hrv2).trans <|
    (MdbStep.of_same RR2.M hSS3).trans <|
    (MdbStep.pool RR3.M RR3.I hxm RR3.cap hf4 hnd hvm hctx.cd hbA htA (fun z hz => hctx.cz hz) hrv4
      ⟨by rw [hbase]; omega, by rw [hbase]; omega, hp0⟩).trans <|
    MdbStep.of_same hM4 hSS5
  have VM : ∀ ksb : U64, Vs.VsMdbInv ksb (L.mem s) G → Vs.VsMdbInv ksb (L.mem s5) G' := fun ksb h0 => by
    have W1 := h0.keep (fun z hz => hSS.capV ((hM.members z).1 hz).1)
    have W2 := W1.setFi hcx1 RR2.cap hco2'
    have W3 := W2.keep (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
    have W4 := W3.pool hxm hctx.cd ⟨by rw [hbase]; omega, by rw [hbase]; omega, hp0⟩ (fun z hz => hctx.cz hz)
    exact W4.keep (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  refine ⟨τf, th', G', by rw [hrun]; exact hmem, by rw [hrun]; exact hall.1, hP', hR5, hV5, hM5, hC5,
    MdbInv.of_same hM4 hI4 hSS5, UtInv.of_same hM4 hU4 hSS5, by rw [hksb5]; exact hVs5, hPt5, hSR5, ⟨hKTf, F5⟩, FR5, VC,
    MS, VM, hMp.1.ct, by rw [hth', h2sb],
    by rw [hksb5], ?_, ⟨hpal, hpfit, hp0, hN, hns, hcn, hPo, hLo, hTo⟩,
    ⟨x, fi, hxm, by rw [← hsb]; exact capV_of_capAt hcap, hnd⟩, ?_, hMid⟩
  · -- no new SC
    intro q y n hk
    have e := hMp.1.keep' (q := q.bv) (by
      rw [hk]; rintro (h | ⟨r, cs, h⟩ | ⟨ao, h⟩) <;> cases h)
    rw [e] at hk
    exact ⟨y, hk⟩
  -- the pools' entries: the new pool's zero, the others' kept
  intro L4' hPI q hq lo hl hne
  rcases hq with rfl | hq
  · exact absurd (hz5 lo hl) hne
  have hw : VsWrite P K (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
  have hal := VsWrite.aligned hVP hw
  obtain ⟨-, qf⟩ := hVP.pal q hq
  have hnv : peA q lo ≠ atA K i := fun e => by
    have := congrArg UScalar.val e
    rw [peA_val qf hl, atA_val hVP.ksb_fit hi] at this
    have := hVP.ptab q hq; omega
  have e : L.mem s5 (peA q lo) = L.mem s (peA q lo) := by
    rw [hm54 _ hal (hpne _ hnv), hmem41 _ hal (hVO _ hw) (hVout _ hw)]
  rw [e] at hne ⊢
  exact hPI q hq lo hl hne

set_option maxHeartbeats 4000000 in
/-- **`MakePool`'s perform refines l4v** (see the module docstring): from the
state after the decode checks (an untyped cap of `ASID_POOL` bits, not a
device, without children, at `(pp, idx)`; an empty target slot; the first
free table entry `i`), FL4's result is related to an outcome of l4v's
`set_thread_state Restart` and `perform_asid_control_invocation`, which
does not fail (`MpPost`). -/
theorem mp_perform_rel {A : Type} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (ct : U64) (hcur : ct.bv = σ.curThread) {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} (hsb : sb = fl4_abi.consts.bits.ASID_POOL)
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx))
    {pd : U64} {rd : Nat} (hpd : th pd = some (.cnode rd)) {idxd : List Bool} (hidxd : idxd.length = rd)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    {i base : U64} (hi : i.val < 2048) (hbase : base.val = i.val * 512)
    (hRg : MpRegion th G P L4 L3 L2 L1 (L.ksb s) p) (hRO : RegOK s σ p)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b) (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) {rc : capability.Cap} (hCn : CnRef th (L.mem s) rc pd) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let i1 ← lift (sb &&& 63#u64)
      let i2 ← 1#u64 <<< i1
      let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s1 (capability.Cap.Untyped p sb i2 false)
      let s3 ← st.clear_free s2 p 4096#u64
      let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
      let s5 ← vspace.set_asid_table st s4 i p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = a ∧ MpPost (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G s rc σ p (pd.bv, idxd) (pp.bv, idx) base.bv res ⦄ := by
  have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hidxd] using hpd)⟩
  refine WP.spec_bind (spec_eq_mp (WP.spec_and (hH.restart s a σ ct xct hS hR hPt hcur hkt' htcb hact hrun)
    (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact))) ?_
  rintro s1 ⟨hs1e, ⟨hR1, hPt1, hS1, hksb1, hcpu1, hRO1⟩, hSS⟩
  set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) :=
    Notif.setThreadState_eq .restart hkt'
  have hKT1 : KTyped th σ1 := hFI.kt.sub (ksub_of_eq (setThreadState_nks _ _) hst)
  obtain ⟨σ1', hst', hSt1, hSV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hSt hSV hM hC hSS hkt' .restart
  have e1 : σ1' = σ1 := by
    rw [hst] at hst'
    have := congrArg Prod.fst hst'
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  rw [e1] at hSt1 hC1 hcdt1 hio1
  clear e1 hst' σ1'
  have hI1 := MdbInv.of_same hM hI hSS
  have hU1 := UtInv.of_same hM hU hSS
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) := by
    rw [hSS.capAt hAs.isSlot]; exact hcap
  have hdst1 : capAt (L.mem s1) (cslotAddr (pd.bv, idxd)) = ok .Null := by rw [hSS.capAt hAd.isSlot]; exact hdst
  have hnch1 : ¬ ∃ sl, σ1.cdt sl = some (pp.bv, idx) := by rw [hcdt1]; exact hnch
  have hcG : ∀ z ∈ G.chains.flatten, capV (L.mem s1) z = capV (L.mem s) z := fun z hz => hSS.capV ((hM.members z).1 hz).1
  have hFI1 : FinInv th (L.mem s1) σ1 G := ⟨hKT1, hFI.fm.of_caps hM.tree.nodup hcG⟩
  have hFR1 : Vs.FrameInv (L.mem s1) G := hFR.of_caps hcG
  have hVP1 : VsPlaced P (L.ksb s1) := by rw [hksb1]; exact hVP
  have hRg1 : MpRegion th G P L4 L3 L2 L1 (L.ksb s1) p := by rw [hksb1]; exact hRg
  have hVO1 : ∀ b, VsWrite P (L.ksb s1) b → OutsideObjects th b := by rw [hksb1]; exact hVO
  have hPV1 : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s1) b := by rw [hksb1]; exact hPV
  refine WP.spec_mono (mp_perform_relB (L := L) hH s1 a σ1 G hPl hSt1 hSV1 hM1 hC1 hI1 hU1 hR1 hPt1 hS1 hVP1 hPP hpp
    hidx hsb hcap1 hnch1 hpd hidxd hdst1 hi hbase hRg1 (hRO1 p hRO) hVO1 hPO hPV1 hFI1 hFR1 (rc := rc)) ?_
  rintro res ⟨h1, h2, σ', th', G', hm, hnf, hP', hR', hV', hM', hC', hI', hU', hVs', hPt', hSR', hF', hFR', hVC, hMS,
    hVM, hct', hth', hk', hsc, -, -, hPI, hMid⟩
  have hrun : (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ =
      (Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ1 := by
    rw [← hcur, nd_bind_one hst]
  have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)) := nodesc_of_cdt hPl hC1 hAs hnch1
  have hct1 : σ1.curThread = σ.curThread := by rw [hσ1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hpools1 : ∀ q ∈ P, σ1.kheap q.bv = σ.kheap q.bv := by
    intro q hq
    obtain ⟨g, hg, -⟩ := hR.pool q hq
    have : q.bv ≠ ct.bv := Endp.kheap_ne hg hkt' (fun _ h1 h2 => by subst h1; cases h2)
    rw [hσ1, Notif.stsAct_kheap]; simp [this]
  have ht1 : σ1.archState.x64AsidTable = σ.archState.x64AsidTable := by
    rw [hσ1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hR1' : VsRel P (L.mem s1) (L.ksb s) σ1 := by rw [← hksb1]; exact hR1
  have hw1 := Vs.VsRel.words_eq hR hR1' ht1 hpools1
  obtain ⟨hi', hh, hks, hcpu, hW, hz, htab, hMs, hkp, hkh, hcdt, hor, hsrc, hdst', hdstb, hcapK, hDI, -, -⟩ := hMid
  refine ⟨h1, h2, σ', th', G', by rw [hrun]; exact hm, by rw [hrun]; exact hnf, hP', hR', hV', hM', hC', hI', hU', hVs',
    hPt', hSR', hF', hFR', fun P' L4' L3' L2' L1' h => hVC _ _ _ _ _ (h.of_caps hcG), (MdbStep.of_same hM hSS).trans hMS,
    fun ksb h0 => hVM ksb (h0.keep hcG), hct'.trans hct1, hth', hk'.trans hksb1, fun q y n hq => ?_, hRg,
    ⟨_, fi, hxm, by rw [← hsb]; exact capV_of_capAt hcap, hnd⟩, fun L4' h0 => hPI L4' (fun q hq lo hl hne => ?_), ?_⟩
  · obtain ⟨y0, hy0⟩ := hsc q y n hq
    by_cases e : q.bv = ct.bv
    · rw [e, hσ1, Notif.stsAct_kheap] at hy0; simp at hy0
    · refine ⟨y0, ?_⟩
      rw [hσ1, Notif.stsAct_kheap] at hy0; simp only [Notif.updK, Function.update_of_ne e] at hy0; exact hy0
  · have hw : VsWrite P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hw1 _ hw] at hne ⊢
    exact h0 q hq lo hl hne
  · refine ⟨s1, ct, hi', σ1, hs1e, hcur, by rw [← hcur]; exact hst, hh, hks, hcpu, hW, hz, htab, hMs, hkp, hkh, hcdt,
      hor, hsrc, hdst', hdstb, fun y hy e1 e2 => (hcapK y hy e1 e2).trans (hSS.capV (by rw [hth'] at hy; exact hy.of_restrict)),
      fun D0 => hDI (delInv_same_mp D0 (fun a ha => hSS a (by rw [hth'] at ha; exact ha.of_restrict))),
      ⟨pp, rs, idx, fi, rfl, hpp, hidx, by rw [← hsb]; exact hcap, hnch⟩, pd, rd, idxd, rfl, hpd, hidxd, hdst, hCn⟩

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The post of `MakePool`'s decode and perform, against the spec's decode
outcome `D`: an error, as the spec's, the state unchanged; or one of the
spec's invocations, with no failure, performed (`MpPost`). -/
def MpDecPost {A : Type} (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (th0 : TypedHeap) (k0 : U64) (m0 : U64 → U64) (G0 : MdbGhost) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (D : Set (Except Fl4Spec.SyscallError Fl4Spec.ArchInvocation × Fl4Spec.State Unit) × Prop)
    (s : S) (a : A) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧ D = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
  (res.1 = .Ok () ∧ ∃ (p : U64) (dest ps : Fl4Spec.CslotPtr) (base : Fl4Spec.Asid),
    (.ok (.invokeASIDControl (.makePool p.bv dest ps base)), σ) ∈ D.1 ∧ ¬ D.2 ∧
    MpPost (L := L) P L4 L3 L2 L1 SR th0 k0 m0 G0 s rc σ p dest ps base res)

/-- `MpDecPost` with any post `Post` of the perform (`makepool_relP`): an error, as the spec's, the state unchanged; or one of the
spec's invocations, with no failure, performed (`MpPost`). -/
def MpDecPostP {A : Type}
    (Post : U64 → Fl4Spec.CslotPtr → Fl4Spec.CslotPtr → Fl4Spec.Asid → core.result.Result Unit error.Exc × S × A → Prop)
    (σ : Fl4Spec.State Unit) (D : Set (Except Fl4Spec.SyscallError Fl4Spec.ArchInvocation × Fl4Spec.State Unit) × Prop)
    (s : S) (a : A) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧ D = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
  (res.1 = .Ok () ∧ ∃ (p : U64) (dest ps : Fl4Spec.CslotPtr) (base : Fl4Spec.Asid),
    (.ok (.invokeASIDControl (.makePool p.bv dest ps base)), σ) ∈ D.1 ∧ ¬ D.2 ∧
    Post p dest ps base res)

/-- **`makepool_rel` with any perform** (`hPf`, its post `Post`; for the
dirty case of XTopJointMakePoolD): FL4's error is the spec decode's single outcome, or the
spec decodes an invocation (FL4's choice of the free table entry, the first,
among l4v's), with no failure, and `MpPost` holds. -/
theorem makepool_relP {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (slot : obj.Slot) (call : Bool)
    (ex : Array obj.Slot 3#usize)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    (hex0 : vspace.extra ex 0#usize = ok (some (cslotAddr (pp.bv, idx))))
    {y : obj.Slot} (hex1 : vspace.extra ex 1#usize = ok (some y))
    {uc : capability.Cap} (hcx : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc) {uc' : Fl4Spec.Cap}
    (hur : CapRel uc uc')
    {rc : capability.Cap} (hcy : capAt (L.mem s) y = ok rc) {rc' : Fl4Spec.Cap} (hrr : CapRel rc rc')
    (hrv : CapValid th rc)
    (ysl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {Post : U64 → Fl4Spec.CslotPtr → Fl4Spec.CslotPtr → Fl4Spec.Asid → core.result.Result Unit error.Exc × S × A → Prop}
    (hPf : ∀ (p sb fi : U64), sb = fl4_abi.consts.bits.ASID_POOL →
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      ∀ (pd : U64) (rd : Nat) (idxd : List Bool), th pd = some (.cnode rd) → idxd.length = rd →
      capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null → CnRef th (L.mem s) rc pd →
      ∀ (i base : U64), i.val < 2048 → base.val = i.val * 512 →
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let i1 ← lift (sb &&& 63#u64)
        let i2 ← 1#u64 <<< i1
        let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s1 (capability.Cap.Untyped p sb i2 false)
        let s3 ← st.clear_free s2 p 4096#u64
        let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
        let s5 ← vspace.set_asid_table st s4 i p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
        res.1 = .Ok () ∧ res.2.2 = a ∧ Post p (pd.bv, idxd) (pp.bv, idx) base.bv res ⦄) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDControlMakePool length slot .AsidControl call buf ex ⦃ res =>
      MpDecPostP Post σ (ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
        (args.map UScalar.bv) xs cte .asidControlCap ((uc', (pp.bv, idx)) :: (rc', ysl) :: rest)) σ) s a res ⦄ := by
  unfold vspace.decode
  rw [hct]
  apply ok_bind_spec
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hex0, hex1]
  simp only [bind_ok]
  by_cases hl2 : length >= 2#u64
  swap
  · rw [if_neg hl2]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, Or.inl trivial, ?_, rfl, rfl⟩)
    have h2 : ¬ 1 < (args.map UScalar.bv).length := by
      rw [List.length_map, ← hlen]; intro h; apply hl2
      show (2#u64).val ≤ length.val; simp; omega
    unfold Fl4Spec.archDecodeInvocation
    dsimp only
    rw [if_pos hl, if_neg (fun h => h2 h.1)]; rfl
  rw [if_pos hl2]
  obtain ⟨a0, a1, rs', rfl⟩ : ∃ a0 a1 r, args = a0 :: a1 :: r := by
    have : 2 ≤ args.length := by rw [← hlen]; have := hl2; simp at this; scalar_tac
    match args, this with
    | a0 :: a1 :: r, _ => exact ⟨a0, a1, r, rfl⟩
  rw [hargs 0#u64 a0 rfl, hargs 1#u64 a1 rfl]
  simp only [bind_ok]
  rw [slot_cap_eq, hcx, slot_cap_eq, hcy]
  simp only [bind_ok, List.map_cons]
  refine WP.spec_bind (decode_loop0_spec (L := L) s) ?_
  rintro i ⟨hi5, hall, hfree⟩
  have hN2 : vspace.N_ASID_POOLS = 2048#u64 := by unfold vspace.N_ASID_POOLS; rfl
  rw [hN2]
  by_cases hi2 : i = 2048#u64
  · rw [if_pos hi2]
    have hF := table_full_of_none hR (fun j hj => hall j (by rw [hi2]; simpa using hj))
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, Or.inl trivial, mp_full hl _ _ _ _ _ _ _ _ _ _ σ hF,
      rfl, rfl⟩)
  rw [if_neg hi2]
  have hi : i.val < 2048 := by
    have : i.val ≠ 2048 := fun h => hi2 (UScalar.eq_of_val_eq h)
    omega
  have hfi := table_free_of_found hR hi (hfree hi)
  have hF : (Fl4Spec.dom σ.archState.x64AsidTable)ᶜ ≠ ∅ := fun h => by rw [h] at hfi; exact hfi
  have hsel := mp_sel hl (UScalar.bv a0) (UScalar.bv a1) (rs'.map UScalar.bv) xs cte uc' (pp.bv, idx) rc' ysl rest σ hF
  step as ⟨base, hbase⟩
  have hbv : base.val = i.val * 512 := by
    have h9 : vspace.ASID_LOW_BITS.val = 9 := by unfold vspace.ASID_LOW_BITS; rfl
    rw [hbase, h9, Nat.shiftLeft_eq]
    simp only [U64.size_def, U64.numBits, UScalarTy.U64_numBits_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hbase' : (Fl4Spec.ucast Fl4Spec.asidRepLen (Fl4Spec.ucast 11 i.bv : BitVec 11) <<< Fl4Spec.asidLowBits :
      BitVec 64) = base.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [Fl4Spec.ucast, Fl4Spec.asidLowBits, Fl4Spec.asidLowLen, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    show (i.val % 2 ^ 11 % 2 ^ 64 * 2 ^ 9) % 2 ^ 64 = base.val
    rw [hbv, Nat.mod_eq_of_lt (show i.val < 2 ^ 11 by omega), Nat.mod_eq_of_lt (show i.val < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  -- the untyped cap
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hbad : (∀ p n fi, uc' ≠ .untypedCap false p n fi) → (Fl4Spec.SyscallError.invalidCapability 1 :
      Fl4Spec.SyscallError) = .invalidCapability 1 → ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
        (UScalar.bv a0 :: UScalar.bv a1 :: rs'.map UScalar.bv) xs cte .asidControlCap
        ((uc', (pp.bv, idx)) :: (rc', ysl) :: rest)) σ = ({(.error (.invalidCapability 1), σ)}, False) :=
    fun h _ => by rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_bad h)
  cases uc with
  | Untyped p sb fi dev =>
    have huc : uc' = .untypedCap dev p.bv sb.val fi.val := hur.abs
    subst huc
    cases dev
    swap
    · simp only [↓reduceIte, error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩,
        hbad (fun p n fi h => by cases h) rfl, rfl, rfl⟩)
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hsb : sb = fl4_abi.consts.bits.ASID_POOL
    swap
    · rw [if_neg hsb]
      simp only [error.invalid_cap, bind_ok]
      have hsbv : sb.val ≠ Fl4Spec.pageBits := fun h => hsb (UScalar.eq_of_val_eq (by
        rw [h]; unfold fl4_abi.consts.bits.ASID_POOL; rfl))
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩, ?_, rfl, rfl⟩)
      rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_size hsbv)
    rw [if_pos hsb]
    have hsbv : sb.val = Fl4Spec.pageBits := by rw [hsb]; unfold fl4_abi.consts.bits.ASID_POOL; rfl
    rw [hsbv] at hsel ⊢
    -- no children
    have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcx, by simp⟩
    have hnc := noChildren_of_adj (st := st) th hPl s σ G hM hC (hI.parentAdj (th := th)) (pp.bv, idx) hAs hxm
    unfold NoChildrenRel at hnc
    rw [hnc]
    simp only [bind_ok]
    by_cases hch : ∃ x, σ.cdt x = some (pp.bv, idx)
    · rw [if_pos hch]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .revokeFirst, rfl, Or.inl trivial,
        by rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_children hch), rfl, rfl⟩)
    rw [if_neg hch]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    -- the target slot
    unfold cspace.lookup_target_slot
    obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
      (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hSt hSV false rc rc' hrr hrv a0 a1)
    rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) rc' (Fl4Spec.toBl a0.bv) (Fl4Spec.unat a1.bv)).run σ =
        ({(e1, σ)}, False) := he1
    cases r1 with
    | Err e =>
      cases e1 with
      | ok _ => exact hrel1.elim
      | error e' =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, e', rfl, Or.inl hrel1,
          by rw [hsel]; exact mpSel_const hF (fun f _ => by rw [mpRest_slot hch hlt]), rfl, rfl⟩)
    | Ok dest =>
      cases e1 with
      | error _ => exact hrel1.elim
      | ok dsl =>
        obtain ⟨rfl, pd, hpd1, hpd, hcn1⟩ := hrel1
        obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hSt.slot_cap (Z := Unit) hpd1 hpd
        unfold cdt.ensure_empty_slot
        simp only [slot_cap_eq, hcd, bind_ok]
        have hee := ensureEmpty_run dsl σ hgd
        by_cases hdn : cd = .Null
        swap
        · rw [cap_is_null_ne hdn]
          simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
            core.convert.FromSame.from, bind_tc_ok]
          have : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
          simp only [this, ↓reduceIte] at hee
          exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, Or.inl trivial,
            by rw [hsel]; exact mpSel_const hF (fun f _ => mpRest_full hch hlt hee), rfl, rfl⟩)
        subst hdn
        have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
        simp only [hadn, ↓reduceIte] at hee
        rw [cap_is_null_null]
        simp only [bind_ok, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨o, idxd⟩ := dsl
        simp only at hpd1 hpd
        subst hpd1
        refine WP.spec_mono (hPf p sb fi hsb hcx hch pd _ idxd hpd rfl hcd hcn1 i base hi hbv) ?_
        rintro res ⟨h1, -, hpost⟩
        have hk : ExceptT.run (mpRest a0.bv a1.bv (.untypedCap false p.bv Fl4Spec.pageBits fi.val) (pp.bv, idx) rc'
            (Fl4Spec.ucast Fl4Spec.asidRepLen (Fl4Spec.ucast 11 i.bv : BitVec 11) <<< Fl4Spec.asidLowBits)) σ =
            ({(.ok (.invokeASIDControl (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)), σ)}, False) := by
          rw [mpRest_ok hch hlt hee, hbase']
        have hm := mpSel_mem hfi hk (fun f' _ => by rw [mpRest_ok hch hlt hee]; exact id)
        rw [← hsel] at hm
        exact Or.inr ⟨h1, p, (pd.bv, idxd), (pp.bv, idx), base.bv, hm.1, hm.2, hpost⟩
  | _ =>
    simp only [error.invalid_cap, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inr ⟨1#u64, rfl, rfl⟩,
      hbad (fun p n fi h => by rw [hur.abs] at h; simp [absCap] at h) rfl, rfl, rfl⟩)

/-- **ASIDControl `MakePool` refines l4v** (decode and perform; for the
extra caps present): FL4's error is the spec decode's single outcome, or the
spec decodes an invocation (FL4's choice of the free table entry, the first,
among l4v's), with no failure, and `MpPost` holds. -/
theorem makepool_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (slot : obj.Slot) (call : Bool)
    (ex : Array obj.Slot 3#usize)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    (hex0 : vspace.extra ex 0#usize = ok (some (cslotAddr (pp.bv, idx))))
    {y : obj.Slot} (hex1 : vspace.extra ex 1#usize = ok (some y))
    {uc : capability.Cap} (hcx : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc) {uc' : Fl4Spec.Cap}
    (hur : CapRel uc uc')
    {rc : capability.Cap} (hcy : capAt (L.mem s) y = ok rc) {rc' : Fl4Spec.Cap} (hrr : CapRel rc rc')
    (hrv : CapValid th rc)
    (ysl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hRg : ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOK s σ p) (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDControlMakePool length slot .AsidControl call buf ex ⦃ res =>
      MpDecPost (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G rc σ (ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
        (args.map UScalar.bv) xs cte .asidControlCap ((uc', (pp.bv, idx)) :: (rc', ysl) :: rest)) σ) s a res ⦄ := by
  refine WP.spec_mono (makepool_relP (L := L) hH s a σ G hPl hSt hSV hM hC hI hU hR hPt hS hVP hPP hVO hPO hPV ct hct
    hcur hkt hrun htcb hact hl length buf args hlen hargs xs cte slot call ex hpp hidx hex0 hex1 hcx hur hcy hrr hrv ysl rest
    (Post := fun p dest ps base res => MpPost (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G s rc σ p dest ps base res)
    (fun p sb fi hsb hcap hnch pd rd idxd hpd hld hnull hCn i base hi hbase => by
      have huc : uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false := by
        subst hsb; exact eq_of_ok_eq (hcx.symm.trans hcap)
      exact mp_perform_rel (L := L) hH s a σ G hPl hSt hSV hM hC hI hU hR hPt hS hVP hPP ct hcur hkt hrun htcb hact hpp
        hidx hsb hcap hnch hpd hld hnull hi hbase (hRg p fi huc hnch).1 (hRg p fi huc hnch).2 hVO hPO hPV hFI hFR hCn))
    (fun res h => h)

end

end

end Fl4Proofs.P3.Vs
