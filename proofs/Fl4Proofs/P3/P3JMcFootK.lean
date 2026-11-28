/-
P3 (p3J gen 20): **the `…Foot` premises without ghosts and without `KhNoneKeep`** (gen 19's open items 1 and 3 of
the weak point: `UtKeep` at every outcome MDB ghost, and the spec-side `KhNoneKeep`).

* **Finding (the MDB ghost's members are determined by memory).** `JAtZ.mdbL` gives `MdbLinks Z.th (L.mem s) Z.G`,
  whose `members` says `x ∈ G.chains.flatten ↔ IsSlot Z.th x ∧ capAt (L.mem s) x` non-null. `UtKeep` reads `G'` only
  through `G'.chains.flatten`, so at every `JAtZ (Z.mv G' V')` outcome it is the ghost-free **`UtMem Z.th s s'`**
  (every slot of the typed heap holding a RAM untyped cap at `s'` held the same cap at `s`):
  **`utKeep_of_utMem`** and **`utMem_of_utKeep`** (both directions). So gen 19's `∀ G'` in `IrqFoot` / `FootAt` was
  not a vacuity risk; the new premises state `UtMem` (no ghost at all).
* **`KhNoneKeep` is not needed.** `ForeignIdle` asks only that the two foreign idle addresses hold no spec object
  at the outcome. `JAtZ` at the outcome already excludes every object kind there except a *malformed* CNode:
  a TCB by `ObjCover.tcb` + `zH` (TCB of `H`), an endpoint / notification / reply / arch object by `SpecCover`
  (object of `H`), an SC by `ObjCover.sc` + `c0` + `JPlaced.sc` (SC of `H`), a well-formed CNode by `FinInv.kt`
  (`KTyped`) + `JPlaced.cnode` (object of `H`); the idle objects are apart from `H` (`ForeignIdle.tH` / `sH`, `H`
  unchanged). **`kh_none_of_apart`**. What is left: **`CnWF σ'`** (every spec CNode well formed, l4v `valid_objs` →
  `valid_cs` → `well_formed_cnode_n`; a single-state invariant of the spec, not FL4).
* **`ForeignIdle.stepK`** (`ForeignIdle.step` with the two outcome facts for `KhNoneKeep`), **`jAtMcW_stepK`**
  (`UtMem` and `CnWF` for `UtKeep` and `KhNoneKeep`), **`runMcW_of_stK`**.
* **`IrqFootK` / `UserFootK` / `VmfFootK` / `SysUFootK` [J]**: at every `JAtZ` ghosts of the entry state, the clause's
  run writes only `ProjW H Cs s`, keeps `UtMem Z.th s`, and every outcome spec state is `CnWF`. Ghost-free; the FL4
  part is a pure footprint statement. **`kernel_entry_runMcW_irqK` / `_userK` / `_vmfK` / `_sysUK`**.

Named premises: `IrqFootK`, `UserFootK`, `VmfFootK`, `SysUFootK` [J] (above); U45nv's globals as in
`kernel_entry_runCK`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStEvTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **No new RAM untyped cap at a slot of the typed heap** (ghost-free `UtKeep`, module docstring). -/
def UtMem (th : TypedHeap) (s s' : S) : Prop :=
  ∀ x, IsSlot th x → ∀ p sb fi, capV (L.mem s') x = .Untyped p sb fi false → capV (L.mem s) x = .Untyped p sb fi false

/-- **Every spec CNode well formed** (l4v `valid_objs` → `valid_cs` → `well_formed_cnode_n`). -/
def CnWF (σ : Fl4Spec.State Unit) : Prop :=
  ∀ o r cs, σ.kheap o = some (.cnode r cs) → Fl4Spec.wellFormedCnodeN r cs

variable {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop}

theorem untyped_ne_null {p sb fi : U64} {d : Bool} : (capability.Cap.Untyped p sb fi d) ≠ capability.Cap.Null :=
  fun h => by cases h

/-- **`UtMem` gives `UtKeep` at every outcome ghost** (module docstring). -/
theorem utKeep_of_utMem {Z : XSets} {H : P1.Heap} {Cs Ac Ac' : Set U64} {Lst Lst' : U64 → List U64} {D D' : Set U64}
    {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {G' : MdbGhost} {V' : XVs}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ') (h : UtMem (L := L) Z.th s s') :
    UtKeep (L := L) Z.G G' s s' := by
  intro x hx p sb fi hc
  have hsl : IsSlot Z.th x := ((J'.mdbL.members x).1 hx).1
  have hc0 := h x hsl p sb fi hc
  exact ⟨(J.mdbL.members x).2 ⟨hsl, _, by rw [capAt_capV, hc0], untyped_ne_null⟩, hc0⟩

/-- **`UtKeep` at an outcome ghost gives `UtMem`** (the converse: nothing is lost). -/
theorem utMem_of_utKeep {Z : XSets} {H : P1.Heap} {Cs Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64}
    {s s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {G' : MdbGhost} {V' : XVs}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ') (h : UtKeep (L := L) Z.G G' s s') :
    UtMem (L := L) Z.th s s' := by
  intro x hsl p sb fi hc
  exact (h x ((J'.mdbL.members x).2 ⟨hsl, _, by rw [capAt_capV, hc], untyped_ne_null⟩) p sb fi hc).2

theorem not_apart_self {q : U64} {n m : Nat} (hn : 0 < n) (hm : 0 < m) : ¬ Apart q.val n q.val m := by
  unfold Apart; omega

/-- **No spec object at an address apart from `H`, at a `JAtZ` state with `CnWF`** (module docstring). -/
theorem kh_none_of_apart {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hCn : CnWF σ)
    {q : U64} {n : Nat} (hn : 0 < n) (hq : ∀ p k, H p = some k → Apart p.val (2 ^ k.bits) q.val n) :
    σ.kheap q.bv = none := by
  have hH : ∀ k, H q ≠ some k := fun k e => not_apart_self (Nat.two_pow_pos _) hn (hq q k e)
  have hqq : (⟨q.bv⟩ : U64) = q := rfl
  obtain ⟨Tr, Cq, hP⟩ := J.jpl
  cases hk : σ.kheap q.bv with
  | none => rfl
  | some ko =>
    exfalso
    cases ko with
    | cnode r cs =>
      have h1 := (J.xtop.rel.2.2.1.kt q.bv).1 r cs hk (hCn _ r cs hk)
      rw [hqq] at h1
      exact hH _ (hP.cnode q r h1)
    | tcb x =>
      obtain ⟨t, ht, e⟩ := J.obj.tcb q.bv x hk
      have : t = q := UScalar.eq_of_val_eq (congrArg BitVec.toNat e)
      subst this
      exact hH _ (J.zH.1 t ht)
    | endpoint x => exact hH _ (by have := J.cover.ep q.bv x hk; rwa [hqq] at this)
    | notification x => exact hH _ (by have := J.cover.ntfn q.bv x hk; rwa [hqq] at this)
    | reply x => exact hH _ (by have := J.cover.reply q.bv x hk; rwa [hqq] at this)
    | archObj ao =>
      obtain ⟨m, -, hm⟩ := J.cover.arch q.bv ao hk
      rw [hqq] at hm; exact hH _ hm
    | schedContext y k =>
      obtain ⟨c, hc, e⟩ := J.obj.sc q.bv y k hk
      have : c = q := UScalar.eq_of_val_eq (congrArg BitVec.toNat e)
      subst this
      exact hH _ (hP.sc c y k (J.c0 c hc) hk).2

variable {H : P1.Heap} {Cs : Set U64} {s s' : S}

/-- **`ForeignIdle.step` with `KhNoneKeep` replaced by the outcome's two idle words** (module docstring). -/
theorem ForeignIdle.stepK {T : Set U64} {Z Z' : XSets} {σ σ' : Fl4Spec.State Unit} {c : U64}
    (hth : Z'.th = Z.th) (hT : Z'.T = Z.T) (hC : Z'.C = Z.C)
    (F : ForeignIdle (L := L) Z H Cs s σ c) (FW : FIdleW (L := L) s c) (hc : c ∈ Cs) (hne : c ≠ L.cpu s)
    (hNP : NodePlaced st T s c)
    (hnd : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val)
    (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s)) (hK1 : σ'.kheap (idleOf (L := L) s c).bv = none) (hK2 : σ'.kheap (idleScOf (L := L) s c).bv = none) (hU : UtKeep (L := L) Z.G Z'.G s s') :
    ForeignIdle (L := L) Z' H Cs s' σ' c ∧ FIdleW (L := L) s' c := by
  have e1 : idleOf (L := L) s' c = idleOf (L := L) s c :=
    keep_idleWord (o := layout.node.IDLE_THREAD) hW hc hne hNP (Or.inl (by unfold layout.node.IDLE_THREAD; rfl)) hnd
  have e2 : idleScOf (L := L) s' c = idleScOf (L := L) s c :=
    keep_idleWord (o := layout.node.IDLE_SC) hW hc hne hNP (Or.inr (by unfold layout.node.IDLE_SC; rfl)) hnd
  have hks := hW.1
  have kt : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (idleOf (L := L) s c) K) =
        L.mem s (core.num.U64.wrapping_add (idleOf (L := L) s c) K) := fun K hK h8 =>
    keep_off hW hK (by have := FW.tal; omega) FW.tfit F.tH F.tKs F.tN
  have ks : ∀ K : U64, K.val < 128 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (idleScOf (L := L) s c) K) =
        L.mem s (core.num.U64.wrapping_add (idleScOf (L := L) s c) K) := fun K hK h8 =>
    keep_off hW hK (by have := FW.sal; omega) FW.sfit F.sH F.sKs F.sN
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have h := F.tSt; rw [e1]; unfold P1.stA layout.tcb.STATE layout.tcb.F at h ⊢
    rw [kt _ (by decide) (by decide)]; exact h
  · have h := F.tAff; rw [e1]; unfold affA at h ⊢; rw [kt _ (by decide) (by decide)]; exact h
  · have h := F.tSc; rw [e1, e2]; unfold scA at h ⊢; rw [kt _ (by decide) (by decide)]; exact h
  · have h := F.sTcb; rw [e1, e2]; unfold scTcbA layout.sc.TCB at h ⊢; rw [ks _ (by decide) (by decide)]; exact h
  · have h := F.sCore; rw [e2]; unfold scCoreA layout.sc.CORE at h ⊢; rw [ks _ (by decide) (by decide)]; exact h
  · rw [e1]; exact F.tH
  · rw [e2]; exact F.sH
  · rw [e1, hth]; exact F.tTh
  · rw [e2, hth]; exact F.sTh
  · rw [e1, hT]; exact F.tT
  · rw [e2, hC]; exact F.sC
  · rw [e1]; exact hK1
  · rw [e2]; exact hK2
  · rw [e1, hks]; exact F.tKs
  · rw [e2, hks]; exact F.sKs
  · intro c' hc'; rw [e1, nodeBase_of_ksb hks]; exact F.tN c' hc'
  · intro c' hc'; rw [e2, nodeBase_of_ksb hks]; exact F.sN c' hc'
  · intro x hx p sb fi hcap
    obtain ⟨hx0, hc0⟩ := hU x hx p sb fi hcap
    rw [e1, e2]; exact F.ut x hx0 p sb fi hc0
  · exact ⟨by rw [e1]; exact FW.tal, by rw [e2]; exact FW.sal, by rw [e1]; exact FW.tfit, by rw [e2]; exact FW.sfit⟩

/-- **`JAtMcW` across a step with the projection footprint, `UtMem` and `CnWF`** (module docstring). -/
theorem jAtMcW_stepK {Z : XSets} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {a a' : A}
    {σ σ' : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hF : ∀ c ∈ Cs, c ≠ L.cpu s → ForeignIdle (L := L) Z H Cs s σ c ∧ FIdleW (L := L) s c)
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ') (hV' : VxE (Z.mv G' V'))
    (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s)) (hU : UtMem (L := L) Z.th s s') (hCn : CnWF σ') :
    JAtMcW (L := L) arI AR s' a' σ' := by
  refine ⟨Z.mv G' V', H, Cs, Ac', Lst', D', J', hV', fun c hc hne => ?_⟩
  have hne0 : c ≠ L.cpu s := by rw [← hW.2.1]; exact hne
  obtain ⟨F, FW⟩ := hF c hc hne0
  obtain ⟨Q, R, hq⟩ := J.blk.1
  exact ForeignIdle.stepK (Z := Z) (Z' := Z.mv G' V') rfl rfl rfl F FW hc hne0 (SchedQueuesInvX.nodes hq c hc)
    (fun p k hp => J.kern.hnd p k hp c hc) hW (kh_none_of_apart J' hCn (by decide) F.tH)
    (kh_none_of_apart J' hCn (by decide) F.sH) (utKeep_of_utMem J J' hU)

variable {MR : A → Fl4Spec.MachineState → Prop}

/-- **`RunMcW` at an outcome with stable ghosts, the footprint, `UtMem` and `CnWF`.** -/
theorem runMcW_of_stK {Z : XSets} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : VxE Z)
    (hF : ∀ c ∈ Cs, c ≠ L.cpu s → ForeignIdle (L := L) Z H Cs s σ c ∧ FIdleW (L := L) s c)
    {a' : A} {σ' : Fl4Spec.State Unit} (hC : RunCK (L := L) arI AR MR s' a' σ')
    (hSt : JStab (L := L) arI AR Z H Cs s' a' σ')
    (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s)) (hU : UtMem (L := L) Z.th s s') (hCn : CnWF σ') :
    RunMcW (L := L) arI AR MR s' a' σ' := by
  obtain ⟨G', V', Ac', Lst', D', J'⟩ := hSt
  exact ⟨hC, jAtMcW_stepK J hF J' (@VxE.mv Z hV G' V') hW hU hCn⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The step facts the `…FootK` premises ask** (module docstring). -/
def StepK (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  P1.WritesIn st s s' (ProjW (L := L) H Cs s) ∧ UtMem (L := L) Z.th s s' ∧ CnWF σ'

/-- **`IrqFootK` [J]** (module docstring). -/
def IrqFootK (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∀ σ', EvOut false .interrupt σ σ' →
        StepK (L := L) Z H Cs s r.1 σ' ⦄

/-- **`UserFootK` [J]** (module docstring). -/
def UserFootK (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∀ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' →
        StepK (L := L) Z H Cs s r.1 σ' ⦄

/-- **`VmfFootK` [J]** (module docstring). -/
def VmfFootK (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType),
      σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∀ σ', EvOut false (.vmFaultEvent ft) σ σ' →
        StepK (L := L) Z H Cs s r.1 σ' ⦄

/-- **`SysUFootK` [J]** (module docstring). -/
def SysUFootK (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64), σ.curThread ≠ σ.idleThread →
      UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∀ ev σ', KEvSpec (.sysU n) true ev → EvOut true ev σ σ' →
        StepK (L := L) Z H Cs s r.1 σ' ⦄

variable {arI AR MR}

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, through `RunMcW`, with `IrqFootK`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_irqK [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : IrqFootK (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (irq_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW hC J w a1 hw)
    (hFt Z H Cs Ac Lst D J hV w a1 hw)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hK⟩
  obtain ⟨hW, hU, hCn⟩ := hK σ' hO
  exact ⟨σ', hO, runMcW_of_stK J hV hF hC' hSt hW hU hCn⟩

set_option maxHeartbeats 4000000 in
/-- **The user-exception entry on any core, through `RunMcW`, with `UserFootK`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_userK [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : UserFootK (L := L) arI AR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c hct hu
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (user_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J n c hct hu)
    (hFt Z H Cs Ac Lst D J hV n c hct hu)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hK⟩
  obtain ⟨hW, hU, hCn⟩ := hK σ' hO
  exact ⟨σ', hO, runMcW_of_stK J hV hF hC' hSt hW hU hCn⟩

set_option maxHeartbeats 4000000 in
/-- **The VM-fault entry on any core, through `RunMcW`, with `VmfFootK`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_vmfK [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : VmfFootK (L := L) arI AR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro ad c ft hct hv
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (vmf_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J ad c ft hct hv)
    (hFt Z H Cs Ac Lst D J hV ad c ft hct hv)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hK⟩
  obtain ⟨hW, hU, hCn⟩ := hK σ' hO
  exact ⟨σ', hO, runMcW_of_stK J hV hF hC' hSt hW hU hCn⟩

set_option maxHeartbeats 4000000 in
/-- **The unknown-syscall entry on any core, through `RunMcW`, with `SysUFootK`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_sysUK [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : SysUFootK (L := L) arI AR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n hct hU hND
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (sysU_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J n hct hU hND)
    (hFt Z H Cs Ac Lst D J hV n hct hU hND)) ?_
  rintro r ⟨⟨ev, σ', hK, hO, hC', hSt⟩, hF'⟩
  obtain ⟨hW, hU', hCn⟩ := hF' ev σ' hK hO
  exact ⟨ev, σ', hK, hO, runMcW_of_stK J hV hF hC' hSt hW hU' hCn⟩

end

end Fl4Proofs.P3.Mc
