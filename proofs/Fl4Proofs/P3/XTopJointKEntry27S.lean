/-
P3 (DESIGN.md §9), invariant line G3 (INV-PLAN §4, g3a): **the spec facts that
`kernel_entryJ27` reads from `SInvB` at states reached from the entry state by
the spec front** (spec side only, outside the JAtZ cone; imports SpecInvAllB).

* `SInvF.fo_front`: fo1's `kentry_fpuOwn` cut at the handled event: from the
  carried `IfLiveT`, `FT`, `NtfnQB ∧ EpQB`, `UtInv3` and an active current
  thread, every outcome of `fl4SyscallFaultIP ct >>= handleE (fl4HandleEvent
  rep (syscall c)) preemptionPath` (XTopJointKEntry's `specFront`, before
  `fl4Awaken`) has `FT`, hence `FpuOwnOKS` (`KFinAtR.fo`). The proof is
  `fo_fl4CallKernel_of`'s first half (`fo_fl4HandleEvent_sys`,
  `nq_fl4HandleEvent_sys`, `fo_preemptionPath`).
* `SInvAll.sinvB_front_fo`: the same from `SInvB σ` and `ct ≠ idle`.
* `SInvAll.sinvB_disp`: at a state σb whose heap is σ's with the current
  thread's TCB replaced by one with the same fault handler and fault (the
  `FaultIP` write, then `update_time_stamp` and a passing
  `check_budget_restart`, which touch no object): the current thread's fault
  handler is valid (`JEntryAt.vfh`, `KDispHypsKV26.recv`'s second part; from
  `VfhAll`) and it has no fault (`JEntryAt.cnf`; from `FaultTcbsS` and l4v
  `ct_active`, `SInvB.entryJ`).
-/
import Fl4Proofs.P3.SpecInvAllB

open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000

/-- **`FT` at the outcomes of the front end** (module docstring). -/
theorem fo_front (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ y ∈ ((fl4SyscallFaultIP (Z := Unit) σ.curThread >>= fun _ =>
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c))
        (fun _ => withoutPreemption preemptionPath))) σ).1, FT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  intro y ⟨y2, h2, hy⟩
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 hN) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hJ : JF σ.interruptIrqNode σ.curThread σ :=
    ⟨⟨il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active ha0)), hNQ, rfl, hU, rfl⟩, hF⟩
  have hI : Iu σ.curThread σ :=
    ⟨hNQ, rfl, hU.1.1.1, nqDet_of_live hU.1 (ifLiveB_of h)⟩
  have hJ2 : JF σ.interruptIrqNode σ.curThread y2.2 ∧ Iu σ.curThread y2.2 := by
    refine ⟨(?_ : IK (JF σ.interruptIrqNode σ.curThread) _) σ hJ y2 h2, (?_ : IK (Iu σ.curThread) _) σ hI y2 h2⟩
    · juf_auto
    · iu_auto
  have hE : HKE (fun s => JF σ.interruptIrqNode σ.curThread s ∧ Iu σ.curThread s) (ILF [])
      (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) :=
    hk_pre (fo_fl4HandleEvent_sys _ σ.curThread rep c) fun _ h => h.1
  have hEN : HKE (fun s => JF σ.interruptIrqNode σ.curThread s ∧ Iu σ.curThread s) (NQ [])
      (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) :=
    hk_pre (nq_fl4HandleEvent_sys σ.curThread rep c) fun _ h => h.2
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : FN [] z.2 := ⟨⟨(hE y2.2 hJ2 z hz).1, hEN y2.2 hJ2 z hz⟩, (hE y2.2 hJ2 z hz).2⟩
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'.2
  | error e =>
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) hy
    exact (fo_preemptionPath s hz' w hw).2

end

end Fl4Proofs.P3.SInvF

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec

noncomputable section

/-- **`FpuOwnOKS` at the front end's outcomes from `SInvB`** (module docstring). -/
theorem sinvB_front_fo (rep : Bool) (c : Syscall) {σ : State Unit} (h : SInvB σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4SyscallFaultIP (Z := Unit) σ.curThread >>= fun _ =>
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c))
        (fun _ => withoutPreemption preemptionPath))) σ).1, SInvF.FpuOwnOKS y.2 :=
  fun y hy => SInvF.fpuOwnOK_of_ft
    (SInvF.fo_front rep c (h.entryJ hct).ctAct ⟨h.1.1.nq, h.1.1.epq⟩ h.1.1.ut h.1.1.live h.1.1.ft y hy)

/-- **The current thread's handler and fault at a dispatch state** (module docstring). -/
theorem sinvB_disp {σ σb : State Unit} (h : SInvB σ) (hct : σ.curThread ≠ σ.idleThread)
    {x x' : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x))
    (hfh : x'.tcbFaultHandler = x.tcbFaultHandler) (hf : x'.tcbFault = x.tcbFault)
    (ek : σb.kheap = Function.update σ.kheap σ.curThread (some (.tcb x')))
    (ect : σb.curThread = σ.curThread) :
    (∀ y, σb.kheap σb.curThread = some (.tcb y) → validFaultHandler y.tcbFaultHandler) ∧
    (∀ y, σb.kheap σb.curThread = some (.tcb y) → y.tcbFault = none) := by
  have hy : ∀ y, σb.kheap σb.curThread = some (.tcb y) → y = x' := by
    intro y hy
    rw [ek, ect, Function.update_self] at hy
    cases hy
    rfl
  refine ⟨fun y hy' => ?_, fun y hy' => ?_⟩
  · rw [hy y hy', hfh]
    exact h.1.1.vfh _ x hk
  · rw [hy y hy', hf]
    obtain ⟨x1, hx1, ha⟩ := (h.entryJ hct).ctAct
    rw [hk] at hx1
    cases hx1
    by_contra hne
    have hs := h.1.1.fts _ x hk hne
    revert ha hs
    generalize x.tcbState = ts
    intro ha hs
    cases ts <;> first | exact (ha : False).elim | exact (hs : False).elim

end

end Fl4Proofs.P3.SInvAll
