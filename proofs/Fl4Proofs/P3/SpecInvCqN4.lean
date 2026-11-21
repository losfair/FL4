/-
P3 (DESIGN.md §9), invariant line G1 (ctq17): **`call_kernel` of a syscall
carries the ready-queue bundle to the exit** (spec side only, outside the
JAtZ cone; KENTRY-PLAN ctq15 handoff 3, ctq16 handoff 2).

* **`ebx_handleE_sys`**: every outcome of the event with its preemption
  handler has ctq8's `EBX N S false` (`EB false ∧ NQ [] ∧ VI`): an `ok`
  outcome by `eb_fl4HandleEvent_sys` (SpecInvCqN3), nq3's
  `nq_fl4HandleEvent_sys` and vi3's `vi_fl4HandleEvent_sys` (with `viGap`);
  an error outcome by ctq18's `ebx_fl4HandleEvent_err` (`JE` = sl3's `Js`,
  `EB true`, `Simple`: all in `EvP`), the preemption handler's `EBX N S true`
  weakened to `VI N S false`.
* `evp_start`: SpecInvCqN3's `EvP` at the entry from the carried facts (ctq5's
  EX, ctq6's RB, ctnq1's T4, vi3's ValidIdle, sb2's EntryOK, g1c's CtExit,
  nq3's `Iu`, il2's `IL`, sl3's `Js`), `ne_idle_of_active` (the active
  current thread is not the idle one).
* **`kcall_tq_sys`**: `fl4CallKernel rep (.syscallEvent c)` from those facts
  ends in ctq6's `EX ∧ RB` (`rb_tail`).
-/
import Fl4Proofs.P3.SpecInvCqN3
import Fl4Proofs.P3.SpecInvCqZA
import Fl4Proofs.P3.SpecInvViM
import Fl4Proofs.P3.SpecInvCqEr2
open Classical

namespace Fl4Proofs.P3.SInvQ.P17
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL

noncomputable section

set_option maxHeartbeats 2000000

theorem vi_false_of_true {N S : ObjRef} {s : State Unit} (h : SInvI.VI N S true s) : SInvI.VI N S false s :=
  ⟨h.1, h.2.1, (fun e => by cases e), h.2.2.2⟩

section E
variable {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}

set_option maxHeartbeats 4000000 in
/-- **The syscall event and its preemption handler**: every outcome `EBX`. -/
theorem ebx_handleE_sys (hnd : numDomains = 1) {σ : State Unit} (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc)
    (hI1 : IrqOutV (fun _ => I.1) (uV σ)) (hCN : C ≠ N) (rep : Bool) (c : Syscall)
    (hσ : EvP C N S I d Nq σ σ) {T : ObjRef} (hW : SInvI.W N S T σ σ) (hO : IO (fun _ => N) σ)
    (hS : IrqOutV (fun _ => S) (uV σ)) (hT : SInvI.Pinned c → T = σ.curThread)
    (hEO : SInvB.EntryOK σ) (hX : SInvAll.CtExit σ) (hC : CurScT σ) :
    ∀ y ∈ (ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c))
      (fun _ => withoutPreemption preemptionPath)) σ).1, EBX N S false y.2 := by
  intro y hy
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a =>
    have hP : EBX N S false s := ⟨eb_fl4HandleEvent_sys hnd hE hI2 hI1 hCN rep c σ hσ _ hz,
      nq_fl4HandleEvent_sys C rep c σ hσ.2.2.1 _ hz,
      vi_false_of_true (SInvI.vi_fl4HandleEvent_sys SInvI.viGap rep c hW hO hS hσ.1.2.2.2.2.1 hT _ hz)⟩
    first
      | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hP)
      | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hP)
  | error e =>
    dsimp only at hy
    unfold withoutPreemption at hy
    obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
    obtain ⟨hE1, hP⟩ := R18.ebx_fl4HandleEvent_err hE hI2 rep _ σ ⟨hσ.2.2.2.1, hσ.1.1.1, hσ.1.1.2.2.1⟩ hσ.2.2.1
      hW hO hS hσ.1.2.2.2.2.1 (fun c' e hp => hT (by cases e; exact hp)) hEO hX hC _ hz e rfl
    obtain ⟨a1, a2, a3⟩ := hP hE1 v hv
    exact ⟨a1, a2, vi_false_of_true a3⟩

end E

/-! ## The entry facts -/

/-- The active current thread is not the idle thread. -/
theorem ne_idle_of_active {σ : State Unit} (hV : SInvI.ValidIdle σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) : σ.curThread ≠ σ.idleThread := by
  intro e
  obtain ⟨x, hx, -⟩ := hCX
  have h1 := ha x hx
  have h2 := idleSt_of_vi (show SInvI.VI σ.idleThread σ.idleSc false σ from hV) x (by rw [← e]; exact hx)
  rw [h2] at h1
  first | exact h1 | simp [activeSt] at h1

/-- **`EvP` at the entry** from the carried facts. -/
theorem evp_start {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σ : State Unit} (hX : EX σ) (hR : RB σ)
    (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ) (hCX : SInvAll.CtExit σ)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ) :
    EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ :=
  ⟨⟨⟨⟨⟨hX.1, h4⟩, hR⟩, rfl, hX.2.2.1, hIu.1⟩, hEO.sc, hV, R11.rt_of_curScT hCX hX.2.2.2, hEO.ut.1, hIL⟩,
    R16.ckn_of_exit hCX hX.2.2.2, hIu, hJ, R11.rt_of_curScT hCX hX.2.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across `call_kernel` of a syscall**: from the
carried entry facts, every outcome has ctq5's `EX` and ctq6's `RB`
(`hct` is vi3's `CtSc` [J] for the pinned syscalls, unchanged). -/
theorem kcall_tq_sys (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ) (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep (.syscallEvent c)) σ).1, EX y.2 ∧ RB y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hσ := evp_start (I := I) (d := d) (Nq := Nq) hX hR h4 hV hEO hCX hIu hIL hJ
  have hCN := ne_idle_of_active hV hCX ha
  have hV1 : SInvI.VI σ.idleThread σ.idleSc true σ := SInvI.vi_true_of_active hV ha
  have hx : EBX σ.idleThread σ.idleSc false y1.2 := by
    by_cases hp : SInvI.Pinned c
    · exact ebx_handleE_sys hnd hE hI2 hI1 hCN rep c hσ (T := σ.curThread)
        ⟨SInvI.vit_of_vi hV1 (hct hp), rfl, rfl⟩ hO hI (fun _ => rfl) hEO hCX hX.2.2.2 y1 h1
    · exact ebx_handleE_sys hnd hE hI2 hI1 hCN rep c hσ (T := σ.idleThread)
        ⟨hV1, rfl, rfl⟩ hO hI (fun h => absurd h hp) hEO hCX hX.2.2.2 y1 h1
  obtain ⟨hE1, hN1, hV2⟩ := hx
  exact rb_tail y1.2 ⟨hE1.1, SInvI.validIdle_of (σ := σ) hV2, hN1, hE1.2⟩ y hy

end

end Fl4Proofs.P3.SInvQ.P17
