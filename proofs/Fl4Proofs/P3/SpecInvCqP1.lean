/-
P3 (DESIGN.md §9), invariant line G1 (ctq19): **`call_kernel` of every
event carries the ready-queue bundle to the exit** (spec side only, outside
the JAtZ cone; KENTRY-PLAN ctq17 handoff 1).

* `EvO C N S`: what the non-syscall events read (`EB true`, ct = `C`,
  `NQ [C]`, sb2's `ScInv` and ctq14's `CKN` for ctq8's `hB`, vi's `VI`),
  kept by `update_time_stamp` (`evo_updateTimeStamp`). Unlike SpecInvCqN3's
  `EvP` it has no `IL [C]` / `Js` (which need a thread cap to `C`, false
  when an interrupt arrives in the idle thread).
* The fault events (unknownSyscall, userLevelFault, vmFaultEvent,
  hypervisorEvent): `check_budget_restart` without restart gives `EB false`
  (ctq8's `eb_checkBudgetRestart_p`), with restart leaves the state; then the
  handler on the current thread `C`: `handle_fault` by ctq8's
  `eb_handleFault_p` (`NPQ C` from `EB true`, `NQ [C]`), `handle_vm_fault`
  keeps `EB true ∧ NQ [C] ∧ ct = C` to its error (`eb_auto` / `nq_auto` /
  `ct_auto`) and the catch runs `handle_fault`; the hypervisor fault is a
  no-op on x64 (`eb_faultArm`, `eb_handleEvent_fault`).
* The interrupt: `update_time_stamp`, `check_budget` (ctq8's
  `eb_checkBudget_p`, nq's `nq_checkBudget`, vi's `vi_checkBudget`), then
  ctq8's `ebx_maybeHandleInterrupt` (`NtfnQB` from `NQ []`, `IdS` from `VI`);
  the current thread may be idle here (`ebx_handleEvent_irq`).
* `ok_other`: the non-syscall events are `withoutPreemption` (no error
  outcome), so the preemption handler never runs; **`ebx_handleE_other`**:
  every outcome `EBX N S false` (NQ: nq3's `nq_fl4HandleEvent_other`; VI:
  vi3's `vi_handleEvent_fault` for an active current thread,
  `vi_handleEvent_irq` for the interrupt).
* **`kcall_tq_other`** (ctq6's `rb_tail`) and **`kcall_tq`**: every event,
  with ctq17's `kcall_tq_sys` for the syscalls (its shell facts asked only
  for a syscall event: `hS`; its `CtSc` from EX's `CurScT`); the activeness
  premise is vi3's `kcall_validIdle_of` form (`activeSt ∨ ev = .interrupt`).
-/
import Fl4Proofs.P3.SpecInvCqN4
import Fl4Proofs.P3.SpecInvCqW
open Classical

namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P17

noncomputable section

set_option maxHeartbeats 2000000

/-- **The facts a non-syscall event reads.** -/
abbrev EvO (C N S : ObjRef) (s : State Unit) : Prop :=
  EB true s ∧ CTh C s ∧ NQ [C] s ∧ SInvB.ScInv s ∧ SInvI.VI N S false s ∧ R14.CKN s

section E
variable {C N S : ObjRef}

theorem evo_updateTimeStamp : IK (EvO C N S) (updateTimeStamp (Z := Unit)) := by
  have h1 : EBK true (updateTimeStamp (Z := Unit)) := by eb_auto
  have h2 : IK (CTh C) (updateTimeStamp (Z := Unit)) := by ct_auto
  have h3 : IK (NQ [C]) (updateTimeStamp (Z := Unit)) := by nq2_auto
  have h4 : ∀ h0, IK (SInvB.BRs h0) (updateTimeStamp (Z := Unit)) := fun _ => by sb_auto
  have h5 : IK (SInvI.VI N S false) (updateTimeStamp (Z := Unit)) := by vi_auto
  have h6 : R14.CKK (updateTimeStamp (Z := Unit)) := by ck_auto
  intro σ hσ y hy
  obtain ⟨hE, hC, hN, hI, hV, hK⟩ := hσ
  exact ⟨h1 σ hE y hy, h2 σ hC y hy, h3 σ hN y hy,
    SInvB.scInv_of_br hI (h4 σ.kheap σ (SInvB.BR.refl _) y hy), h5 σ hV y hy, h6 σ hK y hy⟩

/-- ctq8's `hB` from `EvO`. -/
theorem hb_of_evo {s : State Unit} (h : EvO C N S s) : schedulable s.curThread s = true → BC s :=
  fun hs => R11.bc_of_ck (R14.ckn_ck h.2.2.2.2.2) h.2.2.2.1.back hs

/-- `handle_fault` on the current thread from `EB true` and `NQ [C]`. -/
theorem eb_handleFault_c (ex : Fault) (s : State Unit) (hE : EB true s) (hN : NQ [C] s) (hc : s.curThread = C) :
    ∀ z ∈ (handleFault (Z := Unit) C ex s).1, EB false z.2 := fun z hz =>
  eb_weak (eb_handleFault_p (k := true) (K := [C]) C ex s (by rw [← hc]; exact npq_ct hE) hN
    (by rw [hc]; exact List.mem_singleton_self _) hE z hz)

/-- **A fault event's body**: `update_time_stamp`, `check_budget_restart`, the
handler `F` on the current thread. -/
theorem eb_faultArm (F : ObjRef → SMonad Unit Unit)
    (hF : ∀ s, EvO C N S s → ∀ z ∈ (F C s).1, EB false z.2) (σ : State Unit) (hσ : EvO C N S σ) :
    ∀ y ∈ ((do
        updateTimeStamp (Z := Unit)
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          F thread) σ).1, EB false y.2 := by
  intro y ⟨y1, h1, hy⟩
  have hσ1 : EvO C N S y1.2 := evo_updateTimeStamp σ hσ y1 h1
  obtain ⟨y2, h2, hy⟩ := hy
  (try dsimp only at hy)
  unfold NonDet.when at hy
  split at hy
  · rename_i hr
    have e2 : y2.2 = y1.2 := SInv.checkBudgetRestart_true h2 hr
    obtain ⟨y3, h3, hy⟩ := hy
    rw [mem_gets h3] at hy
    (try dsimp only at hy)
    rw [e2, hσ1.2.1] at hy
    exact hF _ hσ1 y hy
  · rename_i hr
    rw [Set.mem_singleton_iff.1 hy]
    have h := eb_checkBudgetRestart_p y1.2 (hb_of_evo hσ1) (nq_weak_nil _ hσ1.2.2.1) hσ1.1 y2 h2
    cases hw : y2.1
    · rw [hw] at h; exact h
    · exact absurd hw hr

/-- `handle_vm_fault` keeps `EB true`, `NQ [C]` and the current thread. -/
theorem fv_handleVmFault (ft : VMFaultType) :
    IKE (fun s => EB true s ∧ NQ [C] s ∧ s.curThread = C) (handleVmFault (Z := Unit) C ft) :=
  fun σ h y hy => ⟨(show EBKE true (handleVmFault (Z := Unit) C ft) by eb_auto) σ h.1 y hy,
    (show NQKE [C] (handleVmFault (Z := Unit) C ft) by nq_auto) σ h.2.1 y hy,
    (show CTKE C (handleVmFault (Z := Unit) C ft) by ct_auto) σ h.2.2 y hy⟩

set_option maxHeartbeats 8000000 in
/-- **The fault events**: every outcome `EB false`. -/
theorem eb_handleEvent_fault (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (hi : ev ≠ .interrupt)
    (σ : State Unit) (hσ : EvO C N S σ) :
    ∀ y ∈ ((handleEvent (Z := Unit) ev).run σ).1, EB false y.2 := by
  have hHF : ∀ ex s, EvO C N S s → ∀ z ∈ (handleFault (Z := Unit) C ex s).1, EB false z.2 :=
    fun ex s hs => eb_handleFault_c ex s hs.1 hs.2.2.1 hs.2.1
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | interrupt => exact absurd rfl hi
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (eb_faultArm _ (hHF _)) σ hσ
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (eb_faultArm _ (hHF _)) σ hσ
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (eb_faultArm _ ?_) σ hσ
    intro s hs z hz
    exact hk_catch (I := fun s => EB true s ∧ NQ [C] s ∧ s.curThread = C) (Q0 := EB false)
      (hkr_of_ike (fv_handleVmFault ft) fun _ h => eb_weak h.1)
      (fun e s' hs' z' hz' => eb_handleFault_c e s' hs'.1 hs'.2.1 hs'.2.2 z' hz')
      s ⟨hs.1, hs.2.2.1, hs.2.1⟩ z hz
  | hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (eb_faultArm _ ?_) σ hσ
    intro s hs z hz
    cases ht
    exact eb_weak ((ik_pure (P := EB true) ()) s hs.1 z hz)

/-- **The interrupt**: every outcome `EBX N S false` (the current thread may be idle). -/
theorem ebx_handleEvent_irq (σ : State Unit) (hσ : EvO C N S σ) :
    ∀ y ∈ ((handleEvent (Z := Unit) .interrupt).run σ).1, EBX N S false y.2 := by
  simp only [handleEvent, withoutPreemption]
  refine hk_liftE ?_ σ hσ
  intro σ hσ y ⟨y1, h1, hy⟩
  have hσ1 : EvO C N S y1.2 := evo_updateTimeStamp σ hσ y1 h1
  obtain ⟨y2, h2, hy⟩ := hy
  have hE2 := eb_checkBudget_p y1.2 (hb_of_evo hσ1) (nq_weak_nil _ hσ1.2.2.1) hσ1.1 y2 h2
  have hN2 : NQ [] y2.2 := nq_checkBudget y1.2 hσ1.2.2.1 y2 h2
  have hV2 : SInvI.VI N S false y2.2 := SInvI.vi_checkBudget y1.2 hσ1.2.2.2.2.1 y2 h2
  exact ebx_maybeHandleInterrupt N S false false y2.2 ⟨eb_weak hE2, hN2, hV2⟩ y hy

end E

/-! ## The event with its preemption handler -/

/-- The non-syscall events have no error outcome (`withoutPreemption`). -/
theorem ok_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (σ : State Unit) :
    ∀ z ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ∃ a, z.1 = .ok a := by
  intro z hz
  rw [fl4HandleEvent_other rep ev h] at hz
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ =>
    simp only [handleEvent, withoutPreemption] at hz
    obtain ⟨x, -, rfl⟩ := ft_mem_liftE hz
    exact ⟨_, rfl⟩

section K
variable {C N S : ObjRef}

set_option maxHeartbeats 4000000 in
/-- **A non-syscall event and its preemption handler**: every outcome `EBX N S false`
(`hV`: `VI N S true` unless the event is the interrupt). -/
theorem ebx_handleE_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hσ : EvO C N S σ) (hV : ev ≠ .interrupt → SInvI.VI N S true σ) :
    ∀ y ∈ (ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
      (fun _ => withoutPreemption preemptionPath)) σ).1, EBX N S false y.2 := by
  intro y hy
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨a, ha⟩ := ok_other rep ev h σ z hz
  obtain ⟨r, s⟩ := z
  simp only at ha; subst ha
  have hP : EBX N S false s := by
    by_cases hi : ev = .interrupt
    · subst hi
      rw [fl4HandleEvent_other rep _ h] at hz
      exact ebx_handleEvent_irq σ hσ _ hz
    · have hz' := hz
      rw [fl4HandleEvent_other rep _ h] at hz'
      exact ⟨eb_handleEvent_fault ev h hi σ hσ _ hz',
        nq_fl4HandleEvent_other C rep ev h σ ⟨hσ.2.2.1, hσ.2.1⟩ _ hz,
        vi_false_of_true (SInvI.vi_handleEvent_fault ev h hi σ (hV hi) _ hz')⟩
  first
    | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hP)
    | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hP)

end K

/-! ## The tops -/

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across `call_kernel` of a non-syscall event**
(`hN`: nq's `NQ [ct]`, true also for the idle thread). -/
theorem kcall_tq_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hSc : SInvB.ScInv σ)
    (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, EX y.2 ∧ RB y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hσ : EvO σ.curThread σ.idleThread σ.idleSc σ :=
    ⟨⟨⟨hX.1, h4⟩, hR⟩, rfl, hN, hSc, hV, R16.ckn_of_exit hCX hX.2.2.2⟩
  have hx : EBX σ.idleThread σ.idleSc false y1.2 :=
    ebx_handleE_other rep ev h hσ (fun hi => SInvI.vi_true_of_active hV fun x hx => (ha x hx).resolve_right hi)
      y1 h1
  obtain ⟨hE1, hN1, hV2⟩ := hx
  exact rb_tail y1.2 ⟨hE1.1, SInvI.validIdle_of (σ := σ) hV2, hN1, hE1.2⟩ y hy

/-- The shell facts a syscall event reads (sl3's `Js`, ctq11's `EF` / `I`, nq3's `Iu`, il2's `IL`). -/
abbrev SysF (I : ObjRef × ObjRef) (d : Prop) (Nq : Irq → ObjRef) (σ : State Unit) : Prop :=
  Iu σ.curThread σ ∧ IL [σ.curThread] σ ∧ Js I σ.curThread d Nq σ σ ∧ EF Nq σ ∧ I.2 = σ.idleSc ∧
    IrqOutV (fun _ => I.1) (uV σ)

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across `call_kernel` of every event**: from the
carried entry facts, every outcome has ctq5's `EX` and ctq6's `RB`
(`hnd` SpecInvQDom's [P]; `hS` only for a syscall event). -/
theorem kcall_tq (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ)
    (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, EX y.2 ∧ RB y.2 := by
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    obtain ⟨hIu, hIL, hJ, hE, hI2, hI1⟩ := hS c rfl
    exact kcall_tq_sys hnd rep c hX hR h4 hV hEO hCX
      (fun x hx => (ha x hx).resolve_right fun e => by cases e) hIu hIL hJ hE hI2 hI1 hO hI
      (fun _ => ctSc_of_curScT hX.2.2.2)
  · exact kcall_tq_other rep ev (fun c e => hs ⟨c, e⟩) hX hR h4 hV hEO.sc hCX ha hN

end

end Fl4Proofs.P3.SInvQ.P19
