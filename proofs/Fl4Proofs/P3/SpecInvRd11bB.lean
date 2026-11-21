/-
P3 (DESIGN.md §9), invariant line G1 (rd11b, KENTRY-PLAN rd10 handoff 3-4):
**`hEvO` for the fault events and `hQ4` from ctq17 / ctq19** (spec side only).

* `FH ev t`: a fault event's handler on the current thread after a `true`
  front (handle_fault for unknown syscalls / user-level faults, handle_vm_fault
  caught by handle_fault, the x64 hypervisor no-op); `mem_arm` / **`mem_faultEv`**:
  every outcome of a fault event's part is a `false` front outcome, or an `FH`
  outcome from a `true` one.
* **`hf_ev`**: from `BS` at a `true` front outcome `s`, every `FH` outcome is `s`
  (hypervisor) or keeps rd8a's `CP s cur_sc` and cfS and leaves ct not runnable
  (SpecInvRd11bA). **`ss4_end`**: then `SS4` (OS by `os_frame`; CtR vacuous;
  RCA / HRC vacuous since ctq's `CB` at the outcome and ct not runnable, not
  idle rule out resume).
* **`ev_fault`** (`hEvO` for the four fault events): `SS ∧ NQ []` at every
  outcome, from rd8a's `EF`, ctq's EBX at the outcomes (`CB`, `NQ []`) and
  `hRdF : RdF ev σ` (Rdy after the handler at the `true` front outcomes, named
  for rd8e/f's eventual `rd_handleFault`; the `false` front is rd8a's
  `front_false`, its `hCtRc` from rd10's `charge_ss4`).
* **`ebx_other` / `ebx_sys` / `sq4_ev`** (`hQ4`): ctq19's `kcall_tq_other` /
  ctq17's `kcall_tq_sys` stopped at the event part; **`sq4_fip`**: ctq19's
  `kentry_tq` carry to the FaultIP state (any `rep`).
* Tops **`kcall_rdyOff3j` / `kentry_rdyOff3j`**: rd10's tops with `hEvO` (fault
  part) and `hQ4` discharged; `hni` derived (ct active, ValidIdle, CtExit).
-/
import Fl4Proofs.P3.SpecInvRd11bA
import Fl4Proofs.P3.SpecInvCqP2
open Classical

namespace Fl4Proofs.P3.SInvR.A11b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The fault events' part -/

/-- A fault event's handler on the current thread `t` after a `true` front. -/
def FH : Event → ObjRef → SMonad Unit Unit
  | .unknownSyscall n, t => handleFault t <| .unknownSyscallException <| BitVec.ofNat 64 n
  | .userLevelFault w1 w2, t => handleFault t <| .userException (w1 &&& mask 32) (w2 &&& mask 28)
  | .vmFaultEvent ft, t => NonDetE.catch (handleVmFault t ft) (handleFault t)
  | .hypervisorEvent h, t => handleHypervisorFault t h
  | _, _ => pure ()

/-- One fault arm: a `false` front outcome, or the handler after a `true` one. -/
theorem mem_arm {B : ObjRef → SMonad Unit Unit} {σ : State Unit} {w : Unit × State Unit}
    (hw : w ∈ ((do
        updateTimeStamp (Z := Unit)
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          B thread) σ).1) :
    ∃ v ∈ (A8.front σ).1, (v.1 = false ∧ w.2 = v.2) ∨ (v.1 = true ∧ w ∈ (B v.2.curThread v.2).1) := by
  obtain ⟨y1, h1, hw⟩ := hw
  obtain ⟨v, hv, hw⟩ := hw
  refine ⟨v, ⟨y1, h1, hv⟩, ?_⟩
  (try dsimp only at hw)
  unfold NonDet.when at hw
  split at hw
  · rename_i hr
    obtain ⟨g, hg, hw⟩ := hw
    rw [mem_gets hg] at hw
    exact Or.inr ⟨hr, hw⟩
  · rename_i hr
    exact Or.inl ⟨Bool.eq_false_iff.mpr hr, by rw [Set.mem_singleton_iff.1 hw]⟩

/-- **Every outcome of a fault event's part**: a `false` front outcome, or an
`FH` outcome after a `true` one. -/
theorem mem_faultEv (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (hi : ev ≠ .interrupt)
    {σ : State Unit} {y : Except Unit Unit × State Unit} (hy : y ∈ (A8.evRun rep ev σ).1) :
    ∃ v ∈ (A8.front σ).1, (v.1 = false ∧ y.2 = v.2) ∨
      (v.1 = true ∧ ∃ z ∈ (FH ev v.2.curThread v.2).1, y.2 = z.2) := by
  dsimp only [A8.evRun] at hy
  rw [fl4HandleEvent_other rep _ h] at hy
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | interrupt => exact absurd rfl hi
  | _ =>
    simp only [handleEvent] at hy
    obtain ⟨w, hw, e⟩ := A10.mem_handleE_wp hy
    obtain ⟨v, hv, hc⟩ := mem_arm hw
    refine ⟨v, hv, ?_⟩
    rcases hc with ⟨hf, e2⟩ | ⟨ht, hz⟩
    · exact Or.inl ⟨hf, e.trans e2⟩
    · exact Or.inr ⟨ht, w, hz, e⟩

/-- ct is not receive-blocked at a body-start state. -/
theorem nb0_of_bs {s : State Unit} (h : A10.BS s) : TP (NB0 s.curThread) s := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  intro p x hp ep e r d hx
  subst ep
  rw [hct] at hp; cases hp
  rcases hst with hs | hs <;> rw [hs] at hx <;> cases hx

/-- **The handler from the body-start facts**: the state is kept (hypervisor), or
`CP` and cfS are kept and ct ends not runnable. -/
theorem hf_ev (ev : Event) {s : State Unit} (hB : A10.BS s) :
    ∀ z ∈ (FH ev s.curThread s).1, z.2 = s ∨
      (A8.CP s s.curSc z.2 ∧ cfS z.2 = cfS s ∧ A8.NRun s.curThread z.2) := by
  have hP0 : PV s s.curThread s := ⟨⟨rfl, A8.CW.refl _ _⟩, rfl, nb0_of_bs hB⟩
  have hHF : ∀ ex s', PV s s.curThread s' → ∀ z ∈ (handleFault (Z := Unit) s.curThread ex s').1,
      A8.CP s s.curSc z.2 ∧ cfS z.2 = cfS s ∧ A8.NRun s.curThread z.2 := fun ex s' hs' z hz =>
    ⟨cp_handleFault _ ex s s.curSc s' hs'.1 z hz, (cfk_handleFault _ ex s' z hz).trans hs'.2.1,
      nr_handleFault _ ex s' hs'.2.2 z hz⟩
  intro z hz
  cases ev with
  | unknownSyscall n => exact Or.inr (hHF _ s hP0 z hz)
  | userLevelFault w1 w2 => exact Or.inr (hHF _ s hP0 z hz)
  | vmFaultEvent ft =>
    obtain ⟨z0, hz0, hz⟩ := hz
    obtain ⟨⟨e, he⟩, hP⟩ := pv_handleVmFault _ ft s s hP0 z0 hz0
    obtain ⟨r, s'⟩ := z0
    dsimp only at he hP hz
    subst he
    exact Or.inr (hHF e s' hP z hz)
  | hypervisorEvent ht =>
    cases ht
    left
    simp only [FH, handleHypervisorFault] at hz
    rw [Set.mem_singleton_iff.1 hz]
  | syscallEvent c => left; rw [Set.mem_singleton_iff.1 hz]
  | interrupt => left; rw [Set.mem_singleton_iff.1 hz]

/-- **`SS4` after the handler** from OS at its start, the frame, ct not runnable,
ctq's `CB` and ct not idle. -/
theorem ss4_end {s z : State Unit} (hO : OS s) (hP : A8.CP s s.curSc z) (hc : cfS z = cfS s)
    (hN : A8.NRun s.curThread z) (hCB : CB z) (hni : s.curThread ≠ s.idleThread) : A10.SS4 z := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨-, -, et, ei, -, -⟩ := hc'
  have hnr : z.schedulerAction ≠ .resumeCurThread := by
    intro e
    rcases hCB e with ⟨x, hx, hr⟩ | hi
    · rw [et] at hx; rw [hN x hx] at hr; cases hr
    · exact hni (by rw [← et, ← ei]; exact hi)
  refine ⟨os_frame hO ⟨hc, fun y n hy => ?_, hP.2.2⟩, fun e => absurd e hnr, ?_, fun e => absurd e hnr⟩
  · rw [hP.1] at hy; exact hP.2.1 y n hy
  · intro x hx hrun
    rw [et] at hx; rw [hN x hx] at hrun; cases hrun

/-- **rd8e/f's eventual `rd_handleFault`, pinned to the given entry**: `Rdy` at
every handler outcome after a `true` front. -/
abbrev RdF (ev : Event) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ z ∈ (FH ev v.2.curThread v.2).1, Rdy z.2

/-- **`hEvO` for the fault events**: `SS ∧ NQ []` at every outcome of the
event's part (`hE`: ctq's EBX there; `hRdF`: rd8e/f's Rdy after the handler). -/
theorem ev_fault (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (hi : ev ≠ .interrupt)
    {σ : State Unit} {N S : ObjRef} (hEF : A8.EF σ)
    (hE : ∀ y ∈ (A8.evRun rep ev σ).1, EBX N S false y.2) (hRdF : RdF ev σ) :
    ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2 := by
  intro y hy
  obtain ⟨hE1, hN1, -⟩ := hE y hy
  obtain ⟨v, hv, hc⟩ := mem_faultEv rep ev h hi hy
  rcases hc with ⟨hf, e⟩ | ⟨ht, z, hz, e⟩
  · rw [e]
    exact A8.front_false hEF (fun y1 hy1 z1 hz1 => (A10.charge_ss4 (A10.bs_uts hEF hy1) _ true hz1).2.2.1) hv hf
  · obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
    have hR : Rdy z.2 := hRdF v hv ht z hz
    rw [e] at hE1 hN1 ⊢
    refine ⟨⟨hR, ?_⟩, hN1⟩
    rcases hf_ev ev hB z hz with ez | ⟨hP, hc, hNr⟩
    · rw [ez]; exact A10.ss4_of_bs hB hS
    · exact ss4_end (A10.ss4_of_bs hB hS).1 hP hc hNr hE1.2.2 hB.ni

/-! ## ctq's EBX at the event part's outcomes (`hQ4`) -/

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

set_option maxHeartbeats 4000000 in
/-- ctq19's `kcall_tq_other` stopped at the event part. -/
theorem ebx_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hSc : SInvB.ScInv σ)
    (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) :
    ∀ y ∈ (A8.evRun rep ev σ).1, EBX σ.idleThread σ.idleSc false y.2 := fun y hy =>
  ebx_handleE_other rep ev h (C := σ.curThread)
    ⟨⟨⟨hX.1, h4⟩, hR⟩, rfl, hN, hSc, hV, R16.ckn_of_exit hCX hX.2.2.2⟩
    (fun hi => SInvI.vi_true_of_active hV fun x hx => (ha x hx).resolve_right hi) y hy

set_option maxHeartbeats 4000000 in
/-- ctq17's `kcall_tq_sys` stopped at the event part. -/
theorem ebx_sys (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ) (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ (A8.evRun rep (.syscallEvent c) σ).1, EBX σ.idleThread σ.idleSc false y.2 := by
  intro y1 h1
  have hσ := evp_start (I := I) (d := d) (Nq := Nq) hX hR h4 hV hEO hCX hIu hIL hJ
  have hCN := ne_idle_of_active hV hCX ha
  have hV1 : SInvI.VI σ.idleThread σ.idleSc true σ := SInvI.vi_true_of_active hV ha
  by_cases hp : SInvI.Pinned c
  · exact ebx_handleE_sys hnd hE hI2 hI1 hCN rep c hσ (T := σ.curThread)
      ⟨SInvI.vit_of_vi hV1 (hct hp), rfl, rfl⟩ hO hI (fun _ => rfl) hEO hCX hX.2.2.2 y1 h1
  · exact ebx_handleE_sys hnd hE hI2 hI1 hCN rep c hσ (T := σ.idleThread)
      ⟨hV1, rfl, rfl⟩ hO hI (fun h => absurd h hp) hEO hCX hX.2.2.2 y1 h1

/-- **`hQ4`**: SQ4 at every outcome of the event part (ctq19's `kcall_tq` split). -/
theorem sq4_ev (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ)
    (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ) :
    ∀ y ∈ (A8.evRun rep ev σ).1, SQ4 y.2 := by
  intro y hy
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    obtain ⟨hIu, hIL, hJ, hE, hI2, hI1⟩ := hS c rfl
    exact (ebx_sys hnd rep c hX hR h4 hV hEO hCX (fun x hx => (ha x hx).resolve_right fun e => by cases e)
      hIu hIL hJ hE hI2 hI1 hO hI (fun _ => ctSc_of_curScT hX.2.2.2) y hy).1.1
  · exact (ebx_other rep ev (fun c e => hs ⟨c, e⟩) hX hR h4 hV hEO.sc hCX ha hN y hy).1.1

set_option maxHeartbeats 8000000 in
/-- **`hQ4` at the syscall entry**: ctq19's `kentry_tq` carry to the FaultIP
state (any `rep`), then `ebx_sys`. -/
theorem sq4_fip (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ) (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, SQ4 y.2 := by
  intro w hw y hy
  have hu : uV w.2 = uV σ := SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw
  have hf : (w.2.idleThread, w.2.idleSc, w.2.curThread) = (σ.idleThread, σ.idleSc, σ.curThread) :=
    fld_arch _ σ rfl w hw
  simp only [Prod.mk.injEq] at hf
  obtain ⟨fN, fS, fC⟩ := hf
  have hX' : EX w.2 :=
    ⟨⟨tq_fl4SyscallFaultIP _ σ hX.1.1 w hw, sa_fl4SyscallFaultIP _ σ hX.1.2 w hw⟩,
      ctQ_arch σ hX.2.1 w hw, simple_arch σ hX.2.2.1 w hw, curScT_fip σ hX.2.2.2 w hw⟩
  have hR' : RB w.2 := rb_fl4SyscallFaultIP _ σ hR w hw
  have h4' : T4 w.2 := q4_fl4SyscallFaultIP _ σ h4 w hw
  have hV' : SInvI.ValidIdle w.2 := by
    have h := SInvI.vi_fl4SyscallFaultIP (N := σ.idleThread) (S := σ.idleSc) (T := σ.idleThread) (b := false)
      σ.curThread σ hV w hw
    unfold SInvI.ValidIdle; rw [fN, fS]; exact h
  have hEO' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hEO hu
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    (vfh_fip σ hEO.vfh w hw)
  have hCX' : SInvAll.CtExit w.2 := ctExit_arch σ hCX w hw
  have ha' := act_arch σ ha w hw
  have hIu' : Iu σ.curThread w.2 :=
    (show IK (Iu σ.curThread) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by iu_auto) σ hIu w hw
  have hIL' : IL [σ.curThread] w.2 := il_fl4SyscallFaultIP _ σ hIL w hw
  have hJ' : Js I σ.curThread d Nq σ w.2 :=
    (show IK (Js I σ.curThread d Nq σ) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by js_auto) σ hJ w hw
  have hE' : EF Nq w.2 := by
    refine ⟨?_, ?_, ?_, vfh_fip σ hE.2.2.2 w hw⟩
    · show P3V Nq (uV w.2); rw [hu]; exact hE.1
    · show ScKindV (uV w.2); rw [hu]; exact hE.2.1
    · show IrqOutV (fun _ => w.2.idleSc) (uV w.2); rw [hu, fS]; exact hE.2.2.1
  rw [← fC] at hIu' hIL' hJ'
  exact (ebx_sys hnd rep c hX' hR' h4' hV' hEO' hCX' ha' hIu' hIL' (js_rebase hJ') hE'
    (by rw [fS]; exact hI2) (by rw [hu]; exact hI1)
    (by show IrqOutV (fun _ => w.2.idleThread) (uV w.2); rw [hu, fN]; exact hO)
    (by show IrqOutV (fun _ => w.2.idleSc) (uV w.2); rw [hu, fS]; exact hI)
    (fun _ => ctSc_of_curScT hX'.2.2.2) y hy).1.1

/-! ## The tops -/

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd11b top): rd10's
`kcall_rdyOff3i` with `hEvO` for the fault events (`ev_fault`) and `hQ4`
(`sq4_ev`) discharged, `hni` derived. Remaining: `hRdB` (rd8e/f, unchanged),
`hOsB` (syscalls other than Yield; rd11a), `hRdF` (rd8e/f's handle_fault Rdy,
fault events only); the rest are carried entry facts (rd8a `EF`, rd10 `EFI` /
`EV10`, ctq19's bundle and `kcall_tq` premises). -/
theorem kcall_rdyOff3j (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → c ≠ .sysYield → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A10.kcall_rdyOff3i rep ev σ (fun c e => hEF (by rw [e]; intro h; cases h)) hEFI hX10
    (fun hi => ne_idle_of_active hX10.vi hCX fun x hx => (ha x hx).resolve_right hi) hRdB hOsB
    (fun hs hi => ev_fault rep ev hs hi (hEF hi)
      (ebx_other rep ev hs hX hR h4 hX10.vi hX10.eo.sc hCX ha hN) (hRdF hs hi))
    (sq4_ev hnd rep ev hX hR h4 hX10.vi hX10.eo hCX ha hN hX10.io hX10.isc hS)

/-- **The syscall entry** (rd11b top): rd10's `kentry_rdyOff3` with `hQ4`
discharged (`sq4_fip`). Remaining: `hW` = rd8e/f's `RdBody` and rd11a's
`OsBody` (non-Yield) at the FaultIP outcome; the rest carried entry facts. -/
theorem kentry_rdyOff3j (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ (c ≠ .sysYield → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A10.kentry_rdyOff3 rep c σ h hX10 fun w hw =>
    ⟨(hW w hw).1, (hW w hw).2, sq4_fip hnd rep c hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ hE hI2 hI1
      hX10.io hX10.isc w hw⟩

end Q

end

end Fl4Proofs.P3.SInvR.A11b
