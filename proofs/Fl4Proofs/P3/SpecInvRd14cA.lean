/-
P3 (DESIGN.md §9), invariant line G1 (rd14c, KENTRY-PLAN rd14b handoff 1):
**the TCB suspend / resume / register arms, and `InvRo` over any covered set**
(spec side only).

* **`tb_ik`**: rd13b's end case `TB σ0` (σ0's `cfS`, `CW` at cur_sc, ct bound
  to cur_sc, cur_sc an SC) is an invariant of every computation that keeps
  `cfS` (RdP's `CFK`), rd8a's `CP σ0 cur_sc` and rd14b's `BL ct cur_sc` — three
  existing families, no new walk over the scheduler callees.
* Leaves: `sv14_suspend` (suspend keeps every scheduler view: rd8e's
  `sv_cancelIpc'`, the queue removals, the yield-to cancel), `cfk14_restart`,
  **`cp14_restart`** (rd8a's `cp_ifCondTest` / `cp_schedContextResume` /
  `cp_possibleSwitchTo`), **`bl14_restart`** (rd14b's `bl_ifCond` /
  `bl_possibleSwitchTo`).
* **`perfA_liftTB`**: a lifted perform that keeps `TB σ0` has `PerfA` (rd13b's
  `perfA_tbn`, no error outcome). Arms: **`perfA_suspend`**, **`perfA_resume`**,
  **`perfA_readRegistersG`** / **`perfA_writeRegistersG`** /
  **`perfA_copyRegistersG`** (every suspend / resume flag). ct's binding is
  never rewritten by suspend / restart, so `TB` holds at every outcome (also
  when ct suspends itself: it is then Inactive, still bound).
* `RF σ0 u` (the Restart state's facts, `rf_restart`), `ArmA C` (every arm in
  `C` has `PerfA` from `RF`), `armA_cov` (rd14b's `Cov`), `armA_covC`,
  `ArmA.or`; **`PerfRc C` / `InvRc C`** (rd14b's `PerfRo` / `InvRo` over any
  `C`), **`perfR_ofC`**, **`invR_ofC`**, tops **`kcall_rdyOffC`** /
  **`kentry_rdyOffC`** (any `C` with `ArmA C`), instances
  **`kcall_rdyOff5c`** / **`kentry_rdyOff5c`** for `C14c := Cov ∨ CovC`.
-/
import Fl4Proofs.P3.SpecInvRd14bE
import Fl4Proofs.P3.SpecInvRd8eA
import Fl4Proofs.P3.SpecInvRd8A1
open Classical

namespace Fl4Proofs.P3.SInvR.A14c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `TB` as an invariant -/

/-- **`TB σ0` from three existing families.** -/
theorem tb_ik {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : CFK m)
    (h2 : IK (A8.CP σ0 σ0.curSc) m) (h3 : IK (BL σ0.curThread σ0.curSc) m) : IK (TB σ0) m := by
  intro s hs y hy
  have ecs : s.curSc = σ0.curSc := cf_curSc hs.cf
  obtain ⟨-, hw⟩ := h2 s ⟨ecs, hs.cw⟩ y hy
  obtain ⟨hq, hk⟩ := h3 s ⟨fun p x hx he => by subst he; exact hs.bd x hx, hs.sc⟩ y hy
  exact ⟨(h1 s y hy).trans hs.cf, hw, fun x hx => hq _ x hx rfl, hk⟩

/-! ## Leaves: suspend, restart -/

theorem sv14_suspend (t : ObjRef) : SVK.SVM (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc schedContextCancelYieldTo
  sv_auto
  all_goals exact B8e.sv_cancelIpc' _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv14_suspend _)

theorem cfk14_restart (t : ObjRef) : CFK (restart (Z := Unit) t) := by
  unfold restart; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk14_restart _)

theorem cp14_restart (t : ObjRef) (σ0 : State Unit) (c : ObjRef) : IK (A8.CP σ0 c) (restart (Z := Unit) t) := by
  unfold restart testPossibleSwitchTo
  refine SInv.ik_bind (by cp_leaf) fun _ => SInv.ik_bind (by cp_leaf) fun _ => SInv.ik_when _ ?_
  refine SInv.ik_bind (A8.ik_cp (B8e.sv_cancelIpc' _) (cfk_cancelIpc' _) σ0 c) fun _ =>
    SInv.ik_bind (by cp_leaf) fun _ => ?_
  refine SInv.ik_bind (A8.cp_ifCondTest _ _ σ0 c) fun _ =>
    SInv.ik_bind (SInv.ik_maybeM (fun p => A8.cp_schedContextResume p σ0 c) _) fun _ => ?_
  exact SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_when _ (A8.cp_possibleSwitchTo t σ0 c)
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp14_restart _ _ _)

theorem bl14_restart (t c u : ObjRef) : IK (BL t c) (restart (Z := Unit) u) := by
  unfold restart testPossibleSwitchTo
  refine SInv.ik_bind (bl_of_svm (by sv_auto)) fun _ => SInv.ik_bind (bl_of_svm (by sv_auto)) fun _ =>
    SInv.ik_when _ ?_
  refine SInv.ik_bind (bl_of_svm (B8e.sv_cancelIpc' _)) fun _ =>
    SInv.ik_bind (bl_of_svm (SVK.sv_setThreadState' _ _)) fun _ => ?_
  refine SInv.ik_bind (bl_ifCond _ _ _) fun _ =>
    SInv.ik_bind (SInv.ik_maybeM (fun p => bl_of_svm (by sv_auto)) _) fun _ => ?_
  exact SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_when _ (bl_possibleSwitchTo _ _ _)

/-- The `BL` walk of the TCB arms: restart, else whole `SVM` pieces. -/
macro "bl14_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact bl14_restart _ _ _)
  | (refine bl_of_svm ?_; sv_auto; done)
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when)
  | ik_step0))

/-! ## The generic lifted arm -/

/-- **A lifted perform keeping `TB σ0`** has `PerfA` (no error outcome). -/
theorem perfA_liftTB {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation}
    (m : NonDet (State Unit) (List Data)) (he : fl4PerformInvocation (Z := Unit) bl call don oper = NonDetE.liftE m)
    (hB : A10.BS σ0) (hS : Suff σ0) (hm : IK (TB σ0) m) (h0 : TB σ0 s) : PerfA σ0 bl call don oper s := by
  refine perfA_tbn hB hS fun y hy => ?_
  rw [he] at hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact ⟨fun _ _ => Or.inl (hm s h0 x hx), fun e h => by cases h⟩

/-! ## The arms -/

theorem perfA_suspend {σ0 s : State Unit} (bl call don : Bool) (t : ObjRef) (hB : A10.BS σ0) (hS : Suff σ0)
    (h0 : TB σ0 s) : PerfA σ0 bl call don (.invokeTCB (.suspend t)) s :=
  perfA_liftTB _ rfl hB hS (tb_ik (by cfk_auto) (by cp_auto) (by bl14_auto)) h0

theorem perfA_resume {σ0 s : State Unit} (bl call don : Bool) (t : ObjRef) (hB : A10.BS σ0) (hS : Suff σ0)
    (h0 : TB σ0 s) : PerfA σ0 bl call don (.invokeTCB (.resume t)) s :=
  perfA_liftTB _ rfl hB hS (tb_ik (by cfk_auto) (by cp_auto) (by bl14_auto)) h0

theorem perfA_readRegistersG {σ0 s : State Unit} (bl call don : Bool) (src : ObjRef) (sus : Bool) (n a : _)
    (hB : A10.BS σ0) (hS : Suff σ0) (h0 : TB σ0 s) :
    PerfA σ0 bl call don (.invokeTCB (.readRegisters src sus n a)) s :=
  perfA_liftTB _ rfl hB hS (tb_ik (by cfk_auto) (by cp_auto) (by bl14_auto)) h0

theorem perfA_writeRegistersG {σ0 s : State Unit} (bl call don : Bool) (dest : ObjRef) (res : Bool) (v a : _)
    (hB : A10.BS σ0) (hS : Suff σ0) (h0 : TB σ0 s) :
    PerfA σ0 bl call don (.invokeTCB (.writeRegisters dest res v a)) s := by
  refine perfA_liftTB _ rfl hB hS (tb_ik ?_ ?_ ?_) h0 <;>
    simp only [archGetSanitiseRegisterInfo, archPostModifyRegisters]
  · cfk_auto
  · cp_auto
  · bl14_auto

theorem perfA_copyRegistersG {σ0 s : State Unit} (bl call don : Bool) (dest src : ObjRef) (sus res f i : Bool)
    (a : _) (hB : A10.BS σ0) (hS : Suff σ0) (h0 : TB σ0 s) :
    PerfA σ0 bl call don (.invokeTCB (.copyRegisters dest src sus res f i a)) s := by
  refine perfA_liftTB _ rfl hB hS (tb_ik ?_ ?_ ?_) h0 <;>
    simp only [archGetSanitiseRegisterInfo, archPostModifyRegisters]
  · cfk_auto
  · cp_auto
  · bl14_auto

/-! ## Arms over any covered set -/

/-- The facts at the Restart state `u` that the arm lemmas use. -/
structure RF (σ0 u : State Unit) : Prop where
  bs : A10.BS σ0
  suff : Suff σ0
  kp : A11.KP σ0 u
  cb : A11.CB0 u
  bd : ∀ x, u.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc
  sc : ∃ y n, u.kheap σ0.curSc = some (.schedContext y n)
  rs : ∀ x, u.kheap σ0.curThread = some (.tcb x) → x.tcbState = .restart
  ct : ∃ x, u.kheap σ0.curThread = some (.tcb x)

theorem RF.tb {σ0 u : State Unit} (h : RF σ0 u) : TB σ0 u := ⟨h.kp.1, h.kp.2.1, h.bd, h.sc⟩

/-- **The Restart state's facts** (rd14b's `kpc_restart`, `bdsc_restart`). -/
theorem rf_restart {σ0 s : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (hz : KZ σ0 s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1) : RF σ0 u.2 := by
  obtain ⟨hK, hb0⟩ := kpc_restart hB hz hu
  obtain ⟨hbd, hsc⟩ := bdsc_restart hB hz hu
  have hr : ∀ x, u.2.kheap σ0.curThread = some (.tcb x) → x.tcbState = .restart := by
    rw [← kz_curThread hz]; exact SInv.sts_post hu
  have hct : ∃ x, u.2.kheap σ0.curThread = some (.tcb x) := by
    obtain ⟨xt, hxt, -⟩ := hB.ct
    have e := (kz_parts hz).1 σ0.curThread
    rw [hxt] at e
    obtain ⟨x, hx, -⟩ := tcbV_some e
    have e1 := (SVK.sv_setThreadState' _ _ s u hu).1 σ0.curThread
    rw [hx] at e1
    obtain ⟨x', hx', -⟩ := SVK.sv_tcb (o := u.2.kheap σ0.curThread) (a := x.tcbSchedContext) e1
    exact ⟨x', hx'⟩
  exact ⟨hB, hS, hK, hb0, hbd, hsc, hr, hct⟩

/-- Every arm in `C` has `PerfA` from the Restart state's facts. -/
def ArmA (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 u : State Unit) (bl cl dn : Bool) (b : Fl4Invocation), C b → RF σ0 u → PerfA σ0 bl cl dn b u

theorem ArmA.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmA C1) (h2 : ArmA C2) : ArmA (fun b => C1 b ∨ C2 b) :=
  fun σ0 u bl cl dn b hc h => hc.elim (fun c => h1 σ0 u bl cl dn b c h) (fun c => h2 σ0 u bl cl dn b c h)

theorem armA_cov : ArmA Cov :=
  fun _ _ bl cl dn b hc h => perfA_cov bl cl dn b hc h.bs h.suff h.kp h.cb h.bd h.sc h.rs

/-- The TCB arms of this module. -/
def CovT : TcbInvocation → Prop
  | .suspend _ => True
  | .resume _ => True
  | .readRegisters _ _ _ _ => True
  | .writeRegisters _ _ _ _ => True
  | .copyRegisters _ _ _ _ _ _ _ => True
  | _ => False

def CovC : Fl4Invocation → Prop
  | .invokeTCB i => CovT i
  | _ => False

theorem armA_covC : ArmA CovC := by
  intro σ0 u bl cl dn b hc h
  cases b
  case invokeTCB i =>
    cases i
    case suspend t => exact perfA_suspend bl cl dn t h.bs h.suff h.tb
    case resume t => exact perfA_resume bl cl dn t h.bs h.suff h.tb
    case readRegisters src sus n a => exact perfA_readRegistersG bl cl dn src sus n a h.bs h.suff h.tb
    case writeRegisters d r v a => exact perfA_writeRegistersG bl cl dn d r v a h.bs h.suff h.tb
    case copyRegisters d src s1 s2 f i a => exact perfA_copyRegistersG bl cl dn d src s1 s2 f i a h.bs h.suff h.tb
    all_goals exact hc.elim
  all_goals exact hc.elim

/-- rd14b's `Cov` and this module's TCB arms. -/
def C14c (b : Fl4Invocation) : Prop := Cov b ∨ CovC b

theorem armA_c14c : ArmA C14c := armA_cov.or armA_covC

/-- rd14b's `PerfRo` over any covered set `C`. -/
def PerfRc (C : Fl4Invocation → Prop) (σ0 : State Unit) (calling blocking canDonate firstPhase : Bool)
    (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE firstPhase cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1,
      C b ∨ PerfA σ0 blocking calling canDonate b u.2

/-- **`PerfRc` gives rd12b's `PerfR`.** -/
theorem perfR_ofC {C : Fl4Invocation → Prop} (hA : ArmA C) {σ0 σ : State Unit} (hB : A10.BS σ0) (hS : Suff σ0)
    (hz : KZ σ0 σ) {calling blocking don fp : Bool} {cptr : CapRef}
    (h : PerfRc C σ0 calling blocking don fp cptr σ) : PerfR σ0 calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    rw [et] at hu
    exact hA σ0 u.2 blocking calling don b hc (rf_restart hB hS hz2 hu)
  · exact hP

/-- rd14b's `InvRo` over any covered set `C`. -/
def InvRc (C : Fl4Invocation → Prop) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true →
    (∀ r cl bl dn, sendArgs c = some (r, cl, bl, dn) →
      ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfRc C v.2 cl bl dn false g.1 g.2) ∧
    (∀ r cr, srArgs c = some (r, cr) → ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      PerfRc C v.2 false false true true g.1 g.2)

/-- **`InvRc` gives rd12b's `InvR`.** -/
theorem invR_ofC {C : Fl4Invocation → Prop} (hA : ArmA C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (h : InvRc C c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_ofC hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg =>
      perfR_ofC hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).2 r cr hc g hg)⟩

/-! ## The tops -/

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **rd12b's `kcall_rdyOff4r` with `InvRc C`** for any covered set `C`
with `ArmA C`. -/
theorem kcall_rdyOffC {C : Fl4Invocation → Prop} (hA : ArmA C) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
    (σ : State Unit) {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → InvRc C c σ)
    (hRT : ∀ c, ev = .syscallEvent c → RecvT rep c σ)
    (hOsR : ∀ c, ev = .syscallEvent c → RecvC c → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff4r hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB
    (fun c e => invR_ofC hA (hEF (by rw [e]; intro h; cases h)) (hP c e)) hRT hOsR hRdF

/-- **rd12b's `kentry_rdyOff4r` with `InvRc C`.** -/
theorem kentry_rdyOffC {C : Fl4Invocation → Prop} (hA : ArmA C) (hnd : numDomains = 1) (rep : Bool) (c : Syscall)
    (σ : State Unit) {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ InvRc C c w.2 ∧ RecvT rep c w.2 ∧ (RecvC c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOff4r hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, invR_ofC hA (A8.ef_fip h w hw) (hW w hw).2.1, (hW w hw).2.2.1, (hW w hw).2.2.2⟩

/-- **`kcall_rdyOffC` for rd14b's arms and the TCB suspend / resume /
register arms** (`hP` asks `PerfA` only outside `C14c`). -/
theorem kcall_rdyOff5c (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → InvRc C14c c σ)
    (hRT : ∀ c, ev = .syscallEvent c → RecvT rep c σ)
    (hOsR : ∀ c, ev = .syscallEvent c → RecvC c → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOffC armA_c14c hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB hP hRT hOsR hRdF

theorem kentry_rdyOff5c (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ InvRc C14c c w.2 ∧ RecvT rep c w.2 ∧ (RecvC c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOffC armA_c14c hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 hW

end Q

end

end Fl4Proofs.P3.SInvR.A14c
