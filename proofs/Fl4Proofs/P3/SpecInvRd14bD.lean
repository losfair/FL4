/-
P3 (DESIGN.md §9), invariant line G1 (rd14b, KENTRY-PLAN rd13b handoff 2-3):
**`InvR` from the per-arm lemmas** (spec side only).

* `Cov b`: the perform arms proved (rd12b's Domain, rd13b's frame-keeping
  arms, rd14b's Notification and Endpoint); **`perfA_cov`**: every covered arm has `PerfA`
  from the Restart state's facts (`KP σ0 ∧ CB0` by `kpc_restart`, ct bound to
  σ0's cur_sc and cur_sc an SC by `bdsc_restart`).
* `PerfRo` / `InvRo`: rd12b's `PerfR` / `InvR` with `PerfA` asked only of the
  arms outside `Cov` (`Cov b ∨ PerfA …`), pinned to the same run.
* **`perfR_of`** (`PerfRo → PerfR` along the shell's run: KZ across the
  lookups and the decode, `kpc_restart`, `bdsc_restart`), **`invR_of`**; tops
  **`kcall_rdyOff5` / `kentry_rdyOff5`** (rd12b's `*rdyOff4r` with `InvRo`).
-/
import Fl4Proofs.P3.SpecInvRd14bB
open Classical

namespace Fl4Proofs.P3.SInvR.A14b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The covered arms -/

/-- The perform arms with a `PerfA` lemma. -/
def Cov : Fl4Invocation → Prop
  | .invokeNotification _ _ => True
  | .invokeEndpoint _ _ _ _ => True
  | .invokeDomain _ => True
  | .invokeIRQControl _ => True
  | .invokeIRQHandler (.aCKIrq _) => True
  | .invokeFl4TCB _ => True
  | .invokeCNode (.insertCall _ _ _) => True
  | .invokeCNode (.moveCall _ _ _) => True
  | .invokeCNode (.rotateCall _ _ _ _ _) => True
  | .invokeTCB (.setTLSBase _ _) => True
  | .invokeTCB (.setFlags _ _ _) => True
  | .invokeTCB (.notificationControl _ _) => True
  | .invokeTCB (.readRegisters _ false _ _) => True
  | .invokeTCB (.writeRegisters _ false _ _) => True
  | .invokeTCB (.copyRegisters _ _ false false _ _ _) => True
  | .invokeArchObject (.spec (.invokeASIDControl _)) => False
  | .invokeArchObject _ => True
  | _ => False

/-- **Every covered arm has `PerfA`** from the Restart state's facts. -/
theorem perfA_cov {σ0 u : State Unit} (bl cl dn : Bool) (b : Fl4Invocation) (hc : Cov b)
    (hB : A10.BS σ0) (hS : Suff σ0) (hK : A11.KP σ0 u) (hb : A11.CB0 u)
    (hbd : ∀ x, u.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc)
    (hsc : ∃ y n, u.kheap σ0.curSc = some (.schedContext y n))
    (hr : ∀ x, u.kheap σ0.curThread = some (.tcb x) → x.tcbState = .restart) : PerfA σ0 bl cl dn b u := by
  match b, hc with
  | .invokeNotification ep bd, _ => exact perfA_notification ep bd hB hS hK hbd hsc
  | .invokeEndpoint ep bd g gr, _ => exact perfA_endpoint ep bd g gr hB hS hK hbd hsc hr
  | .invokeDomain d, _ => exact perfA_domain bl cl dn d hK hb
  | .invokeIRQControl i, _ => exact perfA_irqControl bl cl dn i hK hb
  | .invokeIRQHandler (.aCKIrq irq), _ => exact perfA_irqAck bl cl dn irq hK hb
  | .invokeFl4TCB i, _ => exact perfA_fl4Tcb bl cl dn i hK hb
  | .invokeCNode (.insertCall c a d), _ => exact perfA_cnodeInsert bl cl dn c a d hK hb
  | .invokeCNode (.moveCall c a d), _ => exact perfA_cnodeMove bl cl dn c a d hK hb
  | .invokeCNode (.rotateCall c1 c2 a d e), _ => exact perfA_cnodeRotate bl cl dn c1 c2 a d e hK hb
  | .invokeTCB (.setTLSBase t v), _ => exact perfA_tlsBase bl cl dn t v hK hb
  | .invokeTCB (.setFlags t c f), _ => exact perfA_tcbFlags bl cl dn t c f hK hb
  | .invokeTCB (.notificationControl t n), _ => exact perfA_ntfnControl bl cl dn t n hK hb
  | .invokeTCB (.readRegisters src false n a), _ => exact perfA_readRegisters bl cl dn src n a hK hb
  | .invokeTCB (.writeRegisters d false v a), _ => exact perfA_writeRegisters bl cl dn d v a hK hb
  | .invokeTCB (.copyRegisters d src false false f i a), _ =>
    exact perfA_copyRegisters bl cl dn d src f i a hK hb
  | .invokeArchObject (.spec (.invokePageTable i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.spec (.invokePageDirectory i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.spec (.invokePDPT i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.spec (.invokePage i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.spec (.invokeASIDPool i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.spec (.invokeIOPort i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.spec (.invokeIOPortControl i)), _ =>
    exact perfA_archSpec bl cl dn _ (fun _ e => by cases e) hK hb
  | .invokeArchObject (.pml4Flush i), _ => exact perfA_pml4Flush bl cl dn i hK hb
  | .invokeArchObject (.deriveSubframe i), _ => exact perfA_deriveSubframe bl cl dn i hK hb
  | .invokeArchObject (.testAndClearAccessed p), _ => exact perfA_testAndClear bl cl dn p hK hb
  | .invokeArchObject (.spec (.invokeASIDControl _)), hc => exact False.elim hc
  | .invokeUntyped _, hc => exact False.elim hc
  | .invokeReply _ _, hc => exact False.elim hc
  | .invokeSchedContext _, hc => exact False.elim hc
  | .invokeSchedControl _, hc => exact False.elim hc
  | .invokeIRQHandler (.setIRQHandler _ _ _), hc => exact False.elim hc
  | .invokeIRQHandler (.clearIRQHandler _), hc => exact False.elim hc
  | .invokeCNode (.revokeCall _), hc => exact False.elim hc
  | .invokeCNode (.deleteCall _), hc => exact False.elim hc
  | .invokeCNode (.cancelBadgedSendsCall _), hc => exact False.elim hc
  | .invokeTCB (.readRegisters _ true _ _), hc => exact False.elim hc
  | .invokeTCB (.writeRegisters _ true _ _), hc => exact False.elim hc
  | .invokeTCB (.copyRegisters _ _ true _ _ _ _), hc => exact False.elim hc
  | .invokeTCB (.copyRegisters _ _ false true _ _ _), hc => exact False.elim hc
  | .invokeTCB (.threadControlCaps _ _ _ _ _ _ _), hc => exact False.elim hc
  | .invokeTCB (.threadControlSched _ _ _ _ _ _), hc => exact False.elim hc
  | .invokeTCB (.suspend _), hc => exact False.elim hc
  | .invokeTCB (.resume _), hc => exact False.elim hc

/-! ## The Restart state -/

/-- At the Restart state ct is bound to σ0's cur_sc and cur_sc is an SC. -/
theorem bdsc_restart {σ0 s : State Unit} (hB : A10.BS σ0) (hz : KZ σ0 s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1) :
    (∀ x, u.2.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc) ∧
      ∃ y n, u.2.kheap σ0.curSc = some (.schedContext y n) := by
  have hS := SVK.sv_setThreadState' _ _ s u hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  constructor
  · intro x hx
    have e := hS.1 σ0.curThread
    rw [hx] at e
    obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap σ0.curThread) (a := x.tcbSchedContext) e.symm
    rw [← et] at hy
    obtain ⟨x0, hx0, -, eb⟩ := kz_ct hz hy
    rw [← hys, ← eb]; exact hB.cs x0 hx0
  · obtain ⟨xa, c, z, m, hxa, hca, hkz, -⟩ := hB.ca hB.ni
    rw [hB.cs xa hxa] at hca; cases hca
    have e1 := kz_sv hz σ0.curSc
    rw [hkz] at e1
    obtain ⟨y1, hy1, -⟩ := SVK.sv_sc (o := s.kheap σ0.curSc) e1
    have e2 := hS.1 σ0.curSc
    rw [hy1] at e2
    obtain ⟨y2, hy2, -⟩ := SVK.sv_sc (o := u.2.kheap σ0.curSc) e2
    exact ⟨y2, m, hy2⟩

/-! ## The open arms only -/

/-- rd12b's `PerfR` with `PerfA` asked only of the arms outside `Cov`. -/
def PerfRo (σ0 : State Unit) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) (σ : State Unit) :
    Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE firstPhase cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1,
      Cov b ∨ PerfA σ0 blocking calling canDonate b u.2

/-- **`PerfRo` gives `PerfR`.** -/
theorem perfR_of {σ0 σ : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (hz : KZ σ0 σ)
    {calling blocking don fp : Bool} {cptr : CapRef} (h : PerfRo σ0 calling blocking don fp cptr σ) :
    PerfR σ0 calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    rw [et] at hu
    obtain ⟨hK, hb0⟩ := kpc_restart hB hz2 hu
    obtain ⟨hbd, hsc⟩ := bdsc_restart hB hz2 hu
    have hr : ∀ x, u.2.kheap σ0.curThread = some (.tcb x) → x.tcbState = .restart := by
      rw [← kz_curThread hz2]; exact SInv.sts_post hu
    exact perfA_cov blocking calling don b hc hB hS hK hb0 hbd hsc hr
  · exact hP

/-- rd12b's `InvR` with `PerfRo`. -/
def InvRo (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true →
    (∀ r cl bl dn, sendArgs c = some (r, cl, bl, dn) →
      ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfRo v.2 cl bl dn false g.1 g.2) ∧
    (∀ r cr, srArgs c = some (r, cr) → ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfRo v.2 false false true true g.1 g.2)

/-- **`InvRo` gives rd12b's `InvR`.** -/
theorem invR_of {c : Syscall} {σ : State Unit} (hEF : A8.EF σ) (h : InvRo c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_of hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg => perfR_of hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).2 r cr hc g hg)⟩

/-! ## The tops -/

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **`kcall_rdyOff4r` with `InvRo`** (only the arms outside `Cov` asked). -/
theorem kcall_rdyOff5 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → InvRo c σ)
    (hRT : ∀ c, ev = .syscallEvent c → RecvT rep c σ)
    (hOsR : ∀ c, ev = .syscallEvent c → RecvC c → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff4r hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB
    (fun c e => invR_of (hEF (by rw [e]; intro h; cases h)) (hP c e)) hRT hOsR hRdF

/-- **`kentry_rdyOff4r` with `InvRo`.** -/
theorem kentry_rdyOff5 (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ InvRo c w.2 ∧ RecvT rep c w.2 ∧ (RecvC c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOff4r hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, invR_of (A8.ef_fip h w hw) (hW w hw).2.1, (hW w hw).2.2.1, (hW w hw).2.2.2⟩

end Q

end

end Fl4Proofs.P3.SInvR.A14b
