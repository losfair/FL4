/-
P3 (DESIGN.md §9), invariant line G1 (rd14d): **arms that read the decode's
binding facts; the SchedContext bind of a TCB** (spec side only).

* **`ArmAKB C`**: every arm in `C` has `PerfA` at the Restart outcome of a
  `KZ σ0` state `s`, given sb2's `BindOK (bv h0) b` for a heap `h0` with
  sb2's binding frame `BR h0 s.kheap` (the decode's start heap);
  `armAKB_of` (`ArmAK` gives it), `ArmAKB.or`; **`bindOK_invE`** (every `ok`
  outcome of the shell's decode step `invE` has `BindOK` of the decode's start
  heap and the frame to its end: sb2's `okb_fl4Decode`, `sb_fl4DecodeInvocation`);
  **`perfR_ofKB`**, **`invR_ofKB`**, tops **`kcall_rdyOffKB`** /
  **`kentry_rdyOffKB`**.
* `unb_of_bindOK` (a TCB unbound in `bv h0` is unbound at the Restart
  outcome); **`perfA_scBindTcb`** (binding an unbound TCB `t`: `t ≠ ct` since
  ct is bound to cur_sc, so `TB` through rd14c's `tb_ik`).
* `CovB`, `armAKB_bind`, **`C14dC := C14dB ∨ CovB`** (every SchedContext arm
  now covered), **`armAKB_c14dC`**.
-/
import Fl4Proofs.P3.SpecInvRd14dB
open Classical

namespace Fl4Proofs.P3.SInvR.A14d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Arms with the decode's binding facts -/

/-- Every arm in `C` has `PerfA` at the Restart outcome, given the decode's `BindOK`. -/
def ArmAKB (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (bl cl dn : Bool) (b : Fl4Invocation), C b →
    A10.BS σ0 → Suff σ0 → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b → SInvB.BR h0 s.kheap →
    u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfA σ0 bl cl dn b u.2

theorem armAKB_of {C : Fl4Invocation → Prop} (h : ArmAK C) : ArmAKB C :=
  fun σ0 s u _ bl cl dn b hc hB hS hz _ _ hu => h σ0 s u bl cl dn b hc hB hS hz hu

theorem ArmAKB.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmAKB C1) (h2 : ArmAKB C2) :
    ArmAKB (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 bl cl dn b hc hB hS hz ho hr hu =>
    hc.elim (fun c => h1 σ0 s u h0 bl cl dn b c hB hS hz ho hr hu)
      (fun c => h2 σ0 s u h0 bl cl dn b c hB hS hz ho hr hu)

/-- **The decode step's binding facts.** -/
theorem bindOK_invE {fp : Bool} {cptr : CapRef} {t : ObjRef} {info : MessageInfo}
    {a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef} {s s' : State Unit} {b : Fl4Invocation}
    (h : ((.ok b, s') : Except SyscallError Fl4Invocation × State Unit) ∈ ((invE fp cptr t info a).run s).1) :
    ∃ h0, SInvB.BindOK (SInvB.bv h0) b ∧ SInvB.BR h0 s'.kheap := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold invE at h
  (try dsimp only at h)
  change _ ∈ (NonDet.bind (ExceptT.run (NonDetE.liftE (ε := SyscallError) (getMrs (Z := Unit) t buf info))) _ s).1
    at h
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := h
  obtain ⟨x, -, e⟩ := ft_mem_liftE hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨x.2.kheap, SInvB.okb_fl4Decode _ fp info.miLabel x.1 cptr sl cap ex buf x.2 rfl b s' hy,
    SInvB.sb_fl4DecodeInvocation (h0 := x.2.kheap) _ _ _ _ _ _ _ _ x.2 (SInvB.BR.refl _) _ hy⟩

/-- **`PerfRc` gives rd12b's `PerfR`** for any `C` with `ArmAKB C`. -/
theorem perfR_ofKB {C : Fl4Invocation → Prop} (hA : ArmAKB C) {σ0 σ : State Unit} (hB : A10.BS σ0)
    (hS : Suff σ0) (hz : KZ σ0 σ) {calling blocking don fp : Bool} {cptr : CapRef}
    (h : PerfRc C σ0 calling blocking don fp cptr σ) : PerfR σ0 calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    rw [et] at hu
    obtain ⟨h0, hok, hbr⟩ := bindOK_invE hb
    exact hA σ0 s' u h0 blocking calling don b hc hB hS hz2 hok hbr hu
  · exact hP

/-- **`InvRc` gives rd12b's `InvR`** for any `C` with `ArmAKB C`. -/
theorem invR_ofKB {C : Fl4Invocation → Prop} (hA : ArmAKB C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (h : InvRc C c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_ofKB hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg =>
      perfR_ofKB hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).2 r cr hc g hg)⟩

/-! ## SchedContext bind of a TCB -/

/-- A TCB unbound in `bv h0` is unbound at the Restart outcome. -/
theorem unb_of_bindOK {h0 : KHeap} {t : ObjRef} {s : State Unit} (hv : SInvB.bv h0 t = .t none)
    (hbr : SInvB.BR h0 s.kheap) {u : Unit × State Unit} {c : ObjRef} {ts : ThreadState}
    (hu : u ∈ (setThreadState (Z := Unit) c ts s).1) :
    ∀ x, u.2.kheap t = some (.tcb x) → x.tcbSchedContext = none := by
  intro x hx
  have e := (SVK.sv_setThreadState' c ts s u hu).1 t
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := SVK.sv_tcb (o := s.kheap t) (a := x.tcbSchedContext) e.symm
  obtain ⟨xh, hxh, eh⟩ := SInvB.bv_t.1 hv
  obtain ⟨x2, hx2, e2⟩ := hbr.tcb t xh hxh
  have ex : x2 = x0 := by
    rw [hx0] at hx2; exact (KernelObject.tcb.inj (Option.some.inj hx2)).symm
  rw [← e0, ← ex, e2, eh]

theorem perfA_scBindTcb {σ0 s : State Unit} (bl call don : Bool) (c t : ObjRef) (hB : A10.BS σ0)
    (hS : Suff σ0) (h0 : TB σ0 s) (hct : ∃ x, s.kheap σ0.curThread = some (.tcb x))
    (ht : ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext = none) :
    PerfA σ0 bl call don (.invokeSchedContext (.invokeSchedContextBind c (.threadCap t))) s := by
  have hne : t ≠ σ0.curThread := by
    intro e; subst e
    obtain ⟨x, hx⟩ := hct
    have h1 := h0.bd x hx
    rw [ht x hx] at h1; cases h1
  refine perfA_liftTB _ rfl hB hS ?_ h0
  show IK (TB σ0) (do schedContextBindTcb (Z := Unit) c t; return [])
  refine ik_bind ?_ fun _ => ik_pure _
  refine tb_ik ?_ ?_ ?_
  · unfold schedContextBindTcb; cfk_auto
  · unfold schedContextBindTcb
    refine ik_bind (A8.cp_threadSet _ _ _ _) fun _ => ik_bind (by cp_leaf) fun _ => ?_
    refine ik_bind (A8.cp_ifCondTest _ _ σ0 _) fun _ => ik_bind (A8.cp_schedContextResume _ σ0 _) fun _ => ?_
    exact ik_bind (ik_gets _) fun _ => ik_when _ (by cp_auto)
  · unfold schedContextBindTcb
    refine SInv.ik_bind (SInv.ik_and (tp_threadSet _ _ fun _ _ e => absurd e hne) (by ks_auto)) fun _ => ?_
    refine SInv.ik_bind (SInv.ik_and (by qb_auto) (by ks_auto)) fun _ => ?_
    refine SInv.ik_bind (bl_of_nks (nks_ifCondG _ _ _)) fun _ => ?_
    refine SInv.ik_bind (bl_of_nks (nks_schedContextResume _)) fun _ => ?_
    refine SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_when _ ?_
    exact SInv.ik_bind (bl_of_svm (by sv_auto)) fun _ => bl_of_svm SVK.sv_rescheduleRequired'

def CovB : Fl4Invocation → Prop
  | .invokeSchedContext (.invokeSchedContextBind _ (.threadCap _)) => True
  | _ => False

theorem armAKB_bind : ArmAKB CovB := by
  intro σ0 s u h0 bl cl dn b hc hB hS hz hok hbr hu
  cases b
  case invokeSchedContext i =>
    cases i
    case invokeSchedContextBind c cap =>
      cases cap
      case threadCap t =>
        have hrf := rf_restart hB hS hz hu
        exact perfA_scBindTcb bl cl dn c t hB hS hrf.tb hrf.ct (unb_of_bindOK hok.2 hbr hu)
      all_goals exact (hc : False).elim
    all_goals exact (hc : False).elim
  all_goals exact (hc : False).elim

/-- rd14d's arms: rd14c's, the SchedContext arms, cancelBadgedSends, SchedControl. -/
def C14dC (b : Fl4Invocation) : Prop := C14dB b ∨ CovB b

theorem armAKB_c14dC : ArmAKB C14dC := (armAKB_of armAK_c14dB).or armAKB_bind

/-! ## The tops over any `ArmAKB` set -/

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **rd12b's `kcall_rdyOff4r` with `InvRc C`** for any covered set `C`
with `ArmAKB C`. -/
theorem kcall_rdyOffKB {C : Fl4Invocation → Prop} (hA : ArmAKB C) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
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
    (fun c e => invR_ofKB hA (hEF (by rw [e]; intro h; cases h)) (hP c e)) hRT hOsR hRdF

/-- **rd12b's `kentry_rdyOff4r` with `InvRc C`.** -/
theorem kentry_rdyOffKB {C : Fl4Invocation → Prop} (hA : ArmAKB C) (hnd : numDomains = 1) (rep : Bool) (c : Syscall)
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
    ⟨(hW w hw).1, invR_ofKB hA (A8.ef_fip h w hw) (hW w hw).2.1, (hW w hw).2.2.1, (hW w hw).2.2.2⟩

end Q

end

end Fl4Proofs.P3.SInvR.A14d
