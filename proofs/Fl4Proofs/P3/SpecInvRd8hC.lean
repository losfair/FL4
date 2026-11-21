/-
P3 (DESIGN.md §9), invariant line G1 (rd8h, rd8f handoff 1 rest):
**every `invoke_tcb` arm keeps `Rdy`** (spec side only, outside the JAtZ
cone).

* **`rd_restart t s (hR : Rdy s) (hB : ScBackS s)`**: cancel_ipc (rd8f's
  `rd_cancelIpc`), the Restart write, the unblock check (`rd_ifCond`),
  `sched_context_resume` (rd's `sr_schedContextResume`: the mutual binding
  read at the start by `ScBackS`, carried by sb2's `BR` across the prefix;
  an unbound thread by `sr_unbound`), then `possible_switch_to` under
  `schedulable` (`rd_possibleSwitchTo_p`).
* `RO C I m`: `Rdy` at every outcome and rd8f's `RB C I` at the `ok`
  outcomes; `ro_bind`, `ro_ret`. `io_installTcbCap` / `io_installTcbFrameCap`
  (vi3's IdleScOutV, as `vo_install*` without `VI`),
  `rd_installTcbFrameCap`, **`ro_installTcbCap`**, **`ro_installTcbFrameCap`**
  (RB's members by their families: ctq's DK, q1, sb2's si, gk, io, isk).
* Arms: `rd_tcCaps` (four installs and the frame install by `RO`),
  `rd_tcCopy` / `rd_tcWrite` (the resume of the target by `rd_restart`, ScInv
  carried by sb2's leaves to it), `rd_tcRead`, `rd_tcNtfn`, `rd_tcTls`,
  `rd_tcFlags`, `rd_tcSuspend`, `rd_tcResume`.
* **`rd_invokeTcbP`**: every arm of the TCB perform from `RB ct I`,
  `RdyT ct` and `TcbOK` (ThreadControlSched: VfhAll's slot-3 fact and the
  decode's `BindRel`, as Rd8hB's `rd_tcSched`).
-/
import Fl4Proofs.P3.SpecInvRd8hR
import Fl4Proofs.P3.SpecInvSbN
import Fl4Proofs.P3.SpecInvUtO1
import Fl4Proofs.P3.SpecInvSbG6
import Fl4Proofs.P3.SpecInvSbF4
import Fl4Proofs.P3.SpecInvCqF5
import Fl4Proofs.P3.SpecInvSlI6
import Fl4Proofs.P3.SpecInvValidMachineTimeGen
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `restart` -/

/-- **`restart t`** keeps `Rdy` (module docstring). -/
theorem rd_restart (t : ObjRef) (s : State Unit) (hR : Rdy s) (hB : SInvB.ScBackS s) :
    ∀ y ∈ (restart (Z := Unit) t s).1, Rdy y.2 := by
  intro y hy
  unfold restart at hy
  obtain ⟨⟨st, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  obtain ⟨z2, h2, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet h2
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  swap
  · rw [Set.mem_singleton_iff.1 hy]; exact hR
  obtain ⟨z3, h3, hy⟩ := hy
  have r3 : Rdy z3.2 := B8f.rd_cancelIpc t s hR z3 h3
  have b3 : SInvB.BRs s.kheap z3.2 := SInvB.sb_cancelIpc t s (SInvB.BR.refl _) z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have r4 : Rdy z4.2 := rd_setThreadState t .restart trivial z3.2 r3 z4 h4
  have b4 : SInvB.BRs s.kheap z4.2 := SInvB.sb_setThreadState t .restart z3.2 b3 z4 h4
  obtain ⟨z5, h5, hy⟩ := hy
  have r5 : Rdy z5.2 := (rd_ifCond x.tcbSchedContext (some false) (some false) z4.2 r4 h5).1
  have b5 : SInvB.BRs s.kheap z5.2 :=
    SInvB.sb_ifCondRefillUnblockCheck x.tcbSchedContext (some false) (some false) z4.2 b4 z5 h5
  obtain ⟨z6, h6, hy⟩ := hy
  have r6 : Rdy z6.2 := (ik_maybeM (fun p => rd_schedContextResume p) x.tcbSchedContext) z5.2 r5 z6 h6
  have sr6 : SR t z6.2 := by
    cases hc : x.tcbSchedContext with
    | none =>
      rw [hc] at h6
      obtain rfl := Set.mem_singleton_iff.1 h6
      obtain ⟨x', hx', e'⟩ := b5.tcb t x hx
      exact sr_unbound hx' (e'.trans hc)
    | some p =>
      rw [hc] at h6
      obtain ⟨y0, k0, hy0, hyt, -⟩ := hB t x p hx hc
      refine sr_schedContextResume p t z5.2 (fun y n hy => ?_) (fun x' hx' => ?_) h6
      · obtain ⟨y', n', hy', hk⟩ := b5.sc p y0 k0 hy0
        rw [hy] at hy'; cases hy'; exact hk.1.trans hyt
      · obtain ⟨x'', hx'', e''⟩ := b5.tcb t x hx
        rw [hx'] at hx''; cases hx''; exact e''.trans hc
  unfold testPossibleSwitchTo at hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  dsimp only at hy
  unfold NonDet.when at hy
  split_ifs at hy with hs
  · exact rd_possibleSwitchTo_p t z6.2 (sr6 hs) r6 y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact r6

/-! ## The cap installs: `Rdy` everywhere, `RB` at the `ok` outcomes -/

/-- `Rdy` at every outcome, rd8f's `RB C I` at the `ok` outcomes. -/
def RO (C I : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, B8f.RB C I σ → ∀ y ∈ (m.run σ).1, Rdy y.2 ∧ (∀ a, y.1 = .ok a → B8f.RB C I y.2)

variable {C I : ObjRef}

theorem ro_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hm : RO C I m) (hf : ∀ a, RO C I (f a)) : RO C I (m >>= f) := by
  intro σ h y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · exact hf a z.2 ((hm σ h z hz).2 a ha) y hy
  · exact ⟨(hm σ h z hz).1, fun a h' => by cases h'⟩

theorem ro_ret {ε α : Type} (a : α) : RO C I (NonDetE.returnOk a : NonDetE (State Unit) ε α) := by
  intro σ h y hy
  rw [SInvU.mem_ret_ok hy]
  exact ⟨h.1, fun _ _ => h⟩

theorem io_installTcbCap (N : Irq → ObjRef) (target : ObjRef) (slot : CslotPtr) (n : Nat)
    (o : Option (Cap × CslotPtr)) : IKE (SInvU.IO N) (installTcbCap (Z := Unit) target slot n o) := by
  cases o with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine ike_bind (SInvU.io_capDelete _) fun _ => ?_
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (SInvU.io_checkCapAt_ins c src _ slot _)

theorem io_installTcbFrameCap (N : Irq → ObjRef) (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (SInvU.IO N) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  cases buffer with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    simp only [installTcbFrameCap]
    refine ike_bind (SInvU.io_capDelete _) fun _ => ?_
    refine ike_bind (ike_liftE (by io0_auto)) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · cases frame with
      | none => exact ik_pure _
      | some q =>
        obtain ⟨c, src⟩ := q
        exact SInvU.io_checkCapAt_ins c src _ slot _
    · exact ike_bind (ike_liftE (ik_gets _)) fun _ => ike_liftE (by io0_auto)

/-- `install_tcb_frame_cap` keeps `Rdy` at every outcome from `RB`. -/
theorem rd_installTcbFrameCap (C I t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr)))
    (σ : State Unit) (h : B8f.RB C I σ) :
    ∀ y ∈ ((installTcbFrameCap (Z := Unit) t sl b).run σ).1, Rdy y.2 := by
  intro y hy
  rcases b with _ | ⟨ptr, frame⟩
  · rw [SInvU.mem_ret_ok hy]; exact h.1
  · simp only [installTcbFrameCap] at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' : Rdy z.2 := (B8f.rb_capDelete (C := C) (I := I) _ σ h z hz).1
      refine (show IKE Rdy _ from ?_) z.2 hz' y hy
      refine ike_bind (ike_liftE (rd_threadSet _ _ fun _ => ⟨rfl, rfl, rfl⟩)) fun _ => ?_
      refine ike_bind (ike_liftE ?_) fun _ => ?_
      · rcases frame with _ | ⟨c, src⟩
        · exact ik_pure _
        · exact rd_checkCapAt _ _ _ (rd_checkCapAt _ _ _ (rd_capInsert _ _ _))
      · exact ike_bind (ike_liftE (ik_gets _)) fun _ => ike_liftE (ik_when _ rd_rescheduleRequired)
    · exact (B8f.rb_capDelete (C := C) (I := I) _ σ h z hz).1

theorem ro_installTcbCap (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    RO C I (installTcbCap (Z := Unit) t sl n o) := by
  intro σ h y hy
  have r := rd_install C I t sl n o σ h y hy
  refine ⟨r, fun a ha => ⟨r, (R14.dk_installTcbCapD C t sl n o σ h.2.1 y hy).2 a ha,
    SInvQ.q1_installTcbCap t sl n o σ h.2.2.1 y hy, SInvB.si_installTcbCap t sl n o σ h.2.2.2.1 y hy,
    SInvV.gk_installTcbCap t sl n o _ SInvV.wl_vmt σ h.2.2.2.2.1 y hy,
    io_installTcbCap _ t sl n o σ h.2.2.2.2.2.1 y hy, SInvL.isk_installTcbCap t sl n o σ h.2.2.2.2.2.2 y hy⟩⟩

theorem ro_installTcbFrameCap (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    RO C I (installTcbFrameCap (Z := Unit) t sl b) := by
  intro σ h y hy
  have r := rd_installTcbFrameCap C I t sl b σ h y hy
  refine ⟨r, fun a ha => ⟨r, (R14.dk_installTcbFrameCapD C t sl b σ h.2.1 y hy).2 a ha,
    SInvQ.q1_installTcbFrameCap t sl b σ h.2.2.1 y hy, SInvB.si_installTcbFrameCap t sl b σ h.2.2.2.1 y hy,
    SInvV.gk_installTcbFrameCap t sl b _ SInvV.wl_vmt σ h.2.2.2.2.1 y hy,
    io_installTcbFrameCap _ t sl b σ h.2.2.2.2.2.1 y hy, SInvL.isk_installTcbFrameCap t sl b σ h.2.2.2.2.2.2 y hy⟩⟩

/-! ## The arms -/

macro "rdh_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact B8f.rd_suspend _) | (with_reducible exact rd_asUser _ _)
  | (with_reducible exact rd_archGetSanitiseRegisterInfo _) | (with_reducible exact rd_archPostModifyRegisters _ _)
  | (with_reducible exact rd_rescheduleRequired) | (with_reducible exact rd_bindNotification _ _)
  | (with_reducible exact rd_unbindNotification _) | (with_reducible exact rd_setFlags _ _)
  | (with_reducible exact rd_archPostSetFlags _ _) | ik_step0 | ik_unfold))

theorem ikRS {α : Type} {m : NonDet (State Unit) α} (hR : IK Rdy m) (hS : SInvB.SIK m) :
    IK (fun s => Rdy s ∧ SInvB.ScInv s) m :=
  fun σ h y hy => ⟨hR σ h.1 y hy, hS σ h.2 y hy⟩

theorem rd_tcCaps (bl call don : Bool) (t : ObjRef) (sl : CslotPtr) (fh th cr vr : Option (Cap × CslotPtr))
    (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) (σ : State Unit) (h : B8f.RB C I σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don
      (.invokeTCB (.threadControlCaps t sl fh th cr vr buf))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  exact ((ro_bind (ro_installTcbCap _ _ _ _) fun _ => ro_bind (ro_installTcbCap _ _ _ _) fun _ =>
    ro_bind (ro_installTcbCap _ _ _ _) fun _ => ro_bind (ro_installTcbCap _ _ _ _) fun _ =>
    ro_bind (ro_installTcbFrameCap _ _ _) fun _ => ro_ret _) σ h y hy).1

theorem rd_tcSuspend (bl call don : Bool) (t : ObjRef) (σ : State Unit) (hR : Rdy σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.suspend t))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  exact (show IKE Rdy _ from ike_liftE (ik_bind (B8f.rd_suspend t) fun _ => ik_pure _)) σ hR y hy

theorem rd_tcResume (bl call don : Bool) (t : ObjRef) (σ : State Unit) (hR : Rdy σ) (hI : SInvB.ScInv σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.resume t))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
  obtain ⟨z, hz, hx⟩ := hx
  have r := rd_restart t σ hR hI.back z hz
  rw [Set.mem_singleton_iff.1 hx]; exact r

theorem rd_tcCopy (bl call don : Bool) (d src : ObjRef) (a b c e : Bool) (ar : ArchCopyRegisterSets)
    (σ : State Unit) (hR : Rdy σ) (hI : SInvB.ScInv σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don
      (.invokeTCB (.copyRegisters d src a b c e ar))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
  obtain ⟨z1, h1, hx⟩ := hx
  have k1 := ikRS (ik_when _ (B8f.rd_suspend src)) (ik_when _ (SInvB.sik_of_sbk fun _ => SInvB.sb_suspend src))
    σ ⟨hR, hI⟩ z1 h1
  obtain ⟨z2, h2, hx⟩ := hx
  have r2 : Rdy z2.2 := by
    unfold NonDet.when at h2
    split at h2
    · exact rd_restart d z1.2 k1.1 k1.2.back z2 h2
    · rw [Set.mem_singleton_iff.1 h2]; exact k1.1
  exact (show IK Rdy _ by rdh_auto) z2.2 r2 x hx

theorem rd_tcRead (bl call don : Bool) (src : ObjRef) (a : Bool) (n : Word) (ar : ArchCopyRegisterSets)
    (σ : State Unit) (hR : Rdy σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don
      (.invokeTCB (.readRegisters src a n ar))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  exact (show IKE Rdy _ from ike_liftE (by rdh_auto)) σ hR y hy

theorem rd_tcWrite (bl call don : Bool) (d : ObjRef) (a : Bool) (vs : List Word) (ar : ArchCopyRegisterSets)
    (σ : State Unit) (hR : Rdy σ) (hI : SInvB.ScInv σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don
      (.invokeTCB (.writeRegisters d a vs ar))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
  obtain ⟨z1, h1, hx⟩ := hx
  have k1 := ikRS (ik_gets _) (ik_gets _) σ ⟨hR, hI⟩ z1 h1
  obtain ⟨z2, h2, hx⟩ := hx
  have k2 := ikRS (rd_archGetSanitiseRegisterInfo _) (SInvB.sik_of_sbk fun _ => by sb_auto) z1.2 k1 z2 h2
  obtain ⟨z3, h3, hx⟩ := hx
  have k3 := ikRS (rd_asUser _ _) (SInvB.sik_of_sbk fun _ => SInvB.sb_asUser _ _) z2.2 k2 z3 h3
  obtain ⟨z4, h4, hx⟩ := hx
  have k4 := ikRS (rd_archPostModifyRegisters _ _) (SInvB.sik_of_sbk fun _ => by sb_auto) z3.2 k3 z4 h4
  obtain ⟨z5, h5, hx⟩ := hx
  have r5 : Rdy z5.2 := by
    unfold NonDet.when at h5
    split at h5
    · exact rd_restart d z4.2 k4.1 k4.2.back z5 h5
    · rw [Set.mem_singleton_iff.1 h5]; exact k4.1
  exact (show IK Rdy _ by rdh_auto) z5.2 r5 x hx

theorem rd_tcNtfn (bl call don : Bool) (t : ObjRef) (n : Option ObjRef) (σ : State Unit) (hR : Rdy σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don
      (.invokeTCB (.notificationControl t n))).run σ).1, Rdy y.2 := by
  intro y hy
  cases n
  · simp only [fl4PerformInvocation, invokeTcb] at hy
    exact (show IKE Rdy _ from ike_liftE (by rdh_auto)) σ hR y hy
  · simp only [fl4PerformInvocation, invokeTcb] at hy
    exact (show IKE Rdy _ from ike_liftE (by rdh_auto)) σ hR y hy

theorem rd_tcTls (bl call don : Bool) (t : ObjRef) (b : Word) (σ : State Unit) (hR : Rdy σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.setTLSBase t b))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  exact (show IKE Rdy _ from ike_liftE (by rdh_auto)) σ hR y hy

theorem rd_tcFlags (bl call don : Bool) (t : ObjRef) (c s : TcbFlags) (σ : State Unit) (hR : Rdy σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.setFlags t c s))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  exact (show IKE Rdy _ from ike_liftE (by rdh_auto)) σ hR y hy

/-- The per-arm facts of a TCB invocation at the perform: ThreadControlSched
needs VfhAll's slot-3 fact (a null or endpoint cap) and the decode's
`BindRel` for a new SC. -/
def TcbOK (σ : State Unit) : TcbInvocation → Prop
  | .threadControlSched t _ fh _ _ sc =>
    (fh ≠ none → ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c) ∧
      (∀ c, sc = some (some c) → BindRel σ c t)
  | _ => True

/-- **Every arm of the TCB perform keeps `Rdy`** from `RB ct I`, `RdyT ct`
and `TcbOK`. -/
theorem rd_invokeTcbP (bl call don : Bool) (i : TcbInvocation) (I : ObjRef) (σ : State Unit)
    (hRB : B8f.RB σ.curThread I σ) (hRT : RdyT σ σ.curThread) (hOK : TcbOK σ i) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB i)).run σ).1, Rdy y.2 := by
  cases i with
  | threadControlSched t sl fh mcp prio sc => exact rd_tcSched bl call don t sl fh mcp prio sc I σ hRB hRT hOK.1 hOK.2
  | suspend t => exact rd_tcSuspend bl call don t σ hRB.1
  | resume t => exact rd_tcResume bl call don t σ hRB.1 hRB.2.2.2.1
  | threadControlCaps t sl fh th cr vr buf => exact rd_tcCaps bl call don t sl fh th cr vr buf σ hRB
  | copyRegisters d s a b c e ar => exact rd_tcCopy bl call don d s a b c e ar σ hRB.1 hRB.2.2.2.1
  | readRegisters s a n ar => exact rd_tcRead bl call don s a n ar σ hRB.1
  | writeRegisters d a vs ar => exact rd_tcWrite bl call don d a vs ar σ hRB.1 hRB.2.2.2.1
  | notificationControl t n => exact rd_tcNtfn bl call don t n σ hRB.1
  | setTLSBase t b => exact rd_tcTls bl call don t b σ hRB.1
  | setFlags t c s => exact rd_tcFlags bl call don t c s σ hRB.1

end

end Fl4Proofs.P3.SInvR.B8h
