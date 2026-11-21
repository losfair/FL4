/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi2): **valid_idle across the kernel
entries** (vi1's handoff steps 5-6), reduced to one named obligation `ViGap` for the
decode-dependent performs.

* `ViGapInv` / **`ViGap`** (the REMAINING obligation, not an invariant premise; ut7's
  `PerfGap` pattern): the untyped, TCB, SchedContext and ASID-control performs keep
  `VI N S true` from a `VI` state whose view satisfies `IO (fun _ => N)` (no cap covers the
  idle thread, sg1's `IdleOutV`), `IrqOutV (fun _ => S)` (no cap covers the idle SC,
  `IdleScOutV`) and `UtInv''`, for an invocation decoded from that view (ut7's
  `DecodedFrom`). What each needs (believed true, l4v `invoke_untyped_invs`,
  `invoke_tcb_invs`, `invoke_sched_context_invs`, `perform_asid_control_invocation_invs`):
  thread-cap targets `≠ N` (the cap is held: `IO`), SC-cap pointers `≠ S` (held: `IrqOutV
  (fun _ => S)`), retype / detype regions `∌ N, S` (an untyped / frame cap's `covR` is its
  region) and retyped objects default.
* `vi_fl4Perform` (every other perform; the endpoint send with the pinned donor),
  `W N S T σ0 s` (VIT at `s`, the entry's cap view and current thread: the invocation
  prefix keeps all three), the shell `vi_handleInvocationR`, the syscalls, the events,
  `fl4CallKernel`, the entry.
* **`CtSc σ` [J]**: the current thread is bound to an SC at a syscall entry (l4v
  `cur_sc_tcb_are_bound` with `sym_refs`; INV-PLAN B2's `CurInv.tcb` is the same fact
  with the SC named). Needed only by `ReplyRecv` / `NBSendRecv` / `NBSendWait`, whose
  non-call send may donate `the sender_sc`. It is not derivable from what is carried:
  `ScInv` relates existing bindings only, and a Running / Restart thread may be unbound
  (a passive server woken by a reply-less signal, a resumed passive thread); l4v gets it
  from `valid_sched` (`ct_active ⟶ is_schedulable_bool ct`) at the entry. The previous
  exit establishes it: `schedule` switches only to a `schedulable` thread (bound to an
  active SC) or to idle, and between `schedule` and the next entry nothing runs.
* **`IdleScOutV σ := IrqOutV (fun _ => σ.idleSc) (uV σ)`**: carried for free by sg1's
  `sgN_kentry` at `M := fun _ => idleSc` (no new [J]).
* Tops: **`kentry_validIdle_of (hG : ViGap) (c) (hV : ValidIdle σ) (hS : SpecGlobS σ ∧
  IdleOutV σ) (hI : IdleScOutV σ) (hU : UtInv3 σ) (ha : ct active) (hct : pinned c →
  CtSc σ)`** and **`kcall_validIdle_of`** (every event).
-/
import Fl4Proofs.P3.SpecInvViG
import Fl4Proofs.P3.SpecInvUtO6
import Fl4Proofs.P3.SpecInvSgE
import Fl4Proofs.P3.SpecInvNtfnQC4
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef}

/-! ## The remaining obligation -/

/-- The performs that need decode facts. -/
def ViGapInv : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeTCB _ => True
  | .invokeSchedContext _ => True
  | .invokeArchObject (.spec (.invokeASIDControl _)) => True
  | _ => False

/-- **The remaining obligation** (module docstring). -/
def ViGap : Prop :=
  ∀ (N S : ObjRef) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit), ViGapInv inv →
    VI N S true σ → IO (fun _ => N) σ → IrqOutV (fun _ => S) (uV σ) → UtInv'' σ → DecodedFrom (uV σ) inv →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, VI N S true y.2

/-! ## The performs -/

theorem vi_invokeCnodeO (ci : CnodeInvocation) :
    ∀ σ, VO N S true σ → ∀ z ∈ ((invokeCnode (Z := Unit) ci).run σ).1, VI N S true z.2 := by
  intro σ hσ z hz
  cases ci
  case revokeCall sl => exact (vo_capRevoke sl σ hσ z hz).1
  case deleteCall sl => exact (vo_capDelete sl σ hσ z hz).1
  case insertCall c a d =>
    exact (show IKE (VI N S true) (invokeCnode (Z := Unit) (.insertCall c a d)) by
      simp only [invokeCnode]; vi_auto) σ hσ.1 z hz
  case moveCall c a d =>
    exact (show IKE (VI N S true) (invokeCnode (Z := Unit) (.moveCall c a d)) by
      simp only [invokeCnode]; vi_auto) σ hσ.1 z hz
  case rotateCall c1 c2 s1 s2 s3 =>
    exact (show IKE (VI N S true) (invokeCnode (Z := Unit) (.rotateCall c1 c2 s1 s2 s3)) by
      simp only [invokeCnode]; vi_auto) σ hσ.1 z hz
  case cancelBadgedSendsCall c =>
    -- the nested `.cancelBadgedSendsCall (.endpointCap …)` pattern reduces only on a constructor
    cases c
    all_goals exact (show IKE (VI N S true) (invokeCnode (Z := Unit) (.cancelBadgedSendsCall _)) by
      simp only [invokeCnode]; vi_auto) σ hσ.1 z hz

theorem vi_fl4ArchPerform {b : Bool} (ai : Fl4ArchInvocation) (h : ∀ a, ai ≠ .spec (.invokeASIDControl a)) :
    IKE (VI N S b) (fl4ArchPerformInvocation (Z := Unit) ai) := by
  cases ai
  case spec i =>
    cases i
    case invokeASIDControl a => exact absurd rfl (h a)
    all_goals simp only [fl4ArchPerformInvocation, archPerformInvocation]; vi_auto
  all_goals simp only [fl4ArchPerformInvocation]; vi_auto

set_option maxHeartbeats 8000000 in
theorem vi_fl4Perform (hG : ViGap) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hV : VIT N S T true σ) (hO : IO (fun _ => N) σ) (hS : IrqOutV (fun _ => S) (uV σ)) (hU : UtInv'' σ)
    (hD : DecodedFrom (uV σ) inv) (hT : don = true → call = false → T = σ.curThread) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, VI N S true y.2 := by
  intro y hy
  have hV' : VI N S true σ := vi_of_vit hV
  cases inv
  case invokeUntyped ui => exact hG N S blk call don (.invokeUntyped ui) σ trivial hV' hO hS hU hD y hy
  case invokeTCB i => exact hG N S blk call don (.invokeTCB i) σ trivial hV' hO hS hU hD y hy
  case invokeSchedContext i => exact hG N S blk call don (.invokeSchedContext i) σ trivial hV' hO hS hU hD y hy
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    obtain ⟨z, hz, hx⟩ := hx
    rw [mem_gets_vi hz] at hx
    obtain ⟨w, hw, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    exact vh_sendIpc blk call bd g gr don σ.curThread ep (hV.2.2.1 rfl) hT σ hV w hw
  case invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact vi_invokeCnodeO ci σ ⟨hV', hO⟩ z hz
  case invokeArchObject ai =>
    by_cases hm : ∃ a, ai = .spec (.invokeASIDControl a)
    · obtain ⟨a, rfl⟩ := hm
      exact hG N S blk call don (.invokeArchObject (.spec (.invokeASIDControl a))) σ trivial hV' hO hS hU hD y hy
    · simp only [fl4PerformInvocation] at hy
      exact vi_fl4ArchPerform ai (fun a e => hm ⟨a, e⟩) σ hV' y hy
  all_goals exact (show IKE (VI N S true) _ by simp only [fl4PerformInvocation]; vi_auto) σ hV' y hy

/-! ## The invocation shell -/

/-- `VIT` at `s` with the entry's cap view and current thread. -/
def W (N S T : ObjRef) (σ0 s : State Unit) : Prop :=
  VIT N S T true s ∧ uV s = uV σ0 ∧ s.curThread = σ0.curThread

theorem w_step {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : IKE (VIT N S T true) m) (h2 : ∀ v, UKE v m)
    (h3 : ∀ c, CTKE c m) {σ0 s : State Unit} (hs : W N S T σ0 s) : ∀ w ∈ (m.run s).1, W N S T σ0 w.2 :=
  fun w hw => ⟨h1 s hs.1 w hw, (h2 (uV s) s rfl w hw).trans hs.2.1, (h3 s.curThread s rfl w hw).trans hs.2.2⟩

theorem w_stepN {α : Type} {m : NonDet (State Unit) α} (h1 : IK (VIT N S T true) m) (h2 : ∀ v, UK v m)
    (h3 : ∀ c, CTK c m) {σ0 s : State Unit} (hs : W N S T σ0 s) : ∀ w ∈ (m s).1, W N S T σ0 w.2 :=
  fun w hw => ⟨h1 s hs.1 w hw, (h2 (uV s) s rfl w hw).trans hs.2.1, (h3 s.curThread s rfl w hw).trans hs.2.2⟩

theorem io_of_w {σ0 s : State Unit} (hs : W N S T σ0 s) {M : Irq → ObjRef} (h : IrqOutV M (uV σ0)) :
    IrqOutV M (uV s) := by rw [hs.2.1]; exact h

set_option maxHeartbeats 16000000 in
/-- **The invocation keeps `VI`** (the pinned `T` is the current thread when the send may donate). -/
theorem vi_handleInvocationR (hG : ViGap) (rep calling blocking don fp : Bool) (cptr : CapRef)
    {σ0 σ : State Unit} (hW : W N S T σ0 σ) (hO : IO (fun _ => N) σ0) (hS : IrqOutV (fun _ => S) (uV σ0))
    (hU : UtInv'' σ0) (hT : don = true → calling = false → T = σ0.curThread) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, VI N S true y.2 := by
  intro y hy
  unfold fl4HandleInvocationR at hy
  obtain ⟨z, hz, ⟨thread, hth, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := mem_liftE' hz; simp [hx] at he
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
  rw [mem_gets_vi hx] at hth hy
  simp only [Except.ok.injEq] at hth
  subst hth
  have hct : σ.curThread ≠ N := hW.1.2.2.1 rfl
  obtain ⟨z, hz, ⟨info, hinfo, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
  swap
  · exact vi_of_vit (w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hW z hz).1
  have hWz : W N S T σ0 z.2 := w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hW z hz
  obtain ⟨r1, s1⟩ := z
  simp only at hinfo hWz hy
  subst hinfo
  have hOk : OkV (uV s1) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV s1).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV s1).2.1 p.2 = some p.1 ∧ DestRefV (uV s1) p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) σ.curThread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false σ.curThread
       let extracaps ← lookupExtraCaps σ.curThread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := W N S T σ0) (Q := VI N S true)
    (fun w hw => w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hWz w hw) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK (VI N S true) (NonDet.when blocking (handleFault σ.curThread f)) by vi_auto) s (vi_of_vit hs.1) v hv
  · intro a s has w hw
    have hs : W N S T σ0 s := w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hWz _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hs w hw
  · intro e s hs v hv
    exact (show IK (VI N S true) _ by vi_auto) s (vi_of_vit hs.1) v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hs : W N S T σ0 s := w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hWz _ has
    obtain ⟨hc, hex⟩ := hOk s1 rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV s := uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0
    have hvs : uV s = uV s1 := hs.2.1.trans hWz.2.1.symm
    have hD : DecodedFrom (uV s') b := by
      rw [hI'.2.1, ← hWz.2.1]
      exact ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx.trans hvs, hc, hex, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : W N S T σ0 z.2 := w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hI' z hz
      obtain ⟨r, s2⟩ := z
      simp only at hu hz'; subst hu
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s3⟩ := z2
        simp only at hr; subst hr
        have hD2 : DecodedFrom (uV s2) b := by rw [hz'.2.1, ← hI'.2.1]; exact hD
        have hs3 := vi_fl4Perform hG blocking calling don b s2 hz'.1 (io_of_w hz' hO) (io_of_w hz' hS)
          (by show UtInv''V (uV s2); rw [hz'.2.1]; exact hU) hD2 (fun h1 h2 => (hT h1 h2).trans hz'.2.2.symm) _ hz2
        exact (show IKE (VI N S true) _ by vi_auto) s3 hs3 y hy
      · have hD2 : DecodedFrom (uV s2) b := by rw [hz'.2.1, ← hI'.2.1]; exact hD
        exact vi_fl4Perform hG blocking calling don b s2 hz'.1 (io_of_w hz' hO) (io_of_w hz' hS)
          (by show UtInv''V (uV s2); rw [hz'.2.1]; exact hU) hD2 (fun h1 h2 => (hT h1 h2).trans hz'.2.2.symm) _ hz2
    · exact vi_of_vit (w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hI' z hz).1

/-! ## Syscalls -/

/-- The syscalls whose non-call send may donate. -/
def Pinned (c : Syscall) : Prop := c = .sysReplyRecv ∨ c = .sysNBSendRecv ∨ c = .sysNBSendWait

set_option maxHeartbeats 16000000 in
theorem vi_fl4HandleSyscall (hG : ViGap) (rep : Bool) (c : Syscall) {σ0 σ : State Unit} (hW : W N S T σ0 σ)
    (hO : IO (fun _ => N) σ0) (hS : IrqOutV (fun _ => S) (uV σ0)) (hU : UtInv'' σ0)
    (hT : Pinned c → T = σ0.curThread) :
    ∀ y ∈ ((fl4HandleSyscall (Z := Unit) rep c).run σ).1, VI N S true y.2 := by
  intro y hy
  cases c
  case sysSend | sysNBSend | sysCall =>
    simp only [fl4HandleSyscall] at hy
    obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · exact vi_handleInvocationR hG _ _ _ _ _ _
        (w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hW z hz) hO hS hU
        (fun h1 h2 => by simp_all) y hy
    · exact vi_of_vit (w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hW z hz).1
  case sysReplyRecv | sysNBSendRecv | sysNBSendWait =>
    have hT' := hT (by simp [Pinned])
    simp only [fl4HandleSyscall] at hy
    obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' := w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hW z hz
      obtain ⟨z2, hz2, ⟨a2, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · have h2 := vi_handleInvocationR hG _ _ _ _ _ _ hz' hO hS hU (fun _ _ => hT') z2 hz2
        exact (show IKE (VI N S true) (withoutPreemption (Z := Unit) (handleRecv true _)) by vi_auto) _ h2 y hy
      · exact vi_handleInvocationR hG _ _ _ _ _ _ hz' hO hS hU (fun _ _ => hT') z2 hz2
    · exact vi_of_vit (w_step (by vi_auto) (fun _ => by uk_auto) (fun _ => by ct_auto) hW z hz).1
  all_goals
    simp only [fl4HandleSyscall] at hy
    exact (show IKE (VI N S true) _ by vi_auto) σ (vi_of_vit hW.1) y hy

/-! ## Events -/

theorem vi_cbTrue {σ : State Unit} {y : Bool × State Unit} (hy : y ∈ (checkBudget (Z := Unit) σ).1)
    (hr : y.1 = true) : y.2 = σ := by
  unfold checkBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets_vi h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets_vi h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have e3 : y3.2 = σ := (show IK (fun s => s = σ) (getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime) by
    repeat' (first | ik_step0 | ik_unfold)) σ rfl y3 h3
  (try dsimp only at hy)
  split at hy
  · obtain ⟨y4, h4, hy⟩ := hy
    rw [mem_gets_vi h4] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact e3
  · obtain ⟨y4, h4, hy⟩ := hy
    obtain ⟨y5, h5, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy] at hr
    cases hr

theorem vi_cbrTrue {σ : State Unit} {y : Bool × State Unit}
    (hy : y ∈ (checkBudgetRestart (Z := Unit) σ).1) (hr : y.1 = true) : y.2 = σ := by
  unfold checkBudgetRestart at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets_vi h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h3
  obtain ⟨y4, h4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy] at hr ⊢
  have hr' : y1.1 = true := hr
  have e1 := vi_cbTrue h1 hr'
  unfold NonDet.when at h4
  rw [if_neg (by simp [hr'])] at h4
  rw [Set.mem_singleton_iff.1 h4]; exact e1

set_option maxHeartbeats 8000000 in
theorem vi_fl4HandleEvent_sys (hG : ViGap) (rep : Bool) (c : Syscall) {σ0 σ : State Unit} (hW : W N S T σ0 σ)
    (hO : IO (fun _ => N) σ0) (hS : IrqOutV (fun _ => S) (uV σ0)) (hU : UtInv'' σ0)
    (hT : Pinned c → T = σ0.curThread) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1, VI N S true y.2 := by
  intro y hy
  simp only [fl4HandleEvent] at hy
  obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  swap
  · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
    exact vi_of_vit (w_stepN (by vi_auto) (fun _ => uk_updateTimeStamp) (fun _ => ct_updateTimeStamp) hW x hx).1
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
  have hWx := w_stepN (by vi_auto) (fun _ => uk_updateTimeStamp) (fun _ => ct_updateTimeStamp) hW x hx
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
  · obtain ⟨x2, hx2, rfl⟩ := mem_liftE' hz
    simp only [Except.ok.injEq] at hr; subst hr
    unfold NonDetE.whenE at hy
    by_cases hb : x2.1 = true
    · rw [if_pos hb] at hy
      have e2 : x2.2 = x.2 := vi_cbrTrue hx2 hb
      exact vi_fl4HandleSyscall hG rep c (e2 ▸ hWx) hO hS hU hT y hy
    · rw [if_neg hb] at hy
      rw [Set.mem_singleton_iff.1 hy]
      exact vi_checkBudgetRestart x.2 (vi_of_vit hWx.1) x2 hx2
  · obtain ⟨x2, hx2, rfl⟩ := mem_liftE' hz; cases he

set_option maxHeartbeats 8000000 in
/-- The other events: the fault events act on the current thread (active, so not idle). -/
theorem vi_handleEvent_fault (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) (hi : ev ≠ .interrupt) :
    IKE (VI N S true) (handleEvent (Z := Unit) ev) := by
  cases ev
  case syscallEvent c => exact absurd rfl (h c)
  case interrupt => exact absurd rfl hi
  all_goals simp only [handleEvent]; vi_auto

theorem vi_handleEvent_irq {b : Bool} : IKE (VI N S b) (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent]; vi_auto

theorem vi_afterEvent :
    IK (VI N S false) (do fl4Awaken (Z := Unit); schedule; activateThread) := by
  vi_auto

theorem vit_false {b : Bool} {σ : State Unit} (h : VIT N S T b σ) : VIT N S T false σ := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, h6⟩
  intro e; exact absurd e (by decide)

/-- `fl4CallKernel` from the event's post (`VI N S b`) on, with the preemption path. -/
theorem vi_callKernel_of {b : Bool} (rep : Bool) (ev : Event) {σ : State Unit}
    (hE : ∀ z ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, VI N S b z.2) (hσ : VI N S b σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, VI N S false y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz1 : VI N S b z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw' := hE w hw
    obtain ⟨r, s⟩ := w
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 hz]; exact hw'
    | error e => exact (show IKE (VI N S b) (withoutPreemption (Z := Unit) preemptionPath) by vi_auto) s hw' z hz
  exact vi_afterEvent z.2 (vit_false hz1) y hy

/-! ## The tops -/

/-- The current thread is bound to an SC [J] (module docstring). -/
def CtSc (σ : State Unit) : Prop := ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbSchedContext ≠ none

/-- No cap covers the idle SC (carried by sg1's family at `M := fun _ => idleSc`). -/
def IdleScOutV (σ : State Unit) : Prop := IrqOutV (fun _ => σ.idleSc) (uV σ)

theorem vi_true_of_active {b : Bool} {σ : State Unit} (hV : VI N S b σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) : VI N S true σ := by
  refine vit_true hV ?_
  intro e
  obtain ⟨x, hx⟩ := hV.2.2.2.1
  have hst := ((vi_obj hV hx).1 rfl).1
  rw [← e] at hx
  have h := ha x hx
  rw [hst] at h
  simp [activeSt] at h

theorem validIdle_of {σ y : State Unit} (h : VI σ.idleThread σ.idleSc false y) : ValidIdle y := by
  unfold ValidIdle
  rw [h.1, h.2.1]; exact h

/-- The syscall event from `σ0`'s facts, at any state `W`-related to `σ0`. -/
theorem vi_kcall_sys (hG : ViGap) (rep : Bool) (c : Syscall) {σ0 σ : State Unit}
    (hW : W N S T σ0 σ) (hO : IO (fun _ => N) σ0) (hS : IrqOutV (fun _ => S) (uV σ0)) (hU : UtInv'' σ0)
    (hT : Pinned c → T = σ0.curThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep (.syscallEvent c)) σ).1, VI N S false y.2 :=
  vi_callKernel_of rep _ (vi_fl4HandleEvent_sys hG rep c hW hO hS hU hT) (vi_of_vit hW.1)

/-- **valid_idle across the syscall entry**, given the remaining obligation `ViGap`. -/
theorem kentry_validIdle_of (hG : ViGap) (c : Syscall) {σ : State Unit} (hV : ValidIdle σ)
    (hS : SInvG.SpecGlobS σ ∧ SInvG.IdleOutV σ) (hI : IdleScOutV σ) (hU : UtInv3 σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) (hct : Pinned c → CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ValidIdle y.2 ∧ IdleScOutV y.2 := by
  intro y hy
  have hV1 : VI σ.idleThread σ.idleSc true σ := vi_true_of_active hV ha
  have hVI : VI σ.idleThread σ.idleSc false y.2 := by
    have hy' := hy
    unfold fl4KernelEntrySyscall at hy'
    obtain ⟨z, hz, hy'⟩ := hy'
    rw [mem_gets_vi hz] at hy'
    obtain ⟨w, hw, hy'⟩ := hy'
    by_cases hp : Pinned c
    · have hW0 : W σ.idleThread σ.idleSc σ.curThread σ σ := ⟨vit_of_vi hV1 (hct hp), rfl, rfl⟩
      have hWw := w_stepN (by unfold fl4SyscallFaultIP; exact vi_asUser _ _)
        (fun _ => uk_fl4SyscallFaultIP _) (fun _ => ct_fl4SyscallFaultIP _) hW0 w hw
      exact vi_kcall_sys hG true c hWw hS.2 hI hU.1 (fun _ => rfl) y hy'
    · have hW0 : W σ.idleThread σ.idleSc σ.idleThread σ σ := ⟨hV1, rfl, rfl⟩
      have hWw := w_stepN (by unfold fl4SyscallFaultIP; exact vi_asUser _ _)
        (fun _ => uk_fl4SyscallFaultIP _) (fun _ => ct_fl4SyscallFaultIP _) hW0 w hw
      exact vi_kcall_sys hG true c hWw hS.2 hI hU.1 (fun h => absurd h hp) y hy'
  refine ⟨validIdle_of hVI, ?_⟩
  have hSG := SInvG.sgN_kentry c σ.interruptIrqNode (fun _ => σ.idleSc) σ
    ⟨hU, hI, fun irq a ha => hS.1.irq irq a ha⟩ rfl y hy
  unfold IdleScOutV; rw [hVI.2.1]; exact hSG.2.1

/-- **valid_idle across every kernel event**, given `ViGap`. -/
theorem kcall_validIdle_of (hG : ViGap) (rep : Bool) (ev : Event) {σ : State Unit} (hV : ValidIdle σ)
    (hS : SInvG.SpecGlobS σ ∧ SInvG.IdleOutV σ) (hI : IdleScOutV σ) (hU : UtInv3 σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hct : ∀ c, ev = .syscallEvent c → Pinned c → CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ValidIdle y.2 ∧ IdleScOutV y.2 := by
  intro y hy
  have hVI : VI σ.idleThread σ.idleSc false y.2 := by
    by_cases hi : ev = .interrupt
    · subst hi
      refine vi_callKernel_of rep _ ?_ hV y hy
      rw [fl4HandleEvent_other rep _ fun c e => by cases e]
      exact vi_handleEvent_irq σ hV
    · have hV1 : VI σ.idleThread σ.idleSc true σ :=
        vi_true_of_active hV fun x hx => (ha x hx).resolve_right hi
      by_cases hs : ∃ c, ev = .syscallEvent c
      · obtain ⟨c, rfl⟩ := hs
        by_cases hp : Pinned c
        · exact vi_kcall_sys hG rep c (T := σ.curThread) ⟨vit_of_vi hV1 (hct c rfl hp), rfl, rfl⟩ hS.2 hI hU.1
            (fun _ => rfl) y hy
        · exact vi_kcall_sys hG rep c (T := σ.idleThread) ⟨hV1, rfl, rfl⟩ hS.2 hI hU.1 (fun h => absurd h hp) y hy
      · refine vi_callKernel_of rep _ ?_ hV1 y hy
        rw [fl4HandleEvent_other rep _ fun c e => hs ⟨c, e⟩]
        exact vi_handleEvent_fault ev (fun c e => hs ⟨c, e⟩) hi σ hV1
  refine ⟨validIdle_of hVI, ?_⟩
  have hSG := SInvG.sgN_fl4CallKernel rep ev σ.interruptIrqNode (fun _ => σ.idleSc) σ
    ⟨hU, hI, fun irq a ha => hS.1.irq irq a ha⟩ rfl y hy
  unfold IdleScOutV; rw [hVI.2.1]; exact hSG.2.1

end

end Fl4Proofs.P3.SInvI
