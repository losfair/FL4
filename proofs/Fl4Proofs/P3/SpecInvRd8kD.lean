/-
P3 (DESIGN.md §9), invariant line G1 (rd8k): **`Sched.BlockedScActive`
across the invocation performs** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd8i handoff 3).

* `ba_seqRet` / `ba_lift` (rd8h's `rd_seqRet` / `rd_lift` for `BSA`),
  **`kd_installTcbCap`**, **`kd_installTcbFrameCap`** (the deletion by
  `kd_capDelete`, rd8h's `io_install*`, sl's `isk_install*`).
* **`ba_invokeCnode`** (revoke / delete from `KD`), **`ba_invokeTcbK`**
  (every arm; ThreadControlSched with a new SC bound: the input `TcbB`,
  see KENTRY-PLAN rd8k), **`ba_invokeSchedContext`** (the bind from rd8k's
  decode fact `BQ`, rd8i's `ba_schedContextBindTcb_p`).
* **`ba_fl4PerformInvocation bl call don iv I σ (hK : KD I σ) (hI : ScInv σ)
  (hC : CBa ct σ) (hD : call = false → don → Bd ct σ) (hOK : PerfB σ iv)`**:
  Endpoint (rd8i's `ba_sendIpc_p`, `TA ct` = `ta_of_fwd ScFwd (CBa ct)`),
  Notification (`ba_sendSignal`), TCB, Reply (`ba_doReplyTransfer`), CNode,
  SchedContext, SchedControl (`ba_invokeSchedControlConfigureFlags`, rd8c's
  `CfgD`), Untyped / ASIDControl (SpecInvRd8kE), the rest by the generated
  family.
-/
import Fl4Proofs.P3.SpecInvRd8kC
import Fl4Proofs.P3.SpecInvRd8kE
import Fl4Proofs.P3.SpecInvRd8hP
open Classical

namespace Fl4Proofs.P3.SInvR.B8k
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i

noncomputable section

set_option maxHeartbeats 1000000

variable {I : ObjRef}

theorem ba_seqRet {ε α β : Type} {m : NonDetE (State Unit) ε α} {b : β} {σ : State Unit}
    (hm : ∀ y ∈ (m.run σ).1, BSA y.2) :
    ∀ y ∈ ((m >>= fun _ => (NonDetE.returnOk b : NonDetE (State Unit) ε β)).run σ).1, BSA y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · rw [SInvU.mem_ret_ok hy]; exact hm z hz
  · exact hm z hz

theorem ba_lift {ε α : Type} {m : NonDet (State Unit) α} {σ : State Unit} (hm : ∀ y ∈ (m σ).1, BSA y.2) :
    ∀ y ∈ ((NonDetE.liftE (ε := ε) m).run σ).1, BSA y.2 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
  exact hm x hx

/-! ## The installs -/

theorem kd_installTcbCap (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    IKE (KD I) (installTcbCap (Z := Unit) t sl n o) := by
  intro σ h y hy
  refine ⟨?_, B8h.io_installTcbCap _ t sl n o σ h.2.1 y hy, SInvL.isk_installTcbCap t sl n o σ h.2.2 y hy⟩
  unfold installTcbCap at hy
  rcases o with _ | ⟨nc, src⟩
  · rw [SInvU.mem_ret_ok hy]; exact h.1
  · try dsimp only at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' : BSA z.2 := (kd_capDelete (I := I) _ σ h z hz).1
      exact (ike_unlessE _ (ike_liftE (ba_checkCapAt _ _ _ (ba_checkCapAt _ _ _ (ba_capInsert _ _ _)))))
        z.2 hz' y hy
    · exact (kd_capDelete (I := I) _ σ h z hz).1

theorem kd_installTcbFrameCap (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (KD I) (installTcbFrameCap (Z := Unit) t sl b) := by
  intro σ h y hy
  refine ⟨?_, B8h.io_installTcbFrameCap _ t sl b σ h.2.1 y hy, SInvL.isk_installTcbFrameCap t sl b σ h.2.2 y hy⟩
  rcases b with _ | ⟨ptr, frame⟩
  · rw [SInvU.mem_ret_ok hy]; exact h.1
  · simp only [installTcbFrameCap] at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' : BSA z.2 := (kd_capDelete (I := I) _ σ h z hz).1
      refine (show IKE BSA _ from ?_) z.2 hz' y hy
      refine ike_bind (ike_liftE (ba_threadSet _ _ fun _ => rfl)) fun _ => ?_
      refine ike_bind (ike_liftE ?_) fun _ => ?_
      · rcases frame with _ | ⟨c, src⟩
        · exact ik_pure _
        · exact ba_checkCapAt _ _ _ (ba_checkCapAt _ _ _ (ba_capInsert _ _ _))
      · exact ike_bind (ike_liftE (ik_gets _)) fun _ => ike_liftE (by ba_auto)
    · exact (kd_capDelete (I := I) _ σ h z hz).1

/-! ## The performs -/

/-- **`invoke_cnode`** from `KD`. -/
theorem ba_invokeCnode (i : CnodeInvocation) (σ : State Unit) (h : KD I σ) :
    ∀ y ∈ ((invokeCnode (Z := Unit) i).run σ).1, BSA y.2 := by
  cases i with
  | revokeCall sl => exact fun y hy => (kd_capRevoke sl σ h y hy).1
  | deleteCall sl => exact fun y hy => (kd_capDelete sl σ h y hy).1
  | cancelBadgedSendsCall c =>
    cases c <;> (intro y hy; simp only [invokeCnode] at hy; exact (show IKE BSA _ by ba_auto) σ h.1 y hy)
  | _ => intro y hy; simp only [invokeCnode] at hy; exact (show IKE BSA _ by ba_auto) σ h.1 y hy

/-- The TCB perform's input: ThreadControlSched binding a new SC (handed off,
KENTRY-PLAN rd8k: needs a "no thread becomes ipc-queued" frame across the
slot-3 deletion). -/
def TcbB (σ : State Unit) : TcbInvocation → Prop
  | .threadControlSched t sl fh mcp prio (some (some c)) =>
    ∀ y ∈ ((invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio (some (some c)))).run σ).1, BSA y.2
  | _ => True

/-- ThreadControlSched without a new SC bound: the install by `kd_installTcbCap`,
the rest by the generated family. -/
theorem ba_tcSchedNB (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef))
    (sc : Option (Option ObjRef)) (hsc : ∀ c, sc ≠ some (some c)) (σ : State Unit) (h : KD I σ) :
    ∀ y ∈ ((invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio sc)).run σ).1, BSA y.2 := by
  intro y hy
  simp only [invokeTcb] at hy
  obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · have hz' : BSA z.2 := (kd_installTcbCap (I := I) _ _ _ _ σ h z hz).1
    rcases mcp with _ | ⟨m1, m2⟩ <;> rcases prio with _ | ⟨p1, p2⟩ <;> rcases sc with _ | (_ | c) <;>
      first | exact absurd rfl (hsc _) | exact (show IKE BSA _ by simp only [NonDet.maybeM]; ba_auto) z.2 hz' y hy
  · exact (kd_installTcbCap (I := I) _ _ _ _ σ h z hz).1

/-- **Every arm of `invoke_tcb`** from `KD` (and `TcbB`). -/
theorem ba_invokeTcbK (i : TcbInvocation) (σ : State Unit) (h : KD I σ) (hOK : TcbB σ i) :
    ∀ y ∈ ((invokeTcb (Z := Unit) i).run σ).1, BSA y.2 := by
  cases i with
  | threadControlCaps t sl fh th cr vr buf =>
    intro y hy
    simp only [invokeTcb] at hy
    exact ((ike_bind (kd_installTcbCap _ _ _ _) fun _ => ike_bind (kd_installTcbCap _ _ _ _) fun _ =>
      ike_bind (kd_installTcbCap _ _ _ _) fun _ => ike_bind (kd_installTcbCap _ _ _ _) fun _ =>
      ike_bind (kd_installTcbFrameCap _ _ _) fun _ => ike_returnOk _ : IKE (KD I) _) σ h y hy).1
  | threadControlSched t sl fh mcp prio sc =>
    cases sc with
    | none => exact ba_tcSchedNB t sl fh mcp prio none (fun _ e => by cases e) σ h
    | some s =>
      cases s with
      | none => exact ba_tcSchedNB t sl fh mcp prio (some none) (fun _ e => by cases e) σ h
      | some c => exact hOK
  | notificationControl t n =>
    cases n <;> (intro y hy; simp only [invokeTcb] at hy; exact (show IKE BSA _ by ba_auto) σ h.1 y hy)
  | _ => intro y hy; simp only [invokeTcb] at hy; exact (show IKE BSA _ by ba_auto) σ h.1 y hy

/-- **`invoke_sched_context`**: the bind from `BQ`. -/
theorem ba_invokeSchedContext (i : SchedContextInvocation) (σ : State Unit) (hOK : RqS σ i) :
    IKp BSA σ (invokeSchedContext (Z := Unit) i) := by
  cases i with
  | invokeSchedContextBind p cap =>
    cases cap
    case threadCap t =>
      simp only [invokeSchedContext]
      exact ikp_bind (ba_schedContextBindTcb_p p t σ (nqpa_of_bq hOK)) fun _ => ik_pure _
    all_goals exact ikp_of_ik (by simp only [invokeSchedContext]; ba_auto) σ
  | invokeSchedContextUnbindObject p cap =>
    cases cap <;> exact ikp_of_ik (by simp only [invokeSchedContext]; ba_auto) σ
  | _ => exact ikp_of_ik (by simp only [invokeSchedContext]; ba_auto) σ

/-- **Every arch perform** (ASIDControl's MakePool by rd8k's
`ba_performAsidControlInvocation`). -/
theorem ba_archPerf (i : Fl4ArchInvocation) (σ : State Unit) (hb : BSA σ) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) i).run σ).1, BSA y.2 := by
  intro y hy
  cases i with
  | spec j =>
    cases j <;>
    · simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
      exact (show IKE BSA _ from ike_liftE (by ba_auto)) σ hb y hy
  | _ =>
    simp only [fl4ArchPerformInvocation] at hy
    exact (show IKE BSA _ from ike_liftE (by ba_auto)) σ hb y hy

/-- The per-arm inputs of a perform (module docstring). -/
def PerfB (σ : State Unit) : Fl4Invocation → Prop
  | .invokeTCB i => TcbB σ i
  | .invokeSchedContext i => RqS σ i
  | .invokeSchedControl i => CfgD (.invokeSchedControl i)
  | _ => True

/-- **Every perform arm keeps `BlockedScActive`** (module docstring). -/
theorem ba_fl4PerformInvocation (bl call don : Bool) (iv : Fl4Invocation) (I : ObjRef) (σ : State Unit)
    (hK : KD I σ) (hI : SInvB.ScInv σ) (hC : CBa σ.curThread σ)
    (hD : call = false → don = true → Bd σ.curThread σ) (hOK : PerfB σ iv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don iv).run σ).1, BSA y.2 := by
  have hb : BSA σ := hK.1
  cases iv with
  | invokeUntyped i => simp only [fl4PerformInvocation]; exact ba_seqRet (ba_fl4InvokeUntyped i σ hb)
  | invokeEndpoint ep badge cg cgr =>
    intro y hy
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain ⟨w2, hw2, hx⟩ := hx
    have r2 := ba_sendIpc_p bl call badge cg cgr don σ.curThread ep σ (ta_of_fwd hI.fwd hC)
      (fun _ => hC) hD hb w2 hw2
    rw [Set.mem_singleton_iff.1 hx]; exact r2
  | invokeNotification ep badge =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact ba_seqRet (ba_lift (ba_sendSignal ep badge σ hb))
  | invokeTCB i => simp only [fl4PerformInvocation]; exact ba_invokeTcbK i σ hK hOK
  | invokeReply reply grant =>
    simp only [fl4PerformInvocation]
    refine ba_lift fun x hx => ?_
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain ⟨w2, hw2, hx⟩ := hx
    have r2 := ba_doReplyTransfer _ reply grant σ hI hb w2 hw2
    rw [Set.mem_singleton_iff.1 hx]; exact r2
  | invokeCNode i => simp only [fl4PerformInvocation]; exact ba_seqRet (ba_invokeCnode i σ hK)
  | invokeSchedContext i =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact ba_lift (ba_invokeSchedContext i σ hOK hb)
  | invokeSchedControl i =>
    simp only [fl4PerformInvocation]
    exact ba_seqRet (ba_lift (ba_invokeSchedControlConfigureFlags i hOK σ hb))
  | invokeArchObject i => simp only [fl4PerformInvocation]; exact ba_archPerf i σ hb
  | _ => intro y hy; simp only [fl4PerformInvocation] at hy; exact (show IKE BSA _ by ba_auto) σ hb y hy

end

end Fl4Proofs.P3.SInvR.B8k
