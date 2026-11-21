/-
P3 (DESIGN.md §9), invariant line G1 (rd8b): **`Rdy` across the SC bind and
every SchedContext invocation** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd7 handoff 2).

* `rdy_upd_bind'`: rd7's `rdy_upd_bind` for a thread that may be `BlkR`, when
  its new SC is released (active, head ready): `R3` then holds for it.
* `BindRel σ p t` (the decode's facts at the perform; `decode_sched_context_bind`
  and `decode_update_sc` check `sc_tcb = None`, `tcb_sched_context = None` and
  throw on `ipc_queued_thread_state st ∧ ¬ sc_released` — seL4's
  "tcb blocked and scheduling context not schedulable"): the SC is bound to no
  TCB, the TCB to no SC, and when blocked the SC is released.
* **`rd_schedContextBindTcb`**: from `BindRel`: the bind (`rdy_upd_bind'`; the
  thread is in no ready queue, not the switch target, not released, all three
  needing an SC: rd7's `free_of_rdy`), the back-pointer (`rd_updateSchedContext`),
  the unblock check (rd6's `rd_ifCond`; the mutual binding kept by sb2's
  `sb_ifCondRefillUnblockCheck`), `sched_context_resume` (rd7's
  `sr_schedContextResume`: afterwards the thread, when schedulable, is
  released), the enqueue under `schedulable`.
* **`rd_invokeSchedContext`** (`T1`, `Simple` — ctq's facts at a perform —,
  `ScFwd`, the current thread `RdyT`, `BindRel` for a TCB bind): every arm.
-/
import Fl4Proofs.P3.SpecInvRd8bA
import Fl4Proofs.P3.SpecInvSbF2
open Classical

namespace Fl4Proofs.P3.SInvR.B8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

/-! ## Binding a possibly blocked thread to a released SC -/

theorem rdy_upd_bind' {σ : State Unit} (h : Rdy σ) (p : ObjRef) (x y : Tcb) (hx : σ.kheap p = some (.tcb x))
    (hblk : BlkR y.tcbState y.tcbFault → ∀ c, y.tcbSchedContext = some c →
      ∃ z m, σ.kheap c = some (.schedContext z m) ∧ scActive z = true ∧ refillReady σ.curTime (refillHd z) = true)
    (hq : ∀ d q, p ∉ σ.readyQueues d q) (ha : σ.schedulerAction ≠ .switchThread p) (hr : p ∉ σ.releaseQueue) :
    Rdy { σ with kheap := Function.update σ.kheap p (some (.tcb y)) } := by
  set σ' : State Unit := { σ with kheap := Function.update σ.kheap p (some (.tcb y)) }
  have hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', hq]
  have hp : σ'.kheap p = some (.tcb y) := by simp [σ']
  have F : ∀ {t}, t ≠ p → RdyT σ t → RdyT σ' t := by
    intro t htp ⟨x0, c, y0, n, hx0, hc, hy0, h1, h2⟩
    have hcp : c ≠ p := by rintro rfl; rw [hx] at hy0; cases hy0
    exact ⟨x0, c, y0, n, by rw [hk t htp]; exact hx0, hc, by rw [hk c hcp]; exact hy0, h1, h2⟩
  have G : ∀ {t}, t ≠ p → ActB σ t → ActB σ' t := by
    intro t htp ⟨x0, c, y0, n, hx0, hc, hy0, h1⟩
    have hcp : c ≠ p := by rintro rfl; rw [hx] at hy0; cases hy0
    exact ⟨x0, c, y0, n, by rw [hk t htp]; exact hx0, hc, by rw [hk c hcp]; exact hy0, h1⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun d q t hm => F (fun e => hq d q (e ▸ hm)) (h1 d q t hm),
    fun t e => F (fun e' => ha (e' ▸ e)) (h2 t e), fun t x' c hx' hb hc => ?_, fun q z n hz hz' => ?_,
    fun t hm => G (fun e => hr (e ▸ hm)) (h5 t hm), fun z m hz => ?_⟩
  rotate_right
  · have e : σ.idleSc ≠ p := by rintro e; rw [← e] at hp; change σ'.kheap σ.idleSc = _ at hz; rw [hp] at hz; cases hz
    change σ'.kheap σ.idleSc = _ at hz; rw [hk _ e] at hz; exact h6 z m hz
  · by_cases e : t = p
    · subst e; rw [hp] at hx'; cases hx'
      obtain ⟨z, m, hz, ha', hrd⟩ := hblk hb c hc
      have hcp : c ≠ t := by rintro rfl; rw [hx] at hz; cases hz
      exact ⟨y, c, z, m, hp, hc, by rw [hk c hcp]; exact hz, ha', hrd⟩
    · rw [hk t e] at hx'; exact F e (h3 t x' c hx' hb hc)
  · by_cases e : q = p
    · subst e; rw [hp] at hz; cases hz
    · rw [hk q e] at hz; exact h4 q z n hz hz'

/-! ## `sched_context_bind_tcb` -/

/-- The decode's facts of an SC-to-TCB bind, at the perform. -/
def BindRel (σ : State Unit) (p t : ObjRef) : Prop :=
  (∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = none) ∧
  ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext = none ∧
    (BlkR x.tcbState x.tcbFault → ∃ y n, σ.kheap p = some (.schedContext y n) ∧ scReleased σ.curTime y = true)

/-- **`sched_context_bind_tcb p t`** keeps `Rdy` under the decode's facts. -/
theorem rd_schedContextBindTcb (p t : ObjRef) (σ : State Unit) (hB : BindRel σ p t) :
    IKp Rdy σ (schedContextBindTcb (Z := Unit) p t) := by
  unfold schedContextBindTcb
  intro hσ r hr
  obtain ⟨w1, hw1, hr⟩ := hr
  obtain ⟨x, hx, e1⟩ := SInv.mem_threadSet hw1
  obtain ⟨hn, hrel⟩ := hB.2 x hx
  obtain ⟨hq, ha, hrq⟩ := free_of_rdy hσ hx hn
  have hR1 : Rdy w1.2 := by
    rw [e1]
    refine rdy_upd_bind' hσ t x _ hx (fun hb c hc => ?_) hq ha hrq
    obtain ⟨y, n, hk, hrl⟩ := hrel hb
    cases hc
    unfold scReleased at hrl
    rw [Bool.and_eq_true] at hrl
    exact ⟨y, n, hk, hrl.1, hrl.2⟩
  have hx1 : w1.2.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => some p) x)) := by rw [e1]; simp
  obtain ⟨w2, hw2, hr⟩ := hr
  have hR2 := rd_updateSchedContext p (scTcbUpdate fun _ => some t) (fun _ => ⟨rfl, rfl, rfl⟩) w1.2 hR1 w2 hw2
  obtain ⟨y2, n2, hk2, e2⟩ := SInvB.mem_updateSchedContext hw2
  have hpt : p ≠ t := fun e => by rw [e, hx1] at hk2; cases hk2
  have hx2 : w2.2.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => some p) x)) := by
    rw [e2]; simp [Function.update_of_ne (Ne.symm hpt), hx1]
  have hk2' : w2.2.kheap p = some (.schedContext (scTcbUpdate (fun _ => some t) y2) n2) := by rw [e2]; simp
  obtain ⟨w3, hw3, hr⟩ := hr
  have hR3 : Rdy w3.2 := (rd_ifCond (some p) (some true) (some false) w2.2 hR2 hw3).1
  have hBR : SInvB.BR w2.2.kheap w3.2.kheap :=
    SInvB.sb_ifCondRefillUnblockCheck (h0 := w2.2.kheap) (some p) (some true) (some false) w2.2 (SInvB.BR.refl _) w3 hw3
  have hp3 : ∀ y n, w3.2.kheap p = some (.schedContext y n) → y.scTcb = some t := by
    intro y n hy
    obtain ⟨y', n', hy', hkp⟩ := hBR.sc p _ _ hk2'
    rw [hy] at hy'; cases hy'
    exact hkp.1
  have hb3 : ∀ x', w3.2.kheap t = some (.tcb x') → x'.tcbSchedContext = some p := by
    intro x' hx'
    obtain ⟨x'', hx'', hb⟩ := hBR.tcb t _ hx2
    rw [hx'] at hx''; cases hx''
    exact hb
  obtain ⟨w4, hw4, hr⟩ := hr
  have hR4 := rd_schedContextResume p w3.2 hR3 w4 hw4
  have hSR : SR t w4.2 := sr_schedContextResume p t w3.2 hp3 hb3 hw4
  obtain ⟨w5, hw5, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hw5
  dsimp only at hr
  unfold NonDet.when at hr
  split_ifs at hr with hs
  · obtain ⟨w6, hw6, hr⟩ := hr
    have hR6 := rd_tsa_p _ t w4.2 (fun q u hu => (SInvQ.q1_enq t q u hu).imp id fun e => ⟨e, hSR hs⟩) hR4 w6 hw6
    exact rd_rescheduleRequired w6.2 hR6 r hr
  · obtain rfl : r = ((), w4.2) := hr
    exact hR4

/-! ## `invoke_sched_context` -/

/-- The per-arm decode facts of a SchedContext invocation, at the perform. -/
def ScIvOK (σ : State Unit) : SchedContextInvocation → Prop
  | .invokeSchedContextBind p (.threadCap t) => BindRel σ p t
  | _ => True

theorem ikp_bind_ret {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {b : β}
    (h : IKp Rdy σ m) : IKp Rdy σ (m >>= fun _ => (pure b : NonDet (State Unit) β)) := by
  intro hσ y ⟨z, hz, hy⟩
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact h hσ z hz

theorem ikp_failR {α : Type} {σ : State Unit} : IKp Rdy σ (NonDet.fail : NonDet (State Unit) α) := by
  intro _ y hy; exact hy.elim

/-- **`invoke_sched_context`** keeps `Rdy`. -/
theorem rd_invokeSchedContext (iv : SchedContextInvocation) (σ : State Unit) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ) (hct : RdyT σ σ.curThread) (hD : ScIvOK σ iv) :
    IKp Rdy σ (invokeSchedContext (Z := Unit) iv) := by
  cases iv with
  | invokeSchedContextConsumed p => exact ikp_of_ik (rd_returnConsumed p) σ
  | invokeSchedContextBind p cap =>
    cases cap with
    | threadCap t => exact ikp_bind_ret (rd_schedContextBindTcb p t σ hD)
    | notificationCap n b r => exact ikp_bind_ret (ikp_of_ik (rd_schedContextBindNtfn p n) σ)
    | _ => exact ikp_failR
  | invokeSchedContextUnbindObject p cap =>
    cases cap with
    | threadCap t =>
      exact ikp_bind_ret (rd_schedContextUnbindTcb_p p σ h1 fun _ _ u _ _ _ => hA u)
    | notificationCap n b r => exact ikp_bind_ret (ikp_of_ik (rd_schedContextUnbindNtfn p) σ)
    | _ => exact ikp_failR
  | invokeSchedContextUnbind p =>
    dsimp only [invokeSchedContext]
    intro hσ y ⟨z1, hz1, hy⟩
    have hR1 := rd_schedContextUnbindAllTcbs_p p σ h1 (fun _ _ u _ _ _ => hA u) hσ z1 hz1
    obtain ⟨z2, hz2, hy⟩ := hy
    have hR2 := rd_schedContextUnbindNtfn p z1.2 hR1 z2 hz2
    obtain ⟨z3, hz3, hy⟩ := hy
    have hR3 := rd_schedContextUnbindReply p z2.2 hR2 z3 hz3
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hR3
  | invokeSchedContextYieldTo p => exact rd_schedContextYieldTo p σ hF hct

end

end Fl4Proofs.P3.SInvR.B8
