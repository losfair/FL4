/-
P3 (DESIGN.md §9), invariant line G1 (rd8i): **`Sched.BlockedScActive`
across the fault and budget paths** (spec side only, outside the JAtZ cone).

* `Bd t σ` (`t` a bound TCB), `ta_of_fwd` (`TA t` from sb2's `ScFwd` and
  `CBa t`), `cba_of_actB`; frames `cba_threadSet`, `bd_threadSet` (a TCB write
  keeping the bound SC).
* **`ba_sendFaultIpc_p`** (`TA`, and `CBa` / bound when it may donate),
  **`ba_handleFault_p thread ex σ (hT : TA thread σ) (hC : CBa thread σ)`**
  (the donation flag is `thread`'s binding, read in place),
  **`ba_handleTimeout_p`** (`TA` only: no donation).
* **`ba_endTimeslice_p`** (`TA` of the current thread),
  **`ba_chargeBudget_p consumed canTimeout σ (hI : ScInv σ)`** (the timeout
  is raised only for a `schedulable` current thread, bound to an active SC;
  `ScFwd` at that state, carried by sb2's family, makes it its only SC).
* **`ba_fl4Awaken`** (no hypothesis: FL4's timer loop only signals).
-/
import Fl4Proofs.P3.SpecInvRd8iB
open Classical

namespace Fl4Proofs.P3.SInvR.B8i
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g

noncomputable section

set_option maxHeartbeats 1000000

/-- `t` is a TCB bound to an SC. -/
def Bd (t : ObjRef) (σ : State Unit) : Prop :=
  ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c

theorem ta_of_fwd {s : State Unit} {t : ObjRef} (hF : SInvB.ScFwd s) (hC : CBa t s) : TA t s := by
  intro q y n hq hy
  obtain ⟨x, hx, hxs⟩ := hF q y n t hq hy
  obtain ⟨y', n', hk, ha⟩ := hC x q hx hxs
  rw [hq] at hk; cases hk; exact ha

theorem cba_of_actB {s : State Unit} {t : ObjRef} (h : ActB s t) : CBa t s := by
  obtain ⟨x, c, y, n, hx, hc, hk, ha⟩ := h
  intro x' c' hx' hc'
  rw [hx] at hx'; cases hx'; rw [hc] at hc'; cases hc'
  exact ⟨y, n, hk, ha⟩

theorem cba_threadSet (t u : ObjRef) (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) :
    IK (CBa t) (threadSet (Z := Unit) f u) := by
  intro σ hσ y hy
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hy
  rw [e]
  have pa_up : ∀ c, PA c σ → PA c { σ with kheap := Function.update σ.kheap u (some (.tcb (f x0))) } := by
    intro c ⟨y, n, hk, ha⟩
    refine ⟨y, n, ?_, ha⟩
    change Function.update σ.kheap u _ c = _
    rw [Function.update_of_ne (fun h => by rw [h, hx0] at hk; cases hk)]; exact hk
  intro x c hx hc
  change Function.update σ.kheap u _ t = _ at hx
  by_cases et : t = u
  · subst et; rw [Function.update_self] at hx; cases hx
    exact pa_up c (hσ x0 c hx0 (by rw [← hf x0]; exact hc))
  · rw [Function.update_of_ne et] at hx; exact pa_up c (hσ x c hx hc)

theorem bd_threadSet (t u : ObjRef) (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) :
    IK (Bd t) (threadSet (Z := Unit) f u) := by
  intro σ hσ y hy
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hy
  rw [e]
  obtain ⟨x, c, hx, hc⟩ := hσ
  by_cases et : t = u
  · subst et; rw [hx0] at hx; cases hx
    refine ⟨f x0, c, ?_, by rw [hf]; exact hc⟩
    change Function.update σ.kheap t _ t = _; exact Function.update_self _ _ _
  · refine ⟨x, c, ?_, hc⟩
    change Function.update σ.kheap u _ t = _; rw [Function.update_of_ne et]; exact hx

/-! ## Fault messages -/

/-- **`send_fault_ipc tptr cap ex cd`**: `tptr`'s SCs active; its own SC active and bound when it may donate. -/
theorem ba_sendFaultIpc_p (tptr : ObjRef) (cap : Cap) (ex : Fault) (cd : Bool) (σ : State Unit)
    (hT : TA tptr σ) (hC : cd = true → CBa tptr σ) (hD : cd = true → Bd tptr σ) :
    IKp BSA σ (sendFaultIpc (Z := Unit) tptr cap ex cd) := by
  unfold sendFaultIpc
  split
  · refine ikp_bind_q (Q := fun s => TA tptr s ∧ (cd = true → CBa tptr s) ∧ (cd = true → Bd tptr s))
      (ikp_of_ik (ba_threadSet (fun tcb => { tcb with tcbFault := some ex }) tptr (fun _ => rfl)) σ)
      (fun y hy => ⟨ta_threadSet _ _ _ σ hT y hy,
        fun h => cba_threadSet _ _ (fun tcb => { tcb with tcbFault := some ex }) (fun _ => rfl) σ (hC h) y hy,
        fun h => bd_threadSet _ _ (fun tcb => { tcb with tcbFault := some ex }) (fun _ => rfl) σ (hD h) y hy⟩)
      fun _ s hq => ?_
    exact ikp_bind (ba_sendIpc_p _ _ _ _ _ _ _ _ s hq.1 hq.2.1 (fun _ hcd => hq.2.2 hcd)) fun _ => ik_pure _
  · exact ikp_of_ik (ik_pure _) σ
  · exact ikp_of_ik ik_fail σ

/-- **`handle_fault thread ex`**: `thread`'s SCs active, its own SC active. -/
theorem ba_handleFault_p (thread : ObjRef) (ex : Fault) (σ : State Unit) (hT : TA thread σ) (hC : CBa thread σ) :
    IKp BSA σ (handleFault (Z := Unit) thread ex) := by
  unfold handleFault
  refine ikp_pure_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun cap => ?_
  intro hσ y hy
  obtain ⟨⟨so, s1⟩, h1, hy⟩ := hy
  obtain ⟨x1, hx1, e1⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbSchedContext) h1
  simp only [Prod.mk.injEq] at e1; obtain ⟨rfl, e1⟩ := e1; subst s1
  obtain ⟨z2, h2, hy⟩ := hy
  have b2 := ba_sendFaultIpc_p thread cap ex _ σ hT (fun _ => hC) (fun hd => by
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (of_decide_eq_true hd)
    exact ⟨x1, c, hx1, hc⟩) hσ z2 h2
  exact (by (try dsimp only); ba_auto : BAK _) z2.2 b2 y hy

/-- **`handle_timeout tptr ex`**: `tptr`'s SCs active (no donation). -/
theorem ba_handleTimeout_p (tptr : ObjRef) (ex : Fault) (σ : State Unit) (hT : TA tptr σ) :
    IKp BSA σ (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun _ => ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun _ => ?_
  refine ikp_pure_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun cap => ?_
  exact ikp_bind (ba_sendFaultIpc_p _ _ _ false σ hT (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))) fun _ => ik_pure _

/-! ## The budget path -/

/-- **`end_timeslice`**: the current thread's SCs active. -/
theorem ba_endTimeslice_p (canTimeout : Bool) (σ : State Unit) (hT : TA σ.curThread σ) :
    IKp BSA σ (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice
  refine ikp_gets_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun robin => ?_
  refine ikp_gets_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun ts => ?_
  (try dsimp only)
  split
  all_goals (refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun valid => ?_)
  all_goals (try dsimp only)
  all_goals split
  all_goals first
    | (refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun sc => ?_
       exact ba_handleTimeout_p _ _ σ hT)
    | exact ikp_of_ik (by ba_auto) σ

/-- **`charge_budget`** (sb2's `ScInv` at its start). -/
theorem ba_chargeBudget_p (consumed : Ticks) (canTimeout : Bool) (σ : State Unit) (hI : SInvB.ScInv σ) :
    IKp BSA σ (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget
  refine ikp_gets_bind ?_
  refine ikp_gets_bind ?_
  refine ikp_bind_q (Q := SInvB.ScInv) (ikp_of_ik (by ba_auto) σ)
    (fun y hy => (SInvB.sik_of_sbk (fun _ => by sb_auto)) σ hI y hy) fun _ s hq => ?_
  refine ikp_bind_q (Q := SInvB.ScInv) (ikp_of_ik (by ba_auto) s)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hq) fun _ s hq => ?_
  refine ikp_gets_bind ?_
  refine ikp_gets_bind ?_
  unfold NonDet.when
  split
  · rename_i hs
    obtain ⟨x, scp, y, n, hx, hc, -, hk, ha, -⟩ := Sched.schedulable_inv hs
    have hT : TA s.curThread s := ta_of_fwd hq.fwd (cba_of_actB ⟨x, scp, y, n, hx, hc, hk, ha⟩)
    exact ikp_bind (ba_endTimeslice_p canTimeout s hT) fun _ => by ba_auto
  · exact ikp_of_ik (ik_pure _) s

/-! ## The TCB timer loop -/

/-- **FL4's timer step** (`fl4TimerFires`: signals only, by `ba_sendSignal`). -/
theorem ba_fl4Awaken : BAK (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, σ'⟩ := x
  have h : fl4TimerFires σ σ' := hx
  clear hx
  induction h with
  | refl => exact hσ
  | tail _ hstep ih =>
    obtain ⟨σ1, h1 | ⟨n, bd, hs⟩, rfl⟩ := hstep
    · subst h1; exact bsa_kh ih rfl
    · have := ba_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
      exact bsa_kh this rfl

end

end Fl4Proofs.P3.SInvR.B8i
