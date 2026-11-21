/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctq5): **SchedQ across
FL4's timer step and the kernel exit** (spec side only, outside the JAtZ
cone; KENTRY-PLAN ctq4 handoff 1).

* `sa_tcbReleaseEnqueue_p` / `sa_postpone_p`: a release enqueue of a thread
  that is a runnable TCB at that state keeps RR; `sa_schedContextResume`
  (the bound thread is read runnable at the same state as `postpone`),
  `sa_maybeDonateSc`, `sa_completeSignal`.
* `sa_cancelIpc` (one lemma per arm: a thread read blocked is neither the
  switch target nor released, `NP`, kept by every write of the arm up to its
  `set_thread_state t Inactive`: `SAU`).
* `SQ4 σ := SchedQ σ ∧ T4 σ`; `possible_switch_to` of a thread whose
  `schedulable` was just read: runnable, and of `cur_domain` by T4
  (`sq4_pst`). **`sq4_sendSignal`**, **`sq4_fl4Awaken`**.
* **`sq_tail : HK1 (SQ4 ∧ ValidIdle) SchedQ (fl4Awaken; schedule;
  activate_thread)`** (vi2's `vi_fl4Awaken` keeps ValidIdle, so `aw_of`
  applies at `schedule`'s entry).
-/
import Fl4Proofs.P3.SpecInvCqL
import Fl4Proofs.P3.SpecInvQDomF5
import Fl4Proofs.P3.SpecInvViF
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Reads -/

/-- A step keeping every state (`IK` of the equality). -/
theorem cq5_ro {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ0 : State Unit, IK (fun s => s = σ0) m)
    {σ : State Unit} {y : α × State Unit} (hy : y ∈ (m σ).1) : y.2 = σ :=
  h σ σ rfl y hy

theorem cq5_mem_assertOpt {α : Type} {o : Option α} {σ : State Unit} {y : α × State Unit}
    (hy : y ∈ (NonDet.assertOpt o σ).1) : o = some y.1 ∧ y.2 = σ := by
  cases o with
  | none => exact hy.elim
  | some a => rw [Set.mem_singleton_iff.1 hy]; exact ⟨rfl, rfl⟩

theorem cq5_mem_getSc {p : ObjRef} {σ : State Unit} {y : SchedContext × State Unit}
    (h : y ∈ (getSchedContext (Z := Unit) p σ).1) : y.2 = σ ∧ ∃ n, σ.kheap p = some (.schedContext y.1 n) := by
  unfold getSchedContext at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨o, z2⟩ := z
  simp only at hk hs; subst z2
  cases o with
  | schedContext sc n =>
    rw [Set.mem_singleton_iff.1 h]; exact ⟨rfl, n, hk⟩
  | _ => exact h.elim

theorem cq5_mem_getScObjRef {f : SchedContext → Option ObjRef} {p : ObjRef} {σ : State Unit}
    {y : Option ObjRef × State Unit} (h : y ∈ (getScObjRef (Z := Unit) f p σ).1) :
    y.2 = σ ∧ ∃ sc n, σ.kheap p = some (.schedContext sc n) ∧ y.1 = f sc := by
  unfold getScObjRef at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz
  rw [Set.mem_singleton_iff.1 h]
  exact ⟨e, z.1, n, hk, rfl⟩

/-- `ordered_insert` reads only; its list is the old one with `t`. -/
theorem cq5_mem_orderedInsert {α β : Type} [Nonempty β] {t : α} {ts : List α} {f : α → RMonad Unit β}
    {R : β → β → Prop} {σ : State Unit} {y : List α × State Unit}
    (hy : y ∈ (orderedInsert (Z := Unit) t ts f R σ).1) : y.2 = σ ∧ ∀ u ∈ y.1, u = t ∨ u ∈ ts := by
  unfold orderedInsert at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  have e1 : y1.2 = σ := cq5_ro (fun _ => by repeat' ik_step0) hy1
  rw [e1] at hy
  obtain ⟨y2, hy2, hy⟩ := hy
  have e2 : y2.2 = σ := cq5_ro (fun _ => by repeat' ik_step0) hy2
  rw [e2] at hy
  obtain ⟨y3, hy3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy3] at hy
  obtain ⟨y4, hy4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy4] at hy
  rw [Set.mem_singleton_iff.1 hy]
  refine ⟨rfl, fun u hu => ?_⟩
  simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with (hu | hu) | hu
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hu
    exact Or.inr (List.of_mem_zip ((List.takeWhile_sublist _).subset hab)).1
  · exact Or.inl hu
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hu
    exact Or.inr (List.of_mem_zip ((List.dropWhile_sublist _).subset hab)).1

/-! ## The release queue -/

/-- **`tcb_release_enqueue`** of a thread that is a runnable TCB at this state. -/
theorem sa_tcbReleaseEnqueue_p (t : ObjRef) (σ : State Unit) (hr : RnH t σ.kheap) :
    IKp SA σ (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue
  refine ikp_gets_bind ?_
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, hm⟩ := cq5_mem_orderedInsert hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hm; subst z2
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  have hS : SA { σ with releaseQueue := z1 } :=
    ⟨hσ.1, fun u hu => (hm u hu).elim (fun h => h ▸ hr) (hσ.2.1 u), hσ.2.2⟩
  exact (ik_when _ (ik_modify (P := SA) (g := fun s => { s with reprogramTimer := true }) fun _ h => h)) _ hS y hy

/-- **`postpone`** of an SC whose bound thread is a runnable TCB at this state. -/
theorem sa_postpone_p (sc : ObjRef) (σ : State Unit)
    (h : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → RnH t σ.kheap) :
    IKp SA σ (postpone (Z := Unit) sc) := by
  unfold postpone
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, scv, n, hk, hv⟩ := cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  obtain ⟨w, hw, hy⟩ := hy
  have hw1 := sa_dequeue t σ hσ w hw
  obtain ⟨x, -, ew⟩ := q1_tsa_out hw
  obtain ⟨v, hv', hy⟩ := hy
  have hr : RnH t w.2.kheap := by rw [ew]; exact h scv n t hk (hv.symm.trans ha1)
  have hv1 := sa_tcbReleaseEnqueue_p t w.2 hr hw1 v hv'
  exact (ik_modify (P := SA) (g := fun s => { s with reprogramTimer := true }) fun _ h => h) v.2 hv1 y hy

/-- **`sched_context_resume`**: the bound thread is read runnable at the
state `postpone` runs in (everything before it reads). -/
theorem sa_schedContextResume (sc : ObjRef) : SAK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz
  obtain ⟨scv, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  revert hy
  refine ikp_gets_bind ?_ hσ y
  refine ikp_when _ fun _ => ?_
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_when _ fun hc => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' ik_step0) hy) fun _ => ?_
  refine sa_postpone_p sc σ fun y n' t' hk' ht' => ?_
  rw [hk] at hk'; cases hk'
  rw [ha1] at ht'; cases ht'
  exact ⟨x, hx, hc.1⟩
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_schedContextResume _)

theorem sa_maybeDonateSc (t n : ObjRef) : SAK (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc; sa_auto
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_maybeDonateSc _ _)

theorem sa_completeSignal (n t : ObjRef) : SAK (completeSignal (Z := Unit) n t) := by
  unfold completeSignal; sa_auto
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_completeSignal _ _)

/-! ## `cancel_ipc` -/

/-- `t` is not the switch target and not released, and SA. -/
abbrev SAU (t : ObjRef) (σ : State Unit) : Prop := SA σ ∧ NP t σ

theorem np_setSchedulerAction_cn (t : ObjRef) : IK (NP t) (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  exact ik_modify fun _ h => ⟨fun e => (by cases e), h.2⟩

syntax "np_leaf" : tactic
macro_rules | `(tactic| np_leaf) => `(tactic| with_reducible exact np_setSchedulerAction_cn _)

macro "np_auto" : tactic => `(tactic| repeat' (first | np_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem sau_of {α : Type} {t : ObjRef} {m : NonDet (State Unit) α} (h1 : SAK m) (h2 : IK (NP t) m) :
    IK (SAU t) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

theorem np_setThreadStateAct (t u : ObjRef) : IK (NP t) (setThreadStateAct (Z := Unit) u) := by
  unfold setThreadStateAct; np_auto

theorem sau_setThreadState (t : ObjRef) (ts : ThreadState) : IK (SAU t) (setThreadState (Z := Unit) t ts) := by
  intro σ h y hy
  refine ⟨sa_setThreadState_p t ts σ (Or.inr h.2) h.1 y hy, ?_⟩
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : NP t z.2 := (show IK (NP t) (threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t) by
    np_auto) σ h.2 z hz
  exact np_setThreadStateAct t t z.2 hz' y hy

macro "sau_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact sau_setThreadState _ _)
  | ((with_reducible refine sau_of ?_ ?_); sa_leaf; np_auto; done)
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

/-- **`cancel_ipc`**: it writes the state only of a thread it read blocked. -/
theorem sa_cancelIpc (t : ObjRef) : SAK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState
  case running | runningVM | inactive | restart | idleThreadState => exact ikp_of_ik (by sa_auto) σ
  all_goals
    refine ikp_strengthen (P' := SAU t) (fun h => ⟨h, np_of_tcb_nr h hx (by rw [hs]; rfl)⟩) ?_ fun _ h => h.1
    sau_auto
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_cancelIpc _)

/-! ## `send_signal` -/

/-- SchedQ and T4 (ctnq1's one domain). -/
abbrev SQ4 (s : State Unit) : Prop := SchedQ s ∧ T4 s

theorem sq4_of {α : Type} {m : NonDet (State Unit) α} (h1 : TQK m) (h2 : SAK m) (h3 : Q4K m) : IK SQ4 m :=
  fun σ h y hy => ⟨⟨h1 σ h.1.1 y hy, h2 σ h.1.2 y hy⟩, h3 σ h.2 y hy⟩

theorem domOK_of_t4 {σ : State Unit} (h : T4 σ) (t : ObjRef) : DomOK t σ :=
  fun x hx => Or.inl (by rw [h.2.1]; exact h.2.2 t x hx)

/-- `possible_switch_to` of a thread `schedulable` just read. -/
theorem sq4_pst {β : Type} (t : ObjRef) (k : Unit → NonDet (State Unit) β) (hk : ∀ u, IK SQ4 (k u)) :
    IK SQ4 (NonDet.gets (schedulable (Z := Unit) t) >>= fun sched =>
      NonDet.when (sched = true) (possibleSwitchTo (Z := Unit) t) >>= k) := by
  refine ik_gets_bind fun σ => ?_
  refine ikp_bind ?_ hk
  refine ikp_when _ fun hs => ?_
  intro h y hy
  exact ⟨sq_possibleSwitchTo_p t σ (schedulable_rn hs) (domOK_of_t4 h.2 t) h.1 y hy,
    q4_possibleSwitchTo t σ h.2 y hy⟩

macro "sq4_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible refine sq4_pst _ _ (fun _ => ?_))
  | ((with_reducible refine sq4_of ?_ ?_ ?_); tq_leaf; sa_leaf; q4_leaf; done)
  | ik_step0 | ik_unfold))

/-- **`send_signal`** keeps SchedQ ∧ T4: the woken thread was blocked (cancel_ipc
writes it Inactive only while it is neither switch target nor released), is
set Running, and is switched to only if `schedulable`. -/
theorem sq4_sendSignal (n : ObjRef) (b : Badge) : IK SQ4 (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; sq4_auto

/-- **FL4's timer step** (signals only). -/
theorem sq4_fl4Awaken : IK SQ4 (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    have h1' : SQ4 σ1 := by
      rcases h1 with rfl | ⟨n, bd, hs⟩
      · exact ih
      · exact sq4_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
    exact h1'

theorem validIdle_of_vi {N S : ObjRef} {s : State Unit} (h : SInvI.VI N S false s) : SInvI.ValidIdle s := by
  have e1 : s.idleThread = N := h.1
  have e2 : s.idleSc = S := h.2.1
  unfold SInvI.ValidIdle; rw [e1, e2]; exact h

/-- **The tail of every kernel entry**: FL4's timer step, `schedule`,
`activate_thread`. -/
theorem sq_tail : HK1 (fun s => SQ4 s ∧ SInvI.ValidIdle s) SchedQ
    (fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) := by
  intro σ h y ⟨z, hz, hy⟩
  have h1 := sq4_fl4Awaken σ h.1 z hz
  have h2 := validIdle_of_vi (SInvI.vi_fl4Awaken σ h.2 z hz)
  exact sq_exit z.2 (aw_of h1.1 h1.2 h2) y hy

end

end Fl4Proofs.P3.SInvQ
