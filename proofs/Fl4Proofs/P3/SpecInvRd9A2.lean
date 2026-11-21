/-
P3 (DESIGN.md §9), invariant line G1 (rd9, KENTRY-PLAN rd8a handoff 2):
**`RCA ∧ CtR ∧ HRC` across `fl4Awaken`** (rd8a's `hAw`; spec side only,
outside the JAtZ cone).

* `VW u c v r R0 T0 s`: the binding view of `u` (`tvw`: its SC if a TCB) is
  `v`, the refill view of `c` (`rvw`: refills, max, bound TCB if an SC) is
  `r`, the threads `R0` are released, the time is `T0`. Leaves: every `SVM`
  function keeping the release queue (`vw_of`), `possible_switch_to` (RdS's
  `ktc_possibleSwitchTo`), SC writes away from `c` (`vw_updSc`),
  `sched_context_resume` (it only appends to the release queue:
  `rqs_orderedInsert`), the free donation of `maybe_donate_sc` (`vw_md`:
  the woken `t` is unbound, so it is not a bound `u`; the donated SC has no
  TCB, so it is not `c` when `c` is bound), the unblock check of an SC other
  than `c` (`vw_ifCond`).
* The woken thread `t` is never bound to `c` along the wake (`NB t c`).
* `u`'s runnability can only come from `u` itself: the FaultTcbs frame
  instance `rnF u Q` (`p = u → runnable → Q`), carried by the generated
  `fg_*` lemmas; the only wake-up writes `t ≠ u`.
* When `u` is the woken thread, `SR u` (RdL) at `maybe_donate_sc`'s end is
  carried by `possible_switch_to` (`sr_ktc`) and the unblock check
  (`sr_ifCond`: it changes refills only, RdJ's `UK` keeps every `RdyT`).
* **`aw_sendSignal`**, **`aw_fl4Awaken : IK AW9 fl4Awaken`** with
  `AW9 := RO ∧ ScInv ∧ RCA ∧ CtR ∧ HRC`.
-/
import Fl4Proofs.P3.SpecInvRd9A1
import Fl4Proofs.P3.SpecInvSbG4
open Classical

namespace Fl4Proofs.P3.SInvR.A9
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Views -/

/-- The binding view of an object: a TCB's SC. -/
def tvw : Option KernelObject → Option (Option ObjRef)
  | some (.tcb x) => some x.tcbSchedContext
  | _ => none

/-- The refill view of an object: an SC's refills, max and bound TCB. -/
def rvw : Option KernelObject → Option (List Refill × Nat × Option ObjRef)
  | some (.schedContext y _) => some (y.scRefills, y.scRefillMax, y.scTcb)
  | _ => none

theorem vw_sv {o o' : Option KernelObject} (h : SVK.sv o' = SVK.sv o) : tvw o' = tvw o ∧ rvw o' = rvw o := by
  rcases o with _ | o <;> rcases o' with _ | o'
  · exact ⟨rfl, rfl⟩
  all_goals first
    | (cases o' <;> simp_all [SVK.sv, tvw, rvw]; done)
    | (cases o <;> simp_all [SVK.sv, tvw, rvw]; done)
    | (cases o <;> cases o' <;> simp_all [SVK.sv, tvw, rvw])

theorem tvw_tcb {o : Option KernelObject} {a : Option ObjRef} (h : tvw o = some a) :
    ∃ x, o = some (.tcb x) ∧ x.tcbSchedContext = a := by
  rcases o with _ | o
  · cases h
  · cases o <;> simp [tvw] at h
    exact ⟨_, rfl, h⟩

theorem rvw_sc {o : Option KernelObject} {r : List Refill × Nat × Option ObjRef} (h : rvw o = some r) :
    ∃ y n, o = some (.schedContext y n) ∧ (y.scRefills, y.scRefillMax, y.scTcb) = r := by
  rcases o with _ | o
  · cases h
  · cases o <;> simp [rvw] at h
    exact ⟨_, _, rfl, h⟩

/-- The pinned view. -/
abbrev VW (u c : ObjRef) (v : Option (Option ObjRef)) (r : Option (List Refill × Nat × Option ObjRef))
    (R0 : List ObjRef) (T0 : Time) (s : State Unit) : Prop :=
  tvw (s.kheap u) = v ∧ rvw (s.kheap c) = r ∧ (∀ w ∈ R0, w ∈ s.releaseQueue) ∧ s.curTime = T0

/-- The woken thread is not bound to `c`. -/
abbrev NB (t c : ObjRef) (s : State Unit) : Prop := ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some c

section V
variable {u c : ObjRef} {v : Option (Option ObjRef)} {r : Option (List Refill × Nat × Option ObjRef)}
  {R0 : List ObjRef} {T0 : Time}

theorem vw_of {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m)
    (h2 : ∀ R, IK (fun s : State Unit => s.releaseQueue = R) m) : IK (VW u c v r R0 T0) m := by
  intro s hs y hy
  have hS := h1 s y hy
  have hq := h2 s.releaseQueue s rfl y hy
  exact ⟨(vw_sv (hS.1 u)).1.trans hs.1, (vw_sv (hS.1 c)).2.trans hs.2.1, by rw [hq]; exact hs.2.2.1,
    hS.2.1.trans hs.2.2.2⟩

theorem nb_of_sv {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (t c : ObjRef) : IK (NB t c) m := by
  intro s hs y hy x hx
  have e := (h1 s y hy).1 t
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := SVK.sv_tcb (o := s.kheap t) e.symm
  rw [← e0]; exact hs x0 hx0

theorem vw_ktc (t : ObjRef) : IK (VW u c v r R0 T0) (possibleSwitchTo (Z := Unit) t) := by
  intro s hs y hy
  obtain ⟨ek, et, er, -⟩ := ktc_possibleSwitchTo s.kheap s.curTime s.releaseQueue s.curThread t s
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  exact ⟨by rw [ek]; exact hs.1, by rw [ek]; exact hs.2.1, by rw [er]; exact hs.2.2.1, by rw [et]; exact hs.2.2.2⟩

theorem nb_ktc (t' t c : ObjRef) : IK (NB t c) (possibleSwitchTo (Z := Unit) t') := by
  intro s hs y hy
  obtain ⟨ek, -⟩ := ktc_possibleSwitchTo s.kheap s.curTime s.releaseQueue s.curThread t' s
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  intro x hx; rw [ek] at hx; exact hs x hx

/-- An SC write: away from `c`, or `c` is no SC. -/
theorem vw_updSc (q : ObjRef) (f : SchedContext → SchedContext) (hq : q = c → r = none) :
    IK (VW u c v r R0 T0) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  refine ⟨?_, ?_, hs.2.2.1, hs.2.2.2⟩
  · show tvw (Function.update s.kheap q _ u) = v
    by_cases hu : u = q
    · subst hu; rw [Function.update_self, ← hs.1, hk]; rfl
    · rw [Function.update_of_ne hu]; exact hs.1
  · show rvw (Function.update s.kheap q _ c) = r
    by_cases hc : c = q
    · subst hc; have := hs.2.1; rw [hk, hq rfl] at this; cases this
    · rw [Function.update_of_ne hc]; exact hs.2.1

/-- An SC write keeping refills, max and bound TCB. -/
theorem vw_updSc_keep (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax ∧ (f y).scTcb = y.scTcb) :
    IK (VW u c v r R0 T0) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  refine ⟨?_, ?_, hs.2.2.1, hs.2.2.2⟩
  · show tvw (Function.update s.kheap q _ u) = v
    by_cases hu : u = q
    · subst hu; rw [Function.update_self, ← hs.1, hk]; rfl
    · rw [Function.update_of_ne hu]; exact hs.1
  · show rvw (Function.update s.kheap q _ c) = r
    by_cases hc : c = q
    · subst hc; rw [Function.update_self, ← hs.2.1, hk]
      obtain ⟨e1, e2, e3⟩ := hf y0
      simp only [rvw, e1, e2, e3]
    · rw [Function.update_of_ne hc]; exact hs.2.1

end V

/-! ## The release queue -/

theorem rq_walk_asUser {α : Type} (t : ObjRef) (m : UserMonad α) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (asUser (Z := Unit) t m) := by
  unfold asUser; repeat' (first | ik_step0 | ik_unfold)

theorem rq_walk_tcbNtfnDequeue (t n : ObjRef) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; repeat' (first | ik_step0 | ik_unfold)

theorem rq_walk_setNotification (n : ObjRef) (nt : Notification) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (setNotification (Z := Unit) n nt) := by
  unfold setNotification setSimpleKo; repeat' (first | ik_step0 | ik_unfold)

theorem rq_walk_getTcbObjRef (f : Tcb → Option ObjRef) (t : ObjRef) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; repeat' (first | ik_step0 | ik_unfold)

theorem rq_walk_blockedCancelIpc (st : ThreadState) (t : ObjRef) (rp : Option ObjRef) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (blockedCancelIpc (Z := Unit) st t rp) := by
  unfold blockedCancelIpc; repeat' (first | (with_reducible exact rq_setThreadState _ _ _) | ik_step0 | ik_unfold)

theorem rq_walk_refillUnblockCheck (p : ObjRef) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck refillHeadOverlappingLoop isRoundRobin getScRefillReady
  repeat' (first | ik_step0 | ik_unfold)

theorem mapM_length {α β : Type} (g : α → NonDet (State Unit) β) :
    ∀ (xs : List α) (s : State Unit) (y : List β × State Unit), y ∈ (NonDet.mapM g xs s).1 → y.1.length = xs.length
  | [], s, y, hy => by
    simp only [NonDet.mapM] at hy
    rw [Set.mem_singleton_iff.1 hy]; rfl
  | a :: l, s, y, hy => by
    simp only [NonDet.mapM] at hy
    obtain ⟨z1, -, hy⟩ := hy
    obtain ⟨z2, hz2, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy]
    simp only [List.length_cons]
    rw [mapM_length g l _ z2 hz2]

/-- `ordered_insert` keeps the old members. -/
theorem rqs_orderedInsert {α β : Type} [Nonempty β] {t : α} {ts : List α} {f : α → RMonad Unit β}
    {R : β → β → Prop} {σ : State Unit} {y : List α × State Unit}
    (hy : y ∈ (orderedInsert (Z := Unit) t ts f R σ).1) : ∀ w ∈ ts, w ∈ y.1 := by
  unfold orderedInsert at hy
  obtain ⟨y1, -, hy⟩ := hy
  obtain ⟨y2, hy2, hy⟩ := hy
  have hl := mapM_length _ ts _ y2 hy2
  obtain ⟨y3, hy3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy3] at hy
  obtain ⟨y4, hy4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy4] at hy
  rw [Set.mem_singleton_iff.1 hy]
  intro w hw
  have hz : w ∈ (ts.zip y2.1).map Prod.fst := by
    rw [List.map_fst_zip (by omega)]; exact hw
  rw [← List.takeWhile_append_dropWhile (l := ts.zip y2.1) (p := fun x => decide (R x.2 y1.1))] at hz
  simp only [List.map_append, List.mem_append] at hz
  simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons]
  rcases hz with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

theorem rqs_tcbReleaseEnqueue (t : ObjRef) (R0 : List ObjRef) :
    IK (fun s : State Unit => ∀ w ∈ R0, w ∈ s.releaseQueue) (tcbReleaseEnqueue (Z := Unit) t) := by
  intro s hs y hy
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz0
  obtain ⟨z, hz, hy⟩ := hy
  have hm := rqs_orderedInsert hz
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  unfold NonDet.when at hy
  split_ifs at hy <;> rw [Set.mem_singleton_iff.1 hy] <;> exact fun a ha => hm a (hs a ha)

theorem kt_schedContextResume (p : ObjRef) (K : ObjRef → Option KernelObject) (T : Time) :
    IK (fun s : State Unit => s.kheap = K ∧ s.curTime = T) (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume postpone tcbReleaseEnqueue readyTimesAppend orderedInsert
  repeat' (first | ik_step0 | ik_unfold)

theorem rqs_schedContextResume (p : ObjRef) (R0 : List ObjRef) :
    IK (fun s : State Unit => ∀ w ∈ R0, w ∈ s.releaseQueue) (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume postpone
  repeat' (first | (with_reducible exact rqs_tcbReleaseEnqueue _ _) | ik_step0 | ik_unfold)

theorem vw_schedContextResume (p u c : ObjRef) (v : Option (Option ObjRef)) (r : Option (List Refill × Nat × Option ObjRef))
    (R0 : List ObjRef) (T0 : Time) : IK (VW u c v r R0 T0) (schedContextResume (Z := Unit) p) := by
  intro s hs y hy
  obtain ⟨ek, et⟩ := kt_schedContextResume p s.kheap s.curTime s ⟨rfl, rfl⟩ y hy
  exact ⟨by rw [ek]; exact hs.1, by rw [ek]; exact hs.2.1, rqs_schedContextResume p R0 s hs.2.2.1 y hy,
    by rw [et]; exact hs.2.2.2⟩

/-! ## `maybe_donate_sc` -/

/-- **The free donation**: `t` is unbound, so not a bound `u`; the donated SC
has no TCB, so it is not a bound `c`. Also keeps `NB t c`. -/
theorem vw_md (t n u c : ObjRef) (v : Option (Option ObjRef)) (r : Option (List Refill × Nat × Option ObjRef))
    (R0 : List ObjRef) (T0 : Time) (hv : t ≠ u ∨ v ≠ some none)
    (hr : r = none ∨ ∃ a m w, r = some (a, m, some w)) (σ : State Unit) (hσ : VW u c v r R0 T0 σ) :
    ∀ y ∈ (maybeDonateSc (Z := Unit) t n σ).1, VW u c v r R0 T0 y.2 ∧ (NB t c σ → NB t c y.2) := by
  intro y hy
  unfold maybeDonateSc at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold getTcbObjRef at hz
  obtain ⟨x1, hx1, rfl⟩ := SInvQ.q1_mem_threadGet hz
  dsimp only at hy
  unfold NonDet.when at hy
  split_ifs at hy with hn
  · obtain ⟨w, hw, hy⟩ := hy
    have ew : w.2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
    obtain ⟨w1, w2⟩ := w
    simp only at ew; subst w2
    cases w1 with
    | none =>
      obtain rfl : y = ((), σ) := hy
      exact ⟨hσ, id⟩
    | some p =>
      dsimp only [NonDet.maybeM] at hy
      obtain ⟨vv, hvv, hy⟩ := hy
      obtain ⟨ev, sc, m, hk, hv1⟩ := SInvQ.cq5_mem_getScObjRef hvv
      obtain ⟨v1, v2⟩ := vv
      simp only at ev hv1; subst v2; subst hv1
      dsimp only at hy
      split_ifs at hy with hsc
      · obtain ⟨d, hd, hy⟩ := hy
        -- the donation
        have htu : t ≠ u := by
          rintro rfl
          rcases hv with h | h
          · exact h rfl
          · apply h; rw [← hσ.1, hx1]; simp [tvw, hn]
        have hpc : p = c → r = none := by
          rintro rfl
          rcases hr with h | ⟨a, m', w', h⟩
          · exact h
          · have := hσ.2.1; rw [hk, h] at this; simp [rvw, hsc] at this
        unfold schedContextDonate at hd
        obtain ⟨z1, hz1, hd⟩ := hd
        obtain ⟨e1, sc1, n1, hk1, hv2⟩ := SInvQ.cq5_mem_getScObjRef hz1
        obtain ⟨z11, z12⟩ := z1
        simp only at e1 hv2; subst z12
        rw [hk] at hk1; cases hk1
        rw [hsc] at hv2; subst hv2
        obtain ⟨w3, hw3, hd⟩ := hd
        unfold NonDet.when at hw3
        rw [if_neg (by simp)] at hw3
        obtain rfl : w3 = ((), σ) := hw3
        obtain ⟨w4, hw4, hd⟩ := hd
        have hV4 := vw_updSc (u := u) (c := c) (v := v) (r := r) (R0 := R0) (T0 := T0) p _ hpc σ hσ w4 hw4
        obtain ⟨y4, n4, hk4, e4⟩ := SVK.updSc_mem hw4
        obtain ⟨x5, hx5, e5⟩ := SInv.mem_threadSet hd
        have hpt : p ≠ t := fun e => by rw [e, hx1] at hk; cases hk
        have hx4 : w4.2.kheap t = some (.tcb x1) := by
          rw [e4]; dsimp only; rw [Function.update_of_ne (Ne.symm hpt)]; exact hx1
        rw [hx4] at hx5; cases hx5
        have hd5 : VW u c v r R0 T0 d.2 := by
          rw [e5]
          refine ⟨?_, ?_, hV4.2.2.1, hV4.2.2.2⟩
          · show tvw (Function.update w4.2.kheap t _ u) = v
            rw [Function.update_of_ne (Ne.symm htu)]; exact hV4.1
          · show rvw (Function.update w4.2.kheap t _ c) = r
            by_cases hct : c = t
            · subst hct
              have := hσ.2.1; rw [hx1] at this
              rw [Function.update_self, ← this]; rfl
            · rw [Function.update_of_ne hct]; exact hV4.2.1
        refine ⟨vw_schedContextResume p u c v r R0 T0 d.2 hd5 y hy, fun _ => ?_⟩
        -- `t` is now bound to `p ≠ c` (when `c` is bound)
        have hnb5 : NB t c d.2 := by
          intro x hx
          rw [e5] at hx; dsimp only at hx; rw [Function.update_self] at hx; cases hx
          show some p ≠ some c
          intro e; injection e with e; subst e
          rcases hr with h | ⟨a, m', w', h⟩
          · have := hσ.2.1; rw [hk, h] at this; cases this
          · have := hσ.2.1; rw [hk, h] at this; simp [rvw, hsc] at this
        obtain ⟨ek, -⟩ := kt_schedContextResume p d.2.kheap d.2.curTime d.2 ⟨rfl, rfl⟩ y hy
        intro x hx; rw [ek] at hx; exact hnb5 x hx
      · obtain rfl : y = ((), σ) := hy
        exact ⟨hσ, id⟩
  · obtain rfl : y = ((), σ) := hy
    exact ⟨hσ, id⟩

/-! ## The unblock check -/

theorem vw_ifCond (o : Option ObjRef) (a b : Option Bool) (u c : ObjRef) (v : Option (Option ObjRef))
    (r : Option (List Refill × Nat × Option ObjRef)) (R0 : List ObjRef) (T0 : Time) (ho : o ≠ some c ∨ r = none) :
    IK (VW u c v r R0 T0) (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  cases o with
  | none => exact ik_pure _
  | some p =>
    have hq : p = c → r = none := fun e => by
      rcases ho with h | h
      · exact absurd (by rw [e]) h
      · exact h
    refine ik_bind (vw_of (by sv_auto) (fun R => by repeat' (first | ik_step0 | ik_unfold))) fun _ => ?_
    refine ik_bind (ik_gets _) fun _ => ik_pure_bind ?_
    refine ik_when _ (ik_when _ ?_)
    unfold refillUnblockCheck refillHeadOverlappingLoop mergeOverlappingRefills refillPopHead updateRefillHd
      isRoundRobin getRefillHead
    repeat' (first | exact vw_updSc p _ hq | ik_step0 | ik_unfold)

end

end Fl4Proofs.P3.SInvR.A9
