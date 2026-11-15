/-
P3 (DESIGN.md §9), notifications: **`notification::send_signal` refines
l4v `send_signal`** (nondeterministic spec, `Z = Unit`) in the cases that
involve no other subsystem:

* `send_signal_idle_unbound`: an idle notification without a bound TCB
  becomes active with the badge;
* `send_signal_idle_bound_idle`: an idle notification whose bound TCB is
  not blocked on a receive becomes active with the badge;
* `send_signal_active`: on an active notification, the badge is OR-ed into
  the pending one.

In each, from states related by `NtfnStateRel` (with `NPlaced`), the spec has
exactly one outcome and does not fail, and FL4's final state is related to
it; FL4 writes only words of the footprint (`WritesIn … NFoot`), the spec
only changes `ntfn_obj` (`NtfnStep`), so any relation of the other
subsystems that ignores those (`SchedHyps.stable`, NtfnSched.lean) is kept
too. The waiting case and the bound-receiver case wake a thread, which
involves the scheduler: NtfnSched.lean.
-/
import Fl4Proofs.P3.NtfnWrite
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

/-! ## Reading the relation -/

section
variable {Z : Type} {N T : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Z}

theorem NtfnStateRel.at_ntfn (hR : NtfnStateRel N T m σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) : NtfnRel1 m T n x := by
  obtain ⟨y, hky, hy⟩ := hR.ntfn n hn
  rw [hk] at hky; cases hky; exact hy

theorem NtfnStateRel.at_tcb (hR : NtfnStateRel N T m σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) : TcbRel1 m t x := by
  obtain ⟨y, hky, hy⟩ := hR.tcb t ht
  rw [hk] at hky; cases hky; exact hy

theorem optRef_zero : optRef 0#u64 = none := by simp [optRef]
theorem optRef_ne {w : U64} (h : w ≠ 0#u64) : optRef w = some w.bv := by simp [optRef, h]
theorem optRef_none {w : U64} (h : optRef w = none) : w = 0#u64 := by
  by_contra e; rw [optRef_ne e] at h; cases h
theorem optRef_some {w : U64} {p : Fl4Spec.ObjRef} (h : optRef w = some p) : w ≠ 0#u64 ∧ w.bv = p := by
  by_cases e : w = 0#u64
  · rw [e, optRef_zero] at h; cases h
  · rw [optRef_ne e] at h; cases h; exact ⟨e, rfl⟩

/-- A queue relation to the empty list only says the queue is empty. -/
theorem queueRel_nil_iff {m : U64 → U64} {T : Set U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} :
    QueueRel m T l q [] ↔ q.head = 0#u64 ∧ q.end = 0#u64 :=
  ⟨fun h => ⟨h.head, h.last⟩, fun ⟨h1, h2⟩ => ⟨List.nodup_nil, by simp, h1, h2, trivial⟩⟩

end

theorem ntfn_consts : obj.NTFN_IDLE = 0#u64 ∧ obj.NTFN_WAITING = 1#u64 ∧ obj.NTFN_ACTIVE = 2#u64 := by
  unfold obj.NTFN_IDLE obj.NTFN_WAITING obj.NTFN_ACTIVE; exact ⟨rfl, rfl, rfl⟩

theorem two_and3 : (2#u64 &&& 3#u64) = 2#u64 := by decide
theorem zero_and3 : (0#u64 &&& 3#u64) = 0#u64 := by decide

/-! ## The store side: writing the state and the badge -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {N T : Set U64}

/-- `set_active` on an idle notification: related to the spec's
`set_notification` of an active notification with the badge. -/
theorem set_active_rel (hP : NPlaced T N) {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) (b : U64) :
    let s' := L.wr (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
      (nBadgeA n) b
    NtfnStateRel N T (L.mem s')
        (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn b.bv) x))) ∧
      WritesIn st s s' (NWrite N T) := by
  intro s'
  have hna := hP.ntfn n hn
  have h1 : NWr st N T n s (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) := by
    rw [epTSA_eq]; exact nwr_wr hP hn (by simp) (by simp) _ _
  have h2 : NWr st N T n (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) s' := by
    show NWr st N T n _ (L.wr _ (nBadgeA n) b)
    rw [nBadgeA_eq]; exact nwr_wr hP hn (by simp) (by simp) _ _
  have h := h1.trans h2
  have hx := hR.at_ntfn hn hk
  have hobj := hx.obj
  rw [hidle] at hobj
  obtain ⟨-, hq⟩ := hobj
  rw [queueRel_nil_iff] at hq
  -- the words of `n` after the two writes
  have ne_b : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 16#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) =
        L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
          (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    show L.mem (L.wr _ (nBadgeA n) b) _ = _
    rw [nBadgeA_eq]
    exact rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have ne_ts : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 8#u64 →
      L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64)))
          (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    rw [epTSA_eq]
    exact rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have e_head : L.mem s' (epHeadA n) = L.mem s (epHeadA n) := by
    rw [epHeadA_eq, ne_b _ (by simp) (by simp) (by simp), ne_ts _ (by simp) (by simp) (by simp)]
  have e_ts : L.mem s' (epTSA n) = (L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64) := by
    rw [epTSA_eq, ne_b _ (by simp) (by simp) (by simp), ← epTSA_eq]
    exact rd_wr_eq (foot_ts hP hn).1
  have e_badge : L.mem s' (nBadgeA n) = b := rd_wr_eq (foot_badge hP hn).1
  have e_bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq, ne_b _ (by simp) (by simp) (by simp), ne_ts _ (by simp) (by simp) (by simp)]
  have e_sc : L.mem s' (nScA n) = L.mem s (nScA n) := by
    rw [nScA_eq, ne_b _ (by simp) (by simp) (by simp), ne_ts _ (by simp) (by simp) (by simp)]
  refine ⟨hR.upd_ntfn hn _ h.ntfn (fun y hy => (h.tcb y hy).1) (fun y hy _ => (h.tcb y hy).2) ⟨?_, ?_, ?_, ?_⟩, h.foot⟩
  · show NtfnObjRel _ T n (.activeNtfn b.bv)
    refine ⟨?_, ?_, by rw [e_badge]⟩
    · rw [stOf, e_ts, ts_state, ntfn_consts.2.2]; exact two_and3
    · rw [queueRel_nil_iff]
      refine ⟨?_, ?_⟩
      · show L.mem s' (epHeadA n) = 0#u64
        rw [e_head]; exact hq.1
      · show L.mem s' (epTSA n) &&& ~~~3#u64 = 0#u64
        rw [e_ts, ts_end]; exact hq.2
  · show x.ntfnBoundTcb = _; rw [e_bound]; exact hx.bound
  · rw [e_bound]; exact hx.bound_mem
  · show x.ntfnSc = _; rw [e_sc]; exact hx.sc

/-- Writing the badge word of an active notification (`send_signal` on an
active notification). -/
theorem set_badge_rel (hP : NPlaced T N) {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (b : U64) :
    let s' := L.wr s (nBadgeA n) b
    NtfnStateRel N T (L.mem s')
        (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn b.bv) x))) ∧
      WritesIn st s s' (NWrite N T) := by
  intro s'
  have hna := hP.ntfn n hn
  have h : NWr st N T n s s' := by show NWr st N T n s (L.wr s _ b); rw [nBadgeA_eq]; exact nwr_wr hP hn (by simp) (by simp) _ _
  have hx := hR.at_ntfn hn hk
  have hobj := hx.obj
  rw [hact] at hobj
  obtain ⟨hs, hq, -⟩ := hobj
  have ne_b : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 16#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K hK hK8 hne
    show L.mem (L.wr _ (nBadgeA n) b) _ = _
    rw [nBadgeA_eq]
    exact rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn hK hK8).1
      (nwords_ne hna (by simp) (by omega) (Ne.symm hne))
  have hnw : NWordsEq (L.mem s) (L.mem s') n ∨ True := Or.inr trivial
  clear hnw
  have e_head : L.mem s' (epHeadA n) = L.mem s (epHeadA n) := by rw [epHeadA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have e_ts : L.mem s' (epTSA n) = L.mem s (epTSA n) := by rw [epTSA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have e_bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have e_sc : L.mem s' (nScA n) = L.mem s (nScA n) := by rw [nScA_eq, ne_b _ (by simp) (by simp) (by simp)]
  have hqe : qOf (L.mem s') n = qOf (L.mem s) n := by simp only [qOf, e_head, e_ts]
  refine ⟨hR.upd_ntfn hn _ h.ntfn (fun y hy => (h.tcb y hy).1) (fun y hy _ => (h.tcb y hy).2) ⟨?_, ?_, ?_, ?_⟩, h.foot⟩
  · show NtfnObjRel _ T n (.activeNtfn b.bv)
    refine ⟨?_, ?_, by rw [rd_wr_eq (foot_badge hP hn).1]⟩
    · simp only [stOf, e_ts]; exact hs
    · rw [hqe, queueRel_nil_iff]; exact queueRel_nil_iff.1 hq
  · show x.ntfnBoundTcb = _; rw [e_bound]; exact hx.bound
  · rw [e_bound]; exact hx.bound_mem
  · show x.ntfnSc = _; rw [e_sc]; exact hx.sc

end

/-! ## `send_signal` -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T : Set U64}

theorem stOf_idle {m : U64 → U64} {n : U64} {o : Fl4Spec.Ntfn} (h : NtfnObjRel m T n o) (ho : o = .idleNtfn) :
    stOf m n = obj.NTFN_IDLE := by subst ho; rw [h.1, ntfn_consts.1]
theorem stOf_active {m : U64 → U64} {n : U64} {o : Fl4Spec.Ntfn} {b : Fl4Spec.Badge} (h : NtfnObjRel m T n o)
    (ho : o = .activeNtfn b) : stOf m n = obj.NTFN_ACTIVE := by subst ho; rw [h.1, ntfn_consts.2.2]
theorem stOf_waiting {m : U64 → U64} {n : U64} {o : Fl4Spec.Ntfn} {q : List Fl4Spec.ObjRef}
    (h : NtfnObjRel m T n o) (ho : o = .waitingNtfn q) : stOf m n = obj.NTFN_WAITING := by
  subst ho; rw [h.1, ntfn_consts.2.1]

/-- The outcome of `send_signal` on an idle notification, or one whose bound
TCB is not receiving: active with the badge. -/
theorem sendSignal_activate {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    (hb : x.ntfnBoundTcb = none ∨
      ∃ t tcb, x.ntfnBoundTcb = some t ∧ σ.kheap t = some (.tcb tcb) ∧ Fl4Spec.receiveBlocked tcb.tcbState = false)
    (badge : Fl4Spec.Badge) :
    Fl4Spec.sendSignal (Z := Unit) p badge σ =
      ({((), updK σ p (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge) x)))}, False) := by
  unfold Fl4Spec.sendSignal
  rw [nd_bind_one (getNotification_eq hk)]
  rcases hb with hb | ⟨t, tcb, hb, hkt, hr⟩
  · simp only [hidle, hb]
    exact setNotification_eq _ hk
  · simp only [hidle, hb]
    rw [nd_bind_one (getThreadState_eq hkt)]
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    exact setNotification_eq _ hk

theorem sendSignal_active_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (badge : Fl4Spec.Badge) :
    Fl4Spec.sendSignal (Z := Unit) p badge σ =
      ({((), updK σ p (.notification
        (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn (Fl4Spec.combineNtfnBadges badge b0)) x)))}, False) := by
  unfold Fl4Spec.sendSignal
  rw [nd_bind_one (getNotification_eq hk)]
  simp only [hact]
  exact setNotification_eq _ hk

/-- What the simple refinements conclude. -/
def SingleRel (N T : Set U64) (s : S) (σ : Fl4Spec.State Unit) (spec : Set (Unit × Fl4Spec.State Unit) × Prop)
    (s' : S) : Prop :=
  ∃ σ', spec = ({((), σ')}, False) ∧ NtfnStateRel N T (L.mem s') σ' ∧ NtfnStep σ σ' ∧
    WritesIn st s s' (NWrite N T)

/-- **Idle, no bound TCB**: the notification becomes active with the badge. -/
theorem send_signal_idle_unbound (hP : NPlaced T N) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    (hb : x.ntfnBoundTcb = none) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      r.2 = a ∧ SingleRel (st := st) N T s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ := by
  have hx := hR.at_ntfn hn hk
  have h0 : L.mem s (nBoundA n) = 0#u64 := optRef_none (hx.bound ▸ hb)
  unfold notification.send_signal
  step
  have : st = obj.NTFN_IDLE := by rw [st_post]; exact stOf_idle hx.obj hidle
  simp only [this, ↓reduceIte]
  step
  step
  simp only [b_post, i_post, h0, decide_true, ↓reduceIte]
  step
  subst s1_post
  obtain ⟨hR', hW⟩ := set_active_rel hP hR hn hk hidle badge
  exact ⟨_, sendSignal_activate hk hidle (Or.inl hb) badge.bv, hR', NtfnStep.ntfn hk rfl rfl, hW⟩

/-- **Idle, bound TCB not receiving**: the notification becomes active with
the badge. -/
theorem send_signal_idle_bound_idle (hP : NPlaced T N) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t) (hkt : σ.kheap t = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = false)
    (hvm : tcb.tcbState ≠ .runningVM) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      r.2 = a ∧ SingleRel (st := st) N T s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ := by
  have hx := hR.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := optRef_some (hx.bound ▸ hb)
  have hbT := hx.bound_mem hb0
  have hy := hR.at_tcb hbT (hbt ▸ hkt)
  have hns : L.mem s (tStA (L.mem s (nBoundA n))) ≠ sched.TS_BLOCKED_ON_RECV := by
    intro e
    have h3 := hy.st
    rw [e, tsVals.2.2.1] at h3
    revert hrb h3
    cases tcb.tcbState <;> simp [tsCode, Fl4Spec.receiveBlocked]
  have hnvm : L.mem s (tStA (L.mem s (nBoundA n))) ≠ sched.TS_RUNNING_VM := by
    intro e
    have h3 := hy.st
    rw [e] at h3
    simp only [sched.TS_RUNNING_VM] at h3
    cases hst : tcb.tcbState <;> simp_all [tsCode]
  unfold notification.send_signal
  step
  have : st = obj.NTFN_IDLE := by rw [st_post]; exact stOf_idle hx.obj hidle
  simp only [this, ↓reduceIte]
  step
  step
  simp only [b_post, i_post, hb0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step
  simp only [i1_post, hns, ↓reduceIte]
  step
  subst s1_post
  obtain ⟨hR', hW⟩ := set_active_rel hP hR hn hk hidle badge
  have hst' : L.mem (L.wr (L.wr s (epTSA n)
      ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) (nBadgeA n) badge)
      (tStA (L.mem s (nBoundA n))) = L.mem s (tStA (L.mem s (nBoundA n))) := by
    have h1 := nwr_wr (L := L) hP (K := 8#u64) hn (by simp) (by simp) s
      ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))
    rw [← epTSA_eq] at h1
    have h2 := nwr_wr (L := L) hP (K := 16#u64) hn (by simp) (by simp)
      (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) badge
    rw [← nBadgeA_eq] at h2
    exact ((h1.trans h2).tcb _ hbT).1.st
  step with obj.Tcb.state.spec as ⟨vm_state, hvs⟩
  simp only [hvs, hst', hnvm, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
  exact ⟨trivial, _, sendSignal_activate hk hidle (Or.inr ⟨t, tcb, hb, hkt, hrb⟩) badge.bv, hR',
    NtfnStep.ntfn hk rfl rfl, hW⟩

/-- **Active**: the badge is OR-ed into the pending one. -/
theorem send_signal_active (hP : NPlaced T N) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      r.2 = a ∧ SingleRel (st := st) N T s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ := by
  have hx := hR.at_ntfn hn hk
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  unfold notification.send_signal
  step
  have : st = obj.NTFN_ACTIVE := by rw [st_post]; exact stOf_active hx.obj hact
  simp only [this, ntfn_consts.1, ntfn_consts.2.1, ntfn_consts.2.2]
  simp only [show (2#u64 : U64) ≠ 0#u64 by decide, show (2#u64 : U64) ≠ 1#u64 by decide, ↓reduceIte]
  step
  step
  step
  subst s1_post
  obtain ⟨hR', hW⟩ := set_badge_rel hP hR hn hk hact b
  have e : b.bv = Fl4Spec.combineNtfnBadges badge.bv b0 := by
    have h := b_post1
    rw [i_post] at h
    exact h.trans ((BitVec.or_comm _ _).trans (congrArg (badge.bv ||| ·) hb0))
  rw [e] at hR'
  exact ⟨_, sendSignal_active_eq hk hact badge.bv, hR', NtfnStep.ntfn hk rfl rfl, hW⟩

end

end

end Fl4Proofs.P3.Notif
