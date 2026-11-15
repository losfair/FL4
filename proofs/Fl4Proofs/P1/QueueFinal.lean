/-
P1: the object-specific work of `finalise_cap` keeps the invariants (`BlkOK`,
which includes the timer-tree typing) and has a `KW` footprint, so it keeps
every cap slot.
-/
import Fl4Proofs.P1.QueueTimerSet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem restart_ne : sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_RECV :=
  ⟨runnable_ne_reply runnable_restart, runnable_ne_recv runnable_restart⟩

/-- The head of a nonempty queue and the next link. -/
theorem QueueRel.head_next {m : U64 → U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {t : U64} {ys : List U64}
    (h : QueueRel m T l q (t :: ys)) : m (nextA l t) = ys.headD 0#u64 := by
  have := h.seg; simp only [Seg_cons] at this; exact this.2.1

/-! ## `cancel_all_signals` -/

/-- One round of `cancel_all_signals`: the waiter at the head of `n`'s queue
is dequeued, restarted, unblocked and offered to the scheduler. -/
theorem cas_round {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ Foot st T Cs Sg Scs Z {n} s s4 ∧
        (next ≠ 0#u64 → L.epState s4 n = 1#u64 ∧ (L.epQ s4 n).head = next) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst
  rw [hhd] at hdT hbe hds
  have hta := hT t hdT
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 n heE
  have hne : EQ n ≠ [] := fun h0' => ((hEW.2.2.2.2.2.2.2.2.2.2 n heE h0').2 hH) hst
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y = t := by rw [← hhd, hq.head, hys]; rfl
  subst hy
  rw [hys] at hq
  have hnext := hq.head_next
  have hbl : Blocked (L.mem s (stA y)) := by rw [hds]; exact Or.inr (Or.inr rfl)
  obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
  have hyA := hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := notification.ntfn_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq (WP.spec_and (notification.ntfn_dequeue.rel s n y _ hT hE hq
    List.mem_cons_self) (notification.ntfn_dequeue.foot s n y _ hT hE hq List.mem_cons_self))) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, ⟨hq1, hst1⟩, w1⟩
  have hnd := hq.nodup
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_NTFN := by
    rw [stA_eq, f1 y hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
  have iq1 : L.mem s1 (inqA y) = L.mem s (inqA y) := by
    rw [inqA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {n} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (WP.spec_and (sts_all s1 y _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_restart restart_ne
    (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1, r3, r6]; decide))
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 y _ h1 hdT)) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, fw2⟩
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s2 y h2' hB2 hX2 hS2 hSg2 hdT)
    (notification.unblock_sporadic.kw (Es := ∅) s2 y h2' hX2 hS2 hdT)) ?_
  rintro s3 ⟨⟨h3, hB3, hX3, hS3, hSg3, -, -, -, fk3, -⟩, fw3⟩
  have st3 : L.mem s3 (stA y) = sched.TS_RESTART := by
    rw [stA_eq, fk3 y hdT _ (by simp) (by simp), ← stA_eq]; exact st2
  have esc3 : L.mem s3 (scA y) = L.mem s (scA y) := by
    rw [scA_eq, fk3 y hdT _ (by simp) (by simp), ← scA_eq, k2.scf hdT, scA_eq,
      f1 y hdT _ (by simp) (by simp) (by simp) (by simp)]
  refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s3 y Q R h3 hB3 hSg3 hdT
    (by rw [st3]; exact runnable_restart) (by rw [esc3]; exact hyA))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 y h3 hdT)) ?_
  rintro s4 ⟨⟨p4, -, -⟩, fw4⟩
  have f14 : Foot st T Cs Sg Scs Z ∅ s1 s4 := fw2.trans (fw3.trans fw4)
  obtain ⟨eh, et⟩ := f14.epQ h1 hX1.1 hSg1.sub (Or.inr hH)
  refine (WP.spec_ok _).2 ⟨s4, next, rfl, ⟨p4.inv, p4.bnd, hX3.fr p4.fr, hS3.fr p4.fr, hSg3.fr p4.fr⟩,
    fw1.trans (f14.mono (Set.empty_subset _)), fun hn0 => ?_⟩
  have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
  have es : L.epState s4 n = L.epState s1 n := by simp only [LawfulStore.epState, et]
  refine ⟨by rw [es, hst1, if_neg hys0, hst], ?_⟩
  rw [show (L.epQ s4 n).head = L.mem s4 (epHeadA n) from rfl, eh, show L.mem s1 (epHeadA n) = (L.epQ s1 n).head
    from rfl, hq1.head, enext, hnext]


/-- `reschedule_required` keeps `BlkOK`. -/
theorem sched.reschedule_required.blk (s : S) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.reschedule_required st s ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (sched.reschedule_required.schX (Sg := Sg) s Q R h0 hB hSg)
    (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s h0)) ?_
  rintro s' ⟨⟨⟨Q', R', h'⟩, hB', f, -⟩, fw⟩
  exact ⟨⟨⟨Q', R', h'⟩, hB', hX.fr f, hS.fr f, hSg.fr f⟩, fw⟩

theorem notification.cancel_all_signals_loop.blk (s0 s : S) (n t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hf : Foot st T Cs Sg Scs Z {n} s0 s)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {n} s0 s' ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {n} s0 x.1 ∧
      (x.2.1 ≠ 0#u64 → L.epState x.1 n = 1#u64 ∧ (L.epQ x.1 n).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold notification.cancel_all_signals_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cas_round (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4⟩
      exact ⟨hb4, hf1.trans hf4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
  · exact ⟨h, hf, ht⟩

/-- seL4 `cancelAllSignals`: every waiter is restarted. -/
theorem notification.cancel_all_signals.blk (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {n} s s' ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  refine WP.spec_bind (notification.cancel_all_signals_loop.blk s s n _ _ h hH (Foot.refl _)
    (fun _ => ⟨hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.blk s1 h1) fun s2 ⟨h2, f2⟩ =>
    ⟨h2, f1.trans (f2.mono (Set.empty_subset _))⟩



/-! ## `cancel_all_ipc` -/

/-- `restart_thread_if_no_fault` on a thread in no scheduler queue, the
switch-to candidate of no core, and named by no reply object. -/
theorem endpoint.restart_thread_if_no_fault.blk {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i, _hi⟩
  split
  · refine WP.spec_bind (WP.spec_and (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref
      (hq _)) (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t _ h ht)) ?_
    rintro s1 ⟨⟨h1, hB1, hX1, hS1, hSg1, st1, k1⟩, fw1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht)
      (endpoint.unblock_sporadic.kw (Es := ∅) s1 t h1' hX1 hS1 ht)) ?_
    rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, -, -, -, fk2, -⟩, fw2⟩
    have st2 : L.mem s2 (stA t) = sched.TS_RESTART := by
      rw [stA_eq, fk2 t ht _ (by simp) (by simp), ← stA_eq]; exact st1
    have esc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
      rw [scA_eq, fk2 t ht _ (by simp) (by simp), ← scA_eq, k1.scf ht]
    refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s2 t Q R h2 hB2 hSg2 ht
      (by rw [st2]; exact runnable_restart) (by rw [esc2]; exact htA))
      (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 t h2 ht)) ?_
    rintro s3 ⟨⟨p3, -, -⟩, fw3⟩
    exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩, fw1.trans (fw2.trans fw3)⟩
  · refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t _ h ht)) ?_
    rintro s1 ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, fw1⟩
    exact ⟨⟨⟨Q, R, h1.congrX cg⟩, hB1, hX1, hS1, hSg1⟩, fw1⟩



/-- A non-idle endpoint is in the send or the receive state. -/
theorem ep_state12 {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64) :
    L.epState s e = 1#u64 ∨ L.epState s e = 2#u64 := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨k1, k2, -, -, k4, k5⟩ := hEW.2.2.2.2.2
  have hne : EQ e ≠ [] := fun h0 => hst ((k5 e he h0).1 hH)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y ∈ EQ e := by rw [hys]; exact List.mem_cons_self
  obtain ⟨hE, -, hq⟩ := hEW.1 e he
  obtain ⟨-, hbe, hbl⟩ := hEW.2.2.2.1 e he y hy
  have hyT := hq.mem y hy
  obtain ⟨c1, c2, -⟩ := k4 e he y hy
  rcases hbl with hb | hb | hb
  · exact Or.inl (c1 hb)
  · exact Or.inr (c2 hb)
  · have := k2 y hyT (by simp) hb; rw [hbe, hH] at this; cases this

/-- One round of `cancel_all_ipc`: the waiter at the head of `ep`'s queue is
dequeued, its reply unlinked (if receiving) and restarted. -/
theorem cai_round {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hst : L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) (hhd : (L.epQ s ep).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← endpoint.ep_dequeue st s ep t
      let i ← obj.Tcb.state st t s1
      let s2 ← if i = sched.TS_BLOCKED_ON_RECV then do
          let i1 ← obj.Tcb.reply_obj st t s1
          if (i1 != 0#u64) = true then ipc.reply_unlink st s1 i1 t else ok s1
        else ok s1
      let s3 ← endpoint.restart_thread_if_no_fault st s2 t
      ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next, r = .cont (s3, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
        (next ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hs1, hs2⟩ := ep_head h0 hH (w := L.epState s ep) hst rfl
  rw [hhd] at hdT hbe hs1 hs2
  have hta := hT t hdT
  obtain ⟨-, -, r3, r4, -⟩ := ts_vals
  have hsr : L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV := by
    rcases hst with e | e
    · exact Or.inl (hs1 e)
    · exact Or.inr (hs2 e)
  have hbl : Blocked (L.mem s (stA t)) := by
    rcases hsr with e | e
    · rw [e]; exact Or.inl rfl
    · rw [e]; exact Or.inr (Or.inl rfl)
  have hnrun := not_runnable_of_blocked hbl
  obtain ⟨-, -, da⟩ := blocked_out h0 hdT hnrun
  have hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p := fun c hc p hp htq => hnrun (h0.runQ c hc p hp t htq)
  have hnR : ∀ c ∈ Cs, t ∉ R c := fun c hc htr => hnrun (h0.runR c hc t htr)
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : ep ∈ E := (hEW.2.2.2.2.2.2.2.1 ep).2 (Or.inl hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 ep heE
  have hne : EQ ep ≠ [] := fun h0' => by
    have := (hEW.2.2.2.2.2.2.2.2.2.2 ep heE h0').1 hH
    rcases hst with e | e <;> rw [e] at this <;> exact absurd this (by decide)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y = t := by rw [← hhd, hq.head, hys]; rfl
  subst hy
  rw [hys] at hq
  have hnext := hq.head_next
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := endpoint.ep_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq (WP.spec_and (endpoint.ep_dequeue.rel s ep y _ hT hE hq
    List.mem_cons_self) (endpoint.ep_dequeue.foot s ep y _ hT hE hq List.mem_cons_self))) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, ⟨hq1, hst1⟩, w1⟩
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = L.mem s (stA y) := by
    rw [stA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have rp1 : L.mem s1 (replyA y) = L.mem s (replyA y) := f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {ep} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  have da1 : L.actionW s1 ≠ y := by rw [ea1]; exact da
  have hyA1 : L.mem s1 (scA y) ≠ 0#u64 → L.mem s1 (scA y) ∈ Ac := by
    have esc1 : L.mem s1 (scA y) = L.mem s (scA y) := by
      rw [scA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
    rw [esc1]; exact hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
  -- the rest of the round, from a state `s2` with a `KW ∅` footprint from `s1`
  have tail : ∀ (s2 : S), Foot st T Cs Sg Scs Z ∅ s1 s2 →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s2 s' ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
          (next' ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next') ⦄ := by
    intro s2 fw2 hr
    refine WP.spec_bind hr fun s3 ⟨hb3, fw3⟩ => ?_
    have f13 : Foot st T Cs Sg Scs Z ∅ s1 s3 := fw2.trans fw3
    obtain ⟨eh, et⟩ := f13.epQ h1 hX1.1 hSg1.sub (Or.inl hH)
    refine (WP.spec_ok _).2 ⟨s3, next, rfl, hb3, fw1.trans (f13.mono (Set.empty_subset _)), fun hn0 => ?_⟩
    have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
    have es : L.epState s3 ep = L.epState s1 ep := by simp only [LawfulStore.epState, et]
    refine ⟨by rw [es, hst1, if_neg hys0]; exact hst, ?_⟩
    rw [show (L.epQ s3 ep).head = L.mem s3 (epHeadA ep) from rfl, eh,
      show L.mem s1 (epHeadA ep) = (L.epQ s1 ep).head from rfl, hq1.head, enext, hnext]
  have cg1 : ∀ z ∈ {z : U64 | z ∈ (∅ : Set U64) ∨ z = y}, z = y := fun z hz => by simpa using hz
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · rename_i hrecv
    step with obj.Tcb.reply_obj.spec as ⟨i1, ei1⟩
    split
    · rename_i hi1
      have hi10 : i1 ≠ 0#u64 := by simpa using hi1
      have hsr1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_RECV := by rw [← ei, hrecv]
      obtain ⟨hr, hrt⟩ := hX1.2.1.recv y hdT hsr1 (by rw [← ei1]; exact hi10)
      rw [← ei1] at hr hrt
      refine WP.spec_bind (WP.spec_and (ipc.reply_unlink.inv s1 i1 y Q R h1 hdT hX1.1 hSg1.sub hr hrt
        (by rw [st1]; exact hnrun) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kw (Scs := Scs) (Es := ∅) s1 i1 y h1 hX1 hSg1.sub hr hdT)) ?_
      rintro s2 ⟨⟨h2, e2, k2, z2⟩, fw2⟩
      have hB2 := hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_inactive) (by rw [e2]; exact inactive_ne.1)
      have hclr : ∀ r ∈ Rp, L.mem s1 (rTcbA r) = y → L.mem s2 (rTcbA r) = 0#u64 := by
        intro r hr' e
        obtain ⟨-, -, b2, -⟩ := hX1.2.1.back r hr' (by rw [e]; exact fun e0 => hta.ne0 (by rw [e0]; rfl))
        rw [e, ← ei1] at b2
        rw [← b2]; exact z2
      have hX2 := hX1.keepT k2 (by rw [e2]; exact inactive_ne) hclr
      have hS2 := hS1.keepT hX1 k2
      have hSg2 : SgOK st Ω Sg s2 := ⟨hSg1.sub, fun b hb => by rw [k2.ksb]; exact hSg1.ks b hb,
        fun o h1' h2' => by rw [k2.ksb]; exact hSg1.ksΩ o h1' h2'⟩
      have da2 : L.actionW s2 ≠ y := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine tail s2 fw2 (endpoint.restart_thread_if_no_fault.blk s2 y h2 (fun z hz => ?_) hB2 hX2 hS2 hSg2 hdT
        (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
        (by rw [k2.scf hdT]; exact hyA1))
      obtain ⟨hz1, hz2⟩ := hz
      exact absurd (cg1 z hz1) hz2
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (Foot.refl _) (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 hyA1)
  · rename_i hnrecv
    have hsend : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_SEND := by
      rcases hsr with e | e
      · rw [st1, e]
      · exact absurd (by rw [ei, st1, e]) hnrecv
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    simp only [Aeneas.Std.bind_ok]
    exact tail s1 (Foot.refl _) (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1 hyA1)


theorem endpoint.cancel_all_ipc_loop.blk (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧
      (x.2.1 ≠ 0#u64 → (L.epState x.1 ep = 1#u64 ∨ L.epState x.1 ep = 2#u64) ∧ (L.epQ x.1 ep).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold endpoint.cancel_all_ipc_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cai_round (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4⟩
      exact ⟨hb4, hf1.trans hf4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
  · exact ⟨h, hf, ht⟩

/-- seL4 `cancelAllIPC`: every waiter is restarted (or made inactive, if it
has a fault). -/
theorem endpoint.cancel_all_ipc.blk (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s s' ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.blk s s ep _ _ h hH (Foot.refl _)
    (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.blk s1 h1) fun s2 ⟨h2, f2⟩ =>
    ⟨h2, f1.trans (f2.mono (Set.empty_subset _))⟩



/-! ## The notification–SC binding -/

theorem obj.Sc.ntfn.val (s : S) (c : obj.Sc) : obj.Sc.ntfn st c s ⦃ v => v = L.mem s (scNtfnA c) ⦄ := by
  unfold obj.Sc.ntfn; step*; simp_all [scNtfnA]
theorem obj.Sc.set_ntfn.wr (s : S) (c : obj.Sc) (v : U64) :
    obj.Sc.set_ntfn st c s v ⦃ s' => s' = L.wr s (scNtfnA c) v ⦄ := by
  unfold obj.Sc.set_ntfn; step*; simp_all [scNtfnA]
theorem obj.Ntfn.set_sc.wr (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_sc st n s v ⦃ s' => s' = L.wr s (ntfnScA n) v ⦄ := by
  unfold obj.Ntfn.set_sc; step*; simp_all [ntfnScA]

/-- The current SC word after a write of a word outside the TCBs and nodes. -/
theorem idleW_wr_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) : L.idleW (L.wr s a v) = L.idleW s := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
  exact L.mem_wr_ne ho.1 (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
    (fun e => out_ne_node ho h.cur hN (by rw [idle8]; omega) e.symm)

theorem cscW_wr_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) : L.cscW (L.wr s a v) = L.cscW s := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  unfold LawfulStore.cscW; rw [nodeA_wr]
  exact L.mem_wr_ne ho.1 (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
    (fun e => out_ne_node ho h.cur hN (by simp [layout.node.CUR_SC]) e.symm)

/-- The current SC word after a TCB field write. -/
theorem cscW_wr_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.cscW (L.wr s (core.num.U64.wrapping_add y K) v) = L.cscW s := by
  unfold LawfulStore.cscW; rw [nodeA_wr]
  exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8)
    (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
    (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hy (hT y hy) hK (UScalar.eq_of_val_eq e).symm)

/-- Clearing a notification's `SC` word. -/
theorem ntsc_zero_all {s : S} {n : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (ntfnScA n) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (ntfnScA n) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hP := hO.ntP n hn
  have av := ntfnScA_val hP
  have hm : ntfnScA n ∈ Ω := hSg.sub _ (hO.ntW n hn)
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := 0#u64) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.ntORp n hn r hr; omega)
    (fun c hc => by
      obtain ⟨h128, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
      rw [av, e1, e2, e3, e4, e5]; have := hO.ntOSc n hn c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.ntORp n hn r hr; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.ntORp n hn r hr; omega)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (fun c hc e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, scNtfnA_val hPc hzc]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
    (fun _ _ _ => Tz.zero)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, sporA_val hPc hzc]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega)
    (fun _ _ _ _ h => absurd (by simp) h)
    (fun c hc e => absurd e (by
      rw [av, (sc_facts hO hc).2.2.2.2.2.2.1]; have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, foot_wr (h0.omega _ hm).1 (kw_sg (hO.ntW n hn))⟩

/-- Clearing an SC's `NTFN` word. -/
theorem scn_zero_all {s : S} {c : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs)
    (hfree : ∀ n ∈ Nt, L.mem s (ntfnScA n) ≠ c) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (scNtfnA c) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (scNtfnA c) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have av := scNtfnA_val hP hz
  obtain ⟨h128, -⟩ := sc_facts hO hc
  have hm : scNtfnA c ∈ Ω := hSg.sub _ (hO.snW c hc)
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := 0#u64) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' => by
      obtain ⟨h128', e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc'
      rw [av, e1, e2, e3, e4, e5]
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.rpSc r hr c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.rpSc r hr c hc; omega)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (fun c' hc' e n hn e2 => by
      have : c' = c := by
        by_contra hne
        obtain ⟨hP', hz'⟩ := hO.sc c' hc'
        rw [av, scNtfnA_val hP' hz'] at e
        have := hO.scDisj c hc c' hc' (Ne.symm hne); have := (sc_facts hO hc').1; omega
      exact absurd (e2.trans this) (hfree n hn))
    (fun _ _ _ => Tz.zero)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (fun c' hc' => by
      obtain ⟨hP', hz'⟩ := hO.sc c' hc'
      rw [av, sporA_val hP' hz']
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; have := (sc_facts hO hc').1; omega)
    (fun _ _ _ _ h => absurd (by simp) h)
    (fun c' hc' e => absurd e (by
      obtain ⟨hP', hz'⟩ := hO.sc c' hc'
      rw [av, scReplyA_val hP' hz']
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; have := (sc_facts hO hc').1; omega))
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, foot_wr (h0.omega _ hm).1 (kw_sg (hO.snW c hc))⟩

/-- `unbind_ntfn` (seL4 `schedContext_unbindNtfn`): the SC's `TCB` word and
the current SC word are kept, and the SC's `NTFN` word ends null. -/
theorem schedcontext.unbind_ntfn.blk (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_ntfn st s c ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧
      L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.cscW s' = L.cscW s ∧
      (c ≠ 0#u64 → L.mem s' (scNtfnA c) = 0#u64) ⦄ := by
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    refine (WP.spec_ok _).2 ⟨h, Foot.refl _, rfl, rfl, fun h0 => absurd (by rw [eb] at hb; simpa using hb) h0⟩
  rename_i hb
  have hc0 : c ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hcS : c ∈ Scs := hc hc0
  step with obj.Sc.ntfn.val as ⟨j, ej⟩
  split
  · rename_i hj
    have hjN : j ∈ Nt := by rw [ej]; exact h.2.2.1.2.2.scn c hcS (by rw [← ej]; simpa using hj)
    refine WP.spec_bind (obj.Ntfn.set_sc.wr s j 0#u64) fun s1 e1 => ?_
    subst e1
    obtain ⟨h1, f1⟩ := ntsc_zero_all h hjN
    refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c 0#u64) fun s2 e2 => ?_
    subst e2
    have hX := h.2.2.1
    have hO := hX.1
    have h0 := h.1.choose_spec.choose_spec
    have hfree : ∀ n ∈ Nt, L.mem (L.wr s (ntfnScA j) 0#u64) (ntfnScA n) ≠ c := by
      intro n hn e
      rw [L.mem_wr_val (hO.ntAl j hjN) (hO.ntAl n hn)] at e
      split at e
      · exact hc0 e.symm
      rename_i hne
      have hnj : n ≠ j := fun e' => hne (by rw [e'])
      obtain ⟨-, h2⟩ := hX.2.2.nsc n hn (by rw [e]; exact hc0)
      rw [e, ← ej] at h2
      exact hnj h2.symm
    obtain ⟨h2, f2⟩ := scn_zero_all h1 hcS hfree
    obtain ⟨hP, hz⟩ := hO.sc c hcS
    obtain ⟨h128, e1, -⟩ := sc_facts hO hcS
    have av := scNtfnA_val hP hz
    have hm : scNtfnA c ∈ Ω := h.2.2.2.2.sub _ (hO.snW c hcS)
    have hmj : ntfnScA j ∈ Ω := h.2.2.2.2.sub _ (hO.ntW j hjN)
    have htc : Aligned (scTcbA c) := (h0.omega _ (h.2.2.2.2.sub _ (hO.fixW c hcS).1)).1
    refine ⟨h2, f1.trans f2, ?_, ?_, fun _ => L.mem_wr_same (h0.omega _ hm).1⟩
    · rw [L.mem_wr_ne (h0.omega _ hm).1 htc (by rw [av, e1]; omega),
        L.mem_wr_ne (hO.ntAl j hjN) htc (by
          rw [e1, ntfnScA_val (hO.ntP j hjN)]; have := hO.ntOSc j hjN c hcS; omega)]
    · rw [cscW_wr_out h1.1.choose_spec.choose_spec hm, cscW_wr_out h0 hmj]
  · rename_i hj
    refine (WP.spec_ok _).2 ⟨h, Foot.refl _, rfl, rfl, fun _ => ?_⟩
    rw [← ej]; apply UScalar.eq_of_val_eq; simpa using hj

/-- `maybe_unbind_ntfn` (seL4 `schedContext_maybeUnbindNtfn`). -/
theorem schedcontext.maybe_unbind_ntfn.blk (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  · exact WP.spec_mono (schedcontext.unbind_ntfn.blk s i h fun h0 => by
      rw [ei]; exact (h.2.2.1.2.2.nsc n hn (by rw [← ei]; exact h0)).1) fun _ hh => ⟨hh.1, hh.2.1⟩



/-- `unbind_maybe_notification`, with its footprint. -/
theorem notification.unbind_maybe_notification.blkF (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    have hT := h.1.choose_spec.choose_spec.tcbs
    have hm : ntfnBtA n ∈ Sg := (h.2.2.1.1.ntB n hn).2
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    have h1 := ntbt_all h hn Tz.zero
    have f1 : Foot st T Cs Sg Scs Z ∅ s (L.wr s (ntfnBtA n) 0#u64) :=
      foot_wr (h.1.choose_spec.choose_spec.omega _ (h.2.2.2.2.sub _ hm)).1 (kw_sg hm)
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    exact ⟨bnd_all h1 hiT fun h0 => absurd rfl h0,
      f1.trans (foot_field (K := 3368#u64) hT hiT (by simp) (by simp) (by simp) (by simp))⟩

/-! ## `finalise_cap` of an endpoint or a notification -/

/-- `finalise_cap` of an endpoint cap: `cancel_all_ipc` when final. -/
theorem fin_endpoint.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ r.2.2 = a ∧
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ Foot st T Cs Sg Scs Z {ep} s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (endpoint.cancel_all_ipc.blk s ep h hH) fun s1 ⟨h1, f1⟩ => ?_
    exact (WP.spec_ok _).2 ⟨rfl, rfl, h1, f1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, h, Foot.refl _⟩

/-- `finalise_cap` of a notification cap: the SC unbinding, the TCB
unbinding and `cancel_all_signals` when final. -/
theorem fin_ntfn.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n b0 b1 b2 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ r.2.2 = a ∧
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ Foot st T Cs Sg Scs Z {n} s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (schedcontext.maybe_unbind_ntfn.blk s n h hn) fun s1 ⟨h1, f1⟩ => ?_
    refine WP.spec_bind (notification.unbind_maybe_notification.blkF s1 n h1 hn) fun s2 ⟨h2, f2⟩ => ?_
    refine WP.spec_bind (notification.cancel_all_signals.blk s2 n h2 hH) fun s3 ⟨h3, f3⟩ => ?_
    exact (WP.spec_ok _).2 ⟨rfl, rfl, h3, (f1.trans f2).mono (Set.empty_subset _) |>.trans f3⟩
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, h, Foot.refl _⟩



/-! ## Footprints of `cancel_ipc` -/

/-- The heap's endpoints and notifications. -/
def EH (H : Heap) : Set U64 := {e | H e = some .ep ∨ H e = some .ntfn}

/-- An aligned frame word. -/
theorem foot_sgw {s : S} {a v : U64} {Es : Set U64} (ha : Aligned a) (hm : a ∈ Sg) :
    Foot st T Cs Sg Scs Z Es s (L.wr s a v) := foot_wr ha (kw_sg hm)

theorem rp_aligned {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) :
    Aligned (rTcbA r) ∧ Aligned (rPrevA r) ∧ Aligned (rNextA r) := by
  have hp := hO.rp r hr
  refine ⟨?_, ?_, ?_⟩ <;> unfold Aligned
  · rw [rTcbA_val hp]; omega
  · rw [rPrevA_val hp]; omega
  · rw [rNextA_val hp]; omega

theorem screp_aligned {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) : Aligned (scReplyA c) := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have := (sc_lo hP hz).1
  unfold Aligned; rw [scReplyA_val hP hz]; omega

/-- `set_thread_state`, from the placement facts alone. -/
theorem sched.set_thread_state.kwP {Es : Set U64} (s : S) (t : obj.Tcb) (v : U64) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ t
    (by rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hc)) fun s2 f2 => ?_
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
  exact f1.trans f2

theorem ipc.reply_unlink.kwP {Es : Set U64} (s : S) (r t : U64) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hr : r ∈ Rp)
    (ht : t ∈ T) : ipc.reply_unlink st s r t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (rTcbA r) 0#u64) := foot_sgw (rp_aligned hO hr).1 (hO.tcbW hr)
  exact WP.spec_mono (sched.set_thread_state.kwP _ t _ hT (f1.curN hN) (by rw [f1.2.1]; exact hc) ht)
    fun s2 f2 => f1.trans f2

/-- The dequeue of a blocked thread from the object it is blocked on. -/
theorem dequeue_blocked_kw {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t)))
    (deq : S → U64 → obj.Tcb → Result S)
    (hfoot : ∀ (xs : List U64), EpPlaced T (L.mem s (blockA t)) →
      QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) xs → t ∈ xs →
      deq s (L.mem s (blockA t)) t ⦃ s' => WritesIn st s s' (EpFoot xs (L.mem s (blockA t))) ⦄) :
    deq s (L.mem s (blockA t)) t ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  obtain ⟨he, hmem⟩ := hEW.2.2.2.2.1 t ht htX hb
  obtain ⟨hE, -, hq⟩ := hEW.1 _ he
  have hH : L.mem s (blockA t) ∈ EH H := (hEW.2.2.2.2.2.2.2.1 _).1 he
  exact WP.spec_mono (hfoot _ hE hq hmem) fun s' w => Foot.of w fun b hb => hb.kw hq.mem hH

/-- `reply_remove_tcb`. -/
theorem ipc.reply_remove_tcb.kw {Es : Set U64} (s : S) (t : obj.Tcb) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hR : ReplyT st Rp Scs s t) (ht : t ∈ T) :
    ipc.reply_remove_tcb st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨hi, -, hn, hp⟩ := hR
  unfold ipc.reply_remove_tcb
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  step with obj.Reply.next.spec as ⟨next, enext⟩
  step with obj.Reply.prev.spec as ⟨prev, eprev⟩
  rw [← ei] at hi hn hp
  rw [← enext] at hn
  rw [← eprev] at hp
  refine WP.spec_bind (Pₘ := fun s1 => Foot st T Cs Sg Scs Z Es s s1) ?_ ?_
  · split
    · rename_i hne
      have hn0 : next ≠ 0#u64 := by simpa using hne
      step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
      split
      · rename_i hb
        have hS := (hn hn0).1 (by rw [← eb]; exact hb)
        exact WP.spec_mono (obj.Sc.set_reply.spec s next 0#u64) fun s1 e1 => by
          subst e1; exact foot_sgw (screp_aligned hO hS) (hO.repW _ hS)
      · rename_i hb
        have hRp := (hn hn0).2 (by rw [← eb]; simpa using hb)
        exact WP.spec_mono (obj.Reply.set_prev.spec s next 0#u64) fun s1 hs1 => by
          obtain ⟨w, e1, -⟩ := hs1; subst e1; exact foot_sgw (rp_aligned hO hRp).2.1 (hO.prevW hRp)
    · exact (WP.spec_ok _).2 (Foot.refl _)
  intro s1 f1
  refine WP.spec_bind (Pₘ := fun s2 => Foot st T Cs Sg Scs Z Es s s2) ?_ ?_
  · split
    · rename_i hne
      have hRp := hp (by simpa using hne)
      exact WP.spec_mono (obj.Reply.set_next.spec s1 prev 0#u64) fun s2 hs2 => by
        obtain ⟨w, e2, -⟩ := hs2; subst e2; exact f1.trans (foot_sgw (rp_aligned hO hRp).2.2 (hO.nextW hRp))
    · exact (WP.spec_ok _).2 f1
  intro s2 f2
  refine WP.spec_bind (obj.Reply.set_prev.spec s2 i 0#u64) fun s3 hs3 => ?_
  obtain ⟨w3, e3, -⟩ := hs3
  subst e3
  refine WP.spec_bind (obj.Reply.set_next.spec _ i 0#u64) fun s4 hs4 => ?_
  obtain ⟨w4, e4, -⟩ := hs4
  subst e4
  have f4 := (f2.trans (foot_sgw (v := w3) (rp_aligned hO hi).2.1 (hO.prevW hi))).trans
    (foot_sgw (v := w4) (rp_aligned hO hi).2.2 (hO.nextW hi))
  exact WP.spec_mono (ipc.reply_unlink.kwP _ i t hT (f4.curN hN) (by rw [f4.2.1]; exact hc) hO.ksb hi ht)
    fun s5 f5 => f4.trans f5

/-- seL4 `cancelIPC`: its footprint. -/
theorem ipc.cancel_ipc.kw {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 → L.mem s (replyA t) ∈ Rp) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  unfold ipc.cancel_ipc
  refine WP.spec_bind (WP.spec_and (faults.clear_fault.inv s t Q R h ht hO hsub)
    (WP.spec_mono (obj.Tcb.set_fault_type.spec s t _) fun s' e => e)) ?_
  rintro s1 ⟨⟨h1, f1, o1, -, -⟩, e1⟩
  have fw1 : Foot st T Cs Sg Scs Z (EH H) s s1 := by
    rw [e1]; exact foot_field (K := 3376#u64) hT ht (by simp) (by simp) (by simp) (by simp)
  have hO1 : ObjsOK st Ω Sg Rp Scs Nt Z s1 := hO.ksb
  have st1 : L.mem s1 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  -- the endpoint branch, from `s1`
  have rp1 : L.mem s1 (replyA t) = L.mem s (replyA t) := f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have epb : Blocked (L.mem s1 (stA t)) → ∀ rcv : Prop, ∀ _ : Decidable rcv,
      (rcv → L.mem s1 (stA t) = sched.TS_BLOCKED_ON_RECV) →
      (do
        let ep ← obj.Tcb.block_obj st t s1
        let s2 ← endpoint.ep_dequeue st s1 ep t
        let s3 ← if rcv then do
            let i ← obj.Tcb.reply_obj st t s2
            if (i != 0#u64) = true then ipc.reply_unlink st s2 i t else ok s2
          else ok s2
        let s4 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
        ok (s4, a)) ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
    intro hb rcv _ hrcv1
    step with obj.Tcb.block_obj.spec as ⟨ep, ep_post⟩
    subst ep_post
    refine WP.spec_bind (WP.spec_and (endpoint.ep_dequeue.inv s1 t Q R h1 ht (by simp) hb)
      (dequeue_blocked_kw (Sg := Sg) (Scs := Scs) (Z := Z) s1 t h1 ht (by simp) hb (endpoint.ep_dequeue st)
        (fun xs hE hq hm => endpoint.ep_dequeue.foot s1 _ t xs hT hE hq hm))) ?_
    rintro s2 ⟨⟨-, f2, -⟩, fw2⟩
    have hN2 := fw2.curN (h1.nodes _ h1.cur)
    have hc2 : L.cpu s2 ∈ Cs := by rw [fw2.2.1]; exact h1.cur
    refine WP.spec_bind (Pₘ := fun s3 => Foot st T Cs Sg Scs Z (EH H) s s3) ?_ ?_
    · split
      · step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
        split
        · rename_i hrc hi
          have hi0 : i ≠ 0#u64 := by simpa using hi
          have rp2 : L.mem s2 (replyA t) = L.mem s (replyA t) :=
            (f2 t ht _ (by simp) (by simp) (by simp) (by simp)).trans rp1
          have hiR : i ∈ Rp := by
            rw [ei, rp2]; exact hrecv (by rw [← st1]; exact hrcv1 hrc) (by rw [← rp2, ← ei]; exact hi0)
          exact WP.spec_mono (ipc.reply_unlink.kwP s2 i t hT hN2 hc2 hO.ksb hiR ht) fun s3 fw3 =>
            fw1.trans (fw2.trans fw3)
        · exact (WP.spec_ok _).2 (fw1.trans fw2)
      · exact (WP.spec_ok _).2 (fw1.trans fw2)
    intro s3 fw3
    refine WP.spec_bind (sched.set_thread_state.kwP (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ hT
      (fw3.curN (h.nodes _ h.cur)) (by rw [fw3.2.1]; exact h.cur) ht) fun s4 fw4 => ?_
    exact (WP.spec_ok _).2 (fw3.trans fw4)
  obtain ⟨-, -, r3, r4, r6⟩ := ts_vals
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hsd
    exact epb (by rw [← ev, hsd]; exact Or.inl rfl) _ _ (fun e => by rw [← ev]; exact e)
  split
  · rename_i _ hrv
    have := epb (by rw [← ev, hrv]; exact Or.inr (Or.inl rfl)) True instDecidableTrue
      (fun _ => by rw [← ev]; exact hrv)
    simp only [ite_true] at this
    exact this
  split
  · rename_i _ _ hnt
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← ev, hnt]; exact Or.inr (Or.inr rfl)
    step with obj.Tcb.block_obj.spec as ⟨n, en⟩
    subst en
    refine WP.spec_bind (Pₘ := fun s3 => Foot st T Cs Sg Scs Z (EH H) s s3) ?_
      (fun s3 f3 => (WP.spec_ok _).2 f3)
    unfold notification.cancel_signal
    refine WP.spec_bind (WP.spec_and (notification.ntfn_dequeue.inv s1 t Q R h1 ht (by simp) hb)
      (dequeue_blocked_kw (Sg := Sg) (Scs := Scs) (Z := Z) s1 t h1 ht (by simp) hb (notification.ntfn_dequeue st)
        (fun xs hE hq hm => notification.ntfn_dequeue.foot s1 _ t xs hT hE hq hm))) ?_
    rintro s2 ⟨-, fw2⟩
    exact WP.spec_mono (sched.set_thread_state.kwP (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 t _ hT
      (fw2.curN (h1.nodes _ h1.cur)) (by rw [fw2.2.1]; exact h1.cur) ht) fun s3 fw3 =>
      fw1.trans (fw2.trans fw3)
  split
  · rename_i _ _ _ hrp
    have hR1 : ReplyT st Rp Scs s1 t :=
      (hreply (by rw [← st1, ← ev, hrp])).transport hO rp1 (fun b hb => o1 b (hsub b hb))
    refine WP.spec_bind (ipc.reply_remove_tcb.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 t hT
      (h1.nodes _ h1.cur) h1.cur hO1 hR1 ht) fun s2 fw2 => ?_
    exact (WP.spec_ok _).2 (fw1.trans fw2)
  · exact (WP.spec_ok _).2 fw1



/-- seL4 `suspend`: its footprint. -/
theorem sched.suspend.kw {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    sched.suspend st ar s a t ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  obtain ⟨hO, hR, hE⟩ := hX
  have hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  unfold sched.suspend
  refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a t Q R h ht hB ⟨hO, hR, hE⟩ hsub)
    (ipc.cancel_ipc.kw (Sg := Sg) (Scs := Scs) (Z := Z) s a t h ht hO hsub hreply (fun h1 h2 => (hR.recv t ht h1 h2).1))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, -, hX1, -, -, -, k1, -⟩, fw1⟩
  try simp only [WP.uncurry'_pair]
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧
      L.mem s2 (yieldA t) = L.mem s1 (yieldA t) ∧ Foot st T Cs Sg Scs Z (EH H) s s2) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, -⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      exact ⟨h2, f2 _ (by simp) (by simp) (by simp),
        fw1.trans (foot_field (K := 392#u64) hT ht (by simp) (by simp) (by simp) (by simp))⟩
    · exact (WP.spec_ok _).2 ⟨h1, rfl, fw1⟩
  rintro s2 ⟨h2, y2, fw2⟩
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, -⟩
  have fw3 : Foot st T Cs Sg Scs Z (EH H) s2 s3 :=
    Foot.of hw3 fun b hb => hb.kw hW2 hc2 h2.cur ht (fun o ho => by omega)
  have y3 : L.mem s3 (yieldA t) = L.mem s2 (yieldA t) :=
    field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht (K := 3472#u64) (by simp) (by simp) (by simp)
      (fun _ => by simp)
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t _ R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨-, hw4, -⟩
  have fw4 : Foot st T Cs Sg Scs Z (EH H) s3 s4 :=
    Foot.of hw4 fun b hb => hb.kw hW3 hc3 h3.cur ht (fun o ho => by unfold RelOffs at ho; omega)
  have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) :=
    (field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht (K := 3472#u64) (by simp) (by simp) (by simp)
      (fun _ => by simp)).trans (y3.trans (y2.trans y1))
  have f04 := fw2.trans (fw3.trans fw4)
  have hN4 := f04.curN (h.nodes _ h.cur)
  have hc4 : L.cpu s4 ∈ Cs := by rw [f04.2.1]; exact h.cur
  refine WP.spec_bind (Pₘ := fun s5 => Foot st T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · unfold schedcontext.cancel_yield_to
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · exact (WP.spec_ok _).2 f04
    step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
    split
    · rename_i _ hy
      have hyS : yt ∈ Scs := by
        rw [yt_post, y4]; exact hE.yt.2.1 t ht (by rw [← y4, ← yt_post]; simpa using hy)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      have f5 : Foot st T Cs Sg Scs Z (EH H) s4 (L.wr s4 (scYieldFromA yt) 0#u64) :=
        foot_sgw (h3.omega _ (hsub _ (hO.syW yt hyS))).1 (hO.syW yt hyS)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      exact (f04.trans f5).trans (by
        rw [show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl]
        exact foot_field hT ht (by simp) (by simp) (by simp) (by simp))
    · exact (WP.spec_ok _).2 f04
  intro s5 f5
  refine WP.spec_bind (sched.set_thread_state.kwP (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s5 t _ hT
    (f5.curN (h.nodes _ h.cur)) (by rw [f5.2.1]; exact h.cur) ht) fun s6 f6 => ?_
  exact (WP.spec_ok _).2 (f5.trans f6)



/-- seL4 `suspend`: the invariants and the footprint. -/
theorem sched.suspend.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hna : L.actionW s ≠ t) :
    sched.suspend st ar s a t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (sched.suspend.tinv s a t ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ ht hna
    (hX.2.2.yt.2.1 t ht)) (sched.suspend.kw s a t h0 ht hB hX hSg.sub)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact hr

/-- `remote_tcb_stall`: the invariants and the footprint. -/
theorem smp.remote_tcb_stall.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z ∅ s s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      L.idleW s' = L.idleW s ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (smp.remote_tcb_stall.all hA s a t h0 hB hX hS hSg)
    (smp.remote_tcb_stall.spec hA s a t)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨⟨h1, hB1, hX1, hS1, hSg1, ea, ec, ei, -⟩, e⟩ := hr
  refine ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, ?_, ea, ec, ei⟩
  rcases e with rfl | ⟨v, rfl⟩
  · exact Foot.refl _
  · have ip : layout.node.IPI_PENDING.val = 120 := by simp [layout.node.IPI_PENDING]
    exact foot_node (h0.nodes _ h0.cur) h0.cur (by rw [ip]; omega) (by rw [ip]) (by rw [ip]; omega)

/-- `unbind_notification`, with its footprint. -/
theorem notification.unbind_notification.blkF (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    notification.unbind_notification st s t ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold notification.unbind_notification
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s t) fun i ei => ?_
  split
  · rename_i hi
    have hi0 : L.mem s (boundA t) ≠ 0#u64 := by rw [← ei]; simpa using hi
    have hin : i ∈ Nt := by rw [ei]; exact h.2.2.1.2.2.bnd t ht hi0
    have hm : ntfnBtA i ∈ Sg := (h.2.2.1.1.ntB i hin).2
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s i 0#u64) fun s1 e1 => ?_
    subst e1
    have f1 : Foot st T Cs Sg Scs Z ∅ s (L.wr s (ntfnBtA i) 0#u64) :=
      foot_wr (h.1.choose_spec.choose_spec.omega _ (h.2.2.2.2.sub _ hm)).1 (kw_sg hm)
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t 0#u64) fun s2 e2 => ?_
    subst e2
    have h0 := h.1.choose_spec.choose_spec
    exact ⟨bnd_all (ntbt_all h hin Tz.zero) ht fun h0 => absurd rfl h0,
      f1.trans (foot_field (K := 3368#u64) hT ht (by simp) (by simp) (by simp) (by simp)),
      (ani_out (v := 0#u64) (h0.nodes _ h0.cur) h0.cur (h0.omega _ (h.2.2.2.2.sub _ hm))).trans
        (ani_field (K := 3368#u64) hT (by rw [LawfulStore.cpu_wr]; exact (h0.nodes _ h0.cur).ksb (L.ksb_wr _ _ _))
          ht (by simp) (by simp))⟩
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _⟩



/-! ## Unbinding an SC from its thread -/

/-- Clearing an SC's `TCB` word when no thread is bound to it (`TSc` may fail
for that SC before the write). -/
theorem sctcb_zero_all {s : S} {c0 : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h0 : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv0 st T Cs Ω Sg Rp Scs Nt Z s)
    (htx : TScX st Scs c0 s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc0 : c0 ∈ Scs)
    (hnb : ∀ y ∈ T, L.mem s (scA y) ≠ c0) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (scTcbA c0) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (scTcbA c0) 0#u64) ∧ ANI st s (L.wr s (scTcbA c0) 0#u64) := by
  have hO := hX.1
  have hm : scTcbA c0 ∈ Ω := hSg.sub _ (hO.fixW c0 hc0).1
  have ho := h0.omega _ hm
  have hN' := h0.nodes _ h0.cur
  obtain ⟨h128, e1, -, e3, e4, e5, -⟩ := sc_facts hO hc0
  refine ⟨⟨⟨Q, R, inv_of_free h0 ((writesIn_wr (v := 0#u64) ho.1).mono fun b hb => hb ▸ Or.inl hm)⟩,
    BoundInv.owr h0 hB hm, (XInv.set_sctcb h0 hX hSg.sub hc0 hnb (fun h0' => absurd rfl h0') (fun e => absurd e.symm (idle_ne0 h0))).x
      ((TScX.set_sctcb h0 hO hSg.sub hc0 htx hX.2.2.yt.1).full fun h0' => absurd (L.mem_wr_same ho.1) h0'),
    SCsOK.wr' h0 hS hO ho.1 (fun y hy => (out_ne_field (K := 3464#u64) ho hy (h0.tcbs y hy) (by simp)).symm)
      (out_ne_node ho h0.cur hN' (by simp [layout.node.CUR_SC])).symm (fun c hc => ?_)
      (scw_ne_spor hO hc0 e1 (by omega) (by omega))
      (fun c hc e => absurd e (scw_ne_screp hO hc0 e1 (by omega) (by omega) c hc)),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    foot_wr ho.1 (kw_sg (hO.fixW c0 hc0).1), ani_out hN' h0.cur ho⟩
  obtain ⟨h128', -, -, f3, f4, f5, -⟩ := sc_facts hO hc
  rw [e1, f3, f4, f5]
  by_cases e : c0 = c
  · subst e; omega
  · have := hO.scDisj c0 hc0 c hc e; omega

/-- seL4 `schedContext_unbindTCB`: the thread named by the SC, if any, leaves
the scheduler queues and loses its SC; when it is the current thread a
reschedule is requested.  The scheduler action must not name it otherwise. -/
theorem schedcontext.unbind_tcb.blk (s : S) (sc : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (hna : L.mem s (scTcbA sc) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA sc))
    (hidle : L.mem s (scTcbA sc) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.unbind_tcb st s sc ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) ∧ L.idleW s' = L.idleW s ∧
      L.mem s' (scTcbA sc) = 0#u64 ∧ L.cscW s' = L.cscW s ⦄ := by
  unfold schedcontext.unbind_tcb
  step with obj.Sc.tcb.spec as ⟨t, et⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    refine (WP.spec_ok _).2 ⟨h, Foot.refl _, Or.inl rfl, rfl, ?_, rfl⟩
    rw [← et]; rw [eb] at hb; simpa using hb
  rename_i hb
  have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have htT : t ∈ T := by rw [et]; exact h.2.2.1.2.2.yt.1 sc hsc (by rw [← et]; exact ht0)
  have hna0 : L.actionW s ≠ t := by rw [et]; exact hna (by rw [← et]; exact ht0)
  have hid0 : L.idleW s ≠ t := by rw [et]; exact hidle (by rw [← et]; exact ht0)
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b1, eb1⟩
  -- the reschedule, when `t` is current
  refine WP.spec_bind (Pₘ := fun s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ Foot st T Cs Sg Scs Z ∅ s s1 ∧
      L.actionW s1 ≠ t ∧ (L.curW s1 = t → L.actionW s1 ≠ 0#u64) ∧ L.idleW s1 = L.idleW s ∧
      L.mem s1 (scTcbA sc) = L.mem s (scTcbA sc) ∧ (L.actionW s1 = L.actionW s ∨ L.actionW s1 = 1#u64) ∧
      L.cscW s1 = L.cscW s) ?_ ?_
  · split
    · rename_i hbt
      obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
      refine WP.spec_mono (WP.spec_and (sched.reschedule_required.schX (Sg := Sg) s Q R h0 hB hSg)
        (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s h0)) ?_
      rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, f1, ea1, ec1, -, ei1, -⟩, fw1⟩
      refine ⟨⟨⟨Q1, R1, h1⟩, hB1, hX.fr f1, hS.fr f1, hSg.fr f1⟩, fw1, ?_, fun _ => by rw [ea1]; simp, ei1,
        f1.sig _ (hX.1.fixW sc hsc).1, Or.inr ea1, f1.csc⟩
      rw [ea1]; exact fun e => notT_small h0.tcbs (by simp) (e ▸ htT)
    · rename_i hbt
      have hne : t ≠ t1 := fun e => hbt (by rw [eb1, decide_eq_true_eq]; exact e)
      exact (WP.spec_ok _).2 ⟨h, Foot.refl _, hna0, fun e => absurd (by rw [et1]; exact e.symm) hne, rfl, rfl,
        Or.inl rfl, rfl⟩
  rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, fw1, na1, cr1, ei1, sc1, ac1, cs1⟩
  -- dequeue
  have hc1 := h1.aff t htT
  have hp1 := h1.prio t htT
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.sch (Sg := Sg) s1 t Q1 R1 h1 hB1 hSg1 htT)
    (sched.dequeue.foot s1 t _ h1.tcbs htT hp1 (h1.nodes _ hc1) (h1.nodes _ h1.cur) ((h1.ready _ hc1).1.rel _ hp1)
      (h1.queued t htT).1)) (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 t h1 htT)) ?_
  rintro s2 ⟨⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, ea2, ec2⟩, hw2, iq2⟩, fw2⟩
  have hW1 : ∀ w ∈ Q1 (L.mem s1 (affA t)) (L.mem s1 (prioA t)), w ∈ T := fun w hw => h1.memT hc1 hp1 hw
  obtain ⟨-, -, -, -, ei2⟩ := qfoot_keep (Sg := Sg) h1 hSg1 hW1 hc1 htT p128 hw2
  have hc2 := h2.aff t htT
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.release_remove.sch (Sg := Sg) s2 t Q2 R2 h2 hB2
      (hSg1.fr f2) htT)
    (sched.release_remove.foot s2 t _ h2.tcbs htT (h2.nodes _ hc2) (h2.nodes _ h2.cur) (h2.release _ hc2)
      (h2.released t htT).1)) (sched.release_remove.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 t h2 htT)) ?_
  rintro s3 ⟨⟨⟨⟨⟨Q3, R3, h3⟩, hB3, f3⟩, ea3, ec3, -⟩, hw3, iq3⟩, fw3⟩
  have hX3 := (hX1.fr f2).fr f3
  have hS3 := (hS1.fr f2).fr f3
  have hSg3 := (hSg1.fr f2).fr f3
  have hW3 : ∀ w ∈ R2 (L.mem s2 (affA t)), w ∈ T := fun w hw => h2.memTR hc2 hw
  -- `t` is in no queue now
  have iq3' : L.mem s3 (inqA t) = (if (L.mem s2 (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
      then L.mem s2 (inqA t) &&& ~~~sched.Q_RELEASE else L.mem s2 (inqA t)) := iq3
  have q2 : (L.mem s2 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq2]; split_ifs with e
    · exact andn_qq_qq _
    · exact not_not.1 e
  have qq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq3']; split_ifs
    · rw [andn_qr_qq]; exact q2
    · exact q2
  have qr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq3']
    split_ifs with e
    · exact andn_qr_qr _
    · exact not_not.1 e
  have na3 : L.actionW s3 ≠ t := by rw [ea3, ea2]; exact na1
  obtain ⟨-, -, -, -, ei3⟩ := qfoot_keep (Sg := Sg) h2 (hSg1.fr f2) hW3 hc2 htT prel hw3
  have id3 : L.idleW s3 ≠ t := by rw [ei3, ei2, ei1]; exact hid0
  have tc3 : L.mem s3 (scTcbA sc) = t := by
    rw [f3.sig _ (hX1.1.fixW sc hsc).1, f2.sig _ (hX1.1.fixW sc hsc).1, sc1, ← et]
  refine WP.spec_bind (obj.Tcb.set_sc.wr s3 t 0#u64) fun s4 e4 => ?_
  subst e4
  obtain ⟨k1, kB, -, k3, ktx, k4, k5, ka, kc, ki, -, -, kΩ, ks0⟩ :=
    clear_sc_state h3 hB3 hX3 hS3 hSg3 htT ⟨qq3, qr3⟩ id3
  have hB4 := kB na3 (fun e => by rw [ka, ea3, ea2]; exact cr1 (by rw [← ec2, ← ec3, ← kc]; exact e))
  have ktx' : TScX st Scs sc (L.wr s3 (scA t) 0#u64) := by
    have e : L.mem s3 (scA t) = sc := by
      have := hX3.2.2.tsc sc hsc hsc0 (by rw [tc3]; exact fun e0 => (h3.tcbs t htT).ne0 (by rw [e0]; rfl))
      rwa [tc3] at this
    rw [e] at ktx; exact ktx
  have tc4 : L.mem (L.wr s3 (scA t) 0#u64) (scTcbA sc) = t := by
    rw [kΩ _ (hSg3.sub _ (hX3.1.fixW sc hsc).1)]; exact tc3
  have fw4 : Foot st T Cs Sg Scs Z ∅ s3 (L.wr s3 (scA t) 0#u64) := by
    rw [scA_eq]; exact foot_field h3.tcbs htT (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_mono (obj.Sc.set_tcb.wr _ sc 0#u64) fun s5 e5 => ?_
  subst e5
  obtain ⟨hb5, fw5, an5⟩ := sctcb_zero_all k1 hB4 k3 ktx' k4 k5 hsc fun y hy e => by
    by_cases eyt : y = t
    · subst eyt; rw [ks0] at e; exact hsc0 e.symm
    · have := (k3.2.2.bound y hy (by rw [e]; exact hsc0)).2.1
      rw [e, tc4] at this; exact eyt this.symm
  refine ⟨hb5, fw1.trans (fw2.trans (fw3.trans (fw4.trans fw5))), ?_, by rw [an5.2.1, ki, ei3, ei2, ei1],
    L.mem_wr_same (k3.1.aligned k1.tcbs (Or.inr (Or.inl ⟨sc, hsc, Or.inl rfl⟩))), ?_⟩
  · rw [an5.1, ka, ea3, ea2]; exact ac1
  · rw [cscW_wr_out k1 (hSg3.sub _ (hX3.1.fixW sc hsc).1), scA_eq,
      cscW_wr_field h3.tcbs (h3.nodes _ h3.cur) htT (by simp) (by simp), f3.csc, f2.csc, cs1]



/-! ## Register, `CONSUMED` and yield writes -/

theorem obj.Tcb.set_reg.wrK (s : S) (t : obj.Tcb) (r v : U64) (ht : TcbAddr t) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => ∃ K : U64, K.val = 256 + 8 * r.val ∧
      s' = L.wr s (core.num.U64.wrapping_add t K) v ⦄ := by
  unfold obj.Tcb.set_reg
  step*
  subst_vars
  have := ht.fits
  have hK : (core.num.U64.wrapping_add 256#u64 (core.num.U64.wrapping_mul r 8#u64)).val = 256 + 8 * r.val := by
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine ⟨core.num.U64.wrapping_add 256#u64 (core.num.U64.wrapping_mul r 8#u64), hK, ?_⟩
  congr 1
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
    layout.tcb.REGS] at hK ⊢
  omega

/-- A write of a register word of a TCB. -/
theorem regW_all {s : S} {t K v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hK : 256 ≤ K.val) (hK' : K.val < 3328) (hK8 : K.val % 8 = 0) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      ANI st s (L.wr s (core.num.U64.wrapping_add t K) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨b1, b2⟩ := bx_field (K := K) (v := v) h0 hB hX hSg.sub ht (by omega) hK8 (by omega) (by omega)
  exact ⟨⟨⟨Q, R, inv_wr_field h0 ht (by omega) hK8 (by omega)⟩, b1, b2,
    SCsOK.field h0 hS hX ht (by omega) hK8 (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    foot_field h0.tcbs ht (by omega) (by omega) hK8 (by omega), ani_field h0.tcbs (h0.nodes _ h0.cur) ht (by omega) hK8⟩

/-- A write of an SC's `CONSUMED` word. -/
theorem consumedW_all {s : S} {c v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) ∧
      ANI st s (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add c layout.sc.CONSUMED) := by unfold Aligned; rw [hv, hcv]; omega
  have hin : InSC c (Z c) (core.num.U64.wrapping_add c layout.sc.CONSUMED) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  have hm := hO.scW c hc _ hal hin
  have ho := h0.omega _ hm
  obtain ⟨h1, hB1, hX1, hSg1, -⟩ := ring_bx h0 hB hX hSg hc ((writesIn_wr (v := v) hal).mono fun b hb => Or.inr hb)
  refine ⟨⟨⟨Q, R, h1⟩, hB1, hX1, SCsOK.wr h0 hS hX hal
    (fun y hy => (out_ne_field (K := 3464#u64) ho hy (h0.tcbs y hy) (by simp)).symm)
    (out_ne_node ho h0.cur (h0.nodes _ h0.cur) (by simp [layout.node.CUR_SC])).symm (fun c' hc' => ?_)
    (scw_ne_spor hO hc (o := 8) (by rw [hv, hcv]) (by omega) (by omega))
    (fun c' hc' e => absurd e (scw_ne_screp hO hc (o := 8) (by rw [hv, hcv]) (by omega) (by omega) c' hc')), hSg1⟩,
    foot_wr hal (kw_sc hc hin), ani_out (h0.nodes _ h0.cur) h0.cur ho⟩
  obtain ⟨h128', -, -, f3, f4, f5, -⟩ := sc_facts hO hc'
  rw [hv, f3, f4, f5, hcv]
  by_cases e : c = c'
  · subst e; omega
  · have := hO.scDisj c hc c' hc' e; omega

theorem obj.Sc.set_consumed.spec' (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_consumed st sc s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add sc layout.sc.CONSUMED) v ⦄ :=
  obj.Sc.set_consumed.spec s sc v

/-- `update_consumed`. -/
theorem schedcontext.update_consumed.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ Foot st T Cs Sg Scs Z ∅ s r.2 ∧ ANI st s r.2 ⦄ := by
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    refine WP.spec_bind (hA.ticks_to_us a _) fun i _ => ?_
    exact (WP.spec_ok _).2 (consumedW_all h hc)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_bind (hA.ticks_to_us a _) fun i _ => ?_
    exact (WP.spec_ok _).2 (consumedW_all h hc)

theorem regW_spec {s : S} {t r v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧
      ANI st s s' ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (h.1.choose_spec.choose_spec.tcbs t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e; exact regW_all h ht (by omega) (by omega) (by omega)

/-- `set_consumed` with the message write. -/
theorem schedcontext.set_consumed.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (c t : U64) (wm : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (ht : t ∈ T) :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ⦄ := by
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.blk hA s a c h hc) ?_
  rintro ⟨x, s1⟩ ⟨h1, f1, n1⟩
  simp only at h1 f1 n1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true t L.total) fun buf _ => ?_
    refine WP.spec_bind (regW_spec h1 ht (r := layout.reg.BADGE) (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s2 ⟨h2, f2, n2⟩ => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧
        Foot st T Cs Sg Scs Z ∅ s2 r.2 ∧ ANI st s2 r.2) ?_ ?_
    · refine WP.spec_bind (regW_spec h2 ht (r := layout.reg.R10) (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ ⟨h3, f3, n3⟩
    simp only at h3 f3 n3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
    refine WP.spec_mono (regW_spec h3 ht (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 ⟨h4, f4, n4⟩ => ⟨h4, f1.trans (f2.trans (f3.trans f4)), n1.trans (n2.trans (n3.trans n4))⟩
  · exact (WP.spec_ok _).2 ⟨h1, f1, n1⟩



/-- `cancel_yield_to`: the yield link of `t` is cleared on both sides. -/
theorem schedcontext.cancel_yield_to.blk (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    schedcontext.cancel_yield_to st s t ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ⦄ := by
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _⟩
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  split
  · rename_i _ hy
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
    have hT := h0.tcbs
    have hta := hT t ht
    have hO := hX.1
    have hsub := hSg.sub
    have hyS : yt ∈ Scs := by
      rw [yt_post]; exact hX.2.2.yt.2.1 t ht (by rw [← yt_post]; simpa using hy)
    have hm : scYieldFromA yt ∈ Ω := hsub _ (hO.syW yt hyS)
    have ho := h0.omega _ hm
    obtain ⟨-, -, -, -, -, -, -, e56⟩ := sc_facts hO hyS
    step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
    subst s5_post
    have h5 : SchedQueuesInv st T Cs Ω H (L.wr s (scYieldFromA yt) 0#u64) Q R :=
      inv_of_free h0 ((writesIn_wr (v := 0#u64) ho.1).mono fun b hb => hb ▸ Or.inl hm)
    have tmA : TmFr st T Cs Nt s (L.wr s (scYieldFromA yt) 0#u64) :=
      TmFr.wr hT h0.nodes hO ho.1 (notTmW_omega hT h0.nodes ho
        (fun n hn e => by
          rw [show scYieldFromA yt = core.num.U64.wrapping_add yt layout.sc.YIELD_FROM from rfl, e56,
            ntfnBtA_val (hO.ntP n hn)] at e
          have := hO.ntOSc n hn yt hyS; have := (sc_facts hO hyS).1; omega))
    obtain ⟨hB5, -⟩ := bnd_wr (v := 0#u64) h0 hB ho.1
      (fun y hy => ⟨by rw [scA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm,
        by rw [inqA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm⟩)
      (fun o ho' => (out_ne_node ho h0.cur (h0.nodes _ h0.cur) (by omega)).symm)
      (fun y hy => by rw [stA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm)
    have hX5 := XInv.wr_yield0 h0 hX ho.1 (avoidX_scYield h0 hX hsub hyS) (hX.tn tmA)
    have hS5 := SCsOK.scword (v := 0#u64) h0 hS hX hyS (Or.inr rfl) (fun _ h0 => absurd rfl h0)
    have hSg5 : SgOK st Ω Sg (L.wr s (scYieldFromA yt) 0#u64) :=
      ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩
    have f5 : Foot st T Cs Sg Scs Z ∅ s (L.wr s (scYieldFromA yt) 0#u64) := foot_wr ho.1 (kw_sg (hO.syW yt hyS))
    refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
    subst e
    have hya : Aligned (yieldA t) := field_aligned (K := 3472#u64) hta (by simp) (by simp)
    have fne : ∀ u ∈ T, ∀ K : U64, K.val < 4096 → K.val ≠ 3472 →
        (yieldA t).val ≠ (core.num.U64.wrapping_add u K).val :=
      fun u hu K hK hne e => field_ne (K1 := 3472#u64) hta (hT u hu) (by simp) hK (fun _ => by simp; omega)
        (UScalar.eq_of_val_eq e)
    obtain ⟨hB6, -⟩ := bnd_wr (v := 0#u64) h5 hB5 hya
      (fun y hy => ⟨by rw [scA_eq]; exact fne y hy _ (by simp) (by simp),
        by rw [inqA_eq]; exact fne y hy _ (by simp) (by simp)⟩)
      (fun o ho' e => node_ne_field (h5.nodes _ h5.cur) (by omega) ht hta (K := 3472#u64) (by simp)
        (UScalar.eq_of_val_eq e).symm)
      (fun y hy => by rw [stA_eq]; exact fne _ hy _ (by simp) (by simp))
    have hX6 := XInv.wr_yield0 h5 hX5 hya (avoidX_yieldA h5 hX5 hsub ht)
      (hX5.tn_field (v := 0#u64) h5 hsub ht (K := 3472#u64) (by simp) (by simp) (by simp))
    refine ⟨⟨⟨Q, R, inv_wr_field (K := 3472#u64) h5 ht (by simp) (by simp) (by simp)⟩, hB6, hX6,
      SCsOK.field (K := 3472#u64) h5 hS5 hX5 ht (by simp) (by simp) (by simp),
      ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg5.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg5.ksΩ o h1 h2⟩⟩,
      f5.trans ?_, (ani_out (v := 0#u64) (h0.nodes _ h0.cur) h0.cur ho).trans ?_⟩
    · rw [show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl]
      exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
    · rw [show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl]
      exact ani_field hT (h5.nodes _ h5.cur) ht (by simp) (by simp)
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _⟩

/-- seL4 `completeYieldTo`. -/
theorem schedcontext.complete_yield_to.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (y : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ≠ 0#u64 → y ∈ T) :
    schedcontext.complete_yield_to st ar s a y ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ⦄ := by
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _⟩
  rename_i hb
  have hyT : y ∈ T := hy (fun e => hb (by rw [b_post, e]; rfl))
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact h.2.2.1.2.2.yt.2.1 y hyT (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (schedcontext.set_consumed.blk hA s a i y true h hiS hyT) fun s1 ⟨h1, f1, n1⟩ => ?_
    refine WP.spec_bind (schedcontext.cancel_yield_to.blk s1 y h1 hyT) fun s2 ⟨h2, f2, n2⟩ => ?_
    exact (WP.spec_ok _).2 ⟨h2, f1.trans f2, n1.trans n2⟩
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _⟩



/-! ## The debug lists -/

/-- The debug-list words: the TCBs' debug links and the nodes' list heads. -/
def DbgW (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = dnA y ∨ b = dpA y) ∨ (∃ c ∈ Cs, b = L.nodeAt s0 c layout.node.DEBUG_TCBS)

/-- A footprint inside `KW` and the debug-list words. -/
abbrev FootD (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesIn st s s' (fun b => KW st T Cs Sg Scs Z Es s b ∨ DbgW st T Cs s b)

theorem Foot.d {s s' : S} {Es : Set U64} (f : Foot st T Cs Sg Scs Z Es s s') : FootD st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono f fun _ hb => Or.inl hb

theorem FootD.trans {s₁ s₂ s₃ : S} {Es : Set U64} (h₁ : FootD st T Cs Sg Scs Z Es s₁ s₂)
    (h₂ : FootD st T Cs Sg Scs Z Es s₂ s₃) : FootD st T Cs Sg Scs Z Es s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => by
    rcases hb with hb | hb | ⟨y, hy, e⟩ | ⟨c, hc, e⟩
    · exact hb
    · exact Or.inl (KW.ksb h₁.1 hb)
    · exact Or.inr (Or.inl ⟨y, hy, e⟩)
    · exact Or.inr (Or.inr ⟨c, hc, by rw [e, nodeAt_of_ksb h₁.1]⟩)

theorem FootD.mono {s s' : S} {Es Es' : Set U64} (f : FootD st T Cs Sg Scs Z Es s s') (hE : Es ⊆ Es') :
    FootD st T Cs Sg Scs Z Es' s s' :=
  WritesIn.mono f fun _ hb => Or.elim hb (fun h => Or.inl (KW.mono h hE)) Or.inr

/-- A write of a debug link of a TCB. -/
theorem dbgF_all {s : S} {y K v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T)
    (hK : K.val = 3576 ∨ K.val = 3584) (hv : Tz T v) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      FootD st T Cs Sg Scs Z ∅ s (L.wr s (core.num.U64.wrapping_add y K) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hya := hT y hy
  have ha := field_aligned hya (K := K) (by omega) (by omega)
  obtain ⟨b1, b2⟩ := bx_field' (K := K) (v := v) h0 hB hX hSg.sub hy (by omega) (by omega) (by omega)
    ⟨hX.2.2.tm.wr_ptr hT h0.nodes hy (by omega) hv,
     hX.2.2.ntb.wr hX.1 ha (fun n hn => out_ne_field (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) hy hya (by omega))⟩
  refine ⟨⟨⟨Q, R, inv_wr_field h0 hy (by omega) (by omega) (by omega)⟩, b1, b2,
    SCsOK.field h0 hS hX hy (by omega) (by omega) (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    (writesIn_wr ha).mono fun b hb => Or.inr (Or.inl ⟨y, hy, ?_⟩)⟩
  subst hb
  rcases hK with e | e
  · left; unfold dnA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)
  · right; unfold dpA; congr; exact UScalar.eq_of_val_eq (by rw [e]; rfl)

/-- A write of a core's debug-list head. -/
theorem dbgN_all {s : S} {c v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs) (hv : Tz T v) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) ∧
      FootD st T Cs Sg Scs Z ∅ s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hN := h0.nodes c hc
  have hN' := h0.nodes _ h0.cur
  have d88 := debug_val
  have ha : Aligned (L.nodeAt s c layout.node.DEBUG_TCBS) := nodeAt_aligned hN (by omega) (by omega)
  have hw : WritesIn st s (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) (L.Free s Ω Cs) :=
    free_node_write rfl hc hN (by simp only [LowFree]; omega)
  have hcs : (L.nodeAt s c layout.node.DEBUG_TCBS).val ≠ (L.nodeA s layout.node.CUR_SC).val :=
    node_ne_node hN hN' (by omega) (by simp [layout.node.CUR_SC]) (fun _ => by rw [d88]; simp [layout.node.CUR_SC])
  have ecs : L.cscW (L.wr s (L.nodeAt s c layout.node.DEBUG_TCBS) v) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) hcs
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
  refine ⟨⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw,
    hX.writes h0.tcbs (writesIn_wr (v := v) ha) (fun b hb => hb ▸ not_prot_node h0 hX.1 hSg.sub hc (by omega))
      (by rw [ecs]; exact hX.2.2.cur)
      ⟨hX.2.2.tm.wr_node hT h0.nodes hc (by omega) hv,
       hX.2.2.ntb.wr hX.1 ha (fun n hn => out_ne_node (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) hc hN (by omega))⟩
      (by
        unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [idle8]; omega) (by rw [idle8]))
          (node_ne_node hN hN' (by omega) (by rw [idle8]; omega) (fun _ => by rw [d88, idle8]; simp))),
    SCsOK.wr h0 hS hX ha (fun y hy e => node_ne_field (o := layout.node.DEBUG_TCBS) hN (by omega) hy (hT y hy)
        (K := 3464#u64)
        (by simp) (UScalar.eq_of_val_eq (by rw [← scA_eq]; exact e))) hcs
      (fun c' hc' => ⟨fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.1) hc hN (by omega) e,
        fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.2.1) hc hN (by omega) e,
        fun e => out_ne_node (h0.omega _ (hcΩ c' hc').2.2.2.2) hc hN (by omega) e⟩)
      (fun c' hc' e => out_ne_node (h0.omega _ (spor_omega hX.1 hc')) hc hN (by omega) e)
      (fun c' hc' e => absurd e (out_ne_node (h0.omega _ (hSg.sub _ (hX.1.repW c' hc'))) hc hN (by omega))),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    (writesIn_wr ha).mono fun b hb => Or.inr (Or.inr ⟨c, hc, hb⟩)⟩

theorem obj.Tcb.debug_next.val (s : S) (t : obj.Tcb) : obj.Tcb.debug_next st t s ⦃ v => v = L.mem s (dnA t) ⦄ := by
  unfold obj.Tcb.debug_next; step*; simp_all [dnA]
theorem obj.Tcb.debug_prev.val (s : S) (t : obj.Tcb) : obj.Tcb.debug_prev st t s ⦃ v => v = L.mem s (dpA t) ⦄ := by
  unfold obj.Tcb.debug_prev; step*; simp_all [dpA]
theorem obj.Tcb.set_debug_next.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_debug_next st t s v ⦃ s' => s' = L.wr s (dnA t) v ⦄ := by
  unfold obj.Tcb.set_debug_next; step*; simp_all [dnA]
theorem obj.Tcb.set_debug_prev.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_debug_prev st t s v ⦃ s' => s' = L.wr s (dpA t) v ⦄ := by
  unfold obj.Tcb.set_debug_prev; step*; simp_all [dpA]

theorem dbg_next_all {s : S} {y v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T) (hv : Tz T v) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (dnA y) v) ∧ FootD st T Cs Sg Scs Z ∅ s (L.wr s (dnA y) v) :=
  dbgF_all (K := 3576#u64) h hy (Or.inl rfl) hv
theorem dbg_prev_all {s : S} {y v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T) (hv : Tz T v) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (dpA y) v) ∧ FootD st T Cs Sg Scs Z ∅ s (L.wr s (dpA y) v) :=
  dbgF_all (K := 3584#u64) h hy (Or.inr rfl) hv

/-- `debug_remove`: the thread leaves its core's debug list. -/
theorem objects.debug_remove.blk (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootD st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have hc : L.mem s (affA t) ∈ Cs := h.1.choose_spec.choose_spec.aff t ht
  have hTm := h.2.2.1.2.2.tm
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have tnx : Tz T nx := by rw [enx]; exact hTm.dn t ht
  have tpv : Tz T pv := by rw [epv]; exact hTm.dp t ht
  refine WP.spec_bind (Pₘ := fun s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ FootD st T Cs Sg Scs Z ∅ s s1) ?_ ?_
  · split
    · exact WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => by subst e; exact dbgN_all h hcpu tnx
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by subst e; exact dbg_next_all h hpT tnx
      · exact (WP.spec_ok _).2 ⟨h, (Foot.refl _).d⟩
  intro s1 ⟨h1, f1⟩
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ FootD st T Cs Sg Scs Z ∅ s s2) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e; obtain ⟨b, f⟩ := dbg_prev_all h1 hnT tpv; exact ⟨b, f1.trans f⟩
    · exact (WP.spec_ok _).2 ⟨h1, f1⟩
  intro s2 ⟨h2, f2⟩
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, f3⟩ := dbg_prev_all h2 ht Tz.zero
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  obtain ⟨h4, f4⟩ := dbg_next_all h3 ht Tz.zero
  exact ⟨h4, f2.trans (f3.trans f4)⟩



/-! ## `finalise_cap` of a thread -/

theorem obj.Sc.yield_from.val (s : S) (c : obj.Sc) : obj.Sc.yield_from st c s ⦃ v => v = L.mem s (scYieldFromA c) ⦄ := by
  unfold obj.Sc.yield_from; step*; simp_all [scYieldFromA]

/-- The VCPU link is an extra TCB field; native TCBs have no bound VCPU. -/
@[step] theorem vcpu.bound.spec (s : S) (t : obj.Tcb) :
    vcpu.bound st s t ⦃ v => v = L.mem s (core.num.U64.wrapping_add t 3664#u64) ⦄ := by
  unfold vcpu.bound
  step* <;> simp_all

/-- Detaching an unbound native TCB changes neither memory nor hardware. -/
theorem vcpu.detach_none {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (h0 : L.mem s (core.num.U64.wrapping_add t 3664#u64) = 0#u64) :
    vcpu.detach st ar s a t ⦃ r => r = (s, a) ⦄ := by
  unfold vcpu.detach
  step with vcpu.bound.spec
  simp_all

/-- `finalise_cap` of a final thread cap: the thread leaves every scheduler
structure, its notification, timer, SC and yield links are cut, it is
suspended and leaves its core's debug list.  The thread must not be the idle
thread nor the scheduler's switch-to candidate. -/
theorem fin_thread.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ FootD st T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 ⟨h, (Foot.refl _).d⟩
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (vcpu.detach_none ar s1 a1 p (by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0)) ?_
  intro r hr
  subst r
  try dsimp only
  refine WP.spec_bind (notification.unbind_notification.blkF s1 p h1 hp) fun s2 ⟨h2, f2, n2⟩ => ?_
  refine WP.spec_bind (timer.remove.tf (s0 := s2) s2 p ⟨h2, Foot.refl _, ANI.refl _⟩ hp) fun s3 ⟨h3, f3, n3⟩ => ?_
  have ea3 : L.actionW s3 = L.actionW s := by rw [n3.1, n2.1, ea1]
  have ei3 : L.idleW s3 = L.idleW s := by rw [n3.2.1, n2.2.1, ei1]
  have f03 : Foot st T Cs Sg Scs Z ∅ s s3 := f1.trans (f2.trans f3)
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      Foot st T Cs Sg Scs Z ∅ s r.1 ∧ L.actionW r.1 ≠ p) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, f03, by rw [ea3]; exact hna⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (schedcontext.unbind_tcb.blk s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
      (fun _ => by rw [hit, ei3]; exact hidle)) fun s5 hh5 => ?_
    obtain ⟨h5, f5, ea5, _⟩ := hh5
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, f03.trans f5, na5⟩
    · have hiS5 : i ∈ Scs := hiS
      refine WP.spec_mono (schedcontext.complete_yield_to.blk hA s5 a1 y h5 (fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0))) ?_
      rintro ⟨s6, a6⟩ ⟨h6, f6, n6⟩
      exact ⟨h6, (f03.trans f5).trans f6, by rw [n6.1]; exact na5⟩
  rintro ⟨s4, a2⟩ ⟨h4, f4, na4⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.suspend.blk s4 a2 p h4 hp na4) ?_
  rintro ⟨s5, a3⟩ ⟨h5, f5⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (objects.debug_remove.blk s5 p h5 hp) fun s6 ⟨h6, f6⟩ => ?_
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 ⟨h6, ((f4.mono (Set.empty_subset _)).trans f5).d.trans (f6.mono (Set.empty_subset _))⟩


end

end Fl4Proofs.P1
