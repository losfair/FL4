/-
P1: `cancel_badged_sends` (seL4 `cancelBadgedSends`, P3's `CancelEpHyp`)
keeps `BlkOK` with a footprint.

The loop walks the endpoint's send queue from its head; the thread it is at
is always a member of the current queue (blocked sending on the endpoint),
and the next pointer it reads is another member or null.  A matching waiter
is dequeued and restarted, which leaves every other thread's state and block
object as they were (`restart_thread_if_no_fault.oth`, through the scheduler
words `SW` that `possible_switch_to` writes).
-/
import Fl4Proofs.P1.QueueKeeps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## The scheduler words -/

/-- The scheduler's words: the threads' scheduler links and queue flags,
and the nodes' words. -/
def SW (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = nextA .Sched y ∨ b = prevA .Sched y ∨ b = inqA y) ∨
    (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ b = L.nodeAt s0 c o)

theorem SW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : SW st T Cs s1 b) : SW st T Cs s0 b := by
  rcases h with h | ⟨c, hc, o, ho, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, o, ho, by rw [e, nodeAt_of_ksb hk]⟩

theorem sw_trans {s₁ s₂ s₃ : S} (h₁ : WritesIn st s₁ s₂ (SW st T Cs s₁)) (h₂ : WritesIn st s₂ s₃ (SW st T Cs s₂)) :
    WritesIn st s₁ s₃ (SW st T Cs s₁) := (h₁.trans h₂).mono fun _ hb => hb.elim id (SW.ksb h₁.1)

/-- Writes to scheduler words keep every other TCB field. -/
theorem sw_keeps_field {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (SW st T Cs s)) :
    ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
  intro y hy K hK hK8 h1 h2 h3
  have hT := h.tcbs
  refine hw.mem_eq (field_aligned (hT y hy) hK hK8) fun hb => ?_
  rcases hb with ⟨z, hz, e | e | e⟩ | ⟨c, hc, o, ho, e⟩
  · rw [nextA_eq'] at e
    exact field_ne (hT y hy) (hT z hz) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; omega) e
  · rw [prevA_eq'] at e
    exact field_ne (hT y hy) (hT z hz) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; omega) e
  · rw [inqA_eq] at e
    exact field_ne (hT y hy) (hT z hz) hK (by simp) (fun _ => by simp; omega) e
  · exact node_ne_field (h.nodes c hc) ho hy (hT y hy) hK e.symm

theorem qfoot_sw {s : S} {W : List U64} {c t b : U64} {P : Nat → Prop} (hW : ∀ w ∈ W, w ∈ T) (hc : c ∈ Cs)
    (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (h : L.QFoot s W c P t b) : SW st T Cs s b := by
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩
  · exact Or.inl ⟨w, hW w hw, Or.inl e⟩
  · exact Or.inl ⟨w, hW w hw, Or.inr (Or.inl e)⟩
  · exact Or.inr ⟨c, hc, o, ho, e⟩
  · exact Or.inl ⟨t, ht, Or.inr (Or.inr e)⟩
  · exact Or.inr ⟨_, hcpu, o, ho, e⟩

section queues
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.enqueue.sw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => WritesIn st s s' (SW st T Cs s) ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => hh.1.mono fun b hb => qfoot_sw ?_ hc h.cur ht hb
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.set_action.sw (s : S) (v : U64) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_action st s v ⦃ s' => WritesIn st s s' (SW st T Cs s) ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e
    exact (writesIn_wr (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))).mono
      fun b e => Or.inr ⟨_, hc, _, by rw [act_val]; omega, e⟩

theorem sched.reschedule_required.sw (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => WritesIn st s s' (SW st T Cs s) ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => WritesIn st s s1 (SW st T Cs s) ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact sched.enqueue.sw s act h hT
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  exact WP.spec_mono (sched.set_action.sw s1 _ (by rw [f1.2.1]; exact (h.nodes _ h.cur).ksb f1.1)
    (by rw [f1.2.1]; exact h.cur)) fun s2 f2 => sw_trans f1 f2

theorem sched.possible_switch_to.sw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => WritesIn st s s' (SW st T Cs s) ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.sw s t h ht
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.sw s t h ht
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h) (sched.reschedule_required.sw s h)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, f1⟩
    exact WP.spec_mono (sched.enqueue.sw s1 t h1 ht) fun s2 f2 => sw_trans f1 f2
  · exact sched.set_action.sw s _ (h.nodes _ h.cur) h.cur

end queues

theorem endpoint.restart_thread_if_no_fault.oth {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' =>
      ∀ z ∈ T, z ≠ t → L.mem s' (stA z) = L.mem s (stA z) ∧ L.mem s' (blockA z) = L.mem s (blockA z) ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  have kz : ∀ {s1 : S} (k : KeepT st T Cs Rp Scs Nt t s s1) (z : U64), z ∈ T → z ≠ t →
      L.mem s1 (stA z) = L.mem s (stA z) ∧ L.mem s1 (blockA z) = L.mem s (blockA z) := fun k z hz hzt =>
    ⟨k.stf hz hzt, by rw [blockA_eq]; exact k.fld z hz _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e hzt)⟩
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i, _hi⟩
  split
  · refine WP.spec_bind (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref (hq _)) ?_
    rintro s1 ⟨h1, hB1, hX1, hS1, hSg1, st1, k1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht) ?_
    rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, -, -, -, fk2, -⟩
    refine WP.spec_mono (sched.possible_switch_to.sw s2 t h2 ht) fun s3 w3 z hz hzt => ?_
    have f3 := sw_keeps_field h2 w3
    obtain ⟨e1, e2⟩ := kz k1 z hz hzt
    refine ⟨?_, ?_⟩
    · rw [stA_eq, f3 z hz _ (by simp) (by simp) (by simp) (by simp) (by simp), fk2 z hz _ (by simp) (by simp),
        ← stA_eq]; exact e1
    · rw [blockA_eq, f3 z hz _ (by simp) (by simp) (by simp) (by simp) (by simp), fk2 z hz _ (by simp) (by simp),
        ← blockA_eq]; exact e2
  · refine WP.spec_mono (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) ?_
    rintro s1 ⟨-, -, -, -, -, -, k1⟩
    exact kz k1

theorem seg_next {m : U64 → U64} {l : tcbqueue.Link} {p n t : U64} {xs : List U64} (h : Seg m l p xs n)
    (hn : xs.Nodup) (ht : t ∈ xs) : m (nextA l t) = n ∨ (m (nextA l t) ∈ xs ∧ m (nextA l t) ≠ t) := by
  induction xs generalizing p with
  | nil => exact absurd ht List.not_mem_nil
  | cons x ys ih =>
    simp only [Seg_cons] at h
    obtain ⟨-, h2, h3⟩ := h
    have hn' := List.nodup_cons.1 hn
    rcases List.mem_cons.1 ht with rfl | hy
    · rw [h2]
      cases ys with
      | nil => exact Or.inl rfl
      | cons y ys' =>
        refine Or.inr ⟨List.mem_cons_of_mem _ List.mem_cons_self, fun e => hn'.1 ?_⟩
        simp only [List.headD_cons] at e
        rw [← e]; exact List.mem_cons_self
    · rcases ih h3 hn'.2 hy with e | ⟨hm, hne⟩
      · exact Or.inl e
      · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hne⟩

/-- The loop's invariant: `t` is null or a thread blocked sending on `ep`. -/
def CbsAt (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (ep : U64) (s : S) (t : U64) : Prop :=
  t ≠ 0#u64 → t ∈ T ∧ L.mem s (blockA t) = ep ∧ L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND

theorem endpoint.cancel_badged_sends_loop.blk (s0 s : S) (ep badge t fuel : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s)
    (ht : CbsAt st T ep s t) :
    endpoint.cancel_badged_sends_loop st s ep badge t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold endpoint.cancel_badged_sends_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧ CbsAt st T ep x.1 x.2.1)
  · rintro ⟨s1, y, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold endpoint.cancel_badged_sends_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hb
    have hy0 : y ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hdT, hbe, hsend⟩ := ht1 hy0
    split
    swap
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hfuel
    step as ⟨fuel1, efuel⟩
    -- the queue facts at `s1`
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hb1
    have hT := h0.tcbs
    have hta := hT y hdT
    obtain ⟨E, EQ, w1, w2, w5, w3, w4, ty⟩ := h0.eps
    have hbl : Blocked (L.mem s1 (stA y)) := by rw [hsend]; exact Or.inl rfl
    obtain ⟨heE, hyQ⟩ := w4 y hdT (by simp) hbl
    rw [hbe] at heE hyQ
    obtain ⟨hE, -, hq⟩ := w1 ep heE
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨next, enext⟩
    have hnext : next = 0#u64 ∨ (next ∈ EQ ep ∧ next ≠ y) := by
      rw [enext]; exact seg_next hq.seg hq.nodup hyQ
    -- the next thread's facts at `s1`
    have hN1 : CbsAt st T ep s1 next := fun hn0 => by
      rcases hnext with e | ⟨hm, -⟩
      · exact absurd e hn0
      obtain ⟨-, hbn, -⟩ := w3 ep heE next hm
      exact ⟨hq.mem next hm, hbn, by rw [ty.2.2.2.1 ep heE next hm y hyQ, hsend]⟩
    step with P0.obj.Tcb.block_badge.p0 st y s1 hST as ⟨i⟩
    split
    swap
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩, hf1, hN1, by simp only; omega⟩
    -- dequeue and restart
    have hnrun := not_runnable_of_blocked hbl
    obtain ⟨-, -, da⟩ := blocked_out h0 hdT hnrun
    have hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → y ∉ Q c p := fun c hc p hp htq => hnrun (h0.runQ c hc p hp y htq)
    have hnR : ∀ c ∈ Cs, y ∉ R c := fun c hc htr => hnrun (h0.runR c hc y htr)
    have hdq := endpoint.ep_dequeue.inv s1 y Q R h0 hdT (by simp) hbl
    rw [hbe] at hdq
    refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s1 ep y _ hT hE hq hyQ)) ?_
    rintro s2 ⟨⟨h2, f2, o2, n2, k2, c2, nc2⟩, w2'⟩
    have tm2 : TmFr st T Cs Nt s1 s2 := ⟨k2, fun y hy K a b c => f2 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc2 c hc o (by omega) (by omega), fun n' hn' => o2 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
    obtain ⟨hB2, hX2, hS2, hSg2, ea2, -, -⟩ := frame_bx h0 hB hX hS hSg f2 o2 n2 k2 tm2
    have fw2 : Foot st T Cs Sg Scs Z {ep} s1 s2 := Foot.of w2' fun b hb => hb.kw hq.mem rfl
    have st2 : L.mem s2 (stA y) = L.mem s1 (stA y) := by
      rw [stA_eq]; exact f2 y hdT _ (by simp) (by simp) (by simp) (by simp)
    have da2 : L.actionW s2 ≠ y := by rw [ea2]; exact da
    have hyA2 : L.mem s2 (scA y) ≠ 0#u64 → L.mem s2 (scA y) ∈ Ac := by
      have esc2 : L.mem s2 (scA y) = L.mem s1 (scA y) := by
        rw [scA_eq]; exact f2 y hdT _ (by simp) (by simp) (by simp) (by simp)
      rw [esc2]; exact hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
    have cg1 : ∀ z ∈ {z : U64 | z ∈ (∅ : Set U64) ∨ z = y}, z = y := fun z hz => by simpa using hz
    obtain ⟨-, -, r3, r4, -⟩ := ts_vals
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    have hsend2 : L.mem s2 (stA y) = sched.TS_BLOCKED_ON_SEND := by rw [st2, hsend]
    refine WP.spec_bind (WP.spec_and
      (endpoint.restart_thread_if_no_fault.blk s2 y h2 cg1 hB2 hX2 hS2 hSg2 hdT (Or.inl (Or.inr rfl))
        (hX2.noref hta (by rw [hsend2]; exact nrp) (by rw [hsend2]; exact nrc)) hnQ hnR da2 hyA2)
      (endpoint.restart_thread_if_no_fault.oth s2 y h2 cg1 hB2 hX2 hS2 hSg2 hdT (Or.inl (Or.inr rfl))
        (hX2.noref hta (by rw [hsend2]; exact nrp) (by rw [hsend2]; exact nrc)) hnQ hnR da2 hyA2)) ?_
    rintro s3 ⟨⟨h3, fw3⟩, oth3⟩
    refine (WP.spec_ok _).2 ⟨h3, hf1.trans (fw2.trans (fw3.mono (Set.empty_subset _))), fun hn0 => ?_,
      by simp only; omega⟩
    obtain ⟨hnT, hnb, hns⟩ := hN1 hn0
    have hny : next ≠ y := by
      rcases hnext with e | ⟨-, hne⟩
      · exact absurd e hn0
      · exact hne
    obtain ⟨o1, o2'⟩ := oth3 next hnT hny
    refine ⟨hnT, ?_, ?_⟩
    · rw [o2', blockA_eq, f2 next hnT _ (by simp) (by simp) (by simp) (by simp), ← blockA_eq]; exact hnb
    · rw [o1, stA_eq, f2 next hnT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hns
  · exact ⟨h, hf, ht⟩

/-- **seL4 `cancelBadgedSends`** (P3's `CancelEpHyp`): every waiter with the
badge is dequeued and restarted; `BlkOK` is kept, with a footprint. -/
theorem endpoint.cancel_badged_sends.blkF (s : S) (ep badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_badged_sends st s ep badge ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s s' ⦄ := by
  unfold endpoint.cancel_badged_sends
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  rename_i hsend
  have hst : L.epState s ep = 1#u64 := by
    rw [← hv]; apply UScalar.eq_of_val_eq; simpa [obj.EP_SEND] using hsend
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  obtain ⟨hd, hbe, hs1, -⟩ := ep_head h.1.choose_spec.choose_spec hH (w := 1#u64) (Or.inl rfl) hst
  refine WP.spec_bind (endpoint.cancel_badged_sends_loop.blk s s ep badge _ _ h hH (Foot.refl _)
    (fun _ => ⟨hd, hbe, hs1 rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.blk s1 h1) fun s2 ⟨h2, f2⟩ =>
    ⟨h2, f1.trans (f2.mono (Set.empty_subset _))⟩

/-! ## `timer.insert` with its footprint (P3's `SetTimerHyp`) -/

section timer
variable {s0 : S}

theorem timer.insert_fixup_loop.tf (s : S) (c z fuel : U64)
    (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) (hz : Tz T z) :
    timer.insert_fixup_loop st s c z fuel ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L2 := timer.right.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L3 := timer.parent.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L5 := timer.set_red.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L6 := timer.rotate_left.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L7 := timer.rotate_right.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L8 := timer.is_red.any (L := L)
  have L9 := tcb_eq.iff
  unfold timer.insert_fixup_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.1 ∧ Tz T x.2.1)
  · rintro ⟨s1, z1, f1⟩ ⟨h1, hz1⟩
    simp only at h1 hz1
    unfold timer.insert_fixup_loop.body
    step*
    all_goals try (
      refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2.1 ∧ Tz T r.2.2) ?_ ?_
      · split <;> step*
      rintro ⟨sa, za, pa⟩ ⟨ha, hza, hpa⟩
      simp only at ha hza hpa
      step*)
  · exact ⟨h, hz⟩

theorem timer.insert_fixup.tf (s : S) (c z : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hz : Tz T z) : timer.insert_fixup st s c z ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.insert_fixup
  refine WP.spec_bind (timer.insert_fixup_loop.tf s c z _ h hc hz) fun s1 h1 => ?_
  refine WP.spec_bind (timer.root.tzf s1 c h1 hc) fun r hr => ?_
  exact timer.set_red.tf s1 r false h1 hr

/-- **`timer.insert` with its footprint** (P3's `SetTimerHyp`): arming `t`'s
timer keeps `TInv` (`BlkOK`) and writes only footprint words (TCB timer
fields, the tree root and min words and `REPROGRAM` of the core). -/
theorem timer.insert.foot (s : S) (t d bd : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    timer.insert st s t d bd ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have htz : Tz T t := Tz.of_mem ht
  unfold timer.insert
  refine WP.spec_bind (timer.remove.tf (s0 := s) s t ⟨h, Foot.refl _, ANI.refl _⟩ ht) fun s1 h1 => ?_
  split
  · exact (WP.spec_ok _).2 ⟨h1.1, h1.2.1⟩
  refine WP.spec_bind (L.cur_cpu_spec s1) fun cpu ec => ?_
  have hc : cpu ∈ Cs := by
    obtain ⟨⟨Q, R, h0⟩, -⟩ := h1.1
    rw [ec]; exact h0.cur
  refine WP.spec_bind (timer.root.tz s1 cpu h1.1 hc) fun cur hcur => ?_
  refine WP.spec_bind (timer.insert_loop.tz s1 d 0#u64 cur false true _ h1.1 Tz.zero hcur) ?_
  rintro ⟨p, gl, fst⟩ hp
  simp only at hp
  try simp only [WP.uncurry'_pair]
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × U64 => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 ∧ r.2 = t) ?_ ?_
  · split
    · exact WP.spec_bind (timer.set_root.tf s1 cpu t h1 hc htz) fun s3 h3 => (WP.spec_ok _).2 ⟨h3, rfl⟩
    · refine WP.spec_bind (Pₘ := fun s2 => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s s2) ?_
        fun s2 h2 => (WP.spec_ok _).2 ⟨h2, rfl⟩
      split
      · exact timer.set_left.tf s1 p t h1 hp htz
      · exact timer.set_right.tf s1 p t h1 hp htz
  rintro ⟨s2, t1⟩ ⟨h2, e⟩
  simp only at h2 e
  subst t1
  try simp only [WP.uncurry'_pair]
  have hT := h2.tcbs
  have hN2 := h2.nodes _ h2.1.1.choose_spec.choose_spec.cur
  have FA : ∀ {sa : S} (K v : U64), Foot st T Cs Sg Scs Z ∅ s sa → ANI st s sa → NodePlaced st T sa (L.cpu sa) →
      192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3576 → K.val ≠ 3584 →
      Foot st T Cs Sg Scs Z ∅ s (L.wr sa (core.num.U64.wrapping_add t K) v) ∧
        ANI st s (L.wr sa (core.num.U64.wrapping_add t K) v) ∧
        NodePlaced st T (L.wr sa (core.num.U64.wrapping_add t K) v)
          (L.cpu (L.wr sa (core.num.U64.wrapping_add t K) v)) :=
    fun K v f n hN a1 a2 a3 a4 a5 => ⟨f.trans (foot_field hT ht a1 a2 a3 ⟨a4, a5⟩),
      n.trans (ani_field hT hN ht a2 a3), by rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)⟩
  have hx2 : TInvx st T Cs Ω H Sg Rp Scs Nt Z Ac t s2 := ⟨BlkOK.blkT h2.1, h2.1.tm.x t⟩
  refine WP.spec_bind (obj.Tcb.set_timer_deadline.wr s2 t d) fun s3 e3 => ?_
  subst e3
  have hx3 := hx2.wr (K := 3528#u64) (v := d) ht (by simp) (by simp) (by simp) (fun h => by simp at h)
  obtain ⟨f3, n3, N3⟩ := FA (K := 3528#u64) d h2.2.1 h2.2.2 hN2 (by simp) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (obj.Tcb.set_timer_badge.wr _ t bd) fun s4 e4 => ?_
  subst e4
  have hx4 := hx3.wr (K := 3536#u64) (v := bd) ht (by simp) (by simp) (by simp) (fun h => by simp at h)
  obtain ⟨f4, n4, N4⟩ := FA (K := 3536#u64) bd f3 n3 N3 (by simp) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (timer.set_parent.on _ t p hT ht) fun s5 e5 => ?_
  subst e5
  have hx5 := hx4.wr (K := 3560#u64) (v := p) ht (by simp) (by simp) (by simp) (fun _ => hp)
  obtain ⟨f5, n5, N5⟩ := FA (K := 3560#u64) p f4 n4 N4 (by simp) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (timer.set_left.on _ t 0#u64 hT ht) fun s6 e6 => ?_
  subst e6
  have hx6 := hx5.wr (K := 3544#u64) (v := 0#u64) ht (by simp) (by simp) (by simp) (fun _ => Tz.zero)
  obtain ⟨f6, n6, N6⟩ := FA (K := 3544#u64) 0#u64 f5 n5 N5 (by simp) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (timer.set_right.on _ t 0#u64 hT ht) fun s7 e7 => ?_
  subst e7
  have hx7 := hx6.wr (K := 3552#u64) (v := 0#u64) ht (by simp) (by simp) (by simp) (fun _ => Tz.zero)
  obtain ⟨f7, n7, N7⟩ := FA (K := 3552#u64) 0#u64 f6 n6 N6 (by simp) (by simp) (by simp) (by simp) (by simp)
  step as ⟨i, hi1, hi2⟩
  simp only [lift, timer.RED, Aeneas.Std.bind_ok]
  refine WP.spec_bind (obj.Tcb.set_timer_height.wr _ t _) fun s8 e8 => ?_
  subst e8
  have h8 := hx7.wr_ht ht (v := i ||| 1#u64) fun c hcv => by
    rw [or1_shr8, shl8_shr8 (h1.1.cpu_small hc) hi1] at hcv
    rw [show c = cpu from UScalar.eq_of_val_eq hcv]; exact hc
  obtain ⟨f8, n8, -⟩ := FA (K := 3568#u64) (i ||| 1#u64) f7 n7 N7 (by simp) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (timer.insert_fixup.tf (s0 := s) _ cpu t ⟨h8, f8, n8⟩ hc htz) fun s9 h9 => ?_
  split
  · refine WP.spec_bind (obj.node_set.spec s9 cpu _ t) fun s10 e10 => ?_
    subst e10
    have h10 := h9.1.wr_node hc (o := layout.node.TIMER_MIN) (by rw [timer_min_val]; simp) htz
    have f10 := h9.2.1.trans (foot_node (v := t) (h9.nodes cpu hc) hc (by rw [timer_min_val]; omega)
      (by rw [timer_min_val]) (by rw [timer_min_val]; omega))
    refine WP.spec_mono (obj.node_set.spec _ cpu _ 1#u64) fun s11 e11 => ?_
    subst e11
    have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    refine ⟨reprogram_at.tinv h10 hc, f10.trans ?_⟩
    exact foot_node (h10.nodes cpu hc) hc (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)
  · exact (WP.spec_ok _).2 ⟨h9.1, h9.2.1⟩

end timer

end

end Fl4Proofs.P1
