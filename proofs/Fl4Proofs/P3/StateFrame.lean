/-
P3 (DESIGN.md §9), CSpace: FL4's `set_thread_state` leaves every slot word
alone (`set_thread_state_slots`, discharging `SlotsSame`).

`set_thread_state t v` writes the TCB's `STATE` word (offset 3328, past the
five cap slots at offsets 0..159) and, through `schedule_tcb`, maybe the
current core's `SCHED_ACTION` node word. The TCB word is inside `t`'s
object but outside its slots; the node word is assumed to lie outside every
object of the typed heap (`OutsideObjects`: the per-core node is kernel
global data, not a retyped object).
-/
import Fl4Proofs.P3.Restart
import Fl4Proofs.P1.QueueRelease
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Hypothesis: the aligned word `A` lies in no object of the typed heap. -/
def OutsideObjects (th : TypedHeap) (A : U64) : Prop :=
  P1.Aligned A ∧ ∀ p k, th p = some k → ¬ (p.val ≤ A.val ∧ A.val < p.val + objSize k)

theorem SlotsSame.refl (th : TypedHeap) (m : U64 → U64) : SlotsSame th m m :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem SlotsSame.trans {th : TypedHeap} {m1 m2 m3 : U64 → U64} (h1 : SlotsSame th m1 m2)
    (h2 : SlotsSame th m2 m3) : SlotsSame th m1 m3 := by
  intro a ha
  obtain ⟨a1, a2, a3, a4⟩ := h1 a ha
  obtain ⟨b1, b2, b3, b4⟩ := h2 a ha
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-! The reads and writes of `set_thread_state` (as in P1's `QueueCallers`,
restated here so that this file depends only on P1's queue basics). -/

/-- The TCB `STATE` word. -/
def stA (t : U64) : U64 := core.num.U64.wrapping_add t layout.tcb.STATE

theorem stA_eq (t : U64) : stA t = core.num.U64.wrapping_add t 3328#u64 := by
  unfold stA layout.tcb.STATE layout.tcb.F; rfl

theorem tcb_set_state_eq (s : S) (t v : U64) : obj.Tcb.set_state st t s v = ok (L.wr s (stA t) v) := by
  unfold obj.Tcb.set_state; simp [lift, L.write_eq, stA]

theorem tcb_state_spec' (s : S) (t : obj.Tcb) : obj.Tcb.state st t s ⦃ v => v = L.mem s (stA t) ⦄ := by
  unfold obj.Tcb.state; simp [lift, L.read_eq, stA]

theorem sc_is_null_spec' (sc : obj.Sc) : obj.Sc.is_null sc ⦃ b => b = decide (sc = 0#u64) ⦄ := by
  unfold obj.Sc.is_null; simp

theorem action_spec' (s : S) :
    sched.action st s ⦃ v => v = L.mem s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ⦄ := by
  unfold sched.action; step*; simp_all

theorem set_action_spec' (s : S) (v : U64) :
    sched.set_action st s v ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v ⦄ := by
  unfold sched.set_action; step*; simp_all

theorem cur_thread_spec' (s : S) :
    sched.cur_thread st s ⦃ v => v = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ⦄ := by
  unfold sched.cur_thread; step*; simp_all

attribute [local step] tcb_state_spec' sc_is_null_spec' action_spec' set_action_spec' cur_thread_spec'

theorem is_schedulable_spec' (s : S) (t : obj.Tcb) : sched.is_schedulable st s t ⦃ _ => True ⦄ := by
  unfold sched.is_schedulable sched.is_runnable sporadic.sc_active
  step
  repeat' (first | step | (simp only [bind_ok]) | split)
  all_goals simp_all

attribute [local step] is_schedulable_spec'

/-- A write to an aligned word outside every slot keeps the slot words. -/
theorem slotsSame_wr {th : TypedHeap} (hP : Placed th) (s : S) {A : U64} (v : U64) (hA : P1.Aligned A)
    (hout : ∀ a, IsSlot th a → ¬ (a.val ≤ A.val ∧ A.val < a.val + 32)) :
    SlotsSame th (L.mem s) (L.mem (L.wr s A v)) := by
  intro a ha
  have hf := ha.fit hP
  have hal := ha.align hP
  have hn := hout a ha
  have w : ∀ k : U64, k.val < 32 → k.val % 8 = 0 →
      L.mem (L.wr s A v) (wordOf a k) = L.mem s (wordOf a k) := by
    intro k hk hk8
    have hv := wordOf_val (a := a) (k := k) (by omega)
    apply L.mem_wr_ne hA (by unfold P1.Aligned; rw [hv]; omega)
    rw [hv]; omega
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

theorem slot_in_object {th : TypedHeap} (hP : Placed th) {a : U64} (ha : IsSlot th a) :
    ∃ p k, th p = some k ∧ p.val ≤ a.val ∧ a.val + 32 ≤ p.val + objSize k ∧
      (k = .tcb → a.val + 32 ≤ p.val + 32 * tcbSlots) := by
  obtain ⟨p, i, hi, rfl⟩ := ha
  obtain ⟨k, hk, hs⟩ := hi.size
  have hv := hi.val hP
  refine ⟨p, k, hk, by rw [hv]; omega, by rw [hv]; omega, fun hkt => ?_⟩
  subst hkt
  rcases hi with ⟨r, hr, -⟩ | ⟨-, hi⟩
  · rw [hk] at hr; cases hr
  · rw [hv]; simp [tcbSlots] at hi ⊢; omega

/-- **FL4's `set_thread_state` keeps the slot words**, for a TCB of the
typed heap and with the current core's scheduler-action word outside the
objects. -/
theorem set_thread_state_slots (th : TypedHeap) (hP : Placed th) (s : S) (t v : U64)
    (ht : th t = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    sched.set_thread_state st s t v ⦃ s' => SlotsSame th (L.mem s) (L.mem s') ⦄ := by
  -- the state word
  have htf := hP.fits t _ ht
  have hta := hP.align t _ ht
  have hstv : (stA t).val = t.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  have h1 : ∀ s0 : S, SlotsSame th (L.mem s0) (L.mem (L.wr s0 (stA t) v)) := by
    intro s0
    refine slotsSame_wr hP s0 v (by unfold P1.Aligned; rw [hstv]; omega) (fun a ha => ?_)
    obtain ⟨p, k, hk, h1, h2, h3⟩ := slot_in_object hP ha
    rw [hstv]
    by_cases hpt : p = t
    · subst hpt; rw [ht] at hk; cases hk
      have := h3 rfl; simp [tcbSlots] at this; omega
    · have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hP.disj p t k .tcb hk ht hpt with h | h <;> omega
  unfold sched.set_thread_state sched.schedule_tcb
  rw [tcb_set_state_eq]; simp only [bind_ok]
  step*
  all_goals first
    | (subst_vars; exact h1 s)
    | skip
  all_goals
    subst_vars
    have e : L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION =
        L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by simp
    rw [e]
    refine (h1 s).trans (slotsSame_wr hP _ _ hact.1 (fun a ha => ?_))
    obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hP ha
    have := hact.2 p k hk
    omega

end

end

end Fl4Proofs.P3
