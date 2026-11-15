/-
The P0 assumption about the trusted world (DESIGN.md §9): the `Store` and
`Arch` implementations never fail. Their results are otherwise arbitrary,
so P0 theorems hold for every behaviour of memory and hardware.
-/
import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P0
open fl4_core

structure StoreTotal {S : Type _} (st : machine.Store S) : Prop where
  read : ∀ s a, st.read s a ⦃ _ => True ⦄
  write : ∀ s a v, st.write s a v ⦃ _ => True ⦄
  zero : ∀ s a n, st.zero s a n ⦃ _ => True ⦄
  clear_free : ∀ s a n, st.clear_free s a n ⦃ _ => True ⦄
  ks_base : ∀ s, st.ks_base s ⦃ _ => True ⦄
  cur_cpu : ∀ s, st.cur_cpu s ⦃ _ => True ⦄

structure ArchTotal {A : Type _} (ar : machine.Arch A) : Prop where
  virtualization : ∀ a, ar.virtualization a ⦃ _ => True ⦄
  vcpu_capability : ∀ a f, ar.vcpu_capability a f ⦃ _ => True ⦄
  vcpu_barrier : ∀ a, ar.vcpu_barrier a ⦃ _ => True ⦄
  invalidate_ept : ∀ a r m, ar.invalidate_ept a r m ⦃ _ => True ⦄
  now : ∀ a, ar.now a ⦃ _ => True ⦄
  set_deadline : ∀ a t, ar.set_deadline a t ⦃ _ => True ⦄
  us_to_ticks : ∀ a x, ar.us_to_ticks a x ⦃ _ => True ⦄
  ticks_to_us : ∀ a x, ar.ticks_to_us a x ⦃ _ => True ⦄
  max_us : ∀ a, ar.max_us a ⦃ _ => True ⦄
  kernel_wcet_ticks : ∀ a, ar.kernel_wcet_ticks a ⦃ _ => True ⦄
  irq_pending : ∀ a, ar.irq_pending a ⦃ _ => True ⦄
  take_pending_irq : ∀ a, ar.take_pending_irq a ⦃ _ => True ⦄
  mask_irq : ∀ a i m, ar.mask_irq a i m ⦃ _ => True ⦄
  ack_irq : ∀ a i, ar.ack_irq a i ⦃ _ => True ⦄
  set_vspace : ∀ a r i, ar.set_vspace a r i ⦃ _ => True ⦄
  invalidate_page : ∀ a i v, ar.invalidate_page a i v ⦃ _ => True ⦄
  invalidate_asid : ∀ a i, ar.invalidate_asid a i ⦃ _ => True ⦄
  invalidate_page_structures : ∀ a i, ar.invalidate_page_structures a i ⦃ _ => True ⦄
  ioapic_map : ∀ a i p l q v, ar.ioapic_map a i p l q v ⦃ _ => True ⦄
  ioapic_map_remapped : ∀ a i p l q v h, ar.ioapic_map_remapped a i p l q v h ⦃ _ => True ⦄
  num_ioapics : ∀ a, ar.num_ioapics a ⦃ _ => True ⦄
  ioapic_pins : ∀ a i, ar.ioapic_pins a i ⦃ _ => True ⦄
  port_in : ∀ a p n, ar.port_in a p n ⦃ _ => True ⦄
  port_out : ∀ a p n v, ar.port_out a p n v ⦃ _ => True ⦄
  fpu_flush : ∀ a t, ar.fpu_flush a t ⦃ _ => True ⦄
  fpu_sanitise : ∀ a t, ar.fpu_sanitise a t ⦃ _ => True ⦄
  fpu_reload : ∀ a t, ar.fpu_reload a t ⦃ _ => True ⦄
  fpu_release : ∀ a t, ar.fpu_release a t ⦃ _ => True ⦄
  remote_stall : ∀ a c, ar.remote_stall a c ⦃ _ => True ⦄
  send_reschedule : ∀ a m, ar.send_reschedule a m ⦃ _ => True ⦄
  putc : ∀ a c, ar.putc a c ⦃ _ => True ⦄
  get_char : ∀ a, ar.get_char a ⦃ _ => True ⦄
  halt : ∀ a, ar.halt a ⦃ _ => True ⦄

-- The same facts as `step` lemmas; `step*` discharges the `StoreTotal` or
-- `ArchTotal` premise from the context.
section
variable {S : Type _} {st : machine.Store S}
@[step] theorem StoreTotal.read_spec (h : StoreTotal st) s a : st.read s a ⦃ _ => True ⦄ := h.read s a
@[step] theorem StoreTotal.write_spec (h : StoreTotal st) s a v : st.write s a v ⦃ _ => True ⦄ := h.write s a v
@[step] theorem StoreTotal.zero_spec (h : StoreTotal st) s a n : st.zero s a n ⦃ _ => True ⦄ := h.zero s a n
@[step] theorem StoreTotal.clear_free_spec (h : StoreTotal st) s a n : st.clear_free s a n ⦃ _ => True ⦄ := h.clear_free s a n
@[step] theorem StoreTotal.ks_base_spec (h : StoreTotal st) s : st.ks_base s ⦃ _ => True ⦄ := h.ks_base s
@[step] theorem StoreTotal.cur_cpu_spec (h : StoreTotal st) s : st.cur_cpu s ⦃ _ => True ⦄ := h.cur_cpu s
end

section
variable {A : Type _} {ar : machine.Arch A}
@[step] theorem ArchTotal.virtualization_spec (h : ArchTotal ar) a : ar.virtualization a ⦃ _ => True ⦄ := h.virtualization a
@[step] theorem ArchTotal.vcpu_capability_spec (h : ArchTotal ar) a f : ar.vcpu_capability a f ⦃ _ => True ⦄ := h.vcpu_capability a f
@[step] theorem ArchTotal.vcpu_barrier_spec (h : ArchTotal ar) a : ar.vcpu_barrier a ⦃ _ => True ⦄ := h.vcpu_barrier a
@[step] theorem ArchTotal.invalidate_ept_spec (h : ArchTotal ar) a r m : ar.invalidate_ept a r m ⦃ _ => True ⦄ := h.invalidate_ept a r m
@[step] theorem ArchTotal.now_spec (h : ArchTotal ar) a : ar.now a ⦃ _ => True ⦄ := h.now a
@[step] theorem ArchTotal.set_deadline_spec (h : ArchTotal ar) a t : ar.set_deadline a t ⦃ _ => True ⦄ := h.set_deadline a t
@[step] theorem ArchTotal.us_to_ticks_spec (h : ArchTotal ar) a x : ar.us_to_ticks a x ⦃ _ => True ⦄ := h.us_to_ticks a x
@[step] theorem ArchTotal.ticks_to_us_spec (h : ArchTotal ar) a x : ar.ticks_to_us a x ⦃ _ => True ⦄ := h.ticks_to_us a x
@[step] theorem ArchTotal.max_us_spec (h : ArchTotal ar) a : ar.max_us a ⦃ _ => True ⦄ := h.max_us a
@[step] theorem ArchTotal.kernel_wcet_ticks_spec (h : ArchTotal ar) a : ar.kernel_wcet_ticks a ⦃ _ => True ⦄ := h.kernel_wcet_ticks a
@[step] theorem ArchTotal.irq_pending_spec (h : ArchTotal ar) a : ar.irq_pending a ⦃ _ => True ⦄ := h.irq_pending a
@[step] theorem ArchTotal.take_pending_irq_spec (h : ArchTotal ar) a : ar.take_pending_irq a ⦃ _ => True ⦄ := h.take_pending_irq a
@[step] theorem ArchTotal.mask_irq_spec (h : ArchTotal ar) a i m : ar.mask_irq a i m ⦃ _ => True ⦄ := h.mask_irq a i m
@[step] theorem ArchTotal.ack_irq_spec (h : ArchTotal ar) a i : ar.ack_irq a i ⦃ _ => True ⦄ := h.ack_irq a i
@[step] theorem ArchTotal.set_vspace_spec (h : ArchTotal ar) a r i : ar.set_vspace a r i ⦃ _ => True ⦄ := h.set_vspace a r i
@[step] theorem ArchTotal.invalidate_page_spec (h : ArchTotal ar) a i v : ar.invalidate_page a i v ⦃ _ => True ⦄ := h.invalidate_page a i v
@[step] theorem ArchTotal.invalidate_asid_spec (h : ArchTotal ar) a i : ar.invalidate_asid a i ⦃ _ => True ⦄ := h.invalidate_asid a i
@[step] theorem ArchTotal.invalidate_page_structures_spec (h : ArchTotal ar) a i : ar.invalidate_page_structures a i ⦃ _ => True ⦄ := h.invalidate_page_structures a i
@[step] theorem ArchTotal.ioapic_map_spec (h : ArchTotal ar) a i p l q v : ar.ioapic_map a i p l q v ⦃ _ => True ⦄ := h.ioapic_map a i p l q v
@[step] theorem ArchTotal.ioapic_map_remapped_spec (h : ArchTotal ar) a i p l q v hd : ar.ioapic_map_remapped a i p l q v hd ⦃ _ => True ⦄ := h.ioapic_map_remapped a i p l q v hd
@[step] theorem ArchTotal.num_ioapics_spec (h : ArchTotal ar) a : ar.num_ioapics a ⦃ _ => True ⦄ := h.num_ioapics a
@[step] theorem ArchTotal.ioapic_pins_spec (h : ArchTotal ar) a i : ar.ioapic_pins a i ⦃ _ => True ⦄ := h.ioapic_pins a i
@[step] theorem ArchTotal.port_in_spec (h : ArchTotal ar) a p n : ar.port_in a p n ⦃ _ => True ⦄ := h.port_in a p n
@[step] theorem ArchTotal.port_out_spec (h : ArchTotal ar) a p n v : ar.port_out a p n v ⦃ _ => True ⦄ := h.port_out a p n v
@[step] theorem ArchTotal.fpu_flush_spec (h : ArchTotal ar) a t : ar.fpu_flush a t ⦃ _ => True ⦄ := h.fpu_flush a t
@[step] theorem ArchTotal.fpu_sanitise_spec (h : ArchTotal ar) a t : ar.fpu_sanitise a t ⦃ _ => True ⦄ := h.fpu_sanitise a t
@[step] theorem ArchTotal.fpu_reload_spec (h : ArchTotal ar) a t : ar.fpu_reload a t ⦃ _ => True ⦄ := h.fpu_reload a t
@[step] theorem ArchTotal.fpu_release_spec (h : ArchTotal ar) a t : ar.fpu_release a t ⦃ _ => True ⦄ := h.fpu_release a t
@[step] theorem ArchTotal.remote_stall_spec (h : ArchTotal ar) a c : ar.remote_stall a c ⦃ _ => True ⦄ := h.remote_stall a c
@[step] theorem ArchTotal.send_reschedule_spec (h : ArchTotal ar) a m : ar.send_reschedule a m ⦃ _ => True ⦄ := h.send_reschedule a m
@[step] theorem ArchTotal.putc_spec (h : ArchTotal ar) a c : ar.putc a c ⦃ _ => True ⦄ := h.putc a c
@[step] theorem ArchTotal.get_char_spec (h : ArchTotal ar) a : ar.get_char a ⦃ _ => True ⦄ := h.get_char a
@[step] theorem ArchTotal.halt_spec (h : ArchTotal ar) a : ar.halt a ⦃ _ => True ⦄ := h.halt a
end

end Fl4Proofs.P0

/-- `x as usize` keeps small values: usize has at least 32 bits. -/
theorem mod_numBits_of_lt {x : Nat} (h : x < 2 ^ 32) : x % 2 ^ System.Platform.numBits = x := by
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h' | h' <;> simp [h']
  omega

/-- Close a side condition left by `step*`, or leave it untouched. -/
macro "p0_close" : tactic =>
  `(tactic| try (first
    | trivial
    | (exact (WP.spec_ok _).2 trivial)
    | scalar_tac
    | (simp_all; done)
    | (simp (disch := scalar_tac) only [mod_numBits_of_lt, Array.length_eq] at *; scalar_tac)
    | (simp_all <;> scalar_tac)
    -- Constants first (their `val_eq` simp lemmas), then `as usize`.
    | (simp_all <;> simp (disch := scalar_tac) only [mod_numBits_of_lt, Array.length_eq] at * <;> scalar_tac)
    -- Comparisons with named constants, as comparisons of their values.
    | (simp only [UScalar.lt_equiv, UScalar.le_equiv] at * <;> simp_all <;>
        simp (disch := scalar_tac) only [mod_numBits_of_lt, Array.length_eq] at * <;> scalar_tac)))

/-- The automatic P0 proof: step through the body, then close arithmetic
side conditions. -/
macro "p0_auto" : tactic => `(tactic| (step* <;> p0_close))

open Lean Elab Tactic Meta in
/-- Split the first local of a product type into its components, so that
`let (a, b) := x` in the goal reduces. -/
elab "p0_cases_prod" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``Prod 2 then
      liftMetaTactic fun g => do
        let gs ← g.cases d.fvarId
        return gs.toList.map (·.mvarId)
      return
  throwError "p0_cases_prod: no local of a product type"

open Lean Elab Tactic Meta in
/-- Expose a result or option that is matched beneath a monadic bind. -/
elab "p0_cases_sum" : tactic => withMainContext do
  let target ← getMainTarget
  for d in (← getLCtx) do
    if d.isImplementationDetail || !target.containsFVar d.fvarId then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``core.result.Result 2 || t.isAppOfArity ``Option 1 then
      liftMetaTactic fun g => do
        let gs ← g.cases d.fvarId
        return gs.toList.map (·.mvarId)
      return
  throwError "p0_cases_sum: no result or option in the goal"

theorem p0_if {α : Type _} (c : Prop) [Decidable c] (x y : Result α) (P : α → Prop)
    (hx : c → x ⦃ P ⦄) (hy : ¬ c → y ⦃ P ⦄) : (if c then x else y) ⦃ P ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h
theorem p0_if_bind {α : Type _} {β : Type _} (c : Prop) [Decidable c] (x y : Result α)
    (k : α → Result β) (P : β → Prop)
    (hx : c → Aeneas.Std.bind x k ⦃ P ⦄) (hy : ¬ c → Aeneas.Std.bind y k ⦃ P ⦄) :
    Aeneas.Std.bind (if c then x else y) k ⦃ P ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hx h
  · rw [if_neg h]; exact hy h

open Lean Elab Tactic Meta in
elab "p0_ite_head" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOf ``Aeneas.Std.WP.spec do throwError "not a spec"
  let args := target.getAppArgs
  let program := args[args.size - 2]!
  if program.isAppOf ``ite then
    evalTactic (← `(tactic| apply p0_if <;> intro))
  else if let some (m, _) := Aeneas.Step.getBindArgs? program then
    if m.isAppOf ``ite then
      evalTactic (← `(tactic| apply p0_if_bind <;> intro))
    else throwError "bind head is not an if"
  else throwError "head is not an if"
macro "p0_structural" : tactic => `(tactic| (
  (repeat' (first | p0_cases_sum | step | p0_ite_head | (simp only [bind_tc_ok, bind_ok]) | p0_cases_prod | split)) <;> p0_close))

/-- Split data returned by callees before simplifying deeply nested binds. -/
macro "p0_data" : tactic => `(tactic| (
  (repeat' (first | p0_cases_sum | step | (simp only [bind_tc_ok, bind_ok]) | split | p0_cases_prod)) <;> p0_close))

/-- The fallback for large matches on literals, where `step*` times out in
`whnf`: split the matches explicitly. -/
macro "p0_split" : tactic => `(tactic| ((repeat' (first | step | (simp only [bind_tc_ok, bind_ok]) | split | p0_cases_prod)) <;> p0_close))

/-- The fallback for a match on the arguments with a call in each branch:
split the outer matches, then step through each branch. -/
macro "p0_match" : tactic => `(tactic| (split <;> (try split) <;> p0_auto))

/-- A loop body: the automatic proof, or splitting when it gets stuck. -/
macro "p0_body" : tactic => `(tactic| first | (p0_auto; done) | p0_split)
