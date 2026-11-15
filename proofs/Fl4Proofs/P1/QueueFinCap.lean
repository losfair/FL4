/-
P1's half of the P3 CSpace side's `FinWorkHyp`: `finalise_cap` of a final
notification, reply, scheduling-context or thread cap keeps `BlkOK` and
writes no cap-slot word (every `CapW` word is kept, through the `Foot` /
`FootD` footprints of `fin_ntfn.blk`, `fin_reply.blk`, `fin_sc.blk`,
`fin_thread.blk`), with the remainder and cleanup caps.
-/
import Fl4Proofs.P1.QueueDelete
import Fl4Proofs.P1.QueueReplyPop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- A footprint with the debug-list words keeps every cap-slot word too. -/
theorem footD_keeps_capw {s s' : S} {Es : Set U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hE : Es ⊆ EH H) (f : FootD st T Cs Sg Scs Z Es s s') :
    ∀ b, Aligned b → CapW T Ω Sg b → L.mem s' b = L.mem s b := by
  intro b hb hc
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  refine f.mem_eq hb fun hk => ?_
  rcases hk with hk | ⟨y, hy, e | e⟩ | ⟨c, hc', e⟩
  · exact capw_not_kw h hc hb (le_refl _) (by omega) (KW.mono hk hE)
  · rcases hc with hl | ⟨hm, -⟩
    · exact tlow_ne_field hT hy (by simp) (by simp) hl e
    · exact out_ne_field (h0.omega _ hm) hy (hT y hy) (K := 3576#u64) (by simp) (by rw [e]; rfl)
  · rcases hc with hl | ⟨hm, -⟩
    · exact tlow_ne_field hT hy (by simp) (by simp) hl e
    · exact out_ne_field (h0.omega _ hm) hy (hT y hy) (K := 3584#u64) (by simp) (by rw [e]; rfl)
  · have hN := h0.nodes c hc'
    rcases hc with hl | ⟨hm, -⟩
    · exact tlow_ne_node hT hN (by simp [layout.node.DEBUG_TCBS]) hl e.symm
    · exact out_ne_node (h0.omega _ hm) hc' hN (o := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
        (by rw [e])

theorem tcb_slot_ctable (p : U64) : obj.Tcb.slot p layout.tcb.SLOT_CTABLE = ok p := by
  unfold obj.Tcb.slot
  have e : core.num.U64.wrapping_add p (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) = p := by
    apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, layout.tcb.SLOT_CTABLE,
      U64.size_def, U64.numBits]
  simp [lift, e]

/-- The remainder and cleanup of a thread cap's finalisation. -/
theorem fin_thread.rem {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin : Bool) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r =>
      r.1 = (if fin then .Zombie p capability.ZOMBIE_TCB 6#u64 else .Null, .Null) ⦄ := by
  have hS := L.total
  unfold objects.finalise_cap_object
  dsimp only
  simp only [tcb_slot_ctable, bind_ok]
  split
  · rename_i hf
    step*
    refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun r _ => ?_
    · split
      · exact (WP.spec_ok _).2 trivial
      · step*
    · obtain ⟨s4, a2⟩ := r
      try simp only [WP.uncurry'_pair]
      step*
      simp [layout.tcb.NUM_SLOTS]
  · rename_i hf
    simp [hf]

/-- The remainder and cleanup of an SC cap's finalisation. -/
theorem fin_sc.rem {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin : Bool) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) fin ⦃ r => r.1 = (.Null, .Null) ⦄ := by
  have hS := L.total
  unfold objects.finalise_cap_object
  dsimp only
  split
  · step*
    refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun r _ => ?_
    · split
      · exact (WP.spec_ok _).2 trivial
      · step*
    · obtain ⟨s4, a2⟩ := r
      try simp only [WP.uncurry'_pair]
      step*
  · simp

/-- `finalise_cap` of a cap other than an IRQ handler is `finalise_cap_object`. -/
theorem fin_cap_eq_obj {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {c : capability.Cap} {fin ex : Bool}
    (hc : ∀ i, c ≠ .IrqHandler i) :
    objects.finalise_cap st ar s a c fin ex = objects.finalise_cap_object st ar s a c fin := by
  cases c
  case IrqHandler i => exact absurd rfl (hc i)
  all_goals simp [objects.finalise_cap]

/-- **Notification**: `finalise_cap` keeps `BlkOK` and every cap-slot word. -/
theorem fin_cap_ntfn.slots {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n : U64) (b0 b1 b2 : _)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin ex ⦃ r =>
      r.1 = (.Null, .Null) ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ Foot st T Cs Sg Scs Z (EH H) s r.2.1 ∧
      ∀ b, Aligned b → CapW T Ω Sg b → L.mem r.2.1 b = L.mem s b ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  have hm : ({n} : Set U64) ⊆ EH H := fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inr hH
  exact WP.spec_mono (fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin h hn hH) fun r ⟨e, _, hb, f⟩ =>
    ⟨e, hb, f.mono hm, foot_keeps_capw h (f.mono hm)⟩

/-- **Reply**: `finalise_cap` keeps `BlkOK` and every cap-slot word. -/
theorem fin_cap_reply.slots {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp) :
    objects.finalise_cap st ar s a (.Reply p x) fin ex ⦃ r =>
      r.1 = (.Null, .Null) ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ Foot st T Cs Sg Scs Z (EH H) s r.2.1 ∧
      ∀ b, Aligned b → CapW T Ω Sg b → L.mem r.2.1 b = L.mem s b ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_reply.blk hA s a p x fin h hp) fun r ⟨e, hb, f⟩ => ⟨e, hb, f, foot_keeps_capw h f⟩

/-- **Scheduling context**: `finalise_cap` keeps `BlkOK` (the SC leaves the
active set when deactivated) and every cap-slot word. -/
theorem fin_cap_sc.slots {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap st ar s a (.SchedContext p x) fin ex ⦃ r =>
      r.1 = (.Null, .Null) ∧ (∃ Ac', (Ac' = Ac ∨ Ac' = Ac \ {p}) ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' r.2.1) ∧
      Foot st T Cs Sg Scs Z ∅ s r.2.1 ∧ ∀ b, Aligned b → CapW T Ω Sg b → L.mem r.2.1 b = L.mem s b ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (fin_sc.rem hA s a p x fin) (fin_sc.blk hA s a p x fin h hp hp0 hna hidle))
    fun r ⟨e, Ac', hA', hb, f⟩ => ⟨e, ⟨Ac', hA', hb⟩, f, foot_keeps_capw h (f.mono (Set.empty_subset _))⟩

/-- **Thread**: `finalise_cap` keeps `BlkOK` and every cap-slot word (its
footprint adds only the debug-list words); the remainder is the thread's
zombie when final. -/
theorem fin_cap_thread.slots {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap st ar s a (.Thread p) fin ex ⦃ r =>
      r.1 = (if fin then .Zombie p capability.ZOMBIE_TCB 6#u64 else .Null, .Null) ∧
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ FootD st T Cs Sg Scs Z (EH H) s r.2.1 ∧
      ∀ b, Aligned b → CapW T Ω Sg b → L.mem r.2.1 b = L.mem s b ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (WP.spec_and (fin_thread.rem hA s a p fin) (fin_thread.blk hA s a p fin h hp hna hidle hv0))
    fun r ⟨e, hb, f⟩ => ⟨e, hb, f, footD_keeps_capw h (le_refl _) f⟩

end

end Fl4Proofs.P1
