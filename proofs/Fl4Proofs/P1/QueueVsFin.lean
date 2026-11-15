/-
P1's side of the rest of the P3 CSpace side's `FinWorkHyp`.

* VSpace finalisations (`unmap_page_table`, `unmap_page`, `delete_asid`,
  `delete_asid_pool`, and `set_vm_root`, which writes no word): they write
  only page-table and ASID-pool/table words, given as a set `V` of aligned
  words of `Ω` outside `Sg` (`VsOK`); `blk_of_vs` then keeps `BlkOK` with
  the `CaiFr` frame, every TCB field from offset 192, every node word and
  every `Sg` word (so P1's invariant is untouched).
* `deleting_irq_handler`: the IRQ slot's cap (null or a notification cap)
  is finalised with `fin_ntfn.blk`, writing no cap-slot word; then the slot
  is emptied (`hes`, the slot frame, as in `cdt.delete.ep`).
-/
import Fl4Proofs.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The VSpace words: aligned words of the other objects, outside `Sg`. -/
def VsOK (Ω Sg : Set U64) (V : U64 → Prop) : Prop := ∀ b, V b → Aligned b ∧ b ∈ Ω ∧ b ∉ Sg

/-- **Writes to VSpace words leave P1's invariant untouched.** -/
theorem blk_of_vs {s s' : S} {V : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hV : VsOK Ω Sg V)
    (hw : WritesIn st s s' V) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ CaiFr st T Scs 0#u64 s s' ∧ L.actionW s' = L.actionW s ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, 160 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  have hB : ∀ b, V b → CapW T Ω Sg b := fun b hb => Or.inr ⟨(hV b hb).2.1, (hV b hb).2.2⟩
  obtain ⟨h', -, ec, ecs, ea, fld, nod, sig⟩ := blk_of_capw h hw hB
  exact ⟨h', CaiFr.of_capw h hw hB, ea, ec, ecs, fld, nod, sig⟩

theorem writesIn_wr_V {s : S} {V : U64 → Prop} {x v : U64} (hV : VsOK Ω Sg V) (hx : V x) :
    WritesIn st s (L.wr s x v) V :=
  (writesIn_wr (hV x hx).1).mono fun b e => by rw [e]; exact hx

/-- `set_kernel_vm_root` writes no word. -/
theorem vspace.set_kernel_vm_root.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) :
    vspace.set_kernel_vm_root st ar s a ⦃ r => r.1 = s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.set_kernel_vm_root
  refine WP.spec_bind (P0.vspace.kernel_root.p0 st s hS) fun k _ => ?_
  exact WP.spec_bind (hA.set_vspace a k 0#u64) fun a1 _ => (WP.spec_ok _).2 rfl

/-- `set_vm_root` writes no word. -/
theorem vspace.set_vm_root.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) : vspace.set_vm_root st ar s a t ⦃ r => r.1 = s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.set_vm_root
  refine WP.spec_bind (Pₘ := fun _ => True) (by unfold obj.Tcb.slot; simp [lift]) fun sl _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun c _ => ?_
  have K := vspace.set_kernel_vm_root.same (st := st) hA s a
  cases c
  all_goals try exact K
  rename_i ptr b asid
  cases b
  · simp only [Bool.false_eq_true, ite_false]; exact K
  · simp only [ite_true]
    refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s asid hS) fun r _ => ?_
    rcases r with r1 | e
    · by_cases e1 : r1 = ptr
      · simp only [e1, ite_true]
        exact WP.spec_bind (hA.set_vspace a ptr asid) fun a1 _ => (WP.spec_ok _).2 rfl
      · simp only [e1, ite_false]; exact K
    · exact K

/-- **`unmap_page_table`** writes only the PD slot it looks up. -/
theorem vspace.unmap_page_table.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hlk : ∀ r1, vspace.lookup_pd_slot st s r1 vaddr ⦃ r => ∀ x, r = .Ok x → V x ⦄) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_asid
  have i2 := hA.invalidate_page_structures
  unfold vspace.unmap_page_table
  refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s asid hS) fun r _ => ?_
  rcases r with r1 | e
  · refine WP.spec_bind (hlk r1) fun r2 hr2 => ?_
    rcases r2 with x | e
    · have hx := hr2 x rfl
      step*
      all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page`** writes only the PT/PD/PDPT slot it looks up. -/
theorem vspace.unmap_page.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hpt : ∀ r1, vspace.lookup_pt_slot st s r1 vaddr ⦃ r => ∀ x, r = .Ok x → V x ⦄)
    (hpd : ∀ r1, vspace.lookup_pd_slot st s r1 vaddr ⦃ r => ∀ x, r = .Ok x → V x ⦄)
    (hpdpt : ∀ r1, vspace.lookup_pdpt_slot st s r1 vaddr ⦃ r => ∀ x, r = .Ok x → V x ⦄) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_page
  unfold vspace.unmap_page
  refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s asid hS) fun r _ => ?_
  rcases r with r1 | e
  · step with P0.layout.paddr.p0 as ⟨pa, _⟩
    cases size
    · refine WP.spec_bind (hpt r1) fun r2 hr2 => ?_
      rcases r2 with x | e
      · have hx := hr2 x rfl
        repeat step
        try split
        all_goals try simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        all_goals try step*
        all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · refine WP.spec_bind (hpd r1) fun r2 hr2 => ?_
      rcases r2 with x | e
      · have hx := hr2 x rfl
        repeat step
        try split
        all_goals try simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        all_goals try step*
        all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · refine WP.spec_bind (hpdpt r1) fun r2 hr2 => ?_
      rcases r2 with x | e
      · have hx := hr2 x rfl
        repeat step
        try split
        all_goals try simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        all_goals try step*
        all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- Nested translation invalidation changes only the architecture state. -/
theorem ept.invalidate.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (root : U64) : ept.invalidate st ar s a root ⦃ r => r.1 = s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hInv := hA.invalidate_ept
  unfold ept.invalidate
  step* <;> simp_all

set_option maxHeartbeats 1000000 in
/-- Walking native and nested ASIDs changes no memory. -/
theorem vspace.delete_asid_pool_loop.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (base pool i : U64) (hi : i.val ≤ 512) :
    vspace.delete_asid_pool_loop st ar s a base pool i ⦃ r => r.1 = s ⦄ := by
  unfold vspace.delete_asid_pool_loop
  apply loop.spec_decr_nat (measure := fun x => 512 - x.2.2.val)
    (inv := fun x => x.1 = s ∧ x.2.2.val ≤ 512)
  · rintro ⟨s1, a1, j⟩ ⟨hs1, hj⟩
    dsimp only at hs1
    subst s1
    unfold vspace.delete_asid_pool_loop.body
    dsimp only at hj ⊢
    by_cases hjl : j < 512#u64
    · simp only [hjl, ↓reduceIte]
      step as ⟨off, hoff⟩
      simp only [lift, bind_ok]
      step with LawfulStore.read_spec as ⟨v, hv⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = s) ?_ ?_
      · split
        · exact ept.invalidate.same hA s a1 _
        · split
          · exact WP.spec_bind (hA.invalidate_asid a1 _) fun _ _ => (WP.spec_ok _).2 rfl
          · simp only [bind_ok, WP.spec_ok]
      · rintro ⟨s2, a2⟩ hs2
        dsimp only at hs2
        subst s2
        try dsimp only
        step as ⟨j1, hj1⟩
        try simp only [WP.spec_ok]
        exact ⟨by scalar_tac, by scalar_tac⟩
    · simp only [hjl, ↓reduceIte, WP.spec_ok]
  · exact ⟨rfl, hi⟩

/-- **`delete_asid`** writes only the ASID-pool entry. -/
theorem vspace.delete_asid.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid root : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hpool : ∀ i, vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄) :
    vspace.delete_asid st ar s a asid root ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.delete_asid
  step as ⟨i, _⟩
  refine WP.spec_bind (hpool i) fun pool hp => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rename_i hp0
  have he := hp hp0
  simp only [lift, bind_ok]
  step with LawfulStore.read_spec as ⟨v, _⟩
  split
  · split
    · refine WP.spec_bind (ept.invalidate.same hA s a root) ?_
      rintro ⟨s1, a1⟩ hs1
      dsimp only at hs1
      subst s1
      try dsimp only
      step with LawfulStore.write_spec as ⟨s2, e2⟩
      try simp only [WP.spec_ok]
      rw [e2]; exact writesIn_wr_V hV he
    refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    step with sched.cur_thread.spec as ⟨ct, _⟩
    refine WP.spec_mono (vspace.set_vm_root.same hA s1 a1 ct) fun r e => ?_
    rw [e, e1]; exact writesIn_wr_V hV he
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`delete_asid_pool`** writes only the ASID-table entry. -/
theorem vspace.delete_asid_pool.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (base pool : U64) {V : U64 → Prop}
    (hset : ∀ hi, vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄) :
    vspace.delete_asid_pool st ar s a base pool ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.delete_asid_pool
  step as ⟨i, _⟩
  refine WP.spec_bind (P0.vspace.asid_table.p0 st s i hS) fun p1 _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  refine WP.spec_bind (vspace.delete_asid_pool_loop.same hA s a base pool 0#u64 (by simp)) ?_
  rintro ⟨s0, a1⟩ hs0
  dsimp only at hs0
  subst s0
  try dsimp only
  step as ⟨i2, _⟩
  refine WP.spec_bind (hset i2) fun s1 w1 => ?_
  step with sched.cur_thread.spec as ⟨ct, _⟩
  exact WP.spec_mono (vspace.set_vm_root.same hA s1 a1 ct) fun r e => by rw [e]; exact w1

/-- **`deleting_irq_handler`**: the IRQ slot holds a null or notification
cap; finalising it (`fin_ntfn.blk`) keeps `BlkOK` and writes no cap-slot
word, and the slot is then emptied (`hes`: `empty_slot` writes only cap-slot
words, from a state agreeing with `s` on them, with any fact `P` of its
result). -/
theorem interrupt.deleting_irq_handler.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (irq isl : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hisl : interrupt.irq_slot st s irq = ok isl)
    (hcap : obj.Slot.cap st isl s ⦃ c => c = .Null ∨
      ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ∧ n ∈ Nt ∧ H n = some .ntfn ⦄)
    {P : S × A → Prop}
    (hes : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 isl .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧ P r ⦄) :
    interrupt.deleting_irq_handler st ar s a irq ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ (r = (s, a) ∨ P r) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.deleting_irq_handler
  rw [hisl]
  simp only [bind_ok]
  unfold cdt.delete_one
  refine WP.spec_bind hcap fun c hc => ?_
  rcases hc with rfl | ⟨n, b0, b1, b2, rfl, hn, hH⟩
  · simp only [capability.Cap.is_null, bind_ok, ite_true, WP.spec_ok]
    exact ⟨h, by first | exact Or.inl rfl | exact Or.inl trivial | trivial⟩
  · simp only [capability.Cap.is_null, bind_ok, Bool.false_eq_true, ite_false]
    refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s isl hS) fun fin _ => ?_
    have hm : ({n} : Set U64) ⊆ EH H := fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inr hH
    refine WP.spec_bind (fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin h hn hH) ?_
    rintro ⟨rr, s1, a1⟩ ⟨-, -, h1, f1⟩
    simp only [uncurry_apply_pair, WP.uncurry'_pair]
    exact WP.spec_mono (hes s1 a1 (foot_keeps_capw h (f1.mono hm))) fun r ⟨w, hP⟩ =>
      ⟨(blk_of_capw h1 w fun b hb => hb).1, Or.inr hP⟩

end

end Fl4Proofs.P1
