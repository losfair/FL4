/-
P3 (DESIGN.md §9), untyped: **retyping TCBs** (FL4's 4 KiB TCBs, against
FL4's `invoke_untyped`, Fl4Spec/Ext/TcbSize.lean).

`create_object` for a TCB initialises the new TCB's registers, FPU area,
debug registers, domain and debug name, and appends it to the current core's
debug list. `create_tcb_frame`: all of that is written past the TCB's five
cap slots (offsets 256..4095), except the old list head's `debug_prev` word
and the core's list-head word, so the new TCB's slots stay zero (null caps,
l4v's `default_tcb` has null caps).
-/
import Fl4Proofs.P3.UntypedInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `s'` differs from `s` at most in the aligned words satisfying `P` (and has
the same kernel-state base). -/
def WFrame (s s' : S) (P : U64 → Prop) : Prop :=
  L.ksb s' = L.ksb s ∧ ∀ w : U64, P1.Aligned w → ¬ P w → L.mem s' w = L.mem s w

theorem WFrame.refl (s : S) (P : U64 → Prop) : WFrame (L := L) s s P := ⟨rfl, fun _ _ _ => rfl⟩

theorem WFrame.trans {s1 s2 s3 : S} {P : U64 → Prop} (h1 : WFrame (L := L) s1 s2 P) (h2 : WFrame (L := L) s2 s3 P) :
    WFrame (L := L) s1 s3 P := ⟨h2.1.trans h1.1, fun w hw hp => (h2.2 w hw hp).trans (h1.2 w hw hp)⟩

theorem WFrame.mono {s1 s2 : S} {P Q : U64 → Prop} (h : WFrame (L := L) s1 s2 P) (hpq : ∀ w, P w → Q w) :
    WFrame (L := L) s1 s2 Q := ⟨h.1, fun w hw hq => h.2 w hw (fun hp => hq (hpq w hp))⟩

theorem WFrame.wr (s : S) {P : U64 → Prop} {a : U64} (ha : P1.Aligned a) (hp : P a) (v : U64) :
    WFrame (L := L) s (L.wr s a v) P := by
  refine ⟨by simp, fun w hw hnp => ?_⟩
  apply L.mem_wr_ne ha hw
  intro e; exact hnp (by rw [show w = a from UScalar.eq_of_val_eq e.symm]; exact hp)

/-- The words of a TCB past its cap slots, but its affinity word (offset
3520, which `debug_append` reads). -/
def InT (t w : U64) : Prop := t.val + 256 ≤ w.val ∧ w.val < t.val + 4096 ∧ w.val ≠ t.val + 3520

theorem wa_val (a : U64) (n : Nat) (h : a.val + n < 2 ^ 64) :
    (core.num.U64.wrapping_add a ⟨BitVec.ofNat 64 n⟩).val = a.val + n := by
  have : (⟨BitVec.ofNat 64 n⟩ : U64).val = n := by show (BitVec.ofNat 64 n).toNat = n; simp; omega
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, this]; omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A TCB address: 32-byte aligned (FL4 TCBs are 4 KiB aligned), not wrapping. -/
def TcbOk (t : U64) : Prop := t.val % 32 = 0 ∧ t.val + 4096 ≤ 2 ^ 64

macro "addr_tac" : tactic => `(tactic| (simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
  U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega))

theorem flags_total : ∃ fv, regs.FLAGS_USER_DEFAULT = ok fv := by
  have h : regs.FLAGS_USER_DEFAULT ⦃ _ => True ⦄ := by
    unfold regs.FLAGS_USER_DEFAULT regs.FLAGS_IF regs.FLAGS_HIGH
    step*
  obtain ⟨v, hv, -⟩ := spec_exists h
  exact ⟨v, hv⟩

theorem set_reg_frame (s : S) (t r v : U64) (ht : TcbOk t) (hr : r.val < 24) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WFrame (L := L) s s' (InT t) ⦄ := by
  unfold obj.Tcb.set_reg
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, layout.tcb.REGS]
  obtain ⟨h1, h2⟩ := ht
  have hv : (core.num.U64.wrapping_add (core.num.U64.wrapping_add t 256#u64)
      (core.num.U64.wrapping_mul r 8#u64)).val = t.val + 256 + 8 * r.val := by addr_tac
  exact WFrame.wr s (by show _ % 8 = 0; rw [hv]; omega) (by unfold InT; rw [hv]; omega) v

theorem set_debug_reg_frame (s : S) (t r v : U64) (ht : TcbOk t) (hr : r.val < 8) :
    obj.Tcb.set_debug_reg st t s r v ⦃ s' => WFrame (L := L) s s' (InT t) ⦄ := by
  unfold obj.Tcb.set_debug_reg
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, layout.tcb.DEBUG]
  obtain ⟨h1, h2⟩ := ht
  have hv : (core.num.U64.wrapping_add (core.num.U64.wrapping_add t 448#u64)
      (core.num.U64.wrapping_mul r 8#u64)).val = t.val + 448 + 8 * r.val := by addr_tac
  exact WFrame.wr s (by show _ % 8 = 0; rw [hv]; omega) (by unfold InT; rw [hv]; omega) v

theorem init_context_frame (s : S) (t : U64) (ht : TcbOk t) :
    regs.init_context st s t ⦃ s' => WFrame (L := L) s s' (InT t) ⦄ := by
  unfold regs.init_context regs.init_context_loop
  have hloop : loop (fun (s1, i1) => regs.init_context_loop.body st t s1 i1) (s, 0#u64) ⦃ s' =>
      WFrame (L := L) s s' (InT t) ⦄ := by
    refine loop.spec_decr_nat (measure := fun x => 24 - x.2.val)
      (inv := fun x => x.2.val ≤ 24 ∧ WFrame (L := L) s x.1 (InT t)) _ _ _ ?_ ?_
    · rintro ⟨s1, i⟩ ⟨hi, hf⟩
      unfold regs.init_context_loop.body
      simp only [layout.reg.COUNT] at hi ⊢
      by_cases hit : i < 24#u64
      · rw [if_pos hit]
        have hit' : i.val < 24 := hit
        obtain ⟨s2, hs2, hf2⟩ := spec_exists (set_reg_frame (L := L) s1 t i 0#u64 ht hit')
        rw [hs2]; simp only [bind_ok]
        step as ⟨i1, hi1⟩
        exact ⟨by omega, hf.trans hf2, by omega⟩
      · rw [if_neg hit, WP.spec_ok]; exact hf
    · exact ⟨by simp, WFrame.refl s _⟩
  obtain ⟨s1, hs1, hf1⟩ := spec_exists hloop
  rw [hs1]; simp only [bind_ok]
  obtain ⟨s2, hs2, hf2⟩ := spec_exists (set_reg_frame (L := L) s1 t layout.reg.CS regs.SEL_CS_3 ht (by simp [layout.reg.CS]))
  rw [hs2]; simp only [bind_ok]
  obtain ⟨fv, hfv⟩ := flags_total
  rw [hfv]; simp only [bind_ok]
  obtain ⟨s3, hs3, hf3⟩ := spec_exists (set_reg_frame (L := L) s2 t layout.reg.FLAGS fv ht
    (by simp [layout.reg.FLAGS]))
  rw [hs3]; simp only [bind_ok]
  apply WP.spec_mono (set_reg_frame (L := L) s3 t layout.reg.SS regs.SEL_DS_3 ht (by simp [layout.reg.SS]))
  intro s4 hf4
  exact hf1.trans (hf2.trans (hf3.trans hf4))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem and63_lt (x : U64) : (x &&& 63#u64).val < 64 := by
  have : (x &&& 63#u64).val = x.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod x.val 6
  omega

theorem name_byte_total (s : S) (t i : U64) : objects.name_byte st s t i ⦃ _ => True ⦄ := by
  unfold objects.name_byte obj.Tcb.name_addr
  rw [show layout.tcb.NAME = ok 3600#u64 by unfold layout.tcb.NAME layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.read_eq]
  obtain ⟨v, hv, -⟩ := spec_exists (UScalar.ShiftRight_spec (L.mem s (core.num.U64.wrapping_add
    (core.num.U64.wrapping_add t 3600#u64) (i &&& ~~~7#u64))) (core.num.U64.wrapping_mul (i &&& 7#u64) 8#u64 &&& 63#u64)
    (by have := and63_lt (core.num.U64.wrapping_mul (i &&& 7#u64) 8#u64); rw [UScalarTy.U64_numBits_eq]; omega))
  rw [hv]; simp

theorem child_name_byte_total (s : S) (t len i : U64) : objects.child_name_byte st s t len i ⦃ _ => True ⦄ := by
  unfold objects.child_name_byte
  simp only [objects.CHILD_PREFIX_LEN, objects.CHILD_PREFIX0, objects.CHILD_PREFIX1]
  split_ifs with h1 h2 h3
  · step*
  · step*
  · step*
    exact WP.spec_mono (name_byte_total s t _) (fun _ _ => trivial)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem child_len_total (s : S) (t : U64) : objects.set_child_name_loop0 st s t 0#u64 ⦃ _ => True ⦄ := by
  unfold objects.set_child_name_loop0
  refine loop.spec_decr_nat (measure := fun x => 51 - x.val) (inv := fun x => x.val ≤ 51) _ _ _ ?_ (by simp)
  intro len hlen
  unfold objects.set_child_name_loop0.body
  simp only [objects.CHILD_NAME_MAX]
  by_cases h : len < 51#u64
  · rw [if_pos h]
    have h' : len.val < 51 := h
    obtain ⟨b, hb, -⟩ := spec_exists (name_byte_total (L := L) s t len)
    rw [hb]; simp only [bind_ok]
    split
    · step as ⟨l1, hl1⟩
      exact ⟨by omega, by omega⟩
    · simp
  · rw [if_neg h]; simp

theorem child_word_total (s : S) (t len w : U64) :
    objects.set_child_name_loop1_loop0 st s t len w 0#u64 0#u64 ⦃ _ => True ⦄ := by
  unfold objects.set_child_name_loop1_loop0
  refine loop.spec_decr_nat (measure := fun x => 8 - x.2.val) (inv := fun x => x.2.val ≤ 8) _ _ _ ?_ (by simp)
  rintro ⟨v, k⟩ hk
  unfold objects.set_child_name_loop1_loop0.body
  simp only at hk ⊢
  by_cases h : k < 8#u64
  · rw [if_pos h]
    have h' : k.val < 8 := h
    simp only [lift, bind_ok]
    obtain ⟨b, hb, -⟩ := spec_exists (child_name_byte_total (L := L) s t len
      (core.num.U64.wrapping_add (core.num.U64.wrapping_mul w 8#u64) k))
    rw [hb]; simp only [bind_ok]
    obtain ⟨v5, hv5, -⟩ := spec_exists (UScalar.ShiftLeft_spec b (core.num.U64.wrapping_mul k 8#u64 &&& 63#u64) _
      (by have := and63_lt (core.num.U64.wrapping_mul k 8#u64); rw [UScalarTy.U64_numBits_eq]; omega) rfl)
    rw [hv5]; simp only [bind_ok]
    step as ⟨k1, hk1⟩
    exact ⟨by omega, by omega⟩
  · rw [if_neg h]; simp

/-- The debug name is written in the TCB's name words. -/
theorem child_names_frame (s : S) (child parent len : U64) (ht : TcbOk child) :
    objects.set_child_name_loop1 st s child parent len 0#u64 ⦃ s' => WFrame (L := L) s s' (InT child) ⦄ := by
  unfold objects.set_child_name_loop1
  refine loop.spec_decr_nat (measure := fun x => 8 - x.2.val)
    (inv := fun x => x.2.val ≤ 8 ∧ WFrame (L := L) s x.1 (InT child)) _ _ _ ?_ ⟨by simp, WFrame.refl s _⟩
  rintro ⟨s1, w⟩ ⟨hw, hf⟩
  unfold objects.set_child_name_loop1.body
  simp only at hw hf ⊢
  by_cases h : w < 8#u64
  · rw [if_pos h]
    have h' : w.val < 8 := h
    obtain ⟨v, hv, -⟩ := spec_exists (child_word_total (L := L) s1 parent len w)
    rw [hv]; simp only [bind_ok, obj.Tcb.name_addr, lift]
    rw [show layout.tcb.NAME = ok 3600#u64 by unfold layout.tcb.NAME layout.tcb.F; rfl]
    simp only [bind_ok, L.write_eq]
    obtain ⟨h1, h2⟩ := ht
    have hv' : (core.num.U64.wrapping_add (core.num.U64.wrapping_add child 3600#u64)
        (core.num.U64.wrapping_mul w 8#u64)).val = child.val + 3600 + 8 * w.val := by addr_tac
    step as ⟨w1, hw1⟩
    exact ⟨by omega, hf.trans (WFrame.wr s1 (by show _ % 8 = 0; rw [hv']; omega) (by unfold InT; rw [hv']; omega) v),
      by omega⟩
  · rw [if_neg h, WP.spec_ok]; exact hf

theorem set_child_name_frame (s : S) (child parent : U64) (ht : TcbOk child) :
    objects.set_child_name st s child parent ⦃ s' => WFrame (L := L) s s' (InT child) ⦄ := by
  unfold objects.set_child_name
  simp only [fl4_abi.config.DEBUG_BUILD, ↓reduceIte, obj.Tcb.is_null, bind_ok]
  split
  · rw [WP.spec_ok]; exact WFrame.refl s _
  · obtain ⟨len, hl, -⟩ := spec_exists (child_len_total (L := L) s parent)
    rw [hl]; simp only [bind_ok]
    exact child_names_frame s child parent len ht

theorem init_fpu_frame (s : S) (t : U64) (ht : TcbOk t) :
    objects.init_fpu st s t ⦃ s' => WFrame (L := L) s s' (InT t) ⦄ := by
  unfold objects.init_fpu obj.Tcb.fpu_addr
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, layout.tcb.FPU]
  obtain ⟨h1, h2⟩ := ht
  have hv1 : (core.num.U64.wrapping_add t 512#u64).val = t.val + 512 := by addr_tac
  have hv2 : (core.num.U64.wrapping_add (core.num.U64.wrapping_add t 512#u64) 24#u64).val = t.val + 536 := by addr_tac
  exact (WFrame.wr s (by show _ % 8 = 0; rw [hv1]; omega) (by unfold InT; rw [hv1]; omega) _).trans
    (WFrame.wr _ (by show _ % 8 = 0; rw [hv2]; omega) (by unfold InT; rw [hv2]; omega) _)

theorem debug_init_frame (s : S) (t : U64) (ht : TcbOk t) :
    debug.init_context st s t ⦃ s' => WFrame (L := L) s s' (InT t) ⦄ := by
  unfold debug.init_context debug.init_context_loop
  have hloop : loop (fun (s1, i1) => debug.init_context_loop.body st t s1 i1) (s, 0#u64) ⦃ s' =>
      WFrame (L := L) s s' (InT t) ⦄ := by
    refine loop.spec_decr_nat (measure := fun x => 8 - x.2.val)
      (inv := fun x => x.2.val ≤ 8 ∧ WFrame (L := L) s x.1 (InT t)) _ _ _ ?_ ?_
    · rintro ⟨s1, i⟩ ⟨hi, hf⟩
      unfold debug.init_context_loop.body
      simp only at hi hf ⊢
      by_cases hit : i < 8#u64
      · rw [if_pos hit]
        have hit' : i.val < 8 := hit
        obtain ⟨s2, hs2, hf2⟩ := spec_exists (set_debug_reg_frame (L := L) s1 t i 0#u64 ht hit')
        rw [hs2]; simp only [bind_ok]
        step as ⟨i1, hi1⟩
        exact ⟨by omega, hf.trans hf2, by omega⟩
      · rw [if_neg hit, WP.spec_ok]; exact hf
    · exact ⟨by simp, WFrame.refl s _⟩
  obtain ⟨s1, hs1, hf1⟩ := spec_exists hloop
  rw [hs1]; simp only [bind_ok]
  obtain ⟨s2, hs2, hf2⟩ := spec_exists (set_debug_reg_frame (L := L) s1 t debug.DR6 4294905840#u64 ht
    (by simp [debug.DR6]))
  rw [hs2]; simp only [bind_ok]
  exact WP.spec_mono (set_debug_reg_frame (L := L) s2 t debug.DR7 1024#u64 ht (by simp [debug.DR7]))
    (fun s3 hf3 => hf1.trans (hf2.trans hf3))

theorem set_domain_frame (s : S) (t v : U64) (ht : TcbOk t) :
    obj.Tcb.set_domain st t s v ⦃ s' => WFrame (L := L) s s' (InT t) ⦄ := by
  unfold obj.Tcb.set_domain
  rw [show layout.tcb.DOMAIN = ok 3432#u64 by unfold layout.tcb.DOMAIN layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok]
  obtain ⟨h1, h2⟩ := ht
  have hv : (core.num.U64.wrapping_add t 3432#u64).val = t.val + 3432 := by addr_tac
  exact WFrame.wr s (by show _ % 8 = 0; rw [hv]; omega) (by unfold InT; rw [hv]; omega) v

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The core whose debug list a new TCB joins (its affinity word). -/
def tcbCpu (s : S) (t : U64) : U64 := L.mem s (core.num.U64.wrapping_add t 3520#u64)
/-- That core's debug-list head word. -/
def dbgW (s : S) (t : U64) : U64 := L.nodeAt s (tcbCpu (L := L) s t) layout.node.DEBUG_TCBS
/-- The words `create_object` may write for a new TCB `t`: past its slots,
the old list head's `debug_prev` word, and the list-head word. -/
def TcbW (s : S) (t w : U64) : Prop :=
  InT t w ∨ (L.mem s (dbgW (L := L) s t) ≠ 0#u64 ∧ w.val = (L.mem s (dbgW (L := L) s t)).val + 3584) ∨
    w.val = (dbgW (L := L) s t).val

theorem nodeAt_ksb {s s' : S} (h : L.ksb s' = L.ksb s) (cpu off : U64) : L.nodeAt s' cpu off = L.nodeAt s cpu off := by
  unfold P1.LawfulStore.nodeAt; rw [h]

theorem debug_append_frame (s : S) (t : U64) (ht : TcbOk t) (hna : P1.Aligned (dbgW (L := L) s t))
    (hhd : L.mem s (dbgW (L := L) s t) ≠ 0#u64 → TcbOk (L.mem s (dbgW (L := L) s t))) :
    objects.debug_append st s t ⦃ s' => WFrame (L := L) s s' (TcbW (L := L) s t) ∧
      L.mem s' (dbgW (L := L) s t) = t ⦄ := by
  unfold objects.debug_append obj.Tcb.affinity
  rw [show layout.tcb.AFFINITY = ok 3520#u64 by unfold layout.tcb.AFFINITY layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.read_eq]
  rw [spec_eq_ok (Fl4Proofs.P1.obj.node_get.spec (L := L) s (L.mem s (core.num.U64.wrapping_add t 3520#u64))
    layout.node.DEBUG_TCBS)]
  simp only [bind_ok, obj.Tcb.set_debug_prev, obj.Tcb.set_debug_next, lift, L.write_eq,
    show layout.tcb.DEBUG_PREV = ok 3584#u64 by unfold layout.tcb.DEBUG_PREV layout.tcb.F; rfl,
    show layout.tcb.DEBUG_NEXT = ok 3576#u64 by unfold layout.tcb.DEBUG_NEXT layout.tcb.F; rfl]
  have hdw : L.nodeAt s (L.mem s (core.num.U64.wrapping_add t 3520#u64)) layout.node.DEBUG_TCBS = dbgW (L := L) s t := rfl
  rw [hdw]
  obtain ⟨h1, h2⟩ := ht
  have hv1 : (core.num.U64.wrapping_add t 3584#u64).val = t.val + 3584 := by addr_tac
  have hv2 : (core.num.U64.wrapping_add t 3576#u64).val = t.val + 3576 := by addr_tac
  have f1 : WFrame (L := L) s (L.wr s (core.num.U64.wrapping_add t 3584#u64) 0#u64) (TcbW (L := L) s t) :=
    WFrame.wr s (by show _ % 8 = 0; rw [hv1]; omega) (Or.inl (by unfold InT; rw [hv1]; omega)) _
  set s1 := L.wr s (core.num.U64.wrapping_add t 3584#u64) 0#u64
  have f2 : WFrame (L := L) s1 (L.wr s1 (core.num.U64.wrapping_add t 3576#u64) (L.mem s (dbgW (L := L) s t)))
      (TcbW (L := L) s t) :=
    WFrame.wr s1 (by show _ % 8 = 0; rw [hv2]; omega) (Or.inl (by unfold InT; rw [hv2]; omega)) _
  set s2 := L.wr s1 (core.num.U64.wrapping_add t 3576#u64) (L.mem s (dbgW (L := L) s t))
  have f12 := f1.trans f2
  have hlast : ∀ s3 : S, WFrame (L := L) s s3 (TcbW (L := L) s t) →
      obj.node_set st s3 (L.mem s (core.num.U64.wrapping_add t 3520#u64)) layout.node.DEBUG_TCBS t ⦃ s' =>
        WFrame (L := L) s s' (TcbW (L := L) s t) ∧ L.mem s' (dbgW (L := L) s t) = t ⦄ := by
    intro s3 hf3
    apply WP.spec_mono (Fl4Proofs.P1.obj.node_set.spec (L := L) s3 _ _ t)
    rintro s' rfl
    rw [nodeAt_ksb hf3.1]
    exact ⟨hf3.trans (WFrame.wr s3 hna (Or.inr (Or.inr rfl)) t), L.mem_wr_same hna⟩
  by_cases hh : L.mem s (dbgW (L := L) s t) = 0#u64
  · have : (L.mem s (dbgW (L := L) s t) != 0#u64) = false := by simp [hh]
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair]
    exact hlast s2 f12
  · have : (L.mem s (dbgW (L := L) s t) != 0#u64) = true := by simp [hh]
    simp only [this, ↓reduceIte, bind_ok, uncurry_apply_pair]
    obtain ⟨g1, g2⟩ := hhd hh
    have hv3 : (core.num.U64.wrapping_add (L.mem s (dbgW (L := L) s t)) 3584#u64).val =
        (L.mem s (dbgW (L := L) s t)).val + 3584 := by addr_tac
    apply hlast
    exact f12.trans (WFrame.wr s2 (by show _ % 8 = 0; rw [hv3]; omega) (Or.inr (Or.inl ⟨hh, hv3⟩)) t)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem cur_domain_total (s : S) : sched.cur_domain st s ⦃ _ => True ⦄ := by
  unfold sched.cur_domain obj.ks_get; step*

/-- **`create_object` for a TCB**: it returns the thread cap, keeps the
arch state, and writes only the words `TcbW` (past the new TCB's slots, the
old debug-list head's `debug_prev` word, and the list-head word). -/
theorem create_tcb_frame {A' : Type} (arI : machine.Arch A') (s : S) (ar : A') (nt base us : U64) (dev : Bool)
    (hnt : nt.val = 1) (ht : TcbOk base) (hna : P1.Aligned (dbgW (L := L) s base))
    (hhd : L.mem s (dbgW (L := L) s base) ≠ 0#u64 → TcbOk (L.mem s (dbgW (L := L) s base)))
    (hout : ¬ InT base (dbgW (L := L) s base)) :
    objects.create_object st arI s ar nt base us dev ⦃ res =>
      res.1 = .Thread base ∧ res.2.2 = ar ∧ WFrame (L := L) s res.2.1 (TcbW (L := L) s base) ∧
      L.mem res.2.1 (dbgW (L := L) s base) = base ⦄ := by
  have h14 : nt ≠ 14#u64 := by scalar_tac
  have h15 : ¬ nt ≥ 15#u64 := by scalar_tac
  unfold objects.create_object
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.X86EptPml4, h14, h15, ↓reduceIte]
  have h1 : nt = fl4_abi.consts.object.Tcb := UScalar.eq_of_val_eq (by rw [hnt]; simp [fl4_abi.consts.object.Tcb])
  rw [if_pos h1]
  obtain ⟨s1, hs1, f1⟩ := spec_exists (init_context_frame (L := L) s base ht)
  rw [hs1]; simp only [bind_ok]
  obtain ⟨s2, hs2, f2⟩ := spec_exists (init_fpu_frame (L := L) s1 base ht)
  rw [hs2]; simp only [bind_ok]
  obtain ⟨s3, hs3, f3⟩ := spec_exists (debug_init_frame (L := L) s2 base ht)
  rw [hs3]; simp only [bind_ok]
  obtain ⟨d, hd, -⟩ := spec_exists (cur_domain_total (L := L) s3)
  rw [hd]; simp only [bind_ok]
  obtain ⟨s4, hs4, f4⟩ := spec_exists (set_domain_frame (L := L) s3 base d ht)
  rw [hs4]; simp only [bind_ok]
  obtain ⟨ct, hct, -⟩ := spec_exists (cur_thread_spec' (L := L) s4)
  rw [hct]; simp only [bind_ok]
  obtain ⟨s5, hs5, f5⟩ := spec_exists (set_child_name_frame (L := L) s4 base ct ht)
  rw [hs5]; simp only [bind_ok]
  have f := f1.trans (f2.trans (f3.trans (f4.trans f5)))
  -- the debug list, as seen from `s5`
  have hcpu : tcbCpu (L := L) s5 base = tcbCpu (L := L) s base := by
    unfold tcbCpu
    obtain ⟨g1, g2⟩ := ht
    have hv : (core.num.U64.wrapping_add base 3520#u64).val = base.val + 3520 := by addr_tac
    exact f.2 _ (by show _ % 8 = 0; rw [hv]; omega) (by unfold InT; rw [hv]; omega)
  have hdw : dbgW (L := L) s5 base = dbgW (L := L) s base := by
    unfold dbgW; rw [hcpu, nodeAt_ksb f.1]
  have hhv : L.mem s5 (dbgW (L := L) s5 base) = L.mem s (dbgW (L := L) s base) := by
    rw [hdw]; exact f.2 _ hna hout
  have hW : ∀ w, TcbW (L := L) s5 base w ↔ TcbW (L := L) s base w := by
    intro w; unfold TcbW; rw [hhv, hdw]
  obtain ⟨s6, hs6, f6⟩ := spec_exists (debug_append_frame (L := L) s5 base ht (by rw [hdw]; exact hna)
    (by rw [hhv]; exact hhd))
  rw [hs6]; simp only [bind_ok, WP.spec_ok]
  exact ⟨trivial, trivial, (f.mono (fun w h => Or.inl h)).trans (f6.1.mono (fun w h => (hW w).1 h)),
    by rw [← hdw]; exact f6.2⟩

end

theorem tcbCnodeMap_default (d : Fl4Spec.Domain) (i : Nat) (hi : i < tcbSlots) :
    Fl4Spec.tcbCnodeMap (Fl4Spec.defaultTcb d) (Fl4Spec.tcbCnodeIndex i) = some .nullCap := by
  simp only [tcbSlots] at hi
  interval_cases i <;> simp [Fl4Spec.tcbCnodeMap, Fl4Spec.defaultTcb, Function.update_apply] <;> split_ifs <;> rfl

theorem IsSlotAt.of_extend_tcb {th : TypedHeap} {A k n : Nat} {p : U64} {i : Nat}
    (h : IsSlotAt (extendTh th A k n .tcb) p i) :
    IsSlotAt th p i ∨ (NewP A k n p ∧ i < tcbSlots) := by
  by_cases hp : NewP A k n p
  · rcases h with ⟨r, hr, hi⟩ | ⟨ht, hi⟩
    · rw [extendTh_new hp] at hr; cases hr
    · exact Or.inr ⟨hp, hi⟩
  · left
    rcases h with ⟨r, hr, hi⟩ | ⟨ht, hi⟩
    · rw [extendTh_old hp] at hr; exact Or.inl ⟨r, hr, hi⟩
    · rw [extendTh_old hp] at ht; exact Or.inr ⟨ht, hi⟩

theorem AbsSlot.of_extend_tcb {th : TypedHeap} {A k n : Nat} {sl : Fl4Spec.CslotPtr}
    (h : AbsSlot (extendTh th A k n .tcb) sl) (hn : ¬ AbsSlot th sl) :
    ∃ p, NewP A k n p ∧ sl.1 = p.bv ∧ ∃ i, i < tcbSlots ∧ sl.2 = Fl4Spec.tcbCnodeIndex i := by
  obtain ⟨p, h1, h2 | ⟨ht, hi⟩⟩ := h
  · by_cases hp : NewP A k n p
    · rw [extendTh_new hp] at h2; cases h2
    · rw [extendTh_old hp] at h2; exact absurd ⟨p, h1, Or.inl h2⟩ hn
  · by_cases hp : NewP A k n p
    · exact ⟨p, hp, h1, hi⟩
    · rw [extendTh_old hp] at ht; exact absurd ⟨p, h1, Or.inr ⟨ht, hi⟩⟩ hn

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **After `retype_region` of `n` TCBs** (4 KiB, FL4) from `A` in a free,
zeroed region: the typed heap grown by the new TCBs is `Placed`, and the
relations hold against the spec's heap with `default_tcb` objects (whose cap
slots are null, as the zero slots read). -/
theorem extend_tcb_rel (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) (hP : Placed th)
    (hM : MdbLinks th mem G) (hC : CdtRel th mem σ G)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ptr : Fl4Spec.ObjRef) (A n : Nat) (hA : ptr.toNat = A) (d : Fl4Spec.Domain)
    (hfit : A + n * 4096 ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ A) (hal : A % 32 = 0)
    (hfree : RegionFree th A (A + n * 4096)) (hzero : ZeroRegion mem A (A + n * 4096)) :
    Placed (extendTh th A 4096 n .tcb) ∧
    StateRel (extendTh th A 4096 n .tcb) mem (regionHeap σ (regionPtrs ptr n 4096) (.tcb (Fl4Spec.defaultTcb d))) ∧
    SlotsValid (extendTh th A 4096 n .tcb) mem ∧
    MdbLinks (extendTh th A 4096 n .tcb) mem G ∧
    CdtRel (extendTh th A 4096 n .tcb) mem (regionHeap σ (regionPtrs ptr n 4096) (.tcb (Fl4Spec.defaultTcb d))) G := by
  set k := 4096 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hP' : Placed (extendTh th A k n .tcb) := Placed.extend hP hfree (le_refl _) (le_refl _) hfit hhigh hal (by omega) (by simp [objSize, k])
  have hmemP := mem_regionPtrs ptr A k n hA hk1 hfit
  -- the words of a new CNode are zero
  have hnewz : ∀ p, NewP A k n p → ∀ i, i < tcbSlots → ∀ off : Nat, off < 32 → off % 8 = 0 →
      ∀ a : U64, a.val = p.val + 32 * i + off → mem a = 0#u64 := by
    rintro p ⟨j, hj, hpj⟩ i hi off hoff ho8 a ha
    have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : 32 * (i + 1) ≤ k := by simp [tcbSlots] at hi; omega
    have h3 : j * k = 32 * (j * 128) := by rw [hkdef]; ring
    apply hzero a (by show a.val % 8 = 0; omega) <;> omega
  have hslotv : ∀ p, NewP A k n p → ∀ i, i < tcbSlots → (slotOf p i).val = p.val + 32 * i := by
    rintro p ⟨j, hj, hpj⟩ i hi
    have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : 32 * (i + 1) ≤ k := by simp [tcbSlots] at hi; omega
    exact slotOf_val (by omega)
  have hbnd : ∀ p, NewP A k n p → ∀ i, i < tcbSlots → p.val + 32 * i + 32 ≤ 2 ^ 64 := by
    rintro p ⟨j, hj, hpj⟩ i hi
    have h1 : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : 32 * (i + 1) ≤ k := by simp [tcbSlots] at hi; omega
    omega
  have hnull : ∀ p, NewP A k n p → ∀ i, i < tcbSlots → capAt mem (slotOf p i) = ok .Null := by
    intro p hp i hi
    have hv := hslotv p hp i hi
    have hb := hbnd p hp i hi
    rw [capAt_words, hnewz p hp i hi 0 (by decide) (by decide) _ (by rw [wordOf_zero, hv]; rfl),
      hnewz p hp i hi 8 (by decide) (by decide) _ (by rw [slot_word_val_of hv off8 (by omega)]; rfl)]
    exact decode_encode_null.2
  have hrevz : ∀ p, NewP A k n p → ∀ i, i < tcbSlots → revOf mem (slotOf p i) = false := by
    intro p hp i hi
    have hb := hbnd p hp i hi
    unfold revOf
    rw [hnewz p hp i hi 24 (by decide) (by decide) _ (by rw [slot_word_val_of (hslotv p hp i hi) off24 (by omega)]; rfl)]
    rfl
  have hkh : ∀ q : U64, (regionHeap σ (regionPtrs ptr n k) (.tcb (Fl4Spec.defaultTcb d))).kheap q.bv =
      if NewP A k n q then some (.tcb (Fl4Spec.defaultTcb d)) else σ.kheap q.bv := by
    intro q
    simp only [regionHeap]
    rw [foldr_update_apply]
    by_cases h : NewP A k n q
    · rw [if_pos ((hmemP q).2 h), if_pos h]
    · rw [if_neg (fun e => h ((hmemP q).1 e)), if_neg h]
  refine ⟨hP', ?_, ?_, ?_, ?_⟩
  · refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
    · by_cases hn : NewP A k n p
      · rw [extendTh_new hn] at hp; cases hp
      · rw [extendTh_old hn] at hp
        rw [hkh, if_neg hn]; exact hR.cnode p r hp
    · by_cases hn : NewP A k n t
      · refine ⟨Fl4Spec.defaultTcb d, by rw [hkh, if_pos hn], fun i hi => ?_⟩
        exact ⟨.Null, .nullCap, hnull t hn i hi, tcbCnodeMap_default d i hi, ⟨trivial, rfl⟩⟩
      · rw [extendTh_old hn] at ht
        rw [hkh, if_neg hn]; exact hR.tcb t ht
  · refine ⟨fun p r hp i hi c hc => ?_, fun t ht i hi c hc => ?_⟩
    · by_cases hn : NewP A k n p
      · rw [extendTh_new hn] at hp; cases hp
      · rw [extendTh_old hn] at hp
        exact (hV.cnode p r hp i hi c hc).extend hk1 hfree
    · by_cases hn : NewP A k n t
      · change capAt mem (slotOf t i) = _ at hc
        rw [hnull t hn i hi] at hc
        rw [← eq_of_ok_eq hc]; trivial
      · rw [extendTh_old hn] at ht
        exact (hV.tcb t ht i hi c hc).extend hk1 hfree
  · refine ⟨hM.tree, hM.ne_nil, hM.chain, hM.head, hM.last, fun a => ?_⟩
    rw [hM.members a]
    constructor
    · rintro ⟨ha, hc⟩; exact ⟨ha.extend hk1 hfree, hc⟩
    · rintro ⟨⟨p, i, hi, rfl⟩, c, hc, hcn⟩
      rcases hi.of_extend_tcb with hi | ⟨hn, hi⟩
      · exact ⟨⟨p, i, hi, rfl⟩, c, hc, hcn⟩
      · rw [hnull p hn i hi] at hc; exact absurd (eq_of_ok_eq hc).symm hcn
  · have hnew : ∀ sl, AbsSlot (extendTh th A k n .tcb) sl → ¬ AbsSlot th sl →
        ∃ p, NewP A k n p ∧ sl.1 = p.bv ∧ cslotAddr sl = slotOf p (blVal 0 sl.2) ∧ blVal 0 sl.2 < tcbSlots := by
      intro sl h1 h2
      obtain ⟨p, hp, e1, i, hi, e2⟩ := h1.of_extend_tcb h2
      refine ⟨p, hp, e1, ?_, by rw [e2, tcbCnodeIndex_blVal i hi]; exact hi⟩
      obtain ⟨a, b⟩ := sl; simp only at e1 e2 ⊢; subst e1; exact slotAddr_ofBl _ _
    refine ⟨fun sl hsl => ?_, fun sl q hq => ?_, fun sl hsl => ?_, fun a b hab => ?_⟩
    · by_cases ho : AbsSlot th sl
      · exact hC.cdt sl ho
      · show (σ.cdt sl).map cslotAddr = _
        have h1 : σ.cdt sl = none := by
          cases e : σ.cdt sl with
          | none => rfl
          | some q => exact absurd (hC.cdt_slot sl q e).1 ho
        have h2 : G.par (cslotAddr sl) = none := by
          cases e : G.par (cslotAddr sl) with
          | none => rfl
          | some b =>
            obtain ⟨sl0, h0, he⟩ := hC.par_slot _ b e
            exact absurd (cslotAddr_inj hP' (h0.extend hk1 hfree) hsl he ▸ h0) ho
        rw [h1, h2]; rfl
    · obtain ⟨h1, h2⟩ := hC.cdt_slot sl q hq
      exact ⟨h1.extend hk1 hfree, h2.extend hk1 hfree⟩
    · by_cases ho : AbsSlot th sl
      · exact hC.orig sl ho
      · obtain ⟨p, hp, -, he, hi⟩ := hnew sl hsl ho
        show σ.isOriginalCap sl = _
        rw [he, hrevz p hp _ hi]
        cases e : σ.isOriginalCap sl
        · rfl
        · exact absurd (horig sl e) ho
    · obtain ⟨sl, h1, h2⟩ := hC.par_slot a b hab
      exact ⟨sl, h1.extend hk1 hfree, h2⟩


end

end
end Fl4Proofs.P3
