/-
P1 (DESIGN.md §9): the store laws invariant proofs rely on.

P0 assumes only that the `Store` never fails (`StoreTotal`). Invariant
preservation needs more: memory behaves as a map from aligned 64-bit word
addresses to words, and `ks_base` and `cur_cpu` do not change under
writes. `LawfulStore st` packages a functional view of `st` (`mem`, `wr`,
`zr`, `ksb`, `cpu`) with the laws that tie it to the monadic operations.

The laws only talk about aligned addresses (`machine.rs`: "Read the
aligned word at `addr`"), and `zero` only about ranges that do not wrap
around the address space, so any word-addressed memory is a model.
-/
import Fl4Proofs.P0.Totality
import Fl4Proofs.P1.SyscallGen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

/-- A word address the laws talk about. -/
abbrev Aligned (a : U64) : Prop := a.val % 8 = 0

/-- A law-abiding store, with its functional view. The view is determined
by `st` (the `*_eq` fields), so carrying it as data loses nothing. It is a
class so that `step` finds it (by instance resolution) when it applies the
specs below; proofs take it as `[L : LawfulStore st]` and write `L.mem`. -/
class LawfulStore {S : Type _} (st : machine.Store S) where
  frame_masks_total : ∀ s, st.frame_masks s ⦃ _ => True ⦄
  mem : S → U64 → U64
  wr : S → U64 → U64 → S
  zr : S → U64 → U64 → S
  ksb : S → U64
  cpu : S → U64
  read_eq : ∀ s a, st.read s a = ok (mem s a)
  read_pair_eq : ∀ s a, st.read_pair s a = ok (mem s a, mem s (core.num.U64.wrapping_add a 8#u64))
  write_eq : ∀ s a v, st.write s a v = ok (wr s a v)
  zero_eq : ∀ s a n, st.zero s a n = ok (zr s a n)
  /-- `clear_free` (memory no live object occupies) has `zero`'s effect;
  only the runtime treats it differently. -/
  clear_free_eq : ∀ s a n, st.clear_free s a n = ok (zr s a n)
  ks_base_eq : ∀ s, st.ks_base s = ok (ksb s)
  cur_cpu_eq : ∀ s, st.cur_cpu s = ok (cpu s)
  /-- Read after write, on aligned words. -/
  mem_wr : ∀ s a v b, Aligned a → Aligned b →
    mem (wr s a v) b = if a = b then v else mem s b
  /-- `zero s a n` clears the words of `[a, a + n)`, for an aligned range
  that does not wrap. -/
  mem_zr : ∀ s a n b, Aligned a → n.val % 8 = 0 → a.val + n.val ≤ 2 ^ 64 → Aligned b →
    mem (zr s a n) b = if a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else mem s b
  ksb_wr : ∀ s a v, ksb (wr s a v) = ksb s
  cpu_wr : ∀ s a v, cpu (wr s a v) = cpu s
  ksb_zr : ∀ s a n, ksb (zr s a n) = ksb s
  cpu_zr : ∀ s a n, cpu (zr s a n) = cpu s

/-- The native address format used by l4v's page and untyped refinements. -/
class PlainStore {S : Type _} (st : machine.Store S) : Prop where
  frame_masks_eq : ∀ s, st.frame_masks s = ok (0#u64, 0#u64)

@[simp] theorem plain_sharing {S : Type _} {st : machine.Store S} [PlainStore st] (s : S) :
    machine.sharing_enabled st s = ok false := by
  simp [machine.sharing_enabled, PlainStore.frame_masks_eq, lift]

@[simp] theorem plain_retire {S A : Type _} {st : machine.Store S} [PlainStore st] (ar : machine.Arch A)
    (s : S) (a : A) (p : U64) (sz : capability.FrameSize) : objects.retire_dma_frame st ar s a p sz = ok a := by
  simp [objects.retire_dma_frame]

attribute [simp] LawfulStore.ksb_wr LawfulStore.cpu_wr LawfulStore.ksb_zr LawfulStore.cpu_zr

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem LawfulStore.total : P0.StoreTotal st where
  frame_masks := L.frame_masks_total
  read s a := by rw [L.read_eq]; simp
  read_pair s a := by rw [L.read_pair_eq]; simp
  write s a v := by rw [L.write_eq]; simp
  zero s a n := by rw [L.zero_eq]; simp
  clear_free s a n := by rw [L.clear_free_eq]; simp
  ks_base s := by rw [L.ks_base_eq]; simp
  cur_cpu s := by rw [L.cur_cpu_eq]; simp

/-! WP specs for the primitive operations, for `step`. -/

@[step] theorem LawfulStore.read_spec s a : st.read s a ⦃ v => v = L.mem s a ⦄ := by
  rw [L.read_eq]; simp
@[step] theorem LawfulStore.read_pair_spec s a :
    st.read_pair s a ⦃ v => v = (L.mem s a, L.mem s (core.num.U64.wrapping_add a 8#u64)) ⦄ := by
  rw [L.read_pair_eq]; simp
@[step] theorem LawfulStore.write_spec s a v : st.write s a v ⦃ s' => s' = L.wr s a v ⦄ := by
  rw [L.write_eq]; simp
@[step] theorem LawfulStore.zero_spec s a n : st.zero s a n ⦃ s' => s' = L.zr s a n ⦄ := by
  rw [L.zero_eq]; simp
@[step] theorem LawfulStore.clear_free_spec s a n : st.clear_free s a n ⦃ s' => s' = L.zr s a n ⦄ := by
  rw [L.clear_free_eq]; simp
@[step] theorem LawfulStore.ks_base_spec s : st.ks_base s ⦃ v => v = L.ksb s ⦄ := by
  rw [L.ks_base_eq]; simp
@[step] theorem LawfulStore.cur_cpu_spec s : st.cur_cpu s ⦃ v => v = L.cpu s ⦄ := by
  rw [L.cur_cpu_eq]; simp

/-! Read after write, in the forms proofs use. -/

theorem LawfulStore.mem_wr_same {s a v} (ha : Aligned a) : L.mem (L.wr s a v) a = v := by
  rw [L.mem_wr s a v a ha ha]; simp

theorem LawfulStore.mem_wr_ne {s a v b} (ha : Aligned a) (hb : Aligned b) (hne : a.val ≠ b.val) :
    L.mem (L.wr s a v) b = L.mem s b := by
  rw [L.mem_wr s a v b ha hb]
  have : a ≠ b := fun h => hne (congrArg UScalar.val h)
  simp [this]

theorem LawfulStore.mem_wr_val {s a v b} (ha : Aligned a) (hb : Aligned b) :
    L.mem (L.wr s a v) b = if a.val = b.val then v else L.mem s b := by
  rw [L.mem_wr s a v b ha hb]
  by_cases h : a = b
  · subst h; simp
  · have : a.val ≠ b.val := fun h' => h (UScalar.eq_of_val_eq h')
    simp [h, this]

theorem LawfulStore.mem_zr_out {s a n b} (ha : Aligned a) (hn : n.val % 8 = 0)
    (hfit : a.val + n.val ≤ 2 ^ 64) (hb : Aligned b) (hout : b.val < a.val ∨ a.val + n.val ≤ b.val) :
    L.mem (L.zr s a n) b = L.mem s b := by
  rw [L.mem_zr s a n b ha hn hfit hb]
  have : ¬ (a.val ≤ b.val ∧ b.val < a.val + n.val) := by omega
  simp only [this, ite_false]

theorem LawfulStore.mem_zr_in {s a n b} (ha : Aligned a) (hn : n.val % 8 = 0)
    (hfit : a.val + n.val ≤ 2 ^ 64) (hb : Aligned b) (hin : a.val ≤ b.val ∧ b.val < a.val + n.val) :
    L.mem (L.zr s a n) b = 0#u64 := by
  rw [L.mem_zr s a n b ha hn hfit hb]; simp only [hin, and_self, ite_true]

/-! Frames: what a sequence of writes leaves alone. -/

/-- `s'` agrees with `s` on every aligned word outside `[lo, lo + len)`, and
on `ks_base` and `cur_cpu`. -/
def LawfulStore.FrameOut (s s' : S) (lo len : Nat) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
  ∀ b : U64, Aligned b → (b.val < lo ∨ lo + len ≤ b.val) → L.mem s' b = L.mem s b

theorem LawfulStore.FrameOut.refl (s : S) lo len : L.FrameOut s s lo len :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem LawfulStore.FrameOut.trans {s₁ s₂ s₃ : S} {lo len}
    (h₁ : L.FrameOut s₁ s₂ lo len) (h₂ : L.FrameOut s₂ s₃ lo len) : L.FrameOut s₁ s₃ lo len :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun b hb hout => (h₂.2.2 b hb hout).trans (h₁.2.2 b hb hout)⟩

theorem LawfulStore.FrameOut.wr {s : S} {a v lo len} (ha : Aligned a) (hin : lo ≤ a.val ∧ a.val < lo + len) :
    L.FrameOut s (L.wr s a v) lo len := by
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hout => L.mem_wr_ne ha hb ?_⟩
  omega

end

/-! The laws are consistent: a plain map from words to words is a model
(the zeroed range is checked on word addresses, as the laws require). -/

/-- Memory, `ks_base` and `cur_cpu`. -/
abbrev ModelState := (U64 → U64) × U64 × U64

def modelStoreWithMasks (masks : U64 × U64) : machine.Store ModelState where
  frame_masks _ := ok masks
  read s a := ok (s.1 a)
  read_pair s a := ok (s.1 a, s.1 (core.num.U64.wrapping_add a 8#u64))
  write s a v := ok (Function.update s.1 a v, s.2)
  zero s a n := ok (fun b => if a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else s.1 b, s.2)
  clear_free s a n := ok (fun b => if a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else s.1 b, s.2)
  ks_base s := ok s.2.1
  cur_cpu s := ok s.2.2

abbrev modelStore := modelStoreWithMasks (0#u64, 0#u64)

instance : PlainStore modelStore where
  frame_masks_eq _ := rfl

instance (masks : U64 × U64) : LawfulStore (modelStoreWithMasks masks) where
  frame_masks_total _ := by simp [modelStoreWithMasks]
  mem s a := s.1 a
  wr s a v := (Function.update s.1 a v, s.2)
  zr s a n := (fun b => if a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else s.1 b, s.2)
  ksb s := s.2.1
  cpu s := s.2.2
  read_eq _ _ := rfl
  read_pair_eq _ _ := rfl
  write_eq _ _ _ := rfl
  zero_eq _ _ _ := rfl
  clear_free_eq _ _ _ := rfl
  ks_base_eq _ := rfl
  cur_cpu_eq _ := rfl
  mem_wr s a v b _ _ := by
    simp only [Function.update_apply]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  mem_zr _ _ _ _ _ _ _ _ := rfl
  ksb_wr _ _ _ := rfl
  cpu_wr _ _ _ := rfl
  ksb_zr _ _ _ := rfl
  cpu_zr _ _ _ := rfl

end Fl4Proofs.P1
