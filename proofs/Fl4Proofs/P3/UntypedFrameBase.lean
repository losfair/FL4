/-
P3: **word-level write frames**, the base (for retype's frame, P1's
`RetypeP1Step`): `WFrame`, the slot words `SlotSpan`, the zeroing and cap-write
frames, and the object loop of the types whose objects need no
initialisation (`create_loop_frame`: only slot words written).
-/
import Fl4Proofs.P3.UntypedExp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The words of a typed heap's slots. -/
def SlotSpan (th : TypedHeap) (w : U64) : Prop := ∃ a, IsSlot th a ∧ a.val ≤ w.val ∧ w.val < a.val + 32

/-- The words of a TCB that creating it writes: past its cap slots, the
context (below `F`), the domain (`F + 104`), the debug links (`F + 248`,
`F + 256`) and the name (from `F + 272`); not its affinity word (offset
3520, which `debug_append` reads) nor its other scheduler fields, nor its
VCPU word (offset 3664, just past the name; KENTRY-PLAN g2b). -/
def InT (t w : U64) : Prop := t.val + 256 ≤ w.val ∧ w.val < t.val + 4096 ∧ w.val ≠ t.val + 3520 ∧
  (w.val < t.val + 3328 ∨ w.val = t.val + 3432 ∨ w.val = t.val + 3576 ∨ w.val = t.val + 3584 ∨
    (t.val + 3600 ≤ w.val ∧ w.val ≠ t.val + 3664))

/-- The words the TCB loop may write: slot words, the new TCBs' creation
words (`InT`), the debug-list head word `DW`, and the old head's
`debug_prev` word. -/
def TcbLoopW (th : TypedHeap) (A win : Nat) (DW h0 : U64) (w : U64) : Prop :=
  SlotSpan th w ∨ (∃ j, j < win ∧ InT ⟨BitVec.ofNat 64 (A + j * 4096)⟩ w) ∨ w = DW ∨
    (h0 ≠ 0#u64 ∧ w.val = h0.val + 3584)

/-- **The window after a retype** (P1's `WinInit`): its aligned words zero,
but, when `T` (TCBs), the new TCBs' creation words (`InT` of
`A + j * 4096`). -/
def WinZero (m : U64 → U64) (A k win : Nat) (T : Prop) : Prop :=
  ∀ w : U64, P1.Aligned w → A ≤ w.val → w.val < A + win * k →
    m w = 0#u64 ∨ (T ∧ ∃ j, j < win ∧ InT ⟨BitVec.ofNat 64 (A + j * 4096)⟩ w)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_cap_kc (sl : obj.Slot) (s : S) (c : capability.Cap) :
    obj.Slot.set_cap st sl s c ⦃ s' => L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ⦄ :=
  WP.spec_mono (set_cap_spec (L := L) sl s c) (by rintro _ rfl; simp)

theorem insert_new_cap_kc (s : S) (src dest : U64) (c : capability.Cap) :
    cdt.insert_new_cap st s src dest c ⦃ s' => L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ⦄ := by
  unfold cdt.insert_new_cap
  step
  obtain ⟨s1, h1, k1⟩ := spec_exists (set_cap_kc (L := L) dest s c)
  rw [h1]; simp only [bind_ok]
  step; step
  simp only [obj.Slot.is_null, bind_ok]
  by_cases hz0 : next = 0#u64
  · simp only [hz0, decide_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all
  · simp only [hz0, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all


/-- `s'` differs from `s` at most in the aligned words satisfying `P` (and has
the same kernel-state base). -/
def WFrame (s s' : S) (P : U64 → Prop) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧ ∀ w : U64, P1.Aligned w → ¬ P w → L.mem s' w = L.mem s w

theorem WFrame.refl (s : S) (P : U64 → Prop) : WFrame (L := L) s s P := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem WFrame.trans {s1 s2 s3 : S} {P : U64 → Prop} (h1 : WFrame (L := L) s1 s2 P) (h2 : WFrame (L := L) s2 s3 P) :
    WFrame (L := L) s1 s3 P := ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun w hw hp => (h2.2.2 w hw hp).trans (h1.2.2 w hw hp)⟩

theorem WFrame.mono {s1 s2 : S} {P Q : U64 → Prop} (h : WFrame (L := L) s1 s2 P) (hpq : ∀ w, P w → Q w) :
    WFrame (L := L) s1 s2 Q := ⟨h.1, h.2.1, fun w hw hq => h.2.2 w hw (fun hp => hq (hpq w hp))⟩

theorem WFrame.wr (s : S) {P : U64 → Prop} {a : U64} (ha : P1.Aligned a) (hp : P a) (v : U64) :
    WFrame (L := L) s (L.wr s a v) P := by
  refine ⟨by simp, by simp, fun w hw hnp => ?_⟩
  apply L.mem_wr_ne ha hw
  intro e; exact hnp (by rw [show w = a from UScalar.eq_of_val_eq e.symm]; exact hp)

theorem zr_frame (s : S) (a n : U64) (ha : P1.Aligned a) (hn : n.val % 8 = 0) (hf : a.val + n.val ≤ 2 ^ 64) :
    WFrame (L := L) s (L.zr s a n) (fun w => a.val ≤ w.val ∧ w.val < a.val + n.val) :=
  ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun w hw hnp => by rw [L.mem_zr s a n w ha hn hf hw, if_neg hnp]⟩

theorem set_cap_frame (s : S) (x : U64) (c : capability.Cap) (hx : x.val % 8 = 0) (hxf : x.val + 16 ≤ 2 ^ 64) :
    obj.Slot.set_cap st x s c ⦃ s' => WFrame (L := L) s s' (fun w => x.val ≤ w.val ∧ w.val < x.val + 16) ⦄ := by
  apply WP.spec_mono (set_cap_spec x s c)
  rintro s' rfl
  have h8 : (core.num.U64.wrapping_add x 8#u64).val = x.val + 8 := by
    rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  exact (WFrame.wr s hx ⟨le_refl _, by omega⟩ _).trans
    (WFrame.wr _ (by unfold P1.Aligned; rw [h8]; omega) ⟨by rw [h8]; omega, by rw [h8]; omega⟩ _)

/-- **`create_new_objects`' write frame** (types 0, 2..7, 9..13: no
object initialisation): `create_loop_rel` with only slot words of `th'`
written. -/
theorem create_loop_frame {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hcan : CanonR base.val (base.val + win.val * 2 ^ zOf nt.val us.val))
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (th0 : TypedHeap) (hG0 : ∀ x ∈ G0.chains.flatten, IsSlot th0 x)
    (hds0 : ∀ j, j < win.val → IsSlot th0 (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))))
    (hs0 : IsSlot th0 (cslotAddr (pp.bv, idx)))
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1
        win.val ∧ WFrame (L := L) s res.1 (SlotSpan th0) ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ zOf nt.val us.val := Nat.one_le_two_pow
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1
        x.2.2.val ∧ WFrame (L := L) s x.1 (SlotSpan th0)) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hW⟩
    simp only at ha hiw hI hW ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val :=
        Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      have hb0 : 0 < base.val := hcan.1
      have hwk : win.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 2 ^ zOf nt.val us.val := by
        rw [hv2, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 =
          ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3, create_object_eq arI s1 a1 nt _ us dev (by omega)]
      simp only [bind_ok, uncurry_apply_pair]
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      have hL := loop_step (L := L) th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht (by omega) hus hz hsc off.val
        win.val base.val hwin hfit hcan hpA hAp hnewcv zlo zhi hzs G0 m0 hsrcd s1 i.val hit' hI
      obtain ⟨σi, Gi, -, -, -, hMi, -, -, hcsi, -, -, -, -, hmemG, -⟩ := id hI
      have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
      have hss : IsSlot th' (cslotAddr (pp.bv, idx)) := hAs.isSlot
      have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hMi.members _).2 ⟨hss, _, hcsi, by simp⟩
      have hds : IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) :=
        ⟨dest, off.val + i.val, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hnx : nextOf (L.mem s1) (cslotAddr (pp.bv, idx)) = 0#u64 ∨
          IsSlot th' (nextOf (L.mem s1) (cslotAddr (pp.bv, idx))) := by
        rcases hMi.next_mem hsm with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ((hMi.members _).1 h1).1
      refine WP.spec_bind (WP.spec_and hL (WP.spec_and (insert_new_frame hP' s1 _ _ _ hss hds hnx)
        (insert_new_cap_kc s1 _ _ _))) fun s3 ⟨hs3, hfr, hk⟩ => ?_
      have hW3 : WFrame (L := L) s s3 (SlotSpan th0) := hW.trans ⟨hk.1, hk.2, fun w hw hnp => hfr w hw (fun a ha hin => by
        refine hnp ⟨a, ?_, hin.1, hin.2⟩
        rcases ha with e | e | ⟨h0, e⟩
        · rw [e]; exact hs0
        · rw [e]; exact hds0 i.val hit'
        · rw [e]
          rcases hMi.next_mem hsm with h | ⟨h1, -⟩
          · exact absurd h h0
          · rcases hmemG _ h1 with hg | ⟨j, hj, e'⟩
            · exact hG0 _ hg
            · rw [e']; exact hds0 j (by omega))⟩
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hs3, hW3, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hW⟩
  · exact ⟨rfl, by simp, hinv, WFrame.refl s _⟩

end

end

/-- **`WinZero` from the creation's frame**: the window zero before, and
none of the old slots, `DW` nor the old head's `debug_prev` word in it. -/
theorem winZero_of_frame {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {s s' : S}
    {th : TypedHeap} {A k win : Nat} {DW h0 : U64}
    (hW : WFrame (L := L) s s' (TcbLoopW th A win DW h0)) (hz : ZeroRegion (L.mem s) A (A + win * k))
    (hsl : ∀ a, IsSlot th a → a.val + 32 ≤ A ∨ A + win * k ≤ a.val)
    (hdw : ¬ (A ≤ DW.val ∧ DW.val < A + win * k))
    (hh0 : h0 ≠ 0#u64 → ¬ (A ≤ h0.val + 3584 ∧ h0.val + 3584 < A + win * k)) :
    WinZero (L.mem s') A k win True := by
  intro w hw h1 h2
  by_cases hF : TcbLoopW th A win DW h0 w
  · rcases hF with ⟨a, ha, ha1, ha2⟩ | hT | e | ⟨hne, he⟩
    · exfalso; rcases hsl a ha with h | h <;> omega
    · exact Or.inr ⟨trivial, hT⟩
    · exact absurd ⟨by rw [← e]; exact h1, by rw [← e]; exact h2⟩ hdw
    · exact absurd ⟨by rw [← he]; exact h1, by rw [← he]; exact h2⟩ (hh0 hne)
  · left; rw [hW.2.2 w hw hF]; exact hz w hw h1 h2

/-- **`WinZero` from a slot-only frame** (no object initialised): the window
zero before and none of the old slots in it. -/
theorem winZero_of_slots {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {s s' : S}
    {th : TypedHeap} {A k win : Nat} (hW : WFrame (L := L) s s' (SlotSpan th))
    (hz : ZeroRegion (L.mem s) A (A + win * k)) (hsl : ∀ a, IsSlot th a → a.val + 32 ≤ A ∨ A + win * k ≤ a.val)
    (T : Prop) : WinZero (L.mem s') A k win T := by
  intro w hw h1 h2
  left
  rw [hW.2.2 w hw (fun ⟨a, ha, ha1, ha2⟩ => by rcases hsl a ha with h | h <;> omega)]
  exact hz w hw h1 h2

/-- `th` without the objects whose address is in `[lo, hi)` (l4v `detype`). -/
def restrictTh (th : TypedHeap) (lo hi : Nat) : TypedHeap :=
  fun q => if lo ≤ q.val ∧ q.val < hi then none else th q

/-- The typed-heap kind of the new objects of FL4 type `n` (user size
`us`): TCBs and CNodes; the other objects are not in the typed heap. -/
def thKindN (n us : Nat) : Option ObjKind := if n = 1 then some .tcb else if n = 4 then some (.cnode us) else none

/-- **The typed heap after the creation**: `th` with the new objects of
kind `thKindN n us` at the window's slots, over a window free in `th`. -/
def ThX (th th' : TypedHeap) (A k w n us : Nat) : Prop :=
  (∀ q, th' q = if (∃ i, i < w ∧ q.val = A + i * k) ∧ (thKindN n us).isSome then thKindN n us else th q) ∧
  RegionFree th A (A + w * k)

/-- The new caps' slots are slots of `th`'s CNodes. -/
def DslotC (th : TypedHeap) (dslot : Nat → U64) (w : Nat) : Prop :=
  ∀ j, j < w → ∃ q r, th q = some (.cnode r) ∧ ∃ i, i < 2 ^ r ∧ dslot j = slotOf q i

/-- **The retype's frame, as `RetPost` exposes it**: from the restart's
state `s0` (the current thread `ct` set to Restart), either the reset
preempted (`res` its outcome), or the creation ran from `sR` (`s0`, or the
reset's state when done, its cap's region `[lo, hi)` dropped from `th`) over
a heap `thR` of `th`'s slots, free over `[lo, hi)` (the window when no reset): it writes only
its slot words (`SlotSpan`), with TCBs `TcbLoopW`, with PML4s their
window too, and, for a non-device retype but
PML4s, leaves the window `WinZero` (the creation words of TCBs, `T`). -/
def RetFrame {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (arI : machine.Arch A') (ar : A')
    (th th' : TypedHeap) (G : MdbGhost) (s : S) (x : U64) (A k win A0 k0 w0 : Nat) (pml4 T Z : Prop) (tK : Nat → Prop) (us : Nat)
    (cj : Nat → capability.Cap) (dv : Bool) (dslot : Nat → U64) (RB : Prop)
    (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  ∃ ct s0, sched.cur_thread st s = ok ct ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s0 ∧
    ((res.1 = .Err .Preempted ∧ untyped.reset_untyped st arI s0 ar x = ok res) ∨
     (res.1 = .Ok () ∧ (A = A0 ∧ k = k0 ∧ win = w0 ∧ A % k = 0) ∧ ∃ sR thR lo hi,
       ((sR = s0 ∧ thR = th ∧ lo = A ∧ hi = A + win * k ∧ (RB → (∃ p sb d, capAt (L.mem s0) x = ok (.Untyped p sb 0#u64 d)) ∧
          untyped.reset_untyped st arI s0 ar x = ok (.Ok (), s0, ar))) ∨
        ∃ a1 p sb fi d, untyped.reset_untyped st arI s0 ar x = ok (.Ok (), sR, a1) ∧
          capAt (L.mem s0) x = ok (.Untyped p sb fi d) ∧ capAt (L.mem s) x = ok (.Untyped p sb fi d) ∧ p.val % 8 = 0 ∧ 4 ≤ sb.val ∧
          x ∈ G.chains.flatten ∧ (∀ y, ¬ Mdb.Desc G.par y x) ∧ lo = p.val ∧ hi = p.val + 2 ^ sb.val ∧
          thR = restrictTh th lo hi ∧ RB) ∧
       lo ≤ A ∧ A + win * k ≤ hi ∧ RegionFree thR lo hi ∧
       (∀ a, IsSlot thR a → IsSlot th a) ∧ (∃ n0, tK n0 ∧ ThX thR th' A k win n0 us ∧ ∃ uu : U64, uu.val = us ∧ cj = cjOf n0 uu dv A k) ∧ DslotC th dslot win ∧
       WFrame (L := L) sR res.2.1 (fun v => ((T ∧ TcbLoopW thR A win (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
         (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan thR v) ∨
         (pml4 ∧ A ≤ v.val ∧ v.val < A + win * k)) ∧
       (Z → WinZero (L.mem res.2.1) A k win T) ∧
       (T → L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨ th (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) = some .tcb)))

/-- `RetFrame` for an untyped invocation (its source slot, type and device
flag; the window its base, object size and slot count; the new caps
untyped only for an untyped retype). -/
def RetFrameI {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (arI : machine.Arch A') (ar : A')
    (th : TypedHeap) (G : MdbGhost) (s : S) (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (inv : Fl4Spec.UntypedInvocation)
    (A k win : Nat) (dslot : Nat → U64) (cj : Nat → capability.Cap) (th' : TypedHeap) (res : core.result.Result Unit error.Exc × S × A') :
    Prop :=
  match inv with
  | .retype sl rs _ rb t us slots dev => RetFrame (L := L) arI ar th th' G s (cslotAddr sl) A k win rb.toNat
      (2 ^ bitsApi t us) slots.length (t = .archObject .pml4Obj)
      (t = .tcbObject) (dev = false ∧ t ≠ .archObject .pml4Obj) (fun n0 => objTypeOf n0 = some t) us cj dev dslot
      (rs = true) res ∧
    (res.1 = .Ok () → ∀ j, j < win → isUt (cj j) = true → t = .untyped)


end Fl4Proofs.P3
