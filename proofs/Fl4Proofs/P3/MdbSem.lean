/-
P3 (DESIGN.md §9), CSpace: the meaning of FL4's MDB tests, as pure
functions of the slot contents.

* `srB a b`: `same_region_as a b` (total); it depends only on the
  `shape` of the caps (`srB_shape`): rights, badges, mapping data, guards
  and free indices do not matter.
* `isPF rev ca cb fb`: `is_mdb_parent_of a b` for slot `a` (revocable bit
  `rev`, cap `ca`) and slot `b` (cap `cb`, first-badged bit `fb`)
  (`is_mdb_parent_eq`).
* `badgeF`: the badge of an endpoint or notification cap, else 0.
-/
import Fl4Proofs.P3.NoChildren
import Fl4Proofs.P3.Swap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- A cap with the fields `same_region_as` ignores reset. -/
def shape : capability.Cap → capability.Cap
  | .Untyped p sb _ _ => .Untyped p sb 0#u64 false
  | .Endpoint p _ _ _ _ _ => .Endpoint p 0#u64 false false false false
  | .Notification p _ _ _ => .Notification p 0#u64 false false
  | .Reply p _ => .Reply p false
  | .CNode p r _ _ => .CNode p r 0#u64 0#u64
  | .SchedControl _ => .SchedControl 0#u64
  | .Frame p sz _ _ _ _ _ _ => .Frame p sz 0#u64 false false false 0#u64 0#u64
  | .PageTable p _ _ _ => .PageTable p false 0#u64 0#u64
  | .PageDirectory p _ _ _ => .PageDirectory p false 0#u64 0#u64
  | .Pdpt p _ _ _ => .Pdpt p false 0#u64 0#u64
  | .Pml4 p _ _ => .Pml4 p false 0#u64
  | .Ept p level _ _ _ => .Ept p level false 0#u64 0#u64
  | .IoPort f l _ => .IoPort f l 0#u64
  | .AsidPool p _ => .AsidPool p 0#u64
  | c => c

theorem sr_shape (a b : capability.Cap) :
    objects.same_region_as a b = objects.same_region_as (shape a) (shape b) := by
  cases a <;> cases b <;> rfl

theorem mask_total (b : U64) : ∃ m, objects.mask b = ok m := by
  by_cases h : b.val < 64
  · obtain ⟨m, hm, -⟩ := spec_exists (mask_spec b h); exact ⟨m, by rw [objects_mask_eq]; exact hm⟩
  · exact ⟨core.num.U64.MAX, by unfold objects.mask; rw [if_pos (by scalar_tac)]⟩

def maskF (b : U64) : U64 := Classical.choose (mask_total b)
theorem mask_eq (b : U64) : objects.mask b = ok (maskF b) := Classical.choose_spec (mask_total b)

theorem ite_ok_eq {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (ok a : Result α) else ok b) = ok (if c then a else b) := by split <;> rfl

theorem frame_bits_total (sz : capability.FrameSize) : ∃ v, capability.FrameSize.bits sz = ok v := by
  cases sz <;> exact ⟨_, rfl⟩

def fbitsF (sz : capability.FrameSize) : U64 := Classical.choose (frame_bits_total sz)
theorem frame_bits_eq (sz : capability.FrameSize) : capability.FrameSize.bits sz = ok (fbitsF sz) :=
  Classical.choose_spec (frame_bits_total sz)

theorem sr_total (a b : capability.Cap) : ∃ v, objects.same_region_as a b = ok v := by
  cases a <;> cases b <;> simp only [objects.same_region_as, objects.cap_is_physical, capability.Cap.ptr,
    objects.cap_size_bits, frame_bits_eq, mask_eq, lift, bind_ok, ↓reduceIte, Bool.false_eq_true, ite_ok_eq] <;>
    exact ⟨_, rfl⟩

/-- `same_region_as a b`. -/
def srB (a b : capability.Cap) : Bool := Classical.choose (sr_total a b)
theorem srB_eq (a b : capability.Cap) : objects.same_region_as a b = ok (srB a b) :=
  Classical.choose_spec (sr_total a b)

theorem srB_shape (a b : capability.Cap) : srB a b = srB (shape a) (shape b) := by
  have h1 := srB_eq a b
  rw [sr_shape, srB_eq] at h1
  simpa using h1.symm

theorem srB_of_eq {a b : capability.Cap} {v : Bool} (h : objects.same_region_as a b = ok v) : srB a b = v := by
  rw [srB_eq] at h; simpa using h

/-- Endpoint and notification caps are same-region exactly with caps of their kind to their object. -/
theorem srB_ep (p b : U64) (w r g gr : Bool) (x : capability.Cap) :
    srB (.Endpoint p b w r g gr) x = (match x with | .Endpoint q .. => decide (q = p) | _ => false) := by
  apply srB_of_eq
  cases x <;> simp [objects.same_region_as] <;> split <;> simp_all

theorem srB_ntfn (p b : U64) (w r : Bool) (x : capability.Cap) :
    srB (.Notification p b w r) x = (match x with | .Notification q .. => decide (q = p) | _ => false) := by
  apply srB_of_eq
  cases x <;> simp [objects.same_region_as] <;> split <;> simp_all

/-- The badge of an endpoint or notification cap (else 0). -/
def badgeF : capability.Cap → U64
  | .Endpoint _ b _ _ _ _ => b
  | .Notification _ b _ _ => b
  | _ => 0#u64

/-- Endpoint or notification (the badged kinds). -/
def isBadged : capability.Cap → Bool
  | .Endpoint .. => true
  | .Notification .. => true
  | _ => false

def isUt : capability.Cap → Bool
  | .Untyped .. => true
  | _ => false

def isZb : capability.Cap → Bool
  | .Zombie .. => true
  | _ => false

/-- Frame caps. -/
def isFrame : capability.Cap → Bool
  | .Frame .. => true
  | _ => false

/-- `is_mdb_parent_of a b`, from `a`'s revocable bit and cap and `b`'s cap
and first-badged bit. -/
def isPF (rev : Bool) (ca cb : capability.Cap) (fb : Bool) : Bool :=
  rev && srB ca cb && (if isBadged ca then badgeF ca == 0#u64 || (badgeF cb == badgeF ca && !fb) else true)

/-- The cap in a slot, as a pure function of the memory. -/
def capV (mem : U64 → U64) (a : U64) : capability.Cap :=
  decodeF (mem a).bv (mem (wordOf a 8#u64)).bv

theorem capAt_capV (mem : U64 → U64) (a : U64) : capAt mem a = ok (capV mem a) := by
  rw [capAt_words, wordOf_zero, decode_eq]; rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem is_mdb_parent_eq (s : S) (a b : U64) :
    cdt.is_mdb_parent_of st s a b =
      ok (isPF (revOf (L.mem s) a) (capV (L.mem s) a) (capV (L.mem s) b) (fbOf (L.mem s) b)) := by
  unfold cdt.is_mdb_parent_of
  rw [slot_rev_eq]
  simp only [bind_ok]
  cases hr : revOf (L.mem s) a
  · simp [isPF]
  simp only [↓reduceIte, slot_cap_eq, capAt_capV, bind_ok, srB_eq]
  cases hs : srB (capV (L.mem s) a) (capV (L.mem s) b)
  · simp [isPF, hs]
  simp only [↓reduceIte]
  generalize capV (L.mem s) a = ca at hs ⊢
  generalize capV (L.mem s) b = cb at hs ⊢
  cases ca
  case Endpoint p bd w r g gr =>
    rw [srB_ep] at hs
    cases cb <;> simp at hs
    by_cases h0 : bd = 0#u64
    · simp [isPF, isBadged, badgeF, h0, srB_ep, hs]
    · simp [isPF, isBadged, badgeF, h0, srB_ep, hs, slot_first_badged_eq]
      split <;> simp_all
  case Notification p bd w r =>
    rw [srB_ntfn] at hs
    cases cb <;> simp at hs
    by_cases h0 : bd = 0#u64
    · simp [isPF, isBadged, badgeF, h0, srB_ntfn, hs]
    · simp [isPF, isBadged, badgeF, h0, srB_ntfn, hs, slot_first_badged_eq]
      split <;> simp_all
  all_goals simp [isPF, isBadged, hs]

end

/-! ## Facts about shapes, badges and the parent test -/

theorem isBadged_of_shape {c c' : capability.Cap} (h : shape c = shape c') : isBadged c = isBadged c' := by
  cases c <;> cases c' <;> simp_all [shape, isBadged]
theorem isUt_of_shape {c c' : capability.Cap} (h : shape c = shape c') : isUt c = isUt c' := by
  cases c <;> cases c' <;> simp_all [shape, isUt]
theorem isZb_of_shape {c c' : capability.Cap} (h : shape c = shape c') : isZb c = isZb c' := by
  cases c <;> cases c' <;> simp_all [shape, isZb]

theorem isFrame_of_shape {c' c : capability.Cap} (h : shape c' = shape c) : isFrame c' = isFrame c := by
  cases c' <;> cases c <;> simp_all [shape, isFrame]

theorem srB_congr {a a' b b' : capability.Cap} (ha : shape a = shape a') (hb : shape b = shape b') :
    srB a b = srB a' b' := by
  rw [srB_shape, ha, hb, ← srB_shape]

theorem isPF_congr {r f : Bool} {a a' b b' : capability.Cap} (ha : shape a = shape a') (hba : badgeF a = badgeF a')
    (hb : shape b = shape b') (hbb : badgeF b = badgeF b') : isPF r a b f = isPF r a' b' f := by
  unfold isPF; rw [srB_congr ha hb, isBadged_of_shape ha, hba, hbb]

/-- A badged cap's region holds caps of its kind to its object only. -/
theorem srB_badged {a b : capability.Cap} (ha : isBadged a = true) (h : srB a b = true) :
    isBadged b = true ∧ shape b = shape a := by
  cases a <;> simp [isBadged] at ha
  · rw [srB_ep] at h; cases b <;> simp at h; subst h; simp [isBadged, shape]
  · rw [srB_ntfn] at h; cases b <;> simp at h; subst h; simp [isBadged, shape]

theorem srB_badged_trans {a b c : capability.Cap} (ha : isBadged a = true) (hb : srB a b = true)
    (hc : srB a c = true) : srB b c = true := by
  have h1 := (srB_badged ha hb).2
  rw [srB_congr h1 rfl]; exact hc

theorem revF_badged {c s : capability.Cap} (hs : shape c = shape s) (hb : isBadged c = true) :
    revF c s = (badgeF c != badgeF s) := by
  cases c <;> cases s <;> simp_all [shape, isBadged, revF, badgeF]

theorem revF_ut {c s : capability.Cap} (h : isUt c = true) : revF c s = true := by
  cases c <;> simp_all [isUt, revF]

theorem revF_cases {c s : capability.Cap} (hs : shape c = shape s) (h : revF c s = true) :
    (isBadged c = true ∧ badgeF c ≠ badgeF s) ∨ isUt c = true := by
  cases c <;> cases s <;> simp_all [shape, isBadged, revF, badgeF, isUt]

/-- Changing the child cap to one of the same shape, with the same badge (or
any badge from an unbadged one) and the first-badged bit `is_cap_revocable`
gives, keeps a passed parent test passing. -/
theorem isPF_child {rv : Bool} {ca cs c : capability.Cap} {fs : Bool} (h : isPF rv ca cs fs = true)
    (hsh : shape c = shape cs) (hbd : badgeF c = badgeF cs ∨ badgeF cs = 0#u64) :
    isPF rv ca c (revF c cs) = true := by
  unfold isPF at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2' : srB ca c = true := by rw [srB_congr rfl hsh]; exact h2
  refine ⟨⟨h1, h2'⟩, ?_⟩
  by_cases hbca : isBadged ca = true
  · simp only [hbca, ↓reduceIte] at h3 ⊢
    by_cases h0 : badgeF ca = 0#u64
    · simp [h0]
    · have e0 : (badgeF ca == 0#u64) = false := by simpa using h0
      simp only [e0, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h3 ⊢
      obtain ⟨hb1, -⟩ := h3
      have hcs0 : badgeF cs ≠ 0#u64 := by rw [hb1]; exact h0
      have hbc : badgeF c = badgeF cs := hbd.resolve_right hcs0
      have hbad : isBadged c = true := by
        rw [isBadged_of_shape hsh]; exact (srB_badged hbca h2).1
      refine ⟨by rw [hbc, hb1], ?_⟩
      rw [revF_badged hsh hbad, hbc]; simp
  · simp [hbca]

end

end Fl4Proofs.P3
