/-
P3 (DESIGN.md §9), untyped: the MDB invariant `MdbInv` after
`insert_new_cap` (a new cap linked as a child of an untyped cap).

FL4's `same_region_as` from an untyped cap is containment of address
ranges (`srB_ut`): a cap `b`'s range is `ptr b ..= ptr b + mask (size b)`
(`baseF`, `topF`). The hypotheses on the state before the insertion are the
ones l4v takes from `caps_no_overlap` and `descendants_range_in` for the
region of the new object: every cap whose range meets the new object's is
an untyped cap whose range contains the parent's (`hno`), the parent's
descendants miss it (`hdd`), and ranges of physical caps do not wrap
(`hreg`). `InsNCtx.inv` is the result.
-/
import Fl4Proofs.P3.UntypedInsert
import Fl4Proofs.P3.CapRange
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-- **`same_region_as` from an untyped cap is range containment.** -/
theorem srB_utR (q sz f : U64) (d : Bool) (b : capability.Cap) :
    srB (.Untyped q sz f d) b = (physF b && decide (q.val ≤ baseF b) &&
      decide (topF b ≤ (core.num.U64.wrapping_add q (maskF sz)).val) && decide (baseF b ≤ topF b)) := by
  apply srB_of_eq
  unfold objects.same_region_as
  simp only [phys_eq, ptr_eq, size_eq, mask_eq, lift, bind_ok]
  unfold baseF topF
  generalize core.num.U64.wrapping_add (ptrF b) (maskF (sizeF b)) = tb
  generalize core.num.U64.wrapping_add q (maskF sz) = ta
  generalize ptrF b = pb
  cases physF b
  · simp
  · have e1 : (q ≤ pb) ↔ q.val ≤ pb.val := Iff.rfl
    have e2 : (tb ≤ ta) ↔ tb.val ≤ ta.val := Iff.rfl
    have e3 : (pb ≤ tb) ↔ pb.val ≤ tb.val := Iff.rfl
    by_cases h1 : q.val ≤ pb.val <;> by_cases h2 : tb.val ≤ ta.val <;> by_cases h3 : pb.val ≤ tb.val <;>
      simp only [↓reduceIte, e1, e2, e3, h1, h2, h3, decide_true, decide_false, Bool.true_and, Bool.and_true,
        Bool.and_false, Bool.false_and]

/-- The caps `create_object` makes (Untyped, TCB, endpoint, notification,
CNode, scheduling context, reply; frames and the paging structures). -/
def NewKind : capability.Cap → Prop
  | .Untyped .. | .Thread _ | .Endpoint .. | .Notification .. | .CNode .. | .SchedContext .. | .Reply ..
  | .Frame .. | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. => True
  | _ => False

/-- Frame caps (the only new caps whose `same_region_as` is range
containment rather than the same object). -/
def isFr : capability.Cap → Bool
  | .Frame .. => true
  | _ => false

theorem srB_to_ut {a : capability.Cap} {q sz f : U64} {d : Bool} (h : srB a (.Untyped q sz f d) = true) :
    isUt a = true := by
  have h' := srB_eq a (.Untyped q sz f d)
  rw [h] at h'
  cases a <;> first | rfl | (simp [objects.same_region_as] at h')

/-- From a new cap other than an untyped one, `same_region_as` means the same
object (same shape). -/
theorem srB_nk_left {c v : capability.Cap} (hk : NewKind c) (hu : isUt c = false) (hf : isFr c = false)
    (h : srB c v = true) : shape v = shape c := by
  have h' := srB_eq c v
  rw [h] at h'
  cases c <;> simp [NewKind, isUt, isFr] at hk hu hf <;> cases v <;> simp [objects.same_region_as] at h' <;>
    (try split_ifs at h' with e1 e2) <;> simp_all [shape] <;> exact UScalar.eq_of_val_eq h'

/-- Into a new cap other than an untyped one, from a cap other than an
untyped one: the same object. -/
theorem srB_nk_right {u c : capability.Cap} (hk : NewKind c) (hc : isUt c = false) (hf : isFr c = false)
    (hu : isUt u = false) (h : srB u c = true) : shape c = shape u := by
  have h' := srB_eq u c
  rw [h] at h'
  cases c <;> simp [NewKind, isUt, isFr] at hk hc hf <;> cases u <;> simp [isUt] at hu <;>
    simp [objects.same_region_as] at h' <;> (try split_ifs at h' with e1 e2) <;> simp_all [shape] <;>
    exact UScalar.eq_of_val_eq h'


theorem sizeF_frame (p : U64) (sz : capability.FrameSize) (r : U64) (d m : Bool) (a va : U64) (ep : Bool) :
    sizeF (.Frame p sz r d m ep a va) = fbitsF sz :=
  ok_inj ((size_eq _).symm.trans (by simp [objects.cap_size_bits, frame_bits_eq]))

theorem ptrF_frame (p : U64) (sz : capability.FrameSize) (r : U64) (d m : Bool) (a va : U64) (ep : Bool) :
    ptrF (.Frame p sz r d m ep a va) = p := ok_inj (ptr_eq _).symm

/-- `same_region_as` from a frame cap: a frame cap in its range. -/
theorem srB_frame_in {p : U64} {sz : capability.FrameSize} {r : U64} {d m ep : Bool} {a va : U64} {v : capability.Cap}
    (h : srB (.Frame p sz r d m ep a va) v = true) :
    isFr v = true ∧ baseF (.Frame p sz r d m ep a va) ≤ baseF v ∧ topF v ≤ topF (.Frame p sz r d m ep a va) ∧
      baseF v ≤ topF v := by
  have h' := srB_eq (.Frame p sz r d m ep a va) v
  rw [h] at h'
  cases v <;> simp [objects.same_region_as, frame_bits_eq, mask_eq, lift] at h'
  case Frame pb sb rb db mb ept ab vb =>
    unfold baseF topF
    rw [ptrF_frame, ptrF_frame, sizeF_frame, sizeF_frame]
    simp only [core.num.U64.wrapping_add_val_eq]
    split_ifs at h' with h1 h2
    · refine ⟨rfl, h1, by simpa [U64.size] using h2, ?_⟩
      have := ok_inj h'; simpa [U64.size] using this
    · cases ok_inj h'
    · cases ok_inj h'

/-- `same_region_as` into a frame cap: from a frame cap holding it, or an
untyped one. -/
theorem srB_to_frame {u : capability.Cap} {p : U64} {sz : capability.FrameSize} {r : U64} {d m ep : Bool} {a va : U64}
    (hu : isUt u = false) (h : srB u (.Frame p sz r d m ep a va) = true) :
    isFr u = true ∧ baseF u ≤ baseF (.Frame p sz r d m ep a va) ∧ topF (.Frame p sz r d m ep a va) ≤ topF u := by
  have h' := srB_eq u (.Frame p sz r d m ep a va)
  rw [h] at h'
  cases u <;> simp [isUt] at hu <;> simp [objects.same_region_as] at h'
  case Frame pb sb rb db mb ept ab vb =>
    obtain ⟨-, h2, h3, -⟩ := srB_frame_in (show srB (.Frame pb sb rb db mb ept ab vb) (.Frame p sz r d m ep a va) = true from h)
    exact ⟨rfl, h2, h3⟩

theorem physF_frame (p : U64) (sz : capability.FrameSize) (r : U64) (d m : Bool) (a va : U64) (ep : Bool) :
    physF (.Frame p sz r d m ep a va) = true := ok_inj (phys_eq _).symm

theorem isUt_frame {v : capability.Cap} (h : isFr v = true) : isUt v = false ∧ physF v = true := by
  cases v <;> simp [isFr] at h; exact ⟨rfl, physF_frame _ _ _ _ _ _ _ _⟩

/-- **From a new cap, `same_region_as` gives a non-untyped physical cap in
its range** (non-empty). -/
theorem srB_new_left {c v : capability.Cap} (hk : NewKind c) (hu : isUt c = false) (hcr : baseF c ≤ topF c)
    (h : srB c v = true) :
    physF v = true ∧ isUt v = false ∧ baseF c ≤ baseF v ∧ topF v ≤ topF c ∧ baseF v ≤ topF v := by
  cases hf : isFr c
  · have e := srB_nk_left hk hu hf h
    obtain ⟨hb, ht, hp⟩ := range_of_shape e
    have hpc : physF c = true := by cases c <;> simp [NewKind, isUt] at hk hu <;> exact ok_inj (phys_eq _).symm
    refine ⟨by rw [hp]; exact hpc, by rw [isUt_of_shape e]; exact hu, by omega, by omega, by omega⟩
  · cases c <;> simp [isFr] at hf
    obtain ⟨h1, h2, h3, h4⟩ := srB_frame_in h
    exact ⟨(isUt_frame h1).2, (isUt_frame h1).1, h2, h3, h4⟩

/-- **Into a new cap, from a cap other than an untyped one**: a physical cap
holding its range. -/
theorem srB_new_right {u c : capability.Cap} (hk : NewKind c) (hc : isUt c = false) (hu : isUt u = false)
    (h : srB u c = true) : physF u = true ∧ baseF u ≤ baseF c ∧ topF c ≤ topF u := by
  cases hf : isFr c
  · have e := srB_nk_right hk hc hf hu h
    obtain ⟨hb, ht, hp⟩ := range_of_shape e
    have hpc : physF c = true := by cases c <;> simp [NewKind, isUt] at hk hc <;> exact ok_inj (phys_eq _).symm
    exact ⟨by rw [← hp]; exact hpc, by omega, by omega⟩
  · cases c <;> simp [isFr] at hf
    obtain ⟨h1, h2, h3⟩ := srB_to_frame hu h
    exact ⟨(isUt_frame h1).2, h2, h3⟩

theorem ptrF_ut (q sz f : U64) (d : Bool) : ptrF (.Untyped q sz f d) = q := ok_inj (ptr_eq _).symm
theorem sizeF_ut (q sz f : U64) (d : Bool) : sizeF (.Untyped q sz f d) = sz := ok_inj (size_eq _).symm
theorem physF_ut (q sz f : U64) (d : Bool) : physF (.Untyped q sz f d) = true := ok_inj (phys_eq _).symm


theorem isUt_iff {a : capability.Cap} : isUt a = true ↔ ∃ q sz f d, a = .Untyped q sz f d := by
  cases a <;> simp [isUt]

theorem srB_ut_iff {a : capability.Cap} (ha : isUt a = true) (b : capability.Cap) :
    srB a b = true ↔ physF b = true ∧ Within b a ∧ baseF b ≤ topF b := by
  obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 ha
  rw [srB_utR]
  unfold Within
  rw [show baseF (.Untyped q sz f d) = q.val from by unfold baseF; rw [ptrF_ut],
    show topF (.Untyped q sz f d) = (core.num.U64.wrapping_add q (maskF sz)).val from by
      unfold topF; rw [ptrF_ut, sizeF_ut]]
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨h1, ⟨of_decide_eq_true h2, of_decide_eq_true h3⟩, of_decide_eq_true h4⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨h1, decide_eq_true h2⟩, decide_eq_true h3⟩, decide_eq_true h4⟩

theorem physF_of_ut {a : capability.Cap} (ha : isUt a = true) : physF a = true := by
  obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 ha; exact physF_ut _ _ _ _

theorem badgeF_ut {a : capability.Cap} (ha : isUt a = true) : badgeF a = 0#u64 := by
  obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 ha; rfl
theorem isBadged_ut {a : capability.Cap} (ha : isUt a = true) : isBadged a = false := by
  obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 ha; rfl

/-- A new cap is in its own region. -/
theorem srB_self_nk {c : capability.Cap} (hk : NewKind c) (hp : physF c = true) (hr : baseF c ≤ topF c) :
    srB c c = true := by
  cases hu : isUt c
  · cases hf : isFr c
    · have h' := srB_eq c c
      cases c <;> simp [NewKind, isUt, isFr] at hk hu hf <;> simp [objects.same_region_as] at h' <;> exact h'
    · cases c <;> simp [isFr] at hf
      rw [srB_frame]
      unfold baseF topF at hr
      rw [ptrF_frame, sizeF_frame] at hr
      exact decide_eq_true hr
  · rw [srB_ut_iff hu]; exact ⟨hp, ⟨le_refl _, le_refl _⟩, hr⟩

theorem not_disj_within {b a : capability.Cap} (hw : Within b a) (hb : baseF b ≤ topF b) : ¬ Disj a b := by
  unfold Within at hw; unfold Disj; omega

end

namespace Mdb

end Mdb

section

/-- The situation of an `insert_new_cap`, at the level of the slot contents:
`dest` (free) is linked after the untyped cap's slot `src` with the new cap
`c`, both bits set. The range hypotheses are l4v's `caps_no_overlap` and
`descendants_range_in` for `c`'s range. -/
structure InsNCtx (th : TypedHeap) (mem mem' : U64 → U64) (G : MdbGhost) (src dest : U64) (c : capability.Cap) :
    Prop where
  hM : MdbLinks th mem G
  hI : MdbInv mem G
  hsrc : src ∈ G.chains.flatten
  hd : IsSlot th dest
  hdest : dest ∉ G.chains.flatten
  hnext : ∀ a, IsSlot th a → nextOf mem' a =
    if a = dest then nextOf mem src else if a = src then dest else nextOf mem a
  hcap : ∀ a, IsSlot th a → capV mem' a = if a = dest then c else capV mem a
  hrev : ∀ a, IsSlot th a → revOf mem' a = if a = dest then true else revOf mem a
  hfb : ∀ a, IsSlot th a → fbOf mem' a = if a = dest then true else fbOf mem a
  hut : isUt (capV mem src) = true
  hnk : NewKind c
  hcp : physF c = true
  hcr : baseF c ≤ topF c
  hcin : Within c (capV mem src)
  hreg : ∀ x ∈ G.chains.flatten, physF (capV mem x) = true → baseF (capV mem x) ≤ topF (capV mem x)
  hno : ∀ x ∈ G.chains.flatten, physF (capV mem x) = true →
    Disj (capV mem x) c ∨ (isUt (capV mem x) = true ∧ Within (capV mem src) (capV mem x))
  hdd : ∀ y, Mdb.Desc G.par y src → Disj (capV mem y) c
  hsame : isUt c = true → Within (capV mem src) c → shape c = shape (capV mem src)

namespace InsNCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c : capability.Cap}
  (h : InsNCtx th mem mem' G src dest c)
include h

theorem sl {z : U64} (hz : z ∈ G.chains.flatten) : IsSlot th z := ((h.hM.members z).1 hz).1
theorem dne {z : U64} (hz : z ∈ G.chains.flatten) : z ≠ dest := fun e => h.hdest (e ▸ hz)
theorem sd : src ≠ dest := h.dne h.hsrc
theorem cz {z : U64} (hz : z ∈ G.chains.flatten) : capV mem' z = capV mem z := by
  rw [h.hcap z (h.sl hz), if_neg (h.dne hz)]
theorem rz {z : U64} (hz : z ∈ G.chains.flatten) : revOf mem' z = revOf mem z := by
  rw [h.hrev z (h.sl hz), if_neg (h.dne hz)]
theorem fz {z : U64} (hz : z ∈ G.chains.flatten) : fbOf mem' z = fbOf mem z := by
  rw [h.hfb z (h.sl hz), if_neg (h.dne hz)]
theorem nz {z : U64} (hz : z ∈ G.chains.flatten) (hzs : z ≠ src) : nextOf mem' z = nextOf mem z := by
  rw [h.hnext z (h.sl hz), if_neg (h.dne hz), if_neg hzs]
theorem ns : nextOf mem' src = dest := by rw [h.hnext src (h.sl h.hsrc), if_neg h.sd, if_pos rfl]
theorem nd : nextOf mem' dest = nextOf mem src := by rw [h.hnext dest h.hd, if_pos rfl]
theorem cd : capV mem' dest = c := by rw [h.hcap dest h.hd, if_pos rfl]
theorem rd : revOf mem' dest = true := by rw [h.hrev dest h.hd, if_pos rfl]
theorem fd : fbOf mem' dest = true := by rw [h.hfb dest h.hd, if_pos rfl]
theorem sfm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten)
    (hs : srM mem' x y = srM mem x y) : srF mem' x y = srF mem x y :=
  srF_congr hs (by rw [h.cz hx]) (h.rz hx)
theorem snf : isFrame (capV mem src) = false := by
  obtain ⟨q, sz, f, d, e⟩ := isUt_iff.1 h.hut; rw [e]; rfl

theorem pm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : isPM mem' x y = isPM mem x y := by
  unfold isPM; rw [h.rz hx, h.fz hy, h.cz hx, h.cz hy]
theorem sm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : srM mem' x y = srM mem x y := by
  unfold srM; rw [h.cz hx, h.cz hy]

theorem nm (h0 : nextOf mem src ≠ 0#u64) : nextOf mem src ∈ G.chains.flatten ∧ nextOf mem src ≠ src := by
  rcases h.hM.next_mem h.hsrc with h1 | h1
  · exact absurd h1 h0
  · exact h1
theorem nxm {y : U64} (hy : y ∈ G.chains.flatten) (h0 : nextOf mem y ≠ 0#u64) : nextOf mem y ∈ G.chains.flatten := by
  rcases h.hM.next_mem hy with h1 | h1
  · exact absurd h1 h0
  · exact h1.1

theorem pd (z : U64) : G.par z ≠ some dest := fun e => h.hdest (h.hM.tree.par_mem z dest e).2
theorem dn : G.par dest = none := by
  cases e : G.par dest with
  | none => rfl
  | some p => exact absurd (h.hM.tree.par_mem dest p e).1 h.hdest

theorem desc (y x : U64) : Mdb.Desc (insG G src dest true).par y x ↔
    Mdb.Desc G.par y x ∨ (y = dest ∧ (x = src ∨ Mdb.Desc G.par src x)) := by
  have hnp : (if true then some src else G.par src) ≠ some dest := by simp [h.sd]
  show Mdb.Desc (Function.update G.par dest _) y x ↔ _
  rw [Mdb.desc_update_iff h.pd h.dn hnp, np_desc_iff]
  simp

theorem dest_no_desc (x : U64) : ¬ Mdb.Desc G.par dest x := fun e => h.hdest (desc_mem h.hM e).1

theorem memI (z : U64) : z ∈ (insG G src dest true).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
  mem_flatten_ins h.hsrc

theorem srcUt : ∃ q sz f d, capV mem src = .Untyped q sz f d := isUt_iff.1 h.hut

/-- No old cap is in the new cap's region unless the new cap is (the
shape of) the untyped cap itself. -/
theorem k1 {v : U64} (hv : v ∈ G.chains.flatten) (hs : srB c (capV mem v) = true) : shape c = shape (capV mem src) := by
  cases hu : isUt c
  · obtain ⟨hp, hu', h1, h2, h3⟩ := srB_new_left h.hnk hu h.hcr hs
    rcases h.hno v hv hp with hd | ⟨hu'', -⟩
    · exfalso; unfold Disj at hd; omega
    · rw [hu'] at hu''; cases hu''
  · obtain ⟨hp, hw, hr⟩ := (srB_ut_iff hu _).1 hs
    rcases h.hno v hv hp with hd | ⟨-, hw2⟩
    · exact absurd (by unfold Disj at hd ⊢; omega) (not_disj_within hw hr)
    · apply h.hsame hu
      unfold Within at *; obtain ⟨a1, a2⟩ := h.hcin; omega

theorem ssrc : srB (capV mem src) c = true := (srB_ut_iff h.hut c).2 ⟨h.hcp, h.hcin, h.hcr⟩

/-- Every old cap sees the new cap as it sees the untyped cap. -/
theorem k2 {u : U64} (hu : u ∈ G.chains.flatten) : srB (capV mem u) c = srB (capV mem u) (capV mem src) := by
  obtain ⟨q, sz, f, d, hS⟩ := h.srcUt
  have hsr := h.hreg src h.hsrc (physF_of_ut h.hut)
  apply Bool.eq_iff_iff.2
  constructor
  · intro hs
    cases hU : isUt (capV mem u)
    · cases hc : isUt c
      · obtain ⟨hp, h1, h2⟩ := srB_new_right h.hnk hc hU hs
        rcases h.hno u hu hp with hd | ⟨hu', -⟩
        · exfalso; have := h.hcr; unfold Disj at hd; omega
        · rw [hU] at hu'; cases hu'
      · obtain ⟨q', sz', f', d', rfl⟩ := isUt_iff.1 hc
        rw [srB_to_ut hs] at hU; cases hU
    · obtain ⟨-, hw, -⟩ := (srB_ut_iff hU c).1 hs
      rcases h.hno u hu (physF_of_ut hU) with hd | ⟨-, hw2⟩
      · exact absurd hd (not_disj_within hw h.hcr)
      · exact (srB_ut_iff hU _).2 ⟨physF_of_ut h.hut, hw2, hsr⟩
  · intro hs
    rw [hS] at hs
    have hU := srB_to_ut hs
    rw [← hS] at hs
    obtain ⟨-, hw, -⟩ := (srB_ut_iff hU _).1 hs
    refine (srB_ut_iff hU c).2 ⟨h.hcp, ?_, h.hcr⟩
    unfold Within at *; obtain ⟨a1, a2⟩ := h.hcin; omega

theorem orig' (z p : U64) (hz : (insG G src dest true).par z = some p) : revOf mem' p = true := by
  change Function.update G.par dest (if true then some src else G.par src) z = some p at hz
  by_cases hzd : z = dest
  · subst hzd
    rw [Function.update_self] at hz
    have hp : p = src := by simpa using hz.symm
    rw [hp, h.rz h.hsrc]; exact h.hI.utrev src h.hsrc h.hut
  · rw [Function.update_of_ne hzd] at hz
    rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz

theorem desc' (x y : U64) (hd : Mdb.Desc (insG G src dest true).par y x) : isPM mem' x y = true := by
  rcases (h.desc y x).1 hd with hd | ⟨hy, hx⟩
  · obtain ⟨h1, h2⟩ := desc_mem h.hM hd
    rw [h.pm h2 h1]; exact h.hI.desc x y hd
  · rw [hy]
    rcases hx with rfl | hx
    · unfold isPM
      rw [h.rz h.hsrc, h.hI.utrev x h.hsrc h.hut, h.cz h.hsrc, h.cd, h.fd]
      simp [isPF, h.ssrc, isBadged_ut h.hut]
    · have hxm := (desc_mem h.hM hx).2
      have h0 := h.hI.desc x src hx
      unfold isPM at h0 ⊢
      rw [h.rz hxm, h.cz hxm, h.cd, h.fd]
      unfold isPF at h0 ⊢
      simp only [Bool.and_eq_true] at h0 ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := h0
      obtain ⟨q, sz, f, d, hS⟩ := h.srcUt
      have hX : isUt (capV mem x) = true := by rw [hS] at h2; exact srB_to_ut h2
      refine ⟨⟨h1, by rw [h.k2 hxm]; exact h2⟩, ?_⟩
      simp [isBadged_ut hX]

theorem after' (y : U64) (hy : y ∈ (insG G src dest true).chains.flatten) (hn : nextOf mem' y ≠ 0#u64) (x : U64)
    (hx : x = y ∨ Mdb.Desc (insG G src dest true).par y x)
    (hnd : ¬ Mdb.Desc (insG G src dest true).par (nextOf mem' y) x) : isPM mem' x (nextOf mem' y) = false := by
  rcases (h.memI y).1 hy with hyd | hy
  · rw [hyd] at hn hnd hx ⊢
    rw [h.nd] at hn hnd ⊢
    obtain ⟨hN, -⟩ := h.nm hn
    rcases hx with hxd | hx
    · subst hxd
      unfold isPM
      rw [h.rd, h.cd, h.fz hN, h.cz hN]
      cases hsb : srB c (capV mem (nextOf mem src))
      · simp [isPF, hsb]
      · have e := h.k1 hN hsb
        have hcu : isUt c = true := by rw [isUt_of_shape e]; exact h.hut
        by_cases hdN : Mdb.Desc G.par (nextOf mem src) src
        · exfalso
          obtain ⟨-, hw, hr⟩ := (srB_ut_iff hcu _).1 hsb
          exact not_disj_within hw hr (by have := h.hdd _ hdN; unfold Disj at this ⊢; omega)
        · have ha := h.hI.after src h.hsrc hn src (Or.inl rfl) hdN
          unfold isPM at ha
          rw [h.hI.utrev src h.hsrc h.hut] at ha
          rw [isPF_congr e (by rw [badgeF_ut hcu, badgeF_ut h.hut]) rfl rfl]
          exact ha
    · have hx' : x = src ∨ Mdb.Desc G.par src x := by
        rcases (h.desc dest x).1 hx with e | ⟨-, e⟩
        · exact absurd e (h.dest_no_desc x)
        · exact e
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem src) x := fun e => hnd ((h.desc _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact h.hsrc
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hN]
      exact h.hI.after src h.hsrc hn x hx' hnd'
  · by_cases hys : y = src
    · rw [hys] at hn hnd hx hy ⊢
      rw [h.ns] at hn hnd ⊢
      exfalso
      rcases hx with hxy | hx
      · rw [hxy] at hnd; exact hnd ((h.desc dest src).2 (Or.inr ⟨rfl, Or.inl rfl⟩))
      · have hx' : Mdb.Desc G.par src x := ((h.desc src x).1 hx).resolve_right (fun e => h.sd e.1)
        exact hnd ((h.desc dest x).2 (Or.inr ⟨rfl, Or.inr hx'⟩))
    · rw [h.nz hy hys] at hn hnd ⊢
      have hw := h.nxm hy hn
      have hx' : x = y ∨ Mdb.Desc G.par y x := by
        rcases hx with e | e
        · exact Or.inl e
        · exact Or.inr (((h.desc y x).1 e).resolve_right (fun e => h.dne hy e.1))
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem y) x := fun e => hnd ((h.desc _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact hy
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hw]
      exact h.hI.after y hy hn x hx' hnd'

theorem chunk' (ch' : List U64) (hch' : ch' ∈ (insG G src dest true).chains) : Mdb.ChunkL (srF mem') ch' := by
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
  have hchm : ∀ z, z ∈ ch → z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨_, hch, hz⟩
  by_cases hsc : src ∈ ch
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem hsc
    have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 h.hM.tree.nodup).1 _ hch
    rw [Mdb.insAfter_split (Mdb.nodup_mid hnd0).1]
    have hcd : ∀ v, srF mem' dest v = srB c (capV mem' v) := fun v => by
      rw [srF_rev h.rd]; unfold srM; rw [h.cd]
    have hcs : Mdb.CA (srM mem) src B := ca_srM (Mdb.chunkL_ca (h.hI.chunk _ hch)) (Or.inl h.snf)
    refine Mdb.chunkL_ins2 (h.hI.chunk _ hch)
      (fun u hu v hv => h.sfm (hchm u hu) (hchm v hv) (h.sm (hchm u hu) (hchm v hv)))
      (fun u hu => srF_congr ?_ (by rw [h.cz (hchm u hu)]) (h.rz (hchm u hu))) ?_ (srF_of_srM ?_)
    · unfold srM; rw [h.cd, h.cz (hchm u hu), h.k2 (hchm u hu)]
    · by_cases hex : ∃ v ∈ B, srB c (capV mem v) = true
      · obtain ⟨v, hvB, hv⟩ := hex
        have e := h.k1 (hchm v (by simp [hvB])) hv
        apply Mdb.ca_congr hcs
        intro w hw
        rw [hcd, h.cz (hchm w (by simp [hw]))]
        unfold srM; exact srB_congr e rfl
      · push_neg at hex
        apply Mdb.ca_false
        intro w hw
        rw [hcd, h.cz (hchm w (by simp [hw]))]
        simpa using hex w hw
    · unfold srM; rw [h.cz h.hsrc, h.cd]; exact h.ssrc
  · rw [Mdb.insAfter_of_not_mem hsc]
    exact Mdb.chunkL_congr (h.hI.chunk _ hch)
      (fun u hu v hv => h.sfm (hchm u hu) (hchm v hv) (h.sm (hchm u hu) (hchm v hv)))

theorem badges' (y : U64) (hy : y ∈ (insG G src dest true).chains.flatten) (hn : nextOf mem' y ≠ 0#u64)
    (hbg : isBadged (capV mem' y) = true) (hsr : srM mem' y (nextOf mem' y) = true)
    (hbne : badgeF (capV mem' y) ≠ badgeF (capV mem' (nextOf mem' y)))
    (hb0 : badgeF (capV mem' (nextOf mem' y)) ≠ 0#u64) : fbOf mem' (nextOf mem' y) = true := by
  rcases (h.memI y).1 hy with hyd | hy
  · exfalso
    rw [hyd] at hn hsr hbg
    rw [h.nd] at hn hsr
    obtain ⟨hN, -⟩ := h.nm hn
    unfold srM at hsr; rw [h.cd, h.cz hN] at hsr
    rw [h.cd] at hbg
    have e := h.k1 hN hsr
    rw [isBadged_of_shape e, isBadged_ut h.hut] at hbg; cases hbg
  · by_cases hys : y = src
    · exfalso; rw [hys, h.cz h.hsrc, isBadged_ut h.hut] at hbg; cases hbg
    · rw [h.nz hy hys] at hn hsr hbne hb0 ⊢
      have hw := h.nxm hy hn
      rw [h.fz hw]
      rw [h.cz hy, h.cz hw] at hbne
      rw [h.cz hw] at hb0
      rw [h.cz hy] at hbg
      exact h.hI.badges y hy hn hbg (by rw [← h.sm hy hw]; exact hsr) hbne hb0

theorem utrev' (x : U64) (hx : x ∈ (insG G src dest true).chains.flatten) (hu : isUt (capV mem' x) = true) :
    revOf mem' x = true := by
  rcases (h.memI x).1 hx with hxd | hx
  · rw [hxd]; exact h.rd
  · rw [h.rz hx]; rw [h.cz hx] at hu; exact h.hI.utrev x hx hu

theorem self' (x : U64) (hx : x ∈ (insG G src dest true).chains.flatten) (hz : isZb (capV mem' x) = false) :
    srM mem' x x = true := by
  rcases (h.memI x).1 hx with hxd | hx
  · rw [hxd]; unfold srM; rw [h.cd]; exact srB_self_nk h.hnk h.hcp h.hcr
  · rw [h.cz hx] at hz
    rw [h.sm hx hx]; exact h.hI.self x hx hz

/-- **`MdbInv` after `insert_new_cap`.** -/
theorem inv : MdbInv mem' (insG G src dest true) :=
  ⟨h.orig', h.desc', h.after', h.chunk', h.badges', h.utrev', h.self'⟩

end InsNCtx

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`insert_new_cap` of a new cap under an untyped cap refines
`create_cap`'s updates and keeps `MdbInv`**, given the range hypotheses of
`InsNCtx` for the new cap. -/
theorem insert_new_full (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hut : isUt srcC = true)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hnk : NewKind c) (hcp : physF c = true) (hcr : baseF c ≤ topF c) (hcin : Within c srcC)
    (hreg : ∀ x ∈ G.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x))
    (hno : ∀ x ∈ G.chains.flatten, physF (capV (L.mem s) x) = true →
      Disj (capV (L.mem s) x) c ∨ (isUt (capV (L.mem s) x) = true ∧ Within srcC (capV (L.mem s) x)))
    (hdd : ∀ y, Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) → Disj (capV (L.mem s) y) c)
    (hsame : isUt c = true → Within srcC c → shape c = shape srcC) :
    cdt.insert_new_cap st s (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) c ⦃ s' =>
      ∃ σ', Fl4Spec.setCap (Z := Unit) a (pd.bv, idxd) (newCapCdt σ (ps.bv, idxs) (pd.bv, idxd)) =
          ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧
        MdbLinks th (L.mem s') (insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) true) ∧
        CdtRel th (L.mem s') σ' (insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) true) ∧
        MdbInv (L.mem s') (insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) true) ∧
        InsNWords (L := L) th s s' c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦄ := by
  have hsnn : srcC ≠ .Null := by intro e; subst e; simp [isUt] at hut
  have hcnn : c ≠ .Null := by intro e; subst e; simp [NewKind] at hnk
  apply WP.spec_mono (insert_new_refines th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c a hca hcv he hcnn)
  rintro s' ⟨σ', h1, h2, h3, h4, h5, hW⟩
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  set src := cslotAddr (ps.bv, idxs)
  set dest := cslotAddr (pd.bv, idxd)
  have hs : IsSlot th src := hAs.isSlot
  have hd : IsSlot th dest := hAd.isSlot
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, srcC, hsrcC, hsnn⟩
  have hdestm : dest ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members dest).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hM.next_mem hsrcm with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact (hslot _ h).canonical hP
  have hcv0 := capV_of_capAt hsrcC
  have hctx : InsNCtx th (L.mem s) (L.mem s') G src dest c :=
    { hM := hM, hI := hI, hsrc := hsrcm, hd := hd, hdest := hdestm
      hnext := fun x hx => hW.nextOf' hP hx hd hNc
      hcap := fun x hx => by
        have := hW.capAt' hx he
        rw [capAt_capV] at this
        by_cases h1 : x = dest
        · simp only [h1, ↓reduceIte] at this ⊢; exact eq_of_ok_eq this
        · simp only [h1, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; exact eq_of_ok_eq this
      hrev := fun x hx => hW.revOf' hx
      hfb := fun x hx => hW.fbOf' hx
      hut := by rw [hcv0]; exact hut
      hnk := hnk, hcp := hcp, hcr := hcr
      hcin := by rw [hcv0]; exact hcin
      hreg := hreg
      hno := by rw [hcv0]; exact hno
      hdd := hdd
      hsame := by rw [hcv0]; exact hsame }
  exact ⟨σ', h1, h2, h3, h4, h5, hctx.inv, hW⟩

end

end Fl4Proofs.P3
