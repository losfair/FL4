/-
P3 (DESIGN.md §9), VSpace: the MDB invariants after `DeriveSubframe`'s
`cdt::insert` of a 4 KiB alias of a large frame (l4h 0029).

The alias cap `c` (a frame cap inside the large frame cap's range, its slot
non-revocable: `is_cap_revocable` of a frame cap is false) is linked after
the large frame's slot `src`, as `src`'s child if `src` is revocable (an
original frame cap), else as its sibling (`insG G src dest (revOf src)`;
l4v `cap_insert` with `should_be_parent_of`). With the chunk relation
`srF` (a non-revocable frame cap's slot is unconstrained) the chains stay
chunked, given the range hypothesis `hno` (l4v `caps_no_overlap` for the
large frame: a physical cap meeting it contains it, or is a non-revocable
frame cap).

* `InsFCtx.inv`: `MdbInv` afterwards;
* `utinv_alias`: `UtInv` afterwards.
-/
import Fl4Proofs.P3.VsMakePoolMdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P3 Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## Frame caps and `same_region_as` -/

theorem frame_range (p : U64) (sz : capability.FrameSize) (r : U64) (d m : Bool) (a va : U64) (ep : Bool) :
    baseF (.Frame p sz r d m ep a va) = p.val ∧
      topF (.Frame p sz r d m ep a va) = (core.num.U64.wrapping_add p (maskF (fbitsF sz))).val := by
  unfold baseF topF; rw [ptrF_frame, sizeF_frame]; exact ⟨rfl, rfl⟩

/-- From a frame cap to a frame cap: range containment. -/
theorem srB_frame_of {p : U64} {sz : capability.FrameSize} {r : U64} {d m ep : Bool} {a va : U64}
    {p' : U64} {sz' : capability.FrameSize} {r' : U64} {d' m' ep' : Bool} {a' va' : U64}
    (hw : Within (.Frame p' sz' r' d' m' ep' a' va') (.Frame p sz r d m ep a va))
    (hr : baseF (.Frame p' sz' r' d' m' ep' a' va') ≤ topF (.Frame p' sz' r' d' m' ep' a' va')) :
    srB (.Frame p sz r d m ep a va) (.Frame p' sz' r' d' m' ep' a' va') = true := by
  apply srB_of_eq
  obtain ⟨b1, t1⟩ := frame_range p sz r d m a va ep
  obtain ⟨b2, t2⟩ := frame_range p' sz' r' d' m' a' va' ep'
  have hw1 := hw.1; have hw2 := hw.2
  rw [b1, b2] at hw1; rw [t1, t2] at hw2; rw [b2, t2] at hr
  simp only [objects.same_region_as, frame_bits_eq, mask_eq, lift, bind_ok]
  have e1 : p ≤ p' := by show p.val ≤ p'.val; exact hw1
  have e2 : core.num.U64.wrapping_add p' (maskF (fbitsF sz')) ≤ core.num.U64.wrapping_add p (maskF (fbitsF sz)) := by
    show _ ≤ _; omega
  have e3 : p' ≤ core.num.U64.wrapping_add p' (maskF (fbitsF sz')) := by show p'.val ≤ _; omega
  simp [e1, e2, e3]

theorem isFrame_iff {c : capability.Cap} : isFrame c = true ↔ ∃ p sz r d m ep a va, c = .Frame p sz r d m ep a va := by
  cases c <;> simp [isFrame]

theorem isFr_isFrame {c : capability.Cap} : isFr c = isFrame c := by cases c <;> rfl

/-- `same_region_as` from a frame cap: a frame cap in its range. -/
theorem srB_frame_iff {u : capability.Cap} (hu : isFrame u = true) (v : capability.Cap) :
    srB u v = true ↔ isFrame v = true ∧ Within v u ∧ baseF v ≤ topF v := by
  obtain ⟨p, sz, r, d, m, ep, a, va, rfl⟩ := isFrame_iff.1 hu
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := srB_frame_in h
    exact ⟨by rw [← isFr_isFrame]; exact h1, ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨p', sz', r', d', m', ep', a', va', rfl⟩ := isFrame_iff.1 h1
    exact srB_frame_of h2 h3

/-- Into a frame cap from a cap neither untyped nor a frame: nothing. -/
theorem srB_other_frame {u v : capability.Cap} (hu : isUt u = false) (hf : isFrame u = false)
    (hv : isFrame v = true) : srB u v = false := by
  obtain ⟨p, sz, r, d, m, ep, a, va, rfl⟩ := isFrame_iff.1 hv
  cases e : srB u (.Frame p sz r d m ep a va)
  · rfl
  · obtain ⟨h1, -⟩ := srB_to_frame hu e
    rw [isFr_isFrame, hf] at h1; cases h1

theorem physF_frame' {c : capability.Cap} (h : isFrame c = true) : physF c = true := by
  obtain ⟨p, sz, r, d, m, ep, a, va, rfl⟩ := isFrame_iff.1 h; exact physF_frame _ _ _ _ _ _ _ _

theorem isUt_frame' {c : capability.Cap} (h : isFrame c = true) : isUt c = false := by
  obtain ⟨p, sz, r, d, m, ep, a, va, rfl⟩ := isFrame_iff.1 h; rfl

theorem isBadged_frame {c : capability.Cap} (h : isFrame c = true) : isBadged c = false := by
  obtain ⟨p, sz, r, d, m, ep, a, va, rfl⟩ := isFrame_iff.1 h; rfl

/-- A cap seeing a frame cap `s` sees a frame cap inside it. -/
theorem srB_mono_frame {u s c : capability.Cap} (hs : isFrame s = true) (hc : isFrame c = true)
    (hcin : Within c s) (hcr : baseF c ≤ topF c) (h : srB u s = true) : srB u c = true := by
  cases hU : isUt u
  · cases hF : isFrame u
    · rw [srB_other_frame hU hF hs] at h; cases h
    · obtain ⟨-, hw, -⟩ := (srB_frame_iff hF s).1 h
      refine (srB_frame_iff hF c).2 ⟨hc, ?_, hcr⟩
      unfold Within at *; omega
  · obtain ⟨-, hw, -⟩ := (srB_ut_iff hU s).1 h
    refine (srB_ut_iff hU c).2 ⟨physF_frame' hc, ?_, hcr⟩
    unfold Within at *; omega

/-! ## The ghost tree after the insertion -/

theorem desc_insG {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {src dest : U64} (hdest : dest ∉ G.chains.flatten) (hsd : src ≠ dest) (b : Bool) (y x : U64) :
    Mdb.Desc (insG G src dest b).par y x ↔
      Mdb.Desc G.par y x ∨ (y = dest ∧ ((b = true ∧ x = src) ∨ Mdb.Desc G.par src x)) := by
  have hpd : ∀ z, G.par z ≠ some dest := fun z e => hdest (hM.tree.par_mem z dest e).2
  have hdn : G.par dest = none := by
    cases e : G.par dest with
    | none => rfl
    | some p => exact absurd (hM.tree.par_mem dest p e).1 hdest
  have hnp : (if b then some src else G.par src) ≠ some dest := by
    cases b <;> simp [hsd, hpd src]
  show Mdb.Desc (Function.update G.par dest _) y x ↔ _
  rw [Mdb.desc_update_iff hpd hdn hnp, np_desc_iff]

/-! ## `MdbInv` -/

section
open Mdb

/-- The insertion of the alias `c` at `dest` after the large frame's slot
`src` (see the module docstring). -/
structure InsFCtx (th : TypedHeap) (mem mem' : U64 → U64) (G : MdbGhost) (src dest : U64) (c : capability.Cap) :
    Prop where
  hM : MdbLinks th mem G
  hI : MdbInv mem G
  hsrc : src ∈ G.chains.flatten
  hd : IsSlot th dest
  hdest : dest ∉ G.chains.flatten
  hnext : ∀ a, IsSlot th a → nextOf mem' a =
    if a = dest then nextOf mem src else if a = src then dest else nextOf mem a
  hcap : ∀ a, IsSlot th a → capV mem' a = if a = dest then c else capV mem a
  hrev : ∀ a, IsSlot th a → revOf mem' a = if a = dest then false else revOf mem a
  hfb : ∀ a, IsSlot th a → fbOf mem' a = if a = dest then false else fbOf mem a
  hsF : isFrame (capV mem src) = true
  hcF : isFrame c = true
  hcr : baseF c ≤ topF c
  hcin : Within c (capV mem src)
  hno : ∀ x ∈ G.chains.flatten, Disj (capV mem x) (capV mem src) ∨ (isFrame (capV mem x) = true ∧ revOf mem x = false) ∨
    Within (capV mem src) (capV mem x)

namespace InsFCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c : capability.Cap}
  (h : InsFCtx th mem mem' G src dest c)
include h

local notation "bR" => revOf mem src

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
theorem rd : revOf mem' dest = false := by rw [h.hrev dest h.hd, if_pos rfl]
theorem fd : fbOf mem' dest = false := by rw [h.hfb dest h.hd, if_pos rfl]

theorem pm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : isPM mem' x y = isPM mem x y := by
  unfold isPM
  rw [h.rz hx, h.fz hy]
  exact isPF_congr (by rw [h.cz hx]) (by rw [h.cz hx]) (by rw [h.cz hy]) (by rw [h.cz hy])
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

theorem desc (y x : U64) : Mdb.Desc (insG G src dest bR).par y x ↔
    Mdb.Desc G.par y x ∨ (y = dest ∧ ((bR = true ∧ x = src) ∨ Mdb.Desc G.par src x)) :=
  desc_insG h.hM h.hdest h.sd _ y x

theorem dest_no_desc (x : U64) : ¬ Mdb.Desc G.par dest x := fun e => h.hdest (desc_mem h.hM e).1

theorem memI (z : U64) : z ∈ (insG G src dest bR).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
  mem_flatten_ins h.hsrc

theorem hsr : baseF (capV mem src) ≤ topF (capV mem src) := by
  have := h.hcin; have := h.hcr; unfold Within at *; omega

theorem ssrc : srB (capV mem src) c = true := (srB_frame_iff h.hsF c).2 ⟨h.hcF, h.hcin, h.hcr⟩

/-- An old cap that is not an unconstrained frame sees the alias as it sees
the large frame. -/
theorem k2 {u : U64} (hu : u ∈ G.chains.flatten) (hnf : ¬ (isFrame (capV mem u) = true ∧ revOf mem u = false)) :
    srB (capV mem u) c = srB (capV mem u) (capV mem src) := by
  have hsr := h.hsr
  apply Bool.eq_iff_iff.2
  constructor
  · intro hs
    rcases h.hno u hu with hd | hf | hw
    · exfalso
      cases hU : isUt (capV mem u)
      · cases hF : isFrame (capV mem u)
        · rw [srB_other_frame hU hF h.hcF] at hs; cases hs
        · obtain ⟨-, hw, -⟩ := (srB_frame_iff hF c).1 hs
          have := h.hcin; have := h.hcr; unfold Disj Within at *; omega
      · obtain ⟨-, hw, -⟩ := (srB_ut_iff hU c).1 hs
        have := h.hcin; have := h.hcr; unfold Disj Within at *; omega
    · exact absurd hf hnf
    · cases hU : isUt (capV mem u)
      · cases hF : isFrame (capV mem u)
        · rw [srB_other_frame hU hF h.hcF] at hs; cases hs
        · exact (srB_frame_iff hF _).2 ⟨h.hsF, hw, hsr⟩
      · exact (srB_ut_iff hU _).2 ⟨physF_frame' h.hsF, hw, hsr⟩
  · exact srB_mono_frame h.hsF h.hcF h.hcin h.hcr

theorem orig' (z p : U64) (hz : (insG G src dest bR).par z = some p) : revOf mem' p = true := by
  change Function.update G.par dest (if bR then some src else G.par src) z = some p at hz
  by_cases hzd : z = dest
  · subst hzd
    rw [Function.update_self] at hz
    cases hb : revOf mem src
    · rw [hb] at hz
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz
    · rw [hb] at hz
      have hp : p = src := by simpa using hz.symm
      rw [hp, h.rz h.hsrc]; exact hb
  · rw [Function.update_of_ne hzd] at hz
    rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz

theorem desc' (x y : U64) (hd : Mdb.Desc (insG G src dest bR).par y x) : isPM mem' x y = true := by
  rcases (h.desc y x).1 hd with hd | ⟨hy, hx⟩
  · obtain ⟨h1, h2⟩ := desc_mem h.hM hd
    rw [h.pm h2 h1]; exact h.hI.desc x y hd
  · rw [hy]
    rcases hx with ⟨hb, rfl⟩ | hx
    · unfold isPM
      rw [h.rz h.hsrc, hb, h.cz h.hsrc, h.cd, h.fd]
      simp [isPF, h.ssrc, isBadged_frame h.hsF]
    · have hxm := (desc_mem h.hM hx).2
      have h0 := h.hI.desc x src hx
      unfold isPM at h0 ⊢
      rw [h.rz hxm, h.cz hxm, h.cd, h.fd]
      unfold isPF at h0 ⊢
      simp only [Bool.and_eq_true] at h0 ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := h0
      refine ⟨⟨h1, srB_mono_frame h.hsF h.hcF h.hcin h.hcr h2⟩, ?_⟩
      cases hbx : isBadged (capV mem x)
      · simp
      · exfalso
        cases hU : isUt (capV mem x)
        · cases hF : isFrame (capV mem x)
          · rw [srB_other_frame hU hF h.hsF] at h2; cases h2
          · rw [isBadged_frame hF] at hbx; cases hbx
        · rw [isBadged_ut hU] at hbx; cases hbx

theorem after' (y : U64) (hy : y ∈ (insG G src dest bR).chains.flatten) (hn : nextOf mem' y ≠ 0#u64) (x : U64)
    (hx : x = y ∨ Mdb.Desc (insG G src dest bR).par y x)
    (hnd : ¬ Mdb.Desc (insG G src dest bR).par (nextOf mem' y) x) : isPM mem' x (nextOf mem' y) = false := by
  rcases (h.memI y).1 hy with hyd | hy
  · rw [hyd] at hn hnd hx ⊢
    rw [h.nd] at hn hnd ⊢
    obtain ⟨hN, -⟩ := h.nm hn
    rcases hx with hxd | hx
    · subst hxd
      unfold isPM
      rw [h.rd]
      simp [isPF]
    · have hx' : (bR = true ∧ x = src) ∨ Mdb.Desc G.par src x := by
        rcases (h.desc dest x).1 hx with e | ⟨-, e⟩
        · exact absurd e (h.dest_no_desc x)
        · exact e
      have hx'' : x = src ∨ Mdb.Desc G.par src x := hx'.imp (fun e => e.2) id
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem src) x := fun e => hnd ((h.desc _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx'' with e | e
        · rw [e]; exact h.hsrc
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hN]
      exact h.hI.after src h.hsrc hn x hx'' hnd'
  · by_cases hys : y = src
    · rw [hys] at hn hnd hx hy ⊢
      rw [h.ns] at hn hnd ⊢
      rcases hx with hxs | hx
      · rw [hxs] at hnd ⊢
        cases hb : revOf mem src
        · unfold isPM; rw [h.rz h.hsrc, hb]; simp [isPF]
        · exact absurd ((h.desc dest src).2 (Or.inr ⟨rfl, Or.inl ⟨hb, rfl⟩⟩)) hnd
      · have hx' : Mdb.Desc G.par src x := ((h.desc src x).1 hx).resolve_right (fun e => h.sd e.1)
        exact absurd ((h.desc dest x).2 (Or.inr ⟨rfl, Or.inr hx'⟩)) hnd
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

theorem chunk' (ch' : List U64) (hch' : ch' ∈ (insG G src dest bR).chains) : Mdb.ChunkL (srF mem') ch' := by
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
  have hchm : ∀ z, z ∈ ch → z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨_, hch, hz⟩
  have hsf : ∀ u ∈ G.chains.flatten, ∀ v ∈ G.chains.flatten, srF mem' u v = srF mem u v :=
    fun u hu v hv => srF_congr (h.sm hu hv) (by rw [h.cz hu]) (h.rz hu)
  by_cases hsc : src ∈ ch
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem hsc
    have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 h.hM.tree.nodup).1 _ hch
    rw [Mdb.insAfter_split (Mdb.nodup_mid hnd0).1]
    refine Mdb.chunkL_ins2 (h.hI.chunk _ hch) (fun u hu v hv => hsf u (hchm u hu) v (hchm v hv))
      (fun u hu => ?_) (ca_true (fun v => by simp [srF, h.cd, h.rd, h.hcF]) B) ?_
    · have hum := hchm u hu
      by_cases hnf : isFrame (capV mem u) = true ∧ revOf mem u = false
      · simp [srF, h.cz hum, h.rz hum, hnf.1, hnf.2]
      · unfold srF srM; rw [h.cd, h.cz hum, h.rz hum, h.k2 hum hnf]
    · apply srF_of_srM; unfold srM; rw [h.cz h.hsrc, h.cd]; exact h.ssrc
  · rw [Mdb.insAfter_of_not_mem hsc]
    exact Mdb.chunkL_congr (h.hI.chunk _ hch) (fun u hu v hv => hsf u (hchm u hu) v (hchm v hv))

theorem badges' (y : U64) (hy : y ∈ (insG G src dest bR).chains.flatten) (hn : nextOf mem' y ≠ 0#u64)
    (hbg : isBadged (capV mem' y) = true) (hsr : srM mem' y (nextOf mem' y) = true)
    (hbne : badgeF (capV mem' y) ≠ badgeF (capV mem' (nextOf mem' y)))
    (hb0 : badgeF (capV mem' (nextOf mem' y)) ≠ 0#u64) : fbOf mem' (nextOf mem' y) = true := by
  rcases (h.memI y).1 hy with hyd | hy
  · exfalso
    rw [hyd, h.cd, isBadged_frame h.hcF] at hbg; cases hbg
  · by_cases hys : y = src
    · exfalso; rw [hys, h.cz h.hsrc, isBadged_frame h.hsF] at hbg; cases hbg
    · rw [h.nz hy hys] at hn hsr hbne hb0 ⊢
      have hw := h.nxm hy hn
      rw [h.fz hw]
      rw [h.cz hy, h.cz hw] at hbne
      rw [h.cz hw] at hb0
      rw [h.cz hy] at hbg
      exact h.hI.badges y hy hn hbg (by rw [← h.sm hy hw]; exact hsr) hbne hb0

theorem utrev' (x : U64) (hx : x ∈ (insG G src dest bR).chains.flatten) (hu : isUt (capV mem' x) = true) :
    revOf mem' x = true := by
  rcases (h.memI x).1 hx with hxd | hx
  · rw [hxd, h.cd, isUt_frame' h.hcF] at hu; cases hu
  · rw [h.rz hx]; rw [h.cz hx] at hu; exact h.hI.utrev x hx hu

theorem self' (x : U64) (hx : x ∈ (insG G src dest bR).chains.flatten) (hz : isZb (capV mem' x) = false) :
    srM mem' x x = true := by
  rcases (h.memI x).1 hx with hxd | hx
  · rw [hxd]; unfold srM; rw [h.cd]
    exact (srB_frame_iff h.hcF c).2 ⟨h.hcF, ⟨le_refl _, le_refl _⟩, h.hcr⟩
  · rw [h.cz hx] at hz
    rw [h.sm hx hx]; exact h.hI.self x hx hz

/-- **`MdbInv` after inserting the alias.** -/
theorem inv : MdbInv mem' (insG G src dest bR) :=
  ⟨h.orig', h.desc', h.after', h.chunk', h.badges', h.utrev', h.self'⟩

end InsFCtx

end

/-! ## `UtInv` -/

section
variable {th : TypedHeap} {mem memf : U64 → U64} {G : MdbGhost}

/-- **`UtInv` after inserting a cap inside a frame cap's range**, as its
child or sibling. -/
theorem utinv_alias (hM : MdbLinks th mem G) (hI : MdbInv mem G) (hU : UtInv mem G) {src dest : U64} (b : Bool)
    (hsrc : src ∈ G.chains.flatten) (hsF : isFrame (capV mem src) = true) (hdest : dest ∉ G.chains.flatten)
    {c : capability.Cap} (hcF : isFrame c = true) (hcin : Within c (capV mem src)) (hcr : baseF c ≤ topF c)
    (hcf : capV memf dest = c) (hco : ∀ y ∈ G.chains.flatten, capV memf y = capV mem y) :
    UtInv memf (insG G src dest b) := by
  have hsd : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have memI : ∀ z, z ∈ (insG G src dest b).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
    fun z => mem_flatten_ins hsrc
  have desc := desc_insG hM hdest hsd b
  have hsp : physF (capV mem src) = true := physF_frame' hsF
  have hcapU : ∀ u ∈ (insG G src dest b).chains.flatten, ∀ pu su fu du, capV memf u = .Untyped pu su fu du →
      u ∈ G.chains.flatten ∧ capV mem u = .Untyped pu su fu du := by
    intro u hu pu su fu du hcu
    rcases (memI u).1 hu with rfl | hu
    · rw [hcf] at hcu; rw [hcu] at hcF; cases hcF
    · exact ⟨hu, by rw [← hco u hu]; exact hcu⟩
  -- an untyped cap meeting the frame is an ancestor of it
  have hanc : ∀ u ∈ G.chains.flatten, ∀ pu su fu du, capV mem u = .Untyped pu su fu du →
      ¬ Disj (capV mem src) (capV mem u) → Mdb.Desc G.par src u := by
    intro u hu pu su fu du hcu hdj
    have hus : u ≠ src := by intro e; subst e; rw [hcu] at hsF; cases hsF
    rcases hU.drange u hu pu su fu du hcu src hsrc (Ne.symm hus) hsp hdj with h | h
    · exact h
    · exfalso
      have := hI.desc src u h
      unfold isPM isPF at this
      simp only [Bool.and_eq_true] at this
      obtain ⟨⟨-, h2⟩, -⟩ := this
      have h3 := ((srB_frame_iff hsF _).1 h2).1
      rw [hcu] at h3; cases h3
  have hcs : baseF (capV mem src) ≤ topF (capV mem src) := by unfold Within at hcin; omega
  refine ⟨fun z hz hp => ?_, fun u hu pu su fu du hcu y hy => ?_, fun u hu pu su fu du hcu y hy hp => ?_,
    fun u hu y hy huy pu su fu fu' du du' hcu hcy => ?_, fun u hu pu su fu du hcu => ?_,
    fun u hu pu su fu du hcu y hy hyu hp hdj => ?_⟩
  · rcases (memI z).1 hz with rfl | hz
    · rw [hcf]; exact hcr
    · rw [hco z hz] at hp ⊢; exact hU.reg z hz hp
  · obtain ⟨huG, hcu'⟩ := hcapU u hu pu su fu du hcu
    rcases (desc y u).1 hy with hy | ⟨rfl, hux⟩
    · rw [hco y (desc_mem hM hy).1]; exact hU.inc u huG pu su fu du hcu' y hy
    · rw [hcf]
      rcases hux with ⟨-, rfl⟩ | hux
      · rw [hcu'] at hsF; cases hsF
      · obtain ⟨-, h2, h3⟩ := hU.inc u huG pu su fu du hcu' src hux
        unfold Within at hcin
        exact ⟨physF_frame' hcF, by omega, by omega⟩
  · obtain ⟨huG, hcu'⟩ := hcapU u hu pu su fu du hcu
    rw [hco u huG]
    rcases (memI y).1 hy with rfl | hy
    · left
      rw [hcf]
      rcases hU.noov u huG pu su fu du hcu' src hsrc hsp with h | ⟨h, -⟩
      · unfold DisjR at h ⊢; unfold Within at hcin; omega
      · rw [isUt_frame' hsF] at h; cases h
    · rw [hco y hy] at hp ⊢; exact hU.noov u huG pu su fu du hcu' y hy hp
  · obtain ⟨hu', hcu'⟩ := hcapU u hu pu su fu du hcu
    obtain ⟨hy', hcy'⟩ := hcapU y hy pu su fu' du' hcy
    exact hU.excl u hu' y hy' huy pu su fu fu' du du' hcu' hcy'
  · obtain ⟨hu', hcu'⟩ := hcapU u hu pu su fu du hcu
    exact hU.fib u hu' pu su fu du hcu'
  · obtain ⟨huG, hcu'⟩ := hcapU u hu pu su fu du hcu
    rw [hco u huG] at hdj
    rcases (memI y).1 hy with rfl | hy'
    · left
      have hdj' : ¬ Disj (capV mem src) (capV mem u) := by
        rw [hcf] at hdj; unfold Disj at hdj ⊢; unfold Within at hcin; omega
      exact (desc _ _).2 (Or.inr ⟨rfl, Or.inr (hanc u huG pu su fu du hcu' hdj')⟩)
    · rw [hco y hy'] at hp hdj
      rcases hU.drange u huG pu su fu du hcu' y hy' hyu hp hdj with h | h
      · exact Or.inl ((desc _ _).2 (Or.inl h))
      · exact Or.inr ((desc _ _).2 (Or.inl h))

end

end

end Fl4Proofs.P3.Vs
