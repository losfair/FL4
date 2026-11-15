/-
P3 (DESIGN.md §9), CSpace: **inserting a control cap's child** (an IRQ
handler cap from the IRQ control cap, an IO port cap from the IO port
control cap): `cdt::insert` refines `cap_insert` and keeps `MdbInv`.

Unlike `insert_full` the new cap has another shape than its source. What
`MdbInv` needs instead (`CtlCtx`) is that the new cap is fresh: no cap of
the MDB is in its region (`hfr`; l4v: no handler cap for an inactive IRQ,
no IO port cap for a free range). Then the control cap's region test
treats the new cap as the control cap itself (`CtlPair.left`), the new cap's
region holds nothing else, and its parent test from the source is the
source's revocable bit.
-/
import Fl4Proofs.P3.MdbFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
set_option maxRecDepth 4096
open fl4_core Classical

noncomputable section

/-- A control cap and a cap it issues. -/
def CtlPair : capability.Cap → capability.Cap → Prop
  | .IrqControl, .IrqHandler _ => True
  | .IoPortControl, .IoPort .. => True
  | _, _ => False

theorem srB_ok_true {a b : capability.Cap} (h : srB a b = true) : objects.same_region_as a b = ok true := by
  rw [srB_eq, h]

section
variable {sc c : capability.Cap}

theorem CtlPair.cases (h : CtlPair sc c) :
    (sc = .IrqControl ∧ ∃ i, c = .IrqHandler i) ∨ (sc = .IoPortControl ∧ ∃ f l vcpu, c = .IoPort f l vcpu) := by
  cases sc <;> cases c <;> simp_all [CtlPair]

theorem CtlPair.sr (h : CtlPair sc c) : srB sc c = true := by
  rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩ <;> apply srB_of_eq <;> simp [objects.same_region_as]

theorem CtlPair.self (h : CtlPair sc c) : srB c c = true := by
  rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩ <;> apply srB_of_eq <;> simp [objects.same_region_as]

theorem CtlPair.facts (h : CtlPair sc c) :
    isBadged c = false ∧ isBadged sc = false ∧ isUt c = false ∧ isUt sc = false ∧ isZb c = false ∧
      isZb sc = false ∧ c ≠ .Null ∧ sc ≠ .Null ∧ revF c sc = true ∧ fullF sc c = none ∧
      SameBadgeKind c sc := by
  rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩ <;>
    simp [isBadged, isUt, isZb, revF, fullF, SameBadgeKind]

theorem srB_irqH (a : capability.Cap) (i : U64) :
    srB a (.IrqHandler i) = (decide (a = .IrqControl) || decide (a = .IrqHandler i)) := by
  apply srB_of_eq; cases a <;> simp [objects.same_region_as, objects.cap_is_physical]
  split_ifs <;> simp_all [eq_comm]

theorem srB_irqC (a : capability.Cap) : srB a .IrqControl = decide (a = .IrqControl) := by
  apply srB_of_eq; cases a <;> simp [objects.same_region_as, objects.cap_is_physical]

theorem srB_ioP (a : capability.Cap) (f l vcpu : U64) :
    srB a (.IoPort f l vcpu) = (decide (a = .IoPortControl) || decide (shape a = .IoPort f l 0#u64)) := by
  apply srB_of_eq; cases a <;> simp [objects.same_region_as, objects.cap_is_physical, shape]
  split_ifs <;> simp_all [eq_comm]

theorem srB_ioC (a : capability.Cap) : srB a .IoPortControl = decide (a = .IoPortControl) := by
  apply srB_of_eq; cases a <;> simp [objects.same_region_as, objects.cap_is_physical]

/-- The control cap's region test sees the fresh cap as the control cap. -/
theorem CtlPair.left (h : CtlPair sc c) {a : capability.Cap} (ha : srB c a = false) : srB a c = srB a sc := by
  have hs := h.self
  rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩
  · rw [srB_irqH, srB_irqC]
    by_cases e : a = .IrqHandler i
    · subst e; rw [hs] at ha; cases ha
    · simp [e]
  · rw [srB_ioP, srB_ioC]
    by_cases e : shape a = .IoPort f l 0#u64
    · have ha' := srB_ok_true hs
      have hsame : srB (.IoPort f l vcpu) a = true := by
        apply srB_of_eq
        cases a <;> simp [shape] at e
        obtain ⟨rfl, rfl⟩ := e
        simp [objects.same_region_as]
      rw [hsame] at ha; cases ha
    · simp [e]

/-- A passed parent test to the control cap passes to the fresh cap. -/
theorem CtlPair.pf_child (h : CtlPair sc c) {rv : Bool} {ca : capability.Cap} {f f' : Bool}
    (hp : isPF rv ca sc f = true) : isPF rv ca c f' = true := by
  unfold Fl4Proofs.P3.isPF at hp ⊢
  simp only [Bool.and_eq_true] at hp ⊢
  obtain ⟨⟨h1, h2⟩, -⟩ := hp
  rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩
  · have e := srB_ok_true h2
    cases ca <;> simp [objects.same_region_as, objects.cap_is_physical] at e
    refine ⟨⟨h1, h.sr⟩, by simp [isBadged]⟩
  · have e := srB_ok_true h2
    cases ca <;> simp [objects.same_region_as, objects.cap_is_physical] at e
    refine ⟨⟨h1, h.sr⟩, by simp [isBadged]⟩

theorem CtlPair.pf_eq (h : CtlPair sc c) (rv f : Bool) : isPF rv sc c f = rv := by
  unfold Fl4Proofs.P3.isPF; rw [h.sr, h.facts.2.1]; simp

/-- The spec's `should_be_parent_of`, for a control cap's child. -/
theorem CtlPair.sbp (h : CtlPair sc c) (io : Bool) :
    decide (Fl4Spec.shouldBeParentOf (absCap sc) io (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap sc)))) = isPF io sc c (revF c sc) := by
  rw [h.pf_eq]
  rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩
  · cases io <;> simp [Fl4Spec.shouldBeParentOf, absCap, Fl4Spec.sameRegionAs]
  · cases io <;> simp [Fl4Spec.shouldBeParentOf, absCap, Fl4Spec.sameRegionAs, Fl4Spec.archSameRegionAs,
      Fl4Spec.shouldBeArchParentOf]

end

/-! ## Chunks -/

namespace Mdb
variable {α : Type}

theorem ca_allfalse {R : α → α → Bool} {a : α} {L : List α} (h : ∀ v ∈ L, R a v = false) : CA R a L := by
  induction L with
  | nil => trivial
  | cons v L ih =>
    exact ⟨fun _ w hw => h w (by simp [hw]), ih (fun w hw => h w (by simp [hw]))⟩

/-- Inserting `d` right after `s`, `d`'s region holding nothing else, others
seeing `d` as `s`. -/
theorem chunkL_ins_fresh {R R' : α → α → Bool} {s d : α} {A B : List α} (h : ChunkL R (A ++ s :: B))
    (he : ∀ u ∈ A ++ s :: B, ∀ v ∈ A ++ s :: B, R' u v = R u v)
    (hd1 : ∀ u ∈ A ++ s :: B, R' u d = R u s) (hd2 : ∀ v ∈ A ++ s :: B, R' d v = false)
    (hss : R' s d = true) : ChunkL R' (A ++ s :: d :: B) := by
  induction A with
  | nil =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨fun h0 => (by rw [hss] at h0; cases h0), ca_congr h1 (fun v hv => he s (by simp) v (by simp [hv]))⟩,
      ca_allfalse (fun v hv => hd2 v (by simp [hv])), ?_⟩
    have hB : ChunkL R B := h2
    clear h1 h2
    have he' : ∀ u ∈ B, ∀ v ∈ B, R' u v = R u v := fun u hu v hv => he u (by simp [hu]) v (by simp [hv])
    clear he hd1 hd2 hss
    induction B with
    | nil => trivial
    | cons b B ih =>
      exact ⟨ca_congr hB.1 (fun v hv => he' b (by simp) v (by simp [hv])),
        ih hB.2 (fun u hu v hv => he' u (by simp [hu]) v (by simp [hv]))⟩
  | cons a A ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨ca_ins h1 (fun v hv => he a (by simp) v (by simp at hv ⊢; tauto)) (hd1 a (by simp)), ?_⟩
    exact ih h2 (fun u hu v hv => he u (by simp at hu ⊢; tauto) v (by simp at hv ⊢; tauto))
      (fun u hu => hd1 u (by simp at hu ⊢; tauto)) (fun v hv => hd2 v (by simp at hv ⊢; tauto))

end Mdb

/-! ## `MdbInv` -/

/-- The situation of a control-child insertion, at the level of the slot
contents. -/
structure CtlCtx (th : TypedHeap) (mem mem' : U64 → U64) (G : MdbGhost) (src dest : U64)
    (c : capability.Cap) : Prop where
  hM : MdbLinks th mem G
  hI : MdbInv mem G
  hsrc : src ∈ G.chains.flatten
  hd : IsSlot th dest
  hdest : dest ∉ G.chains.flatten
  hnext : ∀ a, IsSlot th a → nextOf mem' a =
    if a = dest then nextOf mem src else if a = src then dest else nextOf mem a
  hcap : ∀ a, IsSlot th a → capV mem' a = if a = dest then c else capV mem a
  hrev : ∀ a, IsSlot th a → revOf mem' a = if a = dest then revF c (capV mem src) else revOf mem a
  hfb : ∀ a, IsSlot th a → fbOf mem' a = if a = dest then revF c (capV mem src) else fbOf mem a
  hctl : CtlPair (capV mem src) c
  hfr : ∀ y ∈ G.chains.flatten, srB c (capV mem y) = false

namespace CtlCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c : capability.Cap}
  (h : CtlCtx th mem mem' G src dest c)
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
theorem rd : revOf mem' dest = revF c (capV mem src) := by rw [h.hrev dest h.hd, if_pos rfl]
theorem fd : fbOf mem' dest = revF c (capV mem src) := by rw [h.hfb dest h.hd, if_pos rfl]

theorem pm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : isPM mem' x y = isPM mem x y := by
  unfold isPM; rw [h.rz hx, h.fz hy, h.cz hx, h.cz hy]
theorem sm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : srM mem' x y = srM mem x y := by
  unfold srM; rw [h.cz hx, h.cz hy]

theorem sf {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : srF mem' x y = srF mem x y :=
  srF_congr (h.sm hx hy) (by rw [h.cz hx]) (h.rz hx)

theorem cnf : isFrame c = false := by
  rcases h.hctl.cases with ⟨-, i, rfl⟩ | ⟨-, f, l, vcpu, rfl⟩ <;> rfl

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

theorem desc (b : Bool) (y x : U64) : Mdb.Desc (insG G src dest b).par y x ↔
    Mdb.Desc G.par y x ∨ (y = dest ∧ ((b = true ∧ x = src) ∨ Mdb.Desc G.par src x)) := by
  have hnp : (if b then some src else G.par src) ≠ some dest := by
    cases b <;> simp [h.sd, h.pd src]
  show Mdb.Desc (Function.update G.par dest _) y x ↔ _
  rw [Mdb.desc_update_iff h.pd h.dn hnp, np_desc_iff]

theorem dest_no_desc (x : U64) : ¬ Mdb.Desc G.par dest x := fun e => h.hdest (desc_mem h.hM e).1

theorem memI (b : Bool) (z : U64) : z ∈ (insG G src dest b).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
  mem_flatten_ins h.hsrc

theorem psd : isPM mem' src dest = isPF (revOf mem src) (capV mem src) c (revF c (capV mem src)) := by
  unfold isPM; rw [h.rz h.hsrc, h.cz h.hsrc, h.cd, h.fd]

local notation "bI" => isPF (revOf mem src) (capV mem src) c (revF c (capV mem src))

theorem orig' (z p : U64) (hz : (insG G src dest bI).par z = some p) : revOf mem' p = true := by
  change Function.update G.par dest (if bI then some src else G.par src) z = some p at hz
  by_cases hzd : z = dest
  · subst hzd
    rw [Function.update_self] at hz
    cases hb : bI
    · rw [hb] at hz; simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz
    · rw [hb] at hz
      have hp : p = src := by simpa using hz.symm
      rw [hp, h.rz h.hsrc]
      simp only [isPF, Bool.and_eq_true] at hb
      exact hb.1.1
  · rw [Function.update_of_ne hzd] at hz
    rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz

theorem desc' (x y : U64) (hd : Mdb.Desc (insG G src dest bI).par y x) : isPM mem' x y = true := by
  rcases (h.desc bI y x).1 hd with hd | ⟨hy, hd⟩
  · obtain ⟨h1, h2⟩ := desc_mem h.hM hd
    rw [h.pm h2 h1]; exact h.hI.desc x y hd
  · rw [hy]
    rcases hd with ⟨hb, hxs⟩ | hd
    · rw [hxs, h.psd]; exact hb
    · have hx := (desc_mem h.hM hd).2
      have h0 := h.hI.desc x src hd
      unfold isPM at h0 ⊢
      rw [h.rz hx, h.cd, h.fd, h.cz hx]
      exact h.hctl.pf_child h0

theorem after_dest (hn : nextOf mem src ≠ 0#u64) :
    isPF (revF c (capV mem src)) c (capV mem (nextOf mem src)) (fbOf mem (nextOf mem src)) = false := by
  obtain ⟨hN, -⟩ := h.nm hn
  unfold Fl4Proofs.P3.isPF; rw [h.hfr _ hN]; simp

theorem after' (y : U64) (hy : y ∈ (insG G src dest bI).chains.flatten) (hn : nextOf mem' y ≠ 0#u64) (x : U64)
    (hx : x = y ∨ Mdb.Desc (insG G src dest bI).par y x)
    (hnd : ¬ Mdb.Desc (insG G src dest bI).par (nextOf mem' y) x) : isPM mem' x (nextOf mem' y) = false := by
  rcases (h.memI bI y).1 hy with hyd | hy
  · rw [hyd] at hn hnd hx ⊢
    rw [h.nd] at hn hnd ⊢
    obtain ⟨hN, -⟩ := h.nm hn
    rcases hx with hxd | hx
    · subst hxd
      unfold isPM
      rw [h.rd, h.cd, h.fz hN, h.cz hN]
      exact h.after_dest hn
    · have hx' : x = src ∨ Mdb.Desc G.par src x := by
        rcases (h.desc bI dest x).1 hx with e | ⟨-, ⟨-, e⟩ | e⟩
        · exact absurd e (h.dest_no_desc x)
        · exact Or.inl e
        · exact Or.inr e
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem src) x := fun e => hnd ((h.desc bI _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact h.hsrc
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hN]
      exact h.hI.after src h.hsrc hn x hx' hnd'
  · by_cases hys : y = src
    · rw [hys] at hn hnd hx hy ⊢
      rw [h.ns] at hn hnd ⊢
      rcases hx with hxy | hx
      · rw [hxy] at hnd ⊢
        rw [h.psd]
        cases hb : bI
        · rfl
        · exact absurd ((h.desc bI dest src).2 (Or.inr ⟨rfl, Or.inl ⟨hb, rfl⟩⟩)) hnd
      · have hx' : Mdb.Desc G.par src x := ((h.desc bI src x).1 hx).resolve_right (fun e => h.sd e.1)
        exact absurd ((h.desc bI dest x).2 (Or.inr ⟨rfl, Or.inr hx'⟩)) hnd
    · rw [h.nz hy hys] at hn hnd ⊢
      have hw := h.nxm hy hn
      have hx' : x = y ∨ Mdb.Desc G.par y x := by
        rcases hx with e | e
        · exact Or.inl e
        · exact Or.inr (((h.desc bI y x).1 e).resolve_right (fun e => h.dne hy e.1))
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem y) x := fun e => hnd ((h.desc bI _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact hy
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hw]
      exact h.hI.after y hy hn x hx' hnd'

theorem chunk' (ch' : List U64) (hch' : ch' ∈ (insG G src dest bI).chains) : Mdb.ChunkL (srF mem') ch' := by
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
  have hchm : ∀ z, z ∈ ch → z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨_, hch, hz⟩
  by_cases hsc : src ∈ ch
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem hsc
    have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 h.hM.tree.nodup).1 _ hch
    rw [Mdb.insAfter_split (Mdb.nodup_mid hnd0).1]
    refine Mdb.chunkL_ins_fresh (h.hI.chunk _ hch) (fun u hu v hv => h.sf (hchm u hu) (hchm v hv))
      (fun u hu => srF_congr ?_ (by rw [h.cz (hchm u hu)]) (h.rz (hchm u hu))) (fun v hv => ?_) (srF_of_srM ?_)
    · unfold srM; rw [h.cd, h.cz (hchm u hu)]; exact h.hctl.left (h.hfr u (hchm u hu))
    · rw [srF_nf (by rw [h.cd]; exact h.cnf)]
      unfold srM; rw [h.cd, h.cz (hchm v hv)]; exact h.hfr v (hchm v hv)
    · unfold srM; rw [h.cz h.hsrc, h.cd]; exact h.hctl.sr
  · rw [Mdb.insAfter_of_not_mem hsc]
    exact Mdb.chunkL_congr (h.hI.chunk _ hch) (fun u hu v hv => h.sf (hchm u hu) (hchm v hv))

theorem badges' (y : U64) (hy : y ∈ (insG G src dest bI).chains.flatten) (hn : nextOf mem' y ≠ 0#u64)
    (hbg : isBadged (capV mem' y) = true) (hsr : srM mem' y (nextOf mem' y) = true)
    (hbne : badgeF (capV mem' y) ≠ badgeF (capV mem' (nextOf mem' y)))
    (hb0 : badgeF (capV mem' (nextOf mem' y)) ≠ 0#u64) : fbOf mem' (nextOf mem' y) = true := by
  rcases (h.memI bI y).1 hy with hyd | hy
  · rw [hyd, h.cd, h.hctl.facts.1] at hbg; cases hbg
  · by_cases hys : y = src
    · rw [hys, h.cz h.hsrc, h.hctl.facts.2.1] at hbg; cases hbg
    · rw [h.nz hy hys] at hn hsr hbne hb0 ⊢
      have hw := h.nxm hy hn
      rw [h.fz hw]
      rw [h.cz hy, h.cz hw] at hbne
      rw [h.cz hw] at hb0
      rw [h.cz hy] at hbg
      exact h.hI.badges y hy hn hbg (by rw [← h.sm hy hw]; exact hsr) hbne hb0

theorem utrev' (x : U64) (hx : x ∈ (insG G src dest bI).chains.flatten) (hu : isUt (capV mem' x) = true) :
    revOf mem' x = true := by
  rcases (h.memI bI x).1 hx with hxd | hx
  · rw [hxd, h.cd, h.hctl.facts.2.2.1] at hu; cases hu
  · rw [h.rz hx]; rw [h.cz hx] at hu; exact h.hI.utrev x hx hu

theorem self' (x : U64) (hx : x ∈ (insG G src dest bI).chains.flatten) (hz : isZb (capV mem' x) = false) :
    srM mem' x x = true := by
  rcases (h.memI bI x).1 hx with hxd | hx
  · rw [hxd]; unfold srM; rw [h.cd]; exact h.hctl.self
  · rw [h.cz hx] at hz
    rw [h.sm hx hx]; exact h.hI.self x hx hz

/-- **`MdbInv` after a control-child insertion.** -/
theorem inv : MdbInv mem' (insG G src dest bI) :=
  ⟨h.orig', h.desc', h.after', h.chunk', h.badges', h.utrev', h.self'⟩

end CtlCtx

/-! ## `cdt::insert` -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem insert_ctl_mdbinv (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hI : MdbInv (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hctl : CtlPair srcC c)
    (hfr : ∀ y ∈ G.chains.flatten, srB c (capV (L.mem s) y) = false) :
    cdt.insert st s c src dest ⦃ s' =>
      MdbInv (L.mem s') (insG G src dest (isPF (revOf (L.mem s) src) srcC c (revF c srcC))) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  have hfull := hctl.facts.2.2.2.2.2.2.2.2.2.1
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW
  have := CtlCtx.inv (c := c) (th := th) (mem := L.mem s) (mem' := L.mem s') (G := G) (src := src) (dest := dest)
    { hM := hM, hI := hI, hsrc := hsrc, hd := hd, hdest := hdest
      hnext := fun a ha => hW.nextOf' hP ha hd hne hNc
      hcap := fun a ha => by
        have := hW.capAt' ha he hes hsrcC
        rw [capAt_capV] at this
        by_cases h1 : a = dest
        · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
        · by_cases h2 : a = src
          · subst h2; simp only [h1, ↓reduceIte, hfull, Option.getD_none] at this ⊢
            rw [hcv]; simpa using this
          · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this
      hrev := fun a ha => by rw [hW.revOf' ha hne, hcv]
      hfb := fun a ha => by rw [hW.fbOf' ha hne, hcv]
      hctl := by rw [hcv]; exact hctl
      hfr := hfr }
  rw [hcv] at this
  exact this

/-- **`cdt::insert` of a control cap's child refines `cap_insert` and keeps
`MdbInv`**, for slots of CNodes, the destination empty and the new cap
fresh. -/
theorem insert_ctl_full (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (hwf : CapWf c) (hcv : CapValid th c) (he : EncWf c) (hctl : CtlPair srcC c)
    (hfr : ∀ y ∈ G.chains.flatten, srB c (capV (L.mem s) y) = false) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) (absCap c) (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ⦄ := by
  obtain ⟨-, -, -, -, -, hzb, hcnn, hsnn, -, -, hk⟩ := hctl.facts
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hcv0 := capV_of_capAt hsrcC
  have hb : decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)))) =
      isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) := by
    rw [hC.orig _ hAs]; exact hctl.sbp _
  have hsib : ¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC))) →
      ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) := by
    intro hn y hy
    have h0 : isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) = false := by
      rw [← hb]; simpa using hn
    rw [hctl.pf_eq] at h0
    obtain ⟨z, hz⟩ := desc_tail_child hy
    rw [hI.orig z _ hz] at h0; cases h0
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (insert_refines' th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c _ ⟨hwf, rfl⟩ hcv he hcnn hk)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (insert_ctl_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hctl hfr)
  rw [h1] at h2
  have e := eq_of_ok_eq h2
  subst e
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hins, hR', hV', hM', hC', hG'⟩ := hpost hsib
  refine ⟨σ', G', hins, hR', hV', hM', hC', ?_⟩
  rw [hG', hb]; exact hinv

end

end

end Fl4Proofs.P3
