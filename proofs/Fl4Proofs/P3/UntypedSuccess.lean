/-
P3 (DESIGN.md §9), untyped: **`untyped::retype` (no reset) refines l4v
`invoke_untyped`** for the non-arch types but the TCB, from the state
after `decode` and `set_thread_state Restart`.

* the untyped cap's new free index keeps the MDB relations (`UtCapUpd`:
  only the cap words of its slot change, to a cap of the same shape);
* `retype_full`: the cap update, `retype_region` (`extend_cnode_rel` /
  `extend_other_rel`) and the loop (`create_loop_rel`), against the spec's
  `invoke_untyped`; the result is related (`StateRel`, `SlotsValid`,
  `MdbLinks`, `CdtRel`, `MdbInv`) for the grown typed heap.

The hypotheses on the state are the untyped invariant `UtInv` (l4v
`untyped_inc`, `caps_no_overlap`) for the untyped cap's slot, the free
region being free (`RegionFree`) and zero (`ZeroRegion`), and `horig`.
-/
import Fl4Proofs.P3.UntypedUtInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## Changing a cap to one of the same shape -/

/-- `m'` is `m` with only the cap of slot `a` changed, to one of the same
shape and badge. -/
structure CapShapeUpd (th : TypedHeap) (m m' : U64 → U64) (a : U64) : Prop where
  links : ∀ x, IsSlot th x → m' (wordOf x 16#u64) = m (wordOf x 16#u64) ∧ m' (wordOf x 24#u64) = m (wordOf x 24#u64)
  caps : ∀ x, IsSlot th x → x ≠ a → capV m' x = capV m x
  shp : shape (capV m' a) = shape (capV m a)
  bdg : badgeF (capV m' a) = badgeF (capV m a)
  nn : capV m' a ≠ .Null

namespace CapShapeUpd
variable {th : TypedHeap} {m m' : U64 → U64} {a : U64} (h : CapShapeUpd th m m' a)
include h

theorem nx {x : U64} (hx : IsSlot th x) : nextOf m' x = nextOf m x := by
  unfold Fl4Proofs.P3.nextOf; rw [(h.links x hx).2]
theorem pv {x : U64} (hx : IsSlot th x) : prevOf m' x = prevOf m x := (h.links x hx).1
theorem rv {x : U64} (hx : IsSlot th x) : revOf m' x = revOf m x := by
  unfold Fl4Proofs.P3.revOf; rw [(h.links x hx).2]
theorem fb {x : U64} (hx : IsSlot th x) : fbOf m' x = fbOf m x := by
  unfold Fl4Proofs.P3.fbOf; rw [(h.links x hx).2]
theorem sh (x : U64) (hx : IsSlot th x) : shape (capV m' x) = shape (capV m x) ∧ badgeF (capV m' x) = badgeF (capV m x) := by
  by_cases hxa : x = a
  · subst hxa; exact ⟨h.shp, h.bdg⟩
  · rw [h.caps x hx hxa]; exact ⟨rfl, rfl⟩

theorem mdbLinks {G : MdbGhost} (hM : MdbLinks th m G) (ha : a ∈ G.chains.flatten) : MdbLinks th m' G := by
  have hs : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x hx => ((hM.members x).1 hx).1
  refine ⟨hM.tree, hM.ne_nil, ?_, ?_, ?_, ?_⟩
  · intro ch hch
    apply (hM.chain ch hch).imp_of_mem_imp
    rintro x y hx hy ⟨h1, h2⟩
    exact ⟨by rw [h.nx (hs x (List.mem_flatten.2 ⟨_, hch, hx⟩)), h1],
      by rw [h.pv (hs y (List.mem_flatten.2 ⟨_, hch, hy⟩)), h2]⟩
  · intro ch hch hne
    rw [h.pv (hs _ (List.mem_flatten.2 ⟨_, hch, List.head_mem hne⟩))]; exact hM.head ch hch hne
  · intro ch hch hne
    rw [h.nx (hs _ (List.mem_flatten.2 ⟨_, hch, List.getLast_mem hne⟩))]; exact hM.last ch hch hne
  · intro x
    rw [hM.members x]
    by_cases hxa : x = a
    · subst hxa
      have hxs := hs x ha
      obtain ⟨-, c0, hc0, hn0⟩ := (hM.members x).1 ha
      constructor
      · intro _; exact ⟨hxs, capV m' x, capAt_capV _ _, h.nn⟩
      · intro _; exact ⟨hxs, c0, hc0, hn0⟩
    · constructor
      · rintro ⟨hx, c, hc, hn⟩
        refine ⟨hx, c, ?_, hn⟩
        rw [capAt_capV, h.caps x hx hxa, ← capAt_capV]; exact hc
      · rintro ⟨hx, c, hc, hn⟩
        refine ⟨hx, c, ?_, hn⟩
        rw [capAt_capV, ← h.caps x hx hxa, ← capAt_capV]; exact hc

theorem mdbInv {G : MdbGhost} (hM : MdbLinks th m G) (hI : MdbInv m G) : MdbInv m' G := by
  have hsl : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hnx : ∀ y ∈ G.chains.flatten, nextOf m y ≠ 0#u64 → nextOf m y ∈ G.chains.flatten := by
    intro y hy hn
    rcases hM.next_mem hy with h | ⟨h, -⟩
    · exact absurd h hn
    · exact h
  have hpm : ∀ x y, x ∈ G.chains.flatten → y ∈ G.chains.flatten → isPM m' x y = isPM m x y := by
    intro x y hx hy
    unfold isPM
    rw [h.rv (hsl x hx), h.fb (hsl y hy)]
    exact isPF_congr (h.sh x (hsl x hx)).1 (h.sh x (hsl x hx)).2 (h.sh y (hsl y hy)).1 (h.sh y (hsl y hy)).2
  have hsr : ∀ x y, x ∈ G.chains.flatten → y ∈ G.chains.flatten → srM m' x y = srM m x y := by
    intro x y hx hy
    unfold srM; exact srB_congr (h.sh x (hsl x hx)).1 (h.sh y (hsl y hy)).1
  refine ⟨fun c p hp => ?_, fun x y hd => ?_, fun y hy hn x hx hd => ?_, fun ch hch => ?_,
    fun y hy hn hb hs hbd hb0 => ?_, fun x hx hu => ?_, fun x hx hz => ?_⟩
  · rw [h.rv (hsl p (hM.tree.par_mem _ _ hp).2)]; exact hI.orig c p hp
  · obtain ⟨h1, h2⟩ := desc_mem hM hd
    rw [hpm x y h2 h1]; exact hI.desc x y hd
  · have hy' := hsl y hy
    rw [h.nx hy'] at hn hd ⊢
    have hx' : x ∈ G.chains.flatten := by rcases hx with rfl | hx; exact hy; exact (desc_mem hM hx).2
    rw [hpm x _ hx' (hnx y hy hn)]; exact hI.after y hy hn x hx hd
  · refine Mdb.chunkL_congr (hI.chunk ch hch) (fun u hu v hv => srF_congr ?_ ?_ ?_)
    · exact hsr u v (List.mem_flatten.2 ⟨_, hch, hu⟩) (List.mem_flatten.2 ⟨_, hch, hv⟩)
    · exact isFrame_of_shape (h.sh u (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))).1
    · exact h.rv (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))
  · have hy' := hsl y hy
    rw [h.nx hy'] at hn hs hbd hb0 ⊢
    have hn' := hnx y hy hn
    rw [(h.sh y hy').2] at hbd
    rw [(h.sh _ (hsl _ hn')).2] at hbd hb0
    rw [isBadged_of_shape (h.sh y hy').1] at hb
    rw [hsr y _ hy hn'] at hs
    rw [h.fb (hsl _ hn')]; exact hI.badges y hy hn hb hs hbd hb0
  · rw [isUt_of_shape (h.sh x (hsl x hx)).1] at hu; rw [h.rv (hsl x hx)]; exact hI.utrev x hx hu
  · rw [isZb_of_shape (h.sh x (hsl x hx)).1] at hz; rw [hsr x x hx hx]; exact hI.self x hx hz

theorem cdtRel {Z : Type} {σ σ' : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th m σ G)
    (hcdt : σ'.cdt = σ.cdt) (hio : σ'.isOriginalCap = σ.isOriginalCap) : CdtRel th m' σ' G := by
  refine ⟨fun sl hs => ?_, fun sl q hq => ?_, fun sl hs => ?_, hC.par_slot⟩
  · rw [hcdt]; exact hC.cdt sl hs
  · rw [hcdt] at hq; exact hC.cdt_slot sl q hq
  · rw [hio, hC.orig sl hs, h.rv hs.isSlot]

end CapShapeUpd

/-! ## The spec's `invoke_untyped` without a reset -/

theorem invokeUntyped_noreset_eq (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (srcSl : Fl4Spec.CslotPtr)
    (base retypeBase : Fl4Spec.ObjRef) (t : Fl4Spec.ApiObjectType) (us : Nat) (slots : List Fl4Spec.CslotPtr)
    (dev : Bool) (σ σa σb σf : Fl4Spec.State Unit) (capS : Fl4Spec.Cap) (ptrs : List Fl4Spec.ObjRef)
    (hg : Fl4Spec.getCap (Z := Unit) srcSl σ = ({(capS, σ)}, False))
    (hs : Fl4Spec.setCap (Z := Unit) (.untypedCap dev base (Fl4Spec.bitsOf capS)
      (Fl4Spec.unat (retypeBase + (BitVec.ofNat 64 slots.length <<< bitsApi t us) - base))) srcSl σ =
        ({((), σa)}, False))
    (hr : Fl4Spec.retypeRegionWith (Z := Unit) bitsApi retypeBase slots.length us t dev σa = ({(ptrs, σb)}, False))
    (hi : t ≠ .archObject .pml4Obj)
    (hm : Fl4Spec.NonDet.mapMx (Fl4Spec.createCap (Z := Unit) t us srcSl dev) (slots.zip ptrs) σb =
      ({((), σf)}, False)) :
    (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype srcSl false base retypeBase t us slots dev)).run σ =
      ({(.ok (), σf)}, False) := by
  unfold Fl4Spec.invokeUntypedWith
  simp only [Fl4Spec.NonDetE.whenE, Bool.false_eq_true, ↓reduceIte, ndE_pure_bind]
  apply run_liftE'
  show (Fl4Spec.getCap srcSl >>= _) σ = _
  rw [nd_bind_single hg]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) _) >>= _) σ = _
  rw [nd_pure_bind]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) _) >>= _) σ = _
  rw [nd_pure_bind]
  show (Fl4Spec.setCap _ _ >>= _) σ = _
  rw [nd_bind_one hs]
  show (Fl4Spec.retypeRegionWith _ _ _ _ _ _ >>= _) σa = _
  rw [nd_bind_one hr]
  show (Fl4Spec.initArchObjects _ _ _ _ _ _ >>= _) σb = _
  rw [nd_bind_one (show Fl4Spec.initArchObjects (Z := Unit) t dev retypeBase slots.length us ptrs σb =
    ({((), σb)}, False) by simp [Fl4Spec.initArchObjects, Fl4Spec.NonDet.when, hi]; rfl)]
  exact hm

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `Slot::set_cap` on a slot of the typed heap: the slot's cap, the other
slots' caps, the link words, and every other word. -/
theorem set_cap_upd {th : TypedHeap} (hP : Placed th) (s : S) {a : U64} (ha : IsSlot th a) (c : capability.Cap)
    (he : EncWf c) :
    obj.Slot.set_cap st a s c ⦃ s' =>
      capV (L.mem s') a = c ∧ (∀ x, IsSlot th x → x ≠ a → capV (L.mem s') x = capV (L.mem s) x) ∧
      (∀ x, IsSlot th x → L.mem s' (wordOf x 16#u64) = L.mem s (wordOf x 16#u64) ∧
        L.mem s' (wordOf x 24#u64) = L.mem s (wordOf x 24#u64)) ∧
      (∀ w : U64, P1.Aligned w → w.val ≠ a.val → w.val ≠ a.val + 8 → L.mem s' w = L.mem s w) ⦄ := by
  apply WP.spec_mono (set_cap_spec a s c)
  rintro s' rfl
  obtain ⟨p, i, hi, rfl⟩ := ha
  have f := hi.fit hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := capAt_wr2_self (L := L) s (slotOf p i) c he (hi.al hP) (hi.al8 hP) (by rw [wa8_val (by omega)]; omega)
    rw [capAt_capV] at this; exact eq_of_ok_eq this
  · rintro x ⟨q, j, hj, rfl⟩ hne
    have := capAt_other_slot (L := L) hP s hi hj (fun ⟨e1, e2⟩ => hne (by rw [e1, e2])) ⟨(encodeF c).1⟩ ⟨(encodeF c).2⟩
    rw [capAt_capV, capAt_capV] at this; exact eq_of_ok_eq this
  · intro x hx
    have hs : IsSlot th (slotOf p i) := ⟨p, i, hi, rfl⟩
    show L.mem (wrCap (L := L) s (slotOf p i) c) _ = _ ∧ L.mem (wrCap (L := L) s (slotOf p i) c) _ = _
    rw [wrCap_eq]
    refine ⟨?_, ?_⟩ <;>
    rw [link_wr_cap hP hx hs (by simp) (Or.inr rfl), link_wr_cap hP hx hs (by simp) (Or.inl rfl)]
  · intro w hw h1 h2
    rw [mem_wr2 _ _ _ _ _ w (hi.al hP) (hi.al8 hP) hw, wa8_val (by omega)]
    simp only [show ¬ (slotOf p i).val + 8 = w.val from fun e => h2 e.symm,
      show ¬ (slotOf p i).val = w.val from fun e => h1 e.symm, ↓reduceIte]

end

theorem objTypeOf_nonarch {n : Nat} {t : Fl4Spec.ApiObjectType} (hn : n = 0 ∨ (2 ≤ n ∧ n ≤ 6))
    (ht : objTypeOf n = some t) (a : Fl4Spec.AObjectType) : t ≠ .archObject a := by
  intro e; subst e
  unfold objTypeOf at ht
  rcases hn with rfl | ⟨h1, h2⟩
  · simp at ht
  · interval_cases n <;> simp at ht

/-- Type numbers other than 8 are not PML4s. -/
theorem objTypeOf_ne_pml4 {n : Nat} {t : Fl4Spec.ApiObjectType} (hn : n ≠ 8)
    (ht : objTypeOf n = some t) : t ≠ .archObject .pml4Obj := by
  intro e; subst e
  unfold objTypeOf Fl4Spec.archDataToObjType at ht
  by_cases h14 : n < 14
  · interval_cases n <;> simp at ht <;> omega
  · simp [show ¬ n = 0 by omega, show ¬ n = 1 by omega, show ¬ n = 2 by omega, show ¬ n = 3 by omega,
      show ¬ n = 4 by omega, show ¬ n = 5 by omega, show ¬ n = 6 by omega, show ¬ n - 7 = 0 by omega,
      show ¬ n - 7 = 1 by omega, show ¬ n - 7 = 2 by omega, show ¬ n - 7 = 3 by omega, show ¬ n - 7 = 4 by omega,
      show ¬ n - 7 = 5 by omega, show ¬ n - 7 = 6 by omega] at ht
    split_ifs at ht <;> simp_all

/-! ## The untyped invariant -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]


/-- A device untyped cap retypes only into frames and untypeds: never TCBs,
CNodes or PML4s. -/
theorem dev_nt {n : Nat} {t : Fl4Spec.ApiObjectType} (ht : objTypeOf n = some t)
    (h : Fl4Spec.isFrameType t = true ∨ t = .untyped) : n ≠ 1 ∧ n ≠ 4 ∧ n ≠ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [objTypeOf, Fl4Spec.archDataToObjType] at ht
  · subst ht; simp [Fl4Spec.isFrameType] at h
  · subst ht; simp [Fl4Spec.isFrameType] at h
  · subst ht; simp [Fl4Spec.isFrameType, Fl4Spec.archIsFrameType] at h

theorem objTypeOf_cnode {n : Nat} (h : objTypeOf n = some .capTableObject) : n = 4 := by
  unfold objTypeOf at h; split_ifs at h <;> simp_all

theorem objTypeOf_tcb {n : Nat} (h : objTypeOf n = some .tcbObject) : n = 1 := by
  unfold objTypeOf at h; split_ifs at h <;> simp_all

/-- **`untyped::retype` without a reset refines `invoke_untyped`**, for the
types 0, 2..7 and 9..13 (object sizes `bitsApi`, which is `zOf` there: the spec's for
these types, FL4's for all). From the state `decode` checked (window empty,
enough memory, sizes) with the untyped cap's slot `srcSl` (a CNode slot), its
cap `Untyped p sb fi dev` aligned to its size, the untyped invariant, and the
free region free, and zero unless the cap is a device one (whose memory FL4
never zeroes; a device region makes no CNodes, `hdevT`, and the contents of
its frames and untypeds are not related): the spec's single outcome, related
to FL4's for the typed heap grown by the new CNodes. -/
theorem retype_full {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz47 : zOf nt.val us.val ≤ 47)
    (hsc : nt.val = 5 → 7 ≤ us.val) (hct0 : nt.val = 4 → us.val ≠ 0)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : dev = false → ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hdevT : dev = true → nt.val ≠ 4)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧ (dev = false → ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val)) ∧
        (FinInv th (L.mem s) σ G → FinInv th' (L.mem res.2.1) σ' G') ⦄ := by
  -- sizes and the region
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  set z := zOf nt.val us.val with hzdef
  have hz : z < 64 := by omega
  set k := 2 ^ z with hkdef
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  obtain ⟨hA1, hA2, hA3, hA4⟩ := retype_region p fi sb.val z win.val hsb hz hpal hpfit hfi hw1 hmem
  rw [← hkdef] at hA2 hA3 hA4
  set Ab := Fl4Spec.alignUp (p.bv + fi.bv) z with hAbdef
  set A := Ab.toNat with hAdef
  set aligned : U64 := ⟨Ab⟩ with halig
  have halv : aligned.val = A := rfl
  have hn14 : nt.val < 14 := by omega
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th src := hAs.isSlot
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hcv0 := capV_of_capAt hcap
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi dev hsb hpfit
  -- FL4: the cap update, then the loop
  obtain ⟨total, htot, hret⟩ := retype_noreset_eq (L := L) arI s ar src aligned nt us dest off win dev hn14 hus hz
    p sb fi dev hcap
  rw [hret]
  set nfi := core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p with hnfi
  set srcC' : capability.Cap := .Untyped p sb nfi dev with hsrcC'
  have he' : EncWf srcC' := by
    have : EncWf (capability.Cap.Untyped p sb fi dev) := by rw [capAt_words] at hcap; exact decode_encWf hcap
    exact ⟨this.1, this.2⟩
  obtain ⟨s1, hs1, hU1⟩ := spec_exists (set_cap_upd (L := L) hP s hs srcC' he')
  obtain ⟨s1', hs1', σa, hσa, hR1, hV1, hcdt1, hio1⟩ := spec_exists
    (retype_set_untyped_rel (L := L) th s σ hR hV hP hpp hidx hcap aligned total win z htot)
  rw [hs1] at hs1'; have e := eq_of_ok_eq hs1'; subst e
  rw [hs1]; simp only [bind_ok]
  obtain ⟨hcs1, hco1, hlk1, hfr1⟩ := hU1
  have hupd : CapShapeUpd th (L.mem s) (L.mem s1) src :=
    { links := hlk1, caps := hco1
      shp := by rw [hcs1, hcv0]; rfl
      bdg := by rw [hcs1, hcv0]; rfl
      nn := by rw [hcs1]; simp [srcC'] }
  have hM1 := hupd.mdbLinks hM hsrcm
  have hI1 := hupd.mdbInv hM hI
  have hC1 := hupd.cdtRel hC hcdt1 hio1
  -- the spec's pieces
  have hgs : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hwl : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hss : Fl4Spec.setCap (Z := Unit) (.untypedCap dev p.bv (Fl4Spec.bitsOf (.untypedCap dev p.bv sb.val fi.val))
      (Fl4Spec.unat (Ab + (BitVec.ofNat 64 (windowSlots dest r off.val win.val).length <<< bitsApi t us.val) - p.bv)))
      (pp.bv, idx) σ = ({((), σa)}, False) := by
    rw [hwl, hb]; exact hσa
  have hrr := retypeRegionWith_eq bitsApi Ab win.val us.val t dev σa
  rw [hb] at hrr
  rw [← hwl] at hrr
  -- the free region after the cap update
  have hzero1 : dev = false → ZeroRegion (L.mem s1) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro hd w hw h1 h2
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    have hne : w.val ≠ src.val ∧ w.val ≠ src.val + 8 := by
      rcases hfree q kq hq with h | h <;> constructor <;> omega
    rw [hfr1 w hw hne.1 hne.2]; exact hzero hd w hw h1 h2
  have hrf : RegionFree th A (A + win.val * k) := by
    intro q kd hq
    rcases hfree q kd hq with h | h
    · left; omega
    · right; omega
  have hnn : ∀ q kd, th q = some kd → 1 ≤ objSize kd → ¬ NewP A k win.val q :=
    fun q kd hq hs1 => not_newP hk1 hrf hq hs1
  have key : ∀ (th' : TypedHeap) (σb : Fl4Spec.State Unit), Placed th' → StateRel th' (L.mem s1) σb →
      SlotsValid th' (L.mem s1) → MdbLinks th' (L.mem s1) G → CdtRel th' (L.mem s1) σb G →
      Fl4Spec.retypeRegionWith (Z := Unit) bitsApi Ab (windowSlots dest r off.val win.val).length us.val t dev σa =
        ({(regionPtrs Ab (windowSlots dest r off.val win.val).length k, σb)}, False) →
      th' pp = some (.cnode rs) → th' dest = some (.cnode r) →
      (∀ i, i < win.val → CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * k)⟩ us dev)) →
      (∀ a, IsSlot th' a → a.val + 32 ≤ A + win.val * k ∨ p.val + 2 ^ sb.val ≤ a.val) →
      (FinInv th (L.mem s) σ G → KTyped th' σb) →
      (do
        let (s2, a2) ← objects.create_new_objects st arI s1 ar nt src dest off win aligned us dev
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv Ab t us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧ (dev = false → ZeroRegion (L.mem res.2.1) (A + win.val * k) (p.val + 2 ^ sb.val)) ∧
        (FinInv th (L.mem s) σ G → FinInv th' (L.mem res.2.1) σ' G') ⦄ := by
    intro th' σb hP' hR' hV' hM' hC' hrb hpp' hdest' hcv' hzs hKb
    -- the zero region kept by the loop: none for a device region
    set zl : Nat := if dev = true then p.val + 2 ^ sb.val else A + win.val * k with hzl
    have hzl1 : A + win.val * k ≤ zl := by rw [hzl]; split_ifs <;> omega
    have hzs' : ∀ a, IsSlot th' a → a.val + 32 ≤ zl ∨ p.val + 2 ^ sb.val ≤ a.val := fun a ha => by
      rcases hzs a ha with h | h
      · left; omega
      · right; exact h
    have hz0 : ZeroRegion (L.mem s1) zl (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      cases hd : dev
      · simp only [hzl, hd, Bool.false_eq_true, ↓reduceIte] at h1
        exact hzero1 hd w hw (by omega) h2
      · simp only [hzl, hd, ↓reduceIte] at h1; omega
    have hbA : (BitVec.ofNat 64 aligned.val : BitVec 64) = Ab := by
      rw [← bv_eq_ofNat]
    have hsrc1 : capAt (L.mem s1) src = ok srcC' := by rw [capAt_capV, hcs1]
    have hsrcd : ∀ j, j < win.val → src ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) := by
      intro j hj e
      have := hempty (off.val + j) (by omega) (by omega)
      rw [← e, hcap] at this; cases eq_of_ok_eq this
    -- the loop invariant at the start
    have hinv0 : LoopInv (L := L) th' (pp.bv, idx) srcC' σb
        (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
        ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val k))
        aligned.val k win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
        zl (p.val + 2 ^ sb.val) G (L.mem s1) (cjOf nt.val us dev aligned.val k) s1 0 := by
      refine ⟨σb, G, fun σf h => h, hR', hV', hM', hC', hI1, hsrc1, ?_, ?_, ?_,
        hz0, fun x hx => Or.inl hx, fun x hx => hx,
        fun j hj => absurd hj (by omega), fun x _ => rfl, fun y x => ⟨Or.inl, by
          rintro (h | ⟨j, hj, -⟩)
          · exact h
          · omega⟩, fun h => h, fun ch hch => ⟨ch, hch, fun z hz => hz⟩, fun x _ => rfl⟩
      · intro j _ hj
        have hj' : off.val + j < 2 ^ r := by omega
        have hd : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
          ⟨dest, off.val + j, Or.inl ⟨r, hdest, hj'⟩, rfl⟩
        have hnull := hempty (off.val + j) (by omega) (by omega)
        have hne : slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) ≠ src := by
          intro e; rw [e, hcap] at hnull; cases eq_of_ok_eq hnull
        rw [capAt_capV, hco1 _ hd hne, ← capAt_capV]; exact hnull
      · intro x hx hp
        have hxs : IsSlot th x := ((hM.members x).1 hx).1
        by_cases hxa : x = src
        · subst hxa
          rw [hcs1]
          refine ⟨?_, Or.inr ⟨rfl, ⟨le_refl _, le_refl _⟩⟩⟩
          obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
          rw [e1, e2, hsb', hst']; have := Nat.one_le_two_pow (n := sb.val); omega
        · rw [hco1 x hxs hxa] at hp ⊢
          refine ⟨hU.reg x hx hp, ?_⟩
          rcases hU.noov src hsrcm p sb fi dev hcv0 x hx hp with h | ⟨hu, hw⟩
          · left; unfold DisjR at h ⊢; simp only [Nat.zero_mul, Nat.add_zero]; omega
          · right; refine ⟨hu, ?_⟩
            obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
            unfold Within at hw ⊢; rw [hcv0] at hw; rw [e1, e2]; exact hw
      · intro y hy
        obtain ⟨hp1, hp2, hp3⟩ := hU.inc src hsrcm p sb fi dev hcv0 y hy
        have hym := (desc_mem hM hy).1
        have hys : IsSlot th y := ((hM.members y).1 hym).1
        have hya : y ≠ src := by
          intro e; subst e
          rw [hcv0, hst'] at hp3
          have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
            rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
            simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
            have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
            rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
              rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
            omega
          rw [this, Nat.shiftRight_eq_div_pow, show 2 ^ sb.val - fi.val = 0 by omega] at hmem
          simp at hmem; omega
        rw [hco1 y hys hya]
        unfold DisjR; left; simp only [Nat.zero_mul, Nat.add_zero]; omega
    obtain ⟨⟨s2, a2⟩, hres, ha2, hfin⟩ := spec_exists (create_loop_rel (L := L) arI ar th' hP' hpp' hidx hsb hpfit σb
      hdest' (by omega) nt us dev t ht hn hus hz hsc off win aligned hwin
      (by simp only [← hzdef, ← hkdef, halv]; omega) (by simp only [halv]; omega) (by simp only [halv]; omega)
      (by simp only [← hzdef, ← hkdef, halv]; omega) hcv' zl (p.val + 2 ^ sb.val) hzs' G (L.mem s1)
      hsrcd s1 hinv0)
    rw [hres]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    simp only at ha2 hfin
    obtain ⟨σf, Gf, hchain, hRf, hVf, hMf, hCf, hIf, -, -, -, -, hZf, hT1, hT1b, hT2a, hT2b, hT3, hFf, hChf, hRvf⟩ := hfin
    have hdrop : ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val k)).drop
        win.val = [] := by
      apply List.drop_of_length_le; simp [windowSlots, regionPtrs]
    rw [hdrop] at hchain
    have hmx := hchain σf (mapMx_nil _ _)
    refine ⟨rfl, ha2, σf, Gf, th', ?_, hP', hRf, hVf, hMf, hCf, hIf, ?_, fun hd => by
      have e : zl = A + win.val * k := by rw [hzl, hd]; simp
      rw [← e]; exact hZf, fun hFI => ⟨(hKb hFI).sub (ksub_of_eq (nks_mapMx (nks_createCap _ _ _ _) _) hmx),
        hFf (hFI.fm.recap hM.tree.nodup src
          (by rw [hcs1, hcv0]; exact CapSim.of_shape rfl rfl)
          (fun z hz hzs => hco1 z ((hM.members z).1 hz).1 hzs))⟩⟩
    · rw [hbA] at hmx
      apply invokeUntyped_noreset_eq bitsApi (pp.bv, idx) p.bv Ab t us.val _ dev σ σa σb σf _ _ hgs hss hrb
      · exact objTypeOf_ne_pml4 (by omega) ht
      · rw [hwl]; exact hmx
    · -- the untyped invariant
      have hfiL : fi.val < 2 ^ sb.val := by
        have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
          rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
          simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
          have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
          rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
            rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
          omega
        rw [this, Nat.shiftRight_eq_div_pow] at hmem
        by_contra hc
        rw [show 2 ^ sb.val - fi.val = 0 by omega] at hmem; simp at hmem; omega
      have hnfiv : nfi.val = A + win.val * k - p.val := by
        rw [← hA4]
        show (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p).bv.toNat = _
        rw [core.num.U64.wrapping_sub_bv_eq, core.num.U64.wrapping_add_bv_eq, htot, ← bv_eq_ofNat]
      have hzv : zOf nt.val us.val < 64 := by omega
      have hkk : 2 ^ zOf nt.val us.val = k := rfl
      suffices hRD : RetypeDelta th (L.mem s) (L.mem s1) (L.mem s2) G Gf src p sb fi nfi dev A k win.val
          (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) (cjOf nt.val us dev aligned.val k) by
        exact ⟨hRD.utinv hU, MdbStep.retype hRD hI hChf
          (fun z hz => by rw [hRvf z hz, hupd.rv ((hM.members z).1 hz).1])
          (cjOf_vplaced rfl hA2 (by omega) (by omega))⟩
      refine ⟨hM, hsrcm, hcv0, hcs1, fun x hx hxs => hco1 x ((hM.members x).1 hx).1 hxs, hfiL, hA1,
        by omega, by omega, by omega, fun j _ => physF_newCap _ _ _ _, fun j hj => ?_, fun j hj => ?_,
        fun j hj hu => ?_, fun j hj hm => ?_, fun j l hj hl he => ?_, hT1, hT1b, hT2a, hT2b, hT3⟩
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨c1, -⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c1]; show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨-, c2⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c2, hkk]; show (BitVec.ofNat 64 (A + j * k)).toNat + _ - 1 = _; simp; omega
      · unfold cjOf at hu ⊢
        rw [halv] at hu ⊢
        obtain ⟨hn0, he⟩ := isUt_newCap hu
        refine ⟨us, dev, he, ?_⟩
        show 2 ^ us.val = 2 ^ zOf nt.val us.val
        simp [zOf, hn0]
      · obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 hm
        rw [hempty (off.val + j) (by omega) (by omega)] at h0
        exact hn0 (eq_of_ok_eq h0).symm
      · have hj' : IsSlotAt th dest (off.val + j) := Or.inl ⟨r, hdest, by omega⟩
        have hl' : IsSlotAt th dest (off.val + l) := Or.inl ⟨r, hdest, by omega⟩
        by_contra hne
        rcases hj'.apart hP hl' (fun ⟨_, h2⟩ => hne (by omega)) with h | h <;>
          (change slotOf dest (off.val + j) = slotOf dest (off.val + l) at he; rw [he] at h; omega)

  have hzeroA : dev = false → ZeroRegion (L.mem s1) A (A + win.val * k) := fun hd w hw h1 h2 =>
    hzero1 hd w hw (by omega) (by omega)
  have hzsOld : ∀ a, IsSlot th a → a.val + 32 ≤ A + win.val * k ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hfitA : A + win.val * k ≤ 2 ^ 64 := by omega
  have hio1' : ∀ sl, σa.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  have hKa : FinInv th (L.mem s) σ G → KTyped th σa := fun hFI => hFI.kt.sub (ksub_of_eq (nks_setCap _ _) hσa)
  by_cases h4 : nt.val = 4
  · -- CNodes: the typed heap grows
    have hdf : dev = false := by
      cases hd : dev
      · rfl
      · exact absurd h4 (hdevT hd)
    replace hzeroA := hzeroA hdf
    have ht4 : t = .capTableObject := by rw [h4] at ht; simpa [objTypeOf] using ht.symm
    subst ht4
    have hk32 : k = 32 * 2 ^ us.val := by
      rw [hkdef, hzdef]; simp [zOf, h4]; rw [Nat.pow_add]
    have hal : A % 32 = 0 := by
      have h32 : 32 ∣ k := by rw [hk32]; exact Nat.dvd_mul_right _ _
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h32 (Nat.dvd_of_mod_eq_zero hA2))
    have hkz : 2 ^ z = 32 * 2 ^ us.val := by rw [← hkdef]; exact hk32
    rw [hk32] at hfitA hrf hzeroA
    obtain ⟨hP', hR', hV', hM', hC'⟩ := extend_cnode_rel th (L.mem s1) σa G hR1 hV1 hP hM1 hC1 hio1' Ab A win.val
      us.val rfl hfitA (by omega) hal hrf hzeroA
    refine key _ _ hP' hR' hV' hM' hC' ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hrr]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, hkz, hwl]
      rw [show k = 32 * 2 ^ us.val from hk32]; rfl
    · rw [extendTh_of_old (by omega) hrf hpp (objSize_pos_cnode _)]; exact hpp
    · rw [extendTh_of_old (by omega) hrf hdest (objSize_pos_cnode _)]; exact hdest
    · intro i hi
      simp only [newCapOf, h4, show ¬ (4 : Nat) = 2 by decide, show ¬ (4 : Nat) = 3 by decide, ↓reduceIte, CapValid]
      refine ⟨extendTh_new ⟨i, hi, ?_⟩, hct0 h4⟩
      rw [← hk32]; show (BitVec.ofNat 64 (A + i * k)).toNat = _
      have : i * k < win.val * k := Nat.mul_lt_mul_of_pos_right hi (by omega)
      simp; omega
    · rintro a ⟨q, j, hj, rfl⟩
      rcases hj.of_extend with hj | ⟨⟨i, hi, hqi⟩, hjl⟩
      · exact hzsOld _ ⟨q, j, hj, rfl⟩
      · left
        have hv : (slotOf q j).val = q.val + 32 * j := slotOf_val (by
          have h1 : (i + 1) * (32 * 2 ^ us.val) ≤ win.val * (32 * 2 ^ us.val) := Nat.mul_le_mul_right _ hi
          rw [Nat.add_mul, Nat.one_mul] at h1; omega)
        have h1 : (i + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hi
        rw [Nat.add_mul, Nat.one_mul] at h1
        rw [hv]; rw [hk32] at h1 ⊢; omega
    · intro hFI
      refine ktyped_region (hKa hFI) Ab A win.val (32 * 2 ^ us.val) rfl (by have := Nat.one_le_two_pow (n := us.val); omega)
        hfitA hrf (fun q kd hq hs => extendTh_of_old (by have := Nat.one_le_two_pow (n := us.val); omega) hrf hq hs) _
        (fun q hq => ⟨?_, fun t ht => by cases ht⟩)
      rintro r cs he -
      cases he; exact extendTh_new hq
  · -- other objects: the typed heap stays
    have hcvo : ∀ i, i < win.val → CapValid th (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * k)⟩ us dev) := by
      intro i hi
      have hlt : A + i * k < 2 ^ 64 := by
        have : (i + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hi
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      have hv : (⟨BitVec.ofNat 64 (A + i * k)⟩ : U64).val = A + i * k := by
        show (BitVec.ofNat 64 (A + i * k)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      have hfr : ∀ m, 2 ^ m ∣ k → (A + i * k) % 2 ^ m = 0 := by
        intro m hm
        apply Nat.mod_eq_zero_of_dvd
        exact Nat.dvd_add (Nat.dvd_trans hm (Nat.dvd_of_mod_eq_zero hA2)) (Nat.dvd_trans hm (Nat.dvd_mul_left _ _))
      apply newCapOf_ind (CapValid th) <;> intros <;> first | trivial | omega |
        (rename_i hn; simp only [CapValid, frameBitsN]; rw [hv]
         exact hfr _ (by rw [hkdef]; exact Nat.pow_dvd_pow 2 (by rw [hzdef]; simp [zOf, hn])))
    by_cases hu : t = .untyped
    · subst hu
      refine key th σa hP hR1 hV1 hM1 hC1 ?_ hpp hdest hcvo hzsOld hKa
      rw [hrr]; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; rfl
    · obtain ⟨hR', hC'⟩ := extend_other_rel th (L.mem s1) σa G hR1 hC1 Ab A win.val k rfl hk1 hfitA hrf
        (Fl4Spec.defaultObject t dev us.val σa.curDomain)
      refine key th _ hP hR' hV1 hM1 hC' ?_ hpp hdest hcvo hzsOld ?_
      · rw [hrr]; simp only [ne_eq, hu, not_false_eq_true, ↓reduceIte, hwl]; rfl
      · intro hFI
        refine ktyped_region (hKa hFI) Ab A win.val k rfl hk1 hfitA hrf (fun _ _ _ _ => rfl) _ (fun q _ => ⟨?_, ?_⟩)
        · intro r cs he _
          cases t <;> first | exact absurd rfl hu | exact absurd (objTypeOf_cnode ht) h4 |
            simp [Fl4Spec.defaultObject] at he
        · intro t' he
          cases t <;> first | exact absurd rfl hu | (have := objTypeOf_tcb ht; omega) |
            simp [Fl4Spec.defaultObject] at he

end

/-! ## A reset of an unused untyped cap does nothing -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem retype_reset_unused {A' : Type} (arI : machine.Arch A') (s : S) (ar : A') (slot base nt us dest off win : U64)
    (dev : Bool) {p sb : U64} {d : Bool} (hcap : capAt (L.mem s) slot = ok (.Untyped p sb 0#u64 d)) :
    untyped.retype st arI s ar slot true base nt us dest off win dev =
      untyped.retype st arI s ar slot false base nt us dest off win dev := by
  unfold untyped.retype
  simp only [↓reduceIte, Bool.false_eq_true]
  unfold untyped.reset_untyped
  simp only [slot_cap_eq, hcap, bind_ok, untyped.as_untyped, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
    uncurry_apply_pair]

end

theorem invokeUntyped_reset_unused (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (srcSl : Fl4Spec.CslotPtr)
    (base retypeBase : Fl4Spec.ObjRef) (t : Fl4Spec.ApiObjectType) (us : Nat) (slots : List Fl4Spec.CslotPtr)
    (dev : Bool) (σ : Fl4Spec.State Unit) {d : Bool} {p : Fl4Spec.ObjRef} {sb : Nat}
    (hg : Fl4Spec.getCap (Z := Unit) srcSl σ = ({(.untypedCap d p sb 0, σ)}, False)) :
    (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype srcSl true base retypeBase t us slots dev)).run σ =
      (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype srcSl false base retypeBase t us slots dev)).run σ := by
  unfold Fl4Spec.invokeUntypedWith
  simp only [Fl4Spec.NonDetE.whenE, ↓reduceIte, Bool.false_eq_true, ndE_pure_bind]
  apply run_bind_ok
  unfold Fl4Spec.resetUntypedCap
  rw [run_bind_ok (run_liftE hg)]
  simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, Fl4Spec.freeIndexOf, ↓reduceIte]
  rfl

end
end Fl4Proofs.P3
