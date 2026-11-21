/-
P3 (DESIGN.md §9), VSpace: **the CSpace relations, `MdbInv` and `FinInv`
across a VSpace invocation** with the footprint of VsFoot (`Recap.carry`):
the invoked slot's cap replaced by one alike for the MDB (`MdbLike`: the
same shape, object key and badge, as a remapped frame or table cap), every
other slot and every link kept, and the spec's CDT and original bits kept
with its CNodes and TCBs (`KFoot`).
-/
import Fl4Proofs.P3.VsFoot
import Fl4Proofs.P3.FinSpec
import Fl4Proofs.P3.DelOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

theorem MdbLike.refl (c : capability.Cap) : MdbLike c c := ⟨rfl, rfl, rfl, rfl⟩

theorem shape_kind {c' c : capability.Cap} (h : shape c' = shape c) :
    isBadged c' = isBadged c ∧ isUt c' = isUt c ∧ isZb c' = isZb c ∧ isFrame c' = isFrame c ∧
      (c' = .Null ↔ c = .Null) := by
  cases c' <;> cases c <;> simp_all [shape, isBadged, isUt, isZb, isFrame]

theorem MdbLike.srl {c' c : capability.Cap} (h : MdbLike c' c) (b : capability.Cap) : srB c' b = srB c b := by
  rw [srB_shape, h.1, ← srB_shape]

theorem MdbLike.srr {c' c : capability.Cap} (h : MdbLike c' c) (b : capability.Cap) : srB b c' = srB b c := by
  rw [srB_shape, h.1, ← srB_shape]

theorem MdbLike.capSim {c' c : capability.Cap} (h : MdbLike c' c) : CapSim c' c :=
  ⟨h.2.1, refs_of_shape h.1, (shape_kind h.1).2.2.1, (shape_kind h.1).2.2.2.1, h.srl, h.srr⟩

theorem MdbLike.isPF {a' a b' b : capability.Cap} (ha : MdbLike a' a) (hb : MdbLike b' b) (r f : Bool) :
    isPF r a' b' f = isPF r a b f := by
  unfold Fl4Proofs.P3.isPF
  rw [ha.srl, hb.srr, (shape_kind ha.1).1, ha.2.2.1, hb.2.2.1]

theorem KFoot.ksub {σ σ' : Fl4Spec.State Unit} (h : KFoot σ σ') : KSub σ σ' := by
  intro o
  by_cases e : σ'.kheap o = σ.kheap o
  · exact ⟨fun r cs hc hw => ⟨cs, e ▸ hc, hw⟩, fun t ht => ⟨t, e ▸ ht⟩, fun hn => e ▸ hn⟩
  · rcases h.2.2.1 o e with ⟨ao, ao', h1, h2⟩ | ⟨r, cs, cs', h1, hw, h2⟩ | ⟨t, t', h1, h2⟩
    · refine ⟨fun r cs hc _ => ?_, fun t ht => ?_, fun hn => ?_⟩ <;> simp_all
    · refine ⟨fun r' cs'' hc _ => ?_, fun t ht => ?_, fun hn => ?_⟩
      · rw [h2] at hc; cases hc; exact ⟨cs, h1, hw⟩
      · simp_all
      · simp_all
    · refine ⟨fun r cs hc _ => ?_, fun t'' ht => ⟨t, h1⟩, fun hn => ?_⟩ <;> simp_all


/-- An object a cap names is at its pointer, and the cap is physical, not untyped. -/
theorem objRef_ptr {c : capability.Cap} {q : Fl4Spec.ObjRef} (h : q ∈ Fl4Spec.objRefs (absCap c)) :
    (ptrF c).bv = q ∧ physF c = true ∧ isUt c = false := by
  cases c <;> simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef] at h <;>
    (refine ⟨?_, physF_of rfl, rfl⟩; rw [ptrF_of rfl]; first | exact h.symm | (split at h <;> simp_all))

/-- A cap overlapping an ASID pool cap names its object. -/
theorem ovl_pool_ref {q b : U64} {c : capability.Cap} (h : Ovl (absCap (.AsidPool q b)) (absCap c)) :
    q.bv ∈ Fl4Spec.objRefs (absCap c) := by
  unfold Ovl at h
  obtain ⟨g, hg1, hg2⟩ := Set.nonempty_iff_ne_empty.2 h
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef, Fl4Spec.capIrqs, Fl4Spec.archCapSetMap,
    Fl4Spec.archGenObjRefs, Fl4Spec.capIrqOpt] at hg1
  subst hg1
  simp only [Fl4Spec.genObjRefs, Set.mem_union, Set.mem_image] at hg2
  rcases hg2 with (⟨x, hx, e⟩ | ⟨x, -, e⟩) | ⟨x, -, e⟩
  · cases e; exact hx
  · cases e
  · cases e

/-- **An ASID pool cap at an untyped region overlaps no cap** that is
disjoint from the region or untyped. -/
theorem not_ovl_pool {q b : U64} {c : capability.Cap} (hr : physF c = true → baseF c ≤ topF c)
    (hno : physF c = true → Disj c (.AsidPool q b) ∨ isUt c = true)
    (hpr : baseF (.AsidPool q b) ≤ topF (.AsidPool q b)) : ¬ Ovl (absCap (.AsidPool q b)) (absCap c) := by
  intro hov
  obtain ⟨hp, hph, hut⟩ := objRef_ptr (ovl_pool_ref hov)
  have hpq : ptrF c = q := P1.eq_of_bv hp
  have hb1 : baseF c = q.val := by unfold baseF; rw [hpq]
  have hb2 : baseF (.AsidPool q b) = q.val := by unfold baseF; rw [ptrF_of rfl]
  have := hr hph
  rcases hno hph with h | h
  · unfold Disj at h; omega
  · rw [hut] at h; cases h

section
variable {th : TypedHeap}

set_option maxHeartbeats 1000000 in
/-- **The relations across a VSpace invocation** (see the module docstring). -/
theorem Recap.carry {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {x : U64}
    (hM : MdbLinks th m G) (hC : CdtRel th m σ G) (hI : MdbInv m G) (hFI : FinInv th m σ G)
    (hF : SlotFoot th m m' x) (hx : MdbLike (capV m' x) (capV m x)) (hK : KFoot σ σ') :
    MdbLinks th m' G ∧ CdtRel th m' σ' G ∧ MdbInv m' G ∧ FinInv th m' σ' G := by
  have hpv : ∀ y, IsSlot th y → prevOf m' y = prevOf m y := fun y hy => (hF y hy).1
  have hnx : ∀ y, IsSlot th y → nextOf m' y = nextOf m y := fun y hy => by
    unfold nextOf; rw [(hF y hy).2.1]
  have hrv : ∀ y, IsSlot th y → revOf m' y = revOf m y := fun y hy => by
    unfold revOf; rw [(hF y hy).2.1]
  have hfb : ∀ y, IsSlot th y → fbOf m' y = fbOf m y := fun y hy => by
    unfold fbOf; rw [(hF y hy).2.1]
  have hcv : ∀ y, IsSlot th y → y ≠ x → capV m' y = capV m y := fun y hy hne => by
    unfold capV; rw [((hF y hy).2.2 hne).1, ((hF y hy).2.2 hne).2]
  have hlk : ∀ y, IsSlot th y → MdbLike (capV m' y) (capV m y) := fun y hy => by
    by_cases e : y = x
    · subst e; exact hx
    · rw [hcv y hy e]; exact MdbLike.refl _
  have hsl : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hM' : MdbLinks th m' G := hM.recap (fun y hy => ⟨hpv y hy, hnx y hy⟩)
    (fun y hy => (shape_kind (hlk y hy).1).2.2.2.2)
  refine ⟨hM', ⟨fun sl hs => by rw [hK.1]; exact hC.cdt sl hs,
    fun sl q hq => hC.cdt_slot sl q (by rw [← hK.1]; exact hq),
    fun sl hs => by rw [hK.2.1, hC.orig sl hs, hrv _ hs.isSlot], hC.par_slot⟩, ?_, ?_⟩
  · have hnx' : ∀ y ∈ G.chains.flatten, nextOf m y ≠ 0#u64 → nextOf m y ∈ G.chains.flatten := by
      intro y hy hn
      rcases hM.next_mem hy with h | ⟨h, -⟩
      · exact absurd h hn
      · exact h
    have hpm : ∀ a b, a ∈ G.chains.flatten → b ∈ G.chains.flatten → isPM m' a b = isPM m a b := by
      intro a b ha hb
      unfold isPM
      rw [hrv a (hsl a ha), hfb b (hsl b hb)]
      exact (hlk a (hsl a ha)).isPF (hlk b (hsl b hb)) _ _
    have hsr : ∀ a b, a ∈ G.chains.flatten → b ∈ G.chains.flatten → srM m' a b = srM m a b := by
      intro a b ha hb
      unfold srM; rw [(hlk a (hsl a ha)).srl, (hlk b (hsl b hb)).srr]
    refine ⟨fun c p h => ?_, fun a b h => ?_, fun y hy hn a ha hd => ?_, fun ch hch => ?_,
      fun y hy hn hb hs hbd hb0 => ?_, fun a ha hu => ?_, fun a ha hz => ?_⟩
    · rw [hrv p (hsl p (hM.tree.par_mem _ _ h).2)]; exact hI.orig c p h
    · obtain ⟨h1, h2⟩ := desc_mem hM h
      rw [hpm a b h2 h1]; exact hI.desc a b h
    · have hy' := hsl y hy
      rw [hnx y hy'] at hn hd ⊢
      have ha' : a ∈ G.chains.flatten := by rcases ha with rfl | ha; exact hy; exact (desc_mem hM ha).2
      rw [hpm a _ ha' (hnx' y hy hn)]; exact hI.after y hy hn a ha hd
    · refine Mdb.chunkL_congr (hI.chunk ch hch) (fun u hu v hv => srF_congr ?_ ?_ ?_)
      · exact hsr u v (List.mem_flatten.2 ⟨_, hch, hu⟩) (List.mem_flatten.2 ⟨_, hch, hv⟩)
      · exact (shape_kind (hlk u (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))).1).2.2.2.1
      · exact hrv u (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))
    · have hy' := hsl y hy
      rw [hnx y hy'] at hn hs hbd hb0 ⊢
      have hn' := hnx' y hy hn
      rw [(shape_kind (hlk y hy').1).1] at hb
      rw [(hlk y hy').2.2.1, (hlk _ (hsl _ hn')).2.2.1] at hbd
      rw [(hlk _ (hsl _ hn')).2.2.1] at hb0
      rw [hsr y _ hy hn'] at hs
      rw [hfb _ (hsl _ hn')]; exact hI.badges y hy hn hb hs hbd hb0
    · rw [(shape_kind (hlk a (hsl a ha)).1).2.1] at hu; rw [hrv a (hsl a ha)]; exact hI.utrev a ha hu
    · rw [(shape_kind (hlk a (hsl a ha)).1).2.2.1] at hz; rw [hsr a a ha ha]; exact hI.self a ha hz
  · exact ⟨hFI.kt.sub hK.ksub, hFI.fm.recap hM.tree.nodup x hx.capSim
      (fun z hz hne => hcv z (hsl z hz) hne)⟩

end

end

end Fl4Proofs.P3.Vs
