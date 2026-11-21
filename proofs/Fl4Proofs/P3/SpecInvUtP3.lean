/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut8): **MakePool keeps
`P3 N`** (spec side only; imports SpecInvUtP2).

`perform_asid_control_invocation` (`makePool frame slot parent base`), from the
decode's facts `MpOKN` (the parent holds a childless RAM untyped of 4 KiB at
`frame`; the destination is a null slot reached through a CNode, `DestRefV`):

* `delete_objects frame 12`: by RegNull every slot inside the region is null, so
  the view keeps every non-null cap (`nv_sameNN`);
* the free-index write `max_free_index_update` (`nv_setUt`, the new free part is
  empty);
* `retype_region` of the pool at `frame` adds no cap;
* `cap_insert` of `AsidPoolCap frame base` from the parent (`hv_capInsertPool`):
  `should_be_parent_of` holds (the untyped is original, `same_region_as`), so
  the new cap is the parent's CDT child, and no cap covers `frame` (by UtCh the
  childless untyped's region is covered by no cap): `nv_cc`.

`UtInv'` along the chain is ut2's `makePool_utInv'` (with `detypeOK_of`):
**`p3_makePool`**.
-/
import Fl4Proofs.P3.SpecInvUtP2
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

theorem nv_congr {w w' : UView} (h1 : w'.2.1 = w.2.1) (h2 : w'.2.2.1 = w.2.2.1) (h : NV N w) : NV N w' :=
  nv_sameNN h2 (fun s c hs _ => by rw [h1] at hs; exact hs) (fun s c hs _ => by rw [h1]; exact hs) h

/-- No cap covers an address of a childless untyped's region (UtCh). -/
theorem clear_of_childless {w : UView} (hN : UtNV w) {u : CslotPtr} {d : Bool} {b : ObjRef} {n f : Nat}
    (hu : w.2.1 u = some (.untypedCap d b n f)) (hk : ∀ c, w.2.2.1 c ≠ some u) :
    ∀ s c r, w.2.1 s = some c → r ∈ capRng c → r ∉ delR b n :=
  fun s c r hs hr hrd => desc_noKids hk (hN.1 u d b n f hu s c r hs hr hrd)

theorem pb_eq : page_bits = 12 := rfl

/-- `same_region_as` of a 4 KiB untyped and the pool cap at its base. -/
theorem sameRegion_poolU {d : Bool} {frame : ObjRef} {f : Nat} {base : Asid}
    (hfit : frame.toNat + 2 ^ page_bits ≤ 2 ^ 64) :
    sameRegionAs (.untypedCap d frame page_bits f) (.archObjectCap (.asidPoolCap frame base)) := by
  obtain ⟨-, -, h3, -⟩ := sameRegionAs_self (d := d) (f := f) (show page_bits < 64 by decide) hfit
  exact ⟨rfl, BitVec.le_refl _, h3, BitVec.le_refl _⟩

/-- **The pool cap's `cap_insert` keeps `NV N`.** -/
theorem hv_capInsertPool {frame : ObjRef} {base : Asid} {parent slot : CslotPtr} {dev : Bool}
    (hfit : frame.toNat + 2 ^ page_bits ≤ 2 ^ 64) :
    HV (fun w => NV N w ∧ w.2.1 parent = some (.untypedCap dev frame page_bits (2 ^ page_bits)) ∧
        w.2.2.2 parent = true ∧ DestRefV w slot ∧ (∀ x, w.2.2.1 x ≠ some slot) ∧
        (∀ s c, w.2.1 s = some c → frame ∉ capRng c) ∧
        (∀ u d b n f, u ≠ parent → w.2.1 u = some (.untypedCap d b n f) → (frame ∈ delR b n ∨ frame.toNat ∈ utR b n) →
          parent ∈ descendantsOf u w.2.2.1 ∧ frame.toNat ∉ utFr b n f))
      (NV N) (capInsert (Z := Unit) (.archObjectCap (.asidPoolCap frame base)) parent slot) := by
  have hpd := mem_delR_iff (show page_bits < 64 by decide) hfit
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  obtain ⟨hN, hpar, horig, hDR, hk, hfr, hanc⟩ := hw
  rw [hpar] at hsc; cases hsc
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  subst hnull
  have hne : slot ≠ parent := fun e => by subst e; rw [hpar] at hoc; cases hoc
  unfold setUntypedCapAsFull
  rw [if_neg (fun h => by simp [isUntypedCap] at h)]
  refine hv_pure_bind ?_
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
  subst w2
  refine hv_pure_bind ?_
  refine hv_gets_bind (fun w => w.2.2.1 parent) (fun _ => rfl) fun w3 hw3 => ?_
  subst w3
  refine hv_gets_bind (fun w => w.2.2.1 slot) (fun _ => rfl) fun w4 hw4 => ?_
  subst w4
  refine hv_bind (hv_updateCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
  subst e
  have hfr0 : frame.toNat ∈ utR frame page_bits := ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  have hNc : NV N (vCC parent slot (.archObjectCap (.asidPoolCap frame base)) w) := by
    refine nv_cc hN hoc hDR hk hne hpar (fun _ _ _ _ e => (by cases e)) (fun _ _ _ e => (by cases e))
      (fun b hb => by cases hb) ?_ (fun r hr => by simp [sRefs] at hr) ?_ ?_ ?_
    · intro s c' r hs hr
      have : r = frame := by simpa [capRng, acRng, aobjRef] using hr
      rw [this]; exact hfr s c' hs
    · intro r hr
      have : r = frame := by simpa [capRng, acRng, aobjRef] using hr
      rw [this]; exact (hpd frame).2 hfr0
    · intro r hr hm
      have := hm.1; have := hm.2; omega
    · intro u d b n f hu hus r hr hrd
      have : r = frame := by simpa [capRng, acRng, aobjRef] using hr
      rw [this] at hrd ⊢; exact hanc u d b n f hu hus hrd
  split
  · exact nv_congr rfl rfl hNc
  · rename_i hsp
    exfalso
    exact hsp (decide_eq_true ⟨horig, sameRegion_poolU hfit, trivial⟩)

/-- **MakePool keeps `NV N`.** -/
theorem nv_makePool {σ : State Unit} (hP : P3 N σ) {frame : ObjRef} {slot parent : CslotPtr} {base : Asid}
    (hm : MpOKN (uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, NV N (uV y.2) := by
  obtain ⟨⟨dev, fi, hc, hk⟩, hdr, hsn⟩ := hm
  obtain ⟨⟨hI, hN⟩, hO⟩ := hP
  have hW := hI.1.2.1 parent dev frame page_bits fi hc
  have hfit : frame.toNat + 2 ^ page_bits ≤ 2 ^ 64 := fit_of_aligned (by decide) hW.2.1
  have hpd := mem_delR_iff (show page_bits < 64 by decide) hfit
  have hRN := regNull_of hN.1 hN.2.1 parent dev frame page_bits fi hc hk
  have hclr := clear_of_childless hN hc hk
  have hpout : parent.1 ∉ delR frame page_bits := fun h => by cases hRN parent _ hc h
  intro y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk', hcdt, horig, -⟩ := deleteObjects_kheap hz
  have hcapz : ∀ sl, capAt z.2 sl = if sl.1 ∈ delR frame page_bits then none else capAt σ sl := by
    intro sl; unfold capAt; rw [hk' sl.1]; split_ifs <;> rfl
  have hNz : NV N (uV z.2) := by
    refine nv_sameNN (w := uV σ) hcdt (fun s c hs hn => ?_) (fun s c hs hn => ?_) ⟨hN, hO⟩
    · have hs' : capAt z.2 s = some c := hs
      rw [hcapz] at hs'; split_ifs at hs'; exact hs'
    · show capAt z.2 s = some c
      rw [hcapz, if_neg]; · exact hs
      intro h; exact hn (hRN s c hs h)
  have hcz : capAt z.2 parent = some (.untypedCap dev frame page_bits fi) := by
    rw [hcapz, if_neg hpout]; exact hc
  -- getCap
  obtain ⟨x, hx, hy⟩ := hy
  obtain ⟨hxs, hxc⟩ := getCap_capAt hx
  obtain ⟨pcap, s1⟩ := x
  simp only at hxs hxc; subst hxs
  rw [hcz] at hxc; cases hxc
  -- the free-index write
  obtain ⟨z2, hz2, hy⟩ := hy
  have hv2 := hv_setCap _ _ (uV z.2) z.2 rfl z2 hz2
  have e2 : maxFreeIndexUpdate (.untypedCap dev frame page_bits fi) = .untypedCap dev frame page_bits (2 ^ page_bits) := rfl
  rw [e2] at hv2
  have hN2 : NV N (uV z2.2) := by
    rw [hv2]
    exact nv_setUt hNz hcz fun _ _ _ _ _ hm => by have := hm.1; have := hm.2; omega
  -- retype_region
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain ⟨-, h3⟩ := retypeRegionWith_out (bA := objBitsApi) hz3
  have hcap3 : capAt z3.2 = capAt z2.2 := by
    funext sl
    rcases h3 with e | ⟨-, e⟩
    · rw [e]
    · rw [e]
      unfold capAt retKh
      dsimp only
      split_ifs with hm
      · have hq : sl.1 = frame := by
          simp only [retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton, Nat.zero_mul] at hm
          rw [hm]; unfold ptrAdd; simp
        have hin : sl.1 ∈ delR frame page_bits := by rw [hq]; exact (hpd frame).2 ⟨le_refl _, by
          have := Nat.two_pow_pos page_bits; omega⟩
        have hsl : sl ≠ parent := fun e => hpout (e ▸ hin)
        have : capAt z2.2 sl = capAt z.2 sl := by
          show (uV z2.2).2.1 sl = _; rw [hv2, vCap_cap, if_neg hsl]; rfl
        have hnone : capAt z2.2 sl = none := by
          rw [this]; unfold capAt; rw [hk' sl.1, if_pos hin]
        unfold capAt at hnone; rw [hnone]
        simp [capView, defaultObject]
      · rfl
  have hcdt3 : z3.2.cdt = z2.2.cdt := by rcases h3 with e | ⟨-, e⟩ <;> rw [e]
  have horig3 : z3.2.isOriginalCap = z2.2.isOriginalCap := by rcases h3 with e | ⟨-, e⟩ <;> rw [e]
  have hv23 : (uV z3.2).2.1 = (uV z2.2).2.1 := hcap3
  have hN3 : NV N (uV z3.2) := nv_congr hv23 hcdt3 hN2
  have hcap3' : ∀ sl, (uV z3.2).2.1 sl = if sl = parent then some (.untypedCap dev frame page_bits (2 ^ page_bits))
      else if sl.1 ∈ delR frame page_bits then none else capAt σ sl := by
    intro sl; rw [hv23, hv2, vCap_cap]; split_ifs <;> first | rfl | (show capAt z.2 sl = _; rw [hcapz]; simp_all)
  have hcdt3' : (uV z3.2).2.2.1 = σ.cdt := by show z3.2.cdt = _; rw [hcdt3]; exact (congrArg (fun w : UView => w.2.2.1) hv2).trans hcdt
  -- cap_insert
  obtain ⟨z4, hz4, hy⟩ := hy
  have hpre : (fun w => NV N w ∧ w.2.1 parent = some (.untypedCap dev frame page_bits (2 ^ page_bits)) ∧
        w.2.2.2 parent = true ∧ DestRefV w slot ∧ (∀ x, w.2.2.1 x ≠ some slot) ∧
        (∀ s c, w.2.1 s = some c → frame ∉ capRng c) ∧
        (∀ u d b n f, u ≠ parent → w.2.1 u = some (.untypedCap d b n f) → (frame ∈ delR b n ∨ frame.toNat ∈ utR b n) →
          parent ∈ descendantsOf u w.2.2.1 ∧ frame.toNat ∉ utFr b n f)) (uV z3.2) := by
    have hold : ∀ s c, (uV z3.2).2.1 s = some c → s ≠ parent → capAt σ s = some c := by
      intro s c hs hsp; rw [hcap3', if_neg hsp] at hs; split_ifs at hs; exact hs
    have hfr0 : frame.toNat ∈ utR frame page_bits := ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
    refine ⟨hN3, by rw [hcap3', if_pos rfl], ?_, ?_, ?_, ?_, ?_⟩
    · show z3.2.isOriginalCap parent = true
      rw [horig3, show z2.2.isOriginalCap = z.2.isOriginalCap from congrArg (fun w : UView => w.2.2.2) hv2, horig]
      exact hI.1.2.2.2.2 parent dev frame page_bits fi hc
    · obtain ⟨s1, c1, hs1, hr1, hz1, hsh1⟩ := hdr
      have hs1p : s1 ≠ parent := fun e => by subst e; rw [hc] at hs1; cases hs1; simp [sRefs] at hr1
      refine ⟨s1, c1, ?_, hr1, hz1, hsh1⟩
      rw [hcap3', if_neg hs1p, if_neg]; · exact hs1
      intro h; exact sRefs_nn hr1 (hRN s1 c1 hs1 h)
    · intro x hx; rw [hcdt3'] at hx
      obtain ⟨c', hc', hcn⟩ := hI.2.1 x slot hx
      have hc'' : capAt σ slot = some c' := hc'
      rw [show capAt σ slot = some .nullCap from hsn] at hc''; cases hc''; exact hcn rfl
    · intro s c hs hr
      by_cases hsp : s = parent
      · subst hsp; rw [hcap3', if_pos rfl] at hs; cases hs; rw [capRng_ut] at hr; exact hr
      · exact hclr s c frame (hold s c hs hsp) hr ((hpd frame).2 hfr0)
    · intro u d b n f hu hus hrd
      have hus' := hold u _ hus hu
      obtain ⟨hn', hfit'⟩ := UtWf.fit (σ := σ) hI.1.2.1 hus'
      have hrd' : frame.toNat ∈ utR b n := by
        rcases hrd with h | h
        · exact (mem_delR_iff hn' hfit' frame).1 h
        · exact h
      rw [hcdt3']
      rcases hI.1.2.2.2.1 parent u dev frame page_bits fi d b n f (Ne.symm hu) hc hus' ⟨_, hfr0, hrd'⟩ with
        ⟨hd, -⟩ | ⟨hd, hr⟩
      · exact absurd hd (desc_noKids hk)
      · exact ⟨hd, hr _ hfr0⟩
  have hN4 : NV N (uV z4.2) := hv_capInsertPool hfit z3.2 hpre z4 hz4
  exact (ik_of_uk (P := fun s => NV N (uV s)) (fun _ _ e h => by rw [e]; exact h) (fun _ => by uk_auto)) z4.2 hN4 y hy

/-- **MakePool keeps `P3 N`.** -/
theorem p3_makePool {σ : State Unit} (hP : P3 N σ) {a : AsidControlInvocation} (hm : MpOKN (uV σ) a) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, P3 N y.2 := by
  intro y hy
  cases a with
  | makePool frame slot parent base =>
    have hU := makePool_utInv' hP.1.1 (detypeOK_of hP.1) (mpOK_of_V (a := .makePool frame slot parent base) hm.1) y hy
    obtain ⟨h1, h2⟩ := nv_makePool hP hm y hy
    exact ⟨⟨hU, h1⟩, h2⟩

end

end Fl4Proofs.P3.SInvU
