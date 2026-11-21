/-
P3 (DESIGN.md §9), untyped: **FL4's `reset_untyped` at `J`** (handoff utj.md
Round 12, item 3d, the reset part).

From a `JAtZ` state whose invoked CNode slot holds a childless used RAM
untyped cap `Untyped p sb fi false` (`fi ≠ 0`), FL4's `reset_untyped`
against l4v `reset_untyped_cap` exactly: the spec's `delete_objects` is
`delSt` (UtResetSpecJ), at which UtDropJ2's `JAtZ.drop` re-establishes
`JAtZ` at the dropped sets (same FL4 state); then either the small case
(`sb < 16`: FL4 clears the region, `JAtZ.zeroRg`, and writes the free index
0, `JAtZ.setFiJ`; spec `reset_smallX`) or the chunk loop
(UtResetLoopJ's `JAtZ.reset_loopJ` from offset `(fi - 1) / 2^16 * 2^16`,
spec `reset_initX`).

* `JAtZ.rgClear_drop`: the dropped sets are clear of the region (`RgClear`):
  the dropped heap by `RegionD`, the pruned VSpace sets by `FrMiss`, the kept
  IPC-buffer words by `KBOf`, the kernel-state block, nodes and ASID area by
  `UtKsApart` (`JCovD.ks`) of the source cap.
* `JAtZ.reset_untypedJ`: the composition, ending in `ResetJPost`.

Premises: those of `JAtZ.drop` (`KeptRefsP3`/`DbgTimerKept`, `ArchFitHyp`,
`VsReachMiss` [J]), `PPPlat` [P] (the preemption points), `PPR0` at the start
(as the deletion loop's `WJR`), one core (`Z.c = 0`, `JUtPath.core0` [P]).
No new named premise.
-/
import Fl4Proofs.P3.UtResetLoopJ
import Fl4Proofs.P3.UntypedResetRefine
import Fl4Proofs.P3.UtDropJ2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The dropped sets are clear of the region** (module docstring). -/
theorem JAtZ.rgClear_drop (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hsl : AbsSlot Z.th sl) {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false)) :
    RgClear ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) p sb := by
  obtain ⟨-, ⟨-, -, hML, -, -⟩, -⟩ := J.xtop.rel
  have hx : cslotAddr sl ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hsl.isSlot, _, hcap, by simp⟩
  obtain ⟨hks, hnd, has⟩ := J.jcov.ks (cslotAddr sl) hx p sb fi (capV_of_capAt hcap)
  refine ⟨fun r k hr => ?_, fun x hx => ?_, fun wp hw => hw.2.2, hks, fun c hc => hnd c hc, UtKsApart.asidOf has⟩
  · rw [P1.Heap.drop_eq_some] at hr
    obtain ⟨hnr, hr⟩ := hr
    unfold P1.RegionD P1.MeetsR at hnr
    rw [hr] at hnr
    simp only [Option.elim, not_not] at hnr
    omega
  · rcases hx with h | h | h | h | h
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2.1 with e | e <;> omega
    · rcases h.2 with e | e <;> omega

set_option maxHeartbeats 16000000 in
/-- **FL4's `reset_untyped` at `J`** (module docstring). -/
theorem JAtZ.reset_untypedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hc0 : Z.c = 0#u64) (hR0 : PPR0 σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx)) (hfi0 : fi.val ≠ 0)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s)
    (hAF : ArchFitHyp H σ)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1)
    (hXc : ∀ y, IsSlot Z.th y → ∀ k q, Vs.VNeed (capV (L.mem s) y) k q → q ∈ Vs.lvlSet XP X4 X3 X2 X1 k) :
    untyped.reset_untyped st arI s a (cslotAddr (pp.bv, idx)) ⦃ res =>
      ResetJPost (L := L) arI AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
        (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) σ (L.mem s) pp idx p sb res ⦄ := by
  set x := cslotAddr (pp.bv, idx) with hxdef
  set Z' := (Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s) with hZ'
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot Z.th x := hAs.isSlot
  obtain ⟨hP, ⟨hSR, -, hML, -, -⟩, -⟩ := J.xtop.rel
  have U := J.utc _ p sb fi false hAs hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfit := U.pfit
  have hxm : x ∈ Z.G.chains.flatten := (hML.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hcv : capV (L.mem s) x = .Untyped p sb fi false := capV_of_capAt hcap
  have hND : NotDev (L.mem s) x p sb fi := by unfold NotDev; rw [hcv]; simp
  have hxout := U.ns hnc x hxm
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    obtain ⟨q, j, hj, hq, he⟩ := hAs.at
    have : pp = q := bv_inj hq
    subst this
    exact hj.obj_out hP U.nostr (by rw [← he]; exact hxout)
  have hpp' : Z'.th pp = some (.cnode rs) := by
    show restrictTh Z.th _ _ pp = _; rw [restrictTh_out hppout]; exact hpp
  have hpb : pp.bv ∉ regionSet p.bv sb.val := by rw [regionSet_iff _ _ _ hsb hfit]; exact hppout
  obtain ⟨cs, hk, hwf, -⟩ := hSR.cnode pp rs hpp
  have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap false p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hSR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 U.sb4; simpa using this
  have hmod : ∀ d, d ∣ 2 ^ sb.val → p.val % d = 0 := by
    intro d hd; have := Nat.mod_mod_of_dvd p.val hd; rw [U.pal, Nat.zero_mod] at this; exact this.symm
  have hp8 : p.bv.toNat % 8 = 0 := hmod 8 (dvd_trans (by norm_num) h16)
  have hfib : fi.val ≤ 2 ^ sb.val := U.fiLe
  -- the spec's `delete_objects`
  obtain ⟨hSD, hcdt, horig, hrepr, hcdom, hdtime, hist, hinode, harch, hdl, hdsi, hum, hz⟩ :=
    delSt_facts p sb hsb hfit σ
  obtain ⟨⟨u, σD⟩, hyD⟩ := deleteObjects_has hp8 sb.val σ
  have hσD : σD = delSt p.bv sb.val σ := deleteObjects_delSt p sb hp8 (by have := U.sb4; omega) hsb hfit σ hyD
  subst hσD
  have J' := J.drop hres hAs hcap hnc hfi0 hKR hDT hAF hSD hcdt horig hrepr hcdom hdtime hist hinode harch hdl hdsi
    hum hXP hX4 hX3 hX2 hX1 hM hXc
  have hRC : RgClear Z' (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) p sb := J.rgClear_drop hAs hcap
  have hTh : restrictTh Z'.th p.val (p.val + 2 ^ sb.val) = Z'.th := restrictTh_idem _ _ _
  have hfr : RegionFree Z'.th p.val (p.val + 2 ^ sb.val) := RegionFree.restrict U.nostr
  have hRM : RgMiss p sb (delSt p.bv sb.val σ) := fun o ko ho => by
    by_cases hr : RgOf p sb o
    · rw [hSD.kin o hr] at ho; cases ho
    · rw [hSD.kout o hr] at ho; exact J.specOff hsb hfit hxm hcv hfib ho hr
  have hncD : ¬ ∃ y, (delSt p.bv sb.val σ).cdt y = some (pp.bv, idx) := by rw [hcdt]; exact hnc
  have hR0D : PPR0 (delSt p.bv sb.val σ) := by
    refine hR0.of_ppk ⟨hSD.cons, hSD.time, hSD.csc, fun u hu => by rw [hSD.rel] at hu; exact hu,
      fun q y n hq => ?_, fun q y hq => ?_, rfl, rfl, fun h => h, fun q x y hx hq hi => ?_, fun h => h⟩
    rotate_right
    · by_cases hr : RgOf p sb q
      · rw [hSD.kin q hr] at hq; cases hq
      · rw [hSD.kout q hr, hx] at hq; cases hq; exact Or.inl hi
    · by_cases hr : RgOf p sb q
      · rw [hSD.kin q hr] at hq; cases hq
      · rw [hSD.kout q hr] at hq; exact hq
    · by_cases hr : RgOf p sb q
      · rw [hSD.kin q hr] at hq; cases hq
      · rw [hSD.kout q hr] at hq; exact ⟨y, hq, rfl, id⟩
  have hc0' : Z'.c = 0#u64 := hc0
  have hP' : Placed Z'.th := J'.xtop.rel.1
  have hAs' : AbsSlot Z'.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp')⟩
  have hxs' : IsSlot Z'.th x := hAs'.isSlot
  have hobj : ∀ y, IsSlot Z'.th y → y.val + 32 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hP' hy
    rcases hfr q kq hq with e | e <;> omega
  have hZf : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val) := U.zero hND
  -- FL4
  unfold untyped.reset_untyped
  rw [slot_cap_eq, hcap]
  have hfi0' : ¬ (fi = 0#u64) := fun e => hfi0 (by rw [e]; rfl)
  simp only [bind_ok, untyped.as_untyped, hfi0', ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hsm : sb < untyped.RESET_CHUNK_BITS
  · -- a small region: zero it, then the free index 0
    rw [if_pos hsm]
    have hsm' : sb.val < 16 := by rw [reset_chunk_bits_eq] at hsm; exact hsm
    have h63 : (sb &&& 63#u64).val = sb.val := by
      have : (sb &&& 63#u64).val = sb.val % 64 := by
        simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
      rw [this]; omega
    obtain ⟨i1, hi1, hv1, -⟩ := spec_exists (UScalar.ShiftLeft_spec (1#u64 : U64) (sb &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
    have hi1v : i1.val = 2 ^ sb.val := by
      rw [hv1, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
      exact Nat.pow_lt_pow_right (by decide) hsb
    simp only [lift, bind_ok, hi1, L.clear_free_eq]
    have hpal : P1.Aligned p := hp8
    have h8 : (2 : Nat) ^ sb.val % 8 = 0 := by obtain ⟨t, ht⟩ := h16; omega
    have J1 := J'.zeroRg hRC hc0' hfit hpal (n := i1) (by rw [hi1v]; exact h8) (le_refl _) (by rw [hi1v])
    set s1z := L.zr s p i1 with hs1z
    have hz1 : ∀ w : U64, P1.Aligned w → L.mem s1z w =
        if p.val ≤ w.val ∧ w.val < p.val + i1.val then 0#u64 else L.mem s w :=
      fun w hw => L.mem_zr s p _ w hpal (by rw [hi1v]; exact h8) (by rw [hi1v]; exact hfit) hw
    have hS1 : SlotsSame Z'.th (L.mem s) (L.mem s1z) :=
      slotsSame_out hP' (fun b hb => by have := hobj b hb; omega) (fun w hw ho => by
        rw [hz1 w hw, if_neg (by rw [hi1v]; omega)])
    have hcap1 : capAt (L.mem s1z) x = ok (.Untyped p sb fi false) := by rw [hS1.capAt hxs']; exact hcap
    have e0 : (0#u64 : U64).val = 0 := rfl
    have hZ1 : ZeroRegion (L.mem s1z) (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      rw [e0] at h1
      rw [hz1 w hw, if_pos (by rw [hi1v]; omega)]
    obtain ⟨s2, hs2, cs2, hk2, hwf2, J2, hcap2, hks2, -, hfr2⟩ := spec_exists
      (J1.setFiJ hpp' hidx hcap1 hncD hfi0 hTh hfr hRM 0#u64 (by rw [e0]; omega) hZ1)
    rw [← hxdef] at hs2 hcap2 hfr2
    rw [hs2]
    simp only [bind_ok]
    have hZ2 : ZeroRegion (L.mem s2) p.val (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      have := hobj x hxs'
      rw [hfr2 w hw (by omega) (by omega), hz1 w hw, if_pos (by rw [hi1v]; omega)]
    have hmem := reset_smallX hk hwf hidx hg hfi0 hp8 hpb hrcb rfl (by rw [hrcb]; exact hsm') hfit
      (by have := U.sb4; omega) hyD hz hk2 hwf2
    rw [e0] at J2
    refine (WP.spec_ok _).2 (Or.inl ⟨rfl, _, Ac, Lst, D, hmem, J2, hcap2, by rw [hks2, hs1z, L.ksb_zr], hZ2,
      hRM.setCn hk2 idx _, hncD, hR0D.setCn hk2 hwf2 hidx _, hz, fun y hy hne => by
        rw [capAt_frame2 hP' hxs' hy hne hfr2, hS1.capAt hy]⟩)
  · -- the chunked reset
    rw [if_neg hsm]
    have hsb16 : 16 ≤ sb.val := by rw [reset_chunk_bits_eq] at hsm; exact Nat.le_of_not_lt hsm
    have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
    obtain ⟨i, hi, hiv, -⟩ := spec_exists (U64.sub_spec (x := fi) (y := 1#u64)
      (by have : (1#u64 : U64).val = 1 := rfl; rw [this]; omega))
    obtain ⟨i1, hi1, hi1v, -⟩ := spec_exists (U64.sub_spec (x := untyped.RESET_CHUNK) (y := 1#u64)
      (by have : (1#u64 : U64).val = 1 := rfl; rw [this, hC]; omega))
    rw [hi, hi1]
    simp only [bind_ok, lift]
    have hi1v' : i1.val = 65535 := by rw [hi1v, hC]; rfl
    have hov : (i &&& ~~~i1).val = (fi.val - 1) / 65536 * 65536 := by
      rw [and_not_mask i i1 hi1v', hiv]; rfl
    have hdv : 65536 ∣ 2 ^ sb.val := by
      have := Nat.pow_dvd_pow 2 hsb16; simpa using this
    obtain ⟨t, ht⟩ := hdv
    have hq : (fi.val - 1) / 65536 < t := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    have hqa := Nat.lt_div_mul_add (a := fi.val - 1) (b := 65536) (by decide)
    have hK := reset_initX hk hwf hidx hg hfi0 hp8 hpb hrcb (by rw [hrcb]; simp; omega) hfib hyD
    rw [hrcb] at hK
    exact JAtZ.reset_loopJ hAK hA hnd hPP hrcb hpp' hidx hTh hfr hRC hc0' (hmod 65536 ⟨t, ht⟩) hfit σ (L.mem s) s a
      (i &&& ~~~i1) _ Ac Lst D fi (by rw [hov]; omega) (by rw [hov, ht]; nlinarith) J' hcap hfi0
      (fun w hw h1 h2 => hZf w hw (by rw [hov] at h1; omega) h2)
      (by rw [hov, Nat.mul_div_cancel _ (by decide)]; simpa using hK) hRM hncD hR0D rfl hz (fun _ _ _ => rfl)

end

/-! ## The spec's retype with a reset, split at the reset -/

section SpecSplit
open Fl4Spec

/-- **The spec's retype with a reset**, a done reset: the retype without one
from the reset's outcome. -/
theorem invoke_reset_ok (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType)
    (us : Nat) (slots : List CslotPtr) (dev : Bool) {σ σr : State Unit}
    (hr : ((.ok (), σr) : Except Unit Unit × State Unit) ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1)
    {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((invokeUntypedWith (Z := Unit) bitsApi (.retype sl false base rb t us slots dev)).run σr).1) :
    y ∈ ((invokeUntypedWith (Z := Unit) bitsApi (.retype sl true base rb t us slots dev)).run σ).1 := by
  unfold invokeUntypedWith at hy ⊢
  simp only [NonDetE.whenE, ↓reduceIte, Bool.false_eq_true, ndE_pure_bind] at hy ⊢
  exact memE_bind hr rfl hy

/-- **The spec's retype with a reset**, a preempted reset. -/
theorem invoke_reset_err (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType)
    (us : Nat) (slots : List CslotPtr) (dev : Bool) {σ σr : State Unit}
    (hr : ((.error (), σr) : Except Unit Unit × State Unit) ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1) :
    ((.error (), σr) : Except Unit Unit × State Unit) ∈
      ((invokeUntypedWith (Z := Unit) bitsApi (.retype sl true base rb t us slots dev)).run σ).1 := by
  unfold invokeUntypedWith
  simp only [NonDetE.whenE, ↓reduceIte]
  exact memE_bind_err hr rfl

end SpecSplit

end

end Fl4Proofs.P3
