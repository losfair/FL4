/-
P3 (DESIGN.md §9), TCB invocations, CSpace side: **ThreadControl's cap
installs** (FL4 `tcb::install_tcb_cap`, `tcb::thread_control_caps`) against
l4v `install_tcb_cap` (`cap_delete` of the TCB slot, then `check_cap_at`
twice and `cap_insert`).

First: `cdt::insert` into a TCB slot keeps `MdbInv` and `FinInv`
(`insert_full_abs_fin`); `same_object_as` is the spec's (`SoSpec`); the
delete of a TCB slot (`delete_full`, or nothing for an empty one).
-/
import Fl4Proofs.P3.DelCnode
import Fl4Proofs.P3.InsAbs
import Fl4Proofs.P3.SoSpec
import Fl4Proofs.P3.CnodeKey
import Fl4Proofs.P3.MdbStepVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a derived cap into any slot of the typed heap**
refines `cap_insert` and keeps `MdbInv` and `FinInv`. -/
theorem insert_full_abs_fin (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs))
    {idxs : List Bool} (hls : idxs.length = rs) {dsl : Fl4Spec.CslotPtr} (hAd : AbsSlot th dsl)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr dsl) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hsh : shape c = shape srcC) (hbd : badgeF c = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) (hzb : isZb srcC = false)
    (hkey : okey c = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 c) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr dsl) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) dsl σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ FinInv th (L.mem s') σ' G' ∧
        ((isUt srcC = true → c = srcC) → MdbStep (L.mem s) G (L.mem s') G') ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr dsl ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hcv0 := capV_of_capAt hsrcC
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hself : srB srcC srcC = true := by
    have := hI.self _ hsrcm (by rw [hcv0]; exact hzb); unfold srM at this; rw [hcv0] at this; exact this
  have hk := sameBadgeKind_of_shape hsh
  obtain ⟨hwf, rfl⟩ := hca
  have hb : decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)))) =
      isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) := by
    rw [hC.orig _ hAs]; exact sbp_eq srcC c _ hsh hself hes hk
  have hsib : ¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC))) →
      ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) := by
    intro hn
    have h0 : isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) = false := by
      rw [← hb]; simpa using hn
    rw [← hcv0] at h0 hsh hbd hzb
    exact MdbInv.sib (th := th) hI hsrcm hzb hsh hbd h0
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (insert_refines_abs th s σ G hR hV hP hM hC hps hls hAd hsrcC hsnn hdst c _ ⟨hwf, rfl⟩ hcv he hcnn hk)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (insert_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hsh hbd hut hzb)
  obtain ⟨s3, h3, hfin⟩ := spec_exists
    (insert_finM hP s G hM hFI.fm hsrcm hAd.isSlot hdestm hsrcC c he hsh hkey hzb)
  obtain ⟨s4, h4, hstep⟩ := spec_exists
    (insert_mstep hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hsh hbd hut hzb hkey hv)
  rw [h1] at h2 h3 h4
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  have e4 := eq_of_ok_eq h4
  subst e e3 e4
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hins, hR', hV', hM', hC', hG'⟩ := hpost hsib
  refine ⟨σ', G', hins, hR', hV', hM', hC', ?_, ⟨hFI.kt.sub (ksub_of_eq (capInsert_nks _ _ _) hins), ?_⟩, ?_⟩
  · rw [hG', hb]; exact hinv
  · have hnd := hM'.tree.nodup
    rw [hG', hb] at hnd ⊢; exact hfin _ hnd
  · rw [hG', hb]; exact hstep

end

/-! ## The pieces of `install_tcb_cap` -/

theorem soB_null_right (a : capability.Cap) : soB a .Null = false := by
  cases a <;> simp only [soB] <;> exact srB_of_eq (by simp [objects.same_region_as, objects.cap_is_physical])

theorem soB_ut_right (a : capability.Cap) (p sb fi : U64) (d : Bool) : soB a (.Untyped p sb fi d) = false := by
  cases a <;> simp only [soB] <;> exact srB_of_eq (by simp [objects.same_region_as, objects.cap_is_physical])

theorem soB_thread (t : U64) (b : capability.Cap) : soB (.Thread t) b = decide (b = .Thread t) := by
  simp only [soB]
  apply srB_of_eq
  cases b <;> simp [objects.same_region_as]
  split_ifs <;> simp_all [eq_comm]

/-- `fullF` is `none` unless both caps are untyped. -/
theorem fullF_none_of {a c : capability.Cap} (h : isUt c = false) : fullF a c = none := by
  cases a <;> cases c <;> simp_all [fullF, isUt]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem still_valid_eq (s : S) (t slot src : U64) (nc : capability.Cap) (hsrc : src ≠ 0#u64) :
    tcb.still_valid st s t slot nc src =
      ok (soB nc (capV (L.mem s) src) && soB (.Thread t) (capV (L.mem s) slot)) := by
  unfold tcb.still_valid
  simp only [is_null_eq, hsrc, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok,
    soB_eq]
  cases soB nc (capV (L.mem s) src) <;> simp

/-- The caps after `cdt::insert` with no `set_untyped_cap_as_full`: the new
cap at `dest`, every other slot's as it was. -/
theorem insert_caps_nofull {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hfull : fullF srcC c = none) :
    cdt.insert st s c src dest ⦃ s' => ∀ a, IsSlot th a →
      capV (L.mem s') a = if a = dest then c else capV (L.mem s) a ⦄ := by
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
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW a ha
  have := hW.capAt' ha he hes hsrcC
  rw [capAt_capV] at this
  by_cases h1 : a = dest
  · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
  · by_cases h2 : a = src
    · subst h2; simp only [h1, ↓reduceIte, hfull, Option.getD_none] at this ⊢
      rw [hcv]; simpa using this
    · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `cdt::delete` of an empty slot does nothing. -/
theorem delete_null_eq (s : S) (a : A) (slot : U64) (hc : capAt (L.mem s) slot = ok .Null)
    (σ : Fl4Spec.State Unit) :
    cdt.delete st arI s a slot true = ok (.Ok (), s, a) := by
  unfold cdt.delete
  simp only [↓reduceIte]
  rw [finalise_imm_triv arI σ s a _ .Null hc (Or.inl rfl)]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  rw [empty_slot_null arI s a _ hc]
  simp only [bind_ok, uncurry_apply_pair]

end

/-- The spec's `cap_delete` of an empty slot does nothing. -/
theorem capDelete_null {sl : Fl4Spec.CslotPtr} {σ : Fl4Spec.State Unit}
    (hg : Fl4Spec.getCap (Z := Unit) sl σ = ({(.nullCap, σ)}, False)) :
    (Fl4Spec.capDelete (Z := Unit) sl).run σ = ({(.ok (), σ)}, False) := by
  have he : Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ = ({((), σ)}, False) := by
    unfold Fl4Spec.emptySlot
    rw [nd_bind_single hg]; simp
  exact capDelete_triv _ σ σ hg (Or.inl rfl) he

/-- `check_cap_at`. -/
theorem checkCapAt_eq {c a : Fl4Spec.Cap} {sl : Fl4Spec.CslotPtr} {m : Fl4Spec.SMonad Unit Unit}
    {σ : Fl4Spec.State Unit} (hg : Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False)) :
    Fl4Spec.checkCapAt (Z := Unit) c sl m σ =
      (if Fl4Spec.sameObjectAs c a then m σ else ({((), σ)}, False)) := by
  unfold Fl4Spec.checkCapAt
  rw [nd_bind_single hg]
  unfold Fl4Spec.NonDet.when
  split_ifs <;> rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a non-null, non-zombie cap with no
`set_untyped_cap_as_full` keeps `DelInv`.** -/
theorem insert_delinv {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hD : DelInv th (L.mem s)) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hfull : fullF srcC c = none) (hcn : c ≠ .Null) (hzc : isZb c = false) :
    cdt.insert st s c src dest ⦃ s' => DelInv th (L.mem s') ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hNs : nextOf (L.mem s) src ≠ src := by
    rcases hnx with h | ⟨-, -, h⟩
    · rw [h]; exact (hs.ne_zero hP).symm
    · exact h
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  refine WP.spec_mono (WP.spec_and (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
    (insert_caps_nofull hP s G hM hsrc hd hdest hsrcC c he hfull)) ?_
  rintro s' ⟨hW, hcap⟩
  have hcz : ∀ y, IsSlot th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n → y ≠ dest ∧
      capV (L.mem s) y = .Zombie p zt n := by
    intro y hy p zt n h
    rw [hcap y hy] at h
    split_ifs at h with hyd
    · subst h; simp [isZb] at hzc
    · exact ⟨hyd, h⟩
  refine ⟨fun y hy p zt n h => hD.zwf y hy p zt n (hcz y hy p zt n h).2,
    fun y y' hy hy' hyy p zt n p' zt' n' h h' => hD.zu y y' hy hy' hyy p zt n p' zt' n'
      (hcz y hy p zt n h).2 (hcz y' hy' p' zt' n' h').2, fun y hy h => ?_⟩
  rw [hcap y hy] at h
  split_ifs at h with hyd
  · exact absurd h hcn
  have hym : y ∉ G.chains.flatten := fun hm => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hm
    rw [capAt_capV, h] at h0; exact hn0 (by simpa using h0.symm)
  have hys : y ≠ src := fun e => hym (e ▸ hsrc)
  have hyn : ¬ (nextOf (L.mem s) src ≠ 0#u64 ∧ y = nextOf (L.mem s) src) := by
    rintro ⟨h0, rfl⟩
    rcases hM.next_mem hsrc with h1 | ⟨h1, -⟩
    · exact h0 h1
    · exact hym h1
  rw [hW.prevOf' hy hNs, hW.nextOf' hP hy hd hne hNc, if_neg hyd, if_neg hyn, if_neg hyd, if_neg hys]
  exact hD.nc y hy h

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem tcb_root_eq (t idx : U64) {n : Nat} (hn : n < tcbSlots) (hidx : idx.val = n) :
    slotAddr t.bv idx.bv = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := by
  have he : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) = slotOf t n := by
    show slotAddr t.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal n hn]
  rw [he]
  show slotAddr t.bv idx.bv = slotAddr t.bv (BitVec.ofNat 64 n)
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← hidx, Nat.mod_eq_of_lt (show idx.val < 2 ^ 64 by scalar_tac)]
  rfl

/-- **After the delete of the TCB slot**: FL4's checks and insert against
the spec's `check_cap_at` (the new cap against the source slot's cap, the
thread cap against the invoked slot's cap) and `cap_insert`. -/
theorem install_after (th : TypedHeap) (hP : Placed th) (s s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit)
    (G1 : MdbGhost) (hDS1 : DState (L := L) th s1 σ1 G1)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots)
    (hroot : capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hczs : ChgZ (L.mem s) (L.mem s1) (cslotAddr (ps.bv, idxs)))
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc) :
    (do
      let b ← nc.is_null
      if b = true then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)
        else do
          let b1 ← tcb.still_valid st s1 t (cslotAddr ssl) nc (cslotAddr (ps.bv, idxs))
          if b1 = true then do
              let s2 ← cdt.insert st s1 nc (cslotAddr (ps.bv, idxs)) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))
              ok (core.result.Result.Ok (), s2, a1)
            else ok (core.result.Result.Ok (), s1, a1)) ⦃ res =>
      ∃ σ' G', (Fl4Spec.NonDetE.unlessE (ε := Unit) (absCap nc = .nullCap) (Fl4Spec.NonDetE.liftE
          (Fl4Spec.checkCapAt (absCap nc) (ps.bv, idxs) (Fl4Spec.checkCapAt (.threadCap t.bv) ssl
            (Fl4Spec.capInsert (absCap nc) (ps.bv, idxs) (t.bv, Fl4Spec.tcbCnodeIndex n)))))).run σ1 =
            ({(.ok (), σ')}, False) ∧
        res.1 = .Ok () ∧ res.2.2 = a1 ∧ DState (L := L) th res.2.1 σ' G' ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
          capV (L.mem res.2.1) y = capV (L.mem s1) y) ∧ MdbStep (L.mem s1) G1 (L.mem res.2.1) G' ⦄ := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS1
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsr : cslotAddr (ps.bv, idxs) ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := by
    intro e
    have := cslotAddr_inj hP hAsrc hAt e
    have hpt : ps = t := (UScalar.eq_equiv_bv_eq ps t).2 (congrArg Prod.fst this)
    rw [hpt, ht] at hps; cases hps
  by_cases hnn : nc = .Null
  · subst hnn
    rw [cap_is_null_null]; simp only [bind_ok, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ?_, by trivial, by trivial, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩,
      by intros; trivial, MdbStep.refl hM⟩
    simp only [absCap, Fl4Spec.NonDetE.unlessE, ↓reduceIte]; rfl
  have hann : absCap nc ≠ .nullCap := fun h => hnn ((show CapRel nc (absCap nc) from ⟨hwf, rfl⟩).null_iff.1 h)
  rw [cap_is_null_ne hnn]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [still_valid_eq _ _ _ _ nc (hAsrc.isSlot.ne_zero hP)]
  simp only [bind_ok]
  obtain ⟨cs, asr, hcs, hcas, hgs⟩ := hR.abs_cap hAsrc
  obtain ⟨cl, al, hcl, hcal, hgl⟩ := hR.abs_cap hAs
  rw [capV_of_capAt hcs, capV_of_capAt hcl]
  have e1 : soB nc cs = true ↔ Fl4Spec.sameObjectAs (absCap nc) asr := by
    rw [hcas.abs]; exact soB_iff nc cs hwf hcas.1 hfw
  have e2 : soB (.Thread t) cl = true ↔ Fl4Spec.sameObjectAs (.threadCap t.bv) al := by
    rw [hcal.abs]; exact soB_iff (.Thread t) cl trivial hcal.1 (by simp [isFrame])
  have hun : ∀ m : Fl4Spec.SMonad Unit Unit,
      (Fl4Spec.NonDetE.unlessE (absCap nc = .nullCap) (Fl4Spec.NonDetE.liftE (ε := Unit) m)).run σ1 =
        (Fl4Spec.NonDetE.liftE (ε := Unit) m).run σ1 := by
    intro m; simp only [Fl4Spec.NonDetE.unlessE, hann, ↓reduceIte]
  by_cases h1 : soB nc cs = true
  swap
  · simp only [h1, Bool.false_and, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ?_, by trivial, by trivial, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩,
      by intros; trivial, MdbStep.refl hM⟩
    rw [hun, run_liftE' (s' := σ1) (a := ())]
    rw [checkCapAt_eq hgs, if_neg (fun h => h1 (e1.2 h))]
  by_cases h2 : soB (.Thread t) cl = true
  swap
  · simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ?_, by trivial, by trivial, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩,
      by intros; trivial, MdbStep.refl hM⟩
    rw [hun, run_liftE' (s' := σ1) (a := ())]
    rw [checkCapAt_eq hgs, if_pos (e1.1 h1), checkCapAt_eq hgl, if_neg (fun h => h2 (e2.2 h))]
  simp only [h1, h2, Bool.and_self, ↓reduceIte]
  -- the source slot still holds the cap the new one was derived from
  have hcs0 : cs = srcC0 := by
    rcases hczs with e | e | e
    · rw [capV_of_capAt hcs] at e; rw [e, hsrc0]
    · rw [capV_of_capAt hcs] at e; subst e; rw [soB_null_right] at h1; cases h1
    · rw [capV_of_capAt hcs] at e
      obtain ⟨p, zt, k, rfl⟩ : ∃ p zt k, cs = .Zombie p zt k := by
        cases cs <;> simp [isZb] at e; exact ⟨_, _, _, rfl⟩
      rw [soB_zombie_right] at h1; cases h1
  subst hcs0
  have hsnn : cs ≠ .Null := fun e => by subst e; rw [soB_null_right] at h1; cases h1
  have hnut : isUt nc = false := by
    cases hu : isUt nc
    · rfl
    · obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 hu; simp [soB] at h1
  have hzb : isZb cs = false := by
    cases hz : isZb cs
    · rfl
    · obtain ⟨p, zt, k, rfl⟩ : ∃ p zt k, cs = .Zombie p zt k := by
        cases cs <;> simp [isZb] at hz; exact ⟨_, _, _, rfl⟩
      rw [soB_zombie_right] at h1; cases h1
  have hut : isUt cs = true → ∀ y, ¬ Mdb.Desc G1.par y (cslotAddr (ps.bv, idxs)) := by
    intro hu
    obtain ⟨q, sz, f, d, e⟩ := isUt_iff.1 hu
    rw [e, soB_ut_right] at h1; cases h1
  have hzc : isZb nc = false := by rw [isZb_of_shape hsh]; exact hzb
  have hdst : capAt (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = ok .Null := by
    rw [capAt_capV, hroot]
  have hsrcm := (hM.members _).2 ⟨hAsrc.isSlot, cs, hcs, hsnn⟩
  have hdestm : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) ∉ G1.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn0 (by simpa using h0.symm)
  have hfull := fullF_none_of (a := cs) hnut
  obtain ⟨s2, h2s, σ', G', hins, hR', hV', hM', hC', hI', hFI', hSti⟩ := spec_exists
    (insert_full_abs_fin th s1 σ1 G1 hR hV hP hM hC hI hFI hps hls hAt hcs hsnn hdst nc (absCap nc)
      ⟨hwf, rfl⟩ hcv he hnn hsh hbd hut hzb hkey hv)
  have hSt := hSti (fun hu => by rw [← isUt_of_shape hsh, hnut] at hu; cases hu)
  obtain ⟨s3, h3s, hD'⟩ := spec_exists
    (insert_delinv hP s1 G1 hM hD hsrcm hAt.isSlot hdestm hcs nc he hfull hnn hzc)
  obtain ⟨s4, h4s, hcap⟩ := spec_exists
    (insert_caps_nofull hP s1 G1 hM hsrcm hAt.isSlot hdestm hcs nc he hfull)
  rw [h2s] at h3s h4s
  cases eq_of_ok_eq h3s; cases eq_of_ok_eq h4s
  rw [h2s]; simp only [bind_ok, WP.spec_ok]
  refine ⟨σ', G', ?_, by trivial, by trivial, ⟨⟨hR', hV', hM', hC', hI'⟩, hD', hFI'⟩, fun y hy hyx => by
    rw [hcap y hy, if_neg hyx], hSt⟩
  rw [hun, run_liftE' (s' := σ') (a := ())]
  rw [checkCapAt_eq hgs, if_pos (e1.1 h1), checkCapAt_eq hgl, if_pos (e2.1 h2), hins]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- A CNode slot is none of a TCB's slots. -/
theorem cnode_slot_ne_tcb {th : TypedHeap} (hP : Placed th) {ps t : U64} {rs : Nat} (hps : th ps = some (.cnode rs))
    {idxs : List Bool} (hls : idxs.length = rs) (ht : th t = some .tcb) :
    ∀ i, i < tcbSlots → cslotAddr (ps.bv, idxs) ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i) := by
  intro i hi e
  have hAsrc : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex i) := ⟨t, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩
  have := cslotAddr_inj hP hAsrc hAt e
  have hpt : ps = t := (UScalar.eq_equiv_bv_eq ps t).2 (congrArg Prod.fst this)
  rw [hpt, ht] at hps; cases hps

/-- What an install of a cap into a TCB slot ends with: an outcome of the
spec's of the same kind (Ok, or preempted) in states related by `DState`;
when Ok, every slot other than the TCB's has its cap kept, emptied or made
a zombie. -/
def InstPost (th : TypedHeap) (t : U64) (m : Fl4Spec.PMonad Unit Unit) (s : S) (σ : Fl4Spec.State Unit)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ (m.run σ).1 ∧
        ∀ y, IsSlot th y → (∀ i, i < tcbSlots → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) →
          ChgZ (L.mem s) (L.mem res.2.1) y) ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ (m.run σ).1)) ∧
    DState (L := L) th res.2.1 σ' G'

def InstPostQ (Q : (U64 → U64) → MdbGhost → Prop) (th : TypedHeap) (t : U64) (m : Fl4Spec.PMonad Unit Unit) (s : S) (σ : Fl4Spec.State Unit)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ (m.run σ).1 ∧
        ∀ y, IsSlot th y → (∀ i, i < tcbSlots → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) →
          ChgZ (L.mem s) (L.mem res.2.1) y) ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ (m.run σ).1)) ∧
    DState (L := L) th res.2.1 σ' G' ∧ Q (L.mem res.2.1) G'

/-- `InstPostQ` without the invariant. -/
theorem InstPostQ.old {Q : (U64 → U64) → MdbGhost → Prop} {th : TypedHeap} {t : U64} {m : Fl4Spec.PMonad Unit Unit} {s : S}
    {σ : Fl4Spec.State Unit} {res : core.result.Result Unit error.Exc × S × A}
    (h : InstPostQ (L := L) Q th t m s σ res) : InstPost (L := L) th t m s σ res := by
  obtain ⟨σ', G', hc, hDS, -⟩ := h; exact ⟨σ', G', hc, hDS⟩

/-- **`tcb::install_tcb_cap` refines l4v `install_tcb_cap`** (slot `n` of
TCB `t`, the new cap `nc` derived from the cap at the source slot): FL4's
`delete(slot, true)` against `cap_delete`, then the checks and the insert
(`install_after`). The deletion's hypotheses are `DelRound`'s; the CSpace
is small enough for its fuel (`hB`). -/
theorem install_tcb_cap_refinesQ {Q : (U64 → U64) → MdbGhost → Prop} (hQ : ∀ m G m' G', MdbStep m G m' G' → Q m G → Q m' G') (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : Q (L.mem s) G)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (idx : U64) (hidx : idx.val = n)
    (hcz0 : ∀ y, IsSlot th y → (∀ i, i < tcbSlots → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) →
      ChgZ (L.mem s0) (L.mem s) y)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPostQ (L := L) Q th t (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ⦄ := by
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht
  have hczs0 := hcz0 _ hAsrc.isSlot hsrcT
  unfold tcb.install_tcb_cap
  rw [spec_eq_ok (tcb_slot_spec t idx), tcb_root_eq t idx hn hidx]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    refine WP.spec_mono (install_after th hP s0 s a σ G hDS t ht n hn (by rw [capV_of_capAt hc0])
      ssl hAs nc hwf hcv he hfw hps hls hczs0 hsrc0 hsh hbd hkey hv) ?_
    rintro res ⟨σ', G', hrun, hr1, -, hDS', hcap, hst⟩
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    refine ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok (by rw [capDelete_null hg0']; rfl) (mem_of_run hrun),
      fun y hy hyt => (hcz0 y hy hyt).trans (ChgZ.of_eq (hcap y hy (hyt n hn)))⟩, hDS', hQ _ _ _ _ hst hMO⟩
  · apply WP.spec_bind (delete_full arI th hP (finalHyp_full th hP) hO hPP hPD K hK hK6 _ hAt s a σ G hDS
      (by rw [capV_of_capAt hc0]; exact hc0n) (hB _ G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_mono (install_after th hP s0 s1 a1 σ1 G1 hDS1 t ht n hn hnull ssl hAs nc hwf hcv he
        hfw hps hls (hczs0.trans (hcz _ hAsrc.isSlot (hsrcT n hn))) hsrc0 hsh hbd hkey hv) ?_
      rintro res ⟨σ', G', hrun, hr1, -, hDS', hcap, hst⟩
      exact ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok hmem (mem_of_run hrun),
        fun y hy hyt => (hcz0 y hy hyt).trans ((hcz y hy (hyt n hn)).trans (ChgZ.of_eq (hcap y hy (hyt n hn))))⟩,
        hDS', hQ _ _ _ _ (hmD.trans hst) hMO⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem⟩, hDS1, hQ _ _ _ _ hmD hMO⟩

end

/-! ## Sequencing the installs -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- Every slot but the TCB's. -/
def NotTcbSlot (t : U64) (y : U64) : Prop := ∀ i, i < tcbSlots → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)

theorem inst_seqQ {Q : (U64 → U64) → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 : S} {σ : Fl4Spec.State Unit} {m1 m2 : Fl4Spec.PMonad Unit Unit}
    {P : Result (core.result.Result Unit error.Exc × S × A)}
    {K : S → A → Result (core.result.Result Unit error.Exc × S × A)}
    (h1 : P ⦃ res => InstPostQ (L := L) Q th t m1 s0 σ res ⦄)
    (h2 : ∀ s1 a1 σ1 G1, DState (L := L) th s1 σ1 G1 → (.ok (), σ1) ∈ (m1.run σ).1 →
      (∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s1) y) → Q (L.mem s1) G1 →
      K s1 a1 ⦃ res => InstPostQ (L := L) Q th t m2 s0 σ1 res ⦄) :
    (do
      let (r, s1, a1) ← P
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => K s1 a1
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s1, a1)) ⦃ res => InstPostQ (L := L) Q th t (m1 >>= fun _ => m2) s0 σ res ⦄ := by
  apply WP.spec_bind h1
  rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hcase, hDS1, hMO1⟩
  rcases hcase with ⟨hr, hmem, hcz⟩ | ⟨hr, hmem⟩
  · simp only at hr; subst hr
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_mono (h2 s1 a1 σ1 G1 hDS1 hmem hcz hMO1) ?_
    rintro res ⟨σ2, G2, hc2, hDS2, hMO2⟩
    refine ⟨σ2, G2, ?_, hDS2, hMO2⟩
    rcases hc2 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, mem_bindE_ok hmem h2, h3⟩
    · exact Or.inr ⟨h1, mem_bindE_ok hmem h2⟩
  · simp only at hr; subst hr
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok]
    rw [WP.spec_ok]
    exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem⟩, hDS1, hMO1⟩

theorem inst_skipQ {Q : (U64 → U64) → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 : S} {σ : Fl4Spec.State Unit} {m2 : Fl4Spec.PMonad Unit Unit}
    {P : Result (core.result.Result Unit error.Exc × S × A)}
    (h : P ⦃ res => InstPostQ (L := L) Q th t m2 s0 σ res ⦄) :
    P ⦃ res => InstPostQ (L := L) Q th t (Fl4Spec.NonDetE.returnOk () >>= fun _ => m2) s0 σ res ⦄ := by
  have e : ∀ x, x ∈ ((Fl4Spec.NonDetE.returnOk () >>= fun _ => m2 : Fl4Spec.PMonad Unit Unit).run σ).1 ↔
      x ∈ (m2.run σ).1 := by
    intro x; rw [run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.PMonad Unit Unit)) rfl]
  refine WP.spec_mono h ?_
  rintro res ⟨σ', G', hc, hDS, hMO⟩
  refine ⟨σ', G', ?_, hDS, hMO⟩
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, (e _).2 h2, h3⟩
  · exact Or.inr ⟨h1, (e _).2 h2⟩

theorem inst_doneQ {Q : (U64 → U64) → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) (hMO : Q (L.mem s) G)
    (hcz : ∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s) y) :
    (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a) :
      Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      InstPostQ (L := L) Q th t (Fl4Spec.NonDetE.returnOk ()) s0 σ res ⦄ := by
  rw [WP.spec_ok]
  exact ⟨σ, G, Or.inl ⟨rfl, rfl, hcz⟩, hDS, hMO⟩

end

/-! ## The IPC buffer -/

theorem mem_liftE_ok {σ' α ε : Type} {m : Fl4Spec.NonDet σ' α} {s : σ'} {x : α × σ'} (h : x ∈ (m s).1) :
    (.ok x.1, x.2) ∈ ((Fl4Spec.NonDetE.liftE (ε := ε) m).run s).1 := by
  unfold Fl4Spec.NonDetE.liftE
  rw [ExceptT.run_lift]
  exact mem_bind_nd h rfl

/-- A new cap and the CNode slot it was derived from, at decode time:
well-formed, valid, of the source's shape, badge (or a fresh badge) and
object. -/
def NewCapOK (th : TypedHeap) (mem0 : U64 → U64) (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) : Prop :=
  ∃ ps rs, th ps = some (.cnode rs) ∧ sl.1 = ps.bv ∧ sl.2.length = rs ∧ CapWf nc ∧ CapValid th nc ∧ EncWf nc ∧
    (isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc)) ∧
    shape nc = shape (capV mem0 (cslotAddr sl)) ∧
    (badgeF nc = badgeF (capV mem0 (cslotAddr sl)) ∨ badgeF (capV mem0 (cslotAddr sl)) = 0#u64) ∧
    okey nc = okey (capV mem0 (cslotAddr sl)) ∧
    ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV mem0 (cslotAddr sl)) → Vs.VCapOK P L4 L3 L2 L1 nc

/-- FL4's buffer argument: no frame is source slot `0`. -/
def bufArg (bc0 : capability.Cap) : Option (capability.Cap × Fl4Spec.CslotPtr) → capability.Cap × U64
  | none => (bc0, 0#u64)
  | some (c, sl) => (c, cslotAddr sl)

/-- The spec's frame argument. -/
def frameOf : Option (capability.Cap × Fl4Spec.CslotPtr) → Option (Fl4Spec.Cap × Fl4Spec.CslotPtr)
  | none => none
  | some (c, sl) => some (absCap c, sl)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem still_valid_zero (s : S) (t slot : U64) (nc : capability.Cap) :
    tcb.still_valid st s t slot nc 0#u64 = ok false := by
  unfold tcb.still_valid; simp [is_null_eq]

/-- **The scheduler-state side of `install_buffer`** (P1's): FL4's
`set_ipc_buffer` against the spec's `thread_set` of the IPC buffer, and the
tail (`reschedule_required` if the target is the current thread) against
the spec's; both keep every cap slot and every CNode and TCB of the spec. -/
structure BufHyp (th : TypedHeap) (t addr : U64) (ptr : Fl4Spec.VSpaceRef) : Prop where
  ipc : ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    obj.Tcb.set_ipc_buffer st t s addr ⦃ s' => SlotsSame th (L.mem s) (L.mem s') ∧ ∃ σ',
      ((), σ') ∈ (Fl4Spec.threadSet (Z := Unit) (fun x => { x with tcbIpcBuffer := ptr }) t.bv σ).1 ∧
      CRel th (L.mem s') σ' G ∧ KSub σ σ' ⦄
  tail : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    (do
      let t_1 ← sched.cur_thread st s
      let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t_1
      if b1 = true then do
          let s5 ← sched.reschedule_required st s
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = a ∧ SlotsSame th (L.mem s) (L.mem res.2.1) ∧ ∃ σ',
        (.ok (), σ') ∈ ((do
          let cur ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
          Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.when (t.bv = cur) Fl4Spec.rescheduleRequired) :
            Fl4Spec.PMonad Unit Unit).run σ).1 ∧
        CRel th (L.mem res.2.1) σ' G ∧ KSub σ σ' ⦄

/-- `DState` across a step keeping every cap slot and every CNode and TCB. -/
theorem DState.of_same {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) (hS : SlotsSame th (L.mem s) (L.mem s')) (hCR : CRel th (L.mem s') σ' G)
    (hK : KSub σ σ') : DState (L := L) th s' σ' G :=
  ⟨hCR, hDS.2.1.of_same hS, hDS.2.2.of_same hDS.1.2.2.1 hS hK⟩

/-- **The frame cap's check and insert**, after the delete: as in
`install_after`, without the null test (a null cap is to no object). -/
theorem check_insert (th : TypedHeap) (hP : Placed th) (s s1 : S) (σ1 : Fl4Spec.State Unit)
    (G1 : MdbGhost) (hDS1 : DState (L := L) th s1 σ1 G1)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots)
    (hroot : capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (srcSl : Fl4Spec.CslotPtr) (hok : NewCapOK th (L.mem s) nc srcSl)
    (hczs : ChgZ (L.mem s) (L.mem s1) (cslotAddr srcSl)) :
    (do
      let b ← tcb.still_valid st s1 t (cslotAddr ssl) nc (cslotAddr srcSl)
      if b = true then cdt.insert st s1 nc (cslotAddr srcSl) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))
        else ok s1) ⦃ s4 =>
      ∃ σ' G', Fl4Spec.checkCapAt (Z := Unit) (absCap nc) srcSl (Fl4Spec.checkCapAt (.threadCap t.bv) ssl
            (Fl4Spec.capInsert (absCap nc) srcSl (t.bv, Fl4Spec.tcbCnodeIndex n))) σ1 = ({((), σ')}, False) ∧
        DState (L := L) th s4 σ' G' ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → capV (L.mem s4) y = capV (L.mem s1) y) ∧
        MdbStep (L.mem s1) G1 (L.mem s4) G' ⦄ := by
  obtain ⟨ps, rs, hps, h1s, hls, hwf, hcv, he, hfw, hsh, hbd, hkey, hvk⟩ := hok
  obtain ⟨sa, idxs⟩ := srcSl
  simp only at h1s hls; subst h1s
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS1
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  rw [still_valid_eq _ _ _ _ nc (hAsrc.isSlot.ne_zero hP)]
  simp only [bind_ok]
  obtain ⟨cs, asr, hcs, hcas, hgs⟩ := hR.abs_cap hAsrc
  obtain ⟨cl, al, hcl, hcal, hgl⟩ := hR.abs_cap hAs
  rw [capV_of_capAt hcs, capV_of_capAt hcl]
  have e1 : soB nc cs = true ↔ Fl4Spec.sameObjectAs (absCap nc) asr := by
    rw [hcas.abs]; exact soB_iff nc cs hwf hcas.1 hfw
  have e2 : soB (.Thread t) cl = true ↔ Fl4Spec.sameObjectAs (.threadCap t.bv) al := by
    rw [hcal.abs]; exact soB_iff (.Thread t) cl trivial hcal.1 (by simp [isFrame])
  by_cases h1 : soB nc cs = true
  swap
  · simp only [h1, Bool.false_and, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ?_, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, by intros; trivial, MdbStep.refl hM⟩
    rw [checkCapAt_eq hgs, if_neg (fun h => h1 (e1.2 h))]
  by_cases h2 : soB (.Thread t) cl = true
  swap
  · simp only [h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ?_, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, by intros; trivial, MdbStep.refl hM⟩
    rw [checkCapAt_eq hgs, if_pos (e1.1 h1), checkCapAt_eq hgl, if_neg (fun h => h2 (e2.2 h))]
  simp only [h1, h2, Bool.and_self, ↓reduceIte]
  have hcs0 : cs = capV (L.mem s) (cslotAddr (ps.bv, idxs)) := by
    rcases hczs with e | e | e
    · rw [capV_of_capAt hcs] at e; exact e
    · rw [capV_of_capAt hcs] at e; subst e; rw [soB_null_right] at h1; cases h1
    · rw [capV_of_capAt hcs] at e
      obtain ⟨p, zt, k, rfl⟩ : ∃ p zt k, cs = .Zombie p zt k := by
        cases cs <;> simp [isZb] at e; exact ⟨_, _, _, rfl⟩
      rw [soB_zombie_right] at h1; cases h1
  rw [← hcs0] at hsh hbd hkey hvk
  have hsnn : cs ≠ .Null := fun e => by subst e; rw [soB_null_right] at h1; cases h1
  have hnn : nc ≠ .Null := fun e => by subst e; simp [soB] at h1; rw [srB_of_eq (v := false) rfl] at h1; cases h1
  have hnut : isUt nc = false := by
    cases hu : isUt nc
    · rfl
    · obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 hu; simp [soB] at h1
  have hzb : isZb cs = false := by
    cases hz : isZb cs
    · rfl
    · obtain ⟨p, zt, k, rfl⟩ : ∃ p zt k, cs = .Zombie p zt k := by
        cases cs <;> simp [isZb] at hz; exact ⟨_, _, _, rfl⟩
      rw [soB_zombie_right] at h1; cases h1
  have hut : isUt cs = true → ∀ y, ¬ Mdb.Desc G1.par y (cslotAddr (ps.bv, idxs)) := by
    intro hu
    obtain ⟨q, sz, f, d, e⟩ := isUt_iff.1 hu
    rw [e, soB_ut_right] at h1; cases h1
  have hzc : isZb nc = false := by rw [isZb_of_shape hsh]; exact hzb
  have hdst : capAt (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = ok .Null := by
    rw [capAt_capV, hroot]
  have hsrcm := (hM.members _).2 ⟨hAsrc.isSlot, cs, hcs, hsnn⟩
  have hdestm : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) ∉ G1.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn0 (by simpa using h0.symm)
  have hfull := fullF_none_of (a := cs) hnut
  obtain ⟨s2, h2s, σ', G', hins, hR', hV', hM', hC', hI', hFI', hSti⟩ := spec_exists
    (insert_full_abs_fin th s1 σ1 G1 hR hV hP hM hC hI hFI hps hls hAt hcs hsnn hdst nc (absCap nc)
      ⟨hwf, rfl⟩ hcv he hnn hsh hbd hut hzb hkey hvk)
  have hSt := hSti (fun hu => by rw [← isUt_of_shape hsh, hnut] at hu; cases hu)
  obtain ⟨s3, h3s, hD'⟩ := spec_exists
    (insert_delinv hP s1 G1 hM hD hsrcm hAt.isSlot hdestm hcs nc he hfull hnn hzc)
  obtain ⟨s4, h4s, hcap⟩ := spec_exists
    (insert_caps_nofull hP s1 G1 hM hsrcm hAt.isSlot hdestm hcs nc he hfull)
  rw [h2s] at h3s h4s
  cases eq_of_ok_eq h3s; cases eq_of_ok_eq h4s
  rw [h2s, WP.spec_ok]
  refine ⟨σ', G', ?_, ⟨⟨hR', hV', hM', hC', hI'⟩, hD', hFI'⟩, fun y hy hyx => by rw [hcap y hy, if_neg hyx], hSt⟩
  rw [checkCapAt_eq hgs, if_pos (e1.1 h1), checkCapAt_eq hgl, if_pos (e2.1 h2), hins]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem tcb_slot_buffer (t : U64) :
    obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) := by
  rw [spec_eq_ok (tcb_slot_spec t _), tcb_root_eq t _ (n := 2) (by decide) (by simp [layout.tcb.SLOT_BUFFER])]

/-- **`tcb::install_buffer` refines l4v `install_tcb_frame_cap`**: the
delete of the buffer slot, the IPC buffer word and the scheduler (`BufHyp`,
P1's), the frame cap's checks and insert. -/
theorem install_buffer_refinesQ {Q : (U64 → U64) → MdbGhost → Prop} (hQ : ∀ m G m' G', MdbStep m G m' G' → Q m G → Q m' G') (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : Q (L.mem s) G) (t : U64) (ht : th t = some .tcb)
    (hcz0 : ∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s) y)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef) (hBuf : BufHyp (L := L) (A := A) th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s0) c sl) :
    tcb.install_buffer st arI s a t (cslotAddr ssl) addr (bufArg bc0 bfr) ⦃ res =>
      InstPostQ (L := L) Q th t (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ := by
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
  obtain ⟨c, s3, hbuf⟩ : ∃ c s3, bufArg bc0 bfr = (c, s3) := ⟨_, _, rfl⟩
  have cont : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) th s1 σ1 G1 →
      Q (L.mem s1) G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = .Null →
      (∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s1) y) →
      (.ok (), σ1) ∈ ((Fl4Spec.capDelete (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex 2)).run σ).1 →
      (do
        let s2 ← obj.Tcb.set_ipc_buffer st t s1 addr
        let b ← tcb.still_valid st s2 t (cslotAddr ssl) c s3
        let s4 ← if b = true then cdt.insert st s2 c s3 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) else ok s2
        let t_1 ← sched.cur_thread st s4
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t_1
        if b1 = true then do
            let s5 ← sched.reschedule_required st s4
            ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1)
          else ok (core.result.Result.Ok (), s4, a1)) ⦃ res =>
        InstPostQ (L := L) Q th t (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hMO1 hnull hcz hmem
    apply WP.spec_bind (hBuf.ipc s1 σ1 G1 hDS1)
    rintro s2 ⟨hS2, σ2, hts, hCR2, hK2⟩
    have hDS2 := hDS1.of_same hS2 hCR2 hK2
    have hMO2 := hQ _ _ _ _ (MdbStep.of_same hDS1.1.2.2.1 hS2) hMO1
    have hnull2 : capV (L.mem s2) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = .Null := by
      rw [hS2.capV hAt.isSlot, hnull]
    cases bfr with
    | none =>
      simp only [bufArg, Prod.mk.injEq] at hbuf
      obtain ⟨rfl, rfl⟩ := hbuf
      simp only [still_valid_zero, bind_ok, Bool.false_eq_true, ↓reduceIte]
      apply WP.spec_mono (hBuf.tail s2 a1 σ2 G1 hDS2)
      rintro res ⟨hr1, -, hS5, σ5, htail, hCR5, hK6'⟩
      refine ⟨σ5, G1, Or.inl ⟨hr1, ?_, fun y hy hyt =>
        ((hcz y hy hyt).trans (ChgZ.of_eq (hS2.capV hy))).trans (ChgZ.of_eq (hS5.capV hy))⟩,
        hDS2.of_same hS5 hCR5 hK6', hQ _ _ _ _ (MdbStep.of_same hDS2.1.2.2.1 hS5) hMO2⟩
      refine mem_bindE_ok hmem (mem_bindE_ok (mem_liftE_ok hts) (mem_bindE_ok (s' := σ2) (a := ()) ?_ htail))
      exact mem_liftE_ok (x := ((), σ2)) rfl
    | some p =>
      obtain ⟨c', sl⟩ := p
      simp only [bufArg, Prod.mk.injEq] at hbuf
      obtain ⟨rfl, rfl⟩ := hbuf
      have hok := hbfr c' sl rfl
      obtain ⟨ps, rs, hps, h1s, hls, -⟩ := hok
      have hsrcIs : IsSlot th (cslotAddr sl) := by
        obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
        exact (show AbsSlot th (ps.bv, idxs) from ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩).isSlot
      have hsrcT : NotTcbSlot t (cslotAddr sl) := by
        obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
        exact cnode_slot_ne_tcb hP hps hls ht
      have hczs : ChgZ (L.mem s0) (L.mem s2) (cslotAddr sl) :=
        (hcz _ hsrcIs hsrcT).trans (ChgZ.of_eq (hS2.capV hsrcIs))
      rw [← Std.bind_assoc]
      apply WP.spec_bind (check_insert th hP s0 s2 σ2 G1 hDS2 t ht 2 (by decide) hnull2 ssl hAs c' sl
        (hbfr c' sl rfl) hczs)
      rintro s4 ⟨σ4, G4, hchk, hDS4, hcap4, hst4⟩
      have hMO4 := hQ _ _ _ _ (MdbStep.same_left hDS1.1.2.2.1 hS2 hst4) hMO1
      apply WP.spec_mono (hBuf.tail s4 a1 σ4 G4 hDS4)
      rintro res ⟨hr1, -, hS5, σ5, htail, hCR5, hK6'⟩
      refine ⟨σ5, G4, Or.inl ⟨hr1, ?_, fun y hy hyt =>
        (((hcz y hy hyt).trans (ChgZ.of_eq (hS2.capV hy))).trans (ChgZ.of_eq (hcap4 y hy (hyt 2 (by decide))))).trans
          (ChgZ.of_eq (hS5.capV hy))⟩, hDS4.of_same hS5 hCR5 hK6', hQ _ _ _ _ (MdbStep.of_same hDS4.1.2.2.1 hS5) hMO4⟩
      refine mem_bindE_ok hmem (mem_bindE_ok (mem_liftE_ok hts) (mem_bindE_ok (s' := σ4) (a := ()) ?_ htail))
      exact mem_liftE_ok (x := ((), σ4)) (by simp only [frameOf]; rw [hchk]; rfl)
  rw [hbuf]
  unfold tcb.install_buffer
  rw [tcb_slot_buffer]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex 2) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    exact cont s a σ G hDS hMO (by rw [capV_of_capAt hc0]) hcz0 (by rw [capDelete_null hg0']; rfl)
  · apply WP.spec_bind (delete_full arI th hP (finalHyp_full th hP) hO hPP hPD K hK hK6 _ hAt s a σ G hDS
      (by rw [capV_of_capAt hc0]; exact hc0n) (hB _ G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact cont s1 a1 σ1 G1 hDS1 (hQ _ _ _ _ hmD hMO) hnull (fun y hy hyt => (hcz0 y hy hyt).trans (hcz y hy (hyt 2 (by decide)))) hmem
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem⟩, hDS1, hQ _ _ _ _ hmD hMO⟩

end

/-! ## ThreadControl's cap installs -/

/-- The spec's argument for an install: the cap and slot when the flag is set. -/
def optArg (b : Prop) [Decidable b] (p : capability.Cap × Fl4Spec.CslotPtr) :
    Option (Fl4Spec.Cap × Fl4Spec.CslotPtr) :=
  if b then some (absCap p.1, p.2) else none

/-- **The spec's cap installs of ThreadControl** (`invoke_tcb
ThreadControlCaps` up to its result): fault handler, timeout handler, CSpace
and VSpace roots, IPC buffer, as FL4's flags select them. -/
noncomputable def tcCapsSpec (t : U64) (ssl : Fl4Spec.CslotPtr) (flags : U64) (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (ptr : Fl4Spec.VSpaceRef) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr)) : Fl4Spec.PMonad Unit Unit :=
  Fl4Spec.installTcbCap t.bv ssl 3 (optArg ((flags &&& tcb.UPDATE_FAULT) ≠ 0#u64) fh) >>= fun _ =>
  Fl4Spec.installTcbCap t.bv ssl 4 (optArg ((flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) tmh) >>= fun _ =>
  Fl4Spec.installTcbCap t.bv ssl 0 (optArg ((flags &&& tcb.UPDATE_SPACE) ≠ 0#u64) cr) >>= fun _ =>
  Fl4Spec.installTcbCap t.bv ssl 1 (optArg ((flags &&& tcb.UPDATE_SPACE) ≠ 0#u64) vr) >>= fun _ =>
  Fl4Spec.installTcbFrameCap t.bv ssl
    (if (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 then some (ptr, frameOf bfr) else none) >>= fun _ =>
  Fl4Spec.NonDetE.returnOk ()

theorem installTcbCap_none (t : Fl4Spec.ObjRef) (sl : Fl4Spec.CslotPtr) (n : Nat) :
    Fl4Spec.installTcbCap (Z := Unit) t sl n none = Fl4Spec.NonDetE.returnOk () := rfl

theorem installTcbFrameCap_none (t : Fl4Spec.ObjRef) (sl : Fl4Spec.CslotPtr) :
    Fl4Spec.installTcbFrameCap (Z := Unit) t sl none = Fl4Spec.NonDetE.returnOk () := rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `install_tcb_cap_refinesQ` with the new cap's conditions as `NewCapOK`. -/
theorem install_okQ {Q : (U64 → U64) → MdbGhost → Prop} (hQ : ∀ m G m' G', MdbStep m G m' G' → Q m G → Q m' G') (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : Q (L.mem s) G)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (idx : U64) (hidx : idx.val = n)
    (hcz0 : ∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s) y)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) (hok : NewCapOK th (L.mem s0) nc sl) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr sl) ⦃ res =>
      InstPostQ (L := L) Q th t (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, sl))) s0 σ res ⦄ := by
  obtain ⟨ps, rs, hps, h1s, hls, hwf, hcv, he, hfw, hsh, hbd, hkey, hvk⟩ := hok
  obtain ⟨sa, idxs⟩ := sl
  simp only at h1s hls; subst h1s
  exact install_tcb_cap_refinesQ arI hQ th hP hO hPP hPD K hK hK6 hB s0 s a σ G hDS hMO t ht n hn idx hidx hcz0 ssl hAs
    nc hwf hcv he hfw hps hls rfl hsh hbd hkey hvk

/-- **FL4's `thread_control_caps` refines the spec's cap installs of
ThreadControl** (`tcCapsSpec`): each selected install deletes the TCB slot
(`cap_delete`) and, if the new cap still names the source's object and the
invoked cap the thread, inserts it; the IPC buffer's word and the
scheduler are P1's (`BufHyp`). The new caps are derived from their source
slots' caps at the start (`NewCapOK`). -/
theorem thread_control_caps_refinesQ {Q : (U64 → U64) → MdbGhost → Prop} (hQ : ∀ m G m' G', MdbStep m G m' G' → Q m G → Q m' G') (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : Q (L.mem s) G)
    (t : U64) (ht : th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) vr.1 vr.2)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHyp (L := L) (A := A) th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s) c sl) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPostQ (L := L) Q th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ := by
  have r0 : ∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s) (L.mem s) y := fun _ _ _ => ChgZ.refl _ _
  have i3 : (layout.tcb.SLOT_FAULT_HANDLER).val = 3 := by simp [layout.tcb.SLOT_FAULT_HANDLER]
  have i4 : (layout.tcb.SLOT_TIMEOUT_HANDLER).val = 4 := by simp [layout.tcb.SLOT_TIMEOUT_HANDLER]
  have i0 : (layout.tcb.SLOT_CTABLE).val = 0 := by simp [layout.tcb.SLOT_CTABLE]
  have i1 : (layout.tcb.SLOT_VTABLE).val = 1 := by simp [layout.tcb.SLOT_VTABLE]
  unfold tcb.thread_control_caps tcCapsSpec
  by_cases hF : (flags &&& tcb.UPDATE_FAULT) = 0#u64 <;>
  by_cases hT : (flags &&& tcb.UPDATE_TIMEOUT) = 0#u64 <;>
  by_cases hS : (flags &&& tcb.UPDATE_SPACE) = 0#u64 <;>
  by_cases hU : (flags &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 <;>
  simp only [lift, bind_ok, hF, hT, hS, hU, bne_iff_ne, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte,
    optArg, installTcbCap_none, installTcbFrameCap_none] <;>
  -- the fault handler
  (first
    | with_reducible refine inst_skipQ ?_
    | refine inst_seqQ (install_okQ arI hQ th hP hO hPP hPD K hK hK6 hB s s a σ G hDS hMO t ht 3 (by decide) _ i3 r0 ssl hAs
        _ _ (hfh hF)) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the timeout handler
  (first
    | with_reducible refine inst_skipQ ?_
    | refine inst_seqQ (install_okQ arI hQ th hP hO hPP hPD K hK hK6 hB s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hMO) t ht 4 (by decide) _ i4
        (by first | assumption | exact r0) ssl hAs _ _ (htmh hT)) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the CSpace root
  (first
    | with_reducible refine inst_skipQ ?_
    | refine inst_seqQ (install_okQ arI hQ th hP hO hPP hPD K hK hK6 hB s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hMO) t ht 0 (by decide) _ i0
        (by first | assumption | exact r0) ssl hAs _ _ (hcr hS)) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the VSpace root
  (first
    | with_reducible refine inst_skipQ ?_
    | refine inst_seqQ (install_okQ arI hQ th hP hO hPP hPD K hK hK6 hB s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hMO) t ht 1 (by decide) _ i1
        (by first | assumption | exact r0) ssl hAs _ _ (hvr hS)) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the IPC buffer
  (first
    | with_reducible refine inst_skipQ ?_
    | refine inst_seqQ (install_buffer_refinesQ arI hQ th hP hO hPP hPD K hK hK6 hB s _ _ _ _ ‹DState _ _ _ _›
        (by first | assumption | exact hMO) t ht
        (by first | assumption | exact r0) ssl hAs addr ptr (hBuf hU) bc0 bfr hbfr) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  exact inst_doneQ ‹DState _ _ _ _› (by first | assumption | exact hMO) (by first | assumption | exact r0)

end

/-! ## The MDB invariants through ThreadControl's cap installs -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **ThreadControl's cap installs keep the MDB invariants** (`MdbOK`; what
`TcFrameHyp` asks for the frame invariant, from `MdbOK` before):
`thread_control_caps_refinesQ` at `MdbOK`, every step an `MdbStep`. -/
theorem thread_control_caps_mdbOK (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    (t : U64) (ht : th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) vr.1 vr.2)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHyp (L := L) (A := A) th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s) c sl) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPostQ (L := L) (MdbOKV (L.ksb s)) th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ :=
  thread_control_caps_refinesQ arI (MdbOKV.step _) th hP hO hPP hPD K hK hK6 hB s a σ G hDS hMO t ht ssl
    hAs flags fh tmh cr vr hfh htmh hcr hvr addr ptr hBuf bc0 bfr hbfr

end

/-! ## The installs without an invariant (the earlier statements) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem install_tcb_cap_refines (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (idx : U64) (hidx : idx.val = n)
    (hcz0 : ∀ y, IsSlot th y → (∀ i, i < tcbSlots → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) →
      ChgZ (L.mem s0) (L.mem s) y)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPost (L := L) th t (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ⦄ :=
  WP.spec_mono (install_tcb_cap_refinesQ arI (Q := fun _ _ => True) (fun _ _ _ _ _ _ => trivial) th hP hO hPP hPD K hK hK6 hB s0 s a σ G hDS trivial t ht n hn idx hidx hcz0 ssl hAs nc hwf hcv he hfw hps hls hsrc0 hsh hbd hkey hv) (fun _ h => h.old)

theorem install_buffer_refines (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (t : U64) (ht : th t = some .tcb)
    (hcz0 : ∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s) y)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef) (hBuf : BufHyp (L := L) (A := A) th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s0) c sl) :
    tcb.install_buffer st arI s a t (cslotAddr ssl) addr (bufArg bc0 bfr) ⦃ res =>
      InstPost (L := L) th t (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ :=
  WP.spec_mono (install_buffer_refinesQ arI (Q := fun _ _ => True) (fun _ _ _ _ _ _ => trivial) th hP hO hPP hPD K hK hK6 hB s0 s a σ G hDS trivial t ht hcz0 ssl hAs addr ptr hBuf bc0 bfr hbfr) (fun _ h => h.old)

theorem install_ok (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (idx : U64) (hidx : idx.val = n)
    (hcz0 : ∀ y, IsSlot th y → NotTcbSlot t y → ChgZ (L.mem s0) (L.mem s) y)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) (hok : NewCapOK th (L.mem s0) nc sl) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr sl) ⦃ res =>
      InstPost (L := L) th t (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, sl))) s0 σ res ⦄ :=
  WP.spec_mono (install_okQ arI (Q := fun _ _ => True) (fun _ _ _ _ _ _ => trivial) th hP hO hPP hPD K hK hK6 hB s0 s a σ G hDS trivial t ht n hn idx hidx hcz0 ssl hAs nc sl hok) (fun _ h => h.old)

theorem thread_control_caps_refines (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (t : U64) (ht : th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) vr.1 vr.2)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHyp (L := L) (A := A) th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s) c sl) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPost (L := L) th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ :=
  WP.spec_mono (thread_control_caps_refinesQ arI (Q := fun _ _ => True) (fun _ _ _ _ _ _ => trivial) th hP hO hPP hPD K hK hK6 hB s a σ G hDS trivial t ht ssl hAs flags fh tmh cr vr hfh htmh hcr hvr addr ptr hBuf bc0 bfr hbfr) (fun _ h => h.old)

end

/-! ## Against `invoke_tcb` -/

theorem mem_bindE_mono {σ ε α β γ : Type} {m : Fl4Spec.NonDetE σ ε α} {k1 : α → Fl4Spec.NonDetE σ ε β}
    {k2 : α → Fl4Spec.NonDetE σ ε γ} {F : Except ε β × σ → Except ε γ × σ}
    (hF : ∀ e s, F (.error e, s) = (.error e, s))
    (hk : ∀ a s x, x ∈ ((k1 a).run s).1 → F x ∈ ((k2 a).run s).1) {s : σ} {x : Except ε β × σ}
    (hx : x ∈ ((m >>= k1).run s).1) : F x ∈ ((m >>= k2).run s).1 := by
  rw [ExceptT.run_bind] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨y, hy, ?_⟩
  obtain ⟨r, s'⟩ := y
  cases r with
  | ok a => exact hk a s' x hxy
  | error e =>
    have : x = (.error e, s') := Set.mem_singleton_iff.1 hxy
    subst this; rw [hF]; rfl

/-- A ThreadControl outcome with the invocation's result. -/
def tcRet {σ : Type} : Except Unit Unit × σ → Except Unit (List Fl4Spec.Data) × σ
  | (.ok (), s) => (.ok [], s)
  | (.error e, s) => (.error e, s)

/-- **`tcCapsSpec` is `invoke_tcb ThreadControlCaps`** up to its result. -/
theorem tcCapsSpec_mem (t : U64) (ssl : Fl4Spec.CslotPtr) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr) (ptr : Fl4Spec.VSpaceRef)
    (bfr : Option (capability.Cap × Fl4Spec.CslotPtr)) {σ : Fl4Spec.State Unit}
    {x : Except Unit Unit × Fl4Spec.State Unit}
    (hx : x ∈ ((tcCapsSpec t ssl flags fh tmh cr vr ptr bfr).run σ).1) :
    tcRet x ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlCaps t.bv ssl
      (optArg ((flags &&& tcb.UPDATE_FAULT) ≠ 0#u64) fh) (optArg ((flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) tmh)
      (optArg ((flags &&& tcb.UPDATE_SPACE) ≠ 0#u64) cr) (optArg ((flags &&& tcb.UPDATE_SPACE) ≠ 0#u64) vr)
      (if (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 then some (ptr, frameOf bfr) else none))).run σ).1 := by
  have hF : ∀ e (s : Fl4Spec.State Unit), tcRet (.error e, s) = (.error e, s) := fun _ _ => rfl
  unfold tcCapsSpec at hx
  unfold Fl4Spec.invokeTcb
  refine mem_bindE_mono hF (fun _ _ _ h => ?_) hx
  refine mem_bindE_mono hF (fun _ _ _ h => ?_) h
  refine mem_bindE_mono hF (fun _ _ _ h => ?_) h
  refine mem_bindE_mono hF (fun _ _ _ h => ?_) h
  refine mem_bindE_mono hF (fun _ _ _ h => ?_) h
  have : _ = _ := Set.mem_singleton_iff.1 h
  subst this; rfl

/-! ## CopyRegisters, ReadRegisters, WriteRegisters: their caps -/

/-- FL4's `thread_arg`: the slot's cap is a thread cap, else
`InvalidCapability`. -/
def threadArgF (c : capability.Cap) (pos : U64) : core.result.Result U64 error.Exc :=
  match c with
  | .Thread p => .Ok p
  | _ => .Err (.Sys (.InvalidCapability pos))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem thread_arg_eq (s : S) (slot pos : U64) :
    tcb.thread_arg st s slot pos = ok (threadArgF (capV (L.mem s) slot) pos) := by
  unfold tcb.thread_arg
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases capV (L.mem s) slot <;> rfl

end

/-- **CopyRegisters' source cap** (`thread_arg` of extra cap 0, position 1)
against the spec's `decode_copy_registers`: a thread cap gives its thread;
any other cap is `InvalidCapability 1`, on both sides. -/
theorem copy_src_rel (c : capability.Cap) (rest : List Fl4Spec.Cap) {σ : Fl4Spec.State Unit} :
    (∃ p, threadArgF c 1#u64 = .Ok p ∧
      ((match absCap c :: rest with
        | .threadCap p :: _ => Fl4Spec.NonDetE.returnOk p
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef).run σ =
        ({(.ok p.bv, σ)}, False))) ∨
    (threadArgF c 1#u64 = .Err (.Sys (.InvalidCapability 1#u64)) ∧
      ((match absCap c :: rest with
        | .threadCap p :: _ => Fl4Spec.NonDetE.returnOk p
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef).run σ =
        ({(.error (.invalidCapability 1), σ)}, False))) := by
  cases c
  case Thread p => exact Or.inl ⟨p, rfl, rfl⟩
  all_goals first
    | exact Or.inr ⟨rfl, rfl⟩
    | (simp only [absCap]; split_ifs <;> exact Or.inr ⟨rfl, rfl⟩)
    | (simp only [absCap]; exact Or.inr ⟨rfl, rfl⟩)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The register invocations' CSpace side: given P1's account of the
register and scheduler work (every cap slot kept; the spec's state related,
with no new CNode or TCB), `DState` is kept. -/
theorem regs_dstate {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) (hS : SlotsSame th (L.mem s) (L.mem s'))
    (hCR : CRel th (L.mem s') σ' G) (hK : KSub σ σ') : DState (L := L) th s' σ' G :=
  hDS.of_same hS hCR hK

end

end Fl4Proofs.P3
