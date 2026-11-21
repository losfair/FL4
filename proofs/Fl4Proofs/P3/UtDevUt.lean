/-
P3 (losfair/FL4#34), untyped: **the no-reset retype of device untypeds at
`J`** (handoff/devretype.md "dj3 line" (1), "dj4 line") and the device
retype's step at `J` without a reset.

FL4's `untyped::retype` from a CNode slot's device untyped cap, without a
reset (the cap has a child), of untypeds (type 0): FL4 writes only the
window's slots, the spec adds no object (its `retype_region` skips untypeds)
and changes only CNodes. The new caps are device untypeds over slices of the
source's free part, so they inherit `DevApart`'s clauses from the source's
(`DevApart.retype`'s `hcjD`) and have no spec object in their range.

* `SpecFreeP.retypeU`: UtUtRet's `SpecFree.retypeU` for any `P` the source
  satisfies; `SpecFree.retypeU_dev`: the RAM caps' `SpecFree` after the
  untyped retype from a device source (with `DevFreeT`).
* `JAtZ.utUtDevBodyJ`: UtUtRet's `JAtZ.utUtBodyJ` for a device source, the
  source's RAM facts replaced as in UtDevRet's `JAtZ.utDevBodyJ` (`DevApart`,
  `DevFreeT`, `retype_bodyD`, `JPlaced.retypeGS`, `create_noresetBD`,
  `retype_window_deadS`); no window zero is needed (no new object).
* `JAtZ.utDevJ`: the restart and the no-reset retype of untypeds or frames
  from a device untyped, ending in `UtRetPostJ`.
  (The reset of a used device cap and `JAtZ.jUtRetHypDev`: UtDevReset.)
-/
import Fl4Proofs.P3.UtUtRet
import Fl4Proofs.P3.UtDevRet
import Fl4Proofs.P3.UtRetLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **`SpecFreeP` across the untyped retype** (UtUtRet's `SpecFree.retypeU`
for any `P` the source satisfies). -/
theorem SpecFreeP.retypeU {P : U64 → U64 → Bool → Prop} {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost}
    {σ σ1 σ' : Fl4Spec.State Unit} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr}
    {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {p sb fi : U64} {d : Bool}
    (hSF : SpecFreeP P m G σ) (hU : UtInv m G) (hst : KSz σ σ1)
    (hcs : capV m (cslotAddr sl) = .Untyped p sb fi d) (hPs : P p sb d)
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap d p.bv sb.val fi.val, σ1)}, False))
    (hbelow : rs = false → p.val + fi.val ≤ rb.toNat)
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1)
    (hK : y.2.kheap = σ'.kheap)
    (hU' : UtInv m' G') (hI' : MdbInv m' G')
    (hE : RetExp th th' m m' G G' A k w dslot cj (cslotAddr sl))
    (hok : y.1 = .ok () → A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧
      ∀ j, j < w → isUt (cj j) = true → t = .untyped)
    (htu : t = .untyped) :
    SpecFreeP P m' G' σ' := by
  intro x' hx' p' sb' fi' d' hcx' hP' o ko' ho
  rw [← hK] at ho
  obtain ⟨hxG, p0, sb0, fi0, fi1, d0, e0, e1, hpA, hAf1, hAs, -, hoth⟩ := hE.usrc
  rw [hcs] at e0; cases e0
  have hsb : sb.val < 64 := capV_ut_sb hcs
  have hfitS : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
    have hreg := hU.reg _ hxG (by rw [hcs]; exact physF_ut _ _ _ _)
    rw [hcs] at hreg
    exact (ut_range hsb hreg).2.2
  have hfiS : fi.val ≤ 2 ^ sb.val := hU.fib _ hxG p sb fi d hcs
  have hk1 := hE.k1
  obtain ⟨hrs, hkh⟩ := invokeUntyped_kheap bitsApi sl rs pb rb t us slots dev σ1 hg y hy
  rcases hkh o ko' ho with ⟨ko1, h1, e1', hR⟩ | ⟨ht, hm, cd, ecd⟩
  · -- an old object
    obtain ⟨ko0, h0, e0'⟩ := hst o ko1 h1
    rw [← objBits_of_aType (e0'.trans e1')]
    have hb1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
    -- against the source: outside its range, or below the window
    have hOW : (o.toNat + 2 ^ Fl4Spec.objBits ko0 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat) ∨
        (p.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko0 ≤ A) := by
      rcases hSF _ hxG p sb fi d hcs hPs o ko0 h0 with e | ⟨l1, l2⟩
      · exact Or.inl e
      · by_cases hc : rs = true ∧ fi.val ≠ 0
        · rw [if_pos hc] at hR
          have := (regionSet_iff p ⟨o⟩ sb.val hsb hfitS).not.1 hR
          exact absurd ⟨l1, by show o.toNat < _; omega⟩ this
        · rcases Bool.eq_false_or_eq_true rs with hr | hr
          · have hz : fi.val = 0 := by by_contra hz; exact hc ⟨hr, hz⟩
            omega
          · have := hbelow hr
            have hy1 : y.1 = .ok () := by rcases hrs with h | h; exact h; rw [hr] at h; cases h
            have := (hok hy1).1
            right; omega
    rcases hE.gmem x' hx' with hxG' | ⟨j, hj, rfl⟩
    · have hut : isUt (capV m x') = true := by
        by_contra hn
        have := (hE.keep x' hxG' (by simpa using hn)).2
        rw [hcx'] at this; rw [← this] at hn; exact hn rfl
      by_cases hxs : x' = cslotAddr sl
      · subst hxs
        rw [e1] at hcx'; cases hcx'
        rcases hOW with e | ⟨l1, l2⟩
        · exact Or.inl e
        · right; omega
      · rw [hoth x' hxG' hut hxs] at hcx'
        exact hSF x' hxG' p' sb' fi' d' hcx' hP' o ko0 h0
    · -- a new cap: in the window
      have hc := hE.newc j hj
      rw [hcx'] at hc
      have hb := hE.cbase j hj
      have ht := hE.ctop j hj
      rw [← hc] at hb ht
      have hsb' := capV_ut_sb hcx'
      have hreg := hU'.reg _ hx' (by rw [hcx']; exact physF_ut _ _ _ _)
      rw [hcx'] at hreg
      obtain ⟨b1, t1, -⟩ := ut_range hsb' hreg
      have hjk : j * k + k ≤ w * k := by
        have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have hp2 := Nat.one_le_two_pow (n := sb'.val)
      left
      rcases hOW with e | ⟨l1, l2⟩ <;> omega
  · -- no new object: the retype makes untypeds
    exact absurd htu ht

/-- **`SpecFree` (RAM caps) across the untyped retype from a device source**
(`SpecFreeP.retypeU` at `RamP ∨ DevP`, as DevFree's `SpecFree.retype_dev`). -/
theorem SpecFree.retypeU_dev {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost}
    {σ σ1 σ' : Fl4Spec.State Unit} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr}
    {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {p sb fi : U64}
    (hSF : Sched.SpecFree m G σ) (hDF : DevFreeT m G σ) (hU : UtInv m G) (hst : KSz σ σ1)
    (hcs : capV m (cslotAddr sl) = .Untyped p sb fi true)
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap true p.bv sb.val fi.val, σ1)}, False))
    (hbelow : rs = false → p.val + fi.val ≤ rb.toNat)
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1)
    (hK : y.2.kheap = σ'.kheap)
    (hU' : UtInv m' G') (hI' : MdbInv m' G')
    (hE : RetExp th th' m m' G G' A k w dslot cj (cslotAddr sl))
    (hok : y.1 = .ok () → A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧
      ∀ j, j < w → isUt (cj j) = true → t = .untyped)
    (htu : t = .untyped) :
    Sched.SpecFree m' G' σ' := by
  have hB : SpecFreeP (fun p sb d => RamP p sb d ∨ DevP (fun _ _ => True) p sb d) m G σ := by
    intro x hx p sb fi d hc hP o ko ho
    rcases hP with hP | hP
    · exact (specFreeP_ram_iff.2 hSF) x hx p sb fi d hc hP o ko ho
    · exact hDF x hx p sb fi d hc hP o ko ho
  have hA := SpecFreeP.retypeU hB hU hst hcs (Or.inr ⟨rfl, trivial⟩) hg hbelow hy hK hU' hI' hE hok htu
  exact specFreeP_ram_iff.1 fun x hx p sb fi d hc hP o ko ho => hA x hx p sb fi d hc (Or.inl hP) o ko ho

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **The no-reset retype of device untypeds from a device untyped cap at a
`JAtZ` state** (module docstring; UtUtRet's `JAtZ.utUtBodyJ` with the
source's facts from `DevApart` / `DevFreeT`, as UtDevRet's
`JAtZ.utDevBodyJ`): `UtBodyPostD`. -/
theorem JAtZ.utUtDevBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 0) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi true nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win true ⦃ res =>
      UtBodyPostD (L := L) arI AR σ (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) true)
        res ⦄ := by
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI0, -, hMO0, -⟩ := J.xtop.rel
  -- the source's facts: `DevApart`
  have hxG0 : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨hpal, hks1, hnd1, -, -, hrf, -, hcan, -⟩ := hDA _ hxG0 p sb fi (capV_of_capAt hcap)
  have hp0 : 0 < p.val := hcan.1
  have hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 :=
    fit_of_al (show p.val < 2 ^ 64 from p.bv.isLt) (capAt_untyped_inv hcap) hpal
  have hfiLe : fi.val ≤ 2 ^ sb.val := J.ut.fib _ hxG0 p sb fi true (capV_of_capAt hcap)
  have hfree : RegionFree Z.th (p.val + fi.val) (p.val + 2 ^ sb.val) := fun q kd hq =>
    (hrf q kd hq).imp (fun h => by omega) id
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hty := hctx.ty
  have ht : t = .untyped := ((objTypeOf_some hty (by omega) us.val).2.2.2.1).2 hnt
  have htP : t ≠ .archObject .pml4Obj := by rw [ht]; exact fun h => by cases h
  have htT : t ≠ .tcbObject := by rw [ht]; exact fun h => by cases h
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  have hz : zOf nt.val us.val = us.val := by simp [zOf, hnt]
  have hus4 : 4 ≤ us.val := by have := hctx.size.2.2.2.1; omega
  have hus64 : us.val < 64 := hctx.size.1
  have hK0 : newKind nt.val us.val = none := by simp [newKind, hnt]
  subst hfiv
  -- no restart here: the state the body starts at
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rw [hz]; exact hus64)
    hpal hpfit hfiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_bodyD (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx hcap
    hpal hpfit hfiLe hcan (fun h => by cases h) hfree (fun h => by cases h) Fl4Spec.fl4ObjBitsApi nt us dest off win t r hty
    (by omega) hctx.size.1 hctx.size.2.1 (fun h => by omega) (fun h => by omega) (fun _ => by omega) hctx.cnode.1
    hctx.cnode.2.1
    hctx.window.2.2 hctx.window.1 hctx.memory hctx.empty hb) (fun res hRP => ?_)
  have hRPN := RetPostB.toNB hRP
  obtain ⟨hok, har, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, Aw, k, w, dslot, cj,
    hE, hbr, hRFu⟩ := hRP
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, -, -, -, -, ⟨n0, hn0, hThX, uu, huu, hcj⟩, -,
    hW, hWZ, -⟩
  · rw [hok] at e; cases e
  have hsR : sR = s ∧ thR = Z.th := by
    rcases hor with ⟨h1, h2, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h1, h2⟩
    · cases hRB
  obtain ⟨e2, e3⟩ := hsR
  subst sR
  subst thR
  have hn0v : n0 = nt.val := objTypeOf_inj hn0 hty
  subst hn0v
  have hk0 : thKindN nt.val us.val = none := by
    unfold thKindN; rw [if_neg (by omega), if_neg (by omega)]
  have hth : th' = Z.th := funext fun q => by rw [hThX.1 q, hk0]; simp
  subst hth
  -- FL4's writes: slot words
  have hw : P1.WritesIn st s res.2.1 (Sched.SlotWd Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact Sched.slotSpan_wd hP hb h
    · exact absurd h1 htP))⟩
  -- the spec's outcome: CNodes changed only
  have hSR1 := J.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  obtain ⟨-, hcnk, hkc, hcdtK, horgK⟩ := invokeUntyped_noreset_ut Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ us.val
    (windowSlots dest r off.val win.val) true σ {pp.bv, dest.bv} (Or.inl rfl)
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Or.inr rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (.ok (), σ') (by rw [← ht, hrun]; rfl)
  have hA := Sched.SpecAdd.none σ (fun _ => .endpoint Fl4Spec.defaultEp)
  have hIN : IdleNew (fun _ => False) (fun _ => Fl4Spec.KernelObject.endpoint Fl4Spec.defaultEp) :=
    fun _ h => h.elim
  have hcjne : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a := by
    intro j _ p b a
    rw [hcj]
    simp [cjOf, newCapOf, hnt]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    exact retExp_pml4_back hE hM hM' hcjne hxs hc
  have hX' := XTopAt.addStep J.xtop hw hA (fun _ h => h.elim) hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (hSt.okv hMO0) hTS
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1
  have hfit := hpfit
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have k1 := hks1
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  have hTn : ¬ t = .tcbObject := htT
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th Z.th (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hA1 hA2 hA3
  -- the spec side
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ.kheap o = σ.kheap o := fun _ _ => rfl
  have hσ1c : ∃ y, σ.kheap (L.curW s).bv = some (.tcb y) := by
    obtain ⟨-, x, hx, -⟩ := J.curRunnable hni hc2; exact ⟨x, hx⟩
  have hC2 := CnStep.of_cnK hcnk
  have hgp' : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcnk.1
    exact e
  have hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao) := fun q ao h => by
    rcases hkc q with e | ⟨r0, cs, cs', e1, -⟩
    · rw [e]; exact h
    · rw [h] at e1; cases e1
  -- the window's slots
  have hslA : ∀ d ∈ windowSlots dest r off.val win.val, AbsSlot Z.th d ∧
      ∃ i, off.val ≤ i ∧ i < off.val + win.val ∧ d = (dest.bv, Fl4Spec.natToCref r i) := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    rw [List.mem_range'_1] at hi
    refine ⟨⟨dest, rfl, Or.inl ?_⟩, i, hi.1, hi.2, rfl⟩
    rw [natToCref_length _ _ (by have := hctx.cnode.2.1; omega)]; exact hctx.cnode.1
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := fun sl h => by
    by_cases hs : sl ∈ windowSlots dest r off.val win.val
    · exact Or.inr (hslA sl hs).1
    · exact Or.inl (by rw [← horgK sl hs]; exact h)
  -- FL4's writes: inside slots
  have hwI : P1.WritesIn st s res.2.1 (InSlot Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact h
    · exact absurd h1 htP))⟩
  have hidl : IdleKeep (L := L) s res.2.1 := J.idleW_keep hX'.fin.1.1.1 hC2.idle hC2.isc
  -- P1's creation: the heap after (no new object), `BlkOK`, `JCovD`
  have hcjR : ∀ j, j < win.val → ∀ p sb fi, cj j ≠ .Untyped p sb fi false := by
    intro j _ p1 sb1 fi1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noresetBD hni hpp hidx hcap hDA hE
    (hRU _ _ hA1 hA3) (fun h => absurd hK0 h) hcjR (by omega) ⟨by omega, fun h => absurd h (by omega)⟩
    (k := 2 ^ zOf nt.val us.val) rfl hAk htT hW (fun hs => by rw [hK0] at hs; cases hs) hidl
  -- `JPlaced` after
  have hcap1 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fiv true) := hcap
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap true p.bv sb.val fiv.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hgc : ∀ y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
        true)).run σ).1,
      ∀ o sz cs y0 n0, σ.kheap o = some (.cnode sz cs) → ¬ Fl4Spec.wellFormedCnodeN sz cs →
        y.2.kheap o ≠ some (.schedContext y0 n0) := by
    intro y hy o sz cs y0 n0 h0 _ hk
    rw [hrun] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    dsimp only at hk
    have h1 : σ.kheap o = some (.cnode sz cs) := h0
    rcases hkc o with e | ⟨r0, cs0, cs', -, e2⟩
    · rw [e, h1] at hk; cases hk
    · rw [e2] at hk; cases hk
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, hhas2, hthx2, hJP2⟩ :=
    Sched.JPlaced.retypeGS (L := L) hJp J.jcov J.ut hI hM hksz hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [hK0] at h; cases h) (fun kd h => by rw [hK0] at h; cases h)
      (fun z h => by rw [hK0] at h; cases h) (fun h => absurd h hn1) (fun h => absurd h hn1)
      J.kern.ksbAl J.kern.nodeFit (fun ct h => by rw [hc2] at h; cases eq_of_ok_eq h; exact J.kern.curT) J.intL
      hgc (capV_of_capAt hcap) k1
      (fun o ko h => hDF _ hxG p sb fiv true (capV_of_capAt hcap) ⟨rfl, trivial⟩ o ko h) hg1
      (fun _ => by rw [← eA]; exact hA1) (fun h => absurd h (by omega)) hidl.2
  have e1' : Aw = A2 := eA.trans eA2.symm
  have e2' : k2' = 2 ^ zOf nt.val us.val := by rw [ek2, hb]
  have e3' : w2 = win.val := by rw [ew2, hlen]
  subst e1' e2' e3'
  have hlohi : Aw = lo2 ∧ Aw + win.val * 2 ^ zOf nt.val us.val = hi2 := by
    rcases hor2 with h | ⟨-, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h.1.symm, h.2.symm⟩
    · cases hRB
  obtain ⟨rfl, rfl⟩ := hlohi
  have hth2 : th2 = Z.th := funext fun q => by rw [(hthx2 rfl).1 q, hk0]; simp
  subst hth2
  obtain ⟨y2, hy2, -, hKS⟩ := hhas2
  rw [hrun] at hy2
  obtain rfl := Set.mem_singleton_iff.1 hy2
  have hJPa := (hJP2 H' hout).of_kheap hKS.1
  -- `JKern` after
  have hDbg : L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hwI.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have K1 := J.kern_keep (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hwI.1 hwI.2.1
    hX'.fin.1.1.1 hC2.ct hC2.csc horig hgp' hao hDbg
  have hRD := (retype_window_deadS J.jcov J.ut hI hE (hDA.srcOK hE (capV_of_capAt hcap) hcjR)).1
  have hoffD : ∀ q kd, H q = some kd → q ∉ D → H' q = some kd := fun q kd hq hqD =>
    hout_old hout rfl rfl hE.k1 hq (by
      by_contra hm
      exact hqD (hRD q kd hq (by unfold MeetsW; omega)).1)
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have hcsR : L.cscW res.2.1 = L.cscW s :=
    cscW_of_sched J.xtop.fin.1.1.1 hX'.fin.1.1.1 hwI.1 hwI.2.1 hC2.csc
  have hcscH : H' (L.cscW res.2.1) ≠ none := by
    rw [hcsR]
    obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 J.kern.cscH
    rw [hoffD _ kd hkd (J.cscLive.resolve_right hres)]; simp
  have hcurR : (L.curW res.2.1).val + 2 ^ 12 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ (L.curW res.2.1).val := by
    have := hfree _ .tcb K1.curT; simp only [objSize] at this; omega
  have hTb : ∀ q, H q = some .tcb → q.val + 4096 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ q.val :=
    fun q hq => by
      have := hfree q .tcb ((hJp.tcb q).2 hq); simp only [objSize] at this; omega
  have hA0 : 0 < Aw := by omega
  have K2 := K1.hout (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hJPa.heap hout hE.k1 hA0
    (fun q kd _ hK => by rw [hK0] at hK; cases hK) hcurR hcscH
  -- the untyped caps' facts after: the source, the new caps (`UtCapP3.slice`), the others
  obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1u, -, hAf1, -, -, -⟩ := hE.usrc
  rw [capV_of_capAt hcap] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp0, hsb0, hfi0, hd0⟩ := e0
  subst p0 sb0 fi0 d0
  have hsrcG' : cslotAddr (pp.bv, idx) ∈ G'.chains.flatten :=
    (hM'.members _).2 ⟨hAs.isSlot, _, capAt_capV _ _, by rw [e1u]; simp⟩
  have hfi1 : fi1.val ≤ 2 ^ sb.val := hU'.fib _ hsrcG' p sb fi1 true e1u
  have hDn0 : ∀ d ∈ windowSlots dest r off.val win.val, capAt (L.mem s) (cslotAddr d) = ok .Null := by
    intro d hd
    obtain ⟨-, i, h1, h2, rfl⟩ := hslA d hd
    rw [cslotAddr_natToCref _ _ _ (by have := hctx.cnode.2.1; omega) (by have := hctx.window.2.2; omega)]
    exact hctx.empty i h1 h2
  have hnull0 : ∀ d ∈ windowSlots dest r off.val win.val, cslotAddr d ∉ Z.G.chains.flatten := fun d hd h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hDn0 d hd] at h0; exact hn (eq_of_ok_eq h0).symm
  have hDu : ∀ d ∈ windowSlots dest r off.val win.val, ∀ p1 sb1 fi2 dv,
      capV (L.mem res.2.1) (cslotAddr d) = .Untyped p1 sb1 fi2 dv → dv = false →
      UtCapP3 (L := L) arI Z.th res.2.1 σ' G' d p1 sb1 fi2 := by
    intro d hd p1 sb1 fi2 dv e hdv
    exfalso
    have hm : cslotAddr d ∈ G'.chains.flatten :=
      (hM'.members _).2 ⟨(hslA d hd).1.isSlot, _, capAt_capV _ _, by rw [e]; simp⟩
    rcases hE.gmem _ hm with h0 | ⟨j, hj, ej⟩
    · exact hnull0 d hd h0
    · rw [ej] at e
      have h3 := (hE.newc j hj).symm.trans e
      exact hcjR j hj p1 sb1 fi2 (by rw [h3, hdv])
  -- the new caps: device untypeds over slices of the source's free part
  have hcjD : ∀ j, j < win.val → ∀ p1 sb1 fi2, cj j = .Untyped p1 sb1 fi2 true →
      ∃ ps sbs fis : U64, capV (L.mem s) (cslotAddr (pp.bv, idx)) = .Untyped ps sbs fis true ∧
        cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten ∧
        p1.val % 2 ^ sb1.val = 0 ∧ ps.val + fis.val ≤ p1.val ∧ p1.val + 2 ^ sb1.val ≤ ps.val + 2 ^ sbs.val ∧
        4 ≤ sb1.val := by
    intro j hj p1 sb1 fi2 h3
    rw [hcj] at h3
    simp only [cjOf] at h3
    unfold newCapOf at h3
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hnt] at h3
    simp only [capability.Cap.Untyped.injEq] at h3
    obtain ⟨rfl, rfl, -, -⟩ := h3
    refine ⟨p, sb, fiv, capV_of_capAt hcap, hxG, ?_⟩
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hlt : Aw + j * 2 ^ zOf nt.val us.val < 2 ^ 64 := by omega
    have hv : (⟨BitVec.ofNat 64 (Aw + j * 2 ^ zOf nt.val us.val)⟩ : U64).val = Aw + j * 2 ^ zOf nt.val us.val := by
      show (BitVec.ofNat 64 (Aw + j * 2 ^ zOf nt.val us.val)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have h2z : 2 ^ zOf nt.val us.val = 2 ^ uu.val := by rw [hz, huu]
    have hzu : zOf nt.val us.val = uu.val := Nat.pow_right_injective (le_refl 2) h2z
    refine ⟨by rw [hv, ← h2z, Nat.add_mul_mod_self_right]; exact hA2, by rw [hv]; omega, by rw [hv, ← h2z]; omega,
      by omega⟩
  have hcapK : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) →
      (∀ d ∈ windowSlots dest r off.val win.val, y ≠ cslotAddr d) →
      capV (L.mem res.2.1) y = capV (L.mem s) y := by
    intro y hy hyx hyd
    by_cases hyG : y ∈ Z.G.chains.flatten
    · cases hu : isUt (capV (L.mem s) y)
      · exact (hE.keep y hyG hu).2
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := hE.usrc
        exact h5 y hyG hu hyx
    · have h0 : capV (L.mem s) y = .Null := by
        by_contra hn
        exact hyG ((hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩)
      rw [h0]
      by_contra hn
      have hm : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
      rcases hE.gmem y hm with h1 | ⟨j, hj, rfl⟩
      · exact hyG h1
      · have hD : Mdb.Desc G'.par (dslot j) (cslotAddr (pp.bv, idx)) :=
          (hE.desc _ _).2 (Or.inr ⟨j, hj, rfl, Or.inl rfl⟩)
        obtain ⟨b, hb1, -⟩ := Relation.TransGen.head'_iff.1 hD
        obtain ⟨d, hdA, hdy⟩ := hC'.par_slot _ _ hb1
        have hcd := hC'.cdt d hdA
        rw [hdy, hb1] at hcd
        by_cases hdW : d ∈ windowSlots dest r off.val win.val
        · exact hyd d hdW hdy.symm
        · rw [hcdtK d hdW] at hcd
          have hcd0 := hC.cdt d hdA
          rw [hdy, hcd] at hcd0
          exact hyG (hM.tree.par_mem _ _ hcd0.symm).1
  have hDL : DestLive Z.th (L.mem s) (L.ksb s) dest := by
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact DestLive.same (Or.inl ⟨y, rr, gs, g, hy, capV_of_capAt hcy⟩) (SlotsSame.refl _ _) rfl
  have hutc := J.ret_utcU (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => hDn0 d hd) hDu hcapK hwI hcdtK horgK hgp' hM'
    (RetExp.src_child hE hctx.window.1 hP' hC' hAs)
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- the spec's invariants and the call stacks (`uaRest`, nothing added)
  obtain ⟨hCR1, hRP1, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J.uaRest (Nn := ∅) hwI hA hIN hcnk (fun _ h => by simp at h)
  rw [Set.union_empty] at hNSC1
  have hSA1 := J.apart.sc_frame hwI.1 (uaSzKeep hA hIN hC2)
  have hspec1 : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases hDF _ hxG p sb fiv true (capV_of_capAt hcap1) ⟨rfl, trivial⟩ o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  -- the set and heap fields (`addSets`, nothing added)
  have hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ e ∈ (∅ : Set U64), e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ (∅ : Set U64), n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ (∅ : Set U64), r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧
        ∃ m, 12 ≤ m ∧ newKind nt.val us.val = some (.other m)) := by
    intro o ko hk
    rcases hkc o with e | ⟨r0, cs, cs', e1, e2⟩
    · exact Or.inl (e.symm.trans hk)
    · rw [e2] at hk; cases hk
      exact Or.inr (Or.inl ⟨r0, cs, cs', e1, rfl⟩)
  have harch1 : ArchFitHyp H σ := hAF
  obtain ⟨hKs', hIp', hnk', hcov', hobj', hzH', hset', hscC'⟩ :=
    J.addSets (Z' := { Z with G := G' }) (En := ∅) (Nn := ∅) (Rn := ∅) hwI.1 (by omega) hpfit hfree
      (by rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => by
        obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hwp
        rcases hDF _ hxG p sb fiv true (capV_of_capAt hcap) ⟨rfl, trivial⟩ o ko hk with (h | h) | ⟨h3, h4⟩ <;>
          omega) harch1 hA1 hA3 hE.k1 hout
      (fun _ h => by simp at h) (fun _ h => by simp at h) (fun _ h => by simp at h)
      (fun q _ kd hK => by rw [hK0] at hK; cases hK) hback rfl (Set.union_empty _).symm rfl rfl
      (Set.union_empty _).symm (Set.union_empty _).symm
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retypeU_dev J.sfree hDF J.ut hksz (capV_of_capAt hcap)
    hg1 (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) ht
  have hDF' : DevFreeT (L.mem res.2.1) G' σ' := SpecFreeP.retypeU hDF J.ut hksz (capV_of_capAt hcap)
    ⟨rfl, trivial⟩ hg1 (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) ht
  have hCs : JCs (L := L) { Z with G := G' } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun _ _ _ h => h) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with G := G' } H' Cs Ac' Lst
      {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1, hRF1, hRR1, hY1, hMc1, hBw1, hRP1, hSA1, ⟨_, _, hJPa⟩, hjc', K2, hutc, hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  -- the VSpace caps placed (`JAtZ.vsc`): an old cap kept or an untyped cap,
  -- a new cap (an untyped cap) set-free
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem res.2.1) := by
    obtain ⟨-, hCRZ, -, -, hMOZ, -, -⟩ := hX'.rel
    obtain ⟨P', L4', L3', L2', L1', hVI⟩ := hMOZ.2.2.1
    refine Vs.VsCapsW.slots (G := G') ?_ hCRZ.2.2.1
    intro x hx
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hu : isUt (capV (L.mem s) x) = true
      · exact Vs.vcapW_ut (hE.utk x hx0 hu)
      · rw [(hE.keep x hx0 (by simpa using hu)).2]
        exact J.vsc x ((hM.members x).1 hx0).1
    · have h1 := hVI _ hx
      rw [hE.newc j hj] at h1 ⊢
      have hT : Vs.SetFree (cj j) := by rw [hcj]; simp [cjOf, newCapOf, hnt, Vs.SetFree]
      exact (Vs.VCapOK.setFree hT h1).toW
  -- the buffer fields (`JBuf`): CNode slots changed only, the new caps untyped
  have hfk : IpcFrKeep σ σ' := IpcFrKeep.of_keepC hkc
  have hbf : JBuf (L := L) { Z with G := G' } res.2.1 σ' := by
    obtain ⟨-, hCRZ, -⟩ := hX'.rel
    exact ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.retype hE hM hCRZ.2.2.1 (fun _ => UFr.keep hfk.page)
      (fun j _ => by rw [hcj]; simp [cjOf, newCapOf, hnt, Vs.FrIn])⟩
  -- `LiveDN` and `zD` after (UtRetLive's `ret_liveN`)
  have hTH : P1.Heap.tcbs H' = P1.Heap.tcbs H :=
    tcbs_hout hout (newKind_ne_tcb (by omega)) hE.k1 hTb
  have hnewZ : ∀ q ∈ ZTcb (L := L) Z.th s,
      q ∈ {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} :=
    fun q hq => ⟨J.zD q hq, not_newQ_of_off hE.k1 (hTb q (J.zH.1 q (J.thT q (J.ztcb_tcb hq))))⟩
  have hWd : ∀ sl ∈ windowSlots dest r off.val win.val, ∃ p r', sl.1 = p.bv ∧ Z.th p = some (.cnode r') ∧
      sl.2.length = r' ∧ DestCap Z.th (L.mem s) p := fun sl hsl => by
    obtain ⟨-, i, -, -, rfl⟩ := hslA sl hsl
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact ⟨dest, r, rfl, hctx.cnode.1, natToCref_length _ _ (by have := hctx.cnode.2.1; omega),
      y, rr, gs, g, hy, capV_of_capAt hcy⟩
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveN hX' rfl rfl rfl (fun _ _ h => h) (NewEmpty.refl _ _ _) hTH
    (dbgKeep_of_writes J.blk hwI fun _ hb => J.inSlot_notDbg hb)
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ hC2.idle hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frame (Z' := { Z with G := G' }) rfl rfl rfl hwI.1 hX' hCs hJR
    hKs' J.thT hIp' hnk' hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hX'.rel.2.1.2.2.1 (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _), J.ext.vkeep (J.vkeep_slot hwI)⟩ hLvN hzDN
  -- `DevApart` after
  have hDA' : DevApart (L := L) Z.th H' G' Cs res.2.1 := by
    refine hDA.retype hE (fun p0 sb0 fi0 d0 h => ?_) hksR hidl hcjD (fun q kd hq => ?_) hDF'
    · rw [capV_of_capAt hcap] at h
      simp only [capability.Cap.Untyped.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hA1
    · have e := hout q
      rw [hq] at e
      by_cases hN : NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ (newKind nt.val us.val).isSome
      · rw [hK0] at hN; simp at hN
      · rw [if_neg hN] at e
        split_ifs at e
        exact Or.inl e.symm
  refine ⟨σ', hrun, hok, ⟨Z.th, G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX'.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', Lst, _, JZ, hDA', hDF'⟩


set_option maxHeartbeats 4000000 in
/-- **The no-reset retype from a device untyped at `J`** (module docstring;
as UtEpRet's `JAtZ.utEpJ`): from `JAtZ` at the decode with `DevApart` and
`DevFreeT` there, the source a CNode slot's device untyped cap, FL4's restart and `untyped::retype` of untypeds (type 0) or
frames (types 9, 10, 11) without a reset, or with the reset of an unused cap
(free index 0: FL4's and the spec's resets do nothing, `retype_reset_unused`,
`invokeUntyped_reset_unused`), end in `UtRetPostJ`. -/
theorem JAtZ.utDevJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 0 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi true nt us dest off win t r reset fiv)
    (hrs : reset = false ∨ fi.val = 0)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hDA : DevApart (L := L) Z.th H Z.G Cs s)
    (hDF : DevFreeT (L.mem s) Z.G σ) (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win true) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) true)
        res ⦄ := by
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  -- the restart (`JAtZ.restartJ`), then the body from its state
  obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, hDS1, -, hks1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : σ1.kheap (L.curW s).bv = some (.tcb { x1 with tcbState := .restart }) := by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hni1 : Entered σ1 :=
    ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact J.restart_keeps_resume hni hkx hcur⟩
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hctx1 : RetCtx (L := L) Z.th s1 σ1 (pp.bv, idx) sb fi true nt us dest off win t r reset fiv :=
    ⟨hctx.ty, hctx.size, ⟨hctx.cnode.1, hctx.cnode.2.1, hctx.cnode.2.2.1, by
        obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
        exact ⟨y, rr, gs, g, hy, (hSS1.capAt hy).trans hcy⟩⟩, hctx.window,
      fun i h1 h2 => (hSS1.capAt ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩).trans
        (hctx.empty i h1 h2),
      by rw [hσ1cdt]; exact hctx.resetEq, hctx.fidx, hctx.sizeBits, hctx.memory, hctx.device⟩
  have hBO1 : BufObjHyp Z.B σ1 := fun wp hw => by
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hw
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hkx] at hk; cases hk
      exact ⟨_, _, hσ1c, h1, by simpa [Fl4Spec.objBits] using h2⟩
    · exact ⟨o, ko, by rw [hσ1k o ho]; exact hk, h1, h2⟩
  have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hσ1c] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  -- the device facts after the restart, the region's free part dead (no `H` object meets it)
  have hcvK : ∀ x ∈ Z.G.chains.flatten, capV (L.mem s1) x = capV (L.mem s) x := fun x hx =>
    capV_of_capAt ((hSS1.capAt ((hM.members x).1 hx).1).trans (capAt_capV _ _))
  have hidK : IdleKeep (L := L) s s1 :=
    J.idleW_keep J1.xtop.fin.1.1.1 hid1 (by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl)
  have hDA1 : DevApart (L := L) Z.th H Z.G Cs s1 := by
    intro x hx p0 sb0 fi0 hc
    rw [hcvK x hx] at hc
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hDA x hx p0 sb0 fi0 hc
    have hnb : ∀ c, L.nodeBase s1 c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks1]
    refine ⟨a1, by rw [hks1]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks1]; exact a4,
      fun q hq => a5 q ?_, a6, a7, a8⟩
    unfold IdleAt at hq ⊢; rw [hidK.1, hidK.2] at hq; exact hq
  have hDF1 : DevFreeT (L.mem s1) Z.G σ1 := SpecFreeP.frame hDF
    (fun x hx p0 sb0 fi0 d hc => ⟨x, hx, fi0, by rw [← hcvK x hx]; exact hc, le_rfl⟩)
    (fun o ko h => by
      by_cases ho : o = (L.curW s).bv
      · subst ho; rw [hσ1c] at h; cases h; exact ⟨_, hkx, rfl⟩
      · exact ⟨ko, by rw [← hσ1k o ho]; exact h, rfl⟩)
  have hRU1 : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s1 ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s1 := by
    intro lo hi h1 h2
    refine hRU s1 hs1 lo hi (fun q kd hq hr => ?_)
    exfalso
    unfold RegionD MeetsR at hr
    rw [hq] at hr
    simp only [Option.elim] at hr
    exact meets_off hr h1 h2 ((hDA _ hxG p sb fi (capV_of_capAt hcap)).2.2.2.2.2.2.1 q kd hq |>.imp_right (Or.imp_right fun h => ⟨h.1, h.2.1⟩))
  have hfiv : fiv = fi := by
    rw [hctx.fidx]
    rcases hrs with rfl | h
    · rfl
    · cases reset
      · rfl
      · exact (UScalar.eq_of_val_eq (by rw [h]; rfl) : fi = 0#u64).symm
  have hbody : untyped.retype st arI s1 ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win true ⦃ res =>
      UtBodyPostD (L := L) arI AR σ1 (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) true)
        res ⦄ := by
    rcases hnt with h0 | hnt
    · exact J1.utUtDevBodyJ hni1 hpp hidx hcap1 h0 hc0 hctx1 hfiv hDA1 hDF1 hBO1 hAF1 hRU1
    · exact J1.utDevBodyJ hni1 hpp hidx hcap1 hnt hc0 hctx1 hfiv hDA1 hDF1 hBO1 hAF1 hRU1
  rw [hs1]; simp only [bind_ok]
  cases reset
  · exact WP.spec_mono hbody (fun res h => utRetPostJ_of_body hst1 h.post)
  · -- an unused cap: the reset does nothing on either side
    have hf0 : fi = 0#u64 := UScalar.eq_of_val_eq (by rw [hrs.resolve_left (by simp)]; rfl)
    subst hf0
    have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
        ({(.untypedCap true p.bv sb.val (0#u64 : U64).val, σ1)}, False) := by
      obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
        (by simpa [hidx] using hpp)
      rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
      rw [hg, hca.abs]; rfl
    rw [retype_reset_unused arI s1 ar _ _ nt us dest off win true hcap1]
    have hU0 := invokeUntyped_reset_unused Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv
      (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) true σ1 hg1
    refine WP.spec_mono hbody (fun res h => ?_)
    obtain ⟨σ', hrun, hok, hrel, hJ⟩ := h.post
    exact utRetPostJ_of_body hst1 ⟨σ', by rw [hU0]; exact hrun, hok, hrel, hJ⟩


end

end

end Fl4Proofs.P3
