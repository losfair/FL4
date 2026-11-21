/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of CNodes at `J`**
(`JAtZ.utCnJ`; handoff/utj.md "uttypes (line ut29-)", "(line ut31-)"; l4v
`invoke_untyped_corres` with `retype_region` of `CapTableObject`s).

`JAtZ.utEpJ`'s skeleton for type 4, with the typed heap grown: FL4's
`retype` (`retype_cont_all`) writes only slot words of the old heap (the new
caps); the window stays zero (`WinZero`), so the new CNodes' slots are empty.
The spec adds the window's CNodes (`emptyCnode`), then changes CNodes. No set
grows (the new CNodes are `H`'s `other (us + 5)` objects, in none of `Z`'s
sets); the typed heap grows to `th'` (`ThX`). The fields after:

* `XTopAt` by UtCnAdd's `XTopAt.addStepT` (the window's words read by no
  relation, `JAtZ.free_noObj`; `retExp_pml4_backG` for the TCBs' VSpace
  slots across the grown heap);
* the scheduler fields by `JAtZ.uaRest`/`JAtZ.addRP` at the old heap, then
  `Sched.SlotsApart.grow` (the window apart from `T`, the nodes, `N`, `C`'s
  SCs and `R`, all off the source cap's free part);
* `JPlaced`/`JCovD` by `JPlaced.retype`/`JAtZ.create_noreset` (already at
  `th'`); `JKern` by `kern_keep`, `JKern.grow`, `JKern.hout`;
* the untyped caps (`utc`): `JAtZ.ret_utc` at the old heap (the MDB after
  shrunk to it, `MdbLinks.shrink`: the window's slots are empty,
  `winSlot_null`), then `Sched.UtCapP3.growI` (each new CNode, a spec object
  after, is off every RAM untyped cap's free part by `SpecFree` after); a slot
  of a new CNode holds no untyped cap (`newSlot_null`);
* `JCs.retype` at `th'`, the sets and heap by `JAtZ.addSetsG` (the new
  CNodes in its CNode disjunct), put together by `JAtZ.add_frameT`
  (`thk_grow`, `thT_grow`, `DelBound.of_placed`, `IntLayout.grow`).
-/
import Fl4Proofs.P3.UtCnAdd
import Fl4Proofs.P3.UtRetLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section GrowI
variable {th th' : TypedHeap} {A k w n us : Nat}

/-- `ThX`'s cases with the new object's index. -/
theorem ThX.casesI (hT : ThX th th' A k w n us) {q : U64} {kd : ObjKind} (h : th' q = some kd) :
    th q = some kd ∨ ((∃ i, i < w ∧ q.val = A + i * k) ∧ thKindN n us = some kd) := by
  rw [hT.1 q] at h
  split_ifs at h with hc
  · exact Or.inr ⟨hc.1, h⟩
  · exact Or.inl h

/-- `RegionFree` at the grown heap, each new object off the region. -/
theorem RegionFree.growI {lo hi : Nat} (h : RegionFree th lo hi) (hT : ThX th th' A k w n us)
    (hW : ∀ q : U64, (∃ i, i < w ∧ q.val = A + i * k) → ∀ kd, thKindN n us = some kd →
      q.val + objSize kd ≤ lo ∨ hi ≤ q.val) :
    RegionFree th' lo hi := by
  intro q kd hq
  rcases hT.casesI hq with h1 | ⟨g1, g2⟩
  · exact h q kd h1
  · exact hW q g1 kd g2

/-- `NoStraddle` at the grown heap, no new object straddling the region. -/
theorem NoStraddle.growI {lo hi : Nat} (h : NoStraddle th lo hi) (hT : ThX th th' A k w n us)
    (hW : ∀ q : U64, (∃ i, i < w ∧ q.val = A + i * k) → ∀ kd, thKindN n us = some kd →
      (lo ≤ q.val ∧ q.val + objSize kd ≤ hi) ∨ q.val + objSize kd ≤ lo ∨ hi ≤ q.val) :
    NoStraddle th' lo hi := by
  intro q kd hq
  rcases hT.casesI hq with h1 | ⟨g1, g2⟩
  · exact h q kd h1
  · exact hW q g1 kd g2

/-- **A slot of the grown heap in the window is empty** when the window is
zero memory. -/
theorem winSlot_null (hP' : Placed th') {m : U64 → U64} {T : Prop} (hTn : ¬ T) (hWZ : WinZero m A k w T)
    {a : U64} (ha : IsSlot th' a) (h1 : A ≤ a.val) (h2 : a.val + 32 ≤ A + w * k) : capV m a = .Null := by
  have h8 : (wordOf a 8#u64).val = a.val + 8 := slot_word_val hP' ha (Or.inr (Or.inl rfl))
  have hal := IsSlot.align hP' ha
  have hz : ∀ v : U64, P1.Aligned v → A ≤ v.val → v.val < A + w * k → m v = 0#u64 := fun v hv1 hv2 hv3 =>
    (hWZ v hv1 hv2 hv3).resolve_right (fun h => hTn h.1)
  refine capV_zero (hz _ ?_ (by omega) (by omega)) (hz _ ?_ (by rw [h8]; omega) (by rw [h8]; omega))
  · unfold P1.Aligned; omega
  · unfold P1.Aligned; rw [h8]; omega

/-- **A slot of a new object is empty** when the window is zero memory. -/
theorem newSlot_null (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    (hP' : Placed th') {m : U64 → U64} {T : Prop} (hTn : ¬ T) (hWZ : WinZero m A k w T) {p : U64} {i : Nat}
    (hi : IsSlotAt th' p i) (hpn : th p = none) : capV m (slotOf p i) = .Null := by
  obtain ⟨kd, hkd, hsz⟩ := hi.size
  rcases hT.casesI hkd with h1 | ⟨⟨j, hj, hpj⟩, h2⟩
  · rw [hpn] at h1; cases h1
  have hk := hks kd h2
  have hjk : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hjk
  have hv := hi.val hP'
  exact winSlot_null hP' hTn hWZ ⟨p, i, hi, rfl⟩ (by omega) (by omega)

/-- **`MdbLinks` at a smaller heap** holding every slot with a cap. -/
theorem MdbLinks.shrink {m : U64 → U64} {G : MdbGhost} (h : MdbLinks th' m G)
    (hb : ∀ a, IsSlot th' a → capV m a ≠ .Null → IsSlot th a) (hf : ∀ a, IsSlot th a → IsSlot th' a) :
    MdbLinks th m G :=
  { h with
    members := fun a => ⟨fun ha => by
      obtain ⟨h1, c, hc, hn⟩ := (h.members a).1 ha
      refine ⟨hb a h1 ?_, c, hc, hn⟩
      rw [capAt_capV] at hc; rw [eq_of_ok_eq hc]; exact hn,
      fun ⟨h1, c, hc, hn⟩ => (h.members a).2 ⟨hf a h1, c, hc, hn⟩⟩ }

/-- `retExp_pml4_backT` across a retype that grows the typed heap. -/
theorem retExp_pml4_backG {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th' m' G')
    (hcj : ∀ j, j < w → ∀ p a, cj j ≠ .Pml4 p true a) {x p : U64} {asid : U64} (hxs : IsSlot th' x)
    (hx : capAt m' x = ok (.Pml4 p true asid)) : capAt m x = ok (.Pml4 p true asid) := by
  have hmem' : x ∈ G'.chains.flatten := (hM'.members x).2 ⟨hxs, _, hx, by simp⟩
  have hv' := capV_of_capAt hx
  rcases hE.gmem x hmem' with hx0 | ⟨j, hj, rfl⟩
  · obtain ⟨-, c, hc, -⟩ := (hM.members x).1 hx0
    have hv := capV_of_capAt hc
    cases hu : isUt (capV m x)
    · have e := (hE.keep x hx0 hu).2
      rw [hv', hv] at e
      rw [hc, ← e]
    · have e := hE.utk x hx0 hu
      rw [hv'] at e; cases e
  · have e := hE.newc j hj
    rw [hv'] at e
    exact absurd e.symm (hcj j hj _ _)

end GrowI

section GrowS
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th th' : TypedHeap} {A k w n us : Nat}

/-- **An untyped cap's facts at the grown heap**, each new object off the
cap's free part and not straddling its region (`Sched.UtCapP3.grow` per new
object). -/
theorem Sched.UtCapP3.growI {A' : Type} {arI : machine.Arch A'} {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64} (U : Sched.UtCapP3 (L := L) arI th s σ G sl p sb fi)
    (hT : ThX th th' A k w n us) (hk0 : 0 < k) (hpos : ∀ q kd, th q = some kd → 0 < objSize kd)
    (hWf : ∀ q : U64, (∃ i, i < w ∧ q.val = A + i * k) → ∀ kd, thKindN n us = some kd →
      q.val + objSize kd ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ q.val)
    (hWs : ∀ q : U64, (∃ i, i < w ∧ q.val = A + i * k) → ∀ kd, thKindN n us = some kd →
      (p.val ≤ q.val ∧ q.val + objSize kd ≤ p.val + 2 ^ sb.val) ∨ q.val + objSize kd ≤ p.val ∨
        p.val + 2 ^ sb.val ≤ q.val) :
    Sched.UtCapP3 (L := L) arI th' s σ G sl p sb fi :=
  { U with
    free := RegionFree.growI U.free hT hWf
    nostr := NoStraddle.growI U.nostr hT hWs
    rst := fun h1 h2 h3 => ⟨fun sl' ho => AbsSlot.restrictMono hT hk0 hpos ((U.rst h1 h2 h3).1 sl' ho),
      (U.rst h1 h2 h3).2⟩ }

end GrowS

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **The body of `JAtZ.utCnJ`: the CNode retype without a reset from a
`JAtZ` state** (handoff/utj.md Round 14; UtEpRet's `JAtZ.utEpBodyJ` for type
4, the typed heap grown by the new CNodes): FL4's `untyped::retype` with
`reset = false` from the state itself (after the restart, or after the
restart and the reset), against the spec's `invoke_untyped` without a reset
from `σ`: `UtBodyPost`. `RetCtx` at the state with any `reset` flag and
`fiv = fi`, `Entered`, the kept objects' references to a range in the cap's
free part (`hRU`). -/
theorem JAtZ.utCnBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 4) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ)
    (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      UtBodyPost (L := L) arI AR σ (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hBF : BufFreeHyp Z.B (L.mem s) Z.G := bufFree_of_obj J.sfree hBO
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hU := J.utc _ p sb fi false hAs hcap rfl
  have hnd : Sched.NotDev (L.mem s) (cslotAddr (pp.bv, idx)) p sb fi := Sched.notDev_ram (capV_of_capAt hcap)
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI0, -, hMO0, -⟩ := J.xtop.rel
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hty := hctx.ty
  have ht : t = .capTableObject := by
    have e := hty; rw [hnt] at e; simpa [objTypeOf] using e.symm
  have htU : t ≠ .untyped := by rw [ht]; simp
  have htP : t ≠ .archObject .pml4Obj := by rw [ht]; simp
  have htT : t ≠ .tcbObject := by rw [ht]; simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  subst hfiv
  have hz5 : zOf nt.val us.val = 5 + us.val := by simp [zOf, hnt]
  have hk32 : (2 : Nat) ^ zOf nt.val us.val = 32 * 2 ^ us.val := by rw [hz5, pow_add]; rfl
  -- no restart here: the state the body starts at
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb
    (by have := hctx.size.2.1; omega) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_body (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx hcap
    hU.pal hU.pfit hU.fiLe (hU.high hnd) hU.free (hU.zero hnd) Fl4Spec.fl4ObjBitsApi nt us dest off win t r hty
    (by omega) hctx.size.1 hctx.size.2.1 (fun h => by omega) (fun h h0 => hctx.size.2.2.1 ⟨h, h0⟩) hctx.cnode.1
    hctx.cnode.2.1 hctx.window.2.2 hctx.window.1 hctx.memory hctx.empty hb) (fun res hRP => ?_)
  have hRPN := RetPostB.toNB hRP
  obtain ⟨hok, har, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, Aw, k, w, dslot, cj,
    hE, hbr, hRFu⟩ := hRP
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, -, -, -, -, ⟨n0, hn0, hThX, uu, -, hcj⟩, -,
    hW, hWZ, -⟩
  · rw [hok] at e; cases e
  have hsR : sR = s ∧ thR = Z.th := by
    rcases hor with ⟨h1, h2, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h1, h2⟩
    · cases hRB
  obtain ⟨e2, e3⟩ := hsR
  subst sR
  subst thR
  have hn0v : n0 = nt.val := by
    rw [hnt]; have e := hn0; rw [ht] at e; exact objTypeOf_cnode e
  subst hn0v
  have hk0 : thKindN nt.val us.val = some (.cnode us.val) := by
    unfold thKindN; rw [if_neg (by omega), if_pos hnt]
  have hposZ : ∀ q kd, Z.th q = some kd → 0 < objSize kd := by
    intro q kd h
    rcases J.thk q kd h with rfl | ⟨r0, rfl⟩
    · simp [objSize]
    · simp only [objSize]; positivity
  -- FL4's writes: slot words of the old heap
  have hw : P1.WritesIn st s res.2.1 (Sched.SlotWd Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact Sched.slotSpan_wd hP hb h
    · exact absurd h1 htP))⟩
  -- the spec's outcome: the window's CNodes added, then CNodes changed
  have hSR1 := J.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  obtain ⟨-, σB, hA, hcnk, hkc⟩ := invokeUntyped_noreset_add Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ htU htP {pp.bv, dest.bv} (Or.inl rfl)
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Or.inr rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (by
      intro q hq
      rw [hlen] at hq
      obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      rw [hb] at hq ⊢
      have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have hfit := hU.pfit
      have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
      cases hq1 : σ.kheap (Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          (j * 2 ^ zOf nt.val us.val)) with
      | none => rfl
      | some ko =>
        exfalso
        obtain ⟨ko0, hko0, -⟩ := hksz _ _ hq1
        have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
        have h1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
        have hz1 := Nat.one_le_two_pow (n := zOf nt.val us.val)
        rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap) _ ko0 hko0 with h | ⟨h2, h3⟩
        · rw [hqv] at h; omega
        · rw [hqv] at h2 h3; omega)
    (.ok (), σ') (by rw [hrun]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∀ x n, Fl4Spec.defaultObject t false us.val σ.curDomain ≠ .schedContext x n := by
    intro q _ x n; rw [ht]; simp [Fl4Spec.defaultObject]
  have hcjne : ∀ j, j < w → ∀ p a, cj j ≠ .Pml4 p true a := by
    intro j _ p a
    rw [hcj]
    simp [cjOf, newCapOf, hnt]
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1
  have hcpuR : L.cpu res.2.1 = L.cpu s := hw.2.1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  have hfit := hU.pfit
  have hhigh := hU.high hnd
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, k2, -⟩ := J.jcov.ks _ hxG p sb fiv (capV_of_capAt hcap)
  obtain ⟨Q0, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  have hreg : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := by
    intro q hq
    obtain ⟨j, hj, e⟩ := hq
    rw [hlen, hb]
    unfold regionPtrs
    refine List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩
    have hjk : (j + 1) * 2 ^ (zOf nt.val us.val) ≤ win.val * 2 ^ (zOf nt.val us.val) := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    apply BitVec.eq_of_toNat_eq
    beta_reduce
    rw [ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (n := j * 2 ^ (zOf nt.val us.val))
      (by omega)]
    simp only [UScalar.bv_toNat]
    omega
  have hspecC : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), ∃ cs', σ'.kheap q.bv = some (.cnode us.val cs') := by
    intro q hq
    have hB := (hA.new _ (hreg q hq)).2
    rw [ht] at hB; simp only [Fl4Spec.defaultObject] at hB
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, e2⟩
    · exact ⟨_, e.trans hB⟩
    · rw [hB] at e1; cases e1; exact ⟨cs', e2⟩
  have hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    have hBk : σB.kheap q.bv = some (.schedContext y n) := by
      rcases hkc q.bv with e | ⟨r0, cs, cs', -, e2⟩
      · exact e.symm.trans hq
      · have e3 := e2.symm.trans hq; cases e3
    by_cases hWq : q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val)
    · rw [(hA.new _ hWq).2] at hBk
      rw [ht] at hBk; simp [Fl4Spec.defaultObject] at hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hWZ' : WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val (t = .tcbObject) := by
    have h0 := hWZ ⟨rfl, htP⟩
    rw [eA, ek, ew, hlen, hb] at h0
    exact h0
  have hTn : ¬ t = .tcbObject := htT
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th th' (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hreg hspecC hWZ' hA1 hA2 hA3
  have hk0' : 0 < 2 ^ zOf nt.val us.val := Nat.two_pow_pos _
  have hksk : ∀ kd, thKindN nt.val us.val = some kd → objSize kd ≤ 2 ^ zOf nt.val us.val := by
    rw [hk0]; intro kd h; cases h; simp only [objSize]; exact le_of_eq hk32.symm
  -- `XTopAt` after (`XTopAt.addStepT`: the window's words read by no relation)
  have hsc1 : ∀ (q : U64) y n, σ.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    obtain ⟨ko, hko, hty'⟩ := hksz _ _ hq
    exact ⟨ko, hko, objBits_of_aType_sc hty'⟩
  have hfr1 := J.free_noObj hAs hcap hBF rfl hsc1
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    exact retExp_pml4_backG hE hM hM' hcjne (IsSlot.thMono hThX hk0' hposZ hxs) hc
  have hX' := XTopAt.addStepT J.xtop hThX hksk hk0' hP' hposZ
    ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb (fun h => hn (Or.inl h))⟩
    (fun b g1 g2 => hfr1 b (by omega) (by omega))
    (by rcases k1 with h | h <;> omega)
    hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (hSt.okv hMO0) hTS
  -- the spec side
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_co Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ htU htP (.ok (), σ') (by rw [hrun]; rfl)
  have hC2 := CnStep.of_cnK hcnk
  have hctB : σB.curThread = σ.curThread := by
    have e := congrArg Fl4Spec.AbstractState.curThread hA.abs; exact e
  have hcscB : σB.curSc = σ.curSc := by
    have e := congrArg Fl4Spec.AbstractState.curSc hA.abs; exact e
  have hidB : σB.idleThread = σ.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hA.abs; exact e
  have hiscB : σB.idleSc = σ.idleSc := by
    have e := congrArg Fl4Spec.AbstractState.idleSc hA.abs; exact e
  have hgp' : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcnk.1
    exact e.trans (congrArg (fun a => a.x64GlobalPml4) hA.arch)
  have hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao) := fun q ao h => by
    have hB := hA.kold h
    rcases hkc q with e | ⟨r0, cs, cs', e1, -⟩
    · rw [e]; exact hB
    · rw [hB] at e1; cases e1
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
  have hidl : IdleKeep (L := L) s res.2.1 :=
    J.idleW_keep hX'.fin.1.1.1 (hC2.idle.trans hidB) (hC2.isc.trans hiscB)
  -- P1's creation: the heap after, `BlkOK`, `JCovD`
  have hcjU : ∀ j, j < win.val → isUt (cj j) = false := by
    intro j _; rw [hcj]; simp [cjOf, newCapOf, hnt, isUt]
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noresetB hni hpp hidx hcap hE
    (hRU _ _ hA1 hA3) (fun _ => hcjU) ⟨by omega, fun h => absurd h (by omega)⟩
    (k := 2 ^ zOf nt.val us.val) rfl hAk htT hW (fun _ => hWZ ⟨rfl, htP⟩) hidl
  -- `JPlaced` after
  have hcap1 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fiv false) := hcap
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap false p.bv sb.val fiv.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hgc : ∀ y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
        false)).run σ).1,
      ∀ o sz cs y0 n0, σ.kheap o = some (.cnode sz cs) → ¬ Fl4Spec.wellFormedCnodeN sz cs →
        y.2.kheap o ≠ some (.schedContext y0 n0) := by
    intro y hy o sz cs y0 n0 h0 _ hk
    rw [hrun] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    dsimp only at hk
    have hk' : σB.kheap o = some (.schedContext y0 n0) := by
      rcases hkc o with e | ⟨r0, cs0, cs', -, e2⟩
      · exact e.symm.trans hk
      · rw [e2] at hk; cases hk
    rcases hA.kback hk' with h1 | ⟨-, h2⟩
    · rw [h0] at h1; cases h1
    · rw [ht] at h2; simp [Fl4Spec.defaultObject] at h2
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, hhas2, hthx2, hJP2⟩ :=
    Sched.JPlaced.retypeG (L := L) hJp J.jcov J.ut hI hM hksz hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by simp [newKind, hnt] at h) (fun h => absurd h hn1) (fun h => absurd h hn1)
      J.kern.ksbAl J.kern.nodeFit (fun ct h => by rw [hc2] at h; cases eq_of_ok_eq h; exact J.kern.curT) J.intL
      J.sfree hgc (capV_of_capAt hcap) rfl hg1
      (fun _ => by rw [← eA]; exact hA1) (fun h => rfl) hidl.2
  have e1' : Aw = A2 := eA.trans eA2.symm
  have e2' : k2' = 2 ^ zOf nt.val us.val := by rw [ek2, hb]
  have e3' : w2 = win.val := by rw [ew2, hlen]
  subst e1' e2' e3'
  have hlohi : Aw = lo2 ∧ Aw + win.val * 2 ^ zOf nt.val us.val = hi2 := by
    rcases hor2 with h | ⟨-, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h.1.symm, h.2.symm⟩
    · cases hRB
  obtain ⟨rfl, rfl⟩ := hlohi
  have hth2 : th2 = th' := funext fun q => by rw [(hthx2 rfl).1 q, hThX.1 q]
  obtain ⟨y2, hy2, -, hKS⟩ := hhas2
  rw [hrun] at hy2
  obtain rfl := Set.mem_singleton_iff.1 hy2
  have hJPa := (hJP2 H' hout).of_kheap hKS.1
  rw [hth2] at hJPa
  -- `JKern` after
  have hDbg : L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hwI.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have K1 := J.kern_keep (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hwI.1 hwI.2.1
    hX'.fin.1.1.1 (hC2.ct.trans hctB) (hC2.csc.trans hcscB) horig hgp' hao hDbg
  have hRD := (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fiv, capV_of_capAt hcap⟩).1
  have hoffD : ∀ q kd, H q = some kd → q ∉ D → H' q = some kd := fun q kd hq hqD =>
    hout_old hout rfl rfl hE.k1 hq (by
      by_contra hm
      exact hqD (hRD q kd hq (by unfold MeetsW; omega)).1)
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have hcsR : L.cscW res.2.1 = L.cscW s :=
    cscW_of_sched J.xtop.fin.1.1.1 hX'.fin.1.1.1 hwI.1 hwI.2.1 (hC2.csc.trans hcscB)
  have hcscH : H' (L.cscW res.2.1) ≠ none := by
    rw [hcsR]
    obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 J.kern.cscH
    rw [hoffD _ kd hkd (J.cscLive.resolve_right hres)]; simp
  have hcurR : (L.curW res.2.1).val + 2 ^ 12 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ (L.curW res.2.1).val := by
    have := hU.free _ .tcb K1.curT; simp only [objSize] at this; omega
  have hTb : ∀ q, H q = some .tcb → q.val + 4096 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ q.val :=
    fun q hq => by
      have := hU.free q .tcb ((hJp.tcb q).2 hq); simp only [objSize] at this; omega
  have hnewK : ∀ q kd, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → newKind nt.val us.val = some kd →
      (q.val + 2 ^ kd.bits ≤ (L.ksb res.2.1).val ∨ (L.ksb res.2.1).val + 13568 ≤ q.val) ∧
      ∀ c ∈ Cs, q.val + 2 ^ kd.bits ≤ L.nodeBase res.2.1 c ∨ L.nodeBase res.2.1 c + 4288 ≤ q.val := by
    intro q kd hq hK
    obtain ⟨j, hj, hqv⟩ := hq
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hbk : 2 ^ kd.bits = 2 ^ zOf nt.val us.val := by rw [newKind_bits hK]
    have hnb : ∀ c, L.nodeBase res.2.1 c = L.nodeBase s c := fun c => by
      simp only [P1.LawfulStore.nodeBase, hksR]
    refine ⟨?_, fun c hc => ?_⟩
    · rw [hksR, hbk]; rcases k1 with h | h <;> omega
    · rw [hnb, hbk]; rcases k2 c hc with h | h <;> omega
  have hA0 : 0 < Aw := by omega
  have K1g := K1.grow hThX hksk hk0' hposZ hP'
    (by rw [P1.nodeAt_of_ksb hksR, hcpuR]; rintro ⟨g1, g2⟩; exact (hU.actZ hnd) ⟨by omega, by omega⟩)
    (by rw [P1.nodeAt_of_ksb hksR]; rintro ⟨g1, g2⟩; exact (hU.dwReg hnd) ⟨by omega, by omega⟩)
  have K2 := K1g.hout (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hJPa.heap hout hE.k1 hA0
    hnewK hcurR hcscH
  -- the untyped caps' facts after
  have hthM : ∀ a, IsSlot Z.th a → IsSlot th' a := fun a ha => IsSlot.thMono hThX hk0' hposZ ha
  obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1u, -, hAf1, -, -, -⟩ := hE.usrc
  rw [capV_of_capAt hcap] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp0, hsb0, hfi0, hd0⟩ := e0
  subst p0 sb0 fi0 d0
  have hsrcG' : cslotAddr (pp.bv, idx) ∈ G'.chains.flatten :=
    (hM'.members _).2 ⟨hthM _ hAs.isSlot, _, capAt_capV _ _, by rw [e1u]; simp⟩
  have hfi1 : fi1.val ≤ 2 ^ sb.val := hU'.fib _ hsrcG' p sb fi1 false e1u
  have hDn0 : ∀ d ∈ windowSlots dest r off.val win.val, capAt (L.mem s) (cslotAddr d) = ok .Null := by
    intro d hd
    obtain ⟨-, i, h1, h2, rfl⟩ := hslA d hd
    rw [cslotAddr_natToCref _ _ _ (by have := hctx.cnode.2.1; omega) (by have := hctx.window.2.2; omega)]
    exact hctx.empty i h1 h2
  have hnull0 : ∀ d ∈ windowSlots dest r off.val win.val, cslotAddr d ∉ Z.G.chains.flatten := fun d hd h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hDn0 d hd] at h0; exact hn (eq_of_ok_eq h0).symm
  have hDu : ∀ d ∈ windowSlots dest r off.val win.val, ∀ p1 sb1 fi2 dv,
      capV (L.mem res.2.1) (cslotAddr d) ≠ .Untyped p1 sb1 fi2 dv := by
    intro d hd p1 sb1 fi2 dv e
    have hm : cslotAddr d ∈ G'.chains.flatten :=
      (hM'.members _).2 ⟨hthM _ (hslA d hd).1.isSlot, _, capAt_capV _ _, by rw [e]; simp⟩
    rcases hE.gmem _ hm with h0 | ⟨j, hj, ej⟩
    · exact hnull0 d hd h0
    · rw [ej] at e
      have h3 := (hE.newc j hj).symm.trans e
      have h2 := hcjU j hj
      rw [h3, isUt_untyped] at h2; cases h2
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
      have hm : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hthM _ hy, _, capAt_capV _ _, hn⟩
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
          have hdA0 : AbsSlot Z.th d := by
            cases hq : σ.cdt d with
            | none => rw [hq] at hcd; cases hcd
            | some q0 => exact (hC.cdt_slot d q0 hq).1
          have hcd0 := hC.cdt d hdA0
          rw [hdy, hcd] at hcd0
          exact hyG (hM.tree.par_mem _ _ hcd0.symm).1
  have hDL : DestLive Z.th (L.mem s) (L.ksb s) dest := by
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact DestLive.same (Or.inl ⟨y, rr, gs, g, hy, capV_of_capAt hcy⟩) (SlotsSame.refl _ _) rfl
  have hM'Z : MdbLinks Z.th (L.mem res.2.1) G' := hM'.shrink (fun a ha hn => by
      rcases IsSlot.thX hThX hksk hP' ha with h | ⟨g1, g2⟩
      · exact h
      · exact absurd (winSlot_null hP' hTn hWZ' ha g1 g2) hn) hthM
  have hutc := J.ret_utc (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => hDn0 d hd) hDu hcapK hwI hcdtK horgK hgp' hM'Z
    (RetExp.src_child hE hctx.window.1 hP' hC' (AbsSlot.thMono hThX hk0' hposZ hAs))
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- `SpecFree` after, then the untyped caps at the grown heap
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd
    rw [hb, hz5, ht]
    simp only [Fl4Spec.defaultObject, Fl4Spec.objBits, Fl4Spec.cteLevelBits]
    omega
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype J.sfree J.ut hksz (capV_of_capAt hcap) rfl hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have e32 : (2 : Nat) ^ (Fl4Spec.cteLevelBits + us.val) = 32 * 2 ^ us.val := by rw [pow_add]; rfl
  have hutc' : ∀ sl p1 sb1 fi2 dev, AbsSlot th' sl → capAt (L.mem res.2.1) (cslotAddr sl) = ok (.Untyped p1 sb1 fi2 dev) →
      dev = false → Sched.UtCapP3 (L := L) arI th' res.2.1 σ' G' sl p1 sb1 fi2 := by
    intro sl p1 sb1 fi2 dev hsl hc hd
    subst hd
    obtain ⟨q, i, hqi, hq1, he⟩ := hsl.at
    by_cases hq : Z.th q = none
    · exfalso
      have h0 := newSlot_null hThX hksk hP' hTn hWZ' hqi hq
      rw [he, capAt_capV, h0] at hc; have e := eq_of_ok_eq hc; cases e
    obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 hq
    have hAs0 : AbsSlot Z.th sl := by
      obtain ⟨p0, h1, h2⟩ := hsl
      have hp : p0 = q := P1.eq_of_bv (h1.symm.trans hq1)
      have e : th' p0 = Z.th p0 := by rw [hp, hThX.mono hk0' hposZ hkd, hkd]
      exact ⟨p0, h1, by rw [e] at h2; exact h2⟩
    have hx' : cslotAddr sl ∈ G'.chains.flatten := (hM'.members _).2 ⟨hsl.isSlot, _, hc, by simp⟩
    have hcv := capV_of_capAt hc
    have hfb : fi2.val ≤ 2 ^ sb1.val := hU'.fib _ hx' p1 sb1 fi2 false hcv
    have hobj : ∀ q0 : U64, (∃ j, j < win.val ∧ q0.val = Aw + j * 2 ^ zOf nt.val us.val) →
        (q0.val + 32 * 2 ^ us.val ≤ p1.val ∨ p1.val + 2 ^ sb1.val ≤ q0.val) ∨
        (p1.val ≤ q0.val ∧ q0.val + 32 * 2 ^ us.val ≤ p1.val + fi2.val) := by
      intro q0 hq0
      obtain ⟨cs', hk'⟩ := hspecC q0 hq0
      have := hSF' _ hx' p1 sb1 fi2 hcv _ _ hk'
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [e32] at this
      exact this
    refine (hutc sl p1 sb1 fi2 false hAs0 hc rfl).growI hThX hk0' hposZ (fun q0 hq0 kd0 hk => ?_)
      (fun q0 hq0 kd0 hk => ?_)
    · rw [hk0] at hk; cases hk; simp only [objSize]; rcases hobj q0 hq0 with (h | h) | h <;> omega
    · rw [hk0] at hk; cases hk; simp only [objSize]; rcases hobj q0 hq0 with (h | h) | h <;> omega
  -- the spec's invariants and the call stacks (`uaRest`, `addRP`)
  have hIN : IdleNew (fun q => q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val))
      (fun _ => Fl4Spec.defaultObject t false us.val σ.curDomain) := fun q _ => by
    rw [ht]; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
  obtain ⟨hCR1, -, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J.uaRest hwI hA hIN hcnk (Nn := ∅) (fun _ h => by simp at h)
  rw [Set.union_empty] at hNSC1
  have hspec0 : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  have hspec1 : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap1) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  obtain ⟨hRP1, hSA1⟩ := J.addRP hwI hA hIN hcnk (Nn := ∅) (Rn := ∅) (fun _ h => by simp at h) (by omega) hU.pfit
    hU.free hspec1 (fun _ h => by simp at h) (fun _ h => by simp at h) (fun _ h => by simp at h) (Or.inl rfl)
  rw [Set.union_empty, Set.union_empty] at hRP1 hSA1
  have hSA1' := hSA1.grow hThX hksk hP' (fun a g1 g2 => by
    refine ⟨fun t0 ht0 => ?_, ?_, fun n hn => ?_, fun sc _ x n hx => ?_, fun r0 hr0 => ?_⟩
    · have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
      have := hU.free t0 .tcb hth; simp only [objSize] at this; omega
    · rw [hnbR]; rcases k2c with h | h <;> omega
    · obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n hn
      have := hspec1 _ _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this; omega
    · obtain ⟨ko, hko, hbits⟩ := hsc sc x n hx
      have := hspec0 _ _ hko
      rw [hbits] at this; simp only [UScalar.bv_toNat] at this; omega
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r0 hr0
      have := hspec1 _ _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega)
  -- the set and heap fields (`addSetsG`)
  have hKn : ∀ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → ∀ kd, newKind nt.val us.val = some kd →
      (kd = .ep ∧ q ∈ (∅ : Set U64)) ∨ (kd = .ntfn ∧ q ∈ (∅ : Set U64)) ∨ (kd = .reply ∧ q ∈ (∅ : Set U64)) ∨
        ∃ m, kd = .other m := by
    intro q _ kd hK
    simp [newKind, hnt] at hK
    first | exact Or.inr (Or.inr (Or.inr ⟨_, hK.symm⟩)) | exact Or.inr (Or.inr (Or.inr ⟨_, hK⟩))
  have hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs', ko = .cnode r cs') ∨
      (∃ e ∈ (∅ : Set U64), e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ (∅ : Set U64), n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ (∅ : Set U64), r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧
        ∃ m, 12 ≤ m ∧ newKind nt.val us.val = some (.other m)) := by
    intro o ko hk
    rcases hkc o with e | ⟨r0, cs, cs', -, e2⟩
    · rcases hA.kback (e.symm.trans hk) with h1 | ⟨-, h2⟩
      · exact Or.inl h1
      · rw [ht] at h2; simp only [Fl4Spec.defaultObject] at h2
        exact Or.inr (Or.inl ⟨_, _, h2⟩)
    · rw [e2] at hk; cases hk; exact Or.inr (Or.inl ⟨r0, cs', rfl⟩)
  have harch1 : ArchFitHyp H σ := hAF
  obtain ⟨hKs', hIp', hnk', hcov', hobj', hzH', hset', hscC'⟩ :=
    J.addSetsG (Z' := { Z with th := th', G := G' }) (En := ∅) (Nn := ∅) (Rn := ∅) hwI.1 (by omega) hU.pfit hU.free
      (by rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => hBF wp hwp _ hxG p sb fiv (capV_of_capAt hcap)) harch1 hA1 hA3 hE.k1 hout
      (fun _ h => by simp at h) (fun _ h => by simp at h) (fun _ h => by simp at h) hKn
      hback rfl (Set.union_empty _).symm rfl rfl (Set.union_empty _).symm (Set.union_empty _).symm
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  have hCs : JCs (L := L) { Z with th := th', G := G' } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun p1 zt n1 h => by
      rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact Or.inl ⟨a, hThX.mono hk0' hposZ b, c⟩
      · exact Or.inr ⟨a, hThX.mono hk0' hposZ b, c⟩) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with th := th', G := G' } H' Cs Ac' Lst
      {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1, hRF1, hRR1, hY1, hMc1, hBw1, hRP1, hSA1', ⟨_, _, hJPa⟩, hjc', K2, hutc', hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  have hintL : IntLayout th' (L.ksb res.2.1) := by
    rw [hwI.1]
    exact IntLayout.grow J.intL hThX hksk hk0' hposZ (by rcases k1 with h | h <;> omega)
  -- the VSpace caps placed (`JAtZ.vsc`): an old cap kept or an untyped cap,
  -- a new cap (a CNode cap) set-free
  have hvc : Vs.VsSlotsW th' Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem res.2.1) := by
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
  -- the buffer fields (`JBuf`): fresh CNodes, then CNode slots; the new caps CNode caps
  have hfk : IpcFrKeep σ σ' :=
    (IpcFrKeep.of_specAdd hA (fun _ _ x e => by rw [ht] at e; cases e)
      (fun _ _ vms e => by rw [ht] at e; cases e)).trans (IpcFrKeep.of_keepC hkc)
  have hbf : JBuf (L := L) { Z with th := th', G := G' } res.2.1 σ' :=
    ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.retype hE hM hM' (fun _ => UFr.keep hfk.page)
      (fun j _ => by rw [hcj]; simp [cjOf, newCapOf, hnt, Vs.FrIn])⟩
  -- `LiveDN` and `zD` after (UtRetLive's `ret_liveN`; the new CNodes' slots empty)
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
  have hold : ∀ q kd, Z.th q = some kd → th' q = some kd := fun q kd h => hThX.mono hk0' hposZ h
  have hNE : NewEmpty Z.th th' (L.mem res.2.1) σ' := fun q hq i hqi => by
    refine ⟨newSlot_null hThX hksk hP' hTn hWZ' hqi hq, fun x hx => ?_⟩
    have hnA := not_absSlot_new hP' hold hq hqi hx
    by_cases hxW : x ∈ windowSlots dest r off.val win.val
    · exact absurd (hslA x hxW).1 hnA
    rw [horgK x hxW]
    cases ho : σ.isOriginalCap x
    · rfl
    · exact absurd (J.kern.orig x ho) hnA
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveN hX' rfl rfl rfl hold hNE hTH
    (dbgKeep_of_writes J.blk hwI fun _ hb => J.inSlot_notDbg hb)
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ (hC2.idle.trans hidB) hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frameT (Z' := { Z with th := th', G := G' }) rfl rfl hwI.1 hX' hCs hJR
    hKs' (fun t0 ht0 => J.thT t0 (thT_grow hThX hksk hn1 ht0)) (thk_grow hThX hksk J.thk)
    (DelBound.of_placed hP') hintL hIp' hnk' hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hM' (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _), fun t0 ht0 => J.ext.vkeep (J.vkeep_slot hwI) t0 (thT_grow hThX hksk hn1 ht0)⟩ hLvN hzDN
  refine ⟨σ', hrun, hok, ⟨th', G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX'.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', Lst, _, JZ⟩

set_option maxHeartbeats 4000000 in
/-- **The no-reset retype of CNodes at `J`** (module docstring; `JAtZ.utEpJ`'s
skeleton, one core, `Z.c = 0`): from `JAtZ` at the decode (no reschedule
pending), the decoded arguments (`RetCtx`, no reset: the source cap has a
child), the source a CNode slot's RAM untyped cap, FL4's restart and
`untyped::retype` of CNodes end in `UtRetPostJ` (done, `JAt` after at the
same sets, the typed heap grown by the new CNodes). -/
theorem JAtZ.utCnJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 4) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r false fiv)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  -- the restart (`JAtZ.restartJ`), then the body from its state
  obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, -, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : σ1.kheap (L.curW s).bv = some (.tcb { x1 with tcbState := .restart }) := by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hni1 : Entered σ1 :=
    ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact J.restart_keeps_resume hni hkx hcur⟩
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hctx1 : RetCtx (L := L) Z.th s1 σ1 (pp.bv, idx) sb fi false nt us dest off win t r false fiv :=
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
  have hRU1 : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s1 ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s1 :=
    fun lo hi h1 h2 => hRU s1 hs1 lo hi (J.free_dead hxG (capV_of_capAt hcap) h1 h2)
  have hfiv : fiv = fi := by rw [hctx.fidx]; rfl
  rw [hs1]; simp only [bind_ok]
  exact WP.spec_mono (J1.utCnBodyJ hni1 hpp hidx hcap1 hnt hc0 hctx1 hfiv hBO1 hAF1 hRU1)
    (fun res h => utRetPostJ_of_body hst1 h)

end

end

end Fl4Proofs.P3
