/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of PML4s at `J`**
(`JAtZ.utPmJ`; handoff/utj.md "uttypes (line ut22-)"; l4v
`invoke_untyped_corres` with `init_arch_objects`' `copy_global_mappings`).

`JAtZ.utEpJ`'s skeleton for type 8: FL4's `retype` (`retype_cont_pml4R`)
writes slot words and the window (each new PML4's kernel half,
`copy_global_mappings`); the spec adds the window's PML4s, each with the
global mappings copied in (`invokeUntyped_noreset_pml4`), then changes
CNodes. `XTopAt` by `XTopAt.addStepW` (the window's words read by no
relation, UtPmAdd), then `XTopAt.addPml4` puts the new PML4s into `L4` (their
caps are unassigned, `JAtZ.vsc` asks them there; a new PML4's user half is
zero in FL4, `retype_cont_pml4R`, and empty in the spec,
`invokeUntyped_noreset_pml4`). The
scheduler and untyped-cap fields across the window writes by UtPmKeep's
`uaRestW`, `addRPW`, `ret_utcW`; P1's creation by `JAtZ.create_noresetW`
(the window's words in new `other 12` objects, which P1 does not track).
-/
import Fl4Proofs.P3.UtPmKeep
import Fl4Proofs.P3.UtTabAdd
import Fl4Proofs.P3.UtRetLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem objTypeOf_pml4 {n : Nat} (h : objTypeOf n = some (.archObject .pml4Obj)) : n = 8 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

set_option maxHeartbeats 16000000 in
/-- **The body of `JAtZ.utPmJ`: the retype of PML4s without a reset from a
`JAtZ` state** (handoff/utj.md Round 13; as UtEpRet's `JAtZ.utEpBodyJ`). -/
theorem JAtZ.utPmBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 8) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
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
  have ht : t = .archObject .pml4Obj := by
    have e := hty; rw [hnt] at e; simpa [objTypeOf, Fl4Spec.archDataToObjType] using e.symm
  have htU : t ≠ .untyped := by rw [ht]; simp
  have htT : t ≠ .tcbObject := by rw [ht]; simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  subst hfiv
  -- no restart here: the state the body starts at
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by simp [zOf, hnt]) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_body_pml4 (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx
    hcap hU.pal hU.pfit hU.fiLe (hU.high hnd) hU.free (hU.zero hnd) Fl4Spec.fl4ObjBitsApi nt us dest off win t r hty
    hnt hctx.size.1 hctx.cnode.1 hctx.cnode.2.1 hctx.window.2.2 hctx.window.1 hctx.memory hctx.empty hb
    J.kern.gpm J.kern.ga J.kern.gf (hU.gReg hnd)) (fun res ⟨hRP, hUZ⟩ => ?_)
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
    rw [hnt]; have e := hn0; rw [ht] at e; exact objTypeOf_pml4 e
  subst hn0v
  have hk0 : thKindN nt.val us.val = none := by
    unfold thKindN; rw [if_neg (by omega), if_neg (by omega)]
  have hth : th' = Z.th := funext fun q => by rw [hThX.1 q, hk0]; simp
  subst hth
  -- FL4's writes: slot words and the window (the new PML4s' kernel half)
  have hw : P1.WritesIn st s res.2.1 (fun b => Sched.SlotWd Z.th b ∨ (Aw ≤ b.val ∧ b.val < Aw + w * k)) :=
    ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨-, h⟩
    · exact absurd h1 htT
    · exact Or.inl (Sched.slotSpan_wd hP hb h)
    · exact Or.inr h))⟩
  -- the spec's outcome: the window's objects added, then CNodes changed
  have hSR1 := J.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hzW : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  have hal : ∀ q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val),
      q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64 := by
    intro q hq
    rw [hlen] at hq
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
    rw [← ht, hb] at hq ⊢
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hfit := hU.pfit
    have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
    rw [hqv]
    rw [hzW] at hjk hA2 hA3 ⊢
    simp only [Nat.reducePow] at hjk hA2 hA3 ⊢
    constructor <;> omega
  have hrunP := hrun
  rw [ht] at hrunP
  obtain ⟨-, σB, oo, hA, hpm, hcnk, hkc⟩ := invokeUntyped_noreset_pml4 Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ us.val
    (windowSlots dest r off.val win.val) false σ {pp.bv, dest.bv} (Or.inl rfl)
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
      rw [← ht, hb] at hq ⊢
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
    hal
    J.kern.gpm J.kern.ga J.kern.gf
    (.ok (), σ') (by rw [hrunP]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val) →
      ∀ x n, oo q ≠ .schedContext x n := by
    intro q hq x n e; obtain ⟨pt, e', -⟩ := hpm q hq; rw [e'] at e; cases e
  have hcjne : ∀ j, j < w → ∀ p a, cj j ≠ .Pml4 p true a := by
    intro j _ p a
    rw [hcj]
    simp [cjOf, newCapOf, hnt]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    exact retExp_pml4_backT hE hM hM' hcjne hxs hc
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  have hfit := hU.pfit
  have hhigh := hU.high hnd
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, k2, -⟩ := J.jcov.ks _ hxG p sb fiv (capV_of_capAt hcap)
  obtain ⟨Q0, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  have hwb : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), p.val + fiv.val ≤ q.val ∧ q.val + 2 ^ (zOf nt.val us.val) ≤ p.val + 2 ^ sb.val ∧ q.val % 2 ^ (zOf nt.val us.val) = 0 := by
    intro q hq
    obtain ⟨b1, b2, b3⟩ := winSet_bd hq
    exact ⟨by omega, by omega, b3 hA2⟩
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
  have hspec : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), σ'.kheap q.bv = some (oo q.bv) := by
    intro q hq
    have hB := (hA.new _ (by rw [← ht]; exact hreg q hq)).2
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, -⟩
    · exact e.trans hB
    · have e2 := hB.symm.trans e1
      obtain ⟨pt, e', -⟩ := hpm _ (by rw [← ht]; exact hreg q hq)
      rw [e'] at e2; cases e2
  have hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    have hBk : σB.kheap q.bv = some (.schedContext y n) := by
      rcases hkc q.bv with e | ⟨r0, cs, cs', -, e2⟩
      · exact e.symm.trans hq
      · have e3 := e2.symm.trans hq; cases e3
    by_cases hWq : q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val)
    · rw [(hA.new _ hWq).2] at hBk
      obtain ⟨pt, e', -⟩ := hpm _ hWq
      rw [e'] at hBk; cases hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hfr0 := J.free_noObj hAs hcap hBF hksR hsc
  have hTT : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), ∀ t0 ∈ Z.T, t0.val + 4096 ≤ q.val ∨ q.val + 2 ^ (zOf nt.val us.val) ≤ t0.val := by
    intro q hq t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    obtain ⟨b1, b2, -⟩ := hwb q hq
    simp only [objSize] at this; omega
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th Z.th (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hwb hreg hspec hTT hA1 hA2 hA3 hUZ
  -- `XTopAt` after (`XTopAt.addStepW`: the window's words read by no relation)
  have hsc1 : ∀ (q : U64) y n, σ.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    obtain ⟨ko, hko, hty'⟩ := hksz _ _ hq
    exact ⟨ko, hko, objBits_of_aType_sc hty'⟩
  have hfr1 := J.free_noObj hAs hcap hBF rfl hsc1
  have hX' := XTopAt.addStepW J.xtop hw
    (fun b ⟨g1, g2⟩ => hfr1 b (by omega) (by omega))
    (fun b ⟨g1, g2⟩ => by rcases k1 with h | h <;> omega)
    hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (hSt.okv hMO0) hTS
  -- no set grows (the new PML4s are in none of the sets)
  obtain ⟨En, Nn, Rn, hXZ, hEs, hNs, hRs, hEt, hNt, hRt, hWEN⟩ : ∃ En Nn Rn : Set U64,
      XTopAt (L := L) AR { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 ar σ' ∧
      En ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ Nn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      Rn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      (∀ e ∈ En, nt.val = 2) ∧ (∀ n ∈ Nn, nt.val = 3) ∧ (∀ r ∈ Rn, nt.val = 6) ∧
      ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∈ En ∨ q ∈ Nn ∨ q ∈ Rn ∨ nt.val = 8 := by
    refine ⟨∅, ∅, ∅, ?_, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => Or.inr (Or.inr (Or.inr hnt))⟩
    simp only [Set.union_empty]
    exact hX'
  -- the spec side
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_coP Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ us.val
    (windowSlots dest r off.val win.val) false σ {pp.bv, dest.bv} (Or.inl rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (fun q hq => by
      have hB := (hA.new q hq).1
      exact hB)
    (fun q hq => hal q hq)
    J.kern.gpm J.kern.ga J.kern.gf (.ok (), σ') (by rw [hrunP]; rfl)
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ.kheap o = σ.kheap o := fun _ _ => rfl
  have hσ1c : ∃ y, σ.kheap (L.curW s).bv = some (.tcb y) := by
    obtain ⟨-, x, hx, -⟩ := J.curRunnable hni hc2; exact ⟨x, hx⟩
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
  have hwI : P1.WritesIn st s res.2.1 (fun b => InSlot Z.th b ∨
      (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val)) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨-, h⟩
    · exact absurd h1 htT
    · exact Or.inl h
    · exact Or.inr h))⟩
  have hidl : IdleKeep (L := L) s res.2.1 :=
    J.idleW_keep hX'.fin.1.1.1 (hC2.idle.trans hidB) (hC2.isc.trans hiscB)
  -- P1's creation: the heap after, `BlkOK`, `JCovD`
  have hcjU : ∀ j, j < win.val → isUt (cj j) = false := by
    intro j _; rw [hcj]; simp [cjOf, newCapOf, hnt, isUt]
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noresetB hni hpp hidx hcap hE (hRU _ _ hA1 hA3)
    (fun _ => hcjU) ⟨by omega, fun h => absurd h (by omega)⟩ (k := 2 ^ zOf nt.val us.val) rfl hAk htT hW
    (fun hz => absurd (by simp [newKind, hnt]) (hz 12)) hidl
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
    rcases hA.kback hk' with h1 | ⟨hW', h2⟩
    · by_cases ho : o = (L.curW s).bv
      · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h1; cases h1
      · rw [h0] at h1; cases h1
    · obtain ⟨pt, e', -⟩ := hpm _ hW'
      rw [e'] at h2; cases h2
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
  have hth2 : th2 = Z.th := funext fun q => by rw [(hthx2 rfl).1 q, hk0]; simp
  subst hth2
  obtain ⟨y2, hy2, -, hKS⟩ := hhas2
  rw [hrun] at hy2
  obtain rfl := Set.mem_singleton_iff.1 hy2
  have hJPa := (hJP2 H' hout).of_kheap hKS.1
  -- `JKern` after
  have hWd : ¬ (Aw ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < Aw + win.val * 2 ^ zOf nt.val us.val) := by
    rintro ⟨g1, g2⟩
    exact hU.dwReg hnd ⟨by omega, by omega⟩
  have hDbg : L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hwI.mem_eq J.kern.dwAl fun h => h.elim (fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩) hWd
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
  have K2 := K1.hout (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hJPa.heap hout hE.k1 hA0 hnewK hcurR hcscH
  -- the untyped caps' facts after
  obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1u, -, hAf1, -, -, -⟩ := hE.usrc
  rw [capV_of_capAt hcap] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp0, hsb0, hfi0, hd0⟩ := e0
  subst p0 sb0 fi0 d0
  have hsrcG' : cslotAddr (pp.bv, idx) ∈ G'.chains.flatten :=
    (hM'.members _).2 ⟨hAs.isSlot, _, capAt_capV _ _, by rw [e1u]; simp⟩
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
      (hM'.members _).2 ⟨(hslA d hd).1.isSlot, _, capAt_capV _ _, by rw [e]; simp⟩
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
  have hutc := J.ret_utcW (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => hDn0 d hd) hDu hcapK hwI
    (fun b ⟨_, g2⟩ => by omega)
    (fun sl1 p1 sb1 fi2 hsl1 hne hcv1 b ⟨g1, g2⟩ => by
      have hm1 : cslotAddr sl1 ∈ Z.G.chains.flatten :=
        (J.xtop.rel.2.1.2.2.1.members _).2 ⟨hsl1.isSlot, _, capAt_capV _ _, by rw [hcv1]; simp⟩
      have hs1G : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
        (J.xtop.rel.2.1.2.2.1.members _).2 ⟨hAs.isSlot, _, hcap1, by simp⟩
      exact ut_free_other J.ut hm1 hs1G hne hcv1 (capV_of_capAt hcap1) (b := b.val) (by omega) (by omega))
    hWd hcdtK horgK hgp' hM'
    (RetExp.src_child hE hctx.window.1 hP' hC' hAs)
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- the spec's invariants and the call stacks (`uaRest`, `addRP`)
  have hIN : IdleNew (fun q => q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val))
      oo := fun q hq => by
    obtain ⟨pt, e, -⟩ := hpm q hq
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, e⟩)))
  have hWnN : ∀ n ∈ Nn, n.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi (.archObject .pml4Obj) us.val) :=
    fun n hn => by rw [← ht]; exact hreg n (hNs hn)
  -- the window's words apart from the scheduler's (`T`, `C`'s SCs, `R`)
  have hWT : ∀ b : U64, (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val) → ∀ t0 ∈ Z.T,
      b.val < t0.val ∨ t0.val + 4096 ≤ b.val := by
    rintro b ⟨g1, g2⟩ t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    simp only [objSize] at this; omega
  have hspec1' : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap1) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  have hWC : ∀ b : U64, (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val) → ∀ q ∈ Z.C, ∀ x n,
      σ.kheap q.bv = some (.schedContext x n) → b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val := by
    rintro b ⟨g1, g2⟩ q hq x n hx
    have := hspec1' _ _ hx
    simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
    rw [Nat.add_comm n]; omega
  have hWR : ∀ b : U64, (Aw ≤ b.val ∧ b.val < Aw + win.val * 2 ^ zOf nt.val us.val) → ∀ r0 ∈ Z.R,
      b.val < r0.val ∨ r0.val + 32 ≤ b.val := by
    rintro b ⟨g1, g2⟩ r0 hr0
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r0 hr0
    have := hspec1' _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  obtain ⟨hCR1, -, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J.uaRestW hwI hWT hWC hWR hA hIN hcnk hWnN
  have hspec1 : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap1) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  have hNw0 : ∀ n ∈ Nn, n.val % 64 = 0 ∧ p.val + fiv.val ≤ n.val ∧ n.val + 64 ≤ p.val + 2 ^ sb.val ∧
      NewAt Aw (2 ^ zOf nt.val us.val) win.val n ∧ newKind nt.val us.val = some .ntfn := by
    intro n hn
    have h3 := hNt n hn
    have h64 : (2 : Nat) ^ zOf nt.val us.val = 64 := by simp [zOf, h3]
    obtain ⟨b1, b2, b3⟩ := hwb n (hNs hn)
    rw [h64] at b2 b3
    exact ⟨b3, b1, b2, hNs hn, by simp [newKind, h3]⟩
  have hEw0 : ∀ e ∈ En, e.val % 16 = 0 ∧ p.val + fiv.val ≤ e.val ∧ e.val + 16 ≤ p.val + 2 ^ sb.val ∧
      NewAt Aw (2 ^ zOf nt.val us.val) win.val e ∧ newKind nt.val us.val = some .ep := by
    intro e he
    have h2 := hEt e he
    have h16 : (2 : Nat) ^ zOf nt.val us.val = 16 := by simp [zOf, h2]
    obtain ⟨b1, b2, b3⟩ := hwb e (hEs he)
    rw [h16] at b2 b3
    exact ⟨b3, b1, b2, hEs he, by simp [newKind, h2]⟩
  have hRw0 : ∀ r ∈ Rn, r.val % 32 = 0 ∧ p.val + fiv.val ≤ r.val ∧ r.val + 32 ≤ p.val + 2 ^ sb.val ∧
      NewAt Aw (2 ^ zOf nt.val us.val) win.val r ∧ newKind nt.val us.val = some .reply := by
    intro r hr
    have h6 := hRt r hr
    have h32 : (2 : Nat) ^ zOf nt.val us.val = 32 := by simp [zOf, h6]
    obtain ⟨b1, b2, b3⟩ := hwb r (hRs hr)
    rw [h32] at b2 b3
    exact ⟨b3, b1, b2, hRs hr, by simp [newKind, h6]⟩
  -- the new replies: free, zero links, not old ones
  have hkR : ∀ r ∈ Rn, σ'.kheap r.bv = some (.reply Fl4Spec.defaultReply) := by
    intro r hr
    exfalso; have := hRt r hr; omega
  have hRz : ∀ r ∈ Rn, L.mem res.2.1 (P1.rNextA r) = 0#u64 ∧ L.mem res.2.1 (P1.rPrevA r) = 0#u64 := by
    intro r hr
    exfalso; have := hRt r hr; omega
  have hRn : ∀ r ∈ Rn, r ∉ Z.R := by
    intro r hr hrR
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hrR
    have := hspec1 _ _ hx
    obtain ⟨-, b1, b2, -⟩ := hRw0 r hr
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  have hnb0 : L.nodeBase s Z.c = (L.ksb s).val + 13568 := by
    unfold P1.LawfulStore.nodeBase; rw [hc0]; simp
  have hRks : ∀ r ∈ Rn, r.val + 32 ≤ (L.ksb res.2.1).val ∨ L.nodeBase res.2.1 Z.c + 4288 ≤ r.val := by
    intro r hr
    obtain ⟨-, b1, b2, -⟩ := hRw0 r hr
    have k2' := k2c
    rw [hnb0] at k2'
    rw [hnbR, hnb0, hksR]
    rcases k1 with h | h <;> rcases k2' with h' | h' <;> omega
  have hNR : Nn = ∅ ∨ Rn = ∅ := by
    rcases Set.eq_empty_or_nonempty Nn with h | ⟨n, hn⟩
    · exact Or.inl h
    · refine Or.inr (Set.ext fun r => ⟨fun hr => ?_, fun h => False.elim h⟩)
      exfalso; have := hNt n hn; have := hRt r hr; omega
  obtain ⟨hRP1, hSA1⟩ := J.addRPW hwI hWT hWC hWR hA hIN hcnk hWnN (by omega) hU.pfit hU.free hspec1
    (fun n hn => ⟨(hNw0 n hn).2.1, (hNw0 n hn).2.2.1⟩) (fun r hr => ⟨(hRw0 r hr).1, (hRw0 r hr).2.1,
      (hRw0 r hr).2.2.1⟩) hRks hNR
  -- the set and heap fields (`addSets`)
  have hKn : ∀ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → ∀ kd, newKind nt.val us.val = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) ∨ (kd = .reply ∧ q ∈ Rn) ∨ ∃ m, kd = .other m := by
    intro q hq kd hK
    rcases hWEN q hq with h | h | h | ha
    · have h2 := hEt q h; simp [newKind, h2] at hK; exact Or.inl ⟨hK.symm, h⟩
    · have h3 := hNt q h; simp [newKind, h3] at hK; exact Or.inr (Or.inl ⟨hK.symm, h⟩)
    · have h6 := hRt q h; simp [newKind, h6] at hK; exact Or.inr (Or.inr (Or.inl ⟨hK.symm, h⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨12, ?_⟩))
      simp [newKind, ha] at hK; first | exact hK.symm | exact hK
  have hrev : ∀ o, o ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∃ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q.bv = o := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem ho
    rw [hlen] at hj
    rw [hb]
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hfit := hU.pfit
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    refine ⟨⟨Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (j * 2 ^ zOf nt.val us.val)⟩,
      ⟨j, hj, ?_⟩, rfl⟩
    show (Fl4Spec.ptrAdd _ _).toNat = _
    rw [ptrAdd_toNat (by omega), ← eA]
  have hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧
        ∃ m, 12 ≤ m ∧ newKind nt.val us.val = some (.other m)) := by
    intro o ko hk
    have hback1 : ∀ ko', σB.kheap o = some ko' → σ.kheap o = some ko' ∨
        (∃ e ∈ En, e.bv = o ∧ ko' = .endpoint Fl4Spec.defaultEp) ∨
        (∃ n ∈ Nn, n.bv = o ∧ ko' = .notification Fl4Spec.defaultNotification) ∨
        (∃ r ∈ Rn, r.bv = o ∧ ko' = .reply Fl4Spec.defaultReply) ∨
        (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧ (∃ ao, ko' = .archObj ao) ∧
        ∃ m, 12 ≤ m ∧ newKind nt.val us.val = some (.other m)) := by
      intro ko' h
      rcases hA.kback h with h1 | ⟨hW', h2⟩
      · exact Or.inl h1
      · obtain ⟨q, hq, hqo⟩ := hrev o (by rw [ht]; exact hW')
        rcases hWEN q hq with hqE | hqN | hqR | ha
        · exfalso; have := hEt q hqE; omega
        · exfalso; have := hNt q hqN; omega
        · exfalso; have := hRt q hqR; omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hq, hqo, ?_, ⟨12, le_rfl, by simp [newKind, ha]⟩⟩)))
          obtain ⟨pt, e, -⟩ := hpm o hW'
          exact ⟨_, by rw [h2, e]⟩
    rcases hkc o with e | ⟨r0, cs, cs', e1, e2⟩
    · rcases hback1 ko (e.symm.trans hk) with h1 | h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    · rw [e2] at hk; cases hk
      rcases hback1 _ e1 with h1 | ⟨e, -, -, he⟩ | ⟨n, -, -, hn⟩ | ⟨n, -, -, hn⟩ | ⟨_, -, -, ⟨_, hn⟩, -⟩
      · exact Or.inr (Or.inl ⟨r0, cs, cs', h1, rfl⟩)
      · cases he
      · cases hn
      · cases hn
      · cases hn
  have harch1 : ArchFitHyp H σ := hAF
  obtain ⟨hKs', hIp', hnk', hcov', hobj', hzH', hset', hscC'⟩ :=
    J.addSets (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn }) hwI.1 (by omega) hU.pfit hU.free
      (by rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => hBF wp hwp _ hxG p sb fiv (capV_of_capAt hcap)) harch1 hA1 hA3 hE.k1 hout hEw0 hNw0 hRw0 hKn
      hback rfl rfl rfl rfl rfl rfl
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd
    rw [ht]; first | exact le_refl _ | decide | simp [Fl4Spec.defaultObject, Fl4Spec.objBits, Fl4Spec.fl4ObjBitsApi]
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype J.sfree J.ut hksz (capV_of_capAt hcap) rfl hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hCs : JCs (L := L) { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun _ _ _ h => h) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } H' Cs Ac' Lst
      {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1.addR hkR hRz hRn, hRF1.addR hCR1 hRz hRn, hRR1.addR hRz, hY1, hMc1, hBw1, hRP1, hSA1, ⟨_, _, hJPa⟩, hjc', K2, hutc, hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  -- the window's PML4s added to `L4` (`XTopAt.addPml4`): the new PML4 caps are
  -- unassigned, `JAtZ.vsc` (`VCapOK`) asks their PML4s in `L4`; a new PML4's
  -- user half is zero in FL4 (`hUZ`) and empty in the spec (`hpm`)
  have h4k : 2 ^ zOf nt.val us.val = 4096 := by simp [zOf, hnt]
  have hal4 : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q.val % 4096 = 0 := fun q hq => by
    have := (hwb q hq).2.2; rw [h4k] at this; exact this
  have hz4 : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ i : U64, i.val < 256 →
      L.mem res.2.1 (peA q i) = 0#u64 := by
    intro q hq i hi
    have hq4 := hal4 q hq
    obtain ⟨j, hj, hqj⟩ := hq
    have hv := peA_val (tbl_fit hq4) (show i.val < 512 by omega)
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    rw [h4k] at hqj hjk
    refine hUZ _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv, h4k]; omega) ?_
    rw [h4k, show (peA q i).val - Aw = 8 * i.val + j * 4096 by rw [hv]; omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hX4 := XTopAt.addPml4 hXZ (W4 := winSet Aw (2 ^ zOf nt.val us.val) win.val)
    (fun q hq => by
      obtain ⟨pt, e, hu⟩ := hpm q.bv (by rw [← ht]; exact hreg q hq)
      refine ⟨pt, by rw [hspec q hq, e], fun i hi => hu _ ?_⟩
      simp only [Fl4Spec.ucast, BitVec.toNat_setWidth]
      exact lt_of_le_of_lt (Nat.mod_le _ _) hi)
    hal4 hz4
    (fun q hq b g1 g2 => by
      obtain ⟨b1, b2, -⟩ := hwb q hq
      rw [h4k] at b2
      obtain ⟨n1, n2⟩ := hfr0 b (by omega) (by omega)
      refine ⟨fun ho => n1 ?_, n2, fun p0 k0 hp0 hpk => ?_⟩
      · rcases oobj_unionR ho with ho | ⟨r, hr, -⟩
        · rcases oobj_unionN ho with ho | ⟨n, hn', -⟩
          · rcases oobj_unionE ho with ho | ⟨e, he, -⟩
            · exact ho
            · have := hEt e he; omega
          · have := hNt n hn'; omega
        · have := hRt r hr; omega
      · have := hU.free p0 k0 hp0; omega)
  -- the VSpace caps placed (`JAtZ.vsc`): an old cap kept or an untyped cap,
  -- a new cap an unassigned PML4 cap, its PML4 in the grown `L4`
  have hvc : Vs.VsSlotsW Z.th Z.P (Z.L4 ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val) Z.L3 Z.L2 Z.L1
      (L.mem res.2.1) := by
    obtain ⟨-, hCRZ, -, -, hMOZ, -, -⟩ := hXZ.rel
    obtain ⟨P', L4', L3', L2', L1', hVI⟩ := hMOZ.2.2.1
    refine Vs.VsCapsW.slots (G := G') ?_ hCRZ.2.2.1
    intro x hx
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hu : isUt (capV (L.mem s) x) = true
      · exact Vs.vcapW_ut (hE.utk x hx0 hu)
      · rw [(hE.keep x hx0 (by simpa using hu)).2]
        exact (J.vsc x ((hM.members x).1 hx0).1).mono subset_rfl Set.subset_union_left subset_rfl subset_rfl
          subset_rfl
    · have h1 := hVI _ hx
      rw [hE.newc j hj] at h1 ⊢
      have hqW : ptrF (cj j) ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val := ⟨j, hj, hE.cbase j hj⟩
      obtain ⟨b, e⟩ : ∃ b, cj j = .Pml4 b false 0#u64 := by rw [hcj]; simp [cjOf, newCapOf, hnt]
      rw [e] at h1 hqW ⊢
      have hb : ptrF (.Pml4 b false 0#u64) = b := ok_inj (ptr_eq _).symm
      rw [hb] at hqW
      exact ⟨Set.mem_union_right _ hqW, h1.2.1, fun h => by cases h⟩
  -- the buffer fields (`JBuf`): fresh PML4s, then CNode slots; the new caps PML4 caps
  have hfk : IpcFrKeep σ σ' :=
    (IpcFrKeep.of_specAdd hA
      (fun q hq x e => by obtain ⟨pt, e', -⟩ := hpm q hq; rw [e'] at e; cases e)
      (fun q hq vms e => by obtain ⟨pt, e', -⟩ := hpm q hq; rw [e'] at e; cases e)).trans
      (IpcFrKeep.of_keepC hkc)
  have hbf : JBuf (L := L) { Z with
      G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn,
      L4 := Z.L4 ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val } res.2.1 σ' :=
    by obtain ⟨-, hCRZ, -⟩ := hX4.rel
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
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveN hX4 rfl rfl rfl (fun _ _ h => h) (NewEmpty.refl _ _ _) hTH
    (dbgKeep_of_writes J.blk hwI fun b hb => hb.elim (fun h => J.inSlot_notDbg h) (fun ⟨g1, g2⟩ => J.notDbg' (fun q hq => by have := hTb q hq; show b.val < q.val ∨ q.val + 4096 ≤ b.val; omega) (fun c hc => by rcases k2 c hc with h | h <;> omega)))
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ (hC2.idle.trans hidB) hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frame
    (Z' := { Z with
      G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn,
      L4 := Z.L4 ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val })
    rfl rfl rfl hwI.1 hX4 ⟨hCs.del, hCs.ut, hCs.finM, hCs.sfree⟩
    ⟨hJR.call, hJR.rfree, hJR.rrecv, hJR.yld, hJR.mcp, hJR.buf, hJR.rp, hJR.apart, hJR.jpl, hJR.jcov, hJR.kern,
      hJR.utc, hJR.nsc, hJR.inv, hJR.cur, hJR.own, hJR.off, hJR.act, hJR.bsa, hJR.isorted, hJR.curRun, hJR.blk⟩
    hKs' J.thT hIp' hnk' hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hXZ.rel.2.1.2.2.1 (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _),
      J.ext.vkeep (J.vkeep_of hwI fun b hb u hu e => by
        rcases hb with hb | hb
        · exact J.inSlot_nv hb u hu e
        · have h1 := hWT b hb u hu
          rw [e, Sched.tVcpuA_val J.ip.e.tcb hu] at h1
          omega)⟩ hLvN hzDN
  refine ⟨σ', hrun, hok, ⟨Z.th, G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hXZ.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', Lst, _, JZ⟩

set_option maxHeartbeats 4000000 in
/-- **The no-reset retype of PML4s at `J`** (module docstring; `JAtZ.utEpJ`'s
skeleton, one core, `Z.c = 0`): from `JAtZ` at the decode (no reschedule
pending), the decoded arguments (`RetCtx`, no reset: the source cap has a
child), the source a CNode slot's RAM untyped cap, FL4's restart and
`untyped::retype` of PML4s (the kernel half copied into each new object)
end in `UtRetPostJ` (done, `JAt` after at the same sets but the MDB ghost). -/
theorem JAtZ.utPmJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 8) (hc0 : Z.c = 0#u64)
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
  exact WP.spec_mono (J1.utPmBodyJ hni1 hpp hidx hcap1 hnt hc0 hctx1 hfiv hBO1 hAF1 hRU1)
    (fun res h => utRetPostJ_of_body hst1 h)


end

end

end Fl4Proofs.P3
