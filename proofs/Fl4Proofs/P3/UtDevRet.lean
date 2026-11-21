/-
P3 (losfair/FL4#34), untyped: **the no-reset retype of device frames at
`J`** (handoff/devretype.md "dj2 line", "dj3 line"): FL4's `untyped::retype`
from a CNode slot's device untyped cap, without a reset, of frames (types 9,
10, 11), against the spec's `invoke_untyped` with the device flag.

* `DevFreeT`: `DevFree` at the trivial apartness predicate (every device
  untyped cap; the apartness itself is `DevApart`).
* `JAtD`, `UtBodyPostD`: `JAt` / UtScRet's `UtBodyPost` with `DevApart` and
  `DevFreeT` at the same sets and heap (carried alongside `JAtZ`, not fields
  of it).
* `DevApart.retype`: `DevApart` across a retype that keeps the typed heap,
  the new caps no device untypeds, `H` grown by objects at new spec objects
  no smaller than them (with `DevFreeT` after).
* `JAtZ.utDevBodyJ`: UtEpRet's `JAtZ.utEpBodyJ` for a device source and the
  frame types: the source's RAM facts (`JAtZ.utc`, `SpecFree`, `JCovD.ks`,
  `BufFreeHyp`) replaced by `DevApart` and `DevFreeT`; `retype_bodyD`,
  `JPlaced.retypeGS`, `JAtZ.create_noresetBD`, `retype_window_deadS` with
  `DevApart.srcOK`, `SpecFree.retype_dev`, `DevFree.retype`. The source's
  range in one canonical half with a nonzero base from `DevApart` (`CanonR`).
-/
import Fl4Proofs.P3.UtEpRet
import Fl4Proofs.P3.DevJ
import Fl4Proofs.P3.UtRetLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **[J] `DevFree` for every device untyped cap** (l4v `valid_untyped` for
device caps; the caps' apartness is `DevApart`). -/
abbrev DevFreeT (mem : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) : Prop :=
  DevFree (fun _ _ => True) mem G σ

theorem frame_nt_ne {n : Nat} (h : n = 9 ∨ n = 10 ∨ n = 11) :
    n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 12 ∧ n ≠ 13 := by omega

theorem meets_off {q b p fi sb lo hi : Nat} (hr : ¬ (q + b ≤ lo ∨ hi ≤ q)) (h1 : p + fi ≤ lo) (h2 : hi ≤ p + sb)
    (h : q + b ≤ p ∨ p + sb ≤ q ∨ (p ≤ q ∧ q + b ≤ p + fi)) : False := by omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`DevApart` across a retype keeping the typed heap** (module docstring):
the old device caps keep their ranges (the source's free index only grows,
`hbelow`), the kernel-state base and the idle objects are kept, a new device
untyped cap is aligned and lies in the device source's free part (`hcjD`:
its clauses inherited from the source's), and a new `H` object lies at a new
spec object no smaller than it, which `DevFreeT` after places. -/
theorem DevApart.retype {th th' : TypedHeap} {H H' : Heap} {G G' : MdbGhost} {Cs : Set U64} {s s' : S}
    {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64} {σ' : Fl4Spec.State Unit}
    (hD : DevApart (L := L) th H G Cs s) (hE : RetExp th th' (L.mem s) (L.mem s') G G' A k w dslot cj xs)
    (hbelow : ∀ p sb fi d, capV (L.mem s) xs = .Untyped p sb fi d → p.val + fi.val ≤ A)
    (hks : L.ksb s' = L.ksb s) (hid : IdleKeep (L := L) s s')
    (hcjD : ∀ j, j < w → ∀ p sb fi, cj j = .Untyped p sb fi true →
      ∃ ps sbs fis : U64, capV (L.mem s) xs = .Untyped ps sbs fis true ∧ xs ∈ G.chains.flatten ∧
        p.val % 2 ^ sb.val = 0 ∧ ps.val + fis.val ≤ p.val ∧ p.val + 2 ^ sb.val ≤ ps.val + 2 ^ sbs.val ∧
        4 ≤ sb.val)
    (hH : ∀ q kd, H' q = some kd → H q = some kd ∨
      ((∃ z, kd = .other z) ∧ ∃ ko, σ'.kheap q.bv = some ko ∧ kd.bits ≤ Fl4Spec.objBits ko))
    (hDF : DevFreeT (L.mem s') G' σ') :
    DevApart (L := L) th H' G' Cs s' := by
  intro x hx p sb fi hc
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  have hidb : ∀ q, IdleAt (L := L) s' q → IdleAt (L := L) s q := fun q h => by
    unfold IdleAt at h ⊢; rw [hid.1, hid.2] at h; exact h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ : p.val % 2 ^ sb.val = 0 ∧
      (p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val) ∧
      (∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val) ∧
      (p.val + 2 ^ sb.val ≤ (L.ksb s).val + 288000 ∨ (L.ksb s).val + 288000 + 16384 ≤ p.val) ∧
      (∀ q, IdleAt (L := L) s q → q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val) ∧
      RegionFree th p.val (p.val + 2 ^ sb.val) ∧
      (∀ q kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
        (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val ∧ ∃ z, kd = .other z)) ∧
      CanonR p.val (p.val + 2 ^ sb.val) ∧ 4 ≤ sb.val := by
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · obtain ⟨fi0, hle, hc0⟩ : ∃ fi0 : U64, fi0.val ≤ fi.val ∧
          capV (L.mem s) x = .Untyped p sb fi0 true := by
        cases hu : isUt (capV (L.mem s) x)
        · have e := (hE.keep x hx0 hu).2
          rw [e] at hc; rw [hc, isUt_untyped] at hu; cases hu
        · by_cases hxs : x = xs
          · subst hxs
            obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1, -, hA2, -, -, -⟩ := hE.usrc
            rw [e1] at hc
            simp only [capability.Cap.Untyped.injEq] at hc
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
            have hb := hbelow _ _ _ _ e0
            exact ⟨fi0, by omega, e0⟩
          · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := hE.usrc
            rw [h5 x hx0 hu hxs] at hc
            exact ⟨fi, le_rfl, hc⟩
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hD x hx0 p sb fi0 hc0
      refine ⟨a1, a2, a3, a4, a5, a6, fun q kd hq => ?_, a8⟩
      rcases a7 q kd hq with e | e | ⟨e1, e2, e3⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨e1, by omega, e3⟩)
    · rw [hE.newc j hj] at hc
      obtain ⟨ps, sbs, fis, hcs, hxsG, hal, hlo, hhi, h4⟩ := hcjD j hj p sb fi hc
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hD xs hxsG ps sbs fis hcs
      refine ⟨hal, by omega, fun c hc => by have := b3 c hc; omega, by omega,
        fun q hq => by have := b5 q hq; omega, fun q kd hq => by have := b6 q kd hq; omega,
        fun q kd hq => by
          rcases b7 q kd hq with e | e | ⟨e1, e2, -⟩
          · left; omega
          · right; left; omega
          · omega, b8.1.sub (by omega) hhi, h4⟩
  refine ⟨a1, by rw [hks]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks]; exact a4,
    fun q hq => a5 q (hidb q hq), a6, fun q kd hq => ?_, a8⟩
  rcases hH q kd hq with h | ⟨hz, ko, hko, hb⟩
  · exact a7 q kd h
  · have h2 : 2 ^ kd.bits ≤ 2 ^ Fl4Spec.objBits ko := Nat.pow_le_pow_right (by decide) hb
    have := hDF x hx p sb fi true hc ⟨rfl, trivial⟩ q.bv ko hko
    simp only [UScalar.bv_toNat] at this
    rcases this with (e | e) | ⟨e1, e2⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨e1, by omega, hz⟩)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

variable (arI) in
/-- **`JAt` with the device untyped caps' facts** (`DevApart`, `DevFreeT`)
at the same sets and heap. -/
def JAtD (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ DevApart (L := L) Z.th H Z.G Cs s ∧ DevFreeT (L.mem s) Z.G σ

theorem JAtD.jAt {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JAtD (L := L) arI AR s a σ) : JAt (L := L) arI AR s a σ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -⟩ := h
  exact ⟨Z, H, Cs, Ac, Lst, D, J⟩

variable (arI) in
/-- **`UtBodyPost` with `JAtD` after.** -/
def UtBodyPostD (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) (inv : Fl4Spec.UntypedInvocation)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ', (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi inv).run σ = ({(.ok (), σ')}, False) ∧
    res.1 = .Ok () ∧
    (∃ th' G', Placed th' ∧ CRel th' (L.mem res.2.1) σ' G' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
    JAtD (L := L) arI AR res.2.1 res.2.2 σ'

theorem UtBodyPostD.post {AR : A → Fl4Spec.Cr3 → Prop} {σ : Fl4Spec.State Unit} {inv : Fl4Spec.UntypedInvocation}
    {res : core.result.Result Unit error.Exc × S × A} (h : UtBodyPostD (L := L) arI AR σ inv res) :
    UtBodyPost (L := L) arI AR σ inv res := by
  obtain ⟨σ', h1, h2, h3, h4⟩ := h
  exact ⟨σ', h1, h2, h3, h4.jAt⟩

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **The no-reset retype of device frames from a `JAtZ` state** (module
docstring; UtEpRet's `JAtZ.utEpBodyJ` for a device source and frame types
9/10/11): `UtBodyPostD` (`UtBodyPost` with `DevApart` and `DevFreeT` after,
at the same sets). The source's facts from `DevApart` / `DevFreeT` instead
of `JAtZ.utc` / `SpecFree` / `JCovD.ks`; its range in one canonical half
with a nonzero base (`DevApart`'s `CanonR`). -/
theorem JAtZ.utDevBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi true nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ)
    (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
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
  have ht : t = .archObject .hugePageObj ∨ t = .archObject .smallPageObj ∨ t = .archObject .largePageObj := by
    rcases hnt with h | h | h <;> rw [h] at hty <;> simp [objTypeOf, Fl4Spec.archDataToObjType] at hty <;>
      simp [hty]
  have htU : t ≠ .untyped := by rcases ht with rfl | rfl | rfl <;> simp
  have htP : t ≠ .archObject .pml4Obj := by rcases ht with rfl | rfl | rfl <;> simp
  have htT : t ≠ .tcbObject := by rcases ht with rfl | rfl | rfl <;> simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  subst hfiv
  -- no restart here: the state the body starts at
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rcases hnt with h | h | h <;>
    simp [zOf, h]) hpal hpfit hfiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_bodyD (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx hcap
    hpal hpfit hfiLe hcan (fun h => by cases h) hfree (fun h => by cases h) Fl4Spec.fl4ObjBitsApi nt us dest off win t r hty
    (by omega) hctx.size.1 hctx.size.2.1 (fun h => by omega) (fun h => by omega) (fun _ => by omega) hctx.cnode.1 hctx.cnode.2.1
    hctx.window.2.2 hctx.window.1 hctx.memory hctx.empty hb) (fun res hRP => ?_)
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
    rcases ht with rfl | rfl | rfl
    · rw [objTypeOf_huge hn0, objTypeOf_huge hty]
    · rw [objTypeOf_small hn0, objTypeOf_small hty]
    · rw [objTypeOf_large hn0, objTypeOf_large hty]
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
  -- the spec's outcome: the window's objects added, then CNodes changed
  have hSR1 := J.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  obtain ⟨-, σB, hA, hcnk, hkc⟩ := invokeUntyped_noreset_add Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) true σ htU htP {pp.bv, dest.bv} (Or.inl rfl)
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
      have hfit := hpfit
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
        rcases hDF _ hxG p sb fiv true (capV_of_capAt hcap) ⟨rfl, trivial⟩ _ ko0 hko0 with h | ⟨h2, h3⟩
        · rw [hqv] at h; omega
        · rw [hqv] at h2 h3; omega)
    (.ok (), σ') (by rw [hrun]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∀ x n, Fl4Spec.defaultObject t true us.val σ.curDomain ≠ .schedContext x n := by
    intro q _ x n; rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hcjne : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a := by
    intro j _ p b a
    rw [hcj]
    rcases hnt with h | h | h <;> simp [cjOf, newCapOf, h]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    exact retExp_pml4_back hE hM hM' hcjne hxs hc
  have hX' := XTopAt.addStep J.xtop hw hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (hSt.okv hMO0) hTS
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  have hfit := hpfit
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have k1 := hks1
  have k2 := hnd1
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
  have hspec : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), σ'.kheap q.bv = some (Fl4Spec.defaultObject t true us.val σ.curDomain) := by
    intro q hq
    have hB := (hA.new _ (hreg q hq)).2
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, -⟩
    · exact e.trans hB
    · have e2 := hB.symm.trans e1
      rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at e2
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
      rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hTn : ¬ t = .tcbObject := htT
  have hTT : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), ∀ t0 ∈ Z.T, t0.val + 4096 ≤ q.val ∨ q.val + 2 ^ (zOf nt.val us.val) ≤ t0.val := by
    intro q hq t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hfree t0 .tcb hth
    obtain ⟨b1, b2, -⟩ := hwb q hq
    simp only [objSize] at this; omega
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th Z.th (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hwb hreg hspec hTT hA1 hA2 hA3
  -- the window's objects, added to `E`, `N` or `R` (`XTopAt.addE`/`addN`/`addR`)
  obtain ⟨En, Nn, Rn, hXZ, hEs, hNs, hRs, hEt, hNt, hRt, hWEN⟩ : ∃ En Nn Rn : Set U64,
      XTopAt (L := L) AR { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 ar σ' ∧
      En ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ Nn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      Rn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      (∀ e ∈ En, nt.val = 2) ∧ (∀ n ∈ Nn, nt.val = 3) ∧ (∀ r ∈ Rn, nt.val = 6) ∧
      ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∈ En ∨ q ∈ Nn ∨ q ∈ Rn ∨
        (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) := by
    have ha : nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11 :=
      Or.inr (Or.inr (Or.inr hnt))
    refine ⟨∅, ∅, ∅, ?_, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => Or.inr (Or.inr (Or.inr ha))⟩
    simp only [Set.union_empty]
    exact hX'
  -- the spec side
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_co Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) true σ htU htP (.ok (), σ') (by rw [hrun]; rfl)
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
    intro j _; rw [hcj]; rcases hnt with h | h | h <;> simp [cjOf, newCapOf, h, isUt]
  have hcjR : ∀ j, j < win.val → ∀ p sb fi, cj j ≠ .Untyped p sb fi false := fun j hj p sb fi e => by
    have h2 := hcjU j hj; rw [e, isUt_untyped] at h2; cases h2
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noresetBD hni hpp hidx hcap hDA hE
    (hRU _ _ hA1 hA3) (fun _ => hcjU) hcjR (by omega) ⟨by omega, fun h => absurd h (by omega)⟩
    (k := 2 ^ zOf nt.val us.val) rfl hAk htT hW (fun _ hz => by
      exfalso
      rcases hnt with h | h | h
      · exact hz 30 (by simp [newKind, h])
      · exact hz 12 (by simp [newKind, h])
      · exact hz 21 (by simp [newKind, h])) hidl
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
    have hk' : σB.kheap o = some (.schedContext y0 n0) := by
      rcases hkc o with e | ⟨r0, cs0, cs', -, e2⟩
      · exact e.symm.trans hk
      · rw [e2] at hk; cases hk
    rcases hA.kback hk' with h1 | ⟨-, h2⟩
    · rw [h0] at h1; cases h1
    · rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at h2
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, hhas2, hthx2, hJP2⟩ :=
    Sched.JPlaced.retypeGS (L := L) hJp J.jcov J.ut hI hM hksz hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by rcases hnt with h' | h' | h' <;> simp [newKind, h'] at h) (fun h => absurd h hn1) (fun h => absurd h hn1)
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
    hX'.fin.1.1.1 (hC2.ct.trans hctB) (hC2.csc.trans hcscB) horig hgp' hao hDbg
  have hRD := (retype_window_deadS J.jcov J.ut hI hE (hDA.srcOK hE (capV_of_capAt hcap) hcjR)).1
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
    have := hfree _ .tcb K1.curT; simp only [objSize] at this; omega
  have hTb : ∀ q, H q = some .tcb → q.val + 4096 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ q.val :=
    fun q hq => by
      have := hfree q .tcb ((hJp.tcb q).2 hq); simp only [objSize] at this; omega
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
  have hutc := J.ret_utc (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => hDn0 d hd) hDu hcapK hwI hcdtK horgK hgp' hM'
    (RetExp.src_child hE hctx.window.1 hP' hC' hAs)
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- the spec's invariants and the call stacks (`uaRest`, `addRP`)
  have hIN : IdleNew (fun q => q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val))
      (fun _ => Fl4Spec.defaultObject t true us.val σ.curDomain) := fun q _ => by
    rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hWnN : ∀ n ∈ Nn, n.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := fun n hn => hreg n (hNs hn)
  obtain ⟨hCR1, -, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J.uaRest hwI hA hIN hcnk hWnN
  have hspec1 : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases hDF _ hxG p sb fiv true (capV_of_capAt hcap1) ⟨rfl, trivial⟩ o ko hk with (h | h) | ⟨h3, h4⟩
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
    rw [hspec r (hRs hr)]
    have h6 := hRt r hr
    have e := hty; rw [h6] at e; simp [objTypeOf] at e; subst e; rfl
  have hRz : ∀ r ∈ Rn, L.mem res.2.1 (P1.rNextA r) = 0#u64 ∧ L.mem res.2.1 (P1.rPrevA r) = 0#u64 :=
    fun r hr => absurd (hRt r hr) (frame_nt_ne hnt).2.2.1
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
  obtain ⟨hRP1, hSA1⟩ := J.addRP hwI hA hIN hcnk hWnN (by omega) hpfit hfree hspec1
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
    · refine Or.inr (Or.inr (Or.inr ?_))
      rcases ha with h | h | h | h | h | h <;> simp [newKind, h] at hK <;> exact ⟨_, hK.symm⟩
  have hrev : ∀ o, o ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∃ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q.bv = o := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem ho
    rw [hlen] at hj
    rw [hb]
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hfit := hpfit
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
      · obtain ⟨q, hq, hqo⟩ := hrev o hW'
        rcases hWEN q hq with hqE | hqN | hqR | ha
        · have h2' := hEt q hqE
          have htE : t = .endpointObject := by
            have e := hty; rw [h2'] at e; simp [objTypeOf] at e; exact e.symm
          exact Or.inr (Or.inl ⟨q, hqE, hqo, by rw [h2, htE]; rfl⟩)
        · have h3' := hNt q hqN
          have htN : t = .notificationObject := by
            have e := hty; rw [h3'] at e; simp [objTypeOf] at e; exact e.symm
          exact Or.inr (Or.inr (Or.inl ⟨q, hqN, hqo, by rw [h2, htN]; rfl⟩))
        · have h6' := hRt q hqR
          have htR : t = .replyObject := by
            have e := hty; rw [h6'] at e; simp [objTypeOf] at e; exact e.symm
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hqR, hqo, by rw [h2, htR]; rfl⟩)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hq, hqo, ?_, ?_⟩)))
          · rw [h2]
            rcases ha with h | h | h | h | h | h <;> have e := hty <;> rw [h] at e <;>
              simp [objTypeOf, Fl4Spec.archDataToObjType] at e <;> subst e <;> exact ⟨_, rfl⟩
          · rcases ha with h | h | h | h | h | h <;> simp [newKind, h]
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
    J.addSets (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn }) hwI.1 (by omega) hpfit hfree
      (by rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => by
        obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hwp
        rcases hDF _ hxG p sb fiv true (capV_of_capAt hcap) ⟨rfl, trivial⟩ o ko hk with (h | h) | ⟨h3, h4⟩ <;>
          omega) harch1 hA1 hA3 hE.k1 hout hEw0 hNw0 hRw0 hKn
      hback rfl rfl rfl rfl rfl rfl
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; rcases hnt with h | h | h <;> simp [cjOf, newCapOf, h]
  have hobE : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t true us.val cd) = Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd; rcases ht with rfl | rfl | rfl <;> rfl
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t true us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val :=
    fun cd => (hobE cd).le
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype_dev J.sfree hDF J.ut hksz (capV_of_capAt hcap)
    trivial hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hDF' : DevFreeT (L.mem res.2.1) G' σ' := DevFree.retype hDF J.ut hksz (capV_of_capAt hcap)
    trivial hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hCs : JCs (L := L) { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun _ _ _ h => h) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } H' Cs Ac' Lst
      {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1.addR hkR hRz hRn, hRF1.addR hCR1 hRz hRn, hRR1.addR hRz, hY1, hMc1, hBw1, hRP1, hSA1, ⟨_, _, hJPa⟩, hjc', K2, hutc, hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  -- the window's tables added to `L3`, `L2` or `L1` (`XTopAt.addTab`): the
  -- new table caps are unmapped, so `JAtZ.vsc` asks their tables in the sets
  have hTw : ∀ q, (q ∈ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7} ∨
      q ∈ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13} ∨
      q ∈ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12}) →
      q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ (2 : Nat) ^ zOf nt.val us.val = 4096 ∧
        (nt.val = 7 ∨ nt.val = 13 ∨ nt.val = 12) := by
    rintro q (⟨hq, h⟩ | ⟨hq, h⟩ | ⟨hq, h⟩) <;> refine ⟨hq, ?_, by omega⟩ <;> simp [zOf, h]
  have hnoT : ¬ (nt.val = 7 ∨ nt.val = 13 ∨ nt.val = 12) := by
    rintro (h | h | h)
    exacts [(frame_nt_ne hnt).2.2.2.1 h, (frame_nt_ne hnt).2.2.2.2.2 h, (frame_nt_ne hnt).2.2.2.2.1 h]
  have hXT := XTopAt.addTab hXZ (W3 := {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7})
    (W2 := {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13})
    (W1 := {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12})
    (fun q ⟨_, h⟩ => absurd h (frame_nt_ne hnt).2.2.2.1) (fun q ⟨_, h⟩ => absurd h (frame_nt_ne hnt).2.2.2.2.2)
    (fun q ⟨_, h⟩ => absurd h (frame_nt_ne hnt).2.2.2.2.1)
    (fun q hq => (hnoT (hTw q hq).2.2).elim) (fun q hq => (hnoT (hTw q hq).2.2).elim)
    (fun q hq => (hnoT (hTw q hq).2.2).elim)
  -- the VSpace caps placed (`JAtZ.vsc`): an old cap kept or an untyped cap,
  -- a new cap set-free (its placement from the ghost-set invariant after) or
  -- a new table cap, unmapped, its table in the grown set
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 (Z.L3 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7})
      (Z.L2 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13})
      (Z.L1 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12}) (L.mem res.2.1) := by
    obtain ⟨-, hCRZ, -, -, hMOZ, -, -⟩ := hXZ.rel
    obtain ⟨P', L4', L3', L2', L1', hVI⟩ := hMOZ.2.2.1
    refine Vs.VsCapsW.slots (G := G') ?_ hCRZ.2.2.1
    intro x hx
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hu : isUt (capV (L.mem s) x) = true
      · exact Vs.vcapW_ut (hE.utk x hx0 hu)
      · rw [(hE.keep x hx0 (by simpa using hu)).2]
        exact (J.vsc x ((hM.members x).1 hx0).1).mono subset_rfl subset_rfl Set.subset_union_left
          Set.subset_union_left Set.subset_union_left
    · have h1 := hVI _ hx
      rw [hE.newc j hj] at h1 ⊢
      by_cases hT : Vs.SetFree (cj j)
      · exact (Vs.VCapOK.setFree hT h1).toW
      · have hqW : ptrF (cj j) ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val := ⟨j, hj, hE.cbase j hj⟩
        obtain ⟨b, hpt⟩ : ∃ b, (nt.val = 7 ∧ cj j = .Pdpt b false 0#u64 0#u64) ∨
            (nt.val = 13 ∧ cj j = .PageDirectory b false 0#u64 0#u64) ∨
            (nt.val = 12 ∧ cj j = .PageTable b false 0#u64 0#u64) := by
          rw [hcj] at hT ⊢
          rcases hnt with h | h | h <;> simp [cjOf, newCapOf, h, Vs.SetFree] at hT ⊢
        rcases hpt with ⟨hn, e⟩ | ⟨hn, e⟩ | ⟨hn, e⟩ <;> rw [e] at h1 hqW ⊢
        · have hb : ptrF (.Pdpt b false 0#u64 0#u64) = b := ok_inj (ptr_eq _).symm
          rw [hb] at hqW
          exact ⟨fun _ => Or.inr ⟨hqW, hn⟩, h1.2.1, (fun h => by cases h), (fun h => by cases h)⟩
        · have hb : ptrF (.PageDirectory b false 0#u64 0#u64) = b := ok_inj (ptr_eq _).symm
          rw [hb] at hqW
          exact ⟨fun _ => Or.inr ⟨hqW, hn⟩, h1.2.1, (fun h => by cases h), (fun h => by cases h)⟩
        · have hb : ptrF (.PageTable b false 0#u64 0#u64) = b := ok_inj (ptr_eq _).symm
          rw [hb] at hqW
          exact ⟨fun _ => Or.inr ⟨hqW, hn⟩, h1.2.1, (fun h => by cases h), (fun h => by cases h)⟩
  -- the buffer fields (`JBuf`): fresh device frames (no non-device data
  -- page, no TCB), then CNode slots; the new caps device frame caps
  have hfk : IpcFrKeep σ σ' :=
    (IpcFrKeep.of_specAdd hA
      (fun _ _ x e => by rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at e)
      (fun _ _ vms e => by
        rcases ht with rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject, Fl4Spec.defaultArchObject] at e)).trans
      (IpcFrKeep.of_keepC hkc)
  have hbf : JBuf (L := L) { Z with
      G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn,
      L3 := Z.L3 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7},
      L2 := Z.L2 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13},
      L1 := Z.L1 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12} } res.2.1 σ' := by
    obtain ⟨-, hCRZ, -⟩ := hXZ.rel
    exact ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.retype hE hM hCRZ.2.2.1 (fun _ => UFr.keep hfk.page)
      (fun j _ => by
        rw [hcj]
        rcases hnt with h | h | h <;> simp [cjOf, newCapOf, h, Vs.FrIn])⟩
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
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveN hXT rfl rfl rfl (fun _ _ h => h) (NewEmpty.refl _ _ _) hTH
    (dbgKeep_of_writes J.blk hwI fun _ hb => J.inSlot_notDbg hb)
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ (hC2.idle.trans hidB) hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frame
    (Z' := { Z with
      G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn,
      L3 := Z.L3 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7},
      L2 := Z.L2 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13},
      L1 := Z.L1 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12} })
    rfl rfl rfl hwI.1 hXT ⟨hCs.del, hCs.ut, hCs.finM, hCs.sfree⟩
    ⟨hJR.call, hJR.rfree, hJR.rrecv, hJR.yld, hJR.mcp, hJR.buf, hJR.rp, hJR.apart, hJR.jpl, hJR.jcov, hJR.kern,
      hJR.utc, hJR.nsc, hJR.inv, hJR.cur, hJR.own, hJR.off, hJR.act, hJR.bsa, hJR.isorted, hJR.curRun, hJR.blk⟩
    hKs' J.thT hIp' hnk' hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hXZ.rel.2.1.2.2.1 (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _), J.ext.vkeep (J.vkeep_slot hwI)⟩ hLvN hzDN
  -- `DevApart` after
  have hDA' : DevApart (L := L) Z.th H' G' Cs res.2.1 := by
    refine hDA.retype hE (fun p0 sb0 fi0 d0 h => ?_) hksR hidl
      (fun j hj p1 sb1 fi2 e => by have h2 := hcjU j hj; rw [e, isUt_untyped] at h2; cases h2)
      (fun q kd hq => ?_) hDF'
    · rw [capV_of_capAt hcap] at h
      simp only [capability.Cap.Untyped.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hA1
    · have e := hout q
      rw [hq] at e
      by_cases hN : NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ (newKind nt.val us.val).isSome
      · rw [if_pos hN] at e
        right
        obtain ⟨j, hj, hv⟩ := hN.1
        refine ⟨?_, _, hspec q ⟨j, hj, hv⟩, ?_⟩
        · rcases hnt with h | h | h <;> rw [h] at e <;> simp [newKind] at e <;> exact ⟨_, e⟩
        rw [hobE, hb, newKind_bits e.symm]
      · rw [if_neg hN] at e
        split_ifs at e
        exact Or.inl e.symm
  refine ⟨σ', hrun, hok, ⟨Z.th, G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hXZ.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', Lst, _, JZ, hDA', hDF'⟩


end

end

end Fl4Proofs.P3
