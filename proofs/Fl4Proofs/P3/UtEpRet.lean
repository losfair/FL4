/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of endpoints,
notifications, replies, VSpace tables or frames at `J`** (handoff/utj.md
"Round 4c", "Round 5", "uttypes"): FL4's restart and `untyped::retype` from a
CNode slot's RAM untyped cap, without a reset (the cap has a child), of
endpoints (type 2), notifications (type 3), replies (type 6), PDPTs (7), page
tables (12), page directories (13) or frames (9, 10, 11: 1 GiB, 4 KiB,
2 MiB), end in XTopJointUt's `UtRetPostJ`: the spec's outcome related, with
`JAtZ` after at the sets grown by the window's objects (`E`, `N` or `R`; no
set for the tables and frames, which are `H`'s `other` objects of 12, 30 or
21 bits, P1's `newKind`), P1's heap after the creation (`HOut`) and the dead
set without the new objects.

* (`perf_ut_mem`, `cscW_of_sched`: UtScRet.)
* `JAtZ.utEpJ`: the step. Its J premises: `BufObjHyp` [J] (every IPC-buffer
  word inside a spec object), `ArchFitHyp` [J] (UtEpSets: `H`'s object at a
  spec arch object no larger than it) and `RegionUnrefJ` [J] (ScJoint: the
  kept objects and FL4's debug and timer lists name no dead object of the
  window); for frames `JEntryAt.urz`/`utks` [J] (the source's free part
  zero in the spec's memory, `UtFreeZ`; its region off the 64 cores' nodes,
  `UtNodesAt`), `B` grown by the new pages' words (UtFrameAdd's
  `XTopAt.chgB`, `JAtZ.add_frameB`). The fields after: `XTopAt` (as `JAtZ.utEpXTop`, the window by
  `XTopAt.addE`/`addN`/`addR`), `JCs` (`JCs.retype`), `JRest`
  (`JAtZ.uaRest`, UtReplyAdd's `CallRel.addR`/`RFree.addR`/`RRecv.addR`,
  `JAtZ.addRP`, `JPlaced.retype`,
  `JAtZ.create_noreset`, `JKern.hout`, `JAtZ.ret_utc`), the sets and heap
  (`JAtZ.addSets`), put together by `JAtZ.add_frame`.
-/
import Fl4Proofs.P3.UtUtRet
import Fl4Proofs.P3.UtPmRet
import Fl4Proofs.P3.UtCnRet
import Fl4Proofs.P3.UtTcbRet
import Fl4Proofs.P3.UtTabAdd
import Fl4Proofs.P3.UtFrameAdd
import Fl4Proofs.P3.UtRetLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem objTypeOf_pdpt {n : Nat} (h : objTypeOf n = some (.archObject .pdptObj)) : n = 7 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

theorem objTypeOf_pt {n : Nat} (h : objTypeOf n = some (.archObject .pageTableObj)) : n = 12 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

theorem objTypeOf_pd {n : Nat} (h : objTypeOf n = some (.archObject .pageDirectoryObj)) : n = 13 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

theorem objTypeOf_huge {n : Nat} (h : objTypeOf n = some (.archObject .hugePageObj)) : n = 9 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

theorem objTypeOf_small {n : Nat} (h : objTypeOf n = some (.archObject .smallPageObj)) : n = 10 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

theorem objTypeOf_large {n : Nat} (h : objTypeOf n = some (.archObject .largePageObj)) : n = 11 := by
  have hn : n < 19 := by
    by_contra hc
    rw [(objTypeOf_none n).2 (by omega)] at h; cases h
  interval_cases n <;> simp_all [objTypeOf, Fl4Spec.archDataToObjType]

/-! ### The frame retype's pieces (`B` grown, UtFrameAdd) -/

/-- The RAM frame types' spec objects, size and FL4 caps. -/
theorem frame_new {n : Nat} {t : Fl4Spec.ApiObjectType} (hty : objTypeOf n = some t)
    (hn : n = 9 ∨ n = 10 ∨ n = 11) (us : Nat) :
    ∃ vms sz, (∀ cd, Fl4Spec.defaultObject t false us cd = .archObj (.dataPage false vms)) ∧
      Fl4Spec.pageBitsForSize vms = zOf n us ∧ (fbitsF sz).val = zOf n us ∧
      ∀ base us' : U64, newCapOf n base us' false = .Frame base sz 3#u64 false false false 0#u64 0#u64 := by
  rcases hn with rfl | rfl | rfl <;> simp [objTypeOf, Fl4Spec.archDataToObjType] at hty <;> subst hty
  · exact ⟨.x64HugePage, .Huge, fun _ => rfl, by simp [zOf, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits,
      Fl4Spec.ptTranslationBits], by rw [fbitsF_val]; simp [zOf, frameSizeOf, Fl4Spec.pageBitsForSize,
      Fl4Spec.pageBits, Fl4Spec.ptTranslationBits], fun _ _ => by simp [newCapOf]⟩
  · exact ⟨.x64SmallPage, .Small, fun _ => rfl, by simp [zOf, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits,
      Fl4Spec.ptTranslationBits], by rw [fbitsF_val]; simp [zOf, frameSizeOf, Fl4Spec.pageBitsForSize,
      Fl4Spec.pageBits, Fl4Spec.ptTranslationBits], fun _ _ => by simp [newCapOf]⟩
  · exact ⟨.x64LargePage, .Large, fun _ => rfl, by simp [zOf, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits,
      Fl4Spec.ptTranslationBits], by rw [fbitsF_val]; simp [zOf, frameSizeOf, Fl4Spec.pageBitsForSize,
      Fl4Spec.pageBits, Fl4Spec.ptTranslationBits], fun _ _ => by simp [newCapOf]⟩

/-- A retype's default object that is a RAM data page is one of a frame type,
of the type's size. -/
theorem frame_of_default {n : Nat} {t : Fl4Spec.ApiObjectType} (hty : objTypeOf n = some t)
    (htU : t ≠ .untyped) {us : Nat}
    {cd : Fl4Spec.Domain} {vms : Fl4Spec.VMPageSize}
    (h : Fl4Spec.defaultObject t false us cd = .archObj (.dataPage false vms)) :
    (n = 9 ∨ n = 10 ∨ n = 11) ∧ Fl4Spec.pageBitsForSize vms = zOf n us := by
  cases t with
  | archObject ao =>
    cases ao <;> simp [Fl4Spec.defaultObject, Fl4Spec.defaultArchObject] at h
    · subst h; have := objTypeOf_small hty; subst this
      exact ⟨by omega, by simp [zOf, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits]⟩
    · subst h; have := objTypeOf_large hty; subst this
      exact ⟨by omega, by simp [zOf, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits, Fl4Spec.ptTranslationBits]⟩
    · subst h; have := objTypeOf_huge hty; subst this
      exact ⟨by omega, by simp [zOf, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits, Fl4Spec.ptTranslationBits]⟩
  | untyped => exact absurd rfl htU
  | _ => simp [Fl4Spec.defaultObject] at h

/-- **A byte of a RAM data page is in a user frame** (`UFr`). -/
theorem ufr_new {σ : Fl4Spec.State Unit} {q : U64} {vms : Fl4Spec.VMPageSize}
    (hk : σ.kheap q.bv = some (.archObj (.dataPage false vms)))
    (hal : q.val % 2 ^ Fl4Spec.pageBitsForSize vms = 0) {a : Nat} (h1 : q.val ≤ a)
    (h2 : a < q.val + 2 ^ Fl4Spec.pageBitsForSize vms) (h64 : a < 2 ^ 64) : UFr σ a := by
  refine ⟨vms, ?_⟩
  have e : (BitVec.ofNat 64 a &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize vms) : BitVec 64)) = q.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [Endp.and_not_mask_toNat _ _ (Endp.pageBits_mem vms), BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64,
      UScalar.bv_toNat]
    have hn2 : 0 < 2 ^ Fl4Spec.pageBitsForSize vms := Nat.two_pow_pos _
    obtain ⟨m, hm⟩ : ∃ m, q.val = m * 2 ^ Fl4Spec.pageBitsForSize vms :=
      ⟨q.val / 2 ^ Fl4Spec.pageBitsForSize vms, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hal)).symm⟩
    have hd : a / 2 ^ Fl4Spec.pageBitsForSize vms = m := by
      apply Nat.div_eq_of_lt_le
      · rw [← hm]; exact h1
      · rw [Nat.succ_mul, ← hm]; exact h2
    rw [hd, hm]
  rw [e]; exact hk

/-- **A word of zero bytes reads 0**, at a word address. -/
theorem loadWordAt_zero8 {um : Fl4Spec.Word → Fl4Spec.Word8} {a : U64} (ha : a.val + 8 ≤ 2 ^ 64)
    (hz : ∀ y : Fl4Spec.Word, a.val ≤ y.toNat → y.toNat < a.val + 8 → um y = 0) :
    Endp.loadWordAt um a.bv = 0 := by
  suffices h : ∀ i ∈ Fl4Spec.intUpto 0 7, um (a.bv + (7 - BitVec.ofInt 64 i)) = 0 by
    unfold Endp.loadWordAt
    rw [List.map_congr_left h, Endp.intUpto_07]
    decide
  intro i hi
  have key : ∀ k : Nat, k < 8 → (a.bv + BitVec.ofNat 64 k).toNat = a.val + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, UScalar.bv_toNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [Endp.intUpto_07] at hi
  obtain ⟨k, hk8, e⟩ : ∃ k, k < 8 ∧ (7 : BitVec 64) - BitVec.ofInt 64 i = BitVec.ofNat 64 k := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨7, by omega, by decide⟩, ⟨6, by omega, by decide⟩, ⟨5, by omega, by decide⟩,
      ⟨4, by omega, by decide⟩, ⟨3, by omega, by decide⟩, ⟨2, by omega, by decide⟩,
      ⟨1, by omega, by decide⟩, ⟨0, by omega, by decide⟩]
  rw [e]
  exact hz _ (by rw [key k hk8]; omega) (by rw [key k hk8]; omega)

/-- **`IpcBufCapOK` across fresh objects** (`SpecAdd`) none a TCB with an IPC
frame (new data pages allowed: the old ones are kept). -/
theorem Endp.IpcBufCapOK.specAdd {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop}
    {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (h : Endp.IpcBufCapOK σ) (hA : Sched.SpecAdd σ σ' W o)
    (ht : ∀ p, W p → ∀ x, o p = .tcb x → x.tcbIpcframe = .nullCap) : Endp.IpcBufCapOK σ' := by
  intro t x hx dev p R mt vms md hf hR
  by_cases hw : W t
  · rw [(hA.new t hw).2] at hx
    rw [ht t hw x (Option.some.inj hx)] at hf; cases hf
  · rw [hA.old t hw] at hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := h t x hx dev p R mt vms md hf hR
    exact ⟨h1, h2, fun k hk => inUserFrame_keep (fun _ _ hp => hA.kold hp) (h3 k hk), h4, h5⟩

set_option maxHeartbeats 16000000 in
/-- **The body of `JAtZ.utEpJ`: the retype without a reset from a `JAtZ`
state** (handoff/utj.md Round 13): FL4's `untyped::retype` with `reset = false`
from the state itself (after the restart; or after the restart and the
reset, the cap's free index then 0), against the spec's `invoke_untyped`
without a reset from `σ`: `UtBodyPost`. The arguments `RetCtx` at the state
(any `reset` flag, the window base from the cap's free index `fiv = fi`),
`Entered` (no switch pending), and the kept objects' references to a range
in the cap's free part (`hRU`, `RegionUnrefJ`'s conclusion at the state). -/
theorem JAtZ.utEpBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11))
    (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ)
    (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s)
    (hZ0 : UtFreeZ σ (p.val + fi.val) (p.val + 2 ^ sb.val)) (hKN : UtNodesAt (L.ksb s) p sb) :
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
  have ht : t = .endpointObject ∨ t = .notificationObject ∨ t = .replyObject ∨ t = .archObject .pdptObj ∨
      t = .archObject .pageTableObj ∨ t = .archObject .pageDirectoryObj ∨ t = .archObject .hugePageObj ∨
      t = .archObject .smallPageObj ∨ t = .archObject .largePageObj := by
    rcases hnt with h | h | h | h | h | h | h | h | h <;> rw [h] at hty <;> simp [objTypeOf, Fl4Spec.archDataToObjType] at hty <;>
      simp [hty]
  have htX : ∀ d x, Fl4Spec.defaultObject t false us.val d = .tcb x → x.tcbIpcframe = .nullCap := by
    intro d x e
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at e
  have htU : t ≠ .untyped := by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have htP : t ≠ .archObject .pml4Obj := by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have htT : t ≠ .tcbObject := by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  subst hfiv
  -- no restart here: the state the body starts at
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rcases hnt with h | h | h | h | h | h | h | h | h <;>
    simp [zOf, h]) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_body (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx hcap
    hU.pal hU.pfit hU.fiLe (hU.high hnd) hU.free (hU.zero hnd) Fl4Spec.fl4ObjBitsApi nt us dest off win t r hty
    (by omega) hctx.size.1 hctx.size.2.1 (fun h => by omega) (fun h => by omega) hctx.cnode.1 hctx.cnode.2.1
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
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [objTypeOf_ep hn0, objTypeOf_ep hty]
    · rw [objTypeOf_ntfn hn0, objTypeOf_ntfn hty]
    · rw [objTypeOf_reply hn0, objTypeOf_reply hty]
    · rw [objTypeOf_pdpt hn0, objTypeOf_pdpt hty]
    · rw [objTypeOf_pt hn0, objTypeOf_pt hty]
    · rw [objTypeOf_pd hn0, objTypeOf_pd hty]
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
    intro q _ x n; rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hcjne : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a := by
    intro j _ p b a
    rw [hcj]
    rcases hnt with h | h | h | h | h | h | h | h | h <;> simp [cjOf, newCapOf, h]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    exact retExp_pml4_back hE hM hM' hcjne hxs hc
  have hX' := XTopAt.addStep J.xtop hw hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (hSt.okv hMO0) hTS
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
  have hspec : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), σ'.kheap q.bv = some (Fl4Spec.defaultObject t false us.val σ.curDomain) := by
    intro q hq
    have hB := (hA.new _ (hreg q hq)).2
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, -⟩
    · exact e.trans hB
    · have e2 := hB.symm.trans e1
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at e2
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
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at hBk
    · rw [hA.old _ hWq] at hBk
      obtain ⟨ko, hko, hty⟩ := hksz _ _ hBk
      exact ⟨ko, hko, objBits_of_aType_sc hty⟩
  have hfr0 := J.free_noObj hAs hcap hBF hksR hsc
  have hWZ' : WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val (t = .tcbObject) := by
    have h0 := hWZ ⟨rfl, htP⟩
    rw [eA, ek, ew, hlen, hb] at h0
    exact h0
  have hTn : ¬ t = .tcbObject := htT
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
  rw [← eA] at hwb hreg hspec hTT hWZ' hA1 hA2 hA3
  -- the window's objects, added to `E`, `N` or `R` (`XTopAt.addE`/`addN`/`addR`)
  obtain ⟨En, Nn, Rn, hXZ, hEs, hNs, hRs, hEt, hNt, hRt, hWEN⟩ : ∃ En Nn Rn : Set U64,
      XTopAt (L := L) AR { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn } res.2.1 ar σ' ∧
      En ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ Nn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      Rn ⊆ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧
      (∀ e ∈ En, nt.val = 2) ∧ (∀ n ∈ Nn, nt.val = 3) ∧ (∀ r ∈ Rn, nt.val = 6) ∧
      ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∈ En ∨ q ∈ Nn ∨ q ∈ Rn ∨
        (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) := by
    rcases hnt with h2 | h3 | h6 | ha
    · -- endpoints
      have htE : t = .endpointObject := by
        have e := hn0; rw [h2] at e; simp [objTypeOf] at e; exact e.symm
      have hz4 : zOf nt.val us.val = 4 := by simp [zOf, h2]
      have h16 : (2 : Nat) ^ (zOf nt.val us.val) = 16 := by rw [hz4]; rfl
      refine ⟨_, ∅, ∅, ?_, fun _ h => h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => h2,
        fun _ h => by simp at h, fun _ h => by simp at h, fun q h => Or.inl h⟩
      simp only [Set.union_empty]
      exact XTopAt.addE hX' (Wn := winSet Aw (2 ^ (zOf nt.val us.val)) win.val)
        (fun e he => by rw [hspec e he, htE]; rfl)
        (fun e he => by
          obtain ⟨b1, b2, b3⟩ := hwb e he
          rw [h16] at b2 b3
          rw [Notif.epTSA_eq, Notif.epHeadA_eq]
          refine ⟨winZero_field hWZ' hTn he (by omega) (by omega) (by rw [h16]; simp) (by simp),
            winZero_field hWZ' hTn he (by omega) (by omega) (by rw [h16]; simp) (by simp)⟩)
        (fun e he => by obtain ⟨b1, b2, b3⟩ := hwb e he; rw [h16] at b2 b3; exact ⟨b3, by omega, by omega⟩)
        (fun e he t0 ht0 => by have := hTT e he t0 ht0; rw [h16] at this; exact this)
        (fun e he => by obtain ⟨b1, b2, -⟩ := hwb e he; rw [h16] at b2; rw [hksR]; omega)
        (fun e he b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb e he; rw [h16] at b2; exact hfr0 b (by omega) (by omega))
    · -- notifications
      have htN : t = .notificationObject := by
        have e := hn0; rw [h3] at e; simp [objTypeOf] at e; exact e.symm
      have hz6 : zOf nt.val us.val = 6 := by simp [zOf, h3]
      have h64 : (2 : Nat) ^ (zOf nt.val us.val) = 64 := by rw [hz6]; rfl
      refine ⟨∅, _, ∅, ?_, fun _ h => by simp at h, fun _ h => h, fun _ h => by simp at h, fun _ h => by simp at h,
        fun _ _ => h3, fun _ h => by simp at h, fun q h => Or.inr (Or.inl h)⟩
      simp only [Set.union_empty]
      exact XTopAt.addN hX' (Wn := winSet Aw (2 ^ (zOf nt.val us.val)) win.val)
        (fun n hn => by rw [hspec n hn, htN]; rfl)
        (fun n hn => by
          obtain ⟨b1, b2, b3⟩ := hwb n hn
          rw [h64] at b2 b3
          rw [Notif.epTSA_eq, Notif.epHeadA_eq, Notif.nBoundA_eq, Notif.nScA_eq]
          refine ⟨winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
            winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
            winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp),
            winZero_field hWZ' hTn hn (by omega) (by omega) (by rw [h64]; simp) (by simp)⟩)
        (fun n hn => by obtain ⟨b1, b2, b3⟩ := hwb n hn; rw [h64] at b2 b3; exact ⟨b3, by omega⟩)
        (fun n hn t0 ht0 => by have := hTT n hn t0 ht0; rw [h64] at this; exact this)
        (fun n hn => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; rw [hnbR]; omega)
        (fun n hn => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; rw [hksR]; omega)
        (fun n hn b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb n hn; rw [h64] at b2; exact hfr0 b (by omega) (by omega))
    · -- replies
      have htR : t = .replyObject := by
        have e := hn0; rw [h6] at e; simp [objTypeOf] at e; exact e.symm
      have hz5 : zOf nt.val us.val = 5 := by simp [zOf, h6]
      have h32 : (2 : Nat) ^ (zOf nt.val us.val) = 32 := by rw [hz5]; rfl
      refine ⟨∅, ∅, _, ?_, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => h, fun _ h => by simp at h,
        fun _ h => by simp at h, fun _ _ => h6, fun q h => Or.inr (Or.inr (Or.inl h))⟩
      simp only [Set.union_empty]
      exact XTopAt.addR hX' (Wn := winSet Aw (2 ^ (zOf nt.val us.val)) win.val)
        (fun r hr => by rw [hspec r hr, htR]; rfl)
        (fun r hr => by
          obtain ⟨b1, b2, b3⟩ := hwb r hr
          rw [h32] at b2 b3
          rw [rTcbA_eqW]
          exact winZero_field hWZ' hTn hr (by omega) (by omega) (by rw [h32]; simp) (by simp))
        (fun r hr => by obtain ⟨b1, b2, b3⟩ := hwb r hr; rw [h32] at b2 b3; exact ⟨b3, by omega, by omega⟩)
        (fun r hr t0 ht0 => by have := hTT r hr t0 ht0; rw [h32] at this; exact this)
        (fun r hr => by obtain ⟨b1, b2, -⟩ := hwb r hr; rw [h32] at b2; rw [hksR]; omega)
        (fun r hr b g1 g2 => by obtain ⟨b1, b2, -⟩ := hwb r hr; rw [h32] at b2; exact hfr0 b (by omega) (by omega))
    · -- VSpace tables: no set grows
      refine ⟨∅, ∅, ∅, ?_, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
        fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => Or.inr (Or.inr (Or.inr ha))⟩
      simp only [Set.union_empty]
      exact hX'
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
    intro j _; rw [hcj]; rcases hnt with h | h | h | h | h | h | h | h | h <;> simp [cjOf, newCapOf, h, isUt]
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
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject] at h2
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, hhas2, hthx2, hJP2⟩ :=
    Sched.JPlaced.retypeG (L := L) hJp J.jcov J.ut hI hM hksz hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by rcases hnt with h' | h' | h' | h' | h' | h' | h' | h' | h' <;> simp [newKind, h'] at h) (fun h => absurd h hn1) (fun h => absurd h hn1)
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
      (fun _ => Fl4Spec.defaultObject t false us.val σ.curDomain) := fun q _ => by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Fl4Spec.defaultObject]
  have hWnN : ∀ n ∈ Nn, n.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := fun n hn => hreg n (hNs hn)
  obtain ⟨hCR1, -, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J.uaRest hwI hA hIN hcnk hWnN
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
    rw [hspec r (hRs hr)]
    have h6 := hRt r hr
    have e := hty; rw [h6] at e; simp [objTypeOf] at e; subst e; rfl
  have hRz : ∀ r ∈ Rn, L.mem res.2.1 (P1.rNextA r) = 0#u64 ∧ L.mem res.2.1 (P1.rPrevA r) = 0#u64 := by
    intro r hr
    have h6 := hRt r hr
    have h32 : (2 : Nat) ^ zOf nt.val us.val = 32 := by simp [zOf, h6]
    obtain ⟨b1, b2, b3⟩ := hwb r (hRs hr)
    rw [h32] at b2 b3
    rw [rNextA_eqW, rPrevA_eqW]
    exact ⟨winZero_field hWZ' hTn (hRs hr) (by omega) (by omega) (by rw [h32]; simp) (by simp),
      winZero_field hWZ' hTn (hRs hr) (by omega) (by omega) (by rw [h32]; simp) (by simp)⟩
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
  obtain ⟨hRP1, hSA1⟩ := J.addRP hwI hA hIN hcnk hWnN (by omega) hU.pfit hU.free hspec1
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
    J.addSets (Z' := { Z with G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn }) hwI.1 (by omega) hU.pfit hU.free
      (by rcases k1 with h | h <;> omega) hspec1
      (fun wp hwp => hBF wp hwp _ hxG p sb fiv (capV_of_capAt hcap)) harch1 hA1 hA3 hE.k1 hout hEw0 hNw0 hRw0 hKn
      hback rfl rfl rfl rfl rfl rfl
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; rcases hnt with h | h | h | h | h | h | h | h | h <;> simp [cjOf, newCapOf, h]
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hb, objTypeOf_ep hty]; simp [Fl4Spec.defaultObject, Fl4Spec.objBits, zOf, Fl4Spec.endpointBits]
    · rw [hb, objTypeOf_ntfn hty]; simp [Fl4Spec.defaultObject, Fl4Spec.objBits, zOf, Fl4Spec.ntfnBits]
    · rw [hb, objTypeOf_reply hty]; simp [Fl4Spec.defaultObject, Fl4Spec.objBits, zOf, Fl4Spec.replyBits]
    all_goals exact le_refl _
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
  -- the window's tables added to `L3`, `L2` or `L1` (`XTopAt.addTab`): the
  -- new table caps are unmapped, so `JAtZ.vsc` asks their tables in the sets
  have hTw : ∀ q, (q ∈ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7} ∨
      q ∈ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13} ∨
      q ∈ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12}) →
      q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ (2 : Nat) ^ zOf nt.val us.val = 4096 ∧
        (nt.val = 7 ∨ nt.val = 13 ∨ nt.val = 12) := by
    rintro q (⟨hq, h⟩ | ⟨hq, h⟩ | ⟨hq, h⟩) <;> refine ⟨hq, ?_, by omega⟩ <;> simp [zOf, h]
  have hXT := XTopAt.addTab hXZ (W3 := {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7})
    (W2 := {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13})
    (W1 := {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12})
    (fun q ⟨hq, h⟩ => by
      have e := hty; rw [h] at e; simp [objTypeOf, Fl4Spec.archDataToObjType] at e
      subst e; rw [hspec q hq]; rfl)
    (fun q ⟨hq, h⟩ => by
      have e := hty; rw [h] at e; simp [objTypeOf, Fl4Spec.archDataToObjType] at e
      subst e; rw [hspec q hq]; rfl)
    (fun q ⟨hq, h⟩ => by
      have e := hty; rw [h] at e; simp [objTypeOf, Fl4Spec.archDataToObjType] at e
      subst e; rw [hspec q hq]; rfl)
    (fun q hq => by
      obtain ⟨hq, h4k, -⟩ := hTw q hq
      obtain ⟨-, -, b3⟩ := hwb q hq
      rw [h4k] at b3; exact b3)
    (fun q hq i hi => by
      obtain ⟨hq, h4k, -⟩ := hTw q hq
      obtain ⟨b1, b2, b3⟩ := hwb q hq
      rw [h4k] at b2 b3
      have hKv : (core.num.U64.wrapping_mul i 8#u64).val = i.val * 8 := by
        simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
      unfold peA
      exact winZero_field hWZ' hTn hq (by omega) (by rw [h4k]; omega) (by rw [h4k, hKv]; omega)
        (by rw [hKv]; omega))
    (fun q hq b g1 g2 => by
      obtain ⟨hq', h4k, hn⟩ := hTw q hq
      obtain ⟨b1, b2, -⟩ := hwb q hq'
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
          rcases hnt with h | h | h | h | h | h | h | h | h <;> simp [cjOf, newCapOf, h, Vs.SetFree] at hT ⊢
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
  -- the IPC-buffer words (UtFrameAdd): for frames, `B` grows by the new
  -- pages' 8-aligned words `(a, a)` (FL4's window zero, the spec's free part
  -- zero by `hZ0`); the old words naming a spec address in the window dropped
  -- (`EPlaced.binj`: none is a data page's, those lie off the free part)
  have hms : σ'.machineState = σ.machineState := by
    have e : (abs0 σ').machineState = (abs0 σB).machineState := congrArg _ hcnk.1
    exact e.trans hA.ms
  have hK8 : 2 ^ zOf nt.val us.val = 16 ∨ 2 ^ zOf nt.val us.val = 64 ∨ 2 ^ zOf nt.val us.val = 32 ∨
      2 ^ zOf nt.val us.val = 4096 ∨ 2 ^ zOf nt.val us.val = 1073741824 ∨ 2 ^ zOf nt.val us.val = 2097152 := by
    rcases hnt with h | h | h | h | h | h | h | h | h <;> simp [zOf, h]
  obtain ⟨Wn, hWn⟩ : ∃ Wn : U64 → Prop, ∀ a, Wn a ↔ (nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) ∧ Aw ≤ a.val ∧
      a.val + 8 ≤ Aw + win.val * 2 ^ zOf nt.val us.val ∧ a.val % 8 = 0 := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Set (U64 × Fl4Spec.Word), ∀ wp, wp ∈ B' ↔
      (wp ∈ Z.B ∧ ¬ (Aw ≤ wp.2.toNat ∧ wp.2.toNat < Aw + win.val * 2 ^ zOf nt.val us.val)) ∨
        (Wn wp.1 ∧ wp.2 = wp.1.bv) :=
    ⟨{wp | (wp ∈ Z.B ∧ ¬ (Aw ≤ wp.2.toNat ∧ wp.2.toNat < Aw + win.val * 2 ^ zOf nt.val us.val)) ∨
      (Wn wp.1 ∧ wp.2 = wp.1.bv)}, fun _ => Iff.rfl⟩
  have hBN : BNew Z.B B' Wn := fun wp hw => ((hB' wp).1 hw).imp_left And.left
  have hWr : ∀ a, Wn a → p.val + fiv.val ≤ a.val ∧ a.val + 8 ≤ p.val + 2 ^ sb.val := by
    intro a ha; obtain ⟨-, g1, g2, -⟩ := (hWn a).1 ha; omega
  have hWf : ∀ a, Wn a → nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11 := fun a ha => ((hWn a).1 ha).1
  have hfr0' : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ wp.1.val :=
    fun wp hw => hBF wp hw _ hxG p sb fiv (capV_of_capAt hcap)
  have hinj : ∀ wp ∈ B', ∀ wq ∈ B', (wp.1 = wq.1 ↔ wp.2 = wq.2) := by
    intro wp hw wq hq
    rcases (hB' wp).1 hw with ⟨hw1, hw2⟩ | ⟨hn1, e1⟩ <;> rcases (hB' wq).1 hq with ⟨hq1, hq2⟩ | ⟨hn2, e2⟩
    · exact J.ip.e.binj wp hw1 wq hq1
    · obtain ⟨-, g1, g2, -⟩ := (hWn _).1 hn2
      have := hfr0' wp hw1
      constructor <;> intro e <;> exfalso
      · have : wp.1.val = wq.1.val := by rw [e]
        omega
      · have : wp.2.toNat = wq.1.val := by rw [e, e2]; rfl
        exact hw2 ⟨by omega, by omega⟩
    · obtain ⟨-, g1, g2, -⟩ := (hWn _).1 hn1
      have := hfr0' wq hq1
      constructor <;> intro e <;> exfalso
      · have : wp.1.val = wq.1.val := by rw [e]
        omega
      · have : wq.2.toNat = wp.1.val := by rw [← e, e1]; rfl
        exact hq2 ⟨by omega, by omega⟩
    · rw [e1, e2]
      exact ⟨fun e => by rw [e], fun e => (UScalar.eq_equiv_bv_eq _ _).2 e⟩
  have hal : ∀ a, Wn a → a.val % 8 = 0 := fun a ha => ((hWn a).1 ha).2.2.2
  have hmem : ∀ a, Wn a → (L.mem res.2.1 a).bv = Endp.loadWordAt σ'.machineState.underlyingMemory a.bv := by
    intro a ha
    obtain ⟨-, g1, g2, g3⟩ := (hWn a).1 ha
    have h0 : L.mem res.2.1 a = 0#u64 := by
      rcases hWZ' a (by unfold P1.Aligned; omega) g1 (by omega) with h | ⟨h, -⟩
      · exact h
      · exact absurd h hTn
    have hw := hWr a ha
    rw [h0, hms, loadWordAt_zero8 (by have := hU.pfit; omega) (fun y y1 y2 => hZ0 y (by omega) (by omega))]
    rfl
  have hT' : ∀ a, Wn a → ∀ t ∈ Z.T, a.val < t.val ∨ t.val + 4096 ≤ a.val := by
    intro a ha t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    have := hWr a ha
    simp only [objSize] at *; omega
  have hE' : ∀ a, Wn a → ∀ e ∈ Z.E ∪ En, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val := by
    rintro a ha e (he | he)
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.ep e he
      have := hspec1 _ _ hx
      have := hWr a ha
      simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, UScalar.bv_toNat] at *; omega
    · have := hEt e he; have := hWf a ha; omega
  have hR' : ∀ a, Wn a → ∀ r ∈ Z.R ∪ Rn, a.val + 8 ≤ r.val ∨ r.val + 32 ≤ a.val := by
    rintro a ha r (hr | hr)
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
      have := hspec1 _ _ hx
      have := hWr a ha
      simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at *; omega
    · have := hRt r hr; have := hWf a ha; omega
  have hN' : ∀ a, Wn a → ∀ n ∈ Z.N ∪ Nn, a.val + 8 ≤ n.val ∨ n.val + 64 ≤ a.val := by
    rintro a ha n (hn | hn)
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.ntfn n hn
      have := hspec1 _ _ hx
      have := hWr a ha
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at *; omega
    · have := hNt n hn; have := hWf a ha; omega
  have hks' : ∀ a, Wn a → a.val + 8 ≤ (L.ksb res.2.1).val ∨ (L.ksb res.2.1).val + 13568 ≤ a.val := by
    intro a ha
    have := hWr a ha
    rw [hksR]; rcases k1 with h | h <;> omega
  have hfr' : ∀ a, Wn a → ∀ b : U64, a.val ≤ b.val → b.val < a.val + 8 →
      ¬ OObj st (Z.N ∪ Nn) Z.T Z.C (Z.E ∪ En) (Z.R ∪ Rn) Z.B Z.c res.2.1 σ' b ∧
      ¬ VObj Z.th Z.P Z.L4 (Z.L3 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7})
        (Z.L2 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13})
        (Z.L1 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12}) (L.ksb res.2.1) b := by
    intro a ha b g1 g2
    have hw := hWr a ha
    have hf := hWf a ha
    obtain ⟨n1, n2⟩ := hfr0 b (by omega) (by omega)
    refine ⟨fun ho => n1 ?_, fun hv => n2 ?_⟩
    · rcases oobj_unionR ho with ho | ⟨r, hr, -⟩
      · rcases oobj_unionN ho with ho | ⟨n, hn', -⟩
        · rcases oobj_unionE ho with ho | ⟨e, he, -⟩
          · exact ho
          · have := hEt e he; omega
        · have := hNt n hn'; omega
      · have := hRt r hr; omega
    · unfold VObj at hv ⊢
      rcases hv with h | h | ⟨q, hq, h1, h2⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr (Or.inl ⟨q, ?_, h1, h2⟩))
        rcases hq with hq | hq | (hq | ⟨-, hq⟩) | (hq | ⟨-, hq⟩) | (hq | ⟨-, hq⟩)
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hq))
        · omega
        · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
        · omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr hq)))
        · omega
      · exact Or.inr (Or.inr (Or.inr h))
  have hXB := hXT.chgB hBN hinj hal hmem hT' hE' hR' hks' hfr'
  have hEPB := hIp'.e.chgB hBN hinj hal hT' hE' hR'
  have hIpB := hIp'.chgB hBN hEPB hN'
  have hKsB := hKs'.chgB hBN hks'
  have hnB : ∀ wp ∈ B', ∀ c : U64, c.val < 64 →
      wp.1.val + 8 ≤ L.nodeBase res.2.1 c ∨ L.nodeBase res.2.1 c + 4288 ≤ wp.1.val := by
    intro wp hw c hc
    have hnbv : L.nodeBase res.2.1 c = (L.ksb s).val + 13568 + c.val * 4288 := by
      show (L.ksb res.2.1).val + 13568 + c.val * 4288 = _; rw [hksR]
    rw [hnbv]
    rcases (hB' wp).1 hw with ⟨hw1, -⟩ | ⟨hn, -⟩
    · have := J.nodeB wp hw1 c hc
      have e : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      rw [e] at this; exact this
    · have := hWr _ hn
      unfold UtNodesAt at hKN
      rcases hKN with h | h <;> omega
  -- the buffer fields (`JBuf`): `IpcBufCapOK` across the fresh objects (no
  -- TCB) and the CNode slots; `FrameCover` at `B'` (the old pages' words kept,
  -- the new pages' words added); the new frame caps name the new pages
  have hpg : ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) →
      σ'.kheap q = some (.archObj (.dataPage false vms)) :=
    fun q vms h => (IpcFrKeep.of_keepC hkc).page _ _ (hA.kold h)
  have hbok : Endp.IpcBufCapOK σ' :=
    (J.bok.specAdd hA (fun _ _ x e => htX _ x e)).keep (IpcFrKeep.of_keepC hkc)
  have hfcov : FrameCover B' σ' := by
    intro q vms hq a h1 h2 h3
    rcases hback q _ hq with h0 | ⟨r0, cs, cs', -, e⟩ | ⟨e0, -, -, e⟩ | ⟨n0, -, -, e⟩ | ⟨r0, -, -, e⟩ |
        ⟨q', hq', hqo, -, -⟩
    · refine (hB' _).2 (Or.inl ⟨J.fcov q vms h0 a h1 h2 h3, fun ⟨g1, g2⟩ => ?_⟩)
      have := hspec1 _ _ h0
      simp only [Fl4Spec.objBits, Fl4Spec.archKobjSize, UScalar.bv_toNat] at this g1 g2
      omega
    · cases e
    · cases e
    · cases e
    · cases e
    · subst hqo
      have hk := hspec q' hq'
      rw [hq] at hk
      obtain ⟨hfrm, hpb⟩ := frame_of_default hty htU (Option.some.inj hk).symm
      obtain ⟨b1, b2, -⟩ := winSet_bd hq'
      have hal' : q'.val % 2 ^ zOf nt.val us.val = 0 := (hwb q' hq').2.2
      have h1' : q'.val ≤ a.val := h1
      have h2' : a.val < q'.val + 2 ^ zOf nt.val us.val := by rw [← hpb]; exact h2
      refine (hB' _).2 (Or.inr ⟨(hWn a).2 ⟨hfrm, by omega, ?_, h3⟩, rfl⟩)
      rcases hK8 with e | e | e | e | e | e <;> rw [e] at h2' b2 hal' ⊢ <;> omega
  have hfcap : Vs.FrSlots Z.th (UFr σ') (L.mem res.2.1) := by
    obtain ⟨-, hCRZ, -⟩ := hXZ.rel
    refine J.fcap.retype hE hM hCRZ.2.2.1 (fun _ => UFr.keep hpg) (fun j hj => ?_)
    by_cases hfrm : nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11
    · obtain ⟨vms, sz, hdo, hpb, hfb, hnc⟩ := frame_new hty hfrm us.val
      obtain ⟨q, hqd⟩ : ∃ q : U64, q = ⟨BitVec.ofNat 64 (Aw + j * 2 ^ zOf nt.val us.val)⟩ := ⟨_, rfl⟩
      have hcjj : cj j = .Frame q sz 3#u64 false false false 0#u64 0#u64 := by
        rw [hcj, hqd]; exact hnc _ _
      have hpf : ptrF (.Frame q sz 3#u64 false false false 0#u64 0#u64) = q := ok_inj (ptr_eq _).symm
      have hqv : q.val = Aw + j * 2 ^ zOf nt.val us.val := by
        have := hE.cbase j hj
        unfold baseF at this
        rw [hcjj, hpf] at this; exact this
      have hqW : q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val := ⟨j, hj, hqv⟩
      have hk := hspec q hqW
      rw [hdo] at hk
      rw [hcjj]
      intro _ a h1 h2
      rw [hfb] at h2
      have hb := hwb q hqW
      have := hU.pfit
      exact ufr_new hk (by rw [hpb]; exact hb.2.2) h1 (by rw [hpb]; exact h2) (by omega)
    · rw [hcj]
      rcases hnt with h | h | h | h | h | h | h | h | h
      all_goals first | omega | simp [cjOf, newCapOf, h, Vs.FrIn]
  have hbf : JBuf (L := L) { Z with
      G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn,
      L3 := Z.L3 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7},
      L2 := Z.L2 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13},
      L1 := Z.L1 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12}, B := B' } res.2.1 σ' :=
    ⟨hbok, hfcov, hfcap⟩
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
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveN hXB rfl rfl rfl (fun _ _ h => h) (NewEmpty.refl _ _ _) hTH
    (dbgKeep_of_writes J.blk hwI fun _ hb => J.inSlot_notDbg hb)
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ (hC2.idle.trans hidB) hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frameB
    (Z' := { Z with
      G := G', E := Z.E ∪ En, N := Z.N ∪ Nn, R := Z.R ∪ Rn,
      L3 := Z.L3 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 7},
      L2 := Z.L2 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 13},
      L1 := Z.L1 ∪ {q | q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val ∧ nt.val = 12}, B := B' })
    rfl rfl hwI.1 hnB hXB ⟨hCs.del, hCs.ut, hCs.finM, hCs.sfree⟩
    ⟨hJR.call, hJR.rfree, hJR.rrecv, hJR.yld, hJR.mcp, hJR.buf, hJR.rp, hJR.apart, hJR.jpl, hJR.jcov, hJR.kern,
      hJR.utc, hJR.nsc, hJR.inv, hJR.cur, hJR.own, hJR.off, hJR.act, hJR.bsa, hJR.isorted, hJR.curRun, hJR.blk⟩
    hKsB J.thT hIpB hnk' hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hXZ.rel.2.1.2.2.1 (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _), J.ext.vkeep (J.vkeep_slot hwI)⟩ hLvN hzDN
  refine ⟨σ', hrun, hok, ⟨Z.th, G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hXZ.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', Lst, _, JZ⟩

set_option maxHeartbeats 4000000 in
/-- **The no-reset retype of endpoints, notifications, replies, VSpace
tables (PDPTs, page directories, page tables) or frames at `J`**
(module docstring; one core, `Z.c = 0`, for the replies' placement off the
nodes): from `JAtZ` at the decode (no reschedule pending), the decoded
arguments (`RetCtx`, no reset: the source cap has a child), the source a
CNode slot's RAM untyped cap, FL4's restart and `untyped::retype` end in
`UtRetPostJ` (done, `JAt` after). -/
theorem JAtZ.utEpJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11))
    (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r false fiv)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s)
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s)) (blk call don : Bool) :
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
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hks1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hms1 : σ1.machineState = σ.machineState := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hZ1 : UtFreeZ σ1 (p.val + fi.val) (p.val + 2 ^ sb.val) := fun a h1 h2 => by
    rw [hms1]; exact hUZ _ hxG p sb fi (capV_of_capAt hcap) a h1 h2
  have hKN1 : UtNodesAt (L.ksb s1) p sb := by rw [hks1]; exact hUN _ hxG p sb fi (capV_of_capAt hcap)
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
  exact WP.spec_mono (J1.utEpBodyJ hni1 hpp hidx hcap1 hnt hc0 hctx1 hfiv hBO1 hAF1 hRU1 hZ1 hKN1)
    (fun res h => utRetPostJ_of_body hst1 h)

variable (arI) in
/-- **[W] The retype of a RAM untyped at `J`, outside `JAtZ.utEpJ`'s case**
(XTopJointUt's `JUtRetHyp` narrowed): asked only with a reset (the source
cap childless) or of an object type other than endpoints, notifications,
replies, PDPTs, page tables, page directories, SCs, untypeds,
PML4s, CNodes and RAM frames (left: the VCPU/EPT types, also `JUtPath.vtx`
[scope]).
l4v: `invoke_untyped_corres` with `invoke_untyped_invs`. -/
def JUtRetHypR (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (sl : Fl4Spec.CslotPtr) (p sb fi ct : U64) (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi false nt us dest off win t r reset fiv →
    (reset = true ∨ (nt.val ≠ 2 ∧ nt.val ≠ 3 ∧ nt.val ≠ 6 ∧ nt.val ≠ 7 ∧ nt.val ≠ 12 ∧ nt.val ≠ 13 ∧
      nt.val ≠ 9 ∧ nt.val ≠ 10 ∧ nt.val ≠ 11 ∧
      nt.val ≠ 0 ∧ nt.val ≠ 5 ∧ nt.val ≠ 8 ∧ nt.val ≠ 4 ∧ nt.val ≠ 1)) →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄

/-- **`JUtRetHyp` from its narrowed form**: the no-reset retype of
endpoints, notifications, replies, VSpace tables (PDPT, PD, PT) or frames from a
CNode slot by `JAtZ.utEpJ`, of SCs by UtScRet's `JAtZ.utScJ`, of untypeds
by UtUtRet's `JAtZ.utUtJ`, of PML4s by UtPmRet's `JAtZ.utPmJ`, of CNodes by
UtCnRet's `JAtZ.utCnJ` (one
core, as `JUtPath.core0` [P]; with
`BufObjHyp`, `ArchFitHyp`, `RegionUnrefJ` [J]), the rest `JUtRetHypR` [W]. -/
theorem JAtZ.jUtRetHyp {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s))
    {blk call don : Bool} {argsU : List U64}
    (hR : JUtRetHypR (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU) :
    JUtRetHyp (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  by_cases h0 : reset = false ∧ nt.val = 0
  · obtain ⟨rfl, h0⟩ := h0
    obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    exact J.utUtJ hni hct hpp rfl hcap h0 hc0 hctx hBO hAF hRU blk call don
  by_cases h5 : reset = false ∧ nt.val = 5
  · obtain ⟨rfl, h5⟩ := h5
    obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    exact J.utScJ hni hct hpp rfl hcap h5 hc0 hctx hBO hAF hRU blk call don
  by_cases h8 : reset = false ∧ nt.val = 8
  · obtain ⟨rfl, h8⟩ := h8
    obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    exact J.utPmJ hni hct hpp rfl hcap h8 hc0 hctx hBO hAF hRU blk call don
  by_cases h4 : reset = false ∧ nt.val = 4
  · obtain ⟨rfl, h4⟩ := h4
    obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    exact J.utCnJ hni hct hpp rfl hcap h4 hc0 hctx hBO hAF hRU blk call don
  by_cases h1 : reset = false ∧ nt.val = 1
  · obtain ⟨rfl, h1⟩ := h1
    obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    exact J.utTcbJ hni hct hpp rfl hcap h1 hc0 hctx hBO hAF hRU blk call don
  by_cases hc : reset = true ∨ (nt.val ≠ 2 ∧ nt.val ≠ 3 ∧ nt.val ≠ 6 ∧ nt.val ≠ 7 ∧ nt.val ≠ 12 ∧ nt.val ≠ 13 ∧
      nt.val ≠ 9 ∧ nt.val ≠ 10 ∧ nt.val ≠ 11)
  · refine hR nt us dest off win t r reset fiv hh hctx ?_
    cases reset
    · rcases hc with h | ⟨g2, g3, g6, g7, g12, g13, g9, g10, g11⟩
      · exact Or.inl h
      · exact Or.inr ⟨g2, g3, g6, g7, g12, g13, g9, g10, g11,
          fun e => h0 ⟨rfl, e⟩, fun e => h5 ⟨rfl, e⟩, fun e => h8 ⟨rfl, e⟩,
          fun e => h4 ⟨rfl, e⟩, fun e => h1 ⟨rfl, e⟩⟩
    · exact Or.inl rfl
  have hrs : reset = false := by
    cases reset
    · rfl
    · exact absurd (Or.inl rfl) hc
  have hnt : nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) := by
    by_contra h
    exact hc (Or.inr (by omega))
  subst hrs
  obtain ⟨sl1, idx⟩ := sl
  obtain ⟨pp, hp1, hpp⟩ := hsl
  dsimp only at hp1 hpp
  subst hp1
  exact J.utEpJ hni hct hpp rfl hcap hnt hc0 hctx hBO hAF hRU hUZ hUN blk call don

end

end

end Fl4Proofs.P3
