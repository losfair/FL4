/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of TCBs at `J`**
(`JAtZ.utTcbJ`; handoff/utj.md "uttypes", ut37/ut39; l4v
`invoke_untyped_corres` with `retype_region` of `TCBObject`s, `default_tcb`
with `new_context`, seL4's `tcbDebugAppend`).

`JAtZ.utCnJ`'s skeleton for type 1. FL4's `retype` (`retype_cont_all`, and
`retype_full_tcbC` on the same call for the new TCBs' values `TcbC`) writes
slot words, the window (the new TCBs' creation words) and two debug-list
words: core 0's head word `DW` and the old head's `DEBUG_PREV`. The spec adds
the window's TCBs (`default_tcb 0`: one core, `SchedSpec.curDom`), then
changes CNodes. `T` grows by the window's TCBs `Wn`; the typed heap grows to
`th'`.

* `XTopAt`: the FL4 state split at the two debug words (`writesIn_split2`):
  `XTopAt.dbgStep` for them, then `XTopAt.addStepT` for the slot and window
  words, then `XTopAt.addT` (the new TCBs zero but their registers,
  `new_context`'s by `ctxW_newContext`, and their domain word, the current
  domain 0);
* the scheduler fields by `JAtZ.uaRestT` and the `addT` lemmas, `SlotsApart`
  by `sc_frame`, `grow`, `addT`;
* `JPlaced` by `JPlaced.retype` (`n = 1`), P1's creation by
  `JAtZ.create_noresetT` (`DbgLinksOK` from `TcbC`), `JKern` by
  `JKern.grow`, `JKern.keepH` (the head the last new TCB) and `JKern.hout`;
* the untyped caps by `JAtZ.ret_utcT` (`head_off_childless`) and
  `UtCapP3.growI`; the sets and heap by `JAtZ.addSetsT`; `JCs.retype`.
-/
import Fl4Proofs.P3.UtCnRet
import Fl4Proofs.P3.UtTcbRel
import Fl4Proofs.P3.UtTcbXTop
import Fl4Proofs.P3.UtTcbRest
import Fl4Proofs.P3.UtTcbP1
import Fl4Proofs.P3.UtTcbSets
import Fl4Proofs.P3.UtTcbUtc
import Fl4Proofs.P3.UtTcbLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A write frame split at two words**: the state with those two words set
to their values after (`L.wr`), reached by writing only them, and from which
the rest of the writes lead to the state after. -/
theorem writesIn_split2 {s s' : S} {P : U64 → Prop} {a1 a2 : U64} (h1 : P1.Aligned a1) (h2 : P1.Aligned a2)
    (h : P1.WritesIn st s s' (fun b => P b ∨ b = a1 ∨ b = a2)) :
    P1.WritesIn st s (L.wr (L.wr s a1 (L.mem s' a1)) a2 (L.mem s' a2)) (fun b => b = a1 ∨ b = a2) ∧
      P1.WritesIn st (L.wr (L.wr s a1 (L.mem s' a1)) a2 (L.mem s' a2)) s' P := by
  have hk : L.ksb (L.wr (L.wr s a1 (L.mem s' a1)) a2 (L.mem s' a2)) = L.ksb s := by
    rw [L.ksb_wr, L.ksb_wr]
  have hc : L.cpu (L.wr (L.wr s a1 (L.mem s' a1)) a2 (L.mem s' a2)) = L.cpu s := by
    rw [L.cpu_wr, L.cpu_wr]
  have hm : ∀ b, P1.Aligned b → L.mem (L.wr (L.wr s a1 (L.mem s' a1)) a2 (L.mem s' a2)) b =
      if a2 = b then L.mem s' a2 else if a1 = b then L.mem s' a1 else L.mem s b := by
    intro b hb; rw [L.mem_wr _ _ _ _ h2 hb, L.mem_wr _ _ _ _ h1 hb]
  refine ⟨⟨hk, hc, fun b hb hn => ?_⟩, ⟨h.1.trans hk.symm, h.2.1.trans hc.symm, fun b hb hn => ?_⟩⟩
  · rw [hm b hb, if_neg (fun e => hn (Or.inr e.symm)), if_neg (fun e => hn (Or.inl e.symm))]
  · rw [hm b hb]
    split_ifs with e2 e1
    · rw [e2]
    · rw [e1]
    · exact h.2.2 b hb (fun h' => h'.elim hn (fun h'' => h''.elim (fun e => e1 e.symm) (fun e => e2 e.symm)))

/-- **A slot of a new TCB is empty** after a TCB retype: its words lie below
the TCB's offset 256, where `WinZero` leaves no creation word. -/
theorem newSlot_nullT {th th' : TypedHeap} {A w n us : Nat} (hT : ThX th th' A 4096 w n us)
    (hk1 : thKindN n us = some .tcb) (hP' : Placed th') {m : U64 → U64} {T : Prop}
    (hWZ : WinZero m A 4096 w T) (hfit : A + w * 4096 ≤ 2 ^ 64) {p : U64} {i : Nat}
    (hi : IsSlotAt th' p i) (hpn : th p = none) : capV m (slotOf p i) = .Null := by
  obtain ⟨kd, hkd, hsz⟩ := hi.size
  rcases hT.casesI hkd with h1 | ⟨⟨j, hj, hpj⟩, h2⟩
  · rw [hpn] at h1; cases h1
  rw [hk1] at h2; cases h2
  have hit : i < tcbSlots := by
    rcases hi with ⟨r, hr, -⟩ | ⟨-, h⟩
    · rw [hkd] at hr; cases hr
    · exact h
  unfold tcbSlots at hit
  have hv := hi.val hP'
  have hjk : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hjk
  have hal : (slotOf p i).val % 32 = 0 := IsSlot.align hP' ⟨p, i, hi, rfl⟩
  have h8 : (wordOf (slotOf p i) 8#u64).val = (slotOf p i).val + 8 :=
    slot_word_val hP' ⟨p, i, hi, rfl⟩ (Or.inr (Or.inl rfl))
  have hz : ∀ v : U64, P1.Aligned v → p.val ≤ v.val → v.val < p.val + 256 → m v = 0#u64 := by
    intro v hv1 hv2 hv3
    rcases hWZ v hv1 (by omega) (by omega) with h | ⟨-, j', hj', hin⟩
    · exact h
    · exfalso
      obtain ⟨i1, i2, -⟩ := hin
      have hb := bT_v hj' hfit
      unfold bT at hb
      rw [hb] at i1 i2
      have : (j' + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj'
      omega
  refine capV_zero (hz _ (by unfold P1.Aligned; omega) (by omega) (by omega))
    (hz _ (slot_word_aligned hP' ⟨p, i, hi, rfl⟩ (Or.inr (Or.inl rfl))) (by rw [h8]; omega) (by rw [h8]; omega))

/-- **A block in an untyped cap's free part against another untyped cap**
(`UtInv`): off the other's range, or inside its used part (the other an
ancestor of the first). -/
theorem block_vs_other {mem : U64 → U64} {G : MdbGhost} (hU : UtInv mem G) {xs y : U64}
    (hxsG : xs ∈ G.chains.flatten) (hyG : y ∈ G.chains.flatten) (hne : y ≠ xs)
    {p0 sb0 fi0 p sb fi : U64} {d0 d : Bool}
    (hc0 : capV mem xs = .Untyped p0 sb0 fi0 d0) (hcy : capV mem y = .Untyped p sb fi d)
    {b1 b2 : Nat} (h1 : p0.val + fi0.val ≤ b1) (h2 : b2 ≤ p0.val + 2 ^ sb0.val) (h12 : b1 < b2) :
    (b2 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ b1) ∨ (p.val ≤ b1 ∧ b2 ≤ p.val + fi.val) := by
  have hph : physF (capV mem y) = true := by rw [hcy]; exact physF_ut _ _ _ _
  have r1 := hU.reg _ hyG hph
  have r0 := hU.reg _ hxsG (by rw [hc0]; exact physF_ut _ _ _ _)
  rw [hcy] at r1
  rw [hc0] at r0
  obtain ⟨b1', t1, -⟩ := ut_range (capV_ut_sb hcy) r1
  obtain ⟨b0, t0, -⟩ := ut_range (capV_ut_sb hc0) r0
  have hf0 := hU.fib _ hxsG _ _ _ _ hc0
  have : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
  have : 1 ≤ 2 ^ sb0.val := Nat.one_le_two_pow
  by_cases hd : Disj (capV mem y) (capV mem xs)
  · rw [hcy, hc0] at hd
    unfold Disj at hd
    rw [b1', t1, b0, t0] at hd
    left; omega
  · rcases hU.drange _ hxsG p0 sb0 fi0 d0 hc0 _ hyG hne hph hd with h | h
    · obtain ⟨-, i1, i2⟩ := hU.inc _ hxsG p0 sb0 fi0 d0 hc0 _ h
      rw [hcy, b1'] at i1
      rw [hcy, t1] at i2
      left; omega
    · obtain ⟨-, i1, i2⟩ := hU.inc _ hyG p sb fi d hcy _ h
      rw [hc0, b0] at i1
      rw [hc0, t0] at i2
      right; constructor <;> omega

/-- **The TCB retype without a reset from any state** (`retype_full_tcb` as
`RetPostB`; `retype_body` for type 1, `retype_cont_all`'s TCB case without
the restart): the window's frame the TCB creation loop's words. -/
theorem retype_body_tcb {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 1) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val + fi.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      RetPostB (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false) res ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hz47 : zOf nt.val us.val ≤ 47 := by simp [zOf, hnt]
  have htT : t = .tcbObject := by rw [hnt] at ht; simpa [objTypeOf] using ht.symm
  obtain ⟨hA1, hWA2, hA3, -⟩ := retype_region p fi sb.val (zOf nt.val us.val) win.val hsb (by omega) hpal hpfit hfi hw1 hmem
  have hsl : ∀ a, IsSlot th a → a.val + 32 ≤ (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ∨
      (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hzA : ZeroRegion (L.mem s) (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat
      ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val) :=
    fun w hw h1 h2 => hzero w hw (by omega) (by omega)
  refine WP.spec_mono (retype_full_tcb (L := L) arI ar th s σ G hR hV hP hM hC hI hU horig hpp hidx hcap
    hpal hpfit hfi hhigh nt us t ht hnt hus hdest hr off win hwin hw1 hmem hempty hfree hzero
    hDWal hDWobj hDWreg hhead bitsApi hb) ?_
  rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w,
    dslot, cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩
  refine ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt', hFin, hks, _, _, _, dslot, cj, hE,
    ⟨Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s, th, _, _,
      Or.inl ⟨rfl, rfl, rfl, rfl, fun h => by cases h⟩, le_rfl, le_rfl, hthx.2, fun a h => h,
      ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC, hWf.mono fun v hv => Or.inl (Or.inl ⟨htT, hv⟩),
      fun _ w hw e1 e2 => ((winZero_of_frame hWf hzA hsl ?_ ?_) w hw e1 e2).imp id (fun ⟨_, hj⟩ => ⟨htT, hj⟩),
      fun _ => hhead.imp id (fun h => h.1)⟩,
     fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩
  · intro h; exact hDWreg ⟨by omega, by omega⟩
  · intro hne h
    rcases hhead with e | ⟨hq, -⟩
    · exact hne e
    · have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hfree _ _ hq with h' | h' <;> omega

set_option maxHeartbeats 40000000 in
/-- **The body of `JAtZ.utTcbJ`: the TCB retype without a reset from a
`JAtZ` state** (module docstring; `JAtZ.utCnBodyJ` for type 1, one core,
`Z.c = 0`): FL4's `untyped::retype` with `reset = false` from the state
itself (after the restart, or after the restart and the reset), against the
spec's `invoke_untyped` without a reset from `σ`: `UtBodyPost` (`JAt` after at
`T` grown by the new TCBs, the typed heap grown by them). `RetCtx` with any
`reset` flag and `fiv = fi`, `Entered`, the kept references to a range of the
cap's free part (`hRU`). -/
theorem JAtZ.utTcbBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 1) (hc0 : Z.c = 0#u64)
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
  have ht : t = .tcbObject := by
    have e := hty; rw [hnt] at e; simpa [objTypeOf] using e.symm
  have htU : t ≠ .untyped := by rw [ht]; simp
  have htP : t ≠ .archObject .pml4Obj := by rw [ht]; simp
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  subst hfiv
  have hz12 : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  have hk4 : (2 : Nat) ^ zOf nt.val us.val = 4096 := by rw [hz12]; rfl
  -- no restart here: the state the body starts at (as the restart's state below)
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s) := SlotsSame.refl _ _
  have hk1 : L.ksb s = L.ksb s := rfl
  have hcpu1 : L.cpu s = L.cpu s := rfl
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb
    (by have := hctx.size.2.1; omega) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  -- the source cap and the debug-list words at the restart's state
  have hcap1 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fiv false) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hU1 := J.utc _ p sb fiv false hAs hcap1 rfl
  have hnd1 : Sched.NotDev (L.mem s) (cslotAddr (pp.bv, idx)) p sb fiv := Sched.notDev_ram (capV_of_capAt hcap1)
  obtain ⟨hP1, ⟨hSR1, hV1, hM1, hC1, hI1⟩, -, -, -, hIA1, -⟩ := J.xtop.rel
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  obtain ⟨Tr1, Cq1, hJp1⟩ := J.jpl
  obtain ⟨Q1, R1, hcq1, hss1⟩ := J.xtop.fin.1.1.1.lists
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, k2, -⟩ := J.jcov.ks _ hxG p sb fiv (capV_of_capAt hcap)
  have hfit := hU.pfit
  have hhigh := hU.high hnd
  have hks1 : L.ksb s = L.ksb s := hk1
  have hkf := J.kern.nodeFit
  have hDWv : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = (L.ksb s).val + 13568 + 88 := by
    rw [nodeAt_val' (by simp; omega) (by simp [layout.node.DEBUG_TCBS])]
    simp [layout.node.DEBUG_TCBS]
  have hCDv : (Sched.curDomA st s).val = (L.ksb s).val + 8 := Sched.curDomA_val hcq1.node
  have hkal := J.kern.ksbAl
  have hkfit := J.kern.ksbFit
  have hhd0 := J.kern.head
  have hh0H : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      H (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb := fun hne =>
    (hJp1.tcb _).1 (hhd0.resolve_left hne).1
  have hcd0 := hss1.curDom
  -- FL4's retype: `retype_cont_all` and `retype_full_tcbC` on the same call
  have hcont := retype_body_tcb (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx hcap
    hU.pal hU.pfit hU.fiLe (hU.high hnd) hU.free (hU.zero hnd) nt us t hty hnt hctx.size.1 hctx.cnode.1
    hctx.cnode.2.1 off win hctx.window.2.2 hctx.window.1 hctx.memory hctx.empty J.kern.dwAl J.kern.dwObj
    (fun h => (hU.dwReg hnd) ⟨by omega, h.2⟩) hhd0 Fl4Spec.fl4ObjBitsApi hb
  have hfull0 := retype_full_tcbC (L := L) arI ar Z.th s σ Z.G hSR1 hV1 hP1 hM1 hC1 hI1 J.ut J.kern.orig hpp hidx
    hcap1 hU.pal hU.pfit hU.fiLe hhigh nt us t hty hnt hctx.size.1 hctx.cnode.1 hctx.cnode.2.1 off win
    hctx.window.2.2 hctx.window.1 hctx.memory
    (fun i h1 h2 => by
      have hr := hctx.cnode.2.1
      have hw := hctx.window.2.2
      have hAi : AbsSlot Z.th (dest.bv, Fl4Spec.natToCref r i) :=
        ⟨dest, rfl, Or.inl (by rw [natToCref_length _ _ (by omega)]; exact hctx.cnode.1)⟩
      rw [← cslotAddr_natToCref dest.bv r i (by omega) (by omega), hSS1.capAt hAi.isSlot,
        cslotAddr_natToCref dest.bv r i (by omega) (by omega)]
      exact hctx.empty i h1 h2)
    hU1.free (hU1.zero hnd1) J.kern.dwAl J.kern.dwObj (fun h => (hU1.dwReg hnd1) ⟨by omega, h.2⟩) hhd0
    (fun hne => by
      have := J.kern.hnd _ .tcb (hh0H hne) 0#u64 J.kern.cs0
      simp only [HKind.bits, Nat.reducePow, P1.LawfulStore.nodeBase] at this
      unfold Rg; rw [hDWv]; simp at this ⊢; omega)
    (by unfold P1.Aligned; rw [hCDv]; omega)
    (fun h => by rw [hCDv, hks1] at h; rcases k1 with e | e <;> omega)
    (fun hne => by
      have := J.kern.hks _ .tcb (hh0H hne) (fun z h => by cases h)
      simp only [HKind.bits, Nat.reducePow] at this
      unfold Rg; rw [hCDv]; omega)
    (fun e => by have := congrArg UScalar.val e; rw [hCDv, hDWv] at this; omega)
    (fun a ha hin => hIA1.ks _ (by rw [hCDv]; omega) (by rw [hCDv]; omega) (by rw [hCDv]; omega) a ha hin)
    Fl4Spec.fl4ObjBitsApi hb
  have hfull : untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      TcbC (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) (L.mem s (Sched.curDomA st s))
        (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) win.val ⦄ :=
    WP.spec_mono hfull0 (fun res h => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hTC, -⟩, -⟩ := h
      exact hTC)
  refine WP.spec_mono (WP.spec_and hcont hfull) (fun res ⟨hRP, hTC⟩ => ?_)
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
    rw [hnt]; have e := hn0; rw [ht] at e; exact objTypeOf_tcb e
  subst hn0v
  have hk0 : thKindN nt.val us.val = some .tcb := by
    unfold thKindN; rw [if_pos hnt]
  have hposZ : ∀ q kd, Z.th q = some kd → 0 < objSize kd := by
    intro q kd h
    rcases J.thk q kd h with rfl | ⟨r0, rfl⟩
    · simp [objSize]
    · simp only [objSize]; positivity
  -- the window, with short names
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th th' (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hTC hA1 hA2 hA3
  have hk0' : 0 < 2 ^ zOf nt.val us.val := Nat.two_pow_pos _
  have hksk : ∀ kd, thKindN nt.val us.val = some kd → objSize kd ≤ 2 ^ zOf nt.val us.val := by
    rw [hk0]; intro kd h; cases h; simp only [objSize]; omega
  have hfitW : Aw + win.val * 4096 ≤ 2 ^ 64 := by rw [← hk4]; omega
  have hA3' : Aw + win.val * 4096 ≤ p.val + 2 ^ sb.val := by rw [← hk4]; exact hA3
  have hWZ' : WinZero (L.mem res.2.1) Aw (2 ^ zOf nt.val us.val) win.val (t = .tcbObject) := hWZ ⟨rfl, htP⟩
  have hWZ4 : WinZero (L.mem res.2.1) Aw 4096 win.val (t = .tcbObject) := by rw [← hk4]; exact hWZ'
  have hAal : Aw % 32 = 0 := by rw [hk4] at hA2; omega
  -- the debug-list words
  set DW := L.nodeAt s 0#u64 layout.node.DEBUG_TCBS with hDW
  set h0 := L.mem s DW with hh0
  have hDWal : P1.Aligned DW := J.kern.dwAl
  have hh0ok : h0 ≠ 0#u64 → TcbOk h0 := fun hne => (hhd0.resolve_left hne).2
  have hh0T : h0 ≠ 0#u64 → h0 ∈ Z.T := fun hne => J.thT _ (hhd0.resolve_left hne).1
  let a2 : U64 := if h0 = 0#u64 then DW else P1.dpA h0
  have ha2al : P1.Aligned a2 := by
    by_cases hz : h0 = 0#u64
    · show P1.Aligned (if h0 = 0#u64 then DW else P1.dpA h0); rw [if_pos hz]; exact hDWal
    · show P1.Aligned (if h0 = 0#u64 then DW else P1.dpA h0); rw [if_neg hz]; exact (dA_al (hh0ok hz)).2.2
  -- FL4's writes: slot words, the window, the two debug words
  have hwT : P1.WritesIn st s res.2.1 (fun b => InSlot Z.th b ∨
      ((Aw ≤ b.val ∧ b.val < Aw + win.val * 4096) ∨ b = DW ∨ b = a2)) := by
    refine ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn ?_)⟩
    rcases h with (⟨-, h⟩ | h) | ⟨h1, -⟩
    · rcases h with h | ⟨j, hj, hin⟩ | h | ⟨hne, hv⟩
      · exact Or.inl h
      · right; left
        obtain ⟨i1, i2, -⟩ := hin
        have hjv := bT_v hj hfitW
        unfold bT at hjv
        rw [hjv] at i1 i2
        have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
        constructor <;> omega
      · exact Or.inr (Or.inr (Or.inl h))
      · right; right; right
        show b = (if h0 = 0#u64 then DW else P1.dpA h0)
        rw [if_neg hne]; apply UScalar.eq_of_val_eq; rw [hv, dpA_v (hh0ok hne)]
    · exact Or.inl h
    · exact absurd h1 htP
  have hw0 : P1.WritesIn st s res.2.1 (fun b => (InSlot Z.th b ∨ (Aw ≤ b.val ∧ b.val < Aw + win.val * 4096)) ∨
      b = DW ∨ b = a2) :=
    ⟨hwT.1, hwT.2.1, fun b hb hn => hwT.2.2 b hb (fun h => hn (by
      rcases h with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)))⟩
  obtain ⟨hsA, hsB⟩ := writesIn_split2 hDWal ha2al hw0
  set sM := L.wr (L.wr s DW (L.mem res.2.1 DW)) a2 (L.mem res.2.1 a2) with hsM
  have hkM : L.ksb sM = L.ksb s := hsA.1
  -- the slots keep their words at the split state
  have hSSM : SlotsSame Z.th (L.mem s) (L.mem sM) := by
    intro x hx
    have hd : ¬ (x.val ≤ DW.val ∧ DW.val < x.val + 32) := J.kern.dwObj x hx
    have ha2s : ¬ (x.val ≤ a2.val ∧ a2.val < x.val + 32) := by
      by_cases hz : h0 = 0#u64
      · show ¬ (x.val ≤ (if h0 = 0#u64 then DW else P1.dpA h0).val ∧
          (if h0 = 0#u64 then DW else P1.dpA h0).val < x.val + 32)
        rw [if_pos hz]; exact hd
      · show ¬ (x.val ≤ (if h0 = 0#u64 then DW else P1.dpA h0).val ∧
          (if h0 = 0#u64 then DW else P1.dpA h0).val < x.val + 32)
        rw [if_neg hz, dpA_v (hh0ok hz)]
        have := (J.apart x hx).1 h0 (hh0T hz); omega
    have kw : ∀ o : U64, Off o → L.mem sM (wordOf x o) = L.mem s (wordOf x o) := fun o ho =>
      hsA.2.2 _ (slot_word_aligned hP1 hx ho) (fun h => by
        have hv := slot_word_val hP1 hx ho
        have := ho.lt
        rcases h with e | e
        · exact hd ⟨by rw [← e, hv]; omega, by rw [← e, hv]; omega⟩
        · exact ha2s ⟨by rw [← e, hv]; omega, by rw [← e, hv]; omega⟩)
    have k0 := kw 0#u64 (Or.inl rfl)
    rw [wordOf_zero] at k0
    exact ⟨k0, kw 8#u64 (Or.inr (Or.inl rfl)), kw 16#u64 (Or.inr (Or.inr (Or.inl rfl))),
      kw 24#u64 (Or.inr (Or.inr (Or.inr rfl)))⟩
  -- the spec's outcome: the window's TCBs added, then CNodes changed
  have hSR1' := J.xtop.rel.2.1.1
  obtain ⟨-, σB, hA, hcnk, hkc⟩ := invokeUntyped_noreset_add Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ htU htP {pp.bv, dest.bv} (Or.inl rfl)
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Or.inr rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1'.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1'.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (by
      intro q hq
      rw [hlen] at hq
      obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      rw [hb] at hq ⊢
      have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
      cases hq1 : σ.kheap (Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          (j * 2 ^ zOf nt.val us.val)) with
      | none => rfl
      | some ko =>
        exfalso
        obtain ⟨ko0, hko0, -⟩ := hksz _ _ hq1
        have h1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
        have hz1 := Nat.one_le_two_pow (n := zOf nt.val us.val)
        rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap) _ ko0 hko0 with h | ⟨h2, h3⟩
        · rw [hqv, ← eA] at h; omega
        · rw [hqv, ← eA] at h2 h3; omega)
    (.ok (), σ') (by rw [hrun]; rfl)
  have ho : ∀ q, q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∀ x n, Fl4Spec.defaultObject t false us.val σ.curDomain ≠ .schedContext x n := by
    intro q _ x n; rw [ht]; simp [Fl4Spec.defaultObject]
  have hks1' : L.ksb s = L.ksb s := hk1
  have hcjne : ∀ j, j < win.val → ∀ p a, cj j ≠ .Pml4 p true a := by
    intro j _ p a
    rw [hcj]
    simp [cjOf, newCapOf, hnt]
  have hksR : L.ksb res.2.1 = L.ksb s := hwT.1.trans hks1
  have hcpuR : L.cpu res.2.1 = L.cpu s := hwT.2.1.trans hcpu1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  obtain ⟨Q0, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  have hreg : ∀ q ∈ (winSet Aw (2 ^ (zOf nt.val us.val)) win.val), q.bv ∈ regionPtrs
      (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
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
      (by rw [← eA]; omega)]
    simp only [UScalar.bv_toNat]
    rw [← eA]; omega
  have hspecT : ∀ q ∈ (winSet Aw (2 ^ (zOf nt.val us.val)) win.val),
      σ'.kheap q.bv = some (.tcb (Fl4Spec.defaultTcb σ.curDomain)) := by
    intro q hq
    have hB := (hA.new _ (hreg q hq)).2
    rw [ht] at hB; simp only [Fl4Spec.defaultObject] at hB
    rcases hkc q.bv with e | ⟨r0, cs, cs', e1, e2⟩
    · exact e.trans hB
    · rw [hB] at e1; cases e1
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
  have hsc1 : ∀ (q : U64) y n, σ.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    obtain ⟨ko, hko, hty'⟩ := hksz _ _ hq
    exact ⟨ko, hko, objBits_of_aType_sc hty'⟩
  -- `XTopAt` after: the debug words (`dbgStep`), the slot and window words (`addStepT`), the new TCBs (`addT`)
  have hXM : XTopAt (L := L) AR Z sM ar σ := XTopAt.dbgStep J.xtop ⟨hsA.1, hsA.2.1, fun b hb hn =>
    hsA.2.2 b hb (fun h => hn (by
      rcases h with e | e
      · right; rw [e, hc0]
      · by_cases hz : h0 = 0#u64
        · right; rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_pos hz, hc0]
        · left; exact ⟨h0, hh0T hz, Or.inr (by rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_neg hz])⟩))⟩
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem sM) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    rw [hSSM.capAt hxs, hSS1.capAt hxs]
    exact retExp_pml4_backG hE hM hM' hcjne (IsSlot.thMono hThX hk0' hposZ hxs) hc
  have hX' := XTopAt.addStepT hXM hThX hksk hk0' hP' hposZ
    ⟨hsB.1, hsB.2.1, fun b hb hn => hsB.2.2 b hb (fun h => hn (h.elim (fun h => Or.inl (Sched.slotSpan_wd hP hb h))
      (fun h => Or.inr (by rw [hk4]; exact h))))⟩
    (fun b g1 g2 => J.free_noObj hAs hcap hBF (hkM.trans hks1) hsc1 b (by omega) (by omega))
    (by rw [hkM, hks1]; rcases k1 with h | h <;> omega)
    hA ho hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (by rw [hkM, hks1]; exact hSt.okv hMO0) hTS
  -- the new TCBs `Wn`
  have hA0 : 0 < Aw := by omega
  have hWv : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∃ j, j < win.val ∧ q = bT Aw j := by
    rintro q ⟨j, hj, e⟩
    exact ⟨j, hj, UScalar.eq_of_val_eq (by rw [e, bT_v hj hfitW, hk4])⟩
  have hWin : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, Aw ≤ q.val ∧ q.val + 4096 ≤ Aw + win.val * 4096 := by
    rintro q ⟨j, hj, e⟩
    rw [hk4] at e
    have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
    constructor <;> omega
  have hTB : ∀ j, j < win.val → P1.TcbAddr (bT Aw j) := by
    intro j hj
    have hv := bT_v hj hfitW
    have hal4 : Aw % 4096 = 0 := by rw [hk4] at hA2; exact hA2
    have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
    refine ⟨by rw [hv]; omega, by simp only [Nat.reducePow]; rw [hv]; omega, by simp only [Nat.reducePow]; rw [hv]; omega⟩
  have hzW : ∀ j, j < win.val → ∀ K : U64, 3328 ≤ K.val → K.val < 3600 → K.val ≠ 3432 → K.val ≠ 3576 →
      K.val ≠ 3584 → K.val % 8 = 0 → L.mem res.2.1 (core.num.U64.wrapping_add (bT Aw j) K) = 0#u64 := by
    intro j hj K g1 g2 g3 g4 g5 g6
    have hv : (core.num.U64.wrapping_add (bT Aw j) K).val = (bT Aw j).val + K.val :=
      Notif.tfield_val (hTB j hj) (by omega)
    have hbv := bT_v hj hfitW
    exact winZero_tcbF hWZ4 hfitW hj _ (by show _ % 8 = 0; rw [hv, hbv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)
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
  have hWT0 : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∉ Z.T := by
    intro q hq hT
    have hth : Z.th q = some .tcb := (hJp.tcb q).2 (J.zH.1 q hT)
    have := hU.free q .tcb hth
    have := hWin q hq
    simp only [objSize] at *; omega
  have hWC0 : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ∉ Z.C := by
    intro q hq hC
    obtain ⟨Q', R', -, hs'⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨x, n, hx, -⟩ := hs'.scs q hC
    have := hspec0 _ _ hx
    have := hWin q hq
    simp only [UScalar.bv_toNat] at *
    have := Nat.one_le_two_pow (n := Fl4Spec.objBits (.schedContext x n))
    omega
  have hXT := XTopAt.addT hX' (W := winSet Aw (2 ^ zOf nt.val us.val) win.val)
    (fun q hq => by rw [hspecT q hq, hcd0.1])
    (fun q hq => ⟨by obtain ⟨j, hj, rfl⟩ := hWv q hq; exact hTB j hj, hWT0 q hq⟩) hWC0 hc0
    (fun q hq K hK => by
      obtain ⟨j, hj, rfl⟩ := hWv q hq
      rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact (hTC.2.1 j hj).trans hcd0.2
      · exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun q hq => by
      obtain ⟨j, hj, rfl⟩ := hWv q hq
      refine ⟨?_, hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, fun r => ?_⟩
      · unfold Notif.tStA
        rw [show layout.tcb.STATE = 3328#u64 by unfold layout.tcb.STATE layout.tcb.F; rfl]
        exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · rw [badgeRegA_eq_regA]
        apply P1.eq_of_bv
        rw [hTC.1 j hj _ (regIdx_lt _), ctxW_newContext]
        decide
      · rw [hTC.1 j hj _ (regIdx_lt r)]; exact ctxW_newContext r)
    (fun q hq => by
      have := hWin q hq
      simp only [Nat.reducePow, hnbR]
      rcases k2c with h | h <;> omega)
    (fun q hq => by
      have := hWin q hq
      simp only [Nat.reducePow, hksR]; rcases k1 with h | h <;> omega)
    (fun q hq b g1 g2 => (J.free_noObj hAs hcap hBF hksR hsc b (by have := hWin q hq; omega)
      (by have := hWin q hq; omega)).1)
    (fun q hq b g1 g2 hv => by
      have hold := (J.free_noObj hAs hcap hBF hksR hsc b (by have := hWin q hq; omega)
        (by have := hWin q hq; omega)).2
      rcases hv with ⟨q', r', hq', h1, h2⟩ | ⟨t', ht', h1, h2⟩ | h | h
      · rcases hThX.casesI hq' with h' | ⟨-, hk'⟩
        · exact hold (Or.inl ⟨q', r', h', h1, h2⟩)
        · rw [hk0] at hk'; cases hk'
      · rcases hThX.casesI ht' with h' | ⟨⟨j', hj', e'⟩, -⟩
        · exact hold (Or.inr (Or.inl ⟨t', h', h1, h2⟩))
        · obtain ⟨j, hj, e⟩ := hq
          rw [hk4] at e e'
          omega
      · exact hold (Or.inr (Or.inr (Or.inl h)))
      · exact hold (Or.inr (Or.inr (Or.inr h))))
  -- the spec side
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_co Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ htU htP (.ok (), σ') (by rw [hrun]; rfl)
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ.kheap o = σ.kheap o := fun _ _ => rfl
  have hσ1c : ∃ y, σ.kheap (L.curW s).bv = some (.tcb y) := by
    obtain ⟨-, x, hkx, -⟩ := J.curRunnable hni (cur_thread_eq s); exact ⟨x, hkx⟩
  have hσ1cdt : σ.cdt = σ.cdt := rfl
  have hct1 : σ.curThread = σ.curThread := rfl
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
  have hidl2 : IdleKeep (L := L) s res.2.1 :=
    J.idleW_keep hX'.fin.1.1.1 (hC2.idle.trans hidB) (hC2.isc.trans hiscB)
  have hidl : IdleKeep (L := L) s res.2.1 := hidl2
  -- P1's creation: the heap after, `BlkOK`, `JCovD`
  have hcjU : ∀ j, j < win.val → isUt (cj j) = false := by
    intro j _; rw [hcj]; simp [cjOf, newCapOf, hnt, isUt]
  obtain ⟨H', Ac', hblk', hout, hjc'⟩ := J.create_noresetTB hni hpp hidx hcap hE (hRU _ _ hA1 hA3)
    (n := nt.val) (us := us.val) (fun _ => hcjU) hnt hk4 hAk ht htP hW hWZ' hTC hctx.window.1 hidl
  -- `JPlaced` after
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
    · by_cases ho : o = (L.curW s).bv
      · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h1; cases h1
      · rw [hσ1k o ho, h0] at h1; cases h1
    · rw [ht] at h2; simp [Fl4Spec.defaultObject] at h2
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, hhas2, hthx2, hJP2⟩ :=
    Sched.JPlaced.retypeG (L := L) hJp J.jcov J.ut hI hM hksz hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by simp [newKind, hnt] at h) (fun _ => rfl) (fun _ => by rw [hb, hk4])
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
  -- `JKern` after: grown at the restart's state, the head the last new TCB, `H'`
  have hDWres : L.mem res.2.1 DW = bT Aw (win.val - 1) := by
    rw [hTC.2.2.2.2.2.2, if_neg (by have := hctx.window.1; omega)]
  have hheadR : L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th' (L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))) := by
    right
    have hw1 := hctx.window.1
    show th' (L.mem res.2.1 DW) = some .tcb ∧ TcbOk (L.mem res.2.1 DW)
    rw [hDWres]
    refine ⟨?_, bT_ok (by omega) hfitW hAal⟩
    rw [hThX.1, if_pos ⟨⟨win.val - 1, by omega, by rw [bT_v (by omega) hfitW, hk4]⟩, by rw [hk0]; rfl⟩, hk0]
  have K0 := J.kern.grow hThX hksk hk0' hposZ hP'
    (by rw [P1.nodeAt_of_ksb hks1, hcpu1]; rintro ⟨g1, g2⟩; exact (hU.actZ hnd) ⟨by omega, by omega⟩)
    (by rw [P1.nodeAt_of_ksb hks1]; rintro ⟨g1, g2⟩; exact (hU.dwReg hnd) ⟨by omega, by omega⟩)
  have horig' : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot th' sl := fun sl h =>
    (horig sl h).imp id (AbsSlot.thMono hThX hk0' hposZ)
  have K1 := K0.keepH (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) J.xtop.fin.1.1.1
    hwT.1 hwT.2.1 hX'.fin.1.1.1 (hC2.ct.trans hctB) (hC2.csc.trans hcscB) horig' hgp' hao hheadR
  have hRD := (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fiv, capV_of_capAt hcap⟩).1
  have hoffD : ∀ q kd, H q = some kd → q ∉ D → H' q = some kd := fun q kd hq hqD =>
    hout_old hout rfl rfl hE.k1 hq (by
      by_contra hm
      exact hqD (hRD q kd hq (by unfold MeetsW; omega)).1)
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have hcs1 : L.cscW s = L.cscW s := rfl
  have hcsR : L.cscW res.2.1 = L.cscW s :=
    cscW_of_sched J.xtop.fin.1.1.1 hX'.fin.1.1.1 hwT.1 hwT.2.1 (hC2.csc.trans hcscB)
  have hcscH : H' (L.cscW res.2.1) ≠ none := by
    rw [hcsR, hcs1]
    obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 J.kern.cscH
    rw [hoffD _ kd hkd (J.cscLive.resolve_right hres)]; simp
  have ecw : L.curW res.2.1 = L.curW s :=
    P1.eq_of_bv (K1.cur.symm.trans ((hC2.ct.trans hctB).trans J.kern.cur))
  have hcurR : (L.curW res.2.1).val + 2 ^ 12 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ (L.curW res.2.1).val := by
    have := hU.free _ .tcb J.kern.curT; rw [ecw]; simp only [objSize] at this; omega
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
  have K2 := K1.hout (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hJPa.heap hout hE.k1 hA0
    hnewK hcurR hcscH
  -- the untyped caps' facts after
  have hthM : ∀ a, IsSlot Z.th a → IsSlot th' a := fun a ha => IsSlot.thMono hThX hk0' hposZ ha
  have hThX4 : ThX Z.th th' Aw 4096 win.val nt.val us.val := by rw [← hk4]; exact hThX
  obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1u, -, hAf1, -, -, -⟩ := hE.usrc
  rw [capV_of_capAt hcap] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp0, hsb0, hfi0, hd0⟩ := e0
  subst p0 sb0 fi0 d0
  have hAf4 : Aw + win.val * 4096 ≤ p.val + fi1.val := by rw [← hk4]; exact hAf1
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
        · rw [hcdtK d hdW, hσ1cdt] at hcd
          have hdA0 : AbsSlot Z.th d := by
            cases hq : σ.cdt d with
            | none => rw [hq] at hcd; cases hcd
            | some q0 => exact (hC.cdt_slot d q0 hq).1
          have hcd0 := hC.cdt d hdA0
          rw [hdy, hcd] at hcd0
          exact hyG (hM.tree.par_mem _ _ hcd0.symm).1
  have hDL : DestLive Z.th (L.mem s) (L.ksb s) dest := by
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact DestLive.same (Or.inl ⟨y, rr, gs, g, hy, capV_of_capAt hcy⟩) hSS1 hk1
  have hM'Z : MdbLinks Z.th (L.mem res.2.1) G' := hM'.shrink (fun a ha hn => by
      obtain ⟨q, i, hqi, rfl⟩ := ha
      by_cases hq : Z.th q = none
      · exact absurd (newSlot_nullT hThX4 hk0 hP' hWZ4 hfitW hqi hq) hn
      · obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 hq
        have e : th' q = Z.th q := by rw [hThX.mono hk0' hposZ hkd, hkd]
        refine ⟨q, i, ?_, rfl⟩
        rcases hqi with ⟨r0, h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨r0, by rw [← e]; exact h1, h2⟩
        · exact Or.inr ⟨by rw [← e]; exact h1, h2⟩) hthM
  have hs1G : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM1.members _).2 ⟨hAs.isSlot, _, hcap1, by simp⟩
  have hh0T' : h0 ≠ 0#u64 → Z.th h0 = some .tcb := fun hne => (hhd0.resolve_left hne).1
  have hutc := J.ret_utcT (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => (hSS1.capAt (hslA d hd).1.isSlot).trans (hDn0 d hd)) hDu hcapK hwT
    (fun b hb => by
      rcases hb with ⟨g1, g2⟩ | e | e
      · left; omega
      · have : ¬ (p.val ≤ DW.val ∧ DW.val < p.val + 2 ^ sb.val) := hU1.dwReg hnd1
        rw [e]; omega
      · by_cases hz : h0 = 0#u64
        · have e' : b = DW := by rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_pos hz]
          have : ¬ (p.val ≤ DW.val ∧ DW.val < p.val + 2 ^ sb.val) := hU1.dwReg hnd1
          rw [e']; omega
        · have e' : b.val = h0.val + 3584 := by
            rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0).val = _; rw [if_neg hz, dpA_v (hh0ok hz)]
          have := hU1.free _ .tcb (hh0T' hz); simp only [objSize] at this; omega)
    (fun sl1 p1 sb1 fi2 hsl1 hne hcv1 b hb => by
      have hm1 : cslotAddr sl1 ∈ Z.G.chains.flatten :=
        (hM1.members _).2 ⟨hsl1.isSlot, _, capAt_capV _ _, by rw [hcv1]; simp⟩
      have U' := J.utc sl1 p1 sb1 fi2 false hsl1 (by rw [capAt_capV, hcv1]) rfl
      have nd' : Sched.NotDev (L.mem s) (cslotAddr sl1) p1 sb1 fi2 := Sched.notDev_ram hcv1
      rcases hb with ⟨g1, g2⟩ | e | e
      · exact ut_free_other J.ut hm1 hs1G hne hcv1 (capV_of_capAt hcap1) (b := b.val) (by omega) (by omega)
      · have : ¬ (p1.val ≤ DW.val ∧ DW.val < p1.val + 2 ^ sb1.val) := U'.dwReg nd'
        rw [e]; omega
      · by_cases hz : h0 = 0#u64
        · have e' : b = DW := by rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_pos hz]
          have : ¬ (p1.val ≤ DW.val ∧ DW.val < p1.val + 2 ^ sb1.val) := U'.dwReg nd'
          rw [e']; omega
        · have e' : b.val = h0.val + 3584 := by
            rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0).val = _; rw [if_neg hz, dpA_v (hh0ok hz)]
          have := U'.free _ .tcb (hh0T' hz); simp only [objSize] at this; omega)
    (fun sl1 p1 sb1 fi2 hsl1 hne hcv1 hnc => by
      show ¬ (p1.val ≤ (L.mem res.2.1 DW).val ∧ (L.mem res.2.1 DW).val < p1.val + 2 ^ sb1.val)
      have hw1 := hctx.window.1
      have hjk : (win.val - 1 + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hjk
      rw [hDWres]
      exact head_off_childless hP1 hM1 hC1 J.ut hs1G (capV_of_capAt hcap1) hsl1 hne hcv1 hnc
        (by rw [bT_v (by omega) hfitW]; omega) (by rw [bT_v (by omega) hfitW]; omega))
    hcdtK horgK hgp' hM'Z
    (RetExp.src_child hE hctx.window.1 hP' hC' (AbsSlot.thMono hThX hk0' hposZ hAs))
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- `SpecFree` after, then the untyped caps at the grown heap
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd
    rw [hb, hz12, ht]
    simp [Fl4Spec.defaultObject, Fl4Spec.objBits, Fl4Spec.tcbBits]
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype J.sfree J.ut hksz (capV_of_capAt hcap) rfl hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hutc' : ∀ sl p1 sb1 fi2 dev, AbsSlot th' sl → capAt (L.mem res.2.1) (cslotAddr sl) = ok (.Untyped p1 sb1 fi2 dev) →
      dev = false → Sched.UtCapP3 (L := L) arI th' res.2.1 σ' G' sl p1 sb1 fi2 := by
    intro sl p1 sb1 fi2 dev hsl hc hd
    subst hd
    obtain ⟨q, i, hqi, hq1, he⟩ := hsl.at
    by_cases hq : Z.th q = none
    · exfalso
      have h0 := newSlot_nullT hThX4 hk0 hP' hWZ4 hfitW hqi hq
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
        (q0.val + 4096 ≤ p1.val ∨ p1.val + 2 ^ sb1.val ≤ q0.val) ∨
        (p1.val ≤ q0.val ∧ q0.val + 4096 ≤ p1.val + fi2.val) := by
      rintro q0 ⟨j, hj, e⟩
      rw [hk4] at e
      have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
      by_cases hsx : cslotAddr sl = cslotAddr (pp.bv, idx)
      · rw [hsx, e1u] at hcv
        simp only [capability.Cap.Untyped.injEq] at hcv
        obtain ⟨rfl, rfl, rfl, -⟩ := hcv
        right; constructor <;> omega
      · by_cases hdW : ∃ d ∈ windowSlots dest r off.val win.val, cslotAddr sl = cslotAddr d
        · obtain ⟨d, hd, e'⟩ := hdW
          rw [e'] at hcv; exact absurd hcv (hDu d hd p1 sb1 fi2 false)
        · push_neg at hdW
          have hcv1 : capV (L.mem s) (cslotAddr sl) = .Untyped p1 sb1 fi2 false := by
            rw [← hcapK _ hAs0.isSlot hsx (fun d hd => hdW d hd)]; exact hcv
          have hm1 : cslotAddr sl ∈ Z.G.chains.flatten :=
            (hM1.members _).2 ⟨hAs0.isSlot, _, capAt_capV _ _, by rw [hcv1]; simp⟩
          exact block_vs_other J.ut hs1G hm1 hsx (capV_of_capAt hcap1) hcv1 (b1 := q0.val) (b2 := q0.val + 4096)
            (by omega) (by omega) (by omega)
    refine (hutc sl p1 sb1 fi2 false hAs0 hc rfl).growI hThX hk0' hposZ (fun q0 hq0 kd0 hk => ?_)
      (fun q0 hq0 kd0 hk => ?_)
    · rw [hk0] at hk; cases hk; simp only [objSize]; rcases hobj q0 hq0 with (h | h) | h <;> omega
    · rw [hk0] at hk; cases hk; simp only [objSize]; rcases hobj q0 hq0 with (h | h) | h <;> omega
  -- the spec's invariants and the call stacks (`uaRestT`), the new TCBs
  have hIN : IdleNewT (fun q => q ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val))
      (fun _ => Fl4Spec.defaultObject t false us.val σ.curDomain) := fun q _ => by
    rw [ht]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))))
  have hcW : ¬ σ.curThread ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := fun h => by
    have e := (hA.new _ h).1
    rw [hct1, J.kern.cur] at e
    obtain ⟨y, hy⟩ := hσ1c; rw [hy] at e; cases e
  have hWT : ∀ b : U64, ((Aw ≤ b.val ∧ b.val < Aw + win.val * 4096) ∨ b = DW ∨ b = a2) → ∀ t0 ∈ Z.T,
      b.val < t0.val ∨ t0.val + 4096 ≤ b.val ∨ b.val = t0.val + 3584 := by
    intro b hb t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have hH : H t0 = some .tcb := J.zH.1 t0 ht0
    have hnd0 := J.kern.hnd t0 .tcb hH 0#u64 J.kern.cs0
    simp only [HKind.bits, Nat.reducePow, P1.LawfulStore.nodeBase] at hnd0
    rcases hb with ⟨g1, g2⟩ | e | e
    · have := hU.free t0 .tcb hth; simp only [objSize] at this; omega
    · rw [e, hDWv]; simp at hnd0; omega
    · by_cases hz : h0 = 0#u64
      · have e' : b = DW := by rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_pos hz]
        rw [e', hDWv]; simp at hnd0; omega
      · have e' : b.val = h0.val + 3584 := by
          rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0).val = _; rw [if_neg hz, dpA_v (hh0ok hz)]
        by_cases htq : t0 = h0
        · subst htq; right; right; exact e'
        · have hd := J.kern.heap.disj t0 .tcb _ .tcb hH (hh0H hz) htq
          simp only [HKind.bits, Nat.reducePow] at hd; omega
  have hWC : ∀ b : U64, ((Aw ≤ b.val ∧ b.val < Aw + win.val * 4096) ∨ b = DW ∨ b = a2) → ∀ q ∈ Z.C, ∀ x n,
      σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val := by
    intro b hb q hq x n hx
    by_contra hcn
    push_neg at hcn
    obtain ⟨-, o2, o3, -⟩ := J.xtop.fin.1.1.1.scOut q hq x n hx b ⟨hcn.1, hcn.2⟩
    rw [hc0] at o2
    simp only [P1.LawfulStore.nodeBase] at o2
    rcases hb with ⟨g1, g2⟩ | e | e
    · have := hspec1 _ _ hx
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this; omega
    · rw [e, hDWv] at o2; simp at o2
    · by_cases hz : h0 = 0#u64
      · have e' : b = DW := by rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_pos hz]
        rw [e', hDWv] at o2; simp at o2
      · have e' : b.val = h0.val + 3584 := by
          rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0).val = _; rw [if_neg hz, dpA_v (hh0ok hz)]
        have := o3 h0 (hh0T hz); omega
  have hWR : ∀ b : U64, ((Aw ≤ b.val ∧ b.val < Aw + win.val * 4096) ∨ b = DW ∨ b = a2) → ∀ r0 ∈ Z.R,
      b.val < r0.val ∨ r0.val + 32 ≤ b.val := by
    intro b hb r0 hr0
    have hk' := J.rp.ksb r0 hr0
    rw [hc0] at hk'
    simp only [P1.LawfulStore.nodeBase] at hk'
    rcases hb with ⟨g1, g2⟩ | e | e
    · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r0 hr0
      have := hspec1 _ _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
    · rw [e, hDWv]; simp at hk'; omega
    · by_cases hz : h0 = 0#u64
      · have e' : b = DW := by rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_pos hz]
        rw [e', hDWv]; simp at hk'; omega
      · have e' : b.val = h0.val + 3584 := by
          rw [e]; show (if h0 = 0#u64 then DW else P1.dpA h0).val = _; rw [if_neg hz, dpA_v (hh0ok hz)]
        have := J.rp.tcb r0 hr0 h0 (hh0T hz); omega
  obtain ⟨hCR1, hRP1, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1⟩ :=
    J.uaRestT hwT hWT hWC hWR hA hIN hcnk (Nn := ∅) (fun _ h => by simp at h) hcW
  rw [Set.union_empty] at hNSC1
  have hkW : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∃ d, σ'.kheap q.bv = some (.tcb (Fl4Spec.defaultTcb d)) :=
    fun q hq => ⟨_, hspecT q hq⟩
  have hY2 := hY1.addT hkW (fun q hq => by
    obtain ⟨j, hj, rfl⟩ := hWv q hq
    exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hMc2 := hMc1.addT hkW (fun q hq => by
    obtain ⟨j, hj, rfl⟩ := hWv q hq
    exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hBw2 := hBw1.addT hkW (fun q hq => by
    obtain ⟨j, hj, rfl⟩ := hWv q hq
    exact hzW j hj _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hOwn2 := hOwn1.monoT (W := winSet Aw (2 ^ zOf nt.val us.val) win.val)
  have hRP2 := hRP1.addT (W := winSet Aw (2 ^ zOf nt.val us.val) win.val) (fun r0 hr0 t0 ht0 => by
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r0 hr0
    have := hspec1 _ _ hx
    have := hWin t0 ht0
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at *; omega)
  have hsz := uaSzKeepT hA hIN hC2
  have hSA1 := J.apart.sc_frame hwT.1 hsz
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
  have hSA2 := hSA1'.addT (W := winSet Aw (2 ^ zOf nt.val us.val) win.val) (fun a ha t0 ht0 => by
    obtain ⟨j, hj, rfl⟩ := hWv t0 ht0
    have hbv := bT_v hj hfitW
    have hjk : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
    obtain ⟨q, i, hqi, rfl⟩ := ha
    have hv := hqi.val hP'
    obtain ⟨kd, hkd, hsz'⟩ := hqi.size
    rcases hThX.casesI hkd with h1 | ⟨⟨j', hj', e'⟩, h2⟩
    · have := hThX.2 q kd h1
      rw [hk4] at this
      omega
    · rw [hk0] at h2; cases h2
      rw [hk4] at e'
      have hit : i < tcbSlots := by
        rcases hqi with ⟨r0, hr, -⟩ | ⟨-, h⟩
        · rw [hkd] at hr; cases hr
        · exact h
      unfold tcbSlots at hit
      omega)
  -- the set and heap fields (`addSetsT`)
  have harch1 : ArchFitHyp H σ := hAF
  have hout' : HOut H H' Aw (Aw + win.val * 2 ^ zOf nt.val us.val) Aw (2 ^ zOf nt.val us.val) win.val (some .tcb) := by
    have e : newKind nt.val us.val = some .tcb := by simp [newKind, hnt]
    rw [← e]; exact hout
  have hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨ (∃ r cs', ko = .cnode r cs') ∨
      (∃ t ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, t.bv = o ∧ ∃ d, ko = .tcb (Fl4Spec.defaultTcb d)) := by
    intro o ko hk
    rcases hkc o with e | ⟨r0, cs, cs', -, e2⟩
    · rcases hA.kback (e.symm.trans hk) with h1 | ⟨hw, h2⟩
      · exact Or.inl h1
      · rw [ht] at h2; simp only [Fl4Spec.defaultObject] at h2
        right; right
        have hw' := hw
        rw [hlen, hb] at hw'
        obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hw'
        have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at hjk
        refine ⟨⟨Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (j * 2 ^ zOf nt.val us.val)⟩,
          ⟨j, hj, ?_⟩, rfl, _, h2⟩
        show (Fl4Spec.ptrAdd _ _).toNat = _
        rw [ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (n := j * 2 ^ zOf nt.val us.val)
          (by rw [← eA]; omega), ← eA]
    · rw [e2] at hk; cases hk; exact Or.inr (Or.inl ⟨r0, cs', rfl⟩)
  obtain ⟨hKs', hIp', hnk', hcov', hobj', hzH', hset', hscC'⟩ :=
    J.addSetsT (Z' := { Z with th := th', G := G', T := Z.T ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val })
      hwT.1 hU.free hspec1 (fun wp hwp => hBF wp hwp _ hxG p sb fiv (capV_of_capAt hcap)) harch1 hA1 hA3 hE.k1 hout'
      (fun t0 ht0 => ⟨by obtain ⟨j, hj, rfl⟩ := hWv t0 ht0; exact hTB j hj, by have := hWin t0 ht0; omega,
        by have := hWin t0 ht0; omega, ht0⟩) hback rfl rfl rfl rfl rfl rfl
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  have hCs : JCs (L := L) { Z with th := th', G := G', T := Z.T ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val }
      res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun p1 zt n1 h => by
      rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact Or.inl ⟨a, hThX.mono hk0' hposZ b, c⟩
      · exact Or.inr ⟨a, hThX.mono hk0' hposZ b, c⟩) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with th := th', G := G', T := Z.T ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val }
      H' Cs Ac' Lst {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1, hRF1, hRR1, hY2, hMc2, hBw2, hRP2, hSA2, ⟨_, _, hJPa⟩, hjc', K2, hutc', hNSC1, hInv1, hCur1, hOwn2,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  have hintL : IntLayout th' (L.ksb res.2.1) := by
    rw [hwT.1]
    exact IntLayout.grow J.intL hThX hksk hk0' hposZ (by rw [hks1]; rcases k1 with h | h <;> omega)
  -- the VSpace caps placed (`JAtZ.vsc`): an old cap kept or an untyped cap, a new cap (a TCB cap) set-free
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
  -- the buffer fields (`JBuf`): fresh TCBs (null IPC frames), then CNode slots; the new caps TCB caps
  have hfk : IpcFrKeep σ σ' :=
    (IpcFrKeep.of_specAdd hA (fun _ _ x e => by rw [ht] at e; cases e; rfl)
      (fun _ _ vms e => by rw [ht] at e; cases e)).trans (IpcFrKeep.of_keepC hkc)
  have hbf : JBuf (L := L) { Z with th := th', G := G', T := Z.T ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val }
      res.2.1 σ' :=
    ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.retype hE hM hM' (fun _ => UFr.keep hfk.page)
      (fun j _ => by rw [hcj]; simp [cjOf, newCapOf, hnt, Vs.FrIn])⟩
  -- `LiveDN` and `zD` after (UtTcbLive's `ret_liveND`; KENTRY-PLAN g2j): the new
  -- TCBs prepended to core 0's debug list (`TcbC`), their slots empty
  have hTb : ∀ q, H q = some .tcb → q.val + 4096 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ q.val :=
    fun q hq => by
      have := hU.free q .tcb ((hJp.tcb q).2 hq); simp only [objSize] at this; omega
  have hinj : ∀ i j, i < win.val → j < win.val → bT Aw i = bT Aw j → i = j := fun i j hi hj e => by
    have h1 := bT_v hi hfitW
    have h2 := bT_v hj hfitW
    rw [e] at h1; omega
  have hnT : ∀ x ∈ newL Aw win.val, x ∉ P1.Heap.tcbs H := fun x hx hT => by
    obtain ⟨j, hj, rfl⟩ := mem_newL.1 hx
    have h1 := bT_v hj hfitW
    have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hj
    rcases hTb _ hT with h | h <;> rw [h1] at h <;> (try rw [hk4] at h) <;> omega
  have hTH' : P1.Heap.tcbs H' = P1.Heap.tcbs H ∪ {x | x ∈ newL Aw win.val} := by
    ext q
    simp only [P1.Heap.tcbs, Set.mem_union, Set.mem_setOf_eq, mem_newL]
    rw [hout' q]
    by_cases hn : NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ (some HKind.tcb).isSome
    · rw [if_pos hn]
      obtain ⟨⟨j, hj, hq⟩, -⟩ := hn
      exact ⟨fun _ => Or.inr ⟨j, hj, UScalar.eq_of_val_eq (by rw [bT_v hj hfitW, hq, hk4])⟩, fun _ => rfl⟩
    · rw [if_neg hn]
      have hnn : ¬ ∃ j, j < win.val ∧ q = bT Aw j := fun ⟨j, hj, e⟩ =>
        hn ⟨⟨j, hj, by rw [e, bT_v hj hfitW, hk4]⟩, rfl⟩
      simp only [hnn, or_false]
      constructor
      · intro h
        split_ifs at h with h1
        exact h
      · intro h
        rw [if_neg]
        · exact h
        rintro ⟨kd, hq, hm⟩
        rw [h] at hq; cases hq
        unfold MeetsR at hm
        simp only [HKind.bits] at hm
        have := hTb q h; omega
  -- the debug words outside `DW` and `a2` kept
  have hwinD : ∀ b : U64, Aw ≤ b.val → b.val < Aw + win.val * 4096 → ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b :=
    fun b g1 g2 => J.notDbg' (fun q hq => by
        have := hTb q hq; rw [hk4] at this; show b.val < q.val ∨ q.val + 4096 ≤ b.val; omega)
      (fun c hc => by rcases k2 c hc with h | h <;> omega)
  have hkeepW : ∀ b, P1.DbgW st (P1.Heap.tcbs H) Cs s b → b ≠ DW → b ≠ a2 → L.mem res.2.1 b = L.mem s b :=
    fun b hb h1 h2 => hwT.2.2 b (P1.dbgW_aligned J.blk hb) (fun h => by
      rcases h with h | ⟨g1, g2⟩ | h | h
      · exact J.inSlot_notDbg h hb
      · exact hwinD b g1 g2 hb
      · exact h1 h
      · exact h2 h)
  obtain ⟨⟨Qb, Rb, hqb⟩, -⟩ := J.blk
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := hqb.tcbs
  have hDA := dbgApart_of (L := L) (Cs := Cs) hTP (fun c hc => P1.TInv.nodes J.blk c hc)
  obtain ⟨hLv0, ⟨lst, hDW0⟩, -⟩ := J.live
  have hc00 : (0#u64 : U64) ∈ Cs := J.kern.cs0
  have hh0l : h0 = (lst 0#u64).headD 0#u64 := hDW0.head _ hc00
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have ha2 : a2 = DW ∨ (h0 ≠ 0#u64 ∧ a2 = P1.dpA h0) := by
    by_cases hz : h0 = 0#u64
    · left; show (if h0 = 0#u64 then DW else P1.dpA h0) = DW; rw [if_pos hz]
    · right; exact ⟨hz, by show (if h0 = 0#u64 then DW else P1.dpA h0) = _; rw [if_neg hz]⟩
  have hh0T'' : h0 ≠ 0#u64 → h0 ∈ P1.Heap.tcbs H := fun hne => by rw [← hTe]; exact hh0T hne
  have hdnK : ∀ y ∈ P1.Heap.tcbs H, L.mem res.2.1 (P1.dnA y) = L.mem s (P1.dnA y) := fun y hy =>
    hkeepW _ (Or.inl ⟨y, hy, Or.inl rfl⟩) (fun e => hDA.hd_dn 0#u64 hc00 y hy e.symm) (fun e => by
      rcases ha2 with e2 | ⟨hne, e2⟩
      · exact hDA.hd_dn 0#u64 hc00 y hy (by rw [e, e2, hDW])
      · exact hDA.dn_dp y hy h0 (hh0T'' hne) (e.trans e2))
  have hdpK : ∀ y ∈ P1.Heap.tcbs H, (lst 0#u64 = [] ∨ y ≠ (lst 0#u64).headD 0#u64) →
      L.mem res.2.1 (P1.dpA y) = L.mem s (P1.dpA y) := fun y hy hyh =>
    hkeepW _ (Or.inl ⟨y, hy, Or.inr rfl⟩) (fun e => hDA.hd_dp 0#u64 hc00 y hy e.symm) (fun e => by
      rcases ha2 with e2 | ⟨hne, e2⟩
      · exact hDA.hd_dp 0#u64 hc00 y hy (by rw [e, e2, hDW])
      · have hy0 : y = h0 := hDA.dp_inj y hy h0 (hh0T'' hne) (e.trans e2)
        rcases hyh with hl | hl
        · rw [hh0l, hl] at hne; exact hne rfl
        · exact hl (hy0.trans hh0l))
  have hhdK : ∀ c ∈ Cs, c ≠ 0#u64 → L.mem res.2.1 (dbgHd (L := L) s c) = L.mem s (dbgHd (L := L) s c) :=
    fun c hc hc0' => hkeepW _ (Or.inr ⟨c, hc, rfl⟩) (fun e => by
        have h1 := P1.nodeAt_val (P1.TInv.nodes J.blk c hc) (off := layout.node.DEBUG_TCBS)
          (by simp [layout.node.DEBUG_TCBS])
        have h2 := P1.nodeAt_val (P1.TInv.nodes J.blk 0#u64 hc00) (off := layout.node.DEBUG_TCBS)
          (by simp [layout.node.DEBUG_TCBS])
        have e' : (L.nodeAt s c layout.node.DEBUG_TCBS).val = DW.val := congrArg UScalar.val e
        rw [h1, hDW, h2] at e'
        have hnb : ∀ c : U64, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
        rw [hnb, hnb] at e'
        have h0v : (0#u64 : U64).val = 0 := rfl
        rw [h0v] at e'
        have hcv : c.val = 0 := by omega
        exact hc0' (UScalar.eq_of_val_eq (by rw [hcv]; rfl)))
      (fun e => by
        rcases ha2 with e2 | ⟨hne, e2⟩
        · rw [e2] at e
          have h1 := P1.nodeAt_val (P1.TInv.nodes J.blk c hc) (off := layout.node.DEBUG_TCBS)
            (by simp [layout.node.DEBUG_TCBS])
          have h2 := P1.nodeAt_val (P1.TInv.nodes J.blk 0#u64 hc00) (off := layout.node.DEBUG_TCBS)
            (by simp [layout.node.DEBUG_TCBS])
          have e' : (L.nodeAt s c layout.node.DEBUG_TCBS).val = DW.val := congrArg UScalar.val e
          rw [h1, hDW, h2] at e'
          have hnb : ∀ c : U64, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
          rw [hnb, hnb] at e'
          have h0v : (0#u64 : U64).val = 0 := rfl
          rw [h0v] at e'
          have hcv : c.val = 0 := by omega
          exact hc0' (UScalar.eq_of_val_eq (by rw [hcv]; rfl))
        · exact hDA.hd_dp c hc h0 (hh0T'' hne) (e.trans e2))
  -- affinities: XTopAt's lists before and after
  obtain ⟨Qa, Ra, hca, -⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Qb', Rb', hcb, -⟩ := hXT.fin.1.1.1.lists
  have hDW1 : DbgWFL (P1.Heap.tcbs H ∪ {x | x ∈ newL Aw win.val}) Cs (L.mem res.2.1) (dbgHd (L := L) s)
      (Function.update lst 0#u64 (newL Aw win.val ++ lst 0#u64)) := by
    refine hDW0.prepend hc00 (newL Aw win.val) (nodup_newL hinj) hnT (fun h => ?_) ?_ hhdK (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_) hdnK hdpK (fun hne => ?_) (fun y hy => ?_)
    · obtain ⟨j, hj, e⟩ := mem_newL.1 h
      have := bT_v hj hfitW; rw [← e] at this; simp at this; omega
    · show L.mem res.2.1 DW = _
      rw [hDWres, headD_newL_append, if_neg (by have := hctx.window.1; omega)]
    · obtain ⟨j, hj, rfl⟩ := mem_newL.1 hx
      rw [nextIn_newL hinj _ hj, ← hh0l]
      have := hTC.2.2.1 j hj
      exact this
    · obtain ⟨j, hj, rfl⟩ := mem_newL.1 hx
      rw [prevA_newL hinj _ hj]
      by_cases hj1 : j + 1 < win.val
      · rw [if_pos hj1]; exact hTC.2.2.2.1 j hj1
      · rw [if_neg hj1]; exact hTC.2.2.2.2.1 j (by omega)
    · obtain ⟨j, hj, rfl⟩ := mem_newL.1 hx
      have h1 := hcb.aff (bT Aw j) (Or.inr ⟨j, hj, by rw [bT_v hj hfitW, hk4]⟩)
      rw [h1]; exact hc0
    · have hh0 : h0 ≠ 0#u64 := by
        rw [hh0l]; intro e
        cases e2 : lst 0#u64 with
        | nil => exact hne e2
        | cons a r =>
          rw [e2] at e; simp only [List.headD_cons] at e
          exact hDW0.zero _ hc00 (by rw [e2, ← e]; exact List.mem_cons_self ..)
      have hn0 : (lst 0#u64).headD 0#u64 ∉ newL Aw win.val := fun h => hnT _ h (by
        rw [← hh0l]; exact hh0T'' hh0)
      rw [prevA_newL_append hn0, if_neg (by have := hctx.window.1; omega), ← hh0l]
      cases e2 : lst 0#u64 with
      | nil => exact absurd e2 hne
      | cons a r =>
        have ha : a = h0 := by rw [hh0l, e2, List.headD_cons]
        rw [← ha, show prevA (bT Aw 0) (a :: r) a = bT Aw 0 by simp [prevA], ha]
        exact hTC.2.2.2.2.2.1 (by have := hctx.window.1; omega) hh0
    · have h1 := hcb.aff y (Or.inl (by rw [hTe]; exact hy))
      have h2 := hca.aff y (by rw [hTe]; exact hy)
      rw [h1, h2]
  have hDWres' : DbgWF (P1.Heap.tcbs H') Cs (L.mem res.2.1) (dbgHd (L := L) res.2.1) :=
    ⟨Function.update lst 0#u64 (newL Aw win.val ++ lst 0#u64), by rw [hTH', dbgHd_of_ksb hksR]; exact hDW1⟩
  -- the debug walk's TCBs after have thread caps
  have hidS : σ'.idleThread = σ.idleThread := hC2.idle.trans hidB
  have hdbgT : ∀ n, dbgNth (L.mem res.2.1) n (dbgHead (L := L) res.2.1) ≠ 0#u64 →
      (dbgNth (L.mem res.2.1) n (dbgHead (L := L) res.2.1)).bv ≠ σ'.idleThread →
      ∃ y ∈ G'.chains.flatten, capV (L.mem res.2.1) y = .Thread (dbgNth (L.mem res.2.1) n (dbgHead (L := L) res.2.1)) := by
    intro n hn hni
    have hDW2 : DbgWFL (P1.Heap.tcbs H ∪ {x | x ∈ newL Aw win.val}) Cs (L.mem res.2.1) (dbgHd (L := L) res.2.1)
        (Function.update lst 0#u64 (newL Aw win.val ++ lst 0#u64)) := by rw [dbgHd_of_ksb hksR]; exact hDW1
    have hm : dbgNth (L.mem res.2.1) n (dbgHead (L := L) res.2.1) ∈ newL Aw win.val ++ lst 0#u64 := by
      have := (dbgNth_mem_wf hDW2 hc00 n).resolve_left hn
      rw [Function.update_self] at this
      exact this
    rcases List.mem_append.1 hm with h | h
    · obtain ⟨j, hj, e⟩ := mem_newL.1 h
      refine ⟨dslot j, hE.newm j hj, ?_⟩
      rw [hE.newc j hj, e, hcj, hk4]
      simp [cjOf, newCapOf, hnt, bT]
    · obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
      have hni0 : dbgNth (L.mem s) i (dbgHead (L := L) s) = (lst 0#u64)[i] := dbgNth_getElem_wf hDW0 hc00 i hi
      have hx0 : (lst 0#u64)[i] ≠ 0#u64 := fun h0' => by
        have hm := List.getElem_mem hi
        rw [h0'] at hm
        exact hDW0.zero 0#u64 hc00 hm
      obtain ⟨y, hyG, hyc⟩ := hLv0.dbg i (by rw [hni0]; exact hx0) (by rw [hni0, e, ← hidS]; exact hni)
      rw [hni0, e] at hyc
      have hyS : IsSlot Z.th y := ((hM.members y).1 hyG).1
      have hyx : y ≠ cslotAddr (pp.bv, idx) := fun h' => by rw [h', capV_of_capAt hcap] at hyc; cases hyc
      have hyW : ∀ d ∈ windowSlots dest r off.val win.val, y ≠ cslotAddr d := fun d hd h' => by
        rw [h', capV_of_capAt (hDn0 d hd)] at hyc; cases hyc
      have hkeep := hcapK y hyS hyx hyW
      refine ⟨y, (hM'.members y).2 ⟨hthM y hyS, _, capAt_capV _ _, by rw [hkeep, hyc]; exact fun h' => by cases h'⟩, ?_⟩
      rw [hkeep, hyc]
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
    refine ⟨newSlot_nullT hThX4 hk0 hP' hWZ4 hfitW hqi hq, fun x hx => ?_⟩
    have hnA := not_absSlot_new hP' hold hq hqi hx
    by_cases hxW : x ∈ windowSlots dest r off.val win.val
    · exact absurd (hslA x hxW).1 hnA
    rw [horgK x hxW]
    cases ho : σ.isOriginalCap x
    · rfl
    · exact absurd (J.kern.orig x ho) hnA
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveND hXT rfl hold hNE hksR hDWres' hdbgT
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frameT (Z' := { Z with th := th', G := G', T := Z.T ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val })
    rfl rfl hwT.1 hXT hCs hJR hKs'
    (fun t0 ht0 => by
      rcases hThX.casesI ht0 with h | ⟨h, -⟩
      · exact Or.inl (J.thT t0 h)
      · exact Or.inr h)
    (thk_grow hThX hksk J.thk) (DelBound.of_placed hP') hintL hIp' hnk' hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hM' (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _), fun t0 ht0 => by
      rcases hThX.casesI ht0 with h | ⟨⟨i, hi, hq⟩, -⟩
      · exact J.ext.vkeep (J.vkeep_of hwT fun b hb u hu e => by
          rcases hb with hb | hb
          · exact J.inSlot_nv hb u hu e
          · have hv := Sched.tVcpuA_val J.ip.e.tcb hu
            rcases hWT b hb u hu with h' | h' | h' <;> rw [e, hv] at h' <;> omega) t0 h
      · try simp only [hk4] at hq
        have e : t0 = bT Aw i := UScalar.eq_of_val_eq (by rw [bT_v hi hfitW]; omega)
        subst e
        have hv : (tVcpuA (bT Aw i)).val = (bT Aw i).val + 3664 := Notif.tfield_val (hTB i hi) (by simp)
        have a := (hTB i hi).align
        exact winZero_vcpu hWZ4 hfitW hi _ (by show _ % 8 = 0; rw [hv]; omega) hv⟩
    hLvN hzDN
  refine ⟨σ', hrun, hok, ⟨th', G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX'.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', Lst, _, JZ⟩

set_option maxHeartbeats 4000000 in
/-- **The no-reset retype of TCBs at `J`** (module docstring; `JAtZ.utCnJ`'s
wrapper): from `JAtZ` at the decode (no reschedule pending), the decoded
arguments (`RetCtx`, no reset: the source cap has a child), the source a
CNode slot's RAM untyped cap, FL4's restart (`JAtZ.restartJ`) and then
`JAtZ.utTcbBodyJ` end in `UtRetPostJ`. -/
theorem JAtZ.utTcbJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 1) (hc0 : Z.c = 0#u64)
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
  exact WP.spec_mono (J1.utTcbBodyJ hni1 hpp hidx hcap1 hnt hc0 hctx1 hfiv hBO1 hAF1 hRU1)
    (fun res h => utRetPostJ_of_body hst1 h)

end

end

end Fl4Proofs.P3
