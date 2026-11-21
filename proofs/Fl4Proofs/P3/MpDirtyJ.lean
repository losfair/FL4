/-
P3 (DESIGN.md §9), VSpace: **the ASID control cap's `MakePool` at `J` when
the region is dirty** (XTopJointVsCap's `JAsidCPath.dirty`; handoff/utj.md
Round 15): l4v's `delete_objects` of the pool's frame over dead objects, as
the untyped reset's drop (`JAtZ.drop`) at the restart's state, then the
clean case's step (`JAtZ.mpStepJ`) from the drop's state.

* The spec: `perform_asid_control_invocation` from a state detyped at the
  frame is the one from the state itself (`deleteObjects_detype`,
  `perform_mp_detype`: `delete_objects` detypes the frame again).
* The drop is UtDropJ2's `JAtZ.dropA` (any free index); the region facts
  XTopJointVsCap's `MpEmptyAt` lemmas (`JAtZ.mpPlacedCAt`, `JAtZ.mpRegionCAt`,
  `JAtZ.mpAddOKAt`), here from the drop.
-/
import Fl4Proofs.P3.XTopJointMakePool
import Fl4Proofs.P3.UtDropJ2
import Fl4Proofs.P3.VsDecFrame
import Fl4Proofs.P3.UtResetSpecJ
import Fl4Proofs.P3.UtResetZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec: the perform after a detype of the frame -/

section Spec
open Fl4Spec

theorem detype_idemD (R : Set ObjRef) (t : State Unit) : detype R (detype R t) = detype R t := by
  simp only [detype]; congr 2; funext x; split <;> rfl

theorem detype_msD (R : Set ObjRef) (σ : State Unit) (ms : MachineState) :
    ({ detype R σ with machineState := ms } : State Unit) = detype R { σ with machineState := ms } := rfl

theorem doMachineOp_runD {α : Type} (mop : NonDet MachineState α) (σ : State Unit) :
    doMachineOp (Z := Unit) mop σ =
      ({y | ∃ x ∈ (mop σ.machineState).1, y = (x.1, { σ with machineState := x.2 })}, (mop σ.machineState).2) := by
  unfold doMachineOp
  simp only [Bind.bind, NonDet.bind, NonDet.gets, NonDet.selectF, NonDet.modify, Pure.pure, NonDet.pure]
  refine Prod.ext ?_ ?_
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl, x1, ⟨h1, h2⟩, x3, rfl, rfl⟩
      obtain ⟨⟨r, ms⟩, t⟩ := x1
      dsimp only at h1 h2 ⊢
      subst h2
      exact ⟨(r, ms), h1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, rfl, (x, σ), ⟨hx, rfl⟩, _, rfl, rfl⟩
  · simp

/-- `delete_objects` from a state detyped at its region: the same outcomes. -/
theorem deleteObjects_detype (a : Word) (n : Nat) (σ : State Unit) :
    deleteObjects (Z := Unit) a n (detype {x | a ≤ x ∧ x ≤ a + 2 ^ n - 1} σ) = deleteObjects (Z := Unit) a n σ := by
  unfold deleteObjects
  show NonDet.bind (doMachineOp _) _ (detype _ σ) = NonDet.bind (doMachineOp _) _ σ
  unfold NonDet.bind
  rw [doMachineOp_runD, doMachineOp_runD]
  simp only [NonDet.modify]
  congr 1
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, by rw [detype_msD, detype_idemD]⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, by rw [detype_msD, detype_idemD]⟩
  · simp only [Set.mem_setOf_eq, and_false, exists_false, or_false]; rfl

/-- **`perform_asid_control_invocation` (`MakePool`) from a state detyped
at the frame** is the one from the state itself. -/
theorem perform_mp_detype (p : ObjRef) (dest ps : CslotPtr) (base : Asid) (σ : State Unit) :
    (performAsidControlInvocation (Z := Unit) (.makePool p dest ps base)) (detype (regionSet p 12) σ) =
      (performAsidControlInvocation (Z := Unit) (.makePool p dest ps base)) σ := by
  unfold performAsidControlInvocation
  show NonDet.bind (deleteObjects (Z := Unit) p page_bits) _ (detype _ σ) =
    NonDet.bind (deleteObjects (Z := Unit) p page_bits) _ σ
  unfold NonDet.bind
  rw [show regionSet p 12 = {x | p ≤ x ∧ x ≤ p + 2 ^ page_bits - 1} from rfl, deleteObjects_detype]

end Spec



/-! ## Region facts after the drop -/

section Off
variable {th : TypedHeap} {lo hi : Nat}

/-- An object holding a slot off a region, no object straddling it, is off it. -/
theorem obj_off_of_slot (hP : Placed th) (hN : NoStraddle th lo hi) {q : U64} {i : Nat} (hqi : IsSlotAt th q i)
    (hoff : (slotOf q i).val < lo ∨ hi ≤ (slotOf q i).val) : ¬ (lo ≤ q.val ∧ q.val < hi) := by
  intro hin
  have hv := hqi.val hP
  obtain ⟨k, hk, hs⟩ := hqi.size
  rcases hN q k hk with h | h | h <;> omega

/-- A slot off a region is a slot of the restricted typed heap. -/
theorem isSlot_restrict_off (hP : Placed th) (hN : NoStraddle th lo hi) {y : U64} (hy : IsSlot th y)
    (hoff : y.val < lo ∨ hi ≤ y.val) : IsSlot (restrictTh th lo hi) y := by
  obtain ⟨q, i, hqi, rfl⟩ := hy
  have hq := obj_off_of_slot hP hN hqi hoff
  refine ⟨q, i, ?_, rfl⟩
  unfold IsSlotAt
  rw [restrictTh_out hq]
  exact hqi

/-- A CNode slot off a region: its CNode is off it. -/
theorem cnode_off_of_slot (hP : Placed th) (hN : NoStraddle th lo hi) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : th pp = some (.cnode rs)) (hidx : idx.length = rs)
    (hoff : (cslotAddr (pp.bv, idx)).val < lo ∨ hi ≤ (cslotAddr (pp.bv, idx)).val) :
    ¬ (lo ≤ pp.val ∧ pp.val < hi) := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  obtain ⟨q, i, hqi, hq1, he⟩ := hAs.at
  have e : q = pp := P1.eq_of_bv hq1.symm
  subst e
  rw [he] at hoff
  exact obj_off_of_slot hP hN hqi hoff

end Off

/-! ## The dirty case at `J` -/

section Dirty
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The destination CNode misses a childless untyped cap's region**
(`DestLive`: a CNode cap of the MDB names it, `cnode_off_childless`, or it
lies in the kernel-state block, off every RAM untyped region). -/
theorem JAtZ.destOff {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pd : U64} {rd : Nat} (hpd : Z.th pd = some (.cnode rd)) (hDL : DestLive Z.th (L.mem s) (L.ksb s) pd)
    {x : U64} (hx : x ∈ Z.G.chains.flatten) {p sb fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) : ¬ (p.val ≤ pd.val ∧ pd.val < p.val + 2 ^ sb.val) := by
  obtain ⟨-, ⟨-, -, hM, -, hI⟩, -⟩ := J.xtop.rel
  rcases hDL with ⟨y, r, gs, g, hy, hc⟩ | h
  · have hyG : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hc]; simp⟩
    exact cnode_off_childless J.ut hI hx hcx hnd hyG hc
  · obtain ⟨k1, -, -⟩ := J.jcov.ks x hx p sb fi hcx
    have := h _ hpd
    simp only [objSize] at this
    have := Nat.one_le_two_pow (n := rd)
    omega

set_option maxHeartbeats 16000000 in
/-- **The ASID control cap at `JAt`, any region** (the dirty case of
`JAsidCPath`; module docstring): VsDecFrame's
`decode_invocation_asid_controlXP` with `MakePool`'s perform: FL4's restart
(`JAtZ.restartJ`), the drop of the pool's frame at the restart's state
(`JAtZ.dropA`, the spec's state detyped there), then `mp_perform_relB` and
`JAtZ.mpStepJ` from the drop's `JAtZ`, whose region is empty (`MpEmptyAt`); the
spec's perform from the detyped state is its perform from the restart's
(`perform_mp_detype`). The domain schedule from the footprint (`VsFootW`, as
VsThX's `domFrame_asid_control`). Premises: `ArchFitHyp` and
`RegionUnrefJ` [J] (as `JUtPath.heapH`), and `VsReachMiss` [J] at the
restart's state for a childless pool-sized RAM untyped's region, at the
tables the slots' caps ask (`Vs.NeedR`, as `JUtPath.vsReach`). -/
theorem decode_invocation_asid_controlJD (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hVM : ∀ (x p fi : U64) (s1 : S), x ∈ Z.G.chains.flatten →
      capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false → (∀ y, ¬ Mdb.Desc Z.G.par y x) →
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : JMpExtra (L := L) Z s extra excaps)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨hPl, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hrun := J.curRun.run hni
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  -- the footprint (VsThX's `domFrame_asid_control`)
  let W : U64 → Prop := fun b => VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s b ∨
    ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568)
  have hext' : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        Z.th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid Z.th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ (p sb fi : U64), sb = fl4_abi.consts.bits.ASID_POOL →
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      ∀ (pd : U64) (rd : Nat) (idxd : List Bool), Z.th pd = some (.cnode rd) → idxd.length = rd →
      capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null → CnRef Z.th (L.mem s) rc pd →
      ∀ (i base : U64), i.val < 2048 → base.val = i.val * 512 →
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let i1 ← lift (sb &&& 63#u64)
        let i2 ← 1#u64 <<< i1
        let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s1 (capability.Cap.Untyped p sb i2 false)
        let s3 ← st.clear_free s2 p 4096#u64
        let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
        let s5 ← vspace.set_asid_table st s4 i p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, ar)) ⦃ res =>
        res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' th' G',
          ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).1 ∧
          ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).2 ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) σ' G' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
          MdbOKV (L.ksb s) (L.mem res.2.1) G' ∧ P1.WritesIn st s res.2.1 W ∧
          (DomRel (L.mem res.2.1) (L.ksb res.2.1) σ' → JAt (L := L) arI AR res.2.1 res.2.2 σ') ⦄ := by
    rcases hext.2 with h | ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact Or.inl h
    refine Or.inr ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
    intro p sb fi hsb hcap hnch pd rd idxd hpd hld hnull hCn i base hi hbase
    subst hsb
    have hpp := h1
    have hidx := h2
    have hsbv : (fl4_abi.consts.bits.ASID_POOL).val = 12 := by unfold fl4_abi.consts.bits.ASID_POOL; rfl
    have h2sb : 2 ^ (fl4_abi.consts.bits.ASID_POOL).val = 4096 := by rw [hsbv]; norm_num
    have hRg12 : ∀ o, RgOf p fl4_abi.consts.bits.ASID_POOL o ↔ o ∈ regionSet p.bv 12 := fun o => by
      show o ∈ regionSet p.bv (fl4_abi.consts.bits.ASID_POOL).val ↔ _; rw [hsbv]
    -- the source cap: in the MDB, childless, its region's facts
    have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
    have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
      (hCR.2.2.1.members _).2 ⟨hAs.isSlot, _, hcap, fun h => by cases h⟩
    have hnd := nodesc_of_cdt hPl hCR.2.2.2.1 hAs hnch
    have hcv := capV_of_capAt hcap
    have U := J.utc _ p _ fi false hAs hcap rfl
    have hfit := U.pfit
    rw [h2sb] at hfit
    have hns := U.ns hnch
    rw [h2sb] at hns
    have hN := U.nostr
    have hppOff : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) :=
      cnode_off_of_slot hPl hN hpp hidx (by rw [h2sb]; exact hns _ hxG)
    have hDL0 : DestLive Z.th (L.mem s) (L.ksb s) pd :=
      DestLive.of_cnRef (kb := L.ksb s) hCn ⟨y, hext.1 y h4, capV_of_capAt h7⟩
    have hpdOff := J.destOff arI hpd hDL0 hxG hcv hnd
    -- the restart
    obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur1, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hk1, hcpu1⟩ :=
      restart_dstate Z.th hPl s σ Z.G J.dstate ct hct hcur htcb J.kern.act
    rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
    have hσ1k : ∀ o, o ≠ ct.bv → σ1.kheap o = σ.kheap o := fun o ho => by
      rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
    have hσ1c : σ1.kheap ct.bv = some (.tcb { x1 with tcbState := .restart }) := by
      rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
    have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
    have hres1 : σ1.schedulerAction ≠ .chooseNewThread := by
      rw [he1, J.restart_keeps_resume hni hkx hcur1]; simp
    have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
      by_cases ho : o = ct.bv
      · subst ho; rw [hσ1c] at h; cases h
      · rwa [hσ1k o ho] at h) hH
    have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) =
        ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi false) := (hSS1.capAt hAs.isSlot).trans hcap
    have hnch1 : ¬ ∃ y, σ1.cdt y = some (pp.bv, idx) := by rw [hσ1cdt]; exact hnch
    -- the kept references at the restart's state (`RegionUnrefJ` [J])
    have hs1c : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 := by rw [← hctE]; exact hs1
    obtain ⟨hKR, hDT⟩ := hRU s1 hs1c p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val)
      (fun q k hq hr => (region_deadP J.jcov J.ut hCR.2.2.2.2 hxG hcv (Or.inr ⟨hnd, le_rfl⟩) le_rfl q k hq hr).1)
    -- the drop at the restart's state
    set σd : Fl4Spec.State Unit := Fl4Spec.detype (regionSet p.bv 12) σ1 with hσd
    have hSD : SDrop (RgOf p fl4_abi.consts.bits.ASID_POOL) σ1 σd :=
      ⟨fun o ho => by have h := (hRg12 o).1 ho; rw [hσd]; simp only [Fl4Spec.detype]; exact if_pos h,
        fun o ho => by
          have h : o ∉ regionSet p.bv 12 := fun h => ho ((hRg12 o).2 h)
          rw [hσd]; simp only [Fl4Spec.detype]; exact if_neg h,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have Jd := J1.dropA hres1 hAs hcap1 hnch1 hKR hDT hAF1 hSD rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ => rfl) J1.vsc.needR.1 J1.vsc.needR.2.1 J1.vsc.needR.2.2.1 J1.vsc.needR.2.2.2.1
      J1.vsc.needR.2.2.2.2 (hVM _ p fi s1 hxG hcv hnd hs1) Vs.needR_roots
    set Zd := ((Z.keep (KOff (RgOf p fl4_abi.consts.bits.ASID_POOL)) (KBOf p fl4_abi.consts.bits.ASID_POOL)).dropV
      p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1)) with hZd
    set Hd := H.drop (P1.RegionD H p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val)) with hHd
    obtain ⟨hPld, hCRd, hFId, hDRd, hMOd, hIAd, -⟩ := Jd.xtop.rel
    have hppd : Zd.th pp = some (.cnode rs) := by
      show restrictTh Z.th _ _ pp = _; rw [restrictTh_out hppOff]; exact hpp
    have hpdd : Zd.th pd = some (.cnode rd) := by
      show restrictTh Z.th _ _ pd = _; rw [restrictTh_out hpdOff]; exact hpd
    have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
    have hnull1 : capAt (L.mem s1) (cslotAddr (pd.bv, idxd)) = ok .Null := (hSS1.capAt hAd.isSlot).trans hnull
    have hnchd : ¬ ∃ y, σd.cdt y = some (pp.bv, idx) := hnch1
    obtain ⟨k1, -, -⟩ := J.jcov.ks _ hxG p _ fi hcv
    rw [h2sb] at k1
    have hN4 := hN
    rw [h2sb] at hN4
    -- the region is empty at the drop's state
    have hE : MpEmptyAt Zd Hd p := by
      refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun wp hw => ?_⟩
      · obtain ⟨hq0, hqo⟩ := restrictTh_some hq
        rw [h2sb] at hqo
        have hm1 := le_max_left (objSize k) 1
        have hm2 := le_max_right (objSize k) 1
        have hm3 := max_choice (objSize k) 1
        rcases hN4 q k hq0 with h | h | h <;> rcases hm3 with e | e <;> rw [e] <;> omega
      · obtain ⟨hr, hq0⟩ := P1.Heap.drop_eq_some.1 hq
        unfold P1.RegionD P1.MeetsR at hr
        rw [hq0] at hr
        simp only [Option.elim, not_not] at hr
        rw [h2sb] at hr
        omega
      · obtain ⟨-, hb, hw1⟩ := hw
        rw [h2sb] at hw1
        refine ⟨hw1, fun i hi => ?_⟩
        have h0 : ¬ ((wp.2 + (7 - BitVec.ofInt 64 i)) ∈ regionSet p.bv 12) := fun h => hb i hi ((hRg12 _).2 h)
        rw [regionSet_iff' p _ 12 (by decide) hfit] at h0
        omega
    have hxGd : cslotAddr (pp.bv, idx) ∈ Zd.G.chains.flatten := hxG
    have hcvd := capV_of_capAt hcap1
    obtain ⟨hRg, hRO⟩ := Jd.mpRegionCAt arI hppd hidx hcap1 hnchd hE
    -- FL4's restart, then the perform from the drop's state
    rw [hs1]; simp only [bind_ok]
    refine WP.spec_mono (mp_perform_relB (L := L) vsMpHyps_top s1 ar σd Zd.G hPld hCRd.1 hCRd.2.1 hCRd.2.2.1
      hCRd.2.2.2.1 hCRd.2.2.2.2 Jd.ut Jd.xtop.fin.2.1 Jd.xtop.fin.2.2.1 Jd.xtop.fin.1 Jd.xtop.fin.1.2.vs
      Jd.xtop.fin.1.2.pt hppd hidx rfl hcap1 hnchd hpdd hld hnull1 hi hbase hRg hRO Jd.xtop.fin.1.2.vo
      Jd.xtop.fin.1.2.po Jd.xtop.fin.1.2.pv hFId hMOd.1.1 (rc := rc)) ?_
    rintro res ⟨hok, har, σ', th', G', hm, hnf, hP', hSt', hSV', hM', hC', hI', hU', hR', hPt', hSRq, hF', -, -, hMS, -,
      hcur', hth', hk', hsc, hRg', hxu, hPI', hMid⟩
    obtain ⟨hi', hh, hks1, hcpu1', hW, hzero, -, hMs, hkp, hkh, hcdt, horig, hsrc, hdst, hdstb, hcap', hDI, -, -⟩ := hMid
    have hTh := hE.1
    have hrt := restrictTh_clean hTh
    rw [hrt] at hth'
    subst hth'
    -- the spec: the restart, then the perform from the restart's state
    have hpe := perform_mp_detype p.bv (pd.bv, idxd) (pp.bv, idx) base.bv σ1
    have hmem : ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).1 := by
      rw [nd_bind_one hst1, ← hpe]; exact hm
    have hnf1 : ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).2 := by
      rw [nd_bind_one hst1, ← hpe]; exact hnf
    have hMO' : MdbOKV (L.ksb s1) (L.mem res.2.1) G' := hMS.okv hMOd
    -- the footprint
    have hWr0 : P1.WritesIn st s s1 W := by
      have h := sts_foot (W := W) hPl (fun b h => Or.inl h.toW) (P1.WritesIn.refl s W) htcb J.kern.act
        (v := sched.TS_RESTART)
      rw [hs1, WP.spec_ok] at h; exact h
    have hWr1 : P1.WritesIn st s1 res.2.1 W := ⟨hks1, hcpu1', fun b hb hn => hW b hb (fun hw => hn (by
      rcases hw with ⟨x', k, hx', hk, rfl⟩ | hr | rfl
      · exact Or.inl (Or.inr (Or.inl ⟨x', k, hx'.of_restrict, hk, rfl⟩))
      · right; rintro ⟨g1, g2⟩; rcases k1 with e | e <;> omega
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hi', hh, by rw [hk1]⟩)))))))⟩
    refine ⟨hok, har, σ', Zd.th, G', hmem, hnf1, hP', ⟨hSt', hSV', hM', hC', hI'⟩, hF', by rw [← hk1]; exact hMO',
      hWr0.trans1 hWr1, fun hDR' => ?_⟩
    -- `XTopAt` after (as `decode_invocation_asid_controlJC`)
    have hTSR := Jd.mpPlacedCAt arI hE hxGd hcvd Zd.th res.2.1 res.2.2 σ' hrt.symm hk' hsc hRg'
    have hXd := Jd.xtop
    have hFx : FinX st Zd.th (insert p Zd.P) Zd.L4 Zd.L3 Zd.L2 Zd.L1
        (TopSR st Zd.th (insert p Zd.P) Zd.L4 Zd.L3 Zd.L2 Zd.L1 Zd.N Zd.T Zd.C Zd.E Zd.R Zd.B Zd.c AR)
        res.2.1 res.2.2 σ' := by
      refine ⟨hTSR.1 hSRq, hR', hPt', hPI' Zd.L4 hXd.fin.2.2.2.1, ?_⟩
      obtain ⟨t, h1, h2, -⟩ := hXd.fin.2.2.2.2
      obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hMO'.2.2
      have h2' := hTSR.2 t h2
      refine ⟨t, h1.trans hcur'.symm, h2', fun q asid h => ?_⟩
      have hv := hVC.at hM' ⟨t, 1, Or.inr ⟨h2', by decide⟩, rfl⟩ h (by simp)
      simp only [VCapOK] at hv
      exact (hv.2.2 trivial).1
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFx
    have hX' : XTopAt (L := L) AR (Zd.mp G' p) res.2.1 res.2.2 σ' :=
      ⟨hFx, ⟨hFx.1.2.pl, ⟨hSt', hSV', hM', hC', hI'⟩, hF', hDR', by rw [hk']; exact hMO',
        IpcApart.of_topD hFx.1.2 (by rw [hk']; exact hIAd.dom), ScApart.of_top hFx.1.2⟩,
        IpcRel.of hNt hEp (sched_sc hSch), hXd.esa.mono hk' (fun q y n hq => hsc ⟨q⟩ y n hq)⟩
    -- `JAtZ` after, from the drop's `JAtZ` (`JAtZ.mpStepJ`)
    have Ad := Jd.mpAddOKAt arI hxGd hE hcvd hRg.pal hRg.pfit hRg.p0
    have hspecd : ∀ o ko, σd.kheap o = some ko → o.toNat < p.val ∨ p.val + 4096 ≤ o.toNat := by
      intro o ko ho
      have h0 : o ∉ regionSet p.bv 12 := fun hin => by
        have e : σd.kheap o = none := hSD.kin o ((hRg12 o).2 hin)
        rw [e] at ho; cases ho
      rw [regionSet_iff' p o 12 (by decide) hfit] at h0
      omega
    have hDLd : DestCap Zd.th (L.mem s1) pd := by
      obtain ⟨y', r, gs, g, hy', hc⟩ := DestCap.of_cnRef hCn ⟨y, hext.1 y h4, capV_of_capAt h7⟩
      have hy'G : y' ∈ Z.G.chains.flatten := (hCR.2.2.1.members y').2 ⟨hy', _, capAt_capV _ _, by rw [hc]; simp⟩
      exact ⟨y', r, gs, g, isSlot_restrict_off hPl hN hy' (by rw [h2sb]; exact hns y' hy'G),
        by rw [hSS1.capV hy']; exact hc⟩
    exact ⟨_, _, Cs, Ac1, Lst1, D1, Jd.mpStepJ hh hTh hE.2.1 Ad hspecd hppd hidx hcap1 hnchd hpdd hld hnull1 hDLd hX'
      ⟨hks1, hcpu1', hW⟩ hzero hMs hkp hkh hcdt horig hsrc hdst hdstb hRg.p0 hcap' (hDI Jd.del) hU'⟩
  have hD := decode_invocation_asid_controlXP arI Z.th hPl s ar σ Z.G hCR hFI J.ut hMO vsMpHyps_top hX.fin.1
    hX.fin.2.1 hX.fin.2.2.1 hX.fin.1.2.vs hX.fin.1.2.pt hX.fin.1.2.vo hX.fin.1.2.po hX.fin.1.2.pv lbl slbl hlM length
    buf ct hct hcur htcb J.kern.act hrun args hlen hargs extra excaps (Q := fun s' => P1.WritesIn st s s' W)
    (X := fun s' a' σ' => DomRel (L.mem s') (L.ksb s') σ' → JAt (L := L) arI AR s' a' σ') hext'
    (fun _ => ⟨Z, H, Cs, Ac, Lst, D, J⟩) slot blk call don fp ci sl buffer
  -- the domain schedule (VsThX's `domFrame_asid_control`)
  have hS := hX.fin.1
  have hF : DomFrame (L := L) arI s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
    refine ⟨WP.spec_mono hD fun res hr => ?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
    rcases hr.2 with e | hw
    · rw [e]; exact ⟨rfl, fun _ _ => rfl⟩
    · refine ⟨hw.1, fun o ho => hw.2.2 _ ?_ ?_⟩
      · have := hS.2.vs.ksb_fit
        exact ksW_al (by omega) hS.2.vs.ksb_al (domOffs_lt' ho).1 (domOffs_lt' ho).2
      · rintro (h | h)
        · exact dom_not_foot hS ho h
        · apply h
          have := hS.2.vs.ksb_fit
          have hb : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by have := (domOffs_lt' ho).1; omega)
          have := (domOffs_lt' ho).1
          rw [hb]; omega
  exact Or.inl (DecOKMX.toXD arI (DecOKMQX.toX arI hD (fun _ _ _ h => h)) hF
    (okAll_specDec_asidControl fp slbl (args.map UScalar.bv) ci sl excaps buffer) hDR (fun _ _ _ hx hd => hx hd))

end Dirty

end

end Fl4Proofs.P3
