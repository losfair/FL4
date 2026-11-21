/-
P3 (DESIGN.md §9), TCB: **a cap installed into a TCB slot at `J`**
(FL4 `tcb::install_tcb_cap`, l4v `install_tcb_cap`: `cap_delete` of the
TCB slot, `check_cap_at` twice, `cap_insert`), and the Thread cap labels
built on it.

* `SpecGlob.insTcb`: that insert keeps the deletion loop's `SpecGlob` (the
  new cap names the objects of its source cap, `absCap_shape_refs`; only it
  is written, `nik_capInsert`; a TCB slot is no IRQ node slot).
* `JAtZ.insTJ`: `cdt::insert` of a non-untyped cap into an empty TCB slot
  keeps `JAtZ` (no premise). The spec changes the TCB's caps only
  (`KeepCT`, `XTopAt.slotStepT`); the covers kept (the slot was empty);
  the untyped caps' facts by `ins_utcG` with the TCB live: the invoked
  thread cap, still in its slot (`still_valid`), covers the TCB, so the
  new MDB slot misses every childless untyped region (`live_slotT`); the
  fault-handler slot holds an endpoint cap or nothing (`JPlaced.fh`,
  `jowes_slotDF`).
* `InstPostWP`: `InstPostW` (TcbCaps) with `W` after an Ok install and `Wp`
  after a preempted one; `inst_seqWP`, `inst_skipWP`, `inst_doneWP`.
* `InsWJ arI AR Z H Cs kb W`: an invariant `W` of the installs: `WJR`, kept
  by an insert into an empty TCB slot (given `WJR` after it), with
  `BufHypW` at it (`insWJ_wjr` at `WJR` itself; at `WJL`:
  XTopJointTcbInsL's `insWJ_wjl`). `TcbInsW`: `InsWJ` and the deletion
  loop's steps (`DelHypsWRZ`) at every kernel-state base.
* `install_tcb_capJ`, `install_okJ`: the install at an `InsWJ` invariant `W`
  (`WJP` when preempted): the delete by DelFull's `delete_fullWRZ` with the
  loop's steps at `W` (`DelHypsWRZ`), the checks and insert by TcbCaps'
  `install_after`, then `insTJ`, `PPR0` and `NoSwitch` kept by the insert
  (`CnK`), `W` by `InsWJ.ins`.
* `JAtZ.bufWrJ`: a TCB's IPC-buffer word written at `J` with the spec's
  `tcb_ipc_buffer` (as XTopJointTcbSched's `JAtZ.mcpWrJ`; `QKM` now lets the
  IPC buffer change; `BufWordRel` by XTopBuf's `bufWordRel_setIpc`).
* `bufHypW_J`: TcbCaps' `BufHypW` at `WJR` (the word by `bufWrJ`, the tail's
  `reschedule_required` by XTopJointCopyRegs' `JAtZ.schedJ`; `SpecGlob`/`PPR0`/`NoSwitch` kept),
  with `ActReady` from the state's `JAtZ` (`Sched.Inv.actReady`).
* `install_bufferJ`: `tcb::install_buffer` at `W`/`WJP`, as TcbCaps'
  `install_buffer_refinesW` (the insert by `check_insert`'s case split and
  `insTJ`).
* `thread_control_capsJ`: ThreadControl's cap installs at `W`/`WJP`, as
  TcbCaps' `thread_control_caps_refinesW` (`install_okJ`, `install_bufferJ`).
* `JAtZ.restartJ`: the caller's restart at `J` (moved from XTopJointTcb).
* `JAtZ.restartW`: the restart at `TcbInsW`'s `W` (`RestartWJ`, from the
  caller: XTopJointWJLRestart's `WJL.restart`).
* `top_of_instJ`: an install run's outcome at `W`/`WJP` is a
  `TopPostDMXP` outcome at `JAt`/`JAtPre`.
* Labels: SetTimeoutEndpoint (`tcb_set_timeoutJ`), SetSpace (`tcb_set_spaceJ`),
  SetIPCBuffer (`tcb_set_ipcJ`), Configure (`tcb_configureJ`);
  `xcapP_of_tcb` lifts a label's `TcbOKXP` to the Thread cap's `XCapP`.
-/
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.XTopJointTcbSched
import Fl4Proofs.P3.XTopJointCopyRegs
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **An insert into an empty TCB slot keeps `LiveDN`** (XTopJointWJLIns's `LiveDN.insT` with the `XTopAt` after in place of a `JAtZ` after;
KENTRY-PLAN g2i). -/
theorem LiveDN.insTX {G : MdbGhost} {V : XVs} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ)
    {G' : MdbGhost} {V' : XVs} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
    {t : U64} (ht : Z.th t = some .tcb) {n : Nat} (hn : n < tcbSlots) {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr}
    (hci : Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hnull : capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hnn : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null)
    (hsh : ∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0))
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) :
    LiveDN (L := L) Z.th H Cs G' s' σ' := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hP : Placed Z.th := J.xtop.rel.1
  set x := cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) with hx
  have hAd : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hxS : IsSlot Z.th x := hAd.isSlot
  have htn : IsSlotAt Z.th t n := Or.inr ⟨ht, hn⟩
  have hxe : x = slotOf t n := by
    show slotAddr t.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal n hn]
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by
    rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hkc : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hw : P1.WritesIn st s s' (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  have horig : ∀ sl, sl ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) → σ'.isOriginalCap sl = σ.isOriginalCap sl :=
    fun sl e => capInsert_orig c _ _ σ ((), σ') hmem sl e
  have hM := hDS.1.2.2.1
  have hM' := hDS'.1.2.2.1
  -- a non-null cap before, away from `x`: in the MDB after, kept
  have hkeep : ∀ y, IsSlot Z.th y → capV (L.mem s) y ≠ .Null →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y := fun y hy h => by
    have hyx : y ≠ x := fun e => h (by rw [e, hnull])
    have e := hcap y hy hyx
    exact ⟨(hM'.members y).2 ⟨hy, _, capAt_capV _ _, by rw [e]; exact h⟩, e⟩
  have hmemS : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  -- the new cap is no zombie
  have hnz : ∀ p zt k, capV (L.mem s') x ≠ .Zombie p zt k := by
    intro p zt k hz
    obtain ⟨y0, hy0, hsh0⟩ := hsh
    have e0 : capV (L.mem s) y0 = capV (L.mem s') x := zombie_of_shape hsh0 hz
    have hy0x : y0 ≠ x := fun e => by rw [e, hnull, hz] at e0; cases e0
    have h1 := FinInv.zombie_alone hDS'.2.2 hM' hxS hz y0 hy0 hy0x
    rw [hcap y0 hy0 hy0x, e0, hz] at h1
    exact h1 (by simp [absCap, Fl4Spec.objRefs])
  -- the thread cap naming `t`
  obtain ⟨yT, hyT, hTc⟩ := hlive
  obtain ⟨hyTG, hyTc⟩ := hkeep yT hyT (by rw [hTc]; exact fun h => by cases h)
  -- a slot in use after, away from `x`, was in use before
  have hU : ∀ y, IsSlot Z.th y → y ≠ x → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hyx hu => by
    unfold InUse at hu ⊢
    rw [hcap y hy hyx] at hu
    rcases hu with hu | ⟨x', hx', ho⟩
    · exact Or.inl hu
    · refine Or.inr ⟨x', hx', ?_⟩
      have hne : x' ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hyx (by rw [← hx', e])
      rw [← horig x' hne]; exact ho
  -- the debug words
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    dbgKeep_of_writes J.blk hwS fun _ hb => J.inSlot_notDbg (slotWd_range hP hb)
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hc0 : 0#u64 ∈ Cs := J.kern.cs0
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [P1.nodeAt_of_ksb hdk.1]
    exact hdk.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hNt : ∀ k, dbgNth (L.mem s') k (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) :=
    fun k => by
      rw [hhd]
      exact dbgNth_keep (fun y hy => hdk.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) k _
        (hTz.dh _ hc0)
  -- no zombie names `t`
  have hzt : ∀ y, IsSlot Z.th y → ∀ zt k, capV (L.mem s) y ≠ .Zombie t zt k := fun y hy zt k hz => by
    have hne : yT ≠ y := fun e => by rw [e, hz] at hTc; cases hTc
    have h1 := FinInv.zombie_alone hDS.2.2 hM hy hz yT hyT hne
    rw [hTc] at h1
    exact h1 (by simp [absCap, Fl4Spec.objRefs])
  have hL' : LiveJ (L := L) Z.th H G' s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p zt k hz i hpi hki hu => ?_,
      fun y hy p zt k hz hzt' => ?_⟩
    · by_cases hqx : slotOf q i = x
      · obtain ⟨rfl, -⟩ := slotOf_inj hP hqi htn (hqx.trans hxe)
        exact Or.inl ⟨yT, hyTG, by rw [hyTc, hTc]; rfl⟩
      · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hqx hu) with ⟨y, hy, hr⟩ | hb
        · obtain ⟨hyG, hyc⟩ := hkeep y (hmemS y hy) (hmemN y hy)
          exact Or.inl ⟨y, hyG, by rw [hyc]; exact hr⟩
        · exact Or.inr (by rw [hdk.1]; exact hb)
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hcn.idle]; exact hki)
      obtain ⟨hyG, hyc⟩ := hkeep y (hmemS y hy) (hmemN y hy)
      exact ⟨y, hyG, by rw [hyc]; exact hr⟩
    · have hyx : y ≠ x := fun e => hnz p zt k (by rw [← e]; exact hz)
      have hz0 : capV (L.mem s) y = .Zombie p zt k := by rw [← hcap y hy hyx]; exact hz
      by_cases hpx : slotOf p i = x
      · obtain ⟨rfl, -⟩ := slotOf_inj hP hpi htn (hpx.trans hxe)
        exact hzt y hy zt k hz0
      · exact hL.zslots y hy p zt k hz0 i hpi hki (hU _ ⟨p, i, hpi, rfl⟩ hpx hu)
    · have hyx : y ≠ x := fun e => hnz p zt k (by rw [← e]; exact hz)
      have hz0 : capV (L.mem s) y = .Zombie p zt k := by rw [← hcap y hy hyx]; exact hz
      exact J.deadP_slot hX' hcn hkc hw (hL.zdead y hy p zt k hz0 hzt')
  refine ⟨hL', ⟨lst, dbgWFL_step J.xtop hX' rfl rfl J.tcbs_eq.1 hDW hdk⟩, fun sl hA h => ?_⟩
  have hsx : cslotAddr sl ≠ x := fun e => hnn (by rw [← e]; exact h)
  have hne : sl ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hsx (by rw [e])
  rw [horig sl hne]
  exact hN sl hA (by rw [← hcap _ hA.isSlot hsx]; exact h)


set_option maxHeartbeats 16000000 in
/-- **An insertion into an empty TCB slot keeps `JAtZ`** (module
docstring). -/
theorem JAtZ.insTJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat} {σ' : Fl4Spec.State Unit}
    (hok : n = 2 → Endp.IpcBufCapOK σ') {t : U64} (ht : Z.th t = some .tcb)
    (hn : n < tcbSlots) {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr} {s' : S}
    {G' : MdbGhost}
    (hci : Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hDS' : DState (L := L) Z.th s' σ' G') (hSt : MdbStep (L.mem s) Z.G (L.mem s') G')
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hnull : capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hnu : isUt (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = false)
    (hnn : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null)
    (hsh : ∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0))
    (hfh : n = 3 → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbs : n = 2 → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t)
    (hvt : ∀ P L4 L3 L2 L1 : Set U64, Vs.VsSlotsW Z.th P L4 L3 L2 L1 (L.mem s) →
      Vs.VCapW P L4 L3 L2 L1 (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hft : ∀ U : Nat → Prop, Vs.FrSlots Z.th U (L.mem s) →
      Vs.FrIn U (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hnt : Vs.VsNat Z.th (L.mem s) → Vs.NativeCap (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a σ' := by
  have hX := J.xtop
  have hP := hX.rel.1
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by
    rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hkc : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hkz : KSz σ σ' := capInsert_nkz c _ _ σ _ hmem
  have hw : P1.WritesIn st s s' (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  have hAd : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  obtain ⟨hCR', hDl', hFI'⟩ := hDS'
  have hM' := hCR'.2.2.1
  have hMO : MdbOKV (L.ksb s) (L.mem s') G' := hSt.okv hX.rel.2.2.2.2.1
  have hct : σ'.curThread = σ.curThread := by
    have e := congrArg Fl4Spec.AbstractState.curThread hcn.1; exact e
  have hCO := CurOK.of_inv' hX.fin.2.2.2.2 hct hM' hMO.2.2
  have hX1 : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a σ' := XTopAt.slotStepT hX hwS hcn hCR' hFI' hMO hCO
  have hnull' : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = ok .Null := by
    rw [capAt_capV, hnull]
  have hnu' : ∀ p sb fi d, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Untyped p sb fi d :=
    fun p sb fi d e => by rw [e] at hnu; simp [isUt] at hnu
  -- the slots' caps after
  have hTK : TypedKept Z.th (L.mem s) (L.mem s') := fun x hx => by
    by_cases e : x = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · subst e; obtain ⟨y0, hy0, h0⟩ := hsh; exact Or.inr ⟨y0, hy0, h0⟩
    · exact Or.inr ⟨x, hx, by rw [hcap x hx e]⟩
  have hUK : UtKept Z.th (L.mem s) (L.mem s') := fun x hx p sb fi d h => by
    have e : x ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hnu' p sb fi d (e ▸ h)
    exact ⟨x, hx, fi, by rw [← hcap x hx e]; exact h, Or.inl le_rfl⟩
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := fun y hy hp hu => by
    have hyd : y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => by
      rw [e, hnull, physF_null] at hp; cases hp
    have e := hcap y hy hyd
    exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  have hfh' : ∀ u, Z.th u = some .tcb → capV (L.mem s') (cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 3)) =
        .Endpoint ep b0 b1 b2 b3 b4 := by
    intro u hu
    have hAu : AbsSlot Z.th (u.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨u, rfl, Or.inr ⟨hu, 3, by decide, rfl⟩⟩
    by_cases e : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 3) = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · have e' := cslotAddr_inj hP hAu hAd e
      have h3 : 3 = n := tcbCnodeIndex_inj (by decide) hn (congrArg Prod.snd e')
      rw [e]; exact hfh h3.symm
    · rw [hcap _ hAu.isSlot e]
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact hJ.fh u hu
  have hbs' : ∀ u, Z.th u = some .tcb →
      Sched.BufSlotOK (capV (L.mem s') (cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2))) := by
    intro u hu
    have hAu : AbsSlot Z.th (u.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨u, rfl, Or.inr ⟨hu, 2, by decide, rfl⟩⟩
    by_cases e : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2) = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · have e' := cslotAddr_inj hP hAu hAd e
      have h2 : 2 = n := tcbCnodeIndex_inj (by decide) hn (congrArg Prod.snd e')
      rw [e]; exact hbs h2.symm
    · rw [hcap _ hAu.isSlot e]
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact hJ.bfs u hu
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := by
    intro sl h
    by_cases e : sl = (t.bv, Fl4Spec.tcbCnodeIndex n)
    · right; rw [e]; exact hAd
    · left; rw [← capInsert_orig c _ _ σ ((), σ') hmem sl e]; exact h
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hutc := J.ins_utcG arI hAd hcap hnull' hnu' hw (capInsert_cdt c _ _ σ _ hmem)
    (fun sl e => capInsert_orig c _ _ σ ((), σ') hmem sl e) hgp hM'
    fun _ _ _ _ _ hsl hcv _ hnc => J.live_slotT arI hsl hcv hnc ht hn hlive
  have hjc := J.jcov_cover hw.1 hM' hCK hUK (fun q hq => J.deadP_slot hX1 hcn hkc hw (J.jcov.dead q hq))
    (J.idleW_keep hX1.fin.1.1.1 (CnStep.of_cnK hcn).idle (CnStep.of_cnK hcn).isc)
  obtain ⟨hJC, R⟩ := jowes_slotDF J hX1 hcn hkc hw hFI' hMO hkz hTK hfh' hbs' hDl' hUK hjc horig hutc
  have hpgb : ∀ q vms, σ'.kheap q = some (.archObj (.dataPage false vms)) →
      σ.kheap q = some (.archObj (.dataPage false vms)) := fun q vms h => by
    rcases hkc q with e | ⟨_, _, _, _, h1⟩ | ⟨_, _, _, h1, _⟩
    · rw [← e]; exact h
    · rw [h] at h1; cases h1
    · rw [h] at h1; cases h1
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') :=
    Vs.VsSlotsT.of_some (· = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) (fun y hy hn => hcap y hy hn)
      (fun y _ e => by subst e; exact hvt) (fun y _ e => by subst e; exact hft) fun y _ e => by subst e; exact hnt
  have hbf : JBuf (L := L) Z s' σ' := by
    have hpgf : ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) →
        σ'.kheap q = some (.archObj (.dataPage false vms)) := fun q vms h => by
      rcases hkc q with e | ⟨_, _, _, h1, _⟩ | ⟨_, _, h1, _, _⟩
      · rw [e]; exact h
      · rw [h] at h1; cases h1
      · rw [h] at h1; cases h1
    refine ⟨?_, J.fcov.keep subset_rfl hpgb, J.fcap.keepU hvT hpgf⟩
    by_cases e2 : n = 2
    · exact hok e2
    · refine J.bok.keep (J.slot2Fr hkc hX1.rel.2.1.1 fun q hq => Or.inl ?_)
      have hAq : AbsSlot Z.th (q.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨q, rfl, Or.inr ⟨hq, 2, by decide, rfl⟩⟩
      have hne : cslotAddr (q.bv, Fl4Spec.tcbCnodeIndex 2) ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => by
        have e' := cslotAddr_inj hP hAq hAd e
        exact e2 (tcbCnodeIndex_inj (by decide) hn (congrArg Prod.snd e')).symm
      have he2 : cslotAddr (q.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf q 2 := by
        show slotAddr q.bv (Fl4Spec.ofBl _) = _
        rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]
      rw [← he2, capAt_capV, capAt_capV, hcap _ hAq.isSlot hne]
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  have hLv' := LiveDN.insTX (G := Z.G) (V := Z.vs) J hDS J.live hX1 ⟨hCR', hDl', hFI'⟩ ht hn hci hwS hnull hcap hnn hsh hlive
  have hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D := fun p hp => J.zD p (ZTcb.of_zombies (fun y hy p zt k hz => by
    by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · obtain ⟨y0, hy0, hsh0⟩ := hsh
      subst e
      exact ⟨y0, hy0, (zombie_of_shape hsh0 hz).trans hz⟩
    · exact ⟨y, hy, by rw [← hcap y hy e]; exact hz⟩) hp)
  exact ⟨Ac, Lst, D, J.cs_frameV hw.1 hX1 (KBack.of_keepCT hkc) hbf hJC R (J.vsc.step hvT) (J.ext.step hvT (J.vkeep_slot hw))
    hLv' hzD⟩

set_option maxHeartbeats 8000000 in
/-- **`IpcBufCapOK` after SetIPCBuffer/Configure's frame insert** (decision 2
of gl11): the new IPC-frame cap of TCB `t` a non-device frame at a nonzero
pointer (`hc`, `hq0`) with the range of the source slot's cap (`hk`, so its
bytes in user frames by `JAtZ.fcap`), aligned (`hcv`), the buffer address
aligned (`hbuf`); the other TCBs' IPC frames kept. -/
theorem JAtZ.bokInstall {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    {c : capability.Cap} {src : Fl4Spec.CslotPtr} {σ' : Fl4Spec.State Unit} {s' : S}
    (hci : Fl4Spec.capInsert (Z := Unit) (absCap c) src (t.bv, Fl4Spec.tcbCnodeIndex 2) σ = ({((), σ')}, False))
    (hR' : StateRel Z.th (L.mem s') σ')
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2) → capV (L.mem s') y = capV (L.mem s) y)
    (hdst : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = c)
    {q : U64} {sz : capability.FrameSize} {rr aa va : U64} {m : Bool} (hc : c = .Frame q sz rr false m false aa va)
    (hq0 : q ≠ 0#u64) (hcv : CapValid Z.th c) {y0 : U64} (hy0 : IsSlot Z.th y0)
    (hk : okey c = okey (capV (L.mem s) y0))
    (hbuf : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbIpcBuffer.toNat % 1024 = 0) :
    Endp.IpcBufCapOK σ' := by
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap c) src (t.bv, Fl4Spec.tcbCnodeIndex 2) σ).1 := by
    rw [hci]; rfl
  have hkc : KeepCT σ σ' := KeepCT.of_cnK (capInsert_nkn _ _ _ σ _ hmem)
  have hpg : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      σ'.kheap p = some (.archObj (.dataPage false vms)) := fun p vms h => by
    rcases hkc p with e | ⟨_, _, _, h1, _⟩ | ⟨_, _, h1, _, _⟩
    · rw [e]; exact h
    · rw [h] at h1; cases h1
    · rw [h] at h1; cases h1
  intro t' x hx dev pb R mt vms md he hR
  -- the TCB before
  obtain ⟨x0, hx0, hbx⟩ : ∃ x0, σ.kheap t' = some (.tcb x0) ∧ x.tcbIpcBuffer = x0.tcbIpcBuffer := by
    rcases hkc t' with e | ⟨_, _, _, -, h2⟩ | ⟨x1, y, h1, h2, hco⟩
    · rw [e] at hx; exact ⟨x, hx, rfl⟩
    · rw [hx] at h2; cases h2
    · rw [hx] at h2; cases h2; exact ⟨x1, h1, hco.2.1⟩
  obtain ⟨u, rfl, hu⟩ := J.thOfTcb hx0
  obtain ⟨x', c', hkx, hcap', hcr⟩ := hR'.bufCap hu
  rw [hx] at hkx; cases hkx
  have he2 : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf u 2 := by
    show slotAddr u.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]
  have hAu : AbsSlot Z.th (u.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨u, rfl, Or.inr ⟨hu, 2, by decide, rfl⟩⟩
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
  by_cases e : u = t
  · subst e
    have hc'e : c' = c := by
      rw [← he2, capAt_capV, hdst] at hcap'; exact (eq_of_ok_eq hcap').symm
    rw [he, hc'e, hc] at hcr
    obtain ⟨-, h2⟩ := hcr
    simp only [absCap] at h2
    injection h2 with h2
    injection h2 with hd hp0 _ _ hsz _
    subst hd
    have hpv : q.val = pb.toNat := by rw [← hp0]; rfl
    have hbits : (fbitsF sz).val = Fl4Spec.pageBitsForSize vms := by rw [fbitsF_val, hsz]
    have hal : pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0 := by
      rw [hc] at hcv
      have h1 : q.val % 2 ^ frameBitsN sz = 0 := hcv
      have h2 : frameBitsN sz = (fbitsF sz).val := by
        rw [fbitsF_val]; cases sz <;> rfl
      rw [← hpv, ← hbits, ← h2]; exact h1
    have hba : x.tcbIpcBuffer.toNat % 1024 = 0 := by rw [hbx]; exact hbuf x0 hx0
    have hF : Vs.FrIn (UFr σ) c := Vs.FrIn.of_okey hk (J.fcap y0 hy0)
    rw [hc] at hF
    refine ⟨rfl, fun h0 => hq0 (P1.eq_of_bv (by rw [← hp0] at h0; exact h0)), fun k hk128 => ?_, hba, hal⟩
    obtain ⟨r1, r2, -⟩ := buf_frame_rng vms pb x.tcbIpcBuffer k hk128 hal hba
    have hU := hF rfl (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat
      (by rw [hpv]; exact r1) (by rw [hpv, hbits]; omega)
    have hU' : Fl4Spec.inUserFrame (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask
        (Fl4Spec.pageBitsForSize vms))) k) σ := by
      unfold UFr at hU; rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hU
    exact inUserFrame_keep hpg hU'
  · have hne : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2) ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2) := fun e' =>
      e (P1.eq_of_bv (congrArg Prod.fst (cslotAddr_inj J.xtop.rel.1 hAu hAt e')))
    obtain ⟨x2, c2, hkx2, hcap2, hcr2⟩ := J.xtop.rel.2.1.1.bufCap hu
    rw [hx0] at hkx2; cases hkx2
    have hcc : c' = c2 := by
      rw [← he2, capAt_capV, hcap _ hAu.isSlot hne] at hcap'
      rw [← he2, capAt_capV] at hcap2
      exact eq_of_ok_eq (hcap'.symm.trans hcap2)
    have hfr : x0.tcbIpcframe = x.tcbIpcframe := by rw [← hcr2.2, ← hcr.2, hcc]
    obtain ⟨h1, h2, h3, h4, h5⟩ := J.bok u.bv x0 hx0 dev pb R mt vms md (by rw [hfr]; exact he) hR
    rw [hbx]
    exact ⟨h1, h2, fun k hk => inUserFrame_keep hpg (h3 k hk), h4, h5⟩

end

/-! ## `SpecGlob` across the insert into a TCB slot -/

section
open Fl4Spec

/-- Every cap of `σ'` is `σ`'s in the same slot, or `c` at `dest`. -/
def InsK (c : Cap) (dest : CslotPtr) (σ σ' : State Unit) : Prop :=
  ∀ p cref a, capOpt (σ'.kheap p) cref = some a → ((p, cref) = dest ∧ a = c) ∨ capOpt (σ.kheap p) cref = some a

/-- Every outcome of `m` is `InsK`-related to its start. -/
def NIK (c : Cap) (dest : CslotPtr) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → InsK c dest σ x.2

theorem nik_bind {c : Cap} {dest : CslotPtr} {α β : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : NIK c dest m) (hg : ∀ a, NIK c dest (g a)) : NIK c dest (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩ p cref a ha
  rcases hg y.1 y.2 x hx p cref a ha with h | h
  · exact Or.inl h
  · exact hm σ y hy p cref a h

theorem nik_of_kh {c : Cap} {dest : CslotPtr} {α : Type} {m : NonDet (State Unit) α} (h : KhK m) :
    NIK c dest m := fun σ x hx p cref a ha => Or.inr (by have e : x.2.kheap = σ.kheap := h σ x hx; rw [← e]; exact ha)

theorem nik_setCap (c : Cap) (dest : CslotPtr) : NIK c dest (setCap (Z := Unit) c dest) := by
  obtain ⟨o, r⟩ := dest
  intro σ x hx p cref a ha
  rcases setCap_capOpt hx p cref a ha with ⟨e1, e2, e3⟩ | ⟨-, h⟩
  · exact Or.inl ⟨by rw [e1, e2], e3⟩
  · exact Or.inr h

/-- **`cap_insert` of a non-untyped cap writes only the cap at its
destination** (`set_untyped_cap_as_full` then does nothing). -/
theorem nik_capInsert {c : Cap} (hnu : ¬ isUntypedCap c = true) (src dest : CslotPtr) :
    NIK c dest (capInsert (Z := Unit) c src dest) := by
  have hg : ∀ sl : CslotPtr, KhK (getCap (Z := Unit) sl) := fun sl => by
    obtain ⟨o, r⟩ := sl; unfold getCap; kh_auto
  unfold capInsert
  refine nik_bind (nik_of_kh (hg _)) (fun srcCap => ?_)
  refine nik_bind (nik_of_kh (dk_pure _)) (fun _ => ?_)
  refine nik_bind (nik_of_kh (hg _)) (fun _ => ?_)
  refine nik_bind (nik_of_kh (dk_assert _)) (fun _ => ?_)
  refine nik_bind ?_ (fun _ => ?_)
  · unfold setUntypedCapAsFull
    rw [if_neg (fun h => hnu h.2.1)]
    exact nik_of_kh (dk_pure _)
  refine nik_bind (nik_setCap _ _) (fun _ => ?_)
  exact nik_of_kh (by unfold updateCdt setCdt setOriginal; kh_auto)

/-- **`SpecGlob` across an `InsK` step** writing, off the IRQ node, a cap
naming no more objects than a non-frame cap of `σ` (or a frame cap). -/
theorem SpecGlob.ins {c : Cap} {dest : CslotPtr} {σ σ' : State Unit} (h : SpecGlob σ) (hk : InsK c dest σ σ')
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) (hi : σ'.idleThread = σ.idleThread)
    (hd : ∀ irq, dest ≠ (σ.interruptIrqNode irq, []))
    (hc : ¬ IsPageCap c → ∃ p0 cref0 a0, capOpt (σ.kheap p0) cref0 = some a0 ∧ ¬ IsPageCap a0 ∧
      objRefs c ⊆ objRefs a0) : SpecGlob σ' := by
  refine ⟨fun irq a ha => ?_, fun p cref a ha hpa => ?_, fun p cref a ha hpa => ?_⟩
  · rw [hn] at ha
    rcases hk _ _ _ ha with ⟨e, -⟩ | h'
    · exact absurd e.symm (hd irq)
    · exact h.irq irq a h'
  · intro irq
    rw [hn]
    rcases hk _ _ _ ha with ⟨-, rfl⟩ | h'
    · obtain ⟨p0, cref0, a0, h0, hp0, hsub⟩ := hc hpa
      exact fun hm => h.ref p0 cref0 a0 h0 hp0 irq (hsub hm)
    · exact h.ref p cref a h' hpa irq
  · rw [hi]
    rcases hk _ _ _ ha with ⟨-, rfl⟩ | h'
    · obtain ⟨p0, cref0, a0, h0, hp0, hsub⟩ := hc hpa
      exact fun hm => h.idle p0 cref0 a0 h0 hp0 (hsub hm)
    · exact h.idle p cref a h' hpa

end

/-- `shape` keeps the objects a cap names and whether it is a frame cap. -/
theorem absCap_shape_refs (c : capability.Cap) :
    Fl4Spec.objRefs (absCap (shape c)) = Fl4Spec.objRefs (absCap c) ∧
      (IsPageCap (absCap (shape c)) ↔ IsPageCap (absCap c)) := by
  cases c <;> simp [shape, absCap, Fl4Spec.objRefs, IsPageCap, Fl4Spec.aobjRef]

/-- **`SpecGlob` across the insert into a TCB slot** of a non-untyped cap
with the shape of a cap of `σ` (`nik_capInsert`, `SpecGlob.ins`; a TCB slot
is no IRQ node slot). -/
theorem SpecGlob.insTcb {σ σ' : Fl4Spec.State Unit} (h : SpecGlob σ) {nc c0 : capability.Cap}
    {src : Fl4Spec.CslotPtr} {t : U64} {n : Nat}
    (hins : Fl4Spec.capInsert (Z := Unit) (absCap nc) src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hnut : isUt nc = false) (hsh : shape nc = shape c0)
    (hsrc : capOpt (σ.kheap src.1) src.2 = some (absCap c0)) : SpecGlob σ' := by
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap nc) src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by
    rw [hins]; rfl
  have hnu : ¬ Fl4Spec.isUntypedCap (absCap nc) = true := by
    cases nc <;> simp_all [isUt, absCap, Fl4Spec.isUntypedCap]
  have hk := nik_capInsert hnu src _ σ _ hmem
  have hgk := gk_capInsert (absCap nc) src (t.bv, Fl4Spec.tcbCnodeIndex n) σ _ hmem
  have hr := absCap_shape_refs nc
  have hr0 := absCap_shape_refs c0
  rw [hsh] at hr
  refine h.ins hk (congrArg Prod.fst hgk) (congrArg Prod.snd hgk) (fun irq e => ?_)
    (fun hp => ⟨src.1, src.2, absCap c0, hsrc, fun h0 => hp (hr.2.1 (hr0.2.2 h0)), fun x hx => ?_⟩)
  · have h2 := congrArg Prod.snd e
    simp [Fl4Spec.tcbCnodeIndex, Fl4Spec.toBl] at h2
  · rw [← hr.1, hr0.1] at hx; exact hx

/-! ## An install's outcome with an invariant after Ok and one after a preemption -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- `InstPostW` (TcbCaps) with `W` after an Ok install and `Wp` after a
preempted one. -/
def InstPostWP (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (t : U64)
    (m : Fl4Spec.PMonad Unit Unit) (s : S) (σ : Fl4Spec.State Unit)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ (m.run σ).1 ∧ InstFr th t (L.mem s) (L.mem res.2.1) ∧
        W res.2.1 res.2.2 σ' G') ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ (m.run σ).1 ∧ Wp res.2.1 res.2.2 σ' G')) ∧
    DState (L := L) th res.2.1 σ' G'

theorem inst_seqWP {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 : S}
    {σ : Fl4Spec.State Unit} {m1 m2 : Fl4Spec.PMonad Unit Unit}
    {P : Result (core.result.Result Unit error.Exc × S × A)}
    {K : S → A → Result (core.result.Result Unit error.Exc × S × A)}
    (h1 : P ⦃ res => InstPostWP (L := L) W Wp th t m1 s0 σ res ⦄)
    (h2 : ∀ s1 a1 σ1 G1, DState (L := L) th s1 σ1 G1 → (.ok (), σ1) ∈ (m1.run σ).1 →
      InstFr th t (L.mem s0) (L.mem s1) → W s1 a1 σ1 G1 →
      K s1 a1 ⦃ res => InstPostWP (L := L) W Wp th t m2 s0 σ1 res ⦄) :
    (do
      let (r, s1, a1) ← P
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => K s1 a1
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s1, a1)) ⦃ res => InstPostWP (L := L) W Wp th t (m1 >>= fun _ => m2) s0 σ res ⦄ := by
  apply WP.spec_bind h1
  rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hcase, hDS1⟩
  rcases hcase with ⟨hr, hmem, hcz, hW1⟩ | ⟨hr, hmem, hW1⟩
  · simp only at hr; subst hr
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_mono (h2 s1 a1 σ1 G1 hDS1 hmem hcz hW1) ?_
    rintro res ⟨σ2, G2, hc2, hDS2⟩
    refine ⟨σ2, G2, ?_, hDS2⟩
    rcases hc2 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, mem_bindE_ok hmem h2, h3, h4⟩
    · exact Or.inr ⟨h1, mem_bindE_ok hmem h2, h3⟩
  · simp only at hr; subst hr
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok]
    rw [WP.spec_ok]
    exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩

theorem inst_skipWP {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 : S}
    {σ : Fl4Spec.State Unit} {m2 : Fl4Spec.PMonad Unit Unit}
    {P : Result (core.result.Result Unit error.Exc × S × A)}
    (h : P ⦃ res => InstPostWP (L := L) W Wp th t m2 s0 σ res ⦄) :
    P ⦃ res => InstPostWP (L := L) W Wp th t (Fl4Spec.NonDetE.returnOk () >>= fun _ => m2) s0 σ res ⦄ := by
  have e : ∀ x, x ∈ ((Fl4Spec.NonDetE.returnOk () >>= fun _ => m2 : Fl4Spec.PMonad Unit Unit).run σ).1 ↔
      x ∈ (m2.run σ).1 := by
    intro x; rw [run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.PMonad Unit Unit)) rfl]
  refine WP.spec_mono h ?_
  rintro res ⟨σ', G', hc, hDS⟩
  refine ⟨σ', G', ?_, hDS⟩
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, (e _).2 h2, h3, h4⟩
  · exact Or.inr ⟨h1, (e _).2 h2, h3⟩

theorem inst_doneWP {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 s : S}
    {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) (hW : W s a σ G) (hcz : InstFr th t (L.mem s0) (L.mem s)) :
    (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a) :
      Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      InstPostWP (L := L) W Wp th t (Fl4Spec.NonDetE.returnOk ()) s0 σ res ⦄ := by
  rw [WP.spec_ok]
  exact ⟨σ, G, Or.inl ⟨rfl, rfl, hcz, hW⟩, hDS⟩

end

/-! ## The IPC buffer's word, and a scheduler step, at `J` -/

/-- A scheduler step (`SchedK`) keeps what `PPR0` reads. -/
theorem PPK.of_schedK {σ σ' : Fl4Spec.State Unit} (h : SchedK σ σ')
    (hns : ∀ u, σ'.schedulerAction ≠ .switchThread u) (hq : σ'.readyQueues = σ.readyQueues) : PPK σ σ' :=
  ⟨h.cons, h.ctime, h.csc, fun u hu => by rw [h.rel] at hu; exact hu,
    fun p y n hp => by rw [h.kh] at hp; exact hp, fun p y hp => ⟨y, by rw [h.kh] at hp; exact hp, rfl, id⟩, h.ct, h.idle,
    fun _ => hns, fun p x y hx hp hi => by rw [h.kh, hx] at hp; cases hp; exact Or.inl hi,
    fun h0 => by unfold CtNQ; rw [hq, h.ct]; exact h0⟩

/-- `reschedule_required` without a pending switch keeps the ready queues
(kp16). -/
theorem rq_of_resched {σ σ' : Fl4Spec.State Unit} (hn : ∀ t, σ.schedulerAction ≠ .switchThread t)
    (h : Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) : σ'.readyQueues = σ.readyQueues := by
  rw [Sched.rescheduleRequired_noswitch hn] at h
  have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).2
  rw [← e]

/-- An update of one TCB keeping its SC keeps what `PPR0` reads. -/
theorem PPK.updTcbSc {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hy : y.tcbSchedContext = x.tcbSchedContext)
    (hb : NotBlk x.tcbState → NotBlk y.tcbState := by first | exact id | (intro _; exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ _ h => by cases h⟩))
    (hi : x.tcbState = .inactive → y.tcbState = .inactive ∨ t = σ.curThread := by exact fun h => Or.inl h) :
    PPK σ (Notif.updK σ t (.tcb y)) := by
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun p z n hp => ?_, fun p z hp => ?_, rfl, rfl, fun h => h,
    fun p x' z hx hp hi' => ?_, fun h => h⟩
  rotate_right
  · by_cases e : p = t
    · subst e; rw [hk] at hx; cases hx; simp [Notif.updK] at hp; subst hp; exact hi hi'
    · simp [Notif.updK, e, hx] at hp; subst hp; exact Or.inl hi'
  · by_cases e : p = t
    · subst e; simp [Notif.updK] at hp
    · simpa [Notif.updK, e] using hp
  · by_cases e : p = t
    · subst e; simp [Notif.updK] at hp; subst hp; exact ⟨x, hk, hy.symm, hb⟩
    · exact ⟨z, by simpa [Notif.updK, e] using hp, rfl, id⟩

/-- The IPC-buffer update of one TCB empties and writes no cap. -/
theorem SlotK.ipcBuf {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (b : Fl4Spec.VSpaceRef) :
    SlotK σ (Notif.updK σ t (.tcb { x with tcbIpcBuffer := b })) := by
  intro p cref a ha
  right
  by_cases e : p = t
  · subst e
    rw [hk]
    simp only [Notif.updK, Function.update_self] at ha
    have e2 : capOpt (some (.tcb { x with tcbIpcBuffer := b })) cref =
        capOpt (some (.tcb x)) cref := rfl
    rw [e2] at ha; exact ha
  · simpa [Notif.updK, e] using ha

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 Fl4Proofs.P3.Sched in
set_option maxHeartbeats 8000000 in
/-- **A TCB's IPC-buffer word at `J`** (as XTopJointTcbSched's
`JAtZ.mcpWrJ`): FL4's word (offset 3512; P1's `BlkOK` by `plainW_all`),
the spec's `tcb_ipc_buffer` (`XTopAt.bufSpec`, a `QKM` step), `BufWordRel`
by XTopBuf's `bufWordRel_setIpc`; the other fields as `JAtZ.mcpWrJ`. -/
theorem JAtZ.bufWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) (hnf : x.tcbIpcframe = .nullCap) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (tIpcBufA t) v) a
      (Notif.updK σ t.bv (.tcb { x with tcbIpcBuffer := v.bv })) := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hKt : (tIpcBufA t).val = t.val + 3512 := tIpcBufA_val hta
  have hwa : P1.Aligned (tIpcBufA t) := tIpcBufA_aligned hta
  set s' := L.wr s (tIpcBufA t) v with hs'
  set σ' := Notif.updK σ t.bv (.tcb { x with tcbIpcBuffer := v.bv }) with hσ'
  have hw : P1.WritesIn st s s' (· = tIpcBufA t) := P1.writesIn_wr hwa
  obtain ⟨hblk, hfoot0, -⟩ := P1.plainW_all (K := 3512#u64) (v := v) J.blk htH (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hfoot : P1.WritesIn st s (L.wr s (tIpcBufA t) v) (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s) := hfoot0
  have hA : QKM σ σ' := QKM.ipcBuf hk v.bv
  have hX' : XTopAt (L := L) AR Z s' a σ' := (J.xtop.bufWr ht v).bufSpec (tcbBufStep_upd hk v.bv)
  have hks : L.ksb s' = L.ksb s := hw.1
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hwW : P1.WritesIn st s s' (WideW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩
  -- the words other than `t`'s IPC-buffer word kept
  have keep : ∀ b, P1.Aligned b → b ≠ tIpcBufA t → L.mem s' b = L.mem s b := fun b hb hne =>
    hw.mem_eq hb hne
  have hBW : BufWordRel Z.T (L.mem s') σ' := bufWordRel_setIpc J.xtop ht hk v J.buf
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  have hI := J.xtop.irelK J.ks J.buf
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb =>
    Or.inr (Or.inr (Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩))
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  -- the MCP, yield, SC-reply and reply-link words: not `t`'s IPC-buffer word
  have k1 : ∀ u ∈ Z.T, L.mem s' (mcpA u) = L.mem s (mcpA u) := fun u hu =>
    keep _ (mcpA_aligned hT hu) fun e => by
      have h1 := mcpA_val hT hu
      rw [e, hKt] at h1
      have a1 := (hT t ht).align; have a2 := (hT u hu).align
      by_cases eu : u = t
      · subst eu; omega
      · have := val_ne_of_ne eu; omega
  have k2 : ∀ u ∈ Z.T, L.mem s' (yieldA u) = L.mem s (yieldA u) := fun u hu =>
    keep _ (yieldA_aligned hT hu) fun e => by
      have h1 := yieldA_val hT hu
      rw [e, hKt] at h1
      have a1 := (hT t ht).align; have a2 := (hT u hu).align
      by_cases eu : u = t
      · subst eu; omega
      · have := val_ne_of_ne eu; omega
  have k3 : ∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q) := fun q hq =>
    keep _ (sc_reply_word hS hq).1 fun e => by
      obtain ⟨y, n, hky, -⟩ := hs.scs q hq
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hHq := (hJ.sc q y n (J.c0 q hq) hky).2
      have hz := J.kern.heap.scmin q _ hHq
      have h128 : 2 ^ 7 ≤ 2 ^ (n + Fl4Spec.minSchedContextBits) := Nat.pow_le_pow_right (by norm_num) hz
      have hv := (sc_reply_word hS hq).2.1
      rw [e, hKt] at hv
      have hne : q ≠ t := fun e' => by rw [e', J.zH.1 t ht] at hHq; cases hHq
      have := J.kern.heap.disj q _ t _ hHq (J.zH.1 t ht) hne
      simp only [P1.HKind.bits] at this
      omega
  have k4 : ∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      keep _ (J.rp.aligned hr ha) fun e => by
        have := J.rp.tcb r hr t ht; rw [e, hKt] at ha; omega
    exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hyk : YKeep σ σ' := by
    refine ⟨fun q y hq => ?_, fun q y n hq => ?_, fun q y n hq => ?_⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq; exact ⟨{ x with tcbIpcBuffer := v.bv }, by simp [hσ', Notif.updK], rfl⟩
      · exact ⟨y, by simp [hσ', Notif.updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · exact ⟨y, by simp [hσ', Notif.updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; simp [hσ', Notif.updK] at hq
      · exact ⟨y, by simpa [hσ', Notif.updK, e] using hq, rfl⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qm hA hS3 hI3.1 hwW k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.wideW_irq hwW)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwW.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 (mcpKeep_buf hk v.bv), hBW, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc), hkern,
      J.wideW_utc hwW hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, J.inv.updSame hk rfl rfl (Or.inl rfl), hA.cur J.cur,
      hA.own J.own, hA.off J.off, hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameIS hks hX3 hw (fun b hb => WideW.oobj (st := st) (T := Z.T) (N := Z.N) (C := Z.C) (c := Z.c) (σ := σ)
      (Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩))
      (fun b hb u hu => Sched.tVcpuA_ne (K := 3512) hT ht hu (by rw [hb, hKt]) (by omega) (by omega)) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback (J.bfK (IpcFrKeep.of_nullFrame hk hnf) (Vs.VsSlotsT.of_eq fun y hy => hF.1.capV hy)) hC R
      (dbgKeep_of_writes J.blk hw fun b hb => J.tcbw_notDbg ht (K := 3512) (by rw [hb, hKt]) (by omega)) hA.orig
      (XTopAt.idleW_eqS J.xtop hX3 hA.idle) J.zD⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxHeartbeats 8000000 in
/-- **TcbCaps' `BufHypW` at the deletion loop's invariant `WJR`**: the
IPC-buffer word and `thread_set` by `JAtZ.bufWrJ` (the scheduler action and
`PPR0` kept: `PPK.updTcbSc`); the tail's `reschedule_required` of the
current thread as a scheduler step (`JAtZ.schedJ`; after it the action is
`choose_new_thread`), with the spec's `ActReady` at the state's `JAtZ`
(`Sched.Inv.actReady`). -/
theorem bufHypW_J {t : U64} (ht : Z.th t = some .tcb) (kb addr : U64) :
    BufHypW (L := L) (WJR (L := L) arI AR Z H Cs kb) Z.th t addr addr.bv := by
  refine ⟨fun s a σ G hDS hW hnull => ?_, fun s a σ G _ hW => ?_⟩
  · obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩ := hW
    have hX := J.xtop
    have htT : t ∈ Z.T := J.thT t ht
    obtain ⟨Q, R0, hc, hs⟩ := hX.fin.1.1.1.lists
    obtain ⟨x, hk, -⟩ := hs.tcb t htT
    have hta := hc.tcbs t htT
    have hwa : P1.Aligned (tIpcBufA t) := tIpcBufA_aligned hta
    refine WP.spec_mono (set_ipc_buffer_wr s t addr) ?_
    rintro s' rfl
    have hstep := tcbBufStep_upd hk addr.bv
    obtain ⟨V', J'⟩ := J.bufWrJ htT hk addr (ipcframe_null_of hX.rel.2.1.1 ht hk hnull)
    refine ⟨hX.slotsSame_of (P1.writesIn_wr hwa) (fun b hb => by subst hb; exact tcb_oobj htT hta (by decide) (by decide)),
      _, ?_, J'.xtop.rel.2.1, hstep.ksub, V', Ac, Lst, D, J', by rw [L.ksb_wr]; exact hkb, fun u e => hns u e,
      hsg.of_slotK (SlotK.ipcBuf hk addr.bv) rfl rfl, hp0.of_ppk (PPK.updTcbSc hk rfl)⟩
    rw [Notif.threadSet_eq _ hk]; rfl
  · obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩ := hW
    have hX := J.xtop
    have hS := hX.fin.1.1.1
    obtain ⟨Q, R0, hc, hs⟩ := hS.lists
    have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
      rw [hs.curThread, hc.cur]; rfl
    rw [cur_thread_eq]
    simp only [bind_ok, tcb_eq_ct]
    by_cases e : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    · simp only [e, decide_true, ↓reduceIte]
      have hA1 : Notif.ActReady σ := J.inv.actReady
      obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA1
      have hN := hX.fin.1.1.2.2.1
      refine WP.spec_bind (WP.spec_and (WP.spec_and (Sched.reschedule_required_refines s _ hN hS hA1)
        (Sched.reschedule_required_sfootI hS)) (spec_self (Sched.reschedule_required_sfootI hS))) ?_
      rintro s5 ⟨⟨⟨σ3, he3, -, -, -, -⟩, hw⟩, hrun5⟩
      rw [hres] at he3
      have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
      subst σ3
      obtain ⟨Ac5, Lst5, D5, J5⟩ := J.schedJ (schedStep_resched hA1 hrun5 hres hK' hdl' hds')
      have hact5 := Sched.rescheduleRequired_action hA1 hres
      have hgk := gk_rescheduleRequired' σ ((), σ') (by rw [hres]; rfl)
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, hX.slotsSame_of hw (fun b hb => sfootI_oobj hc.tcbs hb), σ', ?_, J5.xtop.rel.2.1,
        KSub.of_kheap hK'.kh, V, Ac5, Lst5, D5, J5, by rw [hw.1]; exact hkb,
        (fun u e' => by rw [hact5] at e'; cases e'), hsg.of_eq hK'.kh (congrArg Prod.fst hgk) (congrArg Prod.snd hgk),
        hp0.of_ppk (PPK.of_schedK hK' (fun u e' => by rw [hact5] at e'; cases e') (rq_of_resched hns hres))⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : t.bv = σ.curThread := by rw [hcur, e]
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ')) (by rw [hres]; rfl)
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨trivial, trivial, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, σ, ?_, hX.rel.2.1, KSub.refl σ, V, Ac, Lst, D, J, hkb,
        hns, hsg, hp0⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : ¬ t.bv = σ.curThread := fun h => e (P1.eq_of_bv (h.trans hcur))
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ)) rfl

end

/-! ## The install at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

/-- **An invariant of the TCB installs at `J`** (module docstring): `WJR`
at the base sets, kept by an insert into an empty TCB slot of a cap alike an
existing one (`WJR` after it given), with TcbCaps' `BufHypW` at it. -/
structure InsWJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : Prop where
  wjr : ∀ s a σ G, W s a σ G → WJR (L := L) arI AR Z H Cs kb s a σ G
  ins : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G G' : MdbGhost) (t : U64) (n : Nat)
      (c : Fl4Spec.Cap) (src : Fl4Spec.CslotPtr),
    DState (L := L) Z.th s σ G → W s a σ G → DState (L := L) Z.th s' σ' G' →
    WJR (L := L) arI AR Z H Cs kb s' a σ' G' → Z.th t = some .tcb → n < tcbSlots →
    Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False) →
    P1.WritesIn st s s' (Sched.SlotWd Z.th) →
    capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null →
    (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → capV (L.mem s') y = capV (L.mem s) y) →
    capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null →
    (∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0)) →
    (∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) →
    W s' a σ' G'
  buf : ∀ t, Z.th t = some .tcb → ∀ addr : U64, BufHypW (L := L) W Z.th t addr addr.bv

/-- **`InsWJ` at `WJR`** (every insert's `WJR` after given; `bufHypW_J`). -/
theorem insWJ_wjr (kb : U64) : InsWJ (L := L) arI AR Z H Cs kb (WJR (L := L) arI AR Z H Cs kb) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ => h,
    fun _ ht addr => bufHypW_J arI ht kb addr⟩

set_option maxHeartbeats 16000000 in
/-- **`tcb::install_tcb_cap` at `J`** (module docstring): from the
deletion loop's invariant `WJR` at the base sets `Z`, `WJR` after an Ok
install, `WJP` after a preempted one. -/
theorem install_tcb_capJ [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid Z.th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc)
    (htu : Vs.TabUn nc → Vs.TabUn srcC0) (hnat : Vs.NativeCap srcC0 → Vs.NativeCap nc)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ⦄ := by
  obtain ⟨V0, Ac0, Lst0, D0, J0, -, -, -⟩ := hI.wjr _ _ _ _ hW
  have hP : Placed Z.th := J0.xtop.rel.1
  obtain ⟨K, hK, hK6, hDE⟩ := J0.delE
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht
  have hczs0 := hcz0.1 _ hAsrc.isSlot hsrcT
  have hsh0 : shape nc = shape (capV (L.mem s0) (cslotAddr (ps.bv, idxs))) := by rw [hsrc0]; exact hsh
  -- the insert after the delete, at `WJR`
  have after : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) Z.th s1 σ1 G1 →
      W s1 a1 σ1 G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null →
      ChgZ (L.mem s0) (L.mem s1) (cslotAddr (ps.bv, idxs)) →
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
          res.1 = .Ok () ∧ DState (L := L) Z.th res.2.1 σ' G' ∧
          (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
            capV (L.mem res.2.1) y = capV (L.mem s1) y) ∧
          (capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
            capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = nc) ∧
          W res.2.1 res.2.2 σ' G' ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hW1 hroot hczs
    refine WP.spec_mono (WP.spec_and (install_after Z.th hP s0 s1 a1 σ1 G1 hDS1 t ht n hn hroot ssl hAs nc hwf hcv he
      hfw hps hls hczs hsrc0 hsh hbd hkey hv)
      (install_after_frame hP s1 a1 hDS1.1.2.2.1 hDS1.2.1 t (cslotAddr ssl) nc hAsrc.isSlot hAt.isSlot)) ?_
    rintro res ⟨⟨σ', G', hrun, hr1, ha1, hDS', hcap, hst, htg, hcase⟩, hF⟩
    refine ⟨σ', G', hrun, hr1, hDS', hcap, htg, ?_⟩
    rcases hcase with ⟨e1, e2, e3⟩ | ⟨hins, hthr, hsrc1, hnn, hnut, hdst⟩
    · rw [ha1, e1, e2, e3]; exact hW1
    obtain ⟨V1, Ac1, Lst1, D1, J1, hkb1, hns1, hsg1, hp1⟩ := hI.wjr _ _ _ _ hW1
    have hsg' : SpecGlob σ' := by
      obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS1.1.1.abs_cap hAsrc
      have e0 : c0 = srcC0 := by rw [← hsrc1, capV_of_capAt hc0]
      have ha0 := (getCap_set_iff σ1 _ _ _).1 (congrArg Prod.fst hg0)
      rw [hca0.abs, e0] at ha0
      exact hsg1.insTcb hins hnut hsh ha0
    have hwS := SlotFrame2.writesIn hF
    obtain ⟨Ac2, Lst2, D2, J2⟩ := J1.insTJ (fun e => absurd e hn2) ht hn hins hDS' hst hwS hroot hcap
      (by rw [hdst]; exact hnut) (by rw [hdst]; exact hnn) ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩
      (fun h3 => by rw [hdst]; exact Or.inr (hep h3 hnn)) (fun e => absurd e hn2) ⟨_, hAs.isSlot, hthr⟩
      (fun P L4 L3 L2 L1 h => by
        rw [hdst]; exact h.copy hAsrc.isSlot (by rw [hsrc1]; exact hv) (by rw [hsrc1]; exact htu))
      (fun U h => by rw [hdst]; exact (h _ hAsrc.isSlot).of_okey (by rw [hsrc1]; exact hkey))
      (fun h => by rw [hdst]; exact hnat (by rw [← hsrc1]; exact h _ hAsrc.isSlot))
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap nc) (ps.bv, idxs)
        (t.bv, Fl4Spec.tcbCnodeIndex n) σ1).1 := by rw [hins]; rfl
    have hcn := capInsert_nkn _ _ _ σ1 _ hmem
    have hact : σ'.schedulerAction = σ1.schedulerAction := by
      have e := congrArg Fl4Spec.AbstractState.schedulerAction hcn.1; exact e
    rw [ha1]
    exact hI.ins s1 res.2.1 a1 σ1 σ' G1 G' t n _ _ hDS1 hW1 hDS'
      ⟨V1, Ac2, Lst2, D2, J2, by rw [hwS.1]; exact hkb1, fun u e => hns1 u (hact ▸ e), hsg',
        hp1.of_ppk (PPK.of_cnK hcn)⟩ ht hn hins hwS hroot hcap (by rw [hdst]; exact hnn)
      ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩ ⟨_, hAs.isSlot, hthr⟩
  unfold tcb.install_tcb_cap
  rw [spec_eq_ok (tcb_slot_spec t idx), tcb_root_eq t idx hn hidx]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    refine WP.spec_mono (after s a σ G hDS hW (by rw [capV_of_capAt hc0]) hczs0) ?_
    rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    exact ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok (by rw [capDelete_null hg0']; rfl) (mem_of_run hrun),
      hcz0.install hP ht hn (fun y hy hne => ChgZ.of_eq (hcap y hy hne)) htg hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩
  · apply WP.spec_bind (delete_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 _ hAt s a σ G hDS hW
      (by rw [capV_of_capAt hc0]; exact hc0n) (hDE.2.1 G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_mono (after s1 a1 σ1 G1 hDS1 hW1 hnull (hczs0.trans (hcz _ hAsrc.isSlot (hsrcT n hn)))) ?_
      rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
      exact ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok hmem (mem_of_run hrun),
        hcz0.install hP ht hn (fun y hy hne => (hcz y hy hne).trans (ChgZ.of_eq (hcap y hy hne))) htg
          hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩

/-- `install_tcb_capJ` with the new cap's conditions as `NewCapOK`. -/
theorem install_okJ [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) (hok : NewCapOK Z.th (L.mem s0) nc sl)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr sl) ⦃ res =>
      InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, sl))) s0 σ res ⦄ := by
  obtain ⟨ps, rs, hps, h1s, hls, hwf, hcv, he, hfw, hsh, hbd, hkey, hvk, htu, hnat⟩ := hok
  obtain ⟨sa, idxs⟩ := sl
  simp only at h1s hls; subst h1s
  exact install_tcb_capJ arI hI hH s0 s a σ G hDS hW t ht n hn hn2 idx hidx hcz0 ssl hAs nc hwf hcv he hfw hps hls rfl
    hsh hbd hkey hvk htu hnat hep

set_option maxHeartbeats 16000000 in
/-- **`tcb::install_buffer` at `J`** (as TcbCaps' `install_buffer_refinesW`):
the delete of the buffer slot by `delete_fullWR` (`WJP` when preempted), the
IPC buffer's word and the scheduler at `WJR` (`BufHypW`), the frame cap's
checks and insert by `check_insert`, the insert by `JAtZ.insTJ`. -/
theorem install_bufferJ [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G) (t : U64) (ht : Z.th t = some .tcb)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : BufHypW (L := L) W Z.th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK Z.th (L.mem s0) c sl)
    (hbfd : ∀ c sl, bfr = some (c, sl) → BufFrOK ptr c) (hfnz : ∀ c sl, bfr = some (c, sl) → FrNZ Z.th (L.mem s0)) :
    tcb.install_buffer st arI s a t (cslotAddr ssl) addr (bufArg bc0 bfr) ⦃ res =>
      InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ := by
  obtain ⟨V0, Ac0, Lst0, D0, J0, -, -, -⟩ := hI.wjr _ _ _ _ hW
  have hP : Placed Z.th := J0.xtop.rel.1
  obtain ⟨K, hK, hK6, hDE⟩ := J0.delE
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
  obtain ⟨c, s3, hbuf⟩ : ∃ c s3, bufArg bc0 bfr = (c, s3) := ⟨_, _, rfl⟩
  have cont : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) Z.th s1 σ1 G1 →
      W s1 a1 σ1 G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = .Null →
      InstFr Z.th t (L.mem s0) (L.mem s1) →
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
        InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
          (Fl4Spec.installTcbFrameCap t.bv ssl (some (ptr, frameOf bfr))) s0 σ res ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hW1 hnull hcz hmem
    apply WP.spec_bind (hBuf.ipc s1 a1 σ1 G1 hDS1 hW1 hnull)
    rintro s2 ⟨hS2, σ2, hts, hCR2, hK2, hW2⟩
    have hDS2 := hDS1.of_same hS2 hCR2 hK2
    have hnull2 : capV (L.mem s2) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = .Null := by
      rw [hS2.capV hAt.isSlot, hnull]
    cases bfr with
    | none =>
      simp only [bufArg, Prod.mk.injEq] at hbuf
      obtain ⟨rfl, rfl⟩ := hbuf
      simp only [still_valid_zero, bind_ok, Bool.false_eq_true, ↓reduceIte]
      apply WP.spec_mono (hBuf.tail s2 a1 σ2 G1 hDS2 hW2)
      rintro res ⟨hr1, -, hS5, σ5, htail, hCR5, hK6', hW5⟩
      refine ⟨σ5, G1, Or.inl ⟨hr1, ?_, (hcz.same hS2 ht).same hS5 ht, hW5⟩, hDS2.of_same hS5 hCR5 hK6'⟩
      refine mem_bindE_ok hmem (mem_bindE_ok (mem_liftE_ok hts) (mem_bindE_ok (s' := σ2) (a := ()) ?_ htail))
      exact mem_liftE_ok (x := ((), σ2)) rfl
    | some p =>
      obtain ⟨c', sl⟩ := p
      simp only [bufArg, Prod.mk.injEq] at hbuf
      obtain ⟨rfl, rfl⟩ := hbuf
      have hok := hbfr c' sl rfl
      obtain ⟨ps, rs, hps, h1s, hls, -, -, -, -, hshc, -⟩ := hok
      have hsrcIs : IsSlot Z.th (cslotAddr sl) := by
        obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
        exact (show AbsSlot Z.th (ps.bv, idxs) from ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩).isSlot
      have hsrcT : NotTcbSlot t (cslotAddr sl) := by
        obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
        exact cnode_slot_ne_tcb hP hps hls ht
      have hczs : ChgZ (L.mem s0) (L.mem s2) (cslotAddr sl) :=
        (hcz.1 _ hsrcIs hsrcT).trans (ChgZ.of_eq (hS2.capV hsrcIs))
      rw [← Std.bind_assoc]
      apply WP.spec_bind (WP.spec_and (check_insert Z.th hP s0 s2 σ2 G1 hDS2 t ht 2 (by decide) hnull2 ssl hAs c' sl
        (hbfr c' sl rfl) hczs) (check_insert_frame hP s2 hDS2.1.2.2.1 hDS2.2.1 t (cslotAddr ssl) c' hsrcIs hAt.isSlot))
      rintro s4 ⟨⟨σ4, G4, hchk, hDS4, hcap4, hst4, htg4, hcase⟩, hF4⟩
      have hW4 : W s4 a1 σ4 G4 := by
        rcases hcase with ⟨e1, e2, e3⟩ | ⟨hins, hthr, hsrc1, hnn, hnut, hdst⟩
        · rw [e1, e2, e3]; exact hW2
        obtain ⟨V2, Ac2, Lst2, D2, J2, hkb2, hns2, hsg2, hp2⟩ := hI.wjr _ _ _ _ hW2
        have hsg4 : SpecGlob σ4 := by
          obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS2.1.1.abs_cap
            (show AbsSlot Z.th sl by
              obtain ⟨sa, idxs⟩ := sl; simp only at h1s hls; subst h1s
              exact ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩)
          have e0 : c0 = capV (L.mem s0) (cslotAddr sl) := by rw [← hsrc1, capV_of_capAt hc0]
          have ha0 := (getCap_set_iff σ2 _ _ _).1 (congrArg Prod.fst hg0)
          rw [hca0.abs, e0] at ha0
          exact hsg2.insTcb hins hnut hshc ha0
        have hwS := SlotFrame2.writesIn hF4
        obtain ⟨⟨q, sz, rr, m, aa, va, hcF⟩, hbal⟩ := hbfd c' sl rfl
        obtain ⟨-, -, -, -, -, -, hcvc, -, -, -, -, hk', -, -⟩ := hbfr c' sl rfl
        have hk2 : okey c' = okey (capV (L.mem s2) (cslotAddr sl)) := by rw [hsrc1]; exact hk'
        have hq0 : q ≠ 0#u64 := by
          obtain ⟨r0, m0, e0, a0, v0, hs0⟩ : ∃ r0 m0 e0 a0 v0,
              capV (L.mem s0) (cslotAddr sl) = .Frame q sz r0 false m0 e0 a0 v0 := by
            rw [hcF] at hk'
            generalize capV (L.mem s0) (cslotAddr sl) = c0 at hk' ⊢
            cases c0 <;> simp [okey] at hk'
            obtain ⟨rfl, rfl, rfl⟩ := hk'
            exact ⟨_, _, _, _, _, rfl⟩
          exact hfnz c' sl rfl _ hsrcIs q sz r0 m0 e0 a0 v0 hs0
        have hbuf2 : ∀ x, σ2.kheap t.bv = some (.tcb x) → x.tcbIpcBuffer.toNat % 1024 = 0 := by
          intro x hx
          obtain ⟨x0, -, he⟩ := PPS.threadSet_mem hts
          have he' : σ2 = _ := he
          rw [he'] at hx
          simp only [Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
          subst hx; exact hbal
        have hbok4 := J2.bokInstall ht hins hDS4.1.1 hcap4 hdst hcF hq0 hcvc hsrcIs hk2 hbuf2
        obtain ⟨Ac4, Lst4, D4, J4⟩ := J2.insTJ (fun _ => hbok4) ht (n := 2) (by decide) hins hDS4 hst4 hwS hnull2 hcap4
          (by rw [hdst]; exact hnut) (by rw [hdst, hcF]; exact fun h => by cases h) ⟨_, hsrcIs, by rw [hdst, hsrc1]; exact hshc⟩
          (fun h => absurd h (by decide)) (fun _ => by rw [hdst, hcF]; exact Or.inr ⟨q, sz, rr, m, false, aa, va, rfl⟩)
          ⟨_, hAs.isSlot, hthr⟩
          (fun P L4 L3 L2 L1 h => by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hvk', htu', -⟩ := hbfr c' sl rfl
            rw [hdst]; exact h.copy hsrcIs (by rw [hsrc1]; exact hvk') (by rw [hsrc1]; exact htu'))
          (fun U h => by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk', -, -⟩ := hbfr c' sl rfl
            rw [hdst]; exact (h _ hsrcIs).of_okey (by rw [hsrc1]; exact hk'))
          (fun h => by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt'⟩ := hbfr c' sl rfl
            rw [hdst]; exact hnt' (by rw [← hsrc1]; exact h _ hsrcIs))
        have hmem' : ((), σ4) ∈ (Fl4Spec.capInsert (Z := Unit) (absCap c') sl
            (t.bv, Fl4Spec.tcbCnodeIndex 2) σ2).1 := by rw [hins]; rfl
        have hcn := capInsert_nkn _ _ _ σ2 _ hmem'
        have hact : σ4.schedulerAction = σ2.schedulerAction := by
          have e := congrArg Fl4Spec.AbstractState.schedulerAction hcn.1; exact e
        exact hI.ins s2 s4 a1 σ2 σ4 G1 G4 t 2 _ _ hDS2 hW2 hDS4
          ⟨V2, Ac4, Lst4, D4, J4, by rw [hwS.1]; exact hkb2, fun u e => hns2 u (hact ▸ e), hsg4,
            hp2.of_ppk (PPK.of_cnK hcn)⟩ ht (by decide) hins hwS hnull2 hcap4 (by rw [hdst]; exact hnn)
          ⟨_, hsrcIs, by rw [hdst, hsrc1]; exact hshc⟩ ⟨_, hAs.isSlot, hthr⟩
      apply WP.spec_mono (hBuf.tail s4 a1 σ4 G4 hDS4 hW4)
      rintro res ⟨hr1, -, hS5, σ5, htail, hCR5, hK6', hW5⟩
      have hAt2 : IsSlot Z.th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) := hAt.isSlot
      refine ⟨σ5, G4, Or.inl ⟨hr1, ?_, (hcz.same hS2 ht).install hP ht (n := 2) (by decide)
        (fun y hy hne => (ChgZ.of_eq (hcap4 y hy hne)).trans (ChgZ.of_eq (hS5.capV hy)))
        (by rw [hS5.capV hAt2]; exact htg4) hsrcIs hshc (fun h => absurd h (by decide)), hW5⟩,
        hDS4.of_same hS5 hCR5 hK6'⟩
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
    exact cont s a σ G hDS hW (by rw [capV_of_capAt hc0]) hcz0 (by rw [capDelete_null hg0']; rfl)
  · apply WP.spec_bind (delete_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 _ hAt s a σ G hDS hW
      (by rw [capV_of_capAt hc0]; exact hc0n) (hDE.2.1 G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact cont s1 a1 σ1 G1 hDS1 hW1 hnull (hcz0.delete hP ht (n := 2) (by decide) hcz hnull) hmem
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩

set_option maxHeartbeats 16000000 in
/-- **ThreadControl's cap installs at `J`**, as TcbCaps'
`thread_control_caps_refinesW` with `install_okJ` and `install_bufferJ`: `WJR` after an Ok run,
`WJP` after a preempted one. -/
theorem thread_control_capsJ [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK Z.th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK Z.th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK Z.th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK Z.th (L.mem s) vr.1 vr.2)
    (hfhE : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → fh.1 ≠ .Null →
      ∃ e b x1 x2 x3 x4, fh.1 = .Endpoint e b x1 x2 x3 x4)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHypW (L := L) W Z.th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK Z.th (L.mem s) c sl)
    (hbfd : ∀ c sl, bfr = some (c, sl) → BufFrOK ptr c) (hfnz : ∀ c sl, bfr = some (c, sl) → FrNZ Z.th (L.mem s)) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
        (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ := by
  have r0 : InstFr Z.th t (L.mem s) (L.mem s) := InstFr.refl _ _ _
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
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJ arI hI hH s s a σ G hDS hW t ht 3 (by decide) (by decide) _ i3 r0 ssl hAs
        _ _ (hfh hF) (fun _ => hfhE hF)) (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the timeout handler
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJ arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht 4
        (by decide) (by decide) _ i4 (by first | assumption | exact r0) ssl hAs _ _ (htmh hT) (fun h => absurd h (by decide)))
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the CSpace root
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJ arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht 0
        (by decide) (by decide) _ i0 (by first | assumption | exact r0) ssl hAs _ _ (hcr hS) (fun h => absurd h (by decide)))
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the VSpace root
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_okJ arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht 1
        (by decide) (by decide) _ i1 (by first | assumption | exact r0) ssl hAs _ _ (hvr hS) (fun h => absurd h (by decide)))
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  -- the IPC buffer
  (first
    | with_reducible refine inst_skipWP ?_
    | refine inst_seqWP (install_bufferJ arI hI hH s _ _ _ _ ‹DState _ _ _ _› (by first | assumption | exact hW) t ht
        (by first | assumption | exact r0) ssl hAs addr ptr (hBuf hU) bc0 bfr hbfr hbfd hfnz)
        (fun s1 a1 σ1 G1 hDS1 _ hcz1 hmo1 => ?_)) <;>
  exact inst_doneWP ‹DState _ _ _ _› (by first | assumption | exact hW) (by first | assumption | exact r0)

/-- **An install run's outcome at `WJR`/`WJP` after the restart is a
`TopPostDMXP` outcome at `JAt`/`JAtPre`** of the spec's ThreadControlCaps
invocation (`XTopAt`'s `DomRel` and `MdbOKV` after an Ok run, `WJP`'s after
a preemption). -/
theorem top_of_instJ {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    (hw : ∀ s a σ G, W s a σ G → WJR (L := L) arI AR Z H Cs kb s a σ G) {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {t : U64} {ssl : Fl4Spec.CslotPtr} {flags : U64}
    {fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr} {ptr : Fl4Spec.VSpaceRef}
    {bfr : Option (capability.Cap × Fl4Spec.CslotPtr)} {s s1 : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (hdec : DecOut m σ (tcInv t ssl flags fh tmh cr vr ptr bfr))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
      (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s1 σ1 res) :
    TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don m s res := by
  obtain ⟨σ', G', hc, hDS'⟩ := h
  rcases hc with ⟨hr, hx, -, hW'⟩ | ⟨hr, hx, hW'⟩
  · obtain ⟨V, Ac', Lst', D', J', -⟩ := hw _ _ _ _ hW'
    have hX' := J'.xtop
    refine Or.inr ⟨_, hdec, σ1, hst, tcRet (.ok (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx,
      ⟨Z.th, G', Or.inl ⟨hr, rfl⟩, hX'.rel.1, hDS'.1, hDS'.2.2, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
    show if res.1 = .Err .Preempted then _ else _
    rw [if_neg (by rw [hr]; exact fun e => by cases e)]
    exact ⟨_, H, Cs, Ac', Lst', D', J'⟩
  · obtain ⟨s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hW'
    refine Or.inr ⟨_, hdec, σ1, hst, tcRet (.error (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx,
      ⟨Z.th, G', Or.inr ⟨hr, rfl⟩, J0.xtop.rel.1, hDS'.1, hDS'.2.2, hDom, hMO⟩, ?_⟩
    show if res.1 = .Err .Preempted then _ else _
    rw [if_pos hr]
    exact ⟨s0, a0, σ0, ⟨⟨_, H, Cs, Ac', Lst', D', J0⟩, hns0, hp00⟩, hpp, hspp⟩

end

/-! ## The caller's restart, and the Thread cap's labels at `J` with a preemption -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The caller's restart at `J`** (`tcb::restart_caller`): FL4's and the
spec's (`restart_dstate`), `XTopAt` after (`XTopAt.restart`), the rest by
`jowes_restart`; no switch pending after (`Entered`), the idle thread kept. -/
theorem JAtZ.restartJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∃ s1 σ1 x, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      σ.kheap ct.bv = some (.tcb x) ∧ σ.curThread = ct.bv ∧
      σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv ∧
      (∀ u, σ1.schedulerAction = .switchThread u → False) ∧ σ1.idleThread = σ.idleThread ∧
      σ1.curThread = σ.curThread ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 ar σ1 := by
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ :=
    restart_dstate Z.th J.xtop.rel.1 s σ Z.G hDS ct hct hcur htcb J.kern.act
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  refine ⟨s1, σ1, x, hrc1, hst1, hk, hcur, e, ?_, ?_, ?_, hs1, Ac', Lst', D, ?_⟩
  · subst e
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  · subst e; unfold Notif.stsAct; split_ifs <;> rfl
  · subst e; exact (stsAct_fields _ _).2.1
  · subst e; exact J1


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `tcb::decode` at one label keeping `X`, `XP` after a preemption
(`TopPostDMXP`). -/
abbrev TcbOKXP (X XP : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64)
    (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPostDMXP (L := L) X XP σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) s res ⦄

/-- **A Thread cap label's `XCapP` from its `TcbOKXP`** (as
`decode_invocation_threadX` for one label; the fast-path flag's decode
error at the start's `X`). -/
theorem xcapP_of_tcb {X XP : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : X s ar σ) (lbl length slot p : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (h : TcbOKXP (L := L) arI X XP s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer) :
    XCapP (L := L) arI X XP s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer
      ct := by
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact hX0

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The caller's restart at the deletion loop's invariant**: `JAtZ.restartJ`,
with `NoSwitch` after (`Entered`), `SpecGlob` (`SpecGlob.sts`) and `PPR0` kept
(`PPK.restart`). -/
theorem JAtZ.restartWJR {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∃ s1 σ1, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      DState (L := L) Z.th s1 σ1 Z.G ∧ WJR (L := L) arI AR Z H Cs (L.ksb s1) s1 ar σ1 Z.G ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) := by
  obtain ⟨s1, σ1, x1, hrc, hst1, hk, hcur, e1, hns1, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨s1', σ1', hrc', -, -, hS1, -⟩ := restart_dstate Z.th J.xtop.rel.1 s σ Z.G J.dstate ct hct hcur htcb J.kern.act
  rw [hrc] at hrc'
  cases eq_of_ok_eq hrc'
  have hp1 : PPR0 σ1 := by rw [e1]; exact hP0.of_ppk (PPK.restart hk .restart (Or.inl hcur.symm))
  exact ⟨s1, σ1, hrc, hst1, J1.dstate, ⟨Z.vs, Ac1, Lst1, D1, J1, rfl, hns1, SpecGlob.sts (mem_of_single hst1) hsg,
    hp1⟩, hS1⟩

/-- **The TCB installs' invariants at every kernel-state base** (module
docstring): `InsWJ` and the deletion loop's steps (`DelHypsWRZ`) at `W kb`. -/
structure TcbInsW (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) : Prop where
  ins : ∀ kb, InsWJ (L := L) arI AR Z H Cs kb (W kb)
  del : ∀ kb, DelHypsWRZ (L := L) arI (W kb) (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th

/-- The caller's restart from `s` establishes `W` (for `JAtZ.restartW`). -/
abbrev RestartWJ (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : Prop :=
  ∀ ct, sched.cur_thread st s = ok ct → ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W s1 ar σ1 Z.G

/-- **The caller's restart at the installs' invariant**: `JAtZ.restartWJR`
with `W` after it (`RestartWJ`), at the kernel-state base after. -/
theorem JAtZ.restartW {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop} {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop}
    (hI : TcbInsW (L := L) arI AR Z H Cs W Rd Rz)
    (hR : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W (L.ksb s) s1 ar σ1 Z.G) :
    ∃ s1 σ1, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      DState (L := L) Z.th s1 σ1 Z.G ∧ W (L.ksb s1) s1 ar σ1 Z.G ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) := by
  obtain ⟨s1, σ1, hrc, hst1, hDS1, -, hS1⟩ := J.restartWJR arI hni hsg hP0 hct
  obtain ⟨s1', σ1', -, hrc', hst1', -, -, -, -, -, -, hs1', -⟩ := J.restartJ hni hct
  have es : s1' = s1 := Result.ok_injective (hrc'.symm.trans hrc)
  have eσ : σ1' = σ1 :=
    (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (hst1'.symm.trans hst1)))).2
  subst es eσ
  have hW := hR s1' σ1' hs1' hst1
  obtain ⟨-, -, -, -, -, hkb, -⟩ := (hI.ins _).wjr _ _ _ _ hW
  exact ⟨s1', σ1', hrc, hst1, hDS1, by rw [hkb]; exact hW, hS1⟩

set_option maxHeartbeats 8000000 in
/-- **The SetTimeoutEndpoint label at `JAt`** (`JAtPre` if preempted), as
TcbCtl's `tcb_set_timeout_refinesW`: the decode, the caller's restart
(`JAtZ.restartWJR`), the timeout handler's install by `thread_control_capsJ`
at the deletion loop's steps (`DelHypsWR` at `WJR`), `top_of_instJ`. -/
theorem tcb_set_timeoutJ [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsW (L := L) arI AR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTimeoutEndpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (args : List Fl4Spec.Data) (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.TCBSetTimeoutEndpoint p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl args ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl args ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKXP
  rw [decode_timeout_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_timeout_endpoint tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTimeoutEp
    rw [whenE_pos (by omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 0#u64 := by scalar_tac
  simp only [h0, ↓reduceIte, if_pos hge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, slot_cap_eq,
    capAt_capV, vfh_eq]
  have hspec0 : ∀ v : Prop, [Decidable v] → v = Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0)) →
      (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps).run σ =
        (Fl4Spec.checkHandlerEp (Z := Unit) 1 e >>= fun handler =>
          Fl4Spec.NonDetE.returnOk (.threadControlCaps p.bv ssl none (some handler) none none none)).run σ := by
    intro v _ _
    unfold Fl4Spec.decodeSetTimeoutEp
    rw [whenE_neg (by have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega),
      retOk_bind, retOk_bind, he, the_some]
    rfl
  by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0))
  · rw [decide_eq_true hv]; simp only [↓reduceIte]
    obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartW arI hni hsg hP0 hct hHp (hR ct hct)
    rw [hrc]; simp only [bind_ok]
    have hxs : IsSlot Z.th x0 := by rw [hxe]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.ok (tcInv p ssl tcb.UPDATE_TIMEOUT (.Null, (0, [])) (capV (L.mem s) x0, e.2) (.Null, (0, []))
          (.Null, (0, [])) (0 : BitVec 64) none), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec0 _ rfl]
      unfold Fl4Spec.checkHandlerEp
      rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he1]; exact hv)]
      show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e) >>= _).run σ = _
      rw [retOk_bind, retOk_bind]
      obtain ⟨e1, e2⟩ := e
      simp only at he1
      subst he1
      simp only [tcInv, optArg, flags_T, ↓reduceIte]
      rfl
    have hnf := vfh_not_frame hv
    have hc1 : capV (L.mem s1) x0 = capV (L.mem s) x0 := hS1.capV hxs
    have hU0 : (tcb.UPDATE_TIMEOUT &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 := by
      simp only [tcb.UPDATE_TIMEOUT, tcb.UPDATE_IPC_BUFFER]; decide
    have hT' := thread_control_capsJ arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs tcb.UPDATE_TIMEOUT
      (.Null, (0, [])) (capV (L.mem s) x0, e.2) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_T.1 h).elim)
      (fun _ => by
        show NewCapOK Z.th (L.mem s1) (capV (L.mem s) x0) e.2
        rw [← hc1, hxe]
        exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe, hc1]; exact hnf))
      (fun h => (Eq.mp flags_T.2.2.1 h).elim) (fun h => (Eq.mp flags_T.2.2.1 h).elim) (fun _ h => absurd rfl h)
      0#u64 0 (fun h => absurd hU0 h) .Null none (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    simp only [cslot_zero, ← hxe] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instJ arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
  · rw [decide_eq_false hv]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_,
      Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0 _ rfl]
    unfold Fl4Spec.checkHandlerEp
    rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he1]; exact hv)]
    exact run_bind_error (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
      Fl4Spec.SEMonad Unit Unit)) rfl _) _


set_option maxHeartbeats 16000000 in
/-- **The SetSpace label at `JAt`** (`JAtPre` if preempted), as TcbCtl's
`tcb_set_space_refinesW`: the decode (the roots by `roots_rel`), the
caller's restart (`JAtZ.restartWJR`), the fault handler's and the roots'
installs by `thread_control_capsJ`, `top_of_instJ`. -/
theorem tcb_set_spaceJ [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsW (L := L) arI AR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSpace)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.TCBSetSpace p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hP := J.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := J.dstate
  unfold TcbOKXP
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSpace (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_space_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR)
        (JAtPre (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSpace (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSpace
    rw [whenE_pos (by simpa using h)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  unfold tcb.decode_set_space tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexc : excaps = [e0, e1, e2] := by
    have h3 := hX.1
    match excaps, he0, he1, he2, h3 with
    | [a, b, c], h0', h1', h2', _ => simp at h0' h1' h2'; rw [h0', h1', h2']
  subst hexc
  subst hxe1 hxe2
  obtain ⟨r, hr, hcase⟩ := roots_rel Z.th hP s σ Z.G hDS p hp y0 y1 e1 e2 he11 ⟨ps1, hps1, hps11⟩ he21
    ⟨ps2, hps2, hps21⟩ (hnc _ (by simp) e1.2 ⟨ps1, hps11, Or.inl hps1⟩ rfl) (hnc _ (by simp) e2.2 ⟨ps2, hps21, Or.inl hps2⟩ rfl) ssl
  rw [hr]
  have hspec : (Fl4Spec.decodeSetSpace (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      [e0, e1, e2]).run σ =
      (Fl4Spec.decodeCvSpace (Z := Unit) [y0.bv, y1.bv] (.threadCap p.bv) ssl [e1, e2] >>= fun space =>
        Fl4Spec.checkHandlerEp (Z := Unit) 1 e0 >>= fun fh =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl (some fh) none
            space.tcNewCroot space.tcNewVroot none)).run σ := by
    unfold Fl4Spec.decodeSetSpace
    rw [whenE_neg (by simp), retOk_bind]
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, the_some, retOk_bind]
    rfl
  rcases hcase with ⟨cc, vc, rfl, hcv, hokc, hokv⟩ | ⟨e, e', rfl, hcv, herr⟩
  · simp only [slot_cap_eq, capAt_capV, vfh_eq, bind_ok]
    rw [run_bind_ok hcv] at hspec
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0))
    · rw [decide_eq_true hv]; simp only [↓reduceIte, lift, bind_ok]
      obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartW arI hni hsg hP0 hct hHp (hR ct hct)
      rw [hrc]; simp only [bind_ok]
      have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact AbsSlot.isSlot ⟨ps0, hps01, Or.inl hps0⟩
      have hc1 : capV (L.mem s1) x0 = capV (L.mem s) x0 := hS1.capV hxs
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSpace (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            [e0, e1, e2])).run σ =
          ({(.ok (tcInv p ssl (tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) (capV (L.mem s) x0, e0.2) (.Null, (0, []))
            (cc, e1.2) (vc, e2.2) (0 : BitVec 64) none), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he01]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e0) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]
        obtain ⟨e01, e02⟩ := e0
        simp only at he01
        subst he01
        simp only [optArg, flags_SF, ↓reduceIte]
        rfl
      have hU0 : ((tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 := by
        simp only [tcb.UPDATE_SPACE, tcb.UPDATE_FAULT, tcb.UPDATE_IPC_BUFFER]; decide
      have hT' := thread_control_capsJ arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs
        (tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT)
        (capV (L.mem s) x0, e0.2) (.Null, (0, [])) (cc, e1.2) (vc, e2.2)
        (fun _ => by
          show NewCapOK Z.th (L.mem s1) (capV (L.mem s) x0) e0.2
          rw [← hc1, hxe0]
          exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps0 hps01 (by rw [← hxe0, hc1]; exact vfh_not_frame hv))
        (fun h => (Eq.mp flags_SF.2.1 h).elim) (fun _ => hokc.of_same hS1) (fun _ => hokv.of_same hS1)
        (fun _ => vfh_ep hv) 0#u64 0 (fun h => absurd hU0 h) .Null none (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      simp only [cslot_zero, ← hxe0, bufArg] at hT'
      exact WP.spec_mono hT' (fun res h => top_of_instJ arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
    · rw [decide_eq_false hv]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_,
        Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec]
      unfold Fl4Spec.checkHandlerEp
      rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he01]; exact hv)]
      exact run_bind_error (run_bind_error (m := (Fl4Spec.NonDetE.throwError
        (Fl4Spec.SyscallError.invalidCapability 1) : Fl4Spec.SEMonad Unit Unit)) rfl _) _
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨e', ?_, herr⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error hcv _


set_option maxHeartbeats 16000000 in
/-- **The SetIPCBuffer label at `JAt`** (`JAtPre` if preempted), as TcbCtl's
`tcb_set_ipc_refinesW`: the decode (the buffer's frame cap derived and
checked), the caller's restart (`JAtZ.restartWJR`), the buffer's install by
`thread_control_capsJ` (`install_bufferJ`, the IPC-buffer word and the tail
at `WJR` by `bufHypW_J`), `top_of_instJ`. -/
theorem tcb_set_ipcJ [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsW (L := L) arI AR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hfnz : FrNZ Z.th (L.mem s))
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.TCBSetIPCBuffer p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hDS : DState (L := L) Z.th s σ Z.G := J.dstate
  unfold TcbOKXP
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_ipc_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_ipc_buffer tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  -- the truncated cases
  have htr : args = [] ∨ excaps = [] →
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.error .truncatedMessage, σ)}, False) := by
    intro h
    apply run_liftME_err
    unfold Fl4Spec.decodeSetIpcBuffer
    by_cases ha : args = []
    · subst ha
      rw [whenE_pos (by simp)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · have he : excaps = [] := h.resolve_left ha
      subst he
      rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (by simp)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
  have htrS : (args = [] ∨ excaps = []) → TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ
      blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s
        (.Err (.Sys .TruncatedMessage), s, ar) := fun h =>
    TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, htr h, Or.inl trivial⟩, hJ0⟩
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (htrS (Or.inr (List.eq_nil_of_length_eq_zero (by omega))))
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  by_cases h1 : length < 1#u64
  · have hge : ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 := by
      show ¬ length >= 1#u64; scalar_tac
    simp only [h0, ↓reduceIte, if_neg hge, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (htrS (Or.inl ?_))
    exact List.eq_nil_of_length_eq_zero (by scalar_tac)
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 := by
    show length >= 1#u64; scalar_tac
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  simp only [h0, ↓reduceIte, if_pos hge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  -- the spec, up to the buffer
  obtain ⟨e1, e2⟩ := e
  simp only at hxe he1 hps hps1
  subst he1 hxe
  have hspec : (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ =
      ((if y0.bv = 0 then Fl4Spec.NonDetE.returnOk none else do
          let bc ← Fl4Spec.deriveCap (Z := Unit) e2 (absCap (capV (L.mem s) (cslotAddr e2)))
          Fl4Spec.checkValidIpcBuffer y0.bv bc
          Fl4Spec.NonDetE.returnOk (some (bc, e2)) : Fl4Spec.SEMonad Unit _) >>= fun nb =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none none none
          (some (y0.bv, nb)))).run σ := by
    unfold Fl4Spec.decodeSetIpcBuffer
    have hne : excaps ≠ [] := List.ne_nil_of_mem (List.mem_of_getElem? he)
    rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simpa using hne), retOk_bind, retOk_bind]
    rw [show (List.map UScalar.bv (y0 :: rest))[0]? = some y0.bv from rfl, the_some, retOk_bind, he, the_some]
    rfl
  obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartW arI hni hsg hP0 hct hHp (hR ct hct)
  have hxs : IsSlot Z.th (cslotAddr e2) := AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1) (cslotAddr e2) = capV (L.mem s) (cslotAddr e2) := hS1.capV hxs
  have hcwf := slot_wf hDS.1.1 hps hps1
  have hcv0 : CapValid Z.th (capV (L.mem s) (cslotAddr e2)) :=
    hDS.1.2.1.abs ⟨ps, hps1, Or.inl hps⟩ (capAt_capV _ _)
  have hB : (tcb.UPDATE_IPC_BUFFER &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 →
      BufHypW (L := L) (W (L.ksb s1)) Z.th p y0 y0.bv :=
    fun _ => (hHp.ins (L.ksb s1)).buf p hp y0
  by_cases hy : y0 = 0#u64
  · -- no frame
    have hy' : y0.bv = 0 := by rw [hy]; rfl
    have hdfb : tcb.derive_for_buffer st s y0 (cslotAddr e2) = ok (.Ok (capV (L.mem s) (cslotAddr e2), 0#u64)) := by
      unfold tcb.derive_for_buffer; rw [if_pos hy]; simp [slot_cap_eq, capAt_capV]
    rw [hdfb]; simp only [bind_ok, hrc]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.ok (tcInv p ssl tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
          (.Null, (0, [])) y0.bv none), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec, if_pos hy', retOk_bind]
      simp only [tcInv, optArg, flags_B, ↓reduceIte, frameOf]
      rfl
    have hT' := thread_control_capsJ arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs tcb.UPDATE_IPC_BUFFER
      (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_B.1 h).elim)
      (fun h => (Eq.mp flags_B.2.1 h).elim) (fun h => (Eq.mp flags_B.2.2.1 h).elim)
      (fun h => (Eq.mp flags_B.2.2.1 h).elim) (fun _ h => absurd rfl h) y0 y0.bv hB
      (capV (L.mem s) (cslotAddr e2)) none (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    simp only [cslot_zero, bufArg] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instJ arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
  -- a frame: derived and checked
  have hy' : ¬ y0.bv = 0 := fun h => hy (UScalar.eq_of_val_eq (by
    have := congrArg BitVec.toNat h; simpa using this))
  unfold tcb.derive_for_buffer
  rw [if_neg hy]
  simp only [slot_cap_eq, capAt_capV, bind_ok]
  generalize capV (L.mem s) (cslotAddr e2) = c0 at hcwf hcv0 hc1 hnc hspec ⊢
  obtain ⟨r, hr, r', hr', hrel⟩ := derive_rel (st := st) s σ (cslotAddr e2) e2 c0
    hcwf.1 hcwf.2 (fun h => hnc e2 ⟨ps, hps1, Or.inl hps⟩ rfl (by cases c0 <;> simp_all [isUt]))
  simp only [hr, bind_ok]
  cases r with
  | Err er =>
    cases r' with
    | ok _ => exact hrel.elim
    | error er' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨er', ?_, Or.inl hrel⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec, if_neg hy']
      exact run_bind_error (run_bind_error hr' _) _
  | Ok c' =>
    cases r' with
    | error _ => exact hrel.elim
    | ok a =>
      obtain ⟨hwf', ha, hev', hcv', -⟩ := hrel
      obtain ⟨rc, hrc', hcase⟩ := Vs.check_valid_ipc_buffer_rel y0 c' σ
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hrc']
      rcases hcase with ⟨rfl, hck⟩ | ⟨er, er', rfl, hmer, hck⟩
      · simp only [bind_ok, hrc]
        obtain ⟨q, sz, rr, m, ep, aa, va, rfl⟩ := check_ok_frame hrc'
        obtain ⟨rfl, m0, ep0, a0, va0, hc0⟩ := derive_frame_inv (fun h => ⟨_, hnc e2 ⟨ps, hps1, Or.inl hps⟩ rfl h⟩) hr
        have hcvc : CapValid Z.th (capability.Cap.Frame q sz rr false m false aa va) := hcv' Z.th hcv0
        have hok : NewCapOK Z.th (L.mem s1) (.Frame q sz rr false m false aa va) e2 := by
          refine ⟨ps, _, hps, hps1, rfl, hwf', hcvc, hev', fun _ => frame_so_refl hcvc, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hc1, hc0]; rfl
          · rw [hc1, hc0]; exact Or.inl rfl
          · rw [hc1, hc0]; rfl
          · rw [hc1]; exact derive_vcap hr
          · exact fun h => False.elim h
          · exact fun _ => by simp [Vs.NativeCap]
        have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)).run σ =
            ({(.ok (tcInv p ssl tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
              (.Null, (0, [])) y0.bv (some (.Frame q sz rr false m false aa va, e2))), σ)}, False) := by
          apply run_liftME_ok
          rw [← ha] at hr'
          have hin : ((do
              let bc ← Fl4Spec.deriveCap (Z := Unit) e2 (absCap c0)
              Fl4Spec.checkValidIpcBuffer y0.bv bc
              Fl4Spec.NonDetE.returnOk (some (bc, e2)) : Fl4Spec.SEMonad Unit _)).run σ =
              ({(.ok (some (absCap (.Frame q sz rr false m false aa va), e2)), σ)}, False) := by
            rw [run_bind_ok hr', run_bind_ok hck]; rfl
          rw [hspec, if_neg hy', run_bind_ok hin]
          simp only [tcInv, optArg, flags_B, ↓reduceIte, frameOf]
          rfl
        have hT' := thread_control_capsJ arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs
          tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
          (fun h => (Eq.mp flags_B.1 h).elim) (fun h => (Eq.mp flags_B.2.1 h).elim)
          (fun h => (Eq.mp flags_B.2.2.1 h).elim) (fun h => (Eq.mp flags_B.2.2.1 h).elim) (fun _ h => absurd rfl h)
          y0 y0.bv hB .Null (some (.Frame q sz rr false m false aa va, e2)) (fun c sl h => by cases h; exact hok)
          (fun c sl h => by cases h; exact ⟨⟨q, sz, rr, m, aa, va, rfl⟩, Vs.check_valid_ipc_buffer_al hrc'⟩)
          (fun _ _ _ => hfnz.of_same hS1)
        simp only [cslot_zero, bufArg] at hT'
        exact WP.spec_mono hT' (fun res h => top_of_instJ arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
      · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, bind_ok]
        refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨er', ?_, ErrRel.of_map hmer⟩, hJ0⟩)
        apply run_liftME_err
        rw [hspec, if_neg hy']
        rw [← ha] at hr'
        exact run_bind_error ((run_bind_ok hr' _).trans (run_bind_error hck _)) _


set_option maxHeartbeats 16000000 in
/-- **The Configure label at `JAt`** (`JAtPre` if preempted), as TcbCtl's
`tcb_configure_refinesW`: the decode (the buffer by `buf_rel`, the roots by
`roots_rel`), the caller's restart (`JAtZ.restartWJR`), the roots' and the
buffer's installs by `thread_control_capsJ` (the buffer's word and tail at
`WJR` by `bufHypW_J`), `top_of_instJ`. -/
theorem tcb_configureJ [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsW (L := L) arI AR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hfnz : FrNZ Z.th (L.mem s))
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.TCBConfigure p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hP := J.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := J.dstate
  unfold TcbOKXP
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeTcbConfigure (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_configure_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 3 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR)
        (JAtPre (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeTcbConfigure (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeTcbConfigure
    by_cases ha : args.length < 3
    · rw [whenE_pos (by simpa using ha)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
  unfold tcb.decode_configure tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 3#u64 ↔ 3 ≤ args.length := by
    show length >= 3#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 3 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, y2, rest, rfl⟩ : ∃ y0 y1 y2 rest, args = y0 :: y1 :: y2 :: rest := by
    match args, hl with
    | y0 :: y1 :: y2 :: rest, _ => exact ⟨_, _, _, _, rfl⟩
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  have ha2 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 2#u64 = ok y2 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 2#u64 y2 (by simp)
  rw [ha0, ha1, ha2]; simp only [bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexc : excaps = [e0, e1, e2] := by
    have h3 := hX.1
    match excaps, he0, he1, he2, h3 with
    | [a, b, c], h0', h1', h2', _ => simp at h0' h1' h2'; rw [h0', h1', h2']
  subst hexc
  subst hxe0 hxe1 hxe2
  have hspec : (Fl4Spec.decodeTcbConfigure (Z := Unit) ((y0 :: y1 :: y2 :: rest).map UScalar.bv) (.threadCap p.bv)
      ssl [e0, e1, e2]).run σ =
      (Fl4Spec.decodeSetIpcBuffer (Z := Unit) [y2.bv] (.threadCap p.bv) ssl [e2] >>= fun sp =>
        Fl4Spec.decodeCvSpace (Z := Unit) [y0.bv, y1.bv] (.threadCap p.bv) ssl [e0, e1] >>= fun ss =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none
            ss.tcNewCroot ss.tcNewVroot sp.tcNewBuffer)).run σ := by
    unfold Fl4Spec.decodeTcbConfigure
    rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simp), retOk_bind]
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.getElem?_cons_succ,
      List.getElem?_cons_zero, the_some, retOk_bind]
    rfl
  obtain ⟨rb, hrb, hbcase⟩ := buf_rel Z.th s σ Z.G hDS y2 e2 he21 ⟨ps2, hps2, hps21⟩ (hnc _ (by simp) e2.2 ⟨ps2, hps21, Or.inl hps2⟩ rfl)
  rw [hrb]
  rcases hbcase with ⟨bc0, bfr, rfl, hbs, hbok, hbfd⟩ | ⟨er, er', rfl, hbs, herr⟩
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨er', ?_, herr⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error ((ipc_spec σ p.bv ssl y2.bv [] e2 []).trans (run_bind_error hbs _)) _
  simp only [bind_ok]
  have hip : (Fl4Spec.decodeSetIpcBuffer (Z := Unit) [y2.bv] (.threadCap p.bv) ssl [e2]).run σ =
      ({(.ok (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none none none (some (y2.bv, frameOf bfr))),
        σ)}, False) :=
    (ipc_spec σ p.bv ssl y2.bv [] e2 []).trans ((run_bind_ok hbs _).trans rfl)
  rw [run_bind_ok hip] at hspec
  obtain ⟨r, hr, hcase⟩ := roots_rel Z.th hP s σ Z.G hDS p hp y0 y1 e0 e1 he01 ⟨ps0, hps0, hps01⟩ he11
    ⟨ps1, hps1, hps11⟩ (hnc _ (by simp) e0.2 ⟨ps0, hps01, Or.inl hps0⟩ rfl) (hnc _ (by simp) e1.2 ⟨ps1, hps11, Or.inl hps1⟩ rfl) ssl
  rw [hr]
  rcases hcase with ⟨cc, vc, rfl, hcv, hokc, hokv⟩ | ⟨e, e', rfl, hcv, herr⟩
  · simp only [lift, bind_ok]
    rw [run_bind_ok hcv] at hspec
    obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartW arI hni hsg hP0 hct hHp (hR ct hct)
    rw [hrc]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeTcbConfigure (Z := Unit) ((y0 :: y1 :: y2 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
          [e0, e1, e2])).run σ =
        ({(.ok (tcInv p ssl (tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) (.Null, (0, [])) (.Null, (0, []))
          (cc, e0.2) (vc, e1.2) y2.bv bfr), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec]
      simp only [tcInv, optArg, flags_SB, ↓reduceIte]
      rfl
    have hT' := thread_control_capsJ arI (hHp.ins (L.ksb s1)) (hHp.del (L.ksb s1)) s1 ar σ1 Z.G hDS1 hW1 p hp ssl hAs
      (tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) (.Null, (0, [])) (.Null, (0, [])) (cc, e0.2) (vc, e1.2)
      (fun h => (Eq.mp flags_SB.1 h).elim) (fun h => (Eq.mp flags_SB.2.1 h).elim)
      (fun _ => hokc.of_same hS1) (fun _ => hokv.of_same hS1) (fun _ h => absurd rfl h) y2 y2.bv
      (fun _ => (hHp.ins (L.ksb s1)).buf p hp y2) bc0 bfr (fun c sl h => (hbok c sl h).of_same hS1) hbfd
      (fun _ _ _ => hfnz.of_same hS1)
    simp only [cslot_zero] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instJ arI (hHp.ins _).wjr (DecOut.of_eq hdec) hst1 h)
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨e', ?_, herr⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error hcv _

end

end

end Fl4Proofs.P3
