/-
P3 (DESIGN.md §9), CSpace: **an insert into an empty TCB slot keeps
`LiveDN`** (XTopJointWJLRestart's `LiveJ ∧ DbgWF ∧ NullOrig`), for the TCB
cap installs at `WJL` (XTopJointTcbInstall's `install_tcb_capJ`,
`install_bufferJ`; l4v `cap_insert` keeps `if_unsafe_then_cap`,
`if_live_then_nonz_cap`, `zombies_final` and `valid_nullcaps`).

* `LiveDN.insT`: `cdt::insert` of a cap alike an existing one (its shape)
  into the empty slot `n` of a TCB `t` that a thread cap names:
  - the new cap is no zombie: a zombie's shape is itself, so its source
    would hold the same zombie, against `zombies_final` after
    (`FinInv.zombie_alone`);
  - `slots`: the new slot's container `t` is named by the thread cap (kept,
    and in the MDB after); a slot in use after but that one was in use
    before (the caps and original bits elsewhere kept, `capInsert_orig`),
    its naming cap kept;
  - `dbg`: the debug words kept (the insert writes slot words only,
    `JAtZ.inSlot_notDbg`), the thread caps kept;
  - `zslots`: a zombie after is one before; the new slot is no zombie's slot
    from its count on: a zombie to `t` would name `t`, which the thread cap
    names too (`FinInv.zombie_alone`);
  - `zdead`: the dead stay dead (`JAtZ.deadP_slot`);
  - `DbgWF` by `JAtZ.dbgWF_keep`; `NullOrig`: the new slot is not null, the
    other slots' caps and bits kept.
-/
import Fl4Proofs.P3.XTopJointWJLRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- **An insert into an empty TCB slot keeps `LiveDN`** (module docstring). -/
theorem LiveDN.insT {G : MdbGhost} {V : XVs} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ)
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
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
    rw [nodeAt_of_ksb hdk.1]
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
      exact J.deadP_slot J'.xtop hcn hkc hw (hL.zdead y hy p zt k hz0 hzt')
  refine ⟨hL', ⟨lst, J.dbgWF_keep J' rfl rfl hDW hdk⟩, fun sl hA h => ?_⟩
  have hsx : cslotAddr sl ≠ x := fun e => hnn (by rw [← e]; exact h)
  have hne : sl ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hsx (by rw [e])
  rw [horig sl hne]
  exact hN sl hA (by rw [← hcap _ hA.isSlot hsx]; exact h)

end

end

end Fl4Proofs.P3
