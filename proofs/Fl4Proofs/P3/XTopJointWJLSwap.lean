/-
P3 (DESIGN.md §9), CSpace: **the deletion loop's zombie swap keeps `WJL`**
(`SwapHypWZ` at `WJL`, XTopJointWJL).

* `WJR` as `jSwapHyp` (XTopJointDelR), at a dead set holding the TCB
  zombies' TCBs (`JAtZ.addDeadSet`, `swapJCoreD` keeping it), `PPR0` by
  `PPK.of_cnK`.
* `LiveJ`: the slots' caps and original bits are swapped (`capV` after at
  `y` is `capV` before at `swap y`, `capSwapForDelete_orig_val/_oth`), the
  ghost tree renamed by the same swap (`mem_renG`), so a slot in use after is
  in use before, or it is the zombie's first slot `p` (`= slotOf p 0`), which
  the zombie now there names. A zombie after is one before (at the swapped
  slot): its slots from its count on unused as before, or the slot is `p`
  itself, which only a zombie of count `0` to `p` could leave unused — not
  the moved zombie (count `≥ 1`) and no other (`DelInv.zu`). TCB zombies'
  TCBs dead by the dead set.
* `DbgWF` (`slotFrame_dbgKeep`), `NullOrig` (`NullOrig.swap`).
-/
import Fl4Proofs.P3.XTopJointWJL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **A zombie swapped with its first slot keeps `WJL`** (module docstring). -/
theorem jSwapHypL (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    SwapHypWZ (L := L) (A := A) (WJL (L := L) arI AR Z H Cs kb) th := by
  intro s s' a σ σ' G G' sl p zt n hW hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS
  subst hth hG'
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ := hW
  have hP := J.xtop.rel.1
  have hxs := hA.isSlot
  have hnk := capSwapForDelete_nkn _ _ σ ((), σ') (mem_of_single hsw)
  have hzok : ZOK Z.th p zt n := J.del.zwf _ hA.isSlot p zt n hz
  -- the dead set: the TCB zombies' TCBs
  set E : Set U64 := ZTcb (L := L) Z.th s with hE
  have J0 := J.addDeadSet (E := E) hL.ztcb
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Z.mv G V) kb s s' a σ σ' G _
    ⟨⟨V, J0.xtop⟩, J0.ks, J0.thT, hkb⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hfk2, hC, Ac', Lst', R⟩ := J0.swapJCoreD hA hz hpx hsw hD2 hcap hX2
    (SlotFrame2.writesIn hF) hnk
  have hsg2 : SpecGlob σ' := by
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hD1.1.1.abs_cap hA
    rw [hca0.abs] at hg0
    have hcv0 := capV_of_capAt hc0
    rw [hz] at hcv0
    subst hcv0
    obtain ⟨c1, ac1, hc1, hca1, hg1⟩ := hD1.1.1.abs_cap (home_abs hzok)
    rw [hca1.abs] at hg1
    have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
    refine SpecGlob.swap (mem_of_single hsw) hsg hg1 hg0 (fun irq e => ?_) (fun irq e => ?_)
    · have e1 : p.bv = σ.interruptIrqNode irq := congrArg Prod.fst e
      apply hsg.ref sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap]) irq
      rw [← e1]; simp [absCap, Fl4Spec.objRefs]
    · rw [e] at ha0
      rcases hsg.irq irq _ ha0 with h | ⟨_, _, _, h⟩ <;> simp [absCap] at h
  have hpS : IsSlot Z.th p := by
    have h := (home_abs hzok).isSlot
    rwa [home_addr] at h
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') := by
    refine ⟨fun P L4 L3 L2 L1 h y hy => ?_, fun U h y hy => ?_, fun h y hy => ?_⟩ <;>
    · rw [hcap y hy]
      split_ifs
      · exact h p hpS
      · exact h _ hA.isSlot
      · exact h y hy
  have hpp : PPR0 σ' := hp0.of_ppk (PPK.of_cnK hnk)
  -- the swap of the slots
  set x := cslotAddr sl with hx
  set e : U64 ≃ U64 := Equiv.swap p x with he
  have hcap' : ∀ y, IsSlot Z.th y → capV (L.mem s') y = capV (L.mem s) (e y) := fun y hy => by
    rw [hcap y hy, he]
    by_cases h1 : y = x
    · subst h1; rw [if_pos rfl, Equiv.swap_apply_right]
    · rw [if_neg h1]
      by_cases h2 : y = p
      · subst h2; rw [if_pos rfl, Equiv.swap_apply_left]
      · rw [if_neg h2, Equiv.swap_apply_of_ne_of_ne h2 h1]
  have heS : ∀ y, IsSlot Z.th y → IsSlot Z.th (e y) := fun y hy => by
    rw [he]
    by_cases h1 : y = x
    · subst h1; rw [Equiv.swap_apply_right]; exact hpS
    · by_cases h2 : y = p
      · subst h2; rw [Equiv.swap_apply_left]; exact hxs
      · rw [Equiv.swap_apply_of_ne_of_ne h2 h1]; exact hy
  have hee : ∀ y, e (e y) = y := fun y => Equiv.swap_apply_self _ _ _
  have hsw_cap : ∀ y, IsSlot Z.th y → capV (L.mem s') (e y) = capV (L.mem s) y := fun y hy => by
    rw [hcap' _ (heS y hy), hee]
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hD1.1.2.2.1.members y).1 hy).1
  have hmemG : ∀ y ∈ G.chains.flatten, e y ∈ (renG G e).chains.flatten := fun y hy => by
    rw [mem_renG]
    have : e.symm (e y) = y := Equiv.symm_apply_apply e y
    rw [this]; exact hy
  have hmd : ∀ y, IsSlot Z.th y → capV (L.mem s') y ≠ .Null → y ∈ (renG G e).chains.flatten := fun y hy h =>
    (hD2.1.2.2.1.members y).2 ⟨hy, _, capAt_capV _ _, h⟩
  have hmw : ((), σ') ∈ (Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ).1 := by rw [hsw]; rfl
  have hHa : cslotAddr (homeSl p zt) = p := home_addr p _
  have hxn : capV (L.mem s) x ≠ .Null := by rw [hz]; simp
  have hU : ∀ y, IsSlot Z.th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y ∨ y = p := fun y hy hu => by
    by_cases h1 : y = x
    · subst h1; exact Or.inl (Or.inl hxn)
    by_cases h2 : y = p
    · exact Or.inr h2
    left
    unfold InUse at hu ⊢
    rw [hcap' y hy, he, Equiv.swap_apply_of_ne_of_ne h2 h1] at hu
    rcases hu with hu | ⟨y', hy', ho⟩
    · exact Or.inl hu
    · refine Or.inr ⟨y', hy', ?_⟩
      have n1 : y' ≠ homeSl p zt := fun e' => h2 (by rw [← hy', e', hHa])
      have n2 : y' ≠ sl := fun e' => h1 (by rw [← hy', e'])
      rw [← capSwapForDelete_orig_oth hmw n1 n2]; exact ho
  -- the first slot `p` is `p`'s slot `0`
  have hp0S : IsSlotAt Z.th p 0 := by
    rcases hzok with ⟨-, ht, -⟩ | ⟨-, hc', -⟩
    · exact Or.inr ⟨ht, by decide⟩
    · exact Or.inl ⟨_, hc', by positivity⟩
  have hp0e : slotOf p 0 = p := by show (⟨p.bv + BitVec.ofNat 64 0 * 32#64⟩ : U64) = p; simp
  have hatp : ∀ q i, IsSlotAt Z.th q i → slotOf q i = p → q = p ∧ i = 0 := fun q i hqi h =>
    slotOf_inj hP hqi hp0S (h.trans hp0e.symm)
  have hzp : capV (L.mem s') p = .Zombie p zt n := by
    rw [hcap' p hpS, he, Equiv.swap_apply_left]; exact hz
  -- the debug words
  have hdk := J.slotFrame_dbgKeep hF
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
  have hL' : LiveJ (L := L) Z.th H (renG G e) s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p' zt' n' hz' i hpi hni hu => ?_,
      fun y hy p' zt' n' hz' hzt => ?_⟩
    · rcases hU _ ⟨q, i, hqi, rfl⟩ hu with hu | hu
      · rcases hL.slots q i hqi hu with ⟨y, hy, hr⟩ | hb
        · exact Or.inl ⟨e y, hmemG y hy, by rw [hsw_cap y (hmem y hy)]; exact hr⟩
        · exact Or.inr (by rw [hdk.1]; exact hb)
      · obtain ⟨rfl, -⟩ := hatp q i hqi hu
        exact Or.inl ⟨q, hmd q hpS (by rw [hzp]; simp), by rw [hzp]; rfl⟩
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hnk.idle]; exact hki)
      exact ⟨e y, hmemG y hy, by rw [hsw_cap y (hmem y hy)]; exact hr⟩
    · have hw : capV (L.mem s) (e y) = .Zombie p' zt' n' := by rw [← hcap' y hy]; exact hz'
      rcases hU _ ⟨p', i, hpi, rfl⟩ hu with hu | hu
      · exact hL.zslots (e y) (heS y hy) p' zt' n' hw i hpi hni hu
      · obtain ⟨rfl, rfl⟩ := hatp p' i hpi hu
        have hn0 : n'.val = 0 := by omega
        by_cases hey : e y = x
        · rw [hey, hz] at hw
          injection hw with _ _ e3
          subst e3; omega
        · exact J.del.zu (e y) x (heS y hy) hxs hey p' zt' n' p' zt n hw hz rfl
    · have hw : capV (L.mem s) (e y) = .Zombie p' zt' n' := by rw [← hcap' y hy]; exact hz'
      exact R.jcov.dead p' (Or.inr ⟨e y, heS y hy, zt', n', hw, hzt⟩)
  have hDW' := dbgWFL_step J.xtop hX2 rfl rfl J.tcbs_eq.1 hDW hdk
  have hN' := hN.swap hP hA hzok hsw hz hpx hcap
  have hZf : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D ∪ E := fun p ⟨y, hy, zt', n', hz', hzt⟩ => by
    have hw : capV (L.mem s) (e y) = .Zombie p zt' n' := by rw [← hcap' y hy]; exact hz'
    exact Or.inr ⟨e y, heS y hy, zt', n', hw, hzt⟩
  have J' := J0.cs_frameB hks (J0.xtop.vs_backC hX2 (SlotFrame2.writesIn hF) hnk) hkb2 (J0.bfK hfk2 hvT) hC R (J0.vsc.step hvT) (J0.ext.step hvT (J0.vkeep_slot ((SlotFrame2.writesIn hF).mono fun b hb => slotWd_range J0.xtop.rel.1 hb)))
    ⟨hL', ⟨lst, hDW'⟩, hN'⟩ hZf
  exact ⟨⟨V, Ac', Lst', D ∪ E, J', hks.trans hkb, (ak_capSwapForDelete' _ _).noSwitch (mem_of_single hsw) hns,
    hsg2, hpp⟩, hL', ⟨lst, hDW'⟩, hN'⟩

end

end

end Fl4Proofs.P3
