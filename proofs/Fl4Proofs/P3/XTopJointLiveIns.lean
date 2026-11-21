/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2f (b)): **an insert into an empty
slot whose container a CNode or thread cap names keeps `LiveDN`**, for the
IPC cap grant's insert into the receiver's CNode receive slot (XTopJointGrant's
`JAtZ.insDJ`; l4v `cap_insert` keeps `if_unsafe_then_cap`,
`if_live_then_nonz_cap`, `zombies_final` and `valid_nullcaps`).

* `CapSimL c' c`: equal, or untyped caps of the same region and device bit
  (the source of `cdt::insert` may have its free index set: Insert's
  `fullF`); such caps agree on null-ness, `RefsObj`, thread caps and zombies
  (`CapSimL.null` / `refs` / `thread` / `zombie`); `capSimL_fullF`.
* `refsObj_objRefs`: a cap naming a container names it as an object
  (`objRefs`), so no zombie names a container a non-zombie cap names
  (`FinInv.zombie_alone`).
* `LiveDN.insG`: XTopJointWJLIns's `LiveDN.insT` for any slot `sl` (slot `i`
  of a container `q`) whose container a non-zombie cap of a slot names
  (`RefsObj`), with every other slot's cap kept up to `CapSimL` (the source
  slot's free index); the new cap no zombie.
* `LiveDN.insC`: the instance at `insDJ`'s post for a destination CNode
  `pd` named by a CNode cap of a slot (`DestLive`'s left disjunct): the
  source's cap `(fullF srcC cc).getD srcC`, every other slot's kept, the new
  cap `cc` no zombie (`isZb cc = isZb srcC = false` by the shape).
-/
import Fl4Proofs.P3.XTopJointWJLIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- **An insert into an empty slot of a named container keeps `LiveDN`**
(module docstring). -/
theorem LiveDN.insG {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ Z.G)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
    {q : U64} {i : Nat} (hqi : IsSlotAt Z.th q i) {sl : Fl4Spec.CslotPtr} (hAd : AbsSlot Z.th sl)
    (hxe : cslotAddr sl = slotOf q i) {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr}
    (hci : Fl4Spec.capInsert (Z := Unit) c src sl σ = ({((), σ')}, False))
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hnull : capV (L.mem s) (cslotAddr sl) = .Null)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → CapSimL (capV (L.mem s') y) (capV (L.mem s) y))
    (hnn : capV (L.mem s') (cslotAddr sl) ≠ .Null)
    (hnz : ∀ p zt k, capV (L.mem s') (cslotAddr sl) ≠ .Zombie p zt k)
    (hlive : ∃ y, IsSlot Z.th y ∧ RefsObj q (capV (L.mem s) y) ∧ isZb (capV (L.mem s) y) = false) :
    LiveDN (L := L) Z.th H Cs G' s' σ' := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hP : Placed Z.th := J.xtop.rel.1
  set x := cslotAddr sl with hx
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c src sl σ).1 := by rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hkc : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hw : P1.WritesIn st s s' (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  have horig : ∀ sl', sl' ≠ sl → σ'.isOriginalCap sl' = σ.isOriginalCap sl' :=
    fun sl' e => capInsert_orig c _ _ σ ((), σ') hmem sl' e
  have hM := hDS.1.2.2.1
  have hM' := hDS'.1.2.2.1
  -- a non-null cap before, away from `x`: in the MDB after, alike
  have hkeep : ∀ y, IsSlot Z.th y → capV (L.mem s) y ≠ .Null →
      y ∈ G'.chains.flatten ∧ CapSimL (capV (L.mem s') y) (capV (L.mem s) y) := fun y hy h => by
    have hyx : y ≠ x := fun e => h (by rw [e, hnull])
    have e := hcap y hy hyx
    exact ⟨(hM'.members y).2 ⟨hy, _, capAt_capV _ _, fun h0 => h ((e.null).1 h0)⟩, e⟩
  have hmemS : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ Z.G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  -- the cap naming `q`
  obtain ⟨yT, hyT, hRT, hzT⟩ := hlive
  have hyTn : capV (L.mem s) yT ≠ .Null := fun h0 => by rw [h0] at hRT; exact hRT
  obtain ⟨hyTG, hyTc⟩ := hkeep yT hyT hyTn
  -- a slot in use after, away from `x`, was in use before
  have hU : ∀ y, IsSlot Z.th y → y ≠ x → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hyx hu => by
    unfold InUse at hu ⊢
    rcases hu with hu | ⟨x', hx', ho⟩
    · exact Or.inl fun h0 => hu (((hcap y hy hyx).null).2 h0)
    · refine Or.inr ⟨x', hx', ?_⟩
      have hne : x' ≠ sl := fun e => hyx (by rw [← hx', e])
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
  -- no zombie names `q`
  have hzt : ∀ y, IsSlot Z.th y → ∀ zt k, capV (L.mem s) y ≠ .Zombie q zt k := fun y hy zt k hz => by
    have hne : yT ≠ y := fun e => by rw [e, hz] at hzT; cases hzT
    exact FinInv.zombie_alone hDS.2.2 hM hy hz yT hyT hne (refsObj_objRefs hRT)
  have hL' : LiveJ (L := L) Z.th H G' s' σ' := by
    refine ⟨fun q' i' hqi' hu => ?_, fun k hk hki => ?_, fun y hy p zt k hz i' hpi hki hu => ?_,
      fun y hy p zt k hz hzt' => ?_⟩
    · by_cases hqx : slotOf q' i' = x
      · obtain ⟨rfl, -⟩ := slotOf_inj hP hqi' hqi (hqx.trans hxe)
        exact Or.inl ⟨yT, hyTG, (hyTc.refs q').2 hRT⟩
      · rcases hL.slots q' i' hqi' (hU _ ⟨q', i', hqi', rfl⟩ hqx hu) with ⟨y, hy, hr⟩ | hb
        · obtain ⟨hyG, hyc⟩ := hkeep y (hmemS y hy) (hmemN y hy)
          exact Or.inl ⟨y, hyG, (hyc.refs q').2 hr⟩
        · exact Or.inr (by rw [hdk.1]; exact hb)
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hcn.idle]; exact hki)
      obtain ⟨hyG, hyc⟩ := hkeep y (hmemS y hy) (hmemN y hy)
      exact ⟨y, hyG, (hyc.thread _).2 hr⟩
    · have hyx : y ≠ x := fun e => hnz p zt k (by rw [← e]; exact hz)
      have hz0 : capV (L.mem s) y = .Zombie p zt k := ((hcap y hy hyx).zombie p zt k).1 hz
      by_cases hpx : slotOf p i' = x
      · obtain ⟨rfl, -⟩ := slotOf_inj hP hpi hqi (hpx.trans hxe)
        exact hzt y hy zt k hz0
      · exact hL.zslots y hy p zt k hz0 i' hpi hki (hU _ ⟨p, i', hpi, rfl⟩ hpx hu)
    · have hyx : y ≠ x := fun e => hnz p zt k (by rw [← e]; exact hz)
      have hz0 : capV (L.mem s) y = .Zombie p zt k := ((hcap y hy hyx).zombie p zt k).1 hz
      exact J.deadP_slot J'.xtop hcn hkc hw (hL.zdead y hy p zt k hz0 hzt')
  refine ⟨hL', ⟨lst, J.dbgWF_keep J' rfl rfl hDW hdk⟩, fun sl' hA h => ?_⟩
  have hsx : cslotAddr sl' ≠ x := fun e => hnn (by rw [← e]; exact h)
  have hne : sl' ≠ sl := fun e => hsx (by rw [e])
  rw [horig sl' hne]
  exact hN sl' hA (((hcap _ hA.isSlot hsx).null).1 h)

/-- **`LiveDN` across a `JAtZ` step keeping the slots** (KENTRY-PLAN g2f (d)/(e),
the generic frame): the slots (`SlotsSame`), the debug words (`DbgKeep`), the
original bits and the spec's idle thread kept, and the TCB zombies' TCBs in the
after state's dead set (start the step from `J.addDeadSet hL.1.ztcb`, so its own
dead-set carry gives them); the affinities by `JAtZ.dbgWF_keep`. Unlike
XTopJointKEntry33's `LiveDN.of_keep`, no per-word frame of the TCBs. -/
theorem LiveDN.of_jstep {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {Z' : XSets} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ')
    (hZT : Z'.T = Z.T) (hZc : Z'.c = Z.c) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hid : σ'.idleThread = σ.idleThread) (hD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    LiveDN (L := L) Z.th H Cs Z.G s' σ' := by
  obtain ⟨hLJ, ⟨lst, hDW⟩, hN⟩ := hL
  have hmem : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
    ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  exact ⟨hLJ.of_sameZ hSS hmem horig hid hK J.kern.cs0 hTz fun p hp => J'.jcov.dead p (hD p hp),
    ⟨lst, J.dbgWF_keep J' hZT hZc hDW hK⟩, hN.of_same (fun y hy => hSS.capV hy) horig⟩

set_option maxHeartbeats 4000000 in
/-- **The cap grant's insert into a CNode receive slot keeps `LiveDN`**
(module docstring): the facts of XTopJointGrant's `JAtZ.insDJ` post, the
destination CNode named by a CNode cap (`DestLive`'s left disjunct). -/
theorem LiveDN.insC {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ Z.G)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
    {ps pd : U64} {rd : Nat} (hpd : Z.th pd = some (.cnode rd)) {idxs idxd : List Bool} (hld : idxd.length = rd)
    {ac : Fl4Spec.Cap}
    (hci : Fl4Spec.capInsert (Z := Unit) ac (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False))
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    {srcC cc : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (hoth : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (ps.bv, idxs) → y ≠ cslotAddr (pd.bv, idxd) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hdc : capV (L.mem s') (cslotAddr (pd.bv, idxd)) = cc)
    (hsc : capV (L.mem s') (cslotAddr (ps.bv, idxs)) = (fullF srcC cc).getD srcC)
    (hcnn : cc ≠ .Null) (hzb : isZb cc = false)
    (hDd : ∃ y r gs g, IsSlot Z.th y ∧ capV (L.mem s) y = .CNode pd r gs g) :
    LiveDN (L := L) Z.th H Cs G' s' σ' := by
  have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  obtain ⟨p, i, hpi, h1, hxe⟩ := hAd.at
  have hp : p = pd := P1.eq_of_bv h1.symm
  subst hp
  have hnull : capV (L.mem s) (cslotAddr (p.bv, idxd)) = .Null := capV_of_capAt hdst
  obtain ⟨y, r, gs, g, hy, hyc⟩ := hDd
  refine LiveDN.insG J hDS hLv J' hDS' hpi hAd hxe hci hwS hnull (fun y hy hyx => ?_) (by rw [hdc]; exact hcnn)
    (fun p' zt k h => by rw [hdc] at h; subst h; simp [isZb] at hzb) ⟨y, hy, by rw [hyc]; rfl, by rw [hyc]; rfl⟩
  by_cases hys : y = cslotAddr (ps.bv, idxs)
  · subst hys
    rw [hsc, capV_of_capAt hsrcC]
    exact capSimL_fullF srcC cc
  · exact Or.inl (hoth y hy hys hyx)

end

end

end Fl4Proofs.P3
