/-
P3 (DESIGN.md §9), CSpace: **the deletion loop's invariant with liveness at
`J`** (`WJL`), and the loop's slot edits keeping it.

* `WJL Z H Cs kb`: `WJR` (XTopJointDelR), `LiveJ` at the loop's MDB ghost,
  `DbgWF` (the debug lists well formed) and `NullOrig` (a null slot not
  original) — the entry fact `JEntryAt.live` carried through the loop, in
  place of the false-as-stated `LiveJHyp`.
* `RzJ H`: the slot fact the finalisation hands to the zombie write
  (DelW's `Rz`): a thread cap's TCB dead and off core 0's debug list.
* `LiveOther s σ G x`: the stronger readiness of the slot `x` to be emptied
  (lead decision (ii)): every slot in use but `x` named by a container cap
  other than `x`'s, every debug-listed thread by a thread cap other than
  `x`'s.
* `jZombieHypL`: a zombie written over a cap alike it keeps `WJL`
  (`ZombieHypWZ` at `WJL`, `RzJ`): `WJR` as `jZombieHyp` (copied at a dead set
  holding the TCB zombies' TCBs and the thread's, `JAtZ.addDeadSet`,
  `zombieJCoreD`), `LiveJ` (the zombie names what the cap names,
  `refsObj_of_alike`; a thread cap's TCB is off the debug list by `RzJ`; the
  zombie's slots from its count on unused: all of its object's when it
  replaces no zombie, else as before, the slot just deleted null and so not
  in use by `NullOrig`), `DbgWF` (`slotFrame_dbgKeep`), `NullOrig`
  (`NullOrig.setCap`).
-/
import Fl4Proofs.P3.XTopJointNullOrig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The spec's idle thread kept by an outcome of a `GK` step (SpecGlobFK:
every deletion step, `suspend`, `capInsert`, …). -/
theorem gk_idle {α : Type} {m : Fl4Spec.NonDet (Fl4Spec.State Unit) α} (h : Vs.GK m)
    {σ : Fl4Spec.State Unit} {x : α × Fl4Spec.State Unit} (hx : x ∈ (m σ).1) : x.2.idleThread = σ.idleThread :=
  congrArg Prod.snd (h σ x hx)

/-- A zombie alike a cap names the containers the cap names. -/
theorem refsObj_of_alike {p zt n q : U64} {c : capability.Cap} (hal : CapAlike (.Zombie p zt n) c)
    (hr : RefsObj q c) : RefsObj q (.Zombie p zt n) := by
  have h := hal.refs
  show p = q
  cases c <;> simp only [RefsObj] at hr <;> subst hr <;> simp only [absCap, Fl4Spec.objRefs] at h <;>
    exact P1.eq_of_bv (Set.singleton_eq_singleton_iff.1 h)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletion loop's invariant with liveness at `J`** (module docstring). -/
def WJL (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  WJR (L := L) arI AR Z H Cs kb s a σ G ∧ LiveJ (L := L) Z.th H G s σ ∧
    DbgWF (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s) ∧ NullOrig Z.th (L.mem s) σ

/-- **The finalisation's slot fact for the zombie write at `J`**: a thread
cap's TCB dead and off core 0's debug list. -/
abbrev RzJ (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s _ _ _ x => ∀ q, capV (L.mem s) x = .Thread q →
    DeadP (L := L) H s q ∧ ∀ n, dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ q

/-- **The stronger readiness of the slot `x` to be emptied** (module
docstring). -/
def LiveOther (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (x : U64) : Prop :=
  (∀ q i, IsSlotAt th q i → slotOf q i ≠ x → InUse (L.mem s) σ (slotOf q i) →
    (∃ y ∈ G.chains.flatten, y ≠ x ∧ RefsObj q (capV (L.mem s) y)) ∨ KsSlot (L.ksb s) (slotOf q i)) ∧
  (∀ n, dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ 0#u64 →
    (dbgNth (L.mem s) n (dbgHead (L := L) s)).bv ≠ σ.idleThread →
    ∃ y ∈ G.chains.flatten, y ≠ x ∧ capV (L.mem s) y = .Thread (dbgNth (L.mem s) n (dbgHead (L := L) s)))

variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **`jZombieHyp` keeping the dead set** (XTopJointDelR's proof, with
`zombieJCoreD`). -/
theorem JAtZ.zombieWD {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {V : XVs}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hns : Vs.NoSwitch σ) (hsg : SpecGlob σ)
    {sl : Fl4Spec.CslotPtr} {p zt n : U64}
    (hD1 : DState (L := L) Z.th s σ G) (hD2 : DState (L := L) Z.th s' σ' G) (hF : Vs.SlotFrame2 (L := L) Z.th s s')
    (hsc : Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ = ({((), σ')}, False)) (hA : AbsSlot Z.th sl)
    (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null) (hz : capV (L.mem s') (cslotAddr sl) = .Zombie p zt n)
    (hal : CapAlike (.Zombie p zt n) (capV (L.mem s) (cslotAddr sl)))
    (hoth : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y)
    (hmS : MdbStep (L.mem s) G (L.mem s') G) :
    ∃ V2 Ac' Lst', XTopAt (L := L) AR ((Z.mv G V).mv G (Z.mv G V).vs) s' a σ' ∧
      (∀ q ∈ D, DeadP (L := L) H s' q) ∧
      (LiveDN (L := L) Z.th H Cs G s' σ' → (∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D) →
        JAtZ (L := L) arI AR (Z.mv G V2) H Cs Ac' Lst' D s' a σ') ∧ L.ksb s' = L.ksb s ∧
      Vs.NoSwitch σ' ∧ SpecGlob σ' := by
  have hnk := Ipc.nkn_setCap _ _ σ ((), σ') (mem_of_single hsc)
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Z.mv G V) (L.ksb s) s s' a σ σ' G G
    ⟨⟨V, J.xtop⟩, J.ks, J.thT, rfl⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hfk2, hC, Ac', Lst', R⟩ := J.zombieJCoreD hA hxn hal hsc hD2 hz hoth hX2
    (SlotFrame2.writesIn hF) hnk
  have hsg2 : SpecGlob σ' := by
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hD1.1.1.abs_cap hA
    rw [hca0.abs] at hg0
    have ha0 : capOpt (σ.kheap sl.1) sl.2 = some (absCap c0) :=
      (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
    have hcv0 := capV_of_capAt hc0
    rw [hcv0] at hal hxn
    have hfr : isFrame c0 = false := by rw [← hal.frame]; rfl
    refine SpecGlob.setCap (mem_of_single hsc) hsg ha0 hal.refs (by simp [IsPageCap, absCap])
      (absCap_notPage hfr) ?_
    intro irq e
    rw [e] at ha0
    rcases hsg.irq irq _ ha0 with h0 | ⟨q, b, rs, h0⟩
    · exact hxn (absCap_eq_null.1 h0)
    · obtain ⟨q', b', w', r', rfl⟩ : ∃ q' b' w' r', c0 = .Notification q' b' w' r' := by
        cases c0 <;> simp [absCap] at h0
        exact ⟨_, _, _, _, rfl⟩
      have hr := hal.refs
      simp only [absCap, Fl4Spec.objRefs] at hr
      have hpq : p = q' := P1.eq_of_bv (Set.singleton_eq_singleton_iff.1 hr)
      subst hpq
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b' w' r' hcv0).2
      rcases hD2.2.1.zwf _ hA.isSlot p zt n hz with ⟨-, ht, -⟩ | ⟨-, hc, -⟩
      · have := J.zH.1 p (J.thT p ht); rw [hHp] at this; cases this
      · have := hJ.cnode p _ hc; rw [hHp] at this; cases this
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') :=
    Vs.VsSlotsT.of_some (· = cslotAddr sl) (fun y hy hn => hoth y hy hn)
      (fun y _ e _ _ _ _ _ _ => by rw [e, hz]; trivial) (fun y _ e _ _ => by rw [e, hz]; trivial) fun y _ e _ => by rw [e, hz]; trivial
  exact ⟨V, Ac', Lst', J.xtop.vs_backC hX2 (SlotFrame2.writesIn hF) hnk, fun q hq => R.jcov.dead q hq,
    fun hlv hzD => J.cs_frameB hks (J.xtop.vs_backC hX2 (SlotFrame2.writesIn hF) hnk) hkb2 (J.bfK hfk2 hvT) hC R
    (J.vsc.step hvT) (J.ext.step hvT (J.vkeep_slot ((SlotFrame2.writesIn hF).mono fun b hb => slotWd_range J.xtop.rel.1 hb)))
    hlv hzD, hks, (ak_setCap' _ _).noSwitch (mem_of_single hsc) hns, hsg2⟩

set_option maxHeartbeats 4000000 in
/-- **A zombie written over a cap alike it keeps `WJL`** (module docstring). -/
theorem jZombieHypL (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    ZombieHypWZ (L := L) (A := A) (WJL (L := L) arI AR Z H Cs kb) (RzJ (L := L) (A := A) H) th := by
  intro s s' a σ σ' G sl p zt n hW hRz0 hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS
  subst hth
  have hRz : ∀ q, capV (L.mem s) (cslotAddr sl) = .Thread q →
      DeadP (L := L) H s q ∧ ∀ k, dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ q := fun q h => hRz0 q h q h
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ := hW
  have hP := J.xtop.rel.1
  have hxs := hA.isSlot
  -- the dead set: the TCB zombies' TCBs and the thread's
  set E : Set U64 := ZTcb (L := L) Z.th s ∪ {q | capV (L.mem s) (cslotAddr sl) = .Thread q} with hE
  have J0 := J.addDeadSet (E := E) (fun q hq => hq.elim (hL.ztcb q) (fun h => (hRz q h).1))
  obtain ⟨V2, Ac', Lst', hXb, hdead0, mk, hks, hns', hsg'⟩ :=
    J0.zombieWD arI hns hsg hD1 hD2 hF hsc hA hxn hz hal hoth hmS
  have hdead : ∀ q ∈ E, DeadP (L := L) H s' q := fun q hq => hdead0 q (Or.inr hq)
  have hpp : PPR0 σ' := hp0.of_ppk (PPK.of_cnK (Ipc.nkn_setCap _ _ σ ((), σ') (mem_of_single hsc)))
  have hdk := J.slotFrame_dbgKeep hF
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hc0 : 0#u64 ∈ Cs := J.kern.cs0
  have ho : σ'.isOriginalCap = σ.isOriginalCap :=
    funext fun sl' => no_setCap (d := fun _ => False) _ sl σ ((), σ') (by rw [hsc]; rfl) sl' id
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hD1.1.2.2.1.members y).1 hy).1
  have hzn : capV (L.mem s') (cslotAddr sl) ≠ .Null := by rw [hz]; simp
  have hU : ∀ y, IsSlot Z.th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    by_cases e : y = cslotAddr sl
    · subst e; exact Or.inl hxn
    · unfold InUse at hu ⊢
      rw [hoth y hy e, ho] at hu
      exact hu
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hdk.1]
    exact hdk.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hNt : ∀ k, dbgNth (L.mem s') k (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) :=
    fun k => by
      rw [hhd]
      exact dbgNth_keep (fun y hy => hdk.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) k _
        (hTz.dh _ hc0)
  have hzE : ∀ p' ∈ ZTcb (L := L) Z.th s', p' ∈ E := by
    rintro p' ⟨y, hy, zt', n', hz', hzt⟩
    by_cases e : y = cslotAddr sl
    · subst e
      rw [hz] at hz'; injection hz' with e1 e2 e3; subst p' zt' n'
      cases hzb : isZb (capV (L.mem s) (cslotAddr sl))
      · rcases (hZF hzb).2 with ⟨q, hq⟩ | ⟨q, r, gs, g, hq⟩
        · have e1 : p = q := refsObj_of_alike hal (q := q) (by rw [hq]; rfl)
          subst e1
          exact Or.inr hq
        · have e1 : p = q := refsObj_of_alike hal (q := q) (by rw [hq]; rfl)
          subst e1
          exfalso
          have hcv : CapValid Z.th (capV (L.mem s) (cslotAddr sl)) :=
            J.xtop.rel.2.1.2.1.abs hA (capAt_capV _ _)
          rw [hq] at hcv
          rcases hD2.2.1.zwf _ hxs _ _ _ hz with ⟨-, ht, -⟩ | ⟨h65, -, -⟩
          · have h1 := hcv.1; rw [ht] at h1; cases h1
          · exact h65 hzt
      · obtain ⟨p1, zt1, n1, hc1⟩ : ∃ p1 zt1 n1, capV (L.mem s) (cslotAddr sl) = .Zombie p1 zt1 n1 := by
          generalize capV (L.mem s) (cslotAddr sl) = c at hzb ⊢
          cases c <;> simp [isZb] at hzb
          exact ⟨_, _, _, rfl⟩
        obtain ⟨e1, e2, -⟩ := hcd p1 zt1 n1 hc1; subst p1 zt1
        exact Or.inl ⟨_, hxs, _, _, hc1, hzt⟩
    · exact Or.inl ⟨y, hy, zt', n', by rw [← hoth y hy e]; exact hz', hzt⟩
  have hL' : LiveJ (L := L) Z.th H G s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p' zt' n' hz' i hpi hni hu => ?_,
      fun y hy p' zt' n' hz' hzt => ?_⟩
    · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu) with ⟨y, hy, hr⟩ | hb
      rotate_left
      · exact Or.inr (by rw [hdk.1]; exact hb)
      refine Or.inl ⟨y, hy, ?_⟩
      by_cases e : y = cslotAddr sl
      · subst e; rw [hz]; exact refsObj_of_alike hal hr
      · rw [hoth y (hmem y hy) e]; exact hr
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← gk_idle (Vs.gk_setCap _ _) (mem_of_single hsc)]; exact hki)
      refine ⟨y, hy, ?_⟩
      by_cases e : y = cslotAddr sl
      · subst e; exact absurd rfl ((hRz _ hr).2 k)
      · rw [hoth y (hmem y hy) e]; exact hr
    · by_cases e : y = cslotAddr sl
      · subst e
        rw [hz] at hz'; injection hz' with e1 e2 e3; subst p' zt' n'
        cases hzb : isZb (capV (L.mem s) (cslotAddr sl))
        · exact absurd ((hZF hzb).1 i hpi) (by omega)
        · obtain ⟨p1, zt1, n1, hc1⟩ : ∃ p1 zt1 n1, capV (L.mem s) (cslotAddr sl) = .Zombie p1 zt1 n1 := by
            generalize capV (L.mem s) (cslotAddr sl) = c at hzb ⊢
            cases c <;> simp [isZb] at hzb
            exact ⟨_, _, _, rfl⟩
          obtain ⟨e1, e2, hcase⟩ := hcd p1 zt1 n1 hc1; subst p1 zt1
          by_cases hle : n1.val ≤ i
          · exact hL.zslots _ hxs _ _ _ hc1 i hpi hle (hU _ ⟨p, i, hpi, rfl⟩ hu)
          · rcases hcase with h | ⟨h1, hnull⟩
            · omega
            · have hi : i = n.val := by omega
              subst hi
              have hz1 := J.del.zwf _ hxs _ _ _ hc1
              obtain ⟨hEa, hEaddr⟩ := zSlot_abs hP hz1 (show n.val < n1.val by omega)
              have hsa : cslotAddr (zSlot p zt n.val) = slotOf p n.val := hEaddr
              have hne : slotOf p n.val ≠ cslotAddr sl := fun e' => by
                rw [← hsa] at e'; rw [e'] at hnull; exact hxn hnull
              apply hN.notInUse J.kern.orig (y := slotOf p n.val) (by rw [← hsa]; exact hnull)
              unfold InUse at hu ⊢
              rw [hoth _ ⟨p, n.val, hpi, rfl⟩ hne, ho] at hu
              exact hu
      · exact hL.zslots y hy p' zt' n' (by rw [← hoth y hy e]; exact hz') i hpi hni (hU _ ⟨p', i, hpi, rfl⟩ hu)
    · exact hdead p' (hzE p' ⟨y, hy, zt', n', hz', hzt⟩)
  have hDW' := dbgWFL_step J.xtop hXb rfl rfl J.tcbs_eq.1 hDW hdk
  have hN' := hN.setCap hP hA hsc hzn hoth
  have J' := mk ⟨hL', ⟨lst, hDW'⟩, hN'⟩ (fun p' hp' => Or.inr (hzE p' hp'))
  exact ⟨⟨V2, Ac', Lst', D ∪ E, J', hks.trans hkb, hns', hsg', hpp⟩, hL', ⟨lst, hDW'⟩, hN'⟩

end

end

end Fl4Proofs.P3
