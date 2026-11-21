/-
P3 (DESIGN.md §9), scheduler: **the entry tail's frame on `JAtZ`** (stage 3c,
`jat_schedule`'s `hSchedRest` discharged down to the facts of the state
after FL4's `schedule`, `SchTailHyps`):

* `JAtZ.sch_kern`: `JKern` across a scheduler step, the current thread
  word FL4's new one (`SchedRel` after: in `T`, so typed and in `H`).
* `JAtZ.sch_tail`: `JAtZ` after `schedule` from `JAtZ` at the state after
  the TCB timers (`Fires`): `XTop` by `xtop_sched_step`, the call stack,
  yield and MCP words by `ScAll.of_k` (FL4's `KFoot` writes, l4v's
  `schedule` a `SchS` step), the placement facts by the `sch_*` lemmas,
  `CurOwnW` from `CurInv`, `CurRunW` from `schedule_refinesWP`'s new
  thread (`RunW.scAndTimer`), `OffOK` (`OffOK.scAndTimer`), `BlockedScActive`
  (`bsa_schedule`); the rest (`SchTailHyps`) given.
* `jat_scheduleT`: `jat_schedule` with `hSchedRest` replaced by `JAtZ`
  after the timers (`hfireJ`) and `SchTailHyps` after `schedule`.
-/
import Fl4Proofs.P3.ScJointSchFrame
import Fl4Proofs.P3.ScJointStep
import Fl4Proofs.P3.ScJointSched
import Fl4Proofs.P3.ScSchedSpec
import Fl4Proofs.P3.ScSchedRun
import Fl4Proofs.P3.ScSchedIdle
import Fl4Proofs.P3.ScSchedOff
import Fl4Proofs.P3.ScSchedBsa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`JKern` across a scheduler step** (module docstring): the current SC
word's heap object (`hcscH`), the node-0
`DEBUG_TCBS` word kept and apart from the new thread's state word (`hDbg`,
`hdw`) given. -/
theorem JAtZ.sch_kern {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hdw : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val)
    (hcscH : H (L.cscW s') ≠ none) : JKern (L := L) H Cs D Z.th s' σ' := by
  have K := J.kern
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have ecw : L.curW s' = nodeW st s' Z.c layout.node.CUR_THREAD := by
    unfold P1.LawfulStore.curW nodeW; rw [hc'.cur]
  have hcT : L.curW s' ∈ Z.T := ecw ▸ hc'.curT
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  have hT := hK.toTK
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => K.orig sl (by rw [← hK.orig]; exact h), by rw [ecw]; exact hs'.curThread,
    (hJ.tcb _).2 (J.zH.1 _ hcT), by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu]; exact ⟨hdw, K.dwNe.2⟩, ?_,
    ⟨pt, by rw [hK.gpml4]; exact hT.archObj hpt⟩, by rw [hK.gpml4]; exact K.ga, by rw [hK.gpml4]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, J.zH.1 _ hcT, hcscH, K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head

/-- **The new current SC after a scheduler step**: `H`'s (the spec's SC,
`JPlaced`) and not dead (bound to the current thread, `CurInv`: its `TCB`
word is not 0, as a dead SC's is). -/
theorem JAtZ.sch_csc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hI' : Inv σ') (hC' : CurInv σ')
    (hdead : ∀ q ∈ D, Sched.DeadP (L := L) H s' q) : H (L.cscW s') ≠ none ∧ L.cscW s' ∉ D := by
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecs : L.cscW s' = nodeW st s' Z.c layout.node.CUR_SC := by
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA nodeW; rw [hc'.cur]
  have hcv0 : σ'.curSc = (L.cscW s').bv := by rw [ecs]; exact hs'.curSc
  obtain ⟨x, n, hx⟩ := hC'.sc
  have hobj0 := J.obj.tkw hK.toTK
  obtain ⟨c, hcC, hcv⟩ := hobj0.sc _ _ _ hx
  have hcw : c = L.cscW s' := P1.eq_of_bv (hcv.trans hcv0)
  rw [← hcw]
  obtain ⟨Tr, Cq, hJ⟩ := J.sch_jpl hw hK (Sched.idleScW_keep_of J.xtop.fin.1.1.1 hS' hK.isc)
  have hxc : σ'.kheap c.bv = some (.schedContext x n) := by rw [hcv]; exact hx
  have hHc := (hJ.sc c x n (J.c0 c hcC) hxc).2
  refine ⟨(by rw [hHc]; exact fun h => by cases h), fun hD => ?_⟩
  have d := ((hdead c hD).2.2.2.2 _ hHc).1
  obtain ⟨x', n', hk', hR⟩ := hs'.scs c hcC
  rw [hxc] at hk'; cases hk'
  obtain ⟨u, -, xt, -, -, hown, -⟩ := curOwn_of_curInv hS' hI' hC'
  have h1 := hR.tcb
  rw [hown x n hx, show scW c 24#u64 = P1.scTcbA c from scW_tcb c, d, optRef_zero] at h1
  cases h1

/-- **The facts after FL4's `schedule` the tail does not derive** (module
docstring): the VSpace current-thread relation and the arch CR3 (the arch
switch), the node-0 debug word, the dead set's objects still dead and P1's
`BlkOK`. -/
structure SchTailHyps (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (D : Set U64)
    (s : S) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) (Ac' : Set U64) : Prop where
  curOK : Vs.CurOK st Z.th s' σ'
  ar : AR a' σ'.archState.x64CurrentCr3
  dbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
  dwNe : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val
  dead : ∀ q ∈ D, Sched.DeadP (L := L) H s' q
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'
  /-- Every debug word kept (KENTRY-PLAN g2i: `JAtZ.live`'s frame). -/
  dbgK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s'

set_option maxHeartbeats 2000000 in
/-- **`JAtZ` after FL4's `schedule`** from `JAtZ` after the TCB timers
(module docstring). -/
theorem JAtZ.sch_tail {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    (hsc : Fl4Spec.schedule (Z := Unit) σ = ({((), σ')}, False))
    (hw : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ))
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hR' : NtfnStateRel Z.N Z.T (L.mem s') σ') (hN' : NSC Z.N Z.C σ')
    (hI' : Inv σ') (hC' : CurInv σ') (hA' : ActIdle σ') (hcr : CurRunW σ') (hoff : Sched.OffOK σ')
    (hbsa : Sched.BlockedScActive σ')
    (hT : SchTailHyps (L := L) AR Z H Cs D s s' a' σ' Ac') :
    ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a' σ' := by
  have hSch : SchS σ σ' := schs_schedule.of_eq hsc
  have hK : SchStep (fun _ => False) σ σ' := hSch.1
  have hKc : ∀ ct : Fl4Spec.ObjRef, SchStep (fun p => p = ct) σ σ' := fun ct =>
    { hK with kh := fun p => (hK.kh p).mono False.elim }
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hS := J.xtop.fin.1.1.1
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sched_step J.xtop J.ip J.nk hwT (hKc σ.curThread) hS' hR' hT.curOK hT.ar
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSch.2⟩
  refine ⟨Lst', J.sch_frame hwT hK hX' hCR' hRF' hY' hM' (J.sch_buf hwT hK) hRP' (J.sch_apart hwT hK)
    (J.sch_jpl hwT hK (J.idleW_keep hS' (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).1
        (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).2).2) (J.sc_jcov hwT hT.dead (fun q hq hn => absurd hq hn)
      (J.idleW_keep hS' (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).1
        (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).2))
    (J.sch_kern hwT hK hS' hT.dbg hT.dwNe (J.sch_csc hwT hK hS' hI' hC' hT.dead).1) (J.sch_utc hwT hK hT.dbg) hN' hI' (Or.inr hC')
    (Or.inl (curOwn_of_curInv hS' hI' hC')) hoff hA' hbsa (Or.inr hcr) hT.blk hT.dbgK
    (J.idleW_keep hS' (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).1
      (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).2).1 J.zD⟩

/-- **The entry tail on `JAt`** with `hSchedRest` discharged (module
docstring): `JAtZ` after the TCB timers (`hfireJ`, with `FireHypW`'s
facts) and the facts after `schedule` (`hTail`). -/
theorem jat_scheduleT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hnd : Fl4Spec.numDomains = 1)
    (hfireJ : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW Z.T Z.C σ1 ∧
      ∃ (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64), JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 r.1 r.2 σ1 ⦄)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      ∃ Ac' : Set U64, SchTailHyps (L := L) AR Z H Cs D1 rf.1 r.1 r.2 σ' Ac' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 r.2 σ' ∧ CurInv σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (schedule_refinesWP (Pf := fun rf σ1 => ∃ (Ac1 : Set U64)
      (Lst1 : U64 → List U64) (D1 : Set U64), JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 rf.1 rf.2 σ1)
    s a σ hS hR J.nsc hnd hfireJ hA hsni hsend hT) hTail) ?_
  rintro r ⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨Ac1, Lst1, D1, J1⟩, hw, hrun⟩, hRest⟩
  obtain ⟨Ac', hTl⟩ := hRest rf σ1 σ' D1 hF hsc hw hS' hI' hC' hA'
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  obtain ⟨Lst', J'⟩ := J1.sch_tail hsc hw hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hTl
  exact ⟨σ', Ac', Lst', D1, J', hC'⟩

end

end

end Fl4Proofs.P3
