/-
P3 (DESIGN.md §9): **the yielder's `complete_yield_to` at `J`**
(`JAtZ.completeYieldJ`; toward a final thread cap's and SC cap's
finalisations, XTop: `scYieldFinHyp_of`).

* `setConsumed_shape`: the spec's `set_consumed` of a yield-to pair: the SC's
  consumed time, the yielder's registers (`replyTcb`).
* `JAtZ.setConsumedJ`: FL4's `set_consumed` (`set_consumed_irel`, P1's
  `set_consumed.blk`) is a register step (`JAtZ.reg_frame`: a quiet step
  `QKY.upd2` keeping the yield fields, `Inv` by `Inv.scFields` and
  `ArchStep.inv`).
* `JAtZ.cancelYieldJ`: FL4's `cancel_yield_to` of a yielder is an SC step
  (`JAtZ.sc_frame`): the relations after as in `complete_yield_to_refines`
  (`set_sc_yf`, `set_yt`, `YieldRel.clear`), the mid-entry facts, `FK`,
  `BlockedScActive` and the link-cutting step by `QKY`, P1's
  `cancel_yield_to.blk`.
* `JAtZ.completeYieldJ`: the two in turn.

Named [P]: the platform's `ticks_to_us` and `getMaxTicksToUs` (`hmax`,
`htu`, as `scYieldFinHyp_of`).
-/
import Fl4Proofs.P3.XTopJointRegFrame
import Fl4Proofs.P3.XTopYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

/-- **The spec's `set_consumed`** of an SC and a TCB (module docstring). -/
theorem setConsumed_shape {σ : State Unit} {p t : ObjRef} {z : SchedContext} {n : Nat} {x : Tcb}
    (hks : σ.kheap p = some (.schedContext z n)) (hkt : σ.kheap t = some (.tcb x)) :
    ∃ v w, setConsumed (Z := Unit) p t σ = ({((), updK (updSc σ p (scConsumedUpdate (fun _ => v) z) n) t
      (.tcb (Endp.replyTcb x w)))}, False) := by
  have hpt : t ≠ p := by rintro rfl; rw [hkt] at hks; cases hks
  obtain ⟨c, v, hv⟩ : ∃ c v, schedContextUpdateConsumed (Z := Unit) p σ =
      ({(c, updSc σ p (scConsumedUpdate (fun _ => v) z) n)}, False) := by
    unfold schedContextUpdateConsumed
    rw [nd_bind_one (getSchedContext_eq hks), nd_pure_bind']
    split_ifs
    · rw [nd_bind_one (updateSchedContext_eq hks _)]; exact ⟨_, _, rfl⟩
    · rw [nd_bind_one (updateSchedContext_eq hks _)]; exact ⟨_, _, rfl⟩
  have hk1 : (updSc σ p (scConsumedUpdate (fun _ => v) z) n).kheap t = some (.tcb x) := by
    simp only [updSc, updK, Function.update_of_ne hpt]; exact hkt
  refine ⟨v, ucast 64 c, ?_⟩
  unfold setConsumed
  rw [nd_bind_one hv]
  exact Endp.replyFromKernel_one hk1 (ucast 64 c)

/-- `YKeep` across an SC's and a TCB's updates keeping their yield fields. -/
theorem ykeep_upd2 {σ : State Unit} {p t : ObjRef} {z w : SchedContext} {n : Nat} {x x' : Tcb}
    (hkp : σ.kheap p = some (.schedContext z n)) (hkt : σ.kheap t = some (.tcb x))
    (hw : w.scYieldFrom = z.scYieldFrom) (hx : x'.tcbYieldTo = x.tcbYieldTo) :
    YKeep σ (updK (updSc σ p w n) t (.tcb x')) := by
  have hpt : p ≠ t := by rintro rfl; rw [hkp] at hkt; cases hkt
  refine ⟨fun q x0 hq => ?_, fun q z0 m hq => ?_, fun q w0 m hq => ?_⟩
  · by_cases e1 : q = t
    · subst e1; rw [hkt] at hq; cases hq; exact ⟨x', by simp [updK], hx⟩
    · have e2 : q ≠ p := by rintro rfl; rw [hkp] at hq; cases hq
      exact ⟨x0, by simp [updK, e1, e2, hq], rfl⟩
  · by_cases e2 : q = p
    · subst e2; rw [hkp] at hq; cases hq; exact ⟨w, by simp [updK, hpt], hw⟩
    · have e1 : q ≠ t := by rintro rfl; rw [hkt] at hq; cases hq
      exact ⟨z0, by simp [updK, e1, e2, hq], rfl⟩
  · by_cases e1 : q = t
    · subst e1; simp [updK] at hq
    by_cases e2 : q = p
    · subst e2
      simp only [updK, Function.update_of_ne e1, Function.update_self, Option.some.injEq,
        KernelObject.schedContext.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      exact ⟨z, hkp, hw⟩
    · simp only [updK, Function.update_of_ne e1, Function.update_of_ne e2] at hq
      exact ⟨w0, hq, rfl⟩

/-- A TCB's saved-context update is an `ArchStep`. -/
theorem archStep_updTcb {σ : State Unit} {t : ObjRef} {x x' : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hx : x' = { x with tcbArch := x'.tcbArch }) : ArchStep σ (updK σ t (.tcb x')) := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = t
  · subst e; exact Or.inr ⟨x, x', hkt, by simp [updK], hx⟩
  · exact Or.inl (by simp [updK, e])

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`set_consumed` of a yield-to pair at `J`** (module docstring). -/
theorem JAtZ.setConsumedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {p y : U64} (hpC : p ∈ Z.C)
    (hy : y ∈ Z.T) :
    schedcontext.set_consumed st arI s a p y true ⦃ s1 => ∃ σ1,
      Fl4Spec.setConsumed (Z := Unit) p.bv y.bv σ = ({((), σ1)}, False) ∧ YKeep σ σ1 ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s1 a σ1 ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨z, n, hkz, -⟩ := hs.scs p hpC
  obtain ⟨x, hkx, -⟩ := hs.tcb y hy
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p z n (J.c0 p hpC) hkz).2⟩
  have hyT : y ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact hy
  have hta := hc.tcbs y hy
  refine WP.spec_mono (WP.spec_and (set_consumed_irel (ar := arI) J.ip s a σ hI hpC hkz hy hkx hmax htu)
    (P1.schedcontext.set_consumed.blk hAT s a p y true J.blk hpS hyT)) ?_
  rintro s1 ⟨⟨σ1, he, hI1, hw⟩, hP1⟩
  obtain ⟨v, w, he'⟩ := Sched.setConsumed_shape hkz hkx
  have e := the_result he' he
  subst e
  have hA := QKY.upd2 (w := Fl4Spec.scConsumedUpdate (fun _ => v) z) (x' := Endp.replyTcb x w) hkz hkx rfl rfl
  have hyk := ykeep_upd2 (w := Fl4Spec.scConsumedUpdate (fun _ => v) z) (x' := Endp.replyTcb x w) hkz hkx rfl rfl
  have hpy : y.bv ≠ p.bv := fun e => by rw [e, hkz] at hkx; cases hkx
  have hk1 : (updSc σ p.bv (Fl4Spec.scConsumedUpdate (fun _ => v) z) n).kheap y.bv = some (.tcb x) := by
    simp only [updSc, updK, Function.update_of_ne hpy]; exact hkx
  have hInv := (archStep_updTcb (x' := Endp.replyTcb x w) hk1 rfl).inv (J.inv.scFields hkz rfl rfl rfl rfl)
  have hw' : P1.WritesIn st s _ (RegCW Z.T Z.C) := hw.mono fun b hb => by
    rcases hb with rfl | ⟨r, rfl⟩
    · exact Or.inr ⟨p, hpC, rfl⟩
    · have hv := regA_val hta (regIdx_lt r)
      have := regIdx_lt r
      exact Or.inl ⟨y, hy, by rw [hv]; omega, by rw [hv]; omega⟩
  obtain ⟨V, J1⟩ := J.reg_frame hI1 hw' hA hyk hInv hP1.1 hP1.2.1
  exact ⟨_, he', hyk, V, J1⟩

set_option maxHeartbeats 8000000 in
/-- **`cancel_yield_to` of a yielder at `J`** (module docstring). -/
theorem JAtZ.cancelYieldJD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y p : U64} (hy : y ∈ Z.T)
    (hp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s y ⦃ s' => ∃ σ',
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := J.yld.tcb y hy
  obtain ⟨hpC, z, n, hkz, eyf⟩ := J.yld.toSc y hy (by rw [hp]; exact hp0)
  rw [hp] at hpC hkz eyt
  have hsw56 := sw_hdr hS hpC (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 : Aligned (scW p 56#u64) := by
    obtain ⟨x0, n0, -, hx0⟩ := hs.scs p hpC; exact (hx0.hdr (K := 56#u64) (by simp) (by simp)).1
  have hyT : y ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact hy
  have hcode : schedcontext.cancel_yield_to st s y ⦃ s' =>
      s' = L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64 ⦄ := by
    unfold schedcontext.cancel_yield_to
    step with obj.Tcb.is_null.spec as ⟨b2, hb2⟩
    have hb2' : b2 = false := by rw [hb2]; exact decide_eq_false hy0
    rw [hb2']
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with obj.Tcb.yield_to.spec as ⟨i2, hi2⟩
    rw [hp] at hi2
    rw [hi2]
    have hb' : (p != 0#u64) = true := by simp [hp0]
    simp only [hb', ↓reduceIte]
    exact WP.spec_bind (obj.Sc.set_yield_from.spec s _ 0#u64) fun s3 h3 => h3 ▸ obj.Tcb.set_yield_to.spec _ y 0#u64
  refine WP.spec_mono (WP.spec_and (P1.schedcontext.cancel_yield_to.blk s y J.blk hyT) hcode) ?_
  rintro s' ⟨hP, rfl⟩
  obtain ⟨hS3, hf3, hK3, hw3⟩ := hS.set_sc_yf hpC hkz 0#u64
  rw [Notif.optRef_zero] at hS3 hK3
  have hpy : p.bv ≠ y.bv := fun e => by rw [e, hky] at hkz; cases hkz
  have hkay : (updSc σ p.bv { z with scYieldFrom := none } n).kheap y.bv = some (.tcb xy) := by
    simp [updK, Ne.symm hpy, hky]
  obtain ⟨hS4, hf4, hK4⟩ := hS3.set_yt hy hkay 0#u64
  rw [Notif.optRef_zero] at hS4 hK4
  have hm4 : ∀ u ∈ Z.T, u ≠ y → L.mem (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) (yieldA u) =
      L.mem s (yieldA u) := by
    intro u hu hne
    rw [L.mem_wr_ne (yieldA_aligned hT hy) (yieldA_aligned hT hu)
      (fun e => hne (yieldA_inj hT hy hu (UScalar.eq_of_val_eq e.symm)))]
    exact WritesIn.yield_keep hT hw3 u hu
  have hmy : L.mem (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) (yieldA y) = 0#u64 :=
    L.mem_wr_same (yieldA_aligned hT hy)
  have hY' := J.yld.clear hy hp hp0 hky hkz hm4 hmy
  have hN' : NSC Z.N Z.C (updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv
      (.tcb { xy with tcbYieldTo := none })) := J.nsc.updSc.updTcb
  have hI' := (J.inv.scFields (y' := { z with scYieldFrom := none }) hkz rfl rfl rfl rfl).ytUpd hkay none
  have hR' := (hR.frame hS.placed hf3 hK3).frame hS3.placed hf4 hK4
  have he := cancelYieldTo_some hky (by rw [eyt, Notif.optRef_ne hp0]) hkz hpy
  have hm : ((), updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv (.tcb { xy with tcbYieldTo := none })) ∈
      (Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ _ := nkt_schedContextCancelYieldTo y.bv σ _ hm
  have hA : QKY σ (updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv (.tcb { xy with tcbYieldTo := none })) :=
    QKY.upd2 hkz hky rfl rfl
  have hW : P1.WritesIn st s (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    ((writesIn_wr (st := st) (s := s) (v := 0#u64)
        (show Aligned (scYieldFromA p) by rw [scYieldFromA_eq]; exact hal56)).trans
      (writesIn_wr (st := st) (s := L.wr s (scYieldFromA p) 0#u64) (v := 0#u64) (yieldA_aligned hT hy))).mono
      fun b hb => by
        rcases hb with rfl | rfl
        · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
        · exact Or.inr ⟨y, hy, rfl⟩
  have hX' : XTopAt (L := L) AR Z _ a _ :=
    xtop_sc_step (ct := σ.curThread) J.xtop J.ip J.nk hW (hK.mono fun _ h => h.elim) hS4 hR' id
  have hall := ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS4, hR', hN', hI'⟩ hY' (hW.mono fun b hb => Or.inl hb)
    ((pres_schedContextCancelYieldTo y.bv).of_eq he) rfl
  obtain ⟨-, -, hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  have hAI := hA.actIdle J.act
  have hYD : ∀ r, YDeadKeep σ (updK (updSc σ p.bv { z with scYieldFrom := none } n) y.bv
      (.tcb { xy with tcbYieldTo := none })) r := fun r =>
    YDeadKeep.upd (p := y.bv) (o := .tcb { xy with tcbYieldTo := none })
      (YDeadKeep.upd (p := p.bv) (o := .schedContext { z with scYieldFrom := none } n) (YDeadKeep.of_at rfl)
        (fun _ e => by cases e) (fun _ _ e => by cases e; rfl))
      (fun _ e => by cases e; rfl) (fun _ _ e => by cases e)
  have hdead : ∀ q ∈ D, DeadP (L := L) H (L.wr (L.wr s (scYieldFromA p) 0#u64) (yieldA y) 0#u64) q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) (hA.lk (W := fun _ => False)) hA.fk hAI.1 hY' (hYD q.bv)
      (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg (hP.2.1.mono (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (hP.2.1.mono (Set.empty_subset _))
  exact ⟨_, he, Ac, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2)) (J.sc_kern hW hK hA.fk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN' hI' (hA.cur J.cur) (hA.own J.own) (hA.off J.off) hAI (hA.bsa J.bsa)
    (hA.curRunM J.curRun) hP.1 hKd (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2).1 J.zD⟩

/-- `cancelYieldJD` with the dead set existential. -/
theorem JAtZ.cancelYieldJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y p : U64} (hy : y ∈ Z.T)
    (hp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s y ⦃ s' => ∃ σ',
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ' ⦄ :=
  WP.spec_mono (J.cancelYieldJD hy hp hp0) fun _ ⟨σ', he, Ac', Lst', J'⟩ => ⟨σ', he, Ac', Lst', D, J'⟩

set_option maxHeartbeats 8000000 in
/-- **The yielder's `complete_yield_to` at `J`** (module docstring), the dead set kept. -/
theorem JAtZ.completeYieldJD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := J.yld.tcb y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb2' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb2']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA y) = 0#u64
  · have : (L.mem s (yieldA y) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, completeYieldTo_none hky (by rw [eyt, hi0, Notif.optRef_zero]), Z.vs, Ac, Lst, J⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA y) = p := ⟨_, rfl⟩
  rw [hp] at hi0 eyt ⊢
  have hb' : (p != 0#u64) = true := by simp [hi0]
  simp only [hb', ↓reduceIte]
  obtain ⟨hpC, -⟩ := J.yld.toSc y hy (by rw [hp]; exact hi0)
  rw [hp] at hpC
  refine WP.spec_bind (J.setConsumedJ hAT hmax htu hpC hy) ?_
  rintro s1 ⟨σ1, he1, hyk, V1, J1⟩
  have hm1 : L.mem s1 (yieldA y) = p := by
    obtain ⟨x1, hk1, e1⟩ := J1.yld.tcb y hy
    obtain ⟨x1', hk1', e1'⟩ := hyk.1 _ xy hky
    rw [hk1] at hk1'; cases hk1'
    rw [eyt, Notif.optRef_ne hi0] at e1'
    rw [e1'] at e1
    exact P1.eq_of_bv (Notif.optRef_some e1.symm).2
  refine WP.spec_bind (J1.cancelYieldJD hy hm1 hi0) ?_
  rintro s2 ⟨σ2, he2, Ac2, Lst2, J2⟩
  refine (WP.spec_ok _).2 ⟨σ2, ?_, V1, Ac2, Lst2, J2⟩
  rw [completeYieldTo_some hky (by rw [eyt, Notif.optRef_ne hi0]), nd_bind_one he1]
  exact he2

/-- `completeYieldJD` with the dead set existential. -/
theorem JAtZ.completeYieldJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  WP.spec_mono (J.completeYieldJD hAT hmax htu hy) fun _ ⟨σ', he, V, Ac', Lst', J'⟩ => ⟨σ', he, V, Ac', Lst', D, J'⟩

end

end

end Fl4Proofs.P3
