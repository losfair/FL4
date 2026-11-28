/-
P3 (p3J gen 38): **the SchedContext YieldTo leaf at stable ghosts; the SchedContext cap done for both classes; the
top with the rest set {CNode, Thread}**.

* `JAtZ.yieldToJSt`, **`decScYieldJSt`**: ScJointYield's `JAtZ.yieldToJ` / `decode_invocation_sched_context_yieldJ`
  with `JStab Z H Cs` for `JAt` (the same proofs: the restart at `Z`, the yielder's completion at `Z.mv Z.G V`,
  `resume` / `yield_switches` at the same sets, `set_consumed` at `(Z.mv Z.G V).mv Z.G V'`, `Running` there; peeled
  by `JStab.mv`).
* **`decScStAll`** (any flags, **any label**): P3JScUnb's `decScStY` and the YieldTo leaf (footprint
  P3JScFt's `scDecFootJ`).
* `IsRestCap6`: CNode or Thread (label-blind). `restCap5_of6`, `restCap6_of`. **`midDecRest5_of_scY`** /
  **`invDecRest5_of_scY`**: `MidDecStWL` / `InvDecStWL` at `KW ∧ IsRestCap5` from the YieldTo leaf and
  `MidDecStW` / `InvDecStW` at `KW ∧ IsRestCap6`; `midDecStW_of_5`, `invDecStW_of_5` (antitone).
* **`DispStabFootLy` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap6` (plain `MidDecStW` / `InvDecStW`),
  midSpec, midRecvSw verbatim}; **`dispStabFootLu_of_Ly`** (the tops' platform facts), **`dispStabFootLy_of_Lu`**,
  **`dispStabFootLy_of_Lo`** (gen 36's `DispStabFootLo` implies it: `IsRestCap6 → IsRestCap`); top
  **`kernel_entry_runMcWKR_sysLy`** (globals verbatim as `_sysLu`).

Premise honesty: `DispStabFootLy` is `DispStabFootLo` with the decode fields at the smaller cap predicate
{CNode, Thread} (`dispStabFootLy_of_Lo`, proved; also implied by `DispStabFootLu`, `dispStabFootLy_of_Lu`), and
implies `DispStabFootLu` / `Lt` / `Ls` / `Lq` given the tops' platform facts. No new kind of premise.

Named premise: `DispStabFootLy` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JScUnb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 32000000 in
/-- (p3J gen 38) **YieldTo's invocation at `J`, at stable ghosts** (ScJointYield's `JAtZ.yieldToJ`, the same
proof: the yielder's completion and `set_consumed` move only the VSpace sets, the rest keep `Z`). -/
theorem JAtZ.yieldToJSt (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hAT : P0.ArchTotal arI)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {sc : U64} (hsc : sc ∈ Z.C) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n)) (htc : x.scTcb = some t.bv)
    {ct : U64} (hct : ct ∈ Z.T) (hcur : σ.curThread = ct.bv)
    {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrs : xc.tcbState = .restart)
    (hycn : xc.tcbYieldTo = none) (hcs : Fl4Spec.schedulable ct.bv σ = true) (call : Bool) :
    schedcontext.yield_to st arI s a sc call ⦃ r => r.2 = a ∧ ∃ data σy,
      Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ = ({(data, σy)}, False) ∧
      ((data = [] ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σy) ∨
        (L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ σ2, ((), σ2) ∈ (specTail call ct.bv data σy).1 ∧
          JStab (L := L) arI AR Z H Cs r.1 r.2 σ2)) ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x0, n0, hk0, hx⟩ := hs.scs sc hsc
  rw [hk] at hk0; cases hk0
  have hsc0 := J.c0 sc hsc
  have hyfw : x.scYieldFrom = Notif.optRef (L.mem s (scYieldFromA sc)) := by
    rw [scYieldFromA_eq]; exact hx.yieldFrom
  have hyc : L.mem s (yieldA ct) = 0#u64 := by
    obtain ⟨y0, hy0, e0⟩ := J.yld.tcb ct hct
    rw [hkc] at hy0; cases hy0
    exact optRef_eq_none (by rw [← e0]; exact hycn)
  -- the SC's thread holds the SC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc x n hsc0 hk).2⟩
  obtain ⟨-, -, -, xt, hkt, hxt⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hsc hscS hsc0 hk htc
  unfold schedcontext.yield_to
  step with obj.Sc.yield_from.spec' as ⟨yf, hyf⟩
  subst hyf
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  subst hb
  refine WP.spec_bind (show _ ⦃ r => r.2 = a ∧ ∃ σc, (Fl4Spec.NonDet.when (x.scYieldFrom ≠ none) (do
        Fl4Spec.completeYieldTo (Z := Unit) (Fl4Spec.the x.scYieldFrom)
        let o ← Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scYieldFrom sc.bv
        Fl4Spec.NonDet.assert (o = none)) : Fl4Spec.SMonad Unit Unit) σ = ({((), σc)}, False) ∧
      SFrame σ σc ∧ (∃ x1, σc.kheap sc.bv = some (.schedContext x1 n) ∧ x1.scYieldFrom = none) ∧
      (∃ xc1, σc.kheap ct.bv = some (.tcb xc1) ∧ xc1.tcbYieldTo = none) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σc ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scYieldFromA sc) = 0#u64
    · simp only [h0, decide_true, ↓reduceIte]
      have hxn : x.scYieldFrom = none := by rw [hyfw, h0, Notif.optRef_zero]
      refine (WP.spec_ok _).mpr ⟨rfl, σ, ?_, SFrame.refl σ, ⟨x, hk, hxn⟩, ⟨xc, hkc, hycn⟩, Z.vs, Ac, Lst, D, J⟩
      rw [nd_when_false_y (by rw [hxn]; simp)]; rfl
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hxf : x.scYieldFrom = some (L.mem s (scYieldFromA sc)).bv := by rw [hyfw, Notif.optRef_ne h0]
      obtain ⟨u, hu, hub, hum⟩ := J.yld.frm sc hsc x n hk _ hxf
      have hue := eq_of_bv hub
      rw [← hue] at hxf ⊢
      obtain ⟨xu, hku, hyu⟩ := J.yld.tcb u hu
      have hyu' : xu.tcbYieldTo = some sc.bv := by rw [hyu, hum, Notif.optRef_ne hsc0]
      have hcu : ct ≠ u := fun e => by rw [e, hum] at hyc; exact hsc0 hyc
      refine WP.spec_mono (J.completeYieldJa hAT hmax htu hu) ?_
      rintro ⟨s1, a1⟩ ⟨ha1, σc, hcy, V, Ac1, Lst1, D1, J1⟩
      obtain ⟨hsf, ⟨x1, hk1, hyf1⟩, hyk⟩ := completeYieldTo_sframe hku hyu' hk hcy
      obtain ⟨xc1, hkc1, hyc1⟩ := hyk _ xc (bv_ne hcu) hkc
      refine ⟨ha1, σc, ?_, hsf, ⟨x1, hk1, hyf1⟩, ⟨xc1, hkc1, hyc1.trans hycn⟩, V, Ac1, Lst1, D1, J1⟩
      unfold Fl4Spec.NonDet.when
      rw [ite_eq_left (by rw [hxf]; simp), hxf]
      show (Fl4Spec.completeYieldTo u.bv >>= _) σ = _
      rw [nd_bind_one hcy, nd_bind_one (getScObjRef_eq hk1 _), hyf1]
      show (({x | (none : Option Fl4Spec.ObjRef) = none ∧ x = ((), σc)}, ¬ (none : Option Fl4Spec.ObjRef) = none) :
        Set (Unit × Fl4Spec.State Unit) × Prop) = _
      simp
  rintro ⟨s1, a1⟩ ⟨ha1, σc, hw1, hsf, ⟨x1, hk1, hyf1⟩, ⟨xc1, hkc1, hyc1⟩, V, Ac1, Lst1, D1, J1⟩
  change a1 = a at ha1
  subst a1
  -- the objects after the yielder's completion
  obtain ⟨x1', hk1', htc1', -⟩ := hsf.sc _ x n hk
  rw [hk1] at hk1'; cases hk1'
  have htc1 : x1.scTcb = some t.bv := htc1'.trans htc
  obtain ⟨xt1, hkt1, -, hxt1', -, -⟩ := hsf.tcb _ xt hkt
  have hxt1 : xt1.tcbSchedContext = some sc.bv := hxt1'.trans hxt
  obtain ⟨xc1', hkc1', hst1, -⟩ := hsf.tcb _ xc hkc
  rw [hkc1] at hkc1'; cases hkc1'
  have hrs1 : xc1.tcbState = .restart := hst1.trans hrs
  have hcur1 : σc.curThread = ct.bv := hsf.cur.trans hcur
  have hcs1 : Fl4Spec.schedulable ct.bv σc = true := hsf.schedulable hcs
  have hyc1' : L.mem s1 (yieldA ct) = 0#u64 := by
    obtain ⟨y1, hy1, e1⟩ := J1.yld.tcb ct hct
    rw [hkc1] at hy1; cases hy1
    exact optRef_eq_none (by rw [← e1]; exact hyc1)
  have hS1 := J1.xtop.fin.1.1.1
  have hR1 := J1.xtop.fin.1.1.2.2.1
  obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
  obtain ⟨hrun1, hrel1⟩ := J1.inv.yieldRes hk1 hkt1 hxt1
  have hne1 := J1.inv.ne _ _ _ hk1
  have hres : Fl4Spec.schedContextResume (Z := Unit) sc.bv σc = ({((), σc)}, False) :=
    resume_spec_noop hk1 htc1 hkt1 hne1 hrun1 hrel1
  refine WP.spec_bind (resume_noop (ar := arI) s1 a σc hR1 hS1 hmb hsc hsc0 ht (word24_of hS1 hsc hk1 htc1)
    (scA_of hS1 ht hkt1 hxt1) hk1 hrel1) ?_
  rintro r rfl
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  have hct'' : ct' = ct := by
    rw [hct', hc1.cur]; exact eq_of_bv (hs1.curThread.symm.trans hcur1)
  clear hct'
  subst ct'
  refine WP.spec_bind (J1.yieldSwitchesJ hsc hk1 hyf1 ht htc1 hct hcur1 hyc1' hcs1) ?_
  rintro ⟨b1, s3⟩ ⟨σ3, hsw, hk3, Ac3, Lst3, D3, J3⟩
  have hsw' := hsw
  unfold yieldSwitch at hsw'
  have hpre : Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ =
      (if (!b1) = true then Fl4Spec.returnConsumed (Z := Unit) sc.bv else pure []) σ3 := by
    unfold Fl4Spec.schedContextYieldTo
    rw [nd_bind_one (getScObjRef_eq hk _), nd_bind_one hw1, nd_bind_one hres, nd_bind_one hsw']
  cases b1
  swap
  · show (if true = true then _ else _) ⦃ _ ⦄
    rw [ite_eq_left rfl]
    exact (WP.spec_ok _).mpr ⟨rfl, [], σ3, by rw [hpre]; rfl, Or.inl ⟨rfl, JStab.mv J3.stab⟩⟩
  -- the call returns at once: the consumed time
  show (if false = true then _ else _) ⦃ _ ⦄
  rw [ite_eq_right (fun h => Bool.false_ne_true h)]
  have hk3' : σ3.kheap = σc.kheap := hk3 rfl
  have hkc3 : σ3.kheap ct.bv = some (.tcb xc1) := by rw [hk3']; exact hkc1
  have hks3 : σ3.kheap sc.bv = some (.schedContext x1 n) := by rw [hk3']; exact hk1
  obtain ⟨c, v, hv⟩ := updConsumed_one hks3
  set σu := updSc σ3 sc.bv (Fl4Spec.scConsumedUpdate (fun _ => v) x1) n with hσu
  have hsct : ct.bv ≠ sc.bv := fun e => by rw [e, hks3] at hkc3; cases hkc3
  have hku : σu.kheap ct.bv = some (.tcb xc1) := by
    simp only [hσu, updSc, updK, Function.update_of_ne hsct]; exact hkc3
  have hrc : Fl4Spec.returnConsumed (Z := Unit) sc.bv σ3 = ({(Fl4Spec.wordsFromTime c, σu)}, False) := by
    unfold Fl4Spec.returnConsumed; rw [nd_bind_one hv]; rfl
  have hsetc : Fl4Spec.setConsumed (Z := Unit) sc.bv ct.bv σ3 =
      Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, Fl4Spec.wordsFromTime c) σu := by
    unfold Fl4Spec.setConsumed; rw [nd_bind_one hv]
  have hSC : schedcontext.set_consumed st arI s3 a sc ct call ⦃ s4 => ∃ σ4,
      Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, Fl4Spec.wordsFromTime c)) σu =
        ({((), σ4)}, False) ∧ ∃ y, σ4.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart ∧
      ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR ((Z.mv Z.G V).mv Z.G V') H Cs Ac' Lst' D' s4 a σ4 ⦄ := by
    cases call
    · unfold schedcontext.set_consumed
      refine WP.spec_bind (J3.updConsumedJ hAT hmax htu hsc hct) ?_
      rintro ⟨cv, s4⟩ ⟨σ4, c', he4, V4, J4⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hv] at he4
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he4))
      refine (WP.spec_ok _).2 ⟨σu, ?_, _, hku, hrs1, V4, Ac3, Lst3, D3, J4⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_right (by simp)]; rfl
    · refine WP.spec_mono (J3.setConsumedJ hAT hmax htu hsc hct) ?_
      rintro s4 ⟨σ4, he4, -, V4, J4⟩
      obtain ⟨v', w', he4'⟩ := Sched.setConsumed_shape hks3 hkc3
      have eσ4 := the_result he4' he4
      refine ⟨σ4, ?_, Endp.replyTcb xc1 w', by rw [eσ4]; simp [updK], hrs1, V4, Ac3, Lst3, D3, J4⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_left rfl, ← hsetc]; exact he4
  refine WP.spec_bind hSC ?_
  rintro s4 ⟨σ4, hrf, y, hk4, hrs4, V4', Ac4, Lst4, D4, J4⟩
  have hct4 : ct ∈ ((Z.mv Z.G V).mv Z.G V4').T := hct
  refine WP.spec_bind (J4.runJ hct4 hk4 hrs4) ?_
  rintro s5 ⟨Lst5, D5, J5⟩
  refine (WP.spec_ok _).mpr ⟨rfl, Fl4Spec.wordsFromTime c, σu, ?_, Or.inr ⟨?_, _, ?_, JStab.mv (JStab.mv J5.stab)⟩⟩
  · rw [hpre]; exact hrc
  · intro e
    obtain ⟨x5, hk5, hrel5⟩ := J5.xtop.fin.1.1.2.2.1.tcb ct hct4
    rw [stsAct_kheap] at hk5
    simp only [updK_kheap, Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hk5
    have h1 := hrel5.st
    rw [← hk5, show tStA ct = stA ct by rw [tStA_eq, stA_eq], e, tsVals.2.1] at h1
    simp [tsCode] at h1
  · rw [specTail_of_restart hku hrs1, nd_bind_one hrf, Notif.setThreadState_eq .running hk4]
    exact Set.mem_singleton _

set_option maxHeartbeats 16000000 in
/-- (p3J gen 38) **The SchedContext cap's YieldTo, `XCap` at stable ghosts** (ScJointYield's
`decode_invocation_sched_context_yieldJ`, the same proof with `JStab Z H Cs` for `JAt`). -/
theorem decScYieldJSt (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ) (hAT : P0.ArchTotal arI)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l45 : lbl = fl4_abi.label.SchedContextYieldTo)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JStab (L := L) arI AR Z H Cs) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  refine xcap_of_or ?_
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  obtain ⟨hcur, xc, hkc, hrunc⟩ := J.curRunnable hni hct
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have hcs : Fl4Spec.schedulable ct.bv σ = true := by
    have h := ct_schedulable (J.curInv (by rw [hni.2]; simp)) J.act J.inv (hcur ▸ hkc) hrunc
    rw [hcur] at h; exact h
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hsc0 := J.c0 sc hsc
  have hg : Fl4Spec.genInvocationType slbl = .schedContextYieldTo := by
    rw [hlbl, l45]; unfold scLabelOf; simp
  have hdec : (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
      (Fl4Spec.decodeSchedContextYieldTo (Z := Unit) sc.bv).run σ := by
    unfold Fl4Spec.decodeSchedContextInvocation; rw [hg]
  have hill : ∀ (P : Prop) [Decidable P], P → ∀ f : Unit → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError .illegalOperation) >>= f).run σ =
        ({(.error .illegalOperation, σ)}, False) := fun P _ h f => wE_pos h _ f σ
  have hxtw : x.scTcb = Notif.optRef (L.mem s (scW sc 24#u64)) := hx.tcb
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl (Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, J.stab⟩)
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold schedcontext.decode
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0).1
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok]
  have l44 : lbl ≠ fl4_abi.label.SchedContextConsumed := lbl_ne l45 (by simp)
  have l41 : lbl ≠ fl4_abi.label.SchedContextBind := lbl_ne l45 (by simp)
  have l43 : lbl ≠ fl4_abi.label.SchedContextUnbindObject := lbl_ne l45 (by simp)
  have l42 : lbl ≠ fl4_abi.label.SchedContextUnbind := lbl_ne l45 (by simp)
  rw [ite_eq_right l44, ite_eq_right l41, ite_eq_right l43, ite_eq_right l42, ite_eq_left l45]
  -- `decode_sched_context_yield_to`'s checks
  step with P1.obj.Sc.tcb.spec as ⟨i1, hi1⟩
  rw [scTcbA_eq] at hi1
  subst hi1
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  subst hb
  by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err ?_, Or.inl trivial⟩,
      J.stab⟩))
    rw [hdec]
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [lE_bind (getScObjRef_eq hk _), hxtw, h0, Notif.optRef_zero]
    exact hill _ rfl _
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨ht, -, -⟩ := hback h0
  set t := L.mem s (scW sc 24#u64) with htdef
  have htc : x.scTcb = some t.bv := by rw [hxtw, Notif.optRef_ne h0]
  obtain ⟨xt, hkt, -, -, hxts, hpt⟩ := hs.tcb t ht
  have hpre : ∀ f : Option Fl4Spec.ObjRef → Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation,
      (Fl4Spec.NonDetE.liftE (Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv) >>= f).run σ =
        (f (some t.bv)).run σ := fun f => by rw [lE_bind (getScObjRef_eq hk _), htc]
  step as ⟨b1, hb1⟩
  by_cases hte : t = ct
  · have : b1 = true := hb1.2 hte
    simp only [this, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err ?_, Or.inl trivial⟩,
      J.stab⟩))
    rw [hdec]
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [hpre, wE_neg (by simp), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur, ← hte]
    exact hill _ rfl _
  have : b1 = false := Bool.eq_false_iff.2 (fun h => hte (hb1.1 h))
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hne' : t.bv ≠ ct.bv := bv_ne hte
  obtain ⟨xm, hkm, hmc, -⟩ := J.mcp ct hctT
  rw [hkc] at hkm; cases hkm
  obtain ⟨xy, hky, hyc⟩ := J.yld.tcb ct hctT
  rw [hkc] at hky; cases hky
  have hpre2 : (Fl4Spec.decodeSchedContextYieldTo (Z := Unit) sc.bv).run σ =
      (Fl4Spec.NonDetE.whenE (xt.tcbPriority > xc.tcbMcpriority)
        (Fl4Spec.NonDetE.throwError .illegalOperation) >>= fun _ => do
        let ytPtr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.threadGet (Z := Unit) Fl4Spec.Tcb.tcbYieldTo ct.bv
        Fl4Spec.NonDetE.whenE (ytPtr ≠ none) <| Fl4Spec.NonDetE.throwError .illegalOperation
        Fl4Spec.NonDetE.returnOk <| .invokeSchedContextYieldTo sc.bv).run σ := by
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [hpre, wE_neg (by simp), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur, wE_neg (by simpa using hne'),
      show Fl4Spec.the (some t.bv) = t.bv from rfl, lE_bind (threadGet_eq _ hkt), lE_bind (threadGet_eq _ hkc)]
  step with obj.Tcb.prio.spec as ⟨i2, hi2⟩
  step with Sched.obj.Tcb.mcp.spec' as ⟨i3, hi3⟩
  subst hi2 hi3
  by_cases hgt : L.mem s (prioA t) > L.mem s (mcpA ct)
  · simp only [hgt, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err ?_, Or.inl trivial⟩,
      J.stab⟩))
    rw [hdec, hpre2]
    exact hill _ ((w8_gt_iff hpt hmc).1 hgt) _
  simp only [hgt, ↓reduceIte]
  have hpre3 := hpre2
  rw [wE_neg (fun h => hgt ((w8_gt_iff hpt hmc).2 h)), lE_bind (threadGet_eq _ hkc)] at hpre3
  step with obj.Tcb.yield_to.spec as ⟨i4, hi4⟩
  subst hi4
  by_cases hy0 : L.mem s (yieldA ct) = 0#u64
  swap
  · have : (L.mem s (yieldA ct) != 0#u64) = true := by simp [hy0]
    simp only [this, ↓reduceIte]
    refine illegal_ok s a _ (Or.inl (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err ?_, Or.inl trivial⟩,
      J.stab⟩))
    rw [hdec, hpre3]
    exact hill _ (by rw [hyc, Notif.optRef_ne hy0]; simp) _
  have : (L.mem s (yieldA ct) != 0#u64) = false := by simp [hy0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hyn : xc.tcbYieldTo = none := by rw [hyc, hy0, Notif.optRef_zero]
  rw [wE_neg (by simp [hyn])] at hpre3
  have hrun : (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
      ({(.ok (.invokeSchedContextYieldTo sc.bv), σ)}, False) := by
    rw [hdec, hpre3]; rfl
  -- the caller's restart, then `yield_to`
  obtain ⟨s1, σ1, x1, -, he0, hkx1, -, eσ1, -, -, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hkc] at hkx1; cases hkx1
  rw [hs1]; simp only [bind_ok]
  have hpcs : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  have hf := stsAct_fields (Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv
  have hk1 : σ1.kheap sc.bv = some (.schedContext x n) := by
    rw [eσ1, hf.1]; simp [updK, hpcs, hk]
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [eσ1, hf.1]; simp [updK]
  have hcur1' : σ1.curThread = ct.bv := hcur1.trans hcur
  have hcs1 : Fl4Spec.schedulable ct.bv σ1 = true := by
    obtain ⟨xq, scp, yq, nq, hq1, hq2, -, hq4, hq5, hq6⟩ := schedulable_inv hcs
    rw [hkc] at hq1; cases hq1
    have hscp : scp ≠ ct.bv := fun e => by rw [e, hkc] at hq4; cases hq4
    refine schedulable_of (y := yq) (n := nq) hkc1 hq2 rfl ?_ hq5 ?_
    · rw [eσ1, hf.1]; simp [updK, hscp, hq4]
    · rw [eσ1, hf.2.2.2]; exact hq6
  refine WP.spec_bind (J1.yieldToJSt hAT hmb hmax htu hsc ht hk1 htc hctT hcur1' hkc1 rfl hyn hcs1 call) ?_
  rintro ⟨s3, a2⟩ ⟨-, data, σy, hyt, hcase⟩
  show (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ _ ⦄
  rw [WP.spec_ok]
  have hmem : (data, σy) ∈ (Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo sc.bv) σ1).1 := by
    show (data, σy) ∈ (Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ1).1
    rw [hyt]; exact Set.mem_singleton _
  rcases hcase with ⟨rfl, G', V', Ac', Lst', D', J'⟩ | ⟨hne, σ2, htail, G', V', Ac', Lst', D', J'⟩
  · left
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
    exact Or.inr ⟨.invokeSchedContext (.invokeSchedContextYieldTo sc.bv), DecOut.of_eq (run_liftME_ok hrun), σ1, he0,
      (.ok [], σy), mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo sc.bv))
        (s := σ1) (x := ([], σy)) hmem,
      ⟨(Z.mv G' V').th, (Z.mv G' V').G, Or.inl ⟨rfl, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ⟨G', V', Ac', Lst', D', J'⟩⟩
  · right
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
    exact Or.inr ⟨rfl, hne, .invokeSchedContext (.invokeSchedContextYieldTo sc.bv), DecOut.of_eq (run_liftME_ok hrun),
      σ1, he0, data, σy,
      mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo sc.bv))
        (s := σ1) (x := (data, σy)) hmem,
      ((), σ2), htail, ⟨(Z.mv G' V').th, (Z.mv G' V').G, hPl, hCR, hFI, hD, hMO⟩, ⟨G', V', Ac', Lst', D', J'⟩⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 38) The caps left after the SchedContext leaf: CNode, Thread. -/
def IsRestCap6 : capability.Cap → Prop
  | .CNode .. => True
  | .Thread _ => True
  | _ => False

theorem restCap5_of6 {cp : capability.Cap} {l : U64} (h : IsRestCap6 cp) : IsRestCap5 cp l := by
  cases cp
  all_goals first | trivial | exact False.elim h

theorem restCap6_of {cp : capability.Cap} {l : U64} (h : IsRestCap5 cp l)
    (hS : ¬ ∃ p sb, cp = .SchedContext p sb ∧ l = fl4_abi.label.SchedContextYieldTo) : IsRestCap6 cp := by
  cases cp
  case SchedContext p sb => exact absurd ⟨p, sb, rfl, h⟩ hS
  all_goals first | trivial | exact False.elim h

theorem restCap_of6 {cp : capability.Cap} (h : IsRestCap6 cp) : IsRestCap cp := by
  cases cp
  all_goals first | trivial | exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The SchedContext cap's decode at a dispatch state, any flags, any label** (module docstring). -/
theorem decScStAll (hA : P0.ArchTotal arI) (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.SchedContext p sb))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (args : List Fl4Spec.Data) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.SchedContext p sb) bl call don fp buf e mi.miLabel
      args ci sl exs buffer ct := by
  by_cases hy : info.label ≠ fl4_abi.label.SchedContextYieldTo
  · exact decScStY hA hARI hMT hKD hT hmax htu J hnib hMb hct hinfo hmi hbuf hbuffer hr2 her sl hsl hc he hexs hy
      args bl call don fp ci
  rw [not_not] at hy
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hq : QuietF (.SchedContext p sb) := by simp [QuietF]
  refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
    (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
  have hX := J.xtop
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  obtain ⟨hpC, hpi, -, -, hback, hbn⟩ := J.scCtxCap arI hAs.isSlot hc
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  obtain ⟨sl', hlbl, -, hd⟩ := sc_canon info.label
  refine XCapP.lbl_congr arI (specDec_sc p sb hd) ?_
  refine XCap.toPN arI ?_ (specDec_noPreK (by trivial))
  have hex := ExtraOK.rel1 hX.rel.1 (hXO e exs he hexs)
  have hx0 := exAt_idx0 e
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hnib hct
  have hcs := ct_schedulable (J.curInv (by rw [hnib.2]; simp)) J.act J.inv (hcur ▸ hkc) hrun
  rw [hcur] at hcs
  refine XCap.andW (X := JStab (L := L) arI AR (Z.mv Z.G V') H Cs)
    (Q := fun s1 => P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ?_
    (scDecFootJ J hT (hT.mb a') hmax (htu a') info.label sl' hlbl sb hpC hpi hback hbn hct hcs e (exAt e 0) hx0
      exs hex (msgLen info buf) (cslotAddr sl) buf bl call don fp)
  exact decScYieldJSt s' a' σb J hnib hA (hT.mb a') hmax (htu a') info.label sl' hlbl hy sb hpC hback hct e exs
    (msgLen info buf) (cslotAddr sl) buf bl call don fp args ci sl buffer

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **`MidDecStWL` at `KW ∧ IsRestCap5` from the YieldTo leaf** (module
docstring). -/
theorem midDecRest5_of_scY (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p sb, cp = .SchedContext p sb ∧ info.label = fl4_abi.label.SchedContextYieldTo
  · obtain ⟨p, sb, rfl, -⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScStAll hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap6_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **`InvDecStWL` at `KW ∧ IsRestCap5` from the YieldTo leaf** (module
docstring). -/
theorem invDecRest5_of_scY (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p sb, cp = .SchedContext p sb ∧ info.label = fl4_abi.label.SchedContextYieldTo
  · obtain ⟨p, sb, rfl, -⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScStAll hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap6_of hW.2 hS⟩

/-- (p3J gen 38) `MidDecStWL` at `KW ∧ IsRestCap5` gives `MidDecStW` at `KW ∧ IsRestCap6` (antitone). -/
theorem midDecStW_of_5 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap5_of6 hW.2⟩

/-- (p3J gen 38) `InvDecStWL` at `KW ∧ IsRestCap5` gives `InvDecStW` at `KW ∧ IsRestCap6` (antitone). -/
theorem invDecStW_of_5 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n call bl don) :
    InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap5_of6 hW.2⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 38) **`DispStabFootLy` [J]**: `DispStabFootLu` with `invDecRest` / `midDecRest` restricted to the
CNode and Thread caps (module docstring). -/
structure DispStabFootLy (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLu.invDecRest` at `KW ∧ IsRestCap6`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLu.midDecRest` at `KW ∧ IsRestCap6`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n c
  /-- `DispStabFootLu.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLu.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 38) **`DispStabFootLy → DispStabFootLu`** given the tops' platform facts (module docstring). -/
theorem dispStabFootLu_of_Ly (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLy (L := L) arI AR MR s a σ) :
    DispStabFootLu (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest5_of_scY hA hnd hARI (MachPlatF.toT hM hIp) hKD hT hmax htu hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest5_of_scY hA hnd hARI (MachPlatF.toT hM hIp) hKD hT hmax htu hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 38) **`DispStabFootLu → DispStabFootLy`** (the honesty claim: `DispStabFootLy` is implied). -/
theorem dispStabFootLy_of_Lu {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLu (L := L) arI AR MR s a σ) : DispStabFootLy (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStW_of_5 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStW_of_5 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 38) **`DispStabFootLo → DispStabFootLy`** (gen 36's premise implies the new one). -/
theorem dispStabFootLy_of_Lo {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLo (L := L) arI AR MR s a σ) : DispStabFootLy (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStW_anti (fun _ hW => ⟨hW.1, restCap_of6 hW.2⟩)
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStW_anti (fun _ hW => ⟨hW.1, restCap_of6 hW.2⟩)
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLy` only** (`hLy` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLy [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLy : DispStabFootLy (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLu hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLu_of_Ly hARI hA hnd hM hIp hKD hT hmax htu hLy)

end

end Fl4Proofs.P3.Mc
