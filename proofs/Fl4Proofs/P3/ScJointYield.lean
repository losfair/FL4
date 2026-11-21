/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext YieldTo at `J`**
(any yielder, either outcome: `decode_invocation_sched_context_yieldJ`),
and the SC labels of no invocation (`decode_invocation_sched_context_otherJ`),
proved at `J` directly as Unbind's (ScJointUnbind).

FL4's YieldTo branch: the decode's prefix, `decode_sched_context_yield_to`'s
checks (the SC's thread, not the caller, its priority at most the caller's
MCP, the caller yielding to nothing; the spec's `IllegalOperation` with the
state unchanged), the caller's restart (`JAtZ.restartJ`), then `yield_to`
(`JAtZ.yieldToJ`, as ScYieldTo's `yield_to_refines` with `JAtZ` carried):

* the SC's yielder (if any) completes its yield (`JAtZ.completeYieldJa`:
  XTopJointYield's `JAtZ.completeYieldJ` with the arch state kept); on the
  spec side `completeYieldTo_sframe` (an `SFrame` step after which the SC is
  yielded from by none and the caller's yield-to field is kept);
* `resume` is a no-op (ScYieldTo's `resume_noop`, `resume_spec_noop`);
* `yield_switches` (`JAtZ.yieldSwitchesJ`): the SC's thread not schedulable
  (nothing), of lower priority (`dequeue` and `enqueue` of it, each a
  scheduler step at `J`: `JAtZ.dequeueJ`, `JAtZ.enqueueJ` by
  XTopJointCopyRegs' `JAtZ.schedJ`), else the yield links
  (`JAtZ.linkYieldJ`: an SC step, `YieldRel.pair`), the requeues and the
  reschedule (`JAtZ.reschedJ`); the spec's `return_now` is the negation;
* when the call returns at once, `set_consumed` (XTopJointYield's
  `JAtZ.setConsumedJ` with the message when a call, else ScJointConsumed's
  `JAtZ.updConsumedJ`) and `Running` (`JAtZ.runJ`); the spec's
  `return_consumed` and `handle_invocation`'s reply tail end in the same
  state (as `sc_consumedReplyJ`).

The outcome is `DecOKDMX`'s (no data, `JAt` after `sched_context_yield_to`)
or `DecOKRMX`'s (the consumed time, `JAt` after the reply tail), chosen per
outcome (`xcap_of_or`). Named [P]: the platform's `min_budget`,
`ticks_to_us`, `getMaxTicksToUs` and `ArchTotal`; [W] the front end's label.
-/
import Fl4Proofs.P3.ScJointConsumed
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-- The spec's yield links of a switching YieldTo (`yieldSwitch`'s first two
steps): the caller yields to the SC, the SC is yielded from by the caller. -/
def yieldLink (ct sc : ObjRef) : SMonad Unit Unit := do
  setTcbObjRef tcbYieldToUpdate ct (some sc)
  setScObjRef scYieldFromUpdate sc (some ct)

theorem nkt_yieldLink (ct sc : ObjRef) : NKT (yieldLink ct sc) := by
  unfold yieldLink setScObjRef setTcbObjRef
  repeat' (first | nkt_step | (unfold NonDet.when; split) | split)

theorem pres_yieldLink (ct sc : ObjRef) : Pres (false, true) (yieldLink ct sc) := by
  unfold yieldLink; pres_auto

theorem yieldLink_eq {σ : State Unit} {ct sc : ObjRef} {xc : Tcb} {y : SchedContext} {n : Nat}
    (hkc : σ.kheap ct = some (.tcb xc)) (hks : σ.kheap sc = some (.schedContext y n)) (hpc : sc ≠ ct) :
    yieldLink ct sc σ = ({((), updSc (updK σ ct (.tcb { xc with tcbYieldTo := some sc })) sc
      { y with scYieldFrom := some ct } n)}, False) := by
  unfold yieldLink
  show (threadSet _ ct >>= _) σ = _
  rw [nd_bind_one (threadSet_eq _ hkc)]
  have hka : (updK σ ct (.tcb { xc with tcbYieldTo := some sc })).kheap sc = some (.schedContext y n) := by
    simp [updK, hpc, hks]
  exact updateSchedContext_eq hka _


/-- A TCB update keeping its state, SC, priority and domain keeps `SFrame`. -/
theorem SFrame.updTcbF {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    (e1 : x'.tcbState = x.tcbState) (e2 : x'.tcbSchedContext = x.tcbSchedContext)
    (e3 : x'.tcbPriority = x.tcbPriority) (e4 : x'.tcbDomain = x.tcbDomain) :
    SFrame σ (updK σ p (.tcb x')) := by
  refine ⟨fun q y hq => ?_, fun q y m hq => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq
      exact ⟨x', by simp [updK], e1, e2, e3, e4⟩
    · exact ⟨y, by simp [updK, h, hq], rfl, rfl, rfl, rfl⟩
  · have h : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp [updK, h, hq], rfl, rfl⟩

/-- **The spec's `complete_yield_to` of a yielder `u` yielding to `p`**: an
`SFrame` step, after which `p` is yielded from by none, and every other
TCB's yield-to field is kept. -/
theorem completeYieldTo_sframe {σ σ' : State Unit} {u p : ObjRef} {x : Tcb} {z : SchedContext} {n : Nat}
    (hku : σ.kheap u = some (.tcb x)) (hyt : x.tcbYieldTo = some p)
    (hkp : σ.kheap p = some (.schedContext z n))
    (he : completeYieldTo (Z := Unit) u σ = ({((), σ')}, False)) :
    SFrame σ σ' ∧ (∃ z', σ'.kheap p = some (.schedContext z' n) ∧ z'.scYieldFrom = none) ∧
      ∀ q y, q ≠ u → σ.kheap q = some (.tcb y) →
        ∃ y', σ'.kheap q = some (.tcb y') ∧ y'.tcbYieldTo = y.tcbYieldTo := by
  have hpu : p ≠ u := by rintro rfl; rw [hkp] at hku; cases hku
  obtain ⟨v, w, hsc⟩ := setConsumed_shape hkp hku
  rw [completeYieldTo_some hku hyt, nd_bind_one hsc] at he
  have hk1 : (updSc σ p (scConsumedUpdate (fun _ => v) z) n).kheap u = some (.tcb x) := by
    simp [updK, Ne.symm hpu, hku]
  have hka : (updK (updSc σ p (scConsumedUpdate (fun _ => v) z) n) u (.tcb (Endp.replyTcb x w))).kheap u =
      some (.tcb (Endp.replyTcb x w)) := by simp [updK]
  have hkpa : (updK (updSc σ p (scConsumedUpdate (fun _ => v) z) n) u (.tcb (Endp.replyTcb x w))).kheap p =
      some (.schedContext (scConsumedUpdate (fun _ => v) z) n) := by simp [updK, hpu]
  have e := the_result (cancelYieldTo_some hka (by rw [← hyt]; rfl) hkpa hpu) he
  subst e
  have h1 := SFrame.updSc (x' := scConsumedUpdate (fun _ => v) z) hkp rfl rfl
  have h2 := SFrame.updTcbF (x' := Endp.replyTcb x w) hk1 rfl rfl rfl rfl
  have h3 := SFrame.updSc (x' := { scConsumedUpdate (fun _ => v) z with scYieldFrom := none }) hkpa rfl rfl
  have hk3 : (updSc (updK (updSc σ p (scConsumedUpdate (fun _ => v) z) n) u (.tcb (Endp.replyTcb x w))) p
      { scConsumedUpdate (fun _ => v) z with scYieldFrom := none } n).kheap u =
      some (.tcb (Endp.replyTcb x w)) := by simp [updK, Ne.symm hpu]
  have h4 := SFrame.ytUpd hk3 none
  refine ⟨((h1.trans h2).trans h3).trans h4, ⟨{ scConsumedUpdate (fun _ => v) z with scYieldFrom := none }, by simp [updK, hpu], rfl⟩, fun q y hqu hq => ?_⟩
  have hqp : q ≠ p := by rintro rfl; rw [hkp] at hq; cases hq
  exact ⟨y, by simp [updK, hqu, hqp, hq], rfl⟩

/-- `tcb_sched_action` keeps the heap, the release queue and the current
thread. -/
theorem tsa_keep {σ σ' : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {f : ObjRef → List ObjRef → List ObjRef} (he : tcbSchedAction (Z := Unit) f t σ = ({((), σ')}, False)) :
    σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread := by
  rw [the_result (tcbSchedAction_gen hk f) he]; exact ⟨rfl, rfl, rfl⟩

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- A thread of `Z.T` is a TCB of the typed heap. -/
theorem JAtZ.thTcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    Z.th t = some .tcb := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact (hJ.tcb t).2 (J.zH.1 t ht)

set_option maxHeartbeats 4000000 in
/-- **`dequeue` at `J`** (DomSched's `dequeue_schedStep`, a scheduler step:
`JAtZ.schedJ`). -/
theorem JAtZ.dequeueJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    sched.dequeue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue t.bv σ =
      ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  refine WP.spec_mono (dequeue_schedStep (J.thTcb ht) hk hS ht) ?_
  rintro s' ⟨-, -, -, hSS⟩
  exact ⟨_, tcbSchedAction_gen hk _, J.schedJ hSS⟩

set_option maxHeartbeats 4000000 in
/-- **`enqueue` of a schedulable thread at `J`** (DomSched's
`enqueue_schedStep`; `JAtZ.schedJ`). -/
theorem JAtZ.enqueueJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.enqueue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv σ =
      ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  have hd := (schedulable_eq hR hS ht).trans hsch
  obtain ⟨hrw, hbd, hmx, hrl⟩ := of_decide_eq_true hd
  have hrun : P1.Runnable (L.mem s (P1.stA t)) := by rw [stA_tStA]; exact hrw
  refine WP.spec_mono (enqueue_schedStep (J.thTcb ht) hk hS ht (fun _ => hrl) hsch hrun hbd hrl
    (fun e => by rw [e] at hmx; simp at hmx)) ?_
  rintro s' ⟨-, -, -, hSS⟩
  exact ⟨_, tcbSchedAction_gen hk _, J.schedJ hSS⟩

set_option maxHeartbeats 8000000 in
/-- **The yield links at `J`** (`yield_switches`' `set_yield_to` and
`set_yield_from` of a switching YieldTo; as `JAtZ.cancelYieldJ` with the
links set: `YieldRel.pair`, P1's `yield_link.blk`). -/
theorem JAtZ.linkYieldJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct sc : U64} (hct : ct ∈ Z.T)
    (hsc : sc ∈ Z.C) (hy0 : L.mem s (yieldA ct) = 0#u64) {xc : Fl4Spec.Tcb}
    (hkc : σ.kheap ct.bv = some (.tcb xc)) {y : Fl4Spec.SchedContext} {n : Nat}
    (hks : σ.kheap sc.bv = some (.schedContext y n)) (hyf : y.scYieldFrom = none)
    (hrun : P1.Runnable (L.mem s (P1.stA ct))) (htw : L.mem s (P1.scTcbA sc) ≠ 0#u64) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D'
      (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) a
      (updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv { y with scYieldFrom := some ct.bv } n) := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hct).ne0 (by rw [e]; rfl)
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsc
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hks] at hk'; cases hk'
  have hsw56 := sw_hdr hS hsc (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 : Aligned (scW sc 56#u64) := (hx.hdr (K := 56#u64) (by simp) (by simp)).1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n hsc0 hks).2⟩
  have hctH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct hct
  have hblk := (P1.yield_link.blk J.blk hctH hscS).1
  -- the spec side
  obtain ⟨hS1, hf1, hK1⟩ := hS.set_yt hct hkc sc
  rw [Notif.optRef_ne hsc0] at hS1 hK1
  have hpc' : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hks; cases hks
  have hka : (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })).kheap sc.bv =
      some (.schedContext y n) := by simp [updK, hpc', hks]
  obtain ⟨hS2, hf2, hK2, hw2⟩ := hS1.set_sc_yf hsc hka ct
  rw [Notif.optRef_ne hct0] at hS2 hK2
  have hR2 := (hR.frame hS.placed hf1 hK1).frame hS1.placed hf2 hK2
  have hN2 := (J.nsc.updTcb (t := ct.bv) (x := { xc with tcbYieldTo := some sc.bv })).updSc
    (p := sc.bv) (y := { y with scYieldFrom := some ct.bv }) (n := n)
  have hI2 := (J.inv.ytUpd hkc (some sc.bv)).scFields (y' := { y with scYieldFrom := some ct.bv }) hka rfl rfl rfl rfl
  have hY2 := J.yld.pair J.c0 hct hsc hy0 hkc hks hyf
    (m' := L.mem (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct))
    (fun u hu hne => by
      rw [WritesIn.yield_keep hT hw2 u hu, L.mem_wr_ne (yieldA_aligned hT hct) (yieldA_aligned hT hu)
        (fun e => hne (yieldA_inj hT hct hu (UScalar.eq_of_val_eq e).symm))])
    (by rw [WritesIn.yield_keep hT hw2 ct hct]; exact L.mem_wr_same (yieldA_aligned hT hct))
  set σ' := updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv
    { y with scYieldFrom := some ct.bv } n with hσ'
  have hm : ((), σ') ∈ (yieldLink ct.bv sc.bv σ).1 := by
    rw [yieldLink_eq hkc hks hpc']; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ σ' := nkt_yieldLink ct.bv sc.bv σ _ hm
  have hsok : SOK (false, true) σ σ' := pres_yieldLink ct.bv sc.bv σ _ hm
  have hA : QKY σ σ' := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
    by_cases e1 : q = ct.bv
    · subst e1; exact Or.inr (Or.inl ⟨xc, { xc with tcbYieldTo := some sc.bv }, hkc, by simp [σ', updK, Ne.symm hpc'], rfl⟩)
    by_cases e2 : q = sc.bv
    · subst e2; exact Or.inr (Or.inr ⟨y, { y with scYieldFrom := some ct.bv }, n, hks, by simp [σ', updK], rfl⟩)
    · exact Or.inl (by simp [σ', updK, e1, e2])
  -- FL4's writes
  have hal' : Aligned (scYieldFromA sc) := by rw [scYieldFromA_eq]; exact hal56
  have hW : P1.WritesIn st s (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    ((writesIn_wr (st := st) (s := s) (v := sc) (yieldA_aligned hT hct)).trans
      (writesIn_wr (st := st) (s := L.wr s (yieldA ct) sc) (v := ct) hal')).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact Or.inr ⟨ct, hct, rfl⟩
      · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
  have hKW : P1.WritesIn st s (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct)
      (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s) :=
    ((writesIn_wr (st := st) (s := s) (v := sc) (yieldA_aligned hT hct)).trans
      (writesIn_wr (st := st) (s := L.wr s (yieldA ct) sc) (v := ct) hal')).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact P1.kw_field (K := 3472#u64) hctH (by simp) (by simp) (by simp)
      · obtain ⟨h128, -, -, -, -, -, -, e56⟩ := P1.sc_facts J.blk.2.2.1.1 hscS
        have e : (scYieldFromA sc).val = sc.val + 56 := e56
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hscS, by rw [e]; omega, by rw [e]; omega⟩)))
  have hDbg := J.kw_dbg hKW
  have hKd := J.kw_dbgKeep hKW
  have hX' : XTopAt (L := L) AR Z _ a σ' :=
    xtop_sc_step (ct := σ.curThread) J.xtop J.ip J.nk hW (hK.mono fun _ h => h.elim) hS2 hR2 id
  have hall := ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS2, hR2, hN2, hI2⟩ hY2 (hW.mono fun b hb => Or.inl hb)
    hsok rfl
  obtain ⟨-, -, hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  have hAI := hA.actIdle J.act
  -- the dead stay dead: the caller (runnable) and the SC (with a thread) are not dead
  have hdead : ∀ q ∈ D, DeadP (L := L) H (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) q := fun q hq => by
    have hd := J.jcov.dead q hq
    have hqc : q.bv ≠ ct.bv := fun e => by
      rw [P1.eq_of_bv e] at hd
      exact P1.runnable_ne_inactive hrun (hd.1 (J.zH.1 ct hct)).1
    have hqs : q.bv ≠ sc.bv := fun e => by
      rw [P1.eq_of_bv e] at hd
      exact htw (hd.2.2.2.2 _ (hJ.sc sc y n hsc0 hks).2).1
    exact J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) (hA.lk (W := fun _ => False)) hA.fk hAI.1 hY2
      (YDeadKeep.of_at (by simp [σ', updK, hqc, hqs])) (fun h => h) hd
  exact ⟨Ac, Lst', D, J.sc_frame hW hK hX' hCR' hRF' hY2 hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2))
    (J.sc_kern hW hK hA.fk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN2 hI2 (hA.cur J.cur) (hA.own J.own) (hA.off J.off) hAI (hA.bsa J.bsa)
    (hA.curRunM J.curRun) hblk hKd (J.idleW_keep hX'.fin.1.1.1 hA.fk.2.1 hA.fk.2.2).1 J.zD⟩

set_option maxHeartbeats 16000000 in
/-- **`yield_switches` at `J`** (ScYieldTo's `yield_switches_refines` with
`JAtZ` carried): the SC's thread not schedulable (nothing), of lower
priority than the caller (requeued: `JAtZ.dequeueJ`, `JAtZ.enqueueJ`), or
else the yield links (`JAtZ.linkYieldJ`), the requeues and the reschedule
(`JAtZ.reschedJ`); the spec's `return_now` computation (`yieldSwitch`)
returns the negation. Without a switch the heap is kept. -/
theorem JAtZ.yieldSwitchesJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {sc : U64} (hsc : sc ∈ Z.C) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    (hyf : x.scYieldFrom = none) {t : U64} (ht : t ∈ Z.T) (htc : x.scTcb = some t.bv)
    {ct : U64} (hct : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hyc : L.mem s (yieldA ct) = 0#u64)
    (hcs : Fl4Spec.schedulable ct.bv σ = true) :
    schedcontext.yield_switches st s sc ct ⦃ r => ∃ σ', yieldSwitch sc.bv σ = ({(!r.1, σ')}, False) ∧
      (r.1 = false → σ'.kheap = σ.kheap) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2 a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨xt, hkt, -, -, -, hpt⟩ := hs.tcb t ht
  obtain ⟨xc, hkc, -, -, -, hpc⟩ := hs.tcb ct hct
  have htw := word24_of hS hsc hk htc
  have hpre : ∀ (k : Fl4Spec.ObjRef → Bool → Fl4Spec.SMonad Unit Bool),
      (Fl4Spec.getScObjRef Fl4Spec.SchedContext.scTcb sc.bv >>= fun scTcbOpt =>
        Fl4Spec.NonDet.assertOpt scTcbOpt >>= fun tcbPtr =>
          Fl4Spec.NonDet.gets (Fl4Spec.schedulable tcbPtr) >>= fun b => k tcbPtr b) σ =
        k t.bv (Fl4Spec.schedulable t.bv σ) σ := by
    intro k
    rw [nd_bind_one (getScObjRef_eq hk _), htc,
      nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some t.bv) σ = ({(t.bv, σ)}, False)
        from rfl), nd_gets_bind]
  unfold schedcontext.yield_switches
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq, htw] at hi
  subst hi
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [schedulable_eq hR hS ht] at hb
  subst hb
  by_cases hsb : Fl4Spec.schedulable i.bv σ = true
  swap
  · simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    refine (WP.spec_ok _).mpr ⟨σ, ?_, fun _ => rfl, Ac, Lst, D, J⟩
    unfold yieldSwitch
    rw [hpre]
    simp only [hsb, Bool.false_eq_true, ↓reduceIte]; rfl
  simp only [hsb, ↓reduceIte]
  step with obj.Sc.cpu.spec as ⟨i1, hi1⟩
  have hi1' : i1 = Z.c := by rw [hi1, scCoreA_eq]; exact hS.core sc hsc
  subst hi1'
  step with LawfulStore.cur_cpu_spec as ⟨i2, hi2⟩
  rw [hc.cur] at hi2
  subst hi2
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.prio.spec as ⟨i3, hi3⟩
  step with obj.Tcb.prio.spec as ⟨i4, hi4⟩
  subst hi3 hi4
  by_cases hlt : L.mem s (prioA i) < L.mem s (prioA ct)
  · simp only [hlt, ↓reduceIte]
    refine WP.spec_bind (J.dequeueJ ht) ?_
    rintro s1 ⟨σ1, he1, Ac1, Lst1, D1, J1⟩
    obtain ⟨hk1, hr1, -⟩ := tsa_keep hkt he1
    have hsb1 : Fl4Spec.schedulable i.bv σ1 = true := by rw [schedulable_heap hk1 hr1]; exact hsb
    refine WP.spec_bind (J1.enqueueJ ht hsb1) ?_
    rintro s2 ⟨σ2, he2, Ac2, Lst2, D2, J2⟩
    obtain ⟨hk2, -, -⟩ := tsa_keep (show σ1.kheap i.bv = some (.tcb xt) by rw [hk1]; exact hkt) he2
    refine (WP.spec_ok _).mpr ⟨σ2, ?_, fun _ => hk2.trans hk1, Ac2, Lst2, D2, J2⟩
    unfold yieldSwitch
    rw [hpre]
    simp only [hsb, ↓reduceIte]
    rw [nd_gets_bind, hcur, nd_bind_one (threadGet_eq _ hkt), nd_bind_one (threadGet_eq _ hkc),
      ite_eq_left ((prio_lt_iff hpt hpc).1 hlt), nd_bind_one he1, nd_bind_one he2]; rfl
  · simp only [hlt, ↓reduceIte]
    refine WP.spec_bind (obj.Tcb.set_yield_to.spec s ct sc) ?_
    rintro s1 rfl
    refine WP.spec_bind (obj.Sc.set_yield_from.spec _ sc ct) ?_
    rintro s2 rfl
    have hpc' : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
    have hka : (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })).kheap sc.bv =
        some (.schedContext x n) := by simp [updK, hpc', hk]
    have hsf := (SFrame.ytUpd hkc (some sc.bv)).trans
      (SFrame.updSc (x' := { x with scYieldFrom := some ct.bv }) hka rfl rfl)
    have hrunc : P1.Runnable (L.mem s (P1.stA ct)) := by
      obtain ⟨hrw, -, -, -⟩ := of_decide_eq_true ((schedulable_eq hR hS hct).trans hcs)
      rw [stA_tStA]; exact hrw
    obtain ⟨AcL, LstL, DL, JL⟩ := J.linkYieldJ hct hsc hyc hkc hk hyf hrunc
      (by rw [scTcbA_eq, htw]; exact fun e => (hc.tcbs i ht).ne0 (by rw [e]; rfl))
    obtain ⟨xtL, hktL, -⟩ := hsf.tcb _ xt hkt
    obtain ⟨xcL, hkcL, -⟩ := hsf.tcb _ xc hkc
    refine WP.spec_bind (JL.dequeueJ ht) ?_
    rintro s3 ⟨σ3, he3, Ac3, Lst3, D3, J3⟩
    obtain ⟨hk3, hr3, -⟩ := tsa_keep hktL he3
    have hcs3 : Fl4Spec.schedulable ct.bv σ3 = true := by
      rw [schedulable_heap hk3 hr3]; exact hsf.schedulable hcs
    refine WP.spec_bind (J3.enqueueJ hct hcs3) ?_
    rintro s4 ⟨σ4, he4, Ac4, Lst4, D4, J4⟩
    obtain ⟨hk4, hr4, -⟩ := tsa_keep (show σ3.kheap ct.bv = some (.tcb xcL) by rw [hk3]; exact hkcL) he4
    have hsb4 : Fl4Spec.schedulable i.bv σ4 = true := by
      rw [schedulable_heap hk4 hr4, schedulable_heap hk3 hr3]; exact hsf.schedulable hsb
    refine WP.spec_bind (J4.enqueueJ ht hsb4) ?_
    rintro s5 ⟨σ5, he5, Ac5, Lst5, D5, J5⟩
    obtain ⟨s6, hr6, σ6, he6, Ac6, Lst6, D6, J6⟩ := J5.reschedJ
    rw [hr6, bind_ok]
    refine (WP.spec_ok _).mpr ⟨σ6, ?_, fun h => absurd h (by simp), Ac6, Lst6, D6, J6⟩
    unfold yieldSwitch
    rw [hpre]
    simp only [hsb, ↓reduceIte]
    rw [nd_gets_bind, hcur, nd_bind_one (threadGet_eq _ hkt), nd_bind_one (threadGet_eq _ hkc),
      ite_eq_right (fun h => hlt ((prio_lt_iff hpt hpc).2 h))]
    show (Fl4Spec.threadSet _ ct.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hkc)]
    show (Fl4Spec.updateSchedContext sc.bv _ >>= _) (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) = _
    rw [nd_bind_one (updateSchedContext_eq hka _)]
    show (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue i.bv >>= _)
      (updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv
      { x with scYieldFrom := some ct.bv } n) = _
    rw [nd_bind_one he3, nd_bind_one he4, nd_bind_one he5, nd_bind_one he6]; rfl

set_option maxHeartbeats 8000000 in
/-- `JAtZ.completeYieldJ` with the arch state kept (FL4's
`complete_yield_to` returns it unchanged). -/
theorem JAtZ.completeYieldJa (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
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
    exact ⟨trivial, σ, completeYieldTo_none hky (by rw [eyt, hi0, Notif.optRef_zero]), Z.vs, Ac, Lst, D, J⟩
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
  refine WP.spec_bind (J1.cancelYieldJ hy hm1 hi0) ?_
  rintro s2 ⟨σ2, he2, Ac2, Lst2, D2, J2⟩
  refine (WP.spec_ok _).2 ⟨rfl, σ2, ?_, V1, Ac2, Lst2, D2, J2⟩
  rw [completeYieldTo_some hky (by rw [eyt, Notif.optRef_ne hi0]), nd_bind_one he1]
  exact he2

set_option maxHeartbeats 32000000 in
/-- **FL4's `yield_to` at `J`** (module docstring; as ScYieldTo's
`yield_to_refines` with `JAtZ` carried): the SC's yielder completes its
yield (`JAtZ.completeYieldJa`; afterwards the SC is yielded from by none,
`completeYieldTo_sframe`), `resume` is a no-op (`resume_noop`), then
`yield_switches` (`JAtZ.yieldSwitchesJ`); when the call returns at once,
`set_consumed` (`JAtZ.setConsumedJ` with the message when a call, else
`JAtZ.updConsumedJ`) and `Running` (`JAtZ.runJ`). The spec's
`sched_context_yield_to` returns no data in the first case (`JAt` after it),
the consumed time in the second (`JAt` after `handle_invocation`'s reply
tail). -/
theorem JAtZ.yieldToJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
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
      ((data = [] ∧ JAt (L := L) arI AR r.1 r.2 σy) ∨
        (L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ σ2, ((), σ2) ∈ (specTail call ct.bv data σy).1 ∧
          JAt (L := L) arI AR r.1 r.2 σ2)) ⦄ := by
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
    exact (WP.spec_ok _).mpr ⟨rfl, [], σ3, by rw [hpre]; rfl, Or.inl ⟨rfl, _, _, _, _, _, _, J3⟩⟩
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
      ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s4 a σ4 ∧ Z'.T = Z.T ⦄ := by
    cases call
    · unfold schedcontext.set_consumed
      refine WP.spec_bind (J3.updConsumedJ hAT hmax htu hsc hct) ?_
      rintro ⟨cv, s4⟩ ⟨σ4, c', he4, V4, J4⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hv] at he4
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he4))
      refine (WP.spec_ok _).2 ⟨σu, ?_, _, hku, hrs1, _, Ac3, Lst3, D3, J4, rfl⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_right (by simp)]; rfl
    · refine WP.spec_mono (J3.setConsumedJ hAT hmax htu hsc hct) ?_
      rintro s4 ⟨σ4, he4, -, V4, J4⟩
      obtain ⟨v', w', he4'⟩ := Sched.setConsumed_shape hks3 hkc3
      have eσ4 := the_result he4' he4
      refine ⟨σ4, ?_, Endp.replyTcb xc1 w', by rw [eσ4]; simp [updK], hrs1, _, Ac3, Lst3, D3, J4, rfl⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_left rfl, ← hsetc]; exact he4
  refine WP.spec_bind hSC ?_
  rintro s4 ⟨σ4, hrf, y, hk4, hrs4, Z4, Ac4, Lst4, D4, J4, hZ4⟩
  have hct4 : ct ∈ Z4.T := by rw [hZ4]; exact hct
  refine WP.spec_bind (J4.runJ hct4 hk4 hrs4) ?_
  rintro s5 ⟨Lst5, D5, J5⟩
  refine (WP.spec_ok _).mpr ⟨rfl, Fl4Spec.wordsFromTime c, σu, ?_, Or.inr ⟨?_, _, ?_, _, _, _, _, _, _, J5⟩⟩
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

/-- **`XCap` from a per-outcome choice** of `DecOKDMX`'s or `DecOKRMX`'s
post (FL4's run is single-valued). -/
theorem xcap_of_or {X : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
      TopPostDMX (L := L) X σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ∨
      TopPostRMX (L := L) X σ blk call don (specDec fp slbl args ci sl c excaps buffer) ct s res ⦄) :
    XCap (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  obtain ⟨r, hr, hp⟩ := spec_exists h
  rcases hp with hp | hp
  · left; unfold DecOKDMX; rw [hr]; exact (WP.spec_ok _).2 hp
  · right; unfold DecOKRMX; rw [hr]; exact (WP.spec_ok _).2 hp

set_option maxHeartbeats 16000000 in
/-- **The SchedContext cap's YieldTo, `XCap` at `JAt`** (module docstring),
for any yielder: the fast-path flag's decode error and
`decode_sched_context_yield_to`'s checks (the SC's thread, not the caller,
priority at most the caller's MCP, the caller yielding to nothing) with `JAt`
at the start; else the spec's decode, the caller's restart
(`JAtZ.restartJ`) and `sched_context_yield_to` (`JAtZ.yieldToJ`): no data
with `JAt` after, or the consumed time with `JAt` after `handle_invocation`'s
reply tail. Named [P]: the platform's `min_budget`, `ticks_to_us`,
`getMaxTicksToUs` and `ArchTotal` (`hmb`, `hmax`, `htu`, `hAT`, as
`JSchedCtxPath`'s and `sc_consumedReplyJ`'s). -/
theorem decode_invocation_sched_context_yieldJ (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hAT : P0.ArchTotal arI)
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
    XCap (L := L) arI (JAt (L := L) arI AR) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
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
    exact Or.inl (Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, _, _, _, _, _, _, J⟩)
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
      _, _, _, _, _, _, J⟩))
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
      _, _, _, _, _, _, J⟩))
    rw [hdec]
    unfold Fl4Spec.decodeSchedContextYieldTo
    rw [hpre, wE_neg (by simp), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur, ← hte]
    exact hill _ rfl _
  have : b1 = false := Bool.eq_false_iff.2 (fun h => hte (hb1.1 h))
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hne' : t.bv ≠ ct.bv := bv_ne hte
  obtain ⟨xm, hkm, hmc⟩ := J.mcp ct hctT
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
      _, _, _, _, _, _, J⟩))
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
      _, _, _, _, _, _, J⟩))
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
  refine WP.spec_bind (J1.yieldToJ hAT hmb hmax htu hsc ht hk1 htc hctT hcur1' hkc1 rfl hyn hcs1 call) ?_
  rintro ⟨s3, a2⟩ ⟨-, data, σy, hyt, hcase⟩
  show (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ _ ⦄
  rw [WP.spec_ok]
  have hmem : (data, σy) ∈ (Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo sc.bv) σ1).1 := by
    show (data, σy) ∈ (Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ1).1
    rw [hyt]; exact Set.mem_singleton _
  rcases hcase with ⟨rfl, Z', H', Cs', Ac', Lst', D', J'⟩ | ⟨hne, σ2, htail, Z', H', Cs', Ac', Lst', D', J'⟩
  · left
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
    exact Or.inr ⟨.invokeSchedContext (.invokeSchedContextYieldTo sc.bv), DecOut.of_eq (run_liftME_ok hrun), σ1, he0,
      (.ok [], σy), mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo sc.bv))
        (s := σ1) (x := ([], σy)) hmem,
      ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ⟨_, _, _, _, _, _, J'⟩⟩
  · right
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
    exact Or.inr ⟨rfl, hne, .invokeSchedContext (.invokeSchedContextYieldTo sc.bv), DecOut.of_eq (run_liftME_ok hrun),
      σ1, he0, data, σy,
      mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo sc.bv))
        (s := σ1) (x := (data, σy)) hmem,
      ((), σ2), htail, ⟨Z'.th, Z'.G, hPl, hCR, hFI, hD, hMO⟩, ⟨_, _, _, _, _, _, J'⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The SchedContext cap with a label of no SC invocation, `XCap` at
`JAt`**: FL4's decode (`error::illegal`) and the spec's
(`decode_sched_context_invocation`'s `IllegalOperation`) both fail, the
state unchanged. Premise: the front end's label (`hlbl` [W], as every SC
label's). -/
theorem decode_invocation_sched_context_otherJ (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l44 : lbl ≠ fl4_abi.label.SchedContextConsumed) (l41 : lbl ≠ fl4_abi.label.SchedContextBind)
    (l43 : lbl ≠ fl4_abi.label.SchedContextUnbindObject) (l42 : lbl ≠ fl4_abi.label.SchedContextUnbind)
    (l45 : lbl ≠ fl4_abi.label.SchedContextYieldTo)
    {sc : U64} (sb : U64) (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 → L.mem s (scW sc 24#u64) ∈ Z.T)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  left
  have hS := J.xtop.fin.1.1.1
  have h44 : lbl.val ≠ 44 := fun h => l44 (UScalar.eq_of_val_eq (by simp [h]))
  have h41 : lbl.val ≠ 41 := fun h => l41 (UScalar.eq_of_val_eq (by simp [h]))
  have h43 : lbl.val ≠ 43 := fun h => l43 (UScalar.eq_of_val_eq (by simp [h]))
  have h42 : lbl.val ≠ 42 := fun h => l42 (UScalar.eq_of_val_eq (by simp [h]))
  have h45 : lbl.val ≠ 45 := fun h => l45 (UScalar.eq_of_val_eq (by simp [h]))
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold scLabelOf; simp [h41, h42, h43, h44, h45]
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, _, _, _, _, _, _, J⟩
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
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0)
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok]
  rw [ite_eq_right l44, ite_eq_right l41, ite_eq_right l43, ite_eq_right l42, ite_eq_right l45]
  refine illegal_ok s a _ (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err ?_, Or.inl trivial⟩,
    _, _, _, _, _, _, J⟩)
  unfold Fl4Spec.decodeSchedContextInvocation; rw [hg]; rfl

end

end

end Fl4Proofs.P3
