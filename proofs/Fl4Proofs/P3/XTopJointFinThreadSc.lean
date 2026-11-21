/-
P3 (DESIGN.md §9), TCB: **`unbind_tcb` of a thread's SC at `J`** (the SC
step of a final thread cap's `unbind_from_sc`; toward XTopJointFinThread's
`JAtZ.finThreadJ`).

* `whenResched_fields`, `unbindTcb_shape`: the spec's
  `sched_context_unbind_tcb` of an SC bound to `t` (its one outcome): `t`'s
  and the SC's links cut, the other objects, the current thread and SC, the
  time, the consumed time and the idle thread kept, the release queue
  shrinking, a reschedule pending iff `t` is the current thread (else the
  action kept).
* `unbindTcb_mid`: the mid-entry facts after it (`CurInv` unless a
  reschedule is pending, `CurOwnW`, `OffOK`, `ActIdle`, `CurRunM`) and `FK`,
  for a thread neither the idle thread nor the switch target (the current
  thread allowed: its SC, the current one, is left unowned, `CurOwnW`'s
  second case).
* `JAtZ.spec_of_words`, `JAtZ.words_of_spec`: the scheduler-action and idle
  words against the spec's at `JAtZ` (`SchedRel.act`, `idleTh`).
* `JAtZ.unbindTcbJ`: `JAtZ.sc_frame` after `unbind_tcb_refines` (`XTop` by
  `xtop_sc_step`, the relations by `ScAll.of_k`, `BlockedScActive` by
  `bk_of_tk_sk`/`skm_unbindTcb`, the dead set kept by `deadP_sc_step` with
  the link-cutting step `lkm_schedContextUnbindTcb`), P1's
  `unbind_tcb.blk` (`BlkOK`, footprint `KW`: the node-0 `DEBUG_TCBS` word
  kept, `JAtZ.kw_dbg`).
-/
import Fl4Proofs.P3.XTopFinThread
import Fl4Proofs.P3.ScFireJ
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.TcbSpecInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

/-- `when P reschedule_required` (one outcome, given `ActReady`): the heap,
the current thread and SC, the times, the idle thread and the release queue
kept; the action choose-new if `P`, else kept. -/
theorem whenResched_fields {σ : State Unit} (hA : ActReady σ) (P : Prop) [Decidable P] :
    ∃ σ1, (if P then rescheduleRequired (Z := Unit) else NonDet.pure ()) σ = ({((), σ1)}, False) ∧
      σ1.kheap = σ.kheap ∧ σ1.curThread = σ.curThread ∧ σ1.curSc = σ.curSc ∧ σ1.curTime = σ.curTime ∧
      σ1.consumedTime = σ.consumedTime ∧ σ1.idleThread = σ.idleThread ∧ σ1.idleSc = σ.idleSc ∧
      σ1.releaseQueue = σ.releaseQueue ∧
      (P → σ1.schedulerAction = .chooseNewThread) ∧ (¬ P → σ1.schedulerAction = σ.schedulerAction) := by
  by_cases hP : P
  · rw [if_pos hP]
    obtain ⟨σ1, e1, hq1, hc1⟩ := rescheduleRequired_calm hA
    obtain ⟨σ2, e2, -, -, -, ha2⟩ := resched_ok hA
    have ha1 : σ1.schedulerAction = .chooseNewThread := by rw [← the_result e1 e2]; exact ha2
    exact ⟨σ1, e1, hc1.1, hc1.2.1, hc1.2.2.1, hc1.2.2.2.1, hc1.2.2.2.2.1, hc1.2.2.2.2.2.1, hc1.isc, hq1.2.1,
      fun _ => ha1, fun h => absurd hP h⟩
  · rw [if_neg hP]
    exact ⟨σ, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h hP, fun _ => rfl⟩

/-- **The spec's `sched_context_unbind_tcb`** of an SC bound to `t` (module
docstring). -/
theorem unbindTcb_shape {σ : State Unit} {i t : ObjRef} {y : SchedContext} {n : Nat} {x : Tcb}
    (hA : ActReady σ) (hks : σ.kheap i = some (.schedContext y n)) (hy : y.scTcb = some t)
    (hkt : σ.kheap t = some (.tcb x)) :
    ∃ σ', schedContextUnbindTcb (Z := Unit) i σ = ({((), σ')}, False) ∧
      σ'.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => none) x)) ∧
      σ'.kheap i = some (.schedContext (scTcbUpdate (fun _ => none) y) n) ∧
      (∀ q, q ≠ t → q ≠ i → σ'.kheap q = σ.kheap q) ∧
      σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
      σ'.consumedTime = σ.consumedTime ∧ σ'.idleThread = σ.idleThread ∧ σ'.idleSc = σ.idleSc ∧
      (∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) ∧
      (t = σ.curThread → σ'.schedulerAction = .chooseNewThread) ∧
      (¬ t = σ.curThread → σ'.schedulerAction = σ.schedulerAction) := by
  have hts : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  unfold schedContextUnbindTcb
  rw [nd_bind_one (getSchedContext_eq hks), hy,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl),
    Notif.nd_gets_bind]
  unfold NonDet.when
  obtain ⟨σ1, he1, k1, c1, s1, t1, n1, i1, isc1, r1, a1, b1⟩ := whenResched_fields hA (t = σ.curThread)
  rw [nd_bind_one he1]
  have hkt1 : σ1.kheap t = some (.tcb x) := by rw [k1]; exact hkt
  rw [nd_bind_one (tcbSchedAction_gen hkt1 _)]
  obtain ⟨bb, h2⟩ := tcbReleaseRemove_eq (setQ σ1 x.tcbDomain x.tcbPriority
    (tcbSchedDequeue t (σ1.readyQueues x.tcbDomain x.tcbPriority))) t
  rw [nd_bind_one h2]
  set σ2 := setRel (setQ σ1 x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ1.readyQueues x.tcbDomain x.tcbPriority)))
    ((setQ σ1 x.tcbDomain x.tcbPriority
      (tcbSchedDequeue t (σ1.readyQueues x.tcbDomain x.tcbPriority))).releaseQueue.filter fun u => decide (t ≠ u)) bb
    with hσ2
  have hk2 : σ2.kheap = σ.kheap := k1
  have hkt2 : σ2.kheap t = some (.tcb x) := by rw [hk2]; exact hkt
  rw [nd_bind_one (show setTcbObjRef (Z := Unit) tcbSchedContextUpdate t none σ2 = _ from threadSet_eq _ hkt2)]
  have hks3 : (updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))).kheap i = some (.schedContext y n) := by
    simp only [updK, Function.update_of_ne (Ne.symm hts)]; rw [hk2]; exact hks
  have e4 : setScObjRef (Z := Unit) scTcbUpdate i none (updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))) =
      ({((), updSc (updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))) i
        (scTcbUpdate (fun _ => none) y) n)}, False) := updateSchedContext_eq hks3 _
  rw [e4]
  have hrq : ∀ u ∈ σ2.releaseQueue, u ∈ σ.releaseQueue := fun u hu => by
    have hu' : u ∈ σ1.releaseQueue.filter (fun u => decide (t ≠ u)) := hu
    rw [← r1]; exact (List.mem_filter.1 hu').1
  refine ⟨_, rfl, ?_, ?_, fun q hq1 hq2 => ?_, c1, s1, t1, n1, i1, isc1, hrq, a1, b1⟩
  · simp [updSc, updK, hts]
  · simp [updSc, updK]
  · simp only [updSc, updK, Function.update_of_ne hq1, Function.update_of_ne hq2]; rw [hk2]

/-- **The mid-entry facts after `sched_context_unbind_tcb`** (module
docstring). -/
theorem unbindTcb_mid {T C : Set U64} {σ σ' : State Unit} {i t : ObjRef} {y : SchedContext} {n : Nat} {x : Tcb}
    (hI : Inv σ) (hks : σ.kheap i = some (.schedContext y n)) (hy : y.scTcb = some t)
    (hkt : σ.kheap t = some (.tcb x)) (hxs : x.tcbSchedContext = some i) (hiC : ∃ q ∈ C, UScalar.bv q = i)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t) (hid : t ≠ σ.idleThread)
    (hcur : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (hown : CurOwnW T C σ) (hoff : OffOK σ)
    (hact : ActIdle σ) (hcr : CurRunM σ)
    (he : schedContextUnbindTcb (Z := Unit) i σ = ({((), σ')}, False)) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW T C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
      CurRunM σ' ∧ FK σ σ' := by
  obtain ⟨σ2, e2, kt, ki, ko, ct, cs, tm, cn, hidl, hisc, rq, a1, b1⟩ := unbindTcb_shape hI.actReady hks hy hkt
  have e := the_result e2 he
  subst e
  have hti : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  -- objects of other kinds than `t`'s and `i`'s
  have nTi : ∀ q (z : Tcb), σ.kheap q = some (.tcb z) → q ≠ i := by
    rintro q z hq rfl; rw [hks] at hq; cases hq
  have nSt : ∀ q (z : SchedContext) m, σ.kheap q = some (.schedContext z m) → q ≠ t := by
    rintro q z m hq rfl; rw [hkt] at hq; cases hq
  -- `ActIdle`
  have hidi : σ.idleThread ≠ i := by obtain ⟨xi, h1, -⟩ := hact.2; exact nTi _ _ h1
  have hIdle : IdleOK σ' := IdleOK.of hact.2 hidl (ko _ (Ne.symm hid) hidi) (fun h => rq _ h)
  have hAct : ActIdle σ' := by
    refine ⟨fun u hu => ?_, hIdle⟩
    by_cases htc : t = σ.curThread
    · rw [a1 htc] at hu; cases hu
    rw [b1 htc] at hu
    obtain ⟨xu, scp, yu, nu, hku, hsc, hrun, hky, hac, hnr⟩ := schedulable_inv (hact.1 u hu)
    have hut : u ≠ t := hsa u hu
    have hui : u ≠ i := nTi _ _ hku
    have hst : scp ≠ t := nSt _ _ _ hky
    have hsi : scp ≠ i := by
      rintro rfl
      obtain ⟨y1, n1, h1, h2⟩ := hI.back u xu scp hku hsc
      rw [hks] at h1; cases h1; rw [hy] at h2; cases h2; exact hut rfl
    exact schedulable_of (by rw [ko _ hut hui]; exact hku) hsc hrun (by rw [ko _ hst hsi]; exact hky) hac
      (fun h => hnr (rq _ h))
  refine ⟨?_, ?_, ?_, hAct, ?_, ⟨cs, hidl, hisc⟩⟩
  · -- `CurInv` unless a reschedule is pending
    by_cases htc : t = σ.curThread
    · exact Or.inl (a1 htc)
    rcases hcur with h | hC
    · exact Or.inl (by rw [b1 htc]; exact h)
    right
    obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
    obtain ⟨y1, n1, hk1⟩ := hC.sc
    have hct : σ.curThread ≠ t := fun e => htc e.symm
    have hci : σ.curThread ≠ i := nTi _ _ hkc
    have hcst : σ.curSc ≠ t := nSt _ _ _ hk1
    have hcsi : σ.curSc ≠ i := by
      rintro e
      obtain ⟨y2, n2, h1, h2⟩ := hI.back _ xt _ hkc hcs
      rw [e, hks] at h1; cases h1; rw [hy] at h2; cases h2; exact htc rfl
    refine ⟨⟨xt, by rw [ct, ko _ hct hci]; exact hkc, by rw [cs]; exact hcs, hnb⟩, ⟨y1, n1, by rw [cs, ko _ hcst hcsi]; exact hk1⟩,
      fun hne y3 n3 h3 => ?_, fun h => hC.notRel (by rw [ct] at h; exact rq _ h)⟩
    rw [cs, hisc] at hne; rw [cs] at h3; rw [ko _ hcst hcsi] at h3
    exact hC.active hne y3 n3 h3
  · -- `CurOwnW`
    rcases hown with ⟨u, hu, xt, hku, hxt, hown, hnr⟩ | ⟨hcs, hun⟩
    · by_cases hut : UScalar.bv u = t
      · have hku' : σ.kheap t = some (.tcb xt) := by rw [← hut]; exact hku
        rw [hkt] at hku'; cases hku'
        rw [hxs] at hxt; cases hxt
        refine Or.inr ⟨by rw [cs]; exact hiC, fun x' n' h => ?_⟩
        rw [cs, ki] at h; cases h; rfl
      · have hui : UScalar.bv u ≠ i := nTi _ _ hku
        obtain ⟨y1, n1, hk1, -⟩ := hI.back _ xt _ hku hxt
        have hcst : σ.curSc ≠ t := nSt _ _ _ hk1
        have hcsi : σ.curSc ≠ i := by
          rintro e
          have := hown y1 n1 hk1
          rw [e, hks] at hk1; cases hk1; rw [hy] at this; cases this; exact hut rfl
        exact Or.inl ⟨u, hu, xt, by rw [ko _ hut hui]; exact hku, by rw [cs]; exact hxt,
          fun x' n' h => hown x' n' (by rw [cs, ko _ hcst hcsi] at h; exact h),
          fun h0 hm => hnr (by rw [← cn]; exact h0) (rq _ hm)⟩
    · refine Or.inr ⟨by rw [cs]; exact hcs, fun x' n' h => ?_⟩
      rw [cs] at h
      by_cases e : σ.curSc = i
      · rw [e, ki] at h; cases h; rfl
      by_cases e2 : σ.curSc = t
      · rw [e2, kt] at h; cases h
      rw [ko _ e2 e] at h; exact hun _ _ h
  · -- `OffOK`
    intro h0 y1 n1 h1 ha
    rw [cn] at h0 ⊢; rw [tm]
    rw [cs] at h1; rw [cs, hisc] at ha
    by_cases e : σ.curSc = i
    · rw [e, ki] at h1; cases h1
      exact hoff h0 y n (by rw [e]; exact hks) ha
    by_cases e2 : σ.curSc = t
    · rw [e2, kt] at h1; cases h1
    rw [ko _ e2 e] at h1
    exact hoff h0 y1 n1 h1 ha
  · -- `CurRunM`
    by_cases htc : t = σ.curThread
    · exact Or.inl (act_cn_nr (a1 htc))
    rcases hcr with h | h | h
    · exact Or.inl (by rw [b1 htc]; exact h)
    · refine Or.inr (Or.inl fun x' hx' => ?_)
      rw [ct] at hx'
      by_cases e : σ.curThread = i
      · rw [e, ki] at hx'; cases hx'
      rw [ko _ (fun e' => htc e'.symm) e] at hx'
      exact h x' hx'
    · exact Or.inr (Or.inr (by rw [ct, hidl]; exact h))

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- `KW` with no endpoint words is inside `KW` with any. -/
theorem kw_empty_mono {T' Cs' Sg Scs : Set U64} {Zf : U64 → Nat} {s0 : S} {b : U64}
    (h : P1.KW st T' Cs' Sg Scs Zf ∅ s0 b) (E : Set U64) : P1.KW st T' Cs' Sg Scs Zf E s0 b := by
  rcases h with h | h | h | h | ⟨e, he, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · simp at he

/-- **The action and idle words at `JAtZ` against the spec's**: a TCB `t`
neither word is not the spec's switch target nor its idle thread. -/
theorem JAtZ.spec_of_words (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64}
    (hna : L.actionW s ≠ t) (hid : L.idleW s ≠ t) :
    (∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) ∧ t.bv ≠ σ.idleThread := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ea : L.actionW s = nodeW st s Z.c layout.node.SCHED_ACTION := by
    unfold P1.LawfulStore.actionW nodeW; rw [hc.cur]
  have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  refine ⟨fun u hu e => ?_, fun e => ?_⟩
  · have h := hS.act
    rw [hu] at h
    obtain ⟨-, -, hw⟩ := h
    apply hna; rw [ea]; apply P1.eq_of_bv
    rw [hw, e]
  · apply hid; rw [ei]; apply P1.eq_of_bv; rw [← hs.idleTh, ← e]

/-- The converse of `JAtZ.spec_of_words` for a TCB of the set. -/
theorem JAtZ.words_of_spec (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    L.actionW s ≠ t ∧ L.idleW s ≠ t := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ea : L.actionW s = nodeW st s Z.c layout.node.SCHED_ACTION := by
    unfold P1.LawfulStore.actionW nodeW; rw [hc.cur]
  have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  have ta := hc.tcbs t ht
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h := hS.act
    rw [← ea, e] at h
    cases ha : σ.schedulerAction with
    | resumeCurThread =>
      rw [ha] at h
      have h0 : t = 0#u64 := h
      exact ta.ne0 (by rw [h0]; rfl)
    | chooseNewThread =>
      rw [ha] at h
      have h1 : t = 1#u64 := h
      have hv : t.val = 1 := by rw [h1]; rfl
      have := ta.align
      rw [hv] at this; norm_num at this
    | switchThread u =>
      rw [ha] at h
      exact hsa u ha h.2.2.symm
  · apply hid; rw [hs.idleTh, ← ei, e]

set_option maxHeartbeats 8000000 in
/-- **`unbind_tcb` of a thread's SC at `J`** (module docstring), for a
thread neither the idle thread nor the switch target. -/
theorem JAtZ.unbindTcbJD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t i : U64} {x : Fl4Spec.Tcb}
    (ht : t ∈ Z.T) (hiC : i ∈ Z.C) (hk : σ.kheap t.bv = some (.tcb x)) (hsp : x.tcbSchedContext = some i.bv)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    schedcontext.unbind_tcb st s i ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindTcb (Z := Unit) i.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y, n, hky, -⟩ := hs.scs i hiC
  obtain ⟨y', n', hky', hyt⟩ := J.inv.back t.bv x i.bv hk hsp
  rw [hky] at hky'; cases hky'
  have hw24 : L.mem s (P1.scTcbA i) = t := by rw [scTcbA_eq]; exact word24_of hS hiC hky hyt
  obtain ⟨hna, hidle⟩ := J.words_of_spec ht hsa hid
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hiS : i ∈ P1.Heap.scs H := ⟨_, (hJ.sc i y n (J.c0 i hiC) hky).2⟩
  refine WP.spec_mono (WP.spec_and (unbind_tcb_refines s σ hS hR J.nsc J.inv hiC hky ht hyt)
    (P1.schedcontext.unbind_tcb.blk s i J.blk hiS (J.c0 i hiC) (fun _ => by rw [hw24]; exact hna)
      (fun _ => by rw [hw24]; exact hidle))) ?_
  rintro s' ⟨⟨σ', he, hS', hR', hN', hI', -, hw5, -⟩, hP1⟩
  have hblk := hP1.1
  have hfoot := hP1.2.1
  have hm : ((), σ') ∈ (Fl4Spec.schedContextUnbindTcb (Z := Unit) i.bv σ).1 := by
    rw [he]; exact Set.mem_singleton _
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) :=
    Sched.WritesIn.kfoot_of_sfoot_scw hS hiC (K := 24#u64) (by simp) (by simp) (by decide) hw5
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWk
  have hK : ScTKw (fun _ => False) σ σ' := nkt_schedContextUnbindTcb i.bv σ ((), σ') hm
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    xtop_sc_step (ct := σ.curThread) hX J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hall := ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree
    ⟨⟨hS', hR', hN', hI'⟩, hWk, (pres_schedContextUnbindTcb (true, true) _).of_eq he⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  obtain ⟨hcur', hown', hoff', hact', hcr', hF⟩ := unbindTcb_mid (T := Z.T) J.inv hky hyt hk hsp ⟨i, hiC, rfl⟩
    hsa hid J.cur J.own J.off J.act J.curRun he
  have hB' : BlockedScActive σ' :=
    J.bsa.bk (bk_of_tk_sk hK (skm_unbindTcb _ σ _ hm)) ((pres_schedContextUnbindTcb (true, true) _).of_eq he)
  have hL : LK (fun _ => False) σ σ' := lkm_schedContextUnbindTcb (W := fun _ => False) i.bv σ _ hm
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) hL hF hact'.1 hY'
      ((((pres_schedContextUnbindTcb (true, true) _).of_eq he).ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg (hfoot.mono (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (hfoot.mono (Set.empty_subset _))
  exact ⟨σ', he, Ac, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2)) (J.sc_kern hW hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN' hI' hcur' hown' hoff' hact' hB' hcr' hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩

/-- `unbindTcbJD` with the dead set existential. -/
theorem JAtZ.unbindTcbJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t i : U64} {x : Fl4Spec.Tcb}
    (ht : t ∈ Z.T) (hiC : i ∈ Z.C) (hk : σ.kheap t.bv = some (.tcb x)) (hsp : x.tcbSchedContext = some i.bv)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    schedcontext.unbind_tcb st s i ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindTcb (Z := Unit) i.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ' ⦄ :=
  WP.spec_mono (J.unbindTcbJD ht hiC hk hsp hsa hid) fun _ ⟨σ', he, Ac', Lst', J'⟩ => ⟨σ', he, Ac', Lst', D, J'⟩

end

end

end Fl4Proofs.P3
