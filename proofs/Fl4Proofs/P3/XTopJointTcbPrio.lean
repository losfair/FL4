/-
P3 (DESIGN.md §9), TCB: **the SetPriority label of the Thread cap at `J`**.

* `requeue_irelW`, `prio_run_irelW`, `set_priority_irelW`: IpcSetPrio's
  `requeue_irel`, `prio_run_irel`, `set_priority_irel` with FL4's footprint
  `CnW` (IpcSignalBound): the scheduler's words (`SFootI`), the target's
  priority word, the reordered endpoint's words and its queue's links
  (`ep_reorder_full`), the reordered notification's writes (`NWrite`,
  `ntfn_reorder_full`).
-/
import Fl4Proofs.P3.XTopJointTcbSched
import Fl4Proofs.P3.TcbPrioFr
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`requeue_irel` with its footprint** (module docstring). -/
theorem requeue_irelW (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) (v : U64) (hv : v.val < 256)
    (hA : ActReady σ) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 v
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue t.bv
        Fl4Spec.threadSetPriority (Z := Unit) t.bv (specPrio v)
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv
        Fl4Spec.rescheduleRequired (Z := Unit)) σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
  have cS : ∀ (s' : S), L.ksb s' = L.ksb s → ∀ b, SFootI st T c s' b → CnW (st := st) T N C E R c s σ b :=
    fun s' hk' b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hk').1 (sfootI_sfoot hb))))
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  refine WP.spec_bind (WP.spec_and (WP.spec_and (dequeue_refines s σ hS t ht) (dequeue_sfootI hS ht))
    (sched.dequeue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) (hc.queued t ht).1)) ?_
  rintro s1 ⟨⟨⟨σ1, he1, -, -, -, hS1⟩, hw1⟩, -, hinq1⟩
  obtain ⟨x0, hkx0, -⟩ := hX.1.tcb t ht
  have hA1 : ActReady σ1 := by
    have he1' := he1
    rw [tcbSchedAction_gen hkx0] at he1'
    rw [pair_eq he1']
    exact actReady_upd hA hkx0 rfl rfl (Function.update_eq_self_iff.2 hkx0.symm).symm rfl rfl rfl
  have hX1 := sc_step_lift hP0 hX (hw1.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he1) hS1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [hinq1]; split_ifs with h
    · exact andn_qq_qq _
    · exact not_not.1 h
  have hrel1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [hinq1]; split_ifs
    · rw [andn_qq_qr]; exact hr0
    · exact hr0
  step with P1.obj.Tcb.set_prio.spec as ⟨s2, hs2⟩
  subst hs2
  obtain ⟨x1, hkx1, -⟩ := hX1.1.tcb t ht
  have hX2 := prio_wr_irel hP0 hX1 ht hkx1 hq1 v hv
  have hta := hc.tcbs t ht
  have hinq2 : L.mem (L.wr s1 (prioA t) v) (inqA t) = L.mem s1 (inqA t) :=
    rd_wr_ne (a_prio hta).1 (field_aligned hta (by simp) (by simp)) (fun e => by
      have := congrArg UScalar.val e; rw [val_prio hta, inqA_eq, tfield_val hta (by simp)] at this; simp at this)
  have hS2 := hX2.2.2.1
  refine WP.spec_bind (WP.spec_and (enqueue_refines _ _ hS2 t ht (fun _ => by rw [hinq2]; exact hrel1))
    (enqueue_sfootI hS2 ht)) ?_
  rintro s3 ⟨⟨σ3, he3, -, -, -, hS3⟩, hw3⟩
  have hA3 : ActReady σ3 := by
    have hk2 : (updK σ1 t.bv (.tcb { x1 with tcbPriority := specPrio v })).kheap t.bv =
        some (.tcb { x1 with tcbPriority := specPrio v }) := by simp [updK]
    have hA2 := actReady_upd (σ' := updK σ1 t.bv (.tcb { x1 with tcbPriority := specPrio v })) (y := { x1 with tcbPriority := specPrio v }) hA1 hkx1 rfl rfl
      rfl rfl rfl rfl
    have he3' := he3
    rw [tcbSchedAction_gen hk2] at he3'
    rw [pair_eq he3']
    exact actReady_upd hA2 hk2 rfl rfl (Function.update_eq_self_iff.2 hk2.symm).symm rfl rfl rfl
  have hX3 := sc_step_lift hP0 hX2 (hw3.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he3) hS3
  refine WP.spec_mono (WP.spec_and (reschedule_required_refines s3 σ3 hX3.1.toN hS3 hA3)
    (reschedule_required_sfootI hS3)) ?_
  rintro s4 ⟨⟨σ4, he4, -, -, -, hS4⟩, hw4⟩
  have hX4 := sc_step_lift hP0 hX3 (hw4.mono fun _ h => Or.inr h) (NKS.of_eq nks_rescheduleRequiredI he4) hS4
  have hpw : WritesIn st s1 (L.wr s1 (prioA t) v) (· = prioA t) := writesIn_wr (a_prio hta).1
  have hk1 : L.ksb s1 = L.ksb s := hw1.1
  have hk2 : L.ksb (L.wr s1 (prioA t) v) = L.ksb s := hpw.1.trans hk1
  have hk3 : L.ksb s3 = L.ksb s := hw3.1.trans hk2
  refine ⟨σ4, ?_, hX4, (((hw1.trans hpw).trans hw3).trans hw4).mono fun b hb => ?_⟩
  swap
  · rcases hb with ((h1 | h2) | h3) | h4
    · exact cS s rfl b h1
    · exact Or.inl (Or.inr ⟨t, ht, 3448, by omega, by omega, by omega, by omega, by omega, by rw [h2, val_prio hta]⟩)
    · exact cS _ hk2 b h3
    · exact cS _ hk3 b h4
  rw [nd_bind_one he1]
  show (Fl4Spec.threadSet _ t.bv >>= _) σ1 = _
  rw [nd_bind_one (threadSet_eq _ hkx1), nd_bind_one he3]
  exact he4


set_option maxHeartbeats 8000000 in
/-- **`prio_run_irel` with its footprint** (module docstring). -/
theorem prio_run_irelW (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true) (v : U64) (hv : v.val < 256)
    (hAc : ActReady σ)
    (hRel : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue) :
    (do
      let b ← sched.queued st s t
      if b then do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 v
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3
      else do
        let t1 ← sched.cur_thread st s
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
        if b1 then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 v
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else obj.Tcb.set_prio st t s v) ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hta0 := hP0.e.tcb t ht
  have hpw : WritesIn st s (L.wr s (prioA t) v) (· = prioA t) := writesIn_wr (a_prio hta0).1
  have cP : ∀ b, b = prioA t → CnW (st := st) T N C E R c s σ b := fun b hb =>
    Or.inl (Or.inr ⟨t, ht, 3448, by omega, by omega, by omega, by omega, by omega, by rw [hb, val_prio hta0]⟩)
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x', hk', hd0, -, -, hpr⟩ := hs.tcb t ht
  rw [hk] at hk'; cases hk'
  have hp := hc.prio t ht
  have hprio : x.tcbPriority = specPrio (L.mem s (prioA t)) := (specPrio_eq hpr).symm
  have hrq : σ.readyQueues x.tcbDomain x.tcbPriority = (Q (L.mem s (prioA t))).map UScalar.bv := by
    rw [hd0, hprio]; exact hs.rq _ hp
  have hrel0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ↔ t.bv ∉ σ.releaseQueue := by
    rw [hs.rel, mem_map_bv]
    constructor
    · intro h0 hm; exact (hc.released t ht).2 hm h0
    · intro hn; by_contra h0; exact hn ((hc.released t ht).1 h0)
  have req : (σ.curThread = t.bv ∨ t.bv ∈ σ.readyQueues x.tcbDomain x.tcbPriority) →
      (do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 v
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3) ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
    intro hcq
    have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      rw [hrel0]
      rcases hcq with h | h
      · exact hRel h
      · intro hm
        rw [hrq, mem_map_bv] at h
        rw [hs.rel, mem_map_bv] at hm
        exact hc.excl t ht h hm
    refine WP.spec_mono (requeue_irelW hP0 hX ht hr0 v hv hAc) ?_
    rintro s' ⟨σ', he, hX', hW'⟩
    refine ⟨σ', ?_, hX', hW'⟩
    rw [setPriority_run hk hrun, if_pos (hcq.elim (fun h => Or.inr h.symm) Or.inl), ucast8_specPrio]
    exact he
  step with P1.sched.queued.spec as ⟨b, hb⟩
  subst hb
  by_cases hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · simp only [hq, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    refine req (Or.inr ?_)
    rw [hrq, mem_map_bv]; exact (hc.queued t ht).1 hq
  · simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte]
    step with P1.sched.cur_thread.spec as ⟨t1, ht1⟩
    subst ht1
    unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
    simp only [bind_ok]
    have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
      rw [hs.curThread, hc.cur]; rfl
    by_cases e : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    · simp only [e, decide_true, ↓reduceIte]
      rw [← e]
      exact req (Or.inl (by rw [hcur, ← e]))
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      step with P1.obj.Tcb.set_prio.spec as ⟨s2, hs2⟩
      subst hs2
      refine ⟨_, ?_, prio_wr_irel hP0 hX ht hk (not_not.1 hq) v hv, hpw.mono cP⟩
      rw [setPriority_run hk hrun, if_neg ?_, ucast8_specPrio]
      · show Fl4Spec.threadSet _ t.bv σ = _
        rw [threadSet_eq _ hk]
      · rintro (h | h)
        · rw [hrq, mem_map_bv] at h
          exact hq ((hc.queued t ht).2 h)
        · rw [hcur] at h; exact e (eq_of_bv h)


set_option maxHeartbeats 16000000 in
/-- **`set_priority_irel` with its footprint** (module docstring). -/
theorem set_priority_irelW (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) (v : U64) (hv : v.val < 256)
    (hAc : ActReady σ)
    (hRel : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue) (hSV : SchedValid σ) (hInv : Inv σ)
    (hOC : ObjCover N T E R C σ) (hSE : QSorted st T E s) (hSN : QSorted st T N s) :
    sched.set_priority st s t v ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hP := hP0.e
  have hT := hP.tcb
  have hta := hT t ht
  obtain ⟨x, hk, hxe⟩ := hX.1.toE.tcb t ht
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hpa := (a_prio hta).1
  have hpv := val_prio hta
  have hA : ∀ b, Aligned b → b.val ≠ t.val + 3448 → L.mem (L.wr s (prioA t) v) b = L.mem s b :=
    fun b hb h => rd_wr_ne hpa hb (fun e => h (by rw [← e, hpv]))
  -- the footprint
  have cP : ∀ b, b = prioA t → CnW (st := st) T N C E R c s σ b := fun b hb =>
    Or.inl (Or.inr ⟨t, ht, 3448, by omega, by omega, by omega, by omega, by omega, by rw [hb, hpv]⟩)
  have hpw : WritesIn st s (L.wr s (prioA t) v) (· = prioA t) := writesIn_wr hpa
  -- a thread that is not runnable is in no ready queue
  have hnq : Fl4Spec.runnable x.tcbState = false → (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    intro hr
    by_contra hq
    have hm := (hc.queued t ht).1 hq
    have hin : t.bv ∈ σ.readyQueues 0 (specPrio (L.mem s (prioA t))) := by
      rw [hs.rq _ (hc.prio t ht), mem_map_bv]; exact hm
    obtain ⟨x2, scp, y2, n2, hk2, -, hr2, -, -⟩ := hInv.rq _ _ _ hin
    rw [hk] at hk2; cases hk2; rw [hr] at hr2; cases hr2
  -- the plain priority write
  have plain : Fl4Spec.runnable x.tcbState = false → Fl4Spec.epBlocked x.tcbState = none →
      Fl4Spec.ntfnBlocked x.tcbState = none →
      obj.Tcb.set_prio st t s v ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
    intro hr he hn
    step with P1.obj.Tcb.set_prio.spec as ⟨s2, hs2⟩
    subst hs2
    refine ⟨_, ?_, prio_wr_irel hP0 hX ht hk (hnq hr) v hv, hpw.mono cP⟩
    rw [setPriority_blk hk hr, ucast8_specPrio]
    show (Fl4Spec.threadSet _ t.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hk), he, hn]
    show ((pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) >>= fun _ =>
      (pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit)) _ = _
    rw [nd_pure_bind']
    rfl
  -- the endpoint reorder
  have epB : ∀ e : Fl4Spec.ObjRef, Fl4Spec.runnable x.tcbState = false → Fl4Spec.epBlocked x.tcbState = some e →
      Fl4Spec.ntfnBlocked x.tcbState = none →
      (∃ xe, σ.kheap e = some (.endpoint xe) ∧ t.bv ∈ xe.epQueue) →
      (do
        let s1 ← obj.Tcb.set_prio st t s v
        let i ← obj.Tcb.block_obj st t s1
        endpoint.reorder_ep st s1 i t) ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
    intro e hr he hn ⟨xe, hke, htq⟩
    step with P1.obj.Tcb.set_prio.spec as ⟨s1, hs1⟩
    subst hs1
    step with P1.obj.Tcb.block_obj.spec as ⟨w, hw⟩
    subst hw
    have hwv : L.mem (L.wr s (prioA t) v) (blockA t) = L.mem s (tBlockA t) :=
      hA _ (a_blk hta).1 (by show (tBlockA t).val ≠ _; rw [val_blk hta]; omega)
    rw [hwv]
    have hwe : (L.mem s (tBlockA t)).bv = e := hxe.blk e he
    obtain ⟨e', he', ee'⟩ := hOC.ep e xe hke
    have hw' : L.mem s (tBlockA t) = e' := eq_of_bv (hwe.trans ee'.symm)
    rw [hw']
    subst ee'
    have hX1 := prio_wr_irel hP0 hX ht hk (hnq hr) v hv
    have het : e'.bv ≠ t.bv := fun h => by rw [h, hk] at hke; cases hke
    have hke1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap e'.bv = some (.endpoint xe) := by
      simp [updK, het, hke]
    have hkt1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap t.bv =
        some (.tcb { x with tcbPriority := specPrio v }) := by simp [updK]
    have hsort : ∀ xs, QueueRel (L.mem (L.wr s (prioA t) v)) T .Ep (qOf (L.mem (L.wr s (prioA t) v)) e') xs →
        PrioSorted (fun y => L.mem (L.wr s (prioA t) v) (prioA y)) (xs.erase t) := by
      intro xs hq
      have hq0 := qrel_prio_back hT ht hA ⟨(a_head hP he').1, by rw [val_head]; have := hP.et e' he' t ht; omega⟩
        ⟨(a_ts hP he').1, by rw [val_ts hP he']; have := hP.et e' he' t ht; omega⟩ hq
      have hs0 : PrioSorted _ (xs.erase t) := (hSE e' he' xs hq0).sublist (List.erase_sublist (a := t))
      refine prioSorted_congr hs0 fun y hy => ?_
      have hyt : y ≠ t := fun h => hq0.nodup.not_mem_erase (h ▸ hy)
      have hya := hT y (hq0.mem y (List.mem_of_mem_erase hy))
      refine hA _ (a_prio hya).1 ?_
      rw [val_prio hya]
      have a1 := hta.align; have a2 := hya.align
      have := val_ne_of_ne hyt
      have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
      rw [h12] at a1 a2; omega
    obtain ⟨xs, hQ, hxs, -⟩ := (hX1.1.toE.at_ep he' hke1).queue
    have htxs : t ∈ xs := by
      rw [hxs] at htq; obtain ⟨y, hy, ey⟩ := List.mem_map.1 htq; rw [← eq_of_bv ey]; exact hy
    refine WP.spec_mono (WP.spec_and (ep_reorder_irel hP0 _ _ hX1 ht hkt1 he' hke1 htq hsort)
      (ep_reorder_full hP _ he' t xs hQ htxs)) ?_
    rintro s' ⟨⟨σ', hm, hX'⟩, -, -, hQA, hWE⟩
    have hW2 : WritesIn st (L.wr s (prioA t) v) s' (fun b => EW e' b ∨ ∃ w ∈ xs, TL w b) :=
      ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
    refine ⟨σ', ?_, hX', (hpw.trans hW2).mono fun b hb => ?_⟩
    swap
    · rcases hb with h | h | ⟨w, hw, h | h⟩
      · exact cP b h
      · exact Or.inr (Or.inl ⟨e', he', h⟩)
      · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
      · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
    rw [setPriority_blk hk hr, ucast8_specPrio]
    show (Fl4Spec.threadSet _ t.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hk), he, hn]
    show (Fl4Spec.reorderEp e'.bv t.bv >>= _) _ = _
    rw [nd_bind_one hm]
    rfl
  -- the notification reorder
  have ntB : ∀ n : Fl4Spec.ObjRef, Fl4Spec.runnable x.tcbState = false → Fl4Spec.epBlocked x.tcbState = none →
      Fl4Spec.ntfnBlocked x.tcbState = some n →
      (∃ xn, σ.kheap n = some (.notification xn) ∧ t.bv ∈ Fl4Spec.ntfnQueueOf xn) →
      (do
        let s1 ← obj.Tcb.set_prio st t s v
        let i ← obj.Tcb.block_obj st t s1
        notification.reorder_ntfn st s1 i t) ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
    intro n hr he hn ⟨xn, hkn, htq⟩
    step with P1.obj.Tcb.set_prio.spec as ⟨s1, hs1⟩
    subst hs1
    step with P1.obj.Tcb.block_obj.spec as ⟨w, hw⟩
    subst hw
    have hwv : L.mem (L.wr s (prioA t) v) (blockA t) = L.mem s (tBlockA t) :=
      hA _ (a_blk hta).1 (by show (tBlockA t).val ≠ _; rw [val_blk hta]; omega)
    rw [hwv]
    obtain ⟨x1, hk1, hx1⟩ := hX.1.toN.tcb t ht
    rw [hk] at hk1; cases hk1
    have hwn : (L.mem s (tBlockA t)).bv = n := by
      cases hts : x.tcbState <;> simp [hts, Fl4Spec.ntfnBlocked] at hn
      subst hn; exact hx1.blk _ hts
    obtain ⟨n', hn', en'⟩ := hOC.ntfn n xn hkn
    have hw' : L.mem s (tBlockA t) = n' := eq_of_bv (hwn.trans en'.symm)
    rw [hw']
    subst en'
    have hX1 := prio_wr_irel hP0 hX ht hk (hnq hr) v hv
    have hnt : n'.bv ≠ t.bv := fun h => by rw [h, hk] at hkn; cases hkn
    have hkn1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap n'.bv = some (.notification xn) := by
      simp [updK, hnt, hkn]
    have hkt1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap t.bv =
        some (.tcb { x with tcbPriority := specPrio v }) := by simp [updK]
    obtain ⟨q, hwq⟩ : ∃ q, xn.ntfnObj = .waitingNtfn q := by
      cases h : xn.ntfnObj with
      | idleNtfn => simp [Fl4Spec.ntfnQueueOf, h, Fl4Spec.Ntfn.ntfnQueue] at htq
      | activeNtfn b => simp [Fl4Spec.ntfnQueueOf, h, Fl4Spec.Ntfn.ntfnQueue] at htq
      | waitingNtfn q => exact ⟨q, rfl⟩
    have htq' : t.bv ∈ q := by simpa [Fl4Spec.ntfnQueueOf, hwq, Fl4Spec.Ntfn.ntfnQueue] using htq
    have hna := hP0.n.ntfn n' hn'
    have hsort : ∀ xs, QueueRel (L.mem (L.wr s (prioA t) v)) T .Ep (qOf (L.mem (L.wr s (prioA t) v)) n') xs →
        PrioSorted (fun y => L.mem (L.wr s (prioA t) v) (prioA y)) (xs.erase t) := by
      intro xs hq
      have hdisj := hP0.n.disj n' hn' t ht
      have hq0 := qrel_prio_back hT ht hA
        ⟨(foot_head hP0.n hn').1, by have := (nw_words hP0 hn').1; unfold NW at this; omega⟩
        ⟨(foot_ts hP0.n hn').1, by have := (nw_words hP0 hn').2.1; unfold NW at this; omega⟩ hq
      have hs0 : PrioSorted _ (xs.erase t) := (hSN n' hn' xs hq0).sublist (List.erase_sublist (a := t))
      refine prioSorted_congr hs0 fun y hy => ?_
      have hyt : y ≠ t := fun h => hq0.nodup.not_mem_erase (h ▸ hy)
      have hya := hT y (hq0.mem y (List.mem_of_mem_erase hy))
      refine hA _ (a_prio hya).1 ?_
      rw [val_prio hya]
      have a1 := hta.align; have a2 := hya.align
      have := val_ne_of_ne hyt
      have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
      rw [h12] at a1 a2; omega
    obtain ⟨xs, hQ, hxs, -⟩ := (hX1.1.toN.at_ntfn hn' hkn1).obj.queue
    have htxs : t ∈ xs := by
      have : t.bv ∈ xn.ntfnObj.ntfnQueue := htq
      rw [hxs] at this; obtain ⟨y, hy, ey⟩ := List.mem_map.1 this; rw [← eq_of_bv ey]; exact hy
    refine WP.spec_mono (WP.spec_and (ntfn_reorder_irel hP0 _ _ hX1 ht hkt1 hn' hkn1 hwq htq' hsort)
      (ntfn_reorder_full hP0.n _ hn' t xs hQ htxs)) ?_
    rintro s' ⟨⟨σ', hm, hX'⟩, -, -, hA3⟩
    refine ⟨σ', ?_, hX', (hpw.trans hA3.foot).mono fun b hb => hb.elim (cP b) fun h => Or.inl (NWrite.finW hT h)⟩
    rw [setPriority_blk hk hr, ucast8_specPrio]
    show (Fl4Spec.threadSet _ t.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hk), he, hn]
    show ((pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) >>= _) _ = _
    rw [nd_pure_bind']
    exact hm
  -- the dispatch on the state word
  unfold sched.set_priority
  step with Notif.obj.Tcb.state.spec as ⟨st0, hst0⟩
  subst hst0
  have hst := hxe.st
  unfold sched.TS_RUNNING sched.TS_RESTART sched.TS_RUNNING_VM sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND
    sched.TS_BLOCKED_ON_NTFN
  cases hts : x.tcbState with
  | running =>
    have hv0 : L.mem s (tStA t) = 1#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp only [hv0, ↓reduceIte]
    exact prio_run_irelW hP0 hX ht hk (by rw [hts]; rfl) v hv hAc hRel
  | restart =>
    have hv0 : L.mem s (tStA t) = 2#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact prio_run_irelW hP0 hX ht hk (by rw [hts]; rfl) v hv hAc hRel
  | runningVM =>
    have hv0 : L.mem s (tStA t) = 8#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact prio_run_irelW hP0 hX ht hk (by rw [hts]; rfl) v hv hAc hRel
  | inactive =>
    have hv0 : L.mem s (tStA t) = 0#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact plain (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
  | idleThreadState =>
    have hv0 : L.mem s (tStA t) = 7#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact plain (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
  | blockedOnReply r =>
    have hv0 : L.mem s (tStA t) = 5#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact plain (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
  | blockedOnReceive e r d =>
    have hv0 : L.mem s (tStA t) = 3#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact epB e (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl) (hSV.recvQ _ _ _ _ _ hk hts)
  | blockedOnSend e d =>
    have hv0 : L.mem s (tStA t) = 4#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact epB e (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl) (hSV.sendQ _ _ _ _ hk hts)
  | blockedOnNotification n =>
    have hv0 : L.mem s (tStA t) = 6#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact ntB n (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl) (hSV.ntfnW _ _ _ hk hts)

/-- **The target queued only on the object it is blocked on** (ScIpcSorted's
`QueuedOnly`, l4v `valid_ep`/`valid_ntfn` with `sym_refs`): FL4's queues hold
TCBs whose state and block words name that object (`EpObjRel.queue`,
`NtfnObjRel.queue`), which the TCB relations read back as the spec's state
(`TcbRelE.blk`, `TcbRel1.blk`). -/
theorem queuedOnly_of {s : S} {σ : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ) (hOC : ObjCover N T E R C σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) : QueuedOnly σ t.bv x.tcbState := by
  refine ⟨fun p ep hp hm => ?_, fun p xn hp hm => ?_⟩
  · obtain ⟨e', he', ee'⟩ := hOC.ep p ep hp
    subst ee'
    obtain ⟨xs, -, hxs, hB⟩ := (hX.1.toE.at_ep he' hp).queue
    rw [hxs, List.mem_map] at hm
    obtain ⟨y, hy, ey⟩ := hm
    obtain rfl : y = t := eq_of_bv ey
    obtain ⟨hb, hs⟩ := hB _ hy
    have hrel := hX.1.toE.at_tcb ht hk
    have hc : tsCode x.tcbState = 3 ∨ tsCode x.tcbState = 4 := by rw [← hrel.st]; exact hs
    obtain ⟨e0, he0⟩ : ∃ e0, Fl4Spec.epBlocked x.tcbState = some e0 := by
      cases hts : x.tcbState <;> rw [hts] at hc <;> simp [tsCode] at hc <;> exact ⟨_, rfl⟩
    have := hrel.blk e0 he0
    rw [hb] at this
    rw [he0, this]
  · obtain ⟨n', hn', en'⟩ := hOC.ntfn p xn hp
    subst en'
    obtain ⟨hyT, hs, hb⟩ := (hX.1.toN.at_ntfn hn' hp).obj.blocked (y := t) hm
    have hrel := hX.1.toN.at_tcb ht hk
    have hc : tsCode x.tcbState = 6 := by rw [← hrel.st]; exact hs
    obtain ⟨n0, hn0⟩ : ∃ n0, x.tcbState = .blockedOnNotification n0 := by
      cases hts : x.tcbState <;> rw [hts] at hc <;> simp [tsCode] at hc <;> exact ⟨_, rfl⟩
    have := hrel.blk n0 hn0
    rw [hb] at this
    rw [hn0, ← this]
    try rfl

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a `PFr` step** with the footprint `CnW`
(XTopJointCancel's `deadP_kfr`: a dead TCB keeps its state; a dead endpoint
or notification holds nobody, so is kept). -/
theorem JAtZ.deadP_pfr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : PFr t σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
    (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK) F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · obtain ⟨pr, hk3⟩ := F.tcbF hx
    exact ⟨_, hk3, rfl, rfl, Or.inl rfl⟩
  · -- a dead endpoint: idle, so holding nobody
    obtain ⟨y, hy, hc⟩ := F.epF hx
    rcases hc with rfl | hm
    · exact hy
    · exfalso
      obtain ⟨e', he', e⟩ := J.obj.ep q.bv x hx
      have heq : e' = q := P1.eq_of_bv e
      subst heq
      have d2 := hd.2.1 (J.zH.2.1 e' he')
      obtain ⟨x', hk', hO⟩ := J.xtop.ipc.toE.ep e' he'
      rw [hx] at hk'; cases hk'
      rw [epState_eq] at d2
      cases x with
      | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hm
      | sendEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
      | recvEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
  · -- a dead notification: not waiting, so holding nobody
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, -, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, hsc', hbd, hc⟩ := F.ntfnF hx
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, ?_, hbd, Or.inl hsc'⟩
    rcases hc with rfl | hm
    · exact Or.inl rfl
    · exfalso
      cases h : x.ntfnObj with
      | waitingNtfn l => exact hnw l h
      | idleNtfn => rw [Fl4Spec.ntfnQueueOf, h] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      | activeNtfn b => rw [Fl4Spec.ntfnQueueOf, h] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm

set_option maxHeartbeats 4000000 in
/-- **The current thread's facts `JAtZ.setPrioJ` takes** when it is the
target, under `CurInv` and the current thread not the
idle one: in no release queue, bound to the current SC, which is active
(`CurInv.active`: the current SC is not the idle SC, since `Inv.back` names
the idle thread there, `IdleOK`); FL4's release bit clear, its SC word
nonzero and among P1's active SCs (`SCsOK.act`, `SchedRel.act_of`). -/
theorem JAtZ.prioCur (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hne : σ.curThread ≠ σ.idleThread)
    (hC : CurInv σ) {t : U64} (ht : t ∈ Z.T) :
    (σ.curThread = t.bv → t.bv ∉ σ.releaseQueue ∧ ∃ x scp y n, σ.kheap t.bv = some (.tcb x) ∧
      x.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true) ∧
    (t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (P1.scA t) ≠ 0#u64 ∧ L.mem s (P1.scA t) ∈ Ac) := by
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨y, n, hky⟩ := hC.sc
  have hnidle : σ.curSc ≠ σ.idleSc := by
    intro e
    obtain ⟨xi, hki, hsi, -, -⟩ := J.act.2
    obtain ⟨y1, n1, hk1, hb1⟩ := J.inv.back _ _ _ hkt hxs
    obtain ⟨y2, n2, hk2, hb2⟩ := J.inv.back _ _ _ hki hsi
    rw [e] at hk1
    rw [hk1] at hk2; cases hk2
    exact hne (Option.some.inj (hb1.symm.trans hb2))
  have hact : Fl4Spec.scActive y = true := hC.active hnidle y n hky
  have A : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue ∧ ∃ x scp y n, σ.kheap t.bv = some (.tcb x) ∧
      x.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true :=
    fun e => ⟨fun hm => hC.notRel (by rw [e]; exact hm), xt, σ.curSc, y, n, by rw [← e]; exact hkt, hxs, hky, hact⟩
  refine ⟨A, fun e => ?_⟩
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hcur : σ.curThread = t.bv := by rw [e, hs.curThread, hc.cur]; rfl
  obtain ⟨hnr, -⟩ := A hcur
  obtain ⟨x', hk', -, -, hsc, -⟩ := hs.tcb t ht
  rw [← hcur, hkt] at hk'; cases hk'
  rw [hxs] at hsc
  obtain ⟨h0, hb⟩ := Sched.optRef_some hsc.symm
  refine ⟨?_, h0, ?_⟩
  · by_contra h0'
    exact hnr (by rw [hs.rel, mem_map_bv]; exact (hc.released t ht).1 h0')
  · have hmC := hs.scMem t ht h0
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hky' : σ.kheap (L.mem s (P1.scA t)).bv = some (.schedContext y n) := by rw [hb]; exact hky
    have hH := (hJ.sc _ y n (J.c0 _ hmC) hky').2
    have hrm := SchedRel.act_of hS ht (by rw [← hcur]; exact hkt) hxs hky hact
    exact (J.blk.2.2.2.1.act _ ⟨_, hH⟩).2 (fun h => hrm (by rw [h]; rfl))

set_option maxHeartbeats 8000000 in
/-- **`set_priority` at `J`** (module docstring): FL4's side
`set_priority_irelW` (`IRel` after, the footprint `CnW`) with P1's `BlkOK`
and footprint (`sched.set_priority.blk`); the spec's frame `PFr`
(`setPriority_pfr`, `BlkQ` by `blkQ_of_sv`), `Inv` by `setPriority_invC`, the
sorted IPC queues by `setPriority_sorted` (`QueuedOnly` by `queuedOnly_of`);
the rest as `JAtZ.kfrStep`. Premises: no switch pending, and the current
thread's facts when it is the target (`hcur`, `hP1`: `JAtZ.prioCur`). -/
theorem JAtZ.setPrioJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hna : ∀ u, σ.schedulerAction ≠ .switchThread u) {t : U64} (ht : t ∈ Z.T) (v : U64) (hv : v.val < 256)
    (hcur : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue ∧ ∃ x scp y n, σ.kheap t.bv = some (.tcb x) ∧
      x.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true)
    (hP1 : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (P1.scA t) ≠ 0#u64 ∧ L.mem s (P1.scA t) ∈ Ac) :
    sched.set_priority st s t v ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
      ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hQ := qSorted_of_spec (L := L) hI.1.toE hI.1.toN hP0.e.tcb J.isorted
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x, hk, -⟩ := hI.1.toE.tcb t ht
  refine WP.spec_mono (WP.spec_and (set_priority_irelW hP0 hI ht v hv J.inv.actReady (fun h => (hcur h).1) J.sv
    J.inv J.obj (fun e he => hQ e (Or.inl he)) (fun e he => hQ e (Or.inr he)))
    (P1.sched.set_priority.blk s t v J.blk htH hv (fun e => (hP1 e).1) (fun e => (hP1 e).2.1)
      (fun e => (hP1 e).2.2))) ?_
  rintro s' ⟨⟨σ', hm, hIR, hw⟩, hblk, hfoot, -⟩
  have hm' : ((), σ') ∈ (Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ).1 := by
    rw [hm]; exact Set.mem_singleton _
  have hBQ := blkQ_of_sv J.sv hk
  have F : PFr t.bv σ σ' := setPriority_pfr hk _ hna hBQ J.sv _ hm'
  have I3 : Inv σ' := (setPriority_invC J.inv hk (fun e => by
    obtain ⟨-, x', scp, y, n, hk', h1, h2, h3⟩ := hcur e.symm
    rw [hk] at hk'; cases hk'
    exact ⟨scp, y, n, h1, h2, h3⟩) _ hm').1
  have S3 : IpcSorted σ' := setPriority_sorted hk _ J.inv.actReady hBQ (queuedOnly_of hI J.obj ht hk) J.isorted _ hm'
  refine ⟨σ', hm, ?_⟩
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := F.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_pfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 F.khrb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, F.cur J.cur, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, S3, F.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

end

end

end Fl4Proofs.P3
