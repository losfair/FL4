/-
P3 (DESIGN.md §9), IPC: **`maybe_return_sched_context` at `J`** (KENTRY-PLAN.md
item 5, the former `JRecvSigRetHyp`): a thread that is not runnable gives the
notification's SC back when it is its own (l4v `maybe_return_sc`: a passive
server waiting again on the notification that lent it its SC).

* `maybeReturn_shape`: the spec's `maybe_return_sc` when the notification's
  SC is the thread's (its one outcome): the thread's and the SC's links cut,
  the other objects, the current thread and SC, the times and the idle
  thread kept, a reschedule pending iff the thread is the current one (as
  XTopJointFinThreadSc's `unbindTcb_shape`); `maybeReturn_mid`: the mid-entry
  facts after it (as `unbindTcb_mid`).
* `nkt_/lkm_/skm_/pres_maybeReturnSc`: the step kinds of the SC framework.
* `maybe_return_sfoot`: FL4's footprint (`SFoot` and the SC's TCB word).
* `JAtZ.maybeReturnJ`: `JAtZ` before to `JAtZ` after, as XTopJointFinThreadSc's
  `JAtZ.unbindTcbJ` (`maybe_return_refines` for `SchedRel`, `Inv.ret`,
  `ActIdle.ret`, P1's `maybe_return_sched_context.inv`/`.kw` for `BlkOK` and
  the node-0 debug word).
* The blocking receive split before `maybe_return_sched_context`: FL4's
  `rsPre` (`receive_signal_split`), `receive_signal_preF` (on `IRel`), P1's
  `ntfn_blockPre`, the spec's `recvSigBlockPre_eq`, and
  `JAtZ.recvSigBlockPreJ` (`JAtZ` after `rsPre`); copies of
  XTopJointRecvSigBlock's `receive_signal_blockF`, P1 `ntfn_block`,
  `recvSigBlock_eq` and `JAtZ.recvSigBlockJ` without their last step (to fold).
* `JAtZ.recvSigRetJ`: the blocking receive on a notification whose SC is the
  current SC (the former `JRecvSigRetHyp` [W]), `recvSigBlockPreJ` then
  `maybeReturnJ`; `jRecvSigHyp_of` (every case, no premise) and
  `dispatch_recvJS` (moved here from XTopJointRecvSigBlock).
-/
import Fl4Proofs.P3.XTopJointRecvSigBlock
import Fl4Proofs.P3.XTopJointFinThreadSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

theorem nkt_maybeReturnSc (n t : ObjRef) : NKT (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; repeat nkt_step2

theorem lkm_maybeReturnSc {W : ObjRef → Prop} (n t : ObjRef) : LKM W (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; repeat lkm_step2

set_option maxHeartbeats 1000000 in
theorem skm_maybeReturnSc (n t : ObjRef) : SKaM (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; repeat' skm_step

theorem pres_maybeReturnSc (f : Bool × Bool) (n t : ObjRef) : Pres f (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; pres_auto
  all_goals exact pres_rescheduleRequired f

/-- **`maybe_return_sc` keeps the invariant**, for a thread in no queue
(not runnable, or the current thread: `Inv.ret`). -/
theorem Inv.retQ {σ σ' : State Unit} (h : Inv σ) {n t : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn))
    (hnq : NotQueued σ t)
    (he : ((), σ') ∈ (maybeReturnSc (Z := Unit) n t σ).1) : Inv σ' := by
  unfold maybeReturnSc getTcbObjRef at he
  rw [nd_bind_one (getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  split_ifs at he with hc
  swap
  · rw [mem_pure he]; exact h
  obtain ⟨e1, e2⟩ := hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 e2
  rw [hp] at he
  have hsc : xt.tcbSchedContext = some p := e1 ▸ hp
  obtain ⟨ys, ns, hks, -⟩ := h.back t xt p hkt hsc
  have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
  rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some p) σ = ({(p, σ)}, False) from rfl),
    nd_bind_one (threadSet_eq _ hkt)] at he
  have hks1 : (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) xt))).kheap p =
      some (.schedContext ys ns) := by simp [updK, hpt, hks]
  change ((), σ') ∈ ((updateSchedContext p _ >>= _) _).1 at he
  rw [nd_bind_one (updateSchedContext_eq hks1 _), Notif.nd_gets_bind] at he
  have hI := h.unbound hkt hsc hks hnq
  have e3 : (updSc (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) xt))) p
      (scTcbUpdate (fun _ => none) ys) ns) =
      updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns := rfl
  rw [e3] at he
  split_ifs at he
  · obtain ⟨σ3, h3, hq3⟩ := rescheduleRequired_qchange hI.actReady
    rw [h3, Set.mem_singleton_iff] at he; cases he; exact hI.qchange hq3
  · rw [mem_pure he]; exact hI

/-- **The spec's `maybe_return_sc`** when the notification's SC is the
thread's (module docstring). -/
theorem maybeReturn_shape {σ : State Unit} {n t i : ObjRef} {xn : Notification} {x : Tcb} {y : SchedContext}
    {m : Nat} (hI : Inv σ) (hkn : σ.kheap n = some (.notification xn)) (hkt : σ.kheap t = some (.tcb x))
    (hks : σ.kheap i = some (.schedContext y m)) (hxs : x.tcbSchedContext = some i) (hxn : xn.ntfnSc = some i)
    (hnq : NotQueued σ t) :
    ∃ σ', maybeReturnSc (Z := Unit) n t σ = ({((), σ')}, False) ∧
      σ'.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => none) x)) ∧
      σ'.kheap i = some (.schedContext (scTcbUpdate (fun _ => none) y) m) ∧
      (∀ q, q ≠ t → q ≠ i → σ'.kheap q = σ.kheap q) ∧
      σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
      σ'.consumedTime = σ.consumedTime ∧ σ'.idleThread = σ.idleThread ∧ σ'.idleSc = σ.idleSc ∧
      (∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) ∧
      (t = σ.curThread → σ'.schedulerAction = .chooseNewThread) ∧
      (¬ t = σ.curThread → σ'.schedulerAction = σ.schedulerAction) ∧
      (∀ d p, t ∉ σ'.readyQueues d p) := by
  have hti : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  set σ2 := updSc (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) x))) i
    (scTcbUpdate (fun _ => none) y) m with hσ2
  have hI2 : Inv σ2 := hI.unbound hkt hxs hks hnq
  have hks1 : (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) x))).kheap i = some (.schedContext y m) := by
    simp [updK, Ne.symm hti, hks]
  obtain ⟨σ1, he1, k1, c1, s1, t1, n1, i1, isc1, r1, a1, b1⟩ :=
    whenResched_fields (σ := σ2) hI2.actReady (t = σ2.curThread)
  have heq : maybeReturnSc (Z := Unit) n t σ = ({((), σ1)}, False) := by
    unfold maybeReturnSc getTcbObjRef
    rw [nd_bind_one (getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt), hxn, hxs]
    unfold NonDet.when
    rw [if_pos ⟨rfl, by simp⟩,
      nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some i) σ = ({(i, σ)}, False) from rfl),
      nd_bind_one (threadSet_eq _ hkt)]
    change (updateSchedContext i _ >>= _) _ = _
    rw [nd_bind_one (updateSchedContext_eq hks1 _), Notif.nd_gets_bind]
    exact he1
  refine ⟨σ1, heq, ?_, ?_, fun q hq1 hq2 => ?_, c1, s1, t1, n1, i1, isc1, fun u hu => by rw [r1] at hu; exact hu,
    fun h => a1 h, fun h => b1 h, ?_⟩
  · rw [k1]; simp [σ2, updSc, updK, hti]
  · rw [k1]; simp [σ2, updSc, updK]
  · rw [k1]; simp only [σ2, updSc, updK, Function.update_of_ne hq1, Function.update_of_ne hq2]
  · intro d p hm
    have hkt2 : σ2.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => none) x)) := by
      simp [σ2, updSc, updK, hti]
    by_cases hP : t = σ2.curThread
    · obtain ⟨σ3, e3, hq3, -⟩ := rescheduleRequired_calm hI2.actReady
      have e4 : (if t = σ2.curThread then rescheduleRequired (Z := Unit) else NonDet.pure ()) σ2 =
          ({((), σ3)}, False) := by rw [if_pos hP]; exact e3
      rw [← the_result he1 e4] at hm
      rcases hq3.2.2.2 d p t hm with h | h
      · exact hnq.1 d p h
      · obtain ⟨xu, scp, -, -, hku, hsc, -⟩ := schedulable_inv h
        rw [hkt2] at hku; cases hku; simp [tcbSchedContextUpdate] at hsc
    · have e4 : (if t = σ2.curThread then rescheduleRequired (Z := Unit) else NonDet.pure ()) σ2 =
          ({((), σ2)}, False) := by rw [if_neg hP]; rfl
      rw [← the_result he1 e4] at hm
      exact hnq.1 d p hm

/-- **The mid-entry facts after `maybe_return_sc`** (module docstring; the
proof is `unbindTcb_mid`'s on `maybeReturn_shape`). -/
theorem maybeReturn_mid {T C : Set U64} {σ σ' : State Unit} {n i t : ObjRef} {y : SchedContext} {m : Nat}
    {x : Tcb} {xn : Notification}
    (hI : Inv σ) (hks : σ.kheap i = some (.schedContext y m)) (hy : y.scTcb = some t)
    (hkt : σ.kheap t = some (.tcb x)) (hxs : x.tcbSchedContext = some i)
    (hkn : σ.kheap n = some (.notification xn)) (hxn : xn.ntfnSc = some i) (hnq : NotQueued σ t)
    (hiC : ∃ q ∈ C, UScalar.bv q = i)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t) (hid : t ≠ σ.idleThread)
    (hcur : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (hown : CurOwnW T C σ) (hoff : OffOK σ)
    (hact : ActIdle σ) (hcr : CurRunM σ)
    (he : maybeReturnSc (Z := Unit) n t σ = ({((), σ')}, False)) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW T C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
      CurRunM σ' ∧ FK σ σ' := by
  obtain ⟨σ2, e2, kt, ki, ko, ct, cs, tm, cn, hidl, hisc, rq, a1, b1, -⟩ := maybeReturn_shape hI hkn hkt hks hxs hxn hnq
  have e := the_result e2 he
  subst e
  have hti : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  have nTi : ∀ q (z : Tcb), σ.kheap q = some (.tcb z) → q ≠ i := by
    rintro q z hq rfl; rw [hks] at hq; cases hq
  have nSt : ∀ q (z : SchedContext) m, σ.kheap q = some (.schedContext z m) → q ≠ t := by
    rintro q z m hq rfl; rw [hkt] at hq; cases hq
  have hidi : σ.idleThread ≠ i := by obtain ⟨xi, h1, -⟩ := hact.2; exact nTi _ _ h1
  have hIdle : IdleOK σ' := IdleOK.of hact.2 hidl (ko _ (Ne.symm hid) hidi) (fun h => rq _ h)
  have hAct : ActIdle σ' := by
    refine ⟨fun u hu => ?_, hIdle⟩
    by_cases htc : t = σ.curThread
    · rw [a1 htc] at hu; cases hu
    rw [b1 htc] at hu
    obtain ⟨xu, scp, yu, nu, hku, hsc, hrun, hky, hac, hnr'⟩ := schedulable_inv (hact.1 u hu)
    have hut : u ≠ t := hsa u hu
    have hui : u ≠ i := nTi _ _ hku
    have hst : scp ≠ t := nSt _ _ _ hky
    have hsi : scp ≠ i := by
      rintro rfl
      obtain ⟨y1, n1, h1, h2⟩ := hI.back u xu scp hku hsc
      rw [hks] at h1; cases h1; rw [hy] at h2; cases h2; exact hut rfl
    exact schedulable_of (by rw [ko _ hut hui]; exact hku) hsc hrun (by rw [ko _ hst hsi]; exact hky) hac
      (fun h => hnr' (rq _ h))
  refine ⟨?_, ?_, ?_, hAct, ?_, ⟨cs, hidl, hisc⟩⟩
  · by_cases htc : t = σ.curThread
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
    refine ⟨⟨xt, by rw [ct, ko _ hct hci]; exact hkc, by rw [cs]; exact hcs, hnb⟩,
      ⟨y1, n1, by rw [cs, ko _ hcst hcsi]; exact hk1⟩, fun hne y3 n3 h3 => ?_,
      fun h => hC.notRel (by rw [ct] at h; exact rq _ h)⟩
    rw [cs, hisc] at hne; rw [cs] at h3; rw [ko _ hcst hcsi] at h3
    exact hC.active hne y3 n3 h3
  · rcases hown with ⟨u, hu, xt, hku, hxt, hown, hnr'⟩ | ⟨hcs, hun⟩
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
          fun h0 hm => hnr' (by rw [← cn]; exact h0) (rq _ hm)⟩
    · refine Or.inr ⟨by rw [cs]; exact hcs, fun x' n' h => ?_⟩
      rw [cs] at h
      by_cases e : σ.curSc = i
      · rw [e, ki] at h; cases h; rfl
      by_cases e2 : σ.curSc = t
      · rw [e2, kt] at h; cases h
      rw [ko _ e2 e] at h; exact hun _ _ h
  · intro h0 y1 n1 h1 ha
    rw [cn] at h0 ⊢; rw [tm]
    rw [cs] at h1; rw [cs, hisc] at ha
    by_cases e : σ.curSc = i
    · rw [e, ki] at h1; cases h1
      exact hoff h0 y m (by rw [e]; exact hks) ha
    by_cases e2 : σ.curSc = t
    · rw [e2, kt] at h1; cases h1
    rw [ko _ e2 e] at h1
    exact hoff h0 y1 n1 h1 ha
  · by_cases htc : t = σ.curThread
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

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **FL4's `maybe_return_sched_context`'s footprint**: the scheduler's words
and the SC's TCB word, for a thread whose SC is `i`. -/
theorem maybe_return_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t n i : U64} (ht : t ∈ T) (hiC : i ∈ C)
    {x : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb x)) (hsp : x.tcbSchedContext = some i.bv) :
    notification.maybe_return_sched_context st s n t ⦃ s' =>
      WritesIn st s s' (fun b => SFoot st T c s b ∨ b = scW i 24#u64) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt', -, -, hsct, -⟩ := hs.tcb t ht
  rw [hkt] at hkt'; cases hkt'
  have hsc : L.mem s (scA t) = i := by
    have h1 : optRef (L.mem s (scA t)) = some i.bv := by rw [← hsct]; exact hsp
    by_cases h0 : L.mem s (scA t) = 0#u64
    · rw [h0, optRef_zero] at h1; cases h1
    · rw [optRef_ne h0] at h1; exact eq_of_bv (Option.some.inj h1)
  obtain ⟨xs, ns, hks, hxs⟩ := hs.scs i hiC
  have ha24 : Aligned (scW i 24#u64) := (hxs.hdr (K := 24#u64) (by simp) (by simp)).1
  have hit : i.bv ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  unfold notification.maybe_return_sched_context
  refine WP.spec_bind (Notif.obj.Ntfn.sc.spec s n) ?_
  rintro v rfl
  refine WP.spec_bind (P1.obj.Sc.is_null.spec _) ?_
  rintro b rfl
  by_cases h0 : L.mem s (nScA n) = 0#u64
  · rw [if_pos (by simp [h0])]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rw [if_neg (by simp [h0])]
  refine WP.spec_bind (P1.obj.Tcb.sc.spec s t) ?_
  rintro i1 rfl
  by_cases e : L.mem s (nScA n) = L.mem s (scA t)
  swap
  · rw [if_neg e]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rw [if_pos e, e, hsc]
  refine WP.spec_bind (obj.Tcb.set_sc.spec' s t 0#u64) ?_
  rintro s1 rfl
  refine WP.spec_bind (obj.Sc.set_tcb.spec' _ i 0#u64) ?_
  rintro s2 rfl
  have w2 : WritesIn st s (L.wr (L.wr s (scA t) 0#u64) (scW i 24#u64) 0#u64)
      (fun b => SFoot st T c s b ∨ b = scW i 24#u64) :=
    ((writesIn_tcb (s := s) (c := c) (K := 3464#u64) hc.tcbs ht (by unfold SOff SOffL; decide) (by simp)
      0#u64).trans (writesIn_wr ha24)).mono fun b hb => hb.elim Or.inl Or.inr
  obtain ⟨hS1, -, -⟩ := hS.set_tcb_sc ht hkt (v := 0#u64) (Or.inl rfl)
  have hks1 : (updK σ t.bv (.tcb { x with tcbSchedContext := optRef 0#u64 })).kheap i.bv =
      some (.schedContext xs ns) := by simp [updK, hit, hks]
  obtain ⟨hS2, -, -⟩ := hS1.set_sc_tcb hiC hks1 0#u64
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  split
  · refine WP.spec_mono (reschedule_required_sfoot hS2) fun s3 h3 => ?_
    exact (w2.trans h3).mono fun b hb => hb.elim id fun h => Or.inl ((SFoot.ksb w2.1).1 h)
  · exact (WP.spec_ok _).2 w2

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st) in
/-- **The blocking receive up to `maybe_return_sched_context`**: the state
and block words, `schedule_tcb`, the queue insertion. -/
def rsPre (s : S) (t n : U64) : Result S := do
  let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
  let s2 ← obj.Tcb.set_block_obj st t s1 n
  let s3 ← sched.schedule_tcb st s2 t
  notification.ntfn_append st s3 n t

/-- **`receive_signal`'s blocking branch split** at `rsPre`, on an idle or
waiting notification. -/
theorem receive_signal_split {s : S} {a : A} {t n : U64}
    (hst : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING)
    {P : S → Prop} {Q : S × A → Prop} (h : rsPre st s t n ⦃ P ⦄)
    (hk : ∀ s4, P s4 → notification.maybe_return_sched_context st s4 n t ⦃ s5 => Q (s5, a) ⦄) :
    notification.receive_signal st ar s a t n true ⦃ Q ⦄ := by
  have key := WP.spec_bind h fun s4 h4 => WP.spec_bind (hk s4 h4) fun s5 h5 => (WP.spec_ok _).2 h5
  simp only [rsPre, Std.bind_assoc] at key
  unfold notification.receive_signal
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with hst | hst
  · rw [hst, if_pos rfl, if_pos rfl]
    exact key
  · rw [hst, if_neg (by rw [ntfn_consts.1, ntfn_consts.2.1]; decide), if_pos rfl, if_pos rfl]
    exact key

set_option maxHeartbeats 16000000 in
/-- **`rsPre` on `IRel`, with its footprint** (as `receive_signal_blockF`,
for any SC of the notification): the spec's prefix (`set_thread_state`,
`tcb_ntfn_append`) and the receive as `maybe_return_sc` after it. -/
theorem receive_signal_preF (hP : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    rsPre st s t n ⦃ s4 => ∃ σ3,
      (Fl4Spec.setThreadState (Z := Unit) t.bv (.blockedOnNotification n.bv) >>= fun _ =>
        Fl4Spec.tcbNtfnAppend t.bv n.bv) σ = ({((), σ3)}, False) ∧
      Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ = Fl4Spec.maybeReturnSc n.bv t.bv σ3 ∧
      IRel st th cr N T C E R B c s4 σ3 ∧ WritesIn st s s4 (RBW st N T s) ∧
      (∃ q, σ3.kheap n.bv = some (.notification { x with ntfnObj := .waitingNtfn q })) ∧
      σ3.kheap t.bv = some (.tcb { xt with tcbState := .blockedOnNotification n.bv }) ⦄ := by
  obtain ⟨hR, hSR⟩ := hX
  have hx := hR.toN.at_ntfn hn hk
  have hta := hP.e.tcb t ht
  obtain ⟨xt', hkx, hxt⟩ := hR.tcb t ht
  rw [hkt] at hkx; injection hkx with hkx; injection hkx with hkx; subst hkx
  have hnm := not_member hR.toN ht hkt hnb
  -- the queue
  obtain ⟨xs, hQ, hxs, hB, hst⟩ : ∃ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs ∧
      x.ntfnObj.ntfnQueue = xs.map UScalar.bv ∧ (∀ y ∈ xs, BlockedOn (L.mem s) n y) ∧
      (stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING) := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn =>
      rw [h] at this
      exact ⟨[], this.2, rfl, by simp, Or.inl (stOf_idle (T := T) (h ▸ hx.obj) rfl)⟩
    | waitingNtfn q =>
      rw [h] at this
      obtain ⟨h1, xs, -, rfl, h2, h3⟩ := this
      exact ⟨xs, h2, rfl, h3, Or.inr (stOf_waiting (T := T) (h ▸ hx.obj) rfl)⟩
    | activeNtfn b => exact absurd h (hna b)
  have htxs : t ∉ xs := fun h => hnm n hn x hk (by rw [hxs]; exact List.mem_map_of_mem h)
  have hsorted := hsort xs hQ
  -- step 1: the state and block-object words
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnNotification n.bv }
  set σ1 := updK σ t.bv (.tcb x1)
  set s2 := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) (tBlockA t) n
  obtain ⟨hw1, hoth1⟩ := twr_wr (st := st) hP.n ht (K := 3328#u64) (Or.inl rfl) s sched.TS_BLOCKED_ON_NTFN
  obtain ⟨hw2, hoth2⟩ := twr_wr (st := st) hP.n ht (K := 3336#u64) (Or.inr (Or.inl rfl))
    (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) n
  rw [← tStA_eq] at hw1 hoth1
  rw [← tBlockA_eq] at hw2 hoth2
  have hw := hw1.trans hw2
  have hsa := (a_st hta).1
  have hba := (a_blk hta).1
  have hstv := val_st hta
  have hbl := val_blk hta
  have two : ∀ b, Aligned b → b.val ≠ t.val + 3328 → b.val ≠ t.val + 3336 → L.mem s2 b = L.mem s b := by
    intro b hb h1 h2
    show L.mem (L.wr (L.wr s _ _) _ _) b = _
    rw [wr_agree (st := st) hba b hb (by rw [hbl]; exact h2), wr_agree (st := st) hsa b hb (by rw [hstv]; exact h1)]
  have hR1 : IpcRel N T E R B (L.mem s2) σ1 := by
    refine hR.upd_tcb hP ht _ (fun b hb ⟨_, hnt⟩ => two b hb
      (fun e => hnt (Or.inl (TF.of_val (a_st hta).2 (by rw [e, hstv]))))
      (fun e => hnt (Or.inl (TF.of_val (a_blk hta).2 (by rw [e, hbl]))))) (Or.inl ⟨hnm, hqE⟩) ?_
    refine TcbRel.of_words hta hxt _ (fun b hb _ hv => two b hb (fun e => hv (Or.inl e))
        (fun e => hv (Or.inr (Or.inl e))))
      ?_ (fun e h => by cases h) (fun m hm => ?_) (Or.inr (by simp [NoEpPayload])) (fun r => ?_) rfl rfl rfl rfl
    · show (L.mem s2 (tStA t)).val = 6
      show (L.mem (L.wr (L.wr s _ _) _ _) _).val = 6
      rw [wr_agree (st := st) hba _ hsa (by rw [hbl, hstv]; omega), rd_wr_eq hsa, six_val]
    · cases hm
      show (L.mem s2 (tBlockA t)).bv = n.bv
      rw [rd_wr_eq hba]
    · rw [two _ (a_reg hta r).1 (by rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)
        (by rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)]
      exact hxt.regs r
  have hK1 : NtfnStep σ σ1 := NtfnStep.tcb hkt (.blockedOnNotification n.bv) xt.tcbArch
  have hW1 := hw.foot
  have hSR1 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s2 σ1 :=
    ⟨hSR.1.stableN hSR.2.1.placed hW1 hK1, hSR.2.1.stable hW1 hK1, hSR.2.2.mono hW1.1 (SzKeep.ntfnStep hK1)⟩
  set σ2 := stsAct σ1 t.bv
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk2 : σ2.kheap n.bv = some (.notification x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  -- the action word of a state with `s`'s kernel base and core
  have hactW : ∀ s' : S, L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      Aligned (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) ∧
        RBW st N T s (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) := by
    intro s' hk' hc'
    obtain ⟨Q0, R0, hc0, -⟩ := hSR.2.1.lists
    have hN0 := hc0.node
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [nodeAt_ksb hk', hc']
    refine ⟨?_, Or.inr rfl⟩
    rw [hc0.cur]
    exact nodeAt_aligned hN0 ho (by simp [layout.node.SCHED_ACTION])
  unfold rsPre
  step
  step
  subst s1_post s2_post
  refine WP.spec_bind (WP.spec_and ((ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c)
    hP.e).scheduleTcb _ σ1 t hR1.toE (ScRelM.of hR1) hSR1 ht) (schedule_tcb_cases _ t)) ?_
  rintro s3 ⟨⟨hf3, hS3⟩, hc3⟩
  have hF3 : WritesIn st s s3 (RBW st N T s) := by
    rcases hc3 with rfl | rfl
    · exact hW1.mono fun b hb => Or.inl hb
    · refine (hW1.trans ((writesIn_wr (hactW _ hW1.1 hW1.2.1).1).mono fun b hb =>
        hb ▸ (hactW _ hW1.1 hW1.2.1).2)).mono fun b hb => hb.elim (fun h => Or.inl h) id
  have hR3 : IpcRel N T E R B (L.mem s3) σ2 := hR1.frame hP hf3 (IKView.stsAct _ _)
  obtain ⟨xs3, hQ3, hxs3, hB3⟩ := (hR3.toN.at_ntfn hn hk2).obj.queue
  have e3 : xs3 = xs := by
    rw [hxs] at hxs3
    exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs3).symm
  subst e3
  have hxt3 := hR3.toN.at_tcb ht hkt2
  -- priorities agree with those of `s`
  have hpr : ∀ y ∈ xs3, L.mem s3 (prioA y) = L.mem s (prioA y) := by
    intro y hy
    have hyT := hQ.mem y hy
    have hyt : y ≠ t := fun e => htxs (e ▸ hy)
    have hyA := hP.e.tcb y hyT
    exact (hf3 _ (a_prio hyA).1 (EFoot.ifoot (Or.inr (Or.inr (Or.inl ⟨y, hyT, Or.inl (a_prio hyA).2⟩))))).trans
      (hw.tcb y hyT hyt).prio
  have hsorted3 : PrioSorted (fun y => L.mem s3 (prioA y)) xs3 := prioSorted_congr hsorted hpr
  refine WP.spec_mono (ntfn_append_full hP.n s3 hn t xs3 hQ3 ht htxs) ?_
  rintro s4 ⟨hA1, hA2, hA3⟩
  set ys := insPrio (fun y => L.mem s3 (prioA y)) (L.mem s3 (prioA t)) t xs3
  have hblk3 : L.mem s3 (tBlockA t) = n := eq_of_bv (hxt3.blk n.bv rfl)
  have hR4 : IpcRel N T E R B (L.mem s4)
      (updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })) := by
    have hx2 := hR3.toN.at_ntfn hn hk2
    have hbw : ∀ w ∈ t :: xs3, w ∈ T ∧ L.mem s3 (tBlockA w) = n := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨ht, hblk3⟩
      · exact ⟨hQ.mem w hw, (hB3 w hw).2⟩
    refine hR3.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
        (fun w hw => by
          obtain ⟨hwT, hwb⟩ := hbw w hw
          have hwa := hP.e.tcb w hwT
          exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
            fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
        (fun e => hnw (e ▸ (nw_words hP hn).1)) (fun e => hnw (e ▸ (nw_words hP hn).2.1)))
      ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨hA2, ys, insPrio_ne_nil hsorted3, rfl, hA1, fun y hy => ?_⟩
      have hyT : y ∈ T := by
        rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
        · exact ht
        · exact hQ.mem y hy'
      have e := hA3.tcb y hyT
      rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
      · exact ⟨by rw [e.st, hxt3.st]; rfl, by rw [e.blk]; exact hblk3⟩
      · exact ⟨by rw [e.st]; exact (hB3 y hy').1, by rw [e.blk]; exact (hB3 y hy').2⟩
    · show x.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
    · rw [hA3.bound]; exact hx2.bound_mem
    · show x.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
  -- the spec
  have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Notif.prioOf σ2 y := by
    intro y hy
    have hy' : y ∈ x.ntfnObj.ntfnQueue := hy
    rw [hxs] at hy'
    obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy'
    obtain ⟨z, hz, -⟩ := hR3.toN.tcb y' (hQ.mem y' hy'x)
    exact ⟨z, hz, by simp [Notif.prioOf, hz]⟩
  have hlist : specIns (Fl4Spec.ntfnQueueOf x) (Notif.prioOf σ2) x1.tcbPriority t.bv = ys.map UScalar.bv := by
    have hq' : Fl4Spec.ntfnQueueOf x = xs3.map UScalar.bv := hxs
    rw [specIns, hq', List.takeWhile_map, List.dropWhile_map]
    simp only [ys, insPrio_eq_sorted _ _ t xs3 hsorted3, List.map_append, List.map_cons]
    have hc : ∀ y ∈ xs3, ((fun y => @decide (Notif.prioOf σ2 y ≥ x1.tcbPriority) (Classical.propDecidable _)) ∘
        UScalar.bv) y =
        (fun y => !decide (L.mem s3 (prioA t) > L.mem s3 (prioA y))) y := by
      intro y hy
      obtain ⟨z, hz, hzr⟩ := hR3.toN.tcb y (hQ.mem y hy)
      have hpz : Notif.prioOf σ2 y.bv = z.tcbPriority := by simp [Notif.prioOf, hz]
      simp only [Function.comp, hpz]
      convert (prio_ge_iff _ _ _ _ hxt3.prio hzr.prio).symm using 2
    rw [takeWhile_congr' hc, dropWhile_congr' hc]
  set σ3 := updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })
  have hk3 : σ3.kheap n.bv = some (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) := by
    simp [σ3, updK]
  have hkt3 : σ3.kheap t.bv = some (.tcb x1) := by simp [σ3, updK, Ne.symm hnt, hkt2]
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ =
      Fl4Spec.maybeReturnSc n.bv t.bv σ3 := by
    rw [receiveSignal_notActive hk hna]
    unfold Fl4Spec.receiveSignalBlocked
    simp only [↓reduceIte]
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (tcbNtfnAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq), hlist]
  have hK4 : NtfnStep σ2 σ3 :=
    NtfnStep.ntfn (y := { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) hk2 rfl rfl
  have hW4 := hA3.foot
  have hSR4 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s4 σ3 :=
    ⟨hS3.1.stableN hS3.2.1.placed hW4 hK4, hS3.2.1.stable hW4 hK4, hS3.2.2.mono hW4.1 (SzKeep.ntfnStep hK4)⟩
  refine ⟨σ3, ?_, hspec, ⟨hR4, hSR4⟩,
    (hF3.trans (hW4.mono fun b hb => (Or.inl hb : RBW st N T s b))).mono fun b hb => hb.elim id id, ⟨_, hk3⟩, hkt3⟩
  rw [nd_bind_one (Notif.setThreadState_eq _ hkt), tcbNtfnAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq, hlist]

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **P1's invariants after `rsPre`** (the blocking receive before
`maybe_return_sched_context`, as `ntfn_block`): `BlkOK`'s parts, the thread
blocked, the idle word kept. -/
theorem ntfn_blockPre (s : S) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t) (hidle : L.idleW s ≠ t)
    (hH : H n = some .ntfn) (hst0 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64) :
    Fl4Proofs.P3.Ipc.rsPre st s t n ⦃ s4 => (∃ Q' R', SchedQueuesInv st T Cs Ω H s4 Q' R') ∧ BoundInv st T Ac s4 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s4 ∧ SCsOK st T Ω Sg Scs Z Ac s4 ∧ SgOK st Ω Sg s4 ∧
      ¬ Runnable (L.mem s4 (stA t)) ∧ L.idleW s4 = L.idleW s ⦄ := by
  unfold Fl4Proofs.P3.Ipc.rsPre
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w2 : WritesIn st s s2 (BlkFoot st s t 0#u64) := by
    rw [e2, e1]; exact blk_wr_field hta (blk_wr_field (K := 3328#u64) hta (WritesIn.refl _ _) (by simp)) (by simp)
  have v2 : L.mem s2 (stA t) = sched.TS_BLOCKED_ON_NTFN := by
    rw [e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
    exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have b2 : L.mem s2 (blockA t) = n := by
    rw [e2]; exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have a2 : L.actionW s2 = L.actionW s := by
    rw [e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
      e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hbl : Blocked sched.TS_BLOCKED_ON_NTFN := Or.inr (Or.inr rfl)
  refine WP.spec_bind (sched.schedule_tcb.blk s2 t h2 (by rw [v2]; exact blocked_not_runnable hbl)) ?_
  rintro s3 ⟨h3, e3, hc3⟩
  obtain ⟨w3, a3, v3, b3, -, -⟩ := blk_sched h2 ht w2 a2 e3
  rw [v2] at v3; rw [b2] at b3
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_mono (blk_tail (f := notification.ntfn_append st s3 n t) (r0 := 0#u64) (hidl := hidle)
    h hB hX hS hSg ht
    (Or.inr (Or.inr ⟨rfl, hH, rfl⟩)) hst0 h3 w3 a3 v3 b3 (fun h0 => absurd rfl h0)
    (fun h1 => absurd (v3.symm.trans h1) (by rw [r3, r6]; decide)) hc.old (fun h0 => absurd rfl h0) hc.ac
    (fun xs hE hq hn => WP.spec_mono (WP.spec_and
      (notification.ntfn_append.rel s3 n t xs h3.tcbs hE hq ht hn)
      (notification.ntfn_append.foot s3 n t xs h3.tcbs hE hq ht hn))
      fun s4 hh => ⟨hh.1.1, by rw [hh.1.2, ntfn_wait_val], hh.2⟩)) ?_
  rintro s4 ⟨h4, hB4, hX4, hS4, hSg4, ea4, ec4, v4, ei4⟩
  exact ⟨⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4, by rw [v4]; exact blocked_not_runnable hbl, ei4⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **The spec's blocking receive's prefix in `BFrN`** (as `recvSigBlock_eq`,
for any SC of the notification). -/
theorem recvSigBlockPre_eq {σ : State Unit} {t n : ObjRef} {xt : Tcb} {x : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hk : σ.kheap n = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (htq : t ∉ ntfnQueueOf x) (hq : ∀ y ∈ ntfnQueueOf x, ∃ z, σ.kheap y = some (.tcb z))
    (hr : runnable xt.tcbState = true) (hS : SortedQ σ (ntfnQueueOf x))
    :
    ∃ σ', (setThreadState (Z := Unit) t (.blockedOnNotification n) >>= fun _ => tcbNtfnAppend t n) σ =
      ({((), σ')}, False) ∧ BFrN t n σ σ' ∧
      IK t σ σ' ∧ σ'.readyQueues = σ.readyQueues ∧
      (t = σ.curThread → σ.schedulerAction = .resumeCurThread → σ'.schedulerAction = .chooseNewThread) ∧
      (∀ y, σ'.kheap n = some (.notification y) → SortedQ σ y.ntfnObj.ntfnQueue) := by
  let x1 : Tcb := { xt with tcbState := .blockedOnNotification n }
  let σ2 := stsAct (updK σ t (.tcb x1)) t
  let q' := Notif.specIns (ntfnQueueOf x) (Sched.prioOf σ2) x1.tcbPriority t
  let y : Notification := { x with ntfnObj := .waitingNtfn q' }
  let σ' := updK σ2 n (.notification y)
  have htn : t ≠ n := by rintro rfl; rw [hkt] at hk; cases hk
  have hk2 : σ2.kheap n = some (.notification x) := by simp [σ2, stsAct_kheap, Ne.symm htn, hk]
  have hkt2 : σ2.kheap t = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  have hq2 : ∀ y ∈ ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Sched.prioOf σ2 y := by
    intro y hy
    obtain ⟨z, hz⟩ := hq y hy
    have hyt : y ≠ t := fun h => htq (h ▸ hy)
    have hz2 : σ2.kheap y = some (.tcb z) := by simp [σ2, stsAct_kheap, hyt, hz]
    exact ⟨z, hz2, (prioOf_eq hz2).symm⟩
  have heq : (setThreadState (Z := Unit) t (.blockedOnNotification n) >>= fun _ => tcbNtfnAppend t n) σ =
      ({((), σ')}, False) := by
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), tcbNtfnAppend_eq hk2 hkt2 (Sched.prioOf σ2) hq2]
  have hkh : ∀ p, σ'.kheap p = if p = n then some (.notification y)
      else if p = t then some (.tcb x1) else σ.kheap p := by
    intro p
    simp only [σ', σ2, updK_kheap, stsAct_kheap, Function.update_apply]
  have hrq : σ'.readyQueues = σ.readyQueues := by
    show (stsAct _ t).readyQueues = _
    unfold stsAct; split <;> rfl
  have hrl : σ'.releaseQueue = σ.releaseQueue := by
    show (stsAct _ t).releaseQueue = _
    unfold stsAct; split <;> rfl
  have htm : σ'.curTime = σ.curTime := by
    show (stsAct _ t).curTime = _
    unfold stsAct; split <;> rfl
  have hsk : Sk σ σ' := by
    show Sk σ (updK (stsAct _ t) n _)
    unfold stsAct; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpr2 : ∀ u, Sched.prioOf σ2 u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = t
    · subst hut; exact (prioOf_eq hkt2).trans (prioOf_eq hkt).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
      simp only [σ2, stsAct_kheap, updK_kheap, Function.update_apply, if_neg hut]
  refine ⟨σ', heq, ⟨hsk, fun p => ?_⟩, ⟨fun p => ?_, hrq, hrl, htm⟩, hrq, fun hct hres => ?_, fun y' hy => ?_⟩
  · rw [hkh]
    by_cases hpn : p = n
    · rw [if_pos hpn]
      exact Or.inr ⟨.notification x, .notification y, by rw [hpn]; exact hk, rfl,
        Or.inr ⟨x, y, rfl, rfl, hpn, rfl, rfl⟩⟩
    · rw [if_neg hpn]
      by_cases hpt : p = t
      · rw [if_pos hpt]
        exact Or.inr ⟨.tcb xt, .tcb x1, by rw [hpt]; exact hkt, rfl, Or.inl ⟨xt, n, rfl, rfl, hpt, hr⟩⟩
      · rw [if_neg hpt]; exact Or.inl rfl
  · rw [hkh]
    by_cases hpn : p = n
    · rw [if_pos hpn, hpn, hk]
      exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => by cases e; exact ⟨_, rfl, rfl⟩,
        fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => by cases e; exact ⟨_, rfl⟩⟩
    · rw [if_neg hpn]
      by_cases hpt : p = t
      · rw [if_pos hpt, hpt, hkt]
        exact ⟨fun _ e => by cases e; exact ⟨_, rfl, rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩,
          fun _ _ e => (by cases e), fun _ e => (by cases e), fun _ e => by cases e; exact ⟨_, rfl⟩,
          fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
      · rw [if_neg hpt]; exact OIK.refl _ _
  · have hns : ¬ schedulable t (updK σ t (.tcb x1)) = true := by
      intro hs
      obtain ⟨y, -, -, -, hy, -, hrun, -⟩ := schedulable_inv hs
      rw [updK_kheap, Function.update_self] at hy
      cases hy
      simp [x1, runnable] at hrun
    show (stsAct _ t).schedulerAction = _
    unfold stsAct
    rw [if_pos ⟨hct, hres, hns⟩]
  · rw [hkh, if_pos rfl] at hy
    cases hy
    exact (sortedQ_specIns (hS.congr fun u _ => hpr2 u) t (prioOf_eq hkt2)).congr fun u _ => (hpr2 u).symm

end Spec

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
/-- **`maybe_return_sched_context` at `J`** (module docstring), for a thread
`t` in no queue (spec `hnq`, FL4 `hout`: not runnable, or the running current
thread of a receive, XTopJointRecvIpcRet), neither the idle thread nor the
switch target, whose SC `i` is the notification `n`'s. -/
theorem JAtZ.maybeReturnJQ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n i : U64} {x : Fl4Spec.Tcb}
    {xn : Fl4Spec.Notification} (ht : t ∈ Z.T) (hn : n ∈ Z.N) (hiC : i ∈ Z.C)
    (hk : σ.kheap t.bv = some (.tcb x)) (hkn : σ.kheap n.bv = some (.notification xn))
    (hsp : x.tcbSchedContext = some i.bv) (hxn : xn.ntfnSc = some i.bv) (hnq : NotQueued σ t.bv)
    (hout : (L.mem s (P1.inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    notification.maybe_return_sched_context st s n t ⦃ s' =>
      P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ) ∧ ∃ σ',
      Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨y, m, hky, hyt⟩ := J.inv.back t.bv x i.bv hk hsp
  obtain ⟨σ2, he, kt, ki, ko, -⟩ := maybeReturn_shape J.inv hkn hk hky hsp hxn hnq
  have hm : ((), σ2) ∈ (Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ).1 := by
    rw [he]; exact Set.mem_singleton _
  obtain ⟨-, hidle⟩ := J.words_of_spec ht hsa hid
  have htP : t ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact ht
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  refine WP.spec_mono (WP.spec_and (WP.spec_and (maybe_return_refines s σ hR hS J.inv.actReady t n ht hn)
    (maybe_return_sfoot hS ht hiC hk hsp))
    (WP.spec_and (P1.notification.maybe_return_sched_context.inv s n t Q0 R0 h0 hB0 hX0 hS0 hSg0 htP hout hidle)
      (P1.notification.maybe_return_sched_context.kw s n t Q0 R0 h0 hB0 hX0 hS0 hSg0 htP hout hidle))) ?_
  rintro s' ⟨⟨⟨-, σ0, hm0, hf, hv, hS'⟩, hw5⟩, hP1, hfoot⟩
  rw [he] at hm0
  have e0 : σ0 = σ2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hm0)
  rw [e0] at hS' hv
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hP1.1, hP1.2.1, hP1.2.2.1, hP1.2.2.2.1, hP1.2.2.2.2.1⟩
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ2 := hR.frame hS.placed hf hv
  have hN' : NSC Z.N Z.C σ2 := fun q hq x' p hx hp => J.nsc q hq x' p (by
    by_cases e1 : q.bv = t.bv
    · rw [e1, kt] at hx; cases hx
    by_cases e3 : q.bv = i.bv
    · rw [e3, ki] at hx; cases hx
    rw [ko _ e1 e3] at hx; exact hx) hp
  have hI' : Inv σ2 := Inv.retQ J.inv hk hkn hnq hm
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) :=
    Sched.WritesIn.kfoot_of_sfoot_scw hS hiC (K := 24#u64) (by simp) (by simp) (by decide) hw5
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWk
  have hK : ScTKw (fun _ => False) σ σ2 := nkt_maybeReturnSc n.bv t.bv σ ((), σ2) hm
  have hX' : XTopAt (L := L) AR Z s' a σ2 :=
    xtop_sc_step (ct := σ.curThread) hX J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hall := ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree
    ⟨⟨hS', hR', hN', hI'⟩, hWk, (pres_maybeReturnSc (true, true) _ _).of_eq he⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  obtain ⟨hcur', hown', hoff', hact', hcr', hF⟩ := maybeReturn_mid (T := Z.T) J.inv hky hyt hk hsp hkn hxn hnq
    ⟨i, hiC, rfl⟩ hsa hid J.cur J.own J.off J.act J.curRun he
  have hB' : BlockedScActive σ2 :=
    J.bsa.bk (bk_of_tk_sk hK (skm_maybeReturnSc _ _ σ _ hm)) ((pres_maybeReturnSc (true, true) _ _).of_eq he)
  have hL : LK (fun _ => False) σ σ2 := lkm_maybeReturnSc (W := fun _ => False) n.bv t.bv σ _ hm
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) hL hF hact'.1 hY'
      ((((pres_maybeReturnSc (true, true) _ _).of_eq he).ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨hW, σ2, he, Ac, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2)
    (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2))
    (J.sc_kern hW hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN' hI' hcur' hown' hoff' hact' hB' hcr' hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩

/-- **`maybe_return_sched_context` at `J`** (module docstring): a thread
`t`, not runnable, neither the idle thread nor the switch target, whose SC
`i` is the notification `n`'s, gives it back. -/
theorem JAtZ.maybeReturnJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n i : U64} {x : Fl4Spec.Tcb}
    {xn : Fl4Spec.Notification} (ht : t ∈ Z.T) (hn : n ∈ Z.N) (hiC : i ∈ Z.C)
    (hk : σ.kheap t.bv = some (.tcb x)) (hkn : σ.kheap n.bv = some (.notification xn))
    (hsp : x.tcbSchedContext = some i.bv) (hxn : xn.ntfnSc = some i.bv) (hnr : Fl4Spec.runnable x.tcbState = false)
    (hnrw : ¬ P1.Runnable (L.mem s (P1.stA t)))
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    notification.maybe_return_sched_context st s n t ⦃ s' => ∃ σ',
      Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have htP : t ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact ht
  obtain ⟨⟨Q0, R0, h0⟩, -⟩ := J.blk
  exact WP.spec_mono (J.maybeReturnJQ ht hn hiC hk hkn hsp hxn (J.inv.notQueued hk hnr) (P1.blocked_out h0 htP hnrw)
    hsa hid) fun _ h => h.2

set_option maxHeartbeats 16000000 in
/-- **The blocking receive at `J` up to `maybe_return_sched_context`** (as
`JAtZ.recvSigBlockJ`, for any SC of the notification): `JAtZ` at the state
after `rsPre`, the thread blocked, a reschedule pending. -/
theorem JAtZ.recvSigBlockPreJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (hcov : (∀ k, Z.th n = some k → Covered (L.mem s) Z.G n.val (n.val + max (objSize k) 1)) ∧
      (∀ k, H n = some k → Covered (L.mem s) Z.G n.val (n.val + 2 ^ k.bits)))
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    Ipc.rsPre st s t n ⦃ s4 => ∃ σ3,
      Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ = Fl4Spec.maybeReturnSc n.bv t.bv σ3 ∧
      ¬ P1.Runnable (L.mem s4 (P1.stA t)) ∧
      σ3.kheap t.bv = some (.tcb { xt with tcbState := .blockedOnNotification n.bv }) ∧
      (∃ q, σ3.kheap n.bv = some (.notification { x with ntfnObj := .waitingNtfn q })) ∧
      σ3.schedulerAction = .chooseNewThread ∧ σ3.curThread = σ.curThread ∧ σ3.idleThread = σ.idleThread ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst (D \ {n}) s4 a σ3 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hres : σ.schedulerAction = .resumeCurThread := hni.2
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  have hr : Fl4Spec.runnable xt.tcbState = true := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
  have hnb3 : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    rcases runnable_code hr with h | h | h <;> rw [h] <;> decide
  have hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by rw [h] at hr; cases hr
  have hqE : ∀ e ∈ Z.E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue :=
    fun e he z hz => Endp.not_queued hI.1.toE ht hkt hnb3 e he z hz
  have hnqN : t.bv ∉ Fl4Spec.ntfnQueueOf x := not_member hI.1.toN ht hkt hnn n hn x hk
  have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ.kheap y = some (.tcb z) := fun y hy => by
    obtain ⟨z, hz, -⟩ := (J.sv.ntfnQ _ _ hk).2 y hy
    exact ⟨z, hz⟩
  obtain ⟨σ', heq, F, hik, -, hcn, hsrt⟩ := recvSigBlockPre_eq hkt hk hna hnqN hq hr (J.isorted.2 _ _ hk)
  have hcn' : σ'.schedulerAction = .chooseNewThread := hcn hcur.symm hres
  -- P1's `BlkOK` after
  have hcb := J.canBlockCur ht hcur hkt hr hni hnq
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have hx := hI.1.toN.at_ntfn hn hk
  have hst0 : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := Z.T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := Z.T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  have h3 : L.epState s n ≠ 3#u64 := by
    rw [epState_eq]
    rcases hst0 with h | h
    · rw [h, ntfn_consts.1]; decide
    · rw [h, ntfn_consts.2.1]; decide
  have hidW : L.idleW s ≠ t :=
    (J.words_of_spec ht (fun u hu => by rw [hres] at hu; cases hu) (by rw [← hcur]; exact hti)).2
  have h01 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64 := by
    rw [epState_eq]
    rcases hst0 with h | h
    · exact Or.inl (by rw [h, ntfn_consts.1])
    · exact Or.inr (by rw [h, ntfn_consts.2.1])
  have p1 := P1.ntfn_blockPre s t n Q0 R0 h0 hB0 hX0 hS0 hSg0 hcb hidW (J.zH.2.2.2 n hn) h01
  refine WP.spec_mono (WP.spec_and (receive_signal_preF J.ip s σ hI ht hkt hnn hqE hn hk hna
    (J.qsortedN n hn) cb rt) p1) ?_
  rintro s' ⟨⟨σ0, h0eq, hspec, hIR, hRB, hkn3, hkt3⟩, hbk⟩
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hbk.1, hbk.2.1, hbk.2.2.1, hbk.2.2.2.1, hbk.2.2.2.2.1⟩
  have hW : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hRB.mono fun b hb => RBW.cnW hS hb
  have hDbg := J.rbw_dbg hRB
  -- the assembly (as XTopJointSendBlock's `JAtZ.sendBlockJ`)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
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
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := ⟨fun u hu => (by rw [hcn'] at hu; cases hu), F.idleOK J.act.2⟩
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcn'
  have hrun3 : CurRunM σ' := Or.inl (by rw [hcn']; intro h; cases h)
  -- the dead: the thread is not dead (runnable); the notification leaves the dead set
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rcases runnable_code hr with h | h | h <;> rw [h] <;> decide)
  have hdead : ∀ q ∈ D \ {n}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ t.bv := htD q hq.1
    have hqn : q.bv ≠ n.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ?_) (fun x hx => F.epF hx) (fun x hx => ?_)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1 (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
      show st' = x.tcbState
      rcases hs' with e1 | ⟨e1, -⟩
      · exact e1
      · exact absurd e1 hqt
    · obtain ⟨y, hy, hc'⟩ := F.ntfnF hx
      rcases hc' with rfl | ⟨e1, -⟩
      · exact ⟨_, hy, Or.inl rfl, rfl, Or.inl rfl⟩
      · exact absurd e1 hqn
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {n})
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {n}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the thread's `RelIfBound` from a runnable state)
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, by rw [← hcur]; exact hC.notRel⟩
  obtain ⟨hIB, -⟩ := (J.inv.toBut t.bv).ik hnqT hik
  have hrib : RelIfBound σ' t.bv := Ipc.RelIfBound.of_keep (J.inv.rd t.bv xt hkt (Or.inl hr)) F.skeep
  have I3 : Inv σ' := hIB.inv fun _ _ _ => hrib
  -- `BlockedScActive`: the thread's SC is the current SC, active
  have hscA : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp).2⟩
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp hyt
    rw [hkt] at hku; cases hku
    have e1 : σ.curSc = q.bv := Option.some.inj (hscc.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {n}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted hsrt, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J3 := J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R
    (J.rbw_dbgKeep hRB) F.sk.orig (XTopAt.idleW_eqS J.xtop hX3 F.sk.idle) (J.zD_diffN hn)
  exact ⟨σ', hspec, hbk.2.2.2.2.2.1, hkt3, hkn3, hcn', F.sk.ct, F.sk.idle, _, J3⟩


set_option maxHeartbeats 4000000 in
/-- **The blocking receive at `J` that gives the SC back** (the former
`JRecvSigRetHyp` [W]): the current thread blocks on an idle or waiting
notification whose SC is the current SC (`hsc`); `JAtZ.recvSigBlockPreJ`,
then `JAtZ.maybeReturnJ` unbinds the SC (a reschedule is pending already). -/
theorem JAtZ.recvSigRetJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (hsc : x.ntfnSc = some σ.curSc)
    (hcov : (∀ k, Z.th n = some k → Covered (L.mem s) Z.G n.val (n.val + max (objSize k) 1)) ∧
      (∀ k, H n = some k → Covered (L.mem s) Z.G n.val (n.val + 2 ^ k.bits)))
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  obtain ⟨i, hiC, hib⟩ := J.nsc n hn x σ.curSc hk hsc
  have hx := hI.1.toN.at_ntfn hn hk
  have hst0 : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := Z.T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := Z.T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  refine receive_signal_split hst0 (J.recvSigBlockPreJ hAT hkt ht hcur hni hnq hn hk hna hcov cb rt) ?_
  rintro s4 ⟨σ3, hspec, hnrw, hkt3, ⟨q, hkn3⟩, hact3, -, hid3, V', J3⟩
  refine WP.spec_mono (J3.maybeReturnJ ht hn hiC hkt3 hkn3 (by rw [hib]; exact hscc) (by rw [hib]; exact hsc)
    (by rfl) hnrw (fun u hu => by rw [hact3] at hu; cases hu) (by rw [hid3, ← hcur]; exact hni.1)) ?_
  rintro s5 ⟨σ5, he5, Ac', Lst', J5⟩
  exact ⟨((), σ5), by rw [hspec, he5]; exact Set.mem_singleton _, J5.xtop.relTop, _, _, _, _, _, _, J5⟩

set_option maxHeartbeats 4000000 in
/-- **`JRecvSigHyp` at a resumed entry**: polling, an active notification,
the blocking receive (`JAtZ.recvSigBlockJ`) and the blocking receive giving
the SC back (`JAtZ.recvSigRetJ`), the held cap's slot covering the
notification (`JAtZ.cover_cap`). No premise left. -/
theorem jRecvSigHyp_of (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv)
    (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (blocking : Bool) :
    JRecvSigHyp (L := L) arI AR Z.th ct blocking s a σ := by
  rintro p b w rd ac hcr ⟨x, hk⟩ ⟨y, hy, hcv⟩
  have hac : ac = absCap (.Notification p b w rd) := hcr.abs
  subst hac
  obtain ⟨n, hn, h⟩ := J.obj.ntfn _ x hk
  rw [Sched.bv_inj h] at hn
  cases hact : x.ntfnObj with
  | activeNtfn b0 =>
    exact J.recvSigActiveJ hAT ht hcur hni hnq hn hk hact blocking b.bv (rightsOf w rd false false)
  | _ =>
    have hna : ∀ b', x.ntfnObj ≠ .activeNtfn b' := fun b' h => by rw [hact] at h; cases h
    cases blocking
    · exact J.recvSigPollJ ht hn hk hna b.bv (rightsOf w rd false false)
    · have hHn : H p = some .ntfn := J.zH.2.2.2 p hn
      have hfit := J.kern.heap.fits p _ hHn
      simp only [P1.HKind.bits] at hfit
      have hcov := J.cover_cap (P1.WritesIn.refl s _) hy (by rw [capAt_capV, hcv]) (fun h => by cases h)
        (ok_inj (phys_eq _).symm) rfl (range_ntfn p b w rd hfit) fun k hk' => by
          rw [hHn] at hk'; cases hk'
          exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
      by_cases hsc : x.ntfnSc = some σ.curSc
      · exact J.recvSigRetJ hAT ht hcur hni hnq hn hk hna hsc hcov b.bv (rightsOf w rd false false)
      · exact J.recvSigBlockJ hAT ht hcur hni hnq hn hk hna hsc hcov b.bv (rightsOf w rd false false)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_recvJE` with `jRecvSigHyp_of`**: the receiving syscalls at
`J` against `fl4HandleEvent rep`'s branches; the notification receive has no
premise left. -/
theorem dispatch_recvJS (rep : Bool) (hAT : P0.ArchTotal arI) (s : S) (a : A)
    (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (number : I64) (bl cr : Bool) (hn : RecvSys number bl cr)
    (hIpc : JRecvIpcHyp (L := L) arI AR Z.th ct bl s a σ) :
    syscall.dispatch_syscall st arI s a number ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) rep (recvSysOf bl cr)).run σ).1,
        y.1 = .ok () ∧ RJ (L := L) arI AR r.1 r.2 y.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  exact dispatch_recvJE arI rep hAT s a σ J hni hct hnq hvfh number bl cr hn hIpc
    (jRecvSigHyp_of hAT J hctT hcur hni hnq bl)

end

end

end Fl4Proofs.P3
