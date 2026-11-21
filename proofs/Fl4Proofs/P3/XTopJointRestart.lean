/-
P3 (DESIGN.md §9), TCB: **`sched::restart` at `J`** (`JAtZ.restartTcbJ`,
for Resume, WriteRegisters and CopyRegisters at `JAt`).

* `restartTail_frame`: the frame of `restart`'s tail after `cancel_ipc`
  (`Restart`, the sporadic unblock check, the SC's resume, the switch) from
  an `Inactive` thread: `ScTKw` at the thread, `LK` cutting no link, `FK`,
  `SOK`, `BK`.
* `restartTail_specJ`: the thread neither current nor idle, no switch
  pending, `CurInv`: `MidKn` (so `MidKn.mid3`) and `ActIdle` after.
* `RCn`, `restartTail_specCn`: a reschedule pending (CopyRegisters'
  target restart after the source, the current thread, suspended itself;
  the target may be the current thread): the reschedule stays pending and
  `CurOwnW`, `OffOK`, `ActIdle` are kept (`RCn.close`). The SC's resume
  postpones its thread only when the SC's head is not ready or not
  sufficient; `OffOK` rules that out for the current SC while time is
  consumed (`resume_keepR`), so `CurOwnW`'s owner is not postponed then.
  l4v: `restart_invs`, `restart_valid_sched` under any scheduler action.
* `JAtZ.undead`: a thread whose cap is in a slot leaves the dead set
  (`cover_cap` at the same state).
* `JAtZ.restartTailJ`: the tail as one SC step (`JAtZ.sc_frame`), FL4's side
  RestartTail's `restart_tail_kfoot`; the dead stay dead
  (`deadP_sc_stepQ`: the thread, set to `Restart`, is not among them); the
  current thread's facts by `restartTail_specCn` with a reschedule pending,
  else by `restartTail_specJ` (`CurInv` and the thread not current from
  `JAtZ.cur`/`JAtZ.curRun`).
* `JAtZ.restartTcbJ`: `sched::restart` at `J`. A running thread: nothing. A
  stopped one: first out of the dead set by its cap (`undead`), `cancel_ipc`
  by the four `JCancelAt` steps (the dead set kept), then the tail; P1's
  `BlkOK` and the node-0 debug word over the whole restart
  (`sched.restart.allK`). Premises at the start: no switch pending, the
  platform's `MIN_BUDGET` [P].
-/
import Fl4Proofs.P3.RestartTail
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScBsaOps
import Fl4Proofs.P3.ScJointKeep
import Fl4Proofs.P3.SpecNoSwitch
import Fl4Proofs.P3.SpecPPR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- `NSC` across an `ScTKw` step cutting no link. -/
theorem nsc_of_lk {N C : Set U64} {P : ObjRef → Prop} {σ σ' : State Unit} (h : NSC N C σ)
    (hK : ScTKw P σ σ') (hL : LK (fun _ => False) σ σ') : NSC N C σ' := by
  intro n hn y p hy hp
  obtain ⟨ko, hko, hn1, -⟩ := hK.kind_back hy
  obtain ⟨x, rfl⟩ := hn1 ⟨y, rfl⟩
  rcases hL n.bv with h0 | hl
  · exact h0.elim
  rw [hko, hy] at hl
  have hl' : LObj (.notification x) (.notification y) := hl
  obtain ⟨y', e, hsc⟩ := hl'.2.2 x rfl
  cases e
  rcases hsc with e | e
  · exact h n hn x p hko (e ▸ hp)
  · rw [e] at hp; cases hp

set_option maxHeartbeats 4000000 in
/-- **The frame of `restart`'s tail** (any current thread, any action):
`ScTKw` at the thread, `LK` cutting no link, `FK`, `SOK`, `BK`. -/
theorem restartTail_frame {σ σb σc σd σ' : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hin : x.tcbState = .inactive)
    (hb : setThreadState (Z := Unit) t .restart σ = ({((), σb)}, False))
    (hc : ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False))
    (hd : NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc = ({((), σd)}, False))
    (he : testPossibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False)) :
    ScTKw (fun p => p = t) σ σ' ∧ LK (fun _ => False) σ σ' ∧ FK σ σ' ∧ SOK (true, true) σ σ' ∧ BK σ σ' := by
  have mb : ((), σb) ∈ (setThreadState (Z := Unit) t .restart σ).1 := by rw [hb]; exact Set.mem_singleton _
  have mc : ((), σc) ∈ (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false) σb).1 := by
    show ((), σc) ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb).1
    rw [hc]; exact Set.mem_singleton _
  have md : ((), σd) ∈ (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc).1 := by
    rw [hd]; exact Set.mem_singleton _
  have me : ((), σ') ∈ (testPossibleSwitchTo (Z := Unit) t σd).1 := by rw [he]; exact Set.mem_singleton _
  have hσb : σb.kheap = (updK σ t (.tcb { x with tcbState := .restart })).kheap := by
    have e := the_result (Notif.setThreadState_eq (Z := Unit) .restart hk) hb
    rw [e, stsAct_kheap]
  have hf0 : IpcFree x.tcbState := by rw [hin]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have nc : NKT (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) :=
    nkt_ifCondRefillUnblockCheck _ _ _
  have nd : NKT (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    nkt_maybeM nkt_schedContextResume _
  have ne : NKT (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact nkt_bind (nkt_gets _) fun _ => nkt_when _ (nkt_possibleSwitchTo _)
  have hK : ScTKw (fun p => p = t) σ σ' :=
    (tk_setThreadState hk hf0 ipcFree_restart _ mb).trans
      (((nc σb _ mc).trans (nd σc _ md)).trans (ne σd _ me)).ofFalse
  have le : LKM (fun _ => False) (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact lkm_bind (lkm_gets _) fun _ => lkm_when _ (lkm_possibleSwitchTo _)
  have hL : LK (fun _ => False) σ σ' :=
    (((lkm_setThreadState t .restart σ _ mb).trans (lkm_ifCondRefillUnblockCheck _ _ _ σb _ mc)).trans
      (lkm_maybeM (fun p => lkm_schedContextResume p) _ σc _ md)).trans (le σd _ me)
  have fc : FKA (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) := by
    fk_auto
  have fd : FKA (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    fk_maybeM (fun p => by fk_auto) _
  have fe : FKA (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact fk_bind (fk_gets _) fun _ => fk_when _ (by fk_auto)
  have hF : FK σ σ' :=
    ((((fk_setThreadState t .restart) σ _ mb).trans (fc σb _ mc)).trans (fd σc _ md)).trans (fe σd _ me)
  have pe : Pres (true, true) (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo
    exact pres_bind (pres_gets (f := (true, true)) _) fun _ => pres_when (f := (true, true)) _
      (pres_possibleSwitchTo (f := (true, true)) _)
  have hsok : SOK (true, true) σ σ' :=
    ((((pres_setThreadState (f := (true, true)) t .restart) σ _ mb).trans
      ((pres_ifCondRefillUnblockCheck (f := (true, true)) _ _ _) σb _ mc)).trans
      ((pres_maybeM (f := (true, true)) (fun p => pres_schedContextResume (f := (true, true)) p) _) σc _ md)).trans
      (pe σd _ me)
  have hBb : BK σ σb := by
    refine ⟨fun u y hu hq => ?_, fun p y n hp ha => ?_⟩
    · rw [hσb] at hu
      by_cases e : u = t
      · subst e
        simp only [updK, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
        subst hu; simp [ipcQueuedThreadState] at hq
      · exact ⟨y, by simpa [updK, e] using hu, hq⟩
    · rw [hσb] at hp ⊢
      have hpt : p ≠ t := by rintro rfl; simp [updK] at hp
      exact ⟨y, by simpa [updK, hpt] using hp, ha, fun _ e => Or.inl e⟩
  have bc : BKM (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) :=
    bkm_of nc (MaxK.mk_ifCondRefillUnblockCheck' _ _ _)
  have bd : BKM (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    bkm_of nd (MaxK.mk_maybeM (fun p => by unf_ref; mk_auto) _)
  have be : BKM (testPossibleSwitchTo (Z := Unit) t) := by
    refine bkm_of ne ?_
    unfold testPossibleSwitchTo
    exact MaxK.mk_bind (MaxK.mk_gets _) fun _ => MaxK.mk_when _ (MaxK.mk_possibleSwitchTo' _)
  exact ⟨hK, hL, hF, hsok, hBb.trans (((bc σb _ mc).trans (bd σc _ md)).trans (be σd _ me))⟩

/-- **What `restart`'s tail keeps with a reschedule pending** (the thread
`t`, restarted, may be the current thread): the current SC, time, consumed
time and idle thread kept, the reschedule pending, every TCB's SC kept (and
all of a TCB other than `t`), the current SC's object kept (backwards), and
the release queue grown by `t` only, and then not as the current SC's
thread while time is consumed. -/
structure RCn (t : ObjRef) (x : Tcb) (σ σ' : State Unit) : Prop where
  csc : σ'.curSc = σ.curSc
  tm : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  act : σ'.schedulerAction = .chooseNewThread
  tcb : ∀ q xq, σ.kheap q = some (.tcb xq) → ∃ y, σ'.kheap q = some (.tcb y) ∧
    y.tcbSchedContext = xq.tcbSchedContext ∧ (q ≠ t → y = xq)
  sc : ∀ y n, σ'.kheap σ.curSc = some (.schedContext y n) → σ.kheap σ.curSc = some (.schedContext y n)
  rq : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue ∨
    (u = t ∧ (0 < σ.consumedTime → x.tcbSchedContext ≠ some σ.curSc))

/-- `set_thread_state` of `t` with a reschedule pending. -/
theorem RCn.init {t : ObjRef} {x : Tcb} {σ : State Unit} (hk : σ.kheap t = some (.tcb x))
    (hcn : σ.schedulerAction = .chooseNewThread) (ts : ThreadState) :
    RCn t x σ (updK σ t (.tcb { x with tcbState := ts })) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, hcn, fun q xq hq => ?_, fun y n hy => ?_, fun u hu => Or.inl hu⟩
  · by_cases e : q = t
    · subst e; rw [hk] at hq; cases hq
      exact ⟨{ x with tcbState := ts }, by simp [updK], rfl, fun h => (h rfl).elim⟩
    · exact ⟨xq, by simp [updK, e, hq], rfl, fun _ => rfl⟩
  · by_cases e : σ.curSc = t
    · rw [e] at hy ⊢; simp [updK] at hy
    · simpa [updK, e] using hy

/-- A further step: the heap changed only at SCs other than the current
one. -/
theorem RCn.next {t : ObjRef} {x : Tcb} {σ σ1 σ2 : State Unit} (h : RCn t x σ σ1)
    (hk : ∀ q, σ2.kheap q ≠ σ1.kheap q → (∃ y n, σ1.kheap q = some (.schedContext y n)) ∧ q ≠ σ1.curSc)
    (h1 : σ2.curSc = σ1.curSc) (h2 : σ2.curTime = σ1.curTime) (h3 : σ2.consumedTime = σ1.consumedTime)
    (h4 : σ2.idleThread = σ1.idleThread) (h5 : σ2.schedulerAction = .chooseNewThread)
    (hrq : ∀ u ∈ σ2.releaseQueue, u ∈ σ1.releaseQueue ∨
      (u = t ∧ (0 < σ.consumedTime → x.tcbSchedContext ≠ some σ.curSc)))
    (h6 : σ2.idleSc = σ1.idleSc := by first | rfl | assumption) :
    RCn t x σ σ2 := by
  refine ⟨h1.trans h.csc, h2.trans h.tm, h3.trans h.cons, h4.trans h.idle, h6.trans h.isc, h5, fun q xq hq => ?_,
    fun y n hy => ?_, fun u hu => ?_⟩
  · obtain ⟨y, hy, f1, f2⟩ := h.tcb q xq hq
    refine ⟨y, ?_, f1, f2⟩
    by_cases e : σ2.kheap q = σ1.kheap q
    · rw [e]; exact hy
    · obtain ⟨⟨y', n', hy'⟩, -⟩ := hk q e
      rw [hy] at hy'; cases hy'
  · by_cases e : σ2.kheap σ.curSc = σ1.kheap σ.curSc
    · rw [e] at hy; exact h.sc y n hy
    · exact absurd h.csc.symm (hk _ e).2
  · rcases hrq u hu with h' | h'
    · exact h.rq u h'
    · exact Or.inr h'

/-- **`CurOwnW`, `OffOK`, `ActIdle` after an `RCn` step.** -/
theorem RCn.close {T C : Set U64} {t : ObjRef} {x : Tcb} {σ σ' : State Unit} (R : RCn t x σ σ')
    (hk : σ.kheap t = some (.tcb x)) (hti : t ≠ σ.idleThread)
    (hO : OffOK σ) (hOw : CurOwnW T C σ) (hA : ActIdle σ) :
    CurOwnW T C σ' ∧ OffOK σ' ∧ ActIdle σ' := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hOw with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · obtain ⟨y, hy, e1, -⟩ := R.tcb _ xt hkt
      refine Or.inl ⟨u, hu, y, hy, by rw [e1, R.csc]; exact hxs, fun z n hz => ?_, fun h0 hm => ?_⟩
      · rw [R.csc] at hz; exact hown z n (R.sc z n hz)
      · rw [R.cons] at h0
        rcases R.rq _ hm with h | ⟨e, h⟩
        · exact hnr h0 h
        · rw [e, hk] at hkt; cases hkt
          exact h h0 hxs
    · exact Or.inr ⟨by rw [R.csc]; exact hcs, fun z n hz => by rw [R.csc] at hz; exact hun z n (R.sc z n hz)⟩
  · intro h0 y n hy ha
    rw [R.cons] at h0 ⊢; rw [R.tm]
    rw [R.csc] at hy; rw [R.csc, R.isc] at ha
    exact hO h0 y n (R.sc y n hy) ha
  unfold ActIdle
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [R.act] at hu; cases hu
  · obtain ⟨xi, h1, h2, h3, h4⟩ := hA.2
    obtain ⟨y, hy, -, e2⟩ := R.tcb _ xi h1
    have e := e2 (Ne.symm hti)
    subst e
    refine ⟨y, by rw [R.idle]; exact hy, by rw [R.isc]; exact h2, h3, fun hm => ?_⟩
    rw [R.idle] at hm
    rcases R.rq _ hm with h | ⟨e, -⟩
    · exact h4 h
    · exact hti e.symm

/-- The sporadic unblock check of `restart`, the SC not the current one when
it runs (as `unblockTest_cases`). -/
theorem unblockTest_casesC {σ σ' : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {r : Unit}
    (hm : (r, σ') ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (some p) σ).1) :
    σ' = σ ∨ (y.scSporadic = true ∧ p ≠ σ.curSc ∧ (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) := by
  change (r, σ') ∈ (ifCondRefillUnblockCheck (Z := Unit) (some p) (some false) (some false) σ).1 at hm
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hm
  dsimp only at hm
  rw [nd_bind_one (getSchedContext_eq hk), Notif.nd_gets_bind, Notif.nd_pure_bind'] at hm
  unfold NonDet.when at hm
  split at hm
  · rename_i hc
    split at hm
    · exact Or.inr ⟨by simpa using hc.1, by simpa using hc.2, hm⟩
    · left; exact congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
  · left; exact congrArg Prod.snd (Set.mem_singleton_iff.1 hm)

/-- `resume_keep` with the reason a thread is postponed: its SC active and
not released. -/
theorem resume_keepR {σ σ' : State Unit} {t p : ObjRef} (h : InvBut σ t) {x : Tcb} {y : SchedContext} {n : Nat}
    (kp : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (kt : σ.kheap t = some (.tcb x))
    (hxp : x.tcbSchedContext = some p) (hnq : NotQueued σ t)
    (he : schedContextResume (Z := Unit) p σ = ({((), σ')}, False)) :
    Calm σ σ' ∧ σ'.schedulerAction = σ.schedulerAction ∧ ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue ∨
      (u = t ∧ scActive y = true ∧
        ¬ (refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true)) := by
  have hne : scActive y = true → y.scRefills ≠ [] := h.ne p y n kp
  rw [resume_spec_eq kp hyt kt hne
    (fun hs => by
      obtain ⟨x', scp, y', m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
      rw [kt] at h1; cases h1; rw [hxp] at h2; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
    (fun _ => hnq.1 _ _)] at he
  split_ifs at he with hc
  · have hact : scActive y = true := by
      obtain ⟨x', scp, y', m, h1, h2, -, h4, h5, -⟩ := schedulable_inv hc.1
      rw [kt] at h1; cases h1; rw [hxp] at h2; cases h2; rw [kp] at h4; cases h4; exact h5
    obtain ⟨b, hp⟩ := postpone_eq kp hyt kt (specRt σ) (fun u hu => by
      rcases hu with rfl | hu
      · exact ⟨x, p, y, n, kt, hxp, kp, hne hact, specRt_eq kt hxp kp (hne hact)⟩
      · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := h.rel u hu
        exact ⟨xu, scp, yu, nu, h1, h2, h4, h.ne _ _ _ h4 h5, specRt_eq h1 h2 h4 (h.ne _ _ _ h4 h5)⟩)
    rw [hp] at he
    rw [pair_eq he]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, fun u hu => ?_⟩
    rcases mem_specInsT.1 hu with e | hu'
    · exact Or.inr ⟨e, hact, hc.2⟩
    · exact Or.inl hu'
  · rw [pair_eq he]
    exact ⟨Calm.refl σ, rfl, fun u hu => Or.inl hu⟩

/-- A sufficient head refill for some usage is sufficient for none. -/
theorem restart_suff0 {c : Time} {r : Refill} (h : refillSufficient c r = true) : refillSufficient 0 r = true := by
  apply suff0_of
  unfold refillSufficient refillCapacity at h
  simp only [decide_eq_true_eq] at h
  have hp := min_budget_pos
  split_ifs at h with hlt
  · bv_omega
  · bv_omega

set_option maxHeartbeats 8000000 in
/-- **The spec side of `restart`'s tail with a reschedule pending** (the
thread may be the current one, suspended by CopyRegisters): the reschedule
stays pending, `CurOwnW`, `OffOK`, `ActIdle` kept. A thread postponed by
the SC's resume while time is consumed is not the current SC's: `OffOK`
gives that SC a ready and sufficient head. -/
theorem restartTail_specCn {T C : Set U64} {σ σb σc σd σ' : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hin : x.tcbState = .inactive) (hti : t ≠ σ.idleThread)
    (hcn : σ.schedulerAction = .chooseNewThread) (hI : Inv σ) (hA : ActIdle σ) (hO : OffOK σ)
    (hOw : CurOwnW T C σ)
    (hsp : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scSporadic = true → scActive y = true)
    (hb : setThreadState (Z := Unit) t .restart σ = ({((), σb)}, False))
    (hc : ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False))
    (hd : NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc = ({((), σd)}, False))
    (he : testPossibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False)) (hId : Inv σd) :
    σ'.schedulerAction = .chooseNewThread ∧ CurOwnW T C σ' ∧ OffOK σ' ∧ ActIdle σ' := by
  have hnq : NotQueued σ t := by
    refine ⟨fun d p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rq d p t hm; rw [hk] at h1; cases h1; rw [hin] at h3; cases h3
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm; rw [hk] at h1; cases h1; rw [hin] at h3; cases h3
  have hσb : σb = updK σ t (.tcb { x with tcbState := .restart }) := by
    have e := the_result (Notif.setThreadState_eq (Z := Unit) .restart hk) hb
    rw [e]
    refine stsAct_eq_self fun h => ?_
    have h2 : σ.schedulerAction = .resumeCurThread := h.2.1
    rw [hcn] at h2; cases h2
  have R0 : RCn t x σ σb := by rw [hσb]; exact RCn.init hk hcn .restart
  obtain ⟨hIb, hnqb⟩ := (hI.toBut t).ik hnq ((ikm_setThreadState (t := t) .restart).of_eq hb)
  have hkb : σb.kheap t = some (.tcb { x with tcbState := .restart }) := by rw [hσb]; simp [updK]
  -- up to the switch
  have Rd : RCn t x σ σd := by
    cases hxs : x.tcbSchedContext with
    | none =>
      rw [hxs] at hc hd
      have hm : ((), σc) ∈ (ifCondRefillUnblockCheck (Z := Unit) none (some false) (some false) σb).1 := by
        show ((), σc) ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) none σb).1
        rw [hc]; exact Set.mem_singleton _
      unfold ifCondRefillUnblockCheck NonDet.maybeM at hm
      have ec : σc = σb := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      unfold NonDet.maybeM at hd
      have ed : σc = σd := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hd))
      rw [← ed, ec]; exact R0
    | some p =>
      rw [hxs] at hc hd
      obtain ⟨y, n, hky, hyt⟩ := hIb.back t _ p hkb hxs
      have hpt : p ≠ t := fun e => by rw [e, hkb] at hky; cases hky
      have hmc : ((), σc) ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (some p) σb).1 := by
        rw [hc]; exact Set.mem_singleton _
      have hcC : InvBut σc t ∧ NotQueued σc t ∧ σc.kheap t = σb.kheap t ∧ RCn t x σ σc := by
        rcases unblockTest_casesC hky hmc with e | ⟨hsy, hpc, hm'⟩
        · rw [e]; exact ⟨hIb, hnqb, rfl, R0⟩
        have hkbp : σb.kheap p = σ.kheap p := by rw [hσb]; simp [updK, hpt]
        have hne : y.scRefills ≠ [] := hIb.ne p y n hky (hsp p y n (by rw [← hkbp]; exact hky) hsy)
        refine ⟨hIb.unblock hky hne (fun _ _ u hu xu hku hsu => ?_) hm', ?_⟩
        · obtain ⟨y', n', hky', hyu⟩ := hIb.back u xu p hku hsu
          rw [hky] at hky'; cases hky'
          rw [hyt] at hyu; cases hyu
          exact hnqb.2 hu
        rcases unblock_result hky hne hm' with ⟨e, -⟩ | ⟨z, e, -⟩
        · rw [e]; exact ⟨hnqb, rfl, R0⟩
        · rw [e]
          refine ⟨⟨fun d q => hnqb.1 d q, hnqb.2⟩, by simp [updK, Ne.symm hpt],
            R0.next (fun q hq => ?_) rfl rfl rfl rfl R0.act (fun u hu => Or.inl hu)⟩
          by_cases eq : q = p
          · subst eq; exact ⟨⟨y, n, hky⟩, hpc⟩
          · exact absurd (by simp [updK, eq]) hq
      obtain ⟨hIc, hnqc, hktc, Rc⟩ := hcC
      have hkc : σc.kheap t = some (.tcb { x with tcbState := .restart }) := by rw [hktc]; exact hkb
      obtain ⟨yc, nc, hkyc, hytc⟩ := hIc.back t _ p hkc hxs
      have hd' : schedContextResume (Z := Unit) p σc = ({((), σd)}, False) := hd
      obtain ⟨hcal, hact, hrq⟩ := resume_keepR hIc hkyc hytc hkc hxs hnqc hd'
      refine Rc.next (fun q hq => absurd (by rw [hcal.1]) hq) hcal.2.2.1 hcal.2.2.2.1 hcal.2.2.2.2.1
        hcal.2.2.2.2.2.1 (by rw [hact]; exact Rc.act) (fun u hu => ?_) hcal.2.2.2.2.2.2.2.2
      rcases hrq u hu with h | ⟨e, hac, hnr⟩
      · exact Or.inl h
      refine Or.inr ⟨e, fun h0 hcur => ?_⟩
      rw [hxs] at hcur
      have hpc : p = σ.curSc := Option.some.inj hcur
      have hy0 : σ.kheap σ.curSc = some (.schedContext yc nc) := Rc.sc yc nc (by rw [← hpc]; exact hkyc)
      obtain ⟨g1, -, g3⟩ := hO h0 yc nc hy0 (fun _ => hac)
      exact hnr ⟨by rw [Rc.tm]; exact g3, restart_suff0 g1⟩
  -- the switch
  have R' : RCn t x σ σ' := by
    unfold testPossibleSwitchTo at he
    rw [nd_gets_bind] at he
    by_cases hs : schedulable t σd = true
    · rw [hs] at he
      have he' : possibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False) := he
      have hcal := possibleSwitchTo_calm hId hs he'
      have hq := possibleSwitchTo_qchange hId hs he'
      exact Rd.next (fun q hq' => absurd (by rw [hcal.1]) hq') hcal.2.2.1 hcal.2.2.2.1 hcal.2.2.2.2.1
        hcal.2.2.2.2.2.1 (possibleSwitchTo_cn hId hs he' Rd.act) (fun u hu => Or.inl (by rw [← hq.2.1]; exact hu))
        hcal.2.2.2.2.2.2.2.2
    · rw [show schedulable t σd = false by simpa using hs] at he
      have e : σ' = σd :=
        the_result (show NonDet.when (false = true) (possibleSwitchTo (Z := Unit) t) σd = ({((), σd)}, False) from rfl) he
      subst e; exact Rd
  exact ⟨R'.act, R'.close hk hti hO hOw hA⟩

set_option maxHeartbeats 4000000 in
/-- **The spec side of `restart`'s tail** (module docstring). -/
theorem restartTail_specJ {σ σb σc σd σ' : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hin : x.tcbState = .inactive)
    (hti : t ≠ σ.idleThread) (htc : t ≠ σ.curThread) (hns : ∀ u, σ.schedulerAction ≠ .switchThread u)
    (hI : Inv σ) (hA : ActIdle σ) (hC : CurInv σ)
    (hb : setThreadState (Z := Unit) t .restart σ = ({((), σb)}, False))
    (hc : ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False))
    (hd : NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc = ({((), σd)}, False))
    (he : testPossibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False)) (hId : Inv σd) :
    ScTKw (fun p => p = t) σ σ' ∧ LK (fun _ => False) σ σ' ∧ FK σ σ' ∧ SOK (true, true) σ σ' ∧ BK σ σ' ∧
      MidKn σ σ' ∧ ActIdle σ' := by
  have mb : ((), σb) ∈ (setThreadState (Z := Unit) t .restart σ).1 := by rw [hb]; exact Set.mem_singleton _
  have mc : ((), σc) ∈ (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false) σb).1 := by
    show ((), σc) ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb).1
    rw [hc]; exact Set.mem_singleton _
  have md : ((), σd) ∈ (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext σc).1 := by
    rw [hd]; exact Set.mem_singleton _
  have me : ((), σ') ∈ (testPossibleSwitchTo (Z := Unit) t σd).1 := by rw [he]; exact Set.mem_singleton _
  have hσb : σb = updK σ t (.tcb { x with tcbState := .restart }) := by
    have e := the_result (Notif.setThreadState_eq (Z := Unit) .restart hk) hb
    rw [e]; exact stsAct_eq_self (fun h => htc h.1)
  have hf0 : IpcFree x.tcbState := by rw [hin]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  -- the frame of the SC step
  have nc : NKT (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) :=
    nkt_ifCondRefillUnblockCheck _ _ _
  have nd : NKT (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    nkt_maybeM nkt_schedContextResume _
  have ne : NKT (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact nkt_bind (nkt_gets _) fun _ => nkt_when _ (nkt_possibleSwitchTo _)
  have hK : ScTKw (fun p => p = t) σ σ' :=
    (tk_setThreadState hk hf0 ipcFree_restart _ mb).trans
      (((nc σb _ mc).trans (nd σc _ md)).trans (ne σd _ me)).ofFalse
  have le : LKM (fun _ => False) (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact lkm_bind (lkm_gets _) fun _ => lkm_when _ (lkm_possibleSwitchTo _)
  have hL : LK (fun _ => False) σ σ' :=
    (((lkm_setThreadState t .restart σ _ mb).trans (lkm_ifCondRefillUnblockCheck _ _ _ σb _ mc)).trans
      (lkm_maybeM (fun p => lkm_schedContextResume p) _ σc _ md)).trans (le σd _ me)
  have fc : FKA (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) := by
    fk_auto
  have fd : FKA (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    fk_maybeM (fun p => by fk_auto) _
  have fe : FKA (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo; exact fk_bind (fk_gets _) fun _ => fk_when _ (by fk_auto)
  have hF : FK σ σ' :=
    ((((fk_setThreadState t .restart) σ _ mb).trans (fc σb _ mc)).trans (fd σc _ md)).trans (fe σd _ me)
  have pe : Pres (true, true) (testPossibleSwitchTo (Z := Unit) t) := by
    unfold testPossibleSwitchTo
    exact pres_bind (pres_gets (f := (true, true)) _) fun _ => pres_when (f := (true, true)) _
      (pres_possibleSwitchTo (f := (true, true)) _)
  have hsok : SOK (true, true) σ σ' :=
    ((((pres_setThreadState (f := (true, true)) t .restart) σ _ mb).trans
      ((pres_ifCondRefillUnblockCheck (f := (true, true)) _ _ _) σb _ mc)).trans
      ((pres_maybeM (f := (true, true)) (fun p => pres_schedContextResume (f := (true, true)) p) _) σc _ md)).trans
      (pe σd _ me)
  -- `BK`
  have hBb : BK σ σb := by
    rw [hσb]
    refine ⟨fun u y hu hq => ?_, fun p y n hp ha => ?_⟩
    · by_cases e : u = t
      · subst e
        simp only [updK, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
        subst hu; simp [ipcQueuedThreadState] at hq
      · exact ⟨y, by simpa [updK, e] using hu, hq⟩
    · have hpt : p ≠ t := by rintro rfl; simp [updK] at hp
      exact ⟨y, by simpa [updK, hpt] using hp, ha, fun _ e => Or.inl e⟩
  have bc : BKM (ifCondRefillUnblockCheck (Z := Unit) x.tcbSchedContext (some false) (some false)) :=
    bkm_of nc (MaxK.mk_ifCondRefillUnblockCheck' _ _ _)
  have bd : BKM (NonDet.maybeM (schedContextResume (Z := Unit)) x.tcbSchedContext) :=
    bkm_of nd (MaxK.mk_maybeM (fun p => by unf_ref; mk_auto) _)
  have be : BKM (testPossibleSwitchTo (Z := Unit) t) := by
    refine bkm_of ne ?_
    unfold testPossibleSwitchTo
    exact MaxK.mk_bind (MaxK.mk_gets _) fun _ => MaxK.mk_when _ (MaxK.mk_possibleSwitchTo' _)
  have hBK : BK σ σ' := hBb.trans (((bc σb _ mc).trans (bd σc _ md)).trans (be σd _ me))
  -- the current thread's facts: `MidK` up to the switch
  have mkb : MidK σ σb := by
    rw [hσb]
    exact MidK.upd hk (fun _ _ h => (h.elim htc hti).elim) (fun _ _ e => by cases e)
  have mkc : MidK σb σc := by
    cases hsc : x.tcbSchedContext with
    | none =>
      rw [hsc] at mc
      unfold ifCondRefillUnblockCheck NonDet.maybeM at mc
      have e := congrArg Prod.snd (Set.mem_singleton_iff.1 mc)
      simp only at e
      rw [e]; exact MidK.refl _
    | some p =>
      rw [hsc] at mc
      refine mka_ifCondRefillUnblockCheck p (some false) (some false) σb ?_ _ mc
      show p ≠ σb.curSc
      rw [hσb]
      show p ≠ σ.curSc
      intro e
      obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back t x p hk hsc
      obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
      obtain ⟨y2, n2, hy2, hy2t⟩ := hI.back _ xt σ.curSc hkt hxs
      rw [← e, hy1] at hy2; cases hy2
      exact htc (Option.some.inj (hy1t.symm.trans hy2t))
  have mkd : MidK σc σd := by
    cases hsc : x.tcbSchedContext with
    | none =>
      rw [hsc] at md
      have e : σd = σc := congrArg Prod.snd (Set.mem_singleton_iff.1 md)
      rw [e]; exact MidK.refl _
    | some p =>
      rw [hsc] at md mc
      refine mka_schedContextResume p σc ?_ _ md
      intro y n u hy hyu
      obtain ⟨y0, hy0, -, e0⟩ := MaxK.mk_ifCondRefillUnblockCheck' _ _ _ σb _ mc p y n hy
      obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back t x p hk hsc
      have hpt : p ≠ t := fun e => by rw [e, hk] at hy1; cases hy1
      have hkb : σb.kheap p = σ.kheap p := by rw [hσb]; exact Function.update_of_ne hpt _ _
      rw [hkb, hy1] at hy0; cases hy0
      rw [e0, hy1t] at hyu; cases hyu
      have m2 := mkb.trans mkc
      exact ⟨by rw [m2.idle]; exact hti, by rw [m2.ct]; exact htc⟩
  have mk : MidK σ σd := (mkb.trans mkc).trans mkd
  have hAd : ActIdle σd := by
    refine ⟨fun u hu => (hns u (mk.sw u hu)).elim, ?_⟩
    obtain ⟨xi, h1, h2, h3, h4⟩ := hA.2
    obtain ⟨y, hy, e1, e2⟩ := mk.idT xi h1
    refine ⟨y, by rw [mk.idle]; exact hy, by rw [e1, mk.isc]; exact h2, by rw [e2]; exact h3, fun hm => ?_⟩
    rw [mk.idle] at hm
    rcases mk.rq _ hm with h | ⟨h, -⟩
    · exact h4 h
    · exact h rfl
  -- the switch
  unfold testPossibleSwitchTo at he
  rw [nd_gets_bind] at he
  by_cases hs : schedulable t σd = true
  · rw [hs] at he
    have he' : possibleSwitchTo (Z := Unit) t σd = ({((), σ')}, False) := he
    have hmn := mkn_possibleSwitchTo ⟨by rw [mk.idle]; exact hti, by rw [mk.ct]; exact htc⟩ ((), σ')
      (by rw [he']; exact Set.mem_singleton _)
    exact ⟨hK, hL, hF, hsok, hBK, mk.toN.trans hmn, hAd.possibleSwitchTo hId hs he'⟩
  · rw [show schedulable t σd = false by simpa using hs] at he
    have e : σ' = σd :=
      the_result (show NonDet.when (false = true) (possibleSwitchTo (Z := Unit) t) σd = ({((), σd)}, False) from rfl) he
    subst e
    exact ⟨hK, hL, hF, hsok, hBK, mk.toN, hAd⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **A thread with a cap in a slot leaves the dead set** (`cover_cap` at the
same state). -/
theorem JAtZ.undead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x t : U64} (hxS : IsSlot Z.th x)
    (hc : capAt (L.mem s) x = ok (.Thread t)) (ht : t ∈ Z.T) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst (D \ {t}) s a σ := by
  have hw : P1.WritesIn st s s (TFoot st Z.T Z.N Z.C Z.c s σ) := P1.WritesIn.refl _ _
  have hK : ScTKw (fun _ => False) σ σ := ScTKw.refl _ σ
  have hHt : H t = some .tcb := J.zH.1 t ht
  have hfit := J.kern.heap.fits t _ hHt
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap hw hxS hc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl (range_thread t hfit)
    fun k hk' => by
      rw [hHt] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  exact { J with
    jcov := J.sc_jcov hw (fun q hq => J.jcov.dead q hq.1) (fun q hq hn => by
      have e : q = t := Classical.byContradiction fun e => hn ⟨hq, e⟩
      subst e; exact hcov) ⟨rfl, rfl⟩
    kern := J.sc_kern hw hK (FK.refl σ) J.xtop rfl Set.sdiff_subset
    zD := fun q hq => ⟨J.zD q hq, fun (e : q = t) => J.not_ztcb hxS
      (by rw [ok_inj ((capAt_capV _ _).symm.trans hc)]; intro _ _ _ h; cases h)
      (by rw [ok_inj ((capAt_capV _ _).symm.trans hc), e]; simp [absCap, Fl4Spec.objRefs]) hq⟩ }

set_option maxHeartbeats 16000000 in
/-- **`restart`'s tail at `J`** (module docstring). -/
theorem JAtZ.restartTailJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hin : x.tcbState = .inactive) (hns : ∀ u, σ.schedulerAction ≠ .switchThread u)
    (hRS : ∀ σb σc, Fl4Spec.setThreadState (Z := Unit) t.bv .restart σ = ({((), σb)}, False) →
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb = ({((), σc)}, False) →
      RelOK σc ∧ (∀ xc p, σc.kheap t.bv = some (.tcb xc) → xc.tcbSchedContext = some p →
        ∃ y n, σc.kheap p = some (.schedContext y n) ∧ y.scTcb = some t.bv) ∧
      ∀ σd, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) x.tcbSchedContext σc =
        ({((), σd)}, False) → Inv σd) :
    restartTailF st arI s a t ⦃ r => r.2 = a ∧ ∀ Ac', P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' r.1 →
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 →
      ∃ σ', specRestartTail t.bv x.tcbSchedContext σ = ({((), σ')}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.1 a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hti : t.bv ≠ σ.idleThread := fun e => by
    obtain ⟨xi, hki, -, hti, -⟩ := J.act.2
    rw [← e, hk] at hki; cases hki; rw [hin] at hti; cases hti
  have hq : ∀ n ∈ Z.N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue := by
    intro n _ z hz hm
    obtain ⟨xu, hku, hsu⟩ := (J.sv.ntfnQ n.bv z hz).2 t.bv hm
    rw [hk] at hku; cases hku; rw [hin] at hsu; cases hsu
  have hrq : ∀ d p, t.bv ∉ σ.readyQueues d p := by
    intro d p hm
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rq d p t.bv hm
    rw [hk] at h1; cases h1; rw [hin] at h3; cases h3
  refine WP.spec_mono (restart_tail_kfoot s a σ hR hS ht hk hin hq hrq hRS hmb) ?_
  rintro ⟨s', a'⟩ ⟨ha', σb, σc, σd, σ', hb, hc, hd, he, hR', hS', hI', hw⟩
  simp only at ha' hR' hS' hw ⊢
  subst a'
  refine ⟨rfl, fun Ac' hblk hKd0 => ⟨σ', specRestartTail_eq hb hc hd he, ?_⟩⟩
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hKd0.2 _ (Or.inr ⟨0#u64, J.kern.cs0, rfl⟩)
  have hId : Inv σd := (hRS σb σc hb hc).2.2 σd hd
  obtain ⟨hK, hL, hF, hsok, hBK⟩ := restartTail_frame hk hin hb hc hd he
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT hK hS' hR' id
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hsok⟩
  -- the current thread's facts: a reschedule pending (`restartTail_specCn`), or resumed (`MidKn.mid3`)
  have hcase : σ.schedulerAction = .chooseNewThread ∨ (t.bv ≠ σ.curThread ∧ CurInv σ) := by
    cases e : σ.schedulerAction with
    | chooseNewThread => exact Or.inl rfl
    | switchThread u => exact (hns u e).elim
    | resumeCurThread =>
      right
      have hC : CurInv σ := J.cur.resolve_left (by rw [e]; intro h; cases h)
      refine ⟨fun htc => ?_, hC⟩
      rcases J.curRun.resolve_left (fun h => h e) with hrun | hidl
      · have h1 := hrun x (htc ▸ hk); rw [hin] at h1; cases h1
      · exact hti (htc.trans hidl)
  have hsch : (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T Z.C σ' ∧ OffOK σ' ∧
      ActIdle σ' ∧ CurRunM σ' := by
    rcases hcase with hcn | ⟨htc, hC⟩
    · obtain ⟨h1, h2, h3, h4⟩ :=
        restartTail_specCn hk hin hti hcn J.inv J.act J.off J.own J.sv.scSpor hb hc hd he hId
      exact ⟨Or.inl h1, h2, h3, h4, Or.inl (by rw [h1]; intro h; cases h)⟩
    obtain ⟨-, -, -, -, -, hMK, hAI⟩ := restartTail_specJ hk hin hti htc hns J.inv J.act hC hb hc hd he hId
    obtain ⟨hC', hOw', hO'⟩ := hMK.mid3 hC J.off J.inv ⟨L.curW s, J.thT _ J.kern.curT, J.kern.cur.symm⟩
    have hcr : CurRunM σ' := by
      by_cases hr : σ'.schedulerAction = .resumeCurThread
      · have h0 : σ.schedulerAction = .resumeCurThread := by
          cases e : σ.schedulerAction with
          | resumeCurThread => rfl
          | switchThread u => exact (hns u e).elim
          | chooseNewThread => rw [hMK.cn e] at hr; cases hr
        right
        rcases J.curRun.resolve_left (fun h => h h0) with hrun | hidl
        · left
          intro y hy
          obtain ⟨xt, hkt, -, -⟩ := hC.tcb
          obtain ⟨y', hy', -, e⟩ := hMK.ctT xt hkt
          rw [hMK.ct, hy'] at hy; cases hy
          rw [e]; exact hrun xt hkt
        · right; rw [hMK.ct, hMK.idle]; exact hidl
      · exact Or.inl hr
    exact ⟨hC', Or.inl (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI')), hO', hAI, hcr⟩
  obtain ⟨hC', hOw', hO', hAI, hcr⟩ := hsch
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK (fun _ hp => absurd (show q = t from P1.eq_of_bv hp) (fun e => htD (e ▸ hq)))
      hL hF hAI.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2))
    (J.sc_kern hwT hK hF hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hC'
    hOw' hO' hAI (J.bsa.bk hBK hsok) hcr hblk
    hKd0 (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩

set_option maxHeartbeats 16000000 in
/-- **`sched::restart` at `J`** (module docstring), the target not dead
(`htD`; `JAtZ.restartTcbJ` from its cap in a slot by `JAtZ.undead`). -/
theorem JAtZ.restartTcbJD (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    (hns : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    sched.restart st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb t ht
  -- P1's `BlkOK` and the debug word across the whole restart
  have hP1 : sched.restart st arI s a t ⦃ r => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 ⦄ := by
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := J.blk
    refine WP.spec_mono (P1.sched.restart.allK hAT s a t Q R h0 htH hB hX hS) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    try simp only [WP.uncurry'_pair] at hr
    obtain ⟨Q', R', h1, hB1, hX1, hS1, -, hF⟩ := hr
    exact ⟨⟨⟨Q', R', h1⟩, hB1, hX1, hS1, ⟨hSg.sub, fun b hb => by rw [hF.1]; exact hSg.ks b hb,
      fun o h1' h2' => by rw [hF.1]; exact hSg.ksΩ o h1' h2'⟩⟩, J.kw_dbgKeep hF⟩
  -- the debug word and the kernel-state base through `cancel_ipc`
  obtain ⟨⟨Q0, R0, h0⟩, -, ⟨hO, hR, -⟩, -, hSg⟩ := J.blk
  have hreply : L.mem s (P1.stA t) = sched.TS_BLOCKED_ON_REPLY → P1.ReplyT st (P1.Heap.replies H)
      (P1.Heap.scs H) s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t htH hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  have hkwc : ipc.cancel_ipc st arI s a t ⦃ r => L.ksb r.1 = L.ksb s ∧
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 ⦄ := by
    refine WP.spec_mono (P1.ipc.cancel_ipc.kw s a t h0 htH hO hSg.sub hreply
      (fun h1 h2 => (hR.recv t htH h1 h2).1)) fun r hr => ?_
    obtain ⟨s1, a1⟩ := r
    try simp only [WP.uncurry'_pair] at hr
    exact ⟨hr.1, J.kw_dbgKeep hr⟩
  have hspec0 : Fl4Spec.restart (Z := Unit) t.bv σ =
      Fl4Spec.NonDet.when (¬ Fl4Spec.runnable x.tcbState = true ∧ ¬ Fl4Spec.idle x.tcbState) (do
        Fl4Spec.cancelIpc t.bv
        Fl4Spec.setThreadState t.bv .restart
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck x.tcbSchedContext
        Fl4Spec.NonDet.maybeM Fl4Spec.schedContextResume x.tcbSchedContext
        Fl4Spec.testPossibleSwitchTo t.bv) σ := by
    unfold Fl4Spec.restart
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (getTcbObjRef_eq _ hk)]
  have hmain : sched.restart st arI s a t ⦃ r => ∀ Ac', P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' r.1 →
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 →
      r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
    unfold sched.restart
    rw [is_stopped_eq (ts := x.tcbState) hTR.st]
    simp only [bind_ok]
    by_cases hc : ¬ Fl4Spec.runnable x.tcbState = true ∧ ¬ Fl4Spec.idle x.tcbState
    swap
    · rw [decide_eq_false hc]
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      intro _ _ _
      refine ⟨trivial, σ, ?_, Z.vs, Ac, Lst, D, J⟩
      rw [hspec0, Fl4Spec.NonDet.when, if_neg hc]; rfl
    rw [decide_eq_true hc]
    simp only [↓reduceIte]
    have hnr : Fl4Spec.runnable x.tcbState = false := by simpa using hc.1
    -- `cancel_ipc`, the dead set kept (without `t`)
    have hcan : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σa,
        Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σa)}, False) ∧ ∃ xa, σa.kheap t.bv = some (.tcb xa) ∧
        xa.tcbState = .inactive ∧ ∃ (V : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac1 Lst1 D r.1 r.2 σa ⦄ := by
      by_cases hfree : IpcFree x.tcbState
      · have hin : x.tcbState = .inactive := by
          revert hfree hc
          cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked, Fl4Spec.runnable, Fl4Spec.idle]
        refine WP.spec_mono (J.cancelFreeJ ht hk hfree) ?_
        rintro r ⟨h1, h2, V, J1⟩
        exact ⟨h1, _, h2, { x with tcbFault := none }, by simp [updK], hin, V, Ac, Lst, J1⟩
      have hcases : (∃ e d, x.tcbState = .blockedOnSend e d) ∨ (∃ e r d, x.tcbState = .blockedOnReceive e r d) ∨
          (∃ n, x.tcbState = .blockedOnNotification n) ∨ (∃ r, x.tcbState = .blockedOnReply r) := by
        revert hfree
        cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked]
      have hP : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ =
          ({((), σ')}, False) ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
            JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
        rcases hcases with h | h | h | h
        · exact hSd Z H Cs Ac Lst D s a σ rfl J t ht x hk h
        · exact hRv Z H Cs Ac Lst D s a σ rfl J t ht x hk h
        · exact hNt Z H Cs Ac Lst D s a σ rfl J t ht x hk h
        · exact hRp Z H Cs Ac Lst D s a σ rfl J t ht x hk h
      refine WP.spec_mono (WP.spec_and hP (cancel_ipc_irelP (ar := arI) hP0 (removeTcbHypP_ok hP0) s a σ hI ht hk
        J.sv J.obj J.inv (fun hfr => removeTcbOK_fault hP0 hI ht hk hfr J.removeTcbOK))) ?_
      rintro r ⟨⟨h1, σ1, h2, V, Ac1, Lst1, J1⟩, -, σ1', x1, h2', -, hk1, hs1⟩
      have e1 : σ1' = σ1 := by
        rw [h2] at h2'; exact ((Prod.mk.inj (Set.singleton_injective (congrArg Prod.fst h2'))).2).symm
      subst e1
      have hin : x1.tcbState = .inactive := by
        rw [hs1]; revert hfree; cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked, cancelSt]
      exact ⟨h1, σ1', h2', x1, hk1, hin, V, Ac1, Lst1, J1⟩
    refine WP.spec_bind (WP.spec_and hcan hkwc) ?_
    rintro ⟨s1, a1⟩ ⟨⟨h1, σa, hca, xa, hka, hina, V1, Ac1, Lst1, J1⟩, hks1, hd1⟩
    simp only at h1 hks1 hd1
    subst a1
    -- the spec facts after `cancel_ipc`
    have hma : ((), σa) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [hca]; exact Set.mem_singleton _
    have hKa := TscK.sk_cancelIpc t.bv σ ((), σa) hma
    have hxsa : xa.tcbSchedContext = x.tcbSchedContext := by
      obtain ⟨y0, hy0, e⟩ := hKa.1 _ _ hka; rw [hk] at hy0; cases hy0; exact e
    have hnsa : ∀ u, σa.schedulerAction ≠ .switchThread u :=
      (Vs.ak_cancelIpc' t.bv).noSwitch (x := ((), σa)) hma hns
    have hRS0 : RestartSpecOK t.bv σ := Sched.restartSpecOK_of J.inv J.sv.scSpor
    have hRS : ∀ σb σc, Fl4Spec.setThreadState (Z := Unit) t.bv .restart σa = ({((), σb)}, False) →
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) xa.tcbSchedContext σb = ({((), σc)}, False) →
        RelOK σc ∧ (∀ xc p, σc.kheap t.bv = some (.tcb xc) → xc.tcbSchedContext = some p →
          ∃ y n, σc.kheap p = some (.schedContext y n) ∧ y.scTcb = some t.bv) ∧
        ∀ σd, Fl4Spec.NonDet.maybeM (Fl4Spec.schedContextResume (Z := Unit)) xa.tcbSchedContext σc =
          ({((), σd)}, False) → Inv σd := by
      intro σb σc hb hc'
      rw [hxsa] at hc' ⊢
      exact hRS0 x σa σb σc hk hnr hca hb hc'
    show restartTailF st arI s1 a t ⦃ _ ⦄
    refine WP.spec_mono (J1.restartTailJ hmb ht htD hka hina hnsa hRS) ?_
    rintro r ⟨hr2, hr⟩ Ac' hblk hd6
    obtain ⟨σ', he', Lst', J'⟩ := hr Ac' hblk (dbgKeep_cancel hd1 hd6)
    refine ⟨hr2, σ', ?_, V1, Ac', Lst', D, by rw [hr2]; exact J'⟩
    rw [hspec0, Fl4Spec.NonDet.when, if_pos hc, nd_bind_one hca]
    rw [hxsa] at he'
    exact he'
  refine WP.spec_mono (WP.spec_and hP1 hmain) ?_
  rintro ⟨s6, a6⟩ ⟨⟨hb6, hd6⟩, hM⟩
  exact hM Ac hb6 hd6

/-- **`sched::restart` at `J`** (`JAtZ.restartTcbJD` after `JAtZ.undead`):
the target's cap in a slot. -/
theorem JAtZ.restartTcbJ (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) {x0 : U64}
    (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s) x0 = ok (.Thread t))
    (hns : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    sched.restart st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.restart (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  (J.undead hxS hcap ht).restartTcbJD hAT hSd hNt hRv hRp hmb ht (fun h => h.2 rfl) hns

end

end

end Fl4Proofs.P3
