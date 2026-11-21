/-
P3 (DESIGN.md §9), IPC: **a send to a waiting receiver without an SC, with
the caller's SC donated** (toward XTopJointSendCall's `JSendRecvHyp`): the
non-call send of an unfaulted caller with `can_donate` to a head receiver
that has no SC. FL4 (and l4v `send_ipc`) gives the receiver the caller's SC,
which is the current SC: `schedcontext::donate` unbinds the caller (in no
queue, so its dequeue and release-queue removal do nothing), asks a
reschedule (the caller is current), and binds the SC to the receiver.

* `dnSt`: the spec's `sched_context_donate` of the current SC from the
  current thread `t` to `d` (`donate_cur_eq`), and what it keeps (`dn_skD`,
  `dn_ksub`, ..., `dn_inv`, `dn_bsa`, `dn_own`: `d` owns the current SC
  after); `dn_swap`: the receiver's `Running` after the donation is the
  donation after the `Running`.
* `schedcontext.donate.kwAX` (P1): `donate`'s writes inside `KW` from a
  thread in no queue, with `SchedQueuesInvX` (P1's `donate.kwA` asks
  `BlkOK`; the dequeued receiver is the hole here).
* `JAtZ.wake_postG`: XTopJointSendCall's `JAtZ.wake_postCI` for any spec
  step after the `DWFr` frame, given its frame facts and the scheduler
  invariants after.
* `JAtZ.sendDonJ`: XTopJointSendRecv's `JAtZ.sendRecvJ0` with the
  donation: FL4's `donate_bound_refines` lifted by `tk_lift`, P1's
  `donate.ipc` and `donate.kwAX`, the spec's outcome `donate_cur_eq`, then
  the receiver `Running`, `JAtZ` by `wake_postG` at `dnSt`, the tail.
-/
import Fl4Proofs.P3.XTopJointSendCall
import Fl4Proofs.P3.IpcSendDon
import Fl4Proofs.P1.QueueReplyKw
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

/-! ## P1: the donation's footprint from a thread in no queue -/

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {Es : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`donate`'s writes inside `KW`** when the SC's thread `fr` is in no
queue and the receiver sits on the SC's core (`donate.kwA` with
`SchedQueuesInvX`: the dequeue and release-queue removal of `fr` do nothing). -/
theorem schedcontext.donate.kwAX {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64}
    (s : S) (a : A) (sc dst fr : U64) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hfr : fr ∈ T) (htcb : L.mem s (scTcbA sc) = fr)
    (hfout : (L.mem s (inqA fr) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA fr) &&& sched.Q_RELEASE) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ =>
      L.mem s (affA dst) = L.mem s (scCoreA sc) → Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  have hdA : Aligned (affA dst) := by rw [affA_eq]; exact field_aligned (hT dst hdst) (by simp) (by simp)
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => Foot st T Cs ∅ ∅ Z ∅ s r.1 ∧
      L.mem r.1 (affA dst) = L.mem s (affA dst) ∧ ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X r.1 Q1 R1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨Foot.refl _, rfl, _, _, h⟩
    have hi : i = fr := ei.trans htcb
    subst hi
    refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.all hA s a i h hB hX hS hSg)
      (smp.remote_tcb_stall.spec hA s a i)) ?_
    rintro ⟨s2, a2⟩ ⟨⟨h2, -, -, -, -, -, -, -, -, f2, -⟩, hs2⟩
    try simp only [WP.uncurry'_pair] at hs2 ⊢
    have f2' : Foot st T Cs ∅ ∅ Z ∅ s s2 := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · exact Foot.refl _
      · exact foot_node (h.nodes _ h.cur) h.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) (by rw [ipi_val]; omega)
    have g2 : L.mem s2 (affA dst) = L.mem s (affA dst) := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · rfl
      · exact L.mem_wr_ne (nodeAt_aligned (h.nodes _ h.cur) (by rw [ipi_val]; omega) (by rw [ipi_val])) hdA
          (fun e => node_ne_field (h.nodes _ h.cur) (by rw [ipi_val]; omega) hdst (hT dst hdst) (K := 3520#u64)
            (by simp) (UScalar.eq_of_val_eq e))
    have iq2 : L.mem s2 (inqA i) = L.mem s (inqA i) := by rw [inqA_eq]; exact f2 i hfr _ (by simp) (by simp)
    refine WP.spec_bind (sched.dequeue.noop s2 i (by rw [iq2]; exact hfout.1)) fun s3 e3 => ?_
    subst e3
    refine WP.spec_bind (sched.release_remove.noop s3 i (by rw [iq2]; exact hfout.2)) fun s4 e4 => ?_
    subst e4
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) h2 hfr (by simp) (by simp) (by simp)
    have f5 : Foot st T Cs ∅ ∅ Z ∅ s4 (L.wr s4 (scA i) 0#u64) := by
      rw [scA_eq]; exact foot_field hT hfr (by simp) (by simp) (by simp) (by simp)
    have g5 : L.mem (L.wr s4 (scA i) 0#u64) (affA dst) = L.mem s4 (affA dst) := by
      rw [scA_eq]
      exact L.mem_wr_ne (field_aligned (hT i hfr) (by simp) (by simp)) hdA
        (fun e => field_ne (K1 := 3464#u64) (K2 := 3520#u64) (hT i hfr) (hT dst hdst) (by simp) (by simp)
          (fun _ => by simp) (UScalar.eq_of_val_eq e))
    have f05 : Foot st T Cs ∅ ∅ Z ∅ s (L.wr s4 (scA i) 0#u64) := f2'.trans f5
    have g05 : L.mem (L.wr s4 (scA i) 0#u64) (affA dst) = L.mem s (affA dst) := g5.trans g2
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => Foot st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        L.mem s6 (affA dst) = L.mem (L.wr s4 (scA i) 0#u64) (affA dst) ∧
        ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s6 Q1 R1) ?_
      fun s6 ⟨f6, g6, q6⟩ => (WP.spec_ok _).2 ⟨f05.trans f6, g6.trans g05, q6⟩
    have RR : sched.reschedule_required st (L.wr s4 (scA i) 0#u64) ⦃ s6 =>
        Foot st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        L.mem s6 (affA dst) = L.mem (L.wr s4 (scA i) 0#u64) (affA dst) ∧
        ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s6 Q1 R1 ⦄ :=
      WP.spec_mono (WP.spec_and (WP.spec_and (sched.reschedule_required.kw (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅)
        _ q5) (sched.reschedule_required.inv _ _ _ q5)) (sched.reschedule_required.aff _ _ _ q5 hdst))
        fun s6 ⟨⟨f6, ⟨Q6, h6⟩, _, _⟩, g6⟩ => ⟨f6, g6, _, _, h6⟩
    split
    · exact RR
    · step with sched.action.spec as ⟨i1, ei1⟩
      split
      · exact RR
      · exact (WP.spec_ok _).2 ⟨Foot.refl _, rfl, _, _, q5⟩
  rintro ⟨s1, a1⟩ ⟨f1, g1, Q1, R1, h1⟩
  try simp only [WP.uncurry'_pair]
  have D1 : DbgTz st T Cs s1 := Foot0.dbg hT h.nodes f1 hX.dbg
  have c1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) := Foot0.out hT h.nodes f1 (h.omega _ hcO)
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst
    (by rw [c1]; exact hX.2.2.core sc hsc)) ?_
  rintro ⟨s', a'⟩ ⟨-, wq⟩
  try simp only [WP.uncurry'_pair] at wq ⊢
  intro he
  refine (Foot.of0 (Sg := Sg) (Scs := Scs) (Es := Es) f1).trans ((wq (by rw [g1, c1]; exact he)).mono fun b hb => ?_)
  rcases hb with rfl | rfl
  · exact kw_sg (hO.fixW sc hsc).1
  · rw [scA_eq]; exact kw_field hdst (by simp) (by simp) (by simp)

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The donation on the spec side -/

section Spec
open Fl4Spec

/-- The SC `p` of the current thread `t` donated to `d` (the spec's
`sched_context_donate`: `t` unbound, a reschedule, then `p` bound to `d`). -/
def dnSt (σ : State Unit) (t d p : ObjRef) (xt xd : Tcb) (y : SchedContext) (n : Nat) : State Unit :=
  donSt { updK σ t (.tcb { xt with tcbSchedContext := none }) with schedulerAction := .chooseNewThread } p d y n xd

/-- `reschedule_required` without a switch candidate only asks a reschedule. -/
theorem rescheduleRequired_nsw {σ : State Unit} (h : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    rescheduleRequired (Z := Unit) σ = ({((), { σ with schedulerAction := .chooseNewThread })}, False) := by
  unfold rescheduleRequired
  rw [nd_gets_bind]
  cases e : σ.schedulerAction with
  | switchThread u => exact absurd e (h u)
  | resumeCurThread => dsimp only; first | rfl | (rw [nd_pure_bind']; rfl)
  | chooseNewThread => dsimp only; first | rfl | (rw [nd_pure_bind']; rfl)

/-- `test_reschedule` of the current thread, resumed. -/
theorem testReschedule_cur {σ : State Unit} {t : ObjRef} (hct : t = σ.curThread)
    (hres : σ.schedulerAction = .resumeCurThread) :
    testReschedule (Z := Unit) t σ = ({((), { σ with schedulerAction := .chooseNewThread })}, False) := by
  unfold testReschedule
  rw [nd_gets_bind, nd_gets_bind, nd_pure_bind']
  unfold NonDet.when
  rw [if_pos (Or.inl hct)]
  exact rescheduleRequired_nsw (fun u e => by rw [hres] at e; cases e)

theorem setQ_self (σ : State Unit) (dm : Domain) (pr : Priority) : setQ σ dm pr (σ.readyQueues dm pr) = σ := by
  unfold setQ
  have : (fun d' p' => if d' = dm ∧ p' = pr then σ.readyQueues dm pr else σ.readyQueues d' p') = σ.readyQueues := by
    funext d' p'
    split_ifs with h
    · rw [h.1, h.2]
    · rfl
  rw [this]

/-- **The spec's donation of the current thread's SC** (in no queue, resumed). -/
theorem donate_cur_eq {σ : State Unit} {t d p : ObjRef} {xt xd : Tcb} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd))
    (hkp : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (htd : t ≠ d) (hpt : p ≠ t)
    (hpd : p ≠ d) (hct : t = σ.curThread) (hnq : NotQueued σ t)
    (hres : σ.schedulerAction = .resumeCurThread) :
    schedContextDonate (Z := Unit) p d σ = ({((), dnSt σ t d p xt xd y n)}, False) := by
  have hQ : setQ σ xt.tcbDomain xt.tcbPriority (tcbSchedDequeue t (σ.readyQueues xt.tcbDomain xt.tcbPriority)) = σ := by
    have h1 : tcbSchedDequeue t (σ.readyQueues xt.tcbDomain xt.tcbPriority) =
        σ.readyQueues xt.tcbDomain xt.tcbPriority := by
      unfold tcbSchedDequeue
      exact List.filter_eq_self.2 fun a ha => by
        have : t ≠ a := fun e => hnq.1 _ _ (e ▸ ha)
        simpa using this
    rw [h1, setQ_self]
  set σ1 : State Unit := { updK σ t (.tcb { xt with tcbSchedContext := none }) with
    schedulerAction := .chooseNewThread } with hσ1
  have hkp1 : σ1.kheap p = some (.schedContext y n) := by simp [σ1, updK, hpt, hkp]
  have hkd2 : (updSc σ1 p { y with scTcb := some d } n).kheap d = some (.tcb xd) := by
    simp [σ1, updK, Ne.symm hpd, Ne.symm htd, hkd]
  unfold schedContextDonate
  rw [nd_bind_one (getScObjRef_eq hkp _), hyt]
  unfold NonDet.when
  rw [if_pos (by simp)]
  have hin : (do
      let fromTptr ← NonDet.assertOpt (some t)
      tcbSchedAction tcbSchedDequeue fromTptr
      tcbReleaseRemove fromTptr
      setTcbObjRef tcbSchedContextUpdate fromTptr none
      testReschedule fromTptr : SMonad Unit Unit) σ = ({((), σ1)}, False) := by
    rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl)]
    rw [nd_bind_one (tcbSchedAction_gen hkt _), hQ]
    rw [nd_bind_one (tcbReleaseRemove_not hnq.2)]
    show (threadSet _ t >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hkt)]
    exact testReschedule_cur hct hres
  rw [nd_bind_one hin]
  show (updateSchedContext p _ >>= _) σ1 = _
  rw [nd_bind_one (updateSchedContext_eq hkp1 _)]
  show threadSet _ d _ = _
  exact threadSet_eq _ hkd2

section Dn
variable {σ : State Unit} {t d p : ObjRef} {xt xd : Tcb} {y : SchedContext} {n : Nat}

theorem dn_kd : (dnSt σ t d p xt xd y n).kheap d = some (.tcb { xd with tcbSchedContext := some p }) := by
  simp [dnSt, donSt, updK]

theorem dn_kp (hpd : p ≠ d) :
    (dnSt σ t d p xt xd y n).kheap p = some (.schedContext { y with scTcb := some d } n) := by
  simp [dnSt, donSt, updK, hpd]

theorem dn_kt (htd : t ≠ d) (hpt : p ≠ t) :
    (dnSt σ t d p xt xd y n).kheap t = some (.tcb { xt with tcbSchedContext := none }) := by
  simp [dnSt, donSt, updK, htd, Ne.symm hpt]

theorem dn_ko {q : ObjRef} (h1 : q ≠ t) (h2 : q ≠ d) (h3 : q ≠ p) :
    (dnSt σ t d p xt xd y n).kheap q = σ.kheap q := by
  simp [dnSt, donSt, updK, h1, h2, h3]

theorem dn_skD : SkD σ (dnSt σ t d p xt xd y n) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem dn_rel : (dnSt σ t d p xt xd y n).releaseQueue = σ.releaseQueue := rfl
theorem dn_rq : (dnSt σ t d p xt xd y n).readyQueues = σ.readyQueues := rfl
theorem dn_act : (dnSt σ t d p xt xd y n).schedulerAction = .chooseNewThread := rfl
theorem dn_ct : (dnSt σ t d p xt xd y n).curThread = σ.curThread := rfl
theorem dn_csc : (dnSt σ t d p xt xd y n).curSc = σ.curSc := rfl
theorem dn_tm : (dnSt σ t d p xt xd y n).curTime = σ.curTime := rfl

variable (hkt : σ.kheap t = some (.tcb xt)) (hkd : σ.kheap d = some (.tcb xd))
  (hkp : σ.kheap p = some (.schedContext y n)) (htd : t ≠ d) (hpt : p ≠ t) (hpd : p ≠ d)
include hkt hkd hkp htd hpt hpd

/-- An object other than a TCB or an SC is kept, both ways. -/
theorem dn_oth {q : ObjRef} {o : KernelObject} (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ x m, o ≠ .schedContext x m) :
    (dnSt σ t d p xt xd y n).kheap q = some o ↔ σ.kheap q = some o := by
  by_cases e1 : q = d
  · subst e1; rw [dn_kd, hkd]; exact ⟨fun h => absurd (Option.some.inj h).symm (h1 _),
      fun h => absurd (Option.some.inj h).symm (h1 _)⟩
  by_cases e2 : q = p
  · subst e2; rw [dn_kp hpd, hkp]; exact ⟨fun h => absurd (Option.some.inj h).symm (h2 _ _),
      fun h => absurd (Option.some.inj h).symm (h2 _ _)⟩
  by_cases e3 : q = t
  · subst e3; rw [dn_kt htd hpt, hkt]; exact ⟨fun h => absurd (Option.some.inj h).symm (h1 _),
      fun h => absurd (Option.some.inj h).symm (h1 _)⟩
  rw [dn_ko e3 e1 e2]

theorem dn_ksub : KSub σ (dnSt σ t d p xt xd y n) := by
  intro o
  by_cases e1 : o = d
  · subst e1
    exact ⟨fun r cs h _ => (by rw [dn_kd] at h; cases h), fun _ _ => ⟨xd, hkd⟩, fun h => (by rw [hkd] at h; cases h)⟩
  by_cases e2 : o = p
  · subst e2
    exact ⟨fun r cs h _ => (by rw [dn_kp hpd] at h; cases h), fun _ h => (by rw [dn_kp hpd] at h; cases h),
      fun h => (by rw [hkp] at h; cases h)⟩
  by_cases e3 : o = t
  · subst e3
    exact ⟨fun r cs h _ => (by rw [dn_kt htd hpt] at h; cases h), fun _ _ => ⟨xt, hkt⟩,
      fun h => (by rw [hkt] at h; cases h)⟩
  rw [dn_ko e3 e1 e2]; exact KSub.refl σ o

theorem dn_szKeep : SzKeep σ (dnSt σ t d p xt xd y n) := fun q x m hq => by
  by_cases e1 : q = d
  · subst e1; rw [dn_kd] at hq; cases hq
  by_cases e2 : q = p
  · subst e2; rw [dn_kp hpd] at hq; cases hq; exact ⟨y, hkp⟩
  by_cases e3 : q = t
  · subst e3; rw [dn_kt htd hpt] at hq; cases hq
  rw [dn_ko e3 e1 e2] at hq; exact ⟨x, hq⟩

theorem dn_ykeep : YKeep σ (dnSt σ t d p xt xd y n) := by
  refine ⟨fun q x hq => ?_, fun q x m hq => ?_, fun q x m hq => ?_⟩
  · by_cases e1 : q = d
    · subst e1; rw [hkd] at hq; cases hq; exact ⟨_, dn_kd, rfl⟩
    by_cases e2 : q = p
    · subst e2; rw [hkp] at hq; cases hq
    by_cases e3 : q = t
    · subst e3; rw [hkt] at hq; cases hq; exact ⟨_, dn_kt htd hpt, rfl⟩
    exact ⟨x, by rw [dn_ko e3 e1 e2]; exact hq, rfl⟩
  · by_cases e1 : q = d
    · subst e1; rw [hkd] at hq; cases hq
    by_cases e2 : q = p
    · subst e2; rw [hkp] at hq; cases hq; exact ⟨_, dn_kp hpd, rfl⟩
    by_cases e3 : q = t
    · subst e3; rw [hkt] at hq; cases hq
    exact ⟨x, by rw [dn_ko e3 e1 e2]; exact hq, rfl⟩
  · by_cases e1 : q = d
    · subst e1; rw [dn_kd] at hq; cases hq
    by_cases e2 : q = p
    · subst e2; rw [dn_kp hpd] at hq; cases hq; exact ⟨y, hkp, rfl⟩
    by_cases e3 : q = t
    · subst e3; rw [dn_kt htd hpt] at hq; cases hq
    exact ⟨x, by rw [← dn_ko e3 e1 e2]; exact hq, rfl⟩

/-- The TCBs kept but for their SCs. -/
theorem dn_tcbF {q : ObjRef} {x : Tcb} (hq : σ.kheap q = some (.tcb x)) :
    ∃ sc, (dnSt σ t d p xt xd y n).kheap q = some (.tcb { x with tcbSchedContext := sc }) := by
  by_cases e1 : q = d
  · subst e1; rw [hkd] at hq; cases hq; exact ⟨_, dn_kd⟩
  by_cases e2 : q = p
  · subst e2; rw [hkp] at hq; cases hq
  by_cases e3 : q = t
  · subst e3; rw [hkt] at hq; cases hq; exact ⟨_, dn_kt htd hpt⟩
  exact ⟨x.tcbSchedContext, by rw [dn_ko e3 e1 e2]; exact hq⟩

theorem dn_tcbB {q : ObjRef} {x : Tcb} (hq : (dnSt σ t d p xt xd y n).kheap q = some (.tcb x)) :
    ∃ x0 sc, σ.kheap q = some (.tcb x0) ∧ x = { x0 with tcbSchedContext := sc } := by
  by_cases e1 : q = d
  · subst e1; rw [dn_kd] at hq; cases hq; exact ⟨xd, _, hkd, rfl⟩
  by_cases e2 : q = p
  · subst e2; rw [dn_kp hpd] at hq; cases hq
  by_cases e3 : q = t
  · subst e3; rw [dn_kt htd hpt] at hq; cases hq; exact ⟨xt, _, hkt, rfl⟩
  rw [dn_ko e3 e1 e2] at hq; exact ⟨x, x.tcbSchedContext, hq, rfl⟩

theorem dn_mcpKeep : McpKeep σ (dnSt σ t d p xt xd y n) := fun q x hq => by
  obtain ⟨sc, h⟩ := dn_tcbF hkt hkd hkp htd hpt hpd hq; exact ⟨_, h, rfl⟩

theorem dn_bufKeep : ∀ q x, σ.kheap q = some (.tcb x) →
    ∃ z, (dnSt σ t d p xt xd y n).kheap q = some (.tcb z) ∧ z.tcbIpcBuffer = x.tcbIpcBuffer := fun q x hq => by
  obtain ⟨sc, h⟩ := dn_tcbF hkt hkd hkp htd hpt hpd hq; exact ⟨_, h, rfl⟩

theorem dn_khrb : KhRB σ (dnSt σ t d p xt xd y n) := fun q o' hq => by
  by_cases e1 : q = d
  · subst e1; rw [dn_kd] at hq; cases hq; exact ⟨_, hkd, ObjRB.tcb (Or.inl rfl)⟩
  by_cases e2 : q = p
  · subst e2; rw [dn_kp hpd] at hq; cases hq
    exact ⟨_, hkp, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
  by_cases e3 : q = t
  · subst e3; rw [dn_kt htd hpt] at hq; cases hq; exact ⟨_, hkt, ObjRB.tcb (Or.inl rfl)⟩
  rw [dn_ko e3 e1 e2] at hq; exact ⟨o', hq, ObjRB.refl o'⟩

theorem dn_ksz : KSz σ (dnSt σ t d p xt xd y n) := fun q o' hq => by
  by_cases e1 : q = d
  · subst e1; rw [dn_kd] at hq; cases hq; exact ⟨_, hkd, rfl⟩
  by_cases e2 : q = p
  · subst e2; rw [dn_kp hpd] at hq; cases hq; exact ⟨_, hkp, rfl⟩
  by_cases e3 : q = t
  · subst e3; rw [dn_kt htd hpt] at hq; cases hq; exact ⟨_, hkt, rfl⟩
  rw [dn_ko e3 e1 e2] at hq; exact ⟨o', hq, rfl⟩

theorem dn_kback : KBack σ (dnSt σ t d p xt xd y n) := fun q o' hq => by
  have tc : ∀ x x', σ.kheap q = some (.tcb x) → o' = .tcb x' → ∃ ko, σ.kheap q = some ko ∧
      ((∃ x, o' = .notification x) → ∃ x, ko = .notification x) ∧
      ((∃ x, o' = .endpoint x) → ∃ x, ko = .endpoint x) ∧ ((∃ x, o' = .reply x) → ∃ x, ko = .reply x) ∧
      ((∃ x, o' = .tcb x) → ∃ x, ko = .tcb x) ∧ ((∃ x n, o' = .schedContext x n) → ∃ x n, ko = .schedContext x n) ∧
      ((∃ x, o' = .archObj x) → ∃ x, ko = .archObj x) := by
    rintro x x' hx rfl
    refine ⟨_, hx, ?_, ?_, ?_, fun _ => ⟨x, rfl⟩, ?_, ?_⟩
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  by_cases e1 : q = d
  · subst e1; rw [dn_kd] at hq; exact tc _ _ hkd (Option.some.inj hq).symm
  by_cases e2 : q = p
  · subst e2; rw [dn_kp hpd] at hq; cases hq
    refine ⟨_, hkp, ?_, ?_, ?_, ?_, fun _ => ⟨y, n, rfl⟩, ?_⟩
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  by_cases e3 : q = t
  · subst e3; rw [dn_kt htd hpt] at hq; exact tc _ _ hkt (Option.some.inj hq).symm
  rw [dn_ko e3 e1 e2] at hq; exact KBack.of_kheap (σ := σ) (σ' := σ) rfl q o' hq


theorem dn_ipcFr : IpcFrKeep σ (dnSt σ t d p xt xd y n) :=
  IpcFrKeep.of_kbackF (dn_kback hkt hkd hkp htd hpt hpd)
    (fun q x hq => by obtain ⟨sc, h⟩ := dn_tcbF hkt hkd hkp htd hpt hpd hq; exact ⟨_, h, rfl, rfl⟩)
    (fun q vms => dn_oth hkt hkd hkp htd hpt hpd (fun _ e => by cases e) (fun _ _ e => by cases e))

theorem dn_ck :
    (∀ q y' m, σ.kheap q = some (.schedContext y' m) → ∃ y'', (dnSt σ t d p xt xd y n).kheap q =
      some (.schedContext y'' m) ∧ y''.scReplies = y'.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', (dnSt σ t d p xt xd y n).kheap q = some (.reply x') ∧
      x'.replySc = x.replySc) ∧
    (∀ q x m, (dnSt σ t d p xt xd y n).kheap q = some (.schedContext x m) →
      ∃ x0, σ.kheap q = some (.schedContext x0 m)) := by
  refine ⟨fun q y' m hq => ?_, fun q x hq => ⟨x, (dn_oth hkt hkd hkp htd hpt hpd (fun _ h => by cases h)
    (fun _ _ h => by cases h)).2 hq, rfl⟩, fun q x m hq => dn_szKeep hkt hkd hkp htd hpt hpd q x m hq⟩
  by_cases e2 : q = p
  · subst e2; rw [hkp] at hq; cases hq; exact ⟨_, dn_kp hpd, rfl⟩
  by_cases e1 : q = d
  · subst e1; rw [hkd] at hq; cases hq
  by_cases e3 : q = t
  · subst e3; rw [hkt] at hq; cases hq
  exact ⟨y', by rw [dn_ko e3 e1 e2]; exact hq, rfl⟩

theorem dn_nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C (dnSt σ t d p xt xd y n) := fun m hm x q hx hq =>
  hN m hm x q ((dn_oth hkt hkd hkp htd hpt hpd (fun _ h => by cases h) (fun _ _ h => by cases h)).1 hx) hq

theorem dn_prio (u : ObjRef) : Sched.prioOf (dnSt σ t d p xt xd y n) u = Sched.prioOf σ u := by
  by_cases e1 : u = d
  · subst e1; rw [Sched.prioOf_eq dn_kd, Sched.prioOf_eq hkd]
  by_cases e2 : u = p
  · subst e2; unfold Sched.prioOf; rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq, dn_kp hpd, hkp]
  by_cases e3 : u = t
  · subst e3; rw [Sched.prioOf_eq (dn_kt htd hpt), Sched.prioOf_eq hkt]
  unfold Sched.prioOf; rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq, dn_ko e3 e1 e2]

theorem dn_isorted (hS : IpcSorted σ) : IpcSorted (dnSt σ t d p xt xd y n) := by
  refine ⟨fun q z hq => ?_, fun q z hq => ?_⟩
  · exact (hS.1 q z ((dn_oth hkt hkd hkp htd hpt hpd (fun _ h => by cases h) (fun _ _ h => by cases h)).1 hq)).congr
      fun u _ => dn_prio hkt hkd hkp htd hpt hpd u
  · exact (hS.2 q z ((dn_oth hkt hkd hkp htd hpt hpd (fun _ h => by cases h) (fun _ _ h => by cases h)).1 hq)).congr
      fun u _ => dn_prio hkt hkd hkp htd hpt hpd u

theorem dn_own {T C : Set U64} (hdT : ∃ u ∈ T, u.bv = d) (hpc : p = σ.curSc)
    (hnr : 0 < σ.consumedTime → d ∉ σ.releaseQueue) : CurOwnW T C (dnSt σ t d p xt xd y n) := by
  obtain ⟨u, hu, rfl⟩ := hdT
  have e : (dnSt σ t u.bv p xt xd y n).curSc = p := hpc.symm
  refine Or.inl ⟨u, hu, _, dn_kd, (by rw [e]), fun x m hx => ?_, hnr⟩
  rw [e, dn_kp hpd] at hx; cases hx; rfl

theorem dn_off (hpc : p = σ.curSc) (hO : OffOK σ) : OffOK (dnSt σ t d p xt xd y n) := by
  intro h0 y' m hy ha
  have e : (dnSt σ t d p xt xd y n).curSc = p := hpc.symm
  rw [e, dn_kp hpd] at hy; cases hy
  exact hO h0 y n (by rw [← hpc]; exact hkp) ha

theorem dn_idleOK (hit : σ.idleThread ≠ t) (hid : σ.idleThread ≠ d) (hO : IdleOK σ) :
    IdleOK (dnSt σ t d p xt xd y n) := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hO
  have hip : σ.idleThread ≠ p := by intro e; rw [e, hkp] at h1; cases h1
  exact ⟨x, by rw [show (dnSt σ t d p xt xd y n).idleThread = σ.idleThread from rfl, dn_ko hit hid hip]; exact h1,
    h2, h3, h4⟩

theorem dn_bsa (hdq : ipcQueuedThreadState xd.tcbState = false) (hB : BlockedScActive σ) :
    BlockedScActive (dnSt σ t d p xt xd y n) := by
  refine ⟨fun q z m u xu hq hz hu hqd => ?_, fun q z m hq hr => ?_⟩
  · obtain ⟨x0, sc, hx0, rfl⟩ := dn_tcbB hkt hkd hkp htd hpt hpd hu
    by_cases e2 : q = p
    · subst e2; rw [dn_kp hpd] at hq; cases hq
      cases hz
      rw [hkd] at hx0; cases hx0; rw [hdq] at hqd; cases hqd
    · have hq' : σ.kheap q = some (.schedContext z m) := by
        by_cases e1 : q = d
        · subst e1; rw [dn_kd] at hq; cases hq
        by_cases e3 : q = t
        · subst e3; rw [dn_kt htd hpt] at hq; cases hq
        rw [dn_ko e3 e1 e2] at hq; exact hq
      exact hB.tcb q z m u x0 hq' hz hx0 hqd
  · by_cases e2 : q = p
    · subst e2; rw [dn_kp hpd] at hq; cases hq; exact hB.replies q y n hkp hr
    · by_cases e1 : q = d
      · subst e1; rw [dn_kd] at hq; cases hq
      by_cases e3 : q = t
      · subst e3; rw [dn_kt htd hpt] at hq; cases hq
      rw [dn_ko e3 e1 e2] at hq; exact hB.replies q z m hq hr

/-- **`Inv` across the donation** of `t`'s SC `p` (`t`, `d` in no queue) to
`d`, whose SC (the same refills) is released if active. -/
theorem dn_inv (hI : Inv σ) (hyt : y.scTcb = some t) (hnqt : NotQueued σ t) (hnqd : NotQueued σ d)
    (hrel : scActive y = true → released σ y) : Inv (dnSt σ t d p xt xd y n) := by
  have h1 : Inv (updK σ t (.tcb { xt with tcbSchedContext := none })) :=
    (hI.toBut t).unboundTcb hkt hyt hkp hnqt
  set σ1 : State Unit := { updK σ t (.tcb { xt with tcbSchedContext := none }) with
    schedulerAction := .chooseNewThread } with hσ1
  have h2 : Inv σ1 := h1.qchange ⟨rfl, rfl, rfl, fun _ _ _ h => Or.inl h⟩
  have hkp1 : σ1.kheap p = some (.schedContext y n) := by simp [σ1, updK, hpt, hkp]
  have hkd1 : σ1.kheap d = some (.tcb xd) := by simp [σ1, updK, Ne.symm htd, hkd]
  have hnp : ∀ u x, σ1.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p := by
    intro u x hx hu
    by_cases e : u = t
    · subst e; simp [σ1, updK] at hx; subst hx; cases hu
    · obtain ⟨y', m', k1, k2⟩ := h2.back u x p hx hu
      rw [hkp1] at k1; cases k1; rw [hyt] at k2; cases k2; exact e rfl
  have hnq1 : NotQueued σ1 d := hnqd
  have h3 : InvBut (donSt σ1 p d y n xd) d := h2.donatedW hkp1 hnp hkd1 hpd hnq1
  refine h3.inv fun x hx _ => ?_
  intro x' scp z m k1 k2 k3 k4 _
  have hk : (donSt σ1 p d y n xd).kheap d = some (.tcb { xd with tcbSchedContext := some p }) := by
    simp [donSt, updK]
  rw [hk] at k1; cases k1; cases k2
  rw [show (donSt σ1 p d y n xd).kheap p = some (.schedContext { y with scTcb := some d } n) by
    simp [donSt, updK, hpd]] at k3
  cases k3
  have := hrel k4
  unfold released at this ⊢
  exact this

end Dn

/-- **The receiver's `Running` after the donation is the donation after the
`Running`** (the receiver not current). -/
theorem dn_swap {σ : State Unit} {t d p : ObjRef} {xt x3 : Tcb} {y : SchedContext} {n : Nat}
    (htd : t ≠ d) (hpd : p ≠ d) (hdc : d ≠ σ.curThread) :
    stsAct (updK (dnSt σ t d p xt x3 y n) d (.tcb { { x3 with tcbSchedContext := some p } with
      tcbState := .running })) d =
      dnSt (stsAct (updK σ d (.tcb { x3 with tcbState := .running })) d) t d p xt
        { x3 with tcbState := .running } y n := by
  have h1 : stsAct (updK σ d (.tcb { x3 with tcbState := .running })) d =
      updK σ d (.tcb { x3 with tcbState := .running }) := stsAct_ne hdc
  have h2 : stsAct (updK (dnSt σ t d p xt x3 y n) d (.tcb { { x3 with tcbSchedContext := some p } with
      tcbState := .running })) d = updK (dnSt σ t d p xt x3 y n) d (.tcb { { x3 with tcbSchedContext := some p } with
      tcbState := .running }) := stsAct_ne hdc
  rw [h1, h2]
  unfold dnSt donSt
  simp only [updK, Function.update_idem, Function.update_comm (Ne.symm htd), Function.update_comm (Ne.symm hpd)] <;> rfl

theorem nd_when_true_bind {σ' β : Type} {P : Prop} [Decidable P] (h : P) (m : NonDet σ' Unit)
    (f : Unit → NonDet σ' β) (s : σ') : (NonDet.when P m >>= f) s = (m >>= f) s := by
  unfold NonDet.when; rw [if_pos h]

/-- The spec's `send_ipc` to a waiting receiver `d` without an SC (non-call,
the sender without a fault, `canDonate`): the donation of the sender's SC
`p` (`hD`), then the receiver's `Running` and tail. -/
theorem sendIpc_recv_eqDon {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) {e' : ObjRef} {rep : Option ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' rep dd) (blk : Bool) (badge : Badge) (g gr : Bool)
    {σ2 σ3 σ4 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) rep σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hf3 : xt3.tcbFault = none)
    (hkd3 : σ3.kheap d = some (.tcb x3)) (hsc3 : x3.tcbSchedContext = none) {p : ObjRef}
    (hts : xt3.tcbSchedContext = some p) (hD : schedContextDonate (Z := Unit) p d σ3 = ({((), σ4)}, False))
    {x4 : Tcb} (hkd4 : σ4.kheap d = some (.tcb x4)) :
    sendIpc (Z := Unit) blk false badge g gr true t e σ =
      specWakeTailE d (stsAct (updK σ4 d (.tcb { x4 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  have hdn : (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun threadSc =>
      schedContextDonate (Z := Unit) (the threadSc) d) σ3 = ({((), σ4)}, False) := by
    rw [nd_bind_one (getTcbObjRef_eq _ hkt3), hts]; exact hD
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3), hf3]
    simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [nd_when_true_bind (show true = true ∧ x3.tcbSchedContext = none from ⟨rfl, hsc3⟩)]
    rw [nd_bind_one hdn, nd_bind_one (Notif.setThreadState_eq _ hkd4)]
    rfl

end Spec


/-! ## The wake with a spec step after the frame at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **A wake in the frame `DWFr` up to `σa`, then a spec step to `σ'`, keeps
`JAtZ`** (XTopJointSendCall's `JAtZ.wake_postCI` for any step `σa → σ'`
with its frame facts; the scheduler invariants after given). -/
theorem JAtZ.wake_postG (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
    {s' : S} {σa σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : DWFr n t σ σa) (G : SkD σa σ') (hks1 : KSub σa σ') (hsz1 : SzKeep σa σ') (hyk1 : YKeep σa σ')
    (hmk1 : McpKeep σa σ')
    (hbk1 : ∀ p x, σa.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer)
    (hrb1 : KhRB σa σ') (hkz1 : KSz σa σ') (hkb1 : KBack σa σ') (hfk1 : IpcFrKeep σa σ')
    (hck1 : (∀ q y n, σa.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
      (∀ q x, σa.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
      (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σa.kheap p = some (.schedContext x0 n)))
    (hrep1 : ∀ q x, σ'.kheap q = some (.reply x) → σa.kheap q = some (.reply x))
    (hao1 : ∀ q ao, σa.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao))
    (hkq : ∀ q ∈ D, σ'.kheap q.bv = σa.kheap q.bv)
    (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') (hrun3 : CurRunM σ')
    (hown3 : CurOwnW Z.T Z.C σ') (hoff3 : OffOK σ') (hnsc3 : NSC Z.N Z.C σ') (hiso3 : IpcSorted σ')
    (hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 (G.cdt.trans F.sk.cdt) (G.orig.trans F.sk.orig)
    (F.ksub.trans hks1) hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck0 := F.callKeep
  have ck : (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
      (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
      (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) := by
    refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
    · obtain ⟨y', h1, h2⟩ := ck0.1 q y n hq
      obtain ⟨y'', h1', h2'⟩ := hck1.1 q y' n h1
      exact ⟨y'', h1', h2'.trans h2⟩
    · obtain ⟨x', h1, h2⟩ := ck0.2.1 q x hq
      obtain ⟨x'', h1', h2'⟩ := hck1.2.1 q x' h1
      exact ⟨x'', h1', h2'.trans h2⟩
    · obtain ⟨x0, h0⟩ := hck1.2.2 p x n hp
      exact ck0.2.2 p x0 n h0
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    have hy' : σa.kheap d.bv = some (.reply y) := hrep1 _ _ hy
    obtain ⟨x, hx, -, hc⟩ := F.replyB hy'
    obtain ⟨e1, e2⟩ := k4 d hd
    rcases hc with e | ⟨hxt, -⟩
    · obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨x, hx, e ▸ hyt⟩
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
    · obtain ⟨h1, h2, h3⟩ := hRR d hd x hx hxt
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hidl0 : σ'.idleThread = σ.idleThread := G.idle.trans F.sk.idle
  have hisc0 : σ'.idleSc = σ.idleSc := G.isc.trans F.sk.isc
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q :=
    J.deadP_dfrCI F hkq hidl0 hS3 hIR.1 hw k3 hAI3.1
      (J.yld.frame k2 (F.ykeep.trans hyk1)) (F.ykeep.trans hyk1) ht
  have hsz : SzKeep σ σ' := fun p y n hp => by
    obtain ⟨y0, hy0⟩ := hsz1 p y n hp
    exact F.szKeep p y0 n hy0
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hsz q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 hidl0 hisc0).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 (G.ct.trans F.sk.ct) (G.csc.trans F.sk.csc)
    (fun sl h => Or.inl (by rw [← F.sk.orig, ← G.orig]; exact h))
    (by rw [G.arch, F.sk.arch])
    (fun q ao h => hao1 q ao (F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
        (fun _ e => by cases e) (fun _ e => by cases e))) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 (F.khrb.trans hrb1)
  have hbuf : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
    fun p x hp => by
      obtain ⟨y, hy, e⟩ := F.bufKeep p x hp
      obtain ⟨z, hz, e'⟩ := hbk1 p y hy
      exact ⟨z, hz, e'.trans e⟩
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 (F.ykeep.trans hyk1),
      J.mcp.frame k1 (F.mcpKeep.trans hmk1), J.buf.frame kb hbuf, hRP',
      J.apart.sc_frame hks hsz, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hidl0 hisc0), hkern,
      J.cnW_utc hw hF.1 (G.cdt.trans F.sk.cdt) (G.orig.trans F.sk.orig) (G.arch.trans F.sk.arch) hDbg,
      hnsc3, I3, hcur3, hown3, hoff3, hAI3, B3, hiso3, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 (F.ksz.trans hkz1)
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) (G.arch.trans F.sk.arch) (fun q ao h => hao1 q ao (F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
        (fun _ e => by cases e) (fun _ e => by cases e))) hsz hF.1 (F.kback.trans' hkb1) (F.ipcFr.trans hfk1) hC R hKd (G.orig.trans F.sk.orig) (J.idleW_keep hS3 hidl0 hisc0).1 J.zD⟩


/-- An SC bound to a thread is not dead (a dead SC's `TCB` word is 0). -/
theorem JAtZ.scOwned_not_dead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t q : U64} (ht : t ∈ Z.T)
    {y : Fl4Spec.SchedContext} {k : Nat} (hq : σ.kheap q.bv = some (.schedContext y k))
    (hyt : y.scTcb = some t.bv) : ¬ DeadP (L := L) H s q := by
  intro hd
  obtain ⟨c', hc', ec⟩ := J.obj.sc q.bv y k hq
  have hcq : c' = q := P1.eq_of_bv ec
  subst hcq
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨-, hH⟩ := hJ.sc c' y k (J.c0 c' hc') hq
  obtain ⟨d1, -, -⟩ := hd.2.2.2.2 _ hH
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have h24 := word24_of hS hc' hq hyt
  rw [← scTcbA_eq] at h24
  rw [h24] at d1
  exact (hc.tcbs t ht).ne0 (by rw [d1]; rfl)

set_option maxHeartbeats 64000000 in
/-- **A send to a waiting receiver without an SC at `J`, with the caller's SC
donated** (module docstring): as `JAtZ.sendRecvJ0` up to the reply unlink,
then FL4's `donate` of the caller's (current) SC on `IRel`
(`donate_bound_refines`, `tk_lift`), P1's `donate.ipc` and `donate.kwAX`
(the receiver on the SC's core), the spec's donation `donate_cur_eq`, the
receiver `Running`, `JAtZ` by `JAtZ.wake_postG` at `dnSt` (`dn_swap`), the
tail `JAtZ.sendTailJ`; the spec's outcome `sendIpc_recv_eqDon`. The
caller is current, resumed (`hres`), not idle (`hti`) and in no ready queue
(`hnq`, JEntryAt's `ctnq`). -/
theorem JAtZ.sendDonJ (hAT : P0.ArchTotal arI)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrs : xt.tcbState = .restart) (hft : xt.tcbFault = none) (hct : σ.curThread = t.bv)
    (hres : σ.schedulerAction = .resumeCurThread) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr : Bool)
    (hdn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext = none) :
    endpoint.send_ipc st arI s a blk false badge g gr true t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr true t.bv e.bv σ).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by rw [hrs]; decide
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdc : d'.bv ≠ σ.curThread := by rw [hct]; exact Ne.symm htd'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, -, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have Fr1 : CFr e.bv d'.bv σ σ1 := CFr.upd hk (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hk (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (J.xferStepGJ hk (epDeq (.recvEP (d'.bv :: q)) d'.bv) hR1 hS1 hW1 F1 ht hdT htd hkt hkd hft
    badge g h1 hB1 hX1 hS1' hSg1) ?_
  rintro s2 ⟨x2, um2, yb, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksy, hKy, hCnKy, hyk⟩
  have hncn : ∀ {q' : Fl4Spec.ObjRef} {o' : Fl4Spec.KernelObject}, σ.kheap q' = some o' →
      (∀ r cs, o' ≠ .cnode r cs) → σy.kheap q' = some o' :=
    fun hq ho => (hyk _ fun r cs h0 => ho r cs (by rw [hq] at h0; exact Option.some.inj h0)).trans hq
  have hky : σy.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := hncn hk (fun _ _ h0 => by cases h0)
  have hkdy : σy.kheap d'.bv = some (.tcb xd) := hncn hkd (fun _ _ h0 => by cases h0)
  have hkty : σy.kheap t.bv = some (.tcb xt) := hncn hkt (fun _ _ h0 => by cases h0)
  have hcty : σy.curThread = σ.curThread := hKy.2.2.2.2
  have hsay : σy.schedulerAction = σ.schedulerAction := by
    have e := congrArg Fl4Spec.AbstractState.schedulerAction hCnKy.1; exact e
  have hidy : σy.idleThread = σ.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hCnKy.1; exact e
  have hrqy : σy.readyQueues = σ.readyQueues := by
    have e := congrArg Fl4Spec.AbstractState.readyQueues hCnKy.1; exact e
  have hrly : σy.releaseQueue = σ.releaseQueue := by
    have e := congrArg Fl4Spec.AbstractState.releaseQueue hCnKy.1; exact e
  set σ1y := Notif.updK σy e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1y
  have hkt1y : σ1y.kheap t.bv = some (.tcb xt) := by simp [σ1y, hte, hkty]
  have hkd1y : σ1y.kheap d'.bv = some (.tcb xd) := by simp [σ1y, hde, hkdy]
  have hk1ey : σ1y.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1y]
  have Fr1y : CFr e.bv d'.bv σy σ1y := CFr.upd hky (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1y : IK d'.bv σy σ1y := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hky (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1y : SKeep σy σ1y := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have hq1y : ∀ e'' ∈ Z.E, ∀ z, σ1y.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    refine hq1 e'' he'' z ?_
    by_cases hee : e''.bv = e.bv
    · rw [hee] at hz ⊢; rw [hk1ey] at hz; rw [hk1e]; exact hz
    · simp only [σ1y, Notif.updK_kheap, Function.update_of_ne hee] at hz
      simp only [σ1, Notif.updK_kheap, Function.update_of_ne hee]
      exact keepC_back hKy.1 hz (fun _ _ h0 => by cases h0)
  set σ2 := Notif.updK (Endp.setUm σ1y um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1y]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1ey]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1y e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨⟨d', hdT, (a_reply hda).2⟩, ?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have Fr2 : CFr e.bv d'.bv σy σ2 := (Fr1y.trans (CFr.um _ _ σ1y um2)).trans (CFr.upd (σ := Endp.setUm σ1y um2) hkd1y
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σy σ2 := IK1y.trans ((IK.um _ σ1y um2).trans (IK.updSelf (σ := Endp.setUm σ1y um2) hkd1y hxsc))
  have SK2 : SKeep σy σ2 := SK1y.trans ((SKeep.um σ1y um2).trans (SKeep.updK (σ := Endp.setUm σ1y um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1y, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb yb := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st yb s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) ∧
      P1.WritesIn st yb s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) yb b ∨ RcvBufW xd b) ∧
      CFr e.bv d'.bv σy σ3 ∧ IK d'.bv σy σ3 ∧ SKeep σy σ3 ∧ σ3.curThread = σy.curThread ∧
      σ3.schedulerAction = σy.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d') ∧
      (L.mem s3 (P1.replyA d') = 0#u64 ∨ (L.mem s3 (P1.stA d') ≠ sched.TS_BLOCKED_ON_REPLY ∧
        L.mem s3 (P1.stA d') ≠ sched.TS_BLOCKED_ON_RECV))) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, x2, _, rfl, hR2, hS2', hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc, hq2, hW2, F2, Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA, Or.inl hrA⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
        simp [σ2, σ1y, hwe, hwd, hncn hkr (fun _ _ h0 => by cases h0)]
      have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      have hX2' := IpcRel.ofSRN hR2 hS2'
      have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
      rw [hrA] at hiR hit
      refine WP.spec_mono (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
          hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
        (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
            (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
          (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
      rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
      have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, hrA] at b2; rw [← b2]; exact z3
      set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
      set σ3a := Notif.updK σ2 w.bv (.reply { xr with replyTcb := none }) with hσ3a
      have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
      have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := by
        show d'.bv ≠ σy.curThread; rw [hcty]; exact hdc
      have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st yb s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc], ?_, hW3',
        footW_trans F2 (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2), Or.inr (by rw [e3']; exact P1.inactive_ne)⟩
      · rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
        exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
      · exact (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
          (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
      · have IK3a : IK d'.bv σy σ3a := IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2 (fun o0 h => by
          rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        have IK3b : IK d'.bv σy (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
        exact IK3b.trans (IK.sts _ _ _)
      · exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply { xr with replyTcb := none }) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
          (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
      · rw [e3s]; rfl
      · rw [e3s]; rfl
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
  rintro s3 ⟨σ3, x3, X3, hU, hR3, hS3, hkt3, hkd3, hrb3, hns3, hsc3, hq3, hW3, F3, Fr3, IK3, SK3, hct3, hact3,
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3, hra3⟩

  have J0 := J
  have hk0 := hk
  have hkd0 := hkd
  have hkt0 := hkt
  have J := Jy
  have hkd : σy.kheap d'.bv = some (.tcb xd) := hkdy
  have hkt : σy.kheap t.bv = some (.tcb xt) := hkty
  have hk : σy.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := hky
  have hres : σy.schedulerAction = .resumeCurThread := hsay.trans hres
  have hti : σy.curThread ≠ σy.idleThread := by rw [hcty, hidy]; exact hti
  have hct : σy.curThread = t.bv := hcty.trans hct
  have hnq : ∀ dm q', t.bv ∉ σy.readyQueues dm q' := by rw [hrqy]; exact hnq
  have hdc : d'.bv ≠ σy.curThread := by rw [hcty]; exact hdc
  have hdn : ∀ xd, σy.kheap d'.bv = some (.tcb xd) → xd.tcbSchedContext = none := fun xd h => hdn xd (by
    rw [hkdy] at h; rw [hkd0]; exact h)
  have hxt3 := hR3.at_tcb ht hkt3
  have hks3 : L.ksb s3 = L.ksb yb := hW3.1
  -- the caller's SC, the current SC
  have hCI : CurInv σy := J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hnrT : t.bv ∉ σy.releaseQueue := by rw [← hct]; exact hCI.notRel
  obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
  rw [hct, hkt] at hkc
  cases hkc
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  obtain ⟨xt', hkt', hsct⟩ := hSM t ht
  rw [hkt3] at hkt'; cases hkt'
  set sc := L.mem s3 (scA t) with hscdef
  have hsc0 : sc ≠ 0#u64 := fun h0 => by
    have : xt.tcbSchedContext = none := by rw [hsct, h0, optRef_zero]
    rw [hcs] at this; cases this
  have hxtsc : xt.tcbSchedContext = some sc.bv := by rw [hsct, Notif.optRef_ne hsc0]
  have hscp : sc.bv = σy.curSc := Option.some.inj (hxtsc.symm.trans hcs)
  have hscC : sc ∈ Z.C := hs3.scMem t ht hsc0
  obtain ⟨y, n, hky3, -⟩ := hs3.scs sc hscC
  have hky : σy.kheap sc.bv = some (.schedContext y n) := SK3.2.2.2 _ _ _ hky3
  have hyt : y.scTcb = some t.bv := by
    obtain ⟨y', n', hk', hyt⟩ := J.inv.back t.bv xt sc.bv hkt hxtsc
    rw [hky] at hk'; cases hk'; exact hyt
  have hpt : sc.bv ≠ t.bv := kheap_ne hky hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hpd : sc.bv ≠ d'.bv := kheap_ne hky hkd (fun _ h1 h2 => by subst h1; cases h2)
  -- the receiver has no SC
  have hxd0 : xd.tcbSchedContext = none := hdn xd hkd
  have hx30 : x3.tcbSchedContext = none := by rw [hsc3, hxd0]
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM d' hdT
  rw [hkd3] at hkd3'; cases hkd3'
  have hd0 : L.mem s3 (scA d') = 0#u64 := by
    by_contra h
    rw [Notif.optRef_ne h] at hdsc; rw [hx30] at hdsc; cases hdsc
  -- in no queue
  have hnqD : NotQueued σy d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hnqT3 : NotQueued σ3 t.bv := ⟨by rw [IK3.2.1]; exact hnq, by rw [IK3.2.2.1]; exact hnrT⟩
  have hnqD3 : NotQueued σ3 d'.bv := ⟨by rw [IK3.2.1]; exact hnqD.1, by rw [IK3.2.2.1]; exact hnqD.2⟩
  have bits3 : ∀ u ∈ Z.T, NotQueued σ3 u.bv →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hnu.2
      rw [hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT3
  obtain ⟨hqbD, hrbD⟩ := bits3 d' hdT hnqD3
  -- the scheduler words
  have ha0 : L.actionW s3 = 0#u64 := by
    have h := hSR3.act
    rw [hact3, hres] at h
    unfold P1.LawfulStore.actionW; rw [hcq3.cur]; exact h
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu h' => by
    rw [ha0] at h'; exact (hcq3.tcbs u hu).ne0 (by rw [← h']; rfl)
  have hcw3 : L.curW s3 = t := by
    have h : (nodeW st s3 Z.c layout.node.CUR_THREAD).bv = t.bv := by rw [← hs3.curThread, hct3, hct]
    unfold P1.LawfulStore.curW; rw [hcq3.cur]; exact P1.eq_of_bv h
  have hidl3 : σ3.idleThread = σy.idleThread := Fr3.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σy.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σy.idleThread := by rw [← hct]; exact hti
  have hid : d'.bv ≠ σy.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hscS : sc ∈ P1.Heap.scs H := (hX3.2.2.bound t htH hsc0).1
  have hsA : sc ∈ Ac := hB3.sact t htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw3⟩))))) hsc0
  have haff : L.mem s3 (P1.affA d') = L.mem s3 (P1.scCoreA sc) := by
    rw [hcq3.aff d' hdT, Fl4Proofs.P3.Sched.scCoreA_eq, hSR3.core sc hscC]
  have htcb3 : L.mem s3 (P1.scTcbA sc) = t := by
    rw [scTcbA_eq]; exact word24_of hSR3 hscC hky3 hyt
  -- the spec facts for the donation
  have hrib3 : RelIfBound σ3 d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK3
  have I3 : Inv σ3 := ((J.inv.toBut d'.bv).ik hnqD IK3).1.inv fun _ _ _ => hrib3
  have hN3 : NSC Z.N Z.C σ3 := Fr3.nsc J.nsc
  have hrelσ : Fl4Spec.scActive y = true → released σy y := fun ha =>
    J.inv.rd t.bv xt hkt (Or.inl (by rw [hrs]; rfl)) xt sc.bv y n hkt hxtsc hky ha hnrT
  have hrel3 : inClass x3.tcbState → Fl4Spec.scActive y = true → released σ3 y := fun _ ha => by
    have := hrelσ ha; unfold released at this ⊢; rw [SK3.2.1]; exact this
  -- FL4: no fault, the donation
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ ∃ σ4,
      Fl4Spec.schedContextDonate (Z := Unit) sc.bv d'.bv σ3 = ({((), σ4)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) σ4 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 σ4 ∧
      P1.WritesIn st s3 r.1 (fun b => SFoot st Z.T Z.c s3 b ∨ b = scW sc 24#u64) ∧
      P1.BlkOKX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac X3 r.1 ∧
      (∀ u ∈ P1.Heap.tcbs H, L.mem r.1 (P1.stA u) = L.mem s3 (P1.stA u)) ∧
      (∀ u ∈ P1.Heap.tcbs H, L.mem r.1 (P1.replyA u) = L.mem s3 (P1.replyA u)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1) ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 hi1
    have hf0 : i1 = fl4_abi.consts.fault.NullFault := by
      rw [hi1, hxt3.fault0.2 hft]; unfold fl4_abi.consts.fault.NullFault; rfl
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    try rw [if_pos rfl]
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
    rw [hi2, if_pos hd0]
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
    subst hi3
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (donate_bound_refines s3 a σ3 hSR3 hX3'.1.toN hN3 I3 hscC hsc0 hky3 ht hyt hkt3 hdT hkd3 hx30 htd (fun h => hrel3 h.cls))
      (P1.schedcontext.donate.ipc hAT s3 a sc d' t Q0 R0 h3 hB3 hX3 hS3' hSg3 htH rfl hsc0
        ⟨hqbT, hrbT, hna3 t ht⟩ (hiw3 t ht hit) (J.zH.1 d' hdT) hd0 hqbD hrbD (hna3 d' hdT) (Ne.symm htd) hsA
        (hiw3 d' hdT hid)))
      (P1.schedcontext.donate.kwAX (Es := P1.EH H) hAT s3 a sc d' t h3 hB3 hX3 hS3' hSg3 hscS (J.zH.1 d' hdT)
        htH htcb3 ⟨hqbT, hrbT⟩)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨σ', hdon, ha, hS', hN', -, -, hW, -⟩, hP1⟩, hkw⟩
    simp only at ha hS' hN' hW hP1 hkw ⊢
    have hK : ScTKw (fun p => p = σ3.curThread) σ3 σ' :=
      ScTKw.ofFalse (NKT.of_eq (nkt_schedContextDonate sc.bv d'.bv) hdon)
    have hI' := tk_lift hP0 hX3' (hW.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h))
      (fun h => Or.inl (Or.inr (Or.inr (h ▸ sw_hdr hSR3 hscC (K := 24#u64) (by simp) (by simp) (by decide))))))
      hK hS' hN'
    obtain ⟨hBX4, hst4, hrp4, -⟩ := hP1
    exact ⟨ha, σ', hdon, hI'.1.toE, IpcRel.toSRN hI'.1 hI'.2, hW, hBX4, hst4, hrp4, hkw haff⟩
  rintro ⟨s4, a4⟩ ⟨ha4, σ4, hdon4, hR4, hS4, hW4, hBX4, hst4, hrp4, fu4⟩
  simp only at ha4 hR4 hS4 hW4 hBX4 hst4 hrp4 fu4 ⊢
  subst ha4
  try dsimp only
  have e4 := pair_eq (hdon4.symm.trans (donate_cur_eq hkt3 hkd3 hky3 hyt htd' hpt hpd
    (by rw [hct3, hct]) hnqT3 (by rw [hact3, hres])))
  subst e4
  set x4 : Fl4Spec.Tcb := { x3 with tcbSchedContext := some sc.bv } with hx4
  have hkd4 : (dnSt σ3 t.bv d'.bv sc.bv xt x3 y n).kheap d'.bv = some (.tcb x4) := dn_kd
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, (dnSt σ3 t.bv d'.bv sc.bv xt x3 y n).kheap e''.bv = some (.endpoint z) →
      d'.bv ∉ z.epQueue := fun e'' he'' z hz => hq3 e'' he'' z
    ((dn_oth hkt3 hkd3 hky3 htd' hpt hpd (fun _ h => by cases h) (fun _ _ h => by cases h)).1 hz)
  obtain ⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4', hSg4⟩ := hBX4
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hx4 : d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := by
    rcases hx3 with h | h
    · exact Or.inl h
    · right; rw [hst4 d' hdH]; exact h
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' := by
    rcases hra3 with h | ⟨h1, h2⟩
    · exact hX4.noref0 hdta (by rw [hrp4 d' hdH]; exact h)
    · exact hX4.noref hdta (by rw [hst4 d' hdH]; exact h1) (by rw [hst4 d' hdH]; exact h2)
  have hks4 : L.ksb s4 = L.ksb yb := hW4.1.trans hks3
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q4 R4 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK (dnSt σ3 t.bv d'.bv sc.bv xt x3 y n) d'.bv
      (.tcb { x4 with tcbState := .running })) d'.bv = dnSt σa t.bv d'.bv sc.bv xt x5 y n :=
    dn_swap htd' hpd hdc3
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5
      (dnSt σa t.bv d'.bv sc.bv xt x5 y n) := by
    rw [← heq5]; exact hIR0
  have hsw : SW Z.C σy (scW sc 24#u64) := sw_hdr J.xtop.fin.1.1.1 hscC (K := 24#u64) (by simp) (by simp) (by decide)
  have hW4' : P1.WritesIn st yb s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
    hW3.trans1 (hW4.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 h)))))
      (fun h => Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h ▸ hsw)))))))
  have hW5' : P1.WritesIn st yb s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q4, R4, h5.congrX (P1.excT_congr hXc3)⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have Fr5 : CFr e.bv d'.bv σy σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σy (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σy σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : SKeep σy σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  -- the donation after the wake (`dn_swap`)
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hkda : σa.kheap d'.bv = some (.tcb x5) := by rw [hσa, stsAct_kheap]; simp [Notif.updK]
  have hkpa : σa.kheap sc.bv = some (.schedContext y n) := by
    rw [hσa, stsAct_kheap]; simp [Notif.updK, hpd, hky3]
  have hnqTa : NotQueued σa t.bv := ⟨by rw [IK5.2.1]; exact hnq, by rw [IK5.2.2.1]; exact hnrT⟩
  have hnqDa : NotQueued σa d'.bv := ⟨by rw [IK5.2.1]; exact hnqD.1, by rw [IK5.2.2.1]; exact hnqD.2⟩
  have hrelA : Fl4Spec.scActive y = true → released σa y := fun ha => by
    have := hrelσ ha; unfold released at this ⊢; rw [SK5.2.1]; exact this
  set σ' := dnSt σa t.bv d'.bv sc.bv xt x5 y n with hσ'
  have hcscA : sc.bv = σa.curSc := by rw [Fr5.sk.csc]; exact hscp
  have hitA : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle]; exact Ne.symm hit
  have hidA : σa.idleThread ≠ d'.bv := by rw [Fr5.sk.idle]; exact Ne.symm hid
  have I5' : Inv σ' := dn_inv hkta hkda hkpa htd' hpt hpd I5 hyt hnqTa hnqDa hrelA
  have B5' : BlockedScActive σ' := dn_bsa hkta hkda hkpa htd' hpt hpd rfl (Fr5.bsa J.bsa)
  have hAI5 : ActIdle σ' :=
    ⟨fun u hu => (by rw [dn_act] at hu; cases hu), dn_idleOK hkta hkda hkpa htd' hpt hpd hitA hidA (Fr5.idleOK J.act.2)⟩
  have hrun5 : CurRunM σ' := Or.inl (by rw [dn_act]; intro h; cases h)
  have hown5 : CurOwnW Z.T Z.C σ' :=
    dn_own hkta hkda hkpa htd' hpt hpd ⟨d', hdT, rfl⟩ hcscA (fun _ => by rw [SK5.1]; exact hnqD.2)
  have hoff5 : OffOK σ' := dn_off hkta hkda hkpa htd' hpt hpd hcscA (Fr5.off J.off)
  have hnsc5 : NSC Z.N Z.C σ' := dn_nsc hkta hkda hkpa htd' hpt hpd (Fr5.nsc J.nsc)
  have hiso5 : IpcSorted σ' := dn_isorted hkta hkda hkpa htd' hpt hpd (Fr5.isorted J.isorted)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rw [hrs]; simp [tsCode])
  have hpD : ∀ q' ∈ D, q'.bv ≠ sc.bv := fun q' hq' e0 => by
    have hqs : q' = sc := P1.eq_of_bv e0
    rw [hqs] at hq'
    exact J.scOwned_not_dead ht hky hyt (J.jcov.dead sc hq')
  have hkq : ∀ q ∈ D, σ'.kheap q.bv = σa.kheap q.bv := fun q hq =>
    dn_ko (hcD q hq) (htD q hq) (hpD q hq)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs) J hdT hdth hkd
    hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σy umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D su _ (Endp.setUm σy umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkd (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x m, o ≠ .schedContext x m) →
      (σ'.kheap q = some o ↔ σa.kheap q = some o) := fun h1 h2 => dn_oth hkta hkda hkpa htd' hpt hpd h1 h2
  obtain ⟨V', J5⟩ := Ju.wake_postG (by rw [← hKy.2.1] at hIR; exact hIR) hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) dn_skD
    (dn_ksub hkta hkda hkpa htd' hpt hpd) (dn_szKeep hkta hkda hkpa htd' hpt hpd)
    (dn_ykeep hkta hkda hkpa htd' hpt hpd) (dn_mcpKeep hkta hkda hkpa htd' hpt hpd)
    (dn_bufKeep hkta hkda hkpa htd' hpt hpd) (dn_khrb hkta hkda hkpa htd' hpt hpd)
    (dn_ksz hkta hkda hkpa htd' hpt hpd) (dn_kback hkta hkda hkpa htd' hpt hpd) (dn_ipcFr hkta hkda hkpa htd' hpt hpd)
    (dn_ck hkta hkda hkpa htd' hpt hpd)
    (fun q x h => (ho (fun _ e => by cases e) (fun _ _ e => by cases e)).1 h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hkq
    I5' B5' hAI5 (Or.inl dn_act) hrun5 hown5 hoff5 hnsc5 hiso5 hRR htD
  -- the tail
  have hk5 : σ'.kheap d'.bv = some (.tcb { x5 with tcbSchedContext := some sc.bv }) := dn_kd
  have hnr5 : d'.bv ∉ σ'.releaseQueue := by rw [dn_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y' n', ({ x5 with tcbSchedContext := some sc.bv } : Fl4Spec.Tcb).tcbSchedContext = some p →
      σ'.kheap p = some (.schedContext y' n') → Fl4Spec.scActive y' = true := by
    intro p y' n' hp hy
    cases hp
    rw [dn_kp hpd] at hy; cases hy
    have hne := J.curSc_ne_idle hCI hti
    exact hCI.active hne y n (by rw [← hscp]; exact hky)
  have hti5 : d'.bv ≠ σ'.idleThread := by
    show d'.bv ≠ σa.idleThread; exact Ne.symm hidA
  have htc5 : d'.bv ≠ σ'.curThread := by
    show d'.bv ≠ σa.curThread; rw [Fr5.sk.ct]; exact hdc
  have hspec := sendIpc_recv_eqDon hk0 hkd0 hde hstd blk badge.bv g gr e2 hU hkt3 hft hkd3 hx30 hxtsc hdon4 hkd4
    (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr true t.bv e.bv σ =
      Endp.specWakeTailE d'.bv σ' := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

/-- **The sends to a waiting receiver `JAtZ.sendRecvJ0` covers**: no call,
no donation (`can_donate` false, or the head receiver has an SC), the sender
without a fault, any grant (XTopJointXferG's `JAtZ.xferStepGJ`: a cap
inserted into the receiver's CNode slot is redone at `J` before the
dequeue). -/
def SendRecvBasic (σ : Fl4Spec.State Unit) (call don : Bool) (t e : Fl4Spec.ObjRef) : Prop :=
  call = false ∧ ∃ xt d q, σ.kheap t = some (.tcb xt) ∧ xt.tcbFault = none ∧
    σ.kheap e = some (.endpoint (.recvEP (d :: q))) ∧
    (don = false ∨ ∀ xd, σ.kheap d = some (.tcb xd) → xd.tcbSchedContext ≠ none)

/-- **The calls to a waiting receiver `JAtZ.sendCallIJ` covers**: a call
from a sender without a fault, any grant (XTopJointXferG's `JAtZ.xferStepGJ`),
and no reply pushed (the caller has neither the grant nor
the grant-reply right, or the receiver no reply object). -/
def SendRecvCI (σ : Fl4Spec.State Unit) (call g gr : Bool) (t e : Fl4Spec.ObjRef) : Prop :=
  call = true ∧ ∃ xt d q, σ.kheap t = some (.tcb xt) ∧ xt.tcbFault = none ∧
    σ.kheap e = some (.endpoint (.recvEP (d :: q))) ∧
    ((g = false ∧ gr = false) ∨
      ∀ xd, σ.kheap d = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none)

/-- **The plain sends to a waiting receiver without an SC that
`JAtZ.sendDonJ` covers**: no call, `can_donate`, the sender without a
fault, the head receiver without an SC, any grant. -/
def SendRecvDon (σ : Fl4Spec.State Unit) (call don : Bool) (t e : Fl4Spec.ObjRef) : Prop :=
  call = false ∧ don = true ∧ ∃ xt d q, σ.kheap t = some (.tcb xt) ∧ xt.tcbFault = none ∧
    σ.kheap e = some (.endpoint (.recvEP (d :: q))) ∧
    (∀ xd, σ.kheap d = some (.tcb xd) → xd.tcbSchedContext = none)

end

end

end Fl4Proofs.P3
