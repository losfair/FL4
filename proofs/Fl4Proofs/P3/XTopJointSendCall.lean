/-
P3 (DESIGN.md §9), IPC: **a call to a waiting receiver at `J` where the
caller gets no reply** (toward XTopJointSendRecv's `JSendRecvHyp`): the call
meets a receiver without a reply object, or the caller has neither the grant
nor the grant-reply right, so FL4 (and l4v `send_ipc`) makes the caller
`Inactive` instead of pushing a reply.

* `ciSt`: the spec's `set_thread_state Inactive` of the caller `c`, and what
  it keeps (`ciSt_skD`, `ciSt_ksub`, ..., `ciSt_own`, `ciSt_off`, `ciSt_inv`,
  `ciSt_bsa`); `ciSt_swap`: the receiver's `Running` and the caller's
  `Inactive` commute on the spec side (different TCBs, the receiver not the
  current thread), so the wake's frame `DWFr` ends before the caller's step.
* `JAtZ.deadP_dfrCI`, `JAtZ.wake_postCI`: ScSignalDonJ's `deadP_dfr` and
  `wake_postD` with the caller's step after the `DWFr` frame.
* `JAtZ.sendCallIJ`: XTopJointSendRecv's `JAtZ.sendRecvJ0` for the call:
  dequeue, transfer, reply unlink, then the caller `Inactive` on `IRel`
  (`set_thread_state_c`, P1's `sts_all` with the caller's queue bits clear,
  `JAtZ.curBits`), then the receiver `Running` and the tail; the spec's
  outcome `sendIpc_callInactive_eq`.
-/
import Fl4Proofs.P3.XTopJointSendRecv
import Fl4Proofs.P3.XTopJointNoFault
import Fl4Proofs.P3.EpCall2
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The caller's `Inactive` on the spec side -/

section Spec
open Fl4Spec

/-- The caller `c` made `Inactive` (the spec's `setThreadState`). -/
def ciSt (σ : State Unit) (c : ObjRef) (x : Tcb) : State Unit :=
  stsAct (updK σ c (.tcb { x with tcbState := .inactive })) c

variable {σ : State Unit} {c : ObjRef} {x : Tcb}

theorem ciSt_kh {p : ObjRef} (hp : p ≠ c) : (ciSt σ c x).kheap p = σ.kheap p := by
  unfold ciSt; rw [stsAct_kheap]; simp [updK, hp]

theorem ciSt_kc : (ciSt σ c x).kheap c = some (.tcb { x with tcbState := .inactive }) := by
  unfold ciSt; rw [stsAct_kheap]; simp [updK]

theorem ciSt_ne {p : ObjRef} {o : KernelObject} (hp : (ciSt σ c x).kheap p = some o) (ho : ∀ y, o ≠ .tcb y) :
    p ≠ c := by
  rintro rfl; rw [ciSt_kc] at hp; exact ho _ (Option.some.inj hp).symm

theorem ne_of_tcb {p : ObjRef} {o : KernelObject} (hkc : σ.kheap c = some (.tcb x)) (hp : σ.kheap p = some o)
    (ho : ∀ y, o ≠ .tcb y) : p ≠ c := by
  rintro rfl; rw [hkc] at hp; exact ho _ (Option.some.inj hp).symm

theorem ciSt_skD : SkD σ (ciSt σ c x) := by
  unfold ciSt stsAct; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ciSt_rel : (ciSt σ c x).releaseQueue = σ.releaseQueue := by unfold ciSt stsAct; split <;> rfl
theorem ciSt_rq : (ciSt σ c x).readyQueues = σ.readyQueues := by unfold ciSt stsAct; split <;> rfl

/-- The caller, current and resumed, made `Inactive`: a reschedule. -/
theorem ciSt_act (hc : c = σ.curThread) (hres : σ.schedulerAction = .resumeCurThread) :
    (ciSt σ c x).schedulerAction = .chooseNewThread := by
  have h3 : ¬ schedulable c (updK σ c (.tcb { x with tcbState := .inactive })) = true := fun h => by
    obtain ⟨y, _, _, _, hky, _, hr, _⟩ := schedulable_inv h
    simp [updK] at hky; subst hky; simp [runnable] at hr
  unfold ciSt stsAct; rw [if_pos ⟨hc, hres, h3⟩]

theorem ciSt_ksub (hkc : σ.kheap c = some (.tcb x)) : KSub σ (ciSt σ c x) := by
  intro o
  by_cases e : o = c
  · subst e
    refine ⟨fun r cs h _ => ?_, fun t _ => ⟨x, hkc⟩, fun h => ?_⟩
    · rw [ciSt_kc] at h; cases h
    · rw [hkc] at h; cases h
  · rw [ciSt_kh e]; exact KSub.refl σ o

theorem ciSt_szKeep : SzKeep σ (ciSt σ c x) := fun p y n hp =>
  ⟨y, by rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp⟩

theorem ciSt_ykeep (hkc : σ.kheap c = some (.tcb x)) : YKeep σ (ciSt σ c x) := by
  refine ⟨fun p x0 hp => ?_, fun p y n hp => ⟨y, ?_, rfl⟩, fun p y n hp => ⟨y, ?_, rfl⟩⟩
  · by_cases e : p = c
    · subst e; rw [hkc] at hp; cases hp; exact ⟨_, ciSt_kc, rfl⟩
    · exact ⟨x0, by rw [ciSt_kh e]; exact hp, rfl⟩
  · rw [ciSt_kh (ne_of_tcb hkc hp (fun _ h => by cases h))]; exact hp
  · rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp

theorem ciSt_mcpKeep (hkc : σ.kheap c = some (.tcb x)) : McpKeep σ (ciSt σ c x) := fun p x0 hp => by
  by_cases e : p = c
  · subst e; rw [hkc] at hp; cases hp; exact ⟨_, ciSt_kc, rfl⟩
  · exact ⟨x0, by rw [ciSt_kh e]; exact hp, rfl⟩

theorem ciSt_bufKeep (hkc : σ.kheap c = some (.tcb x)) :
    ∀ p x0, σ.kheap p = some (.tcb x0) → ∃ y, (ciSt σ c x).kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x0.tcbIpcBuffer :=
  fun p x0 hp => by
    by_cases e : p = c
    · subst e; rw [hkc] at hp; cases hp; exact ⟨_, ciSt_kc, rfl⟩
    · exact ⟨x0, by rw [ciSt_kh e]; exact hp, rfl⟩

theorem ciSt_khrb (hkc : σ.kheap c = some (.tcb x)) : KhRB σ (ciSt σ c x) := fun p o' hp => by
  by_cases e : p = c
  · subst e; rw [ciSt_kc] at hp; cases hp
    exact ⟨_, hkc, ObjRB.tcb (Or.inr rfl)⟩
  · rw [ciSt_kh e] at hp; exact ⟨o', hp, ObjRB.refl o'⟩

theorem ciSt_ksz (hkc : σ.kheap c = some (.tcb x)) : KSz σ (ciSt σ c x) := fun o ko' hp => by
  by_cases e : o = c
  · subst e; rw [ciSt_kc] at hp; cases hp; exact ⟨_, hkc, rfl⟩
  · rw [ciSt_kh e] at hp; exact ⟨ko', hp, rfl⟩

theorem ciSt_ipcFr (hkc : σ.kheap c = some (.tcb x)) : IpcFrKeep σ (ciSt σ c x) :=
  (IpcFrKeep.of_updTcb (y := { x with tcbState := .inactive }) hkc rfl rfl).trans
    (IpcFrKeep.of_kheap (by unfold ciSt; rw [stsAct_kheap]))

theorem ciSt_kback (hkc : σ.kheap c = some (.tcb x)) : KBack σ (ciSt σ c x) := fun o ko' hp => by
  by_cases e : o = c
  · subst e; rw [ciSt_kc] at hp; cases hp
    refine ⟨_, hkc, ?_, ?_, ?_, fun _ => ⟨x, rfl⟩, ?_, ?_⟩
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  · rw [ciSt_kh e] at hp; exact KBack.of_kheap (σ := σ) (σ' := σ) rfl o ko' hp

theorem ciSt_nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C (ciSt σ c x) := fun n hn y p hy hp =>
  hN n hn y p (by rw [← ciSt_kh (ciSt_ne hy (fun _ h => by cases h))]; exact hy) hp

theorem ciSt_prio (hkc : σ.kheap c = some (.tcb x)) (u : ObjRef) :
    Sched.prioOf (ciSt σ c x) u = Sched.prioOf σ u := by
  by_cases e : u = c
  · subst e; rw [Sched.prioOf_eq ciSt_kc, Sched.prioOf_eq hkc]
  · unfold Sched.prioOf; rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq, ciSt_kh e]

theorem ciSt_isorted (hkc : σ.kheap c = some (.tcb x)) (hS : IpcSorted σ) : IpcSorted (ciSt σ c x) := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · have hp' : σ.kheap p = some (.endpoint y) := by
      rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp
    exact (hS.1 p y hp').congr fun u _ => ciSt_prio hkc u
  · have hp' : σ.kheap p = some (.notification y) := by
      rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp
    exact (hS.2 p y hp').congr fun u _ => ciSt_prio hkc u

theorem ciSt_own {T C : Set U64} (hkc : σ.kheap c = some (.tcb x)) (hO : CurOwnW T C σ) :
    CurOwnW T C (ciSt σ c x) := by
  have e_csc : (ciSt σ c x).curSc = σ.curSc := ciSt_skD.csc
  have e_cons : (ciSt σ c x).consumedTime = σ.consumedTime := ciSt_skD.cons
  have e_rel : (ciSt σ c x).releaseQueue = σ.releaseQueue := ciSt_rel
  have hsc6 : ∀ y n, (ciSt σ c x).kheap (ciSt σ c x).curSc = some (.schedContext y n) →
      σ.kheap σ.curSc = some (.schedContext y n) := by
    intro y n hy
    rw [e_csc] at hy
    by_cases e : σ.curSc = c
    · rw [e, ciSt_kc] at hy; cases hy
    · rw [ciSt_kh e] at hy; exact hy
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr'⟩ | ⟨hcs, hun⟩
  · left
    by_cases hut : u.bv = c
    · rw [hut, hkc] at hkt; cases hkt
      exact ⟨u, hu, _, by rw [hut]; exact ciSt_kc, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
        fun h0 hm => hnr' (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
    · exact ⟨u, hu, xt, by rw [ciSt_kh hut]; exact hkt, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
        fun h0 hm => hnr' (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
  · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y n hy => hun y n (hsc6 y n hy)⟩

theorem ciSt_off (hO : OffOK σ) : OffOK (ciSt σ c x) := by
  have F := (ciSt_skD (σ := σ) (c := c) (x := x))
  intro h0 y n hy ha
  rw [F.cons] at h0 ⊢; rw [F.tm]; rw [F.csc] at hy; rw [F.csc, F.isc] at ha
  by_cases e : σ.curSc = c
  · rw [e, ciSt_kc] at hy; cases hy
  · rw [ciSt_kh e] at hy; exact hO h0 y n hy ha

theorem ciSt_idleOK (hic : σ.idleThread ≠ c) (hO : IdleOK σ) : IdleOK (ciSt σ c x) := by
  have F := (ciSt_skD (σ := σ) (c := c) (x := x))
  obtain ⟨y, h1, h2, h3, h4⟩ := hO
  exact ⟨y, by rw [F.idle, ciSt_kh hic]; exact h1, by rw [F.isc]; exact h2, h3, by rw [F.idle, ciSt_rel]; exact h4⟩

theorem ciSt_bsa (hB : BlockedScActive σ) : BlockedScActive (ciSt σ c x) := by
  refine ⟨fun p y n u xu hp hy hu hq => ?_, fun p y n hp hr => ?_⟩
  · have hp' : σ.kheap p = some (.schedContext y n) := by
      rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp
    by_cases e : u = c
    · subst e; rw [ciSt_kc] at hu; cases hu; simp [Fl4Spec.ipcQueuedThreadState] at hq
    · rw [ciSt_kh e] at hu; exact hB.tcb p y n u xu hp' hy hu hq
  · exact hB.replies p y n (by rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp) hr

/-- `Inv` across the caller's `Inactive`, the caller in no ready queue and
not in the release queue (XTopJointNoFault's `JAtZ.stsCurJ`). -/
theorem ciSt_inv (hk : σ.kheap c = some (.tcb x)) (hI : Inv σ) (hnq : ∀ d p, c ∉ σ.readyQueues d p)
    (hnr : c ∉ σ.releaseQueue) : Inv (ciSt σ c x) := by
  have hI1 : Inv (updK σ c (.tcb { x with tcbState := .inactive })) := by
    refine hI.step (NtfnStep.tcb hk .inactive x.tcbArch) (fun u x0 y h1 h2 hqd hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = c
      · subst e
        rcases hqd with ⟨d, p, hm⟩ | hm
        · exact absurd hm (hnq d p)
        · exact absurd hm hnr
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = c
      · subst e; simp [updK] at h2; subst h2
        exact absurd hc (by intro h; rcases h with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩ <;> cases h)
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [updK, e] using h2
        exact hI.rd u y h2' hc
  exact hI1.qchange (qchange_stsAct _ c)

/-- **The receiver's `Running` and the caller's `Inactive` commute** on the
spec side (the receiver `d` not the current thread, so its `stsAct` asks
nothing; the caller's TCB after is not runnable on either side). -/
theorem ciSt_swap {d : ObjRef} {xd : Tcb} (hcd : c ≠ d) (hdc : d ≠ σ.curThread) :
    stsAct (updK (ciSt σ c x) d (.tcb xd)) d = ciSt (stsAct (updK σ d (.tcb xd)) d) c x := by
  have h1 : stsAct (updK σ d (.tcb xd)) d = updK σ d (.tcb xd) := stsAct_ne hdc
  have h2 : stsAct (updK (ciSt σ c x) d (.tcb xd)) d = updK (ciSt σ c x) d (.tcb xd) :=
    stsAct_ne (by show d ≠ (ciSt σ c x).curThread; rw [(ciSt_skD (σ := σ) (c := c) (x := x)).ct]; exact hdc)
  rw [h1, h2]
  have hs : ∀ σ0 : State Unit, ¬ schedulable c (updK σ0 c (.tcb { x with tcbState := .inactive })) = true := by
    intro σ0 h
    obtain ⟨y, _, _, _, hky, _, hr, _⟩ := schedulable_inv h
    simp [updK] at hky; subst hky; simp [runnable] at hr
  have e1 : ∀ σ0 : State Unit, σ0.curThread = σ.curThread → σ0.schedulerAction = σ.schedulerAction →
      stsAct (updK σ0 c (.tcb { x with tcbState := .inactive })) c =
        if c = σ.curThread ∧ σ.schedulerAction = .resumeCurThread then
          { updK σ0 c (.tcb { x with tcbState := .inactive }) with schedulerAction := .chooseNewThread }
        else updK σ0 c (.tcb { x with tcbState := .inactive }) := by
    intro σ0 h1 h2
    by_cases C : c = σ.curThread ∧ σ.schedulerAction = .resumeCurThread
    · rw [if_pos C]; unfold stsAct; split
      · rfl
      · rename_i h; exact absurd (And.intro (C.1.trans h1.symm) (And.intro (h2.trans C.2) (hs σ0))) h
    · rw [if_neg C]; unfold stsAct; split
      · rename_i h; exact absurd (And.intro (h.1.trans h1) (h2.symm.trans h.2.1)) C
      · rfl
  unfold ciSt
  rw [e1 σ rfl rfl, e1 (updK σ d (.tcb xd)) rfl rfl]
  by_cases C : c = σ.curThread ∧ σ.schedulerAction = .resumeCurThread
  · rw [if_pos C, if_pos C]
    simp only [updK, Function.update_comm hcd] <;> rfl
  · rw [if_neg C, if_neg C]
    simp only [updK, Function.update_comm hcd] <;> rfl

end Spec

/-! ## The wake with the caller's `Inactive` at `J`, and the call -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a `DWFr` step and a change of no dead
object** (`hkq`; ScSignalDonJ's `JAtZ.deadP_dfr` with the heap of the dead
read at `σa`). -/
theorem JAtZ.deadP_dfrCI (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : Fl4Spec.ObjRef} {s3 : S}
    {σa σ3 : Fl4Spec.State Unit} (F : DWFr r t σ σa) (hkq : ∀ q ∈ D, σ3.kheap q.bv = σa.kheap q.bv)
    (hidl : σ3.idleThread = σ.idleThread) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK)
    hidl hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state, (null) bound notification and SC kept
    rw [hkq q hq]
    obtain ⟨t', ht', e⟩ := J.obj.tcb q.bv x hx
    have htq : t' = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t' ht')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t' ht'
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t' = P1.boundA t' from rfl, d3, optRef_zero]
    obtain ⟨st', bn, fl, ar, sc, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, ?_⟩
    · show st' = x.tcbState
      rcases hs with ⟨⟨e, -⟩ | ⟨-, e, -⟩, -, -⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e] at h0; simp [tsCode] at h0
      · exact absurd e (ht t' hq)
    · show bn = x.tcbBoundNotification
      rcases hs with ⟨-, -, e | e⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e, hbn]
      · exact absurd e (ht t' hq)
    · show sc = x.tcbSchedContext ∨ sc = none
      by_cases e : sc = x.tcbSchedContext
      · exact Or.inl e
      · exact absurd (F.tsc _ x _ hx hk3 e).1 (ht t' hq)
  · -- a dead endpoint: idle, so holding nobody
    rw [hkq q hq]
    obtain ⟨y, hy, hc⟩ := F.epF hx
    rcases hc with rfl | ⟨-, hm⟩
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
  · -- a dead notification: not waiting, unbound
    rw [hkq q hq]
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, d2, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, -, hobj, hbd, hsc'⟩ := F.ntfnF hx
    have hbn : x.ntfnBoundTcb = none := by
      rw [hR.bound, show nBoundA n' = P1.ntfnBtA n' from rfl, d2, optRef_zero]
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, (hobj hnw).imp id And.right, ?_, hsc'⟩
    rcases hbd with e | e
    · exact e
    · rw [e, hbn]
  · -- a dead reply: naming nobody
    rw [hkq q hq]
    obtain ⟨y, hy, -, hc⟩ := F.replyF hx
    refine ⟨y, hy, ?_⟩
    rcases hc with e | ⟨hxt, -⟩
    · exact e
    · exfalso
      obtain ⟨r', hr', e⟩ := J.obj.reply q.bv x hx
      have heq : r' = q := P1.eq_of_bv e
      subst heq
      have d4 := hd.2.2.2.1 (J.zH.2.2.1 r' hr')
      obtain ⟨x', hk', hx'⟩ := J.xtop.ipc.toE.reply r' hr'
      rw [hx] at hk'; cases hk'
      have d4' : L.mem s (Endp.rTcbA r') = 0#u64 := d4
      rw [hx', d4', optRef_zero] at hxt
      cases hxt
  · -- an SC: its thread kept (a changed one is a notification's SC, not dead), its notification kept or cut
    rw [hkq q hq]
    obtain ⟨rf, nt, tc, hk3, -, hn⟩ := F.scF hx
    refine ⟨_, hk3, ?_, hn⟩
    show tc = x.scTcb ∨ tc = none
    by_cases e : tc = x.scTcb
    · exact Or.inl e
    · obtain ⟨-, o, xo, ho, hsc⟩ := F.scb q.bv x n _ n hx hk3 e
      exact absurd hd (J.ntfnSc_not_dead hx ho hsc)

set_option maxHeartbeats 8000000 in
/-- **A wake without a donation, then the caller's `Inactive`, keeps `JAtZ`**
(ScSignalDonJ's `JAtZ.wake_postD` for the frame `DWFr` up to `σa`, then
`ciSt`: the caller `c`'s TCB to `Inactive`, the action maybe a reschedule;
`c` not dead). -/
theorem JAtZ.wake_postCI (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t c : Fl4Spec.ObjRef}
    {s' : S} {σa : Fl4Spec.State Unit} {xc : Fl4Spec.Tcb} (hkc : σa.kheap c = some (.tcb xc))
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' (ciSt σa c xc))
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : DWFr n t σ σa) (I3 : Inv (ciSt σa c xc)) (B3 : BlockedScActive (ciSt σa c xc))
    (hAI3 : ActIdle (ciSt σa c xc))
    (hcur3 : (ciSt σa c xc).schedulerAction = .chooseNewThread ∨ CurInv (ciSt σa c xc))
    (hrun3 : CurRunM (ciSt σa c xc))
    (hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64)
    (ht : ∀ q ∈ D, q.bv ≠ t) (hcD : ∀ q ∈ D, q.bv ≠ c) (htT : ∃ u ∈ Z.T, u.bv = t) :
    ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a (ciSt σa c xc) := by
  set σ' := ciSt σa c xc with hσ'
  have G := (ciSt_skD (σ := σa) (c := c) (x := xc))
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 (G.cdt.trans F.sk.cdt) (G.orig.trans F.sk.orig)
    (F.ksub.trans (ciSt_ksub hkc)) hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck0 := F.callKeep
  have ck : (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
      (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
      (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) := by
    refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
    · obtain ⟨y', h1, h2⟩ := ck0.1 q y n hq
      exact ⟨y', by rw [ciSt_kh (ne_of_tcb hkc h1 (fun _ h => by cases h))]; exact h1, h2⟩
    · obtain ⟨x', h1, h2⟩ := ck0.2.1 q x hq
      exact ⟨x', by rw [ciSt_kh (ne_of_tcb hkc h1 (fun _ h => by cases h))]; exact h1, h2⟩
    · exact ck0.2.2 p x n (by rw [← ciSt_kh (ciSt_ne hp (fun _ h => by cases h))]; exact hp)
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    have hy' : σa.kheap d.bv = some (.reply y) := by
      rw [← ciSt_kh (ciSt_ne hy (fun _ h => by cases h))]; exact hy
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
    J.deadP_dfrCI F (fun q hq => ciSt_kh (hcD q hq)) hidl0 hS3 hIR.1 hw k3 hAI3.1
      (J.yld.frame k2 (F.ykeep.trans (ciSt_ykeep hkc))) (F.ykeep.trans (ciSt_ykeep hkc)) ht
  have hsz : SzKeep σ σ' := fun p y n hp => by
    obtain ⟨y0, hy0⟩ := ciSt_szKeep (σ := σa) (c := c) (x := xc) p y n hp
    exact F.szKeep p y0 n hy0
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hsz q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 hidl0 hisc0).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 (G.ct.trans F.sk.ct) (G.csc.trans F.sk.csc)
    (fun sl h => Or.inl (by rw [← F.sk.orig, ← G.orig]; exact h))
    (by rw [G.arch, F.sk.arch])
    (fun q ao h => by
      have h1 := F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
        (fun _ e => by cases e) (fun _ e => by cases e)
      rw [ciSt_kh (ne_of_tcb hkc h1 (fun _ e => by cases e))]; exact h1) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 (F.khrb.trans (ciSt_khrb hkc))
  have hbuf : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
    fun p x hp => by
      obtain ⟨y, hy, e⟩ := F.bufKeep p x hp
      obtain ⟨z, hz, e'⟩ := ciSt_bufKeep hkc p y hy
      exact ⟨z, hz, e'.trans e⟩
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 (F.ykeep.trans (ciSt_ykeep hkc)),
      J.mcp.frame k1 (F.mcpKeep.trans (ciSt_mcpKeep hkc)), J.buf.frame kb hbuf, hRP',
      J.apart.sc_frame hks hsz, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hidl0 hisc0), hkern,
      J.cnW_utc hw hF.1 (G.cdt.trans F.sk.cdt) (G.orig.trans F.sk.orig) (G.arch.trans F.sk.arch) hDbg,
      ciSt_nsc (F.nsc J.nsc), I3, hcur3, ciSt_own hkc (F.own htT J.own), ciSt_off (F.off J.off),
      hAI3, B3, ciSt_isorted hkc (F.isorted J.isorted), hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 (F.ksz.trans (ciSt_ksz hkc))
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) (G.arch.trans F.sk.arch) (fun q ao h => by
      have h1 := F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
        (fun _ e => by cases e) (fun _ e => by cases e)
      rw [ciSt_kh (ne_of_tcb hkc h1 (fun _ e => by cases e))]; exact h1) hsz hF.1 (F.kback.trans' (ciSt_kback hkc)) (F.ipcFr.trans (ciSt_ipcFr hkc)) hC R hKd (G.orig.trans F.sk.orig) (J.idleW_keep hS3 hidl0 hisc0).1 J.zD⟩

set_option maxHeartbeats 64000000 in
/-- **A call to a waiting receiver at `J` where the caller gets no reply**
(module docstring): the receiver has no reply object, or the caller neither
the grant nor the grant-reply right (`hno`); as `JAtZ.sendRecvJ0` up to the
reply unlink, then the caller `Inactive` on `IRel` (its queue bits clear by
`JAtZ.curBits`: in no ready queue, `hnq`, l4v `ct_not_in_q`, and not in the
release queue, `CurInv.notRel`), the receiver `Running`, `JAtZ` by
`JAtZ.wake_postCI` (the spec's two state changes swapped, `ciSt_swap`), the
tail `JAtZ.sendTailJ`; the spec's outcome `sendIpc_callInactive_eq`. -/
theorem JAtZ.sendCallIJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrs : xt.tcbState = .restart) (hft : xt.tcbFault = none) (hct : σ.curThread = t.bv)
    (hres : σ.schedulerAction = .resumeCurThread) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hno : (g = false ∧ gr = false) ∨
      ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) :
    endpoint.send_ipc st arI s a blk true badge g gr don t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr don t.bv e.bv σ).1,
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
  rintro s2 ⟨x2, um2, y, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksy, hKy, hCnKy, hyk⟩
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
  have hks2 : L.ksb s2 = L.ksb y := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) ∧
      P1.WritesIn st y s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) y b ∨ RcvBufW xd b) ∧
      CFr e.bv d'.bv σy σ3 ∧ IK d'.bv σy σ3 ∧ SKeep σy σ3 ∧ σ3.curThread = σy.curThread ∧
      σ3.schedulerAction = σy.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d')) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, x2, _, rfl, hR2, hS2', hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc, hq2, hW2, F2, Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA⟩
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
      have hW3' : P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc], ?_, hW3',
        footW_trans F2 (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2)⟩
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
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3⟩
  have hxt3 := hR3.at_tcb ht hkt3
  have hks3 : L.ksb s3 = L.ksb y := hW3.1
  -- the caller's facts for its `Inactive`
  have hCI : CurInv σ := J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  obtain ⟨hqb, hrb'⟩ := J.curBits ht hnq hnrT
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = 2 := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st, hrs]; rfl
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (Or.inr (Or.inl hw3))
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := (IpcRel.ofSRN hR3 hS3).2.2.1
  have hna3 : L.actionW s3 ≠ t := by
    obtain ⟨Q, R', hcq, -⟩ := hSR3.lists
    have h := hSR3.act
    rw [hact3, hsay, hres] at h
    have ha0 : L.actionW s3 = 0#u64 := by unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
    rw [ha0]; intro h'; exact (hcq.tcbs t ht).ne0 (by rw [← h']; rfl)
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  have hstsT := WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hkt3 hqt3
      (by rw [hrs]; decide) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot hSR3 ht sched.TS_INACTIVE))
    (WP.spec_and (P1.sts_all s3 t _ Q0 R0 h3 hB3 hX3 hS3' hSg3 htH P1.not_blocked_inactive P1.inactive_ne
        (Or.inr hnbt3) (hX3.noref (hTP t htH) hnrp3 (fun e0 => hnbt3 (Or.inr (Or.inl e0))))
        ⟨fun c hc' p hp hm => absurd hm (h0.notQ htH hqb hc' hp), fun c hc' hm => absurd hm (h0.notR htH hrb' hc'),
          fun e0 => absurd e0 hna3⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 t sched.TS_INACTIVE h3 htH))
  -- FL4: no reply pushed, the caller `Inactive`
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ sched.set_thread_state st s3 t sched.TS_INACTIVE = ok r.1)
    ?_ ?_
  · by_cases hi : (L.mem s (tReplyA d') != 0#u64) = true
    · rw [if_pos hi]
      have hgg : g = false ∧ gr = false := by
        rcases hno with h | hn
        · exact h
        · exfalso
          have hr0 := hn xd hkd _ _ _ hstd
          rw [hr0] at hrep
          have h00 := optRef_none hrep
          rw [h00] at hi
          simp at hi
      obtain ⟨rfl, rfl⟩ := hgg
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
    · rw [if_neg hi]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
  rintro ⟨s4, a4⟩ ⟨ha4, hs4⟩
  simp only at ha4 hs4
  subst ha4
  try dsimp only
  have hpost := hstsT
  rw [hs4] at hpost
  obtain ⟨⟨⟨hR4, hS4⟩, hW4⟩, ⟨h4, hB4, hX4, hS4', hSg4, -, k4⟩, fu4⟩ := (WP.spec_ok _).1 hpost
  have hkd4 : (ciSt σ3 t.bv xt).kheap d'.bv = some (.tcb x3) := by rw [ciSt_kh (Ne.symm htd')]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, (ciSt σ3 t.bv xt).kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z (by rw [← ciSt_kh (ciSt_ne hz (fun _ h => by cases h))]; exact hz)
  have hx4 : d' ∈ {y | y ∈ X3 ∧ y ≠ t} ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := by
    rcases hx3 with h | h
    · exact Or.inl ⟨h, Ne.symm htd⟩
    · right
      have e0 : L.mem s4 (P1.stA d') = L.mem s3 (P1.stA d') := by
        rw [P1.stA_eq]
        exact k4.fld d' hdH _ (by simp) (by simp) (by simp) (by simp) (fun e1 => absurd e1 (Ne.symm htd))
      rw [e0]; exact h
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' := fun r hr => by
    rcases k4.rtcb r hr with e0 | ⟨-, e0⟩
    · rw [e0]; exact hnr3 r hr
    · rw [e0]; intro h0'; exact hdta.ne0 (by rw [← h0']; rfl)
  have hks4 : L.ksb s4 = L.ksb y := hW4.1.trans hks3
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q0 R0 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3, hcty]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)) d'.bv = ciSt σa t.bv xt :=
    ciSt_swap htd' hdc3
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 (ciSt σa t.bv xt) := by
    rw [← heq5]; exact hIR0
  have hW4' : P1.WritesIn st y s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) :=
    hW3.trans1 (hW4.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb)))))
  have hW5' : P1.WritesIn st y s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr (X := {y | y ∈ X3 ∧ y ≠ t}) (fun y hy => hXc3 y hy.1))⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have Fr5 : CFr e.bv d'.bv σy σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σy (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σy σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : SKeep σy σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hnqD : NotQueued σy d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rq dm p _ hm
      rw [hkdy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rel _ hm
      rw [hkdy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (Jy.inv.rd d'.bv xd hkdy (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((Jy.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σa.schedulerAction = σy.schedulerAction := by
    rw [hσa, stsAct_ne (by show d'.bv ≠ σ3.curThread; exact hdc3)]; exact hact3
  -- the caller's `Inactive` after the wake (`ciSt_swap`)
  have hnqT : ∀ dm p, t.bv ∉ σa.readyQueues dm p := by rw [IK5.2.1, hrqy]; exact hnq
  have hnrT' : t.bv ∉ σa.releaseQueue := by rw [IK5.2.2.1, hrly]; exact hnrT
  have I5' : Inv (ciSt σa t.bv xt) := ciSt_inv hkta I5 hnqT hnrT'
  have B5' : BlockedScActive (ciSt σa t.bv xt) := ciSt_bsa (Fr5.bsa Jy.bsa)
  have hcn : (ciSt σa t.bv xt).schedulerAction = .chooseNewThread :=
    ciSt_act (by rw [Fr5.sk.ct, hcty, hct]) (by rw [act5, hsay, hres])
  have hidT : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle, hidy, ← hct]; exact fun e0 => hti e0.symm
  have hAI5 : ActIdle (ciSt σa t.bv xt) :=
    ⟨fun u hu => (by rw [hcn] at hu; cases hu), ciSt_idleOK hidT (Fr5.idleOK Jy.act.2)⟩
  have hrun5 : CurRunM (ciSt σa t.bv xt) := Or.inl (by rw [hcn]; intro h; cases h)
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rw [hrs]; simp [tsCode])
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs) Jy hdT hdth hkdy
    hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hdT hkdy (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σy umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D su _ (Endp.setUm σy umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkdy (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  obtain ⟨V', J5⟩ := Ju.wake_postCI hkta (by rw [← hKy.2.1] at hIR; exact hIR) hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) I5' B5' hAI5
    (Or.inl hcn) hrun5 hRR htD hcD ⟨d', hdT, rfl⟩
  -- the tail
  have G := (ciSt_skD (σ := σa) (c := t.bv) (x := xt))
  have hk5 : (ciSt σa t.bv xt).kheap d'.bv = some (.tcb x5) := by
    rw [ciSt_kh (Ne.symm htd'), hσa, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ (ciSt σa t.bv xt).releaseQueue := by rw [ciSt_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → (ciSt σa t.bv xt).kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya : σa.kheap p = some (.schedContext y n) := by
      rw [← ciSt_kh (ciSt_ne hy (fun _ h => by cases h))]; exact hy
    have hy0 := SK5.2.2.2 p y n hya
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := Jy.inv.back _ _ _ hkdy hp'
    rw [hy0] at hky'; cases hky'
    exact Jy.bsa.tcb p y n d'.bv xd hy0 hyt hkdy (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ (ciSt σa t.bv xt).idleThread := by
    rw [G.idle, Fr5.sk.idle]
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := Jy.act.2
    rw [← h, hkdy] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ (ciSt σa t.bv xt).curThread := by rw [G.ct, Fr5.sk.ct, hcty]; exact hdc
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨hg, hr⟩
    rcases hno with ⟨rfl, rfl⟩ | hn
    · rcases hg with h | h <;> cases h
    · exact hr (hn xd hkd _ _ _ hstd)
  have hspec := sendIpc_callInactive_eq (don := don) hk hkd hde htd' hstd blk badge.bv g gr hcond e2 hU hkt3 hkd3
    (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr don t.bv e.bv σ =
      Endp.specWakeTailE d'.bv (ciSt σa t.bv xt) := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

end

end

end Fl4Proofs.P3
