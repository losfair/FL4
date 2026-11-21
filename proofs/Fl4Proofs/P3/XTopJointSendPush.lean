/-
P3 (DESIGN.md §9), IPC: **a call to a waiting receiver at `J` that pushes a
reply without a donation** (toward XTopJointSendDon's `JSendRecvHyp`): a call
with the grant or grant-reply right to a receiver with a reply object, where
the receiver has an SC or the call does not donate. FL4 (and l4v
`send_ipc`/`reply_push`) links the receiver's (unlinked) reply to the caller
and blocks the caller on it; no SC moves, so the call stacks stay.

* IpcPushCore's `reply_push_iC`: IpcEpSteps' `reply_push_iG` from `IpcCore`.
* `ipc.reply_push.nd` (P1): without a donation `reply_push` is the reply's
  TCB word and `set_blocked_on_reply`, with `KW` footprint.
* `Sched.schedule_tcb_w`, `Ipc.set_blocked_on_reply_cn`: the caller's block
  on the reply inside `CnW`.
* `pushSt` (IpcEpSteps) on the spec side: what it keeps (`ps_skD`, ...,
  `ps_inv`, `ps_bsa`), `ps_swap` (the receiver's `Running` and the push
  commute).
* `JAtZ.wake_postGR`: XTopJointSendDon's `JAtZ.wake_postG` with the free
  replies and the receive-bound replies after given back instead of the
  replies kept (a push binds a free reply to a thread blocked on it).
* **`JAtZ.sendCallPJ`**: dequeue, transfer, reply unlink, the push on `IRel`
  (`reply_push_iG`, P1's `reply_push.ipc`/`reply_push.nd`), the receiver
  `Running`, `JAtZ` by `wake_postGR` at `pushSt`, the tail; the spec's outcome
  `sendIpc_call_eq`.
-/
import Fl4Proofs.P3.XTopJointSendDon
import Fl4Proofs.P3.EpCall
import Fl4Proofs.P3.IpcPushCore
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

/-! ## P1: `reply_push` without a donation -/

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {Es : Set U64}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

set_option maxHeartbeats 4000000 in
/-- **`reply_push` without a donation** (the call does not donate, or the
callee has an SC): the reply's TCB word and `set_blocked_on_reply`, inside
`KW`. -/
theorem ipc.reply_push.nd {A : Type} {ar : machine.Arch A} (s : S) (a : A)
    (caller callee r : U64) (can_donate : Bool)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64) (hce : callee ∈ T)
    (hne : callee ≠ caller)
    (hcA : L.mem s (scA caller) ≠ 0#u64 → L.mem s (scA caller) ∈ Ac)
    (hnd : can_donate = false ∨ L.mem s (scA callee) ≠ 0#u64) :
    ipc.reply_push st ar s a caller callee r can_donate ⦃ s' a' => a' = a ∧ Foot st T Cs Sg Scs Z Es s s' ∧
      sched.set_blocked_on_reply st (L.wr s (rTcbA r) caller) caller r = ok s' ⦄ := by
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  unfold ipc.reply_push
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Reply.set_tcb.spec as ⟨s1, e1⟩
  subst e1
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (rTcbA r) caller) :=
    foot_wr (h.omega _ (hrΩ r hr).1).1 (kw_sg (hO.tcbW hr))
  have q1 := (omega_wr (v := caller) h (hrΩ r hr).1).1
  refine WP.spec_bind (Fl4Proofs.P3.spec_self (WP.spec_and (sched.set_blocked_on_reply.ipc s caller r Q R h hXc hx
    hB hX hS hSg hcl hcq hcr hca hci hcold hr hr00 hr0 hcA)
    (sched.set_blocked_on_reply.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ caller r q1 hcl))) ?_
  intro s2 e2
  have hpost' := WP.spec_and (sched.set_blocked_on_reply.ipc s caller r Q R h hXc hx
    hB hX hS hSg hcl hcq hcr hca hci hcold hr hr00 hr0 hcA)
    (sched.set_blocked_on_reply.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ caller r q1 hcl)
  rw [e2] at hpost'
  obtain ⟨⟨-, -, -, -, -, f2', -, -, -, -, -⟩, f2⟩ := (WP.spec_ok _).1 hpost'
  have f02 := f1.trans f2
  have sc2 : L.mem s2 (scA callee) = L.mem s (scA callee) := by
    rw [scA_eq]; exact f2' callee hce _ (by simp) (by simp) (fun e => absurd e hne)
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ⟨rfl, f02, e2⟩
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · rename_i hi1
    cases can_donate
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨rfl, f02, e2⟩
    · exfalso
      rcases hnd with hnd | hnd
      · cases hnd
      · exact hnd (by rw [← sc2, ← ei1]; exact hi1)
  · exact (WP.spec_ok _).2 ⟨rfl, f02, e2⟩

end

end Fl4Proofs.P1

/-! ## The caller's block on the reply inside `CnW` -/

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `schedule_tcb` writes in any footprint that holds the scheduler's. -/
theorem schedule_tcb_w {N T C : Set U64} {c : U64} {s s1 : S} {σ : Fl4Spec.State Unit} {W : U64 → Prop}
    (hS : SchedRel st N T C c s σ) (h1 : WritesIn st s s1 W) (hW : ∀ b, SFoot st T c s b → W b) (t : U64) :
    sched.schedule_tcb st s1 t ⦃ s' => WritesIn st s s' W ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hact : sched.set_action st s1 sched.ACTION_CHOOSE_NEW ⦃ s' => WritesIn st s s' W ⦄ := by
    refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
    rintro s' rfl
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    refine (h1.trans ((writesIn_wr ?_).mono fun b hb => ?_)).mono fun b hb => by rcases hb with hb | hb <;> exact hb
    · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN ho (by simp [layout.node.SCHED_ACTION])
    · apply hW
      rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]
      exact Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec' as ⟨t1, _ht1⟩
  step as ⟨b, _hb⟩
  split
  · step with sched.action.spec' as ⟨i, _hi⟩
    split
    · step with sched.is_schedulable.spec' as ⟨b1, _hb1⟩
      split
      · exact (WP.spec_ok _).mpr h1
      · exact hact
    · exact (WP.spec_ok _).mpr h1
  · exact (WP.spec_ok _).mpr h1

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`set_blocked_on_reply`'s footprint** after the reply's TCB word
(`hw1`): the caller's state and reply words, then `schedule_tcb`. -/
theorem set_blocked_on_reply_cn (hP : EPlaced T E R B) {s s1 : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t r : U64} (ht : t ∈ T) (hr : r ∈ R)
    (hw1 : WritesIn st s s1 (fun b => b.val = r.val)) :
    sched.set_blocked_on_reply st s1 t r ⦃ s' => WritesIn st s s' (CnW (st := st) T N C E R c s σ) ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hta := hP.tcb t ht
  unfold sched.set_blocked_on_reply
  step with Fl4Proofs.P1.obj.Tcb.set_state.spec as ⟨s1a, e1a⟩
  step with Fl4Proofs.P1.obj.Tcb.set_reply_obj.wr as ⟨s1b, e1b⟩
  have w2 : WritesIn st s1 s1a (SFoot st T c s1) := by
    rw [e1a, show P1.stA t = tStA t from rfl, tStA_eq]
    exact writesIn_tcb hc.tcbs ht (by unfold SOff SOffL; decide) (by simp) _
  have w3 : WritesIn st s1a s1b (fun b => b = tReplyA t) := by
    rw [e1b]; exact writesIn_wr (a_reply hta).1
  have hks1 : L.ksb s1 = L.ksb s := hw1.1
  have W0 : WritesIn st s s1b (CnW (st := st) T N C E R c s σ) := ((hw1.trans w2).trans w3).mono fun b hb => by
    rcases hb with (hb | hb) | hb
    · exact Or.inr (Or.inr ⟨r, hr, hb⟩)
    · exact Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks1).1 hb)))
    · subst hb
      exact Or.inl (Or.inr ⟨t, ht, 3360, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        val_reply hta⟩)
  exact schedule_tcb_w hS W0 (fun b h => Or.inl (Or.inl (KFoot.of_sfoot h))) t

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The push on the spec side -/

section Spec
open Fl4Spec

section Ps
variable {σ : State Unit} {t w : ObjRef} {xr : Reply} {xt : Tcb}

theorem ps_kt : (pushSt σ t w xr xt).kheap t = some (.tcb { xt with tcbState := .blockedOnReply w }) := by
  unfold pushSt; rw [stsAct_kheap]; simp [updK]

theorem ps_kw (hwt : w ≠ t) : (pushSt σ t w xr xt).kheap w = some (.reply { xr with replyTcb := some t }) := by
  unfold pushSt; rw [stsAct_kheap]; simp [updK, hwt]

theorem ps_ko {q : ObjRef} (h1 : q ≠ t) (h2 : q ≠ w) : (pushSt σ t w xr xt).kheap q = σ.kheap q := by
  unfold pushSt; rw [stsAct_kheap]; simp [updK, h1, h2]

theorem ps_skD : SkD σ (pushSt σ t w xr xt) := by
  unfold pushSt stsAct; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ps_rel : (pushSt σ t w xr xt).releaseQueue = σ.releaseQueue := by unfold pushSt stsAct; split <;> rfl
theorem ps_rq : (pushSt σ t w xr xt).readyQueues = σ.readyQueues := by unfold pushSt stsAct; split <;> rfl

/-- The caller, current and resumed, blocked: a reschedule. -/
theorem ps_act (hc : t = σ.curThread) (hres : σ.schedulerAction = .resumeCurThread) :
    (pushSt σ t w xr xt).schedulerAction = .chooseNewThread := by
  have h3 : ¬ schedulable t (updK (updK σ w (.reply { xr with replyTcb := some t })) t
      (.tcb { xt with tcbState := .blockedOnReply w })) = true := fun h => by
    obtain ⟨y, _, _, _, hky, _, hr, _⟩ := schedulable_inv h
    simp [updK] at hky; subst hky; simp [runnable] at hr
  unfold pushSt stsAct; rw [if_pos ⟨hc, hres, h3⟩]

variable (hkt : σ.kheap t = some (.tcb xt)) (hkw : σ.kheap w = some (.reply xr)) (hwt : w ≠ t)
include hkt hkw hwt

/-- An object other than a TCB or a reply is kept, both ways. -/
theorem ps_oth {q : ObjRef} {o : KernelObject} (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ x, o ≠ .reply x) :
    (pushSt σ t w xr xt).kheap q = some o ↔ σ.kheap q = some o := by
  by_cases e1 : q = t
  · subst e1; rw [ps_kt, hkt]; exact ⟨fun h => absurd (Option.some.inj h).symm (h1 _),
      fun h => absurd (Option.some.inj h).symm (h1 _)⟩
  by_cases e2 : q = w
  · subst e2; rw [ps_kw hwt, hkw]; exact ⟨fun h => absurd (Option.some.inj h).symm (h2 _),
      fun h => absurd (Option.some.inj h).symm (h2 _)⟩
  rw [ps_ko e1 e2]

theorem ps_ksub : KSub σ (pushSt σ t w xr xt) := by
  intro o
  by_cases e1 : o = t
  · subst e1
    exact ⟨fun r cs h _ => (by rw [ps_kt] at h; cases h), fun _ _ => ⟨xt, hkt⟩, fun h => (by rw [hkt] at h; cases h)⟩
  by_cases e2 : o = w
  · subst e2
    exact ⟨fun r cs h _ => (by rw [ps_kw hwt] at h; cases h), fun _ h => (by rw [ps_kw hwt] at h; cases h),
      fun h => (by rw [hkw] at h; cases h)⟩
  rw [ps_ko e1 e2]; exact KSub.refl σ o

theorem ps_szKeep : SzKeep σ (pushSt σ t w xr xt) := fun q x m hq =>
  ⟨x, (ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hq⟩

theorem ps_ykeep : YKeep σ (pushSt σ t w xr xt) := by
  refine ⟨fun q x hq => ?_, fun q x m hq => ⟨x, (ps_oth hkt hkw hwt (fun _ h => by cases h)
    (fun _ h => by cases h)).2 hq, rfl⟩, fun q x m hq => ⟨x, (ps_oth hkt hkw hwt (fun _ h => by cases h)
    (fun _ h => by cases h)).1 hq, rfl⟩⟩
  by_cases e1 : q = t
  · subst e1; rw [hkt] at hq; cases hq; exact ⟨_, ps_kt, rfl⟩
  by_cases e2 : q = w
  · subst e2; rw [hkw] at hq; cases hq
  exact ⟨x, by rw [ps_ko e1 e2]; exact hq, rfl⟩

theorem ps_tcbF {q : ObjRef} {x : Tcb} (hq : σ.kheap q = some (.tcb x)) :
    ∃ ts, (pushSt σ t w xr xt).kheap q = some (.tcb { x with tcbState := ts }) := by
  by_cases e1 : q = t
  · subst e1; rw [hkt] at hq; cases hq; exact ⟨_, ps_kt⟩
  by_cases e2 : q = w
  · subst e2; rw [hkw] at hq; cases hq
  exact ⟨x.tcbState, by rw [ps_ko e1 e2]; exact hq⟩

theorem ps_mcpKeep : McpKeep σ (pushSt σ t w xr xt) := fun q x hq => by
  obtain ⟨ts, h⟩ := ps_tcbF hkt hkw hwt hq; exact ⟨_, h, rfl⟩

theorem ps_bufKeep : ∀ q x, σ.kheap q = some (.tcb x) →
    ∃ z, (pushSt σ t w xr xt).kheap q = some (.tcb z) ∧ z.tcbIpcBuffer = x.tcbIpcBuffer := fun q x hq => by
  obtain ⟨ts, h⟩ := ps_tcbF hkt hkw hwt hq; exact ⟨_, h, rfl⟩

theorem ps_ksz : KSz σ (pushSt σ t w xr xt) := fun q o' hq => by
  by_cases e1 : q = t
  · subst e1; rw [ps_kt] at hq; cases hq; exact ⟨_, hkt, rfl⟩
  by_cases e2 : q = w
  · subst e2; rw [ps_kw hwt] at hq; cases hq; exact ⟨_, hkw, rfl⟩
  rw [ps_ko e1 e2] at hq; exact ⟨o', hq, rfl⟩

theorem ps_kback : KBack σ (pushSt σ t w xr xt) := fun q o' hq => by
  by_cases e1 : q = t
  · subst e1; rw [ps_kt] at hq; cases hq
    refine ⟨_, hkt, ?_, ?_, ?_, fun _ => ⟨xt, rfl⟩, ?_, ?_⟩
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  by_cases e2 : q = w
  · subst e2; rw [ps_kw hwt] at hq; cases hq
    refine ⟨_, hkw, ?_, ?_, fun _ => ⟨xr, rfl⟩, ?_, ?_, ?_⟩
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  rw [ps_ko e1 e2] at hq; exact KBack.of_kheap (σ := σ) (σ' := σ) rfl q o' hq


theorem ps_ipcFr : IpcFrKeep σ (pushSt σ t w xr xt) :=
  IpcFrKeep.of_kbackF (ps_kback hkt hkw hwt)
    (fun q x hq => by obtain ⟨ts, h⟩ := ps_tcbF hkt hkw hwt hq; exact ⟨_, h, rfl, rfl⟩)
    (fun q vms => ps_oth hkt hkw hwt (fun _ e => by cases e) (fun _ e => by cases e))

theorem ps_ck :
    (∀ q y' m, σ.kheap q = some (.schedContext y' m) → ∃ y'', (pushSt σ t w xr xt).kheap q =
      some (.schedContext y'' m) ∧ y''.scReplies = y'.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', (pushSt σ t w xr xt).kheap q = some (.reply x') ∧
      x'.replySc = x.replySc) ∧
    (∀ q x m, (pushSt σ t w xr xt).kheap q = some (.schedContext x m) →
      ∃ x0, σ.kheap q = some (.schedContext x0 m)) := by
  refine ⟨fun q y' m hq => ⟨y', (ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).2 hq, rfl⟩,
    fun q x hq => ?_, fun q x m hq => ⟨x, (ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hq⟩⟩
  by_cases e2 : q = w
  · subst e2; rw [hkw] at hq; cases hq; exact ⟨_, ps_kw hwt, rfl⟩
  by_cases e1 : q = t
  · subst e1; rw [hkt] at hq; cases hq
  exact ⟨x, by rw [ps_ko e1 e2]; exact hq, rfl⟩

/-- A free reply after the push was free before (the pushed one is bound). -/
theorem ps_free {d : U64} (hd : Sched.Free (pushSt σ t w xr xt) d) : Sched.Free σ d := by
  obtain ⟨y, hy, hyt⟩ := hd
  by_cases e2 : d.bv = w
  · rw [e2, ps_kw hwt] at hy; cases hy; simp at hyt
  by_cases e1 : d.bv = t
  · rw [e1, ps_kt] at hy; cases hy
  exact ⟨y, by rw [← ps_ko e1 e2]; exact hy, hyt⟩

/-- A reply bound to a receive-blocked thread after the push was one before. -/
theorem ps_recvB {d : U64} (hd : RecvB (pushSt σ t w xr xt) d) : RecvB σ d := by
  obtain ⟨y, u, xu, hy, hyu, hu, hb⟩ := hd
  by_cases e2 : d.bv = w
  · rw [e2, ps_kw hwt] at hy; cases hy
    simp only [Option.some.injEq] at hyu; subst hyu
    rw [ps_kt] at hu; cases hu; simp [receiveBlocked] at hb
  by_cases e1 : d.bv = t
  · rw [e1, ps_kt] at hy; cases hy
  have hy' : σ.kheap d.bv = some (.reply y) := by rw [← ps_ko e1 e2]; exact hy
  by_cases e3 : u = t
  · subst e3; rw [ps_kt] at hu; cases hu; simp [receiveBlocked] at hb
  have e4 : u ≠ w := by intro e; subst e; rw [ps_kw hwt] at hu; cases hu
  exact ⟨y, u, xu, hy', hyu, by rw [← ps_ko e3 e4]; exact hu, hb⟩

theorem ps_nsc {N C : Set U64} (hN : NSC N C σ) : NSC N C (pushSt σ t w xr xt) := fun m hm x q hx hq =>
  hN m hm x q ((ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hx) hq

theorem ps_prio (u : ObjRef) : Sched.prioOf (pushSt σ t w xr xt) u = Sched.prioOf σ u := by
  by_cases e1 : u = t
  · subst e1; rw [Sched.prioOf_eq ps_kt, Sched.prioOf_eq hkt]
  by_cases e2 : u = w
  · subst e2; unfold Sched.prioOf; rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq, ps_kw hwt, hkw]
  unfold Sched.prioOf; rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq, ps_ko e1 e2]

theorem ps_isorted (hS : IpcSorted σ) : IpcSorted (pushSt σ t w xr xt) := by
  refine ⟨fun q z hq => ?_, fun q z hq => ?_⟩
  · exact (hS.1 q z ((ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hq)).congr
      fun u _ => ps_prio hkt hkw hwt u
  · exact (hS.2 q z ((ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hq)).congr
      fun u _ => ps_prio hkt hkw hwt u

theorem ps_own {T C : Set U64} (hO : CurOwnW T C σ) : CurOwnW T C (pushSt σ t w xr xt) := by
  have F := (ps_skD (σ := σ) (t := t) (w := w) (xr := xr) (xt := xt))
  have hsc6 : ∀ y n, (pushSt σ t w xr xt).kheap (pushSt σ t w xr xt).curSc = some (.schedContext y n) →
      σ.kheap σ.curSc = some (.schedContext y n) := by
    intro y n hy
    rw [F.csc] at hy
    exact (ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hy
  rcases hO with ⟨u, hu, xu, hku, hxs, hown, hnr'⟩ | ⟨hcs, hun⟩
  · left
    obtain ⟨ts, hk'⟩ := ps_tcbF hkt hkw hwt hku
    exact ⟨u, hu, _, hk', by rw [F.csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
      fun h0 hm => hnr' (by rw [← F.cons]; exact h0) (by rw [ps_rel] at hm; exact hm)⟩
  · exact Or.inr ⟨by rw [F.csc]; exact hcs, fun y n hy => hun y n (hsc6 y n hy)⟩

theorem ps_off (hO : OffOK σ) : OffOK (pushSt σ t w xr xt) := by
  have F := (ps_skD (σ := σ) (t := t) (w := w) (xr := xr) (xt := xt))
  intro h0 y n hy ha
  rw [F.cons] at h0 ⊢; rw [F.tm]; rw [F.csc] at hy; rw [F.csc, F.isc] at ha
  exact hO h0 y n ((ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hy) ha

theorem ps_idleOK (hit : σ.idleThread ≠ t) (hO : IdleOK σ) : IdleOK (pushSt σ t w xr xt) := by
  have F := (ps_skD (σ := σ) (t := t) (w := w) (xr := xr) (xt := xt))
  obtain ⟨y, h1, h2, h3, h4⟩ := hO
  have hiw : σ.idleThread ≠ w := by intro e; rw [e, hkw] at h1; cases h1
  exact ⟨y, by rw [F.idle, ps_ko hit hiw]; exact h1, by rw [F.isc]; exact h2, h3, by rw [F.idle, ps_rel]; exact h4⟩

/-- `BlockedScActive` across the push: an SC bound to the caller is active
(`hact`). -/
theorem ps_bsa (hact : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t → scActive y = true)
    (hB : BlockedScActive σ) : BlockedScActive (pushSt σ t w xr xt) := by
  refine ⟨fun p y n u xu hp hy hu hq => ?_, fun p y n hp hr => ?_⟩
  · have hp' : σ.kheap p = some (.schedContext y n) :=
      (ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hp
    by_cases e : u = t
    · subst e; exact hact p y n hp' hy
    · have e2 : u ≠ w := by intro e'; subst e'; rw [ps_kw hwt] at hu; cases hu
      rw [ps_ko e e2] at hu; exact hB.tcb p y n u xu hp' hy hu hq
  · exact hB.replies p y n ((ps_oth hkt hkw hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hp) hr

/-- `Inv` across the push, the caller in no ready queue and not in the
release queue. -/
theorem ps_inv (hI : Inv σ) (hnq : ∀ d p, t ∉ σ.readyQueues d p) (hnr : t ∉ σ.releaseQueue) :
    Inv (pushSt σ t w xr xt) := by
  have hI0 : Inv (updK σ w (.reply { xr with replyTcb := some t })) := hI.updReply hkw
  have hkt0 : (updK σ w (.reply { xr with replyTcb := some t })).kheap t = some (.tcb xt) := by
    simp [updK, Ne.symm hwt, hkt]
  have hI1 : Inv (updK (updK σ w (.reply { xr with replyTcb := some t })) t
      (.tcb { xt with tcbState := .blockedOnReply w })) := by
    refine hI0.step (NtfnStep.tcb hkt0 (.blockedOnReply w) xt.tcbArch) (fun u x0 y h1 h2 hqd hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = t
      · subst e
        rcases hqd with ⟨d, p, hm⟩ | hm
        · exact absurd hm (hnq d p)
        · exact absurd hm hnr
      · have h2' : (updK σ w (.reply { xr with replyTcb := some t })).kheap u = some (.tcb y) := by
          simpa [updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t
      · subst e; simp [updK] at h2; subst h2
        exact absurd hc (by intro h; rcases h with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩ <;> cases h)
      · have h2' : (updK σ w (.reply { xr with replyTcb := some t })).kheap u = some (.tcb y) := by
          simpa [updK, e] using h2
        exact hI0.rd u y h2' hc
  exact hI1.qchange (qchange_stsAct _ t)

end Ps

/-- **The receiver's `Running` and the push commute** on the spec side (the
receiver `d` not the current thread, so its `stsAct` asks nothing). -/
theorem ps_swap {σ : State Unit} {t w d : ObjRef} {xr : Reply} {xt xd : Tcb} (htd : t ≠ d) (hwd : w ≠ d)
    (hdc : d ≠ σ.curThread) :
    stsAct (updK (pushSt σ t w xr xt) d (.tcb xd)) d = pushSt (stsAct (updK σ d (.tcb xd)) d) t w xr xt := by
  have h1 : stsAct (updK σ d (.tcb xd)) d = updK σ d (.tcb xd) := stsAct_ne hdc
  have h2 : stsAct (updK (pushSt σ t w xr xt) d (.tcb xd)) d = updK (pushSt σ t w xr xt) d (.tcb xd) :=
    stsAct_ne (by
      show d ≠ (pushSt σ t w xr xt).curThread
      rw [(ps_skD (σ := σ) (t := t) (w := w) (xr := xr) (xt := xt)).ct]; exact hdc)
  rw [h1, h2]
  have hs : ∀ σ0 : State Unit,
      ¬ schedulable t (updK σ0 t (.tcb { xt with tcbState := .blockedOnReply w })) = true := by
    intro σ0 h
    obtain ⟨y, _, _, _, hky, _, hr, _⟩ := schedulable_inv h
    simp [updK] at hky; subst hky; simp [runnable] at hr
  have e1 : ∀ σ0 : State Unit, σ0.curThread = σ.curThread → σ0.schedulerAction = σ.schedulerAction →
      stsAct (updK σ0 t (.tcb { xt with tcbState := .blockedOnReply w })) t =
        if t = σ.curThread ∧ σ.schedulerAction = .resumeCurThread then
          { updK σ0 t (.tcb { xt with tcbState := .blockedOnReply w }) with schedulerAction := .chooseNewThread }
        else updK σ0 t (.tcb { xt with tcbState := .blockedOnReply w }) := by
    intro σ0 h1 h2
    by_cases C : t = σ.curThread ∧ σ.schedulerAction = .resumeCurThread
    · rw [if_pos C]; unfold stsAct; split
      · rfl
      · rename_i h; exact absurd (And.intro (C.1.trans h1.symm) (And.intro (h2.trans C.2) (hs σ0))) h
    · rw [if_neg C]; unfold stsAct; split
      · rename_i h; exact absurd (And.intro (h.1.trans h1) (h2.symm.trans h.2.1)) C
      · rfl
  unfold pushSt
  rw [e1 (updK σ w (.reply { xr with replyTcb := some t })) rfl rfl,
    e1 (updK (updK σ d (.tcb xd)) w (.reply { xr with replyTcb := some t })) rfl rfl]
  by_cases C : t = σ.curThread ∧ σ.schedulerAction = .resumeCurThread
  · rw [if_pos C, if_pos C]
    simp only [updK, Function.update_comm (Ne.symm hwd), Function.update_comm (Ne.symm htd)] <;> rfl
  · rw [if_neg C, if_neg C]
    simp only [updK, Function.update_comm (Ne.symm hwd), Function.update_comm (Ne.symm htd)] <;> rfl

end Spec

/-! ## The wake with a reply bound after the frame at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`JAtZ.wake_postG` with the replies' facts given back** (a free reply
after was free before, `hfree1`; a reply bound to a receive-blocked thread
after was one before, `hrb1`) instead of the replies kept: the step may bind
a free reply, as `reply_push` does. -/
theorem JAtZ.wake_postGR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
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
    (hrb1 : ∀ d ∈ Z.R, RecvB σ' d → RecvB σa d) (hkz1 : KSz σa σ') (hkb1 : KBack σa σ') (hfk1 : IpcFrKeep σa σ')
    (hck1 : (∀ q y n, σa.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
      (∀ q x, σa.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
      (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σa.kheap p = some (.schedContext x0 n)))
    (hfree1 : ∀ d ∈ Z.R, Free σ' d → Free σa d)
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
    obtain ⟨y, hy', hyt⟩ := hfree1 d hd hfd
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
  have hRR' : RRecv (L.mem s') Z.R σ' := fun d hd hr => by
    obtain ⟨h1, h2⟩ := J.rrecv d hd (F.khrb.recvB (hrb1 d hd hr))
    exact ⟨(k4 d hd).2.trans h1, (k4 d hd).1.trans h2⟩
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
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) (G.arch.trans F.sk.arch)
    (fun q ao h => hao1 q ao (F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
        (fun _ e => by cases e) (fun _ e => by cases e))) hsz hF.1 (F.kback.trans' hkb1) (F.ipcFr.trans hfk1) hC R hKd (G.orig.trans F.sk.orig) (J.idleW_keep hS3 hidl0 hisc0).1 J.zD⟩



set_option maxHeartbeats 64000000 in
/-- **A call to a waiting receiver at `J` that pushes a reply without a
donation** (module docstring): the caller has the grant or grant-reply right
(`hg`), the receiver a reply object (`hrepn`), and the call does not donate or
the receiver has an SC (`hnd`); as `JAtZ.sendCallIJ` up to the reply unlink,
then `reply_push` on `IRel` (`reply_push_iG`, no donation), P1's
`reply_push.ipc` and `reply_push.nd`, the receiver `Running`, `JAtZ` by
`JAtZ.wake_postGR` at `pushSt` (`ps_swap`), the tail `JAtZ.sendTailJ`; the
spec's outcome `sendIpc_call_eq`. -/
theorem JAtZ.sendCallPJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrs : xt.tcbState = .restart) (hft : xt.tcbFault = none) (hct : σ.curThread = t.bv)
    (hres : σ.schedulerAction = .resumeCurThread) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hg : g = true ∨ gr = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hnd : don = false ∨ ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none) :
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
  obtain ⟨r, hrp⟩ := Option.ne_none_iff_exists'.1 (hrepn xd hkd _ _ _ hstd)
  subst hrp
  obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
  have hwR := hrepR (by simp)
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
  set w := L.mem s (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
    simp [σ2, σ1y, hwe, hwd, hncn hkr (fun _ _ h0 => by cases h0)]
  have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd]) hkr
  have hX2' := IpcRel.ofSRN hR2 hS2'
  have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
  obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
  rw [hrA] at hiR hit
  refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
      hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
    (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
        (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
      (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
  rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩

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
  have hrepn : ∀ xd, σy.kheap d'.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none :=
    fun xd h => hrepn xd (by rw [hkdy] at h; rw [hkd0]; exact h)
  have hnd : don = false ∨ ∀ xd, σy.kheap d'.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none :=
    hnd.imp_right fun h xd h' => h xd (by rw [hkdy] at h'; rw [hkd0]; exact h')
  have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
    intro r hr er
    obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
    rw [er, hrA] at b2; rw [← b2]; exact z3
  set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
  set xr3 : Fl4Spec.Reply := { xr with replyTcb := none } with hxr3
  set σ3a := Notif.updK σ2 w.bv (.reply xr3) with hσ3a
  have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
  have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
  have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
    stsAct_ne hct3a
  set σ3 := Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv with hσ3
  have hU : Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) (some w.bv) σ2 =
      ({((), σ3)}, False) := e3
  have hW3' : P1.WritesIn st yb s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply xr3) := by rw [stsAct_kheap]; simp [σ3a, hwd]
  have hq3 : ∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
    exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
  have Fr3 : CFr e.bv d'.bv σy σ3 := (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
    (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σy σ3 := by
    have IK3a : IK d'.bv σy σ3a := IK2.trans (IK.updOther (o' := .reply xr3) hkr2 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    have IK3b : IK d'.bv σy (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
    exact IK3b.trans (IK.sts _ _ _)
  have SK3 : SKeep σy σ3 :=
    ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
      (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans
      (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σy.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σy.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d' :=
    hX3.noref hdta (by rw [e3']; exact P1.inactive_ne.1) (by rw [e3']; exact P1.inactive_ne.2)
  have F3 := footW_trans F2 (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hks3 : L.ksb s3 = L.ksb yb := hW3'.1
  -- the caller's and the receiver's words at `s3`
  have hCI : CurInv σy := J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hnrT : t.bv ∉ σy.releaseQueue := by rw [← hct]; exact hCI.notRel
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = 2 := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st, hrs]; rfl
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (Or.inr (Or.inl hw3))
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
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
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun h0 =>
    hB3.sact t htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw3⟩))))) h0
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the receiver's SC: no donation
  have hndF : don = true → x3.tcbSchedContext = none → False := fun hdon hx0 => by
    rcases hnd with h | h
    · rw [h] at hdon; cases hdon
    · exact h xd hkd (by rw [← hsc3]; exact hx0)
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM d' hdT
  rw [hkd3] at hkd3'; cases hkd3'
  have hnd1 : don = false ∨ L.mem s3 (P1.scA d') ≠ 0#u64 := by
    cases don
    · exact Or.inl rfl
    · right; intro h0; exact hndF rfl (by rw [hdsc, h0, optRef_zero])
  -- the push on `IRel`, at P1
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hns3 : tsCode xt.tcbState ≠ 6 := by rw [hrs]; decide
  have hPush : ipc.reply_push st arI s3 a t d' w don ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv don σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1 ⦄ := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := don) (P := fun s' σ' => σ' = pushSt σ3 t.bv w.bv xr3 xt ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hdon _ _ _ _ _ _ _ hx0 => (hndF hdon hx0).elim))
      (P1.ipc.reply_push.ipc hAT s3 a t d' w don Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hqbD hrbD (hna3 d' hdT) (hiw3 d' hdT hid) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a t d' w don h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hcA hnd1)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, hb2, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hb2, hf, hsb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv don σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1) ?_ ?_
  · rcases hg with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]; exact hPush
    · cases g <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true] <;> exact hPush
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, ⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4', hSg4⟩, hst4, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 h4 hB4 hX4 hS4' hSg4 hst4 fu4 hsb4 ⊢
  subst ha4
  try dsimp only
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 ht hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hW4' : P1.WritesIn st yb s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
    hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3 (SzKeepC.of Fr3.szKeep) hb))
  have hks4 : L.ksb s4 = L.ksb yb := hW4'.1
  set σ4 := pushSt σ3 t.bv w.bv xr3 xt with hσ4
  have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z ((ps_oth hkt3 hkr3 hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hz)
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hst4d : L.mem s4 (P1.stA d') = sched.TS_INACTIVE := by rw [hst4 d' hdH (Ne.symm htd)]; exact e3'
  have hx4 : d' ∈ (∅ : Set U64) ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := Or.inr (by rw [hst4d]; exact P1.not_blocked_inactive)
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' :=
    hX4.noref hdta (by rw [hst4d]; exact P1.inactive_ne.1) (by rw [hst4d]; exact P1.inactive_ne.2)
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4
      (by simp [x3, tsCode]) .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q4 R4 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK σ4 d'.bv (.tcb x5)) d'.bv = pushSt σa t.bv w.bv xr3 xt :=
    ps_swap htd' hwd hdc3
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 (pushSt σa t.bv w.bv xr3 xt) := by
    rw [← heq5]; exact hIR0
  have hW5' : P1.WritesIn st yb s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q4, R4, h5.congrX P1.empty_congr⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have hrb3 : RbIn x3.tcbState := Or.inr rfl
  have Fr5 : CFr e.bv d'.bv σy σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σy (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σy σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : SKeep σy σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σa.schedulerAction = σy.schedulerAction := by
    rw [hσa, stsAct_ne (by show d'.bv ≠ σ3.curThread; exact hdc3)]; exact hact3
  -- the push after the wake (`ps_swap`)
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hkwa : σa.kheap w.bv = some (.reply xr3) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, hwd, hkr3]
  have hnqT : ∀ dm p, t.bv ∉ σa.readyQueues dm p := by rw [IK5.2.1]; exact hnq
  have hnrT' : t.bv ∉ σa.releaseQueue := by rw [IK5.2.2.1]; exact hnrT
  set σ' := pushSt σa t.bv w.bv xr3 xt with hσ'
  have I5' : Inv σ' := ps_inv hkta hkwa hwt I5 hnqT hnrT'
  -- an SC bound to the caller is the current SC, active
  have hscA : ∀ p y n, σa.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    have hp0 : σy.kheap p = some (.schedContext y n) := SK5.2.2.2 _ _ _ hp
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp0
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp0).2⟩
    have hS := J.xtop.fin.1.1.1
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
    rw [hkt] at hku; cases hku
    obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
    rw [hct, hkt] at hkc; cases hkc
    have e1 : σy.curSc = q.bv := Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp0
    exact hCI.active (J.curSc_ne_idle hCI hti) y n hp0
  have B5' : BlockedScActive σ' := ps_bsa hkta hkwa hwt hscA (Fr5.bsa J.bsa)
  have hcn : σ'.schedulerAction = .chooseNewThread :=
    ps_act (by rw [Fr5.sk.ct, hct]) (by rw [act5, hres])
  have hidT : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle, ← hct]; exact fun e0 => hti e0.symm
  have hAI5 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hcn] at hu; cases hu), ps_idleOK hkta hkwa hwt hidT (Fr5.idleOK J.act.2)⟩
  have hrun5 : CurRunM σ' := Or.inl (by rw [hcn]; intro h; cases h)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rw [hrs]; simp [tsCode])
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J0.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := hR.reply w hwR
    rw [hkr] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hkq : ∀ q ∈ D, σ'.kheap q.bv = σa.kheap q.bv := fun q hq => ps_ko (hcD q hq) (hwD q hq)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs) J hdT hdth hkd hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σy umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D su _ (Endp.setUm σy umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkd (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σa.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hwt h1 h2
  obtain ⟨V', J5⟩ := Ju.wake_postGR (by rw [← hKy.2.1] at hIR; exact hIR) hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) ps_skD
    (ps_ksub hkta hkwa hwt) (ps_szKeep hkta hkwa hwt) (ps_ykeep hkta hkwa hwt) (ps_mcpKeep hkta hkwa hwt)
    (ps_bufKeep hkta hkwa hwt) (fun d _ h => ps_recvB hkta hkwa hwt h) (ps_ksz hkta hkwa hwt)
    (ps_kback hkta hkwa hwt) (ps_ipcFr hkta hkwa hwt) (ps_ck hkta hkwa hwt) (fun d _ h => ps_free hkta hkwa hwt h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I5' B5' hAI5 (Or.inl hcn) hrun5 (ps_own hkta hkwa hwt ((DWFr.ofCFr Fr5).own ⟨d', hdT, rfl⟩ J.own))
    (ps_off hkta hkwa hwt ((DWFr.ofCFr Fr5).off J.off)) (ps_nsc hkta hkwa hwt ((DWFr.ofCFr Fr5).nsc J.nsc))
    (ps_isorted hkta hkwa hwt ((DWFr.ofCFr Fr5).isorted J.isorted)) hRR htD
  -- the tail
  have hk5 : σ'.kheap d'.bv = some (.tcb x5) := by
    rw [ps_ko (Ne.symm htd') (Ne.symm hwd), hσa, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ'.releaseQueue := by rw [ps_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ'.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya : σa.kheap p = some (.schedContext y n) :=
      (ho (fun _ h => by cases h) (fun _ h => by cases h)).1 hy
    have hy0 := SK5.2.2.2 p y n hya
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J.inv.back _ _ _ hkd hp'
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y n d'.bv xd hy0 hyt hkd (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ'.idleThread := by
    rw [(ps_skD (σ := σa) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).idle, Fr5.sk.idle]
    exact hid
  have htc5 : d'.bv ≠ σ'.curThread := by
    rw [(ps_skD (σ := σa) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).ct, Fr5.sk.ct]; exact hdc
  have hspec := sendIpc_call_eq (don := don) hk0 hkd0 hde hstd blk badge.bv g gr hg e2 hU hkt3 hkd3 hpush hkd4
    (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr don t.bv e.bv σ =
      Endp.specWakeTailE d'.bv σ' := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩



/-- **The calls to a waiting receiver `JAtZ.sendCallPJ` covers**: a call
from a sender without a fault, any grant, the head receiver
with a reply object, the grant or grant-reply right, and no
donation (`can_donate` false, or the receiver has an SC). -/
def SendRecvCP (σ : Fl4Spec.State Unit) (call g gr don : Bool) (t e : Fl4Spec.ObjRef) : Prop :=
  call = true ∧ ∃ xt d q, σ.kheap t = some (.tcb xt) ∧ xt.tcbFault = none ∧
    σ.kheap e = some (.endpoint (.recvEP (d :: q))) ∧
    (g = true ∨ gr = true) ∧
    (∀ xd, σ.kheap d = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) ∧
    (don = false ∨ ∀ xd, σ.kheap d = some (.tcb xd) → xd.tcbSchedContext ≠ none)

end

end

end Fl4Proofs.P3
