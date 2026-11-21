/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch11 (1)): **the first-phase
non-blocking non-calling invocations keep the current thread `Restart`**
(spec side only), for `JMidRunHyp` (XTopJointMidRun).

`CtRs ct σ`: `ct` is the current thread, and its TCB (if any) is runnable
(`Running`/`Restart`) with no fault. `PR ct m`: every outcome of `m` from a `CtRs` state is
`CtRs`. `KF` frames (XTopJointMidRunK) give `PR` (`pr_of_kf`); the threads
whose state an invocation sets are shown `≠ ct` from what the spec reads
(`pr_threadGet_bind`, `pr_gts_bind`): the receiver of `send_ipc` is
`BlockedOnReceive` (its state is read and matched), the receiver of a reply
`BlockedOnReply`, the bound TCB of a signalled notification
`receive_blocked`, while `ct` is `Restart`; a calling-or-faulted send needs
the sender `≠ ct` or ct's fault field `none` (read).
* `pr_sendIpc`: `send_ipc` from `thread ≠ ct`, or non-blocking non-calling
  from any thread.
* `pr_sendFaultIpc` / `pr_handleTimeout`: from a thread `≠ ct`.
* `pr_doReplyTransfer`.
* `pr_sendSignal`: needs `NQ ct σ` (ct in no notification's waiting queue,
  l4v `valid_ntfn`) at its start (the waiting queue's head is set
  `Running` without a state read).
-/
import Fl4Proofs.P3.XTopJointMidRunK
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- `ct` is the current thread and its TCB (if any) is runnable with no fault. -/
def CtRs (ct : ObjRef) (σ : State Unit) : Prop :=
  σ.curThread = ct ∧ ∀ x, σ.kheap ct = some (.tcb x) → runnable x.tcbState = true ∧ x.tcbFault = none

/-- `ct` is in no notification's waiting queue. -/
def NQ (ct : ObjRef) (σ : State Unit) : Prop :=
  ∀ p n q, σ.kheap p = some (.notification n) → n.ntfnObj = .waitingNtfn q → ct ∉ q

theorem CtRs.of_ctV {ct : ObjRef} {σ σ' : State Unit} (e : ctV ct σ' = ctV ct σ) (h : CtRs ct σ) :
    CtRs ct σ' := by
  unfold ctV at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  refine ⟨e1.trans h.1, fun x hx => ?_⟩
  rw [hx] at e2
  rcases hk : σ.kheap ct with _ | k
  · rw [hk] at e2; simp [tsV] at e2
  · rw [hk] at e2
    cases k with
    | tcb y =>
      simp only [tsV, Option.some.injEq, Prod.mk.injEq] at e2
      obtain ⟨a, b⟩ := h.2 y hk
      exact ⟨by rw [e2.1]; exact a, e2.2.trans b⟩
    | _ => simp [tsV] at e2

/-- Every outcome of `m` from a `CtRs` state is `CtRs`. -/
def PR (ct : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, CtRs ct σ → x ∈ (m σ).1 → CtRs ct x.2

section
variable {ct : ObjRef}

theorem pr_of_kf {α : Type} {m : NonDet (State Unit) α} (h : KF ct m) : PR ct m :=
  fun σ x hs hx => CtRs.of_ctV (h σ x hx) hs

theorem pr_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β}
    (hm : PR ct m) (hf : ∀ a, PR ct (f a)) : PR ct (m >>= f) :=
  fun σ x hs ⟨y, hy, hx⟩ => hf y.1 y.2 x (hm σ y hs hy) hx

theorem pr_fail_bind {α β : Type} {f : α → NonDet (State Unit) β} : PR ct (NonDet.fail >>= f) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

theorem pr_threadGet_bind {α β : Type} (f : Tcb → α) (t : ObjRef) {k : α → NonDet (State Unit) β}
    (hk : ∀ tcb, (t = ct → runnable tcb.tcbState = true ∧ tcb.tcbFault = none) → PR ct (k (f tcb))) :
    PR ct (threadGet (Z := Unit) f t >>= k) := by
  intro σ x hs ⟨⟨a, s1⟩, ⟨⟨tcb, s0⟩, h0, h1⟩, hx⟩
  obtain ⟨e0, e0'⟩ := mem_getsThe' h0
  simp only at e0 e0'
  subst e0'
  have h1 := mem_pure' h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hk tcb (fun e => by subst e; exact hs.2 tcb (getTcb_some e0)) _ x hs hx

theorem pr_gts_bind {β : Type} (t : ObjRef) {k : ThreadState → NonDet (State Unit) β}
    (hk : ∀ ts, (t = ct → runnable ts = true) → PR ct (k ts)) :
    PR ct (getThreadState (Z := Unit) t >>= k) := by
  unfold getThreadState
  exact pr_threadGet_bind _ t fun tcb h => hk _ fun e => (h e).1

/-- The receive branch of `send_ipc` (a receiver `dest` at the head of the
queue). -/
theorem pr_sendIpc_recv (call : Bool) (badge : Badge) (g gr d : Bool) (thread ep dest : ObjRef)
    (hth : thread ≠ ct ∨ call = false) :
    PR ct (do
      tcbEpDequeue (Z := Unit) dest ep
      let recvState ← getThreadState dest
      let reply ← match recvState with
        | .blockedOnReceive _ reply _data => pure reply
        | _ => NonDet.fail
      doIpcTransfer thread (some ep) badge g dest
      NonDet.maybeM (replyUnlinkTcb dest) reply
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext dest
      let fault ← threadGet Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (g ∨ gr) ∧ reply ≠ none then
          replyPush thread dest (the reply) d
        else
          setThreadState thread .inactive
      else NonDet.when (d ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef Tcb.tcbSchedContext thread
        schedContextDonate (the threadSc) dest
      setThreadState dest .running
      let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
  refine pr_gts_bind dest fun ts hts => ?_
  cases ts
  case blockedOnReceive e r dt =>
    have hd : dest ≠ ct := fun e => by have := hts e; simp [runnable] at this
    refine pr_bind (pr_of_kf (dk_pure _)) fun reply => ?_
    refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
    refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
    refine pr_bind (pr_of_kf (by kf_auto)) fun scOpt => ?_
    refine pr_threadGet_bind _ thread fun tf htf => ?_
    simp only [letFun]
    split
    · next hc =>
      have ht : thread ≠ ct := by
        rcases hth with h | hcall
        · exact h
        · intro e
          have h2 := (htf e).2
          subst hcall
          simp only [h2] at hc
          simp at hc
      exact pr_of_kf (by kf_auto)
    · exact pr_of_kf (by kf_auto)
  all_goals exact pr_fail_bind

/-- **`send_ipc` keeps `CtRs`** from a sender `≠ ct`, or non-blocking and
non-calling from any sender. -/
theorem pr_sendIpc (block call : Bool) (badge : Badge) (g gr d : Bool) (thread ep : ObjRef)
    (hth : thread ≠ ct ∨ (block = false ∧ call = false)) :
    PR ct (sendIpc (Z := Unit) block call badge g gr d thread ep) := by
  unfold sendIpc
  refine pr_bind (pr_of_kf (by kf_auto)) fun e => ?_
  have hr : thread ≠ ct ∨ call = false := hth.imp_right (·.2)
  cases e with
  | idleEP =>
    cases block
    · exact pr_of_kf (dk_pure _)
    · exact pr_of_kf (kf_sendIpcBlocked' _ _ _ _ _ _ (hth.resolve_right (by simp)))
  | sendEP q =>
    cases block
    · exact pr_of_kf (dk_pure _)
    · exact pr_of_kf (kf_sendIpcBlocked' _ _ _ _ _ _ (hth.resolve_right (by simp)))
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact fun _ _ _ hx => hx.elim
    | cons dest q => cases block <;> exact pr_sendIpc_recv call badge g gr d thread ep dest hr

theorem pr_sendFaultIpc (tptr : ObjRef) (hc : Cap) (f : Fault) (d : Bool) (ht : tptr ≠ ct) :
    PR ct (sendFaultIpc (Z := Unit) tptr hc f d) := by
  unfold sendFaultIpc
  split
  · refine pr_bind (pr_of_kf (kf_threadSet_ne _ _ ht)) fun _ => ?_
    exact pr_bind (pr_sendIpc _ _ _ _ _ _ _ _ (Or.inl ht)) fun _ => pr_of_kf (dk_pure _)
  · exact pr_of_kf (dk_pure _)
  · exact fun _ _ _ hx => hx.elim

theorem pr_handleTimeout (tptr : ObjRef) (ex : Fault) (ht : tptr ≠ ct) :
    PR ct (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
  refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
  refine pr_bind (pr_of_kf (dk_pure _)) fun _ => ?_
  refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
  exact pr_bind (pr_sendFaultIpc _ _ _ _ ht) fun _ => pr_of_kf (dk_pure _)

/-- The tail of `do_reply_transfer` (the receiver `≠ ct` woken or charged). -/
theorem pr_drt_tail (receiver : ObjRef) (hd : receiver ≠ ct) (fault : Option Fault) :
    PR ct (do
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext receiver
      let state ← getThreadState receiver
      NonDet.when (scOpt ≠ none ∧ runnable state) <| do
        let scPtr ← NonDet.assertOpt scOpt
        let sc ← getSchedContext scPtr
        let curtime ← NonDet.gets fun s : State Unit => s.curTime
        if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
        then possibleSwitchTo receiver
        else do
          let tcb ← NonDet.getsThe (getTcb receiver)
          if isEpCap tcb.tcbTimeoutHandler ∧
             ¬(fault.elim false isTimeoutFault = true)
          then handleTimeout receiver (.timeout sc.scBadge)
          else postpone scPtr) := by
  refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
  refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
  unfold NonDet.when
  split
  · refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
    refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
    refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
    split
    · exact pr_of_kf (by kf_auto)
    · refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
      split
      · exact pr_handleTimeout _ _ hd
      · exact pr_of_kf (by kf_auto)
  · exact pr_of_kf (dk_pure' _)

/-- **`do_reply_transfer` keeps `CtRs`**: the receiver is `BlockedOnReply`. -/
theorem pr_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    PR ct (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine pr_bind (pr_of_kf (by kf_auto)) fun recvOpt => ?_
  cases recvOpt with
  | none => exact pr_of_kf (dk_pure' _)
  | some receiver =>
    refine pr_gts_bind receiver fun ts hts => ?_
    cases ts
    case blockedOnReply r =>
      have hd : receiver ≠ ct := fun e => by have := hts e; simp [runnable] at this
      refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
      refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
      refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
      refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
      refine pr_bind (pr_of_kf (by kf_auto)) fun fault => ?_
      simp only [letFun]
      split
      all_goals repeat (first
        | exact pr_drt_tail receiver hd _
        | refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_)
    all_goals exact pr_of_kf (dk_pure _)

theorem pr_pure_bind {α β : Type} {a : α} {f : α → NonDet (State Unit) β} (h : PR ct (f a)) :
    PR ct (pure a >>= f) :=
  fun σ x hs ⟨y, hy, hx⟩ => by
    have hy := mem_pure' hy; subst hy; exact h σ x hs hx

theorem partialInv_eq' {α β : Type} [Nonempty α] {g : α → β} {b : β} {a : α} (h : partialInv g b = some a) :
    g a = b := by
  unfold partialInv at h
  split_ifs at h with hu
  cases h
  unfold The; rw [dite_eq_left hu]; exact (Classical.choose_spec hu).1

theorem getSimpleKo_mem {α : Type} [Nonempty α] {C : α → KernelObject} {p : ObjRef} {σ : State Unit}
    {x : α × State Unit} (h : x ∈ (getSimpleKo (Z := Unit) C p σ).1) : x.2 = σ ∧ σ.kheap p = some (C x.1) := by
  obtain ⟨⟨k, s1⟩, h1, ⟨u, s2⟩, h2, hx⟩ := h
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only [readObject] at e1 e1'
  subst e1'
  obtain ⟨-, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, rfl⟩ := e2
  revert hx
  rcases hp : partialInv C k with _ | a
  · intro hx; exact hx.elim
  · intro hx
    have hx := mem_pure' hx
    subst hx
    exact ⟨rfl, by rw [e1, partialInv_eq' hp]⟩

theorem the_head_mem {q : List ObjRef} (h : q ≠ []) : the q.head? ∈ q := by
  cases q with
  | nil => exact absurd rfl h
  | cons a q => exact List.mem_cons_self ..

/-- **`send_signal` keeps `CtRs`**, from a state where `ct` waits on no
notification (`NQ`): the woken thread is the bound TCB (state read:
`receive_blocked`) or the waiting queue's head (`≠ ct` by `NQ`). -/
theorem pr_sendSignal (n : ObjRef) (b : Badge) :
    ∀ σ x, CtRs ct σ → NQ ct σ → x ∈ (sendSignal (Z := Unit) n b σ).1 → CtRs ct x.2 := by
  intro σ x hs hq hx
  unfold sendSignal at hx
  obtain ⟨⟨nt, s1⟩, h1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := getSimpleKo_mem h1
  simp only at e1 hk
  subst e1
  rcases hno : nt.ntfnObj with _ | q | b' <;> rcases hbt : nt.ntfnBoundTcb with _ | tcb <;>
    simp only [hno, hbt] at hx
  · exact (pr_of_kf (kf_setSimpleKo _ _ _)) _ x hs hx
  · refine (pr_gts_bind tcb fun ts hts => ?_) _ x hs hx
    split
    · next hrb =>
      have hd : tcb ≠ ct := fun e => by
        have := hts e; cases ts <;> simp_all [runnable, receiveBlocked]
      exact pr_of_kf (by kf_auto)
    · exact pr_of_kf (by kf_auto)
  all_goals try exact (pr_of_kf (kf_setSimpleKo _ _ _)) _ x hs hx
  all_goals
    have hq' : ct ∉ q := hq n nt q hk hno
    unfold updateWaitingNtfn at hx
    refine (?_ : PR ct _) _ x hs hx
    by_cases hqe : q = []
    · subst hqe; exact fun _ _ _ ⟨y, hy, _⟩ => absurd rfl hy.1
    · have hd : the q.head? ≠ ct := fun e => hq' (e ▸ the_head_mem hqe)
      refine pr_bind (pr_of_kf (by kf_auto)) fun _ => ?_
      refine pr_pure_bind ?_
      exact pr_of_kf (by kf_auto)

end

end

end Fl4Proofs.P3.MidRun
