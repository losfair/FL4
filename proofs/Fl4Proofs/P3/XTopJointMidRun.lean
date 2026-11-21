/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch7 (C) step 1, M6): **the
state between ReplyRecv / NBSendRecv / NBSendWait's invocation and their
receive.**

l4v (`Syscall_AI`, `he_invs`) gets the receive's precondition `invs and
ct_active` from `handle_invocation_not_blocking_not_calling_first_phase_ct_active`:
a first-phase (`decode_invocation True`), non-blocking, non-calling invocation
leaves the current thread active, because the first phase rejects the
Thread/Domain/SchedContext/SchedControl/CNode caps (Fl4Spec's
`fl4DecodeInvocation true` and FL4's `decode_invocation(first_phase)` have the
same rejection) and a safe non-blocking non-calling `perform_invocation` keeps
`ct_active` (`perform_invocation_not_blocking_not_calling_ct_active`).

* `JMidRunHyp` [W]: that l4v lemma, at the invocation's entry state, on the
  spec's `fl4HandleInvocationR`: every successful outcome has the current
  thread runnable (`CurRun`, l4v `ct_active`). Not derivable from the J layer
  as it stands: `HIPostMXP`'s `JAt` carries `CurRunM` only (`CurRunW` while
  resumed; the mid action may be `switchThread t` or `chooseNewThread`), and the
  decode paths' `DecOut` facts are internal to `decOK_J`. Removal route: a spec
  frame "the current thread stays runnable" (VsDom's FK pattern) over the
  first-phase perform cone (sendIpc non-blocking, sendSignal, reply, IRQ,
  untyped retype, arch), with the receiver/woken thread ≠ the current thread
  from `CurRun` (blocked threads are not runnable) and decode/lookup outcomes
  read-only.
* `curRun_ne_idle`: `CurRun` and `IdleOK` (JAtZ's `act.2`) make the current
  thread not the idle one (l4v: `ct_active` excludes `IdleThreadState`).
* `JMid`: what the receive at the mid state may assume (l4v `invs and
  ct_active`): `RelTopM`, `JAt`, `CurRun`, not idle. No condition on the
  scheduler action (l4v requires none; sch2's finding).
* `HIPostMXP.mid` / `handle_invocation_midJ`: `handle_invocation_refinesJ`'s
  post for `first_phase = true`, `blocking = is_call = false` with
  `JMidRunHyp` and `MidEntry` at the entry: at `Ok` the mid state is `JMid`.
-/
import Fl4Proofs.P3.XTopJointEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What the mid-state route reads at the invocation's entry** (all true at a
system call's entry, l4v `invs and ct_active`; KENTRY-PLAN sch11):
* `run`: the current thread runnable (`CurRun`, l4v `ct_active`; at J from
  `Entered` and `JAtZ.cur`'s `CurInv`);
* `nf`: the current thread has no pending fault (l4v
  `fault_tcbs_valid_states`: a thread with a fault is blocked or inactive);
* `nq`: the current thread is in no notification's waiting queue (l4v
  `valid_ntfn`: the queue's threads are `BlockedOnNotification`). -/
structure MidEntry (σ : Fl4Spec.State Unit) : Prop where
  run : CurRun σ
  nf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none
  nq : ∀ p n q, σ.kheap p = some (.notification n) → n.ntfnObj = .waitingNtfn q → σ.curThread ∉ q

/-- **[W] The current thread active after a first-phase non-blocking
non-calling invocation** (l4v
`handle_invocation_not_blocking_not_calling_first_phase_ct_active`; module
docstring): from an entry state `σ` with `MidEntry` (sch11: the unconditional
form of sch7 was false, e.g. for a non-runnable current thread whose lookup
faults), every successful outcome of the spec's invocation has the current
thread runnable. -/
def JMidRunHyp (rep don : Bool) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  MidEntry σ → ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) rep false false don true cptr).run σ).1,
    y.1 = .ok () → CurRun y.2

/-- `CurRun` with `IdleOK`: the current thread is not the idle thread. -/
theorem curRun_ne_idle {σ : Fl4Spec.State Unit} (hC : CurRun σ) (hI : IdleOK σ) :
    σ.curThread ≠ σ.idleThread := by
  intro e
  obtain ⟨x, hk, -, hs, -⟩ := hI
  have h := hC x (by rw [e]; exact hk)
  rw [hs] at h
  simp [Fl4Spec.runnable] at h

/-- **The mid state of ReplyRecv / NBSendRecv / NBSendWait** (l4v `invs and
ct_active`; module docstring). -/
def JMid (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RelTopM (L := L) s σ ∧ JAt (L := L) arI AR s a σ ∧ CurRun σ ∧ σ.curThread ≠ σ.idleThread

/-- The post of the first-phase invocation with the mid state. -/
def HIPostMid (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) (don : Bool) (cptr : Fl4Spec.CapRef)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false don true cptr).run σ).1,
    (res.1 = .Ok () ∧ y.1 = .ok () ∧ JMid (L := L) arI AR res.2.1 res.2.2 y.2) ∨
    (res.1 = .Err .Preempted ∧ y.1 = .error () ∧ RelTopM (L := L) res.2.1 y.2 ∧
      JAtPre (L := L) arI AR res.2.1 res.2.2 y.2)

/-- **`HIPostMXP` at `JAt`/`JAtPre` with `JMidRunHyp` is `HIPostMid`.** -/
theorem HIPostMXP.mid {AR : A → Fl4Spec.Cr3 → Prop} {σ : Fl4Spec.State Unit} {don : Bool}
    {cptr : Fl4Spec.CapRef} {res : core.result.Result Unit error.Exc × S × A}
    (h : HIPostMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) true σ false false don true cptr res)
    (hM : JMidRunHyp true don cptr σ) (hE : MidEntry σ) : HIPostMid (L := L) arI AR σ don cptr res := by
  obtain ⟨y, hy, hc, hR, hX⟩ := h
  refine ⟨y, hy, ?_⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hJ : JAt (L := L) arI AR res.2.1 res.2.2 y.2 :=
      ifP_X (X := JAt (L := L) arI AR) (XP := JAtPre (L := L) arI AR) (by rw [h1]; intro e; cases e) hX
    have hC := hM hE y hy h2
    obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
    exact Or.inl ⟨h1, h2, hR, ⟨Z, H, Cs, Ac, Lst, D, J⟩, hC, curRun_ne_idle hC J.act.2⟩
  · rw [h1, if_pos rfl] at hX
    exact Or.inr ⟨h1, h2, hR, hX⟩

/-- **`handle_invocation_refinesJ` for ReplyRecv / NBSendRecv / NBSendWait's
invocation** (`first_phase`, neither blocking nor calling) with the mid state
`JMid` at `Ok`, from `JMidRunHyp` [W]. -/
theorem handle_invocation_midJ [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (can_donate : Bool) (cptr : U64)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (argsU : List U64)
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False))
    (hH : JEntryHyps (L := L) arI AR Z H Cs D s ar σ ct false false can_donate true cptr info mi buf buffer
      argsU r2 er)
    (hM : JMidRunHyp true can_donate (Fl4Spec.toBl cptr.bv) σ) (hE : MidEntry σ) :
    syscall.handle_invocation st arI s ar false false can_donate true cptr ⦃ res =>
      HIPostMid (L := L) arI AR σ can_donate (Fl4Spec.toBl cptr.bv) res ⦄ :=
  WP.spec_mono (handle_invocation_refinesJ arI s ar σ J ct hct false false can_donate true cptr info hinfo mi hmi
    buf hbuf buffer hbuffer r2 hr2 er her argsU hmrs hH) fun _ h => h.mid arI hM hE

end

end

end Fl4Proofs.P3
