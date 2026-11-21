/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` with a reply cap whose reply object
is linked to another thread** (`take_reply`'s `cancel_ipc`, l4v
`receive_ipc`'s `reply_tcb` branch) at `J`.

* Spec side: cancelling a thread `i` that is not the current one keeps the
  current thread, the idle thread, the scheduler action (`caF`, VsDom's
  generic `FK`: `setThreadState i` only reschedules when `i` is current),
  the ready queues (ScRestartSpec's `IK`) and every other TCB
  (TcbReadRegsSpec's `XK`): `cancelOther_keep`. `reply_remove_tcb` leaves
  its thread inactive (`PostI`, `postI_replyRemoveTcb`). After the cancel
  the reply object is free (`cancelOther_reply`: by `SchedValid` before and
  after, the only thread naming it was `i`, now inactive), so the spec's
  `receiveIpc` at the state after is the original one
  (`receiveIpc_linked`).
* FL4 side: `receive_ipc_linked`: `receive_ipc` = `cancel_ipc i` followed by
  `receive_ipc` at the state after (where `take_reply` is a no-op).
* `JAtZ.cancelLinkJ`: the J step (`JAtZ.cancelReplyJ` / `JAtZ.cancelRecvJ`)
  with the post facts the later receive needs (the slots kept:
  `JAtZ.cancel_slots`, so the caps stay held, `jHeld_of_same`).
* The waiting-sender cases, all proved: `RecvSendBasicCase` (XTopJointRecvSendF's
  `JAtZ.recvSendJ0X`, XTopJointRecvSendRet's `JAtZ.recvSendRetJ`), `RecvSendPushCase`
  (XTopJointRecvSendP's `JAtZ.recvSendP0X`), `RecvSendRetPushCase` (XTopJointRecvSendRP's
  `JAtZ.recvSendRetPJ`, XTopJointRecvSendRD's `JAtZ.recvSendRetPDJ`) and the head sender with
  a timeout fault and an SC (XTopJointRecvSendT's `JAtZ.recvSendT0X` / `JAtZ.recvSendRetTJ`;
  exhaustive by `sendOK_split`, the head by `JAtZ.head_sendT`, the former `JRecvSendHyp` [W]
  deleted). `jRecvIpcU_of`: XTopJointRecvIpc's case split for a null or free reply;
  `jRecvIpcLink_of`: the linked case (cancel, then `jRecvIpcU_of` at the state after:
  current thread, idle thread, action and ready queues kept by `cancelOther_keep`, the reply
  free by `cancelOther_reply`); `jRecvIpcHypL_of`: XTopJointDispatch's `JRecvIpcHyp`;
  `dispatch_recvJL`: the receiving syscalls (supersedes the former `dispatch_recvJR` /
  `JRecvIpcRestHyp`), taking JEntryGlob's `maxTU` / `tu` for the timeout-fault transfer.
-/
import Fl4Proofs.P3.XTopJointRecvIpc
import Fl4Proofs.P3.XTopJointRecvSendRet
import Fl4Proofs.P3.XTopJointRecvSendP
import Fl4Proofs.P3.XTopJointRecvSendRP
import Fl4Proofs.P3.XTopJointRecvSendRD
import Fl4Proofs.P3.XTopJointRecvSendT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

/-- The current thread, the idle thread and (when `t` is not current) the
scheduler action. -/
def caF (t : ObjRef) (σ : State Unit) : ObjRef × ObjRef × Option SchedulerAction :=
  (σ.curThread, σ.idleThread, if σ.curThread = t then none else some σ.schedulerAction)

/-- An `FK (caF t)` lemma of a spec function. -/
syntax "caf_leaf" : tactic
macro_rules | `(tactic| caf_leaf) => `(tactic| fail "no caf_leaf")

macro "caf_auto" : tactic => `(tactic| repeat' (first | caf_leaf | dk_step0))

variable (t : ObjRef)

theorem caf_setObject (p : ObjRef) (o : KernelObject) : FK (caF t) (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_setObject _ _ _)

theorem caf_threadSet (f : Tcb → Tcb) (u : ObjRef) : FK (caF t) (threadSet (Z := Unit) f u) := by
  unfold threadSet; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_threadSet _ _ _)

theorem caf_threadGet {α : Type} (f : Tcb → α) (u : ObjRef) : FK (caF t) (threadGet (Z := Unit) f u) := by
  unfold threadGet; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_threadGet _ _ _)

theorem caf_getThreadState (u : ObjRef) : FK (caF t) (getThreadState (Z := Unit) u) := by
  unfold getThreadState; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_getThreadState _ _)

/-- **`set_thread_state t` keeps `caF t`**: it reschedules only when `t` is
current. -/
theorem caf_setThreadStateAct : FK (caF t) (setThreadStateAct (Z := Unit) t) := by
  intro σ x hx
  unfold setThreadStateAct at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  dsimp only at hx
  by_cases hc : t = σ.curThread ∧ σ.schedulerAction = .resumeCurThread ∧ ¬ schedulable t σ
  · unfold NonDet.when at hx
    rw [if_pos hc] at hx
    unfold setSchedulerAction at hx
    rw [Set.mem_singleton_iff.1 hx]
    simp only [caF, hc.1, if_true]
  · unfold NonDet.when at hx
    rw [if_neg hc] at hx
    rw [Set.mem_singleton_iff.1 hx]

theorem caf_setThreadState (ts : ThreadState) : FK (caF t) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact dk_bind (caf_threadSet t _ _) fun _ => caf_setThreadStateAct t
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_setThreadState _ _)

theorem caf_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    FK (caF t) (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_getSimpleKo _ _ _)

theorem caf_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    FK (caF t) (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_setSimpleKo _ _ _ _)

theorem caf_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    FK (caF t) (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_updateSkObjRef _ _ _ _ _)

theorem caf_getSchedContext (q : ObjRef) : FK (caF t) (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_getSchedContext _ _)

theorem caf_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    FK (caF t) (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_updateSchedContext _ _ _)

theorem caf_replyUnlinkTcb (r : ObjRef) : FK (caF t) (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; caf_auto
macro_rules | `(tactic| caf_leaf) => `(tactic| with_reducible exact caf_replyUnlinkTcb _ _)

/-- **`cancel_ipc t` keeps `caF t`.** -/
theorem caf_cancelIpc : FK (caF t) (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  caf_auto

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open Fl4Spec Classical

noncomputable section

/-- Every outcome of `m` leaves `t` an inactive TCB. -/
def PostI (t : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → ∃ y, x.2.kheap t = some (.tcb y) ∧ y.tcbState = .inactive

theorem postI_bind {t : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hg : ∀ a, PostI t (g a)) : PostI t (m >>= g) := by
  intro σ x hx
  obtain ⟨y, -, hx⟩ := hx
  exact hg y.1 y.2 x hx

theorem kh_setThreadStateAct (t : ObjRef) :
    Vs.FK (fun σ : State Unit => σ.kheap) (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction; dk_auto0

theorem postI_setThreadState (t : ObjRef) : PostI t (setThreadState (Z := Unit) t .inactive) := by
  intro σ x hx
  unfold setThreadState at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨xt, -, e⟩ := SVK.threadSet_mem hy
  have h2 : x.2.kheap = y.2.kheap := kh_setThreadStateAct t y.2 x hx
  refine ⟨{ xt with tcbState := .inactive }, ?_, rfl⟩
  rw [h2, e]; simp [Notif.updK]

theorem postI_replyUnlinkTcb (t r : ObjRef) : PostI t (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb
  repeat' (first | exact postI_setThreadState t | refine postI_bind (fun _ => ?_))

theorem postI_replyRemoveTcb (t r : ObjRef) : PostI t (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb
  repeat' (first | exact postI_replyUnlinkTcb t r | refine postI_bind (fun _ => ?_) | split)

/-- **Cancelling a thread that is not current** keeps the current thread,
the idle thread, the scheduler action, the ready queues and every other TCB
(module docstring). -/
theorem cancelOther_keep {σ σ' : State Unit} {i : ObjRef} (hm : ((), σ') ∈ (cancelIpc (Z := Unit) i σ).1)
    (hne : σ.curThread ≠ i) :
    σ'.curThread = σ.curThread ∧ σ'.idleThread = σ.idleThread ∧ σ'.schedulerAction = σ.schedulerAction ∧
      σ'.readyQueues = σ.readyQueues ∧
      ∀ q x, q ≠ i → σ.kheap q = some (.tcb x) → σ'.kheap q = some (.tcb x) := by
  have h1 := Vs.caf_cancelIpc i σ ((), σ') hm
  have hct : σ'.curThread = σ.curThread := congrArg Prod.fst h1
  have hid : σ'.idleThread = σ.idleThread := congrArg (fun p => p.2.1) h1
  have h3 := congrArg (fun p => p.2.2) h1
  simp only [Vs.caF, hct, if_neg hne] at h3
  have hik := Sched.ikm_cancelIpc (t := i) σ ((), σ') hm
  have hxk := Sched.pxk_cancelIpc (p := i) σ ((), σ') hm
  exact ⟨hct, hid, Option.some.inj h3, hik.2.1, fun q x hq h => hxk.1 q x hq h⟩

/-- **After cancelling `i`, the reply object `i` was linked to is free**
(module docstring). -/
theorem cancelOther_reply {σ σ' : State Unit} {i q : ObjRef} (hsv : Sched.SchedValid σ)
    (hsv' : Sched.SchedValid σ') (hm : ((), σ') ∈ (cancelIpc (Z := Unit) i σ).1) {xr : Reply}
    (hkr : σ.kheap q = some (.reply xr)) (hrt : xr.replyTcb = some i)
    (hin : ∃ y, σ'.kheap i = some (.tcb y) ∧ y.tcbState = .inactive) {xr' : Reply}
    (hkr' : σ'.kheap q = some (.reply xr')) : xr'.replyTcb = none := by
  cases h : xr'.replyTcb with
  | none => rfl
  | some u =>
    exfalso
    obtain ⟨x, hku, hst⟩ := hsv'.replyTcb q xr' u hkr' h
    by_cases hui : u = i
    · subst hui
      obtain ⟨y, hy, hy0⟩ := hin
      rw [hku] at hy; cases hy
      rcases hst with e | ⟨ep, d, e⟩ <;> rw [hy0] at e <;> cases e
    · obtain ⟨y0, hk0, es⟩ := (StK.st_cancelIpc (t0 := i) σ ((), σ') hm).1 u x hui hku
      have hq : ∃ xr0, σ.kheap q = some (.reply xr0) ∧ xr0.replyTcb = some u := by
        rcases hst with e | ⟨ep, d, e⟩
        · exact hsv.onReply u y0 q hk0 (es ▸ e)
        · exact hsv.recvReply u y0 ep q d hk0 (es ▸ e)
      obtain ⟨xr0, hk1, e1⟩ := hq
      rw [hkr] at hk1; cases hk1
      rw [hrt] at e1; exact hui (Option.some.inj e1).symm

/-- **The spec's `receive_ipc` with a reply linked to `i ≠ t`** is the one
at the state after cancelling `i`, where the reply is free. -/
theorem receiveIpc_linked {σ σ' : State Unit} {t e i q : ObjRef} (b : Badge) (rights : CapRights) (bl : Bool)
    (rr : CapRights) {xr xr' : Reply} (hkr : σ.kheap q = some (.reply xr)) (hrt : xr.replyTcb = some i) (hit : i ≠ t)
    (hc : cancelIpc (Z := Unit) i σ = ({((), σ')}, False)) (hkr' : σ'.kheap q = some (.reply xr'))
    (hrt' : xr'.replyTcb = none) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) bl (.replyCap q rr) σ =
      receiveIpc (Z := Unit) t (.endpointCap e b rights) bl (.replyCap q rr) σ' := by
  unfold receiveIpc
  dsimp only
  rw [Notif.nd_pure_bind', Notif.nd_pure_bind']
  dsimp only
  rw [Notif.nd_bind_one (Endp.getReplyTcb_eq hkr), Notif.nd_bind_one (Endp.getReplyTcb_eq hkr')]
  have hc' : cancelIpc (Z := Unit) (the xr.replyTcb) σ = ({((), σ')}, False) := by rw [hrt]; exact hc
  rw [nd_when_true_bind (by simp [hrt]; exact hit), Notif.nd_bind_one hc', Endp.nd_when_false_bind (by simp [hrt'])]

end

end Fl4Proofs.P3

/-! ## FL4's `take_reply` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem tcb_ne_eq (a b : obj.Tcb) :
    core.cmp.PartialEq.ne.trait_default obj.Tcb.Insts.CoreCmpPartialEqTcb a b = ok (decide (a ≠ b)) := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
  exact ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

/-- `take_reply` of a free reply object: no cancel. -/
theorem take_reply_free {s : S} {a : A} {t q : U64} {g' : Bool} (h0 : L.mem s (rTcbA q) = 0#u64) :
    endpoint.take_reply st arI s a t (.Reply q g') = ok (q, s, a) := by
  obtain ⟨v, hv, e⟩ := spec_exists (P1.obj.Reply.tcb.blk (L := L) s q)
  rw [show P1.rTcbA q = Endp.rTcbA q from rfl, h0] at e; subst e
  simp [endpoint.take_reply, hv, obj.Tcb.is_null]

/-- `take_reply` of a reply object linked to `i ≠ t`: `cancel_ipc i`. -/
theorem take_reply_linked {s : S} {a : A} {t q i : U64} {g' : Bool} (hi : L.mem s (rTcbA q) = i)
    (hi0 : i ≠ 0#u64) (hit : i ≠ t) :
    endpoint.take_reply st arI s a t (.Reply q g') = (do
      let (s1, a1) ← ipc.cancel_ipc st arI s a i
      ok (q, s1, a1)) := by
  obtain ⟨v, hv, e⟩ := spec_exists (P1.obj.Reply.tcb.blk (L := L) s q)
  rw [show P1.rTcbA q = Endp.rTcbA q from rfl, hi] at e; subst e
  simp [endpoint.take_reply, hv, obj.Tcb.is_null, hi0, tcb_ne_eq]
  intro h
  exact absurd (UScalar.eq_of_val_eq h) hit

/-- **FL4's `receive_ipc` with a reply linked to `i ≠ t`**: `cancel_ipc i`,
then `receive_ipc` at the state after (the reply now free). -/
theorem receive_ipc_linked {s : S} {a : A} {t e cb q i : U64} {c1 c2 c3 c4 bl g' : Bool}
    (hi : L.mem s (rTcbA q) = i) (hi0 : i ≠ 0#u64) (hit : i ≠ t) {P : S × A → Prop}
    (h : ipc.cancel_ipc st arI s a i ⦃ r => L.mem r.1 (rTcbA q) = 0#u64 ∧
      endpoint.receive_ipc st arI r.1 r.2 t (.Endpoint e cb c1 c2 c3 c4) bl (.Reply q g') ⦃ P ⦄ ⦄) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) bl (.Reply q g') ⦃ P ⦄ := by
  unfold endpoint.receive_ipc
  rw [take_reply_linked hi hi0 hit]
  simp only [capability.Cap.ptr, bind_ok, Std.bind_assoc]
  refine WP.spec_bind h ?_
  rintro ⟨s1, a1⟩ ⟨h0, hr⟩
  unfold endpoint.receive_ipc at hr
  rw [take_reply_free h0] at hr
  simp only [capability.Cap.ptr, bind_ok] at hr
  first | (simp only [bind_ok]; exact hr) | (dsimp only; simp only [bind_ok]; exact hr) | simpa using hr | (simp only [Bind.bind, Std.bind] at hr ⊢; exact hr)

end

end

end Fl4Proofs.P3

/-! ## At `J` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`cancel_ipc` keeps the slots** (P1's footprint `ipc.cancel_ipc.kw`
outside the slots: `JPlaced.kwOutBlk`, `slotsSame_of_foot`). -/
theorem JAtZ.cancel_slots {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    ipc.cancel_ipc st arI s a t ⦃ r => SlotsSame Z.th (L.mem s) (L.mem r.1) ⦄ := by
  have hiT : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := J.blk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hK := hJ.kwOutBlk J.blk
  refine WP.spec_mono (P1.ipc.cancel_ipc.kw s a t h0 hiT hX.1 hSg.sub (fun hs' => by
      obtain ⟨h1, h2⟩ := hX.2.1.reply t hiT hs'
      exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs' h0' => (hX.2.1.recv t hiT hs' h0').1)) ?_
  rintro ⟨s', a'⟩ hf
  try simp only [WP.uncurry'_pair] at hf
  exact Sched.slotsSame_of_foot J.xtop.rel.1 hK hf

/-- **`cancel_ipc` at `J` of a thread linked to a reply** (blocked on it, or
receiving with it): `JAtZ.cancelReplyJ` / `JAtZ.cancelRecvJ` with the slots
kept and the thread inactive after. -/
theorem JAtZ.cancelLinkJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {i : U64} (hi : i ∈ Z.T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap i.bv = some (.tcb x)) {q : Fl4Spec.ObjRef}
    (hst : x.tcbState = .blockedOnReply q ∨ ∃ e d, x.tcbState = .blockedOnReceive e (some q) d) :
    ipc.cancel_ipc st arI s a i ⦃ r => SlotsSame Z.th (L.mem s) (L.mem r.1) ∧ r.2 = a ∧
      ∃ σ', Fl4Spec.cancelIpc (Z := Unit) i.bv σ = ({((), σ')}, False) ∧
        (∃ y, σ'.kheap i.bv = some (.tcb y) ∧ y.tcbState = .inactive) ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have hmain : ipc.cancel_ipc st arI s a i ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.cancelIpc (Z := Unit) i.bv σ = ({((), σ')}, False) ∧
        (∃ y, σ'.kheap i.bv = some (.tcb y) ∧ y.tcbState = .inactive) ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
    rcases hst with hst | ⟨e, d, hst⟩
    · refine WP.spec_mono (J.cancelReplyJ hi hk hst) ?_
      rintro ⟨s', a'⟩ ⟨h1, σ', he, V, Ac', Lst', J'⟩
      refine ⟨h1, σ', he, ?_, V, Ac', Lst', J'⟩
      have e2 : Fl4Spec.cancelIpc (Z := Unit) i.bv σ =
          Fl4Spec.replyRemoveTcb i.bv q (updK σ i.bv (.tcb { x with tcbFault := none })) := by
        unfold Fl4Spec.cancelIpc
        rw [Notif.nd_bind_one (Notif.getThreadState_eq hk), Notif.nd_bind_one (Notif.threadSet_eq _ hk), hst]
      have hm : ((), σ') ∈ (Fl4Spec.replyRemoveTcb (Z := Unit) i.bv q
          (updK σ i.bv (.tcb { x with tcbFault := none }))).1 := by
        rw [← e2, he]; exact Set.mem_singleton _
      exact postI_replyRemoveTcb _ _ _ _ hm
    · refine WP.spec_mono (J.cancelRecvJ hi hk hst) ?_
      rintro ⟨s', a'⟩ ⟨h1, σ', he, V, Ac', Lst', J'⟩
      refine ⟨h1, σ', he, ?_, V, Ac', Lst', J'⟩
      obtain ⟨xe, hke, hq⟩ := J.sv.recvQ i.bv x e (some q) d hk hst
      have hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) i.bv σ).1 := by rw [he]; exact Set.mem_singleton _
      exact ⟨_, (Sched.cancelIpc_recv_cfr (r := i.bv) hk hst hke hq
        (fun rp h => J.sv.recvReply i.bv x e rp d hk (by rw [hst, h])) hm).2.1, rfl⟩
  exact WP.spec_mono (WP.spec_and (J.cancel_slots hi) hmain) fun r h => ⟨h.1, h.2⟩

theorem jHeld_of_same {th : TypedHeap} {s s' : S} (h : SlotsSame th (L.mem s) (L.mem s')) {c : capability.Cap}
    (hc : JHeld (L := L) th s c) : JHeld (L := L) th s' c := by
  obtain ⟨y, hy, e⟩ := hc
  refine ⟨y, hy, ?_⟩
  unfold capV
  rw [(h y hy).1, (h y hy).2.1]
  exact e

/-- The case XTopJointRecvSend's `JAtZ.recvSendJ0` and XTopJointRecvSendRet's
`JAtZ.recvSendRetJ` prove: the current thread without a bound notification or
with one not active (if blocking and lending its SC to the thread,
`maybe_return_sc` first), the endpoint's head sender as in
XTopJointRecvSendF's `SendOK` (not faulted and either not calling or calling
without a reply pushed, or faulted (a timeout fault only without an SC)
without a reply pushed; no reply pushed: neither grant right, or no reply
cap, the sender `Inactive`). -/
def RecvSendBasicCase (ct : U64) (blocking : Bool) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) :
    Prop :=
  (∀ xt, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = none ∨
    ∃ n xn, xt.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
      Fl4Spec.isActive xn = false) ∧
    ∃ sd q xs, σ.kheap p.bv = some (.endpoint (.sendEP (sd :: q))) ∧ σ.kheap sd = some (.tcb xs) ∧
      SendOK xs rc

/-- The case XTopJointRecvSendP's `JAtZ.recvSendP0X` proves: the current
thread without a bound notification or with one not active (if blocking, not
lending its SC to the thread), the endpoint's head sender as in
XTopJointRecvSendP's `PushOK` (a reply pushed). -/
def RecvSendPushCase (ct : U64) (blocking : Bool) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) :
    Prop :=
  (∀ xt, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = none ∨
    ∃ n xn, xt.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
      Fl4Spec.isActive xn = false ∧ (blocking = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))) ∧
    ∃ sd q xs, σ.kheap p.bv = some (.endpoint (.sendEP (sd :: q))) ∧ σ.kheap sd = some (.tcb xs) ∧
      PushOK xs rc

/-- The case XTopJointRecvSendRP's `JAtZ.recvSendRetPJ` (head sender without
an SC) and XTopJointRecvSendRD's `JAtZ.recvSendRetPDJ` (with an SC, the
passive-server call) prove: a blocking receive, the current thread's bound
notification not active and lending it its SC, the endpoint's head sender as
in `PushOK`. -/
def RecvSendRetPushCase (ct : U64) (blocking : Bool) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) :
    Prop :=
  blocking = true ∧
    (∀ xt, σ.kheap ct.bv = some (.tcb xt) → ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none) ∧
    ∃ sd q xs, σ.kheap p.bv = some (.endpoint (.sendEP (sd :: q))) ∧ σ.kheap sd = some (.tcb xs) ∧
      PushOK xs rc

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a null or free reply** (the former `jRecvIpcHyp_of`'s
case split, every waiting-sender case proved). -/
theorem jRecvIpcU_of (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (blocking : Bool) (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  by_cases hca : RecvIpcActCase (L := L) ct s σ rc
  · obtain ⟨⟨xt, n0, x, b0, hkt, hbn, hkn, hact⟩, hrr⟩ := hca
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    exact J.recvIpcActJ hAT ht hcur hni hnq hkt hn hkn hbn hact blocking hke b sd true g gr hra b.bv
      (rightsOf sd true g gr)
  by_cases hcb : RecvIpcBlockCase (L := L) ct blocking s σ p rc
  · obtain ⟨rfl, hbn, hns, hrr⟩ := hcb
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨hcov, hcovR⟩ := J.recvCov_of he hHd hHr hra
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    have hx := hI.1.toE.at_ep he hke
    have hst2 : stOf (L.mem s) p = 0#u64 ∨ stOf (L.mem s) p = 2#u64 := by
      cases xe with
      | idleEP => exact Or.inl hx.1
      | recvEP q => exact Or.inr hx.1
      | sendEP q => exact absurd rfl (hns _ hke q)
    have hbound : L.mem s (tBoundA ct) = 0#u64 :=
      optRef_none ((hI.1.toE.at_tcb ht hkt).bound.symm.trans (hbn xt hkt))
    exact J.recvIpcBlockJ ht hcur hni hnq hkt he hke hcB hcov hra hcovR b sd true g gr b.bv
      (rightsOf sd true g gr) (fun h => receive_ipc_block_red hra hbound hst2 h)
      (receiveIpc_noSend b.bv (rightsOf sd true g gr) true (replyArg_spec J.ip.e hI.1.toE hra) hkt (hbn xt hkt) hke
        (hns xe hke))
  by_cases hcn : RecvIpcBoundCase (L := L) ct blocking s σ p rc
  · obtain ⟨rfl, ⟨xt, n0, xn, hkt, hbn, hkn, hna⟩, hns, hrr⟩ := hcn
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    by_cases hnr : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none
    · exact J.recvIpcRetJ ht hcur hni hnq hkt hn hbn hkn hna hnr he hke hcB hHd hHr hra b.bv (rightsOf sd true g gr)
    obtain ⟨hcov, hcovR⟩ := J.recvCov_of he hHd hHr hra
    exact J.recvIpcBlockNJ ht hcur hni hnq hkt hn hbn hkn hna hnr he hke hcB hcov hra hcovR b sd true g gr b.bv
      (rightsOf sd true g gr)
  by_cases hcs : RecvSendBasicCase ct blocking σ p rc
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcs
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    have hrun := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
    rcases hbn xt hkt with hb0 | ⟨n0, xn, hbn0, hkn, hna⟩
    · exact J.recvSendJ0X ht hkt hrun (Or.inl hb0) hcur he hke' hks
        b sd true g gr hra hok b.bv (rightsOf sd true g gr)
    by_cases hl : blocking = true ∧ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    · obtain ⟨rfl, hl⟩ := hl
      obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
      exact J.recvSendRetJ ht hcur hni hnq hkt hn hbn0 hkn hna hl he hke' hks b sd true g gr hra hok b.bv
        (rightsOf sd true g gr)
    · exact J.recvSendJ0X ht hkt hrun (Or.inr ⟨n0, xn, hbn0, hkn, hna, fun hb h => hl ⟨hb, h⟩⟩) hcur he hke' hks
        b sd true g gr hra hok b.bv (rightsOf sd true g gr)
  by_cases hcp : RecvSendPushCase ct blocking σ p rc
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcp
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    have hrun := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
    have hrv0 : rv ≠ 0#u64 := by
      rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hok.1
      · exact (J.rp.align rv hr).2.1
    obtain ⟨-, hcovR⟩ := J.recvCov_of he hHd hHr hra
    exact J.recvSendP0X hAT ht hkt hrun (hbn xt hkt) hcur hni hnq he hke' hks b sd true g gr hra (hcovR hrv0) hok
      b.bv (rightsOf sd true g gr)
  by_cases hcr : RecvSendRetPushCase ct blocking σ p rc
  · obtain ⟨rfl, hbn, sd0, q, xs, hke', hks, hok⟩ := hcr
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    obtain ⟨n0, xn, hbn0, hkn, hna, hl1, hl2⟩ := hbn xt hkt
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    by_cases hsn : xs.tcbSchedContext = none
    · exact J.recvSendRetPJ hAT ht hcur hni hnq hkt hn hbn0 hkn hna ⟨hl1, hl2⟩ he hke' hks b sd hra hok hsn
        hHd hHr b.bv (rightsOf sd true g gr)
    · exact J.recvSendRetPDJ hAT ht hcur hni hnq hkt hn hbn0 hkn hna ⟨hl1, hl2⟩ he hke' hks b sd hra hok hsn
        hHd hHr b.bv (rightsOf sd true g gr)
  by_cases hc : RecvIpcPollCase (L := L) ct blocking s σ p rc
  swap
  · -- the case left: a head sender with a timeout fault and an SC
    obtain ⟨xt, hkt, -⟩ := (J.xtop.irelK J.ks J.buf).1.tcb ct ht
    have hbn0 : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
        σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false := by
      rcases hb : xt.tcbBoundNotification with _ | n
      · exact Or.inl rfl
      · obtain ⟨xn, hkn⟩ := J.sv.tcbNtfn ct.bv xt n hkt hb
        refine Or.inr ⟨n, xn, rfl, hkn, ?_⟩
        cases hxo : xn.ntfnObj with
        | activeNtfn b0 => exact absurd ⟨⟨xt, n, xn, b0, hkt, hb, hkn, hxo⟩, hun⟩ hca
        | idleNtfn => simp [Fl4Spec.isActive, hxo]
        | waitingNtfn q => simp [Fl4Spec.isActive, hxo]
    have hbnA : ∀ xt', σ.kheap ct.bv = some (.tcb xt') → xt'.tcbBoundNotification = none ∨
        ∃ n xn, xt'.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
          Fl4Spec.isActive xn = false := fun x' hx' => by rw [hkt] at hx'; cases hx'; exact hbn0
    have hsend : ∃ l, xe = .sendEP l := by
      by_contra hns
      push_neg at hns
      have hns' : ∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q := fun x hx q => by
        rw [hke] at hx; cases hx; exact hns q
      rcases Bool.eq_false_or_eq_true blocking with hbl | hbl
      · rcases hbn0 with hb0 | ⟨n, xn, hb0, hkn, hna⟩
        · exact hcb ⟨hbl, fun x' hx' => by rw [hkt] at hx'; cases hx'; exact hb0, hns', hun⟩
        · exact hcn ⟨hbl, ⟨xt, n, xn, hkt, hb0, hkn, hna⟩, hns', hun⟩
      · exact hc ⟨hbl, hbnA, hns', hun⟩
    obtain ⟨l, rfl⟩ := hsend
    obtain ⟨sd0, q, xs, e', dd, rfl, hks, hstd⟩ := J.head_sendT he hke
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hnl : ¬ (blocking = true ∧ ∃ n xn, xt.tcbBoundNotification = some n ∧
        σ.kheap n = some (.notification xn) ∧ xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none) →
        ∀ xt', σ.kheap ct.bv = some (.tcb xt') → xt'.tcbBoundNotification = none ∨
          ∃ n xn, xt'.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
            Fl4Spec.isActive xn = false ∧ (blocking = true → ¬ (xn.ntfnSc = xt'.tcbSchedContext ∧ xn.ntfnSc ≠ none)) := by
      intro hl x' hx'
      rw [hkt] at hx'; cases hx'
      rcases hbn0 with h | ⟨n, xn, hb0, hkn, hna⟩
      · exact Or.inl h
      · exact Or.inr ⟨n, xn, hb0, hkn, hna, fun hbl hl' => hl ⟨hbl, n, xn, hb0, hkn, hl'⟩⟩
    have hnaL : ∀ n xn, xt.tcbBoundNotification = some n → σ.kheap n = some (.notification xn) →
        Fl4Spec.isActive xn = false := by
      intro n xn hb0 hkn
      rcases hbn0 with h | ⟨n', xn', h', hkn', hna'⟩
      · rw [hb0] at h; cases h
      · rw [hb0] at h'; cases h'; rw [hkn] at hkn'; cases hkn'; exact hna'
    rcases sendOK_split rc hstd with hok | hok | hok
    · exact absurd ⟨hbnA, _, q, xs, hke, hks, hok⟩ hcs
    · by_cases hl : blocking = true ∧ ∃ n xn, xt.tcbBoundNotification = some n ∧
          σ.kheap n = some (.notification xn) ∧ xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none
      · obtain ⟨hbl, n, xn, hb0, hkn, hl1, hl2⟩ := hl
        exact absurd ⟨hbl, fun x' hx' => by
          rw [hkt] at hx'; cases hx'; exact ⟨n, xn, hb0, hkn, hnaL n xn hb0 hkn, hl1, hl2⟩,
          _, q, xs, hke, hks, hok⟩ hcr
      · exact absurd ⟨hnl hl, _, q, xs, hke, hks, hok⟩ hcp
    · obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
      have hrun := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
      by_cases hl : blocking = true ∧ ∃ n xn, xt.tcbBoundNotification = some n ∧
          σ.kheap n = some (.notification xn) ∧ xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none
      · obtain ⟨rfl, n0, xn, hb0, hkn, hl1, hl2⟩ := hl
        obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
        exact J.recvSendRetTJ hAT hmax htu ht hcur hni hnq hkt hn hb0 hkn (hnaL _ xn hb0 hkn) ⟨hl1, hl2⟩ he hke hks
          b sd hra hok hHd hHr b.bv (rightsOf sd true g gr)
      · exact J.recvSendT0X hAT hmax htu ht hkt hrun (hnl hl xt hkt) hcur hni hnq he hke hks b sd true g gr hra
          (J.recvCov_of he hHd hHr hra).2 hok b.bv (rightsOf sd true g gr)
  obtain ⟨rfl, hbn, hns, hrr⟩ := hc
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
  obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
  rcases hbn xt hkt with hbn | ⟨n0, xn, hbn, hkn, hna⟩
  · exact J.recvIpcPollJ ht hkt hbn he hke (hns xe hke) b sd true g gr hra b.bv (rightsOf sd true g gr)
  · obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    exact J.recvIpcPollNJ ht hkt hn hbn hkn hna he hke (hns xe hke) b sd true g gr hra b.bv
      (rightsOf sd true g gr)

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a reply linked to another thread**
(module docstring): FL4's and the spec's `cancel_ipc` of that thread
(`JAtZ.cancelLinkJ`), then `jRecvIpcU_of` at the state after. -/
theorem jRecvIpcLink_of (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (blocking : Bool) (p b : U64) (sd g gr : Bool) (q : U64) (g' : Bool) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x)) (hcr : CapRel (.Reply q g') rc')
    {xr : Fl4Spec.Reply} (hkr : σ.kheap q.bv = some (.reply xr))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : JHeld (L := L) Z.th s (.Reply q g')) (hi0 : L.mem s (rTcbA q) ≠ 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking (.Reply q g') ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hR := (J.xtop.irelK J.ks J.buf).1.toE
  obtain ⟨q0, hq, hqe⟩ := J.obj.reply _ xr hkr
  rw [Sched.bv_inj hqe] at hq
  have hrt : xr.replyTcb = some (L.mem s (rTcbA q)).bv := (hR.at_reply hq hkr).trans (Notif.optRef_ne hi0)
  obtain ⟨xi, hki, hsti⟩ := J.sv.replyTcb q.bv xr _ hkr hrt
  obtain ⟨i, hiT, hie⟩ := J.obj.tcb _ xi hki
  have hiq : L.mem s (rTcbA q) = i := (P1.eq_of_bv hie).symm
  rw [hiq] at hrt hki hi0
  have hict : i ≠ ct := by
    intro e
    subst e
    have hr := (J.curRun.run hni) xi (by rw [hcur]; exact hki)
    rcases hsti with h | ⟨_, _, h⟩ <;> rw [h] at hr <;> simp [Fl4Spec.runnable] at hr
  have hne : σ.curThread ≠ i.bv := fun e => hict (P1.eq_of_bv (e.symm.trans hcur))
  refine receive_ipc_linked hiq hi0 hict ?_
  refine WP.spec_mono (J.cancelLinkJ hiT hki hsti) ?_
  rintro ⟨s1, a1⟩ ⟨hSS, h1, σ', he, hin, V, Ac', Lst', J'⟩
  dsimp only at h1 hSS J' ⊢
  subst h1
  have hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) i.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  obtain ⟨hct', hid', hact', hrq', -⟩ := cancelOther_keep hm hne
  have hR' := (J'.xtop.irelK J'.ks J'.buf).1.toE
  obtain ⟨xr', hkr', hrl⟩ := hR'.reply q hq
  have hnone : xr'.replyTcb = none := cancelOther_reply J.sv J'.sv hm hkr hrt hin hkr'
  have h0' : L.mem s1 (rTcbA q) = 0#u64 := optRef_none (hrl.symm.trans hnone)
  refine ⟨h0', ?_⟩
  have hcr' : rc' = absCap (.Reply q g') := hcr.abs
  subst hcr'
  have hsp : Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking
      (absCap (.Reply q g')) σ =
      Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking
      (absCap (.Reply q g')) σ' :=
    receiveIpc_linked _ _ _ _ hkr hrt (fun e => hne (hcur.trans e.symm)) he hkr' hnone
  rw [hsp]
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he', h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he'
  obtain ⟨xe', hke', -⟩ := hR'.ep p he'
  exact jRecvIpcU_of (Z := Z.mv Z.G V) hAT hmax htu J' ht (hct'.trans hcur) ⟨by rw [hct', hid']; exact hni.1, by rw [hact']; exact hni.2⟩
    (by rw [hct', hrq']; exact hnq) blocking p b sd g gr (.Reply q g') _ ⟨xe', hke'⟩
    (Or.inr ⟨hcr, q, g', rfl, xr', hkr'⟩) (jHeld_of_same hSS hHd) (fun _ _ _ => jHeld_of_same hSS hHr)
    (Or.inr ⟨q, g', rfl, h0'⟩)

/-- **`JRecvIpcHyp`** (`jRecvIpcU_of` for a null or free
reply, `jRecvIpcLink_of` for a linked one). -/
theorem jRecvIpcHypL_of (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (blocking : Bool) : JRecvIpcHyp (L := L) arI AR Z.th ct blocking s a σ := by
  intro p b sd g gr rc rc' hpE hrc hHd hHr
  by_cases hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64
  · exact jRecvIpcU_of hAT hmax htu J ht hcur hni hnq blocking p b sd g gr rc rc' hpE hrc hHd hHr hun
  · rcases hrc with ⟨rfl, -⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
    · exact absurd (Or.inl rfl) hun
    · exact jRecvIpcLink_of hAT hmax htu J ht hcur hni hnq blocking p b sd g gr q g' rc' hpE hcr hkr hHd (hHr q g' rfl)
        (fun h => hun (Or.inr ⟨q, g', rfl, h⟩))

set_option maxHeartbeats 4000000 in
/-- **`dispatch_recvJS` with `jRecvIpcHypL_of`**: the receiving syscalls at
`J` against `fl4HandleEvent rep`'s branches (JEntryGlob's `maxTU` / `tu` for the
timeout-fault transfer). -/
theorem dispatch_recvJL (rep : Bool) (hAT : P0.ArchTotal arI) (s : S) (a : A)
    (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (number : I64) (bl cr : Bool) (hn : RecvSys number bl cr)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a number ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) rep (recvSysOf bl cr)).run σ).1,
        y.1 = .ok () ∧ RJ (L := L) arI AR r.1 r.2 y.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  exact dispatch_recvJS rep hAT s a σ J hni hct hnq hvfh number bl cr hn
    (jRecvIpcHypL_of hAT hmax htu J hctT hcur hni hnq bl)

end

end

end Fl4Proofs.P3
