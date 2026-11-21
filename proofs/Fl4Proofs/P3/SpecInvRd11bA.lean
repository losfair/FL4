/-
P3 (DESIGN.md §9), invariant line G1 (rd11b, KENTRY-PLAN rd10 handoff 3):
**`handle_fault` of the current thread** (spec side only, outside the JAtZ cone).

* `QS t` (t's fault is set and t is not receive-blocked; rd9's `QR` without
  "runnable"), `qs_tcbEpDequeue`; **`no_sendIpcD`**: rd9's `no_sendIpc` for
  any `canDonate` (the donating arm is the no-fault, non-call one, absurd once
  the fault is set; `reply_push` donates after the BlockedOnReply write).
* `sfi_no` (send_fault_ipc: null cap ⇒ `false`, state kept; endpoint cap ⇒
  `true` and `NO t`), **`nr_handleFault`**: after `handle_fault t` of a thread
  `t` that is not receive-blocked, `t` is not runnable.
* `cp_replyPush` (any `canDonate`), **`cp_sendIpc`**, `cp_sendFaultIpc`,
  **`cp_handleFault`**: rd8a's pinned `CP σ0 c` (cur_sc = c; the SC at `c`
  keeps refills / max; resume is not set) across `handle_fault`; `cfk_handleFault`
  (cfS kept, RdP's family).
* `PV` (CP ∧ cfS ∧ `TP (NB0 t)`), `mem_hvf` (handle_vm_fault always throws,
  after a machine read and a register read), **`pv_handleVmFault`**.
-/
import Fl4Proofs.P3.SpecInvRd10A3
open Classical

namespace Fl4Proofs.P3.SInvR.A11b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `t` not runnable after `handle_fault t` -/

/-- `t` is not receive-blocked. -/
def NB0 (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop :=
  p = t → ∀ e r d, x.tcbState ≠ .blockedOnReceive e r d

/-- `t`'s fault is set and `t` is not receive-blocked. -/
def QS (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop :=
  p = t → x.tcbFault ≠ none ∧ ∀ e r d, x.tcbState ≠ .blockedOnReceive e r d

theorem qs_tcbEpDequeue (t d e : ObjRef) : IK (TP (QS t)) (tcbEpDequeue (Z := Unit) d e) := by
  unfold tcbEpDequeue; tq_auto

/-- **`send_ipc` (blocking, not call, any donation) of a faulted sender that is
not receive-blocked** leaves it not runnable (rd9's `no_sendIpc`). -/
theorem no_sendIpcD (t ep : ObjRef) (bd : Badge) (g gr d : Bool) (σ : State Unit) (hσ : TP (QS t) σ) :
    ∀ y ∈ (sendIpc (Z := Unit) true false bd g gr d t ep σ).1, A9.NO t y.2 := by
  unfold sendIpc
  intro y ⟨e, he, hy⟩
  obtain ⟨hk, hs⟩ := mem_getSimpleKo he
  obtain ⟨ev, σ1⟩ := e
  simp only at hk hs; subst hs
  cases ev with
  | idleEP => exact A9.no_sendIpcBlocked t ep bd g gr false _ y hy
  | sendEP q => exact A9.no_sendIpcBlocked t ep bd g gr false _ y hy
  | recvEP l =>
    cases l with
    | nil => exact hy.elim
    | cons dest q =>
      obtain ⟨z1, hz1, hy⟩ := hy
      have hQ1 : TP (QS t) z1.2 := qs_tcbEpDequeue t dest ep σ1 hσ z1 hz1
      obtain ⟨z2, hz2, hy⟩ := hy
      unfold getThreadState at hz2
      obtain ⟨xd, hxd, rfl⟩ := mem_threadGet hz2
      dsimp only at hy
      have hQF1 : TP (A9.QF t) z1.2 := fun p x hp e => (hQ1 p x hp e).1
      cases hst : xd.tcbState with
      | blockedOnReceive ep' reply dd =>
        have hne : dest ≠ t := by
          intro e; subst e
          exact (hQ1 dest xd hxd rfl).2 ep' reply dd hst
        rw [hst] at hy
        obtain ⟨z3, hz3, hy⟩ := hy
        rw [Set.mem_singleton_iff.1 hz3] at hy
        obtain ⟨z4, hz4, hy⟩ := hy
        have hQ4 := A9.qf_doIpcTransfer t (some ep) bd g dest z1.2 hQF1 z4 hz4
        obtain ⟨z5, hz5, hy⟩ := hy
        have hQ5 : TP (A9.QF t) z5.2 :=
          (ik_maybeM (fun r => A9.qf_replyUnlinkTcb t dest r) reply) z4.2 hQ4 z5 hz5
        obtain ⟨z6, hz6, hy⟩ := hy
        unfold getTcbObjRef at hz6
        obtain ⟨x6, -, rfl⟩ := mem_threadGet hz6
        obtain ⟨z7, hz7, hy⟩ := hy
        obtain ⟨xt, hxt, rfl⟩ := mem_threadGet hz7
        have hF : xt.tcbFault ≠ none := hQ5 t xt hxt rfl
        dsimp only at hy
        split at hy
        · split at hy
          · obtain ⟨z8, hz8, hy⟩ := hy
            exact A9.no_wakeTail t dest hne z8.2 (A9.no_replyPush t dest _ d _ z8 hz8) y hy
          · obtain ⟨z8, hz8, hy⟩ := hy
            exact A9.no_wakeTail t dest hne z8.2 (A9.no_sts t _ (by rfl) hz8) y hy
        · rename_i hc; exact absurd (Or.inr hF) hc
      | _ => rw [hst] at hy; obtain ⟨_, h, _⟩ := hy; exact h.elim

/-- `send_fault_ipc`: a null cap returns `false` and keeps the state; an
endpoint cap returns `true` with `t` not runnable. -/
theorem sfi_no (t : ObjRef) (cap : Cap) (ex : Fault) (d : Bool) (s : State Unit) (hr : TP (NB0 t) s) :
    ∀ y ∈ (sendFaultIpc (Z := Unit) t cap ex d s).1, (y.1 = false ∧ y.2 = s) ∨ (y.1 = true ∧ A9.NO t y.2) := by
  intro y hy
  cases cap with
  | endpointCap r bd rights =>
    simp only [sendFaultIpc] at hy
    obtain ⟨y6, h6, hy⟩ := hy
    obtain ⟨xf, hxf, e6⟩ := SInv.mem_threadSet h6
    have hQ6 : TP (QS t) y6.2 := by
      intro p x hp ept; subst ept
      rw [e6] at hp; dsimp only at hp; rw [Function.update_self] at hp
      cases hp
      exact ⟨by simp, hr p xf hxf rfl⟩
    obtain ⟨y7, h7, hy⟩ := hy
    right
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨rfl, no_sendIpcD t _ _ _ _ _ y6.2 hQ6 y7 h7⟩
  | nullCap =>
    simp only [sendFaultIpc] at hy
    left
    first
      | (rw [Set.mem_singleton_iff.1 hy]; exact ⟨rfl, rfl⟩)
      | (subst hy; exact ⟨rfl, rfl⟩)
  | _ =>
    simp only [sendFaultIpc] at hy
    first | exact hy.elim | (simp [NonDet.fail] at hy)

/-- **After `handle_fault t` of a thread that is not receive-blocked, `t` is not runnable.** -/
theorem nr_handleFault (t : ObjRef) (ex : Fault) (s : State Unit) (hr : TP (NB0 t) s) :
    ∀ z ∈ (handleFault (Z := Unit) t ex s).1, A8.NRun t z.2 := by
  intro z hz
  unfold handleFault at hz
  obtain ⟨y1, h1, hz⟩ := hz
  rw [Set.mem_singleton_iff.1 h1] at hz
  obtain ⟨y2, h2, hz⟩ := hz
  obtain ⟨cap, s2⟩ := y2
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  dsimp only at e2 hz
  subst e2
  obtain ⟨y3, h3, hz⟩ := hz
  obtain ⟨x3, -, rfl⟩ := mem_threadGet h3
  obtain ⟨y4, h4, hz⟩ := hz
  dsimp only at h4 hz
  obtain ⟨y5, h5, hz⟩ := hz
  rw [Set.mem_singleton_iff.1 hz]
  rcases sfi_no t cap ex _ _ hr y4 h4 with ⟨ef, -⟩ | ⟨et, hn⟩
  · rw [ef] at h5
    unfold NonDet.unless handleNoFault at h5
    rw [if_neg (by decide)] at h5
    exact A9.nrun_of_no (A9.no_sts t _ rfl h5)
  · rw [et] at h5
    unfold NonDet.unless at h5
    rw [if_pos rfl] at h5
    rw [Set.mem_singleton_iff.1 h5]; exact A9.nrun_of_no hn

/-! ## `CP` across `handle_fault` -/

/-- `ordered_insert` keeps the state (RdL's `t_mem_orderedInsert`). -/
theorem sv_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : SVK.SVM (orderedInsert (Z := Unit) t ts f R) := fun σ y hy => by
  rw [(t_mem_orderedInsert hy).1]; exact SVK.SVS.refl _

theorem sv_tcbEpAppend (t e : ObjRef) (b : Bool) : SVK.SVM (tcbEpAppend (Z := Unit) t e b) := by
  unfold tcbEpAppend tcbAppend
  repeat' (first | (with_reducible exact sv_orderedInsert _ _ _ _) | sv_leaf | sv_step0)

theorem cp_tcbEpDequeue (t e : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (tcbEpDequeue (Z := Unit) t e) :=
  A8.ik_cp (sv_tcbEpDequeue t e) (cfk_tcbEpDequeue' t e) σ0 c

theorem cp_tcbEpAppend (t e : ObjRef) (b : Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (tcbEpAppend (Z := Unit) t e b) :=
  A8.ik_cp (sv_tcbEpAppend t e b) (cfk_tcbEpAppend' t e b) σ0 c

theorem cp_bindScReply (p r : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (bindScReply (Z := Unit) p r) :=
  A8.ik_cp (SVK.sv_bindScReply' p r) (cfk_bindScReply' p r) σ0 c

theorem cp_replyUnlinkTcb (t r : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (replyUnlinkTcb (Z := Unit) t r) :=
  A8.ik_cp (SVK.sv_replyUnlinkTcb t r) (cfk_replyUnlinkTcb' t r) σ0 c

macro "cp11_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact cp_tcbEpAppend _ _ _ _ _)
  | (with_reducible exact cp_tcbEpDequeue _ _ _ _)
  | (with_reducible exact cp_bindScReply _ _ _ _)
  | (with_reducible exact cp_replyUnlinkTcb _ _ _ _)
  | (with_reducible exact A8.cp_ifCondTest _ _ _ _)
  | (with_reducible refine ik_maybeM (fun _ => ?_) _)
  | cp_leaf | ik_step0 | split))

theorem cp_replyPush (a b r : ObjRef) (d : Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (replyPush (Z := Unit) a b r d) := by
  unfold replyPush; cp11_auto

macro "cp11b_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact cp_replyPush _ _ _ _ _ _)
  | (with_reducible exact cp_tcbEpAppend _ _ _ _ _)
  | (with_reducible exact cp_tcbEpDequeue _ _ _ _)
  | (with_reducible exact cp_bindScReply _ _ _ _)
  | (with_reducible exact cp_replyUnlinkTcb _ _ _ _)
  | (with_reducible exact A8.cp_ifCondTest _ _ _ _)
  | (with_reducible refine ik_maybeM (fun _ => ?_) _)
  | cp_leaf | ik_step0 | split))

/-- **`send_ipc` keeps `CP`** (any blocking / call / donation). -/
theorem cp_sendIpc (b k : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (sendIpc (Z := Unit) b k bd g gr d t e) := by
  unfold sendIpc sendIpcBlocked
  cp11b_auto

theorem cp_sendFaultIpc (t : ObjRef) (cap : Cap) (ex : Fault) (d : Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (sendFaultIpc (Z := Unit) t cap ex d) := by
  unfold sendFaultIpc
  split
  · exact ik_bind (A8.cp_threadSet _ _ _ _) fun _ => ik_bind (cp_sendIpc _ _ _ _ _ _ _ _ _ _) fun _ => ik_pure _
  · exact ik_pure _
  · exact ik_fail

/-- **`handle_fault` keeps `CP`.** -/
theorem cp_handleFault (t : ObjRef) (ex : Fault) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (handleFault (Z := Unit) t ex) := by
  unfold handleFault handleNoFault NonDet.unless
  repeat' (first
    | (with_reducible exact cp_sendFaultIpc _ _ _ _ _ _)
    | cp_leaf | ik_step0)

theorem cfk_handleFault (t : ObjRef) (ex : Fault) : CFK (handleFault (Z := Unit) t ex) := by
  unfold handleFault handleNoFault
  cfk_auto

/-! ## `handle_vm_fault` -/

/-- CP, cfS and `t` not receive-blocked. -/
abbrev PV (σ0 : State Unit) (t : ObjRef) (s : State Unit) : Prop :=
  A8.CP σ0 σ0.curSc s ∧ cfS s = cfS σ0 ∧ TP (NB0 t) s

theorem pv_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) (h3 : IK (TP (NB0 t)) m)
    (σ0 : State Unit) : IK (PV σ0 t) m := by
  intro s hs y hy
  exact ⟨A8.ik_cp h1 h2 σ0 σ0.curSc s hs.1 y hy, (h2 s y hy).trans hs.2.1, h3 s hs.2.2 y hy⟩

/-- `handle_vm_fault` always throws, after a machine read and a register read. -/
theorem mem_hvf {t : ObjRef} {ft : VMFaultType} {s : State Unit} {y : Except Fault Unit × State Unit}
    (hy : y ∈ ((handleVmFault (Z := Unit) t ft).run s).1) :
    (∃ e, y.1 = .error e) ∧ ∃ z1 ∈ (doMachineOp (Z := Unit) getFaultAddress s).1,
      ∃ z2 ∈ (asUser (Z := Unit) t (getRegister .errorRegister) z1.2).1, y.2 = z2.2 := by
  unfold handleVmFault at hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w1, hw1, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    obtain ⟨z', hz', ⟨a', ha', hy⟩ | ⟨e', he', -⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w2, hw2, rfl⟩ := ft_mem_liftE hz'
      simp only [Except.ok.injEq] at ha'; subst ha'
      cases ft <;>
      · dsimp only at hy
        obtain rfl := Set.mem_singleton_iff.1 hy
        exact ⟨⟨_, rfl⟩, w1, hw1, w2, hw2, rfl⟩
    · obtain ⟨w2, -, rfl⟩ := ft_mem_liftE hz'; cases he'
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he

/-- **`PV` across `handle_vm_fault`**, which has only error outcomes. -/
theorem pv_handleVmFault (t : ObjRef) (ft : VMFaultType) (σ0 s : State Unit) (hs : PV σ0 t s)
    (y : Except Fault Unit × State Unit) (hy : y ∈ ((handleVmFault (Z := Unit) t ft).run s).1) :
    (∃ e, y.1 = .error e) ∧ PV σ0 t y.2 := by
  obtain ⟨he, z1, h1, z2, h2, e⟩ := mem_hvf hy
  refine ⟨he, ?_⟩
  rw [e]
  have k1 : IK (PV σ0 t) (doMachineOp (Z := Unit) getFaultAddress) := ik_doMachineOp (fun _ _ h => h) _
  have k2 : IK (PV σ0 t) (asUser (Z := Unit) t (getRegister .errorRegister)) :=
    pv_of (SVK.sv_asUser' _ _) (by cfk_auto) (tp_asUser _ _ fun _ _ h => h) σ0
  exact k2 z1.2 (k1 s hs z1 h1) z2 h2

end

end Fl4Proofs.P3.SInvR.A11b
