/-
P3 (DESIGN.md §9): **the IPC caps' leaves at `J`** (XTopJointEntry's
`JPath` for the Endpoint, Notification and Reply caps): the caller's
restart, then FL4's `send_signal` / `do_reply_transfer` / `send_ipc`,
against the spec's, from `JAtZ` at the invocation to `JAt` after.

* `notifLeafJ`: the caller's restart at `J` (`JAtZ.restartJ`), the cap's
  notification one of `N` (`JAtZ.slotN`), then ScSignalJ's `SignalJHyp`
  (`signalJHyp_of`: from `SignalRestJHyp` [J], the bound thread
  `RunningVM`, VT-x; the platform's `MIN_BUDGET`
  [P]).
* `replyLeafJ`: the restart, then `replyXferJ`: `do_reply_transfer` at `J`
  where nothing happens (no thread on the reply, or one not blocked on it)
  and `reply_remove` (`JAtZ.replyRemoveJD`, the dead set kept, the receiver
  `Inactive`), then `replyRestNoScJ` for a receiver without SC or fault,
  the transfer any (XTopJointGrant's `JAtZ.xferAllJ`: a faulted replier,
  XTopJointFault; granted caps, `transfer_capsJ`; [P] `hAT`, `hmax`, `htu`,
  JEntryGlob's `tot`, `maxTU`, `tu`, for a timeout fault with an SC)
  (`ReplyRestNoSc`: no sporadic test, `JAtZ.xferAllJ` with no endpoint and
  badge 0, `JAtZ.runIJ` with `RelIfBound` vacuous, no tail),
  `replyRestSwJ` for a released SC (`JAtZ.switchJ`),
  `replyRestPostJ` for an active SC that is not released and no
  valid timeout handler (`Running` and the tail's `postpone` as one step,
  `JAtZ.runPostJ`), `replyRestFaultJ` for a faulted receiver (the fault
  reply, `faultBranchJ`: XTopJointFaultReply's `JAtZ.hfrJ`, the fault clear,
  `Inactive` or `Restart` by XTopJointStsI's `JAtZ.stsIJ`, then the tail:
  nothing, `JAtZ.switchJ`, or `Restart` and `postpone` as one step,
  `JAtZ.rstPostJ`; not the restart into a timeout-fault send,
  `ReplyFaultTmo`); all four after the sporadic unblock test
  (`JAtZ.replyUnblockJ`, XTopJointUnblock; `fl4ReplyRest_eq` splits FL4's
  code there), their cases read at the state after it; the other cases
  named: `ReplyRestTmo` (the tail's `handle_timeout`) by `replyRestTmoJ`
  (the transfer or fault reply, then `Running` / `Restart` and the
  timeout-fault send as one step, `RunTmoP`): `runTmoP_idle` when the
  timeout handler's endpoint is idle or sending (`TmoIdle`, the blocking
  send, XTopJointSendBlockG's `JAtZ.runTmoJ`), the hypothesis `hRT` when
  receivers wait on it (proved downstream by XTopJointFaultTmo's
  `runTmoP_recv`). The IPC-buffer facts at each `JAtZ` state: BufJ's
  `JAtZ.xferH`.
* `sendLeafJ`: the restart, then `sendXferJ`: `send_ipc` at `J` where
  nothing happens (a non-blocking send to an endpoint without receivers),
  the blocking send (XTopJointSendBlock's `JAtZ.sendBlockJ`; the caller in
  no ready queue, JEntryAt's `ctnq` [J]), the send to a receiver named
  (`JSendRestHyp` [W]).
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.JProducers
import Fl4Proofs.P3.IpcReply
import Fl4Proofs.P3.XTopJointXfer
import Fl4Proofs.P3.XTopJointFault
import Fl4Proofs.P3.XTopJointGrant
import Fl4Proofs.P3.XTopJointRunI
import Fl4Proofs.P3.XTopJointSwitch
import Fl4Proofs.P3.XTopJointRunPost
import Fl4Proofs.P3.XTopJointUnblock
import Fl4Proofs.P3.XTopJointFaultReply
import Fl4Proofs.P3.XTopJointSendBlock
import Fl4Proofs.P3.XTopJointSendBlockG
import Fl4Proofs.P3.AllDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The caller's restart in the spec is deterministic. -/
theorem restart_out_eq {σ σ1 σ2 : Fl4Spec.State Unit}
    (h1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h2 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ2)}, False)) : σ1 = σ2 := by
  have e := (Prod.mk.inj (h1.symm.trans h2)).1
  exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e)

set_option maxHeartbeats 4000000 in
/-- **The notification cap's leaf at `J`** (module docstring). -/
theorem notifLeafJ (hAT : P0.ArchTotal arI) (hW : SignalRestJHyp (L := L) arI AR H Cs)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← notification.send_signal st arI s1 ar p b
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1) := by
  intro _
  have hpN := (J.slotN hA hc).1
  obtain ⟨s1, σ1', x, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  rw [hs1]
  simp only [bind_ok]
  refine WP.spec_bind (signalJHyp_of hAT hW hmb Z Ac1 Lst1 D1 s1 ar σ1' p b J1 hpN) ?_
  rintro ⟨s2, a1⟩ ⟨σ', V', Ac', Lst', D', hsp, -, J'⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ((), σ'), by rw [hsp]; exact Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J'⟩


variable (st arI) in
/-- FL4's `do_reply_transfer` after `reply_remove` (the receiver `i` was
blocked on the reply): the sporadic unblock test, the transfer and
`Running` or the fault reply, then the tail. -/
def fl4ReplyRest (s1 : S) (a1 : A) (sender i : U64) (grant : Bool) : Result (S × A) := do
  let i2 ← obj.Tcb.sc st i s1
  let b1 ← sporadic.sc_sporadic st s1 i2
  let s2 ←
    if b1
    then
      do
      let i3 ← obj.Sc.cpu st i2 s1
      let i4 ← obj.node_get st s1 i3 layout.node.CUR_SC
      if i2 != i4
      then sporadic.unblock_check st s1 i2
      else ok s1
    else ok s1
  let fault_type ← obj.Tcb.fault_type st i s2
  let (s3, a2) ←
    if fault_type = fl4_abi.consts.fault.NullFault
    then
      do
      let s4 ←
        ipc.do_ipc_transfer st arI s2 a1 sender
          0#u64 0#u64 grant i
      let s5 ←
        sched.set_thread_state st s4 i sched.TS_RUNNING
      ok (s5, a1)
    else
      do
      let (restart, s4, a3) ←
        faults.handle_fault_reply st arI s2 a1 i
          sender
      let s5 ← faults.clear_fault st s4 i
      if restart
      then
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_RESTART
        ok (s6, a3)
      else
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_INACTIVE
        ok (s6, a3)
  let i3 ← obj.Tcb.sc st i s3
  let b2 ← obj.Sc.is_null i3
  if b2
  then ok (s3, a2)
  else
    let b3 ← sched.is_runnable st s3 i
    if b3
    then
      let b4 ← sporadic.ready st s3 i3
      if b4
      then
        let b5 ←
          sporadic.sufficient st arI s3 a2 i3
            0#u64
        if b5
        then
          let s4 ← sched.possible_switch_to st s3 i
          ok (s4, a2)
        else
          let b6 ← faults.valid_timeout_handler st s3 i
          if b6
          then
            if fault_type != fl4_abi.consts.fault.Timeout
            then
              let badge ← obj.Sc.badge st i3 s3
              faults.handle_timeout st arI s3 a2
                i (error.Fault.Timeout badge)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
      else
        let b5 ← faults.valid_timeout_handler st s3 i
        if b5
        then
          if fault_type != fl4_abi.consts.fault.Timeout
          then
            let badge ← obj.Sc.badge st i3 s3
            faults.handle_timeout st arI s3 a2 i
              (error.Fault.Timeout badge)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
        else let s4 ← sched.postpone st s3 i3
             ok (s4, a2)
    else ok (s3, a2)

variable (st arI) in
/-- `fl4ReplyRest` after the sporadic unblock test (`s2`). -/
def fl4ReplyRest2 (s2 : S) (a1 : A) (sender i : U64) (grant : Bool) : Result (S × A) := do
  let fault_type ← obj.Tcb.fault_type st i s2
  let (s3, a2) ←
    if fault_type = fl4_abi.consts.fault.NullFault
    then
      do
      let s4 ←
        ipc.do_ipc_transfer st arI s2 a1 sender
          0#u64 0#u64 grant i
      let s5 ←
        sched.set_thread_state st s4 i sched.TS_RUNNING
      ok (s5, a1)
    else
      do
      let (restart, s4, a3) ←
        faults.handle_fault_reply st arI s2 a1 i
          sender
      let s5 ← faults.clear_fault st s4 i
      if restart
      then
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_RESTART
        ok (s6, a3)
      else
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_INACTIVE
        ok (s6, a3)
  let i3 ← obj.Tcb.sc st i s3
  let b2 ← obj.Sc.is_null i3
  if b2
  then ok (s3, a2)
  else
    let b3 ← sched.is_runnable st s3 i
    if b3
    then
      let b4 ← sporadic.ready st s3 i3
      if b4
      then
        let b5 ←
          sporadic.sufficient st arI s3 a2 i3
            0#u64
        if b5
        then
          let s4 ← sched.possible_switch_to st s3 i
          ok (s4, a2)
        else
          let b6 ← faults.valid_timeout_handler st s3 i
          if b6
          then
            if fault_type != fl4_abi.consts.fault.Timeout
            then
              let badge ← obj.Sc.badge st i3 s3
              faults.handle_timeout st arI s3 a2
                i (error.Fault.Timeout badge)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
      else
        let b5 ← faults.valid_timeout_handler st s3 i
        if b5
        then
          if fault_type != fl4_abi.consts.fault.Timeout
          then
            let badge ← obj.Sc.badge st i3 s3
            faults.handle_timeout st arI s3 a2 i
              (error.Fault.Timeout badge)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
        else let s4 ← sched.postpone st s3 i3
             ok (s4, a2)
    else ok (s3, a2)

theorem fl4ReplyRest_eq (s1 : S) (a1 : A) (sender i : U64) (grant : Bool) :
    fl4ReplyRest st arI s1 a1 sender i grant = (do
      let i2 ← obj.Tcb.sc st i s1
      let b1 ← sporadic.sc_sporadic st s1 i2
      let s2 ←
        if b1
        then
          do
          let i3 ← obj.Sc.cpu st i2 s1
          let i4 ← obj.node_get st s1 i3 layout.node.CUR_SC
          if i2 != i4
          then sporadic.unblock_check st s1 i2
          else ok s1
        else ok s1
      fl4ReplyRest2 st arI s2 a1 sender i grant) := rfl

/-- The case of the rest of `do_reply_transfer` proved at `J`
(`replyRestNoScJ`), after `reply_remove` (`σ2`): the receiver `i` has no SC
and no fault (any transfer from the replier `ct`). -/
def ReplyRestNoSc (σ2 : Fl4Spec.State Unit) (ct i : U64) (g : Bool) : Prop :=
  ∃ xs xi, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧ xi.tcbSchedContext = none ∧
    xi.tcbFault = none

set_option maxHeartbeats 8000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestNoSc`**: FL4's
SC word of the receiver is 0 (`SchedSpec.tcb`), so no sporadic test and no
tail; its fault word 0 (`fault0`), so the transfer (`JAtZ.xferAllJ`, no
endpoint, badge 0) and `Running` (`JAtZ.runIJ`, `RelIfBound` with no SC);
the spec's outcome by `mem_doReplyTransfer` (unblock test on no SC the
identity, `specReplyTail_skip`). -/
theorem replyRestNoScJ
    (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hC : ReplyRestNoSc σ2 ct i g) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, hks, hki, hnsc, hfi⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨x0', hk0', hTR⟩ := hI.1.tcb i hiT
  rw [hki] at hk0'; cases hk0'
  unfold fl4ReplyRest2
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 := by rw [hft]; exact hTR.fault0.2 hfi
  rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb) (G : MdbGhost) (V : XVs)
      (Lst' : U64 → List U64),
      Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
      σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = none ∧
      JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst' D res.1 ar
        (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv)) ?_ ?_
  · refine WP.spec_bind (J2.xferAllJ hAT hmax (htu ar) hcT hiT hne hks hki g none 0#u64 0#u64 (Or.inr ⟨rfl, rfl⟩)) ?_
    rintro s4 ⟨σ3, htr, -, ⟨x3, hk3, hx3⟩, G, V, J3⟩
    rw [e0] at htr
    have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
    have hsc3 : x3.tcbSchedContext = none := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hnsc
    refine WP.spec_bind (J3.runIJ hiT hiD hk3 hs3 (relIfBound_noSc hk3 hsc3)) ?_
    rintro s5 ⟨Lst', J5⟩
    exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, G, V, Lst', htr, hk3, hsc3, J5⟩
  rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, G, V, Lst', htr, hk3, hsc3, J5⟩
  simp only at ha
  subst ha
  set σ5 := stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv with hσ5
  have hk5 : σ5.kheap i.bv = some (.tcb { x3 with tcbState := .running }) := by
    rw [hσ5, stsAct_kheap]; simp [updK]
  obtain ⟨Q5, R5, hc5, hsp5⟩ := J5.xtop.fin.1.1.1.lists
  obtain ⟨x5, hk5', -, -, hscw5, -⟩ := hsp5.tcb i hiT
  rw [hk5] at hk5'; cases hk5'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  have h3 : i3 = 0#u64 := by
    by_contra h
    have e := hscw5
    rw [← hi3, Notif.optRef_ne h] at e
    rw [hsc3] at e
    cases e
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  rw [hb2, if_pos (by simp [h3]), WP.spec_ok]
  have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
      Fl4Spec.setThreadState i.bv .running) σ2).1 := by
    rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
  have hz : ((), σ5) ∈ (specReplyTail i.bv xi.tcbFault σ5).1 := by
    rw [specReplyTail_skip hk5 (Or.inl hsc3)]; rfl
  exact ⟨((), σ5), mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) hz,
    _, _, _, _, _, _, J5⟩

/-- The second case of the rest of `do_reply_transfer` proved at `J`
(`replyRestSwJ`), after `reply_remove` (`σ2`): the receiver `i` has an
active SC `sp` that is released (ready and sufficient), no
fault. -/
def ReplyRestSw (σ2 : Fl4Spec.State Unit) (ct i : U64) (g : Bool) : Prop :=
  ∃ xs xi sp y n, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧
    xi.tcbSchedContext = some sp ∧ σ2.kheap sp = some (.schedContext y n) ∧
    Fl4Spec.scActive y = true ∧ Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧
    Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true ∧
    xi.tcbFault = none

set_option maxHeartbeats 16000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestSw`**: the
sporadic unblock test done (`σ0` to `σ2`), the transfer (`JAtZ.xferAllJ`), `Running` (`JAtZ.runIJ`, the SC
released: `RelIfBound`), then the tail's tests true (`ready_refines`,
`sufficient_refines`, MIN_BUDGET `hmb` [P]) and `possible_switch_to`
(`JAtZ.switchJ`). -/
theorem replyRestSwJ (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D) (hct2 : σ2.curThread = ct.bv)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hC : ReplyRestSw σ2 ct i g) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, sp, y, n, hks, hki, hxsc, hky, hya, hrdy, hsuf, hfi⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  have hnr2 : i.bv ∉ σ2.releaseQueue := fun hm => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J2.inv.rel _ hm
    rw [hki] at h1; cases h1; rw [hin] at h3; cases h3
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨x0', hk0', hTR⟩ := hI.1.tcb i hiT
  rw [hki] at hk0'; cases hk0'
  unfold fl4ReplyRest2
  obtain ⟨i2, hi2⟩ : ∃ i2 : U64, i2 = L.mem s2 (P1.scA i) := ⟨_, rfl⟩
  rw [← hi2] at hscw
  have h0 : i2 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero, hxsc] at hscw; cases hscw
  have esp : sp = i2.bv := by rw [Notif.optRef_ne h0, hxsc] at hscw; exact Option.some.inj hscw
  subst esp
  have hi2C : i2 ∈ Z.C := by rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h0)
  obtain ⟨y', n', hky', hy⟩ := hsp.scs i2 hi2C
  rw [hky] at hky'; cases hky'
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 := by rw [hft]; exact hTR.fault0.2 hfi
  rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb) (G : MdbGhost) (V : XVs)
      (Lst' : U64 → List U64),
      Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
      σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = some i2.bv ∧ x3.tcbFault = none ∧
      σ3.kheap i2.bv = σ2.kheap i2.bv ∧
      JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst' D res.1 ar
        (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv)) ?_ ?_
  · refine WP.spec_bind (J2.xferAllJ hAT hmax (htu ar) hcT hiT hne hks hki g none 0#u64 0#u64 (Or.inr ⟨rfl, rfl⟩)) ?_
    rintro s4 ⟨σ3, htr, hkp3, ⟨x3, hk3, hx3⟩, G, V, J3⟩
    rw [e0] at htr
    have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
      rw [htr]; exact Set.mem_singleton _
    have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
    have hsc3 : x3.tcbSchedContext = some i2.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hxsc
    have hf3 : x3.tcbFault = none := (congrArg Fl4Spec.Tcb.tcbFault hx3).trans hfi
    have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
    have hsd : ∀ sc, xs.tcbSchedContext = some sc → i2.bv ≠ sc := by
      rintro sc hsc rfl
      obtain ⟨y1, n1, hk1, hb1⟩ := J2.inv.back _ _ _ hks hsc
      obtain ⟨y2, n2, hk2, hb2⟩ := J2.inv.back _ _ _ hki hxsc
      rw [hk1] at hk2; cases hk2; rw [hb1] at hb2
      exact hne (P1.eq_of_bv (Option.some.inj hb2))
    have hkp3 : σ3.kheap i2.bv = σ2.kheap i2.bv := (hkp3 _ hti hsd).elim id
      (fun h => by obtain ⟨r, cs, cs', h1, _⟩ := h; rw [hky] at h1; cases h1)
    have hky3 : σ3.kheap i2.bv = some (.schedContext y n) := by rw [hkp3]; exact hky
    have htm3 : σ3.curTime = σ2.curTime := (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
    have hrel : RelIfBound σ3 i.bv := by
      intro x' scp y' n' h1 h2 h3 _ _
      rw [hk3] at h1; cases h1; rw [hsc3] at h2; cases h2; rw [hky3] at h3; cases h3
      exact ⟨by rw [htm3]; exact hrdy, hsuf⟩
    refine WP.spec_bind (J3.runIJ hiT hiD hk3 hs3 hrel) ?_
    rintro s5 ⟨Lst', J5⟩
    exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, G, V, Lst', htr, hk3, hsc3, hf3, hkp3, J5⟩
  rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, G, V, Lst', htr, hk3, hsc3, hf3, hkp3, J5⟩
  simp only at ha
  subst ha
  have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
    rw [htr]; exact Set.mem_singleton _
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ4 := updK σ3 i.bv (.tcb x5) with hσ4
  set σ5 := stsAct σ4 i.bv with hσ5
  have hrec : σ5 = { σ4 with schedulerAction := σ5.schedulerAction } := stsAct_rec σ4 i.bv
  have hk5 : σ5.kheap i.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp [hσ4, updK]
  have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
  have hky5 : σ5.kheap i2.bv = some (.schedContext y n) := by
    rw [hσ5, stsAct_kheap, hσ4]; simp only [updK, Function.update_of_ne hti]; rw [hkp3]; exact hky
  have htm5 : σ5.curTime = σ2.curTime := by
    rw [hrec]; exact (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
  have hct5 : σ5.curThread = ct.bv := by
    rw [hrec]; show σ3.curThread = _; rw [(dk_doIpcTransfer' _ _ _ _ _).ct mem3, hct2]
  have hnr5 : i.bv ∉ σ5.releaseQueue := fun hm => by
    rw [hrec] at hm
    exact hnr2 (RelQ.rq_doIpcTransfer' _ _ _ _ _ σ2 _ mem3 _ hm)
  have hsch : Fl4Spec.schedulable i.bv σ5 = true := schedulable_of hk5 hsc3 rfl hky5 hya hnr5
  have hti5 : i.bv ≠ σ5.idleThread := by
    intro e
    obtain ⟨yi, h1, -, h3, -⟩ := J5.act.2
    rw [← e, hk5] at h1; cases h1; cases h3
  have htc5 : i.bv ≠ σ5.curThread := by
    rw [hct5]; intro e; exact hne (P1.eq_of_bv e).symm
  obtain ⟨Q5, R5, hc5, hsp5⟩ := J5.xtop.fin.1.1.1.lists
  obtain ⟨x6, hk6, -, -, hscw5, -⟩ := hsp5.tcb i hiT
  rw [hk5] at hk6; cases hk6
  obtain ⟨x6', hk6', hTR5⟩ := (J5.xtop.irelK J5.ks J5.buf).1.tcb i hiT
  rw [hk5] at hk6'; cases hk6'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  rw [← hi3] at hscw5
  have h3 : i3 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hscw5; rw [hsc3] at hscw5; cases hscw5
  have e3 : i3 = i2 := by
    rw [Notif.optRef_ne h3] at hscw5; rw [hsc3] at hscw5
    exact P1.eq_of_bv (Option.some.inj hscw5).symm
  subst e3
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  rw [hb2, if_neg (by simp [h3])]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s5 i) ?_
  rintro b3 rfl
  have hrw : L.mem s5 (tStA i) = sched.TS_RUNNING := by
    apply UScalar.eq_of_val_eq; rw [hTR5.st]; unfold sched.TS_RUNNING; rfl
  rw [if_pos (by simp [hrw])]
  have hS5 := J5.xtop.fin.1.1.1
  have hne5 : y.scRefills ≠ [] := J5.inv.ne _ y n hky5 hya
  refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s5 σ5 hS5 hi2C hky5 hya) ?_
  rintro b4 hb4
  rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky5 hne5] at hb4
  have hb4' : b4 = Fl4Spec.refillReady σ5.curTime (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b4, σ5) ∈ q.1) hb4; simpa using this.symm
  rw [if_pos (by rw [hb4', htm5]; exact hrdy)]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s5 _ σ5 hS5 hi2C hky5 hya 0#u64 (hmb _)) ?_
  rintro b5 hb5
  rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky5 hne5] at hb5
  have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b5, σ5) ∈ q.1) hb5; simpa using this.symm
  rw [if_pos (by rw [hb5', e0]; exact hsuf)]
  refine WP.spec_bind (J5.switchJ hiT hti5 htc5 hsch) ?_
  rintro s6 ⟨σ6, hps, Lst6, J6⟩
  apply (WP.spec_ok _).2
  have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
      Fl4Spec.setThreadState i.bv .running) σ2).1 := by
    rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
  have hz : ((), σ6) ∈ (specReplyTail i.bv xi.tcbFault σ5).1 := by
    rw [specReplyTail_run hk5 hsc3 rfl hky5, if_pos ⟨by rw [htm5]; exact hrdy, hsuf⟩, hps]
    exact Set.mem_singleton _
  exact ⟨((), σ6), mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) hz,
    _, _, _, _, _, _, J6⟩

/-- The third case of the rest of `do_reply_transfer` proved at `J`
(`replyRestPostJ`), after `reply_remove` (`σ2`): the receiver `i` has an
active SC `sp` that is not released (not ready or not
sufficient) and no valid timeout handler, no fault.
The tail then postpones the SC. -/
def ReplyRestPost (σ2 : Fl4Spec.State Unit) (ct i : U64) (g : Bool) : Prop :=
  ∃ xs xi sp y n, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧
    xi.tcbSchedContext = some sp ∧ σ2.kheap sp = some (.schedContext y n) ∧
    Fl4Spec.scActive y = true ∧ ¬ (Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true) ∧
    Fl4Spec.isEpCap xi.tcbTimeoutHandler = false ∧
    xi.tcbFault = none

set_option maxHeartbeats 16000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestPost`**: the
sporadic unblock test done, the transfer (`JAtZ.xferAllJ`), then `Running` and the
tail's `postpone` as one step (`JAtZ.runPostJ`): the tail's reads at the
state between (its SC, runnable, the ready and sufficient tests not both
true, no valid timeout handler: `valid_timeout_handler_rel`) on `XTopAt`
there. -/
theorem replyRestPostJ (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D) (hct2 : σ2.curThread = ct.bv)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hC : ReplyRestPost σ2 ct i g) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, sp, y, n, hks, hki, hxsc, hky, hya, hnrel, hvt, hfi⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨x0', hk0', hTR⟩ := hI.1.tcb i hiT
  rw [hki] at hk0'; cases hk0'
  unfold fl4ReplyRest2
  obtain ⟨i2, hi2⟩ : ∃ i2 : U64, i2 = L.mem s2 (P1.scA i) := ⟨_, rfl⟩
  rw [← hi2] at hscw
  have h0 : i2 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero, hxsc] at hscw; cases hscw
  have esp : sp = i2.bv := by rw [Notif.optRef_ne h0, hxsc] at hscw; exact Option.some.inj hscw
  subst esp
  have hi2C : i2 ∈ Z.C := by rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h0)
  obtain ⟨y', n', hky', hy⟩ := hsp.scs i2 hi2C
  rw [hky] at hky'; cases hky'
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 := by rw [hft]; exact hTR.fault0.2 hfi
  rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
  refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb) (G : MdbGhost) (V : XVs),
      Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
      σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = some i2.bv ∧ x3.tcbFault = none ∧
      x3.tcbTimeoutHandler = xi.tcbTimeoutHandler ∧
      σ3.kheap i2.bv = σ2.kheap i2.bv ∧
      XTopAt (L := L) AR (Z.mv G V) res.1 ar
        (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv) ∧
      sched.postpone st res.1 i2 ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) i2.bv
          (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv) = ({((), σ7)}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst' D s7 ar σ7 ⦄) ?_ ?_
  · refine WP.spec_bind (J2.xferAllJ hAT hmax (htu ar) hcT hiT hne hks hki g none 0#u64 0#u64 (Or.inr ⟨rfl, rfl⟩)) ?_
    rintro s4 ⟨σ3, htr, hkp3, ⟨x3, hk3, hx3⟩, G, V, J3⟩
    rw [e0] at htr
    have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
      rw [htr]; exact Set.mem_singleton _
    have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
    have hsc3 : x3.tcbSchedContext = some i2.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hxsc
    have hf3 : x3.tcbFault = none := (congrArg Fl4Spec.Tcb.tcbFault hx3).trans hfi
    have hth3 : x3.tcbTimeoutHandler = xi.tcbTimeoutHandler := (congrArg Fl4Spec.Tcb.tcbTimeoutHandler hx3).trans rfl
    have hsd : ∀ sc, xs.tcbSchedContext = some sc → i2.bv ≠ sc := by
      rintro sc hsc rfl
      obtain ⟨y1, n1, hk1, hb1⟩ := J2.inv.back _ _ _ hks hsc
      obtain ⟨y2, n2, hk2, hb2⟩ := J2.inv.back _ _ _ hki hxsc
      rw [hk1] at hk2; cases hk2; rw [hb1] at hb2
      exact hne (P1.eq_of_bv (Option.some.inj hb2))
    have hkp3 : σ3.kheap i2.bv = σ2.kheap i2.bv := (hkp3 _ hti hsd).elim id
      (fun h => by obtain ⟨r, cs, cs', h1, _⟩ := h; rw [hky] at h1; cases h1)
    have hky3 : σ3.kheap i2.bv = some (.schedContext y n) := by rw [hkp3]; exact hky
    have htm3 : σ3.curTime = σ2.curTime := (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
    have hct3 : i.bv ≠ σ3.curThread := by
      rw [(dk_doIpcTransfer' _ _ _ _ _).ct mem3, hct2]; intro e; exact hne (P1.eq_of_bv e).symm
    refine WP.spec_bind (J3.runPostJ hiT hiD hk3 hs3 hct3 hi2C hsc3 hky3 hya (by rw [htm3]; exact hnrel)) ?_
    rintro s5 ⟨hX5, -, hpost⟩
    exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, G, V, htr, hk3, hsc3, hf3, hth3, hkp3, hX5, hpost⟩
  rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, G, V, htr, hk3, hsc3, hf3, hth3, hkp3, hX5, hpost⟩
  simp only at ha
  subst ha
  have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
    rw [htr]; exact Set.mem_singleton _
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ4 := updK σ3 i.bv (.tcb x5) with hσ4
  set σ5 := stsAct σ4 i.bv with hσ5
  have hrec : σ5 = { σ4 with schedulerAction := σ5.schedulerAction } := stsAct_rec σ4 i.bv
  have hk5 : σ5.kheap i.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp [hσ4, updK]
  have hky5 : σ5.kheap i2.bv = some (.schedContext y n) := by
    rw [hσ5, stsAct_kheap, hσ4]; simp only [updK, Function.update_of_ne hti]; rw [hkp3]; exact hky
  have htm5 : σ5.curTime = σ2.curTime := by
    rw [hrec]; exact (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
  have hS5 := hX5.fin.1.1.1
  obtain ⟨Q5, R5, hc5, hsp5⟩ := hS5.lists
  obtain ⟨x6, hk6, -, -, hscw5, -⟩ := hsp5.tcb i hiT
  rw [hk5] at hk6; cases hk6
  obtain ⟨x6', hk6', hTR5⟩ := hX5.ipc.tcb i hiT
  rw [hk5] at hk6'; cases hk6'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  rw [← hi3] at hscw5
  have h3 : i3 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hscw5; rw [hsc3] at hscw5; cases hscw5
  have e3 : i3 = i2 := by
    rw [Notif.optRef_ne h3] at hscw5; rw [hsc3] at hscw5
    exact P1.eq_of_bv (Option.some.inj hscw5).symm
  subst e3
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  rw [hb2, if_neg (by simp [h3])]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s5 i) ?_
  rintro b3 rfl
  have hrw : L.mem s5 (tStA i) = sched.TS_RUNNING := by
    apply UScalar.eq_of_val_eq; rw [hTR5.st]; unfold sched.TS_RUNNING; rfl
  rw [if_pos (by simp [hrw])]
  have hne5 : y.scRefills ≠ [] := J2.inv.ne _ y n hky hya
  -- the spec's outcome
  have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
      Fl4Spec.setThreadState i.bv .running) σ2).1 := by
    rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
  have hvt5 : Fl4Spec.isEpCap x5.tcbTimeoutHandler = false := by
    show Fl4Spec.isEpCap x3.tcbTimeoutHandler = false; rw [hth3]; exact hvt
  -- the timeout branch: no valid handler, so `postpone`
  have tmo : fl4ReplyTmo st arI i ft i3 s5 a2 ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
    unfold fl4ReplyTmo
    refine WP.spec_bind (valid_timeout_handler_rel s5 σ5 hX5.rel.2.1.1 (hX5.rel.tcbT hk5)) ?_
    rintro b5 ⟨-, x', hkx', hb5⟩
    rw [hk5] at hkx'; cases hkx'
    rw [if_neg (by rw [hb5, hvt5]; simp)]
    refine WP.spec_bind hpost ?_
    rintro s7 ⟨σ7, hpp, Lst7, J7⟩
    apply (WP.spec_ok _).2
    have hz : ((), σ7) ∈ (specReplyTail i.bv xi.tcbFault σ5).1 := by
      rw [specReplyTail_run hk5 hsc3 rfl hky5, if_neg (by rw [htm5]; exact hnrel)]
      unfold specReplyTmo
      rw [nd_bind_one (getTcb_eq hk5), if_neg (fun h => by rw [hvt5] at h; exact Bool.false_ne_true h.1), hpp]
      exact Set.mem_singleton _
    exact ⟨((), σ7), mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) hz,
      _, _, _, _, _, _, J7⟩
  unfold fl4ReplyTmo at tmo
  refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s5 σ5 hS5 hi2C hky5 hya) ?_
  rintro b4 hb4
  rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky5 hne5] at hb4
  have hb4' : b4 = Fl4Spec.refillReady σ5.curTime (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b4, σ5) ∈ q.1) hb4; simpa using this.symm
  by_cases hr4 : b4 = true
  · rw [if_pos hr4]
    refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s5 _ σ5 hS5 hi2C hky5 hya 0#u64 (hmb _)) ?_
    rintro b5 hb5
    rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky5 hne5] at hb5
    have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
      have := congrArg (fun q => (b5, σ5) ∈ q.1) hb5; simpa using this.symm
    have hr5 : ¬ b5 = true := fun h => hnrel ⟨by rw [← htm5, ← hb4']; exact hr4, by rw [← e0, ← hb5']; exact h⟩
    rw [if_neg hr5]
    exact tmo
  · rw [if_neg hr4]
    exact tmo

/-- The replier's message label of the fault reply (l4v `get_message_info`). -/
abbrev frLbl (xs : Fl4Spec.Tcb) : Fl4Spec.Data :=
  (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLabel

/-- The replier's message words of the fault reply (l4v `get_mrs`). -/
abbrev frMrs (xs : Fl4Spec.Tcb) (σ : Fl4Spec.State Unit) : List Fl4Spec.Word :=
  Endp.specMrs xs.tcbArch.tcbContext.userRegs (Endp.ipcBufOf false xs) σ.machineState.underlyingMemory
    (Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLength)

/-- The spec state after the fault reply (the receiver `i`'s user context
`x4`, its fault cleared, its new state). -/
abbrev frSt (σ2 : Fl4Spec.State Unit) (i : U64) (x4 : Fl4Spec.Tcb) (rst : Bool) : Fl4Spec.State Unit :=
  stsAct (updK (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })) i.bv
    (.tcb { ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
      tcbState := if rst then .restart else .inactive })) i.bv

set_option maxHeartbeats 8000000 in
/-- **FL4's fault reply at `J`** (`fl4FaultReply`): `handle_fault_reply`
(XTopJointFaultReply's `JAtZ.hfrJ`), `clear_fault` (`JAtZ.faultClearJ`),
then the receiver's new state by the given step `hQ` (for each outcome
`rst` of the spec's `handle_fault_reply`). The spec's fault reply ends at
`frSt`. -/
theorem faultBranchJ
    {s2 : S} {ar : A} {σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i : U64} (hne : ct ≠ i) (hiT : i ∈ Z.T) (hcT : ct ∈ Z.T) {xs xi : Fl4Spec.Tcb} {f : Fl4Spec.Fault}
    (hks : σ2.kheap ct.bv = some (.tcb xs)) (hki : σ2.kheap i.bv = some (.tcb xi)) (hfi : xi.tcbFault = some f)
    (hns : ∀ e d, xi.tcbState ≠ .blockedOnSend e d)
    (Q : Bool → S → Fl4Spec.State Unit → Prop)
    (hQ : ∀ (rst : Bool) (x4 : Fl4Spec.Tcb) (s5 : S) (V : XVs), x4 = { xi with tcbArch := x4.tcbArch } →
      JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s5 ar
        (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })) →
      sched.set_thread_state st s5 i (if rst then sched.TS_RESTART else sched.TS_INACTIVE) ⦃ s6 =>
        Q rst s6 (frSt σ2 i x4 rst) ⦄) :
    fl4FaultReply st arI s2 ar i ct ⦃ res => res.2 = ar ∧ ∃ (rst : Bool) (x4 : Fl4Spec.Tcb),
      x4 = { xi with tcbArch := x4.tcbArch } ∧
      Fl4Spec.handleFaultReply (Z := Unit) f i.bv (frLbl xs) (frMrs xs σ2) σ2 =
        ({(rst, updK σ2 i.bv (.tcb x4))}, False) ∧
      ((), frSt σ2 i x4 rst) ∈ (specFaultReply ct.bv i.bv f σ2).1 ∧ Q rst res.1 (frSt σ2 i x4 rst) ⦄ := by
  unfold fl4FaultReply
  refine WP.spec_bind (J2.hfrJ hiT hcT hne hki hks hfi) ?_
  rintro ⟨rst, s4, a3⟩ ⟨ha, x4, hhf, hpre, hx4, V4, J4⟩
  dsimp only at ha hhf hpre J4
  subst ha
  have hk4 : (updK σ2 i.bv (.tcb x4)).kheap i.bv = some (.tcb x4) := by simp [updK]
  have hk5 : (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap i.bv =
      some (.tcb { x4 with tcbFault := none }) := by simp [updK]
  have hmem : ∀ ts : Fl4Spec.ThreadState, ((), stsAct (updK (updK (updK σ2 i.bv (.tcb x4)) i.bv
      (.tcb { x4 with tcbFault := none })) i.bv (.tcb { ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := ts })) i.bv) ∈ ((Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) i.bv >>=
      fun _ => Fl4Spec.setThreadState (Z := Unit) i.bv ts) (updK σ2 i.bv (.tcb x4))).1 := by
    intro ts
    rw [nd_bind_one (Notif.threadSet_eq _ hk4), Notif.setThreadState_eq _ hk5]; rfl
  unfold faults.clear_fault
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s5, hs5⟩
  have e5 : s5 = L.wr s4 (tFaultA i) 0#u64 := by rw [hs5]; unfold fl4_abi.consts.fault.NullFault; rfl
  subst e5
  obtain ⟨V5, J5⟩ := J4.faultClearJ hiT hk4 fun e d h => hns e d ((congrArg Fl4Spec.Tcb.tcbState hx4).symm.trans h)
  have key := hQ rst x4 _ V5 hx4 J5
  cases rst
  · simp only [Bool.false_eq_true, ↓reduceIte] at key hpre ⊢
    refine WP.spec_bind key ?_
    intro s6 hq
    exact (WP.spec_ok _).2 ⟨rfl, false, x4, hx4, hhf, hpre _ (hmem _), hq⟩
  · simp only [eq_self_iff_true, if_true, ↓reduceIte] at key hpre ⊢
    refine WP.spec_bind key ?_
    intro s6 hq
    exact (WP.spec_ok _).2 ⟨rfl, true, x4, hx4, hhf, hpre _ (hmem _), hq⟩

/-- The case of a faulted receiver of `ReplyRestTmo`: the fault reply
restarts it, its SC is bound and not released, it has a valid timeout
handler and its fault is no timeout fault (the tail then sends a timeout
fault, `handle_timeout`). -/
def ReplyFaultTmo (σ : Fl4Spec.State Unit) (xi : Fl4Spec.Tcb) (f : Fl4Spec.Fault) : Prop :=
  ∃ sp y n, xi.tcbSchedContext = some sp ∧ σ.kheap sp = some (.schedContext y n) ∧
    ¬ (Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true) ∧
    Fl4Spec.isEpCap xi.tcbTimeoutHandler = true ∧ Fl4Spec.isTimeoutFault f = false

/-- The fourth case of the rest of `do_reply_transfer` proved at `J`
(`replyRestFaultJ`), after `reply_remove` and the unblock test (`σ2`): the
receiver `i` has a fault, and a restart by its fault reply (the spec's
`handle_fault_reply` returning true) does not lead into `ReplyFaultTmo`. -/
def ReplyRestFault (σ2 : Fl4Spec.State Unit) (ct i : U64) : Prop :=
  ∃ xs xi f, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧ xi.tcbFault = some f ∧
    ∀ σ', Fl4Spec.handleFaultReply (Z := Unit) f i.bv (frLbl xs) (frMrs xs σ2) σ2 = ({(true, σ')}, False) →
      ¬ ReplyFaultTmo σ2 xi f

set_option maxHeartbeats 32000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestFault`**: FL4's
fault word of the receiver is not 0 (`fault0`), so the fault reply
(`faultBranchJ`), the new state `Inactive` or `Restart` by `JAtZ.stsIJ`
(XTopJointStsI; `RelIfBound` with no SC or a released one), then the tail:
nothing for no SC or `Inactive`; `possible_switch_to` (`JAtZ.switchJ`) for a
released SC; for an SC not released, `Restart` and `postpone` as one step
(`JAtZ.rstPostJ`), the timeout handler invalid or the fault a timeout
(`faultT`: FL4's fault word 5) by `ReplyRestFault`. The spec's outcome by
`mem_doReplyTransfer` (the fault branch). -/
theorem replyRestFaultJ (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D) (hct2 : σ2.curThread = ct.bv)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hact : ∀ q y n, σ2.kheap q = some (.schedContext y n) → y.scTcb = some i.bv → Fl4Spec.scActive y = true)
    (hC : ReplyRestFault σ2 ct i) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, f, hks, hki, hfi, hnt⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  have hnr2 : i.bv ∉ σ2.releaseQueue := fun hm => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J2.inv.rel _ hm
    rw [hki] at h1; cases h1; rw [hin] at h3; cases h3
  have hxr := hI.1.toE.at_tcb hiT hki
  obtain ⟨Q0, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  unfold fl4ReplyRest2
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
    intro e
    have h := hxr.fault0.1 (by rw [← hft, e]; unfold fl4_abi.consts.fault.NullFault; rfl)
    rw [hfi] at h; cases h
  have hftT : ft = fl4_abi.consts.fault.Timeout ↔ Fl4Spec.isTimeoutFault f = true := by
    rw [hft, show fl4_abi.consts.fault.Timeout = 5#u64 by unfold fl4_abi.consts.fault.Timeout; rfl, hxr.faultT, hfi]
    cases f <;> simp [Fl4Spec.isTimeoutFault]
  rw [if_neg hft0]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  -- the receiver's new state, `J` after it (no SC, or a released one, or `Inactive`)
  have stsQ : ∀ (rst : Bool) (x4 : Fl4Spec.Tcb) (s5 : S) (V : XVs), x4 = { xi with tcbArch := x4.tcbArch } →
      JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s5 ar
        (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })) →
      (rst = true → RelIfBound (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })) i.bv) →
      sched.set_thread_state st s5 i (if rst then sched.TS_RESTART else sched.TS_INACTIVE) ⦃ s6 =>
        ∃ (V' : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst' D s6 ar
          (frSt σ2 i x4 rst) ⦄ := by
    intro rst x4 s5 V hx4 J5 hrel
    have hk5 : (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap i.bv =
        some (.tcb { x4 with tcbFault := none }) := by simp [updK]
    have hrs : ({ x4 with tcbFault := none } : Fl4Spec.Tcb).tcbState = .inactive := by
      have h := congrArg Fl4Spec.Tcb.tcbState hx4; exact h.trans hin
    obtain ⟨x5, hk5', hTR5⟩ := (J5.xtop.irelK J5.ks J5.buf).1.tcb i hiT
    rw [hk5] at hk5'; cases hk5'
    have hr0 : L.mem s5 (P1.stA i) = sched.TS_INACTIVE := by
      apply UScalar.eq_of_val_eq
      rw [P1.stA_eq, ← tStA_eq, hTR5.st, hrs]; unfold sched.TS_INACTIVE; rfl
    have htH : i ∈ P1.Heap.tcbs H := J5.zH.1 i hiT
    cases rst
    · refine WP.spec_mono (J5.stsIJ hiT hiD hk5 hrs .inactive (by decide) sched.TS_INACTIVE
        (by unfold sched.TS_INACTIVE; rfl) (fun h => by
          rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h)
        (P1.sched.set_thread_state.inactive_blkI (Es := P1.EH H) s5 i J5.blk htH hr0)) ?_
      rintro s6 ⟨Lst', J6⟩
      exact ⟨V, Lst', J6⟩
    · refine WP.spec_mono (J5.stsIJ hiT hiD hk5 hrs .restart (by decide) sched.TS_RESTART
        (by unfold sched.TS_RESTART; rfl) (fun _ => hrel rfl)
        (P1.sched.set_thread_state.restart_blkI (Es := P1.EH H) s5 i J5.blk htH hr0)) ?_
      rintro s6 ⟨Lst', J6⟩
      exact ⟨V, Lst', J6⟩
  -- the spec's facts at the state after the fault reply
  have hk6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), (frSt σ2 i x4 rst).kheap i.bv = some (.tcb { ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
      tcbState := if rst then .restart else .inactive }) := by
    intro x4 rst; simp [frSt, stsAct_kheap, updK]
  have hkp6 : ∀ x4 rst q, q ≠ i.bv → (frSt σ2 i x4 rst).kheap q = σ2.kheap q := by
    intro x4 rst q hq; simp [frSt, stsAct_kheap, updK, hq]
  have hrec6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), frSt σ2 i x4 rst = { (updK (updK (updK σ2 i.bv (.tcb x4)) i.bv
      (.tcb { x4 with tcbFault := none })) i.bv (.tcb { ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := if rst then .restart else .inactive })) with
      schedulerAction := (frSt σ2 i x4 rst).schedulerAction } := fun x4 rst => stsAct_rec _ _
  have htm6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), (frSt σ2 i x4 rst).curTime = σ2.curTime := fun x4 rst => by rw [hrec6]; rfl
  have hct6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), (frSt σ2 i x4 rst).curThread = ct.bv := fun x4 rst => by rw [hrec6]; exact hct2
  have hrq6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), (frSt σ2 i x4 rst).releaseQueue = σ2.releaseQueue := fun x4 rst => by rw [hrec6]; rfl
  have hsc6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), x4 = { xi with tcbArch := x4.tcbArch } →
      ({ ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := if rst then Fl4Spec.ThreadState.restart else .inactive } : Fl4Spec.Tcb).tcbSchedContext =
        xi.tcbSchedContext := by
    intro x4 rst hx4; have h := congrArg Fl4Spec.Tcb.tcbSchedContext hx4; exact h
  have hth6 : ∀ (x4 : Fl4Spec.Tcb) (rst : Bool), x4 = { xi with tcbArch := x4.tcbArch } →
      ({ ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := if rst then Fl4Spec.ThreadState.restart else .inactive } : Fl4Spec.Tcb).tcbTimeoutHandler =
        xi.tcbTimeoutHandler := by
    intro x4 rst hx4; have h := congrArg Fl4Spec.Tcb.tcbTimeoutHandler hx4; exact h
  have fin : ∀ (rst : Bool) (x4 : Fl4Spec.Tcb) (z : Unit × Fl4Spec.State Unit) (s' : S) (a' : A),
      ((), frSt σ2 i x4 rst) ∈ (specFaultReply ct.bv i.bv f σ2).1 →
      z ∈ (specReplyTail i.bv xi.tcbFault (frSt σ2 i x4 rst)).1 → JAt (L := L) arI AR s' a' z.2 →
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1, JAt (L := L) arI AR s' a' z.2 :=
    fun rst x4 z s' a' hz1 hz hJ => ⟨z, mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inr ⟨f, hfi, hz1⟩) hz, hJ⟩
  -- the receiver's SC word, and whether its SC is released
  obtain ⟨i2, hi2⟩ : ∃ i2 : U64, i2 = L.mem s2 (P1.scA i) := ⟨_, rfl⟩
  rw [← hi2] at hscw
  set relC : Prop := ∀ sp y n, xi.tcbSchedContext = some sp → σ2.kheap sp = some (.schedContext y n) →
    Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧ Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true
    with hrelC
  -- the step after the fault reply: `Inactive`, `J`; `Restart`, `J` when `relC`, otherwise with the tail's `postpone`
  refine WP.spec_bind (faultBranchJ J2 hne hiT hcT hks hki hfi (fun e d h => by rw [hin] at h; cases h)
    (fun rst s σ => (rst = false → ∃ (V' : XVs) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst' D s ar σ) ∧
      (rst = true → ∃ V' : XVs, XTopAt (L := L) AR (Z.mv Z.G V') s ar σ ∧
        (relC → ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst' D s ar σ) ∧
        (¬ relC → sched.postpone st s i2 ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) i2.bv σ = ({((), σ7)}, False) ∧
          ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst' D s7 ar σ7 ⦄)))
    ?_) ?_
  · intro rst x4 s5 V hx4 J5
    have hk5 : (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap i.bv =
        some (.tcb { x4 with tcbFault := none }) := by simp [updK]
    have hsc5 : ({ x4 with tcbFault := none } : Fl4Spec.Tcb).tcbSchedContext = xi.tcbSchedContext := by
      have h := congrArg Fl4Spec.Tcb.tcbSchedContext hx4; exact h
    cases rst
    · refine WP.spec_mono (stsQ false x4 s5 V hx4 J5 (fun h => absurd h Bool.false_ne_true)) ?_
      intro s6 h6
      exact ⟨fun _ => h6, fun h => absurd h Bool.false_ne_true⟩
    · by_cases hR : relC
      · have hrel : RelIfBound (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })) i.bv := by
          intro x' scp y' n' h1 h2 h3 _ _
          rw [hk5] at h1; cases h1
          have hsp' : xi.tcbSchedContext = some scp := hsc5.symm.trans h2
          have hti' : scp ≠ i.bv := fun e => by
            rw [e] at h3; simp [updK] at h3
          have h3' : σ2.kheap scp = some (.schedContext y' n') := by simpa [updK, hti'] using h3
          exact hR scp y' n' hsp' h3'
        refine WP.spec_mono (stsQ true x4 s5 V hx4 J5 (fun _ => hrel)) ?_
        rintro s6 ⟨V', Lst', J6⟩
        exact ⟨fun h => absurd h.symm Bool.false_ne_true, fun _ => ⟨V', J6.xtop, fun _ => ⟨Lst', J6⟩,
          fun h => absurd hR h⟩⟩
      · -- the SC is bound and not released: `Restart` and `postpone` as one step
        have hR' : ∃ sp y n, xi.tcbSchedContext = some sp ∧ σ2.kheap sp = some (.schedContext y n) ∧
            ¬ (Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧
              Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true) := by
          by_contra hc
          exact hR fun sp y n h1 h2 => by
            by_contra h3; exact hc ⟨sp, y, n, h1, h2, h3⟩
        obtain ⟨sp, y, n, hxsc, hky, hnrel⟩ := hR'
        have h0 : i2 ≠ 0#u64 := by
          intro e; rw [e, optRef_zero, hxsc] at hscw; cases hscw
        have esp : sp = i2.bv := by rw [Notif.optRef_ne h0, hxsc] at hscw; exact Option.some.inj hscw
        subst esp
        have hi2C : i2 ∈ Z.C := by rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h0)
        obtain ⟨y0, n0, hky0, hyt⟩ := J2.inv.back _ _ _ hki hxsc
        rw [hky] at hky0; cases hky0
        have hya := hact _ y n hky hyt
        have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
        have hky5 : (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap i2.bv =
            some (.schedContext y n) := by simp [updK, hti, hky]
        have hrs : ({ x4 with tcbFault := none } : Fl4Spec.Tcb).tcbState = .inactive := by
          have h := congrArg Fl4Spec.Tcb.tcbState hx4; exact h.trans hin
        have htc5 : i.bv ≠ (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).curThread := by
          show i.bv ≠ σ2.curThread
          rw [hct2]; intro e; exact hne (P1.eq_of_bv e).symm
        refine WP.spec_mono (J5.rstPostJ hiT hiD hk5 hrs htc5 hi2C (hsc5.trans hxsc) hky5 hya hnrel) ?_
        rintro s6 ⟨hX6, -, hpost⟩
        exact ⟨fun h => absurd h.symm Bool.false_ne_true, fun _ => ⟨V, hX6, fun h => absurd h hR, fun _ => hpost⟩⟩
  rintro ⟨s6, a2⟩ ⟨ha, rst, x4, hx4, hhf, hz1, hq⟩
  dsimp only at ha hq
  subst ha
  -- the tail's reads at the state after the fault reply
  have hX6 : ∃ V6 : XVs, XTopAt (L := L) AR (Z.mv Z.G V6) s6 a2 (frSt σ2 i x4 rst) := by
    cases rst
    · obtain ⟨V6, _, J6⟩ := hq.1 rfl; exact ⟨V6, J6.xtop⟩
    · obtain ⟨V6, hX, -⟩ := hq.2 rfl; exact ⟨V6, hX⟩
  obtain ⟨V6, hX6⟩ := hX6
  have hS6 := hX6.fin.1.1.1
  obtain ⟨Q6, R6, hc6, hsp6⟩ := hS6.lists
  obtain ⟨x6, hk6', -, -, hscw6, -⟩ := hsp6.tcb i hiT
  rw [hk6 x4 rst] at hk6'; cases hk6'
  obtain ⟨x6', hk6'', hTR6⟩ := hX6.ipc.tcb i hiT
  rw [hk6 x4 rst] at hk6''; cases hk6''
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  by_cases h3 : i3 = 0#u64
  · -- no SC: nothing
    rw [hb2, if_pos (by simp [h3]), WP.spec_ok]
    have hn : xi.tcbSchedContext = none := by
      have e := hscw6
      rw [← hi3, h3, optRef_zero] at e
      exact (hsc6 x4 rst hx4).symm.trans e
    have hJ6 : JAt (L := L) arI AR s6 a2 (frSt σ2 i x4 rst) := by
      cases rst
      · obtain ⟨V', Lst', J6⟩ := hq.1 rfl; exact ⟨_, _, _, _, _, _, J6⟩
      · obtain ⟨V', -, hJ, -⟩ := hq.2 rfl
        obtain ⟨Lst', J6⟩ := hJ (fun sp y n h => by rw [hn] at h; cases h)
        exact ⟨_, _, _, _, _, _, J6⟩
    exact fin rst x4 ((), frSt σ2 i x4 rst) s6 a2 hz1
      (by rw [specReplyTail_skip (hk6 x4 rst) (Or.inl ((hsc6 x4 rst hx4).trans hn))]; rfl) hJ6
  rw [hb2, if_neg (by simp [h3])]
  have e3 : xi.tcbSchedContext = some i3.bv := by
    have e := hscw6
    rw [← hi3, Notif.optRef_ne h3] at e
    exact (hsc6 x4 rst hx4).symm.trans e
  have hi23 : i3 = i2 := by
    rw [Notif.optRef_ne (fun e => by rw [e, optRef_zero, e3] at hscw; cases hscw), e3] at hscw
    exact P1.eq_of_bv (Option.some.inj hscw)
  subst hi23
  have hi2C : i3 ∈ Z.C := by
    rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h3)
  obtain ⟨y, n, hky, hyt⟩ := J2.inv.back _ _ _ hki e3
  have hya := hact _ y n hky hyt
  have hti : i3.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
  have hky6 : (frSt σ2 i x4 rst).kheap i3.bv = some (.schedContext y n) := by rw [hkp6 x4 rst _ hti]; exact hky
  refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s6 i) ?_
  rintro b3 rfl
  cases rst
  · -- `Inactive`: not runnable, nothing
    have hrw : L.mem s6 (tStA i) = sched.TS_INACTIVE := by
      apply UScalar.eq_of_val_eq; rw [hTR6.st]; unfold sched.TS_INACTIVE; rfl
    rw [if_neg (by rw [hrw]; unfold sched.TS_INACTIVE sched.TS_RUNNING sched.TS_RESTART sched.TS_RUNNING_VM; decide),
      WP.spec_ok]
    obtain ⟨V', Lst', J6⟩ := hq.1 rfl
    exact fin false x4 ((), frSt σ2 i x4 false) s6 a2 hz1 (by rw [specReplyTail_skip (hk6 x4 false) (Or.inr rfl)]; rfl)
      ⟨_, _, _, _, _, _, J6⟩
  -- `Restart`: runnable
  have hrw : L.mem s6 (tStA i) = sched.TS_RESTART := by
    apply UScalar.eq_of_val_eq; rw [hTR6.st]; unfold sched.TS_RESTART; rfl
  rw [if_pos (by rw [hrw]; simp)]
  obtain ⟨V', hX6', hJR, hpost⟩ := hq.2 rfl
  have hne6 : y.scRefills ≠ [] := J2.inv.ne _ y n hky hya
  have hsc6' := hsc6 x4 true hx4
  refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s6 (frSt σ2 i x4 true) hS6 hi2C hky6 hya) ?_
  rintro b4 hb4
  rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky6 hne6] at hb4
  have hb4' : b4 = Fl4Spec.refillReady (frSt σ2 i x4 true).curTime (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b4, frSt σ2 i x4 true) ∈ q.1) hb4; simpa using this.symm
  by_cases hrl : Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true
  · -- released: `possible_switch_to`
    have hR : relC := fun sp y' n' h1 h2 => by
      rw [e3] at h1; cases h1; rw [hky] at h2; cases h2; exact hrl
    obtain ⟨Lst', J6⟩ := hJR hR
    rw [if_pos (by rw [hb4', htm6]; exact hrl.1)]
    refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s6 _ (frSt σ2 i x4 true) hS6 hi2C hky6 hya 0#u64 (hmb _)) ?_
    rintro b5 hb5
    rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky6 hne6] at hb5
    have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
      have := congrArg (fun q => (b5, frSt σ2 i x4 true) ∈ q.1) hb5; simpa using this.symm
    rw [if_pos (by rw [hb5', e0]; exact hrl.2)]
    have hnr6 : i.bv ∉ (frSt σ2 i x4 true).releaseQueue := by rw [hrq6]; exact hnr2
    have hsch : Fl4Spec.schedulable i.bv (frSt σ2 i x4 true) = true :=
      schedulable_of (hk6 x4 true) (hsc6'.trans e3) rfl hky6 hya hnr6
    have hti6 : i.bv ≠ (frSt σ2 i x4 true).idleThread := by
      intro e
      obtain ⟨yi, h1, -, h3, -⟩ := J6.act.2
      rw [← e, hk6 x4 true] at h1; cases h1; cases h3
    have htc6 : i.bv ≠ (frSt σ2 i x4 true).curThread := by
      rw [hct6]; intro e; exact hne (P1.eq_of_bv e).symm
    refine WP.spec_bind (J6.switchJ hiT hti6 htc6 hsch) ?_
    rintro s7 ⟨σ7, hps, Lst7, J7⟩
    apply (WP.spec_ok _).2
    refine fin true x4 ((), σ7) s7 a2 hz1 ?_ ⟨_, _, _, _, _, _, J7⟩
    rw [specReplyTail_run (hk6 x4 true) (hsc6'.trans e3) rfl hky6, if_pos ⟨by rw [htm6]; exact hrl.1, hrl.2⟩, hps]
    exact Set.mem_singleton _
  · -- not released: `postpone` (no valid timeout handler, or a timeout fault)
    have hnR : ¬ relC := fun h => hrl (h _ _ _ e3 hky)
    have hnot : ¬ (Fl4Spec.isEpCap xi.tcbTimeoutHandler = true ∧ Fl4Spec.isTimeoutFault f = false) :=
      fun ⟨h1, h2⟩ => hnt _ hhf ⟨i3.bv, y, n, e3, hky, hrl, h1, h2⟩
    have hpost' := hpost hnR
    have tmo : fl4ReplyTmo st arI i ft i3 s6 a2 ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
        JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
      unfold fl4ReplyTmo
      refine WP.spec_bind (valid_timeout_handler_rel s6 (frSt σ2 i x4 true) hX6.rel.2.1.1
        (hX6.rel.tcbT (hk6 x4 true))) ?_
      rintro b5 ⟨-, x', hkx', hb5⟩
      rw [hk6 x4 true] at hkx'; cases hkx'
      have hb5x : b5 = Fl4Spec.isEpCap xi.tcbTimeoutHandler :=
        hb5.trans (congrArg Fl4Spec.isEpCap (hth6 x4 true hx4))
      have post : (do let s4 ← sched.postpone st s6 i3; ok (s4, a2)) ⦃ res =>
          ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1, JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
        refine WP.spec_bind hpost' ?_
        rintro s7 ⟨σ7, hpp, Lst7, J7⟩
        apply (WP.spec_ok _).2
        refine fin true x4 ((), σ7) s7 a2 hz1 ?_ ⟨_, _, _, _, _, _, J7⟩
        rw [specReplyTail_run (hk6 x4 true) (hsc6'.trans e3) rfl hky6, if_neg (by rw [htm6]; exact hrl)]
        unfold specReplyTmo
        rw [nd_bind_one (getTcb_eq (hk6 x4 true)), if_neg (fun h => hnot ⟨by rw [← hth6 x4 true hx4]; exact h.1,
          by have h2 := h.2; rw [hfi] at h2; simpa using h2⟩), hpp]
        exact Set.mem_singleton _
      by_cases hb : b5 = true
      · rw [if_pos hb]
        have htf : Fl4Spec.isTimeoutFault f = true := by
          by_contra h; exact hnot ⟨by rw [← hb5x]; exact hb, by simpa using h⟩
        rw [if_neg (by simp [hftT.2 htf])]
        exact post
      · rw [if_neg hb]
        exact post
    unfold fl4ReplyTmo at tmo
    by_cases hr4 : b4 = true
    · rw [if_pos hr4]
      refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s6 _ (frSt σ2 i x4 true) hS6 hi2C hky6 hya 0#u64 (hmb _)) ?_
      rintro b5 hb5
      rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky6 hne6] at hb5
      have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
        have := congrArg (fun q => (b5, frSt σ2 i x4 true) ∈ q.1) hb5; simpa using this.symm
      have hr5 : ¬ b5 = true := fun h => hrl ⟨by rw [← htm6 x4 true, ← hb4']; exact hr4, by rw [← e0, ← hb5']; exact h⟩
      rw [if_neg hr5]
      exact tmo
    · rw [if_neg hr4]
      exact tmo

/-- **The case of the rest of `do_reply_transfer` with the tail's `handle_timeout`**
(at `σ3`, after `reply_remove` and the unblock test): the receiver `i`'s SC
is bound, active and not released, it has a valid timeout handler, and it
either has no fault (the transfer, then `Running`) or a fault `f` other than
a timeout whose fault reply restarts it (`Restart`, `ReplyFaultTmo`); the
tail then calls `handle_timeout`. Every other case is proved
(`replyRestNoScJ`, `replyRestSwJ`, `replyRestPostJ`, `replyRestFaultJ`;
`replyXferJ` shows the split complete). -/
def ReplyRestTmo (σ3 : Fl4Spec.State Unit) (ct i : U64) : Prop :=
  ∃ xi sp y n, σ3.kheap i.bv = some (.tcb xi) ∧ xi.tcbSchedContext = some sp ∧
    σ3.kheap sp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true ∧
    ¬ (Fl4Spec.refillReady σ3.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true) ∧
    Fl4Spec.isEpCap xi.tcbTimeoutHandler = true ∧
    (xi.tcbFault = none ∨ ∃ xs f σ', σ3.kheap ct.bv = some (.tcb xs) ∧ xi.tcbFault = some f ∧
      Fl4Spec.isTimeoutFault f = false ∧
      Fl4Spec.handleFaultReply (Z := Unit) f i.bv (frLbl xs) (frMrs xs σ3) σ3 = ({(true, σ')}, False))

/-- **The receiver's timeout handler endpoint takes a blocking send** (at
`σ`): the receiver `i`'s timeout handler cap names an endpoint that is idle
or has senders (`CanBlock false`); `TmoEp` for any class of endpoints
(`replyRestTmoJ` for each class given its `RunTmoP`). -/
def TmoIdle (σ : Fl4Spec.State Unit) (i : U64) : Prop :=
  ∃ xi ep bd r xe, σ.kheap i.bv = some (.tcb xi) ∧ xi.tcbTimeoutHandler = .endpointCap ep bd r ∧
    σ.kheap ep = some (.endpoint xe) ∧ Endp.CanBlock false xe

/-- `TmoIdle` for a class `EC` of handler endpoints (`TmoIdle` is
`TmoEp (CanBlock false)`; receivers waiting: `TmoEp (¬ CanBlock false)`). -/
def TmoEp (EC : Fl4Spec.Endpoint → Prop) (σ : Fl4Spec.State Unit) (i : U64) : Prop :=
  ∃ xi ep bd r xe, σ.kheap i.bv = some (.tcb xi) ∧ xi.tcbTimeoutHandler = .endpointCap ep bd r ∧
    σ.kheap ep = some (.endpoint xe) ∧ EC xe

variable (arI) in
/-- **`Running` or `Restart` of an `Inactive` thread other than the current
one, then its `handle_timeout`, at `J`, for a timeout handler endpoint in the
class `EC`** (the statement of XTopJointSendBlockG's `JAtZ.runTmoJ`, ending
at `JAt`): `runTmoP_idle` (idle or sending, `JAtZ.runTmoJ`) here,
XTopJointFaultTmo's `runTmoP_recv` (receivers waiting) downstream, for the
`J` states whose typed heap is `Z0`'s. `hcr`: the current thread runnable. -/
def RunTmoP (AR : A → Fl4Spec.Cr3 → Prop) (Z0 : XSets) (EC : Fl4Spec.Endpoint → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = Z0.th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    (∃ xc, σ.kheap σ.curThread = some (.tcb xc) ∧ Fl4Spec.runnable xc.tcbState = true) →
    ∀ (t : U64), t ∈ Z.T → t ∉ D → ∀ (x : Fl4Spec.Tcb), σ.kheap t.bv = some (.tcb x) → x.tcbState = .inactive →
    t.bv ≠ σ.curThread → ∀ (sc : U64), sc ∈ Z.C → x.tcbSchedContext = some sc.bv →
    ∀ (y : Fl4Spec.SchedContext) (n : Nat), σ.kheap sc.bv = some (.schedContext y n) → Fl4Spec.scActive y = true →
    ∀ (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights), x.tcbTimeoutHandler = .endpointCap p bd r →
    (∀ xe, σ.kheap p = some (.endpoint xe) → EC xe) →
    ∀ (ts : Fl4Spec.ThreadState), Fl4Spec.runnable ts = true → tsCode ts < 3 → ∀ (v : U64), v.val = tsCode ts →
    sched.set_thread_state st s t v ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄ →
    sched.set_thread_state st s t v ⦃ s6 =>
      XTopAt (L := L) AR Z s6 a (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6
        (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      ∀ b : U64, faults.handle_timeout st arI s6 a t (error.Fault.Timeout b) ⦃ res => ∃ z ∈
        (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv)
          (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv)).1,
        JAt (L := L) arI AR res.1 res.2 z.2 ⦄ ⦄

/-- `RunTmoP` for an idle or sending handler endpoint: XTopJointSendBlockG's
`JAtZ.runTmoJ`. -/
theorem runTmoP_idle (Z0 : XSets) : RunTmoP (L := L) arI AR Z0 (Endp.CanBlock false) :=
  fun _ _ _ _ _ _ _ _ _ _ J _ _ ht htD _ hk hrs htc _ hsc hxsc _ _ hky hya _ _ _ hth hcb ts hrun hts v hv hB =>
    WP.spec_mono (J.runTmoJ ht htD hk hrs htc hsc hxsc hky hya hth hcb ts hrun hts v hv hB) fun _ ⟨h1, h2, h3⟩ =>
      ⟨h1, h2, fun b => WP.spec_mono (h3 b) fun _ ⟨z, hz, _, _, J'⟩ => ⟨z, hz, _, _, _, _, _, _, J'⟩⟩

set_option maxHeartbeats 32000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestTmo` with an
idle or sending timeout handler endpoint (`TmoIdle`)**: the transfer
(`JAtZ.xferAllJ`) or the fault reply (`faultBranchJ`), then `Running` /
`Restart` and the tail's `handle_timeout` as one step
(XTopJointSendBlockG's `JAtZ.runTmoJ`: `set_fault` of the timeout fault and
the blocking `send_ipc` on the handler endpoint; `Inv` by the weakened
`Inv.rd`, a sender with a timeout fault exempt). The tail's reads (its SC,
runnable, the ready and sufficient tests not both true, the valid timeout
handler, the fault not a timeout, the SC's badge) at the state between, on
`XTopAt` there. The spec's outcome by `mem_doReplyTransfer`. -/
theorem replyRestTmoJ (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D) (hct2 : σ2.curThread = ct.bv)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    {xs : Fl4Spec.Tcb} (hks : σ2.kheap ct.bv = some (.tcb xs))
    (hxsr : Fl4Spec.runnable xs.tcbState = true) {EC : Fl4Spec.Endpoint → Prop}
    (hRT : RunTmoP (L := L) arI AR Z EC) (hC : ReplyRestTmo σ2 ct i) (hid : TmoEp EC σ2 i) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xi, sp, y, n, hki, hxsc, hky, hya, hnrel, hvt, hcase⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  obtain ⟨xi', ep, bd, r, xe2, hki', hth, hke2, hcb2⟩ := hid
  rw [hki] at hki'; cases hki'
  have hep : ep ≠ i.bv := fun e => by rw [e, hki] at hke2; cases hke2
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  have hxr := hI.1.toE.at_tcb hiT hki
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨i2, hi2⟩ : ∃ i2 : U64, i2 = L.mem s2 (P1.scA i) := ⟨_, rfl⟩
  rw [← hi2] at hscw
  have h0 : i2 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero, hxsc] at hscw; cases hscw
  have esp : sp = i2.bv := by rw [Notif.optRef_ne h0, hxsc] at hscw; exact Option.some.inj hscw
  subst esp
  have hi2C : i2 ∈ Z.C := by rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h0)
  have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
  have hne2 : y.scRefills ≠ [] := J2.inv.ne _ y n hky hya
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  unfold fl4ReplyRest2
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  rcases hcase with hfi | ⟨xs', f, σ', hks', hfi, htf, hhf⟩
  · ------------------------------------------------------------------ no fault
    have hft0 : ft = 0#u64 := by rw [hft]; exact hxr.fault0.2 hfi
    rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
    have hto : ¬ ft = fl4_abi.consts.fault.Timeout := by
      rw [hft0, show fl4_abi.consts.fault.Timeout = 5#u64 by unfold fl4_abi.consts.fault.Timeout; rfl]; decide
    refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb)
        (G : MdbGhost) (V : XVs),
        Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
        σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = some i2.bv ∧ x3.tcbFault = none ∧
        x3.tcbTimeoutHandler = xi.tcbTimeoutHandler ∧
        σ3.kheap i2.bv = σ2.kheap i2.bv ∧
        XTopAt (L := L) AR (Z.mv G V) res.1 ar
          (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv) ∧
        ∀ b : U64, faults.handle_timeout st arI res.1 ar i (error.Fault.Timeout b) ⦃ res' => ∃ z ∈
          (Fl4Spec.handleTimeout (Z := Unit) i.bv (.timeout b.bv)
            (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv)).1,
          JAt (L := L) arI AR res'.1 res'.2 z.2 ⦄) ?_ ?_
    · refine WP.spec_bind (J2.xferAllJ hAT hmax (htu ar) hcT hiT hne hks hki g none 0#u64 0#u64
        (Or.inr ⟨rfl, rfl⟩)) ?_
      rintro s4 ⟨σ3, htr, hkp3, ⟨x3, hk3, hx3⟩, G, V, J3⟩
      rw [e0] at htr
      have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
        rw [htr]; exact Set.mem_singleton _
      have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
      have hsc3 : x3.tcbSchedContext = some i2.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hxsc
      have hf3 : x3.tcbFault = none := (congrArg Fl4Spec.Tcb.tcbFault hx3).trans hfi
      have hth3 : x3.tcbTimeoutHandler = xi.tcbTimeoutHandler :=
        (congrArg Fl4Spec.Tcb.tcbTimeoutHandler hx3).trans rfl
      have hsd : ∀ sc, xs.tcbSchedContext = some sc → i2.bv ≠ sc := by
        rintro sc hsc rfl
        obtain ⟨y1, n1, hk1, hb1⟩ := J2.inv.back _ _ _ hks hsc
        obtain ⟨y2, n2, hk2, hb2⟩ := J2.inv.back _ _ _ hki hxsc
        rw [hk1] at hk2; cases hk2; rw [hb1] at hb2
        exact hne (P1.eq_of_bv (Option.some.inj hb2))
      have hes : ∀ sc, xs.tcbSchedContext = some sc → ep ≠ sc := by
        rintro sc hsc rfl
        obtain ⟨y1, n1, hk1, -⟩ := J2.inv.back _ _ _ hks hsc
        rw [hk1] at hke2; cases hke2
      have hcb3 : ∀ xe, σ3.kheap ep = some (.endpoint xe) → EC xe := by
        intro xe he
        rcases hkp3 ep hep hes with h | ⟨r', cs, cs', h1, -⟩
        · rw [h, hke2] at he; cases he; exact hcb2
        · rw [hke2] at h1; cases h1
      have hkpi : σ3.kheap i2.bv = σ2.kheap i2.bv := (hkp3 _ hti hsd).elim id
        (fun h => by obtain ⟨r', cs, cs', h1, _⟩ := h; rw [hky] at h1; cases h1)
      have hky3 : σ3.kheap i2.bv = some (.schedContext y n) := by rw [hkpi]; exact hky
      have hct3 : i.bv ≠ σ3.curThread := by
        rw [(dk_doIpcTransfer' _ _ _ _ _).ct mem3, hct2]; intro e; exact hne (P1.eq_of_bv e).symm
      obtain ⟨x5, hk5', hTR5⟩ := (J3.xtop.irelK J3.ks J3.buf).1.tcb i hiT
      rw [hk3] at hk5'; cases hk5'
      have hr0 : L.mem s4 (P1.stA i) = sched.TS_INACTIVE := by
        apply UScalar.eq_of_val_eq
        rw [P1.stA_eq, ← tStA_eq, hTR5.st, hs3]; unfold sched.TS_INACTIVE; rfl
      have htH : i ∈ P1.Heap.tcbs H := J3.zH.1 i hiT
      have hcs3 : σ3.kheap ct.bv = some (.tcb xs) := by
        rcases hkp3 ct.bv (fun e => hne (P1.eq_of_bv e)) (fun sc hsc e => by
          obtain ⟨y1, n1, hk1, -⟩ := J2.inv.back _ _ _ hks hsc
          rw [← e, hks] at hk1; cases hk1) with h | ⟨r', cs, cs', h1, -⟩
        · rw [h]; exact hks
        · rw [hks] at h1; cases h1
      have hcr3 : ∃ xc, σ3.kheap σ3.curThread = some (.tcb xc) ∧ Fl4Spec.runnable xc.tcbState = true :=
        ⟨xs, by rw [(dk_doIpcTransfer' _ _ _ _ _).ct mem3, hct2]; exact hcs3, hxsr⟩
      refine WP.spec_bind (hRT _ _ _ _ _ _ _ _ _ (by rfl) J3 hcr3 i hiT hiD x3 hk3 hs3 hct3 i2 hi2C hsc3 y n hky3 hya
        ep bd r (hth3.trans hth) hcb3
        .running rfl (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)
        (P1.sched.set_thread_state.running_blkI (Es := P1.EH H) s4 i J3.blk htH hr0)) ?_
      rintro s5 ⟨hX5, -, htmo⟩
      exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, G, V, htr, hk3, hsc3, hf3, hth3, hkpi, hX5, htmo⟩
    rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, G, V, htr, hk3, hsc3, hf3, hth3, hkpi, hX5, htmo⟩
    simp only at ha
    subst ha
    have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
      rw [htr]; exact Set.mem_singleton _
    set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
    set σ4 := updK σ3 i.bv (.tcb x5) with hσ4
    set σ5 := stsAct σ4 i.bv with hσ5
    have hrec : σ5 = { σ4 with schedulerAction := σ5.schedulerAction } := stsAct_rec σ4 i.bv
    have hk5 : σ5.kheap i.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp [hσ4, updK]
    have hky5 : σ5.kheap i2.bv = some (.schedContext y n) := by
      rw [hσ5, stsAct_kheap, hσ4]; simp only [updK, Function.update_of_ne hti]; rw [hkpi]; exact hky
    have htm5 : σ5.curTime = σ2.curTime := by
      rw [hrec]; exact (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
    have hS5 := hX5.fin.1.1.1
    obtain ⟨Q5, R5, hc5, hsp5⟩ := hS5.lists
    obtain ⟨x6, hk6, -, -, hscw5, -⟩ := hsp5.tcb i hiT
    rw [hk5] at hk6; cases hk6
    obtain ⟨x6', hk6', hTR5⟩ := hX5.ipc.tcb i hiT
    rw [hk5] at hk6'; cases hk6'
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
    rw [← hi3] at hscw5
    have h3 : i3 ≠ 0#u64 := by
      intro e; rw [e, optRef_zero] at hscw5; rw [hsc3] at hscw5; cases hscw5
    have e3 : i3 = i2 := by
      rw [Notif.optRef_ne h3] at hscw5; rw [hsc3] at hscw5
      exact P1.eq_of_bv (Option.some.inj hscw5).symm
    subst e3
    step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
    rw [hb2, if_neg (by simp [h3])]
    refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s5 i) ?_
    rintro b3 rfl
    have hrw : L.mem s5 (tStA i) = sched.TS_RUNNING := by
      apply UScalar.eq_of_val_eq; rw [hTR5.st]; unfold sched.TS_RUNNING; rfl
    rw [if_pos (by simp [hrw])]
    have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
        Fl4Spec.setThreadState i.bv .running) σ2).1 := by
      rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
    have hvt5 : Fl4Spec.isEpCap x5.tcbTimeoutHandler = true := by
      show Fl4Spec.isEpCap x3.tcbTimeoutHandler = true; rw [hth3]; exact hvt
    have tmo : fl4ReplyTmo st arI i ft i3 s5 a2 ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
        JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
      unfold fl4ReplyTmo
      refine WP.spec_bind (valid_timeout_handler_rel s5 σ5 hX5.rel.2.1.1 (hX5.rel.tcbT hk5)) ?_
      rintro b5 ⟨-, x', hkx', hb5⟩
      rw [hk5] at hkx'; cases hkx'
      rw [if_pos (by rw [hb5]; exact hvt5)]
      rw [if_pos (by simpa using hto)]
      step with Fl4Proofs.P3.Sched.obj.Sc.badge.spec' as ⟨bw, hbw⟩
      subst hbw
      obtain ⟨y5, n5, hky5', hy5⟩ := hsp5.scs i3 hi2C
      rw [hky5] at hky5'; cases hky5'
      refine WP.spec_mono (htmo _) ?_
      rintro res ⟨z, hz, hJz⟩
      refine ⟨z, mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) ?_, hJz⟩
      rw [specReplyTail_run hk5 hsc3 rfl hky5, if_neg (by rw [htm5]; exact hnrel)]
      unfold specReplyTmo
      rw [nd_bind_one (getTcb_eq hk5), if_pos ⟨hvt5, by rw [hfi]; simp [Option.elim]⟩, hy5.badge]
      exact hz
    unfold fl4ReplyTmo at tmo
    refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s5 σ5 hS5 hi2C hky5 hya) ?_
    rintro b4 hb4
    rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky5 hne2] at hb4
    have hb4' : b4 = Fl4Spec.refillReady σ5.curTime (Fl4Spec.refillHd y) := by
      have := congrArg (fun q => (b4, σ5) ∈ q.1) hb4; simpa using this.symm
    by_cases hr4 : b4 = true
    · rw [if_pos hr4]
      refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s5 _ σ5 hS5 hi2C hky5 hya 0#u64 (hmb _)) ?_
      rintro b5 hb5
      rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky5 hne2] at hb5
      have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
        have := congrArg (fun q => (b5, σ5) ∈ q.1) hb5; simpa using this.symm
      have hr5 : ¬ b5 = true := fun h => hnrel ⟨by rw [← htm5, ← hb4']; exact hr4, by rw [← e0, ← hb5']; exact h⟩
      rw [if_neg hr5]
      exact tmo
    · rw [if_neg hr4]
      exact tmo
  · ------------------------------------------------------------------ a fault, restarted by its reply
    rw [hks] at hks'; cases hks'
    have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
      intro e
      have h := hxr.fault0.1 (by rw [← hft, e]; unfold fl4_abi.consts.fault.NullFault; rfl)
      rw [hfi] at h; cases h
    have hftT : ft = fl4_abi.consts.fault.Timeout ↔ Fl4Spec.isTimeoutFault f = true := by
      rw [hft, show fl4_abi.consts.fault.Timeout = 5#u64 by unfold fl4_abi.consts.fault.Timeout; rfl, hxr.faultT, hfi]
      cases f <;> simp [Fl4Spec.isTimeoutFault]
    have hto : ¬ ft = fl4_abi.consts.fault.Timeout := fun h => absurd (hftT.1 h) (by rw [htf]; decide)
    rw [if_neg hft0]
    -- after the fault reply: `Restart` and the tail's `handle_timeout` as one step
    refine WP.spec_bind (faultBranchJ J2 hne hiT hcT hks hki hfi (fun e d h => by rw [hin] at h; cases h)
      (fun rst s σ => rst = true → ∃ V' : XVs, XTopAt (L := L) AR (Z.mv Z.G V') s ar σ ∧
        ∀ b : U64, faults.handle_timeout st arI s ar i (error.Fault.Timeout b) ⦃ res' => ∃ z ∈
          (Fl4Spec.handleTimeout (Z := Unit) i.bv (.timeout b.bv) σ).1, JAt (L := L) arI AR res'.1 res'.2 z.2 ⦄)
      ?_) ?_
    · intro rst x4 s5 V hx4 J5
      have hk5 : (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap i.bv =
          some (.tcb { x4 with tcbFault := none }) := by simp [updK]
      have hrs : ({ x4 with tcbFault := none } : Fl4Spec.Tcb).tcbState = .inactive := by
        have h := congrArg Fl4Spec.Tcb.tcbState hx4; exact h.trans hin
      have hsc5 : ({ x4 with tcbFault := none } : Fl4Spec.Tcb).tcbSchedContext = some i2.bv := by
        have h := congrArg Fl4Spec.Tcb.tcbSchedContext hx4; exact h.trans hxsc
      have hth5 : ({ x4 with tcbFault := none } : Fl4Spec.Tcb).tcbTimeoutHandler = .endpointCap ep bd r := by
        have h := congrArg Fl4Spec.Tcb.tcbTimeoutHandler hx4; exact h.trans hth
      obtain ⟨x5, hk5', hTR5⟩ := (J5.xtop.irelK J5.ks J5.buf).1.tcb i hiT
      rw [hk5] at hk5'; cases hk5'
      have hr0 : L.mem s5 (P1.stA i) = sched.TS_INACTIVE := by
        apply UScalar.eq_of_val_eq
        rw [P1.stA_eq, ← tStA_eq, hTR5.st, hrs]; unfold sched.TS_INACTIVE; rfl
      have htH : i ∈ P1.Heap.tcbs H := J5.zH.1 i hiT
      cases rst
      · refine WP.spec_mono (J5.stsIJ hiT hiD hk5 hrs .inactive (by decide) sched.TS_INACTIVE
          (by unfold sched.TS_INACTIVE; rfl) (fun h => by
            rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h)
          (P1.sched.set_thread_state.inactive_blkI (Es := P1.EH H) s5 i J5.blk htH hr0)) ?_
        intro s6 _ h
        exact absurd h Bool.false_ne_true
      · have hky5 : (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap i2.bv =
            some (.schedContext y n) := by simp [updK, hti, hky]
        have htc5 : i.bv ≠ (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).curThread := by
          show i.bv ≠ σ2.curThread
          rw [hct2]; intro e; exact hne (P1.eq_of_bv e).symm
        have hcb5 : ∀ xe, (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap ep =
            some (.endpoint xe) → EC xe := by
          intro xe he
          have he' : σ2.kheap ep = some (.endpoint xe) := by simpa [updK, hep] using he
          rw [hke2] at he'; cases he'; exact hcb2
        have hcr5 : ∃ xc, (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap
            (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).curThread = some (.tcb xc) ∧
            Fl4Spec.runnable xc.tcbState = true := by
          have hci : ct.bv ≠ i.bv := fun e => hne (P1.eq_of_bv e)
          refine ⟨xs, ?_, hxsr⟩
          show (updK (updK σ2 i.bv (.tcb x4)) i.bv (.tcb { x4 with tcbFault := none })).kheap σ2.curThread = _
          rw [hct2]; simp [updK, hci, hks]
        refine WP.spec_mono (hRT _ _ _ _ _ _ _ _ _ (by rfl) J5 hcr5 i hiT hiD _ hk5 hrs htc5 i2 hi2C hsc5 y n hky5 hya
          ep bd r hth5 hcb5
          .restart rfl (by decide) sched.TS_RESTART (by unfold sched.TS_RESTART; rfl)
          (P1.sched.set_thread_state.restart_blkI (Es := P1.EH H) s5 i J5.blk htH hr0)) ?_
        rintro s6 ⟨hX6, -, htmo⟩ -
        exact ⟨V, hX6, htmo⟩
    rintro ⟨s6, a2⟩ ⟨ha, rst, x4, hx4, hhf2, hz1, hq⟩
    dsimp only at ha hq
    subst ha
    -- the fault reply restarts (`ReplyRestTmo`)
    have hrst : rst = true := by
      rw [hhf2] at hhf
      exact (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hhf))).1
    subst hrst
    obtain ⟨V6, hX6, htmo⟩ := hq rfl
    have hk6 : (frSt σ2 i x4 true).kheap i.bv = some (.tcb { ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := .restart }) := by simp [frSt, stsAct_kheap, updK]
    have hkp6 : ∀ q, q ≠ i.bv → (frSt σ2 i x4 true).kheap q = σ2.kheap q := by
      intro q hq'; simp [frSt, stsAct_kheap, updK, hq']
    have hrec6 : frSt σ2 i x4 true = { (updK (updK (updK σ2 i.bv (.tcb x4)) i.bv
        (.tcb { x4 with tcbFault := none })) i.bv (.tcb { ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
          tcbState := if true then .restart else .inactive })) with
        schedulerAction := (frSt σ2 i x4 true).schedulerAction } := stsAct_rec _ _
    have htm6 : (frSt σ2 i x4 true).curTime = σ2.curTime := by rw [hrec6]; rfl
    have hsc6 : ({ ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := Fl4Spec.ThreadState.restart } : Fl4Spec.Tcb).tcbSchedContext = some i2.bv := by
      have h := congrArg Fl4Spec.Tcb.tcbSchedContext hx4; exact h.trans hxsc
    have hth6 : ({ ({ x4 with tcbFault := none } : Fl4Spec.Tcb) with
        tcbState := Fl4Spec.ThreadState.restart } : Fl4Spec.Tcb).tcbTimeoutHandler = xi.tcbTimeoutHandler := by
      have h := congrArg Fl4Spec.Tcb.tcbTimeoutHandler hx4; exact h
    have hky6 : (frSt σ2 i x4 true).kheap i2.bv = some (.schedContext y n) := by rw [hkp6 _ hti]; exact hky
    have hS6 := hX6.fin.1.1.1
    obtain ⟨Q6, R6, hc6, hsp6⟩ := hS6.lists
    obtain ⟨x6, hk6', -, -, hscw6, -⟩ := hsp6.tcb i hiT
    rw [hk6] at hk6'; cases hk6'
    obtain ⟨x6', hk6'', hTR6⟩ := hX6.ipc.tcb i hiT
    rw [hk6] at hk6''; cases hk6''
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
    rw [← hi3] at hscw6
    have h3 : i3 ≠ 0#u64 := by
      intro e; rw [e, optRef_zero] at hscw6; rw [hsc6] at hscw6; cases hscw6
    have e3 : i3 = i2 := by
      rw [Notif.optRef_ne h3] at hscw6; rw [hsc6] at hscw6
      exact P1.eq_of_bv (Option.some.inj hscw6).symm
    subst e3
    step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
    rw [hb2, if_neg (by simp [h3])]
    refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s6 i) ?_
    rintro b3 rfl
    have hrw : L.mem s6 (tStA i) = sched.TS_RESTART := by
      apply UScalar.eq_of_val_eq; rw [hTR6.st]; unfold sched.TS_RESTART; rfl
    rw [if_pos (by rw [hrw]; simp)]
    have hvt6 : Fl4Spec.isEpCap xi.tcbTimeoutHandler = true := hvt
    have tmo : fl4ReplyTmo st arI i ft i3 s6 a2 ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
        JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
      unfold fl4ReplyTmo
      refine WP.spec_bind (valid_timeout_handler_rel s6 (frSt σ2 i x4 true) hX6.rel.2.1.1 (hX6.rel.tcbT hk6)) ?_
      rintro b5 ⟨-, x', hkx', hb5⟩
      rw [hk6] at hkx'; cases hkx'
      rw [if_pos (by rw [hb5]; exact (congrArg Fl4Spec.isEpCap hth6).trans hvt6)]
      rw [if_pos (by simpa using hto)]
      step with Fl4Proofs.P3.Sched.obj.Sc.badge.spec' as ⟨bw, hbw⟩
      subst hbw
      obtain ⟨y6, n6, hky6', hy6⟩ := hsp6.scs i3 hi2C
      rw [hky6] at hky6'; cases hky6'
      refine WP.spec_mono (htmo _) ?_
      rintro res ⟨z, hz, hJz⟩
      refine ⟨z, mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inr ⟨f, hfi, hz1⟩) ?_, hJz⟩
      rw [specReplyTail_run hk6 hsc6 rfl hky6, if_neg (by rw [htm6]; exact hnrel)]
      unfold specReplyTmo
      rw [nd_bind_one (getTcb_eq hk6), if_pos ⟨by rw [hth6]; exact hvt6, by rw [hfi]; simp [Option.elim, htf]⟩,
        hy6.badge]
      exact hz
    unfold fl4ReplyTmo at tmo
    refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s6 (frSt σ2 i x4 true) hS6 hi2C hky6 hya) ?_
    rintro b4 hb4
    rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky6 hne2] at hb4
    have hb4' : b4 = Fl4Spec.refillReady (frSt σ2 i x4 true).curTime (Fl4Spec.refillHd y) := by
      have := congrArg (fun q => (b4, frSt σ2 i x4 true) ∈ q.1) hb4; simpa using this.symm
    by_cases hr4 : b4 = true
    · rw [if_pos hr4]
      refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s6 _ (frSt σ2 i x4 true) hS6 hi2C hky6 hya 0#u64
        (hmb _)) ?_
      rintro b5 hb5
      rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky6 hne2] at hb5
      have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
        have := congrArg (fun q => (b5, frSt σ2 i x4 true) ∈ q.1) hb5; simpa using this.symm
      have hr5 : ¬ b5 = true := fun h => hnrel ⟨by rw [← htm6, ← hb4']; exact hr4, by rw [← e0, ← hb5']; exact h⟩
      rw [if_neg hr5]
      exact tmo
    · rw [if_neg hr4]
      exact tmo

section StKX
open Fl4Spec StK

/-- A `thread_set` keeping the thread state keeps every thread's state
(IpcStK's `STK`). -/
theorem st_threadSet_keep {t0 : ObjRef} (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbState = x.tcbState) (t : ObjRef) :
    STK t0 (threadSet (Z := Unit) f t) := by
  intro σ x hx
  by_cases hT : ∃ y0, σ.kheap t = some (.tcb y0)
  · obtain ⟨y0, hy0⟩ := hT
    rw [Notif.threadSet_eq f hy0] at hx
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨fun p z _ hz => ?_, rfl⟩
    by_cases hp : p = t
    · subst hp; simp [Notif.updK] at hz; subst hz; exact ⟨y0, hy0, hf y0⟩
    · exact ⟨z, by simpa [Notif.updK, hp] using hz, rfl⟩
  · have hg : getTcb (Z := Unit) t σ = none := by
      unfold getTcb readObject
      cases hk : σ.kheap t with
      | none => rfl
      | some k => cases k <;> first | rfl | exact absurd ⟨_, hk⟩ hT
    unfold threadSet at hx; obtain ⟨y, hy, -⟩ := hx
    unfold NonDet.getsThe at hy; rw [hg] at hy; exact hy.elim

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_tcbSchedAction _ _)
local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_tcbReleaseRemove _)

theorem st_rescheduleRequired' {t0 : ObjRef} : STK t0 (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  st_auto

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_rescheduleRequired')

open Classical in
theorem st_testReschedule' {t0 : ObjRef} (f : ObjRef) : STK t0 (testReschedule (Z := Unit) f) := by
  unfold testReschedule
  refine st_bind (st_gets _) fun _ => st_bind (st_gets _) fun _ => st_bind (st_pure _) fun _ => ?_
  apply st_when
  exact st_rescheduleRequired'

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_testReschedule' _)

theorem st_getScObjRef' {t0 : ObjRef} (f : SchedContext → Option ObjRef) (p : ObjRef) :
    STK t0 (getScObjRef (Z := Unit) f p) := by
  unfold getScObjRef getSchedContext; st_auto

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_getScObjRef' _ _)

theorem st_schedContextDonate' {t0 : ObjRef} (sc t : ObjRef) : STK t0 (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; st_auto
  all_goals (refine st_threadSet_keep _ ?_ _; intro; rfl)

/-- `reply_remove t r` keeps the state of every thread but `t`. -/
theorem st_replyRemove' (t r : ObjRef) : STK t (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; st_auto
  · unfold getTcbObjRef; st_auto
  · unfold replyUnlinkSc; st_auto
  · exact st_schedContextDonate' _ _

end StKX

/-- The timeout handler cap of a TCB names an endpoint object (the cap
valid in `J`, as in XTopJointSendBlockG's `JAtZ.runTmoJ`). -/
theorem JAtZ.tmoEpObj (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights}
    (hth : x.tcbTimeoutHandler = .endpointCap p bd r) : ∃ xe, σ.kheap p = some (.endpoint xe) := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨⟨G0, hB0⟩, -⟩ := hI.2.1
  have hth0 : Z.th t = some .tcb := hB0.tcbT hk
  obtain ⟨xh, cv, hkh, hcv, hca⟩ := hB0.2.1.1.timeoutCap hth0
  rw [hk] at hkh; cases hkh
  have habs := hca.2
  rw [hth] at habs
  obtain ⟨ptr, bdg, sd, rv, g, gr, rfl⟩ : ∃ ptr bdg sd rv g gr, cv = .Endpoint ptr bdg sd rv g gr := by
    cases cv <;> simp [absCap] at habs; exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs
  obtain ⟨hp, -, -⟩ := habs
  subst hp
  have hAS : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 4) := ⟨t, rfl, Or.inr ⟨hth0, 4, by decide, rfl⟩⟩
  have hcv' : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 4)) = ok (.Endpoint ptr bdg sd rv g gr) := by
    rw [tcbSlot4_eq]; exact hcv
  have hpE : ptr ∈ Z.E := J.slotE hAS hcv'
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  exact ⟨xe, hke⟩

set_option maxHeartbeats 8000000 in
/-- **`do_reply_transfer` at `J`**: no thread on the reply, or a thread not
blocked on it, nothing happens on either side; a thread blocked on it,
`reply_remove` at `J` (`JAtZ.replyRemoveJD`), then `replyRestNoScJ`,
`replyRestSwJ`, `replyRestPostJ`, `replyRestFaultJ`, or (`ReplyRestTmo`, the
split complete) `replyRestTmoJ` with `runTmoP_idle` (`TmoIdle`) or with
`hRT` (receivers waiting on the handler endpoint: XTopJointFaultTmo's
`runTmoP_recv`). The caller stays `Restart` across `reply_remove`
(`st_replyRemove'`), so it is not the receiver the timeout fault wakes. -/
theorem replyXferJ (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s1 : S} {ar : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 ar σ1) {ct p : U64} (hp : p ∈ Z.R) (g : Bool)
    (hcs : σ1.curThread = ct.bv ∧ ∃ xc, σ1.kheap ct.bv = some (.tcb xc) ∧ xc.tcbState = .restart)
    (hRT : RunTmoP (L := L) arI AR Z (fun xe => ¬ Endp.CanBlock false xe)) :
    ipc.do_reply_transfer st arI s1 ar ct p g ⦃ res =>
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1, JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  have hJ1 : JAt (L := L) arI AR s1 ar σ1 := ⟨_, _, _, _, _, _, J1⟩
  have hI := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨xr, hkr, hxr⟩ := hI.1.reply p hp
  unfold ipc.do_reply_transfer
  step with Fl4Proofs.P3.Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
  step with Fl4Proofs.P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
  by_cases h0 : i = 0#u64
  · rw [hb, if_pos (by simp [h0]), WP.spec_ok]
    exact ⟨((), σ1), by rw [doReplyTransfer_none hkr (by rw [hxr, ← hi, h0, optRef_zero])]; rfl, hJ1⟩
  rw [hb, if_neg (by simp [h0])]
  have hrep : xr.replyTcb = some i.bv := by rw [hxr, ← hi, Notif.optRef_ne h0]
  obtain ⟨x, hkx, hxs⟩ := J1.sv.replyTcb p.bv xr i.bv hkr hrep
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J1.obj.tcb _ x hkx
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb i hiT
  rw [hkx] at hk0; cases hk0
  step with Fl4Proofs.P3.Notif.obj.Tcb.state.spec as ⟨i1, hi1⟩
  rcases hxs with hst | ⟨ep, d, hst⟩
  swap
  · -- receiving with the reply: nothing happens
    have hne : (i1 != sched.TS_BLOCKED_ON_REPLY) = true := by
      have h := hTR.st
      rw [hst] at h
      rw [hi1]
      have : L.mem s1 (tStA i) ≠ sched.TS_BLOCKED_ON_REPLY := by
        intro e; rw [e] at h; unfold sched.TS_BLOCKED_ON_REPLY at h; simp [tsCode] at h
      simpa using this
    rw [if_pos hne, WP.spec_ok]
    refine ⟨((), σ1), ?_, hJ1⟩
    rw [doReplyTransfer_notReply hkr hrep hkx (by rw [hst]; intro r' h; cases h)]; rfl
  have hne : (i1 != sched.TS_BLOCKED_ON_REPLY) = false := by
    have h := hTR.st
    rw [hst] at h
    rw [hi1]
    have : L.mem s1 (tStA i) = sched.TS_BLOCKED_ON_REPLY := by
      apply UScalar.eq_of_val_eq; rw [h]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
    simp [this]
  rw [if_neg (by rw [hne]; simp)]
  have hiD : i ∉ D := fun h => J1.notDead hiT hkx (by rw [hst]; simp [tsCode]) i h rfl
  have hne : ct ≠ i := by
    rintro rfl
    obtain ⟨xc, hkc, hcr⟩ := hcs.2
    rw [hkc] at hkx; cases hkx; rw [hcr] at hst; cases hst
  obtain ⟨⟨s2, a2⟩, hrr, hpost⟩ := spec_exists (J1.replyRemoveJD hAT hp hiT hkx hst)
  obtain ⟨ea, σ2, V', Ac', Lst', D', hrm, J2, -, -, hDD, hin, hact⟩ := hpost
  simp only at ea
  subst ea
  subst hDD
  rw [hrr]
  simp only [bind_ok]
  have hct2 : σ2.curThread = ct.bv := by
    rw [(Vs.dk_replyRemove' i.bv p.bv).ct (x := ((), σ2)) (by rw [hrm]; exact Set.mem_singleton _)]
    exact hcs.1
  obtain ⟨xi0, hki0, hin0⟩ := hin
  suffices key : fl4ReplyRest st arI s2 a2 ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ from key
  rw [fl4ReplyRest_eq]
  refine J2.replyUnblockJ hiT hki0 hin0 (fun s3 => fl4ReplyRest2 st arI s3 a2 ct i g) _ ?_
  intro s3 σ3 Lst3 hub J3 htk hct3 hscK
  -- the receiver's SC is active (`replyRemoveJD`'s `remove_act`, kept by the unblock test)
  have hact3 : ∀ q y n, σ3.kheap q = some (.schedContext y n) → y.scTcb = some i.bv →
      Fl4Spec.scActive y = true := by
    intro q y n hq hyt
    obtain ⟨y0, hq0, hm, htc⟩ := hscK q y n hq
    have h0 := hact q y0 n hq0 (htc.symm.trans hyt)
    show Fl4Spec.activeSc y.scRefillMax = true
    rw [hm]; exact h0
  have hin3 : ∃ x', σ3.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive := ⟨xi0, htk _ _ hki0, hin0⟩
  have hct3' : σ3.curThread = ct.bv := hct3.trans hct2
  by_cases hC : ReplyRestNoSc σ3 ct i g
  · exact replyRestNoScJ (Z := Z.mv Z.G V') hAT hmax htu J3 g hne hiD hkr hrep hkx hst hrm hub hin3 hC
  by_cases hC2 : ReplyRestSw σ3 ct i g
  · exact replyRestSwJ (Z := Z.mv Z.G V') hmb hAT hmax htu J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hC2
  by_cases hC3 : ReplyRestPost σ3 ct i g
  · exact replyRestPostJ (Z := Z.mv Z.G V') hmb hAT hmax htu J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hC3
  by_cases hC4 : ReplyRestFault σ3 ct i
  · exact replyRestFaultJ (Z := Z.mv Z.G V') hmb J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hact3 hC4
  -- the case left: the split is complete (`ReplyRestTmo`)
  have hcT : ct ∈ Z.T := by
    obtain ⟨xc, hkc, -⟩ := hcs.2
    obtain ⟨t, ht, h⟩ := J1.obj.tcb _ xc hkc
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨xs, hks3, -⟩ := (J3.xtop.irelK J3.ks J3.buf).1.tcb ct hcT
  have hTmo : ReplyRestTmo σ3 ct i := by
    obtain ⟨xi, hki3, -⟩ := hin3
    cases hf : xi.tcbFault with
    | none =>
      cases hsc : xi.tcbSchedContext with
      | none => exact absurd ⟨xs, xi, hks3, hki3, hsc, hf⟩ hC
      | some sp =>
        obtain ⟨y, n, hky, hyt⟩ := J3.inv.back _ _ _ hki3 hsc
        have hya := hact3 _ y n hky hyt
        have hnrel : ¬ (Fl4Spec.refillReady σ3.curTime (Fl4Spec.refillHd y) = true ∧
            Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true) :=
          fun h => hC2 ⟨xs, xi, sp, y, n, hks3, hki3, hsc, hky, hya, h.1, h.2, hf⟩
        have hvt : Fl4Spec.isEpCap xi.tcbTimeoutHandler = true := by
          cases h : Fl4Spec.isEpCap xi.tcbTimeoutHandler
          · exact absurd ⟨xs, xi, sp, y, n, hks3, hki3, hsc, hky, hya, hnrel, h, hf⟩ hC3
          · rfl
        exact ⟨xi, sp, y, n, hki3, hsc, hky, hya, hnrel, hvt, Or.inl hf⟩
    | some f =>
      have h4 : ∃ σ', Fl4Spec.handleFaultReply (Z := Unit) f i.bv (frLbl xs) (frMrs xs σ3) σ3 =
          ({(true, σ')}, False) ∧ ReplyFaultTmo σ3 xi f := by
        by_contra hc
        exact hC4 ⟨xs, xi, f, hks3, hki3, hf, fun σ' h1 h2 => hc ⟨σ', h1, h2⟩⟩
      obtain ⟨σ', hhf, sp, y, n, hsc, hky, hnrel, hvt, htf⟩ := h4
      obtain ⟨y0, n0, hky0, hyt⟩ := J3.inv.back _ _ _ hki3 hsc
      rw [hky] at hky0; cases hky0
      exact ⟨xi, sp, y, n, hki3, hsc, hky, hact3 _ y n hky hyt, hnrel, hvt, Or.inr ⟨xs, f, σ', hks3, hf, htf, hhf⟩⟩
  -- the caller is still `Restart`
  have hxsr : Fl4Spec.runnable xs.tcbState = true := by
    obtain ⟨xc, hkc, hcr⟩ := hcs.2
    obtain ⟨y2, hk2, -⟩ := (J2.xtop.irelK J2.ks J2.buf).1.tcb ct hcT
    obtain ⟨y0, hy0, hst0⟩ := (st_replyRemove' i.bv p.bv σ1 ((), σ2) (by rw [hrm]; exact Set.mem_singleton _)).1
      ct.bv y2 (fun e => hne (P1.eq_of_bv e)) hk2
    rw [hkc] at hy0; cases hy0
    have h3 := htk _ _ hk2
    rw [hks3] at h3; cases h3
    rw [hst0, hcr]; rfl
  by_cases hid : TmoIdle σ3 i
  · exact replyRestTmoJ (Z := Z.mv Z.G V') hmb hAT hmax htu J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hks3
      hxsr (runTmoP_idle _) hTmo hid
  have hid' : TmoEp (fun xe => ¬ Endp.CanBlock false xe) σ3 i := by
    obtain ⟨xi, sp, y, n, hki, -, -, -, -, hvt, -⟩ := hTmo
    obtain ⟨ep, bd, r, hth⟩ : ∃ ep bd r, xi.tcbTimeoutHandler = .endpointCap ep bd r := by
      cases h : xi.tcbTimeoutHandler <;> simp [h, Fl4Spec.isEpCap] at hvt
      exact ⟨_, _, _, rfl⟩
    obtain ⟨xe, hke⟩ := J3.tmoEpObj hiT hki hth
    exact ⟨xi, ep, bd, r, xe, hki, hth, hke, fun hcb => hid ⟨xi, ep, bd, r, xe, hki, hth, hke, hcb⟩⟩
  exact replyRestTmoJ (Z := Z.mv Z.G V') hmb hAT hmax htu J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hks3
    hxsr hRT hTmo hid'

set_option maxHeartbeats 4000000 in
/-- **The reply cap's leaf at `J`** (`replyXferJ`
after the caller's restart, `JAtZ.restartJ`; the cap's reply in `R`,
`JAtZ.slotR`). -/
theorem replyLeafJ (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p : U64} {g : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Reply p g))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hRT : RunTmoP (L := L) arI AR Z (fun xe => ¬ Endp.CanBlock false xe)) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← ipc.do_reply_transfer st arI s1 ar ct p g
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1) := by
  intro _
  have hpR := J.slotR hA hc
  obtain ⟨s1, σ1', x, -, hst1, -, hcur, hσe, -, -, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  have hcs : σ1'.curThread = ct.bv ∧ ∃ xc, σ1'.kheap ct.bv = some (.tcb xc) ∧ xc.tcbState = .restart :=
    ⟨hc1, { x with tcbState := .restart }, by rw [hσe, stsAct_kheap]; simp [updK], rfl⟩
  rw [hs1]
  simp only [bind_ok]
  rw [hc1]
  refine WP.spec_bind (replyXferJ hAT hmax htu hmb J1 hpR g hcs hRT) ?_
  rintro ⟨s2, a2⟩ ⟨z, hz, Z', H', Cs', Ac', Lst', D', J'⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, J'.xtop.relTop, Z', H', Cs', Ac', Lst', D', J'⟩


variable (arI) in
/-- **[W] The endpoint cap's `send_ipc` at `J` where it meets a receiver**
(`sendLeafJ`): after the caller's restart (`s1`, `σ1`), a send to an
endpoint with receivers ends at `JAt` with an outcome of the spec's
`send_ipc`. The restart, a non-blocking send to an endpoint without
receivers (nothing happens, `send_ipc_noblock`) and the blocking send to one
(XTopJointSendBlock's `JAtZ.sendBlockJ`) are proved. What is left has an
`IRel` proof (IpcLeaves's `send_ipc_top`: the receiver's dequeue,
`do_ipc_transfer`, the reply push or the caller's block, the SC donation and
the switch, `send_ipc_recvG` / `send_ipc_callX_gen`, `SendRest`) but no J
frame. l4v: `send_ipc_invs` / `send_ipc_corres`. -/
def JSendRestHyp (AR : A → Fl4Spec.Cr3 → Prop) (s1 : S) (ar : A) (σ1 : Fl4Spec.State Unit)
    (blk call : Bool) (b : U64) (g gr don : Bool) (ct p : U64) : Prop :=
  ∀ x : Fl4Spec.Endpoint, σ1.kheap p.bv = some (.endpoint x) → ¬ CanBlock false x →
    endpoint.send_ipc st arI s1 ar blk call b g gr don ct p ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don ct.bv p.bv σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`send_ipc` at `J`** but for `JSendRestHyp`: a non-blocking send to an
endpoint without receivers (nothing happens on either side), or a blocking
one (`hblk`, from `JAtZ.sendBlockJ` in `sendLeafJ`). -/
theorem sendXferJ {s1 : S} {ar : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 ar σ1) {ct p : U64} (hp : p ∈ Z.E)
    (blk call : Bool) (b : U64) (g gr don : Bool)
    (hblk : ∀ x : Fl4Spec.Endpoint, σ1.kheap p.bv = some (.endpoint x) → CanBlock false x →
      endpoint.send_ipc st arI s1 ar true call b g gr don ct p ⦃ r =>
        ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true call b.bv g gr don ct.bv p.bv σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄)
    (hR : JSendRestHyp (L := L) arI AR s1 ar σ1 blk call b g gr don ct p) :
    endpoint.send_ipc st arI s1 ar blk call b g gr don ct p ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don ct.bv p.bv σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hJ1 : JAt (L := L) arI AR s1 ar σ1 := ⟨_, _, _, _, _, _, J1⟩
  have hI := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨x, hk, -⟩ := hI.1.ep p hp
  by_cases hc : CanBlock false x
  · cases blk
    · refine WP.spec_mono (send_ipc_noblock (ar := arI) s1 ar σ1 hI.1.toE hp hk hc call b g gr don ct) ?_
      rintro r ⟨rfl, h2⟩
      exact ⟨((), σ1), by rw [h2]; exact Set.mem_singleton _, hJ1⟩
    · exact hblk x hk hc
  · exact hR x hk hc

set_option maxHeartbeats 4000000 in
/-- **The endpoint cap's leaf at `J`** but for `JSendRestHyp` (`sendXferJ`
after the caller's restart, `JAtZ.restartJ`; the cap's endpoint in `E`,
`JAtZ.slotE`; the blocking send by `JAtZ.sendBlockJ`: the current thread
`Restart`, still resumed (schedulable, `ct_schedulable`), in no ready queue
(`hnq`, JEntryAt's `ctnq`), the endpoint covered by the invoked cap,
`JAtZ.cover_cap`, its slot kept by the restart, `restart_dstate`). -/
theorem sendLeafJ {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hnq : ∀ d q, σ.curThread ∉ σ.readyQueues d q) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {x1 x2 x3 x4 : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Endpoint p b x1 x2 x3 x4))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call : Bool) (g gr don : Bool)
    (hR : ∀ s1 σ1', sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1')}, False) →
      JSendRestHyp (L := L) arI AR s1 ar σ1' blk call b g gr don ct p) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← endpoint.send_ipc st arI s1 ar blk call b g gr don ct p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1) := by
  intro _
  have hpE := J.slotE hA hc
  obtain ⟨-, xr0, hkr, hrun0⟩ := J.curRunnable hni hct
  obtain ⟨s1, σ1', x, -, hst1, hkx, hcur, eσ1, -, hidl, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  have hrun : Fl4Spec.runnable x.tcbState = true := by rw [hkx] at hkr; cases hkr; exact hrun0
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  -- the blocking send's premises at the restart's state
  have hblk : ∀ xe : Fl4Spec.Endpoint, σ1'.kheap p.bv = some (.endpoint xe) → CanBlock false xe →
      endpoint.send_ipc st arI s1 ar true call b g gr don ct p ⦃ r =>
        ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true call b.bv g gr don ct.bv p.bv σ1').1,
          JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
    intro xe hke hcb
    have hS := J.xtop.fin.1.1.1
    obtain ⟨Q, R', hcq, -⟩ := hS.lists
    have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
      have h := sched.cur_thread.spec' (L := L) s
      rw [hct, WP.spec_ok, hcq.cur] at h; exact h
    have hctT : ct ∈ Z.T := hct' ▸ hcq.curT
    set xr : Fl4Spec.Tcb := { x with tcbState := .restart }
    have hkt1 : σ1'.kheap ct.bv = some (.tcb xr) := by
      rw [eσ1, (stsAct_fields _ _).1]; simp [Notif.updK]
    -- still resumed: the current thread stays schedulable
    have hsch : Fl4Spec.schedulable ct.bv σ = true := by
      have h := ct_schedulable (J.curInv (by rw [hni.2]; simp)) J.act J.inv (hcur ▸ hkx) hrun
      rw [hcur] at h; exact h
    have hsch1 : Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb xr)) = true := by
      rw [schedulable_updK_tcb (y := xr) (y' := x) (by rw [hrun]; rfl) rfl]
      exact (schedulable_heap (σ := σ) (σ' := Notif.updK σ ct.bv (.tcb x))
        (by simp only [Notif.updK_kheap]; exact Function.update_eq_self_iff.2 hkx.symm) rfl ct.bv).trans hsch
    have hres1 : σ1'.schedulerAction = .resumeCurThread := by
      rw [eσ1]; unfold Notif.stsAct
      rw [if_neg (fun h => by simp [hsch1] at h)]
      exact hni.2
    have hti1 : σ1'.curThread ≠ σ1'.idleThread := by rw [hcur1, hidl]; exact hni.1
    have hrq1 : σ1'.readyQueues = σ.readyQueues := by
      rw [eσ1]; unfold Notif.stsAct; split <;> rfl
    have hnq1 : ∀ d q, ct.bv ∉ σ1'.readyQueues d q := by
      rw [hrq1, ← hcur]; exact hnq
    -- the endpoint covered by the invoked cap (its slot kept by the restart)
    have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
    obtain ⟨s1'', -, -, hrs, -, hSS, -⟩ :=
      restart_dstate Z.th J.xtop.rel.1 s σ Z.G hDS ct hct hcur (J.xtop.curTcb hcur).1 J.kern.act
    obtain rfl : s1 = s1'' := eq_of_ok_eq (hs1.symm.trans hrs)
    have hc1' : capAt (L.mem s1) (cslotAddr sl) = ok (.Endpoint p b x1 x2 x3 x4) := by
      rw [hSS.capAt hA.isSlot]; exact hc
    have hHe : H p = some .ep := J1.zH.2.1 p hpE
    have hfit := J1.kern.heap.fits p _ hHe
    simp only [P1.HKind.bits] at hfit
    have hcov := J1.cover_cap (P1.WritesIn.refl s1 _) hA.isSlot hc1' (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
      (range_ep p b x1 x2 x3 x4 hfit) fun k hk => by
        rw [hHe] at hk; cases hk
        exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
    refine WP.spec_mono (J1.sendBlockJ hctT hkt1 rfl hc1 hres1 hti1 hnq1 hpE hke hcb hcov call b g gr don) ?_
    rintro r ⟨-, σ', heq, V, J'⟩
    exact ⟨((), σ'), by rw [heq]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J'⟩⟩
  rw [hs1]
  simp only [bind_ok]
  rw [hc1]
  refine WP.spec_bind (sendXferJ J1 hpE blk call b g gr don hblk (hR s1 σ1' hs1 hst1)) ?_
  rintro ⟨s2, a2⟩ ⟨z, hz, Z', H', Cs', Ac', Lst', D', J'⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, J'.xtop.relTop, Z', H', Cs', Ac', Lst', D', J'⟩

end

end

end Fl4Proofs.P3
