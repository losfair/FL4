/-
P3 (DESIGN.md §9): **the syscall dispatch above `handle_invocation` at `J`**
(proofs/KENTRY-PLAN.md, items 1–3).

* `JAtZ.frontEx`: at `JAtZ` (with BufJ's `JAtZ.xferH`: the IPC-buffer facts at the
  entry), FL4's front-end reads (`msg_info`, `lookup_ipc_buffer`,
  `lookup_extra_caps`) succeed and the spec's (`getMessageInfo`,
  `lookupIpcBuffer`, `lookupExtraCaps`, `getMrs`) have exactly one outcome
  each: the seven equations `handle_invocation_refinesJ` takes.
* `handle_invocation_entryJ`: `handle_invocation_refinesJ` with those
  equations discharged; the per-cap path premise (`JEntryHyps.path`) is asked
  at the front end's values (`JPathAt`).
* `dispatch_invokeJ`: FL4's `dispatch_syscall` for `SysSend`, `SysNBSend`
  and `SysCall` against the spec's `handleSend true`, `handleSend false`,
  `handleCall` with FL4's dispatcher (`fl4HandleInvocationR true`, the
  `fl4HandleInvocation` substitution of Ext/Invocation one level up; the
  inline `DispInv`, see KENTRY-PLAN.md M3): the cap register read
  (`getCapReg cap_register`, the register words related by `IRel`), the
  invocation at `J`, then `after_invocation`. Not preempted: the spec's
  outcome `.ok ()`, `JAt` after. Preempted: the spec's `.error ()` (what
  `callKernel`'s `handleE` sends to `preemptionPath`) and any `Q` that FL4's
  `after_invocation` (`mcs_preemption_point`, `check_interrupt`) reaches from
  every related `JAtPre` state (`hPre`; the preemption path at `J` against
  `preemptionPath` is plan item 7).
* `handle_recvJ`: IpcRecvTop's `handle_recv_refines` at `RJ` (`RelTopM`
  and `JAt`): the cap and reply registers, `lookup_cap` (`lookup_cap_refines`),
  the looked-up caps' objects (`lookup_cap_held`, the placement `J.jpl`, the
  sets' `IpcRel`), the bound TCB (`recv_bound_leaf`) and the cap faults
  (`JAtZ.faultHypJZ` with the receive flag) proved; `receive_ipc` and
  `receive_signal` at `J` named (`JRecvIpcHyp`, `JRecvSigHyp` [W]: plan
  items 5, 6).
* `dispatch_recvJ`: `dispatch_syscall` for `SysRecv`, `SysNBRecv`,
  `SysWait`, `SysNBWait` by `handle_recvJ`.
* `dispatch_invokeJE`, `dispatch_recvJE`: the same against the branches of
  `fl4HandleEvent true` (Ext/Entry's `fl4HandleSyscall true c`, `c` the
  spec syscall of FL4's number: `invSysOf`, `recvSysOf`).
-/
import Fl4Proofs.P3.XTopJointEntry
import Fl4Proofs.P3.IpcRecvTopH
import Fl4Spec.Ext.Entry
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem regIdx_cap : regIdx Fl4Spec.cap_register = layout.reg.CAP := by
  unfold layout.reg.CAP layout.reg.RDI; rfl

theorem map_bv_ofBv (l : List Fl4Spec.Data) : (l.map (fun b => (⟨b⟩ : U64))).map UScalar.bv = l := by
  induction l with
  | nil => rfl
  | cons b t ih => exact congrArg (b :: ·) ih

set_option maxHeartbeats 4000000 in
/-- **The front end's reads at `J`**: FL4's succeed, the spec's have one
outcome each (the equations of `handle_invocation_refinesJ`). -/
theorem JAtZ.frontEx {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover Z.T Z.B σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∃ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
      msg.msg_info st s ct = ok info ∧
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) ∧
      msg.lookup_ipc_buffer st s false ct = ok buf ∧
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) ∧
      ipc.lookup_extra_caps st s ct buf info = ok r2 ∧
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False) ∧
      Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hwmi : (L.mem s (regA ct layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  obtain ⟨info, hinfo, hm⟩ := Fl4Proofs.P3.spec_exists (Endp.msg_info_spec (L := L) s ct)
  have hext := hm.2.2.1
  obtain ⟨buf, hbuf, hsb, hsbp⟩ := Fl4Proofs.P3.spec_exists
    (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 htcb hks hOK false)
  obtain ⟨xs', hks', hws⟩ := J.buf ct hctT
  rw [hks] at hks'; cases hks'
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → Endp.BufMap Z.B buf sp :=
    fun sp h => hBC ct hctT xs false sp hks h buf (hsbp hws sp h)
  have hal : ∀ sb, Endp.ipcBufOf false xs = some sb → ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0 := by
    intro sb hsb' k hk
    have hmb := hBC ct hctT xs false sb hks hsb' ⟨sb⟩ rfl
    have hv : (⟨BitVec.ofNat 64 k⟩ : U64).val = k := by
      show (BitVec.ofNat 64 k).toNat = k; simp; omega
    have h := (J.ip.e.balign _ (hmb ⟨BitVec.ofNat 64 k⟩ (by rw [hv]; omega))).2
    rw [hv] at h; exact h
  have hlk := Ipc.lookup_extra_rel J.ip J.xtop.rel hI.1 htcb buf (Endp.ipcBufOf false xs)
    ⟨hsb.1, hsb.2⟩ hsm info (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))
    (by show info.extra_caps.bv.toNat = _; rw [hext, hwmi])
    (by show info.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact Endp.extra_le3 _)
  obtain ⟨r2, hr2, hlk⟩ := Fl4Proofs.P3.spec_exists hlk
  have her : ∃ er, (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv (Endp.ipcBufOf false xs)
      (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))).run σ =
      ({(er, σ)}, False) := by
    cases r2 with
    | Ok e => obtain ⟨caps, hc, -⟩ := hlk; exact ⟨_, hc⟩
    | Err f => obtain ⟨f', hc, -⟩ := hlk; exact ⟨_, hc⟩
  obtain ⟨er, her⟩ := her
  refine ⟨info, _, buf, _, r2, er, (specMrs xs.tcbArch.tcbContext.userRegs (Endp.ipcBufOf false xs)
      σ.machineState.underlyingMemory (Fl4Spec.unat (Fl4Spec.dataToMessageInfo
        (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLength)).map (fun b => (⟨b⟩ : U64)),
    hinfo, getMessageInfo_eq hks, hbuf, lookupIpcBuffer_eq hks false, hr2, her, ?_⟩
  rw [map_bv_ofBv]
  exact getMrs_eq hks _ hal _

/-- **The per-cap path premise at the front end's values** (`JEntryHyps.path`
for every outcome of the front end's reads, which `JAtZ.frontEx` shows to
exist and be unique). -/
def JPathAt (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64) : Prop :=
  ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
    msg.msg_info st s ct = ok info →
    Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) →
    msg.lookup_ipc_buffer st s false ct = ok buf →
    Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) →
    ipc.lookup_extra_caps st s ct buf info = ok r2 →
    (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False) →
    Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c → Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) →
      r2 = .Ok e → er = .ok exs →
      JPath (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **One invocation at `J`, the front end discharged**:
`handle_invocation_refinesJ` from `JAtZ`, `JEntryGlob`, `JEntryAt` and the
path premise at the front end's values. -/
theorem handle_invocation_entryJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct is_call blocking can_donate first_phase cptr) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) true σ is_call blocking can_donate first_phase
        (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  exact handle_invocation_refinesJ arI s ar σ J ct hct is_call blocking can_donate first_phase cptr info hinfo mi hmi
    buf hbuf buffer hbuffer r2 hr2 er her argsU hmrs
    ⟨hG, hE, hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs⟩

/-- The spec's invoking syscalls with FL4's dispatcher: `handleSend bl`
(`call = false`, `don = false`) and `handleCall` (`call = bl = don = true`)
with `fl4HandleInvocationR true` for l4v's `handleInvocation`. -/
def DispInv (call bl don : Bool) : Fl4Spec.PMonad Unit Unit := do
  let cptr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getCapReg (Z := Unit) Fl4Spec.cap_register
  Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false cptr

/-- **The post of an invoking syscall at `J`**: not preempted, the spec's
`.ok ()` with `JAt`; preempted, the spec's `.error ()` and `Q` of the spec's
state and FL4's (`Q`: what the preemption path, `after_invocation` from a
`JAtPre` state, gives). -/
def DispPost (AR : A → Fl4Spec.Cr3 → Prop) (Q : Fl4Spec.State Unit → S × A → Prop) (m : Fl4Spec.PMonad Unit Unit)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ y ∈ (m.run σ).1,
    (y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧ JAt (L := L) arI AR r.1 r.2 y.2) ∨ (y.1 = .error () ∧ Q y.2 r)

set_option maxHeartbeats 4000000 in
/-- **`handle_invocation` then `after_invocation` at `J`**, from the cap
register's word; the preemption path (`after_invocation` of `Err`) from
every related `JAtPre` state to `Q` is the premise `hPre` (plan item 7). -/
theorem invoke_afterJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (call bl don : Bool)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call bl don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have top : ∀ y, y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false
      (Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv)).run σ).1 → y ∈ ((DispInv call bl don).run σ).1 :=
    fun y hy => mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (handle_invocation_entryJ arI s ar σ J ct hct call bl don false _ hG hE hP) ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
  rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
  · show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    refine hok ?_
    exact ⟨y, top y hy, Or.inl ⟨hy1, hrel, ifP_X (fun h => by cases h) hX⟩⟩
  · rw [if_pos rfl] at hX
    refine WP.spec_bind (hPre s1 a1 y.2 hrel hX) ?_
    rintro ⟨b, s2, a2⟩ hQ
    refine hok ?_
    exact ⟨y, top y hy, Or.inr ⟨hy1, hQ⟩⟩

theorem regIdx_reply : regIdx Fl4Spec.replyRegister = layout.reg.REPLY := by
  unfold layout.reg.REPLY layout.reg.R12; rfl

/-- A cap held in a slot of `th` (IpcRecvTopH's `Hd` at `J`). -/
def JHeld (th : TypedHeap) (s : S) (c : capability.Cap) : Prop := ∃ y, IsSlot th y ∧ capV (L.mem s) y = c

/-- The relation a receive at `J` ends in. -/
abbrev RJ (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RelTopM (L := L) s σ ∧ JAt (L := L) arI AR s a σ

/-- **`receive_ipc` at `J`** [W] (KENTRY-PLAN.md item 6; IpcLeaves'
`recv_ipc_leaf` is at `IRel` only): IpcRecvTopH's `RecvLeavesH.ipc` at `RJ`, the
endpoint cap and the reply cap (if any) held in slots of `th` (`JHeld`). -/
def JRecvIpcHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (blocking : Bool) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **`receive_signal` at `J`** [W] (KENTRY-PLAN.md item 5; IpcLeaves'
`recv_sig_leaf` is at `IRel` only): IpcRecvTopH's `RecvLeavesH.sig` at `RJ`, the
notification cap held in a slot of `th` (`JHeld`). -/
def JRecvSigHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (blocking : Bool) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) →
    notification.receive_signal st arI s a ct p blocking ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac blocking σ).1, RJ (L := L) arI AR r.1 r.2 z.2 ⦄

set_option maxHeartbeats 8000000 in
/-- **`handle_recv` at `J`**: IpcRecvTop's `handle_recv_refines` at `RJ`,
the registers, the cap lookup, the caps' objects, the bound TCB and the cap
faults (`JAtZ.faultHypJZ`, with the receive flag) proved from `JAtZ`; the
two receive leaves named (`JRecvIpcHyp`, `JRecvSigHyp` [W]). `hni`, `hnq`,
`hvfh`: JEntryAt's `ni`, `ctnq`, `vfh` at the receive's state. -/
theorem handle_recvJ (hAT : P0.ArchTotal arI) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (blocking canReply : Bool)
    (hIpc : JRecvIpcHyp (L := L) arI AR Z.th ct blocking s a σ) (hSig : JRecvSigHyp (L := L) arI AR Z.th ct blocking s a σ) :
    syscall.handle_recv st arI s a blocking canReply ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1, RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  refine handle_recv_refinesH (RJ (L := L) arI AR) (JHeld (L := L) Z.th s) s a σ blocking canReply ct hct hcur hks
    (by rw [← regIdx_cap]; exact hxs.regs _) (by rw [← regIdx_reply]; exact hxs.regs _)
    (fun cptr => lookup_cap_refines Z.th s σ hR hV ct htcb cptr)
    (fun cptr => WP.spec_mono (lookup_cap_held Z.th s σ hR hV ct htcb cptr) fun r hr c hc => ⟨?_, hr c hc⟩)
    ⟨hIpc, hSig, recv_bound_leaf hI.1 J.obj, fun cptr lf lf' h =>
      J.faultHypJZ hAT hni hct hnq hvfh ⟨cptr, true, lf, lf', rfl, by rw [ofBl_toBl64], h⟩⟩
  obtain ⟨y, hy, hcv⟩ := hr c hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  cases c with
  | Endpoint p b x1 x2 x3 x4 =>
    obtain ⟨xe, hke, -⟩ := hI.1.ep p (J.hset.1 p ((hJ.typed _ hy).1 p b x1 x2 x3 x4 hcv))
    exact ⟨xe, hke⟩
  | Reply p g =>
    obtain ⟨xr, hkr, -⟩ := hI.1.reply p (J.hset.2.2 p ((hJ.typed _ hy).2.2 p g hcv))
    exact ⟨xr, hkr⟩
  | Notification p b w r =>
    obtain ⟨xn, hkn, -⟩ := hI.1.ntfn p (J.capN ⟨y, b, w, r, hy, hcv⟩).1
    exact ⟨xn, hkn⟩
  | _ => trivial

/-- FL4's invoking syscall numbers with `handle_invocation`'s flags
(`dispatch_syscall`): `SysSend` (`handleSend true`), `SysNBSend`
(`handleSend false`), `SysCall` (`handleCall`). -/
def InvSys (n : I64) (call bl don : Bool) : Prop :=
  (n = fl4_abi.syscall.SysSend ∧ call = false ∧ bl = true ∧ don = false) ∨
  (n = fl4_abi.syscall.SysNBSend ∧ call = false ∧ bl = false ∧ don = false) ∨
  (n = fl4_abi.syscall.SysCall ∧ call = true ∧ bl = true ∧ don = true)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_syscall` for `SysSend`, `SysNBSend`, `SysCall` at `J`**
against `handleSend true`, `handleSend false`, `handleCall` with FL4's
dispatcher (`DispInv`), the preemption path the premise `hPre`
(`invoke_afterJ`). -/
theorem dispatch_invokeJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
  have h := invoke_afterJ arI s ar σ J ct hct call bl don hG hE hP Q hPre
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  have n65 : fl4_abi.syscall.SysNBSend ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysNBSend fl4_abi.syscall.SysSend; decide
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl]; exact h
  · rw [if_neg n65, if_pos rfl]; exact h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact h

/-- FL4's receiving syscall numbers with `handle_recv`'s flags
(`dispatch_syscall`): `SysRecv`, `SysNBRecv`, `SysWait`, `SysNBWait`
(`handleRecv true true`, `false true`, `true false`, `false false`). -/
def RecvSys (n : I64) (bl cr : Bool) : Prop :=
  (n = fl4_abi.syscall.SysRecv ∧ bl = true ∧ cr = true) ∨
  (n = fl4_abi.syscall.SysNBRecv ∧ bl = false ∧ cr = true) ∨
  (n = fl4_abi.syscall.SysWait ∧ bl = true ∧ cr = false) ∨
  (n = fl4_abi.syscall.SysNBWait ∧ bl = false ∧ cr = false)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_syscall` for the receiving syscalls at `J`** (`handle_recvJ`):
against `handleRecv bl cr` (the spec's `withoutPreemption` of it). -/
theorem dispatch_recvJ (hAT : P0.ArchTotal arI) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (number : I64) (bl cr : Bool) (hn : RecvSys number bl cr)
    (hIpc : JRecvIpcHyp (L := L) arI AR Z.th ct bl s a σ) (hSig : JRecvSigHyp (L := L) arI AR Z.th ct bl s a σ) :
    syscall.dispatch_syscall st arI s a number ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) bl cr σ).1, RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have h := handle_recvJ arI hAT s a σ J hni hct hnq hvfh bl cr hIpc hSig
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_pos rfl]; exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysRecv; decide)]
    rw [if_pos rfl]; exact h
  · rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_pos rfl]; exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysWait; decide)]
    rw [if_pos rfl]; exact h

/-- The spec syscall of an invoking syscall's flags (`InvSys`). -/
def invSysOf (call bl : Bool) : Fl4Spec.Syscall :=
  if call then .sysCall else if bl then .sysSend else .sysNBSend

/-- The invoking branches of `fl4HandleEvent true` are `DispInv`. -/
theorem fl4HandleSyscall_inv {n : I64} {call bl don : Bool} (hn : InvSys n call bl don) :
    Fl4Spec.fl4HandleSyscall (Z := Unit) true (invSysOf call bl) = DispInv call bl don := by
  rcases hn with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ <;> rfl

/-- The spec syscall of a receiving syscall's flags (`RecvSys`). -/
def recvSysOf (bl cr : Bool) : Fl4Spec.Syscall :=
  match bl, cr with
  | true, true => .sysRecv
  | false, true => .sysNBRecv
  | true, false => .sysWait
  | false, false => .sysNBWait

/-- The receiving branches of `fl4HandleEvent rep` are `withoutPreemption
(handleRecv bl cr)`. -/
theorem fl4HandleSyscall_recv (rep bl cr : Bool) :
    Fl4Spec.fl4HandleSyscall (Z := Unit) rep (recvSysOf bl cr) =
      Fl4Spec.withoutPreemption (Fl4Spec.handleRecv bl cr) := by
  cases bl <;> cases cr <;> rfl

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJ` against `fl4HandleEvent true`'s branch.** -/
theorem dispatch_invokeJE [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR Q (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ := by
  rw [fl4HandleSyscall_inv hn]
  exact dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP Q hPre

set_option maxHeartbeats 4000000 in
/-- **`dispatch_recvJ` against `fl4HandleEvent rep`'s branch** (the spec's
outcome `.ok ()`). -/
theorem dispatch_recvJE (rep : Bool) (hAT : P0.ArchTotal arI) (s : S) (a : A)
    (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (number : I64) (bl cr : Bool) (hn : RecvSys number bl cr)
    (hIpc : JRecvIpcHyp (L := L) arI AR Z.th ct bl s a σ) (hSig : JRecvSigHyp (L := L) arI AR Z.th ct bl s a σ) :
    syscall.dispatch_syscall st arI s a number ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) rep (recvSysOf bl cr)).run σ).1,
        y.1 = .ok () ∧ RJ (L := L) arI AR r.1 r.2 y.2 ⦄ := by
  refine WP.spec_mono (dispatch_recvJ arI hAT s a σ J hni hct hnq hvfh number bl cr hn hIpc hSig) ?_
  rintro r ⟨z, hz, hR⟩
  rw [fl4HandleSyscall_recv]
  exact ⟨_, mem_liftE (ε := Unit) hz, rfl, hR⟩

end

end

end Fl4Proofs.P3
