/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch7 (D), item 12):
**`kernel_entryJ`: FL4's `handle_syscall` for a native system call against
Fl4Spec's `fl4KernelEntrySyscall true c`** (Ext/Entry: the `FaultIP` write,
`fl4HandleEvent` (time stamp, budget check, FL4's dispatcher), the preemption
path, `fl4Awaken`, `schedule`, `activateThread`).

Composition (FL4 side in order):
* `FAULT_IP := NEXT_IP - 2` (M1): `reg_wr_irel` + `JAtZ.regWrJ`, spec side
  `fl4SyscallFaultIP_eq` (`faultIPSt`).
* the trap flag (M2, out of scope: `hflag` [S]) and the number range
  (`NativeSys.range`: the native numbers are in [SYSCALL_MIN, SYSCALL_MAX]).
* `budget_ok`: `JAtZ.budgetOkJ` (runs) with `JAtZ.budgetOkF` (stops, no
  timeout-fault send) or `JAtZ.budgetOkT` (stops, the timeout fault blocks the
  current thread) (`KBudget`).
* `dispatch_syscall` (`dispatch_allJ`): `dispatch_invokeJEPZJ` (Send/NBSend/
  Call, preemption to `PPQ`), `dispatch_recvJL` (Recv/NBRecv/Wait/NBWait),
  `dispatch_yieldJ` (Yield); ReplyRecv/NBSendRecv/NBSendWait: `KDispHyps.mid`
  [W] (M6: the receive at the mid state; sch7 (C) step 2 not done).
* `finish`: `jat_finishJ2` from the `JAtZ` after the dispatch or the stopping
  budget check (`KFinAt` at those states); after a preemption `KPreFinHyp`
  [W] (`after_invocation`'s post `PPQ` is `JHoleAt`/`XTopAt`, not `JAt`).

Spec side: `specFront c σ` (the `FaultIP` write then the handled event),
`mem_kentry` (an outcome of `specFront` then of `fl4Awaken; schedule;
activateThread` is an outcome of `fl4KernelEntrySyscall true c`),
`fail_kentry` (a failing preemption path fails the whole entry).

Premises at intermediate states are stated at the spec-reachable ones only
(`BudgetAt`, `specFront`, `PreemptedAt`), never at every `JAt` state.
-/
import Fl4Proofs.P3.XTopJointMidRun
import Fl4Proofs.P3.XTopJointSchedRF3
import Fl4Proofs.P3.XTopJointPreemptI
import Fl4Proofs.P3.XTopJointRecvIpcLink
import Fl4Proofs.P3.XTopJointYieldSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec

theorem fail_bind_l {σs α β : Type} {m : NonDet σs α} {f : α → NonDet σs β} {s : σs} (h : (m s).2) :
    ((m >>= f) s).2 := Or.inl h

theorem fail_bind_r {σs α β : Type} {m : NonDet σs α} {f : α → NonDet σs β} {s : σs} {x : α × σs}
    (hx : x ∈ (m s).1) (h : (f x.1 x.2).2) : ((m >>= f) s).2 := Or.inr ⟨x, hx, h⟩

theorem mem_bind_elim {σs α β : Type} {m : NonDet σs α} {f : α → NonDet σs β} {s : σs} {y : β × σs}
    (h : y ∈ ((m >>= f) s).1) : ∃ x ∈ (m s).1, y ∈ (f x.1 x.2).1 := h

theorem mem_handleE_ok {σs ε ε' α : Type} {m : NonDetE σs ε α} {h : ε → NonDetE σs ε' α} {s s' : σs} {a : α}
    (hx : (.ok a, s') ∈ (m.run s).1) :
    ((.ok a, s') : Except ε' α × σs) ∈ ((NonDetE.handleE m h).run s).1 :=
  mem_bind_nd (m := ExceptT.run m) (x := ((.ok a : Except ε α), s')) hx rfl

theorem mem_handleE_err {σs ε ε' α : Type} {m : NonDetE σs ε α} {h : ε → NonDetE σs ε' α} {s s' : σs} {e : ε}
    {y : Except ε' α × σs} (hx : (.error e, s') ∈ (m.run s).1) (hy : y ∈ ((h e).run s').1) :
    y ∈ ((NonDetE.handleE m h).run s).1 :=
  mem_bind_nd (m := ExceptT.run m) (x := ((.error e : Except ε α), s')) hx hy

theorem fail_handleE_err {σs ε ε' α : Type} {m : NonDetE σs ε α} {h : ε → NonDetE σs ε' α} {s s' : σs} {e : ε}
    (hx : (.error e, s') ∈ (m.run s).1) (hf : ((h e).run s').2) :
    ((NonDetE.handleE m h).run s).2 :=
  fail_bind_r (m := ExceptT.run m) (x := ((.error e : Except ε α), s')) hx hf

theorem fail_liftE {σs ε α : Type} {m : NonDet σs α} {s : σs} (h : (m s).2) :
    ((NonDetE.liftE (ε := ε) m).run s).2 := by
  unfold NonDetE.liftE
  rw [ExceptT.run_lift]
  exact fail_bind_l h

/-- The spec's time stamp and budget check (`fl4HandleEvent`'s first two
statements, as `JAtZ.budgetOkJ` states them). -/
def specBudget (σ : State Unit) : Set (Bool × State Unit) × Prop :=
  (updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart) σ

/-- The `FaultIP` write then the handled event: what `fl4CallKernel` runs
before `fl4Awaken`. -/
def specFront (c : Syscall) (σ : State Unit) : Set (Except Unit Unit × State Unit) × Prop :=
  (fl4SyscallFaultIP (Z := Unit) σ.curThread >>= fun _ =>
    ExceptT.run (NonDetE.handleE (fl4HandleEvent true (.syscallEvent c))
      (fun _ => withoutPreemption preemptionPath))) σ

/-- The spec's `FaultIP` write as a state. -/
def faultIPSt (σ : State Unit) (t : ObjRef) (x : Tcb) : State Unit :=
  updK σ t (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))

theorem fl4SyscallFaultIP_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    fl4SyscallFaultIP (Z := Unit) t σ = ({((), faultIPSt σ t x)}, False) := by
  unfold fl4SyscallFaultIP asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Unit) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Unit) ((NonDet.bind (getRegister nextInstructionRegister)
      fun n => setRegister faultRegister (n - 2)) (archTcbContextGet x.tcbArch)) σ =
      ({(((), ⟨(archTcbContextGet x.tcbArch).userFpuState,
        Function.update (archTcbContextGet x.tcbArch).userRegs .faultIP
          ((archTcbContextGet x.tcbArch).userRegs .nextIP - 2)⟩), σ)}, False) by
    simp only [NonDet.selectF, NonDet.bind, getRegister, setRegister, NonDet.gets, NonDet.modify,
      nextInstructionRegister, faultRegister]
    ext ⟨a, b⟩ <;> simp)]
  show ((pure _ : NonDet (State Unit) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  exact (nd_bind_one (setObject_eq (o' := KernelObject.tcb (setReg x .faultIP
    (x.tcbArch.tcbContext.userRegs .nextIP - 2))) hk rfl) _).trans rfl

/-- The handled event from a budget outcome. -/
theorem mem_fl4HandleEvent {σ0 σb : State Unit} {b : Bool} {c : Syscall}
    (hb : (b, σb) ∈ (specBudget σ0).1) {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((NonDetE.whenE (b = true) (fl4HandleSyscall (Z := Unit) true c)).run σb).1) :
    y ∈ ((fl4HandleEvent (Z := Unit) true (.syscallEvent c)).run σ0).1 := by
  obtain ⟨u, hu, hr⟩ := mem_bind_elim hb
  unfold fl4HandleEvent
  exact mem_bindE_ok (mem_liftE hu) (mem_bindE_ok (mem_liftE hr) hy)

theorem mem_whenE_true {σs ε : Type} {m : NonDetE σs ε Unit} {s : σs} {y : Except ε Unit × σs}
    (h : y ∈ (m.run s).1) : y ∈ ((NonDetE.whenE (true = true) m).run s).1 := by
  unfold NonDetE.whenE; rw [if_pos rfl]; exact h

theorem mem_whenE_false {σs ε : Type} {m : NonDetE σs ε Unit} {s : σs} :
    ((.ok (), s) : Except ε Unit × σs) ∈ ((NonDetE.whenE (false = true) m).run s).1 := by
  unfold NonDetE.whenE; rw [if_neg (by decide)]; rfl

theorem mem_specFront {σ σ0 : State Unit} {c : Syscall} (hF : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    {x : Except Unit Unit × State Unit}
    (hx : x ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) true (.syscallEvent c))
      (fun _ => withoutPreemption preemptionPath)).run σ0).1) : x ∈ (specFront c σ).1 :=
  mem_bind_nd hF hx

/-- **An outcome of `specFront` then of `fl4Awaken; schedule;
activateThread` is an outcome of the syscall entry.** -/
theorem mem_kentry {σ σ' : State Unit} {c : Syscall} {x : Except Unit Unit × State Unit}
    (hx : x ∈ (specFront c σ).1)
    (hT : ((), σ') ∈ ((fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) x.2).1) :
    ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1 := by
  obtain ⟨u, hu, hh⟩ := mem_bind_elim hx
  unfold fl4KernelEntrySyscall fl4CallKernel
  exact mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd hu (mem_bind_nd hh hT))

/-- **A failing preemption path fails the syscall entry.** -/
theorem fail_kentry {σ σ0 σb σ1 : State Unit} {c : Syscall}
    (hF : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1) (hb : (true, σb) ∈ (specBudget σ0).1)
    (hy : (.error (), σ1) ∈ ((fl4HandleSyscall (Z := Unit) true c).run σb).1)
    (hp : (preemptionPath (Z := Unit) σ1).2) : (fl4KernelEntrySyscall (Z := Unit) true c σ).2 := by
  unfold fl4KernelEntrySyscall fl4CallKernel
  exact fail_bind_r (x := (σ.curThread, σ)) rfl (fail_bind_r hF (fail_bind_l
    (fail_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (fail_liftE hp))))

end Spec

/-! ## Native system calls -/

/-- ReplyRecv / NBSendRecv / NBSendWait (invocation, then a receive). -/
def MidSys (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  (n = fl4_abi.syscall.SysReplyRecv ∧ c = .sysReplyRecv) ∨
  (n = fl4_abi.syscall.SysNBSendRecv ∧ c = .sysNBSendRecv) ∨
  (n = fl4_abi.syscall.SysNBSendWait ∧ c = .sysNBSendWait)

/-- **FL4's native system call numbers and their spec `Syscall`** (M2: the
debug / TLS numbers and unknown numbers are out of scope). -/
def NativeSys (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  (∃ call bl don, InvSys n call bl don ∧ c = invSysOf call bl) ∨
  (∃ bl cr, RecvSys n bl cr ∧ c = recvSysOf bl cr) ∨
  (n = fl4_abi.syscall.SysYield ∧ c = .sysYield) ∨ MidSys n c

theorem NativeSys.num {n : I64} {c : Fl4Spec.Syscall} (h : NativeSys n c) :
    n = fl4_abi.syscall.SysCall ∨ n = fl4_abi.syscall.SysReplyRecv ∨ n = fl4_abi.syscall.SysNBSendRecv ∨
    n = fl4_abi.syscall.SysNBSendWait ∨ n = fl4_abi.syscall.SysSend ∨ n = fl4_abi.syscall.SysNBSend ∨
    n = fl4_abi.syscall.SysRecv ∨ n = fl4_abi.syscall.SysNBRecv ∨ n = fl4_abi.syscall.SysWait ∨
    n = fl4_abi.syscall.SysNBWait ∨ n = fl4_abi.syscall.SysYield := by
  rcases h with ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨h, -⟩ | h
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  · simp [h]
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- The native numbers are in `[SYSCALL_MIN, SYSCALL_MAX]`. -/
theorem NativeSys.range {n : I64} {c : Fl4Spec.Syscall} (h : NativeSys n c) :
    ¬ n < fl4_abi.syscall.SYSCALL_MIN ∧ ¬ n > fl4_abi.syscall.SYSCALL_MAX := by
  rcases h.num with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    (simp only [fl4_abi.syscall.SYSCALL_MIN, fl4_abi.syscall.SYSCALL_MAX, fl4_abi.syscall.SysCall,
      fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait,
      fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv,
      fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysYield]) <;> decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The budget outcomes the spec reaches after the `FaultIP` write. -/
def BudgetAt (σ σb : Fl4Spec.State Unit) (b : Bool) : Prop :=
  ∃ σ0, ((), σ0) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 ∧ (b, σb) ∈ (specBudget σ0).1

/-- The preempted invocation outcomes the spec reaches. -/
def PreemptedAt (c : Fl4Spec.Syscall) (σ σ1 : Fl4Spec.State Unit) : Prop :=
  ∃ σb, BudgetAt σ σb true ∧ (.error (), σ1) ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true c).run σb).1

/-- **The budget-check premises at the entry state after the `FaultIP`
write** (`JAtZ.budgetOkJ` / `budgetOkF` / `budgetOkT`): the clock [P]
`NowAgree`, `CurInv` and `OffReady` [J] (ScEntryRd's `budget_ok_offReady`;
the write changes one register, which neither reads), and either no
timeout-fault send (`NoTmoSend`) or the premises of the blocking timeout
fault (`budgetOkT`: the current thread in no ready queue (l4v
`ct_not_in_q`), running or restarting, its endpoint handler can block it,
a non-round-robin SC). -/
structure KBudget (a : A) (σ0 : Fl4Spec.State Unit) : Prop where
  now : NowAgree arI a σ0
  cur : CurInv σ0
  off : OffReady σ0
  tmo : NoTmoSend σ0 ∨ ((∀ d p, σ0.curThread ∉ σ0.readyQueues d p) ∧ ∃ xt, σ0.kheap σ0.curThread = some (.tcb xt) ∧
    (xt.tcbState = .running ∨ xt.tcbState = .restart) ∧ ∃ (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
      xt.tcbTimeoutHandler = .endpointCap p bd r ∧
      (∀ x n, σ0.kheap σ0.curSc = some (.schedContext x n) → x.scPeriod ≠ 0) ∧
      (∀ xe, σ0.kheap p = some (.endpoint xe) → Endp.CanBlock false xe))

/-- **The dispatch premises at the state after a passing budget check**
(per syscall class): the invoking ones' `JEntryGlob` / `JEntryAt` / `JPathAt`
(the entry premises of `dispatch_invokeJEPZJ`, [P]/[J]/[W] per field), the
receiving ones' `ct_not_in_q` / `valid_fault_handler` [J], and for
ReplyRecv / NBSendRecv / NBSendWait the whole dispatch [W] (`mid`: M6, the
receive after the invocation at the mid state `JMid`; sch7 (C) step 2). -/
structure KDispHyps (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : MidSys n c → syscall.dispatch_syscall st arI s a n ⦃ r =>
    DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄

/-- **The finish premises at a state before `finish`** (`jat_finishJ2`'s
state- and ghost-dependent premises: `hd` [J] (NdOK), `hVt` [J], `hW` [W],
`ArchSwF`/`ArchNdF` [P], `FpuOwnOK` [J], `SniHyp`/`SendHyp` [P], `hTail`
(the CR3 [P] fact)). -/
structure KFinAt (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  vt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64
  w : SignalRestJHyp (L := L) arI AR H Cs
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  fo : FpuOwnOK σ
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄

/-- What the entry ends in: the spec entry fails, or one of its outcomes is
related (`RJ`). -/
def KPost (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ'

/-- **[W] `finish` after a preempted invocation** (KENTRY-PLAN item 7 with
item 11): from the post of `after_invocation (Err)` (`PPQ`: a `JHoleAt` or
`XTopAt` state after an outcome of `preemption_path`, or a spec failure),
FL4's `finish` refines `fl4Awaken; schedule; activateThread` from that
outcome. l4v: `call_kernel`'s `handle_preemption` then `schedule` /
`activate_thread` from `invs` (Syscall_AI `he_invs`, `schedule_invs`).
Missing at J: `JAt` after the preemption path (the hole is closed only for
the covered cases, XTopJointPreemptZ), so `jat_finishJ2` does not apply. -/
def KPreFinHyp (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ σ1, PreemptedAt c σ σ1 → ∀ r : S × A, PPQ (L := L) arI AR σ1 r →
    syscall.finish st arI r.1 r.2 ⦃ r' => (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ⦄

variable {arI}

set_option maxHeartbeats 4000000 in
/-- **`dispatch_syscall` for every native system call at `J`** after a
passing budget check (module docstring). -/
theorem dispatch_allJ [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps (L := L) arI AR Z H Cs D s a σ n c)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypJ (L := L) arI AR)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP⟩ := hK.inv _ call bl don hct hi
    exact dispatch_invokeJEPZJ s a σ J _ hct n call bl don hi hG hE hP hARI hA hnd hPP hmrt hIP hNS hRest
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hmb a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2⟩⟩
  · exact hK.mid hm

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`** (KENTRY-PLAN item
12; module docstring): FL4's `handle_syscall` refines Fl4Spec's
`fl4KernelEntrySyscall true c` (the `FaultIP` write, `fl4HandleEvent true`,
the preemption path, `fl4Awaken`, `schedule`, `activateThread`), `RJ` after.

Premises: at the entry `JAtZ` and `Entered` [J] (l4v `ct_running`,
`scheduler_action = resume_cur_thread`); the trap flag clear `hflag` [S]
(M2); the budget-check premises after the `FaultIP` write `hB` (`KBudget`);
the dispatch premises at the budget outcomes `hK` (`KDispHyps`, incl. the
M6 [W] for the mid-receive syscalls); the finish premises at the states
before `finish` `hFin` (`KFinAt`); `finish` after a preemption `hPF` [W]
(`KPreFinHyp`); the platform/global premises of the composed theorems
(`hARI` `hA` `hnd` `hPP` `hmrt` `hmb` `hIP` `hNS` [P]/[S], `hRest` [W]
(JPreemptRestHypJ), `hT` `hmax` `htu` [P], `hvm` [S]). -/
theorem kernel_entryJ [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAt (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hPF : KPreFinHyp (L := L) arI AR c σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypJ (L := L) arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hvm : ∀ s1 a1 σ1, JAt (L := L) arI AR s1 a1 σ1 → ∀ x, σ1.kheap σ1.curThread = some (.tcb x) →
      x.tcbState ≠ .runningVM) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hBud : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart)
          (faultIPSt σ σ.curThread x) = ({(true, σ')}, False) ∧
        σ'.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σ'.curThread = (faultIPSt σ σ.curThread x).curThread ∧
        σ'.curSc = (faultIPSt σ σ.curThread x).curSc ∧
        σ'.schedulerAction = (faultIPSt σ σ.curThread x).schedulerAction ∧
        σ'.idleThread = (faultIPSt σ σ.curThread x).idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget (faultIPSt σ σ.curThread x)).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
    rcases hBu.tmo with hnt | ⟨hnq, xt, hkt, hrr, p, bd, rr, hth, hper, hcb⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
          obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl, _, Ac', Lst', D', J'⟩
          unfold specBudget faultIPSt
          rw [he]; exact Set.mem_singleton _⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb)) fun r ⟨h1, h2⟩ =>
          ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩⟩
  refine WP.spec_bind hBud ?_
  rintro ⟨b, s2, a1⟩ ⟨hTr, hFa⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1 J'
    exact WP.spec_mono (jat_finishJ2 s2 a1 σb J' F.hd hnd hA F.vt F.w hmb F.arch F.archNd F.fo F.sni F.send hT
      F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    refine WP.spec_bind (dispatch_allJ s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hARI hA hnd hPP hmrt hmb hIP hNS hRest hmax htu) ?_
    rintro ⟨s3, a2⟩ ⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, Jm⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2 Jm
      exact WP.spec_mono (jat_finishJ2 s3 a2 σm Jm F.hd hnd hA F.vt F.w hmb F.arch F.archNd F.fo F.sni F.send hT
        F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (hPF σ1 hPA (s3, a2) hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩

end

end

end Fl4Proofs.P3
