/-
P3 (DESIGN.md §9): **`syscall::handle_invocation`** against l4v's
`handle_invocation` with FL4's dispatcher (`fl4HandleInvocation`,
`Fl4Spec/Ext/Invocation`): `handle_invocation_refines`.

The composition: the cap lookup (`lookup_slot_refines`, the cap at the
slot), the decode and invocation of the cap (`TopPostD`, from
`decode_invocation_refinesD` for the CSpace, untyped and domain caps), and
the tails: the success tail (the thread still `Restart`: the reply when
called, then `Running`), the error reply, and the fault handler of a failed
lookup. The result `HIPost`: an outcome of `fl4HandleInvocation` of FL4's
kind (done, or preempted), whose state is related to FL4's (`RelTop`: a
placed typed heap and a ghost tree with the CSpace relation, `MdbInv`,
`FinInv`, and `DomRel`).

Hypotheses for the IPC proofs:
* the reads of the front end (the message info, the IPC buffer, the extra
  caps, the message registers), as explicit values with their spec
  counterparts (`get_message_info`, `lookup_ipc_buffer`, `lookup_extra_caps`,
  `get_mrs`); the decode's argument relations are in `hDec`;
* `ReplyHyp`: the message-register and reply writes (`reply_success_empty`
  or no reply, then `set_thread_state Running`, against the spec's
  `get_thread_state`, `reply_from_kernel (0, reply)`, `set_thread_state
  Running`; `reply_error` against `reply_from_kernel (msg_from_syscall_error
  e)`), from related states;
* `FaultHypAt`: `handle_fault` against `handle_fault`, for the related
  faults of the lookups.

A decode that replies itself (IO port `In` called: FL4 sets the message
registers and `Running` in the decode) gives `TopPostR` (`DecOKR`) instead
of `TopPostD`: `decode_invocation_ioport_in_call`, from `PortInCallHyp`
(the access and the reply, against the spec's `In` invocation and success
tail).
-/
import Fl4Proofs.P3.TopF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The spec's `syscall` -/

section
open Fl4Spec

theorem mem_syscall_fault {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ σ' : State Unit} {f : Fault} {z : γ × State Unit}
    (h1 : (.error f, σ') ∈ ((ExceptT.run mF) σ).1) (h2 : z ∈ (hF f σ').1) :
    ((.ok z.1, z.2) : Except Unit γ × State Unit) ∈ ((syscall mF hF mE hE mFin).run σ).1 := by
  unfold syscall withoutPreemption
  exact mem_bindE_ok (a := (Except.error f : Except Fault α)) (s' := σ') (mem_liftE (x := ((Except.error f : Except Fault α), σ')) h1) (mem_liftE h2)

theorem mem_syscall_err {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ σ' σ'' : State Unit} {a : α} {e : SyscallError} {z : γ × State Unit}
    (h1 : (.ok a, σ') ∈ ((ExceptT.run mF) σ).1) (h2 : (.error e, σ'') ∈ ((ExceptT.run (mE a)) σ').1)
    (h3 : z ∈ (hE e σ'').1) :
    ((.ok z.1, z.2) : Except Unit γ × State Unit) ∈ ((syscall mF hF mE hE mFin).run σ).1 := by
  unfold syscall withoutPreemption
  exact mem_bindE_ok (a := (Except.ok a : Except Fault α)) (s' := σ') (mem_liftE (x := ((Except.ok a : Except Fault α), σ')) h1)
    (mem_bindE_ok (a := (Except.error e : Except SyscallError β)) (s' := σ'') (mem_liftE (x := ((Except.error e : Except SyscallError β), σ'')) h2) (mem_liftE h3))

theorem mem_syscall_fin {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ σ' σ'' : State Unit} {a : α} {b : β} {y : Except Unit γ × State Unit}
    (h1 : (.ok a, σ') ∈ ((ExceptT.run mF) σ).1) (h2 : (.ok b, σ'') ∈ ((ExceptT.run (mE a)) σ').1)
    (h3 : y ∈ ((mFin b).run σ'').1) :
    y ∈ ((syscall mF hF mE hE mFin).run σ).1 := by
  unfold syscall withoutPreemption
  exact mem_bindE_ok (a := (Except.ok a : Except Fault α)) (s' := σ') (mem_liftE (x := ((Except.ok a : Except Fault α), σ')) h1)
    (mem_bindE_ok (a := (Except.ok b : Except SyscallError β)) (s' := σ'') (mem_liftE (x := ((Except.ok b : Except SyscallError β), σ'')) h2) h3)

theorem mem_of_eq {σ α : Type} {m : NonDet σ α} {s : σ} {x : α × σ} (h : m s = ({x}, False)) : x ∈ (m s).1 := by
  rw [h]; rfl

theorem run_handleE_ok {σ ε ε' α : Type} {m : NonDetE σ ε α} {h : ε → NonDetE σ ε' α} {s s' : σ} {a : α}
    (hm : m.run s = ({(.ok a, s')}, False)) : (NonDetE.handleE m h).run s = ({(.ok a, s')}, False) := by
  unfold NonDetE.handleE
  rw [ExceptT.run_mk]
  show (ExceptT.run m >>= _) s = _
  rw [nd_bind_one hm]; rfl

theorem run_handleE_err {σ ε ε' α : Type} {m : NonDetE σ ε α} {h : ε → NonDetE σ ε' α} {s s' : σ} {e : ε}
    (hm : m.run s = ({(.error e, s')}, False)) : (NonDetE.handleE m h).run s = (h e).run s' := by
  unfold NonDetE.handleE
  rw [ExceptT.run_mk]
  show (ExceptT.run m >>= _) s = _
  rw [nd_bind_one hm]

end

/-! ## The phases of `fl4HandleInvocation` -/

section
open Fl4Spec

/-- The spec's success tail of `handle_invocation`. -/
def specTail (calling : Bool) (thread : ObjRef) (reply : List Data) :
    SMonad Unit Unit := do
  let state ← getThreadState thread
  match state with
  | .restart => do
    NonDet.when calling <|
      replyFromKernel thread (0, reply)
    setThreadState thread .running
  | _ => return ()

/-- The lookup phase. -/
def hiMF (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- The decode phase. -/
def hiME (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) (firstPhase : Bool) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4Invocation :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs thread buffer info
    fl4DecodeInvocation firstPhase info.miLabel args cptr slot cap extracaps buffer

/-- The invocation phase. -/
def hiMFin (thread : ObjRef) (calling blocking canDonate : Bool) : Fl4Invocation → PMonad Unit Unit :=
  fun oper => do
    withoutPreemption <| setThreadState thread .restart
    let reply ← fl4PerformInvocation blocking calling canDonate oper
    withoutPreemption <| do
        let state ← getThreadState thread
        match state with
        | .restart => do
          NonDet.when calling <|
            replyFromKernel thread (0, reply)
          setThreadState thread .running
        | _ => return ()

theorem hi_mem {σ : State Unit} {calling blocking canDonate firstPhase : Bool} {cptr : CapRef} {mi : MessageInfo}
    {t : ObjRef} (hcur : σ.curThread = t) (hmi : getMessageInfo (Z := Unit) t σ = ({(mi, σ)}, False))
    {y : Except Unit Unit × State Unit}
    (h : y ∈ ((syscall (hiMF t mi cptr) (fun fault => NonDet.when blocking <| handleFault t fault)
      (hiME t mi cptr firstPhase)
      (fun err => NonDet.when calling <| replyFromKernel t <| msgFromSyscallError err)
      (hiMFin t calling blocking canDonate)).run σ).1) :
    y ∈ ((fl4HandleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr).run σ).1 := by
  unfold fl4HandleInvocation
  refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE (x := (σ.curThread, σ)) rfl) ?_
  refine mem_bindE_ok (a := mi) (s' := σ) (mem_liftE (x := (mi, σ)) (by rw [hcur, hmi]; rfl)) ?_
  rw [hcur]
  exact h

theorem hiMF_lookup_err {σ : State Unit} {t : ObjRef} {mi : MessageInfo} {cptr : CapRef} {lf : LookupFailure}
    (hl : (lookupCapAndSlot (Z := Unit) t cptr).run σ = ({(.error lf, σ)}, False)) :
    ((.error (.capFault (ofBl cptr) false lf), σ) : Except Fault _ × State Unit) ∈
      (ExceptT.run (hiMF t mi cptr) σ).1 := by
  unfold hiMF
  apply mem_bindE_err
  unfold capFaultOnFailure
  rw [run_handleE_err hl]; rfl

theorem hiMF_extra_err {σ : State Unit} {t : ObjRef} {mi : MessageInfo} {cptr : CapRef} {a : Cap}
    {sl : CslotPtr} {buffer : Option ObjRef} {f : Fault}
    (hl : (lookupCapAndSlot (Z := Unit) t cptr).run σ = ({(.ok (a, sl), σ)}, False))
    (hb : lookupIpcBuffer (Z := Unit) false t σ = ({(buffer, σ)}, False))
    (he : (lookupExtraCaps (Z := Unit) t buffer mi).run σ = ({(.error f, σ)}, False)) :
    ((.error f, σ) : Except Fault _ × State Unit) ∈ (ExceptT.run (hiMF t mi cptr) σ).1 := by
  unfold hiMF capFaultOnFailure
  refine mem_bindE_ok (a := (a, sl)) (s' := σ) (by rw [run_handleE_ok hl]; rfl) ?_
  refine mem_bindE_ok (a := buffer) (s' := σ) (mem_liftE (x := (buffer, σ)) (by rw [hb]; rfl)) ?_
  apply mem_bindE_err
  rw [he]; rfl

theorem hiMF_ok {σ : State Unit} {t : ObjRef} {mi : MessageInfo} {cptr : CapRef} {a : Cap}
    {sl : CslotPtr} {buffer : Option ObjRef} {exs : List (Cap × CslotPtr)}
    (hl : (lookupCapAndSlot (Z := Unit) t cptr).run σ = ({(.ok (a, sl), σ)}, False))
    (hb : lookupIpcBuffer (Z := Unit) false t σ = ({(buffer, σ)}, False))
    (he : (lookupExtraCaps (Z := Unit) t buffer mi).run σ = ({(.ok exs, σ)}, False)) :
    ((.ok (sl, a, exs, buffer), σ) : Except Fault _ × State Unit) ∈ (ExceptT.run (hiMF t mi cptr) σ).1 := by
  unfold hiMF capFaultOnFailure
  refine mem_bindE_ok (a := (a, sl)) (s' := σ) (by rw [run_handleE_ok hl]; rfl) ?_
  refine mem_bindE_ok (a := buffer) (s' := σ) (mem_liftE (x := (buffer, σ)) (by rw [hb]; rfl)) ?_
  refine mem_bindE_ok (a := exs) (s' := σ) (by rw [he]; rfl) ?_
  rfl

theorem hiME_run {σ : State Unit} {t : ObjRef} {mi : MessageInfo} {cptr : CapRef} {fp : Bool} {a : Cap}
    {sl : CslotPtr} {buffer : Option ObjRef} {exs : List (Cap × CslotPtr)} {args : List Data}
    (hm : getMrs (Z := Unit) t buffer mi σ = ({(args, σ)}, False)) :
    ExceptT.run (hiME t mi cptr fp (sl, a, exs, buffer)) σ =
      (fl4DecodeInvocation (Z := Unit) fp mi.miLabel args cptr sl a exs buffer).run σ := by
  unfold hiME
  exact run_bind_ok (run_liftE hm) _

theorem hiMFin_ok {σ σ1 σy : State Unit} {t : ObjRef} {calling blocking canDonate : Bool} {inv : Fl4Invocation}
    {rr : List Data} {z : Unit × State Unit}
    (hst : setThreadState (Z := Unit) t .restart σ = ({((), σ1)}, False))
    (hy : (.ok rr, σy) ∈ ((fl4PerformInvocation (Z := Unit) blocking calling canDonate inv).run σ1).1)
    (hz : z ∈ (specTail calling t rr σy).1) :
    ((.ok z.1, z.2) : Except Unit Unit × State Unit) ∈ ((hiMFin t calling blocking canDonate inv).run σ).1 := by
  unfold hiMFin withoutPreemption
  refine mem_bindE_ok (a := ()) (s' := σ1) (mem_liftE (x := ((), σ1)) (by rw [hst]; rfl)) ?_
  refine mem_bindE_ok (a := rr) (s' := σy) hy ?_
  exact mem_liftE hz

theorem hiMFin_pre {σ σ1 σy : State Unit} {t : ObjRef} {calling blocking canDonate : Bool} {inv : Fl4Invocation}
    (hst : setThreadState (Z := Unit) t .restart σ = ({((), σ1)}, False))
    (hy : (.error (), σy) ∈ ((fl4PerformInvocation (Z := Unit) blocking calling canDonate inv).run σ1).1) :
    ((.error (), σy) : Except Unit Unit × State Unit) ∈ ((hiMFin t calling blocking canDonate inv).run σ).1 := by
  unfold hiMFin withoutPreemption
  refine mem_bindE_ok (a := ()) (s' := σ1) (mem_liftE (x := ((), σ1)) (by rw [hst]; rfl)) ?_
  exact mem_bindE_err hy

theorem mem_when {σ : State Unit} {b : Bool} {m : SMonad Unit Unit} {z : Unit × State Unit}
    (h : b = true → z ∈ (m σ).1) (h' : b = false → z = ((), σ)) : z ∈ (NonDet.when b m σ).1 := by
  cases b
  · rw [h' rfl]; unfold NonDet.when; simp only [Bool.false_eq_true, ↓reduceIte]; rfl
  · unfold NonDet.when; simp only [↓reduceIte]; exact h rfl

end

/-! ## The statement -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The related states: a placed typed heap and a ghost tree with the CSpace
relation (with `MdbInv`), `FinInv` and the domain schedule. -/
def RelTop (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th G, Placed th ∧ CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ DomRel (L.mem s) (L.ksb s) σ ∧
    Vs.FrameInv (L.mem s) G

/-- The message length `handle_invocation` passes to the decode. -/
def msgLen (info : msginfo.MessageInfo) (buf : U64) : U64 :=
  if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then msg.N_MSG_REGISTERS else info.length)
  else info.length

/-- FL4's success tail of `handle_invocation`. -/
def flTail (t : U64) (is_call : Bool) (s1 : S) (a1 : A) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let i ← obj.Tcb.state st t s1
  if i = sched.TS_RESTART
  then
    let s2 ← if is_call then msg.reply_success_empty st s1 t else ok s1
    let s3 ← sched.set_thread_state st s2 t sched.TS_RUNNING
    ok (core.result.Result.Ok (), s3, a1)
  else ok (core.result.Result.Ok (), s1, a1)

/-- **The message-register and reply writes** (for the IPC proofs): from
related states, FL4's success tail (the reply when called, then
`Running`, if the thread is still `Restart`) against the spec's, and FL4's
error reply against `reply_from_kernel (msg_from_syscall_error e)` when
called. -/
structure ReplyHyp (ct : U64) (is_call : Bool) : Prop where
  succ : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (rr : List Fl4Spec.Data), RelTop (L := L) s1 σ' →
    flTail (st := st) ct is_call s1 a1 ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail is_call ct.bv rr σ').1, RelTop (L := L) res.2.1 z.2 ⦄
  fail : ∀ (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (e : error.SysError) (e' : Fl4Spec.SyscallError),
    RelTop (L := L) s1 σ' → ErrRel (.Sys e) e' →
    ((if is_call then do
        let s2 ← syscall.reply_error st s1 ct e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
        Fl4Spec.replyFromKernel ct.bv (Fl4Spec.msgFromSyscallError e')) σ').1, RelTop (L := L) res.2.1 z.2 ⦄

/-- **The fault handler** (for the IPC proofs): FL4's `handle_fault` of `f`
against the spec's of `f'`, from the state of the lookup. -/
def FaultHypAt (s : S) (σ : Fl4Spec.State Unit) (ct : U64) (f : error.Fault) (f' : Fl4Spec.Fault) : Prop :=
  ∀ a : A, faults.handle_fault st arI s a ct f ⦃ r =>
    ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1, RelTop (L := L) r.1 z.2 ⦄

/-- **The result of `handle_invocation`**: an outcome of
`fl4HandleInvocation` of FL4's kind, with the states related. -/
def HIPost (σ : Fl4Spec.State Unit) (calling blocking canDonate firstPhase : Bool) (cptr : Fl4Spec.CapRef)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ y ∈ ((Fl4Spec.fl4HandleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr).run σ).1,
    ((res.1 = .Ok () ∧ y.1 = .ok ()) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
    RelTop (L := L) res.2.1 y.2

/-- **The result of a decode that replies itself** (an `In` called): the
spec's error with the state unchanged, or FL4 is done and its thread no
longer `Restart`, and the spec's decode, restart, invocation and success
tail have an outcome related to FL4's state. -/
def TopPostR (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (ct : U64) (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧
  ∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1 ∧
      ∃ z ∈ (specTail call ct.bv rr σy).1, RelTop (L := L) res.2.1 z.2

/-- The statement for one cap whose decode replies itself. -/
abbrev DecOKR (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostR (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) ct s res ⦄

theorem msgLen_eq (info : msginfo.MessageInfo) (buf : U64) :
    (if info.length > msg.N_MSG_REGISTERS
      then if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length
      else ok info.length : Result U64) = ok (msgLen info buf) := by
  unfold msgLen; split_ifs <;> rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `handle_invocation` refines l4v's `handle_invocation` with FL4's
dispatcher** (see the module docstring): from related states, the
front end's reads (`HIRead`, the explicit values `info` .. `args` with
their hypotheses), the decode and invocation of the cap at the looked-up
slot (`hDec`, as `decode_invocation_refinesD` gives it), the reply writes
(`ReplyHyp`) and the fault handler (`FaultHypAt`, for the lookup's fault
and the extra caps'). -/
theorem handle_invocation_refines (s : S) (ar : A) (σ : Fl4Spec.State Unit) (th : TypedHeap) (G : MdbGhost)
    (hP : Placed th) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hDR : DomRel (L.mem s) (L.ksb s) σ) (hFR : Vs.FrameInv (L.mem s) G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    -- the front end's reads (`HIRead`)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (hrr : (∃ e exs, r2 = .Ok e ∧ er = .ok exs) ∨
      (∃ f f', r2 = .Err f ∧ er = .error f' ∧ (blocking = true → FaultHypAt (L := L) arI s σ ct f f')))
    (args : List Fl4Spec.Data) (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    -- the fault of a failed lookup
    (hFL : blocking = true → ∀ lf lf', LookupFaultRel lf lf' →
      FaultHypAt (L := L) arI s σ ct (.Cap cptr false lf)
        (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) false lf'))
    -- the reply writes
    (hRep : ReplyHyp (L := L) ct is_call (A := A))
    -- the decode and invocation of the cap
    (hDec : ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      DecOKDF (L := L) arI s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate first_phase
        buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ∨
      DecOKR (L := L) arI s ar σ info.label (msgLen info buf) (cslotAddr sl) c blocking is_call can_donate first_phase
        buf e mi.miLabel args (Fl4Spec.toBl cptr.bv) sl exs buffer ct) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPost (L := L) σ is_call blocking can_donate first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  have hRT0 : RelTop (L := L) s σ := ⟨th, G, hP, hCR, hFI, hDR, hFR⟩
  unfold syscall.handle_invocation
  rw [hct]; simp only [bind_ok, hinfo]
  refine WP.spec_bind (lookup_slot_refines (Z := Unit) th s σ hCR.1 hCR.2.1 ct htcb cptr) ?_
  rintro r ⟨e, he, hrel, hok⟩
  cases r with
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.error lf', σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot; exact run_bind_error (s := σ) he _
      have hmF := hiMF_lookup_err (mi := mi) hl
      cases blocking
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨(.ok (), σ), hi_mem hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
          (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0⟩
      · simp only [↓reduceIte]
        refine WP.spec_bind (hFL rfl lf lf' hrel ar) ?_
        rintro ⟨s1, a1⟩ ⟨z, hz, hRT⟩
        refine (WP.spec_ok _).2 ?_
        exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
          Or.inl ⟨rfl, rfl⟩, hRT⟩
  | Ok r1 =>
    cases e with
    | error lf' => exact hrel.elim
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hCR.1.slot_cap hp hth
      have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
          ({(.ok (a, sl), σ)}, False) := by
        unfold Fl4Spec.lookupCapAndSlot
        rw [run_bind_ok he]
        simp only
        rw [run_bind_ok (run_liftE hget)]
        rfl
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, hbuf, hr2]
      rcases hrr with ⟨ex, exs, rfl, rfl⟩ | ⟨f, f', rfl, rfl, hfh⟩
      · simp only
        rw [msgLen_eq]; simp only [bind_ok]
        have hca' : absCap c = a := hca.2
        subst hca'
        have hmF := hiMF_ok (mi := mi) hl hbuffer her
        have hmE := hiME_run (cptr := Fl4Spec.toBl cptr.bv) (fp := first_phase) (a := absCap c) (sl := sl)
          (exs := exs) hmrs
        rcases hDec sl c ex exs hc hget rfl rfl with hD | hD
        swap
        · refine WP.spec_bind hD ?_
          rintro ⟨r3, s1, a1⟩ (⟨e3, he3, hs1, e', hdec, herr⟩ | ⟨hok3, hne, inv, hdec, σ1, hst, rr, σy, hy, z, hz, hRT⟩)
          · simp only at he3 hs1
            subst he3 hs1
            cases e3 with
            | Sys e2 =>
              refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 herr) ?_
              rintro res ⟨hres, z, hz, hRT⟩
              exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
                Or.inl ⟨hres, rfl⟩, hRT⟩
            | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
            | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          simp only at hok3; subst hok3
          refine WP.spec_bind (tcb_state_spec' (st := st) s1 ct) ?_
          rintro v rfl
          rw [if_neg hne]
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
            (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨rfl, rfl⟩, hRT⟩
        refine WP.spec_bind hD ?_
        rintro ⟨r3, s1, a1⟩ hq
        rcases hq with ⟨e3, he3, hs1, e', hdec, herr⟩ |
            ⟨inv, hdec, σ1, hst, y, hy, th', G', hcase, hP', hCR', hFI', hDR', hFR'⟩
        · simp only at he3 hs1
          subst he3 hs1
          cases e3 with
          | Sys e2 =>
            refine WP.spec_mono (hRep.fail _ a1 σ e2 e' hRT0 herr) ?_
            rintro res ⟨hres, z, hz, hRT⟩
            exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_err hmF (by rw [hmE, hdec]; rfl) hz),
              Or.inl ⟨hres, rfl⟩, hRT⟩
          | Fault _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Lookup _ => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
          | Preempted => exact absurd herr (by rintro (h | ⟨n, h, -⟩) <;> cases h)
        · rcases hcase with ⟨hok3, rr, hyr⟩ | ⟨hpre, hyr⟩
          · simp only at hok3
            subst hok3
            refine WP.spec_mono (hRep.succ s1 a1 y.2 rr ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩) ?_
            rintro res ⟨hres, z, hz, hRT⟩
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_ok (by rw [← hcur]; exact hst) hy hz)), Or.inl ⟨hres, rfl⟩, hRT⟩
          · simp only at hpre
            subst hpre
            refine (WP.spec_ok _).2 ?_
            obtain ⟨y1, y2⟩ := y
            simp only at hyr; subst hyr
            exact ⟨(.error (), y2), hi_mem hcur hmi (mem_syscall_fin hmF (by rw [hmE]; exact hdec.1)
              (hiMFin_pre (by rw [← hcur]; exact hst) hy)), Or.inr ⟨rfl, rfl⟩,
              ⟨th', G', hP', hCR', hFI', hDR', hFR'⟩⟩
      · simp only
        have hmF := hiMF_extra_err (cptr := Fl4Spec.toBl cptr.bv) hl hbuffer her
        cases blocking
        · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨(.ok (), σ), hi_mem hcur hmi (mem_syscall_fault (z := ((), σ)) hmF
            (mem_when (fun h => by cases h) (fun _ => rfl))), Or.inl ⟨rfl, rfl⟩, hRT0⟩
        · simp only [↓reduceIte]
          refine WP.spec_bind (hfh rfl ar) ?_
          rintro ⟨s1, a1⟩ ⟨z, hz, hRT⟩
          refine (WP.spec_ok _).2 ?_
          exact ⟨(.ok z.1, z.2), hi_mem hcur hmi (mem_syscall_fault hmF (mem_when (fun _ => hz) (fun h => by cases h))),
            Or.inl ⟨rfl, rfl⟩, hRT⟩

end

/-! ## `In` called -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- FL4's `In` after the checks: `Restart`, the port access, the reply when
called, `Running`. -/
def portInTail (s : S) (a : A) (ct port size : U64) (call : Bool) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
  let (v, a1) ← arI.port_in a port size
  let s2 ←
    if call
    then do
      let b ← msg.lookup_ipc_buffer st s1 true ct
      let s3 ← obj.Tcb.set_reg st ct s1 layout.reg.BADGE 0#u64
      let (n, s4) ← msg.set_mr st s3 ct b 0#u64 v
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      msg.set_msg_info st s4 ct mi
    else ok s1
  let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
  ok (core.result.Result.Ok (), s3, a1)

/-- **The `In` access and its reply** (for the IPC proofs and the arch
backend): FL4's `In` of `size` bytes at `port`, called, against the spec's
restart, `In` invocation and success tail: FL4 is done, its thread no longer
`Restart`, and the spec has an outcome related to FL4's state. -/
def PortInCallHyp (s : S) (σ : Fl4Spec.State Unit) (ar : A) (ct port size : U64) (d : Fl4Spec.IoPortInvocationData) :
    Prop :=
  portInTail (st := st) arI s ar ct port size true ⦃ res => res.1 = .Ok () ∧
    L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) d))).run σ1).1 ∧
      ∃ z ∈ (specTail true ct.bv rr σy).1, RelTop (L := L) res.2.1 z.2 ⦄

/-- **IOPort `In` called** (labels 64..66, `call` true): `DecOKR`, the reply
being FL4's own (`PortInCallHyp`). -/
theorem decode_invocation_ioport_in_call (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) {tcb : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb tcb))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    (hIn : ∀ port : U64, port.val < 65536 →
      PortInCallHyp (L := L) arI s σ ar ct port ⟨BitVec.ofNat 64 (portSz lbl)⟩ (inData (portSz lbl)))
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKR (L := L) arI s ar σ lbl length slot (.IoPort first last 0#u64) blk true don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  unfold DecOKR syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec
        (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
          (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)))) := rfl
  rw [hspec, decode_in_eq slbl _ _ hsz hlbl]
  unfold ioport.decode
  simp only
  rw [hct, port_size_eq lbl ⟨hl.1, by omega⟩, is_port_in_eq lbl ⟨hl.1, by omega⟩]
  simp only [bind_ok]
  have hszU : (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64 else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64
      else 4#u64) = ⟨BitVec.ofNat 64 (portSz lbl)⟩ := by
    unfold portSz; split_ifs <;> rfl
  rw [hszU]
  have hsz0 : ¬ (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 0#u64 := by
    rw [u64_eq_iff]; show ¬ (BitVec.ofNat 64 (portSz lbl)).toNat = 0
    rcases hsz with h | h | h <;> rw [h] <;> decide
  rw [if_neg hsz0, decide_eq_true (by omega : lbl.val ≤ 66)]
  simp only [↓reduceIte]
  -- the argument
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, .truncatedMessage, run_liftME_err (run_liftME_err ?_), Or.inl trivial⟩
    unfold Fl4Spec.argsAtLeast
    rw [whenE_pos (show 1 > (args.map UScalar.bv).length by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), lift, bind_ok]
  unfold Fl4Spec.argsAtLeast
  rw [whenE_neg (show ¬ 1 > ((y0 :: rest).map UScalar.bv).length by simp), retOk_bind, retOk_bind]
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  have g0 : (y0.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  rw [hmap, g0, the_some]
  set port := y0 &&& 65535#u64 with hport
  have hpv : port.val < 65536 := by rw [hport, and_ffff]; omega
  have hp16 : (Fl4Spec.ucast 16 y0.bv : BitVec 16) = BitVec.ofNat 16 port.val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hport, and_ffff]; omega
  rw [hp16]
  have hszv : (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64).val = portSz lbl := by
    show (BitVec.ofNat 64 (portSz lbl)).toNat = _
    rw [BitVec.toNat_ofNat]; rcases hsz with h | h | h <;> rw [h]
  rw [allowed_eq first last port _ hl16 hpv (by rw [hszv]; exact hsz)]
  simp only [hszv, bind_ok]
  have hens := ensure_run first last hfl hl16 port hpv hsz σ
  by_cases hc : port.val < first.val ∨ port.val + portSz lbl - 1 > last.val
  · rw [if_pos hc]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok]
    rw [if_pos hc] at hens
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, .illegalOperation, run_liftME_err (run_liftME_err (run_bind_error hens _)),
      Or.inl trivial⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_mono (hIn port hpv) ?_
  rintro res ⟨hres, hne, hall⟩
  obtain ⟨σ1, hst, -⟩ := setThreadState_eq σ ct.bv tcb hkt .restart
  obtain ⟨rr, σy, hy, z, hz, hRT⟩ := hall σ1 hst
  refine Or.inr ⟨hres, hne, .invokeArchObject (.spec (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val)
    (inData (portSz lbl))))), ?_, σ1, by rw [hcur]; exact hst, rr, σy, hy, z, hz, hRT⟩
  exact DecOut.of_eq (run_liftME_ok (run_liftME_ok ((run_bind_ok hens _).trans rfl)))

end

end

end Fl4Proofs.P3
