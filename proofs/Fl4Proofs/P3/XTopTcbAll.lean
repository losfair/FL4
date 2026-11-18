/-
P3 (DESIGN.md §9), TCB invocations: **the Thread cap at `XTop` with its
CSpace labels proved** (`decode_invocation_threadXC`): TcbXLeaves'
SetTimeoutEndpoint, SetSpace, SetIPCBuffer and Configure from XTopTcbCtl and
XTopBuf; the other labels' leaves (`TcbXRest`: the scheduler's, the IPC
side's, FL4's debug and l4h labels) named.
-/
import Fl4Proofs.P3.XTopBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The Thread cap's leaves not on the CSpace side** (TcbXLeaves without
SetTimeoutEndpoint, SetSpace, SetIPCBuffer, Configure) [W]: the register
labels, the scheduler's (SetPriority, SetMCPriority, SetSchedParams,
SetTLSBase), the IPC side's (Suspend, Resume, Bind/UnbindNotification), FL4's
debug, FPU and timer labels, SetFlags. -/
structure TcbXRest (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  readRegisters : lbl = fl4_abi.label.TCBReadRegisters →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  writeRegisters : lbl = fl4_abi.label.TCBWriteRegisters →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  copyRegisters : lbl = fl4_abi.label.TCBCopyRegisters →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setPriority : lbl = fl4_abi.label.TCBSetPriority →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setMCPriority : lbl = fl4_abi.label.TCBSetMCPriority →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setSchedParams : lbl = fl4_abi.label.TCBSetSchedParams →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  suspend : lbl = fl4_abi.label.TCBSuspend →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  resume : lbl = fl4_abi.label.TCBResume →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  bindNotification : lbl = fl4_abi.label.TCBBindNotification →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  unbindNotification : lbl = fl4_abi.label.TCBUnbindNotification →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  getBreakpoint : lbl = fl4_abi.label.TCBGetBreakpoint →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  unsetBreakpoint : lbl = fl4_abi.label.TCBUnsetBreakpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  configureSingleStepping : lbl = fl4_abi.label.TCBConfigureSingleStepping →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  setTLSBase : lbl = fl4_abi.label.TCBSetTLSBase →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setFlags : lbl = fl4_abi.label.TCBSetFlags →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  readFPU : lbl = fl4_abi.label.TCBReadFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  writeFPU : lbl = fl4_abi.label.TCBWriteFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setTimer : lbl = fl4_abi.label.TCBSetTimer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer

/-- **`TcbXHyp` with the CSpace labels proved**: the Thread cap's `XCap` at
`XTop`, every label, from `TcbXRest` and the CSpace labels' premises
(XTopTcbCtl's: `XTopAt` with `KsApart`, the typed heap's TCBs in `Z.T`, the
caller runnable, `DelInv`, the deletion's premises at `XTop`, the bound;
the extra caps `XcRel`, `NcHyp`; `ActReady` at `WX` for the buffer's
reschedule), the invoked slot `sl` a slot of the typed heap. -/
theorem decode_invocation_threadXC [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (lbl length : U64) (p : U64) (hp : Z.th p = some .tcb)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hR : TcbXRest (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  refine decode_invocation_threadX arI s ar σ ⟨Z, hX⟩ lbl length _ p blk call don fp buf extra ct hct slbl hlbl _ ci sl
    excaps buffer hext hstall hNative ⟨hR.readRegisters, hR.writeRegisters, hR.copyRegisters, fun h => ?_,
      hR.setPriority, hR.setMCPriority, hR.setSchedParams, fun h => ?_, fun h => ?_, fun h => ?_, hR.suspend,
      hR.resume, hR.bindNotification, hR.unbindNotification, hR.setBreakpoint, hR.getBreakpoint,
      hR.unsetBreakpoint, hR.configureSingleStepping, hR.setTLSBase, hR.setFlags, hR.readFPU, hR.writeFPU,
      hR.setTimer⟩
  · subst h
    exact tcb_configureXT arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB hA p hp slbl
      (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hcur hact hstall call sl hAs extra x0 x1
      x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer
  · subst h
    exact tcb_set_timeoutX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp slbl
      (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct hcur hact hstall call sl hAs extra x0 x1 x2 hx0 excaps hXc
      _ blk don ci buffer
  · subst h
    exact tcb_set_ipcXT arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB hA p hp slbl
      (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hcur hact hstall call sl hAs extra x0 x1
      x2 hx0 excaps hXc hnc0 blk don ci buffer
  · subst h
    exact tcb_set_spaceX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp slbl
      (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hcur hact hstall call sl hAs extra x0 x1
      x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer

end

end

end Fl4Proofs.P3
