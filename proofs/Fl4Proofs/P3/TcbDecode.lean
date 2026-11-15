/-
P3 (DESIGN.md §9), TCB invocations: **`tcb::decode`, native labels**, against
l4v's `decode_tcb_invocation` and `invoke_tcb` (through FL4's dispatcher):
`tcb_decode_refines` and the Thread cap's branch `decode_invocation_thread`,
posted as `DecOK` (`TopPost`).

Each label of FL4 is one hypothesis (`TcbOK` at that label), to be
discharged by the subsystem it belongs to: the CSpace-side labels in this
directory (`TcbTls`, `TcbCtl`: `tcb_decode_cspace`), the scheduler-side ones (SetPriority,
SetMCPriority, SetSchedParams, Suspend, Resume, Bind/UnbindNotification,
the scheduling part of Configure) by the scheduler's proofs. Every other
label is the spec's `IllegalOperation` (proved). The FL4 debug and l4h
labels (breakpoints, single stepping, FPU, TCB timers) and FL4's SetFlags
go to the dispatcher's extension decoders (`fl4DecodeTcbInvocation`,
`Ext/Tcb`; the extension label of the message is `hext`), discharged in
`TcbExt` (`tcb_decode_ext`).
SetEPTRoot is outside these native refinement statements (`hNative`). The stall of
the target (`smp::remote_tcb_stall`) is the hypothesis `hstall` (a no-op
for a thread of the current core).
-/
import Fl4Proofs.P3.DecodeTop
import Fl4Proofs.P3.TopF
import Fl4Proofs.P3.TopM
import Fl4Proofs.P3.TcbCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

@[simp] theorem lbl_tcbReadRegisters_val : fl4_abi.label.TCBReadRegisters.val = 2 := by simp [fl4_abi.label.TCBReadRegisters]
@[simp] theorem lbl_tcbWriteRegisters_val : fl4_abi.label.TCBWriteRegisters.val = 3 := by simp [fl4_abi.label.TCBWriteRegisters]
@[simp] theorem lbl_tcbCopyRegisters_val : fl4_abi.label.TCBCopyRegisters.val = 4 := by simp [fl4_abi.label.TCBCopyRegisters]
@[simp] theorem lbl_tcbConfigure_val : fl4_abi.label.TCBConfigure.val = 5 := by simp [fl4_abi.label.TCBConfigure]
@[simp] theorem lbl_tcbSetPriority_val : fl4_abi.label.TCBSetPriority.val = 6 := by simp [fl4_abi.label.TCBSetPriority]
@[simp] theorem lbl_tcbSetMCPriority_val : fl4_abi.label.TCBSetMCPriority.val = 7 := by simp [fl4_abi.label.TCBSetMCPriority]
@[simp] theorem lbl_tcbSetSchedParams_val : fl4_abi.label.TCBSetSchedParams.val = 8 := by simp [fl4_abi.label.TCBSetSchedParams]
@[simp] theorem lbl_tcbSetTimeoutEndpoint_val : fl4_abi.label.TCBSetTimeoutEndpoint.val = 9 := by simp [fl4_abi.label.TCBSetTimeoutEndpoint]
@[simp] theorem lbl_tcbSetIPCBuffer_val : fl4_abi.label.TCBSetIPCBuffer.val = 10 := by simp [fl4_abi.label.TCBSetIPCBuffer]
@[simp] theorem lbl_tcbSetSpace_val : fl4_abi.label.TCBSetSpace.val = 11 := by simp [fl4_abi.label.TCBSetSpace]
@[simp] theorem lbl_tcbSuspend_val : fl4_abi.label.TCBSuspend.val = 12 := by simp [fl4_abi.label.TCBSuspend]
@[simp] theorem lbl_tcbResume_val : fl4_abi.label.TCBResume.val = 13 := by simp [fl4_abi.label.TCBResume]
@[simp] theorem lbl_tcbBindNotification_val : fl4_abi.label.TCBBindNotification.val = 14 := by simp [fl4_abi.label.TCBBindNotification]
@[simp] theorem lbl_tcbUnbindNotification_val : fl4_abi.label.TCBUnbindNotification.val = 15 := by simp [fl4_abi.label.TCBUnbindNotification]
@[simp] theorem lbl_tcbSetBreakpoint_val : fl4_abi.label.TCBSetBreakpoint.val = 16 := by simp [fl4_abi.label.TCBSetBreakpoint]
@[simp] theorem lbl_tcbGetBreakpoint_val : fl4_abi.label.TCBGetBreakpoint.val = 17 := by simp [fl4_abi.label.TCBGetBreakpoint]
@[simp] theorem lbl_tcbUnsetBreakpoint_val : fl4_abi.label.TCBUnsetBreakpoint.val = 18 := by simp [fl4_abi.label.TCBUnsetBreakpoint]
@[simp] theorem lbl_tcbConfigureSingleStepping_val : fl4_abi.label.TCBConfigureSingleStepping.val = 19 := by simp [fl4_abi.label.TCBConfigureSingleStepping]
@[simp] theorem lbl_tcbSetTLSBase_val : fl4_abi.label.TCBSetTLSBase.val = 20 := by simp [fl4_abi.label.TCBSetTLSBase]
@[simp] theorem lbl_tcbSetFlags_val : fl4_abi.label.TCBSetFlags.val = 21 := by simp [fl4_abi.label.TCBSetFlags]
@[simp] theorem lbl_tcbReadFPU_val : fl4_abi.label.TCBReadFPU.val = 22 := by simp [fl4_abi.label.TCBReadFPU]
@[simp] theorem lbl_tcbWriteFPU_val : fl4_abi.label.TCBWriteFPU.val = 23 := by simp [fl4_abi.label.TCBWriteFPU]
@[simp] theorem lbl_tcbSetEPTRoot_val : fl4_abi.label.TCBSetEPTRoot.val = 88 := by simp [fl4_abi.label.TCBSetEPTRoot]
@[simp] theorem lbl_tcbSetTimer_val : fl4_abi.label.TCBSetTimer.val = 24 := by simp [fl4_abi.label.TCBSetTimer]

/-- The spec's TCB label of an FL4 label (the FL4 debug and l4h labels, and
every other label, are not l4v TCB labels). -/
def tcbLabelOf (lbl : U64) : Fl4Spec.GenInvocationLabels :=
  if lbl.val = 2 then .tcbReadRegisters else if lbl.val = 3 then .tcbWriteRegisters else if lbl.val = 4 then .tcbCopyRegisters else if lbl.val = 5 then .tcbConfigure else if lbl.val = 6 then .tcbSetPriority else if lbl.val = 7 then .tcbSetMCPriority else if lbl.val = 8 then .tcbSetSchedParams else if lbl.val = 9 then .tcbSetTimeoutEndpoint else if lbl.val = 10 then .tcbSetIPCBuffer else if lbl.val = 11 then .tcbSetSpace else if lbl.val = 12 then .tcbSuspend else if lbl.val = 13 then .tcbResume else if lbl.val = 14 then .tcbBindNotification else if lbl.val = 15 then .tcbUnbindNotification else if lbl.val = 20 then .tcbSetTLSBase else if lbl.val = 21 then .tcbSetFlags else .invalidInvocation

/-- The spec's TCB extension label of an FL4 label (the debug API and the
l4h labels; the dispatcher's `fl4TcbExtLabelOf` of the message label is
this, a hypothesis of each refinement). -/
def tcbExtOf (lbl : U64) : Option Fl4Spec.Fl4TcbExtLabel :=
  if lbl.val = 16 then some .setBreakpoint else if lbl.val = 17 then some .getBreakpoint
  else if lbl.val = 18 then some .unsetBreakpoint else if lbl.val = 19 then some .configureSingleStepping
  else if lbl.val = 22 then some .readFpu else if lbl.val = 23 then some .writeFpu
  else if lbl.val = 24 then some .setTimer else none

/-- FL4's TCB decoder is l4v's on an l4v label but `SetFlags`. -/
theorem fl4DecodeTcb_spec {label : Fl4Spec.Data} (h1 : Fl4Spec.genInvocationType label ≠ .tcbSetFlags)
    (h2 : Fl4Spec.genInvocationType label ≠ .invalidInvocation) {args : List Fl4Spec.Data} {cap : Fl4Spec.Cap}
    {slot : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} :
    Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB (Fl4Spec.decodeTcbInvocation label args cap slot excaps) := by
  unfold Fl4Spec.fl4DecodeTcbInvocation Fl4Spec.fl4TcbExtLabelOf
  rw [if_neg h1, if_neg h2]

/-- FL4's TCB decoder is l4v's off its extension labels and `SetFlags`. -/
theorem fl4DecodeTcb_spec' {label : Fl4Spec.Data} (h1 : Fl4Spec.genInvocationType label ≠ .tcbSetFlags)
    (h2 : Fl4Spec.fl4TcbExtLabelOf label = none) {args : List Fl4Spec.Data} {cap : Fl4Spec.Cap}
    {slot : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} :
    Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB (Fl4Spec.decodeTcbInvocation label args cap slot excaps) := by
  unfold Fl4Spec.fl4DecodeTcbInvocation
  rw [if_neg h1, h2]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The statement for `tcb::decode` at one label: `TopPost` against the
spec's decode and invocation of the Thread cap. -/
abbrev TcbOK (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64) (p : U64) (c : tcb.Ctx)
    (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPost (L := L) σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) s res ⦄

/-- The statement for `tcb::decode` at one label with the frame invariant:
`TopPostM`. -/
abbrev TcbOKF (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64) (p : U64) (c : tcb.Ctx)
    (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPostM (L := L) σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) s res ⦄

theorem TcbOKF.toTcbOK {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl p : U64} {c : tcb.Ctx} {blk call don : Bool}
    {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (h : TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer) :
    TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer :=
  WP.spec_mono h (fun _ h => h.toF.top)

/-- **`tcb::decode`, native labels**: from one hypothesis per FL4 TCB label
(see the module docstring), every other label being the spec's
`IllegalOperation`. -/
theorem tcb_decode_refines (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl p : U64) (c : tcb.Ctx)
    (blk call don : Bool) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hReadRegisters : lbl = fl4_abi.label.TCBReadRegisters →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hWriteRegisters : lbl = fl4_abi.label.TCBWriteRegisters →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hCopyRegisters : lbl = fl4_abi.label.TCBCopyRegisters →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hConfigure : lbl = fl4_abi.label.TCBConfigure →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetPriority : lbl = fl4_abi.label.TCBSetPriority →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetMCPriority : lbl = fl4_abi.label.TCBSetMCPriority →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetSchedParams : lbl = fl4_abi.label.TCBSetSchedParams →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetTimeoutEndpoint : lbl = fl4_abi.label.TCBSetTimeoutEndpoint →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetIPCBuffer : lbl = fl4_abi.label.TCBSetIPCBuffer →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetSpace : lbl = fl4_abi.label.TCBSetSpace →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSuspend : lbl = fl4_abi.label.TCBSuspend →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hResume : lbl = fl4_abi.label.TCBResume →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hBindNotification : lbl = fl4_abi.label.TCBBindNotification →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hUnbindNotification : lbl = fl4_abi.label.TCBUnbindNotification →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hGetBreakpoint : lbl = fl4_abi.label.TCBGetBreakpoint →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hUnsetBreakpoint : lbl = fl4_abi.label.TCBUnsetBreakpoint →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hConfigureSingleStepping : lbl = fl4_abi.label.TCBConfigureSingleStepping →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetTLSBase : lbl = fl4_abi.label.TCBSetTLSBase →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetFlags : lbl = fl4_abi.label.TCBSetFlags →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hReadFPU : lbl = fl4_abi.label.TCBReadFPU →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hWriteFPU : lbl = fl4_abi.label.TCBWriteFPU →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetTimer : lbl = fl4_abi.label.TCBSetTimer →
      TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer) :
    TcbOK (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer := by
  by_cases h2 : lbl.val = 2
  · exact hReadRegisters (UScalar.eq_of_val_eq (by rw [h2]; simp))
  by_cases h3 : lbl.val = 3
  · exact hWriteRegisters (UScalar.eq_of_val_eq (by rw [h3]; simp))
  by_cases h4 : lbl.val = 4
  · exact hCopyRegisters (UScalar.eq_of_val_eq (by rw [h4]; simp))
  by_cases h5 : lbl.val = 5
  · exact hConfigure (UScalar.eq_of_val_eq (by rw [h5]; simp))
  by_cases h6 : lbl.val = 6
  · exact hSetPriority (UScalar.eq_of_val_eq (by rw [h6]; simp))
  by_cases h7 : lbl.val = 7
  · exact hSetMCPriority (UScalar.eq_of_val_eq (by rw [h7]; simp))
  by_cases h8 : lbl.val = 8
  · exact hSetSchedParams (UScalar.eq_of_val_eq (by rw [h8]; simp))
  by_cases h9 : lbl.val = 9
  · exact hSetTimeoutEndpoint (UScalar.eq_of_val_eq (by rw [h9]; simp))
  by_cases h10 : lbl.val = 10
  · exact hSetIPCBuffer (UScalar.eq_of_val_eq (by rw [h10]; simp))
  by_cases h11 : lbl.val = 11
  · exact hSetSpace (UScalar.eq_of_val_eq (by rw [h11]; simp))
  by_cases h12 : lbl.val = 12
  · exact hSuspend (UScalar.eq_of_val_eq (by rw [h12]; simp))
  by_cases h13 : lbl.val = 13
  · exact hResume (UScalar.eq_of_val_eq (by rw [h13]; simp))
  by_cases h14 : lbl.val = 14
  · exact hBindNotification (UScalar.eq_of_val_eq (by rw [h14]; simp))
  by_cases h15 : lbl.val = 15
  · exact hUnbindNotification (UScalar.eq_of_val_eq (by rw [h15]; simp))
  by_cases h16 : lbl.val = 16
  · exact hSetBreakpoint (UScalar.eq_of_val_eq (by rw [h16]; simp))
  by_cases h17 : lbl.val = 17
  · exact hGetBreakpoint (UScalar.eq_of_val_eq (by rw [h17]; simp))
  by_cases h18 : lbl.val = 18
  · exact hUnsetBreakpoint (UScalar.eq_of_val_eq (by rw [h18]; simp))
  by_cases h19 : lbl.val = 19
  · exact hConfigureSingleStepping (UScalar.eq_of_val_eq (by rw [h19]; simp))
  by_cases h20 : lbl.val = 20
  · exact hSetTLSBase (UScalar.eq_of_val_eq (by rw [h20]; simp))
  by_cases h21 : lbl.val = 21
  · exact hSetFlags (UScalar.eq_of_val_eq (by rw [h21]; simp))
  by_cases h22 : lbl.val = 22
  · exact hReadFPU (UScalar.eq_of_val_eq (by rw [h22]; simp))
  by_cases h23 : lbl.val = 23
  · exact hWriteFPU (UScalar.eq_of_val_eq (by rw [h23]; simp))
  by_cases h24 : lbl.val = 24
  · exact hSetTimer (UScalar.eq_of_val_eq (by rw [h24]; simp))
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; simp [tcbLabelOf, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
  unfold TcbOK tcb.decode
  rw [hstall]
  simp only [hNative, ↓reduceIte]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val,
    h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, ↓reduceIte]
  refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
  show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
  rw [fl4DecodeTcb_spec' (by rw [hg]; decide) (by rw [hext hg]; simp [tcbExtOf, h16, h17, h18, h19, h22, h23, h24])]
  apply run_liftME_err
  unfold Fl4Spec.decodeTcbInvocation
  rw [hg]
  rfl

/-- `tcb_decode_refines` with the frame invariant. -/
theorem tcb_decode_refinesF (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl p : U64) (c : tcb.Ctx)
    (blk call don : Bool) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hReadRegisters : lbl = fl4_abi.label.TCBReadRegisters →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hWriteRegisters : lbl = fl4_abi.label.TCBWriteRegisters →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hCopyRegisters : lbl = fl4_abi.label.TCBCopyRegisters →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hConfigure : lbl = fl4_abi.label.TCBConfigure →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetPriority : lbl = fl4_abi.label.TCBSetPriority →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetMCPriority : lbl = fl4_abi.label.TCBSetMCPriority →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetSchedParams : lbl = fl4_abi.label.TCBSetSchedParams →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetTimeoutEndpoint : lbl = fl4_abi.label.TCBSetTimeoutEndpoint →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetIPCBuffer : lbl = fl4_abi.label.TCBSetIPCBuffer →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetSpace : lbl = fl4_abi.label.TCBSetSpace →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSuspend : lbl = fl4_abi.label.TCBSuspend →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hResume : lbl = fl4_abi.label.TCBResume →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hBindNotification : lbl = fl4_abi.label.TCBBindNotification →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hUnbindNotification : lbl = fl4_abi.label.TCBUnbindNotification →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hGetBreakpoint : lbl = fl4_abi.label.TCBGetBreakpoint →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hUnsetBreakpoint : lbl = fl4_abi.label.TCBUnsetBreakpoint →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hConfigureSingleStepping : lbl = fl4_abi.label.TCBConfigureSingleStepping →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetTLSBase : lbl = fl4_abi.label.TCBSetTLSBase →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetFlags : lbl = fl4_abi.label.TCBSetFlags →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hReadFPU : lbl = fl4_abi.label.TCBReadFPU →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hWriteFPU : lbl = fl4_abi.label.TCBWriteFPU →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer)
    (hSetTimer : lbl = fl4_abi.label.TCBSetTimer →
      TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer) :
    TcbOKF (L := L) arI s ar σ lbl p c blk call don slbl args ci sl excaps buffer := by
  by_cases h2 : lbl.val = 2
  · exact hReadRegisters (UScalar.eq_of_val_eq (by rw [h2]; simp))
  by_cases h3 : lbl.val = 3
  · exact hWriteRegisters (UScalar.eq_of_val_eq (by rw [h3]; simp))
  by_cases h4 : lbl.val = 4
  · exact hCopyRegisters (UScalar.eq_of_val_eq (by rw [h4]; simp))
  by_cases h5 : lbl.val = 5
  · exact hConfigure (UScalar.eq_of_val_eq (by rw [h5]; simp))
  by_cases h6 : lbl.val = 6
  · exact hSetPriority (UScalar.eq_of_val_eq (by rw [h6]; simp))
  by_cases h7 : lbl.val = 7
  · exact hSetMCPriority (UScalar.eq_of_val_eq (by rw [h7]; simp))
  by_cases h8 : lbl.val = 8
  · exact hSetSchedParams (UScalar.eq_of_val_eq (by rw [h8]; simp))
  by_cases h9 : lbl.val = 9
  · exact hSetTimeoutEndpoint (UScalar.eq_of_val_eq (by rw [h9]; simp))
  by_cases h10 : lbl.val = 10
  · exact hSetIPCBuffer (UScalar.eq_of_val_eq (by rw [h10]; simp))
  by_cases h11 : lbl.val = 11
  · exact hSetSpace (UScalar.eq_of_val_eq (by rw [h11]; simp))
  by_cases h12 : lbl.val = 12
  · exact hSuspend (UScalar.eq_of_val_eq (by rw [h12]; simp))
  by_cases h13 : lbl.val = 13
  · exact hResume (UScalar.eq_of_val_eq (by rw [h13]; simp))
  by_cases h14 : lbl.val = 14
  · exact hBindNotification (UScalar.eq_of_val_eq (by rw [h14]; simp))
  by_cases h15 : lbl.val = 15
  · exact hUnbindNotification (UScalar.eq_of_val_eq (by rw [h15]; simp))
  by_cases h16 : lbl.val = 16
  · exact hSetBreakpoint (UScalar.eq_of_val_eq (by rw [h16]; simp))
  by_cases h17 : lbl.val = 17
  · exact hGetBreakpoint (UScalar.eq_of_val_eq (by rw [h17]; simp))
  by_cases h18 : lbl.val = 18
  · exact hUnsetBreakpoint (UScalar.eq_of_val_eq (by rw [h18]; simp))
  by_cases h19 : lbl.val = 19
  · exact hConfigureSingleStepping (UScalar.eq_of_val_eq (by rw [h19]; simp))
  by_cases h20 : lbl.val = 20
  · exact hSetTLSBase (UScalar.eq_of_val_eq (by rw [h20]; simp))
  by_cases h21 : lbl.val = 21
  · exact hSetFlags (UScalar.eq_of_val_eq (by rw [h21]; simp))
  by_cases h22 : lbl.val = 22
  · exact hReadFPU (UScalar.eq_of_val_eq (by rw [h22]; simp))
  by_cases h23 : lbl.val = 23
  · exact hWriteFPU (UScalar.eq_of_val_eq (by rw [h23]; simp))
  by_cases h24 : lbl.val = 24
  · exact hSetTimer (UScalar.eq_of_val_eq (by rw [h24]; simp))
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; simp [tcbLabelOf, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
  unfold TcbOKF tcb.decode
  rw [hstall]
  simp only [hNative, ↓reduceIte]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val,
    h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, ↓reduceIte]
  refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
  show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
  rw [fl4DecodeTcb_spec' (by rw [hg]; decide) (by rw [hext hg]; simp [tcbExtOf, h16, h17, h18, h19, h22, h23, h24])]
  apply run_liftME_err
  unfold Fl4Spec.decodeTcbInvocation
  rw [hg]
  rfl

/-- **The Thread cap** of the dispatcher (`DecOK`), from `TcbOK` at its
label (not in the first phase). -/
theorem decode_invocation_thread (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (h : fp = false → TcbOK (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer) :
    DecOK (L := L) arI s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h rfl
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩


/-- **The Thread cap**, with the MDB invariants (`DecOKM`). -/
theorem decode_invocation_threadF (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (h : fp = false → TcbOKF (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer) :
    DecOKM (L := L) arI s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer := by
  unfold DecOKM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h rfl
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The Thread cap with the MDB invariants** (`DecOKM`): `decode_invocation_threadF`
under its M name. -/
theorem decode_invocation_threadM (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (h : fp = false → TcbOKF (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer) :
    DecOKM (L := L) arI s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer :=
  decode_invocation_threadF arI s ar σ lbl length slot p blk call don fp buf extra ct hct slbl args ci sl excaps buffer h

end

end

end Fl4Proofs.P3
