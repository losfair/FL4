/-
FL4 differences (PORTING.md, "FL4 differences"): **TCB extensions**, the
TCB invocations of FL4 that l4v's `decode_tcb_invocation` does not have,
modelled on FL4's Rust (`crates/fl4-core/src/tcb.rs`).

The decoders are FL4's checks, in FL4's order. FL4 reads its arguments
with `arg(i)` whatever the message length (`syscall_arg`: a message
register, else the IPC buffer word `i + 1`, else 0); `fl4GetMr` is that
read on the spec's state. The effects on state the abstract model does not
keep (debug registers, the FPU image, the l4h timer queue) are not
modelled: those invocations change no state but the frame contents of
ReadFPU (the 2696 bytes at the frame offset, `fl4FpuToFrame`), for SetTimer, possibly `reprogram_timer` (FL4 sets its
reprogram flag when the new deadline is the core's earliest; the spec sets
it nondeterministically, never clearing it), and for ConfigureSingleStepping
with no instruction count the trap flag (bit 8 of the target's `FLAGS`
register, cleared as FL4 does), and their replies are any value of the
right shape.

1. seL4's debug API (`CONFIG_HARDWARE_DEBUG_API`, not in l4v):
   `TCBSetBreakpoint`, `TCBGetBreakpoint`, `TCBUnsetBreakpoint`,
   `TCBConfigureSingleStepping`. The breakpoint number is checked against
   the four debug registers (`RangeError 0 3`); SetBreakpoint's checks are
   FL4's `set_breakpoint_checked`.
2. l4h 0002: `TCBReadFPU` (to a frame) and `TCBWriteFPU` (from a frame):
   the first extra cap, a non-device frame cap that is not kernel-only (and
   read-write for ReadFPU), and an offset in it, 64-byte aligned, with room
   for the FPU image (`FPU_STATE_SIZE`, 2696 bytes).
3. l4h: `TCBSetTimer` (two arguments): a deadline and a badge for the
   thread's l4h timer.
4. FL4's `TCBSetFlags`: l4v's, except that the flags word is FL4's (the
   `TRAP_SYSCALLS` bit of l4h is not one of l4v's `TcbFlag`s, so it is
   not kept, and the reply's word is any word of the new flags), and FL4
   does not restore the FPU lazily when the FPU is enabled
   (`arch_post_set_flags`'s `lazy_fpu_restore`).

The ported modules are not changed.
-/
import Fl4Spec

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4's TCB invocations that l4v does not have. -/
inductive Fl4TcbInvocation where
  | setBreakpoint (t : ObjRef) (bp vaddr ty size rw : Data)
  | getBreakpoint (t : ObjRef) (bp : Data)
  | unsetBreakpoint (t : ObjRef) (bp : Data)
  | configureSingleStepping (t : ObjRef) (bp n : Data)
  | fpuTransfer (t : ObjRef) (toFrame : Bool) (frame : ObjRef)
  | setTimer (t : ObjRef) (deadline badge : Data)
  | setFlags (t : ObjRef) (clearFlags setFlags : Data)
deriving Inhabited

/-- FL4's TCB extension labels (their numbers are the dispatcher's). -/
inductive Fl4TcbExtLabel where
  | setBreakpoint | getBreakpoint | unsetBreakpoint | configureSingleStepping
  | readFpu | writeFpu | setTimer
deriving DecidableEq, Inhabited

/-! ## FL4's constants (`fl4_abi`, `debug`) -/

/-- `fl4_abi::consts::USER_TOP`. -/
def fl4UserTop : Data := 0x00007fffffffffff
/-- `debug::DATA_BREAKPOINT`. -/
def fl4DataBreakpoint : Data := 0
/-- `debug::INSTRUCTION_BREAKPOINT`. -/
def fl4InstructionBreakpoint : Data := 1
/-- `debug::BREAK_ON_READ`. -/
def fl4BreakOnRead : Data := 0
/-- `debug::BREAK_ON_WRITE`. -/
def fl4BreakOnWrite : Data := 1
/-- `debug::BREAK_ON_READ_WRITE`. -/
def fl4BreakOnReadWrite : Data := 2
/-- `debug::N_REGS`: the debug registers. -/
def fl4NDebugRegs : Data := 4
/-- `fl4_abi::consts::FPU_STATE_SIZE`, in bytes. -/
def fl4FpuStateSize : Nat := 2696

/-- **FL4's ReadFPU write of the FPU image into the user frame** (FL4
extension, no l4v counterpart; the TCB's FPU image itself is not in the
model). FL4 (crates/fl4-core tcb.rs `fpu_transfer` with `to_frame`) calls
`restart_caller` (the spec's `setThreadState Restart` before the perform),
`Arch::fpu_flush` (saves the live registers of the target into its TCB's
FPU image; the registers, the FPU owner and the enable state are left as
they were: fl4-arch-x86_64 `fpu::flush`/`flush_local` restore CR0.TS), then
`copy_words` of `(FPU_STATE_SIZE + 7) / 8` = 337 words from the TCB's FPU
image to `frame`, `frame + 8`, ... (`wrapping_add`): exactly the bytes at
`frame + k` for `k < fl4FpuStateSize` = 2696. So only `underlyingMemory`
changes, and only at addresses whose offset from `frame` (modulo `2^64`) is
below `fl4FpuStateSize`; the IRQ masks, IRQ/time oracle positions,
lastMachineTime, device state, `fpuEnabled` and `machineStateRest` are
kept. The written values are left open (the FPU image is not modelled). -/
def fl4FpuToFrame (frame : Word) : MachineMonad Unit := do
  let um ← NonDet.gets MachineState.underlyingMemory
  let um' ← NonDet.select
    {um' : Word64 → Word8 | ∀ a : Word64, fl4FpuStateSize ≤ (a - frame).toNat → um' a = um a}
  NonDet.modify fun ms => { ms with underlyingMemory := um' }

section
variable {Z : Type} [StateExt Z]

/-- FL4's `syscall_arg`: message register `i` of thread `t` (a CPU message
register, else word `i + 1` of the IPC buffer, else 0). -/
def fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : SMonad Z Data := do
  let context ← threadGet (archTcbGetRegisters ∘ Tcb.tcbArch) t
  if h : i < msg_registers.length then return context (msg_registers[i]'h)
  else match buf with
    | none => return 0
    | some p => loadWordOffs p (i + 1)

/-- The caller's argument `i`. -/
def fl4Arg (buf : Option ObjRef) (i : Nat) : SEMonad Z Data := do
  let caller ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
  NonDetE.liftE <| fl4GetMr caller buf i

/-- FL4's `debug::check_bp_num`. -/
def fl4CheckBpNum (bp : Data) : SEMonad Z Unit :=
  NonDetE.whenE (bp ≥ fl4NDebugRegs) <| NonDetE.throwError (.rangeError 0 3)

/-- FL4's `set_breakpoint_checked`. -/
def decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SEMonad Z Fl4TcbInvocation := do
  let bp ← fl4Arg buf 0
  let vaddr ← fl4Arg buf 1
  let ty ← fl4Arg buf 2
  let size ← fl4Arg buf 3
  let rw ← fl4Arg buf 4
  NonDetE.whenE (vaddr ≥ fl4UserTop) <| NonDetE.throwError (.invalidArgument 1)
  NonDetE.whenE (ty ≠ fl4InstructionBreakpoint ∧ ty ≠ fl4DataBreakpoint) <|
    NonDetE.throwError (.invalidArgument 2)
  if ty = fl4InstructionBreakpoint then do
    NonDetE.whenE (size ≠ 0) <| NonDetE.throwError (.invalidArgument 3)
    NonDetE.whenE (rw ≠ fl4BreakOnRead) <| NonDetE.throwError (.invalidArgument 4)
  else
    NonDetE.whenE (size = 0) <| NonDetE.throwError (.invalidArgument 3)
  NonDetE.whenE (rw ≠ fl4BreakOnRead ∧ rw ≠ fl4BreakOnWrite ∧ rw ≠ fl4BreakOnReadWrite) <|
    NonDetE.throwError (.invalidArgument 3)
  NonDetE.whenE (size ≠ 0 ∧ size ≠ 1 ∧ size ≠ 2 ∧ size ≠ 4 ∧ size ≠ 8) <|
    NonDetE.throwError (.invalidArgument 3)
  NonDetE.whenE (size > 0 ∧ vaddr &&& (size - 1) ≠ 0) <| NonDetE.throwError .alignmentError
  fl4CheckBpNum bp
  NonDetE.whenE (size = 8) <| NonDetE.throwError (.invalidArgument 3)
  NonDetE.returnOk (.setBreakpoint t bp vaddr ty size rw)

/-- FL4's `decode_get_breakpoint`. -/
def decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SEMonad Z Fl4TcbInvocation := do
  let bp ← fl4Arg buf 0
  fl4CheckBpNum bp
  NonDetE.returnOk (.getBreakpoint t bp)

/-- FL4's `TCBUnsetBreakpoint`. -/
def decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SEMonad Z Fl4TcbInvocation := do
  let bp ← fl4Arg buf 0
  fl4CheckBpNum bp
  NonDetE.returnOk (.unsetBreakpoint t bp)

/-- FL4's `decode_configure_single_stepping` (no checks). -/
def decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : SEMonad Z Fl4TcbInvocation := do
  let bp ← fl4Arg buf 0
  let n ← fl4Arg buf 1
  NonDetE.returnOk (.configureSingleStepping t bp n)

/-- FL4's `fpu_transfer` checks (l4h 0002): `toFrame` for ReadFPU. -/
def decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef)
    (excaps : List (Cap × CslotPtr)) : SEMonad Z Fl4TcbInvocation := do
  NonDetE.whenE (excaps = [] ∨ args.length < 1) <| NonDetE.throwError .truncatedMessage
  let offset ← NonDetE.returnOk <| the args[0]?
  match (the excaps[0]?).1 with
  | .archObjectCap (.pageCap dev base rights _ sz _) =>
    if dev ∨ rights = vmKernelOnly ∨ (toFrame ∧ rights ≠ vmReadWrite)
    then NonDetE.throwError (.invalidCapability 1)
    else do
      let size := 2 ^ pageBitsForSize sz
      NonDetE.whenE (offset.toNat % 64 ≠ 0 ∨ offset.toNat ≥ size ∨ size - offset.toNat < fl4FpuStateSize) <|
        NonDetE.throwError (.invalidArgument 0)
      NonDetE.returnOk (.fpuTransfer t toFrame (base + offset))
  | _ => NonDetE.throwError (.invalidCapability 1)

/-- FL4's `TCBSetTimer` (l4h). -/
def decodeFl4SetTimer (args : List Data) (t : ObjRef) : SEMonad Z Fl4TcbInvocation := do
  NonDetE.whenE (args.length < 2) <| NonDetE.throwError .truncatedMessage
  NonDetE.returnOk (.setTimer t (the args[0]?) (the args[1]?))

/-- FL4's `decode_set_flags`. -/
def decodeFl4SetFlags (args : List Data) (t : ObjRef) : SEMonad Z Fl4TcbInvocation := do
  NonDetE.whenE (args.length < 2) <| NonDetE.throwError .truncatedMessage
  NonDetE.returnOk (.setFlags t (the args[0]?) (the args[1]?))

/-- The decoder of an extension label. -/
def decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr))
    (buf : Option ObjRef) : SEMonad Z Fl4TcbInvocation :=
  match l with
  | .setBreakpoint => decodeFl4SetBreakpoint buf t
  | .getBreakpoint => decodeFl4GetBreakpoint buf t
  | .unsetBreakpoint => decodeFl4UnsetBreakpoint buf t
  | .configureSingleStepping => decodeFl4ConfigureSingleStepping buf t
  | .readFpu => decodeFl4FpuTransfer true args t excaps
  | .writeFpu => decodeFl4FpuTransfer false args t excaps
  | .setTimer => decodeFl4SetTimer args t

/-- The invocations. The debug registers, the FPU image and the l4h timer
queue are not in the model: those invocations change no state (ReadFPU:
the frame's bytes it writes, `fl4FpuToFrame`; SetTimer: possibly
`reprogram_timer`, set, never cleared, as FL4's reprogram flag after an
insert at the head of the core's timer queue; ConfigureSingleStepping with
no instruction count: the target's trap flag, cleared), and their replies
are any value of the right shape. -/
def invokeFl4Tcb : Fl4TcbInvocation → PMonad Z (List Data)
  | .setBreakpoint .. => NonDetE.returnOk []
  | .getBreakpoint .. => NonDetE.liftE <| NonDet.select {l | l.length = 5}
  | .unsetBreakpoint .. => NonDetE.returnOk []
  | .configureSingleStepping t _ n => NonDetE.liftE <| do
    -- FL4 (and seL4's x86 `configureSingleStepping`) clears the trap flag
    -- (bit 8 of `FLAGS`) of the target when single-stepping is turned off
    NonDet.when (n = 0) <| asUser t do
      let f ← getRegister .flags
      setRegister .flags (f &&& ~~~((1 : Word) <<< 8))
    NonDet.select {[0], [1]}
  | .fpuTransfer _ toFrame frame =>
    if toFrame then NonDetE.liftE <| do
      doMachineOp (fl4FpuToFrame frame)
      return []
    else NonDetE.returnOk []
  | .setTimer .. => NonDetE.liftE <| do
    -- the l4h timer queue is not modelled; FL4 asks for a timer reprogram
    -- when the new deadline is the core's first, which `reprogram_timer`
    -- may record (any value, kept if already set)
    let b ← NonDet.select (Set.univ : Set Bool)
    NonDet.modify fun σ => { σ with reprogramTimer := σ.reprogramTimer || b }
    return []
  | .setFlags t clearFlags setFlags' => NonDetE.liftE <| do
    let flags ← threadGet Tcb.tcbFlags t
    let newFlags ← pure (flags \ wordToTcbFlags clearFlags ∪ wordToTcbFlags setFlags')
    Fl4Spec.setFlags t newFlags
    NonDet.when (TcbFlag.fpuDisabled ∈ newFlags) (fpuRelease t)
    let w ← NonDet.select {w | wordToTcbFlags w = newFlags}
    return [w]

end

end

end Fl4Spec
