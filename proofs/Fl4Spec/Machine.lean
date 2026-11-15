/-
The machine interface of the seL4 abstract specification, x86-64, MCS.

Ports, in this order:
- the parts of l4v `lib/Word_Lib` and `lib/Lib` the spec relies on (word
  operations, `undefined`, `the`, `THE`, `partial_inv`, list helpers);
- the generated `Kernel_Config` constants the spec uses;
- `spec/machine/X64/Platform`;
- `spec/machine/Time`;
- `spec/design/m-skel/X64/MachineTypes` (with the Haskell parts it includes,
  `SEL4/Machine/RegisterSet/X64.lhs` and the listed types of
  `SEL4/Machine/Hardware/X64.lhs`);
- `spec/machine/MachineMonad`;
- `spec/machine/X64/MachineOps`;
- `spec/machine/MachineExports` (only requalifications; nothing to port);
- `spec/abstract/X64/Machine_A` and `spec/abstract/MiscMachine_A`.

l4v's `rt` branch has not been ported to X64: the X64 machine theories lack
the MCS timer interface (`getCurrentTime`, `setDeadline`, `ackDeadlineIRQ`,
the `time_state` and `last_machine_time` fields, the time oracle) and the
MCS registers (`replyRegister`, `nbsendRecvDest`, `timeoutMessage`). These are
added here following the RISCV64 versions on `rt` (`RISCV64/MachineOps`,
`m-skel/RISCV64/MachineTypes`), with the X64 register choices of the seL4 C
kernel. Each such definition says so in its docstring ("rt X64 gap").
-/
import Fl4Spec.Monad
import Mathlib.Logic.Function.Basic

namespace Fl4Spec

open Classical

noncomputable section

/-! ## Lib and Word_Lib helpers -/

/-- l4v `machine_word` / `word64`. -/
abbrev Word := BitVec 64
/-- l4v `word8`. -/
abbrev Word8 := BitVec 8
/-- l4v `word16`. -/
abbrev Word16 := BitVec 16
/-- l4v `word32`. -/
abbrev Word32 := BitVec 32
/-- l4v `word64`. -/
abbrev Word64 := BitVec 64

/-- l4v: Word_Lib.word_bits (`LENGTH(machine_word_len)`). -/
def wordBits : Nat := 64
/-- l4v: Word_Lib.word_size (bytes in a machine word). -/
def wordSize : Nat := 8
/-- l4v: Word_Lib.word_size_bits. -/
def wordSizeBits : Nat := 3

/-- l4v: Word_Lib.mask, `2 ^ n - 1` (all ones when `n ≥ w`). -/
def mask {w : Nat} (n : Nat) : BitVec w := (1 <<< n) - 1

/-- l4v: Word_Lib.ucast, unsigned cast between word lengths. -/
abbrev ucast {v : Nat} (w : Nat) (x : BitVec v) : BitVec w := x.setWidth w

/-- l4v: Word_Lib.alignUp (More_Word_Operations), `x + 2 ^ n - 1 AND NOT
(2 ^ n - 1)`: round up to a multiple of `2 ^ n`. -/
def alignUp {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  (x + BitVec.ofNat w (2 ^ n) - 1) &&& ~~~(BitVec.ofNat w (2 ^ n) - 1)

/-- l4v: Word_Lib.unat. -/
abbrev unat {w : Nat} (x : BitVec w) : Nat := x.toNat

/-- l4v: Word_Lib.test_bit (infix `!!`). -/
abbrev testBit {w : Nat} (x : BitVec w) (n : Nat) : Bool := x.getLsbD n

/-- l4v: Word_Lib.to_bl, the bits of a word, most significant first. -/
def toBl {w : Nat} (x : BitVec w) : List Bool := (List.range w).reverse.map x.getLsbD

/-- l4v: Word_Lib.of_bl, a word from a bit list, most significant first
(truncated to the word length). -/
def ofBl {w : Nat} (bs : List Bool) : BitVec w :=
  bs.foldl (fun acc b => (acc <<< 1) ||| (if b then 1 else 0)) 0

/-- l4v: Word_Lib.word_rcat, concatenate words, most significant first. -/
def wordRcat {m n : Nat} (ws : List (BitVec m)) : BitVec n :=
  ws.foldl (fun acc b => (acc <<< m) ||| b.setWidth n) 0

/-- l4v: Word_Lib.word_rsplit, split a word into words of length `m`, most
significant first. -/
def wordRsplit {n m : Nat} (w : BitVec n) : List (BitVec m) :=
  (List.range ((n + m - 1) / m)).reverse.map fun k => (w >>> (k * m)).setWidth m

/-- l4v: Word_Lib.upto_enum on words (`[a .e. b]`), in the form of l4v's
lemma `upto_enum_word`: `map of_nat [unat a ..< Suc (unat b)]`. -/
def uptoEnum {w : Nat} (a b : BitVec w) : List (BitVec w) :=
  (List.range' a.toNat (b.toNat + 1 - a.toNat)).map (BitVec.ofNat w)

/-- l4v: Word_Lib.upto_enum_step (`[a, b .e. c]`). -/
def uptoEnumStep {w : Nat} (a b c : BitVec w) : List (BitVec w) :=
  if c < a then [] else (uptoEnum 0 ((c - a) / (b - a))).map fun x => a + x * (b - a)

/-- l4v: Enumeration.enum for words: every value, in increasing order. -/
def wordEnum (w : Nat) : List (BitVec w) := (List.range (2 ^ w)).map (BitVec.ofNat w)

/-- l4v: Enumeration.assocs on a word domain. -/
def assocs {w : Nat} {β : Type} (f : BitVec w → β) : List (BitVec w × β) :=
  (wordEnum w).map fun x => (x, f x)

/-- l4v `[i..j]` on `int`. -/
def intUpto (i j : Int) : List Int := (List.range (j - i + 1).toNat).map fun k : Nat => i + (k : Int)

/-- l4v: Word_Lib.More_Word_Operations.ptr_add. -/
def ptrAdd {w : Nat} (ptr : BitVec w) (n : Nat) : BitVec w := ptr + BitVec.ofNat w n

/-- l4v: Word_Lib.Aligned.is_aligned (`2 ^ n dvd unat w`). -/
def isAligned {w : Nat} (x : BitVec w) (n : Nat) : Prop := 2 ^ n ∣ x.toNat

/-- Isabelle/HOL `undefined`: an unspecified value of a (nonempty) type. -/
def undefined {α : Sort _} [h : Nonempty α] : α := Classical.choice h

/-- Isabelle/HOL `the`: the content of `Some`, `undefined` for `None`. -/
def the {α : Type} [Nonempty α] : Option α → α
  | some x => x
  | none => undefined

/-- Isabelle/HOL `THE x. P x`: the unique value satisfying `P` (an
unspecified value if there is none or more than one). -/
def The {α : Type} [Nonempty α] (P : α → Prop) : α :=
  if h : ∃! x, P x then Classical.choose h else undefined

/-- l4v: Lib.partial_inv. -/
def partialInv {α β : Type} [Nonempty α] (f : α → β) (x : β) : Option α :=
  if ∃! y, f y = x then some (The fun y => f y = x) else none

/-- Isabelle/HOL `Max` on a finite set: its greatest element (an
unspecified value for the empty set, as in Isabelle). -/
def setMax {α : Type} [LE α] [Nonempty α] (S : Set α) : α :=
  The fun m => m ∈ S ∧ ∀ x ∈ S, x ≤ m

/-- l4v: Word_Lib.Enumeration.the_index (`primrec (nonexhaustive)`): the
position of the first occurrence of `y` in a list. -/
def theIndex {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => undefined
  | x :: xs, y => if x = y then 0 else theIndex xs y + 1

/-- Isabelle/HOL `dom` of a partial map. -/
def dom {α β : Type} (m : α → Option β) : Set α := {a | m a ≠ none}

/-- Isabelle/HOL `ran` of a partial map. -/
def ran {α β : Type} (m : α → Option β) : Set β := {b | ∃ a, m a = some b}

/-! ## Kernel_Config

`Kernel_Config` is generated from the C kernel's build configuration. FL4
detects hardware at boot and sets the rest at build time, so the constants the
spec uses stay unspecified here, constrained by exactly what l4v proves about
them in `Kernel_Config_Lemmas`. -/

/-- The unspecified constants of `Kernel_Config` with the facts that
`Kernel_Config_Lemmas` proves of them. -/
structure KernelConfig where
  numDomains : Nat
  numDomains_not_zero : 0 < numDomains
  numDomains_fits_domainBits : numDomains ≤ 2 ^ 8
  /-- `CONFIG_RESET_CHUNK_BITS` (no lemmas about it in l4v) -/
  resetChunkBits : Nat
  /-- `CONFIG_RETYPE_FAN_OUT_LIMIT` (no lemmas about it in l4v) -/
  retypeFanOutLimit : Word64

instance : Inhabited KernelConfig := ⟨⟨1, by decide, by decide, 8, 256⟩⟩

/-- The build configuration (stands for the generated `Kernel_Config`). -/
opaque kernelConfig : KernelConfig

/-- l4v: Kernel_Config.numDomains (generated; unspecified here). -/
def numDomains : Nat := kernelConfig.numDomains

/-- l4v: Kernel_Config_Lemmas.numDomains_not_zero. -/
theorem numDomains_not_zero : 0 < numDomains := kernelConfig.numDomains_not_zero

/-- l4v: Kernel_Config_Lemmas.domainBits. -/
def domainBits : Nat := 8

/-- l4v: Kernel_Config_Lemmas.numDomains_fits_domainBits. -/
theorem numDomains_fits_domainBits : numDomains ≤ 2 ^ domainBits :=
  kernelConfig.numDomains_fits_domainBits

/-- l4v: Kernel_Config.resetChunkBits (generated from
`CONFIG_RESET_CHUNK_BITS`; unspecified here): the size in bits of the chunks
of memory to zero before checking a preemption point. -/
def resetChunkBits : Nat := kernelConfig.resetChunkBits

/-- l4v: Kernel_Config.retypeFanOutLimit (generated from
`CONFIG_RETYPE_FAN_OUT_LIMIT`, C default 256; unspecified here): the most
objects one `Retype` invocation can create. -/
def retypeFanOutLimit : Word64 := kernelConfig.retypeFanOutLimit

/-- l4v: Kernel_Config.config_HAVE_FPU. Always set on x86-64. -/
def config_HAVE_FPU : Bool := true

/-! ## Platform (spec/machine/X64/Platform) -/

/-- l4v: Platform.int_word (`32 signed word`, C int literals). -/
abbrev IntWord := BitVec 32

/-- l4v: Platform.X64.irq (`irq_len word`, `irq_len = 8`). -/
abbrev Irq := BitVec 8
/-- l4v: Platform.X64.paddr. -/
abbrev Paddr := Word64

/-- l4v: Platform.X64.toPAddr. -/
abbrev toPAddr (x : Word) : Paddr := x
/-- l4v: Platform.X64.fromPAddr. -/
abbrev fromPAddr (x : Paddr) : Word := x

/-- l4v: Platform.X64.pptrBase. -/
def pptrBase : Word64 := 0xffffff8000000000
/-- l4v: Platform.X64.kernelELFBaseOffset. -/
def kernelELFBaseOffset : Word64 := 0xffffffff80000000
/-- l4v: Platform.X64.pptrUserTop. -/
def pptrUserTop : Word64 := 0x00007fffffffffff
/-- l4v: Platform.X64.ptrFromPAddr. -/
def ptrFromPAddr (paddr : Paddr) : Word64 := paddr + pptrBase
/-- l4v: Platform.X64.addrFromPPtr. -/
def addrFromPPtr (pptr : Word64) : Paddr := pptr - pptrBase
/-- l4v: Platform.X64.addrFromKPPtr. -/
def addrFromKPPtr (pptr : Word64) : Paddr := pptr - kernelELFBaseOffset

/-- l4v: Platform.X64.minIRQ. -/
def minIRQ : Irq := 0
/-- l4v: Platform.X64.maxIRQ. -/
def maxIRQ : Irq := 125
/-- l4v: Platform.X64.minUserIRQ. -/
def minUserIRQ : Irq := 16
/-- l4v: Platform.X64.maxUserIRQ. -/
def maxUserIRQ : Irq := 123

/-- l4v: Platform.X64.timerIRQ (rt X64 gap; RISCV64 `Platform.timerIRQ`).
The value is the C kernel's `irq_timer` on pc99 without SMP IPIs
(`int_timer - IRQ_INT_OFFSET = 157 - 32`), which equals `maxIRQ`. -/
def timerIRQ : Irq := 125

/-- l4v: Platform.X64.cr3 (`X64CR3 CR3BaseAddress cr3pcid`). Named
`Platform.Cr3` to keep it apart from `Arch_Structs_A.cr3`. -/
structure Platform.Cr3 where
  /-- l4v `CR3BaseAddress`. -/
  cr3BaseAddress : Word64
  /-- l4v `cr3pcid`. -/
  cr3pcid : Word64
deriving DecidableEq, Inhabited

/-! ## Time (spec/machine/Time) -/

/-- l4v: Time.maxTimer_us (unconstrained constant). -/
opaque maxTimerUs : Word64
/-- l4v: Time.max_ticks_to_us (unconstrained constant). -/
opaque maxTicksToUs : Word64
/-- l4v: Time.max_us_to_ticks (unconstrained constant). -/
opaque maxUsToTicks : Word64

/-- l4v: Time.ticks (`ticks_len word`, `ticks_len = 64`). -/
abbrev Ticks := BitVec 64
/-- l4v: Time.time. -/
abbrev Time := BitVec 64

/-- l4v: Time.max_time (`max_word`). -/
abbrev maxTime : Time := BitVec.allOnes 64

/-- l4v: Time.μs_in_ms. -/
def μsInMs : Word64 := 1000

/-- The unspecified timer constants of l4v `Time` (`kernelWCETUs`,
`ticksPerTimerUnit`, `timerUnit`) bundled with the axioms Time.thy states
about them (`axiomatization where ...`). The witness in the `Inhabited`
instance is the one of Time.thy's consistency `notepad` (50, 1, 100).

FL4 configuration: `maxPeriodUs` (l4v's `MAX_PERIOD_US`) is a platform
constant too. l4v fixes it at one hour; the C kernel's default
(`KernelStaticMaxPeriodUs = 0`) is `getMaxUsToTicks() / 8`, which FL4
follows. The witness keeps l4v's one hour. -/
structure TimeConsts where
  maxPeriodUs : Word64
  kernelWCETUs : Ticks
  ticksPerTimerUnit : Ticks
  timerUnit : Ticks
  kernelWCET_us_pos2 : 0 < 2 * kernelWCETUs
  MIN_BUDGET_le_MAX_PERIOD : 2 * kernelWCETUs ≤ maxPeriodUs
  ticks_per_timer_unit_non_zero : ticksPerTimerUnit ≠ 0
  MIN_BUDGET_bound : 2 * unat kernelWCETUs * unat ticksPerTimerUnit < unat maxTime
  getCurrentTime_buffer_bound : 5 * unat maxPeriodUs * unat ticksPerTimerUnit < unat maxTime
  kernelWCET_pos' : 0 < (kernelWCETUs * ticksPerTimerUnit) / timerUnit
  MIN_BUDGET_pos' : 0 < 2 * ((kernelWCETUs * ticksPerTimerUnit) / timerUnit)
  init_domain_time_pos : 0 < ((15 * μsInMs) * ticksPerTimerUnit) / timerUnit
  init_domain_time_bound : 15 * unat μsInMs * unat ticksPerTimerUnit < unat maxTime
  getCurrentTime_buffer_pos : 0 < 5 * ((maxPeriodUs * ticksPerTimerUnit) / timerUnit)

instance : Inhabited TimeConsts :=
  ⟨{ maxPeriodUs := 60 * 60 * 1000 * 1000,
     kernelWCETUs := 100, ticksPerTimerUnit := 50, timerUnit := 1,
     kernelWCET_us_pos2 := by decide
     MIN_BUDGET_le_MAX_PERIOD := by decide
     ticks_per_timer_unit_non_zero := by decide
     MIN_BUDGET_bound := by decide
     getCurrentTime_buffer_bound := by decide
     kernelWCET_pos' := by decide
     MIN_BUDGET_pos' := by decide
     init_domain_time_pos := by decide
     init_domain_time_bound := by decide
     getCurrentTime_buffer_pos := by decide }⟩

/-- The timer constants of the machine (stands for Time.thy's `consts` and
`axiomatization`). -/
opaque timeConsts : TimeConsts

/-- l4v: Time.MAX_PERIOD_US (here a platform constant; see `TimeConsts`). -/
def MAX_PERIOD_US : Word64 := timeConsts.maxPeriodUs
/-- l4v: Time.kernelWCET_us. -/
def kernelWCETUs : Ticks := timeConsts.kernelWCETUs
/-- l4v: Time.ticks_per_timer_unit. -/
def ticksPerTimerUnit : Ticks := timeConsts.ticksPerTimerUnit
/-- l4v: Time.timer_unit. -/
def timerUnit : Ticks := timeConsts.timerUnit

/-- l4v: Time.us_to_ticks. -/
def usToTicks (us : Ticks) : Ticks := (us * ticksPerTimerUnit) / timerUnit

/-- l4v: Time.ticks_to_us. -/
def ticksToUs (ticks : Ticks) : Ticks := ticks / (ticksPerTimerUnit / timerUnit)

/-- l4v: Time.kernelWCET_us_pos2 (axiom). -/
theorem kernelWCET_us_pos2 : 0 < 2 * kernelWCETUs := timeConsts.kernelWCET_us_pos2
/-- l4v: Time.MIN_BUDGET_le_MAX_PERIOD (axiom). -/
theorem MIN_BUDGET_le_MAX_PERIOD : 2 * kernelWCETUs ≤ MAX_PERIOD_US :=
  timeConsts.MIN_BUDGET_le_MAX_PERIOD
/-- l4v: Time.ticks_per_timer_unit_non_zero (axiom). -/
theorem ticks_per_timer_unit_non_zero : ticksPerTimerUnit ≠ 0 :=
  timeConsts.ticks_per_timer_unit_non_zero
/-- l4v: Time.MIN_BUDGET_bound (axiom). -/
theorem MIN_BUDGET_bound : 2 * unat kernelWCETUs * unat ticksPerTimerUnit < unat maxTime :=
  timeConsts.MIN_BUDGET_bound
/-- l4v: Time.getCurrentTime_buffer_bound (axiom). -/
theorem getCurrentTime_buffer_bound :
    5 * unat MAX_PERIOD_US * unat ticksPerTimerUnit < unat maxTime :=
  timeConsts.getCurrentTime_buffer_bound
/-- l4v: Time.kernelWCET_pos' (axiom). -/
theorem kernelWCET_pos' : 0 < usToTicks kernelWCETUs := timeConsts.kernelWCET_pos'
/-- l4v: Time.MIN_BUDGET_pos' (axiom). -/
theorem MIN_BUDGET_pos' : 0 < 2 * usToTicks kernelWCETUs := timeConsts.MIN_BUDGET_pos'
/-- l4v: Time.init_domain_time_pos (axiom). -/
theorem init_domain_time_pos : 0 < usToTicks (15 * μsInMs) := timeConsts.init_domain_time_pos
/-- l4v: Time.init_domain_time_bound (axiom). -/
theorem init_domain_time_bound : 15 * unat μsInMs * unat ticksPerTimerUnit < unat maxTime :=
  timeConsts.init_domain_time_bound
/-- l4v: Time.getCurrentTime_buffer_pos (axiom). -/
theorem getCurrentTime_buffer_pos : 0 < 5 * usToTicks MAX_PERIOD_US :=
  timeConsts.getCurrentTime_buffer_pos

/-- l4v: Time.MAX_PERIOD. -/
def MAX_PERIOD : Ticks := usToTicks MAX_PERIOD_US

/-- l4v: Time.kernelWCET_ticks. -/
def kernelWCETTicks : Ticks := usToTicks kernelWCETUs

/-- l4v: Time.time_buffer_const. -/
abbrev timeBufferConst : Ticks := 5

/-- l4v: Time.getCurrentTime_buffer. -/
abbrev getCurrentTimeBuffer : Ticks := timeBufferConst * MAX_PERIOD

/-- l4v: Time.MAX_RELEASE_TIME. -/
def MAX_RELEASE_TIME : Time := maxTime - 5 * MAX_PERIOD

/-! ## MachineTypes (spec/design/m-skel/X64/MachineTypes)

### Register set (Haskell SEL4/Machine/RegisterSet/X64.lhs) -/

/-- l4v: MachineTypes.X64.register (Haskell `Register`). -/
inductive Register where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  | faultIP
  | fsBase | gsBase
  | errorRegister | nextIP | cs | flags | rsp | ss
deriving DecidableEq, Repr, Inhabited

open Register in
/-- Haskell `[RAX .. R15]` (the derived `Enum` range). -/
def Register.raxToR15 : List Register :=
  [rax, rbx, rcx, rdx, rsi, rdi, rbp, r8, r9, r10, r11, r12, r13, r14, r15]

/-- l4v: MachineTypes.X64.capRegister. -/
def capRegister : Register := .rdi
/-- l4v: MachineTypes.X64.msgInfoRegister. -/
def msgInfoRegister : Register := .rsi
/-- l4v: MachineTypes.X64.msgRegisters. -/
def msgRegisters : List Register := [.r10, .r8, .r9, .r15]
/-- l4v: MachineTypes.X64.badgeRegister. -/
def badgeRegister : Register := capRegister
/-- l4v: MachineTypes.X64.faultRegister. -/
def faultRegister : Register := .faultIP
/-- l4v: MachineTypes.X64.nextInstructionRegister. -/
def nextInstructionRegister : Register := .nextIP
/-- l4v: MachineTypes.X64.frameRegisters (`FaultIP : RSP : FLAGS : [RAX .. R15]`). -/
def frameRegisters : List Register := .faultIP :: .rsp :: .flags :: Register.raxToR15
/-- l4v: MachineTypes.X64.gpRegisters. -/
def gpRegisters : List Register := [.fsBase, .gsBase]
/-- l4v: MachineTypes.X64.exceptionMessage. -/
def exceptionMessage : List Register := [.faultIP, .rsp, .flags]
/-- l4v: MachineTypes.X64.tlsBaseRegister. -/
def tlsBaseRegister : Register := .fsBase
/-- l4v: MachineTypes.X64.syscallMessage (`[RAX .. R15] ++ [FaultIP, RSP, FLAGS]`). -/
def syscallMessage : List Register := Register.raxToR15 ++ [.faultIP, .rsp, .flags]

/-- l4v: MachineTypes.X64.replyRegister (rt X64 gap; RISCV64 `replyRegister`).
X64 value from the C kernel's MCS register set: `replyRegister = R12`. -/
def replyRegister : Register := .r12
/-- l4v: MachineTypes.X64.nbsendRecvDest (rt X64 gap; RISCV64
`nbsendRecvDest`). X64 value from the C kernel: `nbsendRecvDest = R13`. -/
def nbsendRecvDest : Register := .r13
/-- l4v: MachineTypes.X64.timeoutMessage (rt X64 gap; RISCV64
`timeoutMessage`). X64 value from the C kernel's `TIMEOUT_REPLY_MESSAGE`:
FaultIP, RSP, FLAGS, RAX..R15, TLS_BASE (= FS_BASE). -/
def timeoutMessage : List Register :=
  [.faultIP, .rsp, .flags] ++ Register.raxToR15 ++ [.fsBase]

/-- l4v: MachineTypes.X64.gdtslot (Haskell `GDTSlot`). -/
inductive GDTSlot where
  | gdtNull | gdtCs0 | gdtDs0 | gdtTss | gdtTssPadding
  | gdtCs3 | gdtDs3 | gdtFs | gdtGs | gdtEntries
deriving DecidableEq, Repr, Inhabited

/-- Haskell derived `fromEnum` on `GDTSlot`. -/
def GDTSlot.fromEnum : GDTSlot → Nat
  | .gdtNull => 0 | .gdtCs0 => 1 | .gdtDs0 => 2 | .gdtTss => 3
  | .gdtTssPadding => 4 | .gdtCs3 => 5 | .gdtDs3 => 6 | .gdtFs => 7
  | .gdtGs => 8 | .gdtEntries => 9

/-- l4v: MachineTypes.X64.gdtToSel. -/
def gdtToSel (g : GDTSlot) : Word := (BitVec.ofNat 64 g.fromEnum <<< 3) ||| 3
/-- l4v: MachineTypes.X64.gdtToSel_masked. -/
def gdtToSel_masked (g : GDTSlot) : Word := gdtToSel g ||| 3

/-- l4v: MachineTypes.X64.selCS3. -/
def selCS3 : Word := gdtToSel_masked .gdtCs3
/-- l4v: MachineTypes.X64.selDS3. -/
def selDS3 : Word := gdtToSel_masked .gdtDs3
/-- l4v: MachineTypes.X64.selFS. -/
def selFS : Word := gdtToSel_masked .gdtFs
/-- l4v: MachineTypes.X64.selGS. -/
def selGS : Word := gdtToSel_masked .gdtGs
/-- l4v: MachineTypes.X64.selCS0. -/
def selCS0 : Word := gdtToSel_masked .gdtCs0
/-- l4v: MachineTypes.X64.selDS0. -/
def selDS0 : Word := gdtToSel .gdtDs0

/-- l4v: MachineTypes.X64.initContext. -/
def initContext : List (Register × Word) :=
  [(.cs, selCS3), (.ss, selDS3), (.flags, (1 <<< 9) ||| (1 <<< 1))]

-- Haskell `type FPUState = Array Word Word8` is not used by the abstract
-- spec, which has its own `fpu_state` (MachineOps); not ported.

/-! ### Machine state -/

/-- Carrier of `MachineStateRest`: some nonempty type (Isabelle `typedecl`
types are nonempty). -/
opaque MachineStateRestType : {α : Type // Nonempty α} := ⟨PUnit, ⟨⟨⟩⟩⟩

/-- l4v: MachineTypes.X64.machine_state_rest (`typedecl`): the
underspecified rest of the machine state. -/
def MachineStateRest : Type := MachineStateRestType.1

instance : Nonempty MachineStateRest := MachineStateRestType.2

/-- l4v: MachineTypes.X64.machine_state. The fields `time_state` and
`last_machine_time` are an rt X64 gap, added as in RISCV64 `machine_state`. -/
structure MachineState where
  irqMasks : Irq → Bool
  irqState : Nat
  /-- position in the time oracle (rt X64 gap) -/
  timeState : Nat
  /-- value read from the timer device (rt X64 gap) -/
  lastMachineTime : Word64
  underlyingMemory : Word64 → Word8
  deviceState : Word64 → Option Word8
  fpuEnabled : Bool
  machineStateRest : MachineStateRest

instance : Nonempty MachineState :=
  ⟨⟨fun _ => false, 0, 0, 0, fun _ => 0, fun _ => none, false, undefined⟩⟩

/-- l4v: MachineTypes.X64.irq_oracle (`consts`, unconstrained on X64). -/
opaque irqOracle : Nat → Word8

/-- l4v: MachineTypes.X64.time_oracle (rt X64 gap; RISCV64 `timeOracle`,
an unconstrained `axiomatization`): how much time passed since the last
query. -/
opaque timeOracle : Nat → Nat

/-- l4v: MachineTypes.X64.machine_monad. -/
abbrev MachineMonad (α : Type) := NonDet MachineState α

/-- l4v: MachineTypes.X64.init_irq_masks. -/
def initIrqMasks : Irq → Bool := fun _ => true

/-- l4v: MachineTypes.X64.init_underlying_memory. -/
def initUnderlyingMemory : Word64 → Word8 := fun _ => 0

/-- l4v: MachineTypes.X64.init_machine_state. -/
def initMachineState : MachineState :=
  { irqMasks := initIrqMasks,
    irqState := 0,
    timeState := 0,
    lastMachineTime := 0,
    underlyingMemory := initUnderlyingMemory,
    deviceState := fun _ => none,
    fpuEnabled := false,
    machineStateRest := undefined }

/-! ### Hardware types (Haskell SEL4/Machine/Hardware/X64.lhs) -/

/-- l4v: MachineTypes.X64.vmfault_type (Haskell `VMFaultType`). -/
inductive VMFaultType where
  | x64DataFault
  | x64InstructionFault
deriving DecidableEq, Repr, Inhabited

/-- l4v: MachineTypes.X64.hyp_fault_type (Haskell `HypFaultType`). -/
inductive HypFaultType where
  | x64NoHypFaults
deriving DecidableEq, Repr, Inhabited

/-- l4v: MachineTypes.X64.vmpage_size (Haskell `VMPageSize`). -/
inductive VMPageSize where
  | x64SmallPage
  | x64LargePage
  | x64HugePage
deriving DecidableEq, Repr, Inhabited

/-- l4v: MachineTypes.X64.vmmap_type (Haskell `VMMapType`). The
`VMIOSpaceMap` case is commented out in the Haskell spec too (no IOMMU). -/
inductive VMMapType where
  | vmNoMap
  | vmVSpaceMap
  | vmEptMap
deriving DecidableEq, Repr, Inhabited

/-- l4v: MachineTypes.X64.pageBits. -/
def pageBits : Nat := 12

/-- l4v: MachineTypes.X64.ptTranslationBits. -/
def ptTranslationBits : Nat := 9

/-- l4v: MachineTypes.X64.pageBitsForSize. -/
def pageBitsForSize : VMPageSize → Nat
  | .x64SmallPage => pageBits
  | .x64LargePage => pageBits + ptTranslationBits
  | .x64HugePage => pageBits + ptTranslationBits + ptTranslationBits

/-! ## MachineMonad (spec/machine/MachineMonad) -/

/-- l4v: MachineMonad.machine_rest_monad. -/
abbrev MachineRestMonad (α : Type) := NonDet MachineStateRest α

/-- l4v: MachineMonad.machine_rest_lift. -/
def machineRestLift {α : Type} (f : MachineRestMonad α) : MachineMonad α := do
  let mr ← NonDet.gets MachineState.machineStateRest
  let (r, mr') ← NonDet.selectF (f mr)
  NonDet.modify fun s => { s with machineStateRest := mr' }
  return r

/-- l4v: MachineMonad.ignore_failure. -/
def ignoreFailure {σ : Type} (f : NonDet σ Unit) : NonDet σ Unit := fun s =>
  if (f s).1 = ∅ then ({((), s)}, False) else ((f s).1, False)

/-- l4v: MachineMonad.machine_op_lift. -/
def machineOpLift (f : MachineRestMonad Unit) : MachineMonad Unit :=
  machineRestLift (ignoreFailure f)

/-! ## MachineOps (spec/machine/X64/MachineOps) -/

/-- l4v: MachineOps.X64.memory_regions (`consts'`, avail_p_regs). -/
opaque memoryRegions : List (Paddr × Paddr)
/-- l4v: MachineOps.X64.device_regions (`consts'`, dev_p_regs). -/
opaque deviceRegions : List (Paddr × Paddr)

/-- l4v: MachineOps.X64.getMemoryRegions. -/
def getMemoryRegions : MachineMonad (List (Paddr × Paddr)) := return memoryRegions

/-- l4v: MachineOps.X64.getDeviceRegions_impl (`consts'`). -/
opaque getDeviceRegionsImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.getDeviceRegions_val (`consts'`). -/
opaque getDeviceRegionsVal : MachineState → List (Paddr × Paddr)

/-- l4v: MachineOps.X64.getDeviceRegions. -/
def getDeviceRegions : MachineMonad (List (Paddr × Paddr)) := return deviceRegions

/-- l4v: MachineOps.X64.getKernelDevices_impl (`consts'`). -/
opaque getKernelDevicesImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.getKernelDevices_val (`consts'`). -/
opaque getKernelDevicesVal : MachineState → List (Paddr × Word)

/-- l4v: MachineOps.X64.getKernelDevices. -/
def getKernelDevices : MachineMonad (List (Paddr × Word)) := do
  machineOpLift getKernelDevicesImpl
  NonDet.gets getKernelDevicesVal

/-- l4v: MachineOps.X64.loadWord. -/
def loadWord (p : Word) : MachineMonad Word := do
  let m ← NonDet.gets MachineState.underlyingMemory
  NonDet.assert (p &&& mask 3 = 0)
  return wordRcat ((intUpto 0 7).map fun i => m (p + (7 - BitVec.ofInt 64 i)))

/-- l4v: MachineOps.X64.storeWord. -/
def storeWord (p : Word) (w : Word) : MachineMonad Unit := do
  NonDet.assert (p &&& mask 3 = 0)
  NonDet.modify fun s =>
    let mem := (intUpto 0 7).foldl
      (fun m i => Function.update m (p + BitVec.ofInt 64 i)
        ((wordRsplit w : List Word8).getD (7 - i.toNat) 0))
      s.underlyingMemory
    { s with underlyingMemory := mem }

/-- l4v: MachineOps.X64.storeWordVM. -/
def storeWordVM (_w _p : Word) : MachineMonad Unit := return ()

/-- l4v: MachineOps.X64.configureTimer_impl (`consts'`). -/
opaque configureTimerImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.configureTimer_val (`consts'`). -/
opaque configureTimerVal : MachineState → Irq

/-- l4v: MachineOps.X64.configureTimer. -/
def configureTimer : MachineMonad Irq := do
  machineOpLift configureTimerImpl
  NonDet.gets configureTimerVal

/-- l4v: MachineOps.X64.initTimer_impl (`consts'`). -/
opaque initTimerImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.initTimer. -/
def initTimer : MachineMonad Unit := machineOpLift initTimerImpl

/-- l4v: MachineOps.X64.resetTimer_impl (`consts'`). -/
opaque resetTimerImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.resetTimer. -/
def resetTimer : MachineMonad Unit := machineOpLift resetTimerImpl

/-- l4v: MachineOps.X64.getCurrentTime (rt X64 gap; RISCV64
`getCurrentTime`). Time increases monotonically and the 64-bit time does
not overflow during the lifetime of the system. -/
def getCurrentTime : MachineMonad Word64 := do
  NonDet.modify fun s => { s with timeState := s.timeState + 1 }
  let passed ← NonDet.gets (timeOracle ∘ MachineState.timeState)
  let last' ← NonDet.gets MachineState.lastMachineTime
  let last ← pure (unat last')
  let current ← pure (min (unat (-(getCurrentTimeBuffer + 1))) (last + passed))
  NonDet.modify fun s => { s with lastMachineTime := BitVec.ofNat 64 current }
  return (BitVec.ofNat 64 current)

/-- l4v: MachineOps.X64.setDeadline_impl (rt X64 gap; RISCV64, `consts'`). -/
opaque setDeadlineImpl : Word64 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.setDeadline (rt X64 gap; RISCV64 `setDeadline`). -/
def setDeadline (d : Word64) : MachineMonad Unit := machineOpLift (setDeadlineImpl d)

/-- l4v: MachineOps.X64.invalidateTLB_impl (`consts'`). -/
opaque invalidateTLBImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.invalidateTLB. -/
def invalidateTLB : MachineMonad Unit := machineOpLift invalidateTLBImpl

/-- l4v: MachineOps.X64.debugPrint. -/
def debugPrint (_message : List Unit) : MachineMonad Unit := return ()

/-- l4v: MachineOps.X64.non_kernel_IRQs. Empty on plain x86-64. -/
def nonKernelIRQs : Set Irq := ∅

/-- l4v: MachineOps.X64.getActiveIRQ. -/
def getActiveIRQ (in_kernel : Bool) : MachineMonad (Option Irq) := do
  let is_masked ← NonDet.gets MachineState.irqMasks
  NonDet.modify fun s => { s with irqState := s.irqState + 1 }
  let active_irq ← NonDet.gets (irqOracle ∘ MachineState.irqState)
  if is_masked active_irq ∨ active_irq = 0xFF ∨ (in_kernel ∧ active_irq ∈ nonKernelIRQs)
  then return none
  else return (some active_irq)

/-- l4v: MachineOps.X64.maskInterrupt. -/
def maskInterrupt (m : Bool) (irq : Irq) : MachineMonad Unit :=
  NonDet.modify fun s => { s with irqMasks := Function.update s.irqMasks irq m }

/-- l4v: MachineOps.X64.ackInterrupt. -/
def ackInterrupt (_irq : Irq) : MachineMonad Unit := return ()

/-- l4v: MachineOps.X64.deadlineIRQ (rt X64 gap; RISCV64, `consts'`). -/
opaque deadlineIRQ : Irq

/-- l4v: MachineOps.X64.ackDeadlineIRQ (rt X64 gap; RISCV64 `ackDeadlineIRQ`). -/
def ackDeadlineIRQ : MachineMonad Unit := ackInterrupt deadlineIRQ

/-- l4v: MachineOps.X64.setInterruptMode. -/
def setInterruptMode (_irq : Irq) (_levelTrigger _polarityLow : Bool) : MachineMonad Unit :=
  return ()

/-- l4v: MachineOps.X64.clearMemory. -/
def clearMemory (ptr : Word) (bytelength : Nat) : MachineMonad Unit :=
  NonDet.mapMx (fun p => storeWord p 0)
    (uptoEnumStep ptr (ptr + BitVec.ofNat 64 wordSize) (ptr + BitVec.ofNat 64 bytelength - 1))

/-- l4v: MachineOps.X64.clearMemoryVM. -/
def clearMemoryVM (_ptr : Word) (_bits : Nat) : MachineMonad Unit := return ()

/-- l4v: MachineOps.X64.initMemory (`abbreviation`). -/
abbrev initMemory : Word → Nat → MachineMonad Unit := clearMemory

/-- l4v: MachineOps.X64.freeMemory. -/
def freeMemory (ptr : Word) (bits : Nat) : MachineMonad Unit :=
  NonDet.mapMx (fun p => storeWord p 0)
    (uptoEnumStep ptr (ptr + BitVec.ofNat 64 wordSize) (ptr + 2 ^ bits - 1))

/-- l4v: MachineOps.X64.fpu_bytes (the numeral type `576`). -/
abbrev fpuBytes : Nat := 576
/-- l4v: MachineOps.X64.fpu_state. -/
abbrev FpuState := Fin fpuBytes → BitVec 8
/-- l4v: MachineOps.X64.user_regs. -/
abbrev UserRegs := Register → Word

/-- l4v: MachineOps.X64.user_context (`UserContext user_fpu_state user_regs`). -/
structure UserContext where
  userFpuState : FpuState
  userRegs : UserRegs

instance : Inhabited UserContext := ⟨⟨fun _ => 0, fun _ => 0⟩⟩

/-- l4v: MachineOps.X64.user_monad. -/
abbrev UserMonad (α : Type) := NonDet UserContext α

/-- l4v: MachineOps.X64.getRegister. -/
def getRegister (r : Register) : UserMonad Word := NonDet.gets fun s => s.userRegs r

/-- l4v: MachineOps.X64.modify_registers. -/
def modifyRegisters (f : UserRegs → UserRegs) (uc : UserContext) : UserContext :=
  ⟨uc.userFpuState, f uc.userRegs⟩

/-- l4v: MachineOps.X64.setRegister. -/
def setRegister (r : Register) (v : Word) : UserMonad Unit :=
  NonDet.modify fun s => ⟨s.userFpuState, Function.update s.userRegs r v⟩

/-- l4v: MachineOps.X64.getRestartPC. -/
def getRestartPC : UserMonad Word := getRegister .faultIP

/-- l4v: MachineOps.X64.setNextPC. -/
def setNextPC : Word → UserMonad Unit := setRegister .nextIP

/-- l4v: MachineOps.X64.getFPUState. -/
def getFPUState : UserMonad FpuState := NonDet.gets UserContext.userFpuState

/-- l4v: MachineOps.X64.setFPUState. -/
def setFPUState (fc : FpuState) : UserMonad Unit := NonDet.modify fun s => ⟨fc, s.userRegs⟩

/-- l4v: MachineOps.X64.FPUNullState (`consts'`): a constant snapshot of the
FPU taken after initialisation. -/
opaque FPUNullState : FpuState

/-- l4v: MachineOps.X64.readFpuState_val (`consts'`). -/
opaque readFpuStateVal : MachineStateRest → FpuState

/-- l4v: MachineOps.X64.readFpuState. -/
def readFpuState : MachineMonad FpuState := do
  NonDet.stateAssert fun s => s.fpuEnabled = true
  machineRestLift (NonDet.gets readFpuStateVal)

/-- l4v: MachineOps.X64.writeFpuState_impl (`consts'`). -/
opaque writeFpuStateImpl : FpuState → MachineRestMonad Unit

/-- l4v: MachineOps.X64.writeFpuState. -/
def writeFpuState (val : FpuState) : MachineMonad Unit := do
  NonDet.stateAssert fun s => s.fpuEnabled = true
  machineOpLift (writeFpuStateImpl val)

/-- l4v: MachineOps.X64.enableFpu_impl (`consts'`). -/
opaque enableFpuImpl : MachineRestMonad Unit

/-- l4v: MachineOps.X64.enableFpu. -/
def enableFpu : MachineMonad Unit := do
  machineOpLift enableFpuImpl
  NonDet.modify fun s => { s with fpuEnabled := true }

/-- l4v: MachineOps.X64.disableFpu_impl (`consts'`). -/
opaque disableFpuImpl : MachineRestMonad Unit

/-- l4v: MachineOps.X64.disableFpu. -/
def disableFpu : MachineMonad Unit := do
  machineOpLift disableFpuImpl
  NonDet.modify fun s => { s with fpuEnabled := false }

/-- l4v: MachineOps.X64.isFpuEnable. -/
def isFpuEnable : MachineMonad Bool := NonDet.gets MachineState.fpuEnabled

/-- l4v: MachineOps.X64.initL2Cache_impl (`consts'`). -/
opaque initL2CacheImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.initL2Cache. -/
def initL2Cache : MachineMonad Unit := machineOpLift initL2CacheImpl

/-- l4v: MachineOps.X64.writeCR3_impl (`consts'`). -/
opaque writeCR3Impl : Word → Word → MachineRestMonad Unit
/-- l4v: MachineOps.X64.writeCR3. -/
def writeCR3 (vspace pcid : Word) : MachineMonad Unit := machineOpLift (writeCR3Impl vspace pcid)

/-- l4v: MachineOps.X64.mfence_impl (`consts'`). -/
opaque mfenceImpl : MachineRestMonad Unit
/-- l4v: MachineOps.X64.mfence. -/
def mfence : MachineMonad Unit := machineOpLift mfenceImpl

/-- l4v: MachineOps.X64.invalidateTLBEntry_impl (`consts'`). -/
opaque invalidateTLBEntryImpl : Word64 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.invalidateTLBEntry. -/
def invalidateTLBEntry (vptr : Word64) : MachineMonad Unit :=
  machineOpLift (invalidateTLBEntryImpl vptr)

/-- l4v: MachineOps.X64.invalidateTranslationSingleASID_impl (`consts'`). -/
opaque invalidateTranslationSingleASIDImpl : Word → Word → MachineRestMonad Unit
/-- l4v: MachineOps.X64.invalidateTranslationSingleASID. -/
def invalidateTranslationSingleASID (vptr asid : Word) : MachineMonad Unit :=
  machineOpLift (invalidateTranslationSingleASIDImpl vptr asid)

/-- l4v: MachineOps.X64.invalidateASID_impl (`consts'`). -/
opaque invalidateASIDImpl : Word → Word → MachineRestMonad Unit
/-- l4v: MachineOps.X64.invalidateASID. -/
def invalidateASID (vspace asid : Word) : MachineMonad Unit :=
  machineOpLift (invalidateASIDImpl vspace asid)

/-- l4v: MachineOps.X64.invalidateLocalPageStructureCacheASID_impl (`consts'`). -/
opaque invalidateLocalPageStructureCacheASIDImpl : Word → Word → MachineRestMonad Unit
/-- l4v: MachineOps.X64.invalidateLocalPageStructureCacheASID. -/
def invalidateLocalPageStructureCacheASID (vspace asid : Word) : MachineMonad Unit :=
  machineOpLift (invalidateLocalPageStructureCacheASIDImpl vspace asid)

/-- l4v: MachineOps.X64.getFaultAddress_val (`consts'`). -/
opaque getFaultAddressVal : MachineState → Word
/-- l4v: MachineOps.X64.getFaultAddress. -/
def getFaultAddress : MachineMonad Word64 := NonDet.gets getFaultAddressVal

/-- l4v: MachineOps.X64.irqIntOffset_val (`consts'`, unused). -/
opaque irqIntOffsetVal : MachineState → Word
/-- l4v: MachineOps.X64.irqIntOffset. -/
def irqIntOffset : Word := 0x20

/-- l4v: MachineOps.X64.maxPCIBus. -/
def maxPCIBus : Word := 0xFF
/-- l4v: MachineOps.X64.maxPCIDev. -/
def maxPCIDev : Word := 31
/-- l4v: MachineOps.X64.maxPCIFunc. -/
def maxPCIFunc : Word := 7
/-- l4v: MachineOps.X64.ioapicIRQLines. -/
def ioapicIRQLines : Word := 24

/-- l4v: MachineOps.X64.ioapicMapPinToVector_impl (`consts'`). -/
opaque ioapicMapPinToVectorImpl : Word → Word → Word → Word → Word → MachineRestMonad Unit
/-- l4v: MachineOps.X64.ioapicMapPinToVector. -/
def ioapicMapPinToVector (ioapic pin level polarity vector : Word) : MachineMonad Unit :=
  machineOpLift (ioapicMapPinToVectorImpl ioapic pin level polarity vector)

/-- l4v: MachineOps.X64.IRQ. -/
def IRQ (x : Word8) : Irq := x

/-- l4v: MachineOps.X64.in8_impl (`consts'`). -/
opaque in8Impl : Word16 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.in8_val (`consts'`). -/
opaque in8Val : MachineState → Word
/-- l4v: MachineOps.X64.in8. -/
def in8 (port : Word16) : MachineMonad Word := do
  machineOpLift (in8Impl port); NonDet.gets in8Val

/-- l4v: MachineOps.X64.in16_impl (`consts'`). -/
opaque in16Impl : Word16 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.in16_val (`consts'`). -/
opaque in16Val : MachineState → Word
/-- l4v: MachineOps.X64.in16. -/
def in16 (port : Word16) : MachineMonad Word := do
  machineOpLift (in16Impl port); NonDet.gets in16Val

/-- l4v: MachineOps.X64.in32_impl (`consts'`). -/
opaque in32Impl : Word16 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.in32_val (`consts'`). -/
opaque in32Val : MachineState → Word
/-- l4v: MachineOps.X64.in32. -/
def in32 (port : Word16) : MachineMonad Word := do
  machineOpLift (in32Impl port); NonDet.gets in32Val

/-- l4v: MachineOps.X64.out8_impl (`consts'`). -/
opaque out8Impl : Word16 → Word8 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.out8. -/
def out8 (port : Word16) (dat : Word8) : MachineMonad Unit := machineOpLift (out8Impl port dat)

/-- l4v: MachineOps.X64.out16_impl (`consts'`). -/
opaque out16Impl : Word16 → Word16 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.out16. -/
def out16 (port : Word16) (dat : Word16) : MachineMonad Unit :=
  machineOpLift (out16Impl port dat)

/-- l4v: MachineOps.X64.out32_impl (`consts'`). -/
opaque out32Impl : Word16 → Word32 → MachineRestMonad Unit
/-- l4v: MachineOps.X64.out32. -/
def out32 (port : Word16) (dat : Word32) : MachineMonad Unit :=
  machineOpLift (out32Impl port dat)

/-! ## Machine_A (spec/abstract/X64/Machine_A) -/

/-- l4v: Machine_A.X64_A.obj_ref. -/
abbrev ObjRef := Word
/-- l4v: Machine_A.X64_A.vspace_ref. -/
abbrev VSpaceRef := Word
/-- l4v: Machine_A.X64_A.data. -/
abbrev Data := Word
/-- l4v: Machine_A.X64_A.cap_ref. -/
abbrev CapRef := List Bool
/-- l4v: Machine_A.X64_A.length_type. -/
abbrev LengthType := Word

/-- l4v: Machine_A.X64_A.asid_low_len. -/
abbrev asidLowLen : Nat := 9
/-- l4v: Machine_A.X64_A.asid_low_index. -/
abbrev AsidLowIndex := BitVec asidLowLen
/-- l4v: Machine_A.X64_A.asid_high_len. FL4 has 2048 ASID pools, not 8
(PORTING.md). -/
abbrev asidHighLen : Nat := 11
/-- l4v: Machine_A.X64_A.asid_high_index. -/
abbrev AsidHighIndex := BitVec asidHighLen
/-- l4v: Machine_A.X64_A.asid_len: 20 in FL4, 12 in l4v. -/
abbrev asidLen : Nat := 20
/-- l4v: Machine_A.X64_A.asid_rep_len (`machine_word_len`). -/
abbrev asidRepLen : Nat := 64
/-- l4v: Machine_A.X64_A.asid. -/
abbrev Asid := BitVec asidRepLen

/-- l4v: Machine_A.X64_A.oref_to_data. -/
def orefToData (x : ObjRef) : Data := x
/-- l4v: Machine_A.X64_A.data_to_oref. -/
def dataToOref (x : Data) : ObjRef := x
/-- l4v: Machine_A.X64_A.vref_to_data. -/
def vrefToData (x : VSpaceRef) : Data := x
/-- l4v: Machine_A.X64_A.data_to_vref. -/
def dataToVref (x : Data) : VSpaceRef := x
/-- l4v: Machine_A.X64_A.nat_to_len. -/
def natToLen (n : Nat) : LengthType := BitVec.ofNat 64 n
/-- l4v: Machine_A.X64_A.data_to_nat. -/
def dataToNat (x : Data) : Nat := unat x
/-- l4v: Machine_A.X64_A.data_to_16. -/
def dataTo16 (x : Data) : BitVec 16 := ucast 16 x
/-- l4v: Machine_A.X64_A.data_to_cptr. -/
def dataToCptr (x : Data) : CapRef := toBl x
/-- l4v: Machine_A.X64_A.combine_ntfn_badges. -/
def combineNtfnBadges (a b : Data) : Data := a ||| b
/-- l4v: Machine_A.X64_A.combine_ntfn_msgs. -/
def combineNtfnMsgs (a b : Data) : Data := a ||| b

/-- l4v: Machine_A.X64_A.slot_bits. -/
def slotBits : Nat := 5
/-- l4v: Machine_A.X64_A.msg_label_bits. -/
def msgLabelBits : Nat := 52

/-- l4v: Machine_A.X64_A.new_context. -/
def newContext : UserContext :=
  ⟨FPUNullState,
   Function.update (Function.update (Function.update (fun _ => 0) .cs selCS3) .ss selDS3)
     .flags 0x202⟩

/-- l4v: Machine_A.X64_A.pptr_base. -/
def pptr_base : Word := pptrBase
/-- l4v: Machine_A.X64_A.user_vtop. -/
def userVtop : Word := pptrUserTop
/-- l4v: Machine_A.X64_A.kernel_base. The lowest virtual address in the
kernel window. -/
def kernelBase : VSpaceRef := 0xffffffff80000000
/-- l4v: Machine_A.X64_A.idle_thread_ptr. -/
def idleThreadPtr : VSpaceRef := kernelBase + 0x1000

/-- l4v: Machine_A.X64_A.idle_sc_ptr (rt X64 gap; RISCV64 `idle_sc_ptr =
pptr_base + 0x3000`): the idle thread's scheduling context. The C kernel
has no fixed address for it (x86-64 MCS `ksIdleSC` points at the BSS array
`ksIdleThreadSC`, aligned to `seL4_MinSchedContextBits`), and l4v picks an
arbitrary aligned address next to the idle TCB: every MCS architecture on
`rt` (RISCV64, AARCH64, ARM) uses `idle_thread_ptr + 0x2000`. On X64 that
address is inside the 8KiB `init_irq_node_ptr` region (`kernel_base +
0x2000 .. 0x3fff`, X64 Init_A), and the global paging structures follow up
to `kernel_base + 0x6000`, so this uses the next free page (aligned for
the idle SC's `min_sched_context_bits + 0` bits). -/
def idleScPtr : VSpaceRef := kernelBase + 0x7000

/-- l4v: Machine_A.X64_A.nat_to_cref. -/
def natToCref (len n : Nat) : CapRef := (toBl (BitVec.ofNat 64 n)).drop (wordBits - len)

/-- l4v: Machine_A.X64_A.msg_info_register. -/
def msg_info_register : Register := msgInfoRegister
/-- l4v: Machine_A.X64_A.msg_registers. -/
def msg_registers : List Register := msgRegisters
/-- l4v: Machine_A.X64_A.cap_register. -/
def cap_register : Register := capRegister
/-- l4v: Machine_A.X64_A.badge_register. -/
def badge_register : Register := badgeRegister
/-- l4v: Machine_A.X64_A.frame_registers. -/
def frame_registers : List Register := frameRegisters
/-- l4v: Machine_A.X64_A.gp_registers. -/
def gp_registers : List Register := gpRegisters
/-- l4v: Machine_A.X64_A.exception_message. -/
def exception_message : List Register := exceptionMessage
/-- l4v: Machine_A.X64_A.syscall_message. -/
def syscall_message : List Register := syscallMessage

/-- l4v: Machine_A.X64_A.arch_fault. -/
inductive ArchFault where
  | vmFault (addr : VSpaceRef) (msg : List Word)
deriving DecidableEq, Repr, Inhabited

/-! ## MiscMachine_A (spec/abstract/MiscMachine_A) -/

/-- l4v: MiscMachine_A.asid_high_bits. -/
def asidHighBits : Nat := asidHighLen
/-- l4v: MiscMachine_A.asid_low_bits. -/
def asidLowBits : Nat := asidLowLen
/-- l4v: MiscMachine_A.asid_bits. -/
def asidBits : Nat := asidLen

-- l4v MiscMachine_A.ipa_size depends on the ARM-only
-- `config_ARM_PA_SIZE_BITS_40`; not ported (X64 only).

end

end Fl4Spec
