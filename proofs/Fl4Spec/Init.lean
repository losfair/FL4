/-
A dummy initial kernel state (MCS, x86-64).

Ports `spec/abstract/X64/Init_A` (imports Retype_A). l4v: "This is not a
specification of true kernel initialisation. This theory describes a dummy
initial state only, to show that the invariants and refinement relation are
consistent."

rt X64 gap: X64 Init_A on `rt` builds the non-MCS idle TCB (`tcb_reply`,
`tcb_caller`, `tcb_time_slice`, a `cap_ref` fault handler) and state (no
time or scheduling-context fields). The idle TCB, the idle scheduling
context and the MCS fields of `init_A_st` are taken from RISCV64 `rt`
Init_A: the TCB has NullCap fault and timeout handlers and
`tcb_sched_context = Some idle_sc_ptr`; `idle_sc_ptr` holds the idle
scheduling context (bound to the idle thread, refills `[(0, MAX_PERIOD),
(MAX_PERIOD, 0)]`, budget `MAX_PERIOD`, `MIN_REFILLS` refills, size bits 0);
`consumed_time = 0`, `cur_time = 0`, `cur_sc = idle_sc_ptr`,
`reprogram_timer = False`, `release_queue = []`. The X64 address layout
(IRQ node, global paging structures) and arch state are X64's.

`spec/abstract/KernelInit_A` is not ported: l4v marks it "FIXME: unused,
out of date", it is commented out of `spec/ROOT` (it does not build), and it
is an ARM32 (iMX31) boot model with 32-bit words and fields that no longer
exist (`tcb_reply`, `tcb_caller`, `arm_global_pd`, `CPSR`, `ARMSection`).
-/
import Fl4Spec.Retype

namespace Fl4Spec

open Classical

noncomputable section

/-- l4v: Init_A.X64_A.init_irq_node_ptr (8KiB: 256 one-slot CNodes of
`2 ^ cte_level_bits` bytes). -/
def initIrqNodePtr : ObjRef := kernelBase + 0x2000

/-- l4v: Init_A.X64_A.init_global_pml4 (4KiB). -/
def initGlobalPml4 : ObjRef := kernelBase + 0x4000

/-- l4v: Init_A.X64_A.init_global_pdpt (4KiB). -/
def initGlobalPdpt : ObjRef := kernelBase + 0x5000

/-- l4v: Init_A.X64_A.init_global_pd (4KiB). -/
def initGlobalPd : ObjRef := kernelBase + 0x6000

/-- l4v: Init_A.X64_A.init_arch_state. -/
def initArchState : ArchState :=
  { x64AsidTable := fun _ => none,
    x64GlobalPml4 := initGlobalPml4,
    x64KernelVspace :=
      fun ref => if ref ∈ {x | pptr_base ≤ x ∧ x ≤ pptr_base + mask pml4ShiftBits}
              then .x64VSpaceKernelWindow
              else .x64VSpaceInvalidRegion,
    x64GlobalPts := [],
    x64GlobalPdpts := [initGlobalPdpt],
    x64GlobalPds := [initGlobalPd],
    x64CurrentCr3 := .cr3 0 0,
    x64AllocatedIoPorts := fun _ => false,
    x64NumIoapics := 1,
    x64IoapicNirqs := fun _ => ucast 8 ioapicIRQLines,
    x64IrqState := fun _ => .irqFree,
    x64CurrentFpuOwner := none }

/-- l4v: Init_A.X64_A.global_pml4. -/
def globalPml4 : BitVec 9 → PML4E :=
  Function.update (fun _ => .invalidPML4E)
    0x1FF (.pdPointerTablePML4E (addrFromPPtr initGlobalPdpt) ∅ ∅)

/-- l4v: Init_A.X64_A.global_pdpt: the kernel uses huge page mappings in the
global PDPT to get a view of all physical memory; the upper-most PDPT entry
maps to the global page directory. -/
def globalPdpt : BitVec 9 → PDPTE :=
  Function.update (fun i => .hugePagePDPTE (ucast 64 i <<< 30) ∅ ∅)
    0x1FF (.pageDirectoryPDPTE (addrFromPPtr initGlobalPd) ∅ ∅)

/-- l4v: Init_A.X64_A.global_pd (`0x03FE00 + ucast i << 21`: Isabelle `<<`
binds weaker than `+`). C kernel initialisation refines this down to small
pages for devices. -/
def globalPd : BitVec 9 → PDE :=
  fun i => .largePagePDE ((0x03FE00 + ucast 64 i) <<< 21) ∅ ∅

/-- l4v: Init_A.X64_A.init_kheap (MCS idle TCB and idle scheduling context
from RISCV64 `rt`; see the module comment). -/
def initKheap : KHeap :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun x => if ∃ irq : Irq, initIrqNodePtr + (ucast 64 irq <<< cteLevelBits) = x
              then some (.cnode 0 (emptyCnode 0))
              else none)
    idleThreadPtr (some (.tcb
      { tcbCtable := .nullCap,
        tcbVtable := .nullCap,
        tcbIpcframe := .nullCap,
        tcbFaultHandler := .nullCap,
        tcbTimeoutHandler := .nullCap,
        tcbEpt := .nullCap,
        tcbState := .idleThreadState,
        tcbIpcBuffer := 0,
        tcbFault := none,
        tcbBoundNotification := none,
        tcbMcpriority := 0,
        tcbSchedContext := some idleScPtr,
        tcbYieldTo := none,
        tcbPriority := 0,
        tcbDomain := defaultDomain,
        tcbFlags := ∅,
        tcbArch := initArchTcb })))
    idleScPtr (some (.schedContext
      { defaultSchedContext with
        scTcb := some idleThreadPtr,
        scRefills := [{ rTime := 0, rAmount := MAX_PERIOD }, { rTime := MAX_PERIOD, rAmount := 0 }],
        scBudget := MAX_PERIOD,
        scRefillMax := MIN_REFILLS } 0)))
    initGlobalPml4 (some (.archObj (.pageMapL4 globalPml4))))
    initGlobalPdpt (some (.archObj (.pdPointerTable globalPdpt))))
    initGlobalPd (some (.archObj (.pageDirectory globalPd)))

/-- l4v: Init_A.X64_A.init_cdt. -/
def initCdt : Cdt := fun _ => none

/-- l4v: Init_A.X64_A.init_ioc: the non-null caps of the initial heap are
original. -/
def initIoc : CslotPtr → Bool := fun (a, b) =>
  decide (∃ obj, initKheap a = some obj ∧ (∃ cap, capOf obj b = some cap ∧ ¬cap = .nullCap))

/-- l4v: Init_A.X64_A.init_A_st (MCS fields from RISCV64 `rt`). -/
def initASt {Z : Type} [StateExt Z] : State Z :=
  { kheap := initKheap,
    cdt := initCdt,
    isOriginalCap := initIoc,
    curThread := idleThreadPtr,
    idleThread := idleThreadPtr,
    consumedTime := 0,
    curTime := 0,
    curSc := idleScPtr,
    reprogramTimer := false,
    schedulerAction := .resumeCurThread,
    domainList := [(0, -1), (0, 0)],
    domainIndex := 0,
    domainStartIndex := 0,
    curDomain := 0,
    domainTime := 15,
    readyQueues := fun _ _ => [],
    releaseQueue := [],
    machineState := initMachineState,
    interruptIrqNode := fun irq => initIrqNodePtr + (ucast 64 irq <<< cteLevelBits),
    interruptStates := fun _ => .irqInactive,
    archState := initArchState,
    exst := StateExt.extInit }

end

end Fl4Spec
