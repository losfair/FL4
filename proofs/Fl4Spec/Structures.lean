/-
The architecture-independent data types of the seL4 abstract specification
(MCS): capabilities, kernel objects and the kernel state.

Ports `spec/abstract/Structures_A`. Its `arch_requalify` lines refer to the
X64 definitions in `Fl4Spec.X64.Structs`. Lemmas (`cap_cases`,
`is_blocked_thread_state_simps`, `MIN_BUDGET_pos`, `msg_align_bits'`, ...)
are not ported.
-/
import Fl4Spec.X64.Structs
import Mathlib.Data.Nat.Find

namespace Fl4Spec

open Classical

noncomputable section

/-- l4v: Structures_A.apiobject_type: the objects user mode can ask retype to
create. -/
inductive ApiObjectType where
  | untyped
  | tcbObject
  | endpointObject
  | notificationObject
  | capTableObject
  | schedContextObject
  | replyObject
  | archObject (t : AObjectType)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.is_frame_type. -/
def isFrameType (obj : ApiObjectType) : Bool :=
  match obj with
  | .archObject aobj => archIsFrameType aobj
  | _ => false

/-- l4v: Structures_A.badge. -/
abbrev Badge := Data
/-- l4v: Structures_A.msg_label. -/
abbrev MsgLabel := Data
/-- l4v: Structures_A.message. -/
abbrev Message := Data

/-- l4v: Structures_A.cnode_index. -/
abbrev CnodeIndex := List Bool
/-- l4v: Structures_A.cslot_ptr: the object holding the slot and the slot's
index in it. -/
abbrev CslotPtr := ObjRef × CnodeIndex

/-- l4v: Structures_A.cap. -/
inductive Cap where
  | nullCap
  /-- device flag, pointer, size in bits, free index -/
  | untypedCap (dev : Bool) (ref : ObjRef) (bits : Nat) (freeIndex : Nat)
  | endpointCap (ref : ObjRef) (badge : Badge) (rights : CapRights)
  | notificationCap (ref : ObjRef) (badge : Badge) (rights : CapRights)
  | replyCap (ref : ObjRef) (rights : CapRights)
  /-- CNode pointer, number of bits translated, guard -/
  | cnodeCap (ref : ObjRef) (bits : Nat) (guard : List Bool)
  | threadCap (ref : ObjRef)
  | domainCap
  | schedContextCap (ref : ObjRef) (bits : Nat)
  | schedControlCap
  | irqControlCap
  | irqHandlerCap (irq : Irq)
  /-- cnode pointer, `none` for a TCB or the cnode size, number of slots -/
  | zombie (ref : ObjRef) (bits : Option Nat) (n : Nat)
  | archObjectCap (theArchCap : ArchCap)
deriving Inhabited

/-- l4v: Structures_A.the_arch_cap (selector). -/
def Cap.theArchCap : Cap → ArchCap
  | .archObjectCap a => a
  | _ => undefined

/-- l4v: Structures_A.cnode_contents. Empty slots hold `NullCap`; the
domain is all bit lists of one length. -/
abbrev CnodeContents := CnodeIndex → Option Cap

/-- l4v: Structures_A.the_cnode_cap. -/
def theCnodeCap (cap : Cap) : ObjRef × Nat × List Bool :=
  match cap with
  | .cnodeCap oref bits guard => (oref, bits, guard)
  | _ => undefined

/-- l4v: Structures_A.cap_ep_badge (`nonexhaustive`). -/
def capEpBadge : Cap → Badge
  | .endpointCap _ badge _ => badge
  | .notificationCap _ badge _ => badge
  | _ => undefined

/-- l4v: Structures_A.cap_ep_ptr (`nonexhaustive`). -/
def capEpPtr : Cap → Badge
  | .endpointCap objRef _ _ => objRef
  | .notificationCap objRef _ _ => objRef
  | _ => undefined

/-- l4v: Structures_A.bits_of. -/
def bitsOf (cap : Cap) : Nat :=
  match cap with
  | .untypedCap _ _ bits _ => bits
  | .schedContextCap _ n => n
  | .cnodeCap _ radixBits _ => radixBits
  | _ => undefined

/-- l4v: Structures_A.free_index_of. -/
def freeIndexOf (cap : Cap) : Nat :=
  match cap with
  | .untypedCap _ _ _ freeIndex => freeIndex
  | _ => undefined

/-- l4v: Structures_A.is_reply_cap. -/
def isReplyCap (cap : Cap) : Bool := match cap with | .replyCap _ _ => true | _ => false
/-- l4v: Structures_A.is_zombie. -/
def isZombie (cap : Cap) : Bool := match cap with | .zombie _ _ _ => true | _ => false
/-- l4v: Structures_A.is_arch_cap. -/
def isArchCap (cap : Cap) : Bool := match cap with | .archObjectCap _ => true | _ => false

/-- l4v: Structures_A.is_cnode_cap. -/
def isCnodeCap : Cap → Bool
  | .cnodeCap _ _ _ => true
  | _ => false
/-- l4v: Structures_A.is_thread_cap. -/
def isThreadCap : Cap → Bool
  | .threadCap _ => true
  | _ => false
/-- l4v: Structures_A.is_domain_cap. -/
def isDomainCap : Cap → Bool
  | .domainCap => true
  | _ => false
/-- l4v: Structures_A.is_untyped_cap. -/
def isUntypedCap : Cap → Bool
  | .untypedCap _ _ _ _ => true
  | _ => false
/-- l4v: Structures_A.is_ep_cap. -/
def isEpCap : Cap → Bool
  | .endpointCap _ _ _ => true
  | _ => false
/-- l4v: Structures_A.is_ntfn_cap. -/
def isNtfnCap : Cap → Bool
  | .notificationCap _ _ _ => true
  | _ => false
/-- l4v: Structures_A.is_sched_context_cap. -/
def isSchedContextCap : Cap → Bool
  | .schedContextCap _ _ => true
  | _ => false

/-- l4v: Structures_A.cap_rights (`nonexhaustive`). -/
def capRights : Cap → CapRights
  | .endpointCap _ _ cr => cr
  | .notificationCap _ _ cr => cr
  | .replyCap _ cr => cr
  | .archObjectCap acap => acap.acapRights
  | _ => undefined

/-- l4v: Structures_A.cap_rights_update. -/
def capRightsUpdate (cr' : CapRights) (cap : Cap) : Cap :=
  match cap with
  | .endpointCap oref badge _ => .endpointCap oref badge cr'
  | .notificationCap oref badge _ =>
      .notificationCap oref badge (cr' \ {.allowGrant, .allowGrantReply})
  | .replyCap t _ => .replyCap t (cr' \ {.allowRead, .allowGrantReply} ∪ {.allowWrite})
  | .archObjectCap acap => .archObjectCap (acapRightsUpdate cr' acap)
  | _ => cap

/-- l4v: Structures_A.badge_update. -/
def badgeUpdate (data : Badge) (cap : Cap) : Cap :=
  match cap with
  | .endpointCap oref _ cr => .endpointCap oref (data &&& mask badgeBits) cr
  | .notificationCap oref _ cr => .notificationCap oref (data &&& mask badgeBits) cr
  | _ => cap

/-- l4v: Structures_A.mask_cap. -/
def maskCap (rights : CapRights) (cap : Cap) : Cap := capRightsUpdate (capRights cap ∩ rights) cap

/-! ## Message info -/

/-- l4v: Structures_A.message_info (`MI mi_length mi_extra_caps
mi_caps_unwrapped mi_label`). -/
structure MessageInfo where
  mk ::
  miLength : LengthType
  miExtraCaps : LengthType
  miCapsUnwrapped : Data
  miLabel : MsgLabel
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.message_info_to_data. -/
def messageInfoToData : MessageInfo → Data
  | ⟨len, exc, unw, mlabel⟩ =>
    let extra := exc <<< 7
    let unwrapped := unw <<< 9
    let label := mlabel <<< 12
    label ||| extra ||| unwrapped ||| len

/-- l4v: Structures_A.data_to_message_info. -/
def dataToMessageInfo (w : Data) : MessageInfo :=
  ⟨let v := w &&& mask 7; if v > 120 then 120 else v,
   (w >>> 7) &&& mask 2,
   (w >>> 9) &&& mask 3,
   (w >>> 12) &&& mask msgLabelBits⟩

/-! ## Kernel objects -/

/-- l4v: Structures_A.endpoint. -/
inductive Endpoint where
  | idleEP
  | sendEP (q : List ObjRef)
  | recvEP (q : List ObjRef)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.ep_queue (selector; `ep_queue IdleEP = []`). -/
def Endpoint.epQueue : Endpoint → List ObjRef
  | .idleEP => []
  | .sendEP q => q
  | .recvEP q => q

/-- l4v: Structures_A.ntfn. -/
inductive Ntfn where
  | idleNtfn
  | waitingNtfn (q : List ObjRef)
  | activeNtfn (badge : Badge)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.ntfn_queue (selector; `[]` for idle and active). -/
def Ntfn.ntfnQueue : Ntfn → List ObjRef
  | .idleNtfn => []
  | .waitingNtfn q => q
  | .activeNtfn _ => []

/-- l4v: Structures_A.ntfn_badge (selector). -/
def Ntfn.ntfnBadge : Ntfn → Badge
  | .activeNtfn b => b
  | _ => undefined

/-- l4v: Structures_A.notification. -/
structure Notification where
  ntfnObj : Ntfn
  ntfnBoundTcb : Option ObjRef
  ntfnSc : Option ObjRef
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.default_ep. -/
def defaultEp : Endpoint := .idleEP

/-- l4v: Structures_A.default_ntfn. -/
def defaultNtfn : Ntfn := .idleNtfn

/-- l4v: Structures_A.default_notification. -/
def defaultNotification : Notification :=
  { ntfnObj := defaultNtfn, ntfnBoundTcb := none, ntfnSc := none }

/-- l4v: Structures_A.sender_payload. -/
structure SenderPayload where
  senderBadge : Badge
  senderCanGrant : Bool
  senderCanGrantReply : Bool
  senderIsCall : Bool
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.receiver_payload. -/
structure ReceiverPayload where
  receiverCanGrant : Bool
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.thread_state. -/
inductive ThreadState where
  | running
  | runningVM
  | inactive
  | restart
  | blockedOnReceive (ep : ObjRef) (replyOpt : Option ObjRef) (data : ReceiverPayload)
  | blockedOnSend (ep : ObjRef) (data : SenderPayload)
  | blockedOnReply (reply : ObjRef)
  | blockedOnNotification (ntfn : ObjRef)
  | idleThreadState
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.reply_object. -/
def replyObject : ThreadState → Option ObjRef
  | .blockedOnReceive _ replyOpt _ => replyOpt
  | .blockedOnReply reply => some reply
  | _ => none

/-- l4v: Structures_A.is_blocked_on_receive. -/
def isBlockedOnReceive (st : ThreadState) : Prop :=
  ∃ ep replyOpt receiverData, st = .blockedOnReceive ep replyOpt receiverData

/-- l4v: Structures_A.is_blocked_on_send. -/
def isBlockedOnSend (st : ThreadState) : Prop := ∃ ep senderData, st = .blockedOnSend ep senderData

/-- l4v: Structures_A.is_blocked_on_reply. -/
def isBlockedOnReply (st : ThreadState) : Prop := ∃ reply, st = .blockedOnReply reply

/-- l4v: Structures_A.is_blocked_on_ntfn. -/
def isBlockedOnNtfn (st : ThreadState) : Prop := ∃ ntfn, st = .blockedOnNotification ntfn

/-- l4v: Structures_A.priority. -/
abbrev Priority := Word8

/-- l4v: Structures_A.domain_len (`value_type domain_len = domainBits`). -/
abbrev domainLen : Nat := domainBits
/-- l4v: Structures_A.domain. -/
abbrev Domain := BitVec domainLen

/-- l4v: Structures_A.tcb_flags. -/
abbrev TcbFlags := Set TcbFlag

/-- l4v: Structures_A.word_to_tcb_flags. Only flags in `tcbFlagMask` are
converted. -/
def wordToTcbFlags (w : Word) : TcbFlags := {flag | w &&& tcbFlagToWord flag &&& tcbFlagMask ≠ 0}

/-- l4v: Structures_A.tcb_flags_to_word. -/
def tcbFlagsToWord (flags : TcbFlags) : Word :=
  The fun w => wordToTcbFlags w = flags ∧ w &&& ~~~tcbFlagMask = 0

/-- l4v: Structures_A.tcb. -/
structure Tcb where
  tcbCtable : Cap
  tcbVtable : Cap
  tcbIpcframe : Cap
  tcbFaultHandler : Cap
  tcbTimeoutHandler : Cap
  tcbEpt : Cap
  tcbState : ThreadState
  tcbIpcBuffer : VSpaceRef
  tcbFault : Option Fault
  tcbBoundNotification : Option ObjRef
  tcbMcpriority : Priority
  tcbSchedContext : Option ObjRef
  tcbYieldTo : Option ObjRef
  tcbPriority : Priority
  tcbDomain : Domain
  tcbFlags : TcbFlags
  /-- must have a field for the user context -/
  tcbArch : ArchTcb
deriving Inhabited

/-- l4v: Structures_A.runnable: whether a thread in this state may be
scheduled. -/
def runnable : ThreadState → Bool
  | .running => true
  | .runningVM => true
  | .inactive => false
  | .restart => true
  | .blockedOnReceive _ _ _ => false
  | .blockedOnSend _ _ => false
  | .blockedOnNotification _ => false
  | .idleThreadState => false
  | .blockedOnReply _ => false

/-- l4v: Structures_A.ipc_queued_thread_state: whether a thread is in a
notification or endpoint queue. -/
def ipcQueuedThreadState : ThreadState → Bool
  | .running => false
  | .runningVM => false
  | .inactive => false
  | .restart => false
  | .blockedOnReceive _ _ _ => true
  | .blockedOnSend _ _ => true
  | .blockedOnNotification _ => true
  | .idleThreadState => false
  | .blockedOnReply _ => true

/-- l4v: Structures_A.default_domain (`minBound`). -/
def defaultDomain : Domain := 0

/-- l4v: Structures_A.default_priority (`minBound`). -/
def defaultPriority : Priority := 0

/-- l4v: Structures_A.default_tcb. -/
def defaultTcb (d : Domain) : Tcb :=
  { tcbCtable := .nullCap,
    tcbVtable := .nullCap,
    tcbIpcframe := .nullCap,
    tcbFaultHandler := .nullCap,
    tcbTimeoutHandler := .nullCap,
    tcbEpt := .nullCap,
    tcbState := .inactive,
    tcbIpcBuffer := 0,
    tcbFault := none,
    tcbBoundNotification := none,
    tcbMcpriority := 0,
    tcbSchedContext := none,
    tcbYieldTo := none,
    tcbPriority := defaultPriority,
    tcbDomain := d,
    tcbFlags := ∅,
    tcbArch := defaultArchTcb }

/-- l4v: Structures_A.refill. -/
structure Refill where
  rTime : Time
  rAmount : Time
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.sched_context. -/
structure SchedContext where
  scPeriod : Ticks
  scBudget : Ticks
  scConsumed : Ticks
  scTcb : Option ObjRef
  scNtfn : Option ObjRef
  scRefills : List Refill
  scRefillMax : Nat
  scBadge : Badge
  scYieldFrom : Option ObjRef
  scReplies : List ObjRef
  scSporadic : Bool
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.MIN_REFILLS. -/
def MIN_REFILLS : Nat := 2

/-- l4v: Structures_A.MIN_BUDGET_US. -/
def MIN_BUDGET_US : Ticks := 2 * kernelWCETUs
/-- l4v: Structures_A.MIN_BUDGET. -/
def MIN_BUDGET : Ticks := 2 * kernelWCETTicks

/-- l4v: Structures_A.min_sched_context_bits. -/
def minSchedContextBits : Nat := 7

/-- l4v: Structures_A.sizeof_sched_context_t: size of the C
`sched_context` struct without refills, `10 * sizeof(word_t) +
2 * sizeof(ticks_t)`. -/
def sizeofSchedContextT : Nat := (10 * wordSize) + (2 * 8)

/-- l4v: Structures_A.refill_size_bytes (`2 * sizeof(ticks_t)`). -/
def refillSizeBytes : Nat := 16

/-- l4v: Structures_A.max_num_refills (C `refill_absolute_max`). -/
def maxNumRefills (sz : Nat) : Nat := ((2 ^ sz) - sizeofSchedContextT) / refillSizeBytes

/-- l4v: Structures_A.sc_sporadic_flag. -/
def scSporadicFlag : Nat := 0

/-- l4v: Structures_A.default_sched_context. -/
def defaultSchedContext : SchedContext :=
  { scPeriod := 0,
    scBudget := 0,
    scConsumed := 0,
    scTcb := none,
    scNtfn := none,
    scRefills := [],
    scRefillMax := 0,
    scBadge := 0,
    scYieldFrom := none,
    scReplies := [],
    scSporadic := false }

/-- l4v: Structures_A.reply. -/
structure Reply where
  replyTcb : Option ObjRef
  replySc : Option ObjRef
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.default_reply. -/
def defaultReply : Reply := { replyTcb := none, replySc := none }

/-- l4v: Structures_A.kernel_object. -/
inductive KernelObject where
  /-- size in bits, and contents -/
  | cnode (sz : Nat) (cs : CnodeContents)
  | tcb (t : Tcb)
  | endpoint (ep : Endpoint)
  | notification (ntfn : Notification)
  | schedContext (sc : SchedContext) (n : Nat)
  | reply (r : Reply)
  | archObj (theArchObj : ArchKernelObj)
deriving Inhabited

/-- l4v: Structures_A.the_arch_obj (selector). -/
def KernelObject.theArchObj : KernelObject → ArchKernelObj
  | .archObj a => a
  | _ => undefined

/-- l4v: Structures_A.aobj_of. -/
def aobjOf (ko : KernelObject) : Option ArchKernelObj :=
  match ko with
  | .archObj aobj => some aobj
  | _ => none

/-- l4v: Structures_A.well_formed_cnode_n: the slots are exactly the bit
lists of length `n`. -/
def wellFormedCnodeN (n : Nat) (cs : CnodeContents) : Prop := dom cs = {x | x.length = n}

/-- l4v: Structures_A.valid_sched_context_size. -/
def validSchedContextSize (n : Nat) : Prop := minSchedContextBits + n ≤ untypedMaxBits

/-- l4v: Structures_A.obj_bits. -/
def objBits : KernelObject → Nat
  | .cnode sz _ => cteLevelBits + sz
  | .tcb _ => tcbBits
  | .endpoint _ => endpointBits
  | .notification _ => ntfnBits
  | .schedContext _ n => minSchedContextBits + n
  | .reply _ => replyBits
  | .archObj ao => archKobjSize ao

/-- l4v: Structures_A.obj_size (`nonexhaustive`). -/
def objSize : Cap → Word
  | .nullCap => 0
  | .untypedCap _ _ bits _ => 1 <<< bits
  | .endpointCap _ _ _ => 1 <<< objBits (.endpoint undefined)
  | .notificationCap _ _ _ => 1 <<< objBits (.notification undefined)
  | .cnodeCap _ bits _ => 1 <<< (cteLevelBits + bits)
  | .threadCap _ => 1 <<< objBits (.tcb undefined)
  | .schedContextCap _ bits => 1 <<< (minSchedContextBits + bits)
  | .replyCap _ _ => 1 <<< objBits (.reply undefined)
  | .zombie _ zb _ => match zb with
      | none => 1 <<< objBits (.tcb undefined)
      | some n => 1 <<< (cteLevelBits + n)
  | .archObjectCap a => 1 <<< archObjSize a
  | _ => undefined

/-- l4v: Structures_A.a_type (the datatype). -/
inductive AType where
  | aTCB
  | aEndpoint
  | aNTFN
  | aSchedContext (n : Nat)
  | aReply
  | aCapTable (n : Nat)
  /-- number of bytes of garbage -/
  | aGarbage (n : Nat)
  | aArch (t : AAType)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.a_type (the function). -/
def aType (ob : KernelObject) : AType :=
  match ob with
  | .cnode sz cspace =>
      if wellFormedCnodeN sz cspace then .aCapTable sz else .aGarbage (cteLevelBits + sz)
  | .tcb _ => .aTCB
  | .endpoint _ => .aEndpoint
  | .schedContext _ n =>
      if validSchedContextSize n then .aSchedContext n else .aGarbage (minSchedContextBits + n)
  | .reply _ => .aReply
  | .notification _ => .aNTFN
  | .archObj ao => .aArch (aaType ao)

/-! ## Kernel state -/

/-- l4v: Structures_A.kheap: the kernel heap, a partial map to kernel
objects. -/
abbrev KHeap := ObjRef → Option KernelObject

/-- l4v: Structures_A.cdt: the capability derivation tree, a partial map from
slots to their parent slots. -/
abbrev Cdt := CslotPtr → Option CslotPtr

/-- l4v: Structures_A.irq_state. -/
inductive IrqState where
  | irqInactive
  | irqSignal
  | irqTimer
  | irqReserved
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.scheduler_action. -/
inductive SchedulerAction where
  | resumeCurThread
  | switchThread (schActTarget : ObjRef)
  | chooseNewThread
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.sch_act_target (selector). -/
def SchedulerAction.schActTarget : SchedulerAction → ObjRef
  | .switchThread t => t
  | _ => undefined

/-- l4v: Structures_A.ready_queue. -/
abbrev ReadyQueue := List ObjRef
/-- l4v: Structures_A.release_queue. -/
abbrev ReleaseQueue := List ObjRef

/-- l4v: Structures_A.domain_duration_len (`value_type`, `64 - domainBits`):
the C kernel uses 64 bits in all for a domain schedule entry. -/
abbrev domainDurationLen : Nat := 64 - domainBits
/-- l4v: Structures_A.domain_duration. -/
abbrev DomainDuration := BitVec domainDurationLen

/-- l4v: Structures_A.max_domain_duration. -/
def maxDomainDuration : Ticks := mask domainDurationLen

/-- l4v: Structures_A.abstract_state. -/
structure AbstractState where
  kheap : KHeap
  cdt : Cdt
  isOriginalCap : CslotPtr → Bool
  curThread : ObjRef
  idleThread : ObjRef
  /-- amount of time since kernel time was last updated -/
  consumedTime : Time
  /-- current time at kernel entry -/
  curTime : Time
  /-- current scheduling context -/
  curSc : ObjRef
  /-- whether the timer must be reprogrammed on exit -/
  reprogramTimer : Bool
  schedulerAction : SchedulerAction
  domainList : List (Domain × DomainDuration)
  domainIndex : Nat
  domainStartIndex : Nat
  curDomain : Domain
  domainTime : Ticks
  readyQueues : Domain → Priority → ReadyQueue
  releaseQueue : ReleaseQueue
  machineState : MachineState
  interruptIrqNode : Irq → ObjRef
  interruptStates : Irq → IrqState
  archState : ArchState

instance : Nonempty AbstractState :=
  ⟨⟨fun _ => none, fun _ => none, fun _ => false, 0, 0, 0, 0, 0, false, .resumeCurThread, [], 0, 0,
    0, 0, fun _ _ => [], [], undefined, fun _ => 0, fun _ => .irqInactive, default⟩⟩

/-- l4v: Structures_A.state (`'a state = abstract_state + exst :: 'a`): the
abstract state extended with the state `exst` of a particular
instantiation of the specification (see `Fl4Spec.Deterministic`). -/
structure State (Z : Type) extends AbstractState where
  exst : Z

instance {Z : Type} [Nonempty Z] : Nonempty (State Z) :=
  ⟨{ toAbstractState := undefined, exst := undefined }⟩

/-! ## Helper functions -/

/-- l4v: Structures_A.do_machine_op: lift a machine operation to the kernel
state. -/
def doMachineOp {Z α : Type} (mop : NonDet MachineState α) : NonDet (State Z) α := do
  let ms ← NonDet.gets fun s : State Z => s.machineState
  let (r, ms') ← NonDet.selectF (mop ms)
  NonDet.modify fun state => { state with machineState := ms' }
  return r

/-- l4v: Structures_A.tcb_cnode_index: the cnode indices of the capability
slots of a TCB. -/
def tcbCnodeIndex (n : Nat) : CnodeIndex := toBl (BitVec.ofNat 3 n)

/-- l4v: Structures_A.zombie_cte_bits. -/
def zombieCteBits (N : Option Nat) : Nat :=
  match N with
  | some n => n
  | none => 3

/-- l4v: Structures_A.first_cslot_of (`nonexhaustive`). -/
def firstCslotOf : Cap → CslotPtr
  | .threadCap oref => (oref, tcbCnodeIndex 0)
  | .cnodeCap oref bits _ => (oref, List.replicate bits false)
  | .zombie oref bits _ => (oref, List.replicate (zombieCteBits bits) false)
  | _ => undefined

/-- l4v: Structures_A.obj_refs: the objects a capability references. -/
def objRefs : Cap → Set ObjRef
  | .nullCap => ∅
  | .replyCap r _ => {r}
  | .irqControlCap => ∅
  | .irqHandlerCap _ => ∅
  | .untypedCap _ _ _ _ => ∅
  | .cnodeCap r _ _ => {r}
  | .endpointCap r _ _ => {r}
  | .notificationCap r _ _ => {r}
  | .threadCap r => {r}
  | .domainCap => ∅
  | .schedContextCap r _ => {r}
  | .schedControlCap => ∅
  | .zombie ptr _ _ => {ptr}
  | .archObjectCap x => {r | aobjRef x = some r}

/-- l4v: Structures_A.obj_ref_of (`nonexhaustive`). -/
def objRefOf : Cap → ObjRef
  | .untypedCap _ r _ _ => r
  | .replyCap r _ => r
  | .cnodeCap r _ _ => r
  | .endpointCap r _ _ => r
  | .notificationCap r _ _ => r
  | .threadCap r => r
  | .schedContextCap r _ => r
  | .zombie ptr _ _ => ptr
  | .archObjectCap x => the (aobjRef x)
  | _ => undefined

/-- l4v: Structures_A.cap_bits_untyped (`nonexhaustive`). -/
def capBitsUntyped : Cap → Nat
  | .untypedCap _ _ s _ => s
  | _ => undefined

/-- l4v: Structures_A.cap_badge. -/
def capBadge (cap : Cap) : Option Badge :=
  match cap with
  | .endpointCap _ badge _ => some badge
  | .notificationCap _ badge _ => some badge
  | .archObjectCap acap => archCapBadge acap
  | _ => none

/-- l4v: Structures_A.tcb_cnode_map. -/
def tcbCnodeMap (tcb : Tcb) : CnodeIndex → Option Cap :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => none)
    (tcbCnodeIndex 0) (some tcb.tcbCtable))
    (tcbCnodeIndex 1) (some tcb.tcbVtable))
    (tcbCnodeIndex 2) (some tcb.tcbIpcframe))
    (tcbCnodeIndex 3) (some tcb.tcbFaultHandler))
    (tcbCnodeIndex 4) (some tcb.tcbTimeoutHandler))
    (tcbCnodeIndex 5) (some tcb.tcbEpt)

/-- l4v: Structures_A.cap_of. -/
def capOf (kobj : KernelObject) : CnodeIndex → Option Cap :=
  match kobj with
  | .cnode _ cs => cs
  | .tcb tcb => tcbCnodeMap tcb
  | _ => fun _ => none

/-- l4v: Structures_A.caps_of: the caps held by a kernel object. -/
def capsOf (kobj : KernelObject) : Set Cap := ran (capOf kobj)

/-! ## Record field updates

Isabelle generates an update function `f_update :: ('a ⇒ 'a) ⇒ 'r ⇒ 'r` for
every record field. The spec passes the ones below as arguments
(`set_tcb_obj_ref tcb_sched_context_update`, `set_sc_obj_ref
sc_refills_update`, ...), so they are explicit functions here. -/

/-- Isabelle record update `tcb_sched_context_update`. -/
def tcbSchedContextUpdate (f : Option ObjRef → Option ObjRef) (t : Tcb) : Tcb :=
  { t with tcbSchedContext := f t.tcbSchedContext }
/-- Isabelle record update `tcb_yield_to_update`. -/
def tcbYieldToUpdate (f : Option ObjRef → Option ObjRef) (t : Tcb) : Tcb :=
  { t with tcbYieldTo := f t.tcbYieldTo }
/-- Isabelle record update `tcb_bound_notification_update`. -/
def tcbBoundNotificationUpdate (f : Option ObjRef → Option ObjRef) (t : Tcb) : Tcb :=
  { t with tcbBoundNotification := f t.tcbBoundNotification }

/-- Isabelle record update `sc_period_update`. -/
def scPeriodUpdate (f : Ticks → Ticks) (sc : SchedContext) : SchedContext :=
  { sc with scPeriod := f sc.scPeriod }
/-- Isabelle record update `sc_budget_update`. -/
def scBudgetUpdate (f : Ticks → Ticks) (sc : SchedContext) : SchedContext :=
  { sc with scBudget := f sc.scBudget }
/-- Isabelle record update `sc_consumed_update`. -/
def scConsumedUpdate (f : Ticks → Ticks) (sc : SchedContext) : SchedContext :=
  { sc with scConsumed := f sc.scConsumed }
/-- Isabelle record update `sc_tcb_update`. -/
def scTcbUpdate (f : Option ObjRef → Option ObjRef) (sc : SchedContext) : SchedContext :=
  { sc with scTcb := f sc.scTcb }
/-- Isabelle record update `sc_ntfn_update`. -/
def scNtfnUpdate (f : Option ObjRef → Option ObjRef) (sc : SchedContext) : SchedContext :=
  { sc with scNtfn := f sc.scNtfn }
/-- Isabelle record update `sc_refills_update`. -/
def scRefillsUpdate (f : List Refill → List Refill) (sc : SchedContext) : SchedContext :=
  { sc with scRefills := f sc.scRefills }
/-- Isabelle record update `sc_refill_max_update`. -/
def scRefillMaxUpdate (f : Nat → Nat) (sc : SchedContext) : SchedContext :=
  { sc with scRefillMax := f sc.scRefillMax }
/-- Isabelle record update `sc_badge_update`. -/
def scBadgeUpdate (f : Badge → Badge) (sc : SchedContext) : SchedContext :=
  { sc with scBadge := f sc.scBadge }
/-- Isabelle record update `sc_yield_from_update`. -/
def scYieldFromUpdate (f : Option ObjRef → Option ObjRef) (sc : SchedContext) : SchedContext :=
  { sc with scYieldFrom := f sc.scYieldFrom }
/-- Isabelle record update `sc_replies_update`. -/
def scRepliesUpdate (f : List ObjRef → List ObjRef) (sc : SchedContext) : SchedContext :=
  { sc with scReplies := f sc.scReplies }
/-- Isabelle record update `sc_sporadic_update`. -/
def scSporadicUpdate (f : Bool → Bool) (sc : SchedContext) : SchedContext :=
  { sc with scSporadic := f sc.scSporadic }

/-- Isabelle record update `ntfn_obj_update`. -/
def ntfnObjUpdate (f : Ntfn → Ntfn) (n : Notification) : Notification :=
  { n with ntfnObj := f n.ntfnObj }
/-- Isabelle record update `ntfn_bound_tcb_update`. -/
def ntfnBoundTcbUpdate (f : Option ObjRef → Option ObjRef) (n : Notification) : Notification :=
  { n with ntfnBoundTcb := f n.ntfnBoundTcb }
/-- Isabelle record update `ntfn_sc_update`. -/
def ntfnScUpdate (f : Option ObjRef → Option ObjRef) (n : Notification) : Notification :=
  { n with ntfnSc := f n.ntfnSc }

/-- Isabelle record update `reply_tcb_update`. -/
def replyTcbUpdate (f : Option ObjRef → Option ObjRef) (r : Reply) : Reply :=
  { r with replyTcb := f r.replyTcb }
/-- Isabelle record update `reply_sc_update`. -/
def replyScUpdate (f : Option ObjRef → Option ObjRef) (r : Reply) : Reply :=
  { r with replySc := f r.replySc }

/-! ## Cap transfers -/

/-- l4v: Structures_A.captransfer. -/
structure CapTransfer where
  ctReceiveRoot : CapRef
  ctReceiveIndex : CapRef
  ctReceiveDepth : Data
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structures_A.cap_transfer_data_size. -/
def capTransferDataSize : Nat := 3

/-- l4v: Structures_A.msg_max_length. -/
def msgMaxLength : Nat := 120

/-- l4v: Structures_A.msg_max_extra_caps. -/
def msgMaxExtraCaps : Nat := 3

/-- l4v: Structures_A.max_ipc_length. -/
def maxIpcLength : Nat := capTransferDataSize + msgMaxLength + msgMaxExtraCaps + 2

/-- l4v: Structures_A.msg_align_bits (`word_size_bits + (LEAST n.
max_ipc_length ≤ 2 ^ n)`). -/
def msgAlignBits : Nat :=
  wordSizeBits + Nat.find (⟨7, by decide⟩ : ∃ n, maxIpcLength ≤ 2 ^ n)

end

end Fl4Spec
