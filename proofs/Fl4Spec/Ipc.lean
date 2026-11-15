/-
Inter-process communication: message and cap transfer, fault messages,
endpoint and notification send and receive, replies, and the budget
charging that l4v moved here from Schedule_A (MCS).

Ports `spec/abstract/Ipc_A` (imports Tcb_A and ArchFault_A, both in
`Fl4Spec.Tcb`).
-/
import Fl4Spec.Tcb

namespace Fl4Spec

open Classical

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-! ## Getting and setting the message info register -/

/-- l4v: Ipc_A.get_message_info. -/
def getMessageInfo (thread : ObjRef) : SMonad Z MessageInfo := do
  let x ← asUser thread <| getRegister msg_info_register
  return dataToMessageInfo x

end

/-! ## IPC capability transfers -/

/-- l4v: Ipc_A.remove_rights. -/
def removeRights (rights : CapRights) (cap : Cap) : Cap :=
  capRightsUpdate (capRights cap \ rights) cap

/-- l4v: Ipc_A.buffer_cptr_index: where the cptrs of the extra caps start in
the IPC buffer. -/
def bufferCptrIndex : Nat := msgMaxLength + 2

section
variable {Z : Type} [StateExt Z]

/-- l4v: Ipc_A.get_extra_cptrs: the cptrs of the extra caps a sender names
in its IPC buffer. -/
def getExtraCptrs : Option ObjRef → MessageInfo → SMonad Z (List CapRef)
  | some buf, mi =>
    NonDet.liftM (List.map dataToCptr) <| NonDet.mapM (loadWordOffs buf)
      (List.range' bufferCptrIndex (bufferCptrIndex + unat mi.miExtraCaps - bufferCptrIndex))
  | none, _mi => return []

/-- l4v: Ipc_A.get_extra_cptr. -/
def getExtraCptr (buffer : ObjRef) (n : Nat) : SMonad Z CapRef :=
  NonDet.liftM dataToCptr (loadWordOffs buffer (n + bufferCptrIndex))

/-- l4v: Ipc_A.lookup_extra_caps: look up the extra caps of a message in the
sender's CSpace. -/
def lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) :
    FMonad Z (List (Cap × CslotPtr)) := do
  let cptrs ← NonDetE.liftE <| getExtraCptrs buffer mi
  NonDetE.mapME (fun cptr => capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr) cptrs

/-- l4v: Ipc_A.set_extra_badge. -/
def setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : SMonad Z Unit :=
  storeWordOffs buffer (bufferCptrIndex + n) badge

end

/-- l4v: Ipc_A.transfer_caps_data. -/
abbrev TransferCapsData := List (Cap × CslotPtr) × List CslotPtr

section
variable {Z : Type} [StateExt Z]

/-- l4v: Ipc_A.transfer_caps_loop: caps to the endpoint the message goes
through are unwrapped into badges, the others are copied into the receive
slots. `n` is after the colon because the recursion changes it. -/
def transferCapsLoop (ep : Option ObjRef) (rcvBuffer : ObjRef) :
    Nat → List (Cap × CslotPtr) → List CslotPtr → MessageInfo → SMonad Z MessageInfo
  | n, [], _slots, mi =>
    return ⟨mi.miLength, BitVec.ofNat 64 n, mi.miCapsUnwrapped, mi.miLabel⟩
  | n, (cap, slot) :: morecaps, slots, mi =>
    constOnFailure (⟨mi.miLength, BitVec.ofNat 64 n, mi.miCapsUnwrapped, mi.miLabel⟩ : MessageInfo)
      (show SEMonad Z MessageInfo from do
        let transferRest ← NonDetE.returnOk (transferCapsLoop ep rcvBuffer (n + 1) morecaps)
        if isEpCap cap ∧ ep = some (objRefOf cap)
        then do
          NonDetE.liftE <| setExtraBadge rcvBuffer (capEpBadge cap) n
          NonDetE.liftE <| transferRest slots
            ⟨mi.miLength, mi.miExtraCaps, mi.miCapsUnwrapped ||| ((1 : Data) <<< n), mi.miLabel⟩
        else if slots ≠ []
        then do
          let cap' ← deriveCap slot cap
          NonDetE.whenE (cap' = .nullCap) <| NonDetE.throwError undefined
          NonDetE.liftE <| capInsert cap' slot (the slots.head?)
          NonDetE.liftE <| transferRest slots.tail mi
        else NonDetE.returnOk ⟨mi.miLength, BitVec.ofNat 64 n, mi.miCapsUnwrapped, mi.miLabel⟩)

/-- l4v: Ipc_A.transfer_caps. -/
def transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef)
    (receiver : ObjRef) (recvBuffer : Option ObjRef) : SMonad Z MessageInfo := do
  let destSlots ← getReceiveSlots receiver recvBuffer
  let mi' ← pure (⟨info.miLength, 0, 0, info.miLabel⟩ : MessageInfo)
  match recvBuffer with
  | none => return mi'
  | some receiveBuffer => transferCapsLoop endpoint receiveBuffer 0 caps destSlots mi'

/-! ## Fault handling -/

/-- l4v: Ipc_A.make_fault_msg: the label and message of a fault. -/
def makeFaultMsg : Fault → ObjRef → SMonad Z (Data × List Data)
  | .capFault cptr rp lf, thread => do
    let pc ← asUser thread getRestartPC
    return (1, pc :: cptr :: (if rp then 1 else 0) :: msgFromLookupFailure lf)
  | .unknownSyscallException n, thread => do
    let msg ← asUser thread <| NonDet.mapM getRegister syscallMessage
    return (2, msg ++ [n])
  | .userException exception code, thread => do
    let msg ← asUser thread <| NonDet.mapM getRegister exceptionMessage
    return (3, msg ++ [exception, code])
  | .timeout badge, thread => do
    let tcb ← NonDet.getsThe (getTcb thread)
    match tcb.tcbSchedContext with
    | none => return (5, [badge])
    | some sc => do
      let consumed ← schedContextUpdateConsumed sc
      return (5, badge :: wordsFromTime consumed)
  | .archFault af, thread => makeArchFaultMsg af thread

/-- l4v: Ipc_A.handle_fault_reply: act on the reply to a fault message;
whether the thread should be restarted. -/
def handleFaultReply : Fault → ObjRef → Data → List Data → SMonad Z Bool
  | .capFault _cptr _rp _lf, _thread, _x, _y => return true
  | .unknownSyscallException _n, thread, label, msg => do
    let t ← archGetSanitiseRegisterInfo thread
    asUser thread <| NonDet.zipWithMx
      (fun r v => setRegister r <| sanitiseRegister t r v)
      syscallMessage msg
    return decide (label = 0)
  | .userException _exception _code, thread, label, msg => do
    let t ← archGetSanitiseRegisterInfo thread
    asUser thread <| NonDet.zipWithMx
      (fun r v => setRegister r <| sanitiseRegister t r v)
      exceptionMessage msg
    return decide (label = 0)
  | .timeout _badge, thread, label, msg => do
    let t ← archGetSanitiseRegisterInfo thread
    asUser thread <| NonDet.zipWithMx
      (fun r v => setRegister r <| sanitiseRegister t r v)
      timeoutMessage msg
    return decide (label = 0)
  | .archFault af, thread, label, msg => handleArchFaultReply af thread label msg

/-- l4v: Ipc_A.do_fault_transfer: send a faulting thread's fault message to
its supervisor. -/
def doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) :
    SMonad Z Unit := do
  let fault ← threadGet Tcb.tcbFault sender
  let f ← match fault with
    | some f => pure f
    | none => NonDet.fail
  let (label, msg) ← makeFaultMsg f sender
  let sent ← setMrs receiver buf msg
  setMessageInfo receiver ⟨sent, 0, 0, label⟩
  asUser receiver <| setRegister badge_register badge

/-! ## Synchronous message transfers -/

/-- l4v: Ipc_A.do_normal_transfer: transfer a non-fault message. -/
def doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data)
    (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : SMonad Z Unit := do
  let mi ← getMessageInfo sender
  let caps ← if grant then NonDetE.catch (lookupExtraCaps sender sbuf mi) (fun _ => pure [])
    else pure []
  let mrsTransferred ← copyMrs sender sbuf receiver rbuf mi.miLength
  let mi' ← transferCaps mi caps endpoint receiver rbuf
  setMessageInfo receiver ⟨mrsTransferred, mi'.miExtraCaps, mi'.miCapsUnwrapped, mi.miLabel⟩
  asUser receiver <| setRegister badge_register badge

/-- l4v: Ipc_A.do_ipc_transfer: transfer a message, fault or not. -/
def doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool)
    (receiver : ObjRef) : SMonad Z Unit := do
  let recvBuffer ← lookupIpcBuffer true receiver
  let fault ← threadGet Tcb.tcbFault sender
  match fault with
  | none => do
    let sendBuffer ← lookupIpcBuffer false sender
    doNormalTransfer sender sendBuffer ep badge grant receiver recvBuffer
  | some _f => doFaultTransfer badge sender receiver recvBuffer

/-- l4v: Ipc_A.send_ipc_blocked. -/
def sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) :
    SMonad Z Unit := do
  setThreadState thread (.blockedOnSend epptr
    { senderBadge := badge,
      senderCanGrant := canGrant,
      senderCanGrantReply := canGrantReply,
      senderIsCall := call })
  tcbEpAppend thread epptr false

/-- l4v: Ipc_A.send_ipc: send on an endpoint; transfer to a waiting receiver,
or block in the send queue if `block`. -/
def sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool)
    (thread epptr : ObjRef) : SMonad Z Unit := do
  let ep ← getEndpoint epptr
  match ep, block with
  | .idleEP, true => sendIpcBlocked thread epptr badge canGrant canGrantReply call
  | .sendEP _queue, true => sendIpcBlocked thread epptr badge canGrant canGrantReply call
  | .idleEP, false => return ()
  | .sendEP _queue, false => return ()
  | .recvEP (dest :: _queue), _ => do
    tcbEpDequeue dest epptr
    let recvState ← getThreadState dest
    let reply ← match recvState with
      | .blockedOnReceive _ reply _data => pure reply
      | _ => NonDet.fail
    doIpcTransfer thread (some epptr) badge canGrant dest
    NonDet.maybeM (replyUnlinkTcb dest) reply
    let scOpt ← getTcbObjRef Tcb.tcbSchedContext dest
    let fault ← threadGet Tcb.tcbFault thread
    if call ∨ fault ≠ none then
      if (canGrant ∨ canGrantReply) ∧ reply ≠ none then
        replyPush thread dest (the reply) canDonate
      else
        setThreadState thread .inactive
    else NonDet.when (canDonate ∧ scOpt = none) <| do
      let threadSc ← getTcbObjRef Tcb.tcbSchedContext thread
      schedContextDonate (the threadSc) dest
    setThreadState dest .running
    let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
    ifSporadicCurScTestRefillUnblockCheck destSc
    possibleSwitchTo dest
  | .recvEP [], _ => NonDet.fail

end

/-- l4v: Ipc_A.isActive. -/
def isActive (ntfn : Notification) : Bool :=
  match ntfn.ntfnObj with
  | .activeNtfn _ => true
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- l4v: Ipc_A.complete_signal: deliver a pending signal on a receive on a
normal endpoint. -/
def completeSignal (ntfnptr tptr : ObjRef) : SMonad Z Unit := do
  let ntfn ← getNotification ntfnptr
  match ntfn.ntfnObj with
  | .activeNtfn badge => do
    asUser tptr <| setRegister badge_register badge
    setNotification ntfnptr <| ntfnObjUpdate (fun _ => .idleNtfn) ntfn
    maybeDonateSc tptr ntfnptr
    let scOpt ← getTcbObjRef Tcb.tcbSchedContext tptr
    NonDet.maybeM (fun scp => do
        let sc ← getSchedContext scp
        NonDet.when sc.scSporadic <| do
          let ntfnScp ← getNtfnObjRef Notification.ntfnSc ntfnptr
          let curScPtr ← NonDet.gets fun s : State Z => s.curSc
          NonDet.when (scOpt = ntfnScp ∧ scp ≠ curScPtr) <| refillUnblockCheck scp)
      scOpt
  | _ => NonDet.fail

/-- l4v: Ipc_A.do_nbrecv_failed_transfer. -/
def doNbrecvFailedTransfer (thread : ObjRef) : SMonad Z Unit := do
  asUser thread <| setRegister badge_register 0
  return ()

end

/-- l4v: Ipc_A.is_timeout_fault. -/
def isTimeoutFault (f : Fault) : Bool :=
  match f with
  | .timeout _ => true
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- l4v: Ipc_A.receive_ipc_blocked. -/
def receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) :
    SMonad Z Unit :=
  if isBlocking
  then do
    setThreadState thread (.blockedOnReceive epptr reply { receiverCanGrant := false })
    NonDet.maybeM (fun r => setReplyObjRef replyTcbUpdate r (some thread)) reply
    tcbEpAppend thread epptr true
  else doNbrecvFailedTransfer thread

/-- l4v: Ipc_A.receive_ipc: receive on an endpoint; take a pending signal
of the bound notification, or a waiting sender's message, or block. -/
def receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    SMonad Z Unit := do
  let (epptr, _rights) ← match cap with
    | .endpointCap ref _badge rights => pure (ref, rights)
    | _ => NonDet.fail
  let reply ← match replyCap with
    | .replyCap r _ => do
      let tptr ← getReplyTcb r
      NonDet.when (tptr ≠ none ∧ the tptr ≠ thread) <| cancelIpc (the tptr)
      pure (some r)
    | .nullCap => pure none
    | _ => NonDet.fail
  let ep ← getEndpoint epptr
  let ntfnptr ← getTcbObjRef Tcb.tcbBoundNotification thread
  let ntfn ← match ntfnptr with
    | none => pure defaultNotification
    | some p => getNotification p
  if ntfnptr ≠ none ∧ isActive ntfn
  then
    completeSignal (the ntfnptr) thread
  else do
    NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) thread
    match ep with
    | .sendEP q => do
      NonDet.assert (q ≠ [])
      let sender ← pure (the q.head?)
      tcbEpDequeue sender epptr
      let senderState ← getThreadState sender
      let data ← match senderState with
        | .blockedOnSend _ref data => pure data
        | _ => NonDet.fail
      doIpcTransfer sender (some epptr)
        data.senderBadge data.senderCanGrant
        thread
      let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck scPtr
      let fault ← threadGet Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush sender thread (the reply) donate
        else setThreadState sender .inactive
      else do
        setThreadState sender .running
        possibleSwitchTo sender
        -- l4v: FIXME RT: the C code has a test here for (refill_sufficient
        -- sender's sc ∨ sender's sc is None)
    | _ => receiveIpcBlocked isBlocking thread epptr reply

/-! ## Asynchronous message transfers -/

/-- l4v: Ipc_A.update_waiting_ntfn: signal a notification with a waiting
receiver. -/
def updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) :
    SMonad Z Unit := do
  NonDet.assert (queue ≠ [])
  let dest ← pure (the queue.head?)
  tcbNtfnDequeue dest ntfnptr
  setThreadState dest .running
  asUser dest <| setRegister badge_register badge
  maybeDonateSc dest ntfnptr
  let sched ← NonDet.gets (schedulable dest)
  NonDet.when sched <| possibleSwitchTo dest
  let scopt ← getTcbObjRef Tcb.tcbSchedContext dest
  ifSporadicCurScTestRefillUnblockCheck scopt

end

/-- l4v: Ipc_A.receive_blocked. -/
def receiveBlocked (st : ThreadState) : Bool :=
  match st with
  | .blockedOnReceive _ _ _ => true
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- l4v: Ipc_A.send_signal: signal a notification; wake a waiting or bound
receiver, or combine the badge with a pending one. -/
def sendSignal (ntfnptr : ObjRef) (badge : Badge) : SMonad Z Unit := do
  let ntfn ← getNotification ntfnptr
  match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
  | .idleNtfn, some tcb => do
    let st ← getThreadState tcb
    if receiveBlocked st
    then do
      cancelIpc tcb
      setThreadState tcb .running
      asUser tcb <| setRegister badge_register badge
      maybeDonateSc tcb ntfnptr
      let sched ← NonDet.gets (schedulable tcb)
      NonDet.when sched <| possibleSwitchTo tcb
      let scopt ← getTcbObjRef Tcb.tcbSchedContext tcb
      ifSporadicCurScTestRefillUnblockCheck scopt
    else setNotification ntfnptr <| ntfnObjUpdate (fun _ => .activeNtfn badge) ntfn
  | .idleNtfn, none => setNotification ntfnptr <| ntfnObjUpdate (fun _ => .activeNtfn badge) ntfn
  | .waitingNtfn queue, _boundTcb => updateWaitingNtfn ntfnptr queue badge
  | .activeNtfn badge', _ =>
    setNotification ntfnptr <|
      ntfnObjUpdate (fun _ => .activeNtfn (combineNtfnBadges badge badge')) ntfn

/-- l4v: Ipc_A.receive_signal_blocked. -/
def receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : SMonad Z Unit :=
  if isBlocking
  then do
    setThreadState thread (.blockedOnNotification ntfnptr)
    tcbNtfnAppend thread ntfnptr
    maybeReturnSc ntfnptr thread
  else doNbrecvFailedTransfer thread

/-- l4v: Ipc_A.receive_signal: wait on a notification. -/
def receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : SMonad Z Unit := do
  let ntfnptr ← match cap with
    | .notificationCap ntfnptr _badge _rights => pure ntfnptr
    | _ => NonDet.fail
  let ntfn ← getNotification ntfnptr
  match ntfn.ntfnObj with
  | .activeNtfn badge => do
    asUser thread <| setRegister badge_register badge
    setNotification ntfnptr <| ntfnObjUpdate (fun _ => .idleNtfn) ntfn
    maybeDonateSc thread ntfnptr
    let scPtr ← getTcbObjRef Tcb.tcbSchedContext thread
    ifSporadicCurScTestRefillUnblockCheck scPtr
  | _ => receiveSignalBlocked thread ntfnptr isBlocking

/-! ## Sending fault messages -/

/-- l4v: Ipc_A.send_fault_ipc: send a fault message to a handler endpoint;
whether there was a handler. -/
def sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) :
    SMonad Z Bool :=
  match handlerCap with
  | .endpointCap _ref _badge rights => do
    threadSet (fun tcb => { tcb with tcbFault := some fault }) tptr
    sendIpc true false (capEpBadge handlerCap)
      (decide (Rights.allowGrant ∈ rights)) (decide (Rights.allowGrantReply ∈ rights)) canDonate tptr
      (capEpPtr handlerCap)
    return true
  | .nullCap => return false
  | _ => NonDet.fail

/-- l4v: Ipc_A.is_valid_timeout_handler. -/
def isValidTimeoutHandler (tptr : ObjRef) : SMonad Z Bool := do
  let timeoutHandlerSlot ← pure (getTcbTimeoutHandlerPtr tptr)
  let timeoutHandlerCap ← getCap timeoutHandlerSlot
  return isEpCap timeoutHandlerCap

/-- l4v: Ipc_A.handle_timeout: send a timeout fault to the timeout handler. -/
def handleTimeout (tptr : ObjRef) (ex : Fault) : SMonad Z Unit := do
  let valid ← isValidTimeoutHandler tptr
  NonDet.assert valid
  let timeoutHandlerSlot ← pure (getTcbTimeoutHandlerPtr tptr)
  let timeoutHandlerCap ← getCap timeoutHandlerSlot
  let _ ← sendFaultIpc tptr timeoutHandlerCap ex false
  return ()

/-- l4v: Ipc_A.handle_no_fault: a thread whose fault cannot be sent is left
inactive. -/
def handleNoFault (tptr : ObjRef) : SMonad Z Unit := setThreadState tptr .inactive

/-- l4v: Ipc_A.handle_fault: send a fault message to the thread's fault
handler if possible. -/
def handleFault (thread : ObjRef) (ex : Fault) : SMonad Z Unit := do
  let faultHandlerSlot ← pure (getTcbFaultHandlerPtr thread)
  let faultHandlerCap ← getCap faultHandlerSlot
  let threadScPtrOpt ← threadGet Tcb.tcbSchedContext thread
  let hasFh ← sendFaultIpc thread faultHandlerCap ex (decide (threadScPtrOpt ≠ none))
  NonDet.unless hasFh <| handleNoFault thread
  return ()

/-- l4v: Ipc_A.do_reply_transfer: transfer a reply message (or handle a
fault reply) to the thread waiting on the reply object. -/
def doReplyTransfer (sender reply : ObjRef) (grant : Bool) : SMonad Z Unit := do
  let recvOpt ← getReplyTcb reply
  NonDet.maybeM (fun receiver => do
      let state ← getThreadState receiver
      match state with
      | .blockedOnReply r => do
        NonDet.assert (r = reply)
        replyRemove receiver reply
        let scOpt ← getTcbObjRef Tcb.tcbSchedContext receiver
        ifSporadicCurScTestRefillUnblockCheck scOpt
        let fault ← threadGet Tcb.tcbFault receiver
        match fault with
        | none => do
          doIpcTransfer sender none 0 grant receiver
          setThreadState receiver .running
        | some f => do
          let mi ← getMessageInfo sender
          let buf ← lookupIpcBuffer false sender
          let mrs ← getMrs sender buf mi
          let restart ← handleFaultReply f receiver mi.miLabel mrs
          threadSet (fun tcb => { tcb with tcbFault := none }) receiver
          setThreadState receiver (if restart then .restart else .inactive)
        let scOpt ← getTcbObjRef Tcb.tcbSchedContext receiver
        let state ← getThreadState receiver
        NonDet.when (scOpt ≠ none ∧ runnable state) <| do
          let scPtr ← NonDet.assertOpt scOpt
          let sc ← getSchedContext scPtr
          let curtime ← NonDet.gets fun s : State Z => s.curTime
          if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
          then possibleSwitchTo receiver
          else do
            let tcb ← NonDet.getsThe (getTcb receiver)
            if isEpCap tcb.tcbTimeoutHandler ∧
               ¬(fault.elim false isTimeoutFault = true)
            then handleTimeout receiver (.timeout sc.scBadge)
            else postpone scPtr
      | _ => return ())
    recvOpt

/-! ## Budget charging (moved from Schedule_A in l4v, "due to a dependency
issue") -/

/-- l4v: Ipc_A.end_timeslice: the current thread's budget is used up; raise
a timeout fault or requeue it. -/
def endTimeslice (canTimeout : Bool) : SMonad Z Unit := do
  let scPtr ← NonDet.gets fun s : State Z => s.curSc
  let roundRobin ← isRoundRobin scPtr
  let ct ← NonDet.gets fun s : State Z => s.curThread
  let ts ← getThreadState ct
  let valid ← if ts = .runningVM then pure false else isValidTimeoutHandler ct
  if canTimeout ∧ ¬roundRobin ∧ valid
  then do
    let sc ← getSchedContext scPtr
    handleTimeout ct (.timeout sc.scBadge)
  else do
    let ready ← getScRefillReady scPtr
    let sufficient ← getScRefillSufficient scPtr 0
    if ready ∧ sufficient
    then tcbSchedAction tcbSchedAppend ct -- not_queued & ready & sufficient & runnable
    else postpone scPtr

/-- l4v: Ipc_A.refill_reset_rr. -/
def refillResetRr (cscPtr : ObjRef) : SMonad Z Unit := do
  let head ← getRefillHead cscPtr
  let tail ← getRefillTail cscPtr
  updateRefillHd cscPtr (fun hd => { hd with rAmount := head.rAmount + tail.rAmount })
  updateRefillTl cscPtr (fun r => { r with rAmount := 0 })

/-- l4v: Ipc_A.charge_budget: charge `consumed` to the current scheduling
context. -/
def chargeBudget (consumed : Ticks) (canTimeout : Bool) : SMonad Z Unit := do
  let cscPtr ← NonDet.gets fun s : State Z => s.curSc
  NonDet.when (cscPtr ≠ idleScPtr) <| do
    let robin ← isRoundRobin cscPtr
    if robin
    then refillResetRr cscPtr
    else refillBudgetCheck consumed
    updateSchedContext cscPtr (fun sc => { sc with scConsumed := sc.scConsumed + consumed })
  NonDet.modify fun s : State Z => { s with consumedTime := 0 }
  let ct ← NonDet.gets fun s : State Z => s.curThread
  let sched ← NonDet.gets (schedulable ct)
  NonDet.when sched <| do
    endTimeslice canTimeout
    rescheduleRequired
    NonDet.modify fun s : State Z => { s with reprogramTimer := true }

/-- l4v: Ipc_A.check_budget: whether the current thread can continue;
charges the consumed time if the budget is insufficient. -/
def checkBudget : SMonad Z Bool := do
  let csc ← NonDet.gets fun s : State Z => s.curSc
  let consumed ← NonDet.gets fun s : State Z => s.consumedTime
  -- l4v: FIXME RT: maybe assert refill_ready?
  let sufficient ← getScRefillSufficient csc consumed
  if sufficient
  then do
    let domExp ← NonDet.gets isCurDomainExpired
    return !domExp
  else do
    let consumed ← NonDet.gets fun s : State Z => s.consumedTime
    chargeBudget consumed true
    return false

/-- l4v: Ipc_A.check_budget_restart. -/
def checkBudgetRestart : SMonad Z Bool := do
  let result ← checkBudget
  let cur ← NonDet.gets fun s : State Z => s.curThread
  let st ← getThreadState cur
  NonDet.when (¬result ∧ runnable st) <| setThreadState cur .restart
  return result

/-- l4v: Ipc_A.invoke_sched_control_configure_flags: configure the budget,
period and flags of a scheduling context. -/
def invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : SMonad Z Unit :=
  match iv with
  | .invokeSchedControlConfigureFlags scPtr budget period mrefills badge flag => do
    let sc ← getSchedContext scPtr
    NonDet.when (sc.scTcb ≠ none) <| do
      let tcbPtr ← NonDet.assertOpt sc.scTcb
      tcbReleaseRemove tcbPtr
      tcbSchedAction tcbSchedDequeue tcbPtr
      let curSc ← NonDet.gets fun s : State Z => s.curSc
      NonDet.when (curSc = scPtr) commitTime
      -- l4v: The C code here includes an assert saying that check_budget
      -- returns True. However, we can call invoke_sched_control_configure
      -- only if the call to check_budget_restart at the beginning of
      -- handle_event returns True, so we know that check_budget would return
      -- True if called here.
    if period = budget
    then refillNew scPtr MIN_REFILLS budget 0
    else do
      let active ← getScActive scPtr
      if active ∧ sc.scTcb ≠ none
      then do
        let tcbPtr ← NonDet.assertOpt sc.scTcb
        let st ← getThreadState tcbPtr
        if runnable st
        then refillUpdate scPtr period budget mrefills
        else refillNew scPtr mrefills budget period
      else refillNew scPtr mrefills budget period
    NonDet.when (sc.scTcb ≠ none) <| do
      schedContextResume scPtr
      let tcbPtr ← NonDet.assertOpt sc.scTcb
      let st ← getThreadState tcbPtr
      let ct ← NonDet.gets fun s : State Z => s.curThread
      if tcbPtr = ct then rescheduleRequired
      else NonDet.when (runnable st) <| possibleSwitchTo tcbPtr
    setScObjRef scBadgeUpdate scPtr badge
    setScObjRef scSporadicUpdate scPtr (testBit flag scSporadicFlag)

end

end

end Fl4Spec
