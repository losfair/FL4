/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`GK` for every
spec function of the syscall entry** (spec side only; outside the `JAtZ` cone).

One lemma per spec function reachable from `fl4KernelEntrySyscall` that
MachFieldFamT's `MTK` family leaves out (the functions reaching a machine-time
or IRQ writer: `updateTimeStamp`, `getActiveIRQ`, `maskInterrupt`,
`setIrqState`, the timer and port operations, `clearMemory`/`freeMemory`, and
their callers, plus the decodes), bottom-up by `gk_auto` (generated:
scratch/invB/gen2.py from the spec's call graph). By hand: `rec_del` and
`cap_revoke` (the pre-fixed point of DomRecDel's `dk_recDel` /
`dk_capRevoke`, at the predicate "every `GK` predicate is kept"),
`fl4Awaken` (each fired timer is MachFieldFamT's `sendSignal`), and the
higher-order `syscall`, `orChoiceE`, `checkCapAt`, `archNoReturn`,
`decodeIrqControlInvocationWith`, `portIn`, `portOut`.
-/
import Fl4Proofs.P3.SpecInvValidMachineTimeKit

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem gk_archActivateIdleThread (_t : ObjRef) : GK (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archActivateIdleThread)

theorem gk_activateThread  : GK (activateThread (Z := Unit)) := by
  unfold activateThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_activateThread)

theorem gk_ensureEmpty (slot : CslotPtr) : GKE (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_ensureEmpty)

theorem gk_isIoportRangeFree (f l : IoPort) : GK (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_isIoportRangeFree)

theorem gk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : GKE (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeIoportControlInvocation)

theorem gk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKE (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodePageDirectoryInvocation)

theorem gk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : GKE (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkVpAlignment)

theorem gk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (x0 : VMPageSize) (x1 : VMRights) (x2 : VMAttributes) (x3 : ObjRef) : GKE (createMappingEntries (Z := Unit) base vptr x0 x1 x2 x3) := by
  unfold createMappingEntries; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_createMappingEntries)

theorem gk_ensureSafeMapping (x0 : VMPageEntry × ObjRef) : GKE (ensureSafeMapping (Z := Unit) x0) := by
  unfold ensureSafeMapping; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_ensureSafeMapping)

theorem gk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKE (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodePageInvocation)

theorem gk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKE (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodePageTableInvocation)

theorem gk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKE (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodePdptInvocation)

theorem gk_argsAtLeast (n : Nat) (args : List Data) : GKE (argsAtLeast (Z := Unit) n args) := by
  unfold argsAtLeast; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_argsAtLeast)

theorem gk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : GKE (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_ensurePortOperationAllowed)

theorem gk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : GKE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodePortInvocation)

theorem gk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : GK (selectExt (Z := Unit) a S) := by
  unfold selectExt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_selectExt)

theorem gk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKE (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archDecodeInvocation)

theorem gk_getIrqState (irq : Irq) : GK (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getIrqState)

theorem gk_isIrqActive (irq : Irq) : GK (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_isIrqActive)

theorem gk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GKE (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archDecodeIrqControlInvocation)

theorem gk_archGetSanitiseRegisterInfo (_t : ObjRef) : GK (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archGetSanitiseRegisterInfo)

theorem gk_archInvokeIrqControl (aic : ArchIrqControlInvocation) : GKE (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archInvokeIrqControl)

theorem gk_archInvokeIrqHandler (x0 : IrqHandlerInvocation) : GK (archInvokeIrqHandler (Z := Unit) x0) := by
  unfold archInvokeIrqHandler; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archInvokeIrqHandler)

theorem gk_archMaskIrqSignal (irq : Irq) : GK (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archMaskIrqSignal)

theorem gk_archNoReturn {m : SMonad Unit Unit} (h : GK m) : GK (archNoReturn (Z := Unit) m) := by
  unfold archNoReturn; exact gk_bind h fun _ => gk_pure _
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_archNoReturn ?_)

theorem gk_deleteObjects (ptr : Word) (bits : Nat) : GK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact gk_bind (gk_doMachineOp (mt_freeMemory _ _)) fun _ => gk_modify fun _ => rfl
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_deleteObjects)

theorem gk_performAsidControlInvocation (iv : AsidControlInvocation) : GK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_performAsidControlInvocation)

theorem gk_portIn {f : MachineMonad Data} (h : MaskT f) : GK (portIn (Z := Unit) f) := by
  unfold portIn; exact gk_bind (gk_doMachineOp h) fun _ => gk_pure _
macro_rules | `(tactic| gk_leaf) => `(tactic| (with_reducible refine gk_portIn ?_); mt_auto; done)

theorem gk_portOut {n : Nat} {f : BitVec n → MachineMonad Unit} (h : ∀ w, MaskT (f w)) (w : BitVec n) :
    GK (portOut (Z := Unit) f w) := by
  unfold portOut; exact gk_bind (gk_doMachineOp (h w)) fun _ => gk_pure _
macro_rules | `(tactic| gk_leaf) => `(tactic| (with_reducible refine gk_portOut (fun _ => ?_) _); mt_auto; done)

theorem gk_performIoPortInvocation (i : IoPortInvocation) : GK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_performIoPortInvocation)

theorem gk_archPerformInvocation (i : ArchInvocation) : GKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archPerformInvocation)

theorem gk_lazyFpuRestore (threadPtr : ObjRef) : GK (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_lazyFpuRestore)

theorem gk_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : GK (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archPostSetFlags)

theorem gk_archPrepareNextDomain  : GK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archPrepareNextDomain)

theorem gk_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : GK (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archPrepareSetDomain)

theorem gk_archSwitchToIdleThread  : GK (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archSwitchToIdleThread)

theorem gk_archSwitchToThread (t : ObjRef) : GK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_archSwitchToThread)

theorem gk_tcbReleaseDequeue  : GK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_tcbReleaseDequeue)

theorem gk_awaken  : GK (awaken (Z := Unit)) := by
  unfold awaken; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_awaken)

theorem gk_setNtfnObjRef (update : (Option ObjRef → Option ObjRef) → Notification → Notification) (ref : ObjRef) (new : Option ObjRef) : GK (setNtfnObjRef (Z := Unit) update ref new) := by
  unfold setNtfnObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setNtfnObjRef)

theorem gk_setTcbObjRef (f : (Option ObjRef → Option ObjRef) → Tcb → Tcb) (ref : ObjRef) (new : Option ObjRef) : GK (setTcbObjRef (Z := Unit) f ref new) := by
  unfold setTcbObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setTcbObjRef)

theorem gk_bindNotification (tcbptr ntfnptr : ObjRef) : GK (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_bindNotification)

theorem gk_deletedIrqHandler (irq : Irq) : GK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_deletedIrqHandler)

theorem gk_postCapDeletion (cap : Cap) : GK (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_postCapDeletion)

theorem gk_setCdt (t : Cdt) : GK (setCdt (Z := Unit) t) := by
  unfold setCdt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setCdt)

theorem gk_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : GK (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_emptySlot)

theorem gk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) {f g : NonDetE (State Unit) ε α} (hf : GKE f)
    (hg : GKE g) : GKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE
  refine gke_bind (gke_liftE gk_get) fun _ => gke_bind (gke_liftE (gk_selectF _)) fun r => ?_
  obtain ⟨rv, _⟩ := r
  try dsimp only
  exact gke_ite _ hf hg
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_orChoiceE _ ?_ ?_)

theorem gk_preemptionPoint  : GKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_preemptionPoint)

/-- One step of `rec_del` keeps every `GK` predicate, its recursive calls keeping them. -/
theorem gk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, GK (f k)) (k : RecDelCall) : GKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, GKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k <;> (unfold recDelF; gk_auto) <;> exact hrec' _

/-- **`rec_del` keeps every `GK` predicate** (the pre-fixed point of DomRecDel's `dk_recDel`). -/
theorem gk_recDel (c : RecDelCall) : GKE (recDel (Z := Unit) c) := by
  intro P L σ h x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | ∀ P, WL P → P t → P y.2}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy P' L' ht => gk_recDelF (f := f) (fun _ P'' L'' _ hs _ hz => hz P'' L'' hs) k P' L' t ht y hy,
      fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf c σ).1 hx P L h
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_recDel)

theorem gk_capDelete (slot : CslotPtr) : GKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_capDelete)

/-- One step of `cap_revoke` keeps every `GK` predicate, its recursive calls keeping them. -/
theorem gk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, GK (f k)) (sl : CslotPtr) : GKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, GKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF selectExt
  gk_auto
  all_goals exact hrec' _

/-- **`cap_revoke` keeps every `GK` predicate.** -/
theorem gk_capRevoke (sl : CslotPtr) : GKE (capRevoke (Z := Unit) sl) := by
  intro P L σ h x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | ∀ P, WL P → P t → P y.2}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy P' L' ht => gk_capRevokeF (f := f) (fun _ P'' L'' _ hs _ hz => hz P'' L'' hs) k P' L' t ht y hy,
      fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf sl σ).1 hx P L h
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_capRevoke)

theorem gk_endTimeslice (canTimeout : Bool) : GK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_endTimeslice)

theorem gk_refillResetRr (cscPtr : ObjRef) : GK (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_refillResetRr)

theorem gk_chargeBudget (consumed : Ticks) (canTimeout : Bool) : GK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_chargeBudget)

theorem gk_checkBudget  : GK (checkBudget (Z := Unit)) := by
  unfold checkBudget; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkBudget)

theorem gk_checkBudgetRestart  : GK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkBudgetRestart)

theorem gk_checkCapAt (cap : Cap) (slot : CslotPtr) {m : SMonad Unit Unit} (h : GK m) :
    GK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; gk_auto; all_goals exact h
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_checkCapAt _ _ ?_)

theorem gk_checkDomainTime  : GK (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkDomainTime)

theorem gk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : GKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkHandlerEp)

theorem gk_checkPrio (newPrio : Data) (authTcb : ObjRef) : GKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkPrio)

theorem gk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : GKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_checkValidIpcBuffer)

theorem gk_nextDomain  : GK (nextDomain (Z := Unit)) := by
  unfold nextDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_nextDomain)

theorem gk_switchToThread (t : ObjRef) : GK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_switchToThread)

theorem gk_guardedSwitchTo (thread : ObjRef) : GK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_guardedSwitchTo)

theorem gk_switchToIdleThread  : GK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_switchToIdleThread)

theorem gk_chooseThread  : GK (chooseThread (Z := Unit)) := by
  unfold chooseThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_chooseThread)

theorem gk_getNotification (x0 : ObjRef) : GK (getNotification (Z := Unit) x0) := by
  unfold getNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getNotification)

theorem gk_getNtfnObjRef (update : Notification → Option ObjRef) (ref : ObjRef) : GK (getNtfnObjRef (Z := Unit) update ref) := by
  unfold getNtfnObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getNtfnObjRef)

theorem gk_setNotification (x0 : ObjRef) (x1 : Notification) : GK (setNotification (Z := Unit) x0 x1) := by
  unfold setNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setNotification)

theorem gk_completeSignal (ntfnptr tptr : ObjRef) : GK (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_completeSignal)

theorem gk_dataToObjType (type : Data) : GKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_dataToObjType)

theorem gk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : GKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeBindNotification)

theorem gk_lookupPivotSlot (x0 : Cap) (x1 : CapRef) (x2 : Nat) : GKE (lookupPivotSlot (Z := Unit) x0 x1 x2) := by
  unfold lookupPivotSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_lookupPivotSlot)

theorem gk_lookupSourceSlot (x0 : Cap) (x1 : CapRef) (x2 : Nat) : GKE (lookupSourceSlot (Z := Unit) x0 x1 x2) := by
  unfold lookupSourceSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_lookupSourceSlot)

theorem gk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : GKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeCnodeInvocation)

/-- At a thread cap (as `gk_decodeReadRegisters`). -/
theorem gk_decodeCopyRegisters (data : List Data) (p : ObjRef) (ec : List Cap) :
    GKE (decodeCopyRegisters (Z := Unit) data (.threadCap p) ec) := by
  unfold decodeCopyRegisters; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeCopyRegisters)

theorem gk_slotCapLongRunningDelete (slot : CslotPtr) : GK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_slotCapLongRunningDelete)

theorem gk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : GKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeCvSpace)

theorem gk_subframeNode (nodeCap : Cap) (index depth : Data) : GKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_subframeNode)

theorem gk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : GKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeDeriveSubframe)

theorem gk_decodeDomainScheduleConfigure (args : List Data) : GKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeDomainScheduleConfigure)

theorem gk_decodeDomainScheduleSetStart (args : List Data) : GKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeDomainScheduleSetStart)

theorem gk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : GKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeDomainSet)

theorem gk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : GKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeDomainInvocation)

theorem gk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : GK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4GetMr)

theorem gk_fl4Arg (buf : Option ObjRef) (i : Nat) : GKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4Arg)

theorem gk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : GKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4ConfigureSingleStepping)

theorem gk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : GKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4FpuTransfer)

theorem gk_fl4CheckBpNum (bp : Data) : GKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4CheckBpNum)

theorem gk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4GetBreakpoint)

theorem gk_decodeIrqControlInvocationWith {check : Data → SEMonad Unit Unit} (h : ∀ d, GKE (check d))
    (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) :
    GKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; gk_auto; all_goals exact h _
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_decodeIrqControlInvocationWith (fun _ => ?_) _ _ _ _)

theorem gk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeIrqControlRemapped)

theorem gk_fl4ArchCheckIrq (irq : Data) : GKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4ArchCheckIrq)

theorem gk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4IrqControl)

theorem gk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4SetBreakpoint)

theorem gk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : GKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4SetFlags)

theorem gk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : GKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4SetTimer)

theorem gk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4UnsetBreakpoint)

theorem gk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : GKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeFl4TcbExt)

theorem gk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : GKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeIrqHandlerInvocation)

theorem gk_decodePml4Flush (cap : ArchCap) : GKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodePml4Flush)

theorem gk_rangeCheck (v minV maxV : Word) : GKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_rangeCheck)

/-- At a thread cap (its only caller, `decodeTcbInvocation` from the thread-cap
branch of `fl4DecodeInvocation`; the non-thread-cap branch is l4v's `undefined`). -/
theorem gk_decodeReadRegisters (data : List Data) (p : ObjRef) : GKE (decodeReadRegisters (Z := Unit) data (.threadCap p)) := by
  unfold decodeReadRegisters; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeReadRegisters)

theorem gk_getScReleased (scPtr : ObjRef) : GK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getScReleased)

theorem gk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : GKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSchedContextBind)

theorem gk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : GKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSchedContextUnbindObject)

theorem gk_decodeSchedContextYieldTo (scPtr : ObjRef) : GKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSchedContextYieldTo)

theorem gk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : GKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSchedContextInvocation)

theorem gk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : GKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSchedControlInvocationFlags)

theorem gk_decodeSetFlags (args : List Data) (cap : Cap) : GKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetFlags)

theorem gk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : GKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetIpcBuffer)

theorem gk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetMcpriority)

theorem gk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetPriority)

theorem gk_isBlocked (thread : ObjRef) : GK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_isBlocked)

theorem gk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : GKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeUpdateSc)

theorem gk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetSchedParams)

theorem gk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : GKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetSpace)

theorem gk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetTimeoutEp)

theorem gk_decodeSetTlsBase (args : List Data) (cap : Cap) : GKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeSetTlsBase)

theorem gk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeTcbConfigure)

theorem gk_decodeUnbindNotification (cap : Cap) : GKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeUnbindNotification)

/-- At a thread cap (its only caller, `decodeTcbInvocation` from the thread-cap
branch of `fl4DecodeInvocation`; the non-thread-cap branch is l4v's `undefined`). -/
theorem gk_decodeWriteRegisters (data : List Data) (p : ObjRef) : GKE (decodeWriteRegisters (Z := Unit) data (.threadCap p)) := by
  unfold decodeWriteRegisters; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeWriteRegisters)

/-- At a thread cap. -/
theorem gk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : GKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeTcbInvocation)

theorem gk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : GKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_frameMappingSlot)

theorem gk_decodeTestAndClearAccessed (cap : ArchCap) : GKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeTestAndClearAccessed)

theorem gk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : GKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeUntypedInvocationWith)

theorem gk_doNbrecvFailedTransfer (thread : ObjRef) : GK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_doNbrecvFailedTransfer)

theorem gk_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : GK (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_domainScheduleConfigure)

theorem gk_setNextInterrupt  : GK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setNextInterrupt)

theorem gk_ifConstantBandwidthRefillUnblockCheck (scOpt : Option ObjRef) : GK (ifConstantBandwidthRefillUnblockCheck (Z := Unit) scOpt) := by
  unfold ifConstantBandwidthRefillUnblockCheck; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_ifConstantBandwidthRefillUnblockCheck)

theorem gk_switchSchedContext  : GK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_switchSchedContext)

theorem gk_scAndTimer  : GK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_scAndTimer)

theorem gk_scheduleChooseNewThread  : GK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_scheduleChooseNewThread)

theorem gk_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : GK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_scheduleSwitchThreadFastfail)

theorem gk_scheduleSwitchThreadBranch (candidate ct : ObjRef) (ctSchdble : Bool) : GK (scheduleSwitchThreadBranch (Z := Unit) candidate ct ctSchdble) := by
  unfold scheduleSwitchThreadBranch; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_scheduleSwitchThreadBranch)

theorem gk_schedule  : GK (schedule (Z := Unit)) := by
  unfold schedule; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_schedule)

theorem gk_domainSetStart (index : Nat) : GK (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_domainSetStart)

theorem gk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4ArchDecodeInvocation)

theorem gk_fl4ArchPerformInvocation (x0 : Fl4ArchInvocation) : GKE (fl4ArchPerformInvocation (Z := Unit) x0) := by
  unfold fl4ArchPerformInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4ArchPerformInvocation)

/-- **FL4's TCB timer step keeps every `GK` predicate**: each fired timer is
a `sendSignal` (MachFieldFamT's frame) and the timer reprogram flag. -/
theorem gk_fl4Awaken : GK (fl4Awaken (Z := Unit)) := by
  intro P L σ h x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  show P s'
  clear hx
  induction hx' with
  | refl => exact h
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    have h2 : P σ1 := by
      rcases h1 with rfl | ⟨n, b, e⟩
      · exact ih
      · exact gk_of_mtk (mtk_sendSignal' n b) P L _ ih ((), σ1) (by rw [e]; exact Set.mem_singleton _)
    exact L.view σ1 _ rfl h2
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_fl4Awaken)

/-- At a thread cap. -/
theorem gk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    GKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excaps buffer) := by
  unfold fl4DecodeTcbInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4DecodeTcbInvocation)

theorem gk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : GKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4DecodeInvocation)

theorem gk_resetUntypedCap (srcSlot : CslotPtr) : GKE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_resetUntypedCap)

theorem gk_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : GKE (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeUntypedWith)

theorem gk_invokeCnode (i : CnodeInvocation) : GKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeCnode)

theorem gk_threadSetDomain (tptr : ObjRef) (domain : Domain) : GK (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_threadSetDomain)

theorem gk_setDomain (tptr : ObjRef) (newDom : Domain) : GK (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setDomain)

theorem gk_invokeSetDomain (thread : ObjRef) (domain : Domain) : GK (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeSetDomain)

theorem gk_invokeDomain (domInv : DomainInvocation) : GK (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeDomain)

theorem gk_invokeIrqControl (x0 : IrqControlInvocation) : GKE (invokeIrqControl (Z := Unit) x0) := by
  unfold invokeIrqControl; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeIrqControl)

theorem gk_invokeFl4IrqControl (x0 : Fl4IrqControlInvocation) : GKE (invokeFl4IrqControl (Z := Unit) x0) := by
  unfold invokeFl4IrqControl; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeFl4IrqControl)

theorem gk_setFlags (ref : ObjRef) (flags : TcbFlags) : GK (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setFlags)

theorem gk_invokeFl4Tcb (x0 : Fl4TcbInvocation) : GKE (invokeFl4Tcb (Z := Unit) x0) := by
  unfold invokeFl4Tcb; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeFl4Tcb)

theorem gk_invokeIrqHandler (x0 : IrqHandlerInvocation) : GK (invokeIrqHandler (Z := Unit) x0) := by
  unfold invokeIrqHandler; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeIrqHandler)

theorem gk_ifSporadicActiveCurScTestRefillUnblockCheck (scOpt : Option ObjRef) : GK (ifSporadicActiveCurScTestRefillUnblockCheck (Z := Unit) scOpt) := by
  unfold ifSporadicActiveCurScTestRefillUnblockCheck; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_ifSporadicActiveCurScTestRefillUnblockCheck)

theorem gk_setScObjRef {α : Type} (f : (α → α) → SchedContext → SchedContext) (ref : ObjRef) (new : α) : GK (setScObjRef (Z := Unit) f ref new) := by
  unfold setScObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setScObjRef)

theorem gk_schedContextBindTcb (scPtr tcbPtr : ObjRef) : GK (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_schedContextBindTcb)

theorem gk_invokeSchedContext (iv : SchedContextInvocation) : GK (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeSchedContext)

theorem gk_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : GKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_installTcbCap)

theorem gk_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : GKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_installTcbFrameCap)

theorem gk_restart (thread : ObjRef) : GK (restart (Z := Unit) thread) := by
  unfold restart; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_restart)

theorem gk_setMcpriority (ref : ObjRef) (mcp : Priority) : GK (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setMcpriority)

theorem gk_setPriority (tptr : ObjRef) (prio : Priority) : GK (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setPriority)

theorem gk_invokeTcb (x0 : TcbInvocation) : GKE (invokeTcb (Z := Unit) x0) := by
  unfold invokeTcb; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_invokeTcb)

theorem gk_fl4PerformInvocation (x0 : Bool) (x1 : Bool) (x2 : Bool) (x3 : Fl4Invocation) : GKE (fl4PerformInvocation (Z := Unit) x0 x1 x2 x3) := by
  unfold fl4PerformInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4PerformInvocation)

theorem gk_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : GK (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4ReplyFromKernelError)

theorem gk_handleNoFault (tptr : ObjRef) : GK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleNoFault)

theorem gk_handleFault (thread : ObjRef) (ex : Fault) : GK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleFault)

theorem gk_syscall {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    (h1 : GKE mF) (h2 : ∀ f, GK (hF f)) (h3 : ∀ a, GKE (mE a)) (h4 : ∀ e, GK (hE e))
    (h5 : ∀ b, GKE (mFin b)) : GKE (syscall (Z := Unit) mF hF mE hE mFin) := by
  unfold syscall
  refine gke_bind (gke_withoutPreemption h1) fun r => ?_
  cases r with
  | error f => exact gke_withoutPreemption (h2 f)
  | ok a =>
    refine gke_bind (gke_withoutPreemption (h3 a)) fun r => ?_
    cases r with
    | error e => exact gke_withoutPreemption (h4 e)
    | ok b => exact h5 b
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_syscall ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem gk_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : GKE (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4HandleInvocationR)

theorem gk_getCapReg (reg : Register) : GK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getCapReg)

theorem gk_lookupReply  : GKE (lookupReply (Z := Unit)) := by
  unfold lookupReply; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_lookupReply)

theorem gk_getEndpoint (x0 : ObjRef) : GK (getEndpoint (Z := Unit) x0) := by
  unfold getEndpoint; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getEndpoint)

theorem gk_getReply (x0 : ObjRef) : GK (getReply (Z := Unit) x0) := by
  unfold getReply; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getReply)

theorem gk_getReplyTcb (r : ObjRef) : GK (getReplyTcb (Z := Unit) r) := by
  unfold getReplyTcb; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_getReplyTcb)

theorem gk_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : GK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_maybeReturnSc)

theorem gk_setReplyObjRef (update : (Option ObjRef → Option ObjRef) → Reply → Reply) (ref : ObjRef) (new : Option ObjRef) : GK (setReplyObjRef (Z := Unit) update ref new) := by
  unfold setReplyObjRef; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_setReplyObjRef)

theorem gk_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : GK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_receiveIpcBlocked)

set_option maxHeartbeats 4000000 in
theorem gk_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) : GK (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_receiveIpc)

theorem gk_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : GK (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_tcbNtfnAppend)

theorem gk_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : GK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_receiveSignalBlocked)

theorem gk_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : GK (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_receiveSignal)

theorem gk_handleRecv (isBlocking canReply : Bool) : GK (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleRecv)

theorem gk_handleYield  : GK (handleYield (Z := Unit)) := by
  unfold handleYield; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleYield)

theorem gk_fl4HandleSyscall (rep : Bool) (x0 : Syscall) : GKE (fl4HandleSyscall (Z := Unit) rep x0) := by
  unfold fl4HandleSyscall; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4HandleSyscall)

theorem gk_fl4SyscallFaultIP (thread : ObjRef) : GK (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4SyscallFaultIP)

theorem gk_handleReservedIrq (_irq : Irq) : GK (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleReservedIrq)

theorem gk_handleInterrupt (irq : Irq) : GK (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleInterrupt)

theorem gk_handleSpuriousIrq  : GK (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleSpuriousIrq)

theorem gk_maybeHandleInterrupt (inKernel : Bool) : GK (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_maybeHandleInterrupt)

theorem gk_preemptionPath  : GK (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_preemptionPath)

/-- The syscall event of FL4's `handle_event`. -/
theorem gk_fl4HandleEvent_sys (rep : Bool) (c : Syscall) :
    GKE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  unfold fl4HandleEvent; gk_auto

/-- The interrupt event (l4v's `handle_event Interrupt`). -/
theorem gk_fl4HandleEvent_irq (rep : Bool) : GKE (fl4HandleEvent (Z := Unit) rep .interrupt) := by
  unfold fl4HandleEvent handleEvent; gk_auto

/-- FL4's `call_kernel` from the syscall event. -/
theorem gk_fl4CallKernel_sys (rep : Bool) (c : Syscall) : GK (fl4CallKernel (Z := Unit) rep (.syscallEvent c)) := by
  unfold fl4CallKernel
  exact gk_bind (gke_handleE (gk_fl4HandleEvent_sys rep c) fun _ => gke_withoutPreemption gk_preemptionPath)
    fun _ => gk_bind gk_fl4Awaken fun _ => gk_bind gk_schedule fun _ => gk_activateThread

/-- FL4's `call_kernel` from the interrupt event. -/
theorem gk_fl4CallKernel_irq (rep : Bool) : GK (fl4CallKernel (Z := Unit) rep .interrupt) := by
  unfold fl4CallKernel
  exact gk_bind (gke_handleE (gk_fl4HandleEvent_irq rep) fun _ => gke_withoutPreemption gk_preemptionPath)
    fun _ => gk_bind gk_fl4Awaken fun _ => gk_bind gk_schedule fun _ => gk_activateThread

/-- **The syscall entry keeps every `GK` predicate.** -/
theorem gk_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    GK (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact gk_bind (gk_gets _) fun ct => gk_bind (gk_fl4SyscallFaultIP ct) fun _ => gk_fl4CallKernel_sys rep c

end

end Fl4Proofs.P3.SInvV
