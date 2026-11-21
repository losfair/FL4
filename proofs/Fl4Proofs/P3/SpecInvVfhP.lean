/-
P3 (DESIGN.md §9), invariant line G1 (vfh1): **the cap-writing performs of
CNode, IRQ and TCB invocations keep `VfhV`** (spec side only, outside the
JAtZ cone), from the facts their decodes establish, stated at the anchor
(the decode's state, carried to the perform by the frames: `VS σ0`).

* `VCn σ0 i`: every slot a CNode invocation writes a cap into is no
  fault-handler slot of `σ0` or gets a valid fault handler (insert, move,
  rotate / swap); revoke, delete, cancel-badged-sends need nothing.
  `vs_invokeCnode`.
* `VIrqC σ0 i` / `VFl4IrqC σ0 i`: the handler slot of an IRQ control issue is
  no fault-handler slot (`vs_invokeIrqControl`, `vs_archInvokeIrqControl`,
  `vs_invokeFl4IrqControl`). `vs_invokeIrqHandler` is uniform: the IRQ node
  slot `(node, [])` has index `[]`.
* `VTcb i`: the fault handler a `ThreadControlCaps` / `ThreadControlSched`
  installs is a valid fault handler (the decode's `check_handler_ep`);
  `vs_installTcbCap` (the other TCB slots are no fault-handler slots by index),
  `vs_installTcbFrameCap`, `vs_invokeTcb`.
-/
import Fl4Proofs.P3.SpecInvVfhW
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

theorem vs_doMachineOp {σ0 : State Unit} {α : Type} (mop : NonDet MachineState α) :
    IK (VS σ0) (doMachineOp (Z := Unit) mop) := ik_doMachineOp (fun _ _ h => vs_of_kheap rfl h) mop

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_doMachineOp _)

/-! ## CNode -/

/-- The slots a CNode invocation writes into: no fault-handler slots of the
anchor, or the cap written there a valid fault handler. -/
def VCn (σ0 : State Unit) : CnodeInvocation → Prop
  | .insertCall cap _ dest => (vfh_Bad σ0 dest → validFaultHandler cap) ∧ CnOk σ0 cap
  | .moveCall cap _ dest => (vfh_Bad σ0 dest → validFaultHandler cap) ∧ CnOk σ0 cap
  | .rotateCall c1 c2 s1 s2 s3 => (vfh_Bad σ0 s1 → validFaultHandler c2) ∧ (vfh_Bad σ0 s2 → validFaultHandler c1) ∧
      (vfh_Bad σ0 s3 → validFaultHandler c2) ∧ CnOk σ0 c1 ∧ CnOk σ0 c2
  | _ => True

theorem vs_invokeCnode {σ0 : State Unit} (i : CnodeInvocation) (h : VCn σ0 i) :
    IKE (VS σ0) (invokeCnode (Z := Unit) i) := by
  cases i with
  | revokeCall sl => unfold invokeCnode; exact vs_capRevoke sl σ0
  | deleteCall sl => unfold invokeCnode; exact vs_capDelete sl σ0
  | insertCall cap src dest => unfold invokeCnode withoutPreemption; exact ike_liftE (vs_capInsert src dest h.1 h.2)
  | moveCall cap src dest => unfold invokeCnode withoutPreemption; exact ike_liftE (vs_capMove src dest h.1 h.2)
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨h1, h2, h3, k1, k2⟩ := h
    unfold invokeCnode withoutPreemption
    refine ike_liftE ?_
    split
    · rename_i e; subst e; exact vs_capSwap _ _ h1 h2 k2 k1
    · exact ik_bind (vs_capMove _ _ h3 k2) fun _ => vs_capMove _ _ h2 k1
  | cancelBadgedSendsCall cap =>
    unfold invokeCnode withoutPreemption
    split <;> (try (rename_i heq; cases heq; done))
    all_goals first
      | exact ike_liftE (ik_when _ (hv_cancelBadgedSends (P := VS σ0) _ _))
      | exact ike_liftE ik_fail

/-! ## IRQ control and handlers -/

def VIrqC (σ0 : State Unit) : IrqControlInvocation → Prop
  | .irqControl _ handlerSlot _ => ¬ vfh_Bad σ0 handlerSlot
  | .archIRQControl (.issueIRQHandlerIOAPIC _ dest _ _ _ _ _ _) => ¬ vfh_Bad σ0 dest
  | .archIRQControl (.issueIRQHandlerMSI _ dest _ _ _ _ _) => ¬ vfh_Bad σ0 dest

def VFl4IrqC (σ0 : State Unit) : Fl4IrqControlInvocation → Prop
  | .spec i => VIrqC σ0 i
  | .ioapicRemapped _ dest _ _ _ _ _ _ _ => ¬ vfh_Bad σ0 dest

theorem vs_invokeIrqControl {σ0 : State Unit} (i : IrqControlInvocation) (h : VIrqC σ0 i) :
    IKE (VS σ0) (invokeIrqControl (Z := Unit) i) := by
  cases i with
  | irqControl irq hs cs =>
    unfold invokeIrqControl
    exact ike_liftE (ik_bind (vs_setIrqState _ _) fun _ => vs_capInsert _ _ (fun hb => (h hb).elim) (cnOk_of_nc fun _ _ _ e => by cases e))
  | archIRQControl a =>
    unfold invokeIrqControl archInvokeIrqControl withoutPreemption
    cases a with
    | issueIRQHandlerIOAPIC irq dest src io pin lv pol vec =>
      refine ike_liftE ?_
      refine ik_bind (vs_doMachineOp _) fun _ => ik_pure_bind ?_
      refine ik_bind (hv_updateIrqState _ _) fun _ => ik_bind (vs_setIrqState _ _) fun _ => ?_
      exact vs_capInsert _ _ (fun hb => (h hb).elim) (cnOk_of_nc fun _ _ _ e => by cases e)
    | issueIRQHandlerMSI irq dest src bus dev func hd =>
      refine ike_liftE ?_
      refine ik_pure_bind ?_
      refine ik_bind (hv_updateIrqState _ _) fun _ => ik_bind (vs_setIrqState _ _) fun _ => ?_
      exact vs_capInsert _ _ (fun hb => (h hb).elim) (cnOk_of_nc fun _ _ _ e => by cases e)

theorem vs_invokeFl4IrqControl {σ0 : State Unit} (i : Fl4IrqControlInvocation) (h : VFl4IrqC σ0 i) :
    IKE (VS σ0) (invokeFl4IrqControl (Z := Unit) i) := by
  cases i with
  | spec i => unfold invokeFl4IrqControl; exact vs_invokeIrqControl i h
  | ioapicRemapped irq dest src io pin lv pol vec hd =>
    unfold invokeFl4IrqControl withoutPreemption
    refine ike_liftE ?_
    refine ik_bind (vs_doMachineOp _) fun _ => ik_pure_bind ?_
    refine ik_bind (hv_updateIrqState _ _) fun _ => ik_bind (vs_setIrqState _ _) fun _ => ?_
    exact vs_capInsert _ _ (fun hb => (h hb).elim) (cnOk_of_nc fun _ _ _ e => by cases e)

theorem vfh_nil_ne : ([] : CnodeIndex) ≠ tcbCnodeIndex 3 := by decide

/-- The set-handler cap is `CnOk` (it is a notification cap, the decode's check). -/
def VIh (σ0 : State Unit) : IrqHandlerInvocation → Prop
  | .setIRQHandler _ c _ => CnOk σ0 c
  | _ => True

theorem vs_invokeIrqHandler {σ0 : State Unit} (i : IrqHandlerInvocation) (h : VIh σ0 i) :
    IK (VS σ0) (invokeIrqHandler (Z := Unit) i) := by
  cases i with
  | aCKIrq irq => unfold invokeIrqHandler archInvokeIrqHandler; exact vs_doMachineOp _
  | setIRQHandler irq cap sl =>
    unfold invokeIrqHandler getIrqSlot
    refine ik_gets_bind fun σ => ikp_of_ik ?_ σ
    exact ik_bind (vs_capDeleteOne _ σ0) fun _ => vs_capInsert _ _ (fun hb => (vfh_nil_ne hb.1).elim) h
  | clearIRQHandler irq =>
    unfold invokeIrqHandler
    exact ik_bind (hv_getIrqSlot _) fun _ => vs_capDeleteOne _ σ0

/-! ## TCB -/

/-- `same_object_as nc c'` with `c'` a slot cap: a CNode `nc` has `c'`'s object and radix. -/
theorem vfh_sameObj_cn {nc c' : Cap} (h : sameObjectAs nc c') : CnSame c' nc := by
  intro p r g e
  subst e
  cases c' <;> simp_all [sameObjectAs, sameRegionAs, isCnodeCap, objRefOf] <;> exact h.2

/-- `check_cap_at newCap src (check_cap_at (ThreadCap t) sl (cap_insert newCap src dst))`
into a slot that is no fault-handler slot or with a valid handler: the re-read
source cap gives `CnOk`. -/
theorem vs_checkCapAt_ins {σ0 : State Unit} (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr)
    (hd : vfh_Bad σ0 dst → validFaultHandler nc) :
    IK (VS σ0) (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  intro σ
  refine ikp_getCap_bind fun c' hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro hσ x hx
    have hk : CnOk σ nc := (hσ.cnOk hc').same (vfh_sameObj_cn hso)
    refine vs_pin hσ (ik_bind (hv_getCap _) fun _ => ik_ite _ (vs_capInsert _ _ (fun hb => hd (hb.back hσ.2.1)) hk)
      (ik_pure _)) x hx
  · exact ikp_of_ik (ik_pure _) σ

theorem vs_installTcbCap {σ0 : State Unit} (target : ObjRef) (slot : CslotPtr) (n : Nat)
    (o : Option (Cap × CslotPtr))
    (h : tcbCnodeIndex n = tcbCnodeIndex 3 → ∀ c sl, o = some (c, sl) → validFaultHandler c) :
    IKE (VS σ0) (installTcbCap (Z := Unit) target slot n o) := by
  cases o with
  | none => unfold installTcbCap; exact ike_returnOk _
  | some p =>
    obtain ⟨c, sl⟩ := p
    unfold installTcbCap
    refine ike_bind (vs_capDelete _ σ0) fun _ => ?_
    refine ike_unlessE _ (ike_liftE ?_)
    exact vs_checkCapAt_ins _ _ _ _ _ fun hb => h hb.1 c sl rfl

theorem vs_installTcbFrameCap {σ0 : State Unit} (target : ObjRef) (slot : CslotPtr)
    (b : Option (VSpaceRef × Option (Cap × CslotPtr))) : IKE (VS σ0) (installTcbFrameCap (Z := Unit) target slot b) := by
  cases b with
  | none => unfold installTcbFrameCap; exact ike_returnOk _
  | some p =>
    obtain ⟨ptr, fr⟩ := p
    unfold installTcbFrameCap
    refine ike_bind (vs_capDelete _ σ0) fun _ => ?_
    refine ike_bind (ike_liftE (hv_threadSet _ _ fun _ => rfl)) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · cases fr with
      | none => exact ik_pure _
      | some q =>
        obtain ⟨c, sl⟩ := q
        exact vs_checkCapAt_ins _ _ _ _ _ fun hb => absurd hb.1 (show tcbCnodeIndex 2 ≠ tcbCnodeIndex 3 by decide)
    · exact ike_bind (ike_liftE (ik_gets _)) fun _ => ike_liftE (ik_when _ (hv_rescheduleRequired))

/-- What a TCB invocation's decode establishes: the fault handler it installs is valid. -/
def VTcb : TcbInvocation → Prop
  | .threadControlCaps _ _ fh _ _ _ _ => ∀ c sl, fh = some (c, sl) → validFaultHandler c
  | .threadControlSched _ _ fh _ _ _ => ∀ c sl, fh = some (c, sl) → validFaultHandler c
  | _ => True

theorem vs_invokeTcb {σ0 : State Unit} (i : TcbInvocation) (h : VTcb i) : IKE (VS σ0) (invokeTcb (Z := Unit) i) := by
  cases i with
  | threadControlCaps t sl fh th cr vr buf =>
    unfold invokeTcb
    refine ike_bind (vs_installTcbCap _ _ 3 _ fun _ => h) fun _ => ?_
    refine ike_bind (vs_installTcbCap _ _ 4 _ fun e => absurd e (by decide)) fun _ => ?_
    refine ike_bind (vs_installTcbCap _ _ 0 _ fun e => absurd e (by decide)) fun _ => ?_
    refine ike_bind (vs_installTcbCap _ _ 1 _ fun e => absurd e (by decide)) fun _ => ?_
    exact ike_bind (vs_installTcbFrameCap _ _ _) fun _ => ike_returnOk _
  | threadControlSched t sl fh mcp pr sc =>
    unfold invokeTcb
    refine ike_bind (vs_installTcbCap _ _ 3 _ fun _ => h) fun _ => ?_
    hv_auto
  | _ => unfold invokeTcb; split <;> (try (rename_i heq; cases heq; done)) <;> hv_auto

/-! ## IPC cap transfer -/

/-- `derive_cap` keeps a CNode cap's object and radix (or yields a non-CNode cap). -/
theorem vfh_deriveCap_cn (sl : CslotPtr) (c c' : Cap) (σ s : State Unit)
    (h : ((.ok c', s) : Except SyscallError Cap × State Unit) ∈ ((deriveCap (Z := Unit) sl c).run σ).1) :
    CnSame c c' := by
  revert c' s
  show OkDAt σ (fun _ c' => CnSame c c') (deriveCap (Z := Unit) sl c)
  cases c with
  | archObjectCap a =>
    simp only [deriveCap]; unfold archDeriveCap
    split <;> first | exact okdAt_throw _ | exact okdAt_returnOk (cnSame_nc fun _ _ _ h => by cases h)
  | untypedCap d b n f =>
    simp only [deriveCap]
    exact okdAt_bind fun _ _ _ => okdAt_returnOk (cnSame_refl _)
  | zombie => simp only [deriveCap]; exact okdAt_returnOk (cnSame_nc fun _ _ _ h => by cases h)
  | irqControlCap => simp only [deriveCap]; exact okdAt_returnOk (cnSame_nc fun _ _ _ h => by cases h)
  | _ => simp only [deriveCap]; exact okdAt_returnOk (cnSame_refl _)

/-- A bind whose head keeps `P` and whose `.ok` outcomes continue pinned. -/
theorem ikpE_bind_ok {P : State Unit → Prop} {ε α β : Type} {σ : State Unit} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : IKp P σ (ExceptT.run m))
    (hg : ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → IKp P s (ExceptT.run (g a))) :
    IKp P σ (ExceptT.run (m >>= g)) := by
  intro hσ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨⟨r, s⟩, h1, hx⟩ := hx
  have h1' := hm hσ _ h1
  cases r with
  | error e => simp only [ExceptT.bindCont] at hx; rw [Set.mem_singleton_iff.1 hx]; exact h1'
  | ok a => simp only [ExceptT.bindCont] at hx; exact hg a s h1 h1' x hx

/-- **`transfer_caps_loop`** into receive slots that are no fault-handler slots
of the anchor (the receive slot is looked up by `get_receive_slots`). -/
theorem vs_transferCapsLoop {σ0 : State Unit} (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      (∀ s ∈ sl, ¬ vfh_Bad σ0 s) → (∀ c ∈ cs, CnOk σ0 c.1) → IK (VS σ0) (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi, _, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, hsl, hcs => by
    have ih := fun sl' mi' h' => vs_transferCapsLoop (σ0 := σ0) ep rb (n + 1) cs sl' mi' h'
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    unfold transferCapsLoop
    refine hv_constOnFailure _ _ ?_
    refine ike_returnOk_bind ?_
    split
    · exact ike_bind (ike_liftE (hv_setExtraBadge _ _ _)) fun _ => ike_liftE (ih _ _ hsl)
    · split
      · rename_i hne
        obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hne
        intro σ hσ
        refine ikpE_bind_ok (P := VS σ0) (hv_deriveCap _ _ σ) (fun c' s' hd' => ?_) hσ
        have hk : CnOk σ0 c' := (hcs (c, s) (by simp)).same (vfh_deriveCap_cn _ _ _ _ _ hd')
        refine ikp_of_ik (?_ : IKE (VS σ0) _) s'
        refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
        refine ike_bind (ike_liftE (vs_capInsert _ _ (fun hb => (hsl d (by simp) hb).elim) hk)) fun _ => ?_
        exact ike_liftE (ih _ _ fun s' hs' => hsl s' (List.mem_cons_of_mem _ hs'))
      · exact ike_returnOk _

end

end Fl4Proofs.P3.SInv
