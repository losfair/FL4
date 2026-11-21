/-
P3 (DESIGN.md §9), invariant line G1 (vfh2): **the decode's carry for VfhAll**
(spec side only, outside the JAtZ cone; l4v: `decode_invocation`'s result is
`valid_invocation`, here the slots it writes are no fault-handler slots and the
caps it writes are `CnOk`).

* `cnOk_maskCap`, `cnOk_updateCapData`, `vfh_okv_deriveCap`: the cap
  transformations keep a CNode cap's object and radix (`CnSame`).
* `vfh_okv_decodeCnode`: insert / move / rotate targets are found by
  `lookup_slot_for_cnode_op` (full slots, SpecInvVfhC), the caps are read from
  slots (`CnOk` by `CnDom`) and transformed.
* `vfh_okd_checkHandlerEp` / `vfh_okd_decodeTcb`: the installed fault handler
  is valid (the decode's `check_handler_ep`).
* `vfh_okv_decodeIrqControl` (IRQ control, arch IOAPIC/MSI, FL4's remapped
  IOAPIC: the handler slot is a target slot), `vfh_okd_decodeIrqHandler` (the
  set-handler cap is a notification cap).
-/
import Fl4Proofs.P3.SpecInvVfhC
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

theorem vfh_the_mem {α : Type} [Nonempty α] {xs : List α} {i : Nat} (hi : i < xs.length) : the xs[i]? ∈ xs := by
  rw [List.getElem?_eq_getElem hi]; exact List.getElem_mem hi

theorem cnSame_maskCap (c : Cap) (r : CapRights) : CnSame c (maskCap r c) := by
  intro p q g e
  cases c <;> simp_all [maskCap, capRightsUpdate]

theorem cnSame_updateCapData (c : Cap) (pr : Bool) (w : Data) : CnSame c (updateCapData pr w c) := by
  intro p q g e
  cases c with
  | cnodeCap r b g0 =>
    refine ⟨g0, ?_⟩
    simp only [updateCapData, isEpCap, isNtfnCap, isCnodeCap, theCnodeCap] at e
    split_ifs at e <;> simp_all
  | archObjectCap a =>
    simp only [updateCapData, isEpCap, isNtfnCap, isCnodeCap, isArchCap, archUpdateCapData] at e
    split_ifs at e <;> cases e
  | endpointCap =>
    simp only [updateCapData, isEpCap] at e
    split_ifs at e <;> simp_all [badgeUpdate]
  | notificationCap =>
    simp only [updateCapData, isEpCap, isNtfnCap] at e
    split_ifs at e <;> simp_all [badgeUpdate]
  | _ => simp_all [updateCapData, isEpCap, isNtfnCap, isCnodeCap, isArchCap]

theorem cnOk_maskCap {σ : State Unit} {c : Cap} (h : CnOk σ c) (r : CapRights) : CnOk σ (maskCap r c) :=
  h.same (cnSame_maskCap c r)

theorem cnOk_updateCapData {σ : State Unit} {c : Cap} (h : CnOk σ c) (pr : Bool) (w : Data) :
    CnOk σ (updateCapData pr w c) := h.same (cnSame_updateCapData c pr w)

theorem vfh_okv_getCapOk {ε : Type} (σ0 : State Unit) (hd : CnDom σ0) (sl : CslotPtr) :
    OkV σ0 (CnOk σ0) (NonDetE.liftE (ε := ε) (getCap (Z := Unit) sl)) :=
  okv_mono (vfh_okv_getCap sl) fun c h => hd sl c h

theorem vfh_okv_deriveCap (σ0 : State Unit) (sl : CslotPtr) (c : Cap) (hc : CnOk σ0 c) :
    OkV σ0 (CnOk σ0) (deriveCap (Z := Unit) sl c) := by
  intro s hs a s' h
  have e : hV s' = hV s := hv_deriveCap (P := fun x => hV x = hV s) sl c s rfl _ h
  exact ⟨e.trans hs, hc.same (vfh_deriveCap_cn sl c a s s' h)⟩

theorem vfh_okv_liftME {ε α β : Type} {σ0 : State Unit} {Pr : β → Prop} {g : α → β} {m : NonDetE (State Unit) ε α}
    (h : OkV σ0 (fun a => Pr (g a)) m) : OkV σ0 Pr (NonDetE.liftME g m) := fun s hs => okdAt_liftME (h s hs)


/-! ## CNode -/

set_option maxHeartbeats 8000000 in
theorem vfh_okv_decodeCnode (σ0 : State Unit) (hd : CnDom σ0) (label : Data) (args : List Data) (cap : Cap)
    (excaps : List Cap) (hc : CnOk σ0 cap) (hex : ∀ c ∈ excaps, CnOk σ0 c) :
    OkV σ0 (VCn σ0) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  simp only [lookupTargetSlot, lookupSourceSlot, lookupPivotSlot]
  repeat' (first
    | (refine okv_bind (vfh_lookupSlotForCnodeOp σ0 hd _ _ _ _ (by first | exact hc | exact hex _ (vfh_the_mem (by omega)) | exact hex _ (vfh_the_mem (by simp_all)))) fun _ _ => ?_)
    | (refine okv_bind (vfh_okv_getCapOk σ0 hd _) fun _ _ => ?_)
    | (refine okv_bind (okv_ite_app _ (okv_returnOk ?_) (vfh_okv_deriveCap σ0 _ _ ?_)) fun _ _ => ?_)
    | exact okv_returnOk (by
        split <;> exact ⟨fun hb => (vfh_notBad_cnFull (by assumption) hb).elim, by assumption⟩)
    | exact okv_returnOk ⟨fun hb => (vfh_notBad_cnFull (by assumption) hb).elim,
        fun hb => (vfh_notBad_cnFull (by assumption) hb).elim, fun hb => (vfh_notBad_cnFull (by assumption) hb).elim,
        cnOk_updateCapData (by assumption) _ _, cnOk_updateCapData (by assumption) _ _⟩
    | exact okv_throw _
    | exact okv_returnOk trivial
    | (refine okv_returnOk_bind ?_)
    | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
    | split
    | (apply okv_ite))
  all_goals first
    | (split <;> exact cnOk_updateCapData (cnOk_maskCap (by assumption) _) _ _)
    | exact cnOk_updateCapData (cnOk_maskCap (by assumption) _) _ _
    | exact cnOk_maskCap (by assumption) _
    | (split <;> first | exact cnOk_updateCapData (cnOk_maskCap (by assumption) _) _ _ |
        exact cnOk_maskCap (by assumption) _)

/-! ## TCB -/

theorem okdAt_bind_v {ε α β : Type} {σ : State Unit} {Q : State Unit → α → Prop} {P : State Unit → β → Prop}
    {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : OkDAt σ Q m)
    (hg : ∀ a s, Q s a → OkDAt s P (g a)) : OkDAt σ P (m >>= g) :=
  okdAt_bind fun a s h => hg a s (hm a s h)

theorem vfh_okd_checkHandlerEp (pos : Nat) (h : Cap × CslotPtr) (σ : State Unit) :
    OkDAt σ (fun _ r => validFaultHandler r.1) (checkHandlerEp (Z := Unit) pos h) := by
  unfold checkHandlerEp NonDetE.unlessE
  refine okdAt_bind fun a s ha => ?_
  split at ha
  · rename_i hv
    exact okdAt_returnOk hv
  · exact (okdAt_throw (P := fun _ _ => False) _ a s ha).elim

theorem vfh_vtcb_some {fh : Cap × CslotPtr} (h : validFaultHandler fh.1) :
    ∀ c sl, some fh = some (c, sl) → validFaultHandler c := by
  intro c sl e; cases e; exact h

theorem vfh_vtcb_none : ∀ (c : Cap) (sl : CslotPtr), (none : Option (Cap × CslotPtr)) = some (c, sl) →
    validFaultHandler c := by
  intro c sl e; cases e

set_option maxHeartbeats 8000000 in
theorem vfh_okd_decodeTcb (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ i => VTcb i) (decodeTcbInvocation (Z := Unit) label args cap slot excaps) := by
  unfold decodeTcbInvocation
  split
  all_goals (try unfold decodeReadRegisters)
  all_goals (try unfold decodeWriteRegisters)
  all_goals (try unfold decodeCopyRegisters)
  all_goals (try unfold decodeTcbConfigure)
  all_goals (try unfold decodeSetPriority)
  all_goals (try unfold decodeSetMcpriority)
  all_goals (try unfold decodeSetSchedParams)
  all_goals (try unfold decodeSetTimeoutEp)
  all_goals (try unfold decodeSetIpcBuffer)
  all_goals (try unfold decodeSetSpace)
  all_goals (try unfold decodeCvSpace)
  all_goals (try unfold decodeUpdateSc)
  all_goals (try unfold decodeBindNotification)
  all_goals (try unfold decodeUnbindNotification)
  all_goals (try unfold decodeSetTlsBase)
  all_goals (try unfold decodeSetFlags)
  all_goals repeat' (first
    | exact okdAt_throw _
    | (refine okdAt_bind_v (vfh_okd_checkHandlerEp _ _ _) fun _ _ hvfh => ?_)
    | exact okdAt_returnOk trivial
    | exact okdAt_returnOk (vfh_vtcb_some hvfh)
    | exact okdAt_returnOk vfh_vtcb_none
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-! ## IRQ control and handlers -/

set_option maxHeartbeats 8000000 in
theorem vfh_okv_decodeIrqControl (σ0 : State Unit) (hd : CnDom σ0) (remapped : Bool) (label : Data)
    (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (hex : ∀ c ∈ cps, CnOk σ0 c) :
    OkV σ0 (VFl4IrqC σ0) (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl decodeIrqControlRemapped decodeIrqControlInvocationWith archDecodeIrqControlInvocation
  simp only [lookupTargetSlot]
  repeat' (first
    | (refine vfh_okv_liftME ?_)
    | (refine okv_bind (vfh_lookupSlotForCnodeOp σ0 hd _ _ _ _
        (by first | exact hex _ (vfh_the_mem (by omega)) | exact hex _ (vfh_the_mem (by simp_all)))) fun _ _ => ?_)
    | exact okv_returnOk (vfh_notBad_cnFull (by assumption))
    | exact okv_throw _
    | (refine okv_returnOk_bind ?_)
    | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
    | split
    | (apply okv_ite))

theorem vfh_okd_decodeIrqHandler (σ0 : State Unit) (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr))
    (s : State Unit) : OkDAt s (fun _ i => VIh σ0 i) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  split
  · exact okdAt_returnOk trivial
  · split
    · split
      · generalize the cps.head? = p
        obtain ⟨cap, slot⟩ := p
        dsimp only
        split
        · rename_i hn
          exact okdAt_returnOk (cnOk_of_nc fun _ _ _ e => by rw [e] at hn; simp [isNtfnCap] at hn)
        · exact okdAt_throw _
      · exact okdAt_throw _
    · split
      · exact okdAt_returnOk trivial
      · exact okdAt_throw _

end

end Fl4Proofs.P3.SInv
