/-
P3 (DESIGN.md §9), invariant line G1 (vih2): **the IRQ ack's handler cap,
carried from the decode to the perform** (spec side only; outside the `JAtZ`
cone: SpecInvValidIrqHandlersF4 and SpecInvDom's `OkDAt` kit).

l4v proves the ack case of `valid_irq_masks` from `valid_irq_handlers` and the
invoked handler cap being in a slot (`cte_wp_at`), carried from
`lookup_cap_and_slot` through `decode_invocation` to `perform_invocation`.
The pieces here:
* `vih_mem_getCap`: `get_cap` keeps the state and returns the slot's `capOpt`.
* `okCap_lookupCapAndSlot`: every `.ok (cap, slot)` outcome of
  `lookupCapAndSlot` has `cap` in `slot` at its state; `okdAt_capFault`: the
  same through `capFaultOnFailure`.
* `okAck_fl4Decode`: a decoded `.invokeIRQHandler (.aCKIrq irq)` comes only
  from the decode's cap `irqHandlerCap irq` (Ext/Invocation's IRQ handler
  branch, `decodeIrqHandlerInvocation`).
* `capOpt_of_ikh`: a cap in a slot stays there across every function of the
  generated frame family (`lookupIpcBuffer`, `lookupExtraCaps`, `getMrs`, the
  decode, `setThreadState`), so the perform's state has `HIrq σ irq`.
* `vimh_invokeIrqHandler_ack`: the perform of the ack keeps `ValidIrqMasks ∧
  ValidIrqHandlers` from `HIrq` (vih1's `vimh_ack`).
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersF4
import Fl4Proofs.P3.SpecInvDom
open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

theorem vih_assertOpt_mem {o : Option Cap} {s : State Unit} {x : Cap × State Unit}
    (hx : x ∈ (NonDet.assertOpt o s).1) : x.2 = s ∧ o = some x.1 := by
  cases o with
  | none => exact hx.elim
  | some a => obtain rfl := Set.mem_singleton_iff.1 hx; exact ⟨rfl, rfl⟩

/-- `get_cap` keeps the state and returns the slot's cap. -/
theorem vih_mem_getCap {o : ObjRef} {c : CnodeIndex} {σ : State Unit} {x : Cap × State Unit}
    (hx : x ∈ (getCap (Z := Unit) (o, c) σ).1) : x.2 = σ ∧ capOpt (σ.kheap o) c = some x.1 := by
  unfold getCap at hx
  try dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  rw [hk]
  cases obj with
  | cnode sz cn =>
    try dsimp only at hx
    obtain ⟨u, ⟨hw, rfl⟩, hx⟩ := hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hz
    have := vih_assertOpt_mem hx
    exact ⟨this.1, by simp only [capOpt, if_pos hw]; exact this.2⟩
  | tcb t =>
    try dsimp only at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact vih_assertOpt_mem hx
  | _ =>
    try dsimp only at hx
    obtain ⟨z, hz, -⟩ := hx
    exact hz.elim

/-- Every `.ok (cap, slot)` of `lookupCapAndSlot` has `cap` in `slot`. -/
theorem okCap_lookupCapAndSlot (t : ObjRef) (c : CapRef) (σ : State Unit) :
    OkDAt σ (fun s r => capOpt (s.kheap r.2.1) r.2.2 = some r.1) (lookupCapAndSlot (Z := Unit) t c) := by
  unfold lookupCapAndSlot
  refine okdAt_bind fun a s _ => ?_
  obtain ⟨⟨o, r⟩, cr⟩ := a
  dsimp only
  refine okdAt_bind fun cap s' h => ?_
  obtain ⟨x, hx, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨e1, e2⟩ := vih_mem_getCap hx
  exact okdAt_returnOk (by rw [e1]; exact e2)

/-- `capFaultOnFailure` adds no `.ok` outcome. -/
theorem okdAt_capFault {α : Type} {P : State Unit → α → Prop} {σ : State Unit} {m : LFMonad Unit α}
    (cp : ObjRef) (rp : Bool) (hm : OkDAt σ P m) : OkDAt σ P (capFaultOnFailure (Z := Unit) cp rp m) := by
  intro a s ha
  unfold capFaultOnFailure NonDetE.handleE at ha
  rw [ExceptT.run_mk] at ha
  obtain ⟨⟨r, s1⟩, h1, h2⟩ := ha
  cases r with
  | ok b =>
    have e := Set.mem_singleton_iff.1 h2
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact hm _ _ h1
  | error e =>
    have e' := Set.mem_singleton_iff.1 h2
    simp at e'

theorem okdAt_mono {ε α : Type} {P Q : State Unit → α → Prop} {σ : State Unit} {m : NonDetE (State Unit) ε α}
    (h : OkDAt σ Q m) (hPQ : ∀ s a, Q s a → P s a) : OkDAt σ P m :=
  fun a s ha => hPQ s a (h a s ha)

/-- The IRQ handler decode acks only its own line. -/
theorem okAck_decodeIrqHandler (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ v => ∀ i, v = .aCKIrq i → i = irq) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun i h => by cases h; rfl)
    | exact okdAt_returnOk (fun i h => by cases h)
    | (apply okdAt_ite)
    | split)

set_option maxHeartbeats 4000000 in
/-- **A decoded ack names the decode's handler cap.** -/
theorem okAck_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ inv => ∀ i, inv = .invokeIRQHandler (.aCKIrq i) → cap = .irqHandlerCap i)
      (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun i h => nomatch h)
    | exact okdAt_liftME (okdAt_mono (okAck_decodeIrqHandler _ _ _ _) fun _ v hv i h => by
        cases h; rw [hv i rfl])
    | exact okdAt_liftME (fun _ _ _ i h => nomatch h)
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-- A cap in a slot stays there across a frame-family function. -/
theorem capOpt_of_ikh {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, IKH (fun s => hV s = v) m)
    {σ : State Unit} {x : α × State Unit} (hx : x ∈ (m σ).1) {p : ObjRef} {r : CnodeIndex} {c : Cap}
    (hc : capOpt (σ.kheap p) r = some c) : capOpt (x.2.kheap p) r = some c := by
  rw [hV_cap (h (hV σ) σ rfl x hx)]; exact hc

theorem hIrq_of_hV {σ σ' : State Unit} (e : hV σ' = hV σ) {irq : Irq} (h : HIrq σ irq) : HIrq σ' irq := by
  obtain ⟨p, cref, hc⟩ := h; exact ⟨p, cref, by rw [hV_cap e]; exact hc⟩

/-- **The ack's perform with its handler cap in a slot** keeps `ValidIrqMasks ∧
ValidIrqHandlers` (vih1's `vimh_ack`). -/
theorem vimh_invokeIrqHandler_ack {irq : Irq} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ)
    (hn : HIrq σ irq) : ∀ x ∈ (invokeIrqHandler (Z := Unit) (.aCKIrq irq) σ).1,
      ValidIrqMasks x.2 ∧ ValidIrqHandlers x.2 := by
  intro x hx
  simp only [invokeIrqHandler, archInvokeIrqHandler] at hx
  exact vimh_ack hm hh hn x hx

end

end Fl4Proofs.P3.SInvV
