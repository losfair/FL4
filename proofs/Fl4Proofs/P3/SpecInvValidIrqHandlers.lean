/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, vih1): **`ValidIrqHandlers`
(l4v `valid_irq_handlers`) and the IRQ ack's leaf of `ValidIrqMasks`** (spec side
only; outside the `JAtZ` cone: imports CnodeOther / DelAbs / SpecCnK and
SpecInvValidIrqMasks only).

* `ValidIrqHandlers σ`: every IRQ handler cap readable in a slot (`capOpt`, what
  `getCap` returns) names a line that is not inactive (l4v `valid_irq_handlers`:
  `cap_irqs cap ⊆ {irq. interrupt_states s irq ≠ IRQInactive}` for every cap of
  `caps_of_state`).
* `HIrq σ irq`: some slot holds `irqHandlerCap irq`. `HK σ σ'`: every line named
  by a handler cap of `σ'` is either named by one in `σ` and not newly inactive,
  or not inactive in `σ'`; reflexive, transitive, and `ValidIrqHandlers` is kept
  along it (`ValidIrqHandlers.hk`). The writers' leaves are `HK` facts:
  * `hk_of_kheap_is`: the heap's caps and `interruptStates` kept;
  * `hk_setCap`: `set_cap` of a cap that is not a handler cap, or of a handler
    cap whose line is already named (a copy/move/mint/derive of a cap read from a
    slot of the same state: `hk_setCap_named`) or not inactive (the IRQ control
    issue after its `set_irq_state IRQSignal`: `hk_setCap_active`);
  * `hk_setIrqState_active`: `set_irq_state` of a non-inactive state;
    `hk_setIrqState_inactive`: of `IRQInactive` for a line no slot names (the
    deletion's `deleted_irq_handler`, after `empty_slot` removed the final cap:
    `final_handler_unique` (a final handler cap, `is_final_cap'` over
    `gen_obj_refs`, is the only slot naming its line) and `setCap_null_unique`
    (after `set_cap NullCap` over that slot no slot names it)).
* The ack: `vim_ack` (`maskInterrupt false irq` keeps `ValidIrqMasks` when the
  line is not inactive), `vih_ack` (it keeps `ValidIrqHandlers`), and
  `vimh_ack`: from `ValidIrqMasks ∧ ValidIrqHandlers` and the invoked handler
  cap in a slot (`HIrq σ irq`, the decode's lookup carried to the perform), both
  are kept. This replaces invB's ∀-states ack leaf (`wl_vim_of`'s `hA`, false).
* `boot_vih`: the initial state (no handler cap in `initKheap`).

Not done here (KENTRY-PLAN vih1): the whole-entry `HK` family (`kentry_vih`) and
the decode→perform carry of `HIrq` for the ack (`kentry_validIrqMasks`).
-/
import Fl4Proofs.P3.SpecInvValidIrqMasks
import Fl4Proofs.P3.CnodeOther
import Fl4Proofs.P3.DelAbs
import Fl4Proofs.P3.SpecCnK

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3

noncomputable section

/-- **l4v `valid_irq_handlers`** (module docstring). -/
def ValidIrqHandlers (σ : State Unit) : Prop :=
  ∀ p cref irq, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → σ.interruptStates irq ≠ .irqInactive

/-- Some slot holds a handler cap for `irq`. -/
def HIrq (σ : State Unit) (irq : Irq) : Prop :=
  ∃ p cref, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq)

theorem ValidIrqHandlers.active {σ : State Unit} (h : ValidIrqHandlers σ) {irq : Irq} (hn : HIrq σ irq) :
    σ.interruptStates irq ≠ .irqInactive := by
  obtain ⟨p, cref, hc⟩ := hn; exact h p cref irq hc

/-- **The step relation of `ValidIrqHandlers`** (module docstring). -/
def HK (σ σ' : State Unit) : Prop :=
  ∀ irq, HIrq σ' irq → σ'.interruptStates irq ≠ .irqInactive ∨
    (HIrq σ irq ∧ (σ.interruptStates irq ≠ .irqInactive → σ'.interruptStates irq ≠ .irqInactive))

theorem HK.refl (σ : State Unit) : HK σ σ := fun _ h => Or.inr ⟨h, id⟩

theorem HK.trans {σ1 σ2 σ3 : State Unit} (h1 : HK σ1 σ2) (h2 : HK σ2 σ3) : HK σ1 σ3 := by
  intro irq h3
  rcases h2 irq h3 with e | ⟨hn2, m23⟩
  · exact Or.inl e
  · rcases h1 irq hn2 with e | ⟨hn1, m12⟩
    · exact Or.inl (m23 e)
    · exact Or.inr ⟨hn1, fun e => m23 (m12 e)⟩

theorem ValidIrqHandlers.hk {σ σ' : State Unit} (h : ValidIrqHandlers σ) (hk : HK σ σ') :
    ValidIrqHandlers σ' := by
  intro p cref irq hc
  rcases hk irq ⟨p, cref, hc⟩ with e | ⟨hn, m⟩
  · exact e
  · exact m (h.active hn)

/-- `HK` of every outcome. -/
def HKM {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → HK σ x.2

theorem hkm_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : HKM m)
    (hf : ∀ a, HKM (f a)) : HKM (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem ValidIrqHandlers.hkm {α : Type} {m : NonDet (State Unit) α} (hm : HKM m) {σ : State Unit}
    (h : ValidIrqHandlers σ) : ∀ x ∈ (m σ).1, ValidIrqHandlers x.2 := fun x hx => h.hk (hm σ x hx)

/-! ## Leaves -/

theorem hk_of_kheap_is {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap)
    (hi : σ'.interruptStates = σ.interruptStates) : HK σ σ' := by
  intro irq h
  refine Or.inr ⟨?_, fun e => by rw [hi]; exact e⟩
  obtain ⟨p, cref, hc⟩ := h
  exact ⟨p, cref, by rw [← hk]; exact hc⟩

/-- An object's caps after `set_cap` at index `r` (SpecGlob's `capOpt_cnode_set`). -/
theorem vih_capOpt_cnode_set {sz : Nat} {cs : CnodeContents} {r : CnodeIndex} (c : Cap)
    (hc : r ∈ dom cs ∧ wellFormedCnodeN sz cs) (cref : CnodeIndex) :
    capOpt (some (.cnode sz (Function.update cs r (some c)))) cref =
      Function.update (capOpt (some (.cnode sz cs))) r (some c) cref := by
  have hw' : wellFormedCnodeN sz (Function.update cs r (some c)) := by
    unfold wellFormedCnodeN at hc ⊢
    rw [← hc.2]
    ext y
    simp only [dom, Set.mem_ofPred_eq, Function.update_apply]
    by_cases e : y = r
    · subst e; simp only [if_true]; exact ⟨fun _ => hc.1, fun _ => by simp⟩
    · simp only [e, if_false]
  have e1 : capOpt (some (.cnode sz (Function.update cs r (some c)))) = Function.update cs r (some c) := by
    funext x; simp only [capOpt, if_pos hw']
  have e2 : capOpt (some (.cnode sz cs)) = cs := by
    funext x; simp only [capOpt, if_pos hc.2]
  rw [e1, e2]

theorem vih_capOpt_tcb_set (t : Tcb) {i : Nat} (hi : i < tcbSlots) (c : Cap) (cref : CnodeIndex) :
    capOpt (some (.tcb (tcbSet t i c))) cref = Function.update (capOpt (some (.tcb t))) (tcbCnodeIndex i) (some c) cref := by
  have e1 : capOpt (some (.tcb (tcbSet t i c))) = tcbCnodeMap (tcbSet t i c) := by funext x; rfl
  have e2 : capOpt (some (.tcb t)) = tcbCnodeMap t := by funext x; rfl
  rw [e1, e2, tcbCnodeMap_set t hi c]

/-- **The caps after `set_cap`** (SpecGlob's `setCap_capOpt`, outside the `JAtZ`
cone), and `interruptStates` kept. -/
theorem vih_setCap_out {c : Cap} {o : ObjRef} {r : CnodeIndex} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setCap (Z := Unit) c (o, r) σ).1) :
    x.2.interruptStates = σ.interruptStates ∧
    ∀ p cref a, capOpt (x.2.kheap p) cref = some a →
      (p = o ∧ cref = r ∧ a = c) ∨ ((p ≠ o ∨ cref ≠ r) ∧ capOpt (σ.kheap p) cref = some a) := by
  unfold setCap at hx
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  have key : ∀ k', (∀ cref, capOpt (some k') cref = Function.update (capOpt (some k)) r (some c) cref) →
      x ∈ (setObject (Z := Unit) o k' σ).1 → x.2.interruptStates = σ.interruptStates ∧
      ∀ p cref a, capOpt (x.2.kheap p) cref = some a →
      (p = o ∧ cref = r ∧ a = c) ∨ ((p ≠ o ∨ cref ≠ r) ∧ capOpt (σ.kheap p) cref = some a) := by
    intro k' hk' hx'
    rw [Ipc.setObject_out hx']
    refine ⟨rfl, fun p cref a h => ?_⟩
    by_cases hp : p = o
    · subst hp
      simp only [Function.update_self] at h
      rw [hk'] at h
      by_cases hr : cref = r
      · subst hr; rw [Function.update_self] at h
        exact Or.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩
      · rw [Function.update_of_ne hr, ← hk] at h
        exact Or.inr ⟨Or.inr hr, h⟩
    · simp only [Function.update_of_ne hp] at h
      exact Or.inr ⟨Or.inl hp, h⟩
  have pb : ∀ o', x ∈ ((pure o' >>= fun obj' => setObject (Z := Unit) o obj') σ).1 →
      x ∈ (setObject (Z := Unit) o o' σ).1 := by
    intro o' hx'; obtain ⟨z, hz, hx'⟩ := hx'; rw [Set.mem_singleton_iff.1 hz] at hx'; exact hx'
  have fb : ∀ (f : KernelObject → NonDet (State Unit) Unit), x ∈ ((NonDet.fail >>= f) σ).1 → False := by
    intro f hx'; obtain ⟨z, hz, -⟩ := hx'; exact hz
  cases k with
  | cnode sz cs =>
    dsimp only at hx
    split at hx
    · rename_i hc
      exact key _ (vih_capOpt_cnode_set c hc) (pb _ hx)
    · exact (fb _ hx).elim
  | tcb t =>
    dsimp only at hx
    repeat' split at hx
    all_goals first
      | exact (fb _ hx).elim
      | (rename_i h; subst h
         first
          | exact key _ (vih_capOpt_tcb_set t (i := 0) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 1) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 2) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 3) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 4) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 5) (by decide) c) (pb _ hx))
  | _ => dsimp only at hx; exact (fb _ hx).elim

/-- **`set_cap` as an `HK` step**: the written cap is not a handler cap, or
names a line already named in the state or not inactive. -/
theorem hk_setCap {c : Cap} (sl : CslotPtr) {σ : State Unit}
    (hc : ∀ irq, c = .irqHandlerCap irq → HIrq σ irq ∨ σ.interruptStates irq ≠ .irqInactive) :
    ∀ x ∈ (setCap (Z := Unit) c sl σ).1, HK σ x.2 := by
  obtain ⟨o, r⟩ := sl
  intro x hx irq ⟨p, cref, h⟩
  obtain ⟨hi, hcaps⟩ := vih_setCap_out hx
  rw [hi]
  rcases hcaps p cref _ h with ⟨-, -, e⟩ | h0
  · rcases hc irq e.symm with hn | ha
    · exact Or.inr ⟨hn, id⟩
    · exact Or.inl ha
  · exact Or.inr ⟨⟨p, cref, h0.2⟩, id⟩

/-- `set_cap` of a cap read from a slot of the same state (copy, move, mint of
a handler cap: `derive_cap` / `update_cap_data` keep it). -/
theorem hk_setCap_named {c : Cap} (sl : CslotPtr) {σ : State Unit} {p0 : ObjRef} {r0 : CnodeIndex}
    (h0 : capOpt (σ.kheap p0) r0 = some c) : ∀ x ∈ (setCap (Z := Unit) c sl σ).1, HK σ x.2 :=
  hk_setCap sl fun irq e => Or.inl ⟨p0, r0, e ▸ h0⟩

/-- `set_cap` of a handler cap for a line that is not inactive (the IRQ control
issue, after its `set_irq_state IRQSignal`). -/
theorem hk_setCap_active {irq : Irq} (sl : CslotPtr) {σ : State Unit}
    (h : σ.interruptStates irq ≠ .irqInactive) : ∀ x ∈ (setCap (Z := Unit) (.irqHandlerCap irq) sl σ).1, HK σ x.2 :=
  hk_setCap sl fun _ e => by cases e; exact Or.inr h

/-- The outcome of `set_irq_state`. -/
theorem setIrqState_out {st : IrqState} {i : Irq} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setIrqState (Z := Unit) st i σ).1) :
    x.2.kheap = σ.kheap ∧ x.2.interruptStates = Function.update σ.interruptStates i st := by
  unfold setIrqState at hx
  rw [SInvV.sv_bind_modify] at hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨-, e2⟩ := h2
  dsimp only at e2
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨rfl, rfl⟩

theorem hk_setIrqState_active {st : IrqState} (hst : st ≠ .irqInactive) (i : Irq) :
    HKM (setIrqState (Z := Unit) st i) := by
  intro σ x hx irq hn
  obtain ⟨hk, hi⟩ := setIrqState_out hx
  rw [hi]
  by_cases e : irq = i
  · subst e; left; rw [Function.update_self]; exact hst
  · right
    obtain ⟨p, cref, hc⟩ := hn
    exact ⟨⟨p, cref, by rw [← hk]; exact hc⟩, fun h => by rw [Function.update_of_ne e]; exact h⟩

/-- `set_irq_state IRQInactive` of a line no slot names (`deleted_irq_handler`
after the final handler cap's slot was emptied). -/
theorem hk_setIrqState_inactive {i : Irq} {σ : State Unit} (hn : ¬ HIrq σ i) :
    ∀ x ∈ (setIrqState (Z := Unit) .irqInactive i σ).1, HK σ x.2 := by
  intro x hx irq hn'
  obtain ⟨hk, hi⟩ := setIrqState_out hx
  have hn0 : HIrq σ irq := by obtain ⟨p, cref, hc⟩ := hn'; exact ⟨p, cref, by rw [← hk]; exact hc⟩
  have e : irq ≠ i := fun e => hn (e ▸ hn0)
  right
  rw [hi]
  exact ⟨hn0, fun h => by rw [Function.update_of_ne e]; exact h⟩

/-- **A final handler cap is the only cap naming its line** (`is_final_cap'`
over `gen_obj_refs`, which holds the IRQ reference of a handler cap). -/
theorem final_handler_unique {σ : State Unit} {irq : Irq} {sl : CslotPtr}
    (hf : isFinalCap' (Z := Unit) (.irqHandlerCap irq) σ)
    (hs : capOpt (σ.kheap sl.1) sl.2 = some (.irqHandlerCap irq)) :
    ∀ p cref, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → (p, cref) = sl := by
  obtain ⟨c0, hc0⟩ := hf
  have h1 : GenObjRef.iRQRef irq ∈ genObjRefs (.irqHandlerCap irq) := Or.inl (Or.inr ⟨irq, rfl, rfl⟩)
  have mem : ∀ p cref, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) →
      (p, cref) ∈ {cref | ∃ cap', ((getCap cref : SMonad Unit Cap) σ).1 = {(cap', σ)} ∧
        genObjRefs (.irqHandlerCap irq) ∩ genObjRefs cap' ≠ ∅} := by
    intro p cref h
    refine ⟨_, (getCap_set_iff σ p cref _).2 h, fun e => ?_⟩
    have : GenObjRef.iRQRef irq ∈ genObjRefs (.irqHandlerCap irq) ∩ genObjRefs (.irqHandlerCap irq) := ⟨h1, h1⟩
    rw [e] at this; exact this
  intro p cref h
  have m1 := mem p cref h
  have m2 := mem sl.1 sl.2 hs
  rw [hc0] at m1 m2
  rw [Set.mem_singleton_iff.1 m1]
  exact (Set.mem_singleton_iff.1 m2).symm

/-- After `set_cap NullCap` over the only slot naming `irq`, no slot names it
(`empty_slot`'s write before `post_cap_deletion`'s `deleted_irq_handler`). -/
theorem setCap_null_unique {σ : State Unit} {x : Unit × State Unit} {irq : Irq} {sl : CslotPtr}
    (hu : ∀ p cref, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → (p, cref) = sl)
    (hx : x ∈ (setCap (Z := Unit) .nullCap sl σ).1) : ¬ HIrq x.2 irq := by
  obtain ⟨o, r⟩ := sl
  rintro ⟨p, cref, h⟩
  rcases (vih_setCap_out hx).2 p cref _ h with ⟨-, -, e⟩ | ⟨hne, h0⟩
  · cases e
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (hu p cref h0)
    rcases hne with e | e
    · exact e e1
    · exact e e2

/-! ## The IRQ ack -/

/-- **The ack keeps `ValidIrqMasks` when its line is not inactive.** -/
theorem vim_ack {irq : Irq} {σ : State Unit} (h : SInvV.ValidIrqMasks σ)
    (ha : σ.interruptStates irq ≠ .irqInactive) :
    ∀ x ∈ (doMachineOp (Z := Unit) (maskInterrupt false irq) σ).1, SInvV.ValidIrqMasks x.2 := by
  intro x hx j hj
  obtain ⟨e1, e2⟩ := SInvV.dmo_mask_out false irq hx
  rw [e2] at hj; rw [e1]
  by_cases e : j = irq
  · subst e; exact absurd hj ha
  · rw [Function.update_of_ne e]; exact h j hj

/-- The ack keeps the heap and `interruptStates`. -/
theorem hkm_ack (irq : Irq) : HKM (doMachineOp (Z := Unit) (maskInterrupt false irq)) := by
  intro σ x hx
  have e : maskInterrupt false irq σ.machineState =
      ({((), { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks irq false })}, False) := rfl
  rw [SInvV.dmo_single e] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hk_of_kheap_is rfl rfl

/-- **The ack with the invoked handler cap in a slot** (module docstring): from
`ValidIrqMasks ∧ ValidIrqHandlers`, both are kept. -/
theorem vimh_ack {irq : Irq} {σ : State Unit} (hm : SInvV.ValidIrqMasks σ) (hh : ValidIrqHandlers σ)
    (hn : HIrq σ irq) :
    ∀ x ∈ (doMachineOp (Z := Unit) (maskInterrupt false irq) σ).1,
      SInvV.ValidIrqMasks x.2 ∧ ValidIrqHandlers x.2 :=
  fun x hx => ⟨vim_ack hm (hh.active hn) x hx, hh.hk (hkm_ack irq σ x hx)⟩

/-! ## Boot -/

/-- **`ValidIrqHandlers` at boot**: `initKheap` holds no handler cap (the IRQ node's
empty CNodes and the idle thread's null slots). -/
theorem boot_vih : ValidIrqHandlers (initASt (Z := Unit)) := by
  intro p cref irq hc
  exfalso
  simp only [initASt, initKheap, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)

end

end Fl4Proofs.P3.SInvV
