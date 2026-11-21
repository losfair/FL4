/-
P3 (DESIGN.md §9), invariant line G1 (sb2): **the decode-free gap performs of
`ScInv`** (spec side only; imports SpecInvSbG6).

* `SN p s := ScInv s ∧ NE p s.kheap` (the SC at `p` has refills), kept by every
  `SBK` frame (`ik_sn_of_sbk`) and by an SC update keeping the TCB and the
  refills (`ik_sn_upd`); `refill_new` / `refill_update` establish it
  (`hk_sn_refillNew`, `hk_sn_refillUpdate`, sb1's RO/RN argument).
* **`si_invokeSchedControlConfigureFlags`** (no premise): the `sc_sporadic`
  write after `refill_new` / `refill_update` finds refills (l4v
  `invoke_sched_control_configure_flags_invs`).
* **`sbp_capDelete_fh`**: `cap_delete` of a slot holding a null or endpoint cap
  (a valid fault handler, `validFaultHandler`) keeps the binding frame `BR`
  (`rec_del` once: `finalise_cap` of an endpoint cap is `cancel_all_ipc`, its
  remainder the null cap; no Zombie is reduced). Used by `install_tcb_cap` of
  the fault-handler slot in `threadControlSched`.
-/
import Fl4Proofs.P3.SpecInvSbG6
import Fl4Proofs.P3.SpecInvUtN5
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `ScInv` with refills at one SC -/

/-- `ScInv` and the SC at `p` (if any) has refills. -/
def SN (p : ObjRef) (s : State Unit) : Prop := ScInv s ∧ NE p s.kheap

theorem ne_of_br {p : ObjRef} {k k' : KHeap} (hb : BR k k') (h : NE p k) : NE p k' := by
  intro y n hy
  obtain ⟨y0, n0, hy0⟩ := hb.sc' p y n hy
  obtain ⟨y1, n1, hy1, -, k2, -⟩ := hb.sc p y0 n0 hy0
  rw [hy] at hy1
  simp only [Option.some.injEq, KernelObject.schedContext.injEq] at hy1
  obtain ⟨rfl, rfl⟩ := hy1
  exact k2 (h y0 n0 hy0)

theorem ik_sn_of_sbk {p : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : ∀ h0, SBK h0 m) : IK (SN p) m :=
  fun _ hσ _ hx => ⟨scInv_of_br hσ.1 (br_mem_of_sbk h hx), ne_of_br (br_mem_of_sbk h hx) hσ.2⟩

theorem ik_sn_upd {p : ObjRef} {f : SchedContext → SchedContext} (h1 : ∀ y, (f y).scTcb = y.scTcb)
    (h2 : ∀ y, (f y).scRefills = y.scRefills) : IK (SN p) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, hk, e⟩ := mem_updateSchedContext hx
  have hk' : ObjKeep (σ.kheap p) (.schedContext (f y) n) := by
    rw [hk]; exact objKeep_sc (scKeep_ne (h1 y) (by rw [h2 y]; exact hσ.2 y n hk))
  have hb : BR σ.kheap x.2.kheap := by rw [e]; exact br_update hk'
  exact ⟨scInv_of_br hσ.1 hb, ne_of_br hb hσ.2⟩

theorem hk_sn_of_rn {p : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : ∀ k, HK (ROs p k) (RN p k) m) :
    HK ScInv (SN p) m := fun σ hσ x hx => by
  have hr := h σ.kheap σ (RO.refl _ _) x hx
  exact ⟨scInv_of_br hσ (br_of_ro_ne hr.1 hr.2), hr.2⟩

theorem hk_rn_refillNew (p : ObjRef) (mr : Nat) (budget period : Ticks) (k : KHeap) :
    HK (ROs p k) (RN p k) (refillNew (Z := Unit) p mr budget period) := by
  unfold refillNew
  refine hk_bind (hk_of_ik (ik_gets _)) fun ct => ?_
  refine hk_bind (hk_of_ik (ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_pure _)) fun _ => ?_
  exact hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ =>
    hk_of_ik (ik_rn_maybeAddEmptyTail p k)

theorem hk_rn_refillUpdate (p : ObjRef) (np nb : Ticks) (nm : Nat) (k : KHeap) :
    HK (ROs p k) (RN p k) (refillUpdate (Z := Unit) p np nb nm) := by
  unfold refillUpdate
  refine hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ => hk_of_ik ?_
  refine ik_bind (ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (by unfold getScRefillReady; rd_auto) fun _ => ?_
  refine ik_bind ?_ fun _ => ?_
  · unfold NonDet.when
    split
    · refine ik_bind (ik_gets _) fun _ => ?_
      unfold updateRefillHd
      exact ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _)
    · exact ik_pure _
  refine ik_bind (by unfold getRefillHead; rd_auto) fun _ => ?_
  split
  · unfold updateRefillHd
    exact ik_bind (ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _)) fun _ =>
      ik_rn_maybeAddEmptyTail p k
  · refine ik_pure_bind (ik_pure_bind ?_)
    unfold refillAddTail
    exact ik_rn_upd (fun _ => rfl) (fun _ _ => by simp [scRefillsUpdate])

/-- The shared tail of the configure (after the refill write). -/
macro "cfg_tail" : tactic => `(tactic| (
  refine hk_bind (hk_of_ik (ik_sn_of_sbk fun _ => by sb_auto)) fun _ => ?_;
  refine hk_bind (hk_of_ik (ik_sn_of_sbk fun _ => by sb_auto)) fun _ => ?_;
  exact hk_mono (hk_of_ik (ik_sn_upd (fun _ => rfl) (fun _ => rfl))) fun _ h => h.1))

set_option maxHeartbeats 4000000 in
/-- **SchedControl configure keeps `ScInv`** (no premise). -/
theorem si_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) :
    SIK (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  cases iv with
  | invokeSchedControlConfigureFlags scPtr budget period mrefills badge flag =>
  unfold invokeSchedControlConfigureFlags
  refine ik_bind (sik_of_sbk fun _ => by sb_auto) fun sc => ?_
  refine ik_bind (sik_of_sbk fun _ => by sb_auto) fun _ => ?_
  show HK ScInv ScInv _
  (try dsimp only)
  split
  · exact hk_bind (hk_sn_of_rn (hk_rn_refillNew _ _ _ _)) fun _ => by cfg_tail
  · refine hk_bind (hk_of_ik (sik_of_sbk fun _ => by sb_auto)) fun active => ?_
    split
    · refine hk_bind (hk_of_ik (sik_of_sbk fun _ => by sb_auto)) fun tcbPtr => ?_
      refine hk_bind (hk_of_ik (sik_of_sbk fun _ => by sb_auto)) fun st => ?_
      split
      · exact hk_bind (hk_sn_of_rn (hk_rn_refillUpdate _ _ _ _)) fun _ => by cfg_tail
      · exact hk_bind (hk_sn_of_rn (hk_rn_refillNew _ _ _ _)) fun _ => by cfg_tail
    · exact hk_bind (hk_sn_of_rn (hk_rn_refillNew _ _ _ _)) fun _ => by cfg_tail

macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_invokeSchedControlConfigureFlags _)

/-! ## `cap_delete` of a fault-handler slot -/

/-- A null or endpoint cap (`validFaultHandler`'s caps). -/
def FhC (c : Cap) : Prop := c = .nullCap ∨ ∃ r b rs, c = .endpointCap r b rs

theorem fhC_of_valid {c : Cap} (h : validFaultHandler c) : FhC c := by
  rcases h with ⟨he, -⟩ | h
  · cases c <;> simp_all [isEpCap, FhC]
  · exact Or.inl h.symm

def FPre (h0 : KHeap) : RecDelCall → State Unit → Prop
  | .cTEDeleteCall s _, σ => BR h0 σ.kheap ∧ ∀ c, SInvU.capAt σ s = some c → FhC c
  | .finaliseSlotCall s _, σ => BR h0 σ.kheap ∧ ∀ c, SInvU.capAt σ s = some c → FhC c
  | .reduceZombieCall _ _ _, _ => False

def FPost (h0 : KHeap) : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | _, _, σ => BR h0 σ.kheap

theorem fh_step (h0 : KHeap) (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, SInvU.HR (FPre h0 k) (FPost h0 k) (f k)) (k : RecDelCall) :
    SInvU.HR (FPre h0 k) (FPost h0 k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hp : BR h0 z.2.kheap := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      try dsimp only at hy
      obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2
        rw [SInvU.mem_ret_ok hy]
        show BR h0 x.2.kheap
        exact (ik_when _ (sb_emptySlot (h0 := h0) _ _)) z.2 hp x hx
      · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2
        rw [hx] at her; cases her
    · exact hrec (.finaliseSlotCall s e) σ hσ z hz
  | finaliseSlotCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := SInvU.mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := SInvU.getCap_capAt hx
    simp only at e1 hc
    subst e1
    have hfc := hσ.2 cap hc
    try dsimp only at hy1
    split at hy1
    · rw [SInvU.mem_ret_ok hy1]; exact hσ.1
    · rename_i hnn
      obtain ⟨r, b, rs, rfl⟩ : ∃ r b rs, cap = .endpointCap r b rs := hfc.resolve_left hnn
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      have hb2 : BR h0 σ2.kheap := sb_isFinalCap (h0 := h0) _ _ hσ.1 _ hx2
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨⟨u, σ3'⟩, hx3', e3⟩ := hx3
      have hb3 : BR h0 σ3'.kheap := (ik_when _ (sb_cancelAllIpc (h0 := h0) _)) σ2 hb2 _ hx3'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 e3)
      try dsimp only at hy3
      rw [if_pos (show capRemoveable Cap.nullCap s from trivial)] at hy3
      rw [SInvU.mem_ret_ok hy3]; exact hb3
  | reduceZombieCall c s e => intro σ hσ; exact hσ.elim

theorem hr_recDel_fh (h0 : KHeap) (k : RecDelCall) :
    SInvU.HR (FPre h0 k) (FPost h0 k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact SInvU.hr_lfp (FPre h0) (FPost h0) (fun f hf k => fh_step h0 f hf k) k

/-- **`cap_delete` of a slot holding a null or endpoint cap keeps the binding frame.** -/
theorem sbp_capDelete_fh (sl : CslotPtr) (σ : State Unit) (hc : ∀ c, SInvU.capAt σ sl = some c → FhC c) :
    ∀ y ∈ ((capDelete (Z := Unit) sl).run σ).1, BR σ.kheap y.2.kheap := by
  intro y hy
  unfold capDelete at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨er, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · rw [SInvU.mem_ret_ok hy]
    exact hr_recDel_fh σ.kheap (.cTEDeleteCall sl true) σ ⟨BR.refl _, hc⟩ z hz
  · exact hr_recDel_fh σ.kheap (.cTEDeleteCall sl true) σ ⟨BR.refl _, hc⟩ z hz

end

end Fl4Proofs.P3.SInvB
