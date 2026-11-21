/-
P3 (DESIGN.md §9), invariant line G1 (rd8k): **`Sched.BlockedScActive`
across retype / detype** (spec side only, outside the JAtZ cone; KENTRY-PLAN
rd8i handoff 4).

`BlockedScActive` reads only TCBs (ipc-queued or not) and SCs (bound TCB,
reply stack, active): removing objects only drops hypotheses (`bsa_detype`),
and the fresh objects of a retype — an Inactive TCB, an SC with no bound TCB
and an empty reply stack, or any other kind — satisfy it wherever they are
written (`bsa_fresh`). So every lemma here is hypothesis-free.

* `bsa_fresh`, `bsa_detype`, `fresh_default`, `bsa_foldr`.
* **`ba_retypeRegionWith`**, **`ba_retypeRegion`**, **`ba_deleteObjects`**
  (leaves of the generated family), then `ba_resetUntypedCap`,
  **`ba_invokeUntypedWith`**, **`ba_fl4InvokeUntyped`**,
  **`ba_performAsidControlInvocation`** by `ba_auto`.
-/
import Fl4Proofs.P3.SpecInvRd8iD
open Classical

namespace Fl4Proofs.P3.SInvR.B8k
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8g

noncomputable section

set_option maxHeartbeats 1000000

/-- What a fresh object may be. -/
def Fresh (o : KernelObject) : Prop :=
  (∀ y, o = .tcb y → ipcQueuedThreadState y.tcbState = false) ∧
  (∀ y n, o = .schedContext y n → y.scTcb = none ∧ y.scReplies = [])

/-- **A fresh object written anywhere keeps `BlockedScActive`.** -/
theorem bsa_fresh {σ : State Unit} (h : BSA σ) (p : ObjRef) (o : KernelObject) (ho : Fresh o) :
    BSA { σ with kheap := Function.update σ.kheap p (some o) } := by
  constructor
  · intro q y n t x hq hy ht hst
    change Function.update σ.kheap p (some o) q = _ at hq
    change Function.update σ.kheap p (some o) t = _ at ht
    by_cases eq : q = p
    · subst eq; rw [Function.update_self] at hq
      rw [(ho.2 y n (Option.some.inj hq)).1] at hy; cases hy
    · rw [Function.update_of_ne eq] at hq
      by_cases et : t = p
      · subst et; rw [Function.update_self] at ht
        rw [ho.1 x (Option.some.inj ht)] at hst; cases hst
      · rw [Function.update_of_ne et] at ht; exact h.tcb q y n t x hq hy ht hst
  · intro q y n hq hr
    change Function.update σ.kheap p (some o) q = _ at hq
    by_cases eq : q = p
    · subst eq; rw [Function.update_self] at hq
      exact absurd (ho.2 y n (Option.some.inj hq)).2 hr
    · rw [Function.update_of_ne eq] at hq; exact h.replies q y n hq hr

/-- **Removing objects keeps `BlockedScActive`.** -/
theorem bsa_detype {σ : State Unit} (h : BSA σ) (S : Set ObjRef) : BSA (detype S σ) := by
  constructor
  · intro q y n t x hq hy ht hst
    change (if q ∈ S then none else σ.kheap q) = _ at hq
    change (if t ∈ S then none else σ.kheap t) = _ at ht
    split_ifs at hq ht
    exact h.tcb q y n t x hq hy ht hst
  · intro q y n hq hr
    change (if q ∈ S then none else σ.kheap q) = _ at hq
    split_ifs at hq
    exact h.replies q y n hq hr

theorem fresh_default {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain) :
    Fresh (defaultObject ty dev n d) := by
  cases ty
  case untyped => exact absurd rfl hty
  all_goals
    refine ⟨fun y h => ?_, fun y m h => ?_⟩ <;> simp only [defaultObject] at h <;>
      first | (cases h; done) | (cases h; rfl) | (cases h; exact ⟨rfl, rfl⟩) | (subst h; rfl) | (obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl⟩) | (subst h; exact ⟨rfl, rfl⟩)

theorem bsa_foldr (σ : State Unit) (o : KernelObject) (ho : Fresh o) :
    ∀ (l : List ObjRef) (kh : ObjRef → Option KernelObject), BSA { σ with kheap := kh } →
      BSA { σ with kheap := l.foldr (fun p kh => Function.update kh p (some o)) kh }
  | [], kh, h => h
  | p :: l, kh, h => by
    rw [List.foldr_cons]
    exact bsa_kh (bsa_fresh (bsa_foldr σ o ho l kh h) p o ho) rfl

theorem ba_retypeRegionWith (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (num oBits : Nat)
    (ty : ApiObjectType) (dev : Bool) : BAK (retypeRegionWith (Z := Unit) bitsApi ptr num oBits ty dev) := by
  intro σ hσ y hy
  unfold retypeRegionWith at hy
  simp only [Notif.nd_pure_bind'] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hy
  unfold NonDet.when at hz
  split at hz
  · rename_i hty
    simp only [Notif.nd_gets_bind, Notif.nd_pure_bind'] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact bsa_kh (bsa_foldr σ _ (fresh_default hty dev oBits σ.curDomain) _ σ.kheap (bsa_kh hσ rfl)) rfl
  · rw [Set.mem_singleton_iff.1 hz]; exact hσ
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_retypeRegionWith _ _ _ _ _ _)

theorem ba_retypeRegion (ptr : ObjRef) (num oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    BAK (retypeRegion (Z := Unit) ptr num oBits ty dev) :=
  ba_retypeRegionWith objBitsApi ptr num oBits ty dev
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_retypeRegion _ _ _ _ _)

theorem ba_deleteObjects (ptr : Word) (bits : Nat) : BAK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => bsa_kh h rfl) _) fun _ => ik_modify fun _ h => bsa_detype h _
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_deleteObjects _ _)

theorem ba_resetUntypedCap (sl : CslotPtr) : BAKE (resetUntypedCap (Z := Unit) sl) := by
  unfold resetUntypedCap; ba_auto
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_resetUntypedCap _)

theorem ba_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) :
    BAKE (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  cases ui; simp only [invokeUntypedWith]; ba_auto

theorem ba_fl4InvokeUntyped (ui : UntypedInvocation) : BAKE (fl4InvokeUntyped (Z := Unit) ui) :=
  ba_invokeUntypedWith _ ui

theorem ba_performAsidControlInvocation (iv : AsidControlInvocation) :
    BAK (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv; simp only [performAsidControlInvocation]; ba_auto

end

end Fl4Proofs.P3.SInvR.B8k
