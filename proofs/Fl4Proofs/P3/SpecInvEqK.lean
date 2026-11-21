/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq1): **the frame kit of
`RPos`** (spec side only, outside the `JAtZ` cone).

`RPos` reads the heap only through the SC objects' refills, period and refill
max. The only SC writer below the refill code is `update_sched_context`
(`set_sched_context` has no other caller), so:

* `pz_setObject` (no SC written), `pz_updateSchedContext` (refills, period and
  refill max kept), `pz_setSimpleKo` (`a_type` of an endpoint / notification /
  reply), the TCB / CNode writers, `retype_region` (the default SC has refill
  max 0, so it is inactive), `delete_objects` (removes objects);
* the generated family `PZK := IK RPos` (SpecInvEqG1..G6) uses `pz_auto`; the
  refill writers are proved by hand (SpecInvEqB).
-/
import Fl4Proofs.P3.SpecInvEqA
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

abbrev PZK {α : Type} (m : NonDet (State Unit) α) : Prop := IK RPos m
abbrev PZKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE RPos m

/-! ## The frame -/

theorem rpos_update {σ : State Unit} (h : RPos σ) (p : ObjRef) (o : KernelObject)
    (ho : ∀ y n, o = .schedContext y n → RPosS y) :
    RPos { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro q y n hq
  dsimp only at hq
  rw [Function.update_apply] at hq
  split_ifs at hq with e
  · exact ho y n (Option.some.inj hq)
  · exact h q y n hq

/-- `RPos` across a heap change creating no SC and changing none, except into
one with the same refills, period and refill max. -/
theorem rpos_of_heap {σ σ' : State Unit} (h : RPos σ)
    (hk : ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y' n', σ.kheap p = some (.schedContext y' n') ∧
      y.scRefills = y'.scRefills ∧ y.scPeriod = y'.scPeriod ∧ y.scRefillMax = y'.scRefillMax) : RPos σ' := by
  intro p y n hp
  obtain ⟨y', n', hp', e1, e2, e3⟩ := hk p y n hp
  intro ha hpe
  have ha' : scActive y' = true := by rw [← ha]; simp only [scActive, e3]
  obtain ⟨h1, h2⟩ := h p y' n' hp' ha' (by rw [← e2]; exact hpe)
  rw [e1]; exact ⟨h1, h2⟩

theorem rpos_kheap {σ σ' : State Unit} (h : RPos σ) (hk : σ'.kheap = σ.kheap) : RPos σ' := by
  intro p y n hp; rw [hk] at hp; exact h p y n hp

/-- `setObject` writing an object that is no SC or an SC satisfying `RPosS`. -/
theorem pz_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : RPos σ → ∀ y n, o = .schedContext y n → RPosS y) : IKp RPos σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨y1, y2⟩ := y
  have e2 : y2 = σ := (mem_getObject hy).2
  subst e2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact rpos_update hσ p o (ho hσ)

theorem pz_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ y n, o ≠ .schedContext y n) :
    PZK (setObject (Z := Unit) p o) :=
  fun σ => pz_setObject_p p o σ fun _ y n e => absurd e (ho y n)

/-- `update_sched_context` with an update keeping `RPosS`. -/
theorem pz_updateSchedContext_g (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, RPosS y → RPosS (f y)) : PZK (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  dsimp only at hx
  split at hx
  · rename_i sc n
    refine pz_setObject_p _ _ _ (fun _ y' n' e => ?_) hσ x hx
    cases e; exact hf sc (hσ p sc n hk)
  · exact hx.elim

theorem rposS_congr {y : SchedContext} (z : SchedContext) (e1 : z.scRefills = y.scRefills)
    (e2 : z.scPeriod = y.scPeriod) (e3 : z.scRefillMax = y.scRefillMax) (h : RPosS y) : RPosS z := by
  intro ha hp
  have ha' : scActive y = true := by rw [← ha]; simp only [scActive, e3]
  rw [e1]; exact h ha' (by rw [← e2]; exact hp)

theorem pz_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scPeriod = y.scPeriod ∧ (f y).scRefillMax = y.scRefillMax) :
    PZK (updateSchedContext (Z := Unit) p f) :=
  pz_updateSchedContext_g p f fun y h => rposS_congr (f y) (hf y).1 (hf y).2.1 (hf y).2.2 h

theorem pz_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    PZK (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hk3, hs3⟩ := mem_getObject hy3
  obtain ⟨obj', y3⟩ := y3
  simp only at hk3 hs3 hsimp; subst hs3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine rpos_update hσ p _ fun y n ht => ?_
  exfalso
  rw [ht] at hty
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  rcases hsimp with h | h | h <;> rw [h] at hty <;> simp only [aType] at hty <;> split_ifs at hty <;> cases hty

macro "pz_side" : tactic => `(tactic| first
  | (intro _ _ h; cases h; done)
  | (intro _; exact ⟨rfl, rfl, rfl⟩)
  | (intro _ _ h; exact h)
  | (intro _ h; exact h)
  | trivial)

macro "pz0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); pz_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); pz_side)
  | with_reducible exact ik_getObject _
  | ((with_reducible refine pz_setObject _ _ ?_); pz_side)
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem pz_threadSet (f : Tcb → Tcb) (t : ObjRef) : PZK (threadSet (Z := Unit) f t) := by
  unfold threadSet; pz0_auto

theorem pz_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : PZK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; pz0_auto

theorem pz_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : PZK (asUser (Z := Unit) t u) := by
  unfold asUser; pz0_auto

theorem pz_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : PZK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; pz0_auto

theorem pz_setCap (c : Cap) (sl : CslotPtr) : PZK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hS : ∀ o', (∀ y n, o' ≠ .schedContext y n) → IKp RPos σ (setObject (Z := Unit) o o') :=
    fun o' h => pz_setObject_p _ _ σ fun _ y n e => absurd e (h y n)
  split
  · split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    · exact ikp_fail_bind
  · split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    split
    · exact ikp_pure_bind (hS _ fun _ _ e => by cases e)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

/-- New objects of `retype_region`: an SC among them is inactive. -/
theorem rposS_default (ty : ApiObjectType) (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain) :
    ∀ y m, defaultObject ty dev n d = .schedContext y m → RPosS y := by
  intro y m h ha
  cases ty with
  | untyped => exact absurd rfl hty
  | schedContextObject =>
    simp only [defaultObject] at h; cases h
    simp [scActive, activeSc, defaultSchedContext] at ha
  | _ => simp only [defaultObject] at h <;> cases h

theorem rpos_foldr (ps : List ObjRef) (o : KernelObject) (ho : ∀ y n, o = .schedContext y n → RPosS y)
    (kh : ObjRef → Option KernelObject) (h : ∀ p y n, kh p = some (.schedContext y n) → RPosS y) :
    ∀ p y n, (ps.foldr (fun p kh => Function.update kh p (some o)) kh) p = some (.schedContext y n) → RPosS y := by
  induction ps with
  | nil => exact h
  | cons a ps ih =>
    intro p y n hp
    simp only [List.foldr_cons, Function.update_apply] at hp
    split_ifs at hp with e
    · exact ho y n (Option.some.inj hp)
    · exact ih p y n hp

theorem pz_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType)
    (dev : Bool) : PZK (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith
  refine ik_bind (ik_pure _) fun _ => ik_bind (ik_pure _) fun ptrs => ik_bind ?_ fun _ => ik_pure _
  unfold NonDet.when
  split
  · rename_i hty
    refine ik_gets_bind fun σ => ikp_gets_bind (ikp_pure_bind (ikp_modify fun hσ => ?_))
    exact rpos_foldr _ _ (rposS_default ty hty dev oBits _) _ hσ
  · exact ik_pure' _

theorem pz_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    PZK (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact pz_retypeRegionWith _ _ _ _ _ _

theorem pz_deleteObjects (ptr : Word) (bits : Nat) : PZK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ => ik_modify fun σ h => ?_
  intro p y n hp
  unfold detype at hp
  dsimp only at hp
  split_ifs at hp
  exact h p y n hp

theorem pz_setThreadState (t : ObjRef) (ts : ThreadState) : PZK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (pz_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; pz0_auto

theorem pz_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    PZK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact pz_threadSet _ _

syntax "pz_leaf" : tactic
macro_rules | `(tactic| pz_leaf) => `(tactic| fail "no pz_leaf")

macro "pz_auto" : tactic => `(tactic| repeat' (first | pz_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| pz_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); pz_side))
macro_rules | `(tactic| pz_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); pz_side))
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| pz_leaf) => `(tactic| ((with_reducible refine pz_setObject _ _ ?_); pz_side))
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setSimpleKo _ _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_threadSet _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archThreadSet _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_asUser _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setMrs _ _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setCap _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_deleteObjects _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setThreadState _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_optionUpdateThread _ _ _)
macro_rules | `(tactic| pz_leaf) => `(tactic| ((with_reducible refine pz_updateSchedContext _ _ ?_); pz_side))

end

end Fl4Proofs.P3.SInvE
