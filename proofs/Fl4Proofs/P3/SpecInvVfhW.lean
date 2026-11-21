/-
P3 (DESIGN.md §9), invariant line G1 (vfh1): **the CSpace writers keep
`VfhV`** (spec side only, outside the JAtZ cone; SpecInvVfhK's `VS`).

* Pinned combinators (`ikp_keep_v`, `ikp_getCap_bind`, `ikpE_getCap_bind`):
  a read's value as a fact about the current state.
* `vs_setUntypedCapAsFull_p` (the source slot holds the untyped source cap, no
  valid fault handler, so it is no fault-handler slot), `vs_capInsert` /
  `vs_capMove` (destination not `Bad` at the anchor or the cap a valid fault
  handler), `vs_capSwap`, `vs_capSwapForDelete` (both slots not `Bad`).
* The deletion path, uniform (`VK`): `vs_emptySlot` (a null write and the IRQ
  state), `vs_capDeleteOne`, `vs_deletingIrqHandler`, `vs_finaliseCap` (with
  `vfh_finaliseCap_rem`: the remainder of a valid fault handler is null),
  `vs_recDel` for the calls `rec_del` is entered with (the reduce-zombie call
  with its slot not `Bad`, true at the one call site: the slot holds the zombie
  just written; `vfh_lfp`, the pre-fixed-point argument with a call-dependent
  precondition), `vs_capDelete`, `vs_capRevoke`.
-/
import Fl4Proofs.P3.SpecInvVfhK
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Valid fault handlers -/

theorem vfh_cases {c : Cap} (h : validFaultHandler c) : c = .nullCap ∨ isEpCap c = true := by
  rcases h with ⟨h, -⟩ | h
  · exact Or.inr h
  · exact Or.inl h.symm

theorem vfh_not {c : Cap} (h1 : c ≠ .nullCap) (h2 : isEpCap c = false) : ¬ validFaultHandler c := by
  intro h; rcases vfh_cases h with h | h
  · exact h1 h
  · rw [h2] at h; cases h

theorem vfh_not_untyped {c : Cap} (h : isUntypedCap c = true) : ¬ validFaultHandler c := by
  apply vfh_not <;> cases c <;> simp_all [isUntypedCap, isEpCap]

theorem vfh_not_zombie (r : ObjRef) (b : Option Nat) (n : Nat) : ¬ validFaultHandler (.zombie r b n) :=
  vfh_not (by simp) rfl

theorem vfh_replicate_ne (k : Nat) : List.replicate k false ≠ tcbCnodeIndex 3 := by
  intro h
  have h3 : true ∈ tcbCnodeIndex 3 := by decide
  rw [← h] at h3
  exact absurd (List.eq_of_mem_replicate h3) (by decide)

/-! ## Pinned combinators -/

section Pin
variable {P : State Unit → Prop}

theorem ikp_keep_v {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    {Q : α → Prop} (hm : ∀ y, y ∈ (m σ).1 → y.2 = σ ∧ Q y.1) (hg : ∀ a, Q a → IKp P σ (g a)) :
    IKp P σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨e, hq⟩ := hm y hy
  obtain ⟨a, s⟩ := y
  simp only at e hq; subst e
  exact hg a hq hσ x hx

theorem ikp_getCap_bind {β : Type} {σ : State Unit} {sl : CslotPtr} {g : Cap → NonDet (State Unit) β}
    (hg : ∀ a, capOpt (σ.kheap sl.1) sl.2 = some a → IKp P σ (g a)) : IKp P σ (getCap (Z := Unit) sl >>= g) := by
  obtain ⟨o, r⟩ := sl
  exact ikp_keep_v (fun y hy => vih_mem_getCap hy) hg

theorem vfh_run_liftE_bind_mem {ε α β : Type} {m : NonDet (State Unit) α} {k : α → NonDetE (State Unit) ε β}
    {σ : State Unit} {y : Except ε β × State Unit} (hy : y ∈ (ExceptT.run (NonDetE.liftE m >>= k) σ).1) :
    ∃ x ∈ (m σ).1, y ∈ (ExceptT.run (k x.1) x.2).1 := by
  unfold NonDetE.liftE at hy
  rw [ExceptT.run_bind, ExceptT.run_lift] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact ⟨x, hx, hy⟩

theorem ikpE_getCap_bind {ε β : Type} {σ : State Unit} {sl : CslotPtr} {g : Cap → NonDetE (State Unit) ε β}
    (hg : ∀ a, capOpt (σ.kheap sl.1) sl.2 = some a → IKp P σ (ExceptT.run (g a))) :
    IKp P σ (ExceptT.run (NonDetE.liftE (getCap (Z := Unit) sl) >>= g)) := by
  obtain ⟨o, r⟩ := sl
  intro hσ x hx
  obtain ⟨y, hy, hx'⟩ := vfh_run_liftE_bind_mem hx
  clear hx
  obtain ⟨e, hc⟩ := vih_mem_getCap hy
  obtain ⟨a, s⟩ := y
  simp only at e hc; subst e
  exact hg a hc hσ x hx'

/-- A step from the current state to an anchored one. -/
theorem ikp_bind_v {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    {Q : α → State Unit → Prop} (hm : P σ → ∀ y ∈ (m σ).1, P y.2 ∧ Q y.1 y.2)
    (hg : ∀ a s, P s → Q a s → IKp P s (g a)) : IKp P σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨h1, h2⟩ := hm hσ y hy
  exact hg y.1 y.2 h1 h2 h1 x hx

theorem ikpE_liftE_bind_v {ε α β : Type} {σ : State Unit} {m : NonDet (State Unit) α}
    {g : α → NonDetE (State Unit) ε β} {Q : α → State Unit → Prop} (hm : P σ → ∀ y ∈ (m σ).1, P y.2 ∧ Q y.1 y.2)
    (hg : ∀ a s, P s → Q a s → IKp P s (ExceptT.run (g a))) : IKp P σ (ExceptT.run (NonDetE.liftE m >>= g)) := by
  intro hσ x hx
  obtain ⟨y, hy, hx⟩ := vfh_run_liftE_bind_mem hx
  obtain ⟨h1, h2⟩ := hm hσ y hy
  exact hg y.1 y.2 h1 h2 h1 x hx

theorem ikpE_bind {ε α β : Type} {σ : State Unit} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKp P σ (ExceptT.run m)) (hg : ∀ a, IKE P (g a)) : IKp P σ (ExceptT.run (m >>= g)) := by
  intro hσ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨⟨r, s⟩, h1, hx⟩ := hx
  have h1' := hm hσ _ h1
  cases r with
  | error e => simp only [ExceptT.bindCont] at hx; rw [Set.mem_singleton_iff.1 hx]; exact h1'
  | ok a => simp only [ExceptT.bindCont] at hx; exact hg a s h1' x hx

end Pin

/-! ## Leaves -/

theorem vfh_maxFree_nc {c : Cap} (h : isUntypedCap c = true) : ∀ p r g, maxFreeIndexUpdate c ≠ .cnodeCap p r g := by
  cases c <;> simp_all [isUntypedCap, maxFreeIndexUpdate, freeIndexUpdate]

/-- `set_untyped_cap_as_full` with the source cap in its slot. -/
theorem vs_setUntypedCapAsFull_p {σ0 σ : State Unit} {srcCap newCap : Cap} {src : CslotPtr}
    (hc : capOpt (σ.kheap src.1) src.2 = some srcCap) :
    IKp (VS σ0) σ (setUntypedCapAsFull (Z := Unit) srcCap newCap src) := by
  intro hσ x hx
  unfold setUntypedCapAsFull at hx
  split at hx
  · rename_i h
    exact hσ.trans (vfh_setCap_step hσ.1 hσ.2.2 (fun hb => absurd hb (vfh_notBad_old hσ.1 hc (vfh_not_untyped h.1)))
      (cnOk_of_nc (vfh_maxFree_nc h.1)) x hx)
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

macro "vs_tail" : tactic => `(tactic| repeat' (first
  | (with_reducible exact vs_setCdt _) | (with_reducible exact vs_updateCdt _)
  | (with_reducible exact vs_setOriginal _ _) | (with_reducible exact vs_doExtendedOp _)
  | (with_reducible exact vs_setIrqState _ _) | (with_reducible exact vs_setCap_null _)
  | hv_leaf | ik_step0 | ik_unfold))

/-- **`cap_insert`** (destination not `Bad` at the anchor, or a valid fault handler). -/
theorem vs_capInsert {σ0 : State Unit} {newCap : Cap} (src dest : CslotPtr)
    (hd : vfh_Bad σ0 dest → validFaultHandler newCap) (hk : CnOk σ0 newCap) :
    IK (VS σ0) (capInsert (Z := Unit) newCap src dest) := by
  unfold capInsert
  intro σ
  refine ikp_getCap_bind fun srcCap hsc => ?_
  refine ikp_pure_bind ?_
  refine ikp_getCap_bind fun _ _ => ?_
  refine ikp_keep (fun y hy => by rw [hy.2]) fun _ => ?_
  refine ikp_bind (vs_setUntypedCapAsFull_p hsc) fun _ => ?_
  refine ik_bind (vs_setCap hd hk) fun _ => ?_
  vs_tail

/-- **`cap_move`**. -/
theorem vs_capMove {σ0 : State Unit} {newCap : Cap} (src dest : CslotPtr)
    (hd : vfh_Bad σ0 dest → validFaultHandler newCap) (hk : CnOk σ0 newCap) :
    IK (VS σ0) (capMove (Z := Unit) newCap src dest) := by
  unfold capMove
  refine ik_bind (vs_setCap hd hk) fun _ => ?_
  vs_tail

/-- **`cap_swap`**. -/
theorem vs_capSwap {σ0 : State Unit} {c1 c2 : Cap} (s1 s2 : CslotPtr) (h1 : vfh_Bad σ0 s1 → validFaultHandler c2)
    (h2 : vfh_Bad σ0 s2 → validFaultHandler c1) (k1 : CnOk σ0 c2) (k2 : CnOk σ0 c1) :
    IK (VS σ0) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap
  refine ik_bind (vs_setCap h1 k1) fun _ => ?_
  refine ik_bind (vs_setCap h2 k2) fun _ => ?_
  vs_tail

/-- **`cap_swap_for_delete`** of two slots that are no fault-handler slots. -/
theorem vs_capSwapForDelete {σ0 : State Unit} (s1 s2 : CslotPtr) (h1 : ¬ vfh_Bad σ0 s1) (h2 : ¬ vfh_Bad σ0 s2) :
    IK (VS σ0) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ ?_
  intro σ
  refine ikp_getCap_bind fun c1 hc1 => ikp_getCap_bind fun c2 hc2 => ?_
  intro hσ x hx
  exact vs_pin hσ (vs_capSwap _ _ (fun h => (h1 (h.back hσ.2.1)).elim) (fun h => (h2 (h.back hσ.2.1)).elim)
    (hσ.cnOk hc2) (hσ.cnOk hc1)) x hx

/-! ## Deletion -/

theorem vs_emptySlot (sl : CslotPtr) (c : Cap) : VK (emptySlot (Z := Unit) sl c) := by
  intro σ0
  unfold emptySlot postCapDeletion deletedIrqHandler
  vs_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_emptySlot _ _ _)

theorem vs_capDeleteOne (sl : CslotPtr) : VK (capDeleteOne (Z := Unit) sl) := by
  intro σ0; unfold capDeleteOne; vs_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_capDeleteOne _ _)

theorem vs_deletingIrqHandler (irq : Irq) : VK (deletingIrqHandler (Z := Unit) irq) := by
  intro σ0; unfold deletingIrqHandler; vs_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_deletingIrqHandler _ _)

theorem vs_finaliseCap (c : Cap) (b : Bool) : VK (finaliseCap (Z := Unit) c b) := by
  intro σ0; unfold finaliseCap; vs_tail

/-- The remainder of a valid fault handler's finalisation is null. -/
theorem vfh_finaliseCap_rem {c : Cap} (hc : validFaultHandler c) (b : Bool) {σ : State Unit}
    {x : (Cap × Cap) × State Unit} (hx : x ∈ (finaliseCap (Z := Unit) c b σ).1) : x.1.1 = .nullCap := by
  rcases vfh_cases hc with rfl | h
  · unfold finaliseCap at hx; rw [Set.mem_singleton_iff.1 hx]
  · cases c <;> simp [isEpCap] at h
    unfold finaliseCap NonDet.liftM at hx
    obtain ⟨y, -, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]

/-- Every outcome's value satisfies `Q` (ut3's `OV`). -/
def VOV {α : Type} (Q : α → Prop) (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → Q x.1

section VOVc
variable {α β : Type} {Q : β → Prop}

theorem vov_bind {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (h : ∀ a, VOV Q (g a)) :
    VOV Q (m >>= g) := by
  rintro σ x ⟨y, -, hx⟩; exact h y.1 y.2 x hx

theorem vov_bind' {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (h : ∀ a, VOV Q (g a)) :
    VOV Q (NonDet.bind m g) := vov_bind h

theorem vov_pure {b : β} (h : Q b) : VOV Q (pure b : NonDet (State Unit) β) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact h

theorem vov_pure' {b : β} (h : Q b) : VOV Q (NonDet.pure b : NonDet (State Unit) β) := vov_pure h

theorem vov_liftM {f : α → β} {m : NonDet (State Unit) α} (h : ∀ a, Q (f a)) : VOV Q (NonDet.liftM f m) :=
  vov_bind' fun a => vov_pure' (h a)

theorem vov_fail : VOV Q (NonDet.fail : NonDet (State Unit) β) := fun _ _ hx => hx.elim

theorem vov_ite {c : Prop} [Decidable c] {m1 m2 : NonDet (State Unit) β} (h1 : VOV Q m1) (h2 : VOV Q m2) :
    VOV Q (if c then m1 else m2) := by
  split <;> assumption

end VOVc

/-- The remainder is no CNode cap. -/
def VRemNC (p : Cap × Cap) : Prop := ∀ q r g, p.1 ≠ .cnodeCap q r g

macro "vov_auto" : tactic => `(tactic| repeat' (first
  | (refine vov_bind fun _ => ?_) | (refine vov_bind' fun _ => ?_)
  | (refine vov_liftM fun _ => ?_)
  | exact vov_fail
  | (refine vov_pure ?_) | (refine vov_pure' ?_)
  | (refine vov_ite ?_ ?_)
  | (show VRemNC _; intro _ _ _ h; first | cases h | (split at h <;> cases h))
  | split))

/-- **`finalise_cap`'s remainder is never a CNode cap** (a final CNode cap
becomes a Zombie, a non-final one null). -/
theorem vfh_finaliseCap_nc (c : Cap) (fin : Bool) : VOV VRemNC (finaliseCap (Z := Unit) c fin) := by
  cases c <;> simp only [finaliseCap, archFinaliseCap] <;> vov_auto

/-- `lfp` with a call-dependent relation (`ik_lfp` generalised). -/
theorem vfh_lfp {ι α : Type} {F : (ι → NonDet (State Unit) α) → ι → NonDet (State Unit) α}
    (R : ι → State Unit → State Unit → Prop)
    (hF : ∀ f : ι → NonDet (State Unit) α, (∀ k σ x, x ∈ (f k σ).1 → R k σ x.2) →
      ∀ k σ x, x ∈ (F f k σ).1 → R k σ x.2) (i : ι) (σ : State Unit) (x : α × State Unit)
    (hx : x ∈ (NonDet.lfp F i σ).1) : R i σ x.2 := by
  let f : ι → NonDet (State Unit) α := fun k t => ({y | R k t y.2}, True)
  have hf : ∀ k t, F f k t ≤ f k t := fun k t =>
    ⟨fun y hy => hF f (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (ik_lfp_le F f hf i σ).1 hx

/-- What a `rec_del` call needs: a reduce-zombie call of an unexposed slot
whose slot is no fault-handler slot (or whose cap is a valid fault handler, the
call then failing). -/
def vfhRecPre : RecDelCall → State Unit → Prop
  | .reduceZombieCall c sl false, σ => ¬ vfh_Bad σ sl ∨ validFaultHandler c
  | _, _ => True

def vfhRecR (k : RecDelCall) (σ σ' : State Unit) : Prop := VfhV σ ∧ CnDom σ → vfhRecPre k σ → VS σ σ'

theorem vs_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k σ x, x ∈ (f k σ).1 → vfhRecR k σ x.2) (k : RecDelCall) (σ : State Unit) (hσ : VfhV σ ∧ CnDom σ)
    (hpre : vfhRecPre k σ) : ∀ x ∈ ((recDelF (Z := Unit) f k).run σ).1, VS σ x.2 := by
  -- the recursive calls without precondition keep any anchor
  have hu : ∀ k, (∀ σ, vfhRecPre k σ) → ∀ σ0, IKE (ε := Unit) (VS σ0) (f k : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun k hk σ0 s hs x hx => hs.trans (hrec k s x hx hs.cur (hk s))
  have hu1 : ∀ sl e σ0, IKE (ε := Unit) (VS σ0) (f (.cTEDeleteCall sl e) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun sl e => hu _ fun _ => trivial
  have hu2 : ∀ sl e σ0, IKE (ε := Unit) (VS σ0) (f (.finaliseSlotCall sl e) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun sl e => hu _ fun _ => trivial
  have hu3 : ∀ c sl σ0, IKE (ε := Unit) (VS σ0) (f (.reduceZombieCall c sl true) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun c sl => hu _ fun _ => trivial
  cases k with
  | cTEDeleteCall sl e =>
    have : IKE (VS σ) (recDelF (Z := Unit) f (.cTEDeleteCall sl e)) := by
      unfold recDelF withoutPreemption
      try dsimp only
      refine ike_bind (hu2 sl e σ) fun _ => ?_
      vs_tail
    exact this σ (VS.refl hσ)
  | finaliseSlotCall sl e =>
    unfold recDelF withoutPreemption
    try dsimp only
    refine ikpE_getCap_bind (fun cap hcap => ?_) (VS.refl hσ)
    -- the cap read is at the anchor state `σ`
    refine ike_ite _ (ike_returnOk _) ?_ σ
    refine ike_bind (ike_liftE (hv_isFinalCap _)) (fun fin => ?_)
    intro s hs x hx
    obtain ⟨y, hy, hx⟩ := vfh_run_liftE_bind_mem hx
    have hy1 := vs_finaliseCap cap fin σ s hs y hy
    have hrem : vfh_Bad σ sl → validFaultHandler y.1.1 := fun hb => by
      have := hσ.1 _ _ (hb.1 ▸ hcap) hb.2
      rw [vfh_finaliseCap_rem this fin hy]; exact vfh_null
    have hremk : CnOk σ y.1.1 := cnOk_of_nc (vfh_finaliseCap_nc cap fin s y hy)
    obtain ⟨⟨rem, ci⟩, s1⟩ := y
    dsimp only at hx hrem hy1 hremk
    refine (?_ : IKE (VS σ) _) s1 hy1 x hx
    refine ike_ite _ (ike_returnOk _) (ike_ite _ ?_ ?_)
    · exact ike_bind (ike_liftE (vs_setCap hrem hremk)) fun _ => ike_returnOk _
    · intro s2 hs2 x hx
      obtain ⟨⟨u, s3⟩, h3, hx⟩ := vfh_run_liftE_bind_mem hx
      have hs3 := vs_setCap hrem hremk s2 hs2 ⟨u, s3⟩ h3
      dsimp only at hx
      -- the reduce-zombie call: its slot is not `Bad` unless the remainder is a valid fault handler
      have hpre3 : vfhRecPre (.reduceZombieCall rem sl e) s3 := by
        cases e
        · by_cases hb : vfh_Bad s3 sl
          · exact Or.inr (hrem (hb.back hs3.2.1))
          · exact Or.inl hb
        · trivial
      rw [ExceptT.run_bind] at hx
      obtain ⟨⟨r4, s4⟩, h4, hx⟩ := hx
      have hs4 : VS σ s4 := hs3.trans (hrec _ s3 _ h4 hs3.cur hpre3)
      cases r4 with
      | error e' =>
        simp only [ExceptT.bindCont] at hx
        rw [Set.mem_singleton_iff.1 hx]; exact hs4
      | ok _ =>
        simp only [ExceptT.bindCont] at hx
        exact (ike_bind hv_preemptionPoint fun _ => hu2 sl e σ) s4 hs4 x hx
  | reduceZombieCall c sl e =>
    by_cases hz : ∃ ptr bits n, c = .zombie ptr bits (n + 1)
    · obtain ⟨ptr, bits, n, rfl⟩ := hz
      cases e
      · -- unexposed: swap the zombie's first slot into place
        have hnb : ¬ vfh_Bad σ sl := by
          rcases hpre with h | h
          · exact h
          · exact (vfh_not_zombie _ _ _ h).elim
        have : IKE (VS σ) (recDelF (Z := Unit) f (.reduceZombieCall (.zombie ptr bits (n + 1)) sl false)) := by
          unfold recDelF withoutPreemption
          try dsimp only
          refine ike_returnOk_bind ?_
          refine ike_bind (ike_assertE _) fun _ => ?_
          refine ike_bind (ike_liftE (vs_capSwapForDelete _ _ ?_ hnb)) fun _ => ike_returnOk _
          unfold firstCslotOf
          exact vfh_notBad_idx (vfh_replicate_ne _)
        exact this σ (VS.refl hσ)
      · have : IKE (VS σ) (recDelF (Z := Unit) f (.reduceZombieCall (.zombie ptr bits (n + 1)) sl true)) := by
          unfold recDelF withoutPreemption
          try dsimp only
          refine ike_returnOk_bind ?_
          refine ike_bind (hu1 _ _ σ) fun _ => ?_
          intro s hs
          refine ikpE_getCap_bind (fun nc hnc => ?_) hs
          by_cases hz : nc = .zombie ptr bits (n + 1)
          · rw [if_pos hz]; subst hz
            refine ikpE_bind ?_ (fun _ => ike_returnOk _)
            intro hs' x hx
            exact vs_reanchor hs' (ike_liftE (vs_setCap_nb (vfh_notBad_old hs'.1 hnc (vfh_not_zombie _ _ _))
              (cnOk_zombie _ _ _)) s) x hx
          · rw [if_neg hz]; exact ikp_of_ik (ike_bind (ike_assertE _) fun _ => ike_returnOk _) s
        exact this σ (VS.refl hσ)
    · have e1 : recDelF (Z := Unit) f (.reduceZombieCall c sl e) = NonDetE.liftE NonDet.fail := by
        rw [recDelF.eq_def]
        split <;> first | rfl | (exfalso; apply hz; exact ⟨_, _, _, rfl⟩) | (exfalso; apply hz; simp_all)
      rw [e1]
      intro x hx
      unfold NonDetE.liftE at hx
      rw [ExceptT.run_lift] at hx
      obtain ⟨_, h, _⟩ := hx
      exact h.elim

/-- **`rec_del`** keeps `VfhV` (and every slot) for every call satisfying `vfhRecPre`. -/
theorem vs_recDel (k : RecDelCall) (σ : State Unit) (hσ : VfhV σ ∧ CnDom σ) (hpre : vfhRecPre k σ) :
    ∀ x ∈ ((recDel (Z := Unit) k) σ).1, VS σ x.2 := by
  intro x hx
  unfold recDel at hx
  exact vfh_lfp vfhRecR (fun f hf k σ x hx hσ hp => vs_recDelF hf k σ hσ hp x hx) k σ x hx hσ hpre

theorem vs_capDelete (sl : CslotPtr) : VKE (capDelete (Z := Unit) sl) := by
  intro σ0
  unfold capDelete
  refine ike_bind (fun σ hσ x hx => hσ.trans (vs_recDel (.cTEDeleteCall sl true) σ hσ.cur trivial x hx)) fun _ => ike_returnOk _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_capDelete _ _)

theorem vs_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k σ0, IK (VS σ0) (f k)) (sl : CslotPtr) (σ0 : State Unit) :
    IKE (VS σ0) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (ε := Unit) (VS σ0) (f k : NonDetE (State Unit) Unit Unit) := fun k => hrec k σ0
  unfold capRevokeF withoutPreemption selectExt
  vs_tail
  all_goals exact hrec' _

theorem vs_capRevoke (sl : CslotPtr) : VKE (capRevoke (Z := Unit) sl) := by
  intro σ0
  unfold capRevoke
  intro σ hσ x hx
  exact vfh_lfp (fun _ s s' => ∀ σ1, VS σ1 s → VS σ1 s')
    (fun f hf k s y hy σ1 h1 => vs_capRevokeF (fun k' σ2 s2 h2 z hz => hf k' s2 z hz σ2 h2) k σ1 s h1 y hy)
    sl σ x hx σ0 hσ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_capRevoke _ _)

end

end Fl4Proofs.P3.SInv
