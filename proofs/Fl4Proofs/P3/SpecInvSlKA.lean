/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **`ScKindR` carried in the cap view,
anchored** (spec side only; sl4 handoff 1, the deletion leaves for the range form,
done once for every writer).

* `KD c0 c` (the cap condition that carries `ScKindR` over a derived cap): an SC cap
  `c` comes from an SC cap to its object, and every address in `c`'s range is `c`'s
  own SC object or lies in `c0`'s range without `c0` being the SC cap to it. A
  preorder; implied by sl4's `KindRel` (`kd_of_kindRel`) and by every cap with an
  empty range that is no SC cap (null, untyped, IRQ caps: `kd_empty`).
* `KOk σ0 c`: `c` is `KD` to "the SC caps of `σ0`": an SC cap names an object some
  slot of `σ0` holds an SC cap to; an address in its range is its own SC object or
  no SC cap of `σ0` names it. Every slot cap of a `ScKindR` state is `KOk` there
  (`kok_of_slot`), `KD` keeps it (`KOk.kd`).
* **`KS σ0 σ`**: every cap of `σ` is `KOk σ0`. `KS σ0 σ → ScKindR σ` (`KS.cur`),
  `ScKindR σ → KS σ σ` (`KS.refl`); it reads only vih2's cap view `hV`, so it is a
  `WLH` predicate and the 341 generated frames (SpecInvValidIrqHandlersF1..F4) keep
  it. A cap write keeps `KS σ0` as soon as the written cap is `KOk σ0`, whatever the
  slot (`ks_setCap`): the only writes that need more are the fresh caps of a retype.
* Writers (`KK m := ∀ σ0, IK (KS σ0) m`): `ks_setUntypedCapAsFull` (an untyped cap),
  `ks_capInsert` / `ks_capMove` / `ks_capSwap` (`KOk σ0` caps), `ks_capSwapForDelete`
  (both caps re-read), deletion: `ks_emptySlot`, `ks_capDeleteOne`,
  `ks_deletingIrqHandler`, `ks_finaliseCap`, `kd_finaliseCap` (the remainder is null
  or a Zombie of the finalised cap's object), **`ks_recDel`** (no call precondition:
  every remainder and Zombie written is `KD` to the cap read from that slot),
  `ks_capDelete`, `ks_capRevoke`.
-/
import Fl4Proofs.P3.SpecInvSlKR
import Fl4Proofs.P3.SpecInvVfhE
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvV (hV hV_cap WLH wlh_of_hV hv_isFinalCap hv_preemptionPoint setIrqState_out)

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## Derived caps -/

/-- The condition under which `c` inherits `KOk` from `c0` (module docstring). -/
def KD (c0 c : Cap) : Prop :=
  (∀ r b, c = .schedContextCap r b → ∃ b', c0 = .schedContextCap r b') ∧
    ∀ r ∈ capRng c, (∃ b, c = .schedContextCap r b) ∨ (r ∈ capRng c0 ∧ ∀ b, c0 ≠ .schedContextCap r b)

theorem kd_refl (c : Cap) : KD c c := by
  refine ⟨fun r b e => ⟨b, e⟩, fun r hr => ?_⟩
  by_cases h : ∃ b, c = .schedContextCap r b
  · exact Or.inl h
  · exact Or.inr ⟨hr, fun b e => h ⟨b, e⟩⟩

theorem kd_trans {a b c : Cap} (h1 : KD a b) (h2 : KD b c) : KD a c := by
  refine ⟨fun r x e => ?_, fun r hr => ?_⟩
  · obtain ⟨y, ey⟩ := h2.1 r x e; exact h1.1 r y ey
  · rcases h2.2 r hr with h | ⟨hb, hn⟩
    · exact Or.inl h
    · rcases h1.2 r hb with ⟨x, ex⟩ | h
      · exact absurd ex (hn x)
      · exact Or.inr h

theorem kd_of_kindRel {c0 c : Cap} (h : KindRel c0 c) : KD c0 c := by
  refine ⟨h.1, fun r hr => ?_⟩
  by_cases hc : ∃ b, c0 = .schedContextCap r b
  · obtain ⟨b, e⟩ := hc; exact Or.inl (h.2.1 r b e)
  · exact Or.inr ⟨h.2.2 hr, fun b e => hc ⟨b, e⟩⟩

/-- A cap with an empty range that is no SC cap is derived from anything. -/
theorem kd_empty {c0 c : Cap} (h : capRng c = ∅) (hs : ∀ r b, c ≠ .schedContextCap r b) : KD c0 c :=
  ⟨fun r b e => absurd e (hs r b), fun r hr => by rw [h] at hr; exact hr.elim⟩

theorem kd_null (c0 : Cap) : KD c0 .nullCap :=
  kd_empty (by ext r; simp [capRng, objRefs]) (fun _ _ e => by cases e)

/-- A Zombie of an object in `c`'s range (`c` no SC cap). -/
theorem kd_zombie_of {c : Cap} {r : ObjRef} {b : Option Nat} {n : Nat} (h : r ∈ capRng c)
    (hs : ∀ x y, c ≠ .schedContextCap x y) : KD c (.zombie r b n) := by
  refine ⟨(fun _ _ e => by cases e), fun r' hr => Or.inr ?_⟩
  have e : r' = r := by simpa [capRng, objRefs] using hr
  subst e
  exact ⟨h, fun b' e => hs _ _ e⟩

/-! ## `KOk` and the anchored predicate -/

/-- `c` is derived from the SC caps of `σ0` (module docstring). -/
def KOk (σ0 : State Unit) (c : Cap) : Prop :=
  (∀ r b, c = .schedContextCap r b → ∃ s b', SInvU.capAt σ0 s = some (.schedContextCap r b')) ∧
    ∀ r ∈ capRng c, (∃ b, c = .schedContextCap r b) ∨ ∀ s b, SInvU.capAt σ0 s ≠ some (.schedContextCap r b)

theorem KOk.kd {σ0 : State Unit} {c0 c : Cap} (h : KOk σ0 c0) (hd : KD c0 c) : KOk σ0 c := by
  refine ⟨fun r b e => ?_, fun r hr => ?_⟩
  · obtain ⟨b', e'⟩ := hd.1 r b e; exact h.1 r b' e'
  · rcases hd.2 r hr with h1 | ⟨h0, hn⟩
    · exact Or.inl h1
    · rcases h.2 r h0 with ⟨b, e⟩ | h2
      · exact absurd e (hn b)
      · exact Or.inr h2

theorem kok_of_slot {σ0 : State Unit} (hK : ScKindR σ0) {s : CslotPtr} {c : Cap}
    (h : SInvU.capAt σ0 s = some c) : KOk σ0 c := by
  refine ⟨fun r b e => ⟨s, b, e ▸ h⟩, fun r hr => ?_⟩
  by_cases hx : ∃ s' b, SInvU.capAt σ0 s' = some (.schedContextCap r b)
  · obtain ⟨s', b, hs'⟩ := hx
    exact Or.inl (hK s' r b s c hs' h hr)
  · exact Or.inr fun s' b e => hx ⟨s', b, e⟩

theorem kok_empty {σ0 : State Unit} {c : Cap} (h : capRng c = ∅) (hs : ∀ r b, c ≠ .schedContextCap r b) :
    KOk σ0 c :=
  ⟨fun r b e => absurd e (hs r b), fun r hr => by rw [h] at hr; exact hr.elim⟩

theorem kok_null {σ0 : State Unit} : KOk σ0 .nullCap :=
  kok_empty (by ext r; simp [capRng, objRefs]) (fun _ _ e => by cases e)

/-- **Every cap of `σ` is `KOk σ0`.** -/
def KS (σ0 σ : State Unit) : Prop := ∀ (sl : CslotPtr) (c : Cap), capOpt (σ.kheap sl.1) sl.2 = some c → KOk σ0 c

theorem KS.cap {σ0 σ : State Unit} (h : KS σ0 σ) {sl : CslotPtr} {c : Cap} (hc : SInvU.capAt σ sl = some c) :
    KOk σ0 c := h sl c (by rw [← vfh_capAt]; exact hc)

theorem KS.cur {σ0 σ : State Unit} (h : KS σ0 σ) : ScKindR σ := by
  intro s r b s' c' h1 h2 h3
  obtain ⟨s0, b0, h0⟩ := (h.cap h1).1 r b rfl
  rcases (h.cap h2).2 r h3 with e | hn
  · exact e
  · exact absurd h0 (hn s0 b0)

theorem KS.refl {σ : State Unit} (h : ScKindR σ) : KS σ σ :=
  fun sl c hc => kok_of_slot h (by rw [vfh_capAt]; exact hc)

theorem KS.view {σ0 σ σ' : State Unit} (e : hV σ' = hV σ) (h : KS σ0 σ) : KS σ0 σ' :=
  fun sl c hc => h sl c (by rw [← hV_cap e]; exact hc)

instance (σ0 : State Unit) : WLH (KS σ0) := wlh_of_hV fun _ _ e h => h.view e

/-- Everything a frame function of the family keeps. -/
abbrev KK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ0, IK (KS σ0) m
abbrev KKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := ∀ σ0, IKE (KS σ0) m

theorem ik_skr_of {α : Type} {m : NonDet (State Unit) α} (h : KK m) : IK ScKindR m :=
  fun σ hσ y hy => (h σ σ (KS.refl hσ) y hy).cur

theorem ike_skr_of {ε α : Type} {m : NonDetE (State Unit) ε α} (h : KKE m) : IKE ScKindR m :=
  ik_skr_of h

/-! ## `set_cap` and the fields `KS` does not read -/

/-- **A cap write keeps `KS σ0` when the cap is `KOk σ0`.** -/
theorem ks_setCap {σ0 : State Unit} {c : Cap} (sl : CslotPtr) (hc : KOk σ0 c) :
    IK (KS σ0) (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ hσ x hx sl' c' h
  obtain ⟨p, l⟩ := sl'
  rw [vfh_setCap_view hx p l] at h
  split at h
  · cases h; exact hc
  · exact hσ (p, l) c' h

theorem ks_setCap_null {σ0 : State Unit} (sl : CslotPtr) : IK (KS σ0) (setCap (Z := Unit) .nullCap sl) :=
  ks_setCap sl kok_null

theorem ks_of_kheap {σ0 σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h : KS σ0 σ) : KS σ0 σ' :=
  fun sl c hc => h sl c (by rw [hk] at hc; exact hc)

theorem ks_setCdt {σ0 : State Unit} (t : Cdt) : IK (KS σ0) (setCdt (Z := Unit) t) := by
  unfold setCdt
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ks_of_kheap rfl hσ

theorem ks_updateCdt {σ0 : State Unit} (f : Cdt → Cdt) : IK (KS σ0) (updateCdt (Z := Unit) f) := by
  unfold updateCdt
  exact ik_bind (ik_gets _) fun _ => ks_setCdt _

theorem ks_setOriginal {σ0 : State Unit} (sl : CslotPtr) (b : Bool) : IK (KS σ0) (setOriginal (Z := Unit) sl b) := by
  unfold setOriginal
  exact ik_bind (ik_gets _) fun _ => ik_modify fun _ h => ks_of_kheap rfl h

theorem ks_doExtendedOp {σ0 : State Unit} (eop : DetExtMonad Unit) : IK (KS σ0) (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => ks_of_kheap rfl h) eop

theorem ks_setIrqState {σ0 : State Unit} (st : IrqState) (i : Irq) : IK (KS σ0) (setIrqState (Z := Unit) st i) := by
  intro σ hσ x hx
  obtain ⟨hk, -⟩ := setIrqState_out hx
  exact ks_of_kheap hk hσ

theorem ks_doMachineOp {σ0 : State Unit} {α : Type} (mop : NonDet MachineState α) :
    IK (KS σ0) (doMachineOp (Z := Unit) mop) := ik_doMachineOp (fun _ _ h => ks_of_kheap rfl h) mop

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_doMachineOp _)

macro "ks_tail" : tactic => `(tactic| repeat' (first
  | (with_reducible exact ks_setCdt _) | (with_reducible exact ks_updateCdt _)
  | (with_reducible exact ks_setOriginal _ _) | (with_reducible exact ks_doExtendedOp _)
  | (with_reducible exact ks_setIrqState _ _) | (with_reducible exact ks_setCap_null _)
  | hv_leaf | ik_step0 | ik_unfold))

/-! ## The CSpace writers -/

theorem kok_maxFree {σ0 : State Unit} {c : Cap} (h : isUntypedCap c = true) : KOk σ0 (maxFreeIndexUpdate c) := by
  cases c <;> simp [isUntypedCap] at h
  exact kok_empty (by ext r; simp [maxFreeIndexUpdate, freeIndexUpdate, capRng, objRefs])
    (fun _ _ e => by simp [maxFreeIndexUpdate, freeIndexUpdate] at e)

theorem ks_setUntypedCapAsFull {σ0 : State Unit} (srcCap newCap : Cap) (src : CslotPtr) :
    IK (KS σ0) (setUntypedCapAsFull (Z := Unit) srcCap newCap src) := by
  intro σ hσ x hx
  unfold setUntypedCapAsFull at hx
  split at hx
  · rename_i h; exact ks_setCap _ (kok_maxFree h.1) σ hσ x hx
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

/-- **`cap_insert`** of a `KOk σ0` cap. -/
theorem ks_capInsert {σ0 : State Unit} {newCap : Cap} (src dest : CslotPtr) (hk : KOk σ0 newCap) :
    IK (KS σ0) (capInsert (Z := Unit) newCap src dest) := by
  unfold capInsert
  intro σ
  refine ikp_getCap_bind fun srcCap _ => ?_
  refine ikp_pure_bind ?_
  refine ikp_getCap_bind fun _ _ => ?_
  refine ikp_keep (fun y hy => by rw [hy.2]) fun _ => ?_
  refine ikp_bind (ikp_of_ik (ks_setUntypedCapAsFull _ _ _) σ) fun _ => ?_
  refine ik_bind (ks_setCap _ hk) fun _ => ?_
  ks_tail

/-- **`cap_move`** of a `KOk σ0` cap. -/
theorem ks_capMove {σ0 : State Unit} {newCap : Cap} (src dest : CslotPtr) (hk : KOk σ0 newCap) :
    IK (KS σ0) (capMove (Z := Unit) newCap src dest) := by
  unfold capMove
  refine ik_bind (ks_setCap _ hk) fun _ => ?_
  ks_tail

/-- **`cap_swap`** of `KOk σ0` caps. -/
theorem ks_capSwap {σ0 : State Unit} {c1 c2 : Cap} (s1 s2 : CslotPtr) (k1 : KOk σ0 c2) (k2 : KOk σ0 c1) :
    IK (KS σ0) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap
  refine ik_bind (ks_setCap _ k1) fun _ => ?_
  refine ik_bind (ks_setCap _ k2) fun _ => ?_
  ks_tail

/-- **`cap_swap_for_delete`**: both caps are re-read from their slots. -/
theorem ks_capSwapForDelete (s1 s2 : CslotPtr) : KK (capSwapForDelete (Z := Unit) s1 s2) := by
  intro σ0
  unfold capSwapForDelete
  refine ik_when _ ?_
  intro σ
  refine ikp_getCap_bind fun c1 hc1 => ikp_getCap_bind fun c2 hc2 => ?_
  intro hσ x hx
  exact ks_capSwap _ _ (hσ _ _ hc2) (hσ _ _ hc1) σ hσ x hx

/-! ## Deletion -/

theorem ks_emptySlot (sl : CslotPtr) (c : Cap) : KK (emptySlot (Z := Unit) sl c) := by
  intro σ0
  unfold emptySlot postCapDeletion deletedIrqHandler
  ks_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_emptySlot _ _ _)

theorem ks_capDeleteOne (sl : CslotPtr) : KK (capDeleteOne (Z := Unit) sl) := by
  intro σ0; unfold capDeleteOne; ks_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_capDeleteOne _ _)

theorem ks_deletingIrqHandler (irq : Irq) : KK (deletingIrqHandler (Z := Unit) irq) := by
  intro σ0; unfold deletingIrqHandler; ks_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_deletingIrqHandler _ _)

theorem ks_finaliseCap (c : Cap) (b : Bool) : KK (finaliseCap (Z := Unit) c b) := by
  intro σ0; unfold finaliseCap; ks_tail

macro "kov_auto" : tactic => `(tactic| repeat' (first
  | (refine vov_bind fun _ => ?_) | (refine vov_bind' fun _ => ?_)
  | (refine vov_liftM fun _ => ?_)
  | exact vov_fail
  | (refine vov_pure ?_) | (refine vov_pure' ?_)
  | (refine vov_ite ?_ ?_)
  | exact kd_null _ | exact kd_refl _
  | exact kd_zombie_of (by simp [capRng, objRefs]) (fun _ _ e => by cases e)
  | (dsimp only)
  | split))

/-- **`finalise_cap`'s remainder is null or a Zombie of the finalised object.** -/
theorem kd_finaliseCap (c : Cap) (fin : Bool) : VOV (fun p : Cap × Cap => KD c p.1) (finaliseCap (Z := Unit) c fin) := by
  cases c <;> simp only [finaliseCap, archFinaliseCap] <;> kov_auto

theorem ks_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k σ x, x ∈ (f k σ).1 → ∀ σ0, KS σ0 σ → KS σ0 x.2) (k : RecDelCall) (σ0 : State Unit) :
    IKE (KS σ0) (recDelF (Z := Unit) f k) := by
  have hu : ∀ k, IKE (ε := Unit) (KS σ0) (f k : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun k s hs x hx => hrec k s x hx σ0 hs
  cases k with
  | cTEDeleteCall sl e =>
    unfold recDelF withoutPreemption
    try dsimp only
    refine ike_bind (hu _) fun _ => ?_
    ks_tail
  | finaliseSlotCall sl e =>
    unfold recDelF withoutPreemption
    try dsimp only
    intro σ hσ
    refine ikpE_getCap_bind (fun cap hcap => ?_) hσ
    have hk : KOk σ0 cap := hσ _ _ hcap
    refine ikp_of_ik (?_ : IKE (KS σ0) _) σ
    refine ike_ite _ (ike_returnOk _) ?_
    refine ike_bind (ike_liftE (hv_isFinalCap _)) (fun fin => ?_)
    intro s hs x hx
    obtain ⟨y, hy, hx⟩ := vfh_run_liftE_bind_mem hx
    have hy1 := ks_finaliseCap cap fin σ0 s hs y hy
    have hrem : KOk σ0 y.1.1 := hk.kd (kd_finaliseCap cap fin s y hy)
    obtain ⟨⟨rem, ci⟩, s1⟩ := y
    dsimp only at hx hrem hy1
    refine (?_ : IKE (KS σ0) _) s1 hy1 x hx
    refine ike_ite _ (ike_returnOk _) (ike_ite _ ?_ ?_)
    · exact ike_bind (ike_liftE (ks_setCap _ hrem)) fun _ => ike_returnOk _
    · refine ike_bind (ike_liftE (ks_setCap _ hrem)) fun _ => ?_
      refine ike_bind (hu _) fun _ => ?_
      exact ike_bind hv_preemptionPoint fun _ => hu _
  | reduceZombieCall c sl e =>
    by_cases hz : ∃ ptr bits n, c = .zombie ptr bits (n + 1)
    · obtain ⟨ptr, bits, n, rfl⟩ := hz
      cases e
      · unfold recDelF withoutPreemption
        try dsimp only
        refine ike_returnOk_bind ?_
        refine ike_bind (ike_assertE _) fun _ => ?_
        exact ike_bind (ike_liftE (ks_capSwapForDelete _ _ σ0)) fun _ => ike_returnOk _
      · unfold recDelF withoutPreemption
        try dsimp only
        refine ike_returnOk_bind ?_
        refine ike_bind (hu _) fun _ => ?_
        intro s hs
        refine ikpE_getCap_bind (fun nc hnc => ?_) hs
        by_cases hz : nc = .zombie ptr bits (n + 1)
        · rw [if_pos hz]; subst hz
          refine ikp_of_ik (ike_bind (ike_liftE (ks_setCap _ ((hs _ _ hnc).kd
            (kd_zombie_of (by simp [capRng, objRefs]) (fun _ _ e => by cases e))))) fun _ => ike_returnOk _) s
        · rw [if_neg hz]; exact ikp_of_ik (ike_bind (ike_assertE _) fun _ => ike_returnOk _) s
    · have e1 : recDelF (Z := Unit) f (.reduceZombieCall c sl e) = NonDetE.liftE NonDet.fail := by
        rw [recDelF.eq_def]
        split <;> first | rfl | (exfalso; apply hz; exact ⟨_, _, _, rfl⟩) | (exfalso; apply hz; simp_all)
      rw [e1]
      intro σ _ x hx
      unfold NonDetE.liftE at hx
      rw [ExceptT.run_lift] at hx
      obtain ⟨_, h, _⟩ := hx
      exact h.elim

/-- **`rec_del` keeps `KS σ0`** for every call. -/
theorem ks_recDel (k : RecDelCall) : KK (recDel (Z := Unit) k) := by
  intro σ0 σ hσ x hx
  unfold recDel at hx
  exact vfh_lfp (fun _ s s' => ∀ σ1, KS σ1 s → KS σ1 s')
    (fun f hf k s y hy σ1 h1 => ks_recDelF (fun k' s2 z hz σ2 h2 => hf k' s2 z hz σ2 h2) k σ1 s h1 y hy)
    k σ x hx σ0 hσ

theorem ks_capDelete (sl : CslotPtr) : KKE (capDelete (Z := Unit) sl) := by
  intro σ0
  unfold capDelete
  exact ike_bind (ks_recDel (.cTEDeleteCall sl true) σ0) fun _ => ike_returnOk _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_capDelete _ _)

theorem ks_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k σ0, IK (KS σ0) (f k)) (sl : CslotPtr) (σ0 : State Unit) :
    IKE (KS σ0) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (ε := Unit) (KS σ0) (f k : NonDetE (State Unit) Unit Unit) := fun k => hrec k σ0
  unfold capRevokeF withoutPreemption selectExt
  ks_tail
  all_goals exact hrec' _

theorem ks_capRevoke (sl : CslotPtr) : KKE (capRevoke (Z := Unit) sl) := by
  intro σ0
  unfold capRevoke
  intro σ hσ x hx
  exact vfh_lfp (fun _ s s' => ∀ σ1, KS σ1 s → KS σ1 s')
    (fun f hf k s y hy σ1 h1 => ks_capRevokeF (fun k' σ2 s2 h2 z hz => hf k' s2 z hz σ2 h2) k σ1 s h1 y hy)
    sl σ x hx σ0 hσ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ks_capRevoke _ _)

end

end Fl4Proofs.P3.SInvL
