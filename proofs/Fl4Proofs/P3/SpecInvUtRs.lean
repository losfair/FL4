/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **the reset of an
untyped cap keeps `UtInv'`** (spec side only).

`reset_untyped_cap src` (after `ensure_no_children src` at the decode) deletes
every object of the region `[b, b + 2^n)` and then lowers the free index step by
step. With no CDT child, UtDesc says that no other untyped cap's free part meets
the region and every other untyped cap overlapping it is an ancestor
(`RSV`, kept by every step); then `set_cap` of the source with *any* free index
up to the size keeps `UtInv'` (`rs_setCap`) — also the free-index write of the
retype that follows the reset.

The one fact the deletion needs that `UtInv'` does not give: no CDT parent slot
lies in a deleted object (else `CdtOK` breaks). l4v derives it from
`untyped_children_in_mdb` + `if_unsafe_then_cap` + `mdb_cte_at`: an object in a
childless untyped's region is referenced by no cap, so its slots are empty.
That chain is not carried here; its narrowest form is the named premise
**`DetypeOK` [J]** below (a fact of the state the invocation starts from, read
through the view, true in every l4v `invs` state).
-/
import Fl4Proofs.P3.SpecInvUtIns
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **DetypeOK [J]** (l4v `untyped_children_in_mdb` + `if_unsafe_then_cap` +
`mdb_cte_at`): no CDT parent slot lies in an object inside the region of an
untyped cap that has no CDT child. -/
def DetypeOK (σ : State Unit) : Prop :=
  ∀ u dev b n fi, capAt σ u = some (.untypedCap dev b n fi) → (∀ c, σ.cdt c ≠ some u) →
    ∀ c p, σ.cdt c = some p → p.1 ∉ delR b n

theorem detypeOK_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hD : DetypeOK σ) : DetypeOK σ' := by
  have hcap : capAt σ' = capAt σ := congrArg (fun w : UView => w.2.1) h
  have hcdt : σ'.cdt = σ.cdt := congrArg (fun w : UView => w.2.2.1) h
  intro u dev b n fi hc hk c p hp
  rw [hcap] at hc; rw [hcdt] at hk hp
  exact hD u dev b n fi hc hk c p hp

/-- The reset's carried facts about the source `src` with region `(b, n)`. -/
def RSV (src : CslotPtr) (dev : Bool) (b : ObjRef) (n : Nat) (t : Cdt) (w : UView) : Prop :=
  ((∃ f, w.2.1 src = some (.untypedCap dev b n f)) ∨ w.1 src.1 = false) ∧
  (∀ q, w.1 q = true → q.toNat ∉ utR b n) ∧ w.2.2.1 = t ∧ (∀ c, t c ≠ some src) ∧
  (∀ s2 d2 b2 n2 f2, s2 ≠ src → w.2.1 s2 = some (.untypedCap d2 b2 n2 f2) →
    (∀ k ∈ utR b n, k ∉ utFr b2 n2 f2) ∧ ((∃ k, k ∈ utR b n ∧ k ∈ utR b2 n2) → src ∈ descendantsOf s2 t)) ∧
  n ≤ untypedMaxBits ∧ b.toNat % 2 ^ n = 0

/-- **`set_cap` of the source with any free index up to its size.** -/
theorem rs_setCap {w : UView} (hI : UtInv'V w) {src : CslotPtr} {dev : Bool} {b : ObjRef} {n : Nat} {t : Cdt}
    (hR : RSV src dev b n t w) (hex : w.1 src.1 = true) {f : Nat} (hf : f ≤ 2 ^ n) :
    UtInv'V (vCap src (.untypedCap dev b n f) w) ∧ RSV src dev b n t (vCap src (.untypedCap dev b n f) w) := by
  obtain ⟨⟨hF, hW, hD, hDe, hOr⟩, hO, hA⟩ := hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
  obtain ⟨f0, hc0⟩ := h1.resolve_right (fun e => by rw [hex] at e; cases e)
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hA⟩, Or.inl ⟨f, by rw [vCap_cap, if_pos rfl]⟩, h2, h3, h4,
    fun s2 d2 b2 n2 f2 hne hc => ?_, h6, h7⟩
  · intro sl d b' n' f' hc q hq hk
    rw [vCap_cap] at hc
    by_cases e : sl = src
    · rw [if_pos e] at hc; cases hc; exact h2 q hq (utFr_sub hk)
    · rw [if_neg e] at hc; exact hF sl d b' n' f' hc q hq hk
  · intro sl d b' n' f' hc
    rw [vCap_cap] at hc
    by_cases e : sl = src
    · rw [if_pos e] at hc; cases hc; exact ⟨h6, h7, hf⟩
    · rw [if_neg e] at hc; exact hW sl d b' n' f' hc
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 k hk1 hk2
    rw [vCap_cap] at hc1 hc2
    by_cases e1 : s1 = src
    · subst e1; rw [if_pos rfl] at hc1; rw [if_neg (Ne.symm hne)] at hc2; cases hc1
      exact (h5 s2 _ _ _ _ (Ne.symm hne) hc2).1 k (utFr_sub hk1) hk2
    · rw [if_neg e1] at hc1
      by_cases e2 : s2 = src
      · rw [if_pos e2] at hc2; cases hc2
        exact (h5 s1 _ _ _ _ e1 hc1).1 k (utFr_sub hk2) hk1
      · rw [if_neg e2] at hc2; exact hD s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 k hk1 hk2
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 hov
    have hdt : (vCap src (.untypedCap dev b n f) w).2.2.1 = t := h3
    rw [vCap_cap] at hc1 hc2
    rw [hdt]
    by_cases e1 : s1 = src
    · subst e1; rw [if_pos rfl] at hc1; rw [if_neg (Ne.symm hne)] at hc2; cases hc1
      have := h5 s2 _ _ _ _ (Ne.symm hne) hc2
      exact Or.inr ⟨this.2 hov, this.1⟩
    · rw [if_neg e1] at hc1
      by_cases e2 : s2 = src
      · rw [if_pos e2] at hc2; cases hc2; subst e2
        have := h5 s1 _ _ _ _ e1 hc1
        obtain ⟨k, hk1, hk2⟩ := hov
        exact Or.inl ⟨this.2 ⟨k, hk2, hk1⟩, this.1⟩
      · rw [if_neg e2] at hc2; rw [← h3]; exact hDe s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 hov
  · intro sl d b' n' f' hc
    rw [vCap_cap] at hc
    by_cases e : sl = src
    · subst e; exact hOr sl dev b n f0 hc0
    · rw [if_neg e] at hc; exact hOr sl d b' n' f' hc
  · intro c q h
    rw [vCap_cap]
    by_cases e : q = src
    · rw [if_pos e]; exact ⟨_, rfl, by intro h; cases h⟩
    · rw [if_neg e]; exact hO c q h
  · rw [vCap_cap, if_neg hne] at hc; exact h5 s2 d2 b2 n2 f2 hne hc

theorem hv_setCap_ex (c : Cap) (sl : CslotPtr) (w : UView) :
    HV (· = w) (fun w' => w' = vCap sl c w ∧ w.1 sl.1 = true) (setCap (Z := Unit) c sl) := by
  intro σ hσ y hy
  refine ⟨hv_setCap c sl w σ hσ y hy, ?_⟩
  subst hσ
  have hat := setCap_at hy
  have hk := (setCap_out hy).1 sl.1
  show (σ.kheap sl.1).isSome = true
  rw [← hk]
  unfold capAt at hat
  cases e : y.2.kheap sl.1 with
  | none => simp [e] at hat
  | some _ => rfl

/-! ## The reset as an `IK` family -/

/-- `UtInv'` with the reset's facts. -/
def PR (src : CslotPtr) (dev : Bool) (b : ObjRef) (n : Nat) (t : Cdt) (σ : State Unit) : Prop :=
  UtInv' σ ∧ RSV src dev b n t (uV σ)

section PRs
variable {src : CslotPtr} {dev : Bool} {b : ObjRef} {n : Nat} {t : Cdt}

theorem ik_PR_setCap {f : Nat} (hf : f ≤ 2 ^ n) : IK (PR src dev b n t) (setCap (Z := Unit) (.untypedCap dev b n f) src) := by
  intro σ hσ y hy
  obtain ⟨e, hex⟩ := hv_setCap_ex _ _ (uV σ) σ rfl y hy
  show UtInv'V (uV y.2) ∧ RSV src dev b n t (uV y.2)
  rw [e]; exact rs_setCap hσ.1 hσ.2 hex hf

theorem ik_PR_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (PR src dev b n t) m :=
  ik_of_uk (fun σ σ' e h => ⟨by show UtInv'V (uV σ'); rw [e]; exact h.1, by show RSV _ _ _ _ _ (uV σ'); rw [e]; exact h.2⟩) h

theorem ik_PR_mach {α : Type} (mop : NonDet MachineState α) : IK (PR src dev b n t) (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) mop

end PRs

theorem ike_mapMEx_mem {P : State Unit → Prop} {ε α γ : Type} {F : α → NonDetE (State Unit) ε γ} :
    ∀ xs : List α, (∀ a ∈ xs, IKE P (F a)) → IKE P (NonDetE.mapMEx F xs)
  | [], _ => by unfold NonDetE.mapMEx; exact ike_pure _
  | a :: as, h => by
    unfold NonDetE.mapMEx
    exact ike_bind (h a (List.mem_cons.2 (Or.inl rfl))) fun _ =>
      ike_mapMEx_mem as fun x hx => h x (List.mem_cons.2 (Or.inr hx))

/-- The reset's facts from the decode state's: a state whose caps are some of
the old ones, with the same CDT and no object in the region. -/
theorem rsv_mk {σ : State Unit} (hI : UtInv' σ) {src : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some src) {w : UView}
    (h1 : (∃ f, w.2.1 src = some (.untypedCap dev b n f)) ∨ w.1 src.1 = false)
    (h2 : ∀ q, w.1 q = true → q.toNat ∉ utR b n) (hcdt : w.2.2.1 = σ.cdt)
    (hsub : ∀ s2 c, w.2.1 s2 = some c → capAt σ s2 = some c) : RSV src dev b n σ.cdt w := by
  obtain ⟨hW1, hW2, -⟩ := hI.1.2.1 src dev b n fi hc
  refine ⟨h1, h2, hcdt, hk, fun s2 d2 b2 n2 f2 hne hc2 => ?_, hW1, hW2⟩
  have hc2' := hsub s2 _ hc2
  refine ⟨UtDesc.noKids hI.1.2.2.2.1 hc hk (Ne.symm hne) hc2', fun hov => ?_⟩
  rcases hI.1.2.2.2.1 src s2 dev b n fi d2 b2 n2 f2 (Ne.symm hne) hc hc2' hov with ⟨hd, -⟩ | ⟨hd, -⟩
  · exact absurd hd (desc_noKids hk)
  · exact hd

theorem prfi_mem {i c f n : Nat} {l : List Nat}
    (hi : i ∈ (l.filter (fun i => decide (i * 2 ^ c < f))).reverse) (hf : f ≤ 2 ^ n) : i * 2 ^ c ≤ 2 ^ n := by
  have hi' := List.mem_filter.1 (List.mem_reverse.1 hi)
  have hlt : i * 2 ^ c < f := of_decide_eq_true hi'.2
  omega

macro "pr_auto" : tactic => `(tactic| repeat' (first
  | (exact ik_PR_setCap (Nat.zero_le _))
  | (exact ik_PR_setCap (prfi_mem (by assumption) (by assumption)))
  | (exact ik_PR_mach _)
  | (exact ik_PR_uk fun _ => uk_preemptionPoint)
  | (exact ik_PR_uk fun _ => uk_archPostResetUntyped _ _)
  | (refine ike_mapMEx_mem _ fun _ _ => ?_)
  | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE)))

/-- **`reset_untyped_cap` keeps `UtInv'`** and leaves the reset's facts
(every outcome, finished or preempted). -/
theorem reset_utInv' {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) {src : CslotPtr} {dev : Bool}
    {b : ObjRef} {n fi : Nat} (hc : capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some src) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) src) σ).1, PR src dev b n σ.cdt y.2 := by
  intro y hy
  obtain ⟨hn, hfit⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc
  have hfi : fi ≤ 2 ^ n := (hI.1.2.1 src dev b n fi hc).2.2
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s⟩ := x
  obtain ⟨hs, hcx⟩ := getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    subst h0
    refine ⟨hI, rsv_mk hI hc hk (Or.inl ⟨0, hc⟩) (fun q hq hm => ?_) rfl fun _ _ h => h⟩
    exact hI.1.1 src dev b n 0 hc q hq ⟨by have := hm.1; omega, hm.2⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    simp only [bitsOf, objRefOf] at hz
    obtain ⟨hk', hcdt, -, -⟩ := deleteObjects_kheap hz
    have hcapz : ∀ sl, capAt z.2 sl = if sl.1 ∈ delR b n then none else capAt σ sl := by
      intro sl; unfold capAt; rw [hk' sl.1]; split_ifs <;> rfl
    have hz0 : PR src dev b n σ.cdt z.2 := by
      refine ⟨⟨ik_deleteObjects_utInv b n σ hI.1 z hz, fun c q h => ?_, fun x hx => ?_⟩, ?_⟩
      · have h' : σ.cdt c = some q := by rw [← hcdt]; exact h
        obtain ⟨cap, hcq, hcn⟩ := hI.2.1 c q h'
        refine ⟨cap, ?_, hcn⟩
        show capAt z.2 q = _
        rw [hcapz, if_neg (hDT src dev b n fi hc hk c q h')]; exact hcq
      · have hx' : Relation.TransGen (parentOf σ.cdt) x x := by rw [← hcdt]; exact hx
        exact hI.2.2 x hx'
      · refine rsv_mk hI hc hk ?_ (fun q hq hm => ?_) hcdt (fun s2 c hc2 => ?_)
        · by_cases hm : src.1 ∈ delR b n
          · right; show (z.2.kheap src.1).isSome = false; rw [hk', if_pos hm]; rfl
          · left; exact ⟨fi, by show capAt z.2 src = _; rw [hcapz, if_neg hm]; exact hc⟩
        · have hq' : (z.2.kheap q).isSome = true := hq
          rw [hk', if_pos ((mem_delR_iff hn hfit q).2 hm)] at hq'; cases hq'
        · have hc2' : capAt z.2 s2 = some c := hc2
          rw [hcapz] at hc2'
          split_ifs at hc2'
          exact hc2'
    refine (?_ : IKE (PR src dev b n σ.cdt) _) z.2 hz0 y hy
    pr_auto

end

end Fl4Proofs.P3.SInvU
