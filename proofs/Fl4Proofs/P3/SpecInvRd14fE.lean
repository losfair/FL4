/-
P3 (DESIGN.md §9), invariant line G1 (rd14f, KENTRY-PLAN rd14e-3): **the
deletion walk** — `rec_del`, `cap_delete`, `cap_revoke` keep `DW σ0` beside
rd8f's `RB` and ctq14's `CKC` (spec side only).

* `J σ0 I := RB ct I ∧ CKC ct ∧ DW σ0` (ct = σ0's current thread), `JS := J ∧
  Suff`; **`HJ σ0 I m`**: from a `JS` state every outcome is `J`, every `ok`
  outcome `Suff` (the error outcomes are preemption points that threw, after
  a time stamp without a sufficiency check). Combinators `hj_bind`, `hj_lift`,
  `hj_ret`, `hj_whenE`, **`hj_lfp`** (rd8f's `ik_lfp` with the outcome-dependent
  post, through SpecInvNativeScopeK's `ik_lfp_le`).
* Steps: `j_ro`, `j_getCap`, `j_emptySlot` (`sv14f_postCapDeletion`),
  `j_capSwapForDelete`, `j_setCap_cov` (rd8f's covered write), `j_finaliseCap`
  (rd8f's `rb_finaliseCap` with the slot's cap, ctq14's `ck_finaliseCap`,
  rd14f D's `dws_finaliseCap`), **`hj_preemptionPoint`** (rd14f C).
* **`hj_recDelF`** (rd8f's `rb_recDelF` skeleton), **`hj_recDel`**,
  **`hj_capDelete`**, `hj_capRevokeF`, **`hj_capRevoke`**.
-/
import Fl4Proofs.P3.SpecInvRd14fD
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Leaves -/

theorem sv14f_postCapDeletion (c : Cap) : SVK.SVM (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion
  split
  · unfold deletedIrqHandler setIrqState; sv_auto
  · unfold archPostCapDeletion
    split
    · unfold freeIoportRange; sv_auto
    · sv_auto
  · sv_auto

theorem cfk14f_postCapDeletion (c : Cap) : CFK (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion
  split
  · unfold deletedIrqHandler setIrqState; cfk_auto
  · unfold archPostCapDeletion
    split
    · unfold freeIoportRange; cfk_auto
    · cfk_auto
  · cfk_auto

theorem sv14f_emptySlot (sl : CslotPtr) (ci : Cap) : SVK.SVM (emptySlot (Z := Unit) sl ci) := by
  simp only [emptySlot, setCdt]
  sv_auto
  all_goals first | exact sv14f_postCapDeletion _ | (unfold setOriginal; sv_auto)

theorem cfk14f_emptySlot (sl : CslotPtr) (ci : Cap) : CFK (emptySlot (Z := Unit) sl ci) := by
  simp only [emptySlot, setCdt]
  cfk_auto
  all_goals first | exact cfk14f_postCapDeletion _ | (unfold setOriginal; cfk_auto)

theorem sv14f_capSwapForDelete (a b : CslotPtr) : SVK.SVM (capSwapForDelete (Z := Unit) a b) := by
  simp only [capSwapForDelete, capSwap, setCdt]; sv_auto

/-! ## The carried facts and the triple -/

/-- rd8f's `RB`, ctq14's `CKC` (both at σ0's current thread) and `DW σ0`. -/
abbrev J (σ0 : State Unit) (I : ObjRef) (s : State Unit) : Prop :=
  B8f.RB σ0.curThread I s ∧ R14.CKC σ0.curThread s ∧ DW σ0 s

abbrev JS (σ0 : State Unit) (I : ObjRef) (s : State Unit) : Prop := J σ0 I s ∧ Suff s

/-- **The triple** (module docstring). -/
def HJ (σ0 : State Unit) (I : ObjRef) {α : Type} (m : NonDetE (State Unit) Unit α) : Prop :=
  σ0.curThread ≠ σ0.idleThread → ∀ s, JS σ0 I s → ∀ y ∈ (m.run s).1, J σ0 I y.2 ∧ (∀ a, y.1 = .ok a → Suff y.2)

variable {σ0 : State Unit} {I : ObjRef}

theorem hj_bind {α β : Type} {m : NonDetE (State Unit) Unit α} {g : α → NonDetE (State Unit) Unit β}
    (hm : HJ σ0 I m) (hg : ∀ a, HJ σ0 I (g a)) : HJ σ0 I (m >>= g) := by
  intro hni s hs y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨h1, h2⟩ := hm hni s hs z hz
    exact hg a hni z.2 ⟨h1, h2 a ha⟩ y hy
  · exact ⟨(hm hni s hs z hz).1, fun a h => by simp at h⟩

theorem hj_lift {α : Type} {m : NonDet (State Unit) α} (h : ∀ s, JS σ0 I s → ∀ y ∈ (m s).1, JS σ0 I y.2) :
    HJ σ0 I (NonDetE.liftE m) := by
  intro _ s hs y hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact ⟨(h s hs x hx).1, fun _ _ => (h s hs x hx).2⟩

theorem hj_ret {α : Type} (a : α) : HJ σ0 I (NonDetE.returnOk a : NonDetE (State Unit) Unit α) := by
  intro _ s hs y hy
  rw [SInvU.mem_ret_ok hy]
  exact ⟨hs.1, fun _ _ => hs.2⟩

theorem hj_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) Unit Unit} (h : HJ σ0 I m) :
    HJ σ0 I (NonDetE.whenE P m) := by
  unfold NonDetE.whenE
  split
  · exact h
  · exact hj_ret ()

/-- **The least fixed point** keeps the triple. -/
theorem hj_lfp {ι α : Type} {F : (ι → NonDet (State Unit) (Except Unit α)) → ι → NonDet (State Unit) (Except Unit α)}
    (hF : ∀ f : ι → NonDet (State Unit) (Except Unit α), (∀ k, HJ σ0 I (f k : NonDetE (State Unit) Unit α)) →
      ∀ k, HJ σ0 I (F f k : NonDetE (State Unit) Unit α)) (i : ι) :
    HJ σ0 I (NonDet.lfp F i : NonDetE (State Unit) Unit α) := by
  intro hni σ hσ x hx
  let f : ι → NonDet (State Unit) (Except Unit α) := fun _ t =>
    ({y | JS σ0 I t → J σ0 I y.2 ∧ (∀ a, y.1 = .ok a → Suff y.2)}, True)
  have hf : ∀ k t, F f k t ≤ f k t := fun k t =>
    ⟨fun y hy => fun ht => hF f (fun _ _ _ hs0 _ hz => hz hs0) k hni t ht y hy, fun _ => trivial⟩
  exact (ik_lfp_le F f hf i σ).1 hx hσ

/-! ## Steps -/

theorem j_ro {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ1, IK (· = σ1) m) :
    ∀ s, JS σ0 I s → ∀ y ∈ (m s).1, JS σ0 I y.2 :=
  fun _ hs _ hy => (cq5_ro h hy) ▸ hs

theorem j_getCap (sl : CslotPtr) : ∀ s, JS σ0 I s → ∀ y ∈ (getCap (Z := Unit) sl s).1, JS σ0 I y.2 :=
  j_ro fun _ => by unfold getCap; repeat' (first | ik_step0 | ik_unfold)

theorem j_of {α : Type} {m : NonDet (State Unit) α} (hR : IK (B8f.RB σ0.curThread I) m)
    (hC : IK (R14.CKC σ0.curThread) m) (hD : IK (DWS σ0) m) : ∀ s, JS σ0 I s → ∀ y ∈ (m s).1, JS σ0 I y.2 :=
  fun s hs y hy =>
    ⟨⟨hR s hs.1.1 y hy, hC s hs.1.2.1 y hy, (hD s ⟨hs.1.2.2, hs.2⟩ y hy).1⟩, (hD s ⟨hs.1.2.2, hs.2⟩ y hy).2⟩

theorem j_emptySlot (sl : CslotPtr) (ci : Cap) : ∀ s, JS σ0 I s → ∀ y ∈ (emptySlot (Z := Unit) sl ci s).1, JS σ0 I y.2 :=
  j_of (B8f.rb_emptySlot sl ci) (by ckc_leaf) (dst_svcf (sv14f_emptySlot sl ci) (cfk14f_emptySlot sl ci)).dws

theorem j_capSwapForDelete (a b : CslotPtr) :
    ∀ s, JS σ0 I s → ∀ y ∈ (capSwapForDelete (Z := Unit) a b s).1, JS σ0 I y.2 :=
  j_of (B8f.rb_capSwapForDelete a b) (by ckc_leaf)
    (dst_svcf (sv14f_capSwapForDelete a b) (cfk_capSwapForDelete' a b)).dws

theorem j_setCap_cov (c : Cap) (sl : CslotPtr) (s : State Unit) (hcov : SInvU.CovBy (SInvU.uV s).2.1 c)
    (hs : JS σ0 I s) {y : Unit × State Unit} (hy : y ∈ (setCap (Z := Unit) c sl s).1) : JS σ0 I y.2 := by
  have hD := (dst_svcf (SVK.sv_setCap c sl) (cfk_setCap c sl)).dws (σ0 := σ0) s ⟨hs.1.2.2, hs.2⟩ y hy
  exact ⟨⟨B8f.rb_setCap_cov c sl s hcov hs.1.1 hy,
    (by ckc_leaf : IK (R14.CKC σ0.curThread) (setCap (Z := Unit) c sl)) s hs.1.2.1 y hy, hD.1⟩, hD.2⟩

theorem j_finaliseCap (c : Cap) (fin : Bool) (s : State Unit) (sl : CslotPtr) (hc : SInvU.capAt s sl = some c)
    (hni : σ0.curThread ≠ σ0.idleThread) (hs : JS σ0 I s) {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) c fin s).1) : JS σ0 I y.2 := by
  have hD := dws_finaliseCap c fin ⟨hs.1.2.2, hs.2⟩ hs.1.2.1.1 hs.1.1.2.2.2.1 hs.1.1.2.1.1.2.2 hni y hy
  exact ⟨⟨B8f.rb_finaliseCap c fin s sl hc hs.1.1 hy, R14.ck_finaliseCap _ c fin s hs.1.2.1 y hy, hD.1⟩, hD.2⟩

/-- **`preemption_point`** keeps the triple. -/
theorem hj_preemptionPoint : HJ σ0 I (preemptionPoint (Z := Unit)) := by
  intro _ s hs y hy
  obtain ⟨hd, -, hsf⟩ := dw_preemptionPoint ⟨hs.1.2.2, hs.2⟩ hs.1.1.2.2.2.2.1 hy
  exact ⟨⟨B8f.rb_preemptionPoint s hs.1.1 y hy, ⟨R14.ck_preemptionPoint s hs.1.2.1.1 y hy, hd.ct⟩, hd⟩, hsf⟩

/-! ## `rec_del` -/

/-- **One step of `rec_del`** (rd8f's `rb_recDelF` skeleton). -/
theorem hj_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HJ σ0 I (f k : NonDetE (State Unit) Unit (Bool × Cap))) (k : RecDelCall) :
    HJ σ0 I (recDelF (Z := Unit) f k) := by
  cases k with
  | cTEDeleteCall s e =>
    unfold recDelF withoutPreemption
    refine hj_bind (hrec _) fun r => ?_
    obtain ⟨success, cl⟩ := r
    refine hj_bind (hj_lift ?_) fun _ => hj_ret _
    intro t ht y hy
    unfold NonDet.when at hy
    split at hy
    · exact j_emptySlot _ _ t ht y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact ht
  | finaliseSlotCall sl e =>
    intro hni σ hσ y hy
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
    try dsimp only at hy1
    split at hy1
    · rw [SInvU.mem_ret_ok hy1]; exact ⟨hσ.1, fun _ _ => hσ.2⟩
    · obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hx2)
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rem, cl⟩ := rc
      have hO3 : JS σ0 I σ3 := j_finaliseCap cap _ _ sl hc hni hσ hx3
      have hc3 : SInvU.capAt σ3 sl = some cap := SInvU.finaliseCap_keepAt hc _ _ hx3
      have hcov : SInvU.covR rem ⊆ SInvU.covR cap := SInvU.finaliseCap_cov cap _ _ _ hx3
      try dsimp only at hy3
      split at hy3
      · rw [SInvU.mem_ret_ok hy3]; exact ⟨hO3.1, fun _ _ => hO3.2⟩
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := SInvU.mem_liftE' hz
            rw [SInvU.mem_ret_ok hy4]
            have h4 := j_setCap_cov rem sl σ3 (SInvU.covBy_of hc3 hcov) hO3 hx4
            exact ⟨h4.1, fun _ _ => h4.2⟩
          · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := SInvU.mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hO5 : JS σ0 I σ4 := j_setCap_cov rem sl σ3 (SInvU.covBy_of hc3 hcov) hO3 hx4
          obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy4
          have hI5 := hrec (.reduceZombieCall rem sl e) hni σ4 hO5 z hz
          obtain ⟨a, ha5, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := SInvU.mem_bindE' hy5
            have hI6 := hj_preemptionPoint (σ0 := σ0) (I := I) hni z.2 ⟨hI5.1, hI5.2 a ha5⟩ z6 hz6
            obtain ⟨a6, ha6, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall sl e) hni z6.2 ⟨hI6.1, hI6.2 a6 ha6⟩ y hy6
            · exact ⟨hI6.1, fun _ h => by simp at h⟩
          · exact ⟨hI5.1, fun _ h => by simp at h⟩
  | reduceZombieCall c s e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => intro _ σ _ y hy; exact (SInvU.rz_fail rfl hy).elim
      | succ n =>
        cases e with
        | false =>
          simp only [recDelF, withoutPreemption]
          refine hj_bind (hj_ret _) fun cn => hj_bind (hj_lift (j_ro fun _ => ?_)) fun _ =>
            hj_bind (hj_lift (j_capSwapForDelete _ _)) fun _ => hj_ret _
          exact ik_assert _
        | true =>
          intro hni σ hσ y hy
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
          · obtain rfl := SInvU.mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy
            have hp := hrec (.cTEDeleteCall _ _) hni σ hσ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact ⟨hp.1, fun _ h => by simp at h⟩
            have hp' : JS σ0 I z.2 := ⟨hp.1, hp.2 a ha⟩
            obtain ⟨z2, hz2, ⟨nc, hnc, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
            swap
            · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2
              rw [hx] at her; cases her
            obtain ⟨⟨nc', σ5⟩, hx5, rfl⟩ := SInvU.mem_liftE' hz2
            cases hnc
            obtain ⟨e5, hc5⟩ := SInvU.getCap_capAt hx5
            simp only at e5 hc5
            subst e5
            try dsimp only at hy
            split at hy
            · rename_i hnz
              subst hnz
              obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz3
                rw [SInvU.mem_ret_ok hy]
                have h3 := j_setCap_cov (.zombie ptr bits n) s z.2
                  (SInvU.covBy_of hc5 (fun q hq => by simpa [SInvU.covR, SInvU.capRng, objRefs] using hq)) hp' hx
                exact ⟨h3.1, fun _ _ => h3.2⟩
              · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [SInvU.mem_ret_ok hy]
                exact ⟨hp'.1, fun _ _ => hp'.2⟩
              · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := SInvU.mem_ret_ok hz; cases her
    | _ => intro _ σ _ y hy; exact (SInvU.rz_fail rfl hy).elim

/-- **`rec_del` keeps the triple.** -/
theorem hj_recDel (k : RecDelCall) : HJ σ0 I (recDel (Z := Unit) k) := by
  unfold recDel
  exact hj_lfp (fun f hf k => hj_recDelF f hf k) k

/-- **`cap_delete` keeps the triple.** -/
theorem hj_capDelete (sl : CslotPtr) : HJ σ0 I (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact hj_bind (hj_recDel _) fun _ => hj_ret _

theorem hj_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, HJ σ0 I (f k : NonDetE (State Unit) Unit Unit)) (sl : CslotPtr) :
    HJ σ0 I (capRevokeF (Z := Unit) f sl) := by
  unfold capRevokeF withoutPreemption
  refine hj_bind (hj_lift (j_getCap _)) fun cap => ?_
  refine hj_bind (hj_lift (j_ro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun cdt => ?_
  refine hj_bind (hj_ret _) fun ds => ?_
  refine hj_whenE _ ?_
  refine hj_bind (hj_lift (j_ro fun _ => by unfold selectExt; repeat' (first | ik_step0 | ik_unfold))) fun child => ?_
  refine hj_bind (hj_lift (j_getCap _)) fun cap' => ?_
  refine hj_bind (hj_lift (j_ro fun _ => ik_assert _)) fun _ => ?_
  refine hj_bind (hj_capDelete _) fun _ => ?_
  refine hj_bind hj_preemptionPoint fun _ => ?_
  exact hrec _

/-- **`cap_revoke` keeps the triple.** -/
theorem hj_capRevoke (sl : CslotPtr) : HJ σ0 I (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact hj_lfp (fun f hf k => hj_capRevokeF hf k) sl

end

end Fl4Proofs.P3.SInvR.A14f
