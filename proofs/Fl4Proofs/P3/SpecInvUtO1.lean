/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut7): **the IRQ-node fact
alone, `IO N σ := IrqOutV N (uV σ)`, kept by the cap writers that need no
decode fact** (spec side only; imports SpecInvUtN8).

`IrqOutV N` (ut6) is antitone along cap domination (`CD`), so a writer keeps it
whenever every address a cap it writes covers was covered before (`CovBy`).
This holds with NO other premise for `empty_slot` / `cap_delete_one`, for
`cap_swap_for_delete`, for `finalise_cap` (it only deletes, through
`deleting_irq_handler`), for the whole of `rec_del` (the written remainder is a
Zombie of the finalised cap's object, `finaliseCap_cov`, and the cap is still
in its slot after `finalise_cap`, `finaliseCap_keepAt`; the Zombie shrink writes
a Zombie of the object of the Zombie it replaces), and for `cap_insert` of a cap
covered by the source's cap (`hv_capInsertIO`; `set_untyped_cap_as_full` keeps
the source's region), so for the TCB installs' `check_cap_at` inserts
(`same_object_as` gives `RefRel`). With `IK UtInv''` (ut4-ut6) these give
`IK (P3 N)` for `P3 N σ := UtInv'' σ ∧ IO N σ`.
-/
import Fl4Proofs.P3.SpecInvUtN8
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The IRQ-node fact on a state, for a fixed node map `N`. -/
abbrev IO (N : Irq → ObjRef) (σ : State Unit) : Prop := IrqOutV N (uV σ)

/-- Every address `c` covers is covered by a cap of `m`. -/
def CovBy (m : CslotPtr → Option Cap) (c : Cap) : Prop :=
  ∀ r, r ∈ covR c → ∃ s c', m s = some c' ∧ r ∈ covR c'

theorem cd_upd {m m0 : CslotPtr → Option Cap} (hm : CD m m0) {c : Cap} (hc : CovBy m0 c) (sl : CslotPtr) :
    CD (Function.update m sl (some c)) m0 := by
  intro s c' r hs hr
  rcases upd_cap hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
  · exact hc r hr
  · exact hm s c' r hs' hr

theorem covBy_of {m : CslotPtr → Option Cap} {s : CslotPtr} {c0 c : Cap} (h : m s = some c0)
    (hs : covR c ⊆ covR c0) : CovBy m c := fun r hr => ⟨s, c0, h, hs hr⟩

theorem covBy_null (m : CslotPtr → Option Cap) : CovBy m .nullCap := fun r hr => by
  rw [covR_null] at hr; exact hr.elim

theorem covBy_cd {m m' : CslotPtr → Option Cap} {c : Cap} (h : CovBy m' c) (hd : CD m' m) : CovBy m c :=
  fun r hr => by obtain ⟨s, c', hs, hr'⟩ := h r hr; exact hd s c' r hs hr'

theorem covR_sub_of_refRel {c0 c : Cap} (h : RefRel c0 c) : covR c ⊆ covR c0 := by
  rw [covR_nonUt h.2.2.2.2]; exact fun r hr => capRng_sub_covR _ (h.1 hr)

theorem covR_maxFree (c : Cap) : covR (maxFreeIndexUpdate c) = covR c := by
  cases c <;> rfl

theorem irqOut_vCap {N : Irq → ObjRef} {w : UView} (h : IrqOutV N w) {c : Cap} (hc : CovBy w.2.1 c)
    (sl : CslotPtr) : IrqOutV N (vCap sl c w) :=
  irqOut_cd h (cd_upd (cd_refl _) hc sl)

variable {N : Irq → ObjRef}

/-! ## Frames -/

theorem io_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (IO N) m :=
  ik_of_uk (fun _ _ e hI => by show IrqOutV N _; rw [e]; exact hI) h

theorem ioe_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (IO N) m :=
  io_of_uk h

theorem io_of_dm {α : Type} {m : NonDet (State Unit) α} (h : DMV (fun _ => True) m) : IK (IO N) m :=
  fun σ hσ y hy => irqOut_cd hσ (h (uV σ) trivial σ rfl y hy)

theorem io_capDeleteOne (sl : CslotPtr) : IK (IO N) (capDeleteOne (Z := Unit) sl) :=
  io_of_dm (dm_capDeleteOne sl)

theorem io_emptySlot (s : CslotPtr) (info : Cap) : IK (IO N) (emptySlot (Z := Unit) s info) :=
  io_of_dm (dm_emptySlot s info)

theorem dm_capSwapForDelete (s1 s2 : CslotPtr) : DMV (fun _ => True) (capSwapForDelete (Z := Unit) s1 s2) := by
  intro w _
  unfold capSwapForDelete NonDet.when
  split
  · rename_i hne
    refine hv_getCap_bind fun w1 c1 hw h1 => ?_
    subst hw
    refine hv_getCap_bind fun w' c2 hw' h2 => ?_
    subst hw'
    refine hv_mono (capSwap_view hne c1 c2) fun w' e => ?_
    subst e
    exact cd_upd (cd_upd cd_vRen (covBy_of h2 subset_rfl) s1) (covBy_of h1 subset_rfl) s2
  · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w' e => e ▸ cd_refl _

theorem io_capSwapForDelete (s1 s2 : CslotPtr) : IK (IO N) (capSwapForDelete (Z := Unit) s1 s2) :=
  io_of_dm (dm_capSwapForDelete s1 s2)

/-- `set_cap` of a cap covered by the start's caps. -/
theorem hv_setCapIO (c : Cap) (sl : CslotPtr) :
    HV (fun w => IrqOutV N w ∧ CovBy w.2.1 c) (IrqOutV N) (setCap (Z := Unit) c sl) := by
  refine hv_pin fun w hw => ?_
  exact hv_mono (hv_setCap c sl w) fun w' e => e ▸ irqOut_vCap hw.1 hw.2 sl

/-- **`cap_insert` of a cap covered by the source's cap keeps `IrqOut`.** -/
theorem hv_capInsertIO (c : Cap) (src dest : CslotPtr) :
    HV (fun w => IrqOutV N w ∧ ∀ c0, w.2.1 src = some c0 → covR c ⊆ covR c0) (IrqOutV N)
      (capInsert (Z := Unit) c src dest) := by
  refine hv_pin fun w0 hw0 => ?_
  refine hv_mono (Q := fun w' => CD w'.2.1 w0.2.1) ?_ fun w' h => irqOut_cd hw0.1 h
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  subst hw
  have hcov := hw0.2 sc hsc
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun _ => ?_
  unfold setUntypedCapAsFull
  split
  · refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
    subst w2
    refine hv_pure_bind ?_
    refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
    subst w3
    refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
    subst w4
    refine hv_bind (hv_updateCdt _ _) fun _ => ?_
    refine hv_bind (hv_doExtendedOp _) fun _ => ?_
    refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
    subst e
    exact cd_upd (cd_upd (cd_refl _) (covBy_of hsc (by rw [covR_maxFree])) src) (covBy_of hsc hcov) dest
  · refine hv_pure_bind ?_
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
    subst w2
    refine hv_pure_bind ?_
    refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
    subst w3
    refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
    subst w4
    refine hv_bind (hv_updateCdt _ _) fun _ => ?_
    refine hv_bind (hv_doExtendedOp _) fun _ => ?_
    refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
    subst e
    exact cd_upd (cd_refl _) (covBy_of hsc hcov) dest

/-- **The TCB installs' checked insert keeps `IrqOut`** (no premise). -/
theorem io_checkCapAt_ins (c : Cap) (src : CslotPtr) (t : Cap) (sl dest : CslotPtr) :
    IK (IO N) (checkCapAt (Z := Unit) c src (checkCapAt t sl (capInsert c src dest))) := by
  show HV (IrqOutV N) (IrqOutV N) _
  unfold checkCapAt
  refine hv_getCap_bind fun w c' hw hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    refine hv_getCap_bind fun w' c'' hw' _ => ?_
    subst hw'
    split
    · refine hv_pre (hv_capInsertIO c src dest) fun w1 e => ?_
      subst e
      exact ⟨hw, fun c0 h0 => by rw [hc'] at h0; cases h0; exact covR_sub_of_refRel (refRel_of_sameObj hso)⟩
    · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w1 e => e ▸ hw
  · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w1 e => e ▸ hw

/-! ## `finalise_cap` -/

theorem io_finaliseCap (c : Cap) (fin : Bool) : IK (IO N) (finaliseCap (Z := Unit) c fin) := by
  by_cases hirq : ∃ i, c = .irqHandlerCap i
  · obtain ⟨i, rfl⟩ := hirq
    simp only [finaliseCap, deletingIrqHandler, getIrqSlot]
    repeat' (first | exact io_capDeleteOne _ | ik_step0)
  · exact io_of_uk (uk_finaliseCap_nonIrq c (fun i e => hirq ⟨i, e⟩) fin)

/-- `finalise_cap` leaves the finalised cap in its slot. -/
theorem finaliseCap_keepAt {σ : State Unit} {s : CslotPtr} {c : Cap} (hc : capAt σ s = some c) (fin : Bool) :
    ∀ y ∈ (finaliseCap (Z := Unit) c fin σ).1, capAt y.2 s = some c := by
  intro y hy
  by_cases hirq : ∃ i, c = .irqHandlerCap i
  · obtain ⟨i, rfl⟩ := hirq
    simp only [finaliseCap] at hy
    split at hy
    · obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hy]
      unfold deletingIrqHandler getIrqSlot at hz
      obtain ⟨u, hu, hz⟩ := hz
      rw [Set.mem_singleton_iff.1 hu] at hz
      dsimp only at hz
      by_cases e : s = (σ.interruptIrqNode i, [])
      · rw [e] at hc; exact absurd hz (capDeleteOne_irq hc z)
      · exact (capDeleteOne_keep _ s e (uV σ) σ rfl z hz).trans hc
    · rw [Set.mem_singleton_iff.1 hy]; exact hc
  · have hv : uV y.2 = uV σ := uk_finaliseCap_nonIrq c (fun i e => hirq ⟨i, e⟩) fin (uV σ) σ rfl y hy
    show (uV y.2).2.1 s = _
    rw [hv]; exact hc

/-- `finalise_cap`'s remainder covers nothing its cap does not. -/
theorem finaliseCap_cov (c : Cap) (fin : Bool) :
    OV (fun p : Cap × Cap => covR p.1 ⊆ covR c) (finaliseCap (Z := Unit) c fin) := by
  intro σ x hx
  by_cases hsr : sRefs c = ∅
  · rw [finaliseCap_null hsr fin σ x hx, covR_null]; exact Set.empty_subset _
  · cases c with
    | cnodeCap r bits g =>
      simp only [finaliseCap] at hx
      rw [Set.mem_singleton_iff.1 hx]
      dsimp only
      split
      · intro q hq; simpa [covR, capRng, objRefs] using hq
      · rw [covR_null]; exact Set.empty_subset _
    | threadCap r =>
      rw [finaliseCap_thread_val r fin σ x hx]
      split
      · intro q hq; simpa [covR, capRng, objRefs] using hq
      · rw [covR_null]; exact Set.empty_subset _
    | zombie r b n =>
      simp only [finaliseCap] at hx
      obtain ⟨u, -, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
    | _ => exact absurd rfl hsr

/-! ## `rec_del` -/

macro "io0_auto" : tactic => `(tactic| repeat' (first
  | exact io_emptySlot _ _ | exact io_capSwapForDelete _ _
  | (refine io_of_uk fun _ => ?_; uk_leaf; done) | (refine ioe_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem io_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, IK (IO N) (f k)) (k : RecDelCall) :
    IKE (IO N) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (ε := Unit) (IO N) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall s e =>
    unfold recDelF withoutPreemption; io0_auto
    all_goals exact hrec' _
  | finaliseSlotCall sl e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := getCap_capAt hx
    simp only at e1 hc
    subst e1
    try dsimp only at hy1
    split at hy1
    · rw [mem_ret_ok hy1]; exact hσ
    · obtain ⟨z, hz, H⟩ := mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hx2)
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rem, cl⟩ := rc
      have hO3 : IO N σ3 := io_finaliseCap cap _ _ hσ _ hx3
      have hc3 : capAt σ3 sl = some cap := finaliseCap_keepAt hc _ _ hx3
      have hcov : covR rem ⊆ covR cap := finaliseCap_cov cap _ _ _ hx3
      have hO4 : IrqOutV N (vCap sl rem (uV σ3)) := irqOut_vCap hO3 (covBy_of hc3 hcov) sl
      try dsimp only at hy3
      split at hy3
      · rw [mem_ret_ok hy3]; exact hO3
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]
            have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
            show IrqOutV N (uV σ4); rw [hv4]; exact hO4
          · obtain ⟨x, -, hx⟩ := mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
          have hO5 : IO N σ4 := by show IrqOutV N (uV σ4); rw [hv4]; exact hO4
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hI5 : IO N z.2 := hrec _ σ4 hO5 z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : IO N z6.2 := by show IrqOutV N (uV z6.2); rw [hv6]; exact hI5
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec _ z6.2 hI6 y hy6
            · exact hI6
          · exact hI5
  | reduceZombieCall c s e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => intro σ _ y hy; exact (rz_fail rfl hy).elim
      | succ n =>
        cases e with
        | false =>
          simp only [recDelF, withoutPreemption]; io0_auto
        | true =>
          intro σ hσ y hy
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
          · obtain rfl := mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := mem_bindE' hy
            have hp : IO N z.2 := hrec _ σ hσ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact hp
            obtain ⟨z2, hz2, ⟨nc, hnc, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
            swap
            · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
              rw [hx] at her; cases her
            obtain ⟨⟨nc', σ5⟩, hx5, rfl⟩ := mem_liftE' hz2
            cases hnc
            obtain ⟨e5, hc5⟩ := getCap_capAt hx5
            simp only at e5 hc5
            subst e5
            try dsimp only at hy
            split at hy
            · rename_i hnz
              subst hnz
              obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                rw [mem_ret_ok hy]
                have hv := hv_setCap (.zombie ptr bits n) s (uV z.2) z.2 rfl _ hx
                show IrqOutV N (uV x.2)
                rw [hv]
                exact irqOut_vCap hp (covBy_of hc5 (fun q hq => by simpa [covR, capRng, objRefs] using hq)) s
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [mem_ret_ok hy]
                exact hp
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
    | _ => intro σ _ y hy; exact (rz_fail rfl hy).elim

/-- **`rec_del` keeps `IrqOut`** (no premise). -/
theorem io_recDel (c : RecDelCall) : IKE (IO N) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => io_recDelF f hf k) c

theorem io_capDelete (slot : CslotPtr) : IKE (IO N) (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (io_recDel _) fun _ => ike_returnOk _

end

end Fl4Proofs.P3.SInvU
