/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut7): **the CNode
invocations keep `P3 N`, from the decode's facts** (spec side only; imports
SpecInvUtO3).

* `refEq_mask` / `refEq_upd` / `refEq_trans`: `mask_cap` and `update_cap_data`
  keep a cap's covered range, shape, Zombie- and untyped-ness (`RefEq`);
  `refRel_of_eq_rel` composes with `derive_cap`'s `RefRel`.
* `CnOKN w ci` (what the CNode performs need: the inserted cap `CI3`, the moved
  and rotated caps `RefEq` to the slots' caps, destinations `DestRefV`) and
  **`okv_decodeCnodeN`** (the CNode decode establishes it, given that the
  invoked cap is in a slot).
* `hv_capMove3`, `hv_capSwap3` (`P3 N` kept by `cap_move` / `cap_swap`) and
  **`p3_invokeCnode`**.
-/
import Fl4Proofs.P3.SpecInvUtO3
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The decode's cap transformations -/

theorem refEq_trans {a b c : Cap} (h1 : RefEq a b) (h2 : RefEq b c) : RefEq a c := by
  rcases h1 with rfl | ⟨h0, ho, hs, hz, hz0, hu, hu0, hr⟩
  · exact h2
  · rcases h2 with rfl | ⟨-, ho', hs', hz', -, hu', -, hr'⟩
    · exact Or.inr ⟨h0, ho, hs, hz, hz0, hu, hu0, hr⟩
    · exact Or.inr ⟨h0, ho'.trans ho, hs'.trans hs, hz', hz0, hu', hu0, hr'.trans hr⟩

theorem refRel_of_eq_rel {a b c : Cap} (h1 : RefEq a b) (h2 : RefRel b c) : RefRel a c := by
  rcases h1 with rfl | ⟨-, -, hs, -, hz0, -, -, hr⟩
  · exact h2
  · obtain ⟨hR, hS, hZ, -, hU⟩ := h2
    exact ⟨hr ▸ hR, hS.trans hs, hZ, fun r b n e => absurd e (hz0 r b n), hU⟩

theorem covR_of_refEq {c0 c : Cap} (h : RefEq c0 c) : covR c = covR c0 := by
  rcases h with rfl | ⟨-, -, -, -, -, hu, hu0, hr⟩
  · rfl
  · rw [covR_nonUt hu, covR_nonUt hu0, hr]

theorem capRel_of_refEq {c0 c : Cap} (h : RefEq c0 c) (hc : c ≠ .nullCap) : CapRel c0 c := by
  refine ⟨h.nn hc, hc, ?_⟩
  rcases h with rfl | ⟨-, -, -, -, -, hu, hu0, -⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hu, hu0⟩

macro "refeq_right" : tactic => `(tactic| (right; exact ⟨by assumption, rfl, rfl, fun _ _ _ e => (by cases e),
  fun _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), rfl⟩))

theorem refEq_mask (r : CapRights) {c : Cap} (h0 : c ≠ .nullCap) : RefEq c (maskCap r c) := by
  cases c with
  | archObjectCap a => cases a <;> first | (left; rfl) | refeq_right
  | _ => first | exact absurd rfl h0 | (left; rfl) | refeq_right

theorem refEq_upd (p : Bool) (x : Data) {c : Cap} (h0 : c ≠ .nullCap) (hn : updateCapData p x c ≠ .nullCap) :
    RefEq c (updateCapData p x c) := by
  cases c with
  | endpointCap o b R =>
    unfold updateCapData at hn ⊢
    simp only [isEpCap, ↓reduceIte] at hn ⊢
    split
    · refeq_right
    · rename_i h; rw [if_neg h] at hn; exact absurd rfl hn
  | notificationCap o b R =>
    unfold updateCapData at hn ⊢
    simp only [isEpCap, isNtfnCap, Bool.false_eq_true, ↓reduceIte] at hn ⊢
    split
    · refeq_right
    · rename_i h; rw [if_neg h] at hn; exact absurd rfl hn
  | cnodeCap o b g =>
    have e : updateCapData p x (.cnodeCap o b g) = if (updateCnodeCapData x).1 + b > wordBits then .nullCap
        else .cnodeCap o b ((toBl (updateCnodeCapData x).2).drop (64 - (updateCnodeCapData x).1)) := by
      first | rfl | (simp only [updateCapData, isEpCap, isNtfnCap, isCnodeCap, theCnodeCap, Bool.false_eq_true,
        ↓reduceIte]; done)
    rw [e] at hn ⊢
    by_cases h : (updateCnodeCapData x).1 + b > wordBits
    · rw [if_pos h] at hn; exact absurd rfl hn
    · rw [if_neg h]; refeq_right
  | archObjectCap a => left; rfl
  | _ => first | exact absurd rfl h0 | (left; rfl)

theorem upd_null (p : Bool) (x : Data) : updateCapData p x .nullCap = .nullCap := rfl

theorem okv_and {ε α : Type} {w : UView} {P Q : α → Prop} {m : NonDetE (State Unit) ε α} (h1 : OkV w P m)
    (h2 : OkV w Q m) : OkV w (fun a => P a ∧ Q a) m :=
  fun σ hσ a s hs => ⟨h1 σ hσ a s hs, h2 σ hσ a s hs⟩

theorem okv_deriveCap_nn {w : UView} (sl : CslotPtr) (c : Cap) :
    OkV w (fun nc => nc ≠ .nullCap → c ≠ .nullCap) (deriveCap (Z := Unit) sl c) := by
  intro σ _ a s h hn e
  subst e
  rw [show deriveCap (Z := Unit) sl .nullCap = NonDetE.returnOk .nullCap from rfl] at h
  have e := Set.mem_singleton_iff.1 h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  exact hn e.1

/-! ## The CNode decode -/

/-- What the CNode performs need from the decode. -/
def CnOKN (w : UView) : CnodeInvocation → Prop
  | .insertCall c src dest => CI3 w c src ∧ DestRefV w dest
  | .moveCall c src dest => ∃ c0, w.2.1 src = some c0 ∧ w.2.1 dest = some .nullCap ∧ RefEq c0 c ∧
      c ≠ .nullCap ∧ src ≠ dest ∧ DestRefV w dest
  | .rotateCall c1 c2 s1 s2 s3 => ∃ c1' c2', w.2.1 s1 = some c1' ∧ w.2.1 s2 = some c2' ∧ RefEq c1' c1 ∧
      c1 ≠ .nullCap ∧ RefEq c2' c2 ∧ c2 ≠ .nullCap ∧ s2 ≠ s1 ∧ s2 ≠ s3 ∧ DestRefV w s3 ∧
      (s1 ≠ s3 → w.2.1 s3 = some .nullCap)
  | _ => True

set_option maxHeartbeats 4000000 in
/-- **The CNode decode's checks for `P3`.** -/
theorem okv_decodeCnodeN {w : UView} (label : Data) (args : List Data) (cap : Cap) (ex : List Cap)
    (hroot : ∃ s, w.2.1 s = some cap) :
    OkV w (CnOKN w) (decodeCnodeInvocation (Z := Unit) label args cap ex) := by
  unfold decodeCnodeInvocation
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind
    (okv_returnOk_bind (okv_bind (fun _ => uk_lookupTargetSlot _ _ _)
      (okv_lookupSlotForCnodeOpN false cap _ _ hroot) fun destSlot hdr => ?_)))
  refine okv_ite ?_ (okv_ite (okv_returnOk trivial) (okv_ite (okv_returnOk trivial) (okv_ite ?_ (okv_ite ?_ (okv_throw _)))))
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))
    refine okv_bind (fun _ => uk_ensureEmpty _) (okv_ensureEmpty _) fun _ hd => ?_
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun hnn => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun x => ?_
    obtain ⟨rights, capData, isMove⟩ := x
    dsimp only
    refine okv_returnOk_bind ?_
    have hm := refEq_mask rights hnn
    have hk1 : (match capData with
        | some x => updateCapData isMove x (maskCap rights srcCap)
        | none => maskCap rights srcCap) ≠ .nullCap → RefEq srcCap (match capData with
        | some x => updateCapData isMove x (maskCap rights srcCap)
        | none => maskCap rights srcCap) := by
      intro hn
      cases capData with
      | none => exact hm
      | some x =>
        have hmn : maskCap rights srcCap ≠ .nullCap := by
          intro e; apply hn; simp only; rw [e]; rfl
        exact refEq_trans hm (refEq_upd _ _ hmn hn)
    cases isMove
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine okv_bind (fun _ => uk_deriveCap _ _) (okv_and (okv_deriveCapR _ _) (okv_deriveCap_nn _ _))
        fun nc hnc => okv_whenE_bind fun hncn => okv_returnOk ?_
      have hc1 := hnc.2 hncn
      have he := hk1 hc1
      refine ⟨⟨srcCap, hsc, ?_⟩, hdr⟩
      rcases hnc.1 hncn with ⟨e1, ⟨d, b, n, f, e2⟩, hk⟩ | hR
      · rcases he with e3 | ⟨-, -, -, -, -, hu, -, -⟩
        · exact Or.inl ⟨e1.trans e3, ⟨d, b, n, f, e3.symm.trans e2⟩, hk⟩
        · exact absurd e2 (hu d b n f)
      · exact Or.inr (refRel_of_eq_rel he hR)
    · simp only [↓reduceIte]
      refine okv_returnOk_bind (okv_whenE_bind fun hnn2 => okv_returnOk ?_)
      refine ⟨srcCap, hsc, hd, hk1 hnn2, hnn2, ?_, hdr⟩
      intro e; subst e; rw [hd] at hsc; exact hnn (Option.some.inj hsc).symm
  · repeat' okv_step
    all_goals exact okv_returnOk trivial
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind
      (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))))))
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_bind_uk (fun _ => uk_lookupPivotSlot _ _ _) fun pivotSlot => ?_
    refine okv_whenE_bind fun hpv => ?_
    refine okv_bind (Q := fun _ => srcSlot ≠ destSlot → w.2.1 destSlot = some .nullCap) (fun _ => by uk_auto) ?_
      fun _ hd => ?_
    · unfold NonDetE.unlessE
      split
      · rename_i hc; exact okv_pure fun h => absurd hc h
      · exact okv_mono (okv_ensureEmpty _) fun _ h _ => h
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun hn1 => ?_
    refine okv_liftE_getCap_bind fun pivCap hpc => okv_whenE_bind fun hn2 => ?_
    refine okv_returnOk_bind (okv_returnOk_bind (okv_whenE_bind fun hn3 => okv_whenE_bind fun hn4 => okv_returnOk ?_))
    exact ⟨srcCap, pivCap, hsc, hpc, refEq_upd _ _ hn1 hn3, hn3, refEq_upd _ _ hn2 hn4, hn4,
      fun e => hpv (Or.inl e), fun e => hpv (Or.inr e), hdr, hd⟩

/-! ## Move and swap -/

variable {N : Irq → ObjRef}

/-- **`cap_move` of a `RefEq` cap to a null `PosOK` slot keeps `P3 N`.** -/
theorem hv_capMove3 {w : UView} (hI : P3V N w) {c0 c : Cap} {src dest : CslotPtr}
    (hs : w.2.1 src = some c0) (hd : w.2.1 dest = some .nullCap) (hre : RefEq c0 c) (hc : c ≠ .nullCap)
    (hpd : PosOK w dest) (hne : src ≠ dest) :
    HV (· = w) (fun w' => P3V N w' ∧ w'.2.1 src = some .nullCap ∧ w'.2.1 dest = some c ∧
      ∀ x, x ≠ src → x ≠ dest → w'.2.1 x = w.2.1 x) (capMove (Z := Unit) c src dest) := by
  intro σ hσ y hy
  obtain ⟨hU, h1, h2, h3⟩ := hv_capMoveN hI.1 hs hd (capRel_of_refEq hre hc) hre hpd hne σ hσ y hy
  refine ⟨⟨hU, ?_⟩, h1, h2, h3⟩
  obtain ⟨-, hO, hA⟩ := hI.1.1
  have hkd : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hss : w.2.2.1 src ≠ some src := fun h => hA src (Relation.TransGen.single h)
  have hv := capMove_view (c := c) hne hd hss (hkd src) hkd σ hσ y hy
  rw [hv]
  exact irqOut_cd hI.2 (cd_upd cd_vRen (covBy_of hs (by rw [covR_of_refEq hre])) dest)

/-- **`cap_swap` of `RefEq` caps keeps `P3 N`.** -/
theorem hv_capSwap3 {s1 s2 : CslotPtr} (hne : s1 ≠ s2) {c1' c2' c1 c2 : Cap} (h1e : RefEq c1' c1)
    (h2e : RefEq c2' c2) (hn1 : c1 ≠ .nullCap) (hn2 : c2 ≠ .nullCap) :
    HV (fun w => P3V N w ∧ w.2.1 s1 = some c1' ∧ w.2.1 s2 = some c2') (P3V N)
      (capSwap (Z := Unit) c1 s1 c2 s2) := by
  refine hv_pin fun w ⟨hI, h1, h2⟩ => ?_
  intro σ hσ y hy
  have hU := hv_capSwapN hne (capRel_of_refEq h1e hn1) (capRel_of_refEq h2e hn2) h1e h2e σ
    (by rw [hσ]; exact ⟨hI.1, h1, h2⟩) y hy
  refine ⟨hU, ?_⟩
  have hv := capSwap_view (w := w) hne c1 c2 σ hσ y hy
  rw [hv]
  exact irqOut_cd hI.2 (cd_upd (cd_upd cd_vRen (covBy_of h2 (by rw [covR_of_refEq h2e])) s1)
    (covBy_of h1 (by rw [covR_of_refEq h1e])) s2)

/-! ## The CNode performs -/

/-- **`invoke_cnode` keeps `P3 N`** from the decode's facts. -/
theorem p3_invokeCnode (ci : CnodeInvocation) (σ : State Unit) (hI : P3 N σ) (hok : CnOKN (uV σ) ci) :
    ∀ y ∈ ((invokeCnode (Z := Unit) ci).run σ).1, P3 N y.2 := by
  intro y hy
  cases ci with
  | revokeCall d => exact un_capRevoke d σ hI y hy
  | deleteCall d => exact p3_capDelete d σ hI y hy
  | insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact hv_capInsert3 c src dest σ ⟨hI, hok.1, posOK_of_destRef hI.1.2 hok.2⟩ x hx
  | moveCall c src dest =>
    obtain ⟨c0, hs, hd, hre, hc, hne, hdr⟩ := hok
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (hv_capMove3 hI hs hd hre hc (posOK_of_destRef hI.1.2 hdr) hne σ rfl x hx).1
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, hr1, hn1, hr2, hn2, h21, h23, hdr, h3⟩ := hok
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · exact hv_capSwap3 (Ne.symm h21) hr1 hr2 hn1 hn2 σ ⟨hI, h1, h2⟩ x hx
    · rename_i h13
      obtain ⟨x1, hx1, hx⟩ := hx
      have hP2 : PosOK (uV σ) s2 := posOK_of_nn hI.1.2 h2 (hr2.nn hn2)
      obtain ⟨hI1, hs1, hd1, hoth⟩ :=
        hv_capMove3 hI h2 (h3 h13) hr2 hn2 (posOK_of_destRef hI.1.2 hdr) h23 σ rfl x1 hx1
      have h1' : (uV x1.2).2.1 s1 = some c1' := by
        rw [hoth s1 (Ne.symm h21) h13]; exact h1
      have hP2' : PosOK (uV x1.2) s2 := posOK_move h2 hr2 hs1 hd1 hoth (h3 h13) hP2
      exact (hv_capMove3 hI1 h1' hs1 hr1 hn1 hP2' (Ne.symm h21) x1.2 rfl x hx).1
  | cancelBadgedSendsCall cap =>
    cases cap
    case endpointCap ep b r =>
      exact (show IKE (P3 N) (withoutPreemption (Z := Unit) (NonDet.when (b ≠ 0) (cancelBadgedSends ep b))) by
        un_auto) σ hI y hy
    all_goals
      obtain ⟨x, hx, -⟩ := mem_liftE' (show y ∈ ((NonDetE.liftE (ε := Unit)
        (NonDet.fail : NonDet (State Unit) Unit)).run σ).1 from hy)
      exact hx.elim

end

end Fl4Proofs.P3.SInvU
