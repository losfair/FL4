/-
P3 (DESIGN.md §9), invariant line G1 (fo1): **`FT` across `rec_del` /
`cap_delete` / `cap_revoke`** (spec side only).

il2's SpecInvNtfnQLD with the owner carried: `TcSafe` at `K = oL σ` (the
owner as a list) is exactly what `FT` needs of a cap removal — the removed
thread cap is the same cap, or another slot holds one to its thread, or the
thread is dead AND not the owner. A FINAL thread cap's `finalise_cap` ends with
`prepare_thread_delete` = `fpu_release t` (`finThread_owner`: `t` is not the
owner after), so the `Zombie t none 6` over it is safe (`fo_tcs_rem`); a
non-final one has another thread cap (il2's `other_threadCap`).

The induction is il2's (ut5's `hr_lfp`) with `FPre k := RPre k ∧ FN []` and
`FPost` = `RPost` ∧ `FN []` ∧ (a `true` finalise result makes emptying the slot
`TcSafe (oL σ)`). Tops `fo_recDel`, **`fou_capDelete`, `fou_capRevoke : IKE
FU`** with `FU σ := FN [] σ ∧ UtInv'' σ`.
-/
import Fl4Proofs.P3.SpecInvFoA
import Fl4Proofs.P3.SpecInvNtfnQLD
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## Pointwise combinators -/

theorem ilf_pt {α : Type} {K : List ObjRef} {m : NonDet (State Unit) α} {σ : State Unit} {y : α × State Unit}
    (hσ : ILF K σ) (hI : IKp (IL (oL σ ++ K)) σ m) (hO : ∀ q, OIK q m) (hy : y ∈ (m σ).1) : ILF K y.2 :=
  ft_back (hI (il_oL hσ.1 hσ.2) y hy) (hO _ σ ⟨rfl, fun t ht => (hσ.2 t ht).1⟩ y hy)

theorem fn_pt {α : Type} {K : List ObjRef} {m : NonDet (State Unit) α} {σ : State Unit} {y : α × State Unit}
    (hσ : FN K σ) (hI : IKp (IL (oL σ ++ K)) σ m) (hN : NQK [] m) (hO : ∀ q, OIK q m) (hy : y ∈ (m σ).1) :
    FN K y.2 :=
  let h := ilf_pt (fn_ilf hσ) hI hO hy
  ⟨⟨h.1, hN σ hσ.1.2 y hy⟩, h.2⟩

theorem fo_ikn' {α : Type} {K : List ObjRef} {m : NonDet (State Unit) α} (hI : ∀ L, ILK (L ++ K) m)
    (hN : NQK [] m) (hO : ∀ q, OIK q m) : IK (FN K) m :=
  fun σ h y hy => fn_pt h (ikp_of_ik (hI _) σ) hN hO hy

/-! ## `finalise_cap` -/

theorem fo_prepareThreadDelete (t : ObjRef) {K : List ObjRef} :
    IK (ILF K) (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; exact fo_fpuRelease t

theorem ilf_finThread (t : ObjRef) (fin : Bool) {K : List ObjRef} :
    IK (ILF K) (finaliseCap (Z := Unit) (.threadCap t) fin) := by
  simp only [finaliseCap]
  refine ik_bind (ik_when _ (fo_ik (fun _ => il_unbindNotification _) (fun _ => oi_unbindNotification _))) fun _ =>
    ik_bind (ik_when _ (fo_ik (fun _ => il_unbindFromSc _) (fun _ => oi_unbindFromSc _))) fun _ =>
    ik_bind (ik_when _ (fo_ik (fun _ => il_suspend _) (fun _ => oi_suspend _))) fun _ =>
    ik_bind (ik_when _ (fo_prepareThreadDelete t)) fun _ => ik_pure _

/-- **`finalise_cap` keeps `FN K`**. -/
theorem fo_finaliseCap (c : Cap) (fin : Bool) {K : List ObjRef} : IK (FN K) (finaliseCap (Z := Unit) c fin) := by
  by_cases ht : ∃ t, c = .threadCap t
  · obtain ⟨t, rfl⟩ := ht
    intro σ h y hy
    exact ⟨iln_finaliseCap _ _ σ h.1 y hy, (ilf_finThread t fin σ (fn_ilf h) y hy).2⟩
  · refine fo_ikn (fun _ => iln_finaliseCap c fin) (fun _ => ?_)
    cases c
    case threadCap t => exact absurd ⟨t, rfl⟩ ht
    all_goals (simp only [finaliseCap]; oi_auto)

/-- After a FINAL thread cap's `finalise_cap`, its thread is not the FPU owner. -/
theorem finThread_owner (t : ObjRef) {σ : State Unit} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) (.threadCap t) true σ).1) :
    y.2.archState.x64CurrentFpuOwner ≠ some t := by
  simp only [finaliseCap, NonDet.when, ↓reduceIte] at hy
  obtain ⟨z1, -, hy⟩ := hy
  obtain ⟨z2, -, hy⟩ := hy
  obtain ⟨z3, -, hy⟩ := hy
  obtain ⟨z4, hz4, hy⟩ := hy
  have e : y.2 = z4.2 := (Prod.ext_iff.1 (Set.mem_singleton_iff.1 hy)).2
  rw [e]
  unfold prepareThreadDelete at hz4
  exact fpuRelease_ne t hz4

/-! ## The cap removals -/

theorem fo_emptySlot_ts (slot : CslotPtr) (info : Cap) {K : List ObjRef} (σ : State Unit)
    (h : TcSafe (oL σ ++ K) σ slot .nullCap) : IKp (ILF K) σ (emptySlot (Z := Unit) slot info) :=
  fun hσ y hy => ilf_pt hσ (il_emptySlot_ts slot info σ h (il_postCapDeletion _)) (fun _ => oi_emptySlot _ _) hy

theorem fo_setCap_p (c : Cap) (sl : CslotPtr) {K : List ObjRef} (σ : State Unit)
    (h : TcSafe (oL σ ++ K) σ sl c) : IKp (ILF K) σ (setCap (Z := Unit) c sl) :=
  fun hσ y hy => ilf_pt hσ (il_setCap_p c sl σ fun _ => h) (fun _ => oi_setCap _ _) hy

theorem fo_capSwapForDelete (s1 s2 : CslotPtr) {K : List ObjRef} : IK (FN K) (capSwapForDelete (Z := Unit) s1 s2) :=
  fo_ikn (fun _ => iln_capSwapForDelete s1 s2) (fun _ => oi_capSwapForDelete _ _)

theorem fo_preemptionPoint {K : List ObjRef} : IKE (FN K) (preemptionPoint (Z := Unit)) :=
  fo_ikn (fun _ => iln_preemptionPoint) (fun _ => oi_preemptionPoint)

/-- `finalise_slot`'s removeable case (il2's `tcs_removable` at any `K`). -/
theorem fo_tcs_removable {K : List ObjRef} {σ : State Unit} (hI : SInvU.UtInv'' σ) {s : CslotPtr} {cap : Cap}
    (hc : SInvU.capAt σ s = some cap) {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : SInvU.capAt y.2 s = some cap) (hrm : capRemoveable y.1.1 s) : TcSafe K y.2 s .nullCap := by
  by_cases ht : ∃ t, cap = .threadCap t
  · obtain ⟨t, rfl⟩ := ht
    by_cases hf : isFinalCap' (Z := Unit) (.threadCap t) σ
    · have hv := finaliseCap_thread_val t _ σ y hy
      simp [hf] at hv
      rw [hv] at hrm
      simp [capRemoveable] at hrm
    · have hfe : decide (isFinalCap' (Z := Unit) (.threadCap t) σ) = false := by simp [hf]
      rw [hfe] at hy
      have e := finThread_false_eq t hy
      obtain ⟨s', hne, hs'⟩ := other_threadCap hI hc hf
      intro u hu
      rw [hc3] at hu; cases hu
      exact Or.inr (Or.inl ⟨s', hne, by rw [e]; exact hs'⟩)
  · exact tcSafe_of_not fun u e => ht ⟨u, Option.some.inj (hc3.symm.trans e)⟩

/-- `finalise_slot`'s other cases: the remainder is safe at `K = oL` (the finalised thread is not the owner). -/
theorem fo_tcs_rem {σ : State Unit} {s : CslotPtr} {cap : Cap} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : SInvU.capAt y.2 s = some cap) (hrm : ¬ capRemoveable y.1.1 s) : TcSafe (oL y.2 ++ []) y.2 s y.1.1 := by
  by_cases ht : ∃ t, cap = .threadCap t
  · obtain ⟨t, rfl⟩ := ht
    by_cases hf : isFinalCap' (Z := Unit) (.threadCap t) σ
    · have hfe : decide (isFinalCap' (Z := Unit) (.threadCap t) σ) = true := by simp [hf]
      rw [hfe] at hy
      have hd := hk_finThread_dead t σ trivial y hy
      have ho := finThread_owner t hy
      intro u hu
      rw [hc3] at hu; cases hu
      refine Or.inr (Or.inr ⟨fun hm => ho (mem_oL.1 ?_), fun x hx => hd t x hx rfl⟩)
      simpa using hm
    · have hv := finaliseCap_thread_val t _ σ y hy
      simp [hf] at hv
      rw [hv] at hrm
      exact absurd trivial hrm
  · exact tcSafe_of_not fun u e => ht ⟨u, Option.some.inj (hc3.symm.trans e)⟩

/-! ## `rec_del` -/

def FPre (k : RecDelCall) (σ : State Unit) : Prop := RPre k σ ∧ FN [] σ

def FPost : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | .cTEDeleteCall s e, r, σ => RPost (.cTEDeleteCall s e) r σ ∧ FN [] σ
  | .finaliseSlotCall s e, r, σ => RPost (.finaliseSlotCall s e) r σ ∧ FN [] σ ∧
      ∀ info, r = .ok (true, info) → TcSafe (oL σ ++ []) σ s .nullCap
  | .reduceZombieCall c s e, r, σ => RPost (.reduceZombieCall c s e) r σ ∧ FN [] σ

theorem FPost.rp {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : FPost k r σ) :
    RPost k r σ := by
  cases k with
  | cTEDeleteCall => exact h.1
  | finaliseSlotCall => exact h.1
  | reduceZombieCall => exact h.1

theorem FPost.fn {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : FPost k r σ) :
    FN [] σ := by
  cases k with
  | cTEDeleteCall => exact h.2
  | finaliseSlotCall => exact h.2.1
  | reduceZombieCall => exact h.2

theorem FPost.inv {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : FPost k r σ) :
    UtInv'' σ := h.rp.inv

theorem fo_step (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (FPre k) (FPost k) (f k)) (k : RecDelCall) :
    HR (FPre k) (FPost k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := mem_bindE' hy
    · have hp := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      have hp2 := hp.1.2 b info ha
      try dsimp only at hy
      obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz2
        rw [mem_ret_ok hy]; try dsimp only
        unfold NonDet.when at hx
        split at hx
        · rename_i heb
          have hbt : b = true := by
            cases b
            · obtain ⟨he, -⟩ := hp2.2 rfl
              subst he
              simp at heb
            · rfl
          subst hbt
          have hsafe : ∀ c, capAt z.2 s = some c → SafeDelV (uV z.2) s c := hp2.1 rfl
          obtain ⟨h1, h2⟩ := hv_emptySlotN0 s info z.2 ⟨hp.1.1, hsafe⟩ x hx
          have hts := hp.2.2 info (by rw [ha])
          have hF := fo_emptySlot_ts s info z.2 hts (fn_ilf hp.2.1) x hx
          exact ⟨⟨h1, fun _ _ _ => Or.inl h2⟩,
            ⟨⟨hF.1, nq_emptySlot s info z.2 hp.2.1.1.2 x hx⟩, hF.2⟩⟩
        · rename_i heb
          obtain rfl := Set.mem_singleton_iff.1 hx
          have hb : b = false := by
            cases b
            · rfl
            · exact absurd (Or.inr rfl) heb
          exact ⟨⟨hp.1.1, fun _ _ _ => Or.inr (hp2.2 hb).2⟩, hp.2.1⟩
      · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
        rw [hx] at her; cases her
    · have hp := hrec (.finaliseSlotCall s e) σ hσ z hz
      exact ⟨⟨hp.inv, fun a ha _ => by cases ha⟩, hp.fn⟩
  | finaliseSlotCall s e =>
    intro σ hσ y hy
    obtain ⟨hI, hL⟩ := hσ
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
    · rename_i hn
      subst hn
      rw [mem_ret_ok hy1]; try dsimp only
      refine ⟨⟨hI, fun b info h => ?_⟩, hL, fun _ _ => tcSafe_of_not fun t e => by rw [hc] at e; cases e⟩
      cases h
      refine ⟨fun _ c hc' => ?_, fun h => by cases h⟩
      rw [hc] at hc'; cases hc'
      exact safeDel_of_sRefs rfl
    · rename_i hnn
      obtain ⟨z, hz, H⟩ := mem_bindE' hy1
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
      have hL3 : FN [] σ3 := fo_finaliseCap cap _ _ hL _ hx3
      have hrem := fo_tcs_rem (s := s) hx3
      have hrmv := fo_tcs_removable (K := oL σ3 ++ []) hI hc hx3
      obtain ⟨rem, cl⟩ := rc
      obtain ⟨hI3, hc3, hB3, hC3⟩ := fin_step hI hc hnn hx3
      try dsimp only at hI3
      try dsimp only at hc3
      try dsimp only at hB3
      try dsimp only at hC3
      try dsimp only at hrem
      try dsimp only at hrmv
      try dsimp only at hy3
      split at hy3
      · rename_i hrm
        rw [mem_ret_ok hy3]; try dsimp only
        refine ⟨⟨hI3, fun b info h => ?_⟩, hL3, fun info h => ?_⟩
        · cases h
          refine ⟨fun _ c hc' => ?_, fun h => by cases h⟩
          rw [hc3] at hc'; cases hc'
          exact hB3 hrm
        · exact hrmv hc3 hrm
      · rename_i hrm
        have hW := hC3 hrm
        have hT : TcSafe (oL σ3 ++ []) σ3 s rem := hrem hc3 hrm
        have hFs : ∀ σ4 u, (u, σ4) ∈ (setCap (Z := Unit) rem s σ3).1 → FN [] σ4 := fun σ4 u hx4 =>
          let hF := fo_setCap_p rem s σ3 hT (fn_ilf hL3) _ hx4
          ⟨⟨hF.1, nq_setCap rem s σ3 hL3.1.2 _ hx4⟩, hF.2⟩
        split at hy3
        · rename_i hcy
          obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]; try dsimp only
            have hv4 : uV σ4 = vCap s rem (uV σ3) := hv_setCap rem s (uV σ3) σ3 rfl _ hx4
            refine ⟨⟨by show UtInv''V (uV σ4); rw [hv4]; exact hW, fun b info h => ?_⟩,
              hFs σ4 u' hx4, fun info h => by cases h⟩
            cases h
            refine ⟨fun h => (by cases h), fun _ => ⟨by simpa using hcy.2, rem, ?_, ?_⟩⟩
            · show (uV σ4).2.1 s = _
              rw [hv4, vCap_cap, if_pos rfl]
            · obtain ⟨hcz, -⟩ := hcy
              cases rem with
              | zombie p bb n => exact ⟨p, bb, n, rfl, hcz⟩
              | _ => exact False.elim hcz
          · obtain ⟨x, -, hx⟩ := mem_liftE' hz
            rw [hx] at her; cases her
        · rename_i hcy
          obtain ⟨z, hz, H⟩ := mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hv4 : uV σ4 = vCap s rem (uV σ3) := hv_setCap rem s (uV σ3) σ3 rfl _ hx4
          have hI4 : UtInv'' σ4 := by show UtInv''V (uV σ4); rw [hv4]; exact hW
          have hL4 : FN [] σ4 := hFs σ4 u' hx4
          have hc4 : capAt σ4 s = some rem := by
            show (uV σ4).2.1 s = _
            rw [hv4, vCap_cap, if_pos rfl]
          have hpre : FPre (.reduceZombieCall rem s e) σ4 := by
            refine ⟨⟨hI4, hc4, hrm, fun hcz => ?_⟩, hL4⟩
            by_contra hne
            exact hcy ⟨hcz, hne⟩
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hP5 := hrec _ σ4 hpre z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : UtInv'' z6.2 := by show UtInv''V (uV z6.2); rw [hv6]; exact hP5.inv
            have hL6 : FN [] z6.2 := fo_preemptionPoint z.2 hP5.fn z6 hz6
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall s e) z6.2 ⟨hI6, hL6⟩ y hy6
            · exact ⟨⟨hI6, fun _ _ h => by cases h⟩, hL6, fun _ h => by cases h⟩
          · exact ⟨⟨hP5.inv, fun _ _ h => by cases h⟩, hP5.fn, fun _ h => by cases h⟩
  | reduceZombieCall c s e =>
    intro σ hσ y hy
    obtain ⟨⟨hI, hc, hnr, hcy⟩, hL⟩ := hσ
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => exact (rz_fail rfl hy).elim
      | succ n =>
        cases e with
        | false =>
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨cn, hcn, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
          · obtain rfl := mem_ret_ok hz
            cases hcn
            try dsimp only at hy
            obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
            · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
              obtain ⟨hne, rfl⟩ := hx
              obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
                rw [mem_ret_ok hy]; try dsimp only
                refine ⟨?_, fo_capSwapForDelete _ s σ hL x hx⟩
                show UtInv''V (uV x.2)
                refine hv_capSwapForDeleteN _ s σ ⟨hI, fun c1 c2 h1 h2 => ⟨fun _ => ?_, fun _ => ?_⟩⟩ x hx
                · exact posOK_of_nn hI.2 hc (fun e => by cases e)
                · exact posOK_firstSlot hI.2 hc
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz
                rw [hx] at her; cases her
            · obtain ⟨x, -, hx⟩ := mem_liftE' hz
              rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
        | true =>
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
          · obtain rfl := mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := mem_bindE' hy
            have hp := hrec (.cTEDeleteCall (ptr, natToCref (zombieCteBits bits) n) false) σ ⟨hI, hL⟩ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact ⟨hp.1.1, hp.2⟩
            have hend := hp.1.2 a ha rfl
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
                rw [mem_ret_ok hy]; try dsimp only
                have hv := hv_setCap (.zombie ptr bits n) s (uV z.2) z.2 rfl _ hx
                have hF := fo_setCap_p (K := []) (.zombie ptr bits n) s z.2
                  (tcSafe_of_not fun t e => by rw [hc5] at e; cases e) (fn_ilf hp.2) x hx
                refine ⟨?_, ⟨hF.1, nq_setCap _ s z.2 hp.2.1.2 x hx⟩, hF.2⟩
                show UtInv''V (uV x.2)
                rw [hv]
                exact utN_shrink hp.1.1 hc5 hnr hend
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [mem_ret_ok hy]; try dsimp only
                exact ⟨hp.1.1, hp.2⟩
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
    | _ => exact (rz_fail rfl hy).elim

/-- **`rec_del` keeps `FT`** (with IfLiveT, NtfnQB ∧ EpQB and UtInv''). -/
theorem fo_recDel (k : RecDelCall) :
    HR (FPre k) (FPost k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact hr_lfp FPre FPost (fun f hf k => fo_step f hf k) k

/-- `FN []` with ut4's UtInv''. -/
def FU (σ : State Unit) : Prop := FN [] σ ∧ UtInv'' σ

theorem fou_recDel_cte (s : CslotPtr) (e : Bool) : IKE FU (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  fun σ h y hy => let hp := fo_recDel (.cTEDeleteCall s e) σ ⟨h.2, h.1⟩ y hy; ⟨hp.fn, hp.inv⟩

theorem fou_recDel_fin (s : CslotPtr) (e : Bool) : IKE FU (recDel (Z := Unit) (.finaliseSlotCall s e)) :=
  fun σ h y hy => let hp := fo_recDel (.finaliseSlotCall s e) σ ⟨h.2, h.1⟩ y hy; ⟨hp.fn, hp.inv⟩

/-- **`cap_delete` keeps `FT`**. -/
theorem fou_capDelete (slot : CslotPtr) : IKE FU (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (fou_recDel_cte slot true) fun _ => ike_returnOk _

theorem fou_preemptionPoint : IKE FU (preemptionPoint (Z := Unit)) := fun σ h y hy =>
  ⟨fo_preemptionPoint σ h.1 y hy, by
    show UtInv''V (uV y.2); rw [uk_preemptionPoint (uvw := uV σ) σ rfl y hy]; exact h.2⟩

theorem fou_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK FU (f k)) (sl : CslotPtr) : IKE FU (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE FU (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first
    | (with_reducible exact fou_capDelete _) | (with_reducible exact fou_preemptionPoint)
    | (with_reducible exact hrec' _) | ik_step0 | ik_unfold | (unfold NonDetE.whenE))
  all_goals exact hrec' _

/-- **`cap_revoke` keeps `FT`**. -/
theorem fou_capRevoke (sl : CslotPtr) : IKE FU (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => fou_capRevokeF hf k) sl

end

end Fl4Proofs.P3.SInvF
