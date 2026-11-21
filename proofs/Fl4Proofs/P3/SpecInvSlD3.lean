/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive across `rec_del` /
`cap_delete` / `cap_revoke`** (sl2 handoff 2; spec side only).

The induction is ut5's `hr_lfp` on il2's `LPre` / `LPost` (UtInv'', IfLiveT with
NtfnQB ∧ EpQB) with `DX I := SL I [] ∧ ScInv ∧ IdleScIs I.2 ∧ ScKind` carried
beside (`DPre`, `DPost`; for `FinaliseSlotCall s`, a `true` result makes
emptying `s` `NSafe`). `sd_step` replays il2's `ld_step`; the new facts at
`finalise_slot` are `ns_removable` / `ns_rem`:
* thread cap: NON-final → il2's `other_threadCap`; FINAL → the Zombie over it,
  the thread unbound (`tunb_finThread`, sb1's `ScBackS` at that state).
* SC cap: NON-final → `other_scCap` (`ScKind` [J]); FINAL → the null cap over
  it, the SC not live or idle (`scd_finSc`, the idle SC fixed: `IdleScIs`).
* any other cap: no `NCap`.
Tops: **`sd_recDel`**, **`sdu_capDelete`, `sdu_capRevoke : IKE (SDU I)`** with
`SDU I := (ILN [] ∧ UtInv'') ∧ DX I`.
-/
import Fl4Proofs.P3.SpecInvSlD2
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## The carried facts -/

/-- What deletion carries beside il2's `LPre` / `LPost`. -/
def DX (I : ObjRef × ObjRef) (σ : State Unit) : Prop :=
  SL I [] σ ∧ SInvB.ScInv σ ∧ IdleScIs I.2 σ ∧ ScKind σ

section D
variable {I : ObjRef × ObjRef}

theorem dx_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I [] m) (h2 : ∀ h0, SInvB.SBK h0 m)
    (h3 : IsK I.2 m) (h4 : IK ScKind m) : IK (DX I) m :=
  fun σ h x hx => ⟨h1 σ h.1 x hx, SInvB.sik_of_sbk h2 σ h.2.1 x hx, h3 σ h.2.2.1 x hx, h4 σ h.2.2.2 x hx⟩

theorem dx_ike {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : SLKE I [] m) (h2 : ∀ h0, SInvB.SBKE h0 m)
    (h3 : IsKE I.2 m) (h4 : IKE ScKind m) : IKE (DX I) m :=
  dx_ik h1 h2 h3 h4

/-- The value of `finalise_cap`: the remainder is null, or a Zombie to what the cap named (no SC cap). -/
theorem finaliseCap_rem (c : Cap) (fin : Bool) :
    OV (fun p : Cap × Cap => p.1 = .nullCap ∨ ∃ r b n, p.1 = .zombie r b n ∧ r ∈ objRefs c ∧
      ∀ r' b', c ≠ .schedContextCap r' b') (finaliseCap (Z := Unit) c fin) := by
  by_cases hs : sRefs c = ∅
  · intro σ x hx; exact Or.inl (finaliseCap_null hs fin σ x hx)
  · cases c
    case cnodeCap r bits g =>
      intro σ x hx
      simp only [finaliseCap] at hx
      rw [Set.mem_singleton_iff.1 hx]
      cases fin
      · exact Or.inl rfl
      · exact Or.inr ⟨r, some bits, 2 ^ bits, rfl, by simp [objRefs], fun _ _ h => by cases h⟩
    case threadCap r =>
      intro σ x hx
      have hv := finaliseCap_thread_val r fin σ x hx
      cases fin
      · exact Or.inl (by simpa using hv)
      · exact Or.inr ⟨r, none, 6, by simpa using hv, by simp [objRefs], fun _ _ h => by cases h⟩
    case zombie r b n =>
      intro σ x hx
      simp only [finaliseCap] at hx
      obtain ⟨z, -, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      exact Or.inr ⟨r, b, n, rfl, by simp [objRefs], fun _ _ h => by cases h⟩
    all_goals exact absurd (by simp [sRefs]) hs

/-- `finalise_slot`'s removable case: emptying the slot is `NSafe`. -/
theorem ns_removable {σ : State Unit} (hI : UtInv'' σ) (hD : DX I σ) {s : CslotPtr} {cap : Cap}
    (hc : capAt σ s = some cap) {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : capAt y.2 s = some cap) (hrm : capRemoveable y.1.1 s) : NSafe I [] y.2 s .nullCap := by
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
      intro u c0 hu hn
      rw [hc3] at hu; cases hu
      exact Or.inr (Or.inl ⟨s', _, hne, by rw [e]; exact hs', hn⟩)
  by_cases hsc : ∃ p b, cap = .schedContextCap p b
  · obtain ⟨p, b, rfl⟩ := hsc
    by_cases hf : isFinalCap' (Z := Unit) (.schedContextCap p b) σ
    · have hfe : decide (isFinalCap' (Z := Unit) (.schedContextCap p b) σ) = true := by simp [hf]
      rw [hfe] at hy
      have hd := scd_finSc I.2 p b σ hD.2.2.1 y hy
      intro u c0 hu hn
      rw [hc3] at hu; cases hu
      have e : p = u := hn
      subst e
      exact Or.inr (Or.inr ⟨by simp, scd_dead I.2 p I.1 hd⟩)
    · have hfe : decide (isFinalCap' (Z := Unit) (.schedContextCap p b) σ) = false := by simp [hf]
      rw [hfe] at hy
      have e := (finSc_false_eq p b hy).1
      obtain ⟨s', b', hne, hs'⟩ := other_scCap hD.2.2.2 hc hf
      intro u c0 hu hn
      rw [hc3] at hu; cases hu
      exact Or.inr (Or.inl ⟨s', .schedContextCap p b', hne, by rw [e]; exact hs', hn⟩)
  · exact nSafe_of_not fun u c0 e hn => by
      rw [hc3] at e; cases e
      cases cap with
      | threadCap t => exact ht ⟨t, rfl⟩
      | schedContextCap p b => exact hsc ⟨p, b, rfl⟩
      | _ => exact hn

/-- `finalise_slot`'s other cases: writing the remainder is `NSafe`. -/
theorem ns_rem {σ : State Unit} (hD : DX I σ) {s : CslotPtr} {cap : Cap} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : capAt y.2 s = some cap) (hrm : ¬ capRemoveable y.1.1 s) : NSafe I [] y.2 s y.1.1 := by
  by_cases ht : ∃ t, cap = .threadCap t
  · obtain ⟨t, rfl⟩ := ht
    by_cases hf : isFinalCap' (Z := Unit) (.threadCap t) σ
    · have hfe : decide (isFinalCap' (Z := Unit) (.threadCap t) σ) = true := by simp [hf]
      rw [hfe] at hy
      have hd := tunb_finThread t σ hD.2.1 y hy
      intro u c0 hu hn
      rw [hc3] at hu; cases hu
      have e : t = u := hn
      subst e
      exact Or.inr (Or.inr ⟨by simp, fun o ho hl => absurd hl (tunb_dead hd o ho)⟩)
    · have hv := finaliseCap_thread_val t _ σ y hy
      simp [hf] at hv
      rw [hv] at hrm
      exact absurd trivial hrm
  by_cases hsc : ∃ p b, cap = .schedContextCap p b
  · obtain ⟨p, b, rfl⟩ := hsc
    have hv := finaliseCap_null (c := .schedContextCap p b) (by simp [sRefs]) _ σ y hy
    rw [hv] at hrm
    exact absurd trivial hrm
  · exact nSafe_of_not fun u c0 e hn => by
      rw [hc3] at e; cases e
      cases cap with
      | threadCap t => exact ht ⟨t, rfl⟩
      | schedContextCap p b => exact hsc ⟨p, b, rfl⟩
      | _ => exact hn

/-- `ScKind` across the remainder's write. -/
theorem sk_rem {σ : State Unit} {s : CslotPtr} {cap : Cap} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : capAt y.2 s = some cap) : IKp ScKind y.2 (setCap (Z := Unit) y.1.1 s) := by
  rcases finaliseCap_rem cap _ σ y hy with h | ⟨r, b, n, h, hr, hn⟩
  · rw [h]; exact sk_setCap_null s y.2
  · rw [h]
    exact sk_setCap_p _ s y.2 (fun _ _ e => by cases e) fun r' hr' => by
      simp [objRefs] at hr'; subst hr'
      exact ⟨cap, hc3, hr, hn⟩

end D

/-! ## `rec_del` -/

def DPre (I : ObjRef × ObjRef) (k : RecDelCall) (σ : State Unit) : Prop := LPre k σ ∧ DX I σ

def DPost (I : ObjRef × ObjRef) : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | .cTEDeleteCall s e, r, σ => LPost (.cTEDeleteCall s e) r σ ∧ DX I σ
  | .finaliseSlotCall s e, r, σ => LPost (.finaliseSlotCall s e) r σ ∧ DX I σ ∧
      ∀ info, r = .ok (true, info) → NSafe I [] σ s .nullCap
  | .reduceZombieCall c s e, r, σ => LPost (.reduceZombieCall c s e) r σ ∧ DX I σ

section R
variable {I : ObjRef × ObjRef}

theorem DPost.lp {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : DPost I k r σ) :
    LPost k r σ := by
  cases k with
  | cTEDeleteCall => exact h.1
  | finaliseSlotCall => exact h.1
  | reduceZombieCall => exact h.1

theorem DPost.dx {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : DPost I k r σ) :
    DX I σ := by
  cases k with
  | cTEDeleteCall => exact h.2
  | finaliseSlotCall => exact h.2.1
  | reduceZombieCall => exact h.2

theorem dx_preemptionPoint : IKE (DX I) (preemptionPoint (Z := Unit)) :=
  dx_ike sl_preemptionPoint (fun _ => SInvB.sb_preemptionPoint) isk_preemptionPoint sk_preemptionPoint

theorem sd_step (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (DPre I k) (DPost I k) (f k)) (k : RecDelCall) :
    HR (DPre I k) (DPost I k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := mem_bindE' hy
    · have hp := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      have hp2 := hp.1.1.2 b info ha
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
          obtain ⟨h1, h2⟩ := hv_emptySlotN0 s info z.2 ⟨hp.1.1.1, hsafe⟩ x hx
          have hts := hp.1.2.2 info (by rw [ha])
          have hns := hp.2.2 info (by rw [ha])
          have hD := hp.2.1
          exact ⟨⟨⟨h1, fun _ _ _ => Or.inl h2⟩,
            il_emptySlot_ts s info z.2 hts (il_postCapDeletion _) hp.1.2.1.1 x hx,
            nq_emptySlot s info z.2 hp.1.2.1.2 x hx⟩,
            sl_emptySlot_ns s info z.2 hns (sl_postCapDeletion _) hD.1 x hx,
            SInvB.sik_of_sbk (fun _ => SInvB.sb_emptySlot _ _) z.2 hD.2.1 x hx,
            isk_emptySlot s info z.2 hD.2.2.1 x hx,
            sk_emptySlot s info z.2 hD.2.2.2 x hx⟩
        · rename_i heb
          obtain rfl := Set.mem_singleton_iff.1 hx
          have hb : b = false := by
            cases b
            · rfl
            · exact absurd (Or.inr rfl) heb
          exact ⟨⟨⟨hp.1.1.1, fun _ _ _ => Or.inr (hp2.2 hb).2⟩, hp.1.2.1⟩, hp.2.1⟩
      · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
        rw [hx] at her; cases her
    · have hp := hrec (.finaliseSlotCall s e) σ hσ z hz
      exact ⟨⟨⟨hp.lp.inv, fun a ha _ => by cases ha⟩, hp.lp.il⟩, hp.dx⟩
  | finaliseSlotCall s e =>
    intro σ hσ y hy
    obtain ⟨⟨hI, hL⟩, hD⟩ := hσ
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
      refine ⟨⟨⟨hI, fun b info h => ?_⟩, hL, fun _ _ => tcSafe_of_not fun t e => by rw [hc] at e; cases e⟩,
        hD, fun _ _ => nSafe_of_not fun p c0 e => by rw [hc] at e; cases e; exact id⟩
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
      have hL3 : ILN [] σ3 := iln_finaliseCap cap _ _ hL _ hx3
      have hD3 : DX I σ3 := ⟨sl_finaliseCap cap _ _ ⟨hD.1, hL.1⟩ _ hx3,
        SInvB.si_finaliseCap cap _ _ hD.2.1 _ hx3, isk_finaliseCap cap _ _ hD.2.2.1 _ hx3,
        sk_finaliseCap cap _ _ hD.2.2.2 _ hx3⟩
      have hrem := tcs_rem (s := s) hx3
      have hrmv := tcs_removable hI hc hx3
      have hnrem := ns_rem (I := I) (s := s) hD hx3
      have hnrmv := ns_removable (I := I) hI hD hc hx3
      have hskr := sk_rem (s := s) hx3
      obtain ⟨rem, cl⟩ := rc
      obtain ⟨hI3, hc3, hB3, hC3⟩ := fin_step hI hc hnn hx3
      try dsimp only at hI3
      try dsimp only at hc3
      try dsimp only at hB3
      try dsimp only at hC3
      try dsimp only at hrem
      try dsimp only at hrmv
      try dsimp only at hnrem
      try dsimp only at hnrmv
      try dsimp only at hskr
      try dsimp only at hy3
      split at hy3
      · rename_i hrm
        rw [mem_ret_ok hy3]; try dsimp only
        refine ⟨⟨⟨hI3, fun b info h => ?_⟩, hL3, fun info h => ?_⟩, hD3, fun info h => hnrmv hc3 hrm⟩
        · cases h
          refine ⟨fun _ c hc' => ?_, fun h => by cases h⟩
          rw [hc3] at hc'; cases hc'
          exact hB3 hrm
        · exact hrmv hc3 hrm
      · rename_i hrm
        have hW := hC3 hrm
        have hT : TcSafe [] σ3 s rem := hrem hc3 hrm
        have hN : NSafe I [] σ3 s rem := hnrem hc3 hrm
        have hD4 : ∀ u ∈ (setCap (Z := Unit) rem s σ3).1, DX I u.2 := fun u hu =>
          ⟨sl_setCap_p rem s σ3 (fun _ => hN) hD3.1 u hu, SInvB.sik_of_sbk (fun _ => SInvB.sb_setCap _ _) σ3 hD3.2.1 u hu,
            isk_setCap rem s σ3 hD3.2.2.1 u hu, hskr hc3 hD3.2.2.2 u hu⟩
        split at hy3
        · rename_i hcy
          obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]; try dsimp only
            have hv4 : uV σ4 = vCap s rem (uV σ3) := hv_setCap rem s (uV σ3) σ3 rfl _ hx4
            refine ⟨⟨⟨by show UtInv''V (uV σ4); rw [hv4]; exact hW, fun b info h => ?_⟩,
              ⟨il_setCap_p rem s σ3 (fun _ => hT) hL3.1 _ hx4, nq_setCap rem s σ3 hL3.2 _ hx4⟩,
              fun info h => by cases h⟩, hD4 _ hx4, fun info h => by cases h⟩
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
          have hL4 : ILN [] σ4 := ⟨il_setCap_p rem s σ3 (fun _ => hT) hL3.1 _ hx4, nq_setCap rem s σ3 hL3.2 _ hx4⟩
          have hc4 : capAt σ4 s = some rem := by
            show (uV σ4).2.1 s = _
            rw [hv4, vCap_cap, if_pos rfl]
          have hpre : DPre I (.reduceZombieCall rem s e) σ4 := by
            refine ⟨⟨⟨hI4, hc4, hrm, fun hcz => ?_⟩, hL4⟩, hD4 _ hx4⟩
            by_contra hne
            exact hcy ⟨hcz, hne⟩
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hP5 := hrec _ σ4 hpre z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : UtInv'' z6.2 := by show UtInv''V (uV z6.2); rw [hv6]; exact hP5.lp.inv
            have hL6 : ILN [] z6.2 := iln_preemptionPoint z.2 hP5.lp.il z6 hz6
            have hD6 : DX I z6.2 := dx_preemptionPoint z.2 hP5.dx z6 hz6
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall s e) z6.2 ⟨⟨hI6, hL6⟩, hD6⟩ y hy6
            · exact ⟨⟨⟨hI6, fun _ _ h => by cases h⟩, hL6, fun _ h => by cases h⟩, hD6, fun _ h => by cases h⟩
          · exact ⟨⟨⟨hP5.lp.inv, fun _ _ h => by cases h⟩, hP5.lp.il, fun _ h => by cases h⟩, hP5.dx,
              fun _ h => by cases h⟩
  | reduceZombieCall c s e =>
    intro σ hσ y hy
    obtain ⟨⟨⟨hI, hc, hnr, hcy⟩, hL⟩, hD⟩ := hσ
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
                refine ⟨⟨?_, iln_capSwapForDelete _ s σ hL x hx⟩,
                  dx_ik (sl_capSwapForDelete _ s) (fun _ => SInvB.sb_capSwapForDelete _ s)
                    (isk_capSwapForDelete _ s) (sk_capSwapForDelete _ s) σ hD x hx⟩
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
            have hp := hrec (.cTEDeleteCall (ptr, natToCref (zombieCteBits bits) n) false) σ ⟨⟨hI, hL⟩, hD⟩ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact ⟨⟨hp.1.1.1, hp.1.2⟩, hp.2⟩
            have hend := hp.1.1.2 a ha rfl
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
                refine ⟨⟨?_, il_setCap_nt _ s z.2 (fun t e => by rw [hc5] at e; cases e) hp.1.2.1 x hx,
                  nq_setCap _ s z.2 hp.1.2.2 x hx⟩,
                  sl_setCap_nt _ s z.2 (fun t c0 e => by rw [hc5] at e; cases e; exact id) hp.2.1 x hx,
                  SInvB.sik_of_sbk (fun _ => SInvB.sb_setCap _ _) z.2 hp.2.2.1 x hx,
                  isk_setCap _ s z.2 hp.2.2.2.1 x hx,
                  sk_setCap_p _ s z.2 (fun _ _ e => by cases e) (fun r hr => ⟨_, hc5, by simpa [objRefs] using hr,
                    fun _ _ e => by cases e⟩) hp.2.2.2.2 x hx⟩
                show UtInv''V (uV x.2)
                rw [hv]
                exact utN_shrink hp.1.1.1 hc5 hnr hend
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [mem_ret_ok hy]; try dsimp only
                exact ⟨⟨hp.1.1.1, hp.1.2⟩, hp.2⟩
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
    | _ => exact (rz_fail rfl hy).elim

/-- **`rec_del` keeps `SL I []`** (with il2's IfLiveT / NtfnQB ∧ EpQB / UtInv'', ScInv, the idle SC and ScKind). -/
theorem sd_recDel (k : RecDelCall) :
    HR (DPre I k) (DPost I k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact hr_lfp (DPre I) (DPost I) (fun f hf k => sd_step f hf k) k

/-- The deletion carrier: il2's `ILU` with `DX`. -/
def SDU (I : ObjRef × ObjRef) (σ : State Unit) : Prop := ILU σ ∧ DX I σ

theorem sdu_recDel_cte (s : CslotPtr) (e : Bool) : IKE (SDU I) (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  fun σ h y hy => let hp := sd_recDel (I := I) (.cTEDeleteCall s e) σ ⟨⟨h.1.2, h.1.1⟩, h.2⟩ y hy;
    ⟨⟨hp.lp.il, hp.lp.inv⟩, hp.dx⟩

/-- **`cap_delete` keeps `SL I []`.** -/
theorem sdu_capDelete (slot : CslotPtr) : IKE (SDU I) (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (sdu_recDel_cte slot true) fun _ => ike_returnOk _

theorem sdu_preemptionPoint : IKE (SDU I) (preemptionPoint (Z := Unit)) := fun σ h y hy =>
  ⟨ilu_preemptionPoint σ h.1 y hy, dx_preemptionPoint σ h.2 y hy⟩

theorem sdu_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (SDU I) (f k)) (sl : CslotPtr) : IKE (SDU I) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (SDU I) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first
    | (with_reducible exact sdu_capDelete _) | (with_reducible exact sdu_preemptionPoint)
    | (with_reducible exact hrec' _) | ik_step0 | ik_unfold | (unfold NonDetE.whenE))
  all_goals exact hrec' _

/-- **`cap_revoke` keeps `SL I []`.** -/
theorem sdu_capRevoke (sl : CslotPtr) : IKE (SDU I) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => sdu_capRevokeF hf k) sl

end R

end

end Fl4Proofs.P3.SInvL
