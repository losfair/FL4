/-
P3 (DESIGN.md §9), invariant line G1 (il2): **IfLiveT across `rec_del` /
`cap_delete`** (il1 handoff step 2; spec side only).

The only cap removals in `rec_del` are `empty_slot` of the deleted slot (after
`finalise_slot` returned `true`) and `set_cap remainder slot`. For a thread
cap `threadCap t` in the slot:
* NON-final (`is_final_cap` false): another slot overlaps it, and ut4's
  `CapKind` / `ZFinal` make that one a thread cap to `t` (`other_threadCap`);
  `finalise_cap _ false` writes nothing (`finThread_false_eq`).
* FINAL: `finalise_cap` suspends `t` (Inactive, `hk_suspend_dead`), and
  `prepare_thread_delete` keeps its state (`tp_prepareThreadDelete_d`), so the
  `Zombie t none 6` written over it removes the thread cap of a dead thread
  (`TcSafe`'s third case, `K = []`).
Every other removed cap is no thread cap (ut5's `fin_step`: the slot still
holds its cap after `finalise_cap`). The unexposed Zombie reduction swaps two
slots (`il_capSwap`: thread caps are permuted, not removed).

The induction is ut5's `hr_lfp` with `LPre k := RPre k ∧ ILN []` and `LPost`
= ut5's `RPost` ∧ `ILN []` ∧ (for `FinaliseSlotCall s`, a `true` result makes
emptying `s` safe for IfLiveT: `TcSafe [] σ s nullCap`), the l4v
`rec_del_call` specs; `ld_step` replays ut5's `rd_step` adding the IfLiveT
facts. Tops: `ld_recDel`, **`ilu_capDelete : IKE ILU (cap_delete slot)`** with
`ILU σ := ILN [] σ ∧ UtInv'' σ`.
-/
import Fl4Proofs.P3.SpecInvNtfnQLW
import Fl4Proofs.P3.SpecInvUtN5
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

/-! ## Generic cap facts -/

theorem tcSafe_of_kheap {K : List ObjRef} {σ σ' : State Unit} {sl : CslotPtr} {c : Cap}
    (e : σ'.kheap = σ.kheap) (h : TcSafe K σ sl c) : TcSafe K σ' sl c := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [e]
  intro t ht
  rw [hc] at ht
  rcases h t ht with h1 | ⟨s, h2, h3⟩ | ⟨h4, h5⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨s, h2, by rw [hc]; exact h3⟩)
  · exact Or.inr (Or.inr ⟨h4, fun y hy => h5 y (by rw [← e]; exact hy)⟩)

/-- `empty_slot` when emptying the slot is safe (`TcSafe` for the null cap). -/
theorem il_emptySlot_ts (slot : CslotPtr) (info : Cap) (σ : State Unit) (h : TcSafe Kq σ slot .nullCap)
    (hp : ILK Kq (postCapDeletion (Z := Unit) info)) : IKp (IL Kq) σ (emptySlot (Z := Unit) slot info) := by
  unfold emptySlot
  intro hσ x hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨c, s1⟩ := y1
  simp only at e1 hc1; subst s1
  dsimp only at hx
  split at hx
  · exact ik_pure () σ hσ x hx
  · have hQ : ∀ s : State Unit, (IL Kq s ∧ s.kheap = σ.kheap) →
        IKp (IL Kq) s (setCap (Z := Unit) .nullCap slot) :=
      fun s hs => il_setCap_p _ _ s (fun _ => tcSafe_of_kheap hs.2 h)
    refine (?_ : HK (fun s => IL Kq s ∧ s.kheap = σ.kheap) (IL Kq) _) σ ⟨hσ, rfl⟩ x hx
    repeat' (first
      | (exact fun s hs => ikp_bind (hQ s hs) (fun _ => hp) hs.1)
      | (refine hk_bind (hk_of_ik (by repeat' (first | ik_step0 | ik_unfold | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)))) fun _ => ?_))

theorem ik_getCap_bind' {P : State Unit → Prop} {β : Type} {sl : CslotPtr} {k : Cap → NonDet (State Unit) β}
    (h : ∀ σ c, SInvU.capAt σ sl = some c → IKp P σ (k c)) : IK P (getCap (Z := Unit) sl >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e, hc⟩ := SInvU.getCap_capAt hy
  obtain ⟨c, s⟩ := y
  simp only at e hc; subst e
  exact h _ c hc hσ x hx

/-- The TCB states of the start, kept by `cap_swap`. -/
theorem tp_capSwap (σ0 : State Unit) (c1 c2 : Cap) (s1 s2 : CslotPtr) :
    IK (TP (StQ σ0)) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap
  repeat' (first
    | ((with_reducible refine tp_setCap _ _ ?_); exact fun p x h => ⟨h, h, h, h, h, h⟩)
    | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)
    | ik_step0 | ik_unfold)

/-- **`cap_swap`** of the caps read in two distinct slots: thread caps are permuted. -/
theorem il_capSwap (c1 c2 : Cap) (s1 s2 : CslotPtr) (σ : State Unit) (hne : s1 ≠ s2)
    (h1 : SInvU.capAt σ s1 = some c1) (h2 : SInvU.capAt σ s2 = some c2) :
    IKp (IL Kq) σ (capSwap (Z := Unit) c1 s1 c2 s2) := by
  intro hσ y hy
  have hv : uV y.2 = vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) (uV σ))) :=
    capSwap_view hne c1 c2 σ rfl y hy
  have hcap : ∀ x, SInvU.capAt y.2 x =
      if x = s2 then some c1 else if x = s1 then some c2 else SInvU.capAt σ x := by
    intro x
    show (uV y.2).2.1 x = _
    rw [hv, vCap_cap, vCap_cap]
    split_ifs with e2 e1 <;> first
      | rfl
      | (show (uV σ).2.1 (sw s1 s2 x) = _; unfold sw; rw [if_neg e1, if_neg e2]; rfl)
  have hs : TP (StQ σ) y.2 := tp_capSwap σ c1 c2 s1 s2 σ (fun p x hp => ⟨x, hp, rfl⟩) y hy
  have hT : ∀ t, HasTC σ t → HasTC y.2 t := by
    rintro t ⟨x, hx⟩
    by_cases e1 : x = s1
    · subst e1
      rw [h1] at hx; cases hx
      exact ⟨s2, by rw [hcap, if_pos rfl]⟩
    · by_cases e2 : x = s2
      · subst e2
        rw [h2] at hx; cases hx
        exact ⟨s1, by rw [hcap, if_neg hne, if_pos rfl]⟩
      · exact ⟨x, by rw [hcap, if_neg e2, if_neg e1]; exact hx⟩
  refine ⟨fun t x hx hl => ?_, fun t ht => hT t (hσ.2 t ht)⟩
  obtain ⟨y0, hy0, e⟩ := hs t x hx
  exact hT t (hσ.1 t y0 hy0 (e ▸ hl))

theorem il_capSwapForDelete (s1 s2 : CslotPtr) : ILK Kq (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · rename_i hne
    refine ik_getCap_bind' fun σ c1 h1 => ?_
    intro hσ y hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨e, h2⟩ := SInvU.getCap_capAt hz
    obtain ⟨c2, s⟩ := z
    simp only at e h2; subst e
    exact il_capSwap c1 c2 s1 s2 _ hne h1 h2 hσ y hy
  · exact ik_pure _

theorem iln_capSwapForDelete (s1 s2 : CslotPtr) : IK (ILN Kq) (capSwapForDelete (Z := Unit) s1 s2) :=
  iln_ik (il_capSwapForDelete s1 s2) (nq_capSwapForDelete s1 s2)

/-! ## `finalise_cap` -/

theorem iln_finaliseCap (c : Cap) (fin : Bool) : IK (ILN Kq) (finaliseCap (Z := Unit) c fin) := by
  cases c
  case endpointCap r b g =>
    simp only [finaliseCap]; exact ik_liftM _ (ik_when _ (iln_cancelAllIpc r))
  case notificationCap r b g =>
    simp only [finaliseCap]
    exact ik_liftM _ (ik_when _ (ik_bind (iln_ik (il_schedContextMaybeUnbindNtfn r)
      (nq_schedContextMaybeUnbindNtfn r)) fun _ => ik_bind (iln_ik (il_unbindMaybeNotification r)
        (nq_unbindMaybeNotification r)) fun _ => iln_cancelAllSignals r))
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    exact ik_ite _ (ik_bind (iln_deletingIrqHandler irq) fun _ => ik_pure _) (ik_pure _)
  all_goals exact iln_ik (by simp only [finaliseCap]; il_auto) (nq_finaliseCap _ _)

/-- A dead `t`: not a live TCB. -/
def QDead (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop := p = t → ¬ liveSt x.tcbState

theorem hk_sts_dead (t : ObjRef) :
    HK (fun _ => True) (TP (QDead t)) (setThreadState (Z := Unit) t .inactive) := by
  intro σ _ y hy
  unfold setThreadState at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨x, -, e⟩ := mem_threadSet hy1
  have hk := kh_setThreadStateAct t y1.2.kheap y1.2 rfl y hy
  intro p z hz het
  subst het
  rw [hk, e] at hz
  dsimp only at hz
  rw [Function.update_self] at hz
  injection hz with hz
  injection hz with hz
  subst hz
  exact fun h => h

theorem hk_suspend_dead (t : ObjRef) : HK (fun _ => True) (TP (QDead t)) (suspend (Z := Unit) t) := by
  unfold suspend
  repeat' (first | exact hk_sts_dead t | refine hk_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_)

theorem tp_prepareThreadDelete_d (t r : ObjRef) : IK (TP (QDead t)) (prepareThreadDelete (Z := Unit) r) := by
  repeat' (first
    | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _)
    | ((with_reducible refine tp_asUser _ _ ?_); exact fun _ _ h => h)
    | ((with_reducible refine tp_archThreadSet _ _ ?_); exact fun _ _ h => h)
    | ik_step0 | ik_unfold)

/-- A final thread cap's `finalise_cap` leaves its thread dead. -/
theorem hk_finThread_dead (t : ObjRef) :
    HK (fun _ => True) (TP (QDead t)) (finaliseCap (Z := Unit) (.threadCap t) true) := by
  simp only [finaliseCap, NonDet.when, ↓reduceIte]
  refine hk_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ =>
    hk_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
  refine hk_bind (hk_suspend_dead t) fun _ => hk_bind (tp_prepareThreadDelete_d t t) fun _ => ?_
  exact hk_of_ik (ik_pure _)

/-- A non-final thread cap's `finalise_cap` writes nothing. -/
theorem finThread_false_eq (t : ObjRef) {σ : State Unit} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) (.threadCap t) false σ).1) : y.2 = σ := by
  have h : IK (fun s => s = σ) (finaliseCap (Z := Unit) (.threadCap t) false) := by
    simp only [finaliseCap, NonDet.when, Bool.false_eq_true, ↓reduceIte]
    repeat' ik_step0
  exact h σ rfl y hy

/-- A non-final thread cap has another slot holding a thread cap to its thread
(ut4's `CapKind` and `ZFinal`). -/
theorem other_threadCap {σ : State Unit} (hI : SInvU.UtInv'' σ) {s : CslotPtr} {t : ObjRef}
    (hs : SInvU.capAt σ s = some (.threadCap t)) (hnf : ¬ isFinalCap' (Z := Unit) (.threadCap t) σ) :
    ∃ s', s' ≠ s ∧ SInvU.capAt σ s' = some (.threadCap t) := by
  obtain ⟨s', c', hne, hc', hr⟩ := nonfinal_other hnf hs (r := t) (by simp [sRefs])
  have hk := hI.2.2.2.2.1 s' c' s (.threadCap t) t hc' hs (objRefs_sub_capRng c' hr) (by simp [sRefs])
  cases c' with
  | threadCap r =>
    have : t = r := by simpa [objRefs] using hr
    subst this
    exact ⟨s', hne, hc'⟩
  | zombie r b n =>
    have hrt : t = r := by simpa [objRefs] using hr
    subst hrt
    exact absurd (by simp [objRefs]) (hI.2.2.2.2.2.2.1 s' t b n hc' s (.threadCap t) (Ne.symm hne) hs)
  | _ => simp [shp] at hk

/-- `finalise_slot`'s removeable case: emptying the slot keeps IfLiveT. -/
theorem tcs_removable {σ : State Unit} (hI : SInvU.UtInv'' σ) {s : CslotPtr} {cap : Cap}
    (hc : SInvU.capAt σ s = some cap) {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : SInvU.capAt y.2 s = some cap) (hrm : capRemoveable y.1.1 s) : TcSafe [] y.2 s .nullCap := by
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

/-- `finalise_slot`'s other cases: writing the remainder keeps IfLiveT. -/
theorem tcs_rem {σ : State Unit} {s : CslotPtr} {cap : Cap} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1)
    (hc3 : SInvU.capAt y.2 s = some cap) (hrm : ¬ capRemoveable y.1.1 s) : TcSafe [] y.2 s y.1.1 := by
  by_cases ht : ∃ t, cap = .threadCap t
  · obtain ⟨t, rfl⟩ := ht
    by_cases hf : isFinalCap' (Z := Unit) (.threadCap t) σ
    · have hfe : decide (isFinalCap' (Z := Unit) (.threadCap t) σ) = true := by simp [hf]
      rw [hfe] at hy
      have hd := hk_finThread_dead t σ trivial y hy
      intro u hu
      rw [hc3] at hu; cases hu
      exact Or.inr (Or.inr ⟨by simp, fun x hx => hd t x hx rfl⟩)
    · have hv := finaliseCap_thread_val t _ σ y hy
      simp [hf] at hv
      rw [hv] at hrm
      exact absurd trivial hrm
  · exact tcSafe_of_not fun u e => ht ⟨u, Option.some.inj (hc3.symm.trans e)⟩

/-! ## `rec_del` -/

def LPre (k : RecDelCall) (σ : State Unit) : Prop := RPre k σ ∧ ILN [] σ

def LPost : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | .cTEDeleteCall s e, r, σ => RPost (.cTEDeleteCall s e) r σ ∧ ILN [] σ
  | .finaliseSlotCall s e, r, σ => RPost (.finaliseSlotCall s e) r σ ∧ ILN [] σ ∧
      ∀ info, r = .ok (true, info) → TcSafe [] σ s .nullCap
  | .reduceZombieCall c s e, r, σ => RPost (.reduceZombieCall c s e) r σ ∧ ILN [] σ

theorem LPost.rp {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : LPost k r σ) :
    RPost k r σ := by
  cases k with
  | cTEDeleteCall => exact h.1
  | finaliseSlotCall => exact h.1
  | reduceZombieCall => exact h.1

theorem LPost.il {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : LPost k r σ) :
    ILN [] σ := by
  cases k with
  | cTEDeleteCall => exact h.2
  | finaliseSlotCall => exact h.2.1
  | reduceZombieCall => exact h.2

theorem LPost.inv {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : LPost k r σ) :
    UtInv'' σ := h.rp.inv

theorem iln_preemptionPoint : IKE (ILN Kq) (preemptionPoint (Z := Unit)) :=
  iln_ik il_preemptionPoint nq_preemptionPoint

theorem ld_step (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (LPre k) (LPost k) (f k)) (k : RecDelCall) :
    HR (LPre k) (LPost k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
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
          exact ⟨⟨h1, fun _ _ _ => Or.inl h2⟩,
            il_emptySlot_ts s info z.2 hts (il_postCapDeletion _) hp.2.1.1 x hx,
            nq_emptySlot s info z.2 hp.2.1.2 x hx⟩
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
      exact ⟨⟨hp.inv, fun a ha _ => by cases ha⟩, hp.il⟩
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
      have hL3 : ILN [] σ3 := iln_finaliseCap cap _ _ hL _ hx3
      have hrem := tcs_rem (s := s) hx3
      have hrmv := tcs_removable hI hc hx3
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
        have hT : TcSafe [] σ3 s rem := hrem hc3 hrm
        split at hy3
        · rename_i hcy
          obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]; try dsimp only
            have hv4 : uV σ4 = vCap s rem (uV σ3) := hv_setCap rem s (uV σ3) σ3 rfl _ hx4
            refine ⟨⟨by show UtInv''V (uV σ4); rw [hv4]; exact hW, fun b info h => ?_⟩,
              ⟨il_setCap_p rem s σ3 (fun _ => hT) hL3.1 _ hx4, nq_setCap rem s σ3 hL3.2 _ hx4⟩,
              fun info h => by cases h⟩
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
          have hpre : LPre (.reduceZombieCall rem s e) σ4 := by
            refine ⟨⟨hI4, hc4, hrm, fun hcz => ?_⟩, hL4⟩
            by_contra hne
            exact hcy ⟨hcz, hne⟩
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hP5 := hrec _ σ4 hpre z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : UtInv'' z6.2 := by show UtInv''V (uV z6.2); rw [hv6]; exact hP5.inv
            have hL6 : ILN [] z6.2 := iln_preemptionPoint z.2 hP5.il z6 hz6
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall s e) z6.2 ⟨hI6, hL6⟩ y hy6
            · exact ⟨⟨hI6, fun _ _ h => by cases h⟩, hL6, fun _ h => by cases h⟩
          · exact ⟨⟨hP5.inv, fun _ _ h => by cases h⟩, hP5.il, fun _ h => by cases h⟩
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
                refine ⟨?_, iln_capSwapForDelete _ s σ hL x hx⟩
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
                refine ⟨?_, il_setCap_nt _ s z.2 (fun t e => by rw [hc5] at e; cases e) hp.2.1 x hx,
                  nq_setCap _ s z.2 hp.2.2 x hx⟩
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

/-- **`rec_del` keeps IfLiveT** (with NtfnQB ∧ EpQB and UtInv'', every call from its precondition). -/
theorem ld_recDel (k : RecDelCall) :
    HR (LPre k) (LPost k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact hr_lfp LPre LPost (fun f hf k => ld_step f hf k) k

/-- IfLiveT with NtfnQB ∧ EpQB and ut4's UtInv''. -/
def ILU (σ : State Unit) : Prop := ILN [] σ ∧ UtInv'' σ

theorem ilu_recDel_cte (s : CslotPtr) (e : Bool) : IKE ILU (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  fun σ h y hy => let hp := ld_recDel (.cTEDeleteCall s e) σ ⟨h.2, h.1⟩ y hy; ⟨hp.il, hp.inv⟩

theorem ilu_recDel_fin (s : CslotPtr) (e : Bool) : IKE ILU (recDel (Z := Unit) (.finaliseSlotCall s e)) :=
  fun σ h y hy => let hp := ld_recDel (.finaliseSlotCall s e) σ ⟨h.2, h.1⟩ y hy; ⟨hp.il, hp.inv⟩

/-- **`cap_delete` keeps IfLiveT** (with NtfnQB ∧ EpQB and UtInv''). -/
theorem ilu_capDelete (slot : CslotPtr) : IKE ILU (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (ilu_recDel_cte slot true) fun _ => ike_returnOk _


theorem ilu_preemptionPoint : IKE ILU (preemptionPoint (Z := Unit)) := fun σ h y hy =>
  ⟨iln_preemptionPoint σ h.1 y hy, by
    show UtInv''V (uV y.2); rw [uk_preemptionPoint (uvw := uV σ) σ rfl y hy]; exact h.2⟩

/-- One step of `cap_revoke`, its recursive calls keeping `ILU`. -/
theorem ilu_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK ILU (f k)) (sl : CslotPtr) : IKE ILU (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE ILU (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first
    | (with_reducible exact ilu_capDelete _) | (with_reducible exact ilu_preemptionPoint)
    | (with_reducible exact hrec' _) | ik_step0 | ik_unfold | (unfold NonDetE.whenE))
  all_goals exact hrec' _

/-- **`cap_revoke` keeps IfLiveT** (with NtfnQB ∧ EpQB and UtInv''). -/
theorem ilu_capRevoke (sl : CslotPtr) : IKE ILU (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ilu_capRevokeF hf k) sl

end

end Fl4Proofs.P3.SInv
