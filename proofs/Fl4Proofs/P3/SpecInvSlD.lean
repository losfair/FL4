/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive across deletion, the
kit** (sl2 handoff 2, first part; spec side only).

The only removals of a thread / SC cap in `rec_del` are `empty_slot` after
`finalise_slot` returned `true`, the remainder written over the slot, and
`cap_delete_one`'s `empty_slot` (inside `deleting_irq_handler`):
* `cap_delete_one`: `fast_finalise` fails on thread and SC caps, so the emptied
  slot holds no `NCap` (`sl_emptySlot_p`).
* `finalise_cap` keeps `SL I K` given IfLiveT at its start (`sl_finaliseCap`):
  a final reply cap's `reply_remove` donates the reply's SC to the
  BlockedOnReply caller, read live, so (IfLiveT) named: it joins `K`.
* FINAL thread cap: `unbind_from_sc` unbinds the thread (its SC is bound back to
  it by sb1's `ScBackS`) and `suspend` / `prepare_thread_delete` keep its binding
  (sb1's frame `BR`): the thread is not live (`tunb_finThread`), so the Zombie
  written over its last cap is `NSafe`'s third case.
* FINAL SC cap: `sched_context_unbind_all_tcbs` (skipping the idle SC only),
  `_ntfn`, `_reply` leave the SC not live or idle, and `_yield_from` /
  `set_inactive` keep its binding fields (`scd_finSc`, the frame `ScB`).
* NON-final thread cap: il2's `other_threadCap` (ut4's `CapKind` / `ZFinal`).
  NON-final SC cap: another slot's cap names the SC; it is an SC cap by
  **`ScKind` [J]** (l4v `valid_caps` with the object typing of `obj_refs`: a cap
  naming the object an SC cap names is an SC cap). `CapKind` covers only the
  slot-holding caps, so the SC case needs this typing fact; it is view-only and
  kept by every deletion step (`sk_*`).
* `cap_swap` permutes the caps and writes no live object (`sl_capSwap`).
-/
import Fl4Proofs.P3.SpecInvSlM
import Fl4Proofs.P3.SpecInvSlI6
import Fl4Proofs.P3.SpecInvNtfnQLD
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `ScKind` -/

/-- **ScKind [J]** (l4v `valid_caps`: an SC cap's object is an SC, and a cap's
`obj_refs` point at an object of the cap's type): a cap naming the object an SC
cap names is an SC cap. -/
def ScKindV (w : SInvU.UView) : Prop :=
  ∀ s r b s' c', w.2.1 s = some (.schedContextCap r b) → w.2.1 s' = some c' → r ∈ objRefs c' →
    ∃ b', c' = .schedContextCap r b'

abbrev ScKind (σ : State Unit) : Prop := ScKindV (SInvU.uV σ)

theorem sk_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, SInvU.UK v m) : IK ScKind m := by
  intro σ hσ x hx
  have e := h (SInvU.uV σ) σ rfl x hx
  show ScKindV (SInvU.uV x.2); rw [e]; exact hσ

theorem ske_of_uke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, SInvU.UKE v m) : IKE ScKind m :=
  sk_of_uk h

theorem sk_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) (h : ScKind σ) : ScKind σ' := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [e]
  intro s r b s' c' h1 h2 h3
  change SInvU.capAt σ' s = _ at h1
  change SInvU.capAt σ' s' = _ at h2
  rw [hc] at h1 h2
  exact h s r b s' c' h1 h2 h3

/-- A cap write keeping ScKind: the new cap is no SC cap, and names only what the
old cap (no SC cap) named. -/
theorem sk_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : ∀ r b, c ≠ .schedContextCap r b)
    (hr : ∀ r ∈ objRefs c, ∃ old, SInvU.capAt σ sl = some old ∧ r ∈ objRefs old ∧
      ∀ r' b', old ≠ .schedContextCap r' b') :
    IKp ScKind σ (setCap (Z := Unit) c sl) := by
  intro hK y hy
  obtain ⟨-, hne, hsl, -, -⟩ := SInvU.setCap_out hy
  have key : ∀ x, SInvU.capAt y.2 x = SInvU.capAt σ x ∨ (x = sl ∧ SInvU.capAt y.2 x = some c) := by
    intro x
    by_cases e : x = sl
    · subst e
      rcases hsl with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl (hne x e)
  intro s r b s' c' hs hs' hrr
  change SInvU.capAt y.2 s = _ at hs
  change SInvU.capAt y.2 s' = _ at hs'
  have hs0 : SInvU.capAt σ s = some (.schedContextCap r b) := by
    rcases key s with h | ⟨-, h⟩
    · rw [← h]; exact hs
    · rw [h] at hs; cases hs; exact absurd rfl (hc r b)
  rcases key s' with h | ⟨rfl, h⟩
  · exact hK s r b s' c' hs0 (by show SInvU.capAt σ s' = _; rw [← h]; exact hs') hrr
  · rw [h] at hs'; cases hs'
    obtain ⟨old, ho, hro, hno⟩ := hr r hrr
    obtain ⟨b', e⟩ := hK s r b _ old hs0 ho hro
    exact absurd e (hno r b')

theorem sk_setCap_null (sl : CslotPtr) : IK ScKind (setCap (Z := Unit) .nullCap sl) :=
  fun σ => sk_setCap_p _ _ σ (fun _ _ h => by cases h) (fun r hr => by simp [objRefs] at hr)

theorem sk_emptySlot (slot : CslotPtr) (info : Cap) : IK ScKind (emptySlot (Z := Unit) slot info) := by
  unfold emptySlot
  repeat' (first
    | (with_reducible exact sk_setCap_null _)
    | (with_reducible exact sk_of_uk fun _ => SInvU.uk_postCapDeletion _)
    | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)
    | ik_step0 | ik_unfold)

theorem sk_capDeleteOne (slot : CslotPtr) : IK ScKind (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne
  refine ik_bind (sk_of_uk fun _ => SInvU.uk_getCap _) fun cap => ik_unless _ ?_
  exact ik_bind (sk_of_uk fun _ => SInvU.uk_isFinalCap _) fun fin =>
    ik_bind (sk_of_uk fun _ => SInvU.uk_fastFinalise _ _) fun _ => sk_emptySlot _ _

theorem sk_finaliseCap (c : Cap) (fin : Bool) : IK ScKind (finaliseCap (Z := Unit) c fin) := by
  by_cases hi : ∃ i, c = .irqHandlerCap i
  · obtain ⟨i, rfl⟩ := hi
    simp only [finaliseCap]
    refine ik_ite _ ?_ (ik_pure _)
    refine ik_bind ?_ fun _ => ik_pure _
    unfold deletingIrqHandler
    exact ik_bind (sk_of_uk fun _ => SInvU.uk_getIrqSlot _) fun s => sk_capDeleteOne s
  · exact sk_of_uk (SInvU.uk_finaliseCap_nonIrq c (fun i e => hi ⟨i, e⟩) fin)

theorem sk_preemptionPoint : IKE ScKind (preemptionPoint (Z := Unit)) :=
  ske_of_uke fun _ => SInvU.uk_preemptionPoint

/-- Caps permuted: ScKind kept. -/
theorem sk_perm {w w' : SInvU.UView} (π : CslotPtr → CslotPtr) (h : ∀ x, w'.2.1 x = w.2.1 (π x))
    (hK : ScKindV w) : ScKindV w' := by
  intro s r b s' c' h1 h2 h3
  rw [h] at h1 h2
  exact hK _ r b _ c' h1 h2 h3

/-! ## `cap_swap` -/

/-- Every live object of `s` was live at `σ0`. -/
def NLs (σ0 s : State Unit) : Prop := ∀ p o, s.kheap p = some o → liveO o → ∃ o0, σ0.kheap p = some o0 ∧ liveO o0

theorem nl_setCap (σ0 : State Unit) (c : Cap) (sl : CslotPtr) : IK (NLs σ0) (setCap (Z := Unit) c sl) := by
  intro σ hσ y hy p o hp hl
  obtain ⟨o1, h1, hl1⟩ := setCap_live hy p o hp hl
  exact hσ p o1 h1 hl1

theorem nl_capSwap (σ0 : State Unit) (c1 c2 : Cap) (s1 s2 : CslotPtr) :
    IK (NLs σ0) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap
  repeat' (first
    | (with_reducible exact nl_setCap _ _ _)
    | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)
    | ik_step0 | ik_unfold)

theorem capSwap_capAt {c1 c2 : Cap} {s1 s2 : CslotPtr} (hne : s1 ≠ s2) {σ : State Unit}
    {y : Unit × State Unit} (hy : y ∈ (capSwap (Z := Unit) c1 s1 c2 s2 σ).1) :
    ∀ x, SInvU.capAt y.2 x = if x = s2 then some c1 else if x = s1 then some c2 else SInvU.capAt σ x := by
  have hv : SInvU.uV y.2 = SInvU.vCap s2 c1 (SInvU.vCap s1 c2 (SInvU.vRen (SInvU.sw s1 s2) (SInvU.uV σ))) :=
    SInvU.capSwap_view hne c1 c2 σ rfl y hy
  intro x
  show (SInvU.uV y.2).2.1 x = _
  rw [hv, SInvU.vCap_cap, SInvU.vCap_cap]
  split_ifs with e2 e1 <;> first
    | rfl
    | (show (SInvU.uV σ).2.1 (SInvU.sw s1 s2 x) = _; unfold SInvU.sw; rw [if_neg e1, if_neg e2]; rfl)

section W
variable {I : ObjRef × ObjRef} {K : List ObjRef}

/-- **`cap_swap`** of the caps read in two distinct slots: names are permuted, no
object made live. -/
theorem sl_capSwap (c1 c2 : Cap) (s1 s2 : CslotPtr) (σ : State Unit) (hne : s1 ≠ s2)
    (h1 : SInvU.capAt σ s1 = some c1) (h2 : SInvU.capAt σ s2 = some c2) :
    IKp (SL I K) σ (capSwap (Z := Unit) c1 s1 c2 s2) := by
  intro hσ y hy
  have hcap := capSwap_capAt hne hy
  have hs : NLs σ y.2 := nl_capSwap σ c1 c2 s1 s2 σ (fun p o hp hl => ⟨o, hp, hl⟩) y hy
  have hT : ∀ t, HasN σ t → HasN y.2 t := by
    rintro t ⟨x, c, hx, hn⟩
    by_cases e1 : x = s1
    · subst e1
      rw [h1] at hx; cases hx
      exact ⟨s2, c1, by rw [hcap, if_pos rfl], hn⟩
    · by_cases e2 : x = s2
      · subst e2
        rw [h2] at hx; cases hx
        exact ⟨s1, c2, by rw [hcap, if_neg hne, if_pos rfl], hn⟩
      · exact ⟨x, c, by rw [hcap, if_neg e2, if_neg e1]; exact hx, hn⟩
  refine ⟨fun t o ht hl h1' h2' => ?_, fun t ht => (hσ.2 t ht).imp_left (hT t)⟩
  obtain ⟨o0, ho0, hl0⟩ := hs t o ht hl
  exact hT t (hσ.1 t o0 ho0 hl0 h1' h2')

theorem sl_capSwapForDelete (s1 s2 : CslotPtr) : SLK I K (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · rename_i hne
    refine ik_getCap_bind' fun σ c1 h1 => ?_
    intro hσ y hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨e, h2⟩ := SInvU.getCap_capAt hz
    obtain ⟨c2, s⟩ := z
    simp only at e h2; subst e
    exact sl_capSwap c1 c2 s1 s2 _ hne h1 h2 hσ y hy
  · exact ik_pure _

end W

theorem sk_capSwapForDelete (s1 s2 : CslotPtr) : IK ScKind (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · rename_i hne
    refine ik_getCap_bind' fun σ c1 h1 => ?_
    intro hσ y hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨e, h2⟩ := SInvU.getCap_capAt hz
    obtain ⟨c2, s0⟩ := z
    simp only at e h2; subst e
    have hcap := capSwap_capAt hne hy
    refine sk_perm (w := SInvU.uV s0) (SInvU.sw s1 s2) (fun x => ?_) hσ
    show SInvU.capAt y.2 x = SInvU.capAt s0 (SInvU.sw s1 s2 x)
    rw [hcap]
    unfold SInvU.sw
    by_cases e1 : x = s1
    · subst e1; simp [hne, h2]
    · by_cases e2 : x = s2
      · subst e2; simp [Ne.symm hne, h1]
      · simp [e1, e2]
  · exact ik_pure _

/-! ## `NSafe` helpers and `empty_slot` -/

section W2
variable {I : ObjRef × ObjRef} {K : List ObjRef}

theorem nSafe_of_kheap {σ σ' : State Unit} {sl : CslotPtr} {c : Cap} (e : σ'.kheap = σ.kheap)
    (h : NSafe I K σ sl c) : NSafe I K σ' sl c := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [e]
  intro t c0 ht hn
  rw [hc] at ht
  rcases h t c0 ht hn with h1 | ⟨s, c', h2, h3, h4⟩ | ⟨h4, h5⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨s, c', h2, by rw [hc]; exact h3, h4⟩)
  · exact Or.inr (Or.inr ⟨h4, fun y hy => h5 y (by rw [← e]; exact hy)⟩)

/-- `empty_slot` when emptying the slot is safe (`NSafe` for the null cap). -/
theorem sl_emptySlot_ns (slot : CslotPtr) (info : Cap) (σ : State Unit) (h : NSafe I K σ slot .nullCap)
    (hp : SLK I K (postCapDeletion (Z := Unit) info)) : IKp (SL I K) σ (emptySlot (Z := Unit) slot info) := by
  unfold emptySlot
  intro hσ x hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨c, s1⟩ := y1
  simp only at e1 hc1; subst s1
  dsimp only at hx
  split at hx
  · exact ik_pure () σ hσ x hx
  · have hQ : ∀ s : State Unit, (SL I K s ∧ s.kheap = σ.kheap) →
        IKp (SL I K) s (setCap (Z := Unit) .nullCap slot) :=
      fun s hs => sl_setCap_p _ _ s (fun _ => nSafe_of_kheap hs.2 h)
    refine (?_ : HK (fun s => SL I K s ∧ s.kheap = σ.kheap) (SL I K) _) σ ⟨hσ, rfl⟩ x hx
    repeat' (first
      | (exact fun s hs => ikp_bind (hQ s hs) (fun _ => hp) hs.1)
      | (refine hk_bind (hk_of_ik (by repeat' (first | ik_step0 | ik_unfold | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)))) fun _ => ?_))

/-! ## `finalise_cap` and `fast_finalise` -/

/-- `SL I K` with IfLiveT. -/
def SLI0 (I : ObjRef × ObjRef) (K : List ObjRef) (s : State Unit) : Prop := SL I K s ∧ IL [] s

/-- The final reply cap's arm: the BlockedOnReply caller joins `K`. -/
theorem sl_replyWhen (r : ObjRef) (final : Bool) : HK (SLI0 I K) (SL I K) (NonDet.when final <| do
        let tptr ← getReplyTcb (Z := Unit) r
        match tptr with
        | none => return ()
        | some tp => do
          let state ← getThreadState tp
          match state with
          | .blockedOnReply r => replyRemove tp r
          | _ => cancelIpc tp) := by
  intro σ h x hx
  unfold NonDet.when at hx
  split at hx
  · obtain ⟨z, hz, hx⟩ := hx
    have ez : z.2 = σ :=
      (show IK (fun s => s = σ) (getReplyTcb (Z := Unit) r) by repeat' (first | ik_step0 | ik_unfold)) σ rfl z hz
    obtain ⟨tptr, s1⟩ := z
    simp only at ez; subst s1
    cases tptr with
    | none => exact (ik_pure () : SLK I K _) σ h.1 x hx
    | some tp =>
      dsimp only at hx
      obtain ⟨w, hw, hx⟩ := hx
      unfold getThreadState at hw
      obtain ⟨xr, hxr, rfl⟩ := mem_threadGet hw
      dsimp only at hx
      cases hs : xr.tcbState with
      | blockedOnReply r' =>
        rw [hs] at hx
        dsimp only at hx
        have h1 : SL I (tp :: K) σ := sl_cons h.1 (Or.inl (hasN_of_tc (h.2.1 tp xr hxr (liveSt_eq hs True.intro))))
        exact sl_tail (sl_replyRemove tp r' (List.mem_cons.2 (Or.inl rfl)) σ h1 x hx)
      | _ => rw [hs] at hx; dsimp only at hx; exact sl_cancelIpc tp σ h.1 x hx
  · rw [Set.mem_singleton_iff.1 hx]; exact h.1

theorem sl_fastFinalise (c : Cap) (fin : Bool) : HK (SLI0 I K) (SL I K) (fastFinalise (Z := Unit) c fin) := by
  cases c
  case replyCap r g => simp only [fastFinalise]; exact sl_replyWhen r fin
  case nullCap => simp only [fastFinalise]; exact shk_pure _ fun s h => h.1
  case endpointCap r b g =>
    simp only [fastFinalise]; exact shk_ik (ik_when _ (sl_cancelAllIpc r)) fun s h => h.1
  case notificationCap r b g =>
    simp only [fastFinalise]
    exact shk_ik (ik_when _ (ik_bind (sl_schedContextMaybeUnbindNtfn r) fun _ =>
      ik_bind (sl_unbindMaybeNotification r) fun _ => sl_cancelAllSignals r)) fun s h => h.1
  all_goals (simp only [fastFinalise]; exact shk_fail)

/-- **`cap_delete_one`**: `fast_finalise` fails on thread and SC caps, so the
emptied slot holds no `NCap`. -/
theorem sl_capDeleteOne (slot : CslotPtr) : HK (SLI0 I K) (SL I K) (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne
  intro σ h x hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨cap, s1⟩ := y1
  simp only at e1 hc1; subst s1
  dsimp only at hx
  unfold NonDet.unless at hx
  split at hx
  · rw [Set.mem_singleton_iff.1 hx]; exact h.1
  obtain ⟨⟨fin, s2⟩, hy2, hx⟩ := hx
  have e2 : s2 = σ := by unfold isFinalCap at hy2; exact (Prod.mk.inj (Set.mem_singleton_iff.1 hy2)).2
  subst s2
  obtain ⟨y3, hy3, hx⟩ := hx
  have hS3 : SL I K y3.2 := sl_fastFinalise cap fin σ h y3 hy3
  have hv3 : SInvU.uV y3.2 = SInvU.uV σ := SInvU.uk_fastFinalise cap fin σ rfl y3 hy3
  have hc3 : SInvU.capAt y3.2 slot = some cap := by
    show (SInvU.uV y3.2).2.1 slot = _; rw [hv3]; exact hc1
  have hnt : ∀ p c0, SInvU.capAt y3.2 slot = some c0 → ¬ NCap p c0 := by
    intro p c0 hc0 hn
    rw [hc3] at hc0; cases hc0
    cases cap <;> simp only [NCap] at hn <;> simp [fastFinalise, NonDet.fail] at hy3
  exact sl_emptySlot_p slot .nullCap y3.2 hnt (sl_postCapDeletion _) hS3 x hx

theorem sl_deletingIrqHandler (irq : Irq) : HK (SLI0 I K) (SL I K) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  intro σ h x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact sl_capDeleteOne _ σ h x hx

/-- **`finalise_cap`** keeps `SL I K` given IfLiveT at its start. -/
theorem sl_finaliseCap (c : Cap) (fin : Bool) : HK (SLI0 I K) (SL I K) (finaliseCap (Z := Unit) c fin) := by
  cases c
  case replyCap r g =>
    simp only [finaliseCap]
    intro σ h x ⟨y, hy, hx⟩
    rw [Set.mem_singleton_iff.1 hx]
    exact sl_replyWhen r fin σ h y hy
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    split
    · exact shk_bind (sl_deletingIrqHandler irq) fun _ => shk_pure _ fun _ h => h
    · exact shk_pure _ fun s h => h.1
  all_goals exact shk_ik (by simp only [finaliseCap]; sl_auto) fun s h => h.1

end W2

end

end Fl4Proofs.P3.SInvL
