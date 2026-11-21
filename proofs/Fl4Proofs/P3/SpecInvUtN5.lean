/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut5): **`rec_del` keeps
`UtInv''`** (spec side only; imports SpecInvUtN4). l4v `rec_del_invs` /
`rec_del_call` specs, by the least fixed point with a call-dependent
precondition and a result-dependent postcondition (`hr_lfp`):

* `CTEDeleteCall s e`: pre `UtInv''`; post `UtInv''` and, for an unexposed call
  that returns, the slot is null or holds a cyclic Zombie (`CycZ`).
* `FinaliseSlotCall s e`: pre `UtInv''`; post `UtInv''`, a `true` result makes
  emptying the slot safe (`SafeDelV`), a `false` result comes only from an
  unexposed call that left a cyclic Zombie.
* `ReduceZombieCall c s e`: pre `UtInv''`, `c` in `s`, not removeable, cyclic
  only when exposed; post `UtInv''`. The unexposed one swaps the Zombie to its
  first slot (`posOK_firstSlot`); the exposed one deletes the last slot and
  shrinks the Zombie (`utN_shrink`: the deleted slot is null, or is the
  Zombie's own slot — another cyclic Zombie for the same object would break
  `ZFinal`).

`ikN_capDelete`, `ikN_recDel` (every call, from `UtInv''` alone when its
precondition is only that).
-/
import Fl4Proofs.P3.SpecInvUtN4
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 2000000

/-- A cyclic Zombie at `s`. -/
def CycZ (s : CslotPtr) (c : Cap) : Prop :=
  ∃ p bb n, c = .zombie p bb n ∧ (p, List.replicate (zombieCteBits bb) false) = s

/-- Hoare triple with a result-dependent postcondition. -/
def HR {α : Type} (P : State Unit → Prop) (Q : α → State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ y ∈ (m σ).1, Q y.1 y.2

theorem hr_lfp {ι α : Type} {F : (ι → NonDet (State Unit) α) → ι → NonDet (State Unit) α}
    (Pre : ι → State Unit → Prop) (Post : ι → α → State Unit → Prop)
    (hF : ∀ f : ι → NonDet (State Unit) α, (∀ k, HR (Pre k) (Post k) (f k)) → ∀ k, HR (Pre k) (Post k) (F f k))
    (i : ι) : HR (Pre i) (Post i) (NonDet.lfp F i) := by
  intro σ hσ x hx
  let f : ι → NonDet (State Unit) α := fun k t => ({y | Pre k t → Post k y.1 y.2}, True)
  have hf : ∀ k t, F f k t ≤ f k t := fun k t =>
    ⟨fun y hy => fun ht => hF f (fun k' t' ht' z hz => hz ht') k t ht y hy, fun _ => trivial⟩
  exact (ik_lfp_le F f hf i σ).1 hx hσ

def RPre : RecDelCall → State Unit → Prop
  | .cTEDeleteCall _ _, σ => UtInv'' σ
  | .finaliseSlotCall _ _, σ => UtInv'' σ
  | .reduceZombieCall c s e, σ => UtInv'' σ ∧ capAt σ s = some c ∧ ¬ capRemoveable c s ∧
      (capCyclicZombie c s → e = true)

def RPost : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | .cTEDeleteCall s e, r, σ => UtInv'' σ ∧ ∀ a, r = .ok a → e = false →
      capAt σ s = some .nullCap ∨ ∃ c, capAt σ s = some c ∧ CycZ s c
  | .finaliseSlotCall s e, r, σ => UtInv'' σ ∧ ∀ b info, r = .ok (b, info) →
      (b = true → ∀ c, capAt σ s = some c → SafeDelV (uV σ) s c) ∧
      (b = false → e = false ∧ ∃ c, capAt σ s = some c ∧ CycZ s c)
  | .reduceZombieCall _ _ _, _, σ => UtInv'' σ

theorem RPost.inv {k : RecDelCall} {r : Except Unit (Bool × Cap)} {σ : State Unit} (h : RPost k r σ) :
    UtInv'' σ := by
  cases k with
  | cTEDeleteCall => exact h.1
  | finaliseSlotCall => exact h.1
  | reduceZombieCall => exact h

/-! ## The exposed Zombie reduction's shrink -/

theorem utN_shrink {w : UView} (hI : UtInv''V w) {s : CslotPtr} {ptr : ObjRef} {bits : Option Nat} {n : Nat}
    (hs : w.2.1 s = some (.zombie ptr bits (n + 1))) (hnr : ¬ capRemoveable (.zombie ptr bits (n + 1)) s)
    (hend : w.2.1 (ptr, natToCref (zombieCteBits bits) n) = some .nullCap ∨
      ∃ c, w.2.1 (ptr, natToCref (zombieCteBits bits) n) = some c ∧ CycZ (ptr, natToCref (zombieCteBits bits) n) c) :
    UtInv''V (vCap s (.zombie ptr bits n) w) := by
  obtain ⟨hI1, hN⟩ := hI
  have hZ := hN.2.2.2.2.2.1
  have hL := zcb_le hN.2.2.2.2.2.2 hs
  refine ⟨utInv'_vCap_nn hI1 ⟨fun e => (by cases e), fun _ _ _ _ e => (by cases e)⟩,
    utN_vCapGen hN hs (fun e => (by cases e)) rfl rfl rfl (fun _ _ _ _ e => (by cases e)) ?_ ?_⟩
  · intro r hr i c' hi hc' hsh
    obtain ⟨k, hk, hik⟩ := hsh
    have hr' : r = ptr := by simpa [sRefs] using hr
    rw [hr'] at hi
    by_cases hkn : k = n
    · rw [hkn] at hik
      rcases hend with h0 | ⟨c, hcE, p, bb, m, hcm, hcy⟩
      · rw [← hik, hi] at h0; cases h0; exact absurd rfl hc'
      · have hp : p = ptr := congrArg Prod.fst hcy
        rw [hcm, hp] at hcE
        by_cases hes : (ptr, natToCref (zombieCteBits bits) n) = s
        · rw [hes, hs] at hcE
          cases hcE
          have hcyc : (ptr, List.replicate (zombieCteBits bits) false) = s := by
            rw [← hp]; exact hcy.trans hes
          have hk0 : n ≠ 0 := fun h0 => hnr (Or.inr ⟨by omega, hcyc⟩)
          refine ⟨0, by omega, ?_⟩
          rw [hik, natToCref_zero _ hL]
          exact (congrArg Prod.snd hcy).symm
        · exact absurd (show ptr ∈ objRefs (.zombie ptr bb m) by simp [objRefs])
            (hZ s ptr bits (n + 1) hs _ _ hes hcE)
    · exact ⟨k, by omega, hik⟩
  · intro r b' n' e s' c' hne hs'
    injection e with e1 e2 e3
    rw [← e1]
    exact hZ s ptr bits (n + 1) hs s' c' hne hs'

/-! ## One step -/

theorem mem_ret_ok {ε α : Type} {a : α} {σ : State Unit} {y : Except ε α × State Unit}
    (hy : y ∈ ((NonDetE.returnOk a : NonDetE (State Unit) ε α).run σ).1) : y = (.ok a, σ) :=
  Set.mem_singleton_iff.1 hy

theorem rz_fail {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))} {c : Cap} {s : CslotPtr}
    {e : Bool} (h : (recDelF (Z := Unit) f (.reduceZombieCall c s e) : NonDet (State Unit) _) =
      (NonDetE.liftE (ε := Unit) (NonDet.fail : NonDet (State Unit) (Bool × Cap)) : NonDet (State Unit) _))
    {σ : State Unit} {y : Except Unit (Bool × Cap) × State Unit}
    (hy : y ∈ ((recDelF (Z := Unit) f (.reduceZombieCall c s e) : NonDet (State Unit) _) σ).1) : False := by
  rw [h] at hy
  obtain ⟨x, hx, -⟩ := mem_liftE' (m := (NonDet.fail : NonDet (State Unit) (Bool × Cap))) hy
  exact hx

theorem rd_step (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (RPre k) (RPost k) (f k)) (k : RecDelCall) :
    HR (RPre k) (RPost k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := mem_bindE' hy
    · have hp := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      have hp2 := hp.2 b info ha
      try dsimp only at hy
      obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz2
        rw [mem_ret_ok hy]; try dsimp only
        unfold NonDet.when at hx
        split at hx
        · rename_i heb
          have hsafe : ∀ c, capAt z.2 s = some c → SafeDelV (uV z.2) s c := by
            cases b
            · obtain ⟨he, -⟩ := hp2.2 rfl
              subst he
              simp at heb
            · exact hp2.1 rfl
          obtain ⟨h1, h2⟩ := hv_emptySlotN0 s info z.2 ⟨hp.1, hsafe⟩ x hx
          exact ⟨h1, fun _ _ _ => Or.inl h2⟩
        · rename_i heb
          obtain rfl := Set.mem_singleton_iff.1 hx
          have hb : b = false := by
            cases b
            · rfl
            · exact absurd (Or.inr rfl) heb
          exact ⟨hp.1, fun _ _ _ => Or.inr (hp2.2 hb).2⟩
      · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
        rw [hx] at her; cases her
    · exact ⟨(hrec (.finaliseSlotCall s e) σ hσ z hz).inv, fun a ha _ => by cases ha⟩
  | finaliseSlotCall s e =>
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
    · rename_i hn
      subst hn
      rw [mem_ret_ok hy1]; try dsimp only
      refine ⟨hσ, fun b info h => ?_⟩
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
      obtain ⟨rem, cl⟩ := rc
      obtain ⟨hI3, hc3, hB3, hC3⟩ := fin_step hσ hc hnn hx3
      try dsimp only at hy3
      try dsimp only at hI3
      try dsimp only at hc3
      try dsimp only at hB3
      try dsimp only at hC3
      split at hy3
      · rename_i hrm
        rw [mem_ret_ok hy3]; try dsimp only
        refine ⟨hI3, fun b info h => ?_⟩
        cases h
        refine ⟨fun _ c hc' => ?_, fun h => by cases h⟩
        rw [hc3] at hc'; cases hc'
        exact hB3 hrm
      · rename_i hrm
        have hW := hC3 hrm
        split at hy3
        · rename_i hcy
          obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]; try dsimp only
            have hv4 : uV σ4 = vCap s rem (uV σ3) := hv_setCap rem s (uV σ3) σ3 rfl _ hx4
            refine ⟨by show UtInv''V (uV σ4); rw [hv4]; exact hW, fun b info h => ?_⟩
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
          have hc4 : capAt σ4 s = some rem := by
            show (uV σ4).2.1 s = _
            rw [hv4, vCap_cap, if_pos rfl]
          have hpre : RPre (.reduceZombieCall rem s e) σ4 := by
            refine ⟨hI4, hc4, hrm, fun hcz => ?_⟩
            by_contra hne
            exact hcy ⟨hcz, hne⟩
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hI5 : UtInv'' z.2 := hrec _ σ4 hpre z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : UtInv'' z6.2 := by show UtInv''V (uV z6.2); rw [hv6]; exact hI5
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall s e) z6.2 hI6 y hy6
            · exact ⟨hI6, fun _ _ h => by cases h⟩
          · exact ⟨hI5, fun _ _ h => by cases h⟩
  | reduceZombieCall c s e =>
    intro σ hσ y hy
    obtain ⟨hI, hc, hnr, hcy⟩ := hσ
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
            have hp := hrec (.cTEDeleteCall (ptr, natToCref (zombieCteBits bits) n) false) σ hI z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact hp.1
            have hend := hp.2 a ha rfl
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
                show UtInv''V (uV x.2)
                rw [hv]
                exact utN_shrink hp.1 hc5 hnr hend
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [mem_ret_ok hy]; try dsimp only
                exact hp.1
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
    | _ => exact (rz_fail rfl hy).elim

/-- **`rec_del` keeps `UtInv''`** (every call, from its precondition). -/
theorem hr_recDel (k : RecDelCall) :
    HR (RPre k) (RPost k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact hr_lfp RPre RPost (fun f hf k => rd_step f hf k) k

theorem ikN_recDel_cte (s : CslotPtr) (e : Bool) : IKE UtInv'' (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  fun σ hI y hy => (hr_recDel (.cTEDeleteCall s e) σ hI y hy).inv

theorem ikN_recDel_fin (s : CslotPtr) (e : Bool) : IKE UtInv'' (recDel (Z := Unit) (.finaliseSlotCall s e)) :=
  fun σ hI y hy => (hr_recDel (.finaliseSlotCall s e) σ hI y hy).inv

/-- **`cap_delete` keeps `UtInv''`.** -/
theorem ikN_capDelete (slot : CslotPtr) : IKE UtInv'' (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (ikN_recDel_cte slot true) fun _ => ike_returnOk _

end

end Fl4Proofs.P3.SInvU
