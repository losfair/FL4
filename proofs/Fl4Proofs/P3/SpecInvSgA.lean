/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sg1): **SpecGlob's IRQ-node
slots as a carried fact, the family `S N M` and the deletion / transfer / TCB
install leaves** (spec side only, outside the JAtZ cone; imports ut8's
SpecInvUtP6 and the idle-thread frames SpecInvSgI6).

SpecGlob (SpecGlob.lean, l4v `valid_irq_node` + `valid_global_refs`) has three
clauses. Two of them follow from facts about every cap's range (`covR`, ut6):
"no non-frame cap names an IRQ-node CNode" from UtInv3's `IrqOutV`, and "no
non-frame cap names the idle thread" from **`IrqOutV (fun _ => idle)`**, the same
statement for the idle thread (l4v `valid_global_refs`: `idle_thread_ptr` is a
global ref, outside the `cap_range` of every cap, untyped caps included). The
third, the IRQ node's slots hold null or notification caps, is `NOV N`
(this module). The family carried across the entry is

* **`SV N M w := P3V N w ∧ IrqOutV M w ∧ NOV N w`** (`S N M σ := SV N M (uV σ)`):
  ut7/ut8's `P3 N` (UtInv'' and the node fact, `N` the node map), the range fact for
  a second map `M` (at the top `M = fun _ => idle`), and the node slots' contents.
  ut7/ut8 prove `IK (P3 K) m` for every `K` (no step but `set_irq_handler` reads the
  state's node), so the first two conjuncts come from their lemmas at `K = N` and
  `K = M` (`s_of`); only `NOV N` needs new proofs.
* A slot written with a cap that is not null or a notification cap is no node slot
  (`NotNode N sl`): it holds such a cap (`notNode_of_held`, by `NOV`), it is a
  lookup destination (`notNode_of_destRef`: some cap covers its object, `IrqOutV N`
  keeps every node CNode out of every cap's range), a TCB slot
  (`notNode_tcb`), or lies in an object a cap covers (`notNode_of_cov`).
* Deletion only nulls slots (`NulK`): `empty_slot`, `cap_delete_one`; `rec_del`
  (`no_recDel`, the least fixed point with a call-dependent precondition: the
  reduce-zombie call's Zombie is in its slot, so the swapped slots are no node slots).
* Leaves of the generated family (SpecInvSgG): `sg_capDeleteOne`, `sg_recDel_cte`,
  `sg_recDel_fin`, `sg_capDelete`, `sg_checkCapAt_ins`, `sg_installTcbCap`,
  `sg_doNormalTransfer`.
-/
import Fl4Proofs.P3.SpecInvUtP6
import Fl4Proofs.P3.SpecInvSgI6
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-- A null or notification cap (what an IRQ-node slot may hold). -/
def NtfnOrNull (a : Cap) : Prop := a = .nullCap ∨ ∃ r b rs, a = .notificationCap r b rs

/-- **The IRQ node's slots hold null or notification caps** (l4v `valid_irq_node`
with the IRQ handler slots' contents; SpecGlob.irq), for a fixed node map `N`. -/
def NOV (N : Irq → ObjRef) (w : UView) : Prop := ∀ irq a, w.2.1 (N irq, []) = some a → NtfnOrNull a

/-- The slot is no IRQ-node slot. -/
def NotNode (N : Irq → ObjRef) (sl : CslotPtr) : Prop := ∀ irq, sl ≠ (N irq, [])

/-- **The carried family** (module docstring). -/
def SV (N M : Irq → ObjRef) (w : UView) : Prop := P3V N w ∧ IrqOutV M w ∧ NOV N w

abbrev S (N M : Irq → ObjRef) (σ : State Unit) : Prop := SV N M (uV σ)

/-- Slots only nulled. -/
def NulK (w w' : UView) : Prop := ∀ s, w'.2.1 s = w.2.1 s ∨ w'.2.1 s = some .nullCap

theorem ntfnOrNull_null : NtfnOrNull .nullCap := Or.inl rfl

theorem nulK_refl (w : UView) : NulK w w := fun _ => Or.inl rfl

theorem nulK_trans {w1 w2 w3 : UView} (h1 : NulK w1 w2) (h2 : NulK w2 w3) : NulK w1 w3 := by
  intro s
  rcases h2 s with e | e
  · rw [e]; exact h1 s
  · exact Or.inr e

section Basic
variable {N M : Irq → ObjRef}

theorem nov_nulK {w w' : UView} (h : NOV N w) (hk : NulK w w') : NOV N w' := by
  intro irq a ha
  rcases hk (N irq, []) with e | e
  · rw [e] at ha; exact h irq a ha
  · rw [e] at ha; cases ha; exact ntfnOrNull_null

theorem nov_vCap {w : UView} (h : NOV N w) {sl : CslotPtr} {c : Cap} (hs : NotNode N sl ∨ NtfnOrNull c) :
    NOV N (vCap sl c w) := by
  intro irq a ha
  rw [vCap_cap] at ha
  split_ifs at ha with e
  · cases ha
    rcases hs with hs | hs
    · exact absurd e.symm (hs irq)
    · exact hs
  · exact h irq a ha

theorem notNode_of_held {w : UView} (h : NOV N w) {sl : CslotPtr} {c : Cap} (hs : w.2.1 sl = some c)
    (hc : ¬ NtfnOrNull c) : NotNode N sl := by
  intro irq e; subst e; exact hc (h irq c hs)

theorem notNode_of_cov {w : UView} (hO : IrqOutV N w) {s sl : CslotPtr} {c : Cap} (hs : w.2.1 s = some c)
    (hr : sl.1 ∈ covR c) : NotNode N sl := by
  intro irq e; subst e; exact hO irq s c hs hr

theorem notNode_of_destRef {w : UView} (hO : IrqOutV N w) {d : CslotPtr} (hD : DestRefV w d) : NotNode N d := by
  obtain ⟨s1, c1, hs1, hr1, -, -⟩ := hD
  exact notNode_of_cov hO hs1 (capRng_sub_covR _ (sRefs_sub_capRng _ hr1))

theorem tcbCnodeIndex_ne_nil (n : Nat) : tcbCnodeIndex n ≠ [] := by
  simp [tcbCnodeIndex, toBl]

theorem notNode_tcb (t : ObjRef) (n : Nat) : NotNode N (t, tcbCnodeIndex n) := by
  intro irq e
  exact tcbCnodeIndex_ne_nil n (congrArg Prod.snd e)

theorem not_ntfnOrNull_zombie (r : ObjRef) (b : Option Nat) (n : Nat) : ¬ NtfnOrNull (.zombie r b n) := by
  rintro (e | ⟨_, _, _, e⟩) <;> cases e

theorem sRefs_ntfnOrNull {c : Cap} (h : NtfnOrNull c) : sRefs c = ∅ := by
  rcases h with rfl | ⟨r, b, rs, rfl⟩ <;> rfl

/-! ## Deletion nulls slots -/

theorem nulK_emptySlot (s : CslotPtr) (info : Cap) (w : UView) :
    HV (· = w) (NulK w) (emptySlot (Z := Unit) s info) := by
  refine hv_mono (emptySlot_view s info w) fun w' h => ?_
  rcases h with ⟨rfl, -⟩ | rfl
  · exact nulK_refl _
  · intro x
    unfold vEs
    rw [vCap_cap]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem nulK_capDeleteOne (isl : CslotPtr) (w : UView) :
    HV (· = w) (NulK w) (capDeleteOne (Z := Unit) isl) := by
  unfold capDeleteOne
  refine hv_getCap_bind fun w0 c hw hc => ?_
  subst hw
  unfold NonDet.unless
  split
  · exact hv_ret _ (nulK_refl _)
  · refine hv_bind (R := (· = w0)) (hv_uk fun _ => uk_isFinalCap c) fun fin => ?_
    refine hv_bind (R := (· = w0)) (hv_uk fun _ => uk_fastFinalise c fin) fun _ => ?_
    exact nulK_emptySlot isl .nullCap w0

/-- `NOV` across a step that only nulls slots. -/
theorem nov_of_nulK {α : Type} {m : NonDet (State Unit) α} (h : ∀ w, HV (· = w) (NulK w) m) :
    IK (fun σ => NOV N (uV σ)) m :=
  fun σ hσ y hy => nov_nulK hσ (h (uV σ) σ rfl y hy)

/-! ## The family -/

theorem s_of {α : Type} {m : NonDet (State Unit) α} (h : ∀ K, IK (P3 K) m)
    (hn : ∀ σ, S N M σ → ∀ y ∈ (m σ).1, NOV N (uV y.2)) : IK (S N M) m :=
  fun σ hσ y hy => ⟨h N σ hσ.1 y hy, (h M σ ⟨hσ.1.1, hσ.2.1⟩ y hy).2, hn σ hσ y hy⟩

theorem s_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (S N M) m :=
  ik_of_uk (fun _ _ e hI => by show SV N M _; rw [e]; exact hI) h

theorem se_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (S N M) m := s_of_uk h

theorem s_of_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hI : S N M σ) : S N M σ' := by
  show SV N M (uV σ'); rw [h]; exact hI

theorem s_capDeleteOne_nov (sl : CslotPtr) : IK (fun σ => NOV N (uV σ)) (capDeleteOne (Z := Unit) sl) :=
  nov_of_nulK (nulK_capDeleteOne sl)

theorem sg_capDeleteOne (sl : CslotPtr) : IK (S N M) (capDeleteOne (Z := Unit) sl) :=
  s_of (fun _ => p3_capDeleteOne sl) fun σ h y hy => s_capDeleteOne_nov sl σ h.2.2 y hy

/-! ## `rec_del` -/

/-- The IRQ-node facts kept by the deletion (no untyped invariant needed). -/
abbrev NO (N : Irq → ObjRef) (σ : State Unit) : Prop := IO N σ ∧ NOV N (uV σ)

theorem no_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (NO N) m :=
  ik_of_uk (fun _ _ e hI => by show IrqOutV N _ ∧ NOV N _; rw [e]; exact hI) h

theorem noe_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (NO N) m := no_of_uk h

theorem no_capDeleteOne (sl : CslotPtr) : IK (NO N) (capDeleteOne (Z := Unit) sl) :=
  fun σ h y hy => ⟨io_capDeleteOne sl σ h.1 y hy, s_capDeleteOne_nov sl σ h.2 y hy⟩

theorem no_emptySlot (s : CslotPtr) (info : Cap) : IK (NO N) (emptySlot (Z := Unit) s info) :=
  fun σ h y hy => ⟨io_emptySlot s info σ h.1 y hy, nov_of_nulK (nulK_emptySlot s info) σ h.2 y hy⟩

theorem no_finaliseCap (c : Cap) (fin : Bool) : IK (NO N) (finaliseCap (Z := Unit) c fin) := by
  by_cases hirq : ∃ i, c = .irqHandlerCap i
  · obtain ⟨i, rfl⟩ := hirq
    simp only [finaliseCap, deletingIrqHandler, getIrqSlot]
    repeat' (first | exact no_capDeleteOne _ | ik_step0)
  · exact no_of_uk (uk_finaliseCap_nonIrq c (fun i e => hirq ⟨i, e⟩) fin)

/-- `cap_swap_for_delete` of two non-node slots. -/
theorem no_capSwapForDelete {s1 s2 : CslotPtr} (h1 : NotNode N s1) (h2 : NotNode N s2) :
    IK (NO N) (capSwapForDelete (Z := Unit) s1 s2) := by
  intro σ hσ y hy
  refine ⟨io_capSwapForDelete s1 s2 σ hσ.1 y hy, ?_⟩
  have key : HV (· = uV σ) (fun w' => NOV N w') (capSwapForDelete (Z := Unit) s1 s2) := by
    unfold capSwapForDelete NonDet.when
    split
    · rename_i hne
      refine hv_getCap_bind fun w1 c1 hw _ => ?_
      subst hw
      refine hv_getCap_bind fun w' c2 hw' _ => ?_
      subst hw'
      refine hv_mono (capSwap_view hne c1 c2) fun w' e => ?_
      subst e
      refine nov_vCap (nov_vCap ?_ (Or.inl h1)) (Or.inl h2)
      intro irq a ha
      have e1 : sw s1 s2 (N irq, []) = (N irq, []) := by
        unfold sw; rw [if_neg (fun e => h1 irq e.symm), if_neg (fun e => h2 irq e.symm)]
      have ha' : (uV σ).2.1 (sw s1 s2 (N irq, [])) = some a := ha
      rw [e1] at ha'
      exact hσ.2 irq a ha'
    · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w' e => e ▸ hσ.2
  exact key σ rfl y hy

macro "no0_auto" : tactic => `(tactic| repeat' (first
  | exact no_emptySlot _ _
  | (refine no_of_uk fun _ => ?_; uk_leaf; done) | (refine noe_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- The deletion's call-dependent precondition: a reduce-zombie call's cap is in its slot. -/
def NPre (N : Irq → ObjRef) : RecDelCall → State Unit → Prop
  | .reduceZombieCall c s _, σ => NO N σ ∧ capAt σ s = some c
  | _, σ => NO N σ

theorem NPre.no {k : RecDelCall} {σ : State Unit} (h : NPre N k σ) : NO N σ := by
  cases k with
  | reduceZombieCall => exact h.1
  | _ => exact h

/-- The remainder of a finalised cap written back into its slot. -/
theorem fin_rem {w : UView} (h : NOV N w) {sl : CslotPtr} {cap : Cap} (hc : w.2.1 sl = some cap)
    {σ : State Unit} {x : (Cap × Cap) × State Unit} {fin : Bool} (hx : x ∈ (finaliseCap (Z := Unit) cap fin σ).1) :
    NotNode N sl ∨ NtfnOrNull x.1.1 := by
  by_cases hn : NtfnOrNull cap
  · right
    have e : x.1.1 = .nullCap := finaliseCap_null (sRefs_ntfnOrNull hn) fin σ x hx
    rw [e]; exact ntfnOrNull_null
  · exact Or.inl (notNode_of_held h hc hn)

theorem no_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (NPre N k) (fun _ => NO N) (f k)) (k : RecDelCall) :
    HR (NPre N k) (fun _ => NO N) (recDelF (Z := Unit) f k) := by
  have hfin : ∀ s e, IKE (ε := Unit) (NO N) (f (.finaliseSlotCall s e) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun s e σ h y hy => hrec (.finaliseSlotCall s e) σ h y hy
  have hcte : ∀ s e, IKE (ε := Unit) (NO N) (f (.cTEDeleteCall s e) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun s e σ h y hy => hrec (.cTEDeleteCall s e) σ h y hy
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    replace hσ : NO N σ := hσ
    refine (show IKE (NO N) (recDelF (Z := Unit) f (.cTEDeleteCall s e)) by
      unfold recDelF withoutPreemption; no0_auto
      all_goals first | exact hfin _ _ | exact hcte _ _) σ hσ y hy
  | finaliseSlotCall sl e =>
    intro σ hσ y hy
    replace hσ : NO N σ := hσ
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
      have hO3 : NO N σ3 := no_finaliseCap cap _ _ hσ _ hx3
      have hc3 : capAt σ3 sl = some cap := finaliseCap_keepAt hc _ _ hx3
      have hcov : covR rem ⊆ covR cap := finaliseCap_cov cap _ _ _ hx3
      have hrem : NotNode N sl ∨ NtfnOrNull rem := fin_rem (N := N) hσ.2 hc hx3
      have hO4 : NO N σ3 → IrqOutV N (vCap sl rem (uV σ3)) ∧ NOV N (vCap sl rem (uV σ3)) := fun h =>
        ⟨irqOut_vCap h.1 (covBy_of hc3 hcov) sl, nov_vCap h.2 hrem⟩
      try dsimp only at hy3
      split at hy3
      · rw [mem_ret_ok hy3]; exact hO3
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]
            have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
            show IrqOutV N (uV σ4) ∧ NOV N (uV σ4); rw [hv4]; exact hO4 hO3
          · obtain ⟨x, -, hx⟩ := mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
          have hO5 : NO N σ4 := by show IrqOutV N (uV σ4) ∧ NOV N (uV σ4); rw [hv4]; exact hO4 hO3
          have hc4 : capAt σ4 sl = some rem := by
            show (uV σ4).2.1 sl = some rem; rw [hv4, vCap_cap, if_pos rfl]
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hI5 : NO N z.2 := hrec (.reduceZombieCall rem sl e) σ4 ⟨hO5, hc4⟩ z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : NO N z6.2 := by show IrqOutV N (uV z6.2) ∧ NOV N (uV z6.2); rw [hv6]; exact hI5
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall sl e) z6.2 hI6 y hy6
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
          intro σ hσ y hy
          obtain ⟨hσ, hcs⟩ := hσ
          have h1 : NotNode N (firstCslotOf (.zombie ptr bits (n + 1))) :=
            notNode_of_cov (w := uV σ) hσ.1 hcs (by simp [firstCslotOf, covR, capRng, objRefs])
          have h2 : NotNode N s := notNode_of_held (w := uV σ) hσ.2 hcs (not_ntfnOrNull_zombie _ _ _)
          refine (show IKE (NO N) (recDelF (Z := Unit) f (.reduceZombieCall (.zombie ptr bits (n + 1)) s false)) by
            simp only [recDelF, withoutPreemption]
            repeat' (first | exact no_capSwapForDelete h1 h2 | ik_step0 | ik_unfold)) σ hσ y hy
        | true =>
          intro σ hσ y hy
          replace hσ := hσ.1
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
          · obtain rfl := mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := mem_bindE' hy
            have hp : NO N z.2 := hrec (.cTEDeleteCall _ _) σ hσ z hz
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
                show IrqOutV N (uV x.2) ∧ NOV N (uV x.2)
                rw [hv]
                exact ⟨irqOut_vCap hp.1 (covBy_of hc5 (fun q hq => by simpa [covR, capRng, objRefs] using hq)) s,
                  nov_vCap hp.2 (Or.inl (notNode_of_held (w := uV z.2) hp.2 hc5 (not_ntfnOrNull_zombie _ _ _)))⟩
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

/-- **`rec_del` keeps the IRQ-node facts** (no premise beyond the call's own precondition). -/
theorem no_recDel (k : RecDelCall) : HR (NPre N k) (fun _ => NO N) (recDel (Z := Unit) k) := by
  unfold recDel
  exact hr_lfp (NPre N) (fun _ _ => NO N) (fun f hf k => no_recDelF f hf k) k

theorem sg_recDel_cte (s : CslotPtr) (e : Bool) : IKE (S N M) (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  s_of (fun _ => p3_recDel_cte s e) fun σ h y hy => (no_recDel (.cTEDeleteCall s e) σ ⟨h.1.2, h.2.2⟩ y hy).2

theorem sg_recDel_fin (s : CslotPtr) (e : Bool) : IKE (S N M) (recDel (Z := Unit) (.finaliseSlotCall s e)) :=
  s_of (fun _ => p3_recDel_fin s e) fun σ h y hy => (no_recDel (.finaliseSlotCall s e) σ ⟨h.1.2, h.2.2⟩ y hy).2

theorem sg_capDelete (slot : CslotPtr) : IKE (S N M) (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (sg_recDel_cte _ _) fun _ => ike_returnOk _

/-! ## Inserts -/

/-- **`cap_insert` keeps `NOV`** when the destination is no node slot or the cap is null /
a notification cap (the source is rewritten only when it holds an untyped cap). -/
theorem nov_capInsert (c : Cap) (src dest : CslotPtr) :
    HV (fun w => NOV N w ∧ (NotNode N dest ∨ NtfnOrNull c)) (NOV N) (capInsert (Z := Unit) c src dest) := by
  refine hv_pin fun w0 hw0 => ?_
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  subst hw
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun _ => ?_
  unfold setUntypedCapAsFull
  split
  · rename_i hut
    have hsrc : NotNode N src := by
      refine notNode_of_held hw0.1 hsc ?_
      rintro (e | ⟨_, _, _, e⟩) <;> (subst e; simp [isUntypedCap] at hut)
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
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
    exact nov_vCap (nov_vCap hw0.1 (Or.inl hsrc)) hw0.2
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
    exact nov_vCap hw0.1 hw0.2

/-- **`cap_insert` keeps `SV N M`** (ut7's `hv_capInsert3` at `N` and `M`, and `nov_capInsert`). -/
theorem hv_capInsertS (c : Cap) (src dest : CslotPtr) :
    HV (fun w => SV N M w ∧ CI3 w c src ∧ PosOK w dest ∧ (NotNode N dest ∨ NtfnOrNull c)) (SV N M)
      (capInsert (Z := Unit) c src dest) := by
  intro σ hσ y hy
  obtain ⟨⟨h3, hM, hn⟩, hci, hp, hd⟩ := hσ
  exact ⟨hv_capInsert3 c src dest σ ⟨h3, hci, hp⟩ y hy,
    (hv_capInsert3 (N := M) c src dest σ ⟨⟨h3.1, hM⟩, hci, hp⟩ y hy).2,
    nov_capInsert c src dest σ ⟨hn, hd⟩ y hy⟩

/-- `set_cap` keeps `NOV` off the node slots, or of a null / notification cap. -/
theorem nov_setCap (c : Cap) (sl : CslotPtr) :
    HV (fun w => NOV N w ∧ (NotNode N sl ∨ NtfnOrNull c)) (NOV N) (setCap (Z := Unit) c sl) := by
  refine hv_pin fun w hw => ?_
  exact hv_mono (hv_setCap c sl w) fun w' e => e ▸ nov_vCap hw.1 hw.2

/-! ## TCB installs -/

theorem nov_checkCapAt_ins (c : Cap) (src : CslotPtr) (t : Cap) (sl : CslotPtr) (tt : ObjRef) (n : Nat) :
    IK (fun σ => NOV N (uV σ)) (checkCapAt (Z := Unit) c src (checkCapAt t sl (capInsert c src (tt, tcbCnodeIndex n)))) := by
  show HV (NOV N) (NOV N) _
  unfold checkCapAt
  refine hv_getCap_bind fun w c' hw _ => ?_
  unfold NonDet.when
  split
  · refine hv_getCap_bind fun w' c'' hw' _ => ?_
    subst hw'
    split
    · exact hv_pre (nov_capInsert c src _) fun w1 e => e ▸ ⟨hw, Or.inl (notNode_tcb tt n)⟩
    · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w1 e => e ▸ hw
  · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w1 e => e ▸ hw

theorem sg_checkCapAt_ins (c : Cap) (src : CslotPtr) (t : ObjRef) (sl : CslotPtr) (n : Nat) (hn : n < 6) :
    IK (S N M) (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap t) sl (capInsert c src (t, tcbCnodeIndex n)))) :=
  s_of (fun _ => p3_checkCapAt_ins c src t sl n hn) fun σ h y hy =>
    nov_checkCapAt_ins c src (.threadCap t) sl t n σ h.2.2 y hy

theorem sg_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr))
    (hn : n < 6) : IKE (S N M) (installTcbCap (Z := Unit) target slot n slotOpt) := by
  cases slotOpt with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine ike_bind (sg_capDelete _) fun _ => ?_
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (sg_checkCapAt_ins c src target slot n hn)

/-! ## The IPC cap transfer -/

theorem sg_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (caps : List (Cap × CslotPtr)) (n : Nat) (slots : List CslotPtr) (mi : MessageInfo) (σ : State Unit),
      S N M σ → slots.length ≤ 1 → (∀ d ∈ slots, DestRefV (uV σ) d) →
      (slots ≠ [] → ∀ p ∈ caps, capAt σ p.2 = some p.1) →
      ∀ y ∈ (transferCapsLoop (Z := Unit) ep rb n caps slots mi σ).1, S N M y.2
  | [], n, slots, mi, σ, hI, _, _, _, y, hy => by
    unfold transferCapsLoop at hy; rw [Set.mem_singleton_iff.1 hy]; exact hI
  | (cap, slot) :: more, n, slots, mi, σ, hI, hl, hD, hc, y, hy => by
    have ih := sg_transferCapsLoop ep rb more (n + 1)
    unfold transferCapsLoop constOnFailure NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hyz : y.2 = z.2 := by
      obtain ⟨r, s⟩ := z
      cases r <;> (rw [Set.mem_singleton_iff.1 hy])
    rw [hyz]
    clear hy hyz
    replace hz := run_returnOk_bind_mem hz
    try dsimp only at hz
    split at hz
    · obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
      have hv := uk_mem (fun _ => uk_setExtraBadge _ _ _) hx
      obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
      refine ih slots _ x.2 (s_of_view hv hI) hl (fun d hd => by rw [hv]; exact hD d hd) (fun hne p hp => ?_) w hw
      rw [capAt_of_view hv]; exact hc hne p (List.mem_cons.2 (Or.inr hp))
    · split at hz
      · rename_i hne
        obtain ⟨z0, hz0, ⟨c', hc', hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
        · obtain ⟨r0, s0⟩ := z0
          simp only at hc'; subst hc'
          have hv0 : uV s0 = uV σ := uk_deriveCap slot cap σ rfl _ hz0
          have hd := okv_deriveCapR slot cap σ rfl c' s0 hz0
          obtain ⟨z1, hz1, ⟨u, hu, hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
          · obtain ⟨hnn, hs1⟩ := whenE_throw_ok hz1 hu
            obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
            rw [hs1] at hx
            have hI0 := s_of_view hv0 hI
            have hcs := hc hne (cap, slot) (List.mem_cons.2 (Or.inl rfl))
            obtain ⟨dd, tl, rfl⟩ : ∃ dd tl, slots = dd :: tl := by
              cases slots with
              | nil => exact absurd rfl hne
              | cons a t => exact ⟨a, t, rfl⟩
            have hok : CI3 (uV s0) c' slot := by
              refine ⟨cap, by show capAt s0 slot = _; rw [capAt_of_view hv0]; exact hcs, ?_⟩
              rcases hd hnn with ⟨e1, hu', hk⟩ | hR
              · exact Or.inl ⟨e1, hu', by rw [hv0]; exact hk⟩
              · exact Or.inr hR
            have hDd : DestRefV (uV s0) dd := by rw [hv0]; exact hD dd (List.mem_cons_self)
            have hP : PosOK (uV s0) dd := posOK_of_destRef hI0.1.1.2 hDd
            have hIx := hv_capInsertS c' slot dd s0
              ⟨hI0, hok, hP, Or.inl (notNode_of_destRef hI0.1.2 hDd)⟩ x hx
            obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
            have htl : tl = [] := by
              simp only [List.length_cons] at hl; exact List.eq_nil_of_length_eq_zero (by omega)
            subst htl
            exact ih [] _ x.2 hIx (by simp) (fun _ h => absurd h List.not_mem_nil) (fun h => absurd rfl h) w hw
          · have hs1 : z1.2 = s0 := by
              unfold NonDetE.whenE at hz1
              split at hz1 <;> (rw [Set.mem_singleton_iff.1 hz1])
            show S N M z1.2
            rw [hs1]; exact s_of_view hv0 hI
        · exact s_of_view (uk_deriveCap slot cap σ rfl _ hz0) hI
      · rw [Set.mem_singleton_iff.1 hz]; exact hI

theorem sg_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (recv : ObjRef)
    (rbuf : Option ObjRef) (σ : State Unit) (hI : S N M σ) (hc : ∀ p ∈ caps, capAt σ p.2 = some p.1) :
    ∀ y ∈ (transferCaps (Z := Unit) info caps ep recv rbuf σ).1, S N M y.2 := by
  intro y hy
  unfold transferCaps at hy
  obtain ⟨x, hx, hy⟩ := hy
  have hv := uk_mem (fun _ => uk_getReceiveSlots _ _) hx
  have hlen := getReceiveSlots_len recv rbuf σ x hx
  have hdst := getReceiveSlots_dest recv rbuf σ x hx
  obtain ⟨x2, hx2, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx2
  dsimp only at hy
  cases rbuf with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact s_of_view hv hI
  | some b =>
    exact sg_transferCapsLoop ep b caps 0 x.1 _ x.2 (s_of_view hv hI) hlen
      (fun d hd => by rw [hv]; exact hdst d hd)
      (fun _ p hp => by rw [capAt_of_view hv]; exact hc p hp) y hy

/-- **The normal IPC transfer keeps `S N M`** (no premise). -/
theorem sg_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (recv : ObjRef) (rbuf : Option ObjRef) :
    IK (S N M) (doNormalTransfer (Z := Unit) sender sbuf ep badge grant recv rbuf) := by
  intro σ hI y hy
  unfold doNormalTransfer at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  have hv1 := uk_mem (fun _ => uk_getMessageInfo _) hx1
  have hI1 : S N M x1.2 := s_of_view hv1 hI
  have tail : ∀ (caps : List (Cap × CslotPtr)) (s : State Unit), S N M s → (∀ p ∈ caps, capAt s p.2 = some p.1) →
      ∀ y ∈ ((do
        let mrsTransferred ← copyMrs (Z := Unit) sender sbuf recv rbuf x1.1.miLength
        let mi' ← transferCaps x1.1 caps ep recv rbuf
        setMessageInfo recv { miLength := mrsTransferred, miExtraCaps := mi'.miExtraCaps, miCapsUnwrapped := mi'.miCapsUnwrapped, miLabel := x1.1.miLabel }
        asUser recv (setRegister badge_register badge)) s).1, S N M y.2 := by
    intro caps s hs hc y hy
    obtain ⟨x3, hx3, hy⟩ := hy
    have hv3 := uk_mem (fun _ => uk_copyMrs _ _ _ _ _) hx3
    obtain ⟨x4, hx4, hy⟩ := hy
    have hI4 := sg_transferCaps _ _ _ _ _ x3.2 (s_of_view hv3 hs)
      (fun p hp => by rw [capAt_of_view hv3]; exact hc p hp) x4 hx4
    exact (s_of_uk fun _ => by uk_auto) x4.2 hI4 y hy
  simp only at hy
  split at hy
  · obtain ⟨x2, hx2, hy⟩ := hy
    unfold NonDetE.catch at hx2
    obtain ⟨z, hz, hx2⟩ := hx2
    have hvz : uV z.2 = uV x1.2 := uk_lookupExtraCaps _ _ _ x1.2 rfl z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      exact tail [] s (s_of_view hvz hI1) (fun p hp => absurd hp List.not_mem_nil) y hy
    | ok l =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      refine tail l s (s_of_view hvz hI1) (fun p hp => ?_) y hy
      have := okv_lookupExtraCaps sender sbuf x1.1 x1.2 rfl l s hz p hp
      rw [capAt_of_view hvz]; exact this
  · obtain ⟨x2, hx2, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hx2
    exact tail [] x1.2 hI1 (fun p hp => absurd hp List.not_mem_nil) y hy

end Basic

end

end Fl4Proofs.P3.SInvG
