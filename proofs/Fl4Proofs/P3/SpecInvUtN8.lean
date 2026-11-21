/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut6): **the IRQ node lies
outside every untyped region and no cap covers it** (`IrqOutV`, lead decision
on ut5's IRQ-node gap, option (a)), and the cap-domination step relation that
carries it (spec side only; imports SpecInvUtN7).

* `covR c`: the addresses a cap covers, an untyped cap its whole region
  (`delR`), any other cap its `capRng`.
* **`IrqOutV N w` [J]** (l4v `valid_irq_node` + `valid_global_refs`: the IRQ
  node CNodes are global refs, outside the `cap_range` of every cap, untyped
  ones included): `∀ irq s c, w.2.1 s = some c → N irq ∉ covR c`.
  `posOK_irq`: it makes the IRQ-node slot `(N irq, [])` a `PosOK` destination
  (SetIRQHandler's `cap_insert`). Boot: vacuous (only null caps).
* `CD m' m` (cap domination): every address a cap of `m'` covers is covered by
  some cap of `m`. Reflexive, transitive, and `IrqOutV N` is antitone along it
  (`irqOut_cd`). Every writer of the entry dominates: deletion and moves only
  shrink or rename caps, a derived cap covers a part of its source
  (`RefRel`), a retyped object lies in its untyped's region, an untyped child
  inside its parent. `cd_vEs`, `cd_vCap`, `cd_vRen`, `cd_capRel`.
* `DMV P m`: every outcome of `m` from a view satisfying `P` dominates its
  start. `dm_emptySlot`, `dm_capDeleteOne`, `dm_capInsert` (a `RefRel` cap).
* **`UtInv3 σ := UtInv'' σ ∧ IrqOutV σ.interruptIrqNode (uV σ)`**: `ik3_of`
  combines `IK UtInv''`, `DMV UtInv''V` and the IRQ-node frame (invB's `GK`
  family proves it for every function of the syscall entry).
-/
import Fl4Proofs.P3.SpecInvUtN7
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The addresses a cap covers: an untyped cap its region, any other cap its `capRng`. -/
def covR : Cap → Set ObjRef
  | .untypedCap _ b n _ => delR b n
  | c => capRng c

theorem capRng_sub_covR (c : Cap) : capRng c ⊆ covR c := by
  intro r hr; cases c <;> simp_all [covR, capRng, objRefs]

theorem covR_nonUt {c : Cap} (h : ∀ d b n f, c ≠ .untypedCap d b n f) : covR c = capRng c := by
  cases c <;> first | rfl | exact absurd rfl (h _ _ _ _)

theorem covR_null : covR .nullCap = ∅ := by simp [covR, capRng, objRefs]

/-- **IrqOut [J]** (l4v `valid_irq_node` + `valid_global_refs`). -/
def IrqOutV (N : Irq → ObjRef) (w : UView) : Prop := ∀ irq s c, w.2.1 s = some c → N irq ∉ covR c

/-- Cap domination. -/
def CD (m' m : CslotPtr → Option Cap) : Prop :=
  ∀ s c r, m' s = some c → r ∈ covR c → ∃ s' c', m s' = some c' ∧ r ∈ covR c'

theorem cd_refl (m : CslotPtr → Option Cap) : CD m m := fun s c r h hr => ⟨s, c, h, hr⟩

theorem cd_trans {m1 m2 m3 : CslotPtr → Option Cap} (h12 : CD m2 m1) (h23 : CD m3 m2) : CD m3 m1 := by
  intro s c r h hr
  obtain ⟨s', c', h', hr'⟩ := h23 s c r h hr
  exact h12 s' c' r h' hr'

theorem irqOut_cd {N : Irq → ObjRef} {w w' : UView} (h : IrqOutV N w) (hd : CD w'.2.1 w.2.1) : IrqOutV N w' := by
  intro irq s c hs hr
  obtain ⟨s', c', h', hr'⟩ := hd s c _ hs hr
  exact h irq s' c' h' hr'

theorem posOK_irq {N : Irq → ObjRef} {w : UView} (h : IrqOutV N w) (irq : Irq) : PosOK w (N irq, []) := by
  refine ⟨fun ⟨u, d, b, n, f, hu, hr⟩ => (h irq u _ hu hr).elim, fun s c' hs hr => ?_⟩
  exact (h irq s c' hs (capRng_sub_covR _ (sRefs_sub_capRng _ hr))).elim

theorem boot_irqOut (N : Irq → ObjRef) : IrqOutV N (uV (initASt (Z := Unit))) := by
  intro irq s c hs
  rw [init_capAt hs, covR_null]; exact fun h => h

/-! ## Domination of the view edits -/

theorem cd_vCap {w : UView} {sl : CslotPtr} {c : Cap}
    (h : ∀ r, r ∈ covR c → ∃ s' c', w.2.1 s' = some c' ∧ r ∈ covR c') : CD (vCap sl c w).2.1 w.2.1 := by
  intro s c' r hs hr
  rcases upd_cap hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
  · exact h r hr
  · exact ⟨s, c', hs', hr⟩

theorem cd_vCap_null {w : UView} (sl : CslotPtr) : CD (vCap sl .nullCap w).2.1 w.2.1 :=
  cd_vCap fun r hr => by rw [covR_null] at hr; exact hr.elim

theorem cd_vEs {w : UView} (s : CslotPtr) : CD (vEs s w).2.1 w.2.1 := cd_vCap_null s

theorem cd_vRen {π : CslotPtr → CslotPtr} {w : UView} : CD (vRen π w).2.1 w.2.1 :=
  fun s c r hs hr => ⟨π s, c, hs, hr⟩

/-- A cap derived from the cap `c0` of a slot (`RefRel`) is dominated by it. -/
theorem cd_capRel {w : UView} {src sl : CslotPtr} {c0 c : Cap} (hs : w.2.1 src = some c0) (hR : RefRel c0 c) :
    CD (vCap sl c w).2.1 w.2.1 := by
  refine cd_vCap fun r hr => ⟨src, c0, hs, ?_⟩
  rw [covR_nonUt hR.2.2.2.2] at hr
  exact capRng_sub_covR _ (hR.1 hr)

/-! ## Domination of the writers -/

/-- Every outcome from a view satisfying `P` dominates its start. -/
def DMV (P : UView → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ w, P w → HV (· = w) (fun w' => CD w'.2.1 w.2.1) m

theorem dm_of_uk {P : UView → Prop} {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : DMV P m := by
  intro w _ σ hσ y hy
  rw [h (uV σ) σ rfl y hy, hσ]; exact cd_refl _

theorem dm_emptySlot (s : CslotPtr) (info : Cap) : DMV (fun _ => True) (emptySlot (Z := Unit) s info) := by
  intro w _
  refine hv_mono (emptySlot_view s info w) fun w' h => ?_
  rcases h with ⟨rfl, -⟩ | rfl
  · exact cd_refl _
  · exact cd_vEs s

theorem dm_capDeleteOne (sl : CslotPtr) : DMV (fun _ => True) (capDeleteOne (Z := Unit) sl) := by
  intro w _
  unfold capDeleteOne
  refine hv_getCap_bind fun w0 c hw hc => ?_
  subst hw
  unfold NonDet.unless
  split
  · exact hv_ret _ (cd_refl _)
  · refine hv_bind (R := (· = w0)) (hv_uk fun _ => uk_isFinalCap c) fun fin => ?_
    refine hv_bind (R := (· = w0)) (hv_uk fun _ => uk_fastFinalise c fin) fun _ => ?_
    exact dm_emptySlot sl .nullCap w0 trivial

/-- **`cap_insert` of a derived non-untyped cap dominates.** -/
theorem dm_capInsert (c : Cap) (src dest : CslotPtr) :
    DMV (fun w => UtInv''V w ∧ ∀ c0, w.2.1 src = some c0 → RefRel c0 c) (capInsert (Z := Unit) c src dest) := by
  intro w0 hw0
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  subst hw
  have hR := hw0.2 sc hsc
  have hnu := hR.2.2.2.2
  have hnu' : isUntypedCap c = false := by
    cases c <;> first | rfl | exact absurd rfl (hnu _ _ _ _)
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  unfold setUntypedCapAsFull
  rw [if_neg (fun h => by rw [hnu'] at h; exact Bool.false_ne_true h.2.1)]
  refine hv_pure_bind ?_
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
  exact cd_capRel hsc hR

/-! ## The combined invariant -/

/-- **The carried untyped invariant with the IRQ node fact.** -/
def UtInv3 (σ : State Unit) : Prop := UtInv'' σ ∧ IrqOutV σ.interruptIrqNode (uV σ)

theorem UtInv3.ut'' {σ : State Unit} (h : UtInv3 σ) : UtInv'' σ := h.1

/-- `UtInv3` kept: `UtInv''` kept, the outcome dominates, the IRQ node kept. -/
theorem ik3_of {α : Type} {m : NonDet (State Unit) α} (hI : IK UtInv'' m) (hD : DMV UtInv''V m)
    (hG : ∀ σ y, y ∈ (m σ).1 → y.2.interruptIrqNode = σ.interruptIrqNode) : IK UtInv3 m := by
  intro σ hσ y hy
  refine ⟨hI σ hσ.1 y hy, ?_⟩
  rw [hG σ y hy]
  exact irqOut_cd hσ.2 (hD (uV σ) hσ.1 σ rfl y hy)

theorem boot_utInv3 : UtInv3 (initASt (Z := Unit)) := ⟨boot_utInv'', boot_irqOut _⟩

end

end Fl4Proofs.P3.SInvU
