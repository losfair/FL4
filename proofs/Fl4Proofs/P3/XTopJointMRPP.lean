/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr1, irq1 NEXT (1) with kfix1's
correction): **the preemption point and the IRQ take against `MachPlat`**, the
platform relation `MR` between FL4's arch state and the spec's machine state
(XTopJointMachRel), in place of the unsatisfiable `PPPlat.now/irq` and the
degenerate `IrqPlat.take`.

* `PPPlatA` / `IrqPlatA` [P]: the arch-only parts of `PPPlat` / `IrqPlat`
  (`irqAR`, `minBudget`; `takeAR`, `noIpi`, `ackAR`), each a statement about
  the arch state alone (no spec state): `PPPlat.toA`, `IrqPlat.toA`, and the
  model satisfies them whenever `AR` is kept by its (identity-like) ops.
* `update_timestamp_mr`: FL4's `update_timestamp` reads the clock once (the
  only arch op that returns a new state on it), so `MR a ms` becomes
  `MR r.2 (gctState ms)`.
* `MachPlat.irqAtE`: `irq_pending` at a related state, the spec's
  `getActiveIRQ true` outcome, `MR` after, and the last machine time kept.
* `pp_err_ms` (spec): every `error` outcome of `preemptionPoint` has machine
  state `gaiState (gctState σ.ms)` (one clock read, one IRQ sample) and
  satisfies `ValidMachineTime`.
* `JAtZ.ppJDM` / `JAtZ.ppJHM`: XTopJointPP's `ppJD` / XTopJointPPH's `ppJH`
  under `MachPlat` + `MR a σ.ms` + `ValidMachineTime σ` (instead of
  `PPPlat`), with `MR r.2.2 σ'.ms ∧ ValidMachineTime σ'` added to every
  outcome. Since kfix1 FL4 reads the line right after the time stamp on every
  path past the work limit, like the spec, so the relation moves in one
  `gctState` and one `gaiState` step: below the limit nothing is read
  (`σ' = σ`, `a` unchanged); past it every outcome (the budget/domain error
  with the line false included) is at `(a2, σ2)` after both reads.
  These are adapted copies: the originals take `PPPlat`, which is false
  (`PPPlat.false`), so they cannot be instantiated; the copies use the
  per-state `MachPlat.nowAgree` and `irqAtE` at the two read points.
* `afterInv_of_mcsJM`: XTopJointIrqZR's `afterInv_of_mcsJ` with
  `MachPlat.takeAt` at the `take_pending_irq` read (`MR` after the MCS
  preemption point asked in its hypothesis) in place of `IrqPlat.take`.
-/
import Fl4Proofs.P3.XTopJointMachRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **The arch-only part of `PPPlat`** [P] (no spec state: the IRQ read keeps
the CR3 relation, the minimum budget constant). -/
structure PPPlatA (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  irqAR : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄
  minBudget : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄

theorem PPPlat.toA (h : PPPlat arI AR) : PPPlatA arI AR := ⟨h.irqAR, h.minBudget⟩

variable (arI) in
/-- **The arch-only part of `IrqPlat`** [P] (`IrqPlat` without its ∀-spec-state
`take`). -/
structure IrqPlatA (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  takeAR : ∀ a c, AR a c → arI.take_pending_irq a ⦃ r => AR r.2 c ⦄
  noIpi : ∀ a : A, arI.take_pending_irq a ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄
  ackAR : ∀ a i c, AR a c → arI.ack_irq a i ⦃ a' => AR a' c ⦄

theorem IrqPlat.toA (h : IrqPlat arI AR) : IrqPlatA arI AR := ⟨h.takeAR, h.noIpi, h.ackAR⟩

/-- **`update_timestamp` moves `MR` by one clock read.** -/
theorem update_timestamp_mr (hM : MachPlat arI MR) {a : A} {ms : Fl4Spec.MachineState} (hR : MR a ms) (s : S) :
    sched.update_timestamp st arI s a ⦃ r => MR r.2 (gctState ms) ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hM.now a ms hR) ?_
  rintro ⟨now, a1⟩ ⟨-, ha1⟩
  try simp only [WP.uncurry'_pair]
  step with P1.LawfulStore.cur_cpu_spec as ⟨c', ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [Sched.num_domains_eq, if_neg (by decide), WP.spec_ok]
  exact ha1

/-- **`irq_pending` at a related state**: the spec's sample, `MR` after, the
memory and the last machine time kept. -/
theorem MachPlat.irqAtE (hM : MachPlat arI MR) {a : A} {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) :
    arI.irq_pending a ⦃ r => ∃ irq ms,
      Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
      (r.1 = true ↔ irq ≠ none) ∧ ms.underlyingMemory = σ.machineState.underlyingMemory ∧ MR r.2 ms ∧
      ms.lastMachineTime = σ.machineState.lastMachineTime ⦄ := by
  refine WP.spec_mono (hM.irqPending a _ hR) ?_
  rintro r ⟨h1, h2⟩
  exact ⟨_, _, doMachineOp_single (getActiveIRQ_eq true _), h1, rfl, h2, rfl⟩

/-- **The machine state of every `error` outcome of the spec's preemption
point**: one clock read and one IRQ sample, and `ValidMachineTime`. -/
theorem pp_err_ms (hnd : Fl4Spec.numDomains = 1) {σ σ' : Fl4Spec.State Unit}
    (h : (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) :
    σ'.machineState = gaiState (gctState σ.machineState) ∧ ValidMachineTime σ' := by
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  have e : σ' = _ := pp_err_eq hE (doMachineOp_single (getActiveIRQ_eq true _)) _ h rfl
  subst e
  exact ⟨rfl, BitVec.le_refl _, (validMachineTime_gct σ).2⟩

set_option maxHeartbeats 16000000 in
/-- **XTopJointPP's `ppJD` under `MachPlat`** (module docstring), with `MR`
and `ValidMachineTime` at every outcome. -/
theorem JAtZ.ppJDM {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hPA : PPPlatA arI AR)
    (hR : MR a σ.machineState) (hV : ValidMachineTime σ) (hRd : PPR0 σ) :
    sched.preemption_point st arI s a ⦃ r => ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
      XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧
      (r.1 = .Ok () → (∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.2.1 r.2.2 σ') ∧ PPR0 σ') ∧
      MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
  generalize hPP : ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 = PPs
  unfold sched.preemption_point
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨w, _⟩
  step with obj.ks_set.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨Ac1, Lst1, J1⟩ := J.workUnitsJD arI w
  split
  swap
  · rw [WP.spec_ok]
    obtain ⟨y, hy, rfl⟩ := pp_ok σ
    rw [hPP] at hy
    exact ⟨σ, Or.inl ⟨rfl, hy⟩, J1.xtop, fun _ => ⟨⟨Ac1, Lst1, J1⟩, hRd⟩, hR, hV⟩
  step with obj.ks_set.spec as ⟨s2, e2⟩
  subst e2
  obtain ⟨Ac2, Lst2, J2⟩ := J1.workUnitsJD arI 0#u64
  refine WP.spec_bind (WP.spec_and (J2.timestampJD arI hAK hA hnd (hM.nowAgree hR hV)) (update_timestamp_mr hM hR _)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨σ1, hE1, hk1, hcs1, hrq1, hct1, har1, hum1, -, hK⟩, hR1⟩
  have hσ1m := the_result (Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))) hE1
  have hR1' : MR a1 σ1.machineState := by rw [hσ1m]; exact hR1
  have hV1 : ValidMachineTime σ1 := by rw [hσ1m]; exact validMachineTime_gct σ
  -- the time and the consumed time after the update
  obtain ⟨r0, -, ms0, hm0, hle0, -⟩ := spec_exists (hM.nowAgree hR hV)
  have hσ1 := the_result (updateTimeStamp_eq' hnd hm0) hE1
  have hct1' : σ1.curTime = r0.1.bv := by rw [hσ1]
  have hcn1 : σ1.consumedTime = σ.consumedTime + (r0.1.bv - σ.curTime) := by rw [hσ1]
  -- the arch relation after the time update
  have hX1 := (hK σ1.machineState a1 hum1 id).1
  have hAR1 : AR a1 σ.archState.x64CurrentCr3 := by
    have h := hX1.fin.1.1.2.2.2.2.2.2
    rw [show ({ σ1 with machineState := σ1.machineState } : Fl4Spec.State Unit).archState = σ.archState from har1] at h
    exact h
  -- the IRQ check on the spec side
  obtain ⟨⟨b2, a2⟩, hip, ⟨irq, ms, hIq, hiff, hum, hR2, hlm⟩, hAR2⟩ :=
    spec_exists (WP.spec_and (hM.irqAtE hR1') (hPA.irqAR a1 _ hAR1))
  have hum' : ms.underlyingMemory = σ.machineState.underlyingMemory := hum.trans hum1
  have hV2 : ValidMachineTime { σ1 with machineState := ms } := by
    show σ1.curTime ≤ ms.lastMachineTime ∧ Fl4Spec.unat ms.lastMachineTime ≤ timeCap
    rw [hlm]; exact hV1
  set σ2 : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσ2
  obtain ⟨hX2, -⟩ := hK ms a1 hum' id
  obtain ⟨hX2', hJ2'⟩ := hK ms a2 hum' (fun _ => hAR2)
  have hS2 := hX2.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS2.lists
  -- the current SC's owner
  have hOw2 : CurOwnW Z.T Z.C σ2 := by
    rcases J.own with ⟨u, hu, xt, hk, hxs, hb', hnr⟩ | ⟨⟨c', hc', hcv'⟩, h2⟩
    · refine Or.inl ⟨u, hu, xt, ?_, ?_, fun x n h => hb' x n ?_, fun _ => ?_⟩
      · show σ1.kheap u.bv = _; rw [hk1]; exact hk
      · show _ = some σ1.curSc; rw [hcs1]; exact hxs
      · rw [← hk1, ← hcs1]; exact h
      · show u.bv ∉ σ1.releaseQueue; rw [hrq1]
        by_cases h0 : σ.consumedTime = 0
        · exact (hRd.2 h0).2 u.bv xt hk hxs
        · exact hnr (bv_pos h0)
    · exact Or.inr ⟨⟨c', hc', hcv'.trans hcs1.symm⟩, fun x n h => h2 x n (by rw [← hk1, ← hcs1]; exact h)⟩
  -- FL4's IRQ read (first, in C's and the spec's order)
  refine WP.spec_bind (Pₘ := fun q => q = (b2, a2)) (by rw [hip, WP.spec_ok]) ?_
  rintro ⟨b2', a2'⟩ he
  cases he
  try dsimp only
  -- FL4's reads
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sched.consumed.spec' as ⟨cv, hcv⟩
  step with sporadic.sc_active.spec' as ⟨b, hb⟩
  rw [hc.cur] at hsc hcv
  subst hsc hcv
  have hscC : nodeW st s3 Z.c layout.node.CUR_SC ∈ Z.C := cursc_in hS2 hOw2
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hkx' : σ2.kheap σ2.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hab : b = Fl4Spec.scActive x := by
    rw [hb]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  subst hab
  obtain ⟨y, hy, rfl⟩ := pp_over hE1 hIq (readScActive_eq' hkx')
  rw [hPP] at hy
  have hexp : Fl4Spec.isCurDomainExpired σ2 = false := by
    unfold Fl4Spec.isCurDomainExpired; simp [hnd]
  rw [is_cur_domain_expired_eq]
  cases hact : Fl4Spec.scActive x
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, ite_self, WP.spec_ok]
    refine ⟨σ2, Or.inr ⟨by simp, ?_⟩, hX2', fun h => by simp at h, hR2, hV2⟩
    rw [if_pos (by simp [hact])] at hy
    exact hy
  simp only [↓reduceIte]
  refine WP.spec_bind (sufficient_refines s3 a2 σ2 hS2 hscC hkx hact _ (hPA.minBudget a2)) ?_
  intro ok1 hsuf
  have hrs : Fl4Spec.readScRefillSufficient (Z := Unit) σ2.curSc σ2.consumedTime σ2 = some ok1 := by
    rw [hs.curSc, hs.consumed]; unfold Fl4Spec.getScRefillSufficient at hsuf; exact getsThe_some hsuf
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  cases b2
  swap
  · rw [if_pos rfl, WP.spec_ok]
    rw [if_pos (Or.inl (hiff.1 rfl))] at hy
    exact ⟨σ2, Or.inr ⟨by simp, hy⟩, hX2', fun h => by simp at h, hR2, hV2⟩
  rw [if_neg (by simp)]
  have hirq : irq = none := by
    by_contra h; exact absurd (hiff.2 h) (by simp)
  cases hok : ok1
  · rw [if_neg (by simp), WP.spec_ok]
    refine ⟨σ2, Or.inr ⟨by simp, ?_⟩, hX2', fun h => by simp at h, hR2, hV2⟩
    rw [if_pos (by simp [hrs, hok])] at hy
    exact hy
  · rw [if_pos rfl, WP.spec_ok]
    rw [if_neg (by simp [hirq, hexp, hact, hrs, hok])] at hy
    have hx' := hx.strong hact
    have hne : x.scRefills ≠ [] := by rw [hx'.refills]; exact refills_ne hx'.wf
    have hr2 := getsThe_some (getScRefillSufficient_eq hkx' hne σ2.consumedTime)
    rw [hrs, hok] at hr2
    -- the current SC's head before the update, then after
    have hkσ : σ.kheap σ.curSc = some (.schedContext x n) := by
      rw [← hk1, ← hcs1]; exact hkx'
    have hrd : (Fl4Spec.refillHd x).rTime + σ.consumedTime ≤ σ.curTime ∧ (Fl4Spec.refillHd x).rTime ≤ σ.curTime := by
      by_cases h0 : σ.consumedTime = 0
      · have h := (hRd.2 h0).1 x n hkσ hact
        simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h
        rw [h0, bv_add0]; exact ⟨h, h⟩
      · obtain ⟨-, h1, h2⟩ := J.off (bv_pos h0) x n hkσ (fun _ => hact)
        simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h1 h2
        exact ⟨h1, h2⟩
    obtain ⟨hs1, hs2⟩ := rdy_shift hrd.1 hrd.2 hle0
    have e1 : σ2.consumedTime = σ.consumedTime + (r0.1.bv - σ.curTime) := hcn1
    have e2 : σ2.curTime = r0.1.bv := hct1'
    have hO2 : OffOK σ2 := by
      intro _ y m hy' _
      rw [hkx'] at hy'; cases hy'
      refine ⟨(Option.some.inj hr2).symm, ?_, ?_⟩
      · simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq]; rw [e1, e2]; exact hs1
      · simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0]; rw [e2]; exact hs2
    have hP2 : PPR0 σ2 := by
      refine ⟨by rw [hσ2, hσ1]; exact hRd.1, fun _ => ?_⟩
      refine ⟨fun y m hy' _ => ?_, fun u xt hu hus hur => ?_⟩
      · rw [hkx'] at hy'; cases hy'
        simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0]; rw [e2]; exact hs2
      · have hu' : σ.kheap u = some (.tcb xt) := by rw [← hk1]; exact hu
        have hus' : xt.tcbSchedContext = some σ.curSc := by rw [← hcs1]; exact hus
        have hur' : u ∉ σ.releaseQueue → False := fun h => h (by rw [← hrq1]; exact hur)
        by_cases h0 : σ.consumedTime = 0
        · exact hur' ((hRd.2 h0).2 u xt hu' hus')
        · obtain ⟨y', n', hy', hyt⟩ := J.inv.back u xt _ hu' hus'
          rcases J.own with ⟨u0, -, xt0, -, -, hb0, hnr0⟩ | ⟨-, hun⟩
          · have := hb0 y' n' hy'
            rw [hyt] at this; cases this
            exact hur' (hnr0 (bv_pos h0))
          · rw [hun y' n' hy'] at hyt; cases hyt
    refine ⟨σ2, Or.inl ⟨by simp, hy⟩, hX2', fun _ => ⟨hJ2' hO2 hOw2, hP2⟩, hR2, hV2⟩


set_option maxHeartbeats 16000000 in
/-- **XTopJointPPH's `ppJH` under `MachPlat`** (module docstring): every spec
`error` outcome is a `JHole` with `MR` and `ValidMachineTime`. -/
theorem JAtZ.ppJHM {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hPA : PPPlatA arI AR)
    (hR : MR a σ.machineState) (hV : ValidMachineTime σ) :
    sched.preemption_point st arI s a ⦃ r => r.1 = .Err .Preempted → ∀ σ',
      (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ∧
        MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
  unfold sched.preemption_point
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨w, _⟩
  step with obj.ks_set.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨Ac1, Lst1, J1⟩ := J.workUnitsJD arI w
  split
  swap
  · rw [WP.spec_ok]; intro h; cases h
  step with obj.ks_set.spec as ⟨s2, e2⟩
  subst e2
  obtain ⟨Ac2, Lst2, J2⟩ := J1.workUnitsJD arI 0#u64
  have hS0 := J2.xtop.fin.1.1.1
  have hscC0 := cursc_in hS0 J2.own
  refine WP.spec_bind (WP.spec_and (J2.timestampJH hAK hA hnd (hM.nowAgree hR hV)) (update_timestamp_mr hM hR _)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨σ1, hE1, hk1, hcs1, hrq1, hct1, har1, hum1, -, hK⟩, hR1⟩
  have hσ1m := the_result (Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))) hE1
  have hR1' : MR a1 σ1.machineState := by rw [hσ1m]; exact hR1
  have hV1 : ValidMachineTime σ1 := by rw [hσ1m]; exact validMachineTime_gct σ
  have hX1 := (hK σ1.machineState a1 hum1 id).xtop
  have hAR1 : AR a1 σ.archState.x64CurrentCr3 := by
    have h := hX1.fin.1.1.2.2.2.2.2.2
    rw [show ({ σ1 with machineState := σ1.machineState } : Fl4Spec.State Unit).archState = σ.archState from har1] at h
    exact h
  obtain ⟨⟨b2, a2⟩, hip, ⟨irq, ms, hIq, hiff, hum, hR2, hlm⟩, hAR2⟩ :=
    spec_exists (WP.spec_and (hM.irqAtE hR1') (hPA.irqAR a1 _ hAR1))
  have hum' : ms.underlyingMemory = σ.machineState.underlyingMemory := hum.trans hum1
  have hV2 : ValidMachineTime { σ1 with machineState := ms } := by
    show σ1.curTime ≤ ms.lastMachineTime ∧ Fl4Spec.unat ms.lastMachineTime ≤ timeCap
    rw [hlm]; exact hV1
  set σ2 : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσ2
  have hX2 := (hK ms a1 hum' id).xtop
  have hS2 := hX2.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS2.lists
  obtain ⟨Q0, R00, hc0, hs0⟩ := hS0.lists
  have hfin : ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 → σ' = σ2 :=
    fun σ' h => pp_err_eq hE1 hIq _ h rfl
  -- FL4's IRQ read (first, in C's and the spec's order)
  refine WP.spec_bind (Pₘ := fun q => q = (b2, a2)) (by rw [hip, WP.spec_ok]) ?_
  rintro ⟨b2', a2'⟩ he
  cases he
  try dsimp only
  -- FL4's reads
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sched.consumed.spec' as ⟨cv, hcv⟩
  step with sporadic.sc_active.spec' as ⟨b, hb⟩
  rw [hc.cur] at hsc hcv
  subst hsc hcv
  have hscC : nodeW st s3 Z.c layout.node.CUR_SC ∈ Z.C := by
    have e : (nodeW st s3 Z.c layout.node.CUR_SC).bv =
        (nodeW st (L.wr (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w)
          (core.num.U64.wrapping_add
            (L.ksb (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w))
            layout.ks.WORK_UNITS) 0#u64) Z.c layout.node.CUR_SC).bv := by
      rw [← hs.curSc, ← hs0.curSc]; exact hcs1
    rw [P1.eq_of_bv e]; exact hscC0
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hkx' : σ2.kheap σ2.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hab : b = Fl4Spec.scActive x := by
    rw [hb]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  subst hab
  rw [is_cur_domain_expired_eq]
  -- every preempted outcome ends at `(s3, a2)`, the spec's at `σ2`
  have hErr : (ok ((core.result.Result.Err error.Exc.Preempted : core.result.Result Unit error.Exc), s3, a2) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ r =>
      r.1 = .Err .Preempted → ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ∧
        MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
    rw [WP.spec_ok]
    intro _ σ' hσ'
    rw [hfin σ' hσ']
    exact ⟨_, Ac2, Lst2, hK _ a2 hum' (fun _ => hAR2), hR2, hV2⟩
  have hOk : (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ r =>
      r.1 = .Err .Preempted → ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ∧
        MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
    rw [WP.spec_ok]; intro h; cases h
  cases hact : Fl4Spec.scActive x
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, ite_self]
    exact hErr
  simp only [↓reduceIte]
  refine WP.spec_bind (sufficient_refines s3 a2 σ2 hS2 hscC hkx hact _ (hPA.minBudget a2)) ?_
  intro ok1 _
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  split
  · exact hErr
  split
  · exact hOk
  · exact hErr


set_option maxHeartbeats 16000000 in
/-- **XTopJointIrqZR's `afterInv_of_mcsJ` under `MachPlat`** (module
docstring). -/
theorem afterInv_of_mcsJM {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ⦄)
    (hM : MachPlat arI MR) (hIP : IrqPlatA arI AR) (hIrq : JIrqHypJ (L := L) arI AR) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, ⟨Z', H', Cs', Ac', Lst', D', J'⟩, hR1⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hM.takeAt hR1) (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum, -⟩, hAR2⟩, h126, h127⟩
  obtain ⟨Lst2, J2⟩ := J'.msArJ ms a2 hum (fun _ => hAR2)
  unfold syscall.check_interrupt
  by_cases hw : w = syscall.NO_IRQ
  · have hirq : irq = none := hnone.1 hw
    subst hirq
    have e : (w != syscall.NO_IRQ) = false := by simp [hw]
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨((), { σ' with machineState := ms }),
      hm _ (mem_maybeHandle_none hIq), ⟨Z', H', Cs', Ac', Lst2, D', J2⟩⟩⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, hmask⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    refine WP.spec_bind (hIrq s1 a2 _ w i ⟨Z', H', Cs', Ac', Lst2, D', J2⟩ hwi hmask h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inl (hmf (fail_maybeHandle_some hIq hf))⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ⟩⟩

end

end

end Fl4Proofs.P3
