/-
P3 (p3J gen 44, restated in gen 45): **the deletion loop's `MRV` lifts over the minimal platform record
`MachPlatC`**, so that P3JFinWJL's bundle with `MR` can be instantiated at the stable tops (which carry
`MachPlatF.toT hM hIp : MachPlatT`) as well as at the older tops (`MachPlat`).

XTopJointMRDel's lifts (`mrv_keep`, `FinObjHypWRcZ.mrv`, `post_mrv`, …, `jPreemptHypLM`) and the preemption
point they rest on (XTopJointMRPP's `JAtZ.ppJDM`, XTopJointMRHole2's `JAtZ.ppJDMV`, XTopJointMachRel's
`MachPlat.nowAgree`, `update_timestamp_mr`, `MachPlat.irqAtE`) take `MachPlat`, whose `mask` unmasks any line
`< 256` — too strong for the stable tops (IrqFixA / JBootIpi). Those proofs read only four things of the record:
`now`, `irqPending`, `frame` and **masking** (`mask_irq w true`, `w < 256`; used by `post_cap_deletion` of an
IRQ handler). Gen 45 states exactly that as
* **`MachPlatC`** (`now`, `irqPending`, `mask1`, `frame`), with projections **`MachPlat.toC`** and
  **`MachPlatT.toC`** (so `MachPlatF.toT hM hIp |>.toC` at the stable tops),

and proves each lemma once over it (gen 44's file was a script copy of the `MachPlat` proofs with `MachPlatT`
substituted; it is replaced by this single version):
* `MachPlatC.nowAgree`, `update_timestamp_mrC`, `MachPlatC.irqAtE`, **`JAtZ.ppJDMC`**, `JAtZ.ppJDMVC`;
* `mrv_keepC`, `ZombieHypWZ.mrvC`, `SwapHypWZ.mrvC`, `EmptyHypWR.mrvC`, `RdTrivHyp.mrvC`, `FinObjHypWRcZ.mrvC`,
  `post_mrvC`, `PostDelHypW.mrvC`, **`jPreemptHypLMC`**;
* **`delHypsJLMckC`** / **`delHypsJLMftC`**: P3JFinWJL's `delHypsJLMck` / `delHypsJLMft` over `MachPlatC` (the
  installs' deletion bundle at `WFt s0 (WMR MR (WCk WJL))`, `WFt s0 (WCk WJPM)` after a preemption, from the
  tops' globals: `ArchTotal`, `ARKeep`, `ARMask`, `PPPlatA`, `MachPlatC`, `MRKeepD`, `numDomains = 1`, `ticks`);
  **`delHypsJLMckT`** / **`delHypsJLMftT`** (gen 44's public names, preempted invariant `WJPM`): their
  corollaries at `MachPlatT` (`DelHypsWRZ.mapP`).
* (gen 45, for P3JPreSt) **`WJPV`**: `WJP` with `MRV` at its own `WJR` pre-state; `jPreemptHypLMC` and the `…C`
  bundles end a preemption at `WJPMV = WJPM ∧ WJPV`.

The originals (XTopJointMRDel / MRPP / MRHole2 / MachRel) are untouched; in the proof collapse they can be
re-stated over `MachPlatC` (their `MachPlat` users pass `hM.toC`).

No premise; no sorry. No existing statement changed.
-/
import Fl4Proofs.P3.P3JFinWJL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **The platform reads the deletion loop uses** [P] (module docstring): the part of `MachPlat` /
`MachPlatT` read by the preemption point (`now`, `irqPending`), by `post_cap_deletion` of an IRQ handler
(masking a line `< 256`) and by every `MR`-keeping step (`frame`). Not a premise of any top: it is
projected from `MachPlat` (`MachPlat.toC`; collapse A, Q: `MachPlatT` is `MachPlat`, its `MachPlatT.toC` is gone). -/
structure MachPlatC (MR : A → Fl4Spec.MachineState → Prop) : Prop where
  now : ∀ a ms, MR a ms → arI.now a ⦃ r => r.1.bv = gctVal ms ∧ MR r.2 (gctState ms) ⦄
  irqPending : ∀ a ms, MR a ms → arI.irq_pending a ⦃ r =>
    (r.1 = true ↔ gaiLine true ms ≠ none) ∧ MR r.2 (gaiState ms) ⦄
  /-- Masking (`m = true`) any line `< 256`. -/
  mask1 : ∀ a (w : U64) ms, MR a ms → w.val < 256 → arI.mask_irq a w true ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) true } ⦄
  frame : ∀ a ms ms', MR a ms → ms'.irqMasks = ms.irqMasks → ms'.irqState = ms.irqState →
    ms'.timeState = ms.timeState → ms'.lastMachineTime = ms.lastMachineTime → MR a ms'

/-- `MachPlat` gives `MachPlatC`. -/
theorem MachPlat.toC (h : MachPlat arI MR) : MachPlatC arI MR :=
  ⟨h.now, h.irqPending, fun a w ms hR hw => h.mask a w true ms hR hw, h.frame⟩

/-- **`NowAgree` at a related state** (module docstring): the platform's
clock read is the spec's at `σ`, and `σ.curTime ≤ r` from
`ValidMachineTime`. -/
theorem MachPlatC.nowAgree {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlatC arI MR) {a : A}
    {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) (hV : ValidMachineTime σ) : NowAgree arI a σ := by
  unfold NowAgree
  refine WP.spec_mono (hM.now a _ hR) ?_
  rintro r ⟨hv, -⟩
  refine ⟨gctState σ.machineState, ?_, ?_, rfl⟩
  · rw [hv]; exact doMachineOp_single (getCurrentTime_eq _)
  · rw [hv]; exact vmt_le_gct hV


/-- **`update_timestamp` moves `MR` by one clock read.** -/
theorem update_timestamp_mrC (hM : MachPlatC arI MR) {a : A} {ms : Fl4Spec.MachineState} (hR : MR a ms) (s : S) :
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
theorem MachPlatC.irqAtE (hM : MachPlatC arI MR) {a : A} {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) :
    arI.irq_pending a ⦃ r => ∃ irq ms,
      Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
      (r.1 = true ↔ irq ≠ none) ∧ ms.underlyingMemory = σ.machineState.underlyingMemory ∧ MR r.2 ms ∧
      ms.lastMachineTime = σ.machineState.lastMachineTime ⦄ := by
  refine WP.spec_mono (hM.irqPending a _ hR) ?_
  rintro r ⟨h1, h2⟩
  exact ⟨_, _, doMachineOp_single (getActiveIRQ_eq true _), h1, rfl, h2, rfl⟩


set_option maxHeartbeats 4000000 in
/-- **XTopJointPP's `ppJD` under `MachPlatC`** (module docstring), with `MR`
and `ValidMachineTime` at every outcome. -/
theorem JAtZ.ppJDMC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hPA : PPPlatA arI AR)
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
  refine WP.spec_bind (WP.spec_and (J2.timestampJD arI hAK hA hnd (hM.nowAgree hR hV)) (update_timestamp_mrC hM hR _)) ?_
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

set_option maxHeartbeats 4000000 in
/-- **The preemption point at a `JAtZ` state carrying `MR`, `ValidMachineTime`
and `ValidIrqMasks`** (module docstring): continuing with the invariant
again, or preempted at a `JAtPreMV` state. -/
theorem JAtZ.ppJDMVC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hPA : PPPlatA arI AR)
    (hR : MR a σ.machineState) (hV : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hns : Vs.NoSwitch σ)
    (hRd : PPR0 σ) :
    ∃ r, sched.preemption_point st arI s a = ok r ∧ ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          (∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.2.1 r.2.2 σ') ∧
          PPR0 σ' ∧ Vs.NoSwitch σ') ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          JAtPreMV (L := L) arI AR MR r.2.1 r.2.2 σ')) ∧
      XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧
      MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ∧ ValidIrqMasks σ' := by
  obtain ⟨⟨r1, s', a'⟩, hr, σ', hcase, hX', hJ', hR', hV'⟩ := spec_exists (J.ppJDMC hAK hA hnd hM hPA hR hV hRd)
  refine ⟨(r1, s', a'), hr, σ', ?_, hX', hR', hV', ?_⟩
  · rcases hcase with ⟨rfl, hm0⟩ | ⟨rfl, hm⟩
    · obtain ⟨hJ0, hp'⟩ := hJ' rfl
      exact Or.inl ⟨rfl, hm0, hJ0, hp', Vs.ake_preemptionPoint'.noSwitch hm0 hns⟩
    · exact Or.inr ⟨rfl, hm, s, a, σ, ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hns, hRd, hR, hV, hVI⟩, hr, hm⟩
  · rcases hcase with ⟨-, hm0⟩ | ⟨-, hm⟩
    · exact vim_pp hm0 hVI
    · exact vim_pp hm hVI

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {th : TypedHeap}

/-- (p3J gen 45) **The deletion's state after a preemption with `MRV` at the `WJP` pre-state** [definition]:
`WJP`'s pre-state (a `WJR` state, so a `JAtZ (Z.mv G V) H Cs` state) carries `MRV` itself. (`WJPM`'s `JAtPreMV`
states `MRV` at an existential `JAt` pre-state, which loses the sets; P3JPreSt's `midXP_of_pre` needs the
timestamp's `NowAgree` at the `JAtZ` pre-state.) -/
def WJPV (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit), (WJR (L := L) arI AR Z H Cs kb s0 a0 σ0 G ∧ MRV MR a0 σ0) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1 ∧
    DomRel (L.mem s) (L.ksb s) σ ∧ MdbOKV (L.ksb s) (L.mem s) G

/-- (p3J gen 45) `WJPM ∧ WJPV`: the preempted invariant `jPreemptHypLMC` produces. -/
abbrev WJPMV (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  WJPM (L := L) arI AR MR Z H Cs kb s a σ G ∧ WJPV (L := L) arI AR MR Z H Cs kb s a σ G

/-- (p3J gen 45) **`DelHypsWRZ` along a map of the preempted invariant** (it occurs only in the preemption
point's post). -/
theorem DelHypsWRZ.mapP {W Wx Wp Wp' : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop}
    (h : DelHypsWRZ (L := L) arI W Wx Wp Rd Rz th) (g : ∀ s a σ G, Wp s a σ G → Wp' s a σ G) :
    DelHypsWRZ (L := L) arI W Wx Wp' Rd Rz th :=
  ⟨h.fin, h.triv, fun s a σ G hDS hW => WP.spec_mono (h.pp s a σ G hDS hW)
    fun _ ⟨h1, σ', h2, h3, h4⟩ => ⟨h1, σ', h2, h3, h4.map id (g _ _ _ _)⟩,
    h.post, h.zomb, h.swap, h.empty, h.wx⟩

/-- **A spec step keeping `msFT` keeps `MRV`.** -/
theorem mrv_keepC {arI : machine.Arch A} (hM : MachPlatC arI MR) {a : A} {σ σ' : Fl4Spec.State Unit}
    (h : MRV MR a σ) (e : MachT.msFT σ' = MachT.msFT σ) : MRV MR a σ' := by
  unfold MRV ValidMachineTime ValidIrqMasks at *
  obtain ⟨hR, ⟨hV1, hV2⟩, hI⟩ := h
  simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e
  obtain ⟨⟨e1, e2, e3, e4, e5⟩, e6⟩ := e
  refine ⟨hM.frame a _ _ hR e1 e2 e3 e4, ⟨?_, ?_⟩, fun i hi => ?_⟩
  · rw [e6, e4]; exact hV1
  · rw [e4]; exact hV2
  · rw [e1]; exact hI i (by rw [← e5]; exact hi)

variable {W Wx : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
  {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop}

theorem ZombieHypWZ.mrvC {arI : machine.Arch A} (hM : MachPlatC arI MR) (h : ZombieHypWZ (L := L) (A := A) W Rz th) :
    ZombieHypWZ (L := L) (A := A) (WMR MR W) Rz th := by
  intro s s' a σ σ' G sl p zt n hW hRz hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS
  exact ⟨h s s' a σ σ' G sl p zt n hW.1 hRz hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS,
    mrv_keepC hM hW.2 (MachT.mtk_setCap _ _ σ ((), σ') (mem_of_single hsc))⟩

theorem SwapHypWZ.mrvC {arI : machine.Arch A} (hM : MachPlatC arI MR) (h : SwapHypWZ (L := L) (A := A) W th) :
    SwapHypWZ (L := L) (A := A) (WMR MR W) th := by
  intro s s' a σ σ' G G' sl p zt n hW hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS
  exact ⟨h s s' a σ σ' G G' sl p zt n hW.1 hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS,
    mrv_keepC hM hW.2 (MachT.mtk_capSwapForDelete' _ _ σ ((), σ') (mem_of_single hsw))⟩

theorem EmptyHypWR.mrvC {arI : machine.Arch A} (hM : MachPlatC arI MR) (h : EmptyHypWR (L := L) W Wx Rd th) :
    EmptyHypWR (L := L) (WMR MR W) (WMR MR Wx) Rd th := by
  intro s s' a σ σ' G G' sl hW hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS
  exact ⟨h s s' a σ σ' G G' sl hW.1 hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS,
    mrv_keepC hM hW.2 (MachT.mtk_emptySlotNull _ σ ((), σ') hes)⟩

theorem RdTrivHyp.mrvC (h : RdTrivHyp (L := L) W Rd th) : RdTrivHyp (L := L) (WMR MR W) Rd th :=
  fun s a σ G sl c hDS hW => h s a σ G sl c hDS hW.1

theorem FinObjHypWRcZ.mrvC (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) (hT : P0.ArchTotal arI)
    (h : FinObjHypWRcZ (L := L) arI W Wx Rd Rz th) : FinObjHypWRcZ (L := L) arI (WMR MR W) (WMR MR Wx) Rd Rz th := by
  intro s a σ G sl c hDS hW hA hc hk ht
  refine WP.spec_mono (WP.spec_and (h s a σ G sl c hDS hW.1 hA hc hk ht)
    (MKD.objects_finalise_cap L.total hT hKD hW.2.1)) ?_
  rintro r ⟨⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10, h11⟩, hR⟩
  have hmv := mrv_keepC hM ⟨hR, hW.2.2⟩ (MachT.mtk_finaliseCap _ _ σ _ h4)
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8,
    ⟨fun hn => ⟨h9.1 hn, hmv⟩, fun hr => ⟨h9.2 hr, hmv⟩⟩, h10, h11⟩

/-- **A cleanup cap's `post_cap_deletion` keeps `MRV`** (module docstring). -/
theorem post_mrvC (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {cl : capability.Cap} (h : MRV MR a σ) (hcl : CleanCap cl) (hn : cl ≠ .Null) (hw : CapWf cl) :
    objects.post_cap_deletion st arI s a cl ⦃ r => ∀ σ',
      ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap cl) σ).1 → MRV MR r.2 σ' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hn
  · rename_i irq
    have hirq : irq.val < 128 := hw
    have hd : decide (interrupt.IRQ_INACTIVE = interrupt.IRQ_INACTIVE) = true := by simp
    obtain ⟨a1, hm1, hR1⟩ := spec_exists (hM.mask1 a irq σ.machineState h.1 (by omega))
    have hm : arI.mask_irq a irq (decide (interrupt.IRQ_INACTIVE = interrupt.IRQ_INACTIVE)) = ok a1 := by
      rw [hd]; exact hm1
    obtain ⟨a2, hf, hR2⟩ := spec_exists (hKD.irq_free a1 irq _ hR1)
    unfold objects.post_cap_deletion
    simp only
    rw [deleted_irq_handler_eq arI s a irq hm hf, WP.spec_ok]
    intro σ' hσ'
    have e : σ' = setIrqSt .irqInactive (BitVec.ofNat 8 irq.val) σ :=
      setIrqInactive_out (irq := BitVec.ofNat 8 irq.val) (x := ((), σ')) hσ'
    subst e
    have e8 : BitVec.ofNat 8 irq.val = irq.bv.setWidth 8 := BitVec.ofNat_toNat 8 irq.bv
    unfold MRV at h ⊢
    obtain ⟨hR, hV, hI⟩ := h
    refine ⟨hM.frame a2 _ _ hR2 ?_ rfl rfl rfl, hV, ?_⟩
    · show Function.update σ.machineState.irqMasks (BitVec.ofNat 8 irq.val)
          (decide (Fl4Spec.IrqState.irqInactive = .irqInactive)) =
        Function.update σ.machineState.irqMasks (irq.bv.setWidth 8) true
      rw [e8]; simp
    · unfold ValidIrqMasks at hI ⊢
      intro i hi
      show Function.update σ.machineState.irqMasks (BitVec.ofNat 8 irq.val)
          (decide (Fl4Spec.IrqState.irqInactive = .irqInactive)) i = true
      have hi' : Function.update σ.interruptStates (BitVec.ofNat 8 irq.val) Fl4Spec.IrqState.irqInactive i =
          .irqInactive := hi
      by_cases ei : i = BitVec.ofNat 8 irq.val
      · subst ei; simp
      · rw [Function.update_of_ne ei] at hi' ⊢
        exact hI i hi'
  · rename_i f l o
    unfold objects.post_cap_deletion
    simp only
    refine WP.spec_bind (P0.ioport.free_ioports.p0 st s f l hS) fun s1 _ => ?_
    rw [WP.spec_ok]
    intro σ' hσ'
    exact mrv_keepC hM h (MachT.mtk_archPostCapDeletion'
      (.ioPortCap (BitVec.ofNat 16 f.val) (BitVec.ofNat 16 l.val)) σ _ hσ')

theorem PostDelHypW.mrvC (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) (h : PostDelHypW (L := L) arI W th) :
    PostDelHypW (L := L) arI (WMR MR W) th := by
  intro s a σ G cl hDS hW h1 h2 h3
  refine WP.spec_mono (WP.spec_and (h s a σ G cl hDS hW.1 h1 h2 h3) (post_mrvC arI hM hKD hW.2 h1 h2 h3)) ?_
  rintro r ⟨⟨hSS, σ', hm, hCR, hW'⟩, hmv⟩
  exact ⟨hSS, σ', hm, hCR, hW', hmv σ' hm⟩

set_option maxHeartbeats 4000000 in
/-- **The preemption point keeps `WMR MR WJL`** (module docstring). -/
theorem jPreemptHypLMC (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlatC arI MR) (hPA : PPPlatA arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPMV (L := L) arI AR MR Z H Cs kb) th := by
  intro s a σ G hDS ⟨⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩, hR, hV, hVI⟩
  subst hth
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb (fun p hp => J.jcov.dx p (J.zD p hp))
  obtain ⟨r0, hr0, hP0⟩ := J0.ppJDMVC hAK hA hnd hM hPA hR hV hVI hns hp0
  have hPS : sched.preemption_point st arI s a ⦃ r => ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          (∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac' Lst'
            (D ∪ ZTcb (L := L) Z.th s) r.2.1 r.2.2 σ') ∧ PPR0 σ' ∧ Vs.NoSwitch σ') ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          JAtPreMV (L := L) arI AR MR r.2.1 r.2.2 σ')) ∧
      XTopAt (L := L) AR (Z.mv G V) r.2.1 r.2.2 σ' ∧
      MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ∧ ValidIrqMasks σ' ⦄ := by
    rw [hr0, WP.spec_ok]; exact hP0
  obtain ⟨⟨r1, s', a'⟩, hr, ⟨⟨σ', hcase2, hX', hR', hV', hVI'⟩, -, hw⟩, hK⟩ :=
    spec_exists (WP.spec_and (WP.spec_and hPS
      (P1.sched.preemption_point.pp hA s a J.blk)) (J.ppDbg hA))
  have hcase : ((r1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
      (r1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) :=
    hcase2.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
  rw [hr, WP.spec_ok]
  simp only at hcase hcase2 hX' hw hK hR' hV' hVI' ⊢
  have hX := J.xtop
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hN' : P1.NodePlaced st (Z.mv G V).T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ (hc.cur ▸ J.kern.cpuCs)
  have hSS : SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') := hX.slotsSame_of hw fun b hb => by
    have hf := J.kern.ksbFit
    rcases hb with rfl | rfl | rfl
    · have := workUnits_val hf; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e := P1.nodeAt_val hN' (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
    · have e := P1.nodeAt_val hN' (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
  have hks : L.ksb s' = L.ksb s := hw.1
  refine ⟨hSS, σ', hcase, hX'.rel.2.1, ?_⟩
  rcases hcase2 with ⟨rfl, hm0, ⟨Ac', Lst', J'⟩, hp', -⟩ | ⟨rfl, hm, hPre⟩
  · have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
    have horig : σ'.isOriginalCap = σ.isOriginalCap :=
      orig_eq_of_slots hDS.1.2.2.2.1 hX'.rel.2.1.2.2.2.1 J.kern.orig J'.kern.orig hSS
    have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
      ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
    have hL' : LiveJ (L := L) Z.th H G s' σ' :=
      hL.of_sameZ hSS hmem horig (congrArg Prod.snd (Vs.gke_preemptionPoint' σ _ hm0)) hK J.kern.cs0 hTz fun p hp => J'.jcov.dead p (Or.inr hp)
    exact ⟨⟨⟨V, Ac', Lst', _, J', by rw [hks]; exact hkb, Vs.ake_preemptionPoint'.noSwitch hm0 hns,
      SpecGlob.pp hm0 hsg, hp'⟩, hL', ⟨lst, J.dbgWF_keep J' rfl rfl hDW hK⟩,
      hN.of_same (fun y hy => hSS.capV hy) horig⟩, hR', hV', hVI'⟩
  · exact ⟨⟨⟨s, a, σ, ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hr, hm, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, hPre⟩,
      s, a, σ, ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hR, hV, hVI⟩, hr, hm, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩

/-- (p3J gen 45) **P3JFinWJL's `delHypsJLMck` over `MachPlatC`** (module docstring). -/
theorem delHypsJLMckC [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb)))
      (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb)))
      (WCk (WJPMV (L := L) arI AR MR Z H Cs kb)) (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  have hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := fun a i m => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a i m); exact ⟨a', h⟩
  have hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := fun a i => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a i); exact ⟨a', h⟩
  exact ⟨(finJLZck arI hT hK hticks Z H Cs kb hth).mrvC arI hM hKD hT, (rdTrivJLX arI Z H Cs kb hth).ck.mrvC,
    (jPreemptHypLMC arI hK hT hnd hM hPA Z H Cs kb hth).ckMap arI (fun _ _ _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)
      (fun _ _ _ _ h c => ⟨⟨h.1, c⟩, h.2⟩) (fun _ _ _ _ h c => ⟨h, c⟩),
    ((jPostDelHypL arI hAM hmask hfree Z H Cs kb hth).ck arI).mrvC arI hM hKD,
    (jZombieHypL arI Z H Cs kb hth).ck.mrvC hM, (jSwapHypL arI Z H Cs kb hth).ck.mrvC hM,
    (emptyHypJL arI Z H Cs kb hth).ck.mrvC hM, fun _ _ _ _ h => ⟨⟨h.1.1.x arI, h.1.2⟩, h.2⟩⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **P3JFinWJL's `delHypsJLMft` over `MachPlatC`**: the installs' deletion bundle with the `ProjW`
footprint from `s0` (module docstring). -/
theorem delHypsJLMftC [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) (s0 : S) :
    DelHypsWRZ (L := L) arI (WFt (L := L) H Cs s0 (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb))))
      (WFt (L := L) H Cs s0 (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb))))
      (WFt (L := L) H Cs s0 (WCk (WJPMV (L := L) arI AR MR Z H Cs kb)))
      (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th := by
  subst hth
  refine (delHypsJLMckC arI hT hK hticks hnd hM hKD hPA hAM Z H Cs kb rfl).foot arI s0 ?_ ?_ ?_ ?_
  · intro s a σ G sl c hDS hW hAs hc _
    exact hfinWJL hT Z H Cs kb hDS hW.1 hAs hc _ false
  · intro s a σ G _ hW
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1.1.1
    exact J.ppProjW hT
  · intro s a σ G cl _ hW _ _ hwf
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1.1.1
    exact J.postCapDelWf hT hwf
  · intro s a σ G hW b hb
    obtain ⟨E, ⟨V, Ac, Lst, D, J, -⟩, -⟩ := hW.1.1
    exact J.slotWdProjW hb


/-- (p3J gen 44 name) **`delHypsJLMckC` at the stable tops' `MachPlatT`**. -/
theorem delHypsJLMckT [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb)))
      (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb)))
      (WCk (WJPM (L := L) arI AR MR Z H Cs kb)) (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th :=
  (delHypsJLMckC arI hT hK hticks hnd hM.toC hKD hPA hAM Z H Cs kb hth).mapP arI fun _ _ _ _ h => ⟨h.1.1, h.2⟩

/-- (p3J gen 44 name) **`delHypsJLMftC` at the stable tops' `MachPlatT`**. -/
theorem delHypsJLMftT [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) (s0 : S) :
    DelHypsWRZ (L := L) arI (WFt (L := L) H Cs s0 (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb))))
      (WFt (L := L) H Cs s0 (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb))))
      (WFt (L := L) H Cs s0 (WCk (WJPM (L := L) arI AR MR Z H Cs kb)))
      (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th :=
  (delHypsJLMftC arI hT hK hticks hnd hM.toC hKD hPA hAM Z H Cs kb hth s0).mapP arI
    fun _ _ _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩

end

end

end Fl4Proofs.P3
