/-
P3 (p3J gen 45): **the deletion loop's preempted state at stable ghosts, part 2: the preempted outcome `MidXP`**
(item 3 of gen 44's plan), with the IRQ handler's signal line closed.

From a preempting `preemption_point` at a `JAtZ (Z.mv G V) H Cs` pre-state (round-robin `RR`, `CKI`,
`NativeScope`, `MRV`), FL4's `after_invocation (Err Preempted)` (= `mcs_preemption_point` and `check_interrupt`)
ends at an outcome of the spec's `preemptionPath` with `JStab Z H Cs`, `MR`, and writes only `ProjW H Cs`:

* **`syscall.mcs_preemption_point.rrN`** (P2 level): on a round-robin current SC (period word `0`), with P1's
  scheduler invariants, the current SC word linked to the current thread's (`hcsc`) and the action not the current
  thread (`hna`), FL4's `mcs_preemption_point` is a `FootN ∅ False` step: P1 QueueBudgetG's
  `mcs_preemption_point.allG` walk with P2 EntryIrq's round-robin `check_budget.rr` / `charge_budget.rr` (no timeout
  fault) and `footN_node` for the inactive-SC branch's `CONSUMED` write.
* **`JHole.mcsFt`**: at a hole (P3JPreHole) with `CtOK` (the current thread's SC word), `NoSwitch` and `RR`, the
  MCS preemption point writes only `ProjW H Cs s` (P3JMcKwN's `cur0wN_projW`).
* **`Mc.JAtZ.handleIrqFt`**: at a `JAtZ` state whose spec state is `CKI`, FL4's `handle_interrupt` of **any** line
  writes only `ProjW H Cs s`. Off the signal lines P3JMcIrqH's `handle_interrupt_footN0`; on a signal line the
  handler slot's cap is typed (`JPlaced.irq`: a notification cap names an `H` notification) and the signal is
  P3JMidNtfn's `sendSignalProjW` (`NoBufCap` from `CKI`, P3JMcFlt's `noBufCap_cki`). This closes the signal-line
  gap of P3JMcIrqF's `IrqSigFootJ` at `CKI` states (`irqSigFootJ_of_cki`).
* **`JHole.afterInvSt`**: `after_invocation (Err _)` from a round-robin hole: P3JPreHole's `JHole.mcsSt`, then the
  IRQ take (`MachPlatT.takeAt`, `IrqPlatK.takeAR`, `MachPlatT.noIpi`) and the stable handler (IrqFixGen's
  transported `JAtZ.handleIrqJIMSt`; collapse A, Q: formerly its `Fl4ProofsQ` copy at `MachPlatT` / `IrqPlatK`), the footprints composed.
* **`midXP_of_pre`**: P3JMidInv's `MidXP Z H Cs MR s0` at the preempted state, from the pre-state facts
  (`JAtZ (Z.mv G V) H Cs`, `NoSwitch`, `PPR0`, `MRV`), `CKI` / `RR` / `NativeScope` at the preempted spec state
  and the footprint `s0 → preempted state`; **`midXP_of_wjpv`**: the same from P3JDelMT's preempted invariant
  `WFt s0 (WCk WJPMV)` (the installs' deletion bundle `delHypsJLMftC`) with `RR` and `NativeScope`.

Platform facts used (all [P], the stable tops' globals except `IrqPlatK`, which the stable interrupt top
`kernel_entry_runMcWKR_irqJ` already takes): `ARIface`, `ArchTotal`, `numDomains = 1`, `MachPlatT`, `MRKeepD`,
`IrqPlatK`, `TimeAgree` (`max_release_time`), `PPPlatA` (`irq_pending` keeps `AR`, `min_budget`).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JPreHole
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- (p3J gen 45) **`mcs_preemption_point` on a round-robin current SC is a `FootN ∅ False` step** (module
docstring). -/
theorem syscall.mcs_preemption_point.rrN (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hrr : L.rperiod s (L.cscW s) = 0#u64) :
    syscall.mcs_preemption_point st ar s a ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have ect : ct = L.curW s := ct_post
  subst ect
  step with sched.is_schedulable.spec' as ⟨b, eb⟩
  split
  · rename_i hb
    obtain ⟨-, hbd, -, hrm⟩ := eb hb
    have hcA : L.cscW s ∈ Ac := by
      have e : L.mem s (scA (L.curW s)) = L.cscW s := (hcsc hbd).symm
      rw [← e]; exact (hS.act _ (hX.2.2.bound _ h.curT hbd).1).2 hrm
    refine WP.spec_bind (sched.check_budget.rr (Kp := ∅) (Nd := False) (Es := (∅ : Set U64)) hA s a Q R h hB hX hSg
      hS hcsc hna hcA (fun _ h => h) (fun _ _ _ => ⟨hrr, fun h => h⟩)) ?_
    rintro ⟨r, s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    refine (WP.spec_ok _).2 ?_
    try simp only [WP.uncurry'_pair]
    exact h1.2.1
  · step with sched.cur_sc.spec as ⟨c, ec⟩
    step with sporadic.sc_active.val as ⟨b1, eb1⟩
    split
    · rename_i hb1
      have hcA : L.cscW s ∈ Ac := (hS.act _ hX.2.2.cur).2 (by
        have := eb1 hb1; rwa [ec] at this)
      step with sched.consumed.spec as ⟨u⟩
      refine WP.spec_mono (sched.charge_budget.rr (Kp := ∅) (Nd := False) (Es := (∅ : Set U64)) hA s a u false Q R h
        hB hX hSg hS hcsc hna hcA (fun h => h) (fun _ h => h) hrr) ?_
      rintro ⟨s1, a1⟩ h1
      try simp only [WP.uncurry'_pair] at h1 ⊢
      exact h1.2.1
    · step with LawfulStore.cur_cpu_spec as ⟨cpu, cpu_post⟩
      subst cpu_post
      step with obj.node_set.spec as ⟨s2, e2⟩
      subst e2
      try simp only [WP.uncurry'_pair]
      exact footN_node h.nodes h.cur (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
        (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [IdOff, layout.node.CONSUMED])
        h.cur

end

end Fl4Proofs.P2.Stall

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **The MCS preemption point at a round-robin hole writes only `ProjW`** (module docstring). -/
theorem JHole.mcsFt {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hct : CtOK σ) (hns : Vs.NoSwitch σ) (hRR : SInvRr.RR σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have J := Hh.j0
  have hS := Hh.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hscC := Hh.curSc_in
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hct' : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb _ hct'
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hcsc1 : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)) := fun h0 => by
    rw [ecur] at h0 ⊢; rw [ecsc]
    have hl := (hct xt (by rw [hs.curThread]; exact hkt)).1
    rw [hsct, Notif.optRef_ne h0] at hl
    rcases hl with hl | hl
    · exact P1.eq_of_bv (hpc.trans (Option.some.inj hl).symm)
    · cases hl
  have hna : L.actionW s ≠ L.curW s := by
    rw [ecur]; exact actionW_ne_of hS hct' (hns _)
  have hx0 : x.scPeriod = 0 := SInvRr.rr_period hRR hk
  have hrr : L.rperiod s (L.cscW s) = 0#u64 := by
    rw [ecsc]; exact P1.eq_of_bv (by rw [← hx.period, hx0]; rfl)
  refine WP.spec_mono (P2.Stall.syscall.mcs_preemption_point.rrN hAT s a Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc1 hna hrr) ?_
  rintro ⟨s', a'⟩ hr
  try simp only [WP.uncurry'_pair] at hr
  exact (P1.WritesA.w hr).mono fun _ hb => Mc.cur0wN_projW J.kern.heap h1.nodes (Or.inl hb)

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **At a `CKI` `JAtZ` state, the handler of any line writes only `ProjW`** (module docstring). -/
theorem JAtZ.handleIrqFt (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : SInvCk.CKI σ) (w : U64) :
    interrupt.handle_interrupt st arI s a w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  by_cases hsig : w.val ≤ 127 ∧ L.mem s (irqStA (L.ksb s) w) = 1#u64
  swap
  · have hb := BlkOK.bxi J.blk
    exact WP.spec_mono (handle_interrupt_footN0 (Es := EH H) hA s a w hb fun hle e => hsig ⟨hle, e⟩) fun r hr =>
      projW_of_cur0wN J ((WritesA.w hr).mono fun _ hb => Or.inl hb)
  obtain ⟨hle, hst⟩ := hsig
  have hi : w.val < 128 := by omega
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hty := hJ.irq w hi
  unfold interrupt.handle_interrupt
  step with layout.irq.MAX.spec as ⟨mx, emx⟩
  have hmx : mx.val = 127 := by rw [emx]; simp
  split
  · rename_i hgt
    exfalso
    simp at hgt
    omega
  rw [irq_state_eq']
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s)) ?_ ?_
  · rw [if_pos (hst.trans irqSig_eq.symm)]
    rw [irq_slot_eq]
    simp only [bind_ok]
    rw [slot_cap_eq, capAt_capV]
    simp only [bind_ok]
    refine WP.spec_bind (Pₘ := fun r : S × A => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s)) ?_ ?_
    · generalize hcv : capV (L.mem s) (nodeA (L.ksb s) w) = c at hty
      cases c
      case Notification p b wr rr =>
        cases wr
        · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
        · simp only [↓reduceIte]
          exact sendSignalProjW hA J.kern.heap J.blk (noBufCap_cki J hC) (hty.2.1 p b true rr rfl).2 b
      all_goals exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
    · rintro ⟨s3, a2⟩ h3
      try simp only [WP.uncurry'_pair] at h3
      try dsimp only
      refine WP.spec_bind (hA.mask_irq a2 w true) fun a3 _ => ?_
      exact (WP.spec_ok _).2 h3
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair] at h1
    try dsimp only
    refine WP.spec_bind (hA.ack_irq a1 w) fun a2 _ => ?_
    exact (WP.spec_ok _).2 h1

/-- (p3J gen 45) **P3JMcIrqF's `IrqSigFootJ` [J] holds at every `CKI` state** (`handleIrqFt`; the premise's
antecedents include `CKI σ`). -/
theorem irqSigFootJ_of (hA : P0.ArchTotal arI) : IrqSigFootJ (st := st) (L := L) arI AR :=
  fun _ _ _ _ _ _ _ _ _ J _ hC w _ _ => Fl4Proofs.P3.Mc.JAtZ.handleIrqFt hA J hC w

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **`after_invocation (Err _)` from a round-robin hole at the hole's sets, with footprint**
(module docstring). -/
theorem JHole.afterInvSt [VxE Z] {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ)
    (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR) (hTA : TimeAgree arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hni : σ.curThread ≠ σ.idleThread) (hns : Vs.NoSwitch σ) (hf : CurScFree σ) (hct : CtOK σ) (hg : Chg σ)
    (hRR : SInvRr.RR σ) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) (hN : NativeScope σ)
    (hC : SInvCk.CKI σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧
      (∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1,
        JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 z.2 ∧ MR r.2.2 z.2.machineState) ∧
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind (WP.spec_and (Hh.mcsSt hT hAT hnd (hTA.mrt a) (hmb a) hni hns hf hct hg hRR hM.toC hKD.toK hR hV)
    (Hh.mcsFt hAT hct hns hRR)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ', hm, -, ⟨G1, V1, Ac1, Lst1, D1, J'⟩, hR1, hVI, hN', hC'⟩, hW1⟩
  have hN1 : NativeScope σ' := hN' hN
  have hC1 : SInvCk.CKI σ' := hC' hC
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hM.takeAt hR1) (hIP.takeAR a1 _ hAR1)) (hM.noIpi a1 _ hR1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum, hR2⟩, hAR2⟩, h126, h127⟩
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
    exact (WP.spec_ok _).2 ⟨rfl, ⟨((), { σ' with machineState := ms }), hm _ (mem_maybeHandle_none hIq),
      JStab.mv J2.stab, hR2⟩, hW1⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, -⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    have hw256 : w.val < 256 := by rw [hwi]; exact i.isLt
    refine WP.spec_bind (WP.spec_and (Fl4Proofs.P3.JAtZ.handleIrqJIMSt hARI hAT hIP hM hKD.toK hmb J2 hN1 hR2 w i hwi
      hw256 h126 h127) (Mc.JAtZ.handleIrqFt hAT J2 hC1 w)) ?_
    rintro ⟨s2, a3⟩ ⟨hf | ⟨z, hz, hJ, hRz⟩, hW2⟩
    · exact absurd hf (gai_active hVI hIq i rfl)
    · exact (WP.spec_ok _).2 ⟨rfl, ⟨z, hm _ (mem_maybeHandle_some hIq hz), JStab.mv hJ, hRz⟩,
        hW1.projW_trans hW2⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **P3JMidInv's `MidXP` at a preempted deletion step** (module docstring): the pre-state is a
`JAtZ (Z.mv G V) H Cs` state with `NoSwitch`, `PPR0` and `MRV`, its preemption point preempts, the preempted spec
state is `CKI`, `RR` and `NativeScope`, and the run from `s0` to the preempted state writes only `ProjW H Cs s0`. -/
theorem midXP_of_pre [VxE Z] (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR) (hTA : TimeAgree arI)
    (hPA : PPPlatA arI AR) {s0 s' s : S} {a' a : A} {σ' σ : Fl4Spec.State Unit} {G : MdbGhost} {V : XVs}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s' a' σ') (hns : Vs.NoSwitch σ') (hp : PPR0 σ')
    (hMV : MRV MR a' σ')
    (hpp : sched.preemption_point st arI s' a' = ok (.Err .Preempted, s, a))
    (hσ : (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ').1)
    (hC : SInvCk.CKI σ) (hRR : SInvRr.RR σ) (hN : NativeScope σ)
    (hW : P1.WritesIn st s0 s (Mc.ProjW (L := L) H Cs s0)) :
    MidXP (L := L) arI AR MR Z H Cs s0 s a σ := by
  obtain ⟨hR0, hV0, hI0⟩ := hMV
  obtain ⟨s1, Ac1, Lst1, Hh, hTs, hni, hns', hf, hct, hg, -, hR, -, hVI⟩ :=
    J.preHoleC hARI.toARKeep hAT hnd hM.toC hPA hns hp hR0 hV0 hI0 hpp hσ
  refine ⟨hW, WP.spec_mono (Hh.afterInvSt hTs hARI hAT hnd hM hKD hIP hTA hPA.minBudget hni hns' hf hct hg hRR hR
    hVI hN hC _) ?_⟩
  rintro r ⟨h1, ⟨z, hz, hJ, hRz⟩, hW2⟩
  exact ⟨h1, ⟨z, hz, JStab.mv hJ, hRz⟩, hW.projW_trans hW2⟩

/-- (p3J gen 45) **`MidXP` at the installs' preempted invariant** (P3JDelMT's `delHypsJLMftC` ends a preemption at
`WFt s0 (WCk WJPMV)`): with `RR` and `NativeScope` at the preempted spec state. -/
theorem midXP_of_wjpv [VxE Z] (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR) (hTA : TimeAgree arI)
    (hPA : PPPlatA arI AR) {kb : U64} {s0 s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WFt (L := L) H Cs s0 (WCk (WJPMV (L := L) arI AR MR Z H Cs kb)) s a σ G)
    (hRR : SInvRr.RR σ) (hN : NativeScope σ) :
    MidXP (L := L) arI AR MR Z H Cs s0 s a σ := by
  obtain ⟨⟨⟨-, s', a', σ', ⟨⟨V, Ac', Lst', D', J, -, hns, -, hp⟩, hMV⟩, hpp, hσ, -⟩, hC⟩, hW⟩ := h
  exact midXP_of_pre hARI hAT hnd hM hKD hIP hTA hPA J hns hp hMV hpp hσ hC hRR hN hW

end

end

end Fl4Proofs.P3
