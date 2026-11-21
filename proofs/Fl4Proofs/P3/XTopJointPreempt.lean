/-
P3 (DESIGN.md §9): **the preemption path at `J`** (KENTRY-PLAN item 7):
FL4's `after_invocation (Err _)` (`mcs_preemption_point`, `take_pending_irq`,
`check_interrupt`) against the spec's `preemption_path`, from every `JAtPre`
state (XTopJointPPH's `jAtPre_hole`: a `JHole`).

* `JHole.msAr`: a `JHole` with another machine state (same memory) and an
  arch state keeping `AR` is a `JHole` (the IRQ check).
* `JHoleAt`: some `JHole` ends at the state (what the path keeps).
* `mem_pp_sched` / `mem_pp_charge` (spec): outcomes of `preemption_path`
  from an outcome of its budget part (`check_budget`, or `charge_budget
  consumed false` for an active SC) and of `maybe_handle_interrupt true`.
* `JHole.mcsPPJ`: `mcs_preemption_point` from a `JHole` under `PPCov`
  (`CurInv`, a non-idle current thread, no switch to it pending, `NoTmoSend`)
  or `PPCovT` (`JHole.checkBudgetT`'s case: an endpoint timeout handler on an
  idle or sending endpoint, non-RR SC, the current thread running or
  restarting, unqueued, no reschedule pending):
  schedulable → `check_budget` (`true`: nothing changes, `check_budgetT` /
  `checkBudget_suff`; `false`: `JHole.checkBudgetF` / `JHole.checkBudgetT`,
  the current thread's timeout fault blocking it), not schedulable →
  `charge_budget consumed false` (`JHole.chargeBudgetJ`; the SC is active:
  `CurInv.active`, `curSc ≠ idleSc`); the third FL4 branch (inactive SC) is
  unreachable under either.
* `IrqPlat` [P] (M4): FL4's `take_pending_irq` is the spec's
  `getActiveIRQ true` (an oracle of the spec's machine state; `NO_IRQ` ↔
  `none`, otherwise the same line number, not masked in the spec), keeping
  `AR`; one core: no IPI line is pending (`noIpi`); `ack_irq` keeps `AR`.
* `JIrqHyp` [W] (l4v `handle_interrupt_corres`): `handle_interrupt` of an
  unmasked line from a `JHoleAt` state refines `handle_interrupt` (or the
  spec fails: e.g. an inactive line, where FL4 masks it; l4v excludes it by
  `valid_irq_masks`, which `JHoleAt` does not carry), `XTopAt`
  after (not `JHoleAt`: a `JHole`'s spec state differs from its base only in
  the machine state and the time words, while the timer branch sets
  `reprogramTimer` and a signal changes the heap); the IPI lines 126/127
  excluded (`IrqPlat.noIpi`). Proved downstream: XTopJointIrq's
  `jIrqHyp_of` (the signal from a hole that is not `JAtZ` named there,
  `JIrqSigHyp` [W]).
* `JHole.afterInvJ`: `after_invocation (Err _)` from a `JHole` under `PPCov ∨ PPCovT`
  refines `preemption_path` (`PPQ`: the spec fails, or an outcome with
  `JHoleAt` after when no line is pending,
  `XTopAt` after `JIrqHyp` for a pending line).
* `JPreemptRestHyp` [W]: `hPre` at the `JHoleAt` states outside `PPCov ∨
  PPCovT` (a reschedule pending without `CurInv`, the idle thread current, a
  pending switch to the current thread, an endpoint timeout handler with a
  non-RR SC and waiting receivers / a reschedule pending / a queued or
  RUNNING_VM current thread).
* `hPre_of`: `invoke_afterJ`'s `hPre` for `Q := PPQ` from the platform facts
  [P], `JIrqHyp` [W] and `JPreemptRestHyp` [W]; `dispatch_invokeJP` /
  `dispatch_invokeJEP` are `dispatch_invokeJ` / `dispatch_invokeJE` with it
  (no `hPre`).
-/
import Fl4Proofs.P3.XTopJointPPH
import Fl4Proofs.P3.XTopJointBudgetT
import Fl4Proofs.P3.XTopJointDispatch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **An outcome of `preemption_path`, schedulable current thread**: an
outcome of `check_budget`, then of `maybe_handle_interrupt true`. -/
theorem mem_pp_sched {σ σ' : State Unit} {b : Bool} {y : Unit × State Unit}
    (hs : schedulable σ.curThread σ = true) (h1 : (b, σ') ∈ (checkBudget (Z := Unit) σ).1)
    (h2 : y ∈ (maybeHandleInterrupt (Z := Unit) true σ').1) : y ∈ (preemptionPath (Z := Unit) σ).1 := by
  unfold preemptionPath
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd (x := (schedulable σ.curThread σ, σ)) rfl ?_)
  show y ∈ ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_pos hs]
  exact mem_bind_nd h1 h2

/-- **An outcome of `preemption_path`, current thread not schedulable, active
current SC**: an outcome of `charge_budget consumed false`, then of
`maybe_handle_interrupt true`. -/
theorem mem_pp_charge {σ σ' : State Unit} {y : Unit × State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False))
    (h1 : ((), σ') ∈ (chargeBudget (Z := Unit) σ.consumedTime false σ).1)
    (h2 : y ∈ (maybeHandleInterrupt (Z := Unit) true σ').1) : y ∈ (preemptionPath (Z := Unit) σ).1 := by
  unfold preemptionPath
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd (x := (schedulable σ.curThread σ, σ)) rfl ?_)
  show y ∈ ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_neg (by simp [hs])]
  refine mem_bind_nd (x := (σ.curSc, σ)) rfl (mem_bind_nd (x := (true, σ)) (by rw [hga]; rfl) ?_)
  show y ∈ ((if true = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_pos rfl]
  exact mem_bind_nd (x := (σ.consumedTime, σ)) rfl (mem_bind_nd h1 h2)

theorem fail_pp_sched {σ σ' : State Unit} {b : Bool}
    (hs : schedulable σ.curThread σ = true) (h1 : (b, σ') ∈ (checkBudget (Z := Unit) σ).1)
    (h2 : (maybeHandleInterrupt (Z := Unit) true σ').2) : (preemptionPath (Z := Unit) σ).2 := by
  unfold preemptionPath
  refine Or.inr ⟨(σ.curThread, σ), rfl, Or.inr ⟨(schedulable σ.curThread σ, σ), rfl, ?_⟩⟩
  show ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_pos hs]
  exact Or.inr ⟨_, h1, h2⟩

theorem fail_pp_charge {σ σ' : State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False))
    (h1 : ((), σ') ∈ (chargeBudget (Z := Unit) σ.consumedTime false σ).1)
    (h2 : (maybeHandleInterrupt (Z := Unit) true σ').2) : (preemptionPath (Z := Unit) σ).2 := by
  unfold preemptionPath
  refine Or.inr ⟨(σ.curThread, σ), rfl, Or.inr ⟨(schedulable σ.curThread σ, σ), rfl, ?_⟩⟩
  show ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_neg (by simp [hs])]
  refine Or.inr ⟨(σ.curSc, σ), rfl, Or.inr ⟨(true, σ), by rw [hga]; rfl, ?_⟩⟩
  show ((if true = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_pos rfl]
  exact Or.inr ⟨(σ.consumedTime, σ), rfl, Or.inr ⟨_, h1, h2⟩⟩

theorem checkBudget_suff {σ : State Unit} (hnd : numDomains = 1)
    (hb : getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(true, σ)}, False)) :
    checkBudget (Z := Unit) σ = ({(true, σ)}, False) := by
  unfold checkBudget
  rw [nd_gets_bind, nd_gets_bind, nd_bind_one hb]
  have e : isCurDomainExpired σ = false := by simp [isCurDomainExpired, hnd]
  show (do let domExp ← NonDet.gets isCurDomainExpired; return !domExp) σ = _
  rw [nd_gets_bind, e]; rfl

/-- `maybe_handle_interrupt` with no pending line. -/
theorem mem_maybeHandle_none {σ σ' : State Unit}
    (h : doMachineOp (Z := Unit) (getActiveIRQ true) σ = ({(none, σ')}, False)) :
    ((), σ') ∈ (maybeHandleInterrupt (Z := Unit) true σ).1 := by
  unfold maybeHandleInterrupt
  exact mem_bind_nd (x := (none, σ')) (by rw [h]; rfl) rfl

/-- `maybe_handle_interrupt` fails when the handling of its line does. -/
theorem fail_maybeHandle_some {σ σ' : State Unit} {i : Irq}
    (h : doMachineOp (Z := Unit) (getActiveIRQ true) σ = ({(some i, σ')}, False))
    (hf : (handleInterrupt (Z := Unit) i σ').2) : (maybeHandleInterrupt (Z := Unit) true σ).2 := by
  unfold maybeHandleInterrupt
  exact Or.inr ⟨(some i, σ'), by rw [h]; rfl, hf⟩

/-- `maybe_handle_interrupt` with a pending line. -/
theorem mem_maybeHandle_some {σ σ' : State Unit} {i : Irq} {z : Unit × State Unit}
    (h : doMachineOp (Z := Unit) (getActiveIRQ true) σ = ({(some i, σ')}, False))
    (hz : z ∈ (handleInterrupt (Z := Unit) i σ').1) :
    z ∈ (maybeHandleInterrupt (Z := Unit) true σ).1 := by
  unfold maybeHandleInterrupt
  exact mem_bind_nd (x := (some i, σ')) (by rw [h]; rfl) hz

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A `JHole` with another machine state and arch state** (module docstring). -/
theorem JHole.msAr {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (ms : Fl4Spec.MachineState) (a' : A)
    (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a' { σ with machineState := ms } := by
  have J := Hh.j0
  obtain ⟨ms0, t, c, hum0, e⟩ := Hh.spec
  have hX := Hh.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hARh : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hum' : ms.underlyingMemory = σ0.machineState.underlyingMemory := by
    rw [hum, e]; exact hum0
  have earch : σ.archState = σ0.archState := by rw [e]
  have hK : ScTKw (fun _ => False) σ0 { σ with machineState := ms } := by
    subst e
    exact ⟨fun p => OTK.refl _ _, hum', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hS2 : SchedRel st Z.N Z.T Z.C Z.c s { σ with machineState := ms } :=
    hS.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hR2 : NtfnStateRel Z.N Z.T (L.mem s) { σ with machineState := ms } := ⟨hR.ntfn, hR.tcb⟩
  have hwT : P1.WritesIn st s0 s (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot Hh.ws
  have hX' : XTopAt (L := L) AR Z s a' { σ with machineState := ms } :=
    xtop_sc_step J.xtop J.ip J.nk hwT (ct := σ0.curThread) (hK.mono fun _ h => h.elim) hS2 hR2
      fun _ => by rw [← earch]; exact hAR hARh
  exact ⟨J, ⟨ms, t, c, hum', by rw [e]⟩, Hh.ws, hX', Hh.nsc, Hh.inv.congr rfl rfl rfl rfl,
    Hh.cur.imp id fun h => h.congr rfl rfl rfl rfl, Hh.act, Hh.blk, Hh.dbg, Hh.dbgK⟩

variable (arI) in
/-- Some `JHole` ends at `(s, a, σ)`. -/
def JHoleAt (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
    (σ0 : Fl4Spec.State Unit), JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ

/-- **The cases of the preemption path proved here**: `CurInv`, the current
thread not idle, no switch to it pending, no timeout fault raisable. -/
def PPCov (σ : Fl4Spec.State Unit) : Prop :=
  CurInv σ ∧ σ.curThread ≠ σ.idleThread ∧ σ.schedulerAction ≠ .switchThread σ.curThread ∧ NoTmoSend σ

/-- **The endpoint-timeout-handler case of the preemption path proved here**
(`JHole.checkBudgetT`'s conditions): `CurInv`, the current thread not idle,
running or restarting, not queued, no reschedule pending, an endpoint cap as
its timeout handler on an idle or sending endpoint, a non-RR current SC. -/
def PPCovT (σ : Fl4Spec.State Unit) : Prop :=
  CurInv σ ∧ σ.curThread ≠ σ.idleThread ∧ σ.schedulerAction = .resumeCurThread ∧
    (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0) ∧
    ∃ (xt : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
      σ.kheap σ.curThread = some (.tcb xt) ∧ (xt.tcbState = .running ∨ xt.tcbState = .restart) ∧
      xt.tcbTimeoutHandler = .endpointCap p bd r ∧ ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` from a `JHole`** (module docstring). -/
theorem JHole.mcsPPJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ ∨ PPCovT σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JHoleAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  obtain ⟨hC, hni, hnsw⟩ : CurInv σ ∧ σ.curThread ≠ σ.idleThread ∧
      σ.schedulerAction ≠ .switchThread σ.curThread := by
    rcases hcov with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩
    · exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, by rw [h3]; exact fun h => by cases h⟩
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct
  subst hct
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  cases hsch : Fl4Spec.schedulable (nodeW st s Z.c layout.node.CUR_THREAD).bv σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with sched.cur_sc.spec' as ⟨sc, hsc⟩
    step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
    rw [hc.cur] at hsc
    subst hsc
    obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
    have hab : b1 = Fl4Spec.scActive x := by
      rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
    have hax : Fl4Spec.scActive x = true := hact (by rw [← hs.curSc]; exact hid) x n hkx
    rw [hab, hax]
    simp only [↓reduceIte]
    step with sched.consumed.spec' as ⟨cv, hcv⟩
    rw [hc.cur] at hcv
    subst hcv
    refine WP.spec_mono (Hh.chargeBudgetJ hAT hC hni hnsw hmrt hmb _) ?_
    rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
    simp only at ha
    subst a'
    have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
    have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
      unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax]; rfl
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    have hs' : Fl4Spec.schedulable σ.curThread σ = false := by rw [ect]; exact hsch
    refine ⟨σ', ?_, ?_, Z, H, Cs, Ac, Lst', D, s', a, σ', J'.toHole⟩
    · exact fun y hy => mem_pp_charge hs' hga (by rw [h1']; rfl) hy
    · exact fun hy => fail_pp_charge hs' hga (by rw [h1']; rfl) hy
  · simp only [↓reduceIte]
    have hs' : Fl4Spec.schedulable σ.curThread σ = true := by rw [ect]; exact hsch
    have hFT : sched.check_budget st arI s a ⦃ res => res.1 = false → ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 →
          y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JHoleAt (L := L) arI AR res.2.1 res.2.2 σ' ⦄ := by
      rcases hcov with ⟨-, -, -, hnt⟩ | ⟨-, -, hres, hnq, hper, xt, p, bd, r, hkt, hrr, hth, hcb⟩
      · refine WP.spec_mono (Hh.checkBudgetF hAT hC hni hnsw hmrt hmb hnt) ?_
        rintro ⟨r, s', a'⟩ hF hr
        obtain ⟨ha, σ', h1, -, Lst', J'⟩ := hF hr
        simp only at ha
        subst a'
        exact ⟨σ', fun y hy => mem_pp_sched hs' (by rw [h1]; rfl) hy,
          fun hy => fail_pp_sched hs' (by rw [h1]; rfl) hy, Z, H, Cs, Ac, Lst', D, s', a, σ', J'.toHole⟩
      · refine WP.spec_mono (Hh.checkBudgetT hAT hC hni hres hnq hmrt hmb hkt hrr hth hper hcb) ?_
        rintro ⟨r, s', a'⟩ hF hr
        obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF hr
        exact ⟨z.2, fun y hy => mem_pp_sched hs' hz hy, fun hy => fail_pp_sched hs' hz hy,
          Z.mv Z.G V, H, Cs, Ac', Lst', D', s', a', z.2, J'.toHole⟩
    refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb) hFT) ?_
    rintro ⟨r, s', a'⟩ ⟨hT, hF⟩
    refine (WP.spec_ok _).2 ?_
    cases r
    · exact hF rfl
    · obtain ⟨e, hsuf, -⟩ := hT rfl
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨σ, fun y hy => mem_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy,
        fun hy => fail_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy, Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩

variable (arI) in
/-- **The platform's pending interrupt is the spec's** [P] (M4; module
docstring). -/
structure IrqPlat (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  take : ∀ (a : A) (σ : Fl4Spec.State Unit), arI.take_pending_irq a ⦃ r => ∃ irq ms,
    Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
    (r.1 = syscall.NO_IRQ ↔ irq = none) ∧
    (∀ i, irq = some i → r.1.val = i.toNat ∧ ms.irqMasks i = false) ∧
    ms.underlyingMemory = σ.machineState.underlyingMemory ⦄
  takeAR : ∀ a c, AR a c → arI.take_pending_irq a ⦃ r => AR r.2 c ⦄
  /-- One core (l4v's model is uniprocessor; seL4 C raises IPIs only under
  `ENABLE_SMP_SUPPORT`): no IPI line (`REMOTE_CALL_IPI` = 126,
  `RESCHEDULE_IPI` = 127 on x86_64) is ever pending. -/
  noIpi : ∀ a : A, arI.take_pending_irq a ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄
  /-- Acknowledging an interrupt keeps `AR` (the CR3 is not touched). -/
  ackAR : ∀ a i c, AR a c → arI.ack_irq a i ⦃ a' => AR a' c ⦄

variable (arI) in
/-- **`handle_interrupt` at `J`** [W] (l4v `handle_interrupt_corres`; module
docstring). -/
def JIrqHyp (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JHoleAt (L := L) arI AR s a σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄

variable (arI) in
/-- What the preemption path ends in: some outcome of the spec's
`preemption_path` from `σ1`, a `JHoleAt` state. -/
def PPQ (AR : A → Fl4Spec.Cr3 → Prop) (σ1 : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨ ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1,
    JHoleAt (L := L) arI AR r.1 r.2 z.2 ∨ ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2

set_option maxHeartbeats 16000000 in
/-- **`after_invocation (Err _)` from a `JHole`** (module docstring). -/
theorem JHole.afterInvJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHyp (L := L) arI AR) (hcov : PPCov σ ∨ PPCovT σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind (Hh.mcsPPJ hAT hnd hmrt hmb hcov) ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, Z', H', Cs', Ac', Lst', D', s0', a0', σ0', Hh'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := Hh'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hIP.take a1 σ') (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum⟩, hAR2⟩, h126, h127⟩
  have Hh2 := Hh'.msAr ms a2 hum (fun _ => hAR2)
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
      hm _ (mem_maybeHandle_none hIq), Or.inl ⟨Z', H', Cs', Ac', Lst', D', s0', a0', σ0', Hh2⟩⟩⟩
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
    refine WP.spec_bind (hIrq s1 a2 _ w i ⟨Z', H', Cs', Ac', Lst', D', s0', a0', σ0', Hh2⟩ hwi hmask h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inl (hmf (fail_maybeHandle_some hIq hf))⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨z, hm _ (mem_maybeHandle_some hIq hz), Or.inr hJ⟩⟩

variable (arI) in
/-- **The preemption path outside `PPCov`** [W] (module docstring;
KENTRY-PLAN kp6). -/
def JPreemptRestHyp (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → ¬ (PPCov σ ∨ PPCovT σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

/-- **`invoke_afterJ`'s `hPre` for `Q := PPQ`** (module docstring). -/
theorem hPre_of (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHyp (L := L) arI AR) (hRest : JPreemptRestHyp (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := jAtPre_hole hAK hA hnd hP h
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJ hA hnd (hmrt a1) (hP.minBudget a1) hIP hIrq hc _) fun _ h => h.2
  · exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ hc

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJ` without `hPre`**: the preemption path from
`hPre_of` (module docstring). -/
theorem dispatch_invokeJP [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHyp (L := L) arI AR) (hRest : JPreemptRestHyp (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_of hAK hA hnd hPP hmrt hIP hIrq hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJE` without `hPre`** (against `fl4HandleEvent true`'s
branch). -/
theorem dispatch_invokeJEP [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHyp (L := L) arI AR) (hRest : JPreemptRestHyp (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_of hAK hA hnd hPP hmrt hIP hIrq hRest)

end

end

end Fl4Proofs.P3
