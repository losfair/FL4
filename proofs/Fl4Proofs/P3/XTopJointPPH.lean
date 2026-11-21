/-
P3 (DESIGN.md §9), scheduling contexts: **the state after a PREEMPTING
preemption point** (KENTRY-PLAN item 7, step 1: `JAtPre`).

* `nall_getsThe` (SpecFreeRet's `NAll`: every outcome satisfies `P`).
* `pp_err_eq` (spec): every `error` outcome of `preemption_point` is the
  state after its time update and its IRQ check (the only error is the final
  `whenE`; every step before it is deterministic or keeps the state).
* `JAtZ.ppJH`: from `JAtZ` (no `PPR0` needed), a preempting
  `sched.preemption_point` ends at a `JHole` (ScChargeH) whose base is the
  state after the two `WORK_UNITS` writes (XTopJointPP's `ppJD` with
  `JAtZ.timestampJH` in place of `timestampJD`), for EVERY spec `error`
  outcome (`pp_err_eq`).
* `jAtPre_hole`: every `JAtPre` state is a `JHole` (`JAtZ.ppJH`; since kp10
  `JAtPre` has no `JAt` disjunct), so the preemption path
  (`after_invocation (Err)`) can start from a `JHole`.
-/
import Fl4Proofs.P3.ScChargeH
import Fl4Proofs.P3.XTopJointCnDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
open Fl4Spec
variable {σ' α β ε : Type}

theorem nall_getsThe {f : σ' → Option α} {s : σ'} {P : α × σ' → Prop} (h : ∀ v, P (v, s)) :
    NAll (NonDet.getsThe f) s P := by
  intro x hx
  unfold NonDet.getsThe at hx
  cases e : f s with
  | none => rw [e] at hx; exact (show False from hx).elim
  | some v => rw [e] at hx; rw [show x = (v, s) from hx]; exact h v

/-- **Every `error` outcome of the spec's preemption point** is the state
after its time update (`σ1`) and its IRQ check (`σ2`). -/
theorem pp_err_eq {σ σ1 σ2 : State Unit} {irq : Option Irq}
    (hE : updateTimeStamp (Z := Unit) σ = ({((), σ1)}, False))
    (hI : doMachineOp (Z := Unit) (getActiveIRQ true) σ1 = ({(irq, σ2)}, False)) :
    NAll (preemptionPoint (Z := Unit)).run σ (fun y => y.1 = .error () → y.2 = σ2) := by
  unfold preemptionPoint
  apply nallE_bind
  apply nall_liftE
  unfold doExtendedOp
  refine nall_bind (nall_det rfl ?_)
  refine nall_bind ?_
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨⟨u, es⟩, s1⟩ := x
  have hx1' : (u, es) = ((), σ) := hx1
  have hes : es = σ := (Prod.mk.inj hx1').2
  subst es
  have hx2' : s1 = σ := hx2
  subst s1
  refine nall_det rfl ?_
  show NAll (orChoiceE _ _ _).run { σ with exst := σ.exst } _
  unfold orChoiceE
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  intro x hx
  obtain ⟨⟨rv, es2⟩, s2⟩ := x
  obtain ⟨-, hs2⟩ := hx
  have hs2' : s2 = σ := hs2
  subst s2
  dsimp only
  cases rv
  · exact nall_det rfl (fun h => by cases h)
  apply nallE_bind
  apply nall_liftE
  refine nall_bind (nall_det rfl ?_)
  refine nall_bind ?_
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨⟨u, es3⟩, s3⟩ := x
  have hx2' : s3 = σ := hx2
  subst s3
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det hE ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det hI ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  apply nallE_bind
  apply nall_liftE
  unfold getScActive
  refine nall_getsThe (fun v => ?_)
  apply nallE_bind
  apply nall_liftE
  refine nall_det rfl ?_
  dsimp only
  unfold NonDetE.whenE
  split
  · exact nall_det rfl (fun _ => rfl)
  · exact nall_det rfl (fun _ => rfl)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A `JAtZ` state is a `JHole` over itself.** -/
theorem JAtZ.toHole {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JHole (L := L) arI AR Z H Cs Ac Lst D s a σ s a σ where
  j0 := J
  spec := ⟨σ.machineState, σ.curTime, σ.consumedTime, rfl, rfl⟩
  ws := P1.WritesIn.refl s _
  xtop := J.xtop
  nsc := J.nsc
  inv := J.inv
  cur := J.cur
  act := J.act
  blk := J.blk
  dbg := rfl
  dbgK := P1.DbgKeep.refl s

set_option maxHeartbeats 16000000 in
/-- **A preempting preemption point from `JAtZ` ends at a `JHole`** (module
docstring), for every spec `error` outcome. -/
theorem JAtZ.ppJH {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hP : PPPlat arI AR) :
    sched.preemption_point st arI s a ⦃ r => r.1 = .Err .Preempted → ∀ σ',
      (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ⦄ := by
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
  refine WP.spec_bind (J2.timestampJH hAK hA hnd (hP.now a σ)) ?_
  rintro ⟨s3, a1⟩ ⟨σ1, hE1, hk1, hcs1, hrq1, hct1, har1, hum1, -, hK⟩
  have hX1 := (hK σ1.machineState a1 hum1 id).xtop
  have hAR1 : AR a1 σ.archState.x64CurrentCr3 := by
    have h := hX1.fin.1.1.2.2.2.2.2.2
    rw [show ({ σ1 with machineState := σ1.machineState } : Fl4Spec.State Unit).archState = σ.archState from har1] at h
    exact h
  obtain ⟨⟨b2, a2⟩, hip, ⟨irq, ms, hIq, hiff, hum⟩, hAR2⟩ :=
    spec_exists (WP.spec_and (hP.irq a1 σ1) (hP.irqAR a1 _ hAR1))
  have hum' : ms.underlyingMemory = σ.machineState.underlyingMemory := hum.trans hum1
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
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ⦄ := by
    rw [WP.spec_ok]
    intro _ σ' hσ'
    rw [hfin σ' hσ']
    exact ⟨_, Ac2, Lst2, hK ms a2 hum' (fun _ => hAR2)⟩
  have hOk : (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ r =>
      r.1 = .Err .Preempted → ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ⦄ := by
    rw [WP.spec_ok]; intro h; cases h
  cases hact : Fl4Spec.scActive x
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, ite_self]
    exact hErr
  simp only [↓reduceIte]
  refine WP.spec_bind (sufficient_refines s3 a2 σ2 hS2 hscC hkx hact _ (hP.minBudget a2)) ?_
  intro ok1 _
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  split
  · exact hErr
  split
  · exact hOk
  · exact hErr

/-- **Every `JAtPre` state is a `JHole`** (module docstring). -/
theorem jAtPre_hole (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPre (L := L) arI AR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
      (σ0 : Fl4Spec.State Unit), JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ := by
  obtain ⟨s0, a0, σ0, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, -, -⟩, hpp, hσ⟩ := h
  have h := J.ppJH hAK hA hnd hP
  rw [hpp, WP.spec_ok] at h
  obtain ⟨s1, Ac1, Lst1, Hh⟩ := h rfl σ hσ
  exact ⟨Z, H, Cs, Ac1, Lst1, D, s1, a0, σ0, Hh⟩

end

end

end Fl4Proofs.P3
