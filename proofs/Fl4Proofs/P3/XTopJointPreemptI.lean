/-
P3 (DESIGN.md §9): **the preemption path with an inactive current SC**
(KENTRY-PLAN kp8, item 7 / `JPreemptRestHypN` (b)): the third branch of
`mcs_preemption_point` (current thread not schedulable, current SC not
active: FL4 writes the node's `CONSUMED` word 0, the spec sets
`consumed_time := 0`), from ANY `JHole`, `JAtZ` after.

This is the reachable shape of kp1's "reschedule pending without `CurInv`"
case in which the thread finalised its own SC (l4v `sched_context_unbind_all_tcbs`
then `sched_context_zero_refill_max`: the current SC stays the current SC,
unbound and inactive; the same holds for an idle current thread with an
inactive idle SC). `CurInv` is not needed: the step touches one node word.

* `mem_pp_inact` / `fail_pp_inact` (spec): outcomes / failure of
  `preemption_path` in that branch.
* `JHole.mcsPPJI`: FL4's branch at a `JHole`; the end is a `JHole` over the
  same base (the time words of a hole are free), `JAtZ` by `JHole.toJ`:
  `OffOK` is vacuous at a zero consumed time and `CurOwnW` is the base's
  (same heap, current SC and release queue; its release-queue clause is
  vacuous at a zero consumed time).
* `PPCovI σ`: the branch's condition; `JPreemptRestHypI` [W]:
  `JPreemptRestHypN` outside `PPCov ∨ PPCovT ∨ PPCovI` (narrower;
  `jPreemptRestHypI_of`); `afterInv_of_mcs` (XTopJointPreemptZ's
  `afterInvJZ` from any `mcs_preemption_point` post with `JAt`),
  `hPre_ofZI`, `dispatch_invokeJPZI` / `dispatch_invokeJEPZI`.
* kp10: `JPreemptRestHypJ` [W] = `JPreemptRestHypI` at a hole whose current
  thread is not idle and with no switch pending (`JAtPre` carries both from
  the preemption point's base, XTopJointPreemptZ's `jAtPre_holeTN`;
  `jPreemptRestHypJ_of`), `hPre_ofZJ`, `dispatch_invokeJPZJ` /
  `dispatch_invokeJEPZJ`.
-/
import Fl4Proofs.P3.XTopJointPreemptZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem mem_pp_inact {σ : State Unit} {y : Unit × State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(false, σ)}, False))
    (h2 : y ∈ (maybeHandleInterrupt (Z := Unit) true { σ with consumedTime := 0 }).1) :
    y ∈ (preemptionPath (Z := Unit) σ).1 := by
  unfold preemptionPath
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd (x := (schedulable σ.curThread σ, σ)) rfl ?_)
  show y ∈ ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_neg (by simp [hs])]
  refine mem_bind_nd (x := (σ.curSc, σ)) rfl (mem_bind_nd (x := (false, σ)) (by rw [hga]; rfl) ?_)
  show y ∈ ((if false = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_neg (by simp)]
  exact mem_bind_nd (Set.mem_singleton _) h2

theorem fail_pp_inact {σ : State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(false, σ)}, False))
    (h2 : (maybeHandleInterrupt (Z := Unit) true { σ with consumedTime := 0 }).2) :
    (preemptionPath (Z := Unit) σ).2 := by
  unfold preemptionPath
  refine Or.inr ⟨(σ.curThread, σ), rfl, Or.inr ⟨(schedulable σ.curThread σ, σ), rfl, ?_⟩⟩
  show ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_neg (by simp [hs])]
  refine Or.inr ⟨(σ.curSc, σ), rfl, Or.inr ⟨(false, σ), by rw [hga]; rfl, ?_⟩⟩
  show ((if false = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_neg (by simp)]
  exact Or.inr ⟨_, Set.mem_singleton _, h2⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The state with no consumed time. -/
abbrev cons0 (σ : Fl4Spec.State Unit) : Fl4Spec.State Unit := { σ with consumedTime := 0 }

/-- **The inactive-SC branch of the preemption path** (module docstring). -/
def PPCovI (σ : Fl4Spec.State Unit) : Prop :=
  Fl4Spec.schedulable σ.curThread σ = false ∧
    ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → Fl4Spec.scActive x = false

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` with an inactive current SC, from any `JHole`**
(module docstring). -/
theorem JHole.mcsPPJI {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hcov : PPCovI σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  obtain ⟨hsch, hin⟩ := hcov
  have J := Hh.j0
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hS0 := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q0, R00, hc0, hs0⟩ := hS0.lists
  obtain ⟨-, -, -, -, hk, hct, -, -, -, hrq, -, -⟩ := Hh.sfacts
  obtain ⟨ms, t, c, hum, e⟩ := Hh.spec
  have hcs : σ.curSc = σ0.curSc := by rw [e]
  have hks : L.ksb s = L.ksb s0 := Hh.ws.1
  have hcpu : L.cpu s = L.cpu s0 := Hh.ws.2.1
  -- the current SC is one of `Z.C` (the base's `CurOwnW`)
  have hscC : nodeW st s Z.c layout.node.CUR_SC ∈ Z.C := by
    have e1 : (nodeW st s Z.c layout.node.CUR_SC).bv = (nodeW st s0 Z.c layout.node.CUR_SC).bv := by
      rw [← hs.curSc, ← hs0.curSc]; exact hcs
    rw [P1.eq_of_bv e1]; exact cursc_in hS0 J.own
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
  rw [hc.cur] at hsc
  subst hsc
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hab : b1 = Fl4Spec.scActive x := by
    rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hax : Fl4Spec.scActive x = false := hin x n hkx'
  rw [hab, hax]
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with P1.LawfulStore.cur_cpu_spec as ⟨cc, ecc⟩
  step with P1.obj.node_set.spec as ⟨s2, es2⟩
  subst es2 ecc
  rw [hc.cur]
  have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(false, σ)}, False) := by
    unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax]; rfl
  have hs' : Fl4Spec.schedulable σ.curThread σ = false := hsch
  -- FL4's write and the relations
  obtain ⟨hS2, hF2, -⟩ := hS.set_node_consumed 0#u64
  have e0 : U64.bv 0#u64 = (0 : BitVec 64) := by first | rfl | decide | simp
  rw [e0] at hS2
  have hS2' : SchedRel st Z.N Z.T Z.C Z.c (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (cons0 σ) := hS2
  have hR2 : NtfnStateRel Z.N Z.T (L.mem (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64)) (cons0 σ) :=
    hR.frame hS.placed hF2 (KView.refl σ)
  have hcC : Z.c ∈ Cs := hc0.cur ▸ J.kern.cpuCs
  have hN0 : P1.NodePlaced st Z.T s0 Z.c := by
    rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hN : P1.NodePlaced st Z.T s Z.c := by
    rw [J.tcbs_eq.1]; exact P1.TInv.nodes Hh.blk Z.c hcC
  have eA : L.nodeAt s Z.c layout.node.CONSUMED = L.nodeAt s0 Z.c layout.node.CONSUMED :=
    nodeAt_ksb hks _ _
  have hw1 : P1.WritesIn st s (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64)
      (· = L.nodeAt s Z.c layout.node.CONSUMED) :=
    P1.writesIn_wr (P1.nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  have hnb : ∀ o : U64, o.val < 4288 → L.nodeBase s0 Z.c ≤ (L.nodeAt s0 Z.c o).val ∧
      (L.nodeAt s0 Z.c o).val < L.nodeBase s0 Z.c + 4288 := fun o ho => by
    rw [P1.nodeAt_val hN0 ho]; omega
  have hwK : P1.WritesIn st s0 (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (KFoot st Z.T Z.N Z.C Z.c s0 σ0) :=
    (Hh.ws.trans hw1).mono fun b hb => by
      rcases hb with hb | rfl
      · exact hb
      · rw [eA]; exact Or.inl (Or.inr (hnb _ (by simp [layout.node.CONSUMED])))
  have hwT : P1.WritesIn st s0 (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot hwK
  have eσ' : cons0 σ = { σ0 with machineState := ms, curTime := t, consumedTime := 0 } := by rw [e]
  have hK : ScTKw (fun _ => False) σ0 (cons0 σ) := by
    rw [eσ']; exact ⟨fun p => OTK.refl _ _, hum, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hARh : AR a σ.archState.x64CurrentCr3 := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have earch : σ.archState = σ0.archState := by rw [e]
  have hX2 : XTopAt (L := L) AR Z (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) a (cons0 σ) :=
    xtop_sc_step J.xtop J.ip J.nk hwT (ct := σ0.curThread) (hK.mono fun _ h => h.elim) hS2' hR2
      fun _ => by rw [← earch]; exact hARh
  -- P1
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hbx := P1.consumed0_bxi h1 hB1 hX1 hSg1 hS1
  rw [hc.cur] at hbx
  have hblk' : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac
      (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) :=
    ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  -- the debug word
  have hDbg : L.mem (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hh.dbg]
    have hN00 : P1.NodePlaced st Z.T s0 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
    have hd := P1.nodeAt_val hN00 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have h2 := P1.nodeAt_val hN0 (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    have hnb' : ∀ c, L.nodeBase s0 c = (L.ksb s0).val + 13568 + c.val * 4288 := fun _ => rfl
    refine hw1.mem_eq J.kern.dwAl fun hb => ?_
    rw [eA] at hb
    rw [hnb'] at hd h2
    have := congrArg UScalar.val hb
    rw [hd, h2] at this; simp [layout.node.DEBUG_TCBS, layout.node.CONSUMED] at this; omega
  have Hh2 : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0
      (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) a (cons0 σ) :=
    ⟨J, ⟨ms, t, 0, hum, eσ'⟩, hwK, hX2, Hh.nsc, Hh.inv.congr rfl rfl rfl rfl,
      Hh.cur.imp id fun h => h.congr rfl rfl rfl rfl, Hh.act, hblk', hDbg,
        Hh.dbgK_node (by obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists; exact hc.cur ▸ J.kern.cpuCs)
          (Or.inr rfl) hw1⟩
  have hO : OffOK (cons0 σ) := fun h0 => absurd h0 (by show ¬ (0 : BitVec 64) < 0; decide)
  have hOw : CurOwnW Z.T Z.C (cons0 σ) := by
    rcases J.own with ⟨u, hu, xt, hk1, hxs, hb', -⟩ | ⟨⟨c', hc', hcv'⟩, h2⟩
    · refine Or.inl ⟨u, hu, xt, ?_, ?_, fun y m hy => hb' y m ?_,
        fun h0 => absurd h0 (by show ¬ (0 : BitVec 64) < 0; decide)⟩
      · show σ.kheap u.bv = _; rw [hk]; exact hk1
      · show _ = some σ.curSc; rw [hcs]; exact hxs
      · rw [← hk, ← hcs]; exact hy
    · exact Or.inr ⟨⟨c', hc', hcv'.trans hcs.symm⟩, fun y m hy => h2 y m (by rw [← hk, ← hcs]; exact hy)⟩
  obtain ⟨Lst', J'⟩ := Hh2.toJ hO hOw
  exact ⟨cons0 σ, fun y hy => mem_pp_inact hs' hga hy, fun hy => fail_pp_inact hs' hga hy, Z, H, Cs, Ac, Lst', D, J'⟩

set_option maxHeartbeats 16000000 in
/-- **`after_invocation (Err _)` from an `mcs_preemption_point` with `JAt`
after** (XTopJointPreemptZ's `JHole.afterInvJZ`, generic in the budget
part). -/
theorem afterInv_of_mcs {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHypZ (L := L) arI AR) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQZ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, Z', H', Cs', Ac', Lst', D', J'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hIP.take a1 σ') (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum⟩, hAR2⟩, h126, h127⟩
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
      hm _ (mem_maybeHandle_none hIq), Or.inl ⟨Z', H', Cs', Ac', Lst2, D', J2⟩⟩⟩
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
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨z, hm _ (mem_maybeHandle_some hIq hz), Or.inr hJ⟩⟩

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI`** [W] (module
docstring; `JPreemptRestHypN` narrowed by the inactive-SC branch). -/
def JPreemptRestHypI (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypI_of (h : JPreemptRestHypN (L := L) arI AR) : JPreemptRestHypI (L := L) arI AR :=
  fun s a σ hJ hn hc => h s a σ hJ hn fun h' => hc (h'.elim Or.inl fun h2 => Or.inr (Or.inl h2))

/-- **`invoke_afterJ`'s `hPre` with the inactive-SC branch proved** (module
docstring). -/
theorem hPre_ofZI (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypI (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩ := jAtPre_holeT hARI.toARKeep hA hnd hP h
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZ hTs hA hnd (hmrt a1) (hP.minBudget a1) hIP hIrq hc _)
      fun _ h => h.2.toPPQ
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJI hi) hIP hIrq _) fun _ h => h.2.toPPQ
  · exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
      (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) fun h' => h'.elim (fun h2 => hc (Or.inl h2))
        fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZ` with `JPreemptRestHypI`**. -/
theorem dispatch_invokeJPZI [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypI (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZI hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZ` with `JPreemptRestHypI`** (against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZI [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypI (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZI hARI hA hnd hPP hmrt hIP hNS hRest)

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
no switch pending and a non-idle current thread** [W] (kp10:
`JPreemptRestHypI` narrowed by `JAtPre`'s base facts, `jAtPre_holeTN`).
Left: no `CurInv` with a schedulable thread or an active current SC (l4v
`charge_budget` of an SC not owned by the current thread, after SchedContext
Unbind of the own SC or a rebind, kp8 (b')), and kp5 (i) (an endpoint
timeout handler with waiting receivers). -/
def JPreemptRestHypJ (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypJ_of (h : JPreemptRestHypI (L := L) arI AR) : JPreemptRestHypJ (L := L) arI AR :=
  fun s a σ hJ hn _ _ hc => h s a σ hJ hn hc

/-- **`hPre_ofZI` with `JPreemptRestHypJ`** (kp10). -/
theorem hPre_ofZJ (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypJ (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns⟩ := jAtPre_holeTN hARI.toARKeep hA hnd hP h
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZ hTs hA hnd (hmrt a1) (hP.minBudget a1) hIP hIrq hc _)
      fun _ h => h.2.toPPQ
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJI hi) hIP hIrq _) fun _ h => h.2.toPPQ
  · exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
      (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns fun h' => h'.elim (fun h2 => hc (Or.inl h2))
        fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZI` with `JPreemptRestHypJ`** (kp10). -/
theorem dispatch_invokeJPZJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypJ (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZJ hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZI` with `JPreemptRestHypJ`** (kp10; against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypJ (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZJ hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
