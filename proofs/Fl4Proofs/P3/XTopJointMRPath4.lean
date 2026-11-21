/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr2): **the remaining MCS
branches of the preemption path under `MachPlat`**: XTopJointPreemptI's
`mcsPPJI` (inactive current SC: `cons0`, the machine fields kept),
XTopJointPreemptA's `mcsPPJA` and ScChargeTR's `mcsPPJR` (insufficient
budget: `checkBudget`'s charge with a timeout fault to an endpoint handler,
idle/sending resp. receiving; `mfk_checkBudget`), with `MR r.2 σ'.ms ∧
ValidIrqMasks σ'` after. Scripted copies as in XTopJointMRPath3.
-/
import Fl4Proofs.P3.XTopJointMRPath3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}
set_option maxHeartbeats 16000000 in
/-- `JHole.mcsPPJI` with `MR` and `ValidIrqMasks` after (module docstring). -/
theorem JHole.mcsPPJIM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hcov : PPCovI σ)
    (hAT : P0.ArchTotal arI)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  have key : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
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
    exact ⟨cons0 σ, fun y hy => mem_pp_inact hs' hga hy, fun hy => fail_pp_inact hs' hga hy, ⟨Z, H, Cs, Ac, Lst', D, J'⟩, rfl, fun hN => hN⟩
  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

set_option maxHeartbeats 16000000 in
/-- `JHole.mcsPPJA` with `MR` and `ValidIrqMasks` after (module docstring). -/
theorem JHole.mcsPPJAM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hnsuf : ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true))
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  have key : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
    have hS := Hh.xtop.fin.1.1.1
    have hR := Hh.xtop.fin.1.1.2.2.1
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
    unfold syscall.mcs_preemption_point
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
    rw [hc.cur] at hct'
    subst hct'
    rw [schedulable_eq hR hS hc.curT] at hb
    have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
    subst hb
    rw [← ect, hsch]
    simp only [↓reduceIte]
    refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb)
      (Hh.checkBudgetTA hAT hC hni hres hnq hmrt hmb hkt hrr hth hper hcb)) ?_
    rintro ⟨r, s', a'⟩ ⟨hT, hF⟩
    refine (WP.spec_ok _).2 ?_
    cases r
    · obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF rfl
      exact ⟨z.2, fun y hy => mem_pp_sched hsch hz hy, fun hy => fail_pp_sched hsch hz hy,
        ⟨Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩, MachF.mfk_checkBudget σ z hz, fun hN => SInv.ns_checkBudget σ hN z hz⟩
    · exact absurd (hT rfl).2.2 hnsuf
  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

set_option maxHeartbeats 16000000 in
/-- `JHole.mcsPPJR` with `MR` and `ValidIrqMasks` after (module docstring). -/
theorem JHole.mcsPPJRM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hnsuf : ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true))
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l)))
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  have key : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
    have hS := Hh.xtop.fin.1.1.1
    have hR := Hh.xtop.fin.1.1.2.2.1
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
    unfold syscall.mcs_preemption_point
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
    rw [hc.cur] at hct'
    subst hct'
    rw [schedulable_eq hR hS hc.curT] at hb
    have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
    subst hb
    rw [← ect, hsch]
    simp only [↓reduceIte]
    refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb)
      (Hh.checkBudgetTR hAT hmax htu hC hni hres hnq hmrt hmb hkt hrr hth hper hkl)) ?_
    rintro ⟨r, s', a'⟩ ⟨hT, hF⟩
    refine (WP.spec_ok _).2 ?_
    cases r
    · obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF rfl
      exact ⟨z.2, fun y hy => mem_pp_sched hsch hz hy, fun hy => fail_pp_sched hsch hz hy,
        ⟨Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩, MachF.mfk_checkBudget σ z hz, fun hN => SInv.ns_checkBudget σ hN z hz⟩
    · exact absurd (hT rfl).2.2 hnsuf
  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

end

end

end Fl4Proofs.P3
