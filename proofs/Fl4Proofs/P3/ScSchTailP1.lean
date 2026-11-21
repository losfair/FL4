/-
P3 (DESIGN.md §9), scheduler: **`SchTailHyps`' P1 facts from P1's
`schedule`** (`jat_scheduleT2`): of the facts after FL4's `schedule` that
`jat_scheduleT` names, three follow from P1's theorems about the whole of
`schedule` (the TCB timers, then the scheduler) at `JAtZ`'s `BlkOK`:

* `dbg`: core 0's `DEBUG_TCBS` word is in neither footprint (`KW` leaves the
  nodes' `DEBUG_TCBS` words out, `dbg0_not_schedW`), so it is kept from the
  entry to the timers' end and to `schedule`'s;
* `dwNe`: that word is in core 0's node, which no TCB overlaps;
* `blk`: P1's `sched.schedule.tinv` (the queues, `BoundInv`, `XInv`,
  `SCsOK`) with `SgOK` (the kernel base kept).

`jat_scheduleT2` is `jat_scheduleT` with `hTail` giving only the remaining
fact (`SchTailHypsR`: the CR3 after the arch switch, [P]), given P1's
`ArchTotal` (core 0 among the cores is `JKern.cs0`) and, at the `JAtZ` states, every TCB of
the sets in the typed heap with its mapped vtable PML4's ASID non-zero ([J],
issue #16's vtable-ASID fact; `CurOK` after from it at the new current
thread, the slots kept); the dead set stays dead by
`deadP_sch_step` with the spec's `schedule` cutting no links (`lkm_schedule`).
-/
import Fl4Proofs.P3.ScJointSchTail
import Fl4Proofs.P3.ScDeadSch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **Core 0's `DEBUG_TCBS` word is in no footprint of `schedule`.** -/
theorem dbg0_not_schedW {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (h0 : 0#u64 ∈ Cs) :
    ¬ SchedW st T Cs Sg Scs Z H s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, hS, hSg⟩ := h
  have hT := hq.tcbs
  have hN0 := hq.nodes 0#u64 h0
  have hd : layout.node.DEBUG_TCBS.val = 88 := debug_val
  have hv := nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [hd])
  have hal := nodeAt_aligned hN0 (off := layout.node.DEBUG_TCBS) (by simp [hd]) (by simp [hd])
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  have h00 : (0#u64 : U64).val = 0 := rfl
  have outN : ∀ b, OutsideObjs st T Cs s b → b ≠ L.nodeAt s 0#u64 layout.node.DEBUG_TCBS := by
    intro b hb e
    subst e
    have := hb.2.2 0#u64 h0
    rw [hv, hd] at this; omega
  rintro (hk | ⟨o, ho, e⟩)
  · rcases hk with ⟨y, hy, K, hK1, hK2, -, -, e⟩ | ⟨c, hc, o, ho, ho88, e⟩ | hs | ⟨c, hc, hin⟩ | ⟨e, he, he'⟩
    · have hyv := field_val (hT y hy) hK2
      have := hN0.disj y hy
      have e' := congrArg UScalar.val e
      rw [hv, hd, hyv] at e'
      have e12 : (2 : Nat) ^ 12 = 4096 := rfl
      omega
    · have hNc := hq.nodes c hc
      have e' := congrArg UScalar.val e
      rw [hv, hd, nodeAt_val hNc ho, hnb, hnb, h00] at e'
      by_cases hc0 : c.val = 0
      · omega
      · have : 1 ≤ c.val := Nat.one_le_iff_ne_zero.mpr hc0
        omega
    · exact outN _ (hq.omega _ (hSg.sub _ hs)) rfl
    · have hsg := (hS.all c hc).2.2 _ hal hin
      exact outN _ (hq.omega _ (hSg.sub _ hsg)) rfl
    · obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := hq.eps
      have heE : e ∈ E := (ty.2.2.1 e).2 he
      obtain ⟨hE, hEN, -⟩ := w1 e heE
      obtain ⟨o1, o2⟩ := ep_out hE hEN
      rcases he' with e1 | e1
      · exact outN _ o1 e1.symm
      · exact outN _ o2 e1.symm
  · have hfit := hN0.fits
    have e' := congrArg UScalar.val e
    rw [hv, hd] at e'
    simp only [core.num.U64.wrapping_add_val_eq] at e'
    rw [hnb, h00] at hfit e'
    have : ((L.ksb s).val + o.val) % UScalar.size UScalarTy.U64 = (L.ksb s).val + o.val := by
      apply Nat.mod_eq_of_lt; simp [U64.size_def, U64.numBits]; omega
    rw [this] at e'
    omega

/-- **`schedule`'s footprint keeps every debug word** (KENTRY-PLAN g2i: `KW`
leaves them out, the kernel-state block holds none: the TCBs and the nodes lie
outside it). -/
theorem dbgKeep_schedW {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hw : WritesIn st s s' (SchedW st T Cs Sg Scs Z H s)) :
    DbgKeep st T Cs s s' :=
  ⟨hw.1, fun b hb => hw.mem_eq (dbgW_aligned h hb) fun hs => by
    rcases hs with hk | ⟨o, ho, rfl⟩
    · exact dbgW_not_kw h hk hb
    · obtain ⟨⟨Q, R, hq⟩, -⟩ := h
      have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := wadd_val (by omega)
      have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
      rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
      · have hyv : (dnA y).val = y.val + 3576 := field_val (hq.tcbs y hy) (K := 3576#u64) (by simp)
        have e' := congrArg UScalar.val e
        rw [hv, hyv] at e'
        rcases hq.ksOut y hy with h1 | h1 <;> omega
      · have hyv : (dpA y).val = y.val + 3584 := field_val (hq.tcbs y hy) (K := 3584#u64) (by simp)
        have e' := congrArg UScalar.val e
        rw [hv, hyv] at e'
        rcases hq.ksOut y hy with h1 | h1 <;> omega
      · have e' := congrArg UScalar.val e
        rw [hv, nodeAt_val (hq.nodes c hc) (by simp [debug_val]), hnb, debug_val] at e'
        omega⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The facts after `schedule` still named** (`SchTailHyps` without its
P1 facts). -/
structure SchTailHypsR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (D : Set U64)
    (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop where
  ar : AR a' σ'.archState.x64CurrentCr3

set_option maxHeartbeats 4000000 in
/-- **`jat_scheduleT` with `SchTailHyps`' P1 facts proved** (module
docstring). -/
theorem jat_scheduleT2 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T, Z.th t = some .tcb ∧
        ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hfireJ : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW Z.T Z.C σ1 ∧
      ∃ (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64), JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 r.1 r.2 σ1 ⦄)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 r.2 σ' ∧ CurInv σ' ⦄ := by
  have h0Cs : 0#u64 ∈ Cs := J.kern.cs0
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  obtain ⟨⟨Q, R, hq⟩, hBd, hXi, hSc, hSg⟩ := id hB
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hq.nodes 0#u64 h0Cs) (by simp [P1.debug_val]) (by simp [P1.debug_val])
  have hfire2 : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW Z.T Z.C σ1 ∧
      ((∃ (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64), JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 r.1 r.2 σ1) ∧
        timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s) ⦄ := by
    refine WP.spec_mono (P1.spec_eq' (WP.spec_and hfireJ (P1.timer.fire.kw hAT hNt s a hB))) ?_
    rintro ⟨s1, a1⟩ ⟨hf, ⟨σ1, h1, h2, h3, h4, h5, hJ⟩, hk⟩
    simp only [WP.uncurry'_pair] at hk
    exact ⟨σ1, h1, h2, h3, h4, h5, hJ, hf, hk.1⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and (schedule_refinesWP s a σ hS hR J.nsc hnd hfire2 hA hsni hsend hT)
    (P1.sched.schedule.kw hAT hNt s a hB)) (WP.spec_and (P1.sched.schedule.tinv hAT hNt s a Q R hq hBd hSc hXi hSg)
      hTail)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨Ac1, Lst1, D1, J1⟩, hfr, hkf⟩, hw, hrun⟩,
    hkw⟩, ⟨htinv, hRest⟩⟩
  simp only [WP.uncurry'_pair] at hkw htinv
  obtain ⟨rf', hrf', -, hkw⟩ := hkw
  obtain rfl : rf = rf' := by simpa using (hrf'.symm.trans hfr).symm
  have hTl := hRest rf σ1 σ' D1 hF hsc hw hS' hI' hC' hA'
  obtain ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', -, -, -, -⟩ := htinv
  have hks' : L.ksb s' = L.ksb s := hkw.1.trans hkf
  have hnA : L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hkf _ _
  have hdbg : L.mem s' (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) =
      L.mem rf.1 (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) := by
    exact hkw.mem_eq (by rw [hnA]; exact hal) (P1.dbg0_not_schedW J1.blk h0Cs)
  have hdw : (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val := by
    have hN0 := hq'.nodes 0#u64 h0Cs
    have hct : L.curW s' ∈ P1.Heap.tcbs H := hq'.curT
    have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [P1.debug_val])
    have hsv := P1.field_val (hq'.tcbs _ hct) (K := 3328#u64) (by decide)
    have hdj := hN0.disj _ hct
    have hv' : (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s' 0#u64 + 88 := by
      rw [hnA, ← P1.nodeAt_of_ksb hks' 0#u64 layout.node.DEBUG_TCBS, hv, P1.debug_val]
    have hsv' : (P1.stA (L.curW s')).val = (L.curW s').val + 3328 := by
      rw [P1.stA_eq, hsv]; rfl
    rw [hv', hsv']
    have e12 : (2 : Nat) ^ 12 = 4096 := rfl
    rw [e12] at hdj
    omega
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  have hK1 : SchStep (fun _ => False) σ1 σ' := (schs_schedule.of_eq hsc).1
  have hL1 : LK (fun _ => False) σ1 σ' := lkm_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hSS : SlotsSame Z.th (L.mem rf.1) (L.mem s') :=
    slotsSame_of_iw J1.xtop.rel.1 J1.xtop.rel.2.2.2.2.2.1 J1.xtop.rel.2.2.2.2.2.2 hwT
      fun b hb => tfoot_iw J1.xtop.fin.1.1.1 hb
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hS'.lists
  obtain ⟨hth, hvt⟩ := hVt _ _ _ _ _ _ J1 _ hcc.curT
  have hcur : Vs.CurOK st Z.th s' σ' :=
    ⟨_, hsc'.curThread.symm, hth, fun p asid h => hvt p asid (by
      rwa [hSS.capAt ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩] at h)⟩
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sched_step J1.xtop J1.ip J1.nk hwT (ct := σ1.curThread)
      { hK1 with kh := fun p => (hK1.kh p).mono False.elim } hS' hR' hcur hTl.ar
  have hSOK1 := (schs_schedule.of_eq hsc).2
  have hY1 : YieldRel Z.T Z.C (L.mem s') σ' :=
    (ScAll.of_k J1.xtop.fin.1.1.1 J1.rp J1.yld J1.mcp J1.call J1.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSOK1⟩).2.1
  have hdead : ∀ q ∈ D1, Sched.DeadP (L := L) H s' q := fun q hq =>
    J1.deadP_sch_step hX' hwT hK1 hL1 hA' (J1.ymd hS' hY1 ((hSOK1.ykeep rfl).dk q.bv)) (fun h => h)
      (J1.jcov.dead q hq)
  have hT2 : SchTailHyps (L := L) AR Z H Cs D1 rf.1 s' a' σ' Ac :=
    ⟨hcur, hTl.ar, hdbg, hdw, hdead,
      ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', hSg.ksb' hks'⟩, P1.dbgKeep_schedW J1.blk J1.kern.ksbFit hkw⟩
  obtain ⟨Lst', J'⟩ := J1.sch_tail hsc hw hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hT2
  exact ⟨σ', Ac, Lst', D1, J', hC'⟩

end

end

end Fl4Proofs.P3
