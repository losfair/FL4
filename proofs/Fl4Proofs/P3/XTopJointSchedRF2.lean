/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch5 (B)): **`schedule` at
`J` with the domain switch, up to the FPU, spec side**. From a `JAtZ`
entry with `σ.domainTime ≠ 0 ∨ NdOK s σ` (no `hd`), ScNextDomCF's
`schedule_refinesWP0F` runs: the timers' predicate is built here.

* `JAtZ.ndOK_fire`: `NdOK` (ScNextDomB; its two [J] facts `DomListOK` and
  the `DOM_SCHED_IDX` word) carried from the entry to the state after FL4's
  TCB timers: the spec side keeps the domain list, index and start
  (ScFpuOwnK's `fires_dom`: `send_signal` keeps them), FL4's `timer::fire`
  writes only P1's `FootD` words (`timer.fire.kw`), which miss the
  kernel-global block's first 256 bytes (`kwApartJ` for `KW`; the debug
  links are TCB and node words, off the block by `JKern.hks`/the node
  layout).
* `jat_scheduleWP0F`: FL4's `schedule` from `JAtZ` with `σ.domainTime ≠ 0 ∨
  NdOK s σ`, `FpuOwnOK σ` [J], `ArchSwF`/`ArchNdF` [P]: the spec outcome
  (`Fires`, `schedule σ1 = {σ'}`), SchedRel/NtfnStateRel/NSC/Inv/CurInv/
  ActIdle at `σ'`, `JAtZ` after the timers and FL4's writes from there in
  `KFootN` (SchedRel-level post: the J reconstruction at `σ'` across the
  `next_domain` words is the remaining step, KENTRY-PLAN.md sch5).
-/
import Fl4Proofs.P3.XTopJointSchedRF
import Fl4Proofs.P3.ScNextDomCF
import Fl4Proofs.P3.JEntryIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`NdOK` after FL4's TCB timers** (module docstring). -/
theorem JAtZ.ndOK_fire {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hNd : NdOK (L := L) s σ) {s1 : S}
    (hf : P1.FootD st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1)
    (hF : Fires σ σ1) : NdOK (L := L) s1 σ1 := by
  have hkf := J.kern.ksbFit
  have hka := J.kern.ksbAl
  have hks := J.kern.hks
  have hH := J.kern.heap
  have hKW := J.kwApartJ (s' := s) rfl (fun c hc => J.blk.2.2.1.2.2.tm.npl c hc)
  obtain ⟨hdl, hdi, hds⟩ := fires_dom hF
  refine hNd.keep hf.1 (fun o ho h8 => hf.mem_eq (ksW_al hkf hka ho h8) fun hb => ?_) hdl hdi hds
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hb with hb | hb
  · rcases hKW _ (ksW_al hkf hka ho h8) hb with e | e <;> rw [hv] at e <;> omega
  · rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dnA y).val = y.val + 3576 := by
        unfold P1.dnA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dpA y).val = y.val + 3584 := by
        unfold P1.dpA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hnv := P1.nodeAt_val (J.blk.2.2.1.2.2.tm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp)
      unfold P1.LawfulStore.nodeBase at hnv
      have := congrArg UScalar.val e
      rw [hv, hnv] at this
      simp [layout.node.DEBUG_TCBS] at this
      omega


set_option maxHeartbeats 2000000 in
/-- **FL4's `schedule` from `JAtZ`, with the domain switch, up to the FPU**
(module docstring): no `σ.domainTime ≠ 0`; instead `σ.domainTime ≠ 0 ∨
NdOK s σ` (NdOK's [J] facts at the entry), `ArchNdF` [P] and `FpuOwnOK σ`
[J] at the entry. -/
theorem jat_scheduleWP0F {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI) (hSig : SignalJHyp (L := L) arI AR H Cs)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem r.1) σ' ∧ NSC Z.N Z.C σ' ∧ Inv σ' ∧
      CurInv σ' ∧ ActIdle σ' ∧ ∃ rf : S × A,
        ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 rf.1 rf.2 σ1) ∧
          timer.fire st arI s a = ok rf ∧ L.ksb rf.1 = L.ksb s ∧ FpuOwnOK σ1) ∧
        P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) ∧
        ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1 → RunW σ3) ∧
          Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hfire : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW0 Z.T Z.C σ1 ∧
      ((σ1.domainTime ≠ 0 ∨ NdOK (L := L) r.1 σ1) ∧
        (∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb r.1).val ∨ (L.ksb r.1).val + 13568 ≤ n.val) ∧
        ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 r.1 r.2 σ1) ∧
          timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s ∧ FpuOwnOK σ1)) ⦄ := by
    refine WP.spec_mono (P1.spec_eq' (WP.spec_and (J.fireJ hSig) (P1.timer.fire.kw hAT hNt s a hB))) ?_
    rintro ⟨s1, a1⟩ ⟨hf, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩
    simp only [WP.uncurry'_pair] at hk
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, ⟨J1.inv, J1.cur, J1.off, J1.act, J1.own⟩,
      hd.imp (fun h => by rw [hd1]; exact h) (fun h => J.ndOK_fire h hk h1), J1.nk,
      ⟨V1, Ac1, Lst1, D1, J1⟩, hf, hk.1, fpuOwnOK_fires J h1 J1.xtop.fin.1.1.2.2.1 hFO⟩
  exact schedule_refinesWP0F s a σ hS hR J.nsc hnd hfire (fun _ _ h => h.2.2.2) hA hAN hsni hsend hT

end

end

end Fl4Proofs.P3
