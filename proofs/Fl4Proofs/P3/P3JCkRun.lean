/-
P3 (line p3J, gen 16): **every entry of every run from the root-thread witness `w1` / `σ1`**: U45nv's per-entry
path premise is exactly K6, at every state of the run, not only the first.

* **`RunCK s a σ := JReachU40 s a σ ∧ CKI σ`** (`CKI`: every slot's cap is no untyped, SchedControl,
  IRQ-control or arch cap; P3JCkW/X/S): the run invariant. `CKI` is kept by every spec kernel entry
  (`kentry_cki`, `kcall_cki`, and the FaultIP write by the `WLH` frame), `JReachU40` by U45nv itself.
* **`jPathAtMU44w_cki` / `kDispHypsKVU44w_cki`** (gen 15's `…_σ1` for any `CKI` state): at every passing-budget
  dispatch state `σb` of an entry from a `CKI` state `σ`, `KDispHypsKVU44w NK6` holds: the invoked cap is a
  slot cap of `σ` (`budgetAt_capOpt`), so it is no SchedControl (K1), Untyped (K3/K4) or Frame (K7) cap, and a
  thread cap off label `TCBSetEPTRoot` asks nothing. **`kDispHypsKVU44_cki_of_k6`**: there `KDispHypsKVU44` is
  its K6 part.
* **`kernel_entry_runCK`** (U45nv's globals, start `RunCK`): at a `RunCK` state, every entry clause of U45nv,
  with the syscall clause's `KDispHypsKVU44` premise replaced by **its K6 part only**
  (`KDispHypsKVU44w (¬ NK6 · ·)`: the current thread invoking a thread cap at label `TCBSetEPTRoot`, [scope]),
  ends in a `RunCK` state related to the spec outcome. The other per-entry antecedents are U45nv's case
  conditions, unchanged: non-idle current thread, `NativeSys` / `UserHw` / `VmfHw` / `IrqHw` / `UnkSys` /
  `NoDbgSys` / trap number, and the TRAP_SYSCALLS flag `hfl` (not an invariant: the root thread may set its
  own flag, JBootQ1Hfl's docstring; at `w1` it holds, `JBootQ.w1_hfl`).
* **`runCK_w1`** (`OpaqueWK` [P]): `RunCK` at the start `w1 / σ1`. **`kernel_entry_runCK_w1`**: the step theorem
  at the jboot platform, every global discharged except the opaque [P]s `OpaqueWK`, `FpuImplDet`,
  `FpuWriteDet`, `KCfgFL4` (as `u45nv_w1I1`). So, by induction along any run from `w1 / σ1` whose entries
  meet their case conditions, every state is `RunCK` and the only per-entry premise left is K6.

Named premises: none new. K6 [scope] remains as the syscall clause's antecedent (not discharged, not
weakened: the port has no TCB label 88, `specDec_ept_noOk`). No sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JCkS
import Fl4Proofs.P3.JBootQ1Hfl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- **`CKI` at the root-thread witness**: `σ1`'s caps are null or the root CNode / thread / SC caps. -/
theorem cki_σ1 : SInvCk.CKI σ1 := by
  intro p cref c hc
  have h1 := capAt1 (sl := (p, cref)) (c := c) (by rw [SInvUZ.capAt_capOpt]; exact hc)
  rcases h1 with e | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> subst e <;> first | trivial | simp [SInvCk.KW]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **Every invocation but K6 is covered at the dispatch states of an entry from a `CKI` state.** -/
theorem jPathAtMU44w_cki (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hC : SInvCk.CKI σ)
    (hb : BudgetAt σ σb true)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} :
    JPathAtMU44w (L := L) arI NK6 AR Z s ar σb ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU _ _ _ _ _ _ _ sl c e exs _ _ hgc _ _ _ _ hW
  have hcap : capOpt (σ.kheap sl.1) sl.2 = some (absCap c) := by
    rw [← budgetAt_capOpt hnd hb]
    obtain ⟨o, i⟩ := sl
    exact (getCap_set_iff σb o i (absCap c)).1 (congrArg Prod.fst hgc)
  have hk := hC _ _ _ hcap
  cases c
  all_goals first
    | (intro h; exact absurd h (hW _ rfl))
    | trivial
    | (exfalso; simp [absCap, SInvCk.KW] at hk; done)
    | (exfalso; revert hk; unfold absCap; split <;> simp [SInvCk.KW]; done)

theorem kDispHypsKVU44w_cki (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hC : SInvCk.CKI σ)
    (hb : BudgetAt σ σb true) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {n : I64} {c : Fl4Spec.Syscall} : KDispHypsKVU44w (L := L) arI NK6 AR Z H Cs D s a σb n c :=
  ⟨fun _ _ _ _ _ _ => jPathAtMU44w_cki hnd hC hb, fun _ _ _ _ _ _ => jPathAtMU44w_cki hnd hC hb⟩

/-- **At a `CKI` state's dispatch states `KDispHypsKVU44` is its K6 part.** -/
theorem kDispHypsKVU44_cki_of_k6 (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit}
    (hC : SInvCk.CKI σ) (hb : BudgetAt σ σb true) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs D : Set U64} {s : S} {a : A} {n : I64} {c : Fl4Spec.Syscall}
    (hK6 : KDispHypsKVU44w (L := L) arI (fun l c => ¬ NK6 l c) AR Z H Cs D s a σb n c) :
    KDispHypsKVU44 (L := L) arI AR Z H Cs D s a σb n c :=
  KDispHypsKVU44.of_w (kDispHypsKVU44w_cki hnd hC hb) hK6

end

/-! ## The run invariant -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The run invariant**: U40's joint reach and the cap-kind invariant. -/
def RunCK (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU40 (L := L) arI AR MR s a σ ∧ SInvCk.CKI σ

theorem cki_evOut {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (h : SInvCk.CKI σ)
    (he : EvOut fip ev σ σ') : SInvCk.CKI σ' := by
  cases fip with
  | false => exact SInvCk.kcall_cki true ev h _ he
  | true =>
    obtain ⟨w, hw, h2⟩ := he
    have hw' : SInvCk.CKI w.2 := SInvV.hv_fl4SyscallFaultIP (P := SInvCk.CKI) σ.curThread σ h _ hw
    exact SInvCk.kcall_cki true ev hw' _ h2

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_runCK`** (module docstring): U45nv from a `RunCK` state, the syscall clause's
`KDispHypsKVU44` premise narrowed to its K6 part, every clause ending in `RunCK`. -/
theorem kernel_entry_runCK [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4) (hNV : NoVirt arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunCK (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU44w (L := L) arI (fun l c => ¬ NK6 l c) AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RunCK (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RunCK (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RunCK (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RunCK (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RunCK (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RunCK (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨hJ, hC⟩ := hR
  obtain ⟨Z, H, Cs, Ac, Lst, D, hZ, -, -, -, -, -, -, -, -, hS, hI, hU, hV, hTr, hUn⟩ :=
    kernel_entry_reachU45nv arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap
      hFpu hFW hCfg hNV hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, hZ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hne hns hfl hK6
    refine WP.spec_mono (hS n c hne hns hfl fun σb hb V' Ac' Lst' D' s' a' hF hZ' =>
      kDispHypsKVU44_cki_of_k6 hnd hC hb (hK6 σb hb V' Ac' Lst' D' s' a' hF hZ')) ?_
    rintro r ⟨σ', h1, -, -, -, -, -, -, -, hJ'⟩
    exact ⟨σ', h1, hJ', SInvCk.kentry_cki true c hC _ h1⟩
  · intro w a1 hw
    refine WP.spec_mono (hI w a1 hw) ?_
    rintro r ⟨σ', h1, -, -, -, -, -, -, hJ'⟩
    exact ⟨σ', h1, hJ', cki_evOut hC h1⟩
  · intro n c hne hu
    refine WP.spec_mono (hU n c hne hu) ?_
    rintro r ⟨σ', h1, -, -, -, -, -, -, hJ'⟩
    exact ⟨σ', h1, hJ', cki_evOut hC h1⟩
  · intro ad c ft hne hv
    refine WP.spec_mono (hV ad c ft hne hv) ?_
    rintro r ⟨σ', h1, -, -, -, -, -, -, hJ'⟩
    exact ⟨σ', h1, hJ', cki_evOut hC h1⟩
  · intro v hne hv
    refine WP.spec_mono (hTr v hne hv) ?_
    rintro r ⟨ev, σ', he, h1, -, -, -, -, -, -, hJ'⟩
    exact ⟨ev, σ', he, h1, hJ', cki_evOut hC h1⟩
  · intro n hne hu hd
    refine WP.spec_mono (hUn n hne hu hd) ?_
    rintro r ⟨ev, σ', he, h1, -, -, -, -, -, -, hJ'⟩
    exact ⟨ev, σ', he, h1, hJ', cki_evOut hC h1⟩

end

/-- **`RunCK` at the start `w1 / σ1`** (`OpaqueWK` [P], as `u40_w1I1`). -/
theorem runCK_w1 (O : OpaqueWK) : RunCK (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨(u40_w1I1 O).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, cki_σ1⟩

/-- **`kernel_entry_runCK` at the jboot platform**: from any `RunCK` state (in particular `w1 / σ1`,
`runCK_w1`), under the global opaque [P]s `OpaqueWK`, `FpuImplDet`, `FpuWriteDet`, `KCfgFL4`. -/
theorem kernel_entry_runCK_w1 (O : OpaqueWK) (hFpu : Sched.FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4)
    {s : WSt} {a : Fl4Spec.MachineState} {σ : Fl4Spec.State Unit}
    (hR : RunCK (L := wL) warI1 wAR ipiMR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := wL) warI1 wAR Z H Cs Ac Lst D s a σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ := u40_w1I1 O
  obtain ⟨Z, H, Cs, Ac, Lst, D, hZ, -⟩ :=
    kernel_entry_runCK warI1 wAR ipiMR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hFpu hFW
      hCfg noVirt_warI1 hR
  exact ⟨Z, H, Cs, Ac, Lst, D, hZ⟩

end

end Fl4Proofs.P3.JBootQ
