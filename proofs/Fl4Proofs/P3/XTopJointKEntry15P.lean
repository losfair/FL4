/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr5): **`kernel_entryJ15P`**,
XTopJointKEntry14P's `kernel_entryJ14P` without `KDispHyps13P.vmt` [J]
(mr4 NEXT (4)).

* `budget_vmt_at`: `ValidMachineTime` holds at every spec state the entry
  dispatches from (`BudgetAt σ σb true`), with no premise at the entry: the
  time stamp sets `curTime` to the clock value and the last machine time to
  the same value (`validMachineTime_gct`), and a `check_budget_restart` that
  answers `true` changes nothing (ScEntryRd's `checkBudgetRestart_true`: the
  timeout-fault path of `checkBudget` only runs on `false`).
* `KDispHypsKV K`: `KDispHypsK K` without its `vmt` field; `kernel_entryJ15P`
  takes it (the field from `budget_vmt_at`).
-/
import Fl4Proofs.P3.XTopJointKEntry14P
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **`ValidMachineTime` at the spec's budget outcome `true`** (module
docstring). -/
theorem budget_vmt_at (hnd : Fl4Spec.numDomains = 1) {σ0 σb : Fl4Spec.State Unit}
    (hmem : (true, σb) ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0).1) :
    ValidMachineTime σb := by
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hmem
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hb : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  rw [hb, e]
  exact ⟨(validMachineTime_gct σ0).1, (validMachineTime_gct σ0).2⟩

/-- `ValidMachineTime` at a dispatch state of the entry. -/
theorem BudgetAt.vmt (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (h : BudgetAt σ σb true) :
    ValidMachineTime σb := by
  obtain ⟨σ0, -, hb⟩ := h
  exact budget_vmt_at hnd hb

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises without `ValidMachineTime`** (`KDispHypsK` without
its `vmt` field: it is `BudgetAt.vmt`). -/
structure KDispHypsKV (K : capability.Cap → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp6 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The kernel entry with `ValidMachineTime` transported** (module
docstring): `kernel_entryJ14P` with `KDispHypsKV PreKind14` (no `vmt`). -/
theorem kernel_entryJ15P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV (L := L) arI PreKind14 AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ14P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      let h := hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J'
      ⟨h.inv, h.recv, h.mid, hBA.vmt hnd⟩)
    hFin hARI hA hnd hM hMK hPA hIA hmrt hmb hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
