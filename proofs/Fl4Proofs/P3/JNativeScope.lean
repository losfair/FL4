/-
P3 (line nscope, gen 1): **`NativeScope` (no TCB in `runningVM`) at every reachable joint state**, and the
current thread's state word `RESTART` / `RUNNING` there without a `NativeScope` premise.

`NativeScope` is not a field of `JAtZ` (nor derivable from it: `JExt.vw` zeroes every TCB's VCPU word, but no FL4-
or spec-side invariant inside `JAtZ` ties `TS_RUNNING_VM` to a bound VCPU; P1 does not track the VCPU word). It is
already carried, though, in the spec invariant `SInvX` that `kernel_entry_reachU29` exports beside its `JAtZ`: invA's
`SInvAll.SInvA.ns : SInv.NativeScopeS σ` (P3/SpecInvNativeScopeF1: every spec step keeps it, the spec never writes
`runningVM`; `SInv.nativeScopeS_iff` makes it IpcLeaves' `NativeScope` by `Iff.rfl`). So no new preservation
proof is needed: this module only projects it and packages it.

* **`SInvX.nativeScope`**: `SInvX σ → NativeScope σ` (`h.1.a.ns`).
* **`JAtZ.curRunR'`**: famw's `JAtZ.curRunR` with the `NativeScope` premise replaced by `SInvX σ` (the spec
  invariant carried at every reachable state); **`JAtZ.curRunRX`**: the same from `ct ≠ idle` (`SInvX.entered`
  gives `Entered`).
* **`kernel_entry_nativeScopeU29`**: same premises as `kernel_entry_domInvU29` (= `kernel_entry_reachU29`'s);
  at every `JReachU17` state, a `JAtZ` (the one `kernel_entry_reachU29` returns) together with `NativeScope σ`,
  the current thread's state word `TS_RESTART ∨ TS_RUNNING` under `Entered σ` and under `ct ≠ idle`, and, at the
  exit of each of the six entry kinds, `RJ ∧ NativeScope ∧ JReachU17` at the exit state.
* **`send_signal_topX`** (c): IpcLeaves' `send_signal_top` with `SInvX σ` for its `hvm : NativeScope σ`.

The IpcLeaves lemmas whose premise is `∀ s' σ', IRel … s' σ' → NativeScope σ'` (`send_tail_ntfn`,
`decode_notification_top`) are not discharged here: that premise quantifies over every `IRel` state, not only
reachable ones (the top chain already discharges them internally; `kernel_entry_reachU29` has no `NativeScope`
premise).

No new premise ([J]/[P]/[W]): every theorem's premises are those of the lemma it wraps. No existing statement
changed.
-/
import Fl4Proofs.P3.XTopJointDomInv29
import Fl4Proofs.P3.JCurRunR
import Fl4Proofs.P3.SpecInvNativeScopeBridge
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G4

/-- **`NativeScope` from the carried spec invariant** (`SInvA.ns`, invA). -/
theorem SInvX.nativeScope {σ : Fl4Spec.State Unit} (h : SInvX σ) : Fl4Proofs.P3.Endp.NativeScope σ :=
  (SInv.nativeScopeS_iff σ).1 h.1.a.ns

end Fl4Proofs.P3.SInvR.G4

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The current thread is `RESTART` or `RUNNING`** at an `Entered` joint state carrying `SInvX`
(`JAtZ.curRunR` with `SInvX.nativeScope`). -/
theorem JAtZ.curRunR' (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : Entered σ) :
    L.mem s (P1.stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (P1.stA (L.curW s)) = sched.TS_RUNNING :=
  J.curRunR hni hX.nativeScope

/-- **`JAtZ.curRunR'` from `ct ≠ idle`** (`SInvX.entered`). -/
theorem JAtZ.curRunRX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    L.mem s (P1.stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (P1.stA (L.curW s)) = sched.TS_RUNNING :=
  J.curRunR' hX (hX.entered hct)

end

section
variable {S : Type} {st : machine.Store S} {A : Type} {ar : machine.Arch A}
  {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`send_signal_top` at a state carrying `SInvX`** (its `hvm` by `SInvX.nativeScope`). -/
theorem send_signal_topX [P1.LawfulStore st]
    (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {n : U64} (hn : n ∈ N) (hS : SInvX σ) (badge : U64) :
    notification.send_signal st ar s a n badge ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, IRel st th cr N T C E R B c r.1 z.2 ⦄ :=
  send_signal_top hH hP s a σ hX hn hS.nativeScope badge

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`NativeScope` at every reachable joint state and every kernel exit** (module docstring): at a `JReachU17`
state, `kernel_entry_reachU29`'s `JAtZ` with `NativeScope σ` and the current thread's state word
`TS_RESTART ∨ TS_RUNNING` (under `Entered σ`, and under `ct ≠ idle`); at the exit of each entry kind, the exit
state's `RJ`, `NativeScope` and `JReachU17`. Same premises as `kernel_entry_domInvU29`. -/
theorem kernel_entry_nativeScopeU29 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ NativeScope σ ∧
      (Entered σ →
        L.mem s (P1.stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (P1.stA (L.curW s)) = sched.TS_RUNNING) ∧
      (σ.curThread ≠ σ.idleThread →
        L.mem s (P1.stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (P1.stA (L.curW s)) = sched.TS_RUNNING) ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧ NativeScope σ' ∧
          JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          NativeScope σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          NativeScope σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          NativeScope σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          NativeScope σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', RJ (L := L) arI AR r.1 r.2 σ' ∧
          NativeScope σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, -, -, -, -, -, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX.nativeScope, J.curRunR' hX, J.curRunRX hX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', -, hRJ, hX', -, -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hX'.nativeScope, hJR⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hX'.nativeScope, hJR⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hX'.nativeScope, hJR⟩
  · intro ad c ft hct hV hE
    refine WP.spec_mono (hVm ad c ft hct hV hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hX'.nativeScope, hJR⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', -, -, hRJ, hX', -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hX'.nativeScope, hJR⟩
  · intro n hct hU hND hE
    refine WP.spec_mono (hSU n hct hU hND hE) ?_
    rintro r ⟨ev, σ', -, -, hRJ, hX', -, -, -, -, hJR⟩
    exact ⟨σ', hRJ, hX'.nativeScope, hJR⟩

end

end

end Fl4Proofs.P3.SInvR.G5
