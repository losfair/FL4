/-
P3 (p3P): **`kernel_entry_reachU30`** = `kernel_entry_reachU29` without three [P] premises that
the extracted code and the other premises already determine (p3P premise audit of U29).

* **Removed (b):** `hPA.minBudget` (`PPPlatA`; now `TimeAgree.mb hT`: the top takes only `hPAi`, the
  `irqAR` half), `JSchedCtxPathU7.arch` and `JSchedCPathU7.arch` (the SchedContext / SchedControl
  decodes keep `AR`: an `ARKeep` walk, `AK.schedcontext_*`, `decode_sched_context_keepAR`,
  `decode_sched_control_keepAR`; `JPathMEU30`, `JPathAtMU30`, `KDispHypsKVU30`, `.toU29`).
* **Added:** none. [J] 0, [W] 0. Every other premise is `kernel_entry_reachU29`'s, verbatim.
* `set_option maxHeartbeats 4000000` only at `AK.schedcontext_configure_flags` (as MachKeepG4d's
  `MKD.schedcontext_configure_flags`; the default times out at `whnf`).
* **Finding (c):** `JEntryAtR7.stall` (∀ q) is false at states with a user-frame pattern
  (`StallFinding`, `stall_false`); kept, to be narrowed to `∀ q ∈ Z.T`.

## Premise table of `kernel_entry_reachU29` (p3P)

Classes: (a) a hardware / platform / boot / configuration fact outside fl4-core (kept);
(b) determined by fl4-core's extracted code, Fl4Spec or the other premises (proved here);
(c) false at reachable states (finding, kept, evidence in `StallFinding`).
"Opaque" = an l4v `consts` / unconstrained constant, ported as a Lean `opaque`: no Lean proof can
fix its value, so a premise about it can only be (a).

**Theorem premises of `kernel_entry_reachU29`** (in statement order)

| # | premise | statement (short) | used by | class |
|---|---|---|---|---|
| 1 | `[PlainStore st]` | `st.frame_masks s = ok (0, 0)` (no frame sharing) | P1 page / untyped refinements | (a) store platform |
| 2 | `hARI : ARIface arI AR` [P] | `ARKeep` (now, set_deadline, send_reschedule, remote_stall, fpu_*, vcpu_barrier, vcpu_release keep the CR3 relation) + `mask` (`ArchIrqStep` keeps it) | every IPC / sched / IRQ path (`AK.*`) | (a) arch backend |
| 3 | `hA : P0.ArchTotal arI` | every arch op returns `ok` | P0 totality everywhere | (a) arch backend |
| 4 | `hnd : numDomains = 1` [P] | the opaque `kernelConfig.numDomains` is FL4's 1 | domain / scheduler refinement | (a) config (opaque) |
| 5 | `hM : MachPlat arI MR` [P] | now / irq_pending / take_pending_irq / mask_irq / ack_irq are the spec machine ops under `MR`; `MR` reads 4 fields | timer, IRQ, preemption | (a) platform |
| 6 | `hKD : MRKeepD arI MR` [P] | finalisation's arch ops keep `MR` | deletion, TDX, frame ops | (a) arch backend (`arI`, `MR` abstract) |
| 7 | `hIo : MRKeepIo arI MR` [S] | `port_in` / `port_out` keep `MR` | IO port decode (`MKD.decode_ioport`) | (a): `arI` and `MR` are parameters; nothing in fl4-core or Fl4Spec says what `port_in` does to the arch state |
| 8 | `hIoa : MRKeepIoapic arI MR` [P] | `ioapic_map(_remapped)` keep `MR` | IRQ control decode | (a) as 7 |
| 9a | `hPA.irqAR` [P] | `irq_pending` keeps `AR` | preemption points | (a) arch backend |
| 9b | `hPA.minBudget` [P] | `sporadic.min_budget arI a` returns `MIN_BUDGET` | StPost*Top `hmb`, sched decodes | **(b) proved**: `TimeAgree.mb hT` (fl4-core's `min_budget = 2 * kernel_wcet_ticks` + `hT.kernelWcet`) |
| 10 | `hIA : IrqPlatA arI AR` [P] | take_pending_irq / ack_irq keep `AR`; no IPI vector 126/127 | interrupt entry | (a) platform |
| 11 | `hT : TimeAgree arI` [P] | max_period_us / us_to_ticks / kernel_wcet_ticks agree with the opaque `timeConsts`; `kernelWCETUs = 10`; `timerUnit = 1` | sched-context decodes, refills | (a) platform + config (opaque) |
| 12 | `hmax : maxTicksToUs = U64.MAX` [P] | opaque l4v `max_ticks_to_us` | `SchedContext.consumed`, YieldTo | (a) config (opaque) |
| 13 | `htu` [P] | `ticks_to_us` is the spec's `ticksToUs` | as 12 | (a) arch backend |
| 14 | `hRef : ArchRefines arI AR` [P] | set_vspace / invalidations against CR3 | VSpace ops, schedule's CR3 | (a) arch backend |
| 15 | `hPI : PortInValMR arI MR` [P] | `port_in`'s value is an outcome of the opaque `in8/16/32Impl` + `in*Val` at an `MR` state | IO port `In` reply | (a): the spec side is opaque (`in8Impl`, `in8Val`), the FL4 side is the abstract `arI.port_in` |
| 16 | `hSX : P1.StoreExt st` [P] | two stores with the same aligned words, ksb, cpu are equal | `MemResp` of every post | (a) store platform |
| 17 | `hDR : SetDlDetR MR` [P] | the opaque `setDeadlineImpl d` has ≤ 1 outcome at an `MR` state | `setNextInterrupt` singleton (`setDlDet_of`) | (a): `setDeadlineImpl` is opaque (l4v `consts'`); `MR` does not read `machineStateRest` (`MachPlat.frame`), so this is exactly the state-free `SetDlDet`, not derivable and not refutable |
| 18 | `hJ : JReachU17` | reachability from a start `JAtZ` state | the induction | not a premise tag (start-state facts as BndS / JPlaced / VsNamed) |

**Per-entry hypotheses of the clauses** (supplied by the caller at each entry)

| # | where | premise | class |
|---|---|---|---|
| E1 | every clause | `σ.curThread ≠ σ.idleThread` [S] | (a) event scope |
| E2 | syscall | `NativeSys n c`, `TRAP_SYSCALLS` clear after the FaultIP write [S] | (a) event scope |
| E3 | `KDispHypsKVU29.inv/mid` → `JEntryAtR7.stall` [P] | `∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)` | **(c) false** at states with a user-frame pattern (see `StallFinding`); kept |
| E4 | `JEntryAtR7.ioapics` [P] | `num_ioapics` is the spec's `x64NumIoapics` | (a) platform |
| E5 | `JEntryAtR7.archIrq` [P] | `ArchIrqRel` (IOAPIC pins, routed maps) | (a) platform |
| E6 | `JPathMEU29` SchedContext → `JSchedCtxPathU7.arch` [P] | the decode keeps `AR` | **(b) proved**: `decode_sched_context_keepAR` (ARKeep walk of `schedcontext.decode`) |
| E7 | SchedControl → `JSchedCPathU7.arch` [P] | the decode keeps `AR` | **(b) proved**: `decode_sched_control_keepAR` |
| E8 | SchedControl → `JSchedCPathU7.core` [P]/[S] | `cpu = Z.c` | (a) one-core scope (a valid cap may name another core) |
| E9 | RAM / device Untyped → `fan` [P] | opaque `retypeFanOutLimit = 256` | (a) config (opaque) |
| E10 | Untyped → `rcb` [P] | opaque `resetChunkBits = 16` | (a) config (opaque) |
| E11 | Untyped → `core0` [P] | `Z.c = 0` | (a) one-core scope |
| E12 | Untyped / Thread SetEPTRoot / IoPort z≠0 / EPT frame / Vcpu / Ept → `JVtxScope`, `JDecMRLK VtxK` | [scope] VT-x | (a) scope |
| E13 | finish `KFinAtR13.arch` = `ArchSwF` [P] | FL4 `set_vm_root` / `set_kernel_vm_root` refine `archSwitchTo(Idle)Thread` with one outcome | (a): needs one outcome of opaque `writeCR3Impl` / FPU machine ops (the FL4 half is fl4-core and would be provable given that; splitting it is follow-up) |
| E14 | finish `KFinAtR13.archNd` = `ArchNdF` [P] | the spec's `archPrepareNextDomain` has one outcome | (a): opaque `enableFpuImpl` / `disableFpuImpl` / FPU read |
| E15 | interrupt | `IrqHw` [P] | (a) hardware vector |
| E16 | user exception | `UserHw n c` [P] (`n < 2^32`, `c < 2^28`) | (a) x86 hardware |
| E17 | VM fault | `VmfHw` [P] (cr2 = opaque `getFaultAddressVal`, error code) | (a) hardware |
| E18 | trap | `v < 256` | (a) hardware |
| E19 | unknown syscall | `UnkSys` [S], `NoDbgSys` [S] | (a) event scope |
-/
import Fl4Proofs.P3.XTopJointKEntryU29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-! ## The SchedContext / SchedControl decodes keep `AR` (`ARKeep` walk) -/

section
variable {S A C : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) {c : C}
include hS hA hK
set_option linter.unusedSectionVars false

theorem AK.schedcontext_complete_yield_to {s : S} {a : A} {yielder : obj.Tcb} (h : AR a c) :
    schedcontext.complete_yield_to st arI s a yielder ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.complete_yield_to; ak_walk

theorem AK.schedcontext_unbind_all_tcbs {s : S} {a : A} {sc : obj.Sc} (h : AR a c) :
    schedcontext.unbind_all_tcbs st arI s a sc ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.unbind_all_tcbs; ak_walk

-- 4000000: the same walk as MachKeepG4d's `MKD.schedcontext_configure_flags`, which sets it too; the default
-- (200000) times out at `whnf` in this walk.
set_option maxHeartbeats 4000000 in
theorem AK.schedcontext_configure_flags {s : S} {a : A} {target : obj.Sc} {cpu budget period max_refills badge flags : Std.U64}
    (h : AR a c) :
    schedcontext.configure_flags st arI s a target cpu budget period max_refills badge flags ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.configure_flags; ak_walk

theorem AK.schedcontext_yield_to {s : S} {a : A} {sc : obj.Sc} {call : Bool} (h : AR a c) :
    schedcontext.yield_to st arI s a sc call ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.yield_to; ak_walk

theorem AK.schedcontext_decode {s : S} {a : A} {lbl : Std.U64} {sc : obj.Sc} {call : Bool}
    {extra : Array obj.Slot 3#usize} (h : AR a c) :
    schedcontext.decode st arI s a lbl sc call extra ⦃ r => AR r.2.2 c ⦄ := by
  unfold schedcontext.decode; ak_walk

theorem AK.schedcontext_decode_sched_control {s : S} {a : A} {lbl cpu length buf : Std.U64}
    {extra : Array obj.Slot 3#usize} (h : AR a c) :
    schedcontext.decode_sched_control st arI s a lbl cpu length buf extra ⦃ r => AR r.2.2 c ⦄ := by
  unfold schedcontext.decode_sched_control; ak_walk

theorem AK.decode_sched_context {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {p sb : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedContext p sb) blk call don fp buf extra ⦃ r =>
      AR r.2.2 c ⦄ := by
  unfold syscall.decode_invocation; ak_walk

theorem AK.decode_sched_control {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {cpu : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra ⦃ r =>
      AR r.2.2 c ⦄ := by
  unfold syscall.decode_invocation; ak_walk

end

section
variable {S A C : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A} {AR : A → C → Prop}

/-- A total program whose post holds at every `c` with `AR a c`: the post with `∀ c` inside. -/
theorem spec_forall_AR {α : Type} {m : Result (α × S × A)} {a : A} (h0 : m ⦃ _ => True ⦄)
    (h : ∀ c, AR a c → m ⦃ r => AR r.2.2 c ⦄) : m ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄ := by
  cases hm : m with
  | ret r =>
    rw [WP.spec_ok]; intro c hc
    have h1 := h c hc
    rw [hm, WP.spec_ok] at h1; exact h1
  | _ => rw [hm] at h0; simp [WP.spec_vis, WP.spec_div] at h0

/-- **`JSchedCtxPath.arch` from `ARKeep`** (C type generic). -/
theorem decode_sched_context_keepAR (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) {s : S}
    {a : A} {lbl length : Std.U64} {slot : obj.Slot} {p sb : Std.U64} {blk call don fp : Bool} {buf : Std.U64}
    {extra : Array obj.Slot 3#usize} :
    syscall.decode_invocation st arI s a lbl length slot (.SchedContext p sb) blk call don fp buf extra ⦃ r =>
      ∀ c, AR a c → AR r.2.2 c ⦄ :=
  spec_forall_AR (P0.syscall.decode_invocation.p0 st arI s a lbl length slot _ blk call don fp buf extra hS hA)
    (fun _ hc => AK.decode_sched_context hS hA hK hc)

/-- **`JSchedCPath.arch` from `ARKeep`**. -/
theorem decode_sched_control_keepAR (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) {s : S}
    {a : A} {lbl length : Std.U64} {slot : obj.Slot} {cpu : Std.U64} {blk call don fp : Bool} {buf : Std.U64}
    {extra : Array obj.Slot 3#usize} :
    syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra ⦃ r =>
      ∀ c, AR a c → AR r.2.2 c ⦄ :=
  spec_forall_AR (P0.syscall.decode_invocation.p0 st arI s a lbl length slot _ blk call don fp buf extra hS hA)
    (fun _ hc => AK.decode_sched_control hS hA hK hc)

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JPathMEU29` without the two scheduler decodes' `arch` fields** (proved from `ARKeep`:
`decode_sched_context_keepAR`, `decode_sched_control_keepAR`). A SchedContext cap asks nothing; a
SchedControl cap asks only `JSchedCPathU7.core` ([P]/[S] one core: the cap's core is the sets'). -/
def JPathMEU30 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .SchedContext _ _ => True
  | .SchedControl cpu => cpu = Z.c
  | c => JPathMEU29 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c

/-- **`JPathAtMU29` with `JPathMEU30`.** -/
def JPathAtMU30 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (ct : U64) (is_call blocking can_donate first_phase : Bool) (cptr : U64) : Prop :=
  ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
    msg.msg_info st s ct = ok info →
    Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False) →
    msg.lookup_ipc_buffer st s false ct = ok buf →
    Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False) →
    ipc.lookup_extra_caps st s ct buf info = ok r2 →
    (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False) →
    Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False) →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok c → Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) →
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c →
      JPathMEU30 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU29` with `JPathAtMU30`** (the SchedContext / SchedControl `arch` fields proved). -/
structure KDispHypsKVU30 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7 (st := st) arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7 (st := st) arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JPathAtMU30.toU29 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (hA : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (h : JPathAtMU30 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU29 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  cases c
  case SchedContext p sb =>
    exact fun _ => JSchedCtxPathU7.mk (decode_sched_context_keepAR P1.LawfulStore.total hA hK)
  case SchedControl cpu =>
    exact JSchedCPathU7.mk hP (decode_sched_control_keepAR P1.LawfulStore.total hA hK)
  all_goals exact hP

theorem KDispHypsKVU30.toU29 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hA : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (h : KDispHypsKVU30 (L := L) arI AR Z H Cs D s a σ n c) : KDispHypsKVU29 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi; ⟨e, p.toU29 hA hK⟩,
    fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm; ⟨e, p.toU29 hA hK⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`kernel_entry_reachU29` without `PPPlatA.minBudget`, `JSchedCPathU7.arch`, `JSchedCtxPathU7.arch`** (module
docstring). -/
theorem kernel_entry_reachU30 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU30 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄)  := by
  have hPA : PPPlatA arI AR := ⟨hPAi, hT.mb⟩
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU29 hA hARI.toARKeep) hDL hFin,
    hIrq, hUs, hVm, hTr, hSU⟩

end

end

end Fl4Proofs.P3.SInvR.G5
