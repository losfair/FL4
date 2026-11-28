/-
P3 (line p3J, gen 12): **`kernel_entry_reachU44`** = `kernel_entry_reachU43` with the per-entry config
fields K2 `fan` / K5 `rcb` removed (one global [P] `KCfgFL4` instead), and the syscall clause's path record
restated as exactly what is left of it: scope facts about the invoked cap only.

* Config (K2 / K5). Fl4Spec's `kernelConfig` is `opaque` (Machine.lean; l4v's generated `Kernel_Config`,
  `Kernel_Config_Lemmas` says nothing about these two fields), so `retypeFanOutLimit = 256#64` and
  `resetChunkBits = 16` are not provable from the port; FL4's values are the extracted
  `untyped.RETYPE_FAN_OUT_LIMIT` / `untyped.RESET_CHUNK_BITS`. **`KCfgFL4`** [P] (module KCfgFL4) states the
  spec's two constants are those (global; it mentions no state, joint set or entry, so asking it per entry,
  as every untyped leaf of `JPathAtMU35` did, asked one constant fact again; `kCfgFL4_consistent`).
* `JPathMEU44` (cap-by-cap, unfolding `JPathMEU30` → `JPathMEU29` → `JPathMEU12` → `JPathMEU7` → `JPathMEU4`
  → `JPathME6` → `JPathME` → `JPathM`): every leaf of `JPathMEU30` that is not `True` at a native cap, and
  nothing else:
  - SchedControl `cpu`: **K1** `cpu = Z.c` [S] (the invoked SchedControl cap names the current core;
    false for a cross-core `SchedControl` invocation, which the refinement does not cover; since U36 only at
    the invoked slot, so no SMP vacuity);
  - Untyped (RAM or device): **K3** `vtx` [scope] (VT-x object types 14..18: `JVtxScope`) and **K4** `core0`
    [S] (`Z.c = 0`: untyped invocations on the boot core only; since U36 only when the invoked cap is an
    untyped, so not vacuous on cores ≠ 0 that invoke other caps);
  - Thread at `TCBSetEPTRoot` (**K6**) and Frame with the EPT flag or at `X86PageMapEPT` (**K7**): `JVtxScope`
    [scope];
  - every other native cap: `True` (IO ports with a VT-x owner, VCPUs and EPT caps are not native,
    `NativeCap`).
  `JPathMEU44.toU30 (KCfgFL4) (NativeCap c)` re-adds `fan` / `rcb` and the non-native leaves;
  `JPathMEU30.toU44` drops them (no premise).
* `JPathAtMU44` / **`KDispHypsKVU44`**: `JPathAtMU35` / `KDispHypsKVU39` on `JPathMEU44` (same quantifier
  prefix, `LookAt` at the invoked slot). So the syscall clause's remaining path premise carries no [J] or
  [P] fact any more: only [S] K1 / K4 and [scope] K3 / K6 / K7, all about the invoked cap.
  `KDispHypsKVU44.toU39 (KCfgFL4)`, `KDispHypsKVU39.toU44`.

**Premise diff U43 → U44** (checked with diff): + `(hCfg : KCfgFL4)` [P] (global) after `hFW`; syscall clause
`KDispHypsKVU39 …` ↦ `KDispHypsKVU44 …` (K2 / K5 removed in `inv` and `mid`, the leaves restated). Start
(`JReachU40`), `JDecMRLK` and the conclusion verbatim. [W] 0.
**`kernel_entry_reachU43_of44`**: U43's statement verbatim plus `hCfg : KCfgFL4` (U43's premises do not give
it: `kernelConfig` is opaque and U43 asks the two equations only at untyped invocations), as gen 11's
`kernel_entry_reachU42_of43` + `hFW`.

K1 / K4 are kept as they are (gen 2 narrowed them to the invoked cap; they are honest single-core scope
statements about FL4's refinement coverage, not facts the chain could prove: a `SchedControl {cpu ≠ Z.c}`
or an untyped invoked on a core ≠ 0 is reachable on an SMP boot (`boot.rs:639-642` hands the root task one
SchedControl cap per node and its untypeds), and the refinement proofs (`decode_invocation_sched_controlJ`,
`UtResetTopJ`'s `hc0`) are stated for that case only). Not narrowed here: `JDecMRLK … VtxK …` (D1 / D2, the
MR-keeping of the VT-x decodes; module XTopJointKEntry40), unchanged.

Named premises: U43's (XTopJointKEntryU43) minus the per-entry `fan` / `rcb` [P], plus `KCfgFL4` [P]
(global, opaque configuration). Per entry: `KDispHypsKVU44` ([S] K1 / K4, [scope] K3 / K6 / K7) and
`JDecMRLK` [J]. No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU43
import Fl4Proofs.P3.KCfgFL4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **What `JPathMEU30` still asks of a native cap** (module docstring): K1 [S], K3 / K4 / K6 / K7
([scope] / [S]); `fan` / `rcb` are `KCfgFL4`, every other leaf is `True`. -/
def JPathMEU44 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .SchedControl cpu => cpu = Z.c
  | .Untyped p sb fi dev =>
      (∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
        JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi dev) blk call don fp buf extra slbl argsU ci sl
          excaps buffer ct) ∧
      Z.c = 0#u64
  | .Thread p =>
      lbl = fl4_abi.label.TCBSetEPTRoot →
        JVtxScope (L := L) arI AR s ar σ lbl length (.Thread p) blk call don fp buf extra slbl argsU ci sl excaps buffer
          ct
  | .Frame p sz rt d m ep asid va =>
      ep = true ∨ lbl = fl4_abi.label.X86PageMapEPT → JVtxScope (L := L) arI AR s ar σ lbl length
        (.Frame p sz rt d m ep asid va) blk call don fp buf extra slbl argsU ci sl excaps buffer ct
  | _ => True

/-- **`JPathAtMU35` on `JPathMEU44`.** -/
def JPathAtMU44 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A)
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
      r2 = .Ok e → er = .ok exs → Vs.NativeCap c → LookAt ct cptr σ sl c →
      JPathMEU44 (L := L) arI AR Z s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU39` on `JPathAtMU44`** (module docstring): scope facts about the invoked cap only. -/
structure KDispHypsKVU44 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [S] K1 / K4, [scope] K3 / K6 / K7 at the invoked cap of the invoking syscalls (`KDispHypsKVU39.inv`
  without `fan` / `rcb`). -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JPathAtMU44 (L := L) arI AR Z s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [S] / [scope] the same at the invoked cap of the mid syscalls (`KDispHypsKVU39.mid`). -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JPathAtMU44 (L := L) arI AR Z s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- **`JPathMEU44` gives `JPathMEU30`** at a native cap, under `KCfgFL4`. -/
theorem JPathMEU44.toU30 (hC : KCfgFL4) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64}
    {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    {ct : U64} {c : capability.Cap} (hN : Vs.NativeCap c)
    (h : JPathMEU44 (L := L) arI AR Z s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c) :
    JPathMEU30 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c := by
  cases c
  case SchedControl cpu => exact h
  case Thread p => exact h
  case Frame p sz rt d m ep asid va => exact h
  case Untyped p sb fi dev =>
    obtain ⟨hv, hc⟩ := h
    cases dev
    · exact ⟨fun hf => Bool.noConfusion hf, fun _ => ⟨hC.fan', hv, hc, hC.rcb'⟩⟩
    · exact ⟨fun _ => ⟨hC.fan', hv, hc, hC.rcb'⟩, fun hf => Bool.noConfusion hf⟩
  case IoPort f l z => exact fun hz => (hz hN).elim
  case Vcpu p => exact hN.elim
  case Ept p l m asid va => exact hN.elim
  all_goals exact trivial

/-- **`JPathMEU30` gives `JPathMEU44`** (the `fan` / `rcb` and non-native leaves dropped). -/
theorem JPathMEU30.toU44 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64}
    {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    {ct : U64} {c : capability.Cap}
    (h : JPathMEU30 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c) :
    JPathMEU44 (L := L) arI AR Z s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c := by
  cases c
  case SchedControl cpu => exact h
  case Thread p => exact h
  case Frame p sz rt d m ep asid va => exact h
  case Untyped p sb fi dev =>
    obtain ⟨h1, h2⟩ := h
    cases dev
    · exact ⟨(h2 rfl).vtx, (h2 rfl).core0⟩
    · exact ⟨(h1 rfl).vtx, (h1 rfl).core0⟩
  all_goals exact trivial

/-- **`JPathAtMU44` gives `JPathAtMU35`** under `KCfgFL4`. -/
theorem JPathAtMU44.toU35 (hC : KCfgFL4) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64}
    {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU44 (L := L) arI AR Z s ar σ ct ic bl cd fp cptr) :
    JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL =>
    JPathMEU44.toU30 hC h13 (h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL)

/-- **`JPathAtMU35` gives `JPathAtMU44`.** -/
theorem JPathAtMU35.toU44 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64}
    {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU44 (L := L) arI AR Z s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL =>
    JPathMEU30.toU44 (h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 hL)

/-- **`KDispHypsKVU44` gives `KDispHypsKVU39`** under `KCfgFL4`. -/
theorem KDispHypsKVU44.toU39 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU44 (L := L) arI AR Z H Cs D s a σ n c) (hC : KCfgFL4) :
    KDispHypsKVU39 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => (h.inv ct call bl don hct hi).toU35 hC,
   fun ct rg sr cr hct hm => (h.mid ct rg sr cr hct hm).toU35 hC⟩

/-- **`KDispHypsKVU39` gives `KDispHypsKVU44`** (fields dropped). -/
theorem KDispHypsKVU39.toU44 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU39 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU44 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => (h.inv ct call bl don hct hi).toU44,
   fun ct rg sr cr hct hm => (h.mid ct rg sr cr hct hm).toU44⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU44`** (module docstring). -/
theorem kernel_entry_reachU44 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU40 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU44 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU43 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hFW hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, hIrq, hUs, hVm, hTr, hSU⟩
  intro n c hct hn hfl hK hDL
  exact hSys n c hct hn hfl (fun σb hB V' Ac' Lst' D' s' a' hF hJ' => (hK σb hB V' Ac' Lst' D' s' a' hF hJ').toU39 hCfg) hDL


end

end

end Fl4Proofs.P3.SInvR.G5
