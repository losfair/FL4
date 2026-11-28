/-
P3 (line p3J, gen 2): **`kernel_entry_reachU36`** = `kernel_entry_reachU35` with the path premise
narrowed to the invoked slot.

**Why** (inventory K1 / K4, `WS/handoff/p3J.md`): `JPathAtMU30` asks its per-cap leaf at *every* slot of
every CNode of `Z.th`, with the entry's message. FL4's boot gives the root CNode one `SchedControl` cap
per node (`crates/fl4-core/src/boot.rs:639-642`), so on any boot with two or more nodes the leaf
`cpu = Z.c` (K1, `JSchedCPathU7.core`) fails at some slot on every core, and `JUtPathMU29.core0`
(`Z.c = 0`, K4) fails on every core but 0 as soon as an untyped cap exists anywhere: the invocation half of
U35's syscall clause was vacuous on SMP. `jPathAtMU30_schedControl` states the forcing.

**Change**: `KDispHypsKVU36` = `KDispHypsKVU35` with `JPathAtMU30` ↦ **`JPathAtMU35`** (P3JLook): one more
hypothesis `LookAt ct cptr σ sl c`, i.e. `sl` / `c` are the slot and cap the spec's `lookupCapAndSlot`
returns for the invoked `cptr` (with `capAt … (cslotAddr sl) = ok c`, FL4's read of the same slot;
`lookup_slot_refines` relates FL4's `cspace.lookup_slot` to it). The proof is P3JGen's kernel-checked
transport of U35's proof onto the narrowed premises (16 conversions, the refinement lemma's `hDec` and the
two consumers re-proved in P3JLook).

**Premise diff U35 → U36**: in the syscall clause `KDispHypsKVU35 …` ↦ `KDispHypsKVU36 …` (`JPathAtMU30` ↦
`JPathAtMU35`, weaker: `JPathAtMU30.toU35`). Every other premise and the conclusion verbatim. No new premise,
[W] 0. **`kernel_entry_reachU35_of36`** proves U35's statement, verbatim, from U36.

**Non-vacuity of the narrowing** (K1): `lookAt_unique` (one invoked slot per entry),
`lookAt_other` (no other slot satisfies `LookAt`), `JPathAtMU35.of_invoked` (the narrowed premise follows
from its instance at the invoked slot alone). So a `SchedControl {cpu}` cap with `cpu ≠ Z.c`, or an untyped
cap on a core ≠ 0, in a slot other than the invoked one no longer falsifies the premise; only invoking such
a cap does (K1 / K4 are then genuine [S] one-core premises about the invoked cap).

**Known false at these entries (not fixed here; the clause's scope)**, all VT-x [scope] leaves, now asked
only for the invoked cap:
* K6 / D1: a Thread cap invoked at label 88 (`TCBSetEPTRoot`) with no extra cap: FL4 `TruncatedMessage`
  (`crates/fl4-core/src/tcb.rs:410-411`), the ported spec `IllegalOperation`; with an EPT root cap FL4
  installs it (`tcb.rs:412-419`), the spec errs.
* K7: a frame cap invoked at label 60 (`X86PageMapEPT`): FL4 `ept::map_frame`
  (`crates/fl4-core/src/arch/x86_64/vspace.rs:495-496`) errs or maps with its own checks, the spec
  `IllegalOperation`.
* K3 / D2: `UntypedRetype` of an object type 14..18 with `virtualization() == 0`: FL4 `InvalidArgument 0`
  (`crates/fl4-core/src/untyped.rs:43`), the ported retype proceeds (Fl4Spec/Ext/VirtP3x §1).
At such entries `KDispHypsKVU36` / `JDecMRLK … VtxK …` are false and the clause says nothing.

Named premises still open (inherited, unchanged): [P] `JEntryAtR7V` (`ioapics`, `pins`, `map`, `mapr`);
`JPathAtMU35`'s leaves ([P]/[S] SchedControl `cpu = Z.c`, untyped `fan`, `core0`, `rcb` [P], `vtx` [scope],
Thread SetEPTRoot / EPT frame `JVtxScope` [scope]); [J]/[scope] `JDecMRLK … VtxK …`; [P] `KFinAtR13`; U34's
global [P] premises. No sorry.
-/
import Fl4Proofs.P3.P3JGen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-- **One invoked slot per entry**: `lookupCapAndSlot` has a single outcome. -/
theorem lookAt_unique {ct cptr : U64} {σ : Fl4Spec.State Unit} {sl sl' : Fl4Spec.CslotPtr} {c c' : capability.Cap}
    (h : LookAt ct cptr σ sl c) (h' : LookAt ct cptr σ sl' c') : sl' = sl ∧ absCap c' = absCap c := by
  unfold LookAt at h h'
  rw [h] at h'
  have e := Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h')
  have e2 := Except.ok.inj (Prod.mk.inj e).1
  exact ⟨(Prod.mk.inj e2).2.symm, (Prod.mk.inj e2).1.symm⟩

/-- **No other slot is the invoked one.** -/
theorem lookAt_other {ct cptr : U64} {σ : Fl4Spec.State Unit} {sl0 sl : Fl4Spec.CslotPtr} {c0 c : capability.Cap}
    (h0 : LookAt ct cptr σ sl0 c0) (hne : sl ≠ sl0) : ¬ LookAt ct cptr σ sl c :=
  fun h => hne (lookAt_unique h0 h).1

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKVU35` with `JPathAtMU35`** (the path premise at the invoked slot only). -/
structure KDispHypsKVU36 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU35.inv`, the path premise at the invoked slot (`JPathAtMU35`). -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU35.mid`, the path premise at the invoked slot (`JPathAtMU35`). -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- **The narrowed premise is weaker**: `JPathAtMU30` gives `JPathAtMU35` (drop `LookAt`). -/
theorem JPathAtMU30.toU35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU30 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 _ =>
    h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13

/-- **`JPathAtMU35` from its instance at the invoked slot alone** (non-vacuity of the narrowing): only the
slot `lookupCapAndSlot` returns is asked about; caps in other slots are unconstrained. -/
theorem JPathAtMU35.of_invoked {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    {sl0 : Fl4Spec.CslotPtr} {c0 : capability.Cap} (h0 : LookAt ct cptr σ sl0 c0)
    (hI : ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64)
      (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
      capAt (L.mem s) (cslotAddr sl0) = ok c → LookAt ct cptr σ sl0 c → Vs.NativeCap c →
      JPathMEU30 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) bl ic cd fp buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl0 exs buffer ct c) :
    JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU _ _ _ _ _ _ _ sl c e exs _ h9 _ _ _ h13 hL
  obtain ⟨rfl, -⟩ := lookAt_unique h0 hL
  exact hI info mi buf buffer r2 er argsU c e exs h9 hL h13

/-- `KDispHypsKVU36` as the transported record (P3JGen's copy of `KDispHypsKVU35`). -/
theorem KDispHypsKVU36.toJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c) :
    Fl4ProofsJ.P3.SInvR.G5.KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c :=
  Fl4ProofsJ.P3.SInvR.G5.KDispHypsKVU35.mk h.inv h.mid

/-- **`KDispHypsKVU35` gives `KDispHypsKVU36`** (`JPathAtMU30.toU35`). -/
theorem KDispHypsKVU35.toU36 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1, (h.inv ct call bl don hct hi).2.toU35⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1, (h.mid ct rg sr cr hct hm).2.toU35⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU36`** (module docstring): U35 with the path premise at the invoked slot only. -/
theorem kernel_entry_reachU36 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU34 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU36 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU35 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' => (hK σb hb V' Ac' Lst' D' s' a' hF J').toJ) hDL hFin


end

end

end Fl4Proofs.P3.SInvR.G5
