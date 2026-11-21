/-
P3 (DESIGN.md §9), invariant line g5a (KENTRY-PLAN g5a; INV-PLAN §1.3 E4–E10,
§2, §4 G2 / G3): **`kernel_entryJ35E`** = `kernel_entryJ35` whose dispatch
bundle no longer asks five of `JEntryAtR3`'s seven joint fields.

At the dispatch state σb `hK` has `J' : JAtZ … σb` in hand. From it:
* `fnz` (`FrNZ`, no non-device frame cap at 0) is a theorem of `J'`
  (`JAtZ.fnzJ`): every non-device frame cap's bytes are in user frames
  (`JAtZ.fcap`), a user frame at 0 would be a spec arch object at 0, hence an
  object of `H` at 0 (`SpecCover.arch`), and `H 0 = none` (`JKern.h0`).
* `utks` (`UtNodesJ`, the RAM untyped regions miss the 64 cores' nodes) is a
  theorem of `J'` (`JAtZ.utksJ`): `UtKsApart`'s third part (ScPlaceUt) now
  asks the whole static area `[ksb+13568, ksb+304384)` (all 64 nodes and the
  ASID table), so `JAtZ.jcov.ks` gives it. The strengthened part is carried
  exactly as before (`UtKsApart.keep`, the retype's sub-range `omega`).
* `handlers`, `ports`, `urz` are FL4 readings of spec facts: with `StateRel`,
  `MdbLinks`, `IrqRel` / `IoRel` of `J'.xtop` each follows from a spec-only
  invariant (SpecInvG5: `SpecIrqH`, `SpecIoP`, `SpecUtZ`; l4v
  `valid_irq_handlers`, `valid_ioports`, `untyped_ranges_zero`): `JAtZ.handlersJ`,
  `JAtZ.portsJ` (IntInv's `handlersActive_of_spec` / `ioPortsAlloc_of_spec`)
  and `JAtZ.urzJ`. They are asked once, at the entry state σ (`hI : SInvI σ`),
  and carried to σb by `sinvI_disp` (the FaultIP write keeps every cap, the
  time stamp keeps the interrupt states, the IO ports and the memory).
* the Thread path's `hFr` (`JThreadPath`, ReadFPU's destination frame,
  KENTRY-PLAN g4a P1) is a theorem of `J'` (`JAtZ.fpuFrameJ`, from `fcap`
  since g5b; g5a used the spec-only `SpecFrPg`, now unused here):
  the dispatch bundle asks `JPathAtM35E` (`JPathME`: `JPathM` without
  `JThreadPath`), `JPathAtM35E.to35`.
Left in the dispatch bundle (`JEntryAtR5`): `stall`, `ioapics`, `archIrq`
[P] and the two genuinely joint fields `flags` (`FlagsRel`) and `vsTyp`
(`OffTabOK`) [J] (KENTRY-PLAN g5a: why they are not `JExt` fields yet).
-/
import Fl4Proofs.P3.XTopJointKEntry35
import Fl4Proofs.P3.SpecInvG5
import Fl4Proofs.P3.IntInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5

noncomputable section

/-! ## The five fields from `JAtZ` (and the spec-only bundle) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **No non-device frame cap at 0** (module docstring; INV-PLAN E16 (a)). -/
theorem JAtZ.fnzJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : FrNZ Z.th (L.mem s) := by
  intro y hy q sz r m e v w hc hq
  subst hq
  have h := J.fcap y hy
  rw [hc] at h
  obtain ⟨sz', hk⟩ := h rfl 0 (by simp) (by positivity)
  have e0 : ∀ m : BitVec 64, BitVec.ofNat 64 0 &&& m = 0 := fun m => by simp
  rw [e0] at hk
  obtain ⟨n, -, hH⟩ := J.cover.arch _ _ hk
  have h0 : H ⟨0⟩ = none := J.kern.h0
  rw [h0] at hH
  cases hH

/-- **`UtNodesJ` from `UtKsApart`** (its first and third parts). -/
theorem utNodesJ_of_ks {G : MdbGhost} (h : UtKsApart (L := L) G Cs s) : UtNodesJ (L.mem s) G (L.ksb s) := by
  intro x hx p sb fi hc
  obtain ⟨k1, -, k3⟩ := h x hx p sb fi hc
  unfold UtNodesAt
  omega

/-- **The RAM untyped regions miss every node** (INV-PLAN E18 (a), module docstring). -/
theorem JAtZ.utksJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : UtNodesJ (L.mem s) Z.G (L.ksb s) :=
  utNodesJ_of_ks J.jcov.ks

/-- **`HandlersActive` from the spec's `SpecIrqH`** (INV-PLAN E8). -/
theorem JAtZ.handlersJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hS : SpecIrqH σ) :
    HandlersActive (L.mem s) (L.ksb s) Z.G :=
  handlersActive_of_spec J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.2.1 J.xtop.fin.1.1.2.2.2.1 fun sl irq hg =>
    hS sl irq (SInvU.getCap_capAt (x := (_, σ)) (by rw [hg]; exact Set.mem_singleton _)).2

/-- **`IoPortsAlloc` from the spec's `SpecIoP`** (INV-PLAN E9). -/
theorem JAtZ.portsJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hS : SpecIoP σ) :
    IoPortsAlloc (L.mem s) (L.ksb s) Z.G :=
  ioPortsAlloc_of_spec J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.2.1 J.xtop.fin.1.1.2.2.2.2.1 fun sl f l hg =>
    hS sl f l (SInvU.getCap_capAt (x := (_, σ)) (by rw [hg]; exact Set.mem_singleton _)).2

/-- **`UtZero` from the spec's `SpecUtZ`** (INV-PLAN E17): an MDB slot's
non-device untyped cap is the spec's `untypedCap false p sb fi` there. -/
theorem JAtZ.urzJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hS : SpecUtZ σ) :
    UtZero (L.mem s) Z.G σ := by
  intro x hx p sb fi hc w h1 h2
  have hR := J.xtop.rel.2.1.1
  have hM := J.xtop.rel.2.1.2.2.1
  obtain ⟨ysl, hys, rfl⟩ := ((hM.members _).1 hx).1.abs
  obtain ⟨c, ac, hc', hca, hg⟩ := hR.abs_cap hys
  rw [capV_of_capAt hc'] at hc; subst hc
  rw [hca.abs] at hg
  have hcap := (SInvU.getCap_capAt (x := (_, σ)) (by rw [hg]; exact Set.mem_singleton _)).2
  exact hS ysl p.bv sb.val fi.val hcap w h1 h2

/-- **ReadFPU's destination frame from `JAtZ`** (INV-PLAN P1, KENTRY-PLAN g4a
P1; g5b): `FpuFrameJHyp` is `JAtZ.fcap` at the slot (every byte of a
non-device frame cap in a spec user frame). -/
theorem JAtZ.fpuFrameJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (x : U64) :
    FpuFrameJHyp (L := L) Z s σ x := by
  intro sl0 hA hx p sz r m ep asid va hc a h1 h2
  subst hx
  have h := J.fcap _ hA.isSlot
  rw [hc] at h
  have hfb : (fbitsF sz).val = frameBitsN sz := by rw [fbitsF_val]; cases sz <;> rfl
  exact h rfl a h1 (by rw [hfb]; exact h2)

end

/-- **`SInvI` from the entry state to the dispatch state** (module docstring;
the FaultIP write keeps the caps, `update_time_stamp` the rest). -/
theorem sinvI_disp (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hBA : BudgetAt σ σb true) (h : SInvI σ) : SInvI σb := by
  obtain ⟨⟨σu, hu, ebu⟩, ek, -⟩ := BudgetAt.shape27 hnd hk hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  refine h.frame (capAt_updTcb hk (by rfl) ek') ?_ ?_ ?_ (archObj_updTcb hk ek') <;> rw [ebu, e] <;> rfl

/-! ## The bundles -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR3` without `fnz`, `utks` (theorems of `JAtZ`) and `handlers`,
`ports`, `urz` (from `SInvI`)** (module docstring). -/
structure JEntryAtR5 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] joint `JEntryAt.flags` (l4v `tcb_relation`'s flags). -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] joint `JEntryAt.vsTyp` (l4v `valid_cap` typ_at, `pspace_distinct`). -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)

variable {arI}

theorem JEntryAtR5.toR3 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hI : SInvI σ) (E : JEntryAtR5 (L := L) arI AR Z s ar σ) :
    JEntryAtR3 (L := L) arI AR Z s ar σ where
  stall := E.stall
  flags := E.flags
  handlers := J.handlersJ hI.irqH
  ports := J.portsJ hI.ioP
  ioapics := E.ioapics
  archIrq := E.archIrq
  vsTyp := E.vsTyp
  fnz := J.fnzJ
  urz := J.urzJ hI.utZ
  utks := J.utksJ

variable (arI)

/-- **`JPathM` without the Thread path's `JThreadPath`** (`hFr`, ReadFPU's
destination frame, from `JAtZ.fpuFrameJ`); every other cap's
premise is `JPathM`'s. -/
def JPathME (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Thread p =>
      lbl = fl4_abi.label.TCBSetEPTRoot →
        JVtxScope (L := L) arI AR s ar σ lbl length (.Thread p) blk call don fp buf extra slbl argsU ci sl excaps buffer
          ct
  | c => JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c

/-- **`JPathAtM35` with `JPathME`.** -/
def JPathAtM35E (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      JPathME (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

variable {arI}

theorem JPathME.toM {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {lbl length : U64}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {argsU : List U64} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} {c : capability.Cap}
    (h : JPathME (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c) :
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c := by
  cases c
  case Thread p => exact ⟨h, fun _ => ⟨fun _ x0 _ => J.fpuFrameJ x0⟩⟩
  all_goals exact h

theorem JPathAtM35E.to35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtM35E (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtM35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 =>
    (h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13).toM J

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKV35` with `JEntryAtR5`** (module docstring). -/
structure KDispHypsKV35E (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR5 (L := L) arI AR Z s a σ ∧
    JPathAtM35E (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR5 (L := L) arI AR Z s a σ ∧
    JPathAtM35E (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI}

theorem KDispHypsKV35E.to35 {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hI : SInvI σ)
    (h : KDispHypsKV35E (L := L) arI AR MR Z H Cs D s a σ n c) :
    KDispHypsKV35 (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p, v⟩ := h.inv ct call bl don hct hi; ⟨e.toR3 J hI, p.to35 J, v⟩,
    fun ct rg sr cr hct hm => let ⟨e, p, v⟩ := h.mid ct rg sr cr hct hm; ⟨e.toR3 J hI, p.to35 J, v⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ35` with the spec-only
entry bundle `hI : SInvI σ` [J] spec in place of `JEntryAtR3`'s `handlers`,
`ports`, `urz` at every dispatch state and the Thread path's `hFr`, and `fnz`,
`utks` proved from `JAtZ`.
Every other premise is `kernel_entryJ35`'s. -/
theorem kernel_entryJ35E [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ) (hI : SInvI σ)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV35E (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPost (L := L) arI AR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostX (L := L) arI AR c σ r ⦄ := by
  obtain ⟨x, hk, -⟩ := hX.sb.1.2
  exact kernel_entryJ35 s a σ J hct hR hX n c hn hflag
    (fun σb hBA V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hBA V' Ac' Lst' D' s' a' hF J').to35 J' (sinvI_disp hnd hk hBA hI))
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu hRef hPI hFast

end

end

end Fl4Proofs.P3.SInvR.G5
