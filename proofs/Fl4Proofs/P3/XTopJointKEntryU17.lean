/-
P3 (issue #16, s26-2): **`kernel_entry_reachU17`** = g7a-3's `kernel_entry_reachU11`
without C26 `devFree`, C27 `devGpm` and D7 `idle` (INV-PLAN §1.U3L): sd7-2's U15
combined with s26's U14.

* **`JReachU17 s a σ := JReachU3 s a σ ∧ GpmOutV σ ∧ IdleVtS σ ∧ DevRangeS σ`**
  (`JReachU3`, `JAtZ`, `RelTopM`, `JExt` unchanged): the three spec-only facts carried
  with the reachable states, each asked at one state, the start state.
* The proof runs U15 (at `⟨hJ.1, hJ.2.1, hJ.2.2.1⟩`); its dispatch bundle
  `KDispHypsKVU12` (C26 still in it) comes from `KDispHypsKVU17` (`JDevPathU17` =
  U12's `JDevPathU12` without `devFree`) by `KDispHypsKVU17.toU12`, with `DevFreeT` at
  the dispatch state from U14's `devFreeT_of` and `BudgetAt.devRange`. Each exit
  ends in `JReachU17`: U15's exit gives `JReachU15`, and `DevRangeS σ'` comes from
  SpecInvDvP (`kentry_devRange`, `kcall_devRange`, `fip_kcall_devRange`).

Premises removed (relative to U11): C26 `devFree`, C27 `devGpm`, D7 `idle` [J].
Added: none (the three spec facts are asked at the start state, in `JReachU17`).
-/
import Fl4Proofs.P3.XTopJointKEntryU14
import Fl4Proofs.P3.XTopJointKEntryU15
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `JDevPathU12` without `devFree` (C26). -/
structure JDevPathU17 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p sb fi : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [P] `CONFIG_RETYPE_FAN_OUT_LIMIT` is FL4's 256 (as `JUtPath.fan`). -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [scope] a VT-x object type (14 to 18), as `JUtPath.vtx` (the decode of a
  device cap refuses these types on both sides; `decode_invocation_untypedJ`
  takes the native types only). -/
  vtx : ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi true) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  /-- [P] one core (as `JUtPath.core0`). -/
  core0 : Z.c = 0#u64
  /-- [J] as `JUtPath.bufObj`. -/
  bufObj : BufObjHyp Z.B σ
  /-- [J] as `JUtPath.heapH`. -/
  heapH : ArchFitHyp H σ ∧ RegionUnrefAt (L := L) H Cs D s
  /-- [J] DevJ's `DevApart` at the entry's sets and heap (l4v `valid_untyped` /
  `pspace_no_overlap` for device caps with `valid_global_refs` /
  `kernel_window`: no device untyped range covers a kernel object, a typed-heap
  object or a RAM object, `H`'s objects meeting it lie below its free index, and
  its range lies in one canonical half with a nonzero base, of size bits at
  least 4, l4v `untyped_min_bits`): true from boot by
  the boot checks (e408a625: no device untyped over the kernel image's names;
  9ab17db1: none at the pointer 0; RAM and device physical ranges are
  disjoint; physical memory below `2^47`; boot.rs gives out blocks of at
  least `MIN_UNTYPED` = 4 size bits), kept by retype
  (UtDevRet's `DevApart.retype`: a device child is a sub-range, a new device
  frame lies below the source's new free index). -/
  devApart : DevApart (L := L) Z.th H Z.G Cs s
  /-- [J] the reset's `VsReachMiss` at the restart's state, as
  `JUtPath.vsReach`, for the device cap's region (UtDevDrop's `JAtZ.dropAD`
  in UtDevReset's `JAtZ.reset_untypedDJ`). Asked only when the cap has no
  descendants (FINDING g7b-2: unguarded it is false). -/
  vsReach : (∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl)) → ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1)
  /-- [P] `CONFIG_RESET_CHUNK_BITS` is FL4's 16, as `JUtPath.rcb` (the spec's
  device reset, UtDevDrop's `reset_devX`). -/
  rcb : Fl4Spec.resetChunkBits = 16
/-- **`JPathMEU12` with `JDevPathU17` for the device Untyped cap.** -/
def JPathMEU17 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Untyped p sb fi dev =>
      (dev = true → JDevPathU17 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU
        ci sl excaps buffer ct) ∧
      (dev = false → JUtPathM (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl
        excaps buffer ct)
  | c => JPathMEU12 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer
      ct c

/-- **`JPathAtMU12` with `JPathMEU17`.** -/
def JPathAtMU17 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      JPathMEU17 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU12` with `JPathAtMU17`.** -/
structure KDispHypsKVU17 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtMU17 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtMU17 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JDevPathU17.toU12 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length p sb fi : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : JDevPathU17 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct) (hDF : DevFreeT (L.mem s) Z.G σ) :
    JDevPathU12 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct :=
  { fan := h.fan, vtx := h.vtx, core0 := h.core0, bufObj := h.bufObj, heapH := h.heapH, devApart := h.devApart,
    devFree := hDF, vsReach := h.vsReach, rcb := h.rcb }

set_option maxHeartbeats 4000000 in
theorem JPathAtMU17.toU12 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} (hDF : DevFreeT (L.mem s) Z.G σ)
    (h : JPathAtMU17 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU12 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  cases c
  case Untyped p sb fi dev => exact ⟨fun hd => JDevPathU17.toU12 (hP.1 hd) hDF, hP.2⟩
  all_goals exact hP

/-- **`KDispHypsKVU17` gives `KDispHypsKVU12`** at a `JAtZ` dispatch state with `DevRangeS`. -/
theorem KDispHypsKVU17.toU12 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hD : SInvDV.DevRangeS σ)
    (h : KDispHypsKVU17 (L := L) arI AR Z H Cs D s a σ n c) : KDispHypsKVU12 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi; ⟨e, p.toU12 (devFreeT_of arI J hD)⟩,
    fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm; ⟨e, p.toU12 (devFreeT_of arI J hD)⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with the three spec facts** (module docstring). -/
abbrev JReachU17 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU3 (L := L) arI AR MR s a σ ∧ SInvGp.GpmOutV σ ∧ SInvIV.IdleVtS σ ∧ SInvDV.DevRangeS σ

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **`kernel_entry_reachU11` without C26 `devFree`, C27 `devGpm` and D7 `idle`** (module docstring). -/
theorem kernel_entry_reachU17V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      VxE Z ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU17 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
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
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU15V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR
      ⟨hJ3, hGp, hIv⟩
  have hU3 := sinvX_ut3 hX
  refine ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl (fun σb hB V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hB V' Ac' Lst' D' s' a' hF J').toU12 J' (BudgetAt.devRange hDv hB)) hDL hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'.1, hJ'.2.1, hJ'.2.2,
      SInvDV.kentry_devRange c hU3 hDv _ hσ'⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1, hJ'.2.1, hJ'.2.2,
      SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1, hJ'.2.1, hJ'.2.2,
      SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1, hJ'.2.1, hJ'.2.2,
      SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, ⟨w, hw, hO⟩, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, ⟨w, hw, hO⟩, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1, hJ'.2.1, hJ'.2.2,
      SInvDV.fip_kcall_devRange _ true ev hU3 hDv w hw _ hO⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, ⟨w, hw, hO⟩, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, ⟨w, hw, hO⟩, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1, hJ'.2.1, hJ'.2.2,
      SInvDV.fip_kcall_devRange _ true ev hU3 hDv w hw _ hO⟩

end

end

end Fl4Proofs.P3.SInvR.G5
