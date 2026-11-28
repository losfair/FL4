/-
P3 (issue #16, jc5): **`kernel_entry_reachU21`** = jc3's `kernel_entry_reachU20`
without C24's device `vsReach` (INV-PLAN §1.U3L C24; KENTRY-PLAN jc4 (2), jc5).

* `JAtZ.carry` (JCarryDefs' `JCarry`) carries `devTab : DevTab Z.G (L.mem s) σ`: every
  spec arch object of a VSpace table or ASID pool type (`VsTy`: PML4, PDPT, PD, PT,
  pool) misses the range of every device untyped cap of the MDB. True in reachable
  states: FL4 (as seL4's `decodeUntypedInvocation`) retypes only frames and untypeds
  from a device untyped (fl4-core untyped.rs), MakePool takes a RAM untyped, RAM and
  device ranges are apart (`devSep`). Frame steps keep it (`DevTab.frame`: the device
  ranges after inside old ones, `DevSub`; the tables after old ones, `TabBack` from
  `KSz` or `KBack` + `ArchFwd`), RAM retypes and MakePool by `devTabRetypeR` /
  `DevTab.step` (new tables in the window, off every device range by `devSep`), device
  retypes by `devTabRetypeD` (the new device caps inside the source; no new table),
  the resets' free-index writes by `DevSub.of_utFrom`, the drops by `TabBack`.
* `JAtZ.devVsReach`: C24's device `vsReach` at a `JAtZ` state that is `Entered`:
  the caller's restart (`JAtZ.restartJ`) gives `JAtZ` at `s1`, a table `VsReach`es
  from the `NeedR` roots is in its set (`VsReach.mem`, `VsSlotsW.needR`), so a spec
  table or pool of `σ1` (`VsRel.pool`, `PtRel.l4 … l1`), so one of `σ` (only the
  caller's TCB changed), which `devTab` keeps off the device cap's range.
* `JDevPathU21` = `JDevPathU19` without `vsReach`; `KDispHypsKVU21.toU20 J' hni` fills
  it from the dispatch state's own `JAtZ`, `Entered` there by `BudgetAt.enteredP`.

Premises removed (relative to U20): C24 device `vsReach` [J]. Added: none.
-/
import Fl4Proofs.P3.XTopJointKEntryU20
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **C24's device `vsReach` at an `Entered` `JAtZ` state** (module docstring). -/
theorem _root_.Fl4Proofs.P3.JAtZ.devVsReach (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {x p sb fi : U64} (hx : x ∈ Z.G.chains.flatten)
    (hc : capV (L.mem s) x = .Untyped p sb fi true) :
    ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1) := by
  intro s1 hs1
  obtain ⟨s1', σ1, x1, -, -, -, -, he1, -, -, -, hs1', Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hs1] at hs1'
  cases eq_of_ok_eq hs1'
  intro k q hR
  obtain ⟨-, hRv, hPt, hPI, -⟩ := J1.xtop.fin
  have hF := J1.xtop.fin
  have hm := hR.mem hRv hPt hPI J1.vsc.needR.1 J1.vsc.needR.2.1 J1.vsc.needR.2.2.1 J1.vsc.needR.2.2.2.1
    J1.vsc.needR.2.2.2.2
  have hT : ∃ ao, σ1.kheap q.bv = some (.archObj ao) ∧ VsTy (Fl4Spec.aaType ao) := by
    unfold Vs.lvlSet at hm
    split at hm
    · obtain ⟨f, hf, -⟩ := hF.2.1.pool q hm; exact ⟨_, hf, by simp [VsTy, Fl4Spec.aaType]⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q hm; exact ⟨_, hf, by simp [VsTy, Fl4Spec.aaType]⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q hm; exact ⟨_, hf, by simp [VsTy, Fl4Spec.aaType]⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q hm; exact ⟨_, hf, by simp [VsTy, Fl4Spec.aaType]⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q hm; exact ⟨_, hf, by simp [VsTy, Fl4Spec.aaType]⟩
    · simp at hm
  obtain ⟨ao, hk1, hv⟩ := hT
  subst he1
  rw [Notif.stsAct_kheap, Notif.updK_kheap] at hk1
  have hne : q.bv ≠ ct.bv := fun e => by rw [e] at hk1; simp at hk1
  rw [Function.update_of_ne hne] at hk1
  exact J.carry.devTab x hx p sb fi hc q.bv ao hk1 hv

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JDevPathU19` without `vsReach`** (C24 device vsReach, from `JAtZ.carry.devTab`, jc5). -/
structure JDevPathU21 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length p sb fi : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  /-- [P] as `JUtPath.fan`. -/
  fan : Fl4Spec.retypeFanOutLimit = 256#64
  /-- [scope] as `JDevPath.vtx`. -/
  vtx : ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi true) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  /-- [P] as `JUtPath.core0`. -/
  core0 : Z.c = 0#u64
  /-- [J] the `RegionUnrefAt` half of `JDevPath.heapH` (C24 heapH). -/
  unref : RegionUnrefAt (L := L) H Cs D s
  /-- [P] as `JDevPath.rcb`. -/
  rcb : Fl4Spec.resetChunkBits = 16

/-- **`JPathMEU19` with `JDevPathU21`.** -/
def JPathMEU21 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Untyped p sb fi dev =>
      (dev = true → JDevPathU21 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU
        ci sl excaps buffer ct) ∧
      (dev = false → JUtPathMU16 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl
        argsU ci sl excaps buffer ct)
  | .AsidControl => JAsidCPathU16 (L := L) AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct
  | c => JPathMEU12 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct c

/-- **`JPathAtMU19` with `JPathMEU21`.** -/
def JPathAtMU21 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      JPathMEU21 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU20` with `JPathAtMU21`.** -/
structure KDispHypsKVU21 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7 (st := st) arI AR Z s a σ ∧
    JPathAtMU21 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7 (st := st) arI AR Z s a σ ∧
    JPathAtMU21 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JDevPathU21.toU19 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length p sb fi : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : JDevPathU21 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl excaps buffer ct)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hct : sched.cur_thread st s = ok ct)
    (hx : cslotAddr sl ∈ Z.G.chains.flatten) (hc : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi true) :
    JDevPathU19 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl excaps buffer ct :=
  { fan := h.fan, vtx := h.vtx, core0 := h.core0, unref := h.unref,
    vsReach := fun _ => J.devVsReach hni hct hx hc, rcb := h.rcb }

set_option maxHeartbeats 4000000 in
theorem JPathAtMU21.toU19 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hct : sched.cur_thread st s = ok ct)
    (h : JPathAtMU21 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU19 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  cases c
  case Untyped p sb fi dev =>
    refine ⟨fun hd => ?_, hP.2⟩
    subst hd
    obtain ⟨pp, e1, hpp⟩ := h8
    have hAs : AbsSlot Z.th sl := ⟨pp, e1, Or.inl hpp⟩
    have hx : cslotAddr sl ∈ Z.G.chains.flatten :=
      (J.xtop.rel.2.1.2.2.1.members _).2 ⟨hAs.isSlot, _, h9, by simp⟩
    exact (hP.1 rfl).toU19 J hni hct hx (capV_of_capAt h9)
  case AsidControl => exact hP
  all_goals exact hP

theorem KDispHypsKVU21.toU20 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : KDispHypsKVU21 (L := L) arI AR Z H Cs D s a σ n c) : KDispHypsKVU20 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi; ⟨e, p.toU19 J hni hct⟩,
    fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm; ⟨e, p.toU19 J hni hct⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **`kernel_entry_reachU20` without C24's device `vsReach`** (module docstring). -/
theorem kernel_entry_reachU21V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
            KDispHypsKVU21 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
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
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU20V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU20 J' (hb.enteredP hnd (hX.entered hct))) hDL hFin,
    hIrq, hUs, hVm, hTr, hSU⟩

end

end

end Fl4Proofs.P3.SInvR.G5
