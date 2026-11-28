/-
P3 (issue #16, s27): **`kernel_entry_reachU12`** = g7a-3's `kernel_entry_reachU11`
without C27 `devGpm` (INV-PLAN §1.U3L; KENTRY-PLAN g7a-4 (3), s27): the global
PML4 off every device untyped cap's range, asked by the device Untyped path
(`JDevPath.devGpm`) at every dispatch state.

* Spec half: SpecInvGpm's `GpmOutV` (l4v `valid_global_refs`: no cap of any
  kind covers `x64_global_pml4`), carried across the syscall entry, every
  event and the FaultIP write by the SpecGlob family's cap-domination argument
  (`kentry_gpmOut`, `kcall_gpmOut`, `fipEv_gpmOut`) with `x64GlobalPml4`
  constant (SpecInvGpK1..K6).
* The carry: `JReachU12 s a σ := JReachU3 s a σ ∧ GpmOutV σ` (JReachU3, JAtZ,
  RelTopM, JExt unchanged). Each clause ends in `JReachU12`: U11's exit gives
  `JReachU3` and `SInvX` at the entry state (`SpecGlobS`, `UtInv3`), the
  preservation lemma the spec fact at the exit. The start fact is asked at
  one state, in `JReachU12`'s first component's state (`hJ.2`).
* At the dispatch state σb (`BudgetAt σ σb true`): the view and the global
  PML4 are σ's (`fip_view`/`fip_gpm`, `budget_view`/`budget_gpm`), so
  `GpmOutV σb` and `UtInv'' σb` (`UtWfV`: size bits ≤ 47, aligned base).
* The bridge `devGpm_of`: at a `JAtZ` state, a chain slot's FL4 cap
  `Untyped p sb fi true` is related to the spec cap
  `untypedCap true p.bv sb fi` in the same slot (`J.dstate.1.1.abs_cap`, the
  MDB's `members` and `IsSlot.abs`), whose `covR` is `delR p sb`; with the
  alignment, `delR` is the `Nat` range `DevGpm` reads (`mem_delR_iff`).
* `JDevPathU12` = `JDevPath` without `devGpm`; `JPathMEU12` / `JPathAtMU12` /
  `KDispHypsKVU12` = U7's with it; `.toU7` given `DevGpm` at the dispatch state.

Premise removed (relative to U11): C27 `devGpm` [J]. Added: none (the start
state's `GpmOutV` is part of the start bundle `JReachU12`, asked at one state,
[S] start as A18).
-/
import Fl4Proofs.P3.XTopJointKEntryU11
import Fl4Proofs.P3.SpecInvGpm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec facts at the dispatch state -/

theorem utWf_of {σ : Fl4Spec.State Unit} (hU : SInvU.UtInv'' σ) : SInvU.UtWfV (SInvU.uV σ) := hU.1.1.2.1

/-- `GpmOutV` and `UtInv''` at a dispatch state. -/
theorem budget_gpmOut {σ σb : Fl4Spec.State Unit} (hX : SInvX σ) (hI : SInvGp.GpmOutV σ)
    (h : BudgetAt σ σb true) : SInvGp.GpmOutV σb ∧ SInvU.UtInv'' σb := by
  obtain ⟨σ0, h0, hb⟩ := h
  have hv : SInvU.uV σb = SInvU.uV σ := (SInvGp.budget_view hb).trans (SInvGp.fip_view h0)
  have hg : σb.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 :=
    (SInvGp.budget_gpm (y := (true, σb)) hb).trans (SInvGp.fip_gpm h0)
  refine ⟨?_, ?_⟩
  · unfold SInvGp.GpmOutV; rw [hv, hg]; exact hI
  · show SInvU.UtInv''V (SInvU.uV σb); rw [hv]; exact (sinvX_ut3 hX).1

/-- An aligned untyped region fits below `2^64`. -/
theorem fit_of_align {b : Fl4Spec.ObjRef} {n : Nat} (hn : n < 64) (ha : b.toNat % 2 ^ n = 0) :
    b.toNat + 2 ^ n ≤ 2 ^ 64 := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero ha
  have hlt : b.toNat < 2 ^ 64 := b.isLt
  have e64 : (2 : Nat) ^ 64 = 2 ^ n * 2 ^ (64 - n) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hq, e64] at hlt
  have hq' : q < 2 ^ (64 - n) := Nat.lt_of_mul_lt_mul_left hlt
  have : 2 ^ n * (q + 1) ≤ 2 ^ n * 2 ^ (64 - n) := Nat.mul_le_mul_left _ hq'
  rw [hq, e64]; rw [Nat.mul_add, Nat.mul_one] at this; exact this

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **C27 at a `JAtZ` state from the spec fact** (module docstring). -/
theorem devGpm_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hI : SInvGp.GpmOutV σ) (hU : SInvU.UtInv'' σ) :
    DevGpm (L.mem s) Z.G σ := by
  intro x hx p sb fi hcv hr
  have hM := J.xtop.rel.2.1.2.2.1
  obtain ⟨sl, hAs, rfl⟩ := ((hM.members x).1 hx).1.abs
  obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hAs
  rw [capAt_capV, hcv] at hc0; cases eq_of_ok_eq hc0
  rw [hca0.abs] at hg0
  have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
  have hsc : (SInvU.uV σ).2.1 sl = some (absCap (.Untyped p sb fi true)) := by
    show SInvU.capAt σ sl = _; rw [SInv.vfh_capAt]; exact ha0
  obtain ⟨hn, hal, -⟩ := utWf_of hU sl true p.bv sb.val fi.val hsc
  have hn' : sb.val < 64 := by simp [Fl4Spec.untypedMaxBits] at hn; omega
  refine hI (default : Fl4Spec.Irq) sl _ hsc ?_
  show σ.archState.x64GlobalPml4 ∈ SInvU.delR p.bv sb.val
  exact (SInvU.mem_delR_iff hn' (fit_of_align hn' hal) _).2 hr

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JDevPath` without C27 `devGpm`** (from `GpmOutV`, `devGpm_of`). -/
structure JDevPathU12 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
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
  /-- [J] UtDevRet's `DevFreeT` (l4v `valid_untyped` for device caps: no spec
  object in a device untyped cap's free part): true from boot (no spec object
  in a device range), kept by retype (DevFree's `DevFree.retype`,
  UtDevUt's `SpecFreeP.retypeU`). -/
  devFree : DevFreeT (L.mem s) Z.G σ
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
/-- **`JPathMEU7` with `JDevPathU12` for the device Untyped cap.** -/
def JPathMEU12 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : capability.Cap → Prop
  | .Untyped p sb fi dev =>
      (dev = true → JDevPathU12 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU
        ci sl excaps buffer ct) ∧
      (dev = false → JUtPathM (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl
        excaps buffer ct)
  | c => JPathMEU7 (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer
      ct c

/-- **`JPathAtMU7` with `JPathMEU12`.** -/
def JPathAtMU12 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (ar : A)
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
      JPathMEU12 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) blocking is_call can_donate first_phase buf
        e mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct c

/-- **`KDispHypsKVU7` with `JPathAtMU12`.** -/
structure KDispHypsKVU12 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtMU12 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtMU12 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JDevPathU12.toDev {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length p sb fi : U64} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {argsU : List U64} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : JDevPathU12 (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct) (hG : DevGpm (L.mem s) Z.G σ) :
    JDevPath (L := L) arI AR Z H Cs D s ar σ lbl length p sb fi blk call don fp buf extra slbl argsU ci sl excaps
      buffer ct :=
  ⟨h.fan, h.vtx, h.core0, h.bufObj, h.heapH, h.devApart, h.devFree, hG, h.vsReach, h.rcb⟩

set_option maxHeartbeats 4000000 in
theorem JPathAtMU12.toU7 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64} (hG : DevGpm (L.mem s) Z.G σ)
    (h : JPathAtMU12 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU7 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  have hP := h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13
  cases c
  case Untyped p sb fi dev => exact ⟨fun hd => (hP.1 hd).toDev hG, hP.2⟩
  all_goals exact hP

theorem KDispHypsKVU12.toU7 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hG : DevGpm (L.mem s) Z.G σ)
    (h : KDispHypsKVU12 (L := L) arI AR Z H Cs D s a σ n c) : KDispHypsKVU7 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi; ⟨e, p.toU7 hG⟩,
    fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm; ⟨e, p.toU7 hG⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with the global-PML4 fact** (module docstring). -/
def JReachU12 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU3 (L := L) arI AR MR s a σ ∧ SInvGp.GpmOutV σ

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **`kernel_entry_reachU11` without C27 `devGpm`** (module docstring). -/
theorem kernel_entry_reachU12V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU12 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      VxE Z ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU12 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR11 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU12 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv11 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU12 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv11 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU12 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv11 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU12 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv11 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU12 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv11 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU12 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU11V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ.1
  have hG := hJ.2
  have hSg : SInvG.SpecGlobS σ := hX.sb.1.1.sg
  have hU3 := sinvX_ut3 hX
  refine ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    exact WP.spec_mono (hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU7
        (devGpm_of J' (budget_gpmOut hX hG hb).1 (budget_gpmOut hX hG hb).2)) hDL hFin)
      fun r ⟨σ', hm, hRJ, hX', hMR, hIo', hNo, hZ, hPg', hJ'⟩ =>
        ⟨σ', hm, hRJ, hX', hMR, hIo', hNo, hZ, hPg', hJ', SInvGp.kentry_gpmOut c hSg hU3 hG _ hm⟩
  · intro w a1 hIh hE
    exact WP.spec_mono (hIrq w a1 hIh hE) fun r ⟨σ', hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ'⟩ =>
      ⟨σ', hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ', SInvGp.kcall_gpmOut true .interrupt hSg hU3 hG _ hO⟩
  · intro n c hct hU hE
    exact WP.spec_mono (hUs n c hct hU hE) fun r ⟨σ', hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ'⟩ =>
      ⟨σ', hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ', SInvGp.kcall_gpmOut true _ hSg hU3 hG _ hO⟩
  · intro ad c ft hct hVm' hE
    exact WP.spec_mono (hVm ad c ft hct hVm' hE) fun r ⟨σ', hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ'⟩ =>
      ⟨σ', hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ', SInvGp.kcall_gpmOut true _ hSg hU3 hG _ hO⟩
  · intro v hct hv hE
    exact WP.spec_mono (hTr v hct hv hE) fun r ⟨ev, σ', hK, hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ'⟩ =>
      ⟨ev, σ', hK, hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ',
        let ⟨_, hw, hy⟩ := hO; SInvGp.fipEv_gpmOut true ev hSg hU3 hG hw _ hy⟩
  · intro n hct hU hD hE
    exact WP.spec_mono (hSU n hct hU hD hE) fun r ⟨ev, σ', hK, hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ'⟩ =>
      ⟨ev, σ', hK, hO, hRJ, hX', hMR, hIo', hNo, hZ, hJ',
        let ⟨_, hw, hy⟩ := hO; SInvGp.fipEv_gpmOut true ev hSg hU3 hG hw _ hy⟩

end

end

end Fl4Proofs.P3.SInvR.G5
