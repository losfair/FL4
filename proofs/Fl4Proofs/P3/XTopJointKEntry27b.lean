/-
P3 (DESIGN.md §9), invariant line G3 (INV-PLAN §4, KENTRY-PLAN g3c):
**`kernel_entryJ27b` = `kernel_entryJ27` with the mid-path premises g3a listed
(`JPerfRegHyp`, `JPerfIrqSlotHyp`, `JMidVfhHyp`) and `JEntryAt.epQ` discharged**.

All four are read at the dispatch state σb (`BudgetAt σ σb true`: the `FaultIP`
write and `update_time_stamp` from the entry state σ) or at the states where a
first-phase perform starts from it (`MidPerfAt`), from `SInvB σ` and one new
per-state fact `EpQAll σ`; the spec side is XTopJointKEntry27bS.

* `disp27b`: σb's spec front (the `FaultIP` state `SInvK.fipSt σ x` = `faultIPSt`,
  `update_time_stamp` from it; `BudgetAt.shape27`).
* `midPerfAt_sV`: the first phase keeps sch23's SC view `sV` (`sck_getMessageInfo'`,
  `scke_midF`, `scke_midE`, `sck_setThreadState`), so every binding `mV σ1` at a
  `MidPerfAt` state is σb's, hence σ's (`bound27b`: the `FaultIP` write keeps ct's SC).
* `jPerfRegHyp_27b` (JPerfRegHyp [J] REMOVED): at a `MidPerfAt` state the decode
  result satisfies ut8's `InvOKV` at σ's view (`SInvK.midAt_facts`); an Untyped
  retype's region (`utD` = `SInvK.UtSet`) and MakePool's (`asidD` = `SInvK.MpSet`)
  miss the current thread (`SInvK.out_ct`) and every bound SC (`SInvK.out_bound`).
  l4v counterpart: `valid_untyped_inv` / `valid_aci` (free regions, reset untyped
  childless), from `untyped_children_in_mdb` (UtInv''), `if_live_then_nonz_cap`
  (IfLiveT, sl's ScLiveT), `sym_refs` (ScInv) and `valid_global_refs` (IdleOutV,
  IdleScOutV).
* `jPerfIrqSlotHyp_27b` (JPerfIrqSlotHyp [J] REMOVED): `SpecGlobS.irq` at σ, the
  view and the IRQ node unchanged up to the perform.
* `jMidVfhHyp_27b` (JMidVfhHyp [J] REMOVED): vfh3's `vfh_handleInvocationR` from
  `VfhV ∧ CnDom ∧ UtInv''` at σb.
* `epQPre_of_sinv` (JEntryAt.epQ [J] REMOVED, replaced by `hE : EpQAll σ`): epq2's
  `EpQAll` is exactly `∀ e, EpQPre σ e` at σ (its ScBack / ActReady parts are already
  inside); `SInvK.epQAll_disp` moves it to σb (ct's registers only, the clock only
  advances, the action is `resume_cur_thread` by `Entered`). So neither `Rdy σ` nor
  `ScInv`'s ScBack is needed as a separate premise here: `EpQAll σ` is the one
  per-state fact, carried at every exit by epq2's `kentry_epQAll` / `kcall_epQAll`
  (an SInvB candidate field).
* `JEntryAtR2` (= `JEntryAtR` without `epQ`), `KDispHypsKV27b` (= `KDispHypsKV27` with
  `JEntryAtR2` and no mid perf / IRQ-slot / handler facts), `.to27`,
  `kernel_entryJ27b`.
-/
import Fl4Proofs.P3.XTopJointKEntry27
import Fl4Proofs.P3.XTopJointKEntry27bS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec premises -/

/-- **The dispatch state's spec front** (module docstring). -/
theorem disp27b (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hS : SInvAll.SInvB σ)
    (hBA : BudgetAt σ σb true) :
    ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      ((), SInvK.fipSt σ x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 ∧
      ((), σb) ∈ (Fl4Spec.updateTimeStamp (Z := Unit) (SInvK.fipSt σ x)).1 ∧
      σb.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σb.curThread = σ.curThread := by
  obtain ⟨x, hk, -⟩ := hS.1.2
  obtain ⟨⟨σu, hu, ebu⟩, ek, ect, -, -, -⟩ := BudgetAt.shape27 hnd hk hBA
  subst ebu
  refine ⟨x, hk, ?_, hu, ek, ect⟩
  rw [fl4SyscallFaultIP_eq hk]
  exact Set.mem_singleton _

/-- **The first phase keeps the SC view** (module docstring). -/
theorem midPerfAt_sV {cptr : Fl4Spec.CapRef} {σ σ1 : Fl4Spec.State Unit} {inv : Fl4Spec.Fl4Invocation}
    (hA : MidRun.MidPerfAt cptr σ inv σ1) : MidRun.sV σ1 = MidRun.sV σ := by
  obtain ⟨info, σa, a, σb, σc, hia, hb, hc, h1⟩ := hA
  have e1 := MidRun.sck_getMessageInfo' _ σ _ hia
  have e2 := MidRun.scke_midF _ _ _ σa _ hb
  have e3 := MidRun.scke_midE _ _ _ a σb _ hc
  have e4 := MidRun.sck_setThreadState _ _ σc _ h1
  exact e4.trans (e3.trans (e2.trans e1))

/-- **A binding at a `MidPerfAt` state is the entry state's** (module docstring). -/
theorem bound27b {σ σb σ1 : Fl4Spec.State Unit} {x : Fl4Spec.Tcb} (hk : σ.kheap σ.curThread = some (.tcb x))
    (ek : σb.kheap = (faultIPSt σ σ.curThread x).kheap) (hm : MidRun.mV σ1 = MidRun.mV σb) {u p : Fl4Spec.ObjRef}
    (h : (MidRun.mV σ1 u).1 = some (some p)) :
    ∃ x0, σ.kheap u = some (.tcb x0) ∧ x0.tcbSchedContext = some p := by
  rw [hm] at h
  have h' : MidRun.tP (σb.kheap u) = some (some p) := h
  rw [ek] at h'
  by_cases hu : u = σ.curThread
  · subst hu
    refine ⟨x, hk, ?_⟩
    simp only [faultIPSt, updK, Function.update_self, MidRun.tP, Option.some.injEq] at h'
    exact h'
  · have e : (faultIPSt σ σ.curThread x).kheap u = σ.kheap u := Function.update_of_ne hu _ _
    rw [e] at h'
    cases hku : σ.kheap u with
    | none => rw [hku] at h'; cases h'
    | some o =>
      rw [hku] at h'
      cases o <;> simp [MidRun.tP] at h'
      exact ⟨_, rfl, h'⟩

set_option maxHeartbeats 4000000 in
/-- **[J] `JPerfRegHyp` holds at the dispatch state** (module docstring). -/
theorem jPerfRegHyp_27b (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hS : SInvAll.SInvB σ)
    (hct : σ.curThread ≠ σ.idleThread) (hBA : BudgetAt σ σb true) (cptr : Fl4Spec.CapRef) :
    MidRun.JPerfRegHyp cptr σb := by
  obtain ⟨x, hk, h0, hu, ek, ect⟩ := disp27b hnd hS hBA
  have hbu : SInvU.uV σb = SInvU.uV σ := SInvK.disp_uv h0 hu
  have hU : SInvU.UtInv'' σ := hS.1.1.ut.1
  intro inv σ1 hA
  obtain ⟨hv1, -, hinv⟩ := SInvK.midAt_facts (show SInvK.MidAt cptr σb inv σ1 from hA)
  have hm : MidRun.mV σ1 = MidRun.mV σb := congrArg (fun v : MidRun.VT => v.2.2.2) (midPerfAt_sV hA)
  have hv : SInvU.uV σ1 = SInvU.uV σ := hv1.trans hbu
  rw [hbu] at hinv
  have hc : SInvK.Out σ σb.curThread := by rw [ect]; exact SInvK.out_ct hS hct
  have hB : ∀ u p, (MidRun.mV σ1 u).1 = some (some p) → SInvK.Out σ p := fun u p h => by
    obtain ⟨x0, hx0, hp⟩ := bound27b hk ek hm h
    exact SInvK.out_bound hS hx0 hp
  cases inv with
  | invokeUntyped ui =>
    cases ui with
    | retype src reset base rb ty sz slots dev =>
      have hok := (show SInvU.UtRetOKV _ _ ∧ SInvU.DestNullV _ _ from hinv).1
      exact And.intro (SInvK.out_ut hU hv hok hc) (fun u p h => SInvK.out_ut hU hv hok (hB u p h))
  | invokeArchObject ai =>
    cases ai with
    | spec i =>
      cases i with
      | invokeASIDControl a =>
        cases a with
        | makePool frame slot parent base =>
          have hok : SInvU.MpOKV (SInvU.uV σ) (.makePool frame slot parent base) := hinv
          exact And.intro (SInvK.out_mp hU hok hc) (fun u p h => SInvK.out_mp hU hok (hB u p h))
      | _ => trivial
    | _ => trivial
  | _ => trivial

/-- **[J] `JPerfIrqSlotHyp` holds at the dispatch state** (module docstring). -/
theorem jPerfIrqSlotHyp_27b (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hS : SInvAll.SInvB σ)
    (hBA : BudgetAt σ σb true) (cptr : Fl4Spec.CapRef) : MidRun.JPerfIrqSlotHyp cptr σb := by
  obtain ⟨x, -, h0, hu, -, -⟩ := disp27b hnd hS hBA
  intro i σ1 hA
  obtain ⟨hv1, hn1, -⟩ := SInvK.midAt_facts (show SInvK.MidAt cptr σb _ σ1 from hA)
  exact SInvK.irqSlot_of hS.1.1.sg (hv1.trans (SInvK.disp_uv h0 hu)) (hn1.trans (SInvK.disp_node h0 hu))

/-- **[J] `JMidVfhHyp` holds at the dispatch state** (module docstring). -/
theorem jMidVfhHyp_27b (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hS : SInvAll.SInvB σ)
    (hBA : BudgetAt σ σb true) (cptr : Fl4Spec.CapRef) : JMidVfhHyp cptr σb := by
  obtain ⟨x, -, h0, hu, -, -⟩ := disp27b hnd hS hBA
  exact SInvK.vfh_mid hS h0 hu cptr

/-- **`JEntryAt.epQ` at the dispatch state from `EpQAll σ`** (module docstring). -/
theorem epQPre_of_sinv (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hS : SInvAll.SInvB σ)
    (hni : Entered σ) (hE : SInvE.EpQAll σ) (hBA : BudgetAt σ σb true) : ∀ e, Sched.EpQPre σb e := by
  obtain ⟨x, hk, -, hu, -, -⟩ := disp27b hnd hS hBA
  exact SInvK.epQAll_disp hS hni.2 hk hu hE

/-! ## The bundles and the top -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR` without `epQ`** (module docstring); every other field as
`JEntryAt`'s (same tags). -/
structure JEntryAtR2 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `JEntryAt.stall`. -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] `JEntryAt.flags`. -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] `JEntryAt.handlers`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] `JEntryAt.ports`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] `JEntryAt.vsTyp`. -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] `JEntryAt.live`. -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [J] `JEntryAt.fnz`. -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] `JEntryAt.urz`. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] `JEntryAt.utks`. -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

variable {arI}

theorem JEntryAtR2.toR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (E : JEntryAtR2 (L := L) arI AR Z H Cs s ar σ) (epQ : ∀ e, Sched.EpQPre σ e) :
    JEntryAtR (L := L) arI AR Z H Cs s ar σ where
  stall := E.stall
  flags := E.flags
  epQ := epQ
  handlers := E.handlers
  ports := E.ports
  ioapics := E.ioapics
  archIrq := E.archIrq
  vsTyp := E.vsTyp
  live := E.live
  fnz := E.fnz
  urz := E.urz
  utks := E.utks

variable (arI)

/-- **`KDispHypsKV27` with `JEntryAtR2` and no mid perf / IRQ-slot / handler facts**
(module docstring). -/
structure KDispHypsKV27b (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAtR2 (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAtR2 (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`KDispHypsKV27` at a dispatch state from `KDispHypsKV27b`, `SInvB` and
`EpQAll` at the entry state** (module docstring). -/
theorem KDispHypsKV27b.to27 (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit}
    (hS : SInvAll.SInvB σ) (hni : Entered σ) (hE : SInvE.EpQAll σ) (hBA : BudgetAt σ σb true)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {n : I64}
    {c : Fl4Spec.Syscall} (h : KDispHypsKV27b (L := L) arI AR MR Z H Cs D s a σb n c) :
    KDispHypsKV27 (L := L) arI AR MR Z H Cs D s a σb n c := by
  have hq := epQPre_of_sinv hnd hS hni hE hBA
  refine ⟨fun ct call bl don hct' hi => ?_, fun ct rg sr cr hct' hm => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h.inv ct call bl don hct' hi
    exact ⟨a1, a2.toR hq, a3, a4⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h.mid ct rg sr cr hct' hm
    exact ⟨a1, a2.toR hq, a3,
      ⟨jPerfRegHyp_27b hnd hS hni.1 hBA _, jPerfIrqSlotHyp_27b hnd hS hBA _⟩, jMidVfhHyp_27b hnd hS hBA _, a4⟩

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ27` with the mid-path premises and `JEntryAt.epQ` discharged**
(module docstring). Removed: `JPerfRegHyp`, `JPerfIrqSlotHyp`, `JMidVfhHyp` (in `hK`'s
`mid`) and `JEntryAt.epQ` (in `hK`'s `inv` and `mid`). Added: `hE : EpQAll σ` [J]
(l4v `valid_ep` with `valid_sched`'s released-queue / action slices at σ; epq2
carries it at every exit). -/
theorem kernel_entryJ27b [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV27b (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ27 s a σ J hni hR hS hQ n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to27 hnd hS hni hE hBA)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
