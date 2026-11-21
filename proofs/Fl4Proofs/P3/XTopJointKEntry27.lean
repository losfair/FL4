/-
P3 (DESIGN.md §9), invariant line G3 (INV-PLAN §4, KENTRY-PLAN g3a): **`kernel_entryJ27`
= `kernel_entryJ26P` with the per-state spec premises read from the carried spec
invariant `SInvB` (g1c)**.

The spec front of a syscall entry, from the entry state σ: the `FaultIP` write
(`faultIPSt σ ct x`, one register of ct), `update_time_stamp` (time fields and the
machine state only), a passing `check_budget_restart` (no change:
`checkBudgetRestart_true`); so the dispatch state σb has σ's heap with ct's TCB
replaced by one with the same caps, fault handler and fault (`BudgetAt.shape27`).
Then the handled event, the outcomes `specFront c σ` that `finish` starts from.

Premises supplied here (none of them is a hypothesis of `kernel_entryJ27`):
* `hVI : ValidIrqMasks σ` [J]: `SInvA.vim` (the same definition as SInvV's).
* `hB.now` (NowAgree at `faultIPSt`): `MachPlat.nowAgree` from `hR` and `SInvA.vmt`
  (the write keeps the machine state and the time).
* `hB.cur` (CurInv at `faultIPSt`): `JAtZ.cur` with `Entered` (as `KDispHypsKV26.to25`)
  across the register write (`curInv_faultIPSt`).
* `hB.tmo`: its right disjunct from the new per-state premise `hQ` (below).
* `JEntryAt.ni` at σb: `BudgetAt.enteredP` (already in J26P).
* `JEntryAt.ctnq` at σb and `KDispHypsKV26.recv`'s first part: from `hQ` (the ready
  queues are σ's).
* `JEntryAt.sg` at σb: `SInvA.sg` (SpecGlobS) across the register write
  (`specGlob_disp`, the caps of every object unchanged).
* `JEntryAt.rd0` at σb: `OffReady σb` by invB's `offReady_updateTimeStamp` from
  `hB`'s `OffReady (faultIPSt …)` and `SInvA.vmt`, then `OffReady.rd0`.
* `JEntryAt.vfh` at σb and `recv`'s second part: `SInvA.vfh` (VfhAll);
  `JEntryAt.cnf` at σb: `SInvA.fts` (FaultTcbsS) with l4v `ct_active`
  (`SInvB.entryJ`) (`SInvAll.sinvB_disp`).
* `KFinAtR.fo` (FpuOwnOK at every front-end outcome): `SInvF.fo_front` (fo1's FT
  carried to the handled event; `SInvAll.sinvB_front_fo`).

New per-state premise: `hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p` [J] (l4v
`ct_not_in_q`, part of `valid_sched` under `resume_cur_thread`; not yet a field of
SInvB: ctq's SchedQ / CtNQR line). It is true in every reachable state and replaces
three path-restricted copies (`hB.tmo`'s right disjunct at `faultIPSt`, `JEntryAt.ctnq`
and `recv.1` at σb).

* `JEntryAtR`: `JEntryAt` without `ni`, `ctnq`, `sg`, `rd0`, `vfh`, `cnf`; `.toAt`.
* `KDispHypsKV27`: `KDispHypsKV26` with `JEntryAtR` and no `recv`; `.to26`.
* `KFinAtR27`: `KFinAtR` without `fo`; `.toR`.
* `kernel_entryJ27` (wrapper over J26P).
-/
import Fl4Proofs.P3.XTopJointKEntry26P
import Fl4Proofs.P3.XTopJointKEntry27S
import Fl4Proofs.P3.SpecInvOffT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The dispatch state of the entry** (module docstring): σ's heap with the
`FaultIP` write, σ's current thread, IRQ node, idle thread and ready queues; it is
the `update_time_stamp` outcome of `faultIPSt`. -/
theorem BudgetAt.shape27 (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (h : BudgetAt σ σb true) :
    (∃ σu : Fl4Spec.State Unit,
      ((), σu) ∈ (Fl4Spec.updateTimeStamp (Z := Unit) (faultIPSt σ σ.curThread x)).1 ∧ σb = σu) ∧
    σb.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σb.curThread = σ.curThread ∧
    σb.interruptIrqNode = σ.interruptIrqNode ∧ σb.idleThread = σ.idleThread ∧
    σb.readyQueues = σ.readyQueues := by
  obtain ⟨σ0, h0, hb⟩ := h
  rw [fl4SyscallFaultIP_eq hk] at h0
  have e0 : σ0 = faultIPSt σ σ.curThread x := congrArg Prod.snd (Set.mem_singleton_iff.1 h0)
  subst e0
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hb
  cases u
  have hb' : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  refine ⟨⟨σu, hu, hb'⟩, ?_⟩
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  rw [hb', e]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`CurInv` across the `FaultIP` write** (one register of the current thread). -/
theorem curInv_faultIPSt {σ : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (h : CurInv σ) : CurInv (faultIPSt σ σ.curThread x) := by
  obtain ⟨⟨xt, hxt, h1, h2⟩, ⟨y, n, hy⟩, hact, hrel⟩ := h
  rw [hk] at hxt
  cases hxt
  have hne : σ.curSc ≠ σ.curThread := fun e => by rw [e, hk] at hy; cases hy
  have hkp : (faultIPSt σ σ.curThread x).kheap σ.curSc = σ.kheap σ.curSc :=
    Function.update_of_ne hne _ _
  refine ⟨⟨_, Function.update_self _ _ _, h1, h2⟩, ⟨y, n, hkp.trans hy⟩, ?_, hrel⟩
  intro hi y' n' hy'
  exact hact hi y' n' (hkp.symm.trans hy')

/-- **`SpecGlob` at a state with the caps of `σ`** (module docstring): `SInvA.sg`
(`SpecGlobS`, on `capAt`) read through `capOpt` (`SInv.vfh_capAt`). -/
theorem specGlob_disp {σ σb : Fl4Spec.State Unit} (hS : SInvG.SpecGlobS σ) {x x' : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hcm : Fl4Spec.tcbCnodeMap x' = Fl4Spec.tcbCnodeMap x)
    (ek : σb.kheap = Function.update σ.kheap σ.curThread (some (.tcb x')))
    (en : σb.interruptIrqNode = σ.interruptIrqNode) (ei : σb.idleThread = σ.idleThread) : SpecGlob σb := by
  have hcap : ∀ p c, capOpt (σb.kheap p) c = capOpt (σ.kheap p) c := by
    intro p c
    rw [ek]
    by_cases hp : p = σ.curThread
    · subst hp
      rw [Function.update_self, hk]
      show Fl4Spec.tcbCnodeMap x' c = Fl4Spec.tcbCnodeMap x c
      rw [hcm]
    · rw [Function.update_of_ne hp]
  have hc : ∀ p c a, capOpt (σb.kheap p) c = some a → SInvU.capAt σ (p, c) = some a := fun p c a h => by
    rw [SInv.vfh_capAt]; rw [hcap] at h; exact h
  have hfr : ∀ a, ¬ IsPageCap a → ¬ SInvG.IsFrameCap a := fun a h => h
  refine ⟨fun irq a ha => ?_, fun p cref a ha hn => ?_, fun p cref a ha hn => ?_⟩
  · rw [en] at ha
    exact hS.irq irq a (hc _ _ _ ha)
  · intro irq
    rw [en]
    exact hS.ref p cref a (hc _ _ _ ha) (hfr a hn) irq
  · rw [ei]
    exact hS.idle p cref a (hc _ _ _ ha) (hfr a hn)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAt` without the fields `SInvB`, `hQ` and `OffReady` supply** (module
docstring): `ni`, `ctnq`, `sg`, `rd0`, `vfh`, `cnf` removed; every other field as
`JEntryAt`'s (same tags). -/
structure JEntryAtR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `JEntryAt.stall`. -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] `JEntryAt.flags`. -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] `JEntryAt.epQ`. -/
  epQ : ∀ e, Sched.EpQPre σ e
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

theorem JEntryAtR.toAt {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (E : JEntryAtR (L := L) arI AR Z H Cs s ar σ) (ni : Entered σ) (ctnq : ∀ d q, σ.curThread ∉ σ.readyQueues d q)
    (sg : SpecGlob σ)
    (rd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (vfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (cnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none) :
    JEntryAt (L := L) arI AR Z H Cs s ar σ where
  ni := ni
  ctnq := ctnq
  sg := sg
  rd0 := rd0
  stall := E.stall
  flags := E.flags
  epQ := E.epQ
  handlers := E.handlers
  ports := E.ports
  ioapics := E.ioapics
  archIrq := E.archIrq
  vfh := vfh
  cnf := cnf
  vsTyp := E.vsTyp
  live := E.live
  fnz := E.fnz
  urz := E.urz
  utks := E.utks

variable (arI)

/-- **`KDispHypsKV26` with `JEntryAtR` and no `recv`** (module docstring). -/
structure KDispHypsKV27 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAtR (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAtR (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    (MidRun.JPerfRegHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
      MidRun.JPerfIrqSlotHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ) ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

/-- **`KFinAtR` without `fo`** (module docstring). -/
structure KFinAtR27 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  vt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

theorem KFinAtR27.toR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (F : KFinAtR27 (L := L) arI AR Z H Cs s a σ) (fo : FpuOwnOK σ) :
    KFinAtR (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.vt, F.arch, F.archNd, fo, F.sni, F.send, F.tail⟩

/-- **`KDispHypsKV26` at a dispatch state from `KDispHypsKV27`, `SInvB`, `hQ` and
`OffReady` at the `FaultIP` state** (module docstring). -/
theorem KDispHypsKV27.to26 (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit}
    (hS : SInvAll.SInvB σ) (hni : Entered σ) (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hOff : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hBA : BudgetAt σ σb true) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs D : Set U64} {s : S} {a : A} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV27 (L := L) arI AR MR Z H Cs D s a σb n c) :
    KDispHypsKV26 (L := L) arI AR MR Z H Cs D s a σb n c := by
  obtain ⟨x, hk, -⟩ := hS.1.2
  obtain ⟨⟨σu, hu, ebu⟩, ek, ect, en, ei, eq⟩ := BudgetAt.shape27 hnd hk hBA
  have hct : σ.curThread ≠ σ.idleThread := hni.1
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨hvfh, hcnf⟩ := SInvAll.sinvB_disp (x' := setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2))
    hS hct hk rfl rfl ek' ect
  have hOb : OffReady σb := by
    rw [ebu]
    exact SInvO.offReady_updateTimeStamp (σ := faultIPSt σ σ.curThread x) hS.1.1.vmt (hOff x hk) hu
  have hsg : SpecGlob σb :=
    specGlob_disp (x' := setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)) hS.1.1.sg hk rfl ek' en ei
  have hq : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect, eq]; exact hQ
  have hE : ∀ E : JEntryAtR (L := L) arI AR Z H Cs s a σb, JEntryAt (L := L) arI AR Z H Cs s a σb :=
    fun E => E.toAt (hBA.enteredP hnd hni) hq hsg hOb.rd0 hvfh hcnf
  refine ⟨fun ct call bl don hct' hi => ?_, fun _ _ _ => ⟨hq, hvfh⟩, fun ct rg sr cr hct' hm => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h.inv ct call bl don hct' hi
    exact ⟨a1, hE a2, a3, a4⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.mid ct rg sr cr hct' hm
    exact ⟨a1, hE a2, a3, a4, a5, a6⟩

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ26P` with the per-state spec premises from `SInvB`** (module
docstring). Removed: `hVI` (SInvB), `hB`'s `now` / `cur` / `tmo`, `JEntryAt`'s
`ni` / `ctnq` / `sg` / `rd0` / `vfh` / `cnf` and `recv` in `hK`, `KFinAtR.fo` in
`hFin`. Added: `hS : SInvB σ` (carried) and `hQ` [J] (l4v `ct_not_in_q` at σ). -/
theorem kernel_entryJ27 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV27 (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
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
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hct : σ.curThread ≠ σ.idleThread := hni.1
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  exact kernel_entryJ26P s a σ J hni hR hS.1.1.vim n c hn hflag
    (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to26 hnd hS hni hQ hB hBA)
    (fun x hx Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' J').toR (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
    hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
