/-
P3 (DESIGN.md §9), invariant line G2 (g2b): **`kernel_entryJ32`**, the newest
top. Its premise list is `kernel_entryJ31`'s, except that the bundles inside
`hK` no longer hold the ∀-state `JThreadFinHypsU.obj` ([S]: at EVERY `JAtZ`
state of the typed heap, a slot's `Thread p` cap has `p`'s VCPU word zero).

g2b carries that word in `JAtZ.ext` (`JExt.vw`: every TCB of the typed heap
has its VCPU word `tVcpuA t` (offset 3664) zero). FL4 writes the word only in
`vcpu::detach` (0) and `X86VCPUSetTCB` (a Vcpu cap's invocation, excluded by
`JExt.nat`), and a TCB's creation leaves it zero (`InT` excludes it), so
every native step keeps it; the frames take `VKeep` from each step's
footprint (`TFoot`, `FinW`, `CnW`, `RmW`, `KsW`, `SchW`, `DbgWc`, `TmW`, slot
words, the retype windows).

* `jThrObj_ofExt`: `JThreadFinHypsU.obj` with no premise (a slot's `Thread p`
  names a TCB of the typed heap, `SlotsValid.abs`; then `J.ext.vw`).
* `JDelPartsN32`: `JDelPartsN` without `thr.obj` (`archRef`, `arKeep`,
  `ticks` [P]); `.toN`.
* `JEntryGlobM32` / `KDispHypsKV32`: with `JDelPartsN32`; `.to31`.
* `kernel_entryJ32`: `kernel_entryJ31` with `hK` giving `KDispHypsKV32`. No
  premise added.
-/
import Fl4Proofs.P3.XTopJointKEntry31
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JThreadFinHypsU.obj` is a theorem** (g2b): at a `JAtZ` state, a slot's
`Thread p` cap is valid (`SlotsValid`: `p` a TCB of the typed heap), and
`JExt.vw` makes that TCB's VCPU word zero. -/
theorem jThrObj_ofExt (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) :
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
      ∀ (x p : U64), IsSlot Z.th x → capV (L.mem s) x = .Thread p →
        L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64 := by
  intro Z H Cs Ac Lst D s a σ _ J x p hx hc
  obtain ⟨sl, hA, rfl⟩ := hx.abs
  have hv : CapValid Z.th (.Thread p) := J.dstate.1.2.1.abs hA (by rw [← hc]; exact capAt_capV _ _)
  exact J.ext.vw p hv

/-- **`JDelPartsN` without `thr.obj`** (module docstring). -/
structure JDelPartsN32 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [P] `JDelParts.archRef`. -/
  archRef : ArchRefines arI AR
  /-- [P] `JDelParts.arKeep`. -/
  arKeep : ARKeep arI AR
  /-- [P] `JThreadFinHypsU.ticks`. -/
  ticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
    ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄

/-- **`JEntryGlobM31` with `JDelPartsN32`** (module docstring). -/
structure JEntryGlobM32 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  ari : ARIface arI AR
  tot : P0.ArchTotal arI
  delParts : JDelPartsN32 arI AR th
  nd : Fl4Spec.numDomains = 1
  ppA : PPPlatA arI AR
  dom : DomConfig
  portIn : PortInVal arI
  timeAg : TimeAgree arI
  maxTU : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄

/-- **`KDispHypsKV31` with `JEntryGlobM32`** (module docstring). -/
structure KDispHypsKV32 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM32 arI AR Z.th ∧ JEntryAtR2 (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM32 arI AR Z.th ∧ JEntryAtR2 (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI}

/-- `JDelPartsN` from `JDelPartsN32`: `thr.obj` by `jThrObj_ofExt` (g2b). -/
theorem JDelPartsN32.toN {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (h : JDelPartsN32 arI AR th) :
    JDelPartsN (L := L) arI AR th :=
  ⟨h.archRef, h.arKeep, ⟨jThrObj_ofExt (L := L) arI AR th, h.ticks⟩⟩

theorem JEntryGlobM32.to31 {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (h : JEntryGlobM32 arI AR th) :
    JEntryGlobM31 (L := L) arI AR th :=
  ⟨h.ari, h.tot, h.delParts.toN, h.nd, h.ppA, h.dom, h.portIn, h.timeAg, h.maxTU, h.tu⟩

theorem KDispHypsKV32.to31 {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV32 (L := L) arI AR MR Z H Cs D s a σ n c) : KDispHypsKV31 (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hI => let ⟨g, e, p, v⟩ := h.inv ct call bl don hct hI; ⟨g.to31, e, p, v⟩,
    fun ct rg sr cr hct hM => let ⟨g, e, p, v⟩ := h.mid ct rg sr cr hct hM; ⟨g.to31, e, p, v⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ31`'s premises, with
the bundles inside `hK` (`KDispHypsKV32`) free of the ∀-state
`JThreadFinHypsU.obj`. -/
theorem kernel_entryJ32 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV32 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
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
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ31 s a σ J hni hR hS hE hQ n c hn hflag hB
    (fun σb hBA V' Ac' Lst' D' s' a' hF J' => (hK σb hBA V' Ac' Lst' D' s' a' hF J').to31)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu

end

end

end Fl4Proofs.P3
