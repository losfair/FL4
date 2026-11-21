/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr8): **`kernel_entryJ20P`**,
XTopJointKEntry19P's `kernel_entryJ19P` with no [W] invocation premise left:
the last case `JPreDecHypK PreKind18` [W] asked for (an Untyped cap retyping
a VT-x object, types 14..18) is out of the semantic scope, as XTopJointEntry's
`JVtxScope` [scope] already says for every other VT-x decode (lead decision,
mr7's open question). It is now asked as that scope premise, stated at
`MachPlat`'s preempted post:

* `JVtxScopeM` [scope]: `JVtxScope` with `JAtPreMV MR` as the preempted post.
* `JVtxHypM` [scope]: `JVtxScopeM` for an Untyped cap whose first argument is a
  VT-x object type (14..18), at the dispatch state, with exactly the decode
  facts `JPreDecHypK PreKind18` had (it replaces it field for field).
* `jPreDecHyp_of20`: `JPreDecHypK PreKind18` from `JVtxHypM` (an unfold:
  `PreKind18` names only those caps).
* `KDispHypsKV20` (`KDispHypsKV12 PreKind18` with `JVtxHypM`), `.to12`, NEW TOP
  `kernel_entryJ20P` (wrapper over J19P), `j20P_platform` (non-vacuity of the
  platform premises, unchanged: `j19P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry19P
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A VT-x cap's decode at `MachPlat`** [scope]: `JVtxScope` (XTopJointEntry)
with `JAtPreMV MR` as the preempted post. Same scope justification: outside
the semantic scope (DESIGN §9: the VCPU/EPT object families have no functional
refinement yet; P0 covers their extracted core), the cap's statement named.
The `MachPlat` form is needed because the one decode stated with it, an
Untyped retype to a VT-x type (`JVtxHypM`), may run the untyped reset, whose
preemption point can preempt: the preempted post must then carry the machine
facts (`MR`, `ValidMachineTime`, `ValidIrqMasks`) the `MachPlat` top needs,
and `XCapP.reXP` (which turns a `JAtPre` statement into a `JAtPreMV` one) only
applies to decodes that never preempt. -/
abbrev JVtxScopeM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c blk
    call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- **[scope] The VT-x Untyped retype at the dispatch state** (module
docstring): for an Untyped cap (RAM or device) whose first argument is a VT-x
object type (14..18), `JVtxScopeM`, given the decode's front-end facts (the
ones `JPreDecHypK PreKind18` took) and the machine facts at the dispatch
state. No l4v counterpart (l4v has no VT-x objects); the same scope as
`JUtPath.vtx` / `JDevPath.vtx` (`JVtxScope`), stated at `JAtPreMV`. -/
def JVtxHypM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ p sb fi dev, capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    ∀ x, argsU.head? = some x → 14 ≤ x.val → x.val < 19 →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPath (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct
      (.Untyped p sb fi dev) →
    JVtxScopeM (L := L) arI AR MR s ar σ lbl length (.Untyped p sb fi dev) blk call don fp buf extra slbl argsU ci sl
      excaps buffer ct

/-- **`KDispHypsKV12 PreKind18` with the scope premise `JVtxHypM`** (module
docstring). -/
structure KDispHypsKV20 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypM (L := L) arI AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp12 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JVtxHypM (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`JPreDecHypK PreKind18` from the scope premise** (an unfold). -/
theorem jPreDecHyp_of20 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} (h : JVtxHypM (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JPreDecHypK (L := L) arI PreKind18 AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hK excaps buffer
    hXO hXN hLb hA5 hN
  cases c
  case Untyped p sb fi dev =>
    obtain ⟨x, hx, h1, h2⟩ := hK
    exact h hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl p sb fi dev hc
      x hx h1 h2 excaps buffer hXO hXN hLb hA5 hN
  all_goals exact (show False from hK).elim

/-- **`KDispHypsKV12 PreKind18` from `KDispHypsKV20`**. -/
theorem KDispHypsKV20.to12 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV20 (L := L) arI AR MR Z H Cs D s a σ n c) :
    KDispHypsKV12 (L := L) arI PreKind18 AR MR Z H Cs D s a σ n c where
  inv := fun ct call bl don hct hi => by
    obtain ⟨h1, h2, h3, h4⟩ := h.inv ct call bl don hct hi
    exact ⟨h1, h2, h3, jPreDecHyp_of20 h4⟩
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, h6, jPreDecHyp_of20 h7⟩

set_option maxHeartbeats 4000000 in
/-- **The P line with no [W] invocation premise** (module docstring):
`kernel_entryJ19P` with `KDispHypsKV20` (the VT-x Untyped retype asked as the
scope premise `JVtxHypM`). -/
theorem kernel_entryJ20P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV20 (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
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
  kernel_entryJ19P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to12)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu

/-- **The platform premises of `kernel_entryJ20P` are satisfiable** (the same
as J19P's: `j19P_platform`). -/
theorem j20P_platform :
    MachPlat modelArch modelMR ∧ MRKeepD modelArch modelMR ∧
      ∀ (ms : Fl4Spec.MachineState) (i : Fl4Spec.Irq), gaiLine true ms = some i →
        modelArch.take_pending_irq ms ⦃ r => r.1 ≠ syscall.NO_IRQ ∧ r.1.val = i.toNat ⦄ :=
  j19P_platform

end

end

end Fl4Proofs.P3
