/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **`kernel_entryJ18P`**,
XTopJointKEntry17P's `kernel_entryJ17P` with the Thread invocation taken out
of `JPreDecHypK` [W]: the five installing labels run the deletion loop at
`MachPlat` (XTopJointMRTcb, XTopJointMRTcbL), so the Thread cap's decode is
proved at `JAtPreMV`.

* `PreKind18`: an Untyped cap whose first argument is a VT-x object type
  (14..18, `JUtPath.vtx` [scope]); nothing else.
* `jPreDecHyp_of18`: `JPreDecHypK PreKind17` from `JPreDecHypK PreKind18` at a
  `JAtZ` dispatch state: the Thread cap as XTopJointEntry's `decOK_J` does
  (generated: scratch/mr7/gen18.py + t18.lean), by XTopJointMRTcbL's
  `decode_invocation_threadJ_stepM` (`MRV` at the dispatch state from
  `JPreDecHypK`'s own premises, `MachPlat`, `MRKeepD`, `JEntryGlobM.ppA`);
  SetEPTRoot ([scope] `JVtxScope`, stated at `JAtPre`) by `XCapP.reXP`: its
  spec decode is no installing label, so it never preempts.
* `kernel_entryJ18P`: J17P with `KDispHypsKV7 PreKind18`.
-/
import Fl4Proofs.P3.XTopJointKEntry17P
import Fl4Proofs.P3.XTopJointMRTcbL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The caps `JPreDecHypK` is still asked for after mr7's Thread step**
(module docstring): an Untyped cap at a VT-x object type. -/
def PreKind18 : capability.Cap → List U64 → Prop
  | .Untyped .., argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _ => False

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`JPreDecHypK` without the Thread invocation** (module docstring). -/
theorem jPreDecHyp_of18 [Fl4Proofs.P1.PlainStore st] {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z s ar σ) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPD : JPreDecHypK (L := L) arI PreKind18 AR MR Z H Cs D s ar σ ct) :
    JPreDecHypK (L := L) arI PreKind17 AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hK excaps buffer
    hXO hXN hLb hA5 hN
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hPl : Placed Z.th := J.xtop.rel.1
  have hsc : capV (L.mem s) (cslotAddr sl) = c := capV_of_capAt hc
  have hni := hE.ni
  have hLv := hE.live H Cs Ac Lst D J
  cases c
@THREAD@
  case Untyped p sb fi dev =>
    exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc hK
      excaps buffer hXO hXN hLb hA5 hN
  all_goals exact (show False from hK).elim

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The kernel entry with the Thread installs proved under `MachPlat`**
(module docstring): `kernel_entryJ17P` with `KDispHypsKV7 PreKind18`. -/
theorem kernel_entryJ18P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV7 (L := L) arI PreKind18 AR MR Z' H' Cs' D' s' a' σb n c)
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
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ17P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').toK fun ct hct hG hE hPD =>
        jPreDecHyp_of18 J' hct hG hE hM hKD hPD)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
