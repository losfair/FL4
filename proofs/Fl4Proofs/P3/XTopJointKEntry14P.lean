/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr5): **`kernel_entryJ14P`**,
XTopJointKEntry13P's `kernel_entryJ13P` with the Untyped invocation taken out
of `JPreDecHyp` [W] (mr4 NEXT (1)).

* `JPreDecHypK K`: `JPreDecHyp` asked only for the caps `K c argsU` names
  (`JPreDecHyp` is `JPreDecHypK (fun c _ => NoPreKind c → False)` by
  definition); `KDispHypsK K` = `KDispHyps13P` with `JPreDecHypK K`;
  `KDispHypsK.to` (a stronger family premise from a weaker one at each
  dispatch state), `KDispHypsK.to13P`.
* `PreKind14`: CNode and Thread caps, and an Untyped cap whose first argument
  is a VT-x object type (14..18; those are `JUtPath.vtx` [scope] anyway, stated
  at `JAtPre`, so they stay here).
* `jPreDecHyp_of14`: `JPreDecHyp` from `JPreDecHypK PreKind14` at a `JAtZ`
  dispatch state: the Untyped cap by UtRetResetJM's `decode_invocation_untypedJM`
  with `JAtZ.jUtRetHypM` (RAM: the reset under `MachPlat`, `reset_loopJM`) or
  `JAtZ.jUtRetHypDevM` (device: never preempted), from the cap's `JPath`.
* `kernel_entryJ14P`: `kernel_entryJ13P` with `KDispHypsK PreKind14`;
  `j14P_platform` (non-vacuity of the platform premises, as `j13P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry13P
import Fl4Proofs.P3.UtRetResetJM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] `JPreDecHyp` asked only for the caps `K` names** (module docstring). -/
def JPreDecHypK (K : capability.Cap → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c → K c argsU →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPath (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c blk call
      don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- **The caps `JPreDecHyp` is still asked for after mr5 step 1** (module
docstring): CNode, Thread, and an Untyped cap at a VT-x object type. -/
def PreKind14 : capability.Cap → List U64 → Prop
  | .CNode .., _ => True
  | .Thread _, _ => True
  | .Untyped .., argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _ => False

/-- **The dispatch premises with `JPreDecHypK K`** (`KDispHyps13P` is
`KDispHypsK (fun c _ => NoPreKind c → False)`). -/
structure KDispHypsK (K : capability.Cap → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp6 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct
  vmt : ValidMachineTime σ

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **A dispatch premise from a narrower one**, the family premise converted
at each dispatch state. -/
theorem KDispHypsK.to {K K' : capability.Cap → List U64 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (hK : KDispHypsK (L := L) arI K AR MR Z H Cs D s a σ n c)
    (hc : ∀ ct, sched.cur_thread st s = ok ct → JEntryGlobM (L := L) arI AR Z.th → JEntryAt (L := L) arI AR Z H Cs s a σ →
      JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct → JPreDecHypK (L := L) arI K' AR MR Z H Cs D s a σ ct) :
    KDispHypsK (L := L) arI K' AR MR Z H Cs D s a σ n c where
  inv ct call bl don hct hi := by
    obtain ⟨hG, hE, hP, hPD⟩ := hK.inv ct call bl don hct hi
    exact ⟨hG, hE, hP, hc ct hct hG hE hPD⟩
  recv := hK.recv
  mid ct rg sr cr hct hm := by
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid ct rg sr cr hct hm
    exact ⟨hG, hE, hP, hW, hV, hS6, hc ct hct hG hE hPD⟩
  vmt := hK.vmt

theorem KDispHypsK.to13P {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (hK : KDispHypsK (L := L) arI (fun c _ => NoPreKind c → False) AR MR Z H Cs D s a σ n c) :
    KDispHyps13P (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨hK.inv, hK.recv, hK.mid, hK.vmt⟩

set_option maxHeartbeats 4000000 in
/-- **`JPreDecHyp` without the Untyped invocation** (module docstring). -/
theorem jPreDecHyp_of14 [Fl4Proofs.P1.PlainStore st] {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ) (hM : MachPlat arI MR)
    (hPD : JPreDecHypK (L := L) arI PreKind14 AR MR Z H Cs D s ar σ ct) :
    JPreDecHypK (L := L) arI (fun c _ => NoPreKind c → False) AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hK excaps buffer
    hXO hXN hLb hA5 hN
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hPl : Placed Z.th := J.xtop.rel.1
  have hN0 := hN
  cases c
  case CNode p r gs g =>
    exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc trivial
      excaps buffer hXO hXN hLb hA5 hN
  case Thread p =>
    exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc trivial
      excaps buffer hXO hXN hLb hA5 hN
  case Untyped p sb fi dev =>
    by_cases hv : ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
    · exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc hv
        excaps buffer hXO hXN hLb hA5 hN0
    have hNat : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val :=
      fun x hx => Classical.byContradiction fun hn => hv ⟨x, hx, by omega, by omega⟩
    obtain ⟨hDv, hU⟩ := hN
    have hex := ExtraOK.rel1 hPl hXO
    have hx0 := exAt_idx0 extra
    generalize exAt extra 0 = x0 at hex hx0
    cases dev
    · have hN := hU rfl
      exact decode_invocation_untypedJM s ar σ J lbl slbl (by rw [← hLb]; exact genInvocationType_untyped_iff lbl)
        length buf ct hct argsU hlen hargs hNat sl hAs p sb fi hc extra x0 hx0 excaps hex hN.fan blk call don fp ci
        buffer (J.jUtRetHypM hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0 hG.ari.toARKeep hG.tot hG.nd
          hM hG.ppA hN.rcb hE.rd0 hE.ctnq hN.vsReach hE.urz hE.utks hR hVT hVI hNat)
    · have hN := hDv rfl
      exact decode_invocation_untypedJM s ar σ J lbl slbl (by rw [← hLb]; exact genInvocationType_untyped_iff lbl)
        length buf ct hct argsU hlen hargs hNat sl hAs p sb fi hc extra x0 hx0 excaps hex hN.fan blk call don fp ci
        buffer (J.jUtRetHypDevM hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0 hN.devApart hN.devFree
          hN.devGpm hN.rcb hN.vsReach)
  all_goals exact (hK trivial).elim

set_option maxHeartbeats 4000000 in
/-- **The kernel entry with the Untyped invocation proved under `MachPlat`**
(module docstring): `kernel_entryJ13P` with `KDispHypsK PreKind14`. -/
theorem kernel_entryJ14P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsK (L := L) arI PreKind14 AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ13P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => ((hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to
      fun _ hct hG hE hPD => jPreDecHyp_of14 J' hct hG hE hM hPD).to13P)
    hFin hARI hA hnd hM hMK hPA hIA hmrt hmb hNS hNSR hT hmax htu

/-- **The platform premises of `kernel_entryJ14P` are satisfiable** by a
platform that raises interrupts (`j13P_platform`: the same platform premises). -/
theorem j14P_platform :
    MachPlat modelArch modelMR ∧ MRKeep modelArch modelMR ∧
      ∀ (ms : Fl4Spec.MachineState) (i : Fl4Spec.Irq), gaiLine true ms = some i →
        modelArch.take_pending_irq ms ⦃ r => r.1 ≠ syscall.NO_IRQ ∧ r.1.val = i.toNat ⦄ :=
  j13P_platform

end

end

end Fl4Proofs.P3
