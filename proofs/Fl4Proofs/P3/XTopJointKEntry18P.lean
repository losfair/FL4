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
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPD : JPreDecHypK (L := L) arI PreKind18 AR MR Z H Cs D s ar σ ct) :
    JPreDecHypK (L := L) arI PreKind17 AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hK excaps buffer
    hXO hXN hLb hA5 hN
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hPl : Placed Z.th := J.xtop.rel.1
  have hsc : capV (L.mem s) (cslotAddr sl) = c := capV_of_capAt hc
  have hni := hE.ni
  have hLv := hE.live
  cases c
  case Thread p =>
    obtain ⟨hEpt, hN⟩ := hN
    by_cases hn : lbl = fl4_abi.label.TCBSetEPTRoot
    · -- SetEPTRoot [scope] (`JVtxScope`, at `JAtPre`): no installing label, so no preemption (`XCapP.reXP`)
      have hx := hEpt hn
      subst hLb
      obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon lbl
      refine XCapP.reXP (arI := arI) hx fun inv hD => ?_
      rw [specDec_thread p hd] at hD
      have e : lbl.val = fl4_abi.label.TCBSetEPTRoot.val := by rw [hn]
      exact thread_noPre_of hlbl ⟨by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot],
        by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot], by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot],
        by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot], by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot]⟩ inv hD
    have hFr := (hN hn).hFr
    subst hLb
    obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon lbl
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    have hx0 := exAt_idx0 extra
    have hx1 := exAt_idx1 extra
    have hx2 := exAt_idx2 extra
    have hXc := ExtraOK.xc hPl hXO
    -- the untyped extra caps' children at their abstract names: CRel's
    -- `MdbLinks`/`CdtRel`/`MdbInv.parentAdj` (`noChildren_of_adj`)
    have hnc : NcHyp (st := st) Z.th s σ (exAt extra 0) (exAt extra 1) (exAt extra 2) := by
      obtain ⟨-, -, hM, hC, hI⟩ := J.dstate.1
      intro x _ sl0 hAs0 hx hu
      subst hx
      refine noChildren_of_adj Z.th hPl s σ Z.G hM hC (hI.parentAdj (th := Z.th)) sl0 hAs0
        ((hM.members _).2 ⟨hAs0.isSlot, capV (L.mem s) (cslotAddr sl0), capAt_capV _ _, ?_⟩)
      intro h0; rw [h0] at hu; simp [isUt] at hu
    have hnc0 : ∀ sl0 : Fl4Spec.CslotPtr, AbsSlot Z.th sl0 → exAt extra 0 = cslotAddr sl0 →
        isUt (capV (L.mem s) (exAt extra 0)) = true → NoChildrenRel (st := st) s σ (exAt extra 0) sl0 :=
      fun sl0 hA h hu => hnc _ (by simp) sl0 hA h hu
    have hcapC : exAt extra 1 ≠ 0#u64 → ∀ q b, capV (L.mem s) (exAt extra 1) = .SchedContext q b → q ∈ Z.C := by
      -- the slot `XcRel` names, a slot of a CNode of `Z.th` (`JAtZ.scCtxCap`)
      intro h1 q b hq
      obtain ⟨hz, he⟩ := hXc.2 1 _ rfl
      rcases hee : excaps[1]? with _ | e
      · exact absurd (hz.2 (List.getElem?_eq_none_iff.1 hee)) h1
      · obtain ⟨ex, -, ps, hps, hps1⟩ := he e hee
        have hAs1 : AbsSlot Z.th e.2 := ⟨ps, hps1, Or.inl hps⟩
        rw [ex] at hq
        exact (J.scCtxCap arI hAs1.isSlot (by rw [capAt_capV, hq])).1
    have hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
        q ≠ L.idleW s := by
      -- no cap but a frame cap names the idle thread (`SpecGlob.idle`)
      intro sl' q hAs' hsc' e
      obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hAs'
      rw [capAt_capV, hsc'] at hc0; cases eq_of_ok_eq hc0
      rw [hca0.abs] at hg0
      have ha0 := (getCap_set_iff σ sl'.1 sl'.2 _).1 (congrArg Prod.fst hg0)
      apply hE.sg.idle sl'.1 sl'.2 _ ha0 (by simp [IsPageCap, absCap])
      rw [JAtZ.idleThread_eq arI J, ← e]; simp [absCap, Fl4Spec.objRefs]
    have hpI : p ≠ L.idleW s := hidS sl p hAs hsc
    exact decode_invocation_threadJ_stepM arI s ar σ J hni hG.ari hG.tot hE.flags hE.fnz lbl length p blk call don fp buf extra ct hct sl' hlbl argsU hlen hargs ci sl
      hAs hsc excaps buffer hext hE.stall hn J.cwOut hpI _ _ _ hx0 hx1 hx2 hXc hnc hnc0 hcapC hA5 (getBpHyp_of s ct p)
      (fun h => hFr h _ hx0) hG.ppA.minBudget hidS hbuf hl hG.delParts hE.sg hLv hG.nd hM hKD hG.ppA ⟨hR, hVT, hVI⟩ hE.rd0 hE.ctnq hG.timeAg
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
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ17P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').toK fun ct hct hG hE hPD =>
        jPreDecHyp_of18 J' hct hG hE hM hKD hPD)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
