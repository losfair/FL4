/-
P3 (p3J gen 37): **the IrqHandler cap's decode leaf, for both classes** (one leaf, generic in the flags), with the
`ProjW` footprint of `delete_one` on a notification cap.

* **What the non-stable leaf asked** (XTopJointIrqL's `decode_invocation_irq_handlerJL`: `Entered`, `SpecGlob`,
  `PPR0`, `LiveDN` at the decode state) **is all at hand at a dispatch state**:
  `LiveDN` is a field of `JAtZ` itself (`JAtZ.live`, KENTRY-PLAN g2i; gen 36's handoff, written from the older
  `JEntryAt.live` chain, missed it); `Entered` / `SpecGlob` by gen 36's `dispEnteredSg`; `PPR0` by
  XTopJointCnDel's `JAtZ.ppr0_start` from `Entered`, the current thread in no ready queue (`SInvX.ctQ`, the queues
  kept by the front: `BudgetAt.shape27`) and `OffReady` at the dispatch state (`SInvX.offReady`, KEntry35's
  `offReady_faultIPSt`, SpecInvOffT's `offReady_updateTimeStamp` with `ValidMachineTime`): `ppr0_disp`.
* **The one input not derivable: the Ack's unmask.** FL4's `decode_irq_handler` (crates/fl4-core/src/interrupt.rs
  l.64-67) unmasks the cap's line (`a.mask_irq(irq, false)`); `MachPlatT.mask` relates an unmask only for a line
  `< 126` (IrqFixA: 126 / 127 are the IPI lines), while FL4's cap word bounds only `irq < 128` (`CapWf`). No
  carried invariant bounds a handler cap's line (IrqFixC's docstring: SpecInvG5's `SpecIrqH` was never proved
  preserved). Taken as **`SpecIrqB` [J]** (l4v `valid_cap`'s `irq ≤ maxIRQ` for every handler cap of the spec
  CSpace — only the bound, not `valid_irq_handlers`' activity part), at the entry state, carried to the dispatch
  state by `irqB_disp` (the front rewrites only the current TCB's registers). True on every reachable state: FL4
  creates handler caps only in `invoke_irq_control` (interrupt.rs l.47-50), reached from `decode_irq_control`
  with `irq ≤ USER_MAX − USER_MIN` then `+ USER_MIN` (arch/x86_64/interrupt.rs l.19-22: `irq ≤ 123`) or
  `irq ≤ ISA_MAX = 15` (l.48-50); copies keep the line (objects.rs l.104); boot creates none. `maxIRQ = 125`.
* **`P1.fin_cap_ntfn.kwN0`** (P3JNtfnFt) + `Sched.empty_ws` (every word written a slot word of the typed heap,
  `slotWd_range`, P3JStepFt's `JAtZ.inSlotProjW`): **`delete_one_ntfnProjW`**, `delete_one` of a notification cap
  at `WJL` writes only `ProjW`.
* **`IrqSteps.jatZW`**: `IrqSteps` (StepSem steps, or restart + notification deletion + steps) from a `JAtZ` state
  ends at `JAtZ (Z.mv G' V')` with the `ProjW` footprint (`Steps.jatZW`, `WJL.restart`, `delete_oneJL`,
  `delete_one_ntfnProjW`, `Det.detAt_capDeleteOne_ntfn` as XTopJointIrqL's `IrqSteps.jat`).
* **`decIrqSt`** (any flags): XTopIrqH's `decode_invocation_irq_handlerXSD` at
  `X := JStab (Z.mv Z.G V') H Cs ∧ WritesIn s' · (ProjW H Cs s')`, `MR` by IrqFixGenB's transported `XCapP.mrG`
  (KEntry39's route: `MKD.decode_irq_handler_mr`, `perfF_irqH`), the unmask by `MachPlatT.mask` at `irq ≤ 125`.
  **`midDecIrq_of`**, **`invDecIrq_of`**; `midDecRest_of_irq` / `invDecRest_of_irq` (gen 36's `IsRestCap`
  predicates from the IrqHandler leaf and `IsRestCap3`: CNode, Thread, SchedContext).
* **`DispStabFootLq` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap3`, midSpec, midRecvSw (verbatim),
  irqB (`SpecIrqB` at the entry state)}; **`dispStabFootLo_of_Lq`**; top **`kernel_entry_runMcWKR_sysLq`**
  (globals as `_sysLo`).

Premise honesty: `DispStabFootLq`'s four decode / spec fields are `DispStabFootLo`'s at a smaller cap predicate or
verbatim (implied by `DispStabFootLo`); `irqB` is new and not implied by `DispStabFootLo` (a spec invariant, l4v
`valid_cap`, justified above). So `DispStabFootLq` is implied by `DispStabFootLo ∧ SpecIrqB σ`, and implies
`DispStabFootLo` (`dispStabFootLo_of_Lq`).

Named premises: `DispStabFootLq` [J], `SpecIrqB` [J] (its field). No sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JNtfnFt
import Fl4Proofs.P3.P3JCapDom
import Fl4Proofs.P3.XTopJointIrqL
import Fl4Proofs.P3.JBootIpi
import Fl4Proofs.P3.ScInstFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 37) **`SpecIrqB` [J]**: l4v `valid_cap`'s bound for the IRQ handler caps — every handler cap held in
the spec's CSpace is for a line `≤ maxIRQ` (module docstring). -/
def SpecIrqB (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p cref (i : Fl4Spec.Irq), capOpt (σ.kheap p) cref = some (.irqHandlerCap i) → i.toNat ≤ Fl4Spec.maxIRQ.toNat

/-- (p3J gen 37) `SpecIrqB` across the syscall front (the current TCB's registers only). -/
theorem irqB_disp (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hX : SInvX σ)
    (hBA : BudgetAt σ σb true) (h : SpecIrqB σ) : SpecIrqB σb := by
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  obtain ⟨-, ek, -, -, -, -⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  intro p cref i hc
  rw [ek'] at hc
  by_cases e : p = σ.curThread
  · subst e
    rw [Function.update_self] at hc
    exact h _ cref i (by rw [hk0]; exact hc)
  · rw [Function.update_of_ne e] at hc
    exact h p cref i hc

/-- (p3J gen 37) A handler cap's line at a `SpecIrqB` state is `≤ 125` (`maxIRQ`). -/
theorem irq125_of {σb : Fl4Spec.State Unit} (hB : SpecIrqB σb) (sl : Fl4Spec.CslotPtr) {irq : U64}
    (hirq : irq.val < 128)
    (hget : Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap (.IrqHandler irq), σb)}, False)) : irq.val ≤ 125 := by
  obtain ⟨o, i⟩ := sl
  have h := hB o i (BitVec.ofNat 8 irq.val) ((getCap_set_iff σb o i _).1 (congrArg Prod.fst hget))
  have e : Fl4Spec.maxIRQ.toNat = 125 := rfl
  have e2 : (BitVec.ofNat 8 irq.val).toNat = irq.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (lt_of_lt_of_le hirq (by norm_num))
  rw [e, e2] at h
  exact h

/-- (p3J gen 37) **`PPR0` at a dispatch state** (module docstring). -/
theorem ppr0_disp {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {s : S} {a : A} (hX : SInvX σ)
    (hBA : BudgetAt σ σb true) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σb) (hnib : Entered σb) :
    PPR0 σb := by
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  obtain ⟨⟨σu, hu, ebu⟩, -, ect, -, -, eq⟩ := BudgetAt.shape27 hnd hk0 hBA
  have hOb : OffReady σb := by
    rw [ebu]
    exact SInvO.offReady_updateTimeStamp (σ := faultIPSt σ σ.curThread x0) hX.sb.1.1.vmt
      (offReady_faultIPSt hX.offReady) hu
  have hq : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect, eq]; exact hX.ctQ
  exact J.ppr0_start arI hnib hOb.rd0 hq

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 37) **`delete_one` of a notification cap at `WJL` writes only `ProjW`** (module docstring). -/
theorem delete_one_ntfnProjW [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} (hDS : DState (L := L) Z.th s σ G)
    (hW : WJL (L := L) arI AR Z H Cs kb s a σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64}
    {w r : Bool} (hk : capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ res => P1.WritesIn st s res.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨V, Ac0, Lst0, D0, J, -⟩ := hW.1
  have hP : Placed Z.th := J.xtop.rel.1
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rw [hcv] at hk; subst hk
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full Z.th hP s σ G sl _ hDS hA hc hcn
  have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
  rw [hbf2 hNF] at hbf
  rw [is_final_with_cap_eq _ _ _ hc, hbf]; simp only [bind_ok]
  rw [← finalise_cap_ntfn arI s a p b w r _ false]
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨hpN, hHp⟩ := (hJ.typed _ hA.isSlot).2.1 p b w r hcv
  have h0 := J.blk.1.choose_spec.choose_spec
  apply WP.spec_bind (WP.spec_and (jFinNtfnK arI Z H Cs kb rfl s a σ G sl p b w r hDS (hW.1.wj arI) hA hc)
    (P1.fin_cap_ntfn.kwN0 (ar := arI) s a p b w r _ false J.blk hpN hHp))
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨hrem, hcl, σ1, G1, hmem, hDS1, hkeep, -⟩, F⟩
  simp only at hrem hcl hDS1 hkeep F
  subst hcl
  simp only [uncurry_apply_pair]
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) :=
    (P1.WritesA.w F).mono fun b hb => Mc.kwN_projW J.kern.heap h0.nodes hb
  have hxs : IsSlot Z.th (cslotAddr sl) := hA.isSlot
  have hM1 := hDS1.1.2.2.1
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Notification p b w r := by rw [hkeep _ hxs, hcv]
  have hxm : cslotAddr sl ∈ G1.chains.flatten :=
    (hM1.members _).2 ⟨hxs, _, capAt_capV _ _, by rw [hcv1]; simp⟩
  have hslot : ∀ y ∈ G1.chains.flatten, IsSlot Z.th y := fun y hy => ((hM1.members y).1 hy).1
  refine WP.spec_mono (Sched.empty_ws (ar := arI) hP s1 a1 (cslotAddr sl) hxs ?_ ?_) fun r hr =>
    W1.trans1 ((hr.mono fun b hb => slotWd_range hP hb).mono fun b hb => J.inSlotProjW hb)
  · by_cases hp0 : prevOf (L.mem s1) (cslotAddr sl) = 0#u64
    · exact Or.inl hp0
    · exact Or.inr (hslot _ (hM1.prev_link hxm hp0).1)
  · rcases hM1.next_mem hxm with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr (hslot _ h1)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 37) **`JAtZ` and the `ProjW` footprint after an IRQ handler invocation's run** (module docstring). -/
theorem IrqSteps.jatZW [Fl4Proofs.P1.PlainStore st] (hAM : ARMask arI AR) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (h : IrqSteps (L := L) arI Z.th s ar σ s' a' σ') :
    (∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ') ∧
    P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) := by
  rcases h with h | ⟨ct, s2, σ1, sl, p, b, w, r, s3, a3, σ3, hct, hs2, hst, h1, hA, -, hk, hd, hm, h2⟩
  · obtain ⟨⟨G', V', Ac', Lst', D', J', -⟩, hw⟩ := Steps.jatZW arI hAM (jStepHyps arI) h rfl J (J.zNoBlk hsg)
    exact ⟨⟨G', V', Ac', Lst', D', J'⟩, hw⟩
  have hW := WJL.restart arI J hni hsg hP0 J.live hct s2 σ1 hs2 hst
  obtain ⟨-, W1⟩ := Steps.jatZW arI hAM (jStepHyps arI) h1 rfl J (J.zNoBlk hsg)
  have hDS2 : DState (L := L) Z.th s2 σ1 Z.G := by
    obtain ⟨⟨V, Ac2, Lst2, D2, J2, -⟩, -⟩ := hW
    exact ⟨J2.xtop.rel.2.1, J2.del, J2.xtop.rel.2.2.1⟩
  have hd' := delete_oneJL arI Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G hDS2 hW hA hk
  have hdW := delete_one_ntfnProjW arI Z H Cs (L.ksb s) hDS2 hW hA hk
  rw [hd, WP.spec_ok] at hd' hdW
  obtain ⟨σ4, G4, hm4, -, -, -, -, hW4⟩ := hd'
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS2.1.1.abs_cap hA
  rw [hca.abs] at hg
  rw [capV_of_capAt hc] at hk; subst hk
  have e := (Det.detAt_capDeleteOne_ntfn hg).eq hm4 hm
  have e2 : σ4 = σ3 := congrArg Prod.snd e
  subst e2
  obtain ⟨⟨V4, Ac4, Lst4, D4, J4, -, -, hsg4, -⟩, -⟩ := hW4
  obtain ⟨⟨G', V', Ac', Lst', D', J', -⟩, W3⟩ :=
    Steps.jatZW arI hAM (jStepHyps arI) h2 (Z := Z.mv G4 V4) rfl J4 (J4.zNoBlk hsg4)
  exact ⟨⟨G', V', Ac', Lst', D', J'⟩, W1.projW_trans (hdW.projW_trans W3)⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 37) **The IrqHandler cap's decode at a dispatch state, any flags** (module docstring). -/
theorem decIrqSt [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsg : SpecGlob σb)
    (hP0 : PPR0 σb) (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {irq : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.IrqHandler irq)) (hB : SpecIrqB σb)
    (hget : Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap (.IrqHandler irq), σb)}, False))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs) (args : List Fl4Spec.Data) (bl call don fp : Bool)
    (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.IrqHandler irq) bl call don fp buf e mi.miLabel
      args ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb : Z.th ct = some .tcb := (hX.curTcb hcur).1
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc := capV_of_capAt hc
  have hirq : irq.val < 128 := (slot_cap_wf hX hAs hsc).1
  have h125 := irq125_of hB sl hirq hget
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  have hXN : ExtraNamed Z.th (L.mem s') e := by
    have h := lookup_extra_named Z.th s' σb J.dstate.1.1 J.dstate.1.2.1 htcb buf info
    rw [hr2, WP.spec_ok] at h
    exact h e he
  rw [← hLb]
  refine Fl4Proofs.P3.XCapP.mrG
    (f := fun ms => if info.label = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) hMT ?_
    (MKD.decode_irq_handler_mr L.total hA hKD (hMT.mask a' irq false _ hMb (by simp; omega)) hMb)
    (perfF_irqH irq hirq info.label σb bl call don fp _ ci sl exs buffer)
  obtain ⟨sl', hl', hd⟩ := irqH_canon info.label
  refine XCapP.lbl_congr arI (specDec_irqH irq hd) ?_
  refine XCap.toPN arI ?_ (specDec_noPreK (by trivial))
  have hex : info.label.val = 35 → ExtraSRel Z.th (L.mem s') (exAt e 0) exs :=
    fun _ => ExtraOK.relS hX.rel.1 (hXO e exs he hexs)
  have hxn : info.label.val = 35 → exAt e 0 ≠ nodeA (L.ksb s') irq := fun _ => J.irqExtraNe hsg hXN hirq
  exact decode_invocation_irq_handlerXSD arI (Z := Z.mv Z.G V') Z.th hX.rel.1 s' a' σb Z.G J.dstate J.intL
    hX.fin.1.1.2.2.2.1 info.label sl' hl' ct hct hcur htcb J.kern.act (maskIrq_total arI hA) irq hirq
    (irqSlotOK_of_spec J.intL J.dstate.1.1 hX.fin.1.1.2.2.2.1 hsg.irqNode hirq)
    (irqDelOKJL arI J hnib hsg hP0 J.live hct irq hirq) (irqDelDKJ arI (jStepHyps arI) J hnib hsg hct irq hirq)
    e _ (exAt_idx0 e) exs hex hxn hX.rel.2.2.2.2.1 J.domPlaced (J.irqDelP1J hnib hct hirq) rfl hX
    (J.curRun.run hnib) _ hX0
    (fun _ _ _ h => by
      obtain ⟨⟨G', V'', Ac'', Lst'', D'', J'⟩, hw⟩ := IrqSteps.jatZW arI hARI.toMask J hnib hsg hP0 h
      exact ⟨⟨G', V'', Ac'', Lst'', D'', J'⟩, hw⟩)
    (fun _ _ _ h => by obtain ⟨⟨_, _, _, _, _, J'⟩, -⟩ := h; exact ⟨_, J'.xtop⟩)
    (msgLen info buf) (cslotAddr sl) buf bl call don fp args ci sl buffer

end

end

end Fl4Proofs.P3
