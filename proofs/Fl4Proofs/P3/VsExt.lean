/-
P3 (DESIGN.md §9), VSpace: **the l4h VSpace extensions** against the
Fl4Spec/Ext/VSpace model.

* `frame_getaddr_rel`: Frame `GetAddress` against l4v's decode, `Restart`,
  `perform_page_invocation` (the frame's physical address) and the reply of
  `handle_invocation` (`replyRunning`; FL4's `reply1` against it is the
  hypothesis `VsReplyHyps.reply`, the IPC-buffer and register part of
  replies, outside VSpace);
* `pml4_flush_rel` (l4h 0017): FL4's `vspace::decode` on a PML4 cap with
  label `X86PML4Flush` against `decodePml4Flush`, `Restart` and
  `performPml4Flush` (FL4's `invalidate_asid` matched by an outcome of l4v's
  `flush_all`, as for `unmap_pd`).
-/
import Fl4Proofs.P3.Vs
import Fl4Spec.Ext.VSpace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The hypotheses of the PML4 flush. -/
structure VsFlushHyps (A : Type) (ar : machine.Arch A) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), UR st th P L4 L3 L2 L1 SR s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      UR st th P L4 L3 L2 L1 SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ⦄
  flushAllOK : ∀ (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid),
    ¬ (Fl4Spec.flushAll (Z := Unit) vs asid σ).2
  flushAllH : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ → ar.invalidate_asid a asid ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.flushAll (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄

/-- The reply of `handle_invocation` after a successful invocation:
`reply_from_kernel` when the caller called, then `Running`. -/
def replyRunning (t : Fl4Spec.ObjRef) (call : Bool) (msg : List Fl4Spec.Data) : Fl4Spec.SMonad Unit Unit :=
  Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel t (0, msg)) >>= fun _ =>
    Fl4Spec.setThreadState t .running

/-- The hypotheses of the invocations that reply: `Restart`, and FL4's
`reply1` against `replyRunning` (with and without the `Restart` before it,
which FL4's `TestAndClearAccessed` omits). -/
structure VsReplyHyps (A : Type) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), UR st th P L4 L3 L2 L1 SR s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      UR st th P L4 L3 L2 L1 SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ⦄
  reply : ∀ s a σ (ct : U64) (call : Bool) (v : U64), UR st th P L4 L3 L2 L1 SR s a σ → ct.bv = σ.curThread →
    vspace.reply1 st s ct call v ⦃ s' => ¬ (replyRunning ct.bv call [v.bv] σ).2 ∧
      ∃ σ', ((), σ') ∈ (replyRunning ct.bv call [v.bv] σ).1 ∧ UR st th P L4 L3 L2 L1 SR s' a σ' ⦄
  replyR : ∀ s a σ (ct : U64) (call : Bool) (v : U64), UR st th P L4 L3 L2 L1 SR s a σ → ct.bv = σ.curThread →
    vspace.reply1 st s ct call v ⦃ s' =>
      ¬ ((Fl4Spec.setThreadState (Z := Unit) ct.bv .restart >>= fun _ => replyRunning ct.bv call [v.bv]) σ).2 ∧
      ∃ σ', ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) ct.bv .restart >>= fun _ =>
        replyRunning ct.bv call [v.bv]) σ).1 ∧ UR st th P L4 L3 L2 L1 SR s' a σ' ⦄

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem decodeGetAddr_eq {lbl : Fl4Spec.Data}
    (hl : Fl4Spec.invocationType lbl = .archInvocationLabel .x64PageGetAddress)
    (args : List Fl4Spec.Data) (cte : Fl4Spec.CslotPtr) (dev : Bool) (p : Fl4Spec.ObjRef) (R : Fl4Spec.VMRights)
    (mt : Fl4Spec.VMMapType) (sz : Fl4Spec.VMPageSize) (ma : Option (Fl4Spec.Asid × Fl4Spec.VSpaceRef))
    (ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) lbl args cte (.pageCap dev p R mt sz ma) ex) σ =
      ({(.ok (.invokePage (.pageGetAddr p)), σ)}, False) := by
  unfold Fl4Spec.decodePageInvocation
  dsimp only
  rw [if_neg (by rw [hl]; simp), if_neg (by rw [hl]; simp), if_pos hl]
  rfl

/-- **Frame `GetAddress` refines l4v** (see the module docstring). -/
theorem frame_getaddr_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsReplyHyps st A th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hU : UR st th P L4 L3 L2 L1 SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr)
    (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    vspace.decode_frame st ar s a fl4_abi.label.X86PageGetAddress length slot (frameCapOf f) call buf ex ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = a ∧
      ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs cte (frameACapG f) vcs) σ =
        ({(.ok (.invokePage (.pageGetAddr f.ptr.bv)), σ)}, False) ∧
      ∃ σ1 σ', (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
          Fl4Spec.performPageInvocation (.pageGetAddr f.ptr.bv)) σ =
          ({([Fl4Spec.addrFromPPtr f.ptr.bv], σ1)}, False) ∧
        ¬ (replyRunning σ.curThread call [Fl4Spec.addrFromPPtr f.ptr.bv] σ1).2 ∧
        ((), σ') ∈ (replyRunning σ.curThread call [Fl4Spec.addrFromPPtr f.ptr.bv] σ1).1 ∧
        UR st th P L4 L3 L2 L1 SR res.2.1 res.2.2 σ' ⦄ := by
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  have hdec : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs cte
      (frameACapG ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩) vcs) σ =
      ({(.ok (.invokePage (.pageGetAddr ptr.bv)), σ)}, False) := decodeGetAddr_eq hl _ _ _ _ _ _ _ _ _ σ
  unfold vspace.decode_frame
  have hn1 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageMap; decide
  have hn2 : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageUnmap; decide
  have hnEpt : ¬ fl4_abi.label.X86PageGetAddress = fl4_abi.label.X86PageMapEPT := by
    unfold fl4_abi.label.X86PageGetAddress fl4_abi.label.X86PageMapEPT; decide
  simp only [frameCapOf, vspace.as_frame, bind_ok, hn1, hn2, hnEpt, ↓reduceIte]
  rw [hct]
  apply ok_bind_spec
  have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
  refine WP.spec_bind (hH.restart s a σ ct xct hU hcur hkt' htcb hact hrun) ?_
  intro s1 hU1
  simp only [layout.paddr, bind_ok]
  have hc1 : ct.bv = (stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv).curThread := by
    rw [hcur]; unfold stsAct; split <;> rfl
  refine WP.spec_bind (hH.reply s1 a _ ct call _ hU1 hc1) ?_
  rintro s2 ⟨hnf, σ', hm, hU2⟩
  refine (WP.spec_ok _).2 ⟨rfl, rfl, hdec, stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv, σ',
    ?_, ?_, ?_, hU2⟩
  · rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]; rfl
  · rw [← hcur, ← paddr_bv]; exact hnf
  · rw [← hcur, ← paddr_bv]; exact hm

/-- **PML4 `Flush` refines the l4h model** (see the module docstring). -/
theorem pml4_flush_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFlushHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hU : UR st th P L4 L3 L2 L1 SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (p asid : U64) (mp : Bool) (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) :
    vspace.decode st ar s a fl4_abi.label.X86PML4Flush length slot (.Pml4 p mp asid) call buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodePml4Flush (Z := Unit) (.pml4Cap p.bv (if mp then some asid.bv else none))) σ =
          ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ',
        ExceptT.run (Fl4Spec.decodePml4Flush (Z := Unit) (.pml4Cap p.bv (if mp then some asid.bv else none))) σ =
          ({(.ok iv, σ)}, False) ∧
        ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
          Fl4Spec.performPml4Flush iv) σ).1 ∧
        ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ => Fl4Spec.performPml4Flush iv) σ).2 ∧
        UR st th P L4 L3 L2 L1 SR res.2.1 res.2.2 σ') ⦄ := by
  unfold vspace.decode
  rw [hct]
  apply ok_bind_spec
  simp only [↓reduceIte]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩, rfl, rfl, rfl⟩)
  · simp only [↓reduceIte]
    have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
    refine WP.spec_bind (hH.restart s a σ ct xct hU hcur hkt' htcb hact hrun) ?_
    rintro s1 ⟨hS1, hSt1, hSV1, hR1, hPt1⟩
    refine WP.spec_bind (hH.flushAllH s1 a _ p.bv asid hS1) ?_
    rintro a1 ⟨σ', hσ', hS'⟩
    have hσ'' := hσ'
    obtain ⟨ms, rfl⟩ := doMachineOp_mem hσ'
    refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, rfl, ?_, ?_, hS', Vs.StateRel.ms hSt1 ms, hSV1,
      ⟨hR1.1, hR1.2, hR1.3⟩, ⟨hPt1.l4, hPt1.l3, hPt1.l2, hPt1.l1⟩⟩)
    · rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]; exact hσ''
    · rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]; exact hH.flushAllOK _ _ _

end

end

end Fl4Proofs.P3.Vs
