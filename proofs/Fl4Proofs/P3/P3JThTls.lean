/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at SetTLSBase (20)
and UnbindNotification (15), for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other
than 15 / 20, or SetEPTRoot}.

* Footprints (P1 namespace / `JAtZ`): **`notification.unbind_notification.kwN0`** (`KWN ∅ False`: the
  notification's bound word by `footN0_sgw`, the TCB's bound word by `footN_field`, as P3JNtfnFt's
  `unbind_maybe_notification.kwN0`); `JAtZ.unbindNProjW`, `JAtZ.reschedProjW` (P2's
  `reschedule_required.kwN` at `Kp = ∅` through `kwN_projW`), `JAtZ.tlsProjW` (the one `TLS_BASE` word of a TCB of
  `Z.T`: `writesIn_wr`, `ProjW`'s object clause).
* **`tcb_set_tlsJSt`** / **`tcb_unbind_ntfnJSt`**: XTopJointTcb's `tcb_set_tlsJ` / `tcb_unbind_ntfnJ` with the
  post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)` (proof text unchanged but the posts): the caller's restart by
  `JAtZ.restartJ` with its footprint `stsProjW`, the register write (`JAtZ.regWrJ`) / the unbinding
  (`JAtZ.unbindNJ`), the reschedule (`JAtZ.schedJ`); the footprints joined by `WritesIn.projW_trans`. The ghosts
  stay (`Z`, `Z.mv Z.G V`).
* **`decThTlsSt`** (any flags): the dispatch leaf at either label: the front (`JAtZ.frontJ`, `JAtZ.argsJ`), the
  label (`tcb_canon`, `specDec_thread`, `XCapP.lbl_congr`), `MR` by IrqFixGenB's transported `XCapP.mrG` with
  `MKD.decode_thread_nonins` / `perfF_tcbN` (`MachPlatT`), never preempted (`thread_noPre_of`), the target among
  `Z.T` by `slot_cap_wf`, its stall a no-op (`JAtZ.stallT`), the current-thread word outside the objects
  (`JAtZ.cwOut`). No dispatch-state input of `decode_invocation_threadJ_stepMMT` is needed at these two labels:
  neither reads `FlagsRel`, `XcRel`, `NcHyp`, `ArgRel5`, `GetBpHyp` or `FpuFrameJHyp`.
* `ThTls l`: `l` is 15 or 20. `ThHard2 l`: `ThHard l ∧ ¬ ThTls l`. `IsRestCap10` (CNode with `CnDel`, Thread with
  `ThHard2`). `restCap9_of10`, `restCap10_of`. **`midDecRest9_of_tls`** / **`invDecRest9_of_tls`**,
  `midDecStWL_of_9` / `invDecStWL_of_9`.
* **`DispStabFootLzc` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap10`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzb_of_Lzc`** (under the tops' platform facts), **`dispStabFootLzc_of_Lzb`**; top
  **`kernel_entry_runMcWKR_sysLzc`** (globals verbatim as `_sysLzb`).

Premise honesty: `DispStabFootLzc`'s decode fields are `DispStabFootLzb`'s at the smaller antecedent
(`IsRestCap10 → IsRestCap9`), midSpec / midRecvSw verbatim: implied by `DispStabFootLzb` and implying it given the
tops' platform facts.

Named premise: `DispStabFootLzc` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThIll
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64} {Es : Set U64}

/-- (p3J gen 40) `unbind_notification` in `KWN ∅ False` (P1 `unbind_notification.blkF`). -/
theorem notification.unbind_notification.kwN0 (s : S) (t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    notification.unbind_notification st s t ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.unbind_notification
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s t) fun i ei => ?_
  split
  · rename_i hi
    have hi0 : L.mem s (boundA t) ≠ 0#u64 := by rw [← ei]; simpa using hi
    have hin : i ∈ Nt := by rw [ei]; exact h.2.2.1.2.2.bnd t ht hi0
    have hm : ntfnBtA i ∈ Sg := (h.2.2.1.1.ntB i hin).2
    have h0 := h.1.choose_spec.choose_spec
    have hT := h0.tcbs
    have hsub := h.2.2.2.2.sub
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s i 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t 0#u64) fun s2 e2 => ?_
    subst e2
    exact (footN0_sgw h0 hsub rfl rfl (h0.omega _ (hsub _ hm)).1 hm).trans
      (footN_field (K := 3368#u64) hT (fun c hc => (h0.nodes c hc).ksb (L.ksb_wr _ _ _))
        (by rw [L.cpu_wr]; exact h0.cur) ht (by simp) (by simp) (by simp) (by simp))
  · exact (WP.spec_ok _).2 (FootN.refl _)

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 40) **`unbind_notification` of a thread of `Z.T` writes only `ProjW`** (module docstring). -/
theorem JAtZ.unbindNProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) :
    notification.unbind_notification st s t ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.notification.unbind_notification.kwN0 (Es := P1.EH H) s t J.blk (J.zH.1 t ht))
    fun _ F => (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

/-- (p3J gen 40) **`reschedule_required` at a `JAtZ` state writes only `ProjW`** (module docstring). -/
theorem JAtZ.reschedProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    sched.reschedule_required st s ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨⟨Q0, R0, h0⟩, -⟩ := J.blk
  exact WP.spec_mono (P1.sched.reschedule_required.kwN (Kp := ∅) (Nd := False) (Sg := P1.Heap.frame H)
    (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := P1.EH H) s h0 (fun _ => Set.notMem_empty _))
    fun s' f => (P1.WritesA.w f).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

/-- (p3J gen 40) **The `TLS_BASE` word of a thread of `Z.T` is a `ProjW` write** (module docstring). -/
theorem JAtZ.tlsProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (htH : Z.th t = some .tcb) (s1 : S) (w : U64) :
    P1.WritesIn st s1 (L.wr s1 (tlsA t) w) (Mc.ProjW (L := L) H Cs s1) := by
  have hP := J.xtop.rel.1
  have ht : t ∈ Z.T := J.thT t htH
  have hf := hP.fits t _ htH
  have hal := hP.align t _ htH
  simp only [objSize] at hf
  have hv := tlsA_val (t := t) (by omega)
  have hH : H t = some .tcb := J.zH.1 t ht
  refine (P1.writesIn_wr (s := s1) (v := w) (show P1.Aligned (tlsA t) by unfold P1.Aligned; rw [hv]; omega)).mono ?_
  rintro b rfl
  exact Or.inl ⟨t, .tcb, hH, by rw [hv]; omega, by rw [hv]; simp only [P1.HKind.bits]; omega⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **SetTLSBase at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_set_tlsJ`;
module docstring). -/
theorem tcb_set_tlsJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTLSBase)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBSetTLSBase p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  have hP := hX.rel.1
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (hX.curTcb hcur).1
  have hact := J.kern.act
  have hpT : p ∈ Z.T := J.thT p hp
  have hctT : ct ∈ Z.T := J.thT ct htcb
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hdec0 : (specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer) =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTlsBase (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val,
    lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val,
    lbl_tcbSetTLSBase_val, lbl_tcbSetEPTRoot_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_set_tls_base st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_set_tls_base
  by_cases h1 : length < 1#u64
  · simp only [if_pos h1, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_pos (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeSetTlsBase (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.setTLSBase p.bv y0.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_neg (by simp), retOk_bind]
    show (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.setTLSBase p.bv (Fl4Spec.ucast 64 y0.bv)) :
      Fl4Spec.SEMonad Unit _).run σ = _
    rw [ucast64_self]; rfl
  rw [harg]; simp only [bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, -, -, -, -, -, hcur1', hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  have hc1 := set_thread_state_cases (L := L) s ct sched.TS_RESTART
  rw [hs1, WP.spec_ok] at hc1
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨w, hw, hwb⟩ := sanitise_tls y0
  rw [hw]; simp only [bind_ok, set_reg_tls_eq]
  have W2 : P1.WritesIn st s (L.wr s1 (tlsA p) w) (Mc.ProjW (L := L) H Cs s) :=
    W1.projW_trans (J1.tlsProjW hp s1 w)
  -- the current thread is unchanged
  have hctv : L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct := by
    have := cur_thread_spec' (L := L) s; rw [hct, WP.spec_ok] at this; exact this.symm
  have hpf := hP.fits p _ hp
  have hcf := hP.fits ct _ htcb
  have hpa := hP.align p _ hp
  have hca := hP.align ct _ htcb
  simp only [objSize] at hpf hcf
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp; omega)]; simp
  have hcs2 : sched.cur_thread st (L.wr s1 (tlsA p) w) = ok ct := by
    rw [cur_thread_eq]
    simp only [P1.nodeAt_wr, L.cpu_wr]
    have hcwA : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := hcw.1
    have hn1 : L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD = L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      rcases hc1 with rfl | rfl <;> simp
    rw [hn1, L.mem_wr_ne (by unfold P1.Aligned; rw [tlsA_val (by omega)]; omega) hcwA
      (fun e => out_ne hcw hp (w := tlsA p) (by rw [tlsA_val (by omega)]; omega) e)]
    rcases hc1 with rfl | rfl
    · rw [L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
    · rw [L.mem_wr_ne hact.1 hcwA (fun e => cur_ne_action s e.symm),
        L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
  rw [hcs2]; simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
  -- the spec: the target's TCB, its register at `J`
  have hcur1 : σ1.curThread = ct.bv := by rw [hcur1', hcur]
  obtain ⟨x, hkx, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
  have htl : tlsA p = regA p (regIdx Fl4Spec.tlsBaseRegister) := by
    unfold tlsA regA layout.tcb.REGS; rfl
  have hXr := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hpT hkx Fl4Spec.tlsBaseRegister (by decide) w
  obtain ⟨V2, J2⟩ := J1.regWrJ hpT hkx Fl4Spec.tlsBaseRegister w hXr
  rw [← htl] at J2
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte]
    have hA2 : Notif.ActReady _ := J2.inv.actReady
    obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA2
    have hS := J2.xtop.fin.1.1.1
    have hN := J2.xtop.fin.1.1.2.2.1
    obtain ⟨s3, hrun3, ⟨σ3, he3, -, -, -, -⟩, hw⟩ := spec_exists (WP.spec_and
      (Sched.reschedule_required_refines _ _ hN hS hA2) (Sched.reschedule_required_sfootI hS))
    have W3 : P1.WritesIn st s s3 (Mc.ProjW (L := L) H Cs s) := by
      have h := J2.reschedProjW
      rw [hrun3, WP.spec_ok] at h
      exact W2.projW_trans h
    rw [hrun3]; simp only [bind_ok]
    rw [hres] at he3
    have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
    subst σ3
    obtain ⟨Ac3, Lst3, D3, J3⟩ := J2.schedJ (schedStep_resched hA2 hrun3 hres hK' hdl' hds')
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ'), ?_,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac3, Lst3, D3, J3⟩, W3⟩⟩)
    refine invoke_tls_mem (y := ((), σ')) hkx y0.bv ?_ blk call don
    rw [← hwb, hcur1]
    simp only [Fl4Spec.NonDet.when, if_pos trivial]
    rw [hres]; rfl
  · have hne : decide (p = ct) = false := by simp [hpc]
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1,
        J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac1, Lst1, D1, J2⟩, W2⟩⟩)
    refine invoke_tls_mem (y := ((), Notif.updK σ1 p.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister w.bv))))
      hkx y0.bv ?_ blk call don
    have : ¬ p.bv = σ1.curThread := fun e => hpc (UScalar.eq_of_val_eq (by
      rw [hcur1] at e; have := congrArg BitVec.toNat e; simpa using this))
    rw [← hwb]
    simp only [Fl4Spec.NonDet.when, if_neg this]
    exact Set.mem_singleton _

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **UnbindNotification at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's
`tcb_unbind_ntfnJ`; module docstring). -/
theorem tcb_unbind_ntfnJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbUnbindNotification)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (length buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBUnbindNotification p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer := by
  have hX := J.xtop
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hctT : ct ∈ Z.T := J.thT ct (hX.curTcb hcur).1
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  show (do
    let i ← obj.Tcb.bound_ntfn st p s
    if (i : U64).val = (0#u64).val then do
        let r ← error.illegal Unit
        ok (r, s, ar)
      else do
        let s2 ← tcb.restart_caller st s
        let s3 ← notification.unbind_notification st s2 p
        ok (core.result.Result.Ok (), s3, ar)) ⦃ r => TopPostDMX (L := L) (fun s1 a1 σ1 =>
          JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧ P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (Fl4Spec.Cap.threadCap p.bv))) s r ⦄
  rw [tcb_bound_eq]
  simp only [bind_ok, ← u64_eq_iff]
  obtain ⟨xp, hkp, hxp⟩ := hX.fin.1.1.2.1.tcb p hpT
  have hbp : xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)) := hxp.bound
  have hsp0 : (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)).run σ =
      ((match Notif.optRef (L.mem s (P1.boundA p)) with
        | none => Fl4Spec.NonDetE.throwError .illegalOperation
        | some _ => Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.notificationControl p.bv none)).run σ := by
    simp only [Fl4Spec.decodeUnbindNotification]
    rw [lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
      (Notif.threadGet_eq _ hkp), hbp]
    generalize Notif.optRef (L.mem s (P1.boundA p)) = o
    cases o <;> rfl
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  · simp only [hb0, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_throw_bind _ _ _
  simp only [hb0, ↓reduceIte]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.notificationControl p.bv none)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
  obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  -- the bound word after the restart, through the spec (the restart keeps the binding)
  have hb1 : L.mem s1 (P1.boundA p) ≠ 0#u64 := by
    intro h1
    obtain ⟨xp1, hkp1, hxp1⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
    have hb1' : xp1.tcbBoundNotification = Notif.optRef (L.mem s1 (P1.boundA p)) := hxp1.bound
    have b1 : xp1.tcbBoundNotification = none := by rw [hb1', h1]; simp [Notif.optRef]
    have b0 : xp.tcbBoundNotification ≠ none := by rw [hbp]; simp [Notif.optRef, hb0]
    apply b0
    rw [he1, stsAct_kheap, updK_kheap] at hkp1
    by_cases hpc : p.bv = ct.bv
    · rw [hpc, Function.update_self] at hkp1
      rw [hpc, hk] at hkp
      cases hkp; cases hkp1; exact b1
    · rw [Function.update_of_ne hpc, hkp] at hkp1
      cases hkp1; exact b1
  rw [hrc1]; simp only [bind_ok]
  refine WP.spec_bind (WP.spec_and (J1.unbindNJ hpT hb1) (J1.unbindNProjW hpT)) ?_
  rintro s3 ⟨⟨σ', hun, -, -, -, V, Ac', Lst', D', J2⟩, W2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeTCB (.notificationControl p.bv none))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hun]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac', Lst', D', J2⟩, W1.projW_trans W2⟩⟩

end

/-- (p3J gen 40) The Thread labels proved this generation: UnbindNotification (15), SetTLSBase (20). -/
def ThTls (l : U64) : Prop := l = fl4_abi.label.TCBUnbindNotification ∨ l = fl4_abi.label.TCBSetTLSBase

/-- (p3J gen 40) The Thread labels left after `ThTls`. -/
def ThHard2 (l : U64) : Prop := ThHard l ∧ ¬ ThTls l

/-- (p3J gen 40) The caps left after the SetTLSBase / UnbindNotification leaf, with the message label. -/
def IsRestCap10 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard2 l
  | _, _ => False

theorem restCap9_of10 {cp : capability.Cap} {l : U64} (h : IsRestCap10 cp l) : IsRestCap9 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap10_of {cp : capability.Cap} {l : U64} (h : IsRestCap9 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ ThTls l) : IsRestCap10 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem tls_nonIns : TcbNonIns fl4_abi.label.TCBSetTLSBase := by
  unfold TcbNonIns fl4_abi.label.TCBSetTLSBase fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

theorem unbN_nonIns : TcbNonIns fl4_abi.label.TCBUnbindNotification := by
  unfold TcbNonIns fl4_abi.label.TCBUnbindNotification fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at SetTLSBase or UnbindNotification, any flags**
(module docstring). -/
theorem decThTlsSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hl : ThTls info.label) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  rcases hl with hl | hl
  · rw [hl]
    obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBUnbindNotification
    have hl5 : fl4_abi.label.TCBUnbindNotification.val ≠ 5 ∧ fl4_abi.label.TCBUnbindNotification.val ≠ 8 ∧
        fl4_abi.label.TCBUnbindNotification.val ≠ 9 ∧ fl4_abi.label.TCBUnbindNotification.val ≠ 10 ∧
        fl4_abi.label.TCBUnbindNotification.val ≠ 11 := by simp [fl4_abi.label.TCBUnbindNotification]
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
      (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD unbN_nonIns hMb) fun r h => by split <;> exact h)
      (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
    refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
    left
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact tcb_unbind_ntfnJSt s' a' σb J hnib p hpT sl' (by rw [hlbl]; simp [tcbLabelOf]) (J.stallT p hpT) ct hct
        _ buf call _ e bl don _ ci sl exs buffer
    · simp only [↓reduceIte]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  · rw [hl]
    obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetTLSBase
    have hl5 : fl4_abi.label.TCBSetTLSBase.val ≠ 5 ∧ fl4_abi.label.TCBSetTLSBase.val ≠ 8 ∧
        fl4_abi.label.TCBSetTLSBase.val ≠ 9 ∧ fl4_abi.label.TCBSetTLSBase.val ≠ 10 ∧
        fl4_abi.label.TCBSetTLSBase.val ≠ 11 := by simp [fl4_abi.label.TCBSetTLSBase]
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
      (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD tls_nonIns hMb) fun r h => by split <;> exact h)
      (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
    refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
    left
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact tcb_set_tlsJSt s' a' σb J hnib p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen hArgs
        J.cwOut (J.stallT p hpT) call _ e bl don ci sl exs buffer
    · simp only [↓reduceIte]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap9` from the SetTLSBase / UnbindNotification leaf** (module
docstring). -/
theorem midDecRest9_of_tls (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap9 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ ThTls info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThTlsSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap10_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap9` from the SetTLSBase / UnbindNotification leaf** (module
docstring). -/
theorem invDecRest9_of_tls (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap9 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ ThTls info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThTlsSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap10_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap9` gives it at `KW ∧ IsRestCap10` (antitone). -/
theorem midDecStWL_of_9 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap9 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap9_of10 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap9` gives it at `KW ∧ IsRestCap10` (antitone). -/
theorem invDecStWL_of_9 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap9 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap9_of10 hW.2⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 40) **`DispStabFootLzc` [J]**: `DispStabFootLzb` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than UnbindNotification /
SetTLSBase, or SetEPTRoot (module docstring). -/
structure DispStabFootLzc (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzb.invDecRest` at `KW ∧ IsRestCap10`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzb.midDecRest` at `KW ∧ IsRestCap10`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzb.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzb.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzc → DispStabFootLzb`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzb_of_Lzc (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzc (L := L) arI AR MR s a σ) :
    DispStabFootLzb (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest9_of_tls hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest9_of_tls hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzb → DispStabFootLzc`** (the honesty claim: `DispStabFootLzc` is implied). -/
theorem dispStabFootLzc_of_Lzb {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzb (L := L) arI AR MR s a σ) : DispStabFootLzc (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_9 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_9 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzc` only** (`hLzc` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzc [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzc : DispStabFootLzc (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzb hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzb_of_Lzc hA hnd hM hIp hKD hLzc)

end

end Fl4Proofs.P3.Mc
