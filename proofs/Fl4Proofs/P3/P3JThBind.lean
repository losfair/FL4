/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at BindNotification
(14), for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than 7 / 14 / 15 / 16 / 18 /
20, or SetEPTRoot}.

* **`notification.bind_notification.kwN0`** (`KWN ∅ False`: the notification's bound word by `footN0_sgw`, the TCB's
  bound word by `footN_field`, as `unbind_notification.kwN0`); `JAtZ.bindNProjW` (through `kwN_projW`).
* **`tcb_bind_ntfnJSt`**: XTopJointTcb's `tcb_bind_ntfnJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts, the restart's footprint `stsProjW` and `bindNProjW` beside `JAtZ.bindNJ`).
* **`decThBindSt`** (any flags): the dispatch leaf (as P3JThMcp's `decThMcpSt`: `XcRel` by `ExtraOK.xc` at the
  dispatch state; the invoked slot a slot of `Z.th` with the Thread cap).
* `ThHard5 l`: `ThHard4 l ∧ l ≠ TCBBindNotification`. `IsRestCap13`. `restCap12_of13`, `restCap13_of`.
  **`midDecRest12_of_bind`** / **`invDecRest12_of_bind`**, `midDecStWL_of_12` / `invDecStWL_of_12`.
* **`DispStabFootLzf` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap13`, midSpec, midRecvSw verbatim};
  **`dispStabFootLze_of_Lzf`** (under the tops' platform facts), **`dispStabFootLzf_of_Lze`**; top
  **`kernel_entry_runMcWKR_sysLzf`** (globals verbatim as `_sysLze`).

Premise honesty: `DispStabFootLzf`'s decode fields are `DispStabFootLze`'s at the smaller antecedent
(`IsRestCap13 → IsRestCap12`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzf` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThBp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64} {Es : Set U64}

/-- (p3J gen 40) `bind_notification` in `KWN ∅ False`. -/
theorem notification.bind_notification.kwN0 (s : S) (t n : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hn : n ∈ Nt) :
    notification.bind_notification st s t n ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.bind_notification
  have hm : ntfnBtA n ∈ Sg := (h.2.2.1.1.ntB n hn).2
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  have hsub := h.2.2.2.2.sub
  refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n t) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t n) fun s2 e2 => ?_
  subst e2
  exact (footN0_sgw h0 hsub rfl rfl (h0.omega _ (hsub _ hm)).1 hm).trans
    (footN_field (K := 3368#u64) hT (fun c hc => (h0.nodes c hc).ksb (L.ksb_wr _ _ _))
      (by rw [L.cpu_wr]; exact h0.cur) ht (by simp) (by simp) (by simp) (by simp))

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

/-- (p3J gen 40) **`bind_notification` of a thread and a notification of the sets writes only `ProjW`** (module
docstring). -/
theorem JAtZ.bindNProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t n : U64} (ht : t ∈ Z.T) (hn : n ∈ Z.N) :
    notification.bind_notification st s t n ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.notification.bind_notification.kwN0 (Es := P1.EH H) s t n J.blk (J.zH.1 t ht)
    (J.zH.2.2.2 n hn)) fun _ F => (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **BindNotification at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's
`tcb_bind_ntfnJ`; module docstring). -/
theorem tcb_bind_ntfnJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbBindNotification)
    (length buf : U64)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    {xT : U64} (hxT : IsSlot Z.th xT) (hcT : capV (L.mem s) xT = .Thread p)
    (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBBindNotification p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer := by
  have hX := J.xtop
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ Z.N := by
    intro hx q b w r hc
    obtain ⟨e, -, ex, -, ps, hps, he⟩ := hXc.get (show [x0, x1, x2][0]? = some x0 from rfl) hx
    exact (J.capN ⟨x0, b, w, r, by rw [ex]; exact AbsSlot.isSlot (th := Z.th) (sl := e.2) ⟨ps, he, Or.inl hps⟩,
      hc⟩).1
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  have hNR : Notif.NtfnStateRel Z.N Z.T (L.mem s) σ := hX.fin.1.1.2.2.1
  have hNP : Notif.NPlaced Z.T Z.N := hX.fin.1.1.1.placed
  have hbnd : ∀ xp, σ.kheap p.bv = some (.tcb xp) → xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)) := by
    intro xp hk
    obtain ⟨xp', hkp', hxp⟩ := hX.fin.1.1.2.1.tcb p hpT
    rw [hk] at hkp'; cases hkp'; exact hxp.bound
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_bind_notification st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_bind_notification tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  obtain ⟨xp, hkp, -⟩ := hX.fin.1.1.2.1.tcb p hpT
  have hbp := hbnd xp hkp
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length = 0 := by have := ((hXc.2 0 x0 hx0').1).1 h0; omega
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    simp only [Fl4Spec.decodeBindNotification]
    rw [whenE_pos hl]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  have hhd : excaps.head? = some e := by rw [List.head?_eq_getElem?]; exact he
  simp only [h0, ↓reduceIte, show length >= 0#u64 from by scalar_tac, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, tcb_bound_eq]
  -- the spec up to the bound-notification check
  have hsp0 : ∀ (k : Option Fl4Spec.ObjRef → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      ((Fl4Spec.NonDetE.whenE (excaps.length = 0) (Fl4Spec.NonDetE.throwError .truncatedMessage) >>= fun _ =>
        Fl4Spec.NonDetE.liftE (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv) >>= k) :
          Fl4Spec.SEMonad Unit _).run σ = (k (Notif.optRef (L.mem s (P1.boundA p)))).run σ := by
    intro k
    rw [whenE_neg hexl, retOk_bind,
      lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
        (Notif.threadGet_eq _ hkp), hbp]
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  swap
  · -- already bound
    simp only [bne_iff_ne, ne_eq, hb0, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    simp only [Fl4Spec.decodeBindNotification]
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hb0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hsp1 : (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps).run σ = (do
      let (ntfnptr, rights) ← (match (absCap (capV (L.mem s) x0)) with
        | .notificationCap ptr _ r => Fl4Spec.NonDetE.returnOk (ptr, r)
        | _ => Fl4Spec.NonDetE.throwError .illegalOperation : Fl4Spec.SEMonad Unit _)
      Fl4Spec.NonDetE.whenE (Fl4Spec.AllowRecv ∉ rights) <| Fl4Spec.NonDetE.throwError .illegalOperation
      let ntfn ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getNotification ntfnptr
      match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
      | .idleNtfn, none => Fl4Spec.NonDetE.returnOk ()
      | .activeNtfn _, none => Fl4Spec.NonDetE.returnOk ()
      | _, _ => Fl4Spec.NonDetE.throwError .illegalOperation
      Fl4Spec.NonDetE.returnOk <| Fl4Spec.TcbInvocation.notificationControl p.bv (some ntfnptr)).run σ := by
    simp only [Fl4Spec.decodeBindNotification]
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    rw [retOk_bind, hhd, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc
    cases cc <;> rfl
  unfold tcb.bindable_ntfn
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc : capV (L.mem s) x0
  case Notification q b w r =>
    rw [hc] at hsp1
    simp only [absCap] at hsp1
    rw [retOk_bind] at hsp1
    have hqN := hcapN h0 q b w r hc
    obtain ⟨xn, hkn, hrn⟩ := hNR.ntfn q hqN
    by_cases hr : r = true
    swap
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp1, whenE_pos (by simp only [allowRecv_mem]; exact hr)]
      exact run_throw_bind _ _ _
    rw [whenE_neg (by simp only [allowRecv_mem, not_not]; exact hr), retOk_bind] at hsp1
    simp only [hr, ↓reduceIte, ntfn_head_eq, bind_ok]
    have hbt := hrn.bound
    have hob := hrn.obj
    by_cases hh : L.mem s (P1.epHeadA q) = 0#u64
    swap
    · -- a waiting notification
      simp only [bne_iff_ne, ne_eq, hh, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn)]
      have hw : ∃ qs, xn.ntfnObj = .waitingNtfn qs := by
        revert hob
        cases xn.ntfnObj with
        | idleNtfn => intro hob; exact absurd (by have := hob.2.head; simpa [Notif.qOf] using this) hh
        | activeNtfn b => intro hob; exact absurd (by have := hob.2.1.head; simpa [Notif.qOf] using this) hh
        | waitingNtfn qs => intro _; exact ⟨qs, rfl⟩
      obtain ⟨qs, hqs⟩ := hw
      rw [hqs]
      exact run_throw_bind _ _ _
    simp only [hh, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ntfn_bound_eq, bind_ok]
    have hnw : ∀ qs, xn.ntfnObj ≠ .waitingNtfn qs := by
      intro qs hq
      rw [hq] at hob
      obtain ⟨-, xs, hxs, -, hqr, -⟩ := hob
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxs
      have h1 := hqr.head
      have := hqr.ne0 hNP.tcb y (by simp)
      simp only [Notif.qOf, List.headD_cons] at h1
      rw [hh] at h1
      exact this h1.symm
    by_cases hnb : L.mem s (Notif.nBoundA q) = 0#u64
    swap
    · -- a bound notification
      simp only [bne_iff_ne, ne_eq, hnb, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn), hbt]
      simp only [Notif.optRef, hnb, ↓reduceIte]
      generalize xn.ntfnObj = o
      cases o <;> exact run_throw_bind _ _ _
    simp only [hnb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps)).run σ =
        ({(.ok (.invokeTCB (.notificationControl p.bv (some q.bv))), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn), hbt]
      simp only [Notif.optRef, hnb, ↓reduceIte]
      cases ho : xn.ntfnObj with
      | waitingNtfn qs => exact absurd ho (hnw qs)
      | idleNtfn => exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
      | activeNtfn b => exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
    have hx0s : IsSlot Z.th x0 := by
      obtain ⟨e, -, ex, -, ps, hps, he⟩ := hXc.get hx0' h0
      rw [ex]; exact AbsSlot.isSlot (th := Z.th) (sl := e.2) ⟨ps, he, Or.inl hps⟩
    have hq0 : q ≠ 0#u64 := (J.capN ⟨x0, b, w, r, hx0s, hc⟩).2
    obtain ⟨s1, σ1, -, hrc1, hst, -, -, -, -, -, -, hss1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    obtain ⟨hcur, -⟩ := J.curEq hct
    have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
      have h := stsProjW J (J.thT ct (hX.curTcb hcur).1) sched.TS_RESTART
      rw [hss1, WP.spec_ok] at h; exact h
    -- both still unbound after the restart (P1's `KeepT` of the restart)
    have ectc : ct = L.curW s := by
      have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
      rw [hct] at hc2; exact eq_of_ok_eq hc2
    obtain ⟨-, xc, hkxc, hrxc⟩ := J.curRunnable hni (cur_thread_eq s)
    have hcTZ : L.curW s ∈ Z.T := by rw [J.tcbs_eq.1]; exact J.kern.curH
    have hrunc : P1.Runnable (L.mem s (P1.stA (L.curW s))) := by
      rw [stA_tStA]; exact (runnable_iff (J.xtop.fin.1.1.2.2.1.at_tcb hcTZ hkxc).st).2 hrxc
    have hkr := P1.sched.set_thread_state.restart_blk (Es := ∅) s (L.curW s) J.blk J.kern.curH
      (P1.runnable_ok hrunc).1 (P1.runnable_ok hrunc).2
    rw [← ectc, hss1, WP.spec_ok] at hkr
    obtain ⟨-, -, -, kr⟩ := hkr
    have hz1 : L.mem s1 (P1.boundA p) = 0#u64 := by rw [kr.bndf (J.zH.1 p hpT)]; exact hb0
    have hz2 : L.mem s1 (P1.ntfnBtA q) = 0#u64 := by rw [kr.ntb q (J.zH.2.2.2 q hqN)]; exact hnb
    obtain ⟨s1', σ1', hrc', -, -, hSS, -⟩ := restart_dstate Z.th hX.rel.1 s σ Z.G
      ⟨hX.rel.2.1, J.del, hX.rel.2.2.1⟩ ct hct hcur (hX.curTcb hcur).1 J.kern.act
    have e1 : s1' = s1 := by
      have := hrc'.symm.trans hrc1
      simpa using this
    subst e1
    have hcT1 : capAt (L.mem s1') xT = ok (.Thread p) := by rw [capAt_capV, hSS.capV hxT, hcT]
    have hcN1 : capAt (L.mem s1') x0 = ok (.Notification q b w r) := by rw [capAt_capV, hSS.capV hx0s, hc]
    refine leaf_assoc ?_
    rw [hrc1]; simp only [bind_ok]
    refine WP.spec_bind (WP.spec_and (J1.bindNJ hpT hqN hq0 hz1 hz2 hxT hcT1 hx0s hcN1) (J1.bindNProjW hpT hqN)) ?_
    rintro s2 ⟨⟨σ', hbn, V, D', J2⟩, W2⟩
    refine (WP.spec_ok _).2 ?_
    have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
          (.invokeTCB (.notificationControl p.bv (some q.bv)))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
      exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hbn]; exact Set.mem_singleton _) rfl)
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac1, Lst1, D', J2⟩, W1.projW_trans W2⟩⟩
  all_goals
    rw [hc] at hsp1
    simp only [error.illegal, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp1]
    exact run_throw_bind _ _ _

end

/-- (p3J gen 40) The Thread labels left after BindNotification. -/
def ThHard5 (l : U64) : Prop := ThHard4 l ∧ l ≠ fl4_abi.label.TCBBindNotification

/-- (p3J gen 40) The caps left after the BindNotification leaf, with the message label. -/
def IsRestCap13 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard5 l
  | _, _ => False

theorem restCap12_of13 {cp : capability.Cap} {l : U64} (h : IsRestCap13 cp l) : IsRestCap12 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap13_of {cp : capability.Cap} {l : U64} (h : IsRestCap12 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBBindNotification) : IsRestCap13 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem bindN_nonIns : TcbNonIns fl4_abi.label.TCBBindNotification := by
  unfold TcbNonIns fl4_abi.label.TCBBindNotification fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at BindNotification, any flags** (module docstring). -/
theorem decThBindSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
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
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBBindNotification) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hPl : Placed Z.th := J.xtop.rel.1
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  have hXc := ExtraOK.xc hPl (hXO e exs he hexs)
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBBindNotification
  have hl5 : fl4_abi.label.TCBBindNotification.val ≠ 5 ∧ fl4_abi.label.TCBBindNotification.val ≠ 8 ∧
      fl4_abi.label.TCBBindNotification.val ≠ 9 ∧ fl4_abi.label.TCBBindNotification.val ≠ 10 ∧
      fl4_abi.label.TCBBindNotification.val ≠ 11 := by simp [fl4_abi.label.TCBBindNotification]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD bindN_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_bind_ntfnJSt s' a' σb J hnib p hpT sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf (J.stallT p hpT) ct
      hct hAs.isSlot hsc call _ e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) exs hXc bl don _ ci sl buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap12` from the BindNotification leaf** (module docstring). -/
theorem midDecRest12_of_bind (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBBindNotification
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThBindSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap13_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap12` from the BindNotification leaf** (module docstring). -/
theorem invDecRest12_of_bind (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBBindNotification
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThBindSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap13_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap12` gives it at `KW ∧ IsRestCap13` (antitone). -/
theorem midDecStWL_of_12 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap12_of13 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap12` gives it at `KW ∧ IsRestCap13` (antitone). -/
theorem invDecStWL_of_12 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap12_of13 hW.2⟩

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

/-- (p3J gen 40) **`DispStabFootLzf` [J]**: `DispStabFootLze` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetMCPriority /
Bind- and UnbindNotification / Set- and UnsetBreakpoint / SetTLSBase, or SetEPTRoot (module docstring). -/
structure DispStabFootLzf (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLze.invDecRest` at `KW ∧ IsRestCap13`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLze.midDecRest` at `KW ∧ IsRestCap13`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLze.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLze.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzf → DispStabFootLze`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLze_of_Lzf (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzf (L := L) arI AR MR s a σ) :
    DispStabFootLze (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest12_of_bind hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest12_of_bind hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLze → DispStabFootLzf`** (the honesty claim: `DispStabFootLzf` is implied). -/
theorem dispStabFootLzf_of_Lze {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLze (L := L) arI AR MR s a σ) : DispStabFootLzf (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_12 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_12 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzf` only** (`hLzf` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzf [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzf : DispStabFootLzf (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLze hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLze_of_Lzf hA hnd hM hIp hKD hLzf)

end

end Fl4Proofs.P3.Mc
