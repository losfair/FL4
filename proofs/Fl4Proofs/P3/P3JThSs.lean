/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at
ConfigureSingleStepping (19), for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than
7 / 14 / 15 / 16 / 18 / 19 / 20, or SetEPTRoot}.

* `JAtZ.regProjW`: a saved user register of a thread of `Z.T` is a `ProjW` write (`tcbWordProjW` at offset
  `256 + 8 * regIdx r`, `regA_val`, `regIdx_lt`).
* `JAtZ.cssProjW`: FL4's `configure_single_stepping` of a thread of `Z.T` writes only `ProjW` (the debug words
  `SS_ENABLED` / `SS_COUNT` by `tcbWordProjW`, the `FLAGS` register by `regProjW`).
* `JAtZ.replyWords1JSt`: XTopJointTcb's `JAtZ.replyWords1J` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the post: the three register writes by `regProjW`, `Running` by `stsProjW`).
* **`tcb_single_stepJSt`**: XTopJointTcb's `tcb_single_stepJ` (a replying label, `TcbOKRX`) with the post
  `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)` (proof text unchanged but the posts: the restart by `stsProjW`, the
  step by `cssProjW`, the uncalled tail by `stsProjW`, the called tail by `replyWords1JSt`; `projW_trans`).
* **`decThSsSt`** (any flags): the dispatch leaf (as P3JThBp's `decThBpSt`, the `DecOKRMX` disjunct of `XCap`). The
  arguments' relation `ArgRel … 2` is `JAtZ.argsJ`'s third conjunct at the dispatch state (not a premise).
* `ThHard6 l`: `ThHard5 l ∧ l ≠ TCBConfigureSingleStepping`. `IsRestCap14`. `restCap13_of14`, `restCap14_of`.
  **`midDecRest13_of_ss`** / **`invDecRest13_of_ss`**, `midDecStWL_of_13` / `invDecStWL_of_13`.
* **`DispStabFootLzg` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap14`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzf_of_Lzg`** (under the tops' platform facts), **`dispStabFootLzg_of_Lzf`**; top
  **`kernel_entry_runMcWKR_sysLzg`** (globals verbatim as `_sysLzf`).

Premise honesty: `DispStabFootLzg`'s decode fields are `DispStabFootLzf`'s at the smaller antecedent
(`IsRestCap14 → IsRestCap13`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzg` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThBind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 40) **A saved user register of a thread of `Z.T` is a `ProjW` write** (module docstring). -/
theorem JAtZ.regProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (r : Fl4Spec.Register)
    (s1 : S) (v : U64) :
    P1.WritesIn st s1 (L.wr s1 (regA t (regIdx r)) v) (Mc.ProjW (L := L) H Cs s1) := by
  have hr := regIdx_lt r
  exact J.tcbWordProjW ht (Kv := 256 + 8 * (regIdx r).val) ⟨by omega, by omega⟩
    (by rw [regA_val (J.ip.e.tcb t ht) hr]; omega) s1 v

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`configure_single_stepping` of a thread of `Z.T` writes only `ProjW`** (module docstring). -/
theorem JAtZ.cssProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpT : p ∈ Z.T) (bp n : U64) :
    debug.configure_single_stepping st arI s a p bp n false ⦃ r =>
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hpf := (J.ip.e.tcb p hpT).fits
  have hE : (dbgA p debug.SS_ENABLED).val = p.val + (448 + 48) := by
    rw [dbgA_val (by omega) (by unfold debug.SS_ENABLED; decide)]; unfold debug.SS_ENABLED; simp
  have hC : (dbgA p debug.SS_COUNT).val = p.val + (448 + 56) := by
    rw [dbgA_val (by omega) (by unfold debug.SS_COUNT; decide)]; unfold debug.SS_COUNT; simp
  unfold debug.configure_single_stepping
  by_cases hn : n = 0#u64
  · subst hn
    simp only [↓reduceIte, set_debug_reg_wr, bind_ok]
    simp only [Std.bind_assoc]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec _ p layout.reg.FLAGS) ?_
    rintro i rfl
    rw [eflags_tf_eq]; simp only [bind_ok, lift]
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ p layout.reg.FLAGS _) ?_
    rintro s3 rfl
    simp only [set_debug_reg_wr, bind_ok, WP.spec_ok]
    set s2 := L.wr s (dbgA p debug.SS_ENABLED) 0#u64
    have W1 : P1.WritesIn st s s2 (Mc.ProjW (L := L) H Cs s) :=
      J.tcbWordProjW hpT (Kv := 448 + 48) ⟨by omega, by omega⟩ hE s 0#u64
    rw [show regA p layout.reg.FLAGS = regA p (regIdx Fl4Spec.Register.flags) by rw [regIdx_flags]]
    exact (W1.projW_trans (J.regProjW hpT Fl4Spec.Register.flags s2 _)).projW_trans
      (J.tcbWordProjW hpT (Kv := 448 + 56) ⟨by omega, by omega⟩ hC _ 0#u64)
  · simp only [hn, ↓reduceIte, set_debug_reg_wr, bind_ok, WP.spec_ok]
    exact (J.tcbWordProjW hpT (Kv := 448 + 48) ⟨by omega, by omega⟩ hE s 1#u64).projW_trans
      (J.tcbWordProjW hpT (Kv := 448 + 56) ⟨by omega, by omega⟩ hC _ n)

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **The single-word reply tail at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's
`JAtZ.replyWords1J`; module docstring). -/
theorem JAtZ.replyWords1JSt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart) (v : U64) :
    (do
      let s4 ← tcb.reply_words st (L.wr s (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) ct 1#u64
      let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
        ∀ z ∈ (specTail true ct.bv [v.bv] σ).1, JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 z.2 ∧
          P1.WritesIn st s res.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  set s1 := L.wr s (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v
  have hRW : tcb.reply_words st s1 ct 1#u64 ⦃ s3 => ∃ w : U64,
      s3 = L.wr (L.wr s1 (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
        (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
      w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
    unfold tcb.reply_words
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s1 ct layout.reg.BADGE 0#u64) ?_
    rintro s2 rfl
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 1#u64 (by decide)) ?_
    rintro s3 ⟨w, rfl, hw⟩
    refine ⟨w, ?_, by rw [hw]; exact msg_info_one_bv⟩
    rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
  refine WP.spec_bind hRW ?_
  rintro s3 ⟨w, rfl, hw⟩
  have W3 : P1.WritesIn st s (L.wr (L.wr s1 (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
      (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w) (Mc.ProjW (L := L) H Cs s) :=
    ((J.regProjW hct (Endp.mrIdx 0) s v).projW_trans (J.regProjW hct Fl4Spec.badge_register s1 0#u64)).projW_trans
      (J.regProjW hct Fl4Spec.msg_info_register _ w)
  -- MR0
  have hX1 := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hk (Endp.mrIdx 0) (by decide) v
  obtain ⟨V1, J1⟩ := J.regWrJ hct hk (Endp.mrIdx 0) v hX1
  set x1 := setReg x (Endp.mrIdx 0) v.bv with hx1
  have hk1 : (updK σ ct.bv (.tcb x1)).kheap ct.bv = some (.tcb x1) := by simp [updK]
  -- the badge
  have hXb := badge_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hct hk1 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V2, J2⟩ := J1.regWrJ hct hk1 Fl4Spec.badge_register 0#u64 hXb
  set x2 := setReg x1 Fl4Spec.badge_register (0#u64 : U64).bv with hx2
  have hk2 : (updK (updK σ ct.bv (.tcb x1)) ct.bv (.tcb x2)).kheap ct.bv = some (.tcb x2) := by simp [updK]
  -- the message info
  have hX3 := reg_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hct hk2 Fl4Spec.msg_info_register (by decide) w
  obtain ⟨V3, J3⟩ := J2.regWrJ hct hk2 Fl4Spec.msg_info_register w hX3
  have hxC : setReg x2 Fl4Spec.msg_info_register w.bv = Endp.replyTcb x v.bv := by
    rw [hw, hx2, hx1, setReg_comm x (show Endp.mrIdx 0 ≠ Fl4Spec.badge_register by decide)]
    rfl
  rw [updK_updK, updK_updK, hxC] at J3
  have hkC : (updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv = some (.tcb (Endp.replyTcb x v.bv)) := by
    simp [updK]
  refine WP.spec_bind (WP.spec_and (J3.runJ hct hkC hrs) (stsProjW J3 hct sched.TS_RUNNING)) ?_
  rintro s4 ⟨⟨Lst', D', J4⟩, W4⟩
  refine (WP.spec_ok _).2 fun z hz => ?_
  rw [specTail_restart hk hrs true v.bv] at hz
  simp only [↓reduceIte] at hz
  rw [Notif.setThreadState_eq .running hkC] at hz
  rw [Set.mem_singleton_iff.1 hz]
  exact ⟨JStab.mv (G := Z.G) (V := V1) (JStab.mv (G := (Z.mv Z.G V1).G) (V := V2) ⟨_, _, _, _, _, J4⟩),
    W3.projW_trans W4⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **ConfigureSingleStepping at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's
`tcb_single_stepJ`; module docstring). -/
theorem tcb_single_stepJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    [VxE Z]
    (hni : Entered σ) (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .configureSingleStepping)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 2)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKRX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBConfigureSingleStepping p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hpT : p ∈ Z.T := J.thT p hp
  have hctT : ct ∈ Z.T := J.thT ct htcb
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKRX
  rw [decode_step_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  obtain ⟨n, hn, hns⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 1#u64 (by decide)
  unfold tcb.decode_configure_single_stepping
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [hn]; simp only [bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, hk0, -, hσ1, -, -, hcu1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  rw [hkc] at hk0; cases hk0
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4ConfigureSingleStepping
    rw [run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 0).run σ = _ from hbs),
      run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 1).run σ = _ from hns)]
    rfl
  obtain ⟨xp, hkp, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
  refine WP.spec_bind (WP.spec_and (J1.cssJ hpT hkp bp n) (J1.cssProjW hpT bp n)) ?_
  rintro ⟨consumed, s2, a2⟩ ⟨⟨hcons, ha2, V2, J2⟩, Wc⟩
  simp only at hcons ha2 J2
  subst hcons ha2
  have Wc' : P1.WritesIn st s s2 (Mc.ProjW (L := L) H Cs s) := W1.projW_trans Wc
  set Z2 : XSets := Z.mv Z.G V2 with hZ2
  have hX2 := J2.xtop
  obtain ⟨xy, hky, hrsy⟩ := css_tcb hkp hkc1 n.bv
  have hcurY : ct.bv = (cssState σ1 p.bv xp n.bv).curThread := by
    unfold cssState; split <;> (show ct.bv = σ1.curThread; rw [hcu1, hcur])
  have htcb2 : Z2.th ct = some .tcb := htcb
  have hact2 : OutsideObjects Z2.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := J2.kern.act
  have hy := css_mem (bp := bp.bv) hkp n.bv
  have hy' : (.ok [0], cssState σ1 p.bv xp n.bv) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv))).run σ1).1 := hy
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hJt : (do
        let s5 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
          ∀ z ∈ (specTail false ct.bv [0] (cssState σ1 p.bv xp n.bv)).1,
            JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 z.2 ∧
              P1.WritesIn st s res.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
      refine WP.spec_bind (WP.spec_and (J2.runJ hctT hky (by rw [hrsy])) (stsProjW J2 hctT sched.TS_RUNNING)) ?_
      rintro s5 ⟨⟨Lst', D', J5⟩, W5⟩
      refine (WP.spec_ok _).2 fun z hz => ?_
      rw [specTail_restart hky (by rw [hrsy]) false 0] at hz
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [Notif.setThreadState_eq .running hky] at hz
      rw [Set.mem_singleton_iff.1 hz]
      exact ⟨⟨_, _, _, _, _, J5⟩, Wc'.projW_trans W5⟩
    refine WP.spec_mono (WP.spec_and (nodata_tail_xtop hX2 hcurY hky (by rw [hrsy]) hact2 [0]) hJt) ?_
    rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
    exact Or.inr ⟨hres, hne, _, DecOut.of_eq hdec, σ1, hst1, [0], _, hy', z, hz, hRT, hJ5 z hz⟩
  · simp only [↓reduceIte]
    refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
    rintro bf -
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hI0 : Vs.RInv (L := L) Z2.th Z2.P Z2.L4 Z2.L3 Z2.L2 Z2.L1 Z2.N Z2.T Z2.C Z2.E Z2.R Z2.B Z2.c AR Z2.G s2 a2
        (MrS (cssState σ1 p.bv xp n.bv) ct.bv xy (Endp.ipcBufOf true xy) []) := by
      rw [MrS_nil hky]; exact hX2.toRInv
    have tail : (do
        let (len, s3) ← msg.set_mr st s2 ct bf 0#u64 0#u64
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
          TopPostRMX (L := L) (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
            P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk true don (Fl4Spec.NonDetE.liftME
            Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv))
            ct s res ⦄ := by
      have hset : msg.set_mr st s2 ct bf 0#u64 0#u64 ⦃ r =>
          r = (1#u64, L.wr s2 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) 0#u64) ⦄ := by
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ 0#u64) ?_
        rintro s2' rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (WP.spec_and (setmr_reg_inv _ ct htcb2 hcurY xy _ bf s2 a2 [] hI0 0#u64 rfl (by decide)
        0#u64) hset) ?_
      rintro ⟨len, s3⟩ ⟨⟨hlen, hI3, hk3, hc3⟩, he3⟩
      simp only [Prod.mk.injEq] at hlen hI3 hk3 hc3 he3
      obtain ⟨rfl, rfl⟩ := he3
      refine WP.spec_mono (WP.spec_and (data_tail_xtop hX2 hcurY hky (by rw [hrsy]) hact2 hI3 hk3 hc3 (by decide)
        (fun _ _ z hz => by simp [Endp.mrPairs] at hz) 1#u64
        (by cases Endp.ipcBufOf true xy <;> simp [mrLen]) (by decide))
        (J2.replyWords1JSt hctT hky (by rw [hrsy]) 0#u64)) ?_
      rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
      obtain ⟨hS5, W5⟩ := hJ5 z hz
      exact Or.inr ⟨hres, hne, _, DecOut.of_eq hdec, σ1, hst1, [0], _, hy', z, hz, hRT,
        JStab.mv (G := Z.G) (V := V2) hS5, Wc'.projW_trans W5⟩
    split <;> first | exact tail | (split <;> exact tail)

end

/-- (p3J gen 40) The Thread labels left after ConfigureSingleStepping. -/
def ThHard6 (l : U64) : Prop := ThHard5 l ∧ l ≠ fl4_abi.label.TCBConfigureSingleStepping

/-- (p3J gen 40) The caps left after the ConfigureSingleStepping leaf, with the message label. -/
def IsRestCap14 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard6 l
  | _, _ => False

theorem restCap13_of14 {cp : capability.Cap} {l : U64} (h : IsRestCap14 cp l) : IsRestCap13 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap14_of {cp : capability.Cap} {l : U64} (h : IsRestCap13 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBConfigureSingleStepping) : IsRestCap14 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem ss_nonIns : TcbNonIns fl4_abi.label.TCBConfigureSingleStepping := by
  unfold TcbNonIns fl4_abi.label.TCBConfigureSingleStepping fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at ConfigureSingleStepping, any flags** (module
docstring). -/
theorem decThSsSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
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
    (hl : info.label = fl4_abi.label.TCBConfigureSingleStepping) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨-, -, hA5⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  rw [hl]
  obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon fl4_abi.label.TCBConfigureSingleStepping
  have hl5 : fl4_abi.label.TCBConfigureSingleStepping.val ≠ 5 ∧
      fl4_abi.label.TCBConfigureSingleStepping.val ≠ 8 ∧
      fl4_abi.label.TCBConfigureSingleStepping.val ≠ 9 ∧ fl4_abi.label.TCBConfigureSingleStepping.val ≠ 10 ∧
      fl4_abi.label.TCBConfigureSingleStepping.val ≠ 11 := by simp [fl4_abi.label.TCBConfigureSingleStepping]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD ss_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  right
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf])
      (show tcbExtOf _ = some .configureSingleStepping by simp [tcbExtOf])
    exact tcb_single_stepJSt s' a' σb J hnib p hp sl' hg he _ buf ct hct (J.stallT p hpT) buffer
      (fun i hi => hA5 i (by omega)) call _ e bl don _ ci sl exs
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap13` from the ConfigureSingleStepping leaf** (module docstring). -/
theorem midDecRest13_of_ss (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBConfigureSingleStepping
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThSsSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap14_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap13` from the ConfigureSingleStepping leaf** (module docstring). -/
theorem invDecRest13_of_ss (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBConfigureSingleStepping
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThSsSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap14_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap13` gives it at `KW ∧ IsRestCap14` (antitone). -/
theorem midDecStWL_of_13 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap13_of14 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap13` gives it at `KW ∧ IsRestCap14` (antitone). -/
theorem invDecStWL_of_13 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap13 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap13_of14 hW.2⟩

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

/-- (p3J gen 40) **`DispStabFootLzg` [J]**: `DispStabFootLzf` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetMCPriority /
Bind- and UnbindNotification / Set- and UnsetBreakpoint / ConfigureSingleStepping / SetTLSBase, or SetEPTRoot
(module docstring). -/
structure DispStabFootLzg (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzf.invDecRest` at `KW ∧ IsRestCap14`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzf.midDecRest` at `KW ∧ IsRestCap14`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzf.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzf.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzg → DispStabFootLzf`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzf_of_Lzg (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzg (L := L) arI AR MR s a σ) :
    DispStabFootLzf (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest13_of_ss hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest13_of_ss hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzf → DispStabFootLzg`** (the honesty claim: `DispStabFootLzg` is implied). -/
theorem dispStabFootLzg_of_Lzf {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzf (L := L) arI AR MR s a σ) : DispStabFootLzg (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_13 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_13 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzg` only** (`hLzg` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzg [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzg : DispStabFootLzg (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzf hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzf_of_Lzg hA hnd hM hIp hKD hLzg)

end

end Fl4Proofs.P3.Mc
