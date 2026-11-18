/-
P3 (DESIGN.md §9), TCB invocations: **the scheduler-only TCB labels at
`XTop`** (TcbXRest's leaves done with the CSpace machinery).

* `tcb_set_mcpX`: SetMCPriority: ScTcb's decode correspondence
  (`tcb_set_mcp_refines`) with the restart (`XTopAt.restart'`), FL4's `MCP`
  word (`XTopAt.tcbWr`) and the spec's `set_mcpriority` (`TcbBufStep`,
  `XTopAt.bufSpec`): no relation reads the `MCP`.
* `tcb_unset_bpX`: UnsetBreakpoint, debug-word writes (`XTopAt.tcbWrA`);
  SetTLSBase is in XTopTcbTls (its register write from IpcSuspend's
  `reg_wr_irel`).
* The other subsystems' labels: the decode proved at `XTop` here, the
  invocation a named leaf for the IPC/Sc side (`SuspendXLeaf`,
  `ResumeXLeaf`, `UnbindXLeaf`, `BindXLeaf`, `SetPrioXLeaf`,
  `SchedTailXHyp` after the fault-handler install at `WX` (`ssp_tailX`),
  `ReadRegsXHyp`, `WriteRegsXHyp`, `CopyRegsXHyp`).
-/
import Fl4Proofs.P3.XTopTcbAll
import Fl4Proofs.P3.ScTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's SetMCPriority at `XTop`**: beyond `tcb_set_mcp_refines`'
premises (`McpRel` for the authority's MCP [J], the authority among its
TCBs [J]), `XTopAt` at the typed heap, the caller runnable [J], `DelInv`
[J], the target among the sets' TCBs [J]. -/
theorem tcb_set_mcpX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hp : Z.th p = some .tcb) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetMCPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    {T : Set U64} (hM : McpRel T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetMCPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetMcpriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_mcp_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetMcpriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, hrc, hsts, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
      have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
        rw [← hcur]; exact hst1
      obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hsts hst1'
      rw [hrc]; simp only [bind_ok, tcs_mcp]
      refine (WP.spec_ok _).2 ?_
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      obtain ⟨x, hkx, -⟩ := hDS1.1.1.tcb p hp
      have hX2 := (hX1.tcbWr hpT 3440#u64 (Or.inl rfl) y0).bufSpec (tcbMcpStep_upd hkx (Fl4Spec.ucast 8 y0.bv))
      refine Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_, ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX2.rel.1,
        hX2.rel.2.1, hX2.rel.2.2.1, hX2.rel.2.2.2.1, hX2.rel.2.2.2.2.1⟩, ⟨Z, hX2⟩⟩
      rw [invoke_mcp_run hkx]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _


end

/-! ## UnsetBreakpoint -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The TCB word of debug register `i`. -/
def dbgA (t i : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.DEBUG) (core.num.U64.wrapping_mul i 8#u64)

theorem dbgA_val {t i : U64} (ht : t.val + 4096 ≤ 2 ^ 64) (hi : i.val < 8) : (dbgA t i).val = t.val + 448 + 8 * i.val := by
  unfold dbgA layout.tcb.DEBUG
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

theorem set_debug_reg_wr (s : S) (t i v : U64) : obj.Tcb.set_debug_reg st t s i v = ok (L.wr s (dbgA t i) v) := by
  unfold obj.Tcb.set_debug_reg
  simp [lift, L.write_eq, dbgA]

/-- **FL4's `unset_breakpoint`**: the `DR7` word, then the breakpoint's
address word. -/
theorem unset_bp_wr (s : S) (t bp : U64) (hbp : bp.val < 4) :
    debug.unset_breakpoint st s t bp ⦃ s2 => ∃ v, s2 = L.wr (L.wr s (dbgA t 5#u64) v) (dbgA t bp) 0#u64 ⦄ := by
  unfold debug.unset_breakpoint debug.set_dr7
  simp only [set_debug_reg_wr, debug.DR7]
  unfold debug.dr7 obj.Tcb.debug_reg debug.enable_bit debug.size_shift debug.type_shift
  step*

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's UnsetBreakpoint at `XTop`**: `tcb_unset_bp_refines`' decode
(the argument by `ArgRel` [J]), the restart, the two debug-register words
(`DR7`, the breakpoint's; offsets 448..504, read by no relation:
`XTopAt.tcbWrA`); the spec keeps its state (the debug registers are not in
the model). -/
theorem tcb_unset_bpX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .unsetBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBUnsetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_unset_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  simp only [bind_ok]
  have hsp : (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.unsetBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4UnsetBreakpoint
    exact run_bind_ok hbs _
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1'
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.unsetBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    have hbpv : bp.val < 4 := by
      have : ¬ (4 ≤ bp.val) := fun h => hb (by scalar_tac)
      omega
    obtain ⟨Q, R0, hc, -⟩ := hX1.fin.1.1.1.lists
    have hpf := (hc.tcbs p hpT).fits
    refine WP.spec_bind (unset_bp_wr s1 p bp hbpv) ?_
    rintro s2 ⟨v, rfl⟩
    have hX2 := (hX1.tcbWrA hpT (dbgA p 5#u64) (448 + 40) (by omega) (by rw [dbgA_val (by omega) (by decide)]; simp)
      v).tcbWrA hpT (dbgA p bp) (448 + 8 * bp.val) (by omega) (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) 0#u64
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX2.rel.1, hX2.rel.2.1, hX2.rel.2.2.1, hX2.rel.2.2.2.1,
        hX2.rel.2.2.2.2.1⟩, ⟨Z, hX2⟩⟩)

end


/-! ## Suspend and Resume: the decode, the invocation a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The Suspend leaf at `XTop`** (for the IPC/Sc side): from `XTop`, the
caller's restart then `sched::suspend` of the target, against the spec's
`suspend` from `σ1` (the state after the spec's restart). -/
def SuspendXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.suspend st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2))
    (Fl4Spec.suspend (Z := Unit) p.bv σ1)

/-- **The Resume leaf at `XTop`**: the caller's restart then
`sched::restart` of the target, against the spec's `restart`. -/
def ResumeXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.restart st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2))
    (Fl4Spec.restart (Z := Unit) p.bv σ1)

theorem decode_suspend_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSuspend p c = (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.suspend st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val,
    lbl_tcbCopyRegisters_val, lbl_tcbSuspend_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

theorem decode_resume_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBResume p c = (do
      let s1 ← tcb.restart_caller st s
      let (s2, a2) ← sched.restart st arI s1 ar p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val,
    lbl_tcbCopyRegisters_val, lbl_tcbSuspend_val, lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- A leaf's outcome is a `TopPostDMX` outcome of a decode with one outcome,
whose invocation's run is the leaf's spec with an empty result. -/
theorem topX_of_leaf {AR : A → Fl4Spec.Cr3 → Prop} {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {inv : Fl4Spec.Fl4Invocation} {s : S}
    {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hdec : m.run σ = ({(.ok inv, σ)}, False))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hrun : ∀ z ∈ spec.1, ((.ok [], z.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1)
    {res : core.result.Result Unit error.Exc × S × A}
    (h : res.1 = .Ok () ∧ ∃ z ∈ spec.1, RelTopM (L := L) res.2.1 z.2 ∧ XTop (L := L) AR res.2.1 res.2.2 z.2) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don m s res := by
  obtain ⟨hr, z, hz, ⟨th', G', hPl, hCR, hFI, hD, hMO⟩, hX⟩ := h
  exact Or.inr ⟨inv, DecOut.of_eq hdec, σ1, hst, (.ok [], z.2), hrun z hz,
    ⟨th', G', Or.inl ⟨hr, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, hX⟩

/-- **TcbXRest's Suspend at `XTop`**, from the leaf (`SuspendXLeaf`, the
IPC/Sc side's). -/
theorem tcb_suspendX {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : XTop (L := L) AR s ar σ) (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSuspend)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hL : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      SuspendXLeaf (L := L) arI AR s ar σ σ1 p) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSuspend p c blk call don slbl args ci sl excaps
      buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.suspend p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  obtain ⟨σ1, hst⟩ := hX0.restart
  unfold TcbOKX
  rw [decode_suspend_eq arI s ar p c hstall]
  refine WP.spec_mono (hL σ1 hst hX0) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)

/-- **TcbXRest's Resume at `XTop`**, from the leaf (`ResumeXLeaf`). -/
theorem tcb_resumeX {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : XTop (L := L) AR s ar σ) (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbResume)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hL : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ResumeXLeaf (L := L) arI AR s ar σ σ1 p) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBResume p c blk call don slbl args ci sl excaps
      buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.resume p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  obtain ⟨σ1, hst⟩ := hX0.restart
  unfold TcbOKX
  rw [decode_resume_eq arI s ar p c hstall]
  refine WP.spec_mono (hL σ1 hst hX0) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)

end


/-! ## UnbindNotification: the decode, the invocation a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The UnbindNotification leaf at `XTop`** (for the IPC side): from
`XTop`, the caller's restart then `unbind_notification` of the target,
against the spec's `unbind_notification` from `σ1`. -/
def UnbindXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let s2 ← notification.unbind_notification st s1 p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar))
    (Fl4Spec.unbindNotification (Z := Unit) p.bv σ1)

/-- **TcbXRest's UnbindNotification at `XTop`**: the bound-notification check
on both sides (the TCB word against the spec's `tcb_bound_notification`, by
the endpoint relation), then the leaf (`UnbindXLeaf`, the IPC side's) when a
notification is bound. -/
theorem tcb_unbind_ntfnX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbUnbindNotification)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (length buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hL : L.mem s (P1.boundA p) ≠ 0#u64 → ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      UnbindXLeaf (L := L) AR s ar σ σ1 p) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBUnbindNotification p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer := by
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
        ok (core.result.Result.Ok (), s3, ar)) ⦃ r => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
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
  obtain ⟨σ1, hst⟩ := XTop.restart (L := L) (AR := AR) ⟨Z, hX⟩
  refine WP.spec_mono (hL hb0 σ1 hst ⟨Z, hX⟩) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)

end


/-! ## SetPriority: the decode, the invocation a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The SetPriority leaf at `XTop`** (for the IPC/Sc side): from `XTop`,
the caller's restart then `sched::set_priority` of the target to `v`,
against the spec's `set_priority` (to `v`'s byte) from `σ1`. -/
def SetPrioXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p v : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let s2 ← sched.set_priority st s1 p v
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar))
    (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 v.bv) σ1)

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's SetPriority at `XTop`**: ScTcb's decode correspondence
(`tcb_set_prio_refines`; `McpRel` [J], the authority among its TCBs [J]),
then the leaf (`SetPrioXLeaf`, the IPC/Sc side's: the queues reordered). -/
theorem tcb_set_prioX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    {T : Set U64} (hM : McpRel T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (hL : ∀ σ1 (v : U64), Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      v.val < 256 → SetPrioXLeaf (L := L) AR s ar σ σ1 p v)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetPriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_prio_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetPriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, hrc, -, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      have hl := hL σ1 y0 hst1 hlt ⟨Z, hX⟩
      unfold SetPrioXLeaf at hl
      rw [hrc] at hl; simp only [bind_ok] at hl
      rw [hrc]; simp only [bind_ok, tcs_prio]
      exact WP.spec_mono hl fun res h => topX_of_leaf hdec hst1 (fun z hz => invoke_prio_mem ssl _ q.bv blk call don hz) h
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _


end


/-! ## Write/CopyRegisters: the decode, the register work a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The WriteRegisters leaf at `XTop`** (for the IPC/Sc side): after the
caller's restart, at `XTop`, FL4's `write_registers` against the spec's
`invoke_tcb WriteRegisters` (from the state after the spec's restart),
with an empty result and `XTop` after. -/
def WriteRegsXHyp (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (σ : Fl4Spec.State Unit) (ct p buf : U64) (args : List U64)
    (blk call don : Bool) : Prop :=
  ∀ s1 σ1 (flags n : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → n.val ≤ args.length - 2 →
    XTop (L := L) AR s1 a σ1 →
    tcb.write_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n buf ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.writeRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) (((args.drop 2).map UScalar.bv).take n.val)
          Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1,
        y.1 = .ok [] ∧ RelTopM (L := L) r.1 y.2 ∧ XTop (L := L) AR r.1 r.2 y.2 ⦄

/-- **The CopyRegisters leaf at `XTop`**: after the caller's restart, at
`XTop`, FL4's `copy_registers` (source `src`, a thread cap's in a slot)
against the spec's `invoke_tcb CopyRegisters`. -/
def CopyRegsXHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64)
    (blk call don : Bool) : Prop :=
  ∀ s1 σ1 (src flags : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    (∃ x, IsSlot th x ∧ capV (L.mem s) x = .Thread src) → XTop (L := L) AR s1 a σ1 →
    tcb.copy_registers st arI s1 a p src flags ⦃ r => r.1 = .Ok () ∧
      ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.copyRegisters p.bv src.bv
          (Fl4Spec.testBit flags.bv 0) (Fl4Spec.testBit flags.bv 1) (Fl4Spec.testBit flags.bv 2)
          (Fl4Spec.testBit flags.bv 3) Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1,
        y.1 = .ok [] ∧ RelTopM (L := L) r.2.1 y.2 ∧ XTop (L := L) AR r.2.1 r.2.2 y.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's WriteRegisters at `XTop`**: TcbCtl's decode
(`tcb_write_regs_refines`), the restart, then the leaf (`WriteRegsXHyp`). -/
theorem tcb_write_regsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC0 : CurRun σ)
    (hDI : DelInv Z.th (L.mem s)) (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbWriteRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (hW : WriteRegsXHyp (L := L) arI AR s σ ct p buf args blk call don) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBWriteRegisters p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeWriteRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_write_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_write_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨i, hi, hiv⟩ := spec_exists (U64.sub_spec (x := length) (y := 2#u64) (by scalar_tac))
  have hrl : rest.length = length.val - 2 := by simp at hlen; scalar_tac
  have hiv' : i.val = length.val - 2 := by rw [hiv.1]; rfl
  have hl2 : 2 ≤ length.val := by have : ¬ length.val < (2#u64 : U64).val := h1; exact Nat.le_of_not_lt this
  rw [ha0, ha1]; simp only [bind_ok, hi]
  have hsp : (Fl4Spec.decodeWriteRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
        (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters)) := by
    simp only [Fl4Spec.decodeWriteRegisters, List.map_cons, retOk_bind]
  rw [hsp]
  have hun : Fl4Spec.unat y1.bv = y1.val := by simp [Fl4Spec.unat]
  by_cases hw : i < y1
  · simp only [hw, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [whenE_pos (by rw [hun, List.length_map, hrl]; have h' : i.val < y1.val := hw; omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hw, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
  have hwh : (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
      (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) : Fl4Spec.SEMonad Unit Unit).run σ = ({(.ok (), σ)}, False) := by
    rw [whenE_neg (by rw [hun, List.length_map, hrl]; have h' : ¬ i.val < y1.val := hw; omega)]; rfl
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩
    apply run_liftME_err
    rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
      s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC0 hcur hs1 hst1'
    rw [hrc1]; simp only [bind_ok, lift]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
          (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
          let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
          Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
            ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((((y0 :: y1 :: rest).drop 2).map UScalar.bv).take y1.val) Fl4Spec.ArchDefaultExtraRegisters)), σ)},
          False) := by
      apply run_liftME_ok
      rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc),
        retOk_bind, hun]
      rfl
    refine WP.spec_bind (hW s1 σ1 y0 y1 ar hs1 hst1' (by simp only [List.length_cons]; have h' : ¬ i.val < y1.val := hw; omega) ⟨Z, hX1⟩) ?_
    rintro ⟨s2, a2⟩ ⟨y, hy, hy1, ⟨th', G', hPl, hCR, hFI, hD, hMO⟩, hX2⟩
    exact (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, y, hy, ⟨th', G', Or.inl ⟨rfl, hy1⟩, hPl, hCR, hFI, hD,
      hMO⟩, hX2⟩)


set_option maxHeartbeats 4000000 in
/-- **TcbXRest's CopyRegisters at `XTop`**: TcbCtl's decode
(`tcb_copy_regs_refines`), the restart, then the leaf (`CopyRegsXHyp`). -/
theorem tcb_copy_regsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC0 : CurRun σ)
    (hDI : DelInv Z.th (L.mem s)) (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbCopyRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hC : CopyRegsXHyp (L := L) arI AR Z.th s σ ct p blk call don) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBCopyRegisters p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call
      don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_copy_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_copy_registers tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : args = [] ∨ excaps = [] →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)))
        s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rcases h with rfl | rfl
    · exact copy_trunc0 σ _ _
    · cases args with
      | nil => exact copy_trunc0 σ _ _
      | cons y0 rest => exact copy_trunc1 σ _ _ _
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (List.eq_nil_of_length_eq_zero (by omega)))
  by_cases hl : length < 1#u64
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, show ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by
        show ¬ length >= 1#u64; scalar_tac]
    exact htr (Or.inl (List.eq_nil_of_length_eq_zero (by scalar_tac)))
  simp only [h0, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    show (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by show length >= 1#u64; scalar_tac]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args, hlen with
    | y0 :: rest, _ => exact ⟨_, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  rw [ha0]; simp only [bind_ok, thread_arg_eq]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hXc.get hx0' h0
  obtain ⟨erest, rfl⟩ : ∃ erest, excaps = e0 :: erest := by
    match excaps, he0 with
    | a :: r, h => simp at h; exact ⟨r, by rw [h]⟩
  have hsp : (Fl4Spec.decodeCopyRegisters (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv)
      ((e0 :: erest).map Prod.fst)) =
      ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
        | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
          (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    rw [List.map_cons, List.map_cons, copy_spec, he01]
    rfl
  rw [hsp]
  rcases copy_src_rel (capV (L.mem s) x0) (erest.map Prod.fst) (σ := σ) with ⟨src, hsrc, hrun⟩ | ⟨hsrc, hrun⟩
  · rw [hsrc]
    simp only [hstall' src, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC0 hcur hs1 hst1'
    refine let_pair2 s ar (fun s1 a1 => do let s2 ← tcb.restart_caller st s1; tcb.copy_registers st arI s2 a1 p src y0)
      _ ?_
    rw [hrc1]; simp only [bind_ok]
    have hthr : capV (L.mem s) x0 = .Thread src := by
      revert hsrc; cases capV (L.mem s) x0 <;> simp [threadArgF]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
          | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
          | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>=
          fun q => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
            (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
            Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.copyRegisters p.bv src.bv (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1)
          (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3) Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
      apply run_liftME_ok
      exact (run_bind_ok hrun _).trans rfl
    have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact AbsSlot.isSlot ⟨ps0, hps01, Or.inl hps0⟩
    refine WP.spec_mono (hC s1 σ1 src y0 ar hs1 hst1' ⟨x0, hxs, hthr⟩ ⟨Z, hX1⟩) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, y, hy, hy1, ⟨th', G', hPl, hCR, hFI, hD, hMO⟩, hX2⟩
    simp only at hr2; subst hr2
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, y, hy, ⟨th', G', Or.inl ⟨rfl, hy1⟩, hPl, hCR, hFI, hD, hMO⟩, hX2⟩
  · rw [hsrc]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    exact run_liftME_err (run_bind_error hrun _)


end


/-! ## BindNotification: the decode, the bind a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The BindNotification leaf at `XTop`** (for the IPC side): from `XTop`,
the caller's restart then `notification::bind_notification` of `p` to `q`,
against the spec's `bind_notification` from `σ1`. -/
def BindXLeaf (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (p q : U64) : Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      let s2 ← notification.bind_notification st s1 p q
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar))
    (Fl4Spec.bindNotification (Z := Unit) p.bv q.bv σ1)

theorem leaf_assoc {m : Result S} {f : S → Result S} {ar : A}
    {P : core.result.Result Unit error.Exc × S × A → Prop}
    (h : (do
        let s1 ← m
        let s2 ← f s1
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ r => P r ⦄) :
    (do
      let (r, s2) ← (do
        let s1 ← m
        let s2 ← f s1
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2))
      ok (r, s2, ar)) ⦃ r => P r ⦄ := by
  simp only [Std.bind_assoc, bind_ok]
  exact h

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's BindNotification at `XTop`**: ScTcb's decode
(`tcb_bind_ntfn_refines`: the target unbound, the cap's receive right, the
notification neither waited on nor bound; the bound words by the endpoint
and notification relations; `NPlaced` by the scheduler relation), then the
leaf (`BindXLeaf`). -/
theorem tcb_bind_ntfnX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbBindNotification)
    (length buf : U64)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ Z.N)
    (blk don : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hL : ∀ q, q ∈ Z.N → (∃ x b w r, IsSlot Z.th x ∧ capV (L.mem s) x = .Notification q b w r) →
      L.mem s (P1.boundA p) = 0#u64 → L.mem s (Notif.nBoundA q) = 0#u64 → ∀ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      BindXLeaf (L := L) AR s ar σ σ1 p q) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBBindNotification p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer := by
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
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
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
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
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
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
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
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
    obtain ⟨σ1, hst⟩ := XTop.restart (L := L) (AR := AR) ⟨Z, hX⟩
    have hx0s : IsSlot Z.th x0 := by
      obtain ⟨e, -, ex, -, ps, hps, he⟩ := hXc.get hx0' h0
      rw [ex]; exact AbsSlot.isSlot (th := Z.th) (sl := e.2) ⟨ps, he, Or.inl hps⟩
    have hl := hL q hqN ⟨x0, b, w, r, hx0s, hc⟩ hb0 hnb σ1 hst ⟨Z, hX⟩
    unfold BindXLeaf at hl
    refine WP.spec_mono (leaf_assoc hl) fun res h => topX_of_leaf hdec hst (fun z hz => ?_) h
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], z.2)) (mem_bind_nd hz rfl)
  all_goals
    rw [hc] at hsp1
    simp only [error.illegal, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hsp1]
    exact run_throw_bind _ _ _


end


/-! ## SetSchedParams: the decode, the install at `WX`, the scheduler step a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The SetSchedParams leaf at `XTop`** (for the Sc side): ScTcb's
`SchedTailHyp` with the state after the fault-handler install at `WX`
(`XTopAt` there), and `XTop` with the IPC relation after the spec's
`set_mcpriority`, `set_priority` and SC step. -/
def SchedTailXHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p mcp prio scv x2 : U64) (scf : Bool) (ssl : Fl4Spec.CslotPtr)
    (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (q : Fl4Spec.ObjRef) (sco : Option (Option Fl4Spec.ObjRef))
    (s2 : S) (a1 : A) (σ2 : Fl4Spec.State Unit) (G2 : MdbGhost),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    th p = some .tcb → mcp.val < 256 → prio.val < 256 →
    (sco = none ↔ scf = false) → (sco = some none → scv = 0#u64) →
    (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) →
    ScDec σ p.bv sco → p ≠ L.idleW s → IsSlot th x2 →
    tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
      ok (.Ok (), s2, a1) →
    (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
    DState (L := L) th s2 σ2 G2 → WX (L := L) AR th s2 a1 σ2 G2 →
    schedTail (st := st) arI s2 a1 p mcp prio scv scf ⦃ r =>
      r.1 = .Ok () ∧ ∃ σa σb σc, ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 ∧
        ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 prio.bv) σa).1 ∧
        ((), σc) ∈ (scStep p.bv sco σb).1 ∧ RelTopM (L := L) r.2.1 σc ∧ XTop (L := L) AR r.2.1 r.2.2 σc ⦄

set_option maxHeartbeats 4000000 in
/-- **SetSchedParams after its checks at `XTop`** (ScTcb's `ssp_tail`): the
restart, the fault-handler install at `WX` (`install_okW`, the deletion's
premises at `XTop`), then the leaf (`SchedTailXHyp`); a preempted install is
the spec's preempted install, `XTop` from `WX`. -/
theorem ssp_tailX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (p : U64) (hp : Z.th p = some .tcb) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (x2 : U64) (e2 : Fl4Spec.Cap × Fl4Spec.CslotPtr)
    (hxe2 : x2 = cslotAddr e2.2) (he21 : e2.1 = absCap (capV (L.mem s) x2)) (ps : U64)
    (hps : Z.th ps = some (.cnode e2.2.2.length)) (hps1 : e2.2.1 = ps.bv)
    (hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2)))
    (y0 y1 scv : U64) (hy0 : y0.val < 256) (hy1 : y1.val < 256) (scf : Bool) (q : Fl4Spec.ObjRef)
    (sco : Option (Option Fl4Spec.ObjRef)) (h1 : sco = none ↔ scf = false) (h2 : sco = some none → scv = 0#u64)
    (h3 : ∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64)
    (hD : ScDec σ p.bv sco) (hpI : p ≠ L.idleW s)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (hdec : DecOut m σ (.invokeTCB (.threadControlSched p.bv ssl (some e2) (some (Fl4Spec.ucast 8 y0.bv, q))
      (some (Fl4Spec.ucast 8 y1.bv, q)) sco)))
    (hH : SchedTailXHyp (L := L) arI AR Z.th s σ ct) (blk call don : Bool) :
    (do
      let s1 ← tcb.restart_caller st s
      tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (capV (L.mem s) x2, x2) y0 y1 scv
        (if scf then (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC)
          else (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT))) ⦃ res =>
      TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don m s res ⦄ := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  obtain ⟨s1, σ1, hrc, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
  rw [hrc]; simp only [bind_ok]; rw [tcs_fault_eq]
  have hxs : IsSlot Z.th x2 := by rw [hxe2]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1) x2 = capV (L.mem s) x2 := hS1.capV hxs
  have hnf := vfh_not_frame hv
  obtain ⟨K, hK, hK6, hB⟩ := hKB
  have hok : NewCapOK Z.th (L.mem s1) (capV (L.mem s) x2) e2.2 := by
    rw [← hc1, hxe2]; exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe2, hc1]; exact hnf)
  have hI := install_okW arI (WX (L := L) AR Z.th) Z.th hP (delHypsW_X arI hXF hXP hXD) K hK hK6 hB s1 s1 ar σ1 Z.G
    hDS1 (WX.restart hX hKA hC hTh hcur s1 σ1 hs1 hS1 hst1) p hp 3 (by simp [tcbSlots])
    layout.tcb.SLOT_FAULT_HANDLER (by simp [layout.tcb.SLOT_FAULT_HANDLER]) (InstFr.refl _ _ _) ssl hAs
    (capV (L.mem s) x2) e2.2 hok (fun _ => vfh_ep hv)
  rw [← hxe2] at hI
  obtain ⟨⟨r, s2, a1⟩, hins, σ', G', hc, hDS', hW2⟩ := spec_exists hI
  have he2 : e2 = (absCap (capV (L.mem s) x2), e2.2) := by rw [← he21]
  rw [hins]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hc with ⟨hr, hx, -⟩ | ⟨hr, hx⟩
  · simp only at hr; subst hr
    rw [← he2] at hx
    refine WP.spec_mono (hH s1 σ1 ar p y0 y1 scv x2 scf ssl e2 q sco s2 a1 σ' G' hs1 (by rw [← hcur]; exact hst1)
      hp hy0 hy1 h1 h2 h3 hD hpI hxs hins hx hDS' hW2) ?_
    rintro ⟨r5, s5, a5⟩ ⟨hr5, σa, σb, σc, ha, hb, hcc, ⟨th', G5, hPl, hCR, hFI, hDo, hMO⟩, hX5⟩
    simp only at hr5; subst hr5
    refine Or.inr ⟨_, hdec, σ1, hst1, (.ok [], σc), ?_, ⟨th', G5, Or.inl ⟨rfl, rfl⟩, hPl, hCR, hFI, hDo, hMO⟩, hX5⟩
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
      (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1).1
    simp only [Fl4Spec.invokeTcb]
    exact mem_bindE_ok hx (mem_bindE_ok (mem_liftE ha) (mem_bindE_ok (mem_liftE hb)
      (mem_bindE_ok (mem_liftE hcc) (Set.mem_singleton _))))
  · simp only at hr; subst hr
    rw [← he2] at hx
    obtain ⟨Z', -, -, hX', -, -⟩ := hW2
    refine (WP.spec_ok _).2 (Or.inr ⟨_, hdec, σ1, hst1, (.error (), σ'), ?_, ⟨Z'.th, Z'.G, Or.inr ⟨rfl, rfl⟩,
      hX'.rel.1, hX'.rel.2.1, hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ⟨Z', hX'⟩⟩)
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
      (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1).1
    simp only [Fl4Spec.invokeTcb]
    exact mem_bindE_err hx

set_option maxHeartbeats 8000000 in
/-- **TcbXRest's SetSchedParams at `XTop`**: ScTcb's decode
(`tcb_set_sched_params_refines`: `McpRel` [J], the authority's and the SC
cap's objects among `Z.T`/`Z.C` [J], no null SC [J], the target not idle
[J]; the SC checks by the scheduler and notification relations at `XTop`),
then `ssp_tailX` (the leaf `SchedTailXHyp`, the Sc side's). -/
theorem tcb_set_sched_paramsX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
   
    (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSchedParams)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (hpI : p ≠ L.idleW s)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hM : McpRel Z.T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C) (hC0 : ∀ q ∈ Z.C, q ≠ 0#u64)
    (hH : SchedTailXHyp (L := L) arI AR Z.th s σ ct)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetSchedParams p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hS : SchedRel st Z.N Z.T Z.C Z.c s σ := hX.fin.1.1.1
  have hR : Notif.NtfnStateRel Z.N Z.T (L.mem s) σ := hX.fin.1.1.2.2.1
  have hpT : p ∈ Z.T := hTh p hp
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_ssp_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSchedParams
    by_cases ha : args.length < 2
    · rw [whenE_pos (by simpa using ha)]
      exact run_throw_bind _ _ _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_throw_bind _ _ _
  unfold tcb.decode_set_sched_params tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hXc.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hXc.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  have ha1 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 1#u64 y1 (by simp))
  simp only [ha0, ha1, bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hXc.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hXc.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hXc.get hx2' h2
  have hexl : ¬ excaps.length < 3 := by
    have := (List.getElem?_eq_some_iff.1 he2).1; omega
  -- the spec up to the authority's cap
  have hspec0 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = ((match e0.1 with
        | .threadCap tcbPtr => Fl4Spec.NonDetE.returnOk tcbPtr
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.checkPrio (Z := Unit) y0.bv q >>= fun _ => Fl4Spec.checkPrio (Z := Unit) y1.bv q >>= fun _ =>
        Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ := by
    unfold Fl4Spec.decodeSetSchedParams
    rw [whenE_neg (by simp), retOk_bind, whenE_neg hexl, retOk_bind, retOk_bind, retOk_bind, retOk_bind,
      retOk_bind, retOk_bind, he0, he1, he2, the_some, the_some, the_some]
    generalize e0.1 = cc
    cases cc <;> rfl
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  swap
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hspec0, he01]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_throw_bind _ _ _
  obtain ⟨q, hq⟩ := hth
  rw [thread_arg_thread s 1#u64 hq]
  simp only [bind_ok, check_prio_eq]
  have hqT := hcapT h0 q hq
  have he0' : e0.1 = .threadCap q.bv := by rw [he01, hq]; rfl
  rw [he0'] at hspec0
  simp only [] at hspec0
  rw [retOk_bind] at hspec0
  have hcp0 := checkPrio_run hM hqT y0.bv
  have hcp1 := checkPrio_run hM hqT y1.bv
  obtain ⟨xq, hkq, hmq⟩ := hM q hqT
  have hmq8 : (L.mem s (mcpA q)).val < 256 := by rw [hmq]; exact xq.tcbMcpriority.isLt
  by_cases hg0 : y0 > L.mem s (mcpA q)
  · rw [ite_eq_left hg0]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg0)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg0]
  simp only [bind_ok]
  by_cases hg1 : y1 > L.mem s (mcpA q)
  · rw [ite_eq_left hg1]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg1)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg1]
  simp only [bind_ok]
  have hy0 : y0.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y0.val := hg0; omega
  have hy1 : y1.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y1.val := hg1; omega
  have hspec1 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg1), retOk_bind]
  obtain ⟨Q, R', hcL, hsL⟩ := hS.lists
  obtain ⟨xp, hkp, -, -, hxts, -⟩ := hsL.tcb p hpT
  have hsc0 : obj.Tcb.sc st p s = ok (L.mem s (P1.scA p)) := by
    obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Tcb.sc.spec (L := L) s p); exact hw
  -- after the SC check: the fault handler, the restart and the invocation
  have hafter : ∀ (scv : U64) (sco : Option (Option Fl4Spec.ObjRef)),
      (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1).run σ = ({(.ok sco, σ)}, False) →
      (sco = none ↔ (L.mem s (P1.scA p) != scv) = false) → (sco = some none → scv = 0#u64) →
      (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) → ScDec σ p.bv sco →
      (do
        let i ← lift (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO)
        let flags ← lift (i ||| tcb.SCHED_UPDATE_FAULT)
        if (L.mem s (P1.scA p) != scv) = true then do
            let flags1 ← lift (flags ||| tcb.SCHED_UPDATE_SC)
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags1
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)
          else do
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)) ⦃ res => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
    intro scv sco hdus hs1 hs2 hs3 hD
    simp only [lift, bind_ok, slot_cap_eq, capAt_capV, vfh_eq]
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2))
    · simp only [decide_eq_true hv, ↓reduceIte]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (.threadControlSched p.bv ssl (some e2)
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he21]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e2) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]; rfl
      by_cases hscf : (L.mem s (P1.scA p) != scv) = true
      · simp only [hscf, ↓reduceIte]
        have h1' : sco = none ↔ true = false := by rw [hs1, hscf]
        have := ssp_tailX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp ct hct hcur hact ssl hAs x2 e2 hxe2 he21 ps2 hps2 hps21
          hv y0 y1 scv hy0 hy1 true q.bv sco h1' hs2 hs3 hD hpI _ (DecOut.of_eq hdec) hH blk call don
        simp only [↓reduceIte] at this
        exact this
      · simp only [Bool.not_eq_true] at hscf
        simp only [hscf, Bool.false_eq_true, ↓reduceIte]
        have h1' : sco = none ↔ false = false := by rw [hs1, hscf]
        have := ssp_tailX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp ct hct hcur hact ssl hAs x2 e2 hxe2 he21 ps2 hps2 hps21
          hv y0 y1 scv hy0 hy1 false q.bv sco h1' hs2 hs3 hD hpI _ (DecOut.of_eq hdec) hH blk call don
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        exact this
    · simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      have hiv : ∀ (scf : Bool), (ok ((.Err (.Sys (.InvalidCapability 3#u64)) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
        intro _
        refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 3, ?_, Or.inr ⟨3#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
        apply run_liftME_err
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he21]; exact hv)]
        exact run_bind_error (run_throw_bind _ _ _) _
      split <;> exact hiv true
  have hpre : ∀ cp : Fl4Spec.Cap, e1.1 = cp →
      (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl cp >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rintro cp rfl; exact hspec1
  unfold tcb.sched_params_sc
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc1 : capV (L.mem s) x1
  case Null =>
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    rw [hct]
    simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
    by_cases hpc : p = ct
    · simp only [decide_eq_true hpc, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hspec1]
      refine run_bind_error ?_ _
      rw [dus_null hkp ssl, whenE_pos (by rw [hcur, hpc])]
      exact run_throw_bind _ _ _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte, bind_ok, hsc0]
      have hpc' : ¬ p.bv = σ.curThread := by rw [hcur]; intro e; exact hpc (P1.eq_of_bv e)
      refine hafter 0#u64 _ (by rw [he11, hc1]; simp only [absCap]; rw [dus_null hkp ssl, whenE_neg hpc', retOk_bind]; rfl)
        ?_ (fun _ => rfl) (fun v h => by split at h <;> cases h)
        ⟨xp, hkp, fun h => ⟨hpc', fun e => (by simp [e] at h)⟩, fun v h => (by split at h <;> cases h)⟩
      rw [hxts]
      by_cases hz : L.mem s (P1.scA p) = 0#u64
      · simp [hz, Notif.optRef_zero]
      · simp [hz, Notif.optRef_ne hz]
  case SchedContext ptr sz =>
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    have hpC := hcapC h1 ptr sz hc1
    have hptr0 := hC0 ptr hpC
    obtain ⟨y, n, hks, hx⟩ := hsL.scs ptr hpC
    have hne : Fl4Spec.scActive y = true → y.scRefills ≠ [] := fun ha => by
      rw [(hx.strong ha).refills]; exact refills_ne (hx.strong ha).wf
    have hdus := dus_sc hkp hks hne ssl (sz.val - Fl4Spec.minSchedContextBits)
    have hst := (hR.at_tcb hpT hkp).st
    have hxt' : y.scTcb = Notif.optRef (L.mem s (scW ptr 24#u64)) := hx.tcb
    have hcons : (((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = none ↔
          (L.mem s (P1.scA p) != ptr) = false) ∧
        ((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some none → ptr = 0#u64) ∧
        (∀ v, (if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some (some v) →
          v = ptr.bv ∧ ptr ≠ 0#u64)) := by
      rw [hxts]
      refine ⟨?_, (fun h => by split at h <;> cases h), (fun v h => by split at h <;> cases h; exact ⟨rfl, hptr0⟩)⟩
      simp only [ne_eq, bv_optRef_some hptr0]
      by_cases e : L.mem s (P1.scA p) = ptr <;> simp [e]
    have hillT : (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl
          (.schedContextCap ptr.bv (sz.val - Fl4Spec.minSchedContextBits))).run σ =
          ({(.error .illegalOperation, σ)}, False) →
        (ok ((.Err (.Sys .IllegalOperation) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
      intro h
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hspec1]
      exact run_bind_error h _
    simp only [hsc0, bind_ok]
    by_cases hip : L.mem s (P1.scA p) = ptr
    · -- the thread's own SC
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hxts, hip, Notif.optRef_ne hptr0]; simp
      rw [if_neg (show ¬ (L.mem s (P1.scA p) != ptr) = true by simp [hip])]
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

    · have hne1 : (L.mem s (P1.scA p) != ptr) = true := by simp [hip]
      simp only [hne1, ↓reduceIte]
      by_cases hi0 : L.mem s (P1.scA p) = 0#u64
      swap
      · have : (L.mem s (P1.scA p) != 0#u64) = true := by simp [hi0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hxts, Ne, bv_optRef_some hptr0]; exact hip,
          Or.inl (by rw [hxts, Notif.optRef_ne hi0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (P1.scA p) != 0#u64) = false := by simp [hi0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hscT : obj.Sc.tcb st ptr s = ok (L.mem s (scW ptr 24#u64)) := by
        obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Sc.tcb.spec (L := L) s ptr); rw [scTcbA_eq] at hw; exact hw
      simp only [hscT, bind_ok]
      have hx0n : xp.tcbSchedContext = none := by rw [hxts, hi0, Notif.optRef_zero]
      by_cases ht0 : L.mem s (scW ptr 24#u64) = 0#u64
      swap
      · have : (L.mem s (scW ptr 24#u64) != 0#u64) = true := by simp [ht0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hx0n]; simp, Or.inr (by rw [hxt', Notif.optRef_ne ht0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (scW ptr 24#u64) != 0#u64) = false := by simp [ht0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hx0n, hxt', ht0, Notif.optRef_zero]; simp
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun _ => by rw [← hr, eb])⟩)⟩⟩
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun hq => absurd hq hb)⟩)⟩⟩
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

  all_goals
    rw [he11, hc1] at hspec1
    simp only [error.invalid_cap, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 2, ?_, Or.inr ⟨2#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    rw [hspec1]
    exact run_bind_error (dus_other hkp ssl (by simp [absCap]) (by simp [absCap])) _


end


/-! ## ReadRegisters: the decode, the register read and its reply a leaf -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The ReadRegisters leaf at `XTop`** (for the IPC side: FL4's
`read_registers` replies itself): after the caller's restart, at `XTop`,
FL4's `read_registers` (with the reply when called) against the spec's
`invoke_tcb ReadRegisters` then its reply tail (`specTail`), the caller
no longer `Restart`, `XTop` after. -/
def ReadRegsXHyp (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64)
    (blk call don : Bool) : Prop :=
  ∀ s1 σ1 (flags n : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → XTop (L := L) AR s1 a σ1 →
    tcb.read_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n call ⦃ r =>
      L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ rr σy,
        (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.readRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
        ∃ z ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) r.1 z.2 ∧ XTop (L := L) AR r.1 r.2 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **TcbXRest's ReadRegisters at `XTop`**: TcbCtl's decode
(`tcb_read_regs_refines`), the restart, then the leaf (`ReadRegsXHyp`). -/
theorem tcb_read_regsX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC0 : CurRun σ)
    (hDI : DelInv Z.th (L.mem s)) (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbReadRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (hR : p ≠ ct → ReadRegsXHyp (L := L) arI AR s σ ct p blk call don) :
    TcbOKRX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBReadRegisters p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeReadRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKRX
  rw [decode_read_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_read_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp at h; scalar_tac
    | [_], h => exfalso; simp at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok, nregs_eq]
  have hsp : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      (Fl4Spec.decodeReadRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    intro _
    simp only [Fl4Spec.decodeReadRegisters, List.map_cons, nregs_spec, retOk_bind]
  rw [hsp (fun _ => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.suspend 0))]
  have hrng := range20_iff y1
  by_cases hr : 1 ≤ y1.val ∧ y1.val ≤ 20
  · have hn1 : ¬ y1 < 1#u64 := by scalar_tac
    have hn2 : ¬ y1 > 20#u64 := by scalar_tac
    simp only [hn1, hn2, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
    have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ = ({(.ok (), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_pos (hrng.2 hr)]; rfl
    by_cases hpc : p = ct
    · subst hpc
      simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
      refine (WP.spec_ok _).2 ?_
      apply Or.inl
      refine ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, ⟨Z, hX⟩⟩
      apply run_liftME_err
      rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
      have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
        rw [← hcur]; exact hst1
      obtain ⟨hX1, -, -⟩ := hX.restart' hC0 hcur hs1 hst1'
      rw [hrc1]; simp only [bind_ok, lift]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
            let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
            Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
            Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
              Fl4Spec.ArchDefaultExtraRegisters))).run σ =
          ({(.ok (.invokeTCB (.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
            Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
        apply run_liftME_ok
        rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
          s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc), retOk_bind]
        rfl
      refine WP.spec_bind (hR hpc s1 σ1 y0 y1 ar hs1 hst1' ⟨Z, hX1⟩) ?_
      rintro ⟨s2, a2⟩ ⟨hne, rr, σy, hm, z, hz, hRz, hXz⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, rr, σy, hm, z, hz, hRz, hXz⟩)
  · have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ =
        ({(.error (.rangeError 1 (BitVec.ofNat 64 20)), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_neg (fun h => hr (hrng.1 h))]; rfl
    have herr : ErrRel (.Sys (.RangeError 1#u64 20#u64)) (.rangeError 1 (BitVec.ofNat 64 20)) :=
      Or.inl ⟨rfl, rfl⟩
    by_cases hn1 : y1 < 1#u64
    · simp only [hn1, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr⟩, ⟨Z, hX⟩⟩)
      exact run_liftME_err (run_bind_error hrc _)
    · have hn2 : y1 > 20#u64 := by scalar_tac
      simp only [hn1, hn2, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr⟩, ⟨Z, hX⟩⟩)
      exact run_liftME_err (run_bind_error hrc _)


end

end

end Fl4Proofs.P3
