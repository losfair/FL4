/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at SetMCPriority (7),
for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than 7 / 15 / 20, or SetEPTRoot}.

* `JAtZ.mcpProjW`: the `MCP` word of a TCB of `Z.T` (`writesIn_wr`, `obj_projW`).
* **`tcb_set_mcpJSt`**: XTopJointTcb's `tcb_set_mcpJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts and the restart's footprint `stsProjW`, joined by `WritesIn.projW_trans`).
* **`decThMcpSt`** (any flags): the dispatch leaf (as P3JThTls's `decThTlsSt`). The extra caps' relation `XcRel` at
  the dispatch state is FrontEndExtra's `ExtraOK.xc` of the front's `ExtraOK` (`JAtZ.frontJ`), and the authority
  among the TCBs (`hcapT`) from it and the slots' caps (`CapValid`, `JAtZ.thT`), as StallNarrowTcb's
  `decode_invocation_threadJ_stepMMT` derives it: so neither is a premise.
* `ThHard3 l`: `ThHard2 l ∧ l ≠ TCBSetMCPriority`. `IsRestCap11`. `restCap10_of11`, `restCap11_of`.
  **`midDecRest10_of_mcp`** / **`invDecRest10_of_mcp`**, `midDecStWL_of_10` / `invDecStWL_of_10`.
* **`DispStabFootLzd` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap11`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzc_of_Lzd`** (under the tops' platform facts), **`dispStabFootLzd_of_Lzc`**; top
  **`kernel_entry_runMcWKR_sysLzd`** (globals verbatim as `_sysLzc`).

Premise honesty: `DispStabFootLzd`'s decode fields are `DispStabFootLzc`'s at the smaller antecedent
(`IsRestCap11 → IsRestCap10`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzd` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThTls
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 40) **The `MCP` word of a thread of `Z.T` is a `ProjW` write** (module docstring). -/
theorem JAtZ.mcpProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (s1 : S) (v : U64) :
    P1.WritesIn st s1 (L.wr s1 (mcpA t) v) (Mc.ProjW (L := L) H Cs s1) := by
  refine (P1.writesIn_wr (s := s1) (v := v) (mcpA_aligned J.ip.e.tcb ht)).mono ?_
  rintro b rfl
  exact Mc.obj_projW J.kern.heap (k := .tcb) (J.zH.1 t ht) (by simp [P1.HKind.bits])

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **SetMCPriority at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_set_mcpJ`;
module docstring). -/
theorem tcb_set_mcpJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetMCPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBSetMCPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  have hM := J.mcp
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hctT : ct ∈ Z.T := J.thT ct (hX.curTcb (J.curEq hct).1).1
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
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
    obtain ⟨xq, hkq, hmq, -⟩ := hM q (hcapT h0 q hq)
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
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, x1, hrc, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
      have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
        have h := stsProjW J hctT sched.TS_RESTART
        rw [hs1, WP.spec_ok] at h; exact h
      rw [hrc]; simp only [bind_ok, tcs_mcp]
      refine (WP.spec_ok _).2 ?_
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      obtain ⟨x, hkx, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
      obtain ⟨V2, J2⟩ := J1.mcpWrJ hpT hkx y0 (Fl4Spec.ucast 8 y0.bv)
        (by rw [Ipc.ucast8_specPrio, Sched.specPrio_toNat hlt])
      refine Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1,
        J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac1, Lst1, D1, J2⟩, W1.projW_trans (J1.mcpProjW hpT s1 y0)⟩⟩
      rw [invoke_mcp_run hkx]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
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

/-- (p3J gen 40) The Thread labels left after SetMCPriority. -/
def ThHard3 (l : U64) : Prop := ThHard2 l ∧ l ≠ fl4_abi.label.TCBSetMCPriority

/-- (p3J gen 40) The caps left after the SetMCPriority leaf, with the message label. -/
def IsRestCap11 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard3 l
  | _, _ => False

theorem restCap10_of11 {cp : capability.Cap} {l : U64} (h : IsRestCap11 cp l) : IsRestCap10 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap11_of {cp : capability.Cap} {l : U64} (h : IsRestCap10 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSetMCPriority) : IsRestCap11 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem mcp_nonIns : TcbNonIns fl4_abi.label.TCBSetMCPriority := by
  unfold TcbNonIns fl4_abi.label.TCBSetMCPriority fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at SetMCPriority, any flags** (module docstring). -/
theorem decThMcpSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
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
    (hl : info.label = fl4_abi.label.TCBSetMCPriority) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  have hcapT : exAt e 0 ≠ 0#u64 → ∀ q, capV (L.mem s') (exAt e 0) = .Thread q → q ∈ (Z.mv Z.G V').T := by
    intro hx q hq
    have h0 := hXc.2 0 (exAt e 0) rfl
    obtain ⟨y, hy⟩ : ∃ y, exs[0]? = some y := by
      rcases exs with _ | ⟨y, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨y, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 y hy
    have hA0 : AbsSlot Z.th y.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hq]))
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetMCPriority
  have hl5 : fl4_abi.label.TCBSetMCPriority.val ≠ 5 ∧ fl4_abi.label.TCBSetMCPriority.val ≠ 8 ∧
      fl4_abi.label.TCBSetMCPriority.val ≠ 9 ∧ fl4_abi.label.TCBSetMCPriority.val ≠ 10 ∧
      fl4_abi.label.TCBSetMCPriority.val ≠ 11 := by simp [fl4_abi.label.TCBSetMCPriority]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD mcp_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_set_mcpJSt s' a' σb J hnib p hpT sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen hArgs
      (J.stallT p hpT) call sl e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) exs hXc hcapT bl don ci buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap10` from the SetMCPriority leaf** (module docstring). -/
theorem midDecRest10_of_mcp (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetMCPriority
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThMcpSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap11_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap10` from the SetMCPriority leaf** (module docstring). -/
theorem invDecRest10_of_mcp (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetMCPriority
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThMcpSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap11_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap10` gives it at `KW ∧ IsRestCap11` (antitone). -/
theorem midDecStWL_of_10 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap10_of11 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap10` gives it at `KW ∧ IsRestCap11` (antitone). -/
theorem invDecStWL_of_10 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap10 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap10_of11 hW.2⟩

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

/-- (p3J gen 40) **`DispStabFootLzd` [J]**: `DispStabFootLzc` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetMCPriority /
UnbindNotification / SetTLSBase, or SetEPTRoot (module docstring). -/
structure DispStabFootLzd (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzc.invDecRest` at `KW ∧ IsRestCap11`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzc.midDecRest` at `KW ∧ IsRestCap11`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzc.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzc.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzd → DispStabFootLzc`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzc_of_Lzd (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzd (L := L) arI AR MR s a σ) :
    DispStabFootLzc (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest10_of_mcp hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest10_of_mcp hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzc → DispStabFootLzd`** (the honesty claim: `DispStabFootLzd` is implied). -/
theorem dispStabFootLzd_of_Lzc {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzc (L := L) arI AR MR s a σ) : DispStabFootLzd (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_10 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_10 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzd` only** (`hLzd` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzd [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzd : DispStabFootLzd (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzc hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzc_of_Lzd hA hnd hM hIp hKD hLzd)

end

end Fl4Proofs.P3.Mc
