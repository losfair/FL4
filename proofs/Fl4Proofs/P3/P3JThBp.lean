/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at SetBreakpoint (16)
and UnsetBreakpoint (18), for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than
7 / 15 / 16 / 18 / 20, or SetEPTRoot}.

* `JAtZ.tcbWordProjW`: a word at offset `< 4096` (8-aligned) of a TCB of `Z.T` is a `ProjW` write
  (`writesIn_wr`, `ProjW`'s object clause).
* **`tcb_unset_bpJSt`** / **`tcb_set_bpJSt`**: XTopJointTcb's `tcb_unset_bpJ` / `tcb_set_bpJ` with the post
  `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)` (proof text unchanged but the posts): the restart's footprint
  `stsProjW`, the two debug words by `tcbWordProjW`, joined by `WritesIn.projW_trans`.
* **`decThBpSt`** (any flags): the dispatch leaf (as P3JThTls's `decThTlsSt`, the extension labels by TcbExt's
  `ext_lbl`). The arguments' relation `ArgRel … 5` (formerly an input of `decode_invocation_threadJ_stepMMT`) is the
  third conjunct of `JAtZ.argsJ` at the dispatch state (XTopJointKEntry13P l.540 reads it there the same way), and
  `ArgRel … 1` follows from it: so neither is a premise.
* `ThBp l`: `l` is 16 or 18. `ThHard4 l`: `ThHard3 l ∧ ¬ ThBp l`. `IsRestCap12`. `restCap11_of12`, `restCap12_of`.
  **`midDecRest11_of_bp`** / **`invDecRest11_of_bp`**, `midDecStWL_of_11` / `invDecStWL_of_11`.
* **`DispStabFootLze` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap12`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzd_of_Lze`** (under the tops' platform facts), **`dispStabFootLze_of_Lzd`**; top
  **`kernel_entry_runMcWKR_sysLze`** (globals verbatim as `_sysLzd`).

Premise honesty: `DispStabFootLze`'s decode fields are `DispStabFootLzd`'s at the smaller antecedent
(`IsRestCap12 → IsRestCap11`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLze` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThMcp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 40) **A word of a thread of `Z.T` is a `ProjW` write** (module docstring). -/
theorem JAtZ.tcbWordProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) {wa : U64} {Kv : Nat}
    (hK : Kv < 4096 ∧ Kv % 8 = 0) (hwav : wa.val = t.val + Kv) (s1 : S) (v : U64) :
    P1.WritesIn st s1 (L.wr s1 wa v) (Mc.ProjW (L := L) H Cs s1) := by
  have hta := J.ip.e.tcb t ht
  have h1 := hta.align
  have h2 := hta.fits
  refine (P1.writesIn_wr (s := s1) (v := v) (show P1.Aligned wa by unfold P1.Aligned; rw [hwav]; omega)).mono ?_
  rintro b rfl
  exact Or.inl ⟨t, .tcb, J.zH.1 t ht, by rw [hwav]; omega, by rw [hwav]; simp only [P1.HKind.bits]; omega⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **UnsetBreakpoint at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's
`tcb_unset_bpJ`; module docstring). -/
theorem tcb_unset_bpJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .unsetBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBUnsetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, x, hrc1, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
      have h := stsProjW J (J.thT ct (J.xtop.curTcb hcur).1) sched.TS_RESTART
      rw [hs1, WP.spec_ok] at h; exact h
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
    have hpf := (J1.ip.e.tcb p hpT).fits
    refine WP.spec_bind (unset_bp_wr s1 p bp hbpv) ?_
    rintro s2 ⟨v, rfl⟩
    obtain ⟨V2, J2⟩ := J1.dbgWrJ hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) 0#u64
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨JStab.mv (G := Z.G) (V := V2) ⟨_, _, Ac1, Lst1, D1, J3⟩,
          (W1.projW_trans (J.tcbWordProjW hpT (Kv := 448 + 40) ⟨by omega, by omega⟩
            (by rw [dbgA_val (by omega) (by decide)]; simp) s1 v)).projW_trans
          (J.tcbWordProjW hpT (Kv := 448 + 8 * bp.val) ⟨by omega, by omega⟩
            (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) _ 0#u64)⟩⟩)

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **SetBreakpoint at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_set_bpJ`;
module docstring). -/
theorem tcb_set_bpJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 5)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBSetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_setbp_eq arI s ar p _ hstall, hdec0]
  have hc : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).buf = buf := rfl
  obtain ⟨bp, h0, g0⟩ := arg_rel hA hct hcur _ hc 0#u64 (by decide)
  obtain ⟨vaddr, h1, g1⟩ := arg_rel hA hct hcur _ hc 1#u64 (by decide)
  obtain ⟨ty, h2, g2⟩ := arg_rel hA hct hcur _ hc 2#u64 (by decide)
  obtain ⟨size, h3, g3⟩ := arg_rel hA hct hcur _ hc 3#u64 (by decide)
  obtain ⟨rw, h4, g4⟩ := arg_rel hA hct hcur _ hc 4#u64 (by decide)
  rw [set_bp_checked_eq s p _ h0 h1 h2 h3 h4]
  have hsp := set_bp_spec_run σ buffer p.bv g0 g1 g2 g3 g4
  have hrel := bpErr_rel bp vaddr ty size rw
  cases hF : bpErrF bp vaddr ty size rw with
  | some e =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | none => rw [hF, hS] at hrel; exact hrel.elim
    | some e' =>
      rw [hF, hS] at hrel
      dsimp only at hrel
      dsimp only
      simp only [bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨e, rfl, rfl, ⟨e', ?_, hrel⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp, hS]
  | none =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | some e' => rw [hF, hS] at hrel; exact hrel.elim
    | none =>
    have hbpv := bpErrF_bp hF
    simp only
    obtain ⟨s1, σ1, x, hrc1, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
      have h := stsProjW J (J.thT ct (J.xtop.curTcb hcur).1) sched.TS_RESTART
      rw [hs1, WP.spec_ok] at h; exact h
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.setBreakpoint p.bv bp.bv vaddr.bv ty.bv size.bv rw.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, hS]
    have hpf := (J1.ip.e.tcb p hpT).fits
    have hin : (do
        let s2 ← debug.set_breakpoint st s1 p bp vaddr ty size rw
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ x =>
          ∃ v, x = (.Ok (), L.wr (L.wr s1 (dbgA p bp) vaddr) (dbgA p 5#u64) v) ⦄ :=
      WP.spec_bind (set_bp_wr (st := st) s1 p bp vaddr ty size rw) (fun s2 ⟨v, h⟩ => (WP.spec_ok _).2 ⟨v, by rw [h]⟩)
    refine WP.spec_bind hin ?_
    rintro x ⟨v, rfl⟩
    obtain ⟨V2, J2⟩ := J1.dbgWrJ hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) vaddr
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨JStab.mv (G := Z.G) (V := V2) ⟨_, _, Ac1, Lst1, D1, J3⟩,
          (W1.projW_trans (J.tcbWordProjW hpT (Kv := 448 + 8 * bp.val) ⟨by omega, by omega⟩
            (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) s1 vaddr)).projW_trans
          (J.tcbWordProjW hpT (Kv := 448 + 40) ⟨by omega, by omega⟩
            (by rw [dbgA_val (by omega) (by decide)]; simp) _ v)⟩⟩)

end

/-- (p3J gen 40) The breakpoint labels: SetBreakpoint (16), UnsetBreakpoint (18). -/
def ThBp (l : U64) : Prop := l = fl4_abi.label.TCBSetBreakpoint ∨ l = fl4_abi.label.TCBUnsetBreakpoint

/-- (p3J gen 40) The Thread labels left after the breakpoint labels. -/
def ThHard4 (l : U64) : Prop := ThHard3 l ∧ ¬ ThBp l

/-- (p3J gen 40) The caps left after the breakpoint leaf, with the message label. -/
def IsRestCap12 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard4 l
  | _, _ => False

theorem restCap11_of12 {cp : capability.Cap} {l : U64} (h : IsRestCap12 cp l) : IsRestCap11 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap12_of {cp : capability.Cap} {l : U64} (h : IsRestCap11 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ ThBp l) : IsRestCap12 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem setBp_nonIns : TcbNonIns fl4_abi.label.TCBSetBreakpoint := by
  unfold TcbNonIns fl4_abi.label.TCBSetBreakpoint fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

theorem unsetBp_nonIns : TcbNonIns fl4_abi.label.TCBUnsetBreakpoint := by
  unfold TcbNonIns fl4_abi.label.TCBUnsetBreakpoint fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at SetBreakpoint or UnsetBreakpoint, any flags** (module docstring). -/
theorem decThBpSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
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
    (hl : ThBp info.label) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  have hPl : Placed Z.th := J.xtop.rel.1
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  rcases hl with hl | hl
  · rw [hl]
    obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon fl4_abi.label.TCBSetBreakpoint
    have hl5 : fl4_abi.label.TCBSetBreakpoint.val ≠ 5 ∧ fl4_abi.label.TCBSetBreakpoint.val ≠ 8 ∧
        fl4_abi.label.TCBSetBreakpoint.val ≠ 9 ∧ fl4_abi.label.TCBSetBreakpoint.val ≠ 10 ∧
        fl4_abi.label.TCBSetBreakpoint.val ≠ 11 := by simp [fl4_abi.label.TCBSetBreakpoint]
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
      (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD setBp_nonIns hMb) fun r h => by split <;> exact h)
      (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
    refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
    left
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
        simp [tcbExtOf])
      exact tcb_set_bpJSt s' a' σb J hnib p hpT sl' hg he _ buf ct hct (J.stallT p hpT) buffer hA5 call
        _ e bl don _ ci sl exs
    · simp only [↓reduceIte]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  · rw [hl]
    obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon fl4_abi.label.TCBUnsetBreakpoint
    have hl5 : fl4_abi.label.TCBUnsetBreakpoint.val ≠ 5 ∧ fl4_abi.label.TCBUnsetBreakpoint.val ≠ 8 ∧
        fl4_abi.label.TCBUnsetBreakpoint.val ≠ 9 ∧ fl4_abi.label.TCBUnsetBreakpoint.val ≠ 10 ∧
        fl4_abi.label.TCBUnsetBreakpoint.val ≠ 11 := by simp [fl4_abi.label.TCBUnsetBreakpoint]
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
      (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD unsetBp_nonIns hMb) fun r h => by split <;> exact h)
      (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
    refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
    left
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
        simp [tcbExtOf])
      exact tcb_unset_bpJSt s' a' σb J hnib p hpT sl' hg he _ buf ct hct (J.stallT p hpT) buffer
        (fun i hi => hA5 i (by omega)) call _ e bl don _ ci sl exs
    · simp only [↓reduceIte]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap11` from the breakpoint leaf** (module docstring). -/
theorem midDecRest11_of_bp (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ ThBp info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThBpSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap12_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap11` from the breakpoint leaf** (module docstring). -/
theorem invDecRest11_of_bp (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ ThBp info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThBpSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap12_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap11` gives it at `KW ∧ IsRestCap12` (antitone). -/
theorem midDecStWL_of_11 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap11_of12 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap11` gives it at `KW ∧ IsRestCap12` (antitone). -/
theorem invDecStWL_of_11 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap11 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap11_of12 hW.2⟩

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

/-- (p3J gen 40) **`DispStabFootLze` [J]**: `DispStabFootLzd` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetMCPriority /
UnbindNotification / Set- and UnsetBreakpoint / SetTLSBase, or SetEPTRoot (module docstring). -/
structure DispStabFootLze (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzd.invDecRest` at `KW ∧ IsRestCap12`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzd.midDecRest` at `KW ∧ IsRestCap12`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap12 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzd.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzd.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLze → DispStabFootLzd`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzd_of_Lze (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLze (L := L) arI AR MR s a σ) :
    DispStabFootLzd (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest11_of_bp hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest11_of_bp hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzd → DispStabFootLze`** (the honesty claim: `DispStabFootLze` is implied). -/
theorem dispStabFootLze_of_Lzd {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzd (L := L) arI AR MR s a σ) : DispStabFootLze (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_11 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_11 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLze` only** (`hLze` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLze [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLze : DispStabFootLze (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzd hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzd_of_Lze hA hnd hM hIp hKD hLze)

end

end Fl4Proofs.P3.Mc
