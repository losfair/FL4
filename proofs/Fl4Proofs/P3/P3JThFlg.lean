/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at SetFlags (21), for
both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than 7 / 14 / 15 / 16 / 18 / 19 / 20 /
21, or SetEPTRoot}.

* **`tcb_set_flagsJSt`**: XTopJointTcb's `tcb_set_flagsJ` (a replying label, `TcbOKRX`) with the post
  `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)` (proof text unchanged but the posts: the restart by `stsProjW`, the
  flags word (offset 3456 of the target's TCB) by `writesIn_wr` + `obj_projW`, the FPU release writes no memory
  (`fpuReleaseJ'` keeps the store), the uncalled tail by `stsProjW`, the called tail by P3JThSs's
  `replyWords1JSt`; the tail's ghosts are carried by a `JStab Z3 → JStab Z` map, `JStab.mv`).
* **`decThFlgSt`** (any flags): the dispatch leaf. Its inputs of the non-stable chain are derived at the dispatch
  state: `FlagsRel` by XTopJointKEntry38E's `JAtZ.flagsRel` (`McpRel`'s flags part, a field of `JAtZ`); the
  arguments by `JAtZ.argsJ`; `ARKeep` [P] is the tops' `ARIface` (`ARIface.toARKeep`), passed as a hypothesis.
* `ThHard7 l`: `ThHard6 l ∧ l ≠ TCBSetFlags`. `IsRestCap15`. `restCap14_of15`, `restCap15_of`.
  **`midDecRest14_of_flg`** / **`invDecRest14_of_flg`**, `midDecStWL_of_14` / `invDecStWL_of_14`.
* **`DispStabFootLzh` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap15`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzg_of_Lzh`** (under the tops' platform facts, now incl. `ARIface`), **`dispStabFootLzh_of_Lzg`**;
  top **`kernel_entry_runMcWKR_sysLzh`** (globals verbatim as `_sysLzg`).

Premise honesty: `DispStabFootLzh`'s decode fields are `DispStabFootLzh`'s at the smaller antecedent
(`IsRestCap15 → IsRestCap14`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzh` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThSs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- (p3J gen 40) **SetFlags at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_set_flagsJ`;
module docstring). -/
theorem tcb_set_flagsJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ)
    (hFl : FlagsRel Z.T (L.mem s) σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (hK : ARKeep arI AR)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKRX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBSetFlags p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hpT : p ∈ Z.T := J.thT p hp
  have hctT : ct ∈ Z.T := J.thT ct htcb
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  unfold TcbOKRX
  rw [decode_flags_eq arI s ar p _ hstall, setFlags_dec slbl hlbl]
  by_cases h1 : length < 2#u64
  · unfold tcb.decode_set_flags
    simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage,
      setFlags_trunc σ p.bv _ (by rw [List.length_map, ← hlen]; scalar_tac), Or.inl trivial⟩, hJ0⟩)
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨s1, σ1, x0, hrc1, hst1, hk0, -, hσ1, -, -, hcu1, hss1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hss1, WP.spec_ok] at h; exact h
  rw [hkc] at hk0; cases hk0
  have hX1 := J1.xtop
  have hFl1 : FlagsRel Z.T (L.mem s1) σ1 := by rw [hσ1]; exact J.flagsRestart hFl htcb hkc hss1
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  have hcurY1 : σ1.curThread = ct.bv := by rw [hcu1, hcur]
  have hdec := DecOut.of_eq (setFlags_ok σ p.bv y0.bv y1.bv (rest.map UScalar.bv))
  unfold tcb.decode_set_flags
  simp only [h1, ↓reduceIte]
  rw [hct]; simp only [bind_ok]; rw [ha0]; simp only [bind_ok]; rw [ha1]; simp only [bind_ok]
  rw [hrc1]; simp only [bind_ok]
  rw [flags_eq]; simp only [bind_ok, lift, set_flags_eq]
  -- the flags, both sides
  obtain ⟨xp, hkp, hfp⟩ := hFl1 p hpT
  set f := L.mem s1 (tFlagsWA p)
  set f2 := (f &&& ~~~y0) ||| (y1 &&& fl4_abi.consts.tcb_flag.MASK) with hf2
  set nf : Fl4Spec.TcbFlags := xp.tcbFlags \ Fl4Spec.wordToTcbFlags y0.bv ∪ Fl4Spec.wordToTcbFlags y1.bv with hnf
  have hW2 : Fl4Spec.wordToTcbFlags f2.bv = nf := by
    rw [hnf, ← hfp, hf2, flags_mask_eq, UScalar.bv_or, UScalar.bv_and, UScalar.bv_and, UScalar.bv_not]
    exact flags_new _ _ _
  obtain ⟨V2, J2⟩ := J1.flagsWrJ hpT hkp f2 nf hW2
  set s2 := L.wr s1 (core.num.U64.wrapping_add p 3456#u64) f2
  have W2 : P1.WritesIn st s s2 (Mc.ProjW (L := L) H Cs s) := by
    have hfa : P1.Aligned (tFlagsWA p) := P1.field_aligned (J.ip.e.tcb p hpT) (by decide) (by decide)
    refine W1.projW_trans ((P1.writesIn_wr (s := s1) (v := f2) hfa).mono ?_)
    rintro b rfl
    exact Mc.obj_projW J.kern.heap (k := .tcb) (J.zH.1 p hpT) (by simp [P1.HKind.bits])
  set σ2 := Notif.updK σ1 p.bv (.tcb { xp with tcbFlags := nf })
  have hts : Fl4Spec.setFlags (Z := Unit) p.bv nf σ1 = ({((), σ2)}, False) := Notif.threadSet_eq _ hkp
  have hcur2 : σ2.curThread = ct.bv := hcurY1
  have hkc2 : ∃ y, σ2.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart := by
    by_cases e : ct.bv = p.bv
    · rw [e] at hkc1 ⊢
      have e2 := Fl4Spec.KernelObject.tcb.inj (Option.some.inj (hkp.symm.trans hkc1))
      exact ⟨{ xp with tcbFlags := nf }, by simp [σ2, Notif.updK], by rw [e2]⟩
    · exact ⟨{ xc with tcbState := .restart }, by simp [σ2, Notif.updK, Function.update_of_ne e, hkc1], rfl⟩
  have hfpu : ((f2 &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) != 0#u64) = true ↔
      Fl4Spec.TcbFlag.fpuDisabled ∈ nf := by
    rw [← hW2, w2f_mem, ← and1_ne]
    have key : ∀ x : U64, (x &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) = 0#u64 ↔ x.bv &&& 1 = 0 := by
      intro x; rw [← bv_eq_iff']
      show UScalar.bv (x &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) = UScalar.bv 0#u64 ↔ _
      rw [UScalar.bv_and]; unfold fl4_abi.consts.tcb_flag.FPU_DISABLED; rfl
    simp only [bne_iff_ne, ne_eq, key]
  -- the tail, from the spec's state after the FPU step
  have tail : ∀ (a1 : A) (σ3 : Fl4Spec.State Unit) (Z3 : XSets) (Ac3 : Set U64) (Lst3 : U64 → List U64)
      (D3 : Set U64),
      ((), σ3) ∈ (Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ nf) (Fl4Spec.fpuRelease (Z := Unit) p.bv)
        σ2).1 → JAtZ (L := L) arI AR Z3 H Cs Ac3 Lst3 D3 s2 a1 σ3 → [VxE Z3] →
      (∀ s' a' σ', JStab (L := L) arI AR Z3 H Cs s' a' σ' → JStab (L := L) arI AR Z H Cs s' a' σ') →
      Z3.th = Z.th → σ3.curThread = ct.bv →
      (∃ y, σ3.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart) →
      (if call = true then (do
        let buf ← msg.lookup_ipc_buffer st s2 true ct
        let (len, s3) ← msg.set_mr st s2 ct buf 0#u64 f2
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1))
      else (do
        let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a1))) ⦃ res =>
        TopPostRMX (L := L) (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk call don (Fl4Spec.NonDetE.liftME
          Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4SetFlags (Z := Unit)
            ((y0 :: y1 :: rest).map UScalar.bv) p.bv)) ct s res ⦄ := by
    intro a1 σ3 Z3 Ac3 Lst3 D3 h3 J3 _ hS3 hth3 hcur3 ⟨y3, hk3, hrs3⟩
    have hX3 := J3.xtop
    have hmem : (.ok [f2.bv], σ3) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeFl4TCB (.setFlags p.bv y0.bv y1.bv))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
      refine mem_liftE (x := ([f2.bv], σ3)) ?_
      show ([f2.bv], σ3) ∈ ((do
        let flags ← Fl4Spec.threadGet (Z := Unit) Fl4Spec.Tcb.tcbFlags p.bv
        let newFlags ← pure (flags \ Fl4Spec.wordToTcbFlags y0.bv ∪ Fl4Spec.wordToTcbFlags y1.bv)
        Fl4Spec.setFlags p.bv newFlags
        Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ newFlags) (Fl4Spec.fpuRelease p.bv)
        let w ← Fl4Spec.NonDet.select {w | Fl4Spec.wordToTcbFlags w = newFlags}
        return [w]) σ1).1
      rw [Notif.nd_bind_one (Notif.threadGet_eq _ hkp), Notif.nd_pure_bind', Notif.nd_bind_one hts]
      exact mem_bind_nd (x := ((), σ3)) (by convert h3) (mem_bind_nd (x := (f2.bv, σ3)) (y := ([f2.bv], σ3)) ⟨hW2, rfl⟩
        (Set.mem_singleton _))
    have hcurY : ct.bv = σ3.curThread := hcur3.symm
    have htcb3 : Z3.th ct = some .tcb := by rw [hth3]; exact htcb
    have hact3 : OutsideObjects Z3.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := J3.kern.act
    have hctT3 : ct ∈ Z3.T := J3.thT ct htcb3
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hJt : (do
          let s5 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1)) ⦃ res =>
            ∀ z ∈ (specTail false ct.bv [f2.bv] σ3).1, JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 z.2 ∧
              P1.WritesIn st s res.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
        refine WP.spec_bind (WP.spec_and (J3.runJ hctT3 hk3 hrs3) (stsProjW J3 hctT3 sched.TS_RUNNING)) ?_
        rintro s5 ⟨⟨Lst', D', J5⟩, W5⟩
        refine (WP.spec_ok _).2 fun z hz => ?_
        rw [specTail_restart hk3 hrs3 false f2.bv] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        rw [Notif.setThreadState_eq .running hk3] at hz
        rw [Set.mem_singleton_iff.1 hz]
        exact ⟨hS3 _ _ _ J5.stab, W2.projW_trans W5⟩
      refine WP.spec_mono (WP.spec_and (nodata_tail_xtop hX3 hcurY hk3 hrs3 hact3 [f2.bv]) hJt) ?_
      rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
      exact Or.inr ⟨hres, hne, _, hdec, σ1, hst1, [f2.bv], σ3, hmem, z, hz, hRT, hJ5 z hz⟩
    · simp only [↓reduceIte]
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
      rintro bf -
      have hI0 : Vs.RInv (L := L) Z3.th Z3.P Z3.L4 Z3.L3 Z3.L2 Z3.L1 Z3.N Z3.T Z3.C Z3.E Z3.R Z3.B Z3.c AR Z3.G s2 a1
          (MrS σ3 ct.bv y3 (Endp.ipcBufOf true y3) []) := by
        rw [MrS_nil hk3]; exact hX3.toRInv
      have hset : msg.set_mr st s2 ct bf 0#u64 f2 ⦃ r =>
          r = (1#u64, L.wr s2 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) f2) ⦄ := by
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ f2) ?_
        rintro s2' rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (WP.spec_and (setmr_reg_inv _ ct htcb3 hcurY y3 _ bf s2 a1 [] hI0 0#u64 rfl (by decide) f2)
        hset) ?_
      rintro ⟨len, s3⟩ ⟨⟨hlen, hI3, hk3', hc3'⟩, he3⟩
      simp only [Prod.mk.injEq] at hlen hI3 hk3' hc3' he3
      obtain ⟨rfl, rfl⟩ := he3
      refine WP.spec_mono (WP.spec_and (data_tail_xtop hX3 hcurY hk3 hrs3 hact3 hI3 hk3' hc3'
        (by simp [Fl4Spec.msgMaxLength]) (fun _ _ z hz => by simp [Endp.mrPairs] at hz) 1#u64
        (by cases Endp.ipcBufOf true y3 <;> simp [mrLen]) (by decide))
        (J3.replyWords1JSt hctT3 hk3 hrs3 f2)) ?_
      rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
      obtain ⟨hS5, W5⟩ := hJ5 z hz
      exact Or.inr ⟨hres, hne, _, hdec, σ1, hst1, [f2.bv], σ3, hmem, z, hz, hRT, hS3 _ _ _ hS5, W2.projW_trans W5⟩
  by_cases hF : ((f2 &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) != 0#u64) = true
  · simp only [hF, ↓reduceIte]
    refine WP.spec_bind (J2.fpuReleaseJ' hK hpT) ?_
    rintro a1 ⟨σ3, h3, hc3, hst3, V3, J3⟩
    obtain ⟨y2, hky2, hrs2⟩ := hkc2
    obtain ⟨y3, hky3, hrs3⟩ := hst3 _ y2 hky2
    refine tail a1 σ3 _ _ _ _ ?_ J3 (fun _ _ _ h => JStab.mv (JStab.mv h)) rfl (by rw [hc3]; exact hcur2) ⟨y3, hky3, by rw [hrs3, hrs2]⟩
    unfold Fl4Spec.NonDet.when; rw [if_pos (hfpu.1 hF)]; exact h3
  · simp only [Bool.not_eq_true] at hF
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    refine tail ar σ2 _ _ _ _ ?_ J2 (fun _ _ _ h => JStab.mv h) rfl hcur2 hkc2
    unfold Fl4Spec.NonDet.when
    rw [if_neg (fun h => by have := hfpu.2 h; rw [hF] at this; cases this)]
    exact Set.mem_singleton _

end

/-- (p3J gen 40) The Thread labels left after SetFlags. -/
def ThHard7 (l : U64) : Prop := ThHard6 l ∧ l ≠ fl4_abi.label.TCBSetFlags

/-- (p3J gen 40) The caps left after the SetFlags leaf, with the message label. -/
def IsRestCap15 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard7 l
  | _, _ => False

theorem restCap14_of15 {cp : capability.Cap} {l : U64} (h : IsRestCap15 cp l) : IsRestCap14 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap15_of {cp : capability.Cap} {l : U64} (h : IsRestCap14 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSetFlags) : IsRestCap15 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem flg_nonIns : TcbNonIns fl4_abi.label.TCBSetFlags := by
  unfold TcbNonIns fl4_abi.label.TCBSetFlags fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at SetFlags, any flags** (module
docstring). -/
theorem decThFlgSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hK : ARKeep arI AR)
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
    (hl : info.label = fl4_abi.label.TCBSetFlags) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetFlags
  have hl5 : fl4_abi.label.TCBSetFlags.val ≠ 5 ∧
      fl4_abi.label.TCBSetFlags.val ≠ 8 ∧
      fl4_abi.label.TCBSetFlags.val ≠ 9 ∧ fl4_abi.label.TCBSetFlags.val ≠ 10 ∧
      fl4_abi.label.TCBSetFlags.val ≠ 11 := by simp [fl4_abi.label.TCBSetFlags]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD flg_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  right
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_set_flagsJSt s' a' σb J hnib J.flagsRel p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct
      argsU hLen hArgs (J.stallT p hpT) hK call _ e bl don ci sl exs buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap14` from the SetFlags leaf** (module docstring). -/
theorem midDecRest14_of_flg (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hK : ARKeep arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetFlags
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFlgSt hA hMT hKD hK J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap15_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap14` from the SetFlags leaf** (module docstring). -/
theorem invDecRest14_of_flg (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hK : ARKeep arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetFlags
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFlgSt hA hMT hKD hK J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap15_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap14` gives it at `KW ∧ IsRestCap15` (antitone). -/
theorem midDecStWL_of_14 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap14_of15 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap14` gives it at `KW ∧ IsRestCap15` (antitone). -/
theorem invDecStWL_of_14 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap14 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap14_of15 hW.2⟩

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

/-- (p3J gen 40) **`DispStabFootLzh` [J]**: `DispStabFootLzg` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetMCPriority /
Bind- and UnbindNotification / Set- and UnsetBreakpoint / ConfigureSingleStepping / SetTLSBase / SetFlags, or
SetEPTRoot
(module docstring). -/
structure DispStabFootLzh (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzg.invDecRest` at `KW ∧ IsRestCap15`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzg.midDecRest` at `KW ∧ IsRestCap15`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzg.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzg.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzh → DispStabFootLzg`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzg_of_Lzh (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzh (L := L) arI AR MR s a σ) :
    DispStabFootLzg (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest14_of_flg hA hnd (MachPlatF.toT hM hIp) hKD hARI.toARKeep hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest14_of_flg hA hnd (MachPlatF.toT hM hIp) hKD hARI.toARKeep hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzg → DispStabFootLzh`** (the honesty claim: `DispStabFootLzh` is implied). -/
theorem dispStabFootLzh_of_Lzg {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzg (L := L) arI AR MR s a σ) : DispStabFootLzh (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_14 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_14 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzh` only** (`hLzh` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzh [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzh : DispStabFootLzh (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzg hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzg_of_Lzh hARI hA hnd hM hIp hKD hLzh)

end

end Fl4Proofs.P3.Mc
