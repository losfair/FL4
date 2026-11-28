/-
P3 (p3J gen 41): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at WriteRegisters (3),
for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2, 4, 5, 8–11, 17, 22, or SetEPTRoot}.

* **`JAtZ.rcvRegProjW`**: a register word of a thread of `Z.T` (EpXfer's `RcvReg`) is a `ProjW` word.
* **`JAtZ.writeRegsJW`**: XTopJointWriteRegs' `JAtZ.writeRegsJ` (proof text unchanged but the posts; at 4M
  heartbeats, its source has 32M) with the footprint `WritesIn s1 · (ProjW H Cs s1)`: the
  register loops, the restart PC and `post_modify_registers` write the target's register words (`RcvReg`, already
  carried by `wrJ_loop0` / `wrJ_loop1` / `wr_regW` for `IRel.iframe_of`), the optional restart by P3JThRes's
  `JAtZ.restartProjW`; the closing `reschedule_required` is not reached (the target is not the caller).
* **`tcb_write_regsJSt`**: XTopJointTcb's `tcb_write_regsJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts; the caller's restart by `stsProjW`).
* **`decThWrSt`** (any flags): the dispatch leaf. The non-stable chain's WriteRegisters inputs are derived at the
  dispatch state exactly as StallNarrowTcb's `decode_invocation_threadJ_stepMT` derives them: the caller's buffer
  mapped (`hbm`, from `lookup_buf_full` and `BufCover`), the arguments after the caller's restart (`hWR`, from
  `JAtZ.argsRestart`, the message length `≤ 120` as P3JLook reads it off `msg_info_spec`); `MIN_BUDGET` by
  `TimeAgree.mb`. No new premise.
* `ThHard13 l`: `ThHard12 l ∧ l ≠ TCBWriteRegisters`. `IsRestCap21`. `restCap20_of21`, `restCap21_of`.
  **`midDecRest20_of_wr`** / **`invDecRest20_of_wr`**, `midDecStWL_of_20` / `invDecStWL_of_20`.
* **`DispStabFootLzn` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap21`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzm_of_Lzn`** (under the tops' platform facts, incl. `TimeAgree`), **`dispStabFootLzn_of_Lzm`**;
  top **`kernel_entry_runMcWKR_sysLzn`** (globals verbatim as `_sysLzm`).

Premise honesty: `DispStabFootLzn`'s decode fields are `DispStabFootLzm`'s at the smaller antecedent
(`IsRestCap21 → IsRestCap20`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzn` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThTm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 41) **A register word of a thread of `Z.T` is a `ProjW` word** (module docstring). -/
theorem JAtZ.rcvRegProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {b : U64} (hb : RcvReg t b) : Mc.ProjW (L := L) H Cs s b := by
  obtain ⟨r, hb⟩ := hb
  have hr := regIdx_lt r
  have hv := regA_val (J.ip.e.tcb t ht) hr
  exact Or.inl ⟨t, .tcb, J.zH.1 t ht, by rw [hb, hv]; omega, by rw [hb, hv]; simp only [P1.HKind.bits]; omega⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`write_registers` at `J`, with its `ProjW` footprint** (XTopJointWriteRegs' `JAtZ.writeRegsJ`;
module docstring). -/
theorem JAtZ.writeRegsJW (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s1 : S} {σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a σ1)
    {p ct buf : U64} (hpT : p ∈ Z.T) (hpc : p ≠ ct) (hcur : σ1.curThread = ct.bv) (hctT : ct ∈ Z.T)
    {x0 : U64} (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s1) x0 = ok (.Thread p))
    (hns : ∀ u, σ1.schedulerAction ≠ .switchThread u)
    {sp : Fl4Spec.Word} (hbm : buf ≠ 0#u64 → BufMap Z.B buf sp)
    (resume : Bool) (n : U64) {V : List Fl4Spec.Word} (hVn : V.length = n.val)
    (hargs : ∀ (j : Nat) (i2 : U64), i2.val = j + 2 → j < n.val →
      ∃ w, msg.syscall_arg st s1 ct buf i2 = ok w ∧ w.bv = V[j]!) :
    tcb.write_registers st arI s1 a p resume n buf ⦃ r => r.2 = a ∧
      P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ∧ ∃ σ',
      specWr p.bv resume V σ1 = ({((), σ')}, False) ∧
      ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := hI.2.2.1
  have hta := hP0.e.tcb p hpT
  obtain ⟨x, hk, -⟩ := hI.1.tcb p hpT
  unfold tcb.write_registers
  refine WP.spec_bind (cur_thread_bv hS) ?_
  rintro ct' hct'
  obtain rfl : ct = ct' := (P1.eq_of_bv (hct'.trans hcur)).symm
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := tcb.N_FRAME) (y := tcb.N_GP) (by rw [hf, hg]; scalar_tac))
  rw [hie, bind_ok]
  have hi20 : i.val = 20 := by have := hiv; simp only [hf, hg] at this ⊢; omega
  obtain ⟨n', hn'e, hn'v⟩ : ∃ n' : U64, (if n > i then ok i else ok n : Result U64) = ok n' ∧
      n'.val = min n.val 20 := by
    by_cases h : n > i
    · exact ⟨i, if_pos h, by have := (P1.gt_iff_val).1 h; omega⟩
    · exact ⟨n, if_neg h, by have := (P1.gt_iff_val).not.1 h; omega⟩
  rw [hn'e, bind_ok]
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ1.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hEH := hH.epHyps hP0
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hI0 := rgInv_init (L := L) (T := Z.T) (E := Z.E) (R := Z.R) (B := Z.B) hI.1.toE hSR.1 hk
  have hn20 : n'.val ≤ 20 := by omega
  have hVl : n'.val ≤ V.length := by omega
  have hRd : WrRead (L := L) Z.T Z.E Z.R Z.B
      (SRS st Z.T (SRT st Z.th σ1.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s1 σ1 p x ct buf n' V :=
    wrRead_of hP0.e hI.1.toE hpT hk hctT hbm hn20 fun j i2 hi2 hj => hargs j i2 hi2 (by omega)
  refine WP.spec_bind (wrJ_loop0 hEH hP0.e J hpT hk hn20 hVl hRd hI0) ?_
  rintro s2 ⟨hI2, ⟨V2, J2⟩, hw2⟩
  refine WP.spec_bind (wrJ_loop1 (Z := Z.mv Z.G V2) hEH hP0.e hpT hn20 hVl hRd hI2 J2 hw2) ?_
  rintro s3 ⟨-, ⟨V3, J3⟩, hw3⟩
  rw [sanRegs_take x wrRegs V n'.val (by rw [wrRegs_length]; omega)] at J3
  set x2 := sanRegs x wrRegs V with hx2
  have hX3 := J3.xtop.irelK J3.ks J3.buf
  have hk2 : (updK σ1 p.bv (.tcb x2)).kheap p.bv = some (.tcb x2) := by simp [updK]
  obtain ⟨x2', hk2', hTR2⟩ := hX3.1.tcb p hpT
  rw [hk2] at hk2'; cases hk2'
  -- the restart PC
  have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
  have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s3 p _) ?_
  rintro pc hpc'
  have hpcv : pc.bv = x2.tcbArch.tcbContext.userRegs .faultIP := by rw [hpc', hF]; exact hTR2.regs .faultIP
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s3 p _ pc) ?_
  rintro s4 rfl
  rw [hNx]
  obtain ⟨V4, J4⟩ := J3.regWrJ hpT hk2 .nextIP pc (reg_wr_irelN J3.ip hX3 hpT hk2 .nextIP pc)
  rw [hpcv] at J4
  set x3 := setReg x2 .nextIP (x2.tcbArch.tcbContext.userRegs .faultIP) with hx3
  have e3 : updK (updK σ1 p.bv (.tcb x2)) p.bv (.tcb x3) = updK σ1 p.bv (.tcb x3) := by
    simp only [updK, Function.update_idem]
  rw [e3] at J4
  have hk3 : (updK σ1 p.bv (.tcb x3)).kheap p.bv = some (.tcb x3) := by simp [updK]
  have hX4 := J4.xtop.irelK J4.ks J4.buf
  -- `post_modify_registers`: the target is not the caller
  have hpm : tcb.post_modify_registers st (L.wr s3 (regA p (regIdx .nextIP)) pc) p ⦃ s5 =>
      s5 = L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc) (regA p (regIdx .errorRegister)) 0#u64 ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX4.2.2.1) ?_
    rintro ct3 hc3
    obtain rfl : ct = ct3 := (P1.eq_of_bv (hc3.trans hcur)).symm
    rw [tcb_ne_eq, bind_ok]
    simp only [ne_eq, hpc, not_false_eq_true, decide_true, ↓reduceIte]
    have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
    rw [hE]; exact Endp.obj.Tcb.set_reg.spec _ p _ 0#u64
  refine WP.spec_bind hpm ?_
  rintro s5 rfl
  obtain ⟨V5, J5⟩ := J4.regWrJ hpT hk3 .errorRegister 0#u64 (reg_wr_irelN J4.ip hX4 hpT hk3 .errorRegister 0#u64)
  set x4 := setReg x3 .errorRegister (0#u64).bv with hx4
  have e4 : updK (updK σ1 p.bv (.tcb x3)) p.bv (.tcb x4) = updK σ1 p.bv (.tcb x4) := by
    simp only [updK, Function.update_idem]
  rw [e4] at J5
  have hpm4 : Fl4Spec.archPostModifyRegisters (Z := Unit) ct.bv p.bv (updK σ1 p.bv (.tcb x3)) =
      ({((), updK σ1 p.bv (.tcb x4))}, False) := by
    unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
    rw [if_pos (fun e => hpc (P1.eq_of_bv e)), asUser_setRegister_eq _ _ hk3, ← e4]
    rfl
  -- the restart's premises at the state after the register words
  have hX5 := J5.xtop.irelK J5.ks J5.buf
  have hw5 := wr_regW hta .errorRegister 0#u64 (wr_regW hta .nextIP pc hw3)
  have hIF := IRel.iframe_of hI hw5 fun _ ⟨r, hb⟩ => by
    have := regIdx_lt r
    have hr := regA_val hta (regIdx_lt r)
    exact Or.inr (Or.inr (Or.inl ⟨p, hpT, by omega, by omega⟩))
  have hcap5 : capAt (L.mem (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc) (regA p (regIdx .errorRegister)) 0#u64))
      x0 = ok (.Thread p) := by
    rw [capAt_capV, hIF.1.capV hxS, ← capAt_capV]; exact hcap
  -- the restart
  have hrs : (if resume then sched.restart st arI (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc)
      (regA p (regIdx .errorRegister)) 0#u64) a p else ok (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc)
      (regA p (regIdx .errorRegister)) 0#u64, a)) ⦃ r => r.2 = a ∧
      P1.WritesIn st (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc) (regA p (regIdx .errorRegister)) 0#u64) r.1
        (Mc.ProjW (L := L) H Cs (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc) (regA p (regIdx .errorRegister)) 0#u64)) ∧
      ∃ σ6,
      Fl4Spec.NonDet.when resume (Fl4Spec.restart (Z := Unit) p.bv) (updK σ1 p.bv (.tcb x4)) =
        ({((), σ6)}, False) ∧ σ6.curThread = ct.bv ∧
      ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ6 ⦄ := by
    cases resume
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, P1.WritesIn.refl _ _, _, rfl, hcur, V5, Ac, Lst, D, J5⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (WP.spec_and (WP.spec_and (J5.restartTcbJ (Z := Z.mv Z.G V5) hAT hSd hNt hRv hRp hmb hpT
        hxS hcap5 hns) (J5.restartProjW hAT hpT))
        (restart_tcb_irelS (ar := arI) hP0 (removeTcbHypP_ok hP0) _ a _ hX5 hpT J5.sv J5.obj J5.inv
          (fun x' hk' hfr => removeTcbOK_fault hP0 hX5 hpT hk' hfr J5.removeTcbOK)
          (Sched.restartSpecOK_of J5.inv J5.sv.scSpor) hmb)) ?_
      rintro r ⟨⟨⟨h1, σ6, h2, V', Ac', Lst', D', J6⟩, hWr⟩, -, σ6', h2', -, hc6, -⟩
      have e6 : σ6' = σ6 := by
        rw [h2] at h2'; exact ((Prod.mk.inj (Set.singleton_injective (congrArg Prod.fst h2'))).2).symm
      subst e6
      exact ⟨h1, hWr, σ6', by simpa [Fl4Spec.NonDet.when] using h2, hc6.trans hcur, V', Ac', Lst', D', J6⟩
  refine WP.spec_bind hrs ?_
  rintro ⟨s6, a1⟩ ⟨rfl, hW6', σ6, hrs6, hct6, V6, Ac6, Lst6, D6, J6⟩
  have hW6 : P1.WritesIn st s1 s6 (Mc.ProjW (L := L) H Cs s1) :=
    (hw5.mono fun _ hb => J.rcvRegProjW hpT hb).projW_trans hW6'
  refine WP.spec_bind (cur_thread_bv (J6.xtop.irelK J6.ks J6.buf).2.2.1) ?_
  rintro ct5 hc5
  obtain rfl : ct = ct5 := (P1.eq_of_bv (hc5.trans hct6)).symm
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok, hpc, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  refine ⟨trivial, hW6, σ6, ?_, V6, Ac6, Lst6, D6, J6⟩
  unfold specWr
  rw [nd_gets_bind, hcur, nd_bind_one (show Fl4Spec.archGetSanitiseRegisterInfo (Z := Unit) p.bv σ1 =
    ({(false, σ1)}, False) from rfl), nd_bind_one (wr_regs_eq hk V), nd_bind_one hpm4, nd_bind_one hrs6]
  unfold Fl4Spec.NonDet.when
  rw [if_neg (fun e => hpc (P1.eq_of_bv e))]
  rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **WriteRegisters at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_write_regsJ`;
module docstring). -/
theorem tcb_write_regsJSt (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ)
    (p : U64) (hpT : p ∈ Z.T) (x0 : U64) (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s) x0 = ok (.Thread p))
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbWriteRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hbuf : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp)
    (hargs1 : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBWriteRegisters p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hctT : ct ∈ Z.T := J.thT ct (hX.curTcb hcur).1
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [whenE_pos (by rw [hun, List.length_map, hrl]; have h' : i.val < y1.val := hw; omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hw, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
  have hy1 : y1.val ≤ rest.length := by have h' : ¬ i.val < y1.val := hw; omega
  have hwh : (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
      (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) : Fl4Spec.SEMonad Unit Unit).run σ =
      ({(.ok (), σ)}, False) := by
    rw [whenE_neg (by rw [hun, List.length_map]; omega)]; rfl
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩
    apply run_liftME_err
    rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
      s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
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
  -- the caller's restart
  obtain ⟨s1, σ1, x, hrc1, hst, hk, -, -, hns, -, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  obtain ⟨-, x', hk', hrun⟩ := J.curRunnable hni hct
  rw [hk] at hk'; cases hk'
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := XTopAt.restart J.xtop hcur hk hrun
    rw [hs1, WP.spec_ok] at h; exact h.2.1
  have hcap1 : capAt (L.mem s1) x0 = ok (.Thread p) := by
    rw [capAt_capV, hSS.capV hxS, ← capAt_capV]; exact hcap
  have hcur1 : σ1.curThread = ct.bv := hct1.trans hcur
  rw [hrc1]; simp only [bind_ok, lift]
  -- the arguments after the restart
  set V := (((y0 :: y1 :: rest).drop 2).map UScalar.bv).take y1.val with hV
  have hVn : V.length = y1.val := by simp [hV]; omega
  obtain ⟨sp, hbm⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
    by_cases hb : buf = 0#u64
    · exact ⟨0, fun h => absurd hb h⟩
    · obtain ⟨sp, h⟩ := hbuf hb; exact ⟨sp, fun _ => h⟩
  have hargsV : ∀ (j : Nat) (i2 : U64), i2.val = j + 2 → j < y1.val →
      ∃ w, msg.syscall_arg st s1 ct buf i2 = ok w ∧ w.bv = V[j]! := by
    intro j i2 hi2 hj
    have hjl : j + 2 < (y0 :: y1 :: rest).length := by simp; omega
    refine ⟨(y0 :: y1 :: rest)[j + 2], hargs1 s1 hs1 i2 _ (by rw [hi2]; exact List.getElem?_eq_getElem hjl), ?_⟩
    have hjV : j < V.length := by omega
    rw [getElem!_pos V j hjV]
    simp only [hV, List.getElem_take, List.getElem_map, List.getElem_drop]
    congr 2; omega
  refine WP.spec_bind (J1.writeRegsJW hAT (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
    (jCancel_reply arI) (hmb ar) hpT hpc hcur1 hctT hxS hcap1 (fun u h => hns u h) hbm
    ((y0 &&& 1#u64) != 0#u64) y1 hVn hargsV) ?_
  rintro ⟨s2, a2⟩ ⟨-, W2, σ', hsp, V', Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.writeRegisters p.bv
        (Fl4Spec.testBit y0.bv 0) V Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
    rw [invokeTcb_wr, ← and1_ne0]
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac', Lst', D', J2⟩, W1.projW_trans W2⟩⟩

end

/-- (p3J gen 41) The Thread labels left after WriteRegisters. -/
def ThHard13 (l : U64) : Prop := ThHard12 l ∧ l ≠ fl4_abi.label.TCBWriteRegisters

/-- (p3J gen 41) The caps left after the WriteRegisters leaf, with the message label. -/
def IsRestCap21 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard13 l
  | _, _ => False

theorem restCap20_of21 {cp : capability.Cap} {l : U64} (h : IsRestCap21 cp l) : IsRestCap20 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap21_of {cp : capability.Cap} {l : U64} (h : IsRestCap20 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBWriteRegisters) : IsRestCap21 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem wr_nonIns : TcbNonIns fl4_abi.label.TCBWriteRegisters := by
  unfold TcbNonIns fl4_abi.label.TCBWriteRegisters fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The Thread cap's decode at a dispatch state at WriteRegisters, any flags** (module docstring). -/
theorem decThWrSt (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
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
    (hl : info.label = fl4_abi.label.TCBWriteRegisters) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  -- the caller's buffer mapped and the arguments after its restart (as StallNarrowTcb)
  have hcur : σb.curThread = ct.bv := (J.curEq hct).1
  have hctH : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ (Z.mv Z.G V').T := J.thT ct hctH
  have hl120 : argsU.length ≤ 120 := by
    have hm := Endp.msg_info_spec (L := L) s' ct
    rw [hinfo, WP.spec_ok] at hm
    have h120 := hm.2.2.2
    have h4 : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
    rw [← hLen]; unfold msgLen
    split_ifs <;> omega
  have hbm : buf ≠ 0#u64 → ∃ sp, BufMap (Z.mv Z.G V').B buf sp := by
    intro hb0
    obtain ⟨x, hk, hwx⟩ := J.buf ct hctT
    have hL := lookup_buf_full s' σb J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hctH hk (J.xferH.1) false
    rw [hbuf, WP.spec_ok] at hL
    cases hq : Endp.ipcBufOf false x with
    | none => exact absurd (hL.1.2 hq) hb0
    | some q => exact ⟨q, J.xferH.2.1 ct hctT x false q hk hq buf (hL.2 hwx q hq)⟩
  have hWR : ∀ s1, sched.set_thread_state st s' ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x := by
    intro s1 h1 i x hx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨sp, hsp⟩ : ∃ sp, buf ≠ 0#u64 → BufMap (Z.mv Z.G V').B buf sp := by
      by_cases hb : buf = 0#u64
      · exact ⟨0, fun h => absurd hb h⟩
      · obtain ⟨sp, h⟩ := hbm hb; exact ⟨sp, fun _ => h⟩
    rw [J.argsRestart (J.xferH.2.2) hctT hctH hsp (by omega) h1]
    exact hArgs i x hx
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBWriteRegisters
  have hl5 : fl4_abi.label.TCBWriteRegisters.val ≠ 5 ∧ fl4_abi.label.TCBWriteRegisters.val ≠ 8 ∧
      fl4_abi.label.TCBWriteRegisters.val ≠ 9 ∧ fl4_abi.label.TCBWriteRegisters.val ≠ 10 ∧
      fl4_abi.label.TCBWriteRegisters.val ≠ 11 := by simp [fl4_abi.label.TCBWriteRegisters]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine XCapP.mrGT (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD wr_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_write_regsJSt hA hT.mb s' a' σb J hnib p hpT (cslotAddr sl) hAs.isSlot hc sl'
      (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen hArgs hbm hWR (J.stallT p hpT) call _ e bl don ci sl
      exs buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`MidDecStWL` at `KW ∧ IsRestCap20` from the WriteRegisters leaf** (module docstring). -/
theorem midDecRest20_of_wr (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap20 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBWriteRegisters
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThWrSt hA hT hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap21_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`InvDecStWL` at `KW ∧ IsRestCap20` from the WriteRegisters leaf** (module docstring). -/
theorem invDecRest20_of_wr (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap20 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBWriteRegisters
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThWrSt hA hT hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap21_of hW.2 hS⟩

/-- (p3J gen 41) `MidDecStWL` at `KW ∧ IsRestCap20` gives it at `KW ∧ IsRestCap21` (antitone). -/
theorem midDecStWL_of_20 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap20 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap20_of21 hW.2⟩

/-- (p3J gen 41) `InvDecStWL` at `KW ∧ IsRestCap20` gives it at `KW ∧ IsRestCap21` (antitone). -/
theorem invDecStWL_of_20 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap20 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap20_of21 hW.2⟩

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

/-- (p3J gen 41) **`DispStabFootLzn` [J]**: `DispStabFootLzm` with `invDecRest` / `midDecRest` restricted to
`IsRestCap21` (`IsRestCap20` minus the Thread caps at WriteRegisters; module docstring). -/
structure DispStabFootLzn (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzm.invDecRest` at `KW ∧ IsRestCap21`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzm.midDecRest` at `KW ∧ IsRestCap21`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzm.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzm.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 41) **`DispStabFootLzn → DispStabFootLzm`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzm_of_Lzn (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzn (L := L) arI AR MR s a σ) :
    DispStabFootLzm (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest20_of_wr hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest20_of_wr hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 41) **`DispStabFootLzm → DispStabFootLzn`** (the honesty claim: `DispStabFootLzn` is implied). -/
theorem dispStabFootLzn_of_Lzm {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzm (L := L) arI AR MR s a σ) : DispStabFootLzn (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_20 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_20 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzn` only** (`hLzn` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzn [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzn : DispStabFootLzn (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzm hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzm_of_Lzn hA hT hnd hM hIp hKD hLzn)

end

end Fl4Proofs.P3.Mc
