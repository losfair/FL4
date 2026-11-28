/-
P3 (p3J gen 41): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at CopyRegisters (4),
for both classes**; the rest set {CNode at Revoke / Delete, Thread at 2, 5, 8–11, 17, 22, or SetEPTRoot}.

* XTopJointCopyRegs' pieces with the footprint threaded (proof text unchanged but the posts; all at 4M
  heartbeats, the sources have 8M / 32M): **`crJ_loopW`** (`crJ_loop` with the target's register words `RcvReg` carried, `wr_regW`), **`JAtZ.crTailJW`**
  (`crTailJ`: `post_modify_registers` by P3JThSs's `JAtZ.regProjW`, the reschedule by P3JThTls's
  `JAtZ.reschedProjW`), **`JAtZ.copyRegsJW`** (`copyRegsJ`: the source's `suspend` by P3JThSus's
  `JAtZ.suspendProjW`, the target's `restart` by P3JThRes's `JAtZ.restartProjW`, the loops by `crJ_loopW` and
  P3JThWr's `JAtZ.rcvRegProjW`, the restart PC by `JAtZ.regProjW`).
* **`tcb_copy_regsJTSt`**: StallNarrowTcb's `tcb_copy_regsJT` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs
  s)` (the caller's restart by `stsProjW`).
* **`JAtZ.thrNotIdle`**: at a state with `SpecGlob`, no thread cap in a slot of the typed heap names the idle thread
  (`SpecGlob.idle`, l4v `valid_global_refs`, as XTopJointDelR's `jFinAt_thread`). This discharges the non-stable
  chain's `hidS` (StallNarrowTcb) at the dispatch state (`SpecGlob σb` by P3JCapDom's `dispEnteredSg`): no premise.
* **`decThCpSt`** (any flags): the dispatch leaf (`XcRel` by `ExtraOK.xc`; `MIN_BUDGET` by `TimeAgree.mb`).
* `ThHard14 l`: `ThHard13 l ∧ l ≠ TCBCopyRegisters`. `IsRestCap22`. `restCap21_of22`, `restCap22_of`.
  **`midDecRest21_of_cp`** / **`invDecRest21_of_cp`**, `midDecStWL_of_21` / `invDecStWL_of_21`.
* **`DispStabFootLzo` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap22`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzn_of_Lzo`** (under the tops' platform facts, incl. `TimeAgree`), **`dispStabFootLzo_of_Lzn`**;
  top **`kernel_entry_runMcWKR_sysLzo`** (globals verbatim as `_sysLzn`).

Premise honesty: `DispStabFootLzo`'s decode fields are `DispStabFootLzn`'s at the smaller antecedent
(`IsRestCap22 → IsRestCap21`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzo` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}

/-- (p3J gen 41) **No thread cap of the typed heap names the idle thread** (`SpecGlob.idle`; module docstring). -/
theorem JAtZ.thrNotIdle (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hsg : SpecGlob σ) :
    ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s := by
  intro sl' q hA hcv e
  obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hA
  rw [capAt_capV, hcv] at hc0; cases eq_of_ok_eq hc0
  rw [hca0.abs] at hg0
  have ha0 := (getCap_set_iff σ sl'.1 sl'.2 _).1 (congrArg Prod.fst hg0)
  apply hsg.idle sl'.1 sl'.2 _ ha0 (by simp [IsPageCap, absCap])
  rw [J.idleThread_bv, ← e]; simp [absCap, Fl4Spec.objRefs]

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **A register-copy loop of `copy_registers` at `J`, with the target's register words**
(XTopJointCopyRegs' `crJ_loop`; module docstring). -/
theorem crJ_loopW {a : A} {k : Usize} (arr : Aeneas.Std.Array U64 k) (Nl : U64)
    (Lr : List Fl4Spec.Register) (harr : arr.val = Lr.map regIdx) (hN : Nl.val = Lr.length) (hLr : Lr.length ≤ 18)
    {src dest : U64} (hs : src ∈ Z.T) (hd : dest ∈ Z.T)
    (body : S → U64 → Result (ControlFlow (S × U64) S))
    (hbody : ∀ s i, body s i = if i < Nl then (do
        let i1 ← lift (UScalar.cast .Usize i)
        let r ← Aeneas.Std.Array.index_usize arr i1
        let v ← obj.Tcb.reg st src s r
        let i2 ← regs.sanitise r v
        let s1 ← obj.Tcb.set_reg st dest s r i2
        let i3 ← i + 1#u64
        ok (ControlFlow.cont (s1, i3)))
      else ok (ControlFlow.done s))
    {s0 : S} {σ0 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a σ0) :
    loop (fun (x : S × U64) => body x.1 x.2) (s0, 0#u64) ⦃ s' => P1.WritesIn st s0 s' (RcvReg dest) ∧ ∃ σ',
      Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Lr σ0 = ({((), σ')}, False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  apply loop.spec_decr_nat (measure := fun x => Lr.length - x.2.val)
    (inv := fun x => x.2.val ≤ Lr.length ∧ P1.WritesIn st s0 x.1 (RcvReg dest) ∧ ∃ σ', Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) (Lr.take x.2.val) σ0 =
      ({((), σ')}, False) ∧ ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D x.1 a σ')
  · rintro ⟨s', i⟩ ⟨hi, hw', σ', hm, V', J'⟩
    simp only at hi hw' hm J' ⊢
    have hX' := J'.xtop.irelK J'.ks J'.buf
    rw [hbody]
    by_cases h1 : i < Nl
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = Lr.length := by have := (P1.gt_iff_val).not.1 h1; omega
      rw [this, List.take_length] at hm
      exact ⟨hw', σ', hm, V', J'⟩
    rw [if_pos h1]
    have hiL : i.val < Lr.length := by have := (P1.gt_iff_val).1 h1; omega
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by
      rw [cast_to_us' i (by omega)]; simp [harr]; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx Lr[i.val] := by
      rw [hrr, List.getElem_of_eq harr, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega)]
    subst hrv
    obtain ⟨xs, hks, hTs⟩ := hX'.1.tcb src hs
    obtain ⟨xd, hkd, -⟩ := hX'.1.tcb dest hd
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    obtain ⟨w, hw, hwv⟩ := sanitise_eq Lr[i.val] (L.mem s' (regA src (regIdx Lr[i.val])))
    rw [hw, bind_ok]
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' dest _ w) ?_
    rintro s2 rfl
    obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h3e, bind_ok, WP.spec_ok]
    have hi3 : i3.val = i.val + 1 := by simpa using h3v
    obtain ⟨V2, J2⟩ := J'.regWrJ hd hkd Lr[i.val] w (reg_any_wr_irel J'.ip hX' hd hkd Lr[i.val] w)
    refine ⟨⟨by show i3.val ≤ Lr.length; omega, wr_regW (J'.ip.e.tcb dest hd) Lr[i.val] w hw', _, ?_, V2, J2⟩,
      by show Lr.length - i3.val < Lr.length - i.val; omega⟩
    rw [hi3, List.take_succ, List.getElem?_eq_getElem hiL]
    simp only [Option.toList_some]
    rw [mapMx_snoc, nd_bind_one hm]
    unfold crb
    simp only [nd_assoc_f]
    rw [nd_bind_one (asUser_getRegister_eq hks _), ← hTs.regs, ← hwv, nd_bind_one (asUser_setRegister_eq _ _ hkd)]
    rfl
  · exact ⟨by simp, P1.WritesIn.refl _ _, σ0, by simp; rfl, Z.vs, by simpa using J⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The tail of `copy_registers` at `J`, with its `ProjW` footprint** (XTopJointCopyRegs'
`JAtZ.crTailJ`; module docstring). -/
theorem JAtZ.crTailJW {a : A} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {dest : U64} (hd : dest ∈ Z.T) :
    (do
      let s6 ← tcb.post_modify_registers st s dest
      let t ← sched.cur_thread st s6
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
      if b then do
        let s7 ← sched.reschedule_required st s6
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)) ⦃ r =>
      r.1 = .Ok () ∧ r.2.2 = a ∧ P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ∧ ∃ σ', (do
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ = ({((), σ')}, False) ∧
        JAtV (L := L) arI AR Z H Cs r.2.1 a σ' ⦄ := by
  have hX := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, -⟩ := hX.1.tcb dest hd
  have hpm : tcb.post_modify_registers st s dest ⦃ s4 => P1.WritesIn st s s4 (Mc.ProjW (L := L) H Cs s) ∧ ∃ ct : U64, σ.curThread = ct.bv ∧ ∃ σ4,
      Fl4Spec.archPostModifyRegisters (Z := Unit) ct.bv dest.bv σ = ({((), σ4)}, False) ∧
      σ4.curThread = ct.bv ∧ ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s4 a σ4 ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX.2.2.1) ?_
    rintro ct hct
    rw [tcb_ne_eq, bind_ok]
    by_cases hpc' : dest = ct
    · subst hpc'
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨P1.WritesIn.refl _ _, dest, hct.symm, σ, ?_, hct.symm, Z.vs, by simpa using J⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_neg (by simp)]; rfl
    · simp only [ne_eq, hpc', not_false_eq_true, decide_true, ↓reduceIte]
      have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ dest _ 0#u64) ?_
      rintro s4 rfl
      rw [hE]
      refine ⟨J.regProjW hd .errorRegister s 0#u64, ct, hct.symm, _, ?_, by simp [Notif.updK, hct],
        J.regWrJ hd hk .errorRegister 0#u64 (reg_any_wr_irel J.ip hX hd hk .errorRegister 0#u64)⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_pos (fun e => hpc' (P1.eq_of_bv e)), asUser_setRegister_eq _ _ hk]
      rfl
  refine WP.spec_bind hpm ?_
  rintro s4 ⟨hW4, ct, hct, σ4, hpm4, hct4, V4, J4⟩
  refine WP.spec_bind (cur_thread_bv (J4.xtop.irelK J4.ks J4.buf).2.2.1) ?_
  rintro ct5 hc5
  obtain rfl : ct = ct5 := (P1.eq_of_bv (hc5.trans hct4)).symm
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  have hfin : ∀ σ6, Fl4Spec.NonDet.when (dest.bv = ct.bv) (Fl4Spec.rescheduleRequired (Z := Unit)) σ4 =
      ({((), σ6)}, False) → (do
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ = ({((), σ6)}, False) := by
    intro σ6 h6
    rw [nd_gets_bind, hct, nd_bind_one hpm4, h6]
  by_cases hpc' : dest = ct
  · subst hpc'
    simp only [decide_true, ↓reduceIte]
    obtain ⟨s6, hrun, σ6, h6, Ac6, Lst6, D6, J6⟩ := J4.reschedJ
    have hW6 := J4.reschedProjW
    rw [hrun, WP.spec_ok] at hW6
    rw [hrun, bind_ok, WP.spec_ok]
    exact ⟨rfl, rfl, hW4.projW_trans hW6, σ6, hfin σ6 (by simpa [Fl4Spec.NonDet.when] using h6), V4, Ac6, Lst6, D6, J6⟩
  · simp only [hpc', decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, trivial, hW4, σ4, hfin σ4 (by
      unfold Fl4Spec.NonDet.when; rw [if_neg (fun e => hpc' (P1.eq_of_bv e))]; rfl), V4, Ac, Lst, D, J4⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`copy_registers` at `J`, with its `ProjW` footprint** (XTopJointCopyRegs' `JAtZ.copyRegsJ`;
module docstring). -/
theorem JAtZ.copyRegsJW (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    {a : A}
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hEn : Entered σ)
    {src dest : U64} (hsT : src ∈ Z.T) (hdT : dest ∈ Z.T) (hsI : src.bv ≠ σ.idleThread) (hdD : dest ∉ D)
    (flags : U64) :
    tcb.copy_registers st arI s a dest src flags ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ∧ ∃ σ',
      specCr dest.bv src.bv (Fl4Spec.testBit flags.bv 0) (Fl4Spec.testBit flags.bv 1) (Fl4Spec.testBit flags.bv 2)
        (Fl4Spec.testBit flags.bv 3) σ = ({((), σ')}, False) ∧ JAtV (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  have hns : ∀ u, σ.schedulerAction ≠ .switchThread u := fun u e => by rw [hEn.2] at e; cases e
  unfold tcb.copy_registers
  simp only [lift, bind_ok]
  rw [andk_ne0 flags 1#u64 0 (by decide) (by decide), andk_ne0 flags 2#u64 1 (by decide) (by decide),
    andk_ne0 flags 4#u64 2 (by decide) (by decide), andk_ne0 flags 8#u64 3 (by decide) (by decide)]
  generalize Fl4Spec.testBit flags.bv 0 = b0
  generalize Fl4Spec.testBit flags.bv 1 = b1
  generalize Fl4Spec.testBit flags.bv 2 = b2
  generalize Fl4Spec.testBit flags.bv 3 = b3
  -- the source's suspend (the dead set kept)
  have h1 : (if b0 = true then sched.suspend st arI s a src else ok (s, a)) ⦃ r => r.2 = a ∧
      P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ∧ ∃ σ1,
      Fl4Spec.NonDet.when (b0 = true) (Fl4Spec.suspend (Z := Unit) src.bv) σ = ({((), σ1)}, False) ∧
      (∀ u, σ1.schedulerAction ≠ .switchThread u) ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ1 ⦄ := by
    cases b0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, P1.WritesIn.refl _ _, σ, rfl, hns, Z.vs, Ac, Lst, by simpa using J⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (WP.spec_and (J.suspendJD hSd hNt hRv hRp hsT (fun u e => (hns u e).elim) hsI)
        (J.suspendProjW hsT)) ?_
      rintro r ⟨⟨h1, σ1, h2, V, Ac', Lst', J'⟩, hW⟩
      exact ⟨h1, hW, σ1, by simpa [Fl4Spec.NonDet.when] using h2,
        (Vs.ak_suspend' src.bv).noSwitch (x := ((), σ1)) (by rw [h2]; exact Set.mem_singleton _) hns,
        V, Ac', Lst', J'⟩
  refine WP.spec_bind h1 ?_
  rintro ⟨s1, a1⟩ ⟨ha1, Wa, σ1, hm1, hns1, V1, Ac1, Lst1, J1⟩
  obtain rfl : a = a1 := ha1.symm
  -- the target's restart
  have h2 : (if b1 = true then sched.restart st arI s1 a dest else ok (s1, a)) ⦃ r => r.2 = a ∧
      P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ∧ ∃ σ2,
      Fl4Spec.NonDet.when (b1 = true) (Fl4Spec.restart (Z := Unit) dest.bv) σ1 = ({((), σ2)}, False) ∧
      JAtV (L := L) arI AR Z H Cs r.1 r.2 σ2 ⦄ := by
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, P1.WritesIn.refl _ _, σ1, rfl, V1, Ac1, Lst1, D, J1⟩
    · simp only [↓reduceIte]
      have hrs : sched.restart st arI s1 a dest ⦃ r => r.2 = a ∧ ∃ σ',
          Fl4Spec.restart (Z := Unit) dest.bv σ1 = ({((), σ')}, False) ∧ JAtV (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ :=
        J1.restartTcbJD (Z := Z.mv Z.G V1) hAT hSd hNt hRv hRp hmb hdT hdD hns1
      refine WP.spec_mono (WP.spec_and hrs (J1.restartProjW hAT hdT)) ?_
      rintro r ⟨⟨h1, σ2, h2, hJ⟩, hW⟩
      exact ⟨h1, hW, σ2, by simpa [Fl4Spec.NonDet.when] using h2, hJ⟩
  refine WP.spec_bind h2 ?_
  rintro ⟨s2, a2⟩ ⟨ha2, Wb, σ2, hm2, V2, Ac2, Lst2, D2, J2⟩
  obtain rfl : a = a2 := ha2.symm
  -- the register copies and the tail
  have hfr := frame_regs_val
  have hgr := gp_regs_val
  have hgp : ∀ (lp : S → Result S) (s3 : S) (σ3 : Fl4Spec.State Unit), JAtV (L := L) arI AR Z H Cs s3 a σ3 →
      (∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → lp s' ⦃ s'' => P1.WritesIn st s' s'' (Mc.ProjW (L := L) H Cs s') ∧
        ∃ σ'',
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
        JAtV (L := L) arI AR Z H Cs s'' a σ'' ⦄) →
      (if b3 = true then do
        let s5 ← lp s3
        let s6 ← tcb.post_modify_registers st s5 dest
        let t ← sched.cur_thread st s6
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s7 ← sched.reschedule_required st s6
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)
      else do
        let s6 ← tcb.post_modify_registers st s3 dest
        let t ← sched.cur_thread st s6
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s7 ← sched.reschedule_required st s6
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)) ⦃ r =>
      r.1 = .Ok () ∧ r.2.2 = a ∧ P1.WritesIn st s3 r.2.1 (Mc.ProjW (L := L) H Cs s3) ∧ ∃ σ', (do
        Fl4Spec.NonDet.when (b3 = true) (Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters)
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) ∧
        JAtV (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    intro lp s3 σ3 hJ3 hlp
    cases b3
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨V3, Ac3, Lst3, D3, J3⟩ := hJ3
      refine WP.spec_mono (J3.crTailJW hdT) ?_
      rintro r ⟨h1, h2, hW, σ', h3, h4⟩
      refine ⟨h1, h2, hW, σ', ?_, by rw [h2]; exact h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (false = true) _ σ3 = ({((), σ3)}, False) from rfl)]
      exact h3
    · simp only [↓reduceIte]
      refine WP.spec_bind (hlp s3 σ3 hJ3) ?_
      rintro s5 ⟨hW5, σ5, hm5, V5, Ac5, Lst5, D5, J5⟩
      refine WP.spec_mono (J5.crTailJW hdT) ?_
      rintro r ⟨h1, h2, hW, σ', h3, h4⟩
      refine ⟨h1, h2, hW5.projW_trans hW, σ', ?_, by rw [h2]; exact h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (true = true) _ σ3 = ({((), σ5)}, False) by
        unfold Fl4Spec.NonDet.when; rw [if_pos rfl]; exact hm5)]
      exact h3
  have hlpg : ∀ (body : S → U64 → Result (ControlFlow (S × U64) S)), (∀ s i, body s i = if i < tcb.N_GP then (do
        let i1 ← lift (UScalar.cast .Usize i)
        let r ← Aeneas.Std.Array.index_usize regs.GP_REGISTERS i1
        let v ← obj.Tcb.reg st src s r
        let i2 ← regs.sanitise r v
        let s1 ← obj.Tcb.set_reg st dest s r i2
        let i3 ← i + 1#u64
        ok (ControlFlow.cont (s1, i3)))
      else ok (ControlFlow.done s)) →
      ∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → loop (fun (x : S × U64) => body x.1 x.2) (s', 0#u64) ⦃ s'' =>
        P1.WritesIn st s' s'' (Mc.ProjW (L := L) H Cs s') ∧ ∃ σ'', Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
          JAtV (L := L) arI AR Z H Cs s'' a σ'' ⦄ :=
    fun body hbody s' σ' ⟨V', Ac', Lst', D', J'⟩ => WP.spec_mono (crJ_loopW (Z := Z.mv Z.G V') regs.GP_REGISTERS
      tcb.N_GP Fl4Spec.gpRegisters hgr (by unfold tcb.N_GP; rfl) (by decide) hsT hdT body hbody J')
      fun _ ⟨hW, σ'', hm, V'', J''⟩ => ⟨hW.mono fun _ hb => J'.rcvRegProjW hdT hb, σ'', hm, V'', Ac', Lst', D', J''⟩
  have hspec : ∀ σ3 σ', (Fl4Spec.NonDet.when (b2 = true) (do
        Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.frame_registers
        let pc ← Fl4Spec.asUser (Z := Unit) dest.bv Fl4Spec.getRestartPC
        Fl4Spec.asUser dest.bv (Fl4Spec.setNextPC pc))) σ2 = ({((), σ3)}, False) →
      (do
        Fl4Spec.NonDet.when (b3 = true) (Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters)
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) →
      specCr dest.bv src.bv b0 b1 b2 b3 σ = ({((), σ')}, False) := by
    intro σ3 σ' e3 e4
    unfold specCr
    rw [nd_bind_one hm1, nd_bind_one hm2, nd_bind_one (show Fl4Spec.archGetSanitiseRegisterInfo (Z := Unit) dest.bv σ2 =
      ({(false, σ2)}, False) from rfl)]
    exact (nd_bind_one e3 _).trans e4
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop2 st s' dest src 0#u64) s2 σ2
      ⟨V2, Ac2, Lst2, D2, J2⟩
      (fun s' σ' hJ' => by unfold tcb.copy_registers_loop2; exact hlpg _ (fun _ _ => rfl) s' σ' hJ')) ?_
    rintro r ⟨h1, h2, hW, σ', h3, h4⟩
    exact ⟨h1, h2, Wa.projW_trans (Wb.projW_trans hW), σ', hspec σ2 σ' rfl h3, h4⟩
  · simp only [↓reduceIte]
    have hl0 := crJ_loopW (Z := Z.mv Z.G V2) regs.FRAME_REGISTERS tcb.N_FRAME Fl4Spec.frame_registers hfr
      (by unfold tcb.N_FRAME; rfl) (by decide) hsT hdT _ (fun _ _ => rfl) J2
    unfold tcb.copy_registers_loop0
    refine WP.spec_bind hl0 ?_
    rintro s3 ⟨hw3, σ3, hm3, V3, J3⟩
    have Wc : P1.WritesIn st s2 s3 (Mc.ProjW (L := L) H Cs s2) := hw3.mono fun _ hb => J2.rcvRegProjW hdT hb
    have hX3 := J3.xtop.irelK J3.ks J3.buf
    obtain ⟨x3, hk3, hTR3⟩ := hX3.1.tcb dest hdT
    have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
    have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s3 dest _) ?_
    rintro pc hpc
    have hpcv : pc.bv = x3.tcbArch.tcbContext.userRegs .faultIP := by rw [hpc, hF]; exact hTR3.regs .faultIP
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s3 dest _ pc) ?_
    rintro s4 rfl
    rw [hNx]
    have Wd := J3.regProjW hdT .nextIP s3 pc
    obtain ⟨V4, J4⟩ := J3.regWrJ hdT hk3 .nextIP pc (reg_any_wr_irel J3.ip hX3 hdT hk3 .nextIP pc)
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop1 st s' dest src 0#u64) _ _ ⟨V4, Ac2, Lst2, D2, J4⟩
      (fun s' σ' hJ' => by unfold tcb.copy_registers_loop1; exact hlpg _ (fun _ _ => rfl) s' σ' hJ')) ?_
    rintro r ⟨h1, h2, hW, σ', h3, h4⟩
    refine ⟨h1, h2, Wa.projW_trans (Wb.projW_trans (Wc.projW_trans (Wd.projW_trans hW))), σ', hspec _ σ' ?_ h3, h4⟩
    unfold Fl4Spec.NonDet.when
    rw [if_pos rfl, nd_bind_one hm3,
      nd_bind_one (show Fl4Spec.asUser (Z := Unit) dest.bv Fl4Spec.getRestartPC σ3 =
        ({(x3.tcbArch.tcbContext.userRegs .faultIP, σ3)}, False) from asUser_getRegister_eq hk3 .faultIP), ← hpcv]
    exact asUser_setRegister_eq .nextIP pc.bv hk3


set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **CopyRegisters at stable ghosts, with its `ProjW` footprint** (StallNarrowTcb's `tcb_copy_regsJT`;
module docstring). -/
theorem tcb_copy_regsJTSt (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbCopyRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (hsc : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBCopyRegisters p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hctT : ct ∈ Z.T := J.thT ct (J.xtop.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_copy_eq arI s ar p _ (J.stallT p hpT), hdec0]
  unfold tcb.decode_copy_registers tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : args = [] ∨ excaps = [] →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (fun s1 a1 σ1 =>
          JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧ P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk
        call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)))
        s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
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
    have hthr0 : capV (L.mem s) x0 = .Thread src := by
      revert hsrc; cases capV (L.mem s) x0 <;> simp [threadArgF]
    simp only [J.stallT src (hcapT h0 src hthr0), bind_ok]
    obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
      have h := stsProjW J hctT sched.TS_RESTART
      rw [hs1, WP.spec_ok] at h; exact h
    obtain ⟨-, x', hk', hrun'⟩ := J.curRunnable hni hct
    rw [hk] at hk'; cases hk'
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
    have hA0 : AbsSlot Z.th e0.2 := ⟨ps0, hps01, Or.inl hps0⟩
    have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact hA0.isSlot
    have hsrcT : src ∈ Z.T := J.thT src (show CapValid Z.th (.Thread src) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe0, capAt_capV, hthr]))
    have hsI : src.bv ≠ σ1.idleThread := by rw [hid1]; exact J.ne_idle (hidS e0.2 src hA0 (by rw [← hxe0]; exact hthr))
    -- the slots kept by the caller's restart: the target's cap, so the target out of the dead set
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
      have h := XTopAt.restart J.xtop hcur hk hrun'
      rw [hs1, WP.spec_ok] at h; exact h.2.1
    have hcap1 : capAt (L.mem s1) (cslotAddr ssl) = ok (.Thread p) := by
      rw [capAt_capV, hSS.capV hAs.isSlot, hsc]
    have hC := J.curInv (by rw [hni.2]; simp)
    have hcs : Fl4Spec.schedulable σ.curThread σ = true := ct_schedulable hC J.act J.inv (hcur ▸ hk) hrun'
    obtain ⟨hres1, -, -, -, -⟩ := restart_mid hcur hk (hcur ▸ hcs) hni.2 hC J.off J.act J.inv
    have hEn1 : Entered σ1 := ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact hres1⟩
    refine WP.spec_mono ((J1.undead hAs.isSlot hcap1 hpT).copyRegsJW hAT (jCancel_send arI) (jCancel_ntfn arI)
      (jCancel_recv arI) (jCancel_reply arI) (hmb ar) hEn1 hsrcT hpT hsI (fun h => h.2 rfl) y0) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, -, W2, σ', hsp, V', Ac', Lst', D', J2⟩
    simp only at hr2; subst hr2
    have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.copyRegisters p.bv src.bv
          (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
      rw [invokeTcb_cr]
      exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac', Lst', D', J2⟩, W1.projW_trans W2⟩⟩
  · rw [hsrc]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    exact run_liftME_err (run_bind_error hrun _)

end

/-- (p3J gen 41) The Thread labels left after CopyRegisters. -/
def ThHard14 (l : U64) : Prop := ThHard13 l ∧ l ≠ fl4_abi.label.TCBCopyRegisters

/-- (p3J gen 41) The caps left after the CopyRegisters leaf, with the message label. -/
def IsRestCap22 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard14 l
  | _, _ => False

theorem restCap21_of22 {cp : capability.Cap} {l : U64} (h : IsRestCap22 cp l) : IsRestCap21 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap22_of {cp : capability.Cap} {l : U64} (h : IsRestCap21 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBCopyRegisters) : IsRestCap22 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem cp_nonIns : TcbNonIns fl4_abi.label.TCBCopyRegisters := by
  unfold TcbNonIns fl4_abi.label.TCBCopyRegisters fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The Thread cap's decode at a dispatch state at CopyRegisters, any flags** (module docstring). -/
theorem decThCpSt (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsgb : SpecGlob σb)
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
    (hl : info.label = fl4_abi.label.TCBCopyRegisters) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBCopyRegisters
  have hl5 : fl4_abi.label.TCBCopyRegisters.val ≠ 5 ∧ fl4_abi.label.TCBCopyRegisters.val ≠ 8 ∧
      fl4_abi.label.TCBCopyRegisters.val ≠ 9 ∧ fl4_abi.label.TCBCopyRegisters.val ≠ 10 ∧
      fl4_abi.label.TCBCopyRegisters.val ≠ 11 := by simp [fl4_abi.label.TCBCopyRegisters]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine XCapP.mrGT (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD cp_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_copy_regsJTSt hA hT.mb s' a' σb J hnib (J.thrNotIdle hsgb) p hpT sl'
      (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen hArgs call sl hAs hsc e (exAt e 0) (exAt e 1)
      (exAt e 2) (exAt_idx0 e) exs hXc bl don ci buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`MidDecStWL` at `KW ∧ IsRestCap21` from the CopyRegisters leaf** (module docstring). -/
theorem midDecRest21_of_cp (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBCopyRegisters
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThCpSt hA hT hMT hKD J hnib hsgb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap22_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`InvDecStWL` at `KW ∧ IsRestCap21` from the CopyRegisters leaf** (module docstring). -/
theorem invDecRest21_of_cp (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBCopyRegisters
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThCpSt hA hT hMT hKD J hnib hsgb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap22_of hW.2 hS⟩

/-- (p3J gen 41) `MidDecStWL` at `KW ∧ IsRestCap21` gives it at `KW ∧ IsRestCap22` (antitone). -/
theorem midDecStWL_of_21 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap21_of22 hW.2⟩

/-- (p3J gen 41) `InvDecStWL` at `KW ∧ IsRestCap21` gives it at `KW ∧ IsRestCap22` (antitone). -/
theorem invDecStWL_of_21 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap21 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap21_of22 hW.2⟩

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

/-- (p3J gen 41) **`DispStabFootLzo` [J]**: `DispStabFootLzn` with `invDecRest` / `midDecRest` restricted to
`IsRestCap22` (`IsRestCap21` minus the Thread caps at CopyRegisters; module docstring). -/
structure DispStabFootLzo (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzn.invDecRest` at `KW ∧ IsRestCap22`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzn.midDecRest` at `KW ∧ IsRestCap22`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzn.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzn.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 41) **`DispStabFootLzo → DispStabFootLzn`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzn_of_Lzo (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzo (L := L) arI AR MR s a σ) :
    DispStabFootLzn (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest21_of_cp hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest21_of_cp hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 41) **`DispStabFootLzn → DispStabFootLzo`** (the honesty claim: `DispStabFootLzo` is implied). -/
theorem dispStabFootLzo_of_Lzn {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzn (L := L) arI AR MR s a σ) : DispStabFootLzo (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_21 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_21 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzo` only** (`hLzo` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzo [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzo : DispStabFootLzo (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzn hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzn_of_Lzo hA hT hnd hM hIp hKD hLzo)

end

end Fl4Proofs.P3.Mc
