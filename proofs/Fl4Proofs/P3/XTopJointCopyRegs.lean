/-
P3 (DESIGN.md §9), TCB: **CopyRegisters' work at `J`** (IpcCopyRegsJ's
`copy_registers_irelS` with `JAtZ` carried; the label itself is
XTopJointTcb's `tcb_copy_regsJ`).

* `JAtZ.schedJ` (moved from XTopJointTcb), `JAtZ.reschedJ`: a scheduler
  step, `reschedule_required`, at `J` (`ActReady` from `Inv`).
* `crJ_loop`: a register-copy loop of `copy_registers` at `J` (as
  `cr_loop_gen`, each copy by `JAtZ.regWrJ` with `reg_any_wr_irel`).
* `JAtZ.crTailJ`: `post_modify_registers` and the reschedule of the
  current thread at `J` (as `cr_tailA`).
* `JAtZ.copyRegsJ`: `tcb::copy_registers` at `J`: the source's suspend by
  `JAtZ.suspendJD` (the dead set kept, so the target, out of it, stays out),
  the target's restart by `JAtZ.restartTcbJD` (no switch pending; when the
  source was the current thread, a reschedule is pending and the target may
  be the current thread itself: `restartTail_specCn`), the copies and the
  tail.
-/
import Fl4Proofs.P3.XTopJointWriteRegs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **A scheduler step at `J`** (`stepClosed_jat`'s scheduler case, with
XTopJointRest's `jowes_sched`, no premise). -/
theorem JAtZ.schedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS : SchedStep (L := L) Z.th s σ s' σ') :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' ar σ' := by
  have hX := J.xtop
  have hX1 := hX.schedStep J.ks J.thT hS
  have hW := (hS.2.1 Z.N Z.T Z.C Z.c J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    hX.slotsSame_of hW fun b hb => schW_oobj hX.fin.1.1.1.placed.tcb hb
  obtain ⟨Ac', Lst', R⟩ := jowes_sched arI s s' ar σ σ' hS Z H Cs Ac Lst D rfl J hX1
  exact ⟨Ac', Lst', D, J.cs_frameK hW.1 hX1 (KBack.of_kheap hS.1.kh) (IpcFrKeep.of_kheap hS.1.kh) (JCs.same J hSS (KSz.of_kheap hS.1.kh)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J.vkeep_of hW fun _ hb => J.schW_nv hb)
    hSS (dbgKeep_of_writes J.blk hW fun _ hb => J.schW_notDbg hb) hS.1.idle⟩

set_option maxHeartbeats 4000000 in
/-- **`reschedule_required` at `J`** (`ActReady` from `JAtZ`'s `Inv`;
`JAtZ.schedJ`). -/
theorem JAtZ.reschedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) :
    ∃ s', sched.reschedule_required st s = ok s' ∧ ∃ σ', Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' ar σ' := by
  have hA2 : Notif.ActReady σ := J.inv.actReady
  obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA2
  have hS := J.xtop.fin.1.1.1
  have hN := J.xtop.fin.1.1.2.2.1
  obtain ⟨s3, hrun3, ⟨σ3, he3, -, -, -, -⟩, -⟩ := spec_exists (WP.spec_and
    (Sched.reschedule_required_refines _ _ hN hS hA2) (Sched.reschedule_required_sfootI hS))
  rw [hres] at he3
  have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
  subst σ3
  exact ⟨s3, hrun3, _, hres, J.schedJ (schedStep_resched hA2 hrun3 hres hK' hdl' hds')⟩

/-- `JAtZ` at some VSpace sets, frame sets, call lists and dead set. -/
abbrev JAtV (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ

set_option maxHeartbeats 8000000 in
/-- **A register-copy loop of `copy_registers` at `J`** (as `cr_loop_gen`). -/
theorem crJ_loop {a : A} {k : Usize} (arr : Aeneas.Std.Array U64 k) (Nl : U64)
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
    loop (fun (x : S × U64) => body x.1 x.2) (s0, 0#u64) ⦃ s' => ∃ σ',
      Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Lr σ0 = ({((), σ')}, False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  apply loop.spec_decr_nat (measure := fun x => Lr.length - x.2.val)
    (inv := fun x => x.2.val ≤ Lr.length ∧ ∃ σ', Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) (Lr.take x.2.val) σ0 =
      ({((), σ')}, False) ∧ ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D x.1 a σ')
  · rintro ⟨s', i⟩ ⟨hi, σ', hm, V', J'⟩
    simp only at hi hm J' ⊢
    have hX' := J'.xtop.irelK J'.ks J'.buf
    rw [hbody]
    by_cases h1 : i < Nl
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = Lr.length := by have := (P1.gt_iff_val).not.1 h1; omega
      rw [this, List.take_length] at hm
      exact ⟨σ', hm, V', J'⟩
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
    refine ⟨⟨by show i3.val ≤ Lr.length; omega, _, ?_, V2, J2⟩,
      by show Lr.length - i3.val < Lr.length - i.val; omega⟩
    rw [hi3, List.take_succ, List.getElem?_eq_getElem hiL]
    simp only [Option.toList_some]
    rw [mapMx_snoc, nd_bind_one hm]
    unfold crb
    simp only [nd_assoc_f]
    rw [nd_bind_one (asUser_getRegister_eq hks _), ← hTs.regs, ← hwv, nd_bind_one (asUser_setRegister_eq _ _ hkd)]
    rfl
  · exact ⟨by simp, σ0, by simp; rfl, Z.vs, by simpa using J⟩

set_option maxHeartbeats 8000000 in
/-- **The tail of `copy_registers` at `J`** (as `cr_tailA`):
`post_modify_registers` (`JAtZ.regWrJ`), the reschedule of the current
thread (`JAtZ.reschedJ`). -/
theorem JAtZ.crTailJ {a : A} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {dest : U64} (hd : dest ∈ Z.T) :
    (do
      let s6 ← tcb.post_modify_registers st s dest
      let t ← sched.cur_thread st s6
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
      if b then do
        let s7 ← sched.reschedule_required st s6
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s7, a)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a)) ⦃ r =>
      r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ', (do
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ = ({((), σ')}, False) ∧
        JAtV (L := L) arI AR Z H Cs r.2.1 a σ' ⦄ := by
  have hX := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, -⟩ := hX.1.tcb dest hd
  have hpm : tcb.post_modify_registers st s dest ⦃ s4 => ∃ ct : U64, σ.curThread = ct.bv ∧ ∃ σ4,
      Fl4Spec.archPostModifyRegisters (Z := Unit) ct.bv dest.bv σ = ({((), σ4)}, False) ∧
      σ4.curThread = ct.bv ∧ ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s4 a σ4 ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX.2.2.1) ?_
    rintro ct hct
    rw [tcb_ne_eq, bind_ok]
    by_cases hpc' : dest = ct
    · subst hpc'
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨dest, hct.symm, σ, ?_, hct.symm, Z.vs, by simpa using J⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_neg (by simp)]; rfl
    · simp only [ne_eq, hpc', not_false_eq_true, decide_true, ↓reduceIte]
      have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
      refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ dest _ 0#u64) ?_
      rintro s4 rfl
      rw [hE]
      refine ⟨ct, hct.symm, _, ?_, by simp [Notif.updK, hct],
        J.regWrJ hd hk .errorRegister 0#u64 (reg_any_wr_irel J.ip hX hd hk .errorRegister 0#u64)⟩
      unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
      rw [if_pos (fun e => hpc' (P1.eq_of_bv e)), asUser_setRegister_eq _ _ hk]
      rfl
  refine WP.spec_bind hpm ?_
  rintro s4 ⟨ct, hct, σ4, hpm4, hct4, V4, J4⟩
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
    rw [hrun, bind_ok, WP.spec_ok]
    exact ⟨rfl, rfl, σ6, hfin σ6 (by simpa [Fl4Spec.NonDet.when] using h6), V4, Ac6, Lst6, D6, J6⟩
  · simp only [hpc', decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, trivial, σ4, hfin σ4 (by
      unfold Fl4Spec.NonDet.when; rw [if_neg (fun e => hpc' (P1.eq_of_bv e))]; rfl), V4, Ac, Lst, D, J4⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 32000000 in
/-- **`copy_registers` at `J`** (module docstring): `Entered` at the start
(the caller's restart's); the source not idle (`hsI`); the target out of
the dead set (`hdD`, its cap in a slot by `JAtZ.undead`); the platform's
`MIN_BUDGET` [P]. -/
theorem JAtZ.copyRegsJ (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    {a : A}
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hEn : Entered σ)
    {src dest : U64} (hsT : src ∈ Z.T) (hdT : dest ∈ Z.T) (hsI : src.bv ≠ σ.idleThread) (hdD : dest ∉ D)
    (flags : U64) :
    tcb.copy_registers st arI s a dest src flags ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ',
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
  have h1 : (if b0 = true then sched.suspend st arI s a src else ok (s, a)) ⦃ r => r.2 = a ∧ ∃ σ1,
      Fl4Spec.NonDet.when (b0 = true) (Fl4Spec.suspend (Z := Unit) src.bv) σ = ({((), σ1)}, False) ∧
      (∀ u, σ1.schedulerAction ≠ .switchThread u) ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ1 ⦄ := by
    cases b0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ, rfl, hns, Z.vs, Ac, Lst, by simpa using J⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (J.suspendJD hSd hNt hRv hRp hsT (fun u e => (hns u e).elim) hsI) ?_
      rintro r ⟨h1, σ1, h2, V, Ac', Lst', J'⟩
      exact ⟨h1, σ1, by simpa [Fl4Spec.NonDet.when] using h2,
        (Vs.ak_suspend' src.bv).noSwitch (x := ((), σ1)) (by rw [h2]; exact Set.mem_singleton _) hns,
        V, Ac', Lst', J'⟩
  refine WP.spec_bind h1 ?_
  rintro ⟨s1, a1⟩ ⟨ha1, σ1, hm1, hns1, V1, Ac1, Lst1, J1⟩
  obtain rfl : a = a1 := ha1.symm
  -- the target's restart
  have h2 : (if b1 = true then sched.restart st arI s1 a dest else ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ2,
      Fl4Spec.NonDet.when (b1 = true) (Fl4Spec.restart (Z := Unit) dest.bv) σ1 = ({((), σ2)}, False) ∧
      JAtV (L := L) arI AR Z H Cs r.1 r.2 σ2 ⦄ := by
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ1, rfl, V1, Ac1, Lst1, D, J1⟩
    · simp only [↓reduceIte]
      have hrs : sched.restart st arI s1 a dest ⦃ r => r.2 = a ∧ ∃ σ',
          Fl4Spec.restart (Z := Unit) dest.bv σ1 = ({((), σ')}, False) ∧ JAtV (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ :=
        J1.restartTcbJD (Z := Z.mv Z.G V1) hAT hSd hNt hRv hRp hmb hdT hdD hns1
      refine WP.spec_mono hrs ?_
      rintro r ⟨h1, σ2, h2, hJ⟩
      exact ⟨h1, σ2, by simpa [Fl4Spec.NonDet.when] using h2, hJ⟩
  refine WP.spec_bind h2 ?_
  rintro ⟨s2, a2⟩ ⟨ha2, σ2, hm2, V2, Ac2, Lst2, D2, J2⟩
  obtain rfl : a = a2 := ha2.symm
  -- the register copies and the tail
  have hfr := frame_regs_val
  have hgr := gp_regs_val
  have hgp : ∀ (lp : S → Result S) (s3 : S) (σ3 : Fl4Spec.State Unit), JAtV (L := L) arI AR Z H Cs s3 a σ3 →
      (∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → lp s' ⦃ s'' => ∃ σ'',
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
      r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ', (do
        Fl4Spec.NonDet.when (b3 = true) (Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters)
        let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
        Fl4Spec.archPostModifyRegisters cur dest.bv
        Fl4Spec.NonDet.when (dest.bv = cur) Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) ∧
        JAtV (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    intro lp s3 σ3 hJ3 hlp
    cases b3
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨V3, Ac3, Lst3, D3, J3⟩ := hJ3
      refine WP.spec_mono (J3.crTailJ hdT) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, by rw [h2]; exact h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (false = true) _ σ3 = ({((), σ3)}, False) from rfl)]
      exact h3
    · simp only [↓reduceIte]
      refine WP.spec_bind (hlp s3 σ3 hJ3) ?_
      rintro s5 ⟨σ5, hm5, V5, Ac5, Lst5, D5, J5⟩
      refine WP.spec_mono (J5.crTailJ hdT) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, by rw [h2]; exact h4⟩
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
        ∃ σ'', Fl4Spec.NonDet.mapMx (crb src.bv dest.bv) Fl4Spec.gpRegisters σ' = ({((), σ'')}, False) ∧
          JAtV (L := L) arI AR Z H Cs s'' a σ'' ⦄ :=
    fun body hbody s' σ' ⟨V', Ac', Lst', D', J'⟩ => WP.spec_mono (crJ_loop (Z := Z.mv Z.G V') regs.GP_REGISTERS
      tcb.N_GP Fl4Spec.gpRegisters hgr (by unfold tcb.N_GP; rfl) (by decide) hsT hdT body hbody J')
      fun _ ⟨σ'', hm, V'', J''⟩ => ⟨σ'', hm, V'', Ac', Lst', D', J''⟩
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
    rintro r ⟨h1, h2, σ', h3, h4⟩
    exact ⟨h1, h2, σ', hspec σ2 σ' rfl h3, h4⟩
  · simp only [↓reduceIte]
    have hl0 := crJ_loop (Z := Z.mv Z.G V2) regs.FRAME_REGISTERS tcb.N_FRAME Fl4Spec.frame_registers hfr
      (by unfold tcb.N_FRAME; rfl) (by decide) hsT hdT _ (fun _ _ => rfl) J2
    unfold tcb.copy_registers_loop0
    refine WP.spec_bind hl0 ?_
    rintro s3 ⟨σ3, hm3, V3, J3⟩
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
    obtain ⟨V4, J4⟩ := J3.regWrJ hdT hk3 .nextIP pc (reg_any_wr_irel J3.ip hX3 hdT hk3 .nextIP pc)
    refine WP.spec_mono (hgp (fun s' => tcb.copy_registers_loop1 st s' dest src 0#u64) _ _ ⟨V4, Ac2, Lst2, D2, J4⟩
      (fun s' σ' hJ' => by unfold tcb.copy_registers_loop1; exact hlpg _ (fun _ _ => rfl) s' σ' hJ')) ?_
    rintro r ⟨h1, h2, σ', h3, h4⟩
    refine ⟨h1, h2, σ', hspec _ σ' ?_ h3, h4⟩
    unfold Fl4Spec.NonDet.when
    rw [if_pos rfl, nd_bind_one hm3,
      nd_bind_one (show Fl4Spec.asUser (Z := Unit) dest.bv Fl4Spec.getRestartPC σ3 =
        ({(x3.tcbArch.tcbContext.userRegs .faultIP, σ3)}, False) from asUser_getRegister_eq hk3 .faultIP), ← hpcv]
    exact asUser_setRegister_eq .nextIP pc.bv hk3

end

end

end Fl4Proofs.P3
