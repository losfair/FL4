/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2g (a')): **every CNode label ends in
`LiveDN`**: XTopJointMRCnode's `decode_invocation_cnodeJ_stepsLM` with the
posts `JAtL` / `JAtPreMVL` (XTopJointWJPL), from `LiveDN` and `SpecGlob` at
the decode's state, with no new premise.

* `JAtZ.zNoBlk`: `ZNoBlk` (XTopJointLiveStep) from `SpecGlob` at a `JAtZ`
  state: a zombie's object is a TCB (off the kernel-state block, `JKern.hks`)
  or a CNode; a CNode inside the block has its slot 0 in the IRQ node
  (`IpcApart.ks`), so it is one of the IRQ node's CNodes (`Placed.disj`),
  which no cap but a frame cap names (`SpecGlob.ref`, `IrqRel.node`).
* `JAtZLB` (`JAtZ ∧ LiveDN ∧ ZNoBlk`): the copy, mint, move, mutate and
  rotate labels by `decode_invocation_cnode_copyXS` at it (`Steps.jatL`).
* `JAtZ.cancelBadgedJL`, `cn_cancel_topJL`, `decode_invocation_cnode_cancelJL`:
  CancelBadgedSends (XTopJointCbs's `…J` at `JAtL`: the restart by
  `stepClosed_jatL`, the cancel by `LiveDN.of_jstep` with the debug words from
  P1's footprint, the original bits by `orig_eq_of_slots`, the idle thread
  from the spec's `inv_cancelBadgedSends`).
* `decode_invocation_cnode_illegalXG`: the invalid labels at any post holding
  at the decode's state.
* `decode_invocation_cnodeJ_stepsLML`: all labels; Revoke / Delete by
  g2f's `decode_invocation_cnode_{revoke,delete}JLML`.
-/
import Fl4Proofs.P3.XTopJointWJPL
import Fl4Proofs.P3.XTopJointLiveStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`cancel_badged_sends` keeps `LiveDN`** (module docstring). -/
theorem JAtZ.cancelBadgedJL {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hL : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {e : U64} (b : U64) (he : e ∈ Z.E) (hpre : EpQPre σ e.bv) :
    endpoint.cancel_badged_sends st s e b ⦃ s3 => ∃ σ3 V' D',
      ((), σ3) ∈ (Fl4Spec.cancelBadgedSends (Z := Unit) e.bv b.bv σ).1 ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D' s3 a σ3 ∧ LiveDN (L := L) Z.th H Cs Z.G s3 σ3 ⦄ := by
  have hpH : H e = some .ep := J.zH.2.1 e he
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.1.ztcb
  refine WP.spec_mono (WP.spec_and (J0.cancelBadgedJ b he hpre)
    (P1.endpoint.cancel_badged_sends.blkF s e b J.blk hpH)) ?_
  rintro s3 ⟨⟨σ3, V', hm3, J3, hSS, -⟩, -, hfoot0⟩
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s3 :=
    P1.Foot.dbgKeep J.blk (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inl hpH) hfoot0
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨y, hky, -⟩ := hI.1.toE.ep e he
  have hEP := hI.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, -⟩ := hEP.queue
  have hnd : y.epQueue.Nodup := by rw [hxs]; exact hQ.nodup.map (fun a b h => eq_of_bv h)
  have hbl : ∀ u ∈ y.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧ Fl4Spec.epBlocked xu.tcbState = some e.bv :=
    fun u hu => ep_queue_blocked J.ip hI he hky hu
  obtain ⟨-, -, F, -⟩ := inv_cancelBadgedSends (P := fun _ => False) J.inv J.bsa hky hnd hbl hm3
  exact ⟨σ3, V', _, hm3, J3, LiveDN.of_jstep J hL J3 rfl rfl hSS hdk
    (orig_eq_of_slots J.xtop.rel.2.1.2.2.2.1 J3.xtop.rel.2.1.2.2.2.1 J.kern.orig J3.kern.orig hSS) F.sk.idle
    (fun p hp => Or.inr hp)⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- **`JAtZ`, `LiveDN` and `ZNoBlk` at their own ghosts.** -/
def JAtZLB (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ LiveDN (L := L) Z.th H Cs Z.G s σ ∧ ZNoBlk Z.th (L.mem s) (L.ksb s)

theorem JAtZLB.toL {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtZLB (L := L) arI AR s a σ) :
    JAtL (L := L) arI AR s a σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, J, hL, _⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, J, hL⟩

set_option maxHeartbeats 4000000 in
/-- **A CancelBadgedSends's outcome at `JAtL`** (XTopJointCbs's `cn_cancel_topJ`;
module docstring). -/
theorem cn_cancel_topJL (hAM : ARMask arI AR) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (hQ : ∀ e, EpQPre σ e)
    (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (e b : U64) (sl : Fl4Spec.CslotPtr), AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z.E)
    {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : CancelDec (L := L) Z.th ct σ m s (res.1, res.2.1) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (JAtL (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, p, b, rfl, ⟨sl, hsl, hcV⟩, s2, hs2, h0, h1⟩ := hq
    obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
    have hrn : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
    have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
      have hst' := hst
      rw [hcur, Notif.setThreadState_eq .restart hk] at hst'
      have := congrArg (fun q => ((), σ1) ∈ q.1) hst'
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
      simpa using this.symm
    -- the caller's restart at `J` with the liveness
    obtain ⟨G1, V1, Ac1, Lst1, D1, J1, -⟩ := (stepClosed_jat arI hAM (jStepHyps arI)).restart s a' σ ct x s2 hcur
      hk htcb hrn hs2 Z H Cs Ac Lst D rfl J hZB
    have hL1 := J1.live
    rw [← hσ1] at J1 hL1
    by_cases hb : b = 0#u64
    · subst hb
      have e := h0 rfl
      subst e
      have hrun0 : (Fl4Spec.invokeCnode (Z := Unit)
          (.cancelBadgedSendsCall (absCap (.Endpoint p 0#u64 true true true true)))).run σ1 =
          ({(.ok (), σ1)}, False) := by
        show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv (0#u64 : U64).bv (rightsOf true true true true)))).run σ1 = _
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when]
        have : ¬ ((0#u64 : U64).bv ≠ 0) := by simp
        simp only [this, ↓reduceIte]
        exact run_liftE rfl
      have hx : ((.ok (), σ1) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p 0#u64 true true true true)))).run σ1).1 := by rw [hrun0]; rfl
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ1),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨_, _, Or.inl ⟨rfl, rfl⟩, J1.xtop.rel.1, J1.xtop.rel.2.1,
          J1.xtop.rel.2.2.1, J1.xtop.rel.2.2.2.1, J1.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J1, hL1⟩⟩
    · have hcb := h1 hb
      have he : p ∈ (Z.mv G1 V1).E := hE p b sl hsl hcV
      have hpre : EpQPre σ1 p.bv := by rw [hσ1]; exact epQPre_restart hk (hQ _) hsw
      have h := J1.cancelBadgedJL hL1 b he hpre
      rw [hcb, WP.spec_ok] at h
      obtain ⟨σ3, V3, D3, hm3, J3, hL3⟩ := h
      have hbv : b.bv ≠ 0 := by
        intro h; apply hb; apply UScalar.eq_of_val_eq
        have := congrArg BitVec.toNat h; simpa using this
      have hx : ((.ok (), σ3) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p b true true true true)))).run σ1).1 := by
        show _ ∈ ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv b.bv (rightsOf true true true true)))).run σ1).1
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when, hbv, ne_eq, not_false_eq_true, ↓reduceIte]
        exact mem_liftE (x := ((), σ3)) hm3
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ3),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1,
          J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1, J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D3, J3, hL3⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The CNode CancelBadgedSends label at `JAtL`** (XTopJointCbs's
`decode_invocation_cnode_cancelJ`, `cn_cancel_topJL`). -/
theorem decode_invocation_cnode_cancelJL (hAM : ARMask arI AR) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (hQ : ∀ e, EpQPre σ e)
    (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (e b : U64) (sl : Fl4Spec.CslotPtr), AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z.E)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAtL (L := L) arI AR) s ar σ fl4_abi.label.CNodeCancelBadgedSends length slot
      (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_cancel_dec arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hFI hact hcur htcb)
      fun res h => cn_cancel_topJL arI hAM J hLv hZB hC hcur hQ hsw hE h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩⟩

/-- **The CNode cap's invalid labels at any post holding at the decode's
state** (XTopJointCbs's `decode_invocation_cnode_illegalJ`). -/
theorem decode_invocation_cnode_illegalXG {X : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX0 : X s ar σ)
    (lbl : U64) (hlo : lbl.val < 25 ∨ 32 < lbl.val) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List Fl4Spec.Data)
    (p r gs g : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI X s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold cnodeLabelOf
    simp only [show lbl.val ≠ 25 by omega, show lbl.val ≠ 26 by omega, show lbl.val ≠ 27 by omega,
      show lbl.val ≠ 28 by omega, show lbl.val ≠ 29 by omega, show lbl.val ≠ 30 by omega,
      show lbl.val ≠ 31 by omega, show lbl.val ≠ 32 by omega, ↓reduceIte]
  have hdec := decode_illegal slbl args (absCap (.CNode p r gs g)) (excaps.map Prod.fst) σ (by rw [hg]; decide)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold cnode.decode
    rcases hlo with h | h
    · have n1 : lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      rw [if_pos n1]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, hX0⟩
    · have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      have n2 : lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
      rw [if_neg n1, if_pos n2]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, hX0⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- **The CNode cap, every label, `JAtL` after** (XTopJointMRCnode's
`decode_invocation_cnodeJ_stepsLM` with the liveness; module docstring). -/
theorem decode_invocation_cnodeJ_stepsLML [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hJDP : JDelParts (L := L) arI AR Z.th)
    (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hQ : ∀ e, Sched.EpQPre σ e)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAtL (L := L) arI AR) (JAtPreMVL (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl)
      (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  have hZB := J.zNoBlk hsg
  have hJP : ∀ kb, PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb))
      (WJPML (L := L) arI AR MR Z H Cs kb) Z.th :=
    fun kb => jPreemptHypLML arI hARI.toARKeep hT hnd hMP hPA Z H Cs kb rfl
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hJD := hJDP.jDelHypLML arI hT hnd hMP hKD hPA hARI.toMask
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 32
  · obtain ⟨hcur, -⟩ := J.curEq hct
    exact (XCap.imp arI (decode_invocation_cnode_copyXS arI s ar σ hX (J.curRun.run hni)
      (X := JAtZLB (L := L) arI AR) ⟨Z, H, Cs, Ac, Lst, D, J, hLv, hZB⟩
      (fun _ _ _ h => let ⟨_, V', Ac', Lst', D', J', hL', hZ'⟩ := Steps.jatL hARI.toMask h rfl J hLv hZB
        ⟨_, H, Cs, Ac', Lst', D', J', hL', hZ'⟩)
      (fun _ _ _ h => let ⟨Z', _, _, _, _, _, J', _⟩ := h; ⟨Z', J'.xtop⟩) lbl hcp slbl hlbl
      length buf ct hct args hlen hargs p r gs g hwf hcv ⟨cslotAddr sl, hAs.isSlot, hsc⟩ extra x0 x1 hx0 hx1
      excaps hex J.kern.act hcur (cslotAddr sl) blk call don fp ci sl buffer)
      fun _ _ _ h => JAtZLB.toL arI h).toPN arI (cnode_noPre_of hlbl (by omega))
  by_cases hrd : 25 ≤ lbl.val ∧ lbl.val ≤ 26
  · rcases (show lbl.val = 25 ∨ lbl.val = 26 by omega) with h | h
    · have e : lbl = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
      subst e
      exact decode_invocation_cnode_revokeJLML arI s ar σ J hni hMP hmv hJD hJP hsg hP0 hLv slbl
        (by rw [hlbl]; simp [cnodeLabelOf])
        length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
    · have e : lbl = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
      subst e
      exact decode_invocation_cnode_deleteJLML arI s ar σ J hni hMP hmv hJD hsg hP0 hLv slbl
        (by rw [hlbl]; simp [cnodeLabelOf])
        length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
  by_cases hlo : lbl.val < 25 ∨ 32 < lbl.val
  · exact (decode_invocation_cnode_illegalXG arI (X := JAtL (L := L) arI AR) s ar σ ⟨Z, H, Cs, Ac, Lst, D, J, hLv⟩
      lbl hlo slbl hlbl length buf ct hct _ p r gs g extra excaps
      (cslotAddr sl) blk call don fp ci sl buffer).toPN arI (cnode_noPre_of hlbl (by omega))
  have h27 : lbl.val = 27 := by omega
  have e : lbl = fl4_abi.label.CNodeCancelBadgedSends := UScalar.eq_of_val_eq (by rw [h27, lbl_cancel_val])
  subst e
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact (decode_invocation_cnode_cancelJL arI hARI.toMask s ar σ J hLv hZB (J.curRun.run hni) slbl
    (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps J.kern.act hcur
    hQ (fun u hu => by rw [hni.2] at hu; cases hu) (fun e b sl' hsl hcV => by
      obtain ⟨Tr, Cq, hJl⟩ := J.jpl
      exact J.hset.1 e ((hJl.typed _ hsl.isSlot).1 e b _ _ _ _ hcV)) (cslotAddr sl)
    blk call don fp ci sl buffer).toPN arI (cnode_noPre_of hlbl (by omega))

end

end

end Fl4Proofs.P3
