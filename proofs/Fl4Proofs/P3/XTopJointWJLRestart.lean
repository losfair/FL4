/-
P3 (DESIGN.md §9), CSpace: **`WJL` across the caller's restart** and the CNode
Delete and Revoke labels with the deletion at `WJL` (XTopJointWJLDel's
`JDelHypL`), so that they need no `LiveJHyp`.

* `LiveDN th H Cs G s σ`: `LiveJ`, `DbgWF` and `NullOrig` at a state (the
  three facts `WJL` adds to `WJR`; the entry fact `JEntryAt.live`).
* `WJL.restart`: the caller's restart keeps `WJL` from `JAtZ`, `LiveDN`,
  `SpecGlob` and `PPR0` at the start: the slots, the original bits and the
  debug words kept (P1's `set_thread_state.restart_ok` footprint,
  `Foot.dbgKeep`), the TCB zombies' TCBs dead after (XTopJointRest's
  `jowes_restartD` at the dead set grown by `ZTcb`, `JAtZ.addDeadSet`: a dead TCB is
  `TS_INACTIVE`, the restarted current thread runnable, so it is no TCB
  zombie's TCB), then XTopJointWJLFin's `wjl_keep`. `EJL.restart`: with
  `DelE` (`delE_restart`).
* `cn_del_topJL`, `decode_invocation_cnode_{revoke,delete}JL`,
  `decode_invocation_cnodeJ_stepsL`: XTopJointCnDel's `cn_del_topJ`,
  `decode_invocation_cnode_{revoke,delete}J` and
  the former `decode_invocation_cnodeJ_steps` with the deletion at `EJL` (`DelE ∧ WJL`,
  `JDelHypL`; the preemption point by `rppHyp_fullW` of `jPreemptHypL`), from
  `LiveDN` at the invocation's start.
-/
import Fl4Proofs.P3.XTopJointWJLDel
import Fl4Proofs.P3.XTopJointIrqDel
import Fl4Proofs.P3.ZNoBlkJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The caller's restart keeps `WJL`** (module docstring). -/
theorem WJL.restart {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      WJL (L := L) arI AR Z H Cs (L.ksb s) s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 hst
  have hsg1 : SpecGlob σ1 := SpecGlob.sts (mem_of_single hst) hsg
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  obtain ⟨hL, hDW, hN⟩ := hLv
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨Ac1, Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  have hns1 : Vs.NoSwitch (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  -- the debug words: P1's footprint of the restart
  have hT : ct ∈ Z.T := J.thT ct htcb
  have hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := by
    obtain ⟨x', hk', hRt⟩ := J.xtop.ipc.tcb ct hT
    rw [hk] at hk'; cases hk'
    have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
      have hq := Sched.blockedR_queued hRt.st hb
      cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
    have hTe : Z.T = P1.Heap.tcbs H := by
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
    rw [hTe] at hT
    exact P1.Foot.dbgKeep J.blk (Set.empty_subset _)
      (P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hT (fun h => hnbr (Or.inl h))
        (fun h => hnbr (Or.inr h)) hs1).2.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  have hDS1 : DState (L := L) Z.th s1 (Notif.stsAct (Notif.updK σ ct.bv
      (.tcb { x with tcbState := .restart })) ct.bv) Z.G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI (Z := Z) (G := Z.G) (V := Z.vs) (V1 := Z.vs) J hDS hL hDW hN J1 J.zD hSS hDS1 hK (by unfold Notif.stsAct; split <;> rfl)
  exact ⟨⟨Z.vs, Ac1, Lst', D, J1, hk1, hns1, hsg1, hP0.of_ppk (PPK.restart hk .restart (Or.inl hcur.symm))⟩, hL1, hDW1, hN1⟩

/-- **`DelE` and `WJL`** (the deletion's invariant at `WJL`, `JDelHypL`). -/
abbrev EJL (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJL (L := L) arI AR Z H Cs kb s a σ G

/-- **The caller's restart keeps `EJL`** (module docstring). -/
theorem EJL.restart {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {K : Nat} (hDE : DelE (L := L) Z.th K s σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      EJL (L := L) arI AR Z H Cs (L.ksb s) K s1 ar σ1 Z.G :=
  fun s1 σ1 hs1 hS hst => ⟨delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst),
    WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 hs1 hst⟩

set_option maxHeartbeats 4000000 in
/-- **A Delete's or Revoke's outcome at `EJL`** (`cn_del_topJ` at `EJL`). -/
theorem cn_del_topJL {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    {kb : U64} {K : Nat} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (EJL (L := L) arI AR Z H Cs kb K) (EJP (L := L) arI AR Z H Cs kb K) s ar
      res) :
    TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ |
    ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR', hFI', -, hE'⟩
  · have hne : e ≠ .Preempted := by rintro rfl; cases e' <;> exact h2.elim
    refine Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ?_⟩
    simp only [core.result.Result.Err.injEq, hne, if_false]
    exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
  · rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · obtain ⟨-, ⟨V, Ac', Lst', D', J', -⟩, -⟩ := hE'
      have hX' := J'.xtop
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
      simp only [reduceCtorEq, if_false]
      exact ⟨_, H, Cs, Ac', Lst', D', J'⟩
    · obtain ⟨-, s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hE'
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.error (), σ'),
        mem_bindE_err hx, ⟨Z.th, G', Or.inr ⟨rfl, rfl⟩, J.xtop.rel.1, hCR', hFI', hDom, hMO⟩, ?_⟩
      simp only [if_true]
      exact ⟨s0, a0, σ0, ⟨⟨_, H, Cs, Ac', Lst', D', J0⟩, hns0, hp00⟩, hpp, hspp⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Revoke label** (25): `cnode_revoke_refinesW` at
`EJL` (`JDelHypL`, `rppHyp_fullW` of `jPreemptHypL`, `EJL.restart`), then
`cn_del_topJL`. -/
theorem decode_invocation_cnode_revokeJL (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hJD : JDelHypL (L := L) arI AR Z.th)
    (hJP : ∀ kb, PPHypDW (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) Z.th)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.CNodeRevoke length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hfew : psiD (L.mem s) Z.G < 2 ^ 64 - 1 := by
    have := hDE.2.1 Z.G hM
    omega
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_revoke_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJL (L := L) arI AR Z H Cs (L.ksb s) K)
      (EJP (L := L) arI AR Z H Cs (L.ksb s) K)
      psiD psiD_slotsSame (hJD Z H Cs (L.ksb s) K rfl hK hK6)
      (rppHyp_fullW arI (WJL (L := L) arI AR Z H Cs (L.ksb s)) (WJP (L := L) arI AR Z H Cs (L.ksb s)) Z.th K
        (hJP (L.ksb s)))
      (EJL.restart arI J hni hsg hP0 hLv hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩) hfew)
      fun res h => cn_del_topJL arI J h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨Z, H, Cs, Ac, Lst, D, J⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Delete label** (26), for any cap: as
`decode_invocation_cnode_revokeJL`, by `cnode_delete_refinesW` at `EJL`. -/
theorem decode_invocation_cnode_deleteJL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hJD : JDelHypL (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.CNodeDelete length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_delete_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJL (L := L) arI AR Z H Cs (L.ksb s) K)
      (EJP (L := L) arI AR Z H Cs (L.ksb s) K)
      psiD (hJD Z H Cs (L.ksb s) K rfl hK hK6) (EJL.restart arI J hni hsg hP0 hLv hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      fun res h => cn_del_topJL arI J h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨Z, H, Cs, Ac, Lst, D, J⟩

/-- **A CNode cap at an FL4 label other than Revoke and Delete** decodes to
no invocation with a preemption point (`specDec_cnode_noPre`). -/
theorem cnode_noPre_of {slbl : Fl4Spec.Data} {lbl : U64}
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl) (h : lbl.val ≠ 25 ∧ lbl.val ≠ 26)
    {fp : Bool} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit}
    {p r gs g : U64} :
    ∀ inv, DecOut (specDec fp slbl args ci sl (.CNode p r gs g) excaps buffer) σ inv → ¬ NoPre.PreInv inv := by
  refine specDec_cnode_noPre ?_ ?_ <;> rw [hlbl] <;> unfold cnodeLabelOf <;> intro e <;> split_ifs at e <;>
    first | omega | cases e

set_option maxHeartbeats 4000000 in
/-- **The CNode cap, `JAt` after, with the deletion at `EJL`**:
the former XTopJointCnDel `decode_invocation_cnodeJ_steps` with Revoke and Delete by
`decode_invocation_cnode_{revoke,delete}JL` (`JDelParts.jDelHypL`, the
preemption point by `jPreemptHypL`), from `LiveDN` at the invocation's start
(`hLv`). -/
theorem decode_invocation_cnodeJ_stepsL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hJDP : JDelParts (L := L) arI AR Z.th)
    (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
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
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ lbl length (cslotAddr sl)
      (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ : JStepHyps (L := L) arI AR Z.th := jStepHyps arI
  have hX := J.xtop
  have hJP : ∀ kb, PPHypDW (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) Z.th :=
    fun kb => jPreemptHypL arI hARI.toARKeep hT hnd hPP Z H Cs kb rfl
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hJD := hJDP.jDelHypL arI hT hnd hPP hARI.toMask
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 32
  · obtain ⟨hcur, -⟩ := J.curEq hct
    exact (decode_invocation_cnode_copyXS arI s ar σ hX (J.curRun.run hni) ⟨Z, H, Cs, Ac, Lst, D, J⟩
      (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J (J.zNoBlk hsg)) (fun _ _ _ h => JAt.xtop arI h) lbl hcp slbl hlbl
      length buf ct hct args hlen hargs p r gs g hwf hcv ⟨cslotAddr sl, hAs.isSlot, hsc⟩ extra x0 x1 hx0 hx1
      excaps hex J.kern.act hcur (cslotAddr sl) blk call don fp ci sl buffer).toPN arI
      (cnode_noPre_of hlbl (by omega))
  by_cases hrd : 25 ≤ lbl.val ∧ lbl.val ≤ 26
  · rcases (show lbl.val = 25 ∨ lbl.val = 26 by omega) with h | h
    · have e : lbl = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
      subst e
      exact decode_invocation_cnode_revokeJL arI s ar σ J hni hJD hJP hsg hP0 hLv slbl (by rw [hlbl]; simp [cnodeLabelOf])
        length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
    · have e : lbl = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
      subst e
      exact decode_invocation_cnode_deleteJL arI s ar σ J hni hJD hsg hP0 hLv slbl (by rw [hlbl]; simp [cnodeLabelOf])
        length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
  by_cases hlo : lbl.val < 25 ∨ 32 < lbl.val
  · exact (decode_invocation_cnode_illegalJ arI s ar σ J lbl hlo slbl hlbl length buf ct hct _ p r gs g extra excaps
      (cslotAddr sl) blk call don fp ci sl buffer).toPN arI (cnode_noPre_of hlbl (by omega))
  have h27 : lbl.val = 27 := by omega
  have e : lbl = fl4_abi.label.CNodeCancelBadgedSends := UScalar.eq_of_val_eq (by rw [h27, lbl_cancel_val])
  subst e
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact (decode_invocation_cnode_cancelJ arI hARI.toMask hJ s ar σ J (J.curRun.run hni) slbl
    (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps J.kern.act hcur
    hQ (fun u hu => by rw [hni.2] at hu; cases hu) (fun e b sl' hsl hcV => by
      obtain ⟨Tr, Cq, hJl⟩ := J.jpl
      exact J.hset.1 e ((hJl.typed _ hsl.isSlot).1 e b _ _ _ _ hcV)) (cslotAddr sl)
    blk call don fp ci sl buffer).toPN arI (cnode_noPre_of hlbl (by omega))

end

end

end Fl4Proofs.P3
