/-
P3 (DESIGN.md §9), IPC: **the receive after an invocation, at the mid state**
(KENTRY-PLAN.md M6, sch8 (2), toward deleting `KDispHyps.mid`): foundations.

At ReplyRecv / NBSendRecv / NBSendWait's mid state the scheduler action may be
`switchThread u` (a reply or send woke a higher-priority thread:
`possibleSwitchTo`), not only `resumeCurThread`. The receive leaves take
`Entered σ` only for (i) `CurInv` (available whenever no reschedule is
pending, `JAtZ.curInv`), (ii) `CurRun` (from `JMid` at the mid state), (iii)
the action disjunct of the blocking lemmas (`canBlockCurG`'s `hsa`) and (iv)
"no pending switch to the current thread".

* `JAtZ.curScAc`: under `CurInv`, the current thread (not idle) has the
  current SC in its SC word and that SC is active (`∈ Ac`: SCsOK.act); the
  idle SC is the idle thread's (`Inv.back`), so the current SC is not it.
* `JAtZ.canBlockCurM`: `canBlockCurG` with a third action case,
  `switchThread u` with `u ≠ ct` (l4v `scheduler_act_sane`); `CanBlock.ac`
  from `curScAc` (the current thread is not `Sch` then, so P1's `BoundInv`
  does not give it).
-/
import Fl4Proofs.P3.XTopJointRecvSig
import Fl4Proofs.P3.ScChargeJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The current SC is active and in the current thread's SC word** under
`CurInv` (module docstring). -/
theorem JAtZ.curScAc {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) :
    L.mem s (P1.scA (L.curW s)) = L.cscW s ∧ L.cscW s ∈ Ac := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS J.inv hC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  have hcsI : σ.curSc ≠ σ.idleSc := by
    intro e
    obtain ⟨y, n, hky, hyt⟩ := J.inv.back _ xt _ hkt hxs
    obtain ⟨xi, hki, hxi, -, -⟩ := J.act.2
    rw [← e] at hxi
    obtain ⟨y', n', hky', hyt'⟩ := J.inv.back _ xi _ hki hxi
    rw [hky] at hky'; cases hky'
    exact hni (Option.some.inj (hyt.symm.trans hyt'))
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hact (by rw [hpc]; exact hcsI) x n hk
  have hscS : nodeW st s Z.c layout.node.CUR_SC ∈ P1.Heap.scs H := ⟨_, (hJ.sc _ x n hsc0 hk).2⟩
  refine ⟨by rw [ecur, ecsc, hts], ?_⟩
  rw [ecsc]; exact (J.blk.2.2.2.1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))

set_option maxHeartbeats 4000000 in
/-- **P1's `CanBlock` of the current thread with a pending switch to another
thread** allowed (module docstring). -/
theorem JAtZ.canBlockCurM {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrn : Fl4Spec.runnable x.tcbState = true)
    (hti : σ.curThread ≠ σ.idleThread) (hnr : ct.bv ∉ σ.releaseQueue)
    (hsa : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ x.tcbSchedContext = none) ∨
      (∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ ct.bv))
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) :
    P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := by
  rcases hsa with h | h | ⟨u, hu, hune⟩
  · exact J.canBlockCurG ht hcur hk hrn hti hnr (Or.inl h) hnq
  · exact J.canBlockCurG ht hcur hk hrn hti hnr (Or.inr h) hnq
  have hS := J.xtop.fin.1.1.1
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have htH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct ht
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  obtain ⟨bq, br⟩ := J.curBits ht hnq' hnr
  have hsw : ∀ v, σ.schedulerAction = .switchThread v → v ≠ ct.bv := fun v hv => by
    rw [hu] at hv; cases hv; exact hune
  obtain ⟨hna, -⟩ := J.words_of_spec ht hsw (fun e => hti (by rw [hcur, e]))
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct ht
  rw [hk] at hk0; cases hk0
  have hv : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by
    rw [P1.stA_eq, ← tStA_eq]; exact hTR.st
  obtain ⟨hnb, hnrp⟩ := P1.run_word (w := L.mem s (P1.stA ct)) (by rw [hv]; exact runnable_code hrn)
  have hcw : L.curW s = ct := by
    apply P1.eq_of_bv
    rw [← hcur, hs.curThread]
    unfold P1.LawfulStore.curW nodeW; rw [hcq.cur]
  refine ⟨htH, hnb, hnrp, bq, br, hna, ?_, ?_⟩
  · intro h
    have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
      unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
    exact hti (by rw [hcur, hs.idleTh, ← ei, h])
  · obtain ⟨e1, hA⟩ := J.curScAc (J.curInv (by rw [hu]; intro e; cases e)) hti
    rw [hcw] at e1
    intro _; rw [e1]; exact hA

/-- **The mid-state entry facts of a receive** (module docstring): not the
idle thread, `CurRun` (l4v `ct_active`), and the action resumes the current
thread or switches to another one (l4v `scheduler_act_sane`; a
`chooseNewThread` mid state is a separate case). -/
def MidE (σ : Fl4Spec.State Unit) : Prop :=
  σ.curThread ≠ σ.idleThread ∧ CurRun σ ∧
    (σ.schedulerAction = .resumeCurThread ∨ ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ σ.curThread)

theorem MidE.ncn {σ : Fl4Spec.State Unit} (h : MidE σ) : σ.schedulerAction ≠ .chooseNewThread := by
  rcases h.2.2 with e | ⟨u, e, -⟩ <;> rw [e] <;> intro e' <;> cases e'

theorem MidE.run {σ : Fl4Spec.State Unit} (h : MidE σ) : CurRun σ := h.2.1

theorem MidE.sa {σ : Fl4Spec.State Unit} {t : U64} {x : Fl4Spec.Tcb} (h : MidE σ) (hcur : σ.curThread = t.bv) :
    σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ x.tcbSchedContext = none) ∨
      (∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ t.bv) := by
  rcases h.2.2 with e | ⟨u, e, hu⟩
  · exact Or.inl e
  · exact Or.inr (Or.inr ⟨u, e, by rw [← hcur]; exact hu⟩)

/-- A resumed entry is a mid state. -/
theorem JAtZ.midE {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) : MidE σ :=
  ⟨hni.1, J.curRun.run hni, Or.inl hni.2⟩

set_option maxHeartbeats 16000000 in
/-- **Receiving from an active notification at `J`** (module docstring): the
current thread at a mid state (`MidE`: resumed or a switch to another
thread pending). -/
theorem JAtZ.recvSigActiveJM (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidE σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0) (blk : Bool) (cb : Fl4Spec.Badge)
    (cr : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n blk ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := J.curInv hni.ncn
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  obtain ⟨ys, ms, hks⟩ := hC.sc
  have hrn : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCurM ht hcur hkt hrn hni.1
    (by rw [← hcur]; exact hC.notRel) (hni.sa (x := xt) hcur) hnq
  -- the badge register
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx.obj) rfl
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  have hXb := badge_wr_irel J.ip hI ht hkt (L.mem s (nBadgeA n))
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register _ hXb
  rw [hb0] at J1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk1 : (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))).kheap n.bv = some (.notification x) := by
    simp [updK, hnt, hk]
  -- the notification's state
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI J1.ip hI1.1 hn hk1 hact
  have hSch2 := hI1.2.2.1.stable hW2 hS2
  obtain ⟨Q, R, hc, hs⟩ := hSch2.lists
  obtain ⟨xt2, hkt2, -, -, hsct2, -⟩ := hs.tcb t ht
  have hkt2' : (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t.bv =
      some (.tcb (setReg xt Fl4Spec.badge_register b0)) := by
    simp [updK, hnt.symm]
  rw [hkt2'] at hkt2; cases hkt2
  have hsw : optRef (L.mem (recvActS st s t n) (P1.scA t)) = some σ.curSc := hsct2.symm.trans hscc
  have h0 : L.mem (recvActS st s t n) (P1.scA t) ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hsw; cases hsw
  have hcw : L.mem (recvActS st s t n) (P1.scA t) =
      Sched.nodeW st (recvActS st s t n) (L.cpu (recvActS st s t n)) layout.node.CUR_SC := by
    apply P1.eq_of_bv
    rw [Notif.optRef_ne h0] at hsw
    rw [Option.some.inj hsw]
    exact hs.curSc.trans (congrArg (fun q => (Sched.nodeW st (recvActS st s t n) q layout.node.CUR_SC).bv) hc.cur).symm
  have heq := spec_eq_ok (receive_signal_active_eq (arI := arI) (a := a) blk hst h0 hcw)
  -- P1's `BlkOK` after
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have p1 := P1.notification.receive_signal.ipc hAT s a t n blk Q0 R0 h0' hB0 hX0 hS0 hSg0 hcb
    (J.zH.2.2.2 n hn) (J.zH.2.2.2 n hn) (by rw [epState_eq, hst, ntfn_consts.2.2]; decide)
  rw [heq, WP.spec_ok] at p1
  simp only [WP.uncurry'_pair] at p1
  -- the notification write at `J`
  have hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := fun l h => by rw [hact] at h; cases h
  obtain ⟨σ', V', hsp', -, J2⟩ := J1.signal_badge_post hn hk1 hxw
    (y := Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) (fun l h => by cases h) rfl rfl rfl
    ⟨_, rfl, hR2, hS2, hW2, NoBlock.ntfnUpd _ _ _⟩ p1
  obtain rfl := (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hsp').1))
  -- the spec's outcome
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ =
      specRecvTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    rw [receiveSignal_cap hk]
    simp only [hact]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1)]
  have hct : σ.curSc ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  have hcn : σ.curSc ≠ n.bv := fun e => by rw [e, hk] at hks; cases hks
  rw [hspec, specRecvTail_cur hkt2' hscc (y := ys) (m := ms) (by simp [updK, hct, hcn, hks]), heq, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2⟩


end

end

end Fl4Proofs.P3
