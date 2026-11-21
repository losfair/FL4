/-
P3 (DESIGN.md §9), IPC: **`receive_signal`'s blocking receive at `J`**
(KENTRY-PLAN.md item 5, the former `JRecvSigBlockHyp` of XTopJointRecvSig): the
current thread, runnable, resumed and in no ready queue, blocks receiving on
an idle or waiting notification (`JAtZ.recvSigBlockJ`), from `JAtZ` before to
`JAtZ` after. The notification analogue of XTopJointSendBlock's
`JAtZ.sendBlockJ`.

* FL4's side: `receive_signal_blockF`, IpcNtfnBlock's `receive_signal_blockI`
  on `IRel` (`SRT` kept as `ipcSchedHyps_top` keeps it: only `stableN` and
  `scheduleTcb` are used), with the footprint `RBW`: the notification code's
  words `NWrite` (the thread's state and block words, the notification's
  words, the queue links) and the current core's action word
  (`schedule_tcb`). `maybe_return_sched_context` is a no-op when the
  notification's SC is not the thread's (`maybe_return_noop`,
  `maybeReturnSc_noop`; `hnr`). `RBW` is in `CnW` (`RBW.cnW`) and misses
  core 0's debug word (`JAtZ.rbw_dbg`).
* The spec's side: `recvSigBlock_eq` (the outcome, explicit); the frame
  `BFrN t n` (`Sk`; `t`'s TCB from a runnable state to
  `blockedOnNotification`, `n`'s notification with its SC and bound TCB
  kept) and what it keeps (as XTopJointSendBlock's `BFr`); `IK` of the step
  (`ik_recvBlock`), so `Inv` after by `InvBut.ik` with `t`'s `RelIfBound`
  carried from `Inv.rd` of a runnable thread.
* The dead set: the notification may lie in it only while covered by a cap
  (`hcov`), so it leaves the dead set (`JCovD.undead`).
* The blocking receive that gives the SC back, `jRecvSigHyp_of` and
  `dispatch_recvJS` are in XTopJointRecvSigRet.
-/
import Fl4Proofs.P3.XTopJointRecvSig
import Fl4Proofs.P3.XTopJointSendBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- FL4's `maybe_return_sched_context` when the notification has no SC or
another SC than the thread's: nothing. -/
theorem maybe_return_noop {s : S} {n t : U64}
    (h : L.mem s (nScA n) = 0#u64 ∨ L.mem s (nScA n) ≠ L.mem s (scA t)) :
    notification.maybe_return_sched_context st s n t ⦃ s' => s' = s ⦄ := by
  unfold notification.maybe_return_sched_context
  refine WP.spec_bind (Notif.obj.Ntfn.sc.spec s n) ?_
  rintro i rfl
  refine WP.spec_bind (P1.obj.Sc.is_null.spec _) ?_
  rintro b rfl
  by_cases h0 : L.mem s (nScA n) = 0#u64
  · simp [h0, WP.spec_ok]
  · rw [if_neg (by simp [h0])]
    refine WP.spec_bind (P1.obj.Tcb.sc.spec s t) ?_
    rintro i1 rfl
    rw [if_neg (h.resolve_left h0)]
    exact (WP.spec_ok _).2 rfl

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st) in
/-- **The blocking receive's footprint**: the notification code's words and
the current core's action word. -/
def RBW (N T : Set U64) (s : S) (b : U64) : Prop :=
  NWrite N T b ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION

/-- `RBW` is in `CnW`. -/
theorem RBW.cnW {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : RBW st N T s b) : CnW (st := st) T N C E R c s σ b := by
  rcases h with h | rfl
  · exact Or.inl (NWrite.finW hS.placed.tcb h)
  · obtain ⟨Q0, R0, hc0, -⟩ := hS.lists
    have hN0 := hc0.node
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [hc0.cur]
    refine Or.inl (Or.inl (KFoot.of_sfoot (Or.inr ?_)))
    exact ⟨by rw [nodeAt_val hN0 ho]; omega, by rw [nodeAt_val hN0 ho]; omega⟩

/-- The spec's `maybe_return_sc` when the notification's SC is not the
thread's: nothing. -/
theorem maybeReturnSc_noop {σ : Fl4Spec.State Unit} {n t : Fl4Spec.ObjRef} {xn : Fl4Spec.Notification}
    {xt : Fl4Spec.Tcb} (hkn : σ.kheap n = some (.notification xn)) (hkt : σ.kheap t = some (.tcb xt))
    (h : ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)) :
    Fl4Spec.maybeReturnSc (Z := Unit) n t σ = ({((), σ)}, False) := by
  unfold Fl4Spec.maybeReturnSc Fl4Spec.getTcbObjRef
  rw [nd_bind_one (Sched.getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt), Fl4Spec.NonDet.when, ite_f h]
  rfl

set_option maxHeartbeats 16000000 in
/-- **The blocking receive on `IRel`, with its footprint** (module docstring). -/
theorem receive_signal_blockF (hP : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    (hqE : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (hnr : ¬ (x.ntfnSc = xt.tcbSchedContext ∧ x.ntfnSc ≠ none))
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    notification.receive_signal st ar s a t n true ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (RBW st N T s) ⦄ := by
  obtain ⟨hR, hSR⟩ := hX
  have hx := hR.toN.at_ntfn hn hk
  have hta := hP.e.tcb t ht
  obtain ⟨xt', hkx, hxt⟩ := hR.tcb t ht
  rw [hkt] at hkx; injection hkx with hkx; injection hkx with hkx; subst hkx
  have hnm := not_member hR.toN ht hkt hnb
  -- the queue
  obtain ⟨xs, hQ, hxs, hB, hst⟩ : ∃ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs ∧
      x.ntfnObj.ntfnQueue = xs.map UScalar.bv ∧ (∀ y ∈ xs, BlockedOn (L.mem s) n y) ∧
      (stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING) := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn =>
      rw [h] at this
      exact ⟨[], this.2, rfl, by simp, Or.inl (stOf_idle (T := T) (h ▸ hx.obj) rfl)⟩
    | waitingNtfn q =>
      rw [h] at this
      obtain ⟨h1, xs, -, rfl, h2, h3⟩ := this
      exact ⟨xs, h2, rfl, h3, Or.inr (stOf_waiting (T := T) (h ▸ hx.obj) rfl)⟩
    | activeNtfn b => exact absurd h (hna b)
  have htxs : t ∉ xs := fun h => hnm n hn x hk (by rw [hxs]; exact List.mem_map_of_mem h)
  have hsorted := hsort xs hQ
  -- step 1: the state and block-object words
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnNotification n.bv }
  set σ1 := updK σ t.bv (.tcb x1)
  set s2 := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) (tBlockA t) n
  obtain ⟨hw1, hoth1⟩ := twr_wr (st := st) hP.n ht (K := 3328#u64) (Or.inl rfl) s sched.TS_BLOCKED_ON_NTFN
  obtain ⟨hw2, hoth2⟩ := twr_wr (st := st) hP.n ht (K := 3336#u64) (Or.inr (Or.inl rfl))
    (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) n
  rw [← tStA_eq] at hw1 hoth1
  rw [← tBlockA_eq] at hw2 hoth2
  have hw := hw1.trans hw2
  have hsa := (a_st hta).1
  have hba := (a_blk hta).1
  have hstv := val_st hta
  have hbl := val_blk hta
  have two : ∀ b, Aligned b → b.val ≠ t.val + 3328 → b.val ≠ t.val + 3336 → L.mem s2 b = L.mem s b := by
    intro b hb h1 h2
    show L.mem (L.wr (L.wr s _ _) _ _) b = _
    rw [wr_agree (st := st) hba b hb (by rw [hbl]; exact h2), wr_agree (st := st) hsa b hb (by rw [hstv]; exact h1)]
  have hR1 : IpcRel N T E R B (L.mem s2) σ1 := by
    refine hR.upd_tcb hP ht _ (fun b hb ⟨_, hnt⟩ => two b hb
      (fun e => hnt (Or.inl (TF.of_val (a_st hta).2 (by rw [e, hstv]))))
      (fun e => hnt (Or.inl (TF.of_val (a_blk hta).2 (by rw [e, hbl]))))) (Or.inl ⟨hnm, hqE⟩) ?_
    refine TcbRel.of_words hta hxt _ (fun b hb _ hv => two b hb (fun e => hv (Or.inl e))
        (fun e => hv (Or.inr (Or.inl e))))
      ?_ (fun e h => by cases h) (fun m hm => ?_) (Or.inr (by simp [NoEpPayload])) (fun r => ?_) rfl rfl rfl rfl
    · show (L.mem s2 (tStA t)).val = 6
      show (L.mem (L.wr (L.wr s _ _) _ _) _).val = 6
      rw [wr_agree (st := st) hba _ hsa (by rw [hbl, hstv]; omega), rd_wr_eq hsa, six_val]
    · cases hm
      show (L.mem s2 (tBlockA t)).bv = n.bv
      rw [rd_wr_eq hba]
    · rw [two _ (a_reg hta r).1 (by rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)
        (by rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega)]
      exact hxt.regs r
  have hK1 : NtfnStep σ σ1 := NtfnStep.tcb hkt (.blockedOnNotification n.bv) xt.tcbArch
  have hW1 := hw.foot
  have hSR1 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s2 σ1 :=
    ⟨hSR.1.stableN hSR.2.1.placed hW1 hK1, hSR.2.1.stable hW1 hK1, hSR.2.2.mono hW1.1 (SzKeep.ntfnStep hK1)⟩
  set σ2 := stsAct σ1 t.bv
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk2 : σ2.kheap n.bv = some (.notification x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  -- the action word of a state with `s`'s kernel base and core
  have hactW : ∀ s' : S, L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      Aligned (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) ∧
        RBW st N T s (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) := by
    intro s' hk' hc'
    obtain ⟨Q0, R0, hc0, -⟩ := hSR.2.1.lists
    have hN0 := hc0.node
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [nodeAt_ksb hk', hc']
    refine ⟨?_, Or.inr rfl⟩
    rw [hc0.cur]
    exact nodeAt_aligned hN0 ho (by simp [layout.node.SCHED_ACTION])
  -- step 2: `schedule_tcb`
  have key : (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
      let s2 ← obj.Tcb.set_block_obj st t s1 n
      let s3 ← sched.schedule_tcb st s2 t
      let s4 ← notification.ntfn_append st s3 n t
      let s5 ← notification.maybe_return_sched_context st s4 n t
      ok (s5, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (RBW st N T s) ⦄ := by
    step
    step
    subst s1_post s2_post
    refine WP.spec_bind (WP.spec_and ((ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c)
      hP.e).scheduleTcb _ σ1 t hR1.toE (ScRelM.of hR1) hSR1 ht) (schedule_tcb_cases _ t)) ?_
    rintro s3 ⟨⟨hf3, hS3⟩, hc3⟩
    have hF3 : WritesIn st s s3 (RBW st N T s) := by
      rcases hc3 with rfl | rfl
      · exact hW1.mono fun b hb => Or.inl hb
      · refine (hW1.trans ((writesIn_wr (hactW _ hW1.1 hW1.2.1).1).mono fun b hb =>
          hb ▸ (hactW _ hW1.1 hW1.2.1).2)).mono fun b hb => hb.elim (fun h => Or.inl h) id
    have hR3 : IpcRel N T E R B (L.mem s3) σ2 := hR1.frame hP hf3 (IKView.stsAct _ _)
    obtain ⟨xs3, hQ3, hxs3, hB3⟩ := (hR3.toN.at_ntfn hn hk2).obj.queue
    have e3 : xs3 = xs := by
      rw [hxs] at hxs3
      exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs3).symm
    subst e3
    have hxt3 := hR3.toN.at_tcb ht hkt2
    -- priorities agree with those of `s`
    have hpr : ∀ y ∈ xs3, L.mem s3 (prioA y) = L.mem s (prioA y) := by
      intro y hy
      have hyT := hQ.mem y hy
      have hyt : y ≠ t := fun e => htxs (e ▸ hy)
      have hyA := hP.e.tcb y hyT
      exact (hf3 _ (a_prio hyA).1 (EFoot.ifoot (Or.inr (Or.inr (Or.inl ⟨y, hyT, Or.inl (a_prio hyA).2⟩))))).trans
        (hw.tcb y hyT hyt).prio
    have hsorted3 : PrioSorted (fun y => L.mem s3 (prioA y)) xs3 := prioSorted_congr hsorted hpr
    refine WP.spec_bind (ntfn_append_full hP.n s3 hn t xs3 hQ3 ht htxs) ?_
    rintro s4 ⟨hA1, hA2, hA3⟩
    set ys := insPrio (fun y => L.mem s3 (prioA y)) (L.mem s3 (prioA t)) t xs3
    have hblk3 : L.mem s3 (tBlockA t) = n := eq_of_bv (hxt3.blk n.bv rfl)
    have hR4 : IpcRel N T E R B (L.mem s4)
        (updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })) := by
      have hx2 := hR3.toN.at_ntfn hn hk2
      have hbw : ∀ w ∈ t :: xs3, w ∈ T ∧ L.mem s3 (tBlockA w) = n := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact ⟨ht, hblk3⟩
        · exact ⟨hQ.mem w hw, (hB3 w hw).2⟩
      refine hR3.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
          (fun w hw => by
            obtain ⟨hwT, hwb⟩ := hbw w hw
            have hwa := hP.e.tcb w hwT
            exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
              fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
          (fun e => hnw (e ▸ (nw_words hP hn).1)) (fun e => hnw (e ▸ (nw_words hP hn).2.1)))
        ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨hA2, ys, insPrio_ne_nil hsorted3, rfl, hA1, fun y hy => ?_⟩
        have hyT : y ∈ T := by
          rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
          · exact ht
          · exact hQ.mem y hy'
        have e := hA3.tcb y hyT
        rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
        · exact ⟨by rw [e.st, hxt3.st]; rfl, by rw [e.blk]; exact hblk3⟩
        · exact ⟨by rw [e.st]; exact (hB3 y hy').1, by rw [e.blk]; exact (hB3 y hy').2⟩
      · show x.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
      · rw [hA3.bound]; exact hx2.bound_mem
      · show x.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
    -- the spec
    have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Notif.prioOf σ2 y := by
      intro y hy
      have hy' : y ∈ x.ntfnObj.ntfnQueue := hy
      rw [hxs] at hy'
      obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy'
      obtain ⟨z, hz, -⟩ := hR3.toN.tcb y' (hQ.mem y' hy'x)
      exact ⟨z, hz, by simp [Notif.prioOf, hz]⟩
    have hlist : specIns (Fl4Spec.ntfnQueueOf x) (Notif.prioOf σ2) x1.tcbPriority t.bv = ys.map UScalar.bv := by
      have hq' : Fl4Spec.ntfnQueueOf x = xs3.map UScalar.bv := hxs
      rw [specIns, hq', List.takeWhile_map, List.dropWhile_map]
      simp only [ys, insPrio_eq_sorted _ _ t xs3 hsorted3, List.map_append, List.map_cons]
      have hc : ∀ y ∈ xs3, ((fun y => @decide (Notif.prioOf σ2 y ≥ x1.tcbPriority) (Classical.propDecidable _)) ∘
          UScalar.bv) y =
          (fun y => !decide (L.mem s3 (prioA t) > L.mem s3 (prioA y))) y := by
        intro y hy
        obtain ⟨z, hz, hzr⟩ := hR3.toN.tcb y (hQ.mem y hy)
        have hpz : Notif.prioOf σ2 y.bv = z.tcbPriority := by simp [Notif.prioOf, hz]
        simp only [Function.comp, hpz]
        convert (prio_ge_iff _ _ _ _ hxt3.prio hzr.prio).symm using 2
      rw [takeWhile_congr' hc, dropWhile_congr' hc]
    set σ3 := updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })
    have hk3 : σ3.kheap n.bv = some (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) := by
      simp [σ3, updK]
    have hkt3 : σ3.kheap t.bv = some (.tcb x1) := by simp [σ3, updK, Ne.symm hnt, hkt2]
    have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ =
        Fl4Spec.maybeReturnSc n.bv t.bv σ3 := by
      rw [receiveSignal_notActive hk hna]
      unfold Fl4Spec.receiveSignalBlocked
      simp only [↓reduceIte]
      rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (tcbNtfnAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq), hlist]
    have hK4 : NtfnStep σ2 σ3 :=
      NtfnStep.ntfn (y := { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) hk2 rfl rfl
    have hW4 := hA3.foot
    have hSR4 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s4 σ3 :=
      ⟨hS3.1.stableN hS3.2.1.placed hW4 hK4, hS3.2.1.stable hW4 hK4, hS3.2.2.mono hW4.1 (SzKeep.ntfnStep hK4)⟩
    -- `maybe_return_sched_context`: nothing
    have hwn : L.mem s4 (nScA n) = 0#u64 ∨ L.mem s4 (nScA n) ≠ L.mem s4 (scA t) := by
      have hsN : x.ntfnSc = optRef (L.mem s4 (nScA n)) := (hR4.toN.at_ntfn hn hk3).sc
      obtain ⟨Q4, R4, -, hs4⟩ := hSR4.2.1.lists
      obtain ⟨xt4, hkt4, -, -, hsct4, -⟩ := hs4.tcb t ht
      rw [hkt3] at hkt4; cases hkt4
      by_cases h0 : L.mem s4 (nScA n) = 0#u64
      · exact Or.inl h0
      · refine Or.inr fun e => hnr ⟨?_, ?_⟩
        · rw [hsN, e]; exact hsct4.symm
        · rw [hsN, Notif.optRef_ne h0]; simp
    refine WP.spec_bind (Sched.maybe_return_noop hwn) ?_
    rintro s5 rfl
    simp only [WP.spec_ok]
    refine ⟨by simp, σ3, by rw [hspec]; exact maybeReturnSc_noop hk3 hkt3 hnr, ⟨hR4, hSR4⟩, ?_⟩
    exact (hF3.trans (hW4.mono fun b hb => (Or.inl hb : RBW st N T s b))).mono fun b hb => hb.elim id id
  unfold notification.receive_signal
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with hst | hst
  · rw [hst, if_pos rfl, if_pos rfl]
    exact key
  · rw [hst, if_neg (by rw [ntfn_consts.1, ntfn_consts.2.1]; decide), if_pos rfl, if_pos rfl]
    exact key

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **One object's change by the blocking receive**: `t`'s TCB from a
runnable state to `blockedOnNotification`, or `n`'s notification with its SC
and bound TCB kept. -/
def BChgN (t n p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x m, o = .tcb x ∧ o' = .tcb { x with tcbState := .blockedOnNotification m } ∧ p = t ∧
    runnable x.tcbState = true) ∨
  (∃ x y, o = .notification x ∧ o' = .notification y ∧ p = n ∧ y.ntfnSc = x.ntfnSc ∧
    y.ntfnBoundTcb = x.ntfnBoundTcb)

/-- **The spec's frame of the blocking receive** (module docstring). -/
structure BFrN (t n : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ BChgN t n p o o'

theorem BChgN.objFrK {t n p : ObjRef} {o o' : KernelObject} (h : BChgN t n p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, rfl, rfl, -, -⟩ | ⟨_, _, rfl, rfl, -, -, -⟩
  · exact IpcFrKeep.objFrK_tcb rfl rfl
  · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

/-- The blocking receive keeps what the IPC-buffer fields read. -/
theorem BFrN.ipcFr {t n : ObjRef} {σ σ' : State Unit} (F : BFrN t n σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK

section
variable {t n : ObjRef} {σ σ' : State Unit}

/-- A TCB's change: kept, or `t`'s, runnable, to `blockedOnNotification`. -/
def TKbN (t p : ObjRef) (x : Tcb) (st : ThreadState) : Prop :=
  st = x.tcbState ∨ (p = t ∧ runnable x.tcbState = true ∧ ∃ m, st = .blockedOnNotification m)

theorem TKbN.run {p : ObjRef} {x : Tcb} {st : ThreadState} (h : TKbN t p x st) (hr : runnable x.tcbState = false) :
    st = x.tcbState := by
  rcases h with h | ⟨-, h, -⟩
  · exact h
  · rw [hr] at h; cases h

theorem BFrN.tcbF (h : BFrN t n σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st, σ'.kheap p = some (.tcb { x with tcbState := st }) ∧ TKbN t p x st := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', m, e1, rfl, hp', hr⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨_, h2, Or.inr ⟨hp', hr, m, rfl⟩⟩

theorem BFrN.tcbB (h : BFrN t n σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st, σ.kheap p = some (.tcb x) ∧ y = { x with tcbState := st } ∧ TKbN t p x st := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, by rw [← h1, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, m, rfl, e2, hp', hr⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, _, h1, rfl, Or.inr ⟨hp', hr, m, rfl⟩⟩

/-- The other kinds kept. -/
theorem BFrN.othF (h : BFrN t n σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h4 : ∀ x, o ≠ .notification x) : σ'.kheap p = some o := by
  rcases h.kh p with e' | ⟨o0, o', k1, k2, hc⟩
  · rw [e', hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h4 _)

theorem BFrN.othB (h : BFrN t n σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h4 : ∀ x, o' ≠ .notification x) : σ.kheap p = some o' := by
  rcases h.kh p with e' | ⟨o, o'', k1, k2, hc⟩
  · rw [← e', hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h4 _)

theorem BFrN.scF (h : BFrN t n σ σ') {p : ObjRef} {y : SchedContext} {m : Nat}
    (hp : σ.kheap p = some (.schedContext y m)) : σ'.kheap p = some (.schedContext y m) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrN.scB (h : BFrN t n σ σ') {p : ObjRef} {y : SchedContext} {m : Nat}
    (hp : σ'.kheap p = some (.schedContext y m)) : σ.kheap p = some (.schedContext y m) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrN.replyF (h : BFrN t n σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrN.replyB (h : BFrN t n σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrN.epF (h : BFrN t n σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    σ'.kheap p = some (.endpoint x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFrN.epB (h : BFrN t n σ σ') {p : ObjRef} {x : Endpoint} (hp : σ'.kheap p = some (.endpoint x)) :
    σ.kheap p = some (.endpoint x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

/-- The notifications: kept, or `n`'s with its SC and bound TCB. -/
def NKb (n p : ObjRef) (x y : Notification) : Prop :=
  y = x ∨ (p = n ∧ y.ntfnSc = x.ntfnSc ∧ y.ntfnBoundTcb = x.ntfnBoundTcb)

theorem NKb.sc {n p : ObjRef} {x y : Notification} (h : NKb n p x y) : y.ntfnSc = x.ntfnSc := by
  rcases h with rfl | ⟨-, h, -⟩
  · rfl
  · exact h

theorem NKb.bound {n p : ObjRef} {x y : Notification} (h : NKb n p x y) : y.ntfnBoundTcb = x.ntfnBoundTcb := by
  rcases h with rfl | ⟨-, -, h⟩
  · rfl
  · exact h

theorem BFrN.ntfnF (h : BFrN t n σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ NKb n p x y := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, e1, -⟩ | ⟨x', y, e1, rfl, hp', hs, hb⟩ <;> cases e1
    exact ⟨y, h2, Or.inr ⟨hp', hs, hb⟩⟩

theorem BFrN.ntfnB (h : BFrN t n σ σ') {p : ObjRef} {y : Notification} (hp : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ NKb n p x y := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← h1, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hp', hs, hb⟩ <;> cases e2
    exact ⟨x, h1, Or.inr ⟨hp', hs, hb⟩⟩

theorem BFrN.kind (h : BFrN t n σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e', ho], rfl⟩, fun o' ho => ⟨o', by rw [← e', ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, m, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

theorem BFrN.szKeep (h : BFrN t n σ σ') : SzKeep σ σ' := fun _ y m hp => ⟨y, h.scB hp⟩

theorem BFrN.ykeep (h : BFrN t n σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y m hp => ⟨y, h.scF hp, rfl⟩, fun p z m hp => ⟨z, h.scB hp, rfl⟩⟩
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFrN.mcpKeep (h : BFrN t n σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFrN.bufKeep (h : BFrN t n σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFrN.prio (h : BFrN t n σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  unfold Sched.prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  cases hk : σ.kheap u with
  | some o =>
    cases o with
    | tcb x =>
      obtain ⟨st, hk', -⟩ := h.tcbF hk
      rw [hk']; rfl
    | _ =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
        | _ => rfl
  | none =>
    cases hk' : σ'.kheap u with
    | none => rfl
    | some o' => cases o' with
      | tcb y => obtain ⟨x, -, hx, -⟩ := h.tcbB hk'; rw [hk] at hx; cases hx
      | _ => rfl

theorem BFrN.nsc {N C : Set U64} (h : BFrN t n σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro q hq y p hy hp
  obtain ⟨x, hx, hc⟩ := h.ntfnB hy
  exact hN q hq x p hx (hc.sc ▸ hp)

theorem BFrN.own {T C : Set U64} (h : BFrN t n σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y m hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y m (h.scB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y m hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y m (h.scB hy)

theorem BFrN.off (h : BFrN t n σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y m hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy; rw [h.sk.csc, h.sk.isc] at ha
  exact hO hc y m (h.scB hy) ha

theorem BFrN.idleOK (h : BFrN t n σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st }, by rw [h.sk.idle]; exact hx', by rw [h.sk.isc]; exact h1, ?_,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.run (by rw [h2]; rfl)]; exact h2

/-- `BlockedScActive` after, `t`'s SCs active. -/
theorem BFrN.bsa (h : BFrN t n σ σ') (hB : BlockedScActive σ)
    (ht : ∀ p y m, σ.kheap p = some (.schedContext y m) → y.scTcb = some t → scActive y = true) :
    BlockedScActive σ' := by
  refine ⟨fun p z m u y hp hyt hy hq => ?_, fun p z m hp hr => hB.replies p z m (h.scB hp) hr⟩
  obtain ⟨x, st, hx, rfl, hs⟩ := h.tcbB hy
  rcases hs with rfl | ⟨rfl, -, -⟩
  · exact hB.tcb p z m u x (h.scB hp) hyt hx hq
  · exact ht p z m (h.scB hp) hyt

/-- `IpcSorted` after, `n`'s queue sorted. -/
theorem BFrN.isorted (h : BFrN t n σ σ') (hS : IpcSorted σ)
    (hn : ∀ y, σ'.kheap n = some (.notification y) → SortedQ σ y.ntfnObj.ntfnQueue) : IpcSorted σ' := by
  refine ⟨fun p y hp => (hS.1 p y (h.epB hp)).congr fun u _ => h.prio u, fun p y hp => ?_⟩
  obtain ⟨x, hx, hc⟩ := h.ntfnB hp
  rcases hc with rfl | ⟨rfl, -, -⟩
  · exact (hS.2 p y hx).congr fun u _ => h.prio u
  · exact (hn y hp).congr fun u _ => h.prio u

theorem BFrN.kback (h : BFrN t n σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e' | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e', ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, m, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem BFrN.ksz (h : BFrN t n σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e'⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e'.symm⟩

theorem BFrN.ksub (h : BFrN t n σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e' | ⟨ko, ko', h1, -, -⟩
    · rw [e']; exact hn
    · rw [hn] at h1; cases h1

theorem BFrN.callKeep (h : BFrN t n σ σ') :
    (∀ q y m, σ.kheap q = some (.schedContext y m) → ∃ y', σ'.kheap q = some (.schedContext y' m) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x m, σ'.kheap p = some (.schedContext x m) → ∃ x0, σ.kheap p = some (.schedContext x0 m)) :=
  ⟨fun q y m hq => ⟨y, h.scF hq, rfl⟩, fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x m hp => ⟨x, h.scB hp⟩⟩

theorem BFrN.skeep (h : BFrN t n σ σ') : Ipc.SKeep σ σ' := by
  refine ⟨h.sk.rel, h.sk.tm, fun p y hy => ?_, fun p y m hy => h.scB hy⟩
  obtain ⟨x, st, hx, rfl, -⟩ := h.tcbB hy
  exact ⟨x, hx, rfl⟩

theorem BFrN.khrb (h : BFrN t n σ σ') : KhRB σ σ' :=
  KhRB.of_kh h.kh fun p o o' hc => by
    rcases hc with ⟨x, m, rfl, rfl, -, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ObjRB.tcb (Or.inr rfl)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)

end

/-- **The spec's blocking receive in `BFrN`** (module docstring), the
notification's SC not the thread's. -/
theorem recvSigBlock_eq {σ : State Unit} {t n : ObjRef} {xt : Tcb} {x : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hk : σ.kheap n = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (htq : t ∉ ntfnQueueOf x) (hq : ∀ y ∈ ntfnQueueOf x, ∃ z, σ.kheap y = some (.tcb z))
    (hr : runnable xt.tcbState = true) (hS : SortedQ σ (ntfnQueueOf x))
    (hnr : ¬ (x.ntfnSc = xt.tcbSchedContext ∧ x.ntfnSc ≠ none)) (cb : Badge) (rt : CapRights) :
    ∃ σ', receiveSignal (Z := Unit) t (.notificationCap n cb rt) true σ = ({((), σ')}, False) ∧ BFrN t n σ σ' ∧
      IK t σ σ' ∧ σ'.readyQueues = σ.readyQueues ∧
      (t = σ.curThread → σ.schedulerAction = .resumeCurThread → σ'.schedulerAction = .chooseNewThread) ∧
      (∀ y, σ'.kheap n = some (.notification y) → SortedQ σ y.ntfnObj.ntfnQueue) := by
  let x1 : Tcb := { xt with tcbState := .blockedOnNotification n }
  let σ2 := stsAct (updK σ t (.tcb x1)) t
  let q' := Notif.specIns (ntfnQueueOf x) (Sched.prioOf σ2) x1.tcbPriority t
  let y : Notification := { x with ntfnObj := .waitingNtfn q' }
  let σ' := updK σ2 n (.notification y)
  have htn : t ≠ n := by rintro rfl; rw [hkt] at hk; cases hk
  have hk2 : σ2.kheap n = some (.notification x) := by simp [σ2, stsAct_kheap, Ne.symm htn, hk]
  have hkt2 : σ2.kheap t = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  have hq2 : ∀ y ∈ ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Sched.prioOf σ2 y := by
    intro y hy
    obtain ⟨z, hz⟩ := hq y hy
    have hyt : y ≠ t := fun h => htq (h ▸ hy)
    have hz2 : σ2.kheap y = some (.tcb z) := by simp [σ2, stsAct_kheap, hyt, hz]
    exact ⟨z, hz2, (prioOf_eq hz2).symm⟩
  have heq : receiveSignal (Z := Unit) t (.notificationCap n cb rt) true σ = ({((), σ')}, False) := by
    rw [receiveSignal_notActive hk hna]
    unfold receiveSignalBlocked
    simp only [↓reduceIte]
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (tcbNtfnAppend_eq hk2 hkt2 (Sched.prioOf σ2) hq2)]
    exact Ipc.maybeReturnSc_noop (xn := y) (xt := x1)
      (by show (updK σ2 n (.notification y)).kheap n = _; rw [updK_kheap, Function.update_self]) (by simp [σ', updK, htn, hkt2]) hnr
  have hkh : ∀ p, σ'.kheap p = if p = n then some (.notification y)
      else if p = t then some (.tcb x1) else σ.kheap p := by
    intro p
    simp only [σ', σ2, updK_kheap, stsAct_kheap, Function.update_apply]
  have hrq : σ'.readyQueues = σ.readyQueues := by
    show (stsAct _ t).readyQueues = _
    unfold stsAct; split <;> rfl
  have hrl : σ'.releaseQueue = σ.releaseQueue := by
    show (stsAct _ t).releaseQueue = _
    unfold stsAct; split <;> rfl
  have htm : σ'.curTime = σ.curTime := by
    show (stsAct _ t).curTime = _
    unfold stsAct; split <;> rfl
  have hsk : Sk σ σ' := by
    show Sk σ (updK (stsAct _ t) n _)
    unfold stsAct; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpr2 : ∀ u, Sched.prioOf σ2 u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = t
    · subst hut; exact (prioOf_eq hkt2).trans (prioOf_eq hkt).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
      simp only [σ2, stsAct_kheap, updK_kheap, Function.update_apply, if_neg hut]
  refine ⟨σ', heq, ⟨hsk, fun p => ?_⟩, ⟨fun p => ?_, hrq, hrl, htm⟩, hrq, fun hct hres => ?_, fun y' hy => ?_⟩
  · rw [hkh]
    by_cases hpn : p = n
    · rw [if_pos hpn]
      exact Or.inr ⟨.notification x, .notification y, by rw [hpn]; exact hk, rfl,
        Or.inr ⟨x, y, rfl, rfl, hpn, rfl, rfl⟩⟩
    · rw [if_neg hpn]
      by_cases hpt : p = t
      · rw [if_pos hpt]
        exact Or.inr ⟨.tcb xt, .tcb x1, by rw [hpt]; exact hkt, rfl, Or.inl ⟨xt, n, rfl, rfl, hpt, hr⟩⟩
      · rw [if_neg hpt]; exact Or.inl rfl
  · rw [hkh]
    by_cases hpn : p = n
    · rw [if_pos hpn, hpn, hk]
      exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => by cases e; exact ⟨_, rfl, rfl⟩,
        fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => by cases e; exact ⟨_, rfl⟩⟩
    · rw [if_neg hpn]
      by_cases hpt : p = t
      · rw [if_pos hpt, hpt, hkt]
        exact ⟨fun _ e => by cases e; exact ⟨_, rfl, rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩,
          fun _ _ e => (by cases e), fun _ e => (by cases e), fun _ e => by cases e; exact ⟨_, rfl⟩,
          fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
      · rw [if_neg hpt]; exact OIK.refl _ _
  · have hns : ¬ schedulable t (updK σ t (.tcb x1)) = true := by
      intro hs
      obtain ⟨y, -, -, -, hy, -, hrun, -⟩ := schedulable_inv hs
      rw [updK_kheap, Function.update_self] at hy
      cases hy
      simp [x1, runnable] at hrun
    show (stsAct _ t).schedulerAction = _
    unfold stsAct
    rw [if_pos ⟨hct, hres, hns⟩]
  · rw [hkh, if_pos rfl] at hy
    cases hy
    exact (sortedQ_specIns (hS.congr fun u _ => hpr2 u) t (prioOf_eq hkt2)).congr fun u _ => (hpr2 u).symm

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- `RBW` misses core 0's debug word: no TCB or notification word, and the
action word is another node word (`JKern.dwNe`). -/
theorem JAtZ.rbw_dbg (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hW : P1.WritesIn st s s' (RBW st Z.N Z.T s)) :
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
  have hT := J.xtop.fin.1.1.1.placed.tcb
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk 0#u64 J.kern.cs0
  have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp)
  have hd88 : layout.node.DEBUG_TCBS.val = 88 := P1.debug_val
  refine hW.mem_eq J.kern.dwAl fun hb => ?_
  rcases hb with hb | hb
  · rcases NWrite.iwords (E := Z.E) (R := Z.R) (B := Z.B) hT hb with ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ |
      ⟨r, hr, g1, g2⟩ | ⟨m, hm, g1, g2⟩ | ⟨wp, hwp, g1, g2⟩
    · have := J.kern.hnd t _ (J.zH.1 t ht) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd e _ (J.zH.2.1 e he) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd r _ (J.zH.2.2.1 r hr) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd m _ (J.zH.2.2.2 m hm) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.nodeB wp hwp 0#u64 (by simp); omega
  · exact J.kern.dwNe.2 (congrArg UScalar.val hb)

/-- **`RBW` keeps every debug word** (KENTRY-PLAN g2i; `rbw_dbg`'s `DbgKeep`):
a notification step's word (`nwrite_notDbg`) or the current node's action
word (apart from the TCBs, `JKern.hnd`; another offset than the debug head). -/
theorem JAtZ.rbw_dbgKeep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hW : P1.WritesIn st s s' (RBW st Z.N Z.T s)) : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
  dbgKeep_of_writes J.blk hW fun b hb => by
    rcases hb with hb | rfl
    · exact J.nwrite_notDbg hb
    · have hcC : L.cpu s ∈ Cs := J.kern.cpuCs
      have hN : P1.NodePlaced st (P1.Heap.tcbs H) s (L.cpu s) := P1.TInv.nodes J.blk _ hcC
      have hsa : (layout.node.SCHED_ACTION).val < 4288 ∧ (layout.node.SCHED_ACTION).val ≠ 88 := by
        simp [layout.node.SCHED_ACTION]
      have hv := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) hsa.1
      have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
      refine J.notDbg' (fun p hp => ?_) (fun c hc => ?_)
      · have := J.kern.hnd p _ hp _ hcC
        simp only [P1.HKind.bits] at this ⊢
        omega
      · have h1 := J.kern.csLt c hc
        have h2 := J.kern.csLt _ hcC
        rw [hv, hnb, hnb]
        omega

set_option maxHeartbeats 16000000 in
/-- **The blocking receive at `J`** (module docstring): the current thread
`t`, resumed and in no ready queue, blocks receiving on the idle or waiting
notification `n`, covered by a cap (`hcov`), whose SC is not the current SC
(`hnr`; otherwise `maybe_return_sched_context` gives it back). -/
theorem JAtZ.recvSigBlockJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (hnr : x.ntfnSc ≠ some σ.curSc)
    (hcov : (∀ k, Z.th n = some k → Covered (L.mem s) Z.G n.val (n.val + max (objSize k) 1)) ∧
      (∀ k, H n = some k → Covered (L.mem s) Z.G n.val (n.val + 2 ^ k.bits)))
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hres : σ.schedulerAction = .resumeCurThread := hni.2
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  have hr : Fl4Spec.runnable xt.tcbState = true := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
  have hnr' : ¬ (x.ntfnSc = xt.tcbSchedContext ∧ x.ntfnSc ≠ none) := fun h => hnr (h.1.trans hscc)
  have hnb3 : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    rcases runnable_code hr with h | h | h <;> rw [h] <;> decide
  have hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by rw [h] at hr; cases hr
  have hqE : ∀ e ∈ Z.E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue :=
    fun e he z hz => Endp.not_queued hI.1.toE ht hkt hnb3 e he z hz
  have hnqN : t.bv ∉ Fl4Spec.ntfnQueueOf x := not_member hI.1.toN ht hkt hnn n hn x hk
  have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ.kheap y = some (.tcb z) := fun y hy => by
    obtain ⟨z, hz, -⟩ := (J.sv.ntfnQ _ _ hk).2 y hy
    exact ⟨z, hz⟩
  obtain ⟨σ', heq, F, hik, -, hcn, hsrt⟩ := recvSigBlock_eq hkt hk hna hnqN hq hr (J.isorted.2 _ _ hk) hnr' cb rt
  have hcn' : σ'.schedulerAction = .chooseNewThread := hcn hcur.symm hres
  -- P1's `BlkOK` after
  have hcb := J.canBlockCur ht hcur hkt hr hni hnq
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have hx := hI.1.toN.at_ntfn hn hk
  have hst0 : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := Z.T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := Z.T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  have h3 : L.epState s n ≠ 3#u64 := by
    rw [epState_eq]
    rcases hst0 with h | h
    · rw [h, ntfn_consts.1]; decide
    · rw [h, ntfn_consts.2.1]; decide
  have p1 := P1.notification.receive_signal.ipc hAT s a t n true Q0 R0 h0 hB0 hX0 hS0 hSg0 hcb
    (J.zH.2.2.2 n hn) (J.zH.2.2.2 n hn) h3
  refine WP.spec_mono (WP.spec_and (receive_signal_blockF (ar := arI) J.ip s a σ hI ht hkt hnn hqE hn hk hna
    (J.qsortedN n hn) hnr' cb rt) p1) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, σ0, h0eq, hIR, hRB⟩, hbk⟩
  simp only [WP.uncurry'_pair] at ea hbk hIR hRB
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  have hblk := hbk
  have hW : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hRB.mono fun b hb => RBW.cnW hS hb
  have hDbg := J.rbw_dbg hRB
  -- the assembly (as XTopJointSendBlock's `JAtZ.sendBlockJ`)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := ⟨fun u hu => (by rw [hcn'] at hu; cases hu), F.idleOK J.act.2⟩
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcn'
  have hrun3 : CurRunM σ' := Or.inl (by rw [hcn']; intro h; cases h)
  -- the dead: the thread is not dead (runnable); the notification leaves the dead set
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rcases runnable_code hr with h | h | h <;> rw [h] <;> decide)
  have hdead : ∀ q ∈ D \ {n}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ t.bv := htD q hq.1
    have hqn : q.bv ≠ n.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ?_) (fun x hx => F.epF hx) (fun x hx => ?_)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1 (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
      show st' = x.tcbState
      rcases hs' with e1 | ⟨e1, -⟩
      · exact e1
      · exact absurd e1 hqt
    · obtain ⟨y, hy, hc'⟩ := F.ntfnF hx
      rcases hc' with rfl | ⟨e1, -⟩
      · exact ⟨_, hy, Or.inl rfl, rfl, Or.inl rfl⟩
      · exact absurd e1 hqn
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {n})
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {n}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the thread's `RelIfBound` from a runnable state)
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, by rw [← hcur]; exact hC.notRel⟩
  obtain ⟨hIB, -⟩ := (J.inv.toBut t.bv).ik hnqT hik
  have hrib : RelIfBound σ' t.bv := Ipc.RelIfBound.of_keep (J.inv.rd t.bv xt hkt (Or.inl hr)) F.skeep
  have I3 : Inv σ' := hIB.inv fun _ _ _ => hrib
  -- `BlockedScActive`: the thread's SC is the current SC, active
  have hscA : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp).2⟩
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp hyt
    rw [hkt] at hku; cases hku
    have e1 : σ.curSc = q.bv := Option.some.inj (hscc.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {n}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted hsrt, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J3 := J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R
    (J.rbw_dbgKeep hRB) F.sk.orig (XTopAt.idleW_eqS J.xtop hX3 F.sk.idle) (J.zD_diffN hn)
  rw [heq]
  exact ⟨_, Set.mem_singleton _, J3.xtop.relTop, _, _, _, _, _, _, J3⟩


end

end

end Fl4Proofs.P3
