/-
P3 (DESIGN.md §9), IPC: **`send_ipc`'s blocking send at `J`** (toward
XTopJointIpcJ's `JSendRestHyp`): the current thread, `Restart` after the
caller's restart and in no ready queue, blocks sending on an idle or sending
endpoint (`JAtZ.sendBlockJ`), from `JAtZ` before to `JAtZ` after.

* FL4's side: `send_ipc_blockF`, IpcEpBlock's `send_ipc_block_i` on `IRel`
  (only `IpcCore`'s `stableE`/`scheduleTcb` are used: `ipcCore_top`), with
  the footprint `CnW`: the thread's state, blocking object, badge and flags
  words, `schedule_tcb`'s action word, `ep_append`'s endpoint words and
  queue links. P1's `BlkOK` after (`endpoint.send_ipc.block`) and footprint
  `KW` (`endpoint.send_ipc.blockFoot`) from P1's `CanBlock` (`canBlockP1`:
  the thread's state word, `Restart`; not queued, from the spec by the
  scheduler relation; not in the release queue, `CurInv.notRel`; the action
  resume, `Entered`; not idle; its SC active, `BoundInv.sact`).
* The spec's side: `sendIpcBlock_eq` (the outcome, explicit); the frame
  `BFr t e` (`Sk`, `t`'s TCB from a runnable state to `blockedOnSend`,
  `e`'s endpoint queue grown by `t`) and what it keeps (as IpcCancelFr's
  `KFr`); `Inv` after by `InvBut.ik` (`ikm_sendIpcBlocked`; `t`'s
  `RelIfBound` carried from `Inv.rd` of `Restart`); `BlockedScActive` with
  `t`'s SC active (`CurInv.active`, `t` not idle); `IpcSorted` by
  `sortedQ_specIns`; `CurInv` and `CurRunM` hold through the pending
  reschedule (`stsAct`: `t` current, resumed, no longer schedulable).
* The dead set: the endpoint may lie in it only while covered by a cap (the
  invoked cap, ScDeadStep's `JAtZ.cover_cap`), so it leaves the dead set
  (`JCovD.undead`); every other dead object is kept (`JAtZ.deadP_keep`).
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.XTopJointCancel
import Fl4Proofs.P3.IpcCapJ
import Fl4Proofs.P3.IpcEpBlock
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 16000000 in
/-- **The blocking send on `IRel`, with its footprint** (module docstring). -/
theorem send_ipc_blockF (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (call : Bool) (badge : U64) (g gr d : Bool) :
    endpoint.send_ipc st ar s a true call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (CnW (st := st) T N C E R c s σ) ⦄ := by
  have hH0 := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e
  have hH := hH0.epHyps hP0
  have hP := hP0.e
  obtain ⟨hRI, hSRT⟩ := hX
  have hSchR : SchedRel st N T C c s σ := hSRT.2.1
  obtain ⟨Q0, R0, hc0, -⟩ := hSchR.lists
  have hR := hRI.toE
  have hN := hRI.toN
  have hSR : SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ := ⟨hSRT, ScRelM.of hRI⟩
  have hqn := not_member hN ht hkt hnn
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hq := not_queued hR ht hkt hnb
  have htq : t.bv ∉ x.epQueue := hq e he x hk
  set d' : Fl4Spec.SenderPayload :=
    { senderBadge := badge.bv, senderCanGrant := g, senderCanGrantReply := gr, senderIsCall := call }
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnSend e.bv d' }
  set σ1 := updK σ t.bv (.tcb x1)
  set f := ((if g then endpoint.FLAG_GRANT else 0#u64) ||| (if gr then endpoint.FLAG_GRANT_REPLY else 0#u64)) |||
      (if call then endpoint.FLAG_CALL else 0#u64) with hf
  set s4 := L.wr (L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_SEND) (tBlockA t) e) (tBadgeA t) badge)
      (tFlagsA t) f
  obtain ⟨hA4, r1, r2, r3, r4, hW4⟩ := block_send_writes (L := L) hP s ht e badge f
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_badge hta; have v4 := val_flags hta
  -- the footprint of the four field writes
  have hF4 : WritesIn st s s4 (CnW (st := st) T N C E R c s σ) := by
    refine ⟨hW4.1, hW4.2.1, fun b hb hn => hA4 b hb ⟨fun h => hn ?_, fun h => hn ?_, fun h => hn ?_,
      fun h => hn ?_⟩⟩
    · exact Or.inl (Or.inr ⟨t, ht, 3328, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3336, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3344, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3352, by omega, by omega, by omega, by omega, by omega, h⟩)
  -- the action word of a state with `s`'s kernel base and core
  have hactW : ∀ s' : S, L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      Aligned (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) ∧
        CnW (st := st) T N C E R c s σ (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) := by
    intro s' hk' hc'
    have hN0 := hc0.node
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [nodeAt_ksb hk', hc', hc0.cur]
    refine ⟨nodeAt_aligned hN0 ho (by simp [layout.node.SCHED_ACTION]), Or.inl (Or.inl (KFoot.of_sfoot (Or.inr ?_)))⟩
    exact ⟨by rw [nodeAt_val hN0 ho]; omega, by rw [nodeAt_val hN0 ho]; omega⟩
  have hR1 : EpStateRel T E R B (L.mem s4) σ1 := by
    refine hR.upd_tcb hP ht x1 (hA4.mono fun b hb => ?_) (Or.inl hq) ?_
    · have n1 : b.val ≠ (tStA t).val := fun h => hb.2 (TF.of_val (a_st hta).2 h)
      have n2 : b.val ≠ (tBlockA t).val := fun h => hb.2 (TF.of_val (a_blk hta).2 h)
      have n3 : b.val ≠ (tBadgeA t).val := fun h => hb.2 (TF.of_val (a_badge hta).2 h)
      have n4 : b.val ≠ (tFlagsA t).val := fun h => hb.2 (TF.of_val (a_flags hta).2 h)
      omega
    refine hxt.restate hta (hA4.mono fun b hb => ?_) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · have := hb.2; omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_SEND; rfl
    · intro e' h; simp only [x1, Fl4Spec.epBlocked, Option.some.injEq] at h; subst h; rw [r2]
    · intro e' d'' h
      simp only [x1, Fl4Spec.ThreadState.blockedOnSend.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨by rw [r3], by rw [r4, hf, Fl4Proofs.P3.Endp.flags_eq]; rfl⟩
    · intro e' r d'' h; simp [x1] at h
    · intro r h; simp [x1] at h
  have hN1 : NtfnStateRel N T (L.mem s4) σ1 := by
    have hxt1 := hN.at_tcb ht hkt
    have g4 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3360 ≤ b.val) → L.mem s4 b = L.mem s b :=
      fun b hb hv => hA4 b hb (by omega)
    refine ntfn_upd_fields hP0.toC hN ht x1 (fun b hb hv => hA4 b hb ?_) hqn ⟨?_, ?_, ?_, ?_⟩
    · omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_SEND; rfl
    · intro n h; simp [x1] at h
    · show (L.mem s4 (badgeRegA t)).bv = badgeOf xt
      rw [g4 _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hxt1.badge
    · show (L.mem s4 (prioA t)).val = xt.tcbPriority.toNat
      rw [g4 _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hxt1.prio
  have hS1 : EpStep σ σ1 := EpStep.tcb hkt _ xt.tcbArch
  have hSR1 := hH.stable _ _ _ _ hSR hW4 hS1
  set σ2 := stsAct σ1 t.bv
  have hnt : e.bv ≠ t.bv := kheap_ne hk hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  have hspec : Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ =
      Fl4Spec.tcbEpAppend t.bv e.bv false σ2 := by
    rw [sendIpc_block hk hc]
    unfold Fl4Spec.sendIpcBlocked
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt)]
  have key : (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_SEND
      let s2 ← obj.Tcb.set_block_obj st t s1 e
      let s3 ← obj.Tcb.set_block_badge st t s2 badge
      let i ← ok (if g = true then endpoint.FLAG_GRANT else 0#u64)
      let i1 ← ok (if gr = true then endpoint.FLAG_GRANT_REPLY else 0#u64)
      let i2 ← lift (i ||| i1)
      let i3 ← ok (if call = true then endpoint.FLAG_CALL else 0#u64)
      let f ← lift (i2 ||| i3)
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (CnW (st := st) T N C E R c s σ) ⦄ := by
    step; step; step
    simp only [lift]
    step
    subst s1_post s2_post s3_post i2_post
    simp only [show ∀ u, Fl4Proofs.P3.stA u = tStA u from fun _ => rfl,
      show ∀ u, Fl4Proofs.P1.stA u = tStA u from fun _ => rfl]
    refine WP.spec_bind (WP.spec_and (hH0.schedC hP0 s4 σ1 t (by exact hR1) (by exact hSR1) ht)
      (schedule_tcb_cases s4 t)) ?_
    rintro s5 ⟨⟨hf5, hfN5, hS5⟩, hc5⟩
    -- the footprint up to `schedule_tcb`
    have hF5 : WritesIn st s s5 (CnW (st := st) T N C E R c s σ) := by
      rcases hc5 with rfl | rfl
      · exact hF4
      · refine hF4.trans (B := CnW (st := st) T N C E R c s σ) ?_ |>.mono fun b hb => hb.elim id id
        obtain ⟨ha1, ha2⟩ := hactW _ hW4.1 hW4.2.1
        exact (writesIn_wr ha1).mono fun b hb => hb ▸ ha2
    have hN2 : NtfnStateRel N T (L.mem s5) σ2 := hN1.frame hP0.n hfN5 (Notif.KView.stsAct _ _)
    have hR2 : EpStateRel T E R B (L.mem s5) σ2 := hR1.frame hP hf5 (KView.stsAct' _ _)
    have hpr : ∀ y ∈ T, L.mem s5 (prioA y) = L.mem s (prioA y) := by
      intro y hy
      have hya := hP.tcb y hy
      rw [hf5 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩)))]
      refine hA4 _ (a_prio hya).1 ?_
      have := val_prio hya
      by_cases eyt : y = t
      · subst eyt; omega
      · have := tcb_disj hP ht hy eyt; omega
    have hsort5 := sorted_transfer hP.tcb hx (hR2.at_ep he hk2) hpr hsort
    have htst : (L.mem s5 (tStA t)).val = if false = true then 3 else 4 := by
      rw [hf5 _ (a_st hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_st hta).2⟩))), r1]
      unfold sched.TS_BLOCKED_ON_SEND; rfl
    have htb : L.mem s5 (tBlockA t) = e := by
      rw [hf5 _ (a_blk hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_blk hta).2⟩))), r2]
    have happ := ep_append_rel hH hP s5 σ2 hR2 hS5 ht hkt2 he hk2 false hc htq htst htb hsort5
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    obtain ⟨xs, hQ, hxs, hB⟩ := (hR2.at_ep he hk2).queue
    have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
    have hqa := ep_append_full hP s5 he t obj.EP_SEND xs hQ ht htxs
    refine WP.spec_bind (WP.spec_and happ hqa) ?_
    rintro s6 ⟨⟨σ', hσ', hR', hS'⟩, -, -, hQA, hWE⟩
    -- the footprint of the append
    have hF6 : WritesIn st s s6 (CnW (st := st) T N C E R c s σ) := by
      refine hF5.trans (B := CnW (st := st) T N C E R c s σ) ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb
        ⟨fun h => hn (Or.inr (Or.inl ⟨e, he, h⟩)), fun ⟨w, hw, h⟩ => hn ?_⟩⟩ |>.mono fun b hb => hb.elim id id
      have hwT : w ∈ T := by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact ht
        · exact hQ.mem w hw
      rcases h with h | h
      · exact Or.inl (Or.inr ⟨w, hwT, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
      · exact Or.inl (Or.inr ⟨w, hwT, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
    -- the spec's append only changes the endpoint
    have hq2 : ∀ y ∈ x.epQueue, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Notif.prioOf σ2 y := by
      intro y hy
      rw [hxs] at hy
      obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
      obtain ⟨z, hz, -⟩ := hR2.tcb y' (hQ.mem y' hy'x)
      exact ⟨z, hz, by simp [Notif.prioOf, hz]⟩
    rw [tcbEpAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq2] at hσ'
    have hσe : σ' = updK σ2 e.bv (.endpoint (Fl4Spec.updateEpQueue x
        (specIns x.epQueue (Notif.prioOf σ2) x1.tcbPriority t.bv) false)) := by
      have := congrArg Prod.fst hσ'
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    have hkv : Notif.KView σ2 σ' := by
      rw [hσe]
      refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
      · have : p ≠ e.bv := by intro h'; rw [h', hk2] at h; cases h
        simp [this, h]
      · have : p ≠ e.bv := by intro h'; rw [h', hk2] at h; cases h
        simp [this, h]
    have hW : ∀ w ∈ t :: xs, w ∈ T ∧ (L.mem s5 (tStA w)).val ≠ 6 := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨ht, by rw [htst]; simp⟩
      · exact ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
    have hN3 := ntfn_frame_ep hP0.toC hN2 he hW hQA hkv
    simp only [WP.spec_ok]
    exact ⟨by simp, σ', by rw [hspec, tcbEpAppend_eq hk2 hkt2 (Notif.prioOf σ2) hq2, hσe],
      ⟨IpcRel.of hN3 hR' hS'.2.all, hS'.1⟩, hF6⟩
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    simp only [↓reduceIte, flag_ite]
    exact key
  | sendEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.1.symm]
    simp only [↓reduceIte, flag_ite]
    exact key
  | recvEP q => simp [Endp.CanBlock] at hc

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **One object's change by the blocking send**: `t`'s TCB from a runnable
state to `blockedOnSend`, or `e`'s endpoint. -/
def BChg (t e p : ObjRef) (o o' : KernelObject) : Prop :=
  (∃ x ep d, o = .tcb x ∧ o' = .tcb { x with tcbState := .blockedOnSend ep d } ∧ p = t ∧
    runnable x.tcbState = true) ∨
  (∃ x y, o = .endpoint x ∧ o' = .endpoint y ∧ p = e)

/-- **The spec's frame of the blocking send** (module docstring). -/
structure BFr (t e : ObjRef) (σ σ' : State Unit) : Prop where
  sk : Sk σ σ'
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ BChg t e p o o'

theorem BChg.objFrK {t e p : ObjRef} {o o' : KernelObject} (h : BChg t e p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, rfl, rfl, -, -⟩ | ⟨_, _, rfl, rfl, -⟩
  · exact IpcFrKeep.objFrK_tcb rfl rfl
  · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.ipcFr {t e : ObjRef} {σ σ' : State Unit} (F : BFr t e σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK

section
variable {t e : ObjRef} {σ σ' : State Unit}

/-- A TCB's change: kept, or `t`'s, runnable, to `blockedOnSend`. -/
def TKb (t p : ObjRef) (x : Tcb) (st : ThreadState) : Prop :=
  st = x.tcbState ∨ (p = t ∧ runnable x.tcbState = true ∧ ∃ ep d, st = .blockedOnSend ep d)

theorem TKb.run {p : ObjRef} {x : Tcb} {st : ThreadState} (h : TKb t p x st) (hr : runnable x.tcbState = false) :
    st = x.tcbState := by
  rcases h with h | ⟨-, h, -⟩
  · exact h
  · rw [hr] at h; cases h

theorem BFr.tcbF (h : BFr t e σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ st, σ'.kheap p = some (.tcb { x with tcbState := st }) ∧ TKb t p x st := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x.tcbState, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨x', ep, d, e1, rfl, hp', hr⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    exact ⟨_, h2, Or.inr ⟨hp', hr, ep, d, rfl⟩⟩

theorem BFr.tcbB (h : BFr t e σ σ') {p : ObjRef} {y : Tcb} (hp : σ'.kheap p = some (.tcb y)) :
    ∃ x st, σ.kheap p = some (.tcb x) ∧ y = { x with tcbState := st } ∧ TKb t p x st := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, y.tcbState, by rw [← h1, hp], rfl, Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨x, ep, d, rfl, e2, hp', hr⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    exact ⟨x, _, h1, rfl, Or.inr ⟨hp', hr, ep, d, rfl⟩⟩

/-- The other kinds kept. -/
theorem BFr.othF (h : BFr t e σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h4 : ∀ x, o ≠ .endpoint x) : σ'.kheap p = some o := by
  rcases h.kh p with e' | ⟨o0, o', k1, k2, hc⟩
  · rw [e', hp]
  · rw [hp] at k1; cases k1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩
    · exact absurd e1 (h1 _)
    · exact absurd e1 (h4 _)

theorem BFr.othB (h : BFr t e σ σ') {p : ObjRef} {o' : KernelObject} (hp : σ'.kheap p = some o')
    (h1 : ∀ x, o' ≠ .tcb x) (h4 : ∀ x, o' ≠ .endpoint x) : σ.kheap p = some o' := by
  rcases h.kh p with e' | ⟨o, o'', k1, k2, hc⟩
  · rw [← e', hp]
  · rw [hp] at k2; cases k2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩
    · exact absurd e2 (h1 _)
    · exact absurd e2 (h4 _)

theorem BFr.scF (h : BFr t e σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) : σ'.kheap p = some (.schedContext y n) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.scB (h : BFr t e σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.replyF (h : BFr t e σ σ') {p : ObjRef} {x : Reply} (hp : σ.kheap p = some (.reply x)) :
    σ'.kheap p = some (.reply x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.replyB (h : BFr t e σ σ') {p : ObjRef} {x : Reply} (hp : σ'.kheap p = some (.reply x)) :
    σ.kheap p = some (.reply x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.ntfnF (h : BFr t e σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    σ'.kheap p = some (.notification x) :=
  h.othF hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.ntfnB (h : BFr t e σ σ') {p : ObjRef} {x : Notification} (hp : σ'.kheap p = some (.notification x)) :
    σ.kheap p = some (.notification x) :=
  h.othB hp (fun _ e => by cases e) (fun _ e => by cases e)

theorem BFr.epF (h : BFr t e σ σ') {p : ObjRef} {x : Endpoint} (hp : σ.kheap p = some (.endpoint x)) :
    ∃ y, σ'.kheap p = some (.endpoint y) ∧ (y = x ∨ p = e) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [h1, hp], Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hp'⟩ <;> cases e1
    exact ⟨y, h2, Or.inr hp'⟩

theorem BFr.epB (h : BFr t e σ σ') {p : ObjRef} {y : Endpoint} (hp : σ'.kheap p = some (.endpoint y)) :
    ∃ x, σ.kheap p = some (.endpoint x) ∧ (y = x ∨ p = e) := by
  rcases h.kh p with h1 | ⟨o, o', h1, h2, hc⟩
  · exact ⟨y, by rw [← h1, hp], Or.inl rfl⟩
  · rw [hp] at h2; cases h2
    rcases hc with ⟨_, _, _, -, e2, -⟩ | ⟨x, y', rfl, e2, hp'⟩ <;> cases e2
    exact ⟨x, h1, Or.inr hp'⟩

theorem BFr.kind (h : BFr t e σ σ') (p : ObjRef) :
    (∀ o, σ.kheap p = some o → ∃ o', σ'.kheap p = some o' ∧ aType o' = aType o) ∧
    (∀ o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ aType o' = aType o) := by
  rcases h.kh p with e' | ⟨o, o', h1, h2, hc⟩
  · exact ⟨fun o ho => ⟨o, by rw [e', ho], rfl⟩, fun o' ho => ⟨o', by rw [← e', ho], rfl⟩⟩
  · have ha : aType o' = aType o := by
      rcases hc with ⟨x, ep, d, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;> rfl
    exact ⟨fun o0 ho0 => ⟨o', h2, by rw [h1] at ho0; cases ho0; exact ha⟩,
      fun o0 ho0 => ⟨o, h1, by rw [h2] at ho0; cases ho0; exact ha⟩⟩

theorem BFr.szKeep (h : BFr t e σ σ') : SzKeep σ σ' := fun _ y n hp => ⟨y, h.scB hp⟩

theorem BFr.ykeep (h : BFr t e σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p y n hp => ⟨y, h.scF hp, rfl⟩, fun p z n hp => ⟨z, h.scB hp, rfl⟩⟩
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFr.mcpKeep (h : BFr t e σ σ') : McpKeep σ σ' := fun p x hp => by
  obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFr.bufKeep (h : BFr t e σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => by obtain ⟨st, hp', -⟩ := h.tcbF hp; exact ⟨_, hp', rfl⟩

theorem BFr.prio (h : BFr t e σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
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

theorem BFr.nsc {N C : Set U64} (h : BFr t e σ σ') (hN : NSC N C σ) : NSC N C σ' := by
  intro n hn y p hy hp
  exact hN n hn y p (h.ntfnB hy) hp

theorem BFr.own {T C : Set U64} (h : BFr t e σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · obtain ⟨st, hkt', -⟩ := h.tcbF hkt
    refine Or.inl ⟨u, hu, _, hkt', by rw [h.sk.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.sk.csc] at hy
      exact hown y n (h.scB hy)
    · rw [h.sk.cons] at h0; rw [h.sk.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.sk.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.sk.csc] at hy
    exact hun y n (h.scB hy)

theorem BFr.off (h : BFr t e σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.sk.cons] at hc ⊢; rw [h.sk.tm]
  rw [h.sk.csc] at hy; rw [h.sk.csc, h.sk.isc] at ha
  exact hO hc y n (h.scB hy) ha

theorem BFr.idleOK (h : BFr t e σ σ') (hO : IdleOK σ) : IdleOK σ' := by
  obtain ⟨x, hx, h1, h2, h3⟩ := hO
  obtain ⟨st, hx', hs⟩ := h.tcbF hx
  refine ⟨{ x with tcbState := st }, by rw [h.sk.idle]; exact hx', by rw [h.sk.isc]; exact h1, ?_,
    by rw [h.sk.idle, h.sk.rel]; exact h3⟩
  show st = _
  rw [hs.run (by rw [h2]; rfl)]; exact h2

/-- `BlockedScActive` after, `t`'s SCs active. -/
theorem BFr.bsa (h : BFr t e σ σ') (hB : BlockedScActive σ)
    (ht : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t → scActive y = true) :
    BlockedScActive σ' := by
  refine ⟨fun p z n u y hp hyt hy hq => ?_, fun p z n hp hr => hB.replies p z n (h.scB hp) hr⟩
  obtain ⟨x, st, hx, rfl, hs⟩ := h.tcbB hy
  rcases hs with rfl | ⟨rfl, -, -⟩
  · exact hB.tcb p z n u x (h.scB hp) hyt hx hq
  · exact ht p z n (h.scB hp) hyt

/-- `IpcSorted` after, `e`'s queue sorted. -/
theorem BFr.isorted (h : BFr t e σ σ') (hS : IpcSorted σ)
    (he : ∀ y, σ'.kheap e = some (.endpoint y) → SortedQ σ y.epQueue) : IpcSorted σ' := by
  refine ⟨fun p y hp => ?_, fun p y hp => ?_⟩
  · obtain ⟨x, hx, hc⟩ := h.epB hp
    rcases hc with rfl | rfl
    · exact (hS.1 p y hx).congr fun u _ => h.prio u
    · exact (he y hp).congr fun u _ => h.prio u
  · exact (hS.2 p y (h.ntfnB hp)).congr fun u _ => h.prio u

theorem BFr.kback (h : BFr t e σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e' | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e', ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, ep, d, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h1, by simp⟩

theorem BFr.ksz (h : BFr t e σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e'⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e'.symm⟩

theorem BFr.ksub (h : BFr t e σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun u hu => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, hx, -⟩ := h.tcbB hu; exact ⟨x, hx⟩
  · rcases h.kh o with e' | ⟨ko, ko', h1, -, -⟩
    · rw [e']; exact hn
    · rw [hn] at h1; cases h1

theorem BFr.callKeep (h : BFr t e σ σ') :
    (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
    (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
    (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) :=
  ⟨fun q y n hq => ⟨y, h.scF hq, rfl⟩, fun q x hq => ⟨x, h.replyF hq, rfl⟩, fun p x n hp => ⟨x, h.scB hp⟩⟩

theorem BFr.skeep (h : BFr t e σ σ') : Ipc.SKeep σ σ' := by
  refine ⟨h.sk.rel, h.sk.tm, fun p y hy => ?_, fun p y n hy => h.scB hy⟩
  obtain ⟨x, st, hx, rfl, -⟩ := h.tcbB hy
  exact ⟨x, hx, rfl⟩

theorem BFr.khrb (h : BFr t e σ σ') : KhRB σ σ' :=
  KhRB.of_kh h.kh fun p o o' hc => by
    rcases hc with ⟨x, ep, d, rfl, rfl, -, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · exact ObjRB.tcb (Or.inr rfl)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)

end

/-- `tcb_ep_append` keeps what `IK` reads. -/
theorem ikm_tcbEpAppend {t : ObjRef} (u e : ObjRef) (b : Bool) : IKM t (tcbEpAppend (Z := Unit) u e b) := by
  unfold tcbEpAppend
  exact ikm_bind (ikm_of_rdo (rdo_getSimpleKo _ _)) fun _ => ikm_bind (ikm_pure _) fun _ =>
    ikm_bind (ikm_of_rdo (rdo_tcbAppend _ _)) fun _ => ikm_setSimpleKo notTSN_ep _ _

/-- **The spec's blocking send in `BFr`** (module docstring). -/
theorem sendIpcBlock_eq {σ : State Unit} {t e : ObjRef} {xt : Tcb} {x : Endpoint}
    (hkt : σ.kheap t = some (.tcb xt)) (hk : σ.kheap e = some (.endpoint x)) (hc : Endp.CanBlock false x)
    (htq : t ∉ x.epQueue) (hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z)) (hr : runnable xt.tcbState = true)
    (hS : SortedQ σ x.epQueue) (call : Bool) (badge : Badge) (g gr d : Bool) :
    ∃ σ', sendIpc (Z := Unit) true call badge g gr d t e σ = ({((), σ')}, False) ∧ BFr t e σ σ' ∧
      IK t σ σ' ∧ (∃ ds, σ'.kheap t = some (.tcb { xt with tcbState := .blockedOnSend e ds })) ∧
      σ'.readyQueues = σ.readyQueues ∧
      (σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread) ∧
      (t = σ.curThread → σ.schedulerAction = .resumeCurThread → σ'.schedulerAction = .chooseNewThread) ∧
      (∀ y, σ'.kheap e = some (.endpoint y) → SortedQ σ y.epQueue) := by
  let ds : SenderPayload := { senderBadge := badge, senderCanGrant := g, senderCanGrantReply := gr, senderIsCall := call }
  let x1 : Tcb := { xt with tcbState := .blockedOnSend e ds }
  let σ2 := stsAct (updK σ t (.tcb x1)) t
  let q' := Notif.specIns x.epQueue (Sched.prioOf σ2) x1.tcbPriority t
  let σ' := updK σ2 e (.endpoint (updateEpQueue x q' false))
  have hte : t ≠ e := by rintro rfl; rw [hkt] at hk; cases hk
  have hk2 : σ2.kheap e = some (.endpoint x) := by simp [σ2, stsAct_kheap, Ne.symm hte, hk]
  have hkt2 : σ2.kheap t = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  have hq2 : ∀ y ∈ x.epQueue, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Sched.prioOf σ2 y := by
    intro y hy
    obtain ⟨z, hz⟩ := hq y hy
    have hyt : y ≠ t := fun h => htq (h ▸ hy)
    have hz2 : σ2.kheap y = some (.tcb z) := by simp [σ2, stsAct_kheap, hyt, hz]
    exact ⟨z, hz2, (prioOf_eq hz2).symm⟩
  have heq : sendIpc (Z := Unit) true call badge g gr d t e σ = ({((), σ')}, False) := by
    rw [Endp.sendIpc_block hk hc]
    unfold sendIpcBlocked
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt)]
    exact Endp.tcbEpAppend_eq hk2 hkt2 (Sched.prioOf σ2) hq2 false
  have hm : ((), σ') ∈ (sendIpc (Z := Unit) true call badge g gr d t e σ).1 := by
    rw [heq]; exact Set.mem_singleton _
  have hik : IK t σ σ' := by
    rw [Endp.sendIpc_block hk hc] at hm
    unfold sendIpcBlocked at hm
    exact ikm_bind (ikm_setThreadState _) (fun _ => ikm_tcbEpAppend t e false) σ ((), σ') hm
  have hsk2 : Sk σ σ2 := by
    show Sk σ (stsAct _ t)
    unfold stsAct; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsk : Sk σ σ' := hsk2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkh : ∀ p, σ'.kheap p = if p = e then some (.endpoint (updateEpQueue x q' false))
      else if p = t then some (.tcb x1) else σ.kheap p := by
    intro p
    simp only [σ', σ2, updK_kheap, stsAct_kheap, Function.update_apply]
  have hact2 : σ2.schedulerAction = σ.schedulerAction ∨ σ2.schedulerAction = .chooseNewThread := by
    show (stsAct (updK σ t (.tcb x1)) t).schedulerAction = _ ∨
      (stsAct (updK σ t (.tcb x1)) t).schedulerAction = _
    unfold stsAct; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hpr2 : ∀ u, Sched.prioOf σ2 u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = t
    · subst hut; exact (prioOf_eq hkt2).trans (prioOf_eq hkt).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
      simp only [σ2, stsAct_kheap, updK_kheap, Function.update_apply, if_neg hut]
  have hrq : σ'.readyQueues = σ.readyQueues := by
    show (stsAct _ t).readyQueues = _
    unfold stsAct; split <;> rfl
  refine ⟨σ', heq, ⟨hsk, fun p => ?_⟩, hik, ⟨ds, by rw [hkh, if_neg hte, if_pos rfl]⟩, hrq, hact2,
    fun hct hres => ?_, fun y hy => ?_⟩
  · rw [hkh]
    by_cases hpe : p = e
    · rw [if_pos hpe]; exact Or.inr ⟨.endpoint x, .endpoint (updateEpQueue x q' false), by rw [hpe]; exact hk, rfl,
        Or.inr ⟨x, _, rfl, rfl, hpe⟩⟩
    · rw [if_neg hpe]
      by_cases hpt : p = t
      · rw [if_pos hpt]
        exact Or.inr ⟨.tcb xt, .tcb x1, by rw [hpt]; exact hkt, rfl, Or.inl ⟨xt, e, ds, rfl, rfl, hpt, hr⟩⟩
      · rw [if_neg hpt]; exact Or.inl rfl
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
    rw [epQueue_update]
    exact (sortedQ_specIns (hS.congr fun u _ => hpr2 u) t (prioOf_eq hkt2)).congr fun u _ => (hpr2 u).symm

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **An object leaves the dead set once covered** (module docstring). -/
theorem JCovD.undead {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}
    (h : JCovD (L := L) th H G D Cs s) {e : U64}
    (hth : ∀ k, th e = some k → Covered (L.mem s) G e.val (e.val + max (objSize k) 1))
    (hH : ∀ k, H e = some k → Covered (L.mem s) G e.val (e.val + 2 ^ k.bits)) :
    JCovD (L := L) th H G (D \ {e}) Cs s := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => h.dead q hq.1, h.ks, h.idleOut⟩
  · by_cases hqe : q = e
    · subst hqe; exact Or.inl (hth k hq)
    · rcases h.th q k hq with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h1, hqe⟩)
      · exact Or.inr (Or.inr h1)
  · by_cases hqe : q = e
    · subst hqe; exact Or.inl (hH k hq)
    · rcases h.h q k hq with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h1, hqe⟩)
      · exact Or.inr (Or.inr h1)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- The current SC is not the idle SC when the current thread is not idle
(`Inv.back`: both threads would be the SC's). -/
theorem JAtZ.curSc_ne_idle (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : CurInv σ)
    (hti : σ.curThread ≠ σ.idleThread) : σ.curSc ≠ σ.idleSc := by
  intro hci
  obtain ⟨xc, hkc, hcs, -⟩ := hC.tcb
  obtain ⟨xi, hki, hxi, -, -⟩ := J.act.2
  obtain ⟨y1, n1, hk1, hy1⟩ := J.inv.back _ _ _ hkc hcs
  obtain ⟨y2, n2, hk2, hy2⟩ := J.inv.back _ _ _ hki hxi
  rw [hci, hk2] at hk1; cases hk1
  rw [hy1] at hy2
  exact hti (Option.some.inj hy2)

set_option maxHeartbeats 16000000 in
/-- **The blocking send at `J`** (module docstring): the current thread
`t`, `Restart` and in no ready queue, blocks sending on the idle or
sending endpoint `e`, covered by a cap (`hcov`). -/
theorem JAtZ.sendBlockJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hrs : xt.tcbState = .restart)
    (hct : σ.curThread = t.bv) (hres : σ.schedulerAction = .resumeCurThread)
    (hti : σ.curThread ≠ σ.idleThread) (hnq : ∀ d p, t.bv ∉ σ.readyQueues d p)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock false x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    (call : Bool) (b : U64) (g gr don : Bool) :
    endpoint.send_ipc st arI s a true call b g gr don t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call b.bv g gr don t.bv e.bv σ = ({((), σ')}, False) ∧
        ∃ V : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst (D \ {e}) r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hC : CurInv σ := J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hr : Fl4Spec.runnable xt.tcbState = true := by rw [hrs]; rfl
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by rw [hrs]; decide
  have hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by rw [hrs] at h; cases h
  have htq : t.bv ∉ x.epQueue := Endp.not_queued hI.1.toE ht hkt hnb e he x hk
  have hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z) := fun y hy => by
    obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hk).2 y hy
    exact ⟨z, hz⟩
  obtain ⟨σ', heq, F, hik, -, -, hact, hcn, hsrt⟩ :=
    sendIpcBlock_eq hkt hk hc htq hq hr (J.isorted.1 _ _ hk) call b.bv g gr don
  have hcn' : σ'.schedulerAction = .chooseNewThread := hcn hct.symm hres
  -- P1's `CanBlock` of the current thread
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hcb : P1.CanBlock st (P1.Heap.tcbs H) Ac s t := by
    obtain ⟨Q, R, hcq, hs⟩ := hS.lists
    have h3 := (hI.1.toN.at_tcb ht hkt).st
    have hsw : L.mem s (P1.stA t) = sched.TS_RESTART := by
      rw [P1.stA_eq, ← tStA_eq]; apply UScalar.eq_of_val_eq; rw [h3, hrs, tsVals.2.1]; rfl
    have ha0 : L.actionW s = 0#u64 := by
      have h := hS.act
      rw [hres] at h
      unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
    have hcw : L.curW s = t := by
      apply P1.eq_of_bv
      rw [← hct, hs.curThread]
      unfold P1.LawfulStore.curW nodeW; rw [hcq.cur]
    refine ⟨htH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsw]; unfold P1.Blocked; rw [tsVals.2.1, tsVals.2.2.2.1, tsVals.2.2.1, tsVals.2.2.2.2]; decide
    · rw [hsw, tsVals.2.1]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    · by_contra hq'
      have hm := (hcq.queued t ht).1 hq'
      exact hnq 0 _ (by rw [hs.rq _ (hcq.prio t ht), mem_map_bv]; exact hm)
    · by_contra hq'
      have hm := (hcq.released t ht).1 hq'
      exact hC.notRel (by rw [hct, hs.rel, mem_map_bv]; exact hm)
    · rw [ha0]; intro h; exact (hcq.tcbs t ht).ne0 (by rw [← h]; rfl)
    · intro h
      have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
        unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
      exact hti (by rw [hct, hs.idleTh, ← ei, h])
    · exact fun h1 => hB0.sact t htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw⟩))))) h1
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 1#u64 := by
    have hx := hI.1.toE.at_ep he hk
    rw [epState_eq]
    cases x with
    | idleEP => exact Or.inl hx.1
    | sendEP q => exact Or.inr hx.1
    | recvEP q => simp [Endp.CanBlock] at hc
  have p1b := P1.endpoint.send_ipc.block arI s a true call b g gr don t e Q0 R0 h0 hB0 hX0 hS0 hSg0
    (fun _ => hcb) hHe hst0
  have p1f : endpoint.send_ipc st arI s a true call b g gr don t e ⦃ s' _ => P1.Foot st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄ :=
    P1.endpoint.send_ipc.blockFoot arI s a true call b g gr don t e h0 (fun _ => hcb) hHe hst0
  refine WP.spec_mono (WP.spec_and (WP.spec_and (send_ipc_blockF (ar := arI) J.ip s a σ hI ht hkt hnb hnn he hk hc
    (J.qsortedE e he) call b g gr don) p1b) p1f) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0, h0eq, hIR, hW⟩, hbk⟩, hfoot⟩
  simp only [WP.uncurry'_pair] at ea hbk hfoot hIR hW
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
  -- the assembly (as XTopJointCancel's `JAtZ.kfrStep`)
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
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := ⟨fun u hu => (by rw [hcn'] at hu; cases hu), F.idleOK J.act.2⟩
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcn'
  have hrun3 : CurRunM σ' := Or.inl (by rw [hcn']; intro h; cases h)
  -- the dead: the thread is not dead (`Restart`); the endpoint leaves the dead set
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rw [hrs]; simp [tsCode])
  have hdead : ∀ q ∈ D \ {e}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ t.bv := htD q hq.1
    have hqe : q.bv ≠ e.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ?_) (fun x hx => ?_)
      (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1 (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
      show st' = x.tcbState
      rcases hs' with e1 | ⟨e1, -⟩
      · exact e1
      · exact absurd e1 hqt
    · obtain ⟨y, hy, hc'⟩ := F.epF hx
      rcases hc' with rfl | e1
      · exact hy
      · exact absurd e1 hqe
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {e})
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {e}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the thread's `RelIfBound` from `Restart`)
  have hnqT : NotQueued σ t.bv := ⟨hnq, by rw [← hct]; exact hC.notRel⟩
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
    obtain ⟨xc, hkc, hcs, -⟩ := hC.tcb
    rw [hct, hkt] at hkc; cases hkc
    have e1 : σ.curSc = q.bv := Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {e}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted hsrt, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨rfl, σ', heq, Z.vs, J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R hKd F.sk.orig hidl.1 (J.zD_diffE he)⟩

end

end

end Fl4Proofs.P3
