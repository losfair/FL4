/-
P3 (DESIGN.md §9), IPC: **`cancel_all_signals` on `IRel`** (a notification's
finalisation: every thread waiting on it restarted).

FL4 walks the notification's queue from its head, reading each thread's
successor before the thread's step (`ntfn_dequeue`, `set_thread_state
Restart`, `unblock_sporadic`, `possible_switch_to`); the spec runs
`remove_and_restart_ntfn_queued_thread` over the queue (`mapM_x`), then
`reschedule_required`.

* `ntfn_restart_irel`: one thread's step, the head of the notification's
  queue (the dequeue as `cancel_ipc_ntfnI`'s, the restart, the sporadic
  unblock by `unblock_irel`, the switch by `switch_top`).
* `cancel_all_signals_irel`: the loop, by the queue still to visit (the
  notification's queue itself), the spec's outcomes from it included in
  the whole's (`mapMx`); FL4's fuel (`WALK_FUEL`) exceeds any queue.

Every slot and the kernel-global base are kept (`IFrame`, from the steps' footprints:
`unblock_sporadic_tfoot` for the sporadic unblock).

The spec's scheduler facts are carried along the loop (`SpecFinOut`'s
`ntfn_restart_mid`, `pst_actReady`): the queued threads' SCs ready and sufficient
(`MemOK`), `ScBack`, `ActReady`; named at the start (`NtfnQPre`), with the
notification in `N`.
-/
import Fl4Proofs.P3.IpcCancelBadged
import Fl4Proofs.P3.IpcCancelAll
import Fl4Proofs.P3.IpcSlotsSame
import Fl4Proofs.P3.DomSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Step
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

open Fl4Spec in
/-- One step of the spec's loop. -/
abbrev rrn (n : U64) (t : ObjRef) : SMonad Unit Unit := removeAndRestartNtfnQueuedThread t n.bv

/-! ### The TCB and SC frame words a finalisation never writes -/

/-- **The frame words of `JAtZ` kept by a notification's finalisation**
(`JRest`'s `mcp`, `yld`, `buf` and `call`): no TCB's `MCP` (3440),
`YIELD_TO` (3472) or IPC-buffer (3512) word, no SC's `REPLY` word. -/
def TSW (T C : Set U64) (a : U64) : Prop :=
  (∀ t ∈ T, a.val ≠ t.val + 3440 ∧ a.val ≠ t.val + 3472 ∧ a.val ≠ t.val + 3512) ∧ ∀ q ∈ C, a ≠ scReplyA q

/-- A word at offset `K0` of a TCB is at no other offset `K` of a TCB. -/
theorem tw_ne {T : Set U64} (hT : TcbPlaced T) {t y a : U64} (ht : t ∈ T) (hy : y ∈ T) {K0 K : Nat}
    (ha : a.val = t.val + K0) (hK0 : K0 < 4096) (hK : K < 4096) (hne : K0 ≠ K) : a.val ≠ y.val + K := by
  have h1 := (hT t ht).align; have h2 := (hT y hy).align
  by_cases e : y = t
  · subst e; omega
  · have := val_ne_of_ne e; omega

/-- A word of an SC of `C` is not written: its `REPLY` word lies in it. -/
theorem screply_obj {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {q : U64} (hq : q ∈ C) :
    ∃ x n, σ.kheap q.bv = some (.schedContext x n) ∧ Sched.ScObj q n (scReplyA q) := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
  obtain ⟨-, hv, hsz⟩ := sc_reply_word hS hq
  exact ⟨xq, nq, hkq, by have := hsz xq nq hkq; unfold Sched.ScObj; rw [hv]; omega⟩

/-- A word inside a TCB of `T`, not at the frame offsets, is `TSW`. -/
theorem tsw_tcb {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {y a : U64} (hy : y ∈ T)
    {K0 : Nat} (ha : a.val = y.val + K0) (hK0 : K0 < 4096) (h1 : K0 ≠ 3440) (h2 : K0 ≠ 3472) (h3 : K0 ≠ 3512) :
    TSW T C a := by
  have hT := hS.placed.tcb
  refine ⟨fun t ht => ⟨tw_ne hT hy ht ha hK0 (by decide) h1, tw_ne hT hy ht ha hK0 (by decide) h2,
    tw_ne hT hy ht ha hK0 (by decide) h3⟩, fun q hq e => ?_⟩
  obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
  have := (hS.scOut q hq xq nq hkq _ hin).2.2.1 y hy
  rw [← e, ha] at this; omega

theorem KFoot.tsw {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (hb : KFoot st T N C c s σ b) : TSW T C b := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  refine ⟨fun t ht => ?_, fun q hq => hb.ne_screply hS hq⟩
  have k : ∀ K : U64, K.val < 4096 → ¬ SOff K → b.val ≠ t.val + K.val := fun K hK hs' e =>
    hb.ne_tcbw hS ht hK hs' (UScalar.eq_of_val_eq (by rw [e, tfield_val (hT t ht) hK]))
  exact ⟨k 3440#u64 (by simp) (fun h => h.2.2.1 rfl), k 3472#u64 (by simp) (fun h => h.2.2.2.1 rfl),
    k 3512#u64 (by simp) (fun h => h.2.2.2.2.1 rfl)⟩

theorem NWrite.tsw {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (hb : NWrite N T b) : TSW T C b := by
  have hT := hS.placed.tcb
  rcases hb with ⟨n, hn, g1, g2⟩ | ⟨t, ht, h⟩
  · refine ⟨fun t ht => ?_, fun q hq e => ?_⟩
    · have := hS.placed.disj n hn t ht; omega
    · obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
      exact (hS.scOut q hq xq nq hkq _ hin).1 (e ▸ Or.inl ⟨n, hn, g1, g2⟩)
  · have hta := hT t ht
    have := regIdx_lt Fl4Spec.badge_register
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact tsw_tcb hS ht (val_st hta) (by omega) (by omega) (by omega) (by omega)
    · exact tsw_tcb hS ht (val_blk hta) (by omega) (by omega) (by omega) (by omega)
    · rw [badgeRegA_eq_regA]
      exact tsw_tcb hS ht (K0 := 256 + 8 * (regIdx Fl4Spec.badge_register).val)
        (by rw [regA_val hta (regIdx_lt _)]; omega) (by omega) (by omega) (by omega) (by omega)
    · exact tsw_tcb hS ht (val_next hta) (by omega) (by omega) (by omega) (by omega)
    · exact tsw_tcb hS ht (val_prev hta) (by omega) (by omega) (by omega) (by omega)

theorem SFootI.tsw {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (hb : SFootI st T c s b) : TSW T C b := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  rcases hb with ⟨y, hy, rfl | rfl | rfl⟩ | ⟨g1, g2, -⟩
  · exact tsw_tcb hS hy (tfield_val (hT y hy) (K := 3480#u64) (by simp)) (by simp) (by simp) (by simp) (by simp)
  · exact tsw_tcb hS hy (tfield_val (hT y hy) (K := 3488#u64) (by simp)) (by simp) (by simp) (by simp) (by simp)
  · exact tsw_tcb hS hy (tfield_val (hT y hy) (K := 3592#u64) (by simp)) (by simp) (by simp) (by simp) (by simp)
  · refine ⟨fun t ht => ?_, fun q hq e => ?_⟩
    · have := hc.node.disj t ht; omega
    · obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
      have := (hS.scOut q hq xq nq hkq _ hin).2.1
      rw [← e] at this; omega

theorem tsw_bound {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {y : U64} (hy : y ∈ T) :
    TSW T C (tBoundA y) :=
  tsw_tcb hS hy (val_bound (hS.placed.tcb y hy)) (by omega) (by omega) (by omega) (by omega)

/-- **The words a notification's finalisation writes**, against a start's
sets and SC sizes: the scheduler's (`KFoot`) and the TCBs' words off their
frame offsets, none at the VCPU word (3664, `tVcpuA`; KENTRY-PLAN g2b: no
native step writes it). -/
def FinW (T N C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  KFoot st T N C c s σ b ∨
    ∃ y ∈ T, ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ b.val = y.val + K

/-- `FinW`'s words are words of the other objects (`OObj`). -/
theorem FinW.oobj {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : FinW (st := st) T N C c s σ b) : Vs.OObj st N T C E R B c s σ b := by
  rcases h with hk | ⟨y, hy, K, h1, h2, -, -, -, e⟩
  · exact tfoot_oobj hS (Or.inl hk)
  · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))

theorem SzKeepC.trans' {C : Set U64} {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : SzKeepC C σ1 σ2)
    (h2 : SzKeepC C σ2 σ3) : SzKeepC C σ1 σ3 :=
  fun sc hsc x n hk => by obtain ⟨x1, h⟩ := h2 sc hsc x n hk; exact h1 sc hsc x1 n h

theorem FinW.back {s s' : S} {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s) (hz : SzKeepC C σ σ') {b : U64}
    (h : FinW (st := st) T N C c s' σ' b) : FinW (st := st) T N C c s σ b := by
  rcases h with (h | h | ⟨sc, hsc, x, n, hx, ho, hne⟩) | h
  · exact Or.inl (Or.inl ((SFoot.ksb hk).1 h))
  · exact Or.inl (Or.inr (Or.inl h))
  · obtain ⟨x0, hx0⟩ := hz sc hsc x n hx
    exact Or.inl (Or.inr (Or.inr ⟨sc, hsc, x0, n, hx0, ho, hne⟩))
  · exact Or.inr h

/-- A step of the finalisation: its writes `FinW` (at its start), the SCs'
sizes kept. -/
def FinStep (T N C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  WritesIn st s s' (FinW (st := st) T N C c s σ) ∧ SzKeepC C σ σ'

theorem FinStep.refl (s : S) (σ : Fl4Spec.State Unit) : FinStep (st := st) T N C c s σ s σ :=
  ⟨WritesIn.refl _ _, fun _ _ x _ h => ⟨x, h⟩⟩

theorem FinStep.trans {s1 s2 s3 : S} {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : FinStep (st := st) T N C c s1 σ1 s2 σ2)
    (h2 : FinStep (st := st) T N C c s2 σ2 s3 σ3) : FinStep (st := st) T N C c s1 σ1 s3 σ3 :=
  ⟨h1.1.trans1 (h2.1.mono fun _ hb => FinW.back h1.1.1 h1.2 hb), SzKeepC.trans' h1.2 h2.2⟩

theorem FinW.tsw {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : FinW (st := st) T N C c s σ b) : TSW T C b := by
  rcases h with h | ⟨y, hy, K, h1, h2, h3, h4, h5, e⟩
  · exact KFoot.tsw hS h
  · exact tsw_tcb hS hy e h2 h3 h4 h5.1

/-- **A `FinW` word is no TCB's VCPU word** (KENTRY-PLAN g2b). -/
theorem FinW.nv {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : FinW (st := st) T N C c s σ b) : ∀ t ∈ T, b ≠ tVcpuA t := by
  intro t ht
  rcases h with h | ⟨y, hy, K, h1, h2, h3, h4, h5, e⟩
  · exact KFoot.ne_vcpu hS h ht
  · intro hb
    have hT := hS.placed.tcb
    have hv : b.val = t.val + 3664 := by rw [hb]; exact tfield_val (hT t ht) (K := 3664#u64) (by simp)
    exact tw_ne hT hy ht e h2 (by decide) h5.2 hv

theorem NWrite.finW {s : S} {σ : Fl4Spec.State Unit} (hT : TcbPlaced T) {b : U64} (hb : NWrite N T b) :
    FinW (st := st) T N C c s σ b := by
  rcases hb with ⟨n, hn, g1, g2⟩ | ⟨t, ht, h⟩
  · exact Or.inl (KFoot.of_nw ⟨n, hn, g1, g2⟩)
  · have hta := hT t ht
    have := regIdx_lt Fl4Spec.badge_register
    refine Or.inr ⟨t, ht, ?_⟩
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨3328, by omega, by omega, by omega, by omega, by omega, val_st hta⟩
    · exact ⟨3336, by omega, by omega, by omega, by omega, by omega, val_blk hta⟩
    · rw [badgeRegA_eq_regA]
      exact ⟨256 + 8 * (regIdx Fl4Spec.badge_register).val, by omega, by omega, by omega, by omega, by omega,
        regA_val hta (regIdx_lt _)⟩
    · exact ⟨3496, by omega, by omega, by omega, by omega, by omega, val_next hta⟩
    · exact ⟨3504, by omega, by omega, by omega, by omega, by omega, val_prev hta⟩

theorem SFootI.finW {s : S} {σ : Fl4Spec.State Unit} (hT : TcbPlaced T) {b : U64} (hb : SFootI st T c s b) :
    FinW (st := st) T N C c s σ b := by
  rcases hb with ⟨y, hy, rfl | rfl | rfl⟩ | ⟨g1, g2, -⟩
  · exact Or.inr ⟨y, hy, 3480, by omega, by omega, by omega, by omega, by omega,
      tfield_val (hT y hy) (K := 3480#u64) (by simp)⟩
  · exact Or.inr ⟨y, hy, 3488, by omega, by omega, by omega, by omega, by omega,
      tfield_val (hT y hy) (K := 3488#u64) (by simp)⟩
  · exact Or.inr ⟨y, hy, 3592, by omega, by omega, by omega, by omega, by omega,
      tfield_val (hT y hy) (K := 3592#u64) (by simp)⟩
  · exact Or.inl (KFoot.of_sfoot (Or.inr ⟨g1, g2⟩))

theorem finW_bound {s : S} {σ : Fl4Spec.State Unit} (hT : TcbPlaced T) {y : U64} (hy : y ∈ T) :
    FinW (st := st) T N C c s σ (tBoundA y) :=
  Or.inr ⟨y, hy, 3368, by omega, by omega, by omega, by omega, by omega, val_bound (hT y hy)⟩

/-- **`unblock_sporadic` writes in the SC code's footprint** (`TFoot`): the
SC's words (`unblock_check_scw`), or nothing. -/
theorem unblock_sporadic_kfoot {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) (t : U64)
    (ht : t ∈ T) : notification.unblock_sporadic st s t ⦃ s' => WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  unfold notification.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc.cur]
  by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    refine WP.spec_mono (unblock_check_scw hS hscC (hy.spor hsp')) fun s' hw => hw.mono fun b hb => ?_
    rcases hb with h | h
    · exact KFoot.of_sw h
    · exact KFoot.of_sfoot (Or.inr h)

theorem unblock_sporadic_tfoot {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) (t : U64)
    (ht : t ∈ T) : notification.unblock_sporadic st s t ⦃ s' => WritesIn st s s' (TFoot st T N C c s σ) ⦄ :=
  WP.spec_mono (unblock_sporadic_kfoot hS t ht) fun _ hw => hw.mono fun _ hb => Or.inl hb

set_option maxHeartbeats 8000000 in
/-- **One waiting thread of a notification restarted** (the head `t` of its
queue `t :: rest`) on `IRel`: the notification's queue `rest` after. -/
theorem ntfn_restart_irel (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hnN : n ∈ N)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn)) {t : U64} {rest : List U64}
    (hq : Fl4Spec.ntfnQueueOf xn = (t :: rest).map UScalar.bv)
    (hm : ∀ u ∈ Fl4Spec.ntfnQueueOf xn, MemOK σ u) (hBk : ScBack σ) (hAr : ActReady σ)
    {γ : Type} (k : S → Result γ) {Q : γ → Prop}
    (hkont : ∀ s' σ' xn', ((), σ') ∈ (rrn n t.bv σ).1 → IRel st th cr N T C E R B c s' σ' →
      σ'.kheap n.bv = some (.notification xn') → Fl4Spec.ntfnQueueOf xn' = rest.map UScalar.bv →
      IFrame (L := L) th s s' → FinStep (st := st) T N C c s σ s' σ' → (∀ u ∈ rest.map UScalar.bv, MemOK σ' u) →
      ScBack σ' → ActReady σ' → k s' ⦃ Q ⦄) :
    (do
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      k s4) ⦃ Q ⦄ := by
  have hP := hP0.e
  obtain ⟨hR, hSRT⟩ := hX
  have hx2 := hR.toN.at_ntfn hnN hkn
  obtain ⟨xs, hQ, hxs, hB⟩ := hx2.obj.queue
  have hxs' : xs = t :: rest := by
    have h1 : xn.ntfnObj.ntfnQueue = (t :: rest).map UScalar.bv := hq
    rw [hxs] at h1
    exact List.map_injective_iff.2 (fun a b h => eq_of_bv h) h1
  subst hxs'
  have ht : t ∈ T := hQ.mem t (by simp)
  have htxs : t ∈ t :: rest := by simp
  have hta := hP.tcb t ht
  obtain ⟨x, hk, hx⟩ := hR.tcb t ht
  have hqn : t.bv ∈ Fl4Spec.ntfnQueueOf xn := by rw [hq]; simp
  have htn : t.bv ≠ n.bv := by intro h; rw [h, hkn] at hk; cases hk
  have hnd := hQ.nodup
  have hb1 : L.mem s (tBlockA t) = n := (hB t htxs).2
  have hst6 : (L.mem s (tStA t)).val = 6 := (hB t htxs).1
  -- the dequeue
  refine WP.spec_bind (ntfn_dequeue_full hP0.n s hnN t (t :: rest) hQ htxs) ?_
  rintro s2 ⟨hA1, hA2, hA3⟩
  have hSS1 : IFrame (L := L) th s s2 :=
    IRel.iframe_of ⟨hR, hSRT⟩ hA3.foot fun b hb => iwords_oobj (NWrite.iwords hP.tcb hb)
  obtain ⟨q', hq'⟩ : ∃ q', Fl4Spec.removeAll t.bv (Fl4Spec.ntfnQueueOf xn) = q' := ⟨_, rfl⟩
  have herase : (t :: rest).erase t = rest := List.erase_cons_head t rest
  have hrm : q' = rest.map UScalar.bv := by
    rw [← hq', hq, removeAll_map hnd t, herase]
  set xn' : Fl4Spec.Notification :=
    { xn with ntfnObj := if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q' } with hxn'
  have hdeq : Fl4Spec.tcbNtfnDequeue (Z := Unit) t.bv n.bv σ = ({((), updK σ n.bv (.notification xn'))}, False) := by
    rw [tcbNtfnDequeue_eq hkn hqn, hq', hxn']
    cases q' <;> simp [Fl4Spec.ntfnObjUpdate]
  set σ2 := updK σ n.bv (.notification xn') with hσ2
  have hbw : ∀ w ∈ t :: rest, w ∈ T ∧ L.mem s (tBlockA w) = n := fun w hw => ⟨hQ.mem w hw, (hB w hw).2⟩
  rw [herase] at hA1 hA2
  have hR2 : IpcRel N T E R B (L.mem s2) σ2 := by
    refine hR.upd_ntfn hP0 hnN _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
        (fun w hw => by
          obtain ⟨hwT, hwb⟩ := hbw w hw
          have hwa := hP.tcb w hwT
          exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
            fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
        (fun e => hnw (e ▸ (nw_words hP0 hnN).1)) (fun e => hnw (e ▸ (nw_words hP0 hnN).2.1)))
      ⟨?_, ?_, ?_, ?_⟩
    · show NtfnObjRel _ T n (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q')
      by_cases hemp : rest = []
      · have : q' = [] := by rw [hrm, hemp]; rfl
        rw [if_pos this]
        rw [hemp] at hA1
        exact ⟨by rw [hA2, if_pos hemp], hA1⟩
      · have hne : q' ≠ [] := by rw [hrm]; simpa using hemp
        rw [if_neg hne]
        have hstn : stOf (L.mem s) n = 1#u64 := by
          have := hx2.obj
          cases h : xn.ntfnObj with
          | idleNtfn => rw [h] at hxs; simp [Fl4Spec.Ntfn.ntfnQueue] at hxs
          | activeNtfn b => rw [h] at hxs; simp [Fl4Spec.Ntfn.ntfnQueue] at hxs
          | waitingNtfn q => rw [h] at this; exact this.1
        refine ⟨by rw [hA2, if_neg hemp]; exact hstn, rest, hemp, hrm, hA1, fun y hy => ?_⟩
        have hyx : y ∈ t :: rest := List.mem_cons_of_mem t hy
        have e := hA3.tcb y (hQ.mem y hyx)
        exact ⟨by rw [e.st]; exact (hB y hyx).1, by rw [e.blk]; exact (hB y hyx).2⟩
    · show xn.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
    · rw [hA3.bound]; exact hx2.bound_mem
    · show xn.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
  have hK := NtfnStep.ntfn (y := xn') hkn rfl rfl
  have hTW1 : FinStep (st := st) T N C c s σ s2 σ2 :=
    ⟨hA3.foot.mono fun b hb => NWrite.finW hP.tcb hb, SzKeepC.of (SzKeep.ntfnStep hK)⟩
  have hS2 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s2 σ2 :=
    ⟨hSRT.1.stableN hSRT.2.1.placed hA3.foot hK, hSRT.2.1.stable hA3.foot hK,
      hSRT.2.2.mono hA3.foot.1 (SzKeep.ntfnStep hK)⟩
  have hk2 : σ2.kheap t.bv = some (.tcb x) := by simp [hσ2, updK, htn, hk]
  have hkn2 : σ2.kheap n.bv = some (.notification xn') := by simp [hσ2, updK]
  have hb2 : (L.mem s2 (tStA t)).val = 6 := by rw [(hA3.tcb t ht).st]; exact hst6
  have hq2 : ∀ e ∈ E, ∀ z', σ2.kheap e.bv = some (.endpoint z') → t.bv ∉ z'.epQueue :=
    Notif.IpcRel.not_ep_queued hR2 (by rw [hb2]; omega)
  have hqn2 : ∀ n' ∈ N, ∀ z', σ2.kheap n'.bv = some (.notification z') → t.bv ∉ z'.ntfnObj.ntfnQueue := by
    intro n' hn' z' hz' hm
    by_cases e : n' = n
    · subst e
      rw [hkn2] at hz'; cases hz'
      change t.bv ∈ (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q').ntfnQueue at hm
      by_cases hq2 : q' = []
      · rw [if_pos hq2] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      · rw [if_neg hq2] at hm; simp only [Fl4Spec.Ntfn.ntfnQueue] at hm
        rw [hrm, mem_map_bv] at hm
        rw [← herase] at hm
        exact hnd.not_mem_erase hm
    · obtain ⟨z0, hz0, hzr⟩ := hR2.toN.ntfn n' hn'
      rw [hz'] at hz0; cases hz0
      obtain ⟨ys, -, hys, hBy⟩ := hzr.obj.queue
      rw [hys, mem_map_bv] at hm
      have hb := (hBy t hm).2
      have hbt : L.mem s2 (tBlockA t) = n := by rw [(hA3.tcb t ht).blk, hb1]
      exact e (hb.symm.trans hbt)
  -- the restart
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (WP.spec_and (set_thread_state_cq (ipcCore_top hP) hP0 hP s2 σ2 hR2.toE
    (IpcRel.toSRN hR2 hS2) ht hk2 hq2 hqn2 .restart (by decide) sched.TS_RESTART hcode)
    (set_thread_state_sfoot hS2.2.1 ht sched.TS_RESTART)) ?_
  rintro s3 ⟨⟨hE3, hS3⟩, hw3⟩
  have hSS2 : IFrame (L := L) th s2 s3 :=
    IRel.iframe_of ⟨hR2, hS2⟩ hw3 fun b hb => tfoot_oobj hS2.2.1 (Or.inl (KFoot.of_sfoot hb))
  have hX3 := IpcRel.ofSRN hE3 hS3
  set σ3 := stsAct (updK σ2 t.bv (.tcb { x with tcbState := .restart })) t.bv with hσ3
  have hTW2 : FinStep (st := st) T N C c s2 σ2 s3 σ3 :=
    ⟨hw3.mono fun b hb => Or.inl (KFoot.of_sfoot hb), SzKeepC.of (SzKeep.of_tcb (p := t.bv)
      (x' := { x with tcbState := .restart }) (fun q hq => by rw [hσ3, stsAct_kheap]; simp [updK, hq])
      (by rw [hσ3, stsAct_kheap]; simp [updK]))⟩
  have hkn3 : σ3.kheap n.bv = some (.notification xn') := by
    rw [hσ3, stsAct_kheap]; simp [updK, Ne.symm htn, hkn2]
  -- the sporadic unblock and the switch
  refine WP.spec_bind (WP.spec_and (unblock_irel hP0 s3 _ hX3 t ht) (unblock_sporadic_kfoot hX3.2.2.1 t ht)) ?_
  rintro s4 ⟨⟨σ4, hu, hf4, hv4, hX4⟩, hw4⟩
  have hSS3 : IFrame (L := L) th s3 s4 :=
    IRel.iframe_of hX3 hw4 fun b hb => tfoot_oobj hX3.2.2.1 (Or.inl hb)
  have hTW3 : FinStep (st := st) T N C c s3 σ3 s4 σ4 := by
    refine ⟨hw4.mono fun b hb => Or.inl hb, SzKeepC.of fun p y k hp => ?_⟩
    have hmem : ((), σ4) ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) σ3).1 := by
      rw [show (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) = specUnblock t.bv from rfl, hu]
      exact Set.mem_singleton _
    obtain ⟨y0, h0, -, -⟩ := MaxK.mk_unblock t.bv σ3 ((), σ4) hmem p y k hp
    exact ⟨y0, h0⟩
  -- the spec's scheduler facts at the unblock check (`ntfn_restart_mid`)
  have hF1 : SFr σ σ2 := SFr.updOther hkn (fun _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ h => by cases h) (fun _ _ h => by cases h)
  have hm1 : ∀ u ∈ t.bv :: rest.map UScalar.bv, MemOK σ2 u := fun u hu =>
    hF1.memOK (hm u (by rw [hq]; simpa using hu))
  have htl : t.bv ∉ rest.map UScalar.bv := by
    rw [mem_map_bv]; exact (List.nodup_cons.1 hnd).1
  obtain ⟨σ3', hm3', hkt3', -, hmm3, hB3, hA3, hT3⟩ :=
    ntfn_restart_mid hkn2 hk2 htl hm1 (hF1.scBack hBk) (hF1.actReady hAr (Or.inl rfl))
  have hkt3 : σ3.kheap t.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [hσ3, stsAct_kheap]; simp [updK]
  have e34 : σ3' = σ4 := by
    have hmem : ((), σ3') ∈ (specUnblock t.bv σ3).1 := by
      rw [← specSporadicAssert_eq]; unfold specSporadicAssert
      rw [nd_bind_one (show Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv σ3 = _ from
        threadGet_eq _ hkt3)]
      exact hm3'
    rw [hu] at hmem
    exact (Prod.mk.inj (Set.mem_singleton_iff.1 hmem)).2
  subst e34
  refine WP.spec_bind (WP.spec_and (switch_top hP0 s4 σ3' hX4.1 hX4.2 hA3 t ht)
    (possible_switch_to_sfootI hX4.1.toN hX4.2.2.1 hA3 ht)) ?_
  rintro s5 ⟨⟨σ5, hps, hk5, hf5, hv5, hS5⟩, hw5⟩
  have hSS4 : IFrame (L := L) th s4 s5 :=
    IRel.iframe_of hX4 hw5 fun b hb => sfootI_oobj hP.tcb hb
  have hTW4 : FinStep (st := st) T N C c s4 σ3' s5 σ5 :=
    ⟨hw5.mono fun b hb => SFootI.finW hP.tcb hb, SzKeepC.of (SzKeep.of_kheap hk5)⟩
  obtain ⟨σ6, he6, hk6, ht6, hr6, ha6⟩ := pst_ok hkt3' hA3
  have e56 : σ6 = σ5 := by
    have h : ((), σ6) ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ3').1 := by rw [he6]; rfl
    rw [hps] at h; exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
  subst e56
  have hF6 := SFr.of_heap hk6 ht6 hr6
  refine hkont s5 σ6 xn' ?_ ⟨hX4.1.frame hP0 hf5 hv5, hS5⟩ (by rw [hk5]; exact hv4.1.1 _ _ hkn3) ?_
    (((hSS1.trans hSS2).trans hSS3).trans hSS4) (((hTW1.trans hTW2).trans hTW3).trans hTW4)
    (fun u hu => hF6.memOK (hmm3 u hu)) (hF6.scBack hB3)
    (pst_actReady hA3 hT3 hk6 ht6 hr6 ha6)
  · show ((), σ6) ∈ (Fl4Spec.removeAndRestartNtfnQueuedThread (Z := Unit) t.bv n.bv σ).1
    unfold Fl4Spec.removeAndRestartNtfnQueuedThread
    rw [nd_bind_one hdeq, nd_bind_one (Notif.setThreadState_eq .restart hk2), restart_spec_eq,
      specSporadicAssert_eq, nd_bind_one hu, hps]
    rfl
  · show (if q' = [] then Fl4Spec.Ntfn.idleNtfn else Fl4Spec.Ntfn.waitingNtfn q').ntfnQueue = _
    by_cases hq0 : q' = []
    · rw [if_pos hq0, ← hrm, hq0]; rfl
    · rw [if_neg hq0, ← hrm]; rfl

end Step

/-! ## The loop -/

section Loop
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st th cr N T C E R B c) in
/-- The loop invariant: the queue still to visit is the notification's,
from FL4's next thread, the spec's outcomes from it among the whole's. -/
def SInv (n : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x : S × U64 × U64) : Prop :=
  ∃ σ' xn, ∃ rest : List U64, IRel st th cr N T C E R B c x.1 σ' ∧ σ'.kheap n.bv = some (.notification xn) ∧
    Fl4Spec.ntfnQueueOf xn = rest.map UScalar.bv ∧ x.2.1 = rest.headD 0#u64 ∧ rest.length ≤ x.2.2.val ∧
    (∀ z, z ∈ (Fl4Spec.NonDet.mapMx (rrn n) (rest.map UScalar.bv) σ').1 →
      z ∈ (Fl4Spec.NonDet.mapMx (rrn n) q0 σ0).1) ∧ IFrame (L := L) th s0 x.1 ∧ FinStep (st := st) T N C c s0 σ0 x.1 σ' ∧
    (∀ u ∈ rest.map UScalar.bv, MemOK σ' u) ∧ ScBack σ' ∧ ActReady σ'

set_option maxHeartbeats 4000000 in
/-- **The loop of `cancel_all_signals`** on `IRel`. -/
theorem signals_loop (hP0 : IPlaced N T E R B)
    {n : U64} (hnN : n ∈ N) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x0 : S × U64 × U64)
    (h0 : SInv st th cr N T C E R B c n s0 σ0 q0 x0) :
    notification.cancel_all_signals_loop st x0.1 n x0.2.1 x0.2.2 ⦃ s' => ∃ σf,
      ((), σf) ∈ (Fl4Spec.NonDet.mapMx (rrn n) q0 σ0).1 ∧ IRel st th cr N T C E R B c s' σf ∧
      IFrame (L := L) th s0 s' ∧ FinStep (st := st) T N C c s0 σ0 s' σf ∧ ActReady σf ⦄ := by
  have hP := hP0.e
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 × U64 => x.2.2.val)
    (inv := SInv st th cr N T C E R B c n s0 σ0 q0) _ _ x0 ?_ h0
  rintro ⟨s, t, fuel⟩ ⟨σ', xn, rest, hX, hkn, hq, ht, hlen, hinc, hss, htw, hm, hBk, hAr⟩
  simp only at hX hkn hq ht hlen hinc hss htw hm hBk hAr ⊢
  have hx2 := hX.1.toN.at_ntfn hnN hkn
  obtain ⟨xs, hQ, hxs, -⟩ := hx2.obj.queue
  have hxs' : xs = rest := by
    have h1 : xn.ntfnObj.ntfnQueue = rest.map UScalar.bv := hq
    rw [hxs] at h1
    exact List.map_injective_iff.2 (fun a b h => eq_of_bv h) h1
  subst hxs'
  unfold notification.cancel_all_signals_loop.body
  step with obj.Tcb.is_null.spec as ⟨bn, hbn⟩
  cases xs with
  | nil =>
    simp only [List.headD_nil] at ht
    subst ht
    simp only [hbn, decide_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ', hinc _ rfl, hX, hss, htw, hAr⟩
  | cons t0 rest' =>
    simp only [List.headD_cons] at ht
    subst t
    have ht00 : t0 ≠ 0#u64 := hQ.ne0 hP.tcb t0 (by simp)
    simp only [hbn, ht00, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hf0 : fuel > 0#u64 := by
      simp only [List.length_cons] at hlen
      show (0#u64 : U64).val < fuel.val; simp; omega
    simp only [hf0, ↓reduceIte]
    step as ⟨fuel1, hfuel1⟩
    -- the successor
    have hseg := hQ.seg
    rw [show t0 :: rest' = [] ++ t0 :: rest' from rfl, Seg_mid] at hseg
    obtain ⟨-, -, hnext, -⟩ := hseg
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨nx, hnx⟩
    try simp only [bind_ok]
    refine ntfn_restart_irel hP0 s σ' hX hnN hkn hq (by rw [hq]; exact hm) hBk hAr _
      fun s4 σ'' xn' hres hX4 hkn4 hq4 hss4 htw4 hm4 hB4 hA4 => ?_
    rw [WP.spec_ok]
    refine ⟨⟨σ'', xn', rest', hX4, hkn4, hq4, by rw [hnx, hnext], ?_, ?_, hss.trans hss4, htw.trans htw4, hm4, hB4,
      hA4⟩, ?_⟩
    · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
    · exact fun z hz => hinc z (by rw [List.map_cons]; exact mapMx_cons_mem (l := rest'.map UScalar.bv) hres z hz)
    · rw [hfuel1]; scalar_tac

set_option maxHeartbeats 4000000 in
/-- **`cancel_all_signals` on `IRel`.** -/
theorem cancel_all_signals_irel (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hnN : n ∈ N)
    (hpre : Sched.NtfnQPre σ n.bv) :
    notification.cancel_all_signals st s n ⦃ s' => ∃ σ',
      ((), σ') ∈ (Fl4Spec.cancelAllSignals (Z := Unit) n.bv σ).1 ∧ IRel st th cr N T C E R B c s' σ' ∧
      IFrame (L := L) th s s' ∧ FinStep (st := st) T N C c s σ s' σ' ⦄ := by
  have hP := hP0.e
  obtain ⟨xn, hkn, hx2⟩ := hX.1.toN.ntfn n hnN
  obtain ⟨hm0, hB0, hA0⟩ := hpre xn hkn
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨i, hi⟩
  rw [epState_eq] at hi
  have hsp : Fl4Spec.cancelAllSignals (Z := Unit) n.bv σ = (match xn.ntfnObj with
        | .waitingNtfn queue => (do Fl4Spec.NonDet.mapMx (fun t => Fl4Spec.removeAndRestartNtfnQueuedThread t n.bv)
                                      queue
                                    Fl4Spec.rescheduleRequired)
        | _ => return ()) σ := by
    unfold Fl4Spec.cancelAllSignals
    rw [nd_bind_one (getNotification_eq hkn)]
    rfl
  have hob := hx2.obj
  cases hxo : xn.ntfnObj with
  | idleNtfn =>
    rw [hxo] at hob
    have h0 : i ≠ obj.NTFN_WAITING := by rw [hi, hob.1]; unfold obj.NTFN_WAITING; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp, hxo]; rfl, hX, IFrame.refl _ _, FinStep.refl _ _⟩
  | activeNtfn b =>
    rw [hxo] at hob
    have h0 : i ≠ obj.NTFN_WAITING := by rw [hi, hob.1]; unfold obj.NTFN_WAITING; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp, hxo]; rfl, hX, IFrame.refl _ _, FinStep.refl _ _⟩
  | waitingNtfn q =>
    rw [hxo] at hob
    obtain ⟨h1, xs, -, hqx, hQ, -⟩ := hob
    have h0 : i = obj.NTFN_WAITING := by rw [hi, h1]; unfold obj.NTFN_WAITING; rfl
    simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    step with notification.get_queue.spec as ⟨qq, hqq⟩
    have hfuel : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
    have hI0 : SInv st th cr N T C E R B c n s σ q (s, qq.head, layout.WALK_FUEL) :=
      ⟨σ, xn, xs, hX, hkn, by show xn.ntfnObj.ntfnQueue = _; rw [hxo, hqx]; rfl,
        by rw [hqq, epQ_eq, hQ.head], by rw [hfuel]; exact len_le_max xs hQ.nodup (hQ.ne0 hP.tcb),
        fun z hz => by rw [hqx]; exact hz, IFrame.refl _ _, FinStep.refl _ _,
        fun u hu => hm0 u (by show u ∈ xn.ntfnObj.ntfnQueue; rw [hxo]; show u ∈ q; rw [hqx]; exact hu), hB0, hA0⟩
    refine WP.spec_bind (signals_loop hP0 hnN s σ q _ hI0) ?_
    rintro s1 ⟨σf, hmf, hXf, hss1, htw1, hAf⟩
    refine WP.spec_mono (WP.spec_and (resched_irel hP0 s1 σf hXf hAf)
      (reschedule_required_sfootI hXf.2.2.1)) ?_
    rintro s2 ⟨⟨σr, hrs, hkr, hX2⟩, hw2⟩
    refine ⟨σr, ?_, hX2, hss1.trans (IRel.iframe_of hXf hw2 fun b hb => sfootI_oobj hP.tcb hb),
      htw1.trans ⟨hw2.mono fun b hb => SFootI.finW hP.tcb hb, SzKeepC.of (SzKeep.of_kheap hkr)⟩⟩
    rw [hsp, hxo]
    exact ⟨((), σf), hmf, by show ((), σr) ∈ (Fl4Spec.rescheduleRequired σf).1; rw [hrs]; rfl⟩

end Loop

end

end Fl4Proofs.P3.Ipc
