/-
P3 (DESIGN.md §9), invariant line G1 (rd8l, KENTRY-PLAN rd8k handoff 3):
**ThreadControlSched's SC bind keeps `BlockedScActive` with no input**
(spec side only, outside the JAtZ cone).

rd8k left `TcbB` (BSA at every outcome of ThreadControlSched binding a new SC)
as a perform input: rd8i's `ba_schedContextBindTcb_p` needs `NotQ t ∨ PA c`
after the slot-3 deletion and the priority writes, while the decode's check
gives rd8k's `BQ σ c t` at the decode state.

* **`MQ s s'`**: every ipc-queued TCB of `s'` was an ipc-queued TCB of `s`
  ("no thread becomes ipc-queued"); `MFQ := B8h.MF ∧ MQ` (rd8h's MF is not
  edited). Leaves: rd8c's `BK` view, heap-and-time frames,
  `set_thread_state` to a non-ipc-queued state, `if_cond_refill_unblock_check`
  (rd8h's `mfk_ifCond` with rd8d's `sf_ifCond`: TCBs kept).
* `mfqk_cancelAllIpc`, **`mfq_capDelete_fh`** (rd8hA's `mf_step` /
  `hr_recDel_mf` skeleton with `MFQ`), **`mfq_installTcbCap3`**,
  `mfqk_setMcpriority` / `mfqk_setPriority`; **`bq_mfq`** (BQ along MFQ).
* **`ba_tcSchedB`**: ThreadControlSched with `some (some c)` keeps BSA from
  `KD I σ`, the slot-3 `FhAt` (VfhAll) and `BQ σ c t`.
* The decode: `okpl_bind` / `okpl_bind_pin` / `pinl_checkPrio` (rd8j's
  combinators, renamed: rd8j is on another branch),
  **`okpl_decodeUpdateSc`** (decode_update_sc returns `some (some c)` only
  with ¬ (ipc_queued ∧ ¬ released): `BQ`; the target is a TCB),
  `RqTi` / `RqT`, `okpl_decodeSetSchedParams`, `okpl_decodeTcbInvocation`,
  **`okp_fl4DecodeRqT`**, **`rqTi_perform`** (to the perform, after the
  shell's `set_thread_state ct Restart`).
* **`tcbB_of (KD I σ) (VfhAll σ) (RqTi σ i) : TcbB σ i`**, `rqD_perform`,
  **`perfB_perform`**: rd8k's `PerfB` at the perform from the decode outcome,
  `RNE` at the decode state, and `KD` / `VfhAll` at the perform (all carried).
-/
import Fl4Proofs.P3.SpecInvRd8kD
import Fl4Proofs.P3.SpecInvRd8hB
import Fl4Proofs.P3.SpecInvVfhAll
open Classical

namespace Fl4Proofs.P3.SInvR.B8l
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k
  Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvE Fl4Proofs.P3.Notif Fl4Proofs.P3.SInvB

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The "no thread becomes ipc-queued" frame -/

/-- Every ipc-queued TCB of `s'` was an ipc-queued TCB of `s`. -/
def MQ (s s' : State Unit) : Prop :=
  ∀ q x', s'.kheap q = some (.tcb x') → ipcQueuedThreadState x'.tcbState = true →
    ∃ x, s.kheap q = some (.tcb x) ∧ ipcQueuedThreadState x.tcbState = true

theorem MQ.refl (s : State Unit) : MQ s s := fun _ x h hq => ⟨x, h, hq⟩

theorem MQ.trans {s1 s2 s3 : State Unit} (a : MQ s1 s2) (b : MQ s2 s3) : MQ s1 s3 := by
  intro q x h hq
  obtain ⟨x2, h2, q2⟩ := b q x h hq
  exact a q x2 h2 q2

theorem MQ.of_bk {s s' : State Unit} (h : BKv s' = BKv s) : MQ s s' := by
  have h' := h
  unfold BKv at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hT, -, -⟩ := h'
  intro q x' hx' hq
  have e := congrFun hT q
  try simp only at e
  rw [hx'] at e
  obtain ⟨x, hx, e1, -, -⟩ := tcbV_some e.symm
  exact ⟨x, hx, by rw [e1]; exact hq⟩

abbrev MQK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ0, IK (MQ σ0) m

theorem mqk_of_bk {α : Type} {m : NonDet (State Unit) α} (h : ∀ V, BKK V m) : MQK m :=
  fun _ s hs x hx => hs.trans (MQ.of_bk (h (BKv s) s rfl x hx))

theorem mqk_of_kt {α : Type} {m : NonDet (State Unit) α} (h : ∀ K T, IK (KT K T) m) : MQK m :=
  mqk_of_bk fun _ => B8h.bk_of_kt h

theorem mqk_setThreadState (c : ObjRef) (ts : ThreadState) (hts : ipcQueuedThreadState ts = false) :
    MQK (setThreadState (Z := Unit) c ts) := by
  intro σ0 σ hs y hy
  refine hs.trans ?_
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hz
  have k : y.2.kheap = z.2.kheap :=
    (show IK (fun s => s.kheap = z.2.kheap) (setThreadStateAct (Z := Unit) c) from by
      unfold setThreadStateAct setSchedulerAction; repeat' (first | ik_step0 | ik_unfold)) z.2 rfl y hy
  intro q x' hx' hq
  rw [k, e] at hx'
  change Function.update σ.kheap c _ q = _ at hx'
  by_cases eq : q = c
  · subst eq; rw [Function.update_self] at hx'; cases hx'
    rw [hts] at hq; cases hq
  · rw [Function.update_of_ne eq] at hx'; exact ⟨x', hx', hq⟩

theorem mqk_ifCond (o : Option ObjRef) (a b : Option Bool) : MQK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  intro σ0 s hs r hr
  refine hs.trans ?_
  have hm : B8h.MF s r.2 := B8h.mfk_ifCond o a b s s (B8h.MF.refl s) r hr
  have hf := (B8d.sf_ifCond o a b s hr).2.2
  intro q x' hx' hq
  obtain ⟨x, hx, -, -⟩ := hm.tcb q x' hx'
  have e := hf q x hx
  rw [hx'] at e; cases e
  exact ⟨_, hx, hq⟩

theorem mqk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) :
    MQK (getSimpleKo (Z := Unit) f p) := mqk_of_bk fun _ => bk_getSimpleKo _ _
theorem mqk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    MQK (setSimpleKo (Z := Unit) f p e) := mqk_of_bk fun _ => bk_setSimpleKo _ _ _
theorem mqk_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : MQK (threadGet (Z := Unit) f t) :=
  mqk_of_bk fun _ => bk_threadGet _ _
theorem mqk_getTcbObjRef (f : Tcb → Option ObjRef) (t : ObjRef) : MQK (getTcbObjRef (Z := Unit) f t) :=
  mqk_of_bk fun _ => bk_getTcbObjRef _ _
theorem mqk_getThreadState (t : ObjRef) : MQK (getThreadState (Z := Unit) t) :=
  mqk_of_bk fun _ => bk_getThreadState _
theorem mqk_possibleSwitchTo (t : ObjRef) : MQK (possibleSwitchTo (Z := Unit) t) :=
  mqk_of_kt fun K T => kt_possibleSwitchTo K T t
theorem mqk_rescheduleRequired : MQK (rescheduleRequired (Z := Unit)) :=
  mqk_of_kt fun K T => kt_rescheduleRequired K T

syntax "mq_leaf" : tactic
macro_rules | `(tactic| mq_leaf) => `(tactic| fail "no mq_leaf")
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_getSimpleKo _ _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_setSimpleKo _ _ _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_threadGet _ _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_getTcbObjRef _ _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_getThreadState _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_possibleSwitchTo _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_rescheduleRequired _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_ifCond _ _ _ _)
macro_rules | `(tactic| mq_leaf) => `(tactic| with_reducible exact mqk_setThreadState _ _ rfl _)

macro "mq_auto" : tactic => `(tactic| repeat' (first | mq_leaf | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem mqk_cancelAllIpc (e : ObjRef) : MQK (cancelAllIpc (Z := Unit) e) := by
  intro σ0; unfold cancelAllIpc; mq_auto

/-! ## `MFQ` across the fault-handler slot deletion -/

/-- rd8h's readiness frame together with `MQ`. -/
def MFQ (s s' : State Unit) : Prop := B8h.MF s s' ∧ MQ s s'

theorem MFQ.refl (s : State Unit) : MFQ s s := ⟨B8h.MF.refl s, MQ.refl s⟩

abbrev MFQK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ0, IK (MFQ σ0) m

theorem mfqk_of {α : Type} {m : NonDet (State Unit) α} (h1 : B8h.MFK m) (h2 : MQK m) : MFQK m :=
  fun σ0 s hs y hy => ⟨h1 σ0 s hs.1 y hy, h2 σ0 s hs.2 y hy⟩

theorem mfqk_emptySlot (sl : CslotPtr) (ci : Cap) : MFQK (emptySlot (Z := Unit) sl ci) :=
  mfqk_of (B8h.mfk_emptySlot sl ci) (mqk_of_bk fun _ => B8h.bk_emptySlot _ _)
theorem mfqk_isFinalCap (c : Cap) : MFQK (isFinalCap (Z := Unit) c) :=
  mfqk_of (B8h.mfk_isFinalCap c) (mqk_of_bk fun _ => bk_isFinalCap _)
theorem mfqk_cancelAllIpc (e : ObjRef) : MFQK (cancelAllIpc (Z := Unit) e) :=
  mfqk_of (B8h.mfk_cancelAllIpc e) (mqk_cancelAllIpc e)
theorem mfqk_setMcpriority (t : ObjRef) (m : Priority) : MFQK (setMcpriority (Z := Unit) t m) :=
  mfqk_of (B8h.mfk_setMcpriority t m) (mqk_of_bk fun _ => bk_threadSet _ _ fun _ => ⟨rfl, rfl, rfl⟩)
theorem mfqk_setPriority (t : ObjRef) (p : Priority) : MFQK (setPriority (Z := Unit) t p) :=
  mfqk_of (B8h.mfk_setPriority t p) (mqk_of_bk fun _ => B8h.bk_setPriority t p)

def MQPre (σ0 : State Unit) : RecDelCall → State Unit → Prop
  | .cTEDeleteCall s _, σ => MFQ σ0 σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .finaliseSlotCall s _, σ => MFQ σ0 σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .reduceZombieCall _ _ _, _ => False

def MQPost (σ0 : State Unit) : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | _, _, σ => MFQ σ0 σ

theorem mfq_step (σ0 : State Unit) (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, SInvU.HR (MQPre σ0 k) (MQPost σ0 k) (f k)) (k : RecDelCall) :
    SInvU.HR (MQPre σ0 k) (MQPost σ0 k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hp : MFQ σ0 z.2 := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      try dsimp only at hy
      obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2
        rw [SInvU.mem_ret_ok hy]
        show MFQ σ0 x.2
        exact (ik_when _ (mfqk_emptySlot _ _ σ0)) z.2 hp x hx
      · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2
        rw [hx] at her; cases her
    · exact hrec (.finaliseSlotCall s e) σ hσ z hz
  | finaliseSlotCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := SInvU.mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := SInvU.getCap_capAt hx
    simp only at e1 hc
    subst e1
    have hfc := hσ.2 cap hc
    try dsimp only at hy1
    split at hy1
    · rw [SInvU.mem_ret_ok hy1]; exact hσ.1
    · rename_i hnn
      obtain ⟨r, b, rs, rfl⟩ : ∃ r b rs, cap = .endpointCap r b rs := hfc.resolve_left hnn
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      have hb2 : MFQ σ0 σ2 := mfqk_isFinalCap _ σ0 _ hσ.1 _ hx2
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨⟨u, σ3'⟩, hx3', e3⟩ := hx3
      have hb3 : MFQ σ0 σ3' := (ik_when _ (mfqk_cancelAllIpc _ σ0)) σ2 hb2 _ hx3'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 e3)
      try dsimp only at hy3
      rw [if_pos (show capRemoveable Cap.nullCap s from trivial)] at hy3
      rw [SInvU.mem_ret_ok hy3]; exact hb3
  | reduceZombieCall c s e => intro σ hσ; exact hσ.elim

theorem hr_recDel_mfq (σ0 : State Unit) (k : RecDelCall) :
    SInvU.HR (MQPre σ0 k) (MQPost σ0 k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact SInvU.hr_lfp (MQPre σ0) (MQPost σ0) (fun f hf k => mfq_step σ0 f hf k) k

/-- **`cap_delete` of a slot holding a null or endpoint cap keeps `MFQ`.** -/
theorem mfq_capDelete_fh (sl : CslotPtr) (σ : State Unit) (hc : ∀ c, SInvU.capAt σ sl = some c → SInvB.FhC c) :
    ∀ y ∈ ((capDelete (Z := Unit) sl).run σ).1, MFQ σ y.2 := by
  intro y hy
  unfold capDelete at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨er, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · rw [SInvU.mem_ret_ok hy]
    exact hr_recDel_mfq σ (.cTEDeleteCall sl true) σ ⟨MFQ.refl _, hc⟩ z hz
  · exact hr_recDel_mfq σ (.cTEDeleteCall sl true) σ ⟨MFQ.refl _, hc⟩ z hz

/-- **`install_tcb_cap` of the fault-handler slot** holding a null or endpoint cap. -/
theorem mfq_installTcbCap3 (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr)) (σ : State Unit)
    (hF : fh ≠ none → ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c) :
    ∀ y ∈ ((installTcbCap (Z := Unit) t sl 3 fh).run σ).1, MFQ σ y.2 := by
  intro y hy
  unfold installTcbCap at hy
  rcases fh with _ | ⟨nc, src⟩
  · rw [SInvU.mem_ret_ok hy]; exact MFQ.refl _
  · try dsimp only at hy
    have hF' := hF (fun h => by cases h)
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' : MFQ σ z.2 := mfq_capDelete_fh _ σ hF' z hz
      refine (ike_unlessE _ (ike_liftE ?_)) z.2 hz' y hy
      exact mfqk_of (B8h.mfk_of_bk (fun _ => B8h.bk_checkCapAt _ _ _ (B8h.bk_checkCapAt _ _ _ (B8h.bk_capInsert _ _ _))))
        (mqk_of_bk (fun _ => B8h.bk_checkCapAt _ _ _ (B8h.bk_checkCapAt _ _ _ (B8h.bk_capInsert _ _ _)))) σ
    · exact mfq_capDelete_fh _ σ hF' z hz

/-- **`BQ` along `MFQ`**: a thread ipc-queued later was ipc-queued before, and
a released SC stays released. -/
theorem bq_mfq {σ s : State Unit} {p t : ObjRef} (hB : B8k.BQ σ p t) (h : MFQ σ s) : B8k.BQ s p t := by
  intro x' hx' hq
  obtain ⟨x, hx, hq0⟩ := h.2 t x' hx' hq
  obtain ⟨y, n, hy, hr⟩ := hB x hx hq0
  obtain ⟨y', hy', hr'⟩ := h.1.rel p y n hy hr
  exact ⟨y', n, hy', hr'⟩

/-! ## ThreadControlSched binding a new SC -/

/-- The fault-handler slot of `t` holds a null or endpoint cap (sl's `FhAt`). -/
def FhAt (t : ObjRef) (σ : State Unit) : Prop :=
  ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c

theorem fhAt_of {σ : State Unit} (hV : VfhAll σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x)) :
    FhAt t σ := by
  intro c hc
  have e3 : tcbCnodeMap x (tcbCnodeIndex 3) = some x.tcbFaultHandler := by
    unfold tcbCnodeMap
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  unfold SInvU.capAt at hc
  rw [hx] at hc
  simp only [SInvU.capView, e3, Option.some.injEq] at hc
  subst hc
  exact SInvB.fhC_of_valid (hV t x hx)

variable {I : ObjRef}

/-- **ThreadControlSched with a new SC keeps `BlockedScActive`** from `KD`, the
slot-3 `FhAt` and the decode's `BQ`. -/
theorem ba_tcSchedB (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef))
    (c : ObjRef) (σ : State Unit) (hK : KD I σ) (hF : fh ≠ none → FhAt t σ) (hB : B8k.BQ σ c t) :
    ∀ y ∈ ((invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio (some (some c)))).run σ).1, BSA y.2 := by
  intro y hy
  simp only [invokeTcb] at hy
  obtain ⟨z1, hz1, ⟨u1, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · exact (kd_installTcbCap (I := I) _ _ _ _ σ hK z1 hz1).1
  have r1 : BSA z1.2 := (kd_installTcbCap (I := I) _ _ _ _ σ hK z1 hz1).1
  have m1 : MFQ σ z1.2 := mfq_installTcbCap3 t sl fh σ hF z1 hz1
  obtain ⟨z2, hz2, ⟨u2, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2; rw [hx] at he; cases he
  obtain ⟨x2, hx2, rfl⟩ := SInvU.mem_liftE' hz2
  have k2 : BSA x2.2 ∧ MFQ σ x2.2 := by
    rcases mcp with _ | ⟨m, _⟩
    · simp only [NonDet.maybeM] at hx2
      rw [Set.mem_singleton_iff.1 hx2]
      exact ⟨r1, m1⟩
    · simp only [NonDet.maybeM] at hx2
      exact ⟨ba_setMcpriority t m z1.2 r1 x2 hx2, mfqk_setMcpriority t m σ z1.2 m1 x2 hx2⟩
  obtain ⟨r2, m2⟩ := k2
  obtain ⟨z3, hz3, ⟨u3, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3; rw [hx] at he; cases he
  obtain ⟨x3, hx3, rfl⟩ := SInvU.mem_liftE' hz3
  have k3 : BSA x3.2 ∧ MFQ σ x3.2 := by
    rcases prio with _ | ⟨p, _⟩
    · simp only [NonDet.maybeM] at hx3
      rw [Set.mem_singleton_iff.1 hx3]; exact ⟨r2, m2⟩
    · simp only [NonDet.maybeM] at hx3
      exact ⟨ba_setPriority t p x2.2 r2 x3 hx3, mfqk_setPriority t p σ x2.2 m2 x3 hx3⟩
  obtain ⟨r3, m3⟩ := k3
  obtain ⟨z4, hz4, ⟨u4, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz4; rw [hx] at he; cases he
  obtain ⟨x4, hx4, rfl⟩ := SInvU.mem_liftE' hz4
  rw [SInvU.mem_ret_ok hy]
  show BSA x4.2
  simp only [NonDet.maybeM] at hx4
  exact ba_schedContextBindTcb_p c t x3.2 (nqpa_of_bq (bq_mfq hB m3)) r3 x4 hx4

/-! ## The decode: `BQ` from `decode_update_sc` -/

section OkPl
variable {ε α β : Type} {σ : State Unit}

theorem okpl_bind {P : β → Prop} {Q : α → Prop} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : OkP σ Q m) (hg : ∀ a, Q a → OkA P (g a)) :
    OkP σ P (m >>= g) := by
  intro c s hc
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hc
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    exact hg a (hm a s' hz) s' c s hy
  · simp at he

theorem okpl_bind_pin {P : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → s = σ) (hg : ∀ a, OkP σ P (g a)) :
    OkP σ P (m >>= g) := by
  intro c s hc
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hc
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have e := hm a s' hz
    subst e
    exact hg a c s hy
  · simp at he

end OkPl

theorem pinl_checkPrio (p : Data) (t : ObjRef) (σ : State Unit) :
    ∀ a s, ((.ok a, s) : Except SyscallError Unit × State Unit) ∈ ((checkPrio (Z := Unit) p t).run σ).1 →
      s = σ := by
  intro a s h
  unfold checkPrio at h
  obtain ⟨z, hz, ⟨m, hm, h⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' h
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
    obtain ⟨x', -, rfl⟩ := SInvQ.q1_mem_threadGet hx
    unfold NonDetE.whenE at h
    split at h
    · unfold NonDetE.throwError at h
      rw [ExceptT.run_throw] at h
      have e := Set.mem_singleton_iff.1 h
      simp at e
    · rw [ExceptT.run_pure] at h
      have e := Set.mem_singleton_iff.1 h
      simp only [Prod.mk.injEq] at e
      exact e.2
  · simp at he

/-- **`decode_update_sc`** returns `some (some c)` only when ¬ (ipc_queued ∧ ¬
released) at the decode's state (`BQ`); the target is a TCB. -/
theorem okpl_decodeUpdateSc (σ : State Unit) (hN : SInvB.RNE σ) (cap : Cap) (slot : CslotPtr) (scCap : Cap) :
    OkP σ (fun r => (∃ x, σ.kheap (objRefOf cap) = some (.tcb x)) ∧
        ∀ c, r = some (some c) → B8k.BQ σ c (objRefOf cap))
      (decodeUpdateSc (Z := Unit) cap slot scCap) := by
  unfold decodeUpdateSc
  refine okp_returnOk_bind ?_
  refine okp_liftE_bind (Q := fun o => ∃ x, σ.kheap (objRefOf cap) = some (.tcb x) ∧ o = x.tcbSchedContext)
    (fun y hy => ?_) fun tcbSc ⟨x, hx, ho⟩ => ?_
  · unfold getTcbObjRef at hy
    obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hy
    exact ⟨rfl, x, hx, rfl⟩
  (try dsimp only)
  cases scCap
  case nullCap =>
    refine okp_liftE_bind (Q := fun _ => True) (fun y hy => ⟨by rw [Set.mem_singleton_iff.1 hy], trivial⟩)
      fun _ _ => ?_
    refine okp_whenE_bind fun _ => okp_returnOk_bind (okp_returnOk ⟨⟨x, hx⟩, fun c hc => ?_⟩)
    split_ifs at hc <;> cases hc
  case schedContextCap scp sz =>
    refine okp_returnOk_bind ?_
    refine okp_liftE_bind (Q := fun o => ∃ y n, σ.kheap (objRefOf (Cap.schedContextCap scp sz)) =
        some (.schedContext y n) ∧ o = y.scTcb) (fun z hz => ?_) fun scTcb ⟨y, n, hy, hs⟩ => ?_
    · obtain ⟨e, y, n, hk, h⟩ := SInvQ.cq5_mem_getScObjRef hz
      exact ⟨e, y, n, hk, h⟩
    refine okp_whenE_bind fun h1 => ?_
    refine okp_liftE_bind (Q := fun bl => bl = ipcQueuedThreadState x.tcbState) (fun z hz => ?_)
      fun bl hbl => ?_
    · unfold isBlocked NonDet.liftM getThreadState at hz
      obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨x', hx', rfl⟩ := SInvQ.q1_mem_threadGet hw
      rw [hx] at hx'; cases hx'
      rw [Set.mem_singleton_iff.1 hz]
      exact ⟨rfl, rfl⟩
    refine okp_liftE_bind (Q := fun r => r = scReleased σ.curTime y) (fun z hz => ?_) fun r hr => ?_
    · rw [Sched.getScReleased_eq hy (fun ha => hN _ y n hy (Or.inr ha))] at hz
      obtain rfl := Set.mem_singleton_iff.1 hz
      exact ⟨rfl, rfl⟩
    refine okp_whenE_bind fun h3 => okp_returnOk_bind (okp_returnOk ⟨⟨x, hx⟩, fun c hc => ?_⟩)
    split_ifs at hc with hne
    simp only [Option.some.injEq] at hc
    subst hc
    intro x' hx' hq
    rw [hx] at hx'; cases hx'
    refine ⟨y, n, hy, ?_⟩
    subst hbl; subst hr
    by_contra hn
    exact h3 ⟨hq, hn⟩
  all_goals exact okp_throw_bind _

/-- ThreadControlSched's new SC satisfies `BQ` at `σ`, its target a TCB. -/
def RqTi (σ : State Unit) : TcbInvocation → Prop
  | .threadControlSched t _ _ _ _ (some (some c)) => (∃ x, σ.kheap t = some (.tcb x)) ∧ B8k.BQ σ c t
  | _ => True

theorem rqTi_tcs {σ : State Unit} {t : ObjRef} {sl : CslotPtr} {fh : Option (Cap × CslotPtr)}
    {mcp prio : Option (Word8 × ObjRef)} {sc : Option (Option ObjRef)}
    (h : ∀ c, sc = some (some c) → (∃ x, σ.kheap t = some (.tcb x)) ∧ B8k.BQ σ c t) :
    RqTi σ (.threadControlSched t sl fh mcp prio sc) := by
  rcases sc with _ | _ | c
  · trivial
  · trivial
  · exact h c rfl

theorem rqTi_tcs_inv {σ : State Unit} {t : ObjRef} {sl : CslotPtr} {fh : Option (Cap × CslotPtr)}
    {mcp prio : Option (Word8 × ObjRef)} {sc : Option (Option ObjRef)}
    (h : RqTi σ (.threadControlSched t sl fh mcp prio sc)) :
    ∀ c, sc = some (some c) → (∃ x, σ.kheap t = some (.tcb x)) ∧ B8k.BQ σ c t := by
  intro c hc
  subst hc
  exact h

def RqT (σ : State Unit) : Fl4Invocation → Prop
  | .invokeTCB i => RqTi σ i
  | _ => True

theorem okpl_decodeSetSchedParams (σ : State Unit) (hN : SInvB.RNE σ) (args : List Data) (cap : Cap)
    (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) :
    OkP σ (RqTi σ) (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams
  refine okp_whenE_bind fun _ => okp_whenE_bind fun _ => ?_
  refine okp_returnOk_bind (okp_returnOk_bind (okp_returnOk_bind (okp_returnOk_bind (okp_returnOk_bind ?_))))
  (try dsimp only)
  split
  · refine okp_returnOk_bind ?_
    refine okpl_bind_pin (pinl_checkPrio _ _ σ) fun _ => ?_
    refine okpl_bind_pin (pinl_checkPrio _ _ σ) fun _ => ?_
    refine okpl_bind (okpl_decodeUpdateSc σ hN cap slot _) fun r hr => ?_
    exact okA_bind fun fh => okA_returnOk (rqTi_tcs fun c hc => ⟨hr.1, hr.2 c hc⟩)
  · exact okp_throw_bind _

set_option maxHeartbeats 4000000 in
theorem okpl_decodeTcbInvocation (σ : State Unit) (hN : SInvB.RNE σ) (label : Data) (args : List Data)
    (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) :
    OkP σ (RqTi σ) (decodeTcbInvocation (Z := Unit) label args cap slot excs) := by
  unfold decodeTcbInvocation
  split
  case h_9 => exact okpl_decodeSetSchedParams σ hN args cap slot excs
  all_goals refine okp_of_okA ?_
  all_goals first
    | exact okA_throw _
    | exact okA_returnOk trivial
    | (unfold decodeReadRegisters; okA_auto)
    | (unfold decodeWriteRegisters; okA_auto)
    | (unfold decodeCopyRegisters; okA_auto)
    | (unfold decodeTcbConfigure; okA_auto)
    | (unfold decodeSetPriority; okA_auto)
    | (unfold decodeSetMcpriority; okA_auto)
    | (unfold decodeSetTimeoutEp; okA_auto)
    | (unfold decodeSetIpcBuffer; okA_auto)
    | (unfold decodeSetSpace; okA_auto)
    | (unfold decodeBindNotification; okA_auto)
    | (unfold decodeUnbindNotification; okA_auto)
    | (unfold decodeSetTlsBase; okA_auto)
    | (unfold decodeSetFlags; okA_auto)

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `RqT` of the decode's state.** -/
theorem okp_fl4DecodeRqT (σ : State Unit) (hN : SInvB.RNE σ) (fp : Bool) (label : Data) (args : List Data)
    (ci : CapRef) (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkP σ (RqT σ) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    refine okp_ite (okp_throw _) ?_
    unfold fl4DecodeTcbInvocation
    refine okp_ite (okp_of_okA (okA_liftME (okA_triv fun _ => trivial))) ?_
    split
    · exact okp_of_okA (okA_liftME (okA_triv fun _ => trivial))
    · exact okp_liftME (okpl_decodeTcbInvocation σ hN label args _ sl ex)
  | _ =>
    unfold fl4DecodeInvocation
    refine okp_of_okA ?_
    repeat' (first
      | exact okA_throw _ | exact okA_returnOk trivial
      | (exact okA_liftME (okA_triv fun _ => trivial))
      | (refine okA_ite ?_ ?_)
      | (dsimp only)
      | split)

/-- **A decoded TCB invocation satisfies `RqTi` at the perform** (after the
shell's `set_thread_state ct Restart`); `RNE` (sb2's `ScInv`) at the decode's
state. -/
theorem rqTi_perform {σ : State Unit} (hN : SInvB.RNE σ) {fp : Bool} {label : Data} {args : List Data}
    {ci : CapRef} {sl : CslotPtr} {cap : Cap} {ex : List (Cap × CslotPtr)} {buf : Option ObjRef}
    {i : TcbInvocation} {s : State Unit}
    (h : ((.ok (.invokeTCB i), s) : Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1)
    (c0 : ObjRef) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) c0 .restart s).1) :
    RqTi y.2 i := by
  have hD : RqTi σ i := okp_fl4DecodeRqT σ hN fp label args ci sl cap ex buf _ s h
  have hV : BKv s = BKv σ := bk_fl4DecodeInvocation (V := BKv σ) fp label args ci sl cap ex buf σ rfl _ h
  have hT : ∀ t, (∃ x, σ.kheap t = some (.tcb x)) → ∃ x, y.2.kheap t = some (.tcb x) := by
    intro t ⟨x, hx⟩
    have e := congrFun (congrArg (fun v : BKw => v.1) hV) t
    simp only [BKv] at e
    rw [hx] at e
    obtain ⟨x1, hx1, -⟩ := tcbV_some e
    have e2 := (SVK.sv_setThreadState' c0 .restart s y hy).1 t
    rw [hx1] at e2
    obtain ⟨x2, hx2, -⟩ := SVK.sv_tcb e2
    exact ⟨x2, hx2⟩
  cases i <;> try trivial
  rename_i t sl' fh mcp prio sc
  have hD' := rqTi_tcs_inv hD
  exact rqTi_tcs fun c hc => ⟨hT t (hD' c hc).1, bq_setThreadState (bq_bk hV (hD' c hc).2) c0 .restart rfl hy⟩

/-- **`TcbB` discharged**: ThreadControlSched's new SC from `KD`, `VfhAll` and
`RqTi` at the perform. -/
theorem tcbB_of (i : TcbInvocation) (σ : State Unit) (hK : KD I σ) (hV : VfhAll σ) (h : RqTi σ i) : TcbB σ i := by
  cases i <;> try trivial
  rename_i t sl fh mcp prio sc
  rcases sc with _ | _ | c
  · trivial
  · trivial
  · obtain ⟨⟨x, hx⟩, hB⟩ := rqTi_tcs_inv h c rfl
    exact ba_tcSchedB (I := I) t sl fh mcp prio c σ hK (fun _ => fhAt_of hV hx) hB

/-- rd8k's `RqD` at the perform (after `set_thread_state ct Restart`). -/
theorem rqD_perform {σ : State Unit} (hN : SInvB.RNE σ) {fp : Bool} {label : Data} {args : List Data}
    {ci : CapRef} {sl : CslotPtr} {cap : Cap} {ex : List (Cap × CslotPtr)} {buf : Option ObjRef}
    {iv : Fl4Invocation} {s : State Unit}
    (h : ((.ok iv, s) : Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1)
    (c0 : ObjRef) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) c0 .restart s).1) :
    RqD y.2 iv := by
  have hD : RqD σ iv := okp_fl4DecodeRqD σ hN fp label args ci sl cap ex buf _ s h
  have hV : BKv s = BKv σ := bk_fl4DecodeInvocation (V := BKv σ) fp label args ci sl cap ex buf σ rfl _ h
  cases iv <;> try trivial
  rename_i i
  cases i <;> try trivial
  rename_i p cap'
  cases cap' <;> try trivial
  exact bq_setThreadState (bq_bk hV hD) c0 .restart rfl hy

/-- **rd8k's `PerfB` at the perform**, every input from carried facts: `RNE`
at the decode's state, `KD` and `VfhAll` at the perform. -/
theorem perfB_perform {σ : State Unit} (hN : SInvB.RNE σ) {fp : Bool} {label : Data} {args : List Data}
    {ci : CapRef} {sl : CslotPtr} {cap : Cap} {ex : List (Cap × CslotPtr)} {buf : Option ObjRef}
    {iv : Fl4Invocation} {s : State Unit}
    (h : ((.ok iv, s) : Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1)
    (c0 : ObjRef) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) c0 .restart s).1)
    (hK : KD I y.2) (hV : VfhAll y.2) : PerfB y.2 iv := by
  have hR := rqD_perform hN h c0 hy
  have hC : CfgD iv := okv_fl4DecodeCfgD fp label args ci sl cap ex buf σ rfl _ s h
  cases iv with
  | invokeTCB i => exact tcbB_of i y.2 hK hV (rqTi_perform hN h c0 hy)
  | invokeSchedContext i => exact hR
  | invokeSchedControl i => exact hC
  | _ => trivial

end

end Fl4Proofs.P3.SInvR.B8l
