/-
P3 (DESIGN.md §9), invariant line G1 (rd8h, KENTRY-PLAN rd8f handoff 1):
**the readiness frame across a fault-handler slot deletion** (spec side only,
outside the JAtZ cone).

`invoke_tcb`'s ThreadControlSched installs the fault handler (deleting the
target's slot 3) before `set_priority` (rd8b's `rd_setPriority` needs `CtRdy`)
and the SC bind (`rd_schedContextBindTcb` needs `BindRel`), both read at the
perform. By `VfhAll` slot 3 holds a null or endpoint cap, so the deletion
finalises at most an endpoint (`cancel_all_ipc`).

* **`MF s s'`** (the readiness-monotone frame): every released SC of `s` is a
  released SC of `s'` (same size); every TCB of `s'` was a TCB of `s` with the
  same SC binding, `BlkR` only lost; every SC of `s'` was one of `s` with the
  same bound TCB. `MFK m := ∀ σ0, IK (MF σ0) m`.
* Leaves: rd8c's `BK` view (`MF.of_bk`: TCB state / fault / SC, SC objects,
  time), heap-and-time frames (`mfk_of_kt`), `mfk_setThreadState` (a state no
  fault makes `BlkR`), `mf_refillUnblockCheck` / `mfk_ifCond` (the rewritten
  head is at the current time, the refill max kept: released stays released;
  rd's `ruc_out`); `bk_setCap`, `bk_emptySlot`, `bk_capInsert`.
* **`mfk_cancelAllIpc`** (`mf_auto`), **`mf_capDelete_fh`** (sb2's
  `sbp_capDelete_fh` skeleton: `rec_del` once, the endpoint's remainder null),
  **`mf_installTcbCap3`**.
* **`bindRel_mf`**, **`rdyT_mf`**: `BindRel` and `RdyT` along `MF`.
-/
import Fl4Proofs.P3.SpecInvRd8fC
import Fl4Proofs.P3.SpecInvRd8cV
import Fl4Proofs.P3.SpecInvRd8cD
import Fl4Proofs.P3.SpecInvSbX3
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8
open Fl4Proofs.P3.SInvE Fl4Proofs.P3.Notif

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The frame -/

/-- **The readiness-monotone frame** (module docstring). -/
structure MF (s s' : State Unit) : Prop where
  rel : ∀ p y n, s.kheap p = some (.schedContext y n) → scReleased s.curTime y = true →
    ∃ y', s'.kheap p = some (.schedContext y' n) ∧ scReleased s'.curTime y' = true
  tcb : ∀ q x', s'.kheap q = some (.tcb x') → ∃ x, s.kheap q = some (.tcb x) ∧
    x'.tcbSchedContext = x.tcbSchedContext ∧ (BlkR x'.tcbState x'.tcbFault → BlkR x.tcbState x.tcbFault)
  sc : ∀ p y' n, s'.kheap p = some (.schedContext y' n) →
    ∃ y, s.kheap p = some (.schedContext y n) ∧ y'.scTcb = y.scTcb

theorem MF.refl (s : State Unit) : MF s s :=
  ⟨fun _ y _ h hr => ⟨y, h, hr⟩, fun _ x h => ⟨x, h, rfl, id⟩, fun _ y _ h => ⟨y, h, rfl⟩⟩

theorem MF.trans {s1 s2 s3 : State Unit} (a : MF s1 s2) (b : MF s2 s3) : MF s1 s3 := by
  refine ⟨fun p y n h hr => ?_, fun q x h => ?_, fun p y n h => ?_⟩
  · obtain ⟨y2, h2, r2⟩ := a.rel p y n h hr; exact b.rel p y2 n h2 r2
  · obtain ⟨x2, h2, e2, b2⟩ := b.tcb q x h
    obtain ⟨x1, h1, e1, b1⟩ := a.tcb q x2 h2
    exact ⟨x1, h1, e2.trans e1, fun hb => b1 (b2 hb)⟩
  · obtain ⟨y2, h2, e2⟩ := b.sc p y n h
    obtain ⟨y1, h1, e1⟩ := a.sc p y2 n h2
    exact ⟨y1, h1, e2.trans e1⟩

theorem MF.of_bk {s s' : State Unit} (h : BKv s' = BKv s) : MF s s' := by
  have h' := h
  unfold BKv at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hT, hS, hC⟩ := h'
  refine ⟨fun p y n hy hr => ⟨y, scAt_iff.1 (by rw [hS]; exact scAt_iff.2 hy), by rw [hC]; exact hr⟩,
    fun q x' hx' => ?_, fun p y n hy => ⟨y, scAt_iff.1 (by rw [← hS]; exact scAt_iff.2 hy), rfl⟩⟩
  have e := congrFun hT q
  try simp only at e
  rw [hx'] at e
  obtain ⟨x, hx, e1, e2, e3⟩ := tcbV_some e.symm
  exact ⟨x, hx, e3.symm, fun hb => by rw [e1, e2]; exact hb⟩

/-- Every outcome of `m` is `MF`-related to its start. -/
abbrev MFK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ0, IK (MF σ0) m

theorem mfk_of_bk {α : Type} {m : NonDet (State Unit) α} (h : ∀ V, BKK V m) : MFK m :=
  fun _ s hs x hx => hs.trans (MF.of_bk (h (BKv s) s rfl x hx))

theorem bkv_of_kt {s s' : State Unit} (hk : s'.kheap = s.kheap) (ht : s'.curTime = s.curTime) :
    BKv s' = BKv s := by
  unfold BKv scAt; rw [hk, ht]

theorem bk_of_kt {α : Type} {m : NonDet (State Unit) α} (h : ∀ K T, IK (KT K T) m) {V : BKw} : BKK V m := by
  intro s hs x hx
  obtain ⟨hk, ht⟩ := h s.kheap s.curTime s ⟨rfl, rfl⟩ x hx
  unfold B8c.BK at hs ⊢
  rw [bkv_of_kt hk ht]; exact hs

theorem mfk_of_kt {α : Type} {m : NonDet (State Unit) α} (h : ∀ K T, IK (KT K T) m) : MFK m :=
  mfk_of_bk fun _ => bk_of_kt h

/-! ## The leaves -/

/-- `set_cap` keeps the BK view (a CNode slot, or a TCB cap field). -/
theorem bk_setCap (c : Cap) (sl : CslotPtr) {V : BKw} : BKK V (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ hσ x hx
  unfold setCap at hx
  obtain ⟨⟨k, σ1⟩, hy, hx⟩ := hx
  obtain ⟨hk, e1⟩ := SInv.mem_getObject hy
  dsimp only at hk e1 hx
  subst e1
  cases k with
  | cnode sz cn =>
    dsimp only at hx; split_ifs at hx
    · obtain ⟨w, hw, hx⟩ := hx
      obtain rfl := Set.mem_singleton_iff.1 hw
      obtain ⟨k, hk', -, e⟩ := mem_setObjectV hx
      rw [hk] at hk'; cases hk'
      unfold B8c.BK at hσ ⊢
      rw [e]; dsimp only
      exact (bkv_put (o := KernelObject.cnode sz (Function.update cn r (some c))) hk (fun _ _ h => by cases h)
        (fun _ _ h => by cases h) rfl).trans hσ
    · obtain ⟨_, h, _⟩ := hx; exact h.elim
  | tcb t =>
    dsimp only at hx
    split_ifs at hx <;> first
      | (obtain ⟨w, hw, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hw;
         unfold B8c.BK at hσ ⊢; rw [bk_setTcb hk hx ⟨rfl, rfl, rfl⟩]; exact hσ)
      | (obtain ⟨_, h, _⟩ := hx; exact h.elim)
  | _ => obtain ⟨_, h, _⟩ := hx; exact h.elim
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_setCap _ _)

theorem bk_rescheduleRequired {V : BKw} : BKK V (rescheduleRequired (Z := Unit)) :=
  bk_of_kt fun K T => kt_rescheduleRequired K T
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_rescheduleRequired)

theorem bk_emptySlot (sl : CslotPtr) (ci : Cap) {V : BKw} : BKK V (emptySlot (Z := Unit) sl ci) := by
  unfold emptySlot; bk_auto

theorem bk_capInsert (c : Cap) (src dst : CslotPtr) {V : BKw} : BKK V (capInsert (Z := Unit) c src dst) := by
  unfold capInsert; bk_auto

theorem bk_checkCapAt (c : Cap) (sl : CslotPtr) (m : SMonad Unit Unit) {V : BKw} (h : BKK V m) :
    BKK V (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt
  exact ik_bind (bk_getCap _) fun _ => ik_when _ h

theorem mfk_setThreadState (t : ObjRef) (ts : ThreadState) (hts : ∀ f, ¬ BlkR ts f) :
    MFK (setThreadState (Z := Unit) t ts) := by
  intro σ0 s hs y hy
  have hcf := cfk_setThreadState' t ts s y hy
  have ht : y.2.curTime = s.curTime := by
    have := hcf; simp only [cfS, Prod.mk.injEq] at this; exact this.2.2.2.2.2
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hz
  have hk : y.2.kheap = z.2.kheap := SInvR.kh_setThreadStateAct _ t z.2 rfl y hy
  rw [e] at hk
  have hkq : ∀ q, q ≠ t → y.2.kheap q = s.kheap q := fun q hq => by
    rw [hk]; exact Function.update_of_ne hq _ _
  have hkt : y.2.kheap t = some (.tcb { x with tcbState := ts }) := by
    rw [hk]; exact Function.update_self _ _ _
  refine hs.trans ⟨fun p y0 n hy0 hr => ?_, fun q x' hx' => ?_, fun p y' n hy' => ?_⟩
  · have hp : p ≠ t := by rintro rfl; rw [hx] at hy0; cases hy0
    exact ⟨y0, by rw [hkq p hp]; exact hy0, by rw [ht]; exact hr⟩
  · by_cases eq : q = t
    · subst eq; rw [hkt] at hx'; cases hx'
      exact ⟨x, hx, rfl, fun hb => absurd hb (hts _)⟩
    · rw [hkq q eq] at hx'; exact ⟨x', hx', rfl, id⟩
  · have hp : p ≠ t := by rintro rfl; rw [hkt] at hy'; cases hy'
    rw [hkq p hp] at hy'; exact ⟨y', hy', rfl⟩

theorem nb_restart (f : Option Fault) : ¬ BlkR .restart f := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩) <;> cases h

theorem nb_inactive (f : Option Fault) : ¬ BlkR .inactive f := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩) <;> cases h

/-- **`refill_unblock_check`**: the rewritten head is at the current time, the
refill max and bound TCB kept. -/
theorem mf_refillUnblockCheck {s : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : s.kheap p = some (.schedContext y n)) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p s).1) : MF s r.2 := by
  have hne := ruc_ne hk hr
  rcases ruc_out hk hne hr with e | ⟨-, z, e, -, hz2, hz3, hz4, -⟩
  · rw [e]; exact MF.refl _
  · rw [e]
    have hkq : ∀ q, q ≠ p → (Sched.updSc { s with reprogramTimer := true } p z n).kheap q = s.kheap q :=
      fun q hq => by simp [Notif.updK, hq]
    have hkp := kh_upd { s with reprogramTimer := true } p z n
    refine ⟨fun q y0 n0 hy0 hr0 => ?_, fun q x' hx' => ?_, fun q y' n' hy' => ?_⟩
    · by_cases eq : q = p
      · subst eq; rw [hk] at hy0; cases hy0
        refine ⟨z, hkp, ?_⟩
        have ha : scActive z = scActive y := by simp only [scActive, hz4]
        have hrd : refillReady s.curTime (refillHd z) = true := ready_of_nat (by rw [hz2]; try exact le_refl _)
        show scReleased s.curTime z = true
        simp only [scReleased, Bool.and_eq_true] at hr0 ⊢
        exact ⟨by rw [ha]; exact hr0.1, hrd⟩
      · exact ⟨y0, by rw [hkq q eq]; exact hy0, hr0⟩
    · have hq : q ≠ p := by rintro rfl; rw [hkp] at hx'; cases hx'
      rw [hkq q hq] at hx'; exact ⟨x', hx', rfl, id⟩
    · by_cases eq : q = p
      · subst eq; rw [hkp] at hy'; cases hy'; exact ⟨y, hk, hz3⟩
      · rw [hkq q eq] at hy'; exact ⟨y', hy', rfl⟩

theorem mfk_ifCond (o : Option ObjRef) (a b : Option Bool) : MFK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  intro σ0 s hs r hr
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hr
  cases o with
  | none =>
    obtain rfl : r = ((), s) := hr
    exact hs
  | some p =>
    dsimp only at hr
    obtain ⟨w, hw, hr⟩ := hr
    obtain ⟨⟨n, hk⟩, e1⟩ := SInvI.mem_getSchedContext_vi hw
    obtain ⟨w1, w2⟩ := w
    simp only at e1 hk hr
    subst w2
    rw [nd_gets_bind, nd_pure_bind'] at hr
    unfold NonDet.when at hr
    split_ifs at hr
    · exact hs.trans (mf_refillUnblockCheck hk hr)
    all_goals (obtain rfl : r = ((), _) := hr; exact hs)

theorem mfk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) :
    MFK (getSimpleKo (Z := Unit) f p) := mfk_of_bk fun _ => bk_getSimpleKo _ _
theorem mfk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    MFK (setSimpleKo (Z := Unit) f p e) := mfk_of_bk fun _ => bk_setSimpleKo _ _ _
theorem mfk_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : MFK (threadGet (Z := Unit) f t) :=
  mfk_of_bk fun _ => bk_threadGet _ _
theorem mfk_getTcbObjRef (f : Tcb → Option ObjRef) (t : ObjRef) : MFK (getTcbObjRef (Z := Unit) f t) :=
  mfk_of_bk fun _ => bk_getTcbObjRef _ _
theorem mfk_getThreadState (t : ObjRef) : MFK (getThreadState (Z := Unit) t) :=
  mfk_of_bk fun _ => bk_getThreadState _
theorem mfk_possibleSwitchTo (t : ObjRef) : MFK (possibleSwitchTo (Z := Unit) t) :=
  mfk_of_kt fun K T => kt_possibleSwitchTo K T t
theorem mfk_rescheduleRequired : MFK (rescheduleRequired (Z := Unit)) :=
  mfk_of_kt fun K T => kt_rescheduleRequired K T
theorem mfk_getCap (sl : CslotPtr) : MFK (getCap (Z := Unit) sl) := mfk_of_bk fun _ => bk_getCap _
theorem mfk_isFinalCap (c : Cap) : MFK (isFinalCap (Z := Unit) c) := mfk_of_bk fun _ => bk_isFinalCap _
theorem mfk_emptySlot (sl : CslotPtr) (ci : Cap) : MFK (emptySlot (Z := Unit) sl ci) :=
  mfk_of_bk fun _ => bk_emptySlot _ _

syntax "mf_leaf" : tactic
macro_rules | `(tactic| mf_leaf) => `(tactic| fail "no mf_leaf")
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_getSimpleKo _ _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_setSimpleKo _ _ _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_threadGet _ _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_getTcbObjRef _ _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_getThreadState _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_possibleSwitchTo _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_rescheduleRequired _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_ifCond _ _ _ _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_setThreadState _ _ nb_restart _)
macro_rules | `(tactic| mf_leaf) => `(tactic| with_reducible exact mfk_setThreadState _ _ nb_inactive _)

macro "mf_auto" : tactic => `(tactic| repeat' (first | mf_leaf | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- **`cancel_all_ipc`** keeps the frame. -/
theorem mfk_cancelAllIpc (e : ObjRef) : MFK (cancelAllIpc (Z := Unit) e) := by
  intro σ0; unfold cancelAllIpc; mf_auto

/-! ## `cap_delete` of a fault-handler slot -/

def MPre (σ0 : State Unit) : RecDelCall → State Unit → Prop
  | .cTEDeleteCall s _, σ => MF σ0 σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .finaliseSlotCall s _, σ => MF σ0 σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .reduceZombieCall _ _ _, _ => False

def MPost (σ0 : State Unit) : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | _, _, σ => MF σ0 σ

theorem mf_step (σ0 : State Unit) (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, SInvU.HR (MPre σ0 k) (MPost σ0 k) (f k)) (k : RecDelCall) :
    SInvU.HR (MPre σ0 k) (MPost σ0 k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hp : MF σ0 z.2 := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      try dsimp only at hy
      obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2
        rw [SInvU.mem_ret_ok hy]
        show MF σ0 x.2
        exact (ik_when _ (mfk_emptySlot _ _ σ0)) z.2 hp x hx
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
      have hb2 : MF σ0 σ2 := mfk_isFinalCap _ σ0 _ hσ.1 _ hx2
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨⟨u, σ3'⟩, hx3', e3⟩ := hx3
      have hb3 : MF σ0 σ3' := (ik_when _ (mfk_cancelAllIpc _ σ0)) σ2 hb2 _ hx3'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 e3)
      try dsimp only at hy3
      rw [if_pos (show capRemoveable Cap.nullCap s from trivial)] at hy3
      rw [SInvU.mem_ret_ok hy3]; exact hb3
  | reduceZombieCall c s e => intro σ hσ; exact hσ.elim

theorem hr_recDel_mf (σ0 : State Unit) (k : RecDelCall) :
    SInvU.HR (MPre σ0 k) (MPost σ0 k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact SInvU.hr_lfp (MPre σ0) (MPost σ0) (fun f hf k => mf_step σ0 f hf k) k

/-- **`cap_delete` of a slot holding a null or endpoint cap keeps the readiness frame.** -/
theorem mf_capDelete_fh (sl : CslotPtr) (σ : State Unit) (hc : ∀ c, SInvU.capAt σ sl = some c → SInvB.FhC c) :
    ∀ y ∈ ((capDelete (Z := Unit) sl).run σ).1, MF σ y.2 := by
  intro y hy
  unfold capDelete at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨er, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · rw [SInvU.mem_ret_ok hy]
    exact hr_recDel_mf σ (.cTEDeleteCall sl true) σ ⟨MF.refl _, hc⟩ z hz
  · exact hr_recDel_mf σ (.cTEDeleteCall sl true) σ ⟨MF.refl _, hc⟩ z hz

/-- **`install_tcb_cap` of the fault-handler slot** holding a null or endpoint cap. -/
theorem mf_installTcbCap3 (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr)) (σ : State Unit)
    (hF : fh ≠ none → ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c) :
    ∀ y ∈ ((installTcbCap (Z := Unit) t sl 3 fh).run σ).1, MF σ y.2 := by
  intro y hy
  unfold installTcbCap at hy
  rcases fh with _ | ⟨nc, src⟩
  · rw [SInvU.mem_ret_ok hy]; exact MF.refl _
  · try dsimp only at hy
    have hF' := hF (fun h => by cases h)
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' : MF σ z.2 := mf_capDelete_fh _ σ hF' z hz
      refine (ike_unlessE _ (ike_liftE ?_)) z.2 hz' y hy
      exact mfk_of_bk (fun _ => bk_checkCapAt _ _ _ (bk_checkCapAt _ _ _ (bk_capInsert _ _ _))) σ
    · exact mf_capDelete_fh _ σ hF' z hz

/-! ## What the frame carries -/

theorem bindRel_mf {σ s : State Unit} {p t : ObjRef} (hB : BindRel σ p t) (h : MF σ s) : BindRel s p t := by
  refine ⟨fun y n hy => ?_, fun x' hx' => ?_⟩
  · obtain ⟨y0, hy0, e⟩ := h.sc p y n hy; rw [e]; exact hB.1 y0 n hy0
  · obtain ⟨x, hx, e, hb⟩ := h.tcb t x' hx'
    obtain ⟨hn, hr⟩ := hB.2 x hx
    refine ⟨by rw [e]; exact hn, fun hb' => ?_⟩
    obtain ⟨y, n, hy, hy'⟩ := hr (hb hb')
    obtain ⟨y', hy1, hr1⟩ := h.rel p y n hy hy'
    exact ⟨y', n, hy1, hr1⟩

theorem rdyT_mf {σ s : State Unit} {t : ObjRef} (hT : RdyT σ t) (h : MF σ s)
    (hx : ∃ x, s.kheap t = some (.tcb x)) : RdyT s t := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨x, c, y, n, hx0, hc, hy, ha, hr⟩ := hT
  obtain ⟨x1, hx1, e, -⟩ := h.tcb t x' hx'
  rw [hx0] at hx1; cases hx1
  obtain ⟨y', hy', hr'⟩ := h.rel c y n hy (by simp only [scReleased, ha, hr, Bool.and_self])
  simp only [scReleased, Bool.and_eq_true] at hr'
  exact ⟨x', c, y', n, hx', e.trans hc, hy', hr'.1, hr'.2⟩

end

end Fl4Proofs.P3.SInvR.B8h
