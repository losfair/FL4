/-
P3 (DESIGN.md §9), invariant line G1 (ft3): **`B` across `set_priority`,
`receive_ipc` and `do_reply_transfer`** (spec side only).

* `set_priority t`: the thread's state is read first; a runnable or
  non-notification state leaves only frame writes; a BlockedOnNotification
  thread has no fault, is not BoS/BoReply and (the threads of `K` are never
  BlockedOnNotification) is not in `K`; the frame keeps these per-thread facts
  (`TT`), and `reorder_ntfn` re-adds it to the queue (`b_reorderNtfn`).
* `receive_ipc t` (receiver in `L`, not exempt): a sender read BlockedOnSend
  is in no queue (NQB) and joins `K`; its fault read decides between
  `reply_push` / Inactive (fault-holding states) and Running (no fault: it
  joins `L`); otherwise the receiver blocks (`b_receiveIpcBlocked`).
* `do_reply_transfer`: the receiver is read BlockedOnReply (so in no queue: it
  joins `K`); with no fault it joins `L` and becomes Running; with one the
  fault is cleared (it joins `L`) and it becomes Restart / Inactive. After
  that write it is active or in a fault state (`fqC`, kept by the frame), so
  when it is read runnable it is active and may be exempt for
  `handle_timeout`, whose post drops it from `L`. The caller's `L` holds no
  BlockedOnReply thread (`NoRpl L`), so the receiver was not in it.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L E K : List ObjRef} {C : ObjRef → Prop}

/-! ## Carrying a frame-kept fact beside `B` -/

/-- At `c`: active or in a fault state. -/
def fqC (c : ObjRef) : FQ where
  R p _ s := p = c → activeSt s ∨ faultTcbSt s
  clr _ _ _ h := h
  st _ _ _ _ _ := Or.inr trivial
  dflt _ _ := Or.inr trivial

/-- `B` and an `OPG F` fact, kept by every frame function. -/
theorem bf_of_gf {F : FQ} {α : Type} {m : NonDet (State Unit) α} (h : GF C m) :
    IK (fun σ => B L E K C σ ∧ OPG F Set.univ C σ) m :=
  fun σ hσ y hy => ⟨b_of_gf h σ hσ.1 y hy, h F _ σ hσ.2 y hy⟩

/-- At `t`: no fault and not BoS/BoReply. -/
def TT (t : ObjRef) (σ : State Unit) : Prop :=
  ∀ y, σ.kheap t = some (.tcb y) → y.tcbFault = none ∧ ¬ sndRpl y.tcbState

theorem bt_of_gf {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : GF C m) :
    IK (fun σ => B L E K C σ ∧ TT t σ) m :=
  fun σ hσ y hy => ⟨b_of_gf h σ hσ.1 y hy, (gf_post h hσ.1.1.2 hy).2.1 t hσ.2⟩

theorem hk_post {P Q Q' : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HK P Q m)
    (hq : ∀ s, Q s → Q' s) : HK P Q' m :=
  fun σ hσ y hy => hq _ (h σ hσ y hy)

theorem hk_pre {P P' Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HK P Q m)
    (hp : ∀ s, P' s → P s) : HK P' Q m :=
  fun σ hσ y hy => h σ (hp σ hσ) y hy

/-! ## `set_priority` -/

theorem b_setPriority (t : ObjRef) (prio : Priority) : BK L E K C (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState
  refine ik_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState
  case blockedOnNotification n =>
    try dsimp only
    rw [if_neg (by simp [runnable])]
    intro hσ
    have hK : t ∉ K := fun h => (hσ.2.2 t h).2 x hx (by rw [hs]; trivial)
    have ht : TT t σ := fun z hz => by
      rw [hx] at hz; cases hz
      exact ⟨b_noFault hσ hx (by rw [hs]; exact fun h => h) (by rw [hs]; exact fun h => h),
        by rw [hs]; exact fun h => h⟩
    refine (hk_bind (R := fun s => B L E K C s ∧ TT t s) (bt_of_gf fun _ _ => by fg_auto) fun _ =>
      hk_bind (R := fun s => B L E K C s ∧ TT t s) (bt_of_gf fun _ _ => by fg_auto) fun _ => ?_) σ ⟨hσ, ht⟩
    exact fun s hs' y hy => b_reorderNtfn n t hK hs'.1 hs'.2 hy
  all_goals
    simp only [runnable, epBlocked, ntfnBlocked, NonDet.maybeM, Bool.false_eq_true, ↓reduceIte]
    exact ikp_of_ik (b_of_gf fun _ _ => by fg_auto) σ
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_setPriority _ _)

/-! ## `receive_ipc` -/

theorem ik_fail_bind {P : State Unit → Prop} {α β : Type} {g : α → NonDet (State Unit) β} :
    IK P ((NonDet.fail : NonDet (State Unit) α) >>= g) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

/-- `b_auto`, closing a failing branch at once and an `if` branch whose
condition simplifies to `False`. -/
macro "b_auto3" : tactic => `(tactic| repeat' (first | b_leaf | (with_reducible exact ik_fail_bind) | b_rd | (show IK _ (ite _ _ _); split <;> try (rename_i hsplit; simp at hsplit; done)) | (show IK _ (ite _ _ _ >>= _); split <;> try (rename_i hsplit; simp at hsplit; done)) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (exfalso; contradiction)))

set_option maxHeartbeats 4000000 in
theorem b_receiveIpc (t : ObjRef) (cap : Cap) (blk : Bool) (rc : Cap) (hL : t ∈ L) (hE : t ∉ E) :
    BK L E K C (receiveIpc (Z := Unit) t cap blk rc) := by
  unfold receiveIpc; b_auto3

/-! ## `do_reply_transfer` -/

/-- BlockedOnReply. -/
def isBoR : ThreadState → Prop
  | .blockedOnReply _ => True
  | _ => False

/-- No thread of `L` is BlockedOnReply. -/
def NoRpl (L : List ObjRef) (σ : State Unit) : Prop :=
  ∀ u ∈ L, ∀ x, σ.kheap u = some (.tcb x) → ¬ isBoR x.tcbState

/-- `set_thread_state` with an active or fault-holding state: afterwards `fqC t`. -/
theorem b_sts_C (t : ObjRef) (ts : ThreadState)
    (h1 : faultTcbSt ts ∨ t ∈ L ∨ (t ∈ E ∧ activeSt ts)) (h2 : t ∈ K → ¬ isBoN ts)
    (h3 : ¬ sndRpl ts ∨ t ∈ K) (h4 : t ∈ E → activeSt ts ∨ faultTcbSt ts) (h5 : activeSt ts ∨ faultTcbSt ts) :
    HK (B L E K C) (fun s => B L E K C s ∧ OPG (fqC t) Set.univ C s) (setThreadState (Z := Unit) t ts) := by
  intro σ hσ y hy
  have hb := b_setThreadState t ts h1 h2 h3 h4 σ hσ y hy
  refine ⟨hb, fun p o hp => ?_, hb.1.2⟩
  cases o with
  | tcb z => intro e; subst e; rw [sts_post hy z hp]; exact h5
  | notification _ => exact fun _ _ => Set.mem_univ _
  | _ => trivial

theorem b_replyTail (receiver : ObjRef) (fault : Option Fault) (hL : receiver ∈ L) (hK : receiver ∈ K) :
    HK (fun σ => B L E K C σ ∧ OPG (fqC receiver) Set.univ C σ) (B (L.filter (· ≠ receiver)) E K C) (do
        let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext receiver
        let state ← getThreadState receiver
        NonDet.when (scOpt ≠ none ∧ runnable state) <| do
          let scPtr ← NonDet.assertOpt scOpt
          let sc ← getSchedContext scPtr
          let curtime ← NonDet.gets fun s : State Unit => s.curTime
          if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
          then possibleSwitchTo receiver
          else do
            let tcb ← NonDet.getsThe (getTcb receiver)
            if isEpCap tcb.tcbTimeoutHandler ∧ ¬(fault.elim false isTimeoutFault = true)
            then handleTimeout receiver (.timeout sc.scBadge)
            else postpone scPtr) := by
  have hfin : ∀ {σ'}, B L E K C σ' → B (L.filter (· ≠ receiver)) E K C σ' :=
    fun h => b_mono h (fun u hu => (mem_filter_ne hu).1) (fun _ h => h) id
  refine hk_bind (hk_of_ik (bf_of_gf fun _ _ => by fg_auto)) fun scOpt => ?_
  unfold getThreadState
  refine hk_threadGet_bind fun σ x hx => ?_
  intro hσ y hy
  try dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hc
    have hact : activeSt x.tcbState := by
      have h1 := hc.2
      have h2 := hσ.2.1 receiver _ hx rfl
      revert h1 h2; cases x.tcbState <;> simp [runnable, activeSt, faultTcbSt]
    have hE : B L (receiver :: E) K C σ := b_addE hσ.1 fun z hz => by rw [hx] at hz; cases hz; exact Or.inl hact
    refine (?_ : HK (B L (receiver :: E) K C) (B (L.filter (· ≠ receiver)) E K C) _) σ hE y hy
    refine hk_bind (hk_of_ik (by b_auto)) fun scPtr => hk_bind (hk_of_ik (by b_auto)) fun sc =>
      hk_bind (hk_of_ik (by b_auto)) fun ct => ?_
    split
    · exact fun s hs y hy => hfin (hk_dropL (by b_auto) hL s hs y hy)
    · refine hk_bind (hk_of_ik (by b_auto)) fun tcb => ?_
      split
      · exact b_handleTimeout receiver _ hL hK
      · exact fun s hs y hy => hfin (hk_dropL (by b_auto) hL s hs y hy)
  · rw [Set.mem_singleton_iff.1 hy]; exact hfin hσ.1

theorem filter_cons_sub {r : ObjRef} : ∀ u ∈ L.filter (· ≠ r), u ∈ (r :: L).filter (· ≠ r) := by
  intro u hu
  have := mem_filter_ne hu
  simp only [List.mem_filter, List.mem_cons, decide_eq_true_eq]
  exact ⟨Or.inr this.1, this.2⟩

set_option maxHeartbeats 4000000 in
theorem b_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    HK (fun σ => B L E K C σ ∧ NoRpl L σ) (B L E K C) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine hk_bind (hk_of_ik (by repeat' (first | ik_step0 | ik_unfold))) fun ro => ?_
  cases ro with
  | none => exact fun σ h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h.1
  | some receiver =>
    show HK _ _ (getThreadState (Z := Unit) receiver >>= _)
    unfold getThreadState
    refine hk_threadGet_bind fun σ x hx => ?_
    cases hs : x.tcbState
    case blockedOnReply r' =>
      dsimp only
      intro ⟨hσ, hR⟩
      have hnL : ∀ u ∈ L, u ∈ L.filter (· ≠ receiver) := by
        intro u hu
        simp only [List.mem_filter, decide_eq_true_eq]
        refine ⟨hu, fun e => ?_⟩
        subst e
        exact hR u hu x hx (by rw [hs]; trivial)
      have hσK : B L E (receiver :: K) C σ := by
        refine ⟨hσ.1, hσ.2.1, fun u hu => ?_⟩
        rcases List.mem_cons.1 hu with rfl | hu
        · refine ⟨fun hq => (hσ.2.1 u hq x hx).2 (by rw [hs]; trivial), fun z hz => ?_⟩
          rw [hx] at hz; cases hz; rw [hs]; exact fun h => h
        · exact hσ.2.2 u hu
      have hrK : receiver ∈ receiver :: K := (List.mem_cons_self ..)
      refine fun y hy => b_mono ((?_ : HK (B L E (receiver :: K) C)
        (B (L.filter (· ≠ receiver)) E (receiver :: K) C) _) σ hσK y hy) (fun u hu => hnL u hu)
        (fun _ h => List.mem_cons_of_mem _ h) id
      refine hk_bind (hk_of_ik (ik_assert _)) fun _ => hk_bind (hk_of_ik (by b_auto)) fun _ =>
        hk_bind (hk_of_ik (by b_auto)) fun _ => hk_bind (hk_of_ik (by b_auto)) fun _ => ?_
      refine hk_threadGet_bind fun σ1 x1 hx1 => ?_
      (try dsimp only)
      cases hf : x1.tcbFault with
      | none =>
        refine hkp_bcons (fun _ y hy => by rw [hx1] at hy; cases hy; exact hf) ?_
        refine hk_bind (hk_of_ik (by b_auto)) fun _ => ?_
        refine hk_bind (b_sts_C receiver .running (Or.inr (Or.inl (List.mem_cons_self ..))) (fun _ h => h)
          (Or.inl fun h => h) (fun _ => Or.inl trivial) (Or.inl trivial)) fun _ => ?_
        exact hk_post (b_replyTail receiver none (List.mem_cons_self ..) hrK) fun s hs => b_mono hs filter_cons_sub
          (fun _ h => h) id
      | some f =>
        refine hkp_of_hk ?_ σ1
        refine hk_bind (hk_of_ik (by b_auto)) fun _ => hk_bind (hk_of_ik (by b_auto)) fun _ =>
          hk_bind (hk_of_ik (by b_auto)) fun _ => hk_bind (hk_of_ik (by b_auto)) fun rs => ?_
        refine hk_bind (b_hk_clearFault receiver) fun _ => ?_
        refine hk_bind (b_sts_C receiver (if rs then .restart else .inactive) (Or.inr (Or.inl (List.mem_cons_self ..)))
          (fun _ => by cases rs <;> exact fun h => h) (Or.inl (by cases rs <;> exact fun h => h))
          (fun _ => by cases rs <;> first | exact Or.inl trivial | exact Or.inr trivial)
          (by cases rs <;> first | exact Or.inl trivial | exact Or.inr trivial)) fun _ => ?_
        exact hk_post (b_replyTail receiver (some f) (List.mem_cons_self ..) hrK) fun s hs => b_mono hs filter_cons_sub
          (fun _ h => h) id
    all_goals
      dsimp only
      exact fun h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h.1

end

end Fl4Proofs.P3.SInv
