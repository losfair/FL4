/-
P3 (DESIGN.md §9), notifications: the state relation.

FL4's notification (layout.rs `ntfn`, 64 bytes) is five words: the queue
head, the queue end with the state (`NTFN_IDLE` 0, `NTFN_WAITING` 1,
`NTFN_ACTIVE` 2) in bits 0-1, the pending badge, the bound TCB (0 for none)
and the scheduling context (0 for none). The spec's (l4v Structures_A
`notification`) is `ntfn_obj` (`IdleNtfn | WaitingNtfn queue | ActiveNtfn
badge`), `ntfn_bound_tcb` and `ntfn_sc`.

Ghost state: `T`, the TCB addresses (as in P1), and `N`, the notification
addresses. Hypothesis on them (`NPlaced`, a P1 well-typed-heap invariant to
come): TCBs are placed (`TcbPlaced`), notifications are 64-byte aligned,
nonzero, do not wrap, and do not overlap a TCB.

The relation (`NtfnStateRel N T m σ`, on memory `m`):

* every `n ∈ N` is a notification `x` in the spec's heap at `n` with
  - `NtfnObjRel`: idle ↔ state 0 and the queue (P1 `QueueRel`, `Ep` links)
    is empty; active `b` ↔ state 2, empty queue, badge word `b`; waiting
    `q` ↔ state 1 and the queue holds TCBs `xs ≠ []` with `q = xs` (as
    `obj_ref`s), each of them in thread state `TS_BLOCKED_ON_NTFN` blocked on
    `n` (l4v `valid_ntfn`);
  - `ntfn_bound_tcb` and `ntfn_sc` are the bound-TCB and SC words (0 ↔
    `None`), and a nonzero bound TCB is in `T` (l4v `valid_ntfn`);
* every `t ∈ T` is a TCB `x` in the spec's heap at `t` with (`TcbRel1`):
  - the state word codes `tcb_state` (`tsCode`: `TS_INACTIVE` 0 ↔ Inactive,
    `TS_RUNNING` 1 ↔ Running, `TS_RESTART` 2 ↔ Restart,
    `TS_BLOCKED_ON_RECV` 3 ↔ BlockedOnReceive, 4 ↔ BlockedOnSend, 5 ↔
    BlockedOnReply, `TS_BLOCKED_ON_NTFN` 6 ↔ BlockedOnNotification, 7 ↔
    IdleThreadState), and for BlockedOnNotification `n` the block-object
    word is `n` (the payloads of the other blocked states are not related);
  - the badge register (`reg::BADGE` = RDI, l4v `badge_register`) of the
    saved user context is the register word `tcb::REGS + 8 * BADGE`; no
    other register is related;
  - the priority word is `tcb_priority`.

Nothing else is related here: endpoints, replies, scheduling contexts, the
TCBs' other fields and the scheduler state are left to their subsystems.
Their relation is a parameter `SR` of the refinement theorems
(NtfnSched.lean), with explicit hypotheses.

The relation reads memory only in the footprint `NFoot N T` (the first five
words of each notification; the state, block-object, badge-register,
priority and `Ep` link words of each TCB) and the spec's heap only through
`KView` (notifications; TCBs' state, badge register and priority), so it is
preserved by any change outside them (`NtfnStateRel.frame`).
-/
import Fl4Proofs.P1.QueueInv
import Fl4Proofs.P1.QueueEp
import Fl4Spec.Ipc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section


/-! ## TCB words (as in P1/QueueCallers.lean, restated here) -/

/-- The state word of the TCB at `t` (layout.rs `tcb::STATE`). -/
def tStA (t : U64) : U64 := core.num.U64.wrapping_add t layout.tcb.STATE
/-- The block-object word of the TCB at `t` (layout.rs `tcb::BLOCK_OBJ`). -/
def tBlockA (t : U64) : U64 := core.num.U64.wrapping_add t 3336#u64

theorem tsVals : sched.TS_RUNNING = 1#u64 ∧ sched.TS_RESTART = 2#u64 ∧ sched.TS_BLOCKED_ON_RECV = 3#u64 ∧
    sched.TS_BLOCKED_ON_SEND = 4#u64 ∧ sched.TS_BLOCKED_ON_NTFN = 6#u64 := by
  unfold sched.TS_RUNNING sched.TS_RESTART sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND sched.TS_BLOCKED_ON_NTFN
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tfield_val {y K : U64} (hy : TcbAddr y) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add y K).val = y.val + K.val := by
  have := hy.fits
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem tfield_ne {x y K1 K2 : U64} (hx : TcbAddr x) (hy : TcbAddr y) (h1 : K1.val < 4096) (h2 : K2.val < 4096)
    (hne : x = y → K1.val ≠ K2.val) : core.num.U64.wrapping_add x K1 ≠ core.num.U64.wrapping_add y K2 := by
  intro e
  have hv := congrArg UScalar.val e
  rw [tfield_val hx h1, tfield_val hy h2] at hv
  have := hx.align; have := hy.align
  by_cases hxy : x = y
  · subst hxy; exact hne rfl (by omega)
  · have : x.val ≠ y.val := fun e' => hxy (UScalar.eq_of_val_eq e')
    omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
@[step] theorem obj.Tcb.state.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.state st t s ⦃ v => v = L.mem s (tStA t) ⦄ := by
  unfold obj.Tcb.state; step*; simp_all [tStA]
end

/-! ## Word addresses -/

def nBadgeA (n : U64) : U64 := core.num.U64.wrapping_add n layout.ntfn.BADGE
def nBoundA (n : U64) : U64 := core.num.U64.wrapping_add n layout.ntfn.BOUND_TCB
def nScA (n : U64) : U64 := core.num.U64.wrapping_add n layout.ntfn.SC
/-- The badge register (`reg::BADGE` = RDI) of the TCB at `t`. -/
def badgeRegA (t : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.REGS)
    (core.num.U64.wrapping_mul layout.reg.BADGE 8#u64)

theorem nBadgeA_eq (n : U64) : nBadgeA n = core.num.U64.wrapping_add n 16#u64 := by
  unfold nBadgeA layout.ntfn.BADGE; rfl
theorem nBoundA_eq (n : U64) : nBoundA n = core.num.U64.wrapping_add n 24#u64 := by
  unfold nBoundA layout.ntfn.BOUND_TCB; rfl
theorem nScA_eq (n : U64) : nScA n = core.num.U64.wrapping_add n 32#u64 := by
  unfold nScA layout.ntfn.SC; rfl
theorem epHeadA_eq (n : U64) : epHeadA n = core.num.U64.wrapping_add n 0#u64 := by
  unfold epHeadA layout.ep.HEAD; rfl
theorem epTSA_eq (n : U64) : epTSA n = core.num.U64.wrapping_add n 8#u64 := by
  unfold epTSA layout.ep.TAIL_STATE; rfl
theorem tStA_eq (t : U64) : tStA t = core.num.U64.wrapping_add t 3328#u64 := by
  unfold tStA layout.tcb.STATE layout.tcb.F; rfl
theorem badgeRegA_eq (t : U64) : badgeRegA t = core.num.U64.wrapping_add t 256#u64 := by
  unfold badgeRegA layout.tcb.REGS layout.reg.BADGE layout.reg.RDI
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]

/-! ## Store specs of the field accessors -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem obj.Ntfn.badge.spec (s : S) (n : obj.Ntfn) :
    obj.Ntfn.badge st n s ⦃ v => v = L.mem s (nBadgeA n) ⦄ := by
  unfold obj.Ntfn.badge; step*; simp_all [nBadgeA]
@[step] theorem obj.Ntfn.set_badge.spec (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_badge st n s v ⦃ s' => s' = L.wr s (nBadgeA n) v ⦄ := by
  unfold obj.Ntfn.set_badge; step*; simp_all [nBadgeA]
@[step] theorem obj.Ntfn.bound_tcb.spec (s : S) (n : obj.Ntfn) :
    obj.Ntfn.bound_tcb st n s ⦃ v => v = L.mem s (nBoundA n) ⦄ := by
  unfold obj.Ntfn.bound_tcb; step*; simp_all [nBoundA]
@[step] theorem obj.Ntfn.sc.spec (s : S) (n : obj.Ntfn) :
    obj.Ntfn.sc st n s ⦃ v => v = L.mem s (nScA n) ⦄ := by
  unfold obj.Ntfn.sc; step*; simp_all [nScA]
@[step] theorem obj.Ntfn.set_state.spec (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_state st n s v ⦃ s' =>
      s' = L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (v &&& 3#u64)) ⦄ := by
  unfold obj.Ntfn.set_state obj.Ntfn.tail obj.Ntfn.tail_state obj.Ntfn.set_tail_state
  step*
  subst_vars
  have e : i1 = (L.mem s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) &&& ~~~3#u64) ||| (v &&& 3#u64) :=
    eq_of_bv (by simp only [i1_post1, i_post1, UScalar.bv_or, UScalar.bv_and])
  simp only [epTSA, ← ntfn_ts_eq, e]
@[step] theorem notification.set_active.spec (s : S) (n : obj.Ntfn) (b : U64) :
    notification.set_active st s n b ⦃ s' => s' = L.wr (L.wr s (epTSA n)
      ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_ACTIVE &&& 3#u64))) (nBadgeA n) b ⦄ := by
  unfold notification.set_active; step*
@[step] theorem obj.Tcb.set_reg_badge.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_reg st t s layout.reg.BADGE v ⦃ s' => s' = L.wr s (badgeRegA t) v ⦄ := by
  unfold obj.Tcb.set_reg; step*; simp_all [badgeRegA]
@[step] theorem obj.Tcb.set_state.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_state st t s v ⦃ s' => s' = L.wr s (tStA t) v ⦄ := by
  unfold obj.Tcb.set_state; step*; simp_all [tStA]
@[step] theorem obj.Tcb.set_block_obj.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_block_obj st t s v ⦃ s' => s' = L.wr s (tBlockA t) v ⦄ := by
  unfold obj.Tcb.set_block_obj; step*; simp_all [tBlockA]

end

end

/-! ## Placement -/

/-- A notification address: 64-byte aligned, and the object does not wrap. -/
structure NAddr (n : U64) : Prop where
  align : n.val % 64 = 0
  fits : n.val + 64 ≤ 2 ^ 64

/-- Hypothesis on the ghost sets: TCBs are placed (P1 `TcbPlaced`),
notifications are placed and do not overlap a TCB. -/
structure NPlaced (T N : Set U64) : Prop where
  tcb : TcbPlaced T
  ntfn : ∀ n ∈ N, NAddr n
  disj : ∀ n ∈ N, ∀ t ∈ T, t.val + 4096 ≤ n.val ∨ n.val + 64 ≤ t.val

theorem nfield_val {n K : U64} (hn : NAddr n) (hK : K.val < 64) :
    (core.num.U64.wrapping_add n K).val = n.val + K.val := by
  have := hn.fits
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem nfield_aligned {n K : U64} (hn : NAddr n) (hK : K.val < 64) (hK8 : K.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add n K) := by
  have := hn.align
  unfold Aligned; rw [nfield_val hn hK]; omega

theorem tt_eq_iff {x y K1 K2 : U64} (hx : TcbAddr x) (hy : TcbAddr y) (h1 : K1.val < 4096)
    (h2 : K2.val < 4096) :
    core.num.U64.wrapping_add x K1 = core.num.U64.wrapping_add y K2 ↔ x = y ∧ K1 = K2 := by
  constructor
  · intro e
    by_cases hxy : x = y
    · subst hxy
      refine ⟨rfl, UScalar.eq_of_val_eq ?_⟩
      have := congrArg UScalar.val e
      rw [tfield_val hx h1, tfield_val hx h2] at this; omega
    · exact absurd e (tfield_ne hx hy h1 h2 (fun h => absurd h hxy))
  · rintro ⟨rfl, rfl⟩; rfl

theorem nn_eq_iff {x y K1 K2 : U64} (hx : NAddr x) (hy : NAddr y) (h1 : K1.val < 64) (h2 : K2.val < 64) :
    core.num.U64.wrapping_add x K1 = core.num.U64.wrapping_add y K2 ↔ x = y ∧ K1 = K2 := by
  constructor
  · intro e
    have := congrArg UScalar.val e
    rw [nfield_val hx h1, nfield_val hy h2] at this
    have := hx.align; have := hy.align
    have hxy : x.val = y.val := by omega
    exact ⟨UScalar.eq_of_val_eq hxy, UScalar.eq_of_val_eq (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem tn_ne {t n K1 K2 : U64} (ht : TcbAddr t) (hn : NAddr n) (hd : t.val + 4096 ≤ n.val ∨ n.val + 64 ≤ t.val)
    (h1 : K1.val < 4096) (h2 : K2.val < 64) :
    core.num.U64.wrapping_add t K1 ≠ core.num.U64.wrapping_add n K2 := by
  intro e
  have := congrArg UScalar.val e
  rw [tfield_val ht h1, nfield_val hn h2] at this; omega

/-- The named addresses as offsets (for `simp`). -/
theorem tBlockA_eq (t : U64) : tBlockA t = core.num.U64.wrapping_add t 3336#u64 := rfl
theorem prioA_eq' (t : U64) : prioA t = core.num.U64.wrapping_add t 3448#u64 := rfl
theorem nextEp_eq (t : U64) : nextA .Ep t = core.num.U64.wrapping_add t 3496#u64 := rfl
theorem prevEp_eq (t : U64) : prevA .Ep t = core.num.U64.wrapping_add t 3504#u64 := rfl

/-! ## The relation -/

section Rel
open Fl4Spec

/-- The queue of the notification at `n` (`notification::get_queue`). -/
def qOf (m : U64 → U64) (n : U64) : tcbqueue.Queue := ⟨m (epHeadA n), m (epTSA n) &&& ~~~3#u64⟩
/-- The state bits of the notification at `n` (`Ntfn::state`). -/
def stOf (m : U64 → U64) (n : U64) : U64 := m (epTSA n) &&& 3#u64

theorem epQ_eq {S : Type _} {st : machine.Store S} [L : LawfulStore st] (s : S) (n : U64) :
    L.epQ s n = qOf (L.mem s) n := rfl
theorem epState_eq {S : Type _} {st : machine.Store S} [L : LawfulStore st] (s : S) (n : U64) :
    L.epState s n = stOf (L.mem s) n := rfl

/-- A pointer word as an optional `obj_ref` (0 is none). -/
def optRef (w : U64) : Option ObjRef := if w = 0#u64 then none else some w.bv

/-- FL4's thread-state word for a spec thread state (sched.rs `TS_*`). -/
def tsCode : ThreadState → Nat
  | .inactive => 0
  | .running => 1
  | .restart => 2
  | .blockedOnReceive _ _ _ => 3
  | .blockedOnSend _ _ => 4
  | .blockedOnReply _ => 5
  | .blockedOnNotification _ => 6
  | .idleThreadState => 7
  | .runningVM => 8

/-- The badge register of a spec TCB's saved user context. -/
def badgeOf (x : Tcb) : Word := x.tcbArch.tcbContext.userRegs badge_register

/-- The TCB at `t` in memory `m` and the spec's TCB `x`: state, the
notification it is blocked on, badge register, priority. -/
structure TcbRel1 (m : U64 → U64) (t : U64) (x : Tcb) : Prop where
  st : (m (tStA t)).val = tsCode x.tcbState
  blk : ∀ n, x.tcbState = .blockedOnNotification n → (m (tBlockA t)).bv = n
  badge : (m (badgeRegA t)).bv = badgeOf x
  prio : (m (prioA t)).val = x.tcbPriority.toNat

/-- A TCB blocked on the notification at `n` (state word and block object). -/
def BlockedOn (m : U64 → U64) (n y : U64) : Prop := (m (tStA y)).val = 6 ∧ m (tBlockA y) = n

/-- `ntfn_obj` of the notification at `n`. -/
def NtfnObjRel (m : U64 → U64) (T : Set U64) (n : U64) : Ntfn → Prop
  | .idleNtfn => stOf m n = 0#u64 ∧ QueueRel m T .Ep (qOf m n) []
  | .activeNtfn b => stOf m n = 2#u64 ∧ QueueRel m T .Ep (qOf m n) [] ∧ (m (nBadgeA n)).bv = b
  | .waitingNtfn q => stOf m n = 1#u64 ∧ ∃ xs : List U64, xs ≠ [] ∧ q = xs.map UScalar.bv ∧
      QueueRel m T .Ep (qOf m n) xs ∧ ∀ y ∈ xs, BlockedOn m n y

/-- The notification at `n` in memory `m` and the spec's notification `x`. -/
structure NtfnRel1 (m : U64 → U64) (T : Set U64) (n : U64) (x : Notification) : Prop where
  obj : NtfnObjRel m T n x.ntfnObj
  bound : x.ntfnBoundTcb = optRef (m (nBoundA n))
  bound_mem : m (nBoundA n) ≠ 0#u64 → m (nBoundA n) ∈ T
  sc : x.ntfnSc = optRef (m (nScA n))

/-- The notification part of the state relation. -/
structure NtfnStateRel {Z : Type} (N T : Set U64) (m : U64 → U64) (σ : State Z) : Prop where
  ntfn : ∀ n ∈ N, ∃ x, σ.kheap n.bv = some (.notification x) ∧ NtfnRel1 m T n x
  tcb : ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ TcbRel1 m t x

/-- The words the relation reads. -/
def NFoot (N T : Set U64) (a : U64) : Prop :=
  (∃ n ∈ N, n.val ≤ a.val ∧ a.val < n.val + 40) ∨
  (∃ t ∈ T, a = tStA t ∨ a = tBlockA t ∨ a = badgeRegA t ∨ a = prioA t ∨ a = nextA .Ep t ∨ a = prevA .Ep t)

/-- The words the notification code writes: the footprint without the
priorities (which the scheduler relation may read). -/
def NWrite (N T : Set U64) (a : U64) : Prop :=
  (∃ n ∈ N, n.val ≤ a.val ∧ a.val < n.val + 40) ∨
  (∃ t ∈ T, a = tStA t ∨ a = tBlockA t ∨ a = badgeRegA t ∨ a = nextA .Ep t ∨ a = prevA .Ep t)

theorem NWrite.foot {N T : Set U64} {a : U64} : NWrite N T a → NFoot N T a := by
  rintro (h | ⟨t, ht, h | h | h | h | h⟩)
  · exact Or.inl h
  all_goals simp_all [NFoot]
  all_goals exact Or.inr ⟨t, ht, by simp⟩

/-- What the relation reads of the spec's heap: notifications, and TCBs'
state, badge register and priority. -/
def KView {Z : Type} (σ σ' : State Z) : Prop :=
  (∀ p x, σ.kheap p = some (.notification x) → σ'.kheap p = some (.notification x)) ∧
  (∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧
    y.tcbState = x.tcbState ∧ badgeOf y = badgeOf x ∧ y.tcbPriority = x.tcbPriority)

/-- What the notification code changes in the spec's state: the `ntfn_obj`
of notifications and the state and user context of TCBs; nothing else. -/
def NtfnStep {Z : Type} (σ σ' : State Z) : Prop :=
  σ'.exst = σ.exst ∧ { σ'.toAbstractState with kheap := σ.kheap } = σ.toAbstractState ∧
  ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ x y, σ.kheap p = some (.notification x) ∧ σ'.kheap p = some (.notification y) ∧
      y.ntfnBoundTcb = x.ntfnBoundTcb ∧ y.ntfnSc = x.ntfnSc) ∨
    (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
      y = { x with tcbState := y.tcbState, tcbArch := y.tcbArch })

end Rel

/-! ## Frames -/

section Frame
open Fl4Spec
variable {Z : Type}

/-- The five words of the notification at `n` agree. -/
structure NWordsEq (m m' : U64 → U64) (n : U64) : Prop where
  head : m' (epHeadA n) = m (epHeadA n)
  ts : m' (epTSA n) = m (epTSA n)
  badge : m' (nBadgeA n) = m (nBadgeA n)
  bound : m' (nBoundA n) = m (nBoundA n)
  sc : m' (nScA n) = m (nScA n)

/-- The related fields of the TCB at `t` agree. -/
structure TFieldsEq (m m' : U64 → U64) (t : U64) : Prop where
  st : m' (tStA t) = m (tStA t)
  blk : m' (tBlockA t) = m (tBlockA t)
  badge : m' (badgeRegA t) = m (badgeRegA t)
  prio : m' (prioA t) = m (prioA t)

/-- The `Ep` links of the TCB at `t` agree. -/
def TLinksEq (m m' : U64 → U64) (t : U64) : Prop :=
  m' (prevA .Ep t) = m (prevA .Ep t) ∧ m' (nextA .Ep t) = m (nextA .Ep t)

theorem queueRel_congr_links {m m' : U64 → U64} {T : Set U64} {q xs} (h : QueueRel m T .Ep q xs)
    (hl : ∀ y ∈ xs, TLinksEq m m' y) : QueueRel m' T .Ep q xs :=
  ⟨h.nodup, h.mem, h.head, h.last, h.seg.congr hl⟩

theorem qOf_congr {m m' : U64 → U64} {n : U64} (h : NWordsEq m m' n) : qOf m' n = qOf m n := by
  simp only [qOf, h.head, h.ts]
theorem stOf_congr {m m' : U64 → U64} {n : U64} (h : NWordsEq m m' n) : stOf m' n = stOf m n := by
  simp only [stOf, h.ts]

theorem TcbRel1.frame {m m' : U64 → U64} {t : U64} {x : Tcb} (h : TcbRel1 m t x) (he : TFieldsEq m m' t) :
    TcbRel1 m' t x :=
  ⟨he.st ▸ h.st, fun n hn => he.blk ▸ h.blk n hn, he.badge ▸ h.badge, he.prio ▸ h.prio⟩

/-- What a notification needs of a member of its queue: state, block object
and links. -/
def MemberEq (m m' : U64 → U64) (y : U64) : Prop :=
  m' (tStA y) = m (tStA y) ∧ m' (tBlockA y) = m (tBlockA y) ∧ TLinksEq m m' y

theorem NtfnObjRel.frame {m m' : U64 → U64} {T : Set U64} {n : U64} {o : Ntfn} (h : NtfnObjRel m T n o)
    (hn : NWordsEq m m' n)
    (hy : ∀ y ∈ T, y.bv ∈ o.ntfnQueue → MemberEq m m' y) : NtfnObjRel m' T n o := by
  cases o with
  | idleNtfn =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨stOf_congr hn ▸ h1, qOf_congr hn ▸ queueRel_congr_links h2 (by simp)⟩
  | activeNtfn b =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨stOf_congr hn ▸ h1, qOf_congr hn ▸ queueRel_congr_links h2 (by simp), hn.badge ▸ h3⟩
  | waitingNtfn q =>
    obtain ⟨h1, xs, hne, rfl, h2, h3⟩ := h
    have hy' : ∀ y ∈ xs, MemberEq m m' y := fun y hyx =>
      hy y (h2.mem y hyx) (by simp only [Ntfn.ntfnQueue]; exact List.mem_map_of_mem hyx)
    refine ⟨stOf_congr hn ▸ h1, xs, hne, rfl, qOf_congr hn ▸ queueRel_congr_links h2 (fun y hyx => (hy' y hyx).2.2),
      fun y hyx => ?_⟩
    obtain ⟨e1, e2⟩ := h3 y hyx
    exact ⟨(hy' y hyx).1 ▸ e1, (hy' y hyx).2.1 ▸ e2⟩

theorem NtfnRel1.frame {m m' : U64 → U64} {T : Set U64} {n : U64} {x : Notification} (h : NtfnRel1 m T n x)
    (hn : NWordsEq m m' n)
    (hy : ∀ y ∈ T, y.bv ∈ x.ntfnObj.ntfnQueue → MemberEq m m' y) : NtfnRel1 m' T n x :=
  ⟨h.obj.frame hn hy, hn.bound ▸ h.bound, hn.bound ▸ h.bound_mem, hn.sc ▸ h.sc⟩

/-- Members of a waiting queue are TCBs blocked on the notification. -/
theorem NtfnObjRel.blocked {m : U64 → U64} {T : Set U64} {n : U64} {o : Ntfn} (h : NtfnObjRel m T n o)
    {y : U64} (hy : y.bv ∈ o.ntfnQueue) : y ∈ T ∧ BlockedOn m n y := by
  cases o with
  | idleNtfn => simp [Ntfn.ntfnQueue] at hy
  | activeNtfn b => simp [Ntfn.ntfnQueue] at hy
  | waitingNtfn q =>
    obtain ⟨-, xs, -, rfl, h2, h3⟩ := h
    simp only [Ntfn.ntfnQueue, List.mem_map] at hy
    obtain ⟨z, hz, e⟩ := hy
    have : z = y := eq_of_bv e
    subst this
    exact ⟨h2.mem z hz, h3 z hz⟩

theorem bv_inj {x y : U64} (h : x ≠ y) : x.bv ≠ y.bv := fun e => h (eq_of_bv e)

/-- Updating the notification at `n`: the other notifications and the TCBs
keep their relation when their words agree (the links of a TCB only need to
agree if it is not blocked on `n`). -/
theorem NtfnStateRel.upd_ntfn {N T : Set U64} {m m' : U64 → U64} {σ : State Z} (hR : NtfnStateRel N T m σ)
    {n : U64} (hn : n ∈ N) (x' : Notification)
    (hN : ∀ n' ∈ N, n' ≠ n → NWordsEq m m' n')
    (hT : ∀ y ∈ T, TFieldsEq m m' y)
    (hL : ∀ y ∈ T, m (tBlockA y) ≠ n → TLinksEq m m' y)
    (hx : NtfnRel1 m' T n x') :
    NtfnStateRel N T m' { σ with kheap := Function.update σ.kheap n.bv (some (.notification x')) } := by
  obtain ⟨x, hk, -⟩ := hR.ntfn n hn
  refine ⟨fun n' hn' => ?_, fun t ht => ?_⟩
  · by_cases e : n' = n
    · subst e; exact ⟨x', by simp, hx⟩
    · obtain ⟨y, hky, hy⟩ := hR.ntfn n' hn'
      refine ⟨y, by simp [bv_inj e, hky], hy.frame (hN n' hn' e) fun z hz hq => ?_⟩
      obtain ⟨-, -, hb⟩ := hy.obj.blocked hq
      exact ⟨(hT z hz).st, (hT z hz).blk, hL z hz (by rw [hb]; exact e)⟩
  · obtain ⟨y, hky, hy⟩ := hR.tcb t ht
    have : t.bv ≠ n.bv := by intro e; rw [e, hk] at hky; cases hky
    exact ⟨y, by simp [this, hky], hy.frame (hT t ht)⟩

/-- Updating the TCB at `t`: the notifications and other TCBs keep their
relation when their words agree; `t`'s state and block object may only
change if `t` is in no notification queue. -/
theorem NtfnStateRel.upd_tcb {N T : Set U64} {m m' : U64 → U64} {σ : State Z} (hR : NtfnStateRel N T m σ)
    {t : U64} (ht : t ∈ T) (x' : Tcb)
    (hN : ∀ n ∈ N, NWordsEq m m' n)
    (hT : ∀ y ∈ T, y ≠ t → TFieldsEq m m' y)
    (hL : ∀ y ∈ T, TLinksEq m m' y)
    (hq : (∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue) ∨
      (m' (tStA t) = m (tStA t) ∧ m' (tBlockA t) = m (tBlockA t)))
    (hx : TcbRel1 m' t x') :
    NtfnStateRel N T m' { σ with kheap := Function.update σ.kheap t.bv (some (.tcb x')) } := by
  obtain ⟨x, hk, -⟩ := hR.tcb t ht
  refine ⟨fun n hn => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hkz, hz⟩ := hR.ntfn n hn
    have : n.bv ≠ t.bv := by intro e; rw [e, hk] at hkz; cases hkz
    refine ⟨z, by simp [this, hkz], hz.frame (hN n hn) fun y hy hq' => ?_⟩
    by_cases e : y = t
    · subst e
      rcases hq with hq | ⟨e1, e2⟩
      · exact absurd hq' (hq n hn z hkz)
      · exact ⟨e1, e2, hL y hy⟩
    · exact ⟨(hT y hy e).st, (hT y hy e).blk, hL y hy⟩
  · by_cases e : y = t
    · subst e; exact ⟨x', by simp, hx⟩
    · obtain ⟨z, hkz, hz⟩ := hR.tcb y hy
      exact ⟨z, by simp [bv_inj e, hkz], hz.frame (hT y hy e)⟩

end Frame

/-! ## The footprint -/

section Foot
open Fl4Spec
variable {Z : Type} {N T : Set U64}

/-- The notification words: aligned, in the footprint. -/
theorem nword {n K : U64} (hP : NPlaced T N) (hn : n ∈ N) (hK : K.val < 40) (hK8 : K.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add n K) ∧ NFoot N T (core.num.U64.wrapping_add n K) := by
  have ha := hP.ntfn n hn
  refine ⟨nfield_aligned ha (by omega) hK8, Or.inl ⟨n, hn, ?_⟩⟩
  rw [nfield_val ha (by omega)]; omega

theorem tword {t K : U64} (hP : NPlaced T N) (ht : t ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add t K) :=
  field_aligned (hP.tcb t ht) hK hK8

theorem foot_head {n : U64} (hP : NPlaced T N) (hn : n ∈ N) : Aligned (epHeadA n) ∧ NFoot N T (epHeadA n) := by
  rw [epHeadA_eq]; exact nword hP hn (by simp) (by simp)
theorem foot_ts {n : U64} (hP : NPlaced T N) (hn : n ∈ N) : Aligned (epTSA n) ∧ NFoot N T (epTSA n) := by
  rw [epTSA_eq]; exact nword hP hn (by simp) (by simp)
theorem foot_badge {n : U64} (hP : NPlaced T N) (hn : n ∈ N) : Aligned (nBadgeA n) ∧ NFoot N T (nBadgeA n) := by
  rw [nBadgeA_eq]; exact nword hP hn (by simp) (by simp)
theorem foot_bound {n : U64} (hP : NPlaced T N) (hn : n ∈ N) : Aligned (nBoundA n) ∧ NFoot N T (nBoundA n) := by
  rw [nBoundA_eq]; exact nword hP hn (by simp) (by simp)
theorem foot_sc {n : U64} (hP : NPlaced T N) (hn : n ∈ N) : Aligned (nScA n) ∧ NFoot N T (nScA n) := by
  rw [nScA_eq]; exact nword hP hn (by simp) (by simp)

theorem foot_st {t : U64} (hP : NPlaced T N) (ht : t ∈ T) : Aligned (tStA t) ∧ NFoot N T (tStA t) :=
  ⟨by rw [tStA_eq]; exact tword hP ht (by simp) (by simp), Or.inr ⟨t, ht, by simp⟩⟩
theorem foot_blk {t : U64} (hP : NPlaced T N) (ht : t ∈ T) : Aligned (tBlockA t) ∧ NFoot N T (tBlockA t) :=
  ⟨by rw [tBlockA_eq]; exact tword hP ht (by simp) (by simp), Or.inr ⟨t, ht, by simp⟩⟩
theorem foot_breg {t : U64} (hP : NPlaced T N) (ht : t ∈ T) : Aligned (badgeRegA t) ∧ NFoot N T (badgeRegA t) :=
  ⟨by rw [badgeRegA_eq]; exact tword hP ht (by simp) (by simp), Or.inr ⟨t, ht, by simp⟩⟩
theorem foot_prio {t : U64} (hP : NPlaced T N) (ht : t ∈ T) : Aligned (prioA t) ∧ NFoot N T (prioA t) :=
  ⟨by rw [prioA_eq']; exact tword hP ht (by simp) (by simp), Or.inr ⟨t, ht, by simp⟩⟩
theorem foot_next {t : U64} (hP : NPlaced T N) (ht : t ∈ T) : Aligned (nextA .Ep t) ∧ NFoot N T (nextA .Ep t) :=
  ⟨nextA_aligned (hP.tcb t ht) .Ep, Or.inr ⟨t, ht, by simp⟩⟩
theorem foot_prev {t : U64} (hP : NPlaced T N) (ht : t ∈ T) : Aligned (prevA .Ep t) ∧ NFoot N T (prevA .Ep t) :=
  ⟨prevA_aligned (hP.tcb t ht) .Ep, Or.inr ⟨t, ht, by simp⟩⟩

/-- Memory that agrees on the footprint. -/
def FootEq (N T : Set U64) (m m' : U64 → U64) : Prop := ∀ a, Aligned a → NFoot N T a → m' a = m a

theorem FootEq.nwords {m m' : U64 → U64} (hP : NPlaced T N) (h : FootEq N T m m') {n : U64} (hn : n ∈ N) :
    NWordsEq m m' n :=
  ⟨h _ (foot_head hP hn).1 (foot_head hP hn).2, h _ (foot_ts hP hn).1 (foot_ts hP hn).2,
   h _ (foot_badge hP hn).1 (foot_badge hP hn).2, h _ (foot_bound hP hn).1 (foot_bound hP hn).2,
   h _ (foot_sc hP hn).1 (foot_sc hP hn).2⟩

theorem FootEq.tfields {m m' : U64 → U64} (hP : NPlaced T N) (h : FootEq N T m m') {t : U64} (ht : t ∈ T) :
    TFieldsEq m m' t :=
  ⟨h _ (foot_st hP ht).1 (foot_st hP ht).2, h _ (foot_blk hP ht).1 (foot_blk hP ht).2,
   h _ (foot_breg hP ht).1 (foot_breg hP ht).2, h _ (foot_prio hP ht).1 (foot_prio hP ht).2⟩

theorem FootEq.tlinks {m m' : U64 → U64} (hP : NPlaced T N) (h : FootEq N T m m') {t : U64} (ht : t ∈ T) :
    TLinksEq m m' t :=
  ⟨h _ (foot_prev hP ht).1 (foot_prev hP ht).2, h _ (foot_next hP ht).1 (foot_next hP ht).2⟩

/-- The relation only reads the footprint and `KView`. -/
theorem NtfnStateRel.frame {m m' : U64 → U64} {σ σ' : State Z} (hR : NtfnStateRel N T m σ)
    (hP : NPlaced T N) (hm : FootEq N T m m') (hk : KView σ σ') : NtfnStateRel N T m' σ' := by
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hkx, hx⟩ := hR.ntfn n hn
    exact ⟨x, hk.1 _ _ hkx, hx.frame (hm.nwords hP hn) fun y hy _ =>
      ⟨(hm.tfields hP hy).st, (hm.tfields hP hy).blk, hm.tlinks hP hy⟩⟩
  · obtain ⟨x, hkx, hx⟩ := hR.tcb t ht
    obtain ⟨y, hky, e1, e2, e3⟩ := hk.2 _ _ hkx
    have hx' := hx.frame (hm.tfields hP ht)
    exact ⟨y, hky, ⟨e1 ▸ hx'.st, fun n hn => hx'.blk n (e1 ▸ hn), e2 ▸ hx'.badge, e3 ▸ hx'.prio⟩⟩

theorem KView.refl (σ : State Z) : KView σ σ :=
  ⟨fun _ _ h => h, fun _ x h => ⟨x, h, rfl, rfl, rfl⟩⟩

theorem KView.trans {σ₁ σ₂ σ₃ : State Z} (h₁ : KView σ₁ σ₂) (h₂ : KView σ₂ σ₃) : KView σ₁ σ₃ :=
  ⟨fun p x h => h₂.1 p x (h₁.1 p x h), fun p x h => by
    obtain ⟨y, hy, e1, e2, e3⟩ := h₁.2 p x h
    obtain ⟨z, hz, f1, f2, f3⟩ := h₂.2 p y hy
    exact ⟨z, hz, f1.trans e1, f2.trans e2, f3.trans e3⟩⟩

theorem NtfnStep.refl (σ : State Z) : NtfnStep σ σ := ⟨rfl, rfl, fun _ => Or.inl rfl⟩

theorem NtfnStep.trans {σ₁ σ₂ σ₃ : State Z} (h₁ : NtfnStep σ₁ σ₂) (h₂ : NtfnStep σ₂ σ₃) : NtfnStep σ₁ σ₃ := by
  obtain ⟨a1, b1, c1⟩ := h₁
  obtain ⟨a2, b2, c2⟩ := h₂
  refine ⟨a2.trans a1, ?_, fun p => ?_⟩
  · rw [← b1]; rw [← b2]
  · rcases c1 p with e1 | ⟨x, y, hx, hy, f1, f2⟩ | ⟨x, y, hx, hy, f⟩ <;>
    rcases c2 p with e2 | ⟨x', y', hx', hy', f1', f2'⟩ | ⟨x', y', hx', hy', f'⟩
    · exact Or.inl (e2.trans e1)
    · rw [e1] at hx'; exact Or.inr (Or.inl ⟨x', y', hx', hy', f1', f2'⟩)
    · rw [e1] at hx'; exact Or.inr (Or.inr ⟨x', y', hx', hy', f'⟩)
    · rw [← e2] at hy; exact Or.inr (Or.inl ⟨x, y, hx, hy, f1, f2⟩)
    · rw [hy] at hx'; cases hx'
      exact Or.inr (Or.inl ⟨x, y', hx, hy', f1'.trans f1, f2'.trans f2⟩)
    · rw [hy] at hx'; cases hx'
    · rw [← e2] at hy; exact Or.inr (Or.inr ⟨x, y, hx, hy, f⟩)
    · rw [hy] at hx'; cases hx'
    · rw [hy] at hx'; cases hx'
      refine Or.inr (Or.inr ⟨x, y', hx, hy', ?_⟩)
      rw [f', f]

/-- Writing a notification object with the same bound TCB and SC. -/
theorem NtfnStep.ntfn {σ : State Z} {p : ObjRef} {x y : Notification} (hk : σ.kheap p = some (.notification x))
    (h1 : y.ntfnBoundTcb = x.ntfnBoundTcb) (h2 : y.ntfnSc = x.ntfnSc) :
    NtfnStep σ { σ with kheap := Function.update σ.kheap p (some (.notification y)) } := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; exact Or.inr (Or.inl ⟨x, y, hk, by simp, h1, h2⟩)
  · exact Or.inl (by simp [e])

/-- Writing a TCB's state and user context. -/
theorem NtfnStep.tcb {σ : State Z} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) (ts : ThreadState)
    (a : ArchTcb) :
    NtfnStep σ { σ with kheap := Function.update σ.kheap p (some (.tcb { x with tcbState := ts, tcbArch := a })) } := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; exact Or.inr (Or.inr ⟨x, { x with tcbState := ts, tcbArch := a }, hk, by simp, rfl⟩)
  · exact Or.inl (by simp [e])

end Foot

end Fl4Proofs.P3.Notif
