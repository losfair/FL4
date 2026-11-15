/-
P1: `cancel_ipc` (ipc.rs; seL4 `cancelIPC`, MCS) and `suspend` keep
`SchedQueuesInv`.

A thread blocked on an endpoint or notification leaves the object's queue
(`ep_dequeue` / `ntfn_dequeue`; for a moment it is in the exception set `X`
of blocked threads outside their queue) and becomes inactive.  The reply
bookkeeping (`reply_unlink`, `reply_remove_tcb`) writes words of reply
objects and SCs, placed as disjoint objects among `Ω` (`ObjsOK`); the
reply object of a thread blocked on reply is typed (`ReplyT`).  `KeepT`
records everything else `cancel_ipc` keeps, for the other invariants
(`QueueObjs`).
-/
import Fl4Proofs.P1.QueueSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs : Set U64}

/-! ## Addresses and small specs -/

def faultA (t : U64) : U64 := core.num.U64.wrapping_add t 3376#u64
def replyA (t : U64) : U64 := core.num.U64.wrapping_add t 3360#u64
def rTcbA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.TCB
def rPrevA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.PREV
def rNextA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.NEXT
/-- An SC's bound-notification word. -/
def scNtfnA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.NTFN
/-- A notification's `SC` word. -/
def ntfnScA (n : U64) : U64 := core.num.U64.wrapping_add n layout.ntfn.SC
/-- A TCB's bound-notification word. -/
def boundA (t : U64) : U64 := core.num.U64.wrapping_add t 3368#u64
/-- A notification's `BADGE` and `BOUND_TCB` words. -/
def ntfnBdA (n : U64) : U64 := core.num.U64.wrapping_add n layout.ntfn.BADGE
def ntfnBtA (n : U64) : U64 := core.num.U64.wrapping_add n layout.ntfn.BOUND_TCB
/-- The timer fields of a TCB (`timer.rs`). -/
def tdA (y : U64) : U64 := core.num.U64.wrapping_add y 3528#u64
def tbA (y : U64) : U64 := core.num.U64.wrapping_add y 3536#u64
def tlA (y : U64) : U64 := core.num.U64.wrapping_add y 3544#u64
def trA (y : U64) : U64 := core.num.U64.wrapping_add y 3552#u64
def tpA (y : U64) : U64 := core.num.U64.wrapping_add y 3560#u64
def thA (y : U64) : U64 := core.num.U64.wrapping_add y 3568#u64
/-- A TCB's debug-list links (`tcb::DEBUG_NEXT`, `tcb::DEBUG_PREV`). -/
def dnA (y : U64) : U64 := core.num.U64.wrapping_add y 3576#u64
/-- A TCB's `YIELD_TO` word and an SC's `YIELD_FROM` word. -/
def yieldA (t : U64) : U64 := core.num.U64.wrapping_add t 3472#u64
def scYieldFromA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.YIELD_FROM
def dpA (y : U64) : U64 := core.num.U64.wrapping_add y 3584#u64

theorem ntfnBtA_val {n : U64} (h : n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64) : (ntfnBtA n).val = n.val + 24 := by
  unfold ntfnBtA; simp [layout.ntfn.BOUND_TCB, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
theorem ntfnBdA_val {n : U64} (h : n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64) : (ntfnBdA n).val = n.val + 16 := by
  unfold ntfnBdA; simp [layout.ntfn.BADGE, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
theorem ntfnScA_val {n : U64} (h : n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64) : (ntfnScA n).val = n.val + 32 := by
  unfold ntfnScA; simp [layout.ntfn.SC, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

variable {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- Reply objects and SCs as placed, disjoint objects. -/
structure ObjsOK (st : machine.Store S) [L : LawfulStore st] (Ω Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s : S) :
    Prop where
  rp : ∀ r ∈ Rp, r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64
  sc : ∀ c ∈ Scs, Placed c (Z c) ∧ 7 ≤ Z c
  rpW : ∀ r ∈ Rp, ∀ b : U64, Aligned b → r.val ≤ b.val → b.val < r.val + 32 → b ∈ Sg
  scW : ∀ c ∈ Scs, ∀ b : U64, Aligned b → InSC c (Z c) b → b ∈ Ω
  fixW : ∀ c ∈ Scs, scTcbA c ∈ Sg ∧ scCoreA c ∈ Sg
  scDisj : ∀ c ∈ Scs, ∀ c' ∈ Scs, c ≠ c' → c.val + 2 ^ Z c ≤ c'.val ∨ c'.val + 2 ^ Z c' ≤ c.val
  rpSc : ∀ r ∈ Rp, ∀ c ∈ Scs, r.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ r.val
  /-- The SCs' `REPLY` words are frame words. -/
  repW : ∀ c ∈ Scs, scReplyA c ∈ Sg
  /-- The notifications' `SC` words are frame words, outside the reply objects and SCs. -/
  ntW : ∀ n ∈ Nt, ntfnScA n ∈ Sg
  ntRp : ∀ n ∈ Nt, ∀ r ∈ Rp, (ntfnScA n).val + 8 ≤ r.val ∨ r.val + 32 ≤ (ntfnScA n).val
  ntSc : ∀ n ∈ Nt, ∀ c ∈ Scs, (ntfnScA n).val + 8 ≤ c.val ∨ c.val + 2 ^ Z c ≤ (ntfnScA n).val
  ntAl : ∀ n ∈ Nt, Aligned (ntfnScA n)
  /-- Notifications are 64-byte objects, outside the reply objects and SCs,
  with their `BADGE` and `BOUND_TCB` words frame words. -/
  ntP : ∀ n ∈ Nt, n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64
  ntB : ∀ n ∈ Nt, ntfnBdA n ∈ Sg ∧ ntfnBtA n ∈ Sg
  ntORp : ∀ n ∈ Nt, ∀ r ∈ Rp, n.val + 64 ≤ r.val ∨ r.val + 32 ≤ n.val
  ntOSc : ∀ n ∈ Nt, ∀ c ∈ Scs, n.val + 64 ≤ c.val ∨ c.val + 2 ^ Z c ≤ n.val
  /-- The SCs' `NTFN` words are frame words. -/
  snW : ∀ c ∈ Scs, scNtfnA c ∈ Sg
  /-- The SCs' `YIELD_FROM` words are frame words. -/
  syW : ∀ c ∈ Scs, scYieldFromA c ∈ Sg
  /-- The SCs' `REFILL_MAX` words are frame words. -/
  mxW : ∀ c ∈ Scs, maxA c ∈ Sg
  /-- Notifications are not at the null address. -/
  nt0 : ∀ n ∈ Nt, n ≠ 0#u64
  /-- Nor are reply objects. -/
  rp0 : ∀ r ∈ Rp, r ≠ 0#u64

/-! ## Addresses -/

theorem rp_val {r : U64} (h : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64) {o : U64} (ho : o.val < 32) :
    (core.num.U64.wrapping_add r o).val = r.val + o.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem ObjsOK.rword (h : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) {o : U64} (ho : o.val < 32)
    (h8 : o.val % 8 = 0) : core.num.U64.wrapping_add r o ∈ Sg := by
  have hp := h.rp r hr
  have hv := rp_val hp ho
  refine h.rpW r hr _ ?_ ?_ ?_
  · unfold Aligned; rw [hv]; omega
  · rw [hv]; omega
  · rw [hv]; omega

theorem ObjsOK.tcbW (h : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) : rTcbA r ∈ Sg :=
  h.rword hr (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
theorem ObjsOK.prevW (h : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) : rPrevA r ∈ Sg :=
  h.rword hr (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
theorem ObjsOK.nextW (h : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) : rNextA r ∈ Sg :=
  h.rword hr (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])

theorem ObjsOK.ksb {s s' : S} (h : ObjsOK st Ω Sg Rp Scs Nt Z s) : ObjsOK st Ω Sg Rp Scs Nt Z s' :=
  ⟨h.rp, h.sc, h.rpW, h.scW, h.fixW, h.scDisj, h.rpSc, h.repW, h.ntW, h.ntRp, h.ntSc, h.ntAl, h.ntP,
    h.ntB, h.ntORp, h.ntOSc, h.snW, h.syW, h.mxW, h.nt0, h.rp0⟩

theorem sc_lo {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) :
    c.val % 8 = 0 ∧ 128 ≤ 2 ^ z ∧ c.val + 2 ^ z ≤ 2 ^ 64 := by
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hd : 8 ∣ 2 ^ z := by
    have : 2 ^ z = 2 ^ 3 * 2 ^ (z - 3) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  refine ⟨?_, by simpa using h128, hP.fits⟩
  have := hP.align
  rw [← Nat.mod_mod_of_dvd c.val hd, this]

theorem sc_word_val {c o : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) (ho : o.val < 128) :
    (core.num.U64.wrapping_add c o).val = c.val + o.val := by
  obtain ⟨-, h1, h2⟩ := sc_lo hP hz
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem rTcbA_val {r : U64} (h : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64) : (rTcbA r).val = r.val := by
  unfold rTcbA; rw [rp_val h (by simp [layout.reply.TCB])]; simp [layout.reply.TCB]
theorem rPrevA_val {r : U64} (h : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64) : (rPrevA r).val = r.val + 8 := by
  unfold rPrevA; rw [rp_val h (by simp [layout.reply.PREV])]; simp [layout.reply.PREV]
theorem rNextA_val {r : U64} (h : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64) : (rNextA r).val = r.val + 16 := by
  unfold rNextA; rw [rp_val h (by simp [layout.reply.NEXT])]; simp [layout.reply.NEXT]
theorem scTcbA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (scTcbA c).val = c.val + 24 := by
  unfold scTcbA; rw [sc_word_val hP hz (by simp [layout.sc.TCB])]; simp [layout.sc.TCB]
theorem scCoreA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (scCoreA c).val = c.val + 16 := by
  unfold scCoreA; rw [sc_word_val hP hz (by simp [layout.sc.CORE])]; simp [layout.sc.CORE]


@[step] theorem obj.Tcb.set_fault_type.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_type st t s v ⦃ s' => s' = L.wr s (faultA t) v ⦄ := by
  unfold obj.Tcb.set_fault_type; step*; simp_all [faultA]
@[step] theorem obj.Tcb.reply_obj.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.reply_obj st t s ⦃ v => v = L.mem s (replyA t) ⦄ := by
  unfold obj.Tcb.reply_obj; step*; simp_all [replyA]
@[step] theorem obj.Reply.set_tcb.spec (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_tcb st r s v ⦃ s' => s' = L.wr s (rTcbA r) v ⦄ := by
  unfold obj.Reply.set_tcb; step*; simp_all [rTcbA]
@[step] theorem obj.Reply.next.spec (s : S) (r : obj.Reply) :
    obj.Reply.next st r s ⦃ v => v = L.mem s (rNextA r) &&& ~~~1#u64 ⦄ := by
  unfold obj.Reply.next obj.Reply.next_raw; step*; simp_all [rNextA]
@[step] theorem obj.Reply.prev.spec (s : S) (r : obj.Reply) :
    obj.Reply.prev st r s ⦃ v => v = L.mem s (rPrevA r) &&& ~~~1#u64 ⦄ := by
  unfold obj.Reply.prev obj.Reply.prev_raw; step*; simp_all [rPrevA]
/-- The head bit of a reply's `next` word. -/
def headBit (v : U64) : Bool := (v &&& 1#u64) != 0#u64

theorem zero_masked (x : U64) : (0#u64 &&& x) &&& ~~~1#u64 = 0#u64 := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : (0#u64).bv = 0#64 := rfl
  simp [UScalar.bv_and, this]
theorem zero_masked' (x y : U64) (hy : y &&& ~~~1#u64 = 0#u64) : ((0#u64 &&& x) ||| y) &&& ~~~1#u64 = 0#u64 := by
  have h0 : (0#u64).bv = 0#64 := rfl
  have := congrArg UScalar.bv hy
  simp only [UScalar.bv_and, UScalar.bv_not, h0] at this
  apply eq_of_bv
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, h0, BitVec.zero_and, BitVec.zero_or]
  exact this
theorem one_masked : (1#u64) &&& ~~~1#u64 = 0#u64 := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : (0#u64).bv = 0#64 := rfl
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, one_bit, this,
    BitVec.getLsbD_zero]
  by_cases h0 : i = 0 <;> simp [h0, hi]
theorem zero_or_masked : (0#u64) &&& ~~~1#u64 = 0#u64 := by
  apply eq_of_bv; have : (0#u64).bv = 0#64 := rfl; simp [UScalar.bv_and, this]

@[step] theorem obj.Reply.next_is_head.spec (s : S) (r : obj.Reply) :
    obj.Reply.next_is_head st r s ⦃ b => b = headBit (L.mem s (rNextA r)) ⦄ := by
  unfold obj.Reply.next_is_head obj.Reply.next_raw
  simp [lift, L.read_eq, headBit, rNextA]
@[step] theorem obj.Reply.set_prev.spec (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_prev st r s v ⦃ s' => ∃ w, s' = L.wr s (rPrevA r) w ∧ (v = 0#u64 → w &&& ~~~1#u64 = 0#u64) ⦄ := by
  unfold obj.Reply.set_prev obj.Reply.set_prev_raw
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok]
  exact ⟨_, rfl, fun e => by subst e; exact zero_masked _⟩
@[step] theorem obj.Reply.set_next.spec (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_next st r s v false ⦃ s' =>
      ∃ w, s' = L.wr s (rNextA r) w ∧ (v = 0#u64 → w &&& ~~~1#u64 = 0#u64) ⦄ := by
  unfold obj.Reply.set_next obj.Reply.set_next_raw
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl, fun e => by subst e; exact zero_masked' _ _ zero_or_masked⟩
@[step] theorem obj.Sc.set_reply.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_reply st sc s v ⦃ s' => s' = L.wr s (scReplyA sc) v ⦄ := by
  unfold obj.Sc.set_reply; step*; simp_all [scReplyA]

theorem ts_inactive : sched.TS_INACTIVE = 0#u64 := by unfold sched.TS_INACTIVE; rfl
theorem ts_reply : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl

theorem not_blocked_inactive : ¬ Blocked sched.TS_INACTIVE := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  unfold Blocked; rw [h3, h4, h6, ts_inactive]; decide
theorem not_runnable_inactive : ¬ Runnable sched.TS_INACTIVE := by
  obtain ⟨h1, h2, -⟩ := ts_vals
  unfold Runnable; rw [h1, h2, ts_inactive]; simp [sched.TS_RUNNING_VM]
theorem not_blocked_reply : ¬ Blocked sched.TS_BLOCKED_ON_REPLY := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  unfold Blocked; rw [h3, h4, h6, ts_reply]; decide
theorem not_runnable_reply : ¬ Runnable sched.TS_BLOCKED_ON_REPLY := by
  obtain ⟨h1, h2, -⟩ := ts_vals
  unfold Runnable; rw [h1, h2, ts_reply]; simp [sched.TS_RUNNING_VM]
theorem not_runnable_of_blocked {v : U64} (h : Blocked v) : ¬ Runnable v := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := ts_vals
  unfold Blocked at h; unfold Runnable
  rw [h1, h2]; rw [h3, h4, h6] at h
  rcases h with rfl | rfl | rfl <;> simp [sched.TS_RUNNING_VM]
theorem runnable_ne_reply {v : U64} (h : Runnable v) : v ≠ sched.TS_BLOCKED_ON_REPLY :=
  fun e => not_runnable_reply (e ▸ h)
theorem runnable_ne_recv {v : U64} (h : Runnable v) : v ≠ sched.TS_BLOCKED_ON_RECV :=
  fun e => not_runnable_of_blocked (Or.inr (Or.inl e)) h

/-! ## Invariant helpers -/

theorem SchedQueuesInvX.congrX {X X' : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : ∀ y, y ∈ X ↔ y ∈ X') : SchedQueuesInvX st T Cs Ω H X' s Q R := by
  have : X = X' := Set.ext hX
  subst this; exact h

/-- A thread that is not runnable is in no scheduler queue and no switch-to
candidate, so `set_thread_state` may give it any non-runnable state. -/
theorem hq_of_not_runnable {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hr : ¬ Runnable (L.mem s (stA t))) :
    (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v) :=
  ⟨fun c hc p hp hm => absurd (h.runQ c hc p hp t hm) hr, fun c hc hm => absurd (h.runR c hc t hm) hr,
   fun e => absurd (by have := (h.actOK (e ▸ ht)).1; rw [e] at this; exact this) hr⟩

theorem maxA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (maxA c).val = c.val + 72 := by
  unfold maxA; rw [sc_word_val hP hz (by simp [layout.sc.REFILL_MAX])]; simp [layout.sc.REFILL_MAX]
theorem sporA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (sporA c).val = c.val + 64 := by
  unfold sporA; rw [sc_word_val hP hz (by simp [layout.sc.SPORADIC])]; simp [layout.sc.SPORADIC]

theorem maxA_facts (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) :
    Aligned (maxA c) ∧ c.val ≤ (maxA c).val ∧ (maxA c).val < c.val + 2 ^ Z c := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have := maxA_val hP hz
  exact ⟨by unfold Aligned; omega, by omega, by omega⟩
theorem headA_val' {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (headA c).val = c.val + 80 := by
  unfold headA; rw [sc_word_val hP hz (by simp [layout.sc.REFILL_HEAD])]; simp [layout.sc.REFILL_HEAD]
theorem tailA_val' {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (tailA c).val = c.val + 88 := by
  unfold tailA; rw [sc_word_val hP hz (by simp [layout.sc.REFILL_TAIL])]; simp [layout.sc.REFILL_TAIL]
theorem scReplyA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (scReplyA c).val = c.val + 32 := by
  unfold scReplyA; rw [sc_word_val hP hz (by simp [layout.sc.REPLY])]; simp [layout.sc.REPLY]
theorem scNtfnA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) : (scNtfnA c).val = c.val + 40 := by
  unfold scNtfnA; rw [sc_word_val hP hz (by simp [layout.sc.NTFN])]; simp [layout.sc.NTFN]
theorem scYieldA_val {c : U64} {z : Nat} (hP : Placed c z) (hz : 7 ≤ z) :
    (core.num.U64.wrapping_add c layout.sc.YIELD_FROM).val = c.val + 56 := by
  rw [sc_word_val hP hz (by simp [layout.sc.YIELD_FROM])]; simp [layout.sc.YIELD_FROM]

/-- What `cancel_ipc` keeps, for the other invariants: the TCB fields other
than the `Ep` links and `t`'s state and fault word; the current, idle and
SC words of the node; the action, or it becomes choose-new; the reply
objects' `TCB` words, except one naming `t`; their `prev`/`next` links, or
they are cleared; the SCs' `TCB`, `CORE` and ring-header words. -/
structure KeepT0 (st : machine.Store S) [L : LawfulStore st] (T Cs Rp Scs Nt : Set U64) (t : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
    (y = t → K.val ≠ 3328 ∧ K.val ≠ 3376) →
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) →
    L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o)
  act : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64
  rtcb : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∨ (L.mem s (rTcbA r) = t ∧ L.mem s' (rTcbA r) = 0#u64)
  rlink : ∀ r ∈ Rp, (L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∨ L.mem s' (rPrevA r) &&& ~~~1#u64 = 0#u64) ∧
    (L.mem s' (rNextA r) = L.mem s (rNextA r) ∨ L.mem s' (rNextA r) &&& ~~~1#u64 = 0#u64)
  fix : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c) ∧
    L.mem s' (maxA c) = L.mem s (maxA c) ∧ L.mem s' (headA c) = L.mem s (headA c) ∧
    L.mem s' (tailA c) = L.mem s (tailA c)
  /-- The SCs' `REPLY` words are kept or cleared. -/
  srep : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) ∨ L.mem s' (scReplyA c) = 0#u64
  /-- The notifications' `SC` words are kept. -/
  nsc : ∀ n ∈ Nt, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n)
  /-- The timer-tree words of the nodes and the notifications' `BOUND_TCB`
  words are kept. -/
  tnd : ∀ c ∈ Cs, ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  ntb : ∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n)
  /-- The SCs' `NTFN` words are kept. -/
  snt : ∀ c ∈ Scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c)
  /-- The SCs' `YIELD_FROM` words are kept or cleared. -/
  syf : ∀ c ∈ Scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c) ∨ L.mem s' (scYieldFromA c) = 0#u64
  /-- The SCs' `SPORADIC` words are kept. -/
  spf : ∀ c ∈ Scs, L.mem s' (sporA c) = L.mem s (sporA c)
  /-- `t`'s reply-object field is kept. -/
  rpt : t ∈ T → L.mem s' (replyA t) = L.mem s (replyA t)

theorem KeepT0.refl (t : U64) (s : S) : KeepT0 st T Cs Rp Scs Nt t s s :=
  ⟨rfl, rfl, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, Or.inl rfl, fun _ _ => Or.inl rfl,
   fun _ _ => ⟨Or.inl rfl, Or.inl rfl⟩, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => Or.inl rfl, fun _ _ => rfl,
   fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => Or.inl rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem KeepT0.zero {t : U64} {s s' : S} (k : KeepT0 st T Cs Rp Scs Nt t s s') {r : U64} (hr : r ∈ Rp)
    (h0 : L.mem s (rTcbA r) = 0#u64) : L.mem s' (rTcbA r) = 0#u64 := by
  rcases k.rtcb r hr with e | ⟨-, e⟩
  · rw [e, h0]
  · exact e

theorem KeepT0.trans {t : U64} {s₁ s₂ s₃ : S} (h₁ : KeepT0 st T Cs Rp Scs Nt t s₁ s₂) (h₂ : KeepT0 st T Cs Rp Scs Nt t s₂ s₃) :
    KeepT0 st T Cs Rp Scs Nt t s₁ s₃ := by
  refine ⟨h₂.ksb.trans h₁.ksb, h₂.cpu.trans h₁.cpu, fun y hy K a b c d e => (h₂.fld y hy K a b c d e).trans
    (h₁.fld y hy K a b c d e), fun o ho => (h₂.nd o ho).trans (h₁.nd o ho), ?_, fun r hr => ?_, fun r hr => ?_,
    fun c hc => ?_, fun c hc => ?_, fun n hn => (h₂.nsc n hn).trans (h₁.nsc n hn),
    fun c hc o ho => by
      have h2 := h₂.tnd c hc o ho
      rw [nodeAt_of_ksb h₁.ksb] at h2
      exact h2.trans (h₁.tnd c hc o ho),
    fun n hn => (h₂.ntb n hn).trans (h₁.ntb n hn), fun c hc => (h₂.snt c hc).trans (h₁.snt c hc),
    fun c hc => by
      rcases h₂.syf c hc with e | e
      · rw [e]; exact h₁.syf c hc
      · exact Or.inr e,
    fun c hc => (h₂.spf c hc).trans (h₁.spf c hc), fun ht => (h₂.rpt ht).trans (h₁.rpt ht)⟩
  · rcases h₂.act with e | e
    · rw [e]; exact h₁.act
    · exact Or.inr e
  · rcases h₂.rtcb r hr with e | ⟨e, e0⟩
    · rcases h₁.rtcb r hr with e' | ⟨e', e0'⟩
      · exact Or.inl (e.trans e')
      · exact Or.inr ⟨e', e.trans e0'⟩
    · rcases h₁.rtcb r hr with e' | ⟨e', e0'⟩
      · exact Or.inr ⟨e' ▸ e, e0⟩
      · exact Or.inr ⟨e', e0⟩
  · obtain ⟨p2, n2⟩ := h₂.rlink r hr
    obtain ⟨p1, n1⟩ := h₁.rlink r hr
    refine ⟨?_, ?_⟩
    · rcases p2 with e | e
      · rw [e]; exact p1
      · exact Or.inr e
    · rcases n2 with e | e
      · rw [e]; exact n1
      · exact Or.inr e
  · obtain ⟨a2, b2, c2, d2, e2⟩ := h₂.fix c hc
    obtain ⟨a1, b1, c1, d1, e1⟩ := h₁.fix c hc
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1⟩
  · rcases h₂.srep c hc with e | e
    · rw [e]; exact h₁.srep c hc
    · exact Or.inr e

/-- The SCs' `REPLY` words are kept, or the only ones cleared held `t`'s
reply object, whose `NEXT` link is cleared too (so no reply-stack head is
left dangling, `RHead`). -/
def KZ (st : machine.Store S) [L : LawfulStore st] (T Rp Scs : Set U64) (t : U64) (s s' : S) : Prop :=
  (∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c)) ∨
  (t ∈ T ∧ L.mem s (replyA t) ∈ Rp ∧ L.mem s' (rNextA (L.mem s (replyA t))) &&& ~~~1#u64 = 0#u64 ∧
    ∀ c ∈ Scs, L.mem s' (scReplyA c) ≠ L.mem s (scReplyA c) → L.mem s (scReplyA c) = L.mem s (replyA t))

/-- What the cancel and state-change steps keep (`KeepT0`), and `KZ`. -/
structure KeepT (st : machine.Store S) [L : LawfulStore st] (T Cs Rp Scs Nt : Set U64) (t : U64) (s s' : S) : Prop
    extends KeepT0 st T Cs Rp Scs Nt t s s' where
  kz : KZ st T Rp Scs t s s'

theorem KeepT.refl (t : U64) (s : S) : KeepT st T Cs Rp Scs Nt t s s :=
  ⟨KeepT0.refl t s, Or.inl fun _ _ => rfl⟩

theorem KeepT.zero {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') {r : U64} (hr : r ∈ Rp)
    (h0 : L.mem s (rTcbA r) = 0#u64) : L.mem s' (rTcbA r) = 0#u64 := k.toKeepT0.zero hr h0

/-- `KZ` after a `KeepT0` prefix whose cleared `REPLY` words held `t`'s
reply object, followed by a `KeepT`, when `t`'s reply object ends unlinked. -/
theorem KeepT.of0 {t : U64} {s₁ s₂ s₃ : S} (ht : t ∈ T) (h₁ : KeepT0 st T Cs Rp Scs Nt t s₁ s₂)
    (h₂ : KeepT st T Cs Rp Scs Nt t s₂ s₃) (hr0 : L.mem s₁ (replyA t) ∈ Rp)
    (hch : ∀ c ∈ Scs, L.mem s₂ (scReplyA c) ≠ L.mem s₁ (scReplyA c) → L.mem s₁ (scReplyA c) = L.mem s₁ (replyA t))
    (hn : L.mem s₃ (rNextA (L.mem s₁ (replyA t))) &&& ~~~1#u64 = 0#u64) :
    KeepT st T Cs Rp Scs Nt t s₁ s₃ := by
  have er : L.mem s₂ (replyA t) = L.mem s₁ (replyA t) := h₁.rpt ht
  refine ⟨KeepT0.trans h₁ h₂.toKeepT0, Or.inr ⟨ht, hr0, hn, fun c hc hne => ?_⟩⟩
  by_cases e1 : L.mem s₂ (scReplyA c) = L.mem s₁ (scReplyA c)
  · rw [← e1]
    rcases h₂.kz with hk | ⟨-, -, -, hz⟩
    · exact absurd ((hk c hc).trans e1) hne
    · rw [← er]; exact hz c hc (by rw [e1]; exact hne)
  · exact hch c hc e1

theorem KeepT.trans {t : U64} {s₁ s₂ s₃ : S} (h₁ : KeepT st T Cs Rp Scs Nt t s₁ s₂)
    (h₂ : KeepT st T Cs Rp Scs Nt t s₂ s₃) : KeepT st T Cs Rp Scs Nt t s₁ s₃ := by
  rcases h₁.kz with k1 | ⟨ht, hr0, hn1, hz1⟩
  · rcases h₂.kz with k2 | ⟨ht, hr0', hn2, hz2⟩
    · exact ⟨KeepT0.trans h₁.toKeepT0 h₂.toKeepT0, Or.inl fun c hc => (k2 c hc).trans (k1 c hc)⟩
    · have er : L.mem s₂ (replyA t) = L.mem s₁ (replyA t) := h₁.rpt ht
      rw [er] at hr0' hn2
      refine ⟨KeepT0.trans h₁.toKeepT0 h₂.toKeepT0, Or.inr ⟨ht, hr0', hn2, fun c hc hne => ?_⟩⟩
      rw [← k1 c hc, ← er]
      exact hz2 c hc (by rw [k1 c hc]; exact hne)
  · have er : L.mem s₂ (replyA t) = L.mem s₁ (replyA t) := h₁.rpt ht
    refine ⟨KeepT0.trans h₁.toKeepT0 h₂.toKeepT0, Or.inr ⟨ht, hr0, ?_, fun c hc hne => ?_⟩⟩
    · rcases (h₂.rlink _ hr0).2 with e | e
      · rw [e]; exact hn1
      · exact e
    · by_cases e1 : L.mem s₂ (scReplyA c) = L.mem s₁ (scReplyA c)
      · rw [← e1]
        rcases h₂.kz with k2 | ⟨-, -, -, hz2⟩
        · exact absurd ((k2 c hc).trans e1) hne
        · rw [← er]; exact hz2 c hc (by rw [e1]; exact hne)
      · exact hz1 c hc e1

theorem KeepT.hch {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') :
    ∀ c ∈ Scs, L.mem s' (scReplyA c) ≠ L.mem s (scReplyA c) → L.mem s (scReplyA c) = L.mem s (replyA t) :=
  fun c hc hne => by
    rcases k.kz with k1 | ⟨-, -, -, hz⟩
    · exact absurd (k1 c hc) hne
    · exact hz c hc hne

theorem node_ne_node {s : S} {c c' o o' : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s c')
    (ho : o.val < 4288) (ho' : o'.val < 4288) (hne : c = c' → o.val ≠ o'.val) :
    (L.nodeAt s c o).val ≠ (L.nodeAt s c' o').val := by
  by_cases e : c = c'
  · subst e; rw [nodeAt_val hN ho, nodeAt_val hN' ho']; have := hne rfl; omega
  · intro e'; exact nodeAt_ne_cpu hN hN' ho ho' e (UScalar.eq_of_val_eq e')

/-- One write keeps `KeepT` if it avoids the kept words (or writes the
action as choose-new, a reply `TCB` word naming `t`, or a cleared link). -/
theorem keep_wr0 {s : S} {t a v : U64}
    (hT : TcbPlaced T) (hN' : NodePlaced st T s (L.cpu s)) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ha : Aligned a)
    (hf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3376) → a.val ≠ (core.num.U64.wrapping_add y K).val)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) → a.val ≠ (L.nodeAt s (L.cpu s) o).val)
    (h16 : a.val = (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val → v = 1#u64)
    (hr : ∀ r ∈ Rp, (a.val = (rTcbA r).val → L.mem s (rTcbA r) = t ∧ v = 0#u64) ∧
      (a.val = (rPrevA r).val → v &&& ~~~1#u64 = 0#u64) ∧ (a.val = (rNextA r).val → v &&& ~~~1#u64 = 0#u64))
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hsr : ∀ c ∈ Scs, a.val = (scReplyA c).val → v = 0#u64)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val)
    (hNs : ∀ c ∈ Cs, NodePlaced st T s c)
    (htn : ∀ c ∈ Cs, ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → a.val ≠ (L.nodeAt s c o).val)
    (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val) (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val)
    (hsy : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → v = 0#u64) (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val) :
    KeepT0 st T Cs Rp Scs Nt t s (L.wr s a v) := by
  have rpa : ∀ r ∈ Rp, Aligned (rTcbA r) ∧ Aligned (rPrevA r) ∧ Aligned (rNextA r) := fun r hr => by
    have hp := hO.rp r hr
    refine ⟨?_, ?_, ?_⟩ <;> unfold Aligned
    · rw [rTcbA_val hp]; omega
    · rw [rPrevA_val hp]; omega
    · rw [rNextA_val hp]; omega
  have sca : ∀ c ∈ Scs, ∀ o : U64, o.val < 128 → o.val % 8 = 0 → Aligned (core.num.U64.wrapping_add c o) :=
    fun c hc o ho h8 => by
      obtain ⟨hP, hz⟩ := hO.sc c hc
      have := (sc_lo hP hz).1
      unfold Aligned; rw [sc_word_val hP hz ho]; omega
  have g : ∀ b, Aligned b → a.val ≠ b.val → L.mem (L.wr s a v) b = L.mem s b := fun b hb hne =>
    L.mem_wr_ne ha hb hne
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun y hy K h1 h2 h3 h4 h5 => ?_, fun o ho => ?_, ?_,
    fun r hr' => ?_, fun r hr' => ?_, fun c hc' => ?_, fun c hc' => ?_,
    fun n hn => g _ (hO.ntAl n hn) (hnt n hn),
    fun c hc o ho => g _ (nodeAt_aligned (hNs c hc) (by omega) (by omega)) (htn c hc o ho),
    fun n hn => g _ (by unfold Aligned; rw [ntfnBtA_val (hO.ntP n hn)]; have := (hO.ntP n hn).1; omega) (hnb n hn),
    fun c hc => g _ (sca c hc _ (by simp [layout.sc.NTFN]) (by simp [layout.sc.NTFN])) (hsn c hc),
    fun c hc => by
      unfold scYieldFromA
      rw [L.mem_wr_val ha (sca c hc _ (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM]))]
      split
      · exact Or.inr (hsy c hc ‹_›)
      · exact Or.inl rfl,
    fun c hc => g _ (sca c hc _ (by simp [layout.sc.SPORADIC]) (by simp [layout.sc.SPORADIC])) (hsp c hc),
    fun ht => g _ (field_aligned (hT t ht) (K := 3360#u64) (by simp) (by simp))
      (hf t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩))⟩
  rotate_right
  · unfold scReplyA
    rw [L.mem_wr_val ha (sca c hc' _ (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY]))]
    split
    · exact Or.inr (hsr c hc' ‹_›)
    · exact Or.inl rfl
  · exact g _ (field_aligned (hT y hy) h1 h2) (hf y hy K h1 h2 h3 h4 h5)
  · simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact g _ (nodeAt_aligned hN' (by omega) (by omega)) (hn o ho)
  · unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    rw [L.mem_wr_val ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))]
    split
    · exact Or.inr (h16 ‹_›)
    · exact Or.inl rfl
  · rw [L.mem_wr_val ha (rpa r hr').1]
    split
    · exact Or.inr ((hr r hr').1 ‹_›)
    · exact Or.inl rfl
  · refine ⟨?_, ?_⟩
    · rw [L.mem_wr_val ha (rpa r hr').2.1]
      split
      · exact Or.inr ((hr r hr').2.1 ‹_›)
      · exact Or.inl rfl
    · rw [L.mem_wr_val ha (rpa r hr').2.2]
      split
      · exact Or.inr ((hr r hr').2.2 ‹_›)
      · exact Or.inl rfl
  · obtain ⟨c1, c2, c3, c4, c5⟩ := hc c hc'
    exact ⟨g _ (sca c hc' _ (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])) c1,
      g _ (sca c hc' _ (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])) c2,
      g _ (sca c hc' _ (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])) c3,
      g _ (sca c hc' _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD])) c4,
      g _ (sca c hc' _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL])) c5⟩

/-- `keep_wr0`, for a write that is no SC's `REPLY` word (so `KZ` holds). -/
theorem keep_wr {s : S} {t a v : U64}
    (hT : TcbPlaced T) (hN' : NodePlaced st T s (L.cpu s)) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ha : Aligned a)
    (hf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3376) → a.val ≠ (core.num.U64.wrapping_add y K).val)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) → a.val ≠ (L.nodeAt s (L.cpu s) o).val)
    (h16 : a.val = (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val → v = 1#u64)
    (hr : ∀ r ∈ Rp, (a.val = (rTcbA r).val → L.mem s (rTcbA r) = t ∧ v = 0#u64) ∧
      (a.val = (rPrevA r).val → v &&& ~~~1#u64 = 0#u64) ∧ (a.val = (rNextA r).val → v &&& ~~~1#u64 = 0#u64))
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hsr : ∀ c ∈ Scs, a.val ≠ (scReplyA c).val)
    (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val)
    (hNs : ∀ c ∈ Cs, NodePlaced st T s c)
    (htn : ∀ c ∈ Cs, ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → a.val ≠ (L.nodeAt s c o).val)
    (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val) (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val)
    (hsy : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → v = 0#u64) (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val) :
    KeepT st T Cs Rp Scs Nt t s (L.wr s a v) := by
  refine ⟨keep_wr0 hT hN' hO ha hf hn h16 hr hc (fun c hc e => absurd e (hsr c hc)) hnt hNs htn hnb hsn hsy hsp,
    Or.inl fun c hc => L.mem_wr_ne ha ?_ (hsr c hc)⟩
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have := (sc_lo hP hz).1
  unfold Aligned; rw [scReplyA_val hP hz]; omega

/-- The words `KeepT` watches that lie in reply objects or SCs are words of
`Ω`, so a TCB field or node word avoids them. -/
theorem objs_omega (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    (∀ r ∈ Rp, rTcbA r ∈ Ω ∧ rPrevA r ∈ Ω ∧ rNextA r ∈ Ω) ∧
    (∀ c ∈ Scs, scTcbA c ∈ Ω ∧ scCoreA c ∈ Ω ∧ maxA c ∈ Ω ∧ headA c ∈ Ω ∧ tailA c ∈ Ω) := by
  refine ⟨fun r hr => ⟨hsub _ (hO.tcbW hr), hsub _ (hO.prevW hr), hsub _ (hO.nextW hr)⟩, fun c hc => ?_⟩
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have w : ∀ o : U64, o.val < 128 → o.val % 8 = 0 → core.num.U64.wrapping_add c o ∈ Ω := fun o ho h8' =>
    hO.scW c hc _ (by unfold Aligned; rw [sc_word_val hP hz ho]; omega)
      ⟨by rw [sc_word_val hP hz ho]; omega, by rw [sc_word_val hP hz ho]; omega⟩
  exact ⟨w _ (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB]), w _ (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE]),
    w _ (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX]),
    w _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]),
    w _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL])⟩

/-- An SC's `SPORADIC` word is in `Ω`. -/
theorem spor_omega (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) : sporA c ∈ Ω := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have := sporA_val hP hz
  exact hO.scW c hc _ (by unfold Aligned; omega) ⟨by omega, by omega⟩

/-- A write outside `Ω` (a TCB field or a node word) avoids the watched
object words. -/
theorem keep_wr_out {s : S} {t a v : U64}
    (hT : TcbPlaced T) (hN' : NodePlaced st T s (L.cpu s)) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (ha : Aligned a) (hout : ∀ b ∈ Ω, a.val ≠ b.val)
    (hf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3376) → a.val ≠ (core.num.U64.wrapping_add y K).val)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) → a.val ≠ (L.nodeAt s (L.cpu s) o).val)
    (h16 : a.val = (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val → v = 1#u64)
    (hNs : ∀ c ∈ Cs, NodePlaced st T s c)
    (htn : ∀ c ∈ Cs, ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → a.val ≠ (L.nodeAt s c o).val) :
    KeepT st T Cs Rp Scs Nt t s (L.wr s a v) := by
  obtain ⟨hr, hc⟩ := objs_omega hO hsub
  refine keep_wr hT hN' hO ha hf hn h16 (fun r hr' => ⟨fun e => absurd e (hout _ (hr r hr').1),
    fun e => absurd e (hout _ (hr r hr').2.1), fun e => absurd e (hout _ (hr r hr').2.2)⟩) (fun c hc' => ?_)
    (fun c hc' => hout _ (hsub _ (hO.repW c hc')))
    (fun n hn e => absurd e (hout _ (hsub _ (hO.ntW n hn)))) hNs htn
    (fun n hn => hout _ (hsub _ (hO.ntB n hn).2)) (fun c hc => hout _ (hsub _ (hO.snW c hc)))
    (fun c hc e => absurd e (hout _ (hsub _ (hO.syW c hc)))) (fun c hc => hout _ (spor_omega hO hc))
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc c hc'
  exact ⟨hout _ c1, hout _ c2, hout _ c3, hout _ c4, hout _ c5⟩

/-- After `set_thread_state t v`, `t`'s state is `v`, and the rest is kept. -/
theorem sched.set_thread_state.state {X : Set U64} (s : S) (t : obj.Tcb) (v : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    sched.set_thread_state st s t v ⦃ s' => L.mem s' (stA t) = v ∧ KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  have hta := h.tcbs t ht
  have hsa : Aligned (stA t) := by rw [stA_eq]; exact field_aligned hta (by simp) (by simp)
  have hN' := h.nodes _ h.cur
  unfold sched.set_thread_state sched.schedule_tcb
  step with obj.Tcb.set_state.spec as ⟨s1, s1_post⟩
  subst s1_post
  have e1 : L.mem (L.wr s (stA t) v) (stA t) = v := L.mem_wr_same hsa
  have k1 : KeepT st T Cs Rp Scs Nt t s (L.wr s (stA t) v) := by
    refine keep_wr_out h.tcbs hN' hO hsub hsa (fun b hb => ?_) (fun y hy K hK hK8 _ _ hyt => ?_) (fun o _ => ?_)
      (fun e => ?_) h.nodes (fun c hc o ho e => by
        rw [stA_eq] at e
        exact node_ne_field (h.nodes c hc) (o := o) (by omega) ht hta (by simp) (UScalar.eq_of_val_eq e.symm))
    · rw [stA_eq]; exact out_ne_field (h.omega b hb) ht hta (by simp)
    · rw [stA_eq]
      exact fun e => field_ne hta (h.tcbs y hy) (by simp) hK (fun ey e' => (hyt ey.symm).1 (by simp at e'; omega))
        (UScalar.eq_of_val_eq e)
    · rw [stA_eq]; exact fun e => node_ne_field hN' (by omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm
    · rw [stA_eq] at e
      exact absurd (UScalar.eq_of_val_eq e).symm (node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp))
  have hO1 : ObjsOK st Ω Sg Rp Scs Nt Z (L.wr s (stA t) v) := hO.ksb
  have hN1 : NodePlaced st T (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) := by rw [L.cpu_wr]; exact hN'.wr
  have kn : KeepT st T Cs Rp Scs Nt t (L.wr s (stA t) v)
      (L.wr (L.wr s (stA t) v) (L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION)
        sched.ACTION_CHOOSE_NEW) := by
    refine keep_wr_out h.tcbs hN1 hO1 hsub (nodeAt_aligned hN1 (by rw [act_val]; omega) (by rw [act_val]))
      (fun b hb => ?_) (fun y hy K hK _ _ _ _ => ?_) (fun o ho => ?_) (fun _ => choose_val)
      (fun c hc => (h.nodes c hc).wr) (fun c hc o ho => by
        simp only [LawfulStore.cpu_wr, nodeAt_wr]
        exact node_ne_node hN' (h.nodes c hc) (by rw [act_val]; omega) (by omega) (fun _ => by rw [act_val]; omega))
    · simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact out_ne_node (h.omega b hb) h.cur hN' (by rw [act_val]; omega)
    · simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact fun e => node_ne_field hN' (by rw [act_val]; omega) hy (h.tcbs y hy) hK (UScalar.eq_of_val_eq e)
    · simp only [LawfulStore.cpu_wr, nodeAt_wr]
      intro e
      rw [nodeAt_val hN' (by rw [act_val]; omega), nodeAt_val hN' (by omega)] at e
      rw [act_val] at e; omega
  step*
  all_goals first | exact ⟨e1, k1⟩ | skip
  subst_vars
  refine ⟨?_, k1.trans kn⟩
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  rw [L.mem_wr_ne (nodeAt_aligned (h.nodes _ h.cur) (by rw [act_val]; omega) (by rw [act_val])) hsa]
  · exact e1
  · intro e; rw [stA_eq] at e
    exact node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e)

/-- `set_thread_state t INACTIVE` for a thread that is not runnable and in
no endpoint queue (or excepted). -/
theorem sts_inactive {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hr : ¬ Runnable (L.mem s (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t))) :
    sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s' =>
      SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧
      KeepT st T Cs Rp Scs Nt t s s' ⦄ :=
  WP.spec_and (sched.set_thread_state.inv s t _ Q R h ht not_blocked_inactive hx (hq_of_not_runnable h ht hr))
    (sched.set_thread_state.state s t _ Q R h ht hO hsub)

/-- A write to a word of `Ω`. -/
theorem free_wr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) : WritesIn st s (L.wr s a v) (L.Free s Ω Cs) :=
  (writesIn_wr (h.omega a ha).1).mono fun b hb => Or.inl (hb ▸ ha)

/-- Words of `Ω` are no TCB fields. -/
theorem omega_ne_field {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a y K : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) :
    a ≠ core.num.U64.wrapping_add y K := fun e =>
  out_ne_field (h.omega a ha) hy (h.tcbs y hy) hK (congrArg UScalar.val e).symm

theorem mem_wr_omega {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a b v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hb : b = core.num.U64.wrapping_add y K) : L.mem (L.wr s a v) b = L.mem s b := by
  subst hb
  exact L.mem_wr_ne (h.omega a ha).1 (field_aligned (h.tcbs y hy) hK hK8)
    (fun e => omega_ne_field h ha hy hK (UScalar.eq_of_val_eq e))

/-! ## Endpoint and notification dequeue -/

theorem endpoint.ep_dequeue.foot (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    endpoint.ep_dequeue st s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄ := by
  unfold endpoint.ep_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨-, hf1, -, -⟩ := h1
  step*
  all_goals subst_vars; exact reorder_foot_tail hE hf1.writesIn

theorem notification.ntfn_dequeue.foot (s : S) (n : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T n) (h : QueueRel (L.mem s) T .Ep (L.epQ s n) xs) (ht : t ∈ xs) :
    notification.ntfn_dequeue st s n t ⦃ s' => WritesIn st s s' (EpFoot xs n) ⦄ := by
  unfold notification.ntfn_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨-, hf1, -, -⟩ := h1
  step*
  all_goals subst_vars; exact reorder_foot_tail hE hf1.writesIn

/-- What an endpoint footprint leaves alone: TCB fields other than the `Ep`
links, the words of `Ω`, and the nodes. -/
theorem epfoot_keep {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e : U64} {W : List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E)
    (hWT : ∀ w ∈ W, w ∈ T) (hw : WritesIn st s s' (EpFoot W e)) :
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o)) := by
  have hT := h.tcbs
  obtain ⟨hE, hEN, -⟩ := hEW.1 e he
  have epv : ∀ (a : U64), (a = epHeadA e ∨ a = epTSA e) → a.val = e.val ∨ a.val = e.val + 8 := by
    rintro a (rfl | rfl)
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE)
  refine ⟨fun y hy K hK hK8 h1 h2 => ?_, fun a ha => ?_, fun o ho h8 => ?_⟩
  · refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · rw [nextA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; exact h1) e'
    · rw [prevA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; exact h2) e'
    · have hv := epv _ e'
      rw [field_val (hT y hy) hK] at hv
      have := hE.disj y hy
      omega
  · have ho := h.omega a ha
    refine hw.mem_eq ho.1 ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · have := congrArg UScalar.val e'; rw [nextA_val (hT w (hWT w hw'))] at this
      have := ho.2.1 w (hWT w hw'); simp [nextOff] at *; omega
    · have := congrArg UScalar.val e'; rw [prevA_val (hT w (hWT w hw'))] at this
      have := ho.2.1 w (hWT w hw'); simp [prevOff] at *; omega
    · have hv := epv _ e'
      have := hEW.2.2.1 e he a ha
      omega
  · have hN' := h.nodes _ h.cur
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned hN' ho h8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · exact nodeAt_ne_nextA hN' ho (hWT w hw') (hT w (hWT w hw')) _ e'
    · exact nodeAt_ne_prevA hN' ho (hWT w hw') (hT w (hWT w hw')) _ e'
    · have hv := epv _ e'
      rw [nodeAt_val hN' ho] at hv
      have := hEN.1 _ h.cur
      omega

/-- An `EpFoot` write leaves the words of the nodes alone. -/
theorem epfoot_nodes {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e : U64} {W : List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E)
    (hWT : ∀ w ∈ W, w ∈ T) (hw : WritesIn st s s' (EpFoot W e)) :
    ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
  have hT := h.tcbs
  obtain ⟨hE, hEN, -⟩ := hEW.1 e he
  intro c hc o ho h8
  have hN := h.nodes c hc
  refine hw.mem_eq (nodeAt_aligned hN ho h8) ?_
  rintro (⟨w, hw', e' | e'⟩ | e')
  · exact nodeAt_ne_nextA hN ho (hWT w hw') (hT w (hWT w hw')) _ e'
  · exact nodeAt_ne_prevA hN ho (hWT w hw') (hT w (hWT w hw')) _ e'
  · have hv : (L.nodeAt s c o).val = e.val ∨ (L.nodeAt s c o).val = e.val + 8 := by
      rcases e' with e' | e' <;> rw [e']
      · exact Or.inl epHeadA_val
      · exact Or.inr (epTSA_val hE)
    rw [nodeAt_val hN ho] at hv
    have := hEN.1 c hc
    omega

/-- `KeepT` from a frame: TCB fields other than the `Ep` links (and `t`'s
state and fault word), the words of `Ω`, and the current node's words. -/
theorem KeepT.of_frame {s s' : S} {t : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s)
    (hf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3376) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hΩ : ∀ a ∈ Ω, L.mem s' a = L.mem s a)
    (hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o))
    (hnc : ∀ c ∈ Cs, ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) :
    KeepT st T Cs Rp Scs Nt t s s' := by
  obtain ⟨hr, hcw⟩ := objs_omega hO hsub
  refine ⟨⟨hk, hc, hf, fun o ho => hn o (by omega) (by omega), Or.inl ?_, fun r hr' => Or.inl (hΩ _ (hr r hr').1),
    fun r hr' => ⟨Or.inl (hΩ _ (hr r hr').2.1), Or.inl (hΩ _ (hr r hr').2.2)⟩, fun c hc' => ?_,
    fun c hc' => Or.inl (hΩ _ (hsub _ (hO.repW c hc'))), fun n hn => hΩ _ (hsub _ (hO.ntW n hn)), hnc,
    fun n hn => hΩ _ (hsub _ (hO.ntB n hn).2), fun c hc => hΩ _ (hsub _ (hO.snW c hc)),
    fun c hc => Or.inl (hΩ _ (hsub _ (hO.syW c hc))), fun c hc => hΩ _ (spor_omega hO hc),
    fun ht => hf t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)⟩,
    Or.inl fun c hc' => hΩ _ (hsub _ (hO.repW c hc'))⟩
  · unfold LawfulStore.actionW; exact hn _ (by rw [act_val]; omega) (by rw [act_val])
  · obtain ⟨c1, c2, c3, c4, c5⟩ := hcw c hc'
    exact ⟨hΩ _ c1, hΩ _ c2, hΩ _ c3, hΩ _ c4, hΩ _ c5⟩

/-- seL4 `tcbEPDequeue` of a blocked thread from the object it is blocked
on: it leaves the queue and joins the exception set. -/
theorem dequeue_blocked_inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t)))
    (deq : S → U64 → obj.Tcb → Result S)
    (hrel : ∀ (xs : List U64), EpPlaced T (L.mem s (blockA t)) →
      QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) xs → t ∈ xs →
      deq s (L.mem s (blockA t)) t ⦃ s' => QueueRel (L.mem s') T .Ep (L.epQ s' (L.mem s (blockA t))) (xs.erase t) ∧
        (xs.erase t ≠ [] → L.epState s' (L.mem s (blockA t)) = L.epState s (L.mem s (blockA t))) ∧
        (xs.erase t = [] → L.epState s' (L.mem s (blockA t)) = 0#u64) ⦄)
    (hfoot : ∀ (xs : List U64), EpPlaced T (L.mem s (blockA t)) →
      QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) xs → t ∈ xs →
      deq s (L.mem s (blockA t)) t ⦃ s' => WritesIn st s s' (EpFoot xs (L.mem s (blockA t))) ⦄) :
    deq s (L.mem s (blockA t)) t ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∨ y = t} s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
        L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
      L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ⦄ := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  obtain ⟨he, hmem⟩ := hEW.2.2.2.2.1 t ht htX hb
  obtain ⟨hE, -, hq⟩ := hEW.1 _ he
  refine WP.spec_mono (WP.spec_and (hrel _ hE hq hmem) (hfoot _ hE hq hmem)) ?_
  rintro s' ⟨⟨hq', hst', hz'⟩, hw⟩
  have nd := hq.nodup
  have hWT : ∀ w ∈ EQ (L.mem s (blockA t)), w ∈ T := hq.mem
  obtain ⟨k1, k2, k3⟩ := epfoot_keep h hEW he hWT hw
  refine ⟨inv_ep_step h hEW he hw hq' hst' (fun h0 => ⟨fun _ => hz' h0, fun _ => by rw [hz' h0]; decide⟩)
    (fun y hy => List.mem_of_mem_erase hy) ?_ (fun y hy => Or.inl hy) ?_ ?_,
    k1, k2, k3, hw.1, hw.2.1, epfoot_nodes h hEW he hWT hw⟩
  · intro y hy hn
    by_cases e : y = t
    · exact Or.inr e
    · exact absurd ((List.mem_erase_of_ne e).2 hy) hn
  · rintro y (hy | rfl)
    · exact Or.inl hy
    · exact Or.inr hmem
  · intro y hy hyX
    rw [nd.mem_erase_iff] at hy
    rcases hyX with hyX | rfl
    · exact (hEW.2.2.2.1 _ he y hy.2).1 hyX
    · exact hy.1 rfl

theorem endpoint.ep_dequeue.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t))) :
    endpoint.ep_dequeue st s (L.mem s (blockA t)) t ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∨ y = t} s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
        L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
      L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ⦄ :=
  dequeue_blocked_inv s t Q R h ht htX hb (endpoint.ep_dequeue st)
    (fun xs hE hq hm => WP.spec_mono (endpoint.ep_dequeue.rel s _ t xs h.tcbs hE hq hm) fun _ h' =>
      ⟨h'.1, fun hne => by rw [h'.2, if_neg hne], fun h0 => by rw [h'.2, if_pos h0]⟩)
    (fun xs hE hq hm => endpoint.ep_dequeue.foot s _ t xs h.tcbs hE hq hm)

theorem notification.ntfn_dequeue.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t))) :
    notification.ntfn_dequeue st s (L.mem s (blockA t)) t ⦃ s' =>
      SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∨ y = t} s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
        L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
      L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ⦄ :=
  dequeue_blocked_inv s t Q R h ht htX hb (notification.ntfn_dequeue st)
    (fun xs hE hq hm => WP.spec_mono (notification.ntfn_dequeue.rel s _ t xs h.tcbs hE hq hm) fun _ h' =>
      ⟨h'.1, fun hne => by rw [h'.2, if_neg hne], fun h0 => by rw [h'.2, if_pos h0]⟩)
    (fun xs hE hq hm => notification.ntfn_dequeue.foot s _ t xs h.tcbs hE hq hm)

/-! ## Writes to `Ω` and to the fault field -/

theorem wr_omega {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s a v) Q R ∧
      ∀ y ∈ T, L.mem (L.wr s a v) (stA y) = L.mem s (stA y) :=
  ⟨inv_of_free h (free_wr h ha), fun y hy => mem_wr_omega h ha hy (by simp) (by simp) (stA_eq y)⟩

/-- `clear_fault` writes `t`'s fault word. -/
theorem faults.clear_fault.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    faults.clear_fault st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3376) →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧ L.actionW s' = L.actionW s ∧ KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  unfold faults.clear_fault
  refine WP.spec_mono (obj.Tcb.set_fault_type.spec s t _) fun s' e => ?_
  subst e
  rw [show faultA t = core.num.U64.wrapping_add t 3376#u64 from rfl]
  have hT := h.tcbs
  have hta := hT t ht
  have hN' := h.nodes _ h.cur
  have ha : Aligned (core.num.U64.wrapping_add t 3376#u64) := field_aligned hta (by simp) (by simp)
  have hf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3376) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 3376#u64) fl4_abi.consts.fault.NullFault)
        (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; simpa using (hne rfl).symm)
        (UScalar.eq_of_val_eq e))
  have hΩ : ∀ a ∈ Ω, L.mem (L.wr s (core.num.U64.wrapping_add t 3376#u64) fl4_abi.consts.fault.NullFault) a =
      L.mem s a := fun a ha' =>
    L.mem_wr_ne ha (h.omega a ha').1 (fun e => omega_ne_field h ha' ht (K := 3376#u64) (by simp)
      (UScalar.eq_of_val_eq e).symm)
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add t 3376#u64) fl4_abi.consts.fault.NullFault)
        (L.nodeAt (L.wr s (core.num.U64.wrapping_add t 3376#u64) fl4_abi.consts.fault.NullFault)
          (L.cpu (L.wr s (core.num.U64.wrapping_add t 3376#u64) fl4_abi.consts.fault.NullFault)) o) =
      L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 => by
    rw [L.cpu_wr]; exact nodeword_wr_field hN' ht hta (K := 3376#u64) (by simp) (by simp) ho h8
  refine ⟨inv_wr_field h ht (K := 3376#u64) (by simp) (by simp) (by simp), hf, hΩ, ?_, ?_⟩
  · unfold LawfulStore.actionW; exact hn _ (by rw [act_val]; omega) (by rw [act_val])
  · exact KeepT.of_frame hO hsub (L.ksb_wr _ _ _) (L.cpu_wr _ _ _)
      (fun y hy K a b _ _ c => hf y hy K a b (fun e => (c e).2)) hΩ hn
      (fun c hc o ho => by
        have := nodeword_wr_field (h.nodes c hc) ht hta (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault)
          (o := o) (by simp) (by simp) (by omega) (by omega)
        rwa [nodeAt_wr] at this)

/-! ## Writes to reply objects and SCs -/

/-- A write to a word of `Ω` that is a reply `TCB` word naming `t`, a cleared
reply link, or another SC word keeps `KeepT`. -/
theorem keep_omega_wr0 {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (haΩ : a ∈ Ω)
    (hr : ∀ r ∈ Rp, (a.val = (rTcbA r).val → L.mem s (rTcbA r) = t ∧ v = 0#u64) ∧
      (a.val = (rPrevA r).val → v &&& ~~~1#u64 = 0#u64) ∧ (a.val = (rNextA r).val → v &&& ~~~1#u64 = 0#u64))
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hsr : ∀ c ∈ Scs, a.val = (scReplyA c).val → v = 0#u64) (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val)
    (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val) (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val)
    (hsy : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → v = 0#u64) (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val) :
    KeepT0 st T Cs Rp Scs Nt t s (L.wr s a v) := by
  have hN' := h.nodes _ h.cur
  have ho := h.omega a haΩ
  refine keep_wr0 h.tcbs hN' hO ho.1 (fun y hy K hK _ _ _ _ => ?_) (fun o ho' => ?_) (fun e => ?_) hr hc hsr hnt
    h.nodes (fun c hc o ho' => (out_ne_node ho hc (h.nodes c hc) (by omega)).symm) hnb hsn hsy hsp
  · exact (out_ne_field ho hy (h.tcbs y hy) hK).symm
  · exact (out_ne_node ho h.cur hN' (by omega)).symm
  · exact absurd e (out_ne_node ho h.cur hN' (by rw [act_val]; omega)).symm

theorem keep_omega_wr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (haΩ : a ∈ Ω)
    (hr : ∀ r ∈ Rp, (a.val = (rTcbA r).val → L.mem s (rTcbA r) = t ∧ v = 0#u64) ∧
      (a.val = (rPrevA r).val → v &&& ~~~1#u64 = 0#u64) ∧ (a.val = (rNextA r).val → v &&& ~~~1#u64 = 0#u64))
    (hc : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧ a.val ≠ (maxA c).val ∧
      a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val)
    (hsr : ∀ c ∈ Scs, a.val ≠ (scReplyA c).val) (hnt : ∀ n ∈ Nt, a.val ≠ (ntfnScA n).val)
    (hnb : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val) (hsn : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val)
    (hsy : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → v = 0#u64) (hsp : ∀ c ∈ Scs, a.val ≠ (sporA c).val) :
    KeepT st T Cs Rp Scs Nt t s (L.wr s a v) := by
  have hN' := h.nodes _ h.cur
  have ho := h.omega a haΩ
  refine keep_wr h.tcbs hN' hO ho.1 (fun y hy K hK _ _ _ _ => ?_) (fun o ho' => ?_) (fun e => ?_) hr hc hsr hnt
    h.nodes (fun c hc o ho' => (out_ne_node ho hc (h.nodes c hc) (by omega)).symm) hnb hsn hsy hsp
  · exact (out_ne_field ho hy (h.tcbs y hy) hK).symm
  · exact (out_ne_node ho h.cur hN' (by omega)).symm
  · exact absurd e (out_ne_node ho h.cur hN' (by rw [act_val]; omega)).symm

theorem rp_facts (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) :
    r.val % 32 = 0 ∧ (rTcbA r).val = r.val ∧ (rPrevA r).val = r.val + 8 ∧ (rNextA r).val = r.val + 16 := by
  have hp := hO.rp r hr
  exact ⟨hp.1, rTcbA_val hp, rPrevA_val hp, rNextA_val hp⟩

theorem sc_facts (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) :
    128 ≤ 2 ^ Z c ∧ (scTcbA c).val = c.val + 24 ∧ (scCoreA c).val = c.val + 16 ∧ (maxA c).val = c.val + 72 ∧
      (headA c).val = c.val + 80 ∧ (tailA c).val = c.val + 88 ∧ (scReplyA c).val = c.val + 32 ∧
      (core.num.U64.wrapping_add c layout.sc.YIELD_FROM).val = c.val + 56 := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  exact ⟨(sc_lo hP hz).2.1, scTcbA_val hP hz, scCoreA_val hP hz, maxA_val hP hz, headA_val' hP hz, tailA_val' hP hz,
    scReplyA_val hP hz, scYieldA_val hP hz⟩

/-- A reply word avoids the SCs' watched words. -/
theorem rword_ne_sc (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r a : U64} (hr : r ∈ Rp)
    (ha : r.val ≤ a.val ∧ a.val < r.val + 32) : ∀ c ∈ Scs, a.val ≠ (scTcbA c).val ∧ a.val ≠ (scCoreA c).val ∧
      a.val ≠ (maxA c).val ∧ a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val := by
  intro c hc
  obtain ⟨h128, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
  have := hO.rpSc r hr c hc
  rw [e1, e2, e3, e4, e5]; omega

/-- A reply word is no SC `SPORADIC` word. -/
theorem rword_ne_spor (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r a : U64} (hr : r ∈ Rp)
    (ha : r.val ≤ a.val ∧ a.val < r.val + 32) : ∀ c ∈ Scs, a.val ≠ (sporA c).val := by
  intro c hc
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h128, -⟩ := sc_facts hO hc
  have := hO.rpSc r hr c hc
  rw [sporA_val hP hz]; omega

/-- An SC word at offset `o ≠ 64` below 128 is no SC `SPORADIC` word. -/
theorem scw_ne_spor (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c a : U64} (hc : c ∈ Scs) {o : Nat}
    (ha : a.val = c.val + o) (ho : o < 128) (h64 : o ≠ 64) : ∀ c' ∈ Scs, a.val ≠ (sporA c').val := by
  intro c' hc'
  obtain ⟨hP, hz⟩ := hO.sc c' hc'
  have := (sc_facts hO hc).1; have := (sc_facts hO hc').1
  rw [sporA_val hP hz]
  by_cases e : c = c'
  · subst e; omega
  · have := hO.scDisj c hc c' hc' e; omega

/-- An SC word at offset `o ≠ 32` below 128 is no SC `REPLY` word. -/
theorem scw_ne_screp (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c a : U64} (hc : c ∈ Scs) {o : Nat}
    (ha : a.val = c.val + o) (ho : o < 128) (h32 : o ≠ 32) : ∀ c' ∈ Scs, a.val ≠ (scReplyA c').val := by
  intro c' hc'
  obtain ⟨hP, hz⟩ := hO.sc c' hc'
  have := (sc_facts hO hc).1; have := (sc_facts hO hc').1
  rw [scReplyA_val hP hz]
  by_cases e : c = c'
  · subst e; omega
  · have := hO.scDisj c hc c' hc' e; omega

theorem rword_ne_screp (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r a : U64} (hr : r ∈ Rp)
    (ha : r.val ≤ a.val ∧ a.val < r.val + 32) : ∀ c ∈ Scs, a.val ≠ (scReplyA c).val := by
  intro c hc
  obtain ⟨h128, -, -, -, -, -, e6, -⟩ := sc_facts hO hc
  have := hO.rpSc r hr c hc
  rw [e6]; omega

/-- An SC word at offset `o` (32: `REPLY`, 56: `YIELD_FROM`) is no reply word
and no watched SC word. -/
theorem scword_facts (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c a : U64} (hc : c ∈ Scs)
    (ha : a.val = c.val + 32 ∨ a.val = c.val + 56) :
    (∀ r ∈ Rp, a.val ≠ (rTcbA r).val ∧ a.val ≠ (rPrevA r).val ∧ a.val ≠ (rNextA r).val) ∧
    (∀ c' ∈ Scs, a.val ≠ (scTcbA c').val ∧ a.val ≠ (scCoreA c').val ∧ a.val ≠ (maxA c').val ∧
      a.val ≠ (headA c').val ∧ a.val ≠ (tailA c').val) := by
  obtain ⟨h128, -⟩ := sc_facts hO hc
  refine ⟨fun r hr => ?_, fun c' hc' => ?_⟩
  · obtain ⟨-, e1, e2, e3⟩ := rp_facts hO hr
    have := hO.rpSc r hr c hc
    rw [e1, e2, e3]; omega
  · obtain ⟨h128', e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc'
    rw [e1, e2, e3, e4, e5]
    by_cases e : c = c'
    · subst e; omega
    · have := hO.scDisj c hc c' hc' e; omega

/-- A reply word is no SC `YIELD_FROM` word. -/
theorem rword_ne_scy (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r a : U64} (hr : r ∈ Rp)
    (ha : r.val ≤ a.val ∧ a.val < r.val + 32) : ∀ c ∈ Scs, a.val ≠ (scYieldFromA c).val := by
  intro c hc
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h128, -, -, -, -, -, -, e7⟩ := sc_facts hO hc
  have := hO.rpSc r hr c hc
  rw [show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl, e7]; omega

/-- A reply word is no SC `NTFN` word. -/
theorem rword_ne_scn (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r a : U64} (hr : r ∈ Rp)
    (ha : r.val ≤ a.val ∧ a.val < r.val + 32) : ∀ c ∈ Scs, a.val ≠ (scNtfnA c).val := by
  intro c hc
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h128, -⟩ := sc_facts hO hc
  have := hO.rpSc r hr c hc
  rw [scNtfnA_val hP hz]; omega

theorem keep_rtcb {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t r v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hr : r ∈ Rp) (ht0 : L.mem s (rTcbA r) = t) (hv : v = 0#u64) : KeepT st T Cs Rp Scs Nt t s (L.wr s (rTcbA r) v) := by
  obtain ⟨m, e0, -, -⟩ := rp_facts hO hr
  refine keep_omega_wr h hO (hsub _ (hO.tcbW hr)) (fun r' hr' => ?_) (rword_ne_sc hO hr (by rw [e0]; omega))
    (rword_ne_screp hO hr (by rw [e0]; omega))
    (fun n hn e => by have := hO.ntRp n hn r hr; omega)
    (fun n hn e => by rw [ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
    (rword_ne_scn hO hr (by rw [e0]; omega)) (fun c hc e => absurd e (rword_ne_scy hO hr (by rw [e0]; omega) c hc))
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨h128, -⟩ := sc_facts hO hc
      rw [sporA_val hPc hzc]; have := hO.rpSc r hr c hc; omega)
  obtain ⟨m', e1, e2, e3⟩ := rp_facts hO hr'
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · have : r = r' := UScalar.eq_of_val_eq (by rw [← e0, ← e1]; exact e)
    subst this; exact ⟨ht0, hv⟩
  · rw [e0, e2] at e; omega
  · rw [e0, e3] at e; omega

theorem keep_rprev {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t r v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hr : r ∈ Rp) (hv : v &&& ~~~1#u64 = 0#u64) : KeepT st T Cs Rp Scs Nt t s (L.wr s (rPrevA r) v) := by
  obtain ⟨m, -, e0, -⟩ := rp_facts hO hr
  refine keep_omega_wr h hO (hsub _ (hO.prevW hr)) (fun r' hr' => ?_) (rword_ne_sc hO hr (by rw [e0]; omega))
    (rword_ne_screp hO hr (by rw [e0]; omega))
    (fun n hn e => by have := hO.ntRp n hn r hr; omega)
    (fun n hn e => by rw [ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
    (rword_ne_scn hO hr (by rw [e0]; omega)) (fun c hc e => absurd e (rword_ne_scy hO hr (by rw [e0]; omega) c hc))
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨h128, -⟩ := sc_facts hO hc
      rw [sporA_val hPc hzc]; have := hO.rpSc r hr c hc; omega)
  obtain ⟨m', e1, e2, e3⟩ := rp_facts hO hr'
  refine ⟨fun e => ?_, fun _ => hv, fun e => ?_⟩
  · rw [e0, e1] at e; omega
  · rw [e0, e3] at e; omega

theorem keep_rnext {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t r v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hr : r ∈ Rp) (hv : v &&& ~~~1#u64 = 0#u64) : KeepT st T Cs Rp Scs Nt t s (L.wr s (rNextA r) v) := by
  obtain ⟨m, -, -, e0⟩ := rp_facts hO hr
  refine keep_omega_wr h hO (hsub _ (hO.nextW hr)) (fun r' hr' => ?_) (rword_ne_sc hO hr (by rw [e0]; omega))
    (rword_ne_screp hO hr (by rw [e0]; omega))
    (fun n hn e => by have := hO.ntRp n hn r hr; omega)
    (fun n hn e => by rw [ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntORp n hn r hr; omega)
    (rword_ne_scn hO hr (by rw [e0]; omega)) (fun c hc e => absurd e (rword_ne_scy hO hr (by rw [e0]; omega) c hc))
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨h128, -⟩ := sc_facts hO hc
      rw [sporA_val hPc hzc]; have := hO.rpSc r hr c hc; omega)
  obtain ⟨m', e1, e2, e3⟩ := rp_facts hO hr'
  refine ⟨fun e => ?_, fun e => ?_, fun _ => hv⟩
  · rw [e0, e1] at e; omega
  · rw [e0, e2] at e; omega

/-- An SC's `REPLY` or `YIELD_FROM` word is in `Ω`. -/
theorem scword_omega (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c a : U64} (hc : c ∈ Scs)
    (ha : a = scReplyA c ∨ a = core.num.U64.wrapping_add c layout.sc.YIELD_FROM) : a ∈ Ω := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  obtain ⟨-, -, -, -, -, -, e6, e7⟩ := sc_facts hO hc
  have hv : a.val = c.val + 32 ∨ a.val = c.val + 56 := by
    rcases ha with rfl | rfl
    · exact Or.inl e6
    · exact Or.inr e7
  exact hO.scW c hc a (by unfold Aligned; omega) ⟨by omega, by omega⟩

theorem keep_scw {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t c a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs)
    (ha : a = scReplyA c ∨ a = core.num.U64.wrapping_add c layout.sc.YIELD_FROM)
    (hv0 : a = scReplyA c → v = 0#u64) (hv1 : a = core.num.U64.wrapping_add c layout.sc.YIELD_FROM → v = 0#u64) :
    KeepT0 st T Cs Rp Scs Nt t s (L.wr s a v) := by
  obtain ⟨h128, -, -, -, -, -, e6, e7⟩ := sc_facts hO hc
  have hv : a.val = c.val + 32 ∨ a.val = c.val + 56 := by
    rcases ha with rfl | rfl
    · exact Or.inl e6
    · exact Or.inr e7
  obtain ⟨f1, f2⟩ := scword_facts hO hc hv
  refine keep_omega_wr0 h hO (scword_omega hO hc ha)
    (fun r hr => ⟨fun e => absurd e (f1 r hr).1, fun e => absurd e (f1 r hr).2.1, fun e => absurd e (f1 r hr).2.2⟩)
    f2 (fun c' hc' e => ?_) (fun n hn e => by have := hO.ntSc n hn c hc; rcases hv with hv | hv <;> omega)
    (fun n hn e => by
      rw [ntfnBtA_val (hO.ntP n hn)] at e; have := hO.ntOSc n hn c hc; rcases hv with hv | hv <;> omega)
    (fun c' hc' e => by
      obtain ⟨hP', hz'⟩ := hO.sc c' hc'
      rw [scNtfnA_val hP' hz'] at e
      by_cases hcc : c = c'
      · subst hcc; rcases hv with hv | hv <;> omega
      · have := hO.scDisj c hc c' hc' hcc; have := h128; obtain ⟨h128', -⟩ := sc_facts hO hc'
        rcases hv with hv | hv <;> omega)
    (fun c' hc' e => by
      obtain ⟨h128', -, -, -, -, -, -, e7'⟩ := sc_facts hO hc'
      rw [show scYieldFromA c' = core.num.U64.wrapping_add c' layout.sc.YIELD_FROM from rfl, e7'] at e
      by_cases hcc : c = c'
      · subst hcc
        rcases ha with rfl | rfl
        · rw [e6] at e; omega
        · exact hv1 rfl
      · have := hO.scDisj c hc c' hc' hcc
        rcases hv with hv | hv <;> omega)
    (fun c' hc' => by
      obtain ⟨hP', hz'⟩ := hO.sc c' hc'; obtain ⟨h128', -⟩ := sc_facts hO hc'
      rw [sporA_val hP' hz']
      by_cases hcc : c = c'
      · subst hcc; rcases hv with hv | hv <;> omega
      · have := hO.scDisj c hc c' hc' hcc; rcases hv with hv | hv <;> omega)
  obtain ⟨h128', -, -, -, -, -, e6', -⟩ := sc_facts hO hc'
  by_cases hcc : c' = c
  · subst hcc
    rcases ha with rfl | rfl
    · exact hv0 rfl
    · rw [e7, e6'] at e; omega
  · have := hO.scDisj c' hc' c hc hcc
    rw [e6'] at e; omega

/-- `reply_unlink`: the reply object forgets `t`, and `t` becomes inactive. -/
theorem ipc.reply_unlink.inv {X : Set U64} (s : S) (r : obj.Reply) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht0 : L.mem s (rTcbA r) = t)
    (hnr : ¬ Runnable (L.mem s (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t))) :
    ipc.reply_unlink st s r t ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s s' ∧ L.mem s' (rTcbA r) = 0#u64 ⦄ := by
  unfold ipc.reply_unlink
  step with obj.Reply.set_tcb.spec as ⟨s1, s1_post⟩
  subst s1_post
  have hrΩ := hsub _ (hO.tcbW hr)
  obtain ⟨h1, e1⟩ := wr_omega (v := 0#u64) h hrΩ
  rw [← e1 t ht] at hnr hx
  have ha : Aligned (rTcbA r) := (h.omega _ hrΩ).1
  exact WP.spec_mono (sts_inactive _ t Q R h1 ht hO.ksb hsub hnr hx) fun s' ⟨h', e', k'⟩ =>
    ⟨h', e', (keep_rtcb h hO hsub hr ht0 rfl).trans k', k'.zero hr (L.mem_wr_same ha)⟩

/-- The reply object of a thread blocked on reply, typed: a reply naming
`t`, whose `next` is an SC (head) or a reply and whose `prev` is a reply. -/
def ReplyT (st : machine.Store S) [L : LawfulStore st] (Rp Scs : Set U64) (s : S) (t : U64) : Prop :=
  L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t ∧
  (L.mem s (rNextA (L.mem s (replyA t))) &&& ~~~1#u64 ≠ 0#u64 →
    (headBit (L.mem s (rNextA (L.mem s (replyA t)))) = true →
      L.mem s (rNextA (L.mem s (replyA t))) &&& ~~~1#u64 ∈ Scs) ∧
    (headBit (L.mem s (rNextA (L.mem s (replyA t)))) = false →
      L.mem s (rNextA (L.mem s (replyA t))) &&& ~~~1#u64 ∈ Rp)) ∧
  (L.mem s (rPrevA (L.mem s (replyA t))) &&& ~~~1#u64 ≠ 0#u64 →
    L.mem s (rPrevA (L.mem s (replyA t))) &&& ~~~1#u64 ∈ Rp)

theorem ReplyT.transport {s s' : S} {t : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hR : ReplyT st Rp Scs s t)
    (hr : L.mem s' (replyA t) = L.mem s (replyA t)) (ho : ∀ a ∈ Sg, L.mem s' a = L.mem s a) :
    ReplyT st Rp Scs s' t := by
  obtain ⟨h0, h1, hn, hp⟩ := hR
  unfold ReplyT
  rw [hr, ho _ (hO.tcbW h0), ho _ (hO.prevW h0), ho _ (hO.nextW h0)]
  exact ⟨h0, h1, hn, hp⟩

/-- `rTcbA` of one reply is not the `prev`/`next` word of a reply, nor an SC
word at offset 32. -/
theorem rtcb_ne (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r : U64} (hr : r ∈ Rp) :
    (∀ r' ∈ Rp, (rTcbA r).val ≠ (rPrevA r').val ∧ (rTcbA r).val ≠ (rNextA r').val) ∧
    (∀ c ∈ Scs, (rTcbA r).val ≠ (scReplyA c).val) := by
  obtain ⟨m, e0, -, -⟩ := rp_facts hO hr
  refine ⟨fun r' hr' => ?_, fun c hc => ?_⟩
  · obtain ⟨m', -, e2, e3⟩ := rp_facts hO hr'
    rw [e0, e2, e3]; omega
  · obtain ⟨h128, -, -, -, -, -, e6, -⟩ := sc_facts hO hc
    have := hO.rpSc r hr c hc
    rw [e0, e6]; omega

/-- A reply whose `next` is an SC (head bit set) is that SC's reply-stack
head (l4v `sym_refs` for `sc_replies`). -/
def RHead (st : machine.Store S) [L : LawfulStore st] (Rp : Set U64) (s : S) : Prop :=
  ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
    L.mem s (scReplyA (L.mem s (rNextA r) &&& ~~~1#u64)) = r

/-- `RHead` when the replies' `NEXT` words and the SCs' `REPLY` words are kept. -/
theorem RHead.keep {s s' : S} (h : RHead st Rp s) (hn : ∀ r ∈ Rp, L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hnx : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → headBit (L.mem s (rNextA r)) = true →
      L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) : RHead st Rp s' := fun r hr hb h0 => by
  rw [hn r hr] at hb h0 ⊢
  rw [hsr _ (hnx r hr h0 hb)]; exact h r hr hb h0

/-- seL4 `reply_remove_tcb`. -/
theorem ipc.reply_remove_tcb.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hR : ReplyT st Rp Scs s t)
    (hhd : RHead st Rp s)
    (hnr : ¬ Runnable (L.mem s (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t))) :
    ipc.reply_remove_tcb st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s s' ∧
      L.mem s' (rTcbA (L.mem s (replyA t))) = 0#u64 ⦄ := by
  obtain ⟨hi, hit, hn, hp⟩ := hR
  set i := L.mem s (replyA t) with hi_def
  obtain ⟨rn, rs⟩ := rtcb_ne hO hi
  have aT : Aligned (rTcbA i) := by
    have hp' := hO.rp i hi; unfold Aligned; rw [rTcbA_val hp']; omega
  have keepT : ∀ {s1 : S} {a v : U64}, Aligned a → a.val ≠ (rTcbA i).val →
      L.mem (L.wr s1 a v) (rTcbA i) = L.mem s1 (rTcbA i) := fun ha hne => L.mem_wr_ne ha aT hne
  have alg : ∀ r ∈ Rp, Aligned (rPrevA r) ∧ Aligned (rNextA r) := fun r hr => by
    have hp' := hO.rp r hr
    exact ⟨by unfold Aligned; rw [rPrevA_val hp']; omega, by unfold Aligned; rw [rNextA_val hp']; omega⟩
  unfold ipc.reply_remove_tcb
  step with obj.Tcb.reply_obj.spec as ⟨i', i_post⟩
  step with obj.Reply.next.spec as ⟨next, next_post⟩
  step with obj.Reply.prev.spec as ⟨prev, prev_post⟩
  subst i_post next_post prev_post
  refine WP.spec_bind (Pₘ := fun s1 => SchedQueuesInvX st T Cs Ω H X s1 Q R ∧
      L.mem s1 (stA t) = L.mem s (stA t) ∧ KeepT0 st T Cs Rp Scs Nt t s s1 ∧ L.mem s1 (rTcbA i) = t ∧
      (∀ c ∈ Scs, L.mem s1 (scReplyA c) ≠ L.mem s (scReplyA c) → L.mem s (scReplyA c) = L.mem s (replyA t))) ?_ ?_
  · split
    · rename_i hne
      have hne' : L.mem s (rNextA i) &&& ~~~1#u64 ≠ 0#u64 := by simpa using hne
      obtain ⟨hn1, hn2⟩ := hn hne'
      step with obj.Reply.next_is_head.spec as ⟨b, b_post⟩
      split
      · rename_i hb
        have hc := hn1 (by rw [← b_post]; exact hb)
        refine WP.spec_mono (obj.Sc.set_reply.spec s _ 0#u64) fun s1 e => ?_
        subst e
        obtain ⟨h1, e1⟩ := wr_omega (v := 0#u64) h (scword_omega hO hc (Or.inl rfl))
        refine ⟨h1, e1 t ht, keep_scw h hO hc (Or.inl rfl) (fun _ => rfl) (fun _ => rfl), ?_, fun c hc' hne => ?_⟩
        · rw [keepT (h.omega _ (scword_omega hO hc (Or.inl rfl))).1 (Ne.symm (rs _ hc))]; exact hit
        · by_cases ec : c = L.mem s (rNextA i) &&& ~~~1#u64
          · subst ec; rw [← hi_def]; exact hhd i hi (by rw [← b_post]; exact hb) hne'
          · exfalso; apply hne
            have ha1 := (h.omega _ (scword_omega hO hc (Or.inl rfl))).1
            have ha2 := (h.omega _ (scword_omega hO hc' (Or.inl rfl))).1
            refine L.mem_wr_ne ha1 ha2 ?_
            obtain ⟨-, -, -, -, -, -, f6, -⟩ := sc_facts hO hc
            obtain ⟨-, -, -, -, -, -, f6', -⟩ := sc_facts hO hc'
            rw [f6, f6']
            have := hO.scDisj _ hc c hc' (Ne.symm ec); have := (sc_facts hO hc).1; have := (sc_facts hO hc').1
            omega
      · rename_i hb
        have hr' := hn2 (by rw [← b_post]; simpa using hb)
        refine WP.spec_mono (obj.Reply.set_prev.spec s _ 0#u64) fun s1 ⟨w, e, hw⟩ => ?_
        subst e
        obtain ⟨h1, e1⟩ := wr_omega (v := w) h (hsub _ (hO.prevW hr'))
        have kp := keep_rprev (t := t) h hO hsub hr' (hw rfl)
        refine ⟨h1, e1 t ht, kp.toKeepT0, ?_, kp.hch⟩
        rw [keepT (alg _ hr').1 (Ne.symm (rn _ hr').1)]; exact hit
    · exact (WP.spec_ok _).2 ⟨h, rfl, KeepT0.refl _ _, hit, fun c _ hne => absurd rfl hne⟩
  rintro s1 ⟨h1, e1, k1, t1, ch1⟩
  have hO1 : ObjsOK st Ω Sg Rp Scs Nt Z s1 := hO.ksb
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInvX st T Cs Ω H X s2 Q R ∧
      L.mem s2 (stA t) = L.mem s (stA t) ∧ KeepT st T Cs Rp Scs Nt t s1 s2 ∧ L.mem s2 (rTcbA i) = t) ?_ ?_
  · split
    · rename_i hne
      have hr' := hp (by simpa using hne)
      refine WP.spec_mono (obj.Reply.set_next.spec s1 _ 0#u64) fun s2 ⟨w, e, hw⟩ => ?_
      subst e
      obtain ⟨h2, e2⟩ := wr_omega (v := w) h1 (hsub _ (hO.nextW hr'))
      refine ⟨h2, (e2 t ht).trans e1, keep_rnext h1 hO1 hsub hr' (hw rfl), ?_⟩
      rw [keepT (alg _ hr').2 (Ne.symm (rn _ hr').2)]; exact t1
    · exact (WP.spec_ok _).2 ⟨h1, e1, KeepT.refl _ _, t1⟩
  rintro s2 ⟨h2, e2, k2, t2⟩
  have hO2 : ObjsOK st Ω Sg Rp Scs Nt Z s2 := hO.ksb
  refine WP.spec_bind (obj.Reply.set_prev.spec s2 _ 0#u64) ?_
  rintro s3 ⟨w3, rfl, hw3⟩
  obtain ⟨h3, e3⟩ := wr_omega (v := w3) h2 (hsub _ (hO.prevW hi))
  have k3 := keep_rprev (t := t) h2 hO2 hsub hi (hw3 rfl)
  have t3 : L.mem (L.wr s2 (rPrevA i) w3) (rTcbA i) = t := by
    rw [keepT (alg _ hi).1 (Ne.symm (rn _ hi).1)]; exact t2
  refine WP.spec_bind (obj.Reply.set_next.spec _ _ 0#u64) ?_
  rintro s4 ⟨w4, rfl, hw4⟩
  obtain ⟨h4, e4⟩ := wr_omega (v := w4) h3 (hsub _ (hO.nextW hi))
  have k4 := keep_rnext (t := t) h3 hO.ksb hsub hi (hw4 rfl)
  have t4 : L.mem (L.wr (L.wr s2 (rPrevA i) w3) (rNextA i) w4) (rTcbA i) = t := by
    rw [keepT (alg _ hi).2 (Ne.symm (rn _ hi).2)]; exact t3
  have est : L.mem (L.wr (L.wr s2 (rPrevA i) w3) (rNextA i) w4) (stA t) = L.mem s (stA t) :=
    (e4 t ht).trans ((e3 t ht).trans e2)
  rw [← est] at hnr hx
  refine WP.spec_mono (ipc.reply_unlink.inv _ _ t Q R h4 ht hO.ksb hsub hi t4 hnr hx) fun s' ⟨h', e', k', z'⟩ =>
    ⟨h', e', KeepT.of0 ht k1 (((k2.trans k3).trans k4).trans k') hi ch1 ?_, z'⟩
  rcases (k'.rlink i hi).2 with e | e
  · rw [e, L.mem_wr_same (alg _ hi).2]; exact hw4 rfl
  · exact e

/-- seL4 `cancelSignal`. -/
theorem notification.cancel_signal.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (htX : t ∉ X)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hb : Blocked (L.mem s (stA t))) :
    notification.cancel_signal st s t (L.mem s (blockA t)) ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  unfold notification.cancel_signal
  refine WP.spec_bind (notification.ntfn_dequeue.inv s t Q R h ht htX hb) ?_
  rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
  have e1 : L.mem s1 (stA t) = L.mem s (stA t) := by rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (by simp) (by simp)
  have kk : KeepT st T Cs Rp Scs Nt t s s1 :=
    KeepT.of_frame hO hsub k1 c1 (fun y hy K a b c d _ => f1 y hy K a b c d) o1 n1
      (fun c hc o ho => nc1 c hc o (by omega) (by omega))
  refine WP.spec_mono (sts_inactive s1 t Q R h1 ht hO.ksb hsub (by rw [e1]; exact not_runnable_of_blocked hb)
    (Or.inl (Or.inr rfl))) fun s2 ⟨h2, e2, k2⟩ => ⟨h2.congrX fun y => ?_, e2, kk.trans k2⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy | rfl, hne⟩
    · exact hy
    · exact absurd rfl hne
  · intro hy; exact ⟨Or.inl hy, fun e => htX (e ▸ hy)⟩

theorem empty_congr {t : U64} : ∀ y, y ∈ {y : U64 | y ∈ (∅ : Set U64) ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := by
  intro y; simp

/-- After the endpoint dequeue: the exception set is at most `{t}`, and `t`
is not runnable. -/
def ExcT (X : Set U64) (t : U64) : Prop := ∀ y ∈ X, y = t

theorem ep_tail {X : Set U64} (s3 : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h3 : SchedQueuesInvX st T Cs Ω H X s3 Q R) (ht : t ∈ T) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s3)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hX : ExcT X t)
    (hnr : ¬ Runnable (L.mem s3 (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s3 (stA t))) :
    sched.set_thread_state st s3 t sched.TS_INACTIVE ⦃ s' =>
      SchedQueuesInv st T Cs Ω H s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s3 s' ⦄ :=
  WP.spec_mono (sts_inactive s3 t Q R h3 ht hO hsub hnr hx) fun s' ⟨h', e', k'⟩ => ⟨h'.congrX fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact hX y, e', k'⟩

/-- The endpoint branch of `cancel_ipc` (blocked on send or receive). -/
theorem ep_branch {A : Type _} (a : A) (s1 : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h1 : SchedQueuesInv st T Cs Ω H s1 Q R) (ht : t ∈ T) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s1)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hb : Blocked (L.mem s1 (stA t))) (rcv : Prop)
    [Decidable rcv] (hrecv : rcv → L.mem s1 (replyA t) ≠ 0#u64 →
      L.mem s1 (replyA t) ∈ Rp ∧ L.mem s1 (rTcbA (L.mem s1 (replyA t))) = t) :
    (do
      let ep ← obj.Tcb.block_obj st t s1
      let s2 ← endpoint.ep_dequeue st s1 ep t
      let s3 ← if rcv then do
          let i ← obj.Tcb.reply_obj st t s2
          if (i != 0#u64) = true then ipc.reply_unlink st s2 i t else ok s2
        else ok s2
      let s4 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ =>
      SchedQueuesInv st T Cs Ω H s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s1 s' ∧
      (rcv → L.mem s1 (replyA t) ≠ 0#u64 → L.mem s' (rTcbA (L.mem s1 (replyA t))) = 0#u64) ⦄ := by
  step with obj.Tcb.block_obj.spec as ⟨ep, ep_post⟩
  subst ep_post
  refine WP.spec_bind (endpoint.ep_dequeue.inv s1 t Q R h1 ht (by simp) hb) ?_
  rintro s2 ⟨h2, f2, o2, n2, kb2, c2, nc2⟩
  have e2 : L.mem s2 (stA t) = L.mem s1 (stA t) := by
    rw [stA_eq]; exact f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have r2 : L.mem s2 (replyA t) = L.mem s1 (replyA t) := f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have hX2 : ExcT {y | y ∈ (∅ : Set U64) ∨ y = t} t := fun y hy => by simpa using hy
  have hnr2 : ¬ Runnable (L.mem s2 (stA t)) := by rw [e2]; exact not_runnable_of_blocked hb
  have k2 : KeepT st T Cs Rp Scs Nt t s1 s2 :=
    KeepT.of_frame hO hsub kb2 c2 (fun y hy K a b c d _ => f2 y hy K a b c d) o2 n2
      (fun c hc o ho => nc2 c hc o (by omega) (by omega))
  have hO2 : ObjsOK st Ω Sg Rp Scs Nt Z s2 := hO.ksb
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ ExcT X3 t ∧
      ¬ Runnable (L.mem s3 (stA t)) ∧ (t ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA t))) ∧ KeepT st T Cs Rp Scs Nt t s1 s3 ∧
      (rcv → L.mem s1 (replyA t) ≠ 0#u64 → L.mem s3 (rTcbA (L.mem s1 (replyA t))) = 0#u64)) ?_ ?_
  · split
    · rename_i hrc
      step with obj.Tcb.reply_obj.spec as ⟨i, i_post⟩
      split
      · rename_i hi
        have hi' : L.mem s1 (replyA t) ≠ 0#u64 := by rw [← r2, ← i_post]; simpa using hi
        obtain ⟨hr, hrt⟩ := hrecv hrc hi'
        rw [← r2] at hr hrt
        rw [← i_post] at hr hrt
        have hrt2 : L.mem s2 (rTcbA i) = t := by rw [o2 _ (hsub _ (hO.tcbW hr))]; exact hrt
        refine WP.spec_mono (ipc.reply_unlink.inv s2 i t Q R h2 ht hO2 hsub hr hrt2 hnr2 (Or.inl (Or.inr rfl)))
          fun s3 ⟨h3, e3, k3, z3⟩ => ⟨_, h3, fun y hy => ?_, by rw [e3]; exact not_runnable_inactive,
            Or.inr (by rw [e3]; exact not_blocked_inactive), k2.trans k3,
            fun _ _ => by rw [← r2, ← i_post]; exact z3⟩
        obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · rename_i hi
        refine (WP.spec_ok _).2 ⟨_, h2, hX2, hnr2, Or.inl (Or.inr rfl), k2, fun _ hn => ?_⟩
        have hi0 : i = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi; exact hi
        exact absurd (by rw [← r2, ← i_post]; exact hi0) hn
    · exact (WP.spec_ok _).2 ⟨_, h2, hX2, hnr2, Or.inl (Or.inr rfl), k2, fun hr' => absurd hr' ‹_›⟩
  rintro s3 ⟨X3, h3, hX3, hnr3, hx3, k3, z3⟩
  refine WP.spec_bind (ep_tail s3 t Q R h3 ht hO.ksb hsub hX3 hnr3 hx3) fun s4 ⟨h4, e4, k4⟩ => ?_
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨h4, e4, k3.trans k4, fun hrc hn => k4.zero (hrecv hrc hn).1 (z3 hrc hn)⟩

/-- seL4 `cancelIPC` (MCS) keeps the invariant.  Afterwards the thread is
neither blocked nor blocked on reply: it is inactive, or (when it was in
neither state) its state and the scheduler action are as before.  `KeepT`
records what else is kept. -/
theorem ipc.cancel_ipc.inv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t)
    (hhd : RHead st Rp s) (hnx : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
      headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧ ¬ Blocked (L.mem s' (stA t)) ∧
      L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧
      (L.mem s' (stA t) = sched.TS_INACTIVE ∨
        (L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' = L.actionW s)) ∧ KeepT st T Cs Rp Scs Nt t s s' ∧
      ((L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY ∨
          (L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV ∧ L.mem s (replyA t) ≠ 0#u64)) →
        L.mem s' (rTcbA (L.mem s (replyA t))) = 0#u64) ⦄ := by
  unfold ipc.cancel_ipc
  refine WP.spec_bind (faults.clear_fault.inv s t Q R h ht hO hsub) ?_
  rintro s1 ⟨h1, f1, o1, a1, k1⟩
  have e1 : L.mem s1 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have r1 : L.mem s1 (replyA t) = L.mem s (replyA t) := f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have g1 : ∀ b ∈ Sg, L.mem s1 b = L.mem s b := fun b hb => o1 b (hsub b hb)
  have hO1 : ObjsOK st Ω Sg Rp Scs Nt Z s1 := hO.ksb
  obtain ⟨-, -, hr3, hs4, hn6⟩ := ts_vals
  have inR : sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_REPLY := by rw [ts_inactive, ts_reply]; decide
  have done : ∀ s', SchedQueuesInv st T Cs Ω H s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st T Cs Rp Scs Nt t s1 s' →
      ((L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY ∨
          (L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV ∧ L.mem s (replyA t) ≠ 0#u64)) →
        L.mem s' (rTcbA (L.mem s (replyA t))) = 0#u64) →
      SchedQueuesInv st T Cs Ω H s' Q R ∧ ¬ Blocked (L.mem s' (stA t)) ∧
      L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧
      (L.mem s' (stA t) = sched.TS_INACTIVE ∨
        (L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' = L.actionW s)) ∧ KeepT st T Cs Rp Scs Nt t s s' ∧
      ((L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY ∨
          (L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV ∧ L.mem s (replyA t) ≠ 0#u64)) →
        L.mem s' (rTcbA (L.mem s (replyA t))) = 0#u64) :=
    fun s' ⟨h', e', k'⟩ hz => ⟨h', by rw [e']; exact not_blocked_inactive, by rw [e']; exact inR, Or.inl e',
      k1.trans k', hz⟩
  step with obj.Tcb.state.spec as ⟨stt, stt_post⟩
  split
  · rename_i hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inl rfl
    have hss : L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND := by rw [← e1, ← stt_post, hs]
    refine WP.spec_mono (ep_branch a s1 t Q R h1 ht hO1 hsub hb (stt = sched.TS_BLOCKED_ON_RECV) ?_) ?_
    · intro hrc; rw [hs] at hrc; rw [hs4, hr3] at hrc; simp at hrc
    · rintro ⟨s4, a4⟩ ⟨h4, e4, k4, -⟩
      refine done s4 ⟨h4, e4, k4⟩ fun hh => ?_
      rw [hss] at hh
      rcases hh with hh | ⟨hh, -⟩
      · rw [hs4, ts_reply] at hh; exact absurd hh (by decide)
      · rw [hs4, hr3] at hh; exact absurd hh (by decide)
  split
  · rename_i _ hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inr (Or.inl rfl)
    have hE := ep_branch a s1 t Q R h1 ht hO1 hsub hb True
      (fun _ hi => by
        rw [r1] at hi ⊢
        obtain ⟨hr, hrt⟩ := hrecv (by rw [← e1, ← stt_post, hs]) hi
        exact ⟨hr, by rw [g1 _ (hO.tcbW hr)]; exact hrt⟩)
    simp only [↓reduceIte] at hE
    have hsr : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV := by rw [← e1, ← stt_post, hs]
    refine WP.spec_mono hE fun r h4 => ?_
    obtain ⟨s4, a4⟩ := r
    obtain ⟨h4, e4, k4, z4⟩ := h4
    refine done s4 ⟨h4, e4, k4⟩ fun hh => ?_
    rw [hsr] at hh
    rcases hh with hh | ⟨-, hn⟩
    · rw [hr3, ts_reply] at hh; exact absurd hh (by decide)
    · rw [← r1]; exact z4 trivial (by rw [r1]; exact hn)
  split
  · rename_i _ _ hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inr (Or.inr rfl)
    step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
    subst i_post
    have hsn : L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN := by rw [← e1, ← stt_post, hs]
    refine WP.spec_bind (notification.cancel_signal.inv s1 t Q R h1 ht (by simp) hO1 hsub hb) ?_
    intro s2 h2
    refine (WP.spec_ok _).2 (done s2 h2 fun hh => ?_)
    rw [hsn] at hh
    rcases hh with hh | ⟨hh, -⟩
    · rw [hn6, ts_reply] at hh; exact absurd hh (by decide)
    · rw [hn6, hr3] at hh; exact absurd hh (by decide)
  split
  · rename_i _ _ _ hs
    have hR : ReplyT st Rp Scs s1 t := (hreply (by rw [← e1, ← stt_post, hs])).transport hO r1 g1
    have hst : L.mem s1 (stA t) = sched.TS_BLOCKED_ON_REPLY := by rw [← stt_post, hs]
    have hhd1 : RHead st Rp s1 := hhd.keep (fun r hr => g1 _ (hO.nextW hr)) (fun c hc => g1 _ (hO.repW c hc)) hnx
    refine WP.spec_bind (ipc.reply_remove_tcb.inv s1 t Q R h1 ht hO1 hsub hR hhd1 (by rw [hst]; exact not_runnable_reply)
      (Or.inr (by rw [hst]; exact not_blocked_reply))) ?_
    rintro s2 ⟨h2, e2, k2, z2⟩
    exact (WP.spec_ok _).2 (done s2 ⟨h2.congrX empty_congr, e2, k2⟩ fun _ => by rw [← r1]; exact z2)
  · rename_i h1' h2' h3' h4'
    simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨h1, ?_, by rw [← stt_post]; exact h4', Or.inr ⟨e1, a1⟩, k1, fun hh => ?_⟩
    swap
    · rw [← e1, ← stt_post] at hh
      rcases hh with hh | ⟨hh, -⟩
      · exact absurd hh h4'
      · exact absurd hh h2'
    rw [← stt_post]
    rintro (e | e | e)
    · exact h1' e
    · exact h2' e
    · exact h3' e

/-! ## `suspend` -/

@[step] theorem obj.Tcb.yield_to.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.yield_to st t s ⦃ v => v = L.mem s (yieldA t) ⦄ := by
  unfold obj.Tcb.yield_to; step*; simp_all [yieldA]
@[step] theorem obj.Tcb.set_yield_to.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_yield_to st t s v ⦃ s' => s' = L.wr s (yieldA t) v ⦄ := by
  unfold obj.Tcb.set_yield_to; step*; simp_all [yieldA]
@[step] theorem obj.Sc.set_yield_from.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_yield_from st sc s v ⦃ s' => s' = L.wr s (scYieldFromA sc) v ⦄ := by
  unfold obj.Sc.set_yield_from; step*; simp_all [scYieldFromA]
@[step] theorem obj.Tcb.reg.spec (s : S) (t : obj.Tcb) (r : U64) : obj.Tcb.reg st t s r ⦃ _ => True ⦄ := by
  unfold obj.Tcb.reg; step*
theorem obj.Tcb.set_reg.fault_ip (s : S) (t : obj.Tcb) (v : U64) (ht : TcbAddr t) :
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 392#u64) v ⦄ := by
  unfold obj.Tcb.set_reg
  step*
  subst_vars
  congr 1
  have := ht.fits
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
    layout.tcb.REGS, layout.reg.FAULT_IP]
  try omega

/-- A write to a field of `t` the invariant does not read. -/
theorem field_wr_keep {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t K v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3592 ∧ K.val ≠ 3520 ∧
      K.val ≠ 3448 ∧ K.val ≠ 3328 ∧ K.val ≠ 3336) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (core.num.U64.wrapping_add t K) v) Q R ∧
      (∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ K.val →
        L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add t K') =
          L.mem s (core.num.U64.wrapping_add t K')) ∧
      L.actionW (L.wr s (core.num.U64.wrapping_add t K) v) = L.actionW s := by
  have hta := h.tcbs t ht
  have ha := field_aligned hta hK hK8
  refine ⟨inv_wr_field h ht hK hK8 hKn, fun K' h1 h2 hne => ?_, ?_⟩
  · exact L.mem_wr_ne ha (field_aligned hta h1 h2)
      (fun e => field_ne hta hta hK h1 (fun _ => Ne.symm hne) (UScalar.eq_of_val_eq e))
  · unfold LawfulStore.actionW
    rw [L.cpu_wr]
    exact nodeword_wr_field (h.nodes _ h.cur) ht hta hK hK8 (by rw [act_val]; omega) (by rw [act_val])

/-- A queue footprint keeps the action word and `t`'s fields other than the
links and `IN_QUEUES`. -/
theorem qfoot_act {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {W : List U64}
    {c t : U64} {P : Nat → Prop} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hW : ∀ w ∈ W, w ∈ T) (hc : c ∈ Cs)
    (ht : t ∈ T) (hP : ¬ P 16) (hw : WritesIn st s s' (L.QFoot s W c P t)) :
    L.actionW s' = L.actionW s := by
  unfold LawfulStore.actionW
  rw [hw.2.1]
  exact node_qfoot h.tcbs hW (h.nodes c hc) (h.nodes _ h.cur) ht hw (h.nodes _ h.cur) (by rw [act_val]; omega)
    (by rw [act_val]) (fun _ => by rw [act_val]; exact hP) (fun _ => by rw [act_val]; omega)

/-- seL4 `suspend` (MCS) keeps the invariant, for a thread that is not the
switch-to candidate (seL4 `scheduler_act_not t`): `set_thread_state` only
reschedules for the current thread, so suspending the candidate would leave
`schedule` switching to an inactive thread. -/
theorem sched.suspend.inv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t)
    (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → scYieldFromA (L.mem s (yieldA t)) ∈ Ω)
    (hhd : RHead st Rp s) (hnx : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
      headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) :
    sched.suspend st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  unfold sched.suspend
  refine WP.spec_bind (ipc.cancel_ipc.inv s a t Q R h ht hO hsub hrecv hreply hhd hnx) ?_
  rintro ⟨s1, a1⟩ ⟨h1, nb1, -, hst1, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  -- the fault-IP copy
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ ¬ Blocked (L.mem s2 (stA t)) ∧
      L.actionW s2 ≠ t ∧ L.mem s2 (yieldA t) = L.mem s (yieldA t)) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, a2⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      refine ⟨h2, ?_, by rw [a2]; exact na1, by rw [← y1]; exact f2 _ (by simp) (by simp) (by simp)⟩
      rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nb1
    · exact (WP.spec_ok _).2 ⟨h1, nb1, na1, y1⟩
  rintro s2 ⟨h2, nb2, na2, y2⟩
  -- out of the ready queue
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, -⟩
  have a3 := qfoot_act h2 hW2 hc2 ht (by omega) hw3
  have f3 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s3 (core.num.U64.wrapping_add t K) = L.mem s2 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht a b c (fun _ => d)
  set Q3 := (if (L.mem s2 (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem s2 (affA t)) (Function.update (Q (L.mem s2 (affA t))) (L.mem s2 (prioA t))
         ((Q (L.mem s2 (affA t)) (L.mem s2 (prioA t))).erase t)) else Q) with hQ3
  have nQ3 : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q3 c p := by
    intro c hc p hp hm
    rw [hQ3] at hm
    split_ifs at hm with hf
    · rcases mem_upd2.1 hm with ⟨-, -, hm⟩ | ⟨hne, hm⟩
      · exact ((h2.ready _ hc2).1.rel _ hp2).nodup.not_mem_erase hm
      · obtain ⟨e1, e2⟩ := h2.inQ c hc p hp t hm
        exact hne ⟨e1.symm, e2.symm⟩
    · exact h2.notQ ht (not_not.1 hf) hc hp hm
  -- out of the release queue
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t Q3 R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨h4, hw4, -⟩
  have a4 := qfoot_act h3 hW3 hc3 ht (by unfold RelOffs; omega) hw4
  have f4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add t K) = L.mem s3 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht a b c (fun _ => d)
  set R4 := (if (L.mem s3 (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
       then Function.update R (L.mem s3 (affA t)) ((R (L.mem s3 (affA t))).erase t) else R) with hR4
  have nR4 : ∀ c ∈ Cs, t ∉ R4 c := by
    intro c hc hm
    rw [hR4] at hm
    split_ifs at hm with hf
    · by_cases e : c = L.mem s3 (affA t)
      · subst e; rw [Function.update_self] at hm
        exact (h3.release _ hc3).nodup.not_mem_erase hm
      · rw [Function.update_of_ne e] at hm
        exact e (h3.inR c hc t hm).symm
    · exact h3.notR ht (not_not.1 hf) hc hm
  have st4 : L.mem s4 (stA t) = L.mem s2 (stA t) := by
    rw [stA_eq, f4 _ (by simp) (by simp) (by simp) (by simp), f3 _ (by simp) (by simp) (by simp) (by simp)]
  have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) := by
    rw [← y2]; exact (f4 _ (by simp) (by simp) (by simp) (by simp)).trans (f3 _ (by simp) (by simp) (by simp) (by simp))
  have na4 : L.actionW s4 ≠ t := by rw [a4, a3]; exact na2
  -- `cancel_yield_to`
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  have hb0 : b = false := by
    rw [b_post]; simp only [decide_eq_false_iff_not]; intro e; exact hta.ne0 (by rw [e]; rfl)
  subst hb0
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  refine WP.spec_bind (Pₘ := fun s5 => SchedQueuesInv st T Cs Ω H s5 Q3 R4 ∧ L.mem s5 (stA t) = L.mem s4 (stA t) ∧
      L.actionW s5 = L.actionW s4) ?_ ?_
  · split
    · rename_i hy
      have hyΩ : scYieldFromA yt ∈ Ω := by rw [yt_post, y4]; exact hyield (by rw [← y4, ← yt_post]; simpa using hy)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      obtain ⟨h5, e5⟩ := wr_omega (v := 0#u64) h4 hyΩ
      have a5 : L.actionW (L.wr s4 (scYieldFromA yt) 0#u64) = L.actionW s4 := by
        unfold LawfulStore.actionW
        simp only [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne (h4.omega _ hyΩ).1 (nodeAt_aligned (h4.nodes _ h4.cur) (by rw [act_val]; omega)
          (by rw [act_val])) (fun e => out_ne_node (h4.omega _ hyΩ) h4.cur (h4.nodes _ h4.cur)
            (by rw [act_val]; omega) e.symm)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, f6, a6⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      refine ⟨h6, ?_, a6.trans a5⟩
      rw [stA_eq, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl,
        f6 _ (by simp) (by simp) (by simp), ← stA_eq, e5 t ht]
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl⟩
  rintro s5 ⟨h5, st5, a5⟩
  have hnr5 : ¬ Blocked (L.mem s5 (stA t)) := by rw [st5, st4]; exact nb2
  refine WP.spec_bind (sched.set_thread_state.inv s5 t _ Q3 R4 h5 ht not_blocked_inactive (Or.inr hnr5)
    ⟨fun c hc p hp hm => absurd hm (nQ3 c hc p hp), fun c hc hm => absurd hm (nR4 c hc),
     fun e => absurd e (by rw [a5]; exact na4)⟩) ?_
  intro s6 h6
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨Q3, R4, h6.congrX empty_congr⟩

end

end Fl4Proofs.P1

