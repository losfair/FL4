/-
# The accepted fault fast path (FL4 #56, m58)

Groundwork for `FastSame` of `fastpath.fault` (KENTRY-PLAN m57 (2), F1–F6):

* the write algebra under `StoreExt` (`wr_comm`, `wr_wr`, `wr_mem`): with
  the store its aligned memory, aligned writes to distinct words commute, a
  second write to a word replaces the first, and writing a word's own value
  is no write;
* F6 by structure: `remote_queue_update` of a thread on the current core is
  no write (`remote_queue_update_local`); with one domain the bitmap and
  ready-queue offsets ignore the domain (`bitmap_dom_one`, `rq_index_one`),
  so `choose_thread`'s domain 0 and `is_highest_prio`'s `cur_domain` read
  the same words (`is_highest_prio_dom`, `highest_prio_dom`);
* the inversion of an accepted run (`fault_acc`): every check of the fast
  path held at the entry state, and the run is the write sequence
  `faultTail` from there;
* F2: the general `ep_dequeue` of the head is the fast path's dequeue
  (`ep_dequeue_head`, from the queue's `QueueRel`);
* the meeting state (`handle_fault_pre`, `fault_sync`): the general
  `handle_fault` makes the fast path's writes up to the handler `Running`,
  plus the action word `CHOOSE_NEW`; from there the fast path runs
  `faultTail3` and the general path `unblock_sporadic`, `possible_switch_to`
  (`possible_switch_to_cn`: an `enqueue`) and `finish` (KENTRY-PLAN m58,
  handoff (a)–(e)).
-/
import Fl4Proofs.P1.FastDecline
import Fl4Proofs.P1.QueueSwitch
import Fl4Proofs.P1.QueueCallers
import Fl4Proofs.P1.QueueRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## Writes under `StoreExt` -/

theorem wr_comm (hX : StoreExt st) (s : S) {a b : U64} (v w : U64) (ha : Aligned a) (hb : Aligned b)
    (hab : a ≠ b) : L.wr (L.wr s a v) b w = L.wr (L.wr s b w) a v := by
  apply hX
  · intro x hx
    rw [L.mem_wr _ _ _ _ hb hx, L.mem_wr _ _ _ _ ha hx, L.mem_wr _ _ _ _ ha hx, L.mem_wr _ _ _ _ hb hx]
    by_cases h1 : a = x
    · subst h1; simp [Ne.symm hab]
    · simp [h1]
  · simp
  · simp

theorem wr_wr (hX : StoreExt st) (s : S) {a : U64} (v w : U64) (ha : Aligned a) :
    L.wr (L.wr s a v) a w = L.wr s a w := by
  apply hX
  · intro x hx
    rw [L.mem_wr _ _ _ _ ha hx, L.mem_wr _ _ _ _ ha hx, L.mem_wr _ _ _ _ ha hx]
    by_cases h1 : a = x <;> simp [h1]
  · simp
  · simp

theorem wr_mem (hX : StoreExt st) (s : S) {a : U64} (ha : Aligned a) : L.wr s a (L.mem s a) = s := by
  apply hX
  · intro x hx
    rw [L.mem_wr _ _ _ _ ha hx]
    by_cases h1 : a = x
    · subst h1; simp
    · simp [h1]
  · simp
  · simp

/-- `wr_mem` for a word known to hold `v`. -/
theorem wr_eq_self (hX : StoreExt st) (s : S) {a v : U64} (ha : Aligned a) (hv : L.mem s a = v) :
    L.wr s a v = s := by
  rw [← hv]; exact wr_mem hX s ha

/-! ## F6: structure -/

/-- `remote_queue_update` of a thread on the current core is no write. -/
theorem remote_queue_update_local (s : S) (t : obj.Tcb) (h : L.mem s (affA t) = L.cpu s) :
    smp.remote_queue_update st s t = ok s := by
  unfold smp.remote_queue_update
  obtain ⟨v, hv, rfl⟩ := spec_ex_fd (obj.Tcb.affinity.spec (L := L) s t)
  rw [hv, L.cur_cpu_eq]; simp [h]

theorem num_domains_one : ¬ (layout.NUM_DOMAINS > 1#u64) := by
  simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]

/-- With one domain the bitmap is domain 0's. -/
theorem bitmap_dom_one (d : U64) : sched.bitmap_dom d = ok 0#u64 := by
  unfold sched.bitmap_dom; simp

/-- With one domain the ready queue of a priority is the same in every domain. -/
theorem rq_index_one (d p : U64) : sched.rq_index d p = ok p := by
  unfold sched.rq_index; simp

theorem rq_head_off_dom (d d' p : U64) : sched.rq_head_off d p = sched.rq_head_off d' p := by
  unfold sched.rq_head_off; simp only [rq_index_one]

/-- `is_highest_prio` ignores its domain. -/
theorem is_highest_prio_dom (s : S) (d d' p : U64) :
    sched.is_highest_prio st s d p = sched.is_highest_prio st s d' p := by
  unfold sched.is_highest_prio sched.highest_prio; simp only [bitmap_dom_one]

/-- `highest_prio` ignores its domain. -/
theorem highest_prio_dom (s : S) (d d' : U64) :
    sched.highest_prio st s d = sched.highest_prio st s d' := by
  unfold sched.highest_prio; simp only [bitmap_dom_one]

end

/-! ## The endpoint dequeue, both ways (F2) -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `set_fault`'s four writes for an UnknownSyscall fault. -/
def sfW (s : S) (t n : U64) : S :=
  L.wr (L.wr (L.wr (L.wr s (faultA t) fl4_abi.consts.fault.UnknownSyscall)
    (core.num.U64.wrapping_add t 3384#u64) n) (core.num.U64.wrapping_add t 3392#u64) 0#u64)
    (core.num.U64.wrapping_add t 3400#u64) 0#u64

theorem set_fault_us (s : S) (t : obj.Tcb) (n : U64) :
    faults.set_fault st s t (error.Fault.UnknownSyscall n) = ok (sfW (L := L) s t n) := by
  apply eq_of_spec_fd
  unfold faults.set_fault
  simp only [bind_ok, uncurry_apply_pair]
  refine WP.spec_bind (obj.Tcb.set_fault_type.spec (L := L) s t _) fun s2 e2 => ?_
  refine WP.spec_bind (obj.Tcb.set_fault_w0.wr (L := L) _ t _) fun s3 e3 => ?_
  refine WP.spec_bind (obj.Tcb.set_fault_w1.wr (L := L) _ t _) fun s4 e4 => ?_
  exact WP.spec_mono (obj.Tcb.set_fault_w2.wr (L := L) _ t _) fun s5 e5 => by
    subst e2 e3 e4 e5; rfl

/-- `set_queue`'s two writes. -/
def epW (s : S) (ep h tl state : U64) : S :=
  L.wr (L.wr s (epHeadA ep) h) (epTSA ep) ((tl &&& ~~~3#u64) ||| (state &&& 3#u64))

/-- The fast path's dequeue of the head `dest` (fastpath.rs, `send_ipc, a
receiver waiting`). -/
def epFast (s : S) (ep dest : U64) : S :=
  let tl := (L.epQ s ep).end
  let af := L.mem s (nextA .Ep dest)
  let s3 := if tl = dest then epW (L := L) s ep 0#u64 0#u64 obj.EP_IDLE
    else epW (L := L) (L.wr s (prevA .Ep af) 0#u64) ep af tl obj.EP_RECV
  L.wr (L.wr s3 (nextA .Ep dest) 0#u64) (prevA .Ep dest) 0#u64

theorem obj.Ep.tail.ok (s : S) (ep : obj.Ep) : obj.Ep.tail st ep s = ok (L.epQ s ep).end := by
  have h := endpoint.get_queue.spec (L := L) s ep
  unfold endpoint.get_queue at h
  obtain ⟨hd, -, h⟩ := spec_bind_inv h
  obtain ⟨tl, etl, h⟩ := spec_bind_inv h
  rw [WP.spec_ok] at h
  rw [etl, ← h]

theorem obj.Ep.set_queue.ok (s : S) (ep : obj.Ep) (h tl state : U64) :
    obj.Ep.set_queue st ep s h tl state = ok (epW (L := L) s ep h tl state) :=
  eq_of_spec_fd (endpoint.set_queue.spec (L := L) s ep ⟨h, tl⟩ state)

theorem obj.Tcb.set_ep_next.ok (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_ep_next st t s v = ok (L.wr s (nextA .Ep t) v) := by
  have h := tcbqueue.set_next.spec (L := L) s .Ep t v
  unfold tcbqueue.set_next at h; exact eq_of_spec_fd h

theorem obj.Tcb.set_ep_prev.ok (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_ep_prev st t s v = ok (L.wr s (prevA .Ep t) v) := by
  have h := tcbqueue.set_prev.spec (L := L) s .Ep t v
  unfold tcbqueue.set_prev at h; exact eq_of_spec_fd h

theorem obj.Tcb.ep_next.ok (s : S) (t : obj.Tcb) :
    obj.Tcb.ep_next st t s = ok (L.mem s (nextA .Ep t)) := by
  have h := tcbqueue.next.spec (L := L) s .Ep t
  unfold tcbqueue.next at h; exact eq_of_spec_fd h

theorem tcbqueue.remove.ok (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb) :
    tcbqueue.remove st s l q t = ok (removeF st s l q t) := by
  obtain ⟨v, hv, hp⟩ := spec_ex_fd (tcbqueue.remove.eq (L := L) s l q t)
  rw [hv]; congr 1

/-- The endpoint words are no link word of a TCB of `T`. -/
theorem ep_ne_links {T : Set U64} {ep y : U64} (hE : EpPlaced T ep) (hy : y ∈ T) (hya : TcbAddr y)
    (l : tcbqueue.Link) :
    epHeadA ep ≠ nextA l y ∧ epHeadA ep ≠ prevA l y ∧ epTSA ep ≠ nextA l y ∧ epTSA ep ≠ prevA l y :=
  ⟨(ep_ne_link hE (Or.inl rfl) hy hya l).1, (ep_ne_link hE (Or.inl rfl) hy hya l).2,
    (ep_ne_link hE (Or.inr rfl) hy hya l).1, (ep_ne_link hE (Or.inr rfl) hy hya l).2⟩

/-- Two writes to the endpoint pass two writes to `dest`'s links. -/
theorem epW_comm (hX : StoreExt st) {T : Set U64} {ep d : U64} (hE : EpPlaced T ep) (hd : d ∈ T)
    (hda : TcbAddr d) (s : S) (h tl state v w : U64) :
    L.wr (L.wr (epW (L := L) s ep h tl state) (nextA .Ep d) v) (prevA .Ep d) w =
      epW (L := L) (L.wr (L.wr s (nextA .Ep d) v) (prevA .Ep d) w) ep h tl state := by
  obtain ⟨ah, at'⟩ := ep_aligned hE
  obtain ⟨n1, p1, n2, p2⟩ := ep_ne_links hE hd hda .Ep
  have an := nextA_aligned hda .Ep
  have ap := prevA_aligned hda .Ep
  unfold epW
  rw [wr_comm hX _ _ _ at' an n2, wr_comm hX _ _ _ ah an n1, wr_comm hX _ _ _ at' ap p2,
    wr_comm hX _ _ _ ah ap p1]

/-- **The general path's `ep_dequeue` of the head is the fast path's** (F2:
the endpoint's queue is related, `QueueRel`, so `tail = head` exactly when
the head is alone and otherwise its successor is a TCB). -/
theorem ep_dequeue_head (hX : StoreExt st) {T : Set U64} (hT : TcbPlaced T) {s : S} {ep dest : U64}
    {rest : List U64} (hE : EpPlaced T ep) (hq : QueueRel (L.mem s) T .Ep (L.epQ s ep) (dest :: rest))
    (hst : L.epState s ep = obj.EP_RECV) :
    endpoint.ep_dequeue st s ep dest = ok (epFast (L := L) s ep dest) := by
  have hdT : dest ∈ T := hq.mem dest (by simp)
  have hda : TcbAddr dest := hT dest hdT
  have hh : (L.epQ s ep).head = dest := by simpa using hq.head
  obtain ⟨-, hn, -⟩ := (Seg_cons _ _ _ _ _ _).1 hq.seg
  -- removeF at the head, both cases
  have key : ∀ (q1 : tcbqueue.Queue) (s1 : S), removeF st s .Ep (L.epQ s ep) dest = (q1, s1) →
      (do
        let b ← tcbqueue.Queue.is_empty q1
        if b = true then endpoint.set_queue st s1 ep q1 obj.EP_IDLE
        else endpoint.set_queue st s1 ep q1 (L.epState s ep)) = ok (epFast (L := L) s ep dest) := by
    intro q1 s1 hp
    cases rest with
    | nil =>
      have he : (L.epQ s ep).end = dest := by simpa using hq.last
      have hrm : removeF st s .Ep (L.epQ s ep) dest =
          (⟨0#u64, 0#u64⟩, L.wr (L.wr s (nextA .Ep dest) 0#u64) (prevA .Ep dest) 0#u64) := by
        simp [removeF, hh, he]
      rw [hrm] at hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp.symm
      rw [eq_of_spec_fd (tcbqueue.Queue.is_empty.spec _)]
      simp only [bind_ok, decide_true, ↓reduceIte]
      rw [eq_of_spec_fd (endpoint.set_queue.spec (L := L) _ ep _ _)]
      unfold epFast
      simp only [he, ↓reduceIte]
      rw [epW_comm hX hE hdT hda]
      rfl
    | cons y ys =>
      have hy0 : y ≠ 0#u64 := hq.ne0 hT y (by simp)
      have hlast : (L.epQ s ep).end = (y :: ys).getLastD 0#u64 := by simpa using hq.last
      have hne : (L.epQ s ep).end ≠ dest := by
        rw [hlast]; intro e
        have hm : (y :: ys).getLastD 0#u64 ∈ y :: ys := getLastD_mem (List.cons_ne_nil y ys) 0#u64
        rw [e] at hm
        exact (List.nodup_cons.1 hq.nodup).1 hm
      have hnext : L.mem s (nextA .Ep dest) = y := by simpa using hn
      have hrm : removeF st s .Ep (L.epQ s ep) dest =
          (⟨y, (L.epQ s ep).end⟩, L.wr (L.wr (L.wr s (prevA .Ep y) 0#u64) (nextA .Ep dest) 0#u64)
            (prevA .Ep dest) 0#u64) := by
        simp [removeF, hh, hne, hnext]
      rw [hrm] at hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp.symm
      rw [eq_of_spec_fd (tcbqueue.Queue.is_empty.spec _)]
      simp only [bind_ok, hy0, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [eq_of_spec_fd (endpoint.set_queue.spec (L := L) _ ep _ _)]
      unfold epFast
      simp only [hne, ↓reduceIte, hnext, hst]
      rw [epW_comm hX hE hdT hda]
      rfl
  apply eq_of_spec_fd
  unfold endpoint.ep_dequeue
  rw [eq_of_spec_fd (endpoint.get_queue.spec (L := L) s ep), eq_of_spec_fd (obj.Ep.state.spec (L := L) s ep)]
  simp only [bind_ok]
  refine WP.spec_bind (tcbqueue.remove.eq (L := L) s .Ep _ dest) ?_
  rintro ⟨q1, s1⟩ hp
  simp only [WP.uncurry'_pair] at hp
  exact spec_of_eq_fd (key q1 s1 hp.symm)

end

/-! ## The general path up to `unblock_sporadic` -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem fault_type_ok (s : S) (t : obj.Tcb) : obj.Tcb.fault_type st t s = ok (L.mem s (faultA t)) := by
  apply eq_of_spec_fd; unfold obj.Tcb.fault_type; step*; simp_all [faultA]

theorem us_ne_null : fl4_abi.consts.fault.UnknownSyscall ≠ fl4_abi.consts.fault.NullFault := by
  simp [fl4_abi.consts.fault.UnknownSyscall, fl4_abi.consts.fault.NullFault]

/-- The current thread word. -/
abbrev curA (s : S) : U64 := L.nodeAt s (L.cpu s) layout.node.CUR_THREAD
/-- The scheduler action word. -/
abbrev actA (s : S) : U64 := L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION

theorem curA_wr (s : S) (a v : U64) : curA (L := L) (L.wr s a v) = curA (L := L) s := by
  simp [curA, LawfulStore.nodeAt]
theorem actA_wr (s : S) (a v : U64) : actA (L := L) (L.wr s a v) = actA (L := L) s := by
  simp [actA, LawfulStore.nodeAt]

/-- `schedule_tcb` of a thread that is not the current one is no write. -/
theorem schedule_tcb_other (s : S) (x : obj.Tcb) (h : L.mem s (curA (L := L) s) ≠ x) :
    sched.schedule_tcb st s x = ok s := by
  unfold sched.schedule_tcb
  rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _)]; simp only [bind_ok]
  simp only [show x ≠ L.mem s (curA (L := L) s) from Ne.symm h, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- A thread in state `v` none of Running, Restart, RunningVM is not schedulable. -/
theorem is_schedulable_not (s : S) (x : obj.Tcb)
    (h : ¬ (L.mem s (stA x) = sched.TS_RUNNING ∨ L.mem s (stA x) = sched.TS_RESTART ∨
      L.mem s (stA x) = sched.TS_RUNNING_VM)) :
    sched.is_schedulable st s x = ok false := by
  unfold sched.is_schedulable
  rw [eq_of_spec_fd (sched.is_runnable.spec (L := L) s x)]; simp only [bind_ok]
  simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- `schedule_tcb` of the current thread, resumed and now blocked: the action
becomes `CHOOSE_NEW`. -/
theorem schedule_tcb_block (s : S) (x : obj.Tcb) (hc : L.mem s (curA (L := L) s) = x)
    (ha : L.actionW s = sched.ACTION_RESUME_CURRENT)
    (h : ¬ (L.mem s (stA x) = sched.TS_RUNNING ∨ L.mem s (stA x) = sched.TS_RESTART ∨
      L.mem s (stA x) = sched.TS_RUNNING_VM)) :
    sched.schedule_tcb st s x = ok (L.wr s (actA (L := L) s) sched.ACTION_CHOOSE_NEW) := by
  unfold sched.schedule_tcb
  rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _), hc]; simp only [bind_ok, decide_true, ↓reduceIte]
  rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]; simp only [bind_ok, ↓reduceIte]
  rw [is_schedulable_not s x h]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  exact eq_of_spec_fd (sched.set_action.spec (L := L) s _)

theorem bor_not_runnable :
    ¬ (sched.TS_BLOCKED_ON_REPLY = sched.TS_RUNNING ∨ sched.TS_BLOCKED_ON_REPLY = sched.TS_RESTART ∨
      sched.TS_BLOCKED_ON_REPLY = sched.TS_RUNNING_VM) := by
  simp [sched.TS_BLOCKED_ON_REPLY, sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM]

/-- `reply_push` of the faulting `t` to the handler `dest`, which has a
scheduling context (so nothing is donated): the reply names `t`, `t` blocks on
it, and, `t` being current and resumed, the action becomes `CHOOSE_NEW`. -/
theorem reply_push_fault {A : Type _} (ar : machine.Arch A) (s10 : S) (a : A) (t dest r : U64) (cd : Bool)
    (hc : L.mem s10 (curA (L := L) s10) = t) (ha : L.actionW s10 = sched.ACTION_RESUME_CURRENT)
    (hst : L.mem (L.wr (L.wr (L.wr s10 (rTcbA r) t) (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r) (stA t) =
      sched.TS_BLOCKED_ON_REPLY)
    (hc' : L.mem (L.wr (L.wr (L.wr s10 (rTcbA r) t) (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)
      (curA (L := L) s10) = t)
    (ha' : L.actionW (L.wr (L.wr (L.wr s10 (rTcbA r) t) (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r) =
      sched.ACTION_RESUME_CURRENT)
    (hd : L.mem (L.wr (L.wr (L.wr (L.wr s10 (rTcbA r) t) (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)
      (actA (L := L) s10) sched.ACTION_CHOOSE_NEW) (scA dest) ≠ 0#u64) :
    ipc.reply_push st ar s10 a t dest r cd =
      ok (L.wr (L.wr (L.wr (L.wr s10 (rTcbA r) t) (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)
        (actA (L := L) s10) sched.ACTION_CHOOSE_NEW, a) := by
  have _ := hc; have _ := ha
  unfold ipc.reply_push
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s10 t)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) s10 r t)]; simp only [bind_ok]
  unfold sched.set_blocked_on_reply
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_reply_obj.wr (L := L) _ t _)]; simp only [bind_ok]
  rw [schedule_tcb_block _ t (by rw [curA_wr, curA_wr, curA_wr]; exact hc') ha'
    (by rw [hst]; exact bor_not_runnable)]
  simp only [bind_ok, curA_wr, actA_wr]
  rw [eq_of_spec_fd (obj.Sc.is_null.spec _)]; simp only [bind_ok]
  by_cases h0 : L.mem s10 (scA t) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) _ dest)]; simp only [bind_ok, hd, ↓reduceIte]

end

/-! ## The accepted run -/

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

/-- The write part of an accepted `fastpath.fault` (fastpath.rs, from
`set_fault` to `switch_to`), verbatim from the extraction. -/
def faultTail (s : S) (a : A) (t : obj.Tcb) (number : Std.U64) (ptr badge i2 i3 : Std.U64) :
    Result (Bool × S × A) := do
  let s2 ←
    faults.set_fault st s t
      (error.Fault.UnknownSyscall number)
  let tail ← obj.Ep.tail st ptr s2
  let s3 ←
    if tail = i2
    then
      obj.Ep.set_queue st ptr s2 0#u64 0#u64
        obj.EP_IDLE
    else
      do
      let i6 ← obj.Tcb.ep_next st i2 s2
      let s4 ← obj.Tcb.set_ep_prev st i6 s2 0#u64
      obj.Ep.set_queue st ptr s4 i6 tail
        obj.EP_RECV
  let s4 ← obj.Tcb.set_ep_next st i2 s3 0#u64
  let s5 ← obj.Tcb.set_ep_prev st i2 s4 0#u64
  let recv_buf ←
    msg.lookup_ipc_buffer st s5 true i2
  let (sent, s6) ←
    faults.set_mrs_fault st ar s5 a t
      i2 recv_buf
  let mi ←
    msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall
      0#u64 0#u64 sent
  let s7 ← msg.set_msg_info st s6 i2 mi
  let s8 ←
    obj.Tcb.set_reg st i2 s7 layout.reg.BADGE badge
  let s9 ← obj.Reply.set_tcb st i3 s8 0#u64
  let s10 ←
    obj.Tcb.set_state st i2 s9 sched.TS_INACTIVE
  let s11 ← obj.Reply.set_tcb st i3 s10 t
  let s12 ←
    obj.Tcb.set_state st t s11
      sched.TS_BLOCKED_ON_REPLY
  let s13 ← obj.Tcb.set_reply_obj st t s12 i3
  let s14 ←
    obj.Tcb.set_state st i2 s13 sched.TS_RUNNING
  let i6 ← obj.Tcb.sc st i2 s14
  let b2 ← sporadic.sc_sporadic st s14 i6
  let s15 ←
    if b2
    then
      do
      let s16 ← sched.cur_sc st s14
      let b3 ←
        core.cmp.PartialEq.ne.trait_default
          obj.Sc.Insts.CoreCmpPartialEqSc i6 s16
      if b3
      then sporadic.unblock_check st s14 i6
      else ok s14
    else ok s14
  let s16 ←
    obj.Tcb.set_sched_next st i2 s15 0#u64
  let s17 ←
    obj.Tcb.set_sched_prev st i2 s16 0#u64
  let (s18, a1) ←
    fastpath.switch_to st ar s17 a i2
  ok (true, s18, a1)

/-- The checks of an accepted `fastpath.fault` at its entry state `s`. -/
structure FaultChecks (s : S) (t : obj.Tcb) (ptr badge dest r : Std.U64) : Prop where
  act : sched.action st s = ok sched.ACTION_RESUME_CURRENT
  cap : ∃ sl x y g gr, obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok sl ∧
      obj.Slot.cap st sl s = ok (capability.Cap.Endpoint ptr badge x y g gr) ∧ (g = true ∨ gr = true)
  ep : obj.Ep.state st ptr s = ok obj.EP_RECV
  head : obj.Ep.head st ptr s = ok dest
  reply : obj.Tcb.reply_obj st dest s = ok r
  r0 : r ≠ 0#u64
  here : fastpath.schedulable_here st s dest = ok true
  prio : ∃ d p, sched.cur_domain st s = ok d ∧ obj.Tcb.prio st dest s = ok p ∧
      sched.is_highest_prio st s d p = ok true

theorem bind_eq_ok {α β : Type _} {m : Result α} {f : α → Result β} {y : β}
    (h : Std.bind m f = ok y) : ∃ x, m = ok x ∧ f x = ok y := by
  obtain ⟨x, e, hx⟩ := spec_bind_inv (spec_of_eq_fd h)
  exact ⟨x, e, eq_of_spec_fd hx⟩

/-- **Inversion of an accepted `fastpath.fault`**: its checks held at the
entry state and the run is `faultTail` from there. -/
theorem fault_acc {s : S} {a : A} {t : obj.Tcb} {n : Std.U64} {s' : S} {a' : A}
    (h : fastpath.fault st ar s a t n = ok (true, s', a')) :
    ∃ ptr badge dest r, FaultChecks st s t ptr badge dest r ∧
      faultTail st ar s a t n ptr badge dest r = ok (true, s', a') := by
  unfold fastpath.fault at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  split at h
  · simp at h
  rename_i hic
  obtain ⟨sl, hsl, h⟩ := bind_eq_ok h
  obtain ⟨c, hc, h⟩ := bind_eq_ok h
  cases c
  all_goals try (simp at h; done)
  rename_i ptr badge x y g gr
  dsimp only at h
  by_cases hg : g = true
  · have GR : g = true ∨ gr = true := Or.inl hg
    rw [if_pos hg] at h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    split at h
    · simp at h
    rename_i hi1c
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
    split at h
    · simp at h
    rename_i hi3c
    obtain ⟨b, hb, h⟩ := bind_eq_ok h
    split at h
    swap
    · simp at h
    rename_i hbc
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
    obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
    split at h
    swap
    · simp at h
    rename_i hb1c
    refine ⟨ptr, badge, i2, i3, ⟨?_, ?_, ?_, hi2, hi3, hi3c, ?_, ⟨i4, i5, hi4, hi5, ?_⟩⟩, h⟩
    · rw [hi]; congr 1; simp only [bne_iff_ne, ne_eq, not_not] at hic; exact hic
    · exact ⟨sl, _, _, g, gr, hsl, hc, GR⟩
    · rw [hi1]; congr 1; simp only [bne_iff_ne, ne_eq, not_not] at hi1c; exact hi1c
    · rw [hb, hbc]
    · rw [hb1, hb1c]
  · rw [if_neg hg] at h
    by_cases hgr : gr = true
    · have GR : g = true ∨ gr = true := Or.inr hgr
      rw [if_pos hgr] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      split at h
      · simp at h
      rename_i hi1c
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      split at h
      · simp at h
      rename_i hi3c
      obtain ⟨b, hb, h⟩ := bind_eq_ok h
      split at h
      swap
      · simp at h
      rename_i hbc
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
      split at h
      swap
      · simp at h
      rename_i hb1c
      refine ⟨ptr, badge, i2, i3, ⟨?_, ?_, ?_, hi2, hi3, hi3c, ?_, ⟨i4, i5, hi4, hi5, ?_⟩⟩, h⟩
      · rw [hi]; congr 1; simp only [bne_iff_ne, ne_eq, not_not] at hic; exact hic
      · exact ⟨sl, _, _, g, gr, hsl, hc, GR⟩
      · rw [hi1]; congr 1; simp only [bne_iff_ne, ne_eq, not_not] at hi1c; exact hi1c
      · rw [hb, hbc]
      · rw [hb1, hb1c]
    · rw [if_neg hgr] at h; simp at h


/-- `faultTail` from the end of the endpoint dequeue (`s5`). -/
def faultTail2 (s5 : S) (a : A) (t : obj.Tcb) (i2 i3 badge : Std.U64) : Result (Bool × S × A) := do
  let recv_buf ←
    msg.lookup_ipc_buffer st s5 true i2
  let (sent, s6) ←
    faults.set_mrs_fault st ar s5 a t
      i2 recv_buf
  let mi ←
    msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall
      0#u64 0#u64 sent
  let s7 ← msg.set_msg_info st s6 i2 mi
  let s8 ←
    obj.Tcb.set_reg st i2 s7 layout.reg.BADGE badge
  let s9 ← obj.Reply.set_tcb st i3 s8 0#u64
  let s10 ←
    obj.Tcb.set_state st i2 s9 sched.TS_INACTIVE
  let s11 ← obj.Reply.set_tcb st i3 s10 t
  let s12 ←
    obj.Tcb.set_state st t s11
      sched.TS_BLOCKED_ON_REPLY
  let s13 ← obj.Tcb.set_reply_obj st t s12 i3
  let s14 ←
    obj.Tcb.set_state st i2 s13 sched.TS_RUNNING
  let i6 ← obj.Tcb.sc st i2 s14
  let b2 ← sporadic.sc_sporadic st s14 i6
  let s15 ←
    if b2
    then
      do
      let s16 ← sched.cur_sc st s14
      let b3 ←
        core.cmp.PartialEq.ne.trait_default
          obj.Sc.Insts.CoreCmpPartialEqSc i6 s16
      if b3
      then sporadic.unblock_check st s14 i6
      else ok s14
    else ok s14
  let s16 ←
    obj.Tcb.set_sched_next st i2 s15 0#u64
  let s17 ←
    obj.Tcb.set_sched_prev st i2 s16 0#u64
  let (s18, a1) ←
    fastpath.switch_to st ar s17 a i2
  ok (true, s18, a1)

/-- The fast path's first writes: `set_fault`, then the dequeue `epFast`. -/
theorem faultTail_eq [L : LawfulStore st] (s : S) (a : A) (t : obj.Tcb) (n ptr badge dest r : U64) :
    faultTail st ar s a t n ptr badge dest r =
      faultTail2 st ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t dest r badge := by
  unfold faultTail
  rw [set_fault_us]; simp only [bind_ok]
  rw [obj.Ep.tail.ok]; simp only [bind_ok]
  by_cases htl : (L.epQ (sfW (L := L) s t n) ptr).end = dest
  · rw [if_pos htl, obj.Ep.set_queue.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    unfold epFast; simp only [htl, ↓reduceIte]; rfl
  · rw [if_neg htl]
    rw [obj.Tcb.ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    rw [obj.Ep.set_queue.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    unfold epFast; simp only [htl, ↓reduceIte]; rfl


/-- `faultTail` from the handler made `Running` (`s14`). -/
def faultTail3 (s14 : S) (a : A) (i2 : Std.U64) : Result (Bool × S × A) := do
  let i6 ← obj.Tcb.sc st i2 s14
  let b2 ← sporadic.sc_sporadic st s14 i6
  let s15 ←
    if b2
    then
      do
      let s16 ← sched.cur_sc st s14
      let b3 ←
        core.cmp.PartialEq.ne.trait_default
          obj.Sc.Insts.CoreCmpPartialEqSc i6 s16
      if b3
      then sporadic.unblock_check st s14 i6
      else ok s14
    else ok s14
  let s16 ←
    obj.Tcb.set_sched_next st i2 s15 0#u64
  let s17 ←
    obj.Tcb.set_sched_prev st i2 s16 0#u64
  let (s18, a1) ←
    fastpath.switch_to st ar s17 a i2
  ok (true, s18, a1)


end

/-! ## `handle_fault`, the general path, up to `unblock_sporadic` -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- `reply_unlink`'s two writes (the reply's TCB word, the handler Inactive). -/
def fS10 (s8 : S) (dest r : U64) : S := L.wr (L.wr s8 (rTcbA r) 0#u64) (stA dest) sched.TS_INACTIVE
/-- `reply_push`'s three writes before `schedule_tcb` (both paths). -/
def fS13 (s10 : S) (t r : U64) : S :=
  L.wr (L.wr (L.wr s10 (rTcbA r) t) (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r

/-- **The general `handle_fault` of an UnknownSyscall fault to a waiting
handler** (fastpath.rs `fault`, KENTRY-PLAN m57 (2)), up to the
`unblock_sporadic` of the handler: the same `set_fault`, the dequeue of the
head (`ep_dequeue_head`, F2), the same `lookup_ipc_buffer` / `set_mrs_fault` /
`set_msg_info` / `BADGE` (at the same states), `reply_unlink`, `reply_push`
(no donation: the handler has an SC) whose `schedule_tcb` of the blocked
current thread writes the action `CHOOSE_NEW`, and the handler `Running`.
The reads are taken at the states where the general path makes them (`hR*`;
their derivation from the entry state is `fault_reads`'s). -/
theorem handle_fault_pre (hX : StoreExt st) {T : Set U64} (hT : TcbPlaced T)
    (s : S) (a : A) (t : obj.Tcb) (n ptr badge dest r : U64) (rest : List U64)
    {sl : obj.Slot} {x y g gr : Bool}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s = ok (capability.Cap.Endpoint ptr badge x y g gr)) (hG : g = true ∨ gr = true)
    (hE : EpPlaced T ptr)
    (hq1 : QueueRel (L.mem (sfW (L := L) s t n)) T .Ep (L.epQ (sfW (L := L) s t n) ptr) (dest :: rest))
    (hst1 : L.epState (sfW (L := L) s t n) ptr = obj.EP_RECV)
    {rb sent : U64} {S6 S7 S8 : S} {mi : msginfo.MessageInfo}
    (hbuf : msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest = ok rb)
    (hmrs : faults.set_mrs_fault st ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t dest rb = ok (sent, S6))
    (hR5 : L.mem (epFast (L := L) (sfW (L := L) s t n) ptr dest) (faultA t) = fl4_abi.consts.fault.UnknownSyscall)
    (hR6 : L.mem S6 (faultA t) = fl4_abi.consts.fault.UnknownSyscall)
    (hmi : msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall 0#u64 0#u64 sent = ok mi)
    (hS7 : msg.set_msg_info st S6 dest mi = ok S7)
    (hS8 : obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8)
    (hR8 : L.mem S8 (replyA dest) = r) (hr0 : r ≠ 0#u64) (hdt : dest ≠ t)
    (hR10c : L.mem (fS10 (L := L) S8 dest r) (curA (L := L) S8) = t)
    (hR10f : L.mem (fS10 (L := L) S8 dest r) (faultA t) = fl4_abi.consts.fault.UnknownSyscall)
    (hR10a : L.actionW (fS10 (L := L) S8 dest r) = sched.ACTION_RESUME_CURRENT)
    (hR13s : L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (hR13c : L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (curA (L := L) S8) = t)
    (hR13a : L.actionW (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) = sched.ACTION_RESUME_CURRENT)
    (hR13d : L.mem (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) S8) sched.ACTION_CHOOSE_NEW)
      (scA dest) ≠ 0#u64)
    (hR14c : L.mem (L.wr (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) S8)
      sched.ACTION_CHOOSE_NEW) (stA dest) sched.TS_RUNNING) (curA (L := L) S8) = t) :
    faults.handle_fault st ar s a t (error.Fault.UnknownSyscall n) =
      (do
        let s6 ← endpoint.unblock_sporadic st (L.wr (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r)
          (actA (L := L) S8) sched.ACTION_CHOOSE_NEW) (stA dest) sched.TS_RUNNING) dest
        let s7 ← sched.possible_switch_to st s6 dest
        ok (s7, a)) := by
  have hcur10 : ∀ v w, curA (L := L) (L.wr (L.wr S8 v w) (stA dest) sched.TS_INACTIVE) = curA (L := L) S8 :=
    fun v w => by rw [curA_wr, curA_wr]
  have hRP : ∀ cd, ipc.reply_push st ar (fS10 (L := L) S8 dest r) a t dest r cd =
      ok (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) S8) sched.ACTION_CHOOSE_NEW, a) := by
    intro cd
    have e := reply_push_fault (L := L) ar (fS10 (L := L) S8 dest r) a t dest r cd
      (by unfold fS10; rw [hcur10]; exact hR10c) hR10a hR13s
      (by unfold fS10 at hR13c ⊢; rw [hcur10]; exact hR13c) hR13a
      (by unfold fS13 at hR13d; unfold fS10 at hR13d ⊢; simp only [actA_wr]; exact hR13d)
    unfold fS13 at e ⊢
    rw [e]; unfold fS10; simp only [actA_wr]
  unfold faults.handle_fault
  rw [hsl]; simp only [bind_ok]
  rw [hcap]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s t)]; simp only [bind_ok]
  unfold faults.send_fault_ipc
  rw [set_fault_us]; simp only [bind_ok]
  unfold endpoint.send_ipc
  have e1 : obj.EP_RECV ≠ obj.EP_IDLE := by unfold obj.EP_RECV obj.EP_IDLE; decide
  have e2 : obj.EP_RECV ≠ obj.EP_SEND := by unfold obj.EP_RECV obj.EP_SEND; decide
  rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) _ ptr), hst1]
  simp only [bind_ok, e1, e2, ↓reduceIte]
  rw [eq_of_spec_fd (endpoint.get_queue.spec (L := L) _ ptr)]; simp only [bind_ok]
  have hh : (L.epQ (sfW (L := L) s t n) ptr).head = dest := by simpa using hq1.head
  rw [hh, ep_dequeue_head hX hT hE hq1 hst1]; simp only [bind_ok]
  unfold ipc.do_ipc_transfer
  rw [hbuf]; simp only [bind_ok]
  rw [fault_type_ok, hR5]; simp only [bind_ok, us_ne_null, ↓reduceIte]
  unfold ipc.do_fault_transfer
  rw [hmrs]; simp only [bind_ok, uncurry_apply_pair]
  rw [fault_type_ok, hR6]; simp only [bind_ok]
  rw [hmi]; simp only [bind_ok]
  rw [hS7]; simp only [bind_ok]
  rw [hS8]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) S8 dest), hR8]
  simp only [bind_ok, bne_iff_ne, ne_eq, hr0, not_false_eq_true, ↓reduceIte]
  unfold ipc.reply_unlink
  rw [eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) S8 r _)]; simp only [bind_ok]
  unfold sched.set_thread_state
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
  rw [schedule_tcb_other _ dest (by rw [hcur10]; unfold fS10 at hR10c; rw [hR10c]; exact Ne.symm hdt)]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have hf10 := hR10f; unfold fS10 at hf10
  rw [fault_type_ok, hf10]; simp only [bind_ok, bne_iff_ne, ne_eq, us_ne_null, not_false_eq_true, ↓reduceIte]
  have hRP' := hRP; unfold fS10 at hRP'
  rcases hG with hg | hgr
  · subst hg; simp only [↓reduceIte]; rw [hRP']; simp only [bind_ok, uncurry_apply_pair]
    rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
    rw [schedule_tcb_other _ dest (by
      unfold fS13 fS10 at hR14c; (try unfold fS13); simp only [curA_wr]; rw [hR14c]; exact Ne.symm hdt)]
    simp only [bind_ok, Std.bind_assoc, ↓reduceIte, uncurry_apply_pair]
    unfold fS13 fS10; rfl
  · subst hgr
    cases g
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hRP']; simp only [bind_ok, uncurry_apply_pair]
      rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
      rw [schedule_tcb_other _ dest (by
        unfold fS13 fS10 at hR14c; (try unfold fS13); simp only [curA_wr]; rw [hR14c]; exact Ne.symm hdt)]
      simp only [bind_ok, Std.bind_assoc, ↓reduceIte, uncurry_apply_pair]
      unfold fS13 fS10; rfl
    · simp only [↓reduceIte]; rw [hRP']; simp only [bind_ok, uncurry_apply_pair]
      rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
      rw [schedule_tcb_other _ dest (by
        unfold fS13 fS10 at hR14c; (try unfold fS13); simp only [curA_wr]; rw [hR14c]; exact Ne.symm hdt)]
      simp only [bind_ok, Std.bind_assoc, ↓reduceIte, uncurry_apply_pair]
      unfold fS13 fS10; rfl

/-- The fast path from the dequeue to the handler `Running`: the general
path's writes in the same order (`fS10`, `fS13`), then `dest` Running. -/
theorem faultTail2_eq (s5 : S) (a : A) (t : obj.Tcb) (dest r badge : U64)
    {rb sent : U64} {S6 S7 S8 : S} {mi : msginfo.MessageInfo}
    (hbuf : msg.lookup_ipc_buffer st s5 true dest = ok rb)
    (hmrs : faults.set_mrs_fault st ar s5 a t dest rb = ok (sent, S6))
    (hmi : msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall 0#u64 0#u64 sent = ok mi)
    (hS7 : msg.set_msg_info st S6 dest mi = ok S7)
    (hS8 : obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8) :
    faultTail2 st ar s5 a t dest r badge =
      faultTail3 st ar (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (stA dest) sched.TS_RUNNING) a dest := by
  unfold faultTail2
  rw [hbuf]; simp only [bind_ok]
  rw [hmrs]; simp only [bind_ok, uncurry_apply_pair]
  rw [hmi]; simp only [bind_ok]
  rw [hS7]; simp only [bind_ok]
  rw [hS8]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ r _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ r _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_reply_obj.wr (L := L) _ t _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
  unfold faultTail3 fS13 fS10; rfl


/-- **The reads of the general fault path** at the states where it makes them
(KENTRY-PLAN m57 F1, F2, F5 at those states), for the run's intermediate
states `S6` (after `set_mrs_fault`) and `S8` (after the `BADGE` write). Each
is a read of a word that only the named writes before it could change; their
derivation from the entry state's P1 placement (`TcbPlaced`, `EpPlaced`,
`NodePlaced`, the receive buffer outside the kernel objects) is the next step
(m58 handoff). -/
structure FaultReads (T : Set U64) (s : S) (t : obj.Tcb) (n ptr dest r : U64) (rest : List U64) (S6 S8 : S) :
    Prop where
  hT : TcbPlaced T
  hE : EpPlaced T ptr
  /-- F2 at `set_fault`'s state: the endpoint's queue, headed by `dest`. -/
  hq1 : QueueRel (L.mem (sfW (L := L) s t n)) T .Ep (L.epQ (sfW (L := L) s t n) ptr) (dest :: rest)
  hst1 : L.epState (sfW (L := L) s t n) ptr = obj.EP_RECV
  hR5 : L.mem (epFast (L := L) (sfW (L := L) s t n) ptr dest) (faultA t) = fl4_abi.consts.fault.UnknownSyscall
  hR6 : L.mem S6 (faultA t) = fl4_abi.consts.fault.UnknownSyscall
  hR8 : L.mem S8 (replyA dest) = r
  /-- F1: the handler is not the faulting thread. -/
  hdt : dest ≠ t
  hR10c : L.mem (fS10 (L := L) S8 dest r) (curA (L := L) S8) = t
  hR10f : L.mem (fS10 (L := L) S8 dest r) (faultA t) = fl4_abi.consts.fault.UnknownSyscall
  hR10a : L.actionW (fS10 (L := L) S8 dest r) = sched.ACTION_RESUME_CURRENT
  hR13s : L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (stA t) = sched.TS_BLOCKED_ON_REPLY
  hR13c : L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (curA (L := L) S8) = t
  hR13a : L.actionW (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) = sched.ACTION_RESUME_CURRENT
  hR13d : L.mem (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) S8) sched.ACTION_CHOOSE_NEW)
      (scA dest) ≠ 0#u64
  hR14c : L.mem (L.wr (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) S8)
      sched.ACTION_CHOOSE_NEW) (stA dest) sched.TS_RUNNING) (curA (L := L) S8) = t
  /-- F5 for the action word and the handler's state word. -/
  haA : Aligned (actA (L := L) S8)
  hsA : Aligned (stA dest)
  hAS : actA (L := L) S8 ≠ stA dest

/-- **The two paths meet** (m58): an accepted `fastpath.fault` run and the
general `handle_fault` reach the same state `S14` (the handler `Running`)
except for the action word, which the general path has set to `CHOOSE_NEW`
(the blocked current thread's `schedule_tcb`); from there the fast path runs
`faultTail3` and the general path `unblock_sporadic` + `possible_switch_to`
(then `finish`). -/
theorem fault_sync (hX : StoreExt st) {T : Set U64} {s : S} {a : A} {t : obj.Tcb} {n ptr badge dest r : U64}
    {sF : S} {aF : A} (hc : FaultChecks st s t ptr badge dest r)
    (hfast : faultTail st ar s a t n ptr badge dest r = ok (true, sF, aF))
    (hR : ∀ (rb sent : U64) (S6 S7 S8 : S) (mi : msginfo.MessageInfo),
      msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest = ok rb →
      faults.set_mrs_fault st ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t dest rb = ok (sent, S6) →
      msginfo.MessageInfo.new fl4_abi.consts.fault.UnknownSyscall 0#u64 0#u64 sent = ok mi →
      msg.set_msg_info st S6 dest mi = ok S7 →
      obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8 →
      ∃ rest, FaultReads (L := L) T s t n ptr dest r rest S6 S8) :
    ∃ S14 : S, faultTail3 st ar S14 a dest = ok (true, sF, aF) ∧
      faults.handle_fault st ar s a t (error.Fault.UnknownSyscall n) =
        (do
          let s6 ← endpoint.unblock_sporadic st (L.wr S14 (actA (L := L) S14) sched.ACTION_CHOOSE_NEW) dest
          let s7 ← sched.possible_switch_to st s6 dest
          ok (s7, a)) := by
  rw [faultTail_eq] at hfast
  have hf0 := hfast
  unfold faultTail2 at hfast
  obtain ⟨rb, hbuf, h1⟩ := bind_eq_ok hfast
  obtain ⟨⟨sent, S6⟩, hmrs, h2⟩ := bind_eq_ok h1
  try simp only [uncurry_apply_pair] at h2
  obtain ⟨mi, hmi, h3⟩ := bind_eq_ok h2
  obtain ⟨S7, hS7, h4⟩ := bind_eq_ok h3
  obtain ⟨S8, hS8, -⟩ := bind_eq_ok h4
  obtain ⟨rest, R⟩ := hR rb sent S6 S7 S8 mi hbuf hmrs hmi hS7 hS8
  obtain ⟨sl, x, y, g, gr, hsl, hcap, hG⟩ := hc.cap
  refine ⟨L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (stA dest) sched.TS_RUNNING, ?_, ?_⟩
  · rw [faultTail2_eq ar _ a t dest r badge hbuf hmrs hmi hS7 hS8] at hf0; exact hf0
  · rw [handle_fault_pre ar hX R.hT s a t n ptr badge dest r rest hsl hcap hG R.hE R.hq1 R.hst1 hbuf hmrs
      R.hR5 R.hR6 hmi hS7 hS8 R.hR8 hc.r0 R.hdt R.hR10c R.hR10f R.hR10a R.hR13s R.hR13c R.hR13a R.hR13d R.hR14c]
    have hA14 : actA (L := L) (L.wr (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (stA dest) sched.TS_RUNNING) =
        actA (L := L) S8 := by
      unfold fS13 fS10; simp only [actA_wr]
    rw [hA14, wr_comm hX _ _ _ R.haA R.hsA R.hAS]


theorem cn_ne_resume : sched.ACTION_CHOOSE_NEW ≠ sched.ACTION_RESUME_CURRENT := by
  unfold sched.ACTION_CHOOSE_NEW sched.ACTION_RESUME_CURRENT; decide

/-- **`possible_switch_to` from `CHOOSE_NEW`** (m57 (2), after `reply_push`):
the handler has an SC, is outside the release queue, in the current domain and
on this core, and the action is already `CHOOSE_NEW`, so `reschedule_required`
rewrites the action with its own value and the call is `enqueue`. -/
theorem possible_switch_to_cn (hX : StoreExt st) (s : S) (d : obj.Tcb) (hsc : L.mem s (scA d) ≠ 0#u64)
    (hrq : (L.mem s (inqA d) &&& sched.Q_RELEASE) = 0#u64)
    (hdom : L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) = L.mem s (domA d))
    (haff : L.mem s (affA d) = L.cpu s) (ha : L.actionW s = sched.ACTION_CHOOSE_NEW)
    (hal : Aligned (actA (L := L) s)) :
    sched.possible_switch_to st s d = sched.enqueue st s d := by
  unfold sched.possible_switch_to
  rw [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s d)]; simp only [bind_ok, hsc, ↓reduceIte]
  rw [eq_of_spec_fd (sched.in_release_queue.spec (L := L) s d)]
  simp only [bind_ok, hrq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold sched.cur_domain
  rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s _), hdom]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.domain.spec (L := L) s d)]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s d), haff, L.cur_cpu_eq]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have h1 : (sched.ACTION_CHOOSE_NEW != sched.ACTION_RESUME_CURRENT) = true := by
    unfold sched.ACTION_CHOOSE_NEW sched.ACTION_RESUME_CURRENT; decide
  have h2 : (sched.ACTION_CHOOSE_NEW != sched.ACTION_CHOOSE_NEW) = false := bne_self_eq_false _
  rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  simp only [bind_ok, h1, ↓reduceIte]
  unfold sched.reschedule_required
  rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  simp only [bind_ok, h1, h2, Bool.false_eq_true, ↓reduceIte]
  rw [eq_of_spec_fd (sched.set_action.spec (L := L) s _)]; simp only [bind_ok]
  rw [wr_eq_self hX s hal ha]

end

end Fl4Proofs.P1
