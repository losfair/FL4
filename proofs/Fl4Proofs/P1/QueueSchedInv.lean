/-
P1: `SchedQueuesInv`, the scheduler queue invariant over the ghost set `T`
of TCBs and the set `Cs` of cores: every core's ready queues (with their
bitmap) and release queue are related to the ghost lists `Q c p` and `R c`;
a thread in a ready queue is in the one of its own core and priority, a
thread in a release queue in the one of its own core, never in both; the
`IN_QUEUES` flags say exactly where a thread is (seL4 `valid_queues`,
`valid_release_q`, `ready_or_release`). `enqueue`, `dequeue`,
`release_enqueue` and `release_remove` preserve it.
-/
import Fl4Proofs.P1.QueueInv
import Fl4Proofs.P1.QueueEp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-! ## The flag bits -/

theorem two_bit (j : Nat) : (2#u64).bv.getLsbD j = decide (j = 1) := by
  have : (2#u64).bv = BitVec.ofNat _ 2 := rfl
  rw [this, BitVec.getLsbD_ofNat]
  rcases j with _ | _ | j <;> simp [Nat.testBit_succ]
theorem qq_val : sched.Q_QUEUED = 1#u64 := by unfold sched.Q_QUEUED; rfl
theorem qr_val : sched.Q_RELEASE = 2#u64 := by unfold sched.Q_RELEASE; rfl
theorem or_qq_qr (x : U64) : (x ||| sched.Q_QUEUED) &&& sched.Q_RELEASE = x &&& sched.Q_RELEASE := by
  simp only [qq_val, qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, two_bit]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · simp [h0, h1]
theorem andn_qq_qr (x : U64) : (x &&& ~~~sched.Q_QUEUED) &&& sched.Q_RELEASE = x &&& sched.Q_RELEASE := by
  simp only [qq_val, qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, two_bit]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · simp [h0, h1]
theorem or_qr_qq (x : U64) : (x ||| sched.Q_RELEASE) &&& sched.Q_QUEUED = x &&& sched.Q_QUEUED := by
  simp only [qq_val, qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, two_bit]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · simp [h0, h1]
theorem andn_qr_qq (x : U64) : (x &&& ~~~sched.Q_RELEASE) &&& sched.Q_QUEUED = x &&& sched.Q_QUEUED := by
  simp only [qq_val, qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, two_bit]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · simp [h0, h1]
theorem or_qq_qq (x : U64) : (x ||| sched.Q_QUEUED) &&& sched.Q_QUEUED = sched.Q_QUEUED := by
  simp only [qq_val, qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, two_bit]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · simp [h0, h1]
theorem andn_qq_qq (x : U64) : (x &&& ~~~sched.Q_QUEUED) &&& sched.Q_QUEUED = 0#u64 := by
  have : (0#u64).bv = 0#64 := rfl
  rw [qq_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, one_bit, this, BitVec.getLsbD_zero]
  by_cases h0 : i = 0 <;> simp [h0]
theorem or_qr_qr (x : U64) : (x ||| sched.Q_RELEASE) &&& sched.Q_RELEASE = sched.Q_RELEASE := by
  simp only [qq_val, qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, one_bit, two_bit]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1
    · simp [h1]
    · simp [h0, h1]
theorem andn_qr_qr (x : U64) : (x &&& ~~~sched.Q_RELEASE) &&& sched.Q_RELEASE = 0#u64 := by
  have : (0#u64).bv = 0#64 := rfl
  rw [qr_val]; apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, two_bit, this, BitVec.getLsbD_zero]
  by_cases h0 : i = 1 <;> simp [h0]
theorem qq_ne : sched.Q_QUEUED ≠ 0#u64 := by rw [qq_val]; intro h; have := congrArg UScalar.val h; simp at this
theorem qr_ne : sched.Q_RELEASE ≠ 0#u64 := by rw [qr_val]; intro h; have := congrArg UScalar.val h; simp at this


/-! ## The typed heap (ghost) -/

/-- Object kinds, with SCs and other objects carrying their size exponent. -/
inductive HKind where
  | tcb
  | ep
  | ntfn
  | reply
  | sc (z : Nat)
  | other (z : Nat)

/-- The size exponent of an object. -/
def HKind.bits : HKind → Nat
  | .tcb => 12
  | .ep => 4
  | .ntfn => 6
  | .reply => 5
  | .sc z => z
  | .other z => z

/-- A ghost typed heap: which pointers are objects, and of which kind. -/
abbrev Heap := U64 → Option HKind

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}

/-! ## The invariant -/

/-- The current core's `SCHED_ACTION` word. -/
def LawfulStore.actionW (s : S) : U64 := L.mem s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)

theorem act_val : layout.node.SCHED_ACTION.val = 16 := by simp [layout.node.SCHED_ACTION]
theorem curth0 : layout.node.CUR_THREAD.val = 0 := by simp [layout.node.CUR_THREAD]
theorem idle8 : layout.node.IDLE_THREAD.val = 8 := by simp [layout.node.IDLE_THREAD]

/-- A word outside every TCB of `T` and every node of `Cs`. -/
def OutsideObjs (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) (a : U64) : Prop :=
  Aligned a ∧ (∀ t ∈ T, a.val < t.val ∨ t.val + 2 ^ 12 ≤ a.val) ∧
    ∀ c ∈ Cs, a.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val

theorem OutsideObjs.ksb {Cs : Set U64} {s s' : S} {a : U64} (h : OutsideObjs st T Cs s a)
    (hk : L.ksb s' = L.ksb s) : OutsideObjs st T Cs s' a := by
  have e : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hk]
  exact ⟨h.1, h.2.1, fun c hc => by rw [e]; exact h.2.2 c hc⟩

def stA (t : U64) : U64 := core.num.U64.wrapping_add t layout.tcb.STATE
def blockA (t : U64) : U64 := core.num.U64.wrapping_add t 3336#u64

theorem stA_eq (t : U64) : stA t = core.num.U64.wrapping_add t 3328#u64 := by
  unfold stA layout.tcb.STATE layout.tcb.F; rfl

/-- A runnable thread state (seL4 `runnable`). -/
def Runnable (v : U64) : Prop := v = sched.TS_RUNNING ∨ v = sched.TS_RESTART ∨ v = sched.TS_RUNNING_VM
/-- A state blocked on an endpoint or notification queue. -/
def Blocked (v : U64) : Prop :=
  v = sched.TS_BLOCKED_ON_SEND ∨ v = sched.TS_BLOCKED_ON_RECV ∨ v = sched.TS_BLOCKED_ON_NTFN

/-- An endpoint (or notification) outside the nodes of `Cs`. -/
def EpOutNodes (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) (ep : U64) : Prop :=
  (∀ c ∈ Cs, ep.val + 16 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ ep.val) ∧
    (ep.val + 16 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ ep.val)

/-- Endpoint/notification typing and the same-state clause (l4v `valid_ep`,
`valid_ntfn`, with the encoding of P3's `EpObjRel` / `NtfnObjRel`): the
objects `E` are exactly the endpoints and notifications of the typed heap `H`; a thread
blocked on send or receive (outside `X`) waits on a heap endpoint, one
blocked on a notification on a heap notification; the members of a queue
share their state, and the object's state word is send (1) or receive (2)
for an endpoint, waiting (1) for a notification. -/
def EpTy (st : machine.Store S) [L : LawfulStore st] (T X : Set U64) (s : S) (E : Set U64)
    (EQ : U64 → List U64) (H : Heap) : Prop :=
  (∀ t ∈ T, t ∉ X → (L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV) →
    H (L.mem s (blockA t)) = some .ep) ∧
  (∀ t ∈ T, t ∉ X → L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN → H (L.mem s (blockA t)) = some .ntfn) ∧
  (∀ e, e ∈ E ↔ (H e = some .ep ∨ H e = some .ntfn)) ∧
  (∀ e ∈ E, ∀ y ∈ EQ e, ∀ z ∈ EQ e, L.mem s (stA y) = L.mem s (stA z)) ∧
  (∀ e ∈ E, ∀ y ∈ EQ e, (L.mem s (stA y) = sched.TS_BLOCKED_ON_SEND → L.epState s e = 1#u64) ∧
    (L.mem s (stA y) = sched.TS_BLOCKED_ON_RECV → L.epState s e = 2#u64) ∧
    (L.mem s (stA y) = sched.TS_BLOCKED_ON_NTFN → L.epState s e = 1#u64)) ∧
  (∀ e ∈ E, EQ e = [] → (H e = some .ep → L.epState s e = 0#u64) ∧ (H e = some .ntfn → L.epState s e ≠ 1#u64))

/-- The endpoint and notification queues: some set `E` of placed, disjoint
objects whose queues hold the ghost lists `EQ e`; the members of `EQ e` are
blocked on `e`, and every blocked thread outside the exception set `X` is a
member of the queue of the object it is blocked on (seL4 `valid_ep_q`,
`valid_ntfn_q`, `st_tcb_at` of the queue members); and `EpTy`. -/
def EpsWit (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (X : Set U64) (s : S)
    (E : Set U64) (EQ : U64 → List U64) : Prop :=
    (∀ e ∈ E, EpPlaced T e ∧ EpOutNodes st Cs s e ∧ QueueRel (L.mem s) T .Ep (L.epQ s e) (EQ e)) ∧
    (∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → e.val + 16 ≤ e'.val ∨ e'.val + 16 ≤ e.val) ∧
    (∀ e ∈ E, ∀ a ∈ Ω, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val) ∧
    (∀ e ∈ E, ∀ t ∈ EQ e, t ∉ X ∧ L.mem s (blockA t) = e ∧ Blocked (L.mem s (stA t))) ∧
    (∀ t ∈ T, t ∉ X → Blocked (L.mem s (stA t)) → L.mem s (blockA t) ∈ E ∧ t ∈ EQ (L.mem s (blockA t))) ∧
    EpTy st T X s E EQ H

def EpsOK (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (X : Set U64) (s : S) : Prop :=
  ∃ (E : Set U64) (EQ : U64 → List U64), EpsWit st T Cs Ω H X s E EQ

/-- `EpTy` only reads the states and block objects of the TCBs, the queue
lists and the state words of the objects. -/
theorem EpTy.agree {X X' : Set U64} {s s' : S} {E : Set U64} {EQ EQ' : U64 → List U64}
    (h : EpTy st T X s E EQ H) (hX : ∀ y, y ∉ X' → y ∉ X ∨ ¬ Blocked (L.mem s' (stA y)))
    (hsb : ∀ y ∈ T, y ∉ X' → Blocked (L.mem s' (stA y)) →
      L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y))
    (hq : ∀ e ∈ E, ∀ y ∈ EQ' e, y ∈ EQ e)
    (hqs : ∀ e ∈ E, ∀ y ∈ EQ' e, L.mem s' (stA y) = L.mem s (stA y))
    (hst : ∀ e ∈ E, EQ' e ≠ [] → L.epState s' e = L.epState s e)
    (hemp : ∀ e ∈ E, EQ' e = [] → (EQ e = [] ∧ L.epState s' e = L.epState s e) ∨
      ((H e = some .ep → L.epState s' e = 0#u64) ∧ (H e = some .ntfn → L.epState s' e ≠ 1#u64))) :
    EpTy st T X' s' E EQ' H := by
  obtain ⟨k1, k2, k0, k3, k4, k5⟩ := h
  have bl1 : ∀ v : U64, (v = sched.TS_BLOCKED_ON_SEND ∨ v = sched.TS_BLOCKED_ON_RECV) → Blocked v := by
    rintro v (e | e)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  refine ⟨fun y hy hyX hs => ?_, fun y hy hyX hs => ?_, k0, fun e he y hy z hz => ?_, fun e he y hy => ?_,
    fun e he h0 => ?_⟩
  rotate_right
  · rcases hemp e he h0 with ⟨h1, h2⟩ | h3
    · rw [h2]; exact k5 e he h1
    · exact h3
  · have hb := bl1 _ hs
    obtain ⟨e1, e2⟩ := hsb y hy hyX hb
    rcases hX y hyX with hx | hx
    · rw [e1] at hs; rw [e2]; exact k1 y hy hx hs
    · exact absurd hb hx
  · have hb : Blocked (L.mem s' (stA y)) := Or.inr (Or.inr hs)
    obtain ⟨e1, e2⟩ := hsb y hy hyX hb
    rcases hX y hyX with hx | hx
    · rw [e1] at hs; rw [e2]; exact k2 y hy hx hs
    · exact absurd hb hx
  · rw [hqs e he y hy, hqs e he z hz]; exact k3 e he y (hq e he y hy) z (hq e he z hz)
  · have hne : EQ' e ≠ [] := List.ne_nil_of_mem hy
    rw [hqs e he y hy, hst e he hne]; exact k4 e he y (hq e he y hy)

/-- The scheduler queues of all cores `Cs`, as ghost lists `Q c p` (ready
queue of priority `p` on core `c`) and `R c` (release queue of core `c`),
with the endpoint queues; `X` is a set of blocked threads that are
temporarily in no endpoint queue (empty in `SchedQueuesInv`). -/
structure SchedQueuesInvX (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (X : Set U64) (s : S)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) : Prop where
  tcbs : TcbPlaced T
  nodes : ∀ c ∈ Cs, NodePlaced st T s c
  cur : L.cpu s ∈ Cs
  aff : ∀ t ∈ T, L.mem s (affA t) ∈ Cs
  prio : ∀ t ∈ T, (L.mem s (prioA t)).val < 256
  ready : ∀ c ∈ Cs, ReadyQueues st T s c (Q c)
  release : ∀ c ∈ Cs, QueueRel (L.mem s) T .Sched (L.relQ s c) (R c)
  inQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → ∀ t ∈ Q c p, L.mem s (affA t) = c ∧ L.mem s (prioA t) = p
  inR : ∀ c ∈ Cs, ∀ t ∈ R c, L.mem s (affA t) = c
  queued : ∀ t ∈ T, ((L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ↔
    t ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)))
  released : ∀ t ∈ T, ((L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ↔ t ∈ R (L.mem s (affA t)))
  excl : ∀ t ∈ T, t ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)) → t ∉ R (L.mem s (affA t))
  /-- The current core's scheduler action is resume, choose-new, or a TCB
  (seL4 `valid_sched_action`, the part the queues need). -/
  action : L.actionW s = 0#u64 ∨ L.actionW s = 1#u64 ∨ L.actionW s ∈ T
  /-- Queued threads are runnable (seL4 `valid_queues`). -/
  runQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → ∀ t ∈ Q c p, Runnable (L.mem s (stA t))
  /-- Threads in a release queue are runnable (seL4 `valid_release_q`). -/
  runR : ∀ c ∈ Cs, ∀ t ∈ R c, Runnable (L.mem s (stA t))
  /-- A switch-to candidate is runnable and in no release queue (seL4
  `weak_valid_sched_action`). -/
  actOK : L.actionW s ∈ T → Runnable (L.mem s (stA (L.actionW s))) ∧ ∀ c ∈ Cs, L.actionW s ∉ R c
  eps : EpsOK st T Cs Ω H X s
  /-- The current and idle threads are TCBs. -/
  curT : L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ∈ T
  idleT : L.mem s (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD) ∈ T
  /-- The TCBs lie outside the kernel-global area below the nodes. -/
  ksOut : ∀ t ∈ T, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val
  /-- `Ω`, the words of the other kernel objects (scheduling contexts,
  replies, the kernel-global area), lies outside the TCBs and nodes. -/
  omega : ∀ a ∈ Ω, OutsideObjs st T Cs s a

/-- The invariant, with no exceptions. -/
abbrev SchedQueuesInv (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (s : S)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) : Prop :=
  SchedQueuesInvX st T Cs Ω H ∅ s Q R

namespace SchedQueuesInvX
variable {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem memT (h : SchedQueuesInvX st T Cs Ω H X s Q R) {c p : U64} (hc : c ∈ Cs) (hp : p.val < 256) {y : U64}
    (hy : y ∈ Q c p) : y ∈ T := ((h.ready c hc).1.rel p hp).mem y hy

theorem memTR (h : SchedQueuesInvX st T Cs Ω H X s Q R) {c : U64} (hc : c ∈ Cs) {y : U64} (hy : y ∈ R c) : y ∈ T :=
  (h.release c hc).mem y hy

/-- An unqueued thread is in no ready queue. -/
theorem notQ (h : SchedQueuesInvX st T Cs Ω H X s Q R) {t : U64} (ht : t ∈ T)
    (h0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) {c p : U64} (hc : c ∈ Cs) (hp : p.val < 256) :
    t ∉ Q c p := by
  intro hm
  obtain ⟨e1, e2⟩ := h.inQ c hc p hp t hm
  exact ((h.queued t ht).2 (by rw [e1, e2]; exact hm)) h0

/-- A thread not in the release state is in no release queue. -/
theorem notR (h : SchedQueuesInvX st T Cs Ω H X s Q R) {t : U64} (ht : t ∈ T)
    (h0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) {c : U64} (hc : c ∈ Cs) : t ∉ R c := by
  intro hm
  have e1 := h.inR c hc t hm
  exact ((h.released t ht).2 (by rw [e1]; exact hm)) h0

/-- Ready queues and release queues are disjoint. -/
theorem QR (h : SchedQueuesInvX st T Cs Ω H X s Q R) {c p : U64} (hc : c ∈ Cs) (hp : p.val < 256) {y : U64}
    (hy : y ∈ Q c p) {c' : U64} (hc' : c' ∈ Cs) : y ∉ R c' := by
  intro hr
  obtain ⟨e1, e2⟩ := h.inQ c hc p hp y hy
  have e3 := h.inR c' hc' y hr
  have hyT := h.memT hc hp hy
  apply h.excl y hyT
  · rw [e1, e2]; exact hy
  · rw [e3]; exact hr

end SchedQueuesInvX

theorem NodePlaced.ksb {s s' : S} {c : U64} (hN : NodePlaced st T s c) (hk : L.ksb s' = L.ksb s) :
    NodePlaced st T s' c := by
  have e : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  exact ⟨by rw [e]; exact hN.align, by rw [e]; exact hN.fits, by rw [e]; exact hN.disj⟩

/-! Membership in updated ghost lists. -/

theorem mem_upd2 {Q : U64 → U64 → List U64} {c p c' p' : U64} {xs : List U64} {y : U64} :
    y ∈ Function.update Q c (Function.update (Q c) p xs) c' p' ↔
      (c' = c ∧ p' = p ∧ y ∈ xs) ∨ (¬ (c' = c ∧ p' = p) ∧ y ∈ Q c' p') := by
  by_cases e1 : c' = c
  · subst e1
    by_cases e2 : p' = p
    · subst e2; simp
    · simp [Function.update_of_ne e2, e2]
  · simp [Function.update_of_ne e1, e1]

/-! ## Footprints and the new parts -/

theorem qfoot_out {Cs : Set U64} {s : S} {W : List U64} {c t : U64} {P : Nat → Prop} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s)) (ht : t ∈ T)
    (hc : c ∈ Cs) (hcur : L.cpu s ∈ Cs) {a : U64} (ha : OutsideObjs st T Cs s a) :
    ¬ L.QFoot s W c P t a := by
  obtain ⟨-, hat, han⟩ := ha
  rintro (⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩) <;> have hv := congrArg UScalar.val e
  · have := nextA_inside (hT w (hW w hw)) .Sched; have := hat w (hW w hw); omega
  · have := prevA_inside (hT w (hW w hw)) .Sched; have := hat w (hW w hw); omega
  · rw [nodeAt_val hN ho] at hv; have := han c hc; omega
  · rw [inqA_val (hT t ht)] at hv; have := hat t ht; omega
  · rw [nodeAt_val hN' ho] at hv; have := han _ hcur; omega

/-! ## The new parts under writes -/

theorem ep_out {Cs : Set U64} {s : S} {e : U64} (hE : EpPlaced T e) (hEN : EpOutNodes st Cs s e) :
    OutsideObjs st T Cs s (epHeadA e) ∧ OutsideObjs st T Cs s (epTSA e) := by
  obtain ⟨a1, a2⟩ := ep_aligned hE
  refine ⟨⟨a1, fun t ht => ?_, fun c hc => ?_⟩, ⟨a2, fun t ht => ?_, fun c hc => ?_⟩⟩ <;>
    simp only [epHeadA_val, epTSA_val hE]
  · have := hE.disj t ht; omega
  · have := hEN.1 c hc; omega
  · have := hE.disj t ht; omega
  · have := hEN.1 c hc; omega

/-- The endpoint queues only depend on the states, blocking objects and `Ep`
links of the TCBs, and on words outside the TCBs and nodes. -/
theorem EpsOK.agree {Cs X : Set U64} {s s' : S} (h : EpsOK st T Cs Ω H X s) (hk : L.ksb s' = L.ksb s)
    (hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y))
    (hEp : ∀ y ∈ T, L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) ∧ L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y))
    (hout : ∀ a, OutsideObjs st T Cs s a → L.mem s' a = L.mem s a) : EpsOK st T Cs Ω H X s' := by
  obtain ⟨E, EQ, h1, h2, h5, h3, h4, h6⟩ := h
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hk]
  refine ⟨E, EQ, fun e he => ?_, h2, h5, fun e he y hy => ?_, fun y hy hyX hb => ?_,
    h6.agree (fun y hy => Or.inl hy) (fun y hy _ _ => hsb y hy) (fun _ _ _ hy => hy)
      (fun e he y hy => (hsb y (((h1 e he).2.2).mem y hy)).1) (fun e he _ => ?_)
      (fun e he h0 => Or.inl ⟨h0, ?_⟩)⟩
  · obtain ⟨hE, hEN, hq⟩ := h1 e he
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    have eq : L.epQ s' e = L.epQ s e := by simp only [LawfulStore.epQ, hout _ o1, hout _ o2]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by rw [hk]; exact hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨(hEp y (hq.mem y hy)).2, (hEp y (hq.mem y hy)).1⟩⟩
  · have hyT := ((h1 e he).2.2).mem y hy
    rw [(hsb y hyT).1, (hsb y hyT).2]; exact h3 e he y hy
  · rw [(hsb y hy).1] at hb
    rw [(hsb y hy).2]; exact h4 y hy hyX hb
  · obtain ⟨hE, hEN, -⟩ := h1 e he
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState, hout _ o2]
  · obtain ⟨hE, hEN, -⟩ := h1 e he
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState, hout _ o2]

/-- `EpsOK` only reads the states and block objects of threads outside the
exception set. -/
theorem EpsOK.agreeX {Cs X : Set U64} {s s' : S} (h : EpsOK st T Cs Ω H X s) (hk : L.ksb s' = L.ksb s)
    (hsb : ∀ y ∈ T, y ∉ X → L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y))
    (hEp : ∀ y ∈ T, L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) ∧ L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y))
    (hout : ∀ a, OutsideObjs st T Cs s a → L.mem s' a = L.mem s a) : EpsOK st T Cs Ω H X s' := by
  obtain ⟨E, EQ, h1, h2, h5, h3, h4, h6⟩ := h
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hk]
  have mX : ∀ e ∈ E, ∀ y ∈ EQ e, y ∉ X := fun e he y hy => (h3 e he y hy).1
  refine ⟨E, EQ, fun e he => ?_, h2, h5, fun e he y hy => ?_, fun y hy hyX hb => ?_,
    h6.agree (fun y hy => Or.inl hy) (fun y hy hyX _ => hsb y hy hyX) (fun _ _ _ hy => hy)
      (fun e he y hy => (hsb y (((h1 e he).2.2).mem y hy) (mX e he y hy)).1) (fun e he _ => ?_)
      (fun e he h0 => Or.inl ⟨h0, ?_⟩)⟩
  · obtain ⟨hE, hEN, hq⟩ := h1 e he
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    have eq : L.epQ s' e = L.epQ s e := by simp only [LawfulStore.epQ, hout _ o1, hout _ o2]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by rw [hk]; exact hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨(hEp y (hq.mem y hy)).2, (hEp y (hq.mem y hy)).1⟩⟩
  · have hyT := ((h1 e he).2.2).mem y hy
    rw [(hsb y hyT (mX e he y hy)).1, (hsb y hyT (mX e he y hy)).2]; exact h3 e he y hy
  · rw [(hsb y hy hyX).1] at hb
    rw [(hsb y hy hyX).2]; exact h4 y hy hyX hb
  · obtain ⟨hE, hEN, -⟩ := h1 e he
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState, hout _ o2]
  · obtain ⟨hE, hEN, -⟩ := h1 e he
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState, hout _ o2]

/-- What a queue operation's footprint leaves of the new parts. -/
theorem ext_qfoot {Cs : Set U64} {s s' : S} {W : List U64} {c t : U64} {P : Nat → Prop} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s)) (ht : t ∈ T)
    (hc : c ∈ Cs) (hcur : L.cpu s ∈ Cs) (hw : WritesIn st s s' (L.QFoot s W c P t)) :
    (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y)) ∧
    (∀ y ∈ T, L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) ∧ L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y)) ∧
    (∀ a, OutsideObjs st T Cs s a → L.mem s' a = L.mem s a) := by
  refine ⟨fun y hy => ⟨?_, ?_⟩, fun y hy => ?_, fun a ha => hw.mem_eq ha.1 (qfoot_out hT hW hN hN' ht hc hcur ha)⟩
  · rw [stA_eq]; exact field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp)
  · exact field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp)
  · have hk := qfoot_link hT hW hN hN' ht hy .Ep (P := P) (fun h => by cases h)
    exact ⟨hw.mem_eq (nextA_aligned (hT y hy) _) hk.1, hw.mem_eq (prevA_aligned (hT y hy) _) hk.2⟩

/-! ## A step on one ready queue -/

/-- The invariant after an operation that replaces the ready queue `(c, p)`
of thread `t` by `xs'` (which holds `t` iff `tIn`, and otherwise the old
members), touching only the footprint `QFoot` of `W` (old members and `t`). -/
theorem inv_ready_step {Cs : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {t c p : U64} {W xs' : List U64} {tIn : Prop}
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hca : L.mem s (affA t) = c) (hpa : L.mem s (prioA t) = p)
    (hW1 : ∀ w ∈ W, w = t ∨ w ∈ Q c p) (hWt : t ∈ W → ∀ c' ∈ Cs, t ∉ R c')
    (hw : WritesIn st s s' (L.QFoot s W c (128 ≤ ·) t))
    (hRc : ReadyQueues st T s' c (Function.update (Q c) p xs'))
    (hmem : ∀ y, y ∈ xs' ↔ (y = t ∧ tIn) ∨ (y ≠ t ∧ y ∈ Q c p))
    (hqq : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ↔ tIn)
    (hqr : L.mem s' (inqA t) &&& sched.Q_RELEASE = L.mem s (inqA t) &&& sched.Q_RELEASE)
    (hnr : tIn → t ∉ R c) (hrun : tIn → Runnable (L.mem s (stA t))) :
    SchedQueuesInvX st T Cs Ω H X s' (Function.update Q c (Function.update (Q c) p xs')) R := by
  have hT := h.tcbs
  have hc : c ∈ Cs := hca ▸ h.aff t ht
  have hp : p.val < 256 := hpa ▸ h.prio t ht
  have hN := h.nodes c hc
  have hN' := h.nodes _ h.cur
  have hW : ∀ w ∈ W, w ∈ T := fun w hw' => by
    rcases hW1 w hw' with rfl | hq
    · exact ht
    · exact h.memT hc hp hq
  have haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => aff_qfoot hT hW hN hN' ht hw hy
  have hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy => prio_qfoot hT hW hN hN' ht hw hy
  have hinq : ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) :=
    fun y hy hyt => inq_qfoot hT hW hN hN' ht hw hy hyt
  -- Members of other queues are outside `W`.
  have hWQ : ∀ c' ∈ Cs, c' ≠ c → ∀ p' : U64, p'.val < 256 → ∀ y ∈ Q c' p', y ∉ W := by
    intro c' hc' hne p' hp' y hy hyW
    have e := (h.inQ c' hc' p' hp' y hy).1
    rcases hW1 y hyW with rfl | hq
    · exact hne (e.symm.trans hca)
    · exact hne (e.symm.trans (h.inQ c hc p hp y hq).1)
  have hWR : ∀ c' ∈ Cs, ∀ y ∈ R c', y ∉ W := by
    intro c' hc' y hy hyW
    rcases hW1 y hyW with rfl | hq
    · exact hWt hyW c' hc' hy
    · exact h.QR hc hp hq hc' hy
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw.2.1]
    exact node_qfoot hT hW hN hN' ht hw hN' (by rw [act_val]; omega) (by rw [act_val])
      (fun _ => by rw [act_val]; simp [RelOffs]) (fun _ => by rw [act_val]; omega)
  obtain ⟨hsb, hEp, hout⟩ := ext_qfoot hT hW hN hN' ht hc h.cur hw
  refine ⟨hT, fun c' hc' => (h.nodes c' hc').ksb hw.1, hw.2.1 ▸ h.cur, fun y hy => (haff y hy) ▸ h.aff y hy,
    fun y hy => (hprio y hy) ▸ h.prio y hy, fun c' hc' => ?_, fun c' hc' => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, h.eps.agree hw.1 hsb hEp hout, ?_, ?_, by rw [hw.1]; exact h.ksOut,
    fun a ha => (h.omega a ha).ksb hw.1⟩
  · by_cases e : c' = c
    · subst e; rw [Function.update_self]; exact hRc
    · rw [Function.update_of_ne e]
      exact (h.ready c' hc').qfoot hT hW hN hN' ht hw (h.nodes c' hc') (fun e' => absurd e' e)
        (hWQ c' hc' e)
  · rw [relQ_qfoot hT hW hN hN' ht hw (h.nodes c' hc') (fun _ => by omega)]
    exact (h.release c' hc').qfoot hT hW hN hN' ht hw (fun _ => hWR c' hc')
  · intro c' hc' p' hp' y hy
    rcases mem_upd2.1 hy with ⟨rfl, rfl, hy'⟩ | ⟨-, hy'⟩
    · rcases (hmem y).1 hy' with ⟨rfl, -⟩ | ⟨-, hq⟩
      · exact ⟨(haff y ht).trans hca, (hprio y ht).trans hpa⟩
      · have := h.inQ c' hc p' hp y hq
        exact ⟨(haff y (h.memT hc hp hq)).trans this.1, (hprio y (h.memT hc hp hq)).trans this.2⟩
    · have := h.inQ c' hc' p' hp' y hy'
      exact ⟨(haff y (h.memT hc' hp' hy')).trans this.1, (hprio y (h.memT hc' hp' hy')).trans this.2⟩
  · intro c' hc' y hy
    exact (haff y (h.memTR hc' hy)).trans (h.inR c' hc' y hy)
  · intro y hy
    rw [haff y hy, hprio y hy]
    by_cases e : y = t
    · subst e
      rw [hqq, hca, hpa, Function.update_self, Function.update_self, hmem]
      simp
    · rw [hinq y hy e, h.queued y hy, mem_upd2]
      constructor
      · intro hq
        by_cases e2 : L.mem s (affA y) = c ∧ L.mem s (prioA y) = p
        · obtain ⟨e3, e4⟩ := e2
          left; refine ⟨e3, e4, (hmem y).2 (Or.inr ⟨e, ?_⟩)⟩
          rw [← e3, ← e4]; exact hq
        · exact Or.inr ⟨e2, hq⟩
      · rintro (⟨e3, e4, hq⟩ | ⟨-, hq⟩)
        · rcases (hmem y).1 hq with ⟨e5, -⟩ | ⟨-, hq'⟩
          · exact absurd e5 e
          · rw [e3, e4]; exact hq'
        · exact hq
  · intro y hy
    rw [haff y hy]
    by_cases e : y = t
    · subst e; rw [hqr]; exact h.released y hy
    · rw [hinq y hy e]; exact h.released y hy
  · intro y hy hq
    rw [haff y hy] at hq ⊢
    rw [hprio y hy] at hq
    rcases mem_upd2.1 hq with ⟨e3, e4, hq'⟩ | ⟨e3, hq'⟩
    · rcases (hmem y).1 hq' with ⟨rfl, hin⟩ | ⟨-, hq''⟩
      · rw [e3]; exact hnr hin
      · exact h.excl y hy (by rw [e3, e4]; exact hq'')
    · exact h.excl y hy hq'
  · rw [hact]; exact h.action
  · intro c' hc' p' hp' y hy
    rw [(hsb y (by
      rcases mem_upd2.1 hy with ⟨rfl, rfl, hy'⟩ | ⟨-, hy'⟩
      · rcases (hmem y).1 hy' with ⟨rfl, -⟩ | ⟨-, hq⟩
        · exact ht
        · exact h.memT hc hp hq
      · exact h.memT hc' hp' hy')).1]
    rcases mem_upd2.1 hy with ⟨rfl, rfl, hy'⟩ | ⟨-, hy'⟩
    · rcases (hmem y).1 hy' with ⟨rfl, hin⟩ | ⟨-, hq⟩
      · exact hrun hin
      · exact h.runQ c' hc p' hp y hq
    · exact h.runQ c' hc' p' hp' y hy'
  · intro c' hc' y hy
    rw [(hsb y (h.memTR hc' hy)).1]; exact h.runR c' hc' y hy
  · rw [hact]; intro haT
    rw [(hsb _ haT).1]; exact h.actOK haT
  · rw [hw.2.1, node_qfoot hT hW hN hN' ht hw hN' (by rw [curth0]; omega) (by rw [curth0])
      (fun _ => by rw [curth0]; simp [RelOffs]) (fun _ => by rw [curth0]; omega)]
    exact h.curT
  · rw [hw.2.1, node_qfoot hT hW hN hN' ht hw hN' (by rw [idle8]; omega) (by rw [idle8])
      (fun _ => by rw [idle8]; simp [RelOffs]) (fun _ => by rw [idle8]; omega)]
    exact h.idleT

/-! ## `enqueue` and `dequeue` -/

/-- `tcbSchedEnqueue` preserves the invariant, for a thread that is queued
already or not in the release queue (seL4's precondition). -/
theorem sched.enqueue.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem s (stA t))) :
    sched.enqueue st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s'
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
         (t :: Q (L.mem s (affA t)) (L.mem s (prioA t))))) R ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have h1 := sched.enqueue.ready s t _ hT ht hp hN hN' hR1 (fun h0 p hp => h.notQ ht h0 hc hp)
  have h2 := sched.enqueue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) (fun h0 => h.notQ ht h0 hc hp)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · rw [if_pos hqd] at hRc hinq ⊢
    have htq := (h.queued t ht).1 hqd
    have := inv_ready_step (W := t :: Q _ _) (xs' := Q (L.mem s (affA t)) (L.mem s (prioA t))) (tIn := True)
      h ht rfl rfl (fun w hw => List.mem_cons.1 hw)
      (fun _ c' hc' hm => h.QR hc hp htq hc' hm) hw (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq]) (by rw [hinq]; simpa using hqd) (by rw [hinq])
      (fun _ => h.QR hc hp htq hc) (fun _ => h.runQ _ hc _ hp t htq)
    simpa [Function.update_eq_self] using this
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    rw [if_neg hqd] at hRc hinq ⊢
    have htq := h.notQ ht hq0 hc hp
    exact inv_ready_step (W := t :: Q _ _) (tIn := True) h ht rfl rfl (fun w hw => List.mem_cons.1 hw)
      (fun _ c' hc' => h.notR ht (hr hq0) hc') hw hRc
      (fun y => by by_cases e : y = t <;> simp [e])
      (by rw [hinq, or_qq_qq]; simpa using qq_ne) (by rw [hinq, or_qq_qr])
      (fun _ => h.notR ht (hr hq0) hc) (fun _ => hrun hq0)

/-- `tcbSchedDequeue` preserves the invariant. -/
theorem sched.dequeue.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s'
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
         ((Q (L.mem s (affA t)) (L.mem s (prioA t))).erase t)) else Q) R ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have hmemq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → t ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)) :=
    (h.queued t ht).1
  have h1 := sched.dequeue.ready s t _ hT ht hp hN hR1 hmemq
  have h2 := sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  have hnd := (hR1.1.rel _ hp).nodup
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · rw [if_pos hqd] at hRc hinq ⊢
    have htq := hmemq hqd
    exact inv_ready_step (W := Q _ _) (tIn := False) h ht rfl rfl (fun w hw => Or.inr hw)
      (fun htW c' hc' hm => h.QR hc hp htW hc' hm) hw hRc
      (fun y => by rw [hnd.mem_erase_iff]; simp [and_comm])
      (by rw [hinq, andn_qq_qq]; simp) (by rw [hinq, andn_qq_qr]) (fun h => h.elim) (fun h => h.elim)
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    rw [if_neg hqd] at hRc hinq ⊢
    have htq := h.notQ ht hq0 hc hp
    have := inv_ready_step (W := Q _ _) (xs' := Q (L.mem s (affA t)) (L.mem s (prioA t))) (tIn := False)
      h ht rfl rfl (fun w hw => Or.inr hw) (fun htW => absurd htW htq) hw
      (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq])
      (by rw [hinq]; exact iff_false_intro (not_not.2 hq0)) (by rw [hinq]) (fun h => h.elim) (fun h => h.elim)
    simpa [Function.update_eq_self] using this

/-! ## A step on one release queue -/

theorem mem_relIns {rt : U64 → U64} {nt t : U64} {xs : List U64} {y : U64} :
    y ∈ relIns rt nt t xs ↔ y = t ∨ y ∈ xs := by
  unfold relIns
  split
  · simp [or_comm]
  · conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun y => decide (rt y ≤ nt)) (l := xs)]
    simp only [List.mem_append, List.mem_cons]; tauto

theorem mem_upd1 {R : U64 → List U64} {c c' : U64} {ys : List U64} {y : U64} :
    y ∈ Function.update R c ys c' ↔ (c' = c ∧ y ∈ ys) ∨ (c' ≠ c ∧ y ∈ R c') := by
  by_cases e : c' = c
  · subst e; simp
  · simp [Function.update_of_ne e, e]

/-- The invariant after an operation that replaces the release queue of
thread `t`'s core `c` by `ys'` (which holds `t` iff `tIn`, and otherwise the
old members), touching only the footprint `QFoot` of `W`. -/
theorem inv_release_step {Cs : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {t c : U64} {W ys' : List U64} {tIn : Prop}
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hca : L.mem s (affA t) = c)
    (hW1 : ∀ w ∈ W, w = t ∨ w ∈ R c) (hWt : t ∈ W → ∀ c' ∈ Cs, ∀ p' : U64, p'.val < 256 → t ∉ Q c' p')
    (hw : WritesIn st s s' (L.QFoot s W c RelOffs t))
    (hRc : QueueRel (L.mem s') T .Sched (L.relQ s' c) ys')
    (hmem : ∀ y, y ∈ ys' ↔ (y = t ∧ tIn) ∨ (y ≠ t ∧ y ∈ R c))
    (hqr : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ↔ tIn)
    (hqq : L.mem s' (inqA t) &&& sched.Q_QUEUED = L.mem s (inqA t) &&& sched.Q_QUEUED)
    (hnq : tIn → t ∉ Q c (L.mem s (prioA t))) (hrun : tIn → Runnable (L.mem s (stA t)))
    (hna : tIn → L.actionW s ≠ t) :
    SchedQueuesInvX st T Cs Ω H X s' Q (Function.update R c ys') := by
  have hT := h.tcbs
  have hc : c ∈ Cs := hca ▸ h.aff t ht
  have hN := h.nodes c hc
  have hN' := h.nodes _ h.cur
  have hW : ∀ w ∈ W, w ∈ T := fun w hw' => by
    rcases hW1 w hw' with rfl | hq
    · exact ht
    · exact h.memTR hc hq
  have haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => aff_qfoot hT hW hN hN' ht hw hy
  have hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy => prio_qfoot hT hW hN hN' ht hw hy
  have hinq : ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) :=
    fun y hy hyt => inq_qfoot hT hW hN hN' ht hw hy hyt
  have hWQ : ∀ c' ∈ Cs, ∀ p' : U64, p'.val < 256 → ∀ y ∈ Q c' p', y ∉ W := by
    intro c' hc' p' hp' y hy hyW
    rcases hW1 y hyW with rfl | hq
    · exact hWt hyW c' hc' p' hp' hy
    · exact h.QR hc' hp' hy hc hq
  have hWR : ∀ c' ∈ Cs, c' ≠ c → ∀ y ∈ R c', y ∉ W := by
    intro c' hc' hne y hy hyW
    have e := h.inR c' hc' y hy
    rcases hW1 y hyW with rfl | hq
    · exact hne (e.symm.trans hca)
    · exact hne (e.symm.trans (h.inR c hc y hq))
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw.2.1]
    exact node_qfoot hT hW hN hN' ht hw hN' (by rw [act_val]; omega) (by rw [act_val])
      (fun _ => by rw [act_val]; simp [RelOffs]) (fun _ => by rw [act_val]; omega)
  obtain ⟨hsb, hEp, hout⟩ := ext_qfoot hT hW hN hN' ht hc h.cur hw
  refine ⟨hT, fun c' hc' => (h.nodes c' hc').ksb hw.1, hw.2.1 ▸ h.cur, fun y hy => (haff y hy) ▸ h.aff y hy,
    fun y hy => (hprio y hy) ▸ h.prio y hy, fun c' hc' => ?_, fun c' hc' => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, h.eps.agree hw.1 hsb hEp hout, ?_, ?_, by rw [hw.1]; exact h.ksOut,
    fun a ha => (h.omega a ha).ksb hw.1⟩
  · exact (h.ready c' hc').qfoot hT hW hN hN' ht hw (h.nodes c' hc')
      (fun _ o ho _ => by simp only [RelOffs]; omega) (hWQ c' hc')
  · by_cases e : c' = c
    · subst e; rw [Function.update_self]; exact hRc
    · rw [Function.update_of_ne e, relQ_qfoot hT hW hN hN' ht hw (h.nodes c' hc') (fun e' => absurd e' e)]
      exact (h.release c' hc').qfoot hT hW hN hN' ht hw (fun _ => hWR c' hc' e)
  · intro c' hc' p' hp' y hy
    have := h.inQ c' hc' p' hp' y hy
    exact ⟨(haff y (h.memT hc' hp' hy)).trans this.1, (hprio y (h.memT hc' hp' hy)).trans this.2⟩
  · intro c' hc' y hy
    rcases mem_upd1.1 hy with ⟨rfl, hy'⟩ | ⟨-, hy'⟩
    · rcases (hmem y).1 hy' with ⟨rfl, -⟩ | ⟨-, hq⟩
      · exact (haff y ht).trans hca
      · exact (haff y (h.memTR hc hq)).trans (h.inR c' hc y hq)
    · exact (haff y (h.memTR hc' hy')).trans (h.inR c' hc' y hy')
  · intro y hy
    rw [haff y hy, hprio y hy]
    by_cases e : y = t
    · subst e; rw [hqq]; exact h.queued y hy
    · rw [hinq y hy e]; exact h.queued y hy
  · intro y hy
    rw [haff y hy]
    by_cases e : y = t
    · subst e
      rw [hqr, hca, Function.update_self, hmem]
      simp
    · rw [hinq y hy e, h.released y hy, mem_upd1]
      constructor
      · intro hq
        by_cases e2 : L.mem s (affA y) = c
        · left; refine ⟨e2, (hmem y).2 (Or.inr ⟨e, ?_⟩)⟩
          rw [← e2]; exact hq
        · exact Or.inr ⟨e2, hq⟩
      · rintro (⟨e3, hq⟩ | ⟨-, hq⟩)
        · rcases (hmem y).1 hq with ⟨e5, -⟩ | ⟨-, hq'⟩
          · exact absurd e5 e
          · rw [e3]; exact hq'
        · exact hq
  · intro y hy hq hr
    rw [haff y hy, hprio y hy] at hq
    rw [haff y hy] at hr
    rcases mem_upd1.1 hr with ⟨e3, hr'⟩ | ⟨-, hr'⟩
    · rcases (hmem y).1 hr' with ⟨rfl, hin⟩ | ⟨-, hr''⟩
      · rw [hca] at hq; exact hnq hin hq
      · exact h.excl y hy hq (by rw [e3]; exact hr'')
    · exact h.excl y hy hq hr'
  · rw [hact]; exact h.action
  · intro c' hc' p' hp' y hy
    rw [(hsb y (h.memT hc' hp' hy)).1]; exact h.runQ c' hc' p' hp' y hy
  · intro c' hc' y hy
    rcases mem_upd1.1 hy with ⟨rfl, hy'⟩ | ⟨-, hy'⟩
    · rcases (hmem y).1 hy' with ⟨rfl, hin⟩ | ⟨-, hq⟩
      · rw [(hsb y ht).1]; exact hrun hin
      · rw [(hsb y (h.memTR hc hq)).1]; exact h.runR _ hc y hq
    · rw [(hsb y (h.memTR hc' hy')).1]; exact h.runR c' hc' y hy'
  · rw [hact]; intro haT
    rw [(hsb _ haT).1]
    refine ⟨(h.actOK haT).1, fun c' hc' hm => ?_⟩
    rcases mem_upd1.1 hm with ⟨rfl, hy'⟩ | ⟨-, hy'⟩
    · rcases (hmem _).1 hy' with ⟨e, hin⟩ | ⟨-, hq⟩
      · exact hna hin e
      · exact (h.actOK haT).2 _ hc hq
    · exact (h.actOK haT).2 c' hc' hy'
  · rw [hw.2.1, node_qfoot hT hW hN hN' ht hw hN' (by rw [curth0]; omega) (by rw [curth0])
      (fun _ => by rw [curth0]; simp [RelOffs]) (fun _ => by rw [curth0]; omega)]
    exact h.curT
  · rw [hw.2.1, node_qfoot hT hW hN hN' ht hw hN' (by rw [idle8]; omega) (by rw [idle8])
      (fun _ => by rw [idle8]; simp [RelOffs]) (fun _ => by rw [idle8]; omega)]
    exact h.idleT

/-! ## `release_enqueue` and `release_remove` -/

/-- `tcbReleaseEnqueue` preserves the invariant, for a thread in neither a
ready queue nor a release queue (seL4's precondition). -/
theorem sched.release_enqueue.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : Runnable (L.mem s (stA t))) (hna : L.actionW s ≠ t) :
    sched.release_enqueue st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q
      (Function.update R (L.mem s (affA t)) (relIns (L.rtime s) (L.rtime s t) t (R (L.mem s (affA t))))) ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hn := h.notR ht hr0 hc
  have h1 := sched.release_enqueue.rel s t _ hT ht hn hN hN' (h.release _ hc)
  have h2 := sched.release_enqueue.foot s t _ hT ht hn hN hN' (h.release _ hc)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  exact inv_release_step (W := t :: R _) (tIn := True) h ht rfl (fun w hw => List.mem_cons.1 hw)
    (fun _ c' hc' p' hp' => h.notQ ht hq0 hc' hp') hw hRc
    (fun y => by rw [mem_relIns]; by_cases e : y = t <;> simp [e])
    (by rw [hinq, or_qr_qr]; simpa using qr_ne) (by rw [hinq, or_qr_qq])
    (fun _ => h.notQ ht hq0 hc (h.prio t ht)) (fun _ => hrun) (fun _ => hna)

/-- `tcbReleaseRemove` preserves the invariant. -/
theorem sched.release_remove.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q
      (if (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
       then Function.update R (L.mem s (affA t)) ((R (L.mem s (affA t))).erase t) else R) ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hmemr : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → t ∈ R (L.mem s (affA t)) := (h.released t ht).1
  have h1 := sched.release_remove.rel s t _ hT ht hN (h.release _ hc) hmemr
  have h2 := sched.release_remove.foot s t _ hT ht hN hN' (h.release _ hc) hmemr
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  have hnd := (h.release _ hc).nodup
  have hWt : t ∈ R (L.mem s (affA t)) → ∀ c' ∈ Cs, ∀ p' : U64, p'.val < 256 → t ∉ Q c' p' :=
    fun htR c' hc' p' hp' hq => h.QR hc' hp' hq hc htR
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
  · rw [if_pos hqd] at hRc hinq ⊢
    exact inv_release_step (W := R _) (tIn := False) h ht rfl (fun w hw => Or.inr hw) hWt hw hRc
      (fun y => by rw [hnd.mem_erase_iff]; simp [and_comm])
      (by rw [hinq, andn_qr_qr]; simp) (by rw [hinq, andn_qr_qq]) (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
  · have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := not_not.1 hqd
    rw [if_neg hqd] at hRc hinq ⊢
    have htr := h.notR ht hr0 hc
    have := inv_release_step (W := R _) (ys' := R (L.mem s (affA t))) (tIn := False) h ht rfl
      (fun w hw => Or.inr hw) hWt hw hRc
      (fun y => by by_cases e : y = t <;> simp [e, htr])
      (by rw [hinq]; exact iff_false_intro (not_not.2 hr0)) (by rw [hinq]) (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
    simpa [Function.update_eq_self] using this

/-! ## Ready times in the post-state (SC placement) -/

/-- The words `ready_time` reads from thread `y`'s scheduling context (its
refill head index and the head refill's time) lie outside the TCBs and the
nodes: the SC placement hypothesis. -/
def ScOutside (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) (y : U64) : Prop :=
  OutsideObjs st T Cs s (headA (L.mem s (scA y))) ∧
    OutsideObjs st T Cs s (rtA (L.mem s (scA y)) (L.rhead s (L.mem s (scA y))))

/-- Ready times survive a queue operation, for threads whose SC words are
outside the TCBs and nodes. -/
theorem rtime_qfoot {Cs : Set U64} {s s' : S} {W : List U64} {c t : U64} {P : Nat → Prop} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s)) (ht : t ∈ T)
    (hc : c ∈ Cs) (hcur : L.cpu s ∈ Cs) (hw : WritesIn st s s' (L.QFoot s W c P t)) {y : U64} (hy : y ∈ T)
    (hsc : ScOutside st T Cs s y) : L.rtime s' y = L.rtime s y := by
  unfold LawfulStore.rtime
  rw [sc_qfoot hT hW hN hN' ht hw hy]
  have h1 : L.rhead s' (L.mem s (scA y)) = L.rhead s (L.mem s (scA y)) :=
    hw.mem_eq hsc.1.1 (qfoot_out hT hW hN hN' ht hc hcur hsc.1)
  simp only [LawfulStore.refill, h1]
  exact hw.mem_eq hsc.2.1 (qfoot_out hT hW hN hN' ht hc hcur hsc.2)

/-- `release_enqueue` keeps the release queue sorted by the ready times of
the state it leaves, for threads whose SC words lie outside the TCBs and
nodes. -/
theorem sched.release_enqueue.sorted_post {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hs : TimeSorted (L.rtime s) (R (L.mem s (affA t))))
    (hsc : ∀ y ∈ t :: R (L.mem s (affA t)), ScOutside st T Cs s y) :
    sched.release_enqueue st s t ⦃ s' => ∃ ys, QueueRel (L.mem s') T .Sched (L.relQ s' (L.mem s (affA t))) ys ∧
      TimeSorted (L.rtime s') ys ∧ ys.Perm (t :: R (L.mem s (affA t))) ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hn := h.notR ht hr0 hc
  have hW : ∀ w ∈ t :: R (L.mem s (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h.memTR hc hw
  have h1 := sched.release_enqueue.sorted s t _ hT ht hn hN hN' (h.release _ hc) hs
  have h2 := sched.release_enqueue.foot s t _ hT ht hn hN hN' (h.release _ hc)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨⟨ys, hq, hsrt, hperm⟩, hw, -⟩
  refine ⟨ys, hq, List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hsrt, hperm⟩
  have ha' := hperm.subset ha
  have hb' := hperm.subset hb
  rw [rtime_qfoot hT hW hN hN' ht hc h.cur hw (hW a ha') (hsc a ha'),
    rtime_qfoot hT hW hN hN' ht hc h.cur hw (hW b hb') (hsc b hb')]
  exact hab

/-! ## Writes away from the queues -/

/-- The invariant survives any change that keeps the `Sched` links, the
node words from the release queue up, and the `IN_QUEUES`/affinity fields of
the TCBs, and changes priorities only of threads in no ready queue. -/
theorem inv_of_agree' {Cs : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {X X' : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hk : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hlink : ∀ y ∈ T, L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) ∧
      L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y))
    (hnode : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 128 ≤ o.val) →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o))
    (hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y))
    (haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y))
    (hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) ∨
      ((L.mem s (inqA y) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s' (prioA y)).val < 256))
    (hact : L.actionW s' = 0#u64 ∨ L.actionW s' = 1#u64 ∨ L.actionW s' ∈ T)
    (hrq : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → ∀ t ∈ Q c p, Runnable (L.mem s' (stA t)))
    (hrr : ∀ c ∈ Cs, ∀ t ∈ R c, Runnable (L.mem s' (stA t)))
    (hact2 : L.actionW s' ∈ T → Runnable (L.mem s' (stA (L.actionW s'))) ∧ ∀ c ∈ Cs, L.actionW s' ∉ R c)
    (heps : EpsOK st T Cs Ω H X' s')
    (hcurT : L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) ∈ T)
    (hidleT : L.mem s' (L.nodeAt s' (L.cpu s') layout.node.IDLE_THREAD) ∈ T) :
    SchedQueuesInvX st T Cs Ω H X' s' Q R := by
  have hT := h.tcbs
  have hn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 128 ≤ o.val) →
      L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o h1 h2 h3; rw [nodeAt_of_ksb hk]; exact hnode c hc o h1 h2 h3
  have hle : ∀ y ∈ T, ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → y ∈ Q c p → L.mem s' (prioA y) = L.mem s (prioA y) := by
    intro y hy c hc p hp hq
    rcases hprio y hy with e | ⟨h0, -⟩
    · exact e
    · exact absurd hq (h.notQ hy h0 hc hp)
  have hrel : ∀ {q xs}, QueueRel (L.mem s) T .Sched q xs → QueueRel (L.mem s') T .Sched q xs := fun hq =>
    ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨(hlink y (hq.mem y hy)).2, (hlink y (hq.mem y hy)).1⟩⟩
  refine ⟨hT, fun c hc => (h.nodes c hc).ksb hk, hcpu ▸ h.cur, fun y hy => (haff y hy) ▸ h.aff y hy,
    fun y hy => ?_, fun c hc => ?_, fun c hc => ?_, ?_, ?_, ?_, ?_, ?_, hact,
    hrq, hrr, hact2, heps, hcurT, hidleT, by rw [hk]; exact h.ksOut,
    fun a ha => (h.omega a ha).ksb hk⟩
  · rcases hprio y hy with e | ⟨-, hlt⟩
    · rw [e]; exact h.prio y hy
    · exact hlt
  · have hNc := h.nodes c hc
    have hv : ViewsEq st s s' c := by
      refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
      · simp only [LawfulStore.rqQ]
        rw [hn c hc _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
          hn c hc _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
            (by rw [rqTailOff_val hp]; omega)]
      · exact hn c hc _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
      · exact hn c hc _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    refine ⟨(h.ready c hc).1.agree hv.1 fun p hp y hy => ?_, (h.ready c hc).2.views hv⟩
    exact hlink y (((h.ready c hc).1.rel p hp).mem y hy)
  · have e : L.relQ s' c = L.relQ s c := by
      simp only [LawfulStore.relQ]
      rw [hn c hc _ (by rw [relh_val]; omega) (by rw [relh_val]) (by rw [relh_val]; simp),
        hn c hc _ (by rw [relt_val]; omega) (by rw [relt_val]) (by rw [relt_val]; omega)]
    rw [e]; exact hrel (h.release c hc)
  · intro c hc p hp y hy
    have := h.inQ c hc p hp y hy
    have hyT := h.memT hc hp hy
    exact ⟨(haff y hyT).trans this.1, (hle y hyT c hc p hp hy).trans this.2⟩
  · intro c hc y hy
    exact (haff y (h.memTR hc hy)).trans (h.inR c hc y hy)
  · intro y hy
    rw [hinq y hy, haff y hy]
    rcases hprio y hy with e | ⟨h0, hlt⟩
    · rw [e]; exact h.queued y hy
    · constructor
      · intro h1; exact absurd h0 h1
      · intro h1; exact absurd h1 (h.notQ hy h0 (h.aff y hy) hlt)
  · intro y hy
    rw [hinq y hy, haff y hy]; exact h.released y hy
  · intro y hy hq
    rw [haff y hy] at hq ⊢
    rcases hprio y hy with e | ⟨h0, hlt⟩
    · rw [e] at hq; exact h.excl y hy hq
    · exact absurd hq (h.notQ hy h0 (h.aff y hy) hlt)


/-- The invariant survives any change that keeps the `Sched` links, the
node words from the release queue up, and the `IN_QUEUES`/affinity fields of
the TCBs, and changes priorities only of threads in no ready queue. -/
theorem inv_of_agree {Cs : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {X X' : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hk : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hlink : ∀ y ∈ T, L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) ∧
      L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y))
    (hnode : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 128 ≤ o.val) →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o))
    (hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y))
    (haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y))
    (hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) ∨
      ((L.mem s (inqA y) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s' (prioA y)).val < 256))
    (hact : L.actionW s' = 0#u64 ∨ L.actionW s' = 1#u64 ∨ L.actionW s' ∈ T)
    (hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y))
    (hact2 : L.actionW s' ∈ T → Runnable (L.mem s' (stA (L.actionW s'))) ∧ ∀ c ∈ Cs, L.actionW s' ∉ R c)
    (heps : EpsOK st T Cs Ω H X' s')
    (hcurT : L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) ∈ T)
    (hidleT : L.mem s' (L.nodeAt s' (L.cpu s') layout.node.IDLE_THREAD) ∈ T) :
    SchedQueuesInvX st T Cs Ω H X' s' Q R := by
  have hT := h.tcbs
  have hn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (o.val = 64 ∨ o.val = 72 ∨ 128 ≤ o.val) →
      L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o h1 h2 h3; rw [nodeAt_of_ksb hk]; exact hnode c hc o h1 h2 h3
  have hle : ∀ y ∈ T, ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → y ∈ Q c p → L.mem s' (prioA y) = L.mem s (prioA y) := by
    intro y hy c hc p hp hq
    rcases hprio y hy with e | ⟨h0, -⟩
    · exact e
    · exact absurd hq (h.notQ hy h0 hc hp)
  have hrel : ∀ {q xs}, QueueRel (L.mem s) T .Sched q xs → QueueRel (L.mem s') T .Sched q xs := fun hq =>
    ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨(hlink y (hq.mem y hy)).2, (hlink y (hq.mem y hy)).1⟩⟩
  refine ⟨hT, fun c hc => (h.nodes c hc).ksb hk, hcpu ▸ h.cur, fun y hy => (haff y hy) ▸ h.aff y hy,
    fun y hy => ?_, fun c hc => ?_, fun c hc => ?_, ?_, ?_, ?_, ?_, ?_, hact,
    fun c hc p hp y hy => by rw [(hsb y (h.memT hc hp hy)).1]; exact h.runQ c hc p hp y hy,
    fun c hc y hy => by rw [(hsb y (h.memTR hc hy)).1]; exact h.runR c hc y hy,
    hact2, heps, hcurT, hidleT, by rw [hk]; exact h.ksOut,
    fun a ha => (h.omega a ha).ksb hk⟩
  · rcases hprio y hy with e | ⟨-, hlt⟩
    · rw [e]; exact h.prio y hy
    · exact hlt
  · have hNc := h.nodes c hc
    have hv : ViewsEq st s s' c := by
      refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
      · simp only [LawfulStore.rqQ]
        rw [hn c hc _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
          hn c hc _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
            (by rw [rqTailOff_val hp]; omega)]
      · exact hn c hc _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
      · exact hn c hc _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    refine ⟨(h.ready c hc).1.agree hv.1 fun p hp y hy => ?_, (h.ready c hc).2.views hv⟩
    exact hlink y (((h.ready c hc).1.rel p hp).mem y hy)
  · have e : L.relQ s' c = L.relQ s c := by
      simp only [LawfulStore.relQ]
      rw [hn c hc _ (by rw [relh_val]; omega) (by rw [relh_val]) (by rw [relh_val]; simp),
        hn c hc _ (by rw [relt_val]; omega) (by rw [relt_val]) (by rw [relt_val]; omega)]
    rw [e]; exact hrel (h.release c hc)
  · intro c hc p hp y hy
    have := h.inQ c hc p hp y hy
    have hyT := h.memT hc hp hy
    exact ⟨(haff y hyT).trans this.1, (hle y hyT c hc p hp hy).trans this.2⟩
  · intro c hc y hy
    exact (haff y (h.memTR hc hy)).trans (h.inR c hc y hy)
  · intro y hy
    rw [hinq y hy, haff y hy]
    rcases hprio y hy with e | ⟨h0, hlt⟩
    · rw [e]; exact h.queued y hy
    · constructor
      · intro h1; exact absurd h0 h1
      · intro h1; exact absurd h1 (h.notQ hy h0 (h.aff y hy) hlt)
  · intro y hy
    rw [hinq y hy, haff y hy]; exact h.released y hy
  · intro y hy hq
    rw [haff y hy] at hq ⊢
    rcases hprio y hy with e | ⟨h0, hlt⟩
    · rw [e] at hq; exact h.excl y hy hq
    · exact absurd hq (h.notQ hy h0 (h.aff y hy) hlt)

end

end Fl4Proofs.P1
