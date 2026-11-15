/-
P1: the facts besides the queue invariant that `sched::schedule` (seL4
`schedule`) needs, and the scheduler steps it makes, keeping them.

Besides the queue invariant this needs two facts that are not about the
queues:

* `BoundInv`: the threads `schedule` may switch to have a scheduling
  context (seL4 `valid_sched`: queued and released threads, the switch-to
  candidate and, when the action is "resume", the current thread are
  `active_sc_tcb_at`; the idle thread has the idle SC).  `schedule` keeps it.
* `SCsOK`: the SCs of the bound TCBs and the current SC are well formed
  (`RefillsWF`, l4v `valid_refills`), lie in the words `Sg ⊆ Ω` (outside the
  kernel-global area) and the current SC is disjoint from the others.  This
  is assumed of the state `timer::fire` leaves behind; the queue code before
  `switch_sched_context` does not touch it (`Fr`).

`timer::fire` sends notification signals (it can wake threads and change
the ready and endpoint queues), so it is not footprint-disjoint from the
invariant: its preservation of the three invariants is a hypothesis.
-/
import Fl4Proofs.P1.QueueSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap} {Scs : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- The current core's `CUR_THREAD` and `IDLE_THREAD` words. -/
def LawfulStore.curW (s : S) : U64 := L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
def LawfulStore.idleW (s : S) : U64 := L.mem s (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD)
/-- The current core's `CUR_SC` word. -/
def LawfulStore.cscW (s : S) : U64 := L.mem s (L.nodeA s layout.node.CUR_SC)

/-- The thread states blocked on an IPC object or on a reply. -/
def BlockedR (v : U64) : Prop := Blocked v ∨ v = sched.TS_BLOCKED_ON_REPLY

/-- The threads whose bound SC must be active: queued and released threads,
the switch-to candidate, the idle thread, the current thread when it is to be
resumed, and the threads blocked on IPC, a notification or a reply (l4v
`valid_ready_qs`, `valid_release_q`, `valid_sched_action`,
`released_ipc_queues`, `active_sc_tcb_at`).  The current thread otherwise
may hold an inactive SC: a passive receiver can be donated one by its bound
notification, and then a reschedule is pending. -/
def Sch (st : machine.Store S) [L : LawfulStore st] (s : S) (t : U64) : Prop :=
  (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
    L.actionW s = t ∨ L.idleW s = t ∨ (L.actionW s = 0#u64 ∧ L.curW s = t) ∨ BlockedR (L.mem s (stA t))

/-- The threads `schedule` can make current have an SC (seL4
`active_sc_tcb_at`, the part `switch_sched_context` needs), and the bound
SCs of the `Sch` threads are among the active ones `Ac`. -/
structure BoundInv (st : machine.Store S) [L : LawfulStore st] (T Ac : Set U64) (s : S) : Prop where
  q : ∀ t ∈ T, (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → L.mem s (scA t) ≠ 0#u64
  r : ∀ t ∈ T, (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → L.mem s (scA t) ≠ 0#u64
  act : L.actionW s ∈ T → L.mem s (scA (L.actionW s)) ≠ 0#u64
  idle : L.mem s (scA (L.idleW s)) ≠ 0#u64
  resume : L.actionW s = 0#u64 → L.mem s (scA (L.curW s)) ≠ 0#u64
  /-- The idle thread is not blocked (so in no endpoint or notification
  queue), nor blocked on a reply (it is never a caller, l4v
  `idle_thread_not_queued`/`valid_idle`). -/
  idleNB : ¬ BlockedR (L.mem s (stA (L.idleW s)))
  /-- The bound SCs of the `Sch` threads are active. -/
  sact : ∀ t ∈ T, Sch st s t → L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac

/-- An SC object whose words are among `Sg` and whose refills are well formed
if it is active (`REFILL_MAX ≠ 0`, l4v `valid_refills` under `sc_active`). -/
def SCA (st : machine.Store S) [L : LawfulStore st] (s : S) (Sg : Set U64) (sc : obj.Sc) (sb : Nat) : Prop :=
  (L.rmax s sc ≠ 0#u64 → RefillsWF st s sc sb) ∧ maxA sc ∈ Sg ∧ ∀ b, Aligned b → InSC sc sb b → b ∈ Sg

/-- The SCs: every SC object lies in the words `Sg ⊆ Ω` (outside the
kernel-global area, which is part of `Ω`) and is well formed if active
(l4v `valid_refills` under `sc_active`); the active ones are `Ac`; a
sporadic SC is active; the current SC is disjoint from the other bound SCs.
`Z sc` is the size exponent of the SC at `sc`. -/
structure SCsOK (st : machine.Store S) [L : LawfulStore st] (T Ω Sg Scs : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (s : S) : Prop where
  sub : ∀ b ∈ Sg, b ∈ Ω
  ks : ∀ b ∈ Sg, b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val
  ksΩ : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∈ Ω
  disj : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ≠ L.cscW s →
    ∀ b, InSC (L.mem s (scA t)) (Z (L.mem s (scA t))) b → Outside b (L.cscW s) (Z (L.cscW s))
  /-- Every SC object is well formed if active. -/
  all : ∀ c ∈ Scs, SCA st s Sg c (Z c)
  /-- The active SCs are `Ac`. -/
  act : ∀ c ∈ Scs, c ∈ Ac ↔ L.rmax s c ≠ 0#u64
  /-- A sporadic SC is active. -/
  spor : ∀ c ∈ Scs, L.mem s (sporA c) ≠ 0#u64 → c ∈ Ac
  /-- The `SPORADIC` words are frame words. -/
  spSg : ∀ c ∈ Scs, sporA c ∈ Sg
  /-- An SC with a reply stack is active (l4v `active_reply_scs`). -/
  rep : ∀ c ∈ Scs, L.mem s (scReplyA c) ≠ 0#u64 → c ∈ Ac
  /-- The `REPLY` words are frame words. -/
  repSg : ∀ c ∈ Scs, scReplyA c ∈ Sg

/-- The frame words `Sg` are among `Ω` and outside the kernel-global area,
which is part of `Ω`. -/
structure SgOK (st : machine.Store S) [L : LawfulStore st] (Ω Sg : Set U64) (s : S) : Prop where
  sub : ∀ b ∈ Sg, b ∈ Ω
  ks : ∀ b ∈ Sg, b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val
  ksΩ : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∈ Ω

theorem SCsOK.sg {Sg : Set U64} {Z : U64 → Nat} {s : S} (h : SCsOK st T Ω Sg Scs Z Ac s) : SgOK st Ω Sg s :=
  ⟨h.sub, h.ks, h.ksΩ⟩

theorem SgOK.empty (s : S) (hks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
    core.num.U64.wrapping_add (L.ksb s) o ∈ Ω) : SgOK st Ω ∅ s :=
  ⟨fun _ h => absurd h (Set.notMem_empty _), fun _ h => absurd h (Set.notMem_empty _), hks⟩

/-- What the queue code leaves alone: the SC words `Sg`, the TCBs' `SC`
fields and the current SC. -/
structure Fr (st : machine.Store S) [L : LawfulStore st] (T Sg : Set U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  sig : ∀ b ∈ Sg, L.mem s' b = L.mem s b
  sc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t)
  csc : L.cscW s' = L.cscW s
  /-- The reply-object and state fields of the TCBs. -/
  rep : ∀ t ∈ T, L.mem s' (core.num.U64.wrapping_add t 3360#u64) = L.mem s (core.num.U64.wrapping_add t 3360#u64)
  st : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t)
  /-- The bound-notification fields of the TCBs. -/
  bnd : ∀ t ∈ T, L.mem s' (core.num.U64.wrapping_add t 3368#u64) = L.mem s (core.num.U64.wrapping_add t 3368#u64)
  /-- The timer fields of the TCBs. -/
  tmr : ∀ t ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3592 → K.val % 8 = 0 →
    L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K)
  /-- The timer-tree words of the placed nodes. -/
  tnd : ∀ c : U64, @NodePlaced _ _ L T s c → ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) →
    L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  /-- The `YIELD_TO` fields of the TCBs. -/
  yld : ∀ t ∈ T, L.mem s' (core.num.U64.wrapping_add t 3472#u64) = L.mem s (core.num.U64.wrapping_add t 3472#u64)
  /-- The idle thread. -/
  idle : L.idleW s' = L.idleW s

theorem Fr.refl (Sg : Set U64) (s : S) : Fr st T Sg s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Fr.trans {Sg : Set U64} {s₁ s₂ s₃ : S} (h₁ : Fr st T Sg s₁ s₂) (h₂ : Fr st T Sg s₂ s₃) : Fr st T Sg s₁ s₃ :=
  ⟨h₂.ksb.trans h₁.ksb, h₂.cpu.trans h₁.cpu, fun b hb => (h₂.sig b hb).trans (h₁.sig b hb),
   fun t ht => (h₂.sc t ht).trans (h₁.sc t ht), h₂.csc.trans h₁.csc,
   fun t ht => (h₂.rep t ht).trans (h₁.rep t ht), fun t ht => (h₂.st t ht).trans (h₁.st t ht),
   fun t ht => (h₂.bnd t ht).trans (h₁.bnd t ht),
   fun t ht K a b c => (h₂.tmr t ht K a b c).trans (h₁.tmr t ht K a b c),
   fun c hc o ho => by
     rw [← nodeAt_of_ksb h₁.ksb]
     exact (h₂.tnd c (hc.ksb h₁.ksb) o ho).trans (by rw [nodeAt_of_ksb h₁.ksb]; exact h₁.tnd c hc o ho),
   fun t ht => (h₂.yld t ht).trans (h₁.yld t ht), h₂.idle.trans h₁.idle⟩

/-- The scheduling words a TCB invocation's later steps rely on: the TCBs'
`SC` and state fields, the frame words `Sg` (the SCs' `TCB` words among
them), the idle thread, and the scheduler action (kept, or `CHOOSE_NEW`). -/
structure PFr (st : machine.Store S) [L : LawfulStore st] (T Sg : Set U64) (s s' : S) : Prop where
  sc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t)
  st : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t)
  sig : ∀ b ∈ Sg, L.mem s' b = L.mem s b
  idle : L.idleW s' = L.idleW s
  act : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64

theorem PFr.refl (Sg : Set U64) (s : S) : PFr st T Sg s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, Or.inl rfl⟩

theorem PFr.trans {Sg : Set U64} {s₁ s₂ s₃ : S} (h₁ : PFr st T Sg s₁ s₂) (h₂ : PFr st T Sg s₂ s₃) :
    PFr st T Sg s₁ s₃ :=
  ⟨fun t ht => (h₂.sc t ht).trans (h₁.sc t ht), fun t ht => (h₂.st t ht).trans (h₁.st t ht),
    fun b hb => (h₂.sig b hb).trans (h₁.sig b hb), h₂.idle.trans h₁.idle, by
      rcases h₂.act with e | e
      · rcases h₁.act with e' | e'
        · exact Or.inl (e.trans e')
        · exact Or.inr (e.trans e')
      · exact Or.inr e⟩

theorem PFr.of_fr {Sg : Set U64} {s s' : S} (f : Fr st T Sg s s')
    (ha : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) : PFr st T Sg s s' :=
  ⟨f.sc, f.st, f.sig, f.idle, ha⟩

theorem SgOK.fr {Sg : Set U64} {s s' : S} (h : SgOK st Ω Sg s) (f : Fr st T Sg s s') : SgOK st Ω Sg s' :=
  ⟨h.sub, fun b hb => by rw [f.ksb]; exact h.ks b hb, fun o h1 h2 => by rw [f.ksb]; exact h.ksΩ o h1 h2⟩

theorem RefillsWF.agree {s s' : S} {sc : obj.Sc} {sb : Nat} (h : RefillsWF st s sc sb)
    (hag : ∀ b, Aligned b → InSC sc sb b → L.mem s' b = L.mem s b) : RefillsWF st s' sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have := h.min_le; simp at this
  have e : ∀ b, Aligned b → sc.val ≤ b.val → b.val < sc.val + 96 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hag b hb ⟨h1, by omega⟩
  have em : L.rmax s' sc = L.rmax s sc := e _ (by addr) (by addr) (by addr)
  refine h.of_hdr em ?_ ?_
  · rw [show L.rhead s' sc = L.rhead s sc from e _ (by addr) (by addr) (by addr)]
    exact h.head_lt
  · rw [show L.rtail s' sc = L.rtail s sc from e _ (by addr) (by addr) (by addr)]
    exact h.tail_lt

theorem SCA.agree {Sg : Set U64} {s s' : S} {sc : obj.Sc} {sb : Nat} (h : SCA st s Sg sc sb)
    (hag : ∀ b ∈ Sg, L.mem s' b = L.mem s b) : SCA st s' Sg sc sb :=
  ⟨fun hm => by
    have e : L.rmax s' sc = L.rmax s sc := hag _ h.2.1
    exact (h.1 (e ▸ hm)).agree fun b hb hi => hag b (h.2.2 b hb hi), h.2.1, h.2.2⟩

theorem SCA.of_wf {Sg : Set U64} {s s' : S} {sc : obj.Sc} {sb : Nat} (h : SCA st s Sg sc sb)
    (hm : L.rmax s' sc = L.rmax s sc) (wf : RefillsWF st s sc sb → RefillsWF st s' sc sb) : SCA st s' Sg sc sb :=
  ⟨fun h0 => wf (h.1 (hm ▸ h0)), h.2.1, h.2.2⟩

theorem SCA.mk' {Sg : Set U64} {s s' : S} {sc : obj.Sc} {sb : Nat} (h : SCA st s Sg sc sb)
    (hwf : L.rmax s' sc ≠ 0#u64 → RefillsWF st s' sc sb) : SCA st s' Sg sc sb := ⟨hwf, h.2.1, h.2.2⟩

/-- An SC object outside a footprint keeps `SCA`. -/
theorem SCA.writesIn {Sg : Set U64} {s s' : S} {sc : obj.Sc} {sb : Nat} {A : U64 → Prop} (h : SCA st s Sg sc sb)
    (hal : Aligned (maxA sc)) (hin : sc.val ≤ (maxA sc).val ∧ (maxA sc).val < sc.val + 2 ^ sb)
    (w : WritesIn st s s' A) (hA : ∀ b, Aligned b → A b → Outside b sc sb) : SCA st s' Sg sc sb := by
  have e : L.rmax s' sc = L.rmax s sc := w.mem_eq hal fun hh => by
    have := hA _ hal hh; unfold Outside at this; omega
  exact h.of_wf e fun hW => hW.writesIn w hA

theorem SCin.agree {Sg : Set U64} {s s' : S} {sc : obj.Sc} {sb : Nat} (h : SCin st s Sg sc sb)
    (hag : ∀ b ∈ Sg, L.mem s' b = L.mem s b) : SCin st s' Sg sc sb :=
  ⟨h.1.agree fun b hb hi => hag b (h.2 b hb hi), h.2⟩

theorem SCin.mono {Sg Ω : Set U64} {s : S} {sc : obj.Sc} {sb : Nat} (h : SCin st s Sg sc sb)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) : SCin st s Ω sc sb := ⟨h.1, fun b hb hi => hsub b (h.2 b hb hi)⟩

theorem cscW_eq {s s' : S} (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s) :
    L.nodeA s' layout.node.CUR_SC = L.nodeA s layout.node.CUR_SC := by
  simp [LawfulStore.nodeA, LawfulStore.nodeAt, hk, hc]

theorem SCsOK.fr {Sg : Set U64} {Z : U64 → Nat} {s s' : S} (h : SCsOK st T Ω Sg Scs Z Ac s) (f : Fr st T Sg s s') :
    SCsOK st T Ω Sg Scs Z Ac s' := by
  refine ⟨h.sub, fun b hb => by rw [f.ksb]; exact h.ks b hb, fun o h1 h2 => by rw [f.ksb]; exact h.ksΩ o h1 h2,
    fun t ht hb hne => ?_, fun c hc => (h.all c hc).agree f.sig,
    fun c hc => by rw [show L.rmax s' c = L.rmax s c from f.sig _ (h.all c hc).2.1]; exact h.act c hc,
    fun c hc h0 => h.spor c hc (by rw [← f.sig _ (h.spSg c hc)]; exact h0), h.spSg,
    fun c hc h0 => h.rep c hc (by rw [← f.sig _ (h.repSg c hc)]; exact h0), h.repSg⟩
  rw [f.sc t ht] at hb hne ⊢; rw [f.csc] at hne ⊢; exact h.disj t ht hb hne

/-- `SCsOK` from its parts: the kernel-global base, the TCBs' SC fields and
the current SC word are kept, the SC objects stay `SCA`, and their
`REFILL_MAX` and `SPORADIC` words are kept. -/
theorem SCsOK.mk2 {Sg : Set U64} {Z : U64 → Nat} {s s' : S} (h : SCsOK st T Ω Sg Scs Z Ac s)
    (hk : L.ksb s' = L.ksb s) (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) (hcs : L.cscW s' = L.cscW s)
    (hall : ∀ c ∈ Scs, SCA st s' Sg c (Z c)) (hmx : ∀ c ∈ Scs, L.mem s' (maxA c) = L.mem s (maxA c))
    (hsp : ∀ c ∈ Scs, L.mem s' (sporA c) = L.mem s (sporA c))
    (hrep : ∀ c ∈ Scs, L.mem s' (scReplyA c) ≠ 0#u64 → c ∈ Ac) : SCsOK st T Ω Sg Scs Z Ac s' := by
  refine ⟨h.sub, fun b hb => by rw [hk]; exact h.ks b hb, fun o h1 h2 => by rw [hk]; exact h.ksΩ o h1 h2,
    fun t ht hb hne => ?_, hall, fun c hc => by rw [show L.rmax s' c = L.rmax s c from hmx c hc]; exact h.act c hc,
    fun c hc h0 => h.spor c hc (by rw [← hsp c hc]; exact h0), h.spSg,
    hrep, h.repSg⟩
  rw [hsc t ht] at hb hne ⊢; rw [hcs] at hne ⊢; exact h.disj t ht hb hne

theorem SCsOK.wf {Sg : Set U64} {Z : U64 → Nat} {s : S} (h : SCsOK st T Ω Sg Scs Z Ac s) {c : U64} (hc : c ∈ Scs)
    (ha : c ∈ Ac) : RefillsWF st s c (Z c) := (h.all c hc).1 ((h.act c hc).1 ha)

theorem SCsOK.scin {Sg : Set U64} {Z : U64 → Nat} {s : S} (h : SCsOK st T Ω Sg Scs Z Ac s) {c : U64} (hc : c ∈ Scs)
    (ha : c ∈ Ac) : SCin st s Sg c (Z c) := ⟨h.wf hc ha, (h.all c hc).2.2⟩

/-! ## Writes that keep `Fr` -/

section frame
variable {Cs X Sg : Set U64} {Z : U64 → Nat} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem scA_aligned {t : U64} (ht : TcbAddr t) : Aligned (scA t) := by
  rw [scA_eq]; exact field_aligned ht (by simp) (by simp)

theorem cscA_val (hN' : NodePlaced st T s (L.cpu s)) :
    (L.nodeA s layout.node.CUR_SC).val = L.nodeBase s (L.cpu s) + 24 := by
  unfold LawfulStore.nodeA; rw [nodeAt_val hN' (by simp [layout.node.CUR_SC])]; simp [layout.node.CUR_SC]

theorem fr_wr (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) {a v : U64}
    (ha : Aligned a) (hsg : ∀ b ∈ Sg, a.val ≠ b.val)
    (hf : ∀ t ∈ T, ∀ K : U64, K.val < 4096 → a.val ≠ (core.num.U64.wrapping_add t K).val)
    (hcs : a.val ≠ (L.nodeA s layout.node.CUR_SC).val)
    (htn : ∀ c : U64, NodePlaced st T s c → ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → a.val ≠ (L.nodeAt s c o).val)
    (hid : a.val ≠ (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD).val) :
    Fr st T Sg s (L.wr s a v) := by
  have fid : L.idleW (L.wr s a v) = L.idleW s := by
    unfold LawfulStore.idleW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes _ h.cur) (by rw [idle8]; omega) (by rw [idle8])) hid
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb => ?_, fun t ht => ?_, ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => L.mem_wr_ne ha (field_aligned (h.tcbs t ht) (by simp) (by simp)) (hf t ht _ (by simp)),
    fun t ht K h1 h2 h3 => L.mem_wr_ne ha (field_aligned (h.tcbs t ht) (by omega) h3) (hf t ht _ (by omega)),
    fun c hc o ho => L.mem_wr_ne ha (nodeAt_aligned hc (by omega) (by omega)) (htn c hc o ho),
    fun t ht => L.mem_wr_ne ha (field_aligned (h.tcbs t ht) (by simp) (by simp)) (hf t ht _ (by simp)), fid⟩
  · exact L.mem_wr_ne ha (h.omega _ (hS.sub b hb)).1 (hsg b hb)
  · rw [scA_eq]; exact L.mem_wr_ne ha (field_aligned (h.tcbs t ht) (by simp) (by simp)) (hf t ht _ (by simp))
  rotate_left
  · exact L.mem_wr_ne ha (field_aligned (h.tcbs t ht) (by simp) (by simp)) (hf t ht _ (by simp))
  · rw [stA_eq]; exact L.mem_wr_ne ha (field_aligned (h.tcbs t ht) (by simp) (by simp)) (hf t ht _ (by simp))
  · unfold LawfulStore.cscW
    rw [cscW_eq (L.ksb_wr _ _ _) (L.cpu_wr _ _ _)]
    exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes _ h.cur) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])) hcs

theorem fr_node (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) {c o v : U64}
    (hc : c ∈ Cs) (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h24 : c = L.cpu s → o.val ≠ 24)
    (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) (hi8 : c = L.cpu s → o.val ≠ 8) :
    Fr st T Sg s (L.wr s (L.nodeAt s c o) v) := by
  have hN := h.nodes c hc
  refine fr_wr h hS (nodeAt_aligned hN ho h8) (fun b hb => out_ne_node (h.omega _ (hS.sub b hb)) hc hN ho)
    (fun t ht K hK => ?_) ?_ (fun c' hc' o' ho' => by
      by_cases e : c = c'
      · subst e; rw [nodeAt_val hN ho, nodeAt_val hc' (by omega)]; omega
      · intro e'; exact nodeAt_ne_cpu hN hc' ho (by omega) e (UScalar.eq_of_val_eq e')) ?_
  rotate_right
  · by_cases e : c = L.cpu s
    · subst e; rw [nodeAt_val hN ho, nodeAt_val hN (by rw [idle8]; omega), idle8]; have := hi8 rfl; omega
    · intro e'
      exact nodeAt_ne_cpu hN (h.nodes _ h.cur) ho (by rw [idle8]; omega) e (UScalar.eq_of_val_eq e')
  · intro e
    exact node_ne_field hN ho ht (h.tcbs t ht) hK (UScalar.eq_of_val_eq e)
  · by_cases e : c = L.cpu s
    · subst e; rw [cscA_val hN, nodeAt_val hN ho]; have := h24 rfl; omega
    · intro e'
      exact nodeAt_ne_cpu hN (h.nodes _ h.cur) ho (by simp [layout.node.CUR_SC]) e (UScalar.eq_of_val_eq e')

theorem ks_val (h : SchedQueuesInvX st T Cs Ω H X s Q R) {o : U64} (ho : o.val < 13568) :
    (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
  have := (h.nodes _ h.cur).fits
  simp only [LawfulStore.nodeBase] at this
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem ks_aligned (h : SchedQueuesInvX st T Cs Ω H X s Q R) {o : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add (L.ksb s) o) := by
  have := (h.nodes _ h.cur).align
  simp only [LawfulStore.nodeBase] at this
  unfold Aligned; rw [ks_val h ho]; omega

theorem fr_ks (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) {o v : U64}
    (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    Fr st T Sg s (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v) := by
  refine fr_wr h hS (ks_aligned h ho h8) (fun b hb => ?_) (fun t ht K hK => ?_) ?_ (fun c hc o' ho' => by
    rw [ks_val h ho, nodeAt_val hc (by omega)]; simp only [LawfulStore.nodeBase]; omega) ?_
  rotate_right
  · rw [ks_val h ho, nodeAt_val (h.nodes _ h.cur) (by rw [idle8]; omega)]; simp only [LawfulStore.nodeBase]; omega
  · rw [ks_val h ho]; have := hS.ks b hb; omega
  · rw [ks_val h ho, field_val (h.tcbs t ht) hK]; have := h.ksOut t ht; simp at this ⊢; omega
  · rw [ks_val h ho, cscA_val (h.nodes _ h.cur)]; simp only [LawfulStore.nodeBase]; omega

theorem act_wr_field {s : S} {t K v a : U64} (hN : NodePlaced st T s (L.cpu s)) (ht : t ∈ T) (hta : TcbAddr t)
    (ha : a = core.num.U64.wrapping_add t K) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.actionW (L.wr s a v) = L.actionW s := by
  subst ha
  unfold LawfulStore.actionW
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  exact L.mem_wr_ne (field_aligned hta hK hK8) (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
    (fun e => node_ne_field hN (by rw [act_val]; omega) ht hta hK (UScalar.eq_of_val_eq e).symm)

/-- A TCB field write keeps `Fr` when the field is none of those `Fr` keeps. -/
theorem fr_field (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) {t K v : U64} (ht : t ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKx : K.val ≠ 3328 ∧ K.val ≠ 3360 ∧ K.val ≠ 3368 ∧ K.val ≠ 3464 ∧ K.val ≠ 3472 ∧ (K.val < 3528 ∨ 3592 ≤ K.val)) :
    Fr st T Sg s (L.wr s (core.num.U64.wrapping_add t K) v) := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha := field_aligned hta hK hK8
  have hN := h.nodes _ h.cur
  have fk : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ K.val →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := fun y hy K' h1 h2 hne =>
    L.mem_wr_ne ha (field_aligned (hT y hy) h1 h2) (fun e => field_ne hta (hT y hy) hK h1
      (fun _ => fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  have nk : ∀ c, NodePlaced st T s c → ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun c hc o ho h8 => L.mem_wr_ne ha (nodeAt_aligned hc ho h8)
      (fun e => node_ne_field hc ho ht hta hK (UScalar.eq_of_val_eq e).symm)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hKx
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb => L.mem_wr_ne ha (h.omega _ (hS.sub b hb)).1
      (out_ne_field (h.omega _ (hS.sub b hb)) ht hta hK),
    fun y hy => by rw [scA_eq]; exact fk y hy _ (by simp) (by simp) (by simp; omega), ?_,
    fun y hy => fk y hy _ (by simp) (by simp) (by simp; omega),
    fun y hy => by rw [stA_eq]; exact fk y hy _ (by simp) (by simp) (by simp; omega),
    fun y hy => fk y hy _ (by simp) (by simp) (by simp; omega),
    fun y hy K' h1 h2 h3 => fk y hy K' (by omega) h3 (by omega),
    fun c hc o ho => nk c hc o (by omega) (by omega),
    fun y hy => fk y hy _ (by simp) (by simp) (by simp; omega), ?_⟩
  · unfold LawfulStore.cscW; rw [cscW_eq (L.ksb_wr _ _ _) (L.cpu_wr _ _ _)]
    exact nk _ hN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  · unfold LawfulStore.idleW; simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact nk _ hN _ (by rw [idle8]; omega) (by rw [idle8])

/-- A queue operation's footprint keeps `Fr`, and the words `BoundInv`
reads apart from the operated thread's `IN_QUEUES`. -/
theorem qfoot_keep (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) {s' : S} {W : List U64}
    {c t : U64} {P : Nat → Prop} (hW : ∀ w ∈ W, w ∈ T) (hc : c ∈ Cs) (ht : t ∈ T)
    (hP : ∀ o, P o → o ≠ 0 ∧ o ≠ 8 ∧ o ≠ 16 ∧ o ≠ 24 ∧ o ≠ 88 ∧ o ≠ 104 ∧ o ≠ 112) (hw : WritesIn st s s' (L.QFoot s W c P t)) :
    Fr st T Sg s s' ∧ (∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y)) ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.idleW s' = L.idleW s := by
  have hT := h.tcbs
  have hN := h.nodes c hc
  have hN' := h.nodes _ h.cur
  have nd : ∀ o : U64, o.val < 128 → o.val % 8 = 0 → (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 hv => by
    rw [hw.2.1]
    exact node_qfoot hT hW hN hN' ht hw hN' (by omega) h8 (fun _ hpo => by have := hP _ hpo; omega)
      (fun _ => by omega)
  obtain ⟨hsb, -, hout⟩ := ext_qfoot hT hW hN hN' ht hc h.cur hw
  refine ⟨⟨hw.1, hw.2.1, fun b hb => hout b (h.omega _ (hS.sub b hb)), fun y hy => sc_qfoot hT hW hN hN' ht hw hy,
    ?_, fun y hy => field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp),
    fun y hy => (hsb y hy).1,
    fun y hy => field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp),
    fun y hy K h1 h2 h3 => field_qfoot hT hW hN hN' ht hw hy (by omega) h3 (by omega) (fun _ => by omega),
    fun c' hc' o ho => by
      have hP' : c' = c → ¬ P o.val := fun _ hpo => by
        obtain ⟨-, -, -, -, h0, h1, h2⟩ := hP _ hpo; omega
      have e := node_qfoot hT hW hN hN' ht hw hc' (o := o) (by omega) (by omega) hP' (fun _ => by omega)
      rwa [nodeAt_of_ksb hw.1] at e,
    fun y hy => field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp),
    nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)⟩,
    fun y hy hyt => inq_qfoot hT hW hN hN' ht hw hy hyt, ?_, ?_, ?_⟩
  · unfold LawfulStore.cscW LawfulStore.nodeA
    exact nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  · unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  · unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)
  · unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)

end frame

/-! ## `BoundInv` under writes -/

section bound
variable {Cs X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- The idle thread stays unblocked when the idle word and its state are kept. -/
theorem BoundInv.nb (hB : BoundInv st T Ac s) (ei : L.idleW s' = L.idleW s)
    (hst : L.mem s' (stA (L.idleW s)) = L.mem s (stA (L.idleW s))) : ¬ BlockedR (L.mem s' (stA (L.idleW s'))) := by
  rw [ei, hst]; exact hB.idleNB

/-- `Sch` when the queue flags only drop and the node words and states are
kept. -/
theorem Sch.of_eq {s s' : S} {y : U64}
    (hq : (L.mem s' (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 → (L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64)
    (hr : (L.mem s' (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64)
    (ha : L.actionW s' = L.actionW s) (hi : L.idleW s' = L.idleW s) (hc : L.curW s' = L.curW s)
    (hs : L.mem s' (stA y) = L.mem s (stA y)) (h : Sch st s' y) : Sch st s y := by
  unfold Sch at h ⊢
  rw [ha, hi, hc, hs] at h
  rcases h with h | h | h
  · exact Or.inl (hq h)
  · exact Or.inr (Or.inl (hr h))
  · exact Or.inr (Or.inr h)

/-- `Sch` when each of its parts in the new state holds in the old one. -/
theorem Sch.of_le {s s' : S} {y : U64}
    (hq : (L.mem s' (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 → (L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64)
    (hr : (L.mem s' (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64)
    (ha : L.actionW s' = y → L.actionW s = y) (hi : L.idleW s' = y → L.idleW s = y)
    (hc : L.actionW s' = 0#u64 ∧ L.curW s' = y → L.actionW s = 0#u64 ∧ L.curW s = y)
    (hs : BlockedR (L.mem s' (stA y)) → BlockedR (L.mem s (stA y))) (h : Sch st s' y) : Sch st s y := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl (hq h)
  · exact Or.inr (Or.inl (hr h))
  · exact Or.inr (Or.inr (Or.inl (ha h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hi h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hc h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hs h)))))

/-- `Sch` after a write of a word of `Ω`. -/
theorem Sch.wr_out {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {a v y : U64} (ha : a ∈ Ω) (hy : y ∈ T)
    (hS : Sch st (L.wr s a v) y) : Sch st s y := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  have hya := h.tcbs y hy
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s a v) (L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o h1 h2 => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ho.1 (nodeAt_aligned hN h1 h2) (fun e => out_ne_node ho h.cur hN h1 e.symm)
  have fl : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s a v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun K hK hK8 => L.mem_wr_ne ho.1 (field_aligned hya hK hK8) (fun e => out_ne_field ho hy hya hK e.symm)
  exact Sch.of_eq (fun hf => by rwa [inqA_eq, fl _ (by simp) (by simp)] at hf)
    (fun hf => by rwa [inqA_eq, fl _ (by simp) (by simp)] at hf)
    (nd _ (by rw [act_val]; omega) (by rw [act_val])) (nd _ (by rw [idle8]; omega) (by rw [idle8]))
    (nd _ (by rw [curth0]; omega) (by rw [curth0])) (by rw [stA_eq]; exact fl _ (by simp) (by simp)) hS

/-- `Sch` after a TCB field write other than the state and `IN_QUEUES`. -/
theorem Sch.wr_field {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {t K v y : U64} (ht : t ∈ T) (hK : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hKs : K.val ≠ 3328 ∧ K.val ≠ 3592) (hy : y ∈ T)
    (hS : Sch st (L.wr s (core.num.U64.wrapping_add t K) v) y) : Sch st s y := by
  have hN := h.nodes _ h.cur
  have hta := h.tcbs t ht
  have hya := h.tcbs y hy
  have ha := field_aligned hta hK hK8
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v)
        (L.nodeAt (L.wr s (core.num.U64.wrapping_add t K) v) (L.cpu (L.wr s (core.num.U64.wrapping_add t K) v)) o) =
        L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN h1 h2)
        (fun e => node_ne_field hN h1 ht hta hK (UScalar.eq_of_val_eq e).symm)
  have fl : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (K'.val = 3328 ∨ K'.val = 3592) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := fun K' h1 h2 h3 =>
    L.mem_wr_ne ha (field_aligned hya h1 h2) (fun e => field_ne hta hya hK h1 (fun _ => by omega)
      (UScalar.eq_of_val_eq e))
  exact Sch.of_eq (fun hf => by rwa [inqA_eq, fl _ (by simp) (by simp) (by simp)] at hf)
    (fun hf => by rwa [inqA_eq, fl _ (by simp) (by simp) (by simp)] at hf)
    (nd _ (by rw [act_val]; omega) (by rw [act_val])) (nd _ (by rw [idle8]; omega) (by rw [idle8]))
    (nd _ (by rw [curth0]; omega) (by rw [curth0])) (by rw [stA_eq]; exact fl _ (by simp) (by simp) (by simp)) hS

/-- The general preservation lemma: the SC fields of `T` are kept, each
flag that gets set belongs to a bound thread, and the action, current and
idle thread are bound where `BoundInv` asks. -/
theorem BoundInv.mk' (hB : BoundInv st T Ac s) (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y))
    (hq : ∀ y ∈ T, (L.mem s' (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 →
      (L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA y) ≠ 0#u64)
    (hr : ∀ y ∈ T, (L.mem s' (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 →
      (L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA y) ≠ 0#u64)
    (ha : L.actionW s' ∈ T → L.actionW s' ∈ T ∧ L.mem s (scA (L.actionW s')) ≠ 0#u64)
    (hidle : L.idleW s' ∈ T ∧ L.mem s (scA (L.idleW s')) ≠ 0#u64)
    (hres : L.actionW s' = 0#u64 → L.curW s' ∈ T ∧ L.mem s (scA (L.curW s')) ≠ 0#u64)
    (hnb : ¬ BlockedR (L.mem s' (stA (L.idleW s'))))
    (hsch : ∀ y ∈ T, Sch st s' y → L.mem s (scA y) ≠ 0#u64 → Sch st s y ∨ L.mem s (scA y) ∈ Ac) :
    BoundInv st T Ac s' := by
  have up : ∀ y ∈ T, ((L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
      L.mem s (scA y) ≠ 0#u64) → L.mem s' (scA y) ≠ 0#u64 := by
    intro y hy hh; rw [hsc y hy]
    rcases hh with hh | hh | hh
    · exact hB.q y hy hh
    · exact hB.r y hy hh
    · exact hh
  refine ⟨fun y hy hf => up y hy (hq y hy hf), fun y hy hf => up y hy (hr y hy hf), fun haT => ?_, ?_, fun h0 => ?_,
    hnb, fun y hy hS h0 => ?_⟩
  · obtain ⟨h1, h2⟩ := ha haT; rw [hsc _ h1]; exact h2
  · rw [hsc _ hidle.1]; exact hidle.2
  · obtain ⟨h1, h2⟩ := hres h0; rw [hsc _ h1]; exact h2
  · rw [hsc y hy] at h0 ⊢
    rcases hsch y hy hS h0 with h | h
    · exact hB.sact y hy h h0
    · exact h

/-- `BoundInv` when the words it reads are kept. -/
theorem BoundInv.keep (hB : BoundInv st T Ac s) (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y))
    (hiq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y)) (ea : L.actionW s' = L.actionW s)
    (ec : L.curW s' = L.curW s) (ei : L.idleW s' = L.idleW s) (hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y))
    (hcT : L.curW s ∈ T) (hiT : L.idleW s ∈ T) : BoundInv st T Ac s' :=
  hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hiq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hiq y hy]; exact hf)))
    (fun haT => by rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩) (by rw [ei]; exact ⟨hiT, hB.idle⟩)
    (fun h0 => by rw [ea] at h0; rw [ec]; exact ⟨hcT, hB.resume h0⟩) (hB.nb ei (hst _ hiT))
    (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hiq y hy] at hf) (fun hf => by rwa [hiq y hy] at hf)
      ea ei ec (hst y hy) hS))

theorem BoundInv.curA (hB : BoundInv st T Ac s) (hcT : L.curW s ∈ T) (h0 : L.actionW s = 0#u64) :
    L.mem s (scA (L.curW s)) ∈ Ac :=
  hB.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, rfl⟩))))) (hB.resume h0)

theorem BoundInv.actA (hB : BoundInv st T Ac s) (haT : L.actionW s ∈ T) :
    L.mem s (scA (L.actionW s)) ∈ Ac :=
  hB.sact _ haT (Or.inr (Or.inr (Or.inl rfl))) (hB.act haT)

theorem BoundInv.idleA (hB : BoundInv st T Ac s) (hiT : L.idleW s ∈ T) :
    L.mem s (scA (L.idleW s)) ∈ Ac :=
  hB.sact _ hiT (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hB.idle

theorem BoundInv.qA (hB : BoundInv st T Ac s) {t : U64} (ht : t ∈ T)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64) : L.mem s (scA t) ∈ Ac :=
  hB.sact t ht (Or.inl hq) (hB.q t ht hq)

theorem BoundInv.rA (hB : BoundInv st T Ac s) {t : U64} (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64) : L.mem s (scA t) ∈ Ac :=
  hB.sact t ht (Or.inr (Or.inl hr)) (hB.r t ht hr)

/-- `BoundInv` after a queue operation on `t` (its `IN_QUEUES` gets only
flags it had, or `t` is bound). -/
theorem BoundInv.qstep (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) {t : U64}
    (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) (hinq : ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y))
    (ha : L.actionW s' = L.actionW s) (hcur : L.curW s' = L.curW s) (hidle : L.idleW s' = L.idleW s)
    (hq : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA t) ≠ 0#u64)
    (hr : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA t) ≠ 0#u64)
    (hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y))
    (hta : Sch st s' t → L.mem s (scA t) ≠ 0#u64 → Sch st s t ∨ L.mem s (scA t) ∈ Ac) : BoundInv st T Ac s' := by
  refine hB.mk' hsc (fun y hy hf => ?_) (fun y hy hf => ?_) (fun haT => ?_) ?_ (fun h0 => ?_)
    (hB.nb hidle (hst _ h.idleT)) (fun y hy hS h0 => ?_)
  · by_cases e : y = t
    · subst e; exact hq hf
    · rw [hinq y hy e] at hf; exact Or.inl hf
  · by_cases e : y = t
    · subst e; exact hr hf
    · rw [hinq y hy e] at hf; exact Or.inr (Or.inl hf)
  · rw [ha] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [hidle]; exact ⟨h.idleT, hB.idle⟩
  · rw [ha] at h0; rw [hcur]; exact ⟨h.curT, hB.resume h0⟩
  · by_cases e : y = t
    · subst e; exact hta hS h0
    · exact Or.inl (Sch.of_eq (fun hf => by rwa [hinq y hy e] at hf) (fun hf => by rwa [hinq y hy e] at hf)
        ha hidle hcur (hst y hy) hS)

/-- `BoundInv.qstep` with the new flags of `t` justified by an old flag or a
bound active SC. -/
theorem BoundInv.qstep' (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) {t : U64}
    (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) (hinq : ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y))
    (ha : L.actionW s' = L.actionW s) (hcur : L.curW s' = L.curW s) (hidle : L.idleW s' = L.idleW s)
    (hq : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        (L.mem s (scA t) ≠ 0#u64 ∧ L.mem s (scA t) ∈ Ac))
    (hr : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        (L.mem s (scA t) ≠ 0#u64 ∧ L.mem s (scA t) ∈ Ac))
    (hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) (ht : t ∈ T) : BoundInv st T Ac s' := by
  have cv : ∀ {P : Prop}, (P ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
      (L.mem s (scA t) ≠ 0#u64 ∧ L.mem s (scA t) ∈ Ac)) →
      (P ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨ L.mem s (scA t) ≠ 0#u64) := fun h =>
    h.imp_right (Or.imp_right And.left)
  refine hB.qstep h hsc hinq ha hcur hidle (fun hf => cv (hq hf)) (fun hf => cv (hr hf)) hst fun hS h0 => ?_
  have hs := hst t ht
  unfold Sch at hS
  rw [ha, hidle, hcur, hs] at hS
  rcases hS with hf | hf | hS
  · rcases hq hf with e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inr e.2
  · rcases hr hf with e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inr e.2
  · exact Or.inl (Or.inr (Or.inr hS))

/-- `BoundInv` under writes to free words. -/
theorem BoundInv.free {Ω : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    (hw : WritesIn st s s' (L.Free s Ω Cs)) : BoundInv st T Ac s' := by
  have hT := h.tcbs
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (hm | ⟨c, hc, o, ho, e⟩)
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
    · exact node_ne_field (h.nodes c hc) (by simp only [LowFree] at ho; omega) hy (hT y hy) hK e.symm
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ LowFree o.val →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 hro
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned (h.nodes _ h.cur) ho h8) ?_
    rintro (hm | ⟨c', hc', o', ho', e⟩)
    · exact out_ne_node (h.omega _ hm) h.cur (h.nodes _ h.cur) ho rfl
    · by_cases ec : L.cpu s = c'
      · subst ec
        have := congrArg UScalar.val e
        rw [nodeAt_val (h.nodes _ h.cur) ho, nodeAt_val (h.nodes _ h.cur) (by simp only [LowFree] at ho'; omega)] at this
        exact hro (by have : o.val = o'.val := by omega
                      rw [this]; exact ho')
      · exact nodeAt_ne_cpu (h.nodes _ h.cur) (h.nodes _ hc') ho (by simp only [LowFree] at ho'; omega) ec e
  have hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp)
  have hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp)
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega) (by rw [act_val]) (by simp [act_val, LowFree])
  have ec : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega) (by rw [curth0]) (by simp [curth0, LowFree])
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega) (by rw [idle8]) (by simp [idle8, LowFree])
  refine hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hinq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hinq y hy]; exact hf))) (fun haT => ?_) ?_ (fun h0 => ?_)
    (hB.nb ei (by rw [stA_eq]; exact fld _ h.idleT _ (by simp) (by simp)))
    (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hinq y hy] at hf) (fun hf => by rwa [hinq y hy] at hf)
      ea ei ec (by rw [stA_eq]; exact fld _ hy _ (by simp) (by simp)) hS))
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ei]; exact ⟨h.idleT, hB.idle⟩
  · rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩

theorem field_wr_node (h : SchedQueuesInvX st T Cs Ω H X s Q R) {c o v y K : U64} (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
  L.mem_wr_ne (nodeAt_aligned (h.nodes c hc) ho h8) (field_aligned (h.tcbs y hy) hK hK8)
    (fun e => node_ne_field (h.nodes c hc) ho hy (h.tcbs y hy) hK (UScalar.eq_of_val_eq e))

/-- `BoundInv` after a write to a current-core node word: `v` must be
bound where the word is the action or the current thread. -/
theorem BoundInv.wr_node (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) {o v : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h8' : o.val ≠ 8)
    (hact : o.val = 16 → (v ∈ T → L.mem s (scA v) ≠ 0#u64) ∧
      (v = 0#u64 → L.mem s (scA (L.curW s)) ≠ 0#u64 ∧ L.mem s (scA (L.curW s)) ∈ Ac))
    (hcur : o.val = 0 → v ∈ T ∧ (L.actionW s = 0#u64 → L.mem s (scA v) ≠ 0#u64))
    (hva : o.val = 16 ∨ o.val = 0 → v ∈ T → L.mem s (scA v) ≠ 0#u64 → Sch st s v ∨ L.mem s (scA v) ∈ Ac) :
    BoundInv st T Ac (L.wr s (L.nodeAt s (L.cpu s) o) v) := by
  have hN' := h.nodes _ h.cur
  have fl : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 => field_wr_node h h.cur ho h8 hy hK hK8
  have hsc : ∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fl y hy _ (by simp) (by simp)
  have hinq : ∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fl y hy _ (by simp) (by simp)
  have rd : ∀ o' : U64, o'.val < 4288 → o'.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) o) v)
        (L.cpu (L.wr s (L.nodeAt s (L.cpu s) o) v)) o') =
      if o.val = o'.val then v else L.mem s (L.nodeAt s (L.cpu s) o') := fun o' ho' h8o' => by
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact rd_node_wr_node hN' ho ho' h8 h8o'
  have ea := rd layout.node.SCHED_ACTION (by rw [act_val]; omega) (by rw [act_val])
  have ec := rd layout.node.CUR_THREAD (by rw [curth0]; omega) (by rw [curth0])
  have ei := rd layout.node.IDLE_THREAD (by rw [idle8]; omega) (by rw [idle8])
  rw [act_val] at ea; rw [curth0] at ec; rw [idle8] at ei
  have ea' : L.actionW (L.wr s (L.nodeAt s (L.cpu s) o) v) = if o.val = 16 then v else L.actionW s := ea
  have ec' : L.curW (L.wr s (L.nodeAt s (L.cpu s) o) v) = if o.val = 0 then v else L.curW s := ec
  have ei' : L.idleW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.idleW s := by
    unfold LawfulStore.idleW; rw [ei, if_neg h8']
  refine hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hinq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hinq y hy]; exact hf))) (fun haT => ?_) ?_ (fun h0 => ?_)
    (hB.nb ei' (by rw [stA_eq]; exact fl _ h.idleT _ (by simp) (by simp))) (fun y hy hS h0 => ?_)
  rotate_right
  · have hs' : L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (stA y) = L.mem s (stA y) := by
      rw [stA_eq]; exact fl _ hy _ (by simp) (by simp)
    unfold Sch at hS
    rw [ea', ec', ei', hs', hinq y hy] at hS
    by_cases e16 : o.val = 16
    · rw [if_pos e16, if_neg (by omega)] at hS
      rcases hS with h1 | h1 | h1 | h1 | ⟨h1, h2⟩ | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inl h1))
      · subst h1; exact hva (Or.inl e16) hy h0
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · subst h2; exact Or.inr ((hact e16).2 h1).2
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))
    · rw [if_neg e16] at hS
      by_cases e0 : o.val = 0
      · rw [if_pos e0] at hS
        rcases hS with h1 | h1 | h1 | h1 | ⟨-, h1⟩ | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (Or.inl h1))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h1))))
        · subst h1; exact hva (Or.inr e0) hy h0
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))
      · rw [if_neg e0] at hS; exact Or.inl hS
  · rw [ea'] at haT ⊢
    by_cases e : o.val = 16
    · rw [if_pos e] at haT ⊢; exact ⟨haT, (hact e).1 haT⟩
    · rw [if_neg e] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ei']; exact ⟨h.idleT, hB.idle⟩
  · rw [ea'] at h0; rw [ec']
    by_cases e : o.val = 16
    · rw [if_pos e] at h0
      rw [if_neg (by omega)]; exact ⟨h.curT, ((hact e).2 h0).1⟩
    · rw [if_neg e] at h0
      by_cases e0 : o.val = 0
      · rw [if_pos e0]; exact ⟨(hcur e0).1, (hcur e0).2 h0⟩
      · rw [if_neg e0]; exact ⟨h.curT, hB.resume h0⟩

end bound

/-! ## The scheduler steps -/

section steps
variable {Cs Sg : Set U64} {Z : U64 → Nat}

theorem p128 : ∀ o : Nat, 128 ≤ o → o ≠ 0 ∧ o ≠ 8 ∧ o ≠ 16 ∧ o ≠ 24 ∧ o ≠ 88 ∧ o ≠ 104 ∧ o ≠ 112 := fun o h => by omega
theorem prel : ∀ o : Nat, RelOffs o → o ≠ 0 ∧ o ≠ 8 ∧ o ≠ 16 ∧ o ≠ 24 ∧ o ≠ 88 ∧ o ≠ 104 ∧ o ≠ 112 := fun o h => by
  unfold RelOffs at h; omega

theorem rd_cur_node {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {o o' v : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (ho' : o'.val < 4288) (h8' : o'.val % 8 = 0) (hne : o.val ≠ o'.val) :
    L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) o) v)
      (L.cpu (L.wr s (L.nodeAt s (L.cpu s) o) v)) o') = L.mem s (L.nodeAt s (L.cpu s) o') := by
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  rw [rd_node_wr_node (h.nodes _ h.cur) ho ho' h8 h8', if_neg hne]

/-- The common post-condition of the steps. -/
structure Post (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Ac : Set U64) (s s' : S) : Prop where
  inv : ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R'
  bnd : BoundInv st T Ac s'
  fr : Fr st T Sg s s'

/-- Thread states are kept and no release flag gets set. -/
def Keeps (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧
  (∀ y ∈ T, (L.mem s' (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64)

theorem Keeps.refl (s : S) : Keeps st T s s := ⟨fun _ _ => rfl, fun _ _ h => h⟩
theorem Keeps.trans {s₁ s₂ s₃ : S} (h₁ : Keeps st T s₁ s₂) (h₂ : Keeps st T s₂ s₃) : Keeps st T s₁ s₃ :=
  ⟨fun y hy => (h₂.1 y hy).trans (h₁.1 y hy), fun y hy hf => h₁.2 y hy (h₂.2 y hy hf)⟩

theorem sched.enqueue.sch (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem s (stA t)))
    (hbd : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ≠ 0#u64)
    (hba : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ∈ Ac) :
    sched.enqueue st s t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  refine WP.spec_mono (WP.spec_and (sched.enqueue.inv s t Q R h ht hr hrun)
    (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
      (fun h0 => h.notQ ht h0 hc hp))) ?_
  rintro s' ⟨h1, hw, hinq⟩
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h.memT hc hp hw
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hS hW hc ht p128 hw
  obtain ⟨hsb, -, -⟩ := ext_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw
  have rf : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · exact hf
    · rw [or_qq_qr] at hf; exact hf
  refine ⟨⟨⟨_, _, h1⟩, hB.qstep h f.sc hi ea ec ei ?_ (fun hf => Or.inr (Or.inl (rf hf))) (fun y hy => (hsb y hy).1)
    (fun _ _ => ?_), f⟩, ea, ec, fun y hy => (hsb y hy).1, fun y hy hf => ?_⟩
  · intro hf; rw [hinq] at hf
    by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl e
    · exact Or.inr (Or.inr (hbd (not_not.1 e)))
  · by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl (Or.inl e)
    · exact Or.inr (hba (not_not.1 e))
  · by_cases e : y = t
    · subst e; exact rf hf
    · rw [hi y hy e] at hf; exact hf

theorem sched.append.sch (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem s (stA t)))
    (hbd : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ≠ 0#u64)
    (hba : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → L.mem s (scA t) ∈ Ac) :
    sched.append st s t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  refine WP.spec_mono (WP.spec_and (sched.append.inv s t Q R h ht hr hrun)
    (sched.append.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
      (fun h0 => h.notQ ht h0 hc hp))) ?_
  rintro s' ⟨h1, hw, hinq⟩
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h.memT hc hp hw
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hS hW hc ht p128 hw
  obtain ⟨hsb, -, -⟩ := ext_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw
  have rf : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · exact hf
    · rw [or_qq_qr] at hf; exact hf
  refine ⟨⟨⟨_, _, h1⟩, hB.qstep h f.sc hi ea ec ei ?_ (fun hf => Or.inr (Or.inl (rf hf))) (fun y hy => (hsb y hy).1)
    (fun _ _ => ?_), f⟩, ea, ec, fun y hy => (hsb y hy).1, fun y hy hf => ?_⟩
  · intro hf; rw [hinq] at hf
    by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl e
    · exact Or.inr (Or.inr (hbd (not_not.1 e)))
  · by_cases e : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
    · exact Or.inl (Or.inl e)
    · exact Or.inr (hba (not_not.1 e))
  · by_cases e : y = t
    · subst e; exact rf hf
    · rw [hi y hy e] at hf; exact hf

theorem sched.dequeue.sch (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  refine WP.spec_mono (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
      (h.queued t ht).1)) ?_
  rintro s' ⟨h1, hw, hinq⟩
  have hW : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hS hW hc ht p128 hw
  obtain ⟨hsb, -, -⟩ := ext_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw
  have q1 : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qq_qq] at hf; exact absurd rfl hf
    · exact hf
  have r1 : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qq_qr] at hf; exact hf
    · exact hf
  refine ⟨⟨⟨_, _, h1⟩, hB.qstep h f.sc hi ea ec ei ?_ ?_ (fun y hy => (hsb y hy).1)
    (fun hS _ => Or.inl (Sch.of_eq q1 r1 ea ei ec (hsb t ht).1 hS)), f⟩, ea, ec⟩
  · intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qq_qq] at hf; exact absurd rfl hf
    · exact Or.inl hf
  · intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inl hf)

theorem sched.release_remove.sch (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
  have hc := h.aff t ht
  refine WP.spec_mono (WP.spec_and (sched.release_remove.inv s t Q R h ht)
    (sched.release_remove.foot s t _ h.tcbs ht (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc)
      (h.released t ht).1)) ?_
  rintro s' ⟨h1, hw, hinq⟩
  have hW : ∀ w ∈ R (L.mem s (affA t)), w ∈ T := fun w hw => h.memTR hc hw
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hS hW hc ht prel hw
  obtain ⟨hsb, -, -⟩ := ext_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw
  have q1 : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qr_qq] at hf; exact hf
    · exact hf
  have r1 : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qr_qr] at hf; exact absurd rfl hf
    · exact hf
  refine ⟨⟨⟨_, _, h1⟩, hB.qstep h f.sc hi ea ec ei ?_ ?_ (fun y hy => (hsb y hy).1)
    (fun hS _ => Or.inl (Sch.of_eq q1 r1 ea ei ec (hsb t ht).1 hS)), f⟩, ea, ec, fun y hy => (hsb y hy).1⟩
  · intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qr_qq] at hf; exact Or.inl hf
    · exact Or.inl hf
  · intro hf; rw [hinq] at hf
    split_ifs at hf with e
    · rw [andn_qr_qr] at hf; exact absurd rfl hf
    · exact Or.inr (Or.inl hf)

theorem sched.set_action.sch (s : S) (v : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s)
    (hv : v = 0#u64 ∨ v = 1#u64 ∨ v ∈ T) (hv2 : v ∈ T → Runnable (L.mem s (stA v)) ∧ ∀ c ∈ Cs, v ∉ R c)
    (hb1 : v ∈ T → L.mem s (scA v) ≠ 0#u64)
    (hb0 : v = 0#u64 → L.mem s (scA (L.curW s)) ≠ 0#u64 ∧ L.mem s (scA (L.curW s)) ∈ Ac)
    (hva : v ∈ T → L.mem s (scA v) ∈ Ac) :
    sched.set_action st s v ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.actionW s' = v ∧ L.curW s' = L.curW s ∧
      Keeps st T s s' ⦄ := by
  refine WP.spec_mono (sched.set_action.spec s v) fun s' s'_post => ?_
  subst s'_post
  obtain ⟨h1, e⟩ := inv_set_action h hv hv2
  have hB1 := hB.wr_node h (o := layout.node.SCHED_ACTION) (v := v) (by rw [act_val]; omega) (by rw [act_val])
    (by rw [act_val]; omega) (fun _ => ⟨hb1, hb0⟩) (fun e => by rw [act_val] at e; omega)
    (fun _ hv _ => Or.inr (hva hv))
  have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := v) h hS h.cur (by rw [act_val]; omega) (by rw [act_val])
    (hto := ⟨by rw [act_val]; omega, by rw [act_val]; omega⟩)
    (fun _ => by rw [act_val]; omega)
  have ec := rd_cur_node (v := v) h (by rw [act_val]; omega) (by rw [act_val]) (by rw [curth0]; omega) (by rw [curth0])
    (by rw [act_val, curth0]; omega)
  have kp : Keeps st T s (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) := by
    refine ⟨fun y hy => ?_, fun y hy hf => ?_⟩
    · rw [stA_eq]; exact field_wr_node h h.cur (by rw [act_val]; omega) (by rw [act_val]) hy (by simp) (by simp)
    · rw [inqA_eq, field_wr_node h h.cur (by rw [act_val]; omega) (by rw [act_val]) hy (by simp) (by simp)] at hf
      exact hf
  exact ⟨⟨⟨Q, R, h1⟩, hB1, f⟩, e, ec, kp⟩

theorem sched.set_reprogram.sch (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.set_reprogram st s ⦃ s' => (SchedQueuesInv st T Cs Ω H s' Q R ∧ BoundInv st T Ac s' ∧ Fr st T Sg s s') ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ⦄ := by
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  refine WP.spec_mono (sched.set_reprogram.spec s) fun s' s'_post => ?_
  subst s'_post
  have hw : WritesIn st s (L.wr s (L.nodeA s layout.node.REPROGRAM) 1#u64) (L.Free s Ω Cs) :=
    free_node_write rfl h.cur (h.nodes _ h.cur) (by simp [rp, LowFree])
  have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := 1#u64) h hS h.cur (by rw [rp]; omega) (by rw [rp]) (fun _ => by rw [rp]; omega)
    ⟨by rw [rp]; omega, by rw [rp]; omega⟩
  have ea := rd_cur_node (v := 1#u64) h (by rw [rp]; omega) (by rw [rp]) (by rw [act_val]; omega) (by rw [act_val])
    (by rw [act_val, rp]; omega)
  have ec := rd_cur_node (v := 1#u64) h (by rw [rp]; omega) (by rw [rp]) (by rw [curth0]; omega) (by rw [curth0])
    (by rw [curth0, rp]; omega)
  exact ⟨⟨inv_of_free h hw, hB.free h hw, f⟩, ea, ec⟩

theorem Post.trans {s s1 s2 : S} (f1 : Fr st T Sg s s1) (h2 : Post st T Cs Ω H Sg Ac s1 s2) : Post st T Cs Ω H Sg Ac s s2 :=
  ⟨h2.inv, h2.bnd, f1.trans h2.fr⟩

theorem one_notT {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) : (1#u64) ∉ T := notT_small h.tcbs (by simp)

theorem sched.reschedule_required.sch (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.reschedule_required st s ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.actionW s' = 1#u64 ∧
      L.curW s' = L.curW s ∧ Keeps st T s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => Post st T Cs Ω H Sg Ac s s1 ∧ L.curW s1 = L.curW s ∧ Keeps st T s s1) ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        have hbd : L.mem s (scA act) ≠ 0#u64 := by
          have := hB.act (act_post ▸ hT); rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact WP.spec_mono (sched.enqueue.sch s act Q R h hB hS hT (fun _ => hb ‹_›) (fun _ => hrun)
            (fun _ => hbd) (fun _ => hB.sact act hT (Or.inr (Or.inr (Or.inl act_post.symm))) hbd))
            fun s1 h1 => ⟨h1.1, h1.2.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, rfl, Keeps.refl _⟩
      · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, rfl, Keeps.refl _⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, rfl, Keeps.refl _⟩
  · rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, ec1, k1⟩
    rw [choose_val]
    refine WP.spec_mono (sched.set_action.sch s1 1#u64 Q1 R1 h1 hB1 (hS.fr f1) (Or.inr (Or.inl rfl))
      (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
      (fun hT => absurd hT (one_notT h)))
      fun s2 h2 => ⟨Post.trans f1 h2.1, h2.2.1, h2.2.2.1.trans ec1, k1.trans h2.2.2.2⟩

/-- seL4 `possibleSwitchTo` keeps the invariants (the thread is bound: the
code checks its SC). -/
theorem sched.possible_switch_to.sch (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (ht : t ∈ T)
    (hrun : Runnable (L.mem s (stA t))) (hta : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    sched.possible_switch_to st s t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ⦄ := by
  unfold sched.possible_switch_to
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, rfl, Keeps.refl _⟩
  rename_i hi0
  have hbd : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  step with sched.in_release_queue.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, rfl, Keeps.refl _⟩
  rename_i hb
  have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 :=
    not_not.1 (fun hc => hb (by rw [b_post]; exact decide_eq_true hc))
  have enq : ∀ s1 Q1 R1, SchedQueuesInv st T Cs Ω H s1 Q1 R1 → BoundInv st T Ac s1 → Fr st T Sg s s1 →
      L.curW s1 = L.curW s → Keeps st T s s1 →
      sched.enqueue st s1 t ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.curW s' = L.curW s ∧ Keeps st T s s' ⦄ := by
    intro s1 Q1 R1 h1 hB1 f1 ec1 k1
    have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hc
      exact hc (by have := mt (k1.2 t ht) (not_not.2 hr0); exact not_not.1 this)
    exact WP.spec_mono (sched.enqueue.sch s1 t Q1 R1 h1 hB1 (hS.fr f1) ht (fun _ => hr1)
      (fun _ => (k1.1 t ht) ▸ hrun) (fun _ => by rw [f1.sc t ht]; exact hbd)
      (fun _ => by rw [f1.sc t ht]; exact hta hbd))
      fun s' h' => ⟨Post.trans f1 h'.1, h'.2.2.1.trans ec1, k1.trans h'.2.2.2⟩
  unfold sched.cur_domain
  step with obj.ks_get.spec as ⟨i1, _⟩
  step with obj.Tcb.domain.spec as ⟨i2, _⟩
  split
  · exact enq s Q R h hB (Fr.refl _ _) rfl (Keeps.refl _)
  step with obj.Tcb.affinity.spec as ⟨i3, _⟩
  step with LawfulStore.cur_cpu_spec as ⟨i4, _⟩
  split
  · exact enq s Q R h hB (Fr.refl _ _) rfl (Keeps.refl _)
  step with sched.action.spec as ⟨i5, _⟩
  split
  · refine WP.spec_bind (sched.reschedule_required.sch s Q R h hB hS) ?_
    rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, -, ec1, k1⟩
    exact enq s1 Q1 R1 h1 hB1 f1 ec1 k1
  · exact WP.spec_mono (sched.set_action.sch s t Q R h hB hS (Or.inr (Or.inr ht))
      (fun _ => ⟨hrun, fun c hc => h.notR ht hr0 hc⟩) (fun _ => hbd)
      (fun e => absurd (e ▸ ht) (notT_small h.tcbs (by simp))) (fun _ => hta hbd)) fun s' h' => ⟨h'.1, h'.2.2.1, h'.2.2.2⟩

/-- The release-queue loop of seL4 `awaken`. -/
theorem sched.awaken_loop.sch (s : S) (fuel : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.awaken_loop st s fuel ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.curW s' = L.curW s ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => Post st T Cs Ω H Sg Ac s x.1 ∧ L.curW x.1 = L.curW s)
  · rintro ⟨s1, fu⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, ec1⟩
    have hS1 := hS.fr f1
    unfold sched.awaken_loop.body
    step*
    all_goals try exact ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, ec1⟩
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    refine WP.spec_bind (sched.release_remove.sch s1 i1 Q1 R1 h1 hB1 hS1 hT1) ?_
    rintro s2 ⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, -, ec2, hst2⟩
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [hst2 i1 hT1]; exact h1.runR _ h1.cur i1 hmem
    have hrel : (L.mem s1 (inqA i1) &&& sched.Q_RELEASE) ≠ 0#u64 := (h1.released i1 hT1).2 (by rw [h1.inR _ h1.cur i1 hmem]; exact hmem)
    refine WP.spec_bind (sched.possible_switch_to.sch s2 i1 Q2 R2 h2 hB2 (hS1.fr f2) hT1 hrun (fun h0 => by
      rw [f2.sc i1 hT1] at h0 ⊢; exact hB1.sact i1 hT1 (Or.inr (Or.inl hrel)) h0)) ?_
    rintro s3 ⟨⟨hi3, hB3, f3⟩, ec3, -⟩
    simp only [WP.spec_ok]
    exact ⟨⟨hi3, hB3, f1.trans (f2.trans f3)⟩, ec3.trans (ec2.trans ec1), by omega⟩
  · exact ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, rfl⟩

/-! ## `next_domain`: writes to the kernel-global area (part of `Ω`) -/

@[step] theorem obj.ks_set.spec (s : S) (o v : U64) :
    obj.ks_set st s o v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v ⦄ := by
  unfold obj.ks_set; step*; simp_all

@[step] theorem layout.ks.DOM_SCHEDULE.spec : layout.ks.DOM_SCHEDULE ⦃ _ => True ⦄ := by
  unfold layout.ks.DOM_SCHEDULE; step*

@[step] theorem sched.dom_sched_duration.spec (s : S) (i : U64) : sched.dom_sched_duration st s i ⦃ _ => True ⦄ := by
  unfold sched.dom_sched_duration; step*

@[step] theorem sched.dom_sched_domain.spec (s : S) (i : U64) : sched.dom_sched_domain st s i ⦃ _ => True ⦄ := by
  unfold sched.dom_sched_domain; step*

theorem ks_wr_cur_node {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {o o' v : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0)
    (ho' : o'.val < 4288) (h8' : o'.val % 8 = 0) :
    L.mem (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v)
      (L.nodeAt (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v)
        (L.cpu (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v)) o') = L.mem s (L.nodeAt s (L.cpu s) o') := by
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  have hN' := h.nodes _ h.cur
  refine L.mem_wr_ne (ks_aligned h ho h8) (nodeAt_aligned hN' ho' h8') ?_
  rw [ks_val h ho, nodeAt_val hN' ho']; simp only [LawfulStore.nodeBase]; omega

/-- One write to the kernel-global area. -/
theorem ks_set.sch (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) {o v : U64}
    (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    obj.ks_set st s o v ⦃ s' => (SchedQueuesInv st T Cs Ω H s' Q R ∧ BoundInv st T Ac s' ∧ Fr st T Sg s s') ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ⦄ := by
  refine WP.spec_mono (obj.ks_set.spec s o v) fun s' s'_post => ?_
  subst s'_post
  have hw : WritesIn st s (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v) (L.Free s Ω Cs) :=
    (writesIn_wr (ks_aligned h ho h8)).mono fun b hb => Or.inl (hb ▸ hS.ksΩ o ho h8)
  exact ⟨⟨inv_of_free h hw, hB.free h hw, fr_ks h hS ho h8⟩,
    ks_wr_cur_node h ho h8 (by rw [act_val]; omega) (by rw [act_val]),
    ks_wr_cur_node h ho h8 (by rw [curth0]; omega) (by rw [curth0])⟩

/-- seL4 `nextDomain`. -/
theorem sched.next_domain.sch (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.next_domain st s ⦃ s' => Post st T Cs Ω H Sg Ac s s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ⦄ := by
  unfold sched.next_domain
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨idx, _⟩
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> step*) fun idx1 _ => ?_
  refine WP.spec_bind (ks_set.sch s Q R h hB hS (o := layout.ks.DOM_SCHED_IDX) (v := idx1)
    (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])) ?_
  rintro s1 ⟨⟨h1, hB1, f1⟩, ea1, ec1⟩
  refine WP.spec_bind (sched.set_reprogram.sch s1 Q R h1 hB1 (hS.fr f1)) ?_
  rintro s2 ⟨⟨h2, hB2, f2⟩, ea2, ec2⟩
  refine WP.spec_bind (ks_set.sch s2 Q R h2 hB2 ((hS.fr f1).fr f2) (o := layout.ks.WORK_UNITS) (v := 0#u64)
    (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])) ?_
  rintro s3 ⟨⟨h3, hB3, f3⟩, ea3, ec3⟩
  have hS3 := ((hS.fr f1).fr f2).fr f3
  step with sched.dom_sched_domain.spec as ⟨d⟩
  step with sched.dom_sched_duration.spec as ⟨t⟩
  refine WP.spec_bind (ks_set.sch s3 Q R h3 hB3 hS3 (o := layout.ks.CUR_DOMAIN) (v := d)
    (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])) ?_
  rintro s4 ⟨⟨h4, hB4, f4⟩, ea4, ec4⟩
  refine WP.spec_mono (ks_set.sch s4 Q R h4 hB4 (hS3.fr f4) (o := layout.ks.DOMAIN_TIME) (v := t)
    (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])) ?_
  rintro s5 ⟨⟨h5, hB5, f5⟩, ea5, ec5⟩
  exact ⟨⟨⟨Q, R, h5⟩, hB5, f1.trans (f2.trans (f3.trans (f4.trans f5)))⟩,
    ea5.trans (ea4.trans (ea3.trans (ea2.trans ea1))), ec5.trans (ec4.trans (ec3.trans (ec2.trans ec1)))⟩

/-- `is_schedulable` says yes only for a runnable, bound thread outside the
release queue. -/
theorem sched.is_schedulable.spec' (s : S) (t : obj.Tcb) :
    sched.is_schedulable st s t ⦃ b => b = true → Runnable (L.mem s (stA t)) ∧ L.mem s (scA t) ≠ 0#u64 ∧
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.rmax s (L.mem s (scA t)) ≠ 0#u64 ⦄ := by
  unfold sched.is_schedulable
  refine WP.spec_bind (sched.is_runnable.spec s t) ?_
  intro b bh
  have hb : b = true → Runnable (L.mem s (stA t)) := by
    intro h
    unfold Runnable
    apply of_decide_eq_true
    exact bh.symm.trans h
  split
  · step with obj.Tcb.sc.spec as ⟨i, i_post⟩
    step with obj.Sc.is_null.spec as ⟨b1, b1_post⟩
    split
    · simp
    rename_i hb1
    have hi : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
    step with sporadic.sc_active.val as ⟨b2, b2_post⟩
    split
    · step with sched.in_release_queue.spec as ⟨b3, b3_post⟩
      try simp only [WP.spec_ok]
      intro e
      refine ⟨hb ‹_›, hi, ?_, by rw [← i_post]; exact b2_post ‹_›⟩
      have : b3 = false := by simpa using e
      rw [b3_post] at this
      exact not_not.1 (fun hc => by simp [hc] at this)
    · simp
  · simp

end steps

end

end Fl4Proofs.P1
