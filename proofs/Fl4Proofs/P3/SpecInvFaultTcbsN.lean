/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **FaultTcbsS with the
notification-queue invariant, as one carried bundle** (spec side only).

* `NQB σ` (l4v `valid_ntfn`, the part FaultTcbsS needs): a thread in a
  notification queue has no fault and is neither BlockedOnSend nor
  BlockedOnReply. l4v's `valid_ntfn` says it is BlockedOnNotification on that
  notification (`ntfn_q_refs_of` / `st_tcb_at ((=) (BlockedOnNotification n))`)
  and `fault_tcbs_valid_states` gives no fault; the weaker form here is kept by
  a fresh `defaultTcb` (Inactive, no fault) without l4v's untyped-freshness
  chain, which the strong form would need at retype.
* `B L E K C σ`: FaultTcbsS up to the exempt threads `E` (a faulted thread
  may be active while its fault is being sent: `sendFaultIpc`), no fault at
  the threads of `L`, `NQB`, the threads of `K` in no notification queue and
  not BlockedOnNotification, and `C` at the current thread. `B [] [] [] ⊤ σ ↔
  FaultTcbsS σ ∧ NQB σ`.
* `b_of_gf`: every function of the generic frame (SpecInvFaultTcbsG1..G7)
  keeps `B` (notification queues only shrink there, so `NQB`'s threads were
  queued before, and their TCBs keep "no fault, not BoS/BoReply"); the TCB and
  queue writers the frame excludes are leaves here (`b_setThreadState`,
  `b_setFault`, …).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsG7
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-- BlockedOnSend or BlockedOnReply. -/
def sndRpl : ThreadState → Prop
  | .blockedOnSend _ _ => True
  | .blockedOnReply _ => True
  | _ => False

/-- BlockedOnNotification. -/
def isBoN : ThreadState → Prop
  | .blockedOnNotification _ => True
  | _ => False

/-- `t` is in some notification's queue. -/
def queued (σ : State Unit) (t : ObjRef) : Prop :=
  ∃ n x, σ.kheap n = some (.notification x) ∧ t ∈ x.ntfnObj.ntfnQueue

/-- **NQB** (l4v `valid_ntfn`, part): a queued thread has no fault and is not
BlockedOnSend / BlockedOnReply. -/
def NQB (σ : State Unit) : Prop :=
  ∀ t, queued σ t → ∀ y, σ.kheap t = some (.tcb y) → y.tcbFault = none ∧ ¬ sndRpl y.tcbState

/-- FaultTcbsS up to the exempt threads `E` (active or holding a fault state;
an active one may have a fault while it is being sent), and no fault at the
threads of `L`. -/
def fqX (L E : List ObjRef) : FQ where
  R p f s := (f ≠ none → faultTcbSt s ∨ (p ∈ E ∧ activeSt s)) ∧ (p ∈ L → f = none) ∧
    (p ∈ E → activeSt s ∨ faultTcbSt s)
  clr _ _ _ h := ⟨fun h' => absurd rfl h', fun _ => rfl, h.2.2⟩
  st _ _ _ h := ⟨fun _ => Or.inl trivial, h.2.1, fun _ => Or.inr trivial⟩
  dflt _ := ⟨fun h' => absurd rfl h', fun _ => rfl, fun _ => Or.inr trivial⟩

/-- At `t`: no fault, not BlockedOnSend / BlockedOnReply. -/
def fqT (t : ObjRef) : FQ where
  R p f s := p = t → f = none ∧ ¬ sndRpl s
  clr _ _ _ h e := ⟨rfl, (h e).2⟩
  st _ _ _ h e := ⟨(h e).1, fun h => h⟩
  dflt _ _ := ⟨rfl, fun h => h⟩

/-- At `t`: not BlockedOnNotification. -/
def fqN (t : ObjRef) : FQ where
  R p _ s := p = t → ¬ isBoN s
  clr _ _ _ h := h
  st _ _ _ _ _ h := h
  dflt _ _ h := h

/-- No constraint. -/
def fq1 : FQ where
  R _ _ _ := True
  clr _ _ _ h := h
  st _ _ _ h := h
  dflt _ := trivial

/-- The carried bundle. -/
def B (L E K : List ObjRef) (C : ObjRef → Prop) (σ : State Unit) : Prop :=
  OPG (fqX L E) Set.univ C σ ∧ NQB σ ∧
    ∀ u ∈ K, ¬ queued σ u ∧ ∀ y, σ.kheap u = some (.tcb y) → ¬ isBoN y.tcbState

abbrev BK {α : Type} (L E K : List ObjRef) (C : ObjRef → Prop) (m : NonDet (State Unit) α) : Prop :=
  IK (B L E K C) m
abbrev BKE {ε α : Type} (L E K : List ObjRef) (C : ObjRef → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  IKE (B L E K C) m

theorem b_nil_iff (σ : State Unit) : B [] [] [] (fun _ => True) σ ↔ FaultTcbsS σ ∧ NQB σ := by
  constructor
  · rintro ⟨⟨h1, -⟩, h2, -⟩
    refine ⟨fun p x hp hf => ?_, h2⟩
    rcases (h1 p _ hp).1 hf with h | ⟨h, -⟩
    · exact h
    · simp at h
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun p o hp => ?_, trivial⟩, h2, fun u hu => by simp at hu⟩
    cases o with
    | tcb x => exact ⟨fun hf => Or.inl (h1 p x hp hf), fun h => by simp at h, fun h => by simp at h⟩
    | notification n => exact fun _ _ => Set.mem_univ _
    | _ => trivial

theorem queued_of_opg {F : FQ} {S : Set ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : OPG F S C σ)
    {t : ObjRef} (ht : queued σ t) : t ∈ S := by
  obtain ⟨n, x, hn, hq⟩ := ht
  exact h.1 n _ hn t hq

/-- At any state: notification queues are the queued threads, and `C`. -/
theorem opg_queued {σ : State Unit} {C : ObjRef → Prop} (hC : C σ.curThread) :
    OPG fq1 {u | queued σ u} C σ := by
  refine ⟨fun p o hp => ?_, hC⟩
  cases o with
  | tcb x => trivial
  | notification n => exact fun t ht => ⟨p, n, hp, ht⟩
  | _ => trivial

theorem opg_fqT {σ : State Unit} {C : ObjRef → Prop} (hC : C σ.curThread) {t : ObjRef}
    (ht : ∀ y, σ.kheap t = some (.tcb y) → y.tcbFault = none ∧ ¬ sndRpl y.tcbState) :
    OPG (fqT t) Set.univ C σ := by
  refine ⟨fun p o hp => ?_, hC⟩
  cases o with
  | tcb x => intro e; subst e; exact ht x hp
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

theorem opg_fqN {σ : State Unit} {C : ObjRef → Prop} (hC : C σ.curThread) {t : ObjRef}
    (ht : ∀ y, σ.kheap t = some (.tcb y) → ¬ isBoN y.tcbState) : OPG (fqN t) Set.univ C σ := by
  refine ⟨fun p o hp => ?_, hC⟩
  cases o with
  | tcb x => intro e; subst e; exact ht x hp
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

/-- The generic frame of a function. -/
abbrev GF {α : Type} (C : ObjRef → Prop) (m : NonDet (State Unit) α) : Prop := ∀ F S, FGK F S C m

/-- The facts a run of a frame function gives, for a start state with `C`. -/
theorem gf_post {α : Type} {C : ObjRef → Prop} {m : NonDet (State Unit) α} (h : GF C m) {σ : State Unit}
    (hC : C σ.curThread) {y : α × State Unit} (hy : y ∈ (m σ).1) :
    (∀ t, queued y.2 t → queued σ t) ∧
    (∀ t, (∀ z, σ.kheap t = some (.tcb z) → z.tcbFault = none ∧ ¬ sndRpl z.tcbState) →
      ∀ z, y.2.kheap t = some (.tcb z) → z.tcbFault = none ∧ ¬ sndRpl z.tcbState) ∧
    (∀ t, (∀ z, σ.kheap t = some (.tcb z) → ¬ isBoN z.tcbState) →
      ∀ z, y.2.kheap t = some (.tcb z) → ¬ isBoN z.tcbState) := by
  refine ⟨fun t ht => queued_of_opg (h fq1 _ σ (opg_queued hC) y hy) ht, fun t ht z hz => ?_,
    fun t ht z hz => ?_⟩
  · exact (h (fqT t) _ σ (opg_fqT hC ht) y hy).1 t _ hz rfl
  · exact (h (fqN t) _ σ (opg_fqN hC ht) y hy).1 t _ hz rfl

/-- **Every function of the generic frame keeps `B`.** -/
theorem b_of_gf {α : Type} {L E K : List ObjRef} {C : ObjRef → Prop} {m : NonDet (State Unit) α}
    (h : GF C m) : BK L E K C m := by
  intro σ ⟨h1, h2, h3⟩ y hy
  obtain ⟨hq, hT, hN⟩ := gf_post h h1.2 hy
  refine ⟨h _ _ σ h1 y hy, fun t ht => hT t (h2 t (hq t ht)), fun u hu => ⟨fun hq' => (h3 u hu).1 (hq u hq'),
    hN u (h3 u hu).2⟩⟩

theorem b_of_gfE {ε α : Type} {L E K : List ObjRef} {C : ObjRef → Prop} {m : NonDetE (State Unit) ε α}
    (h : ∀ F S, FGKE F S C m) : BKE L E K C m := b_of_gf h

/-! ## Weakening -/

theorem b_mono {L L' E K K' : List ObjRef} {C C' : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ)
    (hL : ∀ t ∈ L', t ∈ L) (hK : ∀ t ∈ K', t ∈ K) (hC : C σ.curThread → C' σ.curThread) :
    B L' E K' C' σ := by
  obtain ⟨⟨h1, h1c⟩, h2, h3⟩ := h
  refine ⟨⟨fun p o hp => ?_, hC h1c⟩, h2, fun u hu => h3 u (hK u hu)⟩
  have := h1 p o hp
  cases o with
  | tcb x => exact ⟨this.1, fun hl => this.2.1 (hL _ hl), this.2.2⟩
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

/-- An active (or fault-state) thread becomes exempt. -/
theorem b_addE {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → activeSt x.tcbState ∨ faultTcbSt x.tcbState) :
    B L (t :: E) K C σ := by
  obtain ⟨⟨h1, h1c⟩, h2, h3⟩ := h
  refine ⟨⟨fun p o hp => ?_, h1c⟩, h2, h3⟩
  have := h1 p o hp
  cases o with
  | tcb x =>
    refine ⟨fun hf => ?_, this.2.1, fun he => ?_⟩
    · rcases this.1 hf with h | ⟨he, ha⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_of_mem _ he, ha⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ht x hp
      · exact this.2.2 he
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

/-- A thread with no fault joins `L`. -/
theorem b_cons {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none) : B (t :: L) E K C σ := by
  obtain ⟨⟨h1, h1c⟩, h2, h3⟩ := h
  refine ⟨⟨fun p o hp => ?_, h1c⟩, h2, h3⟩
  have := h1 p o hp
  cases o with
  | tcb x =>
    refine ⟨this.1, fun hl => ?_, this.2.2⟩
    rcases List.mem_cons.1 hl with rfl | hl
    · exact ht x hp
    · exact this.2.1 hl
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

/-- A thread in `L` needs no exemption. -/
theorem b_dropE {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} {t : ObjRef}
    (h : B L (t :: E) K C σ) (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none ∨ faultTcbSt x.tcbState) :
    B L E K C σ := by
  obtain ⟨⟨h1, h1c⟩, h2, h3⟩ := h
  refine ⟨⟨fun p o hp => ?_, h1c⟩, h2, h3⟩
  have := h1 p o hp
  cases o with
  | tcb x =>
    refine ⟨fun hf => ?_, this.2.1, fun he => this.2.2 (List.mem_cons_of_mem _ he)⟩
    rcases this.1 hf with h | ⟨he, ha⟩
    · exact Or.inl h
    · rcases List.mem_cons.1 he with rfl | he
      · rcases ht x hp with h | h
        · exact absurd h hf
        · exact Or.inl h
      · exact Or.inr ⟨he, ha⟩
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

/-- The no-fault fact of a thread whose state holds no fault and is not active. -/
theorem b_noFault {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ) {t : ObjRef}
    {x : Tcb} (hx : σ.kheap t = some (.tcb x)) (hs : ¬ faultTcbSt x.tcbState) (ha : ¬ activeSt x.tcbState) :
    x.tcbFault = none := by
  by_contra hf
  rcases (h.1.1 t _ hx).1 hf with h' | ⟨-, h'⟩
  · exact hs h'
  · exact ha h'

/-- A queued thread has no fault. -/
theorem b_queuedNoFault {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ)
    {n : ObjRef} {x : Notification} (hn : σ.kheap n = some (.notification x)) {t : ObjRef}
    (ht : t ∈ x.ntfnObj.ntfnQueue) : ∀ y, σ.kheap t = some (.tcb y) → y.tcbFault = none :=
  fun y hy => (h.2.1 t ⟨n, x, hn, ht⟩ y hy).1

theorem b_queue_cons {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ)
    {n : ObjRef} {x : Notification} (hn : σ.kheap n = some (.notification x)) :
    B (x.ntfnObj.ntfnQueue ++ L) E K C σ := by
  obtain ⟨⟨h1, h1c⟩, h2, h3⟩ := h
  refine ⟨⟨fun p o hp => ?_, h1c⟩, h2, h3⟩
  have := h1 p o hp
  cases o with
  | tcb y =>
    refine ⟨this.1, fun hl => ?_, this.2.2⟩
    rcases List.mem_append.1 hl with hl | hl
    · exact (h2 p ⟨n, x, hn, hl⟩ y hp).1
    · exact this.2.1 hl
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

/-! ## TCB writers outside the frame -/

/-- `set_thread_state`: the new state is allowed by `fqX` (a fault-holding
state, a thread with no fault, an exempt active one), keeps the threads of `K`
not BlockedOnNotification, and is no BoS/BoReply unless the thread is in no
queue. -/
theorem b_setThreadState {L E K : List ObjRef} {C : ObjRef → Prop} (t : ObjRef) (ts : ThreadState)
    (h1 : faultTcbSt ts ∨ t ∈ L ∨ (t ∈ E ∧ activeSt ts)) (h2 : t ∈ K → ¬ isBoN ts)
    (h3 : ¬ sndRpl ts ∨ t ∈ K) (h4 : t ∈ E → activeSt ts ∨ faultTcbSt ts) :
    BK L E K C (setThreadState (Z := Unit) t ts) := by
  intro σ ⟨hb1, hb2, hb3⟩ y hy
  have hq : ∀ u, queued y.2 u → queued σ u :=
    fun u hu => queued_of_opg (fg_setThreadState (F := fq1) t ts (fun _ _ h => h) σ (opg_queued hb1.2) y hy) hu
  have hft : ∀ f s, (fqX L E).R t f s → (fqX L E).R t f ts := by
    intro f s hR
    refine ⟨fun hf => ?_, hR.2.1, h4⟩
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact absurd (hR.2.1 h) hf
    · exact Or.inr h
  refine ⟨fg_setThreadState (F := fqX L E) (S := Set.univ) t ts hft σ hb1 y hy, fun u hu => ?_,
    fun u hu => ⟨fun hq' => (hb3 u hu).1 (hq u hq'), ?_⟩⟩
  · have hu0 := hq u hu
    have hT : ∀ f s, (fqT u).R t f s → (fqT u).R t f ts := by
      intro f s hR e
      refine ⟨(hR e).1, ?_⟩
      rcases h3 with h | h
      · exact h
      · subst e; exact absurd hu0 (hb3 t h).1
    exact fun z hz => (fg_setThreadState (F := fqT u) (S := Set.univ) t ts hT σ
      (opg_fqT hb1.2 (hb2 u hu0)) y hy).1 u _ hz rfl
  · have hN : ∀ f s, (fqN u).R t f s → (fqN u).R t f ts := by
      intro f s _ e
      subst e; exact h2 hu
    exact fun z hz => (fg_setThreadState (F := fqN u) (S := Set.univ) t ts hN σ
      (opg_fqN hb1.2 (hb3 u hu).2) y hy).1 u _ hz rfl

end

end Fl4Proofs.P3.SInv
