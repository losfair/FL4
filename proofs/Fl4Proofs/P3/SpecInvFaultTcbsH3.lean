/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **`B` across the writes that
add a thread to a notification queue** (spec side only): `tcb_ntfn_append`
(the receiver blocks on a notification: it is in `L`, BlockedOnNotification,
and not in `K`) and `reorder_ntfn` (for `set_priority` of a thread read
BlockedOnNotification: no fault, not BoS/BoReply, not in `K`, since the threads
of `K` are not BlockedOnNotification). `receive_signal` / its blocking part
need the receiver in `L`, not exempt and not in `K`.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L E K : List ObjRef} {C : ObjRef → Prop}

theorem opg_mono_S {F : FQ} {S S' : Set ObjRef} {σ : State Unit} (h : OPG F S C σ) (hS : ∀ u ∈ S, u ∈ S') :
    OPG F S' C σ := by
  refine ⟨fun p o hp => ?_, h.2⟩
  have := h.1 p o hp
  cases o with
  | notification n => exact fun u hu => hS u (this u hu)
  | tcb x => exact this
  | _ => trivial

/-- A notification write whose queue holds `t` (no fault, not BoS/BoReply, not
in `K`) and threads queued before. -/
theorem b_setNtfn_add (n : ObjRef) (v : Notification) (t : ObjRef) {σ : State Unit} (hσ : B L E K C σ)
    (hv : ∀ u ∈ v.ntfnObj.ntfnQueue, u = t ∨ queued σ u)
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none ∧ ¬ sndRpl x.tcbState) (hK : t ∉ K)
    {y : Unit × State Unit} (hy : y ∈ (setNotification (Z := Unit) n v σ).1) : B L E K C y.2 := by
  obtain ⟨hb1, hb2, hb3⟩ := hσ
  have hq : ∀ u, queued y.2 u → u = t ∨ queued σ u := fun u hu =>
    queued_of_opg (fg_setSimpleKo (F := fq1) (S := {u | u = t ∨ queued σ u}) (C := C) KernelObject.notification n v hv σ
      (opg_mono_S (opg_queued hb1.2) fun u hu => Or.inr hu) y hy) hu
  refine ⟨fg_setSimpleKo KernelObject.notification n v (fun _ _ => Set.mem_univ _) σ hb1 y hy, fun u hu z hz => ?_,
    fun u hu => ⟨fun hq' => ?_, fun z hz => ?_⟩⟩
  · have h0 : ∀ z, σ.kheap u = some (.tcb z) → z.tcbFault = none ∧ ¬ sndRpl z.tcbState := by
      rcases hq u hu with rfl | h
      · exact ht
      · exact hb2 u h
    exact (fg_setSimpleKo (F := fqT u) (S := Set.univ) KernelObject.notification n v (fun _ _ => Set.mem_univ _) σ
      (opg_fqT hb1.2 h0) y hy).1 u _ hz rfl
  · rcases hq u hq' with rfl | h
    · exact hK hu
    · exact (hb3 u hu).1 h
  · exact (fg_setSimpleKo (F := fqN u) (S := Set.univ) KernelObject.notification n v (fun _ _ => Set.mem_univ _) σ
      (opg_fqN hb1.2 (hb3 u hu).2) y hy).1 u _ hz rfl

theorem mem_tcbAppend {t : ObjRef} {qs : List ObjRef} {σ : State Unit} {y : List ObjRef × State Unit}
    (hy : y ∈ (tcbAppend (Z := Unit) t qs σ).1) : y.2 = σ ∧ ∀ u ∈ y.1, u = t ∨ u ∈ qs := by
  unfold tcbAppend orderedInsert at hy
  obtain ⟨⟨val, σ1⟩, h1, hy⟩ := hy
  obtain ⟨⟨vals, σ2⟩, h2, hy⟩ := hy
  have e1 : σ1 = σ := (ik_getsThe (P := fun s => s = σ) _) σ rfl _ h1
  have e2 : σ2 = σ1 := (ik_mapM (P := fun s => s = σ1) (fun _ => ik_getsThe _) _) σ1 rfl _ h2
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z', hz', hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz'] at hy
  rw [Set.mem_singleton_iff.1 hy]
  refine ⟨by simp only [e2, e1], fun u hu => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
  rcases List.mem_append.1 hp with hp | hp
  · rcases List.mem_append.1 hp with hp | hp
    · exact Or.inr (List.of_mem_zip ((List.takeWhile_sublist _).subset hp)).1
    · rw [List.mem_singleton.1 hp]; exact Or.inl rfl
  · exact Or.inr (List.of_mem_zip ((List.dropWhile_sublist _).subset hp)).1

/-- `tcb_ntfn_append` of a thread with no fault, not BoS/BoReply, not in `K`. -/
theorem b_tcbNtfnAppend (t n : ObjRef) (hK : t ∉ K) {σ : State Unit} (hσ : B L E K C σ)
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none ∧ ¬ sndRpl x.tcbState)
    {y : Unit × State Unit} (hy : y ∈ (tcbNtfnAppend (Z := Unit) t n σ).1) : B L E K C y.2 := by
  unfold tcbNtfnAppend at hy
  obtain ⟨⟨a, σ1⟩, h1, hy⟩ := hy
  obtain ⟨ha, e1⟩ := mem_getSimpleKo h1
  simp only at ha e1; subst σ1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨⟨qs', σ2⟩, h2, hy⟩ := hy
  obtain ⟨e2, hm⟩ := mem_tcbAppend h2
  simp only at e2 hm; subst σ2
  refine b_setNtfn_add n _ t hσ (fun u hu => ?_) ht hK hy
  rcases hm u hu with h | h
  · exact Or.inl h
  · exact Or.inr ⟨n, a, ha, h⟩

/-- `reorder_ntfn` of a thread with no fault, not BoS/BoReply, not in `K`. -/
theorem b_reorderNtfn (n t : ObjRef) (hK : t ∉ K) {σ : State Unit} (hσ : B L E K C σ)
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none ∧ ¬ sndRpl x.tcbState)
    {y : Unit × State Unit} (hy : y ∈ (reorderNtfn (Z := Unit) n t σ).1) : B L E K C y.2 := by
  unfold reorderNtfn at hy
  obtain ⟨⟨a, σ1⟩, h1, hy⟩ := hy
  obtain ⟨ha, e1⟩ := mem_getSimpleKo h1
  simp only at ha e1; subst σ1
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨⟨qs', σ2⟩, h2, hy⟩ := hy
  obtain ⟨e2, hm⟩ := mem_tcbAppend h2
  simp only at e2 hm; subst σ2
  refine b_setNtfn_add n _ t hσ (fun u hu => ?_) ht hK hy
  rcases hm u hu with h | h
  · exact Or.inl h
  · exact Or.inr ⟨n, a, ha, removeAll_sub h⟩


/-! ## The receiver blocks on a notification -/

theorem b_receiveSignalBlocked (t n : ObjRef) (blk : Bool) (hL : t ∈ L) (hE : t ∉ E) (hK : t ∉ K) :
    BK L E K C (receiveSignalBlocked (Z := Unit) t n blk) := by
  unfold receiveSignalBlocked
  split
  · intro σ hσ y ⟨y1, h1, hy⟩
    have hb1 := b_setThreadState (L := L) (E := E) (K := K) (C := C) t (.blockedOnNotification n)
      (Or.inr (Or.inl hL)) (fun h => absurd h hK) (Or.inl fun h => h) (fun h => absurd h hE) σ hσ y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    refine (by b_auto : BK L E K C (maybeReturnSc (Z := Unit) n t)) _ (b_tcbNtfnAppend t n hK hb1 (fun z hz =>
      ⟨(hb1.1.1 t _ hz).2.1 hL, by rw [sts_post h1 z hz]; exact fun h => h⟩) h2) y hy
  · b_auto

theorem b_receiveSignal (t : ObjRef) (cap : Cap) (blk : Bool) (hL : t ∈ L) (hE : t ∉ E) (hK : t ∉ K) :
    BK L E K C (receiveSignal (Z := Unit) t cap blk) := by
  unfold receiveSignal
  split
  · refine ik_pure_bind ?_
    refine ik_bind (by b_auto) fun a => ?_
    split
    · b_auto
    · exact b_receiveSignalBlocked _ _ _ hL hE hK
  · intro σ _ y ⟨z, hz, _⟩; exact hz.elim

/-! ## `receive_ipc` -/

/-- A thread read BlockedOnSend / BlockedOnReply is in no notification queue. -/
theorem ikp_bconsK {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α} {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hs : sndRpl x.tcbState) (hn : ¬ isBoN x.tcbState)
    (hm : BK L E (t :: K) C m) : IKp (B L E K C) σ m := by
  intro hσ y hy
  have h3 : ∀ u ∈ t :: K, ¬ queued σ u ∧ ∀ z, σ.kheap u = some (.tcb z) → ¬ isBoN z.tcbState := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · refine ⟨fun hq => (hσ.2.1 u hq x hx).2 hs, fun z hz => ?_⟩
      rw [hx] at hz; cases hz; exact hn
    · exact hσ.2.2 u hu
  exact b_mono (hm σ ⟨hσ.1, hσ.2.1, h3⟩ y hy) (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h) id

macro_rules | `(tactic| b_rd) => `(tactic| (show IK _ (getThreadState (Z := Unit) _ >>= _); unfold getThreadState; refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hs : x.tcbState <;> (try dsimp only) <;> first | (refine ikp_bconsK hx (by rw [hs]; trivial) (by rw [hs]; exact fun h => h) ?_) | (refine ikp_bcons (fun hσ y hy => by rw [hx] at hy; cases hy; exact b_noFault hσ hx (by rw [hs]; exact fun h => h) (by rw [hs]; exact fun h => h)) ?_) | (refine ikp_of_ik ?_ σ)))

/-- `reply_push` of a caller in no queue (IK form). -/
theorem b_replyPushK (caller callee r : ObjRef) (d : Bool) (hK : caller ∈ K) :
    BK L E K C (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| (with_reducible refine b_replyPushK _ _ _ _ ?_; simp_all))

theorem b_receiveIpcBlocked (blk : Bool) (t ep : ObjRef) (r : Option ObjRef) (hL : t ∈ L) (hE : t ∉ E) :
    BK L E K C (receiveIpcBlocked (Z := Unit) blk t ep r) := by
  unfold receiveIpcBlocked
  split
  · refine ik_bind (b_setThreadState _ _ (Or.inr (Or.inl hL)) (fun _ h => h) (Or.inl fun h => h)
      (fun h => absurd h hE)) fun _ => ?_
    b_auto
  · b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| (with_reducible refine b_receiveIpcBlocked _ _ _ _ ?_ ?_ <;> simp_all))


end

end Fl4Proofs.P3.SInv
