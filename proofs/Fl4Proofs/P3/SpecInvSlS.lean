/-
P3 (DESIGN.md §9), invariant line G1 (sl2): **ScLive and NtfnScB across the
signals** (sl1 handoff 1, the `maybe_donate_sc` callers; spec side only).

`maybe_donate_sc t n` donates the notification `n`'s SC: it is live by
`NtfnScB` (its notification is `n`, so `sc_ntfn ≠ None`), hence named
(`nsc_of`); the woken thread `t` is in `K`:

* `complete_signal` / `receive_signal` (active notification): the receiver,
  given in `K` (the current thread at the callers);
* `update_waiting_ntfn`: the head of the notification's queue (NtfnQB: a queued
  thread is BlockedOnNotification, so live, so named by IfLiveT: il2's
  `il_ntfnQueue`);
* `send_signal` to a bound receiver: the receiver read BlockedOnReceive, live.

The notification writes read-modify-write the notification read at the start
(`asUser` in between writes a TCB only: `ntfnAt_asUser`), so they keep its SC
pointer (`nb_setSimpleKo_p`): `nb_completeSignal`, `nb_receiveSignal`,
`nb_sendSignal`.
-/
import Fl4Proofs.P3.SpecInvSlM
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

section Sig
variable {I : ObjRef × ObjRef} {K L : List ObjRef}

/-- The notification's SC is named. -/
theorem nsc_of {σ : State Unit} (h : SL I K σ) (hb : NtfnScB σ) (n : ObjRef) : NSc I n σ := by
  intro ntf c hn hc
  obtain ⟨y, k, hy, hyn⟩ := hb n ntf c hn hc
  exact nm_of_live h.1 hy (Or.inr (Or.inl (by rw [hyn]; simp)))

/-- `as_user` writes a TCB only: a notification stays. -/
theorem ntfnAt_asUser {α : Type} (t p : ObjRef) (a : Notification) (u : UserMonad α) :
    IK (fun s : State Unit => s.kheap p = some (.notification a)) (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨b, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (fun hσ y hy => ?_) fun _ => ik_pure _
  obtain ⟨old, -, -, e⟩ := SInvB.mem_setObject hy
  rw [e]
  have htp : p ≠ t := by intro e; subst e; rw [getTcb_kheap hx] at hσ; cases hσ
  show Function.update σ.kheap t _ p = _
  rw [Function.update_of_ne htp]; exact hσ

/-- SL with NtfnScB. -/
def SLN (I : ObjRef × ObjRef) (K : List ObjRef) (σ : State Unit) : Prop := SL I K σ ∧ NtfnScB σ

theorem sln_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I K m) (h2 : NBK m) : IK (SLN I K) m :=
  fun σ h x hx => ⟨h1 σ h.1 x hx, h2 σ h.2 x hx⟩

/-- The donation core: `as_user`, the notification write of the notification
read (`a` at `n`), `maybe_donate_sc t n` (`t ∈ K`). -/
theorem sln_donateCore {α : Type} {t n : ObjRef} {a : Notification} {g : Ntfn → Ntfn} {u : UserMonad α}
    (ht : t ∈ K) {σ : State Unit} (hn : σ.kheap n = some (.notification a)) (hσ : SLN I K σ)
    {y1 : α × State Unit} (hy1 : y1 ∈ (asUser (Z := Unit) t u σ).1)
    {y2 : Unit × State Unit} (hy2 : y2 ∈ (setNotification (Z := Unit) n (ntfnObjUpdate g a) y1.2).1)
    {y3 : Unit × State Unit} (hy3 : y3 ∈ (maybeDonateSc (Z := Unit) t n y2.2).1) : SLN I K y3.2 := by
  have h1 : SLN I K y1.2 := sln_ik (sl_asUser _ _) (nb_asUser _ _) σ hσ y1 hy1
  have hn1 : y1.2.kheap n = some (.notification a) := ntfnAt_asUser t n a u σ hn y1 hy1
  have h2 : SLN I K y2.2 :=
    ⟨sl_setSimpleKo _ _ _ y1.2 h1.1 y2 hy2,
      nb_setSimpleKo_p _ _ _ y1.2 (fun o0 h0 => by rw [hn1] at h0; cases h0; rfl) h1.2 y2 hy2⟩
  exact ⟨sl_maybeDonateSc t n ht y2.2 ⟨h2.1, nsc_of h2.1 h2.2 n⟩ y3 hy3, nb_maybeDonateSc t n y2.2 h2.2 y3 hy3⟩

/-- **`complete_signal`** to a receiver of `K`. -/
theorem sln_completeSignal (n t : ObjRef) (ht : t ∈ K) : IK (SLN I K) (completeSignal (Z := Unit) n t) := by
  unfold completeSignal
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, e⟩ := mem_getSimpleKo hz
  obtain ⟨a, s⟩ := z
  simp only at hk e; subst s
  dsimp only at hy
  rcases ho : a.ntfnObj with _ | q | bd <;> simp only [ho] at hy
  · exact hy.elim
  · exact hy.elim
  · obtain ⟨y1, hy1, hy⟩ := hy
    obtain ⟨y2, hy2, hy⟩ := hy
    obtain ⟨y3, hy3, hy⟩ := hy
    have h3 := sln_donateCore ht hk hσ hy1 hy2 hy3
    refine (?_ : IK (SLN I K) _) y3.2 h3 y hy
    refine ik_bind (sln_ik (sl_getTcbObjRef _ _) (nb_getTcbObjRef _ _)) fun sc => ?_
    exact sln_ik (by sl_auto) (by nb_auto)

theorem sik_pure_bind {P : State Unit → Prop} {α β : Type} {a : α} {k : α → NonDet (State Unit) β}
    (h : IK P (k a)) : IK P ((pure a : NonDet (State Unit) α) >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hσ x hx

/-- **`receive_signal`** of a receiver of `K`. -/
theorem sln_receiveSignal (thread : ObjRef) (cap : Cap) (blk : Bool) (ht : thread ∈ K) :
    IK (SLN I K) (receiveSignal (Z := Unit) thread cap blk) := by
  unfold receiveSignal
  cases cap
  case notificationCap p bd r =>
    intro σ hσ y hy
    dsimp only at hy
    obtain ⟨z0, hz0, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hz0] at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨hk, e⟩ := mem_getSimpleKo hz
    obtain ⟨a, s⟩ := z
    simp only at hk e; subst s
    dsimp only at hy
    rcases ho : a.ntfnObj with _ | q | bd <;> simp only [ho] at hy
    · exact sln_ik (sl_receiveSignalBlocked _ _ _) (nb_receiveSignalBlocked _ _ _) σ hσ y hy
    · exact sln_ik (sl_receiveSignalBlocked _ _ _) (nb_receiveSignalBlocked _ _ _) σ hσ y hy
    · obtain ⟨y1, hy1, hy⟩ := hy
      obtain ⟨y2, hy2, hy⟩ := hy
      obtain ⟨y3, hy3, hy⟩ := hy
      exact (sln_ik (by sl_auto) (by nb_auto) : IK (SLN I K) _) y3.2 (sln_donateCore ht hk hσ hy1 hy2 hy3) y hy
  all_goals (intro σ _ y hy; dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)

/-- **`update_waiting_ntfn`** of a queue of `K`. -/
theorem sln_updateWaitingNtfn (n : ObjRef) (queue : List ObjRef) (badge : Badge) (hq : ∀ u ∈ queue, u ∈ K) :
    IK (SLN I K) (updateWaitingNtfn (Z := Unit) n queue badge) := by
  cases queue with
  | nil =>
    intro σ _ y hy
    unfold updateWaitingNtfn at hy
    obtain ⟨z, hz, -⟩ := hy
    exact (hz.1 rfl).elim
  | cons a l =>
    have ha : the (a :: l).head? ∈ K := hq a (List.mem_cons_self ..)
    unfold updateWaitingNtfn
    refine ik_bind (ik_assert _) fun _ => ?_
    refine sik_pure_bind ?_
    refine ik_bind (sln_ik (sl_tcbNtfnDequeue _ _) (nb_tcbNtfnDequeue _ _)) fun _ => ?_
    refine ik_bind (sln_ik (sl_setThreadState _ _) (nb_setThreadState _ _)) fun _ => ?_
    refine ik_bind (sln_ik (sl_asUser _ _) (nb_asUser _ _)) fun _ => ?_
    refine ik_bind (fun σ h y hy => ⟨sl_maybeDonateSc _ _ ha σ ⟨h.1, nsc_of h.1 h.2 _⟩ y hy,
      nb_maybeDonateSc _ _ σ h.2 y hy⟩) fun _ => ?_
    exact sln_ik (by sl_auto) (by nb_auto)

/-- A notification written back at the state it was read. -/
theorem sln_setNtfn_same {n : ObjRef} {a : Notification} {g : Ntfn → Ntfn} {σ : State Unit}
    (hn : σ.kheap n = some (.notification a)) (hσ : SLN I K σ) {y : Unit × State Unit}
    (hy : y ∈ (setNotification (Z := Unit) n (ntfnObjUpdate g a) σ).1) : SLN I K y.2 :=
  ⟨sl_setSimpleKo _ _ _ σ hσ.1 y hy, nb_setSimpleKo_p _ _ _ σ (fun o0 h0 => by rw [hn] at h0; cases h0; rfl) hσ.2 y hy⟩

theorem sl_append {σ : State Unit} (h : SL I K σ) : ∀ (q : List ObjRef), (∀ u ∈ q, HasN σ u) → SL I (q ++ K) σ
  | [], _ => h
  | u :: q, hq => sl_cons (sl_append h q fun v hv => hq v (List.mem_cons_of_mem _ hv))
      (Or.inl (hq u (List.mem_cons_self ..)))

theorem live_of_rb {s : ThreadState} (h : receiveBlocked s = true) : liveSt s := by
  cases s <;> simp_all [receiveBlocked, liveSt]

/-- `SLN` with il2's `ILN L` (IfLiveT with NtfnQB ∧ EpQB). -/
def SLI (I : ObjRef × ObjRef) (K L : List ObjRef) (σ : State Unit) : Prop := SLN I K σ ∧ ILN L σ

/-- **`send_signal`**: a waiting queue joins `K` (NtfnQB, IfLiveT); a bound
receiver is read BlockedOnReceive. -/
theorem sln_sendSignal (n : ObjRef) (badge : Badge) :
    HK (SLI I K L) (SLN I K) (sendSignal (Z := Unit) n badge) := by
  unfold sendSignal
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, e⟩ := mem_getSimpleKo hz
  obtain ⟨a, s⟩ := z
  simp only at hk e; subst s
  dsimp only at hy
  have hq0 := il_ntfnQueue hσ.2 hk
  rcases ho : a.ntfnObj with _ | queue | bd' <;> rcases hb : a.ntfnBoundTcb with _ | tcb <;>
    simp only [ho, hb] at hy
  · exact sln_setNtfn_same hk hσ.1 hy
  · -- idle, bound
    unfold getThreadState at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x, hx, rfl⟩ := mem_threadGet hz
    dsimp only at hy
    split at hy
    · rename_i hrb
      have h1 : SLN I (tcb :: K) σ :=
        ⟨sl_cons hσ.1.1 (Or.inl (hasN_of_tc (hσ.2.1.1 tcb x hx (live_of_rb hrb)))), hσ.1.2⟩
      have hm : tcb ∈ tcb :: K := List.mem_cons.2 (Or.inl rfl)
      refine (fun h => ⟨sl_tail h.1, h.2⟩ : SLN I (tcb :: K) y.2 → SLN I K y.2) ((?_ : IK (SLN I (tcb :: K)) _) σ h1 y hy)
      refine ik_bind (sln_ik (sl_cancelIpc _) (nb_cancelIpc _)) fun _ => ?_
      refine ik_bind (sln_ik (sl_setThreadState _ _) (nb_setThreadState _ _)) fun _ => ?_
      refine ik_bind (sln_ik (sl_asUser _ _) (nb_asUser _ _)) fun _ => ?_
      refine ik_bind (fun σ h y hy => ⟨sl_maybeDonateSc _ _ hm σ ⟨h.1, nsc_of h.1 h.2 _⟩ y hy,
        nb_maybeDonateSc _ _ σ h.2 y hy⟩) fun _ => ?_
      exact sln_ik (by sl_auto) (by nb_auto)
    · exact sln_setNtfn_same hk hσ.1 hy
  all_goals first
    | exact sln_setNtfn_same hk hσ.1 hy
    | (rw [ho] at hq0
       have h1 : SLN I (queue ++ K) σ :=
         ⟨sl_append hσ.1.1 queue fun u hu => hasN_of_tc (hq0.2 u (List.mem_append_left _ hu)), hσ.1.2⟩
       have h2 := sln_updateWaitingNtfn n queue badge (fun u hu => List.mem_append_left _ hu) σ h1 y hy
       exact ⟨sl_mono h2.1 fun u hu => List.mem_append_right _ hu, h2.2⟩)

end Sig

end

end Fl4Proofs.P3.SInvL
