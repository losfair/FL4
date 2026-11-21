/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive ∧ NtfnScB across
`handle_recv`** (sl2 handoff 4, second part; spec side only).

* NtfnScB across the receive side: `nb_completeSignal`, `nb_receiveSignal`
  (sl2's `sln_*` without the names: the notification written is the one read,
  `maybe_donate_sc` by sl2's `nb_maybeDonateSc`), `nb_receiveIpc` (the family
  with `nb_completeSignal` as a leaf).
* **`sl_handleRecv`**: pre sl2's `SAP I [ct] [ct] False ct` with the current
  thread, post `SLN I []` (il2's `il_handleRecv` skeleton; the receiver `ct` is
  named: sl2's `sl_receiveIpc` / `sln_receiveSignal` with `ct ∈ K`).
-/
import Fl4Proofs.P3.SpecInvSlE
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## NtfnScB on the receive side -/

/-- The donation core without the names. -/
theorem nb_donateCore {α : Type} {t n : ObjRef} {a : Notification} {g : Ntfn → Ntfn} {u : UserMonad α}
    {σ : State Unit} (hn : σ.kheap n = some (.notification a)) (hσ : NtfnScB σ)
    {y1 : α × State Unit} (hy1 : y1 ∈ (asUser (Z := Unit) t u σ).1)
    {y2 : Unit × State Unit} (hy2 : y2 ∈ (setNotification (Z := Unit) n (ntfnObjUpdate g a) y1.2).1)
    {y3 : Unit × State Unit} (hy3 : y3 ∈ (maybeDonateSc (Z := Unit) t n y2.2).1) : NtfnScB y3.2 := by
  have h1 : NtfnScB y1.2 := nb_asUser _ _ σ hσ y1 hy1
  have hn1 : y1.2.kheap n = some (.notification a) := ntfnAt_asUser t n a u σ hn y1 hy1
  have h2 : NtfnScB y2.2 :=
    nb_setSimpleKo_p _ _ _ y1.2 (fun o0 h0 => by rw [hn1] at h0; cases h0; rfl) h1 y2 hy2
  exact nb_maybeDonateSc t n y2.2 h2 y3 hy3

theorem nb_completeSignal (n t : ObjRef) : NBK (completeSignal (Z := Unit) n t) := by
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
    have h3 := nb_donateCore hk hσ hy1 hy2 hy3
    refine (?_ : NBK _) y3.2 h3 y hy
    refine ik_bind (nb_getTcbObjRef _ _) fun sc => ?_
    nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_completeSignal _ _)

theorem nb_receiveSignal (thread : ObjRef) (cap : Cap) (blk : Bool) :
    NBK (receiveSignal (Z := Unit) thread cap blk) := by
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
    · exact nb_receiveSignalBlocked _ _ _ σ hσ y hy
    · exact nb_receiveSignalBlocked _ _ _ σ hσ y hy
    · obtain ⟨y1, hy1, hy⟩ := hy
      obtain ⟨y2, hy2, hy⟩ := hy
      obtain ⟨y3, hy3, hy⟩ := hy
      exact (by nb_auto : NBK _) y3.2 (nb_donateCore hk hσ hy1 hy2 hy3) y hy
  all_goals (intro σ _ y hy; dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)

theorem nb_receiveIpc (thread : ObjRef) (cap : Cap) (blk : Bool) (rc : Cap) :
    NBK (receiveIpc (Z := Unit) thread cap blk rc) := by
  unfold receiveIpc; nb_auto

/-! ## `handle_recv` -/

section R
variable {I : ObjRef × ObjRef}

macro "sap_e" : tactic => `(tactic| exact sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto))

set_option maxHeartbeats 8000000 in
theorem sl_handleRecv (ct : ObjRef) (blk canReply : Bool) :
    HK (fun s => SAP I [ct] [ct] False ct s ∧ s.curThread = ct) (SLN I []) (handleRecv (Z := Unit) blk canReply) := by
  have hct : ct ∈ [ct] := List.mem_singleton_self _
  have hRIP : ∀ c rc, HK (SAP I [ct] [ct] False ct) (SLN I []) (receiveIpc (Z := Unit) ct c blk rc) :=
    fun c rc s hs z hz => ⟨sl_mono (sl_receiveIpc ct c blk rc hct s hs z hz) (fun _ h => by cases h),
      nb_receiveIpc ct c blk rc s hs.2.2 z hz⟩
  have hRS : ∀ c, HK (SAP I [ct] [ct] False ct) (SLN I []) (receiveSignal (Z := Unit) ct c blk) :=
    fun c s hs z hz => let h := sln_receiveSignal (I := I) (K := [ct]) ct c blk hct s ⟨hs.1.1, hs.2.2⟩ z hz;
      ⟨sl_mono h.1 (fun _ h => by cases h), h.2⟩
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = ct := hσ.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : SAP I [ct] [ct] False ct y2.2 := (?_ : IK (SAP I [ct] [ct] False ct) _) σ hσ.1 y2 h2
  · refine hk_catch (I := SAP I [ct] [ct] False ct) (Q0 := SLN I []) ?_ (fun e => ?_) y2.2 hb2 y hy
    · (try dsimp only)
      refine hkr_bind (by sap_e) (fun epCap => ?_)
      (try dsimp only)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (by sap_e) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
          · refine hkr_bind (by sap_e) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
        · exact hkr_throw _
      · (try dsimp only)
        split
        · refine hkr_bind (by sap_e) (fun bt => ?_)
          (try dsimp only)
          split
          · exact hkr_liftE (hRS _)
          · exact hkr_throw _
        · exact hkr_throw _
      · exact hkr_throw _
    · intro s hs z hz
      exact ⟨sl_mono (sl_handleFault ct e s hs z hz) (fun _ h => by cases h), nb_handleFault ct e s hs.2.2 z hz⟩
  · sap_e

end R

end

end Fl4Proofs.P3.SInvL
