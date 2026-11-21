/-
P3 (DESIGN.md §9), invariant line G3 (g3b / g3e): **`JAtZ.signal_atN`**,
ScSignalJ's `signalJHyp_of` at one `JAtZ` state with `NativeScope` there: the
`RunningVM` bound-thread case is absurd, so no `SignalRestJHyp`. Written by
g3b in XTopJointMRPath; moved here unchanged by g3e (a pointwise copy, so
ScSignalJ's cone is untouched) so that the older IRQ handlers
(XTopJointIrq, XTopJointIrqZR, XTopJointIrqZI) and the KEntry13P / 23P
notification leaf (`notifLeafJN`) can use it.
-/
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.IpcLeaves
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **ScSignalJ's `signalJHyp_of` at one `JAtZ` state with `NativeScope`** (g3b):
the `RunningVM` bound-thread case is absurd there, so no `SignalRestJHyp`. -/
theorem JAtZ.signal_atN (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ)
    (n badge : U64) (hn : n ∈ Z.N) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  obtain ⟨x, hk, hx⟩ := J.xtop.ipc.toN.ntfn n hn
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hP1 := P1.notification.send_signal.tinv hAT s a n badge J.blk hnH (hNt n hnH)
  -- the badge-only branches
  have post : ∀ (y : Fl4Spec.Notification), (∀ l, x.ntfnObj ≠ .waitingNtfn l) → (∀ l, y.ntfnObj ≠ .waitingNtfn l) →
      y.ntfnBoundTcb = x.ntfnBoundTcb → y.ntfnSc = x.ntfnSc →
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), updK σ n.bv (.notification y))}, False) →
      notification.send_signal st arI s a n badge ⦃ r => r.2 = a ∧
        SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ (Fl4Spec.sendSignal n.bv badge.bv σ) r.1 ⦄ →
      notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
        (Lst' : U64 → List U64) (D' : Set U64),
        Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
    intro y hxw hyw hyb hys hspec hI
    refine WP.spec_mono (WP.spec_and hI hP1) ?_
    rintro ⟨s', a'⟩ ⟨⟨ea, hrel⟩, hb⟩
    try simp only [WP.uncurry'_pair] at hb
    subst ea
    obtain ⟨σ', V', h1, h2, J'⟩ := J.signal_badge_post hn hk hxw hyw hyb hys hspec hrel hb
    exact ⟨σ', V', Ac, Lst, D, h1, h2, J'⟩
  have hI := J.xtop.irelK J.ks J.buf
  cases ho : x.ntfnObj with
  | activeNtfn b0 =>
    exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn (Fl4Spec.combineNtfnBadges badge.bv b0)) x)
      (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
      (sendSignal_active_eq hk ho badge.bv) (send_signal_activeI (ar := arI) J.ip s a σ hI.1 hn hk ho badge)
  | waitingNtfn l =>
    exact J.signal_waitDJ hAT hmb hn hk ho badge
  | idleNtfn =>
    cases hb : x.ntfnBoundTcb with
    | none =>
      exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x)
        (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
        (sendSignal_activate hk ho (Or.inl hb) badge.bv)
        (send_signal_idle_unboundI (ar := arI) J.ip s a σ hI.1 hn hk ho hb badge)
    | some t =>
      obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
      obtain ⟨tcb, hkt, -⟩ := hI.1.tcb _ (hx.bound_mem hb0)
      rw [hbt] at hkt
      by_cases hrb : Fl4Spec.receiveBlocked tcb.tcbState = true
      · exact J.signal_boundDJ hAT hmb hn hk ho (t := L.mem s (nBoundA n)) (by rw [hbt]; exact hb)
          (by rw [hbt]; exact hkt) hrb
          badge
      by_cases hvm : tcb.tcbState = .runningVM
      · exact absurd hvm (hN t tcb hkt)
      have hrb' : Fl4Spec.receiveBlocked tcb.tcbState = false := by simpa using hrb
      exact post (Fl4Spec.ntfnObjUpdate (fun _ => .activeNtfn badge.bv) x)
        (by rw [ho]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
        (sendSignal_activate hk ho (Or.inr ⟨t, tcb, hb, hkt, hrb'⟩) badge.bv)
        (send_signal_idle_bound_idleI (ar := arI) J.ip s a σ hI.1 hn hk ho hb hkt hrb' hvm badge)

end

end

end Fl4Proofs.P3
