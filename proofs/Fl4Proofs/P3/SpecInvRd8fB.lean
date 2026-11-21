/-
P3 (DESIGN.md §9), invariant line G1 (rd8f): **the deletion cone keeps `Rdy`**,
part 2: `fast_finalise`, `finalise_cap`, `cap_delete_one` (spec side only,
outside the JAtZ cone).

The facts read at the start of a finalisation: `FH := Rdy ∧ NQ [] ∧ T1 ∧
Simple ∧ ScInv` (ctq's `T1` / `Simple`, nq2's queues, sb2's `ScInv`), and,
for a final SC cap, that its SC is not the idle SC (the cap is held: sg1 /
vi3's `IdleScOutV`, supplied by part 3).

* Reply arm: the TCB read BlockedOnReply goes to rd8d's `rd_replyRemove`
  (a BlockedOnReply caller is not `BlkR`); any other state to `rd_cancelIpc`.
* Thread arm: `unbind_notification`, then `unbind_from_sc` (rd3's
  `rd_schedContextUnbindTcb_p` with `T1` / `Simple` carried across the
  notification unbind: q1 / nsw leaves), `suspend`, `prepare_thread_delete`.
* SC arm (final): `sched_context_unbind_all_tcbs` (rd3, `T1` / `Simple`); after
  it sl3's `scd1` gives `sc_tcb = None` (the SC is not idle) and sb2's `ScInv`
  (`ScBackS`) that no TCB is bound to the SC; the three unbinders keep every
  TCB's binding (`SVS`) and the idle SC (`isk`), so rd3's
  `rd_schedContextSetInactive_p` applies.
-/
import Fl4Proofs.P3.SpecInvRd8fA
import Fl4Proofs.P3.SpecInvSbG2
import Fl4Proofs.P3.SpecInvSlI3
import Fl4Proofs.P3.SpecInvSlD2
open Classical

namespace Fl4Proofs.P3.SInvR.B8f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-- The facts a finalisation reads at its start. -/
abbrev FH (s : State Unit) : Prop := Rdy s ∧ NQ [] s ∧ T1 s ∧ Simple s ∧ SInvB.ScInv s

/-- `Rdy` at every outcome from an `FH` state. -/
def RDf {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ, FH σ → ∀ y ∈ (m σ).1, Rdy y.2

theorem rdf_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IK Rdy m) : RDf m :=
  fun σ hσ y hy => h σ hσ.1 y hy

theorem rdf_ro_bind {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : ∀ σ0, IK (· = σ0) m) (hk : ∀ a, RDf (k a)) : RDf (m >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  have e : z.2 = σ := cq5_ro hm hz
  exact hk z.1 z.2 (e ▸ hσ) y hy

theorem rdf_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : RDf m) :
    RDf (NonDet.when P m) := by
  intro σ hσ y hy
  unfold NonDet.when at hy
  split at hy
  · exact h σ hσ y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

theorem rdf_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : RDf m) :
    RDf (NonDet.liftM g m) := by
  intro σ hσ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hy]; exact h σ hσ z hz

theorem rdf_threadGet_bind {β γ : Type} {f : Tcb → β} {t : ObjRef} {k : β → NonDet (State Unit) γ}
    (h : ∀ σ x, σ.kheap t = some (.tcb x) → FH σ → ∀ y ∈ (k (f x) σ).1, Rdy y.2) :
    RDf (threadGet (Z := Unit) f t >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  exact h σ x hx hσ y hy

/-- The reply arm after the reply's TCB read (a macro: the spec's own `match`). -/
macro "rdf_reply_arm" : tactic => `(tactic| (
  refine rdf_threadGet_bind fun σ x hx hσ => ?_
  cases hs : x.tcbState <;> dsimp only
  case blockedOnReply r' =>
    exact fun y hy => B8d.rd_replyRemove _ r' σ hσ.1 hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.1.2
      (fun x' hx' => by rw [hx] at hx'; cases hx'; rw [hs]; exact nb_blk (ts := .blockedOnReply r') trivial _) hy
  all_goals exact fun y hy => rd_cancelIpc _ σ hσ.1 y hy))

/-- The notification arm. -/
theorem rdf_ntfnArm (r : ObjRef) : RDf (do
    schedContextMaybeUnbindNtfn (Z := Unit) r
    unbindMaybeNotification (Z := Unit) r
    cancelAllSignals (Z := Unit) r) := by
  intro σ hσ y ⟨z1, hz1, ⟨z2, hz2, hy⟩⟩
  have q1 : RQ z1.2 := ⟨rd_schedContextMaybeUnbindNtfn r σ hσ.1 z1 hz1,
    nq_schedContextMaybeUnbindNtfn (Kq := []) r σ hσ.2.1 z1 hz1⟩
  have q2 : RQ z2.2 := ⟨rd_unbindMaybeNotification r z1.2 q1.1 z2 hz2,
    nq_unbindMaybeNotification (Kq := []) r z1.2 q1.2 z2 hz2⟩
  exact (rdq_cancelAllSignals r z2.2 q2 y hy).1

theorem rdf_cancelAllIpc (r : ObjRef) : RDf (cancelAllIpc (Z := Unit) r) :=
  fun σ hσ y hy => (rdq_cancelAllIpc r σ ⟨hσ.1, hσ.2.1⟩ y hy).1

/-- **`fast_finalise`** from `FH`. -/
theorem rdf_fastFinalise (c : Cap) (fin : Bool) : RDf (fastFinalise (Z := Unit) c fin) := by
  cases c
  case nullCap => simp only [fastFinalise]; exact rdf_of_ik (ik_pure _)
  case replyCap r _ =>
    simp only [fastFinalise]
    refine rdf_when _ ?_
    refine rdf_ro_bind (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun tp => ?_
    cases tp with
    | none => exact rdf_of_ik (ik_pure _)
    | some tp =>
      dsimp only
      unfold getThreadState
      rdf_reply_arm
  case endpointCap r _ _ => simp only [fastFinalise]; exact rdf_when _ (rdf_cancelAllIpc r)
  case notificationCap r _ _ => simp only [fastFinalise]; exact rdf_when _ (rdf_ntfnArm r)
  all_goals (simp only [fastFinalise]; exact rdf_of_ik ik_fail)

/-- **`cap_delete_one`** from `FH`. -/
theorem rdf_capDeleteOne (slot : CslotPtr) : RDf (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne
  refine rdf_ro_bind (fun _ => by unfold getCap; repeat' (first | ik_step0 | ik_unfold)) fun cap => ?_
  intro σ hσ y hy
  unfold NonDet.unless at hy
  split at hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1
  · obtain ⟨z, hz, hy⟩ := hy
    have e : z.2 = σ := cq5_ro (fun _ => by unfold isFinalCap; repeat' (first | ik_step0 | ik_unfold)) hz
    obtain ⟨z2, hz2, hy⟩ := hy
    have r2 : Rdy z2.2 := rdf_fastFinalise cap z.1 z.2 (e ▸ hσ) z2 hz2
    exact rd_emptySlot slot _ z2.2 r2 y hy

/-! ## `unbind_from_sc` -/

theorem simple_hA {σ : State Unit} (hA : Simple σ) (sc : ObjRef) :
    ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → t ≠ σ.curThread →
      σ.schedulerAction ≠ .switchThread t := fun _ _ t _ _ _ => hA t

theorem rd_unbindFromSc (t : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : T1 σ) (hA : Simple σ)
    {y : Unit × State Unit} (hy : y ∈ (unbindFromSc (Z := Unit) t σ).1) : Rdy y.2 := by
  unfold unbindFromSc at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, -, rfl⟩ := q1_mem_threadGet hz
  obtain ⟨z2, hz2, hy⟩ := hy
  have r2 : Rdy z2.2 := by
    revert hz2
    cases x.tcbSchedContext with
    | none => intro h; rw [Set.mem_singleton_iff.1 h]; exact hR
    | some sc => intro h; exact rd_schedContextUnbindTcb_p sc σ h1 (simple_hA hA sc) hR z2 h
  revert hy
  cases x.tcbSchedContext with
  | none => intro h; rw [Set.mem_singleton_iff.1 h]; exact r2
  | some sc =>
    intro h
    exact (show IK Rdy (do
      let sc' ← getSchedContext (Z := Unit) sc
      NonDet.maybeM completeYieldTo sc'.scYieldFrom) by
        refine ik_bind (by unfold getSchedContext; repeat' (first | ik_step0 | ik_unfold)) fun sc' => ?_
        cases sc'.scYieldFrom with
        | none => exact ik_pure _
        | some u => exact rd_completeYieldTo u) z2.2 r2 y h

/-! ## The SC arm -/

theorem sv_schedContextUnbindNtfn' (sc : ObjRef) : SVK.SVM (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; sv_auto

theorem sv_schedContextUnbindReply' (sc : ObjRef) : SVK.SVM (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; sv_auto

theorem sv_schedContextUnbindYieldFrom' (sc : ObjRef) : SVK.SVM (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; sv_auto

/-- No TCB bound to `p`, kept along `SVS`. -/
theorem unb_svs {s s' : State Unit} {p : ObjRef} (h : ∀ t x, s.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some p)
    (hS : SVK.SVS s s') : ∀ t x, s'.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some p := by
  intro t x hx hc
  have e := hS.1 t
  rw [hx] at e
  obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap t) (a := some p) (by rw [← e]; simp [SVK.sv, hc])
  exact h t y hy hys

/-- **A final SC cap's finalisation** (not the idle SC). -/
theorem rd_finSc (p : ObjRef) (σ : State Unit) (hσ : FH σ) (hI : p ≠ σ.idleSc)
    {z1 z2 z3 z4 y : Unit × State Unit}
    (hz1 : z1 ∈ (schedContextUnbindAllTcbs (Z := Unit) p σ).1)
    (hz2 : z2 ∈ (schedContextUnbindNtfn (Z := Unit) p z1.2).1)
    (hz3 : z3 ∈ (schedContextUnbindReply (Z := Unit) p z2.2).1)
    (hz4 : z4 ∈ (schedContextUnbindYieldFrom (Z := Unit) p z3.2).1)
    (hy : y ∈ (schedContextSetInactive (Z := Unit) p z4.2).1) : Rdy y.2 := by
  have r1 : Rdy z1.2 := rd_schedContextUnbindAllTcbs_p p σ hσ.2.2.1 (simple_hA hσ.2.2.2.1 p) hσ.1 z1 hz1
  have si1 : SInvB.ScInv z1.2 := SInvB.si_schedContextUnbindAllTcbs p σ hσ.2.2.2.2 z1 hz1
  have sb1 := SInvL.scd1_unbindAllTcbs (I2 := σ.idleSc) (p := p) σ rfl z1 hz1
  have i1 : z1.2.idleSc = σ.idleSc := SInvL.isk_schedContextUnbindAllTcbs (N := σ.idleSc) p σ rfl z1 hz1
  have hn1 : ∀ t x, z1.2.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some p := by
    intro t x hx hc
    obtain ⟨y, k, hy, hyt, -⟩ := si1.1.1 t x p hx hc
    obtain ⟨y', n', hy', hq⟩ := sb1
    rw [hy] at hy'; cases hy'
    rcases hq with hq | hq
    · rw [hq] at hyt; cases hyt
    · exact hI hq
  have r2 := rd_schedContextUnbindNtfn p z1.2 r1 z2 hz2
  have r3 := rd_schedContextUnbindReply p z2.2 r2 z3 hz3
  have r4 := rd_schedContextUnbindYieldFrom p z3.2 r3 z4 hz4
  have hS : SVK.SVS z1.2 z4.2 := ((sv_schedContextUnbindNtfn' p z1.2 z2 hz2).trans
    (sv_schedContextUnbindReply' p z2.2 z3 hz3)).trans (sv_schedContextUnbindYieldFrom' p z3.2 z4 hz4)
  have i4 : z4.2.idleSc = σ.idleSc := by
    have i2 := SInvL.isk_schedContextUnbindNtfn (N := σ.idleSc) p z1.2 i1 z2 hz2
    have i3 := SInvL.isk_schedContextUnbindReply (N := σ.idleSc) p z2.2 i2 z3 hz3
    exact SInvL.isk_schedContextUnbindYieldFrom (N := σ.idleSc) p z3.2 i3 z4 hz4
  exact rd_schedContextSetInactive_p p z4.2 (unb_svs hn1 hS) (by rw [i4]; exact hI) r4 y hy

/-! ## `finalise_cap` -/

/-- **`finalise_cap`** from `FH`, an SC cap's SC not the idle SC. -/
theorem rdf_finaliseCap (c : Cap) (fin : Bool) (σ : State Unit) (hσ : FH σ)
    (hI : ∀ p b, c = .schedContextCap p b → p ≠ σ.idleSc) :
    ∀ y ∈ (finaliseCap (Z := Unit) c fin σ).1, Rdy y.2 := by
  cases c
  case replyCap r _ =>
    simp only [finaliseCap]
    refine rdf_liftM _ (rdf_when _ ?_) σ hσ
    refine rdf_ro_bind (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun tp => ?_
    cases tp with
    | none => exact rdf_of_ik (ik_pure _)
    | some tp =>
      dsimp only
      unfold getThreadState
      rdf_reply_arm
  case endpointCap r _ _ =>
    simp only [finaliseCap]; exact rdf_liftM _ (rdf_when _ (rdf_cancelAllIpc r)) σ hσ
  case notificationCap r _ _ =>
    simp only [finaliseCap]; exact rdf_liftM _ (rdf_when _ (rdf_ntfnArm r)) σ hσ
  case threadCap r =>
    simp only [finaliseCap]
    intro y ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, hy⟩
    have r1 : Rdy z1.2 := ik_when _ (rd_unbindNotification r) σ hσ.1 z1 hz1
    have t1 : T1 z1.2 := ik_when _ (q1_unbindNotification r) σ hσ.2.2.1 z1 hz1
    have a1 : Simple z1.2 := fun u => ik_when _
      (show IK (P12.NSw u) (unbindNotification (Z := Unit) r) by unfold unbindNotification; p12_nsw_auto)
      σ (hσ.2.2.2.1 u) z1 hz1
    have r2 : Rdy z2.2 := by
      unfold NonDet.when at hz2
      split at hz2
      · exact rd_unbindFromSc r z1.2 r1 t1 a1 hz2
      · rw [Set.mem_singleton_iff.1 hz2]; exact r1
    have r3 : Rdy z3.2 := ik_when _ (rd_suspend r) z2.2 r2 z3 hz3
    have r4 : Rdy z4.2 := ik_when _ (rd_prepareThreadDelete r) z3.2 r3 z4 hz4
    rw [Set.mem_singleton_iff.1 hy]; exact r4
  case schedContextCap p b =>
    cases fin
    · simp only [finaliseCap, NonDet.when, Bool.false_eq_true, ↓reduceIte]
      intro y hy
      obtain ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, z5, hz5, hy⟩ := hy
      simp only [Set.mem_singleton_iff] at hz1 hz2 hz3 hz4 hz5 hy
      subst hz1 hz2 hz3 hz4 hz5 hy
      exact hσ.1
    · simp only [finaliseCap, NonDet.when, ↓reduceIte]
      intro y ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, z5, hz5, hy⟩
      rw [Set.mem_singleton_iff.1 hy]
      exact rd_finSc p σ hσ (hI p b rfl) hz1 hz2 hz3 hz4 hz5
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    split
    · intro y ⟨z, hz, hy⟩
      rw [Set.mem_singleton_iff.1 hy]
      unfold deletingIrqHandler getIrqSlot at hz
      obtain ⟨w, hw, hz⟩ := hz
      have e : w.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
      exact rdf_capDeleteOne _ w.2 (e ▸ hσ) z hz
    · exact rdf_of_ik (ik_pure _) σ hσ
  case zombie r b n =>
    simp only [finaliseCap]
    exact rdf_of_ik (by repeat' (first | ik_step0 | ik_unfold)) σ hσ
  case archObjectCap a =>
    simp only [finaliseCap]
    exact rd_archFinaliseCap a fin σ hσ.1
  all_goals (simp only [finaliseCap]; exact rdf_of_ik (ik_pure _) σ hσ)

end

end Fl4Proofs.P3.SInvR.B8f
