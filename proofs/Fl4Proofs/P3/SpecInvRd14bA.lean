/-
P3 (DESIGN.md §9), invariant line G1 (rd14b, KENTRY-PLAN rd13b handoff 1):
the TCB-binding / SC-kind transfers for the Notification and Endpoint arms
(spec side only).

* `QB t c` (the TCB `t` is bound to `c`), `KS c` (`c` is an SC object), `BL`
  (both). Small walks `qb_auto` / `ks_auto` (`ks_setObject`: `set_object`
  asserts the old and new `a_type` agree). The scheduler callees are not
  re-walked: `BL` is transferred through rd4's heap view (`SInvR.FK`:
  `ik_of_fk`, `bl_possibleSwitchTo` from `SInvR.fk_possibleSwitchTo`) and
  through IpcSchedLift's `ScOnlyK` (only SC objects change, same size:
  `ik_of_nks`, `nks_ifCond`, `nks_schedContextResume`, `bl_ifCond`).
* **`bl_maybeDonateSc`** (the donation binds the receiver `u`, whose SC was
  read `none`, so `u ≠ t` when `t` is bound; the SC's `sc_tcb` was read
  `none`, so `sched_context_donate`'s unbind branch is dead: `bl_donate`).
-/
import Fl4Proofs.P3.SpecInvRd13bC
import Fl4Proofs.P3.IpcSchedLift
import Fl4Proofs.P3.VsDom
open Classical

namespace Fl4Proofs.P3.SInvR.A14b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `t` bound to `c`, `c` an SC -/

/-- The TCB `t` is bound to `c`. -/
abbrev QB (t c : ObjRef) (p : ObjRef) (x : Tcb) : Prop := p = t → x.tcbSchedContext = some c

/-- `c` is an SC object. -/
abbrev KS (c : ObjRef) (σ : State Unit) : Prop := ∃ y n, σ.kheap c = some (.schedContext y n)

/-- `t` bound to `c` and `c` an SC. -/
abbrev BL (t c : ObjRef) (s : State Unit) : Prop := TP (QB t c) s ∧ KS c s

syntax "qb_leaf" : tactic
macro_rules | `(tactic| qb_leaf) => `(tactic| fail "no qb_leaf")

/-- The writers that keep every TCB's SC binding (small callees only). -/
macro "qb_auto" : tactic => `(tactic| repeat' (first
  | qb_leaf
  | ((with_reducible refine tp_asUser _ _ ?_); intro _ _ h; exact h)
  | ((with_reducible refine tp_setMrs _ _ _ ?_); intro _ _ h; exact h)
  | ((with_reducible refine tp_archThreadSet _ _ ?_); intro _ _ h; exact h)
  | (with_reducible exact tp_setSimpleKo _ _ _)
  | ((with_reducible refine tp_threadSet _ _ ?_); intro _ h; exact h)
  | ((with_reducible refine tp_setObject _ _ ?_); intro _ h; cases h; done)
  | ik_step0 | ik_unfold))

/-- A non-CNode `set_object` keeps an SC an SC (`a_type` is asserted). -/
theorem ks_setObject (c p : ObjRef) (o : KernelObject) (ho : ∀ sz cs, o ≠ .cnode sz cs) :
    IK (KS c) (setObject (Z := Unit) p o) := by
  unfold setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨old, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨y0, n0, h0⟩ := hσ
  by_cases e : p = c
  · subst e
    rw [h0] at hk; cases hk
    cases o with
    | schedContext y n => exact ⟨y, n, by simp⟩
    | cnode sz cs => exact absurd rfl (ho sz cs)
    | _ => revert hty; simp only [aType]; split_ifs <;> intro hty <;> cases hty
  · refine ⟨y0, n0, ?_⟩
    dsimp only
    rw [Function.update_of_ne (fun h => e h.symm)]
    exact h0

/-- The walk keeping `KS c` (small callees only). -/
macro "ks_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ks_setObject _ _ _ ?_); intro _ _ h; cases h)
  | ik_step0 | ik_unfold))

/-! ## Transfer through the heap view (`SInvR.FK`) and `Ipc.ScOnlyK` -/

theorem tp_hv {Q : ObjRef → Tcb → Prop} (hQ : ∀ p x y, y.tcbSchedContext = x.tcbSchedContext → Q p y → Q p x)
    {s s' : State Unit} (hk : ∀ q, SInvR.HV (s'.kheap q) = SInvR.HV (s.kheap q)) (h : TP Q s) : TP Q s' := by
  intro p x hx
  have e := hk p
  rw [hx] at e
  obtain ⟨y, hy, hxy⟩ := SInvR.hv_tcb e.symm
  exact hQ p x y (SInvR.hvT_sc hxy) (h p y hy)

theorem ks_hv {c : ObjRef} {s s' : State Unit} (hk : ∀ q, SInvR.HV (s'.kheap q) = SInvR.HV (s.kheap q))
    (h : KS c s) : KS c s' := by
  obtain ⟨y, n, hy⟩ := h
  exact ⟨y, n, (SInvR.hv_sc (hk c)).2 hy⟩

theorem tp_sok {Q : ObjRef → Tcb → Prop} {s s' : State Unit} (hk : Ipc.ScOnlyK s s') (h : TP Q s) : TP Q s' :=
  fun p x hx => h p x (hk.bwd hx fun _ _ e => by cases e)

theorem ks_sok {c : ObjRef} {s s' : State Unit} (hk : Ipc.ScOnlyK s s') (h : KS c s) : KS c s' := by
  obtain ⟨y0, n0, h0⟩ := h
  rcases hk.1 c with e | ⟨y, n, y', a1, a2⟩
  · exact ⟨y0, n0, by rw [e]; exact h0⟩
  · rw [h0] at a1; cases a1; exact ⟨y', _, a2⟩

/-- A family keeping the heap view keeps any heap-view-stable predicate. -/
theorem ik_of_fk {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α}
    (hP : ∀ s s' : State Unit, (∀ q, SInvR.HV (s'.kheap q) = SInvR.HV (s.kheap q)) → P s → P s')
    (h : ∀ K c u T I S, IK (SInvR.FK K c u T I S) m) : IK P m :=
  fun s hs y hy => hP s y.2 (h _ _ _ _ _ _ s (SInvR.fk_self s) y hy).1 hs

/-- `NKS` keeps any `ScOnlyK`-stable predicate. -/
theorem ik_of_nks {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α}
    (hP : ∀ s s' : State Unit, Ipc.ScOnlyK s s' → P s → P s') (h : Ipc.NKS m) : IK P m :=
  fun s hs y hy => hP s y.2 (h s y hy) hs

theorem qb_stab (t c : ObjRef) : ∀ p x y, y.tcbSchedContext = x.tcbSchedContext → QB t c p y → QB t c p x :=
  fun _ _ _ e h he => by rw [← e]; exact h he

theorem bl_of_fk {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ K c u T I S, IK (SInvR.FK K c u T I S) m) : IK (BL t c) m :=
  ik_of_fk (fun _ _ hk h' => ⟨tp_hv (qb_stab t c) hk h'.1, ks_hv hk h'.2⟩) h

theorem bl_of_nks {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : Ipc.NKS m) : IK (BL t c) m :=
  ik_of_nks (fun _ _ hk h' => ⟨tp_sok hk h'.1, ks_sok hk h'.2⟩) h

/-! ## The refill callees change only SCs -/

theorem nks_ifCond (o : Option ObjRef) : Ipc.NKS (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  cases o with
  | none => exact Ipc.nks_pure' _
  | some p =>
    unfold ifSporadicCurScTestRefillUnblockCheck ifCondRefillUnblockCheck NonDet.maybeM
    repeat (first | exact Ipc.nks_refillUnblockCheck _ | nks_step)

theorem nks_schedContextResume (p : ObjRef) : Ipc.NKS (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume getScRefillReady getScRefillSufficient threadGet getTcbQueue
  repeat (first | exact Ipc.nks_postpone _ | nks_step)

/-! ## Per callee -/

theorem bl_possibleSwitchTo (t c u : ObjRef) : IK (BL t c) (possibleSwitchTo (Z := Unit) u) :=
  bl_of_fk fun _ _ _ _ _ _ => SInvR.fk_possibleSwitchTo _ _ _ _ _ _ u

theorem bl_ifCond (t c : ObjRef) (o : Option ObjRef) :
    IK (BL t c) (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) :=
  bl_of_nks (nks_ifCond o)

/-- `sched_context_donate p u` of an SC with no bound TCB to a TCB `u ≠ t`. -/
theorem bl_donate (t c p u : ObjRef) (σ : State Unit) (hne : u ≠ t)
    (hst : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = none) :
    IKp (BL t c) σ (schedContextDonate (Z := Unit) p u) := by
  unfold schedContextDonate
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨ez, scv, n, hk, hv⟩ := cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at ez hv; subst ez
  rw [hst scv n hk] at hv; subst hv
  revert hy
  refine fun hy => (?_ : IKp (BL t c) z2 _) hσ y hy
  refine ikp_bind (ikp_when _ fun h => (h rfl).elim) fun _ => ?_
  exact SInv.ik_and (ik_bind (by qb_auto) fun _ => tp_threadSet _ _ fun _ _ e => absurd e hne) (by ks_auto)

/-- **`maybe_donate_sc u n`** keeps `t` bound to `c` and `c` an SC. -/
theorem bl_maybeDonateSc (t c u n : ObjRef) : IK (BL t c) (maybeDonateSc (Z := Unit) u n) := by
  unfold maybeDonateSc getTcbObjRef
  refine ik_threadGet_bind fun σ x hx => ?_
  intro hσ y hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hnone
    have hne : u ≠ t := by
      intro e; subst e
      have h := hσ.1 u x hx rfl
      rw [hnone] at h; cases h
    obtain ⟨z, hz, hy⟩ := hy
    have hz' : z.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz
    rw [hz'] at hy
    cases hz1 : z.1 with
    | none =>
      rw [hz1] at hy
      unfold NonDet.maybeM at hy
      rw [Set.mem_singleton_iff.1 hy]; exact hσ
    | some p =>
      rw [hz1] at hy
      unfold NonDet.maybeM at hy
      obtain ⟨w, hw, hy⟩ := hy
      obtain ⟨ew, scv, n', hk, hv⟩ := cq5_mem_getScObjRef hw
      rw [ew] at hy
      dsimp only at hy
      split at hy
      · rename_i hst
        obtain ⟨v, hv1, hy⟩ := hy
        have hvq : BL t c v.2 := bl_donate t c p u σ hne (fun y' n'' hk' => by
          rw [hk] at hk'; cases hk'; rw [← hv]; exact hst) hσ v hv1
        exact bl_of_nks (nks_schedContextResume p) v.2 hvq y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hσ
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ

end

end Fl4Proofs.P3.SInvR.A14b
