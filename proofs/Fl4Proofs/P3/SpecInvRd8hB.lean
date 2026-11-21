/-
P3 (DESIGN.md §9), invariant line G1 (rd8h, KENTRY-PLAN rd8f handoff 1):
**`invoke_tcb` ThreadControlSched keeps `Rdy`** (spec side only, outside the
JAtZ cone).

* `rd_install`: `install_tcb_cap` keeps `Rdy` at every outcome from rd8f's
  bundle `RB` (`rb_capDelete`, then rd's `rd_checkCapAt` / `rd_capInsert`).
* After the fault-handler install (ok outcome): `Rdy`, ctq's `DK ct`
  (`dk_installTcbCapD`: `TQ`, the current thread, `Simple`), and the
  readiness frame `MF σ` (`mf_installTcbCap3`, Rd8hA).
* `set_mcpriority`: a `tcb_mcpriority` write (`TQ` by `tq_setMcpriority`, the
  frame by the BK view).
* `set_priority`: rd8b's `rd_setPriority` with `CtRdy` at that state: the
  current thread is the perform's, `RdyT` at the perform (`hRT`), carried by
  `rdyT_mf`; `TQ` (`tq_setPriority`), `Simple` (`nsw_setPriority`), the frame
  (`bk_setPriority`).
* The SC: unbind (`rd_schedContextUnbindTcb_p`: `T1` from `TQ`, the switch
  target from `Simple`) or bind (`rd_schedContextBindTcb` with `BindRel` at
  that state: `bindRel_mf` from the perform's).
* **`rd_tcSched`**: Rdy at every outcome of the ThreadControlSched perform,
  from `RB ct I` and `RdyT ct` at the perform, the target's slot 3 a null or
  endpoint cap when a handler is installed (VfhAll), and the decode's
  `BindRel` for a new SC.
-/
import Fl4Proofs.P3.SpecInvRd8hA
import Fl4Proofs.P3.SpecInvCqH3
import Fl4Proofs.P3.SpecInvCqD2
import Fl4Proofs.P3.SpecInvCqRF5
import Fl4Proofs.P3.SpecInvRd8bB
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

macro_rules | `(tactic| bk_leaf) => `(tactic| ((with_reducible refine bk_threadSet _ _ ?_); intro _; exact ⟨rfl, rfl, rfl⟩))

theorem bk_setPriority (t : ObjRef) (p : Priority) {V : BKw} : BKK V (setPriority (Z := Unit) t p) := by
  unfold setPriority; bk_auto

theorem mfk_setPriority (t : ObjRef) (p : Priority) : MFK (setPriority (Z := Unit) t p) :=
  mfk_of_bk fun _ => bk_setPriority t p

theorem mfk_setMcpriority (t : ObjRef) (m : Priority) : MFK (setMcpriority (Z := Unit) t m) :=
  mfk_of_bk fun _ => bk_threadSet _ _ fun _ => ⟨rfl, rfl, rfl⟩

/-- `set_mcpriority` keeps the current thread and the scheduler action. -/
theorem ca_setMcpriority {t : ObjRef} {m : Priority} {s : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setMcpriority (Z := Unit) t m s).1) :
    y.2.curThread = s.curThread ∧ y.2.schedulerAction = s.schedulerAction := by
  unfold setMcpriority at hy
  obtain ⟨x, -, e⟩ := SInv.mem_threadSet hy
  rw [e]; exact ⟨rfl, rfl⟩

/-- **`install_tcb_cap`** keeps `Rdy` at every outcome from `RB`. -/
theorem rd_install (C I t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) (σ : State Unit)
    (h : B8f.RB C I σ) : ∀ y ∈ ((installTcbCap (Z := Unit) t sl n o).run σ).1, Rdy y.2 := by
  intro y hy
  unfold installTcbCap at hy
  rcases o with _ | ⟨nc, src⟩
  · rw [SInvU.mem_ret_ok hy]; exact h.1
  · try dsimp only at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' : Rdy z.2 := (B8f.rb_capDelete (C := C) (I := I) _ σ h z hz).1
      exact (ike_unlessE _ (ike_liftE (rd_checkCapAt _ _ _ (rd_checkCapAt _ _ _ (rd_capInsert _ _ _))))) z.2 hz' y hy
    · exact (B8f.rb_capDelete (C := C) (I := I) _ σ h z hz).1

/-- **ThreadControlSched keeps `Rdy`** (module docstring). -/
theorem rd_tcSched (bl call don : Bool) (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr))
    (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef)) (I : ObjRef) (σ : State Unit)
    (hRB : B8f.RB σ.curThread I σ) (hRT : RdyT σ σ.curThread)
    (hF : fh ≠ none → ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c)
    (hB : ∀ c, sc = some (some c) → BindRel σ c t) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don
      (.invokeTCB (.threadControlSched t sl fh mcp prio sc))).run σ).1, Rdy y.2 := by
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  obtain ⟨z1, hz1, ⟨u1, hu1, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · exact rd_install _ _ t sl 3 fh σ hRB z1 hz1
  have r1 : Rdy z1.2 := rd_install _ _ t sl 3 fh σ hRB z1 hz1
  have d1 : P12.DK σ.curThread z1.2 := (R14.dk_installTcbCapD σ.curThread t sl 3 fh σ hRB.2.1 z1 hz1).2 u1 hu1
  have m1 : MF σ z1.2 := mf_installTcbCap3 t sl fh σ hF z1 hz1
  obtain ⟨z2, hz2, ⟨u2, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2; rw [hx] at he; cases he
  obtain ⟨x2, hx2, rfl⟩ := SInvU.mem_liftE' hz2
  have k2 : Rdy x2.2 ∧ TQ x2.2 ∧ x2.2.curThread = σ.curThread ∧ Simple x2.2 ∧ MF σ x2.2 := by
    rcases mcp with _ | ⟨m, _⟩
    · simp only [NonDet.maybeM] at hx2
      rw [Set.mem_singleton_iff.1 hx2]
      exact ⟨r1, d1.1.1.1.1, d1.2.1, d1.2.2.1, m1⟩
    · simp only [NonDet.maybeM] at hx2
      obtain ⟨c1, c2⟩ := ca_setMcpriority hx2
      refine ⟨rd_setMcpriority t m z1.2 r1 x2 hx2, tq_setMcpriority t m z1.2 d1.1.1.1.1 x2 hx2,
        c1.trans d1.2.1, fun u => by rw [c2]; exact d1.2.2.1 u, mfk_setMcpriority t m σ z1.2 m1 x2 hx2⟩
  obtain ⟨r2, q2, c2, s2, m2⟩ := k2
  obtain ⟨z3, hz3, ⟨u3, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3; rw [hx] at he; cases he
  obtain ⟨x3, hx3, rfl⟩ := SInvU.mem_liftE' hz3
  have k3 : Rdy x3.2 ∧ TQ x3.2 ∧ Simple x3.2 ∧ MF σ x3.2 := by
    rcases prio with _ | ⟨p, _⟩
    · simp only [NonDet.maybeM] at hx3
      rw [Set.mem_singleton_iff.1 hx3]; exact ⟨r2, q2, s2, m2⟩
    · simp only [NonDet.maybeM] at hx3
      have hC : CtRdy x2.2 := fun x hx _ => by
        rw [c2] at hx ⊢; exact rdyT_mf hRT m2 ⟨x, hx⟩
      exact ⟨rd_setPriority t p x2.2 hC r2 x3 hx3, tq_setPriority t p x2.2 q2 x3 hx3,
        fun u => P13.nsw_setPriority u t p x2.2 (s2 u) x3 hx3, mfk_setPriority t p σ x2.2 m2 x3 hx3⟩
  obtain ⟨r3, q3, s3, m3⟩ := k3
  obtain ⟨z4, hz4, ⟨u4, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz4; rw [hx] at he; cases he
  obtain ⟨x4, hx4, rfl⟩ := SInvU.mem_liftE' hz4
  rw [SInvU.mem_ret_ok hy]
  show Rdy x4.2
  rcases sc with _ | _ | c
  · simp only [NonDet.maybeM] at hx4; rw [Set.mem_singleton_iff.1 hx4]; exact r3
  · simp only [NonDet.maybeM] at hx4
    obtain ⟨w, hw, hx4⟩ := hx4
    obtain ⟨xt, -, rfl⟩ := q1_mem_threadGet hw
    obtain ⟨w2, hw2, hx4⟩ := hx4
    obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt hw2
    obtain ⟨scp, w2s⟩ := w2
    simp only at ha1 ha2; subst w2s
    exact rd_schedContextUnbindTcb_p scp x3.2 (tq_t1 q3.1) (fun _ _ u _ _ _ => s3 u) r3 _ hx4
  · simp only [NonDet.maybeM] at hx4
    exact rd_schedContextBindTcb c t x3.2 (bindRel_mf (hB c rfl) m3) r3 x4 hx4

end

end Fl4Proofs.P3.SInvR.B8h
