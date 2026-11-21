/-
P3 (DESIGN.md §9), invariant line G1 (ctq13): **EB across the performs**,
part 7: `sched_context_bind_tcb`, the SC Bind arm and ThreadControlSched
(spec side only, outside the JAtZ cone). Both arms run only with
`firstPhase = false`, so `EB false` after them is what is needed.

* **`eb_schedContextBindTcb sc t (hA : AN t σ)`**: the TCB / SC writes keep
  `EB false` and `AN t`, and after the `sc_tcb` write every thread bound to
  `sc` is `t` (ctq8's `BP`, kept by the refill check along sb2's binding
  frame), so `sched_context_resume sc` is ctq8's `rbf_schedContextResume_p`;
  the `schedulable`-guarded enqueue leaves ctq7's `ET` (the enqueued thread
  is not released), and `reschedule_required` gives `EB false`
  (`et_rescheduleRequired`).
* `AN t` at the SC Bind perform: `Simple` (ctq5's EX) and, under
  `resume_cur_thread`, `t ≠ ct`: the decode checked that `t` has no SC
  (decode_sched_context_bind) while ct has one (ctq10's `ResSc`):
  `an_of_resSc`.
* ThreadControlSched: `install_tcb_cap` (ctq12's `dk_installTcbCap`, the
  idle thread kept: sg1's `idk_installTcbCap`), `set_mcpriority` (generated
  leaves), `set_priority` (`y_setPriority`: `EB true` → `EB false`, `Simple`
  kept, and afterwards `t` is not current under `resume_cur_thread`: if it
  was, ct is a runnable non-idle TCB (`CB`), so `set_priority` ends in
  `reschedule_required`), then unbind (generated leaves) or bind. An SC
  argument comes only with a priority (decode_set_sched_params is the only
  decode producing one): the decode fact `hP`.
-/
import Fl4Proofs.P3.SpecInvCqD1
import Fl4Proofs.P3.SpecInvSgI6
open Classical

namespace Fl4Proofs.P3.SInvQ.P13
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Frames -/

/-- `reschedule_required` leaves a reschedule pending (ScMidCur's
`rescheduleRequired_cn`, outside this import closure). -/
theorem rescheduleRequired_cn' {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (rescheduleRequired (Z := Unit) σ).1) : x.2.schedulerAction = .chooseNewThread := by
  unfold rescheduleRequired setSchedulerAction at hx
  obtain ⟨y, -, hx⟩ := hx
  generalize y.1 = act at hx
  cases act with
  | switchThread t =>
    obtain ⟨z, -, hx⟩ := hx
    obtain ⟨w, -, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
  | resumeCurThread =>
    first | (rw [Set.mem_singleton_iff.1 hx]) | (obtain ⟨w, -, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx])
  | chooseNewThread =>
    first | (rw [Set.mem_singleton_iff.1 hx]) | (obtain ⟨w, -, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx])

theorem an_threadSet' (t : ObjRef) (f : Tcb → Tcb) (u : ObjRef) : IK (AN t) (threadSet (Z := Unit) f u) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ?_
  intro h y hy
  rw [cq6_setObject hy]
  exact h

theorem an_updateSchedContext (t p : ObjRef) (f : SchedContext → SchedContext) :
    IK (AN t) (updateSchedContext (Z := Unit) p f) := by
  intro σ h y hy
  unfold updateSchedContext at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨-, hs⟩ := mem_getObject hz
  obtain ⟨o, z2⟩ := z
  simp only at hs; subst hs
  dsimp only at hy
  split at hy
  · rw [cq6_setObject hy]; exact h
  · exact hy.elim

theorem bp_of_br {t p : ObjRef} {s s' : State Unit} (h : BP t p s) (hb : SInvB.BR s.kheap s'.kheap) : BP t p s' := by
  intro y' n' u hk hu
  obtain ⟨y, n, hy⟩ := hb.sc' p y' n' hk
  obtain ⟨y2, n2, hy2, hkp⟩ := hb.sc p y n hy
  rw [hk] at hy2; cases hy2
  exact h y n u hy (by rw [← hkp.1]; exact hu)

/-! ## `sched_context_bind_tcb` -/

/-- **`sched_context_bind_tcb sc t` keeps `EB false`** when `t` has `AN`
(not the switch target, not current under `resume_cur_thread`). -/
theorem eb_schedContextBindTcb (sc t : ObjRef) (σ : State Unit) (hA : AN t σ) :
    IKp (EB false) σ (schedContextBindTcb (Z := Unit) sc t) := by
  intro hσ y hy
  unfold schedContextBindTcb at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  have e1 : EB false z1.2 :=
    eb_threadSet (tcbSchedContextUpdate fun _ => some sc) t (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ h => h) σ hσ z1 hz1
  have a1 : AN t z1.2 := an_threadSet' t _ t σ hA z1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have e2 : EB false z2.2 := eb_of (tq_updateSchedContext _ _) (sa_updateSchedContext _ _)
    (q4_updateSchedContext _ _) (rb_updateSchedContext _ _) z1.2 e1 z2 hz2
  have a2 : AN t z2.2 := an_updateSchedContext t sc _ z1.2 a1 z2 hz2
  have b2 : BP t sc z2.2 := bp_updTcb sc t z1.2 z2 hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  have e3 : EB false z3.2 := eb_of (tq_ifCondRefillUnblockCheck _ _ _) (sa_ifCondRefillUnblockCheck _ _ _)
    (q4_ifCondRefillUnblockCheck _ _ _) (rb_ifCondRefillUnblockCheck _ _ _) z2.2 e2 z3 hz3
  have a3 : AN t z3.2 := an_ifCondRefillUnblockCheck t _ _ _ z2.2 a2 z3 hz3
  have b3 : BP t sc z3.2 :=
    bp_of_br b2 (SInvB.br_mem_of_sbk (fun _ => SInvB.sb_ifCondRefillUnblockCheck _ _ _) hz3)
  obtain ⟨z4, hz4, hy⟩ := hy
  have e4 : EB false z4.2 := by
    refine ⟨sq4_of (tq_schedContextResume sc) (sa_schedContextResume sc) (q4_schedContextResume sc) z3.2
      e3.1 z4 hz4, ?_⟩
    refine rbf_schedContextResume_p sc z3.2 e3.1.1.1 (fun y' n' u hk hu => ?_) e3.2 z4 hz4
    rw [b3 y' n' u hk hu]; exact a3
  obtain ⟨w, hw, hy⟩ := hy
  rw [mem_gets hw] at hy
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hs
    obtain ⟨w1, hw1, hy⟩ := hy
    have hrel : t ∉ z4.2.releaseQueue := by
      have hs' := hs
      unfold schedulable at hs'
      exact (of_decide_eq_true hs').2.2
    have hT := tq_enq_p _ t z4.2 (q1_enq t) (schedulable_rn hs) e4.1.1.1 w1 hw1
    have hR : RR w1.2 := by obtain ⟨_, -, e⟩ := q1_tsa_out hw1; rw [e]; exact e4.1.1.2.2.1
    have h4 := q4_tcbSchedAction _ t z4.2 e4.1.2 w1 hw1
    have hD := (rde_enq _ t (q1_enq t) z4.2 ⟨e4.2.1.1, hrel⟩ w1 hw1).1
    exact et_rescheduleRequired _ ⟨hT, hR, h4, hD⟩ y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact e4

/-- `AN t` at the SC Bind perform: no switch pending, ct has an SC under
`resume_cur_thread` (`ResSc`), `t` has none (the decode's check). -/
theorem an_of_resSc {σ : State Unit} (hS : Simple σ) (hR : ResSc σ) {t : ObjRef} {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hn : x.tcbSchedContext = none) : AN t σ :=
  ⟨hS t, fun hr e => hR hr x (by rw [← e]; exact hx) hn⟩

/-- **The SC Bind arm** keeps `EB false` (`AN t` for a TCB target). -/
theorem eb_perfScBind (bl call don : Bool) (sc : ObjRef) (c : Cap) :
    HKE (fun σ => EB false σ ∧ ∀ t, c = .threadCap t → AN t σ) (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeSchedContext (.invokeSchedContextBind sc c))) := by
  simp only [fl4PerformInvocation, withoutPreemption, invokeSchedContext]
  cases c
  case threadCap t =>
    refine hk_liftE ?_
    intro σ hσ y ⟨z, hz, hy⟩
    rw [Set.mem_singleton_iff.1 hy]
    exact eb_schedContextBindTcb sc t σ (hσ.2 t rfl) hσ.1 z hz
  all_goals
    (try simp only)
    refine fun σ hσ => (?_ : EBKE false _) σ hσ.1
    eb_auto

/-! ## `set_priority` before a bind -/

/-- The carried facts across `set_mcpriority`. -/
abbrev G (C N : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ Simple s ∧ SInvG.IdleIs N s

/-- After `set_priority t`: `t` not current under `resume_cur_thread`. -/
abbrev Y (t : ObjRef) (s : State Unit) : Prop :=
  EB false s ∧ Simple s ∧ (s.schedulerAction = .resumeCurThread → t ≠ s.curThread)

theorem g_setMcpriority (C N t : ObjRef) (m : Priority) : IK (G C N) (setMcpriority (Z := Unit) t m) := by
  intro σ h y hy
  refine ⟨eb_of (tq_setMcpriority t m) (sa_setMcpriority t m) (q4_setMcpriority t m) (rb_setMcpriority t m) σ h.1 y hy,
    SInv.ct_setMcpriority (cq := C) t m σ h.2.1 y hy, fun u => ?_, SInvG.idk_setMcpriority t m σ h.2.2.2 y hy⟩
  exact (show IK (NSw u) (setMcpriority (Z := Unit) t m) by unfold setMcpriority; p12_nsw_auto) σ (h.2.2.1 u) y hy

theorem nsw_setPriority (u t : ObjRef) (p : Priority) : IK (NSw u) (setPriority (Z := Unit) t p) := by
  unfold setPriority; p12_nsw_auto

theorem an_setPriority (u t : ObjRef) (p : Priority) : IK (AN u) (setPriority (Z := Unit) t p) := by
  unfold setPriority; an_auto

/-- **`set_priority t`** from `G C N` (ct = C ≠ idle = N) gives `Y t`. -/
theorem y_setPriority (C N : ObjRef) (hCN : C ≠ N) (t : ObjRef) (p : Priority) :
    HK (G C N) (Y t) (setPriority (Z := Unit) t p) := by
  intro σ h y hy
  refine ⟨eb_setPriority_t t p σ h.1 hy, fun u => nsw_setPriority u t p σ (h.2.2.1 u) y hy, ?_⟩
  by_cases hc : σ.schedulerAction = .resumeCurThread ∧ t = σ.curThread
  · obtain ⟨hr, e⟩ := hc
    have hrn : RnH t σ.kheap := by
      rcases h.1.2.2 hr with hh | hi
      · rw [e]; exact hh
      · exact absurd (h.2.1.symm.trans (hi.trans h.2.2.2)) hCN
    obtain ⟨x0, hx0, hrx⟩ := hrn
    have hcn : y.2.schedulerAction = .chooseNewThread := by
      unfold setPriority getThreadState threadSetPriority getTcbQueue at hy
      obtain ⟨z, hz, hy⟩ := hy
      obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
      rw [hx0] at hx; cases hx
      dsimp only at hy
      split at hy
      · obtain ⟨z, hz, hy⟩ := hy
        obtain ⟨x1, hx1, rfl⟩ := q1_mem_threadGet hz
        obtain ⟨z, hz, hy⟩ := hy
        obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz
        obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
        obtain rfl := Set.mem_singleton_iff.1 hw
        obtain rfl := Set.mem_singleton_iff.1 hz
        obtain ⟨w, hw, hy⟩ := hy
        obtain rfl := Set.mem_singleton_iff.1 hw
        dsimp only at hy
        split at hy
        · obtain ⟨z1, hz1, hy⟩ := hy
          obtain ⟨z2, hz2, hy⟩ := hy
          obtain ⟨z3, hz3, hy⟩ := hy
          exact rescheduleRequired_cn' hy
        · rename_i hq
          exact absurd (Or.inr e) hq
      · rename_i hnr
        exact absurd hrx hnr
    intro hres
    rw [hcn] at hres; cases hres
  · have hX : AN t σ := ⟨h.2.2.1 t, fun hr e => hc ⟨hr, e⟩⟩
    exact (an_setPriority t t p σ hX y hy).2

/-! ## ThreadControlSched -/

theorem hker_and {P Q R : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : HKEr P Q m)
    (h2 : IKE R m) : HKEr (fun s => P s ∧ R s) (fun s => Q s ∧ R s) m :=
  fun σ hσ y hy => ⟨(h σ hσ.1 y hy).1, fun a ha => ⟨(h σ hσ.1 y hy).2 a ha, h2 σ hσ.2 y hy⟩⟩

/-- The SC option of ThreadControlSched from `Y t`. -/
theorem hk_tcsSc (t : ObjRef) (sc : Option (Option ObjRef)) :
    HK (Y t) (EB false) (NonDet.maybeM (fun scopt =>
          match scopt with
          | none => do
              let scPtrOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
              let scPtr ← NonDet.assertOpt scPtrOpt
              schedContextUnbindTcb scPtr
          | some scPtr => schedContextBindTcb scPtr t) sc) := by
  rcases sc with _ | _ | scp
  · intro σ h y hy
    simp only [NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact h.1
  · intro σ h y hy
    simp only [NonDet.maybeM] at hy
    exact (show EBK false _ by eb_auto) σ h.1 y hy
  · intro σ h y hy
    simp only [NonDet.maybeM] at hy
    exact eb_schedContextBindTcb scp t σ ⟨h.2.1 t, h.2.2⟩ h.1 y hy

/-- **The ThreadControlSched arm** keeps `EB false` (`EbCapDeleteH` for the
fault-handler install; the decode fact `hP`: an SC argument comes with a
priority). -/
theorem eb_perfTcbSched (hD : EbCapDeleteH) (C N : ObjRef) (hCN : C ≠ N) (bl call don : Bool) (target : Word)
    (slot : CslotPtr) (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef))
    (sc : Option (Option ObjRef)) (hP : sc ≠ none → prio ≠ none) :
    HKEr (fun s => DK C s ∧ SInvG.IdleIs N s) (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.threadControlSched target slot fh mcp prio sc))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hker_bind (hker_and (dk_installTcbCap hD C _ _ _ _) (SInvG.idk_installTcbCap _ _ _ _)) fun _ => ?_
  refine hker_bind (R := G C N) (hker_of (hk_liftE ?_) fun _ h => eb_weak h.1) fun _ => ?_
  · intro σ h y hy
    have h0 : G C N σ := ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2⟩
    rcases mcp with _ | ⟨m, _⟩
    · simp only [NonDet.maybeM] at hy
      rw [Set.mem_singleton_iff.1 hy]; exact h0
    · simp only [NonDet.maybeM] at hy
      exact g_setMcpriority C N target m σ h0 y hy
  rcases prio with _ | ⟨p, _⟩
  · have hsc : sc = none := by
      by_contra hne; exact hP hne rfl
    subst hsc
    refine hker_bind (R := EB false) (hker_of (hk_liftE ?_) fun _ h => h) fun _ => ?_
    · intro σ h y hy
      simp only [NonDet.maybeM] at hy
      rw [Set.mem_singleton_iff.1 hy]; exact eb_weak h.1
    refine hker_bind (R := EB false) (hker_of (hk_liftE ?_) fun _ h => h) fun _ => hker_ret _ fun _ h => h
    intro σ h y hy
    simp only [NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact h
  · refine hker_bind (R := Y target) (hker_of (hk_liftE ?_) fun _ h => h.1) fun _ => ?_
    · intro σ h y hy
      simp only [NonDet.maybeM] at hy
      exact y_setPriority C N hCN target p σ h y hy
    refine hker_bind (R := EB false) (hker_of (hk_liftE (hk_tcsSc target sc)) fun _ h => h) fun _ => ?_
    exact hker_ret _ fun _ h => h

end

end Fl4Proofs.P3.SInvQ.P13
