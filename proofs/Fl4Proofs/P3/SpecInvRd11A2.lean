/-
P3 (DESIGN.md §9), invariant line G1 (rd11a, KENTRY-PLAN rd10 handoff 1):
**`receive_signal` of the current thread** for `OsBody` (spec side only).

* `KE σ0 s := KP σ0 s ∧ (CB0 s ∨ NRun ct s)` (the end of an arm: CtR by
  A1's `ctR_kp` / `ctR_nrun`); `CB0` = ct unbound or bound to cur_sc.
* `md_ro` (maybe_donate_sc of a bound thread reads only), `ifc_cur` (the
  unblock check of cur_sc itself fails its `scp ≠ cur_sc` test).
* **`ke_receiveSignal`**: from `KP σ0 s` with ct bound to cur_sc at `s`, every
  outcome of `receive_signal ct cap blk` has `KE σ0` (active: an `SVS ∧ cfS`
  run; blocking: ct not runnable; non-blocking: `SVS`).
-/
import Fl4Proofs.P3.SpecInvRd11A1
open Classical

namespace Fl4Proofs.P3.SInvR.A11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-- ct unbound or bound to cur_sc. -/
abbrev CB0 (s : State Unit) : Prop :=
  ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = none ∨ x.tcbSchedContext = some s.curSc

/-- The end of an arm. -/
abbrev KE (σ0 s : State Unit) : Prop := KP σ0 s ∧ (CB0 s ∨ A8.NRun s.curThread s)

theorem ss4_of_ke {σ0 s : State Unit} (h : A10.BS σ0) (hs : Suff σ0) (hK : KE σ0 s) : A10.SS4 s :=
  ss4_of_kp h hs hK.1 (hK.2.elim (ctR_kp h hK.1) ctR_nrun)

/-- An `SVS ∧ cfS` run from a state where ct is bound to cur_sc ends in `KE`. -/
theorem ke_svs {σ0 s s' : State Unit} (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : KE σ0 s' := by
  refine ⟨kp_step hK hc (A8.cw_of_svs hS) fun _ => ⟨hS.1 _, hS.1 _⟩, Or.inl fun x hx => Or.inr ?_⟩
  exact (A8.keep_svcf hS hc).2.2 hb x hx

/-- `maybe_donate_sc` of a bound thread only reads. -/
theorem md_ro {t n : ObjRef} {s : State Unit}
    (hb : ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext ≠ none) {y : Unit × State Unit}
    (hy : y ∈ (maybeDonateSc (Z := Unit) t n s).1) : y.2 = s := by
  unfold maybeDonateSc at hy
  obtain ⟨z1, h1, hy⟩ := hy
  obtain ⟨x1, hx1, rfl⟩ := SInvQ.q1_mem_threadGet h1
  dsimp only at hy
  unfold NonDet.when at hy
  rw [if_neg (hb x1 hx1)] at hy
  rw [Set.mem_singleton_iff.1 hy]

/-- The unblock check of cur_sc itself (the `scp ≠ cur_sc` test fails). -/
theorem ifc_cur {p : ObjRef} {a : Option Bool} {s : State Unit} (he : p = s.curSc) {y : Unit × State Unit}
    (hy : y ∈ (ifCondRefillUnblockCheck (Z := Unit) (some p) a (some false) s).1) : y.2 = s := by
  unfold ifCondRefillUnblockCheck at hy
  obtain ⟨⟨sc, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  beta_reduce at hy
  rw [Notif.nd_gets_bind, Notif.nd_pure_bind'] at hy
  unfold NonDet.when at hy
  split_ifs at hy with hg
  all_goals first
    | exact absurd he (hg.2 rfl)
    | (obtain rfl := Set.mem_singleton_iff.1 hy; rfl)

theorem kp_tcbNtfnAppend (t n : ObjRef) (σ0 : State Unit) : IK (KP σ0) (tcbNtfnAppend (Z := Unit) t n) := by
  unfold tcbNtfnAppend tcbAppend orderedInsert; kp_auto

/-- `receive_signal_blocked` of the current thread bound to cur_sc. -/
theorem ke_rsBlocked (σ0 : State Unit) (np : ObjRef) (blk : Bool) (s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    {y : Unit × State Unit} (hy : y ∈ (receiveSignalBlocked (Z := Unit) σ0.curThread np blk s).1) : KE σ0 y.2 := by
  unfold receiveSignalBlocked at hy
  split at hy
  · refine ⟨(?_ : IK (KP σ0) _) s hK y hy, Or.inr ?_⟩
    · repeat' (first | exact kp_maybeReturnSc _ _ | exact kp_tcbNtfnAppend _ _ _ | kp_leaf | ik_step0)
    · have hn := A9.no_bind (fun z hz => A9.no_sts σ0.curThread _ rfl hz)
        (fun _ => ik_bind (by unfold tcbNtfnAppend; fg_auto) fun _ => fg_maybeReturnSc _ _) y hy
      have ey : y.2.curThread = σ0.curThread := by
        have hK' : KP σ0 y.2 := by
          refine (?_ : IK (KP σ0) _) s hK y hy
          repeat' (first | exact kp_maybeReturnSc _ _ | exact kp_tcbNtfnAppend _ _ _ | kp_leaf | ik_step0)
        exact kp_curThread hK'
      rw [ey]; exact A9.nrun_of_no hn
  · unfold doNbrecvFailedTransfer at hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    have c3 : cfS z3.2 = cfS s := by refine (?_ : CFK _) s z3 h3; cfk_auto
    exact ke_svs hK hb (SVK.sv_asUser' _ _ s z3 h3) c3

/-- **`receive_signal` of the current thread bound to cur_sc.** -/
theorem ke_receiveSignal (σ0 : State Unit) (cap : Cap) (blk : Bool) (s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    {y : Unit × State Unit} (hy : y ∈ (receiveSignal (Z := Unit) σ0.curThread cap blk s).1) : KE σ0 y.2 := by
  have ect := kp_curThread hK
  unfold receiveSignal at hy
  cases cap
  case notificationCap np bd rt =>
    obtain ⟨⟨n1, s1⟩, h1, hy⟩ := hy
    obtain ⟨rfl, e1⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
    subst s1
    obtain ⟨⟨nt, s2⟩, h2, hy⟩ := hy
    have e2 : s2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
    subst s2
    dsimp only at hy
    cases hob : nt.ntfnObj with
    | idleNtfn => simp only [hob] at hy; exact ke_rsBlocked σ0 _ blk s hK hb hy
    | waitingNtfn q => simp only [hob] at hy; exact ke_rsBlocked σ0 _ blk s hK hb hy
    | activeNtfn bdg =>
      simp only [hob] at hy
      -- the active arm: an SVS ∧ cfS run
      obtain ⟨z3, h3, hy⟩ := hy
      obtain ⟨z4, h4, hy⟩ := hy
      obtain ⟨z5, h5, hy⟩ := hy
      have v3 := SVK.sv_asUser' _ _ s z3 h3
      have c3 : cfS z3.2 = cfS s := by refine (?_ : CFK _) s z3 h3; cfk_auto
      have v4 : SVK.SVS z3.2 z4.2 := by refine (?_ : SVK.SVM _) z3.2 z4 h4; sv_auto
      have c4 : cfS z4.2 = cfS z3.2 := by refine (?_ : CFK _) z3.2 z4 h4; cfk_auto
      have v34 := v3.trans v4
      have c34 := c4.trans c3
      have hb4 := (A8.keep_svcf v34 c34).2.2 hb
      have et4 : z4.2.curThread = σ0.curThread := (congrArg (fun p => p.2.2.1) c34).trans ect
      rw [← et4] at h5
      have e5 : z5.2 = z4.2 := md_ro (fun x hx => by rw [hb4 x hx]; simp) h5
      rw [e5] at hy
      obtain ⟨z6, h6, hy⟩ := hy
      obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
      rw [← et4] at hx6
      rw [hb4 x6 hx6] at hy
      rw [ifc_cur rfl hy]
      exact ke_svs hK hb v34 c34
  all_goals (obtain ⟨_, h, -⟩ := hy; exact h.elim)

end

end Fl4Proofs.P3.SInvR.A11
