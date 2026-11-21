/-
P3 (DESIGN.md §9), invariant line G1 (rd14d, KENTRY-PLAN rd14c handoff 2):
**the SchedContext arms (but binding a TCB) and CNode cancelBadgedSends**
(spec side only).

* `EC σ0 q` (σ0's `cfS` and `CW` at cur_sc, and rd14b's `EB ct cur_sc`: ct
  bound to cur_sc with cur_sc an SC, or ct unbound with no resume):
  `ec_of_tb`, `tbu_of_ec` (`EC` gives rd13b's `TBN` or rd14b's `TU`),
  `ec_svcf` (an `SVM ∧ CFK` step keeps it), `ec_ik`, **`perfA_liftEC`** (a
  lifted perform keeping `EC σ0` has `PerfA`, through rd14b's `perfA_tbn3`).
* **`eb_schedContextUnbindTcb`**: unbinding the TCB of any SC from a state with
  `EB ct c` ends in `EB ct c` (the TCB is ct: rescheduled first, so ct ends
  unbound with no resume; else ct's binding is untouched). No `ScSym` needed.
* Arms: **`perfA_schedContext`** (Consumed, Bind of a notification,
  UnbindObject, Unbind, YieldTo: everything but binding a TCB, which needs the
  decode's "the TCB is unbound" fact), **`perfA_cancelBadged`** (CNode
  cancelBadgedSends: `TB` through rd14c's `tb_ik`; new leaves
  `cp_ifCondAssert`, `nks_ifCondG`).
* `CovD` (these arms), **`armA_covD`**, `C14d := C14c ∨ CovD`,
  **`armA_c14d`**.
-/
import Fl4Proofs.P3.SpecInvRd14cC
import Fl4Proofs.P3.SpecInvRd8fB
open Classical

namespace Fl4Proofs.P3.SInvR.A14d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Bound or unbound, with σ0's frame -/

/-- σ0's `cfS` and `CW` at cur_sc, ct bound to cur_sc (an SC) or unbound with no resume. -/
abbrev EC (σ0 q : State Unit) : Prop :=
  cfS q = cfS σ0 ∧ A8.CW σ0.curSc σ0 q ∧ EB σ0.curThread σ0.curSc q

theorem ec_of_tb {σ0 q : State Unit} (h : TB σ0 q) : EC σ0 q :=
  ⟨h.cf, h.cw, Or.inl ⟨fun p x hx he => by subst he; exact h.bd x hx, h.sc⟩⟩

theorem tbu_of_ec {σ0 q : State Unit} (h : EC σ0 q) : TBN σ0 q ∨ TU σ0 q := by
  obtain ⟨hc, hw, ⟨hq, hk⟩ | ⟨hq, hn⟩⟩ := h
  · exact Or.inl (show TBN σ0 q from Or.inl ⟨hc, hw, fun x hx => hq _ x hx rfl, hk⟩)
  · exact Or.inr ⟨hc, hw, fun x hx => hq _ x hx rfl, hn⟩

theorem ec_svcf {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) :
    IK (EC σ0) m :=
  fun s hs y hy => ⟨(h2 s y hy).trans hs.1, hs.2.1.trans (A8.cw_of_svs (h1 s y hy)), eb_svs hs.2.2 (h1 s y hy)⟩

theorem tb_svm {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) :
    IK (TB σ0) m :=
  fun s hs y hy => tb_svcf hs (h1 s y hy) (h2 s y hy)

/-- `EC σ0` from `CFK`, rd8a's `CP` and an `EB` step from ct. -/
theorem ec_ik {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : CFK m)
    (h2 : IK (A8.CP σ0 σ0.curSc) m)
    (h3 : ∀ s : State Unit, s.curThread = σ0.curThread → EB σ0.curThread σ0.curSc s →
      ∀ y ∈ (m s).1, EB σ0.curThread σ0.curSc y.2) : IK (EC σ0) m := by
  intro s hs y hy
  obtain ⟨-, hw⟩ := h2 s ⟨cf_curSc hs.1, hs.2.1⟩ y hy
  exact ⟨(h1 s y hy).trans hs.1, hw, h3 s (cf_curThread hs.1) hs.2.2 y hy⟩

/-- **A lifted perform keeping `EC σ0`** has `PerfA` (no error outcome). -/
theorem perfA_liftEC {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation}
    (m : NonDet (State Unit) (List Data)) (he : fl4PerformInvocation (Z := Unit) bl call don oper = NonDetE.liftE m)
    (hB : A10.BS σ0) (hS : Suff σ0) (hm : IK (EC σ0) m) (h0 : EC σ0 s) : PerfA σ0 bl call don oper s := by
  refine perfA_tbn3 hB hS fun y hy => ?_
  rw [he] at hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact ⟨fun _ _ => tbu_of_ec (hm s h0 x hx), fun e h => by cases h⟩

/-- **A perform keeping `TB σ0` with no error outcome** has `PerfA`. -/
theorem perfA_ikeTB {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (hS : Suff σ0) (hm : IKE (TB σ0) (fl4PerformInvocation (Z := Unit) bl call don oper))
    (hn : NoErr (fl4PerformInvocation (Z := Unit) bl call don oper)) (h0 : TB σ0 s) :
    PerfA σ0 bl call don oper s :=
  perfA_tbn hB hS fun y hy => ⟨fun _ _ => Or.inl (hm s h0 y hy), fun e he => absurd he (hn s y hy e)⟩

/-! ## `sched_context_unbind_tcb` -/

/-- The tail of `sched_context_unbind_tcb` of the TCB `tp` (rescheduled first if `tp = t`). -/
theorem eb_unbindTail (t c tp p : ObjRef) (s : State Unit) (h : EB t c s) (hn : tp = t → NRes s) :
    ∀ y ∈ ((do
      tcbSchedAction (Z := Unit) tcbSchedDequeue tp
      tcbReleaseRemove (Z := Unit) tp
      setTcbObjRef (Z := Unit) tcbSchedContextUpdate tp none
      setScObjRef (Z := Unit) scTcbUpdate p none) s).1, EB t c y.2 := by
  intro y hy
  obtain ⟨a2, ha2, hy⟩ := hy
  obtain ⟨a3, ha3, hy⟩ := hy
  obtain ⟨a4, ha4, hy⟩ := hy
  have s2 : SVK.SVS s a2.2 := (by sv_auto : SVK.SVM (tcbSchedAction (Z := Unit) tcbSchedDequeue tp)) s a2 ha2
  have s3 : SVK.SVS a2.2 a3.2 := (by sv_auto : SVK.SVM (tcbReleaseRemove (Z := Unit) tp)) a2.2 a3 ha3
  have s23 := s2.trans s3
  have e3 : EB t c a3.2 := eb_svs h s23
  have n3 : tp = t → NRes a3.2 := fun e => by
    have h' := hn e
    unfold NRes at h' ⊢
    rcases s23.2.2 with e' | e'
    · rw [e']; exact h'
    · rw [e']; intro h''; cases h''
  have e4 : EB t c a4.2 := by
    by_cases ht : tp = t
    · subst ht
      obtain ⟨x, -, ex⟩ := SInv.mem_threadSet ha4
      refine Or.inr ⟨?_, ?_⟩
      · intro p' x' hp ep
        subst ep
        rw [ex] at hp
        simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hp
        subst hp; rfl
      · have h' := n3 rfl
        unfold NRes at h' ⊢; rw [ex]; exact h'
    · exact (ik_eb (SInv.ik_and (tp_threadSet _ _ fun _ _ e => absurd e ht) (by ks_auto))
        (tp_threadSet _ _ fun _ _ e => absurd e ht) (by nres_auto) :
          IK (EB t c) (setTcbObjRef (Z := Unit) tcbSchedContextUpdate tp none)) a3.2 e3 a4 ha4
  exact (ik_eb (SInv.ik_and (by qb_auto) (by ks_auto)) (by qb_auto) (by nres_auto) :
    IK (EB t c) (setScObjRef (Z := Unit) scTcbUpdate p none)) a4.2 e4 y hy

/-- **`sched_context_unbind_tcb p`** from `EB t c` (`t` current) ends in `EB t c`. -/
theorem eb_schedContextUnbindTcb (t c p : ObjRef) (σ : State Unit) (hct : σ.curThread = t) (h : EB t c σ) :
    ∀ y ∈ (schedContextUnbindTcb (Z := Unit) p σ).1, EB t c y.2 := by
  intro y hy
  unfold schedContextUnbindTcb at hy
  obtain ⟨z, hz, hy⟩ := hy
  have ez : z.2 = σ := cq5_ro (fun _ => by unfold getSchedContext; repeat' (first | ik_step0 | ik_unfold)) hz
  obtain ⟨a1, ha1, hy⟩ := hy
  obtain ⟨-, ea1⟩ := cq5_mem_assertOpt ha1
  have es : a1.2 = σ := ea1.trans ez
  obtain ⟨a2, ha2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 ha2] at hy
  dsimp only at hy
  obtain ⟨b, hb, hy⟩ := hy
  rw [es] at hb
  unfold NonDet.when at hb
  split at hb
  · rename_i heq
    have eb1 : EB t c b.2 :=
      ik_eb (bl_of_fk fun _ _ _ _ _ _ => SInvR.fk_rescheduleRequired _ _ _ _ _ _) (qn_rescheduleRequired t)
        (fun s _ x hx => by
          show x.2.schedulerAction ≠ _
          rw [rescheduleRequired_cn s x hx]; intro h'; cases h') σ h b hb
    have nb : NRes b.2 := by
      show b.2.schedulerAction ≠ _
      rw [rescheduleRequired_cn σ b hb]; intro h'; cases h'
    exact eb_unbindTail t c a1.1 p b.2 eb1 (fun _ => nb) y hy
  · rename_i hne
    rw [Set.mem_singleton_iff.1 hb] at hy
    exact eb_unbindTail t c a1.1 p σ h (fun e => absurd (e.trans hct.symm) hne) y hy

theorem ec_schedContextUnbindTcb (σ0 : State Unit) (p : ObjRef) :
    IK (EC σ0) (schedContextUnbindTcb (Z := Unit) p) :=
  ec_ik (cfk_schedContextUnbindTcb' p) (by unfold schedContextUnbindTcb; cp_auto)
    fun s hct h => eb_schedContextUnbindTcb _ _ p s hct h

theorem ec_schedContextUnbindAllTcbs (σ0 : State Unit) (p : ObjRef) :
    IK (EC σ0) (schedContextUnbindAllTcbs (Z := Unit) p) := by
  unfold schedContextUnbindAllTcbs
  exact ik_bind (by unfold getSchedContext; repeat' (first | ik_step0 | ik_unfold)) fun _ =>
    ik_bind (ik_gets _) fun _ => ik_when _ (ec_schedContextUnbindTcb σ0 p)

/-! ## The SchedContext arms -/

/-- The SchedContext arms covered here (all but binding a TCB). -/
def CovSc : SchedContextInvocation → Prop
  | .invokeSchedContextBind _ (.threadCap _) => False
  | _ => True

theorem perfA_schedContext {σ0 s : State Unit} (bl call don : Bool) (i : SchedContextInvocation) (hc : CovSc i)
    (hB : A10.BS σ0) (hS : Suff σ0) (h0 : TB σ0 s) : PerfA σ0 bl call don (.invokeSchedContext i) s := by
  refine perfA_liftEC _ rfl hB hS ?_ (ec_of_tb h0)
  cases i with
  | invokeSchedContextConsumed p =>
    show IK (EC σ0) (returnConsumed (Z := Unit) p)
    exact ec_svcf (by unfold returnConsumed schedContextUpdateConsumed; sv_auto) (cfk_returnConsumed' p)
  | invokeSchedContextBind p cap =>
    cases cap
    case threadCap t => exact (hc : False).elim
    case notificationCap n b r =>
      show IK (EC σ0) (do schedContextBindNtfn (Z := Unit) p n; return [])
      exact ec_svcf (by unfold schedContextBindNtfn; sv_auto) (by cfk_auto)
    all_goals exact ik_fail
  | invokeSchedContextUnbindObject p cap =>
    cases cap
    case threadCap t =>
      show IK (EC σ0) (do schedContextUnbindTcb (Z := Unit) p; return [])
      exact ik_bind (ec_schedContextUnbindTcb σ0 p) fun _ => ik_pure _
    case notificationCap n b r =>
      show IK (EC σ0) (do schedContextUnbindNtfn (Z := Unit) p; return [])
      exact ec_svcf (by sv_auto; all_goals exact B8f.sv_schedContextUnbindNtfn' p) (by cfk_auto)
    all_goals exact ik_fail
  | invokeSchedContextUnbind p =>
    show IK (EC σ0) (do
      schedContextUnbindAllTcbs (Z := Unit) p
      schedContextUnbindNtfn (Z := Unit) p
      schedContextUnbindReply (Z := Unit) p
      return [])
    refine ik_bind (ec_schedContextUnbindAllTcbs σ0 p) fun _ => ?_
    refine ik_bind (ec_svcf (B8f.sv_schedContextUnbindNtfn' p) (cfk_schedContextUnbindNtfn' p)) fun _ => ?_
    exact ik_bind (ec_svcf (B8f.sv_schedContextUnbindReply' p) (cfk_schedContextUnbindReply' p)) fun _ => ik_pure _
  | invokeSchedContextYieldTo p =>
    show IK (EC σ0) (schedContextYieldTo (Z := Unit) p)
    exact ec_svcf (by unfold schedContextYieldTo returnConsumed schedContextUpdateConsumed; sv_auto)
      (cfk_schedContextYieldTo' p)

/-! ## CNode cancelBadgedSends -/

/-- `if_sporadic_cur_sc_assert_refill_unblock_check`-style guards skip cur_sc. -/
theorem cp_ifCondAssert (o : Option ObjRef) (a : Option Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (ifCondRefillUnblockCheck (Z := Unit) o a (some true)) := by
  unfold ifCondRefillUnblockCheck
  refine ik_maybeM (fun p => ?_) o
  refine ik_bind (by cp_leaf) fun sc => ?_
  intro s hs y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  dsimp only at hy
  unfold NonDet.when at hy
  split_ifs at hy with h1 h2 <;> first
    | (rw [Set.mem_singleton_iff.1 hy]; exact hs)
    | exact A8.cp_refillUnblockCheck_ne p (fun e => h2 rfl (e.trans hs.1.symm)) σ0 s hs y hy
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_ifCondAssert _ _ _ _)

theorem nks_ifCondG (o : Option ObjRef) (a b : Option Bool) :
    Ipc.NKS (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  cases o with
  | none => exact Ipc.nks_pure' _
  | some p =>
    unfold ifCondRefillUnblockCheck NonDet.maybeM
    repeat (first | exact Ipc.nks_refillUnblockCheck _ | nks_step)

macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact SInvR.sv_tcbEpDequeue _ _)

/-- The `BL` walk of cancelBadgedSends. -/
macro "bl14d_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact bl_possibleSwitchTo _ _ _)
  | (exact bl_of_nks (nks_ifCondG _ _ _))
  | (refine bl_of_svm ?_; sv_auto; done)
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when)
  | ik_step0))

theorem tb_cancelBadgedSends (σ0 : State Unit) (ep : ObjRef) (b : Badge) :
    IK (TB σ0) (cancelBadgedSends (Z := Unit) ep b) :=
  tb_ik (cfk_cancelBadgedSends' ep b)
    (by unfold cancelBadgedSends removeAndRestartBadgedThread restartThreadIfNoFault; cp_auto)
    (by unfold cancelBadgedSends removeAndRestartBadgedThread restartThreadIfNoFault; bl14d_auto)

theorem perfA_cancelBadged {σ0 s : State Unit} (bl call don : Bool) (cap : Cap) (hB : A10.BS σ0) (hS : Suff σ0)
    (h0 : TB σ0 s) : PerfA σ0 bl call don (.invokeCNode (.cancelBadgedSendsCall cap)) s := by
  refine perfA_ikeTB hB hS ?_ ?_ h0
  · show IKE (TB σ0) (invokeCnode (Z := Unit) (.cancelBadgedSendsCall cap) >>= fun _ => NonDetE.returnOk [])
    refine ike_bind ?_ fun _ => ike_returnOk _
    cases cap
    case endpointCap ep b r => exact ike_liftE (ik_when _ (tb_cancelBadgedSends σ0 ep b))
    all_goals exact ike_liftE ik_fail
  · show NoErr (invokeCnode (Z := Unit) (.cancelBadgedSendsCall cap) >>= fun _ => NonDetE.returnOk [])
    refine noErr_bind ?_ fun _ => noErr_returnOk _
    cases cap <;> exact noErr_liftE _

/-! ## Covered set -/

def CovD : Fl4Invocation → Prop
  | .invokeSchedContext i => CovSc i
  | .invokeCNode (.cancelBadgedSendsCall _) => True
  | _ => False

theorem armA_covD : ArmA CovD := by
  intro σ0 u bl cl dn b hc h
  cases b
  case invokeSchedContext i => exact perfA_schedContext bl cl dn i hc h.bs h.suff h.tb
  case invokeCNode i =>
    cases i
    case cancelBadgedSendsCall cap => exact perfA_cancelBadged bl cl dn cap h.bs h.suff h.tb
    all_goals exact (hc : False).elim
  all_goals exact (hc : False).elim

/-- rd14c's covered set and this module's arms. -/
def C14d (b : Fl4Invocation) : Prop := C14c b ∨ CovD b

theorem armA_c14d : ArmA C14d := armA_c14c.or armA_covD

end

end Fl4Proofs.P3.SInvR.A14d
