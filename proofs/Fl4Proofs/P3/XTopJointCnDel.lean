/-
P3 (DESIGN.md §9), CSpace: **CNode Delete and Revoke with `JAt` after**, the
deletion loop run with a `JAtZ`-carrying invariant (`WJ`), so that the
deletion's premises are stated at `JAtZ` states (not at every `XTopAt`
state, as `XFinHyps`/`XPreemptHyp`, whose [J] premises no invariant can
supply).

* `WJ`, `EJ`, `JDelHyp`, `JPreemptHyp` [J] and `JDelParts` (the named steps
  of the deletion loop at `WJ`, from which `JDelHyp.of_parts` derives
  `JDelHyp`): XTopJointDelR.
* `EJ.restart`: the caller's restart keeps `EJ` (`JStepHyps.restart`).
* `TopPostDMXP`, `XCapP`: `TopPostDMX`, `XCap` with `XP` after a preempted
  invocation (`X` after any other); `XCap.toP` from `XCap` when `X → XP`.
  `JAtPre`: the post of a preempting preemption point from `JAt` with no
  switch pending and a current thread other than the idle thread (the time
  updated, the current SC's budget possibly exhausted: the caller's
  `mcs_preemption_point` charges it). `TopPostDMX.toPN`/`XCap.toPN`/
  `TopPostDMX.errP`: `XP` arbitrary when the outcome cannot be preempted
  (SpecNoPre: no `PreInv` invocation decoded, or an error).
* `cn_del_topJ`: a Delete's or Revoke's outcome at `EJ` (`EJP` if preempted)
  gives `TopPostDMXP` at `JAt`, `JAtPre`.
* `decode_invocation_cnode_{revoke,delete}J`: the Revoke and Delete labels
  with `JAt` after (`JAtPre` if preempted), from `JAtZ` and `PPR0` (ScPPR)
  at the start, `JStepHyps`, `JDelHyp`, `JPreemptHyp`.
* `JAtZ.ppr0_start`: `PPR0` at the invocation's start, from `Entered` and
  the current SC's head ready at a zero consumed time (`hRd0` [J]).
* (The CNode cap with `JAt` after, every label: XTopJointWJLRestart's
  `decode_invocation_cnodeJ_stepsL`, the deletion at `WJL`.)
-/
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.XTopJointPost
import Fl4Proofs.P3.XTopJointCbs
import Fl4Proofs.P3.XTopJointDelLive
import Fl4Proofs.P3.SpecNoPre
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The caller's restart keeps `EJ`** (`JStepHyps.restart`, `cs_frame`). -/
theorem EJ.restart (hJ : JStepHyps (L := L) arI AR Z.th) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ) {K : Nat}
    (hDE : DelE (L := L) Z.th K s σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      EJ (L := L) arI AR Z H Cs (L.ksb s) K s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 hS hst
  have hsg1 : SpecGlob σ1 := SpecGlob.sts (mem_of_single hst) hsg
  have hDE1 := delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) hst)
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  refine ⟨hDE1, ?_⟩
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ hJ hcur hk htcb hrun hs1
  have hns1 : Vs.NoSwitch (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  exact ⟨Z.vs, Ac', Lst', D, J1, hk1, hns1, hsg1,
    hP0.of_ppk (PPK.restart hk .restart (Or.inl hcur.symm))⟩

/-- **`PPR0` at the invocation's start**: at a zero consumed time, the
current SC's head ready when active (`hRd0` [J], l4v `cur_sc_offset_ready 0`
at the invocation: the running thread's SC released), and no reschedule
pending (`Entered`), so the current thread is the current SC's only thread
(`CurInv`, `Inv.back`) and outside the release queue (`CurInv.notRel`). -/
theorem JAtZ.ppr0_start {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) : PPR0 σ := by
  refine ⟨⟨hni.1, fun u e => (by rw [hni.2] at e; cases e), fun xt hx => ?_, fun u xt hu hus => ?_, hnq⟩,
    fun h0 => ?_⟩
  · obtain ⟨xc, hkc, hsc, -⟩ := (J.curInv (by rw [hni.2]; exact fun h => by cases h)).tcb
    have e : xt = xc := by rw [hkc] at hx; cases hx; rfl
    subst e
    exact ⟨Or.inl hsc, NotBlk.of_runnable (J.curRun.run hni _ hkc)⟩
  · obtain ⟨xc, hkc, hsc, -⟩ := (J.curInv (by rw [hni.2]; exact fun h => by cases h)).tcb
    obtain ⟨y, n, hy, hyt⟩ := J.inv.back u xt _ hu hus
    obtain ⟨y', n', hy', hyt'⟩ := J.inv.back _ xc _ hkc hsc
    rw [hy] at hy'; cases hy'
    rw [hyt] at hyt'; cases hyt'
    exact Or.inl rfl
  refine ⟨hRd0 h0, fun u xt hu hus hur => ?_⟩
  have hC := J.curInv (by rw [hni.2]; exact fun h => by cases h)
  obtain ⟨xc, hkc, hsc, -⟩ := hC.tcb
  obtain ⟨y, n, hy, hyt⟩ := J.inv.back u xt _ hu hus
  obtain ⟨y', n', hy', hyt'⟩ := J.inv.back _ xc _ hkc hsc
  rw [hy] at hy'; cases hy'
  rw [hyt] at hyt'; cases hyt'
  exact hC.notRel hur

/-! ## The outcome after a preemption -/

/-- **`TopPostDMX` with `XP` after a preempted invocation**, `X` after any
other outcome. -/
def TopPostDMXP (X XP : S → A → Fl4Spec.State Unit → Prop) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (s : S) (res : core.result.Result Unit error.Exc × S × A) :
    Prop :=
  TopPostDMX (L := L) (fun s a σ => if res.1 = .Err .Preempted then XP s a σ else X s a σ) σ blk call don m s res

/-- `DecOKDMX` with `XP` after a preempted invocation. -/
abbrev DecOKDMXP (X XP : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl length slot : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostDMXP (L := L) X XP σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

/-- **`XCap` with `XP` after a preempted invocation.** -/
def XCapP (X XP : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  DecOKDMXP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ∨
    DecOKRMX (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct

theorem TopPostDMX.toP {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMX (L := L) X σ blk call don m s res) (hXP : ∀ s a σ, X s a σ → XP s a σ) :
    TopPostDMXP (L := L) X XP σ blk call don m s res :=
  have hI : ∀ s a σ, X s a σ → (if res.1 = .Err .Preempted then XP s a σ else X s a σ) := fun s a σ hx => by
    split
    · exact hXP s a σ hx
    · exact hx
  match h with
  | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, hI _ _ _ h4⟩
  | Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩ => Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hI _ _ _ h4⟩

/-- **`XCap` gives `XCapP`** when `X → XP`. -/
theorem XCap.toP {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hXP : ∀ s a σ, X s a σ → XP s a σ) :
    XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono h fun _ hr => hr.toP hXP)
  · exact Or.inr h

/-- **The post of a preempting preemption point from `JAt`**, no switch
pending and `PPR0` there (carried by the deletion and reset loops from
`Entered`; kp11: all of it, for the release-queue fact at the hole): what a preempted invocation
leaves (module docstring; kp10). -/
def JAtPre (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit),
    (JAt (L := L) arI AR s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1

/-- **A `TopPostDMX` outcome other than `Preempted` is `TopPostDMXP` at any
`XP`.** -/
theorem TopPostDMX.toPne {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMX (L := L) X σ blk call don m s res) (hne : res.1 ≠ .Err .Preempted) :
    TopPostDMXP (L := L) X XP σ blk call don m s res :=
  have hI : ∀ s a σ, X s a σ → (if res.1 = .Err .Preempted then XP s a σ else X s a σ) := fun s a σ hx => by
    rw [if_neg hne]; exact hx
  match h with
  | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, hI _ _ _ h4⟩
  | Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩ => Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hI _ _ _ h4⟩

/-- **`TopPostDMX` gives `TopPostDMXP` at any `XP`** when no decoded
invocation has a preemption point (SpecNoPre's `PreInv`): the outcome is
not `Preempted` (`TopPostDMX.not_preempted`). -/
theorem TopPostDMX.toPN {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMX (L := L) X σ blk call don m s res) (hnp : ∀ inv, DecOut m σ inv → ¬ NoPre.PreInv inv) :
    TopPostDMXP (L := L) X XP σ blk call don m s res :=
  TopPostDMX.toPne h (TopPostDMX.not_preempted (L := L) h hnp)

/-- **An error outcome of `TopPostDMX` is `TopPostDMXP` at any `XP`**: no
spec error is related to `Preempted` (`ErrRel.not_preempted`). -/
theorem TopPostDMX.errP {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : ∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ (∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∧
      X res.2.1 res.2.2 σ) :
    TopPostDMXP (L := L) X XP σ blk call don m s res := by
  obtain ⟨e, h1, h2, ⟨e', h3, h3'⟩, h4⟩ := h
  have hne : res.1 ≠ .Err .Preempted := by
    rw [h1]; intro he; cases he; exact ErrRel.not_preempted h3'
  exact Or.inl ⟨e, h1, h2, ⟨e', h3, h3'⟩, show (if res.1 = .Err .Preempted then XP res.2.1 res.2.2 σ else
    X res.2.1 res.2.2 σ) by rw [if_neg hne]; exact h4⟩

/-- **`XCap` gives `XCapP` at any `XP`** when the cap's spec decode yields
no invocation with a preemption point (`TopPostDMX.toPN`). -/
theorem XCap.toPN {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hnp : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → ¬ NoPre.PreInv inv) :
    XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono h fun _ hr => hr.toPN hnp)
  · exact Or.inr h

/-- **A cap other than a CNode, Untyped or Thread cap** decodes to no
invocation with a preemption point (SpecNoPre's `decOut_noPre`). -/
theorem specDec_noPre {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit}
    (hc : ∀ p r gs g, c ≠ .CNode p r gs g) (hu : ∀ p sb fi dev, c ≠ .Untyped p sb fi dev) (ht : ∀ p, c ≠ .Thread p) :
    ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → ¬ NoPre.PreInv inv := by
  intro inv h
  refine NoPre.decOut_noPre ?_ ?_ ?_ h
  all_goals cases c <;> first
    | exact (hc _ _ _ _ rfl).elim | exact (hu _ _ _ _ rfl).elim | exact (ht _ rfl).elim | simp [absCap]

/-- **A CNode cap at a label other than Revoke and Delete** decodes to no
invocation with a preemption point (SpecNoPre's `dec_cnode_noPre`). -/
theorem specDec_cnode_noPre {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {p r gs g : U64}
    (hr : Fl4Spec.genInvocationType slbl ≠ .cnodeRevoke) (hd : Fl4Spec.genInvocationType slbl ≠ .cnodeDelete) :
    ∀ inv, DecOut (specDec fp slbl args ci sl (.CNode p r gs g) excaps buffer) σ inv → ¬ NoPre.PreInv inv := by
  intro inv h
  have hO : NoPre.OkP (fun inv => ¬ NoPre.PreInv inv) (specDec fp slbl args ci sl (.CNode p r gs g) excaps buffer) := by
    simp only [specDec, absCap, Fl4Spec.fl4DecodeInvocation, Fl4Spec.NonDetE.throwError]
    split
    · exact NoPre.okP_throw
    · exact NoPre.okP_liftME' (NoPre.dec_cnode_noPre slbl args _ _ hr hd) fun _ h => h
  exact hO σ _ h.1 inv rfl

/-- **A Thread cap at a label other than the five installing ones** decodes
to no invocation with a preemption point (SpecNoPre's `dec_thread_noPre`). -/
theorem specDec_thread_noPre {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {p : U64}
    (h1 : Fl4Spec.genInvocationType slbl ≠ .tcbConfigure) (h2 : Fl4Spec.genInvocationType slbl ≠ .tcbSetSchedParams)
    (h3 : Fl4Spec.genInvocationType slbl ≠ .tcbSetTimeoutEndpoint)
    (h4 : Fl4Spec.genInvocationType slbl ≠ .tcbSetIPCBuffer) (h5 : Fl4Spec.genInvocationType slbl ≠ .tcbSetSpace) :
    ∀ inv, DecOut (specDec fp slbl args ci sl (.Thread p) excaps buffer) σ inv → ¬ NoPre.PreInv inv := by
  intro inv h
  have hO : NoPre.OkP (fun inv => ¬ NoPre.PreInv inv) (specDec fp slbl args ci sl (.Thread p) excaps buffer) := by
    simp only [specDec, absCap, Fl4Spec.fl4DecodeInvocation, Fl4Spec.NonDetE.throwError]
    split
    · exact NoPre.okP_throw
    · exact NoPre.dec_thread_noPre slbl args _ sl excaps buffer h1 h2 h3 h4 h5
  exact hO σ _ h.1 inv rfl

/-- A cap other than a CNode, Untyped or Thread cap (`True` by `trivial`
for each concrete such cap). -/
def NoPreKind : capability.Cap → Prop
  | .CNode .. => False
  | .Untyped .. => False
  | .Thread _ => False
  | _ => True

/-- `specDec_noPre` from `NoPreKind`. -/
theorem specDec_noPreK {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} (hk : NoPreKind c) :
    ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → ¬ NoPre.PreInv inv :=
  specDec_noPre (fun _ _ _ _ e => by subst e; exact hk) (fun _ _ _ _ e => by subst e; exact hk)
    (fun _ e => by subst e; exact hk)

set_option maxHeartbeats 4000000 in
/-- **A Delete's or Revoke's outcome at `J`**: from `PInvPostW` at `EJ`
(`EJP` if preempted), `TopPostDMXP` at `JAt`, `JAtPre` (the decode errors
at the start's `JAtZ`). -/
theorem cn_del_topJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    {kb : U64} {K : Nat} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (EJ (L := L) arI AR Z H Cs kb K) (EJP (L := L) arI AR Z H Cs kb K) s ar
      res) :
    TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ |
    ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR', hFI', -, hE'⟩
  · have hne : e ≠ .Preempted := by rintro rfl; cases e' <;> exact h2.elim
    refine Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ?_⟩
    simp only [core.result.Result.Err.injEq, hne, if_false]
    exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
  · rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · obtain ⟨-, V, Ac', Lst', D', J', -⟩ := hE'
      have hX' := J'.xtop
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
      simp only [reduceCtorEq, if_false]
      exact ⟨_, H, Cs, Ac', Lst', D', J'⟩
    · obtain ⟨-, s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hE'
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.error (), σ'),
        mem_bindE_err hx, ⟨Z.th, G', Or.inr ⟨rfl, rfl⟩, J.xtop.rel.1, hCR', hFI', hDom, hMO⟩, ?_⟩
      simp only [if_true]
      exact ⟨s0, a0, σ0, ⟨⟨_, H, Cs, Ac', Lst', D', J0⟩, hns0, hp00⟩, hpp, hspp⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Revoke label** (25): `cnode_revoke_refinesW` at
`EJ` (`JDelHyp`, `rppHyp_fullW` of `JPreemptHyp`, `EJ.restart`), then
`cn_del_topJ`. -/
theorem decode_invocation_cnode_revokeJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hJD : JDelHyp (L := L) arI AR Z.th) (hJP : JPreemptHyp (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.CNodeRevoke length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hfew : psiD (L.mem s) Z.G < 2 ^ 64 - 1 := by
    have := hDE.2.1 Z.G hM
    omega
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_revoke_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJ (L := L) arI AR Z H Cs (L.ksb s) K)
      (EJP (L := L) arI AR Z H Cs (L.ksb s) K)
      psiD psiD_slotsSame (hJD Z H Cs (L.ksb s) K rfl hK hK6)
      (rppHyp_fullW arI (WJR (L := L) arI AR Z H Cs (L.ksb s)) (WJP (L := L) arI AR Z H Cs (L.ksb s)) Z.th K
        (hJP Z H Cs (L.ksb s) rfl))
      (EJ.restart arI hJ J hni hsg hP0 hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩) hfew)
      fun res h => cn_del_topJ arI J h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨Z, H, Cs, Ac, Lst, D, J⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Delete label** (26), for any cap: as
`decode_invocation_cnode_revokeJ`, by `cnode_delete_refinesW` at `EJ`. -/
theorem decode_invocation_cnode_deleteJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hJD : JDelHyp (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.CNodeDelete length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_delete_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJ (L := L) arI AR Z H Cs (L.ksb s) K)
      (EJP (L := L) arI AR Z H Cs (L.ksb s) K)
      psiD (hJD Z H Cs (L.ksb s) K rfl hK hK6) (EJ.restart arI hJ J hni hsg hP0 hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      fun res h => cn_del_topJ arI J h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨Z, H, Cs, Ac, Lst, D, J⟩

end

end

end Fl4Proofs.P3
