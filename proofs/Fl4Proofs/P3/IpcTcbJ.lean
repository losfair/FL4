/-
P3 (DESIGN.md §9), TCB invocations: **the IPC side's TCB leaves on `JAt`**
(the fold's re-scoping, plan §0): each leaf takes `JAtZ` at the decode's
start in place of its "at every `XTopAt`" bundles.

* `jat_restart`: `JAtZ` across the caller's restart (CSpace's
  `JStepHyps.restart` [W], with `JAtZ.cs_frame`, as `stepClosed_jat`).
* `xleaf_restartJ`: an `XLeaf` from `JAtZ` (its `XTopAt` in place of the
  leaf's own), `JAtZ` after the restart for the rest.
-/
import Fl4Proofs.P3.IpcSchedTail
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.ScIpcSorted
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- The current thread at `XTopAt`: the core's `CUR_THREAD` word, a TCB. -/
theorem xtop_cur {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) :
    ∃ ct : U64, σ.curThread = ct.bv ∧ ∃ x, σ.kheap σ.curThread = some (.tcb x) := by
  obtain ⟨Q, R0, hc, hs⟩ := hX.fin.1.1.1.lists
  have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
    rw [hs.curThread, hc.cur]; rfl
  obtain ⟨-, x, hk⟩ := hX.curTcb hcur
  exact ⟨_, hcur, x, by rw [hcur]; exact hk⟩

set_option maxHeartbeats 4000000 in
/-- **`JAtZ` across the caller's restart** (module docstring). -/
theorem jat_restart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    {ct : U64} (hcur : σ.curThread = ct.bv) {s1 : S} (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False)) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a σ1 := by
  have hX := J.xtop
  obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := J.curRun.run hni x (by rw [hcur]; exact hk)
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hk] at hst
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hst))).2).symm
  subst hσ1
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ hJS hcur hk htcb hrun hs1
  exact ⟨Ac', Lst', D, J1⟩

set_option maxHeartbeats 4000000 in
/-- **A TCB leaf from `JAtZ`** (module docstring): the leaf's `XTop` is not
used; the rest on `JAtZ` after the restart (with `IRel` and the TCBs kept
but for their states), `IRel` after. -/
theorem xleaf_restartJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    {g : S → Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hI : ∀ (s1 : S) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 ar σ1 →
      (∀ q y, σ1.kheap q = some (.tcb y) → ∃ y0, σ.kheap q = some (.tcb y0) ∧ y = { y0 with tcbState := y.tcbState }) →
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s1 σ1 →
      g s1 ⦃ r => r.1 = .Ok () ∧ AR r.2.2 σ.archState.x64CurrentCr3 ∧ ∃ z ∈ spec.1,
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄) :
    XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← tcb.restart_caller st s
      g s1) spec := by
  intro _
  have hX := J.xtop
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  set ct := L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) with hctd
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hctd, hc.cur]; rfl
  obtain ⟨-, x, hk⟩ := hX.curTcb hcur
  have hrun : Fl4Spec.runnable x.tcbState = true := J.curRun.run hni x (by rw [hcur]; exact hk)
  have hst' := hst
  rw [hcur] at hst'
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have hcr : σ1.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3 := by
    rw [hσ1]; unfold Notif.stsAct; split <;> rfl
  have hkeep : ∀ q y, σ1.kheap q = some (.tcb y) → ∃ y0, σ.kheap q = some (.tcb y0) ∧
      y = { y0 with tcbState := y.tcbState } := by
    intro q y hq
    rw [hσ1, Notif.stsAct_kheap] at hq
    by_cases e : q = ct.bv
    · subst e; simp [Notif.updK] at hq; subst hq; exact ⟨x, hk, rfl⟩
    · simp only [Notif.updK, Function.update_of_ne e] at hq; exact ⟨y, hq, rfl⟩
  have hR := XTopAt.restart hX hcur hk hrun
  unfold tcb.restart_caller
  step with P1.sched.cur_thread.spec as ⟨ct', hct'⟩
  subst hct'
  obtain ⟨s1, hs1, -⟩ := spec_exists hR
  rw [hs1]
  obtain ⟨Ac', Lst', D', J'⟩ := jat_restart J hni hJS hcur hs1 hst'
  have hI1 := J'.xtop.irelK J'.ks J'.buf
  rw [hcr] at hI1
  try simp only [bind_tc_ok, bind_ok]
  refine WP.spec_mono (hI s1 Ac' Lst' D' J' hkeep hI1) ?_
  rintro r ⟨h1, hAR, z, hz, hI2⟩
  obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (L := L) (AR := AR) (a := r.2.2) hI2 hAR
  exact ⟨h1, z, hz, (SRT.relTop hI2).1, Z', hZ'⟩


/-- **The caller's restart in the spec**: one TCB's state, the scheduler
action at most (`stsAct`); the release queue, the current thread and the
queues' order kept. -/
theorem restart_facts {σ σ1 : Fl4Spec.State Unit} {x : Fl4Spec.Tcb} (hk : σ.kheap σ.curThread = some (.tcb x))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) :
    σ1 = Notif.stsAct (Notif.updK σ σ.curThread (.tcb { x with tcbState := .restart })) σ.curThread ∧
      σ1.releaseQueue = σ.releaseQueue ∧ σ1.curThread = σ.curThread ∧ (Sched.IpcSorted σ → Sched.IpcSorted σ1) := by
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ σ.curThread (.tcb { x with tcbState := .restart })) σ.curThread := by
    rw [Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  refine ⟨hσ1, ?_, ?_, fun hS => ?_⟩
  · rw [hσ1]; unfold Notif.stsAct; split <;> rfl
  · rw [hσ1]; try (unfold Notif.stsAct; split <;> rfl)
  · have hkh : σ1.kheap = Function.update σ.kheap σ.curThread (some (.tcb { x with tcbState := .restart })) := by
      rw [hσ1, Notif.stsAct_kheap]; rfl
    refine hS.frame (fun q x' hq => ?_) (fun q x' hq => ?_) (fun u => ?_)
    · rw [hkh] at hq
      by_cases e : q = σ.curThread
      · subst e; simp at hq
      · rw [Function.update_of_ne e] at hq; exact ⟨x', hq, rfl⟩
    · rw [hkh] at hq
      by_cases e : q = σ.curThread
      · subst e; simp at hq
      · rw [Function.update_of_ne e] at hq; exact ⟨x', hq, rfl⟩
    · unfold Sched.prioOf
      rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq, hkh]
      by_cases e : u = σ.curThread
      · subst e; rw [Function.update_self, hk]; rfl
      · rw [Function.update_of_ne e]

set_option maxHeartbeats 4000000 in
/-- **SetPriority from `JAtZ`** (`setPrioXLeaf_of` re-scoped): the restart
(`xleaf_restartJ`), `set_priority_irel` with `JAtZ`'s `SchedValid`, `Inv`
(hence `ActReady`), `ObjCover` and sorted queues (`IpcSorted`, hence
`QSorted`) after the restart. The current thread in no release queue (l4v
`ct_not_in_release_q`) is `CurInv.notRel` at the decode's start, where no
reschedule is pending (P1's `DecPre.act`), carried across the restart (which
keeps the release queue). -/
theorem setPrioXLeafJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p v : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hv : v.val < 256)
    (hpT : p ∈ Z.T) (hres : σ.schedulerAction = .resumeCurThread) :
    SetPrioXLeaf (L := L) AR s ar σ σ1 p v := by
  have hNR : σ.curThread ∉ σ.releaseQueue := (J.curInv (by rw [hres]; exact fun h => nomatch h)).notRel
  obtain ⟨ct, hcur, x, hk⟩ := xtop_cur J.xtop
  obtain ⟨-, hrq, hct, -⟩ := restart_facts hk hst
  refine xleaf_restartJ J hni hJS hst fun s1 Ac' Lst' D' J' _ hI1 => ?_
  have hP0 := J.ip
  have hAR : AR ar σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hQ := Sched.qSorted_of_spec (L := L) hI1.1.toE hI1.1.toN hP0.e.tcb J'.isorted
  refine WP.spec_bind (set_priority_irel hP0 hI1 hpT v hv J'.inv.actReady
    (fun h => by rw [hrq]; rw [hct] at h; rw [← h]; exact hNR) J'.sv J'.inv J'.obj
    (fun e he => hQ e (Or.inl he)) (fun e he => hQ e (Or.inr he))) ?_
  rintro s2 ⟨σ2, hm, hI2⟩
  simp only [WP.spec_ok]
  exact ⟨trivial, hAR, ((), σ2), by rw [hm]; exact Set.mem_singleton _, hI2⟩


set_option maxHeartbeats 4000000 in
/-- **UnbindNotification from `JAtZ`** (`unbindXLeaf_of` re-scoped): the
restart (`xleaf_restartJ`), the bound notification by `JAtZ`'s `SchedValid`
and `ObjCover` after it, the two bound words (`bound_wr_irel`). Nothing named
beyond the target among the TCBs. -/
theorem unbindXLeafJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hb0 : L.mem s (P1.boundA p) ≠ 0#u64) (hpT : p ∈ Z.T) :
    UnbindXLeaf (L := L) AR s ar σ σ1 p := by
  refine xleaf_restartJ J hni hJS hst fun s1 Ac' Lst' D' J' hkp hI1 => ?_
  have hP0 := J.ip
  have hAR : AR ar σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hI0 := J.xtop.irelK J.ks J.buf
  obtain ⟨x0, hk0, hx0⟩ := hI0.1.tcb p hpT
  obtain ⟨x1, hk1, hx1⟩ := hI1.1.tcb p hpT
  have hb1 : L.mem s1 (P1.boundA p) ≠ 0#u64 := by
    intro h0
    have e1 : x1.tcbBoundNotification = none := by
      rw [hx1.bound]; show Notif.optRef (L.mem s1 (P1.boundA p)) = none; rw [h0]; rfl
    have e0 : x0.tcbBoundNotification ≠ none := by
      rw [hx0.bound, show tBoundA p = P1.boundA p from rfl, Notif.optRef_ne hb0]; simp
    obtain ⟨y0, hy0, ey⟩ := hkp _ _ hk1
    rw [hk0] at hy0; cases hy0
    exact e0 (by rw [ey] at e1; exact e1)
  obtain ⟨x, xn, hk, hb, hn, hkn⟩ := bound_ntfn_of hI1 J'.sv J'.obj hpT hb1
  have hX2 := bound_wr_irel hP0 hI1 hpT hn hk hkn 0#u64 0#u64 (fun h => absurd rfl h)
  rw [Notif.optRef_zero] at hX2
  rw [Sched.unbind_ntfn_eq s1 p hb1]
  simp only [bind_ok, WP.spec_ok]
  refine ⟨trivial, hAR, ((), _), ?_, hX2⟩
  rw [Sched.unbindNotification_eq hkn hk hb]
  exact Set.mem_singleton _

set_option maxHeartbeats 4000000 in
/-- **BindNotification from `JAtZ`** (`bindXLeaf_of` re-scoped). Named: the
target among the TCBs, the notification among the notifications and not at
address 0 (the decode's cap, l4v `valid_cap`). -/
theorem bindXLeafJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} {p q : U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hpT : p ∈ Z.T) (hqN : q ∈ Z.N) (hq0 : q ≠ 0#u64) :
    BindXLeaf (L := L) AR s ar σ σ1 p q := by
  refine xleaf_restartJ J hni hJS hst fun s1 Ac' Lst' D' J' _ hI1 => ?_
  have hP0 := J.ip
  have hAR : AR ar σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨x, hk, -⟩ := hI1.1.tcb p hpT
  obtain ⟨xn, hkn, -⟩ := hI1.1.ntfn q hqN
  have hp0 : p ≠ 0#u64 := fun e => (hP0.e.tcb p hpT).ne0 (by rw [e]; rfl)
  have hX2 := bound_wr_irel hP0 hI1 hpT hqN hk hkn p q (fun _ => hpT)
  rw [Notif.optRef_ne hp0, Notif.optRef_ne hq0] at hX2
  rw [Sched.bind_ntfn_eq s1 p q]
  simp only [bind_ok, WP.spec_ok]
  refine ⟨trivial, hAR, ((), _), ?_, hX2⟩
  rw [Sched.bindNotification_eq hkn hk]
  exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
