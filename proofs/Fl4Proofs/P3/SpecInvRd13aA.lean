/-
P3 (DESIGN.md §9), invariant line G1 (rd13a, KENTRY-PLAN rd12a handoff 1-2,
rd12b handoff 3): **rd12a's `RcvB` discharged, the receive tail after the
send half, the tops `kcall_rdyOff6` / `kentry_rdyOff6`** (spec side only).

* `rt_of_bs` (rd8d's `RT ct` from rd10's `BS`: CAx + CurScT + OffReady),
  `rcvS_of_bs` (rd8e's `RcvS ct` from `BS` and ctq's `EB true`: `T1` from
  the TQ inside SQ4, `ct ∉ releaseQueue` from `NP` inside `RBk true`).
* `evp_uts` / **`evp_front`** (ctq17's `EvP` across the syscall front: over
  `update_time_stamp` by `evp_auto`, `check_budget_restart` returning `true`
  keeps the state), **`rcvB_of`**: `A8.EF σ ∧ EvP … σ ⇒ RcvB σ`.
* **`ss4_handleRecvK`**: rd12a's `ss4_handleRecv` re-anchored: from the body
  start σ0 (`BS σ0`, `Suff σ0`) and a later state `s` with rd11a's `KP σ0 s`,
  ct bound to cur_sc, `RcvS s ct`, `EB true s`, `NQ [ct] s`, every
  `handle_recv` outcome has `SS4`.
* `RcvR` (the part of `RcvS` ctq does not carry), `rcvS_of_r`, **`RecvA σ0 cr
  t`** (at an `ok` outcome `t` of the first-phase invocation: `KP σ0 t ∧ ct
  bound to cur_sc ∧ RcvR t`, or — the open part — the receive tail's
  `CB → SS4` directly), `RecvTA` (`RecvA` at every such outcome of the given
  entry), **`recvT_of`**: `RecvTA ⇒ ` rd12b's `RecvT` (EB true / NQ [ct] /
  ct at the invocation outcome from ctq's `eb_fl4HandleInvocationR`,
  `nq_fl4HandleInvocationR`, `ct_fl4HandleInvocationR`).
* `fip_evp` (rd12b's `ebx_fip` preamble: `EvP` and ct ≠ idle at the FaultIP
  outcome); tops **`kcall_rdyOff6` / `kentry_rdyOff6`**: rd12b's
  `*_rdyOff4r` with `hOsR` discharged (rd12a's `osBody_recv` + `rcvB_of`) and
  `RecvT` narrowed to `RecvTA`.
-/
import Fl4Proofs.P3.SpecInvRd12aC
import Fl4Proofs.P3.SpecInvRd12bC
open Classical

namespace Fl4Proofs.P3.SInvR.A13a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.A11 Fl4Proofs.P3.SInvR.A12a

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `RcvS` at a body start -/

/-- rd8d's `RT ct` at a body start. -/
theorem rt_of_bs {s : State Unit} (h : A10.BS s) : B8d.RT s s.curThread := by
  intro x c hx hc
  obtain ⟨x', c', y, n, h1, h2, h3, h4⟩ := h.ca h.ni
  have ex : x = x' := KernelObject.tcb.inj (Option.some.inj (hx.symm.trans h1))
  subst ex
  have e1 : c' = s.curSc := Option.some.inj (h2.symm.trans (h.cs x hx))
  subst e1
  exact ⟨x, s.curSc, y, n, hx, h2, h3, h4, ready_of_nat (Nat.le_trans (Nat.le_add_right _ _) (h.off y n h3))⟩

/-- **rd8e's `RcvS ct`** from `BS` and ctq's `EB true`. -/
theorem rcvS_of_bs {s : State Unit} (h : A10.BS s) (hE : SInvQ.EB true s) : B8e.RcvS s s.curThread := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  refine ⟨h.rdy, SInvQ.tq_t1 hE.1.1.1.1, h.sc, h.si, h.q, (hE.2.1.2.1 rfl).2.2, ⟨xt, hct, fun f hf => ?_⟩,
    rt_of_bs h⟩
  rcases hst with e | e <;> rw [e] at hf <;> simp [BlkR] at hf

/-! ## The re-anchored receive tail -/

/-- ct bound to cur_sc. -/
abbrev CtB (s : State Unit) : Prop :=
  ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc

/-- **`SS4` after `handle_recv` from a later state** `s` of the body (σ0 = the
body start): rd12a's `ss4_handleRecv` with the invariant `· = s` and rd11a's
frame `KP σ0 s` in place of `KP.refl`. -/
theorem ss4_handleRecvK (blk cr : Bool) (σ0 s : State Unit) (hB : A10.BS σ0) (hSf : Suff σ0)
    (hK : KP σ0 s) (hb : CtB s) (hS : B8e.RcvS s s.curThread) (hE : SInvQ.EB true s)
    (hN : NQ [s.curThread] s) :
    ∀ y ∈ (handleRecv (Z := Unit) blk cr s).1, A10.SS4 y.2 := by
  have ect : s.curThread = σ0.curThread := kp_curThread hK
  have h0 : B0 σ0 := b0_of_bs hB
  have hS0 : B8e.RcvS s σ0.curThread := ect ▸ hS
  have hni : s.curThread ≠ s.idleThread := by
    have e := hK.1
    simp only [cfS, Prod.mk.injEq] at e
    obtain ⟨-, -, e3, e4, -, -⟩ := e
    rw [e3, e4]; exact hB.ni
  have hOS : OS s := (ss4_of_kp hB hSf hK (ctR_rt hS.2.2.2.2.2.2.2)).1
  have hNB : TP (A11b.NB0 s.curThread) s := by
    obtain ⟨-, -, -, -, -, -, ⟨x, hx, hbk⟩, -⟩ := hS
    intro p x' hp ep e r d hx'
    subst ep
    rw [hx] at hp; cases hp
    exact hbk none (by unfold BlkR; exact Or.inr (Or.inr ⟨e, r, d, hx'⟩))
  have hRIP : ∀ cp rc, HK (fun s' => s' = s) A10.SS4 (receiveIpc (Z := Unit) s.curThread cp blk rc) := by
    intro cp rc s' hs' y hy
    rw [hs', ect] at hy
    exact ss4_of_kr hB hSf (kr_receiveIpc σ0 h0 cp blk rc s hK hb hS0 hE.2 hy)
  have hRS : ∀ cp, HK (fun s' => s' = s) A10.SS4 (receiveSignal (Z := Unit) s.curThread cp blk) := by
    intro cp s' hs' y hy
    rw [hs', ect] at hy
    exact ss4_of_ke hB hSf (ke_receiveSignal σ0 cp blk s hK hb hy)
  have hHF : ∀ e, HK (fun s' => s' = s) A10.SS4 (handleFault (Z := Unit) s.curThread e) := by
    intro e s' hs' z hz
    rw [hs'] at hz
    have hE1 := SInvQ.eb_handleFault_p (k := true) s.curThread e s (SInvQ.npq_ct hE) hN
      (List.mem_singleton_self _) hE z hz
    exact A11b.ss4_end hOS (A11b.cp_handleFault _ e s s.curSc s ⟨rfl, A8.CW.refl _ _⟩ z hz)
      (A11b.cfk_handleFault _ e s z hz) (A11b.nr_handleFault _ e s hNB z hz) hE1.2.2 hni
  unfold handleRecv
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  obtain ⟨y2, h2, hy⟩ := hy
  have e2 : y2.2 = s := by
    refine (?_ : IK (fun s' => s' = s) _) s rfl y2 h2
    unfold NonDet.liftM
    exact ik_bind (ik_asUserGet _ _ s) fun _ => ik_pure _
  rw [e2] at hy
  refine hk_catch (I := fun s' => s' = s) (Q0 := A10.SS4) ?_ hHF s rfl y hy
  refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
  split
  · (try dsimp only)
    split
    · (try dsimp only)
      split
      · refine hkr_bind (ik_lookupReply s) (fun rc => ?_)
        exact hkr_liftE (hRIP _ rc)
      · refine hkr_bind (ik_pure _) (fun rc => ?_)
        exact hkr_liftE (hRIP _ rc)
    · exact hkr_throw _
  · (try dsimp only)
    split
    · refine hkr_bind (by repeat' (first | ik_step0 | ik_unfold)) (fun bt => ?_)
      split
      · exact hkr_liftE (hRS _)
      · exact hkr_throw _
    · exact hkr_throw _
  · exact hkr_throw _

/-! ## The receive tail after the send half -/

/-- The part of rd8e's `RcvS ct` that ctq's `EB true` does not give. -/
def RcvR (s : State Unit) : Prop :=
  Rdy s ∧ SInvB.ScInv s ∧ SInvQ.Simple s ∧
    (∃ x, s.kheap s.curThread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧ B8d.RT s s.curThread

theorem rcvS_of_r {s : State Unit} (h : RcvR s) (hE : SInvQ.EB true s) : B8e.RcvS s s.curThread :=
  ⟨h.1, SInvQ.tq_t1 hE.1.1.1.1, h.2.1, h.2.2.1, (hE.2.1.2.1 rfl).1, (hE.2.1.2.1 rfl).2.2, h.2.2.2.1,
    h.2.2.2.2⟩

/-- **The receive tail's start** at an `ok` outcome `t` of the first-phase
invocation (σ0 = the body start): rd11a's frame with ct still bound to cur_sc
and `RcvR` (proved tail: `ss4_handleRecvK`), or — the OPEN part, true in
reachable states — the tail's `CB → SS4` directly (outcomes leaving the frame
or the binding: ct's SC returned by reply_remove (passive server), donated by
send_ipc / send_signal, cur_sc reconfigured; see KENTRY-PLAN rd13a). -/
def RecvA (σ0 : State Unit) (cr : Bool) (t : State Unit) : Prop :=
  (KP σ0 t ∧ CtB t ∧ RcvR t) ∨ ∀ y ∈ (handleRecv (Z := Unit) true cr t).1, SInvQ.CB y.2 → A10.SS4 y.2

/-- `RecvA` at every `ok` first-phase invocation outcome of the given entry
(pinned: the shell's actual run from every `true` front outcome). -/
def RecvTA (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, A12b.srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        RecvA v.2 cr t.2

section P
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13
  Fl4Proofs.P3.SInvQ.P15 Fl4Proofs.P3.SInvQ.P17

theorem evp_uts {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit} :
    IK (EvP C N S I d Nq σe) (updateTimeStamp (Z := Unit)) := by evp_auto

theorem evp_getCapReg {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit}
    (r : Register) : IK (EvP C N S I d Nq σe) (getCapReg (Z := Unit) r) := by evp_auto

/-- **ctq17's `EvP` at a `true` front outcome.** -/
theorem evp_front {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe σ : State Unit}
    (hσ : EvP C N S I d Nq σe σ) {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1) (ht : v.1 = true) :
    EvP C N S I d Nq σe v.2 := by
  obtain ⟨w, hw, hv2⟩ := hv
  rw [SInvB.checkBudgetRestart_true_eq hv2 ht]
  exact evp_uts σ hσ w hw

/-- **rd12a's `RcvB` discharged** from rd8a's `EF` and ctq17's `EvP` at the
event's start. -/
theorem rcvB_of {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe σ : State Unit}
    (hEF : A8.EF σ) (hσ : EvP C N S I d Nq σe σ) : RcvB σ := fun v hv ht =>
  have hE : SInvQ.EB true v.2 := (evp_front hσ hv ht).1.1.1
  ⟨hE, rcvS_of_bs (A10.bs_front hEF hv ht).1 hE⟩

/-- **rd12b's `RecvT` from `RecvTA`.** -/
theorem recvT_of (hnd : numDomains = 1) {rep : Bool} {c : Syscall} {σ : State Unit} {N S : ObjRef}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit}
    (hEF : A8.EF σ) (hσ : EvP σ.curThread N S I d Nq σe σ) (hCN : σ.curThread ≠ N) (hA : RecvTA rep c σ) :
    A12b.RecvT rep c σ := by
  unfold A12b.RecvT
  intro v hv ht r cr hc
  unfold A12b.RecvQ
  intro g hg t ht' hok y hy hCB
  rcases hA v hv ht r cr hc g hg t ht' hok with ⟨hK, hb, hR⟩ | hO
  · obtain ⟨hB, hSf⟩ := A10.bs_front hEF hv ht
    have hg' : EvP σ.curThread N S I d Nq σe g.2 := evp_getCapReg r v.2 (evp_front hσ hv ht) g hg
    have hE1 : SInvQ.EB true t.2 :=
      (eb_fl4HandleInvocationR hnd σ.curThread N S rep false false true true g.1 (fun _ => rfl) hCN g.2
        hg'.1 t ht').2 () hok
    have hct : t.2.curThread = σ.curThread :=
      ct_fl4HandleInvocationR (cq := σ.curThread) rep false false true true g.1 g.2 hg'.1.1.2.1 t ht'
    have hN : NQ [t.2.curThread] t.2 := by
      rw [hct]
      exact (nq_fl4HandleInvocationR σ.curThread rep false false true true g.1 g.2 hg'.2.2.1 t ht').2 rfl
    exact ss4_handleRecvK true cr v.2 t.2 hB hSf hK hb (rcvS_of_r hR hE1) hE1 hN y hy
  · exact hO y hy hCB

end P

/-! ## The tops -/

section Q
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

set_option maxHeartbeats 8000000 in
/-- ctq17's `EvP` and ct ≠ idle at the FaultIP outcome (rd12b's `ebx_fip`
preamble). -/
theorem fip_evp {σ : State Unit} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ) (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      EvP w.2.curThread w.2.idleThread w.2.idleSc I d Nq w.2 w.2 ∧ w.2.curThread ≠ w.2.idleThread := by
  intro w hw
  have hu : uV w.2 = uV σ := SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw
  have hf : (w.2.idleThread, w.2.idleSc, w.2.curThread) = (σ.idleThread, σ.idleSc, σ.curThread) :=
    fld_arch _ σ rfl w hw
  simp only [Prod.mk.injEq] at hf
  obtain ⟨fN, fS, fC⟩ := hf
  have hX' : SInvQ.EX w.2 :=
    ⟨⟨tq_fl4SyscallFaultIP _ σ hX.1.1 w hw, sa_fl4SyscallFaultIP _ σ hX.1.2 w hw⟩,
      ctQ_arch σ hX.2.1 w hw, simple_arch σ hX.2.2.1 w hw, curScT_fip σ hX.2.2.2 w hw⟩
  have hR' : RB w.2 := rb_fl4SyscallFaultIP _ σ hR w hw
  have h4' : T4 w.2 := q4_fl4SyscallFaultIP _ σ h4 w hw
  have hV' : SInvI.ValidIdle w.2 := by
    have h := SInvI.vi_fl4SyscallFaultIP (N := σ.idleThread) (S := σ.idleSc) (T := σ.idleThread) (b := false)
      σ.curThread σ hV w hw
    unfold SInvI.ValidIdle; rw [fN, fS]; exact h
  have hEO' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hEO hu
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    (vfh_fip σ hEO.vfh w hw)
  have hCX' : SInvAll.CtExit w.2 := ctExit_arch σ hCX w hw
  have ha' := act_arch σ ha w hw
  have hIu' : Iu σ.curThread w.2 :=
    (show IK (Iu σ.curThread) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by iu_auto) σ hIu w hw
  have hIL' : IL [σ.curThread] w.2 := il_fl4SyscallFaultIP _ σ hIL w hw
  have hJ' : Js I σ.curThread d Nq σ w.2 :=
    (show IK (Js I σ.curThread d Nq σ) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by js_auto) σ hJ w hw
  rw [← fC] at hIu' hIL' hJ'
  exact ⟨evp_start hX' hR' h4' hV' hEO' hCX' hIu' hIL' (js_rebase hJ'), ne_idle_of_active hV' hCX' ha'⟩

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd13a top): rd12b's
`kcall_rdyOff4r` with rd12a's receive `OsBody` discharged (`hOsR`: from
`rcvB_of`) and `RecvT` narrowed to `RecvTA`. Remaining named hypotheses,
pinned to the given entry's run: `hRdB` (rd8e/f/h, rd8j), `hP` (`InvR`: the
perform arms, rd14b), `hRA` (`RecvTA`: its second disjunct is the open
receive tail for outcomes leaving rd11a's frame or ct's binding), `hRdF`
(rd8e/f, rd8j); the rest carried entry facts. -/
theorem kcall_rdyOff6 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hRA : ∀ c, ev = .syscallEvent c → RecvTA rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have key : ∀ c, ev = .syscallEvent c → A8.EF σ ∧
      EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ ∧ σ.curThread ≠ σ.idleThread := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    exact ⟨hEF (by intro h; cases h), evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ,
      ne_idle_of_active hX10.vi hCX (fun x hx => (ha x hx).resolve_right fun e => by cases e)⟩
  exact A12b.kcall_rdyOff4r hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB hP
    (fun c e => recvT_of hnd (key c e).1 (key c e).2.1 (key c e).2.2 (hRA c e))
    (fun c e hr => osBody_recv rep c hr (key c e).1 (rcvB_of (key c e).1 (key c e).2.1)) hRdF

set_option maxHeartbeats 4000000 in
/-- **The syscall entry** (rd13a top): rd12b's `kentry_rdyOff4r` with rd12a's
receive `OsBody` discharged and `RecvT` narrowed to `RecvTA`; `hW` keeps
rd8e/f/h's `RdBody`, rd12b's `InvR` (rd14b) and `RecvTA` at the FaultIP
outcome. -/
theorem kentry_rdyOff6 (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ A12b.InvR c w.2 ∧ RecvTA rep c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A12b.kentry_rdyOff4r hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    have hF := fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    ⟨(hW w hw).1, (hW w hw).2.1, recvT_of hnd (A8.ef_fip h w hw) hF.1 hF.2 (hW w hw).2.2,
      fun hr => osBody_recv rep c hr (A8.ef_fip h w hw) (rcvB_of (A8.ef_fip h w hw) hF.1)⟩

end Q

end

end Fl4Proofs.P3.SInvR.A13a
