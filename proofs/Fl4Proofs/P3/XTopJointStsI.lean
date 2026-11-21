/-
P3 (DESIGN.md §9), IPC: **`set_thread_state` of an `Inactive` thread to
`Inactive`, `Running` or `Restart` at `J`** (`JAtZ.stsIJ`; toward the fault
reply of `JReplyRestHyp`: after `reply_remove` the receiver is `Inactive`,
and the fault reply sets it `Restart` or `Inactive`).

* `sched.set_thread_state.inactive_blkI`, `sched.set_thread_state.restart_blkI`
  (P1): `set_thread_state Inactive` / `Restart` of an `Inactive` thread keeps
  `BlkOK`, with its footprint (`sts_all`; an `Inactive` thread is in no queue,
  `hq_of_not_runnable`, and no reply names it, `XInv.noref`).
* `JAtZ.stsIJ`: XTopJointRunI's `JAtZ.runIJ` for any target state of code
  below 3 (`tsCode ts < 3`: `Inactive`, `Running`, `Restart`), P1's `BlkOK`
  step given (`hB`); `Inv.rd` for the thread in its new state is the premise
  `hrel` (only when the new state is `inClass`: `Running`, `Restart`).
* `JAtZ.rstPostJ`: XTopJointRunPost's `JAtZ.runPostJ` with `Restart` for
  `Running` (both runnable: `postpone` then puts the thread in the release
  queue).
-/
import Fl4Proofs.P3.XTopJointRunPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`set_thread_state Inactive` of an `Inactive` thread keeps `BlkOK`**,
with the footprint of `set_thread_state`. -/
theorem sched.set_thread_state.inactive_blkI (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : L.mem s (stA t) = sched.TS_INACTIVE) :
    sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) (by rw [hr]; exact inactive_ne.1) (by rw [hr]; exact inactive_ne.2)
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_inactive inactive_ne
    (Or.inr (by rw [hr]; exact not_blocked_inactive)) hnoref
    (hq_of_not_runnable h0 ht (by rw [hr]; exact not_runnable_inactive)))
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, f1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩, f1⟩

/-- **`set_thread_state Restart` of an `Inactive` thread keeps `BlkOK`**,
with the footprint (`restart_blk`). -/
theorem sched.set_thread_state.restart_blkI (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : L.mem s (stA t) = sched.TS_INACTIVE) :
    sched.set_thread_state st s t sched.TS_RESTART ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_thread_state.restart_blk (Es := Es) s t h ht (by rw [hr]; exact not_blocked_inactive)
    (by rw [hr]; exact inactive_ne.1)) fun _ h => ⟨h.1, h.2.1⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- A state of code below 3 (`Inactive`, `Running`, `Restart`) is IPC-free. -/
theorem tsLow_free {ts : Fl4Spec.ThreadState} (h : tsCode ts < 3) : IpcFree ts := by
  cases ts <;> simp [tsCode] at h <;> exact ⟨rfl, rfl, fun _ e => nomatch e⟩

/-- A state of code below 3 is blocked on no endpoint and no notification. -/
theorem tsLow_nb {ts : Fl4Spec.ThreadState} (h : tsCode ts < 3) : NotIpcBlk ts := by
  unfold NotIpcBlk
  cases ts <;> simp [tsCode] at h <;> exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), fun _ _ _ e => nomatch e⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state` of an `Inactive` thread at `J`** (module
docstring). -/
theorem JAtZ.stsIJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (v : U64) (hv : v.val = tsCode ts)
    (hrel : inClass ts → RelIfBound σ t.bv)
    (hB : sched.set_thread_state st s t v ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄) :
    sched.set_thread_state st s t v ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) ts hts v hv)
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _)) hB) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk, hfoot⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  set x6 : Fl4Spec.Tcb := { x with tcbState := ts } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ p, p ≠ t.bv → σ6.kheap p = σ.kheap p := by
    intro p hp; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hp]
  have hact6 : σ6.schedulerAction = .chooseNewThread ∨ σ6.schedulerAction = σ.schedulerAction :=
    stsAct_action σ1 t.bv
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_csc : σ6.curSc = σ.curSc := by rw [hrec]; rfl
  have e_cons : σ6.consumedTime = σ.consumedTime := by rw [hrec]; rfl
  have e_tm : σ6.curTime = σ.curTime := by rw [hrec]; rfl
  have e_idle : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have e_rel : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := by
    rw [hrs]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have hK : ScTKw (fun p => p = t.bv) σ σ6 := by
    refine ⟨fun p => ?_, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
      by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_ct, e_isc⟩
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show TKObj _ _ _
      exact Or.inr (Or.inl ⟨x, x6, rfl, rfl, rfl, Or.inr ⟨rfl, hfx, tsLow_free hts⟩⟩)
    · rw [hkp p hp]; exact OTK.refl _ _
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  -- `Inv`
  have hI1 : Inv σ1 := by
    refine J.inv.step (NtfnStep.tcb hk ts x.tcbArch) (fun u x0 y h1 h2 _ hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = t.bv
      · subst e; rw [hk] at h1; cases h1; rw [hrs] at hr; cases hr
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t.bv
      · subst e; simp [hσ1, updK] at h2; subst h2; exact hrel hc.cls
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        exact J.inv.rd u y h2' hc
  have hInv : Inv σ6 := hI1.qchange (qchange_stsAct σ1 t.bv)
  -- the yield words
  have hY6 : YieldRel Z.T Z.C (L.mem s6) σ6 := by
    have h1 := J.yld.frame (m' := L.mem s6) (σ' := σ1)
      (fun y hy => hy6.mem_eq (yieldA_aligned hT hy) fun h => h ⟨y, hy, rfl⟩)
      (YK.YKS.updTcb (y := x6) hk rfl).ykeep
    exact h1.frame (m' := L.mem s6) (σ' := σ6) (fun _ _ => rfl) (YKeep.of_kheap (stsAct_kheap _ _))
  have hYK6 : YKeep σ σ6 := (YK.YKS.updTcb (y := x6) hk rfl).ykeep.trans (YKeep.of_kheap (stsAct_kheap _ _))
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv ts σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq ts hk
  have hsok : SOK (false, true) σ σ6 := Pres.of_eq (pres_setThreadState _ _ _) hsp
  have hNSC : NSC Z.N Z.C σ6 := by
    intro n hn y p hy hp
    by_cases e : n.bv = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.nsc n hn y p hy hp
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hX6.2.2.1, hX6.1.toN, hNSC, hInv⟩ hY6 (hW.mono fun _ h => Or.inl h)
      hsok rfl
  -- the scheduler facts
  have hsched : ∀ u, Fl4Spec.schedulable u σ = true → Fl4Spec.schedulable u σ6 = true := by
    intro u hs
    obtain ⟨y, scp, z, n, hky, hsc, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
    have hzt : scp ≠ t.bv := by rintro rfl; rw [hk] at hkz; cases hkz
    have hkz6 : σ6.kheap scp = some (.schedContext z n) := by rw [hkp _ hzt]; exact hkz
    have hnr6 : u ∉ σ6.releaseQueue := by rw [e_rel]; exact hnr
    by_cases e : u = t.bv
    · subst e; rw [hk] at hky; cases hky; rw [hrs] at hrun; cases hrun
    · exact schedulable_of (by rw [hkp _ e]; exact hky) hsc hrun hkz6 hac hnr6
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hAI : ActIdle σ6 := by
    refine ⟨fun u hu => ?_, ?_⟩
    · have hu0 : σ.schedulerAction = .switchThread u := by
        rcases hact6 with e | e
        · rw [e] at hu; cases hu
        · rw [← e]; exact hu
      exact hsched u (J.act.1 u hu0)
    · obtain ⟨y, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨y, by rw [e_idle, hkp _ hidt]; exact h1, by rw [e_isc]; exact h2, h3, by rw [e_idle, e_rel]; exact h4⟩
  have hoff : OffOK σ6 := by
    intro h0 y n hy ha
    rw [e_cons] at h0 ⊢; rw [e_tm]; rw [e_csc] at hy; rw [e_csc, e_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.off h0 y n hy ha
  have hcur6 : σ6.schedulerAction = .chooseNewThread ∨ CurInv σ6 := by
    rcases J.cur with e | hC
    · left
      rcases hact6 with e' | e'
      · exact e'
      · rw [e', e]
    · right
      obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
      obtain ⟨y1, n1, hk1'⟩ := hC.sc
      have hne : σ.curSc ≠ t.bv := by intro e; rw [e, hk] at hk1'; cases hk1'
      refine ⟨?_, ⟨y1, n1, by rw [e_csc, hkp _ hne]; exact hk1'⟩, fun hne' y n hy => ?_,
        fun hm => hC.notRel (by rw [e_ct, e_rel] at hm; exact hm)⟩
      · by_cases hct : σ.curThread = t.bv
        · rw [hct, hk] at hkc; cases hkc
          exact ⟨x6, by rw [e_ct, hct]; exact hk6, by rw [e_csc]; exact hcs, tsLow_nb hts⟩
        · exact ⟨xt, by rw [e_ct, hkp _ hct]; exact hkc, by rw [e_csc]; exact hcs, hnb⟩
      · rw [e_csc, e_isc] at hne'; rw [e_csc] at hy
        rw [hkp _ hne] at hy
        exact hC.active hne' y n hy
  have hown6 : CurOwnW Z.T Z.C σ6 := by
    have hsc6 : ∀ y n, σ6.kheap σ6.curSc = some (.schedContext y n) → σ.kheap σ.curSc = some (.schedContext y n) := by
      intro y n hy
      rw [e_csc] at hy
      by_cases e : σ.curSc = t.bv
      · rw [e, hk6] at hy; cases hy
      · rw [hkp _ e] at hy; exact hy
    rcases J.own with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · left
      by_cases hut : u.bv = t.bv
      · rw [hut, hk] at hkt; cases hkt
        exact ⟨u, hu, x6, by rw [hut]; exact hk6, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
      · exact ⟨u, hu, xt, by rw [hkp _ hut]; exact hkt, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
    · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y n hy => hun y n (hsc6 y n hy)⟩
  have hcr6 : CurRunM σ6 := by
    by_cases hnr : σ6.schedulerAction ≠ .resumeCurThread
    · exact Or.inl hnr
    have hr' : σ6.schedulerAction = .resumeCurThread := not_not.1 hnr
    have ha : σ6.schedulerAction = σ.schedulerAction := hact6.resolve_left (by rw [hr']; intro e; cases e)
    have h0 : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
    right
    rcases J.curRun.resolve_left h0 with h | h
    · left
      intro y hy
      rw [e_ct] at hy
      by_cases hct : σ.curThread = t.bv
      · have h' := h x (by rw [hct]; exact hk)
        rw [hrs] at h'; cases h'
      · rw [hkp _ hct] at hy; exact h y hy
    · right; rw [e_ct, e_idle]; exact h
  have hlk : LK (fun _ => False) σ σ6 := fun p => Or.inr (by
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show LObj _ _
      refine ⟨?_, ?_, ?_⟩
      · intro y ey; cases ey; exact ⟨_, rfl, Or.inl rfl⟩
      · intro y n ey; cases ey
      · intro y ey; cases ey
    · rw [hkp p hp]; exact OL.refl _)
  have hfk : FK σ σ6 := ⟨e_csc, e_idle, e_isc⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s6 q := fun q hq =>
    J.deadP_sc_stepQ hX' hW hK (fun _ hp => absurd (show q = t from P1.eq_of_bv hp) (fun e => htD (e ▸ hq)))
      hlk hfk hAI.1 hY' (hYK6.dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2)) (J.sc_kern hW hK hfk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv hcur6 hown6 hoff hAI (BlockedScActive.tkw J.bsa hK fun p y n hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk6] at hp; cases hp
      · rw [hkp _ e] at hp; exact ⟨y, hp, ha, fun _ h => h, id⟩) hcr6 hblk hKd (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD⟩


set_option maxHeartbeats 32000000 in
/-- **`Restart`, then `postpone`, at `J`** (as `JAtZ.runPostJ`). -/
theorem JAtZ.rstPostJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    (hnrel : ¬ (Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true)) :
    sched.set_thread_state st s t sched.TS_RESTART ⦃ s6 =>
      XTopAt (L := L) AR Z s6 a (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv) ∧
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv) ∧
      sched.postpone st s6 sc ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) sc.bv
          (stsAct (updK σ t.bv (.tcb { x with tcbState := .restart })) t.bv) = ({((), σ7)}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s7 a σ7 ⦄ ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hr0 : L.mem s (P1.stA t) = sched.TS_INACTIVE := by
    apply UScalar.eq_of_val_eq
    rw [P1.stA_eq, ← tStA_eq, hst, hrs]; unfold sched.TS_INACTIVE; rfl
  -- the thread is in no queue
  have hnq : NotQueued σ t.bv := by
    refine ⟨fun d p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rq d p t.bv hm
      rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rel t.bv hm
      rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hts : t.bv ≠ sc.bv := fun e => by rw [e, hky] at hk; cases hk
  obtain ⟨y0, n0, hky0, hyt⟩ := J.inv.back t.bv x sc.bv hk hxsc
  rw [hky] at hky0; cases hky0
  -- the action is no switch to the thread (it is not schedulable)
  have hnsw : σ.schedulerAction ≠ .switchThread t.bv := fun e => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := schedulable_inv (J.act.1 _ e)
    rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) .restart (by decide) sched.TS_RESTART (by unfold sched.TS_RESTART; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.restart_blkI (Es := P1.EH H) s t J.blk htH hr0)) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk6, hfoot6⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  set x6 : Fl4Spec.Tcb := { x with tcbState := .restart } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ p, p ≠ t.bv → σ6.kheap p = σ.kheap p := by
    intro p hp; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hp]
  have hact6 : σ6.schedulerAction = .chooseNewThread ∨ σ6.schedulerAction = σ.schedulerAction :=
    stsAct_action σ1 t.bv
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_csc : σ6.curSc = σ.curSc := by rw [hrec]; rfl
  have e_cons : σ6.consumedTime = σ.consumedTime := by rw [hrec]; rfl
  have e_tm : σ6.curTime = σ.curTime := by rw [hrec]; rfl
  have e_idle : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have e_rel : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := by
    rw [hrs]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have hK : ScTKw (fun p => p = t.bv) σ σ6 := by
    refine ⟨fun p => ?_, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
      by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_ct, e_isc⟩
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk6]
      show TKObj _ _ _
      exact Or.inr (Or.inl ⟨x, x6, rfl, rfl, rfl, Or.inr ⟨rfl, hfx, rfl, rfl, fun _ e => by cases e⟩⟩)
    · rw [hkp p hp]; exact OTK.refl _ _
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  have hks6 : L.ksb s6 = L.ksb s := hW.1
  have hbuf6 : BufWordRel Z.T (L.mem s6) σ6 := J.sc_buf hW hK
  have hI6 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6 σ6 := by
    have h := hX'.irelK (by rw [hks6]; exact J.ks) hbuf6
    have e : σ6.archState = σ.archState := hK.arch
    rw [e] at h; exact h
  refine ⟨hX', hI6, ?_⟩
  -- the spec's `Restart`
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv .restart σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq .restart hk
  have hIB6 : InvBut σ6 t.bv ∧ NotQueued σ6 t.bv := (J.inv.toBut t.bv).ik hnq ((ikm_setThreadState .restart).of_eq hsp)
  -- the yield words
  have hY6 : YieldRel Z.T Z.C (L.mem s6) σ6 := by
    have h1 := J.yld.frame (m' := L.mem s6) (σ' := σ1)
      (fun y hy => hy6.mem_eq (yieldA_aligned hT hy) fun h => h ⟨y, hy, rfl⟩)
      (YK.YKS.updTcb (y := x6) hk rfl).ykeep
    exact h1.frame (m' := L.mem s6) (σ' := σ6) (fun _ _ => rfl) (YKeep.of_kheap (stsAct_kheap _ _))
  have hYK6 : YKeep σ σ6 := (YK.YKS.updTcb (y := x6) hk rfl).ykeep.trans (YKeep.of_kheap (stsAct_kheap _ _))
  have hsok6 : SOK (false, true) σ σ6 := Pres.of_eq (pres_setThreadState _ _ _) hsp
  -- the FL4 facts at `s6` for `postpone`
  have hS6 : SchedRel st Z.N Z.T Z.C Z.c s6 σ6 := hX6.2.2.1
  have hR6N : NtfnStateRel Z.N Z.T (L.mem s6) σ6 := hX6.1.toN
  obtain ⟨Q6, R6, hc6, hs6⟩ := hS6.lists
  obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs6.tcb t ht
  rw [hk6] at hkt6; cases hkt6
  have hxsc6 : x6.tcbSchedContext = some sc.bv := hxsc
  have h0 : L.mem s6 (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct6.symm.trans hxsc6)).1
  have hst6 : L.mem s6 (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hsct6.symm.trans hxsc6)).2
  have hky6 : σ6.kheap sc.bv = some (.schedContext y n) := by rw [hkp _ (Ne.symm hts)]; exact hky
  obtain ⟨y', n', hky', hy'⟩ := hs6.scs sc hsc
  rw [hky6] at hky'; cases hky'
  have htw : L.mem s6 (scW sc 24#u64) = t := P1.eq_of_bv (Notif.optRef_some (hy'.tcb.symm.trans hyt)).2
  have hnr6 : t.bv ∉ σ6.releaseQueue := hIB6.2.2
  have hr06 : (L.mem s6 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    have hm := (hc6.released t ht).1 hne
    exact hnr6 (by rw [hs6.rel, mem_map_bv]; exact hm)
  have hrw6 : L.mem s6 (tStA t) = sched.TS_RESTART := by
    obtain ⟨x7, hk7, hTR7⟩ := hI6.1.tcb t ht
    rw [hk6] at hk7; cases hk7
    apply UScalar.eq_of_val_eq; rw [hTR7.st]; unfold sched.TS_RESTART; rfl
  have hrun6 : P1.Runnable (L.mem s6 (P1.stA t)) := by
    rw [stA_tStA, hrw6]; exact P1.runnable_restart
  have hns6 : σ6.schedulerAction ≠ .switchThread t.bv := by
    rcases hact6 with e | e <;> rw [e]
    · intro h; cases h
    · exact hnsw
  have hna6 : L.actionW s6 ≠ t := actionW_ne_of hS6 ht hns6
  have hmx : (L.rmax s6 (L.mem s6 (scA t))).val ≠ 0 := by rw [hst6]; exact hy'.rmax_ne hya
  have htw' : L.mem s6 (P1.scTcbA sc) = t := by rw [Sched.scTcbA_eq]; exact htw
  have hRel6 : RelOK σ6 := by
    refine ⟨fun u hu => ?_, hIB6.1.sorted, fun u hu xu p hku hsu => ?_⟩
    · obtain ⟨xu, p, -, -, h1, h2, -⟩ := hIB6.1.rel u hu; exact ⟨xu, p, h1, h2⟩
    · obtain ⟨xu', p', y1, n1, h1, h2, -, h4, h5⟩ := hIB6.1.rel u hu
      rw [hku] at h1; cases h1; rw [hsu] at h2; cases h2; exact ⟨y1, n1, h4, h5⟩
  refine WP.spec_mono (WP.spec_and (postpone_refines s6 σ6 hS6 hRel6 hsc ht htw h0 hr06 hmx)
    (P1.sched.postpone.blk (Es := P1.EH H) s6 sc hblk6 (by rw [htw']; exact htH) (by rw [htw', hst6])
      (J.c0 sc hsc) (by rw [htw']; exact hr06) (by rw [htw']; exact hrun6)
      (by rw [htw']; exact hna6) (fun e => hmx (by rw [hst6, e]; rfl)))) ?_
  rintro s7 ⟨⟨σ7, he, hke, hae, hte, hrq7, hfe, hw7, hS7⟩, hblk, hfoot7⟩
  refine ⟨σ7, he, ?_⟩
  have mem7 : ((), σ7) ∈ (Fl4Spec.postpone (Z := Unit) sc.bv σ6).1 := by rw [he]; exact Set.mem_singleton _
  -- the spec state after `postpone`
  have hne6 : ∀ p y1 n1, σ6.kheap p = some (.schedContext y1 n1) → Fl4Spec.scActive y1 = true →
      y1.scRefills ≠ [] := hIB6.1.ne
  obtain ⟨b, hpe⟩ := postpone_eq hky6 hyt hk6 (specRt σ6) (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨x6, sc.bv, y, n, hk6, hxsc6, hky6, hne6 _ _ _ hky6 hya, specRt_eq hk6 hxsc6 hky6 (hne6 _ _ _ hky6 hya)⟩
    · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := hIB6.1.rel u hu
      exact ⟨xu, scp, yu, nu, h1, h2, h4, hne6 _ _ _ h4 h5, specRt_eq h1 h2 h4 (hne6 _ _ _ h4 h5)⟩)
  have hσ7 := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (he.symm.trans hpe)))
  simp only at hσ7
  have hI7 : Inv σ7 := by
    rw [hσ7]; exact hIB6.1.postponed hk6 hxsc6 rfl hky6 hya b
  have e7_ct : σ7.curThread = σ.curThread := by rw [hσ7]; exact e_ct
  have e7_csc : σ7.curSc = σ.curSc := by rw [hσ7]; exact e_csc
  have e7_cons : σ7.consumedTime = σ.consumedTime := by rw [hσ7]; exact e_cons
  have e7_tm : σ7.curTime = σ.curTime := hte.trans e_tm
  have e7_idle : σ7.idleThread = σ.idleThread := by rw [hσ7]; exact e_idle
  have e7_isc : σ7.idleSc = σ.idleSc := by rw [hσ7]; exact e_isc
  have hk7 : σ7.kheap t.bv = some (.tcb x6) := by rw [hke]; exact hk6
  have hkp7 : ∀ p, p ≠ t.bv → σ7.kheap p = σ.kheap p := fun p hp => by rw [hke]; exact hkp p hp
  have hrel7 : ∀ u, u ∈ σ7.releaseQueue ↔ u = t.bv ∨ u ∈ σ.releaseQueue := fun u => by
    rw [hrq7 u, e_rel]
  have hact7 : σ7.schedulerAction = .chooseNewThread ∨ σ7.schedulerAction = σ.schedulerAction := by
    rw [hae]; exact hact6
  -- the frame
  have hW7 : P1.WritesIn st s s7 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot hW hw7
  have hK7 : ScTKw (fun p => p = t.bv) σ σ7 := hK.trans (nkt_postpone _ σ6 _ mem7).ofFalse
  have hR7 : NtfnStateRel Z.N Z.T (L.mem s7) σ7 := hR6N.frame hS6.placed hfe (KView.of_kheap hke)
  have hX7 : XTopAt (L := L) AR Z s7 a σ7 := xtop_sc_step J.xtop hP0 J.nk hW7 hK7 hS7 hR7 id
  have hNSC : NSC Z.N Z.C σ7 := by
    intro m hm y1 p hy hp
    by_cases e : m.bv = t.bv
    · rw [e, hk7] at hy; cases hy
    · rw [hkp7 _ e] at hy; exact J.nsc m hm y1 p hy hp
  have hw7K : P1.WritesIn st s6 s7 (KFoot st Z.T Z.N Z.C Z.c s6 σ6) := WritesIn.kfoot_of_sfoot hw7
  have hY7 : YieldRel Z.T Z.C (L.mem s7) σ7 :=
    hY6.frame (fun y1 hy1 => hw7K.mem_eq (yieldA_aligned hT hy1) fun hb => hb.ne_yield hS6 hy1 rfl)
      (YKeep.of_kheap hke)
  have hsok7 : SOK (false, true) σ σ7 := hsok6.trans (pres_postpone (f := (false, true)) _ σ6 _ mem7)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS7, hR7, hNSC, hI7⟩ hY7 (hW7.mono fun _ h => Or.inl h)
      hsok7 rfl
  -- the scheduler facts
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y1, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  have hsched : ∀ u, u ≠ t.bv → Fl4Spec.schedulable u σ = true → Fl4Spec.schedulable u σ7 = true := by
    intro u hut hs
    obtain ⟨y1, scp, z, n1, hky1, hsc1, hrun, hkz, hac, hnr⟩ := schedulable_inv hs
    have hzt : scp ≠ t.bv := by rintro rfl; rw [hk] at hkz; cases hkz
    have hkz7 : σ7.kheap scp = some (.schedContext z n1) := by rw [hkp7 _ hzt]; exact hkz
    have hnr7 : u ∉ σ7.releaseQueue := fun hm => (hrel7 u).1 hm |>.elim hut hnr
    exact schedulable_of (by rw [hkp7 _ hut]; exact hky1) hsc1 hrun hkz7 hac hnr7
  have hAI : ActIdle σ7 := by
    refine ⟨fun u hu => ?_, ?_⟩
    · have hu0 : σ.schedulerAction = .switchThread u := by
        rcases hact7 with e | e
        · rw [e] at hu; cases hu
        · rw [← e]; exact hu
      have hut : u ≠ t.bv := fun e => hnsw (e ▸ hu0)
      exact hsched u hut (J.act.1 u hu0)
    · obtain ⟨y1, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨y1, by rw [e7_idle, hkp7 _ hidt]; exact h1, by rw [e7_isc]; exact h2, h3, by
        rw [e7_idle]; intro hm; rcases (hrel7 _).1 hm with e | e; exact hidt e; exact h4 e⟩
  have hoff : OffOK σ7 := by
    intro h0' y1 n1 hy ha
    rw [e7_cons] at h0' ⊢; rw [e7_tm]; rw [e7_csc] at hy; rw [e7_csc, e7_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk7] at hy; cases hy
    · rw [hkp7 _ e] at hy; exact J.off h0' y1 n1 hy ha
  have hcur7 : σ7.schedulerAction = .chooseNewThread ∨ CurInv σ7 := by
    rcases J.cur with e | hC
    · left
      rcases hact7 with e' | e'
      · exact e'
      · rw [e', e]
    · right
      obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
      obtain ⟨y1, n1, hk1'⟩ := hC.sc
      have hne : σ.curSc ≠ t.bv := by intro e; rw [e, hk] at hk1'; cases hk1'
      refine ⟨?_, ⟨y1, n1, by rw [e7_csc, hkp7 _ hne]; exact hk1'⟩, fun hne' y2 n2 hy => ?_,
        fun hm => ?_⟩
      · exact ⟨xt, by rw [e7_ct, hkp7 _ (Ne.symm htc)]; exact hkc, by rw [e7_csc]; exact hcs, hnb⟩
      · rw [e7_csc, e7_isc] at hne'; rw [e7_csc] at hy
        rw [hkp7 _ hne] at hy
        exact hC.active hne' y2 n2 hy
      · rw [e7_ct] at hm
        rcases (hrel7 _).1 hm with e | e
        · exact htc e.symm
        · exact hC.notRel e
  have hown7 : CurOwnW Z.T Z.C σ7 := by
    have hsc7 : ∀ y1 n1, σ7.kheap σ7.curSc = some (.schedContext y1 n1) →
        σ.kheap σ.curSc = some (.schedContext y1 n1) := by
      intro y1 n1 hy
      rw [e7_csc] at hy
      by_cases e : σ.curSc = t.bv
      · rw [e, hk7] at hy; cases hy
      · rw [hkp7 _ e] at hy; exact hy
    rcases J.own with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · left
      have hnr' : 0 < σ7.consumedTime → u.bv ∉ σ7.releaseQueue := by
        intro h0' hm
        rw [e7_cons] at h0'
        rcases (hrel7 _).1 hm with e | e
        · -- the postponed thread owns the current SC: `OffOK` makes its SC released
          rw [e, hk] at hkt; cases hkt
          have ecs : σ.curSc = sc.bv := Option.some.inj (hxs.symm.trans hxsc)
          obtain ⟨h1, -, h3⟩ := J.off h0' y n (by rw [ecs]; exact hky) (fun _ => hya)
          exact hnrel ⟨h3, restart_suff0 h1⟩
        · exact hnr h0' e
      by_cases hut : u.bv = t.bv
      · rw [hut, hk] at hkt; cases hkt
        exact ⟨u, hu, x6, by rw [hut]; exact hk7, by rw [e7_csc]; exact hxs,
          fun y1 n1 hy => hown y1 n1 (hsc7 y1 n1 hy), hnr'⟩
      · exact ⟨u, hu, xt, by rw [hkp7 _ hut]; exact hkt, by rw [e7_csc]; exact hxs,
          fun y1 n1 hy => hown y1 n1 (hsc7 y1 n1 hy), hnr'⟩
    · exact Or.inr ⟨by rw [e7_csc]; exact hcs, fun y1 n1 hy => hun y1 n1 (hsc7 y1 n1 hy)⟩
  have hcr7 : CurRunM σ7 := by
    by_cases hnr : σ7.schedulerAction ≠ .resumeCurThread
    · exact Or.inl hnr
    have hr' : σ7.schedulerAction = .resumeCurThread := not_not.1 hnr
    have ha : σ7.schedulerAction = σ.schedulerAction := hact7.resolve_left (by rw [hr']; intro e; cases e)
    have h0' : ¬ σ.schedulerAction ≠ .resumeCurThread := fun e => e (by rw [← ha]; exact hr')
    right
    rcases J.curRun.resolve_left h0' with h | h
    · left
      intro y1 hy
      rw [e7_ct] at hy
      rw [hkp7 _ (Ne.symm htc)] at hy; exact h y1 hy
    · right; rw [e7_ct, e7_idle]; exact h
  have hlk : LK (fun _ => False) σ σ7 := fun p => Or.inr (by
    by_cases hp : p = t.bv
    · subst hp; rw [hk, hk7]
      show LObj _ _
      refine ⟨?_, ?_, ?_⟩
      · intro y1 ey; cases ey; exact ⟨_, rfl, Or.inl rfl⟩
      · intro y1 n1 ey; cases ey
      · intro y1 ey; cases ey
    · rw [hkp7 p hp]; exact OL.refl _)
  have hfk : FK σ σ7 := ⟨e7_csc, e7_idle, e7_isc⟩
  have hDbg := J.kw_dbg (P1.Foot.trans hfoot6 hfoot7)
  have hKd := J.kw_dbgKeep (P1.Foot.trans hfoot6 hfoot7)
  have hdead : ∀ q ∈ D, DeadP (L := L) H s7 q := fun q hq =>
    J.deadP_sc_stepQ hX7 hW7 hK7 (fun _ hp => absurd (show q = t from P1.eq_of_bv hp) (fun e => htD (e ▸ hq)))
      hlk hfk hAI.1 hY' ((hYK6.trans (YKeep.of_kheap hke)).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW7 hK7 hX7 hCR' hRF' hY' hM' (J.sc_buf hW7 hK7) hRP' (J.sc_apart hW7 hK7)
    (J.sc_jpl hW7 hK7 (J.idleW_keep hX7.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW7 hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX7.fin.1.1.1 hfk.2.1 hfk.2.2))
    (J.sc_kern hW7 hK7 hfk hX7 hDbg fun _ h => h)
    (J.sc_utc hW7 hK7 hDbg) hNSC hI7 hcur7 hown7 hoff hAI (BlockedScActive.tkw J.bsa hK7 fun p y1 n1 hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk7] at hp; cases hp
      · rw [hkp7 _ e] at hp; exact ⟨y1, hp, ha, fun _ h => h, id⟩) hcr7 hblk hKd (J.idleW_keep hX7.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD⟩

end

end

end Fl4Proofs.P3
