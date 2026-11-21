/-
P3 (DESIGN.md §9), IPC: **`set_thread_state Running` of an `Inactive`
thread at `J`** (toward `JReplyRestHyp`: the receiver of a reply is
`Inactive` after `reply_remove`, and the transfer sets it `Running`).

* `sched.set_thread_state.running_blkI` (P1): `set_thread_state Running` of
  an `Inactive` thread keeps `BlkOK`, with its footprint (as `running_blk`:
  an `Inactive` thread is not blocked and no reply names it, `XInv.noref`).
* `JAtZ.runIJ`: as `JAtZ.runJ` (XTopJointReply), an SC step at the thread
  (`ScTKw`, both states IPC-free). The differences: `Inv.rd` for the thread
  now `Running` (it was not `inClass` before) is the premise `hrel`
  (`RelIfBound`: an active SC bound to it and off the release queue is
  released; e.g. no SC at all, `relIfBound_noSc`); the dead stay dead
  (`deadP_sc_stepQ`) given the thread is not among them (`htD`; for the
  reply's receiver: it was blocked on the reply, `JAtZ.notDead`, and
  `reply_remove` keeps the dead set).
-/
import Fl4Proofs.P3.XTopJointReply
import Fl4Proofs.P3.ScDeadStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`set_thread_state Running` of an `Inactive` thread keeps `BlkOK`**,
with the footprint of `set_thread_state` (as `running_blk`). -/
theorem sched.set_thread_state.running_blkI (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : L.mem s (stA t) = sched.TS_INACTIVE) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) (by rw [hr]; exact inactive_ne.1) (by rw [hr]; exact inactive_ne.2)
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr (by rw [hr]; exact not_blocked_inactive)) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, f1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩, f1⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- `RelIfBound` of a thread without an SC. -/
theorem relIfBound_noSc {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hn : x.tcbSchedContext = none) : RelIfBound σ t := by
  intro x' scp y n hk' hs
  rw [hk] at hk'; cases hk'; rw [hn] at hs; cases hs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Running` of an `Inactive` thread at `J`** (module
docstring). -/
theorem JAtZ.runIJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (hrel : RelIfBound σ t.bv) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ := by
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
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) .running (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.running_blkI (Es := P1.EH H) s t J.blk htH hr0)) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk, hfoot⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  set x6 : Fl4Spec.Tcb := { x with tcbState := .running } with hx6
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
  -- `Inv`
  have hI1 : Inv σ1 := by
    refine J.inv.step (NtfnStep.tcb hk .running x.tcbArch) (fun u x0 y h1 h2 _ hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = t.bv
      · subst e; simp [hσ1, updK] at h2; subst h2; rfl
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t.bv
      · subst e; exact hrel
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
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv .running σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq .running hk
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
    · subst e; rw [hk] at hky; cases hky
      exact schedulable_of hk6 hsc rfl hkz6 hac hnr6
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
          have hnb6 : NotIpcBlk Fl4Spec.ThreadState.running := by
            refine ⟨?_, ?_, ?_⟩
            · intro _ e; cases e
            · intro _ _ e; cases e
            · intro _ _ _ e; cases e
          exact ⟨x6, by rw [e_ct, hct]; exact hk6, by rw [e_csc]; exact hcs, hnb6⟩
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
      · rw [hct, hk6] at hy; cases hy; rfl
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

end

end

end Fl4Proofs.P3
