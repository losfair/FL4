/-
P3 (DESIGN.md §9): **the reply step at `J`** (XTopJointPortIn's
`JReplyHyp` proved, `jReplyHyp`): FL4's `vspace::reply1` of the current,
`Restart` thread (the reply registers when called, then `Running`) against
the spec's success tail (`specTail`), from `JAtZ` before to `JAtZ` after.

* `sched.set_thread_state.running_blk` (P1): `set_thread_state Running` of
  a `Restart` thread keeps `BlkOK`, with its footprint (as
  `restart_blk`).
* `JAtZ.regWrJ`: one register write of a thread (the badge, a message
  register, the message info), a register-frame step (`JAtZ.reg_frameF`,
  `QKY`), as `JAtZ.restartPcJ`.
* `JAtZ.runJ`: `set_thread_state Running` of a `Restart` thread, an SC step
  (`JAtZ.sc_frame`, `ScTKw` for the thread, both states IPC-free): `Inv` by
  `Inv.step` (both states runnable, the thread `RelIfBound` already),
  `XTopAt` by `xtop_sc_step`, the call stacks, MCP and yield words by
  `ScAll.of_tr`, the scheduler facts by the frame (only the thread's state
  and, by `stsAct`, possibly the action to `choose_new_thread` change), the
  dead kept (`deadP_sc_stepG`: the thread is not `Inactive`), P1's `BlkOK`
  by `running_blk`.
* `JAtZ.reply1J`, `jReplyHyp`: the three register writes (when called), then
  `runJ`; the spec's tail is deterministic (`specTail_restart`).
-/
import Fl4Proofs.P3.XTopJointPortIn
import Fl4Proofs.P3.XTopJointSuspend
import Fl4Proofs.P3.XTopJointRegFrame
import Fl4Proofs.P3.XTopYield
import Fl4Proofs.P3.XTopJointLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`set_thread_state Running` of a `Restart` thread keeps `BlkOK`**, with
the footprint of `set_thread_state` (as `restart_blk`). -/
theorem sched.set_thread_state.running_blk (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : L.mem s (stA t) = sched.TS_RESTART) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) (by rw [hr]; exact restart_ne.1) (by rw [hr]; exact restart_ne.2)
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr (by rw [hr]; exact not_blocked_restart)) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, f1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩, f1⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **One register write of a thread at `J`** (module docstring), given
`IRel` after (`reg_wr_irel`, `badge_wr_irel`). -/
theorem JAtZ.regWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (v : U64)
    (hX2 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c (L.wr s (regA t (regIdx r)) v)
      (updK σ t.bv (.tcb (setReg x r v.bv)))) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (regA t (regIdx r)) v) a
      (updK σ t.bv (.tcb (setReg x r v.bv))) := by
  have hP0 := J.ip
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  have hil := regIdx_lt r
  set K : U64 := ⟨BitVec.ofNat 64 (256 + 8 * (regIdx r).val)⟩ with hKdef
  have hKv : K.val = 256 + 8 * (regIdx r).val := by
    show (BitVec.ofNat 64 (256 + 8 * (regIdx r).val)).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hra : (regA t (regIdx r)).val = t.val + 256 + 8 * (regIdx r).val := regA_val hta hil
  have hKt : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta (by rw [hKv]; omega)
  have hreq : regA t (regIdx r) = core.num.U64.wrapping_add t K :=
    UScalar.eq_of_val_eq (by rw [hra, hKt, hKv]; omega)
  have hwr : P1.WritesIn st s (L.wr s (regA t (regIdx r)) v) (· = regA t (regIdx r)) :=
    writesIn_wr (a_reg hta r).1
  have hblk := (blk_rf J.blk (hwr.mono fun b hb => Or.inl ⟨t, htH, K, by rw [hKv]; omega,
    by rw [hKv]; omega, by rw [hb, hreq]⟩)).1
  have hfoot : P1.WritesIn st s (L.wr s (regA t (regIdx r)) v) (P1.KW st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) := by
    rw [hreq]
    exact foot_field hTH htH (by rw [hKv]; omega) (by rw [hKv]; omega) (by rw [hKv]; omega)
      ⟨by rw [hKv]; omega, by rw [hKv]; omega⟩
  have hA : QKY σ (updK σ t.bv (.tcb (setReg x r v.bv))) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => ?_⟩
    by_cases hp : p = t.bv
    · subst hp; exact Or.inr (Or.inl ⟨x, setReg x r v.bv, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, hp])
  exact J.reg_frameF hX2 (hwr.mono fun b hb => Or.inl (Or.inl ⟨t, ht, by rw [hb, hra]; omega,
    by rw [hb, hra]; omega⟩)) hA (YK.YKS.updTcb (y := setReg x r v.bv) hk rfl).ykeep
    (J.inv.updSame (y := setReg x r v.bv) hk rfl rfl (Or.inl rfl)) hblk hfoot

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Running` of a `Restart` thread at `J`, the dead set
kept** (XTopJointReply's `JAtZ.runJ`, same proof; the post names the dead
set `D` and adds the slot and debug-word frames). -/
theorem JAtZ.runJD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .restart) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ∧
      SlotsSame Z.th (L.mem s) (L.mem s6) ∧ P1.DbgKeep st (P1.Heap.tcbs H) Cs s s6 ⦄ := by
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
  have hr0 : L.mem s (P1.stA t) = sched.TS_RESTART := by
    apply UScalar.eq_of_val_eq
    rw [P1.stA_eq, ← tStA_eq, hst, hrs]; unfold sched.TS_RESTART; rfl
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) .running (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.running_blk (Es := P1.EH H) s t J.blk htH hr0)) ?_
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
      · subst e; rw [hk] at h1; cases h1; simp [hσ1, updK] at h2; subst h2; rfl
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t.bv
      · subst e; exact J.inv.rd _ x hk (Or.inl (by rw [hrs]; rfl))
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
    J.deadP_sc_stepG hX' hW hK (fun p x' hp hk' h0 y hy => by
        subst hp; rw [hk] at hk'; cases hk'; rw [hrs] at h0; simp [tsCode] at h0)
      hlk hfk hAI.1 hY' (hYK6.dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2)) (J.sc_kern hW hK hfk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv hcur6 hown6 hoff hAI (BlockedScActive.tkw J.bsa hK fun p y n hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk6] at hp; cases hp
      · rw [hkp _ e] at hp; exact ⟨y, hp, ha, fun _ h => h, id⟩) hcr6 hblk hKd (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD,
    J.xtop.slotsSame_of hW (fun b hb => tfoot_oobj hS hb), P1.Foot.dbgKeep J.blk (fun _ h => h) hfoot⟩

/-- **`set_thread_state Running` of a `Restart` thread at `J`** (module
docstring; `runJD` with the dead set hidden). -/
theorem JAtZ.runJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .restart) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D' s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ :=
  WP.spec_mono (J.runJD ht hk hrs) fun _ ⟨Lst', J', _⟩ => ⟨Lst', D, J'⟩

set_option maxHeartbeats 16000000 in
/-- **`reply1` at `J`** (module docstring): every outcome of the spec's
success tail has `JAt`. -/
theorem JAtZ.reply1J (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => ∀ z ∈ (specTail call ct.bv [v.bv] σ).1, JAt (L := L) arI AR s2 a z.2 ⦄ := by
  unfold vspace.reply1
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (J.runJ hct hk hrs) ?_
    rintro s2 ⟨Lst', D', J2⟩ z hz
    rw [specTail_restart hk hrs false v.bv] at hz
    simp only [Bool.false_eq_true, ↓reduceIte] at hz
    rw [Notif.setThreadState_eq .running hk] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J2⟩
  · simp only [↓reduceIte]
    have hin : (do
        let buf ← msg.lookup_ipc_buffer st s true ct
        let s2 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
        let (n, s3) ← msg.set_mr st s2 ct buf 0#u64 v
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
        msg.set_msg_info st s3 ct mi) ⦃ s3 => ∃ w : U64,
          s3 = L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
            (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
          w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true ct L.total) ?_
      rintro buf -
      refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
      rintro s1 rfl
      have hset : ∀ s1 : S, msg.set_mr st s1 ct buf 0#u64 v ⦃ r =>
          r = (1#u64, L.wr s1 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) ⦄ := by
        intro s1
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ v) ?_
        rintro s2 rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (hset _) ?_
      rintro r rfl
      unfold msginfo.MessageInfo.new
      simp only [bind_ok]
      refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 1#u64 (by decide)) ?_
      rintro s3 ⟨w, rfl, hw⟩
      refine ⟨w, ?_, by rw [hw]; exact msg_info_one_bv⟩
      rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
    refine WP.spec_bind hin ?_
    rintro s3 ⟨w, rfl, hw⟩
    -- the badge register
    have hXb := badge_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hk 0#u64
    rw [badgeRegA_eq_regA] at hXb
    obtain ⟨V1, J1⟩ := J.regWrJ hct hk Fl4Spec.badge_register 0#u64 hXb
    set x1 := setReg x Fl4Spec.badge_register (0#u64 : U64).bv with hx1
    have hk1 : (updK σ ct.bv (.tcb x1)).kheap ct.bv = some (.tcb x1) := by simp [updK]
    -- the message register
    have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hct hk1 (Endp.mrIdx 0) (by decide) v
    obtain ⟨V2, J2⟩ := J1.regWrJ hct hk1 (Endp.mrIdx 0) v hX2
    set x2 := setReg x1 (Endp.mrIdx 0) v.bv with hx2
    have hk2 : (updK (updK σ ct.bv (.tcb x1)) ct.bv (.tcb x2)).kheap ct.bv = some (.tcb x2) := by simp [updK]
    -- the message info
    have hX3 := reg_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hct hk2 Fl4Spec.msg_info_register (by decide) w
    obtain ⟨V3, J3⟩ := J2.regWrJ hct hk2 Fl4Spec.msg_info_register w hX3
    have hxC : setReg x2 Fl4Spec.msg_info_register w.bv = Endp.replyTcb x v.bv := by
      rw [hw]; rfl
    rw [updK_updK, updK_updK, hxC] at J3
    have hkC : (updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv = some (.tcb (Endp.replyTcb x v.bv)) := by
      simp [updK]
    -- `Running`
    refine WP.spec_mono (J3.runJ hct hkC hrs) ?_
    rintro s4 ⟨Lst', D', J4⟩ z hz
    rw [specTail_restart hk hrs true v.bv] at hz
    simp only [↓reduceIte] at hz
    rw [Notif.setThreadState_eq .running hkC] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J4⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JReplyHyp` proved** (`JAtZ.reply1J`). -/
theorem jReplyHyp {AR : A → Fl4Spec.Cr3 → Prop} (th : TypedHeap) : JReplyHyp (L := L) arI AR th := by
  intro Z H Cs Ac Lst D s a σ hth J ct x call v hcur hk hrs s2 z h hz _
  have hct : ct ∈ Z.T := J.thT ct (J.xtop.curTcb hcur).1
  have hp := J.reply1J hct hk hrs call v
  rw [h, WP.spec_ok] at hp
  exact hp z hz

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **An IO port cap, `JAt` after, every label**, with no reply premise
(XTopJointPortIn's `decode_invocation_ioportJ_steps` with `jReplyHyp`, the
primitive steps' closure `jStepHyps`). -/
theorem decode_invocation_ioportJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (first last : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .IoPort first last 0#u64) (call : Bool)
    (hval : call = true → PortInVal arI)
    (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct :=
  decode_invocation_ioportJ_steps arI s ar σ J hni hARI hT (jStepHyps arI) (jReplyHyp arI Z.th) hZB lbl slbl hlbl length buf ct hct
    args hlen hargs sl hAs first last hsc call hval blk don fp extra ci excaps buffer

end

end

end Fl4Proofs.P3
