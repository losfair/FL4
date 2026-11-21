/-
P3 (DESIGN.md §9), VSpace: **the frame labels that reply in the decode, at
`J`** (`GetAddress`, `TestAndClearAccessed`; XTopJointVsCap's `JFramePath.post`
narrowed to `DeriveSubframe`).

* `sched.set_thread_state.running_blkR` (P1), `JAtZ.runRJ`: XTopJointReply's
  `running_blk` / `JAtZ.runJ` for any runnable thread
  (`TestAndClearAccessed` replies without the caller's restart, so the
  caller may still be `Running`).
* `JAtZ.reply1RJ`: XTopJointReply's `JAtZ.reply1J` for a runnable thread, at
  the spec's state with the reply registers and `Running`.
* `specTail_tac`: the spec's restart, reply and `Running` after an omitted
  FL4 restart end in that state (VsReplyTop's `stsAct_twice`, as
  `tacHypX_topT`).
* `XTopAt.clr5`, `JAtZ.clrJ`: the accessed-bit clear of a page-table word,
  the spec unchanged (VsTopX's `finX_clr5`; `JAtZ.vsStepJ` with the trivial
  spec frame).
* `decode_invocation_frame_gaJ`, `decode_invocation_frame_tacJ`: the labels'
  `DecOKRMX` (VsDecReply's `decode_invocation_frame_getaddrX`/`tacX`) with
  `FinXT` and `JAt` carried: the reply hypotheses from VsReplyTop's
  `getAddrHypX_topT`/`tacHypX_topT` and `JAtZ.restartJ` + `JAtZ.reply1J`
  (GetAddress), `JAtZ.clrJ` + `JAtZ.reply1RJ` (TestAndClearAccessed).
* `decode_invocation_frameJR`: a native frame cap at `JAt`, `JPostHyp` [W]
  only for `DeriveSubframe`.
-/
import Fl4Proofs.P3.XTopJointVsMap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`set_thread_state Running` of a thread neither blocked nor waiting on
a reply or a receive keeps `BlkOK`** (`running_blk` for any runnable state). -/
theorem sched.set_thread_state.running_blkR (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : ¬ Blocked (L.mem s (stA t)) ∧ L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧
      L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨hnb, hne⟩ := hr
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t := hX.noref (h0.tcbs t ht) hne.1 hne.2
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr hnb) hnoref
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

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Running` of a runnable thread at `J`** (XTopJointReply's
`JAtZ.runJ` for `Restart`, `Running` or `RunningVM`). -/
theorem JAtZ.runRJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .restart ∨ x.tcbState = .running ∨ x.tcbState = .runningVM) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 => ∃ (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D' s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) (by rcases hrs with hrs | hrs | hrs <;> exact ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩)
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hr0 : ¬ P1.Blocked (L.mem s (P1.stA t)) ∧ L.mem s (P1.stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧
      L.mem s (P1.stA t) ≠ sched.TS_BLOCKED_ON_RECV := by
    have hv : (L.mem s (P1.stA t)).val = tsCode x.tcbState := by rw [P1.stA_eq, ← tStA_eq, hst]
    have hc : (L.mem s (P1.stA t)).val = 1 ∨ (L.mem s (P1.stA t)).val = 2 ∨ (L.mem s (P1.stA t)).val = 8 := by
      rw [hv]; rcases hrs with h | h | h <;> rw [h] <;> simp [tsCode]
    have e3 : sched.TS_BLOCKED_ON_RECV.val = 3 := by unfold sched.TS_BLOCKED_ON_RECV; rfl
    have e4 : sched.TS_BLOCKED_ON_SEND.val = 4 := by unfold sched.TS_BLOCKED_ON_SEND; rfl
    have e5 : sched.TS_BLOCKED_ON_REPLY.val = 5 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
    have e6 : sched.TS_BLOCKED_ON_NTFN.val = 6 := by unfold sched.TS_BLOCKED_ON_NTFN; rfl
    refine ⟨fun hb => ?_, fun e => ?_, fun e => ?_⟩
    · rcases hb with e | e | e <;> rw [e] at hc <;> simp only [e3, e4, e6] at hc <;> omega
    · rw [e, e5] at hc; omega
    · rw [e, e3] at hc; omega
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rcases hrs with hrs | hrs | hrs <;> rw [hrs] <;> decide) .running (by decide) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _))
    (P1.sched.set_thread_state.running_blkR (Es := P1.EH H) s t J.blk htH hr0)) ?_
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
    rcases hrs with hrs | hrs | hrs <;> rw [hrs] <;> exact ⟨rfl, rfl, fun _ e => by cases e⟩
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
      · subst e; exact J.inv.rd _ x hk (Or.inl (by rcases hrs with hrs | hrs | hrs <;> rw [hrs] <;> rfl))
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
    rw [e, hk] at h1; cases h1; rcases hrs with hrs | hrs | hrs <;> rw [hrs] at h3 <;> cases h3
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
        subst hp; rw [hk] at hk'; cases hk'; rcases hrs with hrs | hrs | hrs <;> rw [hrs] at h0 <;> simp [tsCode] at h0)
      hlk hfk hAI.1 hY' (hYK6.dk q.bv) (fun h => h) (J.jcov.dead q hq)
  exact ⟨Lst', D, J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2)) (J.sc_kern hW hK hfk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv hcur6 hown6 hoff hAI (BlockedScActive.tkw J.bsa hK fun p y n hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk6] at hp; cases hp
      · rw [hkp _ e] at hp; exact ⟨y, hp, ha, fun _ h => h, id⟩) hcr6 hblk hKd (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD⟩

set_option maxHeartbeats 16000000 in
/-- **`reply1` of a runnable thread at `J`** (XTopJointReply's
`JAtZ.reply1J` with `JAtZ.runRJ`): `JAt` at the spec's state with the reply
registers (when called) and `Running`. -/
theorem JAtZ.reply1RJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart ∨ x.tcbState = .running ∨ x.tcbState = .runningVM) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => JAt (L := L) arI AR s2 a (stsAct (updK σ ct.bv
      (.tcb { (if call then Endp.replyTcb x v.bv else x) with tcbState := .running })) ct.bv) ⦄ := by
  unfold vspace.reply1
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (J.runRJ hct hk hrs) ?_
    rintro s2 ⟨Lst', D', J2⟩
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
    refine WP.spec_mono (J3.runRJ hct hkC hrs) ?_
    rintro s4 ⟨Lst', D', J4⟩
    rw [updK_updK] at J4
    exact ⟨_, _, _, _, _, _, J4⟩


/-- **The spec's restart, reply and `Running` after an omitted restart**
(as VsReplyTop's `tacHypX_topT`): the reply registers (when called) and
`Running` of the thread at the state before the restart. -/
theorem specTail_tac {σ σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x))
    (hσ1 : Fl4Spec.setThreadState (Z := Unit) t .restart σ = ({((), σ1)}, False)) (call : Bool) (v : Fl4Spec.Word)
    {z : Unit × Fl4Spec.State Unit} (hz : z ∈ (specTail call t [v] σ1).1) :
    z.2 = Notif.stsAct (Notif.updK σ t (.tcb { (if call then Endp.replyTcb x v else x) with
      tcbState := .running })) t := by
  have e : σ1 = Notif.stsAct (Notif.updK σ t (.tcb { x with tcbState := .restart })) t := by
    rw [Notif.setThreadState_eq .restart hk] at hσ1
    have := congrArg Prod.fst hσ1
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e
  have hk1 : (Notif.stsAct (Notif.updK σ t (.tcb { x with tcbState := .restart })) t).kheap t =
      some (.tcb { x with tcbState := .restart }) := by simp [Notif.stsAct_kheap]
  rw [specTail_restart hk1 rfl call v] at hz
  have hsch : ∀ y : Fl4Spec.Tcb, y.tcbSchedContext = x.tcbSchedContext → Fl4Spec.runnable y.tcbState = true →
      Fl4Spec.schedulable t (Notif.updK σ t (.tcb { x with tcbState := .restart })) =
        Fl4Spec.schedulable t (Notif.updK σ t (.tcb y)) := fun y h1 h2 =>
    schedulable_updK_tcb (by rw [h2]; rfl) h1.symm
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte] at hz ⊢
    rw [Notif.setThreadState_eq .running hk1, stsAct_twice (hsch { x with tcbState := .running } rfl rfl)] at hz
    rw [Set.mem_singleton_iff.1 hz]
  · simp only [↓reduceIte] at hz ⊢
    have hkC : (Notif.updK (Notif.stsAct (Notif.updK σ t (.tcb { x with tcbState := .restart })) t) t
        (.tcb (Endp.replyTcb { x with tcbState := .restart } v))).kheap t =
        some (.tcb (Endp.replyTcb { x with tcbState := .restart } v)) := by simp
    rw [Notif.setThreadState_eq .running hkC, updK_updK] at hz
    have ey : ({ Endp.replyTcb { x with tcbState := .restart } v with tcbState := .running } : Fl4Spec.Tcb) =
        { Endp.replyTcb x v with tcbState := .running } := rfl
    rw [ey, stsAct_twice (hsch { Endp.replyTcb x v with tcbState := .running } rfl rfl)] at hz
    rw [Set.mem_singleton_iff.1 hz]

/-- A runnable state is `Restart`, `Running` or `RunningVM`. -/
theorem runnable3 {ts : Fl4Spec.ThreadState} (h : Fl4Spec.runnable ts = true) :
    ts = .restart ∨ ts = .running ∨ ts = .runningVM := by
  cases ts <;> simp_all [Fl4Spec.runnable]

/-- The slots' words across the accessed-bit clear of a page-table word. -/
theorem slotsSame_clr5 {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
    {th : TypedHeap} (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {b : U64}
    (hb : PtWAll L4 L3 L2 L1 b) (hal : P1.Aligned b) :
    SlotsSame th (L.mem s) (L.mem (L.wr s b (L.mem s b &&& ~~~32#u64))) := by
  refine slotsSame_wr hS.2.pl s _ hal (fun a ha => ?_)
  obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hS.2.pl ha
  have := (hS.2.po b hb).2 p k hk
  omega

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across the accessed-bit clear** of a page-table word, the spec
unchanged (VsTopX's `finX_clr5`; the CSpace relations by `cspace_step`, the
domain words by `domSame_low`, as `tacHypX_topT`). -/
theorem XTopAt.clr5 (hX : XTopAt (L := L) AR Z s a σ) {b : U64} (hb : PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b)
    (hba : P1.Aligned b) : XTopAt (L := L) AR Z (L.wr s b (L.mem s b &&& ~~~32#u64)) a σ := by
  obtain ⟨hPl, hCR, hFI, hDom, hMO, hIA, hSA⟩ := hX.rel
  have hF := hX.fin
  set s' := L.wr s b (L.mem s b &&& ~~~32#u64) with hs'
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_clr5 hF.1 hb hba
  have hksb : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hSt : StateRel Z.th (L.mem s') σ := hCR.1.of_caps (fun y hy => hSS.capAt hy)
  have hK0 : KFoot σ σ := ⟨rfl, rfl, fun o h => absurd rfl h, rfl⟩
  obtain ⟨hCR', hFI', hMO'⟩ := cspace_step hCR hFI hMO hSS hK0 hSt
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hF.1.2.vs.ksb_fit; omega
  have hka : (L.ksb s).val % 8 = 0 := hF.1.2.vs.ksb_al
  have hDom' : DomRel (L.mem s') (L.ksb s) σ := by
    refine hDom.of_same (domSame_low hkf hka fun b' hb' h1 h2 => ?_) rfl rfl
    refine Notif.rd_wr_ne hba hb' (fun e => ?_)
    subst e
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    refine hF.1.2.disj _ (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
      (table_vobj hF.1.2.pt hq hi _)
  have hF' := finX_clr5 hF hb hba
  obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hF'
  exact ⟨hF', ⟨hPl, hCR', hFI', by rw [hksb]; exact hDom', by rw [hksb]; exact hMO', by rw [hksb]; exact hIA, hSA⟩,
    IpcRel.of hNt hEp (sched_sc hSch), hX.esa.mono hksb (fun _ x _ h => ⟨x, h⟩)⟩

set_option maxHeartbeats 4000000 in
/-- **`JAtZ` across the accessed-bit clear** (`JAtZ.vsStepJ` with the spec
unchanged, every slot kept). -/
theorem JAtZ.clrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    (hnu : isUt (capV (L.mem s) (cslotAddr (pc.bv, idx))) = false)
    {b : U64} (hb : PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b) (hba : P1.Aligned b) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s b (L.mem s b &&& ~~~32#u64)) a σ := by
  have hSS := slotsSame_clr5 J.xtop.fin.1 hb hba
  have hW : P1.WritesIn st s (L.wr s b (L.mem s b &&& ~~~32#u64))
      (VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx))) :=
    (P1.writesIn_wr hba).mono fun b' e => Or.inl (Or.inl (by rw [e]; exact hb))
  have hA : IsSlot Z.th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := Z.th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  refine J.vsStepJ (jVsApartHyp arI Z H Cs Ac Lst D s a σ rfl J) hpc hidx (J.xtop.clr5 hb hba)
    (VsSFr.of_eq rfl) hW (fun y hy _ => hSS.capV hy) (by rw [hSS.capV hA]) (by rw [hSS.capV hA]) hnu (by rw [hSS.capV hA])
    (fun y hy => ⟨(hSS y hy).2.2.1, (hSS y hy).2.2.2⟩) (J.vsc.of_eq fun y hy => hSS.capV hy)

end

/-! ## The frame's replying labels at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **Frame `GetAddress` at `JAt`** (module docstring). -/
theorem decode_invocation_frame_gaJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (slot : U64) (blk call don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.Frame p sz rt d m false asid va) blk call don
      fp buf extra slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (hX.curTcb hcur).1
  have hcT : ct ∈ Z.T := J.thT ct htcb
  obtain ⟨-, hCR, hFI, hDR, hMO, -, -⟩ := hX.rel
  have hX0 : FinXT (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR (L.ksb s) σ s ar σ :=
    vs_x0T hX.fin.1 hX.fin.2.1 hX.fin.2.2.1 hX.fin.2.2.2.1 hX.fin.2.2.2.2 hCR hFI hMO
  have hga : GetAddrHypX (L := L) (fun s' a' σ' => FinXT (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E
      Z.R Z.B Z.c AR (L.ksb s) σ s' a' σ' ∧ JAt (L := L) arI AR s' a' σ') s σ ar ct p call := by
    intro hXs
    have hT := getAddrHypX_topT (L := L) (th := Z.th) (P := Z.P) (L4 := Z.L4) (L3 := Z.L3) (L2 := Z.L2)
      (L1 := Z.L1) (N := Z.N) (T := Z.T) (C := Z.C) (E := Z.E) (R := Z.R) (B := Z.B) (c := Z.c) (AR := AR)
      s ar σ Z.G hCR hFI hMO hDR ct p call hcur.symm htcb J.kern.act
      (fun y hy => by rw [hk] at hy; cases hy; exact hrun) hXs.1
    obtain ⟨s1, σ1, x1, -, hst1, hk1', -, eσ1, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    rw [hk] at hk1'; cases hk1'
    have hk1 : σ1.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
      rw [eσ1, stsAct_kheap]; simp [updK]
    refine WP.spec_mono (WP.spec_and hT (show (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let s2 ← vspace.reply1 st s1 ct call (core.num.U64.wrapping_sub p layout.PPTR_BASE)
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar)) ⦃ res =>
          ∀ z ∈ (specTail call ct.bv [(core.num.U64.wrapping_sub p layout.PPTR_BASE).bv] σ1).1,
            JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄ from ?_)) ?_
    · rw [hs1]; simp only [bind_ok]
      exact WP.spec_bind (J1.reply1J hcT hk1 rfl call _) (fun s2 h => (WP.spec_ok _).2 h)
    rintro res ⟨⟨h1, hne, hall⟩, hJ⟩
    refine ⟨h1, hne, fun σ1' hσ1' => ?_⟩
    obtain ⟨z, hz, hRT, hXz⟩ := hall σ1' hσ1'
    rw [hcur] at hst1
    rw [hst1] at hσ1'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hσ1'))
    exact ⟨z, hz, hRT, hXz, hJ z (by rw [paddr_bv]; exact hz)⟩
  have hD := decode_invocation_frame_getaddrX (L := L) arI (X := fun s' a' σ' => FinXT (L := L) Z.th Z.P Z.L4 Z.L3
      Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR (L.ksb s) σ s' a' σ' ∧ JAt (L := L) arI AR s' a' σ')
    s ar σ lbl slbl hlbl hl length buf ct hct hcur hk (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d)
    (m := m) slot blk call don fp hga ⟨hX0, Z, H, Cs, Ac, Lst, D, J⟩ extra args ci sl excaps buffer
  exact Or.inr (DecOKRMX.toXR arI hD hDR (fun _ _ _ hx _ => hx.2))

set_option maxHeartbeats 8000000 in
/-- **Frame `TestAndClearAccessed` at `JAt`** (module docstring). -/
theorem decode_invocation_frame_tacJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hl : lbl = fl4_abi.label.X86PageTestAndClearAccessed)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (blk call don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (hX.curTcb hcur).1
  have hcT : ct ∈ Z.T := J.thT ct htcb
  obtain ⟨-, hCR, hFI, hDR, hMO, -, -⟩ := hX.rel
  have hnu : isUt (capV (L.mem s) (cslotAddr (pc.bv, idx))) = false := by rw [capV_of_capAt hcap]; rfl
  have hX0 : FinXT (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR (L.ksb s) σ s ar σ :=
    vs_x0T hX.fin.1 hX.fin.2.1 hX.fin.2.2.1 hX.fin.2.2.2.1 hX.fin.2.2.2.2 hCR hFI hMO
  have htac : TacHypX (L := L) (fun s' a' σ' => FinXT (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E
      Z.R Z.B Z.c AR (L.ksb s) σ s' a' σ' ∧ JAt (L := L) arI AR s' a' σ') Z.L4 Z.L3 Z.L2 Z.L1 s σ ar ct call := by
    intro b hb hba v hv hXb
    have hT := tacHypX_topT (L := L) (th := Z.th) (P := Z.P) (L4 := Z.L4) (L3 := Z.L3) (L2 := Z.L2)
      (L1 := Z.L1) (N := Z.N) (T := Z.T) (C := Z.C) (E := Z.E) (R := Z.R) (B := Z.B) (c := Z.c) (AR := AR)
      s ar σ Z.G hCR hFI hMO hDR ct call hcur.symm htcb J.kern.act
      (fun y hy => by rw [hk] at hy; cases hy; exact hrun) b hb hba v hv hXb.1
    have Jc := J.clrJ hpc hidx hnu hb hba
    refine WP.spec_mono (WP.spec_and hT (Jc.reply1RJ hcT hk (runnable3 hrun) call v)) ?_
    rintro s2 ⟨⟨hne, hall⟩, hJ⟩
    refine ⟨hne, fun σ1 hσ1 => ?_⟩
    obtain ⟨z, hz, hRT, hXz⟩ := hall σ1 hσ1
    refine ⟨z, hz, hRT, hXz, ?_⟩
    rw [specTail_tac hk hσ1 call v.bv hz]
    exact hJ
  have hD := decode_invocation_frame_tacX (L := L) arI (X := fun s' a' σ' => FinXT (L := L) Z.th Z.P Z.L4 Z.L3
      Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR (L.ksb s) σ s' a' σ' ∧ JAt (L := L) arI AR s' a' σ')
    s ar σ hX.fin.2.1 hX.fin.2.2.1 hX.fin.1.2.pt hX.fin.2.2.2.1 lbl slbl hlbl hl length buf ct hct hcur hk
    (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d) (m := m)
    (hfu := by
      have h := J.vsc.at (show AbsSlot Z.th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot hcap
      simp only [Vs.VCapW, Vs.VCapOK] at h; exact h.2.2) (cslotAddr (pc.bv, idx)) blk call don fp
    htac ⟨hX0, Z, H, Cs, Ac, Lst, D, J⟩
    (fun b hb hal => ⟨finXT_clr5 hX0 hb hal, Z, H, Cs, Ac, Lst, D, J.clrJ hpc hidx hnu hb hal⟩)
    extra args ci sl excaps buffer
  exact Or.inr (DecOKRMX.toXR arI hD hDR (fun _ _ _ hx _ => hx.2))

set_option maxHeartbeats 4000000 in
/-- **A native frame cap at `JAt`**, `JPostHyp` [W] only for
`DeriveSubframe` (XTopJointVsMap's `decode_invocation_frameJV` for Map and
Unmap, `decode_invocation_frame_gaJ`, `decode_invocation_frame_tacJ`). -/
theorem decode_invocation_frameJR [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hlGA : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress →
      lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : lbl = fl4_abi.label.X86PageDeriveSubframe →
      JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk
        call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
      buffer ct := by
  by_cases hga : lbl = fl4_abi.label.X86PageGetAddress
  · exact decode_invocation_frame_gaJ arI s ar σ J hni lbl slbl hlbl hga length buf ct hct _ blk call don fp extra
      _ ci _ excaps buffer
  by_cases htac : lbl = fl4_abi.label.X86PageTestAndClearAccessed
  · exact decode_invocation_frame_tacJ arI s ar σ J hni lbl slbl hlbl htac length buf ct hct hpc hidx hcap blk call
      don fp extra _ ci _ excaps buffer
  exact decode_invocation_frameJV arI s ar σ J hni hA hVC lbl slbl hlbl hlGA length buf ct hct args hlen hargs hpc
    hidx hcap hno extra excaps hex blk call don fp ci buffer
    (fun h => h.elim hR (fun h => h.elim (fun e => absurd e hga) (fun e => absurd e htac)))

end

end

end Fl4Proofs.P3
