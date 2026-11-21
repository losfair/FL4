/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch23b (c2)): **the cap
fault of `handle_recv` at a `chooseNewThread` mid state where ct has no SC**
(`MidN`, XTopJointMidN), every handler case. Scripted copies
(sch23bgen/genf.py, untracked) of the `MidC` lemmas (XTopJointFaultC,
XTopJointFaultRecvC) with ct's SC field `none` for `CurInv`:

* ct out of the release queue by `Sched.Inv.notRel_of_noSc`, P1's `CanBlock`
  by `JAtZ.canBlockCurMN`;
* `BlockedScActive` after ct blocks: an SC bound to ct would be ct's SC
  (`scBack_of`), none;
* ct's SC word in `Ac` (the reply-pushing send): vacuous, the word is `0`;
* the donation flag is `false` (FL4 reads ct's SC word, `0`), so the
  donating send `sendFaultPDJC` does not arise (`faultRecvJN`).

`JAtZ.stsCurJN`, `JAtZ.noFaultJN`, `JAtZ.faultBlockJN`, `JAtZ.sendFaultIJN`,
`JAtZ.sendFaultPJN`, `JAtZ.faultRecvJN`, `JAtZ.faultHypJZN` (every
`handle_fault` at a `MidN` state).
-/
import Fl4Proofs.P3.XTopJointMidN
import Fl4Proofs.P3.XTopJointFaultRecvC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Inactive` of the current thread at `J` under a
pending reschedule (ct SC-less)** (module docstring). -/
theorem JAtZ.stsCurJN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) {t : U64} (ht : t ∈ Z.T)
    (htD : t ∉ D) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hcur : σ.curThread = t.bv)
    (hrn : Fl4Spec.runnable x.tcbState = true) (hnq : ∀ d p, t.bv ∉ σ.readyQueues d p)
    (hB : sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄) :
    sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZR (L := L) arI AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := .inactive })) t.bv) ⦄ := by
  have hts : tsCode Fl4Spec.ThreadState.inactive < 3 := by decide
  have hcode := runnable_code hrn
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst]; omega, by rw [hst]; omega⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hnr : t.bv ∉ σ.releaseQueue := J.inv.notRel_of_noSc hk (hni.2.2.2 _ (by rw [hcur]; exact hk))
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by omega) .inactive hts sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
    (set_thread_state_sfoot hS ht _)) (set_thread_state_yw hS ht _)) hB) ?_
  rintro s6 ⟨⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩, hblk, hfoot⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  set x6 : Fl4Spec.Tcb := { x with tcbState := .inactive } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ p, p ≠ t.bv → σ6.kheap p = σ.kheap p := by
    intro p hp; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hp]
  have hact6 : σ6.schedulerAction = σ.schedulerAction := by
    rw [hσ6]; unfold stsAct; rw [if_neg (fun h => hsw h.2.1)]; rfl
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_csc : σ6.curSc = σ.curSc := by rw [hrec]; rfl
  have e_cons : σ6.consumedTime = σ.consumedTime := by rw [hrec]; rfl
  have e_tm : σ6.curTime = σ.curTime := by rw [hrec]; rfl
  have e_idle : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have e_rel : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := runnable_free hrn
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
    refine J.inv.step (NtfnStep.tcb hk .inactive x.tcbArch) (fun u x0 y h1 h2 hqd hr => ?_)
      (fun u x0 y h1 h2 hc => ?_)
    · by_cases e : u = t.bv
      · subst e
        rcases hqd with ⟨d, p, hm⟩ | hm
        · exact absurd hm (hnq d p)
        · exact absurd hm hnr
      · have h2' : σ.kheap u = some (.tcb y) := by simpa [hσ1, updK, e] using h2
        rw [h1] at h2'; cases h2'; exact hr
    · by_cases e : u = t.bv
      · subst e; simp [hσ1, updK] at h2; subst h2
        exact absurd hc (by intro h; rcases h with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩ <;> cases h)
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
  have hsp : Fl4Spec.setThreadState (Z := Unit) t.bv .inactive σ = ({((), σ6)}, False) :=
    Notif.setThreadState_eq .inactive hk
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
  have hidt : σ.idleThread ≠ t.bv := fun e => hni.1 (by rw [hcur, e])
  have hAI : ActIdle σ6 := by
    refine J.act.keepE (E := fun p => p = t.bv) ⟨fun p x0 hp hx => by rw [hkp p hp]; exact hx,
      fun p y m hp => ⟨y, by rw [hkp p (fun e => by rw [e, hk] at hp; cases hp)]; exact hp, rfl⟩⟩
      (fun u hu => Or.inl (by rw [e_rel] at hu; exact hu)) (Or.inl hact6) e_idle (fun u hu => ?_) hidt e_isc
    rw [hni.2.2.1] at hu; cases hu
  have hoff : OffOK σ6 := by
    intro h0 y n hy ha
    rw [e_cons] at h0 ⊢; rw [e_tm]; rw [e_csc] at hy; rw [e_csc, e_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.off h0 y n hy ha
  have hcur6 : CurInvR σ6 := fun h => absurd (hact6.symm.trans h) hsw
  have hown6 : CurOwnW Z.T Z.C σ6 := by
    have hsc6 : ∀ y n, σ6.kheap σ6.curSc = some (.schedContext y n) → σ.kheap σ.curSc = some (.schedContext y n) := by
      intro y n hy
      rw [e_csc] at hy
      by_cases e : σ.curSc = t.bv
      · rw [e, hk6] at hy; cases hy
      · rw [hkp _ e] at hy; exact hy
    rcases J.own with ⟨u, hu, xt, hkt, hxs, hown, hnr'⟩ | ⟨hcs, hun⟩
    · left
      by_cases hut : u.bv = t.bv
      · rw [hut, hk] at hkt; cases hkt
        exact ⟨u, hu, x6, by rw [hut]; exact hk6, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr' (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
      · exact ⟨u, hu, xt, by rw [hkp _ hut]; exact hkt, by rw [e_csc]; exact hxs, fun y n hy => hown y n (hsc6 y n hy),
          fun h0 hm => hnr' (by rw [← e_cons]; exact h0) (by rw [e_rel] at hm; exact hm)⟩
    · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y n hy => hun y n (hsc6 y n hy)⟩
  have hcr6 : CurRunM σ6 := Or.inl (by rw [hact6]; exact hsw)
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
  exact ⟨Lst', J.sc_frameR hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2)) (J.sc_kern hW hK hfk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv hcur6 hown6 hoff hAI (BlockedScActive.tkw J.bsa hK fun p y n hp ha => by
      by_cases e : p = t.bv
      · rw [e, hk6] at hp; cases hp
      · rw [hkp _ e] at hp; exact ⟨y, hp, ha, fun _ h => h, id⟩) hcr6 hblk hKd (J.idleW_keep hX'.fin.1.1.1 hfk.2.1 hfk.2.2).1 J.zD⟩

set_option maxHeartbeats 8000000 in
/-- **`handle_fault` with a null fault handler at `J` under a pending
switch** (module docstring). -/
theorem JAtZ.noFaultJN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hnull : capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok .Null)
    (f : error.Fault) (f' : Fl4Spec.Fault) :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAtR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have hrn : Fl4Spec.runnable x.tcbState = true := hni.run x (by rw [hcur]; exact hk)
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have e1 : c1 = .Null := by rw [hnull] at hc1; simpa using hc1.symm
  subst e1
  have hfh : x.tcbFaultHandler = .nullCap := by rw [← hcr.2]; rfl
  -- the current thread among the TCBs
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hT : ct ∈ Z.T := by rw [hct']; exact hc.curT
  have hD : ct ∉ D := fun h => J.notDead hT hk (by have := runnable_code hrn; omega) ct h rfl
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  have hnr : ct.bv ∉ σ.releaseQueue := J.inv.notRel_of_noSc hk (hni.2.2.2 _ (by rw [hcur]; exact hk))
  obtain ⟨bq, br⟩ := J.curBits hT hnq' hnr
  obtain ⟨hna, -⟩ := J.words_of_spec hT (fun u hu => by rw [hni.2.2.1] at hu; cases hu)
    (fun e => hni.1 (by rw [hcur, e]))
  obtain ⟨x0, hk0, hTR⟩ := (J.xtop.irelK J.ks J.buf).1.tcb ct hT
  rw [hk] at hk0; cases hk0
  have hv : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by
    rw [P1.stA_eq, ← tStA_eq]; exact hTR.st
  obtain ⟨hnb, hnrp⟩ := P1.run_word (w := L.mem s (P1.stA ct)) (by rw [hv]; exact runnable_code hrn)
  have hB := P1.sched.set_thread_state.inactive_blkR (Es := P1.EH H) s ct J.blk (J.zH.1 ct hT) hnb hnrp bq br hna
  have hspec := handleFault_null hk hfh f'
  unfold faults.handle_fault
  rw [tcb_slot_fault]
  apply ok_bind_spec
  rw [slot_cap_eq, hnull]
  apply ok_bind_spec
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, _hi⟩
  unfold faults.send_fault_ipc
  dsimp only
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (J.stsCurJN hni hsw hT hD hk hcur hrn hnq' hB) ?_
  rintro s6 ⟨Lst', J6⟩
  refine (WP.spec_ok _).2 ⟨_, by rw [hspec]; exact Set.mem_singleton _,
    ⟨Z.th, Z.G, J6.xtop.rel.1, J6.xtop.rel.2.1, J6.xtop.rel.2.2.1, J6.xtop.rel.2.2.2.1, J6.xtop.rel.2.2.2.2.1⟩,
    ⟨Z, H, Cs, Ac, Lst', D, J6⟩⟩

set_option maxHeartbeats 64000000 in
/-- **`handle_fault` with an endpoint handler and no waiting receiver at
`J` under a pending reschedule (ct SC-less)** (module docstring). -/
theorem JAtZ.faultBlockJN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {ptr bdg : U64} {sd rv g gr : Bool}
    (hep : capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok (.Endpoint ptr bdg sd rv g gr))
    (hcb : ∀ xe, σ.kheap ptr.bv = some (.endpoint xe) → Endp.CanBlock false xe)
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAtR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩ := hf
  obtain ⟨⟨lt, l0, l1⟩, he, -⟩ := spec_exists (encode_lfRel hlf)
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have hrn : Fl4Spec.runnable x.tcbState = true := hni.run x (by rw [hcur]; exact hk)
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have ht : ct ∈ Z.T := by rw [hct']; exact hcq.curT
  have hta := hP0.e.tcb ct ht
  have htH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct ht
  have htD : ct ∉ D := fun h => J.notDead ht hk (by have := runnable_code hrn; omega) ct h rfl
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  have hnr : ct.bv ∉ σ.releaseQueue := J.inv.notRel_of_noSc hk (hni.2.2.2 _ (by rw [hcur]; exact hk))
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  have hidt : σ.idleThread ≠ ct.bv := fun e => hti (by rw [hcur, e])
  -- the handler cap, its endpoint
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have e1 : c1 = .Endpoint ptr bdg sd rv g gr := by rw [hep] at hc1; simpa using hc1.symm
  subst e1
  have habs := hcr.2
  simp only [absCap] at habs
  have hfh : x.tcbFaultHandler = .endpointCap ptr.bv bdg.bv (rightsOf sd rv g gr) := habs.symm
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : ptr ∈ Z.E := J.slotE hAS hep
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  have hcbe : Endp.CanBlock false xe := hcb xe hke
  have hpt : ptr.bv ≠ ct.bv := fun e => by rw [e, hk] at hke; cases hke
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s _) hAS.isSlot hep (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  -- P1's `CanBlock` of the current thread
  obtain ⟨bq, br⟩ := J.curBits ht hnq' hnr
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct ht
  rw [hk] at hk0; cases hk0
  have hv : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by
    rw [P1.stA_eq, ← tStA_eq]; exact hTR.st
  obtain ⟨hnb, hnrp⟩ := P1.run_word (w := L.mem s (P1.stA ct)) (by rw [hv]; exact runnable_code hrn)
  have hcw : L.curW s = ct := by
    apply P1.eq_of_bv
    rw [← hcur, hs.curThread]
    unfold P1.LawfulStore.curW nodeW; rw [hcq.cur]
  have hcbP : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := J.canBlockCurMN ht hcur hk hrn hti hnr hni hnq
  -- the spec's donation flag is FL4's
  obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb ct ht
  rw [hk] at hkt6; cases hkt6
  have hdon : (L.mem s (scA ct) != 0#u64) = decide (x.tcbSchedContext ≠ none) := by
    rw [hsct6]
    by_cases h0 : L.mem s (scA ct) = 0#u64
    · simp [h0, Notif.optRef]
    · simp [h0, Notif.optRef]
  -- `handle_fault`: the handler cap
  unfold faults.handle_fault
  rw [tcb_slot_fault]
  apply ok_bind_spec
  rw [slot_cap_eq, hep]
  apply ok_bind_spec
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => r.1 = true ∧
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault a0.bv rp lf') σ).1,
      RelTopM (L := L) r.2.1 z.2 ∧ JAtR (L := L) arI AR r.2.1 r.2.2 z.2) ?_ ?_
  swap
  · rintro ⟨b0, s2, a2⟩ ⟨hb, hr0⟩
    simp only at hb hr0
    subst hb
    exact (WP.spec_ok _).2 hr0
  unfold faults.send_fault_ipc
  dsimp only
  -- `set_fault`
  set f' : Fl4Spec.Fault := .capFault a0.bv rp lf' with hf'
  set x2 : Fl4Spec.Tcb := { x with tcbFault := some f' } with hx2
  set σf := updK σ ct.bv (.tcb x2) with hσf
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_fault_cap_top hP0 hI ht hk ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩)
      (set_fault_cap_eq (L := L) s ct a0 rp lf he))
      (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s ct (.Cap a0 rp lf) (t0 := ct) J.blk htH
        (fun _ h => by simp at h) hcbP)
        (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
          (Es := P1.EH H) s ct (.Cap a0 rp lf) hTH htH))) ?_
  rintro s7 ⟨⟨⟨-, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩
  have hkf : σf.kheap ct.bv = some (.tcb x2) := by simp [hσf, updK]
  have hkfp : ∀ q, q ≠ ct.bv → σf.kheap q = σ.kheap q := by
    intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']
  have hkef : σf.kheap ptr.bv = some (.endpoint xe) := by rw [hkfp _ hpt]; exact hke
  -- the FL4 step of `set_fault`: the seven words
  have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s7 σf := by
    refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := ct.bv) (x' := x2) (fun q hq' => by simp [hσf, updK, hq']) hkf)⟩
    subst hs7
    have w := ((((((writesIn_wr (st := st) (s := s) (v := lt) (a_lf hta).1).trans
      (writesIn_wr (v := l0) (a_lf0 hta).1)).trans (writesIn_wr (v := l1) (a_lf1 hta).1)).trans
      (writesIn_wr (v := fl4_abi.consts.fault.CapFault) (a_fault hta).1)).trans (writesIn_wr (v := a0) (a_fw0 hta).1)).trans
      (writesIn_wr (v := if rp then 1#u64 else 0#u64) (a_fw1 hta).1)).trans
      (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
    refine w.mono fun w0 hw0 => ?_
    have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = ct.val + K := by
      rcases hw0 with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h
      · exact ⟨3408, by omega, by omega, by omega, by omega, by omega, val_lf hta⟩
      · exact ⟨3416, by omega, by omega, by omega, by omega, by omega, val_lf0 hta⟩
      · exact ⟨3424, by omega, by omega, by omega, by omega, by omega, val_lf1 hta⟩
      · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
      · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
      · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
      · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
    obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
    exact Or.inl (Or.inr ⟨ct, ht, K, k1, k2, k3, k4, k5, k6⟩)
  -- the spec's blocking send at `σf`
  have hprf : ∀ u, Sched.prioOf σf u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = ct.bv
    · subst hut; exact (prioOf_eq hkf).trans (prioOf_eq hk).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq, hkfp u hut]
  have hnb0 : tsCode x.tcbState ≠ 3 ∧ tsCode x.tcbState ≠ 4 := by
    have := runnable_code hrn; omega
  have htq : ct.bv ∉ xe.epQueue := Endp.not_queued hI.1.toE ht hk hnb0 ptr hpE xe hke
  have hqm : ∀ u ∈ xe.epQueue, ∃ z, σf.kheap u = some (.tcb z) := fun u hu => by
    obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hke).2 u hu
    exact ⟨z, by rw [hkfp u (fun e => htq (e ▸ hu))]; exact hz⟩
  obtain ⟨σ', heq, F0, hik0, ⟨ds, hkt'⟩, -, -, -, hsrt, hactK⟩ :=
    sendIpcBlock_eqM hkf hkef hcbe htq hqm hrn ((J.isorted.1 _ _ hke).congr fun u _ => hprf u)
      false bdg.bv g gr (L.mem s (scA ct) != 0#u64)
  -- FL4's blocking send
  have hIS : IpcSorted σf := QPK.QPS.sorted (QPK.qps_upd (ko := .tcb x2) hk rfl) J.isorted
  obtain ⟨⟨Q0, R0, h0⟩, hB0', hX0, hS0, hSg0⟩ := hblk7
  have hst0 : L.epState s7 ptr = 0#u64 ∨ L.epState s7 ptr = 1#u64 := by
    have hx := hI7.1.toE.at_ep hpE hkef
    rw [epState_eq]
    cases xe with
    | idleEP => exact Or.inl hx.1
    | sendEP q => exact Or.inr hx.1
    | recvEP q => simp [Endp.CanBlock] at hcbe
  have hnn : ∀ m, x2.tcbState ≠ .blockedOnNotification m := fun m h => by
    have h' : tsCode x.tcbState = 6 := congrArg tsCode h
    have := runnable_code hrn; omega
  have p1f : endpoint.send_ipc st arI s7 a true false bdg g gr (L.mem s (scA ct) != 0#u64) ct ptr ⦃ s' _ =>
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s' ⦄ :=
    P1.endpoint.send_ipc.blockFoot arI s7 a true false bdg g gr _ ct ptr h0 (fun _ => hcb7) hHe hst0
  refine WP.spec_bind (WP.spec_and (WP.spec_and (send_ipc_blockF (ar := arI) hP0 s7 a σf hI7 ht hkf hnb0 hnn hpE hkef
    hcbe (Sched.qSorted_of_spec (L := L) hI7.1.toE hI7.1.toN hT hIS ptr (Or.inl hpE)) false bdg g gr
    (L.mem s (scA ct) != 0#u64))
    (P1.endpoint.send_ipc.block arI s7 a true false bdg g gr _ ct ptr Q0 R0 h0 hB0' hX0 hS0 hSg0
      (fun _ => hcb7) hHe hst0))
    p1f) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0, h0eq, hIR, hW3⟩, hbk⟩, hfoot3⟩
  simp only [WP.uncurry'_pair] at ea hbk hfoot3 hIR hW3
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  apply (WP.spec_ok _).2
  refine ⟨rfl, ?_⟩
  -- the spec's outcome
  have hz : ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
      (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
      (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) (decide (x.tcbSchedContext ≠ none)) ct.bv
      ptr.bv (updK σ ct.bv (.tcb { x with tcbFault := some f' }))).1 := by
    rw [rights_grant, rights_grantReply, ← hdon]
    show ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr _ ct.bv ptr.bv σf).1
    rw [heq]; exact Set.mem_singleton _
  refine ⟨((), σ'), handleFault_ep_mem hk hfh _ hz, ?_⟩
  -- the frame from the start
  have hkt3 : σ'.kheap ct.bv =
      some (.tcb { x with tcbState := .blockedOnSend ptr.bv ds, tcbFault := some f' }) := hkt'
  have hsk : Sk σ σ' := by
    have h2 : Sk σ σf := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact h2.trans F0.sk
  have F : BFrT ct.bv ptr.bv σ σ' := by
    refine ⟨hsk, fun q => ?_⟩
    by_cases hqt : q = ct.bv
    · subst hqt
      exact Or.inr ⟨_, _, hk, hkt3, Or.inl ⟨x, ptr.bv, ds, some f', rfl, rfl, rfl⟩⟩
    · rcases F0.kh q with e | ⟨o, o', h1, h2, hc⟩
      · exact Or.inl (e.trans (hkfp q hqt))
      · rw [hkfp q hqt] at h1
        rcases hc with ⟨_, _, _, _, _, e3, -⟩ | ⟨x1, y1, rfl, rfl, e3⟩
        · exact absurd e3 hqt
        · exact Or.inr ⟨_, _, h1, h2, Or.inr ⟨x1, y1, rfl, rfl, e3⟩⟩
  -- the FL4 footprint from the start
  have hC3 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf s' σ' := ⟨hW3, SzKeepC.of F0.szKeep⟩
  have hW : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := (hC2.trans hC3).1
  have hfoot := P1.Foot.trans hfoot7 hfoot3
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
  -- the assembly (as XTopJointSendBlockG's `JAtZ.runTmoJ`)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  -- the scheduler: the current thread blocked, a reschedule pending
  have hact' : σ'.schedulerAction = σ.schedulerAction := hactK (by show σf.schedulerAction ≠ _; exact hsw)
  have hAI3 : ActIdle σ' := by
    refine J.act.keepE (E := fun p => p = ct.bv) ⟨fun p x0 hp hx => F.tcbO hp hx, fun p y m hp => ⟨y, F.scF hp, rfl⟩⟩
      (fun u hu => Or.inl (by rw [F.sk.rel] at hu; exact hu)) (Or.inl hact') F.sk.idle (fun u hu => ?_)
      hidt F.sk.isc
    rw [hni.2.2.1] at hu; cases hu
  have hcur3 : CurInvR σ' := fun h => absurd (hact'.symm.trans h) hsw
  have hrun3 : CurRunM σ' := Or.inl (by rw [hact']; exact hsw)
  -- the dead: the thread is not dead; the endpoint leaves the dead set
  have hdead : ∀ q ∈ D \ {ptr}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ ct.bv := fun h => htD (by rw [← P1.eq_of_bv h]; exact hq.1)
    have hqe : q.bv ≠ ptr.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ⟨_, F.tcbO hqt hx, rfl, rfl, Or.inl rfl⟩) (fun x hx => ?_)
      (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1
      (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    obtain ⟨y, hy, hc'⟩ := F.epF hx
    rcases hc' with rfl | e1
    · exact hy
    · exact absurd e1 hqe
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {ptr})
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {ptr}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩)
      (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the blocked sender's `RelIfBound` from the runnable thread's)
  have hts6 : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some f' }) ct.bv σ =
      ({((), σf)}, False) := Notif.threadSet_eq _ hk
  have hik : IK ct.bv σ σ' :=
    ((ikm_threadSet (t := ct.bv) (p := ct.bv) (g := fun tcb => { tcb with tcbFault := some f' })
      fun _ => ⟨rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩).of_eq hts6).trans hik0
  have hnqT : NotQueued σ ct.bv := ⟨hnq', hnr⟩
  obtain ⟨hIB, -⟩ := (J.inv.toBut ct.bv).ik hnqT hik
  have hskp : Ipc.SKeep σ σ' := ⟨F.sk.rel, F.sk.tm, fun p y hy => by
    obtain ⟨x', hx', e, -⟩ := F.tcbScB hy; exact ⟨x', hx', e.symm⟩, fun p y n hy => F.scB hy⟩
  have hrib : RelIfBound σ' ct.bv := Ipc.RelIfBound.of_keep (J.inv.rd ct.bv x hk (Or.inl hrn)) hskp
  have I3 : Inv σ' := hIB.inv fun _ _ _ => hrib
  -- `BlockedScActive`: the thread's SC is the current SC, active
  have hscA : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some ct.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp).2⟩
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp hyt
    rw [hk] at hku; cases hku
    rw [hni.2.2.2 x (by rw [hcur]; exact hk)] at hxs; cases hxs
  have R : JRestR (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {ptr}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted fun y1 hy1 => (hsrt y1 hy1).congr fun u _ => (hprf u).symm,
      hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J' := J.toR.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R hKd F.sk.orig hidl.1 (J.zD_diffE hpE)
  exact ⟨⟨_, _, J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
    ⟨_, H, Cs, Ac, Lst, D \ {ptr}, J'⟩⟩

set_option maxHeartbeats 64000000 in
/-- **A cap-faulted sender's `send_ipc` to a waiting receiver at `J` where
the sender gets no reply** (XTopJointSendCall's `JAtZ.sendCallIJ` for
`call = false` and a sender with a cap fault, running or restarting: FL4 reads
the fault word where the call flag is false; the transfer is the fault
transfer `do_ipc_transfer_capFJ`).

Original docstring:
(module docstring): the receiver has no reply object, or the caller neither
the grant nor the grant-reply right (`hno`); as `JAtZ.sendRecvJ0` up to the
reply unlink, then the caller `Inactive` on `IRel` (its queue bits clear by
`JAtZ.curBits`: in no ready queue, `hnq`, l4v `ct_not_in_q`, and not in the
release queue, `CurInv.notRel`), the receiver `Running`, `JAtZ` by
`JAtZ.wake_postCI` (the spec's two state changes swapped, `ciSt_swap`), the
tail `JAtZ.sendTailJ`; the spec's outcome `sendIpc_callInactive_eq`. -/
theorem JAtZ.sendFaultIJN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrn : Fl4Spec.runnable xt.tcbState = true) {cf : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure}
    (hft : xt.tcbFault = some (.capFault cf rp lf)) (hct : σ.curThread = t.bv)
    (hcn0 : σ.schedulerAction = .chooseNewThread) (hsc0 : xt.tcbSchedContext = none) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hno : (g = false ∧ gr = false) ∨
      ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) :
    endpoint.send_ipc st arI s a blk false badge g gr don t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdc : d'.bv ≠ σ.curThread := by rw [hct]; exact Ne.symm htd'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, -, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have Fr1 : CFr e.bv d'.bv σ σ1 := CFr.upd hk (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hk (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (xferFaultStepJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) ht hdT htd hkt1 hkd1 hft e badge g
    hTP hdH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT hA2 (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xd b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  have Fr2 : CFr e.bv d'.bv σ σ2 := (Fr1.trans (CFr.um _ _ σ1 um2)).trans (CFr.upd (σ := Endp.setUm σ1 um2) hkd1
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans (IK.updSelf (σ := Endp.setUm σ1 um2) hkd1 hxsc))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((SKeep.um σ1 um2).trans (SKeep.updK (σ := Endp.setUm σ1 um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) ∧
      P1.WritesIn st s s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) s b ∨ RcvBufW xd b) ∧
      CFr e.bv d'.bv σ σ3 ∧ IK d'.bv σ σ3 ∧ Ipc.SKeep σ σ3 ∧ σ3.curThread = σ.curThread ∧
      σ3.schedulerAction = σ.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d')) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, x2, _, rfl, hR2, hS2', hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc, hq2, hW2, footW_trans (footW_of F1) F2, Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
      have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      have hX2' := IpcRel.ofSRN hR2 hS2'
      have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
      rw [hrA] at hiR hit
      refine WP.spec_mono (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
          hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
        (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
            (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
          (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
      rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
      have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, hrA] at b2; rw [← b2]; exact z3
      set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
      set σ3a := Notif.updK σ2 w.bv (.reply { xr with replyTcb := none }) with hσ3a
      have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
      have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
      have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc], ?_, hW3',
        footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2)⟩
      · rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
        exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
      · exact (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
          (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
      · have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2 (fun o0 h => by
          rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
        exact IK3b.trans (IK.sts _ _ _)
      · exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply { xr with replyTcb := none }) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
          (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
      · rw [e3s]; rfl
      · rw [e3s]; rfl
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
  rintro s3 ⟨σ3, x3, X3, hU, hR3, hS3, hkt3, hkd3, hrb3, hns3, hsc3, hq3, hW3, F3, Fr3, IK3, SK3, hct3, hact3,
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3⟩
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = fl4_abi.consts.fault.CapFault := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; rw [hfr.1]; unfold fl4_abi.consts.fault.CapFault; rfl
  have hks3 : L.ksb s3 = L.ksb s := hW3.1
  -- the caller's facts for its `Inactive`
  have hnrT : t.bv ∉ σ.releaseQueue := J.inv.notRel_of_noSc hkt hsc0
  obtain ⟨hqb, hrb'⟩ := J.curBits ht hnq hnrT
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := (IpcRel.ofSRN hR3 hS3).2.2.1
  have hna3 : L.actionW s3 ≠ t := by
    obtain ⟨Q, R', hcq, -⟩ := hSR3.lists
    have h := hSR3.act
    rw [hact3, hcn0] at h
    have ha1 : L.actionW s3 = 1#u64 := by unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
    rw [ha1]; intro h'; exact P1.notT_small hcq.tcbs (by simp) (h' ▸ ht)
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  have hstsT := WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hkt3 hqt3
      (by have := runnable_code hrn; omega) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot hSR3 ht sched.TS_INACTIVE))
    (WP.spec_and (P1.sts_all s3 t _ Q0 R0 h3 hB3 hX3 hS3' hSg3 htH P1.not_blocked_inactive P1.inactive_ne
        (Or.inr hnbt3) (hX3.noref (hTP t htH) hnrp3 (fun e0 => hnbt3 (Or.inr (Or.inl e0))))
        ⟨fun c hc' p hp hm => absurd hm (h0.notQ htH hqb hc' hp), fun c hc' hm => absurd hm (h0.notR htH hrb' hc'),
          fun e0 => absurd e0 hna3⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 t sched.TS_INACTIVE h3 htH))
  -- FL4: no reply pushed, the caller `Inactive`
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ sched.set_thread_state st s3 t sched.TS_INACTIVE = ok r.1)
    ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.CapFault fl4_abi.consts.fault.NullFault; decide)]
    by_cases hi : (L.mem s (tReplyA d') != 0#u64) = true
    · rw [if_pos hi]
      have hgg : g = false ∧ gr = false := by
        rcases hno with h | hn
        · exact h
        · exfalso
          have hr0 := hn xd hkd _ _ _ hstd
          rw [hr0] at hrep
          have h00 := optRef_none hrep
          rw [h00] at hi
          simp at hi
      obtain ⟨rfl, rfl⟩ := hgg
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
    · rw [if_neg hi]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
  rintro ⟨s4, a4⟩ ⟨ha4, hs4⟩
  simp only at ha4 hs4
  subst ha4
  try dsimp only
  have hpost := hstsT
  rw [hs4] at hpost
  obtain ⟨⟨⟨hR4, hS4⟩, hW4⟩, ⟨h4, hB4, hX4, hS4', hSg4, -, k4⟩, fu4⟩ := (WP.spec_ok _).1 hpost
  have hkd4 : (ciSt σ3 t.bv xt).kheap d'.bv = some (.tcb x3) := by rw [ciSt_kh (Ne.symm htd')]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, (ciSt σ3 t.bv xt).kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z (by rw [← ciSt_kh (ciSt_ne hz (fun _ h => by cases h))]; exact hz)
  have hx4 : d' ∈ {y | y ∈ X3 ∧ y ≠ t} ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := by
    rcases hx3 with h | h
    · exact Or.inl ⟨h, Ne.symm htd⟩
    · right
      have e0 : L.mem s4 (P1.stA d') = L.mem s3 (P1.stA d') := by
        rw [P1.stA_eq]
        exact k4.fld d' hdH _ (by simp) (by simp) (by simp) (by simp) (fun e1 => absurd e1 (Ne.symm htd))
      rw [e0]; exact h
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' := fun r hr => by
    rcases k4.rtcb r hr with e0 | ⟨-, e0⟩
    · rw [e0]; exact hnr3 r hr
    · rw [e0]; intro h0'; exact hdta.ne0 (by rw [← h0']; rfl)
  have hks4 : L.ksb s4 = L.ksb s := hW4.1.trans hks3
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q0 R0 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)) d'.bv = ciSt σa t.bv xt :=
    ciSt_swap htd' hdc3
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 (ciSt σa t.bv xt) := by
    rw [← heq5]; exact hIR0
  have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW3.trans1 (hW4.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb)))))
  have hW5' : P1.WritesIn st s s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr (X := {y | y ∈ X3 ∧ y ≠ t}) (fun y hy => hXc3 y hy.1))⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have Fr5 : CFr e.bv d'.bv σ σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σ (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σ σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : Ipc.SKeep σ σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hnqD : NotQueued σ d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σa.schedulerAction = σ.schedulerAction := by
    rw [hσa, stsAct_ne (by show d'.bv ≠ σ3.curThread; exact hdc3)]; exact hact3
  -- the caller's `Inactive` after the wake (`ciSt_swap`)
  have hnqT : ∀ dm p, t.bv ∉ σa.readyQueues dm p := by rw [IK5.2.1]; exact hnq
  have hnrT' : t.bv ∉ σa.releaseQueue := by rw [IK5.2.2.1]; exact hnrT
  have I5' : Inv (ciSt σa t.bv xt) := ciSt_inv hkta I5 hnqT hnrT'
  have B5' : BlockedScActive (ciSt σa t.bv xt) := ciSt_bsa (Fr5.bsa J.bsa)
  have hcn : (ciSt σa t.bv xt).schedulerAction = .chooseNewThread :=
    (ciSt_actN (by rw [act5, hcn0]; intro h; cases h)).trans (act5.trans hcn0)
  have hidT : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle, ← hct]; exact fun e0 => hti e0.symm
  have hAI5 : ActIdle (ciSt σa t.bv xt) :=
    ⟨fun u hu => (by rw [hcn] at hu; cases hu), ciSt_idleOK hidT (Fr5.idleOK J.act.2)⟩
  have hrun5 : CurRunM (ciSt σa t.bv xt) := Or.inl (by rw [hcn]; intro h; cases h)
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by have := runnable_code hrn; omega)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX hdT hdth hkd hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σ umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D su _ (Endp.setUm σ umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkd (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  obtain ⟨V', J5⟩ := Ju.wake_postCI hkta hIR hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) I5' B5' hAI5
    (Or.inl hcn) hrun5 hRR htD hcD ⟨d', hdT, rfl⟩
  -- the tail
  have G := (ciSt_skD (σ := σa) (c := t.bv) (x := xt))
  have hk5 : (ciSt σa t.bv xt).kheap d'.bv = some (.tcb x5) := by
    rw [ciSt_kh (Ne.symm htd'), hσa, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ (ciSt σa t.bv xt).releaseQueue := by rw [ciSt_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → (ciSt σa t.bv xt).kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya : σa.kheap p = some (.schedContext y n) := by
      rw [← ciSt_kh (ciSt_ne hy (fun _ h => by cases h))]; exact hy
    have hy0 := SK5.2.2.2 p y n hya
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J.inv.back _ _ _ hkd hp'
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y n d'.bv xd hy0 hyt hkd (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ (ciSt σa t.bv xt).idleThread := by
    rw [G.idle, Fr5.sk.idle]
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ (ciSt σa t.bv xt).curThread := by rw [G.ct, Fr5.sk.ct]; exact hdc
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨hg, hr⟩
    rcases hno with ⟨rfl, rfl⟩ | hn
    · rcases hg with h | h <;> cases h
    · exact hr (hn xd hkd _ _ _ hstd)
  have hspec := sendIpc_faultInactive_eq (don := don) hk hkd hde htd' hstd blk badge.bv g gr hcond e2 hU hkt3 hkd3
    (by rw [hft]; simp) (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ =
      Endp.specWakeTailE d'.bv (ciSt σa t.bv xt) := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

set_option maxHeartbeats 64000000 in
/-- **A cap-faulted sender's `send_ipc` to a waiting receiver at `J` that
pushes a reply without a donation** (XTopJointSendPush's `JAtZ.sendCallPJ`
for `call = false` and a sender with a cap fault, running or restarting;
the transfer `do_ipc_transfer_capFJ`). Original docstring: (module docstring): the caller has the grant or grant-reply right
(`hg`), the receiver a reply object (`hrepn`), and the call does not donate or
the receiver has an SC (`hnd`); as `JAtZ.sendCallIJ` up to the reply unlink,
then `reply_push` on `IRel` (`reply_push_iG`, no donation), P1's
`reply_push.ipc` and `reply_push.nd`, the receiver `Running`, `JAtZ` by
`JAtZ.wake_postGR` at `pushSt` (`ps_swap`), the tail `JAtZ.sendTailJ`; the
spec's outcome `sendIpc_call_eq`. -/
theorem JAtZ.sendFaultPJN (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrn : Fl4Spec.runnable xt.tcbState = true) {cf : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure}
    (hft : xt.tcbFault = some (.capFault cf rp lf)) (hct : σ.curThread = t.bv)
    (hcn0 : σ.schedulerAction = .chooseNewThread) (hsc0 : xt.tcbSchedContext = none) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hg : g = true ∨ gr = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hnd : don = false ∨ ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none) :
    endpoint.send_ipc st arI s a blk false badge g gr don t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdc : d'.bv ≠ σ.curThread := by rw [hct]; exact Ne.symm htd'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, -, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have Fr1 : CFr e.bv d'.bv σ σ1 := CFr.upd hk (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hk (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (xferFaultStepJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) ht hdT htd hkt1 hkd1 hft e badge g
    hTP hdH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT hA2 (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xd b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  have Fr2 : CFr e.bv d'.bv σ σ2 := (Fr1.trans (CFr.um _ _ σ1 um2)).trans (CFr.upd (σ := Endp.setUm σ1 um2) hkd1
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans (IK.updSelf (σ := Endp.setUm σ1 um2) hkd1 hxsc))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((SKeep.um σ1 um2).trans (SKeep.updK (σ := Endp.setUm σ1 um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  obtain ⟨r, hrp⟩ := Option.ne_none_iff_exists'.1 (hrepn xd hkd _ _ _ hstd)
  subst hrp
  obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
  have hwR := hrepR (by simp)
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
  set w := L.mem s (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
  have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd]) hkr
  have hX2' := IpcRel.ofSRN hR2 hS2'
  have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
  obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
  rw [hrA] at hiR hit
  refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
      hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
    (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
        (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
      (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
  rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
  have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
    intro r hr er
    obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
    rw [er, hrA] at b2; rw [← b2]; exact z3
  set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
  set xr3 : Fl4Spec.Reply := { xr with replyTcb := none } with hxr3
  set σ3a := Notif.updK σ2 w.bv (.reply xr3) with hσ3a
  have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
  have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
  have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
    stsAct_ne hct3a
  set σ3 := Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv with hσ3
  have hU : Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) (some w.bv) σ2 =
      ({((), σ3)}, False) := e3
  have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply xr3) := by rw [stsAct_kheap]; simp [σ3a, hwd]
  have hq3 : ∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
    exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
  have Fr3 : CFr e.bv d'.bv σ σ3 := (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
    (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σ σ3 := by
    have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply xr3) hkr2 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
    exact IK3b.trans (IK.sts _ _ _)
  have SK3 : Ipc.SKeep σ σ3 :=
    ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
      (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans
      (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σ.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σ.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d' :=
    hX3.noref hdta (by rw [e3']; exact P1.inactive_ne.1) (by rw [e3']; exact P1.inactive_ne.2)
  have F3 := footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = fl4_abi.consts.fault.CapFault := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; rw [hfr.1]; unfold fl4_abi.consts.fault.CapFault; rfl
  have hks3 : L.ksb s3 = L.ksb s := hW3'.1
  -- the caller's and the receiver's words at `s3`
  have hnrT : t.bv ∉ σ.releaseQueue := J.inv.notRel_of_noSc hkt hsc0
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD : NotQueued σ d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hnqT3 : NotQueued σ3 t.bv := ⟨by rw [IK3.2.1]; exact hnq, by rw [IK3.2.2.1]; exact hnrT⟩
  have hnqD3 : NotQueued σ3 d'.bv := ⟨by rw [IK3.2.1]; exact hnqD.1, by rw [IK3.2.2.1]; exact hnqD.2⟩
  have bits3 : ∀ u ∈ Z.T, NotQueued σ3 u.bv →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hnu.2
      rw [hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT3
  obtain ⟨hqbD, hrbD⟩ := bits3 d' hdT hnqD3
  have ha1 : L.actionW s3 = 1#u64 := by
    have h := hSR3.act
    rw [hact3, hcn0] at h
    unfold P1.LawfulStore.actionW; rw [hcq3.cur]; exact h
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu h' => by
    rw [ha1] at h'; exact P1.notT_small hcq3.tcbs (by simp) (h' ▸ hu)
  have hcw3 : L.curW s3 = t := by
    have h : (nodeW st s3 Z.c layout.node.CUR_THREAD).bv = t.bv := by rw [← hs3.curThread, hct3, hct]
    unfold P1.LawfulStore.curW; rw [hcq3.cur]; exact P1.eq_of_bv h
  have hidl3 : σ3.idleThread = σ.idleThread := Fr3.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by rw [← hct]; exact hti
  have hid : d'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun h1 => by
    obtain ⟨x'', hk'', -, -, hscw', -⟩ := hs3.tcb t ht
    rw [hkt3] at hk''; cases hk''
    exact absurd (optRef_none (hscw'.symm.trans hsc0)) h1
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the receiver's SC: no donation
  have hndF : don = true → x3.tcbSchedContext = none → False := fun hdon hx0 => by
    rcases hnd with h | h
    · rw [h] at hdon; cases hdon
    · exact h xd hkd (by rw [← hsc3]; exact hx0)
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM d' hdT
  rw [hkd3] at hkd3'; cases hkd3'
  have hnd1 : don = false ∨ L.mem s3 (P1.scA d') ≠ 0#u64 := by
    cases don
    · exact Or.inl rfl
    · right; intro h0; exact hndF rfl (by rw [hdsc, h0, optRef_zero])
  -- the push on `IRel`, at P1
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hns3 : tsCode xt.tcbState ≠ 6 := by have := runnable_code hrn; omega
  have hPush : ipc.reply_push st arI s3 a t d' w don ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv don σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1 ⦄ := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := don) (P := fun s' σ' => σ' = pushSt σ3 t.bv w.bv xr3 xt ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hdon _ _ _ _ _ _ _ hx0 => (hndF hdon hx0).elim))
      (P1.ipc.reply_push.ipc hAT s3 a t d' w don Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hqbD hrbD (hna3 d' hdT) (hiw3 d' hdT hid) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a t d' w don h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hcA hnd1)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, hb2, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hb2, hf, hsb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv don σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1) ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.CapFault fl4_abi.consts.fault.NullFault; decide)]
    rcases hg with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]; exact hPush
    · cases g <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true] <;> exact hPush
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, ⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4', hSg4⟩, hst4, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 h4 hB4 hX4 hS4' hSg4 hst4 fu4 hsb4 ⊢
  subst ha4
  try dsimp only
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 ht hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3 (SzKeepC.of Fr3.szKeep) hb))
  have hks4 : L.ksb s4 = L.ksb s := hW4'.1
  set σ4 := pushSt σ3 t.bv w.bv xr3 xt with hσ4
  have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z ((ps_oth hkt3 hkr3 hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hz)
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hst4d : L.mem s4 (P1.stA d') = sched.TS_INACTIVE := by rw [hst4 d' hdH (Ne.symm htd)]; exact e3'
  have hx4 : d' ∈ (∅ : Set U64) ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := Or.inr (by rw [hst4d]; exact P1.not_blocked_inactive)
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' :=
    hX4.noref hdta (by rw [hst4d]; exact P1.inactive_ne.1) (by rw [hst4d]; exact P1.inactive_ne.2)
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4
      (by simp [x3, tsCode]) .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q4 R4 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK σ4 d'.bv (.tcb x5)) d'.bv = pushSt σa t.bv w.bv xr3 xt :=
    ps_swap htd' hwd hdc3
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 (pushSt σa t.bv w.bv xr3 xt) := by
    rw [← heq5]; exact hIR0
  have hW5' : P1.WritesIn st s s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q4, R4, h5.congrX P1.empty_congr⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have hrb3 : RbIn x3.tcbState := Or.inr rfl
  have Fr5 : CFr e.bv d'.bv σ σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σ (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σ σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : Ipc.SKeep σ σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σa.schedulerAction = σ.schedulerAction := by
    rw [hσa, stsAct_ne (by show d'.bv ≠ σ3.curThread; exact hdc3)]; exact hact3
  -- the push after the wake (`ps_swap`)
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hkwa : σa.kheap w.bv = some (.reply xr3) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, hwd, hkr3]
  have hnqT : ∀ dm p, t.bv ∉ σa.readyQueues dm p := by rw [IK5.2.1]; exact hnq
  have hnrT' : t.bv ∉ σa.releaseQueue := by rw [IK5.2.2.1]; exact hnrT
  set σ' := pushSt σa t.bv w.bv xr3 xt with hσ'
  have I5' : Inv σ' := ps_inv hkta hkwa hwt I5 hnqT hnrT'
  -- an SC bound to the caller is the current SC, active
  have hscA : ∀ p y n, σa.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    have hp0 : σ.kheap p = some (.schedContext y n) := SK5.2.2.2 _ _ _ hp
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp0
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp0).2⟩
    have hS := J.xtop.fin.1.1.1
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
    rw [hkt] at hku; cases hku
    rw [hsc0] at hxs; cases hxs
  have B5' : BlockedScActive σ' := ps_bsa hkta hkwa hwt hscA (Fr5.bsa J.bsa)
  have hcn : σ'.schedulerAction = .chooseNewThread :=
    (ps_actN (by rw [act5, hcn0]; intro h; cases h)).trans (act5.trans hcn0)
  have hidT : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle, ← hct]; exact fun e0 => hti e0.symm
  have hAI5 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hcn] at hu; cases hu), ps_idleOK hkta hkwa hwt hidT (Fr5.idleOK J.act.2)⟩
  have hrun5 : CurRunM σ' := Or.inl (by rw [hcn]; intro h; cases h)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by have := runnable_code hrn; omega)
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := hR.reply w hwR
    rw [hkr] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hkq : ∀ q ∈ D, σ'.kheap q.bv = σa.kheap q.bv := fun q hq => ps_ko (hcD q hq) (hwD q hq)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX hdT hdth hkd hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σ umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D su _ (Endp.setUm σ umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkd (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σa.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hwt h1 h2
  obtain ⟨V', J5⟩ := Ju.wake_postGR hIR hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) ps_skD
    (ps_ksub hkta hkwa hwt) (ps_szKeep hkta hkwa hwt) (ps_ykeep hkta hkwa hwt) (ps_mcpKeep hkta hkwa hwt)
    (ps_bufKeep hkta hkwa hwt) (fun d _ h => ps_recvB hkta hkwa hwt h) (ps_ksz hkta hkwa hwt)
    (ps_kback hkta hkwa hwt) (ps_ipcFr hkta hkwa hwt) (ps_ck hkta hkwa hwt) (fun d _ h => ps_free hkta hkwa hwt h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I5' B5' hAI5 (Or.inl hcn) hrun5 (ps_own hkta hkwa hwt ((DWFr.ofCFr Fr5).own ⟨d', hdT, rfl⟩ J.own))
    (ps_off hkta hkwa hwt ((DWFr.ofCFr Fr5).off J.off)) (ps_nsc hkta hkwa hwt ((DWFr.ofCFr Fr5).nsc J.nsc))
    (ps_isorted hkta hkwa hwt ((DWFr.ofCFr Fr5).isorted J.isorted)) hRR htD
  -- the tail
  have hk5 : σ'.kheap d'.bv = some (.tcb x5) := by
    rw [ps_ko (Ne.symm htd') (Ne.symm hwd), hσa, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ'.releaseQueue := by rw [ps_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ'.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya : σa.kheap p = some (.schedContext y n) :=
      (ho (fun _ h => by cases h) (fun _ h => by cases h)).1 hy
    have hy0 := SK5.2.2.2 p y n hya
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J.inv.back _ _ _ hkd hp'
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y n d'.bv xd hy0 hyt hkd (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ'.idleThread := by
    rw [(ps_skD (σ := σa) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).idle, Fr5.sk.idle]
    exact hid
  have htc5 : d'.bv ≠ σ'.curThread := by
    rw [(ps_skD (σ := σa) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).ct, Fr5.sk.ct]; exact hdc
  have hspec := sendIpc_faultPush_eq (don := don) hk hkd hde hstd blk badge.bv g gr hg e2 hU hkt3 hkd3 hpush hkd4 (by rw [hft]; simp)
    (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ =
      Endp.specWakeTailE d'.bv σ' := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

set_option maxHeartbeats 64000000 in
/-- **`handle_fault` with an endpoint handler and a waiting receiver at `J`,
with or without a receive buffer** (module docstring): XTopJointFaultEp's
`JAtZ.faultBlockJ` up to the handler cap, then `set_fault` at `J`
(`JAtZ.setFaultCapJ`) and the send to the receiver: `JAtZ.sendFaultIJ` (no
reply right or no reply object: the sender `Inactive`), `JAtZ.sendFaultPJ`
(the reply pushed, no donation: `can_donate` false or the receiver with an
SC), `JAtZ.sendFaultPDJ` (the reply pushed and the sender's SC donated). -/
theorem JAtZ.faultRecvJN (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hni : MidN σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {ptr bdg : U64} {sd rv g gr : Bool}
    (hep : capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok (.Endpoint ptr bdg sd rv g gr))
    {d : U64} {q : List Fl4Spec.ObjRef} (hkq : σ.kheap ptr.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩ := hf
  obtain ⟨⟨lt, l0, l1⟩, he, -⟩ := spec_exists (encode_lfRel hlf)
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have hrn : Fl4Spec.runnable x.tcbState = true := hni.run x (by rw [hcur]; exact hk)
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have ht : ct ∈ Z.T := by rw [hct']; exact hcq.curT
  have hta := hP0.e.tcb ct ht
  have htH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct ht
  have htD : ct ∉ D := fun h => J.notDead ht hk (by have := runnable_code hrn; omega) ct h rfl
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  have hnr : ct.bv ∉ σ.releaseQueue := J.inv.notRel_of_noSc hk (hni.2.2.2 _ (by rw [hcur]; exact hk))
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  have hidt : σ.idleThread ≠ ct.bv := fun e => hti (by rw [hcur, e])
  -- the handler cap, its endpoint
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have e1 : c1 = .Endpoint ptr bdg sd rv g gr := by rw [hep] at hc1; simpa using hc1.symm
  subst e1
  have habs := hcr.2
  simp only [absCap] at habs
  have hfh : x.tcbFaultHandler = .endpointCap ptr.bv bdg.bv (rightsOf sd rv g gr) := habs.symm
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : ptr ∈ Z.E := J.slotE hAS hep
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  have hpt : ptr.bv ≠ ct.bv := fun e => by rw [e, hk] at hke; cases hke
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s _) hAS.isSlot hep (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have hcbP : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := J.canBlockCurMN ht hcur hk hrn hti hnr hni hnq
  -- the spec's donation flag is FL4's
  obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb ct ht
  rw [hk] at hkt6; cases hkt6
  have hdon : (L.mem s (scA ct) != 0#u64) = decide (x.tcbSchedContext ≠ none) := by
    rw [hsct6]
    by_cases h0 : L.mem s (scA ct) = 0#u64
    · simp [h0, Notif.optRef]
    · simp [h0, Notif.optRef]
  -- `handle_fault`: the handler cap
  unfold faults.handle_fault
  rw [tcb_slot_fault]
  apply ok_bind_spec
  rw [slot_cap_eq, hep]
  apply ok_bind_spec
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => r.1 = true ∧
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault a0.bv rp lf') σ).1,
      RelTopM (L := L) r.2.1 z.2 ∧ JAt (L := L) arI AR r.2.1 r.2.2 z.2) ?_ ?_
  swap
  · rintro ⟨b0, s2, a2⟩ ⟨hb, hr0⟩
    simp only at hb hr0
    subst hb
    exact (WP.spec_ok _).2 hr0
  unfold faults.send_fault_ipc
  dsimp only
  -- `set_fault`
  set f' : Fl4Spec.Fault := .capFault a0.bv rp lf' with hf'
  set x2 : Fl4Spec.Tcb := { x with tcbFault := some f' } with hx2
  set σf := updK σ ct.bv (.tcb x2) with hσf
  -- `set_fault` at `J`
  refine WP.spec_bind (J.setFaultCapJ ht hk (fun e0 d0 h => by
      have := runnable_code hrn; rw [h] at this; simp [tsCode] at this) hcbP ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩) ?_
  rintro s7 ⟨V, J7, -⟩
  have hkf : σf.kheap ct.bv = some (.tcb x2) := by simp [hσf, updK]
  have hkfp : ∀ q, q ≠ ct.bv → σf.kheap q = σ.kheap q := by
    intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']
  have hkef : σf.kheap ptr.bv = some (.endpoint (.recvEP (d.bv :: q))) := by rw [hkfp _ hpt]; exact hkq
  have hnb0 : tsCode x.tcbState ≠ 3 ∧ tsCode x.tcbState ≠ 4 := by
    have := runnable_code hrn; omega
  have htq : ct.bv ∉ (Fl4Spec.Endpoint.recvEP (d.bv :: q)).epQueue :=
    Endp.not_queued hI.1.toE ht hk hnb0 ptr hpE _ hkq
  have hdc : d.bv ≠ ct.bv := fun e0 => htq (by rw [← e0]; simp [Fl4Spec.Endpoint.epQueue])
  have hsf : x2.tcbSchedContext = none := by rw [hx2]; exact hni.2.2.2 x (by rw [hcur]; exact hk)
  have hpost : ∀ don : Bool, don = false → endpoint.send_ipc st arI s7 a true false bdg g gr don ct ptr ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr don ct.bv ptr.bv σf).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
    intro don hd0
    by_cases hgg : g = true ∨ gr = true
    · by_cases hA : ∀ xd, σf.kheap d.bv = some (.tcb xd) → ∀ e' rep dd,
          xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
      · by_cases hS : don = false ∨ ∀ xd, σf.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none
        · exact J7.sendFaultPJN hAT ht hkf hrn rfl hcur hni.2.2.1 hsf hti hnq' hpE hkef true bdg g gr don hgg hA hS
        · exact absurd (Or.inl hd0) hS
      · refine J7.sendFaultIJN ht hkf hrn rfl hcur hni.2.2.1 hsf hti hnq' hpE hkef true bdg g gr don (Or.inr ?_)
        intro xd hxd e' rep dd hst
        by_contra hne
        apply hA
        intro xd' hxd' e'' rep' dd' hst'
        rw [hxd] at hxd'; cases hxd'
        rw [hst] at hst'; cases hst'; exact hne
    · exact J7.sendFaultIJN ht hkf hrn rfl hcur hni.2.2.1 hsf hti hnq' hpE hkef true bdg g gr don
        (Or.inl ⟨Bool.eq_false_iff.2 fun h => hgg (Or.inl h), Bool.eq_false_iff.2 fun h => hgg (Or.inr h)⟩)
  have hd0 : (L.mem s (scA ct) != 0#u64) = false := by
    rw [hdon, hni.2.2.2 x (by rw [hcur]; exact hk)]; simp
  refine WP.spec_bind (hpost _ hd0) ?_
  rintro ⟨s', a'⟩ ⟨z, hz, hJ⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ?_⟩
  have hz' : z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
      (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
      (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) (decide (x.tcbSchedContext ≠ none)) ct.bv
      ptr.bv (updK σ ct.bv (.tcb { x with tcbFault := some f' }))).1 := by
    rw [rights_grant, rights_grantReply, ← hdon]; exact hz
  obtain ⟨Z', H', Cs', Ac', Lst', D', J'⟩ := hJ
  exact ⟨((), z.2), handleFault_ep_mem hk hfh _ hz',
    ⟨_, _, J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
    ⟨_, _, _, _, _, _, J'⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`handle_fault` at a reschedule mid state with ct SC-less, every case** (module
docstring; `JAtZ.faultHypJZ`'s case split, the waiting receiver by
`JAtZ.faultRecvJN`). -/
theorem JAtZ.faultHypJZN (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAtR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have hv : Fl4Spec.validFaultHandler (absCap c1) := by
    rw [hcr.2]; exact hvfh x (by rw [hcur]; exact hk)
  by_cases hn : c1 = .Null
  · subst hn
    exact J.noFaultJN hni hsw hct hnq hc1 f f'
  obtain ⟨p, b, sd, rv, g, gr, rfl⟩ := vfh_ep hv hn
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : p ∈ Z.E := J.slotE hAS hc1
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xe, hke, -⟩ := hI.1.ep p hpE
  cases xe with
  | recvEP l =>
    obtain ⟨-, xs, hxs0, hq, -⟩ := hI.1.toE.at_ep hpE hke
    obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons] at hq
    subst hq
    refine WP.spec_mono (J.faultRecvJN hAT hni hct hnq hc1 hke hf) ?_
    rintro r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩
    exact ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  | idleEP =>
    exact J.faultBlockJN hni hsw hct hnq hc1 (fun xe h => by rw [hke] at h; cases h; trivial) hf
  | sendEP q =>
    exact J.faultBlockJN hni hsw hct hnq hc1 (fun xe h => by rw [hke] at h; cases h; trivial) hf

end

end

end Fl4Proofs.P3
