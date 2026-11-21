/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch20): **the cap
fault of `handle_recv` at a `chooseNewThread` mid state with `CurInv`, for a
null fault handler and an endpoint handler with no waiting receiver.**
Scripted copies (sch20gen/gen.py fault) of XTopJointFaultM's switch-mid
lemmas with `MidC` (XTopJointRecvSigC) for `MidE`: `JAtZ.stsCurJC`,
`JAtZ.noFaultJC`, `JAtZ.faultBlockJC` (`CurInv` from `MidC`,
`canBlockCurMC`, "the switch target is not ct" closed by the action being
`chooseNewThread`), `FltRecv σ` (ct's fault handler is an endpoint with a
waiting receiver: `faultRecvJ`'s case, not covered here) and
`JAtZ.faultHypJZC`: `handle_fault` at a `MidC` state outside `FltRecv`.
-/
import Fl4Proofs.P3.XTopJointFaultM
import Fl4Proofs.P3.XTopJointRecvSigC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **ct's fault handler is an endpoint with a waiting receiver** (module
docstring). -/
def FltRecv (σ : Fl4Spec.State Unit) : Prop :=
  ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
    ∃ p bd r, x.tcbFaultHandler = .endpointCap p bd r ∧ ∃ l, σ.kheap p = some (.endpoint (.recvEP l))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}


set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Inactive` of the current thread at `J` under a
pending reschedule (with `CurInv`)** (module docstring). -/
theorem JAtZ.stsCurJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidC σ)
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
  have hCI : CurInv σ := hni.2.2.2
  have hnr : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hCI.notRel
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
theorem JAtZ.noFaultJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidC σ)
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
  have hCI : CurInv σ := hni.2.2.2
  have hnr : ct.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hCI.notRel
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
  refine WP.spec_bind (J.stsCurJC hni hsw hT hD hk hcur hrn hnq' hB) ?_
  rintro s6 ⟨Lst', J6⟩
  refine (WP.spec_ok _).2 ⟨_, by rw [hspec]; exact Set.mem_singleton _,
    ⟨Z.th, Z.G, J6.xtop.rel.1, J6.xtop.rel.2.1, J6.xtop.rel.2.2.1, J6.xtop.rel.2.2.2.1, J6.xtop.rel.2.2.2.2.1⟩,
    ⟨Z, H, Cs, Ac, Lst', D, J6⟩⟩

set_option maxHeartbeats 64000000 in
/-- **`handle_fault` with an endpoint handler and no waiting receiver at
`J` under a pending reschedule (with `CurInv`)** (module docstring). -/
theorem JAtZ.faultBlockJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidC σ)
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
  have hC : CurInv σ := hni.2.2.2
  have hnr : ct.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
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
  have hcbP : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := J.canBlockCurMC ht hcur hk hrn hti hnr hni hnq
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
    obtain ⟨xc, hkc, hcs, -⟩ := hC.tcb
    rw [hcur, hk] at hkc; cases hkc
    have e1 : σ.curSc = q.bv := Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
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

set_option maxHeartbeats 4000000 in
/-- **`handle_fault` at a reschedule mid state outside `FltOpen`** (module
docstring; `JAtZ.faultHypJZ`'s case split). -/
theorem JAtZ.faultHypJZC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidC σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hfo : ¬ FltRecv σ)
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
    exact J.noFaultJC hni hsw hct hnq hc1 f f'
  obtain ⟨p, b, sd, rv, g, gr, rfl⟩ := vfh_ep hv hn
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : p ∈ Z.E := J.slotE hAS hc1
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xe, hke, -⟩ := hI.1.ep p hpE
  cases xe with
  | recvEP l =>
    exact absurd ⟨x, by rw [hcur]; exact hk, p.bv, _, _, hcr.2.symm, l, hke⟩ hfo
  | idleEP =>
    exact J.faultBlockJC hni hsw hct hnq hc1 (fun xe h => by rw [hke] at h; cases h; trivial) hf
  | sendEP q =>
    exact J.faultBlockJC hni hsw hct hnq hc1 (fun xe h => by rw [hke] at h; cases h; trivial) hf

end

end

end Fl4Proofs.P3
