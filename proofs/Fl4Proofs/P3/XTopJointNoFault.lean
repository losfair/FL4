/-
P3 (DESIGN.md §9), IPC: **`handle_fault` with no fault handler at `J`**
(`JAtZ.noFaultJ`; toward `JEntryHyps.lookupFault` / `extraLookup`).

FL4's `faults::handle_fault` with a null cap in the thread's fault-handler
slot: `send_fault_ipc` returns `false` without writing, then
`set_thread_state Inactive` (no fault stored, as seL4's
`handleNoFaultHandler`); the spec's `handleFault`: `sendFaultIpc nullCap` is
`return false`, then `handleNoFault` = `setThreadState Inactive`.

* `sched.set_thread_state.inactive_blkR` (P1): `set_thread_state Inactive`
  of a thread that is neither blocked nor queued (ready or release) nor the
  switch target keeps `BlkOK`, with the footprint (`sts_all`).
* `JAtZ.curBits`: a TCB in neither the spec's ready queues nor its release
  queue has FL4's `Q_QUEUED` and `Q_RELEASE` bits clear (`SchedCore.queued`,
  `.released`, `SchedSpec.rq`, `.rel`).
* `JAtZ.stsCurJ`: XTopJointStsI's `JAtZ.stsIJ` for the current, runnable
  thread at a system call (`Entered`: the action `resumeCurThread`, so
  `set_thread_state` asks for a reschedule, `chooseNewThread`), made
  `Inactive`; the thread in no ready queue is the premise `hnq` (l4v
  `ct_not_in_q`), the release queue by `CurInv.notRel`.
* `handleFault_null`: the spec side; `JAtZ.noFaultJ`: the whole
  `handle_fault` at `J`.
* `faultHypJ`: `FaultHypAtMX` at `JAt` from the endpoint-handler case
  (`FaultEpHypJ`, the blocking `send_ipc`), `Entered`, l4v `ct_not_in_q` and
  l4v `valid_fault_handler` for the current thread (a cap that is neither
  null nor an endpoint is excluded).
-/
import Fl4Proofs.P3.XTopJointStsI
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`set_thread_state Inactive` of an unqueued, unblocked thread keeps
`BlkOK`**, with the footprint of `set_thread_state`. -/
theorem sched.set_thread_state.inactive_blkR (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hnb : ¬ Blocked (L.mem s (stA t))) (hnrp : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hnr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hna : L.actionW s ≠ t) :
    sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_inactive inactive_ne
    (Or.inr hnb) (hX.noref (h0.tcbs t ht) hnrp (fun e => hnb (Or.inr (Or.inl e))))
    ⟨fun c hc' p hp hm => absurd hm (h0.notQ ht hnq hc' hp), fun c hc' hm => absurd hm (h0.notR ht hnr hc'),
      fun e => absurd e hna⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, f1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩, f1⟩

/-- A state word of a runnable thread (`Running`, `Restart`, `RunningVM`) is
not blocked and not `BlockedOnReply`. -/
theorem run_word {w : U64} (hv : w.val = 1 ∨ w.val = 2 ∨ w.val = 8) :
    ¬ Blocked w ∧ w ≠ sched.TS_BLOCKED_ON_REPLY := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  refine ⟨?_, ?_⟩
  · unfold Blocked; rw [h3, h4, h6]
    rintro (h | h | h) <;> rw [h] at hv <;> revert hv <;> decide
  · rw [ts_reply]; intro h; rw [h] at hv; revert hv; decide

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- The code of a runnable state. -/
theorem runnable_code {ts : Fl4Spec.ThreadState} (h : Fl4Spec.runnable ts = true) :
    tsCode ts = 1 ∨ tsCode ts = 2 ∨ tsCode ts = 8 := by
  cases ts <;> simp_all [Fl4Spec.runnable, tsCode]

/-- A runnable state is IPC-free. -/
theorem runnable_free {ts : Fl4Spec.ThreadState} (h : Fl4Spec.runnable ts = true) : IpcFree ts := by
  cases ts with
  | running => exact ⟨rfl, rfl, fun _ e => nomatch e⟩
  | restart => exact ⟨rfl, rfl, fun _ e => nomatch e⟩
  | runningVM => exact ⟨rfl, rfl, fun _ e => nomatch e⟩
  | _ => simp [Fl4Spec.runnable] at h

section Spec
open Fl4Spec

/-- **l4v `handle_fault` with a null fault handler**: `handle_no_fault`, the
thread `Inactive`. -/
theorem handleFault_null {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hc : x.tcbFaultHandler = .nullCap) (ex : Fault) :
    handleFault (Z := Unit) t ex σ =
      ({((), stsAct (updK σ t (.tcb { x with tcbState := .inactive })) t)}, False) := by
  unfold handleFault getTcbFaultHandlerPtr
  have hg : getCap (Z := Unit) (t, tcbCnodeIndex 3) σ = ({(.nullCap, σ)}, False) := by
    rw [getCap_tcb_three hk, hc]
  rw [nd_pure_bind', nd_bind_one hg, nd_bind_one (threadGet_eq _ hk)]
  unfold sendFaultIpc
  dsimp only
  rw [nd_pure_bind']
  simp only [NonDet.unless, handleNoFault, Bool.false_eq_true, ↓reduceIte]
  rw [nd_bind_one (Notif.setThreadState_eq .inactive hk)]
  rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The queue bits of a thread in no spec queue** (module docstring). -/
theorem JAtZ.curBits (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hq : ∀ d p, t.bv ∉ σ.readyQueues d p) (hr : t.bv ∉ σ.releaseQueue) :
    (L.mem s (P1.inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
  · have hm := (hc.queued t ht).1 h
    apply hq 0 (specPrio (L.mem s (P1.prioA t)))
    rw [hs.rq _ (hc.prio t ht)]
    exact List.mem_map_of_mem hm
  · have hm := (hc.released t ht).1 h
    apply hr
    rw [hs.rel]
    exact List.mem_map_of_mem hm

set_option maxHeartbeats 16000000 in
/-- **`set_thread_state Inactive` of the current thread at `J`** (module
docstring). -/
theorem JAtZ.stsCurJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {t : U64} (ht : t ∈ Z.T)
    (htD : t ∉ D) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hcur : σ.curThread = t.bv)
    (hrn : Fl4Spec.runnable x.tcbState = true) (hnq : ∀ d p, t.bv ∉ σ.readyQueues d p)
    (hB : sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄) :
    sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s6 a
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
  have hCI : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
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
  have hcn : σ6.schedulerAction = .chooseNewThread := by
    have h3 : ¬ Fl4Spec.schedulable t.bv σ1 = true := fun h => by
      obtain ⟨y, _, _, _, hky, _, hr, _⟩ := schedulable_inv h
      rw [hk1] at hky; cases hky; simp [hx6, Fl4Spec.runnable] at hr
    have h12 : t.bv = σ1.curThread ∧ σ1.schedulerAction = .resumeCurThread ∧
        ¬ Fl4Spec.schedulable t.bv σ1 = true :=
      ⟨hcur.symm, hni.2, h3⟩
    rw [hσ6]; unfold stsAct; rw [if_pos h12]
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
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [hcn] at hu; cases hu
    · obtain ⟨y, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨y, by rw [e_idle, hkp _ hidt]; exact h1, by rw [e_isc]; exact h2, h3, by rw [e_idle, e_rel]; exact h4⟩
  have hoff : OffOK σ6 := by
    intro h0 y n hy ha
    rw [e_cons] at h0 ⊢; rw [e_tm]; rw [e_csc] at hy; rw [e_csc, e_isc] at ha
    by_cases e : σ.curSc = t.bv
    · rw [e, hk6] at hy; cases hy
    · rw [hkp _ e] at hy; exact J.off h0 y n hy ha
  have hcur6 : σ6.schedulerAction = .chooseNewThread ∨ CurInv σ6 := Or.inl hcn
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
  have hcr6 : CurRunM σ6 := Or.inl (by rw [hcn]; intro e; cases e)
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

/-- FL4's and the spec's fault-handler slot of a related TCB. -/
theorem fhCap_rel {th : TypedHeap} {m : U64 → U64} {σ' : Fl4Spec.State Unit} (hR : StateRel th m σ') {t : U64}
    (ht : th t = some .tcb) :
    ∃ x c, σ'.kheap t.bv = some (.tcb x) ∧ capAt m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = ok c ∧
      CapRel c x.tcbFaultHandler := by
  obtain ⟨x, hkx, hsl⟩ := hR.tcb t ht
  obtain ⟨c, ac, hc, hac, hca⟩ := hsl 3 (by decide)
  have h3 : Fl4Spec.tcbCnodeMap x (Fl4Spec.tcbCnodeIndex 3) = some x.tcbFaultHandler := by
    unfold Fl4Spec.tcbCnodeMap
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  rw [h3] at hac
  cases hac
  have he : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3) = slotOf t 3 := by
    show slotAddr t.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal 3 (by decide)]
  exact ⟨x, c, hkx, by rw [he]; exact hc, hca⟩

set_option maxHeartbeats 8000000 in
/-- **`handle_fault` with a null fault handler at `J`** (module docstring). -/
theorem JAtZ.noFaultJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hnull : capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok .Null)
    (f : error.Fault) (f' : Fl4Spec.Fault) :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, x, hk, hrn⟩ := J.curRunnable hni hct
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
  have hCI : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hnr : ct.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hCI.notRel
  obtain ⟨bq, br⟩ := J.curBits hT hnq' hnr
  obtain ⟨hna, -⟩ := J.words_of_spec hT (fun u hu => by rw [hni.2] at hu; cases hu)
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
  refine WP.spec_bind (J.stsCurJ hni hT hD hk hcur hrn hnq' hB) ?_
  rintro s6 ⟨Lst', J6⟩
  refine (WP.spec_ok _).2 ⟨_, by rw [hspec]; exact Set.mem_singleton _,
    ⟨Z.th, Z.G, J6.xtop.rel.1, J6.xtop.rel.2.1, J6.xtop.rel.2.2.1, J6.xtop.rel.2.2.2.1, J6.xtop.rel.2.2.2.2.1⟩,
    ⟨Z, H, Cs, Ac, Lst', D, J6⟩⟩

/-- **[W] The fault handler at `JAt` when the faulting thread's
fault-handler slot holds an endpoint cap**: FL4's `set_fault` then the
blocking `send_ipc` to the handler against the spec's `threadSet` of the
fault then `sendIpc` (XTopJointIpcJ's `JSendRestHyp` machinery; the
par/sendj line). The other handler caps are proved (`faultHypJ`). -/
def FaultEpHypJ (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) (f : error.Fault)
    (f' : Fl4Spec.Fault) : Prop :=
  (∃ p b sd rv g gr, capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok (.Endpoint p b sd rv g gr)) →
    FaultHypAtMX (L := L) arI (JAt (L := L) arI AR) s σ ct f f'

/-- **`FaultHypAtMX` at `JAt`** (module docstring): a null handler by
`JAtZ.noFaultJ`, an endpoint by `hep`, any other cap excluded by l4v
`valid_fault_handler` (`hvfh`). -/
theorem faultHypJ (s : S) (σ : Fl4Spec.State Unit) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct)
    (hnq : σ.schedulerAction = .resumeCurThread → ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (f : error.Fault) (f' : Fl4Spec.Fault) (hep : FaultEpHypJ (L := L) (arI := arI) AR s σ ct f f') :
    FaultHypAtMX (L := L) arI (JAt (L := L) arI AR) s σ ct f f' := by
  intro a hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have hv : Fl4Spec.validFaultHandler (absCap c1) := by
    rw [hcr.2]; exact hvfh x (by rw [hcur]; exact hk)
  by_cases hn : c1 = .Null
  · subst hn
    exact J.noFaultJ hni hct (hnq hni.2) hc1 f f'
  · obtain ⟨e, b, x1, x2, x3, x4, rfl⟩ := vfh_ep hv hn
    exact hep ⟨e, b, x1, x2, x3, x4, hc1⟩ a ⟨Z, H, Cs, Ac, Lst, D, J⟩

end

end

end Fl4Proofs.P3
