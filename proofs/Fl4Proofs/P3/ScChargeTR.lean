/-
P3 (DESIGN.md §9), scheduling contexts: **the preemption path's charge with
the current thread's timeout fault sent to a receiver waiting on its
handler's endpoint** (KENTRY-PLAN kp17 (2)): scripted copies (suffix `R`) of
ScChargeTA's `JTH.endTimesliceTmoJA`, `JHole.chargeBudgetTmoJA`,
`JHole.checkBudgetTA` and XTopJointPreemptA's `JHole.mcsPPJA`, with the
handler endpoint receiving (`hkl`) in place of idle/sending (`hcb`), the
send ScTmoCtRecv's `JTH.tmoRecvJ` in place of `JTH.tmoBlockJA`, and the
platform facts `hmax`/`htu` [P] (as XTopJointFaultTmo's `runTmoP_recv`).
-/
import Fl4Proofs.P3.ScTmoCtRecv
import Fl4Proofs.P3.XTopJointPreemptA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`end_timeslice` with `can_timeout_fault = true` at a `JTH` state, the
current thread with an endpoint timeout handler on an idle or sending
endpoint and a non-round-robin SC**: both sides take the timeout-fault branch
(`handle_timeout` of the current thread with the SC's badge), then
`JTH.tmoBlockJ`. -/
theorem JTH.endTimesliceTmoJR {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {t : U64} (ht : t ∈ Z.T)
    (htc : t.bv = σ.curThread) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrr : x.tcbState = .running ∨ x.tcbState = .restart)
    {sc : U64} (hsc : sc ∈ Z.C) (hcs : σ.curSc = sc.bv) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) (hper : y.scPeriod ≠ 0)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : x.tcbTimeoutHandler = .endpointCap p bd r)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l)))
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread) (hnq : NotQueued σ t.bv) (hidt : σ.idleThread ≠ t.bv) :
    sched.end_timeslice st arI s a true ⦃ res => ∃ z ∈ (Fl4Spec.endTimeslice (Z := Unit) true σ).1,
      ∃ (V : XVs) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D' res.1 res.2 z.2 ⦄ := by
  have J := Hj.j0
  have hS := Hj.xtop.fin.1.1.1
  have hR := Hj.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have ect : nodeW st s Z.c layout.node.CUR_THREAD = t := P1.eq_of_bv (by rw [← hs.curThread]; exact htc.symm)
  have ecs : nodeW st s Z.c layout.node.CUR_SC = sc := P1.eq_of_bv (by rw [← hs.curSc]; exact hcs)
  obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
  rw [hky] at hky'; cases hky'
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th t = some .tcb := (hJ.tcb _).2 (J.zH.1 _ ht)
  have hvm : x.tcbState ≠ .runningVM := by rcases hrr with e | e <;> rw [e] <;> intro h <;> cases h
  -- the spec: the timeout-fault branch
  have hspec : Fl4Spec.endTimeslice (Z := Unit) true σ =
      Fl4Spec.handleTimeout t.bv (.timeout (L.mem s (scW sc 48#u64)).bv) σ := by
    unfold Fl4Spec.endTimeslice
    rw [nd_gets_bind, hcs, nd_bind_one (isRoundRobin_eq hky), nd_gets_bind, ← htc,
      nd_bind_one (getThreadState_eq hk)]
    simp only [hvm, ↓reduceIte]
    rw [nd_bind_one (Endp.isValidTimeoutHandler_eq hk), hth, if_pos, nd_bind_one (getSchedContext_eq hky),
      hy'.badge]
    simp [Fl4Spec.isEpCap]
    exact hper
  -- FL4: the reads
  have hval := hval_of_rel Hj.xtop.rel.1 Hj.xtop.rel.2.1.1 hthc s σ (TmoKeep.refl _ _ _)
  obtain ⟨tx, hkt, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have hst := (hR.at_tcb ht hk).st
  have hnvm : (L.mem s (tStA t) != sched.TS_RUNNING_VM) = true := by
    have e8 : sched.TS_RUNNING_VM = 8#u64 := by unfold sched.TS_RUNNING_VM; rfl
    rw [bne_iff_ne, e8]
    intro e
    rw [e] at hst
    rcases hrr with e' | e' <;> rw [e'] at hst <;> simp [tsCode] at hst
  unfold sched.end_timeslice
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur, ecs] at hsc'
  rw [hc.cur, ect] at hct'
  subst hsc' hct'
  step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
  have hrr0 : rr = false := by
    rw [hrr']
    apply decide_eq_false
    intro e
    exact hper (by rw [hy'.period, e]; rfl)
  subst hrr0
  step with Notif.obj.Tcb.state.spec as ⟨i, hi⟩
  rw [hi, if_pos hnvm]
  refine WP.spec_bind hval ?_
  intro v hv
  have hv' : v = true := by
    rw [Endp.isValidTimeoutHandler_eq hk, hth] at hv
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hv).1)).1).symm
  subst hv'
  simp only [↓reduceIte, Bool.false_eq_true]
  step with obj.Sc.badge.spec' as ⟨bd', hbd'⟩
  subst hbd'
  refine WP.spec_mono (Hj.tmoRecvJ hAT hmax htu ht htc hk hrr hsc hxsc hcs.symm hky hya hth hkl hres hnq hidt _) ?_
  rintro res ⟨z, hz, V, Lst', D', J'⟩
  exact ⟨z, by rw [hspec]; exact hz, V, Lst', D', J'⟩


set_option maxHeartbeats 64000000 in
/-- **`charge_budget` with `can_timeout_fault = true` from a `JHole`, the
current thread's timeout fault blocking it** (module docstring): the current
thread (`Running` or `Restart`, not queued, the action `ResumeCurThread`) has
an endpoint cap as its timeout handler whose endpoint is idle or sending, and
its SC is not round-robin. The head charge at the hole (SchedRel-level
`charge_head_refinesK`, P1's `charge_head.ring`/`charge_pre_post`), the
consumed-time reset, the `JTH` state there (`ScOnly` from the base), then
`end_timeslice` (`JTH.endTimesliceTmoJ`), `reschedule_required`
(`JAtZ.reschedJ`) and the reprogram flag (`JAtZ.reprogramJ`) at `J`. -/
theorem JHole.chargeBudgetTmoJR {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l))) (used : U64) :
    sched.charge_budget st arI s a used true ⦃ res => ∃ z ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv true σ).1,
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' res.1 res.2 z.2 ⦄ := by
  have J := Hh.j0
  obtain ⟨hK0, hsok0, hlk0, hfk0, ekh, ect0, eact0, eidle0, earch0, erel0, -, hbsaσ⟩ := Hh.sfacts
  obtain ⟨ms0, tm0, cn0, -, eσ⟩ := Hh.spec
  have ecs0 : σ.curSc = σ0.curSc := by rw [eσ]
  have eisc0 : σ.idleSc = σ0.idleSc := by rw [eσ]
  have ecdt0 : σ.cdt = σ0.cdt := by rw [eσ]
  have eorig0 : σ.isOriginalCap = σ0.isOriginalCap := by rw [eσ]
  have hP0 := J.ip
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hARs := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS Hh.inv hC
  set sc := nodeW st s Z.c layout.node.CUR_SC with hscd
  set ct := nodeW st s Z.c layout.node.CUR_THREAD with hctd
  have hct : ct ∈ Z.T := hc.curT
  have ecur : L.curW s = ct := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = sc := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have hpc : sc.bv = σ.curSc := hs.curSc.symm
  have hpt : ct.bv = σ.curThread := hs.curThread.symm
  have hcsI := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hact (by rw [hpc]; exact hcsI) x n hk
  have hkt' : σ.kheap ct.bv = some (.tcb xt) := by rw [hpt]; exact hkt
  have hxs : xt.tcbSchedContext = some sc.bv := by
    obtain ⟨xt1, hk1, hs1, -⟩ := hC.tcb
    rw [hkt] at hk1; cases hk1; rw [hs1, hpc]
  have hne : ct.bv ≠ sc.bv := fun e => by rw [e, hk] at hkt'; cases hkt'
  have hper0 : x.scPeriod ≠ 0 := hper x n (by rw [← hpc]; exact hk)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc _ x n hsc0 (by rw [← ekh]; exact hk)).2⟩
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hcS : L.cscW s ∈ P1.Heap.scs H := hX1.2.2.cur
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (hS1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  have hW1 := hS1.wf hcS hcA
  -- the program
  unfold sched.charge_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.idle_sc.spec' as ⟨id', hid'⟩
  rw [hc.cur] at hsc' hid'
  subst hsc' hid'
  rw [sc_ne_eq]
  simp only [bind_ok]
  have hb : decide (sc ≠ nodeW st s Z.c layout.node.IDLE_SC) = decide (sc.bv ≠ σ.idleSc) := by
    rw [← hS.idle]
    apply decide_eq_decide.2
    exact ⟨fun h e => h (P1.eq_of_bv e), fun h e => h (by rw [e])⟩
  refine WP.spec_bind (WP.spec_and (charge_head_refinesK s a σ hS hR Hh.nsc Hh.inv hscC htw hact hnr hmrt hmb
    used _ hb) (P1.sched.charge_head.ring hAT s a used hX1 hcS hW1 ecsc.symm _)) ?_
  rintro s2 ⟨⟨σ2, h2, hS2, hR2, hN2, hI2, hK, hTK, hW2⟩, w2, wf2⟩
  have hK' := hK
  obtain ⟨hcs2, hcc2, hrel2, hact2, -, hid2, hisc2, hrq2, hfr2, hsck2⟩ := hK'
  obtain ⟨y2, hky2, hyt2, hym2⟩ := hsck2 x n hk
  have mem2 : ((), σ2) ∈ (chargeHead used.bv σ).1 := by rw [h2]; exact Set.mem_singleton _
  have hKh : ScTKw (fun _ => False) σ σ2 := (nkt_chargeHead used.bv) σ _ mem2
  have hsokh : SOK (true, true) σ σ2 := pres_chargeHead _ _ σ _ mem2
  have hlkh : LK (fun _ => False) σ σ2 := lkm_chargeHead _ _ σ _ mem2
  have hfkh : FK σ σ2 := fk_chargeHead _ σ _ mem2
  have hc2 := hS2.lists.choose_spec.choose_spec.1.cur
  have hN2' := hS2.lists.choose_spec.choose_spec.1.node
  -- the consumed-time reset
  step with sched.set_consumed.spec' as ⟨s3, hs3⟩
  rw [hc2] at hs3
  subst hs3
  have w3 := sfoot_wr_node hN2' (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED]) 0#u64
  obtain ⟨hS3', hf3, -⟩ := hS2.set_node_consumed 0#u64
  set σ3 : Fl4Spec.State Unit := { σ2 with consumedTime := 0 } with hσ3
  set s3 := L.wr s2 (L.nodeAt s2 Z.c layout.node.CONSUMED) 0#u64 with hs3d
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hS3'
  have hR3 : NtfnStateRel Z.N Z.T (L.mem s3) σ3 := hR2.frame hS2.placed hf3 (KView.of_kheap rfl)
  have hN3 : NSC Z.N Z.C σ3 := hN2
  have hI3 : InvBut σ3 ct.bv := hI2.congr rfl rfl rfl rfl
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  have e1 : nodeW st s3 Z.c layout.node.CUR_THREAD = ct :=
    P1.eq_of_bv (by rw [← hs3.curThread]; exact hcc2.trans hs.curThread)
  have e2 : nodeW st s3 Z.c layout.node.CUR_SC = sc :=
    P1.eq_of_bv (by rw [← hs3.curSc]; exact hcs2.trans hs.curSc)
  -- P1 after the reset
  obtain ⟨hblk3, hG3⟩ := P1.charge_pre_post (G := fun s' => P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
    (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') h1 hB1 hX1 hSg1 hS1 w2 wf2
    (fun _ _ g1 g2 => g1.trans g2) (P1.WritesIn.refl _ _)
  rw [hc2] at hblk3 hG3
  -- the spec state after the reset against the base
  have hky3 : σ3.kheap sc.bv = some (.schedContext y2 n) := hky2
  have hkp3 : ∀ q, q ≠ sc.bv → σ3.kheap q = σ.kheap q := fun q hq => hfr2 q hq
  have hO : ScOnly σ0.curSc σ0 σ3 := by
    intro q
    by_cases hq : q = sc.bv
    · subst hq
      right
      have h0 : σ0.kheap sc.bv = some (.schedContext x n) := by rw [← ekh]; exact hk
      have hpk : PK (true, true) (.schedContext x n) (.schedContext y2 n) := by
        have h := hsokh.kh sc.bv; rw [hk, hky2] at h; exact h
      obtain ⟨-, hyf, hrp⟩ := hpk
      have hl : LObj (.schedContext x n) (.schedContext y2 n) := by
        have h := (hlkh sc.bv).resolve_left id; rw [hk, hky2] at h; exact h
      obtain ⟨y', e', -, hnt⟩ := hl.2.1 x n rfl
      cases e'
      exact ⟨_, _, h0, hky3, by rw [hpc, ecs0], x, y2, n, rfl, rfl, hyt2, hym2, hyf rfl, hrp rfl, hnt⟩
    · left
      rw [hkp3 q hq, ekh]
  have hzO : SzKeepC Z.C σ0 σ3 := SzKeepC.of hO.szKeep
  -- FL4's writes from the base
  have hWK : P1.WritesIn st s s3 (KFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.kfoot_sfoot hW2 w3
  have hWK0 : P1.WritesIn st s0 s3 (KFoot st Z.T Z.N Z.C Z.c s0 σ0) :=
    WritesIn.kfoot_trans Hh.ws (fun sc1 _ x1 n1 h => ⟨x1, by rw [← ekh]; exact h⟩) hWK
  have hW0 : P1.WritesIn st s0 s3 (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot hWK0
  have hK3 : ScTKw (fun _ => False) σ2 σ3 :=
    ⟨fun p => OTK.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hKc : ScTKw (fun _ => False) σ0 σ3 := (hK0.trans hKh).trans hK3
  have hX3 : XTopAt (L := L) AR Z s3 a σ3 :=
    xtop_sc_step (ct := σ0.curThread) J.xtop hP0 J.nk hW0 hKc.ofFalse hS3 hR3 fun _ => by
      rw [← earch0]; exact hARs
  -- the scheduler facts at the reset
  have hA2 := Hh.act.headKeeps hK ⟨x, n, hk⟩
  have hAI3 : ActIdle σ3 := hA2.keep (TKeepE.of_kheap _ rfl) (fun _ h => h) (Or.inl rfl) rfl
  have hya2 : Fl4Spec.scActive y2 = true := by simp only [Fl4Spec.scActive, hym2]; exact hxa
  have hbsa3 : BlockedScActive σ3 := by
    refine hbsaσ.back (fun q y1 n1 hq ha => ?_) (fun t x1 hx1 hq => ?_)
    · by_cases e : q = sc.bv
      · rw [e, hky3] at hq; cases hq; rw [hya2] at ha; cases ha
      · exact ⟨y1, by rw [← hkp3 q e]; exact hq, ha, fun _ h => h, id⟩
    · have e : t ≠ sc.bv := fun e => by rw [e, hky3] at hx1; cases hx1
      exact ⟨x1, by rw [← hkp3 t e]; exact hx1, hq⟩
  have hown3 : CurOwnW Z.T Z.C σ3 := by
    obtain ⟨u, hu, xu, hku, hxu, hou, -⟩ := curOwn_of_curInv hS Hh.inv hC
    have hup : u.bv ≠ sc.bv := fun e => by rw [e, hk] at hku; cases hku
    refine Or.inl ⟨u, hu, xu, by rw [hkp3 _ hup]; exact hku,
      by rw [show σ3.curSc = σ.curSc from hfkh.1]; exact hxu, fun y1 n1 hy1 => ?_,
      fun h0 => absurd h0 (by rw [show σ3.consumedTime = 0 from rfl]; decide)⟩
    rw [show σ3.curSc = σ.curSc from hfkh.1, ← hpc, hky3] at hy1; cases hy1
    rw [hyt2]; exact hou x n (by rw [← hpc]; exact hk)
  have hsort3 : IpcSorted σ3 :=
    J.isorted.frame (fun q x' hq => ⟨x', hO.othB hq (fun _ _ e => by cases e), rfl⟩)
      (fun q x' hq => ⟨x', hO.othB hq (fun _ _ e => by cases e), rfl⟩) hO.prio
  have eN : L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb Hh.ws.1 _ _
  have hDbg3 : L.mem s3 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hh.dbg]
    exact hG3.mem_eq J.kern.dwAl fun hk' => P1.dbg0_not_schedW Hh.blk J.kern.cs0 (Or.inl (by rw [eN]; exact hk'))
  have hct3 : σ3.curThread = ct.bv := hcc2.trans hs.curThread
  have Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s3 a σ3 :=
    { j0 := J, ws := hWK0, xtop := hX3, buf := J.sc_buf hW0 hKc, nsc := hN3,
      inv := by rw [hct3]; exact hI3, act := hAI3, bsa := hbsa3, own := hown3, isorted := hsort3,
      blk := hblk3, dbg := hDbg3, dbgK := Hh.dbgK.trans (P1.Foot.dbgKeep Hh.blk (fun _ h => h) hG3), ksc := hO, ct := hcc2.trans ect0, idle := hid2.trans eidle0,
      csc := hcs2.trans ecs0, rel := hrel2.trans erel0, cdt := hsokh.cdt.trans ecdt0,
      orig := hsokh.orig.trans eorig0, arch := hKh.arch.trans earch0, isc := hisc2.trans eisc0, cons := rfl }
  -- the tail: the current thread, schedulable
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc3.cur, e1] at hct'
  subst hct'
  step with Fl4Proofs.P3.Sched.sched.is_schedulable.spec' as ⟨b1, hb1⟩
  rw [schedulable_eq hR3 hS3 hct] at hb1
  subst hb1
  have hkt3 : σ3.kheap ct.bv = some (.tcb xt) := by rw [hkp3 _ hne]; exact hkt'
  have hrun : Fl4Spec.runnable xt.tcbState = true := by rcases hrr with e | e <;> rw [e] <;> rfl
  have hsch : Fl4Spec.schedulable ct.bv σ3 = true :=
    schedulable_of hkt3 hxs hrun hky3 hya2 (by rw [show σ3.releaseQueue = σ.releaseQueue from hrel2]; rw [hpt]; exact hC.notRel)
  simp only [hsch, ↓reduceIte]
  have hnq3 : NotQueued σ3 ct.bv :=
    ⟨fun d q => by rw [show σ3.readyQueues = σ.readyQueues from hrq2, hpt]; exact hnq d q,
      by rw [show σ3.releaseQueue = σ.releaseQueue from hrel2, hpt]; exact hC.notRel⟩
  have hidt3 : σ3.idleThread ≠ ct.bv := by
    rw [show σ3.idleThread = σ.idleThread from hid2, hpt]; exact fun e => hni e.symm
  have hres3 : σ3.schedulerAction = .resumeCurThread ∨ σ3.schedulerAction = .chooseNewThread :=
    hres.imp (fun e => hact2.trans e) (fun e => hact2.trans e)
  have hp3 : ∃ l, σ3.kheap p = some (.endpoint (.recvEP l)) := by
    obtain ⟨l, hl⟩ := hkl
    by_cases e : p = sc.bv
    · rw [e, hk] at hl; cases hl
    · exact ⟨l, by rw [hkp3 _ e]; exact hl⟩
  have hper2 : y2.scPeriod ≠ 0 := by
    obtain ⟨y', n', hky', hy'⟩ := hs3.scs sc hscC
    rw [hky3] at hky'; cases hky'
    rw [hy'.period]
    have e3 : L.rperiod s3 sc = L.rperiod s sc := by
      have hp2 : L.rperiod s2 sc = L.rperiod s sc := by
        have := P1.rperiod_of_ring hX1 hcS w2; rw [ecsc] at this; exact this
      rw [← hp2]
      obtain ⟨y'', n'', hky'', hy''⟩ := (hS2.lists.choose_spec.choose_spec.2).scs sc hscC
      rw [hky2] at hky''; cases hky''
      have h1' := hy''.period
      rw [hy'.period] at h1'
      exact P1.eq_of_bv h1'
    rw [e3, ← hx.period]; exact hper0
  refine WP.spec_bind (Hj.endTimesliceTmoJR hAT hmax (htu a) hct hct3.symm hkt3 hrr hscC (hcs2.trans hpc.symm) hxs hky3 hya2 hper2
    hth hp3 hres3 hnq3 hidt3) ?_
  rintro ⟨s4, a1⟩ ⟨z4, hz4, V4, Lst4, D4, J4⟩
  obtain ⟨s5, hs5, σ5, h5, Ac5, Lst5, D5, J5⟩ := J4.reschedJ
  refine WP.spec_bind (show sched.reschedule_required st s4 ⦃ s' => s' = s5 ⦄ by
    rw [hs5]; exact (WP.spec_ok _).2 rfl) ?_
  rintro _ rfl
  refine WP.spec_bind (sched.set_reprogram.spec' (L := L) _) ?_
  rintro s6 rfl
  rw [WP.spec_ok]
  beta_reduce
  refine ⟨((), { σ5 with reprogramTimer := true }), ?_, V4, Ac5, Lst5, D5, J5.reprogramJ⟩
  rw [chargeBudget_eq, nd_bind_one h2, chargeTail_eq true σ2 (hcc2.trans hs.curThread), if_pos hsch]
  refine mem_bind_nd (x := z4) hz4 (mem_bind_nd (x := ((), σ5))
    (show ((), σ5) ∈ (Fl4Spec.rescheduleRequired (Z := Unit) z4.2).1 by rw [h5]; exact Set.mem_singleton _) ?_)
  simp [Fl4Spec.NonDet.modify]


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`check_budget` charging from a `JHole`, the current thread's timeout
fault blocking it** (module docstring). -/
theorem JHole.checkBudgetTR {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l))) :
    sched.check_budget st arI s a ⦃ res => res.1 = false → ∃ z ∈ (Fl4Spec.checkBudget (Z := Unit) σ).1,
      z.1 = false ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' res.2.1 res.2.2 z.2 ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  have hax : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk hax _ hmb) ?_
  intro b hb
  by_cases hbt : b = true
  · rw [if_pos hbt, is_cur_domain_expired_eq]
    simp only [bind_ok]
    refine (WP.spec_ok _).2 ?_
    intro h; exact absurd h (by simp)
  · rw [if_neg hbt]
    have hbf : b = false := by simpa using hbt
    subst hbf
    refine WP.spec_bind (Hh.chargeBudgetTmoJR hAT hmax htu hC hni hres hnq hmrt hmb hkt hrr hth hper hkl
      (nodeW st s Z.c layout.node.CONSUMED)) ?_
    rintro ⟨s1, a1⟩ ⟨z, hz, V, Ac', Lst', D', J'⟩
    refine (WP.spec_ok _).2 fun _ => ⟨(false, z.2), ?_, rfl, V, Ac', Lst', D', J'⟩
    have hb' : Fl4Spec.getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(false, σ)}, False) := by
      rw [hs.curSc, hs.consumed]; exact hb
    have hz' : z ∈ (Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime true σ).1 := by
      rw [hs.consumed]; exact hz
    unfold Fl4Spec.checkBudget
    rw [nd_gets_bind, nd_gets_bind, Notif.nd_bind_one hb']
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nd_gets_bind]
    exact mem_bind_nd (x := z) hz' (by simp [pure, Fl4Spec.NonDet.pure])

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` charging the current thread with an endpoint
timeout handler on an idle or sending endpoint, a reschedule pending or
not** (module docstring). -/
theorem JHole.mcsPPJR {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hnsuf : ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true))
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l))) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb)
    (Hh.checkBudgetTR hAT hmax htu hC hni hres hnq hmrt hmb hkt hrr hth hper hkl)) ?_
  rintro ⟨r, s', a'⟩ ⟨hT, hF⟩
  refine (WP.spec_ok _).2 ?_
  cases r
  · obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF rfl
    exact ⟨z.2, fun y hy => mem_pp_sched hsch hz hy, fun hy => fail_pp_sched hsch hz hy,
      Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩
  · exact absurd (hT rfl).2.2 hnsuf

variable (arI) in

end

end

end Fl4Proofs.P3
