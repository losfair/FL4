/-
P3 (DESIGN.md §9), IPC (KENTRY-PLAN sch29): **the reply-push SC donation to
the running receiver for any current SC.** XTopJointRecvSendRD's
`JAtZ.pushDonRJ` / `JAtZ.recvSendFPDJ` / `JAtZ.recvSendPDJ` (the passive
server after `maybe_return_sc`) ask the current SC to be bound to no thread.
At a `chooseNewThread` mid state with ct SC-less the current SC may still be
owned by another thread (a `ReplyRecv` whose reply returned the SC to the
caller), or be the donated SC itself; `CurOwnW` and `OffOK` are kept in every
case:

* the donated SC is the current one: its new owner is the receiver `d`
  (`dn_kp`; `d` in no queue), its refills unchanged;
* another current SC owned by `u`: `u` is neither the donor (whose SC is the
  donated one) nor `d` (no SC), so `u` and the current SC are untouched;
* the current SC bound to no thread: as before.

Scripted (sch29gen/gen.py, untracked): `JAtZ.pushDonRJW`,
`JAtZ.recvSendFPDJW`, `JAtZ.recvSendPDJW` = the originals with the
current-SC premises (`hcsC`, `hcsx`, `hk0`, `hcsF`) removed and the two
`CurOwnW` / `OffOK` steps above.
-/
import Fl4Proofs.P3.XTopJointRecvSendRD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 32000000 in
/-- **The donating part of `reply_push` at `J`, the donor not current**
(module docstring, sch29): `JAtZ.pushDonRJ` for any current SC (`JAtZ.own`); `t`, blocked on the reply `w` (bound to it, unlinked, on
no call stack), donates its SC `sc` (active, released) to `d` (no SC, not
blocked in an IPC queue, not dead), both in no queue, a reschedule pending. -/
theorem JAtZ.pushDonRJW (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t d w sc : U64} (ht : t ∈ Z.T) (hd : d ∈ Z.T) (hw : w ∈ Z.R) (hsC : sc ∈ Z.C) (htd : t ≠ d)
    {xt xd : Fl4Spec.Tcb} {xw : Fl4Spec.Reply} {y : Fl4Spec.SchedContext} {n : Nat}
    (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hkw : σ.kheap w.bv = some (.reply xw)) (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hst : xt.tcbState = .blockedOnReply w.bv) (hxt : xt.tcbSchedContext = some sc.bv) (hyt : y.scTcb = some t.bv)
    (hxd : xd.tcbSchedContext = none) (hdq : Fl4Spec.ipcQueuedThreadState xd.tcbState = false)
    (hidd : d.bv ≠ σ.idleThread) (hwt : xw.replyTcb = some t.bv)
    (hrelD : released σ y) (hcn : σ.schedulerAction = .chooseNewThread)
    (hnqt : NotQueued σ t.bv) (hnqd : NotQueued σ d.bv) (hya : Fl4Spec.scActive y = true)
    (hdet : Detached Z.C Lst w) (hn0 : L.mem s (rNextA w) = 0#u64) (hp0 : L.mem s (rPrevA w) = 0#u64)
    (hdD : ∀ q ∈ D, q.bv ≠ d.bv) :
    (do
      let i2 ← obj.Sc.reply st sc s
      let s3 ← if i2 != 0#u64 then obj.Reply.set_next st i2 s w false else ok s
      let s4 ← obj.Reply.set_prev st w s3 i2
      let s5 ← obj.Sc.set_reply st sc s4 w
      let s6 ← obj.Reply.set_next st w s5 sc true
      schedcontext.donate st arI s6 a sc d) ⦃ res => res.2 = a ∧
        (do
          Fl4Spec.bindScReply (Z := Unit) sc.bv w.bv
          Fl4Spec.schedContextDonate (Z := Unit) sc.bv d.bv) σ =
          ({((), pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n)}, False) ∧
        ∃ Lst', JAtZ (L := L) arI AR Z H Cs Ac Lst' D res.1 a (pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n) ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsC
  have hscH : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n hsc0 hky).2⟩
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hdH : d ∈ P1.Heap.tcbs H := J.zH.1 d hd
  have hwH : w ∈ P1.Heap.replies H := J.tcbs_eq.2 ▸ hw
  -- the objects apart
  have htd' : t.bv ≠ d.bv := bv_ne htd
  have hst' : sc.bv ≠ t.bv := kheap_ne hky hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hsd' : sc.bv ≠ d.bv := kheap_ne hky hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hws : w.bv ≠ sc.bv := kheap_ne hkw hky (fun _ h1 h2 => by subst h1; cases h2)
  have hwt' : w.bv ≠ t.bv := kheap_ne hkw hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hwd' : w.bv ≠ d.bv := kheap_ne hkw hkd (fun _ h1 h2 => by subst h1; cases h2)
  -- the stack's old head
  obtain ⟨⟨y0, n0, hk0, hyL⟩, hLR, -, hLw⟩ := J.call.stack sc hsC
  rw [hky] at hk0; cases hk0
  have hh : ∀ h l, y.scReplies = h :: l → h ≠ sc.bv ∧ h ≠ w.bv ∧ ∃ x, σ.kheap h = some (.reply x) := by
    intro h l hr
    rw [hyL] at hr
    cases e : Lst sc with
    | nil => rw [e] at hr; cases hr
    | cons h' l' =>
      rw [e] at hr
      simp only [List.map_cons, List.cons.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      have hh' : h' ∈ Z.R := hLR h' (by rw [e]; exact List.mem_cons_self ..)
      obtain ⟨x, hx, -⟩ := J.call.reply h' hh'
      refine ⟨fun e' => ?_, fun e' => ?_, x, hx⟩
      · have h2 : σ.kheap sc.bv = some (.reply x) := by rw [← e']; exact hx
        rw [hky] at h2; cases h2
      · exact hdet sc hsC (by rw [e, P1.eq_of_bv e']; exact List.mem_cons_self ..)
  have hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u := fun u e => by rw [hcn] at e; cases e
  have hpd := pd_eqN hkt hkd hky hkw hws hh hyt htd' hst' hsd' hwt' hwd' hcn hnqt
  have hdn := bd_donate_eqN hkt hkd hky hkw hws hh hyt htd' hst' hsd' hcn hnqt
  -- FL4's words at the start
  have bits : ∀ u ∈ Z.T, NotQueued σ u.bv →
      (L.mem s (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hc.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s (P1.prioA u)))
      rw [hs.rq _ (hc.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hc.released u hu).1 h
      apply hnu.2
      rw [hs.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits t ht hnqt
  obtain ⟨hqbD, hrbD⟩ := bits d hd hnqd
  have ha1 : L.actionW s = 1#u64 := by
    have h := hS.act
    rw [hcn] at h
    unfold P1.LawfulStore.actionW; rw [hc.cur]; exact h
  have hna : ∀ u ∈ Z.T, L.actionW s ≠ u := fun u hu h' => by
    rw [ha1] at h'; exact P1.notT_small hc.tcbs (by simp) (h' ▸ hu)
  have hiw : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s ≠ u := fun u hu hne h' => by
    apply hne
    rw [hs.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hc.cur] at h'
    exact congrArg _ (show nodeW st s Z.c layout.node.IDLE_THREAD = u from h').symm
  have hitd : t.bv ≠ σ.idleThread := by
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    intro e; rw [← e, hkt] at hkx; cases hkx; rw [hst] at hxs; cases hxs
  have hsw : L.mem s (P1.scA t) = sc := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs.tcb t ht
    rw [hkt] at hk'; cases hk'
    exact optRef_some_eq (hscw.symm.trans hxt)
  have hd0 : L.mem s (P1.scA d) = 0#u64 := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs.tcb d hd
    rw [hkd] at hk'; cases hk'
    exact Notif.optRef_none (by rw [← hscw]; exact hxd)
  have hiA : sc ∈ Ac := by
    have hrm := SchedRel.act_sc hS hsC hky hya
    exact (J.blk.2.2.2.1.act _ hscH).2 (fun h => hrm (by rw [h]; rfl))
  have haff : L.mem s (P1.affA d) = L.mem s (P1.scCoreA sc) := by
    rw [hc.aff d hd, Fl4Proofs.P3.Sched.scCoreA_eq, hS.core sc hsC]
  have hR0 : ∀ r ∈ Z.R, r ≠ 0#u64 ∧ r.val % 2 = 0 := fun r hr =>
    ⟨(J.rp.align r hr).2.1, by have := (J.rp.align r hr).1; omega⟩
  have hiso : Isolated (L.mem s) Z.R w := J.call.isolated hR0 hw hdet hn0 hp0
  have hrel : inClassR xd.tcbState xd.tcbFault → Fl4Spec.scActive y = true → released σ y := fun _ _ => hrelD
  have hnf : ¬ Free σ w := by
    rintro ⟨x, hx, hn⟩; rw [hkw] at hx; cases hx; rw [hwt] at hn; cases hn
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := J.blk
  refine WP.spec_mono (WP.spec_and
    (push_donate_refinesW s a σ hS hR J.nsc J.inv J.call J.rp hsC hsc0 hky ht hyt hkt hd hkd hxd htd hrel hw hdet
      hiso J.rfree hnf)
    (P1.ipc.push_don.blk (Es := P1.EH H) hAT s a t d w sc Q1 R1 h1 hB1 hX1 hS1 hSg1 htH hqbT hrbT
      (hna t ht) (hiw t ht hitd) hwH hdH (Ne.symm htd) hqbD hrbD (hna d hd) (hiw d hd hidd) hsw hsc0 hiA hd0 haff)) ?_
  rintro ⟨s', a'⟩ ⟨⟨ha, σ', hsp, hS', hR', hN', hI', hCR', hRP', hRF', hw0, hwd⟩, hP1⟩
  simp only [WP.uncurry'_pair] at hP1 ha
  obtain ⟨hblk, hfoot⟩ := hP1
  subst a'
  have e' : σ' = pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n := by
    have h := hsp.symm.trans hpd
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  subst e'
  refine ⟨rfl, hpd, Function.update Lst sc (w :: Lst sc), ?_⟩
  set σ' := pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n with hσ'
  set σB := bdSt σ sc.bv w.bv y n xw with hσB
  -- the spec's step and FL4's writes
  have hK : ScTKw (fun _ => False) σ σ' :=
    NKT.of_eq (nkt_bind (nkt_bindScReply _ _) fun _ => nkt_schedContextDonate _ _) hpd
  have hW : P1.WritesIn st s s' (fun b => TFoot st Z.T Z.N Z.C Z.c s σ b ∨ CallW' Z.R Z.C b) :=
    hw0.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h)) Or.inr
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    xtop_sc_stepCW (ct := σ.curThread) J.xtop J.ip J.nk J.ks.rep hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' :=
    tk_liftCW (ct := σ.curThread) J.ip hI hW (ScTKw.ofFalse (P := fun p => p = σ.curThread) hK) hS' hR'
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw0 fun b hb =>
    hb.elim (fun h => tfoot_oobj hS (Or.inl h)) (fun h => callW'_oobj J.ip hS h)
  have hSS := hF.1
  have hks : L.ksb s' = L.ksb s := hF.2
  have hwR : P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ) :=
    J.rmW_of (hw0.mono fun b hb => hb.elim Or.inl (fun h => Or.inr (Or.inl h)))
  obtain ⟨k1, k2, kb⟩ := J.rmW_keeps hwR
  have hsok : SOK (true, false) σ σ' :=
    (bd_sok hky hkw hws hh).trans ((pres_schedContextDonate (true, false) _ _).of_eq hdn)
  have hyk : YKeep σ σ' := hsok.ykeep rfl
  have hmk : McpKeep σ σ' := hsok.mcpKeep
  have hcn' : σ'.schedulerAction = .chooseNewThread := rfl
  have hFK : FK σ σ' := ⟨pd_csc, pd_idle, pd_isc⟩
  have hIK := J.idleW_keep hS' pd_idle pd_isc
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  -- the bound-before objects at `σB`
  have hktB : σB.kheap t.bv = some (.tcb xt) := bd_oth hky hkw hws hh (fun _ e => by cases e) (Ne.symm hst') hkt
  have hkdB : σB.kheap d.bv = some (.tcb xd) := bd_oth hky hkw hws hh (fun _ e => by cases e) (Ne.symm hsd') hkd
  have hkpB : σB.kheap sc.bv = some (.schedContext { y with scReplies := w.bv :: y.scReplies } n) := bd_kp hws
  -- the current SC (sch29: any owner, `J.own`)
  have hcs' : σ'.curSc = σ.curSc := @pd_csc σ t.bv d.bv sc.bv w.bv xt xd xw y n
  have hcons : σ'.consumedTime = σ.consumedTime := @bd_cons σ sc.bv w.bv y n xw
  have htm : σ'.curTime = σ.curTime := @pd_tm σ t.bv d.bv sc.bv w.bv xt xd xw y n
  have hisc : σ'.idleSc = σ.idleSc := @pd_isc σ t.bv d.bv sc.bv w.bv xt xd xw y n
  have hrl' : σ'.releaseQueue = σ.releaseQueue := @pd_rel σ t.bv d.bv sc.bv w.bv xt xd xw y n
  have hkpP : σ'.kheap sc.bv =
      some (.schedContext { { y with scReplies := w.bv :: y.scReplies } with scTcb := some d.bv } n) := dn_kp hsd'
  obtain ⟨x0, n0, hk0⟩ : ∃ x0 n0, σ.kheap σ.curSc = some (.schedContext x0 n0) := by
    rcases J.own with ⟨u, -, xu, hku, hxu, -, -⟩ | ⟨⟨c0, hc0, e0⟩, -⟩
    · obtain ⟨x0, n0, h0, -⟩ := J.inv.back u.bv xu σ.curSc hku hxu
      exact ⟨x0, n0, h0⟩
    · obtain ⟨x0, n0, h0, -⟩ := hs.scs c0 hc0
      exact ⟨x0, n0, by rw [← e0]; exact h0⟩
  have hcst : σ.curSc ≠ t.bv := kheap_ne hk0 hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hcsd : σ.curSc ≠ d.bv := kheap_ne hk0 hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hko_cs : σ.curSc ≠ sc.bv → σ'.kheap σ.curSc = some (.schedContext x0 n0) := fun hcx => by
    rw [hσ', pd_ko hcst hcsd hcx]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hcx hk0
  -- the receivers' replies
  have hrr : RRecv (L.mem s') Z.R σ' := by
    intro d' hd' hrd
    have hrd0 := (KhRB.of_sctkw hK).recvB hrd
    obtain ⟨h1', h2'⟩ := J.rrecv d' hd' hrd0
    have hdw : d' ≠ w := by
      rintro rfl
      obtain ⟨x, t', xt', hx, ht', hxt', hrb⟩ := hrd0
      rw [hkw] at hx; cases hx; rw [hwt] at ht'; cases ht'; rw [hkt] at hxt'; cases hxt'
      rw [hst] at hrb; cases hrb
    have hdet' := detached_of_next0 J.call (fun r hr => (J.rp.align r hr).2.1) h1'
    have hnh : (Lst sc).head? ≠ some d' := fun e => hdet' sc hsC (List.mem_of_mem_head? e)
    obtain ⟨e1, e2⟩ := hwd d' hd' hdw hnh
    exact ⟨e1.trans h1', e2.trans h2'⟩
  -- the dead
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq => by
    have hdq := J.jcov.dead q hq
    have hqt : q.bv ≠ t.bv := J.notDead ht hkt (by rw [hst]; simp [tsCode]) q hq
    have hqd : q.bv ≠ d.bv := hdD q hq
    have hqs : q.bv ≠ sc.bv := fun e => J.scOwned_not_dead ht hky hyt (by rw [← P1.eq_of_bv e]; exact hdq)
    have hko : σ'.kheap q.bv = σB.kheap q.bv := pd_ko hqt hqd hqs
    refine J.deadP_keep hIR.2.2.1 hIR.1 (fun x0 hx0 _ => ?_) (fun x0 hx0 => ?_) (fun x0 hx0 => ?_)
      (fun x0 hx0 => ?_) (fun x0 m hx0 => ?_) (fun hqC => ?_)
      (fun z hz hqC K hK8 hK' => J.rmW_scOut hwR hz hqC hK8 hK') pd_idle
      (fun u hu => by rw [hcn'] at hu; cases hu) (J.yld.frame k2 hyk) (hyk.dk q.bv) hdq
    · exact ⟨x0, by rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0, rfl, rfl, Or.inl rfl⟩
    · rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0
    · exact ⟨x0, by rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0, Or.inl rfl, rfl,
        Or.inl rfl⟩
    · obtain ⟨x', h1', h2'⟩ := bd_reply hky hkw hws hh hx0
      exact ⟨x', by rw [hko]; exact h1', h2'⟩
    · exact ⟨x0, by rw [hko]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hqs hx0, Or.inl rfl, Or.inl rfl⟩
    · have hqsc : q ≠ sc := fun e => hqs (by rw [e])
      obtain ⟨-, -, -, hW1⟩ := J.call.stack q hqC
      obtain ⟨-, -, -, hW2⟩ := hCR'.stack q hqC
      rw [hW2.1, hW1.1, Function.update_of_ne hqsc]
  -- the scheduler after
  have hown : CurOwnW Z.T Z.C σ' := by
    by_cases hcx : σ.curSc = sc.bv
    · refine Or.inl ⟨d, hd, _, pd_kd, by rw [hcs', hcx], fun x m hx => ?_, fun _ => by rw [hrl']; exact hnqd.2⟩
      rw [hcs', hcx, hkpP] at hx; cases hx; rfl
    · rcases J.own with ⟨u, hu, xu, hku, hxu, hown0, hnr⟩ | ⟨hcsC, hun⟩
      · have hut : u.bv ≠ t.bv := fun e => by
          rw [e, hkt] at hku; cases hku; rw [hxt] at hxu; exact hcx (Option.some.inj hxu).symm
        have hud : u.bv ≠ d.bv := fun e => by
          rw [e, hkd] at hku; cases hku; rw [hxd] at hxu; cases hxu
        have hus : u.bv ≠ sc.bv := kheap_ne hku hky (fun _ h1 h2 => by subst h1; cases h2)
        refine Or.inl ⟨u, hu, xu, ?_, by rw [hcs']; exact hxu, fun x m hx => ?_, fun h0 => ?_⟩
        · rw [hσ', pd_ko hut hud hus]; exact bd_oth hky hkw hws hh (fun _ e => by cases e) hus hku
        · rw [hcs', hko_cs hcx] at hx; cases hx; exact hown0 x0 n0 hk0
        · rw [hrl']; exact hnr (by rw [← hcons]; exact h0)
      · exact Or.inr ⟨by rw [hcs']; exact hcsC, fun x m hx => by
          rw [hcs', hko_cs hcx] at hx; cases hx; exact hun x0 n0 hk0⟩
  have hoff : OffOK σ' := by
    intro h0 y' m hy ha
    rw [hcons] at h0 ⊢; rw [htm]
    by_cases hcx : σ.curSc = sc.bv
    · rw [hcs', hcx, hkpP] at hy; cases hy
      exact J.off h0 y n (by rw [hcx]; exact hky) (fun h => ha (by rw [hcs', hisc]; exact h))
    · rw [hcs', hko_cs hcx] at hy; cases hy
      exact J.off h0 x0 n0 hk0 (fun h => ha (by rw [hcs', hisc]; exact h))
  have hact : ActIdle σ' :=
    ⟨(fun u hu => by rw [hcn'] at hu; cases hu),
      dn_idleOK hktB hkdB hkpB htd' hst' hsd' (by rw [bd_idle]; exact Ne.symm hitd)
        (by rw [bd_idle]; exact Ne.symm hidd) (bd_idleOK hky hkw hws hh J.act.2)⟩
  have hbsa : BlockedScActive σ' :=
    dn_bsa hktB hkdB hkpB htd' hst' hsd' hdq (bd_bsa hky hkw hws hh J.bsa hya)
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hK.szKeep q.bv y n hq) hks (J.rmW_irq hwR) hIK.2⟩
  exact J.sc_frameS hks hSS (J.vkeep_of hwR fun b hb => J.rmW_nv hb) hK hX' hCR' hRF' hrr (J.yld.frame k2 hyk) (J.mcp.frame k1 hmk)
    (J.buf.frame kb hK.bufKeep) hRP' (J.apart.sc_frame hks hK.szKeep) hjpl (J.jcov_keep hks hSS hdead hIK)
    (J.sc_kernW hW hK hFK hX' hDbg (subset_refl D))
    (J.rmW_utc hwR hSS hK.cdt hK.orig pd_arch hDbg) hN' hI' (Or.inl hcn') hown hoff hact hbsa
    (Or.inl (by rw [hcn']; intro h; cases h)) hblk hKd hIK.1 J.zD



set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a faulted head sender with an SC pushing a reply
and donating the SC at `J`** (module docstring): XTopJointRecvSendP's
`JAtZ.recvSendFPJG` for a sender with an SC `p` and a fault other than a
timeout, the receiver (current) without an SC, a reschedule pending (any current SC, sch29); the push donates `p` to the receiver
(`reply_push_iC`'s donation step: `JAtZ` at the block by `JAtZ.rsfr_postGR`,
then `JAtZ.pushDonRJW`). -/
theorem JAtZ.recvSendFPDJW (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) {f : Fl4Spec.Fault}
    (hft : xs.tcbFault = some f) (hnto : ∀ b, f ≠ .timeout b)
    {p : U64} (hpC : p ∈ Z.C) (hxsp : xs.tcbSchedContext = some p.bv) (hxtn : xt.tcbSchedContext = none)
    (hcn : σ.schedulerAction = .chooseNewThread) (hnrT0 : t.bv ∉ σ.releaseQueue)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (hyes : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) (hrn : rc ≠ .Null)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
    {m : Result (S × A)} (hm : ∀ {P : S × A → Prop}, (do
            let st1 ← obj.Ep.state st e s
            if st1 = obj.EP_IDLE then do
              let s3 ← endpoint.wait_for_sender st s t e blk rv
              ok (s3, a)
            else if st1 = obj.EP_RECV then do
              let s3 ← endpoint.wait_for_sender st s t e blk rv
              ok (s3, a)
            else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄ → m ⦃ P ⦄) :
    m ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have J := J.undeadC hcovR.1 hcovR.2 (J.replyArg_ntcb hrc)
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ Z.T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    constructor
    · intro h0; obtain ⟨_, _, _, h1⟩ := tsCode_three h0; rw [h1] at hrun; simp [Fl4Spec.runnable] at hrun
    · intro h0; obtain ⟨_, _, h1⟩ := tsCode_four h0; rw [h1] at hrun; simp [Fl4Spec.runnable] at hrun
  have hts : t ≠ sd' := by intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have hst' : sd'.bv ≠ t.bv := bv_ne (Ne.symm hts)
  have hsc : sd'.bv ≠ σ.curThread := by rw [hct]; exact hst'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hsH : sd' ∈ P1.Heap.tcbs H := J.zH.1 sd' hsT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hsta := hTP sd' hsH
  have hss : L.mem s (P1.stA sd') = sched.TS_BLOCKED_ON_SEND := by
    rw [stA_tStA, tsVals.2.2.2.1]; exact UScalar.eq_of_val_eq hs4
  have hbe : L.mem s (P1.blockA sd') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hsb
  have hdq := P1.endpoint.ep_dequeue.inv s sd' Q0 R0 h0 hsH (by simp) (Or.inl hss)
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : sd' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 sd' hsH (by simp) (Or.inl hss); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e sd' (EQ0 e) hTP hE0 hq0' hdm
  apply hm
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = sd' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := sd')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he sd' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, cc1, nc1⟩, w1⟩
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (sd' :: xs'), TL w b) :=
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
  -- the badge and the flags
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  refine WP.spec_bind (Endp.obj.Tcb.block_badge.spec s1 sd') ?_
  rintro bdg hbdg
  refine WP.spec_bind (Endp.obj.Tcb.block_flags.spec s1 sd') ?_
  rintro fl hfl
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hg : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hc : (i2 != 0#u64) = dd.senderIsCall := by
    rw [← flags_call dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi2
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  -- the transfer: the fault (XTopJointXferF's `xferFaultStepGJ`, on `IRel`)
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) with hσ1
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by simp [σ1]
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  have hth : Z.th t = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkt
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hUt := J.rbufU ht hth hkt
  have hok : FaultOK (L := L) s1 sd' xs f := by
    cases f with
    | timeout b0 => exact absurd rfl (hnto b0)
    | _ => trivial
  refine WP.spec_bind (xferFaultStepGJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) hsT ht (Ne.symm hts) hks1 hkt1 hft hok e bdg (i != 0#u64)
    hTP htH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUt b hb).1.ksb hW1.1, (hUt b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) t.bv (.tcb x2) with hσ2
  have hkt2 : σ2.kheap t.bv = some (.tcb x2) := by simp [σ2]
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, Ne.symm hte, hk1e]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 ht hA2 (fun p hp => by simp [σ2, hp]) hkt1 hkt2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xt b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  -- the spec frame from `σ`
  have Fr1 : RSFr sd'.bv t.bv σ σ1 := RSFr.upd hk (Or.inr (Or.inr ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩))
  have Fr2c : RSFr sd'.bv t.bv (Endp.setUm σ1 um2) σ2 := by
    have h := RSFr.arch (t := sd'.bv) (σ := Endp.setUm σ1 um2) hkt1 x2.tcbArch
    rw [← hx2] at h; exact h
  have Fr2 : RSFr sd'.bv t.bv σ σ2 := (Fr1.trans (RSFr.um _ _ σ1 um2)).trans Fr2c
  have IK1 : IK sd'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) hk
    (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σ σ1 := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have IK2 : IK sd'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans
    (IK.updTcb (σ := Endp.setUm σ1 um2) hkt1 (by rw [hx2]) (by rw [hx2]) (fun _ => by rw [hx2])))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((Fl4Proofs.P3.SKeep.um σ1 um2).trans (Ipc.SKeep.updK (σ := Endp.setUm σ1 um2) (p := t.bv)
    (o := .tcb x2) (fun y' h => ⟨xt, hkt1, by cases h; rw [hx2]⟩) (fun _ _ h => by cases h)))
  -- the sender's sporadic check, at the hole
  have hne2 : ∀ p y' n, σ2.kheap p = some (.schedContext y' n) → Fl4Spec.scActive y' = true → y'.scRefills ≠ [] :=
    fun p y' n hp ha => J.inv.ne p y' n (SK2.2.2.2 p y' n hp) ha
  refine WP.spec_bind (unblockHole hP0 (IpcRel.ofSRN hR2 hS2') hsT hks2 hne2 h2 hB2 hX2 hS2'' hSg2 hsH) ?_
  rintro s3 ⟨σ3, hA, hIR3, hW3, h3, hB3, hX3, hS3', hSg3, hT3, fu3, hU3⟩
  have hk3 : ∀ q' o', σ2.kheap q' = some o' → (∀ y' n, o' ≠ .schedContext y' n) → σ3.kheap q' = some o' := by
    intro q' o' hq ho
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, -, rfl, -⟩
    · exact hq
    · have hqp : q' ≠ p := fun h => by subst h; rw [hkp] at hq; cases hq; exact ho _ _ rfl
      simp [Notif.updK, hqp, hq]
  have hks3 : σ3.kheap sd'.bv = some (.tcb xs) := hk3 _ _ hks2 (fun _ _ h => by cases h)
  have hk3e := hk3 _ _ hk2e (fun _ _ h => by cases h)
  have ct3 : σ3.curThread = σ2.curThread := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]
    · rw [h]; rfl
  have act3 : σ3.schedulerAction = σ2.schedulerAction := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]
    · rw [h]; rfl
  have hR3 := hIR3.1.toE
  have hS3 := IpcRel.toSRN hIR3.1 hIR3.2
  have hxs3 := hR3.at_tcb hsT hks3
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 sd') ?_
  rintro ft hft'
  have hftB : (ft != fl4_abi.consts.fault.NullFault) = true := by
    rw [hft']
    have hne : L.mem s3 (tFaultA sd') ≠ fl4_abi.consts.fault.NullFault := fun e => by
      have := hxs3.fault0.1 (by rw [e]; unfold fl4_abi.consts.fault.NullFault; rfl); rw [hft] at this; cases this
    simpa using hne
  -- the sender is in no queue
  have eW : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → 3328 ≤ K.val → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s3 (core.num.U64.wrapping_add sd' K) = L.mem s (core.num.U64.wrapping_add sd' K) := by
    intro K k1 k2 k3 k4 k5
    rw [hT3 sd' hsH K k1 k2, f2 sd' hsH K k3 k1 k2, f1 sd' hsH K k1 k2 k4 k5]
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [← blockA_tBlockA, P1.blockA_eq, eW _ (by simp) (by simp) (by simp) (by simp) (by simp), ← P1.blockA_eq]
    exact hbe
  have hst3 : L.mem s3 (P1.stA sd') = sched.TS_BLOCKED_ON_SEND := by
    rw [P1.stA_eq, eW _ (by simp) (by simp) (by simp) (by simp) (by simp), ← P1.stA_eq]
    exact hss
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ sd' :=
    hX3.noref hsta (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide)
      (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide)  -- the sender is in no ready or release queue
  have hnqS : NotQueued σ sd'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  -- the receiver: current, without an SC, a reschedule pending
  have hsw : ∀ u, σ.schedulerAction ≠ .switchThread u := fun u h => by rw [hcn] at h; cases h
  have hnrT : t.bv ∉ σ.releaseQueue := hnrT0
  have hnqT : ∀ dm p, t.bv ∉ σ.readyQueues dm p := by rw [← hct]; exact hnq
  -- the frames to `σ3`
  have Fr3 : RSFr sd'.bv t.bv σ2 σ3 := by
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, hpc, rfl, -, -, hz, -⟩
    · exact RSFr.refl _ _ _
    · exact (RSFr.reprog _ _ σ2).trans (RSFr.upd (σ := { σ2 with reprogramTimer := true }) hkp
        (Or.inr (Or.inl ⟨y', n, z.scRefills, rfl, by rw [← hz], hpc⟩)))
  have Fr23 : RSFr sd'.bv t.bv σ σ3 := Fr2.trans Fr3
  have hrq3 : σ3.readyQueues = σ.readyQueues := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]; exact IK2.2.1
    · rw [h]; exact IK2.2.1
  -- the reply
  have hgg := hyes _ _ hstd
  obtain ⟨wb, r', hrcw, hrc'w, hwR, hw0s⟩ : ∃ b r', rc = .Reply rv b ∧ rc' = .replyCap rv.bv r' ∧ rv ∈ Z.R ∧
      L.mem s (Endp.rTcbA rv) = 0#u64 := by
    rcases hrc with ⟨h1, -, -⟩ | h
    · exact absurd h1 hrn
    · exact h
  obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hwR
  have hxr0 : xr.replyTcb = none := by rw [hxr, hw0s, optRef_zero]
  have hkr3 : σ3.kheap rv.bv = some (.reply xr) := Fr23.replyF hkr
  have hkt3 : σ3.kheap t.bv = some (.tcb x2) := hk3 _ _ hkt2 (fun _ _ h => by cases h)
  have hsc2 : x2.tcbSchedContext = xt.tcbSchedContext := by rw [hx2]
  have hws : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  -- P1's facts at `s3`
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hIR3.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have bits3 : ∀ u ∈ Z.T, (∀ dm p, u.bv ∉ σ.readyQueues dm p) → u.bv ∉ σ.releaseQueue →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hq hr
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hq 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [← hrq3, hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hr
      rw [← Fr23.sk.rel, hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbS, hrbS⟩ := bits3 sd' hsT hnqS.1 hnqS.2
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT hnrT
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu =>
    actionW_ne_of hSR3 hu (fun h => hsw _ (act3.symm.trans h))
  have hidl3 : σ3.idleThread = σ.idleThread := Fr23.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by rw [← hct]; exact hni
  have his : sd'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hks] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA sd') ≠ 0#u64 → L.mem s3 (P1.scA sd') ∈ Ac := fun h0 =>
    hB3.sact sd' hsH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hst3))))))) h0
  have hcold : L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide,
      by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide⟩
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hwH : rv ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : rv ≠ 0#u64 := (J.rp.align rv hwR).2.1
  have hz3 : L.mem s3 (P1.rTcbA rv) = 0#u64 := by
    obtain ⟨xr', hkr', hrl⟩ := hR3.reply rv hwR
    rw [hkr3] at hkr'; cases hkr'
    exact optRef_none (hrl.symm.trans hxr0)
  have hns3 : tsCode xs.tcbState ≠ 6 := by rw [hstd]; simp [tsCode]
  have hSM := ScRelM.of hIR3.1
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM t ht
  rw [hkt3] at hkd3'; cases hkd3'
  obtain ⟨xs3', hks3', hssc⟩ := hSM sd' hsT
  rw [hks3] at hks3'; cases hks3'
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA rv) sd') (fun b => b.val = rv.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 sd'
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hXc : P1.ExcT {y' | y' ∈ (∅ : Set U64) ∨ y' = sd'} sd' := fun y' hy' => by simpa using hy'
  have hrv0 : (rv != 0#u64) = true := by simpa using hw00
  -- the donated SC `p`: the sender's
  have hpw3 : L.mem s3 (P1.scA sd') = p := by
    rw [hxsp] at hssc; exact (optRef_some_eq hssc.symm)
  have hxd2 : x2.tcbSchedContext = none := hsc2.trans hxtn
  -- the spec side: the sender `Inactive` (a spec state only), `Inv` there, as in `recvSendFPJG`
  set x5 : Fl4Spec.Tcb := { xs with tcbState := .inactive } with hx5
  have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
    show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σ.curThread; exact hsc
  set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
  have Fr5 : RSFr sd'.bv t.bv σ σ5 := Fr23.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩))
  set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
  have IK5' : IK sd'.bv σ σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
  have SK5' : Ipc.SKeep σ σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
    (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
  have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
  have hrib : RelIfBound σ5' sd'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd sd'.bv xs hks (Or.inr (Or.inr (Or.inl ⟨_, _, hstd,
      fun b' h => hnto b' (Option.some.inj (hft.symm.trans h))⟩)))) SK5'
  have I5' : Inv σ5' := ((J.inv.toBut sd'.bv).ik hnqS IK5').1.inv fun _ _ _ => hrib
  have hpsd : p.bv ≠ sd'.bv := fun h => by
    obtain ⟨y0, m0, hky0, -⟩ := J.inv.back sd'.bv xs p.bv hks hxsp
    rw [h, hks] at hky0; cases hky0
  -- `Inv` and the donated SC released at `σ5`
  have IR5 : Inv σ5 ∧ ∀ y n, σ5.kheap p.bv = some (.schedContext y n) → Fl4Spec.scActive y = true →
      released σ5 y := by
    rcases hU3 with e3 | ⟨p', y', z, n, hxp, hkp, hne', hpc, e3, hz1, hz2, hz3, hz5, hz6⟩
    · have e5 : σ5 = σ5' := by rw [hσ5, stsAct_ne hsc3, e3]
      rw [e5]
      refine ⟨I5', fun y n hy ha => ?_⟩
      exact hrib x5 p.bv y n hk5' hxsp hy ha (fun hm => hnqS.2 (by rw [SK5'.1] at hm; exact hm))
    · have hpp : p' = p.bv := Option.some.inj (hxp.symm.trans hxsp)
      subst hpp
      have hkp' : σ5'.kheap p.bv = some (.schedContext y' n) := by simp [σ5', hpsd, hkp]
      have e5 : σ5 = updSc { σ5' with reprogramTimer := true } p.bv z n := by
        rw [hσ5, stsAct_ne hsc3, e3, hσ5']
        rw [show ({ Notif.updK σ2 sd'.bv (.tcb x5) with reprogramTimer := true } : Fl4Spec.State Unit) =
          Notif.updK { σ2 with reprogramTimer := true } sd'.bv (.tcb x5) from rfl, updSc_updK_comm _ hpsd]
      rw [e5]
      refine ⟨I5'.scRef hkp' hne' hz1 hz2 hz3 hz5 hz6 (fun u hu x hx hxu => ?_), fun y1 n1 hy ha => ?_⟩
      · obtain ⟨y1, n1, hk1, ht1⟩ := I5'.back u x p.bv hx hxu
        obtain ⟨y2, n2, hk2, ht2⟩ := I5'.back sd'.bv x5 p.bv hk5' hxp
        rw [hk1] at hk2; cases hk2
        have hu' : u = sd'.bv := Option.some.inj (ht1.symm.trans ht2)
        subst hu'
        exact hnqS.2 (by rw [← SK5'.1]; exact hu)
      · have hkz : (updSc { σ5' with reprogramTimer := true } p.bv z n).kheap p.bv = some (.schedContext z n) := by
          simp [Notif.updK]
        have hy' := hkz.symm.trans hy; cases hy'
        have hya' : Fl4Spec.scActive y' = true := by rw [hz3] at ha; exact ha
        exact ⟨ready_now _ _ hz2, sufficient_of_refOK (hz1 (I5'.refills _ y' n hkp' hya' hz6))⟩
  obtain ⟨I5, hrel5⟩ := IR5
  have act5 : σ5.schedulerAction = σ.schedulerAction := by
    rw [hσ5, stsAct_ne hsc3]; exact act3
  -- the block (`pushSt`) from `σ5`
  have e5 : σ5 = Notif.updK σ3 sd'.bv (.tcb x5) := stsAct_ne hsc3
  have hkta : σ5.kheap sd'.bv = some (.tcb x5) := by rw [e5]; simp [Notif.updK]
  have hkwa : σ5.kheap rv.bv = some (.reply xr) := by rw [e5]; simp [Notif.updK, hws, hkr3]
  have heqP : pushSt σ3 sd'.bv rv.bv xr xs = pushSt σ5 sd'.bv rv.bv xr x5 := by
    rw [e5]; unfold pushSt; rw [updK3_eq σ3 sd'.bv rv.bv _ _ _ (Ne.symm hws)]; try rfl
  set σ' := pushSt σ5 sd'.bv rv.bv xr x5 with hσ'
  have G' := (ps_skD (σ := σ5) (t := sd'.bv) (w := rv.bv) (xr := xr) (xt := x5))
  have hnqSa : ∀ dm p, sd'.bv ∉ σ5.readyQueues dm p := by
    rw [e5]; show ∀ dm p, sd'.bv ∉ σ3.readyQueues dm p; rw [hrq3]; exact hnqS.1
  have hnrSa : sd'.bv ∉ σ5.releaseQueue := by rw [Fr5.sk.rel]; exact hnqS.2
  have I6 : Inv σ' := ps_inv hkta hkwa hws I5 hnqSa hnrSa
  have hscA : ∀ p y n, σ5.kheap p = some (.schedContext y n) → y.scTcb = some sd'.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨y0, hy0, ey, -⟩ := Fr5.scB hp
    rw [ey]
    exact J.bsa.tcb p y0 n sd'.bv xs hy0 (by rw [ey] at hyt; exact hyt) hks (by rw [hstd]; rfl)
  have B6 : BlockedScActive σ' := ps_bsa hkta hkwa hws hscA (Fr5.bsa J.bsa)
  have hcne1 : σ5.curThread ≠ sd'.bv := by rw [Fr5.sk.ct, hct]; exact Ne.symm hst'
  have hactP : σ'.schedulerAction = σ.schedulerAction := by
    show (pushSt σ5 sd'.bv rv.bv xr x5).schedulerAction = _
    unfold pushSt
    rw [stsAct_ne (by show sd'.bv ≠ σ5.curThread; exact Ne.symm hcne1)]
    exact act5
  have hcnP : σ'.schedulerAction = .chooseNewThread := hactP.trans hcn
  have hidT : σ5.idleThread ≠ sd'.bv := by rw [Fr5.sk.idle]; exact fun e0 => his e0.symm
  have hAI6 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hcnP] at hu; cases hu), ps_idleOK hkta hkwa hws hidT (Fr5.idleOK J.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcnP
  have hrun6 : CurRunM σ' := Or.inl (by rw [hcnP]; intro h; cases h)
  -- the objects at `σ'`
  set xP : Fl4Spec.Tcb := { x5 with tcbState := .blockedOnReply rv.bv } with hxP
  set xr' : Fl4Spec.Reply := { xr with replyTcb := some sd'.bv } with hxr'
  have hkP : σ'.kheap sd'.bv = some (.tcb xP) := ps_kt
  have hkwP : σ'.kheap rv.bv = some (.reply xr') := ps_kw hws
  have hkt5 : σ5.kheap t.bv = some (.tcb x2) := by rw [e5]; simp [Notif.updK, Ne.symm hst', hkt3]
  have hkdP : σ'.kheap t.bv = some (.tcb x2) := by rw [hσ', ps_ko (Ne.symm hst') (Ne.symm hwt)]; exact hkt5
  have hxP : xP.tcbSchedContext = some p.bv := hxsp
  obtain ⟨yP, nP, hkyP, hytP⟩ := I6.back sd'.bv xP p.bv hkP hxP
  have hpr : p.bv ≠ rv.bv := fun h => by rw [h, hkwP] at hkyP; cases hkyP
  have hptP : p.bv ≠ t.bv := fun h => by rw [h, hkdP] at hkyP; cases hkyP
  have hky5 : σ5.kheap p.bv = some (.schedContext yP nP) := by
    rw [← ps_ko (σ := σ5) (t := sd'.bv) (w := rv.bv) (xr := xr) (xt := x5) hpsd hpr]; exact hkyP
  have hyaP : Fl4Spec.scActive yP = true := hscA p.bv yP nP hky5 hytP
  have hrelP : released σ' yP := by
    have h := hrel5 yP nP hky5 hyaP
    unfold released at h ⊢; rw [G'.tm]; exact h
  have hnqP : NotQueued σ' sd'.bv := ⟨by rw [ps_rq]; exact hnqSa, by rw [ps_rel]; exact hnrSa⟩
  have hnqdP : NotQueued σ' t.bv := by
    refine ⟨by rw [ps_rq, e5]; show ∀ dm p, t.bv ∉ σ3.readyQueues dm p; rw [hrq3]; exact hnqT, ?_⟩
    rw [ps_rel, Fr5.sk.rel]; exact hnrT
  -- the stack's head at `σ'` (from `J`)
  have hfree0 : Free σ rv := ⟨xr, hkr, hxr0⟩
  obtain ⟨hdet, -, -⟩ := J.rfree rv hwR hfree0
  obtain ⟨y0, m0, hky0, -⟩ := J.inv.back sd'.bv xs p.bv hks hxsp
  have hh0 := J.stackHead hpC hky0 hdet
  have hrepl : yP.scReplies = y0.scReplies := by
    obtain ⟨y1, hy1, e1⟩ := Fr5.callKeep.1 _ _ _ hky0
    obtain ⟨y2, hy2, e2⟩ := (ps_ck hkta hkwa hws).1 _ _ _ hy1
    rw [hkyP] at hy2; cases hy2; exact e2.trans e1
  have hhP : ∀ h l, yP.scReplies = h :: l → h ≠ p.bv ∧ h ≠ rv.bv ∧ ∃ x, σ'.kheap h = some (.reply x) := by
    intro h l hr
    rw [hrepl] at hr
    obtain ⟨h1, h2, x, hx⟩ := hh0 h l hr
    have hhs : h ≠ sd'.bv := fun e0 => by rw [e0, hks] at hx; cases hx
    exact ⟨h1, h2, x, by rw [hσ', ps_ko hhs h2]; exact Fr5.replyF hx⟩
  -- the spec's donating push
  set σD := pdSt σ' sd'.bv t.bv p.bv rv.bv xP x2 xr' yP nP with hσD
  have hpushE : Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv rv.bv true σ3 = ({((), σD)}, False) := by
    rw [replyPush_don_eq hks3 hkt3 hkr3 hws hxsp hxd2, heqP]
    exact pd_eqN hkP hkdP hkyP hkwP (Ne.symm hpr) hhP hytP hst' hpsd hptP hws hwt hcnP hnqP
  have hneq : pushSt σ3 sd'.bv rv.bv xr xs ≠ σD := by
    rw [heqP]; intro e0
    have h1 : σD.kheap t.bv = some (.tcb x2) := by rw [← e0]; exact hkdP
    rw [show σD.kheap t.bv = _ from @pd_kd σ' sd'.bv t.bv p.bv rv.bv xP x2 xr' yP nP] at h1
    have h3 := congrArg (fun o => match o with | some (.tcb x) => x.tcbSchedContext | _ => none) h1
    simp only at h3; rw [hxd2] at h3; cases h3
  have hst2 : x2.tcbState = xt.tcbState := by rw [hx2]
  have hdq : Fl4Spec.ipcQueuedThreadState x2.tcbState = false := by
    rw [hst2]; exact runnable_notQ _ hrun
  have hiddP : t.bv ≠ σ'.idleThread := by rw [G'.idle, Fr5.sk.idle]; exact hit
  -- FL4: `can_donate` is true
  have hftT : (ft != fl4_abi.consts.fault.Timeout) = true := by
    rw [hft']
    have hne : L.mem s3 (tFaultA sd') ≠ fl4_abi.consts.fault.Timeout := fun e => by
      obtain ⟨b0, hb0⟩ := hxs3.faultT.1 (by rw [e]; unfold fl4_abi.consts.fault.Timeout; first | rfl | decide)
      exact hnto b0 (Option.some.inj (hft.symm.trans hb0))
    simpa using hne
  suffices HH : ipc.reply_push st arI s3 a sd' t rv true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
    have HH' : (do
        let i3 ← obj.Tcb.sc st sd' s3
        let can_donate ← if i3 != 0#u64 then ok (ft != fl4_abi.consts.fault.Timeout) else ok false
        ipc.reply_push st arI s3 a sd' t rv can_donate) ⦃ r =>
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s3 sd') ?_
      rintro i3 hi3
      have h3' : (i3 != 0#u64) = true := by
        rw [hi3, hpw3]; simpa using J.c0 p hpC
      rw [if_pos h3', hftT]; exact ok_bind_spec _ _ HH
    rcases Bool.eq_false_or_eq_true dd.senderCanGrant with hG | hG
    · by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hG, hrv0, ↓reduceIte]; exact HH'
      · simp only [hci, hftB, hg, hG, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
    · have hGR : dd.senderCanGrantReply = true := hgg.resolve_left (by rw [hG]; decide)
      by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
      · simp only [hci, hftB, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
  -- the push: link and block (`J` again), then the donation at `J`
  refine WP.spec_mono (reply_push_iC (don := true) (P := fun s' σ'' => σ'' = σD →
        ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' (D \ {rv}) s' a σ'')
      hH hP0 hP s3 a σ3 hR3 hS3 hsT hks3 hkt3 hq3 hns3 hwR hkr3 (fun _ => ht)
      (fun s' _ _ e0 => absurd e0 hneq) ?_) ?_
  · intro _ s4 hsb hR4 hS4 _ _ _ _
    rw [hpw3, heqP]
    have hsb4 : sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA rv) sd') sd' rv = ok s4 := hsb
    -- FL4's words and P1 at the block
    have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
      have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 hsT hwR hw1
      rw [hsb4, WP.spec_ok] at h; exact h
    have hb4 := P1.sched.set_blocked_on_reply.ipc s3 sd' rv Q0 R0 h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3
      hsH hqbS hrbS (hna3 sd' hsT) (hiw3 sd' hsT his) hcold hwH hw00 hz3 hcA
    rw [hsb4, WP.spec_ok] at hb4
    obtain ⟨h4, hB4, hX4, hS4', hSg4, -, -, -, -, -, -⟩ := hb4
    have hO3 := hX3.1
    obtain ⟨hrΩ3, -⟩ := P1.objs_omega hO3 hSg3.sub
    have f1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H)
        s3 (L.wr s3 (P1.rTcbA rv) sd') :=
      P1.foot_wr (h3.omega _ (hrΩ3 rv hwH).1).1 (P1.kw_sg (hO3.tcbW hwH))
    have q1 := (P1.omega_wr (v := sd') h3 (hrΩ3 rv hwH).1).1
    have f4 := P1.sched.set_blocked_on_reply.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
      (Z := P1.Heap.scBits H) (Es := P1.EH H) _ sd' rv q1 hsH
    rw [hsb4, WP.spec_ok] at f4
    have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s4 := ⟨⟨Q0, R0, h4⟩, hB4, hX4, hS4', hSg4⟩
    have hks2b : L.ksb s2 = L.ksb s := hW2.1
    have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
      hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
    have hks3b : L.ksb s3 = L.ksb s := hW3'.1
    have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
      hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3b (SzKeepC.of Fr23.szKeep) hb))
    have hfoot := footW_trans (footW_trans (footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3))
      (footW_of f1)) (footW_of f4)
    -- back to `JAtZ` at the block
    obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX ht hth hkt hW4' hfoot
    have hIu := Ju.xtop.irelK Ju.ks Ju.buf
    have htD := Ju.not_dead_of_st hsT hks (by rw [hstd]; simp [tsCode])
    have hF : IFrame (L := L) Z.th su s4 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
    have hIR4 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s4 σ' := by
      rw [← heqP]; exact IpcRel.ofSRN hR4 hS4
    have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
        (σ'.kheap q = some o ↔ σ5.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hws h1 h2
    have hkq : ∀ q ∈ D \ {rv}, σ'.kheap q.bv = σ5.kheap q.bv := fun q hq =>
      ps_ko (htD q hq) (fun e0 => hq.2 (P1.eq_of_bv e0))
    obtain ⟨V', J6⟩ := Ju.rsfr_postGR hIR4 hF hWu hblk hFu (RSFr.ofUm Fr5 umu) ps_skD
      (ps_ksub hkta hkwa hws) (ps_szKeep hkta hkwa hws) (ps_ykeep hkta hkwa hws) (ps_mcpKeep hkta hkwa hws)
      (ps_bufKeep hkta hkwa hws) (fun d _ h => ps_recvB hkta hkwa hws h) (ps_ksz hkta hkwa hws)
      (ps_kback hkta hkwa hws) (ps_ipcFr hkta hkwa hws) (ps_ck hkta hkwa hws) (fun d _ h => ps_free hkta hkwa hws h)
      (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
      I6 B6 hAI6 hcur6 hrun6 (ps_own hkta hkwa hws (Fr5.own J.own))
      (ps_off hkta hkwa hws (Fr5.off J.off)) (ps_nsc hkta hkwa hws (Fr5.nsc J.nsc))
      (ps_isorted hkta hkwa hws (Fr5.isorted J.isorted)) htD
    -- the reply's links at the block
    obtain ⟨-, hn0, hp0⟩ := Ju.rfree rv hwR hfree0
    obtain ⟨-, -, -, -, k4⟩ := Ju.cnW_keeps hWu
    have htD6 := J6.not_dead_of_st ht hkdP (by rw [hst2]; exact runnable_tsc0 _ hrun)
    refine WP.spec_mono (J6.pushDonRJW hAT hsT ht hwR hpC (Ne.symm hts) hkP hkdP hkwP hkyP rfl hxP hytP hxd2 hdq
      hiddP rfl hrelP hcnP hnqP hnqdP hyaP hdet (by rw [(k4 rv hwR).2]; exact hn0)
      (by rw [(k4 rv hwR).1]; exact hp0) htD6) ?_
    rintro ⟨s5, a5⟩ ⟨ha5, hsp5, Lst5, J7⟩
    simp only at ha5
    subst a5
    exact ⟨rfl, _, hsp5, fun _ => ⟨V', Lst5, J7⟩⟩
  rintro ⟨s5, a5⟩ ⟨ha5, σ5'', hpush, hPσ⟩
  simp only at ha5 hpush hPσ ⊢
  subst a5
  have e5'' : σ5'' = σD := by
    have h := hpush.symm.trans hpushE
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  obtain ⟨V5, Lst5, J5⟩ := hPσ e5''
  subst e5''
  -- the spec's outcome
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hyesS : (dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none :=
    ⟨by rcases hgg with h | h <;> simp [h], by rw [Notif.optRef_ne hw00]; simp⟩
  have hspec := receiveIpc_sendPushD_eq b rights blk hsr hkt hbN hk hks hse hstd hyesS e2' hA hks3
    (Or.inr (by rw [hft]; simp)) (by rw [hxsp]; simp)
    (by rw [hft]; cases f <;> simp [Fl4Spec.isTimeoutFault] <;> exact hnto _ rfl)
    (fun r hr => by rw [Notif.optRef_ne hw00] at hr; cases hr; exact hpushE)
  exact ⟨((), σD), by rw [hspec]; exact Set.mem_singleton _, J5.xtop.relTop, _, _, _, _, _, _, J5⟩


set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a calling head sender (no fault) with an SC pushing
a reply and donating the SC at `J`** (module docstring): XTopJointRecvSendP's
`JAtZ.recvSendPJG` with the donation of `JAtZ.recvSendFPDJW` (any current SC). -/
theorem JAtZ.recvSendPDJW (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    {p : U64} (hpC : p ∈ Z.C) (hxsp : xs.tcbSchedContext = some p.bv) (hxtn : xt.tcbSchedContext = none)
    (hcn : σ.schedulerAction = .chooseNewThread) (hnrT0 : t.bv ∉ σ.releaseQueue)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (hcl0 : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hyes : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) (hrn : rc ≠ .Null)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
    {m : Result (S × A)} (hm : ∀ {P : S × A → Prop}, (do
            let st1 ← obj.Ep.state st e s
            if st1 = obj.EP_IDLE then do
              let s3 ← endpoint.wait_for_sender st s t e blk rv
              ok (s3, a)
            else if st1 = obj.EP_RECV then do
              let s3 ← endpoint.wait_for_sender st s t e blk rv
              ok (s3, a)
            else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄ → m ⦃ P ⦄) :
    m ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have J := J.undeadC hcovR.1 hcovR.2 (J.replyArg_ntcb hrc)
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ Z.T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    constructor
    · intro h0; obtain ⟨_, _, _, h1⟩ := tsCode_three h0; rw [h1] at hrun; simp [Fl4Spec.runnable] at hrun
    · intro h0; obtain ⟨_, _, h1⟩ := tsCode_four h0; rw [h1] at hrun; simp [Fl4Spec.runnable] at hrun
  have hts : t ≠ sd' := by intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have hst' : sd'.bv ≠ t.bv := bv_ne (Ne.symm hts)
  have hsc : sd'.bv ≠ σ.curThread := by rw [hct]; exact hst'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hsH : sd' ∈ P1.Heap.tcbs H := J.zH.1 sd' hsT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hsta := hTP sd' hsH
  have hss : L.mem s (P1.stA sd') = sched.TS_BLOCKED_ON_SEND := by
    rw [stA_tStA, tsVals.2.2.2.1]; exact UScalar.eq_of_val_eq hs4
  have hbe : L.mem s (P1.blockA sd') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hsb
  have hdq := P1.endpoint.ep_dequeue.inv s sd' Q0 R0 h0 hsH (by simp) (Or.inl hss)
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : sd' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 sd' hsH (by simp) (Or.inl hss); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e sd' (EQ0 e) hTP hE0 hq0' hdm
  apply hm
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = sd' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := sd')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he sd' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, cc1, nc1⟩, w1⟩
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (sd' :: xs'), TL w b) :=
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
  -- the badge and the flags
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  refine WP.spec_bind (Endp.obj.Tcb.block_badge.spec s1 sd') ?_
  rintro bdg hbdg
  refine WP.spec_bind (Endp.obj.Tcb.block_flags.spec s1 sd') ?_
  rintro fl hfl
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hg : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hc : (i2 != 0#u64) = dd.senderIsCall := by
    rw [← flags_call dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi2
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  -- the transfer
  refine WP.spec_bind (J.xferStepGJ hk (epDeq (.sendEP (sd'.bv :: q)) sd'.bv) hR1 hS1 hW1 F1 hsT ht (Ne.symm hts)
    hks hkt hfs bdg (i != 0#u64) h1 hB1 hX1 hS1' hSg1) ?_
  rintro s2 ⟨x2, um2, y, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksb, hKy, hCnKy, hyk⟩
  have hncn : ∀ {q' : Fl4Spec.ObjRef} {o' : Fl4Spec.KernelObject}, σ.kheap q' = some o' →
      (∀ r cs, o' ≠ .cnode r cs) → σy.kheap q' = some o' :=
    fun hq ho => (hyk _ fun r cs h0 => ho r cs (by rw [hq] at h0; exact Option.some.inj h0)).trans hq
  have hky : σy.kheap e.bv = some (.endpoint (.sendEP (sd'.bv :: q))) := hncn hk (fun _ _ h0 => by cases h0)
  have hksy : σy.kheap sd'.bv = some (.tcb xs) := hncn hks (fun _ _ h0 => by cases h0)
  have hkty : σy.kheap t.bv = some (.tcb xt) := hncn hkt (fun _ _ h0 => by cases h0)
  have hcty : σy.curThread = σ.curThread := hKy.2.2.2.2
  set σ1y := Notif.updK σy e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) with hσ1y
  have hkt1y : σ1y.kheap t.bv = some (.tcb xt) := by simp [σ1y, hte, hkty]
  have hks1y : σ1y.kheap sd'.bv = some (.tcb xs) := by simp [σ1y, hse, hksy]
  have hk1ey : σ1y.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by simp [σ1y]
  set σ2 := Notif.updK (Endp.setUm σ1y um2) t.bv (.tcb x2) with hσ2
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1y]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, Ne.symm hte, hk1ey]
  -- the spec frame from `σy`
  have Fr1y : RSFr sd'.bv t.bv σy σ1y := RSFr.upd hky (Or.inr (Or.inr ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩))
  have Fr2c : RSFr sd'.bv t.bv (Endp.setUm σ1y um2) σ2 := by
    have h := RSFr.arch (t := sd'.bv) (σ := Endp.setUm σ1y um2) hkt1y x2.tcbArch
    rw [← hx2] at h; exact h
  have Fr2 : RSFr sd'.bv t.bv σy σ2 := (Fr1y.trans (RSFr.um _ _ σ1y um2)).trans Fr2c
  have IK1y : IK sd'.bv σy σ1y := IK.updOther (o' := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) hky
    (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1y : Ipc.SKeep σy σ1y := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have IK2 : IK sd'.bv σy σ2 := IK1y.trans ((IK.um _ σ1y um2).trans
    (IK.updTcb (σ := Endp.setUm σ1y um2) hkt1y (by rw [hx2]) (by rw [hx2]) (fun _ => by rw [hx2])))
  have SK2 : Ipc.SKeep σy σ2 := SK1y.trans ((Fl4Proofs.P3.SKeep.um σ1y um2).trans (Ipc.SKeep.updK (σ := Endp.setUm σ1y um2) (p := t.bv)
    (o := .tcb x2) (fun y' h => ⟨xt, hkt1y, by cases h; rw [hx2]⟩) (fun _ _ h => by cases h)))
  -- the sender's sporadic check, at the hole
  have hne2 : ∀ p y' n, σ2.kheap p = some (.schedContext y' n) → Fl4Spec.scActive y' = true → y'.scRefills ≠ [] :=
    fun p y' n hp ha => Jy.inv.ne p y' n (SK2.2.2.2 p y' n hp) ha
  refine WP.spec_bind (unblockHole hP0 (IpcRel.ofSRN hR2 hS2') hsT hks2 hne2 h2 hB2 hX2 hS2'' hSg2 hsH) ?_
  rintro s3 ⟨σ3, hA, hIR3, hW3, h3, hB3, hX3, hS3', hSg3, hT3, fu3, hU3⟩
  have hk3 : ∀ q' o', σ2.kheap q' = some o' → (∀ y' n, o' ≠ .schedContext y' n) → σ3.kheap q' = some o' := by
    intro q' o' hq ho
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, -, rfl, -⟩
    · exact hq
    · have hqp : q' ≠ p := fun h => by subst h; rw [hkp] at hq; cases hq; exact ho _ _ rfl
      simp [Notif.updK, hqp, hq]
  have hks3 : σ3.kheap sd'.bv = some (.tcb xs) := hk3 _ _ hks2 (fun _ _ h => by cases h)
  have hk3e := hk3 _ _ hk2e (fun _ _ h => by cases h)
  have ct3 : σ3.curThread = σ2.curThread := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]
    · rw [h]; rfl
  have act3 : σ3.schedulerAction = σ2.schedulerAction := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]
    · rw [h]; rfl
  have hR3 := hIR3.1.toE
  have hS3 := IpcRel.toSRN hIR3.1 hIR3.2
  have hxs3 := hR3.at_tcb hsT hks3
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 sd') ?_
  rintro ft hft
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 hfs]; unfold fl4_abi.consts.fault.NullFault; rfl
  -- the sender is in no queue
  have eW : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → 3328 ≤ K.val → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s3 (core.num.U64.wrapping_add sd' K) = L.mem s (core.num.U64.wrapping_add sd' K) := by
    intro K k1 k2 k3 k4 k5
    rw [hT3 sd' hsH K k1 k2, f2 sd' hsH K k3 k1 k2, f1 sd' hsH K k1 k2 k4 k5]
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [← blockA_tBlockA, P1.blockA_eq, eW _ (by simp) (by simp) (by simp) (by simp) (by simp), ← P1.blockA_eq]
    exact hbe
  have hst3 : L.mem s3 (P1.stA sd') = sched.TS_BLOCKED_ON_SEND := by
    rw [P1.stA_eq, eW _ (by simp) (by simp) (by simp) (by simp) (by simp), ← P1.stA_eq]
    exact hss
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ sd' :=
    hX3.noref hsta (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide)
      (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide)
  have hcl : dd.senderIsCall = true := hcl0 _ _ hstd
  have hsay : σy.schedulerAction = σ.schedulerAction := by
    have e := congrArg Fl4Spec.AbstractState.schedulerAction hCnKy.1; exact e
  have hidy : σy.idleThread = σ.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hCnKy.1; exact e
  have hrqy : σy.readyQueues = σ.readyQueues := by
    have e := congrArg Fl4Spec.AbstractState.readyQueues hCnKy.1; exact e
  -- the sender is in no ready or release queue
  have hnqS : NotQueued σy sd'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rq dm p _ hm
      rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rel _ hm
      rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  -- the receiver: current, without an SC, a reschedule pending
  have hcty' : σy.curThread = t.bv := hcty.trans hct
  have hrly : σy.releaseQueue = σ.releaseQueue := by
    have e := congrArg Fl4Spec.AbstractState.releaseQueue hCnKy.1; exact e
  have hnrT : t.bv ∉ σy.releaseQueue := by rw [hrly]; exact hnrT0
  have hsw : ∀ u, σy.schedulerAction ≠ .switchThread u := fun u h => by rw [hsay, hcn] at h; cases h
  have hnqT : ∀ dm p, t.bv ∉ σy.readyQueues dm p := by rw [hrqy, ← hct]; exact hnq
  -- the frames to `σ3`
  have Fr3 : RSFr sd'.bv t.bv σ2 σ3 := by
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, hpc, rfl, -, -, hz, -⟩
    · exact RSFr.refl _ _ _
    · exact (RSFr.reprog _ _ σ2).trans (RSFr.upd (σ := { σ2 with reprogramTimer := true }) hkp
        (Or.inr (Or.inl ⟨y', n, z.scRefills, rfl, by rw [← hz], hpc⟩)))
  have Fr23 : RSFr sd'.bv t.bv σy σ3 := Fr2.trans Fr3
  have hrq3 : σ3.readyQueues = σy.readyQueues := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]; exact IK2.2.1
    · rw [h]; exact IK2.2.1
  -- the reply
  have hgg := hyes _ _ hstd
  obtain ⟨wb, r', hrcw, hrc'w, hwR, hw0s⟩ : ∃ b r', rc = .Reply rv b ∧ rc' = .replyCap rv.bv r' ∧ rv ∈ Z.R ∧
      L.mem s (Endp.rTcbA rv) = 0#u64 := by
    rcases hrc with ⟨h1, -, -⟩ | h
    · exact absurd h1 hrn
    · exact h
  obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hwR
  have hxr0 : xr.replyTcb = none := by rw [hxr, hw0s, optRef_zero]
  have hkry : σy.kheap rv.bv = some (.reply xr) := hncn hkr (fun _ _ h0 => by cases h0)
  have hkr3 : σ3.kheap rv.bv = some (.reply xr) := Fr23.replyF hkry
  have hkt2 : σ2.kheap t.bv = some (.tcb x2) := by simp [σ2]
  have hkt3 : σ3.kheap t.bv = some (.tcb x2) := hk3 _ _ hkt2 (fun _ _ h => by cases h)
  have hsc2 : x2.tcbSchedContext = xt.tcbSchedContext := by rw [hx2]
  have hws : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  -- P1's facts at `s3`
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hIR3.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have bits3 : ∀ u ∈ Z.T, (∀ dm p, u.bv ∉ σy.readyQueues dm p) → u.bv ∉ σy.releaseQueue →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hq hr
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hq 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [← hrq3, hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hr
      rw [← Fr23.sk.rel, hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbS, hrbS⟩ := bits3 sd' hsT hnqS.1 hnqS.2
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT hnrT
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu =>
    actionW_ne_of hSR3 hu (fun h => hsw _ (act3.symm.trans h))
  have hidl3 : σ3.idleThread = σy.idleThread := Fr23.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σy.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σy.idleThread := by rw [hidy, ← hct]; exact hni
  have his : sd'.bv ≠ σy.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := Jy.act.2
    rw [← h, hksy] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA sd') ≠ 0#u64 → L.mem s3 (P1.scA sd') ∈ Ac := fun h0 =>
    hB3.sact sd' hsH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hst3))))))) h0
  have hcold : L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide,
      by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide⟩
  have hRe : Z.R = P1.Heap.replies H := Jy.tcbs_eq.2
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hwH : rv ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : rv ≠ 0#u64 := (Jy.rp.align rv hwR).2.1
  have hz3 : L.mem s3 (P1.rTcbA rv) = 0#u64 := by
    obtain ⟨xr', hkr', hrl⟩ := hR3.reply rv hwR
    rw [hkr3] at hkr'; cases hkr'
    exact optRef_none (hrl.symm.trans hxr0)
  have hns3 : tsCode xs.tcbState ≠ 6 := by rw [hstd]; simp [tsCode]
  have hSM := ScRelM.of hIR3.1
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM t ht
  rw [hkt3] at hkd3'; cases hkd3'
  obtain ⟨xs3', hks3', hssc⟩ := hSM sd' hsT
  rw [hks3] at hks3'; cases hks3'
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA rv) sd') (fun b => b.val = rv.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 sd'
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hXc : P1.ExcT {y' | y' ∈ (∅ : Set U64) ∨ y' = sd'} sd' := fun y' hy' => by simpa using hy'
  have hrv0 : (rv != 0#u64) = true := by simpa using hw00
  -- the donated SC `p`: the sender's
  have hpw3 : L.mem s3 (P1.scA sd') = p := by
    rw [hxsp] at hssc; exact (optRef_some_eq hssc.symm)
  have hxd2 : x2.tcbSchedContext = none := hsc2.trans hxtn
  -- the spec side: the sender `Inactive` (a spec state only), `Inv` there, as in `recvSendFPJG`
  set x5 : Fl4Spec.Tcb := { xs with tcbState := .inactive } with hx5
  have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
    show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σy.curThread; rw [hcty]; exact hsc
  set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
  have Fr5 : RSFr sd'.bv t.bv σy σ5 := Fr23.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩))
  set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
  have IK5' : IK sd'.bv σy σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
  have SK5' : Ipc.SKeep σy σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
    (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
  have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
  have hrib : RelIfBound σ5' sd'.bv :=
    Ipc.RelIfBound.of_keep (Jy.inv.rd sd'.bv xs hksy (Or.inr (Or.inr (Or.inl ⟨_, _, hstd,
      fun b' h => by rw [hfs] at h; cases h⟩)))) SK5'
  have I5' : Inv σ5' := ((Jy.inv.toBut sd'.bv).ik hnqS IK5').1.inv fun _ _ _ => hrib
  have hpsd : p.bv ≠ sd'.bv := fun h => by
    obtain ⟨y0, m0, hky0, -⟩ := Jy.inv.back sd'.bv xs p.bv hksy hxsp
    rw [h, hksy] at hky0; cases hky0
  -- `Inv` and the donated SC released at `σ5`
  have IR5 : Inv σ5 ∧ ∀ y n, σ5.kheap p.bv = some (.schedContext y n) → Fl4Spec.scActive y = true →
      released σ5 y := by
    rcases hU3 with e3 | ⟨p', y', z, n, hxp, hkp, hne', hpc, e3, hz1, hz2, hz3, hz5, hz6⟩
    · have e5 : σ5 = σ5' := by rw [hσ5, stsAct_ne hsc3, e3]
      rw [e5]
      refine ⟨I5', fun y n hy ha => ?_⟩
      exact hrib x5 p.bv y n hk5' hxsp hy ha (fun hm => hnqS.2 (by rw [SK5'.1] at hm; exact hm))
    · have hpp : p' = p.bv := Option.some.inj (hxp.symm.trans hxsp)
      subst hpp
      have hkp' : σ5'.kheap p.bv = some (.schedContext y' n) := by simp [σ5', hpsd, hkp]
      have e5 : σ5 = updSc { σ5' with reprogramTimer := true } p.bv z n := by
        rw [hσ5, stsAct_ne hsc3, e3, hσ5']
        rw [show ({ Notif.updK σ2 sd'.bv (.tcb x5) with reprogramTimer := true } : Fl4Spec.State Unit) =
          Notif.updK { σ2 with reprogramTimer := true } sd'.bv (.tcb x5) from rfl, updSc_updK_comm _ hpsd]
      rw [e5]
      refine ⟨I5'.scRef hkp' hne' hz1 hz2 hz3 hz5 hz6 (fun u hu x hx hxu => ?_), fun y1 n1 hy ha => ?_⟩
      · obtain ⟨y1, n1, hk1, ht1⟩ := I5'.back u x p.bv hx hxu
        obtain ⟨y2, n2, hk2, ht2⟩ := I5'.back sd'.bv x5 p.bv hk5' hxp
        rw [hk1] at hk2; cases hk2
        have hu' : u = sd'.bv := Option.some.inj (ht1.symm.trans ht2)
        subst hu'
        exact hnqS.2 (by rw [← SK5'.1]; exact hu)
      · have hkz : (updSc { σ5' with reprogramTimer := true } p.bv z n).kheap p.bv = some (.schedContext z n) := by
          simp [Notif.updK]
        have hy' := hkz.symm.trans hy; cases hy'
        have hya' : Fl4Spec.scActive y' = true := by rw [hz3] at ha; exact ha
        exact ⟨ready_now _ _ hz2, sufficient_of_refOK (hz1 (I5'.refills _ y' n hkp' hya' hz6))⟩
  obtain ⟨I5, hrel5⟩ := IR5
  have act5 : σ5.schedulerAction = σy.schedulerAction := by
    rw [hσ5, stsAct_ne hsc3]; exact act3
  -- the block (`pushSt`) from `σ5`
  have e5 : σ5 = Notif.updK σ3 sd'.bv (.tcb x5) := stsAct_ne hsc3
  have hkta : σ5.kheap sd'.bv = some (.tcb x5) := by rw [e5]; simp [Notif.updK]
  have hkwa : σ5.kheap rv.bv = some (.reply xr) := by rw [e5]; simp [Notif.updK, hws, hkr3]
  have heqP : pushSt σ3 sd'.bv rv.bv xr xs = pushSt σ5 sd'.bv rv.bv xr x5 := by
    rw [e5]; unfold pushSt; rw [updK3_eq σ3 sd'.bv rv.bv _ _ _ (Ne.symm hws)]; try rfl
  set σ' := pushSt σ5 sd'.bv rv.bv xr x5 with hσ'
  have G' := (ps_skD (σ := σ5) (t := sd'.bv) (w := rv.bv) (xr := xr) (xt := x5))
  have hnqSa : ∀ dm p, sd'.bv ∉ σ5.readyQueues dm p := by
    rw [e5]; show ∀ dm p, sd'.bv ∉ σ3.readyQueues dm p; rw [hrq3]; exact hnqS.1
  have hnrSa : sd'.bv ∉ σ5.releaseQueue := by rw [Fr5.sk.rel]; exact hnqS.2
  have I6 : Inv σ' := ps_inv hkta hkwa hws I5 hnqSa hnrSa
  have hscA : ∀ p y n, σ5.kheap p = some (.schedContext y n) → y.scTcb = some sd'.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨y0, hy0, ey, -⟩ := Fr5.scB hp
    rw [ey]
    exact Jy.bsa.tcb p y0 n sd'.bv xs hy0 (by rw [ey] at hyt; exact hyt) hksy (by rw [hstd]; rfl)
  have B6 : BlockedScActive σ' := ps_bsa hkta hkwa hws hscA (Fr5.bsa Jy.bsa)
  have hcne1 : σ5.curThread ≠ sd'.bv := by rw [Fr5.sk.ct, hcty']; exact Ne.symm hst'
  have hactP : σ'.schedulerAction = σy.schedulerAction := by
    show (pushSt σ5 sd'.bv rv.bv xr x5).schedulerAction = _
    unfold pushSt
    rw [stsAct_ne (by show sd'.bv ≠ σ5.curThread; exact Ne.symm hcne1)]
    exact act5
  have hcnP : σ'.schedulerAction = .chooseNewThread := hactP.trans (hsay.trans hcn)
  have hidT : σ5.idleThread ≠ sd'.bv := by rw [Fr5.sk.idle]; exact fun e0 => his e0.symm
  have hAI6 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hcnP] at hu; cases hu), ps_idleOK hkta hkwa hws hidT (Fr5.idleOK Jy.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl hcnP
  have hrun6 : CurRunM σ' := Or.inl (by rw [hcnP]; intro h; cases h)
  -- the objects at `σ'`
  set xP : Fl4Spec.Tcb := { x5 with tcbState := .blockedOnReply rv.bv } with hxP
  set xr' : Fl4Spec.Reply := { xr with replyTcb := some sd'.bv } with hxr'
  have hkP : σ'.kheap sd'.bv = some (.tcb xP) := ps_kt
  have hkwP : σ'.kheap rv.bv = some (.reply xr') := ps_kw hws
  have hkt5 : σ5.kheap t.bv = some (.tcb x2) := by rw [e5]; simp [Notif.updK, Ne.symm hst', hkt3]
  have hkdP : σ'.kheap t.bv = some (.tcb x2) := by rw [hσ', ps_ko (Ne.symm hst') (Ne.symm hwt)]; exact hkt5
  have hxP : xP.tcbSchedContext = some p.bv := hxsp
  obtain ⟨yP, nP, hkyP, hytP⟩ := I6.back sd'.bv xP p.bv hkP hxP
  have hpr : p.bv ≠ rv.bv := fun h => by rw [h, hkwP] at hkyP; cases hkyP
  have hptP : p.bv ≠ t.bv := fun h => by rw [h, hkdP] at hkyP; cases hkyP
  have hky5 : σ5.kheap p.bv = some (.schedContext yP nP) := by
    rw [← ps_ko (σ := σ5) (t := sd'.bv) (w := rv.bv) (xr := xr) (xt := x5) hpsd hpr]; exact hkyP
  have hyaP : Fl4Spec.scActive yP = true := hscA p.bv yP nP hky5 hytP
  have hrelP : released σ' yP := by
    have h := hrel5 yP nP hky5 hyaP
    unfold released at h ⊢; rw [G'.tm]; exact h
  have hnqP : NotQueued σ' sd'.bv := ⟨by rw [ps_rq]; exact hnqSa, by rw [ps_rel]; exact hnrSa⟩
  have hnqdP : NotQueued σ' t.bv := by
    refine ⟨by rw [ps_rq, e5]; show ∀ dm p, t.bv ∉ σ3.readyQueues dm p; rw [hrq3]; exact hnqT, ?_⟩
    rw [ps_rel, Fr5.sk.rel]; exact hnrT
  -- the stack's head at `σ'` (from `J`)
  have hfree0 : Free σy rv := ⟨xr, hkry, hxr0⟩
  obtain ⟨hdet, -, -⟩ := Jy.rfree rv hwR hfree0
  obtain ⟨y0, m0, hky0, -⟩ := Jy.inv.back sd'.bv xs p.bv hksy hxsp
  have hh0 := Jy.stackHead hpC hky0 hdet
  have hrepl : yP.scReplies = y0.scReplies := by
    obtain ⟨y1, hy1, e1⟩ := Fr5.callKeep.1 _ _ _ hky0
    obtain ⟨y2, hy2, e2⟩ := (ps_ck hkta hkwa hws).1 _ _ _ hy1
    rw [hkyP] at hy2; cases hy2; exact e2.trans e1
  have hhP : ∀ h l, yP.scReplies = h :: l → h ≠ p.bv ∧ h ≠ rv.bv ∧ ∃ x, σ'.kheap h = some (.reply x) := by
    intro h l hr
    rw [hrepl] at hr
    obtain ⟨h1, h2, x, hx⟩ := hh0 h l hr
    have hhs : h ≠ sd'.bv := fun e0 => by rw [e0, hksy] at hx; cases hx
    exact ⟨h1, h2, x, by rw [hσ', ps_ko hhs h2]; exact Fr5.replyF hx⟩
  -- the spec's donating push
  set σD := pdSt σ' sd'.bv t.bv p.bv rv.bv xP x2 xr' yP nP with hσD
  have hpushE : Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv rv.bv true σ3 = ({((), σD)}, False) := by
    rw [replyPush_don_eq hks3 hkt3 hkr3 hws hxsp hxd2, heqP]
    exact pd_eqN hkP hkdP hkyP hkwP (Ne.symm hpr) hhP hytP hst' hpsd hptP hws hwt hcnP hnqP
  have hneq : pushSt σ3 sd'.bv rv.bv xr xs ≠ σD := by
    rw [heqP]; intro e0
    have h1 : σD.kheap t.bv = some (.tcb x2) := by rw [← e0]; exact hkdP
    rw [show σD.kheap t.bv = _ from @pd_kd σ' sd'.bv t.bv p.bv rv.bv xP x2 xr' yP nP] at h1
    have h3 := congrArg (fun o => match o with | some (.tcb x) => x.tcbSchedContext | _ => none) h1
    simp only at h3; rw [hxd2] at h3; cases h3
  have hst2 : x2.tcbState = xt.tcbState := by rw [hx2]
  have hdq : Fl4Spec.ipcQueuedThreadState x2.tcbState = false := by
    rw [hst2]; exact runnable_notQ _ hrun
  have hiddP : t.bv ≠ σ'.idleThread := by rw [G'.idle, Fr5.sk.idle]; exact hit
  -- FL4: `can_donate` is true
  have hftT : (ft != fl4_abi.consts.fault.Timeout) = true := by
    rw [hft, (hR3.at_tcb hsT hks3).fault0.2 hfs]; unfold fl4_abi.consts.fault.Timeout; decide
  suffices HH : ipc.reply_push st arI s3 a sd' t rv true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
    have HH' : (do
        let i3 ← obj.Tcb.sc st sd' s3
        let can_donate ← if i3 != 0#u64 then ok (ft != fl4_abi.consts.fault.Timeout) else ok false
        ipc.reply_push st arI s3 a sd' t rv can_donate) ⦃ r =>
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s3 sd') ?_
      rintro i3 hi3
      have h3' : (i3 != 0#u64) = true := by
        rw [hi3, hpw3]; simpa using J.c0 p hpC
      rw [if_pos h3', hftT]; exact ok_bind_spec _ _ HH
    rcases Bool.eq_false_or_eq_true dd.senderCanGrant with hG | hG
    · simp only [hc, hcl, hg, hG, hrv0, ↓reduceIte]; exact HH'
    · have hGR : dd.senderCanGrantReply = true := hgg.resolve_left (by rw [hG]; decide)
      simp only [hc, hcl, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
  -- the push: link and block (`J` again), then the donation at `J`
  refine WP.spec_mono (reply_push_iC (don := true) (P := fun s' σ'' => σ'' = σD →
        ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR ((Z.mv Gy Z.vs).mv (Z.mv Gy Z.vs).G V) H Cs Ac Lst' (D \ {rv}) s' a σ'')
      hH hP0 hP s3 a σ3 hR3 hS3 hsT hks3 hkt3 hq3 hns3 hwR hkr3 (fun _ => ht)
      (fun s' _ _ e0 => absurd e0 hneq) ?_) ?_
  · intro _ s4 hsb hR4 hS4 _ _ _ _
    rw [hpw3, heqP]
    have hsb4 : sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA rv) sd') sd' rv = ok s4 := hsb
    -- FL4's words and P1 at the block
    have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
      have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 hsT hwR hw1
      rw [hsb4, WP.spec_ok] at h; exact h
    have hb4 := P1.sched.set_blocked_on_reply.ipc s3 sd' rv Q0 R0 h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3
      hsH hqbS hrbS (hna3 sd' hsT) (hiw3 sd' hsT his) hcold hwH hw00 hz3 hcA
    rw [hsb4, WP.spec_ok] at hb4
    obtain ⟨h4, hB4, hX4, hS4', hSg4, -, -, -, -, -, -⟩ := hb4
    have hO3 := hX3.1
    obtain ⟨hrΩ3, -⟩ := P1.objs_omega hO3 hSg3.sub
    have f1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H)
        s3 (L.wr s3 (P1.rTcbA rv) sd') :=
      P1.foot_wr (h3.omega _ (hrΩ3 rv hwH).1).1 (P1.kw_sg (hO3.tcbW hwH))
    have q1 := (P1.omega_wr (v := sd') h3 (hrΩ3 rv hwH).1).1
    have f4 := P1.sched.set_blocked_on_reply.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
      (Z := P1.Heap.scBits H) (Es := P1.EH H) _ sd' rv q1 hsH
    rw [hsb4, WP.spec_ok] at f4
    have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s4 := ⟨⟨Q0, R0, h4⟩, hB4, hX4, hS4', hSg4⟩
    have hks2b : L.ksb s2 = L.ksb y := hW2.1
    have hW3' : P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
      hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
    have hks3b : L.ksb s3 = L.ksb y := hW3'.1
    have hW4' : P1.WritesIn st y s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
      hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3b (SzKeepC.of Fr23.szKeep) hb))
    have hfoot := footW_trans (footW_trans (footW_trans F2 (footW_of fu3))
      (footW_of f1)) (footW_of f4)
    -- back to `JAtZ` at the block
    have hth : Z.th t = some .tcb := by
      obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
      exact Ipc.RelTopB.tcbT hB0' hkt
    obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs)
      Jy ht hth hkty hW4' hfoot
    have hIu := Ju.xtop.irelK Ju.ks Ju.buf
    have htD := Ju.not_dead_of_st hsT hksy (by rw [hstd]; simp [tsCode])
    have hF : IFrame (L := L) Z.th su s4 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
    have hIR4 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s4 σ' := by
      rw [← heqP]; exact IpcRel.ofSRN hR4 hS4
    have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
        (σ'.kheap q = some o ↔ σ5.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hws h1 h2
    have hkq : ∀ q ∈ D \ {rv}, σ'.kheap q.bv = σ5.kheap q.bv := fun q hq =>
      ps_ko (htD q hq) (fun e0 => hq.2 (P1.eq_of_bv e0))
    obtain ⟨V', J6⟩ := Ju.rsfr_postGR (by rw [← hKy.2.1] at hIR4; exact hIR4) hF hWu hblk hFu (RSFr.ofUm Fr5 umu) ps_skD
      (ps_ksub hkta hkwa hws) (ps_szKeep hkta hkwa hws) (ps_ykeep hkta hkwa hws) (ps_mcpKeep hkta hkwa hws)
      (ps_bufKeep hkta hkwa hws) (fun d _ h => ps_recvB hkta hkwa hws h) (ps_ksz hkta hkwa hws)
      (ps_kback hkta hkwa hws) (ps_ipcFr hkta hkwa hws) (ps_ck hkta hkwa hws) (fun d _ h => ps_free hkta hkwa hws h)
      (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
      I6 B6 hAI6 hcur6 hrun6 (ps_own hkta hkwa hws (Fr5.own Jy.own))
      (ps_off hkta hkwa hws (Fr5.off Jy.off)) (ps_nsc hkta hkwa hws (Fr5.nsc Jy.nsc))
      (ps_isorted hkta hkwa hws (Fr5.isorted Jy.isorted)) htD
    -- the reply's links at the block
    obtain ⟨-, hn0, hp0⟩ := Ju.rfree rv hwR hfree0
    obtain ⟨-, -, -, -, k4⟩ := Ju.cnW_keeps hWu
    have htD6 := J6.not_dead_of_st ht hkdP (by rw [hst2]; exact runnable_tsc0 _ hrun)
    refine WP.spec_mono (J6.pushDonRJW hAT hsT ht hwR hpC (Ne.symm hts) hkP hkdP hkwP hkyP rfl hxP hytP hxd2 hdq
      hiddP rfl hrelP hcnP hnqP hnqdP hyaP hdet (by rw [(k4 rv hwR).2]; exact hn0)
      (by rw [(k4 rv hwR).1]; exact hp0) htD6) ?_
    rintro ⟨s5, a5⟩ ⟨ha5, hsp5, Lst5, J7⟩
    simp only at ha5
    subst a5
    exact ⟨rfl, _, hsp5, fun _ => ⟨V', Lst5, J7⟩⟩
  rintro ⟨s5, a5⟩ ⟨ha5, σ5'', hpush, hPσ⟩
  simp only at ha5 hpush hPσ ⊢
  subst a5
  have e5'' : σ5'' = σD := by
    have h := hpush.symm.trans hpushE
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  obtain ⟨V5, Lst5, J5⟩ := hPσ e5''
  subst e5''
  -- the spec's outcome
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hyesS : (dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none :=
    ⟨by rcases hgg with h | h <;> simp [h], by rw [Notif.optRef_ne hw00]; simp⟩
  have hspec := receiveIpc_sendPushD_eq b rights blk hsr hkt hbN hk hks hse hstd hyesS e2' hA hks3
    (Or.inl hcl) (by rw [hxsp]; simp) (by rw [hfs]; simp)
    (fun r hr => by rw [Notif.optRef_ne hw00] at hr; cases hr; exact hpushE)
  exact ⟨((), σD), by rw [hspec]; exact Set.mem_singleton _, J5.xtop.relTop, _, _, _, _, _, _, J5⟩

end

end

end Fl4Proofs.P3
