/-
P3 (DESIGN.md §9), IPC: **`send_ipc` to a waiting receiver at `J`** (toward
XTopJointIpcJ's `JSendRestHyp`).

* `JAtZ.unblockRJ`: XTopJointUnblock's `JAtZ.unblockJ` for an SC whose
  bound thread is in no release queue (not only an `Inactive` one), with the
  frame facts of `refill_unblock_check` (`unblock_result`).
* `JAtZ.sendUnblockJ`: FL4's `unblock_sporadic` (the SC word, the sporadic
  flag, the current SC) of a thread in no release queue against the spec's
  `ifSporadicCurScTestRefillUnblockCheck` of its SC, from `JAtZ` to `JAtZ`.
* `JAtZ.sendSwitchJ`: `possible_switch_to` of a runnable thread in no
  release queue whose SC (if any) is active: `JAtZ.switchJ` (schedulable),
  or nothing on either side without an SC.
* `JAtZ.sendTailJ`: the receiver's tail of `send_ipc` (`unblock_sporadic`,
  `possible_switch_to`) against `specWakeTailE`.
* `JAtZ.sendRecvJ0`: the plain send to the head receiver; the transfer by
  XTopJointXferG's `JAtZ.xferStepGJ` (any grant; the frames rebuilt from its
  base `σy`), back to `JAtZ` by `JAtZ.bufRebaseX` at its base before
  `JAtZ.wake_postD`.
-/
import Fl4Proofs.P3.XTopJointXferG
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecD
open Fl4Spec

/-- The spec's `send_ipc` to a waiting receiver `d` (non-call, the sender
without a fault), a donation asked only where `d` has an SC (so none
happens): `sendIpc_recv_eq` for any `canDonate`. -/
theorem sendIpc_recv_eqD {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) {e' : ObjRef} {rep : Option ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' rep dd) (blk : Bool) (badge : Badge) (g gr don : Bool)
    {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) rep σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hf3 : xt3.tcbFault = none)
    (hkd3 : σ3.kheap d = some (.tcb x3)) (hdon : don = false ∨ x3.tcbSchedContext ≠ none) :
    sendIpc (Z := Unit) blk false badge g gr don t e σ =
      specWakeTailE d (stsAct (updK σ3 d (.tcb { x3 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  have hnd : ¬ (don = true ∧ x3.tcbSchedContext = none) := by
    rintro ⟨h1, h2⟩
    rcases hdon with h | h
    · rw [h] at h1; cases h1
    · exact h h2
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3), hf3]
    simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [nd_when_false_bind (by exact hnd), nd_bind_one (Notif.setThreadState_eq _ hkd3)]
    rfl

end SpecD

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`unblock_check` at `J`, the SC's thread in no release queue** (module
docstring). -/
theorem JAtZ.unblockRJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnr : t.bv ∉ σ.releaseQueue)
    {p : U64} (hp : p ∈ Z.C) (hxsc : x.tcbSchedContext = some p.bv) (hpc : p.bv ≠ σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap p.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) :
    sporadic.unblock_check st s p ⦃ s' => ∃ σ', Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.curThread = σ.curThread ∧
      σ'.idleThread = σ.idleThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
      (∃ z, σ'.kheap p.bv = some (.schedContext z n) ∧ z.scRefillMax = y.scRefillMax ∧ z.scTcb = y.scTcb) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR : NtfnStateRel Z.N Z.T (L.mem s) σ := hX.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have h0 : L.mem s (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct.symm.trans hxsc)).1
  have hst : L.mem s (scA t) = p := P1.eq_of_bv (Notif.optRef_some (hsct.symm.trans hxsc)).2
  obtain ⟨y', n', hky', hy'⟩ := hs.scs p hp
  rw [hky] at hky'; cases hky'
  have hmx : (L.rmax s p).val ≠ 0 := hy'.rmax_ne hya
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨⟨Q1, R1, hq1⟩, hB, hXi, hSc, hSg⟩ := J.blk
  obtain ⟨hiS, -, -⟩ := hXi.2.2.bound t htH h0
  rw [hst] at hiS
  have hiA : p ∈ Ac := (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))
  have hp0 : p ≠ 0#u64 := fun e => h0 (by rw [hst]; exact e)
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (unblock_check_refines s σ hS hp hmx)
    (unblock_check_kfoot hS hp hmx))
    (Fl4Proofs.P1.sporadic.unblock_check.all s t p hq1 hB hXi hSc hSg htH hst.symm hp0 hiA))
    (Fl4Proofs.P1.sporadic.unblock_check.kw (Es := P1.EH H) s t p hq1 hB hXi hSc hSg htH hst.symm hp0 hiA)) ?_
  rintro s' ⟨⟨⟨⟨σ', he, hfe, hkv, hS'⟩, hw⟩, hq2, hB2, hX2, hS2, hSg2, -⟩, hfoot⟩
  have mem : ((), σ') ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hne : y.scRefills ≠ [] := J.inv.ne _ y n hky hya
  have hF : (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧
      σ'.curTime = σ.curTime ∧ σ'.consumedTime = σ.consumedTime ∧ σ'.releaseQueue = σ.releaseQueue ∧
      σ'.idleThread = σ.idleThread ∧ σ'.schedulerAction = σ.schedulerAction ∧
      ∃ z, σ'.kheap p.bv = some (.schedContext z n) ∧ z.scRefillMax = y.scRefillMax ∧ z.scTcb = y.scTcb := by
    rcases unblock_result hky hne mem with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hz, -⟩
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, y, hky, rfl, rfl⟩
    · exact ⟨fun q hq => by simp [updK, hq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, z, by simp [updK],
        by rw [hz], by rw [hz]⟩
  obtain ⟨hkp, e_ct, e_csc, e_tm, e_cons, e_rel, e_idle, e_act, z, hkz, hzm, hzt⟩ := hF
  refine ⟨σ', he, hkp, e_ct, e_idle, e_rel, ⟨z, hkz, hzm, hzt⟩, ?_⟩
  -- the spec frame
  have hK0 : ScTKw (fun _ => False) σ σ' := nkt_refillUnblockCheck p.bv σ _ mem
  have hK : ScTKw (fun q => q = t.bv) σ σ' := hK0.ofFalse
  have hL : LK (fun _ => False) σ σ' := lkm_refillUnblockCheck p.bv σ _ mem
  have hFK : FK σ σ' := ⟨e_csc, e_idle, hK0.isc⟩
  have hsok : SOK (true, true) σ σ' := pres_refillUnblockCheck (f := (true, true)) p.bv σ _ mem
  have hBK : BK σ σ' := bkm_of (nkt_refillUnblockCheck _) (MaxK.mk_refillUnblockCheck' _) σ _ mem
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ' := hR.frame hS.placed hfe hkv
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT hK hS' hR' id
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  -- the invariant: the only thread bound to `p` is `t`, in no release queue
  have hI' : Inv σ' := by
    refine J.inv.unblock hky hne (fun _ _ u hu xu hku hsu => ?_) mem
    obtain ⟨y1, n1, hk1, hyt1⟩ := J.inv.back u xu p.bv hku hsu
    obtain ⟨y2, n2, hk2, hyt2⟩ := J.inv.back t.bv x p.bv hk hxsc
    rw [hk1] at hk2; cases hk2
    have hut : u = t.bv := Option.some.inj (hyt1.symm.trans hyt2)
    subst hut
    exact hnr hu
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hsok⟩
  have hkcs : σ'.kheap σ'.curSc = σ.kheap σ.curSc := by rw [e_csc]; exact hkp _ (Ne.symm hpc)
  have htk : ∀ q xq, σ'.kheap q = some (.tcb xq) → σ.kheap q = some (.tcb xq) := by
    intro q xq h
    by_cases e : q = p.bv
    · rw [e, hkz] at h; cases h
    · rwa [hkp q e] at h
  have htk' : ∀ q xq, σ.kheap q = some (.tcb xq) → σ'.kheap q = some (.tcb xq) := by
    intro q xq h
    by_cases e : q = p.bv
    · rw [e, hky] at h; cases h
    · rwa [hkp q e]
  have hC' : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J.cur with e | hC
    · left; rw [e_act]; exact e
    · right
      obtain ⟨xc, hkc, hcs, hnb⟩ := hC.tcb
      refine ⟨⟨xc, by rw [e_ct]; exact htk' _ _ hkc, by rw [e_csc]; exact hcs, hnb⟩, ?_, ?_, ?_⟩
      · rw [hkcs]; exact hC.sc
      · intro hne' y2 n2 hy; rw [hkcs] at hy; rw [e_csc, hK0.isc] at hne'; exact hC.active hne' y2 n2 hy
      · rw [e_ct, e_rel]; exact hC.notRel
  have hown' : CurOwnW Z.T Z.C σ' := by
    rcases J.own with ⟨u, hu, xu, hku, hxs, hown, hnr'⟩ | ⟨hcs, hun⟩
    · exact Or.inl ⟨u, hu, xu, htk' _ _ hku, by rw [e_csc]; exact hxs,
        fun y1 n1 hy => hown y1 n1 (by rw [← hkcs]; exact hy), by rw [e_cons, e_rel]; exact hnr'⟩
    · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y1 n1 hy => hun y1 n1 (by rw [← hkcs]; exact hy)⟩
  have hoff : OffOK σ' := by
    intro h0' y1 n1 hy ha
    rw [e_cons] at h0' ⊢; rw [e_tm]; rw [hkcs] at hy; rw [e_csc, hK0.isc] at ha
    exact J.off h0' y1 n1 hy ha
  have hAI : ActIdle σ' := J.act.unblock hky hne mem
  have hcr : CurRunM σ' := by
    rcases J.curRun with h | h
    · left; rw [e_act]; exact h
    · right
      rcases h with h | h
      · left; intro y1 hy; rw [e_ct] at hy; exact h y1 (htk _ _ hy)
      · right; rw [e_ct, e_idle]; exact h
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK0 (fun _ hp => hp.elim) hL hFK hAI.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2))
    (J.sc_kern hwT hK hFK hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hC' hown' hoff hAI
    (J.bsa.bk hBK hsok) hcr ⟨⟨Q1, R1, hq2⟩, hB2, hX2, hS2, hSg2⟩ hKd (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2).1 J.zD⟩

/-- What `sendUnblockJ` keeps of the spec's state. -/
def UnblockKeep (σ σ' : Fl4Spec.State Unit) : Prop :=
  (∀ q xq, σ.kheap q = some (.tcb xq) → σ'.kheap q = some (.tcb xq)) ∧ σ'.curThread = σ.curThread ∧
    σ'.idleThread = σ.idleThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
    (∀ q y n, σ'.kheap q = some (.schedContext y n) → ∃ y0, σ.kheap q = some (.schedContext y0 n) ∧
      y.scRefillMax = y0.scRefillMax ∧ y.scTcb = y0.scTcb)

set_option maxHeartbeats 8000000 in
/-- **`unblock_sporadic` at `J`** (module docstring). -/
theorem JAtZ.sendUnblockJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnr : t.bv ∉ σ.releaseQueue) :
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ = ({((), σ')}, False) ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ∧ UnblockKeep σ σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have skip : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      ({((), σ)}, False) → ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ = ({((), σ')}, False) ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst' D s a σ' ∧ UnblockKeep σ σ' := fun h =>
    ⟨σ, Lst, by rw [hsct]; exact h, J, fun _ _ h => h, rfl, rfl, rfl, fun _ y _ h => ⟨y, h, rfl, rfl⟩⟩
  unfold endpoint.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [h0, optRef_zero]; rfl)
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
        Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    rw [Notif.optRef_ne h0]
    unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hky), nd_gets_bind, nd_pure_bind']
    simp only [Fl4Spec.NonDet.when]
    by_cases e : y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
    · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
        Bool.false_eq_true, IsEmpty.forall_iff]
    · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
      rw [ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
        ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
      rfl
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f (fun h => hsp' (hsp.1 h.1))])
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc0.cur]
  by_cases e : L.mem s (scA t) = nodeW st s Z.c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f]; rw [e, ← hs.curSc]; simp)
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    have hpc : (L.mem s (scA t)).bv ≠ σ.curSc := by rw [hs.curSc]; exact bv_ne e
    have hxsc : x.tcbSchedContext = some (L.mem s (scA t)).bv := by
      rw [hsct, Notif.optRef_ne h0]
    have hya : Fl4Spec.scActive y = true := hy.active_of_rmax (hy.spor hsp')
    refine WP.spec_mono (J.unblockRJ ht hk hnr hscC hxsc hpc hky hya) ?_
    rintro s' ⟨σ', he, hkp, hct, hid, hrl, ⟨z, hkz, hzm, hzt⟩, Lst', J'⟩
    refine ⟨σ', Lst', ?_, J', fun q xq hq => ?_, hct, hid, hrl, fun q y' n' hq => ?_⟩
    · rw [hsct, hif, ite_t ⟨hsp.2 hsp', hpc⟩, he]
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hky] at hq; cases hq
      · rw [hkp q eq]; exact hq
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hkz] at hq; cases hq
        exact ⟨y, by rw [eq]; exact hky, hzm, hzt⟩
      · rw [hkp q eq] at hq; exact ⟨y', hq, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `J`** of a runnable thread in no release queue
with an active SC or none (module docstring). -/
theorem JAtZ.sendSwitchJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hnr : t.bv ∉ σ.releaseQueue)
    (hact : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  cases hsc : x.tcbSchedContext with
  | some p =>
    obtain ⟨y, n, hky, -⟩ := J.inv.back _ _ _ hk hsc
    exact J.switchJ ht hti htc (schedulable_of hk hsc hrun hky (hact p y n hsc hky) hnr)
  | none =>
    have hS := J.xtop.fin.1.1.1
    obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
    obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
    rw [hk] at hkt; cases hkt
    have h0 : L.mem s (scA t) = 0#u64 := by
      by_contra h0
      rw [Notif.optRef_ne h0] at hsct
      rw [hsc] at hsct; cases hsct
    unfold sched.possible_switch_to
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
    rw [hi, h0]
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, Lst, J⟩
    unfold Fl4Spec.possibleSwitchTo Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hk)]
    simp only [hsc, nd_gets_bind]
    rw [nd_when_false (by simp)]
    rfl

set_option maxHeartbeats 4000000 in
/-- **The receiver's tail of `send_ipc` at `J`** (module docstring). -/
theorem JAtZ.sendTailJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hnr : t.bv ∉ σ.releaseQueue)
    (hact : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) :
    (do
      let s6 ← endpoint.unblock_sporadic st s t
      let s7 ← sched.possible_switch_to st s6 t
      ok (s7, a)) ⦃ r => r.2 = a ∧ ∃ σ', Endp.specWakeTailE t.bv σ = ({((), σ')}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  refine WP.spec_bind (J.sendUnblockJ ht hk hnr) ?_
  rintro s6 ⟨σ6, Lst6, hU, J6, hkt6, hct6, hid6, hrl6, hsc6⟩
  have hk6 := hkt6 _ _ hk
  have hact6 : ∀ p y n, x.tcbSchedContext = some p → σ6.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    obtain ⟨y0, hy0, hm, -⟩ := hsc6 p y n hy
    have := hact p y0 n hp hy0
    simp only [Fl4Spec.scActive] at this ⊢
    rw [hm]; exact this
  refine WP.spec_bind (J6.sendSwitchJ ht hk6 hrun (by rw [hrl6]; exact hnr) hact6 (by rw [hid6]; exact hti)
    (by rw [hct6]; exact htc)) ?_
  rintro s7 ⟨σ7, h7, Lst7, J7⟩
  refine (WP.spec_ok _).2 ⟨rfl, σ7, ?_, Lst7, J7⟩
  unfold Endp.specWakeTailE Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk), nd_bind_one hU, h7]


set_option maxHeartbeats 64000000 in
/-- **`send_ipc` to a waiting receiver at `J`, without a call, a donation
(`can_donate` only toward a receiver with an SC, `hdon`: then neither side
donates), a fault or a cap transferred** (module docstring): FL4's dequeue,
transfer (`xferStepJ`, with or without a receive buffer), reply unlink and `Running` on `IRel` with the footprint `CnW`
(`ep_dequeue_c`, `do_ipc_transfer_regsJ` with `IpcBufCapOK` carried,
`reply_unlink_c`, `set_thread_state_c`), P1's `BlkOK` through the
receiver's hole (`ep_dequeue.inv`, `xfer_all`, `reply_unlink.inv`,
`sts_all`) and its footprint `KW`, the spec's frame `CFr` (the receiver
woken as a cancelled receive: its TCB from receive-blocked to `Running`
with a new user context, the endpoint's queue shrunk, its reply unbound),
`Inv` by `InvBut.ik`; `JAtZ` by ScSignalDonJ's `JAtZ.wake_postD`; then the
tail `JAtZ.sendTailJ`; the spec's outcome `sendIpc_recv_eqD`. -/
theorem JAtZ.sendRecvJ0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrs : xt.tcbState = .restart) (hft : xt.tcbFault = none) (hct : σ.curThread = t.bv)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hdon : don = false ∨ ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none) :
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
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by rw [hrs]; decide
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
  have SK1 : SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (J.xferStepGJ hk (epDeq (.recvEP (d'.bv :: q)) d'.bv) hR1 hS1 hW1 F1 ht hdT htd hkt hkd hft
    badge g h1 hB1 hX1 hS1' hSg1) ?_
  rintro s2 ⟨x2, um2, y, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksy, hKy, -, hyk⟩
  have hncn : ∀ {q' : Fl4Spec.ObjRef} {o' : Fl4Spec.KernelObject}, σ.kheap q' = some o' →
      (∀ r cs, o' ≠ .cnode r cs) → σy.kheap q' = some o' :=
    fun hq ho => (hyk _ fun r cs h0 => ho r cs (by rw [hq] at h0; exact Option.some.inj h0)).trans hq
  have hky : σy.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := hncn hk (fun _ _ h0 => by cases h0)
  have hkdy : σy.kheap d'.bv = some (.tcb xd) := hncn hkd (fun _ _ h0 => by cases h0)
  have hkty : σy.kheap t.bv = some (.tcb xt) := hncn hkt (fun _ _ h0 => by cases h0)
  have hcty : σy.curThread = σ.curThread := hKy.2.2.2.2
  set σ1y := Notif.updK σy e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1y
  have hkt1y : σ1y.kheap t.bv = some (.tcb xt) := by simp [σ1y, hte, hkty]
  have hkd1y : σ1y.kheap d'.bv = some (.tcb xd) := by simp [σ1y, hde, hkdy]
  have hk1ey : σ1y.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1y]
  have Fr1y : CFr e.bv d'.bv σy σ1y := CFr.upd hky (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1y : IK d'.bv σy σ1y := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hky (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1y : SKeep σy σ1y := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have hq1y : ∀ e'' ∈ Z.E, ∀ z, σ1y.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    refine hq1 e'' he'' z ?_
    by_cases hee : e''.bv = e.bv
    · rw [hee] at hz ⊢; rw [hk1ey] at hz; rw [hk1e]; exact hz
    · simp only [σ1y, Notif.updK_kheap, Function.update_of_ne hee] at hz
      simp only [σ1, Notif.updK_kheap, Function.update_of_ne hee]
      exact keepC_back hKy.1 hz (fun _ _ h0 => by cases h0)
  set σ2 := Notif.updK (Endp.setUm σ1y um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1y]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1ey]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1y e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨⟨d', hdT, (a_reply hda).2⟩, ?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have Fr2 : CFr e.bv d'.bv σy σ2 := (Fr1y.trans (CFr.um _ _ σ1y um2)).trans (CFr.upd (σ := Endp.setUm σ1y um2) hkd1y
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σy σ2 := IK1y.trans ((IK.um _ σ1y um2).trans (IK.updSelf (σ := Endp.setUm σ1y um2) hkd1y hxsc))
  have SK2 : SKeep σy σ2 := SK1y.trans ((SKeep.um σ1y um2).trans (SKeep.updK (σ := Endp.setUm σ1y um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1y, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb y := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) ∧
      P1.WritesIn st y s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) y b ∨ RcvBufW xd b) ∧
      CFr e.bv d'.bv σy σ3 ∧ IK d'.bv σy σ3 ∧ SKeep σy σ3 ∧ σ3.curThread = σy.curThread ∧
      σ3.schedulerAction = σy.schedulerAction ∧
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
        by rw [hst2']; simp [tsCode], hxsc, hq2, hW2, F2, Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
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
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
        simp [σ2, σ1y, hwe, hwd, hncn hkr (fun _ _ h0 => by cases h0)]
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
      have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := by
        show d'.bv ≠ σy.curThread; rw [hcty]; exact hdc
      have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc], ?_, hW3',
        footW_trans F2 (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
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
      · have IK3a : IK d'.bv σy σ3a := IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2 (fun o0 h => by
          rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        have IK3b : IK d'.bv σy (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
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
  refine WP.spec_bind (Pₘ := fun r : S × A => r = (s3, a)) ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 hi1
    have hf0 : i1 = fl4_abi.consts.fault.NullFault := by
      rw [hi1, hxt3.fault0.2 hft]; unfold fl4_abi.consts.fault.NullFault; rfl
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    cases don with
    | false => exact (WP.spec_ok _).2 rfl
    | true =>
      rw [if_pos rfl]
      step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
      have hne : i2 ≠ 0#u64 := by
        obtain ⟨Q3, R3', -, hs3⟩ := hS3.1.1.2.1.lists
        obtain ⟨x3', hk3', -, -, hsc', -⟩ := hs3.tcb d' hdT
        rw [hkd3] at hk3'; cases hk3'
        intro h0
        rw [hi2] at h0
        rw [h0, optRef_zero, hsc3] at hsc'
        rcases hdon with h | h
        · cases h
        · exact h xd hkd hsc'
      rw [if_neg hne]
      exact (WP.spec_ok _).2 rfl
  rintro _ rfl
  try dsimp only
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 hdT hkd3 hq3 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR3 hS3).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s3 d' _ Q0 R0 h3 hB3 hX3 hS3' hSg3 hdH P1.not_blocked_running P1.running_ne hx3 hnr3
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 d' sched.TS_RUNNING h3 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ5 := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσ5
  have hks3 : L.ksb s3 = L.ksb y := hW3.1
  have hIR := IpcRel.ofSRN hR5 hS5
  have hW5' : P1.WritesIn st y s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xd b) :=
    hW3.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr hXc3)⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans F3 (footW_of fu5)
  have Fr5 : CFr e.bv d'.bv σy σ5 := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σy (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σy σ5 := IK5a.trans (IK.sts _ _ _)
  have SK5 : SKeep σy σ5 := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hnqD : NotQueued σy d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rq dm p _ hm
      rw [hkdy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rel _ hm
      rw [hkdy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σ5 d'.bv :=
    Ipc.RelIfBound.of_keep (Jy.inv.rd d'.bv xd hkdy (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σ5 := ((Jy.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σ5.schedulerAction = σy.schedulerAction := by
    rw [hσ5, stsAct_ne (by show d'.bv ≠ σ3.curThread; rw [hct3, hcty]; exact hdc)]; exact hact3
  have hAI5 : ActIdle σ5 := ⟨fun u hu => Fr5.sched (Jy.act.1 u (by rw [← act5]; exact hu)), Fr5.idleOK Jy.act.2⟩
  have hcur5 : σ5.schedulerAction = .chooseNewThread ∨ CurInv σ5 :=
    Jy.cur.imp (fun e0 => by rw [act5]; exact e0) Fr5.curInv
  have hrun5 : CurRunM σ5 := Jy.curRun.of_cn Fr5.curRunW (Or.inr act5)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs) Jy hdT hdth hkdy
    hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hdT hkdy (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σy umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D su _ (Endp.setUm σy umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkdy (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  obtain ⟨V', J5⟩ := Ju.wake_postD (by rw [← hKy.2.1] at hIR; exact hIR) hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) I5 (Fr5.bsa Jy.bsa) hAI5
    hcur5 hrun5 hRR htD ⟨d', hdT, rfl⟩
  -- the tail
  have hk5 : σ5.kheap d'.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ5.releaseQueue := by rw [SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ5.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hy0 := SK5.2.2.2 p y n hy
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := Jy.inv.back _ _ _ hkdy hp'
    rw [hy0] at hky'; cases hky'
    exact Jy.bsa.tcb p y n d'.bv xd hy0 hyt hkdy (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ5.idleThread := by
    rw [Fr5.sk.idle]
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := Jy.act.2
    rw [← h, hkdy] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ σ5.curThread := by rw [Fr5.sk.ct, hcty]; exact hdc
  have hdon3 : don = false ∨ x3.tcbSchedContext ≠ none := hdon.imp_right fun h => by
    rw [hsc3]; exact h xd hkd
  have hspec := sendIpc_recv_eqD hk hkd hde hstd blk badge.bv g gr don e2 hU hkt3 hft hkd3 hdon3 (t := t.bv)
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec, h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

end

end

end Fl4Proofs.P3
