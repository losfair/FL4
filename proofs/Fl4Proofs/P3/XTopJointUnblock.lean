/-
P3 (DESIGN.md §9), IPC: **the reply's sporadic unblock check at `J`**
(`JAtZ.replyUnblockJ`; toward `JReplyRestHyp`: `do_reply_transfer`, after
`reply_remove`, runs `refill_unblock_check` on the receiver's SC when it is
sporadic and not the current SC, l4v
`if_sporadic_cur_sc_test_refill_unblock_check`).

* `JAtZ.unblockJ`: FL4's `unblock_check` of an active SC `p`, not the
  current SC, bound to an `Inactive` thread, from `JAtZ` to `JAtZ` (an SC
  step: FL4 side `unblock_check_refines` / `unblock_check_kfoot`, P1's
  `sporadic.unblock_check.all`/`.kw` for `BlkOK` and the debug word; spec
  side `ScTKw (fun _ => False)`, `LK`, `SOK`, `BK`; `Inv` by `Inv.unblock`,
  the only thread bound to `p` (`Inv.back`) not in the release queue since
  it is `Inactive`; `ActIdle.unblock`; the current thread's facts since only
  the SC at `p ≠ curSc` changes).
* `JAtZ.replyUnblockJ`: the reply's code (the SC word, the sporadic flag,
  the core's `CUR_SC` node word, then `unblock_check` or nothing) against
  the spec's `getTcbObjRef … >>= ifSporadicCurScTestRefillUnblockCheck`, as
  IpcSchedLift's `unblock_top` but from `JAtZ` to `JAtZ`; every TCB and the
  current thread kept, every SC's `REFILL_MAX` (so its activeness) and bound
  thread kept.
-/
import Fl4Proofs.P3.XTopJointRunPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`unblock_check` at `J`** (module docstring). -/
theorem JAtZ.unblockJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    {p : U64} (hp : p ∈ Z.C) (hxsc : x.tcbSchedContext = some p.bv) (hpc : p.bv ≠ σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap p.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) :
    sporadic.unblock_check st s p ⦃ s' => ∃ σ', Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.curThread = σ.curThread ∧
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
      ∃ z, σ'.kheap p.bv = some (.schedContext z n) := by
    rcases unblock_result hky hne mem with ⟨rfl, -⟩ | ⟨z, rfl, -, -, -, -⟩
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, y, hky⟩
    · exact ⟨fun q hq => by simp [updK, hq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, z, by simp [updK]⟩
  obtain ⟨hkp, e_ct, e_csc, e_tm, e_cons, e_rel, e_idle, e_act, z, hkz⟩ := hF
  refine ⟨σ', he, hkp, e_ct, ?_⟩
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
  -- the invariant: the only thread bound to `p` is `t`, `Inactive`, so in no release queue
  have hI' : Inv σ' := by
    refine J.inv.unblock hky hne (fun _ _ u hu xu hku hsu => ?_) mem
    obtain ⟨y1, n1, hk1, hyt1⟩ := J.inv.back u xu p.bv hku hsu
    obtain ⟨y2, n2, hk2, hyt2⟩ := J.inv.back t.bv x p.bv hk hxsc
    rw [hk1] at hk2; cases hk2
    have hut : u = t.bv := Option.some.inj (hyt1.symm.trans hyt2)
    subst hut
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J.inv.rel _ hu
    rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hsok⟩
  -- the current thread's facts: only the SC at `p ≠ curSc` changes
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
    rcases J.own with ⟨u, hu, xu, hku, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · exact Or.inl ⟨u, hu, xu, htk' _ _ hku, by rw [e_csc]; exact hxs,
        fun y1 n1 hy => hown y1 n1 (by rw [← hkcs]; exact hy), by rw [e_cons, e_rel]; exact hnr⟩
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

set_option maxHeartbeats 8000000 in
/-- **The reply's sporadic unblock check at `J`** (module docstring). -/
theorem JAtZ.replyUnblockJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    {X : Type} (k : S → Result X) (P : X → Prop)
    (hc : ∀ (s' : S) (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = ({((), σ')}, False) →
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' →
      (∀ q xq, σ.kheap q = some (.tcb xq) → σ'.kheap q = some (.tcb xq)) → σ'.curThread = σ.curThread →
      (∀ q y n, σ'.kheap q = some (.schedContext y n) → ∃ y0, σ.kheap q = some (.schedContext y0 n) ∧
        y.scRefillMax = y0.scRefillMax ∧ y.scTcb = y0.scTcb) →
      k s' ⦃ P ⦄) :
    (do
      let i2 ← obj.Tcb.sc st t s
      let b1 ← sporadic.sc_sporadic st s i2
      let s2 ←
        if b1
        then
          do
          let i3 ← obj.Sc.cpu st i2 s
          let i4 ← obj.node_get st s i3 layout.node.CUR_SC
          if i2 != i4
          then sporadic.unblock_check st s i2
          else ok s
        else ok s
      k s2) ⦃ P ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have hspec0 : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)
      (optRef (L.mem s (scA t)))) σ := by
    unfold Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hk), hsct]
  have skip : (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t)))) σ =
      ({((), σ)}, False) → k s ⦃ P ⦄ := fun h =>
    hc s σ Lst (by rw [hspec0, h]) J (fun _ _ h => h) rfl (fun _ y _ h => ⟨y, h, rfl, rfl⟩)
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact skip (by rw [h0, optRef_zero]; rfl)
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : ∀ (P : Prop) [Decidable P] (Q : Prop) [Decidable Q],
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
        (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
          Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    intro _ _ _ _
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
  have hif' := hif True True
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact skip (by rw [hif', ite_f (fun h => hsp' (hsp.1 h.1))])
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with obj.Sc.cpu.spec as ⟨cpu, hcpu⟩
  have hcpu' : cpu = Z.c := by rw [hcpu, Fl4Proofs.P3.Sched.scCoreA_eq]; exact hS.core _ hscC
  step with obj.node_get.spec as ⟨i4, hi4⟩
  rw [hcpu'] at hi4
  by_cases e : L.mem s (scA t) = nodeW st s Z.c layout.node.CUR_SC
  · have : (L.mem s (scA t) != i4) = false := by rw [hi4]; simpa [nodeW] using e
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact skip (by rw [hif', ite_f]; rw [e, ← hs.curSc]; simp)
  · have : (L.mem s (scA t) != i4) = true := by rw [hi4]; simpa [nodeW] using e
    simp only [this, ↓reduceIte]
    have hpc : (L.mem s (scA t)).bv ≠ σ.curSc := by rw [hs.curSc]; exact bv_ne e
    have hxsc : x.tcbSchedContext = some (L.mem s (scA t)).bv := by
      rw [hsct, Notif.optRef_ne h0]
    have hya : Fl4Spec.scActive y = true := hy.active_of_rmax (hy.spor hsp')
    refine WP.spec_bind (J.unblockJ ht hk hrs hscC hxsc hpc hky hya) ?_
    rintro s' ⟨σ', he, hkp, hct, Lst', J'⟩
    refine hc s' σ' Lst' ?_ J' (fun q xq hq => ?_) hct (fun q y' n' hq => ?_)
    · rw [hspec0, hif', ite_t ⟨hsp.2 hsp', hpc⟩, he]
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hky] at hq; cases hq
      · rw [hkp q eq]; exact hq
    · by_cases eq : q = (L.mem s (scA t)).bv
      · subst eq
        have mem : ((), σ') ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) (L.mem s (scA t)).bv σ).1 := by
          rw [he]; exact Set.mem_singleton _
        rcases unblock_result hky (J.inv.ne _ y n hky hya) mem with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hz, -⟩
        · exact ⟨y', hq, rfl, rfl⟩
        · simp [Notif.updK] at hq
          obtain ⟨h1, h2⟩ := hq
          subst h1 h2
          exact ⟨y, hky, (by rw [hz]), (by rw [hz])⟩
      · rw [hkp q eq] at hq; exact ⟨y', hq, rfl, rfl⟩

end

end

end Fl4Proofs.P3
