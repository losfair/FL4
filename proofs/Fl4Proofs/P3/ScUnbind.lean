/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext `UnbindObject`
(thread) and `Unbind`'s TCB step** against l4v `sched_context_unbind_tcb`
and `sched_context_unbind_all_tcbs`.

* `InvBut.unbound`: unbinding a thread in no queue from its SC restores
  `Inv` from `Inv` except `rd` for that thread.
* `unbind_tcb_refines`: `unbind_tcb` of a bound SC (reschedule if the thread
  is the current one, dequeue, release-queue removal, both links cleared),
  ending in `Inv`; `ActIdle` when the action is `resume_cur_thread` at entry
  and the thread is not the idle thread.
* `unbind_all_tcbs_refines`: the same after the (single-core, proved no-op)
  TCB stall; the spec's `sc_ptr ≠ idle_sc_ptr` test is a hypothesis.
-/
import Fl4Proofs.P3.ScConfig
import Fl4Proofs.P3.ScFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **Unbinding a thread in no queue from its SC restores `Inv`** from `Inv`
except `rd` for that thread (it has no SC afterwards). -/
theorem InvBut.unbound {σ : State Unit} {t p : ObjRef} (h : InvBut σ t) {xt : Tcb} {ys : SchedContext} {ns : Nat}
    (hkt : σ.kheap t = some (.tcb xt)) (hyt : ys.scTcb = some t)
    (hks : σ.kheap p = some (.schedContext ys ns)) (hnq : NotQueued σ t) :
    Inv (updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns) := by
  have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
  set σ2 := updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns
  have kt : σ2.kheap t = some (.tcb { xt with tcbSchedContext := none }) := by simp [σ2, updK, Ne.symm hpt]
  have kp : σ2.kheap p = some (.schedContext { ys with scTcb := none } ns) := by simp [σ2, updK]
  have ko : ∀ q, q ≠ t → q ≠ p → σ2.kheap q = σ.kheap q := fun q h1 h2 => by simp [σ2, updK, h1, h2]
  -- only `t` is bound to `p`
  have hown : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p → u = t := fun u x hx hp => by
    obtain ⟨y, m, h1, h2⟩ := h.back u x p hx hp
    rw [hks] at h1; cases h1; rw [hyt] at h2; cases h2; rfl
  have tcb_b : ∀ u x, σ2.kheap u = some (.tcb x) → u ≠ t → σ.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [kp] at hx; cases hx
    rw [ko u hut this] at hx; exact hx
  have tcb_o : ∀ u x, σ.kheap u = some (.tcb x) → u ≠ t → σ2.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [hks] at hx; cases hx
    rw [ko u hut this]; exact hx
  have sc_o : ∀ q y m, σ.kheap q = some (.schedContext y m) → q ≠ p → σ2.kheap q = some (.schedContext y m) :=
    fun q y m hq hqp => by
      have : q ≠ t := by rintro rfl; rw [hkt] at hq; cases hq
      rw [ko q this hqp]; exact hq
  have sc_b : ∀ q y m, σ2.kheap q = some (.schedContext y m) →
      ∃ y0, σ.kheap q = some (.schedContext y0 m) ∧ y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax ∧
        y.scPeriod = y0.scPeriod := by
    intro q y m hq
    by_cases e : q = p
    · subst e; rw [kp] at hq; cases hq; exact ⟨ys, hks, rfl, rfl, rfl⟩
    · have : q ≠ t := by rintro rfl; rw [kt] at hq; cases hq
      rw [ko q this e] at hq; exact ⟨y, hq, rfl, rfl, rfl⟩
  have rt_m : ∀ u ∈ σ.releaseQueue, specRt σ2 u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y, m, h1, h2, -, h4, -⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    have hsp : scp ≠ p := fun e => hut (hown u x h1 (e ▸ h2))
    have hne := h.ne scp y m h4
    rw [specRt_eq (tcb_o u x h1 hut) h2 (sc_o scp y m h4 hsp) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q y m hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y m hy => ?_, fun q y m hy ha hp0 => ?_⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    have hut : u ≠ t := fun e => hnq.1 d q (e ▸ hu)
    exact ⟨x, scp, y, m, tcb_o u x h1 hut, h2, h3, sc_o scp y m h4 (fun e => hut (hown u x h1 (e ▸ h2))), h5⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    exact ⟨x, scp, y, m, tcb_o u x h1 hut, h2, h3, sc_o scp y m h4 (fun e => hut (hown u x h1 (e ▸ h2))), h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt_m a ha, rt_m b hb]; exact hab
  · by_cases hut : u = t
    · subst hut; intro x' scp _ _ h1 h2; rw [kt] at h1; cases h1; cases h2
    · have hx0 := tcb_b u x hx hut
      intro x' scp y m h1 h2 h3 h4 h5
      rw [hx] at h1; cases h1
      obtain ⟨y0, hy0, hr, hm, -⟩ := sc_b scp y m h3
      have := h.rd u x hut hx0 hc x scp y0 m hx0 h2 hy0 (by simpa [scActive, hm] using h4) h5
      unfold released refillHd at this ⊢; rw [hr]; exact this
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    intro hper
    have := h.refills q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hper)
    unfold RefOK refillHd at this ⊢; rw [hr]; exact this
  · by_cases e : u = t
    · subst e; rw [kt] at hx; cases hx; cases hq
    · have hx0 := tcb_b u x hx e
      obtain ⟨y, m, h1, h2⟩ := h.back u x q hx0 hq
      have : q ≠ p := fun e' => e (hown u x hx0 (e' ▸ hq))
      exact ⟨y, m, sc_o q y m h1 this, h2⟩
  · have hq0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = t
      · subst e; rw [kt] at hx; cases hx
      · by_cases e2 : q = p
        · subst e2; rw [kp] at hx; cases hx
        · rw [ko q e e2] at hx; exact hx
    obtain ⟨y, m, h1⟩ := h.ntfnSc q x q' hq0 hq
    by_cases e : q' = p
    · subst e; exact ⟨_, ns, kp⟩
    · exact ⟨y, m, sc_o q' y m h1 e⟩
  · obtain ⟨y0, hy0, hr, -, -⟩ := sc_b q y m hy
    rw [hr]; exact h.ne q y0 m hy0
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    exact (h.rr q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hp0)).of_refills hr

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- Replacing a TCB keeps `NSC`. -/
theorem NSC.updTcb {N C : Set U64} {σ : Fl4Spec.State Unit} (h : NSC N C σ) {t : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} : NSC N C (updK σ t (.tcb x)) := by
  intro m hm x' q hx hq
  by_cases e : m.bv = t
  · subst e; simp [updK] at hx
  · simp only [updK_kheap, Function.update_of_ne e] at hx; exact h m hm x' q hx hq

/-- **`unbind_tcb` of an SC bound to `t` refines `sched_context_unbind_tcb`.** -/
theorem unbind_tcb_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {p : U64} (hp : p ∈ C) {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p.bv = some (.schedContext y n))
    {t : U64} (ht : t ∈ T) (hyt : y.scTcb = some t.bv) :
    schedcontext.unbind_tcb st s p ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindTcb (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ.schedulerAction = .resumeCurThread → IdleOK σ → t.bv ≠ σ.idleThread → ActIdle σ') ∧
      WritesIn st s s' (fun b => SFoot st T c s b ∨ b = scW p 24#u64) ∧ CKeep σ σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -⟩ := hs.tcb t ht
  obtain ⟨xp, np, hkp, hxp⟩ := hs.scs p hp
  rw [hk] at hkp; cases hkp
  have ha24 := (hxp.hdr (K := 24#u64) (by simp) (by simp)).1
  have hP := hS.placed
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  have hpt : p.bv ≠ t.bv := fun e => by rw [e, hkt] at hk; cases hk
  unfold schedcontext.unbind_tcb
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  have hit : i = t := by rw [hi, scTcbA_eq]; exact word24_of hS hp hk hyt
  subst hit
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  simp only [hb, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  rw [hc.cur] at hct
  subst hct
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  have hct0 : (nodeW st s c layout.node.CUR_THREAD).bv = σ.curThread := hs.curThread.symm
  -- the reschedule if `t` is current
  have P1 : (if decide (i = nodeW st s c layout.node.CUR_THREAD) = true then sched.reschedule_required st s
      else ok s) ⦃ s1 => ∃ σ1, Fl4Spec.NonDet.when (i.bv = σ.curThread) Fl4Spec.rescheduleRequired σ =
        ({((), σ1)}, False) ∧ SchedRel st N T C c s1 σ1 ∧ NtfnStateRel N T (L.mem s1) σ1 ∧ QChange σ σ1 ∧
        Calm σ σ1 ∧ (σ.schedulerAction = .resumeCurThread → ∀ u, σ1.schedulerAction ≠ .switchThread u) ∧
        WritesIn st s s1 (SFoot st T c s) ⦄ := by
    by_cases he : i = nodeW st s c layout.node.CUR_THREAD
    · rw [if_pos (decide_eq_true he)]
      refine WP.spec_mono (WP.spec_and (reschedule_required_refines s σ hR hS hI.actReady)
        (reschedule_required_sfoot hS)) ?_
      rintro s1 ⟨⟨σ8, he8, hk8, -, hf8, hS8⟩, hw8⟩
      obtain ⟨σ9, he9, hq9, hc9⟩ := rescheduleRequired_calm hI.actReady
      rw [he9] at he8
      have e := pair_eq he8
      subst e
      refine ⟨σ8, by unfold Fl4Spec.NonDet.when; rw [if_pos (by rw [← hct0, he])]; exact he9, hS8,
        hR.frame hP hf8 (KView.of_kheap hk8), hq9, hc9, fun ha u => ?_, hw8⟩
      have e := rescheduleRequired_noswitch (σ := σ) (fun t h => by rw [ha] at h; cases h)
      rw [he9] at e
      rw [← pair_eq e]; intro h; cases h
    · rw [if_neg (by simpa using he), WP.spec_ok]
      refine ⟨σ, by unfold Fl4Spec.NonDet.when; rw [if_neg (fun e => he (eq_of_bv (by rw [hct0]; exact e)))]; rfl,
        hS, hR, QChange.refl σ, Calm.refl σ, (fun ha u h => by rw [ha] at h; cases h), WritesIn.refl _ _⟩
  refine WP.spec_bind P1 ?_
  rintro s1 ⟨σ1, h1, hS1, hR1, hq1, hc1, ha1, hw1⟩
  have hI1 : Inv σ1 := hI.qchange hq1
  have hkt1 : σ1.kheap i.bv = some (.tcb xt) := by rw [hq1.1]; exact hkt
  have hk1 : σ1.kheap p.bv = some (.schedContext y n) := by rw [hq1.1]; exact hk
  -- dequeue
  refine WP.spec_bind (WP.spec_and (dequeue_refines s1 σ1 hS1 i ht) (dequeue_sfoot hS1 ht)) ?_
  rintro s2 ⟨⟨σ2, hdq, hk2, hrb, hf2, hS2⟩, hw2⟩
  have e2 := pair_eq (hdq.symm.trans (tcbSchedAction_gen hkt1 _))
  subst e2
  set σ2 := setQ σ1 xt.tcbDomain xt.tcbPriority
    (Fl4Spec.tcbSchedDequeue i.bv (σ1.readyQueues xt.tcbDomain xt.tcbPriority)) with hσ2
  have hR2 : NtfnStateRel N T (L.mem s2) σ2 := hR1.frame hP hf2 (KView.of_kheap rfl)
  have hI2 : Inv σ2 := hI1.qchange (qchange_dequeue hkt1)
  have hkt2 : σ2.kheap i.bv = some (.tcb xt) := hkt1
  -- release-queue removal
  refine WP.spec_bind (WP.spec_and (release_remove_refines s2 σ2 hS2 ht) (release_remove_sfoot hS2 ht)) ?_
  rintro s3 ⟨⟨σa, hra, ⟨bb, hσa⟩, hf3, hS3⟩, hw3⟩
  subst hσa
  set σ3 := setRel σ2 (σ2.releaseQueue.filter fun x => decide (i.bv ≠ x)) bb with hσ3
  have hR3 : NtfnStateRel N T (L.mem s3) σ3 := hR2.frame hP hf3 (KView.of_kheap rfl)
  have hI3 : InvBut σ3 i.bv := hI2.relRemove i.bv bb
  have hkt3 : σ3.kheap i.bv = some (.tcb xt) := hkt1
  have hk3 : σ3.kheap p.bv = some (.schedContext y n) := hk1
  have hnq3 : NotQueued σ3 i.bv := by
    refine ⟨fun d q hm => ?_, fun hm => ?_⟩
    · simp only [σ3, σ2, setRel, setQ] at hm
      split at hm
      · exact (by simpa using List.mem_filter.1 hm : False)
      · rename_i hne
        exact hne (ready_only hS1 ht hkt1 hm)
    · simp only [σ3, setRel, List.mem_filter] at hm; simp at hm
  -- the TCB's SC word
  refine WP.spec_bind (obj.Tcb.set_sc.spec' s3 i 0#u64) ?_
  rintro s4 rfl
  obtain ⟨hS4, hf4, hK4⟩ := hS3.set_tcb_sc ht hkt3 (v := 0#u64) (Or.inl rfl)
  rw [optRef_zero] at hS4 hK4
  have hR4 := hR3.frame hP hf4 hK4
  have hk4 : (updK σ3 i.bv (.tcb { xt with tcbSchedContext := none })).kheap p.bv =
      some (.schedContext y n) := by simp only [updK_kheap, Function.update_of_ne hpt]; exact hk3
  -- the SC's TCB word
  refine WP.spec_mono (obj.Sc.set_tcb.spec' _ p 0#u64) ?_
  rintro s5 rfl
  obtain ⟨hS5, hf5, hK6⟩ := hS4.set_sc_tcb hp hk4 0#u64
  rw [optRef_zero] at hS5 hK6
  have hI5 := hI3.unbound hkt3 hyt hk3 hnq3
  have hN3 : NSC N C σ3 := fun m hm x q hx hq => hN m hm x q (by rw [← hq1.1]; exact hx) hq
  have hw : WritesIn st s (L.wr (L.wr s3 (scA i) 0#u64) (scW p 24#u64) 0#u64)
      (fun b => SFoot st T c s b ∨ b = scW p 24#u64) := by
    have w3 := WritesIn.sfoot_trans (WritesIn.sfoot_trans hw1 hw2) hw3
    have w4 := WritesIn.sfoot_trans w3 (writesIn_tcb (s := s3) (K := 3464#u64) hc.tcbs ht (by unfold SOff; decide) (by simp) 0#u64)
    have ha24' : Aligned (scW p 24#u64) := ha24
    exact (w4.trans (writesIn_wr ha24')).mono fun b hb => by
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr hb
  have hck : CKeep σ (updSc (updK σ3 i.bv (.tcb { xt with tcbSchedContext := none })) p.bv { y with scTcb := none } n) :=
    ((CKeep.of_kheap hq1.1).trans ((CKeep.updOther hkt3 (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ _ e => by cases e)).trans (CKeep.updSc hk4 rfl)))
  refine ⟨_, ?_, hS5, hR4.frame hS4.placed hf5 hK6, hN3.updTcb.updSc, hI5, fun ha0 hId hti => ?_, hw, hck⟩
  · -- the spec
    unfold Fl4Spec.schedContextUnbindTcb
    rw [nd_bind_one (getSchedContext_eq hk), hyt,
      nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some i.bv) σ = ({(i.bv, σ)}, False)
        from rfl), nd_gets_bind, nd_bind_one h1, nd_bind_one hdq, nd_bind_one hra]
    show (Fl4Spec.threadSet _ i.bv >>= _) σ3 = _
    rw [nd_bind_one (threadSet_eq _ hkt3)]
    exact updateSchedContext_eq hk4 _
  · -- `ActIdle`: no switch-thread action, the idle thread untouched
    have hip : σ.idleThread ≠ p.bv := by
      obtain ⟨xi, h1, -⟩ := hId; intro e; rw [e, hk] at h1; cases h1
    refine ActIdle.of_noswitch (IdleOK.of hId hc1.2.2.2.2.2.1 ?_ ?_) (ha1 ha0)
    · show (updSc (updK σ3 i.bv _) p.bv _ n).kheap σ.idleThread = _
      simp only [updSc, updK_kheap, Function.update_of_ne hip, Function.update_of_ne (Ne.symm hti)]
      show σ1.kheap σ.idleThread = _
      rw [hq1.1]
    · intro hm
      have hm' : σ.idleThread ∈ σ1.releaseQueue := (List.mem_filter.1 hm).1
      rwa [hq1.2.1] at hm'

/-- **`unbind_all_tcbs` refines `sched_context_unbind_all_tcbs`**, for an SC
other than the idle SC (the spec's test; FL4 has none). -/
theorem unbind_all_tcbs_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {p : U64} (hp : p ∈ C) (hpi : p.bv ≠ Fl4Spec.idleScPtr) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y n))
    (hbnd : ∀ t : U64, y.scTcb = some t.bv → t ∈ T ∧ t.bv ≠ σ.idleThread) :
    schedcontext.unbind_all_tcbs st ar s a p ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.schedContextUnbindAllTcbs (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ.schedulerAction = .resumeCurThread → ActIdle σ → ActIdle σ') ∧
      WritesIn st s r.1 (fun b => SFoot st T c s b ∨ b = scW p 24#u64) ∧ CKeep σ σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs p hp
  rw [hk] at hk'; cases hk'
  unfold schedcontext.unbind_all_tcbs
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  have hyi : y.scTcb = optRef i := by rw [hx.tcb, hi]
  by_cases hi0 : i = 0#u64
  · subst hi0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨trivial, σ, ?_, hS, hR, hN, hI, fun _ h => h, WritesIn.refl _ _, CKeep.refl σ⟩
    unfold Fl4Spec.schedContextUnbindAllTcbs
    rw [nd_bind_one (getSchedContext_eq hk), hyi, optRef_zero]
    unfold Fl4Spec.NonDet.when; rw [if_neg (by simp)]; rfl
  · have hyt : y.scTcb = some i.bv := by rw [hyi, optRef_ne hi0]
    obtain ⟨hiT, hti⟩ := hbnd i hyt
    have hne : (i != 0#u64) = true := by simpa using hi0
    simp only [hne, ↓reduceIte]
    refine WP.spec_bind (remote_tcb_stall_id a hS hiT) ?_
    rintro ⟨s1, a1⟩ he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine WP.spec_bind (unbind_tcb_refines _ σ hS hR hN hI hp hk hiT hyt) ?_
    rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, hA2, hw2, hck2⟩
    rw [WP.spec_ok]
    refine ⟨rfl, σ2, ?_, hS2, hR2, hN2, hI2, fun ha0 hA => hA2 ha0 hA.2 hti, hw2, hck2⟩
    unfold Fl4Spec.schedContextUnbindAllTcbs
    rw [nd_bind_one (getSchedContext_eq hk)]
    unfold Fl4Spec.NonDet.when; rw [if_pos ⟨by rw [hyt]; simp, hpi⟩]; exact h2

end

end

end Fl4Proofs.P3.Sched
