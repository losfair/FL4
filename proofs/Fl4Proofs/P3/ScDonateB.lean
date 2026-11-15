/-
P3 (DESIGN.md §9), scheduling contexts: **`donate` of a bound SC** against
l4v `sched_context_donate` (the donation of `reply_push` and
`reply_remove`): the SC's thread `f` leaves the queues and loses the SC
(`test_reschedule`), then the SC is bound to `t`.

* `InvBut.unboundTcb`, `Inv.donatedW`: the invariant through the unbinding
  of `f` (its SC still names `f`) and the binding to `t`.
* `test_resched_refines`: FL4's current-thread and action test.
* `donate_bound_refines`, with the footprint (the scheduler words and the
  SC's `TCB` word), so it keeps the call stack.
-/
import Fl4Proofs.P3.ScCallFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **Unbinding a thread in no queue from its SC on the TCB side** restores
`Inv` from `Inv` except `rd` for that thread (the SC still names it). -/
theorem InvBut.unboundTcb {σ : State Unit} {t p : ObjRef} (h : InvBut σ t) {xt : Tcb} {ys : SchedContext}
    {ns : Nat} (hkt : σ.kheap t = some (.tcb xt)) (hyt : ys.scTcb = some t)
    (hks : σ.kheap p = some (.schedContext ys ns)) (hnq : NotQueued σ t) :
    Inv (updK σ t (.tcb { xt with tcbSchedContext := none })) := by
  have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
  set σ2 := updK σ t (.tcb { xt with tcbSchedContext := none })
  have kt : σ2.kheap t = some (.tcb { xt with tcbSchedContext := none }) := by simp [σ2, updK]
  have ko : ∀ q, q ≠ t → σ2.kheap q = σ.kheap q := fun q h1 => by simp [σ2, updK, h1]
  have hown : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p → u = t := fun u x hx hp => by
    obtain ⟨y, m, h1, h2⟩ := h.back u x p hx hp
    rw [hks] at h1; cases h1; rw [hyt] at h2; cases h2; rfl
  have tcb_b : ∀ u x, σ2.kheap u = some (.tcb x) → u ≠ t → σ.kheap u = some (.tcb x) := fun u x hx hut => by
    rw [ko u hut] at hx; exact hx
  have tcb_o : ∀ u x, σ.kheap u = some (.tcb x) → u ≠ t → σ2.kheap u = some (.tcb x) := fun u x hx hut => by
    rw [ko u hut]; exact hx
  have sc_s : ∀ q y m, σ2.kheap q = some (.schedContext y m) ↔ σ.kheap q = some (.schedContext y m) := by
    intro q y m
    by_cases e : q = t
    · subst e; rw [kt, hkt]; simp
    · rw [ko q e]
  have rt_m : ∀ u ∈ σ.releaseQueue, specRt σ2 u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y, m, h1, h2, -, h4, -⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    have hne := h.ne scp y m h4
    rw [specRt_eq (tcb_o u x h1 hut) h2 ((sc_s _ _ _).2 h4) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q y m hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y m hy => ?_, fun q y m hy ha hp0 => ?_⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    have hut : u ≠ t := fun e => hnq.1 d q (e ▸ hu)
    exact ⟨x, scp, y, m, tcb_o u x h1 hut, h2, h3, (sc_s _ _ _).2 h4, h5⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    exact ⟨x, scp, y, m, tcb_o u x h1 hut, h2, h3, (sc_s _ _ _).2 h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt_m a ha, rt_m b hb]; exact hab
  · by_cases hut : u = t
    · subst hut; intro x' scp _ _ h1 h2; rw [kt] at h1; cases h1; cases h2
    · have hx0 := tcb_b u x hx hut
      intro x' scp y m h1 h2 h3 h4 h5
      rw [hx] at h1; cases h1
      exact h.rd u x hut hx0 hc x scp y m hx0 h2 ((sc_s _ _ _).1 h3) h4 h5
  · exact h.refills q y m ((sc_s _ _ _).1 hy) ha
  · by_cases e : u = t
    · subst e; rw [kt] at hx; cases hx; cases hq
    · obtain ⟨y, m, h1, h2⟩ := h.back u x q (tcb_b u x hx e) hq
      exact ⟨y, m, (sc_s _ _ _).2 h1, h2⟩
  · have hq0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = t
      · subst e; rw [kt] at hx; cases hx
      · rw [ko q e] at hx; exact hx
    obtain ⟨y, m, h1⟩ := h.ntfnSc q x q' hq0 hq
    exact ⟨y, m, (sc_s _ _ _).2 h1⟩
  · exact h.ne q y m ((sc_s _ _ _).1 hy)
  · exact h.rr q y m ((sc_s _ _ _).1 hy) ha hp0

/-- The donated state from an SC no TCB is bound to. -/
theorem Inv.donatedW {σ : State Unit} (h : Inv σ) {p t : ObjRef} {ys : SchedContext} {ns : Nat} {xt : Tcb}
    (hks : σ.kheap p = some (.schedContext ys ns))
    (hnp : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p) (hkt : σ.kheap t = some (.tcb xt))
    (hpt : p ≠ t) (hnq : NotQueued σ t) : InvBut (donSt σ p t ys ns xt) t := by
  have h' : Inv σ := h
  -- `Inv.donated` only uses that no TCB is bound to `p`; rebuild its proof
  set σd := donSt σ p t ys ns xt
  have kt : σd.kheap t = some (.tcb { xt with tcbSchedContext := some p }) := by simp [σd, donSt, updK]
  have kp : σd.kheap p = some (.schedContext { ys with scTcb := some t } ns) := by
    simp [σd, donSt, updK, hpt]
  have ko : ∀ q, q ≠ t → q ≠ p → σd.kheap q = σ.kheap q := fun q h1 h2 => by simp [σd, donSt, updK, h1, h2]
  have tcb_o : ∀ u x, σ.kheap u = some (.tcb x) → u ≠ t → σd.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [hks] at hx; cases hx
    rw [ko u hut this]; exact hx
  have tcb_b : ∀ u x, σd.kheap u = some (.tcb x) → u ≠ t → σ.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [kp] at hx; cases hx
    rw [ko u hut this] at hx; exact hx
  have sc_o : ∀ q y m, σ.kheap q = some (.schedContext y m) → q ≠ p → σd.kheap q = some (.schedContext y m) :=
    fun q y m hq hqp => by
      have : q ≠ t := by rintro rfl; rw [hkt] at hq; cases hq
      rw [ko q this hqp]; exact hq
  have sc_b : ∀ q y m, σd.kheap q = some (.schedContext y m) →
      ∃ y0, σ.kheap q = some (.schedContext y0 m) ∧ y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax ∧
        y.scPeriod = y0.scPeriod := by
    intro q y m hq
    by_cases e : q = p
    · subst e; rw [kp] at hq; cases hq; exact ⟨ys, hks, rfl, rfl, rfl⟩
    · have : q ≠ t := by rintro rfl; rw [kt] at hq; cases hq
      rw [ko q this e] at hq; exact ⟨y, hq, rfl, rfl, rfl⟩
  have rt_m : ∀ u ∈ σ.releaseQueue, specRt σd u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y, m, h1, h2, -, h4, h5⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    have hsp : scp ≠ p := fun e => hnp u x h1 (e ▸ h2)
    have hne := h.ne scp y m h4
    rw [specRt_eq (tcb_o u x h1 hut) h2 (sc_o scp y m h4 hsp) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun q y m hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y m hy => ?_, fun q y m hy ha hp0 => ?_⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    exact ⟨x, scp, y, m, tcb_o u x h1 (fun e => hnq.1 d q (e ▸ hu)), h2, h3,
      sc_o scp y m h4 (fun e => hnp u x h1 (e ▸ h2)), h5⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact ⟨x, scp, y, m, tcb_o u x h1 (fun e => hnq.2 (e ▸ hu)), h2, h3,
      sc_o scp y m h4 (fun e => hnp u x h1 (e ▸ h2)), h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt_m a ha, rt_m b hb]; exact hab
  · have hx0 := tcb_b u x hx hut
    intro x' scp y m h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    obtain ⟨y0, hy0, hr, hm, -⟩ := sc_b scp y m h3
    have := h.rd u x hx0 hc x scp y0 m hx0 h2 hy0 (by simpa [scActive, hm] using h4) h5
    unfold released refillHd at this ⊢; rw [hr]; exact this
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    intro hper
    have := h.refills q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hper)
    unfold RefOK refillHd at this ⊢; rw [hr]; exact this
  · by_cases e : u = t
    · subst e; rw [kt] at hx; cases hx; cases hq; exact ⟨_, ns, kp, rfl⟩
    · have hx0 := tcb_b u x hx e
      obtain ⟨y, m, h1, h2⟩ := h.back u x q hx0 hq
      have : q ≠ p := fun e' => hnp u x hx0 (e' ▸ hq)
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

/-- A TCB address of `T` is not an action code. -/
theorem act_iff {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {f : U64} (hf : f ∈ T) :
    f = nodeW st s c layout.node.SCHED_ACTION ↔ σ.schedulerAction = .switchThread f.bv := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hfa := hc.tcbs f hf
  have h0 : f ≠ 0#u64 := fun e => hfa.ne0 (by rw [e]; rfl)
  have h1 : f ≠ 1#u64 := fun e => by have := hfa.align; rw [e] at this; simp at this
  have ha := hS.act
  constructor
  · intro e
    cases hσ : σ.schedulerAction with
    | resumeCurThread => rw [hσ] at ha; exact absurd (e.trans ha) h0
    | chooseNewThread => rw [hσ] at ha; exact absurd (e.trans ha) h1
    | switchThread u => rw [hσ] at ha; obtain ⟨-, -, hu⟩ := ha; rw [← e] at hu; rw [hu]
  · intro e
    rw [e] at ha; obtain ⟨-, -, hu⟩ := ha
    exact (eq_of_bv hu).symm

/-- **`donate` of an SC bound to `f` refines `sched_context_donate`.** -/
theorem donate_bound_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) {f : U64} (hf : f ∈ T) (hyf : y.scTcb = some f.bv)
    {xf : Fl4Spec.Tcb} (hkf : σ.kheap f.bv = some (.tcb xf)) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none) (hft : f ≠ t)
    (hrel : inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y) :
    schedcontext.donate st ar s a sc t ⦃ r => ∃ σ',
      Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv σ = ({((), σ')}, False) ∧ r.2 = a ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      WritesIn st s r.1 (fun b => SFoot st T c s b ∨ b = scW sc 24#u64) ∧
      σ'.kheap sc.bv = some (.schedContext { y with scTcb := some t.bv } n) ∧
      (∀ q, q ≠ sc.bv → q ≠ f.bv → q ≠ t.bv → σ'.kheap q = σ.kheap q) ∧
      σ'.kheap f.bv = some (.tcb { xf with tcbSchedContext := none }) ∧
      σ'.kheap t.bv = some (.tcb { xt with tcbSchedContext := some sc.bv }) ∧
      σ'.curThread = σ.curThread ∧ σ'.curTime = σ.curTime ∧ σ'.idleThread = σ.idleThread ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hP := hS.placed
  have hf0 : f ≠ 0#u64 := fun e => (hc.tcbs f hf).ne0 (by rw [e]; rfl)
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  have hif : i = f := by rw [hi, scTcbA_eq]; exact word24_of hS hsc hk hyf
  clear hi
  subst i
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb' : b = false := by rw [hb]; exact decide_eq_false hf0
  rw [hb']
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hpf : sc.bv ≠ f.bv := fun e => by rw [e, hkf] at hk; cases hk
  have hpt : sc.bv ≠ t.bv := fun e => by rw [e, hkt] at hk; cases hk
  have hftb : f.bv ≠ t.bv := bv_ne hft
  -- the unbinding of `f`, up to `test_reschedule`
  have P : (do
      let (s2, a2) ← smp.remote_tcb_stall st ar s a f
      let s3 ← sched.dequeue st s2 f
      let s4 ← sched.release_remove st s3 f
      let s5 ← obj.Tcb.set_sc st f s4 0#u64
      let t ← sched.cur_thread st s5
      let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq f t
      let t1 ←
        if b1 = true then sched.reschedule_required st s5
          else do
            let i1 ← sched.action st s5
            if f = i1 then sched.reschedule_required st s5 else ok s5
      ok (t1, a2)) ⦃ r1 => r1.2 = a ∧ ∃ σ4, (do
        Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedDequeue f.bv
        Fl4Spec.tcbReleaseRemove f.bv
        Fl4Spec.setTcbObjRef Fl4Spec.tcbSchedContextUpdate f.bv none
        Fl4Spec.testReschedule f.bv : Fl4Spec.SMonad Unit Unit) σ = ({((), σ4)}, False) ∧
        SchedRel st N T C c r1.1 σ4 ∧ NtfnStateRel N T (L.mem r1.1) σ4 ∧ NSC N C σ4 ∧ Inv σ4 ∧
        WritesIn st s r1.1 (SFoot st T c s) ∧ σ4.kheap sc.bv = some (.schedContext y n) ∧
        σ4.kheap f.bv = some (.tcb { xf with tcbSchedContext := none }) ∧
        (∀ q, q ≠ f.bv → σ4.kheap q = σ.kheap q) ∧ NotQueued σ4 t.bv ∧
        σ4.curThread = σ.curThread ∧ σ4.curTime = σ.curTime ∧ σ4.idleThread = σ.idleThread ⦄ := by
    refine WP.spec_bind (remote_tcb_stall_id a hS hf) ?_
    rintro ⟨s2, a2⟩ he
    simp only [Prod.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    subst s2 a2
    -- dequeue
    refine WP.spec_bind (WP.spec_and (dequeue_refines s σ hS f hf) (dequeue_sfoot hS hf)) ?_
    rintro s3 ⟨⟨σ1, hdq, -, -, hf3, hS3⟩, hw3⟩
    have e1 := pair_eq (hdq.symm.trans (tcbSchedAction_gen hkf _))
    subst e1
    set σ1 := setQ σ xf.tcbDomain xf.tcbPriority
      (Fl4Spec.tcbSchedDequeue f.bv (σ.readyQueues xf.tcbDomain xf.tcbPriority)) with hσ1
    have hR3 : NtfnStateRel N T (L.mem s3) σ1 := hR.frame hP hf3 (KView.of_kheap rfl)
    have hI1 : Inv σ1 := hI.qchange (qchange_dequeue hkf)
    have hkf1 : σ1.kheap f.bv = some (.tcb xf) := hkf
    -- release-queue removal
    refine WP.spec_bind (WP.spec_and (release_remove_refines s3 σ1 hS3 hf) (release_remove_sfoot hS3 hf)) ?_
    rintro s4 ⟨⟨σa, hra, ⟨bb, hσa⟩, hf4, hS4⟩, hw4⟩
    subst hσa
    set σ2 := setRel σ1 (σ1.releaseQueue.filter fun x => decide (f.bv ≠ x)) bb with hσ2
    have hR4 : NtfnStateRel N T (L.mem s4) σ2 := hR3.frame hP hf4 (KView.of_kheap rfl)
    have hI2 : InvBut σ2 f.bv := hI1.relRemove f.bv bb
    have hkf2 : σ2.kheap f.bv = some (.tcb xf) := hkf
    have hk2 : σ2.kheap sc.bv = some (.schedContext y n) := hk
    have hnq2 : NotQueued σ2 f.bv := by
      refine ⟨fun d q hm => ?_, fun hm => ?_⟩
      · simp only [σ2, σ1, setRel, setQ] at hm
        split at hm
        · exact (by simpa using List.mem_filter.1 hm : False)
        · rename_i hne
          exact hne (ready_only hS hf hkf hm)
      · simp only [σ2, setRel, List.mem_filter] at hm; simp at hm
    -- `f`'s SC word
    refine WP.spec_bind (obj.Tcb.set_sc.spec' s4 f 0#u64) ?_
    rintro s5 rfl
    obtain ⟨hS5, hf5, hK6⟩ := hS4.set_tcb_sc hf hkf2 (v := 0#u64) (Or.inl rfl)
    rw [optRef_zero] at hS5 hK6
    have hR5 := hR4.frame hP hf5 hK6
    have hI3 : Inv (updK σ2 f.bv (.tcb { xf with tcbSchedContext := none })) := hI2.unboundTcb hkf2 hyf hk2 hnq2
    set σ3 := updK σ2 f.bv (.tcb { xf with tcbSchedContext := none }) with hσ3
    have hN3 : NSC N C σ3 := fun m hm x q hx hq => by
      by_cases e : m.bv = f.bv
      · rw [e] at hx; simp [σ3, updK] at hx
      · simp only [σ3, updK_kheap, Function.update_of_ne e] at hx; exact hN m hm x q hx hq
    have hw5 : WritesIn st s (L.wr s4 (scA f) 0#u64) (SFoot st T c s) :=
      WritesIn.sfoot_trans (WritesIn.sfoot_trans hw3 hw4) (writesIn_tcb (K := 3464#u64) hc.tcbs hf (by unfold SOff; decide) (by simp) 0#u64)
    set s5 := L.wr s4 (scA f) 0#u64 with hs5d
    obtain ⟨Q5, R5, hc5, hs5⟩ := hS5.lists
    have hk3 : σ3.kheap sc.bv = some (.schedContext y n) := by simp [σ3, updK, hpf]; exact hk2
    have hkf3 : σ3.kheap f.bv = some (.tcb { xf with tcbSchedContext := none }) := by simp [σ3, updK]
    have hko3 : ∀ q, q ≠ f.bv → σ3.kheap q = σ.kheap q := fun q hq => by
      show Function.update σ.kheap f.bv _ q = σ.kheap q; exact Function.update_of_ne hq _ _
    -- `t` is in no queue and not schedulable
    have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [hko3 _ (Ne.symm hftb)]; exact hkt
    have hnqt : NotQueued σ t.bv := by
      refine ⟨fun d q hm => ?_, fun hm => ?_⟩
      · obtain ⟨x, _, _, _, h1, h2, -⟩ := hI.rq d q _ hm; rw [hkt] at h1; cases h1; rw [hxt0] at h2; cases h2
      · obtain ⟨x, _, _, _, h1, h2, -⟩ := hI.rel _ hm; rw [hkt] at h1; cases h1; rw [hxt0] at h2; cases h2
    have hnq3 : NotQueued σ3 t.bv := by
      refine ⟨fun d q hm => ?_, fun hm => ?_⟩
      · simp only [σ3, σ2, σ1, updK, setRel, setQ] at hm
        split at hm
        · exact hnqt.1 _ _ (List.mem_of_mem_filter hm)
        · exact hnqt.1 _ _ hm
      · simp only [σ3, σ2, updK, setRel, List.mem_filter] at hm
        exact hnqt.2 hm.1
    have hnst : Fl4Spec.schedulable t.bv σ3 = false := by
      cases h : Fl4Spec.schedulable t.bv σ3
      · rfl
      · obtain ⟨x, scp, -, -, h1, h2, -⟩ := schedulable_inv h
        rw [hkt3] at h1; cases h1; rw [hxt0] at h2; cases h2
    -- the finish, from `test_reschedule`'s outcome
    have fin : ∀ (s6 : S) (σ4 : Fl4Spec.State Unit), Fl4Spec.testReschedule (Z := Unit) f.bv σ3 = ({((), σ4)}, False) →
        QChange σ3 σ4 → Calm σ3 σ4 → SchedRel st N T C c s6 σ4 → NtfnStateRel N T (L.mem s6) σ4 →
        WritesIn st s6 s6 (SFoot st T c s6) → WritesIn st s5 s6 (SFoot st T c s5) →
        (ok (s6, a) : Result (S × A)) ⦃ r1 => r1.2 = a ∧ ∃ σ4, (do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedDequeue f.bv
          Fl4Spec.tcbReleaseRemove f.bv
          Fl4Spec.setTcbObjRef Fl4Spec.tcbSchedContextUpdate f.bv none
          Fl4Spec.testReschedule f.bv : Fl4Spec.SMonad Unit Unit) σ = ({((), σ4)}, False) ∧
          SchedRel st N T C c r1.1 σ4 ∧ NtfnStateRel N T (L.mem r1.1) σ4 ∧ NSC N C σ4 ∧ Inv σ4 ∧
          WritesIn st s r1.1 (SFoot st T c s) ∧ σ4.kheap sc.bv = some (.schedContext y n) ∧
          σ4.kheap f.bv = some (.tcb { xf with tcbSchedContext := none }) ∧
          (∀ q, q ≠ f.bv → σ4.kheap q = σ.kheap q) ∧ NotQueued σ4 t.bv ∧
          σ4.curThread = σ.curThread ∧ σ4.curTime = σ.curTime ∧ σ4.idleThread = σ.idleThread ⦄ := by
      intro s6 σ4 h4 hq4 hc4 hS6 hR6 _ hw6
      rw [WP.spec_ok]
      refine ⟨rfl, σ4, ?_, hS6, hR6, fun m hm x q hx hq => hN3 m hm x q (by rw [← hq4.1]; exact hx) hq,
        hI3.qchange hq4, WritesIn.sfoot_trans hw5 hw6, by rw [hq4.1]; exact hk3, by rw [hq4.1]; exact hkf3,
        fun q hq => by rw [hq4.1]; exact hko3 q hq, ⟨fun d q hm => ?_, by rw [hq4.2.1]; exact hnq3.2⟩,
        hc4.2.1, hc4.2.2.2.1, hc4.2.2.2.2.2.1⟩
      · rw [nd_bind_one (tcbSchedAction_gen hkf _), nd_bind_one hra]
        show (Fl4Spec.threadSet _ f.bv >>= _) σ2 = _
        rw [nd_bind_one (threadSet_eq _ hkf2)]
        exact h4
      · rcases hq4.2.2.2 d q _ hm with h | h
        · exact hnq3.1 d q h
        · rw [hnst] at h; cases h
    have htr : ∀ σ', (Fl4Spec.NonDet.when (f.bv = σ3.curThread ∨ σ3.schedulerAction = .switchThread f.bv)
        Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) →
        Fl4Spec.testReschedule (Z := Unit) f.bv σ3 = ({((), σ')}, False) := by
      intro σ' h
      unfold Fl4Spec.testReschedule
      rw [nd_gets_bind, nd_gets_bind, nd_pure_bind']
      unfold Fl4Spec.NonDet.when at h ⊢
      have hiff : (f.bv = σ3.curThread ∨ (match σ3.schedulerAction with
          | .switchThread p => f.bv = p | _ => False)) ↔
          (f.bv = σ3.curThread ∨ σ3.schedulerAction = .switchThread f.bv) := by
        cases σ3.schedulerAction <;> simp [eq_comm]
      split_ifs with h1
      · rw [if_pos (hiff.1 h1)] at h; exact h
      · rw [if_neg (fun h' => h1 (hiff.2 h'))] at h; exact h
    have hresch : ∀ σ', (Fl4Spec.NonDet.when (f.bv = σ3.curThread ∨ σ3.schedulerAction = .switchThread f.bv)
        Fl4Spec.rescheduleRequired) σ3 = ({((), σ')}, False) → True := fun _ _ => trivial
    step with sched.cur_thread.spec' as ⟨ct, hct⟩
    rw [hc5.cur] at hct
    subst hct
    unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
    simp only [bind_ok]
    have hcte : (nodeW st s5 c layout.node.CUR_THREAD).bv = σ3.curThread := hs5.curThread.symm
    -- rescheduling
    have RS : ∀ hcnd : f.bv = σ3.curThread ∨ σ3.schedulerAction = .switchThread f.bv,
        (do
          let t1 ← sched.reschedule_required st s5
          ok (t1, a)) ⦃ r1 => r1.2 = a ∧ ∃ σ4, (do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedDequeue f.bv
          Fl4Spec.tcbReleaseRemove f.bv
          Fl4Spec.setTcbObjRef Fl4Spec.tcbSchedContextUpdate f.bv none
          Fl4Spec.testReschedule f.bv : Fl4Spec.SMonad Unit Unit) σ = ({((), σ4)}, False) ∧
          SchedRel st N T C c r1.1 σ4 ∧ NtfnStateRel N T (L.mem r1.1) σ4 ∧ NSC N C σ4 ∧ Inv σ4 ∧
          WritesIn st s r1.1 (SFoot st T c s) ∧ σ4.kheap sc.bv = some (.schedContext y n) ∧
          σ4.kheap f.bv = some (.tcb { xf with tcbSchedContext := none }) ∧
          (∀ q, q ≠ f.bv → σ4.kheap q = σ.kheap q) ∧ NotQueued σ4 t.bv ∧
          σ4.curThread = σ.curThread ∧ σ4.curTime = σ.curTime ∧ σ4.idleThread = σ.idleThread ⦄ := by
      intro hcnd
      refine WP.spec_bind (WP.spec_and (reschedule_required_refines s5 σ3 hR5 hS5 hI3.actReady)
        (reschedule_required_sfoot hS5)) ?_
      rintro s6 ⟨⟨σ6, he6, hk6, -, hf6, hS6⟩, hw6⟩
      obtain ⟨σ9, he9, hq9, hc9⟩ := rescheduleRequired_calm hI3.actReady
      rw [he9] at he6
      have e := pair_eq he6
      subst e
      exact fin s6 σ6 (htr σ6 (by unfold Fl4Spec.NonDet.when; rw [if_pos hcnd]; exact he9)) hq9 hc9 hS6
        (hR5.frame hP hf6 (KView.of_kheap hk6)) (WritesIn.refl _ _) hw6
    by_cases e1 : f = nodeW st s5 c layout.node.CUR_THREAD
    · rw [if_pos (decide_eq_true e1)]
      exact RS (Or.inl (by rw [← hcte, ← e1]))
    · rw [if_neg (by simpa using e1)]
      step with sched.action.spec' as ⟨act, hact⟩
      rw [hc5.cur] at hact
      subst hact
      by_cases e2 : f = nodeW st s5 c layout.node.SCHED_ACTION
      · rw [if_pos e2]
        exact RS (Or.inr ((act_iff hS5 hf).1 e2))
      · rw [if_neg e2]
        simp only [bind_ok]
        exact fin s5 σ3 (htr σ3 (by
            unfold Fl4Spec.NonDet.when
            rw [if_neg (fun h => h.elim (fun h' => e1 (eq_of_bv (by rw [h', hcte]))) (fun h' => e2 ((act_iff hS5 hf).2 h')))]
            rfl))
          (QChange.refl σ3) (Calm.refl σ3) hS5 hR5 (WritesIn.refl _ _) (WritesIn.refl _ _)
  refine WP.spec_bind P ?_
  rintro ⟨s5, a1⟩ ⟨ha1, σ4, hsp4, hS4, hR4, hN4, hI4, hw4, hk4, hkf4, hko4, hnq4, hct4, htm4, hid4⟩
  simp only at ha1
  subst ha1
  -- the SC's `TCB` word
  refine WP.spec_bind (obj.Sc.set_tcb.spec' s5 sc t) ?_
  rintro s6 rfl
  obtain ⟨hS6, hf6, hK6⟩ := hS4.set_sc_tcb hsc hk4 t
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  rw [optRef_ne ht0] at hS6 hK6
  have hR6 := hR4.frame hP hf6 hK6
  have hkt4 : σ4.kheap t.bv = some (.tcb xt) := by rw [hko4 _ (Ne.symm hftb)]; exact hkt
  have hkt5 : (updSc σ4 sc.bv { y with scTcb := some t.bv } n).kheap t.bv = some (.tcb xt) := by
    simp only [updSc, updK_kheap, Function.update_of_ne (Ne.symm hpt)]; exact hkt4
  -- `t`'s SC word
  refine WP.spec_bind (obj.Tcb.set_sc.spec' _ t sc) ?_
  rintro s7 rfl
  obtain ⟨hS7, hf7, hK7⟩ := hS6.set_tcb_sc ht hkt5 (v := sc) (Or.inr hsc)
  rw [optRef_ne hsc0] at hS7 hK7
  have hR7 := hR6.frame hS6.placed hf7 hK7
  set σ6 := updK (updSc σ4 sc.bv { y with scTcb := some t.bv } n) t.bv
    (.tcb { xt with tcbSchedContext := some sc.bv }) with hσ6
  -- the migration (one core)
  step with obj.Sc.cpu.spec as ⟨i, hi⟩
  have hic : i = c := by rw [hi, scCoreA_eq]; exact hS7.core sc hsc
  clear hi
  subst i
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨j, hj⟩
  obtain ⟨Q7, R7, hc7, hs7⟩ := hS7.lists
  have hji : j = c := by rw [hj]; exact hc7.aff t ht
  clear hj
  subst j
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step as ⟨s8, hs8⟩
  subst hs8
  obtain ⟨hS8, hf8⟩ := hS7.wr_same (field_aligned (hc.tcbs t ht) (K := 3520#u64) (by simp) (by simp)) (hc7.aff t ht)
  -- the invariant
  have hnp : ∀ u x, σ4.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some sc.bv := by
    intro u x hx hu
    by_cases e : u = f.bv
    · subst e; rw [hkf4] at hx; cases hx; cases hu
    · obtain ⟨y', m', h1, h2⟩ := hI4.back u x sc.bv hx hu
      rw [hk4] at h1; cases h1; rw [hyf] at h2; cases h2; exact e rfl
  have hID : InvBut σ6 t.bv := hI4.donatedW hk4 hnp hkt4 hpt hnq4
  have hI6 : Inv σ6 := hID.inv fun x hx hcl => by
    intro x' scp y' m' h1 h2 h3 h4 _
    have hkt6 : σ6.kheap t.bv = some (.tcb { xt with tcbSchedContext := some sc.bv }) := by simp [σ6, updK]
    rw [hkt6] at hx; cases hx
    rw [hkt6] at h1; cases h1; cases h2
    rw [show σ6.kheap sc.bv = some (.schedContext { y with scTcb := some t.bv } n) by simp [σ6, updK, hpt]] at h3
    cases h3
    have := hrel hcl h4
    unfold released at this ⊢
    rw [show σ6.curTime = σ.curTime from htm4]; exact this
  -- the footprint
  have hw8 : WritesIn st s (L.wr (L.wr (L.wr s5 (scW sc 24#u64) t) (scA t) sc) (affA t) c)
      (fun b => SFoot st T c s b ∨ b = scW sc 24#u64) := by
    obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
    have a24 : Aligned (scW sc 24#u64) := (hx.hdr (K := 24#u64) (by simp) (by simp)).1
    have k5 : L.ksb s5 = L.ksb s := hw4.1
    have e1 : WritesIn st s5 (L.wr s5 (scW sc 24#u64) t) (· = scW sc 24#u64) := writesIn_wr a24
    have e2 : WritesIn st (L.wr s5 (scW sc 24#u64) t) (L.wr (L.wr s5 (scW sc 24#u64) t) (scA t) sc)
        (SFoot st T c (L.wr s5 (scW sc 24#u64) t)) :=
      writesIn_tcb (K := 3464#u64) hc.tcbs ht (by unfold SOff; decide) (by simp) sc
    have e3 : WritesIn st (L.wr (L.wr s5 (scW sc 24#u64) t) (scA t) sc)
        (L.wr (L.wr (L.wr s5 (scW sc 24#u64) t) (scA t) sc) (affA t) c)
        (SFoot st T c (L.wr (L.wr s5 (scW sc 24#u64) t) (scA t) sc)) :=
      writesIn_tcb (K := 3520#u64) hc.tcbs ht (by unfold SOff; decide) (by simp) c
    refine (((hw4.trans e1).trans e2).trans e3).mono fun b hb => ?_
    rcases hb with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl ((SFoot.ksb (by simp [k5])).1 h)
    · exact Or.inl ((SFoot.ksb (by simp [k5])).1 h)
  have hkσ6 : σ6.kheap sc.bv = some (.schedContext { y with scTcb := some t.bv } n) := by simp [σ6, updK, hpt]
  have hkt6 : σ6.kheap t.bv = some (.tcb { xt with tcbSchedContext := some sc.bv }) := by simp [σ6, updK]
  have hko6 : ∀ q, q ≠ sc.bv → q ≠ t.bv → σ6.kheap q = σ4.kheap q := fun q h1 h2 => by simp [σ6, updK, h1, h2]
  refine ⟨σ6, ?_, hS8, hR7.frame hS7.placed hf8 (KView.refl _), hN4.updSc.updTcb, hI6, hw8, hkσ6,
    fun q h1 h2 h3 => by rw [hko6 q h1 h3, hko4 q h2], by rw [hko6 _ (Ne.symm hpf) hftb]; exact hkf4, hkt6,
    hct4, htm4, hid4⟩
  -- the spec
  unfold Fl4Spec.schedContextDonate
  have hg : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv σ = ({(y.scTcb, σ)}, False) := by
    unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
  rw [nd_bind_one hg, hyf]
  unfold Fl4Spec.NonDet.when
  rw [if_pos (by simp)]
  have hin : (do
      let fromTptr ← Fl4Spec.NonDet.assertOpt (some f.bv)
      Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedDequeue fromTptr
      Fl4Spec.tcbReleaseRemove fromTptr
      Fl4Spec.setTcbObjRef Fl4Spec.tcbSchedContextUpdate fromTptr none
      Fl4Spec.testReschedule fromTptr : Fl4Spec.SMonad Unit Unit) σ = ({((), σ4)}, False) := by
    rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some f.bv) σ =
      ({(f.bv, σ)}, False) from rfl)]
    exact hsp4
  rw [nd_bind_one hin]
  show (Fl4Spec.updateSchedContext sc.bv _ >>= _) σ4 = _
  rw [nd_bind_one (updateSchedContext_eq hk4 _)]
  show Fl4Spec.threadSet _ t.bv _ = _
  exact threadSet_eq _ hkt5

end

end

end Fl4Proofs.P3.Sched
