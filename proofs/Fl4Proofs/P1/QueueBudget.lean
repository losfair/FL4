/-
P1: `BoundInv` and `XInv` for the other callers that can make a thread
current or the switch-to candidate: `set_priority`, `end_timeslice`,
`charge_budget`, `check_budget`, `check_budget_restart`.

`end_timeslice` may deliver a timeout fault (`faults::handle_timeout`, an IPC
send to the thread's timeout handler); that is a hypothesis, like
`timer::fire` for `schedule`.
-/
import Fl4Proofs.P1.QueueRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A}

/-- An endpoint footprint keeps `BoundInv` and `XInv`. -/
theorem bx_epfoot {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e : U64} {W : List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E)
    (hWT : ∀ w ∈ W, w ∈ T) (hw : WritesIn st s s' (EpFoot W e)) :
    BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
  obtain ⟨kf, kΩ, kn⟩ := epfoot_keep h hEW he hWT hw
  have sc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp)
  have iq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s' = L.actionW s := by unfold LawfulStore.actionW; exact kn _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s' = L.curW s := by unfold LawfulStore.curW; exact kn _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW s' = L.idleW s := by unfold LawfulStore.idleW; exact kn _ (by rw [idle8]; omega) (by rw [idle8])
  obtain ⟨hr, hc⟩ := objs_omega hX.1 hsub
  refine ⟨hB.mk' sc (fun y hy hf => Or.inl (by rw [← iq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← iq y hy]; exact hf)))
    (fun haT => by rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩) (by rw [ei]; exact ⟨h.idleT, hB.idle⟩)
    (fun h0 => by rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩)
    (hB.nb ei (by rw [stA_eq]; exact kf (L.idleW s) h.idleT _ (by simp) (by simp) (by simp) (by simp)))
    (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [iq y hy] at hf) (fun hf => by rwa [iq y hy] at hf) ea ei ec
      (by rw [stA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp)) hS)), hX.keep
    (fun r hr' => ⟨kΩ _ (hr r hr').1, kΩ _ (hr r hr').2.1, kΩ _ (hr r hr').2.2⟩)
    (fun c hc' => ⟨kΩ _ (hc c hc').1, kΩ _ (hc c hc').2.1⟩) sc
    (fun y hy => kf y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => by rw [stA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp)) ?_
    (fun c hc' => kΩ _ (hsub _ (hX.1.repW c hc')))
    (fun y hy => kf y hy _ (by simp) (by simp) (by simp) (by simp)) (fun n hn => kΩ _ (hsub _ (hX.1.ntW n hn)))
    (hX.tn (TmFr.of_epfoot h hEW he hWT hw hX.1 hsub)) (fun c hc => kΩ _ (hsub _ (hX.1.snW c hc)))
    (fun y hy => kf y hy _ (by simp) (by simp) (by simp) (by simp)) (fun c hc => kΩ _ (hsub _ (hX.1.syW c hc)))
    (fun c hc => kΩ _ (hsub _ (hX.1.mxW c hc))) ei⟩
  unfold LawfulStore.cscW LawfulStore.nodeA
  rw [kn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hX.2.2.cur

/-! ## `set_priority` -/

theorem dpe_bx (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hnr : ∀ c ∈ Cs, t ∉ R c) (hrun : Runnable (L.mem s (stA t))) (hbd : L.mem s (scA t) ≠ 0#u64)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hta : L.mem s (scA t) ∈ Ac) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 prio
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
        SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ PFr st T Sg s s' ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hW : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
      (h.queued t ht).1)) ?_
  rintro s1 ⟨h1, hw1, hinq1⟩
  obtain ⟨hB1, hX1, fr1, ea1, -, -⟩ := bx_qfoot h hB hX hSg hW hc ht p128 hw1
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qq] at hf; exact absurd rfl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
                  · exact Or.inr (Or.inl hf))
  have hSg1 := hSg.fr fr1
  have hq0 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [hinq1]; split_ifs with e
    · exact andn_qq_qq _
    · exact not_not.1 e
  obtain ⟨hsb1, -, -⟩ := ext_qfoot hT hW (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw1
  step with obj.Tcb.set_prio.spec as ⟨s2, s2_post⟩
  subst s2_post
  have h2 := inv_wr_prio h1 ht hq0 hv
  obtain ⟨hB2, hX2⟩ := bx_field (K := 3448#u64) (v := prio) h1 hB1 hX1 hSg.sub ht (by simp) (by simp) (by simp) (by simp)
  have hS2 := SCsOK.field (K := 3448#u64) (v := prio) h1 (hS.fr fr1) hX1 ht (by simp) (by simp) (by simp)
  have hSg2 : SgOK st Ω Sg (L.wr s1 (prioA t) prio) :=
    ⟨hSg1.sub, fun b hb => by rw [L.ksb_wr]; exact hSg1.ks b hb, fun o h1' h2' => by rw [L.ksb_wr]; exact hSg1.ksΩ o h1' h2'⟩
  have st2 : L.mem (L.wr s1 (prioA t) prio) (stA t) = L.mem s (stA t) :=
    (prio_wr_eps h1 ht).2.trans (hsb1 t ht).1
  have sc2 : L.mem (L.wr s1 (prioA t) prio) (scA t) = L.mem s (scA t) := by
    rw [← fr1.sc t ht, scA_eq]
    exact L.mem_wr_ne (field_aligned (hT t ht) (by simp) (by simp)) (field_aligned (hT t ht) (by simp) (by simp))
      (fun e => field_ne (hT t ht) (hT t ht) (by simp) (by simp) (fun _ => by simp) (UScalar.eq_of_val_eq e))
  have rf2 : (L.mem (L.wr s1 (prioA t) prio) (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact hnr _ (h2.aff t ht) ((h2.released t ht).1 hcn)
  refine WP.spec_bind (sched.enqueue.sch _ t _ R h2 hB2 hSg2 ht (fun _ => rf2) (fun _ => st2 ▸ hrun)
    (fun _ => sc2 ▸ hbd) (fun _ => by rw [sc2]; exact hta)) ?_
  rintro s3 ⟨⟨⟨Q3, R3, h3⟩, hB3, f3⟩, -, -, -⟩
  have fr2 := fr_field (Sg := Sg) (K := 3448#u64) (v := prio) h1 hSg1 ht (by simp) (by simp) (by simp)
  exact WP.spec_mono (sched.reschedule_required.sch s3 Q3 R3 h3 hB3 (hSg2.fr f3)) fun s4 h4 =>
    ⟨h4.1.bnd, (hX2.fr f3).fr h4.1.fr, (hS2.fr f3).fr h4.1.fr, (hSg2.fr f3).fr h4.1.fr,
      PFr.of_fr (fr1.trans (fr2.trans (f3.trans h4.1.fr))) (Or.inr h4.2.1)⟩

theorem running_bx (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hrun : Runnable (L.mem s (stA t)))
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hbcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) → L.mem s (scA t) ≠ 0#u64)
    (hacur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) → L.mem s (scA t) ∈ Ac)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) :
    (do
      let b ← sched.queued st s t
      if b = true then do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 prio
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3
      else do
        let t1 ← sched.cur_thread st s
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
        if b1 = true then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 prio
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else obj.Tcb.set_prio st t s prio) ⦃ s' => BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
          SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ PFr st T Sg s s' ⦄ := by
  step as ⟨b, b_post⟩
  split
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    have htq := (h.queued t ht).1 hq1
    exact dpe_bx s t prio Q R h ht hv (fun c hc => h.QR (h.aff t ht) (h.prio t ht) htq hc) hrun
      (hB.q t ht hq1) hB hX hSg hS (hB.sact t ht (Or.inl hq1) (hB.q t ht hq1))
  · step as ⟨t1, t1_post⟩
    step as ⟨b1, b1_post⟩
    split
    · have e : t = t1 := by simpa [b1_post] using ‹b1 = true›
      have hr0 := hcur (e.trans t1_post)
      exact dpe_bx s t prio Q R h ht hv (fun c hc => h.notR ht hr0 hc) hrun (hbcur (e.trans t1_post)) hB hX hSg hS
        (hacur (e.trans t1_post))
    · step as ⟨s1, s1_post⟩
      subst s1_post
      obtain ⟨b1, b2⟩ := bx_field (K := 3448#u64) (v := prio) h hB hX hSg.sub ht (by simp) (by simp) (by simp) (by simp)
      exact ⟨b1, b2, SCsOK.field (K := 3448#u64) h hS hX ht (by simp) (by simp) (by simp),
        ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
        PFr.of_fr (fr_field (K := 3448#u64) h hSg ht (by simp) (by simp) (by simp))
          (Or.inl (act_wr_field (h.nodes _ h.cur) ht (h.tcbs t ht) rfl (by simp) (by simp)))⟩

theorem blocked_bx (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hb : Blocked (L.mem s (stA t)))
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (reorder : S → U64 → obj.Tcb → Result S)
    (hfoot : ∀ (s : S) (ep : U64) (xs : List U64), TcbPlaced T → EpPlaced T ep →
      QueueRel (L.mem s) T .Ep (L.epQ s ep) xs → t ∈ xs → reorder s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      reorder s1 i t) ⦃ s' => BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
        SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ PFr st T Sg s s' ⦄ := by
  have hsub := hSg.sub
  step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
  subst s1_post
  have h1 := inv_wr_prio h ht hq0 hv
  have hS1 := SCsOK.field (K := 3448#u64) (v := prio) h hS hX ht (by simp) (by simp) (by simp)
  obtain ⟨hB1, hX1⟩ := bx_field (K := 3448#u64) (v := prio) h hB hX hsub ht (by simp) (by simp) (by simp) (by simp)
  obtain ⟨hbl, hstt⟩ := prio_wr_eps (prio := prio) h ht
  step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
  subst i_post
  obtain ⟨E, EQ, hEW⟩ := h1.eps
  obtain ⟨he, hmem⟩ := hEW.2.2.2.2.1 t ht (by simp) (by rw [hstt]; exact hb)
  obtain ⟨hE, -, hq⟩ := hEW.1 _ he
  refine WP.spec_mono (hfoot _ _ _ h1.tcbs hE hq hmem) fun s2 hw => ?_
  obtain ⟨b1, b2⟩ := bx_epfoot h1 hB1 hX1 hsub hEW he hq.mem hw
  obtain ⟨kf, kΩ, kn⟩ := epfoot_keep h1 hEW he hq.mem hw
  obtain ⟨-, hcΩ⟩ := objs_omega hX1.1 hsub
  refine ⟨b1, b2, SCsOK.keep hS1 hX1 hw.1 (fun y hy => by rw [scA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp))
    ?_ (fun c hc => ⟨kΩ _ (hcΩ c hc).2.2.1, kΩ _ (hcΩ c hc).2.2.2.1, kΩ _ (hcΩ c hc).2.2.2.2⟩)
    (fun c hc => kΩ _ (spor_omega hX1.1 hc)) (fun c hc => kΩ _ (hsub _ (hX1.1.repW c hc))),
    ⟨hsub, fun b hb => by rw [hw.1, L.ksb_wr]; exact hSg.ks b hb,
      fun o h1' h2' => by rw [hw.1, L.ksb_wr]; exact hSg.ksΩ o h1' h2'⟩,
    (PFr.of_fr (fr_field (K := 3448#u64) (v := prio) h hSg ht (by simp) (by simp) (by simp))
      (Or.inl (act_wr_field (h.nodes _ h.cur) ht (h.tcbs t ht) rfl (by simp) (by simp)))).trans
      ⟨fun y hy => by rw [scA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp),
        fun y hy => by rw [stA_eq]; exact kf y hy _ (by simp) (by simp) (by simp) (by simp),
        fun b hb => kΩ b (hsub b hb),
        by unfold LawfulStore.idleW; exact kn _ (by rw [idle8]; omega) (by rw [idle8]),
        Or.inl (by unfold LawfulStore.actionW; exact kn _ (by rw [act_val]; omega) (by rw [act_val]))⟩⟩
  unfold LawfulStore.cscW LawfulStore.nodeA
  rw [kn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; rfl

/-- `set_priority` keeps `BoundInv` and `XInv` (with the invariant, by
`set_priority.inv`), when the current thread is bound. -/
theorem sched.set_priority.all (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hbcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) → L.mem s (scA t) ≠ 0#u64)
    (hacur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) → L.mem s (scA t) ∈ Ac)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) :
    sched.set_priority st s t prio ⦃ s' => (∃ Q', SchedQueuesInv st T Cs Ω H s' Q' R) ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ PFr st T Sg s s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (sched.set_priority.inv s t prio Q R h ht hv hcur) ?_) fun s' hh => hh
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  unfold sched.set_priority
  step as ⟨sv, sv_post⟩
  subst sv_post
  split
  · exact running_bx s t prio Q R h ht hv (Or.inl ‹_›) hcur hbcur hacur hB hX hSg hS
  · split
    · exact running_bx s t prio Q R h ht hv (Or.inr (Or.inl ‹_›)) hcur hbcur hacur hB hX hSg hS
    · split
      · exact running_bx s t prio Q R h ht hv (Or.inr (Or.inr ‹_›)) hcur hbcur hacur hB hX hSg hS
      · have hnr : ¬ Runnable (L.mem s (stA t)) := by rintro (e | e | e) <;> contradiction
        have hq0 := notQ_of_not_runnable h ht hnr
        have fe := fun (s : S) ep xs hT hE hq hm => endpoint.reorder_ep.foot (st := st) (T := T) s ep t xs hT hE hq hm
        have fn := fun (s : S) ep xs hT hE hq hm =>
          notification.reorder_ntfn.foot (st := st) (T := T) s ep t xs hT hE hq hm
        split
        · exact blocked_bx s t prio Q R h ht hv hq0 (Or.inr (Or.inl ‹_›)) hB hX hSg hS _ fe
        · split
          · exact blocked_bx s t prio Q R h ht hv hq0 (Or.inl ‹_›) hB hX hSg hS _ fe
          · split
            · exact blocked_bx s t prio Q R h ht hv hq0 (Or.inr (Or.inr ‹_›)) hB hX hSg hS _ fn
            · step as ⟨s1, s1_post⟩
              subst s1_post
              obtain ⟨b1, b2⟩ := bx_field (K := 3448#u64) (v := prio) h hB hX hSg.sub ht (by simp) (by simp) (by simp) (by simp)
              exact ⟨b1, b2, SCsOK.field (K := 3448#u64) h hS hX ht (by simp) (by simp) (by simp),
                ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
                PFr.of_fr (fr_field (K := 3448#u64) h hSg ht (by simp) (by simp) (by simp))
                  (Or.inl (act_wr_field (h.nodes _ h.cur) ht (h.tcbs t ht) rfl (by simp) (by simp)))⟩
end

end Fl4Proofs.P1
