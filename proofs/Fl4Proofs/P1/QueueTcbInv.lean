/-
P1: the scheduler side of the TCB invocations: `set_mcp` and
`set_priority` keep `BlkOK` (with `SCsOK` and `SgOK`) and have a `KW`
footprint.
-/
import Fl4Proofs.P1.QueueFinSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-! ## `set_mcp` -/

theorem obj.Tcb.set_mcp.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_mcp st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3440#u64) v ⦄ := by
  unfold obj.Tcb.set_mcp layout.tcb.MCP layout.tcb.F; step*
  have e : i = 3440#u64 := by apply UScalar.eq_of_val_eq; simp [i_post]
  rw [s'_post, i1_post, e]

/-- A write of a TCB field no invariant reads (the `MCP` field, say). -/
theorem plainW_all {s : S} {t K v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hK : 192 ≤ K.val) (hK' : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3464 ∧ K.val ≠ 3360 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592 ∧ K.val ≠ 3368 ∧ K.val ≠ 3472)
    (hKt : K.val < 3528 ∨ 3592 ≤ K.val)
    (hKq : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3520 ∧ K.val ≠ 3448 ∧
      K.val ≠ 3336) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      ANI st s (L.wr s (core.num.U64.wrapping_add t K) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨b1, b2⟩ := bx_field (K := K) (v := v) h0 hB hX hSg.sub ht hK' hK8 hKn hKt
  exact ⟨⟨⟨Q, R, inv_wr_field h0 ht hK' hK8 ⟨hKq.1, hKq.2.1, hKq.2.2.1, hKq.2.2.2.1, hKn.2.2.2.1, hKq.2.2.2.2.1,
      hKq.2.2.2.2.2.1, hKn.2.2.1, hKq.2.2.2.2.2.2⟩⟩, b1, b2,
    SCsOK.field h0 hS hX ht hK' hK8 hKn.1,
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    foot_field h0.tcbs ht hK hK' hK8 hKd, ani_field h0.tcbs (h0.nodes _ h0.cur) ht hK' hK8⟩

/-- `set_mcp`. -/
theorem obj.Tcb.set_mcp.blk (s : S) (t : obj.Tcb) (v : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    obj.Tcb.set_mcp st t s v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧
      ANI st s s' ⦄ :=
  WP.spec_mono (obj.Tcb.set_mcp.wr s t v) fun s' e => by
    subst e
    exact plainW_all h ht (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

/-! ## `set_priority`: the footprint -/

section kw
variable {X : Set U64} {Es : Set U64}

theorem dpe_kw (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hnr : ∀ c ∈ Cs, t ∉ R c) (hrun : Runnable (L.mem s (stA t))) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 prio
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (h.queued t ht).1)) (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t h ht)) ?_
  rintro s1 ⟨⟨h1, hw1, -⟩, f1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨hsb1, -, -⟩ := ext_qfoot h.tcbs hW1 (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  step with obj.Tcb.set_prio.spec as ⟨s2, s2_post⟩
  subst s2_post
  have f2 : Foot st T Cs Sg Scs Z Es s1 (L.wr s1 (prioA t) prio) :=
    foot_field h1.tcbs ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)
  have h2 := inv_wr_prio h1 ht hq1 hv
  have hr2 : (L.mem (L.wr s1 (prioA t) prio) (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact hnr _ (h2.aff t ht) ((h2.released t ht).1 hcn)
  have hrun2 : Runnable (L.mem (L.wr s1 (prioA t) prio) (stA t)) := by
    rw [(prio_wr_eps (prio := prio) h1 ht).2, (hsb1 t ht).1]
    exact hrun
  refine WP.spec_bind (WP.spec_and (sched.enqueue.inv _ t _ R h2 ht (fun _ => hr2) (fun _ => hrun2))
    (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ t h2 ht)) ?_
  rintro s3 ⟨h3, f3⟩
  exact WP.spec_mono (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s3 h3)
    fun s' f4 => f1.trans (f2.trans (f3.trans f4))

theorem blocked_kw (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t)))
    (hEs : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → e ∈ Es)
    (reorder : S → U64 → obj.Tcb → Result S)
    (hfoot : ∀ (s : S) (ep : U64) (xs : List U64), TcbPlaced T → EpPlaced T ep →
      QueueRel (L.mem s) T .Ep (L.epQ s ep) xs → t ∈ xs → reorder s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      reorder s1 i t) ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
  subst s1_post
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (prioA t) prio) :=
    foot_field hT ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)
  have h1 := inv_wr_prio h ht hq0 hv
  obtain ⟨hbl, hstt⟩ := prio_wr_eps (prio := prio) h ht
  obtain ⟨E, EQ, hEW⟩ := h1.eps
  obtain ⟨heE, htm⟩ := hEW.2.2.2.2.1 t ht htX (by rw [hstt]; exact hb)
  obtain ⟨hE, -, hq⟩ := hEW.1 _ heE
  have hH : L.mem (L.wr s (prioA t) prio) (blockA t) ∈ Es := hEs _ ((hEW.2.2.2.2.2.2.2.1 _).1 heE)
  step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
  subst i_post
  exact WP.spec_mono (hfoot _ _ _ h1.tcbs hE hq htm) fun s2 hw =>
    f1.trans (Foot.of hw fun b hb => hb.kw hq.mem hH)

theorem running_kw (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hrun : Runnable (L.mem s (stA t)))
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
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
        else obj.Tcb.set_prio st t s prio) ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  step with sched.queued.spec as ⟨b, b_post⟩
  split
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    have htq := (h.queued t ht).1 hq1
    exact dpe_kw s t prio Q R h ht hv (fun c hc => h.QR (h.aff t ht) (h.prio t ht) htq hc) hrun
  · step with sched.cur_thread.spec as ⟨t1, t1_post⟩
    step with tcb_eq.blk as ⟨b1, b1_post⟩
    split
    · have e : t = t1 := by simpa [b1_post] using ‹b1 = true›
      have hr0 := hcur (e.trans t1_post)
      exact dpe_kw s t prio Q R h ht hv (fun c hc => h.notR ht hr0 hc) hrun
    · step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
      subst s1_post
      exact foot_field h.tcbs ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)

end kw

/-- seL4 `setPriority`: its footprint. -/
theorem sched.set_priority.kw (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.set_priority st s t prio ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  have hEs : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → e ∈ EH H := fun e he => he
  unfold sched.set_priority
  step with obj.Tcb.state.spec as ⟨sv, sv_post⟩
  subst sv_post
  split
  · exact running_kw s t prio Q R h ht hv (Or.inl ‹_›) hcur
  · split
    · exact running_kw s t prio Q R h ht hv (Or.inr (Or.inl ‹_›)) hcur
    · split
      · exact running_kw s t prio Q R h ht hv (Or.inr (Or.inr ‹_›)) hcur
      · have hnr : ¬ Runnable (L.mem s (stA t)) := by rintro (e | e | e) <;> contradiction
        have hq0 := notQ_of_not_runnable h ht hnr
        have fe := fun (s : S) ep xs hT hE hq hm => endpoint.reorder_ep.foot (st := st) (T := T) s ep t xs hT hE hq hm
        have fn := fun (s : S) ep xs hT hE hq hm =>
          notification.reorder_ntfn.foot (st := st) (T := T) s ep t xs hT hE hq hm
        split
        · exact blocked_kw s t prio Q R h ht hv hq0 (by simp) (Or.inr (Or.inl ‹_›)) hEs _ fe
        · split
          · exact blocked_kw s t prio Q R h ht hv hq0 (by simp) (Or.inl ‹_›) hEs _ fe
          · split
            · exact blocked_kw s t prio Q R h ht hv hq0 (by simp) (Or.inr (Or.inr ‹_›)) hEs _ fn
            · step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
              subst s1_post
              exact foot_field h.tcbs ht (K := 3448#u64) (by simp) (by simp) (by simp) (by simp)

/-- seL4 `setPriority`: `BlkOK` (with `SCsOK` and `SgOK`) and the footprint,
for a priority below 256, when the current thread, if it is `t`, is bound and
in no release queue. -/
theorem sched.set_priority.blk (s : S) (t : obj.Tcb) (prio : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hbcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) → L.mem s (scA t) ≠ 0#u64)
    (hacur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) → L.mem s (scA t) ∈ Ac) :
    sched.set_priority st s t prio ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z (EH H) s s' ∧ PFr st T Sg s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (sched.set_priority.all s t prio Q R h0 ht hv hcur hbcur hacur hB hX hSg hS)
    (sched.set_priority.kw (Sg := Sg) (Scs := Scs) (Z := Z) s t prio Q R h0 ht hv hcur)) ?_
  rintro s' ⟨⟨⟨Q', h'⟩, hB', hX', hS', hSg', pf⟩, f⟩
  exact ⟨⟨⟨Q', R, h'⟩, hB', hX', hS', hSg'⟩, f, pf⟩

end

end Fl4Proofs.P1
