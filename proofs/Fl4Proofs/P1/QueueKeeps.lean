/-
P1's frames for P3 hypotheses that ask "every cap slot is kept" of a
scheduler-side step (P3's `RPPHyp`/`PPHyp`, `BufHyp`, `DomSetHyp`,
`DomResHyp`, `NtfnKeepHyp`): each step keeps `BlkOK` and writes only
footprint (`KW`) words or the named kernel-global words, which P3 turns into
`SlotsSame` through `kw_out_slot`/`foot_keeps_capw`.
-/
import Fl4Proofs.P1.QueueVsFin
import Fl4Proofs.P1.QueueEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {A : Type _} {ar : machine.Arch A} {P3Ok : S → Prop}

/-! ## The preemption point -/

/-- The words the preemption point writes: the kernel-global `WORK_UNITS`
word and the current core's `CUR_TIME` and `CONSUMED` words. -/
def PPW (st : machine.Store S) [L : LawfulStore st] (s0 : S) (b : U64) : Prop :=
  b = core.num.U64.wrapping_add (L.ksb s0) layout.ks.WORK_UNITS ∨ b = L.nodeA s0 layout.node.CUR_TIME ∨
    b = L.nodeA s0 layout.node.CONSUMED

theorem PPW.of {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : PPW st s1 b) : PPW st s0 b := by
  rcases h with e | e | e
  · left; rw [e, hk]
  · right; left; rw [e]; unfold LawfulStore.nodeA; rw [hc, nodeAt_of_ksb hk]
  · right; right; rw [e]; unfold LawfulStore.nodeA; rw [hc, nodeAt_of_ksb hk]

/-- `update_timestamp` writes the current core's `CUR_TIME` and `CONSUMED`. -/
theorem sched.update_timestamp.w (hA : P0.ArchTotal ar) (s : S) (a : A) (hN : NodePlaced st T s (L.cpu s)) :
    sched.update_timestamp st ar s a ⦃ r => WritesIn st s r.1 (PPW st s) ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  have w1 : WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) (PPW st s) :=
    (writesIn_wr (nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))).mono
      fun b e => Or.inr (Or.inl e)
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  subst e2
  have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
      (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)) := by
    rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)
  have w2 := (writesIn_wr (st := st) (s := L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) (v := total) (nodeAt_aligned hN1 (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED]))).mono fun b e => (Or.inr (Or.inr e) : PPW st _ b)
  have w12 := (w1.trans w2).mono fun b hb => hb.elim id (PPW.of w1.1 w1.2.1)
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok]
  exact w12

/-- The kernel-global `WORK_UNITS` word is a word of `Ω` outside `Sg`. -/
theorem ks_work_units {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    Aligned (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS ∈ Ω ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS ∉ Sg := by
  have h0 := h.1.choose_spec.choose_spec
  have hSg := h.2.2.2.2
  have hN := h0.nodes _ h0.cur
  have hΩ : core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS ∈ Ω :=
    hSg.ksΩ _ (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])
  refine ⟨(h0.omega _ hΩ).1, hΩ, fun hs => ?_⟩
  have hk := hSg.ks _ hs
  have hf := hN.fits
  simp only [LawfulStore.nodeBase] at hf
  have hv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS).val = (L.ksb s).val + 40 := by
    simp [core.num.U64.wrapping_add_val_eq, layout.ks.WORK_UNITS, U64.size_def, U64.numBits]; omega
  rw [hv] at hk; omega

/-- **The preemption point** keeps `BlkOK` and writes only `WORK_UNITS` and
the current core's `CUR_TIME` and `CONSUMED` (no cap slot, no word of any
object but the kernel-global area and the node). -/
theorem sched.preemption_point.pp (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.preemption_point st ar s a ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧
      WritesIn st s r.2.1 (PPW st s) ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  obtain ⟨ha, hΩ, hnS⟩ := ks_work_units h
  unfold sched.preemption_point
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨w, _⟩
  step with obj.ks_set.spec as ⟨s1, e1⟩
  subst e1
  have B1 := blk_capw_wr (v := w) h ha (Or.inr ⟨hΩ, hnS⟩)
  have W1 : WritesIn st s (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w) (PPW st s) :=
    (writesIn_wr ha).mono fun b e => Or.inl e
  split
  · step with obj.ks_set.spec as ⟨s2, e2⟩
    subst e2
    try simp only [LawfulStore.ksb_wr]
    have B2 := blk_capw_wr (v := 0#u64) B1 ha (Or.inr ⟨hΩ, hnS⟩)
    have W2 := (writesIn_wr (st := st) (s := L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w)
      (v := 0#u64) ha).mono fun b e => (Or.inl e : PPW st s b)
    have W12 := (W1.trans W2).mono fun b hb => hb.elim id id
    have hN2 := (h0.nodes _ h0.cur).ksb W12.1
    rw [← W12.2.1] at hN2
    refine WP.spec_bind (WP.spec_and (sched.update_timestamp.bxc hA _ a B2.bxi)
      (sched.update_timestamp.w (T := T) hA _ a hN2)) ?_
    rintro ⟨s3, a1⟩ ⟨⟨⟨k3, -, -⟩, -, -⟩, w3⟩
    simp only [WP.uncurry'_pair] at k3 w3 ⊢
    have W := (W12.trans w3).mono fun b hb => hb.elim id (PPW.of W12.1 W12.2.1)
    have B3 := k3.blk
    have ip := hA.irq_pending
    have sf := sporadic.sufficient.ok (st := st) hA
    have hS : P0.StoreTotal st := L.total
    refine WP.spec_bind (ip a1) ?_
    rintro ⟨irq, a2⟩ -
    try dsimp only
    step*
    all_goals try first | exact ⟨B3, W⟩ | exact (WP.spec_ok _).2 ⟨B3, W⟩ | exact hS
    all_goals
      refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> first | exact sf _ _ _ _ | exact (WP.spec_ok _).2 trivial)
        fun ok1 _ => ?_
      split
      · exact (WP.spec_ok _).2 ⟨B3, W⟩
      · refine WP.spec_bind (P0.sched.is_cur_domain_expired.p0 st _ hS) fun b1 _ => ?_
        split
        · exact (WP.spec_ok _).2 ⟨B3, W⟩
        · split <;> exact (WP.spec_ok _).2 ⟨B3, W⟩
  · exact (WP.spec_ok _).2 ⟨B1, W1⟩

/-! ## TCB field writes: the IPC buffer and the domain -/

/-- `set_ipc_buffer` keeps `BlkOK`, a write of the TCB's `IPC_BUFFER`
field (offset 3512, a footprint word). -/
theorem obj.Tcb.set_ipc_buffer.blk (s : S) (t : obj.Tcb) (v : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    obj.Tcb.set_ipc_buffer st t s v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold obj.Tcb.set_ipc_buffer layout.tcb.IPC_BUFFER
  unfold layout.tcb.F
  step as ⟨K, hK⟩
  step*
  subst_vars
  have hK' : K.val = 3512 := by simp_all
  obtain ⟨b, f, -⟩ := plainW_all (K := K) (v := v) h ht (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  exact ⟨b, f⟩

/-- `set_domain`'s field write keeps `BlkOK` (offset 3432). -/
theorem obj.Tcb.set_domain.blk (s : S) (t : obj.Tcb) (v : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    obj.Tcb.set_domain st t s v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold obj.Tcb.set_domain layout.tcb.DOMAIN
  unfold layout.tcb.F
  step as ⟨K, hK⟩
  step*
  subst_vars
  have hK' : K.val = 3432 := by simp_all
  obtain ⟨b, f, -⟩ := plainW_all (K := K) (v := v) h ht (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  exact ⟨b, f⟩

/-- **The IPC-buffer tail** (`reschedule_required` when the target is the
current thread), the shape of P3's `BufHyp.tail`. -/
theorem buf_tail.blk (s : S) (a : A) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (do
      let t_1 ← sched.cur_thread st s
      let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t_1
      if b1 = true then do
          let s5 ← sched.reschedule_required st s
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = a ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.2.1 ∧
        Foot st T Cs Sg Scs Z ∅ s res.2.1 ⦄ := by
  step with sched.cur_thread.spec as ⟨ct, _⟩
  step with tcb_eq.blk as ⟨b, _⟩
  split
  · exact WP.spec_bind (sched.reschedule_required.blk s h) fun s5 ⟨h5, f5⟩ => (WP.spec_ok _).2 ⟨rfl, rfl, h5, f5⟩
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, h, Foot.refl _⟩

/-- **`set_domain`** keeps `BlkOK`, with a footprint (P3's `DomSetHyp`). -/
theorem sched.set_domain.blkF (s : S) (t : obj.Tcb) (d : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    sched.set_domain st s t d ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  unfold sched.set_domain
  refine WP.spec_bind (WP.spec_and (sched.dequeue.sch s t Q R h0 hB hSg ht)
    (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t h0 ht)) ?_
  rintro s1 ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, -, -⟩, fw1⟩
  have b1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := ⟨⟨Q1, R1, h1⟩, hB1, hX.fr f1, hS.fr f1, hSg.fr f1⟩
  refine WP.spec_bind (obj.Tcb.set_domain.blk s1 t d b1 ht) ?_
  rintro s2 ⟨b2, fw2⟩
  obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩ := b2
  step with sched.is_schedulable.spec' as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z ∅ s s3) ?_ ?_
  · split
    · rename_i hb
      obtain ⟨hrun, hbd, hrl, hrm⟩ := eb hb
      have hA2 : L.mem s2 (scA t) ∈ Ac := (hS2.act _ (hX2.2.2.bound t ht hbd).1).2 hrm
      refine WP.spec_mono (WP.spec_and (sched.enqueue.sch s2 t Q2 R2 h2 hB2 hSg2 ht (fun _ => hrl) (fun _ => hrun)
        (fun _ => hbd) (fun _ => hA2)) (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 t h2 ht)) ?_
      rintro s3 ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, f3⟩, -, -, -⟩, fw3⟩
      exact ⟨⟨⟨Q3, R3, h3⟩, hB3, hX2.fr f3, hS2.fr f3, hSg2.fr f3⟩, fw1.trans (fw2.trans fw3)⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩, fw1.trans fw2⟩
  rintro s3 ⟨b3, fw3⟩
  step with sched.cur_thread.spec as ⟨ct, _⟩
  step with tcb_eq.blk as ⟨b1', _⟩
  split
  · exact WP.spec_mono (sched.reschedule_required.blk s3 b3) fun s4 ⟨h4, f4⟩ => ⟨h4, fw3.trans f4⟩
  · exact (WP.spec_ok _).2 ⟨b3, fw3⟩

/-! ## `activate_thread` (EntryHyps' `act`) -/

/-- Words whose writes keep every thread's `SC` field and the current SC:
words of `Ω`, and TCB fields other than `SC`. -/
def CSW (T Ω : Set U64) (b : U64) : Prop :=
  b ∈ Ω ∨ ∃ y ∈ T, ∃ K : U64, K.val < 4096 ∧ K.val % 8 = 0 ∧ K.val ≠ 3464 ∧ K.val ≠ 3368 ∧ K.val ≠ 3328 ∧
    b = core.num.U64.wrapping_add y K

theorem cs_of_writes {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {B : U64 → Prop}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' B) (hB : ∀ b, B b → CSW T Ω b) :
    L.cscW s' = L.cscW s ∧ ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := by
  have hT := h.tcbs
  have hN := h.nodes _ h.cur
  refine ⟨?_, fun y hy => ?_⟩
  · unfold LawfulStore.cscW LawfulStore.nodeA
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) fun hb => ?_
    rcases hB _ hb with hm | ⟨z, hz, K, hK, -, -, -, -, e⟩
    · exact out_ne_node (h.omega _ hm) h.cur hN (by simp [layout.node.CUR_SC]) rfl
    · exact node_ne_field hN (by simp [layout.node.CUR_SC]) hz (hT z hz) hK e
  · rw [scA_eq]
    refine hw.mem_eq (field_aligned (hT y hy) (by simp) (by simp)) fun hb => ?_
    rcases hB _ hb with hm | ⟨z, hz, K, hK, -, hK3, -, -, e⟩
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) (by simp) rfl
    · exact field_ne (hT y hy) (hT z hz) (by simp) hK (fun _ => by simp; omega) e

/-- `CSW` writes keep every TCB's `SC`, `BOUND_NTFN` and `STATE` fields. -/
theorem csw_keep {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {B : U64 → Prop}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' B) (hB : ∀ b, B b → CSW T Ω b) :
    ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (boundA y) = L.mem s (boundA y) ∧
      L.mem s' (stA y) = L.mem s (stA y) := by
  have hT := h.tcbs
  have K : ∀ y ∈ T, ∀ K0 : U64, K0.val < 4096 → K0.val % 8 = 0 →
      (K0.val = 3464 ∨ K0.val = 3368 ∨ K0.val = 3328) →
      L.mem s' (core.num.U64.wrapping_add y K0) = L.mem s (core.num.U64.wrapping_add y K0) := by
    intro y hy K0 h1 h2 h3
    refine hw.mem_eq (field_aligned (hT y hy) h1 h2) fun hb => ?_
    rcases hB _ hb with hm | ⟨z, hz, K, hK, -, a1, a2, a3, e⟩
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) h1 rfl
    · exact field_ne (hT y hy) (hT z hz) h1 hK (fun _ => by omega) e
  intro y hy
  refine ⟨?_, ?_, ?_⟩
  · rw [scA_eq]; exact K y hy _ (by simp) (by simp) (by simp)
  · exact K y hy 3368#u64 (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact K y hy _ (by simp) (by simp) (by simp)

theorem reg_cs {s : S} {t r v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s s' (CSW T Ω) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hT t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned (hT t ht) (by omega) (by omega))).mono fun b e =>
      Or.inr ⟨t, ht, K, by omega, by omega, by omega, by omega, by omega, e⟩

theorem sc_word_cs {s : S} {c o : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) (ho : o.val < 128)
    (h8 : o.val % 8 = 0) : Aligned (core.num.U64.wrapping_add c o) ∧ CSW T Ω (core.num.U64.wrapping_add c o) := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨c8, c128, cfit⟩ := sc_lo hP hz
  have hv : (core.num.U64.wrapping_add c o).val = c.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have ha : Aligned (core.num.U64.wrapping_add c o) := by unfold Aligned; rw [hv]; omega
  exact ⟨ha, Or.inl (hO.scW c hc _ ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩)⟩

theorem schedcontext.update_consumed.cs {s : S} {a : A} {c : U64} (hA : P0.ArchTotal ar)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => WritesIn st s r.2 (CSW T Ω) ⦄ := by
  obtain ⟨ha, hw⟩ := sc_word_cs (T := T) (o := layout.sc.CONSUMED) hO hc (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED])
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)

theorem cs_trans {s₁ s₂ s₃ : S} (h₁ : WritesIn st s₁ s₂ (CSW T Ω)) (h₂ : WritesIn st s₂ s₃ (CSW T Ω)) :
    WritesIn st s₁ s₃ (CSW T Ω) := (h₁.trans h₂).mono fun _ hb => hb.elim id id

theorem schedcontext.set_consumed.cs (hA : P0.ArchTotal ar) (s : S) (a : A) (c t : U64) (wm : Bool)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (ht : t ∈ T) :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' => WritesIn st s s' (CSW T Ω) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.cs (T := T) hA h.2.2.1.1 hc) ?_
  rintro ⟨x, s1⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true t L.total) fun buf _ => ?_
    refine WP.spec_bind (reg_cs (Ω := Ω) (r := layout.reg.BADGE) hT ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s2 w2 => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => WritesIn st s2 r.2 (CSW T Ω)) ?_ ?_
    · refine WP.spec_bind (reg_cs (Ω := Ω) (r := layout.reg.R10) hT ht (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ w3
    simp only at w3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
    exact WP.spec_mono (reg_cs (Ω := Ω) (r := layout.reg.MSG_INFO) hT ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => cs_trans w1 (cs_trans w2 (cs_trans w3 w4))
  · exact (WP.spec_ok _).2 w1

theorem schedcontext.cancel_yield_to.cs (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    schedcontext.cancel_yield_to st s t ⦃ s' => WritesIn st s s' (CSW T Ω) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have h0 := h.1.choose_spec.choose_spec
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, _⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact h.2.2.1.2.2.yt.2.1 t ht (by rw [← ei]; simpa using hi)
    have hm : scYieldFromA i ∈ Ω := h.2.2.2.2.sub _ (h.2.2.1.1.syW i hiS)
    step with obj.Sc.set_yield_from.spec as ⟨s1, e1⟩
    subst e1
    step with obj.Tcb.set_yield_to.spec as ⟨s2, e2⟩
    subst e2
    have w1 := (writesIn_wr (st := st) (s := s) (v := 0#u64) (h0.omega _ hm).1).mono fun b e => (by rw [e]; exact Or.inl hm : CSW T Ω b)
    have w2 := (writesIn_wr (st := st) (s := L.wr s (scYieldFromA i) 0#u64) (v := 0#u64)
      (field_aligned (K := 3472#u64) (hT t ht) (by simp) (by simp))).mono
      fun b e => (Or.inr ⟨t, ht, 3472#u64, by simp, by simp, by simp, by simp, by simp, e⟩ : CSW T Ω b)
    exact cs_trans w1 w2
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

theorem schedcontext.complete_yield_to.cs (hA : P0.ArchTotal ar) (s : S) (a : A) (y : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ≠ 0#u64 → y ∈ T) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => WritesIn st s r.1 (CSW T Ω) ⦄ := by
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rename_i hb
  have hyT : y ∈ T := hy (fun e => hb (by rw [b_post, e]; rfl))
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact h.2.2.1.2.2.yt.2.1 y hyT (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.blk hA s a i y true h hiS hyT)
      (schedcontext.set_consumed.cs hA s a i y true h hiS hyT)) fun s1 ⟨⟨h1, _, _⟩, w1⟩ => ?_
    refine WP.spec_bind (schedcontext.cancel_yield_to.cs s1 y h1 hyT) fun s2 w2 => ?_
    exact (WP.spec_ok _).2 (cs_trans w1 w2)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- `EntryInv` after a step that keeps `BlkOK`, the current thread and SC,
every thread's SC field, and keeps the action or makes it `CHOOSE_NEW`. -/
theorem EntryInv.of_step {s s' : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h' : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s') (ecs : L.cscW s' = L.cscW s) (ec : L.curW s' = L.curW s)
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) (esc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)) :
    EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hT := h.1.choose_spec.choose_spec.tcbs
  obtain ⟨-, -, -, -, -, hcA, hna, hcsc⟩ := h
  obtain ⟨q, b, x, sc, sg⟩ := h'
  refine ⟨q, b, x, sc, x.2.2.tm, by rw [ecs]; exact hcA, ?_, ?_⟩
  · rw [ec]
    rcases ea with e | e
    · rw [e]; exact hna
    · rw [e]; intro e'; exact notT_small hT (by rw [← e']; decide) hcT
  · rw [ec, esc _ hcT, ecs]; exact hcsc

/-- **EntryHyps' `act`: `activate_thread` keeps `EntryInv`.**  The yield is
completed (`complete_yield_to`), and a restarted thread gets its fault IP as
its next IP and runs again. -/
theorem sched.activate_thread.entry (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.activate_thread st ar s a ⦃ r => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  have hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := (EntryInv.bxi h).blk
  have h0 := hb.1.choose_spec.choose_spec
  have hT := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  unfold sched.activate_thread
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = L.curW s := ect
  subst ect'
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      WritesIn st s r.1 (CSW T Ω) ∧ ANI st s r.1) ?_ ?_
  · split
    · refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s a _ hb (fun _ => hcT))
        (schedcontext.complete_yield_to.cs hA s a _ hb (fun _ => hcT))) ?_
      rintro ⟨s1, a1⟩ ⟨⟨h1, -, n1⟩, w1⟩
      exact ⟨h1, w1, n1⟩
    · exact (WP.spec_ok _).2 ⟨hb, WritesIn.refl _ _, ANI.refl _⟩
  rintro ⟨s1, a1⟩ ⟨h1, w1, n1⟩
  try simp only [WP.uncurry'_pair]
  obtain ⟨ecs1, esc1⟩ := cs_of_writes h0 w1 (fun b hb => hb)
  have E1 := EntryInv.of_step h h1 ecs1 n1.2.2 (Or.inl n1.1) esc1
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    step with obj.Tcb.reg.spec as ⟨pc, _⟩
    have hct1 : L.curW s1 = L.curW s := n1.2.2
    refine WP.spec_bind (obj.Tcb.set_reg.wrK s1 _ layout.reg.NEXT_IP pc (hT _ hcT)
      (by simp [layout.reg.NEXT_IP])) ?_
    rintro s2 ⟨K, hK, e2⟩
    subst e2
    have hK' : K.val < 3328 := by have : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
                                  omega
    obtain ⟨h2, -, n2⟩ := regW_all (K := K) (v := pc) h1 hcT (by omega) hK' (by omega)
    have w2 : WritesIn st s1 (L.wr s1 (core.num.U64.wrapping_add (L.curW s) K) pc) (CSW T Ω) :=
      (writesIn_wr (field_aligned (hT _ hcT) (by omega) (by omega))).mono fun b e =>
        Or.inr ⟨_, hcT, K, by omega, by omega, by omega, by omega, by omega, e⟩
    obtain ⟨ecs2, esc2⟩ := cs_of_writes h1.1.choose_spec.choose_spec w2 (fun b hb => hb)
    have E2 := EntryInv.of_step E1 h2 ecs2 (by rw [n2.2.2]) (Or.inl n2.1) esc2
    have st2 : L.mem (L.wr s1 (core.num.U64.wrapping_add (L.curW s) K) pc) (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, L.mem_wr_ne (field_aligned (hT _ hcT) (by omega) (by omega))
        (field_aligned (hT _ hcT) (by simp) (by simp))
        (fun e => field_ne (hT _ hcT) (hT _ hcT) (by omega) (by simp) (fun _ => by simp; omega)
          (UScalar.eq_of_val_eq e)), ← stA_eq, ← ev]
      exact hv
    obtain ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩ := h2
    have hrun : Runnable sched.TS_RUNNING := Or.inl rfl
    refine WP.spec_bind (sts_all _ _ _ Q2 R2 q2 hB2 hX2 hS2 hSg2 hcT (fun hb' => not_runnable_of_blocked hb' hrun)
      ⟨runnable_ne_reply hrun, runnable_ne_recv hrun⟩ (Or.inr (by rw [st2]; exact not_blocked_restart))
      (hX2.noref (hT _ hcT) (by rw [st2]; exact restart_ne.1) (by rw [st2]; exact restart_ne.2))
      ⟨fun _ _ _ _ _ => hrun, fun _ _ _ => hrun, fun _ => hrun⟩) ?_
    rintro s3 ⟨h3, hB3, hX3, hS3, hSg3, -, k3⟩
    have E3 := EntryInv.of_step E2 ⟨⟨Q2, R2, h3.congrX empty_congr⟩, hB3, hX3, hS3, hSg3⟩ k3.cscW
      (by rw [k3.curW]) k3.act (fun y hy => k3.scf hy)
    exact (WP.spec_ok _).2 E3
  · exact (WP.spec_ok _).2 E1

/-- **`EntryHyps` with `act` discharged** (`sched.activate_thread.entry`);
`fault` is no longer a field (`EntryHyps.fault`, from `tmoOK` and `xfer`). -/
theorem EntryHyps.of {U : Set U64} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (xfer : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok))
    (tmoOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s ∧
      ∀ i, (i = layout.tcb.SLOT_TIMEOUT_HANDLER ∨ i = layout.tcb.SLOT_FAULT_HANDLER) →
        obj.Tcb.slot (L.curW s) i ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (inv : ∀ (Ac : Set U64) (s : S) (a : A) (call blk don fp : Bool) (cptr : U64), EntAt st P3Ok s →
      BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → L.cscW s ∈ Ac → L.actionW s ≠ L.curW s →
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) →
      syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
        BXIs st Cs σ' Ac' s' ∧
        (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
          (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄)
    (blkU : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s)
    (recvOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      (∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄) ∧
      (∀ n ∈ Nt, L.epState s n ≠ 3#u64))
    (irqcap : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      ∀ i : U64, i.val < 128 →
      obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄)
    (debug : ∀ (Ac : Set U64) (s : S) (a : A) (n : I64), EntAt st P3Ok s → EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
      syscall.debug_syscall st ar s a (L.curW s) n ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄)
    (postG : ∀ (s0 : S) (a0 : A) (call blk don fp : Bool) (cptr : U64) (r : core.result.Result Unit error.Exc)
      (s1 : S) (a1 : A), EntAt st P3Ok s0 → syscall.handle_invocation st ar s0 a0 call blk don fp cptr = ok (r, s1, a1) →
      XG st T Cs Ω H Sg Scs Z P3Ok s1 ∧ ∀ (b : Bool) (s2 : S) (a2 : A),
        syscall.after_invocation st ar s1 a1 r = ok (b, s2, a2) → XG st T Cs Ω H Sg Scs Z P3Ok s2) :
    EntryHyps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨⟨xfer, tmoOK, blkU, recvOK, irqcap, debug, postG, fun Ac s a h =>
    WP.spec_mono (sched.activate_thread.entry hA s a h) fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr⟩, inv⟩

end

end Fl4Proofs.P1
