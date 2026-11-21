/-
P3 (DESIGN.md §9), scheduling contexts: **the footprints of the
scheduling-context code** (positive: the words a step may write).

* `SOff`, `SFoot`: TCB words at the offsets the SC code writes (`SOffL`),
  and the node's words (the scheduler's footprint);
* `NW`: a notification's words; `SW`: the words of an SC of `C` other than
  its `REPLY` word (sizes from the spec state);
* `KFoot = SFoot ∨ NW ∨ SW`: what Bind, UnbindObject and Consumed write;
  `WritesIn.kfoot_trans` composes such footprints across steps that keep the
  SC sizes (`SzKeep`).
-/
import Fl4Proofs.P3.ScSpec
import Fl4Proofs.P1.QueueSc
import Fl4Proofs.P1.QueueCancel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The TCB offsets the scheduling-context code writes**: the state
(`STATE`, 3328), the SC pointer (`SC`, 3464), the ready-queue links (3480,
3488), the release flag (3520) and the release-queue link (3592). The
notification code's TCB words (state, blocking object, badge register, `Ep`
links) are not here: `unbind_ntfn` writes only the notification's words. -/
def SOffL (K : U64) : Prop :=
  K = 3328#u64 ∨ K = 3464#u64 ∨ K = 3480#u64 ∨ K = 3488#u64 ∨ K = 3520#u64 ∨ K = 3592#u64

/-- A TCB offset the scheduler code may write: past the cap slots and the
`TCB` header (`≥ 256`), and none of the `MCP` (3440), `YIELD_TO` (3472) and
`IPC_BUFFER` (3512) words. -/
def SOff (K : U64) : Prop := 256 ≤ K.val ∧ K.val < 4096 ∧ K ≠ 3440#u64 ∧ K ≠ 3472#u64 ∧ K ≠ 3512#u64 ∧ SOffL K

/-- A TCB's VCPU word (`layout::tcb::VCPU`, offset 3664; KENTRY-PLAN g2b):
written by FL4 only in `vcpu::detach` (0) and `X86VCPUSetTCB`. -/
def _root_.Fl4Proofs.P3.tVcpuA (t : U64) : U64 := core.num.U64.wrapping_add t 3664#u64

/-- 3664 is no scheduler offset. -/
theorem not_sOff_vcpu : ¬ SOff 3664#u64 := by unfold SOff SOffL; decide

/-- The scheduler footprint: words of the TCBs at `SOff` offsets, and of the
node. -/
def SFoot (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, SOff K ∧ b = core.num.U64.wrapping_add y K) ∨
    (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288)

theorem SFoot.ksb {T : Set U64} {c : U64} {s s' : S} (h : L.ksb s' = L.ksb s) {b : U64} :
    SFoot st T c s' b ↔ SFoot st T c s b := by
  simp only [SFoot, LawfulStore.nodeBase, h]

theorem WritesIn.sfoot_trans {T : Set U64} {c : U64} {s s1 s2 : S} (h1 : WritesIn st s s1 (SFoot st T c s))
    (h2 : WritesIn st s1 s2 (SFoot st T c s1)) : WritesIn st s s2 (SFoot st T c s) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact (SFoot.ksb h1.1).1 hb

/-- The TCB words of the footprint lie in the TCB, past offset 256. -/
theorem SFoot.range {T : Set U64} {c : U64} {s : S} (hT : TcbPlaced T) {b : U64} (h : SFoot st T c s b) :
    (∃ y ∈ T, y.val + 256 ≤ b.val ∧ b.val < y.val + 4096) ∨
      (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288) := by
  rcases h with ⟨y, hy, K, ⟨k1, k2, -, -⟩, rfl⟩ | h
  · exact Or.inl ⟨y, hy, by rw [tfield_val (hT y hy) k2]; omega, by rw [tfield_val (hT y hy) k2]; omega⟩
  · exact Or.inr h

/-- A footprint word is no `MCP` word. -/
theorem SFoot.not_mcp {T : Set U64} {c : U64} {s : S} (hT : TcbPlaced T) (hN : NodePlaced st T s c) {b : U64}
    (h : SFoot st T c s b) {u : U64} (hu : u ∈ T) : b ≠ core.num.U64.wrapping_add u 3440#u64 := by
  rintro rfl
  rcases h with ⟨y, hy, K, ⟨k1, k2, k3, -⟩, e⟩ | ⟨g1, g2⟩
  · rw [tt_eq_iff (hT u hu) (hT y hy) (by simp) k2] at e; exact k3 e.2.symm
  · have := hN.disj u hu; rw [tfield_val (hT u hu) (by simp)] at g1 g2; simp at g1 g2; omega

/-- A footprint word is no `YIELD_TO` word. -/
theorem SFoot.not_yield {T : Set U64} {c : U64} {s : S} (hT : TcbPlaced T) (hN : NodePlaced st T s c) {b : U64}
    (h : SFoot st T c s b) {u : U64} (hu : u ∈ T) : b ≠ core.num.U64.wrapping_add u 3472#u64 := by
  rintro rfl
  rcases h with ⟨y, hy, K, ⟨k1, k2, -, k4, -⟩, e⟩ | ⟨g1, g2⟩
  · rw [tt_eq_iff (hT u hu) (hT y hy) (by simp) k2] at e; exact k4 e.2.symm
  · have := hN.disj u hu; rw [tfield_val (hT u hu) (by simp)] at g1 g2; simp at g1 g2; omega

/-- A word of a TCB at an `SOff` offset is in the footprint. -/
theorem sfoot_tcb {T : Set U64} {c : U64} {s : S} {y K : U64} (hy : y ∈ T) (hK : SOff K) :
    SFoot st T c s (core.num.U64.wrapping_add y K) :=
  Or.inl ⟨y, hy, K, hK, rfl⟩

theorem writesIn_tcb {T : Set U64} {c : U64} {s : S} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T)
    (hK : SOff K) (hK8 : K.val % 8 = 0) (v : U64) :
    WritesIn st s (L.wr s (core.num.U64.wrapping_add y K) v) (SFoot st T c s) :=
  (writesIn_wr (field_aligned (hT y hy) hK.2.1 hK8)).mono fun b hb => hb ▸ sfoot_tcb hy hK

/-- A queue footprint is in the scheduler footprint. -/
theorem qfoot_sfoot {T : Set U64} {c : U64} {s : S} {W : List U64} {P : Nat → Prop} {t b : U64}
    (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T) (ht : t ∈ T) (hN : NodePlaced st T s c) (hcpu : L.cpu s = c)
    (h : L.QFoot s W c P t b) : SFoot st T c s b := by
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩
  · exact Or.inl ⟨w, hW w hw, 3480#u64, by unfold SOff SOffL; decide, e⟩
  · exact Or.inl ⟨w, hW w hw, 3488#u64, by unfold SOff SOffL; decide, e⟩
  · exact Or.inr ⟨by rw [e, nodeAt_val hN ho]; omega, by rw [e, nodeAt_val hN ho]; omega⟩
  · exact Or.inl ⟨t, ht, 3592#u64, by unfold SOff SOffL; decide, e⟩
  · rw [hcpu] at e
    exact Or.inr ⟨by rw [e, nodeAt_val hN ho]; omega, by rw [e, nodeAt_val hN ho]; omega⟩

/-- **`dequeue`'s footprint.** -/
theorem dequeue_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  refine WP.spec_mono (sched.dequeue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) (hc.queued t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => (hc.ready.1.rel _ hp).mem w hw') ht hc.node hc.cur hb

/-- **`enqueue`'s footprint**, for a thread that is queued or not released. -/
theorem enqueue_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ Q (L.mem s (prioA t)) :=
    fun h0 hm => ((hc.queued t ht).2 hm) h0
  refine WP.spec_mono (sched.enqueue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) hnq) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact (hc.ready.1.rel _ hp).mem w hw'

/-- **`release_remove`'s footprint.** -/
theorem release_remove_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  refine WP.spec_mono (sched.release_remove.foot s t _ hc.tcbs ht hN hN' hrel (hc.released t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => hc.release.mem w hw') ht hc.node hc.cur hb

/-- **`release_enqueue`'s footprint**, for a thread not released. -/
theorem release_enqueue_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_enqueue st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  have htR : t ∉ R := fun hm => (hc.released t ht).2 hm hr0
  refine WP.spec_mono (sched.release_enqueue.foot s t _ hc.tcbs ht htR hN hN' hrel) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact hc.release.mem w hw'

/-- A node word is in the footprint. -/
theorem sfoot_node {T : Set U64} {c : U64} {s : S} (hN : NodePlaced st T s c) {o : U64} (ho : o.val < 4288) :
    SFoot st T c s (L.nodeAt s c o) :=
  Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩

/-- **`reschedule_required`'s footprint.** -/
theorem reschedule_required_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) :
    sched.reschedule_required st s ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hact : ∀ s1 : S, WritesIn st s s1 (SFoot st T c s) →
      sched.set_action st s1 sched.ACTION_CHOOSE_NEW ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
    intro s1 h1
    refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
    rintro s' rfl
    refine WritesIn.sfoot_trans h1 ((writesIn_wr ?_).mono fun b hb => ?_)
    · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION])
        (by simp [layout.node.SCHED_ACTION])
    · rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]
      have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
      refine (SFoot.ksb h1.1).2 (Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩)
  unfold sched.reschedule_required
  step with sched.action.spec' as ⟨act, hact'⟩
  rw [hc.cur] at hact'
  have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
  have e1 : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl
  by_cases h1 : act = sched.ACTION_RESUME_CURRENT
  · have : (act != sched.ACTION_RESUME_CURRENT) = false := by simpa using h1
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact hact s (WritesIn.refl _ _)
  have g1 : (act != sched.ACTION_RESUME_CURRENT) = true := by simpa using h1
  by_cases h2 : act = sched.ACTION_CHOOSE_NEW
  · have : (act != sched.ACTION_CHOOSE_NEW) = false := by simpa using h2
    simp only [g1, this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact hact s (WritesIn.refl _ _)
  have g2 : (act != sched.ACTION_CHOOSE_NEW) = true := by simpa using h2
  simp only [g1, g2, ↓reduceIte]
  have hT : act ∈ T := by
    rw [hact']
    rcases hS.actW with h | h | h
    · rw [hact', h] at h1; exact absurd e0.symm h1
    · rw [hact', h] at h2; exact absurd e1.symm h2
    · exact h
  step with sched.is_schedulable.spec' as ⟨b, _hb⟩
  by_cases hb : b = true
  · rw [if_pos hb]; exact WP.spec_bind (enqueue_sfoot hS hT) hact
  · rw [if_neg hb]; simp only [bind_ok]; exact hact s (WritesIn.refl _ _)

/-- `schedule_tcb` writes at most the action word (in the scheduler footprint). -/
theorem schedule_tcb_sfoot {N T C : Set U64} {c : U64} {s s1 : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (h1 : WritesIn st s s1 (SFoot st T c s)) (t : U64) :
    sched.schedule_tcb st s1 t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hact : sched.set_action st s1 sched.ACTION_CHOOSE_NEW ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
    refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
    rintro s' rfl
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    refine (h1.trans ((writesIn_wr ?_).mono fun b hb => ?_)).mono fun b hb => by rcases hb with hb | hb <;> exact hb
    · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN ho (by simp [layout.node.SCHED_ACTION])
    · rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]
      exact Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec' as ⟨t1, _ht1⟩
  step as ⟨b, _hb⟩
  split
  · step with sched.action.spec' as ⟨i, _hi⟩
    split
    · step with sched.is_schedulable.spec' as ⟨b1, _hb1⟩
      split
      · exact (WP.spec_ok _).mpr h1
      · exact hact
    · exact (WP.spec_ok _).mpr h1
  · exact (WP.spec_ok _).mpr h1

/-- `set_thread_state` writes in the scheduler footprint. -/
theorem set_thread_state_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.set_thread_state
  step
  subst s1_post
  rw [show stA t = tStA t from rfl, tStA_eq]
  exact schedule_tcb_sfoot hS (writesIn_tcb hc.tcbs ht (by unfold SOff SOffL; decide) (by simp) v) t

/-- **`possible_switch_to`'s footprint.** -/
theorem possible_switch_to_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hr : ActReady σ) {t : U64} (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.possible_switch_to
  step
  split
  · exact (WP.spec_ok _).mpr (WritesIn.refl _ _)
  step
  split
  · exact (WP.spec_ok _).mpr (WritesIn.refl _ _)
  step
  step
  split
  · exact enqueue_sfoot hS ht
  step
  step
  split
  · exact enqueue_sfoot hS ht
  step
  split
  · refine WP.spec_bind (WP.spec_and (reschedule_required_refines s σ hR hS hr) (reschedule_required_sfoot hS)) ?_
    rintro s1 ⟨⟨σ1, -, -, -, -, hS1⟩, hw1⟩
    exact WP.spec_mono (enqueue_sfoot hS1 ht) fun s2 hw2 => WritesIn.sfoot_trans hw1 hw2
  · step
    subst s'_post
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [show L.cpu s = c from hc.cur]
    exact (writesIn_wr (nodeAt_aligned hc.node ho (by simp [layout.node.SCHED_ACTION]))).mono fun b hb =>
      hb ▸ sfoot_node hc.node ho

/-- A notification's words. -/
def NW (N : Set U64) (b : U64) : Prop := ∃ n ∈ N, n.val ≤ b.val ∧ b.val < n.val + 40

/-- A word of an SC of `C` (of its size in `σ`) other than its `REPLY` word. -/
def SW (C : Set U64) (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  ∃ sc ∈ C, ∃ x n, σ.kheap sc.bv = some (.schedContext x n) ∧ ScObj sc n b ∧ b ≠ scReplyA sc

/-- A register word of a TCB of `T` (offsets 256..448): what a reply from
the kernel writes (`msgW`). -/
def RegW (T : Set U64) (b : U64) : Prop :=
  ∃ y ∈ T, ∃ K : U64, 256 ≤ K.val ∧ K.val < 448 ∧ b = core.num.U64.wrapping_add y K

theorem RegW.range {T : Set U64} (hT : TcbPlaced T) {b : U64} (h : RegW T b) :
    ∃ y ∈ T, y.val + 256 ≤ b.val ∧ b.val < y.val + 448 := by
  obtain ⟨y, hy, K, k1, k2, rfl⟩ := h
  exact ⟨y, hy, by rw [tfield_val (hT y hy) (by omega : K.val < 4096)]; omega,
    by rw [tfield_val (hT y hy) (by omega : K.val < 4096)]; omega⟩

/-- **The footprint of Bind, UnbindObject and Consumed.** -/
def KFoot (st : machine.Store S) [L : LawfulStore st] (T N C : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  SFoot st T c s b ∨ NW N b ∨ SW C σ b

theorem KFoot.of_sfoot {T N C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} {b : U64}
    (h : SFoot st T c s b) : KFoot st T N C c s σ b := Or.inl h

theorem KFoot.of_nw {T N C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} {b : U64}
    (h : NW N b) : KFoot st T N C c s σ b := Or.inr (Or.inl h)

theorem KFoot.of_sw {T N C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} {b : U64}
    (h : SW C σ b) : KFoot st T N C c s σ b := Or.inr (Or.inr h)

theorem scReplyA_eq' (sc : U64) : scReplyA sc = scW sc 32#u64 := by
  unfold scReplyA scW layout.sc.REPLY; rfl

/-- An SC header word other than `REPLY` is in the footprint. -/
theorem sw_hdr {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {sc : U64} (hsc : sc ∈ C) {K : U64} (hK : K.val < 96) (hK8 : K.val % 8 = 0) (h32 : K ≠ 32#u64) :
    SW C σ (scW sc K) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have ha := hx.hdr hK hK8
  refine ⟨sc, hsc, x, n, hk, hx.in_obj ha.2, fun e => h32 ?_⟩
  have hb := hx.bounds
  have := congrArg UScalar.val e
  rw [scReplyA_eq', scW_val (by omega), scW_val (by simp; omega)] at this
  exact UScalar.eq_of_val_eq (by simp at this ⊢; omega)

/-- An SC word from `HEAD` on (`InRing` of its spec size) is in the footprint. -/
theorem sw_ring {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    {b : U64} (h : InRing sc (n + Fl4Spec.minSchedContextBits) b) : SW C σ b := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have hb := hx.bounds
  refine ⟨sc, hsc, x, n, hk, ⟨by have := h.1; omega, h.2⟩, fun e => ?_⟩
  have := h.1
  rw [e, scReplyA_eq', scW_val (by simp; omega)] at this
  simp at this

/-- **`unblock_check`'s footprint**: the SC's ring and the node's `REPROGRAM`. -/
theorem unblock_check_kfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {p : U64} (hp : p ∈ C) (ha : (L.rmax s p).val ≠ 0) :
    sporadic.unblock_check st s p ⦃ s' => WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs p hp
  have hN := hc.node
  have ho : (layout.node.REPROGRAM).val < 4288 := by simp [layout.node.REPROGRAM]
  have e : L.nodeA s layout.node.REPROGRAM = L.nodeAt s c layout.node.REPROGRAM := by
    unfold LawfulStore.nodeA; rw [hc.cur]
  have hal : Aligned (L.nodeA s layout.node.REPROGRAM) := by
    rw [e]; exact nodeAt_aligned hN ho (by simp [layout.node.REPROGRAM])
  have hout : Outside (L.nodeA s layout.node.REPROGRAM) p (n + Fl4Spec.minSchedContextBits) := by
    unfold Outside
    by_contra hin
    push_neg at hin
    have := (hS.scOut p hp x n hk _ ⟨hin.1, hin.2⟩).2.1
    rw [e, nodeAt_val hN ho] at this
    omega
  refine WP.spec_mono (sporadic.unblock_check.fr (hx.act ha).wf ⟨hal, hout⟩) fun s' hw => hw.mono fun b hb => ?_
  rcases hb with hb | hb
  · exact KFoot.of_sw (sw_ring hS hp hk hb)
  · rw [hb, e]; exact KFoot.of_sfoot (sfoot_node hN ho)

/-- `WritesIn.kfoot_sfoot` with register words. -/
theorem WritesIn.kfootR_sfootR {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (fun b => KFoot st T N C c s σ b ∨ RegW T b))
    (h2 : WritesIn st s1 s2 (fun b => SFoot st T c s1 b ∨ RegW T b)) :
    WritesIn st s s2 (fun b => KFoot st T N C c s σ b ∨ RegW T b) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb | hb
    · exact hb
    · exact Or.inl (KFoot.of_sfoot ((SFoot.ksb h1.1).1 hb))
    · exact Or.inr hb

/-- An SFoot step after a footprint. -/
theorem WritesIn.kfoot_sfoot {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (KFoot st T N C c s σ)) (h2 : WritesIn st s1 s2 (SFoot st T c s1)) :
    WritesIn st s s2 (KFoot st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact KFoot.of_sfoot ((SFoot.ksb h1.1).1 hb)

/-- An `SW` step (of the start's spec) after a footprint. -/
theorem WritesIn.kfoot_sw {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (KFoot st T N C c s σ)) (h2 : WritesIn st s1 s2 (SW C σ)) :
    WritesIn st s s2 (KFoot st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact KFoot.of_sw hb

theorem SzKeep.trans {σ σ1 σ2 : Fl4Spec.State Unit} (h1 : SzKeep σ σ1) (h2 : SzKeep σ1 σ2) : SzKeep σ σ2 :=
  fun p x n hp => by obtain ⟨x1, h⟩ := h2 p x n hp; exact h1 p x1 n h

theorem SzKeep.refl (σ : Fl4Spec.State Unit) : SzKeep σ σ := SzKeep.of_kheap rfl

/-- The SCs of `C` in `σ'` had their sizes in `σ`. -/
def SzKeepC (C : Set U64) (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∀ sc ∈ C, ∀ x n, σ'.kheap sc.bv = some (.schedContext x n) → ∃ x0, σ.kheap sc.bv = some (.schedContext x0 n)

theorem SzKeepC.of {C : Set U64} {σ σ' : Fl4Spec.State Unit} (h : SzKeep σ σ') : SzKeepC C σ σ' :=
  fun sc _ x n hk => h sc.bv x n hk

/-- `SzKeepC` from a step that keeps the SCs of `C` (with their sizes) forward. -/
theorem SzKeepC.of_fwd {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ)
    (h : ∀ p x n, σ.kheap p = some (.schedContext x n) → ∃ x', σ'.kheap p = some (.schedContext x' n)) :
    SzKeepC C σ σ' := fun sc hsc x n hk => by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x0, n0, hk0, -⟩ := hs.scs sc hsc
  obtain ⟨x', hk'⟩ := h _ x0 n0 hk0
  rw [hk] at hk'; cases hk'
  exact ⟨x0, hk0⟩

/-- Sizes kept by a step that changes only the TCB at `p` (to a TCB). -/
theorem SzKeep.of_tcb {σ σ' : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x' : Fl4Spec.Tcb}
    (hko : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q) (hkp' : σ'.kheap p = some (.tcb x')) : SzKeep σ σ' :=
  fun q y n hq => by
    by_cases e : q = p
    · subst e; rw [hkp'] at hq; cases hq
    · exact ⟨y, by rw [← hko q e]; exact hq⟩

/-- An `SFoot`-or-SC-word step (sizes of its own spec) is a `KFoot` step. -/
theorem WritesIn.kfoot_of_sfoot_scw {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {p : U64} (hp : p ∈ C) {K : U64} (hK : K.val < 96) (hK8 : K.val % 8 = 0)
    (h32 : K ≠ 32#u64) (h : WritesIn st s s' (fun b => SFoot st T c s b ∨ b = scW p K)) :
    WritesIn st s s' (KFoot st T N C c s σ) :=
  h.mono fun b hb => by
    rcases hb with hb | rfl
    · exact KFoot.of_sfoot hb
    · exact KFoot.of_sw (sw_hdr hS hp hK hK8 h32)

/-- A notification-or-SC-word step is a `KFoot` step. -/
theorem WritesIn.kfoot_of_nw_scw {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {p : U64} (hp : p ∈ C) {K : U64} (hK : K.val < 96) (hK8 : K.val % 8 = 0)
    (h32 : K ≠ 32#u64) (h : WritesIn st s s' (fun b => NW N b ∨ b = scW p K)) :
    WritesIn st s s' (KFoot st T N C c s σ) :=
  h.mono fun b hb => by
    rcases hb with hb | rfl
    · exact KFoot.of_nw hb
    · exact KFoot.of_sw (sw_hdr hS hp hK hK8 h32)

/-- A write of an SC's object words, its `REPLY` word kept, is a `KFoot` step. -/
theorem WritesIn.kfoot_of_scobj {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (hw : WritesIn st s s' (ScObj sc n))
    (h32 : L.mem s' (scReplyA sc) = L.mem s (scReplyA sc)) : WritesIn st s s' (KFoot st T N C c s σ) := by
  refine ⟨hw.1, hw.2.1, fun b hb hn => ?_⟩
  by_cases e : b = scReplyA sc
  · subst e; exact h32
  · exact hw.mem_eq hb fun ho => hn (KFoot.of_sw ⟨sc, hsc, x, n, hk, ho, e⟩)

/-- Sizes kept by a step that changes only the SC at `p` (keeping its size). -/
theorem SzKeep.of_sc {σ σ' : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x x' : Fl4Spec.SchedContext} {n : Nat}
    (hko : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q) (hkp : σ.kheap p = some (.schedContext x n))
    (hkp' : σ'.kheap p = some (.schedContext x' n)) : SzKeep σ σ' :=
  fun q y m hq => by
    by_cases e : q = p
    · subst e; rw [hkp'] at hq; cases hq; exact ⟨x, hkp⟩
    · exact ⟨y, by rw [← hko q e]; exact hq⟩

/-- **Footprints compose** across a step that keeps the SC sizes. -/
theorem WritesIn.kfoot_trans {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ σ1 : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (KFoot st T N C c s σ)) (hz : SzKeepC C σ σ1)
    (h2 : WritesIn st s1 s2 (KFoot st T N C c s1 σ1)) : WritesIn st s s2 (KFoot st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb | hb | ⟨sc, hsc, x, n, hk, ho, hne⟩
    · exact hb
    · exact KFoot.of_sfoot ((SFoot.ksb h1.1).1 hb)
    · exact KFoot.of_nw hb
    · obtain ⟨x0, hk0⟩ := hz sc hsc x n hk
      exact KFoot.of_sw ⟨sc, hsc, x0, n, hk0, ho, hne⟩

theorem WritesIn.kfoot_of_sfoot {T N C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (h : WritesIn st s s' (SFoot st T c s)) : WritesIn st s s' (KFoot st T N C c s σ) :=
  h.mono fun _ hb => KFoot.of_sfoot hb

end

end

end Fl4Proofs.P3.Sched
