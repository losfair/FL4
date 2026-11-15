/-
P1: footprints.  `KW` is the set of words the kernel operations of P1 write:
the TCBs' words past their cap slots (`tcb::NUM_SLOTS` slots of `cte::SIZE`
bytes at the start of the object), the cores' node words, the frame words
`Sg` (reply objects, the SCs' `TCB`/`CORE`/`REPLY` words, the
notifications' frame words), the SC objects, and the queue words of the
endpoints and notifications `Es`.  A cap slot lies outside all of these (a
CNode slot is in a CNode, a TCB slot below offset 192 of its TCB, an IRQ slot
in the kernel-global area), so an operation with a `KW` footprint keeps every
cap slot.
-/
import Fl4Proofs.P1.QueueIpc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The words the kernel operations write (relative to the nodes of `s0`). -/
def KW (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 192 ≤ K.val ∧ K.val < 4096 ∧ K.val ≠ 3576 ∧ K.val ≠ 3584 ∧
    b = core.num.U64.wrapping_add y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ o.val ≠ 88 ∧ b = L.nodeAt s0 c o) ∨
  b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨
  (∃ e ∈ Es, b = epHeadA e ∨ b = epTSA e)

/-- A footprint inside `KW`. -/
abbrev Foot (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesIn st s s' (KW st T Cs Sg Scs Z Es s)

variable {Es : Set U64}

theorem KW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : KW st T Cs Sg Scs Z Es s1 b) :
    KW st T Cs Sg Scs Z Es s0 b := by
  rcases h with h | ⟨c, hc, o, ho, h88, e⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, hc, o, ho, h88, by rw [e, nodeAt_of_ksb hk]⟩)
  · exact Or.inr (Or.inr h)

theorem KW.mono {s0 : S} {b : U64} {Es' : Set U64} (h : KW st T Cs Sg Scs Z Es s0 b) (hE : Es ⊆ Es') :
    KW st T Cs Sg Scs Z Es' s0 b := by
  rcases h with h | h | h | h | ⟨e, he, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e, hE he, h⟩)))

theorem Foot.refl (s : S) : Foot st T Cs Sg Scs Z Es s s := WritesIn.refl _ _

theorem Foot.trans {s₁ s₂ s₃ : S} (h₁ : Foot st T Cs Sg Scs Z Es s₁ s₂) (h₂ : Foot st T Cs Sg Scs Z Es s₂ s₃) :
    Foot st T Cs Sg Scs Z Es s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => KW.ksb h₁.1 hb

theorem Foot.mono {s s' : S} {Es' : Set U64} (h : Foot st T Cs Sg Scs Z Es s s') (hE : Es ⊆ Es') :
    Foot st T Cs Sg Scs Z Es' s s' :=
  WritesIn.mono h fun _ hb => KW.mono hb hE

theorem Foot.of {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) (hB : ∀ b, B b → KW st T Cs Sg Scs Z Es s b) :
    Foot st T Cs Sg Scs Z Es s s' := h.mono hB

theorem Foot.of' {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → KW st T Cs Sg Scs Z Es s b) : Foot st T Cs Sg Scs Z Es s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh)⟩

/-! ## The words of `KW` -/

theorem kw_field {s : S} {y K : U64} (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    KW st T Cs Sg Scs Z Es s (core.num.U64.wrapping_add y K) := Or.inl ⟨y, hy, K, hK, hK', hKd.1, hKd.2, rfl⟩

theorem kw_node {s : S} {c o : U64} (hc : c ∈ Cs) (ho : o.val < 4288) (h88 : o.val ≠ 88) :
    KW st T Cs Sg Scs Z Es s (L.nodeAt s c o) :=
  Or.inr (Or.inl ⟨c, hc, o, ho, h88, rfl⟩)

theorem kw_sg {s : S} {b : U64} (hb : b ∈ Sg) : KW st T Cs Sg Scs Z Es s b := Or.inr (Or.inr (Or.inl hb))

theorem kw_sc {s : S} {c b : U64} (hc : c ∈ Scs) (hb : InSC c (Z c) b) : KW st T Cs Sg Scs Z Es s b :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, hb⟩)))

theorem kw_ep {s : S} {e b : U64} (he : e ∈ Es) (hb : b = epHeadA e ∨ b = epTSA e) : KW st T Cs Sg Scs Z Es s b :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, hb⟩)))

theorem foot_wr {s : S} {a v : U64} (ha : Aligned a) (hk : KW st T Cs Sg Scs Z Es s a) :
    Foot st T Cs Sg Scs Z Es s (L.wr s a v) :=
  (writesIn_wr ha).mono fun b hb => hb ▸ hk

theorem foot_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    Foot st T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  foot_wr (field_aligned (hT y hy) hK' hK8) (kw_field hy hK hK' hKd)

theorem foot_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) : Foot st T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s c o) v) :=
  foot_wr (nodeAt_aligned hN ho h8) (kw_node hc ho h88)

theorem LinkOf.kw {s : S} {l : tcbqueue.Link} {W : List U64} {b : U64} (hW : ∀ w ∈ W, w ∈ T) (h : LinkOf l W b) :
    KW st T Cs Sg Scs Z Es s b := by
  obtain ⟨w, hw, e | e⟩ := h <;> subst e
  · rw [nextA_eq']; exact kw_field (hW w hw) (by cases l <;> simp [nextOff]) (by cases l <;> simp [nextOff])
      (by cases l <;> simp [nextOff])
  · rw [prevA_eq']; exact kw_field (hW w hw) (by cases l <;> simp [prevOff]) (by cases l <;> simp [prevOff])
      (by cases l <;> simp [prevOff])

theorem LawfulStore.NodeOf.kw {s : S} {c : U64} {P : Nat → Prop} {b : U64} (hc : c ∈ Cs) (hP : ∀ o, P o → o ≠ 88)
    (h : L.NodeOf s c P b) : KW st T Cs Sg Scs Z Es s b := by
  obtain ⟨o, hPo, ho, -, rfl⟩ := h; exact kw_node hc ho (hP _ hPo)

theorem LawfulStore.QFoot.kw {s : S} {W : List U64} {c : U64} {P : Nat → Prop} {t b : U64} (hW : ∀ w ∈ W, w ∈ T)
    (hc : c ∈ Cs) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (hP : ∀ o, P o → o ≠ 88) (h : L.QFoot s W c P t b) :
    KW st T Cs Sg Scs Z Es s b := by
  rcases h with h | h | h | h
  · exact h.kw hW
  · exact h.kw hc hP
  · subst h; rw [inqA_eq]; exact kw_field ht (by simp) (by simp) (by simp)
  · exact h.kw hcpu (fun o e => by omega)

theorem EpFoot.kw {s : S} {W : List U64} {e b : U64} (hW : ∀ w ∈ W, w ∈ T) (he : e ∈ Es) (h : EpFoot W e b) :
    KW st T Cs Sg Scs Z Es s b := by
  rcases h with h | h | h
  · exact h.kw hW
  · exact kw_ep he (Or.inl h)
  · exact kw_ep he (Or.inr h)

theorem InRing.kw {s : S} {c b : U64} (hc : c ∈ Scs) (h : InRing c (Z c) b) : KW st T Cs Sg Scs Z Es s b :=
  kw_sc hc h.inSC



/-! ## Endpoint words outside a footprint -/

/-- The queue words of a heap endpoint or notification are outside `KW ∅`. -/
theorem ep_not_kw {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e b : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (he : H e = some .ep ∨ H e = some .ntfn) (hb : b = epHeadA e ∨ b = epTSA e) :
    ¬ KW st T Cs Sg Scs Z ∅ s b := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
  obtain ⟨hE, hEN, -⟩ := hEW.1 e heE
  have hΩ := hEW.2.2.1 e heE
  have hv : b.val = e.val ∨ b.val = e.val + 8 := by
    rcases hb with rfl | rfl
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE)
  have hfit := hE.fits
  rintro (⟨y, hy, K, h1, h2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', -⟩)
  · rw [field_val (h.tcbs y hy) h2] at hv
    have := hE.disj y hy; omega
  · rw [nodeAt_val (h.nodes c hc) ho] at hv
    have := hEN.1 c hc; omega
  · have := hΩ b (hsub b hm); omega
  · have hal : Aligned b := by
      rcases hb with rfl | rfl
      · exact (ep_aligned hE).1
      · exact (ep_aligned hE).2
    have := hΩ b (hO.scW c hc b hal hin); omega
  · exact absurd he' (Set.notMem_empty e')

/-- A `KW ∅` footprint keeps the queue of a heap endpoint or notification. -/
theorem Foot.epQ {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e : U64}
    (f : Foot st T Cs Sg Scs Z ∅ s s') (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (he : H e = some .ep ∨ H e = some .ntfn) :
    L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e) := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
  obtain ⟨hE, -, -⟩ := hEW.1 e heE
  exact ⟨f.mem_eq (ep_aligned hE).1 (ep_not_kw h hO hsub he (Or.inl rfl)),
    f.mem_eq (ep_aligned hE).2 (ep_not_kw h hO hsub he (Or.inr rfl))⟩


/-! ## The current core's scheduler words -/

/-- The current core's `CUR_THREAD`, `IDLE_THREAD` and `SCHED_ACTION` words are kept. -/
def ANI (st : machine.Store S) [L : LawfulStore st] (s s' : S) : Prop :=
  L.actionW s' = L.actionW s ∧ L.idleW s' = L.idleW s ∧ L.curW s' = L.curW s

theorem ANI.refl (s : S) : ANI st s s := ⟨rfl, rfl, rfl⟩
theorem ANI.trans {s₁ s₂ s₃ : S} (h₁ : ANI st s₁ s₂) (h₂ : ANI st s₂ s₃) : ANI st s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem ani_wr {s : S} {a v : U64} {T : Set U64} (hN : NodePlaced st T s (L.cpu s)) (ha : Aligned a)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16) → a.val ≠ (L.nodeAt s (L.cpu s) o).val) :
    ANI st s (L.wr s a v) := by
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16) →
      L.mem (L.wr s a v) (L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN (by omega) (by omega)) (hn o ho)
  exact ⟨by unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega),
    by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega),
    by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega)⟩

theorem ani_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) : ANI st s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  ani_wr hN (field_aligned (hT y hy) hK hK8) fun o ho e =>
    node_ne_field hN (by omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e).symm

theorem ani_out {s : S} {a v : U64} (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs)
    (ho : OutsideObjs st T Cs s a) : ANI st s (L.wr s a v) :=
  ani_wr hN ho.1 fun o h e => out_ne_node ho hc hN (by omega) e.symm

theorem ani_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s))
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (hno : c = L.cpu s → o.val ≠ 0 ∧ o.val ≠ 8 ∧ o.val ≠ 16) :
    ANI st s (L.wr s (L.nodeAt s c o) v) :=
  ani_wr hN' (nodeAt_aligned hN ho h8) fun o' h e =>
    node_ne_node hN hN' ho (by omega) (fun hc => by have := hno hc; omega) e

/-! ## The scheduler queues -/

section queues
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.enqueue.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => Foot.of hh.1 fun b hb => hb.kw ?_ hc h.cur ht (fun o ho => by omega)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.dequeue.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  exact WP.spec_mono (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (h.queued t ht).1) fun s' hh => Foot.of hh.1 fun b hb => hb.kw (hR1.1.rel _ hp).mem hc h.cur ht (fun o ho => by omega)

theorem sched.release_remove.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  exact WP.spec_mono (sched.release_remove.foot s t _ h.tcbs ht (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc)
    (h.released t ht).1) fun s' hh => Foot.of hh.1 fun b hb => hb.kw (h.release _ hc).mem hc h.cur ht (fun o ho => by unfold RelOffs at ho; omega)

/-- A footprint keeps the placement of the current core's node. -/
theorem Foot.curN {s s' : S} {Es : Set U64} (f : Foot st T Cs Sg Scs Z Es s s') (hN : NodePlaced st T s (L.cpu s)) :
    NodePlaced st T s' (L.cpu s') := by rw [f.2.1]; exact hN.ksb f.1

theorem sched.set_action.kw (s : S) (v : U64) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_action st s v ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e; exact foot_node hN hc (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)

theorem sched.schedule_tcb.kw (s : S) (t : obj.Tcb) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.schedule_tcb st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, e1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 (Foot.refl _)
      · exact sched.set_action.kw s _ hN hc
    · exact (WP.spec_ok _).2 (Foot.refl _)
  · exact (WP.spec_ok _).2 (Foot.refl _)

theorem sched.set_thread_state.kw (s : S) (t : obj.Tcb) (v : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) : sched.set_thread_state st s t v ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ t (by rw [LawfulStore.cpu_wr]; exact (h.nodes _ h.cur).ksb (L.ksb_wr _ _ _))
    (by rw [LawfulStore.cpu_wr]; exact h.cur)) fun s2 f2 => ?_
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact foot_field h.tcbs ht (by simp) (by simp) (by simp) (by simp)
  exact f1.trans f2


theorem sched.reschedule_required.kw (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => Foot st T Cs Sg Scs Z Es s s1 ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact sched.enqueue.kw s act h hT
        · exact (WP.spec_ok _).2 (Foot.refl _)
      · exact (WP.spec_ok _).2 (Foot.refl _)
    · exact (WP.spec_ok _).2 (Foot.refl _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  exact WP.spec_mono (sched.set_action.kw s1 _ (by rw [f1.2.1]; exact (h.nodes _ h.cur).ksb f1.1)
    (by rw [f1.2.1]; exact h.cur)) fun s2 f2 => f1.trans f2


theorem sched.possible_switch_to.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 (Foot.refl _)
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (Foot.refl _)
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.kw s t h ht
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.kw s t h ht
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h) (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s h)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, f1⟩
    exact WP.spec_mono (sched.enqueue.kw s1 t h1 ht) fun s2 f2 => f1.trans f2
  · exact sched.set_action.kw s _ (h.nodes _ h.cur) h.cur


theorem endpoint.unblock_sporadic.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => Foot.of w3 fun b hb => ?_
      rcases hb with hb | rfl
      · exact hb.kw hiS
      · exact kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega)
    · exact (WP.spec_ok _).2 (Foot.refl _)
  · exact (WP.spec_ok _).2 (Foot.refl _)

theorem notification.unblock_sporadic.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => Foot.of w3 fun b hb => ?_
      rcases hb with hb | rfl
      · exact hb.kw hiS
      · exact kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega)
    · exact (WP.spec_ok _).2 (Foot.refl _)
  · exact (WP.spec_ok _).2 (Foot.refl _)

theorem ipc.reply_unlink.kw (s : S) (r t : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht : t ∈ T) :
    ipc.reply_unlink st s r t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have hm : rTcbA r ∈ Ω := hsub _ (hX.1.tcbW hr)
  have ha := (h.omega _ hm).1
  have h1 := inv_of_free h ((writesIn_wr (v := 0#u64) ha).mono fun b hb => hb ▸ Or.inl hm)
  exact WP.spec_mono (sched.set_thread_state.kw _ t _ h1 ht) fun s2 f2 =>
    (foot_wr ha (kw_sg (hX.1.tcbW hr))).trans f2

end queues

end

end Fl4Proofs.P1
