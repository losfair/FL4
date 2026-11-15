/-
P1: callers of the queue operations keep `SchedQueuesInv`:
`reschedule_required`, `possible_switch_to`, `set_priority` (the
dequeue / set priority / enqueue pattern of seL4 `setPriority`), and
`append` (`tcbSchedAppend`, used by `schedule`).
-/
import Fl4Proofs.P1.QueueSchedInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}

/-! ## Specs of the small helpers -/

@[step] theorem obj.Tcb.state.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.state st t s ⦃ v => v = L.mem s (stA t) ⦄ := by
  unfold obj.Tcb.state; step*; simp_all [stA]

@[step] theorem obj.Sc.is_null.spec (sc : obj.Sc) : obj.Sc.is_null sc ⦃ b => b = decide (sc = 0#u64) ⦄ := by
  unfold obj.Sc.is_null; simp

@[step] theorem sched.action.spec (s : S) : sched.action st s ⦃ v => v = L.actionW s ⦄ := by
  unfold sched.action; step*; simp_all [LawfulStore.actionW]

@[step] theorem sched.set_action.spec (s : S) (v : U64) :
    sched.set_action st s v ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v ⦄ := by
  unfold sched.set_action; step*; simp_all

@[step] theorem sched.cur_thread.spec (s : S) :
    sched.cur_thread st s ⦃ v => v = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ⦄ := by
  unfold sched.cur_thread; step*; simp_all

@[step] theorem obj.Tcb.set_prio.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_prio st t s v ⦃ s' => s' = L.wr s (prioA t) v ⦄ := by
  unfold obj.Tcb.set_prio; step*; simp_all [prioA]

@[step] theorem sched.is_runnable.spec (s : S) (t : obj.Tcb) :
    sched.is_runnable st s t ⦃ b => b = decide (L.mem s (stA t) = sched.TS_RUNNING ∨
      L.mem s (stA t) = sched.TS_RESTART ∨ L.mem s (stA t) = sched.TS_RUNNING_VM) ⦄ := by
  unfold sched.is_runnable
  step
  repeat' split
  all_goals simp_all [Runnable, lift]

/-- `is_schedulable` only says yes for a thread outside the release queue. -/
@[step] theorem sched.is_schedulable.spec (s : S) (t : obj.Tcb) :
    sched.is_schedulable st s t ⦃ b => b = true → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ⦄ := by
  unfold sched.is_schedulable
  step with sched.is_runnable.spec
  split <;> (try simp only [bind_ok]) <;> step* <;> try simp_all
  all_goals
    unfold sporadic.sc_active
    step* <;> try simp_all

/-! ## TCB fields as addresses -/

theorem field_val {y K : U64} (hy : TcbAddr y) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add y K).val = y.val + K.val := by
  have := hy.fits
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- Two TCB fields are different words unless they are the same field of the
same TCB. -/
theorem field_ne {x y K1 K2 : U64} (hx : TcbAddr x) (hy : TcbAddr y) (h1 : K1.val < 4096) (h2 : K2.val < 4096)
    (hne : x = y → K1.val ≠ K2.val) : core.num.U64.wrapping_add x K1 ≠ core.num.U64.wrapping_add y K2 := by
  intro e
  have hv := congrArg UScalar.val e
  rw [field_val hx h1, field_val hy h2] at hv
  have := hx.align; have := hy.align
  by_cases hxy : x = y
  · subst hxy; exact hne rfl (by omega)
  · have : x.val ≠ y.val := fun e' => hxy (UScalar.eq_of_val_eq e')
    omega

theorem node_ne_field {s : S} {c o y K : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288) (hy : y ∈ T)
    (hya : TcbAddr y) (hK : K.val < 4096) : L.nodeAt s c o ≠ core.num.U64.wrapping_add y K := by
  intro e
  have hv := congrArg UScalar.val e
  rw [field_val hya hK] at hv
  have := nodeAt_out hN ho hy; omega

theorem nextA_eq' (l : tcbqueue.Link) (y : U64) : nextA l y = core.num.U64.wrapping_add y (nextOff l) := rfl
theorem prevA_eq' (l : tcbqueue.Link) (y : U64) : prevA l y = core.num.U64.wrapping_add y (prevOff l) := rfl

/-! ## Writes away from the queues -/

theorem out_ne_node {Cs : Set U64} {s : S} {a c o : U64} (ha : OutsideObjs st T Cs s a) (hc : c ∈ Cs)
    (hN : NodePlaced st T s c) (ho : o.val < 4288) : (L.nodeAt s c o).val ≠ a.val := by
  rw [nodeAt_val hN ho]; have := ha.2.2 c hc; omega

theorem out_ne_field {Cs : Set U64} {s : S} {a y K : U64} (ha : OutsideObjs st T Cs s a) (hy : y ∈ T)
    (hya : TcbAddr y) (hK : K.val < 4096) : (core.num.U64.wrapping_add y K).val ≠ a.val := by
  rw [field_val hya hK]; have := ha.2.1 y hy; omega

theorem blockA_eq (t : U64) : blockA t = core.num.U64.wrapping_add t 3336#u64 := rfl

/-- A TCB field write leaves the node words alone. -/
theorem nodeword_wr_field {s : S} {c y K v o : U64} (hN : NodePlaced st T s c) (hy : y ∈ T) (hya : TcbAddr y)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    L.mem (L.wr s (core.num.U64.wrapping_add y K) v) (L.nodeAt (L.wr s (core.num.U64.wrapping_add y K) v) c o) =
      L.mem s (L.nodeAt s c o) := by
  rw [nodeAt_wr]
  exact L.mem_wr_ne (field_aligned hya hK hK8) (nodeAt_aligned hN ho h8)
    (fun e => node_ne_field hN ho hy hya hK (UScalar.eq_of_val_eq e).symm)

/-- The current and idle thread words after a TCB field write. -/
theorem curidle_wr_field {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem (L.wr s (core.num.U64.wrapping_add y K) v)
      (L.nodeAt (L.wr s (core.num.U64.wrapping_add y K) v) (L.cpu (L.wr s (core.num.U64.wrapping_add y K) v))
        layout.node.CUR_THREAD) ∈ T ∧
    L.mem (L.wr s (core.num.U64.wrapping_add y K) v)
      (L.nodeAt (L.wr s (core.num.U64.wrapping_add y K) v) (L.cpu (L.wr s (core.num.U64.wrapping_add y K) v))
        layout.node.IDLE_THREAD) ∈ T := by
  simp only [LawfulStore.cpu_wr]
  have hN' := h.nodes _ h.cur
  rw [nodeword_wr_field hN' hy (h.tcbs y hy) hK hK8 (by rw [curth0]; omega) (by rw [curth0]),
    nodeword_wr_field hN' hy (h.tcbs y hy) hK hK8 (by rw [idle8]; omega) (by rw [idle8])]
  exact ⟨h.curT, h.idleT⟩

/-- A node write leaves the other words of the nodes alone. -/
theorem nodeword_other {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {c0 o c o' v : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hc0 : c0 ∈ Cs) (hc : c ∈ Cs)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (ho' : o'.val < 4288) (h8' : o'.val % 8 = 0)
    (hne : c0 = c → o.val ≠ o'.val) :
    L.mem (L.wr s (L.nodeAt s c0 o) v) (L.nodeAt s c o') = L.mem s (L.nodeAt s c o') := by
  by_cases e : c0 = c
  · subst e; rw [rd_node_wr_node (h.nodes c0 hc0) ho ho' h8 h8', if_neg (hne rfl)]
  · exact rd_node_wr_node_cpu (h.nodes c hc) (h.nodes c0 hc0) ho ho' h8 h8' e

/-- A write to a node word below the release queue (`SCHED_ACTION`,
`REPROGRAM`, ...) keeps the invariant, if the action stays valid. -/
theorem inv_wr_node_low {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {c0 o v : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hc0 : c0 ∈ Cs) (ho : o.val < 128)
    (ho2 : o.val ≠ 64 ∧ o.val ≠ 72) (h8 : o.val % 8 = 0)
    (hact : L.actionW (L.wr s (L.nodeAt s c0 o) v) = 0#u64 ∨ L.actionW (L.wr s (L.nodeAt s c0 o) v) = 1#u64 ∨
      L.actionW (L.wr s (L.nodeAt s c0 o) v) ∈ T)
    (hact2 : L.actionW (L.wr s (L.nodeAt s c0 o) v) ∈ T →
      Runnable (L.mem s (stA (L.actionW (L.wr s (L.nodeAt s c0 o) v)))) ∧
      ∀ c ∈ Cs, L.actionW (L.wr s (L.nodeAt s c0 o) v) ∉ R c)
    (hcurT : L.mem (L.wr s (L.nodeAt s c0 o) v) (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ∈ T)
    (hidleT : L.mem (L.wr s (L.nodeAt s c0 o) v) (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD) ∈ T) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (L.nodeAt s c0 o) v) Q R := by
  have hT := h.tcbs
  have hN0 := h.nodes c0 hc0
  have ha := nodeAt_aligned hN0 (by omega) h8 (off := o)
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s c0 o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => node_ne_field hN0 (by omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e))
  refine inv_of_agree h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 h3 => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp)) (fun y hy => fld y hy _ (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp))) hact
    (fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp)⟩)
    ?_ (h.eps.agree (L.ksb_wr _ _ _) (fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp)⟩)
    (fun y hy => ⟨by rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]),
      by rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff])⟩)
    (fun a hao => L.mem_wr_ne ha hao.1 (out_ne_node hao hc0 hN0 (by omega))))
    (by simp only [LawfulStore.cpu_wr, nodeAt_wr]; exact hcurT)
    (by simp only [LawfulStore.cpu_wr, nodeAt_wr]; exact hidleT)
  · rw [nextA_eq']; exact fld y hy _ (by cases tcbqueue.Link.Sched <;> simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff])
  · by_cases e : c0 = c
    · subst e
      rw [rd_node_wr_node hN0 (by omega) h1 h8 h2, if_neg (by omega)]
    · exact rd_node_wr_node_cpu (h.nodes c hc) hN0 (by omega) h1 h8 h2 e
  · intro haT
    rw [stA_eq, fld _ haT _ (by simp) (by simp), ← stA_eq]
    exact hact2 haT

/-- Setting the priority of a thread in no ready queue keeps the invariant. -/
theorem inv_wr_prio {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (h0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64)
    (hv : v.val < 256) : SchedQueuesInvX st T Cs Ω H X (L.wr s (prioA t) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (prioA t) := field_aligned hta (by simp) (by simp)
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3448) →
      L.mem (L.wr s (prioA t) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h => hne rfl h.symm)
        (UScalar.eq_of_val_eq e))
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (prioA t) v) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have hsb : ∀ y ∈ T, L.mem (L.wr s (prioA t) v) (stA y) = L.mem s (stA y) ∧
      L.mem (L.wr s (prioA t) v) (blockA y) = L.mem s (blockA y) := fun y hy =>
    ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp)⟩
  refine inv_of_agree h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 h3 => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp)) (fun y hy => ?_) ?_ hsb
    (by rw [e]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT)
    (h.eps.agree (L.ksb_wr _ _ _) hsb
      (fun y hy => ⟨by rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff]),
        by rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])⟩)
      (fun a hao => L.mem_wr_ne ha hao.1 (out_ne_field hao ht hta (by simp))))
    (curidle_wr_field (K := 3448#u64) h ht (by simp) (by simp)).1
    (curidle_wr_field (K := 3448#u64) h ht (by simp) (by simp)).2
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  · by_cases e : y = t
    · subst e; right; exact ⟨h0, by rw [L.mem_wr_same ha]; exact hv⟩
    · left; exact fld y hy _ (by simp) (by simp) (fun e' => absurd e' e)
  · rw [e]; exact h.action

/-- `set_action` with a valid action keeps the invariant. -/
theorem inv_set_action {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hv : v = 0#u64 ∨ v = 1#u64 ∨ v ∈ T)
    (hv2 : v ∈ T → Runnable (L.mem s (stA v)) ∧ ∀ c ∈ Cs, v ∉ R c) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) Q R ∧
      L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) = v := by
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) = v := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_same (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
  have o0 := nodeword_other (v := v) h h.cur h.cur (o := layout.node.SCHED_ACTION) (o' := layout.node.CUR_THREAD)
    (by rw [act_val]; omega) (by rw [act_val]) (by rw [curth0]; omega) (by rw [curth0])
    (fun _ => by rw [act_val, curth0]; omega)
  have o8 := nodeword_other (v := v) h h.cur h.cur (o := layout.node.SCHED_ACTION) (o' := layout.node.IDLE_THREAD)
    (by rw [act_val]; omega) (by rw [act_val]) (by rw [idle8]; omega) (by rw [idle8])
    (fun _ => by rw [act_val, idle8]; omega)
  exact ⟨inv_wr_node_low h h.cur (by rw [act_val]; omega) (by rw [act_val]; omega) (by rw [act_val])
    (by rw [e]; exact hv) (by rw [e]; exact hv2) (by rw [o0]; exact h.curT) (by rw [o8]; exact h.idleT), e⟩

theorem resume_val : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
theorem choose_val : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl

/-! ## `reschedule_required`, `possible_switch_to` -/

theorem notT_small {v : U64} (hT : TcbPlaced T) (hv : v.val < 4096) : v ∉ T := by
  intro h; have ha := hT v h; have := ha.ne0; have := ha.align; omega

theorem stA_wr_node {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c o v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hc : c ∈ Cs) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    ∀ y ∈ T, L.mem (L.wr s (L.nodeAt s c o) v) (stA y) = L.mem s (stA y) := fun y hy => by
  rw [stA_eq]
  exact L.mem_wr_ne (nodeAt_aligned (h.nodes c hc) ho h8) (field_aligned (h.tcbs y hy) (by simp) (by simp))
    (fun e => node_ne_field (h.nodes c hc) ho hy (h.tcbs y hy) (by simp) (UScalar.eq_of_val_eq e))

/-- seL4 `rescheduleRequired` keeps the invariant (release queues and
thread states unchanged) and leaves the action choose-new. -/
theorem sched.reschedule_required.inv {Cs X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => (∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R) ∧
      L.actionW s' = 1#u64 ∧ ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ⦄ := by
  unfold sched.reschedule_required
  step as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => (∃ Q', SchedQueuesInvX st T Cs Ω H X s1 Q' R) ∧
      ∀ y ∈ T, L.mem s1 (stA y) = L.mem s (stA y) ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        step as ⟨b, hb⟩
        split
        · have hc := h.aff act hT
          have hp := h.prio act hT
          have hR1 := h.ready _ hc
          refine WP.spec_mono (WP.spec_and (sched.enqueue.inv s act Q R h hT (fun _ => hb ‹_›) (fun _ => hrun))
            (sched.enqueue.foot s act _ h.tcbs hT hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
              (fun h0 => h.notQ hT h0 hc hp))) ?_
          rintro s1 ⟨h1, hw, -⟩
          have hW : ∀ w ∈ act :: Q (L.mem s (affA act)) (L.mem s (prioA act)), w ∈ T := by
            intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact hT
            · exact h.memT hc hp hw
          obtain ⟨hsb, -, -⟩ := ext_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) hT hc h.cur hw
          exact ⟨⟨_, h1⟩, fun y hy => (hsb y hy).1⟩
        · simp only [WP.spec_ok]; exact ⟨⟨Q, h⟩, by simp⟩
      · simp only [WP.spec_ok]; exact ⟨⟨Q, h⟩, by simp⟩
    · simp only [WP.spec_ok]; exact ⟨⟨Q, h⟩, by simp⟩
  refine WP.spec_bind hpart ?_
  rintro s1 ⟨⟨Q', h1⟩, hst1⟩
  step as ⟨s2, s2_post⟩
  subst s2_post
  rw [choose_val]
  obtain ⟨h2, e⟩ := inv_set_action (v := 1#u64) h1 (Or.inr (Or.inl rfl))
    (fun h1T => absurd h1T (notT_small h.tcbs (by simp)))
  refine ⟨⟨Q', h2⟩, e, fun y hy => ?_⟩
  rw [stA_wr_node h1 h1.cur (by rw [act_val]; omega) (by rw [act_val]) y hy, hst1 y hy]

/-- seL4 `possibleSwitchTo` keeps the invariant (release queues
unchanged), for a runnable thread. -/
theorem sched.possible_switch_to.inv {Cs X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hrun : Runnable (L.mem s (stA t))) :
    sched.possible_switch_to st s t ⦃ s' => ∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R ⦄ := by
  have enq : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 → ∀ s1 Q1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R →
      L.mem s1 (stA t) = L.mem s (stA t) →
      sched.enqueue st s1 t ⦃ s' => ∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R ⦄ := by
    intro hr0 s1 Q1 h1 hst
    have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hc
      exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hc)
    exact WP.spec_mono (sched.enqueue.inv s1 t Q1 R h1 ht (fun _ => hr1) (fun _ => hst ▸ hrun))
      fun s' h' => ⟨_, h'⟩
  unfold sched.possible_switch_to sched.cur_domain
  step*
  all_goals try (have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := not_not.1 (fun hc => ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)))
  all_goals try exact enq hr0 s Q h rfl
  · refine WP.spec_bind (sched.reschedule_required.inv s Q R h) ?_
    rintro s1 ⟨⟨Q1, h1⟩, -, hst⟩
    exact enq hr0 s1 Q1 h1 (hst t ht)
  · subst s'_post
    exact ⟨Q, (inv_set_action h (Or.inr (Or.inr ht)) (fun _ => ⟨hrun, fun c hc => h.notR ht hr0 hc⟩)).1⟩

/-! ## Endpoint and notification reordering, seen from the scheduler -/

/-- The footprint of `reorder_ep` / `reorder_ntfn`: the `Ep` links of the
queue and the object's two words. -/
def EpFoot (W : List U64) (ep : U64) (b : U64) : Prop := LinkOf .Ep W b ∨ b = epHeadA ep ∨ b = epTSA ep

theorem LinkOf.mono {l : tcbqueue.Link} {W W' : List U64} {b : U64} (h : LinkOf l W b) (hW : W ⊆ W') :
    LinkOf l W' b := by
  obtain ⟨w, hw, e⟩ := h; exact ⟨w, hW hw, e⟩

theorem reorder_foot_tail {s s2 : S} {ep : U64} {q : tcbqueue.Queue} {state : U64} {W : List U64}
    (hE : EpPlaced T ep) (h2 : WritesIn st s s2 (LinkOf .Ep W)) :
    WritesIn st s (L.wr (L.wr s2 (epHeadA ep) q.head) (epTSA ep) ((q.end &&& ~~~3#u64) ||| (state &&& 3#u64)))
      (EpFoot W ep) := by
  obtain ⟨ah, at'⟩ := ep_aligned hE
  exact ((h2.trans (writesIn_wr ah)).trans (writesIn_wr at')).mono fun b hb => by
    rcases hb with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem endpoint.reorder_ep.foot (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    endpoint.reorder_ep st s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄ := by
  unfold endpoint.reorder_ep
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 (h.mem t ht) h.nodup.not_mem_erase) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w := hf1.writesIn.trans hf2.writesIn
  step*
  subst_vars
  refine reorder_foot_tail hE (w.mono fun b hb => ?_)
  rcases hb with hb | hb
  · exact hb
  · exact hb.mono (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ht
      · exact List.mem_of_mem_erase hy)

theorem notification.reorder_ntfn.foot (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    notification.reorder_ntfn st s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄ := by
  unfold notification.reorder_ntfn
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 (h.mem t ht) h.nodup.not_mem_erase) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w := hf1.writesIn.trans hf2.writesIn
  step*
  subst_vars
  refine reorder_foot_tail hE (w.mono fun b hb => ?_)
  rcases hb with hb | hb
  · exact hb
  · exact hb.mono (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ht
      · exact List.mem_of_mem_erase hy)


theorem mem_afterLast {pr : U64 → U64} {p t : U64} (xs : List U64) (y : U64) :
    y ∈ afterLast pr p t xs ↔ y = t ∨ y ∈ xs := by
  induction xs with
  | nil => simp [afterLast]
  | cons x xs ih =>
    by_cases hc : (xs.any fun y => !decide (p > pr y)) = true
    · simp only [afterLast, hc, ite_true, List.mem_cons, ih]; tauto
    · simp only [afterLast, hc, Bool.false_eq_true, ite_false, List.mem_cons]; tauto

theorem mem_insPrio {pr : U64 → U64} {p t : U64} {xs : List U64} {y : U64} :
    y ∈ insPrio pr p t xs ↔ y = t ∨ y ∈ xs := by
  cases xs with
  | nil => simp [insPrio]
  | cons x xs =>
    by_cases hc : p > pr x
    · simp only [insPrio, hc, ite_true]; exact List.mem_cons
    · simp only [insPrio, hc, ite_false]; exact mem_afterLast _ _

/-- An operation on one endpoint (or notification) queue `e`, touching only
its footprint `EpFoot`, that leaves the queue holding `xs'`: some old members,
the others joining the exception set. -/
theorem inv_ep_step {Cs X X' : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e : U64} {xs' : List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E)
    (hw : WritesIn st s s' (EpFoot (EQ e) e))
    (hq' : QueueRel (L.mem s') T .Ep (L.epQ s' e) xs') (hst : xs' ≠ [] → L.epState s' e = L.epState s e)
    (hemp : xs' = [] → (H e = some .ep → L.epState s' e = 0#u64) ∧ (H e = some .ntfn → L.epState s' e ≠ 1#u64))
    (hsub : ∀ y ∈ xs', y ∈ EQ e) (hrest : ∀ y ∈ EQ e, y ∉ xs' → y ∈ X')
    (hXX : ∀ y, y ∈ X → y ∈ X') (hXn : ∀ y, y ∈ X' → y ∈ X ∨ y ∈ EQ e) (hx' : ∀ y ∈ xs', y ∉ X') :
    SchedQueuesInvX st T Cs Ω H X' s' Q R := by
  have hT := h.tcbs
  obtain ⟨w1, w2, w5, w3, w4, w6⟩ := hEW
  obtain ⟨hE, hEN, hq⟩ := w1 e he
  have hWT : ∀ w ∈ EQ e, w ∈ T := hq.mem
  have epv : ∀ (e' a : U64), EpPlaced T e' → (a = epHeadA e' ∨ a = epTSA e') →
      a.val = e'.val ∨ a.val = e'.val + 8 := by
    rintro e' a hE' (rfl | rfl)
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE')
  -- TCB fields other than `Ep` links, node words and other objects' words are outside the footprint.
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 h1 h2
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · rw [nextA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; exact h1) e'
    · rw [prevA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; exact h2) e'
    · have hv := epv e _ hE e'
      rw [field_val (hT y hy) hK] at hv
      have := hE.disj y hy
      omega
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    have hN := h.nodes c hc
    refine hw.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · exact nodeAt_ne_nextA hN ho (hWT w hw') (hT w (hWT w hw')) _ e'
    · exact nodeAt_ne_prevA hN ho (hWT w hw') (hT w (hWT w hw')) _ e'
    · have hv := epv e _ hE e'
      rw [nodeAt_val hN ho] at hv
      have := hEN.1 c hc
      omega
  have oth : ∀ e' ∈ E, e' ≠ e → ∀ a, (a = epHeadA e' ∨ a = epTSA e') → L.mem s' a = L.mem s a := by
    intro e' he' hne a ha
    have hE' := (w1 e' he').1
    have hal : Aligned a := by
      rcases ha with rfl | rfl
      · exact (ep_aligned hE').1
      · exact (ep_aligned hE').2
    have hav := epv e' a hE' ha
    refine hw.mem_eq hal ?_
    rintro (⟨w, hw', e2 | e2⟩ | e2)
    · have := nextA_inside (hT w (hWT w hw')) .Ep; rw [← e2] at this
      have := hE'.disj w (hWT w hw'); omega
    · have := prevA_inside (hT w (hWT w hw')) .Ep; rw [← e2] at this
      have := hE'.disj w (hWT w hw'); omega
    · have hv := epv e a hE e2
      have := w2 e' he' e he hne; omega
  have hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y) :=
    fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp)⟩
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    exact nod _ h.cur _ (by rw [act_val]; omega) (by rw [act_val])
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hw.1]
  refine inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩) (fun c hc o h1 h2 _ => nod c hc o h1 h2)
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (by simp) (by simp))) (by rw [hact]; exact h.action) hsb
    (by rw [hact]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT) ?_
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [curth0]; omega) (by rw [curth0])]; exact h.curT)
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [idle8]; omega) (by rw [idle8])]; exact h.idleT)
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  refine ⟨E, Function.update EQ e xs', fun e' he' => ?_, w2, w5, fun e' he' y hy => ?_, fun y hy hyX hb => ?_,
    w6.agree (fun y hy => Or.inl (fun hX => hy (hXX y hX))) (fun y hy _ _ => hsb y hy) (fun e' he' y hy => ?_)
      (fun e' he' y hy => ?_) (fun e' he' hne => ?_) (fun e' he' h0 => ?_)⟩
  rotate_left 3
  · by_cases hee : e' = e
    · subst hee; rw [Function.update_self] at hy; exact hsub y hy
    · rw [Function.update_of_ne hee] at hy; exact hy
  · by_cases hee : e' = e
    · subst hee; rw [Function.update_self] at hy; exact (hsb y (hq'.mem y hy)).1
    · rw [Function.update_of_ne hee] at hy; exact (hsb y ((w1 e' he').2.2.mem y hy)).1
  · by_cases hee : e' = e
    · subst hee; rw [Function.update_self] at hne; exact hst hne
    · simp only [LawfulStore.epState, oth e' he' hee _ (Or.inr rfl)]
  · by_cases hee : e' = e
    · subst hee; rw [Function.update_self] at h0; exact Or.inr (hemp h0)
    · rw [Function.update_of_ne hee] at h0
      exact Or.inl ⟨h0, by simp only [LawfulStore.epState, oth e' he' hee _ (Or.inr rfl)]⟩
  · refine ⟨(w1 e' he').1, ⟨fun c hc => by rw [hnb]; exact (w1 e' he').2.1.1 c hc, by rw [hw.1]; exact (w1 e' he').2.1.2⟩, ?_⟩
    by_cases hee : e' = e
    · subst hee; rw [Function.update_self]; exact hq'
    · rw [Function.update_of_ne hee]
      have hq2 := (w1 e' he').2.2
      have eq : L.epQ s' e' = L.epQ s e' := by
        simp only [LawfulStore.epQ, oth e' he' hee _ (Or.inl rfl), oth e' he' hee _ (Or.inr rfl)]
      rw [eq]
      refine ⟨hq2.nodup, hq2.mem, hq2.head, hq2.last, hq2.seg.congr fun y hy => ?_⟩
      have hyT := hq2.mem y hy
      have hyE : y ∉ EQ e := fun hm => hee ((w3 e' he' y hy).2.1.symm.trans (w3 e he y hm).2.1)
      have hk := fun (K : U64) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKl : K.val = 3496 ∨ K.val = 3504) =>
        hw.mem_eq (field_aligned (hT y hyT) hK hK8) (by
          rintro (⟨w, hw', e2 | e2⟩ | e2)
          · have hwy : w ≠ y := fun h' => hyE (h' ▸ hw')
            rw [nextA_eq'] at e2
            exact field_ne (hT y hyT) (hT w (hWT w hw')) hK (by simp [nextOff])
              (fun h' => absurd h'.symm hwy) e2
          · have hwy : w ≠ y := fun h' => hyE (h' ▸ hw')
            rw [prevA_eq'] at e2
            exact field_ne (hT y hyT) (hT w (hWT w hw')) hK (by simp [prevOff])
              (fun h' => absurd h'.symm hwy) e2
          · have hv := epv e _ hE e2
            rw [field_val (hT y hyT) hK] at hv
            have := hE.disj y hyT; omega)
      exact ⟨by rw [prevA_eq']; exact hk _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]),
        by rw [nextA_eq']; exact hk _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])⟩
  · by_cases hee : e' = e
    · subst hee
      rw [Function.update_self] at hy
      have := w3 e' he y (hsub y hy)
      have hyT := hq'.mem y hy
      exact ⟨hx' y hy, by rw [(hsb y hyT).2]; exact this.2.1, by rw [(hsb y hyT).1]; exact this.2.2⟩
    · rw [Function.update_of_ne hee] at hy
      have := w3 e' he' y hy
      have hyT := (w1 e' he').2.2.mem y hy
      have hyE : y ∉ EQ e := fun hm => hee (this.2.1.symm.trans (w3 e he y hm).2.1)
      refine ⟨fun hX' => ?_, by rw [(hsb y hyT).2]; exact this.2.1, by rw [(hsb y hyT).1]; exact this.2.2⟩
      rcases hXn y hX' with hX | hX
      · exact this.1 hX
      · exact hyE hX
  · rw [(hsb y hy).1] at hb
    have hyX0 : y ∉ X := fun hX => hyX (hXX y hX)
    obtain ⟨hbE, hmem⟩ := w4 y hy hyX0 hb
    rw [(hsb y hy).2]
    refine ⟨hbE, ?_⟩
    by_cases hee : L.mem s (blockA y) = e
    · rw [hee, Function.update_self]
      rw [hee] at hmem
      by_contra hn; exact hyX (hrest y hmem hn)
    · rw [Function.update_of_ne hee]; exact hmem

/-! ## `set_priority` -/

@[step] theorem obj.Tcb.block_obj.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.block_obj st t s ⦃ v => v = L.mem s (blockA t) ⦄ := by
  unfold obj.Tcb.block_obj; step*; simp_all [blockA]

theorem prio_wr_eps {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t prio : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    L.mem (L.wr s (prioA t) prio) (blockA t) = L.mem s (blockA t) ∧
      L.mem (L.wr s (prioA t) prio) (stA t) = L.mem s (stA t) := by
  have hta := h.tcbs t ht
  have ha : Aligned (prioA t) := field_aligned hta (by simp) (by simp)
  refine ⟨?_, ?_⟩
  · exact L.mem_wr_ne ha (field_aligned hta (by simp) (by simp))
      (fun e => field_ne hta hta (by simp) (by simp) (fun _ => by simp) (UScalar.eq_of_val_eq e))
  · rw [stA_eq]
    exact L.mem_wr_ne ha (field_aligned hta (by simp) (by simp))
      (fun e => field_ne hta hta (by simp) (by simp) (fun _ => by simp) (UScalar.eq_of_val_eq e))

/-- After `dequeue`, the thread is in no ready queue. -/
theorem notQ_after_dequeue {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
      then Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
        ((Q (L.mem s (affA t)) (L.mem s (prioA t))).erase t)) else Q) c p := by
  intro c hc p hp hm
  split at hm
  · rcases mem_upd2.1 hm with ⟨rfl, rfl, hm'⟩ | ⟨hne, hm'⟩
    · exact ((h.ready _ hc).1.rel _ hp).nodup.not_mem_erase hm'
    · exact hne ⟨(h.inQ c hc p hp t hm').1.symm, (h.inQ c hc p hp t hm').2.symm⟩
  · exact h.notQ ht (not_not.1 ‹_›) hc hp hm

/-- Dequeue, set the priority, enqueue, reschedule: the running-thread path
of seL4 `setPriority`. -/
theorem dpe_path {Cs X : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hnr : ∀ c ∈ Cs, t ∉ R c) (hrun : Runnable (L.mem s (stA t))) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 prio
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => ∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (h.queued t ht).1)) ?_
  rintro s1 ⟨h1, hw1, -⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨hsb1, -, -⟩ := ext_qfoot h.tcbs hW1 (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  step as ⟨s2, s2_post⟩
  subst s2_post
  have h2 := inv_wr_prio h1 ht hq1 hv
  have hr2 : (L.mem (L.wr s1 (prioA t) prio) (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact hnr _ (h2.aff t ht) ((h2.released t ht).1 hcn)
  have hrun2 : Runnable (L.mem (L.wr s1 (prioA t) prio) (stA t)) := by
    rw [(prio_wr_eps (prio := prio) h1 ht).2, (hsb1 t ht).1]
    exact hrun
  refine WP.spec_bind (sched.enqueue.inv _ t _ R h2 ht (fun _ => hr2) (fun _ => hrun2)) ?_
  intro s3 h3
  exact WP.spec_mono (sched.reschedule_required.inv s3 _ R h3) fun s' h' => h'.1

/-- `reorder_ep` after setting the priority of a blocked thread. -/
theorem blocked_path_ep {Cs X : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t))) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      endpoint.reorder_ep st s1 i t) ⦃ s' => ∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R ⦄ := by
  have hT := h.tcbs
  step as ⟨s1, s1_post⟩
  subst s1_post
  have h1 := inv_wr_prio h ht hq0 hv
  obtain ⟨hbl, hstt⟩ := prio_wr_eps (prio := prio) h ht
  obtain ⟨E, EQ, hEW⟩ := h1.eps
  have hEW' := hEW
  obtain ⟨w1, -, -, -, w4, -⟩ := hEW
  obtain ⟨heE, htm⟩ := w4 t ht htX (by rw [hstt]; exact hb)
  obtain ⟨hE, -, hq⟩ := w1 _ heE
  step as ⟨i, i_post⟩
  subst i_post
  refine WP.spec_mono (WP.spec_and (endpoint.reorder_ep.rel _ _ t _ hT hE hq htm)
    (endpoint.reorder_ep.foot _ _ t _ hT hE hq htm)) ?_
  rintro s' ⟨⟨hq', hst'⟩, hw⟩
  refine ⟨Q, inv_ep_step h1 hEW' heE hw hq' (fun _ => hst')
    (fun h0 => absurd h0 (List.ne_nil_of_mem (mem_insPrio.2 (Or.inl rfl)))) (fun y hy => ?_) (fun y hy hn => ?_) (fun y hy => hy)
    (fun y hy => Or.inl hy) (fun y hy => ?_)⟩
  · rcases mem_insPrio.1 hy with rfl | hy'
    · exact htm
    · exact List.mem_of_mem_erase hy'
  · exfalso; apply hn; rw [mem_insPrio]
    by_cases e : y = t
    · exact Or.inl e
    · exact Or.inr ((hq.nodup.mem_erase_iff).2 ⟨e, hy⟩)
  · rcases mem_insPrio.1 hy with rfl | hy'
    · exact htX
    · exact (hEW'.2.2.2.1 _ heE y (List.mem_of_mem_erase hy')).1

/-- `reorder_ntfn` after setting the priority of a blocked thread. -/
theorem blocked_path_ntfn {Cs X : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t))) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      notification.reorder_ntfn st s1 i t) ⦃ s' => ∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R ⦄ := by
  have hT := h.tcbs
  step as ⟨s1, s1_post⟩
  subst s1_post
  have h1 := inv_wr_prio h ht hq0 hv
  obtain ⟨hbl, hstt⟩ := prio_wr_eps (prio := prio) h ht
  obtain ⟨E, EQ, hEW⟩ := h1.eps
  have hEW' := hEW
  obtain ⟨w1, -, -, -, w4, -⟩ := hEW
  obtain ⟨heE, htm⟩ := w4 t ht htX (by rw [hstt]; exact hb)
  obtain ⟨hE, -, hq⟩ := w1 _ heE
  step as ⟨i, i_post⟩
  subst i_post
  refine WP.spec_mono (WP.spec_and (notification.reorder_ntfn.rel _ _ t _ hT hE hq htm)
    (notification.reorder_ntfn.foot _ _ t _ hT hE hq htm)) ?_
  rintro s' ⟨⟨hq', hst'⟩, hw⟩
  refine ⟨Q, inv_ep_step h1 hEW' heE hw hq' (fun _ => hst')
    (fun h0 => absurd h0 (List.ne_nil_of_mem (mem_insPrio.2 (Or.inl rfl)))) (fun y hy => ?_) (fun y hy hn => ?_) (fun y hy => hy)
    (fun y hy => Or.inl hy) (fun y hy => ?_)⟩
  · rcases mem_insPrio.1 hy with rfl | hy'
    · exact htm
    · exact List.mem_of_mem_erase hy'
  · exfalso; apply hn; rw [mem_insPrio]
    by_cases e : y = t
    · exact Or.inl e
    · exact Or.inr ((hq.nodup.mem_erase_iff).2 ⟨e, hy⟩)
  · rcases mem_insPrio.1 hy with rfl | hy'
    · exact htX
    · exact (hEW'.2.2.2.1 _ heE y (List.mem_of_mem_erase hy')).1

/-- The running-thread path of `set_priority`. -/
theorem running_path {Cs X : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
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
        else obj.Tcb.set_prio st t s prio) ⦃ s' => ∃ Q', SchedQueuesInvX st T Cs Ω H X s' Q' R ⦄ := by
  step as ⟨b, b_post⟩
  split
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    have htq := (h.queued t ht).1 hq1
    exact dpe_path s t prio Q R h ht hv (fun c hc => h.QR (h.aff t ht) (h.prio t ht) htq hc) hrun
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 :=
      not_not.1 fun hc => ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
    step as ⟨t1, t1_post⟩
    step as ⟨b1, b1_post⟩
    split
    · have e : t = t1 := by simpa [b1_post] using ‹b1 = true›
      have hr0 := hcur (e.trans t1_post)
      exact dpe_path s t prio Q R h ht hv (fun c hc => h.notR ht hr0 hc) hrun
    · step as ⟨s1, s1_post⟩
      subst s1_post
      exact ⟨Q, inv_wr_prio h ht hq0 hv⟩

theorem ts_vals : sched.TS_RUNNING = 1#u64 ∧ sched.TS_RESTART = 2#u64 ∧ sched.TS_BLOCKED_ON_RECV = 3#u64 ∧
    sched.TS_BLOCKED_ON_SEND = 4#u64 ∧ sched.TS_BLOCKED_ON_NTFN = 6#u64 := by
  unfold sched.TS_RUNNING sched.TS_RESTART sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND sched.TS_BLOCKED_ON_NTFN
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A thread that is not runnable is in no ready queue (from `runQ`). -/
theorem notQ_of_not_runnable {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hr : ¬ Runnable (L.mem s (stA t))) :
    (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
  by_contra hc
  exact hr (h.runQ _ (h.aff t ht) _ (h.prio t ht) t ((h.queued t ht).1 hc))

/-- seL4 `setPriority` (MCS) keeps the invariant (release queues
unchanged), for a current thread that is in no release queue. -/
theorem sched.set_priority.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.set_priority st s t prio ⦃ s' => ∃ Q', SchedQueuesInv st T Cs Ω H s' Q' R ⦄ := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  have hnR : ∀ v : U64, v = sched.TS_BLOCKED_ON_RECV ∨ v = sched.TS_BLOCKED_ON_SEND ∨ v = sched.TS_BLOCKED_ON_NTFN →
      ¬ Runnable v := by
    rintro v hv' (e | e | e) <;> rcases hv' with e' | e' | e' <;> rw [e'] at e <;> simp_all [sched.TS_RUNNING_VM]
  unfold sched.set_priority
  step as ⟨sv, sv_post⟩
  subst sv_post
  split
  · exact running_path s t prio Q R h ht hv (Or.inl ‹_›) hcur
  · split
    · exact running_path s t prio Q R h ht hv (Or.inr (Or.inl ‹_›)) hcur
    · split
      · exact running_path s t prio Q R h ht hv (Or.inr (Or.inr ‹_›)) hcur
      · have hnr : ¬ Runnable (L.mem s (stA t)) := by rintro (e | e | e) <;> contradiction
        have hq0 := notQ_of_not_runnable h ht hnr
        split
        · exact blocked_path_ep s t prio Q R h ht hv hq0 (by simp) (Or.inr (Or.inl ‹_›))
        · split
          · exact blocked_path_ep s t prio Q R h ht hv hq0 (by simp) (Or.inl ‹_›)
          · split
            · exact blocked_path_ntfn s t prio Q R h ht hv hq0 (by simp) (Or.inr (Or.inr ‹_›))
            · step as ⟨s1, s1_post⟩
              subst s1_post
              exact ⟨Q, inv_wr_prio h ht hq0 hv⟩

/-! ## `append` (`tcbSchedAppend`) -/

/-- The part of `append` after the bitmap update. -/
theorem append_tail (s1 : S) (t c p off : U64) (q : tcbqueue.Queue) (Q : U64 → List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hp : p.val < 256)
    (hR : ReadyRel st T s1 c Q) (hB : BitmapOK st s1 c (fun p' => p' = p ∨ Q p' ≠ []))
    (hN : NodePlaced st T s1 c) (hN' : NodePlaced st T s1 (L.cpu s1))
    (hnot : ∀ p' : U64, p'.val < 256 → t ∉ Q p')
    (hoff : off = rqOff p) (hoff8 : core.num.U64.wrapping_add off 8#u64 = rqTailOff p)
    (hq : q = L.rqQ s1 c p) :
    (do
      let (q1, s2) ← tcbqueue.append st s1 tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c off q1
      let s4 ← sched.set_flag st s3 t sched.Q_QUEUED true
      smp.remote_queue_update st s4 t) ⦃ s' =>
    ReadyQueues st T s' c (Function.update Q p (Q p ++ [t])) ⦄ := by
  have hta : TcbAddr t := hT t ht
  refine WP.spec_bind (tcbqueue.append.rel s1 .Sched q t (Q p) hT (hq ▸ hR.rel p hp) ht (hnot p hp)) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, hf2⟩ := h2
  have hW : ∀ w ∈ t :: Q p, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact (hR.rel p hp).mem w hw
  have hN2 : NodePlaced st T s2 c := hN.framed hf2
  have hcpu2 : L.cpu s2 = L.cpu s1 := hf2.2.1
  have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [hcpu2]; exact hN'.framed hf2
  have hv12 := views_framed hT hN hW hf2
  step as ⟨s3, s3_post⟩
  step as ⟨s4, s4_post⟩
  subst hoff; rw [hoff8] at s3_post
  obtain ⟨e3p, e3o, e3l1, e3l2, hl3, hN3⟩ := q_set_views q1 hT hN2 hp
  rw [← s3_post] at e3p e3o e3l1 e3l2 hl3 hN3
  have hN3' : NodePlaced st T s3 (L.cpu s3) := by
    rw [s3_post]; simp only [LawfulStore.cpu_wr]; exact hN2'.wr.wr
  refine WP.spec_mono (smp.remote_queue_update.spec s4 t) ?_
  intro s5 h5
  have hN4 : NodePlaced st T s4 c := by rw [s4_post]; exact hN3.wr
  have hN4' : NodePlaced st T s4 (L.cpu s4) := by rw [s4_post]; simp only [LawfulStore.cpu_wr]; exact hN3'.wr
  have hv34 : ViewsEq st s3 s4 c := by rw [s4_post]; exact views_wr_inq hN3 ht hta
  have hl34 : LinksEq st T s3 s4 := by rw [s4_post]; exact links_wr_inq hT hta
  obtain ⟨hv45, hl45, -⟩ := remote.views hT hN4 hN4' h5
  have hv35 := hv34.trans hv45
  have hl35 := hl34.trans hl45
  have hrq5 : L.rqQ s5 c p = q1 := by rw [hv35.1 p hp, e3p]
  refine ⟨?_, ?_⟩
  · refine hR.update hT hp ?_ ?_ ?_ ?_
    · intro p' hp' hne
      rw [hv35.1 p' hp', e3o p' hp' hne, hv12.1 p' hp']
    · intro p' hp' hne y hy
      have hyT : y ∈ T := (hR.rel p' hp').mem y hy
      have hyW : y ∉ t :: Q p := by
        intro hy'; rcases List.mem_cons.1 hy' with rfl | hy'
        · exact hnot p' hp' hy
        · exact hR.disj p p' hp hp' (Ne.symm hne) y hy' hy
      have hWa : ∀ w ∈ t :: Q p, TcbAddr w := fun w hw => hT w (hW w hw)
      have h12n := hf2.2.2.next_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      have h12p := hf2.2.2.prev_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      exact ⟨((hl35 y hyT .Sched).1.trans (hl3 y hyT .Sched).1).trans h12n,
        ((hl35 y hyT .Sched).2.trans (hl3 y hyT .Sched).2).trans h12p⟩
    · rw [hrq5]; exact (hr2.links hl3).links hl35
    · intro p' hp' hne x hx hx'
      rcases List.mem_append.1 hx with hx | hx
      · exact hR.disj p p' hp hp' (Ne.symm hne) x hx hx'
      · simp only [List.mem_singleton] at hx; subst hx; exact hnot p' hp' hx'
  · have hB5 : BitmapOK st s5 c (fun p' => p' = p ∨ Q p' ≠ []) := by
      refine hB.agree ?_ ?_
      · rw [hv35.2.1, e3l1, hv12.2.1]
      · intro g hg; rw [hv35.2.2 g hg, e3l2 g hg, hv12.2.2 g hg]
    refine hB5.congr fun p' _ => ?_
    by_cases e : p' = p
    · subst e; simp
    · simp [e]

/-- seL4 `tcbSchedAppend`: like `enqueue`, at the end of the queue. -/
theorem sched.append.ready (s : S) (t : obj.Tcb) (Q : U64 → List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : ReadyQueues st T s (L.mem s (affA t)) Q)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → ∀ p : U64, p.val < 256 → t ∉ Q p) :
    sched.append st s t ⦃ s' => ReadyQueues st T s' (L.mem s (affA t))
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem s (prioA t)) (Q (L.mem s (prioA t)) ++ [t])) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.append
  step*
  have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
  simp only [hq0, ne_eq, not_true_eq_false, if_false]
  subst cpu_post prio_post off_post
  have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by
    rw [q_post, off_post1]; rfl
  by_cases hb1 : b1 = true
  · rw [ite_cond_eq_true _ _ (eq_true hb1)]
    refine WP.spec_bind (sched.add_to_bitmap.spec s _ dom _ hp) ?_
    rintro s1 ⟨v1, v2, rfl, hv1, hv2⟩
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t)) := hN.wr
    have hA2 : L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64)) =
        L.nodeAt (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t))
          (l2Off ((L.mem s (prioA t)).val / 64)) := by simp
    have hrq : ∀ p' : U64, p'.val < 256 → L.rqQ (L.wr (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1)
        (L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))) v2) (L.mem s (affA t)) p' =
        L.rqQ s (L.mem s (affA t)) p' := by
      intro p' hp'
      rw [hA2, rqQ_wr_node hN1 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) hp',
        rqQ_wr_node hN (by rw [l1Off_val]; omega) (by rw [l1Off_val]) hp', l2Off_val hg, l1Off_val,
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hlk := (links_wr_node (v := v1) hT hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])).trans
      (links_wr_node (v := v2) hT hN1 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega))
    rw [← hA2] at hlk
    have hv2' : ∀ i, v2.bv.getLsbD i = ((L.l2W s (L.mem s (affA t)) ((L.mem s (prioA t)).val / 64)).bv.getLsbD i ||
        decide (i = (L.mem s (prioA t)).val % 64)) := by
      intro i; rw [hv2]
      unfold LawfulStore.l2W
      rw [rd_node_wr_node hN (by rw [l1Off_val]; omega) (by rw [l2Off_val hg]; omega) (by rw [l1Off_val])
        (by rw [l2Off_val hg]; omega), if_neg (by rw [l1Off_val, l2Off_val hg]; omega)]
    have hempty : Q (L.mem s (prioA t)) = [] :=
      ((h.1.rel _ hp).empty_iff hT).1 (by rw [← hqq]; simpa [b1_post] using hb1)
    apply append_tail _ t _ _ _ q Q hT ht hp
    · exact h.1.agree hrq fun p' hp' y hy => hlk y ((h.1.rel p' hp').mem y hy) _
    · exact BitmapOK.add hN hp h.2 hv1 hv2'
    · exact hN1.wr
    · simp only [LawfulStore.cpu_wr]; exact hN'.wr.wr
    · exact hq hq0
    · rfl
    · exact off_post1
    · rw [hrq _ hp, hqq]
  · rw [ite_cond_eq_false _ _ (eq_false hb1)]
    simp only [bind_ok]
    have hne : Q (L.mem s (prioA t)) ≠ [] := by
      rw [Ne, ← (h.1.rel _ hp).empty_iff hT, ← hqq]; simpa [b1_post] using hb1
    apply append_tail _ t _ _ _ q Q hT ht hp h.1 _ hN hN' (hq hq0) rfl off_post1 hqq
    refine h.2.congr fun p' _ => ?_
    by_cases e : p' = L.mem s (prioA t)
    · subst e; simp [hne]
    · simp [e]


attribute [local step] smp.remote_queue_update.spec

theorem append_foot_tail (s s1 : S) (t c p off : U64) (q : tcbqueue.Queue) (xs : List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hp : p.val < 256) (hN : NodePlaced st T s c)
    (hN' : NodePlaced st T s (L.cpu s)) (h1 : WritesIn st s s1 (L.NodeOf s c (128 ≤ ·)))
    (hr : QueueRel (L.mem s1) T .Sched q xs) (hn : t ∉ xs)
    (hoff : off = rqOff p) (hoff8 : core.num.U64.wrapping_add off 8#u64 = rqTailOff p) :
    (do
      let (q1, s2) ← tcbqueue.append st s1 tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c off q1
      let s4 ← sched.set_flag st s3 t sched.Q_QUEUED true
      smp.remote_queue_update st s4 t) ⦃ s' =>
    WritesIn st s s' (L.QFoot s (t :: xs) c (128 ≤ ·) t) ∧
      L.mem s' (inqA t) = L.mem s (inqA t) ||| sched.Q_QUEUED ⦄ := by
  have hta : TcbAddr t := hT t ht
  have hW : ∀ w ∈ t :: xs, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hr.mem w hw
  refine WP.spec_bind (tcbqueue.append.rel s1 .Sched q t xs hT hr ht hn) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w12 := hf2.writesIn
  have w02 := h1.trans w12
  step as ⟨s3, s3_post⟩
  have w23 : WritesIn st s2 s3 (L.NodeOf s c (128 ≤ ·)) := by
    subst hoff
    rw [s3_post, nodeAt_of_ksb w02.1, nodeAt_of_ksb w02.1, hoff8]
    exact ((writesIn_node (P := (128 ≤ ·)) hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
      (by rw [rqOff_val hp]; omega)).trans (writesIn_node (P := (128 ≤ ·)) hN (by rw [rqTailOff_val hp]; omega)
      (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega))).mono fun b hb => by
        rcases hb with hb | hb <;> exact hb
  have w03 := w02.trans w23
  step as ⟨s4, s4_post⟩
  simp only [ite_true] at s4_post
  have w34 : WritesIn st s3 s4 (· = inqA t) := by rw [s4_post]; exact writesIn_inq hta
  have w04 := w03.trans w34
  refine WP.spec_mono (smp.remote_queue_update.spec s4 t) ?_
  intro s5 h5
  have w45 := remote_writesIn hN' w04.1 w04.2.1 h5
  refine ⟨(w04.trans w45).mono fun b hb => ?_, ?_⟩
  · simp only [LawfulStore.QFoot]; tauto
  · have ni := inq_not_link_node (W := t :: xs) (Q := (· = 120)) hT hW hN' ht
    have ni' := inq_not_link_node (W := t :: xs) (Q := (128 ≤ ·)) hT hW hN ht
    rw [w45.mem_eq (inqA_aligned hta) ni.2, s4_post, L.mem_wr_same (inqA_aligned hta),
      w03.mem_eq (inqA_aligned hta) (by rintro (((h | h) | h)) <;> [exact ni'.2 h; exact ni'.1 h; exact ni'.2 h])]

/-- The footprint of `append`, as for `enqueue`. -/
theorem sched.append.foot (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (hr : QueueRel (L.mem s) T .Sched (L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t))) xs)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ xs) :
    sched.append st s t ⦃ s' => WritesIn st s s' (L.QFoot s (t :: xs) (L.mem s (affA t)) (128 ≤ ·) t) ∧
      L.mem s' (inqA t) = if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then L.mem s (inqA t)
        else L.mem s (inqA t) ||| sched.Q_QUEUED ⦄ := by
  unfold sched.append
  step*
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    simp only [ne_eq, hq1, not_false_eq_true, if_true]
    exact ⟨WritesIn.refl _ _, by trivial⟩
  have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
  simp only [hq0, ne_eq, not_true_eq_false, if_false]
  subst cpu_post prio_post off_post
  have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by
    rw [q_post, off_post1]; rfl
  by_cases hb1 : b1 = true
  · rw [ite_cond_eq_true _ _ (eq_true hb1)]
    refine WP.spec_bind (sched.add_to_bitmap.spec s _ dom _ hp) ?_
    rintro s1 ⟨v1, v2, rfl, -, -⟩
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have w1 : WritesIn st s (L.wr (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1)
        (L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))) v2)
        (L.NodeOf s (L.mem s (affA t)) (128 ≤ ·)) :=
      ((writesIn_node (P := (128 ≤ ·)) hN (by simp [l1Off_val]) (by simp [l1Off_val]) (by simp [l1Off_val])).trans
        (writesIn_node (P := (128 ≤ ·)) hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
          (by rw [l2Off_val hg]; omega))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t)) := hN.wr
    have hr1 := (hr.wr_node (v := v1) hT hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])).wr_node (v := v2)
      hT hN1 (off := l2Off ((L.mem s (prioA t)).val / 64)) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    rw [show L.nodeAt (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t))
      (l2Off ((L.mem s (prioA t)).val / 64)) = L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))
      by simp] at hr1
    exact append_foot_tail s _ t _ _ _ q xs hT ht hp hN hN' w1 (hqq ▸ hr1) (hq hq0) rfl off_post1
  · rw [ite_cond_eq_false _ _ (eq_false hb1)]
    simp only [bind_ok]
    exact append_foot_tail s s t _ _ _ q xs hT ht hp hN hN' (WritesIn.refl _ _) (hqq ▸ hr) (hq hq0) rfl off_post1


/-- `tcbSchedAppend` preserves the invariant, as `enqueue` does. -/
theorem sched.append.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem s (stA t))) :
    sched.append st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s'
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
         (Q (L.mem s (affA t)) (L.mem s (prioA t)) ++ [t]))) R ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have h1 := sched.append.ready s t _ hT ht hp hN hN' hR1 (fun h0 p hp => h.notQ ht h0 hc hp)
  have h2 := sched.append.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) (fun h0 => h.notQ ht h0 hc hp)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · rw [if_pos hqd] at hRc hinq ⊢
    have htq := (h.queued t ht).1 hqd
    have := inv_ready_step (W := t :: Q _ _) (xs' := Q (L.mem s (affA t)) (L.mem s (prioA t))) (tIn := True)
      h ht rfl rfl (fun w hw => List.mem_cons.1 hw)
      (fun _ c' hc' hm => h.QR hc hp htq hc' hm) hw (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq]) (by rw [hinq]; simpa using hqd) (by rw [hinq])
      (fun _ => h.QR hc hp htq hc) (fun _ => h.runQ _ hc _ hp t htq)
    simpa [Function.update_eq_self] using this
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    rw [if_neg hqd] at hRc hinq ⊢
    have htq := h.notQ ht hq0 hc hp
    exact inv_ready_step (W := t :: Q _ _) (tIn := True) h ht rfl rfl (fun w hw => List.mem_cons.1 hw)
      (fun _ c' hc' => h.notR ht (hr hq0) hc') hw hRc
      (fun y => by by_cases e : y = t <;> simp [e])
      (by rw [hinq, or_qq_qq]; simpa using qq_ne) (by rw [hinq, or_qq_qr])
      (fun _ => h.notR ht (hr hq0) hc) (fun _ => hrun hq0)


/-! ## `postpone` -/

def scTcbA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.TCB
def scCoreA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.CORE

@[step] theorem obj.Sc.tcb.spec (s : S) (sc : obj.Sc) : obj.Sc.tcb st sc s ⦃ v => v = L.mem s (scTcbA sc) ⦄ := by
  unfold obj.Sc.tcb; step*; simp_all [scTcbA]
@[step] theorem obj.Sc.cpu.spec (s : S) (sc : obj.Sc) : obj.Sc.cpu st sc s ⦃ v => v = L.mem s (scCoreA sc) ⦄ := by
  unfold obj.Sc.cpu; step*; simp_all [scCoreA]


/-- seL4 `postpone`: the SC's thread moves from its ready queue to its
core's release queue, and the SC's core is told to reprogram its timer. The
thread must not be in a release queue already, and the SC's `CORE` word must
name a core and lie outside the TCBs and nodes. -/
theorem sched.postpone.inv {Cs : Set U64} (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs)
    (hrun : Runnable (L.mem s (stA (L.mem s (scTcbA sc))))) (hna : L.actionW s ≠ L.mem s (scTcbA sc)) :
    sched.postpone st s sc ⦃ s' => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ⦄ := by
  unfold sched.postpone
  step as ⟨t, t_post⟩
  subst t_post
  set t := L.mem s (scTcbA sc) with ht_def
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have hmemq := (h.queued t ht).1
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq)) ?_
  rintro s1 ⟨h1, hw1, -⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  obtain ⟨hsb1, -, -⟩ := ext_qfoot hT hW1 hN hN' ht hc h.cur hw1
  have hact1 : L.actionW s1 = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw1.2.1]
    exact node_qfoot hT hW1 hN hN' ht hw1 hN' (by rw [act_val]; omega) (by rw [act_val])
      (fun _ => by rw [act_val]; omega) (fun _ => by rw [act_val]; omega)
  refine WP.spec_bind (WP.spec_and (sched.release_enqueue.inv s1 t _ R h1 ht hq1 hr1
      (by rw [(hsb1 t ht).1]; exact hrun) (by rw [hact1]; exact hna))
    (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1' (h1.release _ hc1))) ?_
  rintro s2 ⟨h2, hw2, -⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  step as ⟨s3, s3_post⟩
  subst s3_post
  have hN2 := h2.nodes _ hcs
  have hN2' := h2.nodes _ h2.cur
  have e : L.actionW (L.wr s2 (L.nodeAt s2 (L.mem s (scCoreA sc)) layout.node.REPROGRAM) 1#u64) = L.actionW s2 := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    by_cases hcc : L.mem s (scCoreA sc) = L.cpu s2
    · rw [hcc, rd_node_wr_node hN2' (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]), if_neg (by rw [repr_val, act_val]; omega)]
    · exact rd_node_wr_node_cpu hN2' hN2 (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]) hcc
  have o0 := nodeword_other (v := 1#u64) h2 hcs h2.cur (o := layout.node.REPROGRAM) (o' := layout.node.CUR_THREAD)
    (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [curth0]; omega) (by rw [curth0])
    (fun _ => by rw [repr_val, curth0]; omega)
  have o8 := nodeword_other (v := 1#u64) h2 hcs h2.cur (o := layout.node.REPROGRAM) (o' := layout.node.IDLE_THREAD)
    (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [idle8]; omega) (by rw [idle8])
    (fun _ => by rw [repr_val, idle8]; omega)
  exact ⟨_, _, inv_wr_node_low h2 hcs (by rw [repr_val]; omega) (by rw [repr_val]; omega) (by rw [repr_val])
    (by rw [e]; exact h2.action) (by rw [e]; exact h2.actOK) (by rw [o0]; exact h2.curT) (by rw [o8]; exact h2.idleT)⟩

/-! ## `set_thread_state` -/

/-- A write to a TCB field the queues do not read keeps the invariant. -/
theorem inv_wr_field {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t K v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3592 ∧ K.val ≠ 3520 ∧
      K.val ≠ 3448 ∧ K.val ≠ 3328 ∧ K.val ≠ 3336) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (core.num.U64.wrapping_add t K) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK hK8
  have fld : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → K.val ≠ K'.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (field_aligned (hT y hy) h1 h2)
      (fun e => field_ne hta (hT y hy) hK h1 (fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := hKn
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (core.num.U64.wrapping_add t K) v) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta hK (UScalar.eq_of_val_eq e).symm)
  have hsb : ∀ y ∈ T, L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA y) = L.mem s (stA y) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (blockA y) = L.mem s (blockA y) := fun y hy =>
    ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simpa using k8),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simpa using k9)⟩
  refine inv_of_agree h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 _ => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simpa using k5))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simpa using k6))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (fun _ => by simpa using k7))) (by rw [e]; exact h.action)
    hsb (by rw [e]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT)
    (h.eps.agree (L.ksb_wr _ _ _) hsb
      (fun y hy => ⟨by rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simpa [nextOff] using k3),
        by rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simpa [prevOff] using k4)⟩)
      (fun a hao => L.mem_wr_ne ha hao.1 (out_ne_field hao ht hta hK)))
    (curidle_wr_field h ht hK hK8).1 (curidle_wr_field h ht hK hK8).2
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simpa [nextOff] using k1)
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simpa [prevOff] using k2)
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta hK (UScalar.eq_of_val_eq e).symm)

/-- A write to a field of a thread in the exception set (e.g. its block
object) keeps the invariant. -/
theorem inv_wr_fieldX {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t K v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (htX : t ∈ X) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3592 ∧ K.val ≠ 3520 ∧
      K.val ≠ 3448 ∧ K.val ≠ 3328) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (core.num.U64.wrapping_add t K) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK hK8
  have fld : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → K.val ≠ K'.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (field_aligned (hT y hy) h1 h2)
      (fun e => field_ne hta (hT y hy) hK h1 (fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hKn
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (core.num.U64.wrapping_add t K) v) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta hK (UScalar.eq_of_val_eq e).symm)
  have hst : ∀ y ∈ T, L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simpa using k8)
  have hsb : ∀ y ∈ T, y ∉ X → L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA y) = L.mem s (stA y) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (blockA y) = L.mem s (blockA y) := fun y hy hyX =>
    ⟨hst y hy, by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (fun e => absurd (e ▸ htX) hyX)⟩
  refine inv_of_agree' h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 _ => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simpa using k5))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simpa using k6))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (fun _ => by simpa using k7))) (by rw [e]; exact h.action)
    (fun c hc p hp y hy => by rw [hst y (h.memT hc hp hy)]; exact h.runQ c hc p hp y hy)
    (fun c hc y hy => by rw [hst y (h.memTR hc hy)]; exact h.runR c hc y hy)
    (by rw [e]; intro haT; rw [hst _ haT]; exact h.actOK haT)
    (h.eps.agreeX (L.ksb_wr _ _ _) hsb
      (fun y hy => ⟨by rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simpa [nextOff] using k3),
        by rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simpa [prevOff] using k4)⟩)
      (fun a hao => L.mem_wr_ne ha hao.1 (out_ne_field hao ht hta hK)))
    (curidle_wr_field h ht hK hK8).1 (curidle_wr_field h ht hK hK8).2
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simpa [nextOff] using k1)
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simpa [prevOff] using k2)
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta hK (UScalar.eq_of_val_eq e).symm)

/-- Setting the state of `t` to a non-blocked state `v`, if `t` is in no
endpoint queue, and `v` is runnable if `t` is queued, released or the
switch-to candidate. `t` leaves the exception set. -/
theorem inv_set_state {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : ¬ Blocked v)
    (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hq : (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v)) :
    SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} (L.wr s (stA t) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  rw [stA_eq]
  have ha : Aligned (core.num.U64.wrapping_add t 3328#u64) := field_aligned hta (by simp) (by simp)
  have fld : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → (3328#u64).val ≠ K'.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (field_aligned (hT y hy) h1 h2)
      (fun e => field_ne hta (hT y hy) (by simp) h1 (fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  have hst : ∀ y ∈ T, y ≠ t → L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (stA y) = L.mem s (stA y) :=
    fun y hy hne => by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (fun e => absurd e hne)
  have hstt : L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (stA t) = v := by
    rw [stA_eq]; exact L.mem_wr_same ha
  have hbl : ∀ y ∈ T, L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (blockA y) = L.mem s (blockA y) :=
    fun y hy => by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp)
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have run' : ∀ y ∈ T, (y = t → Runnable v) → Runnable (L.mem s (stA y)) →
      Runnable (L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (stA y)) := by
    intro y hy h1 h2
    by_cases hyt : y = t
    · subst hyt; rw [hstt]; exact h1 rfl
    · rw [hst y hy hyt]; exact h2
  -- `t` is in no endpoint queue.
  obtain ⟨E, EQ, w1, w2, w5, w3, w4, w6⟩ := h.eps
  have htm : ∀ e ∈ E, t ∉ EQ e := by
    intro e he hm
    have := w3 e he t hm
    rcases hx with hX | hb
    · exact this.1 hX
    · exact hb this.2.2
  refine inv_of_agree' h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 _ => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (fun _ => by simp))) (by rw [e]; exact h.action)
    (fun c hc p hp y hy => run' y (h.memT hc hp hy) (fun hyt => hq.1 c hc p hp (hyt ▸ hy)) (h.runQ c hc p hp y hy))
    (fun c hc y hy => run' y (h.memTR hc hy) (fun hyt => hq.2.1 c hc (hyt ▸ hy)) (h.runR c hc y hy))
    (by rw [e]; intro haT
        exact ⟨run' _ haT (fun hyt => hq.2.2 hyt) (h.actOK haT).1, (h.actOK haT).2⟩) ?_
    (curidle_wr_field (K := 3328#u64) h ht (by simp) (by simp)).1
    (curidle_wr_field (K := 3328#u64) h ht (by simp) (by simp)).2
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have hnb : ∀ c, L.nodeBase (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) c = L.nodeBase s c :=
    fun c => by simp [LawfulStore.nodeBase]
  refine ⟨E, EQ, fun e' he' => ?_, w2, w5, fun e' he' y hy => ?_, fun y hy hyX hb => ?_,
    w6.agree (fun y hy => ?_) (fun y hy hyX hb => ?_) (fun _ _ _ hy => hy) (fun e' he' y hy => ?_)
      (fun e' he' _ => ?_) (fun e' he' h0 => Or.inl ⟨h0, ?_⟩)⟩
  rotate_left 3
  · by_cases hyt : y = t
    · subst hyt; right; rw [hstt]; exact hv
    · left; exact fun hX => hy ⟨hX, hyt⟩
  · by_cases hyt : y = t
    · subst hyt; rw [hstt] at hb; exact absurd hb hv
    · exact ⟨hst y hy hyt, hbl y hy⟩
  · exact hst y ((w1 e' he').2.2.mem y hy) (fun e2 => htm e' he' (e2 ▸ hy))
  · obtain ⟨hE, hEN, -⟩ := w1 e' he'
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState]
    rw [L.mem_wr_ne ha o2.1 (out_ne_field o2 ht hta (by simp))]
  · obtain ⟨hE, hEN, -⟩ := w1 e' he'
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState]
    rw [L.mem_wr_ne ha o2.1 (out_ne_field o2 ht hta (by simp))]
  · obtain ⟨hE, hEN, hq2⟩ := w1 e' he'
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    have eq : L.epQ (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) e' = L.epQ s e' := by
      simp only [LawfulStore.epQ]
      rw [L.mem_wr_ne ha o1.1 (out_ne_field o1 ht hta (by simp)), L.mem_wr_ne ha o2.1 (out_ne_field o2 ht hta (by simp))]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by simpa using hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq2.nodup, hq2.mem, hq2.head, hq2.last, hq2.seg.congr fun y hy =>
      ⟨by rw [prevA_eq']; exact fld y (hq2.mem y hy) _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff]),
       by rw [nextA_eq']; exact fld y (hq2.mem y hy) _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])⟩⟩
  · have := w3 e' he' y hy
    have hyT := (w1 e' he').2.2.mem y hy
    have hyt : y ≠ t := fun e2 => htm e' he' (e2 ▸ hy)
    exact ⟨fun hX => this.1 hX.1, by rw [hbl y hyT]; exact this.2.1, by rw [hst y hyT hyt]; exact this.2.2⟩
  · by_cases hyt : y = t
    · subst hyt; rw [hstt] at hb; exact absurd hb hv
    · rw [hst y hy hyt] at hb
      have hyX0 : y ∉ X := fun hX => hyX ⟨hX, hyt⟩
      rw [hbl y hy]; exact w4 y hy hyX0 hb

/-- `set_state` to any state (e.g. a blocked one) for a thread in no queue:
the thread joins the exception set. -/
theorem inv_set_state_blk {Cs X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hq : (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v)) :
    SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∨ y = t} (L.wr s (stA t) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  rw [stA_eq]
  have ha : Aligned (core.num.U64.wrapping_add t 3328#u64) := field_aligned hta (by simp) (by simp)
  have fld : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → (3328#u64).val ≠ K'.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (field_aligned (hT y hy) h1 h2)
      (fun e => field_ne hta (hT y hy) (by simp) h1 (fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  have hst : ∀ y ∈ T, y ≠ t → L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (stA y) = L.mem s (stA y) :=
    fun y hy hne => by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (fun e => absurd e hne)
  have hstt : L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (stA t) = v := by
    rw [stA_eq]; exact L.mem_wr_same ha
  have hbl : ∀ y ∈ T, L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (blockA y) = L.mem s (blockA y) :=
    fun y hy => by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (fun _ => by simp)
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) = L.actionW s := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have run' : ∀ y ∈ T, (y = t → Runnable v) → Runnable (L.mem s (stA y)) →
      Runnable (L.mem (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) (stA y)) := by
    intro y hy h1 h2
    by_cases hyt : y = t
    · subst hyt; rw [hstt]; exact h1 rfl
    · rw [hst y hy hyt]; exact h2
  -- `t` is in no endpoint queue.
  obtain ⟨E, EQ, w1, w2, w5, w3, w4, w6⟩ := h.eps
  have htm : ∀ e ∈ E, t ∉ EQ e := by
    intro e he hm
    have := w3 e he t hm
    rcases hx with hX | hb
    · exact this.1 hX
    · exact hb this.2.2
  refine inv_of_agree' h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 _ => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (fun _ => by simp))) (by rw [e]; exact h.action)
    (fun c hc p hp y hy => run' y (h.memT hc hp hy) (fun hyt => hq.1 c hc p hp (hyt ▸ hy)) (h.runQ c hc p hp y hy))
    (fun c hc y hy => run' y (h.memTR hc hy) (fun hyt => hq.2.1 c hc (hyt ▸ hy)) (h.runR c hc y hy))
    (by rw [e]; intro haT
        exact ⟨run' _ haT (fun hyt => hq.2.2 hyt) (h.actOK haT).1, (h.actOK haT).2⟩) ?_
    (curidle_wr_field (K := 3328#u64) h ht (by simp) (by simp)).1
    (curidle_wr_field (K := 3328#u64) h ht (by simp) (by simp)).2
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  have hnb : ∀ c, L.nodeBase (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) c = L.nodeBase s c :=
    fun c => by simp [LawfulStore.nodeBase]
  refine ⟨E, EQ, fun e' he' => ?_, w2, w5, fun e' he' y hy => ?_, fun y hy hyX hb => ?_,
    w6.agree (fun y hy => ?_) (fun y hy hyX hb => ?_) (fun _ _ _ hy => hy) (fun e' he' y hy => ?_)
      (fun e' he' _ => ?_) (fun e' he' h0 => Or.inl ⟨h0, ?_⟩)⟩
  rotate_left 3
  · exact Or.inl fun hX => hy (Or.inl hX)
  · exact ⟨hst y hy (fun e => hyX (Or.inr e)), hbl y hy⟩
  · exact hst y ((w1 e' he').2.2.mem y hy) (fun e2 => htm e' he' (e2 ▸ hy))
  · obtain ⟨hE, hEN, -⟩ := w1 e' he'
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState]
    rw [L.mem_wr_ne ha o2.1 (out_ne_field o2 ht hta (by simp))]
  · obtain ⟨hE, hEN, -⟩ := w1 e' he'
    obtain ⟨-, o2⟩ := ep_out hE hEN
    simp only [LawfulStore.epState]
    rw [L.mem_wr_ne ha o2.1 (out_ne_field o2 ht hta (by simp))]
  · obtain ⟨hE, hEN, hq2⟩ := w1 e' he'
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    have eq : L.epQ (L.wr s (core.num.U64.wrapping_add t 3328#u64) v) e' = L.epQ s e' := by
      simp only [LawfulStore.epQ]
      rw [L.mem_wr_ne ha o1.1 (out_ne_field o1 ht hta (by simp)), L.mem_wr_ne ha o2.1 (out_ne_field o2 ht hta (by simp))]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by simpa using hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq2.nodup, hq2.mem, hq2.head, hq2.last, hq2.seg.congr fun y hy =>
      ⟨by rw [prevA_eq']; exact fld y (hq2.mem y hy) _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff]),
       by rw [nextA_eq']; exact fld y (hq2.mem y hy) _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])⟩⟩
  · have := w3 e' he' y hy
    have hyT := (w1 e' he').2.2.mem y hy
    have hyt : y ≠ t := fun e2 => htm e' he' (e2 ▸ hy)
    refine ⟨fun hX => ?_, by rw [hbl y hyT]; exact this.2.1, by rw [hst y hyT hyt]; exact this.2.2⟩
    rcases hX with hX | hX
    · exact this.1 hX
    · exact hyt hX
  · have hyt : y ≠ t := fun e => hyX (Or.inr e)
    rw [hst y hy hyt] at hb
    have hyX0 : y ∉ X := fun hX => hyX (Or.inl hX)
    rw [hbl y hy]; exact w4 y hy hyX0 hb

@[step] theorem obj.Tcb.set_state.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_state st t s v ⦃ s' => s' = L.wr s (stA t) v ⦄ := by
  unfold obj.Tcb.set_state; step*; simp_all [stA]


/-- seL4 `setThreadState` (with `scheduleTCB`): setting a non-blocked state
on a thread in no endpoint queue keeps the invariant, if the new state is
runnable whenever the thread is queued, released or the switch-to candidate.
The thread leaves the exception set. -/
theorem sched.set_thread_state.inv {Cs X : Set U64} (s : S) (t : obj.Tcb) (v : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : ¬ Blocked v)
    (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hq : (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v)) :
    sched.set_thread_state st s t v ⦃ s' => SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  step as ⟨s1, s1_post⟩
  subst s1_post
  have h1 := inv_set_state h ht hv hx hq
  step*
  all_goals first | exact h1 | skip
  subst_vars
  rw [choose_val]
  exact (inv_set_action h1 (Or.inr (Or.inl rfl)) (fun h1T => absurd h1T (notT_small h.tcbs (by simp)))).1

/-! ## `awaken`'s loop -/

/-- The loop of seL4 `awaken`: while the head of the current core's release
queue is ready, it leaves the release queue and `possible_switch_to` puts it
in a ready queue. The invariant holds throughout. -/
theorem sched.awaken_loop.inv {Cs : Set U64} (s : S) (fuel : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) :
    sched.awaken_loop st s fuel ⦃ s' => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => ∃ Q' R', SchedQueuesInv st T Cs Ω H x.1 Q' R')
  · rintro ⟨s1, fu⟩ ⟨Q1, R1, h1⟩
    unfold sched.awaken_loop.body
    step*
    all_goals try exact ⟨Q1, R1, h1⟩
    -- the head of the release queue
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    have hc1 := h1.aff i1 hT1
    have hmemr := (h1.released i1 hT1).1
    refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s1 i1 Q1 R1 h1 hT1)
      (sched.release_remove.foot s1 i1 _ h1.tcbs hT1 (h1.nodes _ hc1) (h1.nodes _ h1.cur) (h1.release _ hc1) hmemr)) ?_
    rintro s2 ⟨h2, hw2, -⟩
    have hW2 : ∀ w ∈ R1 (L.mem s1 (affA i1)), w ∈ T := fun w hw => h1.memTR hc1 hw
    obtain ⟨hsb2, -, -⟩ := ext_qfoot h1.tcbs hW2 (h1.nodes _ hc1) (h1.nodes _ h1.cur) hT1 hc1 h1.cur hw2
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [(hsb2 i1 hT1).1]; exact h1.runR _ h1.cur i1 hmem
    refine WP.spec_bind (sched.possible_switch_to.inv s2 i1 _ _ h2 hT1 hrun) ?_
    rintro s3 ⟨Q3, h3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨Q3, _, h3⟩, by omega⟩
  · exact ⟨Q, R, h⟩

/-! ## Writes to the other kernel objects -/

/-- Node offsets the invariant does not read: not `CUR_THREAD`,
`IDLE_THREAD`, `SCHED_ACTION`, the release queue or the bitmap and ready
queues. -/
def LowFree (o : Nat) : Prop := o < 128 ∧ o % 8 = 0 ∧ o ≠ 0 ∧ o ≠ 8 ∧ o ≠ 16 ∧ o ≠ 64 ∧ o ≠ 72

/-- Words the scheduler queues do not depend on: the other kernel objects
`Ω` and the free words of the nodes. -/
def LawfulStore.Free (s : S) (Ω Cs : Set U64) (b : U64) : Prop :=
  b ∈ Ω ∨ ∃ c ∈ Cs, ∃ o : U64, LowFree o.val ∧ b = L.nodeAt s c o

theorem LawfulStore.Free.ksb {s s' : S} {Cs : Set U64} {b : U64} (hk : L.ksb s' = L.ksb s)
    (h : L.Free s' Ω Cs b) : L.Free s Ω Cs b := by
  rcases h with h | ⟨c, hc, o, ho, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, o, ho, by rw [e, nodeAt_of_ksb hk]⟩

/-- A change confined to the free words keeps the invariant. -/
theorem inv_of_free {Cs X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (L.Free s Ω Cs)) :
    SchedQueuesInvX st T Cs Ω H X s' Q R := by
  have hT := h.tcbs
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (hm | ⟨c, hc, o, ho, e⟩)
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) hK rfl
    · exact node_ne_field (h.nodes c hc) (by simp only [LowFree] at ho; omega) hy (hT y hy) hK e.symm
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ LowFree o.val →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8 hro
    refine hw.mem_eq (nodeAt_aligned (h.nodes c hc) ho h8) ?_
    rintro (hm | ⟨c', hc', o', ho', e⟩)
    · exact out_ne_node (h.omega _ hm) hc (h.nodes c hc) ho rfl
    · by_cases hcc : c' = c
      · subst hcc
        simp only [LowFree] at ho' hro
        have := congrArg UScalar.val e
        rw [nodeAt_val (h.nodes c' hc) ho, nodeAt_val (h.nodes c' hc) (by omega : o'.val < 4288)] at this
        omega
      · simp only [LowFree] at ho'
        exact nodeAt_ne_cpu (h.nodes c hc) (h.nodes c' hc') ho (by omega : o'.val < 4288) (Ne.symm hcc) e
  have hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y) :=
    fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp)⟩
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    exact nod _ h.cur _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; simp [LowFree])
  refine inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩)
    (fun c hc o h1 h2 h3 => nod c hc o h1 h2 (by simp only [LowFree]; omega))
    (fun y hy => fld y hy _ (by simp) (by simp)) (fun y hy => fld y hy _ (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp))) (by rw [hact]; exact h.action) hsb
    (by rw [hact]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT) ?_
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [curth0]; omega) (by rw [curth0])
          (by rw [curth0]; simp [LowFree])]; exact h.curT)
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [idle8]; omega) (by rw [idle8])
          (by rw [idle8]; simp [LowFree])]; exact h.idleT)
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff])
  obtain ⟨E, EQ, w1, w2, w5, w3, w4, w6⟩ := h.eps
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hw.1]
  have ewg : ∀ e ∈ E, ∀ a, (a = epHeadA e ∨ a = epTSA e) → L.mem s' a = L.mem s a := by
    intro e he a ha
    obtain ⟨hE, hEN, hq⟩ := w1 e he
    obtain ⟨a1, a2⟩ := ep_aligned hE
    have hal : Aligned a := by rcases ha with rfl | rfl <;> assumption
    have hav : a.val = e.val ∨ a.val = e.val + 8 := by
      rcases ha with rfl | rfl
      · exact Or.inl epHeadA_val
      · exact Or.inr (epTSA_val hE)
    refine hw.mem_eq hal ?_
    rintro (hm | ⟨c, hc, o, ho, e2⟩)
    · have := w5 e he a hm; omega
    · have := congrArg UScalar.val e2
      rw [nodeAt_val (h.nodes c hc) (by simp only [LowFree] at ho; omega)] at this
      have := hEN.1 c hc; simp only [LowFree] at ho; omega
  refine ⟨E, EQ, fun e he => ?_, w2, w5, fun e he y hy => ?_, fun y hy hyX hb => ?_,
    w6.agree (fun y hy => Or.inl hy) (fun y hy _ _ => hsb y hy) (fun _ _ _ hy => hy)
      (fun e he y hy => (hsb y ((w1 e he).2.2.mem y hy)).1)
      (fun e he _ => by simp only [LawfulStore.epState, ewg e he _ (Or.inr rfl)])
      (fun e he h0 => Or.inl ⟨h0, by simp only [LawfulStore.epState, ewg e he _ (Or.inr rfl)]⟩)⟩
  · obtain ⟨hE, hEN, hq⟩ := w1 e he
    obtain ⟨a1, a2⟩ := ep_aligned hE
    have ew : ∀ a, (a = epHeadA e ∨ a = epTSA e) → L.mem s' a = L.mem s a := by
      intro a ha
      have hal : Aligned a := by rcases ha with rfl | rfl <;> assumption
      have hav : a.val = e.val ∨ a.val = e.val + 8 := by
        rcases ha with rfl | rfl
        · exact Or.inl epHeadA_val
        · exact Or.inr (epTSA_val hE)
      refine hw.mem_eq hal ?_
      rintro (hm | ⟨c, hc, o, ho, e2⟩)
      · have := w5 e he a hm; omega
      · have := congrArg UScalar.val e2
        rw [nodeAt_val (h.nodes c hc) (by simp only [LowFree] at ho; omega)] at this
        have := hEN.1 c hc; simp only [LowFree] at ho; omega
    have eq : L.epQ s' e = L.epQ s e := by
      simp only [LawfulStore.epQ, ew _ (Or.inl rfl), ew _ (Or.inr rfl)]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by rw [hw.1]; exact hEN.2⟩, ?_⟩
    rw [eq]
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
      ⟨by rw [prevA_eq']; exact fld y (hq.mem y hy) _ (by simp [prevOff]) (by simp [prevOff]),
       by rw [nextA_eq']; exact fld y (hq.mem y hy) _ (by simp [nextOff]) (by simp [nextOff])⟩⟩
  · have hyT := (w1 e he).2.2.mem y hy
    rw [(hsb y hyT).1, (hsb y hyT).2]; exact w3 e he y hy
  · rw [(hsb y hy).1] at hb
    rw [(hsb y hy).2]; exact w4 y hy hyX hb

end

end Fl4Proofs.P1
