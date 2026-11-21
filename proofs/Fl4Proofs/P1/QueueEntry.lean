/-
P1: native kernel entries (`handle_syscall` excluding VMEnter, and
`handle_interrupt_entry`) keep
`EntryInv` (established by `schedule`, `sched.schedule.entry`).

Inside an entry, before the final `schedule`, the current SC word is not
switched.  The budget check at the entry (`budget_ok`, `check_budget`) needs
the current SC active and the current thread's (`EntryInv`); after an
invocation the preemption point (`mcs_preemption_point.allG`) needs `HCur`:
the current SC is active, or the current thread has no other SC.  `HCur` is
preserved across an invocation (`HCur.step`) given the invocation's
`CurStep` (it keeps the current SC and thread words, and the current
thread's `SC` field is kept or cleared unless the current SC stays active;
an SC deletion takes the current SC out of the active set only with the
current thread unbound from it, `CurStep.del`).

`handle_yield` (`syscall.handle_yield.bxi`) and `handle_interrupt`
(`interrupt.handle_interrupt.bxi`) are proved here.  The other invocations
(`handle_invocation`, `handle_recv`, the fault and timeout handlers, the
debug syscalls, `activate_thread`) and the cap validity the interrupt path
needs are the named hypotheses `EntryHyps`, one per family, stated with the
invariants of P1 (`BXI`, with a possibly smaller active set), for the P3
decode theorems to discharge.
-/
import Fl4Proofs.P1.QueueRecv
import Fl4Proofs.P1.QueueFire
import Fl4Proofs.P1.QueueBudgetG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-! ## `hcur` -/

/-- Inside a kernel entry: the current SC is active, or the current thread
has no other SC than it (it may have lost its SC, e.g. when the SC was
deleted). -/
def HCur (st : machine.Store S) [L : LawfulStore st] (Ac : Set U64) (s : S) : Prop :=
  L.cscW s ∈ Ac ∨ L.mem s (scA (L.curW s)) = L.cscW s ∨ L.mem s (scA (L.curW s)) = 0#u64

/-- What an invocation does to the current SC and thread: the current SC and
current thread words are kept (only `schedule` switches them); if the
current SC leaves the active set (`Ac` to `Ac'`, an SC deletion), the
current thread's `SC` field is cleared or is that SC; otherwise the field is
kept or cleared, unless the current SC stays active. -/
structure CurStep (st : machine.Store S) [L : LawfulStore st] (Ac Ac' : Set U64) (s s' : S) : Prop where
  csc : L.cscW s' = L.cscW s
  cur : L.curW s' = L.curW s
  del : L.cscW s ∈ Ac → L.cscW s ∉ Ac' →
    L.mem s' (scA (L.curW s)) = 0#u64 ∨ L.mem s' (scA (L.curW s)) = L.cscW s
  sc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨ L.mem s' (scA (L.curW s)) = 0#u64 ∨
    L.cscW s ∈ Ac'

/-- **`hcur` is preserved across an invocation.** -/
theorem HCur.step {Ac Ac' : Set U64} {s s' : S} (h : HCur st Ac s) (k : CurStep st Ac Ac' s s') :
    HCur st Ac' s' := by
  unfold HCur
  rw [k.csc, k.cur]
  by_cases h1 : L.cscW s ∈ Ac'
  · exact Or.inl h1
  right
  by_cases h2 : L.cscW s ∈ Ac
  · rcases k.del h2 h1 with e | e
    · exact Or.inr e
    · exact Or.inl e
  · rcases h with h | h | h
    · exact absurd h h2
    · rcases k.sc with e | e | e
      · exact Or.inl (e.trans h)
      · exact Or.inr e
      · exact absurd e h1
    · rcases k.sc with e | e | e
      · exact Or.inr (e.trans h)
      · exact Or.inr e
      · exact absurd e h1

theorem HCur.of_mem {Ac : Set U64} {s : S} (h : L.cscW s ∈ Ac) : HCur st Ac s := Or.inl h

theorem CurStep.refl (Ac : Set U64) (s : S) : CurStep st Ac Ac s s :=
  ⟨rfl, rfl, fun h1 h2 => absurd h1 h2, Or.inl rfl⟩

/-- A step that keeps the active set, the current SC and thread words and the
current thread's `SC` field. -/
theorem CurStep.keep {Ac : Set U64} {s s' : S} (hcs : L.cscW s' = L.cscW s) (hcu : L.curW s' = L.curW s)
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s))) : CurStep st Ac Ac s s' :=
  ⟨hcs, hcu, fun h1 h2 => absurd h1 h2, Or.inl hsc⟩

/-- A step that keeps the active set and may clear the current thread's `SC`
field. -/
theorem CurStep.clear {Ac : Set U64} {s s' : S} (hcs : L.cscW s' = L.cscW s) (hcu : L.curW s' = L.curW s)
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨ L.mem s' (scA (L.curW s)) = 0#u64) :
    CurStep st Ac Ac s s' :=
  ⟨hcs, hcu, fun h1 h2 => absurd h1 h2, by rcases hsc with e | e; exacts [Or.inl e, Or.inr (Or.inl e)]⟩

/-- An SC deletion (`fin_sc.blk`: the active set loses `p`, the thread bound
to `p` is unbound), when the current thread's SC (if any) is the current SC. -/
theorem CurStep.ofDel {Ac : Set U64} {s s' : S} {p : U64} (hcs : L.cscW s' = L.cscW s)
    (hcu : L.curW s' = L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨
      (L.mem s (scA (L.curW s)) = p ∧ L.mem s' (scA (L.curW s)) = 0#u64)) :
    CurStep st Ac (Ac \ {p}) s s' := by
  refine ⟨hcs, hcu, fun h1 h2 => ?_, ?_⟩
  · rcases hsc with e | ⟨-, e⟩
    · rw [e]
      by_cases h0 : L.mem s (scA (L.curW s)) = 0#u64
      · exact Or.inl h0
      · exact Or.inr (hcsc h0).symm
    · exact Or.inl e
  · rcases hsc with e | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)

/-! ## Steps that keep the current SC -/

theorem EntryInv.bxi {Ac : Set U64} {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.sg, h.2.2.2.1⟩

/-- A write to a current-node word other than the scheduler's. -/
theorem nodew_bxc {Ac : Set U64} {s : S} {o v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ho : LowFree o.val) (h24 : o.val ≠ 24) (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) :
    BXC st T Cs Ω H Sg Rp Scs Nt Z Ac s (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      ANI st s (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      (∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (scA y) = L.mem s (scA y)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨h3, hB3, hX3, hSg3, ea, ec, ecs3, f3⟩ := node_bx (o := o) (v := v) h0 hB hX hSg ho h24 hto
  have hN := h0.nodes _ h0.cur
  obtain ⟨-, hc⟩ := objs_omega hX.1 hS.sub
  have ho' := ho
  unfold LowFree at ho'
  refine ⟨⟨⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, SCsOK.wr h0 hS hX (nodeAt_aligned hN (by omega) (by omega))
    (fun y hy => ?_) ?_ (fun c hc' => ?_)
    (fun c hc' => out_ne_node (h0.omega _ (spor_omega hX.1 hc')) h0.cur hN (by omega))
    (fun c hc' e => absurd e (out_ne_node (h0.omega _ (hS.sub _ (hX.1.repW c hc'))) h0.cur hN (by omega)))⟩, ecs3,
    CurK.of h0.tcbs h0.curT ec (f3 _ h0.curT).1 (Or.inl ea)⟩,
    ⟨ea, ?_, ec⟩, fun y hy => (f3 y hy).1⟩
  · rw [scA_eq]; exact fun e => node_ne_field hN (by omega) hy (h0.tcbs y hy) (by simp) (UScalar.eq_of_val_eq e)
  · intro e
    simp only [LawfulStore.nodeA] at e
    rw [nodeAt_val hN (by omega), nodeAt_val hN (by simp [layout.node.CUR_SC])] at e
    simp [layout.node.CUR_SC] at e; omega
  · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
    exact ⟨out_ne_node (h0.omega _ c3) h0.cur hN (by omega), out_ne_node (h0.omega _ c4) h0.cur hN (by omega),
      out_ne_node (h0.omega _ c5) h0.cur hN (by omega)⟩
  · unfold LawfulStore.idleW
    exact rd_cur_node h0 (by omega) (by omega) (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)

variable {A : Type _} {ar : machine.Arch A} {U : Set U64} {P3Ok : S → Prop}

/-- The words the entry prefix may write, from the entry state `e`. -/
def EntW (st : machine.Store S) [L : LawfulStore st] (e : S) (b : U64) : Prop :=
  (∃ K : U64, K.val = 256 + 8 * layout.reg.FAULT_IP.val ∧ b = core.num.U64.wrapping_add (L.curW e) K) ∨
    L.NodeOf e (L.cpu e) (fun _ => True) b

/-- `s` is reached from the entry state `e` by the entry prefix. -/
def Ent (st : machine.Store S) [L : LawfulStore st] (e s : S) : Prop := WritesIn st e s (EntW st e)

/-- `s` is reached by the entry prefix from an entry state satisfying `P3Ok`. -/
def EntAt (st : machine.Store S) [L : LawfulStore st] (P3Ok : S → Prop) (s : S) : Prop :=
  ∃ e, P3Ok e ∧ Ent st e s


/-- seL4 `updateTimestamp`: the current node's time and `CONSUMED` words. -/
theorem sched.update_timestamp.bxc (hA : P0.ArchTotal ar) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.update_timestamp st ar s a ⦃ s' _ => BXC st T Cs Ω H Sg Rp Scs Nt Z Ac s s' ∧ ANI st s s' ∧
      ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  obtain ⟨⟨k1, c1, kk1⟩, n1, f1⟩ := nodew_bxc (o := layout.node.CUR_TIME) (v := now) h
    (by simp [layout.node.CUR_TIME, LowFree]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [show ∀ s0 : S, L.nodeA s0 layout.node.CONSUMED = L.nodeAt s0 (L.cpu s0) layout.node.CONSUMED from
    fun _ => rfl] at e2
  subst e2
  obtain ⟨⟨k2, c2, kk2⟩, n2, f2⟩ := nodew_bxc (o := layout.node.CONSUMED) (v := total) k1
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
  exact ⟨⟨k2, c2.trans c1, kk1.trans kk2⟩, n1.trans n2, fun y hy => (f2 y hy).trans (f1 y hy)⟩

/-- `update_timestamp` at a kernel entry: the facts `check_budget` needs. -/
theorem sched.update_timestamp.entry (hA : P0.ArchTotal ar) {Ac : Set U64} (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.update_timestamp st ar s a ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.cscW s' = L.cscW s ∧
      L.cscW s' ∈ Ac ∧ L.actionW s' ≠ L.curW s' ∧
      (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s'))) ∧ CurK st s s' ⦄ := by
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hT := h.1.choose_spec.choose_spec.tcbs
  have hb := EntryInv.bxi h
  obtain ⟨-, -, -, -, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (sched.update_timestamp.bxc hA s a hb) ?_
  rintro ⟨s1, a1⟩ ⟨⟨k1, c1, -⟩, n1, f1⟩
  simp only [WP.uncurry'_pair] at *
  refine ⟨k1, c1, by rw [c1]; exact hcA, by rw [n1.1, n1.2.2]; exact hna, ?_,
    CurK.of hT hcT n1.2.2 (f1 _ hcT) (Or.inl n1.1)⟩
  rw [n1.2.2, f1 _ hcT, c1]; exact hcsc

/-- The IRQ handler slot of `irq` in the kernel-global IRQ node. -/
def irqSlotA (kb irq : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add kb 1248#u64) (core.num.U64.wrapping_mul irq 32#u64)

theorem irq_node_val : layout.ks.IRQ_NODE ⦃ v => v.val = 1248 ⦄ := by
  unfold layout.ks.IRQ_NODE layout.irq.COUNT layout.irq.MAX layout.ks.IRQ_STATE layout.ks.DOM_SCHEDULE
  step*

theorem interrupt.irq_slot.val (s : S) (irq : U64) :
    interrupt.irq_slot st s irq ⦃ sl => sl = irqSlotA (L.ksb s) irq ⦄ := by
  unfold interrupt.irq_slot
  step with LawfulStore.ks_base_spec as ⟨kb, ekb⟩
  refine WP.spec_bind irq_node_val fun nd hnd => ?_
  have e : nd = 1248#u64 := UScalar.eq_of_val_eq (by simp [hnd])
  subst e ekb
  simp only [lift, bind_ok, WP.spec_ok, irqSlotA, layout.cte.SIZE]

/-- **seL4 `handleInterrupt`**: a signal IRQ signals the notification of its
handler cap (`send_signal`), a timer IRQ marks the current core for
reprogramming, a reschedule IPI requests a reschedule.  The notification
caps of the IRQ slots naming heap notifications is the cap-validity
hypothesis `hirq` (P3's `CapValid`). -/
theorem interrupt.handle_interrupt.bxi (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {Ac : Set U64} (s : S) (a : A) (irq : U64)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hirq : ∀ i : U64, i.val < 128 → obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2,
      c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄) :
    interrupt.handle_interrupt st ar s a irq ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold interrupt.handle_interrupt
  step with layout.irq.MAX.spec as ⟨mx, emx⟩
  split
  · refine WP.spec_bind (hA.mask_irq a irq true) fun a1 _ => ?_
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 h
  step with P0.interrupt.irq_state.p0 st s irq hST as ⟨v⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · rename_i hle _
      step with interrupt.irq_slot.val as ⟨sl, esl⟩
      subst esl
      have hirq' : irq.val < 128 := by
        have : mx.val = 127 := by rw [emx]; simp [layout.irq.MAX]
        simp at hle; omega
      refine WP.spec_bind (hirq irq hirq') fun c hc => ?_
      refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h
        rename_i ptr badge b x
        split
        · have hn := hc ptr badge b x rfl
          exact WP.spec_mono (notification.send_signal.tinv hA s a ptr badge h.blk hn (hNt ptr hn))
            fun r hr => by obtain ⟨s', a'⟩ := r; exact BlkOK.bxi (by simpa using hr)
        · exact (WP.spec_ok _).2 h
      · rintro ⟨s3, a2⟩ h3
        try simp only [WP.uncurry'_pair]
        refine WP.spec_bind (hA.mask_irq a2 irq true) fun a3 _ => ?_
        exact (WP.spec_ok _).2 h3
    split
    · step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_set.spec as ⟨s2, e2⟩
      subst ec e2
      obtain ⟨⟨k2, -, -⟩, -, -⟩ := nodew_bxc (o := layout.node.REPROGRAM) (v := 1#u64) h
        (by simp [layout.node.REPROGRAM, LowFree]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      step with obj.node_set.spec as ⟨s3, e3⟩
      subst e3
      have k3 := nodew_bxc (o := layout.node.ARMED) (v := 0#u64) k2
        (by simp [layout.node.ARMED, LowFree]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
      have k3' := k3.1.1
      simp only [LawfulStore.cpu_wr, nodeAt_wr] at k3' ⊢
      exact k3'
    split
    · unfold smp.handle_ipi
      step with layout.irq.RESCHEDULE_IPI.spec as ⟨ri, eri⟩
      split
      · obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
        refine WP.spec_bind (sched.reschedule_required.sch s Q R h0 hB hSg) fun s1 hh => ?_
        obtain ⟨⟨hi, hB1, f1⟩, -, -, -⟩ := hh
        exact (WP.spec_ok _).2 ⟨hi, hB1, hX.fr f1, hSg.fr f1, hS.fr f1⟩
      · exact (WP.spec_ok _).2 h
    · refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 h
      split
      · exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
      · exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 h1

/-- A state the kernel reached from an entered state `s0` (`EntAt`) writing
only `Cur0W` words (the states P3's placement facts are stated at). -/
def XG (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (P3Ok : S → Prop) (s : S) : Prop :=
  ∃ s0, EntAt st P3Ok s0 ∧ Fr0 st T Cs Ω H Sg Scs Z s0 s

theorem XG.of_fr {P3Ok : S → Prop} {s s' : S} (h : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hw : WritesIn st s s' (Cur0W st T Cs Ω H Sg Scs Z s)) : XG st T Cs Ω H Sg Scs Z P3Ok s' :=
  let ⟨s0, hE, f⟩ := h; ⟨s0, hE, Cur0W.trans f hw⟩

/-- `XG` is kept by a kernel-word footprint. -/
theorem XG.foot {P3Ok : S → Prop} {s s' : S} (h : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (f : Foot st T Cs Sg Scs Z (EH H) s s') : XG st T Cs Ω H Sg Scs Z P3Ok s' :=
  h.of_fr (Foot.cur0w f fun _ hb => hb)

theorem XG.footD {P3Ok : S → Prop} {s s' : S} (h : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (f : FootD st T Cs Sg Scs Z (EH H) s s') : XG st T Cs Ω H Sg Scs Z P3Ok s' :=
  h.of_fr (FootD.cur0w f fun _ hb => hb)

/-- An entered state is an `XG` state. -/
theorem EntAt.xg {P3Ok : S → Prop} {s : S} (h : EntAt st P3Ok s) : XG st T Cs Ω H Sg Scs Z P3Ok s :=
  ⟨s, h, WritesIn.refl _ _⟩

/-- `XG` is kept by writes of the current node's words. -/
theorem XG.node {P3Ok : S → Prop} {s s' : S} (h : XG st T Cs Ω H Sg Scs Z P3Ok s) (hc : L.cpu s ∈ Cs)
    (w : WritesIn st s s' (L.NodeOf s (L.cpu s) fun _ => True)) : XG st T Cs Ω H Sg Scs Z P3Ok s' := by
  refine h.of_fr (w.mono fun b hb => ?_)
  obtain ⟨o, -, ho, -, rfl⟩ := hb
  by_cases h88 : o.val = 88
  · have : o = layout.node.DEBUG_TCBS := by
      apply UScalar.eq_of_val_eq; rw [h88]; simp [layout.node.DEBUG_TCBS]
    subst this
    exact Or.inr (Or.inl (Or.inr ⟨_, hc, rfl⟩))
  · exact Or.inl (kw_node hc ho h88)

/-- `XG` is kept by a budget check's writes before a timeout (`ChgW`). -/
theorem XG.chg {P3Ok : S → Prop} {s s' : S} (h : XG st T Cs Ω H Sg Scs Z P3Ok s) (hc : L.cpu s ∈ Cs)
    (w : WritesIn st s s' (ChgW st Scs Z s)) : XG st T Cs Ω H Sg Scs Z P3Ok s' :=
  h.of_fr (w.mono fun b hb => hb.elim (fun ⟨c, hc', hin⟩ => Or.inl (kw_sc hc' hin))
    fun e => e ▸ Or.inl (kw_node hc (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))

/-- **A fault IPC's guard from `XG` at its start.** -/
theorem XG.faultG {P3Ok : S → Prop} {Ac U : Set U64} {s : S} {t : U64} {f : error.Fault}
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t) :
    FaultG st H (XG st T Cs Ω H Sg Scs Z P3Ok) s t f := by
  intro s1 e s2 e1 hH hst e2
  have ht := hc.mem
  obtain ⟨⟨Q1, R1, q1⟩, -⟩ := (spec_at (faults.set_fault.blk s t f h ht hU hc) e1).1
  have F1 := spec_at (faults.set_fault.kw (Cs := Cs) (Sg := Sg) (Z := Z) (Scs := Scs) (Es := EH H) s t f h.1.choose_spec.choose_spec.tcbs ht) e1
  exact (hG.foot F1).foot (spec_at (endpoint.ep_dequeue.head_kw (Scs := Scs) q1 hH hst) e2)

/-- **A receive's guard from `XG` at its start.** -/
theorem XG.recvG {P3Ok : S → Prop} {Ac : Set U64} {A : Type _} {ar : machine.Arch A} {s : S} {a : A}
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : CanBlock st T Ac s (L.curW s)) : RecvG st ar H Rp (XG st T Cs Ω H Sg Scs Z P3Ok) s a := by
  intro rc e s2 s1 hcap ⟨r, s1', a1, et, hs2⟩ hH hst ed
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have P1 := spec_at (endpoint.take_reply.inv ar s a (L.curW s) rc Q R h0 hB hX hS hSg hc hcap) et
  simp only [WP.uncurry'_pair] at P1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, hc1, hi1, -, -, -⟩ := P1
  have F1 := spec_at (endpoint.take_reply.kw (Scs := Scs) ar s a (L.curW s) rc h0 hX hSg hcap) et
  simp only at F1
  rcases hs2 with rfl | ⟨i, ei⟩
  · exact (hG.foot F1).foot (spec_at (endpoint.ep_dequeue.head_kw (Scs := Scs) h1 hH hst) ed)
  · have hidle : L.idleW s1' ≠ L.curW s := by rw [hi1]; exact hc.ni
    obtain ⟨⟨Q2, R2, h2⟩, -⟩ := spec_at (notification.maybe_return_sched_context.inv s1' i _ Q R h1 hB1 hX1 hS1
      hSg1 hc.mem ⟨hc1.nq, hc1.nr, hc1.na⟩ hidle) ei
    have F2 := spec_at (notification.maybe_return_sched_context.kw (Scs := Scs) s1' i _ Q R h1 hB1 hX1 hS1 hSg1
      hc.mem ⟨hc1.nq, hc1.nr, hc1.na⟩ hidle) ei
    exact ((hG.foot F1).foot F2).foot (spec_at (endpoint.ep_dequeue.head_kw (Scs := Scs) h2 hH hst) ed)

/-! ## The invocation families -/

/-- The sets P1's invariants are stated over (the heap and what it
determines); a retype grows the heap, so a kernel entry ends over some
admissible sets (`Adm`). -/
structure PSets where
  T : Set U64
  Ω : Set U64
  H : Heap
  Sg : Set U64
  Rp : Set U64
  Scs : Set U64
  Nt : Set U64
  Z : U64 → Nat

/-- The hypotheses of the kernel-entry composites, one per family of kernel
operation not proved in P1, stated with P1's invariants.  An invocation may
shrink the active set (`Ac'`, an SC deletion); `handle_invocation` reports
its `CurStep` (for `HCur.step`) and, when it was preempted, what the
preemption point needs (that is `EntryHyps`' `inv`). -/
structure EntryHyps0 (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- The message transfer keeps the invariants within `XferFr` (`do_ipc_transfer`;
  `xferOK_of` proves it from `XferHyps`). -/
  xfer : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)
  /-- At a timeout fault of the current thread (`check_budget`'s
  `end_timeslice`): it can block, the user words are outside the kernel
  objects, and the caps (its timeout-handler slot) are typed. -/
  tmoOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s ∧
    ∀ i, (i = layout.tcb.SLOT_TIMEOUT_HANDLER ∨ i = layout.tcb.SLOT_FAULT_HANDLER) →
      obj.Tcb.slot (L.curW s) i ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄
  /-- The current thread can block and the user words are outside the kernel
  objects, at every `BXI` state (unguarded: `handle_invocation.inv` reads it
  after the invocation, over the sets after, and `decGap_reply`). -/
  blkU : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s) ∧ UserOK st T Cs Ω H U s
  /-- At a receive (`handle_recv`, an `XG` state): the caps the current
  thread looks up are typed, and the notification states are the three
  states. -/
  recvOK : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    (∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄) ∧
    (∀ n ∈ Nt, L.epState s n ≠ 3#u64)
  /-- At an `XG` state (where `handle_interrupt` runs: after the entry's
  budget check or an invocation's preemption point, both keeping `XG`,
  `check_budget.allG` / `mcs_preemption_point.allG` with `TmoXG`): the
  notification caps of the IRQ handler slots name heap notifications (P3's
  `CapValid`); `handle_interrupt` itself is proved
  (`interrupt.handle_interrupt.bxi`). -/
  irqcap : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ∀ i : U64, i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2, c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄
  /-- The debug syscalls (`debug_syscall`, which return to the thread directly). -/
  debug : ∀ (Ac : Set U64) (s : S) (a : A) (n : I64), EntAt st P3Ok s → EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    syscall.debug_syscall st ar s a (L.curW s) n ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄
  /-- (P3, from its post-invocation relation) The states after an invocation
  and after its preemption point are `XG` states: the preemption point's
  timeout and the receive that follows are message transfers. -/
  postG : ∀ (s0 : S) (a0 : A) (call blk don fp : Bool) (cptr : U64) (r : core.result.Result Unit error.Exc)
    (s1 : S) (a1 : A), EntAt st P3Ok s0 → syscall.handle_invocation st ar s0 a0 call blk don fp cptr = ok (r, s1, a1) →
    XG st T Cs Ω H Sg Scs Z P3Ok s1 ∧ ∀ (b : Bool) (s2 : S) (a2 : A),
      syscall.after_invocation st ar s1 a1 r = ok (b, s2, a2) → XG st T Cs Ω H Sg Scs Z P3Ok s2
  /-- `activate_thread`, after `schedule`. -/
  act : ∀ (Ac : Set U64) (s : S) (a : A), EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    sched.activate_thread st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄

/-- `EntryHyps0` and the invocations (`inv`), over the admissible sets `Adm`. -/
structure EntryHyps (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Adm : PSets → Prop)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop
    extends EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok where
  /-- The cap invocations (`handle_invocation`: lookup, decode, perform, reply);
  a retype may grow the heap, so the post is over some admissible sets. -/
  inv : ∀ (Ac : Set U64) (s : S) (a : A) (call blk don fp : Bool) (cptr : U64), EntAt st P3Ok s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → L.cscW s ∈ Ac → L.actionW s ≠ L.curW s →
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) →
    syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s' _ => ∃ σ', Adm σ' ∧ ∃ Ac',
      BXI st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Rp σ'.Scs σ'.Nt σ'.Z Ac' s' ∧
      (∀ e, r = .Err e → CurStep st Ac Ac' s s' ∧ L.actionW s' ≠ L.curW s' ∧
        (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ⦄

/-- `BXI` over a set tuple. -/
abbrev BXIs (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (σ : PSets) (Ac : Set U64) (s : S) : Prop :=
  BXI st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z Ac s

/-- `EntryInv` over a set tuple. -/
abbrev EntryInvs (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (σ : PSets) (Ac : Set U64) (s : S) : Prop :=
  EntryInv st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z Ac s

/-- The entry hypotheses of an admissible set tuple (and its notifications
being the heap's). -/
abbrev EHs (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (Adm : PSets → Prop) (Cs U : Set U64)
    (P3Ok : S → Prop) (σ : PSets) : Prop :=
  EntryHyps st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn

/-- Timeout faults keep the invariants (`faults.handle_timeout.bxi`). -/
theorem EntryHyps0.tmo {U : Set U64} (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (Ac : Set U64) {s0 : S} (hG0 : XG st T Cs Ω H Sg Scs Z P3Ok s0) (hc0 : L.cpu s0 ∈ Cs) :
    TmoK st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 :=
  fun s a f Q R h hB hX hSg hS w => by
    have hG := hG0.chg hc0 w
    obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    exact WP.spec_mono (faults.handle_timeout.bxi hA E.xfer s a _ f
      (XG.faultG hG ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc) ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc
      (hcap _ (Or.inl rfl)))
      fun r hr => by obtain ⟨s', a'⟩ := r; exact BlkOK.bxi (by simpa using hr)

/-- **Timeout faults keep `XG`** (a P1 lemma, `tmoXG_holds` in QueueIpcFoot,
downstream of this module: `send_ipc` keeps `XG`, its transfer by `XferOK`'s
guard and its other steps by `KW` footprints). -/
def TmoXG (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) : Prop :=
  ∀ (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop),
    XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok) →
    ∀ (Ac : Set U64) (s : S) (a : A) (t : obj.Tcb) (f : error.Fault), XG st T Cs Ω H Sg Scs Z P3Ok s →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s → CanBlock st T Ac s t →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄ →
      faults.handle_timeout st ar s a t f ⦃ s' _ => XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄

/-- Timeout faults keep the invariants and `XG` (`faults.handle_timeout.bxi`, `TmoXG`). -/
theorem EntryHyps0.tmoG {U : Set U64} (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (TX : TmoXG st ar) (Ac : Set U64) :
    TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac (XG st T Cs Ω H Sg Scs Z P3Ok) :=
  fun s a f Q R h hB hX hSg hS hG => by
    obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    exact WP.spec_mono (WP.spec_and (faults.handle_timeout.bxi hA E.xfer s a _ f
      (XG.faultG hG ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc) ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc
      (hcap _ (Or.inl rfl)))
      (TX T Cs Ω H Sg Rp Scs Nt Z U P3Ok E.xfer Ac s a _ f hG ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hU hc
        (hcap _ (Or.inl rfl))))
      fun r hr => by
        obtain ⟨s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨BlkOK.bxi hr.1, hr.2⟩

/-- Faults of the current thread keep the invariants (`faults.handle_fault.bxi`,
from `tmoOK` and `xfer`). -/
theorem EntryHyps0.fault {U : Set U64} (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (Ac : Set U64) (s : S) (a : A) (f : error.Fault) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG h
  exact WP.spec_mono (faults.handle_fault.bxi hA E.xfer s a _ f (XG.faultG hG h.blk hU hc) h.blk hU hc
    (hcap _ (Or.inr rfl)))
    fun r hr => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hr)⟩

/-- Receives keep the invariants (`syscall.handle_recv.bxi`). -/
theorem EntryHyps0.recv {U : Set U64} (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (Ac : Set U64) (s : S) (a : A) (blk rep : Bool)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  obtain ⟨hc, hU⟩ := E.blkU Ac s h
  obtain ⟨hlk, h3⟩ := E.recvOK Ac s hG h
  exact syscall.handle_recv.bxi hA hNt E.xfer s a blk rep h (XG.recvG hG h hc) hU hc hlk h3
    fun f => E.fault hA Ac s a f h hG

/-! ## The composites -/

/-- **seL4 `handleYield`** (MCS): the current SC is charged its head refill
and its `CONSUMED` word is updated. -/
theorem syscall.handle_yield.bxi (hA : P0.ArchTotal ar) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcA : L.cscW s ∈ Ac) (hna : L.actionW s ≠ L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (htmo : TmoK st ar T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_yield st ar s a ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  unfold syscall.handle_yield
  step with sched.cur_sc.spec as ⟨csc, ecsc⟩
  have e1 : csc = L.cscW s := ecsc
  subst e1
  step with obj.Sc.consumed.spec as ⟨i⟩
  step with sched.consumed.spec as ⟨i1⟩
  step as ⟨total, _⟩
  step with sporadic.head.spec as ⟨hd, ehd⟩
  refine WP.spec_bind (sched.charge_budget.all hA s a hd.amount false Q R h0 hB hX hSg hS hcsc hna hcA htmo) ?_
  rintro ⟨s1, a1⟩ ⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩
  try simp only [WP.uncurry'_pair]
  have hna1 := hna
  step with obj.Sc.set_consumed.spec as ⟨s2, e2⟩
  subst e2
  have hcS : L.cscW s ∈ Scs := hX.2.2.cur
  have hW1 : RefillsWF st s1 (L.cscW s) (Z (L.cscW s)) := hS1.wf hcS hcA
  have hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) := by
    obtain ⟨hP, hz⟩ := hX1.1.sc _ hcS
    obtain ⟨h8, -, -⟩ := sc_lo hP hz
    unfold Aligned; rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
  have w : WritesIn st s1 (L.wr s1 (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) total)
      (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨ b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) :=
    (writesIn_wr hal).mono fun b hb => Or.inr hb
  have hS2 := SCsOK.ringc h1 hS1 hX1 hcS w hW1.wr_cons
  obtain ⟨h2, hB2, hX2, hSg2, ea2, ec2, ecs2, f2⟩ := ring_bx h1 hB1 hX1 hSg1 hcS w
  have res : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac
      (L.wr s1 (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) total) :=
    ⟨⟨Q1, R1, h2⟩, hB2, hX2, hSg2, hS2⟩
  exact res

/-! ## The entry prefix's frame (`Ent`)

What a native syscall entry writes before it invokes a cap: the current
thread's `FAULT_IP` register (`handle_syscall`) and the current node's words
(`update_timestamp`; `check_budget` writes nothing when the budget is
sufficient).  P3's placement facts are stated at the entry state `e`
(`P3Ok e`) and handed over to the invocation's start `s` along `Ent e s`. -/

theorem sched.update_timestamp.fr (hA : P0.ArchTotal ar) (s : S) (a : A) (hN : NodePlaced st T s (L.cpu s)) :
    sched.update_timestamp st ar s a ⦃ s' _ => WritesIn st s s' (L.NodeOf s (L.cpu s) fun _ => True) ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hA.now a) ?_
  rintro ⟨now, a1⟩ -
  try simp only [WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  have w1 := writesIn_wr (st := st) (s := s) (v := now)
    (nodeAt_aligned hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  rw [show ∀ s0 : S, L.nodeA s0 layout.node.CONSUMED = L.nodeAt s0 (L.cpu s0) layout.node.CONSUMED from
    fun _ => rfl] at e2
  subst e2
  have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) (L.cpu s) := hN.wr
  rw [L.cpu_wr] at *
  have w2 := writesIn_wr (st := st) (s := L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) (v := total)
    (nodeAt_aligned hN1 (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
  refine (w1.trans w2).mono fun b hb => ?_
  rcases hb with rfl | rfl
  · exact ⟨_, trivial, by simp [layout.node.CUR_TIME], by simp [layout.node.CUR_TIME], rfl⟩
  · refine ⟨layout.node.CONSUMED, trivial, by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], ?_⟩
    first | rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)] | rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]

theorem sched.check_budget_restart.same (hA : P0.ArchTotal ar) (s : S) (a : A) :
    sched.check_budget_restart st ar s a ⦃ r s' _ => r = true → s' = s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold sched.check_budget_restart
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => r.1 = true → r.2.1 = s) ?_ ?_
  · unfold sched.check_budget
    refine WP.spec_bind (P0.sched.cur_sc.p0 st s hS) fun sc _ => ?_
    refine WP.spec_bind (P0.sched.consumed.p0 st s hS) fun c _ => ?_
    refine WP.spec_bind (P0.sporadic.sufficient.p0 st ar s a sc c hS hA) fun b _ => ?_
    split
    · refine WP.spec_bind (P0.sched.is_cur_domain_expired.p0 st s hS) fun b1 _ => ?_
      exact (WP.spec_ok _).2 fun _ => rfl
    · refine WP.spec_bind (P0.sched.charge_budget.p0 st ar s a c true hS hA) ?_
      rintro ⟨s1, a1⟩ -
      exact (WP.spec_ok _).2 fun h => by cases h
  rintro ⟨r, s1, a1⟩ e1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s1 hS) fun ct _ => ?_
  split
  · rename_i hr
    exact (WP.spec_ok _).2 fun _ => e1 hr
  · rename_i hr
    refine WP.spec_bind (P0.sched.is_runnable.p0 st s1 ct hS) fun b _ => ?_
    split
    · refine WP.spec_bind (P0.sched.set_thread_state.p0 st s1 ct _ hS) fun s2 _ => ?_
      exact (WP.spec_ok _).2 fun h => absurd h hr
    · exact (WP.spec_ok _).2 fun h => absurd h hr

/-- `budget_ok` at a kernel entry keeps the current SC. -/
theorem syscall.budget_ok.bxc (hA : P0.ArchTotal ar) (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {Ac : Set U64} (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.budget_ok st ar s a ⦃ b s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (b = true → L.cscW s' ∈ Ac ∧ L.actionW s' ≠ L.curW s' ∧
        (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s')))) ∧
      (b = true → XG st T Cs Ω H Sg Scs Z P3Ok s') ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  unfold syscall.budget_ok
  refine WP.spec_bind (WP.spec_and (sched.update_timestamp.entry hA s a h)
    (sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, c1, hcA, hna, hcsc, kk1⟩, w1⟩
  try simp only [WP.uncurry'_pair] at w1 ⊢
  have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := hG.node h0.cur w1
  refine WP.spec_mono (sched.check_budget_restart.all hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA
    (E.tmo hA Ac hG1 h1.cur)) ?_
  rintro ⟨r, s2, a2⟩ ⟨k2, e2⟩
  refine ⟨k2, fun hr => ?_, fun hr => ?_⟩
  · rw [e2 hr]; exact ⟨hcA, hna, hcsc⟩
  · rw [e2 hr]; exact hG1

/-- `budget_ok` passing writes only the current node's words. -/
theorem syscall.budget_ok.fr (hA : P0.ArchTotal ar) (s : S) (a : A) (hN : NodePlaced st T s (L.cpu s)) :
    syscall.budget_ok st ar s a ⦃ b s' _ => b = true → WritesIn st s s' (L.NodeOf s (L.cpu s) fun _ => True) ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (sched.update_timestamp.fr hA s a hN) ?_
  rintro ⟨s1, a1⟩ w1
  try simp only [WP.uncurry'_pair] at w1 ⊢
  refine WP.spec_mono (sched.check_budget_restart.same hA s1 a1) ?_
  rintro ⟨r, s2, a2⟩ e2 hr
  rw [e2 hr]; exact w1

/-- The entry prefix of a syscall: the `FAULT_IP` write, then a passing `budget_ok`. -/
theorem Ent.prefix {e s1 s2 : S} {K v : U64} (hK : K.val = 256 + 8 * layout.reg.FAULT_IP.val)
    (hal : Aligned (core.num.U64.wrapping_add (L.curW e) K))
    (e1 : s1 = L.wr e (core.num.U64.wrapping_add (L.curW e) K) v)
    (w2 : WritesIn st s1 s2 (L.NodeOf s1 (L.cpu s1) fun _ => True)) : Ent st e s2 := by
  subst e1
  refine ((writesIn_wr hal).trans w2).mono fun b hb => ?_
  rcases hb with rfl | ⟨o, -, ho, h8, rfl⟩
  · exact Or.inl ⟨K, hK, rfl⟩
  · exact Or.inr ⟨o, trivial, ho, h8, by rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]⟩

/-- The budget-check facts after a step that keeps the current SC and thread. -/
theorem CurK.entry {s s' : S} (k : CurK st s s') (hc : L.cscW s' = L.cscW s) (hna : L.actionW s ≠ L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) :
    L.actionW s' ≠ L.curW s' ∧
      (L.mem s' (scA (L.curW s')) ≠ 0#u64 → L.cscW s' = L.mem s' (scA (L.curW s'))) := by
  obtain ⟨c, sc, a⟩ := k
  rw [c]
  refine ⟨a hna, fun h0 => ?_⟩
  rcases sc with e | e
  · rw [e] at h0 ⊢; rw [hc]; exact hcsc h0
  · exact absurd e h0

/-- `finish`: `schedule` establishes `EntryInv`, `activate_thread` keeps it. -/
theorem syscall.finish.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.finish st ar s a ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.finish
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_bind (sched.schedule.entry hA hNt s a Q R h0 hB hS hX hSg) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (E.act Ac s1 a1 h1) fun r hr => ⟨Ac, hr⟩

/-- `after_invocation`: the preemption point of a preempted invocation, with
`HCur`, then a pending interrupt. -/
theorem syscall.after_invocation.bxi (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (TX : TmoXG st ar) (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {Ac : Set U64} (s : S) (a : A) (r : core.result.Result Unit error.Exc)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hc : ∀ e, r = .Err e → HCur st Ac s)
    (herr : ∀ e, r = .Err e → L.actionW s ≠ L.curW s ∧
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))) :
    syscall.after_invocation st ar s a r ⦃ _ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.after_invocation
  cases r with
  | Ok _ => exact (WP.spec_ok _).2 ⟨Ac, h⟩
  | Err e =>
    obtain ⟨hna, hcsc⟩ := herr e rfl
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
    dsimp only
    refine WP.spec_bind (syscall.mcs_preemption_point.allG hA s a Q R h0 hB hX hSg hS hcsc hna (hc e rfl)
      (fun _ _ g f => XG.foot g f) hG (E.tmoG hA TX Ac)) ?_
    rintro ⟨s1, a1⟩ ⟨h1, g1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.take_pending_irq a1) ?_
    rintro ⟨irq, a2⟩ -
    try simp only [WP.uncurry'_pair]
    unfold syscall.check_interrupt
    refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.1) ?_ ?_
    · split
      · exact WP.spec_mono (interrupt.handle_interrupt.bxi hA hNt s1 a2 irq h1 (E.irqcap Ac s1 g1 h1)) fun r hr => by
          obtain ⟨s', a'⟩ := r; exact ⟨Ac, by simpa using hr⟩
      · exact (WP.spec_ok _).2 ⟨Ac, h1⟩
    · rintro ⟨s2, a3⟩ h2
      exact (WP.spec_ok _).2 h2

/-- `dispatch_syscall`, after a successful budget check. -/
theorem syscall.dispatch_syscall.bxi (hA : P0.ArchTotal ar) (TX : TmoXG st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHs st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64) (he : EntAt st P3Ok s) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcA : L.cscW s ∈ Ac) (hna : L.actionW s ≠ L.curW s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))) :
    syscall.dispatch_syscall st ar s a number ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ⦄ := by
  obtain ⟨E, hNt⟩ := EH _ hσ
  have IA : ∀ (call blk don fp : Bool) (cptr : U64),
      syscall.handle_invocation st ar s a call blk don fp cptr ⦃ r s1 a1 =>
        syscall.after_invocation st ar s1 a1 r ⦃ _ s2 _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s2 ∧
          XG st σ'.T Cs σ'.Ω σ'.H σ'.Sg σ'.Scs σ'.Z P3Ok s2 ⦄ ⦄ :=
    fun call blk don fp cptr => WP.spec_mono (spec_eq' (E.inv Ac s a call blk don fp cptr he h hcA hna hcsc)) (by
      rintro ⟨r', s1, a1⟩ ⟨eqI, hr⟩
      simp only [WP.uncurry'_pair] at hr ⊢
      obtain ⟨σ1, hσ1, Ac1, h1, e1⟩ := hr
      obtain ⟨E1, hNt1⟩ := EH σ1 hσ1
      obtain ⟨G1, G2⟩ := E1.postG s a call blk don fp cptr r' s1 a1 he eqI
      exact WP.spec_mono (spec_eq' (syscall.after_invocation.bxi hA hNt1 TX E1.toEntryHyps0 s1 a1 r' h1 G1
        (fun e he => (HCur.of_mem hcA).step (e1 e he).1) fun e he => (e1 e he).2)) (by
          rintro ⟨b, s2, a2⟩ ⟨eqA, Ac2, h2⟩
          exact ⟨σ1, hσ1, Ac2, h2, G2 b s2 a2 eqA⟩))
  have IR : ∀ (call blk don fp : Bool) (cptr : U64) (b1 b2 : Bool),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (b, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        if b then syscall.handle_recv st ar s2 a2 b1 b2 else ok (s2, a2)) ⦃ s' _ =>
          ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ⦄ := by
    intro call blk don fp cptr b1 b2
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨σ2, hσ2, Ac2, h2, g2⟩
    try simp only [WP.uncurry'_pair]
    try simp only [uncurry_apply_pair]
    obtain ⟨E2, hNt2⟩ := EH σ2 hσ2
    split
    · exact WP.spec_mono (E2.recv hA hNt2 Ac2 s2 a2 b1 b2 h2 g2) fun _ ⟨Ac3, h3⟩ => ⟨σ2, hσ2, Ac3, h3⟩
    · exact (WP.spec_ok _).2 ⟨σ2, hσ2, Ac2, h2⟩
  have IS : ∀ (call blk don fp : Bool) (cptr : U64),
      (do
        let (r, s1, a1) ← syscall.handle_invocation st ar s a call blk don fp cptr
        let (_, s2, a2) ← syscall.after_invocation st ar s1 a1 r
        ok (s2, a2)) ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' s' ⦄ := by
    intro call blk don fp cptr
    refine WP.spec_bind (IA call blk don fp cptr) ?_
    rintro ⟨r, s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    refine WP.spec_bind hh ?_
    rintro ⟨b, s2, a2⟩ ⟨σ2, hσ2, Ac2, h2, -⟩
    exact (WP.spec_ok _).2 ⟨σ2, hσ2, Ac2, h2⟩
  unfold syscall.dispatch_syscall
  step with sched.cur_thread.spec as ⟨t, et⟩
  step with obj.Tcb.reg.spec as ⟨cptr⟩
  step with obj.Tcb.reg.spec as ⟨reply⟩
  by_cases c1 : number = fl4_abi.syscall.SysSend
  · rw [if_pos c1]; exact IS _ _ _ _ _
  rw [if_neg c1]
  by_cases c2 : number = fl4_abi.syscall.SysNBSend
  · rw [if_pos c2]; exact IS _ _ _ _ _
  rw [if_neg c2]
  by_cases c3 : number = fl4_abi.syscall.SysCall
  · rw [if_pos c3]; exact IS _ _ _ _ _
  rw [if_neg c3]
  by_cases c4 : number = fl4_abi.syscall.SysRecv
  · rw [if_pos c4]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c4]
  by_cases c5 : number = fl4_abi.syscall.SysNBRecv
  · rw [if_pos c5]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c5]
  by_cases c6 : number = fl4_abi.syscall.SysWait
  · rw [if_pos c6]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c6]
  by_cases c7 : number = fl4_abi.syscall.SysNBWait
  · rw [if_pos c7]; exact WP.spec_mono (E.recv hA hNt Ac s a _ _ h he.xg) fun _ ⟨Ac', h'⟩ => ⟨_, hσ, Ac', h'⟩
  rw [if_neg c7]
  by_cases c8 : number = fl4_abi.syscall.SysReplyRecv
  · rw [if_pos c8]; exact IR _ _ _ _ _ _ _
  rw [if_neg c8]
  by_cases c9 : number = fl4_abi.syscall.SysNBSendRecv
  · rw [if_pos c9]
    step with obj.Tcb.reg.spec as ⟨dest⟩
    exact IR _ _ _ _ _ _ _
  rw [if_neg c9]
  by_cases c10 : number = fl4_abi.syscall.SysNBSendWait
  · rw [if_pos c10]; exact IR _ _ _ _ _ _ _
  rw [if_neg c10]
  by_cases c11 : number = fl4_abi.syscall.SysYield
  · rw [if_pos c11]; exact WP.spec_mono (syscall.handle_yield.bxi hA s a h hcA hna hcsc
      (E.tmo hA Ac he.xg h.1.choose_spec.choose_spec.cur)) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact ⟨_, hσ, Ac, hr⟩
  rw [if_neg c11]
  exact (WP.spec_ok _).2 ⟨_, hσ, Ac, h⟩

/-- A register write at a kernel entry keeps `EntryInv`. -/
theorem reg_entry {Ac : Set U64} {s : S} {t r v : U64} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hr : r.val < 384) : obj.Tcb.set_reg st t s r v ⦃ s' => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (h0.tcbs t ht) hr) ?_
  rintro s' ⟨K, hK, rfl⟩
  obtain ⟨⟨⟨Q', R', h'⟩, hB', hX', hS', -⟩, -, n⟩ :=
    regW_all (Ac := Ac) (Sg := Sg) (Z := Z) ⟨⟨Q, R, h0⟩, hB, hX, hS, hS.sg⟩ ht (K := K) (v := v)
      (by omega) (by omega) (by omega)
  have f := fr_field (Sg := Sg) h0 hS.sg ht (K := K) (v := v) (by omega) (by omega)
    ⟨by omega, by omega, by omega, by omega, by omega, Or.inl (by omega)⟩
  refine ⟨⟨Q', R', h'⟩, hB', hX', hS', hX'.2.2.tm, by rw [f.csc]; exact hcA, by rw [n.1, n.2.2]; exact hna, ?_⟩
  rw [n.2.2, f.sc (L.curW s) h0.curT, f.csc]; exact hcsc

/-- seL4 `handleUnknownSyscall`'s fault path (`unknown_syscall_fault`). -/
theorem syscall.unknown_syscall_fault_old.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A) (n : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.unknown_syscall_fault_old st ar s a n ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.unknown_syscall_fault_old
  refine WP.spec_bind (syscall.budget_ok.bxc hA E s a h hG) ?_
  rintro ⟨b, s1, a1⟩ ⟨h1, -, g1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.1) ?_ ?_
  · split
    · step with sched.cur_thread.spec as ⟨t, et⟩
      have et' : t = L.curW s1 := et
      subst et'
      exact WP.spec_mono (E.fault hA Ac s1 a1 _ h1 (g1 (by assumption))) fun r hr => by
        obtain ⟨s', a'⟩ := r; simpa using hr
    · exact (WP.spec_ok _).2 ⟨Ac, h1⟩
  · rintro ⟨s2, a2⟩ ⟨Ac2, h2⟩
    exact syscall.finish.entry hA hNt E s2 a2 h2

/-- seL4 `handleUnknownSyscall`'s SetTLSBase path (`set_tls_base_self`). -/
theorem syscall.set_tls_base_self.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    syscall.set_tls_base_self st ar s a ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.set_tls_base_self
  refine WP.spec_bind (syscall.budget_ok.bxc hA E s a h hG) ?_
  rintro ⟨b, s1, a1⟩ ⟨h1, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s2 : S => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s2) ?_ ?_
  · split
    · step with sched.cur_thread.spec as ⟨t, et⟩
      have htT : t ∈ T := by rw [et]; exact h1.1.choose_spec.choose_spec.curT
      step with obj.Tcb.reg.spec as ⟨base⟩
      step with P0.regs.sanitise.p0 as ⟨i1⟩
      refine WP.spec_mono (regW_spec h1.blk htT (r := layout.reg.TLS_BASE)
        (by simp [layout.reg.TLS_BASE, layout.reg.FS_BASE])) ?_
      rintro s3 ⟨h3, -, -⟩
      exact ⟨Ac, h3.bxi⟩
    · exact (WP.spec_ok _).2 ⟨Ac, h1⟩
  · rintro s2 ⟨Ac2, h2⟩
    exact syscall.finish.entry hA hNt E s2 a1 h2

/-- Native `handleUnknownSyscall`, excluding the new VMEnter transition. -/
theorem syscall.handle_unknown_syscall_old.entry (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A) (number : I64)
    (hNative : number ≠ fl4_abi.syscall.SysVMEnter) (he : EntAt st P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_unknown_syscall_old st ar s a number ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  unfold syscall.handle_unknown_syscall_old
  step with sched.cur_thread.spec as ⟨t, et⟩
  simp only [fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, ↓reduceIte]
  split
  · step with obj.Tcb.reg.spec as ⟨c⟩
    step as ⟨i, _⟩
    refine WP.spec_bind (hA.putc a i) fun a1 _ => ?_
    exact (WP.spec_ok _).2 ⟨Ac, h⟩
  split
  · exact (WP.spec_ok _).2 ⟨Ac, h⟩
  have et' : t = L.curW s := et
  subst et'
  refine WP.spec_bind (WP.spec_and (E.debug Ac s a number he h) (syscall.debug_syscall.same hA s a _ number)) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨Ac1, h1⟩, e1⟩
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  split
  · exact (WP.spec_ok _).2 ⟨Ac1, h1⟩
  · rename_i hb
    simp only [WP.uncurry'_pair] at e1
    have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok s1 := by rw [e1 (by simpa using hb)]; exact he.xg
    simp only [fl4_abi.config.SET_TLS_BASE_SELF, ↓reduceIte]
    split
    · exact syscall.set_tls_base_self.entry hA hNt E s1 a1 h1 hG1
    · step as ⟨i, _⟩
      exact syscall.unknown_syscall_fault_old.entry hA hNt E s1 a1 i h1 hG1

/-- **Native `handle_syscall` keeps `EntryInv`**: the budget check at the entry, the
dispatch (with `HCur` across the invocation, `HCur.step`), then `schedule`. -/
theorem syscall.handle_syscall_old.entry (hA : P0.ArchTotal ar) (TX : TmoXG st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHs st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (number : I64)
    (hNative : number ≠ fl4_abi.syscall.SysVMEnter) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_syscall_old st ar s a number ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄ := by
  obtain ⟨E', hNt⟩ := EH _ hσ
  have E := E'.toEntryHyps0
  have W : ∀ {s : S} {a : A} {m : Result (S × A)},
      m ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ →
      m ⦃ s' _ => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄ := fun hm =>
    WP.spec_mono hm fun r hr => by obtain ⟨s', a'⟩ := r; obtain ⟨Ac', h'⟩ := hr; exact ⟨_, hσ, Ac', h'⟩
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  unfold syscall.handle_syscall_old
  step with sched.cur_thread.spec as ⟨t, et⟩
  have htT : t ∈ T := by rw [et]; exact hcT
  step with obj.Tcb.reg.spec as ⟨nx⟩
  step as ⟨i, _⟩
  refine WP.spec_bind (WP.spec_and (reg_entry h htT (r := layout.reg.FAULT_IP) (v := i) (by simp [layout.reg.FAULT_IP]))
    (obj.Tcb.set_reg.wrK s t layout.reg.FAULT_IP i (h.1.choose_spec.choose_spec.tcbs t htT)
      (by simp [layout.reg.FAULT_IP]))) ?_
  rintro s1 ⟨h1, K, hK, e1⟩
  have et' : t = L.curW s := et
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h.1.choose_spec.choose_spec.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal (by rw [e1, et']) (WritesIn.refl _ _)⟩
  step with P0.obj.Tcb.flags.p0 st t s1 L.total as ⟨fl⟩
  step as ⟨i2, _⟩
  split
  · step as ⟨i3, _⟩
    exact W (s := s) (a := a) (syscall.unknown_syscall_fault_old.entry hA hNt E s1 a i3 h1 he1.xg)
  split
  · exact W (s := s) (a := a) (syscall.handle_unknown_syscall_old.entry hA hNt E s1 a number hNative he1 h1)
  split
  · exact W (s := s) (a := a) (syscall.handle_unknown_syscall_old.entry hA hNt E s1 a number hNative he1 h1)
  have hcA1 : L.cscW s1 ∈ Ac := h1.2.2.2.2.2.1
  have hN1 : NodePlaced st T s1 (L.cpu s1) :=
    (h1.1.choose_spec.choose_spec).nodes _ h1.1.choose_spec.choose_spec.cur
  refine WP.spec_bind (WP.spec_and (syscall.budget_ok.bxc hA E s1 a h1 he1.xg) (syscall.budget_ok.fr hA s1 a hN1)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨h2, k2, -⟩, f2⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ σ', Adm σ' ∧ ∃ Ac', BXIs st Cs σ' Ac' r.1) ?_ ?_
  · split
    · rename_i hb
      obtain ⟨hcA2, hna2, hcsc2⟩ := k2 hb
      have he : EntAt st P3Ok s2 := ⟨s, hP, Ent.prefix hK hal (by rw [e1, et']) (f2 hb)⟩
      exact WP.spec_mono (syscall.dispatch_syscall.bxi hA TX EH hσ s2 a1 number he h2 hcA2 hna2 hcsc2)
        fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr
    · exact (WP.spec_ok _).2 ⟨_, hσ, Ac, h2⟩
  · rintro ⟨s3, a2⟩ ⟨σ3, hσ3, Ac3, h3⟩
    obtain ⟨E3, hNt3⟩ := EH σ3 hσ3
    exact WP.spec_mono (syscall.finish.entry hA hNt3 E3.toEntryHyps0 s3 a2 h3)
      fun r hr => by obtain ⟨s', a'⟩ := r; obtain ⟨Ac', h'⟩ := hr; exact ⟨σ3, hσ3, Ac', h'⟩

/-- **`handle_interrupt_entry` keeps `EntryInv`.** -/
theorem syscall.handle_interrupt_entry.entry (hA : P0.ArchTotal ar) (TX : TmoXG st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Ac : Set U64} (s : S) (a : A) (irq : U64)
    (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hG : XG st T Cs Ω H Sg Scs Z P3Ok s := EntAt.xg ⟨s, hP, WritesIn.refl _ _⟩
  unfold syscall.handle_interrupt_entry
  refine WP.spec_bind (WP.spec_and (sched.update_timestamp.entry hA s a h)
    (sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, -, hcA, hna, hcsc, -⟩, w1⟩
  try simp only [WP.uncurry'_pair] at w1 ⊢
  refine WP.spec_bind (sched.check_budget.allG hA s1 a1 Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc hna hcA
    (fun _ _ g f => XG.foot g f) (hG.node h0.cur w1) (E.tmoG hA TX Ac)) ?_
  rintro ⟨r, s2, a2⟩ ⟨⟨h2, g2⟩, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (interrupt.handle_interrupt.bxi hA hNt s2 a2 irq h2 (E.irqcap Ac s2 g2 h2)) ?_
  rintro ⟨s3, a3⟩ h3
  try simp only [WP.uncurry'_pair]
  exact syscall.finish.entry hA hNt E s3 a3 h3

/-- **Native kernel entries keep `EntryInv`** (`handle_syscall` excluding
VMEnter, `handle_interrupt_entry` for any IRQ), with the active set possibly
shrinking (SC deletion) and the heap possibly growing (retype): the entry
ends over some admissible set tuple.  The hypotheses not proved in P1 are
collected in `EntryHyps`, for every admissible tuple (`EH`); `hA` is P0's
arch totality. -/
theorem kernel_entry.entry (hA : P0.ArchTotal ar) (TX : TmoXG st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHs st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_old st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  ⟨fun number hNative => syscall.handle_syscall_old.entry hA TX EH hσ s a number hNative hP h,
   fun irq => WP.spec_mono (syscall.handle_interrupt_entry.entry hA TX (EH _ hσ).2 (EH _ hσ).1.toEntryHyps0 s a irq hP h)
     fun r hr => by obtain ⟨s', a'⟩ := r; obtain ⟨Ac', h'⟩ := hr; exact ⟨_, hσ, Ac', h'⟩⟩

end

end Fl4Proofs.P1
