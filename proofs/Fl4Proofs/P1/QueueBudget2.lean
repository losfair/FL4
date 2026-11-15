/-
P1: `end_timeslice`, `charge_budget`, `check_budget` and
`check_budget_restart` (sched.rs; seL4 `endTimeslice`, `chargeBudget`,
`checkBudget`, `checkBudgetRestart`) keep the queue invariant, `BoundInv` and
`XInv`.  A timeout fault (`faults::handle_timeout`) is a hypothesis.
-/
import Fl4Proofs.P1.QueueBudget
import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A}

/-- The invariants `end_timeslice` and its callers keep. -/
def BXI (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInv st T Cs Ω H s Q R) ∧ BoundInv st T Ac s ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s ∧ SgOK st Ω Sg s ∧
    SCsOK st T Ω Sg Scs Z Ac s

/-- The current thread across a step inside a kernel entry: it stays current,
its `SC` field is kept or cleared (a timeout fault may donate it), and it
does not become the switch-to candidate. -/
def CurK (st : machine.Store S) [L : LawfulStore st] (s0 s : S) : Prop :=
  L.curW s = L.curW s0 ∧
    (L.mem s (scA (L.curW s0)) = L.mem s0 (scA (L.curW s0)) ∨ L.mem s (scA (L.curW s0)) = 0#u64) ∧
    (L.actionW s0 ≠ L.curW s0 → L.actionW s ≠ L.curW s0)

theorem CurK.refl (s : S) : CurK st s s := ⟨rfl, Or.inl rfl, id⟩

theorem CurK.trans {s₁ s₂ s₃ : S} (h₁ : CurK st s₁ s₂) (h₂ : CurK st s₂ s₃) : CurK st s₁ s₃ := by
  obtain ⟨c1, k1, a1⟩ := h₁
  obtain ⟨c2, k2, a2⟩ := h₂
  rw [c1] at k2 a2
  refine ⟨c2.trans c1, ?_, fun h => a2 (a1 h)⟩
  rcases k2 with e | e
  · rcases k1 with e' | e'
    · exact Or.inl (e.trans e')
    · exact Or.inr (e.trans e')
  · exact Or.inr e

theorem CurK.of {s s' : S} (hT : TcbPlaced T) (hcT : L.curW s ∈ T) (hc : L.curW s' = L.curW s)
    (hsc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)))
    (ha : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) : CurK st s s' := by
  refine ⟨hc, Or.inl hsc, fun h e => ?_⟩
  rcases ha with ha | ha
  · exact h (ha ▸ e)
  · rw [ha] at e; exact notT_small hT (by simp) (e ▸ hcT)

/-- `BXI` after a step from `s0` that keeps the current SC (no step inside a
kernel entry before `schedule` switches it). -/
def BXC (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ L.cscW s = L.cscW s0 ∧ CurK st s0 s

/-- The current thread may be put back in its queue or postponed: it is
schedulable, the current SC is its SC, and it is not the switch-to
candidate. -/
structure CurOK (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop where
  run : Runnable (L.mem s (stA (L.curW s)))
  bnd : L.mem s (scA (L.curW s)) ≠ 0#u64
  rel : (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64
  csc : L.cscW s = L.mem s (scA (L.curW s))
  act : L.actionW s ≠ L.curW s
  rmx : L.rmax s (L.mem s (scA (L.curW s))) ≠ 0#u64

theorem end_append (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s) :
    (do let s1 ← sched.append st s (L.curW s); ok (s1, a)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hcT : L.curW s ∈ T := h.curT
  refine WP.spec_bind (sched.append.sch s _ Q R h hB hSg hcT (fun _ => hc.rel) (fun _ => hc.run)
    (fun _ => hc.bnd) (fun _ => (hS.act _ (hX.2.2.bound _ hcT hc.bnd).1).2 hc.rmx)) ?_
  rintro s1 ⟨⟨hi, hB1, f1⟩, ea1, ec1, -⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  obtain ⟨Q1, R1, h1⟩ := hi
  exact ⟨⟨Q1, R1, h1⟩, hB1, hX.fr f1, hSg.fr f1, hS.fr f1⟩

theorem end_postpone (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s) :
    (do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hcT : L.curW s ∈ T := h.curT
  obtain ⟨hSc, htc, hcore⟩ := hX.2.2.bound (L.curW s) hcT hc.bnd
  rw [← hc.csc] at hSc htc hcore
  have hco : OutsideObjs st T Cs s (scCoreA (L.cscW s)) := h.omega _ ((objs_omega hX.1 hSg.sub).2 _ hSc).2.1
  rw [← htc] at hcT
  refine WP.spec_bind (sched.postpone.all s _ Q R h hcT hB hX hSg (by rw [htc]; exact hc.rel) hco hcore
    (by rw [htc]; exact hc.run) (by rw [htc]; exact hc.act) (by rw [htc]; exact hc.bnd)
    (by rw [htc]; exact (hS.act _ (hc.csc ▸ hSc)).2 hc.rmx)) ?_
  rintro s1 ⟨Q1, R1, h1, hB1, hX1, hSg1, f1, ea1, ec1⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS.fr f1⟩

theorem end_suff (hA : P0.ArchTotal ar) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s) :
    (do
      let b ← sporadic.ready st s (L.cscW s)
      if b = true then do
        let b1 ← sporadic.sufficient st ar s a (L.cscW s) 0#u64
        if b1 = true then do let s1 ← sched.append st s (L.curW s); ok (s1, a)
        else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)
      else do let s1 ← sched.postpone st s (L.cscW s); ok (s1, a)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  step with sporadic.ready.spec as ⟨b⟩
  split
  · step with sporadic.sufficient.ok (st := st) hA as ⟨b1⟩
    split
    · exact end_append s a Q R h hB hX hSg hS hc
    · exact end_postpone s a Q R h hB hX hSg hS hc
  · exact end_postpone s a Q R h hB hX hSg hS hc

/-- seL4 `endTimeslice`. -/
theorem sched.end_timeslice.all (hA : P0.ArchTotal ar) (s : S) (a : A) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s)
    (htmo : ∀ (s : S) (a : A) (f : error.Fault) (Q : U64 → U64 → List U64) (R : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
      SCsOK st T Ω Sg Scs Z Ac s → faults.handle_timeout st ar s a (L.curW s) f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    sched.end_timeslice st ar s a cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have E := end_suff hA s a Q R h hB hX hSg hS hc
  unfold sched.end_timeslice
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e1 : sc = L.cscW s := sc_post
  have e2 : ct = L.curW s := ct_post
  subst e1 e2
  step with sporadic.is_round_robin.spec as ⟨rr⟩
  step with obj.Tcb.state.spec
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun valid _ => ?_
  · split
    · exact P0.faults.valid_timeout_handler.p0 st s _ L.total
    · simp
  split
  · split
    · exact E
    · split
      · step with P0.obj.Sc.badge.p0 st _ s L.total as ⟨badge⟩
        exact htmo s a _ Q R h hB hX hSg hS
      · exact E
  · exact E

/-! ## `charge_budget` -/

/-- Writes to the ring and `CONSUMED` word of an SC object. -/
theorem ring_bx {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hc : c ∈ Scs)
    (w : WritesIn st s s' (fun b => InRing c (Z c) b ∨ b = core.num.U64.wrapping_add c layout.sc.CONSUMED)) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (stA y) = L.mem s (stA y) ∧
        L.mem s' (inqA y) = L.mem s (inqA y)) := by
  obtain ⟨hP, hz⟩ := hX.1.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hN' := h.nodes _ h.cur
  have inΩ : ∀ b, Aligned b → (InRing c (Z c) b ∨ b = core.num.U64.wrapping_add c layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hX.1.scW c hc b hb hh.inSC
    · have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      exact hX.1.scW c hc _ hb ⟨by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
  have wF : WritesIn st s s' (L.Free s Ω Cs) := w.mono' fun b hb hh => Or.inl (inΩ b hb hh)
  have nodeK : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8' => by
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact w.mem_eq (nodeAt_aligned hN' ho h8') fun hh =>
      out_ne_node (h.omega _ (inΩ _ (nodeAt_aligned hN' ho h8') hh)) h.cur hN' ho rfl
  have fldK : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    w.mem_eq (field_aligned (h.tcbs y hy) hK hK8) fun hh =>
      out_ne_field (h.omega _ (inΩ _ (field_aligned (h.tcbs y hy) hK hK8) hh)) hy (h.tcbs y hy) hK rfl
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA; exact nodeK _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  refine ⟨inv_of_free h wF, hB.free h wF, hX.writes h.tcbs
    (w.mono' (B := fun b => ¬ Prot T Rp Scs Nt b) fun b hb hh => not_prot_ring h hX.1 hc hb hh) (fun b hb => hb)
    (by rw [ecs]; exact hX.2.2.cur) (hX.tn_writes h w fun b hb hh => notTmW_ring h hX.1 hSg.sub hc hb hh)
    (by unfold LawfulStore.idleW; exact nodeK _ (by rw [idle8]; omega) (by rw [idle8])),
    ⟨hSg.sub, fun b hb => by rw [w.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [w.1]; exact hSg.ksΩ o h1 h2⟩,
    by unfold LawfulStore.actionW; exact nodeK _ (by rw [act_val]; omega) (by rw [act_val]),
    by unfold LawfulStore.curW; exact nodeK _ (by rw [curth0]; omega) (by rw [curth0]), ecs,
    fun y hy => ⟨by rw [scA_eq]; exact fldK y hy _ (by simp) (by simp),
      by rw [stA_eq]; exact fldK y hy _ (by simp) (by simp), by rw [inqA_eq]; exact fldK y hy _ (by simp) (by simp)⟩⟩

/-- A write to a current-node word that the invariants do not read. -/
theorem node_bx {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {o v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (ho : LowFree o.val) (h24 : o.val ≠ 24) (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s (L.nodeAt s (L.cpu s) o) v) Q R ∧
      BoundInv st T Ac (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧ XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      SgOK st Ω Sg (L.wr s (L.nodeAt s (L.cpu s) o) v) ∧
      L.actionW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.actionW s ∧
      L.curW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.curW s ∧
      L.cscW (L.wr s (L.nodeAt s (L.cpu s) o) v) = L.cscW s ∧
      (∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (scA y) = L.mem s (scA y) ∧
        L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (stA y) = L.mem s (stA y) ∧
        L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (inqA y) = L.mem s (inqA y)) := by
  have hN' := h.nodes _ h.cur
  unfold LowFree at ho
  have ha : Aligned (L.nodeAt s (L.cpu s) o) := nodeAt_aligned hN' (by omega) (by omega)
  have wF : WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) o) v) (L.Free s Ω Cs) :=
    free_node_write rfl h.cur hN' (by unfold LowFree; omega)
  have nd : ∀ o' : U64, o'.val < 4288 → o'.val % 8 = 0 → o'.val ≠ o.val →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (L.nodeAt (L.wr s (L.nodeAt s (L.cpu s) o) v)
        (L.cpu (L.wr s (L.nodeAt s (L.cpu s) o) v)) o') = L.mem s (L.nodeAt s (L.cpu s) o') :=
    fun o' h1 h2 h3 => rd_cur_node h (by omega) (by omega) h1 h2 (Ne.symm h3)
  have fl : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) o) v) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    field_wr_node h h.cur (by omega) (by omega) hy hK hK8
  obtain ⟨hB', hX'⟩ := bx_wr (v := v) h hB hX ha (not_prot_node h hX.1 hSg.sub h.cur (by omega))
    (fun y hy => ⟨fun e => node_ne_field (o := o) hN' (by omega) hy (h.tcbs y hy) (K := 3464#u64) (by decide)
        (by rw [scA_eq] at e; exact UScalar.eq_of_val_eq e),
      fun e => node_ne_field (o := o) hN' (by omega) hy (h.tcbs y hy) (K := 3592#u64) (by decide)
        (by rw [inqA_eq] at e; exact UScalar.eq_of_val_eq e)⟩)
    (fun o' ho' e => by
      rw [nodeAt_val hN' (by omega), nodeAt_val hN' (by omega)] at e; omega)
    (hX.tn_node h hSg.sub h.cur (by omega) (by omega) hto)
  refine ⟨inv_of_free h wF, hB', hX', ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb,
    fun o' h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o' h1 h2⟩,
    by unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega),
    by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega),
    by unfold LawfulStore.cscW LawfulStore.nodeA
       exact nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]; omega),
    fun y hy => ⟨by rw [scA_eq]; exact fl y hy _ (by simp) (by simp),
      by rw [stA_eq]; exact fl y hy _ (by simp) (by simp), by rw [inqA_eq]; exact fl y hy _ (by simp) (by simp)⟩⟩


/-- `SCsOK` after writes to the ring and `CONSUMED` word of the SC object
`i`, kept well formed. -/
theorem SCsOK.ringc {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {i : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hi : i ∈ Scs)
    (w : WritesIn st s s' (fun b => InRing i (Z i) b ∨ b = core.num.U64.wrapping_add i layout.sc.CONSUMED))
    (hwi : RefillsWF st s' i (Z i)) : SCsOK st T Ω Sg Scs Z Ac s' := by
  obtain ⟨hO, -, hE⟩ := hX
  have hN' := h.nodes _ h.cur
  obtain ⟨hP, hz⟩ := hO.sc i hi
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hcv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have inΩ : ∀ b, Aligned b → (InRing i (Z i) b ∨ b = core.num.U64.wrapping_add i layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hO.scW i hi b hb hh.inSC
    · exact hO.scW i hi _ hb ⟨by rw [hcv]; simp, by rw [hcv]; simp [layout.sc.CONSUMED]; omega⟩
  have fld : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy =>
    w.mem_eq (scA_aligned (h.tcbs y hy)) fun hh =>
      out_ne_field (h.omega _ (inΩ _ (scA_aligned (h.tcbs y hy)) hh)) hy (h.tcbs y hy) (K := 3464#u64) (by decide) rfl
  have csc : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]
    have aC : Aligned (L.nodeA s layout.node.CUR_SC) :=
      nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    exact w.mem_eq aC fun hh => out_ne_node (h.omega _ (inΩ _ aC hh)) h.cur hN' (by simp [layout.node.CUR_SC]) rfl
  have wf : ∀ c ∈ Scs, RefillsWF st s c (Z c) → RefillsWF st s' c (Z c) := by
    intro c hc hW
    by_cases e : c = i
    · subst e; exact hwi
    refine hW.writesIn w fun b hb hh => ?_
    have := hO.scDisj c hc i hi e
    rcases hh with hh | rfl
    · unfold Outside; unfold InRing at hh; omega
    · unfold Outside; rw [hcv]; simp [layout.sc.CONSUMED]; omega
  have kk : ∀ c ∈ Scs, ∀ b, Aligned b → (b.val = c.val + 72 ∨ b.val = c.val + 64 ∨ b.val = c.val + 32) →
      L.mem s' b = L.mem s b := by
    intro c hc b hb hv
    refine w.mem_eq hb ?_
    rintro (hh | e)
    · unfold InRing at hh
      by_cases e : c = i
      · subst e; omega
      · have := hO.scDisj c hc i hi e; have := (sc_facts hO hc).1; omega
    · have hb' := congrArg UScalar.val e
      rw [hcv] at hb'; simp [layout.sc.CONSUMED] at hb'
      by_cases e' : c = i
      · subst e'; omega
      · have := hO.scDisj c hc i hi e'; have := (sc_facts hO hc).1; omega
  refine hS.mk2 w.1 fld csc (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc h0 => hS.rep c hc ?_)
  rotate_right
  · obtain ⟨hPc, hzc⟩ := hO.sc c hc; obtain ⟨h8c, -, -⟩ := sc_lo hPc hzc
    have := scReplyA_val hPc hzc
    rwa [kk c hc _ (by unfold Aligned; omega) (Or.inr (Or.inr this))] at h0
  · by_cases e : c = i
    · subst e; exact (hS.all c hc).mk' fun _ => hwi
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc
    refine (hS.all c hc).writesIn a1 ⟨a2, a3⟩ w fun b hb hh => ?_
    have := hO.scDisj c hc i hi e
    rcases hh with hh | rfl
    · unfold Outside; unfold InRing at hh; omega
    · unfold Outside; rw [hcv]; simp [layout.sc.CONSUMED]; omega
  · obtain ⟨a1, -, -⟩ := maxA_facts hO hc
    exact kk c hc _ a1 (Or.inl (sc_facts hO hc).2.2.2.1)
  · obtain ⟨hPc, hzc⟩ := hO.sc c hc
    obtain ⟨h8c, -, -⟩ := sc_lo hPc hzc
    have := sporA_val hPc hzc
    exact kk c hc _ (by unfold Aligned; omega) (Or.inr (Or.inl this))

/-- seL4 `chargeBudget` keeps the invariants, when the current SC is the
current thread's (if it is schedulable), the current thread is not the
switch-to candidate, and timeout faults keep them. -/
theorem sched.charge_budget.all (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64) (cto : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    (htmo : ∀ (s : S) (a : A) (f : error.Fault) (Q : U64 → U64 → List U64) (R : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
      SCsOK st T Ω Sg Scs Z Ac s → faults.handle_timeout st ar s a (L.curW s) f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    sched.charge_budget st ar s a used cto ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hcS : L.cscW s ∈ Scs := hX.2.2.cur
  have hcT0 : L.curW s ∈ T := h.curT
  have hW : RefillsWF st s (L.cscW s) (Z (L.cscW s)) := hS.wf hcS hcA
  unfold sched.charge_budget
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  have e1 : sc = L.cscW s := sc_post
  subst e1
  step with sched.idle_sc.spec as ⟨s1⟩
  step with sc_ne.spec as ⟨b⟩
  -- the ring and the SC's `CONSUMED` word
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) ∧ RefillsWF st s2 (L.cscW s) (Z (L.cscW s))) ?_ ?_
  · split
    · step with sporadic.is_round_robin.spec as ⟨b1⟩
      refine WP.spec_bind (Pₘ := fun s3 => RefillsWF st s3 (L.cscW s) (Z (L.cscW s)) ∧
          WritesIn st s s3 (InRing (L.cscW s) (Z (L.cscW s)))) ?_ ?_
      · split
        · step with obj.Sc.refill_head.spec as ⟨hi, hi_post⟩
          step with obj.Sc.refill_tail.spec as ⟨ti, ti_post⟩
          step with sporadic.get.spec as ⟨hh, hh_post⟩
          step with sporadic.get.spec as ⟨tt, tt_post⟩
          step as ⟨i, _⟩
          step with sporadic.put.spec as ⟨s4, s4_post⟩
          subst hi_post ti_post s4_post
          have h4 := hW.putS (r := { hh with amount := i }) hW.head_lt
          have w4 := hW.frame_putS (r := { hh with amount := i }) hW.head_lt
          obtain ⟨h8, -, -⟩ := hW.bounds
          have hfit : (L.cscW s).val + 96 + 16 * (L.rhead s (L.cscW s)).val + 16 ≤ 2 ^ 64 := by
            have := hW.bounds.2.2; have := hW.inside; have := hW.head_lt; have := hW.le_abs
            have := absMax_lt (Z (L.cscW s)); obtain ⟨-, hm, -⟩ := hW.bounds; omega
          have htl : (L.rtail s (L.cscW s)).val < (L.rmax (L.putS s (L.cscW s) (L.rhead s (L.cscW s))
              { hh with amount := i }) (L.cscW s)).val := by
            rw [rmax_putS h8 hfit]; exact hW.tail_lt
          step with sporadic.put.spec as ⟨s5, s5_post⟩
          subst s5_post
          exact ⟨h4.putS htl, w4.trans1 (h4.frame_putS htl)⟩
        · exact WP.spec_mono (WP.spec_and (sporadic.budget_check.wf hA a used hW rfl)
            (sporadic.budget_check.fr hA a used hW rfl)) fun s3 hh3 => hh3
      · rintro s3 ⟨h3, w3⟩
        step with obj.Sc.consumed.spec as ⟨ci⟩
        step as ⟨total, _⟩
        step with obj.Sc.set_consumed.spec as ⟨s4, s4_post⟩
        subst s4_post
        have hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) := by
          obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
          obtain ⟨h8, -, -⟩ := sc_lo hP hz
          unfold Aligned; rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
        exact ⟨(w3.trans (writesIn_wr hal)).mono fun b hb => by
          rcases hb with hb | hb
          · exact Or.inl hb
          · exact Or.inr hb, h3.wr_cons⟩
    · simp only [WP.spec_ok]; exact ⟨WritesIn.refl _ _, hW⟩
  rintro s2 ⟨w2, wf2⟩
  have hS2 := SCsOK.ringc h hS hX hcS w2 wf2
  obtain ⟨h2, hB2, hX2, hSg2, ea2, ec2, ecs2, f2⟩ := ring_bx h hB hX hSg hcS w2
  -- the node's `CONSUMED`
  step with sched.set_consumed.spec as ⟨s3, s3_post⟩
  rw [show L.nodeA s2 layout.node.CONSUMED = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED from rfl] at s3_post
  obtain ⟨h3, hB3, hX3, hSg3, ea3, ec3, ecs3, f3⟩ := node_bx (o := layout.node.CONSUMED) (v := 0#u64) h2 hB2 hX2 hSg2
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hS3 : SCsOK st T Ω Sg Scs Z Ac (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64) := by
    have hN2 := h2.nodes _ h2.cur
    obtain ⟨-, hc⟩ := objs_omega hX2.1 hS2.sub
    have hco : (layout.node.CONSUMED).val = 40 := by simp [layout.node.CONSUMED]
    refine SCsOK.wr h2 hS2 hX2 (nodeAt_aligned hN2 (by rw [hco]; omega) (by rw [hco])) (fun y hy => ?_) ?_
      (fun c hc' => ?_) (fun c hc' => out_ne_node (h2.omega _ (spor_omega hX2.1 hc')) h2.cur hN2 (by rw [hco]; omega))
      (fun c hc' e => absurd e (out_ne_node (h2.omega _ (hS2.sub _ (hX2.1.repW c hc'))) h2.cur hN2 (by rw [hco]; omega)))
    · rw [scA_eq]; exact fun e => node_ne_field hN2 (by rw [hco]; omega) hy (h2.tcbs y hy) (by simp)
        (UScalar.eq_of_val_eq e)
    · intro e
      simp only [LawfulStore.nodeA] at e
      rw [nodeAt_val hN2 (by rw [hco]; omega), nodeAt_val hN2 (by simp [layout.node.CUR_SC]), hco] at e
      simp [layout.node.CUR_SC] at e
    · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
      exact ⟨out_ne_node (h2.omega _ c3) h2.cur hN2 (by rw [hco]; omega),
        out_ne_node (h2.omega _ c4) h2.cur hN2 (by rw [hco]; omega),
        out_ne_node (h2.omega _ c5) h2.cur hN2 (by rw [hco]; omega)⟩
  rw [← s3_post] at h3 hB3 hX3 hSg3 ea3 ec3 ecs3 f3 hS3
  have K3 : CurK st s s3 := CurK.of h.tcbs hcT0 (ec3.trans ec2) ((f3 _ hcT0).1.trans (f2 _ hcT0).1)
    (Or.inl (ea3.trans ea2))
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e2 : ct = L.curW s3 := ct_post
  subst e2
  step with sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hrun, hbd, hrl, hrm⟩ := b1_post hb1
    have hcT : L.curW s ∈ T := h.curT
    have esc : L.mem s3 (scA (L.curW s3)) = L.mem s (scA (L.curW s)) := by
      rw [ec3, ec2, (f3 _ hcT).1, (f2 _ hcT).1]
    have hc : CurOK st T s3 := ⟨hrun, hbd, hrl, by
      rw [ecs3, ecs2, esc]; exact hcsc (by rw [← esc]; exact hbd), by rw [ea3, ea2, ec3, ec2]; exact hna, hrm⟩
    refine WP.spec_bind (sched.end_timeslice.all hA s3 a cto Q R h3 hB3 hX3 hSg3 hS3 hc htmo) ?_
    rintro ⟨s4, a1⟩ ⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (sched.reschedule_required.sch s4 Q4 R4 h4 hB4 hSg4) ?_
    rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, ea5, ec5, -⟩
    refine WP.spec_bind (sched.set_reprogram.sch s5 Q5 R5 h5 hB5 (hSg4.fr f5)) ?_
    rintro s6 ⟨⟨h6, hB6, f6⟩, ea6, ec6⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨Q5, R5, h6⟩, hB6, (hX4.fr f5).fr f6, (hSg4.fr f5).fr f6, (hS4.fr f5).fr f6⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, hS3⟩

/-- seL4 `checkBudget`. -/
theorem sched.check_budget.all (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    (htmo : ∀ (s : S) (a : A) (f : error.Fault) (Q : U64 → U64 → List U64) (R : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
      SCsOK st T Ω Sg Scs Z Ac s → faults.handle_timeout st ar s a (L.curW s) f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    sched.check_budget st ar s a ⦃ r s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ (r = true → s' = s) ⦄ := by
  unfold sched.check_budget
  step with sched.cur_sc.spec as ⟨sc⟩
  step with sched.consumed.spec as ⟨c⟩
  step with sporadic.sufficient.ok (st := st) hA as ⟨b⟩
  split
  · unfold sched.is_cur_domain_expired
    simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
    have hnd : ¬ ((1#u64) > (1#u64)) := by simp
    simp only [hnd, ↓reduceIte, bind_ok, WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩, fun _ => trivial⟩
  · refine WP.spec_bind (sched.charge_budget.all hA s a c true Q R h hB hX hSg hS hcsc hna hcA htmo) ?_
    rintro ⟨s1, a1⟩ h1
    exact (WP.spec_ok _).2 ⟨h1, fun e => absurd e (by simp)⟩

theorem sched.is_runnable.spec' (s : S) (t : obj.Tcb) :
    sched.is_runnable st s t ⦃ b => b = true → Runnable (L.mem s (stA t)) ⦄ := by
  refine WP.spec_mono (sched.is_runnable.spec s t) ?_
  intro b hb h
  unfold Runnable
  exact of_decide_eq_true (hb.symm.trans h)

/-- seL4 `checkBudgetRestart`. -/
theorem sched.check_budget_restart.all (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    (htmo : ∀ (s : S) (a : A) (f : error.Fault) (Q : U64 → U64 → List U64) (R : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
      SCsOK st T Ω Sg Scs Z Ac s → faults.handle_timeout st ar s a (L.curW s) f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    sched.check_budget_restart st ar s a ⦃ r s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ (r = true → s' = s) ⦄ := by
  unfold sched.check_budget_restart
  refine WP.spec_bind (sched.check_budget.all hA s a Q R h hB hX hSg hS hcsc hna hcA htmo) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, e1⟩
  try simp only [WP.uncurry'_pair]
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have hct : ct ∈ T := by rw [ct_post]; exact h1.curT
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, e1⟩
  rename_i hrf
  step with sched.is_runnable.spec' as ⟨b, b_post⟩
  split
  · rename_i hb
    have hnb : ¬ Blocked (L.mem s1 (stA ct)) := fun hbl => not_runnable_of_blocked hbl (b_post hb)
    refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s1 ct _ Q1 R1 h1 hct not_blocked_restart
      (Or.inr hnb) ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
      (sched.set_thread_state.state s1 ct _ Q1 R1 h1 hct hX1.1 hSg1.sub)) ?_
    rintro s2 ⟨h2, e2, k2⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    have nrr : sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_RECV := by
      obtain ⟨-, -, h3', -⟩ := ts_vals
      rw [ts_restart, ts_reply, h3']; decide
    refine ⟨⟨⟨Q1, R1, h2.congrX empty_congr⟩, hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_restart) (by rw [e2]; exact nrr.1), hX1.keepT k2 (by rw [e2]; exact nrr)
      (fun r hr e => absurd e (hX1.noref (h1.tcbs ct hct) (runnable_ne_reply (b_post hb))
        (runnable_ne_recv (b_post hb)) r hr)),
      ⟨hSg1.sub, fun b hb => by rw [k2.ksb]; exact hSg1.ks b hb, fun o h1' h2' => by rw [k2.ksb]; exact hSg1.ksΩ o h1' h2'⟩,
      hS1.keepT hX1 k2⟩, fun e => absurd e hrf⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hSg1, hS1⟩, fun e => absurd e hrf⟩

/-- Clearing the node's `CONSUMED` word keeps the invariants. -/
theorem consumed0_bxi {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s (L.cpu s) layout.node.CONSUMED) 0#u64) := by
  obtain ⟨h3, hB3, hX3, hSg3, ea3, ec3, ecs3, f3⟩ := node_bx (o := layout.node.CONSUMED) (v := 0#u64) h hB hX hSg
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hN := h.nodes _ h.cur
  obtain ⟨-, hc⟩ := objs_omega hX.1 hS.sub
  have hco : (layout.node.CONSUMED).val = 40 := by simp [layout.node.CONSUMED]
  refine ⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, SCsOK.wr h hS hX (nodeAt_aligned hN (by rw [hco]; omega) (by rw [hco]))
    (fun y hy => ?_) ?_ (fun c hc' => ?_) (fun c hc' => out_ne_node (h.omega _ (spor_omega hX.1 hc')) h.cur hN
      (by rw [hco]; omega))
    (fun c hc' e => absurd e (out_ne_node (h.omega _ (hS.sub _ (hX.1.repW c hc'))) h.cur hN (by rw [hco]; omega)))⟩
  · rw [scA_eq]; exact fun e => node_ne_field hN (by rw [hco]; omega) hy (h.tcbs y hy) (by simp)
      (UScalar.eq_of_val_eq e)
  · intro e
    simp only [LawfulStore.nodeA] at e
    rw [nodeAt_val hN (by rw [hco]; omega), nodeAt_val hN (by simp [layout.node.CUR_SC]), hco] at e
    simp [layout.node.CUR_SC] at e
  · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
    exact ⟨out_ne_node (h.omega _ c3) h.cur hN (by rw [hco]; omega),
      out_ne_node (h.omega _ c4) h.cur hN (by rw [hco]; omega),
      out_ne_node (h.omega _ c5) h.cur hN (by rw [hco]; omega)⟩

/-- seL4 `mcsPreemptionPoint`.  The current SC is charged only when it is
active: either the current thread is schedulable and runs on it (or it is
active anyway), or `sc_active` was checked.  `hcur` is what holds inside a
kernel entry: the current SC is active, or the current thread has no other
SC than it (it may have lost its SC, e.g. after the SC was deleted). -/
theorem syscall.mcs_preemption_point.all (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s)
    (hcur : L.cscW s ∈ Ac ∨ L.mem s (scA (L.curW s)) = L.cscW s ∨ L.mem s (scA (L.curW s)) = 0#u64)
    (htmo : ∀ (s : S) (a : A) (f : error.Fault) (Q : U64 → U64 → List U64) (R : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
      SCsOK st T Ω Sg Scs Z Ac s → faults.handle_timeout st ar s a (L.curW s) f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    syscall.mcs_preemption_point st ar s a ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have ect : ct = L.curW s := ct_post
  subst ect
  step with sched.is_schedulable.spec' as ⟨b, eb⟩
  split
  · rename_i hb
    obtain ⟨-, hbd, -, hrm⟩ := eb hb
    have hcA : L.cscW s ∈ Ac := by
      rcases hcur with e | e | e
      · exact e
      · rw [← e]; exact (hS.act _ (hX.2.2.bound _ h.curT hbd).1).2 hrm
      · exact absurd e hbd
    refine WP.spec_bind (sched.check_budget.all hA s a Q R h hB hX hSg hS hcsc hna hcA htmo) ?_
    rintro ⟨r, s1, a1⟩ h1
    exact (WP.spec_ok _).2 h1.1
  · step with sched.cur_sc.spec as ⟨c, ec⟩
    step with sporadic.sc_active.val as ⟨b1, eb1⟩
    split
    · rename_i hb1
      have hcA : L.cscW s ∈ Ac := (hS.act _ hX.2.2.cur).2 (by
        have := eb1 hb1; rwa [ec] at this)
      step with sched.consumed.spec as ⟨u⟩
      exact sched.charge_budget.all hA s a u false Q R h hB hX hSg hS hcsc hna hcA htmo
    · step with LawfulStore.cur_cpu_spec as ⟨cpu, cpu_post⟩
      subst cpu_post
      step with obj.node_set.spec as ⟨s2, e2⟩
      subst e2
      exact consumed0_bxi h hB hX hSg hS

end

end Fl4Proofs.P1

