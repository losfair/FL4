/-
P3 (DESIGN.md §9), scheduling contexts: **the current thread's own
timeout-fault send inside `charge_budget`** (KENTRY-PLAN kp2/kp4/kp5 (a):
`check_budget`'s charge with `can_timeout_fault = true` when the current
thread has an endpoint timeout handler and a non-round-robin SC).

Pieces (this module):

* P1: `sched.charge_head.ring` (the head charge's writes, the ring and the
  SC's `CONSUMED` word, factored out of ScChargeJ's `charge_budget.allF`),
  `charge_pre_post` (P1's `BlkOK` and a `Foot`-closed `G` after the head and
  the node's `CONSUMED` write), `rperiod_of_ring` (the head keeps the period
  word).
* Spec: `nkt_/pres_/lkm_/fk_chargeHead` (the head is an SC step);
  `ScOnly c σ σ'` (the kheap changes only at the SC `c`, keeping its size,
  bound thread, refill max, yield and call links) with its frame lemmas.
* `JTH`: the state inside `charge_budget` after the head charge and the
  consumed-time reset, "frames from the base" (as ScChargeH's `JHole`): `JAtZ`
  at the base (the kernel-entry state), FL4's writes from it in its `KFoot`,
  the spec state `ScOnly` from it, and what the send reads at the hole, with
  `InvBut` for the current thread in place of `Inv` (after the charge its SC
  is not released, so `Inv.rd` fails for it there: KENTRY-PLAN kp2).
* `JTH.tmoBlockJ`: `handle_timeout` of the current thread whose timeout
  handler's endpoint is idle or sending: XTopJointSendBlockG's
  `JAtZ.runTmoJ` tail for the current thread (no `set_thread_state` before),
  `JAtZ` after assembled from the base with the composite frame (`ScOnly`
  then the send's `BFrT`), `Inv` after by `InvBut.ik` and `inClassR`'s
  exemption of a sender with a timeout fault (l4v `valid_sender_sc_tcb_at`).
* `JTH.endTimesliceTmoJ`: `end_timeslice true` taking the timeout branch
  (non-round-robin SC, valid handler) on both sides, then `tmoBlockJ`.
* `JHole.chargeBudgetTmoJ`: `charge_budget used true` from a `JHole` in this
  case: the head (`charge_head_refinesK`, P1 `charge_head.ring`,
  `charge_pre_post`), the reset, `JTH`, `endTimesliceTmoJ`, then
  `JAtZ.reschedJ` and `JAtZ.reprogramJ`.
  Not covered: a timeout handler endpoint with waiting receivers (the
  timeout fault's transfer to a receiver for the current thread: an
  XTopJointFaultTmo `sendTmoRecvIJ`/`PJ` analogue from a `JTH`).
-/
import Fl4Proofs.P3.ScChargeH
import Fl4Proofs.P3.XTopJointSendBlockG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A} {Ac : Set U64}

/-- **The head charge's writes** (ScChargeJ's `charge_budget.allF`, first
part): the current SC's ring and its `CONSUMED` word; the ring stays
well-formed. -/
theorem sched.charge_head.ring (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hcS : L.cscW s ∈ Scs)
    (hW : RefillsWF st s (L.cscW s) (Z (L.cscW s))) {sc : U64} (hsc : sc = L.cscW s) (b : Bool) :
    (if b then do
      let b1 ← sporadic.is_round_robin st s sc
      let s3 ← if b1 then do
          let hi ← obj.Sc.refill_head st sc s
          let ti ← obj.Sc.refill_tail st sc s
          let h ← sporadic.get st s sc hi
          let t ← sporadic.get st s sc ti
          let i ← lift (core.num.U64.wrapping_add h.amount t.amount)
          let s4 ← sporadic.put st s sc hi { h with amount := i }
          sporadic.put st s4 sc ti { t with amount := 0#u64 }
        else sporadic.budget_check st ar s a used
      let i ← obj.Sc.consumed st sc s3
      let total ← lift (core.num.U64.wrapping_add i used)
      obj.Sc.set_consumed st sc s3 total
    else ok s) ⦃ s2 => WritesIn st s s2 (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) ∧ RefillsWF st s2 (L.cscW s) (Z (L.cscW s)) ⦄ := by
  subst hsc
  split
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

/-- **The head keeps the period word** (`PERIOD` = 0 is below the ring and
is not the `CONSUMED` word). -/
theorem rperiod_of_ring {s s2 : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hcS : L.cscW s ∈ Scs)
    (w2 : WritesIn st s s2 (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED)) :
    L.rperiod s2 (L.cscW s) = L.rperiod s (L.cscW s) := by
  obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
  obtain ⟨h8, -, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.PERIOD) (by simp [layout.sc.PERIOD])
  have hc := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  unfold LawfulStore.rperiod periodA
  refine w2.mem_eq ?_ ?_
  · unfold Aligned; rw [hv]; simp [layout.sc.PERIOD]; omega
  · rintro (h | h)
    · have := h.1; rw [hv] at this; simp [layout.sc.PERIOD] at this
    · have := congrArg UScalar.val h; rw [hv, hc] at this; simp [layout.sc.PERIOD, layout.sc.CONSUMED] at this

/-- **After the head and the node's `CONSUMED` write** (ScChargeJ's
`charge_budget.allF`, middle part): P1's `BlkOK` and a `Foot`-closed `G`. -/
theorem charge_pre_post {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) {s2 : S}
    (w2 : WritesIn st s s2 (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED))
    (wf2 : RefillsWF st s2 (L.cscW s) (Z (L.cscW s)))
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64) ∧
      G (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64) := by
  have hcS : L.cscW s ∈ Scs := hX.2.2.cur
  have hS2 := SCsOK.ringc h hS hX hcS w2 wf2
  obtain ⟨h2, hB2, hX2, hSg2, ea2, ec2, ecs2, f2⟩ := ring_bx h hB hX hSg hcS w2
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
  refine ⟨⟨⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3⟩, ?_⟩
  have W3 : WritesIn st s (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64) (ChgW st Scs Z s) := by
    obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
    obtain ⟨-, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hN2 := h2.nodes _ h2.cur
    have wn : WritesIn st s2 (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64)
        (fun b => b = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) :=
      writesIn_wr (nodeAt_aligned hN2 (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
    refine (w2.trans wn).mono fun b hb => ?_
    rcases hb with (hh | rfl) | rfl
    · exact Or.inl ⟨_, hcS, hh.inSC⟩
    · exact Or.inl ⟨_, hcS, by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
    · exact Or.inr (by rw [nodeAt_of_ksb w2.1, w2.2.1])
  exact hGF _ _ hG (Foot.of W3 fun b hb => by
    rcases hb with ⟨c, hc', hin⟩ | e
    · exact kw_sc hc' hin
    · rw [e]; exact kw_node h.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Spec Classical

noncomputable section

/-- The head charge changes no thread state (`NKT`). -/
theorem nkt_chargeHead (u : Ticks) : NKT (chargeHead u) := by
  unfold chargeHead refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
  repeat (any_goals (first | nkt_step | unfold getRefills | unfold getRefillHead | unfold getRefillTail))

theorem pres_chargeHead (f : Bool × Bool) (u : Ticks) : Pres f (chargeHead u) := by
  unfold chargeHead refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
  repeat (any_goals (first | pres_step | unfold getRefills | unfold getRefillHead | unfold getRefillTail | (apply pres_updateSchedContext; intro _ _; exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩)))

theorem lkm_chargeHead (W : ObjRef → Prop) (u : Ticks) : LKM W (chargeHead u) := by
  unfold chargeHead refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
  repeat (any_goals (first | lkm_step | unfold getRefills | unfold getRefillHead | unfold getRefillTail))

theorem fk_chargeHead (u : Ticks) : FKA (chargeHead u) := by
  unfold chargeHead refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
  repeat (any_goals (first | fk_step | fk_unf))

/-! ### An SC step at one SC (the head charge from the base) -/

/-- One object's change by the head charge: the SC `c`, keeping its size,
bound thread, refill max, yield and call links (the notification link kept or
cleared). -/
def ScChgO (c p : ObjRef) (o o' : KernelObject) : Prop :=
  p = c ∧ ∃ y z n, o = .schedContext y n ∧ o' = .schedContext z n ∧ z.scTcb = y.scTcb ∧
    z.scRefillMax = y.scRefillMax ∧ z.scYieldFrom = y.scYieldFrom ∧ z.scReplies = y.scReplies ∧
    (z.scNtfn = y.scNtfn ∨ z.scNtfn = none)

/-- **The kheap changes only at the SC `c`** (`ScChgO`). -/
def ScOnly (c : ObjRef) (σ σ' : State Unit) : Prop :=
  ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ ScChgO c p o o'

section
variable {c : ObjRef} {σ σ' : State Unit}

theorem ScOnly.othF (h : ScOnly c σ σ') {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o)
    (hn : ∀ y n, o ≠ .schedContext y n) : σ'.kheap p = some o := by
  rcases h p with e | ⟨o1, o2, h1, -, -, y, z, n, e1, -⟩
  · rw [e, hp]
  · rw [hp] at h1; cases h1; exact absurd e1 (hn y n)

theorem ScOnly.othB (h : ScOnly c σ σ') {p : ObjRef} {o : KernelObject} (hp : σ'.kheap p = some o)
    (hn : ∀ y n, o ≠ .schedContext y n) : σ.kheap p = some o := by
  rcases h p with e | ⟨o1, o2, -, h2, -, y, z, n, -, e2, -⟩
  · rw [← e, hp]
  · rw [hp] at h2; cases h2; exact absurd e2 (hn z n)

theorem ScOnly.scF (h : ScOnly c σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ.kheap p = some (.schedContext y n)) : ∃ z, σ'.kheap p = some (.schedContext z n) ∧
      z.scTcb = y.scTcb ∧ z.scRefillMax = y.scRefillMax ∧ z.scYieldFrom = y.scYieldFrom ∧
      z.scReplies = y.scReplies ∧ (z.scNtfn = y.scNtfn ∨ z.scNtfn = none) := by
  rcases h p with e | ⟨o1, o2, h1, h2, -, y1, z, n1, e1, e2, k1, k2, k3, k4, k5⟩
  · exact ⟨y, by rw [e, hp], rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1; cases e1; subst e2
    exact ⟨z, h2, k1, k2, k3, k4, k5⟩

theorem ScOnly.scB (h : ScOnly c σ σ') {p : ObjRef} {z : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext z n)) : ∃ y, σ.kheap p = some (.schedContext y n) ∧
      z.scTcb = y.scTcb ∧ z.scRefillMax = y.scRefillMax ∧ z.scYieldFrom = y.scYieldFrom ∧
      z.scReplies = y.scReplies := by
  rcases h p with e | ⟨o1, o2, h1, h2, -, y, z1, n1, e1, e2, k1, k2, k3, k4, -⟩
  · exact ⟨z, by rw [← e, hp], rfl, rfl, rfl, rfl⟩
  · rw [hp] at h2; cases h2; cases e2; subst e1
    exact ⟨y, h1, k1, k2, k3, k4⟩

theorem ScOnly.tcbF (h : ScOnly c σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    σ'.kheap p = some (.tcb x) := h.othF hp (fun _ _ e => by cases e)

theorem ScOnly.tcbB (h : ScOnly c σ σ') {p : ObjRef} {x : Tcb} (hp : σ'.kheap p = some (.tcb x)) :
    σ.kheap p = some (.tcb x) := h.othB hp (fun _ _ e => by cases e)

theorem ScOnly.szKeep (h : ScOnly c σ σ') : SzKeep σ σ' := fun _ z n hp => by
  obtain ⟨y, hy, -⟩ := h.scB hp; exact ⟨y, hy⟩

theorem ScOnly.ykeep (h : ScOnly c σ σ') : YKeep σ σ' :=
  ⟨fun p x hp => ⟨x, h.tcbF hp, rfl⟩, fun p y n hp => by
    obtain ⟨z, hz, -, -, k, -⟩ := h.scF hp; exact ⟨z, hz, k⟩, fun p z n hp => by
    obtain ⟨y, hy, -, -, k, -⟩ := h.scB hp; exact ⟨y, hy, k⟩⟩

theorem ScOnly.mcpKeep (h : ScOnly c σ σ') : McpKeep σ σ' := fun p x hp => ⟨x, h.tcbF hp, rfl⟩

theorem ScOnly.bufKeep (h : ScOnly c σ σ') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => ⟨x, h.tcbF hp, rfl⟩

theorem ScOnly.kback (h : ScOnly c σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h o with e | ⟨ko, ko'', h1, h2, -, y, z, n, e1, e2, -⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2; subst e1 e2
    refine ⟨_, h1, ?_, ?_, ?_, ?_, fun _ => ⟨y, n, rfl⟩, ?_⟩ <;> rintro ⟨_, e⟩ <;> cases e

theorem ScOnly.ksz (h : ScOnly c σ σ') : KSz σ σ' := by
  intro o ko' ho
  rcases h o with e | ⟨ko, ko'', h1, h2, -, y, z, n, e1, e2, -⟩
  · exact ⟨ko', by rw [← e, ho], rfl⟩
  · rw [ho] at h2; cases h2; subst e1 e2
    exact ⟨_, h1, rfl⟩

theorem ScOnly.ksub (h : ScOnly c σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, h.othB hc (fun _ _ e => by cases e), hw⟩,
    fun u hu => ⟨u, h.tcbB hu⟩, fun hn => ?_⟩
  rcases h o with e | ⟨ko, ko'', h1, -, -⟩
  · rw [e, hn]
  · rw [hn] at h1; cases h1

theorem ScOnly.khrb (h : ScOnly c σ σ') : KhRB σ σ' := by
  intro p o' hp
  rcases h p with e | ⟨o, o'', h1, h2, -, y, z, n, e1, e2, -⟩
  · exact ⟨o', by rw [← e, hp], ObjRB.refl o'⟩
  · rw [hp] at h2; cases h2; subst e1 e2
    exact ⟨_, h1, by unfold ObjRB; refine ⟨fun y' e => ?_, fun y' t' e => ?_⟩ <;> cases e⟩

theorem ScOnly.prio (h : ScOnly c σ σ') (u : ObjRef) : prioOf σ' u = prioOf σ u := by
  unfold Sched.prioOf
  rw [tcbsOf_eq, tcbsOf_eq]
  rcases h u with e | ⟨o, o', h1, h2, -, y, z, n, rfl, rfl, -⟩
  · rw [e]
  · first | (rw [h1, h2]; done) | (rw [h1, h2]; rfl)

theorem ScOnly.ipcFr (h : ScOnly c σ σ') : IpcFrKeep σ σ' := by
  refine ⟨fun t x' hx => Or.inr ⟨x', h.tcbB hx, rfl, rfl⟩, fun p vms hp => h.othF hp (fun _ _ e => by cases e),
    fun p vms hp => h.othB hp (fun _ _ e => by cases e)⟩

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- **The state inside `charge_budget` after the head charge and the consumed
time reset** (module docstring): `JAtZ` at the base `(s0, a0, σ0)` (the
kernel-entry state), FL4's writes from the base in its `KFoot`, the spec
state an SC step at the current SC from the base (`ScOnly`) with the same
scheduler fields and no consumed time, and at `(s, a, σ)` what the
timeout-fault send reads: `XTopAt`, the buffer words, `NSC`, `Inv` but for
the current thread (`InvBut`: its SC is not released after the charge),
`ActIdle`, `BlockedScActive`, `CurOwnW`, `IpcSorted`, P1's `BlkOK` and the
node-0 debug word. -/
structure JTH (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  j0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0
  ws : P1.WritesIn st s0 s (KFoot st Z.T Z.N Z.C Z.c s0 σ0)
  xtop : XTopAt (L := L) AR Z s a σ
  buf : BufWordRel Z.T (L.mem s) σ
  nsc : NSC Z.N Z.C σ
  inv : InvBut σ σ.curThread
  act : ActIdle σ
  bsa : BlockedScActive σ
  own : CurOwnW Z.T Z.C σ
  isorted : IpcSorted σ
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s
  dbg : L.mem s (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) = L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS)
  /-- Every debug word kept from the base (KENTRY-PLAN g2i). -/
  dbgK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s
  ksc : ScOnly σ0.curSc σ0 σ
  ct : σ.curThread = σ0.curThread
  idle : σ.idleThread = σ0.idleThread
  csc : σ.curSc = σ0.curSc
  rel : σ.releaseQueue = σ0.releaseQueue
  cdt : σ.cdt = σ0.cdt
  orig : σ.isOriginalCap = σ0.isOriginalCap
  arch : σ.archState = σ0.archState
  isc : σ.idleSc = σ0.idleSc
  cons : σ.consumedTime = 0

set_option maxHeartbeats 64000000 in
/-- **The current thread's timeout fault blocking it on its timeout
handler's endpoint, at the state inside `charge_budget`** (module docstring):
XTopJointSendBlockG's `JAtZ.runTmoJ` tail for the current thread (no
`set_thread_state` before), started at a `JTH` state; `JAtZ` after,
assembled from the base `JAtZ` with the composite frame (the head's
`ScOnly`, then the send's `BFrT`); `Inv` after from `InvBut` at the hole by
`InvBut.ik` and `inClassR`'s exemption of a sender with a timeout fault. -/
theorem JTH.tmoBlockJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) {t : U64} (ht : t ∈ Z.T)
    (htc : t.bv = σ.curThread) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrr : x.tcbState = .running ∨ x.tcbState = .restart)
    {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : x.tcbTimeoutHandler = .endpointCap p bd r)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe)
    (hres : σ.schedulerAction = .resumeCurThread) (hnq : NotQueued σ t.bv) (hidt : σ.idleThread ≠ t.bv)
    (b : U64) :
    faults.handle_timeout st arI s a t (error.Fault.Timeout b) ⦃ res => ∃ z ∈
      (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ).1,
      ∃ (V : XVs) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D' res.1 res.2 z.2 ⦄ := by
  have J := Hj.j0
  have hO := Hj.ksc
  have hP0 := J.ip
  have hks0 : L.ksb s = L.ksb s0 := Hj.ws.1
  have hI0 := J.xtop.irelK J.ks J.buf
  have hI' := Hj.xtop.irelK (by rw [hks0]; exact J.ks) Hj.buf
  have hI : IRel st Z.th σ0.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
    rw [← Hj.arch]; exact hI'
  have hS := Hj.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have hk0 : σ0.kheap t.bv = some (.tcb x) := hO.tcbB hk
  have hD : t ∉ D := fun h => by
    have hd := J.jcov.dead t h
    have h1 := (hd.1 htH).1
    obtain ⟨x1, hk1, hTR⟩ := hI0.1.tcb t ht
    rw [hk0] at hk1; cases hk1
    have hst := hTR.st
    rw [← stA_tStA, h1] at hst
    unfold sched.TS_INACTIVE at hst
    rcases hrr with e | e <;> rw [e] at hst <;> simp [tsCode] at hst
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ0.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  -- the handler cap at the base, its endpoint, the cover
  obtain ⟨⟨G0, hB0⟩, -⟩ := hI0.2.1
  have hth0 : Z.th t = some .tcb := hB0.tcbT hk0
  obtain ⟨xh, cv, hkh, hcv, hca⟩ := hB0.2.1.1.timeoutCap hth0
  rw [hk0] at hkh; cases hkh
  have habs := hca.2
  rw [hth] at habs
  obtain ⟨ptr, bdg, sd, rv, g, gr, rfl⟩ : ∃ ptr bdg sd rv g gr, cv = .Endpoint ptr bdg sd rv g gr := by
    cases cv <;> simp [absCap] at habs; exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs
  obtain ⟨hp, hbd, hr⟩ := habs
  subst hp hbd hr
  have hAS : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 4) := ⟨t, rfl, Or.inr ⟨hth0, 4, by decide, rfl⟩⟩
  have hcv' : capAt (L.mem s0) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 4)) = ok (.Endpoint ptr bdg sd rv g gr) := by
    rw [tcbSlot4_eq]; exact hcv
  have hpE : ptr ∈ Z.E := J.slotE hAS hcv'
  obtain ⟨xe, hke0, -⟩ := hI0.1.ep ptr hpE
  have hke : σ.kheap ptr.bv = some (.endpoint xe) := hO.othF hke0 (fun _ _ e => by cases e)
  have hcbe : Endp.CanBlock false xe := hcb xe hke
  have hpt : ptr.bv ≠ t.bv := fun e => by rw [e, hk] at hke; cases hke
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s0 _) hAS.isSlot hcv' (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  -- the FL4 step from the base to the hole (`CnStep`)
  have hC1 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0 s σ :=
    ⟨Hj.ws.mono fun b hb => Or.inl (Or.inl hb), SzKeepC.of hO.szKeep⟩
  -- `handle_timeout`: the handler cap at the hole
  obtain ⟨⟨G6, hB6⟩, -⟩ := hI.2.1
  obtain ⟨xh6, cv6, hkh6, hcv6, hca6⟩ := hB6.2.1.1.timeoutCap (hB6.tcbT hk)
  rw [hk] at hkh6; cases hkh6
  have habs6 := hca6.2
  rw [hth] at habs6
  unfold faults.handle_timeout
  rw [tcb_slot_timeout]
  apply ok_bind_spec
  rw [slot_cap_eq, hcv6]
  apply ok_bind_spec
  cases cv6
  case Endpoint ptr' bdg' sd' rv' g' gr' =>
    simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs6
    obtain ⟨hp', hbd', hr'⟩ := habs6
    obtain rfl : ptr = ptr' := (P1.eq_of_bv hp').symm
    obtain rfl : bdg = bdg' := (P1.eq_of_bv hbd').symm
    have hg : g' = g := by have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrant ∈ R)) hr'; simpa [rights_grant] using this
    have hgr : gr' = gr := by
      have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrantReply ∈ R)) hr'; simpa [rights_grantReply] using this
    obtain rfl : g = g' := hg.symm
    obtain rfl : gr = gr' := hgr.symm
    refine WP.spec_bind (Pₘ := fun r : Bool × S × A => ∃ z ∈ (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ).1,
      ∃ (V : XVs) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D' r.2.1 r.2.2 z.2) ?_ ?_
    swap
    · rintro ⟨b0, s2, a2⟩ hr0
      exact (WP.spec_ok _).2 hr0
    unfold faults.send_fault_ipc
    dsimp only
    -- `set_fault`
    set x2 : Fl4Spec.Tcb := { x with tcbFault := some (.timeout b.bv) } with hx2
    set σf := updK σ t.bv (.tcb x2) with hσf
    refine WP.spec_bind (WP.spec_and (WP.spec_and (set_fault_timeout_top hP0 hI ht hk b)
      (set_fault_timeout_eq s t b)) (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s t (error.Fault.Timeout b)
        (t0 := t) Hj.blk htH (fun _ h => by simp at h) ?hcb6)
        (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
          (Es := P1.EH H) s t (error.Fault.Timeout b) hTH htH))) ?_
    case hcb6 =>
      obtain ⟨Q, R0, hcq, hs⟩ := hS.lists
      obtain ⟨x7, hk7, hTR7⟩ := hI.1.tcb t ht
      rw [hk] at hk7; cases hk7
      have hv7 : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR7.st
      have hrr' : L.mem s (P1.stA t) = sched.TS_RUNNING ∨ L.mem s (P1.stA t) = sched.TS_RESTART := by
        rcases hrr with e | e
        · left; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RUNNING; rfl
        · right; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RESTART; rfl
      obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb t ht
      rw [hk] at hkt6; cases hkt6
      have hst6 : L.mem s (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hsct6.symm.trans hxsc)).2
      obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
      rw [hky] at hky'; cases hky'
      have hmx : (L.rmax s (L.mem s (scA t))).val ≠ 0 := by rw [hst6]; exact hy'.rmax_ne hya
      refine ⟨htH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hrr' with h | h <;> rw [h]
        · exact P1.not_blocked_running
        · exact P1.not_blocked_restart
      · rcases hrr' with h | h <;> rw [h]
        · exact P1.running_ne.1
        · exact P1.restart_ne.1
      · by_contra hq'
        have hm := (hcq.queued t ht).1 hq'
        exact hnq.1 0 _ (by rw [hs.rq _ (hcq.prio t ht), mem_map_bv]; exact hm)
      · by_contra hq'
        have hm := (hcq.released t ht).1 hq'
        exact hnq.2 (by rw [hs.rel, mem_map_bv]; exact hm)
      · exact actionW_ne_of hS ht (by rw [hres]; intro e; cases e)
      · intro h
        have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
          unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
        exact hidt (by rw [hs.idleTh, ← ei, h])
      · intro hbd
        obtain ⟨⟨Q', R', h0⟩, hBd, hXi, hSc, hSg⟩ := Hj.blk
        obtain ⟨hiS, -, -⟩ := hXi.2.2.bound _ htH hbd
        exact (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))
    rintro s7 ⟨⟨⟨hsp7, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩
    have hkf : σf.kheap t.bv = some (.tcb x2) := by simp [hσf, updK]
    have hkfp : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := by
      intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']
    have hkef : σf.kheap ptr.bv = some (.endpoint xe) := by rw [hkfp _ hpt]; exact hke
    -- the FL4 step of `set_fault`
    have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s7 σf := by
      refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x2) (fun q hq' => by simp [hσf, updK, hq']) hkf)⟩
      subst hs7
      have w := (((writesIn_wr (st := st) (s := s) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
        (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
        (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
      refine w.mono fun w0 hw0 => ?_
      have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = t.val + K := by
        rcases hw0 with ((h | h) | h) | h <;> subst h
        · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
        · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
        · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
        · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
      obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
      exact Or.inl (Or.inr ⟨t, ht, K, k1, k2, k3, k4, k5, k6⟩)
    -- the spec's blocking send at `σf`
    have hprf : ∀ u, Sched.prioOf σf u = Sched.prioOf σ u := by
      intro u
      by_cases hut : u = t.bv
      · subst hut; exact (prioOf_eq hkf).trans (prioOf_eq hk).symm
      · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq, hkfp u hut]
    have hrun : Fl4Spec.runnable x.tcbState = true := by rcases hrr with e | e <;> rw [e] <;> rfl
    have htq : t.bv ∉ xe.epQueue :=
      Endp.not_queued hI.1.toE ht hk (by rcases hrr with e | e <;> rw [e] <;> exact ⟨by decide, by decide⟩) ptr hpE xe hke
    have hqm : ∀ u ∈ xe.epQueue, ∃ z, σf.kheap u = some (.tcb z) := fun u hu => by
      obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hke0).2 u hu
      exact ⟨z, by rw [hkfp u (fun e => htq (e ▸ hu)), hO.tcbF hz]⟩
    have hsrt0 : SortedQ σ xe.epQueue := (Hj.isorted.1 _ _ hke)
    obtain ⟨σ', heq, F0, hik0, ⟨ds, hkt'⟩, -, hact', hact'', hsrt⟩ :=
      sendIpcBlock_eq hkf hkef hcbe htq hqm hrun (hsrt0.congr fun u _ => hprf u) false bdg.bv g gr false
    -- FL4's blocking send
    have hIS : IpcSorted σf := QPK.QPS.sorted (QPK.qps_upd (ko := .tcb x2) hk rfl) Hj.isorted
    obtain ⟨⟨Q0, R0, h0⟩, hB0', hX0, hS0, hSg0⟩ := hblk7
    have hst0 : L.epState s7 ptr = 0#u64 ∨ L.epState s7 ptr = 1#u64 := by
      have hx := hI7.1.toE.at_ep hpE hkef
      rw [epState_eq]
      cases xe with
      | idleEP => exact Or.inl hx.1
      | sendEP q => exact Or.inr hx.1
      | recvEP q => simp [Endp.CanBlock] at hcbe
    have hnb : tsCode x2.tcbState ≠ 3 ∧ tsCode x2.tcbState ≠ 4 := by
      show tsCode x.tcbState ≠ 3 ∧ tsCode x.tcbState ≠ 4
      rcases hrr with e | e <;> rw [e] <;> exact ⟨by decide, by decide⟩
    have hnn : ∀ m, x2.tcbState ≠ .blockedOnNotification m := fun m h => by
      have h' : x.tcbState = .blockedOnNotification m := h
      rcases hrr with e | e <;> rw [e] at h' <;> cases h'
    have p1f : endpoint.send_ipc st arI s7 a true false bdg g gr false t ptr ⦃ s' _ => P1.Foot st (P1.Heap.tcbs H) Cs
        (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s' ⦄ :=
      P1.endpoint.send_ipc.blockFoot arI s7 a true false bdg g gr false t ptr h0 (fun _ => hcb7) hHe hst0
    refine WP.spec_bind (WP.spec_and (WP.spec_and (send_ipc_blockF (ar := arI) hP0 s7 a σf hI7 ht hkf hnb hnn hpE hkef
      hcbe (Sched.qSorted_of_spec (L := L) hI7.1.toE hI7.1.toN hT hIS ptr (Or.inl hpE)) false bdg g gr false)
      (P1.endpoint.send_ipc.block arI s7 a true false bdg g gr false t ptr Q0 R0 h0 hB0' hX0 hS0 hSg0
        (fun _ => hcb7) hHe hst0))
      p1f) ?_
    rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0', h0eq, hIR, hW3⟩, hbk⟩, hfoot3⟩
    simp only [WP.uncurry'_pair] at ea hbk hfoot3 hIR hW3
    subst a'
    obtain rfl : σ' = σ0' := by
      have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
      exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
    apply (WP.spec_ok _).2
    -- the spec's outcome
    have hz : ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
        (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
        (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) false t.bv ptr.bv
        (updK σ t.bv (.tcb { x with tcbFault := some (.timeout b.bv) }))).1 := by
      rw [rights_grant, rights_grantReply]
      show ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr false t.bv ptr.bv σf).1
      rw [heq]; exact Set.mem_singleton _
    refine ⟨((), σ'), handleTimeout_mem hk hth _ hz, ?_⟩
    -- the frame from the hole
    have hkt3 : σ'.kheap t.bv =
        some (.tcb { x with tcbState := .blockedOnSend ptr.bv ds, tcbFault := some (.timeout b.bv) }) := hkt'
    have hsk : Sk σ σ' := (show Sk σ σf from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans F0.sk
    have F : BFrT t.bv ptr.bv σ σ' := by
      refine ⟨hsk, fun q => ?_⟩
      by_cases hqt : q = t.bv
      · subst hqt
        exact Or.inr ⟨_, _, hk, hkt3, Or.inl ⟨x, ptr.bv, ds, some (.timeout b.bv), rfl, rfl, rfl⟩⟩
      · rcases F0.kh q with e | ⟨o, o', h1, h2, hc⟩
        · exact Or.inl (e.trans (hkfp q hqt))
        · rw [hkfp q hqt] at h1
          rcases hc with ⟨_, _, _, _, _, e3, -⟩ | ⟨x1, y1, rfl, rfl, e3⟩
          · exact absurd e3 hqt
          · exact Or.inr ⟨_, _, h1, h2, Or.inr ⟨x1, y1, rfl, rfl, e3⟩⟩
    -- the FL4 footprint from the base
    have hC3 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf s' σ' := ⟨hW3, SzKeepC.of F0.szKeep⟩
    have hW : P1.WritesIn st s0 s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0) :=
      ((hC1.trans hC2).trans hC3).1
    have hfoot := P1.Foot.trans hfoot7 hfoot3
    have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
    -- the composite frame from the base
    have e_ct : σ'.curThread = σ0.curThread := F.sk.ct.trans Hj.ct
    have e_idle : σ'.idleThread = σ0.idleThread := F.sk.idle.trans Hj.idle
    have e_csc : σ'.curSc = σ0.curSc := F.sk.csc.trans Hj.csc
    have e_cdt : σ'.cdt = σ0.cdt := F.sk.cdt.trans Hj.cdt
    have e_orig : σ'.isOriginalCap = σ0.isOriginalCap := F.sk.orig.trans Hj.orig
    have e_arch : σ'.archState = σ0.archState := F.sk.arch.trans Hj.arch
    have e_isc : σ'.idleSc = σ0.idleSc := F.sk.isc.trans Hj.isc
    have hszc : SzKeep σ0 σ' := SzKeep.trans' hO.szKeep F.szKeep
    have hykc : YKeep σ0 σ' := hO.ykeep.trans F.ykeep
    have hmkc : McpKeep σ0 σ' := hO.mcpKeep.trans F.mcpKeep
    have hbkc : BufKeep σ0 σ' := BufKeep.trans hO.bufKeep F.bufKeep
    have hkbc : KBack σ0 σ' := KBack.trans' hO.kback F.kback
    have hkszc : KSz σ0 σ' := KSz.trans hO.ksz F.ksz
    have hksubc : KSub σ0 σ' := KSub.trans hO.ksub F.ksub
    have hrbc : KhRB σ0 σ' := KhRB.trans hO.khrb F.khrb
    have hfkc : IpcFrKeep σ0 σ' := hO.ipcFr.trans F.ipcFr
    have haoc : ∀ q ao, σ0.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao) := fun q ao h =>
      F.othF (hO.othF h (fun _ _ e => by cases e)) (fun _ e => by cases e) (fun _ e => by cases e)
    have ck1 : ∀ q y n, σ0.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
        y'.scReplies = y.scReplies := fun q y n hq => by
      obtain ⟨z, hz, -, -, -, hr, -⟩ := hO.scF hq
      exact ⟨z, F.scF hz, hr⟩
    have ck2 : ∀ q x, σ0.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc :=
      fun q x hq => ⟨x, F.replyF (hO.othF hq (fun _ _ e => by cases e)), rfl⟩
    -- the assembly (as `JAtZ.runTmoJ`)
    have hAR' : AR a σ0.archState.x64CurrentCr3 := by
      have h := Hj.xtop.fin.1.1.2.2.2.2.2.2; rw [Hj.arch] at h; exact h
    have hF : IFrame (L := L) Z.th s0 s' := IRel.iframe_of hI0 hW fun b hb => CnW.oobj hI0.2.2.1 hb
    have hIR' : IRel st Z.th σ0.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' := hIR
    obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR' hAR' hF.1 e_cdt e_orig hksubc hF.2
    have hks : L.ksb s' = L.ksb s0 := hF.2
    obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
    have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
      J.call.frame k3 k4 (fun q _ y n hy => ck1 _ y n hy) (fun d _ x hx => ck2 _ x hx)
    have hRP' := J.rp.frame hks hszc
    have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
      intro d hd hfd
      obtain ⟨y, hy, hyt⟩ := hfd
      obtain ⟨e1, e2⟩ := k4 d hd
      obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, hO.othB (F.replyB hy) (fun _ _ e => by cases e), hyt⟩
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
    have eN : L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS :=
      P1.nodeAt_of_ksb hks0 _ _
    have hDbg : L.mem s' (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
        L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
      rw [← Hj.dbg]
      exact hfoot.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW Hj.blk J.kern.cs0 (Or.inl (by rw [eN]; exact hk))
    have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
    have hact3 : σ'.schedulerAction = .chooseNewThread := hact'' (by rw [hσf]; exact htc) (by rw [hσf]; exact hres)
    have hAI3 : ActIdle σ' :=
      ⟨fun u hu => (by rw [hact3] at hu; cases hu), F.idleOK Hj.act.2 hidt⟩
    have hrun3 : CurRunM σ' := Or.inl (by rw [hact3]; intro e; cases e)
    -- the dead: the thread is not dead; the endpoint leaves the dead set
    have hdead : ∀ q ∈ D \ {ptr}, DeadP (L := L) H s' q := fun q hq => by
      have hd := J.jcov.dead q hq.1
      have hqt : q.bv ≠ t.bv := fun h => hD (by rw [← P1.eq_of_bv h]; exact hq.1)
      have hqe : q.bv ≠ ptr.bv := fun h => hq.2 (P1.eq_of_bv h)
      refine J.deadP_keep hS3 hIR.1
        (fun x hx h0 => ⟨_, F.tcbO hqt (hO.tcbF hx), rfl, rfl, Or.inl rfl⟩) (fun x hx => ?_)
        (fun x hx => ⟨x, F.ntfnF (hO.othF hx (fun _ _ e => by cases e)), Or.inl rfl, rfl, Or.inl rfl⟩)
        (fun x hx => ⟨x, F.replyF (hO.othF hx (fun _ _ e => by cases e)), rfl⟩)
        (fun x n hx => by
          obtain ⟨z, hz, k1', -, -, -, k5'⟩ := hO.scF hx
          exact ⟨z, F.scF hz, Or.inl k1', k5'⟩)
        (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) e_idle hAI3.1
        (J.yld.frame k2 hykc) (hykc.dk q.bv) hd
      obtain ⟨y, hy, hc'⟩ := F.epF (hO.othF hx (fun _ _ e => by cases e))
      rcases hc' with rfl | e1
      · exact hy
      · exact absurd e1 hqe
    have hidl := J.idleW_keep hS3 e_idle e_isc
    have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hszc q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
    have hkern := J.kern_keep hks hW.2.1 hS3 e_ct e_csc (fun sl h => Or.inl (by rw [← e_orig]; exact h))
      (by rw [e_arch]) haoc hDbg (D' := D \ {ptr})
    have hRR' := J.rrecv.frame k4 hrbc
    have hjcov : JCovD (L := L) Z.th H Z.G (D \ {ptr}) Cs s' := by
      obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
      have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
      exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩)
        (fun q hq _ => hdead q hq)
        (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
        (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
    -- `Inv` (`InvBut.ik` at the hole; the thread a sender with a timeout fault, `inClassR`)
    have hts6 : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some (.timeout b.bv) }) t.bv σ =
        ({((), σf)}, False) := Notif.threadSet_eq _ hk
    have hik : IK t.bv σ σ' :=
      ((ikm_threadSet (t := t.bv) (p := t.bv)
        (g := fun tcb => { tcb with tcbFault := some (.timeout b.bv) })
        fun _ => ⟨rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩).of_eq hts6).trans hik0
    have hIt : InvBut σ t.bv := by rw [htc]; exact Hj.inv
    obtain ⟨hIB, -⟩ := hIt.ik hnq hik
    have I3 : Inv σ' := hIB.inv fun x' hx' hc => by
      rw [hkt3] at hx'; cases hx'
      exact (inClassR.notTmoS hc ptr.bv ds b.bv rfl rfl).elim
    -- `BlockedScActive`: an SC bound to the thread is its SC, active
    have hscA : ∀ q y1 n1, σ.kheap q = some (.schedContext y1 n1) → y1.scTcb = some t.bv →
        Fl4Spec.scActive y1 = true := by
      intro q y1 n1 hq' hyt'
      obtain ⟨xu, hku, hxu⟩ : ∃ xu : Fl4Spec.Tcb,
          σ.kheap t.bv = some (.tcb xu) ∧ xu.tcbSchedContext = some q := by
        obtain ⟨y0, hy0, ey1, -, -, -⟩ := hO.scB hq'
        obtain ⟨c, hcC, eq⟩ := J.obj.sc q y0 n1 hy0
        subst eq
        obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        have hc0 := J.c0 c hcC
        have hcS : c ∈ P1.Heap.scs H := ⟨_, (hJ.sc c y0 n1 hc0 hy0).2⟩
        obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of J.xtop.fin.1.1.1 J.blk.2.2.1 J.tcbs_eq.1.symm hcC hcS hc0 hy0
          (by rw [← ey1]; exact hyt')
        exact ⟨xu, hO.tcbF hku, hxs⟩
      rw [hk] at hku; cases hku
      have e1 : q = sc.bv := Option.some.inj (hxu.symm.trans hxsc)
      rw [e1, hky] at hq'; cases hq'
      exact hya
    have hoff : OffOK σ' := fun h0 => absurd h0 (by rw [F.sk.cons, Hj.cons]; decide)
    have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {ptr}) s' σ' :=
      ⟨hCR', hRF', hRR', J.yld.frame k2 hykc, J.mcp.frame k1 hmkc, J.buf.frame kb hbkc, hRP',
        J.apart.sc_frame hks hszc, hjpl, hjcov, hkern,
        J.cnW_utc hW hF.1 e_cdt e_orig e_arch hDbg, F.nsc Hj.nsc, I3, Or.inl hact3, F.own Hj.own, hoff,
        hAI3, F.bsa Hj.bsa hscA, F.isorted Hj.isorted fun y1 hy1 => (hsrt y1 hy1).congr fun u _ => (hprf u).symm,
        hrun3, hblk⟩
    have hC0 := JCs.same J hF.1 hkszc
    have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
    exact ⟨Z.vs, D \ {ptr}, J.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) e_arch haoc hszc
      hF.1 hkbc hfkc hCs R (Hj.dbgK.trans (P1.Foot.dbgKeep Hj.blk (by first | exact fun _ h => h | exact Set.empty_subset _) hfoot)) e_orig
      (XTopAt.idleW_eqS J.xtop hX3 e_idle) (J.zD_diffE hpE)⟩
  all_goals simp [absCap] at habs6

set_option maxHeartbeats 16000000 in
/-- **`end_timeslice` with `can_timeout_fault = true` at a `JTH` state, the
current thread with an endpoint timeout handler on an idle or sending
endpoint and a non-round-robin SC**: both sides take the timeout-fault branch
(`handle_timeout` of the current thread with the SC's badge), then
`JTH.tmoBlockJ`. -/
theorem JTH.endTimesliceTmoJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) {t : U64} (ht : t ∈ Z.T)
    (htc : t.bv = σ.curThread) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrr : x.tcbState = .running ∨ x.tcbState = .restart)
    {sc : U64} (hsc : sc ∈ Z.C) (hcs : σ.curSc = sc.bv) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) (hper : y.scPeriod ≠ 0)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : x.tcbTimeoutHandler = .endpointCap p bd r)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe)
    (hres : σ.schedulerAction = .resumeCurThread) (hnq : NotQueued σ t.bv) (hidt : σ.idleThread ≠ t.bv) :
    sched.end_timeslice st arI s a true ⦃ res => ∃ z ∈ (Fl4Spec.endTimeslice (Z := Unit) true σ).1,
      ∃ (V : XVs) (D' : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D' res.1 res.2 z.2 ⦄ := by
  have J := Hj.j0
  have hS := Hj.xtop.fin.1.1.1
  have hR := Hj.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have ect : nodeW st s Z.c layout.node.CUR_THREAD = t := P1.eq_of_bv (by rw [← hs.curThread]; exact htc.symm)
  have ecs : nodeW st s Z.c layout.node.CUR_SC = sc := P1.eq_of_bv (by rw [← hs.curSc]; exact hcs)
  obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
  rw [hky] at hky'; cases hky'
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th t = some .tcb := (hJ.tcb _).2 (J.zH.1 _ ht)
  have hvm : x.tcbState ≠ .runningVM := by rcases hrr with e | e <;> rw [e] <;> intro h <;> cases h
  -- the spec: the timeout-fault branch
  have hspec : Fl4Spec.endTimeslice (Z := Unit) true σ =
      Fl4Spec.handleTimeout t.bv (.timeout (L.mem s (scW sc 48#u64)).bv) σ := by
    unfold Fl4Spec.endTimeslice
    rw [nd_gets_bind, hcs, nd_bind_one (isRoundRobin_eq hky), nd_gets_bind, ← htc,
      nd_bind_one (getThreadState_eq hk)]
    simp only [hvm, ↓reduceIte]
    rw [nd_bind_one (Endp.isValidTimeoutHandler_eq hk), hth, if_pos, nd_bind_one (getSchedContext_eq hky),
      hy'.badge]
    simp [Fl4Spec.isEpCap]
    exact hper
  -- FL4: the reads
  have hval := hval_of_rel Hj.xtop.rel.1 Hj.xtop.rel.2.1.1 hthc s σ (TmoKeep.refl _ _ _)
  obtain ⟨tx, hkt, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have hst := (hR.at_tcb ht hk).st
  have hnvm : (L.mem s (tStA t) != sched.TS_RUNNING_VM) = true := by
    have e8 : sched.TS_RUNNING_VM = 8#u64 := by unfold sched.TS_RUNNING_VM; rfl
    rw [bne_iff_ne, e8]
    intro e
    rw [e] at hst
    rcases hrr with e' | e' <;> rw [e'] at hst <;> simp [tsCode] at hst
  unfold sched.end_timeslice
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur, ecs] at hsc'
  rw [hc.cur, ect] at hct'
  subst hsc' hct'
  step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
  have hrr0 : rr = false := by
    rw [hrr']
    apply decide_eq_false
    intro e
    exact hper (by rw [hy'.period, e]; rfl)
  subst hrr0
  step with Notif.obj.Tcb.state.spec as ⟨i, hi⟩
  rw [hi, if_pos hnvm]
  refine WP.spec_bind hval ?_
  intro v hv
  have hv' : v = true := by
    rw [Endp.isValidTimeoutHandler_eq hk, hth] at hv
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hv).1)).1).symm
  subst hv'
  simp only [↓reduceIte, Bool.false_eq_true]
  step with obj.Sc.badge.spec' as ⟨bd', hbd'⟩
  subst hbd'
  refine WP.spec_mono (Hj.tmoBlockJ ht htc hk hrr hsc hxsc hky hya hth hcb hres hnq hidt _) ?_
  rintro res ⟨z, hz, V, D', J'⟩
  exact ⟨z, by rw [hspec]; exact hz, V, D', J'⟩


set_option maxHeartbeats 64000000 in
/-- **`charge_budget` with `can_timeout_fault = true` from a `JHole`, the
current thread's timeout fault blocking it** (module docstring): the current
thread (`Running` or `Restart`, not queued, the action `ResumeCurThread`) has
an endpoint cap as its timeout handler whose endpoint is idle or sending, and
its SC is not round-robin. The head charge at the hole (SchedRel-level
`charge_head_refinesK`, P1's `charge_head.ring`/`charge_pre_post`), the
consumed-time reset, the `JTH` state there (`ScOnly` from the base), then
`end_timeslice` (`JTH.endTimesliceTmoJ`), `reschedule_required`
(`JAtZ.reschedJ`) and the reprogram flag (`JAtZ.reprogramJ`) at `J`. -/
theorem JHole.chargeBudgetTmoJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hres : σ.schedulerAction = .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe) (used : U64) :
    sched.charge_budget st arI s a used true ⦃ res => ∃ z ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv true σ).1,
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' res.1 res.2 z.2 ⦄ := by
  have J := Hh.j0
  obtain ⟨hK0, hsok0, hlk0, hfk0, ekh, ect0, eact0, eidle0, earch0, erel0, -, hbsaσ⟩ := Hh.sfacts
  obtain ⟨ms0, tm0, cn0, -, eσ⟩ := Hh.spec
  have ecs0 : σ.curSc = σ0.curSc := by rw [eσ]
  have eisc0 : σ.idleSc = σ0.idleSc := by rw [eσ]
  have ecdt0 : σ.cdt = σ0.cdt := by rw [eσ]
  have eorig0 : σ.isOriginalCap = σ0.isOriginalCap := by rw [eσ]
  have hP0 := J.ip
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hARs := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS Hh.inv hC
  set sc := nodeW st s Z.c layout.node.CUR_SC with hscd
  set ct := nodeW st s Z.c layout.node.CUR_THREAD with hctd
  have hct : ct ∈ Z.T := hc.curT
  have ecur : L.curW s = ct := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = sc := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have hpc : sc.bv = σ.curSc := hs.curSc.symm
  have hpt : ct.bv = σ.curThread := hs.curThread.symm
  have hcsI := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hact (by rw [hpc]; exact hcsI) x n hk
  have hkt' : σ.kheap ct.bv = some (.tcb xt) := by rw [hpt]; exact hkt
  have hxs : xt.tcbSchedContext = some sc.bv := by
    obtain ⟨xt1, hk1, hs1, -⟩ := hC.tcb
    rw [hkt] at hk1; cases hk1; rw [hs1, hpc]
  have hne : ct.bv ≠ sc.bv := fun e => by rw [e, hk] at hkt'; cases hkt'
  have hper0 : x.scPeriod ≠ 0 := hper x n (by rw [← hpc]; exact hk)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc _ x n hsc0 (by rw [← ekh]; exact hk)).2⟩
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hcS : L.cscW s ∈ P1.Heap.scs H := hX1.2.2.cur
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (hS1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  have hW1 := hS1.wf hcS hcA
  -- the program
  unfold sched.charge_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.idle_sc.spec' as ⟨id', hid'⟩
  rw [hc.cur] at hsc' hid'
  subst hsc' hid'
  rw [sc_ne_eq]
  simp only [bind_ok]
  have hb : decide (sc ≠ nodeW st s Z.c layout.node.IDLE_SC) = decide (sc.bv ≠ σ.idleSc) := by
    rw [← hS.idle]
    apply decide_eq_decide.2
    exact ⟨fun h e => h (P1.eq_of_bv e), fun h e => h (by rw [e])⟩
  refine WP.spec_bind (WP.spec_and (charge_head_refinesK s a σ hS hR Hh.nsc Hh.inv hscC htw hact hnr hmrt hmb
    used _ hb) (P1.sched.charge_head.ring hAT s a used hX1 hcS hW1 ecsc.symm _)) ?_
  rintro s2 ⟨⟨σ2, h2, hS2, hR2, hN2, hI2, hK, hTK, hW2⟩, w2, wf2⟩
  have hK' := hK
  obtain ⟨hcs2, hcc2, hrel2, hact2, -, hid2, hisc2, hrq2, hfr2, hsck2⟩ := hK'
  obtain ⟨y2, hky2, hyt2, hym2⟩ := hsck2 x n hk
  have mem2 : ((), σ2) ∈ (chargeHead used.bv σ).1 := by rw [h2]; exact Set.mem_singleton _
  have hKh : ScTKw (fun _ => False) σ σ2 := (nkt_chargeHead used.bv) σ _ mem2
  have hsokh : SOK (true, true) σ σ2 := pres_chargeHead _ _ σ _ mem2
  have hlkh : LK (fun _ => False) σ σ2 := lkm_chargeHead _ _ σ _ mem2
  have hfkh : FK σ σ2 := fk_chargeHead _ σ _ mem2
  have hc2 := hS2.lists.choose_spec.choose_spec.1.cur
  have hN2' := hS2.lists.choose_spec.choose_spec.1.node
  -- the consumed-time reset
  step with sched.set_consumed.spec' as ⟨s3, hs3⟩
  rw [hc2] at hs3
  subst hs3
  have w3 := sfoot_wr_node hN2' (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED]) 0#u64
  obtain ⟨hS3', hf3, -⟩ := hS2.set_node_consumed 0#u64
  set σ3 : Fl4Spec.State Unit := { σ2 with consumedTime := 0 } with hσ3
  set s3 := L.wr s2 (L.nodeAt s2 Z.c layout.node.CONSUMED) 0#u64 with hs3d
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hS3'
  have hR3 : NtfnStateRel Z.N Z.T (L.mem s3) σ3 := hR2.frame hS2.placed hf3 (KView.of_kheap rfl)
  have hN3 : NSC Z.N Z.C σ3 := hN2
  have hI3 : InvBut σ3 ct.bv := hI2.congr rfl rfl rfl rfl
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  have e1 : nodeW st s3 Z.c layout.node.CUR_THREAD = ct :=
    P1.eq_of_bv (by rw [← hs3.curThread]; exact hcc2.trans hs.curThread)
  have e2 : nodeW st s3 Z.c layout.node.CUR_SC = sc :=
    P1.eq_of_bv (by rw [← hs3.curSc]; exact hcs2.trans hs.curSc)
  -- P1 after the reset
  obtain ⟨hblk3, hG3⟩ := P1.charge_pre_post (G := fun s' => P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
    (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') h1 hB1 hX1 hSg1 hS1 w2 wf2
    (fun _ _ g1 g2 => g1.trans g2) (P1.WritesIn.refl _ _)
  rw [hc2] at hblk3 hG3
  -- the spec state after the reset against the base
  have hky3 : σ3.kheap sc.bv = some (.schedContext y2 n) := hky2
  have hkp3 : ∀ q, q ≠ sc.bv → σ3.kheap q = σ.kheap q := fun q hq => hfr2 q hq
  have hO : ScOnly σ0.curSc σ0 σ3 := by
    intro q
    by_cases hq : q = sc.bv
    · subst hq
      right
      have h0 : σ0.kheap sc.bv = some (.schedContext x n) := by rw [← ekh]; exact hk
      have hpk : PK (true, true) (.schedContext x n) (.schedContext y2 n) := by
        have h := hsokh.kh sc.bv; rw [hk, hky2] at h; exact h
      obtain ⟨-, hyf, hrp⟩ := hpk
      have hl : LObj (.schedContext x n) (.schedContext y2 n) := by
        have h := (hlkh sc.bv).resolve_left id; rw [hk, hky2] at h; exact h
      obtain ⟨y', e', -, hnt⟩ := hl.2.1 x n rfl
      cases e'
      exact ⟨_, _, h0, hky3, by rw [hpc, ecs0], x, y2, n, rfl, rfl, hyt2, hym2, hyf rfl, hrp rfl, hnt⟩
    · left
      rw [hkp3 q hq, ekh]
  have hzO : SzKeepC Z.C σ0 σ3 := SzKeepC.of hO.szKeep
  -- FL4's writes from the base
  have hWK : P1.WritesIn st s s3 (KFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.kfoot_sfoot hW2 w3
  have hWK0 : P1.WritesIn st s0 s3 (KFoot st Z.T Z.N Z.C Z.c s0 σ0) :=
    WritesIn.kfoot_trans Hh.ws (fun sc1 _ x1 n1 h => ⟨x1, by rw [← ekh]; exact h⟩) hWK
  have hW0 : P1.WritesIn st s0 s3 (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot hWK0
  have hK3 : ScTKw (fun _ => False) σ2 σ3 :=
    ⟨fun p => OTK.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hKc : ScTKw (fun _ => False) σ0 σ3 := (hK0.trans hKh).trans hK3
  have hX3 : XTopAt (L := L) AR Z s3 a σ3 :=
    xtop_sc_step (ct := σ0.curThread) J.xtop hP0 J.nk hW0 hKc.ofFalse hS3 hR3 fun _ => by
      rw [← earch0]; exact hARs
  -- the scheduler facts at the reset
  have hA2 := Hh.act.headKeeps hK ⟨x, n, hk⟩
  have hAI3 : ActIdle σ3 := hA2.keep (TKeepE.of_kheap _ rfl) (fun _ h => h) (Or.inl rfl) rfl
  have hya2 : Fl4Spec.scActive y2 = true := by simp only [Fl4Spec.scActive, hym2]; exact hxa
  have hbsa3 : BlockedScActive σ3 := by
    refine hbsaσ.back (fun q y1 n1 hq ha => ?_) (fun t x1 hx1 hq => ?_)
    · by_cases e : q = sc.bv
      · rw [e, hky3] at hq; cases hq; rw [hya2] at ha; cases ha
      · exact ⟨y1, by rw [← hkp3 q e]; exact hq, ha, fun _ h => h, id⟩
    · have e : t ≠ sc.bv := fun e => by rw [e, hky3] at hx1; cases hx1
      exact ⟨x1, by rw [← hkp3 t e]; exact hx1, hq⟩
  have hown3 : CurOwnW Z.T Z.C σ3 := by
    obtain ⟨u, hu, xu, hku, hxu, hou, -⟩ := curOwn_of_curInv hS Hh.inv hC
    have hup : u.bv ≠ sc.bv := fun e => by rw [e, hk] at hku; cases hku
    refine Or.inl ⟨u, hu, xu, by rw [hkp3 _ hup]; exact hku,
      by rw [show σ3.curSc = σ.curSc from hfkh.1]; exact hxu, fun y1 n1 hy1 => ?_,
      fun h0 => absurd h0 (by rw [show σ3.consumedTime = 0 from rfl]; decide)⟩
    rw [show σ3.curSc = σ.curSc from hfkh.1, ← hpc, hky3] at hy1; cases hy1
    rw [hyt2]; exact hou x n (by rw [← hpc]; exact hk)
  have hsort3 : IpcSorted σ3 :=
    J.isorted.frame (fun q x' hq => ⟨x', hO.othB hq (fun _ _ e => by cases e), rfl⟩)
      (fun q x' hq => ⟨x', hO.othB hq (fun _ _ e => by cases e), rfl⟩) hO.prio
  have eN : L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb Hh.ws.1 _ _
  have hDbg3 : L.mem s3 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hh.dbg]
    exact hG3.mem_eq J.kern.dwAl fun hk' => P1.dbg0_not_schedW Hh.blk J.kern.cs0 (Or.inl (by rw [eN]; exact hk'))
  have hct3 : σ3.curThread = ct.bv := hcc2.trans hs.curThread
  have Hj : JTH (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s3 a σ3 :=
    { j0 := J, ws := hWK0, xtop := hX3, buf := J.sc_buf hW0 hKc, nsc := hN3,
      inv := by rw [hct3]; exact hI3, act := hAI3, bsa := hbsa3, own := hown3, isorted := hsort3,
      blk := hblk3, dbg := hDbg3, dbgK := Hh.dbgK.trans (P1.Foot.dbgKeep Hh.blk (fun _ h => h) hG3), ksc := hO, ct := hcc2.trans ect0, idle := hid2.trans eidle0,
      csc := hcs2.trans ecs0, rel := hrel2.trans erel0, cdt := hsokh.cdt.trans ecdt0,
      orig := hsokh.orig.trans eorig0, arch := hKh.arch.trans earch0, isc := hisc2.trans eisc0, cons := rfl }
  -- the tail: the current thread, schedulable
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc3.cur, e1] at hct'
  subst hct'
  step with Fl4Proofs.P3.Sched.sched.is_schedulable.spec' as ⟨b1, hb1⟩
  rw [schedulable_eq hR3 hS3 hct] at hb1
  subst hb1
  have hkt3 : σ3.kheap ct.bv = some (.tcb xt) := by rw [hkp3 _ hne]; exact hkt'
  have hrun : Fl4Spec.runnable xt.tcbState = true := by rcases hrr with e | e <;> rw [e] <;> rfl
  have hsch : Fl4Spec.schedulable ct.bv σ3 = true :=
    schedulable_of hkt3 hxs hrun hky3 hya2 (by rw [show σ3.releaseQueue = σ.releaseQueue from hrel2]; rw [hpt]; exact hC.notRel)
  simp only [hsch, ↓reduceIte]
  have hnq3 : NotQueued σ3 ct.bv :=
    ⟨fun d q => by rw [show σ3.readyQueues = σ.readyQueues from hrq2, hpt]; exact hnq d q,
      by rw [show σ3.releaseQueue = σ.releaseQueue from hrel2, hpt]; exact hC.notRel⟩
  have hidt3 : σ3.idleThread ≠ ct.bv := by
    rw [show σ3.idleThread = σ.idleThread from hid2, hpt]; exact fun e => hni e.symm
  have hres3 : σ3.schedulerAction = .resumeCurThread := hact2.trans hres
  have hp3 : ∀ xe, σ3.kheap p = some (.endpoint xe) → Endp.CanBlock false xe := fun xe h => by
    by_cases e : p = sc.bv
    · rw [e, hky3] at h; cases h
    · rw [hkp3 _ e] at h; exact hcb xe h
  have hper2 : y2.scPeriod ≠ 0 := by
    obtain ⟨y', n', hky', hy'⟩ := hs3.scs sc hscC
    rw [hky3] at hky'; cases hky'
    rw [hy'.period]
    have e3 : L.rperiod s3 sc = L.rperiod s sc := by
      have hp2 : L.rperiod s2 sc = L.rperiod s sc := by
        have := P1.rperiod_of_ring hX1 hcS w2; rw [ecsc] at this; exact this
      rw [← hp2]
      obtain ⟨y'', n'', hky'', hy''⟩ := (hS2.lists.choose_spec.choose_spec.2).scs sc hscC
      rw [hky2] at hky''; cases hky''
      have h1' := hy''.period
      rw [hy'.period] at h1'
      exact P1.eq_of_bv h1'
    rw [e3, ← hx.period]; exact hper0
  refine WP.spec_bind (Hj.endTimesliceTmoJ hct hct3.symm hkt3 hrr hscC (hcs2.trans hpc.symm) hxs hky3 hya2 hper2
    hth hp3 hres3 hnq3 hidt3) ?_
  rintro ⟨s4, a1⟩ ⟨z4, hz4, V4, D4, J4⟩
  obtain ⟨s5, hs5, σ5, h5, Ac5, Lst5, D5, J5⟩ := J4.reschedJ
  refine WP.spec_bind (show sched.reschedule_required st s4 ⦃ s' => s' = s5 ⦄ by
    rw [hs5]; exact (WP.spec_ok _).2 rfl) ?_
  rintro _ rfl
  refine WP.spec_bind (sched.set_reprogram.spec' (L := L) _) ?_
  rintro s6 rfl
  rw [WP.spec_ok]
  beta_reduce
  refine ⟨((), { σ5 with reprogramTimer := true }), ?_, V4, Ac5, Lst5, D5, J5.reprogramJ⟩
  rw [chargeBudget_eq, nd_bind_one h2, chargeTail_eq true σ2 (hcc2.trans hs.curThread), if_pos hsch]
  refine mem_bind_nd (x := z4) hz4 (mem_bind_nd (x := ((), σ5))
    (show ((), σ5) ∈ (Fl4Spec.rescheduleRequired (Z := Unit) z4.2).1 by rw [h5]; exact Set.mem_singleton _) ?_)
  simp [Fl4Spec.NonDet.modify]
end

end

end Fl4Proofs.P3
