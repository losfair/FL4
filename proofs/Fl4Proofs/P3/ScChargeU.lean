/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` of the current SC
for an unschedulable current thread** (KENTRY-PLAN kp14, (2b) case (b) second
half; the preemption path's branch "current thread not schedulable, current
SC active", l4v `preemption_path`'s `charge_budget consumed False`).

ScChargeG's `charge_head_refinesK` / `charge_budget_refinesF` ask the current
thread to own the current SC (`htw`, `hts`) and to be out of the release
queue (`hnr`). At a preemption hole without `CurInv` neither holds in
general: the current thread may be unbound (`CtOK` allows `none`) and the
SC's owner may be another thread (only inactive, by `Chg`). Here the owner is
a parameter `u0`:

* `charge_head_refinesU`: the head with the SC's TCB `u0` or none (`hown`)
  and `u0` out of the release queue; `InvBut σ2 u0` after (`Inv.refillUpd`,
  `budget_check_refines_inv` are already owner-parametrised). No `TmoKeep`:
  `can_timeout_fault = false`.
* `schedulable_headKeeps`: a step keeping what `HeadKeeps` names keeps an
  unschedulable thread unschedulable (the SC's refill max is kept).
* `charge_budget_refinesU`: the whole `charge_budget used false` for an
  unschedulable current thread: the tail is only the consumed-time reset on
  both sides (FL4's `is_schedulable` stays false), and `Inv` after from
  `InvBut σ' u0` because `u0` is in no `inClassR` state (`hnin`; at a hole
  XTopJointPreemptL's `owner_not_inClassR`).
-/
import Fl4Proofs.P3.ScChargeG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- **An unschedulable thread stays unschedulable across a step keeping what
`HeadKeeps` names** (module docstring), with any consumed time after. -/
theorem schedulable_headKeeps {σ σ2 σ3 : Fl4Spec.State Unit} {p t : Fl4Spec.ObjRef} (hK : HeadKeeps σ σ2 p)
    {x0 : Fl4Spec.SchedContext} {n0 : Nat} (hp : σ.kheap p = some (.schedContext x0 n0))
    (h : Fl4Spec.schedulable t σ = false) (e3 : σ3.kheap = σ2.kheap)
    (r3 : σ3.releaseQueue = σ2.releaseQueue) : Fl4Spec.schedulable t σ3 = false := by
  cases e : Fl4Spec.schedulable t σ3 with
  | false => rfl
  | true =>
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e
    obtain ⟨-, -, erq, -, -, -, -, -, hfr, hsc⟩ := hK
    obtain ⟨y0, hy0, -, hm0⟩ := hsc x0 n0 hp
    rw [e3] at h1 h4
    have htp : t ≠ p := fun ee => by rw [ee, hy0] at h1; cases h1
    rw [hfr t htp] at h1
    have h6' : t ∉ σ.releaseQueue := by rw [← erq, ← r3]; exact h6
    by_cases ep : scp = p
    · subst ep
      rw [hy0] at h4; cases h4
      have ha : Fl4Spec.scActive x0 = true := by
        unfold Fl4Spec.scActive Fl4Spec.activeSc at h5 ⊢; rw [← hm0]; exact h5
      rw [schedulable_of h1 h2 h3 hp ha h6'] at h; cases h
    · rw [hfr scp ep] at h4
      rw [schedulable_of h1 h2 h3 h4 h5 h6'] at h; cases h

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`charge_budget` before the consumed-time reset, owner `u0`** (module
docstring; `charge_head_refinesK` with `hown`/`hnr` for `u0` in place of
`htw`/`hnr` for the current thread). -/
theorem charge_head_refinesU {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C) {u0 : Fl4Spec.ObjRef}
    (hown : ∀ y m, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext y m) →
      y.scTcb = some u0 ∨ y.scTcb = none) (hnr : u0 ∉ σ.releaseQueue)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) (b : Bool)
    (hb : b = decide ((nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc)) :
    (if b then do
      let b1 ← sporadic.is_round_robin st s (nodeW st s c layout.node.CUR_SC)
      let s3 ← if b1 then do
          let hi ← obj.Sc.refill_head st (nodeW st s c layout.node.CUR_SC) s
          let ti ← obj.Sc.refill_tail st (nodeW st s c layout.node.CUR_SC) s
          let h ← sporadic.get st s (nodeW st s c layout.node.CUR_SC) hi
          let t ← sporadic.get st s (nodeW st s c layout.node.CUR_SC) ti
          let i ← lift (core.num.U64.wrapping_add h.amount t.amount)
          let s4 ← sporadic.put st s (nodeW st s c layout.node.CUR_SC) hi { h with amount := i }
          sporadic.put st s4 (nodeW st s c layout.node.CUR_SC) ti { t with amount := 0#u64 }
        else sporadic.budget_check st ar s a used
      let i ← obj.Sc.consumed st (nodeW st s c layout.node.CUR_SC) s3
      let total ← lift (core.num.U64.wrapping_add i used)
      obj.Sc.set_consumed st (nodeW st s c layout.node.CUR_SC) s3 total
    else ok s) ⦃ s2 => ∃ σ2, chargeHead used.bv σ = ({((), σ2)}, False) ∧
      SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧
      InvBut σ2 u0 ∧ HeadKeeps σ σ2 (nodeW st s c layout.node.CUR_SC).bv ∧
      WritesIn st s s2 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hscC
  have hspec : chargeHead used.bv σ = Fl4Spec.NonDet.when (sc.bv ≠ σ.idleSc) (do
      let robin ← Fl4Spec.isRoundRobin (Z := Unit) sc.bv
      if robin
      then Fl4Spec.refillResetRr sc.bv
      else Fl4Spec.refillBudgetCheck used.bv
      Fl4Spec.updateSchedContext sc.bv (fun y => { y with scConsumed := y.scConsumed + used.bv })) σ := by
    unfold chargeHead; rw [nd_gets_bind, nd_gets_bind, hs.curSc]
  by_cases hid : sc.bv ≠ σ.idleSc
  · have hb' : b = true := by rw [hb]; simpa using hid
    simp only [hb', ↓reduceIte]
    have hrr : decide (L.rperiod s sc = 0#u64) = decide (x.scPeriod = 0) := by
      apply decide_eq_decide.2
      rw [hx.period]
      exact ⟨fun h => by rw [h]; rfl, fun h => eq_of_bv (by rw [h]; rfl)⟩
    have hspec2 : ∀ (σ3 : Fl4Spec.State Unit),
        (if decide (x.scPeriod = 0) = true then Fl4Spec.refillResetRr (Z := Unit) sc.bv
          else Fl4Spec.refillBudgetCheck used.bv) σ = ({((), σ3)}, False) →
        chargeHead used.bv σ = Fl4Spec.updateSchedContext (Z := Unit) sc.bv
          (fun y => { y with scConsumed := y.scConsumed + used.bv }) σ3 := by
      intro σ3 h3
      rw [hspec]; unfold Fl4Spec.NonDet.when; rw [if_pos hid, nd_bind_one (isRoundRobin_eq hk)]
      split_ifs at h3 ⊢ <;> exact nd_bind_one h3 _
    have fin : ∀ (s3 : S) (y' : Fl4Spec.SchedContext), y' = { x with scRefills := y'.scRefills } →
        (if decide (x.scPeriod = 0) = true then Fl4Spec.refillResetRr (Z := Unit) sc.bv
          else Fl4Spec.refillBudgetCheck used.bv) σ = ({((), updSc σ sc.bv y' n)}, False) →
        SchedRel st N T C c s3 (updSc σ sc.bv y' n) → NtfnStateRel N T (L.mem s3) (updSc σ sc.bv y' n) →
        NSC N C (updSc σ sc.bv y' n) → InvBut (updSc σ sc.bv y' n) u0 →
        WritesIn st s s3 (KFoot st T N C c s σ) →
        (do
          let i ← obj.Sc.consumed st sc s3
          let total ← lift (core.num.U64.wrapping_add i used)
          obj.Sc.set_consumed st sc s3 total) ⦃ s2 => ∃ σ2, chargeHead used.bv σ = ({((), σ2)}, False) ∧
          SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧
          InvBut σ2 u0 ∧ HeadKeeps σ σ2 sc.bv ∧
          WritesIn st s s2 (KFoot st T N C c s σ) ⦄ := by
      intro s3 y' hy' h3 hS3 hR3 hN3 hI3 hW3
      have hk3 : (updSc σ sc.bv y' n).kheap sc.bv = some (.schedContext y' n) := by simp [updK]
      refine WP.spec_mono (consumed_refines s3 _ hS3 hR3 hN3 hI3 hscC hk3 used) ?_
      rintro s2 ⟨σ2, h1, rfl, h2, h3', h4, h5, hw5⟩
      refine ⟨_, by rw [hspec2 _ h3]; exact h1, h2, h3', h4, h5, ?_, ?_⟩
      · rw [updSc_updSc]
        exact HeadKeeps.updSc hk (by rw [hy']) (by rw [hy'])
      · refine (hW3.trans hw5).mono fun b hb => ?_
        rcases hb with hb | rfl
        · exact hb
        · exact KFoot.of_sw (sw_hdr hS hscC (K := 8#u64) (by simp) (by simp) (by decide))
    step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
    subst hrr'
    by_cases h0 : L.rperiod s sc = 0#u64
    · have e0 : decide (L.rperiod s sc = 0#u64) = true := decide_eq_true h0
      have hper : x.scPeriod = 0 := by have := hrr ▸ e0; simpa using this
      simp only [e0, ↓reduceIte]
      have hx := hx.strong (hact hid x n hk)
      refine WP.spec_bind (rr_reset_refines (RingAt.refl hx.wf)) ?_
      rintro s3 ⟨hring, hl⟩
      obtain ⟨hS3, hf, hkv⟩ := hS.ringAt hscC hk hring
      rw [hl] at hS3 hkv
      have hne := refills_ne' hx.wf
      have hI3 : InvBut (updSc σ sc.bv { x with scRefills := (rrResetL (L.refills s sc)).map toRefill } n) u0 :=
        hI.refillUpd hk rfl (by simp [rrResetL]) (fun _ hp => absurd hper hp)
          (fun _ _ => rrResetL_rr hx.refills (hI.rr _ x n hk (hact hid x n hk) hper)) (hown x n hk) hnr
      refine fin s3 _ rfl ?_ hS3 (by rw [← hl]; rw [← hl] at hkv; exact hR.frame hS.placed hf hkv)
        (hN.kview hR hkv) hI3 (RingAt.kfoot hS hscC hring)
      rw [if_pos (by simpa using hper)]
      exact refillResetRr_eq hk hx.refills hne |>.trans rfl
    · have e0 : decide (L.rperiod s sc = 0#u64) = false := decide_eq_false h0
      have hper : ¬ x.scPeriod = 0 := by
        intro e; have := hrr ▸ e0; simp [e] at this
      simp only [e0, Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (budget_check_refines_inv s a σ hS hI hscC (hact hid) hmrt hmb h0 used
        hown hnr) ?_
      rintro s3 ⟨σ3, h1, hf, hkv, hS3, hI3, hpost, hw3⟩
      obtain ⟨y', rfl, hy', -⟩ := hpost x n hk
      exact fin s3 y' hy' (by rw [if_neg (by simpa using hper)]; exact h1) hS3 (hR.frame hS.placed hf hkv)
        (hN.kview hR hkv) hI3 hw3
  · have hb' : b = false := by rw [hb]; simpa using hid
    simp only [hb', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hS, hR, hN, hI.toBut _, HeadKeeps.refl σ _, WritesIn.refl _ _⟩
    rw [hspec]; unfold Fl4Spec.NonDet.when; rw [if_neg hid]; rfl

/-- **`charge_budget used false` for an unschedulable current thread, owner
`u0`** (module docstring): the head, then only the consumed-time reset;
`Inv` after since `u0` is in no `inClassR` state. -/
theorem charge_budget_refinesU {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = σ.idleSc)
    (hact : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      Fl4Spec.scActive x = true)
    {u0 : Fl4Spec.ObjRef}
    (hown : ∀ y m, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext y m) →
      y.scTcb = some u0 ∨ y.scTcb = none) (hnr : u0 ∉ σ.releaseQueue)
    (hnin : ∀ xu, σ.kheap u0 = some (.tcb xu) → ¬ inClassR xu.tcbState xu.tcbFault)
    (hsch : Fl4Spec.schedulable σ.curThread σ = false)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) :
    sched.charge_budget st ar s a used false ⦃ r => ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv false σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧
      σ'.consumedTime = 0 ∧ (ActIdle σ → ActIdle σ') ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ∧ r.2 = a ∧
      ∃ σ2, HeadKeeps σ σ2 (nodeW st s c layout.node.CUR_SC).bv ∧ chargeTail false σ2 = ({((), σ')}, False) ∧
        σ' = { σ2 with consumedTime := 0 } ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.charge_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.idle_sc.spec' as ⟨id', hid'⟩
  rw [hc.cur] at hsc' hid'
  subst hsc' hid'
  rw [sc_ne_eq]
  simp only [bind_ok]
  have hb : decide (nodeW st s c layout.node.CUR_SC ≠ nodeW st s c layout.node.IDLE_SC) =
      decide ((nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc) := by
    rw [← hidle]
    apply decide_eq_decide.2
    exact ⟨fun h e => h (eq_of_bv e), fun h e => h (by rw [e])⟩
  refine WP.spec_bind (charge_head_refinesU s a σ hS hR hN hI hscC hown hnr (fun _ => hact) hmrt hmb used _ hb) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, hK, hW2⟩
  have hc2 := hS2.lists.choose_spec.choose_spec.1.cur
  have hN2' := hS2.lists.choose_spec.choose_spec.1.node
  step with sched.set_consumed.spec' as ⟨s3, hs3⟩
  rw [hc2] at hs3
  subst hs3
  have w3 := sfoot_wr_node hN2' (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED]) 0#u64
  obtain ⟨hS3', hf3, -⟩ := hS2.set_node_consumed 0#u64
  set σ3 : Fl4Spec.State Unit := { σ2 with consumedTime := 0 } with hσ3
  have hS3 : SchedRel st N T C c (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) σ3 := hS3'
  have hR3 : NtfnStateRel N T (L.mem (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64)) σ3 :=
    hR2.frame hS2.placed hf3 (KView.of_kheap rfl)
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  have hct3 := hc3.curT
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc3.cur] at hct'
  subst ct'
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  rw [schedulable_eq hR3 hS3 hct3] at hb1
  subst hb1
  have hcc : σ2.curThread = σ.curThread := hK.2.1
  have hsch3 : Fl4Spec.schedulable σ.curThread σ3 = false :=
    schedulable_headKeeps hK hk hsch rfl rfl
  have ect : σ3.curThread = (nodeW st (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) c
      layout.node.CUR_THREAD).bv := hs3.curThread
  rw [← ect, show σ3.curThread = σ.curThread from hcc, hsch3]
  simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  have hspec := chargeTail_eq false σ2 hcc
  rw [← hσ3, if_neg (by rw [hsch3]; exact Bool.false_ne_true)] at hspec
  have hkp : ∀ q, q ≠ (nodeW st s c layout.node.CUR_SC).bv → σ3.kheap q = σ.kheap q := hK.2.2.2.2.2.2.2.2.1
  obtain ⟨y2, hky2, -, -⟩ := hK.2.2.2.2.2.2.2.2.2 x n hk
  have hI3 : Inv σ3 := (hI2.congr rfl rfl rfl rfl : InvBut σ3 u0).inv fun xu hxu hcl => by
    have hu : u0 ≠ (nodeW st s c layout.node.CUR_SC).bv := fun e => by
      rw [e] at hxu; exact absurd (hxu.symm.trans hky2) (by simp)
    rw [hkp u0 hu] at hxu
    exact absurd hcl (hnin xu hxu)
  refine ⟨σ3, by rw [chargeBudget_eq, nd_bind_one h2]; exact hspec, hS3, hI3, hR3, hN2, hK, rfl,
    fun hA => (hA.headKeeps hK ⟨x, n, hk⟩).keep (TKeepE.of_kheap _ rfl) (fun _ h => h) (Or.inl rfl) rfl,
    WritesIn.kfoot_sfoot hW2 w3, by first | trivial | rfl, σ2, hK, hspec, rfl⟩

end

end

end Fl4Proofs.P3.Sched
