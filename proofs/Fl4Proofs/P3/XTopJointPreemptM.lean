/-
P3 (DESIGN.md §9): **the preemption path's charge of an SC the current
thread does not own** (KENTRY-PLAN kp14, (2b) case (b) second half):
`JPreemptRestHypL` [W] narrowed to `CurInv`.

Case (b): at a preemption hole without `CurInv`, the current thread not
schedulable and the current SC active, FL4's `mcs_preemption_point` runs
`charge_budget consumed false` and the spec's `preemption_path` runs
`charge_budget consumed False` (l4v: `cur_sc_chargeable` makes that safe).

* `JHole.chargeBudgetUJ`: ScChargeH's `JHole.chargeBudgetJ` without
  `CurInv`: the SchedRel-level step is ScChargeU's `charge_budget_refinesU`
  with the owner `u0` from the base's `CurOwnW` (the SC's TCB, out of the
  release queue by `CurScFree` and in no `inClassR` state by
  `owner_not_inClassR`; or, for an unbound SC, the SC itself, which is no
  TCB); P1's `charge_budget.allF` with `hcsc1` from `CtOK` and `hna` from the
  hole's reschedule (no `CurInv` ⇒ `chooseNewThread`). The end is assembled
  from the base as there; `CurOwnW` after is the base's (the SC's TCB is
  kept), `OffOK` vacuous (consumed time 0).
* `JHole.mcsPPJU`: FL4's branch at such a hole, `JAt` after.
* `JPreemptRestHypM` [W]: `JPreemptRestHypL` with `CurInv σ` in place of
  `CurInv σ ∨ schedulable … = false` (narrower; `jPreemptRestHypM_of`).
  Left in it: kp5 (i) (`CurInv`, an endpoint timeout handler with waiting
  receivers, not `PPCovT`). `hPre_ofZM`, `dispatch_invokeJPZM`,
  `dispatch_invokeJEPZM`.
-/
import Fl4Proofs.P3.XTopJointPreemptL
import Fl4Proofs.P3.ScChargeU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The hole's current SC word is one of `Z.C` (the base's `CurOwnW`). -/
theorem JHole.curSc_in {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) : nodeW st s Z.c layout.node.CUR_SC ∈ Z.C := by
  have J := Hh.j0
  have hS := Hh.xtop.fin.1.1.1
  have hS0 := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q0, R00, hc0, hs0⟩ := hS0.lists
  obtain ⟨ms, t, c, hum, e⟩ := Hh.spec
  have hcs : σ.curSc = σ0.curSc := by rw [e]
  have e1 : (nodeW st s Z.c layout.node.CUR_SC).bv = (nodeW st s0 Z.c layout.node.CUR_SC).bv := by
    rw [← hs.curSc, ← hs0.curSc]; exact hcs
  rw [P1.eq_of_bv e1]; exact cursc_in hS0 J.own

set_option maxHeartbeats 32000000 in
/-- **`charge_budget used false` from a `JHole` without `CurInv`, current
thread not schedulable, current SC active** (module docstring). -/
theorem JHole.chargeBudgetUJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hnc : ¬ CurInv σ) (hsch : Fl4Spec.schedulable σ.curThread σ = false) (hct : CtOK σ) (hf : CurScFree σ)
    (hg : Chg σ) (hax : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) :
    sched.charge_budget st arI s a used false ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv false σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have J := Hh.j0
  obtain ⟨hK0, hsok0, hlk0, hfk0, ekh, -, -, -, earch, -, -, hbsaσ⟩ := Hh.sfacts
  have hP0 := J.ip
  have hS0 := J.xtop.fin.1.1.1
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hARs := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hcs : σ.curSc = σ0.curSc := by obtain ⟨ms, t, c, -, e⟩ := Hh.spec; rw [e]
  have hscC := Hh.curSc_in
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hax x n (by rw [← hpc]; exact hk)
  have hsc0 : nodeW st s Z.c layout.node.CUR_SC ≠ 0#u64 := fun e =>
    J.cover.sc0 x n (by rw [← e, ← ekh]; exact hk)
  have hcn : σ.schedulerAction = .chooseNewThread := Hh.cur.resolve_right hnc
  have hct' : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb _ hct'
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have hscS : nodeW st s Z.c layout.node.CUR_SC ∈ P1.Heap.scs H :=
    ⟨_, (hJ.sc _ x n hsc0 (by rw [← ekh]; exact hk)).2⟩
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (Hh.blk.2.2.2.1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hcsc1 : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)) := fun h0 => by
    rw [ecur] at h0 ⊢; rw [ecsc]
    have hl := (hct xt (by rw [hs.curThread]; exact hkt)).1
    rw [hsct, Notif.optRef_ne h0] at hl
    rcases hl with hl | hl
    · exact P1.eq_of_bv (hpc.trans (Option.some.inj hl).symm)
    · cases hl
  have hna : L.actionW s ≠ L.curW s := by
    rw [ecur]; exact actionW_ne_of hS hct' (by rw [hcn]; exact fun h => by cases h)
  -- the owner of the current SC (or the SC itself when unbound)
  obtain ⟨u0, hown, hnr, hnin⟩ : ∃ u0 : Fl4Spec.ObjRef,
      (∀ y m, σ.kheap (nodeW st s Z.c layout.node.CUR_SC).bv = some (.schedContext y m) →
        y.scTcb = some u0 ∨ y.scTcb = none) ∧
      u0 ∉ σ.releaseQueue ∧ ∀ xu, σ.kheap u0 = some (.tcb xu) → ¬ inClassR xu.tcbState xu.tcbFault := by
    rcases J.own with ⟨u, hu, xu, hku, hxu, hou, -⟩ | ⟨-, hun⟩
    · have hku' : σ.kheap u.bv = some (.tcb xu) := by rw [ekh]; exact hku
      have hxu' : xu.tcbSchedContext = some σ.curSc := by rw [hcs]; exact hxu
      refine ⟨u.bv, fun y m hy => Or.inl (hou y m (by rw [← hcs, ← ekh, ← hpc]; exact hy)),
        hf _ xu hku' hxu', fun xu' hk' => ?_⟩
      rw [hku'] at hk'; cases hk'
      exact owner_not_inClassR hct hf hg hsch hku' hxu' (by rw [← hpc]; exact hk) hxa
    · refine ⟨σ.curSc, fun y m hy => Or.inr (hun y m (by rw [← hcs, ← ekh, ← hpc]; exact hy)),
        fun hq => ?_, fun xu hk' => ?_⟩
      · obtain ⟨xq, -, -, -, hq1, -⟩ := Hh.inv.rel _ hq
        rw [← hpc, hk] at hq1; cases hq1
      · rw [← hpc, hk] at hk'; cases hk'
  refine WP.spec_mono (WP.spec_and (charge_budget_refinesU (ar := arI) s a σ hS hR Hh.nsc Hh.inv hscC hS.idle
      (fun x1 n1 h1 => hax x1 n1 (by rw [← hpc]; exact h1)) hown hnr hnin hsch hmrt hmb used)
    (P1.sched.charge_budget.allF (G := fun s' => P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') hAT s a used Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc1 hna hcA
      (fun _ _ g1 g2 => g1.trans g2) (P1.WritesIn.refl _ _))) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hsp, hS', hI', hR', hN', hHK', hcons, hAI, hWK, hra, σ2, hH, -, e2⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨hbx, hfoot⟩ := hP1
  have mem : ((), σ') ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv false σ).1 := by
    rw [hsp]; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ σ' := nkt_chargeBudgetF _ σ _ mem
  refine ⟨hra, σ', hsp, hK, ?_⟩
  have hsok : SOK (true, true) σ σ' := pres_chargeBudgetF _ _ σ _ mem
  have hlk : LK (fun _ => False) σ σ' := lkm_chargeBudgetF _ _ σ _ mem
  have hfk : FK σ σ' := fk_chargeBudgetF _ σ _ mem
  have hkp : ∀ q, q ≠ (nodeW st s Z.c layout.node.CUR_SC).bv → σ'.kheap q = σ.kheap q :=
    hHK'.2.2.2.2.2.2.2.2.1
  obtain ⟨y, hky', hyt, hym⟩ := hHK'.2.2.2.2.2.2.2.2.2 x n hk
  have hya : Fl4Spec.scActive y = true := by simp only [Fl4Spec.scActive, hym]; exact hxa
  have hKc : ScTKw (fun _ => False) σ0 σ' := hK0.trans hK
  have hsokc : SOK (true, true) σ0 σ' := hsok0.trans hsok
  have hlkc : LK (fun _ => False) σ0 σ' := hlk0.trans hlk
  have hfkc : FK σ0 σ' := hfk0.trans hfk
  have hWK0 : P1.WritesIn st s0 s' (KFoot st Z.T Z.N Z.C Z.c s0 σ0) :=
    WritesIn.kfoot_trans Hh.ws (fun sc _ x1 n1 h => ⟨x1, by rw [← ekh]; exact h⟩) hWK
  have hW : P1.WritesIn st s0 s' (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot hWK0
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    xtop_sc_step (ct := σ0.curThread) J.xtop hP0 J.nk hW hKc.ofFalse hS' hR' fun _ => by rw [← earch]; exact hARs
  have hY : YieldRel Z.T Z.C (L.mem s') σ' :=
    J.yld.frame (fun y1 hy1 => hWK0.mem_eq (yieldA_aligned hT hy1) fun hb => hb.ne_yield hS0 hy1 rfl)
      (hsokc.ykeep rfl)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS0 J.rp J.mcp J.call J.rfree ⟨hS', hR', hN', hI'⟩ hY (hW.mono fun _ h => Or.inl h) hsokc rfl
  have hAI' := hAI Hh.act
  have eN : L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb Hh.ws.1 _ _
  have hDbg : L.mem s' (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hh.dbg]
    exact hfoot.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW Hh.blk J.kern.cs0 (Or.inl (by rw [eN]; exact hk))
  have hidW := J.idleW_keep hS' hfkc.2.1 hfkc.2.2
  have hblk' : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  have hcn' : σ'.schedulerAction = .chooseNewThread := hHK'.2.2.2.1.trans hcn
  have hown' : CurOwnW Z.T Z.C σ' := by
    rcases J.own with ⟨u, hu, xu, hku, hxu, hou, -⟩ | ⟨⟨c', hc', hcv'⟩, hun⟩
    · have hup : u.bv ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by
        rw [e, ← ekh, hk] at hku; cases hku
      refine Or.inl ⟨u, hu, xu, by rw [hkp _ hup, ekh]; exact hku, by rw [hfk.1, hcs]; exact hxu,
        fun y1 n1 hy1 => ?_, fun h0 => absurd h0 (by rw [hcons]; decide)⟩
      rw [hfk.1, ← hpc, hky'] at hy1; cases hy1
      rw [hyt]; exact hou x n (by rw [← hcs, ← ekh, ← hpc]; exact hk)
    · refine Or.inr ⟨⟨c', hc', by rw [hfk.1, hcs]; exact hcv'⟩, fun y1 n1 hy1 => ?_⟩
      rw [hfk.1, ← hpc, hky'] at hy1; cases hy1
      rw [hyt]; exact hun x n (by rw [← hcs, ← ekh, ← hpc]; exact hk)
  have hoff : OffOK σ' := fun h0 => absurd h0 (by rw [hcons]; decide)
  have hcr : CurRunM σ' := Or.inl (act_cn_nr hcn')
  have hbsa : BlockedScActive σ' := by
    refine hbsaσ.back (fun q y1 n1 hq ha => ?_) (fun t x1 hx1 hq => ?_)
    · by_cases e : q = (nodeW st s Z.c layout.node.CUR_SC).bv
      · rw [e, hky'] at hq; cases hq; rw [hya] at ha; cases ha
      · exact ⟨y1, by rw [← hkp q e]; exact hq, ha, fun _ h => h, id⟩
    · have e : t ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by rw [e, hky'] at hx1; cases hx1
      exact ⟨x1, by rw [← hkp t e]; exact hx1, hq⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hW hKc (fun _ h => h.elim) hlkc hfkc hAI'.1 hY' ((hsokc.ykeep rfl).dk q.bv) (fun h => h)
      (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW hKc hX' hCR' hRF' hY' hM' (J.sc_buf hW hKc) hRP' (J.sc_apart hW hKc)
    (J.sc_jpl hW hKc hidW.2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) hidW)
    (J.sc_kern hW hKc hfkc hX' hDbg fun _ h => h) (J.sc_utc hW hKc hDbg) hN' hI' (Or.inl hcn') hown' hoff hAI'
    hbsa hcr hblk' (Hh.dbgK.trans (P1.Foot.dbgKeep Hh.blk (by first | exact fun _ h => h | exact Set.empty_subset _) hfoot))
    hidW.1 J.zD⟩


set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` at a hole without `CurInv`, current thread not
schedulable, current SC active** (module docstring). -/
theorem JHole.mcsPPJU {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnc : ¬ CurInv σ) (hct : CtOK σ) (hf : CurScFree σ) (hg : Chg σ)
    (hsch : Fl4Spec.schedulable σ.curThread σ = false) (hin : ¬ PPCovI σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  have hax : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → Fl4Spec.scActive x = true := fun x n h => by
    cases e : Fl4Spec.scActive x with
    | true => rfl
    | false => exact (hin ⟨hsch, fun x' n' h' => by rw [h] at h'; cases h'; exact e⟩).elim
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hscC := Hh.curSc_in
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
  rw [hc.cur] at hsc
  subst hsc
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hab : b1 = Fl4Spec.scActive x := by
    rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hax' : Fl4Spec.scActive x = true := hax x n hkx'
  rw [hab, hax']
  simp only [↓reduceIte]
  step with sched.consumed.spec' as ⟨cv, hcv⟩
  rw [hc.cur] at hcv
  subst hcv
  refine WP.spec_mono (Hh.chargeBudgetUJ hAT hnc hsch hct hf hg hax hmrt hmb _) ?_
  rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
  simp only at ha
  subst a'
  have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
    unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax']; rfl
  have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
    rw [hs.consumed]; exact h1
  exact ⟨σ', fun y hy => mem_pp_charge hsch hga (by rw [h1']; rfl) hy,
    fun hy => fail_pp_charge hsch hga (by rw [h1']; rfl) hy, Z, H, Cs, Ac, Lst', D, J'⟩

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CurInv`** [W] (kp14: `JPreemptRestHypL` with case (b) proved by
`JHole.mcsPPJU`). Left: kp5 (i), an endpoint timeout handler with waiting
receivers (l4v `handle_timeout`'s `send_fault_ipc` to a waiting receiver,
`charge_budget`/`end_timeslice` with `can_timeout_fault`). -/
def JPreemptRestHypM (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypM_of (h : JPreemptRestHypL (L := L) arI AR) : JPreemptRestHypM (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg hC => h s a σ hJ hn hi hs hf hc hg (Or.inl hC)

/-- **`hPre_ofZL` with `JPreemptRestHypM`** (kp14). -/
theorem hPre_ofZM (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypM (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct, hcg⟩ :=
    jAtPre_holeL hARI.toARKeep hA hnd hP h
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZ hTs hA hnd (hmrt a1) (hP.minBudget a1) hIP hIrq hc _)
      fun _ h => h.2.toPPQ
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJI hi) hIP hIrq _) fun _ h => h.2.toPPQ
  by_cases hC : CurInv σ1
  · exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
      (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hC
      fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi
  · have hsch : Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1 with
      | false => rfl
      | true => exact absurd (curInv_of_sched hct e) hC
    exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJU hA (hmrt a1) (hP.minBudget a1) hC hct hfr hcg hsch hi)
      hIP hIrq _) fun _ h => h.2.toPPQ

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZL` with `JPreemptRestHypM`** (kp14). -/
theorem dispatch_invokeJPZM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypM (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZM hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZL` with `JPreemptRestHypM`** (kp14; against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypM (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZM hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
