/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` at the state right
after `update_timestamp`** (KENTRY-PLAN kp3/kp4 (a0): `check_budget`'s charge
in `budget_ok`'s false branch and in the preemption point's schedulable
branch).

After `update_timestamp` the consumed time is the new one, and
`check_budget` charges exactly when the current SC's head cannot pay it, so
`JAtZ`'s `OffOK` fails there: that state is not a `JAtZ` state, and
ScChargeJ's `JAtZ.chargeBudgetJ` (which starts from `JAtZ`) does not apply.
None of the frames reads `OffOK` of the start state; only the record does.
So the charge is proved "from the base" (as XTopJointPP's `JAtZ.timestampJ`
and XTopJointFaultTmo's `sendTmoRecvIJ`):

* `JHole`: the state `(s, a, σ)` right after `update_timestamp` from a `JAtZ`
  state `(s0, a0, σ0)`: `JAtZ` at the base, the spec state the base's with a
  new machine state (same memory), current time and consumed time, FL4's
  writes in the base's `KFoot` (the core's `CUR_TIME`/`CONSUMED` words),
  `XTopAt`, `NSC`, `Inv`, `CurInv`-or-reschedule, `ActIdle`, P1's `BlkOK`
  after, and the node-0 debug word kept. Everything but `OffOK` and
  `CurOwnW` (asked of the state after by `JHole.toJ`).
* `JAtZ.timestampJH`: `update_timestamp` from `JAtZ` refines
  `update_time_stamp` and ends at a `JHole` (XTopJointPP's `timestampJD`
  without asking `OffOK`/`CurOwnW` after).
* `JHole.toJ`: a `JHole` with `OffOK` and `CurOwnW` is a `JAtZ` state.
* `JHole.chargeBudgetJ` / `JHole.chargeBudgetNJ`: ScChargeJ's
  `chargeBudgetJ` / ScChargeN's `chargeBudgetNJ` from a `JHole`: the charge
  steps at the hole (SchedRel-level `charge_budget_refinesF`, P1's
  `charge_budget.allF` from the hole's `BlkOK`), the end assembled from the
  base by `JAtZ.sc_frame` with the writes composed
  (ScKFoot's `WritesIn.kfoot_trans`) and the spec steps composed
  (`ScTKw`/`SOK`/`LK`/`FK` `.trans`). `OffOK`
  after is vacuous (the charge zeroes the consumed time).
-/
import Fl4Proofs.P3.ScChargeR
import Fl4Proofs.P3.XTopJointPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The state right after `update_timestamp` from a `JAtZ` state** (module
docstring): `JAtZ` at the base `(s0, a0, σ0)`; at `(s, a, σ)` every `JAtZ`
fact but `OffOK` and `CurOwnW`, as far as the charge reads them. -/
structure JHole (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  j0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0
  spec : ∃ (ms : Fl4Spec.MachineState) (t c : Fl4Spec.Word),
    ms.underlyingMemory = σ0.machineState.underlyingMemory ∧
    σ = { σ0 with machineState := ms, curTime := t, consumedTime := c }
  ws : P1.WritesIn st s0 s (KFoot st Z.T Z.N Z.C Z.c s0 σ0)
  xtop : XTopAt (L := L) AR Z s a σ
  nsc : NSC Z.N Z.C σ
  inv : Inv σ
  cur : σ.schedulerAction = .chooseNewThread ∨ CurInv σ
  act : ActIdle σ
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s
  dbg : L.mem s (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) = L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS)
  /-- Every debug word kept from the base (KENTRY-PLAN g2i: the `LiveDN` frame
  of the constructions from the hole; `update_timestamp` writes two time
  words of the current node). -/
  dbgK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s

variable {arI}

/-- The hole's spec state against the base's. -/
theorem JHole.sfacts {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) :
    ScTKw (fun _ => False) σ0 σ ∧ SOK (true, true) σ0 σ ∧ LK (fun _ => False) σ0 σ ∧ FK σ0 σ ∧
    σ.kheap = σ0.kheap ∧ σ.curThread = σ0.curThread ∧ σ.schedulerAction = σ0.schedulerAction ∧
    σ.idleThread = σ0.idleThread ∧ σ.archState = σ0.archState ∧ σ.releaseQueue = σ0.releaseQueue ∧
    CurRunM σ ∧ BlockedScActive σ := by
  obtain ⟨ms, t, c, hum, rfl⟩ := Hh.spec
  have hK : ScTKw (fun _ => False) σ0 { σ0 with machineState := ms, curTime := t, consumedTime := c } :=
    ⟨fun p => OTK.refl _ _, hum, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨hK, ⟨fun p => ORel.refl _ _, rfl, rfl, rfl, rfl, rfl⟩, fun p => Or.inr (OL.refl _), ⟨rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, Hh.j0.curRun, Hh.j0.bsa.tkw hK fun p y n h hy => ⟨y, h, hy, fun _ h => h, id⟩⟩

set_option maxHeartbeats 8000000 in
/-- **`update_timestamp` from `JAtZ` ends at a `JHole`** (module docstring;
XTopJointPP's `JAtZ.timestampJD` without asking `OffOK`/`CurOwnW` after). -/
theorem JAtZ.timestampJH {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hnow : NowAgree arI a σ) :
    sched.update_timestamp st arI s a ⦃ r => ∃ σ', Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
      σ'.archState = σ.archState ∧
      σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory ∧
      (Sched.OffReady σ → Sched.OffReady σ') ∧
      ∀ (ms2 : Fl4Spec.MachineState) (a2 : A), ms2.underlyingMemory = σ.machineState.underlyingMemory →
        (AR r.2 σ.archState.x64CurrentCr3 → AR a2 σ.archState.x64CurrentCr3) →
        JHole (L := L) arI AR Z H Cs Ac Lst D s a σ r.1 a2 { σ' with machineState := ms2 } ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hAR := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hnow' : arI.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ⦄ :=
    WP.spec_mono hnow fun _ ⟨ms, h1, h2, _⟩ => ⟨ms, h1, h2⟩
  obtain ⟨r0, -, hr0⟩ := spec_exists hnow
  obtain ⟨ms, hm, -, hum⟩ := hr0
  set nv := r0.1 with hnv
  have hE := updateTimeStamp_eq' hnd hm
  refine WP.spec_mono (WP.spec_and (WP.spec_and (update_timestamp_refines s a σ hS hR J.nsc hnd hnow')
    (update_timestamp_fr arI hAK s a hAR hN)) (P1.sched.update_timestamp.bxc hA s a J.blk.bxi)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ', h1, hS', hR', hN', hI', hC', -, -, hOR', hA', -⟩, hw, hAR'⟩, ⟨k3, -, -⟩, -, -⟩
  simp only at hw hAR' k3
  have e := the_result hE h1
  subst e
  refine ⟨_, h1, rfl, rfl, rfl, rfl, rfl, hum, hOR', fun ms2 a2 hum2 hAa2 => ?_⟩
  set σ1 : Fl4Spec.State Unit := { { { σ with machineState := ms } with curTime := nv.bv } with
    consumedTime := σ.consumedTime + (nv.bv - σ.curTime) } with hσ1
  set σ' : Fl4Spec.State Unit := { σ1 with machineState := ms2 } with hσ'
  have hS2 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hS'.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hR2 : NtfnStateRel Z.N Z.T (L.mem s') σ' := ⟨hR'.ntfn, hR'.tcb⟩
  have hN2 : NSC Z.N Z.C σ' := hN'
  have hI2 : Inv σ' := (hI' J.inv).congr rfl rfl rfl rfl
  have hC2 : CurInv σ → CurInv σ' := fun h => (hC' h).congr rfl rfl rfl rfl
  have hA2 : ActIdle σ → ActIdle σ' := hA'
  have hBlk' := k3.blk
  have hnb : ∀ o : U64, o.val < 4288 → L.nodeBase s Z.c ≤ (L.nodeAt s (L.cpu s) o).val ∧
      (L.nodeAt s (L.cpu s) o).val < L.nodeBase s Z.c + 4288 := fun o ho => by
    rw [P1.nodeAt_val hN ho, hc.cur]; omega
  have hwK : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with rfl | rfl
    · exact Or.inl (Or.inr (hnb _ (by simp [layout.node.CUR_TIME])))
    · exact Or.inl (Or.inr (hnb _ (by simp [layout.node.CONSUMED])))
  have hwT : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_of_kfoot hwK
  have hK : ScTKw (fun _ => False) σ σ' :=
    ⟨fun p => OTK.refl _ _, hum2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hX' : XTopAt (L := L) AR Z s' a2 σ' := xtop_sc_step hX J.ip J.nk hwT (ct := σ.curThread)
    (hK.mono fun _ h => h.elim) hS2 hR2 fun _ => hAa2 hAR'
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
    have hd := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have h1 := P1.nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
    have h2 := P1.nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    have hnb' : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
    have e88 : layout.node.DEBUG_TCBS.val = 88 := by simp [layout.node.DEBUG_TCBS]
    have e40 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
    have e48 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
    refine hw.mem_eq J.kern.dwAl fun hb => ?_
    rw [hnb'] at hd h1 h2
    rcases hb with hb | hb
    · have := congrArg UScalar.val hb; rw [hd, h1] at this; simp at this; omega
    · have := congrArg UScalar.val hb; rw [hd, h2] at this; simp at this; omega
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    ⟨hw.1, fun b hb => hw.mem_eq (P1.dbgW_aligned J.blk hb) fun h' => by
      rcases h' with rfl | rfl
      · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, J.kern.cpuCs, layout.node.CUR_TIME,
          by simp [layout.node.CUR_TIME], by simp [layout.node.CUR_TIME], rfl⟩)) hb
      · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, J.kern.cpuCs, layout.node.CONSUMED,
          by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], rfl⟩)) hb⟩
  exact ⟨J, ⟨ms2, nv.bv, σ.consumedTime + (nv.bv - σ.curTime), hum2, rfl⟩, hwK, hX', hN2, hI2,
    J.cur.imp id hC2, hA2 J.act, hBlk', hDbg, hKd⟩

/-- **`JHole.dbgK` across one more time-word write** (the consumed-time reset
of the preemption path; KENTRY-PLAN g2i). -/
theorem JHole.dbgK_node {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) {c : U64} (hc : c ∈ Cs) {o : U64}
    (ho : o = layout.node.CUR_TIME ∨ o = layout.node.CONSUMED) {s' : S}
    (hw : P1.WritesIn st s s' (· = L.nodeAt s c o)) : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s' :=
  Hh.dbgK.trans ⟨hw.1, fun b hb => hw.mem_eq (P1.dbgW_aligned Hh.blk hb) fun h' => by
    subst h'
    rcases ho with rfl | rfl
    · exact P1.dbgW_not_kw Hh.blk (Or.inr (Or.inl ⟨c, hc, layout.node.CUR_TIME,
        by simp [layout.node.CUR_TIME], by simp [layout.node.CUR_TIME], rfl⟩)) hb
    · exact P1.dbgW_not_kw Hh.blk (Or.inr (Or.inl ⟨c, hc, layout.node.CONSUMED,
        by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], rfl⟩)) hb⟩

set_option maxHeartbeats 4000000 in
/-- **A `JHole` with `OffOK` and `CurOwnW` is a `JAtZ` state** (an SC step
from the base, as in `JAtZ.timestampJD`). -/
theorem JHole.toJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hO : OffOK σ) (hOw : CurOwnW Z.T Z.C σ) :
    ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s a σ := by
  have J := Hh.j0
  obtain ⟨hK, hsok, hL, hF, -, -, -, -, -, -, hcr, hbsa⟩ := Hh.sfacts
  have hS0 := J.xtop.fin.1.1.1
  have hX' := Hh.xtop
  have hS := hX'.fin.1.1.1
  have hR := hX'.fin.1.1.2.2.1
  have hwT : P1.WritesIn st s0 s (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot Hh.ws
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS0 J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS, hR, Hh.nsc, Hh.inv⟩, Hh.ws, hsok⟩
  have hAI' : ActIdle σ := Hh.act
  have hDead : ∀ q ∈ D, DeadP (L := L) H s q := fun q hq =>
    J.deadP_sc_step hX' hwT hK (fun _ _ h => h.elim) hL hF hAI'.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h)
      (J.jcov.dead q hq)
  have hidW := J.idleW_keep hS hF.2.1 hF.2.2
  exact ⟨Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK hidW.2) (J.sc_jcov hwT hDead (fun q hq hn => absurd hq hn) hidW)
    (J.sc_kern hwT hK hF hX' Hh.dbg fun _ h => h)
    (J.sc_utc hwT hK Hh.dbg) Hh.nsc Hh.inv Hh.cur hOw hO hAI' hbsa hcr Hh.blk Hh.dbgK hidW.1 J.zD⟩

set_option maxHeartbeats 32000000 in
/-- **`charge_budget` without timeout faults from a `JHole`** (module
docstring): ScChargeJ's `JAtZ.chargeBudgetJ` at the state after
`update_timestamp`, where `OffOK` need not hold. -/
theorem JHole.chargeBudgetJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) :
    sched.charge_budget st arI s a used false ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv false σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have J := Hh.j0
  obtain ⟨hK0, hsok0, hlk0, hfk0, ekh, -, -, -, earch, -, hcrσ, hbsaσ⟩ := Hh.sfacts
  have hP0 := J.ip
  have hS0 := J.xtop.fin.1.1.1
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hARs := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS Hh.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th (nodeW st s Z.c layout.node.CUR_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hct)
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨xt, hkt, hxs, hnbt⟩ := hC.tcb
  have hcsI : σ.curSc ≠ σ.idleSc := by
    intro e
    obtain ⟨y, n, hky, hyt⟩ := Hh.inv.back _ xt _ hkt hxs
    obtain ⟨xi, hki, hxi, -, -⟩ := Hh.act.2
    rw [← e] at hxi
    obtain ⟨y', n', hky', hyt'⟩ := Hh.inv.back _ xi _ hki hxi
    rw [hky] at hky'; cases hky'
    exact hni (Option.some.inj (hyt.symm.trans hyt'))
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hact (by rw [hpc]; exact hcsI) x n hk
  have hscS : nodeW st s Z.c layout.node.CUR_SC ∈ P1.Heap.scs H :=
    ⟨_, (hJ.sc _ x n hsc0 (by rw [← ekh]; exact hk)).2⟩
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (Hh.blk.2.2.2.1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  have hne : σ.curThread ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by
    rw [e, hk] at hkt; cases hkt
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hcsc1 : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)) := fun _ => by
    rw [ecur, ecsc, hts]
  have hna : L.actionW s ≠ L.curW s := by
    rw [ecur]; exact actionW_ne_of hS hct (by rw [← hs.curThread]; exact hnsw)
  have hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st Z.N Z.T Z.C Z.c s' σ' →
      TmoKeep st (nodeW st s Z.c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s Z.c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s Z.c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄ :=
    fun s' σ' _ hK => hval_of_rel Hh.xtop.rel.1 Hh.xtop.rel.2.1.1 hthc s' σ' hK
  refine WP.spec_mono (WP.spec_and (charge_budget_refinesF (ar := arI) s a σ hAT hS hR Hh.nsc Hh.inv hscC hsc0
    htw hts hS.idle hact hnr hnb hmrt hmb hval used)
    (P1.sched.charge_budget.allF (G := fun s' => P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') hAT s a used Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc1 hna hcA
      (fun _ _ g1 g2 => g1.trans g2) (P1.WritesIn.refl _ _))) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hsp, hS', hI', hR', hN', hact', hcons, hAI, hWK, hra, σ2, hH, ht2⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨hbx, hfoot⟩ := hP1
  have mem0 : ((), σ') ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv false σ).1 := by
    rw [hsp]; exact Set.mem_singleton _
  refine ⟨hra, σ', hsp, nkt_chargeBudgetF _ σ _ mem0, ?_⟩
  have mem : ((), σ') ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv false σ).1 := by
    rw [hsp]; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ σ' := nkt_chargeBudgetF _ σ _ mem
  have hsok : SOK (true, true) σ σ' := pres_chargeBudgetF _ _ σ _ mem
  have hlk : LK (fun _ => False) σ σ' := lkm_chargeBudgetF _ _ σ _ mem
  have hfk : FK σ σ' := fk_chargeBudgetF _ σ _ mem
  have ek : σ'.kheap = σ2.kheap := kh_chargeTailF σ2 ((), σ') (by rw [ht2]; exact Set.mem_singleton _)
  obtain ⟨-, -, -, -, -, -, -, -, hfr2, hsck2⟩ := hH
  have hkp : ∀ q, q ≠ (nodeW st s Z.c layout.node.CUR_SC).bv → σ'.kheap q = σ.kheap q := fun q hq => by
    rw [ek]; exact hfr2 q hq
  obtain ⟨y, hky, hyt, hym⟩ := hsck2 x n hk
  have hky' : σ'.kheap (nodeW st s Z.c layout.node.CUR_SC).bv = some (.schedContext y n) := by rw [ek]; exact hky
  have hya : Fl4Spec.scActive y = true := by simp only [Fl4Spec.scActive, hym]; exact hxa
  -- the composite step from the base
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
  have hcur' : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases hact' with e | hH'
    · exact Or.inl e
    · right
      obtain ⟨hcs, hcc, hrq, -, -, -, -, -, -, -⟩ := hH'
      refine ⟨⟨xt, by rw [hcc, hkp _ hne]; exact hkt, by rw [hcs]; exact hxs, hnbt⟩,
        ⟨y, n, by rw [hcs, ← hpc]; exact hky'⟩, fun _ y1 n1 hy1 => ?_, by rw [hcc, hrq]; exact hC.notRel⟩
      rw [hcs, ← hpc, hky'] at hy1; cases hy1; exact hya
  have hown' : CurOwnW Z.T Z.C σ' := by
    obtain ⟨u, hu, xu, hku, hxu, hou, -⟩ := curOwn_of_curInv hS Hh.inv hC
    have hup : u.bv ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by rw [e, hk] at hku; cases hku
    refine Or.inl ⟨u, hu, xu, by rw [hkp _ hup]; exact hku, by rw [hfk.1]; exact hxu, fun y1 n1 hy1 => ?_,
      fun h0 => absurd h0 (by rw [hcons]; decide)⟩
    rw [hfk.1, ← hpc, hky'] at hy1; cases hy1
    rw [hyt]; exact hou x n (by rw [← hpc]; exact hk)
  have hoff : OffOK σ' := fun h0 => absurd h0 (by rw [hcons]; decide)
  have hcr : CurRunM σ' := by
    rcases hact' with e | hH'
    · exact Or.inl (act_cn_nr e)
    · obtain ⟨-, hcc, -, hac, -, hid, -, -, -, -⟩ := hH'
      rcases hcrσ with h | h
      · exact Or.inl (by rw [hac]; exact h)
      · right
        rcases h with h | h
        · left; intro y1 hy1; rw [hcc, hkp _ hne] at hy1; exact h y1 hy1
        · right; rw [hcc, hid]; exact h
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
    (J.sc_kern hW hKc hfkc hX' hDbg fun _ h => h) (J.sc_utc hW hKc hDbg) hN' hI' hcur' hown' hoff hAI' hbsa hcr
    hblk' (Hh.dbgK.trans (P1.Foot.dbgKeep Hh.blk (by first | exact fun _ h => h | exact Set.empty_subset _) hfoot))
    hidW.1 J.zD⟩


set_option maxHeartbeats 8000000 in
/-- **`charge_budget` with `can_timeout_fault = true` from a `JHole`, when the
current thread has no endpoint cap as its timeout handler**: ScChargeN's
`JAtZ.chargeBudgetNJ` at the state after `update_timestamp`. -/
theorem JHole.chargeBudgetNJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnt : ∀ xt, σ.kheap σ.curThread = some (.tcb xt) → Fl4Spec.isEpCap xt.tcbTimeoutHandler = false)
    (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have J := Hh.j0
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, htw, -, hact, hnr, -⟩ := CurInv.facts hS Hh.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th (nodeW st s Z.c layout.node.CUR_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hct)
  have hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st Z.N Z.T Z.C Z.c s' σ' →
      TmoKeep st (nodeW st s Z.c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s Z.c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s Z.c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄ :=
    fun s' σ' _ hK => hval_of_rel Hh.xtop.rel.1 Hh.xtop.rel.2.1.1 hthc s' σ' hK
  obtain ⟨e1, e2⟩ := charge_budget_noTmo (ar := arI) s a σ hS hR Hh.nsc Hh.inv hscC htw hS.idle hact hnr hmrt hmb
    hval (fun xt hx => hnt xt (by rw [hs.curThread]; exact hx)) used
  rw [e1]
  refine WP.spec_mono (Hh.chargeBudgetJ hAT hC hni hnsw hmrt hmb used) ?_
  rintro r ⟨h1, σ', h2, h3, h4⟩
  exact ⟨h1, σ', by rw [e2]; exact h2, h3, h4⟩

set_option maxHeartbeats 8000000 in
/-- **`charge_budget` with `can_timeout_fault = true` from a `JHole`, round-robin
current SC**: ScChargeR's `JAtZ.chargeBudgetRJ` at the state after
`update_timestamp`. -/
theorem JHole.chargeBudgetRJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hp : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod = 0)
    (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, htw, -, hact, hnr, -⟩ := CurInv.facts hS Hh.inv hC
  have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  obtain ⟨e1, e2⟩ := charge_budget_rr (ar := arI) s a σ hS hR Hh.nsc Hh.inv hscC htw hS.idle hact hnr hmrt hmb
    (by rw [← hs.curSc]; exact hid) (fun x n hx => hp x n (by rw [hs.curSc]; exact hx)) used
  rw [e1]
  refine WP.spec_mono (Hh.chargeBudgetJ hAT hC hni hnsw hmrt hmb used) ?_
  rintro r ⟨h1, σ', h2, h3, h4⟩
  exact ⟨h1, σ', by rw [e2]; exact h2, h3, h4⟩

/-- **`charge_budget` with `can_timeout_fault = true` from a `JHole` when no
timeout fault can be raised** (ScChargeR's `NoTmoSend`). -/
theorem JHole.chargeBudgetTJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnt : NoTmoSend σ) (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  rcases hnt with h | h
  · exact Hh.chargeBudgetNJ hAT hC hni hnsw hmrt hmb h used
  · exact Hh.chargeBudgetRJ hAT hC hni hnsw hmrt hmb h used

set_option maxHeartbeats 8000000 in
/-- **`check_budget` charging from a `JHole`** (KENTRY-PLAN item 10's false
branch and the preemption point's schedulable branch, without an endpoint
timeout handler or with a round-robin current SC, `NoTmoSend`): when FL4's `check_budget` returns `false` at the state
after `update_timestamp`, the head was insufficient, the spec's
`check_budget` returns `false` too (the charge of the consumed time with
`can_timeout_fault = true`, `JHole.chargeBudgetTJ`), the arch state is kept
and `JAtZ` holds after. -/
theorem JHole.checkBudgetF {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnt : NoTmoSend σ) :
    sched.check_budget st arI s a ⦃ r => r.1 = false → r.2.2 = a ∧ ∃ σ',
      Fl4Spec.checkBudget (Z := Unit) σ = ({(false, σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.2.1 a σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  have hax : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk hax _ hmb) ?_
  intro b hb
  by_cases hbt : b = true
  · rw [if_pos hbt, is_cur_domain_expired_eq]
    simp only [bind_ok]
    refine (WP.spec_ok _).2 ?_
    intro h; exact absurd h (by simp)
  · rw [if_neg hbt]
    have hbf : b = false := by simpa using hbt
    subst hbf
    refine WP.spec_bind (Hh.chargeBudgetTJ hAT hC hni hnsw hmrt hmb hnt (nodeW st s Z.c layout.node.CONSUMED)) ?_
    rintro ⟨s1, a1⟩ ⟨ha1, σ', h1, hK, J'⟩
    refine (WP.spec_ok _).2 fun _ => ⟨ha1, σ', ?_, hK, J'⟩
    have hb' : Fl4Spec.getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(false, σ)}, False) := by
      rw [hs.curSc, hs.consumed]; exact hb
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime true σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    unfold Fl4Spec.checkBudget
    rw [nd_gets_bind, nd_gets_bind, Notif.nd_bind_one hb']
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nd_gets_bind, Notif.nd_bind_one h1']
    rfl

end

end

end Fl4Proofs.P3
