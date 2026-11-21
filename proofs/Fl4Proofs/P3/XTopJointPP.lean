/-
P3 (DESIGN.md §9), CSpace: **the preemption point at `J`** (`JPreemptHyp`,
XTopJointDelR), by its steps.

* `JAtZ.workUnitsJ`: a write of the kernel-global `WORK_UNITS` word keeps
  `JAtZ` (a kernel-state step, `jowes_ks`; no relation reads the word).
* `NowAgree` [P]: FL4's `now` agrees with the spec's `get_current_time` (the
  spec's clock is an oracle of its machine state; the model has no relation
  between the arch state and it), and time does not go back.
* `update_timestamp_fr`: `update_timestamp` writes the current core's
  `CUR_TIME` and `CONSUMED` only, and keeps `AR` (`ARKeep.now`).
* `JAtZ.timestampJ`: `update_timestamp` from `JAtZ` refines
  `update_time_stamp`, with `JAtZ` after whenever `OffOK` holds after (the
  current SC's budget covering the consumed time: the preemption point checks
  it). An SC step (`ScTKw` with no object changed, the writes in `TFoot`):
  `xtop_sc_step`, `ScAll.of_k`, `JAtZ.sc_frame` and the `sc_*` frames;
  `Inv`, `CurInv`, `ActIdle` by `update_timestamp_refines`; the fields that
  read neither the time nor the consumed time kept as they are; `OffOK` and
  `CurOwnW` (its owner off the release queue once time is consumed) asked
  after.
* `JAtZ.ppJ`: the preemption point from `JAtZ` and `PPR0` (ScPPR), `JAtZ`
  and `PPR0` after when not preempted. When it does not preempt, the current
  SC is active and its head sufficient for the consumed time; the head's
  readiness (`OffOK`) moves with the time (`rdy_shift`: the time and the
  consumed time grow alike), from `OffOK` before for a positive consumed
  time, from `PPR0` for a zero one; so does `CurOwnW`'s release-queue clause.
* `jPreemptHyp_of`: `JPreemptHyp` (at `WJR`, the loop carrying `PPR0`) from
  the platform's facts (`PPPlat`, `ARKeep`, totality) [P] alone.
-/
import Fl4Proofs.P3.XTopJointDelR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem workUnits_val {kb : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) :
    (core.num.U64.wrapping_add kb layout.ks.WORK_UNITS).val = kb.val + 40 := by
  simp [core.num.U64.wrapping_add_val_eq, layout.ks.WORK_UNITS, U64.size_def, U64.numBits]; omega

set_option maxHeartbeats 4000000 in
/-- **A write of `WORK_UNITS` keeps `JAtZ`** (module docstring). -/
theorem JAtZ.workUnitsJD {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (v : U64) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D
        (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) v) a σ := by
  have hX := J.xtop
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hv := workUnits_val hf
  set w := core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS with hwd
  have ha : P1.Aligned w := by unfold P1.Aligned; rw [hv]; omega
  set s' := L.wr s w v with hs'
  have hw : P1.WritesIn st s s' (KsW (L.ksb s)) :=
    (P1.writesIn_wr ha).mono fun b hb => ⟨40#u64, by decide, by decide, by decide, by rw [hb, hv]; rfl,
      Or.inl (by decide)⟩
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ (L.ksb s).val + 40 → L.mem s' b = L.mem s b := fun b hb hb' =>
    P1.LawfulStore.mem_wr_ne ha hb (by rw [hv]; omega)
  have hirq : IrqRel (L.mem s') (L.ksb s) σ := by
    have hR := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, hR.node⟩
    have e := irqStA_val hf hi
    rw [hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)]
    exact hR.st i hi
  have hio : IoRel (L.mem s') (L.ksb s) σ := by
    have hR := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hw' : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have e := ioA_val hf hw'
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)]
    exact hR p hp
  have hdk : DK4 (L := L) s s' := ⟨by rw [hs', P1.LawfulStore.ksb_wr], fun o ho => by
    obtain ⟨h1, h2⟩ := domOffs0_lt ho
    have e : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have h40 : o.val ≠ 40 := by
      simp only [domOffs0, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    exact hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)⟩
  have hD := hX.rel.2.2.2.1
  have hAR := hX.fin.1.1.2.2.2.2.2.2
  have hX1 : XTopAt (L := L) AR Z s' a σ := XTopAt.ksStep hX J.ks hw (KsStep.refl σ) hirq hio
    (hD.frame (fun o ho => hdk.2 o ho) rfl rfl) hAR
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    hX.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨Ac', Lst', R⟩ := jowes_ksD arI s s' a a σ σ hw (KsStep.refl σ) Z H Cs Ac Lst D rfl J hX1
  exact ⟨Ac', Lst', J.cs_frameK hw.1 hX1 (KBack.of_kheap rfl) (IpcFrKeep.of_kheap rfl) (JCs.same J hSS (KSz.of_kheap rfl)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J.vkeep_of hw fun _ hb => J.ksW_nv hb)
    hSS (dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb) rfl⟩

/-- `JAtZ.workUnitsJD` with the dead set existential. -/
theorem JAtZ.workUnitsJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (v : U64) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D'
        (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) v) a σ :=
  let ⟨Ac', Lst', J'⟩ := J.workUnitsJD arI v; ⟨Ac', Lst', D, J'⟩


/-- **FL4's clock agrees with the spec's** [P] (module docstring). -/
def NowAgree (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  arI.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ∧
    ms.underlyingMemory = σ.machineState.underlyingMemory ⦄

/-- **`update_timestamp`'s writes and arch state** (module docstring). -/
theorem update_timestamp_fr (hAK : ARKeep arI AR) {T : Set U64} (s : S) (a : A) {c : Fl4Spec.Cr3} (hc : AR a c)
    (hN : P1.NodePlaced st T s (L.cpu s)) :
    sched.update_timestamp st arI s a ⦃ r => P1.WritesIn st s r.1 (fun b =>
      b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨ b = L.nodeAt s (L.cpu s) layout.node.CONSUMED) ∧ AR r.2 c ⦄ := by
  unfold sched.update_timestamp
  step with sched.cur_time.spec as ⟨prev⟩
  refine WP.spec_bind (hAK.now a c hc) ?_
  rintro ⟨now, a1⟩ ha1
  try simp only [WP.uncurry'_pair]
  step with P1.LawfulStore.cur_cpu_spec as ⟨c', ec⟩
  step with obj.node_set.spec as ⟨s1, e1⟩
  subst ec e1
  have w1 : P1.WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
      (fun b => b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨ b = L.nodeAt s (L.cpu s) layout.node.CONSUMED) :=
    (P1.writesIn_wr (P1.nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))).mono
      fun b e => Or.inl e
  step as ⟨used, _⟩
  step with sched.consumed.spec as ⟨i⟩
  step as ⟨total, _⟩
  step with sched.set_consumed.spec as ⟨s2, e2⟩
  subst e2
  have hN1 : P1.NodePlaced st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)
      (L.cpu (L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now)) := by
    rw [P1.LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)
  have w2 := (P1.writesIn_wr (st := st) (s := L.wr s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) now) (v := total)
    (P1.nodeAt_aligned (off := layout.node.CONSUMED) hN1 (by simp [layout.node.CONSUMED])
      (by simp [layout.node.CONSUMED])))
  have w12 : P1.WritesIn st s _ (fun b =>
      b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨ b = L.nodeAt s (L.cpu s) layout.node.CONSUMED) :=
    (w1.trans w2).mono fun b hb => hb.elim id fun e => Or.inr (by
      rw [e]; show L.nodeAt _ (L.cpu _) _ = _
      rw [P1.LawfulStore.cpu_wr, P1.nodeAt_of_ksb (L.ksb_wr _ _ _)])
  rw [Sched.num_domains_eq, if_neg (by decide), WP.spec_ok]
  exact ⟨w12, ha1⟩

/-- **`update_time_stamp`'s outcome**, from the clock's (one domain). -/
theorem Sched.updateTimeStamp_eq' {σ : Fl4Spec.State Unit} {now : Fl4Spec.Word} {ms : Fl4Spec.MachineState}
    (hnd : Fl4Spec.numDomains = 1)
    (hm : Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ = ({(now, { σ with machineState := ms })}, False)) :
    Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), { { { σ with machineState := ms } with curTime := now } with
      consumedTime := σ.consumedTime + (now - σ.curTime) })}, False) := by
  set σm : Fl4Spec.State Unit := { σ with machineState := ms } with hσm
  set σ' : Fl4Spec.State Unit := { { σm with curTime := now } with
    consumedTime := σm.consumedTime + (now - σ.curTime) } with hσ'
  show _ = ({((), σ')}, False)
  unfold Fl4Spec.updateTimeStamp
  rw [nd_gets_bind, nd_bind_one hm, nd_pure_bind',
    nd_bind_one (rfl : Fl4Spec.NonDet.modify (fun s : Fl4Spec.State Unit => { s with curTime := now }) σm =
      ({((), { σm with curTime := now })}, False)),
    nd_bind_one (rfl : Fl4Spec.NonDet.modify (fun s : Fl4Spec.State Unit =>
      { s with consumedTime := s.consumedTime + (now - σ.curTime) }) { σm with curTime := now } =
      ({((), σ')}, False)), nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  rw [if_neg (by rw [hnd]; decide)]
  rfl

set_option maxHeartbeats 8000000 in
/-- **`update_timestamp` at `J`** (module docstring). -/
theorem JAtZ.timestampJD {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hnow : NowAgree arI a σ) :
    sched.update_timestamp st arI s a ⦃ r => ∃ σ', Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
      σ'.archState = σ.archState ∧
      σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory ∧
      (Sched.OffReady σ → Sched.OffReady σ') ∧
      ∀ (ms2 : Fl4Spec.MachineState) (a2 : A), ms2.underlyingMemory = σ.machineState.underlyingMemory →
        (AR r.2 σ.archState.x64CurrentCr3 → AR a2 σ.archState.x64CurrentCr3) →
        XTopAt (L := L) AR Z r.1 a2 { σ' with machineState := ms2 } ∧
        (Sched.OffOK { σ' with machineState := ms2 } → Sched.CurOwnW Z.T Z.C { σ' with machineState := ms2 } →
          ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
            JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.1 a2 { σ' with machineState := ms2 }) ⦄ := by
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
  -- the writes: two words of the current core's node
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
  have hX' : XTopAt (L := L) AR Z s' a2 σ' := xtop_sc_step hX J.ip J.nk hwT (ct := σ.curThread) (hK.mono fun _ h => h.elim) hS2 hR2 fun _ => hAa2 hAR'
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    ⟨hw.1, fun b hb => hw.mem_eq (P1.dbgW_aligned J.blk hb) fun h' => by
      rcases h' with rfl | rfl
      · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, J.kern.cpuCs, layout.node.CUR_TIME,
          by simp [layout.node.CUR_TIME], by simp [layout.node.CUR_TIME], rfl⟩)) hb
      · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, J.kern.cpuCs, layout.node.CONSUMED,
          by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], rfl⟩)) hb⟩
  refine ⟨hX', fun hO' hOw' => ?_⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS2, hR2, hN2, hI2⟩, hwK,

      ⟨fun p => ORel.refl _ _, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hF : FK σ σ' := ⟨rfl, rfl, rfl⟩
  have hL : LK (fun _ => False) σ σ' := fun p => Or.inr (OL.refl _)
  have hAI' : ActIdle σ' := hA2 J.act
  have hDead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hwT hK (fun _ _ h => h.elim) hL hF hAI'.1 hY'
      ((SOK.ykeep (f := (true, true)) ⟨fun p => ORel.refl _ _, rfl, rfl, rfl, rfl, rfl⟩ rfl).dk q.bv) (fun h => h)
      (J.jcov.dead q hq)
  -- the node-0 debug word
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
  exact ⟨Ac, Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hwT hDead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2)) (J.sc_kern hwT hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hwT hK hDbg) hN2 hI2 (J.cur.imp id hC2) hOw' hO' hAI' (J.bsa.tkw hK fun p y n h hy => ⟨y, h, hy, fun _ h => h, id⟩) J.curRun hBlk'
    hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩



set_option maxHeartbeats 4000000 in
/-- `JAtZ.timestampJD` with the dead set existential. -/
theorem JAtZ.timestampJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hnow : NowAgree arI a σ) :
    sched.update_timestamp st arI s a ⦃ r => ∃ σ', Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
      σ'.archState = σ.archState ∧
      σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory ∧
      (Sched.OffReady σ → Sched.OffReady σ') ∧
      ∀ (ms2 : Fl4Spec.MachineState) (a2 : A), ms2.underlyingMemory = σ.machineState.underlyingMemory →
        (AR r.2 σ.archState.x64CurrentCr3 → AR a2 σ.archState.x64CurrentCr3) →
        XTopAt (L := L) AR Z r.1 a2 { σ' with machineState := ms2 } ∧
        (Sched.OffOK { σ' with machineState := ms2 } → Sched.CurOwnW Z.T Z.C { σ' with machineState := ms2 } →
          ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
            JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 a2 { σ' with machineState := ms2 }) ⦄ :=
  WP.spec_mono (J.timestampJD arI hAK hA hnd hnow) fun _ ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
    ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, fun ms2 a2 hm ha =>
      let ⟨x1, x2⟩ := h9 ms2 a2 hm ha
      ⟨x1, fun hO hOw => let ⟨Ac', Lst', J'⟩ := x2 hO hOw; ⟨Ac', Lst', D, J'⟩⟩⟩

end

/-- **The spec's preemption point past the work-unit limit**: after the time
update (`σ1`) and the IRQ check (`σ2`), an error exactly when an IRQ is
pending, the domain expired, or the current SC is not active and sufficient
(for `Z = Unit`, `work_units_limit_reached` is any boolean). -/
theorem pp_over {σ σ1 σ2 : Fl4Spec.State Unit} {irq : Option Fl4Spec.Irq}
    (hE : Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), σ1)}, False))
    (hI : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ1 = ({(irq, σ2)}, False)) {act : Bool}
    (ha : Fl4Spec.readScActive (Z := Unit) σ2.curSc σ2 = some act) :
    NHas (Fl4Spec.preemptionPoint (Z := Unit)).run σ (fun y => y =
      ((if irq ≠ none ∨ Fl4Spec.isCurDomainExpired σ2 = true ∨
          ¬(act = true ∧ Fl4Spec.readScRefillSufficient (Z := Unit) σ2.curSc σ2.consumedTime σ2 = some true)
        then .error () else .ok ()), σ2)) := by
  unfold Fl4Spec.preemptionPoint
  apply nhasE_bind
  apply nhas_liftE
  unfold Fl4Spec.doExtendedOp
  refine nhas_bind (nhas_det rfl ?_)
  refine nhas_bind ⟨(((), σ), σ), ⟨rfl, rfl⟩, nhas_det rfl ?_⟩
  show NHas (Fl4Spec.orChoiceE _ _ _).run { σ with exst := σ.exst } _
  unfold Fl4Spec.orChoiceE
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det rfl ?_
  apply nhasE_bind
  apply nhas_liftE
  refine ⟨((true, σ), σ), ⟨⟨trivial, rfl⟩, rfl⟩, ?_⟩
  dsimp only [↓reduceIte]
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_bind (nhas_det rfl ?_)
  refine nhas_bind ⟨(((), σ), σ), ⟨rfl, rfl⟩, nhas_det rfl ?_⟩
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det hE ?_
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det hI ?_
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det rfl ?_
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det rfl ?_
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det rfl ?_
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det (show Fl4Spec.getScActive (Z := Unit) σ2.curSc σ2 = ({(act, σ2)}, False) by
    unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [ha]; rfl) ?_
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det rfl ?_
  dsimp only
  unfold Fl4Spec.NonDetE.whenE
  split
  · rename_i h
    refine nhas_det rfl ?_
    simp only [if_pos h]
  · rename_i h
    refine nhasE_pure ?_
    simp only [if_neg h]


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The platform's clock, IRQ line and minimum budget agree with the
spec's** [P] (`NowAgree`; the spec's `get_active_irq` is an oracle of its
machine state; the IRQ check keeps `AR`). -/
structure PPPlat (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  now : ∀ a σ, NowAgree arI a σ
  irq : ∀ (a : A) (σ : Fl4Spec.State Unit), arI.irq_pending a ⦃ r => ∃ irq ms,
    Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
    (r.1 = true ↔ irq ≠ none) ∧ ms.underlyingMemory = σ.machineState.underlyingMemory ⦄
  irqAR : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄
  minBudget : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄

/-- The current SC is one of `C` (its owner's, or `CurOwnW`'s unowned SC). -/
theorem cursc_in {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hO : Sched.CurOwnW T C σ) : nodeW st s c layout.node.CUR_SC ∈ C := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rcases hO with ⟨u, hu, xt, hk, hxs, -, -⟩ | ⟨⟨c', hc', hcv⟩, -⟩
  · obtain ⟨x', hk', -, -, h3, -⟩ := hs.tcb u hu
    rw [hk] at hk'; cases hk'
    rw [h3, hs.curSc] at hxs
    obtain ⟨h0, hbv⟩ := Notif.optRef_some hxs
    have := hs.scMem u hu h0
    rwa [P1.eq_of_bv hbv] at this
  · rw [hs.curSc] at hcv
    rwa [← P1.eq_of_bv hcv]

theorem readScActive_eq' {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) : Fl4Spec.readScActive (Z := Unit) p σ = some (Fl4Spec.scActive x) := by
  show Option.bind (Fl4Spec.readSchedContext p σ) (fun sc => Fl4Spec.Lookup.oreturn (Fl4Spec.scActive sc) σ) = _
  rw [Sched.readSchedContext_eq hk]; rfl

theorem getsThe_some {σ : Type} {α : Type} {f : σ → Option α} {s : σ} {v : α}
    (h : Fl4Spec.NonDet.getsThe f s = ({(v, s)}, False)) : f s = some v := by
  unfold Fl4Spec.NonDet.getsThe at h
  cases e : f s with
  | none => rw [e] at h; unfold Fl4Spec.NonDet.assertOpt Fl4Spec.NonDet.fail at h; simp at h
  | some w =>
    rw [e] at h; unfold Fl4Spec.NonDet.assertOpt at h
    have := congrArg (fun q => (v, s) ∈ q.1) h
    simp [Fl4Spec.NonDet.pure] at this
    rw [this]

/-- A nonzero consumed time is positive. -/
theorem bv_pos {x : BitVec 64} (h : ¬ x = 0) : 0 < x := by
  rw [BitVec.lt_def]
  have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  show 0 < x.toNat; omega

theorem bv_add0 (x : BitVec 64) : x + 0 = x := BitVec.add_zero x

/-- **The head's readiness moved by the elapsed time**: a head ready with
the consumed time stays so when the time and the consumed time grow by the
same amount (`n - t`, `t ≤ n`), in wrapping arithmetic. -/
theorem rdy_shift {r c t n : BitVec 64} (h1 : r + c ≤ t) (h2 : r ≤ t) (htn : t ≤ n) :
    r + (c + (n - t)) ≤ n ∧ r ≤ n := by
  have hr := r.isLt; have hc := c.isLt; have ht := t.isLt; have hn := n.isLt
  simp only [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow] at h1 h2 htn hr hc ht hn ⊢
  constructor <;> omega

set_option maxHeartbeats 16000000 in
/-- **The preemption point from `JAtZ`** (module docstring): an outcome of
the spec's of the same kind, `XTopAt` after, and `JAtZ` after when not
preempted. -/
theorem JAtZ.ppJD {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hP : PPPlat arI AR) (hRd : PPR0 σ) :
    sched.preemption_point st arI s a ⦃ r => ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
      XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧
      (r.1 = .Ok () → (∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.2.1 r.2.2 σ') ∧ PPR0 σ') ⦄ := by
  generalize hPP : ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 = PPs
  unfold sched.preemption_point
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨w, _⟩
  step with obj.ks_set.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨Ac1, Lst1, J1⟩ := J.workUnitsJD arI w
  split
  swap
  · rw [WP.spec_ok]
    obtain ⟨y, hy, rfl⟩ := pp_ok σ
    rw [hPP] at hy
    exact ⟨σ, Or.inl ⟨rfl, hy⟩, J1.xtop, fun _ => ⟨⟨Ac1, Lst1, J1⟩, hRd⟩⟩
  step with obj.ks_set.spec as ⟨s2, e2⟩
  subst e2
  obtain ⟨Ac2, Lst2, J2⟩ := J1.workUnitsJD arI 0#u64
  refine WP.spec_bind (J2.timestampJD arI hAK hA hnd (hP.now a σ)) ?_
  rintro ⟨s3, a1⟩ ⟨σ1, hE1, hk1, hcs1, hrq1, hct1, har1, hum1, -, hK⟩
  -- the time and the consumed time after the update
  obtain ⟨r0, -, ms0, hm0, hle0, -⟩ := spec_exists (hP.now a σ)
  have hσ1 := the_result (updateTimeStamp_eq' hnd hm0) hE1
  have hct1' : σ1.curTime = r0.1.bv := by rw [hσ1]
  have hcn1 : σ1.consumedTime = σ.consumedTime + (r0.1.bv - σ.curTime) := by rw [hσ1]
  -- the arch relation after the time update
  have hX1 := (hK σ1.machineState a1 hum1 id).1
  have hAR1 : AR a1 σ.archState.x64CurrentCr3 := by
    have h := hX1.fin.1.1.2.2.2.2.2.2
    rw [show ({ σ1 with machineState := σ1.machineState } : Fl4Spec.State Unit).archState = σ.archState from har1] at h
    exact h
  -- the IRQ check on the spec side
  obtain ⟨⟨b2, a2⟩, hip, ⟨irq, ms, hIq, hiff, hum⟩, hAR2⟩ :=
    spec_exists (WP.spec_and (hP.irq a1 σ1) (hP.irqAR a1 _ hAR1))
  have hum' : ms.underlyingMemory = σ.machineState.underlyingMemory := hum.trans hum1
  set σ2 : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσ2
  obtain ⟨hX2, -⟩ := hK ms a1 hum' id
  obtain ⟨hX2', hJ2'⟩ := hK ms a2 hum' (fun _ => hAR2)
  have hS2 := hX2.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS2.lists
  -- the current SC's owner
  have hOw2 : CurOwnW Z.T Z.C σ2 := by
    rcases J.own with ⟨u, hu, xt, hk, hxs, hb', hnr⟩ | ⟨⟨c', hc', hcv'⟩, h2⟩
    · refine Or.inl ⟨u, hu, xt, ?_, ?_, fun x n h => hb' x n ?_, fun _ => ?_⟩
      · show σ1.kheap u.bv = _; rw [hk1]; exact hk
      · show _ = some σ1.curSc; rw [hcs1]; exact hxs
      · rw [← hk1, ← hcs1]; exact h
      · show u.bv ∉ σ1.releaseQueue; rw [hrq1]
        by_cases h0 : σ.consumedTime = 0
        · exact (hRd.2 h0).2 u.bv xt hk hxs
        · exact hnr (bv_pos h0)
    · exact Or.inr ⟨⟨c', hc', hcv'.trans hcs1.symm⟩, fun x n h => h2 x n (by rw [← hk1, ← hcs1]; exact h)⟩
  -- FL4's IRQ read (first, in C's and the spec's order)
  refine WP.spec_bind (Pₘ := fun q => q = (b2, a2)) (by rw [hip, WP.spec_ok]) ?_
  rintro ⟨b2', a2'⟩ he
  cases he
  try dsimp only
  -- FL4's reads
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sched.consumed.spec' as ⟨cv, hcv⟩
  step with sporadic.sc_active.spec' as ⟨b, hb⟩
  rw [hc.cur] at hsc hcv
  subst hsc hcv
  have hscC : nodeW st s3 Z.c layout.node.CUR_SC ∈ Z.C := cursc_in hS2 hOw2
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hkx' : σ2.kheap σ2.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hab : b = Fl4Spec.scActive x := by
    rw [hb]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  subst hab
  obtain ⟨y, hy, rfl⟩ := pp_over hE1 hIq (readScActive_eq' hkx')
  rw [hPP] at hy
  have hexp : Fl4Spec.isCurDomainExpired σ2 = false := by
    unfold Fl4Spec.isCurDomainExpired; simp [hnd]
  rw [is_cur_domain_expired_eq]
  cases hact : Fl4Spec.scActive x
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, ite_self, WP.spec_ok]
    refine ⟨σ2, Or.inr ⟨by simp, ?_⟩, hX2', fun h => by simp at h⟩
    rw [if_pos (by simp [hact])] at hy
    exact hy
  simp only [↓reduceIte]
  refine WP.spec_bind (sufficient_refines s3 a2 σ2 hS2 hscC hkx hact _ (hP.minBudget a2)) ?_
  intro ok1 hsuf
  have hrs : Fl4Spec.readScRefillSufficient (Z := Unit) σ2.curSc σ2.consumedTime σ2 = some ok1 := by
    rw [hs.curSc, hs.consumed]; unfold Fl4Spec.getScRefillSufficient at hsuf; exact getsThe_some hsuf
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  cases b2
  swap
  · rw [if_pos rfl, WP.spec_ok]
    rw [if_pos (Or.inl (hiff.1 rfl))] at hy
    exact ⟨σ2, Or.inr ⟨by simp, hy⟩, hX2', fun h => by simp at h⟩
  rw [if_neg (by simp)]
  have hirq : irq = none := by
    by_contra h; exact absurd (hiff.2 h) (by simp)
  cases hok : ok1
  · rw [if_neg (by simp), WP.spec_ok]
    refine ⟨σ2, Or.inr ⟨by simp, ?_⟩, hX2', fun h => by simp at h⟩
    rw [if_pos (by simp [hrs, hok])] at hy
    exact hy
  · rw [if_pos rfl, WP.spec_ok]
    rw [if_neg (by simp [hirq, hexp, hact, hrs, hok])] at hy
    have hx' := hx.strong hact
    have hne : x.scRefills ≠ [] := by rw [hx'.refills]; exact refills_ne hx'.wf
    have hr2 := getsThe_some (getScRefillSufficient_eq hkx' hne σ2.consumedTime)
    rw [hrs, hok] at hr2
    -- the current SC's head before the update, then after
    have hkσ : σ.kheap σ.curSc = some (.schedContext x n) := by
      rw [← hk1, ← hcs1]; exact hkx'
    have hrd : (Fl4Spec.refillHd x).rTime + σ.consumedTime ≤ σ.curTime ∧ (Fl4Spec.refillHd x).rTime ≤ σ.curTime := by
      by_cases h0 : σ.consumedTime = 0
      · have h := (hRd.2 h0).1 x n hkσ hact
        simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h
        rw [h0, bv_add0]; exact ⟨h, h⟩
      · obtain ⟨-, h1, h2⟩ := J.off (bv_pos h0) x n hkσ (fun _ => hact)
        simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h1 h2
        exact ⟨h1, h2⟩
    obtain ⟨hs1, hs2⟩ := rdy_shift hrd.1 hrd.2 hle0
    have e1 : σ2.consumedTime = σ.consumedTime + (r0.1.bv - σ.curTime) := hcn1
    have e2 : σ2.curTime = r0.1.bv := hct1'
    have hO2 : OffOK σ2 := by
      intro _ y m hy' _
      rw [hkx'] at hy'; cases hy'
      refine ⟨(Option.some.inj hr2).symm, ?_, ?_⟩
      · simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq]; rw [e1, e2]; exact hs1
      · simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0]; rw [e2]; exact hs2
    have hP2 : PPR0 σ2 := by
      refine ⟨by rw [hσ2, hσ1]; exact hRd.1, fun _ => ?_⟩
      refine ⟨fun y m hy' _ => ?_, fun u xt hu hus hur => ?_⟩
      · rw [hkx'] at hy'; cases hy'
        simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0]; rw [e2]; exact hs2
      · have hu' : σ.kheap u = some (.tcb xt) := by rw [← hk1]; exact hu
        have hus' : xt.tcbSchedContext = some σ.curSc := by rw [← hcs1]; exact hus
        have hur' : u ∉ σ.releaseQueue → False := fun h => h (by rw [← hrq1]; exact hur)
        by_cases h0 : σ.consumedTime = 0
        · exact hur' ((hRd.2 h0).2 u xt hu' hus')
        · obtain ⟨y', n', hy', hyt⟩ := J.inv.back u xt _ hu' hus'
          rcases J.own with ⟨u0, -, xt0, -, -, hb0, hnr0⟩ | ⟨-, hun⟩
          · have := hb0 y' n' hy'
            rw [hyt] at this; cases this
            exact hur' (hnr0 (bv_pos h0))
          · rw [hun y' n' hy'] at hyt; cases hyt
    refine ⟨σ2, Or.inl ⟨by simp, hy⟩, hX2', fun _ => ⟨hJ2' hO2 hOw2, hP2⟩⟩

set_option maxHeartbeats 4000000 in
/-- `JAtZ.ppJD` with the dead set existential. -/
theorem JAtZ.ppJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hP : PPPlat arI AR) (hRd : PPR0 σ) :
    sched.preemption_point st arI s a ⦃ r => ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
      XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧
      (r.1 = .Ok () → (∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧ PPR0 σ') ⦄ :=
  WP.spec_mono (J.ppJD arI hAK hA hnd hP hRd) fun _ ⟨σ', h1, h2, h3⟩ =>
    ⟨σ', h1, h2, fun hr => let ⟨⟨Ac', Lst', J'⟩, hp⟩ := h3 hr; ⟨⟨Ac', Lst', D, J'⟩, hp⟩⟩


set_option maxHeartbeats 4000000 in
/-- **`JPreemptHyp` from the preemption point at `J`** (`JAtZ.ppJ`, at
`WJR`: `PPR0` carried by the loop): the platform's [P] (`PPPlat`, `ARKeep`,
totality). The slots kept: the preemption point writes `WORK_UNITS` and the
current core's time words only (P1's `preemption_point.pp`). -/
theorem jPreemptHyp_of (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) (th : TypedHeap) :
    JPreemptHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G _ ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩
  obtain ⟨⟨r1, s', a'⟩, hr, ⟨σ', hcase, hX', hJ'⟩, -, hw⟩ :=
    spec_exists (WP.spec_and (J.ppJ arI hAK hA hnd hP hp0)
      (P1.sched.preemption_point.pp hA s a J.blk))
  rw [hr, WP.spec_ok]
  simp only at hcase hX' hJ' hw ⊢
  have hX := J.xtop
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hN : P1.NodePlaced st (Z.mv G V).T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ (hc.cur ▸ J.kern.cpuCs)
  have hSS : SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') := hX.slotsSame_of hw fun b hb => by
    have hf := J.kern.ksbFit
    rcases hb with rfl | rfl | rfl
    · have := workUnits_val hf; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e := P1.nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
  have hks : L.ksb s' = L.ksb s := hw.1
  refine ⟨hth ▸ hSS, σ', hcase, hth ▸ hX'.rel.2.1, ?_⟩
  rcases hcase with ⟨rfl, hm0⟩ | ⟨rfl, hm⟩
  · obtain ⟨⟨Ac', Lst', D', J'⟩, hp'⟩ := hJ' rfl
    exact ⟨V, Ac', Lst', D', J', by rw [hks]; exact hkb, Vs.ake_preemptionPoint'.noSwitch hm0 hns, SpecGlob.pp hm0 hsg, hp'⟩
  · exact ⟨s, a, σ, ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hr, hm, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩


end

end

end Fl4Proofs.P3
