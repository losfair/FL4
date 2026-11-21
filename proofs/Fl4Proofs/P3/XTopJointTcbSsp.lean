/-
P3 (DESIGN.md §9), TCB: **SetSchedParams of the Thread cap at `J`**
(`tcb_set_sched_paramsJ`).

* `MidK.midN`: ScMidKeep's `MidK.mid` with the resume action at the start
  weakened to "no switch pending" (a reschedule may be pending: the
  fault-handler install's `cancel_all_ipc` asks for one).
* `JAtZ.bindTcbJ`: `schedcontext::bind_tcb` at `J` (as XTopJointFinThreadSc's
  `JAtZ.unbindTcbJ`): `bind_tcb_refines` (the relations),
  `bind_tcb.blkK` (`BlkOK` and the footprint `Foot`), `xtop_sc_step`, `ScAll.of_k`, `BlockedScActive`
  by `bka_schedContextBindTcb`, the mid-entry facts by
  `mka_schedContextBindTcb` and `MidK.midN`, the dead set by
  `deadP_sc_step` outside the bound pair and the pair covered by its caps
  (`cover_cap`), core 0's `DEBUG_TCBS` word by `JAtZ.kw_dbg`.
* `P1.schedcontext.bind_tcb.blkK`: P1's `bind_tcb.blkF` with the tighter
  footprint `Foot` (no debug-list word) when the thread's affinity is
  already the SC's core (at `JAtZ` by `SchedRel`'s one core): `migrate_tcb`
  is then a no-op (`smp.migrate_tcb.frame`).
-/
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.XTopJointTcbPrio
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- **`MidK.mid` with no switch pending at the start** (instead of the
resume action; the switch target's clause of `ActSched` is the only use). -/
theorem MidK.midN {T : Set U64} {σ σ' : State Unit} (hK : MidK σ σ')
    (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) (hC : CurInv σ) (hO : OffOK σ) (hA : ActIdle σ) (hI : Inv σ)
    (hcT : ∃ u ∈ T, u.bv = σ.curThread) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧
      (σ'.schedulerAction = .chooseNewThread → CurOwn T σ') ∧ OffOK σ' ∧ ActIdle σ' := by
  obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
  obtain ⟨y0, n0, hy0⟩ := hC.sc
  obtain ⟨xt', hkt', e1, e2⟩ := hK.ctT xt hkt
  obtain ⟨y0', hy0', f1, f2, f3⟩ := hK.cscS y0 n0 hy0
  have hnr' : ∀ hcn : σ'.schedulerAction ≠ .chooseNewThread ∨ 0 < σ'.consumedTime,
      σ.curThread ∉ σ'.releaseQueue := by
    intro hc hm
    rcases hK.rq _ hm with h | ⟨-, h | ⟨h0, hcn⟩⟩
    · exact hC.notRel h
    · exact h rfl
    · rcases hc with hc | hc
      · exact hc hcn
      · rw [h0] at hc; simp at hc
  refine ⟨?_, fun hcn => ?_, fun hpos y n hy _ => ?_, ⟨fun t ht => ?_, ?_⟩⟩
  · by_cases hcn : σ'.schedulerAction = .chooseNewThread
    · exact Or.inl hcn
    right
    refine ⟨⟨xt', by rw [hK.ct]; exact hkt', by rw [e1, hK.csc]; exact hsc, by rw [e2]; exact hnb⟩,
      ⟨y0', n0, by rw [hK.csc]; exact hy0'⟩, fun hid y m hy => ?_, fun hm => hnr' (Or.inl hcn) (by rw [← hK.ct]; exact hm)⟩
    rw [hK.csc, hK.isc] at hid; rw [hK.csc] at hy
    rw [hy0'] at hy; cases hy
    exact f2 (hC.active hid y0 n0 hy0)
  · obtain ⟨u, hu, hub⟩ := hcT
    obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back _ xt σ.curSc hkt hsc
    rw [hy0] at hy1; cases hy1
    refine ⟨u, hu, xt', by rw [hub]; exact hkt', by rw [e1, hK.csc]; exact hsc, fun x n hx => ?_, fun hpos hm => ?_⟩
    · rw [hK.csc, hy0'] at hx; cases hx; rw [f1, hy1t, hub]
    · exact hnr' (Or.inr hpos) (by rw [← hub]; exact hm)
  · have hne : σ'.consumedTime ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hc := hK.consNe hne
    rw [hK.csc, hy0'] at hy; cases hy
    have hpos0 : 0 < σ.consumedTime := by rw [← hc]; exact hpos
    obtain ⟨g1, g2, g3⟩ := hO hpos0 y0 n0 hy0 (fun hid => hC.active hid y0 n0 hy0)
    have hr : refillHd y0' = refillHd y0 := by unfold refillHd; rw [f3 hne]
    rw [hr, hc, hK.time]
    exact ⟨g1, g2, g3⟩
  · exact absurd (hK.sw t ht) (hnsw t)
  · obtain ⟨xi, hki, hsi, hti, hri⟩ := hA.2
    obtain ⟨xi', hki', g1, g2⟩ := hK.idT xi hki
    refine ⟨xi', by rw [hK.idle]; exact hki', by rw [g1, hK.isc]; exact hsi, by rw [g2]; exact hti, fun hm => ?_⟩
    rw [hK.idle] at hm
    rcases hK.rq _ hm with h | ⟨h, -⟩
    · exact hri h
    · exact h rfl

/-- `CurRunM` across a `MidK` step with no switch pending at the start. -/
theorem MidK.curRunM {σ σ' : State Unit} (hK : MidK σ σ') (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u)
    (hC : CurInv σ) (hcr : CurRunM σ) : CurRunM σ' := by
  by_cases hr : σ'.schedulerAction = .resumeCurThread
  · right
    have hr0 : σ.schedulerAction = .resumeCurThread := by
      cases e : σ.schedulerAction with
      | resumeCurThread => rfl
      | chooseNewThread => rw [hK.cn e] at hr; cases hr
      | switchThread u => exact absurd e (hnsw u)
    rcases hcr with h | h | h
    · exact absurd hr0 h
    · left
      intro x hx
      obtain ⟨xt, hkt, -, -⟩ := hC.tcb
      obtain ⟨y, hy, -, e2⟩ := hK.ctT xt hkt
      rw [hK.ct, hy] at hx; cases hx
      rw [e2]; exact h xt hkt
    · exact Or.inr (by rw [hK.ct, hK.idle]; exact h)
  · exact Or.inl hr

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}

/-- **`bind_tcb` with the footprint `Foot`** when the thread's affinity is
already the SC's core (P1's `schedcontext.bind_tcb.blkF` with `migrate_tcb`
a no-op by `smp.migrate_tcb.frame`): no debug-list word is written. -/
theorem schedcontext.bind_tcb.blkK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac) (haff : L.mem s (affA t) = L.mem s (scCoreA sc)) :
    schedcontext.bind_tcb st ar s a sc t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hO := hX.1
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have ho := h0.omega _ hm
  have hal : Aligned (scTcbA sc) := by
    obtain ⟨hP, hz⟩ := hO.sc sc hsc
    have := (sc_lo hP hz).1
    unfold Aligned; rw [scTcbA_val hP hz]; omega
  have htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hq; exact hB.q t ht hq ht0
  have htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hq; exact hB.r t ht hq ht0
  have hna : L.actionW s ≠ t := fun e => hB.act (e ▸ ht) (by rw [e]; exact ht0)
  have hnb : ∀ y ∈ T, L.mem s (scA y) ≠ sc := fun y hy e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, hc0] at h2; exact (hT y hy).ne0 (by rw [← h2]; rfl)
  have hdisj : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    intro hne b hb
    have := hO.scDisj sc hsc _ hX.2.2.cur hne
    unfold Outside; unfold InSC at hb; omega
  have hcore := hX.2.2.core sc hsc
  have hsA : Sch st s t → sc ∈ Ac := by
    rintro (e | e | e | e | ⟨e1, e2⟩ | e)
    · exact absurd htq e
    · exact absurd htr e
    · exact absurd e hna
    · exact absurd (by rw [e]; exact ht0) hB.idle
    · exact absurd (by rw [e2]; exact ht0) (hB.resume e1)
    · exact hbA e
  -- the two writes
  unfold schedcontext.bind_tcb
  step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
  step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
  subst e1 e2
  have fw2 : Foot st T Cs Sg Scs Z Es s (L.wr (L.wr s (scA t) sc) (scTcbA sc) t) := by
    have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scA t) sc) := by
      rw [scA_eq]; exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
    exact f1.trans (foot_wr hal (kw_sg (hO.fixW sc hsc).1))
  obtain ⟨p8, pB, pX, pS, pSg, -, pfl, pcore, psc, ptc, pact⟩ :=
    donate_pair h0 hB hX.x0 hX.2.2.tsc.x ht0 hS hSg ht hsc hsc0 hnb hcore hdisj hsA
      (fun e => hB.idle (by rw [e]; exact ht0))
  have hsw := bind_swap (L := L) (s := s) (scA_aligned hta) ho.1
    (fun e => out_ne_field (K := 3464#u64) ho ht hta (by simp) e)
  obtain ⟨h2, hB2, hX2, hS2, hSg2⟩ := agree_all p8 pB pX pS pSg (by simp) (by simp) hsw
  set s2 := L.wr (L.wr s (scA t) sc) (scTcbA sc) t with hs2
  have fl2 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => (hsw _ (field_aligned (hT y hy) hK hK8)).trans (pfl y hy K hK hK8 hne)
  have sc2 : L.mem s2 (scA t) = sc := (hsw _ (scA_aligned hta)).trans psc
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hsw _ (h0.omega _ ((objs_omega hO hSg.sub).2 sc hsc).2.1).1).trans pcore
  have ea2 : L.actionW s2 = L.actionW s := by
    have e : L.actionW s2 = L.actionW (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) := by
      unfold LawfulStore.actionW
      rw [show L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION =
        L.nodeAt (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) (L.cpu (L.wr (L.wr s (scTcbA sc) t) (scA t) sc))
          layout.node.SCHED_ACTION by simp [hs2, nodeAt_wr]]
      exact hsw _ (nodeAt_aligned (p8.nodes _ p8.cur) (by rw [act_val]; omega) (by rw [act_val]))
    rw [e, pact]
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact fl2 t ht _ (by simp) (by simp) (fun _ => by simp)
  -- migration
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core2]; exact hcore
  -- the thread already on the SC's core: `migrate_tcb` is a no-op (`migrate_tcb.frame`)
  have haff2 : L.mem s2 (affA t) = cpu := by
    rw [ecpu, core2, ← haff, affA_eq]; exact fl2 t ht _ (by simp) (by simp) (fun _ => by simp)
  refine WP.spec_bind (WP.spec_and (migrate_tail hA s2 a sc t cpu Q R h2 hB2 hX2 hS2 hSg2 ht (by rw [iq2]; exact htq)
    (by rw [iq2]; exact htr) hc' hsc) (smp.migrate_tcb.frame
      hA s2 a t cpu h2.tcbs h2.nodes ⟨hX2.2.2.tm.dn, hX2.2.2.tm.dp, hX2.2.2.tm.dh⟩ (h2.aff t ht) hc' ht)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, -, sc3, -, ea3⟩, -, -, hid⟩
  try simp only [WP.uncurry'_pair]
  rw [sc2] at sc3
  have fw3' : Foot st T Cs Sg Scs Z Es s s3 := by rw [hid haff2]; exact fw2
  -- the sporadic unblock check
  step with sporadic.sc_sporadic.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
      L.actionW s4 = L.actionW s ∧ Foot st T Cs Sg Scs Z Es s s4) ?_ ?_
  · have ok3 : (ok s3 : Result S) ⦃ s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
        L.actionW s4 = L.actionW s ∧ Foot st T Cs Sg Scs Z Es s s4 ⦄ :=
      (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, sc3, by rw [ea3, ea2], fw3'⟩
    split
    · step with sporadic.sc_active.val as ⟨b1, eb1⟩
      split
      · rename_i hb1
        step with sched.cur_sc.spec as ⟨c4, _⟩
        step with sc_ne.spec as ⟨b2⟩
        split
        · have hAc : sc ∈ Ac := (hS3.act sc hsc).2 (eb1 hb1)
          have hW : RefillsWF st s3 sc (Z sc) := hS3.wf hsc hAc
          have hSCin : SCin st s3 Ω sc (Z sc) := ⟨hW, hX3.1.scW sc hsc⟩
          have hN' := h3.nodes _ h3.cur
          have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
          have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
          have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) sc (Z sc) :=
            hSCin.node_out h3.omega h3.cur hN' (by rw [rp]; omega) (by rw [rp])
          refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 t sc h3 hB3 hX3 hS3 hSg3 ht sc3.symm hsc0
            hAc) (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s4 hh => ?_
          obtain ⟨⟨h4, hB4, hX4, hS4, hSg4, ea4, -, -, f4, -⟩, w4⟩ := hh
          have fw4 : Foot st T Cs Sg Scs Z Es s3 s4 := Foot.of w4 fun b hb => by
            rcases hb with hb | rfl
            · exact hb.kw hsc
            · exact kw_node h3.cur (by rw [rp]; omega) (by rw [rp]; omega)
          exact ⟨⟨⟨Q3, R3, h4⟩, hB4, hX4, hS4, hSg4⟩, by rw [scA_eq, f4 t ht _ (by simp) (by simp), ← scA_eq]; exact sc3,
            by rw [ea4, ea3, ea2], fw3'.trans fw4⟩
        · exact ok3
      · exact ok3
    · exact ok3
  rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, sc4, ea4, fw4⟩
  -- resume
  have tc4 : L.mem s4 (scTcbA sc) = t := by
    have := (hX4.2.2.bound t ht (by rw [sc4]; exact hsc0)).2.1; rwa [sc4] at this
  have hres : sc ≠ 0#u64 → L.mem s4 (scTcbA sc) ≠ 0#u64 →
      L.mem s4 (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA sc) ∧ L.mem s4 (scCoreA sc) ∈ Cs ∧
        L.actionW s4 ≠ L.mem s4 (scTcbA sc) := fun _ _ => by
    rw [tc4]
    exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 sc hsc).2.1, hX4.2.2.core sc hsc,
      by rw [ea4]; exact hna⟩
  refine WP.spec_bind (WP.spec_and (schedcontext.resume.all hA s4 a1 sc Q4 R4 h4 hB4 hX4 hSg4 hS4 hres)
    (schedcontext.resume.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) hA s4 a1 sc Q4 R4 h4 hres)) ?_
  rintro ⟨s5, a2⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩, fw5⟩
  have hS5 := hS4.fr f5
  have fw5' : Foot st T Cs Sg Scs Z Es s s5 := fw4.trans fw5
  try simp only [WP.uncurry'_pair]
  -- enqueue if schedulable
  step with sched.is_schedulable.spec' as ⟨b3, eb3⟩
  split
  · rename_i hb3
    obtain ⟨hrun, hbd, hrl, hrm⟩ := eb3 hb3
    have hA5 : L.mem s5 (scA t) ∈ Ac := (hS5.act _ (hX5.2.2.bound t ht hbd).1).2 hrm
    refine WP.spec_bind (WP.spec_and (sched.enqueue.sch s5 t Q5 R5 h5 hB5 hSg5 ht (fun _ => hrl) (fun _ => hrun)
      (fun _ => hbd) (fun _ => hA5)) (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 t h5 ht)) ?_
    rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, fw6⟩
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s6 Q6 R6 h6 hB6 (hSg5.fr f6))
      (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s6 h6)) ?_
    rintro s7 ⟨⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, -, -, -⟩, fw7⟩
    exact (WP.spec_ok _).2 ⟨⟨⟨Q7, R7, h7⟩, hB7, (hX5.fr f6).fr f7, (hS5.fr f6).fr f7, (hSg5.fr f6).fr f7⟩,
      fw5'.trans (fw6.trans fw7)⟩
  · exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, fw5'⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`bind_tcb` at `J`** (module docstring): an SC of `Z.C` bound to no
thread, a thread with no SC (not idle), a blocked thread's SC released (the
decode's check), no switch pending and `CurInv`; the pair's caps in slots
(the invoked thread cap, the SC cap). -/
theorem JAtZ.bindTcbJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    {sc t : U64} (hsC : sc ∈ Z.C) (ht : t ∈ Z.T) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) (hy0 : y.scTcb = none)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none)
    (hrel : Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scReleased σ.curTime y = true)
    (hnsw : ∀ u, σ.schedulerAction ≠ .switchThread u) (hC : CurInv σ)
    (htid : t.bv ≠ σ.idleThread)
    {xs ys sb : U64} (hxS : IsSlot Z.th xs) (hxc : capAt (L.mem s) xs = ok (.Thread t))
    (hyS : IsSlot Z.th ys) (hyc : capAt (L.mem s) ys = ok (.SchedContext sc sb)) (hsb : sb.val < 64)
    (hssz : n + Fl4Spec.minSchedContextBits = sb.val) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => ∃ σ',
      Fl4Spec.schedContextBindTcb (Z := Unit) sc.bv t.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscH : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n hsc0 hk).2⟩
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  -- the thread is not the current one, the SC not the current SC
  obtain ⟨xc, hkc, hxcs, -⟩ := hC.tcb
  have htc : t.bv ≠ σ.curThread := fun e => by
    rw [← e, hkt] at hkc; cases hkc; rw [hxt0] at hxcs; cases hxcs
  have hscc : sc.bv ≠ σ.curSc := fun e => by
    obtain ⟨y1, n1, hk1, hb1⟩ := J.inv.back _ xc _ hkc hxcs
    rw [← e, hk] at hk1; cases hk1; rw [hy0] at hb1; cases hb1
  -- the release check
  have hact_of : Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scActive y = true := fun h => by
    have h1 := hrel h
    unfold Fl4Spec.scReleased at h1; simp only [Bool.and_eq_true] at h1; exact h1.1
  have hblk : Fl4Spec.runnable xt.tcbState = false → inClassR xt.tcbState xt.tcbFault → Fl4Spec.scActive y = true →
      released σ y := by
    intro hr hcl ha
    have hq : Fl4Spec.ipcQueuedThreadState xt.tcbState = true := by
      rcases hcl.cls with h | ⟨m, h⟩ | ⟨e, d, h⟩ | ⟨e, r, d, h⟩
      · rw [h] at hr; cases hr
      all_goals rw [h]; rfl
    have h1 := hrel hq
    unfold Fl4Spec.scReleased at h1; simp only [Bool.and_eq_true] at h1
    exact ⟨h1.2, J.inv.suff hk ha⟩
  -- FL4's side of the decode's checks
  obtain ⟨x', hk', -, -, hscw, -⟩ := hs.tcb t ht
  rw [hkt] at hk'; cases hk'
  have ht0 : L.mem s (P1.scA t) = 0#u64 := Notif.optRef_none (by rw [← hscw]; exact hxt0)
  obtain ⟨y', n', hk2, hx⟩ := hs.scs sc hsC
  rw [hk] at hk2; cases hk2
  have hc0 : L.mem s (P1.scTcbA sc) = 0#u64 := by
    rw [scTcbA_eq]; exact Notif.optRef_none (by rw [← hx.tcb]; exact hy0)
  have hbA : P1.BlockedR (L.mem s (P1.stA t)) → sc ∈ Ac := fun hb => by
    have hq := blockedR_queued (hR.at_tcb ht hkt).st hb
    have hrm := SchedRel.act_sc hS hsC hk (hact_of hq)
    exact (J.blk.2.2.2.1.act _ hscH).2 (fun h => hrm (by rw [h]; rfl))
  have hA0 : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have haff : L.mem s (P1.affA t) = L.mem s (P1.scCoreA sc) := by
    rw [hc.aff t ht, scCoreA_eq, hS.core sc hsC]
  refine WP.spec_mono (WP.spec_and (bind_tcb_refines s a σ hS hR J.nsc J.inv hsC hsc0 hk hy0 ht hkt hxt0 hblk hTA)
    (WP.spec_and (P1.schedcontext.bind_tcb.blkK (Es := ∅) hAT s a sc t J.blk htH hscH hsc0 ht0 hc0 hbA haff)
      (AK.schedcontext_bind_tcb (P1.LawfulStore.total (st := st)) hAT hAK hA0))) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', he, hS', hR', hN', hI', -, hwk⟩, ⟨hblk', hfD⟩, hA'⟩
  have hDbg := J.kw_dbg (P1.Foot.mono hfD (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (P1.Foot.mono hfD (Set.empty_subset _))
  have hm : ((), σ') ∈ (Fl4Spec.schedContextBindTcb (Z := Unit) sc.bv t.bv σ).1 := by
    rw [he]; exact Set.mem_singleton _
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := hwk
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWk
  have hK : ScTKw (fun _ => False) σ σ' := nkt_schedContextBindTcb sc.bv t.bv σ ((), σ') hm
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sc_step (ct := σ.curThread) hX J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' (fun _ => hA')
  have hall := ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree
    ⟨⟨hS', hR', hN', hI'⟩, hWk, (pres_schedContextBindTcb (true, true) _ _).of_eq he⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  -- the mid-entry facts
  have hMid : MidK σ σ' := mka_schedContextBindTcb sc.bv t.bv σ ⟨hscc, htc, htid⟩ _ hm
  have hcT : ∃ u ∈ Z.T, u.bv = σ.curThread := ⟨_, hc.curT, hs.curThread.symm⟩
  obtain ⟨hC', hOw', hO', hAI'⟩ := hMid.midN (T := Z.T) hnsw hC J.off J.act J.inv hcT
  have hF : FK σ σ' := ⟨hMid.csc, hMid.idle, hMid.isc⟩
  have hcr' : CurRunM σ' := hMid.curRunM hnsw hC J.curRun
  have hB' : BlockedScActive σ' := by
    refine J.bsa.bk (bka_schedContextBindTcb sc.bv t.bv σ (fun y2 n2 hy2 => ?_) _ hm)
      ((pres_schedContextBindTcb (true, true) _ _).of_eq he)
    rw [hk] at hy2; cases hy2
    by_cases hq : Fl4Spec.ipcQueuedThreadState xt.tcbState = true
    · exact Or.inl (hact_of hq)
    · exact Or.inr (fun x hx => by rw [hkt] at hx; cases hx; simpa using hq)
  -- the dead set: links cut only at the pair, which is covered by its caps
  have hL : LK (fun p => p = sc.bv ∨ p = t.bv) σ σ' := lkm_schedContextBindTcb sc.bv t.bv σ _ hm
  have hH := J.kern.heap
  have covT : (∀ k, Z.th t = some k → Sched.Covered (L.mem s') Z.G t.val (t.val + max (objSize k) 1)) ∧
      (∀ k, H t = some k → Sched.Covered (L.mem s') Z.G t.val (t.val + 2 ^ k.bits)) := by
    have hHt : H t = some .tcb := J.zH.1 t ht
    have hfit := hH.fits t _ hHt
    simp only [P1.HKind.bits] at hfit
    exact J.cover_cap hW hxS hxc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl (range_thread t hfit)
      fun k hk' => by
        rw [hHt] at hk'; cases hk'
        exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have covS : (∀ k, Z.th sc = some k → Sched.Covered (L.mem s') Z.G sc.val (sc.val + max (objSize k) 1)) ∧
      (∀ k, H sc = some k → Sched.Covered (L.mem s') Z.G sc.val (sc.val + 2 ^ k.bits)) := by
    have hHs := (hJ.sc sc y n hsc0 hk).2
    have hfit := hH.fits sc _ hHs
    simp only [P1.HKind.bits] at hfit
    rw [hssz] at hfit
    refine J.cover_cap hW hyS hyc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
      (range_sc sc sb hsb hfit) fun k hk' => ?_
    rw [hHs] at hk'; cases hk'
    exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have hDead : ∀ q ∈ {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)}, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) hL hF hAI'.1 hY'
      ((((pres_schedContextBindTcb (true, true) _ _).of_eq he).ykeep rfl).dk q.bv) hq.2 (J.jcov.dead q hq.1)
  have hCov : ∀ q ∈ D, q ∉ {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)} →
      (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := fun q hq hn => by
    have hw : q.bv = sc.bv ∨ q.bv = t.bv := by_contra fun h => hn ⟨hq, h⟩
    rcases hw with e | e
    · rw [bv_inj e]; exact covS
    · rw [bv_inj e]; exact covT
  have hIK := J.idleW_keep hS' hF.2.1 hF.2.2
  have hjc := J.sc_jcov hW hDead hCov hIK
  have hsub : {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)} ⊆ D := fun q h => h.1
  have hkern := J.sc_kern hW hK hF hX' hDbg hsub
  exact ⟨σ', he, Ac, Lst', {q : U64 | q ∈ D ∧ ¬ (q.bv = sc.bv ∨ q.bv = t.bv)}, J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK hIK.2) hjc hkern (J.sc_utc hW hK hDbg) hN' hI' hC'
    (Or.inl (hC'.elim hOw' (curOwn_of_curInv hS' hI'))) hO' hAI' hB' hcr' hblk'
    hKd hIK.1 (fun p hp => ⟨J.zD p hp, fun e => by
      rcases e with e | e
      · exact J.not_ztcb hyS (fun _ _ _ h => by rw [capV_of_capAt hyc] at h; cases h)
          (by rw [capV_of_capAt hyc, bv_inj e]; simp [absCap, Fl4Spec.objRefs]) hp
      · exact J.not_ztcb hxS (fun _ _ _ h => by rw [capV_of_capAt hxc] at h; cases h)
          (by rw [capV_of_capAt hxc, bv_inj e]; simp [absCap, Fl4Spec.objRefs]) hp⟩)⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxRecDepth 8000 in
/-- **`cdt::empty_slot` of a slot keeps every other slot's cap** (from any
state agreeing with `s` on P1's `CapW` words), with the `CapW` footprint
(ScInstFoot's `inst_hslot` with the caps: `empty_ws`, `empty_slot_mem`). -/
theorem empty_capV_frame {th : TypedHeap} (hP : Placed th) {T Ω Sg : Set U64} (hSC : SlotCapW th T Ω Sg) {s : S}
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) {root : U64} (hr : IsSlot th root) :
    ∀ (s1 : S) (a1 : A), (∀ b, P1.Aligned b → P1.CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st arI s1 a1 root .Null ⦃ r => P1.WritesIn st s1 r.1 (P1.CapW T Ω Sg) ∧
        ∀ y, IsSlot th y → y ≠ root → capV (L.mem r.1) y = capV (L.mem s) y ⦄ := by
  intro s1 a1 hag
  have hSS : SlotsSame th (L.mem s) (L.mem s1) := fun a ha => by
    have w : ∀ k, Off k → L.mem s1 (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
      hag _ (slot_word_aligned hP ha hk) (hSC _ ⟨a, ha, k, hk, rfl⟩)
    refine ⟨by have := w _ off0; rwa [wordOf_zero] at this, w _ off8, w _ off16, w _ off24⟩
  have hM1 := hM.of_same hSS
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM1.members y).1 h).1
  have hWm : ∀ {s' s'' : S}, P1.WritesIn st s' s'' (SlotWd th) → P1.WritesIn st s' s'' (P1.CapW T Ω Sg) :=
    fun h => h.mono hSC
  by_cases hcn : capV (L.mem s1) root = .Null
  · rw [empty_slot_null arI s1 a1 root (by rw [capAt_capV, hcn]) .Null]
    exact (WP.spec_ok _).2 ⟨P1.WritesIn.refl _ _, fun y hy _ => hSS.capV hy⟩
  have hxm := (hM1.members root).2 ⟨hr, _, capAt_capV _ _, hcn⟩
  have hnx : nextOf (L.mem s1) root = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s1) root) ∧ nextOf (L.mem s1) root ≠ root) := by
    rcases hM1.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s1) root = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s1) root) ∧ prevOf (L.mem s1) root ≠ root) := by
    by_cases h0 : prevOf (L.mem s1) root = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM1.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM1.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hr.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM1.prev_ne_next hP hxm
  have hNc : Canonical (nextOf (L.mem s1) root) := by
    rcases hnx with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  refine WP.spec_mono (WP.spec_and (empty_ws hP s1 a1 root hr (hpv.imp_right And.left) (hnx.imp_right And.left))
    (empty_slot_mem hP s1 a1 root hr _ (capAt_capV _ _) hcn hpv hnx hPN)) ?_
  rintro r ⟨hw, hW, -⟩
  refine ⟨hWm hw, fun y hy hne => ?_⟩
  have h := hW.capAt' hy
  rw [if_neg hne, capAt_capV, capAt_capV] at h
  rw [Result.ok_injective h]
  exact hSS.capV hy

set_option maxHeartbeats 16000000 in
/-- **`tcb::install_tcb_cap` at `J` with the slots' frame** (`install_tcb_capJ`;
the old cap null or an endpoint cap, `NullOrEp`: an Ok install changes no
other slot's cap, by P1's `cdt.delete.ep` with `empty_capV_frame` and the
insert's frame) (module docstring): from the
deletion loop's invariant `WJR` at the base sets `Z`, `WJR` after an Ok
install, `WJP` after a preempted one. -/
theorem install_fhJ [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid Z.th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc)
    (htu : Vs.TabUn nc → Vs.TabUn srcC0) (hnat : Vs.NativeCap srcC0 → Vs.NativeCap nc)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4)
    (hnoe : P1.NullOrEp H (capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ∧
      (res.1 = .Ok () → ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
        capV (L.mem res.2.1) y = capV (L.mem s) y) ⦄ := by
  obtain ⟨V0, Ac0, Lst0, D0, J0, -, -, -⟩ := hI.wjr _ _ _ _ hW
  have hP : Placed Z.th := J0.xtop.rel.1
  obtain ⟨K, hK, hK6, hDE⟩ := J0.delE
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht
  have hczs0 := hcz0.1 _ hAsrc.isSlot hsrcT
  have hsh0 : shape nc = shape (capV (L.mem s0) (cslotAddr (ps.bv, idxs))) := by rw [hsrc0]; exact hsh
  -- the insert after the delete, at `WJR`
  have after : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), DState (L := L) Z.th s1 σ1 G1 →
      W s1 a1 σ1 G1 →
      capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null →
      ChgZ (L.mem s0) (L.mem s1) (cslotAddr (ps.bv, idxs)) →
      (do
        let b ← nc.is_null
        if b = true then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)
          else do
            let b1 ← tcb.still_valid st s1 t (cslotAddr ssl) nc (cslotAddr (ps.bv, idxs))
            if b1 = true then do
                let s2 ← cdt.insert st s1 nc (cslotAddr (ps.bv, idxs)) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))
                ok (core.result.Result.Ok (), s2, a1)
              else ok (core.result.Result.Ok (), s1, a1)) ⦃ res =>
        ∃ σ' G', (Fl4Spec.NonDetE.unlessE (ε := Unit) (absCap nc = .nullCap) (Fl4Spec.NonDetE.liftE
            (Fl4Spec.checkCapAt (absCap nc) (ps.bv, idxs) (Fl4Spec.checkCapAt (.threadCap t.bv) ssl
              (Fl4Spec.capInsert (absCap nc) (ps.bv, idxs) (t.bv, Fl4Spec.tcbCnodeIndex n)))))).run σ1 =
              ({(.ok (), σ')}, False) ∧
          res.1 = .Ok () ∧ DState (L := L) Z.th res.2.1 σ' G' ∧
          (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
            capV (L.mem res.2.1) y = capV (L.mem s1) y) ∧
          (capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
            capV (L.mem res.2.1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = nc) ∧
          W res.2.1 res.2.2 σ' G' ⦄ := by
    intro s1 a1 σ1 G1 hDS1 hW1 hroot hczs
    refine WP.spec_mono (WP.spec_and (install_after Z.th hP s0 s1 a1 σ1 G1 hDS1 t ht n hn hroot ssl hAs nc hwf hcv he
      hfw hps hls hczs hsrc0 hsh hbd hkey hv)
      (install_after_frame hP s1 a1 hDS1.1.2.2.1 hDS1.2.1 t (cslotAddr ssl) nc hAsrc.isSlot hAt.isSlot)) ?_
    rintro res ⟨⟨σ', G', hrun, hr1, ha1, hDS', hcap, hst, htg, hcase⟩, hF⟩
    refine ⟨σ', G', hrun, hr1, hDS', hcap, htg, ?_⟩
    rcases hcase with ⟨e1, e2, e3⟩ | ⟨hins, hthr, hsrc1, hnn, hnut, hdst⟩
    · rw [ha1, e1, e2, e3]; exact hW1
    obtain ⟨V1, Ac1, Lst1, D1, J1, hkb1, hns1, hsg1, hp1⟩ := hI.wjr _ _ _ _ hW1
    have hsg' : SpecGlob σ' := by
      obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS1.1.1.abs_cap hAsrc
      have e0 : c0 = srcC0 := by rw [← hsrc1, capV_of_capAt hc0]
      have ha0 := (getCap_set_iff σ1 _ _ _).1 (congrArg Prod.fst hg0)
      rw [hca0.abs, e0] at ha0
      exact hsg1.insTcb hins hnut hsh ha0
    have hwS := SlotFrame2.writesIn hF
    obtain ⟨Ac2, Lst2, D2, J2⟩ := J1.insTJ (fun e => absurd e hn2) ht hn hins hDS' hst hwS hroot hcap
      (by rw [hdst]; exact hnut) (by rw [hdst]; exact hnn) ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩
      (fun h3 => by rw [hdst]; exact Or.inr (hep h3 hnn)) (fun e => absurd e hn2) ⟨_, hAs.isSlot, hthr⟩
      (fun P L4 L3 L2 L1 h => by
        rw [hdst]; exact h.copy hAsrc.isSlot (by rw [hsrc1]; exact hv) (by rw [hsrc1]; exact htu))
      (fun U h => by rw [hdst]; exact (h _ hAsrc.isSlot).of_okey (by rw [hsrc1]; exact hkey))
      (fun h => by rw [hdst]; exact hnat (by rw [← hsrc1]; exact h _ hAsrc.isSlot))
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap nc) (ps.bv, idxs)
        (t.bv, Fl4Spec.tcbCnodeIndex n) σ1).1 := by rw [hins]; rfl
    have hcn := capInsert_nkn _ _ _ σ1 _ hmem
    have hact : σ'.schedulerAction = σ1.schedulerAction := by
      have e := congrArg Fl4Spec.AbstractState.schedulerAction hcn.1; exact e
    rw [ha1]
    exact hI.ins s1 res.2.1 a1 σ1 σ' G1 G' t n _ _ hDS1 hW1 hDS'
      ⟨V1, Ac2, Lst2, D2, J2, by rw [hwS.1]; exact hkb1, fun u e => hns1 u (hact ▸ e), hsg',
        hp1.of_ppk (PPK.of_cnK hcn)⟩ ht hn hins hwS hroot hcap (by rw [hdst]; exact hnn)
      ⟨_, hAsrc.isSlot, by rw [hdst, hsrc1]; exact hsh⟩ ⟨_, hAs.isSlot, hthr⟩
  unfold tcb.install_tcb_cap
  rw [spec_eq_ok (tcb_slot_spec t idx), tcb_root_eq t idx hn hidx]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    refine WP.spec_mono (after s a σ G hDS hW (by rw [capV_of_capAt hc0]) hczs0) ?_
    rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    exact ⟨⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok (by rw [capDelete_null hg0']; rfl) (mem_of_run hrun),
      hcz0.install hP ht hn (fun y hy hne => ChgZ.of_eq (hcap y hy hne)) htg hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩,
      fun _ y hy hne => hcap y hy hne⟩
  · have hcapNE : obj.Slot.cap st (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) s ⦃ c => P1.NullOrEp H c ⦄ := by
      rw [slot_cap_eq, capAt_capV]; exact (WP.spec_ok _).2 hnoe
    apply WP.spec_bind (WP.spec_and (delete_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 _ hAt s a σ G
      hDS hW (by rw [capV_of_capAt hc0]; exact hc0n) (hDE.2.1 G hDS.1.2.2.1))
      (P1.cdt.delete.ep (ar := arI) s a _ J0.blk hcapNE
        (P := fun s2 => ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
          capV (L.mem s2) y = capV (L.mem s) y)
        (fun s1 a1 hag => WP.spec_mono (empty_capV_frame (arI := arI) hP (J0.slotCapW (tLowSlots_all _))
          hDS.1.2.2.1 hAt.isSlot s1 a1 hag) fun r h => h)))
    rintro ⟨r, s1, a1⟩ ⟨⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩, -, -, -, hfr⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_mono (after s1 a1 σ1 G1 hDS1 hW1 hnull (hczs0.trans (hcz _ hAsrc.isSlot (hsrcT n hn)))) ?_
      rintro res ⟨σ', G', hrun, hr1, hDS', hcap, htg, hW'⟩
      exact ⟨⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok hmem (mem_of_run hrun),
        hcz0.install hP ht hn (fun y hy hne => (hcz y hy hne).trans (ChgZ.of_eq (hcap y hy hne))) htg
          hAsrc.isSlot hsh0 hep, hW'⟩, hDS'⟩, fun _ y hy hne => (hcap y hy hne).trans (hfr rfl y hy hne)⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩, fun h => by cases h⟩



/-- `install_fhJ` with the new cap's conditions as `NewCapOK` (as `install_okJ`). -/
theorem install_fhOkJ [Fl4Proofs.P1.PlainStore st] {kb : U64} {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (hI : InsWJ (L := L) arI AR Z H Cs kb W)
    (hH : DelHypsWRZ (L := L) arI W (WJP (L := L) arI AR Z H Cs kb) Rd Rz Z.th)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) Z.th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : Z.th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (hn2 : n ≠ 2) (idx : U64) (hidx : idx.val = n)
    (hcz0 : InstFr Z.th t (L.mem s0) (L.mem s))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (nc : capability.Cap) (sl : Fl4Spec.CslotPtr) (hok : NewCapOK Z.th (L.mem s0) nc sl)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4)
    (hnoe : P1.NullOrEp H (capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr sl) ⦃ res =>
      InstPostWP (L := L) W (WJP (L := L) arI AR Z H Cs kb) Z.th t
        (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, sl))) s0 σ res ∧
      (res.1 = .Ok () → ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
        capV (L.mem res.2.1) y = capV (L.mem s) y) ⦄ := by
  obtain ⟨ps, rs, hps, h1s, hls, hwf, hcv, he, hfw, hsh, hbd, hkey, hvk, htu, hnat⟩ := hok
  obtain ⟨sa, idxs⟩ := sl
  simp only at h1s hls; subst h1s
  exact install_fhJ arI hI hH s0 s a σ G hDS hW t ht n hn hn2 idx hidx hcz0 ssl hAs nc hwf hcv he hfw hps hls rfl
    hsh hbd hkey hvk htu hnat hep hnoe

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`set_priority` at `J` with its frames** (`JAtZ.setPrioJ`): the spec's
`PFr` (`setPriority_pfr`) and the slots kept (`set_priority_irelW`'s
footprint `CnW`, words of the objects outside the slots). -/
theorem JAtZ.setPrioJS (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hna : ∀ u, σ.schedulerAction ≠ .switchThread u) {t : U64} (ht : t ∈ Z.T) (v : U64) (hv : v.val < 256)
    (hcur : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue ∧ ∃ x scp y n, σ.kheap t.bv = some (.tcb x) ∧
      x.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true)
    (hP1 : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (P1.scA t) ≠ 0#u64 ∧ L.mem s (P1.scA t) ∈ Ac) :
    sched.set_priority st s t v ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
      PFr t.bv σ σ' ∧ SlotsSame Z.th (L.mem s) (L.mem s') ∧
      ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hQ := qSorted_of_spec (L := L) hI.1.toE hI.1.toN hP0.e.tcb J.isorted
  obtain ⟨x, hk, -⟩ := hI.1.toE.tcb t ht
  refine WP.spec_mono (WP.spec_and (J.setPrioJ hna ht v hv hcur hP1) (set_priority_irelW hP0 hI ht v hv
    J.inv.actReady (fun h => (hcur h).1) J.sv J.inv J.obj (fun e he => hQ e (Or.inl he))
    (fun e he => hQ e (Or.inr he)))) ?_
  rintro s' ⟨⟨σ', hm, V', J'⟩, ⟨σ'', hm', -, hw⟩⟩
  have e : σ' = σ'' :=
    (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (hm.symm.trans hm')))).2
  subst e
  have hm1 : ((), σ') ∈ (Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ).1 := by
    rw [hm]; exact Set.mem_singleton _
  exact ⟨σ', hm, setPriority_pfr hk _ hna (blkQ_of_sv J.sv hk) J.sv _ hm1,
    J.xtop.slotsSame_of hw (fun b h => CnW.oobj J.xtop.fin.1.1.1 h), V', J'⟩

/-- A TCB's `MCP` word is no slot word: its write keeps the slots. -/
theorem JAtZ.mcp_slots (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (v : U64) :
    SlotsSame Z.th (L.mem s) (L.mem (L.wr s (mcpA t) v)) := by
  have hT : P1.TcbPlaced Z.T := J.ip.e.tcb
  have hKt : (mcpA t).val = t.val + 3440 := mcpA_val hT ht
  refine J.xtop.slotsSame_of (P1.writesIn_wr (mcpA_aligned hT ht)) fun b hb => ?_
  subst hb
  exact Or.inr (Or.inr (Or.inl ⟨t, ht, by omega, by omega⟩))

end

/-! ## The spec's side of the fault-handler install -/

section
open Fl4Spec

/-- **`SpecPost` across the spec's fault-handler install** over a slot holding
the null cap or an endpoint cap (ScInstPost's `schedTailHyp_disch`'s
`hpost2`: `install_sk` when null or not final, `finEpSpecHyp` when final). -/
theorem specPost_install {σ1 σ2 : State Unit} {p : ObjRef} {x1 : Tcb} {sco : Option (Option ObjRef)}
    {ssl : CslotPtr} {fh : Cap × CslotPtr} {c : capability.Cap} (hk1 : σ1.kheap p = some (.tcb x1))
    (hfc : x1.tcbFaultHandler = absCap c) (hc : c = .Null ∨ ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4)
    (hx : (.ok (), σ2) ∈ ((installTcbCap (Z := Unit) p ssl 3 (some fh)).run σ1).1)
    (hpost : SpecPost σ1 p sco) : SpecPost σ2 p sco := by
  rcases hc with hc0 | ⟨ep, b0, b1, b2, b3, b4, hce⟩
  · exact hpost.sk (install_sk hk1 ssl fh (Or.inl (by rw [hfc, hc0]; rfl)) hx)
  · by_cases hfin : isFinalCap' x1.tcbFaultHandler σ1
    · exact finEpSpecHyp σ1 σ2 p x1 ssl fh sco hk1 ⟨_, _, _, by rw [hfc, hce]; rfl⟩ hfin hx hpost
    · refine hpost.sk (install_sk hk1 ssl fh (Or.inr ⟨by rw [hfc, hce]; simp [absCap], c, hfc,
        by rw [hce]; simp, ?_⟩) hx)
      rw [hce]
      exact ⟨rfl, by rw [← hce, ← hfc]; exact hfin⟩

/-- **What the spec's fault-handler install keeps of the scheduler** (over a
slot holding the null cap or an endpoint cap, from an `Inv` state; from
ScInstPost's `install_ik`): `CurInv` (the current thread, its SC and state,
the current SC, activity and the release queue), the time, the idle thread,
every SC bound to no thread (no TCB names it by `Inv.back`, and
`cancel_all_ipc` refill-checks only each waiter's own SC), and the target's
IPC-blocked state (it can only be restarted or made inactive). -/
theorem install_sched (σ1 σ2 : State Unit) (p : ObjRef) (x : Tcb) (ssl : CslotPtr) (fh : Cap × CslotPtr)
    (hk : σ1.kheap p = some (.tcb x))
    (hfh : x.tcbFaultHandler = .nullCap ∨ ∃ e b R, x.tcbFaultHandler = .endpointCap e b R) (hI : Inv σ1)
    (hx : (.ok (), σ2) ∈ ((installTcbCap (Z := Unit) p ssl 3 (some fh)).run σ1).1) :
    (CurInv σ1 → CurInv σ2) ∧ σ2.curTime = σ1.curTime ∧ σ2.idleThread = σ1.idleThread ∧
    (∀ c y n, σ1.kheap c = some (.schedContext y n) → y.scTcb = none →
      σ2.kheap c = some (.schedContext y n)) ∧
    (∀ x2, σ2.kheap p = some (.tcb x2) → ipcQueuedThreadState x2.tcbState = true → x2.tcbState = x.tcbState) := by
  have K := install_ik hk ssl fh hfh hx
  obtain ⟨hcs, htm, hid, his⟩ := K.fk
  refine ⟨fun hC => ?_, htm, hid, fun c y n hy hy0 => K.scU c y n hy fun u xu hu hc => ?_, fun x2 hx2 hq => ?_⟩
  · obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
    obtain ⟨yt, hyt, sr, hs⟩ := K.tcb _ xt hkt
    obtain ⟨y0, n0, hy0⟩ := hC.sc
    obtain ⟨y0', hy0', hm⟩ := K.sc _ y0 n0 hy0
    refine ⟨⟨yt, by rw [K.ct]; exact hyt, by rw [hs, hcs]; exact hsc, ?_⟩, ⟨y0', n0, by rw [hcs]; exact hy0'⟩,
      fun hne y1 n1 hy1 => ?_, by rw [K.ct, K.rel]; exact hC.notRel⟩
    · rcases sr with e | e | e <;> rw [e]
      · exact hnb
      all_goals exact ⟨fun q h => (by cases h), fun e d h => (by cases h), fun e r d h => (by cases h)⟩
    · rw [hcs, his] at hne
      rw [hcs, hy0'] at hy1; cases hy1
      have := hC.active hne y0 n0 hy0
      simpa [scActive, hm] using this
  · obtain ⟨y1, n1, hk1, hb1⟩ := hI.back u xu c hu hc
    rw [hy] at hk1; cases hk1
    rw [hy0] at hb1; cases hb1
  · obtain ⟨y, hy, sr, -⟩ := K.tcb p x hk
    rw [hx2] at hy; cases hy
    rcases sr with e | e | e
    · exact e
    all_goals rw [e] at hq; simp [ipcQueuedThreadState] at hq

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 32000000 in
/-- **SetSchedParams after its checks at `J`** (as XTopTcbSched's `ssp_tailX`):
the caller's restart (`JAtZ.restartWJR`), the fault handler's install at the
deletion loop's invariant (`install_fhOkJ`, `JAtPre` when preempted; the
other slots' caps kept), then `set_mcp` (`JAtZ.mcpWrJ`), `set_priority`
(`JAtZ.setPrioJS`, the current thread's facts by `JAtZ.prioCur` from
`CurInv`) and the SC step: none, `unbind_tcb` (`JAtZ.unbindTcbJ`) or
`bind_tcb` (`JAtZ.bindTcbJ`, the decode's checks carried: `SpecPost` by
`specPost_restart`, `specPost_install`, `BindOK.after`; the SC and the
release check by `install_sched`). -/
theorem ssp_tailJ [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsW (L := L) arI AR Z H Cs W Rd Rz) (hR : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    (p : U64) (hp : Z.th p = some .tcb) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (hpsl : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (x2 : U64) (e2 : Fl4Spec.Cap × Fl4Spec.CslotPtr)
    (hxe2 : x2 = cslotAddr e2.2) (he21 : e2.1 = absCap (capV (L.mem s) x2)) (ps : U64)
    (hps : Z.th ps = some (.cnode e2.2.2.length)) (hps1 : e2.2.1 = ps.bv)
    (hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2)))
    (y0 y1 scv : U64) (hy0 : y0.val < 256) (hy1 : y1.val < 256) (scf : Bool) (q : Fl4Spec.ObjRef)
    (sco : Option (Option Fl4Spec.ObjRef)) (h1 : sco = none ↔ scf = false) (h2 : sco = some none → scv = 0#u64)
    (h3 : ∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64)
    (hD : ScDec σ p.bv sco) (hpI : p ≠ L.idleW s)
    (hscs : scv ≠ 0#u64 → ∃ xs sb, IsSlot Z.th xs ∧ capV (L.mem s) xs = .SchedContext scv sb)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (hdec : DecOut m σ (.invokeTCB (.threadControlSched p.bv ssl (some e2) (some (Fl4Spec.ucast 8 y0.bv, q))
      (some (Fl4Spec.ucast 8 y1.bv, q)) sco)))
    (blk call don : Bool) :
    (do
      let s1 ← tcb.restart_caller st s
      tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (capV (L.mem s) x2, x2) y0 y1 scv
        (if scf then (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC)
          else (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT))) ⦃ res =>
      TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don m s res ⦄ := by
  have hpT : p ∈ Z.T := J.thT p hp
  obtain ⟨hcur, xc, hkc, hrunc⟩ := J.curRunnable hni hct
  obtain ⟨s1, σ1, hrc, hst1, hDS1, hW1, hS1⟩ := J.restartW arI hni hsg hP0 hct hHp (hR ct hct)
  obtain ⟨s1', σ1', xc', hrc', hst1', hkc', -, e1, -, hid1, hct1, -, -⟩ := J.restartJ hni hct
  have es : s1' = s1 := Result.ok_injective (hrc'.symm.trans hrc)
  have eσ : σ1' = σ1 :=
    (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (hst1'.symm.trans hst1)))).2
  subst es eσ
  rw [hkc] at hkc'; cases hkc'
  have hst1c : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1')}, False) := by
    rw [← hcur]; exact hst1
  have hC0 := J.curInv (by rw [hni.2]; intro h; cases h)
  have hC1 : Sched.CurInv σ1' := by
    have h := hC0.restart (xt := xc) (by rw [hcur]; exact hkc)
    rw [hcur] at h; rw [e1]; exact h
  have htm1 : σ1'.curTime = σ.curTime := by rw [e1]; unfold Notif.stsAct; split_ifs <;> rfl
  -- the decode's checks of the target, after the restart
  obtain ⟨xp, hkp, hDU, hDB⟩ := hD
  obtain ⟨xt0, hkt0, hxs0, -⟩ := hC0.tcb
  have hpc : ∀ v, sco = some (some v) → p.bv ≠ σ.curThread := fun v e hpe => by
    rw [hpe, hkt0] at hkp; cases hkp; rw [(hDB v e).1] at hxs0; cases hxs0
  have hBI : BlkIn σ p.bv xp.tcbState := fun e he => by
    rcases epBlocked_some he with ⟨d, hst⟩ | ⟨ro, d, hst⟩
    · exact J.sv.sendQ _ _ e d hkp hst
    · exact J.sv.recvQ _ _ e ro d hkp hst
  have hpost1 := specPost_restart J.inv hkc hrunc hst1c ⟨xp, hkp, hDU, hDB⟩
    (fun x hx => by rw [hkp] at hx; cases hx; exact ⟨blkQ_of_sv J.sv hkp, hBI⟩) hpc
  -- the old fault handler at the restart: null or an endpoint cap
  obtain ⟨V1, Ac1, Lst1, D1, J1, -⟩ := (hHp.ins _).wjr _ _ _ _ hW1
  obtain ⟨Tr1, Cq1, hJ1⟩ := J1.jpl
  have hnoe : P1.NullOrEp H (capV (L.mem s1') (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3))) := hJ1.fhSlot p hp
  obtain ⟨xp1, hkp1, -⟩ := id hpost1
  obtain ⟨c, a', hca, hCR, hg⟩ := hDS1.1.1.abs_cap (sl := (p.bv, Fl4Spec.tcbCnodeIndex 3))
    ⟨p, rfl, Or.inr ⟨hp, 3, by decide, rfl⟩⟩
  rw [getCap_tcb_three hkp1] at hg
  have ha' : xp1.tcbFaultHandler = a' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hg))).1
  have hfc : xp1.tcbFaultHandler = absCap c := by rw [ha', hCR.abs]
  have hcv : capV (L.mem s1') (cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3)) = c := capV_of_capAt hca
  have hcNE : c = .Null ∨ ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4 := by
    rw [← hcv]
    rcases hnoe with h | ⟨ep, b0, b1, b2, b3, b4, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨ep, b0, b1, b2, b3, b4, h⟩
  have hfcS : xp1.tcbFaultHandler = .nullCap ∨ ∃ e b R, xp1.tcbFaultHandler = .endpointCap e b R := by
    rw [hfc]
    rcases hcNE with h | ⟨ep, b0, b1, b2, b3, b4, h⟩
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr ⟨_, _, _, by rw [h]; rfl⟩
  -- the install
  rw [hrc]; simp only [bind_ok]; rw [tcs_fault_eq]
  have hxs : IsSlot Z.th x2 := by rw [hxe2]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1') x2 = capV (L.mem s) x2 := hS1.capV hxs
  have hnf := vfh_not_frame hv
  have hok : NewCapOK Z.th (L.mem s1') (capV (L.mem s) x2) e2.2 := by
    rw [← hc1, hxe2]; exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe2, hc1]; exact hnf)
  have hI := install_fhOkJ arI (hHp.ins (L.ksb s1')) (hHp.del (L.ksb s1')) s1' s1' ar σ1' Z.G hDS1 hW1 p hp 3 (by simp [tcbSlots]) (by decide)
    layout.tcb.SLOT_FAULT_HANDLER (by simp [layout.tcb.SLOT_FAULT_HANDLER]) (InstFr.refl _ _ _) ssl hAs
    (capV (L.mem s) x2) e2.2 hok (fun _ => vfh_ep hv) hnoe
  rw [← hxe2] at hI
  obtain ⟨⟨r, s2, a1⟩, hins, ⟨σ2, G2, hc, hDS2⟩, hfr⟩ := spec_exists hI
  have he2 : e2 = (absCap (capV (L.mem s) x2), e2.2) := by rw [← he21]
  rw [hins]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hc with ⟨hr, hx, -, hW2⟩ | ⟨hr, hx, hWp⟩
  swap
  · -- preempted: `JAtPre`
    simp only at hr; subst hr
    rw [← he2] at hx
    obtain ⟨s0', a0', σ0', ⟨V0, Ac0, Lst0, D0, J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hWp
    refine (WP.spec_ok _).2 (Or.inr ⟨_, hdec, σ1', hst1, (.error (), σ2), ?_, ⟨Z.th, G2, Or.inr ⟨rfl, rfl⟩,
      J0.xtop.rel.1, hDS2.1, hDS2.2.2, hDom, hMO⟩, ?_⟩)
    · show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
        (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1').1
      simp only [Fl4Spec.invokeTcb]
      exact mem_bindE_err hx
    · show if _ = _ then _ else _
      rw [if_pos rfl]
      exact ⟨s0', a0', σ0', ⟨⟨_, H, Cs, Ac0, Lst0, D0, J0⟩, hns0, hp00⟩, hpp, hspp⟩
  simp only at hr; subst hr
  rw [← he2] at hx
  obtain ⟨V2, Ac2, Lst2, D2, J2, -, hns2, -, -⟩ := (hHp.ins _).wjr _ _ _ _ hW2
  -- the spec after the install
  have hpost2 := specPost_install hkp1 hfc hcNE hx hpost1
  obtain ⟨hCI, htm2, hid2, hscK, hstK⟩ := install_sched σ1' σ2 p.bv xp1 ssl e2 hkp1 hfcS J1.inv hx
  have hC2 : Sched.CurInv σ2 := hCI hC1
  have hct2 : σ2.curThread = σ1'.curThread := Vs.DK.ct (Vs.dke_installTcbCap' p.bv ssl 3 (some e2)) hx
  obtain ⟨x, hk2, -, -, -, hU2, hB2⟩ := hpost2
  -- the slots after the install: those holding neither the null cap nor an endpoint cap kept
  have hroot1 : ∀ y, IsSlot Z.th y → capV (L.mem s) y ≠ .Null →
      (∀ e b0 b1 b2 b3 b4, capV (L.mem s) y ≠ .Endpoint e b0 b1 b2 b3 b4) →
      capV (L.mem s2) y = capV (L.mem s) y := fun y hy hn he => by
    have hne : y ≠ cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex 3) := fun e => by
      rw [← hS1.capV hy, e] at hn he
      rcases hnoe with h | ⟨ep, b0, b1, b2, b3, b4, h, -⟩
      · exact hn h
      · exact he _ _ _ _ _ _ h
    rw [hfr rfl y hy hne, hS1.capV hy]
  -- `set_mcp`
  unfold schedTail
  rw [set_mcp_eq, bind_ok]
  obtain ⟨V3, J3⟩ := J2.mcpWrJ hpT hk2 y0 (Fl4Spec.ucast 8 y0.bv)
    (by rw [Ipc.ucast8_specPrio, Sched.specPrio_toNat hy0])
  set σa := Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 y0.bv }) with hσa
  have hSS3 := J2.mcp_slots hpT y0
  have ha : ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 y0.bv) σ2).1 := by
    show _ ∈ (Fl4Spec.threadSet (Z := Unit) _ p.bv σ2).1
    rw [Notif.threadSet_eq _ hk2]; exact Set.mem_singleton _
  have hCa : Sched.CurInv σa := (QKM.mcp hk2 _).curInv hC2
  have hneA : σa.curThread ≠ σa.idleThread := by
    show σ2.curThread ≠ σ2.idleThread
    rw [hct2, hid2, hct1, hid1]; exact hni.1
  obtain ⟨hc3, hp3⟩ := J3.prioCur hneA hCa hpT
  -- `set_priority`
  refine WP.spec_bind (J3.setPrioJS (fun u => hns2 u) hpT y1 hy1 hc3 hp3) ?_
  rintro s4 ⟨σb, hmb, hPF, hSS4, V4, J4⟩
  have hb : ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 y1.bv) σa).1 := by
    rw [hmb]; exact Set.mem_singleton _
  have hCb : Sched.CurInv σb := hPF.curInv hCa
  have hnsb : ∀ u, σb.schedulerAction ≠ .switchThread u := fun u e => by
    rcases hPF.act with e' | e' <;> rw [e'] at e
    · exact hns2 u e
    · cases e
  have hvk : VK σ2 σb := (presV_setMcpriority _ _ σ2 _ ha).trans (presV_setPriority _ _ σa _ hb)
  obtain ⟨xb, hkb, hstb, hscb⟩ := hvk.tcb _ x hk2
  have hidb : p.bv ≠ σb.idleThread := by
    rw [hPF.sk.idle]
    show p.bv ≠ σ2.idleThread
    rw [hid2, hid1]
    obtain ⟨Q0, R0, hc0, hs0⟩ := J.xtop.fin.1.1.1.lists
    have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
      unfold P1.LawfulStore.idleW nodeW; rw [hc0.cur]
    intro e
    exact hpI (Eq.symm (by rw [ei]; apply P1.eq_of_bv; rw [← hs0.idleTh, ← e]))
  -- the outcome
  have fin : ∀ (s5 : S) (a5 : A) (σc : Fl4Spec.State Unit), ((), σc) ∈ (scStep p.bv sco σb).1 →
      (∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s5 a5 σc) →
      (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a5) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
        TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don m s res ⦄ := by
    rintro s5 a5 σc hcc ⟨Z', Ac', Lst', D', J'⟩
    rw [WP.spec_ok]
    refine TopPostDMX.toPne (Or.inr ⟨_, hdec, σ1', hst1, (.ok [], σc), ?_, ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩,
      J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
      ⟨Z', H, Cs, Ac', Lst', D', J'⟩⟩) (by simp)
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
      (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1').1
    simp only [Fl4Spec.invokeTcb]
    exact mem_bindE_ok hx (mem_bindE_ok (mem_liftE ha) (mem_bindE_ok (mem_liftE hb)
      (mem_bindE_ok (mem_liftE hcc) (Set.mem_singleton _))))
  cases scf
  · -- no SC step
    have hsco : sco = none := h1.2 rfl
    subst hsco
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact fin s4 a1 σb (Set.mem_singleton _) ⟨_, _, _, _, J4⟩
  simp only [↓reduceIte]
  step with Sched.obj.Sc.is_null.spec' as ⟨bz, hbz⟩
  by_cases hs0 : scv = 0#u64
  · -- the unbind
    have hsco : sco = some none := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp)
      | some o =>
        cases o with
        | none => rfl
        | some v => exact absurd hs0 (h3 v rfl).2
    subst hsco
    rw [hbz, decide_eq_true hs0]
    simp only [↓reduceIte]
    obtain ⟨cc, y, n, hcx, hks, hy⟩ := hU2 rfl
    have hksb : σb.kheap cc = some (.schedContext y n) := (hvk.sc cc y n).2 hks
    have hxbsc : xb.tcbSchedContext = some cc := by rw [hscb, hcx]
    obtain ⟨Qb, Rb, hcb, hsbl⟩ := J4.xtop.fin.1.1.1.lists
    obtain ⟨xb', hkb', -, -, hscw, -⟩ := hsbl.tcb p hpT
    rw [hkb] at hkb'; cases hkb'
    step with P1.obj.Tcb.sc.spec as ⟨i4, hi4⟩
    have hi40 : i4 ≠ 0#u64 := fun e => by rw [hscw, ← hi4, e, Notif.optRef_zero] at hxbsc; cases hxbsc
    have hi4c : i4.bv = cc := by rw [hscw, ← hi4, Notif.optRef_ne hi40] at hxbsc; exact Option.some.inj hxbsc
    have hi4C : i4 ∈ Z.C := by rw [hi4]; exact hsbl.scMem p hpT (by rw [← hi4]; exact hi40)
    step with Sched.obj.Sc.is_null.spec' as ⟨b1, hb1⟩
    rw [hb1, decide_eq_false hi40]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (J4.unbindTcbJ hpT hi4C hkb (by rw [hxbsc, hi4c]) (fun u e => absurd e (hnsb u)) hidb) ?_
    rintro s5 ⟨σc, hsc, Ac5, Lst5, D5, J5⟩
    refine fin s5 a1 σc ?_ ⟨_, Ac5, Lst5, D5, J5⟩
    show _ ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext p.bv >>= fun o =>
      Fl4Spec.NonDet.assertOpt o >>= fun c => Fl4Spec.schedContextUnbindTcb c) σb).1
    rw [nd_bind_one (Endp.getTcbObjRef_eq _ hkb), hxbsc]
    rw [nd_bind_one (show (Fl4Spec.NonDet.assertOpt (some cc) : Fl4Spec.SMonad Unit Fl4Spec.ObjRef) σb =
      ({(cc, σb)}, False) from rfl), ← hi4c, hsc]
    exact Set.mem_singleton _
  · -- the bind
    have hsco : sco = some (some scv.bv) := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp)
      | some o =>
        cases o with
        | none => exact absurd (h2 rfl) hs0
        | some v => rw [(h3 v rfl).1]
    subst hsco
    rw [hbz, decide_eq_false hs0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨-, yd, nd, hkd, hyd0, hreld⟩ := hDB _ rfl
    obtain ⟨x0, -, -, hkt0', hxs0', -⟩ := hB2 _ rfl
    rw [hk2] at hkt0'; cases hkt0'
    have hxb0 : xb.tcbSchedContext = none := by rw [hscb]; exact hxs0'
    -- the SC and the release check, carried from the decode
    have hdc : scv.bv ≠ ct.bv := fun e => by rw [e, hkc] at hkd; cases hkd
    have hk1d : σ1'.kheap scv.bv = some (.schedContext yd nd) := by
      rw [restart_kheap hkc hst1c, Function.update_of_ne hdc]; exact hkd
    have hkbd : σb.kheap scv.bv = some (.schedContext yd nd) := (hvk.sc _ yd nd).2 (hscK _ yd nd hk1d hyd0)
    have hpct : p.bv ≠ ct.bv := fun e => hpc _ rfl (by rw [e, hcur])
    have hkp1' : σ1'.kheap p.bv = some (.tcb xp) := by
      rw [restart_kheap hkc hst1c, Function.update_of_ne hpct]; exact hkp
    rw [hkp1'] at hkp1; cases hkp1
    have hrelb : Fl4Spec.ipcQueuedThreadState xb.tcbState = true → Fl4Spec.scReleased σb.curTime yd = true := by
      intro hq
      rw [hstb] at hq
      have e := hstK x hk2 hq
      rw [hvk.tm, htm2, htm1]
      exact hreld (by rw [← e]; exact hq)
    -- the pair's caps, kept by the steps
    have hTn : capV (L.mem s) (cslotAddr ssl) ≠ .Null := by rw [hpsl]; exact fun h => by cases h
    have hTe : ∀ e b0 b1 b2 b3 b4, capV (L.mem s) (cslotAddr ssl) ≠ .Endpoint e b0 b1 b2 b3 b4 := by
      intro e b0 b1 b2 b3 b4 h; rw [hpsl] at h; cases h
    have hT4 : capAt (L.mem s4) (cslotAddr ssl) = ok (.Thread p) := by
      rw [capAt_capV, hSS4.capV hAs.isSlot, hSS3.capV hAs.isSlot, hroot1 _ hAs.isSlot hTn hTe, hpsl]
    obtain ⟨xs, sb, hxsS, hxsc⟩ := hscs hs0
    have hSn : capV (L.mem s) xs ≠ .Null := by rw [hxsc]; exact fun h => by cases h
    have hSe : ∀ e b0 b1 b2 b3 b4, capV (L.mem s) xs ≠ .Endpoint e b0 b1 b2 b3 b4 := by
      intro e b0 b1 b2 b3 b4 h; rw [hxsc] at h; cases h
    have hS4 : capAt (L.mem s4) xs = ok (.SchedContext scv sb) := by
      rw [capAt_capV, hSS4.capV hxsS, hSS3.capV hxsS, hroot1 _ hxsS hSn hSe, hxsc]
    obtain ⟨hscvC, -, hsb, hssz, -⟩ := J4.scCtxCap arI hxsS hS4
    refine WP.spec_bind (J4.bindTcbJ hAT hAK hTA hscvC hpT hkbd hyd0 hkb hxb0 hrelb hnsb hCb hidb
      hAs.isSlot hT4 hxsS hS4 hsb (hssz yd nd hkbd)) ?_
    rintro ⟨s5, a5⟩ ⟨σc, hsc, Ac5, Lst5, D5, J5⟩
    try simp only [uncurry_apply_pair]
    refine fin s5 a5 σc ?_ ⟨_, Ac5, Lst5, D5, J5⟩
    show _ ∈ (Fl4Spec.schedContextBindTcb (Z := Unit) scv.bv p.bv σb).1
    rw [hsc]; exact Set.mem_singleton _

set_option maxHeartbeats 8000000 in
/-- **The SetSchedParams label at `JAt`** (`JAtPre` if preempted; as
XTopTcbSched's `tcb_set_sched_paramsX`): the decode (the authority's MCP by
`JAtZ`'s `McpRel`, the SC checks by the scheduler and notification
relations), then `ssp_tailJ`. -/
theorem tcb_set_sched_paramsJ [Fl4Proofs.P1.PlainStore st] {W : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hHp : TcbInsW (L := L) arI AR Z H Cs W Rd Rz) (hRs : RestartWJ (st := st) Z s ar σ (W (L.ksb s)))
    (hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSchedParams)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hpI : p ≠ L.idleW s)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (hpsl : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ fl4_abi.label.TCBSetSchedParams p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hS : SchedRel st Z.N Z.T Z.C Z.c s σ := J.xtop.fin.1.1.1
  have hR : Notif.NtfnStateRel Z.N Z.T (L.mem s) σ := J.xtop.fin.1.1.2.2.1
  have hpT : p ∈ Z.T := J.thT p hp
  have hM := J.mcp
  have hC0 := J.c0
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKXP
  rw [decode_ssp_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSchedParams
    by_cases ha : args.length < 2
    · rw [whenE_pos (by simpa using ha)]
      exact run_throw_bind _ _ _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_throw_bind _ _ _
  unfold tcb.decode_set_sched_params tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hXc.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hXc.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  have ha1 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 1#u64 y1 (by simp))
  simp only [ha0, ha1, bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hXc.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hXc.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hXc.get hx2' h2
  have hexl : ¬ excaps.length < 3 := by
    have := (List.getElem?_eq_some_iff.1 he2).1; omega
  -- the spec up to the authority's cap
  have hspec0 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = ((match e0.1 with
        | .threadCap tcbPtr => Fl4Spec.NonDetE.returnOk tcbPtr
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.checkPrio (Z := Unit) y0.bv q >>= fun _ => Fl4Spec.checkPrio (Z := Unit) y1.bv q >>= fun _ =>
        Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ := by
    unfold Fl4Spec.decodeSetSchedParams
    rw [whenE_neg (by simp), retOk_bind, whenE_neg hexl, retOk_bind, retOk_bind, retOk_bind, retOk_bind,
      retOk_bind, retOk_bind, he0, he1, he2, the_some, the_some, the_some]
    generalize e0.1 = cc
    cases cc <;> rfl
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  swap
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0, he01]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_throw_bind _ _ _
  obtain ⟨q, hq⟩ := hth
  rw [thread_arg_thread s 1#u64 hq]
  simp only [bind_ok, check_prio_eq]
  have hqT := hcapT h0 q hq
  have he0' : e0.1 = .threadCap q.bv := by rw [he01, hq]; rfl
  rw [he0'] at hspec0
  simp only [] at hspec0
  rw [retOk_bind] at hspec0
  have hcp0 := checkPrio_run hM hqT y0.bv
  have hcp1 := checkPrio_run hM hqT y1.bv
  obtain ⟨xq, hkq, hmq⟩ := hM q hqT
  have hmq8 : (L.mem s (mcpA q)).val < 256 := by rw [hmq]; exact xq.tcbMcpriority.isLt
  by_cases hg0 : y0 > L.mem s (mcpA q)
  · rw [ite_eq_left hg0]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg0)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg0]
  simp only [bind_ok]
  by_cases hg1 : y1 > L.mem s (mcpA q)
  · rw [ite_eq_left hg1]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg1)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg1]
  simp only [bind_ok]
  have hy0 : y0.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y0.val := hg0; omega
  have hy1 : y1.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y1.val := hg1; omega
  have hspec1 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg1), retOk_bind]
  obtain ⟨Q, R', hcL, hsL⟩ := hS.lists
  obtain ⟨xp, hkp, -, -, hxts, -⟩ := hsL.tcb p hpT
  have hsc0 : obj.Tcb.sc st p s = ok (L.mem s (P1.scA p)) := by
    obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Tcb.sc.spec (L := L) s p); exact hw
  -- after the SC check: the fault handler, the restart and the invocation
  have hafter : ∀ (scv : U64) (sco : Option (Option Fl4Spec.ObjRef)),
      (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1).run σ = ({(.ok sco, σ)}, False) →
      (sco = none ↔ (L.mem s (P1.scA p) != scv) = false) → (sco = some none → scv = 0#u64) →
      (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) → ScDec σ p.bv sco →
      (scv ≠ 0#u64 → ∃ xs sb, IsSlot Z.th xs ∧ capV (L.mem s) xs = .SchedContext scv sb) →
      (do
        let i ← lift (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO)
        let flags ← lift (i ||| tcb.SCHED_UPDATE_FAULT)
        if (L.mem s (P1.scA p) != scv) = true then do
            let flags1 ← lift (flags ||| tcb.SCHED_UPDATE_SC)
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags1
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)
          else do
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
    intro scv sco hdus hs1 hs2 hs3 hD hscs
    simp only [lift, bind_ok, slot_cap_eq, capAt_capV, vfh_eq]
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2))
    · simp only [decide_eq_true hv, ↓reduceIte]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (.threadControlSched p.bv ssl (some e2)
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he21]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e2) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]; rfl
      by_cases hscf : (L.mem s (P1.scA p) != scv) = true
      · simp only [hscf, ↓reduceIte]
        have h1' : sco = none ↔ true = false := by rw [hs1, hscf]
        have := ssp_tailJ arI s ar σ J hni hsg hP0 hHp hRs hAT hAK hTA p hp ct hct ssl hAs hpsl x2 e2 hxe2 he21 ps2
          hps2 hps21 hv y0 y1 scv hy0 hy1 true q.bv sco h1' hs2 hs3 hD hpI hscs _ (DecOut.of_eq hdec) blk call don
        simp only [↓reduceIte] at this
        exact this
      · simp only [Bool.not_eq_true] at hscf
        simp only [hscf, Bool.false_eq_true, ↓reduceIte]
        have h1' : sco = none ↔ false = false := by rw [hs1, hscf]
        have := ssp_tailJ arI s ar σ J hni hsg hP0 hHp hRs hAT hAK hTA p hp ct hct ssl hAs hpsl x2 e2 hxe2 he21 ps2
          hps2 hps21 hv y0 y1 scv hy0 hy1 false q.bv sco h1' hs2 hs3 hD hpI hscs _ (DecOut.of_eq hdec) blk call don
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        exact this
    · simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      have hiv : ∀ (scf : Bool), (ok ((.Err (.Sys (.InvalidCapability 3#u64)) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
        intro _
        refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 3, ?_, Or.inr ⟨3#u64, rfl, rfl⟩⟩, hJ0⟩)
        apply run_liftME_err
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he21]; exact hv)]
        exact run_bind_error (run_throw_bind _ _ _) _
      split <;> exact hiv true
  have hpre : ∀ cp : Fl4Spec.Cap, e1.1 = cp →
      (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl cp >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rintro cp rfl; exact hspec1
  unfold tcb.sched_params_sc
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc1 : capV (L.mem s) x1
  case Null =>
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    rw [hct]
    simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
    by_cases hpc : p = ct
    · simp only [decide_eq_true hpc, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1]
      refine run_bind_error ?_ _
      rw [dus_null hkp ssl, whenE_pos (by rw [hcur, hpc])]
      exact run_throw_bind _ _ _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte, bind_ok, hsc0]
      have hpc' : ¬ p.bv = σ.curThread := by rw [hcur]; intro e; exact hpc (P1.eq_of_bv e)
      refine hafter 0#u64 _ (by rw [he11, hc1]; simp only [absCap]; rw [dus_null hkp ssl, whenE_neg hpc', retOk_bind]; rfl)
        ?_ (fun _ => rfl) (fun v h => by split at h <;> cases h)
        ⟨xp, hkp, fun h => ⟨hpc', fun e => (by simp [e] at h)⟩, fun v h => (by split at h <;> cases h)⟩ (fun h => absurd rfl h)
      rw [hxts]
      by_cases hz : L.mem s (P1.scA p) = 0#u64
      · simp [hz, Notif.optRef_zero]
      · simp [hz, Notif.optRef_ne hz]
  case SchedContext ptr sz =>
    have hx1S : IsSlot Z.th x1 := by rw [hxe1]; exact AbsSlot.isSlot ⟨ps1, hps11, Or.inl hps1⟩
    have hscsP : ptr ≠ 0#u64 → ∃ xs sb, IsSlot Z.th xs ∧ capV (L.mem s) xs = .SchedContext ptr sb :=
      fun _ => ⟨x1, sz, hx1S, hc1⟩
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    have hpC := hcapC h1 ptr sz hc1
    have hptr0 := hC0 ptr hpC
    obtain ⟨y, n, hks, hx⟩ := hsL.scs ptr hpC
    have hne : Fl4Spec.scActive y = true → y.scRefills ≠ [] := fun ha => by
      rw [(hx.strong ha).refills]; exact refills_ne (hx.strong ha).wf
    have hdus := dus_sc hkp hks hne ssl (sz.val - Fl4Spec.minSchedContextBits)
    have hst := (hR.at_tcb hpT hkp).st
    have hxt' : y.scTcb = Notif.optRef (L.mem s (scW ptr 24#u64)) := hx.tcb
    have hcons : (((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = none ↔
          (L.mem s (P1.scA p) != ptr) = false) ∧
        ((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some none → ptr = 0#u64) ∧
        (∀ v, (if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some (some v) →
          v = ptr.bv ∧ ptr ≠ 0#u64)) := by
      rw [hxts]
      refine ⟨?_, (fun h => by split at h <;> cases h), (fun v h => by split at h <;> cases h; exact ⟨rfl, hptr0⟩)⟩
      simp only [ne_eq, bv_optRef_some hptr0]
      by_cases e : L.mem s (P1.scA p) = ptr <;> simp [e]
    have hillT : (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl
          (.schedContextCap ptr.bv (sz.val - Fl4Spec.minSchedContextBits))).run σ =
          ({(.error .illegalOperation, σ)}, False) →
        (ok ((.Err (.Sys .IllegalOperation) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMXP (L := L) (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
      intro h
      refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1]
      exact run_bind_error h _
    simp only [hsc0, bind_ok]
    by_cases hip : L.mem s (P1.scA p) = ptr
    · -- the thread's own SC
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hxts, hip, Notif.optRef_ne hptr0]; simp
      rw [if_neg (show ¬ (L.mem s (P1.scA p) != ptr) = true by simp [hip])]
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩ hscsP
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩ hscsP
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

    · have hne1 : (L.mem s (P1.scA p) != ptr) = true := by simp [hip]
      simp only [hne1, ↓reduceIte]
      by_cases hi0 : L.mem s (P1.scA p) = 0#u64
      swap
      · have : (L.mem s (P1.scA p) != 0#u64) = true := by simp [hi0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hxts, Ne, bv_optRef_some hptr0]; exact hip,
          Or.inl (by rw [hxts, Notif.optRef_ne hi0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (P1.scA p) != 0#u64) = false := by simp [hi0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hscT : obj.Sc.tcb st ptr s = ok (L.mem s (scW ptr 24#u64)) := by
        obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Sc.tcb.spec (L := L) s ptr); rw [scTcbA_eq] at hw; exact hw
      simp only [hscT, bind_ok]
      have hx0n : xp.tcbSchedContext = none := by rw [hxts, hi0, Notif.optRef_zero]
      by_cases ht0 : L.mem s (scW ptr 24#u64) = 0#u64
      swap
      · have : (L.mem s (scW ptr 24#u64) != 0#u64) = true := by simp [ht0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hx0n]; simp, Or.inr (by rw [hxt', Notif.optRef_ne ht0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (scW ptr 24#u64) != 0#u64) = false := by simp [ht0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hx0n, hxt', ht0, Notif.optRef_zero]; simp
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun _ => by rw [← hr, eb])⟩)⟩⟩ hscsP
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun hq => absurd hq hb)⟩)⟩⟩ hscsP
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

  all_goals
    rw [he11, hc1] at hspec1
    simp only [error.invalid_cap, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (TopPostDMX.errP ⟨_, rfl, rfl, ⟨.invalidCapability 2, ?_, Or.inr ⟨2#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    rw [hspec1]
    exact run_bind_error (dus_other hkp ssl (by simp [absCap]) (by simp [absCap])) _

end

end

end Fl4Proofs.P3
