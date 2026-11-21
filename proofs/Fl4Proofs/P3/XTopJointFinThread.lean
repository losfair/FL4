/-
P3 (DESIGN.md §9), TCB: **`JAtZ` across a final thread cap's finalisation**
(toward `JStepHyps.del`, as XTopJointFin / XTopJointFinEp /
XTopJointFinReply): FL4's `finalise_cap` of a thread cap against the spec's,
from `JAtZ` before to `JAtZ` after (`JAtZ.finThreadJ`), by the steps of
XTopFinThread's `xFinThread_of`:

* the remote stall and the VCPU detach: no-ops (`remote_tcb_stall_id`,
  `vcpu_detach_none`, the thread's VCPU word zero);
* `unbind_notification`: nothing when unbound (`unbind_ntfn_zero`); a bound
  thread's (`JAtZ.unbindNJ`): FL4's two writes (`unbind_ntfn_eq`,
  `bound_wr_irel`, footprint `FinW` as `unbind_maybe_irel`'s) against the
  spec's, frame `NFr true` (`unbindN_nfr`), assembled by `JAtZ.nfrStep`
  (`finNtfnJ`'s assembly for one quiet step);
* the timer-tree removal (`JAtZ.tmRemoveJ`: P1's `timer.remove.tf`,
  footprint `TW`, the `REPROGRAM` word kept, `JAtZ.tmw_step`; the spec state
  kept);
* `unbind_from_sc`: nothing without an SC; else `unbind_tcb`
  (`JAtZ.unbindTcbJ`, XTopJointFinThreadSc: an SC step by `JAtZ.sc_frame`,
  the thread neither the switch target nor idle, carried in spec terms from
  `obj`'s words by `JAtZ.spec_of_words`) and the yielder's `complete_yield_to`
  (`JAtZ.completeYieldJ`, XTopJointYield: a register step `JAtZ.reg_frame`
  then an SC step), the yield-from word read against the spec's at
  `JAtZ`;
* `suspend` (`JAtZ.suspendJ`, XTopJointSuspend: the fault clear or, for a
  blocked thread, its `cancel_ipc`: receive by XTopJointCancelRecv's
  `jCancel_recv` (by `recvReplyHyp_holds`), reply by
  XTopJointCancelReply's `jCancel_reply`, send and notification by
  XTopJointCancel's `jCancel_send`, `jCancel_ntfn`; the restart PC; the scheduler
  tail as one SC step), the thread neither the switch target nor idle
  (the current thread may be suspended with a switch pending: `CurRunM`
  only asks `CurRunW` while the action is `resumeCurThread`), carried in
  spec terms across the unbinds (`unbindTcb_shape`, `completeYieldTo_ca`);
* the debug-list removal (`JAtZ.dbgRemoveJ`): P1's `debug_remove.frame` at
  the current core (the thread's affinity), so the words written are
  `DbgWc`; `JAtZ.dbgw_step` (as `tmw_step`: `XTopAt.dbgStep`, the words
  apart from every other field, `kern_dbg` with core 0's new list head null
  or a TCB by P1's `TimerOK.dh`, `dbgw_utc` with the new head outside the
  childless untyped regions: the old head by `UtCapP3.rst`, its successor by
  `JThreadFinHyps.utTcb` and `ut_free`, `dbgRemove_head`);
* the FPU release (`JAtZ.fpuReleaseJ`, XTopJointFpu: FL4's `fpu_release`
  changes only the arch state, kept related by `ARKeep` [P]; the spec's
  changes only the thread's FPU image and `tcbCurFpu`, the FPU owner and the
  machine state, read by no relation of `JAtZ`).

The finalised thread's slot is ready after (`JAtZ.tcb_ready`, as
`JAtZ.ep_ready`: the TCB the only object of `H` in the cap's range, dead by
P1's `fin_cap_thread.dead`).

`JThreadFinHyps`: [scope] `obj` (its VCPU word zero, native threads; VT-x
outside the semantic scope, DESIGN §5, as `JVtHyps`); [J] `utTcb` (core 0's
debug-list successor of the head covered by a cap, l4v
`if_live_then_nonz_cap` for FL4's debug list); [P] `ticks`. The FPU
release needs `ARKeep` [P] (`finThreadJ`'s `hK`, the top level's
`JDelParts.arKeep`). That the thread is not the scheduler's switch target
(P1's `fin_cap_thread` precondition) is no premise: no switch is pending
during a deletion (SpecNoSwitch's `NoSwitch`, carried by the deletion loop's
`WJ`; `JAtZ.action_ne_of_noSwitch`), nor the idle thread (`finThreadJ`'s
`hidle`: no cap names the idle thread, the spec's `SpecGlob.idle`, l4v
`valid_global_refs`, carried by `WJ`; XTopJointDelR's `jFinAt_thread`).
-/
import Fl4Proofs.P3.XTopFinThread
import Fl4Proofs.P3.ScFireJ
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.XTopJointEmpty
import Fl4Proofs.P3.XTopJointFinThreadSc
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.XTopJointSuspend
import Fl4Proofs.P3.XTopJointCancelRecv
import Fl4Proofs.P3.XTopJointCancelReply
import Fl4Proofs.P3.XTopJointCancel
import Fl4Proofs.P3.XTopJointFpu
import Fl4Proofs.P3.SpecNoSwitch
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
import Fl4Proofs.P3.DbgWF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JAtZ` after a step** at the same MDB ghost, some VSpace sets, active
SCs, call stacks and dead set. -/
abbrev JTP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ

/-- **`JAtZ` after a step at the same dead set** (`JTP` with `D` kept). -/
abbrev JTPD (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ

/-- **The steps of a thread's finalisation at `J` not proved here** (module
docstring), each at every `JAtZ` state of the typed heap `th`. -/
structure JThreadFinHyps (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [scope] The thread is native: its VCPU word zero (ScPlace's `JState.vcpu`).
  A scope premise like `JVtHyps` (VT-x outside the semantic scope, DESIGN §5:
  the spec has no TCB–VCPU binding, and FL4's `vcpu::detach` of a bound
  thread, with its VM-exit report, has no spec counterpart); no l4v
  invariant. -/
  obj : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (x p : U64), IsSlot Z.th x → capV (L.mem s) x = .Thread p →
      L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64
  /-- [P] The platform's `ticks_to_us` and `getMaxTicksToUs` (the yielder's
  `complete_yield_to`, `JAtZ.completeYieldJ`; as XTopYield's `scYieldFinHyp_of`). -/
  ticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
    ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄
  /-- [J] The debug-list successor of core 0's list head is covered by a cap
  (FL4's debug list holds the TCBs not yet finalised, and a thread's
  finalisation unlinks it before its last cap goes: the debug-list analogue
  of l4v `if_live_then_nonz_cap`). With `ut_free` it keeps the successor out
  of every childless untyped region (`UtCapP3.rst`), which is what the new
  list head needs after `debug_remove` of the head (`dbgRemove_head`); the
  old head is already outside by `UtCapP3.rst`. Was: no TCB of `Z.T` in a
  childless untyped region, false once a TCB retyped from an untyped has
  lost its last cap (it stays in `Z.T` = `H`'s TCBs, dead). -/
  utTcb : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∈ Z.T →
    L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))) ≠ 0#u64 →
    Covered (L.mem s) Z.G (L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))).val
      ((L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))).val + 1)

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`timer::remove` at `J`** (as in ScFireJ's `fireJ`): P1's
`timer.remove.tf` (footprint `TW`, `BlkOK` after), the `REPROGRAM` word
kept (it is no timer word), `JAtZ.tmw_step`; the spec state kept. -/
theorem JAtZ.tmRemoveJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    timer.remove st s t ⦃ s' => JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a σ ⦄ := by
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have htT : t ∈ P1.Heap.tcbs H := by rw [← hTe]; exact ht
  refine WP.spec_mono (P1.timer.remove.tf (s0 := s) s t (P1.TF.start (P1.BlkOK.tinv J.blk)) htT) ?_
  rintro s2 ⟨h2, -, -, -, hw2⟩
  have hw2' : P1.WritesIn st s s2 (TmW (L := L) Z.T Cs Z.c s) :=
    hw2.mono fun b hb => Or.inl (by rw [hTe]; exact hb)
  have hR2 : L.mem s2 (L.nodeAt s Z.c layout.node.REPROGRAM) = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) := by
    obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := by have := J.kern.cpuCs; rw [hc.cur] at this; exact this
    have hN : P1.NodePlaced st Z.T s Z.c := by rw [hTe]; exact P1.TInv.nodes J.blk Z.c hcC
    refine hw2.mem_eq (P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      fun hb => ?_
    have hb' : P1.TW st Z.T Cs s (L.nodeAt s Z.c layout.node.REPROGRAM) := by rw [hTe]; exact hb
    have hv := P1.nodeAt_val hN (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
    have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    rcases J.tw_word hb' with ⟨y, hy, g1, g2⟩ | ⟨c', hc', o, ho, e⟩
    · have := J.kern.hnd y _ (J.zH.1 y hy) Z.c hcC
      simp only [P1.HKind.bits] at this; omega
    · have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
      simp only [hnb] at hv e
      by_cases hcc : c' = Z.c
      · subst hcc; omega
      · have : c'.val ≠ Z.c.val := fun h => hcc (UScalar.eq_of_val_eq h)
        rcases Nat.lt_or_gt_of_ne this with h | h
        · have : c'.val * 4288 + 4288 ≤ Z.c.val * 4288 := by nlinarith
          omega
        · have : Z.c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
          omega
  obtain ⟨r2, J2⟩ := J.tmw_step hw2' (Or.inl hR2) h2
  have e2 : (σ.reprogramTimer || r2) = σ.reprogramTimer := by
    have g1 : (σ.reprogramTimer || r2) = decide (Sched.nodeW st s2 Z.c layout.node.REPROGRAM ≠ 0#u64) :=
      J2.xtop.fin.1.1.1.repr
    have g0 : σ.reprogramTimer = decide (Sched.nodeW st s Z.c layout.node.REPROGRAM ≠ 0#u64) :=
      J.xtop.fin.1.1.1.repr
    rw [g1, g0]; unfold Sched.nodeW
    rw [P1.nodeAt_of_ksb hw2.1, hR2]
  rw [e2] at J2
  exact J2

/-! ## `unbind_notification` of a bound thread at `J` -/

section Spec
open Fl4Spec

/-- **The spec's `unbind_notification` of a bound thread** (its outcome,
`ScTcb`'s `unbindNotification_eq`): the frame `NFr true` of the
notification, `Inv` kept (as `umn_nfr`'s bound branch). -/
theorem unbindN_nfr {σ : State Unit} {t n : ObjRef} {x : Tcb} {xn : Notification}
    (hkn : σ.kheap n = some (.notification xn)) (hkt : σ.kheap t = some (.tcb x)) (hI : Sched.Inv σ) :
    Sched.NFr true n σ (updK (updK σ n (.notification (ntfnBoundTcbUpdate (fun _ => none) xn))) t
        (.tcb (tcbBoundNotificationUpdate (fun _ => none) x))) ∧
      Sched.Inv (updK (updK σ n (.notification (ntfnBoundTcbUpdate (fun _ => none) xn))) t
        (.tcb (tcbBoundNotificationUpdate (fun _ => none) x))) := by
  have hrt : n ≠ t := by rintro rfl; rw [hkn] at hkt; cases hkt
  set σ1 := updK σ n (.notification (ntfnBoundTcbUpdate (fun _ => none) xn)) with hσ1
  have hkt1 : σ1.kheap t = some (.tcb x) := by
    simp only [hσ1, updK, Function.update_of_ne (Ne.symm hrt)]; exact hkt
  refine ⟨(Sched.NFr.upd (o' := .notification (ntfnBoundTcbUpdate (fun _ => none) xn)) hkn
      (Or.inr (Or.inr ⟨xn, _, rfl, rfl, rfl, List.Sublist.refl _, fun _ => Or.inl rfl, Or.inl rfl, fun _ => Or.inl rfl,
        Or.inr rfl⟩))).trans
    (Sched.NFr.upd (o' := .tcb (tcbBoundNotificationUpdate (fun _ => none) x)) hkt1
      (Or.inl ⟨x, x.tcbState, none, x.tcbArch, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr rfl⟩)), ?_⟩
  have hI1 : Sched.Inv σ1 := hI.updNtfn hkn (fun p hp => hI.ntfnSc n xn p hkn hp)
  exact hI1.tcbUpd hkt1 _ rfl rfl rfl

end Spec

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a quiet notification-frame step** (`finNtfnJ`'s
assembly for one step): `IRel` after, the slots kept (`IFrame`), FL4's
footprint `FinW` and P1's `KW`, the spec frame `NFr true` with `Inv` after,
the caps kept (`CKeep`), P1's `BlkOK` after. -/
theorem JAtZ.nfrStep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {r : Fl4Spec.ObjRef}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (F : Sched.NFr true r σ σ') (I3 : Sched.Inv σ') (hck : CKeep σ σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := F.actIdle J.act
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' :=
    J.cur.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curInv
  have hrun3 : CurRunM σ' := J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_nfr F hS3 hI3.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.finW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.finW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

set_option maxHeartbeats 8000000 in
/-- **`unbind_notification` of a bound thread at `J`**: FL4's two writes
(`unbind_ntfn_eq`) against the spec's (`unbindNotification_eq`), `IRel`
after (`bound_wr_irel`), the footprint `FinW` (as `unbind_maybe_irel`'s),
the spec frame `unbindN_nfr`, P1's `unbind_notification.blkF`; then
`JAtZ.nfrStep`. -/
theorem JAtZ.unbindNJD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (h0 : L.mem s (P1.boundA t) ≠ 0#u64) :
    notification.unbind_notification st s t ⦃ s' => ∃ σ',
      Fl4Spec.unbindNotification (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      σ'.schedulerAction = σ.schedulerAction ∧ σ'.idleThread = σ.idleThread ∧ σ'.curThread = σ.curThread ∧
      ∃ V : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  obtain ⟨x, xn, hk, hb, hn, hkn⟩ := bound_ntfn_of hI J.sv J.obj ht h0
  have htT : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  refine WP.spec_mono (WP.spec_and (P1.notification.unbind_notification.blkF s t J.blk htT)
    (show notification.unbind_notification st s t ⦃ s' => s' =
      L.wr (L.wr s (Notif.nBoundA (L.mem s (P1.boundA t))) 0#u64) (P1.boundA t) 0#u64 ⦄ from by
        rw [Sched.unbind_ntfn_eq s t h0, WP.spec_ok])) ?_
  rintro s' ⟨⟨hblk, hfoot, -⟩, rfl⟩
  set n := L.mem s (P1.boundA t) with hnv
  have hX2 := bound_wr_irel hP0 hI ht hn hk hkn 0#u64 0#u64 (fun h => absurd rfl h)
  rw [Notif.optRef_zero] at hX2
  have he := Sched.unbindNotification_eq hkn hk hb
  have hba : Aligned (nBoundA n) := by
    rw [nBoundA_eq]; exact (nword hP0.n hn (K := 24#u64) (by simp) (by simp)).1
  have hbv : (nBoundA n).val = n.val + 24 := by rw [nBoundA_eq]; exact nfield_val (hP0.n.ntfn n hn) (by simp)
  have hpa := hP0.e.tcb _ ht
  have hta := (a_bound hpa).1
  have hbvp := val_bound hpa
  have hw2 := (writesIn_wr (s := s) (v := 0#u64) hba).trans
    (writesIn_wr (s := L.wr s (nBoundA n) 0#u64) (v := 0#u64) hta)
  have hF : IFrame (L := L) Z.th s (L.wr (L.wr s (nBoundA n) 0#u64) (P1.boundA t) 0#u64) :=
    IRel.iframe_of hI hw2 fun b hb => by
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)))))
      · exact Or.inr (Or.inr (Or.inl ⟨_, ht, by rw [hbvp]; omega, by rw [hbvp]; omega⟩))
  have hw : P1.WritesIn st s (L.wr (L.wr s (nBoundA n) 0#u64) (P1.boundA t) 0#u64)
      (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw2.mono fun b hb => by
    rcases hb with rfl | rfl
    · exact NWrite.finW hP0.e.tcb (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)
    · exact finW_bound hP0.e.tcb ht
  obtain ⟨F, I3⟩ := unbindN_nfr hkn hk J.inv
  have hck : CKeep σ _ := nkc_unbindNotification t.bv σ _ (by rw [he]; exact Set.mem_singleton _)
  obtain ⟨V', J'⟩ := J.nfrStep hX2 hF hw F I3 hck hblk hfoot
  exact ⟨_, he, rfl, rfl, rfl, V', J'⟩

/-- `unbindNJD` with the sets existential (`JTP`). -/
theorem JAtZ.unbindNJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (h0 : L.mem s (P1.boundA t) ≠ 0#u64) :
    notification.unbind_notification st s t ⦃ s' => ∃ σ',
      Fl4Spec.unbindNotification (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      σ'.schedulerAction = σ.schedulerAction ∧ σ'.idleThread = σ.idleThread ∧ σ'.curThread = σ.curThread ∧
      JTP (L := L) arI AR Z H Cs s' a σ' ⦄ :=
  WP.spec_mono (J.unbindNJD ht h0) fun _ ⟨σ', he, h1, h2, h3, V, J'⟩ => ⟨σ', he, h1, h2, h3, V, Ac, Lst, D, J'⟩

/-! ## The debug-list removal at `J` -/

/-- **A debug-list word on core `Z.c`, by value**: a TCB's debug links
(offsets 3576..3592) or the node's `DEBUG_TCBS` word (offset 88). -/
theorem JAtZ.dbgw_word (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : DbgWc (L := L) Z.T Z.c s b) :
    (∃ y ∈ Z.T, y.val + 3576 ≤ b.val ∧ b.val < y.val + 3592) ∨ b.val = L.nodeBase s Z.c + 88 := by
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hc.tcbs
  have h88 : layout.node.DEBUG_TCBS.val = 88 := by simp [layout.node.DEBUG_TCBS]
  rcases hb with ⟨y, hy, rfl | rfl⟩ | rfl
  · left
    have hv : (P1.dnA y).val = y.val + 3576 := by
      unfold P1.dnA; rw [Notif.tfield_val (hT y hy) (by decide)]; rfl
    exact ⟨y, hy, by omega, by omega⟩
  · left
    have hv : (P1.dpA y).val = y.val + 3584 := by
      unfold P1.dpA; rw [Notif.tfield_val (hT y hy) (by decide)]; rfl
    exact ⟨y, hy, by omega, by omega⟩
  · right; rw [P1.nodeAt_val hc.node (by rw [h88]; omega), h88]

/-- **A debug-list word lies in no object of `H`** but a TCB's debug links. -/
theorem JAtZ.dbgw_obj (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : DbgWc (L := L) Z.T Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k)
    (hin : p.val ≤ b.val ∧ b.val < p.val + 2 ^ k.bits) :
    k = .tcb ∧ p ∈ Z.T ∧ p.val + 3576 ≤ b.val ∧ b.val < p.val + 3592 := by
  have hH := J.kern.heap
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  rcases J.dbgw_word hb with ⟨y, hy, g1, g2⟩ | e
  · have hHy : H y = some .tcb := J.zH.1 y hy
    by_cases hne : p = y
    · subst hne; rw [hHy] at hp; cases hp; exact ⟨rfl, hy, g1, g2⟩
    · have := hH.disj p _ y _ hp hHy hne
      have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12] at this; omega
  · have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
    have := J.kern.hnd p k hp Z.c hcC
    omega

/-- A debug-list word is no word of a non-TCB object of `H`. -/
theorem JAtZ.dbgw_ne_obj (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : DbgWc (L := L) Z.T Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k) (hk : k ≠ .tcb)
    {w : U64} (hw : p.val ≤ w.val ∧ w.val < p.val + 2 ^ k.bits) : b ≠ w := fun e => by
  subst e; exact hk (J.dbgw_obj hb hp hw).1

/-- A debug-list word is no TCB word off the debug links. -/
theorem JAtZ.dbgw_ne_tcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : DbgWc (L := L) Z.T Z.c s b) {t : U64} (ht : t ∈ Z.T) {w : U64} {K : Nat}
    (hwv : w.val = t.val + K) (hK : K < 3576 ∨ (3592 ≤ K ∧ K < 4096)) : b ≠ w := fun e => by
  subst e
  have := J.dbgw_obj hb (J.zH.1 t ht) (by simp only [P1.HKind.bits]; omega)
  omega

/-- A debug-list word (`DbgWc`) is no TCB's VCPU word (KENTRY-PLAN g2b). -/
theorem JAtZ.dbgWc_nv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : DbgWc (L := L) Z.T Z.c s b) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  intro t ht e
  have hv := Sched.tVcpuA_val J.ip.e.tcb ht
  have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
  have g := J.dbgw_obj hb (J.zH.1 t ht) ⟨by rw [e, hv]; omega, by rw [e, hv, e12]; omega⟩
  rw [e, hv] at g
  omega

/-- `SlotsSame` across debug-list writes (as `tmw_slots`). -/
theorem JAtZ.dbgw_slots (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (DbgWc (L := L) Z.T Z.c s)) : SlotsSame Z.th (L.mem s) (L.mem s') := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hPl := hJ.pl
  intro x hx
  have hf := hx.fit hPl
  have hal := hx.align hPl
  obtain ⟨p, i, hi, rfl⟩ := id hx
  have hv := hi.val hPl
  have hin : ∃ k, H p = some k ∧ p.val + 32 * (i + 1) ≤ p.val + 2 ^ k.bits ∧ (k = .tcb → 32 * (i + 1) ≤ 256) := by
    rcases hi with ⟨r, hp, hr⟩ | ⟨hp, hr⟩
    · refine ⟨_, hJ.cnode p r hp, ?_, fun e => by cases e⟩
      simp only [P1.HKind.bits]
      have : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
      rw [this]
      have : i + 1 ≤ 2 ^ r := hr
      nlinarith
    · refine ⟨_, (hJ.tcb p).1 hp, ?_, fun _ => ?_⟩
      · simp only [P1.HKind.bits]; simp [tcbSlots] at hr; omega
      · simp [tcbSlots] at hr; omega
  obtain ⟨k, hHk, hsz, htcb⟩ := hin
  have w : ∀ kk : U64, kk.val < 32 → kk.val % 8 = 0 → L.mem s' (wordOf (slotOf p i) kk) = L.mem s (wordOf (slotOf p i) kk) := by
    intro kk hk hk8
    have hv' := wordOf_val (a := slotOf p i) (k := kk) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv']; omega) fun hb => ?_
    have g := J.dbgw_obj hb hHk (by rw [hv', hv]; omega)
    have g2 := htcb g.1
    rw [hv', hv] at g
    omega
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

set_option maxHeartbeats 2000000 in
/-- **The untyped caps' facts across debug-list writes** (as `tmw_utc`; the
new head of core 0's list outside a childless untyped cap's region given,
`hhd`). -/
theorem JAtZ.dbgw_utc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (DbgWc (L := L) Z.T Z.c s))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hhd : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      NotDev (L.mem s) (cslotAddr sl) p sb fi → (¬ ∃ x, σ.cdt x = some sl) → fi.val ≠ 0 →
      ¬ (p.val ≤ (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    U.ns, ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases J.dbgw_word hb with ⟨y, hy, g1, g2⟩ | e
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
  · intro g h0 hf0
    obtain ⟨r1, -⟩ := U.rst (B g) h0 hf0
    exact ⟨r1, by rw [hna]; exact hhd sl p sb fi dev hsl hcap0 (B g) h0 hf0⟩

/-- **`JKern` across debug-list writes** (`kern_keep` with the spec state
kept and core 0's list head re-established, `hhead`, instead of kept). -/
theorem JAtZ.kern_dbg (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ)
    (hhead : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (Z.th (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))) :
    JKern (L := L) H Cs D Z.th s' σ := by
  have K := J.kern
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  refine ⟨K.orig, by rw [ecw]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    K.gpm, K.ga, K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0⟩
  rw [hna]; exact hhead

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across debug-list writes** (as `tmw_step`): the spec state
kept (`XTopAt.dbgStep`), P1's `BlkOK` after given, core 0's list head
re-established (`hhead`) and outside the childless untyped caps' regions
(`hhd`). -/
theorem JAtZ.dbgw_step (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (DbgWc (L := L) Z.T Z.c s))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hhead : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (Z.th (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hhd : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      NotDev (L.mem s) (cslotAddr sl) p sb fi → (¬ ∃ x, σ.cdt x = some sl) → fi.val ≠ 0 →
      ¬ (p.val ≤ (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (hdbg : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') ≠ 0#u64 → ∃ k,
      dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) ∧
      dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ 0#u64)
    (hDW' : DbgWF (P1.Heap.tcbs H) Cs (L.mem s') (dbgHd (L := L) s')) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a σ := by
  have hX' := J.xtop.dbgStep hw
  have F : Sched.NFr true σ.curThread σ σ := Sched.NFr.rt _ σ σ.reprogramTimer
  have hS := J.xtop.fin.1.1.1
  have hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ := hX'.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hks : L.ksb s' = L.ksb s := hw.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  -- the frame words
  have k1 : ∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    hw.mem_eq (mcpA_aligned hT ht) fun hb => J.dbgw_ne_tcb hb ht (mcpA_val hT ht) (by omega) rfl
  have k2 : ∀ t ∈ Z.T, L.mem s' (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    hw.mem_eq (yieldA_aligned hT ht) fun hb => J.dbgw_ne_tcb hb ht (yieldA_val hT ht) (by omega) rfl
  have kb : ∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => J.dbgw_ne_tcb hb ht (tIpcBufA_val (hT t ht)) (by omega) rfl
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s' w = L.mem s w := fun q z hq w hal h1 h2 =>
    hw.mem_eq hal fun hb => J.dbgw_ne_obj hb hq (fun e => by cases e) (by simp only [P1.HKind.bits]; omega) rfl
  have k3 : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word hS hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s' (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧ L.mem s' (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      hw.mem_eq (J.rp.aligned hr ha) fun hb => J.dbgw_ne_obj hb hHr (fun e => by cases e)
        (by simp only [P1.HKind.bits]; omega) rfl
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hH.align q _ hq
    have hfit := hH.fits q _ hq
    have hz := hH.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw J.kern.ksbFit J.kern.ksbAl fun b hb => by
      rcases J.dbgw_word hb with ⟨y, hy, g1, g2⟩ | e
      · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
      · simp only [P1.LawfulStore.nodeBase] at e; omega
  have hSS := J.dbgw_slots hw
  -- the dead stay dead
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep (G' := Z.G) hX' ⟨fun p => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun q hq => k3 q hq) hOut
      J.act.1 (J.yld.frame k2 F.ykeep) F.ykeep (J.jcov.dead q hq)
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hks hirq (J.idleW_keep hS' rfl rfl).2⟩
  have hkern := J.kern_dbg hks hw.2.1 hS' hhead
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s' σ :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hSS hdead (J.idleW_keep hS' rfl rfl), hkern,
      J.dbgw_utc hw hSS hhd, J.nsc, J.inv, J.cur, J.own, J.off, J.act, J.bsa, J.isorted, J.curRun, hblk⟩
  have hmem : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  exact J.cs_frame (G' := Z.G) hks hX' F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J.vkeep_of hw fun _ hb => J.dbgWc_nv hb)
    ⟨LiveJ.of_sameDbg J.live.1 hSS hmem rfl rfl hks hdbg (fun p hp => hdead p (J.zD p hp)), hDW',
      J.live.2.2.of_same (fun y hy => hSS.capV hy) rfl⟩ (J.zDX hSS J.zD)

/-- **A debug-list head after `debug_remove t`**: unchanged, or it was `t`
and is now `t`'s old successor (the other writes are TCB debug links). -/
theorem dbgRemove_head {T Cs : Set U64} (s : S) (t : U64) (hT : P1.TcbPlaced T)
    (hN : ∀ c ∈ Cs, P1.NodePlaced st T s c) (hD : P1.DbgTz st T Cs s) (hcpu0 : L.mem s (P1.affA t) ∈ Cs)
    (ht : t ∈ T) {c : U64} (hc : c ∈ Cs) :
    objects.debug_remove st s t ⦃ s' => L.mem s' (L.nodeAt s c layout.node.DEBUG_TCBS) =
        L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) ∨
      (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) = t ∧
        L.mem s' (L.nodeAt s c layout.node.DEBUG_TCBS) = L.mem s (P1.dnA t)) ⦄ := by
  have hb : P1.Aligned (L.nodeAt s c layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hN c hc) (by simp [P1.debug_val]) (by simp [P1.debug_val])
  have hkeep : ∀ (s0 : S) (y K v : U64), y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s0 (core.num.U64.wrapping_add y K) v) (L.nodeAt s c layout.node.DEBUG_TCBS) =
        L.mem s0 (L.nodeAt s c layout.node.DEBUG_TCBS) := by
    intro s0 y K v hy hK hK8
    rw [L.mem_wr _ _ _ _ (P1.field_aligned (hT y hy) hK hK8) hb,
      if_neg (fun e => P1.node_ne_field (hN c hc) (by simp [P1.debug_val]) hy (hT y hy) hK e.symm)]
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hcpu0
  have tpv : P1.Tz T pv := by rw [epv]; exact hD.dp t ht
  have tnx : P1.Tz T nx := by rw [enx]; exact hD.dn t ht
  refine WP.spec_bind (Pₘ := fun s1 => L.mem s1 (L.nodeAt s c layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) ∨
    (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) = t ∧ L.mem s1 (L.nodeAt s c layout.node.DEBUG_TCBS) = nx)) ?_ ?_
  · split
    · rename_i hht
      refine WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => ?_
      subst e
      rw [L.mem_wr _ _ _ _ (P1.nodeAt_aligned (hN cpu hcpu) (by simp [P1.debug_val]) (by simp [P1.debug_val])) hb]
      by_cases he : L.nodeAt s cpu layout.node.DEBUG_TCBS = L.nodeAt s c layout.node.DEBUG_TCBS
      · rw [if_pos he]; right; exact ⟨by rw [← he, ← ehd]; exact hht, rfl⟩
      · rw [if_neg he]; left; rfl
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by
          subst e; exact Or.inl (hkeep s pv 3576#u64 nx hpT (by simp) (by simp))
      · exact (WP.spec_ok _).2 (Or.inl rfl)
  intro s1 h1
  refine WP.spec_bind (Pₘ := fun s2 => L.mem s2 (L.nodeAt s c layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) ∨
    (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) = t ∧ L.mem s2 (L.nodeAt s c layout.node.DEBUG_TCBS) = nx)) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e; rw [show P1.dpA nx = core.num.U64.wrapping_add nx 3584#u64 from rfl,
          hkeep s1 nx 3584#u64 pv hnT (by simp) (by simp)]; exact h1
    · exact (WP.spec_ok _).2 h1
  intro s2 h2
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  rw [show P1.dnA t = core.num.U64.wrapping_add t 3576#u64 from rfl,
    hkeep _ t 3576#u64 0#u64 ht (by simp) (by simp),
    show P1.dpA t = core.num.U64.wrapping_add t 3584#u64 from rfl,
    hkeep _ t 3584#u64 0#u64 ht (by simp) (by simp)]
  rw [enx] at h2
  exact h2

set_option maxHeartbeats 4000000 in
/-- **`debug_remove t` at `J`, the liveness words** (KENTRY-PLAN g2i): the
lists after are the lists before with `t` erased (DbgWF's
`debug_remove_wf`), so every walk of core 0's list after is one before. -/
theorem JAtZ.dbgRemove_live (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    objects.debug_remove st s t ⦃ s' => (∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') ≠ 0#u64 → ∃ k,
      dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) ∧
      dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ 0#u64) ∧
      DbgWF (P1.Heap.tcbs H) Cs (L.mem s') (dbgHd (L := L) s') ⦄ := by
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have htT : t ∈ P1.Heap.tcbs H := by rw [← hTe]; exact ht
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := id J.blk
  have hTm := hX1.2.2.tm
  have hT : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← hTe]; exact hc.tcbs
  have hNa : ∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s c := fun c hc' => P1.TInv.nodes J.blk c hc'
  have hDa : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨hTm.dn, hTm.dp, hTm.dh⟩
  have hafa : L.mem s (P1.affA t) ∈ Cs := by rw [hc.aff t ht]; exact hcC
  obtain ⟨lst, hW⟩ := J.live.2.1
  have c0 : 0#u64 ∈ Cs := J.kern.cs0
  refine WP.spec_mono (debug_remove_wf s t hT hNa hDa hafa htT hW) fun s' hs' => ⟨fun n hn => ?_, ⟨_, hs'.2⟩⟩
  rcases dbgNth_mem_wf hs'.2 c0 n with h0 | hm
  · exact absurd h0 hn
  · obtain ⟨k, hk', e⟩ := List.getElem_of_mem (List.mem_of_mem_erase hm)
    refine ⟨k, ?_, ?_⟩
    · show dbgNth (L.mem s') n (L.mem s' (dbgHd (L := L) s' 0#u64)) =
        dbgNth (L.mem s) k (L.mem s (dbgHd (L := L) s 0#u64))
      rw [dbgNth_getElem_wf hW c0 k hk', e]
    · show dbgNth (L.mem s) k (L.mem s (dbgHd (L := L) s 0#u64)) ≠ 0#u64
      rw [dbgNth_getElem_wf hW c0 k hk', e]; exact hn

set_option maxHeartbeats 4000000 in
/-- **`debug_remove` at `J`**: P1's `debug_remove.frame` at the current
core alone (the thread's affinity, `SchedRel`), so the words written are
`DbgWc`; `BlkOK` after (`debug_remove.blk`), core 0's new list head null or
a TCB (P1's `TimerOK.dh`), outside every childless untyped cap's region:
the old head by `UtCapP3.rst`, or the removed head's successor
(`dbgRemove_head`), covered by `hU`, by `ut_free`. -/
theorem JAtZ.dbgRemoveJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hU : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∈ Z.T →
      L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))) ≠ 0#u64 →
      Covered (L.mem s) Z.G (L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))).val
        ((L.mem s (P1.dnA (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))).val + 1))
    {t : U64} (ht : t ∈ Z.T) :
    objects.debug_remove st s t ⦃ s' => JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a σ ⦄ := by
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have htT : t ∈ P1.Heap.tcbs H := by rw [← hTe]; exact ht
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := id J.blk
  have hTm := hX1.2.2.tm
  have hT : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← hTe]; exact hc.tcbs
  have hN : ∀ c ∈ ({Z.c} : Set U64), P1.NodePlaced st (P1.Heap.tcbs H) s c := fun c hc' => by
    rw [Set.mem_singleton_iff.1 hc']; exact P1.TInv.nodes J.blk Z.c hcC
  have hD : P1.DbgTz st (P1.Heap.tcbs H) {Z.c} s :=
    ⟨hTm.dn, hTm.dp, fun c hc' => by rw [Set.mem_singleton_iff.1 hc']; exact hTm.dh Z.c hcC⟩
  have haf : L.mem s (P1.affA t) ∈ ({Z.c} : Set U64) := by rw [hc.aff t ht]; exact Set.mem_singleton _
  have hNa : ∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s c := fun c hc' => P1.TInv.nodes J.blk c hc'
  have hDa : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨hTm.dn, hTm.dp, hTm.dh⟩
  have hafa : L.mem s (P1.affA t) ∈ Cs := by rw [hc.aff t ht]; exact hcC
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (P1.objects.debug_remove.frame s t hT hN hD haf htT)
    (P1.objects.debug_remove.blk s t J.blk htT)) (dbgRemove_head s t hT hNa hDa hafa htT J.kern.cs0))
    (J.dbgRemove_live ht)) ?_
  rintro s' ⟨⟨⟨⟨hw0, -⟩, hblk, -⟩, hhd0⟩, hdbgL, hDWL⟩
  have hw : P1.WritesIn st s s' (DbgWc (L := L) Z.T Z.c s) := hw0.mono fun b hb => by
    rcases hb with h | ⟨c, hc', e⟩
    · left; rw [hTe]; exact h
    · right; rw [Set.mem_singleton_iff.1 hc'] at e; exact e
  have hks : L.ksb s' = L.ksb s := hw.1
  obtain ⟨-, -, hX2, -, -⟩ := id hblk
  have hdh := hX2.2.2.tm.dh 0#u64 J.kern.cs0
  rw [P1.nodeAt_of_ksb hks] at hdh
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  refine J.dbgw_step hw hblk ?_ ?_ hdbgL hDWL
  · rcases hdh with h0 | hv
    · exact Or.inl h0
    · right
      have hal := hH.align _ _ hv
      have hfit := hH.fits _ _ hv
      have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12] at hal hfit
      refine ⟨(hJ.tcb _).2 hv, show _ ∧ _ from ⟨?_, by omega⟩⟩
      rw [← Nat.mod_mod_of_dvd _ (by norm_num : (32 : Nat) ∣ 4096), hal, Nat.zero_mod]
  · intro sl p sb fi dev hsl hcap g h0 hf0
    rcases hdh with e | hv
    · rw [e]
      rintro ⟨h1, -⟩
      have hh := (J.utc sl p sb fi dev hsl hcap (devF_of_notDev (capV_of_capAt hcap) g)).high g
      have h0' : (0#u64 : U64).val = 0 := rfl
      have e64 : (2 : Nat) ^ 64 - 2 ^ 47 = 18446603336221196288 := by norm_num
      rw [h0'] at h1
      rw [e64] at hh
      omega
    · have U := J.utc sl p sb fi dev hsl hcap (devF_of_notDev (capV_of_capAt hcap) g)
      rcases hhd0 with e | ⟨e1, e2⟩
      · rw [e]; exact (U.rst g h0 hf0).2
      · rw [e2]
        by_cases hz : L.mem s (P1.dnA t) = 0#u64
        · rw [hz]
          rintro ⟨h1, -⟩
          have hh := U.high g
          have h0' : (0#u64 : U64).val = 0 := rfl
          have e64 : (2 : Nat) ^ 64 - 2 ^ 47 = 18446603336221196288 := by norm_num
          rw [h0'] at h1
          rw [e64] at hh
          omega
        · have hcov := hU (by rw [e1]; exact ht) (by rw [e1]; exact hz)
          rw [e1] at hcov
          obtain ⟨hP, ⟨-, -, hM, hC, hI⟩, -⟩ := J.xtop.rel
          have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := capV_of_capAt hcap
          have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
            (hM.members _).2 ⟨hsl.isSlot, _, hcap, fun h => by cases h⟩
          have hfr := ut_free J.ut hI hxm hcv (nodesc_of_cdt hP hC hsl h0) (Nat.lt_succ_self _) hcov
          omega

/-- **No switch pending: the action word names no thread of the set**
(`JAtZ.words_of_spec`'s first half, the switch case excluded by `NoSwitch`). -/
theorem JAtZ.action_ne_of_noSwitch (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hns : Vs.NoSwitch σ) : L.actionW s ≠ t := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ea : L.actionW s = nodeW st s Z.c layout.node.SCHED_ACTION := by
    unfold P1.LawfulStore.actionW nodeW; rw [hc.cur]
  have ta := hc.tcbs t ht
  intro e
  have h := hS.act
  rw [← ea, e] at h
  cases ha : σ.schedulerAction with
  | resumeCurThread =>
    rw [ha] at h
    have h0 : t = 0#u64 := h
    exact ta.ne0 (by rw [h0]; rfl)
  | chooseNewThread =>
    rw [ha] at h
    have h1 : t = 1#u64 := h
    have hv : t.val = 1 := by rw [h1]; rfl
    have := ta.align
    rw [hv] at this; norm_num at this
  | switchThread u => exact hns u ha

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a final thread cap's finalisation** (module docstring),
the steps of `JThreadFinHyps` given, the FPU release's arch step by `ARKeep` [P]. -/
theorem JAtZ.finThreadJ (hAT : P0.ArchTotal arI) (hK : ARKeep arI AR) (hF : JThreadFinHyps (L := L) arI AR Z.th)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ Z.T)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) (hna : L.actionW s ≠ p) (hidle : L.idleW s ≠ p) :
    objects.finalise_cap st arI s a (.Thread p) true false ⦃ r => ∃ σ',
      ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
        (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
      JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  have hfc : objects.finalise_cap st arI s a (.Thread p) true false =
      objects.finalise_cap_object st arI s a (.Thread p) true := by
    simp [objects.finalise_cap]
  rw [hfc]
  unfold objects.finalise_cap_object
  simp only [↓reduceIte]
  have hS0 := J.xtop.fin.1.1.1
  obtain ⟨hsa, hid⟩ := J.spec_of_words hna hidle
  -- the remote stall and the VCPU detach
  refine WP.spec_bind (remote_tcb_stall_id (ar := arI) a hS0 hp) ?_
  rintro ⟨s1, a1⟩ he1
  simp only [Prod.mk.injEq] at he1
  obtain ⟨hs1, ha1⟩ := he1
  subst s1; subst a1
  refine WP.spec_bind (vcpu_detach_none arI s a p hv0) ?_
  rintro ⟨s1, a1⟩ he1
  simp only [Prod.mk.injEq] at he1
  obtain ⟨hs1, ha1⟩ := he1
  subst s1; subst a1
  -- `unbind_notification`
  have h3 : notification.unbind_notification st s p ⦃ s3 => ∃ σ3,
      Fl4Spec.unbindNotification (Z := Unit) p.bv σ = ({((), σ3)}, False) ∧
      σ3.schedulerAction = σ.schedulerAction ∧ σ3.idleThread = σ.idleThread ∧ σ3.curThread = σ.curThread ∧
      JTP (L := L) arI AR Z H Cs s3 a σ3 ⦄ := by
    by_cases h0 : L.mem s (P1.boundA p) = 0#u64
    · rw [unbind_ntfn_zero s p h0, WP.spec_ok]
      have hI0 := J.xtop.irelK J.ks J.buf
      obtain ⟨x, hk, hx⟩ := hI0.1.tcb p hp
      refine ⟨σ, unbindNtfn_none hk ?_, rfl, rfl, rfl, Z.vs, Ac, Lst, D, J⟩
      rw [hx.bound, show tBoundA p = P1.boundA p from rfl, h0, Notif.optRef_zero]
    · exact J.unbindNJ hp h0
  refine WP.spec_bind h3 ?_
  rintro s3 ⟨σ3, he3, ha3, hi3, hc3, V3, Ac3, Lst3, D3, J3⟩
  -- the timer-tree removal
  refine WP.spec_bind (J3.tmRemoveJ hp) ?_
  intro s4 J4
  -- the rest, after `unbind_from_sc`
  have fin6 : ∀ (s5 : S) (a5 : A) (σ5 : Fl4Spec.State Unit), JTP (L := L) arI AR Z H Cs s5 a5 σ5 →
      Fl4Spec.unbindFromSc (Z := Unit) p.bv σ3 = ({((), σ5)}, False) →
      σ5.curThread = σ.curThread ∧ σ5.idleThread = σ.idleThread ∧
        (σ5.schedulerAction = σ.schedulerAction ∨ σ5.schedulerAction = .chooseNewThread) →
      (do
        let (s6, a4) ← sched.suspend st arI s5 a5 p
        let s7 ← objects.debug_remove st s6 p
        let a6 ← arI.fpu_release a4 p
        let s8 ← obj.Tcb.slot p layout.tcb.SLOT_CTABLE
        ok ((capability.Cap.Zombie s8 capability.ZOMBIE_TCB layout.tcb.NUM_SLOTS, capability.Cap.Null), s7, a6))
        ⦃ r => ∃ σ', ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
          JTP (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    rintro s5 a5 σ5 ⟨V5, Ac5, Lst5, D5, J5⟩ he5 ⟨hc5, hi5, ha5⟩
    have hsa5 : ∀ u, σ5.schedulerAction = .switchThread u → u ≠ p.bv := fun u hu => by
      rcases ha5 with e | e
      · exact hsa u (by rw [← e]; exact hu)
      · rw [e] at hu; cases hu
    have hid5 : p.bv ≠ σ5.idleThread := by rw [hi5]; exact hid
    refine WP.spec_bind (JAtZ.suspendJ (Z := Z.mv Z.G V5) (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI) (jCancel_reply arI) J5 hp hsa5 hid5) ?_
    rintro ⟨s6, a6⟩ ⟨ha6, σ6, he6, V6, Ac6, Lst6, D6, J6⟩
    simp only at ha6
    subst ha6
    refine WP.spec_bind (J6.dbgRemoveJ (hF.utTcb (Z.mv Z.G V6) H Cs Ac6 Lst6 D6 s6 _ σ6 rfl J6) hp) ?_
    intro s7 J7
    refine WP.spec_bind (J7.fpuReleaseJ hK hp) ?_
    rintro a8 ⟨σ8, hm8, V8, J8⟩
    simp only [P1.tcb_slot_ctable, bind_ok, WP.spec_ok]
    exact ⟨σ8, finThread_mem he3 he5 he6 hm8, V8, Ac6, Lst6, D6, J8⟩
  -- `unbind_from_sc`
  obtain ⟨Q4, R4, hc4, hs4⟩ := J4.xtop.fin.1.1.1.lists
  obtain ⟨x4, hk4, -, -, hsc4, -⟩ := hs4.tcb p hp
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  step with obj.Sc.is_null.spec' as ⟨b, hb⟩
  by_cases h0 : i = 0#u64
  · have hb' : b = true := by rw [hb, h0]; rfl
    simp only [hb', ↓reduceIte, bind_ok]
    exact fin6 s4 a σ3 ⟨V3, Ac3, Lst3, D3, J4⟩ (unbindFromSc_none hk4 (by rw [hsc4, ← hi, h0, Notif.optRef_zero]))
      ⟨hc3, hi3, Or.inl ha3⟩
  have hb' : b = false := by rw [hb]; simp [h0]
  simp only [hb', Bool.false_eq_true, ↓reduceIte]
  have hiC : i ∈ Z.C := by rw [hi]; exact hs4.scMem p hp (by rw [← hi]; exact h0)
  have hsp : x4.tcbSchedContext = some i.bv := by rw [hsc4, ← hi, Notif.optRef_ne h0]
  have hin : (do
      let s6 ← schedcontext.unbind_tcb st s4 i
      let i1 ← obj.Sc.yield_from st i s6
      let b1 ← obj.Tcb.is_null i1
      if b1 = true then ok (s6, a) else schedcontext.complete_yield_to st arI s6 a i1) ⦃ r =>
      ∃ σ5, JTP (L := L) arI AR Z H Cs r.1 r.2 σ5 ∧
        Fl4Spec.unbindFromSc (Z := Unit) p.bv σ3 = ({((), σ5)}, False) ∧
        σ5.curThread = σ.curThread ∧ σ5.idleThread = σ.idleThread ∧
        (σ5.schedulerAction = σ.schedulerAction ∨ σ5.schedulerAction = .chooseNewThread) ⦄ := by
    refine WP.spec_bind (J4.unbindTcbJ hp hiC hk4 hsp (by rw [ha3]; exact hsa) (by rw [hi3]; exact hid)) ?_
    rintro s5 ⟨σ4, he4, Ac5, Lst5, D5, J5⟩
    have hca4 : σ4.curThread = σ.curThread ∧ σ4.idleThread = σ.idleThread ∧
        (σ4.schedulerAction = σ.schedulerAction ∨ σ4.schedulerAction = .chooseNewThread) := by
      obtain ⟨y', n', hky', hyt'⟩ := J4.inv.back p.bv x4 i.bv hk4 hsp
      obtain ⟨σ4', e4', -, -, -, ct4, -, -, -, idl4, -, -, a14, b14⟩ :=
        Sched.unbindTcb_shape J4.inv.actReady hky' hyt' hk4
      have e := the_result e4' he4
      subst e
      refine ⟨ct4.trans hc3, idl4.trans hi3, ?_⟩
      by_cases hpc : p.bv = σ3.curThread
      · exact Or.inr (a14 hpc)
      · exact Or.inl ((b14 hpc).trans ha3)
    obtain ⟨Q5, R5, hc5, hs5⟩ := J5.xtop.fin.1.1.1.lists
    obtain ⟨y5, n5, hk5, hx5⟩ := hs5.scs i hiC
    step with obj.Sc.yield_from.spec' as ⟨j, hj⟩
    step with obj.Tcb.is_null.spec as ⟨b1, hb1⟩
    by_cases j0 : j = 0#u64
    · have hb1' : b1 = true := by rw [hb1, j0]; rfl
      simp only [hb1', ↓reduceIte, WP.spec_ok]
      refine ⟨σ4, ⟨V3, Ac5, Lst5, D5, J5⟩, unbindFromSc_some hk4 hsp he4 hk5 ?_, hca4⟩
      rw [hx5.yieldFrom, ← scYieldFromA_eq, ← hj, j0, Notif.optRef_zero]; rfl
    · have hb1' : b1 = false := by rw [hb1]; simp [j0]
      simp only [hb1', Bool.false_eq_true, ↓reduceIte]
      rw [hj]
      have hjT : L.mem s5 (scYieldFromA i) ∈ Z.T := by
        have e5 : y5.scYieldFrom = some (L.mem s5 (scYieldFromA i)).bv := by
          rw [hx5.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hj]; exact j0)]
        obtain ⟨t, ht, et, -⟩ := J5.yld.frm i hiC y5 n5 hk5 _ e5
        rw [← P1.eq_of_bv et]; exact ht
      refine WP.spec_mono (J5.completeYieldJ hAT hF.ticks.1 (hF.ticks.2 a) hjT) ?_
      rintro ⟨s6, a6⟩ ⟨σ6, e6, V6, Ac6, Lst6, D6, J6⟩
      obtain ⟨xj, hkj, eyj⟩ := J5.yld.tcb _ hjT
      have hqj : ∀ q, xj.tcbYieldTo = some q → ∃ z n, σ4.kheap q = some (.schedContext z n) := by
        intro q hq
        by_cases h0 : L.mem s5 (yieldA (L.mem s5 (scYieldFromA i))) = 0#u64
        · rw [eyj, h0, Notif.optRef_zero] at hq; cases hq
        · obtain ⟨-, z, n, hkz, -⟩ := J5.yld.toSc _ hjT h0
          rw [eyj, Notif.optRef_ne h0] at hq; cases hq; exact ⟨z, n, hkz⟩
      obtain ⟨c6, a6', i6⟩ := Sched.completeYieldTo_ca hkj hqj e6
      refine ⟨σ6, ⟨V6, Ac6, Lst6, D6, J6⟩, unbindFromSc_some hk4 hsp he4 hk5 ?_, c6.trans hca4.1,
        i6.trans hca4.2.1, by rw [a6']; exact hca4.2.2⟩
      rw [hx5.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hj]; exact j0)]; exact e6
  refine WP.spec_bind hin ?_
  rintro ⟨s5, a5⟩ ⟨σ5, hJ5, he5, hca5⟩
  exact fin6 s5 a5 σ5 hJ5 he5 hca5

/-- **A thread cap's slot is ready once the thread is dead** (as
XTopJointDelR's `JAtZ.ep_ready`: the TCB the only object of `H` in the
cap's range). -/
theorem JAtZ.tcb_ready (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {p : U64}
    (hcv : capV (L.mem s) x = .Thread p) (hHp : H p = some .tcb) (hd : DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  have hpfit : p.val + 2 ^ 12 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  obtain ⟨e1, e2⟩ := range_thread p hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ 12 ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p .tcb hq hHp hne
    simpa only [show (P1.HKind.tcb).bits = 12 from rfl] using this
  refine fun lo hi hlh h1 h2 => ?_
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega

end

end

end Fl4Proofs.P3
