/-
P3 (p3J gen 46): **`RR` and `NativeScope` through the deletion loop, and the TCB installs at stable ghosts**.

FL4 `cdt.rs` l.271–316 / l4v `rec_delete`: P3JFinWJL's generic lift (`WSp P W := W ∧ P σ`, `SpLoopK P`: the loop's
six spec steps keep `P`, `DelHypsWRZ.sp`) instantiated at the two spec predicates the stable preempted exit needs
(P3JPreSt's `midXP_of_wjpv`): the SC-period frame `RR` (P3JRrSys; P3JRrG's `rq_*`) and `NativeScope` (no thread
`runningVM`; SpecInvNativeScopeF*'s `ns_*`).

* `ik_rr_of_rq`, **`spLoopK_rr`**, **`spLoopK_ns`**, `RrNs := RR ∧ NativeScope`, `spLoopK_rrns`.
* The installs' invariants at stable ghosts, footprint from the label's start `s0`:
  `WJSt s0 kb := WSp RrNs (WFt s0 (WMR MR (WCk (WJL kb))))` (Ok), `WJStP s0 kb := WSp RrNs (WFt s0 (WCk (WJPMV kb)))`
  (preempted); **`delHypsJLMstC`**: the deletion bundle there (P3JDelMT's `delHypsJLMftC` + `DelHypsWRZ.sp`).
* **`midX_of_wjst`** / **`midXP_of_wjstp`**: P3JMidInv's `MidX` / `MidXP` from them (the latter by P3JPreSt's
  `midXP_of_wjpv`; platform facts `IrqPlatK` [P] among them, see P3JPreSt).
* **`insWJ_st`** (XTopJointTcbInstall's `InsWJ` at `WJSt`): the insert of a TCB slot keeps `CKI` (the new cap has
  the shape of a typed slot's cap, so it is `KW`: `kw_absCap_shape`, `kw_of_cki`; the spec cap at the slot after the
  insert is the new one: SpecFbX's `fbx_capInsert_at`), `RR`, `NativeScope`, `MRV` and the footprint (the slot words
  are `ProjW`); the IPC buffer's word and the scheduler (`BufHypW`): `JAtZ.ipcBufProjW`, `JAtZ.bufTailProjW`.
* **`restartWJSt`**: the caller's restart at `WJSt` (`WJL.restart`, `stsProjW`).
* **`tcbInsWG_st`**: XTopJointMRTcb's `TcbInsWG` at `WJSt` / `WJStP`, from the stable tops' platform facts only.

No named premise (lemma hypotheses are platform facts of the stable tops). No sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JPreSt
import Fl4Proofs.P3.P3JRrG
import Fl4Proofs.P3.P3JRrSys
import Fl4Proofs.P3.SpecInvNativeScopeF3
import Fl4Proofs.P3.SpecInvNativeScopeF2
import Fl4Proofs.P3.SpecInvNativeScopeBridge
import Fl4Proofs.P3.XTopJointMRTcbM
import Fl4Proofs.P3.XTopJointTcbInsL
import Fl4Proofs.P3.XTopJointWJLRestart
import Fl4Proofs.P3.P3JThTls
import Fl4Proofs.P3.P3JMcBuf
import Fl4Proofs.P3.SpecFbX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## `RR` and `NativeScope` through the loop's spec steps -/

/-- (p3J gen 46) A step keeping every SC period keeps `RR`. -/
theorem ik_rr_of_rq {α : Type} {m : Fl4Spec.NonDet (Fl4Spec.State Unit) α} (h : SInvRr.RQ m) :
    SInv.IK SInvRr.RR m := fun σ hσ x hx => by
  show SInvRr.rpV x.2 = fun _ => 0
  rw [h σ x hx]; exact hσ

/-- (p3J gen 46) **The loop's steps keep `RR`** (P3JRrG / P3JRrF). -/
theorem spLoopK_rr : SpLoopK SInvRr.RR where
  fin c b := ik_rr_of_rq (SInvRr.rq_finaliseCap c b)
  pp := ik_rr_of_rq (m := ExceptT.run (Fl4Spec.preemptionPoint (Z := Unit))) SInvRr.rqe_preemptionPoint'
  post c := ik_rr_of_rq (SInvRr.rq_postCapDeletion' c)
  zomb _ _ _ sl := ik_rr_of_rq (SInvRr.rq_setCap _ sl)
  swap s1 s2 := ik_rr_of_rq (SInvRr.rq_capSwapForDelete' s1 s2)
  empty sl c := ik_rr_of_rq (SInvRr.rq_emptySlot' sl c)

/-- (p3J gen 46) **The loop's steps keep `NativeScope`** (SpecInvNativeScopeF2 / F3). -/
theorem spLoopK_ns : SpLoopK NativeScope where
  fin c b := SInv.ns_finaliseCap c b
  pp := SInv.ns_preemptionPoint
  post c := SInv.ns_postCapDeletion c
  zomb _ _ _ sl := SInv.ti_setCap (Q := SInv.nsQ) _ sl (fun _ hx => ⟨hx, hx, hx, hx, hx, hx⟩)
  swap s1 s2 := SInv.ns_capSwapForDelete s1 s2
  empty sl c := SInv.ns_emptySlot sl c

/-- (p3J gen 46) The two spec predicates the stable preempted exit reads besides `CKI`. -/
abbrev RrNs (σ : Fl4Spec.State Unit) : Prop := SInvRr.RR σ ∧ NativeScope σ

theorem spLoopK_rrns : SpLoopK RrNs := spLoopK_rr.and spLoopK_ns

/-- (p3J gen 46) The new cap of a TCB-slot insert has a typed slot's shape: `KW` is a property of the shape. -/
theorem kw_absCap_shape (c : capability.Cap) : SInvCk.KW (absCap (shape c)) ↔ SInvCk.KW (absCap c) := by
  cases c <;> simp [shape, absCap, SInvCk.KW]

/-! ## The installs' invariants at stable ghosts -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- (p3J gen 46) **The installs' Ok invariant at stable ghosts** (module docstring). -/
abbrev WJSt (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs : Set U64) (s0 : S) (kb : U64) : S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  WSp RrNs (WFt (L := L) H Cs s0 (WMR MR (WCk (WJL (L := L) arI AR Z H Cs kb))))

/-- (p3J gen 46) The window invariant of `WJSt`. -/
abbrev WJStx (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs : Set U64) (s0 : S) (kb : U64) : S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  WSp RrNs (WFt (L := L) H Cs s0 (WMR MR (WCk (WJLx (L := L) arI AR Z H Cs kb))))

/-- (p3J gen 46) **The installs' preempted invariant at stable ghosts** (module docstring). -/
abbrev WJStP (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs : Set U64) (s0 : S) (kb : U64) : S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  WSp RrNs (WFt (L := L) H Cs s0 (WCk (WJPMV (L := L) arI AR MR Z H Cs kb)))

variable {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}
  {th : TypedHeap}

/-- (p3J gen 46) **The deletion bundle at `WJSt` / `WJStP`** (module docstring). -/
theorem delHypsJLMstC [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) [VxE Z] (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) (s0 : S) :
    DelHypsWRZ (L := L) arI (WJSt (L := L) arI AR MR Z H Cs s0 kb) (WJStx (L := L) arI AR MR Z H Cs s0 kb)
      (WJStP (L := L) arI AR MR Z H Cs s0 kb) (RdLX (L := L) (A := A) th H Z.vx) (RzJ (L := L) (A := A) H Cs) th :=
  DelHypsWRZ.sp arI spLoopK_rrns (delHypsJLMftC arI hT hK hticks hnd hM hKD hPA hAM Z H Cs kb hth s0)

variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 46) **`MidX` at the installs' Ok invariant** (module docstring). -/
theorem midX_of_wjst {kb : U64} {s0 s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WJSt (L := L) arI AR MR Z H Cs s0 kb s a σ G) : MidX (L := L) arI AR MR Z H Cs s0 s a σ := by
  obtain ⟨⟨⟨⟨⟨⟨V, Ac', Lst', D', J, -⟩, -⟩, -⟩, hMV⟩, hF⟩, -⟩ := h
  exact ⟨⟨G, V, Ac', Lst', D', J⟩, hMV.1, hF⟩

/-- (p3J gen 46) **`MidXP` at the installs' preempted invariant** (module docstring; P3JPreSt's `midXP_of_wjpv`). -/
theorem midXP_of_wjstp [VxE Z] (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR) (hTA : TimeAgree arI)
    (hPA : PPPlatA arI AR) {kb : U64} {s0 s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WJStP (L := L) arI AR MR Z H Cs s0 kb s a σ G) : MidXP (L := L) arI AR MR Z H Cs s0 s a σ :=
  midXP_of_wjpv hARI hAT hnd hM hKD hIP hTA hPA h.1 h.2.1 h.2.2

/-- (p3J gen 46) **The IPC buffer's word of a typed-heap TCB is a `ProjW` write** (as P3JThTls's `tlsProjW`). -/
theorem JAtZ.ipcBufProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (htH : Z.th t = some .tcb) (w : U64) :
    P1.WritesIn st s (L.wr s (tIpcBufA t) w) (Mc.ProjW (L := L) H Cs s) := by
  have hP := J.xtop.rel.1
  have ht : t ∈ Z.T := J.thT t htH
  have hf := hP.fits t _ htH
  simp only [objSize] at hf
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hta := hc.tcbs t ht
  have hv := tIpcBufA_val hta
  have hH : H t = some .tcb := J.zH.1 t ht
  refine (P1.writesIn_wr (s := s) (v := w) (tIpcBufA_aligned hta)).mono ?_
  rintro b rfl
  exact Or.inl ⟨t, .tcb, hH, by rw [hv]; omega, by rw [hv]; simp only [P1.HKind.bits]; omega⟩

/-- (p3J gen 46) **`install_buffer`'s scheduler tail writes only `ProjW`** (`JAtZ.reschedProjW`). -/
theorem JAtZ.bufTailProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (t : U64) (a' : A) :
    (do
      let t_1 ← sched.cur_thread st s
      let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t_1
      if b1 = true then do
          let s5 ← sched.reschedule_required st s
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a')
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a')) ⦃ res =>
      P1.WritesIn st s res.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  rw [cur_thread_eq]
  simp only [bind_ok, tcb_eq_ct]
  split
  · refine WP.spec_bind J.reschedProjW ?_
    intro s5 h5
    rw [WP.spec_ok]; exact h5
  · rw [WP.spec_ok]; exact P1.WritesIn.refl _ _

/-- (p3J gen 46) The spec side of `install_buffer`'s tail keeps an invariant `rescheduleRequired` keeps. -/
theorem bufTail_ik {P : Fl4Spec.State Unit → Prop} (hR : SInv.IK P (Fl4Spec.rescheduleRequired (Z := Unit)))
    (t : U64) :
    SInv.IKE P ((do
      let cur ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
      Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.when (t.bv = cur) Fl4Spec.rescheduleRequired) :
        Fl4Spec.PMonad Unit Unit)) :=
  SInv.ike_bind (SInv.ike_liftE (SInv.ik_gets _)) fun _ => SInv.ike_liftE (SInv.ik_when _ hR)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 46) **XTopJointTcbInstall's `InsWJ` at `WJSt`** (module docstring). -/
theorem insWJ_st (hM : MachPlatC arI MR) (s0 : S) (kb : U64) :
    InsWJ (L := L) arI AR Z H Cs kb (WJSt (L := L) arI AR MR Z H Cs s0 kb) := by
  have h0 := insWJ_wjl (L := L) arI (AR := AR) (Z := Z) (H := H) (Cs := Cs) kb
  refine ⟨fun s a σ G h => h.1.1.1.1.1, ?_, fun t ht addr => ?_⟩
  · intro s s' a σ σ' G G' t n c src hDS hW hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive
    obtain ⟨⟨⟨⟨hL, hC⟩, hMV⟩, hF⟩, hRR, hNS⟩ := hW
    obtain ⟨V, Ac0, Lst0, D0, J, -⟩ := hL.1
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 :=
      mem_of_single hci
    -- the new cap is `KW`
    have hkw : SInvCk.KW c := by
      have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
      obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS'.1.1.abs_cap hAt
      have hm0 : (a0, σ') ∈ (Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ').1 := by
        rw [hg0]; exact Set.mem_singleton _
      have e1 := (SInvU.getCap_capAt hm0).2
      have e2 := SInv.fbx_capInsert_at hmem
      have ec : c = absCap (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) := by
        rw [capV_of_capAt hc0, ← hca0.abs]
        exact Option.some.inj (e2.symm.trans e1)
      obtain ⟨y0, hy0, hshy⟩ := hsh
      rw [ec, ← kw_absCap_shape, hshy, kw_absCap_shape]
      exact Mc.kw_of_cki J hC hy0
    refine ⟨⟨⟨⟨h0.ins s s' a σ σ' G G' t n c src hDS hL hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive,
        SInvCk.ck_capInsert c src _ hkw σ hC _ hmem⟩,
      mrv_keepC hM hMV (MachT.mtk_capInsert c src _ σ ((), σ') hmem)⟩,
      hF.projW_trans (hwS.mono fun b hb => by
        obtain ⟨x, hx, k, hk, e⟩ := hb
        exact J.slotWdProjW ⟨x, k, hx, hk, e⟩)⟩,
      ik_rr_of_rq (SInvRr.rq_capInsert c src _) σ hRR _ hmem, SInv.ns_capInsert c src _ σ hNS _ hmem⟩
  · have hb0 := h0.buf t ht addr
    refine ⟨fun s a σ G hDS hW hnull => ?_, fun s a σ G hDS hW => ?_⟩
    · obtain ⟨⟨⟨⟨hL, hC⟩, hMV⟩, hF⟩, hRR, hNS⟩ := hW
      obtain ⟨V, Ac0, Lst0, D0, J, -⟩ := hL.1
      refine WP.spec_mono (WP.spec_and (hb0.ipc s a σ G hDS hL hnull) (set_ipc_buffer_wr s t addr)) ?_
      rintro s' ⟨⟨hSS, σ', hm, hCR, hK, hW'⟩, rfl⟩
      exact ⟨hSS, σ', hm, hCR, hK, ⟨⟨⟨⟨hW', SInvV.hv_threadSet (P := SInvCk.CKI)
          (fun x => { x with tcbIpcBuffer := addr.bv }) t.bv (fun _ => rfl) σ hC _ hm⟩,
        mrv_keepC hM hMV (MachT.mtk_threadSet' _ _ σ ((), σ') hm)⟩, hF.projW_trans (J.ipcBufProjW ht addr)⟩,
        ik_rr_of_rq (SInvRr.rq_threadSet' _ _) σ hRR _ hm,
        SInv.ti_threadSet (Q := SInv.nsQ) (fun x => { x with tcbIpcBuffer := addr.bv }) t.bv
          (fun _ hx => hx) σ hNS _ hm⟩⟩
    · obtain ⟨⟨⟨⟨hL, hC⟩, hMV⟩, hF⟩, hRR, hNS⟩ := hW
      obtain ⟨V, Ac0, Lst0, D0, J, -⟩ := hL.1
      refine WP.spec_mono (WP.spec_and (hb0.tail s a σ G hDS hL) (J.bufTailProjW t a)) ?_
      rintro res ⟨⟨h1, h2, hSS, σ', hm, hCR, hK, hW'⟩, hFt⟩
      refine ⟨h1, h2, hSS, σ', hm, hCR, hK, ⟨⟨⟨⟨hW',
        bufTail_ik (SInvV.hv_rescheduleRequired (P := SInvCk.CKI)) t σ hC _ hm⟩, ?_⟩, hF.projW_trans hFt⟩,
        bufTail_ik (ik_rr_of_rq SInvRr.rq_rescheduleRequired') t σ hRR _ hm,
        bufTail_ik SInv.ns_rescheduleRequired t σ hNS _ hm⟩⟩
      rw [h2]
      exact mrv_keepC hM hMV (dke_bind (dke_liftE (dk_gets _))
        (fun _ => dke_liftE (dk_when _ MachT.mtk_rescheduleRequired')) σ _ hm)

/-- (p3J gen 46) **The caller's restart at `WJSt`** (module docstring). -/
theorem restartWJSt (hM : MachPlatC arI MR) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ) :
    RestartWJ (st := st) Z s ar σ (WJSt (L := L) arI AR MR Z H Cs s (L.ksb s)) := by
  intro ct hct s1 σ1 h1 h2
  have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ).1 := mem_of_single h2
  have hctT : ct ∈ Z.T := by
    obtain ⟨hcur, -⟩ := J.curEq hct
    exact J.thT ct (J.xtop.curTcb hcur).1
  have hF := stsProjW J hctT sched.TS_RESTART
  rw [h1, WP.spec_ok] at hF
  exact ⟨⟨⟨⟨WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2,
      SInvV.hv_setThreadState (P := SInvCk.CKI) _ _ σ hC _ hm⟩,
    mrv_keepC hM hMV (MachT.mtk_setThreadState' _ _ σ ((), σ1) hm)⟩, hF⟩,
    ik_rr_of_rq (SInvRr.rq_setThreadState' _ _) σ hRN.1 _ hm,
    SInv.ns_setThreadState _ _ (fun h => by cases h) σ hRN.2 _ hm⟩

/-- (p3J gen 46) **`TcbInsWG` at `WJSt` / `WJStP`** (module docstring). -/
theorem tcbInsWG_st [Fl4Proofs.P1.PlainStore st] [VxE Z] (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (s0 : S) :
    TcbInsWG (L := L) arI AR Z H Cs (fun kb => WJSt (L := L) arI AR MR Z H Cs s0 kb)
      (fun kb => WJStP (L := L) arI AR MR Z H Cs s0 kb) (RdLX (L := L) (A := A) Z.th H Z.vx)
      (RzJ (L := L) (A := A) H Cs) :=
  ⟨fun kb => insWJ_st hM s0 kb, fun kb => ⟨_, delHypsJLMstC hT hK hticks hnd hM hKD hPA hAM Z H Cs kb rfl s0⟩⟩


/-- (p3J gen 46) `MidX` at `Z.mv G V` is `MidX` at `Z` (`JStab.mv`). -/
theorem MidX.mv {G : MdbGhost} {V : XVs} {s0 s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : MidX (L := L) arI AR MR (Z.mv G V) H Cs s0 s a σ) : MidX (L := L) arI AR MR Z H Cs s0 s a σ :=
  ⟨JStab.mv h.1, h.2.1, h.2.2⟩

/-- (p3J gen 46) `MidXP` at `Z.mv G V` is `MidXP` at `Z` (`JStab.mv`). -/
theorem MidXP.mv {G : MdbGhost} {V : XVs} {s0 s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : MidXP (L := L) arI AR MR (Z.mv G V) H Cs s0 s a σ) : MidXP (L := L) arI AR MR Z H Cs s0 s a σ := by
  refine ⟨h.1, WP.spec_mono h.2 fun r hr => ?_⟩
  obtain ⟨h1, ⟨z, hz, hJ, hm⟩, h3⟩ := hr
  exact ⟨h1, ⟨z, hz, JStab.mv hJ, hm⟩, h3⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 46) **SetSpace (11) at stable ghosts, with its `ProjW` footprint and the stable preempted exit**
(XTopJointMRTcbM's `tcb_set_spaceJMG` at `TcbInsWG` = `tcbInsWG_st`; module docstring). The start's facts
(`Entered`, `SpecGlob`, `PPR0`, `LiveDN`, `MRV`, `CKI`, `RR`, `NativeScope`, `NcHyp`) are hypotheses; the start at
`Z.mv G V` (a dispatch state), the exits at `Z`. -/
theorem tcb_set_spaceJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSpace)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.TCBSetSpace p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv)
      ci ssl excaps buffer :=
  tcb_set_spaceJMG (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s) arI s ar σ J
    hni hsg hP0
    (tcbInsWG_st hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask s)
    ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩ (fun _ _ _ _ _ h => (midX_of_wjst h).mv)
    (fun _ _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩)
    (restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN) p hp slbl hlbl length buf ct hct args hlen hargs hstall
    call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hnc blk don ci buffer

end

end

end Fl4Proofs.P3
