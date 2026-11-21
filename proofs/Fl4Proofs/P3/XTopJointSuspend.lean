/-
P3 (DESIGN.md §9): **`suspend` at `J`** (`JAtZ.suspendJ`, toward a final
thread cap's finalisation, XTopJointFinThread's `JThreadFinHyps.suspend`).
FL4's `sched::suspend` against the spec's `suspend`, from `JAtZ` before to
`JAtZ` after, in three `J` steps:

* `cancel_ipc` (`JAtZ.cancelFreeJ` for a thread blocked on nothing: the
  fault clear, a register-frame step `JAtZ.reg_frameF` with `QKY`; a blocked
  thread's by the arguments `hSd`, `hNt`, `hRv`, `hRp`, one `JCancelAt` per
  blocking state: XTopJointCancel's `jCancel_send`, `jCancel_ntfn`,
  XTopJointCancelRecv's `jCancel_recv`, XTopJointCancelReply's
  `jCancel_reply`);
* the restart PC of a running thread (`JAtZ.restartPcJ`: a register step);
* the scheduler tail (`JAtZ.suspendScJ`): the dequeue, the release-queue
  removal, the yield-to cut and `set_thread_state Inactive` as one SC step
  (`JAtZ.sc_frame`; the middle states break `Inv`): FL4's footprint `TFoot`
  (`SFootI` words, the yield words and the SC's `YIELD_FROM` word, the state
  word), the spec frame `SusF` (XTopJointSuspendSpec), `Inv` by
  `suspendSc_inv`, the call stacks by `ScAll.of_tr` (`Pres (false, true)`),
  the dead by `deadP_sc_stepG` (an `Inactive` thread stays `Inactive`). P1's
  `BlkOK` after and the node-0 debug word are supplied by the caller (P1's
  whole-`suspend` lemmas, `sched.suspend.blk`).

Named premises of `JAtZ.suspendJ`: the thread neither the switch target nor
idle (as `JThreadFinHyps.obj`). The current thread may be suspended with a
switch pending: `CurRunM` allows a non-runnable current thread whenever the
action is not `resumeCurThread` (`SusF.curRun`).
-/
import Fl4Proofs.P3.XTopJointSuspendSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat}

/-- **`cancel_ipc` keeps `BlkOK`** (`sched.suspend.all`'s first step). -/
theorem ipc.cancel_ipc.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    ipc.cancel_ipc st ar s a t ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (ipc.cancel_ipc.all s a t Q R h0 ht hB hX hSg.sub) fun r hr => ?_
  obtain ⟨s1, a1⟩ := r
  try simp only [WP.uncurry'_pair] at hr
  obtain ⟨h1, hB1, hX1, -, -, -, k1, -⟩ := hr
  exact ⟨⟨Q, R, h1⟩, hB1, hX1, hS.keepT hX k1, ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
    fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- The scheduler's written words are scheduler words. -/
theorem sfootI_sfoot {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {T : Set U64} {c : U64} {s : S}
    {b : U64} (h : SFootI st T c s b) : SFoot st T c s b := by
  rcases h with ⟨y, hy, e | e | e⟩ | ⟨g1, g2, -⟩
  · exact Or.inl ⟨y, hy, 3480#u64, by unfold SOff SOffL; decide, e⟩
  · exact Or.inl ⟨y, hy, 3488#u64, by unfold SOff SOffL; decide, e⟩
  · exact Or.inl ⟨y, hy, 3592#u64, by unfold SOff SOffL; decide, e⟩
  · exact Or.inr ⟨g1, g2⟩

theorem ipcFree_code {ts : Fl4Spec.ThreadState} (h : IpcFree ts) :
    tsCode ts ≠ 3 ∧ tsCode ts ≠ 4 ∧ tsCode ts ≠ 6 := by
  obtain ⟨h1, h2, h3⟩ := h
  cases ts <;> simp_all [tsCode, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked]

/-- A thread is at most in its own ready queue (IpcCopyRegsJ's `rq_own`). -/
theorem rq_ownS {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {N T C : Set U64} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    ∀ d p, t.bv ∈ σ.readyQueues d p → d = x.tcbDomain ∧ p = x.tcbPriority := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x', hk', hd, -, -, hpr⟩ := hs.tcb t ht
  rw [hk] at hk'; cases hk'
  intro d p hm
  by_cases hd0 : d = 0
  · subst hd0
    obtain ⟨pw, hpw, rfl⟩ := Sched.prio_of_spec p
    rw [hs.rq pw hpw, Sched.mem_map_bv] at hm
    have e := hc.inQ pw hpw t hm
    refine ⟨hd.symm, ?_⟩
    rw [← e]; exact Sched.specPrio_eq hpr
  · rw [hs.rqDom d p hd0] at hm; simp at hm

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`suspend`'s scheduler tail at `J`** (module docstring). -/
theorem JAtZ.suspendScJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hfree : IpcFree x.tcbState)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    (do
      let s3 ← sched.dequeue st s t
      let s4 ← sched.release_remove st s3 t
      let s5 ← schedcontext.cancel_yield_to st s4 t
      let s6 ← sched.set_thread_state st s5 t sched.TS_INACTIVE
      ok (s6, a)) ⦃ r => r.2 = a ∧ ∀ Ac',
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' r.1 →
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 →
      ∃ σ', suspendSc t.bv σ = ({((), σ')}, False) ∧
        ∃ (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.1 a σ' ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q0, R0, hc0, hs0⟩ := hS.lists
  have hy0 : t ≠ 0#u64 := fun e => (hc0.tcbs t ht).ne0 (by rw [e]; rfl)
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (dequeue_refines s σ hS t ht) (dequeue_sfootI hS ht)) ?_
  rintro s3 ⟨⟨σ3, he3, -, -, -, hS3⟩, hw3⟩
  have hX3 := sc_step_lift hP0 hI (hw3.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he3) hS3
  have y3 : ∀ y ∈ Z.T, L.mem s3 (yieldA y) = L.mem s (yieldA y) := fun y hy => yield_sfootI hT hc0.node hw3 hy
  have e3 : σ3 = setQ σ x.tcbDomain x.tcbPriority
      (Fl4Spec.tcbSchedDequeue t.bv (σ.readyQueues x.tcbDomain x.tcbPriority)) := by
    have h3 := he3
    rw [tcbSchedAction_gen hk] at h3
    exact (Prod.mk.inj (Set.singleton_injective (congrArg Prod.fst h3))).2.symm
  -- the release-queue removal
  have hS3' := hX3.2.2.1
  refine WP.spec_bind (WP.spec_and (release_remove_refines s3 σ3 hS3' ht) (release_remove_sfootI hS3' ht)) ?_
  rintro s4 ⟨⟨σ4, he4, ⟨bb, hσ4⟩, -, hS4⟩, hw4⟩
  have hX4 := sc_step_lift hP0 hX3 (hw4.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbReleaseRemove _) he4) hS4
  have y4 : ∀ y ∈ Z.T, L.mem s4 (yieldA y) = L.mem s (yieldA y) := fun y hy =>
    (yield_sfootI hT (let ⟨_, _, hc, _⟩ := hS3'.lists; hc.node) hw4 hy).trans (y3 y hy)
  have hk4 : σ4.kheap = σ.kheap := by rw [hσ4, e3]; rfl
  have hk4t : σ4.kheap t.bv = some (.tcb x) := by rw [hk4]; exact hk
  have hY4 : YieldRel Z.T Z.C (L.mem s4) σ4 := J.yld.frame y4 (YKeep.of_kheap hk4)
  obtain ⟨xy, hky, eyt⟩ := hY4.tcb t ht
  rw [hk4t] at hky; cases hky
  -- the yield-to cut
  have hcan : schedcontext.cancel_yield_to st s4 t ⦃ s5 => ∃ σ5,
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) t.bv σ4 = ({((), σ5)}, False) ∧
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 σ5 ∧
      YieldRel Z.T Z.C (L.mem s5) σ5 ∧
      P1.WritesIn st s4 s5 (TFoot st Z.T Z.N Z.C Z.c s4 σ4) ∧
      σ5.kheap t.bv = some (.tcb { x with tcbYieldTo := none }) ∧
      (∀ p, p ≠ t.bv → σ5.kheap p = σ.kheap p ∨ ∃ z n, σ.kheap p = some (.schedContext z n) ∧
        σ5.kheap p = some (.schedContext { z with scYieldFrom := none } n)) ∧
      { σ5 with kheap := σ4.kheap } = σ4 ⦄ := by
    obtain ⟨Q4, R4, hc4, hs4⟩ := hS4.lists
    by_cases hp0 : L.mem s4 (yieldA t) = 0#u64
    · have hyt : x.tcbYieldTo = none := by rw [eyt, hp0, Notif.optRef_zero]
      have hsp : Fl4Spec.schedContextCancelYieldTo (Z := Unit) t.bv σ4 = ({((), σ4)}, False) := by
        unfold Fl4Spec.schedContextCancelYieldTo
        rw [nd_bind_one (getTcbObjRef_eq _ hk4t), hyt]; rfl
      have hx : { x with tcbYieldTo := none } = x := by rw [← hyt]
      unfold schedcontext.cancel_yield_to
      step with obj.Tcb.is_null.spec as ⟨b2, hb2⟩
      have hb2' : b2 = false := by rw [hb2]; exact decide_eq_false hy0
      rw [hb2']
      simp only [Bool.false_eq_true, ↓reduceIte]
      step with obj.Tcb.yield_to.spec as ⟨i2, hi2⟩
      subst hi2
      have : (L.mem s4 (yieldA t) != 0#u64) = false := by simp [hp0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      refine (WP.spec_ok _).mpr ⟨σ4, hsp, hX4, hY4, WritesIn.refl _ _, by rw [hx]; exact hk4t,
        fun p _ => Or.inl (by rw [hk4]), rfl⟩
    obtain ⟨p, hp⟩ : ∃ p, L.mem s4 (yieldA t) = p := ⟨_, rfl⟩
    rw [hp] at hp0 eyt
    obtain ⟨hpC, z, n, hkz, -⟩ := hY4.toSc t ht (by rw [hp]; exact hp0)
    rw [hp] at hpC hkz
    have hsw56 := sw_hdr hS4 hpC (K := 56#u64) (by simp) (by simp) (by decide)
    have hal56 : Aligned (scW p 56#u64) := by
      obtain ⟨x0, n0, -, hx0⟩ := hs4.scs p hpC; exact (hx0.hdr (K := 56#u64) (by simp) (by simp)).1
    have hcode : schedcontext.cancel_yield_to st s4 t ⦃ s5 =>
        s5 = L.wr (L.wr s4 (scYieldFromA p) 0#u64) (yieldA t) 0#u64 ⦄ := by
      unfold schedcontext.cancel_yield_to
      step with obj.Tcb.is_null.spec as ⟨b2, hb2⟩
      have hb2' : b2 = false := by rw [hb2]; exact decide_eq_false hy0
      rw [hb2']
      simp only [Bool.false_eq_true, ↓reduceIte]
      step with obj.Tcb.yield_to.spec as ⟨i2, hi2⟩
      rw [hp] at hi2
      rw [hi2]
      have hb' : (p != 0#u64) = true := by simp [hp0]
      simp only [hb', ↓reduceIte]
      exact WP.spec_bind (obj.Sc.set_yield_from.spec s4 _ 0#u64) fun s3 h3 => h3 ▸ obj.Tcb.set_yield_to.spec _ t 0#u64
    refine WP.spec_mono hcode ?_
    rintro s5 rfl
    obtain ⟨hS5a, hf3, hK3, hw3'⟩ := hS4.set_sc_yf hpC hkz 0#u64
    rw [Notif.optRef_zero] at hS5a hK3
    have hpy : p.bv ≠ t.bv := fun e => by rw [e, hk4t] at hkz; cases hkz
    have hkay : (updSc σ4 p.bv { z with scYieldFrom := none } n).kheap t.bv = some (.tcb x) := by
      simp [updK, Ne.symm hpy, hk4t]
    obtain ⟨hS5, hf4, hK4⟩ := hS5a.set_yt ht hkay 0#u64
    rw [Notif.optRef_zero] at hS5 hK4
    have hN5 := (hX4.1.toN.frame hS4.placed hf3 hK3).frame hS5a.placed hf4 hK4
    have hwy : WritesIn st s4 (L.wr (L.wr s4 (scYieldFromA p) 0#u64) (yieldA t) 0#u64)
        (TFoot st Z.T Z.N Z.C Z.c s4 σ4) :=
      ((writesIn_wr (st := st) (s := s4) (v := 0#u64)
          (show Aligned (scYieldFromA p) by rw [scYieldFromA_eq]; exact hal56)).trans
        (writesIn_wr (st := st) (s := L.wr s4 (scYieldFromA p) 0#u64) (v := 0#u64) (yieldA_aligned hT ht))).mono
        fun b hb => by
          rcases hb with rfl | rfl
          · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
          · exact Or.inr ⟨t, ht, rfl⟩
    have hsp := cancelYieldTo_some hk4t (by rw [eyt, Notif.optRef_ne hp0]) hkz hpy
    have hK : ScTKw (fun q => q = σ4.curThread) σ4 _ :=
      ScTKw.ofFalse (NKT.of_eq (nkt_schedContextCancelYieldTo t.bv) hsp)
    have hX5 := tk_liftCW hP0 hX4 (hwy.mono fun _ h => Or.inl h) hK hS5 hN5
    have hm4 : ∀ u ∈ Z.T, u ≠ t → L.mem (L.wr (L.wr s4 (scYieldFromA p) 0#u64) (yieldA t) 0#u64) (yieldA u) =
        L.mem s4 (yieldA u) := by
      intro u hu hne
      rw [L.mem_wr_ne (yieldA_aligned hT ht) (yieldA_aligned hT hu)
        (fun e => hne (yieldA_inj hT ht hu (UScalar.eq_of_val_eq e.symm)))]
      exact WritesIn.yield_keep hT hw3' u hu
    have hmy : L.mem (L.wr (L.wr s4 (scYieldFromA p) 0#u64) (yieldA t) 0#u64) (yieldA t) = 0#u64 :=
      L.mem_wr_same (yieldA_aligned hT ht)
    have hY5 := hY4.clear ht hp hp0 hk4t hkz hm4 hmy
    refine ⟨_, hsp, hX5, hY5, hwy, by simp [updK], fun q hq => ?_, rfl⟩
    by_cases hqp : q = p.bv
    · subst hqp
      exact Or.inr ⟨z, n, by rw [← hk4]; exact hkz, by simp [updK, hq]⟩
    · exact Or.inl (by simp [updK, hq, hqp, hk4])
  refine WP.spec_bind hcan ?_
  rintro s5 ⟨σ5, he5, hX5, hY5, hw5, hk5, hko5, hrec5⟩
  -- `Inactive`
  have hS5 := hX5.2.2.1
  obtain ⟨x5', hk5', hTR5⟩ := hX5.1.tcb t ht
  rw [hk5] at hk5'; cases hk5'
  have hcode5 := ipcFree_code hfree
  have hw5c : (L.mem s5 (tStA t)).val = tsCode x.tcbState := hTR5.st
  have hq5 := IpcRel.not_ep_queued hX5.1 (t := t) ⟨by rw [hw5c]; exact hcode5.1, by rw [hw5c]; exact hcode5.2.1⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hX5.1 hX5.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e _ _ hX5.1.toE hSR ht hk5 hq5
    hcode5.2.2 .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
    (set_thread_state_sfoot hS5 ht _)) (set_thread_state_yw hS5 ht _)) ?_
  rintro s6 ⟨⟨⟨hR6, hS6r⟩, hw6⟩, hy6⟩
  rw [WP.spec_ok]
  refine ⟨rfl, fun Ac' hblk hKd0 => ?_⟩
  have hDbg : L.mem s6 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hKd0.2 _ (Or.inr ⟨0#u64, J.kern.cs0, rfl⟩)
  have hX6 := IpcRel.ofSRN hR6 hS6r
  -- the spec's step
  have hsp : suspendSc t.bv σ = ({((), stsAct (updK σ5 t.bv
      (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive })) t.bv)}, False) := by
    unfold suspendSc
    rw [nd_bind_one he3, nd_bind_one he4, nd_bind_one he5, setThreadState_eq' hk5 .inactive]
  set σ6 := stsAct (updK σ5 t.bv (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive })) t.bv
    with hσ6
  -- the fields kept
  have f4 : ∀ {β : Type} (g : Fl4Spec.State Unit → β), (∀ τ : Fl4Spec.State Unit, g { τ with kheap := σ4.kheap } = g τ) →
      g σ4 = g σ → g σ5 = g σ := fun g hg h => by rw [← hg σ5, hrec5, h]
  have hr5 : σ5.releaseQueue = σ4.releaseQueue := by rw [← hrec5]
  have hF : SusF t.bv x σ σ6 := susF_of hk hk5 hko5
    (f4 (fun τ : Fl4Spec.State Unit => τ.curThread) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.curSc) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.consumedTime) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.curTime) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.idleThread) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.idleSc) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (hr5.trans (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.schedulerAction) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.machineState.underlyingMemory) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.cdt) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.isOriginalCap) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.domainList) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.domainStartIndex) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.archState) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.interruptStates) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
    (f4 (fun τ : Fl4Spec.State Unit => τ.interruptIrqNode) (fun _ => rfl) (by rw [hσ4, e3]; rfl))
  -- FL4's footprint
  have hz : ∀ τ : Fl4Spec.State Unit, τ.kheap = σ.kheap → SzKeepC Z.C σ τ :=
    fun τ h sc _ y n hy => ⟨y, by rw [← h]; exact hy⟩
  have hk3 : σ3.kheap = σ.kheap := by rw [e3]; rfl
  have hW3 : P1.WritesIn st s s3 (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    hw3.mono fun _ h => Or.inl (KFoot.of_sfoot (sfootI_sfoot h))
  have hW4 : P1.WritesIn st s s4 (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    WritesIn.tfoot_trans hW3 (hz _ hk3) (hw4.mono fun _ h => Or.inl (KFoot.of_sfoot (sfootI_sfoot h)))
  have hW5 : P1.WritesIn st s s5 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_trans hW4 (hz _ hk4) hw5
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot hW5 hw6
  -- the spec's frame
  have hK : ScTKw (fun p => p = t.bv) σ σ6 := hF.tkw hfree
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  have hInv : Sched.Inv σ6 := suspendSc_inv J.inv hk (rq_ownS hS ht hk) (by rw [hsp]; exact Set.mem_singleton _)
  have hNSC := hF.nsc J.nsc
  have hY6 : YieldRel Z.T Z.C (L.mem s6) σ6 := by
    have h1 := hY5.frame (m' := L.mem s6)
      (σ' := updK σ5 t.bv (.tcb { { x with tcbYieldTo := none } with tcbState := .inactive }))
      (fun y hy => hy6.mem_eq (yieldA_aligned hT hy) fun h => h ⟨y, hy, rfl⟩)
      (YK.YKS.updTcb (y := { { x with tcbYieldTo := none } with tcbState := .inactive }) hk5 rfl).ykeep
    exact h1.frame (m' := L.mem s6) (σ' := σ6) (fun _ _ => rfl) (YKeep.of_kheap (stsAct_kheap _ _))
  have hsok : SOK (false, true) σ σ6 := by
    refine Pres.of_eq ?_ hsp
    unfold suspendSc
    exact pres_bind (pres_tcbSchedAction _ _ _) fun _ => pres_bind (pres_tcbReleaseRemove _ _) fun _ =>
      pres_bind (pres_schedContextCancelYieldTo _) fun _ => pres_setThreadState _ _ _
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hX6.2.2.1, hX6.1.toN, hNSC, hInv⟩ hY6 (hW.mono fun _ h => Or.inl h)
      hsok rfl
  have hAI := hF.actIdle J.act hsa hid
  have hYD5 : ∀ r, YDeadKeep σ σ5 r := fun r => by
    refine ⟨fun x0 hx0 h0 y hy => ?_, fun x0 m hx0 h0 y m' hy => ?_⟩
    · by_cases e : r = t.bv
      · subst e; rw [hk5] at hy; cases hy; rfl
      · rcases hko5 r e with h | ⟨z, n, hz, h⟩
        · rw [h, hx0] at hy; cases hy; exact h0
        · rw [hz] at hx0; cases hx0
    · by_cases e : r = t.bv
      · subst e; rw [hk5] at hy; cases hy
      · rcases hko5 r e with h | ⟨z, n, hz, h⟩
        · rw [h, hx0] at hy; cases hy; exact h0
        · rw [h] at hy; cases hy; rfl
  have hYD6 : ∀ r, YDeadKeep σ σ6 r := fun r =>
    (YDeadKeep.upd (p := t.bv) (o := .tcb { { x with tcbYieldTo := none } with tcbState := .inactive }) (hYD5 r)
      (fun _ e => by cases e; rfl) (fun _ _ e => by cases e)).congr (by rw [hσ6, stsAct_kheap])
  have hdead : ∀ q ∈ D, DeadP (L := L) H s6 q := fun q hq =>
    J.deadP_sc_stepG hX' hW hK (fun p x' hp hk' h0 y hy => by
        subst hp; rw [hk] at hk'; cases hk'; rw [hF.hk'] at hy; cases hy
        show Fl4Spec.ThreadState.inactive = x.tcbState
        cases hx : x.tcbState <;> simp_all [tsCode])
      (hF.lk (W := fun _ => False)) hF.fk hAI.1 hY' (hYD6 q.bv) (fun h => h) (J.jcov.dead q hq)
  refine ⟨_, hsp, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hF.fk.2.1 hF.fk.2.2).2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.fk.2.1 hF.fk.2.2)) (J.sc_kern hW hK hF.fk hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hNSC hInv (J.cur.imp (fun e => hF.act.elim (fun e' => e'.trans e) id) hF.curInv)
    (hF.own J.own) (hF.off J.off) hAI (hF.bsa J.bsa) (hF.curRun J.curRun) hblk
    hKd0 (J.idleW_keep hX'.fin.1.1.1 hF.fk.2.1 hF.fk.2.2).1 J.zD⟩


set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` of a thread blocked on nothing at `J`**: the fault clear
(a register-frame step, `reg_frameF`, `QKY`). -/
theorem JAtZ.cancelFreeJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hfree : IpcFree x.tcbState) :
    ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧
      Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), updK σ t.bv (.tcb { x with tcbFault := none }))}, False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.1 r.2 (updK σ t.bv (.tcb { x with tcbFault := none })) ⦄ := by
  have hP0 := J.ip
  have hX := J.xtop.irelK J.ks J.buf
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  obtain ⟨x0, hk0, hx⟩ := hX.1.tcb t ht
  -- (the TCB is `x`)
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  have h4 : ∀ e d, x.tcbState ≠ .blockedOnSend e d := fun e d h => by
    have := hfree.1; rw [h] at this; simp [Fl4Spec.epBlocked] at this
  have h3 : ∀ e r d, x.tcbState ≠ .blockedOnReceive e r d := fun e r d h => by
    have := hfree.1; rw [h] at this; simp [Fl4Spec.epBlocked] at this
  have h6 : ∀ n, x.tcbState ≠ .blockedOnNotification n := fun n h => by
    have := hfree.2.1; rw [h] at this; simp [Fl4Spec.ntfnBlocked] at this
  have h5 : ∀ r, x.tcbState ≠ .blockedOnReply r := hfree.2.2
  have hR1 := fault_clear_ipc hP0 hX.1 ht hk
  have hS1 := fault_clear_top hX.2 ht hk
  have hfa := a_fault hta
  have g : ∀ w, Aligned w → w.val ≠ t.val + 3376 → L.mem (L.wr s (tFaultA t) 0#u64) w = L.mem s w :=
    fun w hw hne => rd_wr_ne hfa.1 hw (fun e => hne (by rw [← e, val_fault hta]))
  have hstw : (L.mem (L.wr s (tFaultA t) 0#u64) (P1.stA t)).val = tsCode x.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, g _ (a_st hta).1 (by rw [val_st hta]; omega)]; exact hx.st
  have hne : ∀ k : U64, k.val = tsCode x.tcbState → k ≠ sched.TS_BLOCKED_ON_SEND ∧ k ≠ sched.TS_BLOCKED_ON_RECV ∧
      k ≠ sched.TS_BLOCKED_ON_NTFN ∧ k ≠ sched.TS_BLOCKED_ON_REPLY := by
    intro k hk'
    have e3 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
    rw [tsVals.2.2.2.1, tsVals.2.2.1, tsVals.2.2.2.2, e3]
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;>
      cases hts : x.tcbState <;> simp_all [tsCode]
  have hcode : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ r.1 = L.wr s (tFaultA t) 0#u64 ⦄ := by
    unfold ipc.cancel_ipc faults.clear_fault
    step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1', hs1'⟩
    have e1 : s1' = L.wr s (tFaultA t) 0#u64 := by rw [hs1']; unfold fl4_abi.consts.fault.NullFault; rfl
    subst e1
    step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
    obtain ⟨n4, n3, n6, n5⟩ := hne w (by rw [hw]; exact hstw)
    simp only [n4, n3, n6, n5, ↓reduceIte, WP.spec_ok]
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl
  have hsp : Fl4Spec.cancelIpc (Z := Unit) t.bv σ =
      ({((), updK σ t.bv (.tcb { x with tcbFault := none }))}, False) := by
    unfold Fl4Spec.cancelIpc
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (threadSet_eq _ hk)]
    cases hts : x.tcbState <;> simp_all <;> rfl
  refine WP.spec_mono (WP.spec_and hcode (P1.ipc.cancel_ipc.blk s a t J.blk htH)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, h2⟩, hblk⟩
  simp only at h1 h2 hblk ⊢
  subst h1 h2
  have hwr : P1.WritesIn st s (L.wr s (tFaultA t) 0#u64) (· = tFaultA t) := writesIn_wr hfa.1
  have hfoot : P1.WritesIn st s (L.wr s (tFaultA t) 0#u64) (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) :=
    foot_field (K := 3376#u64) hTH htH (by simp) (by simp) (by simp) (by simp)
  have hA : QKY σ (updK σ t.bv (.tcb { x with tcbFault := none })) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => ?_⟩
    by_cases hp : p = t.bv
    · subst hp; exact Or.inr (Or.inl ⟨x, { x with tcbFault := none }, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, hp])
  obtain ⟨V, J1⟩ := J.reg_frameF ⟨hR1, hS1⟩ (hwr.mono fun b hb => Or.inr ⟨t, ht, by rw [hb, val_fault hta]⟩)
    hA (YK.YKS.updTcb (y := { x with tcbFault := none }) hk rfl).ykeep
    (J.inv.updSame (y := { x with tcbFault := none }) hk rfl rfl
      (Or.inr fun e d h => by have h1 := hfree.1; rw [h] at h1; simp [Fl4Spec.epBlocked] at h1)) hblk hfoot
  exact ⟨rfl, hsp, V, J1⟩

set_option maxHeartbeats 8000000 in
/-- **The restart PC of a running thread at `J`** (a register step,
`reg_frameF`). -/
theorem JAtZ.restartPcJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {i : U64} (hi : i = L.mem s (P1.stA t)) :
    (if i = sched.TS_RUNNING then do
        let ip ← obj.Tcb.reg st t s layout.reg.NEXT_IP
        obj.Tcb.set_reg st t s layout.reg.FAULT_IP ip
      else ok s) ⦃ s2 => ∃ σ2 x2,
        Fl4Spec.NonDet.when (x.tcbState = .running) (Fl4Spec.updateRestartPc (Z := Unit) t.bv) σ =
          ({((), σ2)}, False) ∧ σ2.kheap t.bv = some (.tcb x2) ∧ x2.tcbState = x.tcbState ∧
          σ2.curThread = σ.curThread ∧ σ2.schedulerAction = σ.schedulerAction ∧ σ2.idleThread = σ.idleThread ∧
          L.ksb s2 = L.ksb s ∧ P1.DbgKeep st (P1.Heap.tcbs H) Cs s s2 ∧
          ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s2 a σ2 ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  obtain ⟨x', hk', hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk'; cases hk'
  have hw : i.val = tsCode x.tcbState := by rw [hi]; exact hTR.st
  have hrun : i = sched.TS_RUNNING ↔ x.tcbState = .running := by
    constructor
    · intro h; rw [h] at hw; unfold sched.TS_RUNNING at hw
      generalize x.tcbState = ts at hw ⊢; cases ts <;> simp_all [tsCode]
    · intro h; rw [h] at hw; apply UScalar.eq_of_val_eq; unfold sched.TS_RUNNING; simp [tsCode] at hw; simp [hw]
  by_cases hr : x.tcbState = .running
  · rw [if_pos (hrun.2 hr)]
    step with Endp.obj.Tcb.reg.spec as ⟨ip, hip⟩
    refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec s t _ ip) ?_
    rintro s2 rfl
    have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
    have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
    have hipv : ip.bv = x.tcbArch.tcbContext.userRegs .nextIP := by rw [hip, hNx]; exact hTR.regs .nextIP
    rw [hF]
    have h17 : (regIdx .faultIP).val = 17 := by rw [← hF]; unfold layout.reg.FAULT_IP; rfl
    have hra : (regA t (regIdx .faultIP)).val = t.val + 392 := by
      rw [regA_val hta (regIdx_lt _), h17]
    have hreq : regA t (regIdx .faultIP) = core.num.U64.wrapping_add t 392#u64 :=
      UScalar.eq_of_val_eq (by rw [hra, tfield_val hta (by simp)]; simp)
    have hX2 := reg_wr_irel hP0 hI ht hk .faultIP (by decide) ip
    have hwr : P1.WritesIn st s (L.wr s (regA t (regIdx .faultIP)) ip) (· = regA t (regIdx .faultIP)) :=
      writesIn_wr (a_reg hta .faultIP).1
    have hblk := (blk_rf J.blk (hwr.mono fun b hb => Or.inl ⟨t, htH, 392#u64, by simp, by simp,
      by rw [hb, hreq]⟩)).1
    have hfoot : P1.WritesIn st s (L.wr s (regA t (regIdx .faultIP)) ip) (P1.KW st (P1.Heap.tcbs H) Cs
        (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) := by
      rw [hreq]; exact foot_field (K := 392#u64) hTH htH (by simp) (by simp) (by simp) (by simp)
    have hA : QKY σ (updK σ t.bv (.tcb (setReg x .faultIP ip.bv))) := by
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => ?_⟩
      by_cases hp : p = t.bv
      · subst hp; exact Or.inr (Or.inl ⟨x, setReg x .faultIP ip.bv, hk, by simp [updK], rfl⟩)
      · exact Or.inl (by simp [updK, hp])
    obtain ⟨V, J2⟩ := J.reg_frameF hX2 (hwr.mono fun b hb => Or.inl (Or.inl ⟨t, ht, by rw [hb, hra]; omega,
      by rw [hb, hra]; omega⟩)) hA (YK.YKS.updTcb (y := setReg x .faultIP ip.bv) hk rfl).ykeep
      (J.inv.updSame (y := setReg x .faultIP ip.bv) hk rfl rfl (Or.inl rfl)) hblk hfoot
    refine ⟨updK σ t.bv (.tcb (setReg x .faultIP ip.bv)), setReg x .faultIP ip.bv, ?_, by simp [updK], rfl, rfl, rfl, rfl, L.ksb_wr _ _ _,
      J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _), V, J2⟩
    unfold Fl4Spec.NonDet.when
    rw [if_pos hr, updateRestartPc_eq hk, hipv]
  · rw [if_neg (fun h => hr (hrun.1 h)), WP.spec_ok]
    refine ⟨σ, x, ?_, hk, rfl, rfl, rfl, rfl, rfl, P1.DbgKeep.refl s, Z.vs, J⟩
    unfold Fl4Spec.NonDet.when
    rw [if_neg hr]; rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[J-step] `cancel_ipc` at `J` of a thread whose state satisfies `P`**,
the spec's outcome and `JAtZ` after, at every `JAtZ` state of the typed heap
`th`, the dead set kept (a blocked thread is not dead, and `cancel_ipc`
revives nothing). -/
def JCancelAt (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (P : Fl4Spec.ThreadState → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ t ∈ Z.T, ∀ x, σ.kheap t.bv = some (.tcb x) → P x.tcbState →
    ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`suspend` at `J`** (module docstring), the dead set kept (the cancel
steps' `JCancelAt`, the restart PC and the scheduler tail keep it). -/
theorem JAtZ.suspendJD
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    sched.suspend st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.suspend (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨x, hk, -⟩ := hI.1.tcb t ht
  obtain ⟨hna, -⟩ := J.words_of_spec ht hsa hid
  -- the debug word through `cancel_ipc` (P1's footprint)
  obtain ⟨⟨Q0, R0, h0⟩, -, ⟨hO, hR, -⟩, -, hSg⟩ := J.blk
  have hreply : L.mem s (P1.stA t) = sched.TS_BLOCKED_ON_REPLY → P1.ReplyT st (P1.Heap.replies H)
      (P1.Heap.scs H) s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t htH hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  have hkwc : ipc.cancel_ipc st arI s a t ⦃ r => L.ksb r.1 = L.ksb s ∧
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 ⦄ := by
    refine WP.spec_mono (P1.ipc.cancel_ipc.kw s a t h0 htH hO hSg.sub hreply
      (fun h1 h2 => (hR.recv t htH h1 h2).1)) fun r hr => ?_
    obtain ⟨s1, a1⟩ := r
    try simp only [WP.uncurry'_pair] at hr
    exact ⟨hr.1, J.kw_dbgKeep hr⟩
  -- the cancel step
  have hcan : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ1,
      Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) ∧ ∃ x1, σ1.kheap t.bv = some (.tcb x1) ∧
      IpcFree x1.tcbState ∧ (∀ u, σ1.schedulerAction = .switchThread u → u ≠ t.bv) ∧ t.bv ≠ σ1.idleThread ∧
      ∃ (V : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac1 Lst1 D r.1 r.2 σ1 ⦄ := by
    by_cases hfree : IpcFree x.tcbState
    · refine WP.spec_mono (J.cancelFreeJ ht hk hfree) ?_
      rintro r ⟨h1, h2, V, J1⟩
      exact ⟨h1, _, h2, { x with tcbFault := none }, by simp [updK], hfree, hsa, hid, V, Ac, Lst, J1⟩
    have hcases : (∃ e d, x.tcbState = .blockedOnSend e d) ∨ (∃ e r d, x.tcbState = .blockedOnReceive e r d) ∨
        (∃ n, x.tcbState = .blockedOnNotification n) ∨ (∃ r, x.tcbState = .blockedOnReply r) := by
      revert hfree
      cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked]
    have hP : ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ =
        ({((), σ')}, False) ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
      rcases hcases with h | h | h | h
      · exact hSd Z H Cs Ac Lst D s a σ rfl J t ht x hk h
      · exact hRv Z H Cs Ac Lst D s a σ rfl J t ht x hk h
      · exact hNt Z H Cs Ac Lst D s a σ rfl J t ht x hk h
      · exact hRp Z H Cs Ac Lst D s a σ rfl J t ht x hk h
    refine WP.spec_mono (WP.spec_and hP (cancel_ipc_irelP (ar := arI) hP0 (removeTcbHypP_ok hP0) s a σ hI ht hk
      J.sv J.obj J.inv (fun hfr => removeTcbOK_fault hP0 hI ht hk hfr J.removeTcbOK))) ?_
    rintro r ⟨⟨h1, σ1, h2, V, Ac1, Lst1, J1⟩, -, σ1', x1, h2', -, hk1, hs1⟩
    have e1 : σ1' = σ1 := by
      rw [h2] at h2'; exact ((Prod.mk.inj (Set.singleton_injective (congrArg Prod.fst h2'))).2).symm
    subst e1
    have hin : x1.tcbState = .inactive := by
      rw [hs1]; revert hfree; cases x.tcbState <;> simp [IpcFree, Fl4Spec.epBlocked, Fl4Spec.ntfnBlocked, cancelSt]
    have hid1 : t.bv ≠ σ1'.idleThread := fun e => by
      obtain ⟨xi, hki, -, hti, -⟩ := J1.act.2
      rw [← e, hk1] at hki; cases hki; rw [hin] at hti; cases hti
    refine ⟨h1, σ1', h2', x1, hk1, by rw [hin]; exact ⟨rfl, rfl, fun _ e => by cases e⟩, fun u hu => ?_, hid1,
      V, Ac1, Lst1, J1⟩
    rintro rfl
    obtain ⟨y, -, -, -, hky, -, hrun, -⟩ := schedulable_inv (J1.act.1 _ hu)
    rw [hk1] at hky; cases hky; rw [hin] at hrun; cases hrun
  -- the restart PC and the scheduler tail
  have hmain : sched.suspend st arI s a t ⦃ r => ∀ Ac', P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' r.1 →
      P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.1 →
      r.2 = a ∧ ∃ σ', Fl4Spec.suspend (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
    unfold sched.suspend
    refine WP.spec_bind (WP.spec_and hcan hkwc) ?_
    rintro ⟨s1, a1⟩ ⟨⟨h1, σ1, hc1, x1, hk1, hf1, hsa1, hid1, V1, Ac1, Lst1, J1⟩, hks1, hd1⟩
    simp only at h1 hks1 hd1
    subst h1
    step with P1.obj.Tcb.state.spec as ⟨i, hi⟩
    refine WP.spec_bind (J1.restartPcJ ht hk1 hi) ?_
    rintro s2 ⟨σ2, x2, hw2, hk2, hs2, hct2, hact2, hidle2, hks2, hd2, V2, J2⟩
    refine WP.spec_mono (J2.suspendScJ ht hk2 (by rw [hs2]; exact hf1) (by rw [hact2]; exact hsa1)
      (by rw [hidle2]; exact hid1)) ?_
    rintro r ⟨hr2, hr⟩ Ac' hblk hd6
    have hd12 : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s2 := hd1.trans hd2
    obtain ⟨σ6, he6, Lst6, J6⟩ := hr Ac' hblk (dbgKeep_cancel hd12 hd6)
    refine ⟨hr2, σ6, ?_, V2, Ac', Lst6, by rw [hr2]; exact J6⟩
    rw [Sched.suspend_split, nd_bind_one hc1, nd_bind_one (getThreadState_eq hk1), nd_bind_one hw2]
    exact he6
  refine WP.spec_mono (WP.spec_and (P1.sched.suspend.blk s a t J.blk htH hna) hmain) ?_
  rintro ⟨s6, a6⟩ ⟨hP1, hM⟩
  try simp only [WP.uncurry'_pair] at hP1
  exact hM Ac hP1.1 (J.kw_dbgKeep hP1.2)

/-- **`suspend` at `J`** (`JAtZ.suspendJD`, the dead set existential). -/
theorem JAtZ.suspendJ
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    sched.suspend st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.suspend (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  WP.spec_mono (J.suspendJD hSd hNt hRv hRp ht hsa hid) fun _ ⟨h1, σ', h2, V, Ac', Lst', J'⟩ =>
    ⟨h1, σ', h2, V, Ac', Lst', D, J'⟩

end

end

end Fl4Proofs.P3
