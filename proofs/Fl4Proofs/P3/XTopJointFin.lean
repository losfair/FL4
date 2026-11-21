/-
P3 (DESIGN.md §9), IPC: **`JAtZ` across a final notification cap's
finalisation** (toward `JStepHyps.del`): FL4's `maybe_unbind_ntfn`,
`unbind_maybe_notification`, `cancel_all_signals` against the spec's
`finalise_cap` of the notification cap, from `JAtZ` before to `JAtZ` after
at the sets `Z.mv Z.G V'` (the slots kept, the VSpace sets fresh).

* `JAtZ.ntfn_link`: a notification's SC is bound back to it (P1's
  `ObjsOK.nsc` through the relations; `maybe_unbind_irel`'s premise).
* `JAtZ.finNtfn_p3`: the three steps on `IRel` (IpcFinNtfn), the slots kept
  (`IFrame`), the footprint `FinStep`.
* `JAtZ.finNtfnJ`: `JAtZ` after: `XTopAt` (`XTopAt.irel_same`), the kinds
  kept (`KBack`, from the spec frame `NFr`), `JCs` (`JCs.same`), and `JRest`:
  the FL4 frame words from `FinW` (`JAtZ.finW_keeps`, XTopJointFinW), the
  scheduler fields from `finNtfn_spec` (IpcFinNtfnInv), the dead dead
  (`deadP_keep`), the untyped caps' facts (`finW_utc`), core 0's debug word
  (P1's `KW`, `kw_dbg`), P1's `BlkOK` (`fin_cap_ntfn.slots`).
-/
import Fl4Proofs.P3.XTopJointFinW
import Fl4Proofs.P3.IpcFinNtfnInv
import Fl4Proofs.P3.BufFrN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

variable {q : Bool} {r : ObjRef} {σ σ' : State Unit}

theorem Sched.NFr.ntfnF (h : NFr q r σ σ') {p : ObjRef} {x : Notification} (hp : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ (p ≠ r → y = x) ∧
      ((∀ l, x.ntfnObj ≠ .waitingNtfn l) → NObj x.ntfnObj y.ntfnObj) ∧
      (y.ntfnBoundTcb = x.ntfnBoundTcb ∨ y.ntfnBoundTcb = none) ∧ (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) := by
  rcases h.kh p with e | ⟨o, o', h1, h2, hc⟩
  · exact ⟨x, by rw [e, hp], fun _ => rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · rw [hp] at h1; cases h1
    rcases hc with ⟨_, _, _, _, e1, -⟩ | ⟨_, _, _, _, e1, -⟩ | ⟨x', y, e1, rfl, hpr, -, -, hs, hw, hb⟩ <;> cases e1
    exact ⟨y, h2, fun hne => absurd hpr hne, hw, hb, hs⟩

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`): a thread's
state changes only from blocked on the notification to running/restart. -/
theorem Sched.NFr.khrb (h : NFr q r σ σ') : KhRB σ σ' :=
  KhRB.of_kh h.kh fun p o o' hc => by
    rcases hc with ⟨x, st, bn, ar, rfl, rfl, ht, -⟩ | ⟨y, n, rf, nt, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩
    · refine ObjRB.tcb ?_
      rcases ht with ⟨e, -⟩ | ⟨-, -, e⟩
      · exact Or.inl e
      · right; rcases e with rfl | rfl <;> rfl
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)
    · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)

/-- `KBack` (the kinds back) across the frame. -/
theorem Sched.NFr.kback (h : NFr q r σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨ko, ko'', h1, h2, hc⟩
  · exact ⟨ko', by rw [← e, ho], id, id, id, id, id, id⟩
  · rw [ho] at h2; cases h2
    rcases hc with ⟨x, st, bn, ar, rfl, rfl, -⟩ | ⟨y, n, rf, nt, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, -⟩ <;>
      exact ⟨_, h1, by simp⟩

theorem Sched.NFr.ksz (h : NFr q r σ σ') : KSz σ σ' := fun o ko' ho => by
  obtain ⟨ko, h1, e⟩ := (h.kind o).2 ko' ho
  exact ⟨ko, h1, e.symm⟩

theorem Sched.NFr.ksub (h : NFr q r σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun rr cs hc hw => ⟨cs, ?_, hw⟩, fun t ht => ?_, fun hn => ?_⟩
  · exact h.othB hc (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
  · obtain ⟨x, -, -, -, hx, -⟩ := h.tcbB ht; exact ⟨x, hx⟩
  · rcases h.kh o with e | ⟨ko, ko', h1, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at h1; cases h1

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **A notification's SC is bound back to it** (P1's `ObjsOK.nsc` through
the notification and SC relations). -/
theorem JAtZ.ntfn_link {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) :
    ∀ xn q, σ.kheap n.bv = some (.notification xn) → xn.ntfnSc = some q →
      ∃ y m, σ.kheap q = some (.schedContext y m) ∧ y.scNtfn = some n.bv := by
  intro xn q hk hq
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hx := J.xtop.ipc.toN.at_ntfn hn hk
  obtain ⟨sc, hscC, hscv⟩ := J.nsc n hn xn q hk hq
  rw [hx.sc] at hq
  have h0 : L.mem s (nScA n) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hq; cases hq
  have hqv : q = (L.mem s (nScA n)).bv := by rw [Sched.optRef_ne h0] at hq; exact (Option.some.inj hq).symm
  have hsc : sc = L.mem s (nScA n) := P1.eq_of_bv (hscv.trans hqv)
  obtain ⟨-, hback⟩ := J.blk.2.2.1.2.2.nsc n (J.zH.2.2.2 n hn) h0
  obtain ⟨x, m, hkx, hR⟩ := hs.scs sc hscC
  refine ⟨x, m, by rw [← hscv]; exact hkx, ?_⟩
  rw [hR.ntfn, scW_ntfn, hsc]
  have hback' : L.mem s (scNtfnA (L.mem s (nScA n))) = n := hback
  have hn0 : n ≠ 0#u64 := fun e => by have := J.zH.2.2.2 n hn; rw [e, J.kern.h0] at this; cases this
  rw [hback', Sched.optRef_ne hn0]

set_option maxHeartbeats 4000000 in
/-- **A final notification cap's finalisation on `IRel`** (the three steps
of IpcFinNtfn, from `JAtZ`): the spec's three steps, `IRel` after, the slots
kept, the footprint. -/
theorem JAtZ.finNtfn_p3 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p b : U64} {w r : Bool} (hp : p ∈ Z.N) :
    objects.finalise_cap st arI s a (.Notification p b w r) true false ⦃ res =>
      res.1 = (capability.Cap.Null, capability.Cap.Null) ∧ res.2.2 = a ∧ ∃ σ1 σ2 σ3,
        ((), σ1) ∈ (Fl4Spec.schedContextMaybeUnbindNtfn (Z := Unit) p.bv σ).1 ∧
        ((), σ2) ∈ (Fl4Spec.unbindMaybeNotification (Z := Unit) p.bv σ1).1 ∧
        ((), σ3) ∈ (Fl4Spec.cancelAllSignals (Z := Unit) p.bv σ2).1 ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c res.2.1 σ3 ∧
        IFrame (L := L) Z.th s res.2.1 ∧ FinStep (st := st) Z.T Z.N Z.C Z.c s σ res.2.1 σ3 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xn, hkn, -⟩ := J.xtop.ipc.toN.ntfn p hp
  have hpre := ntfnPre_of_valid J.inv J.inv.actReady J.sv ⟨xn, hkn⟩
  rw [finalise_cap_ntfn arI s a p b w r true false]
  unfold objects.finalise_cap_object
  simp only [↓reduceIte]
  refine WP.spec_bind (maybe_unbind_irel J.ip hI hp J.nsc (J.ntfn_link hp)) ?_
  rintro s1 ⟨σ1, he1, hI1, hk1, hf1⟩
  refine WP.spec_bind (unbind_maybe_irel J.ip hI1 hp) ?_
  rintro s2 ⟨σ2, he2, hI2, hk2, hf2⟩
  refine WP.spec_bind (cancel_all_signals_irel J.ip s2 σ2 hI2 hp (ntfnQPre_of_pre hpre he1 he2)) ?_
  rintro s3 ⟨σ3, hm3, hI3, hk3, hf3⟩
  rw [WP.spec_ok]
  exact ⟨rfl, rfl, σ1, σ2, σ3, by rw [he1]; exact Set.mem_singleton _, by rw [he2]; exact Set.mem_singleton _, hm3,
    hI3, (hk1.trans hk2).trans hk3, (hf1.trans hf2).trans hf3⟩


set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a step with the spec frame `NFr`** and the
footprint `FinW` (`deadP_keep`'s facts: a dead TCB's state and null bound
notification kept, a dead notification not waiting and unbound). -/
theorem JAtZ.deadP_nfr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {qq : Bool} {r : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : Sched.NFr qq r σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_)
    (fun x hx => F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e))
    (fun x hx => ?_)
    (fun x hx => ⟨x, F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e), rfl⟩)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.finW_scOut hw hz hqC hK8 hK)
    F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state and (null) bound notification kept
    obtain ⟨t, ht, e⟩ := J.obj.tcb q.bv x hx
    have htq : t = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t ht)
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t ht
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t = P1.boundA t from rfl, d3, optRef_zero]
    obtain ⟨st', bn, ar, hk3, hs, hbb⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, Or.inl rfl⟩
    · show st' = x.tcbState
      rcases hs with ⟨e, -⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e] at h0; simp [tsCode] at h0
    · show bn = x.tcbBoundNotification
      rcases hbb with e | e
      · exact e
      · rw [e, hbn]
  · -- a dead notification: not waiting, unbound
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, d2, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, -, hobj, hbd, hsc'⟩ := F.ntfnF hx
    have hbn : x.ntfnBoundTcb = none := by
      rw [hR.bound, show nBoundA n' = P1.ntfnBtA n' from rfl, d2, optRef_zero]
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, (hobj hnw).imp id And.right, ?_, hsc'⟩
    rcases hbd with e | e
    · exact e
    · rw [e, hbn]
  · -- an SC: its thread kept, its notification kept or cut
    obtain ⟨rf, nt, hk3, -, hn⟩ := F.scF hx
    exact ⟨_, hk3, Or.inl rfl, hn⟩

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a final notification cap's finalisation** (module
docstring): at `Z.mv Z.G V'`, the dead set and P1's sets kept. -/
theorem JAtZ.finNtfnJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p b : U64} {w r : Bool} (hp : p ∈ Z.N) :
    objects.finalise_cap st arI s a (.Notification p b w r) true false ⦃ res =>
      res.1 = (capability.Cap.Null, capability.Cap.Null) ∧ res.2.2 = a ∧ ∃ σ' V',
        ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Notification p b w r)) true σ).1 ∧
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D res.2.1 res.2.2 σ' ∧ KBack σ σ' ∧ IpcFrKeep σ σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.2.1) ∧ L.ksb res.2.1 = L.ksb s ⦄ := by
  have hpH : H p = some .ntfn := J.zH.2.2.2 p hp
  refine WP.spec_mono (WP.spec_and (J.finNtfn_p3 hp)
    (P1.fin_cap_ntfn.slots (ar := arI) s a p b w r true false J.blk hpH hpH)) ?_
  rintro ⟨⟨rem, cl⟩, s3, a3⟩ ⟨⟨e1, e2, σ1, σ2, σ3, h1, h2, h3, hI3, hF, hFS⟩, -, hblk, hfoot, -⟩
  simp only at e1 e2 hI3 hF hFS hblk hfoot ⊢
  -- the spec
  obtain ⟨n0, hkn, hx0⟩ := J.xtop.ipc.toN.ntfn p hp
  have hsc : ∀ c, n0.ntfnSc = some c → ∃ y k, σ.kheap c = some (.schedContext y k) :=
    fun c hc => J.inv.ntfnSc p.bv n0 c hkn hc
  have hb : ∀ t, n0.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x) := by
    intro t ht
    rw [hx0.bound] at ht
    have h0 : L.mem s (nBoundA p) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at ht; cases ht
    obtain ⟨x, hk, -⟩ := J.xtop.ipc.tcb _ (hx0.bound_mem h0)
    rw [Sched.optRef_ne h0] at ht
    rw [← Option.some.inj ht]
    exact ⟨x, hk⟩
  obtain ⟨I3, B3, F, hact⟩ := finNtfn_spec J.inv J.bsa J.sv hkn hsc hb h1 h2 h3
  have hmem : ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ3) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Notification p b w r)) true σ).1 := by
    show _ ∈ (Fl4Spec.NonDet.liftM (fun _ => (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) (Fl4Spec.NonDet.when true
      (do
        Fl4Spec.schedContextMaybeUnbindNtfn p.bv
        Fl4Spec.unbindMaybeNotification p.bv
        Fl4Spec.cancelAllSignals p.bv)) σ).1
    unfold Fl4Spec.NonDet.liftM Fl4Spec.NonDet.when
    simp only [↓reduceIte]
    refine mem_bind_nd (x := ((), σ3)) ?_ (Set.mem_singleton _)
    refine mem_bind_nd (x := ((), σ1)) h1 ?_
    exact mem_bind_nd (x := ((), σ2)) h2 h3
  have hck := finNtfn_nkc p.bv b.bv _ true σ _ hmem
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 (a' := a3) (by rw [e2]; exact hAR) hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s3 = L.ksb s := hF.2
  have hw := hFS.1
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hI3.2.2.1
  -- the scheduler fields
  have hAI3 : ActIdle σ3 := by
    rcases hact with e | Fq
    · exact ⟨fun t ht => (by rw [e] at ht; cases ht), F.idleOK J.act.2⟩
    · exact Fq.actIdle J.act
  have hcur3 : σ3.schedulerAction = .chooseNewThread ∨ CurInv σ3 := by
    rcases hact with e | Fq
    · exact Or.inl e
    · rcases J.cur with e | hC
      · exact Or.inl (by rw [(Fq.act rfl).1, e])
      · exact Or.inr (Fq.curInv hC)
  have hrun3 : CurRunM σ3 := by
    rcases hact with e | Fq
    · exact Or.inl (act_cn_nr e)
    · rcases J.curRun with e | hR
      · exact Or.inl (by rw [(Fq.act rfl).1]; exact e)
      · exact Or.inr (Fq.curRunW hR)
  -- the dead stay dead
  have hdead : ∀ q ∈ D, DeadP (L := L) H s3 q := J.deadP_nfr F hS3 hI3.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s3 σ3 := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.finW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s3 σ3 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.finW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s3 σ3 := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨e1, e2, σ3, Z.vs, hmem, J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD, F.kback, F.ipcFr, hF.1, hks⟩

end

end

end Fl4Proofs.P3
