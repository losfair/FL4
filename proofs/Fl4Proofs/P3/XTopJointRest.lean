/-
P3 (DESIGN.md §9), CSpace: **the per-kind `JRest` discharge of `JAtZ`'s step
closure** (`JStepHyps`, XTopJointStep), in the SC family's pattern
(`ScStepRest`, ScJointRest).

* The restart (`jowes_restart`): FL4 writes the caller's state word
  (`SFoot`), the spec only the caller's TCB (`ScTKw`, `tk_setThreadState`).
  Discharged: the call stacks, yield, MCP and reply placement (`ScAll.of_k`),
  the buffer words, slots apart, `JPlaced`, the kernel words, the untyped
  caps' facts, the dead set (ScJointRest's `sc_*` frames), `NSC`, `Inv`
  (`Inv.restart`), the current thread's invariants (`CurInv.restart`,
  `CurOwn`), `OffOK` (`OffOK.restart`), `ActIdle` (`ActIdle.updState`),
  `BlockedScActive` (`bk_restart`), the sorted IPC queues (`IpcSorted.tkw`), `CurRun`.
  The dead stay dead (`JAtZ.deadP_sc_step`: `ScTKw`, `LK ∅` by
  `lkm_setThreadState`); the node-0 `DEBUG_TCBS` word kept (`set_thread_state_frame`);
  P1's `BlkOK` after (`set_thread_state.restart_ok`).
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScJointStep
import Fl4Proofs.P3.SpecKeepC
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.DeadKeep
import Fl4Proofs.P3.SlotOrig
import Fl4Proofs.P3.SlotCdt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

theorem nsc_updTcb {N C : Set U64} {σ : State Unit} (h : NSC N C σ) (p : ObjRef) (y : Tcb) :
    NSC N C (stsAct (updK σ p (.tcb y)) p) := by
  intro n hn x q hx hq
  rw [stsAct_kheap, updK_kheap] at hx
  by_cases e : n.bv = p
  · rw [e, Function.update_self] at hx; cases hx
  · rw [Function.update_of_ne e] at hx; exact h n hn x q hx hq

theorem scLink_updTcb {σ : State Unit} (h : ScLinkHyp σ) {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (ts : ThreadState) : ScLinkHyp (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  have ek : ∀ q, (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap q =
      Function.update σ.kheap p (some (.tcb { x with tcbState := ts })) q := fun q => by
    rw [stsAct_kheap, updK_kheap]
  have back : ∀ q o, (o.isSome → ∀ y, o ≠ some (.tcb y)) → (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap q = o →
      σ.kheap q = o := by
    intro q o ho h1
    rw [ek] at h1
    by_cases e : q = p
    · subst e; rw [Function.update_self] at h1; subst h1; exact absurd rfl (ho rfl _)
    · rwa [Function.update_of_ne e] at h1
  refine ⟨fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun t z n ht hn => ?_, fun sc y k hy hs => ?_⟩
  · obtain ⟨z, hz⟩ := h.scTcb sc y k f (back _ _ (fun _ _ e => by cases e) hy) hf
    rw [ek]
    by_cases e : f = p
    · subst e; exact ⟨_, Function.update_self ..⟩
    · rw [Function.update_of_ne e]; exact ⟨z, hz⟩
  · obtain ⟨xn, hxn⟩ := h.scNtfn sc y k n (back _ _ (fun _ _ e => by cases e) hy) hn
    refine ⟨xn, ?_⟩
    rw [ek]
    by_cases e : n = p
    · subst e; rw [hk] at hxn; cases hxn
    · rw [Function.update_of_ne e]; exact hxn
  · rw [ek] at ht
    have hz : ∃ z0, σ.kheap t = some (.tcb z0) ∧ z0.tcbBoundNotification = z.tcbBoundNotification := by
      by_cases e : t = p
      · subst e; rw [Function.update_self] at ht; cases ht; exact ⟨x, hk, rfl⟩
      · rw [Function.update_of_ne e] at ht; exact ⟨z, ht, rfl⟩
    obtain ⟨z0, hz0, ez⟩ := hz
    obtain ⟨xn, hxn⟩ := h.tcbNtfn t z0 n hz0 (ez ▸ hn)
    refine ⟨xn, ?_⟩
    rw [ek]
    by_cases e : n = p
    · subst e; rw [hk] at hxn; cases hxn
    · rw [Function.update_of_ne e]; exact hxn
  · exact h.scSpor sc y k (back _ _ (fun _ _ e => by cases e) hy) hs

theorem curOwn_updTcb {T : Set U64} {σ : State Unit} (h : CurOwn T σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (ts : ThreadState) :
    CurOwn T (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  obtain ⟨e1, e2, e3, e4⟩ := stsAct_fields (updK σ p (.tcb { x with tcbState := ts })) p
  have ek : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap =
      Function.update σ.kheap p (some (.tcb { x with tcbState := ts })) := by rw [e1]; rfl
  have ecs : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).curSc = σ.curSc := by rw [e3]; rfl
  have erq : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).releaseQueue = σ.releaseQueue := by rw [e4]; rfl
  have hc : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).consumedTime = σ.consumedTime := by
    unfold stsAct; split_ifs <;> rfl
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := h
  refine ⟨u, hu, ?_⟩
  by_cases e : u.bv = p
  · rw [e, hk] at hkt; cases hkt
    refine ⟨{ x with tcbState := ts }, by rw [ek, e, Function.update_self], by rw [ecs]; exact hxs, fun y n hy => ?_,
      by rw [hc, erq]; exact hnr⟩
    rw [ek, ecs] at hy
    by_cases e' : σ.curSc = p
    · rw [e', Function.update_self] at hy; cases hy
    · rw [Function.update_of_ne e'] at hy; exact hown y n hy
  · refine ⟨xt, by rw [ek, Function.update_of_ne e]; exact hkt, by rw [ecs]; exact hxs, fun y n hy => ?_,
      by rw [hc, erq]; exact hnr⟩
    rw [ek, ecs] at hy
    by_cases e' : σ.curSc = p
    · rw [e', Function.update_self] at hy; cases hy
    · rw [Function.update_of_ne e'] at hy; exact hown y n hy

/-- `curOwn_updTcb` for the weak form (`CurOwnW`: an unowned current SC
stays unowned, a TCB written over no SC). -/
theorem curOwnW_updTcb {T C : Set U64} {σ : State Unit} (h : CurOwnW T C σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (ts : ThreadState) :
    CurOwnW T C (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  obtain ⟨e1, -, e3, -⟩ := stsAct_fields (updK σ p (.tcb { x with tcbState := ts })) p
  have ek : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).kheap =
      Function.update σ.kheap p (some (.tcb { x with tcbState := ts })) := by rw [e1]; rfl
  have ecs : (stsAct (updK σ p (.tcb { x with tcbState := ts })) p).curSc = σ.curSc := by rw [e3]; rfl
  refine h.imp (fun o => curOwn_updTcb o hk ts) ecs fun y n hy => Or.inr ⟨y, ?_, rfl⟩
  rw [ek] at hy
  by_cases e' : σ.curSc = p
  · rw [e', Function.update_self] at hy; cases hy
  · rw [Function.update_of_ne e'] at hy; exact hy

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **`JStepHyps.restart` at a fixed dead set** (module docstring): with no
premise, the dead set kept (every dead object stays dead); P1's `BlkOK`
after by `set_thread_state.restart_ok` (the current thread runnable, so
neither blocked nor waiting for a reply), the node-0 `DEBUG_TCBS` word kept
(`set_thread_state` writes the TCB's state word and the scheduler-action
word only, `JKern.dwNe`). -/
theorem jowes_restartD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (s1 : S) (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x))
    (htcb : Z.th ct = some .tcb) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hX1 : XTopAt (L := L) AR Z s1 a (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)) :
    ∃ Lst' : U64 → List U64, JRest (L := L) arI Z H Cs Ac Lst' D s1
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hT : ct ∈ Z.T := J.thT ct htcb
  have he1 : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := setThreadState_eq' hk _
  have hm1 : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
    rw [he1]; exact Set.mem_singleton _
  have hK : ScTKw (fun p => p = ct.bv) σ σ1 :=
    tk_setThreadState hk (ipcFree_of_runnable hrun) ipcFree_restart _ hm1
  have hwS : P1.WritesIn st s s1 (SFoot st Z.T Z.c s) := by
    have h := set_thread_state_sfoot (L := L) hS hT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  have hwK : P1.WritesIn st s s1 (KFoot st Z.T Z.N Z.C Z.c s σ) := hwS.mono fun b hb => KFoot.of_sfoot hb
  have hwT : P1.WritesIn st s s1 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_of_kfoot hwK
  have hS1 := hX1.fin.1.1.1
  have hN1 := hX1.fin.1.1.2.2.1
  have hNsc : NSC Z.N Z.C σ1 := nsc_updTcb J.nsc _ _
  have hI1 : Inv σ1 := Inv.restart J.inv hk hrun
  have hSOK : SOK (true, true) σ σ1 := pres_setThreadState (f := (true, true)) _ _ σ _ hm1
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS1, hN1, hNsc, hI1⟩, hwK, hSOK⟩
  have hRR' : RRecv (L.mem s1) Z.R σ1 :=
    J.rrecv.frame (TFoot.keep hS J.rp hwT).2.2 (KhRB.of_sctkw hK)
  have hF : FK σ σ1 := (fk_setThreadState _ _).of_eq he1
  have hBlk' : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s1 := by
    obtain ⟨x', hk', hRt⟩ := J.xtop.ipc.tcb ct hT
    rw [hk] at hk'; cases hk'
    have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
      have hq := Sched.blockedR_queued hRt.st hb
      cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
    have hTe : Z.T = P1.Heap.tcbs H := by
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
    rw [hTe] at hT
    exact (P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hT (fun h => hnbr (Or.inl h))
      (fun h => hnbr (Or.inr h)) hs1).1
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hP := hX.rel.1
    have hctW : ct = L.curW s := P1.eq_of_bv (hcur.symm.trans J.kern.cur)
    have htf := hP.fits ct _ htcb
    have hta := hP.align ct _ htcb
    have hstv : (stA ct).val = ct.val + 3328 := by
      rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
    have h := set_thread_state_frame (L := L) s ct sched.TS_RESTART (by unfold P1.Aligned; rw [hstv]; omega)
      J.kern.act.1
    rw [hs1, WP.spec_ok] at h
    exact h _ J.kern.dwAl (fun e => J.kern.dwNe.1 (by rw [← hctW]; exact e)) J.kern.dwNe.2
  have hkc : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hcur' : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := by
    rcases J.cur with h | h
    · left
      show (Notif.stsAct _ ct.bv).schedulerAction = _
      unfold Notif.stsAct; split_ifs with hc
      · rfl
      · exact h
    · right
      have := CurInv.restart h hkc
      rw [hcur] at this; exact this
  have hB' : BlockedScActive σ1 := J.bsa.bk (bk_restart hk hrun hm1) hSOK
  have hCR'' : CurRun σ1 := by
    intro y hy
    rw [show σ1.curThread = σ.curThread from (stsAct_fields _ _).2.1, hcur, stsAct_kheap, updK_kheap,
      Function.update_self] at hy
    cases hy; rfl
  have hAI : ActIdle σ1 := (ActIdle.updState J.act hk hrun .restart rfl).ofSts ct.bv
  have hL : LK (fun _ => False) σ σ1 := (lkm_setThreadState (W := fun _ => False) _ _).of_eq he1
  have hDead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_sc_step hX1 hwT hK (fun p y e hy => by subst e; rw [hk] at hy; cases hy; exact hrun) hL hF hAI.1
      hY' ((hSOK.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  refine ⟨Lst', ⟨hCR', hRF', hRR', hY', hM', J.sc_buf hwT hK, hRP', J.sc_apart hwT hK, J.sc_jpl hwT hK (J.idleW_keep hX1.fin.1.1.1 hF.2.1 hF.2.2).2,
    J.sc_jcov hwT hDead (fun q hq hn => absurd hq hn) (J.idleW_keep hX1.fin.1.1.1 hF.2.1 hF.2.2), J.sc_kern hwT hK hF hX1 hDbg (fun _ h => h),
    J.sc_utc hwT hK hDbg, hNsc, hI1, hcur', curOwnW_updTcb J.own hk _, OffOK.restart J.off _, hAI, hB',
    J.isorted.tkw hK, Or.inr (Or.inl hCR''), hBlk'⟩⟩

/-- **`JStepHyps.restart`** (`jowes_restartD`, at the same dead set). -/
theorem jowes_restart {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (s1 : S) (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x))
    (htcb : th ct = some .tcb) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    JOwes (L := L) arI AR th s a σ s1 a
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
  intro Z H Cs Ac Lst D hth J hX1
  subst hth
  obtain ⟨Lst', R⟩ := jowes_restartD arI s a σ ct x s1 hcur hk htcb hrun hs1 J hX1
  exact ⟨Ac, Lst', D, R⟩

/-! ## The slot steps (an insertion, a CNode-only step) -/

/-- **A word outside every slot is kept by writes of slot words** (the slot
steps' write set, `InSlot`). -/
theorem inSlot_keep {th : TypedHeap} {s s' : S} (hw : P1.WritesIn st s s' (InSlot th)) {b : U64} (hb : P1.Aligned b)
    (hout : ∀ a, IsSlot th a → b.val < a.val ∨ a.val + 32 ≤ b.val) : L.mem s' b = L.mem s b :=
  hw.mem_eq hb fun ⟨a, ha, h1, h2⟩ => by rcases hout a ha with h | h <;> omega

/-- **The scheduler's words a slot step keeps** (from `SlotsApart`): the TCBs'
`MCP`, `YIELD_TO` and IPC-buffer words, the SCs' `REPLY` words, the replies'
links. -/
theorem inSlot_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hA := J.apart
  have tw : ∀ t ∈ Z.T, ∀ b : U64, P1.Aligned b → t.val + 256 ≤ b.val → b.val < t.val + 4096 → L.mem s' b = L.mem s b :=
    fun t ht b hb h1 h2 => inSlot_keep hw hb fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega
  refine ⟨fun t ht => tw t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
    fun t ht => tw t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega),
    fun t ht => tw t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, -⟩ := (hS.lists.choose_spec.choose_spec.2).scs q hq
    have hf := hfit x n hk
    exact inSlot_keep hw hal fun y hy => by
      rcases (hA y hy).2.2.2.1 q hq x n hk with h | h <;> omega
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    refine ⟨inSlot_keep hw (J.rp.aligned hr (Or.inl h8)) fun y hy => ?_,
      inSlot_keep hw (J.rp.aligned hr (Or.inr h16)) fun y hy => ?_⟩
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega

/-- A cap naming no endpoint, notification or reply is typed in any heap. -/
theorem capTyped_of_tyObj {H : P1.Heap} {Rp Nt : Set U64} {c : capability.Cap} (h : tyObj c = false) :
    CapTyped H Rp Nt c := by
  unfold CapTyped
  refine ⟨fun p b x y z w e => ?_, fun p b x y e => ?_, fun p g e => ?_⟩ <;> (subst e; simp [tyObj] at h)

/-- `CapTyped` reads a cap's shape only. -/
theorem capTyped_of_shape {H : P1.Heap} {Rp Nt : Set U64} {c d : capability.Cap} (h : shape c = shape d)
    (hd : CapTyped H Rp Nt d) : CapTyped H Rp Nt c := by
  unfold CapTyped at hd ⊢
  refine ⟨fun p b x y z w e => ?_, fun p b x y e => ?_, fun p g e => ?_⟩ <;> subst e
  · cases d <;> simp [shape] at h
    subst h; exact hd.1 _ _ _ _ _ _ rfl
  · cases d <;> simp [shape] at h
    subst h; exact hd.2.1 _ _ _ _ rfl
  · cases d <;> simp [shape] at h
    subst h; exact hd.2.2 _ _ rfl

theorem cslot_tcb3 (t : U64) : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3) = slotOf t 3 := by
  show slotAddr t.bv (Fl4Spec.ofBl _) = _
  rw [slotAddr_ofBl, tcbCnodeIndex_blVal 3 (by decide)]

theorem cslot_tcb2 (t : U64) : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf t 2 := by
  show slotAddr t.bv (Fl4Spec.ofBl _) = _
  rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]

/-- The TCBs' IPC-buffer slots kept or emptied keep `JPlaced.bfs`. -/
theorem Sched.JPlaced.bfsT {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ)
    (hT2 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 2) = capAt (L.mem s) (slotOf t 2) ∨
      capV (L.mem s') (slotOf t 2) = .Null) :
    ∀ t, th t = some .tcb → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))) := by
  intro t ht
  rcases hT2 t ht with e | e
  · rw [capAt_capV, capAt_capV] at e
    rw [cslot_tcb2, eq_of_ok_eq e, ← cslot_tcb2]; exact h.bfs t ht
  · left; rw [cslot_tcb2]; exact e

/-- **`JPlaced` after a slot step** (CNodes' contents changed only, `KeepC`):
the caps keep their objects (`TypedKept`, the IRQ node's slots among the
slots, `IntLayout`), the TCBs' fault-handler slots kept. -/
theorem Sched.JPlaced.slotTF {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ) (hkc : KeepCT σ σ') (hk : L.ksb s' = L.ksb s) (hL : IntLayout th (L.ksb s))
    (hT : TypedKept th (L.mem s) (L.mem s'))
    (hfh : ∀ t, th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbf : ∀ t, th t = some .tcb → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))))
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    JPlaced (L := L) th H Tr C s' σ' := by
  have hirqS : ∀ i : U64, i.val < 128 → IsSlot th (nodeA (L.ksb s) i) := fun i hi => by
    have hA : AbsSlot th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
    have := hA.isSlot; rwa [cslotAddr_nil] at this
  have hty' : ∀ a, IsSlot th a → CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) (capV (L.mem s') a) := by
    intro a ha
    rcases hT a ha with hn | ⟨b, hb, hs⟩
    · exact capTyped_of_tyObj hn
    · exact capTyped_of_shape hs (h.typed b hb)
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk' => ?_, by rw [hk]; exact h.ks, by rw [hk]; exact h.ksIn,
    fun a ha => hty' a ha, fun i hi => by rw [hk]; exact hty' _ (hirqS i hi), hfh, hbf, fun a ha => ?_⟩
  · rcases hkc c.bv with e | ⟨r, cs, cs', -, h2⟩ | ⟨x, y', -, h2, -⟩
    · rw [e] at hk'; exact h.sc c y n hc hk'
    · rw [h2] at hk'; cases hk'
    · rw [h2] at hk'; cases hk'
  · rcases hT a ha with hn | ⟨b, hb, hs⟩
    · exact capObjH_of_tyObj hn
    · rw [hiw]; exact capObjH_of_shape hs (h.cobj b hb)

theorem Sched.JPlaced.slotT {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ) (hkc : KeepCT σ σ') (hk : L.ksb s' = L.ksb s) (hL : IntLayout th (L.ksb s))
    (hT : TypedKept th (L.mem s) (L.mem s'))
    (hT3 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3) ∨
      capV (L.mem s') (slotOf t 3) = .Null)
    (hT2 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 2) = capAt (L.mem s) (slotOf t 2) ∨
      capV (L.mem s') (slotOf t 2) = .Null)
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    JPlaced (L := L) th H Tr C s' σ' := by
  refine h.slotTF hkc hk hL hT (fun t ht => ?_) (h.bfsT hT2) hiw
  rcases hT3 t ht with e | e
  · rw [capAt_capV, capAt_capV] at e
    rw [cslot_tcb3, eq_of_ok_eq e, ← cslot_tcb3]; exact h.fh t ht
  · left; rw [cslot_tcb3]; exact e

theorem Sched.JPlaced.slot {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ) (hkc : KeepC σ σ') (hk : L.ksb s' = L.ksb s) (hL : IntLayout th (L.ksb s))
    (hT : TypedKept th (L.mem s) (L.mem s'))
    (hT3 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3))
    (hT2 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 2) = capAt (L.mem s) (slotOf t 2))
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    JPlaced (L := L) th H Tr C s' σ' :=
  h.slotT (KeepC.t hkc) hk hL hT (fun t ht => Or.inl (hT3 t ht)) (fun t ht => Or.inl (hT2 t ht)) hiw

theorem sizeF_cnode (q r g gb : U64) :
    sizeF (.CNode q r g gb) = core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT := ok_inj (size_eq _).symm

/-- **A CNode cap in the MDB covers its CNode.** -/
theorem covered_cnode {mem : U64 → U64} {G : MdbGhost} {y q r gs g : U64} (hy : y ∈ G.chains.flatten)
    (hc : capV mem y = .CNode q r gs g) (hr : r.val + 5 < 64) (hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64) :
    Covered mem G q.val (q.val + 32 * 2 ^ r.val) := by
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hs : (core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT).val = r.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits,
      fl4_abi.consts.bits.SLOT]
    omega
  have hm := maskF_val (b := core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT) (by rw [hs]; exact hr)
  rw [hs, e5] at hm
  have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine ⟨y, hy, by rw [hc, physF_cnode], by rw [hc]; rfl, by rw [hc]; unfold baseF; rw [ptrF_cnode], ?_⟩
  rw [hc]
  unfold topF
  rw [ptrF_cnode, sizeF_cnode]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

set_option maxHeartbeats 4000000 in
/-- **The untyped caps' facts after an insertion of a non-untyped cap into
any slot `dsl`** (`ins_utc` for a CNode slot, XTopJointTcbInstall's TCB-slot
insert): the untyped caps are those before, their free parts miss every slot
(`RegionFree`), and the new MDB slot misses every childless untyped region,
its object staying in the region's restriction (`hlv`, the destination's
liveness). -/
theorem JAtZ.ins_utcG {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {dsl : Fl4Spec.CslotPtr} (hAd : AbsSlot Z.th dsl)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr dsl → capV (L.mem s') y = capV (L.mem s) y)
    (hnull : capAt (L.mem s) (cslotAddr dsl) = ok .Null)
    (hnu : ∀ p sb fi d, capV (L.mem s') (cslotAddr dsl) ≠ .Untyped p sb fi d)
    (hw : P1.WritesIn st s s' (InSlot Z.th)) (hcdt : CdtKeepOff (· = dsl) σ σ')
    (horig : ∀ sl, sl ≠ dsl → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G')
    (hlv : ∀ sl p sb fi dev, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev →
      dev = false → (¬ ∃ x, σ.cdt x = some sl) →
      ((cslotAddr dsl).val < p.val ∨ p.val + 2 ^ sb.val ≤ (cslotAddr dsl).val) ∧
        AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) dsl) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi := by
  intro sl p sb fi dev hsl hcap' hdF
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hne : cslotAddr sl ≠ cslotAddr dsl := fun e => hnu p sb fi dev (by rw [← e]; exact capV_of_capAt hcap')
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hcap _ hsl.isSlot hne]; exact capV_of_capAt hcap'
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdF
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hfi := U.fiLe
  -- a slot misses the free part
  have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, i, hi, rfl⟩ := hy
    obtain ⟨k, hk, hs⟩ := hi.size
    have hv := hi.val hP
    rcases U.free q k hk with e | e <;> omega
  -- the debug word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  -- the childless facts after are those before
  have hdnm : cslotAddr dsl ∉ Z.G.chains.flatten := fun h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hnull] at h0; exact hn (eq_of_ok_eq h0).symm
  have hnc' : (¬ ∃ x, σ'.cdt x = some sl) → ¬ ∃ x, σ.cdt x = some sl := by
    rintro h0 ⟨x, hx⟩
    apply h0
    by_cases e : x = dsl
    · exfalso
      subst e
      have h1 := hC.cdt _ hAd
      rw [hx] at h1
      exact hdnm (hM.tree.par_mem _ _ h1.symm).1
    · exact ⟨x, by rw [hcdt x e]; exact hx⟩
  have B := notDev_back (capV_of_capAt hcap') hcv
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free,
    fun g w hal h1 h2 => ?_, U.sb4,
    U.nostr, fun y hy => ?_, fun h0 y hy => ?_, 
    fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
  · rw [hw.mem_eq hal fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
    exact U.zero (B g) w hal h1 h2
  · have := hobj y ((hM'.members y).1 hy).1
    omega
  · have hnc := hnc' h0
    by_cases e : y = cslotAddr dsl
    · subst e
      exact (hlv sl p sb fi dev hsl hcv hdF hnc).1
    · obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
      have hc0 : capAt (L.mem s) y = ok c0 := by
        rw [capAt_capV, ← hcap y hys e, ← capAt_capV]; exact h0'
      have hym : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hys, c0, hc0, hn⟩
      exact U.ns hnc y hym
  · have hnc := hnc' h0
    obtain ⟨r1, r3⟩ := U.rst (B g) hnc hf0
    refine ⟨fun sl' h => ?_, by rw [hna, hDbg]; exact r3⟩
    by_cases e : sl' = dsl
    · subst e
      exact (hlv sl p sb fi dev hsl hcv hdF hnc).2
    · exact r1 sl' (by rw [← horig sl' e]; exact h)

/-- **A live CNode misses a childless untyped region** (`DestLive`: named by
a CNode cap of the MDB, which `ut_free` puts outside, or in the kernel-state
block, which the joint cover puts outside every untyped region). -/
theorem JAtZ.live_apart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64} {dev : Bool}
    (hsl : AbsSlot Z.th sl) (hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev) (hdv : dev = false)
    (hnc : ¬ ∃ x, σ.cdt x = some sl) {q : U64} {rd : Nat} (hpd : Z.th q = some (.cnode rd))
    (hDL : DestLive Z.th (L.mem s) (L.ksb s) q) :
    q.val + 32 * 2 ^ rd ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val := by
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl) := fun y hy => by
    obtain ⟨z, hz⟩ := desc_tail_child hy
    exact hnc ((hC.has_child_iff hP hsl).2 ⟨z, hz⟩)
  rcases hDL with ⟨y, r, gs, g, hy, hyc⟩ | hks'
  · have hya : capAt (L.mem s) y = ok (.CNode q r gs g) := by rw [capAt_capV, hyc]
    have hym : y ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hy, _, hya, fun h => by cases h⟩
    obtain ⟨sly, hsly, hsly'⟩ := IsSlot.abs hy
    have hcvy : CapValid Z.th (.CNode q r gs g) := hV.abs hsly (by rw [hsly']; exact hya)
    obtain ⟨hth, -⟩ := hcvy
    rw [hpd] at hth; cases hth
    have hfit := hP.fits q _ hpd
    simp only [objSize] at hfit
    have hq0n : q.val ≠ 0 := by
      intro e0
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have := hJ.cnode q _ hpd
      have e0' : q = 0#u64 := UScalar.eq_of_val_eq (by simpa using e0)
      rw [e0', J.kern.h0] at this; cases this
    have hr5 : r.val + 5 < 64 := by
      by_contra hc
      have : 2 ^ 64 ≤ 32 * 2 ^ r.val := by
        calc 2 ^ 64 ≤ 2 ^ (r.val + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 32 * 2 ^ r.val := by rw [pow_add]; ring
      omega
    have hcov := covered_cnode hym hyc hr5 hfit
    have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
    exact ut_free J.ut hI hxm hcv hnd (by omega) hcov
  · have hk := hks' _ hpd
    simp only [objSize] at hk
    have := (J.jcov.ks _ hxm p sb fi (by rw [hcv, hdv])).1
    omega

/-- **A slot of a live CNode misses a childless untyped region**, and the
CNode stays an object of the region's restriction. -/
theorem JAtZ.live_slot {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64} {dev : Bool}
    (hsl : AbsSlot Z.th sl) (hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev) (hdv : dev = false)
    (hnc : ¬ ∃ x, σ.cdt x = some sl) {w : Fl4Spec.CslotPtr}
    (hw : ∃ q r, w.1 = q.bv ∧ Z.th q = some (.cnode r) ∧ w.2.length = r ∧ DestLive Z.th (L.mem s) (L.ksb s) q) :
    ((cslotAddr w).val < p.val ∨ p.val + 2 ^ sb.val ≤ (cslotAddr w).val) ∧
      AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) w := by
  obtain ⟨q, rd, hq1, hpd, hld, hDL⟩ := hw
  have hl := J.live_apart arI hsl hcv hdv hnc hpd hDL
  have hP := J.xtop.rel.1
  obtain ⟨q0, i0, hi0, hq1', hq2⟩ := AbsSlot.at (th := Z.th) (sl := w) ⟨q, hq1, Or.inl (by rw [hld]; exact hpd)⟩
  have hq0 : q0 = q := P1.eq_of_bv (hq1'.symm.trans hq1)
  subst hq0
  have hdv : (cslotAddr w).val = q0.val + 32 * i0 := by rw [hq2]; exact hi0.val hP
  have hi0lt : 32 * (i0 + 1) ≤ 32 * 2 ^ rd := by
    rcases hi0 with ⟨r, hr, hir⟩ | ⟨ht, -⟩
    · rw [hpd] at hr; cases hr; omega
    · rw [hpd] at ht; cases ht
  refine ⟨by omega, q0, hq1, Or.inl ?_⟩
  have h1 : 1 ≤ 2 ^ rd := Nat.one_le_two_pow
  simp only [restrictTh]
  rw [if_neg (by omega)]
  rw [hld]; exact hpd

set_option maxHeartbeats 4000000 in
/-- **The untyped caps' facts after an insertion of a non-untyped cap into
a CNode slot** (the IRQ and IO-port inserts, `JStepHyps.slot`): `ins_utcG`,
the destination's CNode live (`DestLive`, `live_slot`). -/
theorem JAtZ.ins_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {pd : U64} {rd : Nat} {idxd : List Bool} (hpd : Z.th pd = some (.cnode rd)) (hld : idxd.length = rd)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y)
    (hnull : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (hnu : ∀ p sb fi d, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Untyped p sb fi d)
    (hw : P1.WritesIn st s s' (InSlot Z.th)) (hcdt : CdtKeepOff (· = (pd.bv, idxd)) σ σ')
    (horig : ∀ sl, sl ≠ (pd.bv, idxd) → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G') (hDL : DestLive Z.th (L.mem s) (L.ksb s) pd) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi :=
  J.ins_utcG arI ⟨pd, rfl, Or.inl (by rw [hld]; exact hpd)⟩ hcap hnull hnu hw hcdt horig hgp hM'
    fun _ _ _ _ _ hsl hcv hdv hnc => J.live_slot arI hsl hcv hdv hnc ⟨pd, rd, rfl, hpd, hld, hDL⟩

/-- **A slot of a TCB named by a thread cap of a slot misses a childless
untyped region**, and the TCB stays an object of the region's restriction
(the thread cap in the MDB covers the TCB's 4 KiB, `ut_free`). -/
theorem JAtZ.live_slotT {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64} {dev : Bool}
    (hsl : AbsSlot Z.th sl) (hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev)
    (hnc : ¬ ∃ x, σ.cdt x = some sl) {t : U64} (ht : Z.th t = some .tcb) {n : Nat} (hn : n < tcbSlots)
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) :
    ((cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)).val < p.val ∨
        p.val + 2 ^ sb.val ≤ (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)).val) ∧
      AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) (t.bv, Fl4Spec.tcbCnodeIndex n) := by
  obtain ⟨hP, ⟨-, -, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl) := fun y hy => by
    obtain ⟨z, hz⟩ := desc_tail_child hy
    exact hnc ((hC.has_child_iff hP hsl).2 ⟨z, hz⟩)
  obtain ⟨y, hy, hyc⟩ := hlive
  have hya : capAt (L.mem s) y = ok (.Thread t) := by rw [capAt_capV, hyc]
  have hym : y ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hy, _, hya, fun h => by cases h⟩
  have hfit := hP.fits t _ ht
  simp only [objSize] at hfit
  have e12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  have hcov := covered_of_cap hym hyc (physF_thread t) rfl (range_thread t (by rw [e12]; omega))
  have hl := ut_free J.ut hI hxm hcv hnd (by rw [e12]; omega) hcov
  rw [e12] at hl
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  obtain ⟨q0, i0, hi0, hq1', hq2⟩ := AbsSlot.at hAt
  have hq0 : q0 = t := P1.eq_of_bv hq1'.symm
  subst hq0
  have hdv : (cslotAddr (q0.bv, Fl4Spec.tcbCnodeIndex n)).val = q0.val + 32 * i0 := by rw [hq2]; exact hi0.val hP
  have hi0lt : 32 * (i0 + 1) ≤ 4096 := by
    obtain ⟨k, hk, hs⟩ := hi0.size
    rw [ht] at hk; cases hk; simpa [objSize] using hs
  refine ⟨by omega, q0, rfl, Or.inr ⟨?_, n, hn, rfl⟩⟩
  simp only [restrictTh]
  rw [if_neg (by omega)]
  exact ht

set_option maxHeartbeats 4000000 in
/-- **The untyped caps' facts after a CNode-only step** (a copy, mint,
move, mutate or rotate, `JStepHyps.cslot`): each untyped cap after comes
from one before (`UtSrc`), the slots written lie in live CNodes
(`DestLive`), so miss every childless untyped region, and the free parts
miss every slot (`RegionFree`). -/
theorem JAtZ.cn_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧ sl.2.length = r ∧
      DestLive Z.th (L.mem s) (L.ksb s) p)
    (hcW : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y)
    (hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W)
    (hUS : UtSrc Z.th (L.mem s) (L.mem s') σ σ')
    (hw : P1.WritesIn st s s' (InSlot Z.th))
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G') :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi := by
  intro sl p sb fi dev hsl hcap' hdv
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  obtain ⟨sl0, fi0, hs0, hc0, hcase⟩ := hUS sl p sb fi dev hsl (capV_of_capAt hcap')
  have hcap0 : capAt (L.mem s) (cslotAddr sl0) = ok (.Untyped p sb fi0 dev) := by rw [capAt_capV, hc0]
  have U := J.utc sl0 p sb fi0 dev hs0 hcap0 hdv
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  -- a slot misses the free part
  have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p.val + fi0.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, i, hi, rfl⟩ := hy
    obtain ⟨k, hk, hs⟩ := hi.size
    have hv := hi.val hP
    rcases U.free q k hk with e | e <;> omega
  -- the debug word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  -- the MDB's slots after: those before and the written ones
  have hnew : ∀ y ∈ G'.chains.flatten, y ∈ Z.G.chains.flatten ∨ ∃ w ∈ W, y = cslotAddr w := by
    intro y hy
    obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
    by_cases e : ∀ w ∈ W, y ≠ cslotAddr w
    · have hc0 : capAt (L.mem s) y = ok c0 := by
        rw [capAt_capV, ← hcW y hys e, ← capAt_capV]; exact h0'
      exact Or.inl ((hM.members y).2 ⟨hys, c0, hc0, hn⟩)
    · push_neg at e
      exact Or.inr e
  have B : NotDev (L.mem s') (cslotAddr sl) p sb fi → NotDev (L.mem s) (cslotAddr sl0) p sb fi0 :=
    notDev_of_flag (capV_of_capAt hcap') hc0
  rcases hcase with ⟨rfl, hcd⟩ | ⟨hfull, hch⟩
  · refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free,
      fun g w hal h1 h2 => ?_, U.sb4,
      U.nostr, fun y hy => ?_, fun h0 y hy => ?_, 
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
    · rw [hw.mem_eq hal fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
      exact U.zero (B g) w hal h1 h2
    · have := hobj y ((hM'.members y).1 hy).1
      omega
    · have hnc := hcd h0
      rcases hnew y hy with hym | ⟨w, hwW, rfl⟩
      · exact U.ns hnc y hym
      · exact (J.live_slot arI hs0 hc0 hdv hnc (hW w hwW)).1
    · have hnc := hcd h0
      obtain ⟨r1, r3⟩ := U.rst (B g) hnc hf0
      refine ⟨fun sl' h => ?_, by rw [hna, hDbg]; exact r3⟩
      rcases hoW sl' h with h' | hwW
      · exact r1 sl' h'
      · exact (J.live_slot arI hs0 hc0 hdv hnc (hW sl' hwW)).2
  · refine ⟨U.pal, U.pfit, by omega, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g),
      fun q k hk => by rcases U.nostr q k hk with h | h | h <;> omega,
      fun _ w _ h1 h2 => by omega, U.sb4, U.nostr, fun y _ => by omega, fun h0 => absurd hch h0,
      fun _ h0 => absurd hch h0,
      fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩

theorem JOwesD.toOwes {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (h : JOwesD (L := L) arI AR th s a σ s' a' σ') : JOwes (L := L) arI AR th s a σ s' a' σ' :=
  fun Z H Cs Ac Lst D hth J hX' => let ⟨Ac', Lst', R⟩ := h Z H Cs Ac Lst D hth J hX'; ⟨Ac', Lst', D, R⟩

theorem JOwesCsD.toCs {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (h : JOwesCsD (L := L) arI AR th G' s a σ s' a' σ') :
    JOwesCs (L := L) arI AR th G' s a σ s' a' σ' :=
  fun Z H Cs Ac Lst D hth J hX' => let ⟨hC, Ac', Lst', R⟩ := h Z H Cs Ac Lst D hth J hX'; ⟨hC, Ac', Lst', D, R⟩

/-- **What a slot step still owes** [W] (each reads the caps changed): the covering caps
surviving and no new untyped region (`CoverKept`, `UtKept`: `jcov_cover`),
the new original bits at `AbsSlot`s (`kern_keep`) and the untyped caps'
facts. -/
def SlotRest (Z : XSets) (s s' : S) (σ σ' : Fl4Spec.State Unit) : Prop :=
    CoverKept Z.th (L.mem s) (L.mem s') ∧ UtKept Z.th (L.mem s) (L.mem s') ∧
    (∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl) ∧
    (∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)

set_option maxHeartbeats 4000000 in
/-- **A slot step's `JOwesCs` from `SlotRest`**: FL4 writes slot words only
(`inSlot_keeps`), the spec changes CNodes only (`CnStep`, SpecKeepC); the
CSpace fields by `jcs_slot` (`DelInv` kept by the step, the objects' kinds kept, `KSz`). -/
theorem jowes_slotOf {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hcn : Ipc.CnK σ σ') (hkc : KeepC σ σ') (hw : P1.WritesIn st s s' (InSlot th))
    {kb : U64} (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV kb (L.mem s') G') (hkz : KSz σ σ')
    (hTK : TypedKept th (L.mem s) (L.mem s'))
    (hT3 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3))
    (hT2 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 2) = capAt (L.mem s) (slotOf t 2))
    (hDl : DelInv th (L.mem s) → DelInv th (L.mem s'))
    (hR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR { Z with G := G' } s' a σ' →
      SlotRest (L := L) arI { Z with G := G' } s s' σ σ') :
    JOwesCsD (L := L) arI AR th G' s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  subst hth
  have hC := CnStep.of_cnK hcn
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlot_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hC.toHStep.khrb
  obtain ⟨hCK, hUK, horig, hutc⟩ := hR Z H Cs Ac Lst D rfl J hX'
  -- P1's `BlkOK`: the slot words are cap-slot words (`JPlaced.slotCapW`)
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    have hPl := J.xtop.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    exact (P1.blk_of_capw J.blk hw' (J.slotCapW P1.tlow_slots)).1
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    let ⟨Tr, Cq, hJ⟩ := J.jpl
    ⟨Tr, Cq, hJ.slot hkc hw.1 J.intL hTK hT3 hT2 (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc).2⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q := fun q _ hd =>
    J.deadP_hstep hX' hC.toHStep k3 (fun q z hq K h8 hK => J.inSlot_scKeep hw hq h8 hK) (J.act.cn hC).1
      (J.yld.frame k2 yk) yk hd
  obtain ⟨-, ⟨-, -, hM', -, -⟩, -⟩ := hX'.rel
  have hJC := J.jcs_slot hM' hMO hFI hUK hkz (hDl J.del)
  have hjc := J.jcov_cover hw.1 hM' hCK hUK (fun q hq => hdead q hq (J.jcov.dead q hq))
    (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc)
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hC.ct hC.csc horig hgp
    (fun p ao h => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 h) hDbg
    (D' := D)
  refine ⟨hJC, Ac, Lst, ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_keepC hkc), hjpl,
    hjc, hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, CurInvW.cn J.cur hC, J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep (Or.inr hC.act), hblk⟩⟩

/-- **`JStepHyps.slot`**, with no premise (an insertion between two CNodes'
slots: `CnK`, and `KeepC` from the two CNodes, `capInsert_nko`; the
destination's cap the only one changed, from `Null` and to no untyped cap:
`CoverKept`, `UtKept`; its original bit the only one set, at an `AbsSlot`;
the untyped caps' facts by `ins_utc`, the destination's CNode live). -/
theorem jowes_ins {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (c : Fl4Spec.Cap) (ps pd : U64) (rs rd : Nat) (idxs idxd : List Bool)
    (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    (hci : Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False))
    (hld : idxd.length = rd)
    (hcap : ∀ y, IsSlot th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y)
    (hnull : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (hnu : ∀ p sb fi d, capV (L.mem s') (cslotAddr (pd.bv, idxd)) ≠ .Untyped p sb fi d)
    (hw : P1.WritesIn st s s' (InSlot th)) (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTK : TypedKept th (L.mem s) (L.mem s'))
    (hT3 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3))
    (hDL : DestLive th (L.mem s) (L.ksb s) pd) (hDl : DelInv th (L.mem s) → DelInv th (L.mem s')) :
    JOwesCsD (L := L) arI AR th G' s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hSt := J.xtop.rel.2.1.1
  subst hth
  have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko c _ _ σ _ hmem) (by
    rintro p (rfl | hp)
    · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
    · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
  have hT2 : ∀ t, Z.th t = some .tcb → capAt (L.mem s') (slotOf t 2) = capAt (L.mem s) (slotOf t 2) := by
    intro t ht
    have hs : IsSlot Z.th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by decide⟩, rfl⟩
    rw [capAt_capV, capAt_capV, hcap _ hs fun e => cnode_slot_ne_tcb J.xtop.rel.1 hpd hld ht 2 (by decide)
      (by rw [cslot_tcb2]; exact e.symm)]
  refine jowes_slotOf arI s s' a σ σ' hcn hkc hw hFI hMO (capInsert_nkz c _ _ σ _ hmem) hTK hT3 hT2 hDl
    (fun Z2 H2 Cs2 Ac2 Lst2 D2 hth2 J2 hX2 => ?_) Z H Cs Ac Lst D rfl J hX'
  have hcap' : ∀ y, IsSlot Z2.th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y :=
    fun y h => hcap y (hth2 ▸ h)
  obtain ⟨-, ⟨-, -, hM2', -, -⟩, -⟩ := hX2.rel
  have hutc := J2.ins_utc arI (G' := G') (hth2 ▸ hpd) hld hcap' hnull hnu (hth2 ▸ hw)
    (capInsert_cdt c _ _ σ _ hmem) (fun sl e => capInsert_orig c _ _ σ ((), σ') hmem sl e)
    (by have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e) hM2' (hth2 ▸ hDL)
  have hn0 : capV (L.mem s) (cslotAddr (pd.bv, idxd)) = .Null := by
    have h := capAt_capV (L.mem s) (cslotAddr (pd.bv, idxd)); rw [hnull] at h; exact (eq_of_ok_eq h).symm
  refine ⟨fun y hy hp hu => ?_, fun x hx p sb fi d hc => ?_, fun sl h => ?_, hutc⟩
  · have hyd : y ≠ cslotAddr (pd.bv, idxd) := fun e => by rw [e, hn0, physF_null] at hp; cases hp
    have e := hcap' y hy hyd
    exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  · have hxd : x ≠ cslotAddr (pd.bv, idxd) := fun e => hnu p sb fi d (e ▸ hc)
    exact ⟨x, hx, fi, by rw [← hcap' x hx hxd]; exact hc, Or.inl le_rfl⟩
  · by_cases e : sl = (pd.bv, idxd)
    · right; subst e; exact ⟨pd, rfl, Or.inl (by rw [hld]; exact hth2 ▸ hpd)⟩
    · left; rw [← capInsert_orig c _ _ σ ((), σ') hmem sl e]; exact h

/-- **`JStepHyps.cslot`**, with no premise (a CNode copy, mint, move, mutate
or rotate: `CnK`, `KeepC`, the cover, the untyped regions and the original
bits from the step, StepSem's `cslot`; the untyped caps' facts by `cn_utc`). -/
theorem jowes_cn {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {G' : MdbGhost} (s s' : S) (a : A)
    (σ σ' : Fl4Spec.State Unit) (hcn : Ipc.CnK σ σ') (hkc : KeepC σ σ')
    (hCK : CoverKept th (L.mem s) (L.mem s')) (hUK : UtKept th (L.mem s) (L.mem s'))
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot th sl)
    (hw : P1.WritesIn st s s' (InSlot th)) (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hkz : KSz σ σ') (hTK : TypedKept th (L.mem s) (L.mem s'))
    (hT3 : ∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 3) = capAt (L.mem s) (slotOf t 3))
    (hDl : DelInv th (L.mem s) → DelInv th (L.mem s')) (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ th p = some (.cnode r) ∧ sl.2.length = r ∧ DestLive th (L.mem s) (L.ksb s) p)
    (hcW : ∀ y, IsSlot th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y)
    (hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W)
    (hUS : UtSrc th (L.mem s) (L.mem s') σ σ') :
    JOwesCsD (L := L) arI AR th G' s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  have hPl : Placed th := hth ▸ J.xtop.rel.1
  refine jowes_slotOf arI s s' a σ σ' hcn hkc hw hFI hMO hkz hTK hT3 ?_ hDl (fun Z2 H2 Cs2 Ac2 Lst2 D2 hth2 J2 hX2 => ?_)
    Z H Cs Ac Lst D hth J hX'
  · intro t ht
    have hs : IsSlot th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by decide⟩, rfl⟩
    rw [capAt_capV, capAt_capV, hcW _ hs fun sl hsl e => ?_]
    obtain ⟨p, r, h1, hp, hl, -⟩ := hW sl hsl
    have hsl' : sl = (p.bv, sl.2) := Prod.ext h1 rfl
    rw [hsl'] at e
    exact cnode_slot_ne_tcb hPl hp hl ht 2 (by decide) (by rw [cslot_tcb2]; exact e.symm)
  subst hth2
  obtain ⟨-, ⟨-, -, hM2', -, -⟩, -⟩ := hX2.rel
  exact ⟨hCK, hUK, horig, J2.cn_utc arI W hW hcW hoW hUS hw
    (by have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e) hM2'⟩

/-! ## A kernel-state step -/

/-- **A word outside the kernel-state block is kept by `KsW` writes** (the
kernel-state steps' write set). -/
theorem ksW_keep {s s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s))) {b : U64} (hb : P1.Aligned b)
    (hout : b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val) : L.mem s' b = L.mem s b :=
  hw.mem_eq hb fun h => by obtain ⟨K, h1, h2, -, e⟩ := h; omega

/-- **The scheduler's words a kernel-state step keeps** (as `inSlot_keeps`):
the TCBs, the SCs and the replies lie outside the kernel-state block. -/
theorem ksW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s))) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  refine ⟨fun t ht => ksW_keep hw (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; rcases hko t ht with h | h <;> omega),
    fun t ht => ksW_keep hw (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; rcases hko t ht with h | h <;> omega),
    fun t ht => ksW_keep hw (tIpcBufA_aligned (hT t ht)) (by
      rw [tIpcBufA_val (hT t ht)]; rcases hko t ht with h | h <;> omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, hx⟩ := hs.scs q hq
    have := (hS.scOutIn hq (a := scReplyA q) ⟨by rw [hv]; omega, by rw [hv]; omega⟩).2.2.2
    exact ksW_keep hw hal (Sched.ksb_word_out hal J.kern.ksbAl this)
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have hk := J.rp.ksb r hr
    exact ⟨ksW_keep hw (J.rp.aligned hr (Or.inl h8)) (by omega), ksW_keep hw (J.rp.aligned hr (Or.inr h16)) (by omega)⟩

/-- **`JPlaced` across a step** keeping every slot, the kernel-state base,
the SCs' sizes and the IRQ node's caps (`JPlaced.same`). -/
theorem JAtZ.jpl_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hkh : σ'.kheap = σ.kheap) (hks : L.ksb s' = L.ksb s)
    (hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i))
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨Tr, Cq, hJ.same hSS (fun c y n _ hk => ⟨y, by rw [← hkh]; exact hk⟩) hks hI hiw⟩

/-- **The IRQ node's caps are kept by writes outside its words.** -/
theorem irqNode_keep {s s' : S} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hW : ∀ b, W b → b.val < (L.ksb s).val + 1248 ∨ (L.ksb s).val + 5344 ≤ b.val) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hv := nodeA_val hf hi
  have hv8 : (wordOf (nodeA (L.ksb s) i) 8#u64).val = (L.ksb s).val + 1248 + 32 * i.val + 8 := by
    rw [wordOf_val (by rw [hv]; simp; omega), hv]; rfl
  unfold capV
  rw [hw.mem_eq (b := nodeA (L.ksb s) i) (by unfold P1.Aligned; rw [hv]; omega) fun h => by
      rcases hW _ h with e | e <;> omega,
    hw.mem_eq (b := wordOf (nodeA (L.ksb s) i) 8#u64) (by unfold P1.Aligned; rw [hv8]; omega) fun h => by
      rcases hW _ h with e | e <;> omega]

set_option maxHeartbeats 4000000 in
/-- **`JStepHyps.ks`**, with no premise, the dead set kept: FL4 writes kernel-state words only
(`ksW_keeps`), the spec keeps the heap and the scheduler's fields (`KsStep`,
so `CnStep`); the untyped caps' facts kept (the caps and their free parts lie
outside the kernel-state block); P1's `BlkOK` kept (`blk_of_capw`: the
kernel-state words are in `Ω` and none is an SC word, `SgOK`). -/
theorem jowes_ksD {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit)
    (hw : P1.WritesIn st s s' (KsW (L.ksb s))) (hO : KsStep σ σ') :
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR Z s' a' σ' →
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JRest (L := L) arI Z H Cs Ac' Lst' D s' σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  have hC : CnStep σ σ' := ⟨⟨fun p => Or.inl (by rw [hO.kh]), hO.rel, hO.ct, hO.csc, hO.ctime, hO.cons, hO.idle, hO.isc⟩,
    hO.rq, hO.act⟩
  obtain ⟨k1, k2, kb, k3, k4⟩ := ksW_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hC.toHStep.khrb
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    have hw' : P1.WritesIn st s s' (fun b => KsW (L.ksb s) b ∧ P1.Aligned b) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn ⟨h, hb⟩⟩
    have hSg := J.blk.2.2.2.2
    have h0 := J.blk.1.choose_spec.choose_spec
    refine (P1.blk_of_capw J.blk hw' fun b hb => ?_).1
    obtain ⟨⟨K, h1, h2, -, e, -⟩, hal⟩ := hb
    refine Or.inr ⟨?_, fun hm => ?_⟩
    · have hK8 : K.val % 8 = 0 := by
        have := J.kern.ksbAl; have hb8 : b.val % 8 = 0 := hal; omega
      have eb : b = core.num.U64.wrapping_add (L.ksb s) K :=
        UScalar.eq_of_val_eq (by rw [P1.ks_val h0 h2]; exact e)
      rw [eb]; exact hSg.ksΩ K h2 hK8
    · have := hSg.ks b hm; omega
  have hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw J.kern.ksbFit J.kern.ksbAl fun b hb => by
      obtain ⟨K, -, -, -, e, h⟩ := hb; omega
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hf := J.kern.nodeFit
    have hv := nodeAt_val' (st := st) (s := s) (c := 0#u64) (off := layout.node.DEBUG_TCBS) (by simp; omega)
      (by simp [layout.node.DEBUG_TCBS])
    exact ksW_keep hw J.kern.dwAl (by rw [hv]; omega)
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hO.ct hO.csc (fun sl h => Or.inl (by rw [← hO.orig]; exact h)) hO.gpml4 (fun p ao h => by rw [hO.kh]; exact h)
    hDbg (D' := D)
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC.toHStep k3 (fun q z hq K h8 hK => J.ksW_scKeep hw hq h8 hK) (J.act.cn hC).1
      (J.yld.frame k2 yk) yk (J.jcov.dead q hq)
  -- the untyped caps' facts: the caps kept, the free parts outside the kernel-state block
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
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
    have hfi := U.fiLe
    have hk8 := J.kern.ksbAl
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, fun g w hal h1 h2 => ?_, U.sb4,
      U.nostr, U.nsFree, fun h0 => U.ns (by rw [hO.cdt] at h0; exact h0),
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [hO.gpml4]; exact U.gReg (B g)⟩
    · have hw8 : w.val % 8 = 0 := hal
      have hapart := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).1
      rw [ksW_keep hw hal (by omega)]
      exact U.zero (B g) w hal h1 h2
    · rw [hO.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← hO.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  exact ⟨Ac, Lst, ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_kheap hO.kh),
    J.jpl_keep arI hSS hO.kh hw.1 hI (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc).2, J.jcov_keep hw.1 hSS hdead (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc), hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, CurInvW.cn J.cur hC, J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep (Or.inr hC.act), hblk⟩⟩

/-- `jowes_ksD` with the dead set existential (`JOwes`). -/
theorem jowes_ks {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit)
    (hw : P1.WritesIn st s s' (KsW (L.ksb s))) (hO : KsStep σ σ') :
    JOwes (L := L) arI AR th s a σ s' a' σ' := fun Z H Cs Ac Lst D hth J hX' =>
  let ⟨Ac', Lst', R⟩ := jowes_ksD arI s s' a a' σ σ' hw hO Z H Cs Ac Lst D hth J hX'
  ⟨Ac', Lst', D, R⟩

/-! ## A scheduler step -/

/-- **The scheduler's words a scheduler step keeps** (as `inSlot_keeps`, for
`SchW`: the TCBs' queue words, the node, the domain words). -/
theorem schW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (SchW (L := L) Z.T Z.c s)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  have hP := J.xtop.fin.1.2
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hnd := hc.node.disj
  -- a word apart from the TCBs' queue words, the node and the domain words
  have keep : ∀ b : U64, P1.Aligned b → (∀ y ∈ Z.T, b.val ≠ y.val + 3480 ∧ b.val ≠ y.val + 3488 ∧ b.val ≠ y.val + 3592) →
      (b.val < L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ b.val) →
      (b.val + 8 ≤ (L.ksb s).val + 16 ∨ (L.ksb s).val + 216 < b.val) → L.mem s' b = L.mem s b := by
    intro b hb h1 h2 h3
    refine hw.mem_eq hb fun hb' => ?_
    rcases schW_val hT hkf hb' with ⟨y, hy, e | e | e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
    · exact (h1 y hy).1 e
    · exact (h1 y hy).2.1 e
    · exact (h1 y hy).2.2 e
    · omega
    · omega
  have tw : ∀ t ∈ Z.T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := by
    intro t ht K h1 h8 n1 n2 n3
    have hv := Notif.tfield_val (hT t ht) h1 (K := K)
    refine keep _ (P1.field_aligned (hT t ht) h1 h8) (fun y hy => ?_) ?_ ?_
    · by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hP.ep ht hy e; omega
    · have := hnd t ht; omega
    · rcases hko t ht with h | h <;> omega
  refine ⟨fun t ht => tw t ht 3440#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
    fun t ht => tw t ht 3472#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
    fun t ht => tw t ht 3512#u64 (by simp) (by simp) (by simp) (by simp) (by simp), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, -⟩ := sc_reply_word hS hq
    obtain ⟨-, o1, o2, o3⟩ := hS.scOutIn hq (a := scReplyA q) ⟨by rw [hv]; omega, by rw [hv]; omega⟩
    refine keep _ hal (fun y hy => ?_) (by omega) (by omega)
    rcases o2 y hy with h | h <;> omega
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have hk := J.rp.ksb r hr
    have ht := J.rp.tcb r hr
    refine ⟨keep _ (J.rp.aligned hr (Or.inl h8)) (fun y hy => ?_) (by omega) (by omega),
      keep _ (J.rp.aligned hr (Or.inr h16)) (fun y hy => ?_) (by omega) (by omega)⟩
    · rcases ht y hy with h | h <;> omega
    · rcases ht y hy with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **`JStepHyps.sched`**, with no premise: FL4 writes the scheduler's words
(`schW_keeps`), the spec keeps the heap (`SchedK`, so `HStep`); `Inv`, the
current thread's invariant and `ActIdle` after (`SchedQOK`: the ready queues
gain schedulable threads only, the action kept or `chooseNewThread`); P1's
`BlkOK` after (`BlkKeep`); the node-0 debug word and the untyped caps'
facts kept (the footprint `SchW` misses them). -/
theorem jowes_sched {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit)
    (hS : SchedStep (L := L) th s σ s' σ') :
    JOwesD (L := L) arI AR th s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  subst hth
  obtain ⟨hK, hS2, hQ, hBK⟩ := hS
  have hw := (hS2 Z.N Z.T Z.C Z.c J.thT J.xtop.fin.1.1.1 J.xtop.fin.1.1.2.2.1).2.1
  have hC : HStep σ σ' := ⟨fun p => Or.inl (by rw [hK.kh]), hK.rel, hK.ct, hK.csc, hK.ctime, hK.cons, hK.idle, hK.isc⟩
  obtain ⟨k1, k2, kb, k3, k4⟩ := schW_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hC.khrb
  -- the spec's scheduler invariants after
  have hI' : Inv σ' := J.inv.congr' hK.kh (fun d p u hu => by
    rcases hQ.1 d p u hu with ⟨d', p', h'⟩ | hs
    · exact J.inv.rq d' p' u h'
    · obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
      exact ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩) hK.rel hK.ctime
  have hcur' : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J.cur with h | h
    · rcases hQ.2 with e | e
      · exact Or.inl e
      · exact Or.inl (by rw [e, h])
    · exact Or.inr (h.congr hK.kh hK.ct hK.csc hK.rel hK.isc)
  have hA' : ActIdle σ' := by
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases hQ.2 with e | e
      · rw [e] at ht; cases ht
      · rw [e] at ht; rw [schedulable_heap hK.kh hK.rel]; exact J.act.1 t ht
    · obtain ⟨x, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨x, by rw [hK.kh, hK.idle]; exact h1, by rw [hK.isc]; exact h2, h3, by rw [hK.idle, hK.rel]; exact h4⟩
  have hblk := hBK _ _ _ H _ _ _ _ _ Ac (fun t ht => J.zH.1 t (J.thT t ht)) J.blk
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hcq.ksOut t ht with h | h <;> omega
  have h88 : (layout.node.DEBUG_TCBS).val = 88 := by simp [layout.node.DEBUG_TCBS]
  -- the node-0 debug word: no TCB queue word (the TCBs miss the kernel-state
  -- block), not core `c`'s node but its own debug word, no domain word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hf := J.kern.nodeFit
    have hv : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = (L.ksb s).val + 13568 + 88 := by
      rw [nodeAt_val' (st := st) (s := s) (c := 0#u64) (off := layout.node.DEBUG_TCBS) (by simp; omega)
        (by simp [layout.node.DEBUG_TCBS])]
      simp [layout.node.DEBUG_TCBS]
    refine hw.mem_eq J.kern.dwAl fun hb => ?_
    rcases hb with hb' | ⟨g1, g2, g3⟩ | hb'
    · obtain ⟨y, hy, e⟩ := hb'
      have e' := tfield3_val (hcq.tcbs y hy) e
      rw [hv] at e'
      rcases hko y hy with h | h <;> omega
    · rw [hv, hnb] at g1 g2 g3
      omega
    · have := domKW_val hb'
      rw [hv] at this; omega
  -- the untyped caps' facts: the caps, the CDT and the original bits kept, the
  -- free parts off the TCBs, the node and the kernel-state block
  have hSS0 : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => schW_oobj J.xtop.fin.1.1.1.placed.tcb hb
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have hks : L.ksb s' = L.ksb s := hw.1
    have hcpu : L.cpu s' = L.cpu s := hw.2.1
    have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
      rw [← hSS0.capV hsl.isSlot]; exact capV_of_capAt hcap
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
    have U := J.utc sl p sb fi dev hsl hcap0 hdv
    have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
    have hfi := U.fiLe
    have hcZ : Z.c ∈ Cs := by rw [← hcq.cur]; exact J.kern.cpuCs
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, fun g w hal h1 h2 => ?_, U.sb4,
      U.nostr, U.nsFree, fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [hK.arch]; exact U.gReg (B g)⟩
    · have hapart := J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))
      have hnd := hapart.2.1 Z.c hcZ
      rw [hw.mem_eq hal fun hb => ?_]
      · exact U.zero (B g) w hal h1 h2
      rcases schW_val hcq.tcbs hkf hb with ⟨y, hy, e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
      · have hty : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
        have := U.free y _ hty
        simp only [objSize] at this
        rcases e with e | e | e <;> omega
      · omega
      · have := hapart.1; omega
    · rw [hK.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  have hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw hkf J.kern.ksbAl fun b hb => by
      rcases schW_val hcq.tcbs hkf hb with ⟨y, hy, e | e | e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
      all_goals first
        | omega
        | (rcases hko y hy with h | h <;> omega)
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hK.ct hK.csc (fun sl h => Or.inl (by rw [← hK.orig]; exact h)) (by rw [hK.arch])
    (fun p ao h => by rw [hK.kh]; exact h) hDbg (D' := D)
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => schW_oobj J.xtop.fin.1.1.1.placed.tcb hb
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC k3 (fun q z hq K h8 hK => J.schW_scKeep hw hq h8 hK) hA'.1 (J.yld.frame k2 yk) yk
      (J.jcov.dead q hq)
  exact ⟨Ac, Lst, ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_kheap hK.kh),
    J.jpl_keep arI hSS hK.kh hw.1 hI (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc).2, J.jcov_keep hw.1 hSS hdead (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc), hkern, hutc, J.nsc.cn hC, hI', hcur', J.own.cn hC, J.off.cn hC, hA', J.bsa.cn hC, J.isorted.cn hC,
    J.curRun.cn hC hQ.2, hblk⟩⟩


/-- **`JStepHyps`, proved**: every primitive step's residue is discharged
(`jowes_restart`, `jowes_ks`, `jowes_ins`, `jowes_sched`, `jowes_cn`); a
notification cap's deletion is no primitive step (StepSem; the IRQ handler
invocations' deletion at `J` in XTopJointIrqL). -/
theorem jStepHyps {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} :
    JStepHyps (L := L) arI AR th where
  restart := fun s a σ ct x s1 hcur hk htcb hrun hs1 Z H Cs Ac Lst D hth J hX1 => by
    subst hth
    obtain ⟨Lst', R⟩ := jowes_restartD arI s a σ ct x s1 hcur hk htcb hrun hs1 J hX1
    exact ⟨Ac, Lst', R⟩
  ks := fun s s' a a' σ σ' hw hO _ _ _ _ _ _ => jowes_ksD arI s s' a a' σ σ' hw hO
  slot := fun s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw _ hFI hMO _ hTK hT3 hDL hDl =>
    (jowes_ins arI s s' a σ σ' c ps pd rs rd idxs idxd hps hpd hci hld hcap hnull hnu hw hFI hMO hTK hT3 hDL hDl)
  sched := fun s s' a σ σ' hS => jowes_sched arI s s' a σ σ' hS
  cslot := fun s s' a σ σ' G' hcn hkc hCK hUK horig hw _ hFI hMO _ hTK hT3 hkz hDl W hW hcW hoW hUS =>
    (jowes_cn arI s s' a σ σ' hcn hkc hCK hUK horig hw hFI hMO hkz hTK hT3 hDl W hW hcW hoW hUS)

end

end

end Fl4Proofs.P3
