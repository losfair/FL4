/-
P3 (DESIGN.md §9), TCB invocations: **the IPC-buffer step at `XTop`**
(TcbCaps' `BufHypW` at `WX`, for SetIPCBuffer and Configure).

* `TcbBufStep`: a spec step changing TCBs in their `tcb_ipc_buffer` only;
  the scheduler, endpoint and notification relations and `TopSR` across it
  (none reads the field), `XTopAt.bufSpec`.
* `XTopAt.bufWr`: FL4's write of a TCB's IPC-buffer word (`t + 3512`, read
  by none of the relations), the spec state kept.
* `bufWordRel_setIpc`: the step establishes `BufWordRel` (IpcBuf) for the
  target, from it for the others (for the final fold, where `BufWordRel`
  becomes a field of `XTopAt`).
* `bufHypW_X`: `BufHypW` at `WX`: the buffer word and `thread_set` by the
  two steps above; the tail's `reschedule_required` as a scheduler step
  (DomSched's machinery), given `ActReady` at `WX`.
-/
import Fl4Proofs.P3.XTopTcbCtl
import Fl4Proofs.P3.IpcBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc Fl4Proofs.P3.Endp

noncomputable section

/-- **A spec step changing TCBs in their IPC buffer only**: `σ` is `σ'` with
another heap, which agrees with `σ'`'s but at TCBs that differ only in
`tcb_ipc_buffer`. -/
def TcbBufStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ k, σ = { σ' with kheap := k } ∧ ∀ p, σ'.kheap p = k p ∨
    ∃ x b m f, k p = some (.tcb x) ∧
      σ'.kheap p = some (.tcb { x with tcbIpcBuffer := b, tcbMcpriority := m, tcbFlags := f })

theorem TcbBufStep.szKeep {σ σ' : Fl4Spec.State Unit} (h : TcbBufStep σ σ') : Sched.SzKeep σ σ' := by
  obtain ⟨k, rfl, hk⟩ := h
  intro p x n hp
  rcases hk p with e | ⟨y, b, m, f, -, h2⟩
  · exact ⟨x, by change k p = _; rw [← e]; exact hp⟩
  · rw [h2] at hp; cases hp

theorem TcbBufStep.keep {σ σ' : Fl4Spec.State Unit} (h : TcbBufStep σ σ') {p : Fl4Spec.ObjRef}
    {o : Fl4Spec.KernelObject} (hp : σ.kheap p = some o) (ho : ∀ x, o ≠ .tcb x) : σ'.kheap p = some o := by
  obtain ⟨k, rfl, hk⟩ := h
  rcases hk p with e | ⟨y, b, m, f, h1, -⟩
  · rw [e]; exact hp
  · change k p = some o at hp
    rw [hp] at h1; cases h1; exact absurd rfl (ho y)

theorem TcbBufStep.tcb {σ σ' : Fl4Spec.State Unit} (h : TcbBufStep σ σ') {p : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ b m f, σ'.kheap p = some (.tcb { x with tcbIpcBuffer := b, tcbMcpriority := m, tcbFlags := f }) := by
  obtain ⟨k, rfl, hk⟩ := h
  change k p = some (.tcb x) at hp
  rcases hk p with e | ⟨y, b, m, f, h1, h2⟩
  · exact ⟨x.tcbIpcBuffer, x.tcbMcpriority, x.tcbFlags, by rw [e, hp]⟩
  · rw [hp] at h1; cases h1; exact ⟨b, m, f, h2⟩

theorem TcbBufStep.ksub {σ σ' : Fl4Spec.State Unit} (h : TcbBufStep σ σ') : KSub σ σ' := by
  have hT := h
  obtain ⟨k, rfl, hk⟩ := hT
  intro o
  refine ⟨fun r cs ho hw => ⟨cs, ?_, hw⟩, fun t ho => ?_, fun ho => ?_⟩
  · rcases hk o with e | ⟨y, b, m, f, -, h2⟩
    · rw [e] at ho; exact ho
    · rw [h2] at ho; cases ho
  · rcases hk o with e | ⟨y, b, m, f, h1, -⟩
    · rw [e] at ho; exact ⟨t, ho⟩
    · exact ⟨y, h1⟩
  · rcases hk o with e | ⟨y, b, m, f, h1, -⟩
    · rw [e]; exact ho
    · change k o = none at ho; rw [ho] at h1; cases h1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem SchedRel.bufFrame {s : S} {σ σ' : Fl4Spec.State Unit} (hS : Sched.SchedRel st N T C c s σ)
    (h : TcbBufStep σ σ') : Sched.SchedRel st N T C c s σ' := by
  have hz := h.szKeep
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, Sched.scOut_transfer rfl hz hS.scOut,
    Sched.scDisj_transfer hz hS.scDisj, hS.actW, hS.act, hS.repr, hS.core, Q, R0, hc, ?_⟩
  refine ⟨fun p hp => hs.rq p hp, fun d p hd => hs.rqDom d p hd, hs.rel, hs.curThread, hs.curSc,
    hs.curTime, hs.consumed, hs.curDom, fun t ht => ?_, hs.scMem, fun sc hsc => ?_, hs.idleSc, hs.domTime,
    hs.idleTh⟩
  · obtain ⟨x, hk, h1⟩ := hs.tcb t ht
    obtain ⟨b, m, f, hk'⟩ := h.tcb hk
    exact ⟨_, hk', h1⟩
  · obtain ⟨x, n, hk, e⟩ := hs.scs sc hsc
    exact ⟨x, n, h.keep hk (fun _ e => by cases e), e⟩

theorem EpStateRel.bufFrame {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hR : Endp.EpStateRel T E R B m σ)
    (h : TcbBufStep σ σ') : Endp.EpStateRel T E R B m σ' := by
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, fun wp hw => hR.buf wp hw⟩
  · obtain ⟨x, hk, h1⟩ := hR.ep e he
    exact ⟨x, h.keep hk (fun _ e => by cases e), h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.reply r hr
    exact ⟨x, h.keep hk (fun _ e => by cases e), h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    obtain ⟨b, m, f, hk'⟩ := h.tcb hk
    exact ⟨_, hk', { h1 with }⟩

theorem NtfnStateRel.bufFrame {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hR : Notif.NtfnStateRel N T m σ)
    (h : TcbBufStep σ σ') : Notif.NtfnStateRel N T m σ' := by
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hk, h1⟩ := hR.ntfn n hn
    exact ⟨x, h.keep hk (fun _ e => by cases e), h1⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    obtain ⟨b, m, f, hk'⟩ := h.tcb hk
    exact ⟨_, hk', { h1 with }⟩

theorem OObj.of_bufStep {s : S} {σ σ' : Fl4Spec.State Unit} (h : TcbBufStep σ σ') {a : U64}
    (ho : OObj st N T C E R B c s σ' a) : OObj st N T C E R B c s σ a := by
  unfold OObj at ho ⊢
  rcases ho with h' | h' | h' | h' | h' | h' | ⟨sc, hsc, x, n, hk, ho⟩ | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))))
  obtain ⟨x0, hx0⟩ := h.szKeep _ _ _ hk
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x0, n, hx0, ho⟩))))))

/-- **The composite `SR` across an IPC-buffer-only spec step.** -/
theorem TopSR.bufStep {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {s : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (h : TcbBufStep σ σ') :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ' := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  exact ⟨⟨SchedRel.bufFrame hSch h, EpStateRel.bufFrame hEp h, NtfnStateRel.bufFrame hNt h,
    ⟨fun i hi => hIrq.st i hi, fun i hi => hIrq.node i hi⟩, fun p hp => hIo p hp,
    by unfold KRootRel globCr3 at hKr ⊢; exact hKr, hAr⟩,
    ⟨hP.ep, hP.vs, hP.pt, hP.pl, fun x hx => hP.disj x (OObj.of_bufStep h hx), hP.nodeE,
      hP.po, hP.ps, hP.pv, hP.vo, hP.sd, hP.tko⟩⟩

/-- `StateRel` across an IPC-buffer-only spec step (it reads the TCBs' caps). -/
theorem StateRel.bufStep {th : TypedHeap} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hR : StateRel th m σ)
    (h : TcbBufStep σ σ') : StateRel th m σ' := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hk, h1, h2⟩ := hR.cnode p r hp
    exact ⟨cs, h.keep hk (fun _ e => by cases e), h1, h2⟩
  · obtain ⟨x, hk, h1⟩ := hR.tcb t ht
    obtain ⟨b, m, f, hk'⟩ := h.tcb hk
    exact ⟨_, hk', h1⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across an IPC-buffer-only spec step**, FL4's state kept. -/
theorem XTopAt.bufSpec {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (h : TcbBufStep σ σ') : XTopAt (L := L) AR Z s a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, ⟨hSt, hV, hM, hC, hI⟩, hFI, hD, hMO, hIA, hSA⟩, -, hE⟩ := hX
  have hS' := TopSR.bufStep hS h
  have hSz := h.szKeep
  have hK := h.ksub
  have hkeep : ∀ q : Fl4Spec.ObjRef, (∀ x, σ.kheap q ≠ some (.tcb x)) → σ'.kheap q = σ.kheap q := by
    intro q hq
    cases e : σ.kheap q with
    | none => exact (hK q).2.2 e
    | some o => exact h.keep e (fun x ex => hq x (by rw [e, ex]))
  have hT := h
  obtain ⟨k, rfl, -⟩ := hT
  refine ⟨⟨hS', ?_, ?_, hPI, hCO⟩, ⟨hPl, ⟨hSt.bufStep h, hV, hM, ⟨hC.cdt, hC.cdt_slot, hC.orig, hC.par_slot⟩, hI⟩, ⟨hFI.kt.sub hK, hFI.fm⟩, hD, hMO,
    hIA, hSA.mono hSz⟩, IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono rfl hSz⟩
  · refine hR.frame (fun _ _ => rfl) rfl fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact hkeep _ (fun x h => by rw [hf] at h; cases h)
  · refine hPt.frame (fun _ _ => rfl) fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq
      exact hkeep _ (fun x h => by rw [hg] at h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq
      exact hkeep _ (fun x h => by rw [hg] at h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq
      exact hkeep _ (fun x h => by rw [hg] at h; cases h)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq
      exact hkeep _ (fun x h => by rw [hg] at h; cases h)

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 8000000 in
/-- **`XTopAt` across FL4's write of a TCB's `MCP` (`t + 3440`), flags
(`t + 3456`), IPC-buffer (`t + 3512`) or debug (`t + 448`..`t + 504`) word**,
read by none of the relations, the spec state kept. -/
theorem XTopAt.tcbWrA {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64) (Kv : Nat)
    (hKw : Kv = 3440 ∨ Kv = 3512 ∨ (448 ≤ Kv ∧ Kv < 512 ∧ Kv % 8 = 0) ∨ Kv = 3456) (hwav : wa.val = t.val + Kv)
    (v : U64) :
    XTopAt (L := L) AR Z (L.wr s (wa) v) a σ := by
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT := hc.tcbs
  have hta := hT t ht
  have hP := hX.fin.1.2
  have hPe := hP.ep
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut t ht
  have hwv : wa.val = t.val + Kv := hwav
  have hwa : P1.Aligned (wa) := by unfold P1.Aligned; rw [hwv]; have := hta.align; omega
  have hw : P1.WritesIn st s (L.wr s (wa) v) (· = wa) := P1.writesIn_wr hwa
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ t.val + Kv →
      L.mem (L.wr s (wa) v) b = L.mem s b := fun b hb hbv =>
    hw.mem_eq hb fun e => hbv (by rw [e, hwv])
  -- the scheduler relation
  have hN := hc.node
  have hnd := hN.disj t ht
  have hSA : Sched.SAgree st Z.T Z.C Z.c s (L.wr s (wa) v) := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ _ => hne _ (P1.nodeAt_aligned hN ho h8) ?_, fun y hy K hK => ?_,
      hne _ ?_ ?_, hne _ ?_ ?_, fun sc hsc b hb hin => hne _ hb ?_⟩
    · rw [P1.nodeAt_val hN ho]; omega
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      refine hne _ (P1.field_aligned (hT y hy) h1 h2) ?_
      rw [Notif.tfield_val (hT y hy) h1]
      by_cases e : y = t
      · subst e; rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
      · have := tcb_disj hPe ht hy e; omega
    · unfold Sched.curDomA; unfold P1.Aligned
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.curDomA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.dtA; unfold P1.Aligned
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.dtA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · have := (hSch.scOutIn hsc hin).2.2.1 t ht; omega
  have hSch' : Sched.SchedRel st Z.N Z.T Z.C Z.c (L.wr s (wa) v) σ := by
    refine hSch.of_sagree hSA ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hne _ (P1.nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
        (by rw [P1.nodeAt_val hN (by simp [layout.node.SCHED_ACTION])]; simp only [layout.node.SCHED_ACTION]; simp; omega)
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hne _ (P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
        (by rw [P1.nodeAt_val hN (by simp [layout.node.REPROGRAM])]; simp only [layout.node.REPROGRAM]; simp; omega)
  refine hX.frameStep hw (fun b hb => by subst hb; exact Or.inr (Or.inr (Or.inl ⟨t, ht, by omega, by omega⟩)))
    (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_) rfl rfl rfl rfl rfl rfl rfl hSch' ?_ ?_ ?_
    hX.fin.1.1.2.2.2.2.2.2
  · -- not read by the endpoint relation
    subst hb
    rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨y, hy, h | h⟩ | ⟨wp, hwp, h⟩
    · have := hPe.et e he t ht; omega
    · have := hPe.rt r hr t ht; omega
    · obtain ⟨h1, h2⟩ := h
      unfold Endp.TOffN at h2
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
    · unfold Endp.TL at h
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
    · have := hPe.bt wp hwp t ht; rw [← h] at this; omega
  · -- not read by the notification relation
    subst hb
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨y, hy, h⟩
    · have := hSch.placed.disj n hn t ht; omega
    · have hv := nfootT_val (hT y hy) h
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := congrArg UScalar.val hb
    rw [hkv, hwv] at this; omega
  · -- the IRQ relation
    have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)]
    exact hI.st i hi
  · -- the IO-port relation
    have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)]
    exact hI p hp
  · -- the domain schedule
    refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)



/-- `XTopAt.tcbWrA` at `t + K`. -/
theorem XTopAt.tcbWr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) (Kw : U64)
    (hKw : Kw.val = 3440 ∨ Kw.val = 3512 ∨ (448 ≤ Kw.val ∧ Kw.val < 512 ∧ Kw.val % 8 = 0) ∨ Kw.val = 3456) (v : U64) :
    XTopAt (L := L) AR Z (L.wr s (core.num.U64.wrapping_add t Kw) v) a σ := by
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  exact hX.tcbWrA ht _ Kw.val hKw (Notif.tfield_val (hc.tcbs t ht) (by omega)) v

/-- `XTopAt.tcbWr` at the IPC-buffer word. -/
theorem XTopAt.bufWr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) (v : U64) :
    XTopAt (L := L) AR Z (L.wr s (Endp.tIpcBufA t) v) a σ :=
  hX.tcbWr ht 3512#u64 (Or.inr (Or.inl rfl)) v
end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem set_ipc_buffer_wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_ipc_buffer st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3512#u64) v ⦄ := by
  unfold obj.Tcb.set_ipc_buffer layout.tcb.IPC_BUFFER layout.tcb.F
  step as ⟨i, hi⟩
  simp only [lift, bind_ok]
  refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s' e => ?_
  rw [e]; congr 2
  apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, hi]

/-- The spec's `thread_set` of the IPC buffer, as an IPC-buffer-only step. -/
theorem tcbBufStep_upd {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (b : Fl4Spec.VSpaceRef) :
    TcbBufStep σ (Notif.updK σ p (.tcb { x with tcbIpcBuffer := b })) := by
  refine ⟨σ.kheap, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; right; exact ⟨x, b, x.tcbMcpriority, x.tcbFlags, hk, by simp [Notif.updK]⟩
  · left; simp [Notif.updK, Function.update_of_ne e]

/-- The spec's `thread_set` of the MCP, as such a step. -/
theorem tcbFlagsStep_upd {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (f : Fl4Spec.TcbFlags) :
    TcbBufStep σ (Notif.updK σ p (.tcb { x with tcbFlags := f })) := by
  refine ⟨σ.kheap, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; right; exact ⟨x, x.tcbIpcBuffer, x.tcbMcpriority, f, hk, by simp [Notif.updK]⟩
  · left; simp [Notif.updK, Function.update_of_ne e]

/-- The spec's `thread_set` of the MCP, as such a step. -/
theorem tcbMcpStep_upd {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (m : Fl4Spec.Priority) :
    TcbBufStep σ (Notif.updK σ p (.tcb { x with tcbMcpriority := m })) := by
  refine ⟨σ.kheap, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; right; exact ⟨x, x.tcbIpcBuffer, m, x.tcbFlags, hk, by simp [Notif.updK]⟩
  · left; simp [Notif.updK, Function.update_of_ne e]

/-- **The IPC-buffer step establishes `BufWordRel`** (IpcBuf) at the target
and keeps it at the other TCBs: FL4's word is the address written, the spec's
`tcb_ipc_buffer` its value. -/
theorem bufWordRel_setIpc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) (h : BufWordRel Z.T (L.mem s) σ) :
    BufWordRel Z.T (L.mem (L.wr s (tIpcBufA t) v)) (Notif.updK σ t.bv (.tcb { x with tcbIpcBuffer := v.bv })) := by
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hT := hc.tcbs
  have hPe := hX.fin.1.2.ep
  have hal : ∀ u ∈ Z.T, P1.Aligned (tIpcBufA u) := fun u hu => by
    unfold P1.Aligned; rw [show (tIpcBufA u).val = u.val + 3512 from Notif.tfield_val (hT u hu) (by decide)]
    have := (hT u hu).align; omega
  intro u hu
  rw [L.mem_wr _ _ _ _ (hal t ht) (hal u hu)]
  by_cases e : u = t
  · subst e
    exact ⟨{ x with tcbIpcBuffer := v.bv }, by simp [Notif.updK], by rw [if_pos rfl]⟩
  · obtain ⟨y, hy, hb⟩ := h u hu
    have hne : u.bv ≠ t.bv := fun h' => e (P1.eq_of_bv h')
    have hne' : tIpcBufA t ≠ tIpcBufA u := by
      intro h'
      have := congrArg UScalar.val h'
      rw [show (tIpcBufA t).val = t.val + 3512 from Notif.tfield_val (hT t ht) (by decide),
        show (tIpcBufA u).val = u.val + 3512 from Notif.tfield_val (hT u hu) (by decide)] at this
      have := tcb_disj hPe ht hu e; omega
    refine ⟨y, by simp [Notif.updK, Function.update_of_ne hne, hy], ?_⟩
    rw [if_neg hne']; exact hb

/-- **`BufHypW` at `WX`**: the IPC-buffer word and `thread_set`
(`XTopAt.bufWr`, `XTopAt.bufSpec`), and the tail's `reschedule_required` of
the current thread as a scheduler step (`schedStep_resched`), given the
spec's `ActReady` at every `WX` state [J]. -/
theorem bufHypW_X {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {t : U64} (ht : th t = some .tcb)
    (hA : ∀ s a σ G, WX (L := L) AR th s a σ G → Notif.ActReady σ) (addr : U64) (ptr : Fl4Spec.VSpaceRef) :
    BufHypW (L := L) (WX (L := L) AR th) th t addr ptr := by
  refine ⟨fun s a σ G _ hW => ?_, fun s a σ G _ hW => ?_⟩
  · obtain ⟨Z, rfl, rfl, hX, hK, hTh⟩ := hW
    have htT := hTh t ht
    obtain ⟨Q, R0, hc, hs⟩ := hX.fin.1.1.1.lists
    obtain ⟨x, hk, -⟩ := hs.tcb t htT
    have hta := hc.tcbs t htT
    have hwa : P1.Aligned (tIpcBufA t) := by
      unfold P1.Aligned; rw [show (tIpcBufA t).val = t.val + 3512 from Notif.tfield_val hta (by decide)]
      have := hta.align; omega
    refine WP.spec_mono (set_ipc_buffer_wr s t addr) ?_
    rintro s' rfl
    have hstep := tcbBufStep_upd hk ptr
    have hX2 := (hX.bufWr htT addr).bufSpec hstep
    refine ⟨hX.slotsSame_of (P1.writesIn_wr hwa) (fun b hb => by subst hb; exact tcb_oobj htT hta (by decide) (by decide)),
      _, ?_, hX2.rel.2.1, hstep.ksub, Z, rfl, rfl, hX2, by rw [L.ksb_wr]; exact hK, hTh⟩
    rw [Notif.threadSet_eq _ hk]; rfl
  · obtain ⟨Z, rfl, rfl, hX, hK, hTh⟩ := hW
    have hW0 : WX (L := L) AR Z.th s a σ Z.G := ⟨Z, rfl, rfl, hX, hK, hTh⟩
    have hS := hX.fin.1.1.1
    obtain ⟨Q, R0, hc, hs⟩ := hS.lists
    have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
      rw [hs.curThread, hc.cur]; rfl
    rw [cur_thread_eq]
    simp only [bind_ok, tcb_eq_ct]
    by_cases e : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    · simp only [e, decide_true, ↓reduceIte]
      have hA1 := hA s a σ Z.G hW0
      obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA1
      have hN := hX.fin.1.1.2.2.1
      refine WP.spec_bind (WP.spec_and (WP.spec_and (Sched.reschedule_required_refines s _ hN hS hA1)
        (Sched.reschedule_required_sfootI hS)) (spec_self (Sched.reschedule_required_sfootI hS))) ?_
      rintro s5 ⟨⟨⟨σ3, he3, -, -, -, -⟩, hw⟩, hrun5⟩
      rw [hres] at he3
      have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
      subst σ3
      have hX5 := hX.schedStep hK hTh (schedStep_resched hA1 hrun5 hres hK' hdl' hds')
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, hX.slotsSame_of hw (fun b hb => sfootI_oobj hc.tcbs hb), σ', ?_, hX5.rel.2.1,
        KSub.of_kheap hK'.kh, Z, rfl, rfl, hX5, by rw [hw.1]; exact hK, hTh⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : t.bv = σ.curThread := by rw [hcur, e]
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ')) (by rw [hres]; rfl)
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨trivial, trivial, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, σ, ?_, hX.rel.2.1, KSub.refl σ, Z, rfl, rfl, hX, hK, hTh⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : ¬ t.bv = σ.curThread := fun h => e (P1.eq_of_bv (h.trans hcur))
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ)) rfl

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **TcbXLeaves' SetIPCBuffer at `XTop`** with the IPC-buffer step
discharged (`bufHypW_X`), given `ActReady` at `WX` [J]. -/
theorem tcb_set_ipcXT [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetIPCBuffer p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer :=
  tcb_set_ipcX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp (fun v => bufHypW_X hp hA v v.bv) slbl hlbl length
    buf ct hct args hlen hargs hcur hact hstall call ssl hAs extra x0 x1 x2 hx0 excaps hXc hnc blk don ci buffer

/-- **TcbXLeaves' Configure at `XTop`** with the IPC-buffer step discharged. -/
theorem tcb_configureXT [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBConfigure p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer :=
  tcb_configureX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp (fun v => bufHypW_X hp hA v v.bv) slbl hlbl length
    buf ct hct args hlen hargs hcur hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci
    buffer

end

end

end Fl4Proofs.P3
