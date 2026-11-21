/-
P3 (DESIGN.md §9), CSpace: **`unbind_reply` of an SC at `J`** (a step of a
final SC cap's finalisation, XTopJointFinSc's `JAtZ.finScJ`):
`JAtZ.unbindReplyJ`.

The spec's `sched_context_unbind_reply` clears the head reply's `SC` link
and the SC's call stack: a frame `RFr` (only a reply changes, or an SC's
`sc_replies` becomes empty; nothing else), which keeps `CurInv`, `CurOwnW`,
`OffOK`, `BlockedScActive`, `CurRunM` and the links (`LK`).

FL4's side (XTop's `unbind_reply_refines`): the call stacks, `RPlaced`,
`RFree` and `ActIdle` after; its writes are the head reply's `NEXT` word and
the SC's `REPLY` word (`RW`, inside `UFoot`, outside `TFoot`), so the
generic SC-step frame is used through variants taking the kernel-state base
and the slots kept (`JAtZ.sc_frameS`, `sc_jcovS`, `sc_kernW`, `sc_utcR`,
`deadP_stepG`): the slots and the IRQ handler slots by `slotsSame_of_ufoot`
and `irq_of_ufoot`, `XTopAt` by `xtop_sc_stepCW`, yield and MCP by
`ScAll.of_u`, the buffer words by `callW'_nobuf`, P1's `BlkOK` by
`unbind_reply.blk`; a dead SC's `REPLY` word stays null through the call
stacks before and after (`RFr`: an SC's stack never grows).
-/
import Fl4Proofs.P3.XTopJointFinScNtfn
import Fl4Proofs.P3.ScDecodeAll
import Fl4Proofs.P3.XTopFinSc
import Fl4Proofs.P3.IpcRemove
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

section Spec

/-- **The spec's frame of `sched_context_unbind_reply`** (module docstring). -/
structure RFr (σ σ' : State Unit) : Prop where
  st : ∃ k, σ' = { σ with kheap := k }
  kh : ∀ q, σ'.kheap q = σ.kheap q ∨ (∃ x x', σ.kheap q = some (.reply x) ∧ σ'.kheap q = some (.reply x')) ∨
    (∃ y n, σ.kheap q = some (.schedContext y n) ∧ σ'.kheap q = some (.schedContext { y with scReplies := [] } n))

variable {σ σ' : State Unit}

theorem RFr.ct (h : RFr σ σ') : σ'.curThread = σ.curThread := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.csc (h : RFr σ σ') : σ'.curSc = σ.curSc := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.idle (h : RFr σ σ') : σ'.idleThread = σ.idleThread := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.isc (h : RFr σ σ') : σ'.idleSc = σ.idleSc := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.rel (h : RFr σ σ') : σ'.releaseQueue = σ.releaseQueue := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.cons (h : RFr σ σ') : σ'.consumedTime = σ.consumedTime := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.tm (h : RFr σ σ') : σ'.curTime = σ.curTime := by obtain ⟨k, rfl⟩ := h.st; rfl
theorem RFr.act (h : RFr σ σ') : σ'.schedulerAction = σ.schedulerAction := by obtain ⟨k, rfl⟩ := h.st; rfl

theorem RFr.tcbF (h : RFr σ σ') {q : ObjRef} {x : Tcb} (hq : σ.kheap q = some (.tcb x)) :
    σ'.kheap q = some (.tcb x) := by
  rcases h.kh q with e | ⟨_, _, e, -⟩ | ⟨_, _, e, -⟩
  · rw [e, hq]
  all_goals (rw [hq] at e; cases e)

theorem RFr.tcbB (h : RFr σ σ') {q : ObjRef} {x : Tcb} (hq : σ'.kheap q = some (.tcb x)) :
    σ.kheap q = some (.tcb x) := by
  rcases h.kh q with e | ⟨_, _, -, e⟩ | ⟨_, _, -, e⟩
  · rw [← e, hq]
  all_goals (rw [hq] at e; cases e)

theorem RFr.scF (h : RFr σ σ') {q : ObjRef} {y : SchedContext} {n : Nat} (hq : σ.kheap q = some (.schedContext y n)) :
    σ'.kheap q = some (.schedContext y n) ∨ σ'.kheap q = some (.schedContext { y with scReplies := [] } n) := by
  rcases h.kh q with e | ⟨_, _, e, -⟩ | ⟨y0, n0, e, e'⟩
  · exact Or.inl (by rw [e, hq])
  · rw [hq] at e; cases e
  · rw [hq] at e; cases e; exact Or.inr e'

theorem RFr.scB (h : RFr σ σ') {q : ObjRef} {z : SchedContext} {n : Nat} (hq : σ'.kheap q = some (.schedContext z n)) :
    ∃ y, σ.kheap q = some (.schedContext y n) ∧ (z = y ∨ z = { y with scReplies := [] }) := by
  rcases h.kh q with e | ⟨_, _, -, e⟩ | ⟨y0, n0, e, e'⟩
  · exact ⟨z, by rw [← e, hq], Or.inl rfl⟩
  · rw [hq] at e; cases e
  · rw [hq] at e'; cases e'; exact ⟨y0, e, Or.inr rfl⟩

theorem RFr.lk (h : RFr σ σ') : LK (fun _ => False) σ σ' := fun q => Or.inr (by
  rcases h.kh q with e | ⟨x, x', e1, e2⟩ | ⟨y, n, e1, e2⟩
  · rw [e]; exact OL.refl _
  · rw [e1, e2]; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
  · rw [e1, e2]; exact LObj.sc (Or.inl rfl) (Or.inl rfl))

theorem RFr.fk (h : RFr σ σ') : FK σ σ' := ⟨h.csc, h.idle, h.isc⟩

theorem RFr.curInv (h : RFr σ σ') (hC : CurInv σ) : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
  obtain ⟨x, n, hx⟩ := hC.sc
  refine ⟨⟨xt, by rw [h.ct]; exact h.tcbF hkt, by rw [h.csc]; exact hxs, hnb⟩, ?_, fun hne y m hy => ?_,
    by rw [h.ct, h.rel]; exact hC.notRel⟩
  · rcases h.scF hx with e | e
    · exact ⟨x, n, by rw [h.csc]; exact e⟩
    · exact ⟨_, n, by rw [h.csc]; exact e⟩
  · rw [h.csc, h.isc] at hne; rw [h.csc] at hy
    obtain ⟨y0, hy0, e | e⟩ := h.scB hy <;> subst e
    · exact hC.active hne _ m hy0
    · exact hC.active hne y0 m hy0

theorem RFr.own {T C : Set U64} (h : RFr σ σ') (hO : CurOwnW T C σ) : CurOwnW T C σ' := by
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
  · refine Or.inl ⟨u, hu, xt, h.tcbF hkt, by rw [h.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [h.csc] at hy
      obtain ⟨y0, hy0, e | e⟩ := h.scB hy <;> subst e
      · exact hown _ n hy0
      · exact hown y0 n hy0
    · rw [h.cons] at h0; rw [h.rel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨by rw [h.csc]; exact hcs, fun y n hy => ?_⟩
    rw [h.csc] at hy
    obtain ⟨y0, hy0, e | e⟩ := h.scB hy <;> subst e
    · exact hun _ n hy0
    · exact hun y0 n hy0

theorem RFr.off (h : RFr σ σ') (hO : OffOK σ) : OffOK σ' := by
  intro hc y n hy ha
  rw [h.cons] at hc ⊢; rw [h.tm]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  obtain ⟨y0, hy0, e | e⟩ := h.scB hy <;> subst e
  · exact hO hc _ n hy0 ha
  · exact hO hc y0 n hy0 ha

theorem RFr.bsa (h : RFr σ σ') (hB : BlockedScActive σ) : BlockedScActive σ' := by
  refine ⟨fun p z n t x hp hyt hx hq => ?_, fun p z n hp hr => ?_⟩
  · obtain ⟨y0, hy0, e | e⟩ := h.scB hp <;> subst e
    · exact hB.tcb p _ n t x hy0 hyt (h.tcbB hx) hq
    · exact hB.tcb p y0 n t x hy0 hyt (h.tcbB hx) hq
  · obtain ⟨y0, hy0, e | e⟩ := h.scB hp <;> subst e
    · exact hB.replies p _ n hy0 hr
    · exact absurd rfl hr

theorem RFr.curRun (h : RFr σ σ') (hR : CurRunM σ) : CurRunM σ' := by
  rcases hR with e | e | e
  · exact Or.inl (by rw [h.act]; exact e)
  · exact Or.inr (Or.inl fun x hx => e x (h.tcbB (by rw [← h.ct]; exact hx)))
  · exact Or.inr (Or.inr (by rw [h.ct, h.idle]; exact e))

/-- **The spec's `sched_context_unbind_reply`** is in the frame `RFr` (its
head reply an object of the spec). -/
theorem unbindReply_rfr {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n))
    (hr : ∀ r, y.scReplies.head? = some r → ∃ x, σ.kheap r = some (.reply x))
    (he : schedContextUnbindReply (Z := Unit) p σ = ({((), σ')}, False)) : RFr σ σ' := by
  have hsp : schedContextUnbindReply (Z := Unit) p σ = (NonDet.unless (y.scReplies = []) (do
      setReplyObjRef replyScUpdate (the y.scReplies.head?) none
      setScObjRef scRepliesUpdate p [])) σ := by
    unfold schedContextUnbindReply
    rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _)]
  cases hy : y.scReplies with
  | nil =>
    have e0 : schedContextUnbindReply (Z := Unit) p σ = ({((), σ)}, False) := by rw [hsp, hy]; rfl
    have := the_result e0 he
    subst this
    exact ⟨⟨_, rfl⟩, fun _ => Or.inl rfl⟩
  | cons r rest =>
    obtain ⟨x, hkr⟩ := hr r (by rw [hy]; rfl)
    have hpr : p ≠ r := fun e => by rw [e, hkr] at hk; cases hk
    have hk1 : (updK σ r (.reply { x with replySc := none })).kheap p = some (.schedContext y n) := by
      simp [updK, hpr, hk]
    have he2 : schedContextUnbindReply (Z := Unit) p σ =
        ({((), updSc (updK σ r (.reply { x with replySc := none })) p { y with scReplies := [] } n)}, False) := by
      rw [hsp, hy]
      unfold NonDet.unless
      rw [if_neg (by simp)]
      simp only [List.head?_cons, the]
      rw [nd_bind_one (setReplySc_eq none hkr)]
      exact updateSchedContext_eq hk1 _
    have := the_result he2 he
    subst this
    refine ⟨⟨_, rfl⟩, fun q => ?_⟩
    by_cases e1 : q = p
    · subst e1; exact Or.inr (Or.inr ⟨y, n, hk, by simp [updK]⟩)
    · by_cases e2 : q = r
      · subst e2; exact Or.inr (Or.inl ⟨x, { x with replySc := none }, hkr, by simp [updK, e1]⟩)
      · exact Or.inl (by simp [updK, e1, e2])

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **`JAtZ.sc_frame` with the kernel-state base and the slots kept as
inputs** (its only uses of the writes). -/
theorem JAtZ.sc_frameS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hks : L.ksb s' = L.ksb s) (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hv : VKeep (L := L) Z.th s s')
    (hK : Sched.ScTKw P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hrr : Sched.RRecv (L.mem s') Z.R σ')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ')
    (hown : Sched.CurOwnW Z.T Z.C σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hcr : CurRunM σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl' : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.tkw hK) hblk J.hset.2.1 hjpl J.c0
  have hsv : Sched.SchedValid σ' := schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.tkw hK) hblk J.hset.1
    J.hset.2.1 hcall hyl J.c0 hinv hsl
  refine ⟨hX, hcall, hrf, hrr, hyl, hmcp, hbuf, by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, hjpl, J.cover.tkw hK, J.obj.tkw hK, J.zH, ?_, J.hset, J.hscC, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, hcur, hown, hoff, hact,
    J.c0, hbsa, hsv, J.isorted.tkw hK, hsl, hcr, hblk, by rw [hks]; exact J.intL,
    J.vsc.of_eq fun y hy => hSS.capV hy,
    J.bok.keep (IpcFrKeep.of_otk hK.kh), J.fcov.ipcFr (IpcFrKeep.of_otk hK.kh),
    J.fcap.keepU (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (IpcFrKeep.of_otk hK.kh).page,
    J.ext.ss hSS hv,
    J.liveX hX rfl rfl rfl hSS hKd hK.orig hidl (fun p hp => hjc.dead p (hDD p hp)), J.zDX hSS hDD⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hK.ksz
    rw [← hSS.capV (hsl' x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)


/-- **`JKern` after a step** writing any words (as `JAtZ.sc_kern`): the current thread and SC words are the
spec's, which the step keeps (`ScTKw`, `FK`); the node-0 `DEBUG_TCBS` word
kept (`hDbg`, P1-supplied); the dead set shrinking. -/
theorem JAtZ.sc_kernW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {P : Fl4Spec.ObjRef → Prop} {D' : Set U64} {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hK : Sched.ScTKw P σ σ') (hF : FK σ σ')
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hD : D' ⊆ D) : JKern (L := L) H Cs D' Z.th s' σ' := by
  have K := J.kern
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hX'.fin.1.1.1.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hK.ct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hF.1]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => K.orig sl (by rw [← hK.orig]; exact h), by rw [ecw, hK.ct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hK.arch]; exact hK.archObj hpt⟩, by rw [hK.arch]; exact K.ga, by rw [hK.arch]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head


/-- **`JCovD` after a step keeping the slots and the base** (as `JAtZ.sc_jcov`), the dead set shrinking to `D'`: the dead
of `D'` dead after (`hdead`), the others of `D` covered after (`hcov`). -/
theorem JAtZ.sc_jcovS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hks : L.ksb s' = L.ksb s) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hdead : ∀ q ∈ D', Sched.DeadP (L := L) H s' q)
    (hcov : ∀ q ∈ D, q ∉ D' →
      (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)))
    (hidl : Sched.IdleKeep (L := L) s s') :
    Sched.JCovD (L := L) Z.th H Z.G D' Cs s' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hk : ∀ y ∈ Z.G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ Z.G.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y :=
    fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩
  have JC := J.jcov
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, hdead,
    JC.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩,
    JC.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩⟩
  · rcases JC.th q k hq with hc | hd | hi
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((hcov q hd h).1 k hq)
    · exact Or.inr (Or.inr ((Sched.exAt_of hidl hks).2 hi))
  · rcases JC.h q k hq with hc | hd | hi
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((hcov q hd h).2 k hq)
    · exact Or.inr (Or.inr ((Sched.exAt_of hidl hks).2 hi))

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a call-stack step** (as `JAtZ.sc_utc`,
FL4 writing replies' `NEXT` words and SCs' `REPLY` words, `RW`; the replies
and SCs are spec objects outside the free parts, `SpecFree`): the caps kept (slots
apart), the free parts zero (no SC-step word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state and
the node-0 `DEBUG_TCBS` word (`hDbg`, P1-supplied). -/
theorem JAtZ.sc_utcR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.RW Z.R Z.C)) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : Sched.ScTKw P σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
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
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [hK.arch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases hb with ⟨r, hr, rfl⟩ | ⟨c, hc', rfl⟩
    · obtain ⟨x, hx, -⟩ := J.call.reply r hr
      have hv := Sched.rNextA_val (J.rp.align r hr)
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) r.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this
      omega
    · obtain ⟨x, n, hk, -⟩ := hs.scs c hc'
      obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hc'
      have := hsz x n hk
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) c.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hK.cdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), by rw [hna, hDbg]; exact r3⟩


set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an SC step**, with the writes' facts given
(as `JAtZ.deadP_sc_step`): a dead SC of `Z.C` keeps its `REPLY` word null
(`hrep`), an SC of `H` outside `Z.C` keeps its words (`hout`). -/
theorem JAtZ.deadP_stepG {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hrep : ∀ q ∈ Z.C, L.mem s (P1.scReplyA q) = 0#u64 → L.mem s' (P1.scReplyA q) = 0#u64)
    (hout : ∀ q z, H q = some (.sc z) → q ∉ Z.C → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K))
    {q : U64} (hYm : YMemDead (L := L) H Z.C s s' q) (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) :
    DeadP (L := L) H s' q := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hS' := hX'.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  have hI' := hX'.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    obtain ⟨y, hy, hso, hst⟩ := hK.tcb hk
    rw [hk'] at hy; cases hy
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    have hstate : x'.tcbState = x.tcbState := by
      rcases hst with e | ⟨hp, -, -⟩
      · exact e
      · exact absurd hst0 (tsCode_ne_of_runnable (hP _ _ hp hk))
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      obtain ⟨y2, hy2, e⟩ := hL.tcb hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_, hYm.1 hq d6⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := by rw [hso]
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW nodeW; rw [hc'.cur]
      rw [← ea, ← e] at hact
      revert hact
      cases hsa : σ'.schedulerAction with
      | resumeCurThread =>
        intro h; simp only [ActRel] at h; subst h
        rw [J.kern.h0] at hq; cases hq
      | chooseNewThread =>
        intro h; simp only [ActRel] at h; subst h
        have := J.kern.heap.align _ _ hq
        simp [P1.HKind.bits] at this
      | switchThread t =>
        intro h; simp only [ActRel] at h
        obtain ⟨-, -, ht⟩ := h
        obtain ⟨x2, scp, -, -, hk2, hsc2, -⟩ := schedulable_inv (hAS t hsa)
        rw [← ht, hk'] at hk2; cases hk2
        rw [hxs'] at hsc2; cases hsc2
    · have ei : L.idleW s' = L.idleW s := by
        unfold P1.LawfulStore.idleW
        apply P1.eq_of_bv
        have h1 := hs'.idleTh; have h2 := hs.idleTh
        unfold nodeW at h1 h2
        rw [hc'.cur, hc.cur, ← h1, ← h2, hF.2.1]
      rw [ei]; exact d5
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    rw [hK.ep hk] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb⟩ := hK.ntfn' hk
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      obtain ⟨y2, hy2, e⟩ := hL.ntfn hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rw [ho] at hO'
      rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hK.reply hk
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3, d4⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hL.sc hW hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_, hYm.2 z hq hqC d4⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · exact hrep q hqC d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb, hout q z hq hqC _ (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', hout q z hq hqC _ (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, hout q z hq hqC _ (by decide) (by decide), scW_ntfn]; exact d3
      · rw [scYieldFromA_eq, hout q z hq hqC _ (by decide) (by decide), ← scYieldFromA_eq]; exact d4

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **`unbind_reply` of an SC at `J`** (module docstring): XTopJointFinSc's
a step of XTopJointFinSc's `JAtZ.finScJ`, proved (for any SC of the SCs, non-null). -/
theorem JAtZ.unbindReplyJD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64) :
    schedcontext.unbind_reply st s p ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindReply (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      JTPD (L := L) arI AR Z H Cs D s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨y, m, hk, -⟩ := hs.scs p hpC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p y m hp0 hk).2⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and (unbind_reply_refines s σ hS hR J.nsc J.inv J.call J.rp hpC hp0 hk J.rfree)
    (P1.schedcontext.unbind_reply.blk s p p J.blk (fun _ => hpS) hpS))
    (unbind_reply_rwords s σ hS J.call J.rp hpC hp0 hk)) ?_
  rintro s' ⟨⟨⟨σ', Lst', he, hS', hR', hN', hI', hCR', hRP', hAI, hRF', hw⟩, hblk, hfoot, -, -⟩, hrw⟩
  -- the spec frame
  have hF : RFr σ σ' := by
    obtain ⟨⟨y1, n1, hk1, hyL⟩, hLR, -, -⟩ := J.call.stack p hpC
    rw [hk] at hk1; cases hk1
    refine unbindReply_rfr hk (fun r hr => ?_) he
    rw [hyL] at hr
    cases e : Lst p with
    | nil => rw [e] at hr; cases hr
    | cons r0 rest =>
      rw [e] at hr
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hr
      subst hr
      obtain ⟨x, hx, -⟩ := J.call.reply r0 (hLR r0 (by rw [e]; simp))
      exact ⟨x, hx⟩
  have hK : ScTKw (fun _ => False) σ σ' :=
    nkt_schedContextUnbindReply p.bv σ ((), σ') (by rw [he]; exact Set.mem_singleton _)
  -- a receiver's reply: unlinked before, its words kept or nulled
  have hRR' : RRecv (L.mem s') Z.R σ' := fun d hd hrd => by
    obtain ⟨h1, h2⟩ := J.rrecv d hd ((KhRB.of_sctkw hK).recvB hrd)
    obtain ⟨e1, e2⟩ := hrw d hd
    exact ⟨e1.elim (fun e => e.trans h1) id, e2.trans h2⟩
  -- FL4's writes
  have hks : L.ksb s' = L.ksb s := hw.1
  have hWC : P1.WritesIn st s s' (fun b => TFoot st Z.T Z.N Z.C Z.c s σ b ∨ CallW' Z.R Z.C b) :=
    hw.mono fun b hb => Or.inr (hb.imp (fun ⟨r, hr, e⟩ => ⟨r, hr, Or.inl e⟩) id)
  have hX' := xtop_sc_stepCW (ct := σ.curThread) J.xtop J.ip J.nk J.ks.rep hWC (hK.mono fun _ h => h.elim)
    hS' hR' id
  have hwR : P1.WritesIn st s s' (RW Z.R Z.C) := hw
  have hwU : P1.WritesIn st s s' (UFoot st Z.T Z.N Z.C Z.R Z.c s σ) := hw.mono fun b hb => Or.inr (Or.inl hb)
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_of_ufoot hJ.pl hS J.rp J.apart hwU
  have hIA := hJ.irqApart (c := Z.c) J.zH.1 J.zH.2.2.2 J.c0 J.zH.2.2.1 J.kern.ksbFit
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hK.szKeep q.bv y n hq) hks (irq_of_ufoot hS J.rp hIA hwU)
      (J.idleW_keep hX'.fin.1.1.1 hF.fk.2.1 hF.fk.2.2).2⟩
  -- yield, MCP, buffer words
  have hsok : SOK (true, false) σ σ' := Pres.of_eq (pres_schedContextUnbindReply p.bv) he
  obtain ⟨-, hY', hM', -, -, -⟩ := ScAll.of_u hS J.rp J.yld J.mcp
    ⟨⟨hS', hR', hN', hI'⟩, hCR', hRP', hRF', hw.mono fun b hb => Or.inr hb⟩ hsok
  have hbuf : BufWordRel Z.T (L.mem s') σ' :=
    J.buf.frame (fun t ht => hw.mem_eq (tIpcBufA_aligned (hc.tcbs t ht)) fun hb =>
      callW'_nobuf J.ip hS (hb.imp (fun ⟨r, hr, e⟩ => ⟨r, hr, Or.inl e⟩) id) t ht rfl) hK.bufKeep
  have hact' : ActIdle σ' := hAI J.act
  -- the dead set
  have hrep : ∀ q ∈ Z.C, L.mem s (P1.scReplyA q) = 0#u64 → L.mem s' (P1.scReplyA q) = 0#u64 := by
    intro q hq h0
    obtain ⟨⟨y1, n1, hk1, hyL1⟩, hLR1, -, hLw1⟩ := J.call.stack q hq
    have hL0 : Lst q = [] := by
      cases e : Lst q with
      | nil => rfl
      | cons r rest =>
        exfalso
        have h1 := hLw1.1
        rw [e] at h1
        have hrR : r ∈ Z.R := hLR1 r (by rw [e]; simp)
        exact (J.rp.align r hrR).2.1 (by simpa using h1.symm.trans h0)
    have hy1 : y1.scReplies = [] := by rw [hyL1, hL0]; rfl
    obtain ⟨⟨y2, n2, hk2, hyL2⟩, -, -, hLw2⟩ := hCR'.stack q hq
    obtain ⟨y0, hk0, hy0⟩ := hF.scB hk2
    rw [hk1] at hk0; cases hk0
    have hy2 : y2.scReplies = [] := by
      rcases hy0 with rfl | rfl
      · exact hy1
      · rfl
    have hL2 : Lst' q = [] := by
      rw [hyL2] at hy2; exact List.map_eq_nil_iff.1 hy2
    rw [hLw2.1, hL2]; rfl
  have hout : ∀ q z, H q = some (.sc z) → q ∉ Z.C → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K) := by
    intro q z hq hqC K hK8 hK128
    have hH := J.kern.heap
    have hal := hH.align q _ hq
    have hfit := hH.fits q _ hq
    have hz := hH.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
    rcases hb with ⟨r, hr, e⟩ | ⟨c, hc', e⟩
    · have hHr : H r = some .reply := J.zH.2.2.1 r hr
      have hne : q ≠ r := fun e' => by rw [e', hHr] at hq; cases hq
      have := hH.disj q _ r _ hq hHr hne
      have hv2 := congrArg UScalar.val e
      rw [hv, Sched.rNextA_val (J.rp.align r hr)] at hv2
      simp only [P1.HKind.bits] at this
      omega
    · obtain ⟨xc, nc, hkc, -⟩ := hs.scs c hc'
      obtain ⟨zc, hHc⟩ : ∃ zc, H c = some (.sc zc) := ⟨_, (hJ.sc c xc nc (J.c0 c hc') hkc).2⟩
      have hzc : 2 ^ 7 ≤ 2 ^ zc := Nat.pow_le_pow_right (by norm_num) (hH.scmin c zc hHc)
      have hne : q ≠ c := fun e' => hqC (e' ▸ hc')
      have := hH.disj q _ c _ hq hHc hne
      obtain ⟨-, hvc, -⟩ := sc_reply_word hS hc'
      have hv2 := congrArg UScalar.val e
      rw [hv, hvc] at hv2
      simp only [P1.HKind.bits] at this
      omega
  have hDead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_stepG hX' hK (fun _ _ h _ => h.elim) hF.lk hF.fk hact'.1 hrep hout
      (J.ymd hX'.fin.1.1.1 hY' ((hsok.ykeep rfl).dk q.bv)) (fun h => h) (J.jcov.dead q hq)
  -- the rest
  have hDbg := J.kw_dbg (hfoot.mono (Set.empty_subset _))
  have hKd := J.kw_dbgKeep (hfoot.mono (Set.empty_subset _))
  exact ⟨σ', he, Z.vs, Ac, Lst', J.sc_frameS hks hSS (J.vkeep_of hwR fun b hb u hu => Sched.RW.ne_tcbw hS J.rp hb hu (K := 3664#u64) (by simp)) hK hX' hCR' hRF' hRR' hY' hM' hbuf hRP'
    (J.apart.sc_frame hks hK.szKeep) hjpl (J.sc_jcovS hks hSS hDead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.fk.2.1 hF.fk.2.2))
    (J.sc_kernW hw hK hF.fk hX' hDbg fun _ h => h) (J.sc_utcR hwR hSS hK hDbg) hN' hI'
    (J.cur.imp (fun e => by rw [hF.act]; exact e) hF.curInv) (hF.own J.own) (hF.off J.off) hact'
    (hF.bsa J.bsa) (hF.curRun J.curRun) hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.fk.2.1 hF.fk.2.2).1 J.zD⟩


set_option maxHeartbeats 4000000 in
/-- `JAtZ.unbindReplyJD` with the dead set existential. -/
theorem JAtZ.unbindReplyJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64) :
    schedcontext.unbind_reply st s p ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindReply (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      JTP (L := L) arI AR Z H Cs s' a σ' ⦄ :=
  WP.spec_mono (J.unbindReplyJD arI hpC hp0) fun _ ⟨σ', he, V, Ac', Lst', J'⟩ => ⟨σ', he, V, Ac', Lst', D, J'⟩

end

end

end Fl4Proofs.P3
