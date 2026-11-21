/-
P3 (DESIGN.md §9), IPC: **`cancel_ipc` of a thread blocked on its reply, at
`J`** (`jCancel_reply`: XTopJointSuspend's `JCancelAt` for the reply state,
toward `suspend` of a final thread cap's thread). Two `J` steps:

* the fault clear (`JAtZ.faultClearJ`): a TCB field write, a register-frame
  step `JAtZ.reg_frameF` (`QKY`), P1's `BlkOK` after by `bxi_field`;
* `reply_remove_tcb` (`JAtZ.replyRemoveTcbJ`, as XTopJointRemove's
  `JAtZ.replyRemoveJ` for `reply_remove`, without the donation): FL4's side
  `Ipc.rrt_topJ` (ScRemoveTcb's `reply_remove_tcb_sc_refines`, then
  `reply_unlink`, with the call stacks and the footprint `KFoot ∨ CallW`, as
  XTopJointRemove's `remove_topJ`), P1's `reply_remove_tcb.kw` (`KW`); the
  spec's `replyRemoveTcbSc` (`rmTcbSc_donV`: an `SVS` step, a `DonV` with no
  donation, `LK` off the cut SC) then `reply_unlink_tcb`; the scheduler
  invariants and the dead as `replyRemoveJ`'s. P1's `BlkOK` after is taken
  from P1's whole-`cancel_ipc` lemma (`cancel_ipc.blk`).
-/
import Fl4Proofs.P3.XTopJointSuspend
import Fl4Proofs.P3.XTopJointRemove
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

/-! ## The spec's `reply_remove_tcb` -/

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

theorem rsf_replyRemoveTcb (t r : ObjRef) : FK rsF (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb getReplyObjRef getSkObjRef; rsf_auto

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3.RelQ
open Fl4Spec

noncomputable section

theorem rq_replyRemoveTcb' (t r : ObjRef) : RQ (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb; rq_auto

end

end Fl4Proofs.P3.RelQ

namespace Fl4Proofs.P3.QPK
open Fl4Spec

noncomputable section

theorem qp_replyRemoveTcb (t r : ObjRef) : QPM (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb; qp_auto

end

end Fl4Proofs.P3.QPK

namespace Fl4Proofs.P3.Sched
open Fl4Spec Fl4Proofs.P3.SVK

noncomputable section

theorem sv_replyRemoveTcbSc (r : ObjRef) : SVM (replyRemoveTcbSc r) := by
  unfold replyRemoveTcbSc; sv_auto

/-- `replyRemoveTcbSc`'s branch with an SC holding the reply. -/
def rrtSome (q r : ObjRef) : SMonad Unit Unit := do
  let scReplies ← NonDet.liftM SchedContext.scReplies (getSchedContext q)
  let replySc ← getReplyObjRef Reply.replySc r
  NonDet.assert (if the scReplies.head? = r then replySc = some q else replySc = none)
  updateSchedContext q (scRepliesUpdate (List.takeWhile fun r' => decide (r' ≠ r)))
  setReplyObjRef replyScUpdate r none

theorem rrt_some {σ : State Unit} {q r : ObjRef} (hw : scWithReply r σ = some q) :
    replyRemoveTcbSc r σ = rrtSome q r σ := by
  unfold replyRemoveTcbSc
  rw [Notif.nd_gets_bind, hw]
  rfl

theorem rrt_none {σ : State Unit} {r : ObjRef} (hw : scWithReply r σ = none) :
    replyRemoveTcbSc r σ = ({((), σ)}, False) := by
  unfold replyRemoveTcbSc
  rw [Notif.nd_gets_bind, hw]
  rfl

theorem lkm_rrtSome (q r t : ObjRef) : LKM (fun p => p = q ∨ p = t) (rrtSome q r) := by
  unfold rrtSome getReplyObjRef getSkObjRef getSimpleKo setReplyObjRef
  repeat' (first
    | exact lkm_getSchedContext _
    | exact lk_updateSchedContextW _ (Or.inl rfl)
    | lkm_step0)

set_option maxHeartbeats 4000000 in
/-- **The call-stack part of `reply_remove_tcb`** (module docstring; as
`rmSc_donV`, no donation). -/
theorem rmTcbSc_donV {σ σ5 : State Unit} {t r : ObjRef} {x0 : Tcb} (hk0 : σ.kheap t = some (.tcb x0))
    (hsp : replyRemoveTcbSc r σ = ({((), σ5)}, False)) :
    ∃ q, (q = t ∨ ∃ y n, σ.kheap q = some (.schedContext y n)) ∧
      (∀ y n, σ.kheap q = some (.schedContext y n) → r ∈ y.scReplies) ∧ DonV t q σ σ5 ∧
      LK (fun p => p = q ∨ p = t) σ σ5 := by
  have hm : ((), σ5) ∈ (replyRemoveTcbSc r σ).1 := by rw [hsp]; rfl
  have hct : σ5.curThread = σ.curThread := (NKT.of_eq (nkt_replyRemoveTcbSc r) hsp).ct
  have hD' : ∀ q, DonV t q σ σ5 := fun q => DonV.ofSVS (sv_replyRemoveTcbSc r σ _ hm) hct
  cases hw : scWithReply r σ with
  | none =>
    rw [rrt_none hw] at hm
    obtain rfl : σ5 = σ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
    exact ⟨t, Or.inl rfl, fun y n h => (by rw [hk0] at h; cases h), hD' t, LK.refl _ _⟩
  | some q =>
    rw [rrt_some hw] at hm
    obtain ⟨yq, nq, hkq, hrq⟩ := scWithReply_mem' hw
    have hQ : ∀ y n, σ.kheap q = some (.schedContext y n) → r ∈ y.scReplies := fun y n h => by
      rw [hkq] at h; cases h; exact hrq
    exact ⟨q, Or.inr ⟨yq, nq, hkq⟩, hQ, hD' q, lkm_rrtSome q r t σ _ hm⟩

end

end Fl4Proofs.P3.Sched

/-! ## `reply_remove_tcb` on `IRel` with the call stacks -/

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`reply_remove_tcb` on `IRel` with the call stacks** (module docstring;
XTopJointRemove's `remove_topJ` for `reply_remove_tcb`). -/
theorem rrt_topJ (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit} {r t : U64}
    {x : Fl4Spec.Tcb} (hX : IRel st th cr N T C E R B c s σ) {Lst : U64 → List U64}
    (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC0 : ∀ q ∈ C, q ≠ 0#u64) (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    (hRF : RFree (L.mem s) R C σ Lst)
    (hr : r ∈ R) (ht : t ∈ T) (hk : σ.kheap t.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply r.bv)
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) (hrt : xr.replyTcb = some t.bv) :
    ipc.reply_remove_tcb st s t ⦃ s6 => ∃ (σ5 σ' : Fl4Spec.State Unit)
        (Lst' : U64 → List U64) (x5 : Fl4Spec.Tcb) (xr5 : Fl4Spec.Reply),
      Fl4Spec.replyRemoveTcb (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      replyRemoveTcbSc r.bv σ = ({((), σ5)}, False) ∧ σ5.kheap t.bv = some (.tcb x5) ∧
      σ5.kheap r.bv = some (.reply xr5) ∧ σ' = unlinkSt σ5 t.bv r.bv x5 xr5 ∧
      IRel st th cr N T C E R B c s6 σ' ∧ IFrame (L := L) th s s6 ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem s6) R C σ' Lst' ∧ RPlaced st N T C R c s6 σ' ∧ RFree (L.mem s6) R C σ' Lst' ∧
      CallStep (L.mem s) (L.mem s6) R C Lst Lst' r ∧
      WritesIn st s s6 (fun b => KFoot st T N C c s σ b ∨ CallW R C b) ⦄ := by
  obtain ⟨x0, hk0, hTR⟩ := hX.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hiw : L.mem s (tReplyA t) = r := Sched.bv_inj (hTR.reply _ hst)
  rw [reply_remove_tcb_eq]
  step with Fl4Proofs.P1.obj.Tcb.reply_obj.spec as ⟨i', hi'⟩
  have hii : i' = r := by rw [hi']; exact hiw
  subst hii
  refine WP.spec_bind (reply_remove_tcb_sc_refines s σ hX.2.2.1 hX.1.toN hN hI hCR hRP hRF hC0 hSCs hr) ?_
  rintro s5 ⟨σ5, Lst5, hsp, h1, h2, h3, h4, h5, h6, -, h7, huf, hcs, -, hw5⟩
  have hK : ScTKw (fun p => p = σ.curThread) σ σ5 :=
    ScTKw.ofFalse (NKT.of_eq (nkt_replyRemoveTcbSc i'.bv) hsp)
  have hX5 := tk_liftCW hP0 hX (hw5.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h)) Or.inr) hK h1 h2
  obtain ⟨xr5, hkr5, er5⟩ := huf.1 _ xr hkr
  obtain ⟨xt5, hkt5, et5⟩ := huf.2 _ x hk
  have hF5 : IFrame (L := L) th s s5 := IRel.iframe_of hX hw5 fun b hb =>
    hb.elim (fun h => tfoot_oobj hX.2.2.1 (Or.inl h)) (fun h => callW'_oobj hP0 hX.2.2.1 h)
  have hst5 : xt5.tcbState = .blockedOnReply i'.bv := by rw [et5]; exact hst
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and
    (reply_unlink_irel hP0 s5 σ5 hX5 ht hkt5 hst5 hr hkr5 (er5.trans hrt))
    (reply_unlink_iframe hP0 hX5 ht hr hkr5))
    (reply_unlink_refines s5 σ5 h1 h2 h3 h4 h5 h6 hr h7 ht hkr5 (er5.trans hrt) hkt5 (Or.inl hst5)))
    (reply_unlink_foot h1 h6 hr ht)) ?_
  rintro s6 ⟨⟨⟨⟨hul, hX6⟩, hF6⟩, σ6, hul6, -, -, hN6, hI6, hCR6, hRP6, hiso6, -, -, hm6, hk6⟩, hw6⟩
  have e6 : σ6 = unlinkSt σ5 t.bv i'.bv xt5 xr5 := by
    have h := hul6.symm.trans hul
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  subst e6
  have hw : WritesIn st s s6 (fun b => KFoot st T N C c s σ b ∨ CallW R C b) :=
    (hw5.trans hw6).mono fun b hb => by
      rcases hb with (hb | hb) | (hb | hb)
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
      · exact Or.inl (KFoot.of_sfoot ((SFoot.ksb hw5.1).1 hb))
      · exact Or.inr hb
  have hcs6 : CallStep (L.mem s) (L.mem s6) R C Lst Lst5 i' :=
    ⟨fun d hd hdet h0n h0p hdr => by
      obtain ⟨e1, e2⟩ := hcs.1 d hd hdet h0n h0p hdr
      exact ⟨(hm6 d hd).1.trans e1, (hm6 d hd).2.trans e2⟩, hcs.2.1, hcs.2.2⟩
  have hRF6 : RFree (L.mem s6) R C (unlinkSt σ5 t.bv i'.bv xt5 xr5) Lst5 := by
    refine RFree.step hRF hcs6 (fun d hd hfd hdr => ?_) (fun _ => ⟨hiso6.1, hiso6.2.1⟩)
    obtain ⟨x6, hk6d, hx6⟩ := hfd
    have hdt : d.bv ≠ t.bv := fun e => by
      obtain ⟨xd, hkd, -⟩ := hCR.reply d hd
      rw [e, hk] at hkd; cases hkd
    rw [hk6 _ (bv_ne hdr) hdt] at hk6d
    obtain ⟨xd, hkd, -⟩ := hCR.reply d hd
    obtain ⟨xd5, hkd5, ed⟩ := huf.1 _ xd hkd
    rw [hkd5] at hk6d; cases hk6d
    exact ⟨xd, hkd, ed ▸ hx6⟩
  exact ⟨σ5, _, Lst5, xt5, xr5, replyRemoveTcb_split hk hst hsp hul, hsp, hkt5, hkr5, rfl, hX6,
    hF5.trans hF6, hN6, hI6, hCR6, hRP6, hRF6, hcs6, hw⟩

end

end

end Fl4Proofs.P3.Ipc

/-! ## At `J` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The fault clear at `J`** (module docstring): a register-frame step. -/
theorem JAtZ.faultClearJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (tFaultA t) 0#u64) a
      (updK σ t.bv (.tcb { x with tcbFault := none })) := by
  have hP0 := J.ip
  have hX := J.xtop.irelK J.ks J.buf
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have hR1 := fault_clear_ipc hP0 hX.1 ht hk
  have hS1 := fault_clear_top hX.2 ht hk
  have hfa := a_fault hta
  have hwr : P1.WritesIn st s (L.wr s (tFaultA t) 0#u64) (· = tFaultA t) := writesIn_wr hfa.1
  have hfoot : P1.WritesIn st s (L.wr s (tFaultA t) 0#u64) (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) :=
    foot_field (K := 3376#u64) hTH htH (by simp) (by simp) (by simp) (by simp)
  have hA : QKY σ (updK σ t.bv (.tcb { x with tcbFault := none })) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => ?_⟩
    by_cases hp : p = t.bv
    · subst hp; exact Or.inr (Or.inl ⟨x, { x with tcbFault := none }, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, hp])
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac (L.wr s (tFaultA t) 0#u64) := by
    obtain ⟨h0, hB, hXi, hSc, hSg⟩ := J.blk
    obtain ⟨b1, b2, b3, b4, b5⟩ := P1.bxi_field (K := 3376#u64) (v := 0#u64) ⟨h0, hB, hXi, hSg, hSc⟩ htH
      (by simp) (by simp) (by simp) (by simp)
    exact ⟨b1, b2, b3, b5, b4⟩
  exact J.reg_frameF ⟨hR1, hS1⟩ (hwr.mono fun b hb => Or.inr ⟨t, ht, by rw [hb, val_fault hta]⟩)
    hA (YK.YKS.updTcb (y := { x with tcbFault := none }) hk rfl).ykeep
    (J.inv.updSame (y := { x with tcbFault := none }) hk rfl rfl (Or.inr hns)) hblk hfoot

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` after `reply_remove_tcb`** (module docstring), given P1's
`BlkOK` after. -/
theorem JAtZ.replyRemoveTcbJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {r t : U64} {x : Fl4Spec.Tcb} (hr : r ∈ Z.R) (ht : t ∈ Z.T) (hk : σ.kheap t.bv = some (.tcb x))
    (hst : x.tcbState = .blockedOnReply r.bv) :
    ipc.reply_remove_tcb st s t ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H)
      (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' → ∃ σ' V' Lst',
      Fl4Spec.replyRemoveTcb (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst' D s' a σ' ∧
      SlotsSame Z.th (L.mem s) (L.mem s') ∧ L.ksb s' = L.ksb s ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
  obtain ⟨xr, hkr, hrt⟩ := J.sv.onReply t.bv x r.bv hk hst
  have hrH : r ∈ P1.Heap.replies H := J.zH.2.2.1 r hr
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hrt_m : L.mem s (P1.rTcbA r) = t := by
    have h := hI.1.toE.at_reply hr hkr
    rw [hrt] at h
    exact optRef_some_eq h.symm
  have hst_m : L.mem s (P1.stA t) = sched.TS_BLOCKED_ON_REPLY := by
    have h := (hI.1.toE.at_tcb ht hk).st
    have e5 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
    apply UScalar.eq_of_val_eq
    rw [stA_tStA, h, hst, e5]
    all_goals simp [tsCode]
  have hreplyT : P1.ReplyT st (P1.Heap.replies H) (P1.Heap.scs H) s t := by
    obtain ⟨-, -, ⟨-, hR0, -⟩, -, -⟩ := J.blk
    obtain ⟨h1, h2⟩ := hR0.reply t htH hst_m
    exact ⟨h1, h2, hR0.next _ h1, hR0.prev _ h1⟩
  have hq0 := J.blk.1.choose_spec.choose_spec
  refine WP.spec_mono (WP.spec_and
    (Ipc.rrt_topJ J.ip hI J.call J.rp J.nsc J.inv J.c0 J.obj.sc J.rfree hr ht hk hst hkr hrt)
    (P1.ipc.reply_remove_tcb.kw (Es := P1.EH H) s t hq0.tcbs (hq0.nodes _ hq0.cur) hq0.cur J.blk.2.2.1.1 hreplyT
      htH)) ?_
  rintro s' ⟨⟨σ5, σ', Lst', x5, xr5, hrm, hsp, hk5t, hk5r, hσ', hIR, hF, hN', hI', hCR', hRP', hRF',
    hcs, hw0⟩, hfoot⟩ hblk
  have hmem : ((), σ') ∈ (Fl4Spec.replyRemoveTcb (Z := Unit) t.bv r.bv σ).1 := by rw [hrm]; exact Set.mem_singleton _
  have hks : L.ksb s' = L.ksb s := hF.2
  have hw := J.rmW_of hw0
  -- the spec's step: the call-stack part, then the unlink
  have hK : ScTKw (fun _ => False) σ σ5 := NKT.of_eq (nkt_replyRemoveTcbSc r.bv) hsp
  obtain ⟨q, hqk, hQ, hD, hL⟩ := rmTcbSc_donV hk hsp
  have hrt' : r.bv ≠ t.bv := fun e => by rw [e, hk] at hkr; cases hkr
  have kt' : σ'.kheap t.bv = some (.tcb { x5 with tcbState := .inactive }) := by
    rw [hσ']; simp [unlinkSt, stsAct_kheap, updK]
  have kr' : σ'.kheap r.bv = some (.reply { xr5 with replyTcb := none }) := by
    rw [hσ']; simp [unlinkSt, stsAct_kheap, updK, hrt']
  have ko' : ∀ p, p ≠ t.bv → p ≠ r.bv → σ'.kheap p = σ5.kheap p := fun p h1 h2 => by
    rw [hσ']; simp [unlinkSt, stsAct_kheap, updK, h1, h2]
  have hact' : σ'.schedulerAction = .chooseNewThread ∨ σ'.schedulerAction = σ5.schedulerAction := by
    rw [hσ']; unfold unlinkSt; exact Sched.stsAct_action _ _
  have hct' : σ'.curThread = σ.curThread := by
    rw [hσ']; unfold unlinkSt stsAct; split_ifs <;> exact hK.ct
  have harch : σ'.archState = σ.archState := by
    rw [hσ']; unfold unlinkSt stsAct; split_ifs <;> exact hK.arch
  have hsF : Vs.rsF σ' = Vs.rsF σ := Vs.rsf_replyRemoveTcb t.bv r.bv σ ((), σ') hmem
  simp only [Vs.rsF, Prod.mk.injEq] at hsF
  obtain ⟨hidle', hcsc', hcons', htime', hisc'⟩ := hsF
  have hRQ : RelQ.RQK σ σ' := RelQ.rq_replyRemoveTcb' t.bv r.bv σ ((), σ') hmem
  have hCK : Fl4Proofs.P3.CKeep σ σ' := nkc_replyRemoveTcb t.bv r.bv σ ((), σ') hmem
  have hrq_t : t.bv ∉ σ.releaseQueue := fun hm => by
    obtain ⟨x0, -, -, -, hk0, -, hr0, -⟩ := J.inv.rel _ hm
    rw [hk] at hk0; cases hk0; rw [hst] at hr0; simp [Fl4Spec.runnable] at hr0
  -- the objects after
  have scB : ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧
      y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax ∧
      (y.scTcb = y0.scTcb ∨ (p = q ∧ y.scTcb = some t.bv ∧ ∀ f, y0.scTcb = some f → DonA σ σ5 f)) :=
    fun p y n hp => by
      have h1 : p ≠ t.bv := by rintro rfl; rw [kt'] at hp; cases hp
      have h2 : p ≠ r.bv := by rintro rfl; rw [kr'] at hp; cases hp
      rw [ko' p h1 h2] at hp
      exact hD.sc p y n hp
  have scF : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) := by
    intro p y n hp
    have h1 : p ≠ t.bv := by rintro rfl; rw [hk] at hp; cases hp
    have h2 : p ≠ r.bv := by rintro rfl; rw [hkr] at hp; cases hp
    rw [ko' p h1 h2]
    have := hK.kh p
    rw [hp] at this
    cases e : σ5.kheap p with
    | none => rw [e] at this; exact this.elim
    | some o =>
      rw [e] at this
      rcases this with rfl | ⟨_, _, e1, -⟩ | ⟨_, y', _, e1, rfl⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩
      · exact ⟨y, rfl⟩
      all_goals (try cases e1)
      exact ⟨y', rfl⟩
  have tcbF : ∀ u x0, σ.kheap u = some (.tcb x0) → u ≠ t.bv → ∃ x', σ'.kheap u = some (.tcb x') ∧
      x'.tcbState = x0.tcbState ∧ x'.tcbBoundNotification = x0.tcbBoundNotification ∧
      (x'.tcbSchedContext = x0.tcbSchedContext ∨ (x'.tcbSchedContext = none ∧ DonA σ σ5 u ∧
        ∃ y0 n, σ.kheap q = some (.schedContext y0 n) ∧ y0.scTcb = some u)) := by
    intro u x0 hx0 hut
    have hur : u ≠ r.bv := by rintro rfl; rw [hkr] at hx0; cases hx0
    obtain ⟨x1, hx1, hso, hs1⟩ := hK.tcb hx0
    obtain ⟨x2, hx2, hsc⟩ := hD.tcb u x0 hx0
    rw [hx1] at hx2; cases hx2
    refine ⟨x1, by rw [ko' u hut hur]; exact hx1, ?_, ?_, ?_⟩
    · rcases hs1 with e | ⟨h, -⟩
      · exact e
      · exact False.elim h
    · have e := congrArg Fl4Spec.Tcb.tcbBoundNotification hso; exact e
    · rcases hsc with e | ⟨e, -⟩ | e
      · exact Or.inl e
      · exact absurd e hut
      · exact Or.inr e
  have tcbB : ∀ u x', σ'.kheap u = some (.tcb x') → u ≠ t.bv → ∃ x0, σ.kheap u = some (.tcb x0) := by
    intro u x' hx' hut
    have hur : u ≠ r.bv := by rintro rfl; rw [kr'] at hx'; cases hx'
    rw [ko' u hut hur] at hx'
    obtain ⟨o, ho, htk⟩ := hK.back hx'
    rcases htk with rfl | ⟨x0, _, rfl, e, -⟩ | ⟨_, _, _, -, e⟩ | ⟨_, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
    · exact ⟨x', ho⟩
    · exact ⟨x0, ho⟩
    all_goals cases e
  have dA : ∀ f, DonA σ σ5 f → σ'.schedulerAction ≠ .chooseNewThread →
      f ≠ σ.curThread ∧ σ.schedulerAction ≠ .switchThread f := by
    intro f hf hcn
    rcases hf with e | e
    · exfalso; rcases hact' with e' | e'
      · exact hcn e'
      · exact hcn (e'.trans e)
    · exact e
  -- the scheduler invariants
  have hoff : OffOK σ' := by
    intro hpos y n hy ha
    rw [hcsc'] at hy; rw [hcsc', hisc'] at ha
    rw [hcons'] at hpos ⊢
    rw [htime']
    obtain ⟨y0, hy0, er, em, -⟩ := scB _ y n hy
    have hr0 : Fl4Spec.refillHd y = Fl4Spec.refillHd y0 := by unfold Fl4Spec.refillHd; rw [er]
    rw [hr0]
    exact J.off hpos y0 n hy0 fun h => by
      have := ha h
      show Fl4Spec.activeSc y0.scRefillMax = true
      rw [← em]; exact this
  have hown : CurOwnW Z.T Z.C σ' := by
    have hcscC : ∃ sc ∈ Z.C, sc.bv = σ.curSc := by
      rcases J.own with ⟨u, hu, xt, hkt, hxs, -, -⟩ | ⟨h, -⟩
      · obtain ⟨y, n, hky, -⟩ := J.inv.back _ xt _ hkt hxs
        exact J.obj.sc _ y n hky
      · exact h
    by_cases hex : ∃ y n, σ'.kheap σ'.curSc = some (.schedContext y n)
    · obtain ⟨y, n, hy⟩ := hex
      cases hyt : y.scTcb with
      | none =>
        refine Or.inr ⟨by rw [hcsc']; exact hcscC, fun x' n' hx' => ?_⟩
        rw [hy] at hx'; cases hx'; exact hyt
      | some f =>
        obtain ⟨sc, hsc, esc⟩ := hcscC
        rw [hcsc', ← esc] at hy
        obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        obtain ⟨y00, hy00, -⟩ := scB _ y n hy
        have hqS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc _ _ (J.c0 sc hsc) hy00).2⟩
        obtain ⟨u, hu, eu, xu, hku, hxu⟩ := scBack_of hIR.2.2.1 hblk.2.2.1 J.tcbs_eq.1.symm hsc hqS (J.c0 sc hsc) hy hyt
        refine Or.inl ⟨u, hu, xu, by rw [eu]; exact hku, by rw [hcsc', ← esc]; exact hxu,
          fun x' n' hx' => by rw [hcsc', ← esc, hy] at hx'; cases hx'; rw [hyt, eu], fun hpos hm => ?_⟩
        rw [hcons'] at hpos
        have hm0 := hRQ _ hm
        obtain ⟨y0, hy0, -, -, et⟩ := scB _ y n hy
        rcases et with et | ⟨-, et, -⟩
        · rcases J.own with ⟨u0, hu0, xt0, hkt0, hxs0, hown0, hnr0⟩ | ⟨-, hun⟩
          · have h1 := hown0 y0 n (by rw [← esc]; exact hy0)
            rw [← et, hyt] at h1
            cases h1
            rw [eu] at hm0
            exact hnr0 hpos hm0
          · have h1 := hun y0 n (by rw [← esc]; exact hy0)
            rw [← et, hyt] at h1
            cases h1
        · rw [hyt] at et
          cases et
          rw [eu] at hm0
          exact hrq_t hm0
    · exact Or.inr ⟨by rw [hcsc']; exact hcscC, fun x' n' hx' => absurd ⟨x', n', hx'⟩ hex⟩
  have hAS : ActSched σ' := by
    intro u hu
    have hu5 : σ5.schedulerAction = .switchThread u := by
      rcases hact' with e | e
      · rw [e] at hu; cases hu
      · rw [← e]; exact hu
    have hu0 : σ.schedulerAction = .switchThread u := by
      rcases hD.act with e | e
      · rw [← e]; exact hu5
      · rw [e] at hu5; cases hu5
    obtain ⟨x0, scp, y0, n0, hk0, hsc0, hrn0, hky0, ha0, hnr0⟩ := schedulable_inv (J.act.1 u hu0)
    have hut : u ≠ t.bv := by rintro rfl; rw [hk] at hk0; cases hk0; rw [hst] at hrn0; simp [Fl4Spec.runnable] at hrn0
    obtain ⟨x', hx', es, -, esc⟩ := tcbF u x0 hk0 hut
    have hsc' : x'.tcbSchedContext = some scp := by
      rcases esc with e | ⟨-, hdA, -⟩
      · rw [e]; exact hsc0
      · exfalso
        have hcn : σ'.schedulerAction ≠ .chooseNewThread := by rw [hu]; intro h; cases h
        exact (dA u hdA hcn).2 hu0
    obtain ⟨y', hy'⟩ := scF _ _ _ hky0
    obtain ⟨y1, hy1, -, em, -⟩ := scB _ _ _ hy'
    rw [hky0] at hy1; cases hy1
    refine schedulable_of hx' hsc' (by rw [es]; exact hrn0) hy' ?_ (fun hm => hnr0 (hRQ _ hm))
    simpa [Fl4Spec.scActive, em] using ha0
  have hidl : IdleOK σ' := by
    obtain ⟨xi, hki, hsi, hti, hri⟩ := J.act.2
    have hit : σ.idleThread ≠ t.bv := by rintro e; rw [e, hk] at hki; cases hki; rw [hst] at hti; cases hti
    obtain ⟨x', hx', es, -, esc⟩ := tcbF _ xi hki hit
    refine ⟨x', by rw [hidle']; exact hx', ?_, by rw [es]; exact hti, by rw [hidle']; exact fun hm => hri (hRQ _ hm)⟩
    rcases esc with e | ⟨-, -, y0, n0, hy0, hyt0⟩
    · rw [e, hisc']; exact hsi
    · exact (J.idle_noStack hy0 (hQ y0 n0 hy0) hyt0).elim
  have hcur : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    by_cases hcn : σ'.schedulerAction = .chooseNewThread
    · exact Or.inl hcn
    right
    have h5 : σ'.schedulerAction = σ5.schedulerAction := hact'.resolve_left hcn
    have h0 : σ.schedulerAction ≠ .chooseNewThread := by
      intro e
      rcases hD.act with e' | e'
      · exact hcn (h5.trans (e'.trans e))
      · exact hcn (h5.trans e')
    have CI := J.curInv h0
    obtain ⟨xc, hkc, hscc, hnb⟩ := CI.tcb
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hct : σ.curThread = t.bv
      · -- the current thread is the caller (a switch pending): its SC kept
        rw [hct, hk] at hkc; cases hkc
        obtain ⟨x2, hx2, hsc2⟩ := hD.tcb t.bv _ hk
        rw [hk5t] at hx2; cases hx2
        refine ⟨_, by rw [hct', hct]; exact kt', ?_, ?_⟩
        · dsimp only
          rcases hsc2 with e | ⟨-, e⟩ | ⟨-, hdA, -⟩
          · rw [e, hcsc']; exact hscc
          · rw [hscc] at e; cases e
          · exact absurd hct.symm (dA _ hdA hcn).1
        · refine ⟨?_, ?_, ?_⟩
          · intro _ e; simp at e
          · intro _ _ e; simp at e
          · intro _ _ _ e; simp at e
      · obtain ⟨x', hx', es, -, esc⟩ := tcbF _ xc hkc hct
        refine ⟨x', by rw [hct']; exact hx', ?_, by rw [es]; exact hnb⟩
        rcases esc with e | ⟨-, hdA, -⟩
        · rw [e, hcsc']; exact hscc
        · exact absurd rfl (dA _ hdA hcn).1
    · obtain ⟨y0, n0, hy0⟩ := CI.sc
      obtain ⟨y', hy'⟩ := scF _ _ _ hy0
      exact ⟨y', n0, by rw [hcsc']; exact hy'⟩
    · intro hne y n hy
      rw [hcsc', hisc'] at hne; rw [hcsc'] at hy
      obtain ⟨y0, hy0, -, em, -⟩ := scB _ y n hy
      have := CI.active hne y0 n hy0
      simpa [Fl4Spec.scActive, em] using this
    · intro hm; rw [hct'] at hm; exact CI.notRel (hRQ _ hm)
  have hrun : CurRunM σ' := by
    by_cases hnr : σ'.schedulerAction ≠ .resumeCurThread
    · exact Or.inl hnr
    right
    have hr' : σ'.schedulerAction = .resumeCurThread := not_not.1 hnr
    have h5 : σ'.schedulerAction = σ5.schedulerAction := hact'.resolve_left (by rw [hr']; intro e; cases e)
    have h0 : ¬ σ.schedulerAction ≠ .resumeCurThread := by
      intro e
      rcases hD.act with e' | e'
      · exact hnr (by rw [h5, e']; exact e)
      · exact hnr (by rw [h5, e']; intro e; cases e)
    rcases J.curRun.resolve_left h0 with h | h
    · left
      intro x' hx'
      rw [hct'] at hx'
      by_cases hct : σ.curThread = t.bv
      · exfalso
        have := h x (by rw [hct]; exact hk); rw [hst] at this; simp [Fl4Spec.runnable] at this
      · obtain ⟨xc, hkc⟩ := tcbB _ x' hx' hct
        obtain ⟨x2, hx2, es, -, -⟩ := tcbF _ xc hkc hct
        rw [hx'] at hx2; cases hx2
        rw [es]; exact h xc hkc
    · right; rw [hct', hidle']; exact h
  have hbsa : BlockedScActive σ' := by
    refine ⟨fun p y n u xu hp hyu hku hq => ?_, fun p y n hp hne => ?_⟩
    · obtain ⟨y0, hy0, -, em, et⟩ := scB p y n hp
      have hut : u ≠ t.bv := by
        rintro rfl; rw [kt'] at hku; cases hku; simp [Fl4Spec.ipcQueuedThreadState] at hq
      obtain ⟨x0, hx0⟩ := tcbB u xu hku hut
      obtain ⟨x2, hx2, es, -, -⟩ := tcbF u x0 hx0 hut
      rw [hku] at hx2; cases hx2
      have hyu0 : y0.scTcb = some u := by
        rcases et with e | ⟨-, e, -⟩
        · rw [← e]; exact hyu
        · rw [hyu] at e; cases e; exact absurd rfl hut
      have := J.bsa.tcb p y0 n u x0 hy0 hyu0 hx0 (by rw [← es]; exact hq)
      simpa [Fl4Spec.scActive, em] using this
    · obtain ⟨y0, hy0, -, em, -⟩ := scB p y n hp
      obtain ⟨q', hq', rfl⟩ := J.obj.sc _ y0 n hy0
      obtain ⟨⟨y1, n1, hk1, hyL1⟩, -⟩ := hCR'.stack q' hq'
      rw [hp] at hk1; cases hk1
      obtain ⟨⟨y2, n2, hk2, hyL2⟩, -⟩ := J.call.stack q' hq'
      rw [hy0] at hk2; cases hk2
      have hne' : Lst' q' ≠ [] := fun e => hne (by rw [hyL1, e]; rfl)
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne'
      have hd0 := hcs.2.1 q' hq' d hd
      have hne0 : y0.scReplies ≠ [] := by
        rw [hyL2]; intro e
        rw [List.map_eq_nil_iff] at e
        rw [e] at hd0; cases hd0
      have := J.bsa.replies _ y0 n hy0 hne0
      simpa [Fl4Spec.scActive, em] using this
  have hiso : IpcSorted σ' := QPK.QPS.sorted (QPK.qp_replyRemoveTcb t.bv r.bv σ ((), σ') hmem) J.isorted
  -- the frames
  obtain ⟨k1, k2, kb⟩ := J.rmW_keeps hw
  have hyk : YKeep σ σ' := (YK.yk_replyRemoveTcb t.bv r.bv σ ((), σ') hmem).ykeep
  have hso : ∀ p x0, σ.kheap p = some (.tcb x0) → ∃ x', σ'.kheap p = some (.tcb x') ∧
      x'.tcbMcpriority = x0.tcbMcpriority ∧ x'.tcbIpcBuffer = x0.tcbIpcBuffer := by
    intro p x0 hp
    obtain ⟨x1, hx1, hso1, -⟩ := hK.tcb hp
    have e1 := congrArg Fl4Spec.Tcb.tcbMcpriority hso1
    have e2 := congrArg Fl4Spec.Tcb.tcbIpcBuffer hso1
    by_cases hpt : p = t.bv
    · subst hpt
      rw [hk5t] at hx1; cases hx1
      exact ⟨_, kt', e1, e2⟩
    · have hpr : p ≠ r.bv := by rintro rfl; rw [hkr] at hp; cases hp
      exact ⟨x1, by rw [ko' p hpt hpr]; exact hx1, e1, e2⟩
  have hmk : McpKeep σ σ' := fun p x0 hp => let ⟨x', h1, h2, _⟩ := hso p x0 hp; ⟨x', h1, h2⟩
  have hbk : ∀ p x0, σ.kheap p = some (.tcb x0) → ∃ y, σ'.kheap p = some (.tcb y) ∧
      y.tcbIpcBuffer = x0.tcbIpcBuffer := fun p x0 hp => let ⟨x', h1, _, h3⟩ := hso p x0 hp; ⟨x', h1, h3⟩
  have szk : SzKeep σ σ' := fun p y n hp => let ⟨y0, hy0, _⟩ := scB p y n hp; ⟨y0, hy0⟩
  have hksz : KSz σ σ' := by
    intro o ko0 ho
    by_cases hot : o = t.bv
    · subst hot; rw [kt'] at ho; cases ho; exact ⟨_, hk, rfl⟩
    by_cases hor : o = r.bv
    · subst hor; rw [kr'] at ho; cases ho; exact ⟨_, hkr, rfl⟩
    rw [ko' o hot hor] at ho
    exact hK.ksz o ko0 ho
  have hkb : KBack σ σ' := by
    intro o ko0 ho
    by_cases hot : o = t.bv
    · subst hot; rw [kt'] at ho; cases ho; exact ⟨_, hk, by simp⟩
    by_cases hor : o = r.bv
    · subst hor; rw [kr'] at ho; cases ho; exact ⟨_, hkr, by simp⟩
    rw [ko' o hot hor] at ho
    obtain ⟨ko, hko, htk⟩ := hK.back ho
    rcases htk with rfl | ⟨a1, b1, rfl, rfl, -⟩ | ⟨a1, b1, n1, rfl, rfl⟩ | ⟨a1, b1, rfl, rfl, -⟩ |
      ⟨a1, b1, rfl, rfl, -⟩
    · exact ⟨_, hko, id, id, id, id, id, id⟩
    all_goals exact ⟨_, hko, by simp⟩
  -- the dead
  have ht' : ∀ q' ∈ D, q'.bv ≠ t.bv := by
    intro q' hq' e
    have htq : t = q' := (P1.eq_of_bv e).symm
    subst htq
    have hd := (J.jcov.dead t hq').1 (J.zH.1 t ht)
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t ht
    rw [hk] at hk'; cases hk'
    have h3 := hR.st
    rw [← stA_tStA, hd.1, hst] at h3
    unfold sched.TS_INACTIVE at h3
    simp [tsCode] at h3
  have hdead : ∀ q' ∈ D, DeadP (L := L) H s' q' := fun q' hq' => by
    have hd := J.jcov.dead q' hq'
    have hqt := ht' q' hq'
    refine J.deadP_keep hIR.2.2.1 hIR.1 (fun x0 hx0 h0 => ?_) (fun x0 hx0 => ?_) (fun x0 hx0 => ?_)
      (fun x0 hx0 => ?_) (fun x0 n hx0 => ?_) (fun hqC => ?_)
      (fun z hz hqC K hK8 hK' => J.rmW_scOut hw hz hqC hK8 hK') hidle' hAS (J.yld.frame k2 hyk) (hyk.dk q'.bv) hd
    · obtain ⟨x', hx', es, eb, esc⟩ := tcbF _ x0 hx0 hqt
      exact ⟨x', hx', es, eb, esc.imp id (fun h => h.1)⟩
    · have hq1 : q'.bv ≠ r.bv := by rintro e; rw [e, hkr] at hx0; cases hx0
      rw [ko' _ hqt hq1]; exact hK.ep hx0
    · have hq1 : q'.bv ≠ r.bv := by rintro e; rw [e, hkr] at hx0; cases hx0
      have hW : ¬ (q'.bv = q ∨ q'.bv = t.bv) := by
        rintro (e | e)
        · rcases hqk with e' | ⟨y0, n0, hy0⟩
          · exact hqt (e.trans e')
          · rw [e, hy0] at hx0; cases hx0
        · exact hqt e
      obtain ⟨y, hy, e1, e2⟩ := hK.ntfn' hx0
      obtain ⟨y', hy', e3⟩ := lk_ntfnAt hL hW hx0
      rw [hy] at hy'; cases hy'
      exact ⟨y, by rw [ko' _ hqt hq1]; exact hy, Or.inl e1, e2, e3⟩
    · by_cases hq1 : q'.bv = r.bv
      · exfalso
        obtain ⟨r', hr', er⟩ := J.obj.reply _ x0 hx0
        have hrr : r' = q' := P1.eq_of_bv er
        subst hrr
        have d4 := hd.2.2.2.1 (J.zH.2.2.1 r' hr')
        have h := hI.1.toE.at_reply hr' hx0
        have d4' : L.mem s (Endp.rTcbA r') = 0#u64 := d4
        rw [d4', optRef_zero] at h
        rw [hq1, hkr] at hx0; cases hx0
        rw [hrt] at h; cases h
      · rw [ko' _ hqt hq1]; exact hK.reply hx0
    · have hq1 : q'.bv ≠ r.bv := by rintro e; rw [e, hkr] at hx0; cases hx0
      have hW : ¬ (q'.bv = q ∨ q'.bv = t.bv) := by
        rintro (e | e)
        · have := hQ x0 n (by rw [← e]; exact hx0)
          rw [(J.dead_sc hq' hx0).2.2.2] at this; cases this
        · exact hqt e
      obtain ⟨y, hy, e1, e2⟩ := lk_scAt hL hW hx0
      exact ⟨y, by rw [ko' _ hqt hq1]; exact hy, e1, e2⟩
    · obtain ⟨⟨y0, n0, hk0, -⟩, -⟩ := J.call.stack q' hqC
      obtain ⟨-, hL0, h0, -⟩ := J.dead_sc hq' hk0
      have hL' : Lst' q' = [] := List.eq_nil_iff_forall_not_mem.2 fun d hd => by
        have := hcs.2.1 q' hqC d hd; rw [hL0] at this; cases this
      obtain ⟨-, -, -, hSW'⟩ := hCR'.stack q' hqC
      rw [hSW'.1, hL', h0]; rfl
  -- assembly
  have hAR := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 hCK.cdt hCK.orig hCK.ks hks
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => szk q.bv y n hq) hks (J.rmW_irq hw)
      (J.idleW_keep hIR.2.2.1 hidle' hisc').2⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hao : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao) := by
    intro p ao hp
    have h1 : p ≠ t.bv := by rintro rfl; rw [hk] at hp; cases hp
    have h2 : p ≠ r.bv := by rintro rfl; rw [hkr] at hp; cases hp
    rw [ko' p h1 h2]
    exact hK.keep_other hp (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)
  have hkern := J.kern_keep hks hw.2.1 hIR.2.2.1 hct' hcsc' (fun sl h => Or.inl (by rw [← hCK.orig]; exact h))
    (by rw [harch]) hao hDbg (D' := D)
  have hRR' : RRecv (L.mem s') Z.R σ' := by
    refine RRecv.step J.rrecv J.call (fun d hd => (J.rp.align d hd).2.1) hcs
      (fun d _ hrd _ => ((KhRB.of_sctkw hK).trans (KhRB.unlink hk5t hk5r kt' kr' ko')).recvB hrd)
      (fun _ => ?_)
    obtain ⟨-, h1, h2⟩ := hRF' r hr ⟨_, kr', rfl⟩
    exact ⟨h1, h2⟩
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst' D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 hmk, J.buf.frame kb hbk, hRP',
      J.apart.sc_frame hks szk, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hIR.2.2.1 hidle' hisc'), hkern,
      J.rmW_utc hw hF.1 hCK.cdt hCK.orig harch hDbg, hN', hI', hcur, hown, hoff, ⟨hAS, hidl⟩, hbsa, hiso,
      hrun, hblk⟩
  have hC0 := JCs.same J hF.1 hksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨σ', Z.vs, Lst', hrm, J.cs_frameI hks hX3 hw (fun b hb => RmW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.rmW_nv hb) harch hao szk hF.1 hkb
    ((IpcFrKeep.of_otk hK.kh).trans (IpcFrKeep.of_upd2 hk5t kt' rfl rfl hk5r kr'
      (IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) ko'))
    hC R hKd hCK.orig (J.idleW_keep hIR.2.2.1 hidle' hisc').1 J.zD, hF.1, hks⟩

set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` of a thread blocked on its reply, at `J`** (module
docstring): the fault clear, then `reply_remove_tcb`. -/
theorem JAtZ.cancelReplyJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {rp : Fl4Spec.ObjRef}
    (hst : x.tcbState = .blockedOnReply rp) :
    ipc.cancel_ipc st arI s a t ⦃ res => res.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D res.1 res.2 σ' ⦄ := by
  have hP0 := J.ip
  have hX := J.xtop.irelK J.ks J.buf
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨xr, hkr, -⟩ := J.sv.onReply t.bv x rp hk hst
  obtain ⟨r, hr, rfl⟩ := J.obj.reply rp xr hkr
  obtain ⟨V1, J1⟩ := J.faultClearJ ht hk fun e d h => by rw [hst] at h; cases h
  have hk1 : (updK σ t.bv (.tcb { x with tcbFault := none })).kheap t.bv = some (.tcb { x with tcbFault := none }) := by
    simp [updK]
  obtain ⟨x0, hk0, hx⟩ := hX.1.tcb t ht
  rw [hk] at hk0; injection hk0 with hk0; injection hk0 with hk0; subst hk0
  have hfa := a_fault hta
  have g : ∀ w, Aligned w → w.val ≠ t.val + 3376 → L.mem (L.wr s (tFaultA t) 0#u64) w = L.mem s w :=
    fun w hw hne => rd_wr_ne hfa.1 hw (fun e => hne (by rw [← e, val_fault hta]))
  have hstw : L.mem (L.wr s (tFaultA t) 0#u64) (P1.stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [P1.stA_eq, ← tStA_eq, g _ (a_st hta).1 (by rw [val_st hta]; omega)]
    apply UScalar.eq_of_val_eq
    rw [hx.st, hst]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
  have e3 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
  have hmain : ipc.cancel_ipc st arI s a t ⦃ res => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac res.1 →
      res.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D res.1 res.2 σ' ⦄ := by
    unfold ipc.cancel_ipc faults.clear_fault
    step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s1', hs1'⟩
    have e1 : s1' = L.wr s (tFaultA t) 0#u64 := by rw [hs1']; unfold fl4_abi.consts.fault.NullFault; rfl
    subst e1
    step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
    rw [hw, hstw, e3, tsVals.2.2.2.1, tsVals.2.2.1, tsVals.2.2.2.2]
    simp only [show (5#u64 : U64) ≠ 4#u64 by decide, show (5#u64 : U64) ≠ 3#u64 by decide,
      show (5#u64 : U64) ≠ 6#u64 by decide, ↓reduceIte]
    refine WP.spec_bind (J1.replyRemoveTcbJ (x := { x with tcbFault := none }) hr ht hk1 hst) ?_
    intro s2 h2
    rw [WP.spec_ok]
    intro hblk
    obtain ⟨σ', V', Lst', he, J', -, -⟩ := h2 hblk
    refine ⟨rfl, σ', ?_, V', Ac, Lst', J'⟩
    unfold Fl4Spec.cancelIpc
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (threadSet_eq _ hk), hst]
    rw [hst] at he
    exact he
  refine WP.spec_mono (WP.spec_and (P1.ipc.cancel_ipc.blk s a t J.blk htH) hmain) ?_
  rintro ⟨s2, a2⟩ ⟨hb, hm⟩
  exact hm hb

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JCancelAt` for a thread blocked on its reply** (module docstring). -/
theorem jCancel_reply {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} :
    JCancelAt (L := L) arI AR th fun ts => ∃ r, ts = .blockedOnReply r := by
  intro Z H Cs Ac Lst D s a σ _ J t ht x hk ⟨r, hst⟩
  exact J.cancelReplyJ ht hk hst

end

end

end Fl4Proofs.P3
