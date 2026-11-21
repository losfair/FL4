/-
P3 (DESIGN.md §9), IPC: **`JAtZ` across `reply_remove` of a thread blocked
on the reply** (`JAtZ.replyRemoveJ`: XTopJointDelR's `JReplyRemoveHyp`, for a
final reply cap's finalisation).

* FL4's side: `Ipc.remove_topJ`, `reply_remove_refinesU` and
  `reply_unlink_refines` together (IpcFinReply's `remove_topF` with the call
  stacks, the spec's call-stack part and the footprint `KFoot ∨ CallW`); P1's
  `ipc.reply_remove.blk` (`BlkOK`) and `ipc.reply_remove.kwA` (no debug-list
  word written: the caller sits on its SC's core, `JAtZ.rmCore`).
* The footprint `RmW`: `FinW` and the words of the replies and of the SCs of
  `Z.C` (`RmX`); `JAtZ.rmW_keeps`, `rmW_scOut`, `rmW_irq`, `rmW_utc`
  (ScSignalBoundJ's `cnW_*`).
* The spec's side (IpcRemoveSpecJ): the call-stack part `replyRemoveSc`
  (`ScTKw`, `DonV`, `LK`), then `reply_unlink_tcb` (`unlinkSt`); the
  scheduler invariants after: `CurOwnW` (an SC's thread after is a thread
  with that SC, `scBack_of`, from P1's `TSc`), `OffOK` (the refills kept),
  `ActIdle` (the switch target and the idle thread keep their SCs: the idle
  thread holds no call stack, `JAtZ.idle_noStack`), `CurInv` and `CurRunM`
  (no reschedule pending: the donor, if any, neither current nor the switch
  target), `BlockedScActive` (the stacks only shrink, `CallStep`).
* The dead stay dead (`deadP_keep`): a dead SC has an empty stack, so it is
  not the donated SC and its `REPLY` word stays 0.
* The donation back (`hdon` of ScCallRemove's `reply_remove_refinesU`): the
  popped reply's SC is bound to another thread (`scBack_of`: its thread has
  it, so it is not the caller, which has none) or to none (its thread
  deleted while the caller waited; ScCallPopRef's `donate_unbound_refines`).
* `JAtZ.replyRemoveJD` also returns the dead set unchanged, the thread
  `Inactive` after, and every SC bound to it after active (IpcRemove's
  `remove_act`, from `BlockedScActive` before) (for the reply's rest,
  XTopJointIpcJ); `replyRemoveJ` is it without them (`JReplyRemoveHyp`).
-/
import Fl4Proofs.P3.XTopJointFinReply
import Fl4Proofs.P3.IpcRemoveSpecJ
import Fl4Proofs.P3.IpcQP
import Fl4Proofs.P1.QueueReplyKw
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

/-! ## `reply_remove` on `IRel` with the call stacks -/

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`reply_remove` on `IRel` with the call stacks** (module docstring). -/
theorem remove_topJ (hP0 : IPlaced N T E R B) {s : S} {a : A} {σ : Fl4Spec.State Unit} {r t : U64}
    {x : Fl4Spec.Tcb} (hX : IRel st th cr N T C E R B c s σ) {Lst : U64 → List U64}
    (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC0 : ∀ q ∈ C, q ≠ 0#u64) (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    (hRF : RFree (L.mem s) R C σ Lst)
    (hr : r ∈ R) (ht : t ∈ T) (hk : σ.kheap t.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply r.bv)
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) (hrt : xr.replyTcb = some t.bv)
    (hdon : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      x.tcbSchedContext = none → (∃ f, f ∈ T ∧ y.scTcb = some f.bv ∧ f ≠ t) ∨ y.scTcb = none) :
    ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ (σ5 σ' : Fl4Spec.State Unit)
        (Lst' : U64 → List U64) (x5 : Fl4Spec.Tcb) (xr5 : Fl4Spec.Reply),
      Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      replyRemoveSc t.bv r.bv σ = ({((), σ5)}, False) ∧ σ5.kheap t.bv = some (.tcb x5) ∧
      σ5.kheap r.bv = some (.reply xr5) ∧ σ' = unlinkSt σ5 t.bv r.bv x5 xr5 ∧
      IRel st th cr N T C E R B c res.1 σ' ∧ IFrame (L := L) th s res.1 ∧ NSC N C σ' ∧ Inv σ' ∧
      CallRel (L.mem res.1) R C σ' Lst' ∧ RPlaced st N T C R c res.1 σ' ∧ RFree (L.mem res.1) R C σ' Lst' ∧
      CallStep (L.mem s) (L.mem res.1) R C Lst Lst' r ∧
      WritesIn st s res.1 (fun b => KFoot st T N C c s σ b ∨ CallW R C b) ⦄ := by
  have hrel : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      x.tcbSchedContext = none → inClassR x.tcbState x.tcbFault → Fl4Spec.scActive y = true → released σ y := by
    intro _ _ _ _ _ _ _ hc
    exfalso
    rw [hst] at hc
    rcases hc.cls with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩
    · simp [Fl4Spec.runnable] at h
    all_goals cases h
  refine reply_remove_refinesU s a σ hX.2.2.1 hX.1.toN hN hI hCR hRP hC0 hSCs hr ht hk hdon hrel _ ?_
  intro s5 σ5 Lst5 h1 h2 h3 h4 h5 h6 h7 huf hcs hsp hw5
  have hK : ScTKw (fun p => p = σ.curThread) σ σ5 :=
    ScTKw.ofFalse (NKT.of_eq (nkt_replyRemoveSc t.bv r.bv) hsp)
  have hX5 := tk_liftCW hP0 hX (hw5.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h)) Or.inr) hK h1 h2
  obtain ⟨xr5, hkr5, er5⟩ := huf.1 _ xr hkr
  obtain ⟨xt5, hkt5, et5⟩ := huf.2 _ x hk
  have hF5 : IFrame (L := L) th s s5 := IRel.iframe_of hX hw5 fun b hb =>
    hb.elim (fun h => tfoot_oobj hX.2.2.1 (Or.inl h)) (fun h => callW'_oobj hP0 hX.2.2.1 h)
  have hst5 : xt5.tcbState = .blockedOnReply r.bv := by rw [et5]; exact hst
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and
    (reply_unlink_irel hP0 s5 σ5 hX5 ht hkt5 hst5 hr hkr5 (er5.trans hrt))
    (reply_unlink_iframe hP0 hX5 ht hr hkr5))
    (reply_unlink_refines s5 σ5 h1 h2 h3 h4 h5 h6 hr h7 ht hkr5 (er5.trans hrt) hkt5 (Or.inl hst5)))
    (reply_unlink_foot h1 h6 hr ht)) ?_
  rintro s6 ⟨⟨⟨⟨hul, hX6⟩, hF6⟩, σ6, hul6, -, -, hN6, hI6, hCR6, hRP6, hiso6, -, -, hm6, hk6⟩, hw6⟩
  have e6 : σ6 = unlinkSt σ5 t.bv r.bv xt5 xr5 := by
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
  have hcs6 : CallStep (L.mem s) (L.mem s6) R C Lst Lst5 r :=
    ⟨fun d hd hdet h0n h0p hdr => by
      obtain ⟨e1, e2⟩ := hcs.1 d hd hdet h0n h0p hdr
      exact ⟨(hm6 d hd).1.trans e1, (hm6 d hd).2.trans e2⟩, hcs.2.1, hcs.2.2⟩
  have hRF6 : RFree (L.mem s6) R C (unlinkSt σ5 t.bv r.bv xt5 xr5) Lst5 := by
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
  exact ⟨rfl, σ5, _, Lst5, xt5, xr5, replyRemove_split hkr hrt hsp hul, hsp, hkt5, hkr5, rfl, hX6,
    hF5.trans hF6, hN6, hI6, hCR6, hRP6, hRF6, hcs6, hw⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-! ## An SC's thread holds it (P1's `TSc`) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **An SC's thread has that SC** (P1's `TSc`, through the scheduler
relation). -/
theorem scBack_of {N T C Cs Ω Sg Rp Scs Nt : Set U64} {Zb : U64 → Nat} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {T' : Set U64} (hX : P1.XInv st T' Cs Ω Sg Rp Scs Nt Zb s)
    (hTT : T' = T)
    {q : U64} (hq : q ∈ C) (hqS : q ∈ Scs) (hq0 : q ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap q.bv = some (.schedContext y n)) {f : Fl4Spec.ObjRef} (hf : y.scTcb = some f) :
    ∃ u ∈ T, u.bv = f ∧ ∃ x, σ.kheap f = some (.tcb x) ∧ x.tcbSchedContext = some q.bv := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y', n', hk', hx⟩ := hs.scs q hq
  rw [hk] at hk'; cases hk'
  have h24 := hx.tcb
  rw [hf] at h24
  obtain ⟨h0, hbv⟩ := Notif.optRef_some h24.symm
  have h0' : L.mem s (scTcbA q) ≠ 0#u64 := by rw [scTcbA_eq]; exact h0
  have huT : L.mem s (scTcbA q) ∈ T := hTT ▸ hX.2.2.yt.1 q hqS h0'
  have htsc : L.mem s (scA (L.mem s (scTcbA q))) = q := hX.2.2.tsc q hqS hq0 h0'
  rw [scTcbA_eq] at huT htsc
  obtain ⟨xu, hku, -, -, hsu, -⟩ := hs.tcb _ huT
  rw [hbv] at hku
  exact ⟨_, huT, hbv, xu, hku, by rw [hsu, htsc, Notif.optRef_ne hq0]⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-! ## The caller's core -/

/-- **The caller sits on the core of the SC its reply heads** (P1's
`reply_remove.kwA` premise): a reply whose `NEXT` word has the head bit is
the head of an SC's stack (`CallRel`: a detached reply's bit is clear, a
reply further down names a reply), that SC's word with the bit cleared; the
TCBs and the SCs of `Z.C` are on core `Z.c` (`SchedCore.aff`,
`SchedRel.core`). -/
theorem JAtZ.rmCore (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : U64} (hr : r ∈ Z.R)
    (ht : t ∈ Z.T) : headBit (L.mem s (rNextA r)) = true →
      L.mem s (P1.affA t) = L.mem s (P1.scCoreA (L.mem s (rNextA r) &&& ~~~1#u64)) := by
  intro hb
  have hSR := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSR.lists
  obtain ⟨sc, hsc, hrL⟩ : ∃ sc ∈ Z.C, r ∈ Lst sc := by
    by_contra hno
    have hd : Detached Z.C Lst r := fun sc hsc hm => hno ⟨sc, hsc, hm⟩
    have h1 := (J.call.det r hr hd).1
    unfold headBit at hb
    rw [h1] at hb
    simp at hb
  obtain ⟨-, hLR, -, hSW⟩ := J.call.stack sc hsc
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hrL
  have hn := (hSW.2 i hi).2
  rw [hix] at hn
  cases i with
  | zero =>
    have hsc2 : sc.val % 2 = 0 := by
      obtain ⟨x, n', -, hx⟩ := hs.scs sc hsc
      have := hx.bounds.1; omega
    have hn' : L.mem s (rNextA r) = sc ||| 1#u64 := hn
    rw [hn', or1_and_not1 sc hsc2, hc.aff t ht, Fl4Proofs.P3.Sched.scCoreA_eq, hSR.core sc hsc]
  | succ j =>
    exfalso
    have hn' : L.mem s (rNextA r) = (Lst sc).getD j 0#u64 := hn
    have hev : ((Lst sc).getD j 0#u64).val % 2 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases h : (Lst sc)[j]? with
      | none => simp
      | some d =>
        have hd := hLR d (List.mem_of_getElem? h)
        have h32 := (J.rp.align d hd).1
        show d.val % 2 = 0
        omega
    rw [hn', headBit_even hev] at hb
    cases hb

/-! ## The footprint -/

/-- The replies' and `C`'s SCs' words (module docstring). -/
def RmX (R C : Set U64) (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  (∃ r ∈ R, r.val ≤ b.val ∧ b.val < r.val + 32) ∨ ScObjW C σ b

/-- **`reply_remove`'s footprint**: `FinW` and `RmX`. -/
def RmW (T N C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  FinW (st := st) T N C c s σ b ∨ RmX R C σ b

/-- `RmW`'s words are words of the other objects (`OObj`). -/
theorem RmW.oobj {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} (hS : Sched.SchedRel st N T C c s σ) {b : U64}
    (h : RmW (st := st) T N C R c s σ b) : Vs.OObj st N T C E R B c s σ b := by
  rcases h with h | ⟨r, hr, h1, h2⟩ | ⟨sc, hsc, x, n, hk, ho⟩
  · exact CnW.oobj hS (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, h1, h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hk, ho⟩))))))

theorem JAtZ.rmW_of (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (fun b => KFoot st Z.T Z.N Z.C Z.c s σ b ∨ CallW Z.R Z.C b)) :
    P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ) := by
  have hS := J.xtop.fin.1.1.1
  refine hw.mono fun b hb => ?_
  rcases hb with hb | (⟨r, hr, e | e⟩ | ⟨q, hq, rfl⟩) | ⟨r, hr, rfl⟩
  · exact Or.inl (Or.inl hb)
  · have := rNextA_val (J.rp.align r hr); subst e
    exact Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩)
  · have := rPrevA_val (J.rp.align r hr); subst e
    exact Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩)
  · obtain ⟨Q, R0, -, hs⟩ := hS.lists
    obtain ⟨x, n, hk, -⟩ := hs.scs q hq
    obtain ⟨-, hv, hsz⟩ := sc_reply_word hS hq
    have := hsz x n hk
    exact Or.inr (Or.inr ⟨q, hq, x, n, hk, by unfold Sched.ScObj; constructor <;> omega⟩)
  · have := rTcbA_val (J.rp.align r hr)
    exact Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩)

/-- An `RmX` word lies in no TCB. -/
theorem JAtZ.rmX_tcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (h : RmX Z.R Z.C σ b) :
    ∀ y ∈ Z.T, b.val < y.val ∨ y.val + 4096 ≤ b.val := by
  intro y hy
  rcases h with ⟨r, hr, h1, h2⟩ | ⟨sc, hsc, x, n, hk, ho⟩
  · have hH := J.kern.heap
    have hrH := J.zH.2.2.1 r hr
    have hyH := J.zH.1 y hy
    have hne : r ≠ y := fun e => by rw [e, hyH] at hrH; cases hrH
    have := hH.disj r _ y _ hrH hyH hne
    simp only [P1.HKind.bits] at this
    omega
  · exact (J.xtop.fin.1.1.1.scOut sc hsc x n hk b ho).2.2.1 y hy

/-- **An `RmW` word is no TCB's VCPU word** (KENTRY-PLAN g2b). -/
theorem JAtZ.rmW_nv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (hb : RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ b) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  have hS := J.xtop.fin.1.1.1
  intro t ht
  rcases hb with hb | hx
  · exact FinW.nv hS hb t ht
  · rintro rfl
    obtain ⟨Q, R0, hc, -⟩ := hS.lists
    have hv : (tVcpuA t).val = t.val + 3664 := tfield_val (hc.tcbs t ht) (K := 3664#u64) (by simp)
    have := J.rmX_tcb hx t ht; omega

/-- **The frame words an `RmW` step keeps** (`cnW_keeps`). -/
theorem JAtZ.rmW_keeps (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have tsw : ∀ b, FinW (st := st) Z.T Z.N Z.C Z.c s σ b → TSW Z.T Z.C b := fun b hb => FinW.tsw hS hb
  have tcbX : ∀ t ∈ Z.T, ∀ b : U64, (b.val = t.val + 3440 ∨ b.val = t.val + 3472 ∨ b.val = t.val + 3512) →
      ¬ RmX Z.R Z.C σ b := fun t ht b hv hx => by
    have := J.rmX_tcb hx t ht; omega
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) fun hb => ?_,
    fun t ht => hw.mem_eq (yieldA_aligned hT ht) fun hb => ?_,
    fun t ht => hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => ?_⟩
  · rcases hb with hb | hb
    · exact ((tsw _ hb).1 t ht).1 (mcpA_val hT ht)
    · exact tcbX t ht _ (Or.inl (mcpA_val hT ht)) hb
  · rcases hb with hb | hb
    · exact ((tsw _ hb).1 t ht).2.1 (yieldA_val hT ht)
    · exact tcbX t ht _ (Or.inr (Or.inl (yieldA_val hT ht))) hb
  · rcases hb with hb | hb
    · exact ((tsw _ hb).1 t ht).2.2 (tIpcBufA_val (hT t ht))
    · exact tcbX t ht _ (Or.inr (Or.inr (tIpcBufA_val (hT t ht)))) hb

/-- **The header words of `H`'s SCs outside `Z.C` are kept** by an `RmW`
step. -/
theorem JAtZ.rmW_scOut (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hfit := hH.fits q _ hq
  simp only [P1.HKind.bits] at hfit
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have scC : ∀ sc ∈ Z.C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ b : U64, Sched.ScObj sc n b →
      b = scW q K → False := fun sc hsc x n hk b ho e => by
    subst e
    have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
    have := hH.disj q _ sc _ hq hHs hne
    simp only [P1.HKind.bits] at this
    unfold Sched.ScObj at ho
    omega
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases hb with hb | hb
  · rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hHy : H y = some .tcb := J.zH.1 y hy
      have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
      have := hH.disj q _ y _ hq hHy hne
      simp only [P1.HKind.bits] at this
      omega
    · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
      have := J.kern.hnd q _ hq Z.c hcC
      simp only [P1.HKind.bits] at this
      omega
    · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
      have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
      have := hH.disj q _ n _ hq hHn hne
      simp only [P1.HKind.bits] at this
      omega
    · exact scC sc hsc x n hk _ ⟨g1, g2⟩ rfl
  · rcases hb with ⟨r, hr, h1, h2⟩ | ⟨sc, hsc, x, n, hk, ho⟩
    · have hrH := J.zH.2.2.1 r hr
      have hne : q ≠ r := fun e => by rw [e, hrH] at hq; cases hq
      have := hH.disj q _ r _ hq hrH hne
      simp only [P1.HKind.bits] at this
      omega
    · exact scC sc hsc x n hk _ ho rfl

/-- **The IRQ node's caps are kept** by an `RmW` step. -/
theorem JAtZ.rmW_irq (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ)) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  refine irqNode_keep hw hkf J.kern.ksbAl (fun b hb => ?_) i hi
  rcases hb with hb | hb
  · rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
    · simp only [P1.LawfulStore.nodeBase] at g1; omega
    · have := J.nk n hn; omega
    · have := (hS.scOut sc hsc x n hk b ⟨g1, g2⟩).2.2.2; omega
  · rcases hb with ⟨r, hr, h1, h2⟩ | ⟨sc, hsc, x, n, hk, ho⟩
    · have := hJ.ks r _ (J.zH.2.2.1 r hr) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
    · have := (hS.scOut sc hsc x n hk b ho).2.2.2; omega

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after an `RmW` step** (`cnW_utc`). -/
theorem JAtZ.rmW_utc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hw.1
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
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases hb with hb | hb
    · rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
      · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
        have := U.free y .tcb hth
        simp only [objSize] at this; omega
      · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
        omega
      · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
        have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
        simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
        omega
      · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
        simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
        rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
        omega
    · rcases hb with ⟨r, hr, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
      · obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
        have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) r.bv _ hx
        simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this
        omega
      · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
        simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
        rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
        omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

/-! ## The call stacks of `JAtZ` -/

/-- A stack's SC's `REPLY` word names its head, nonzero when the stack is
nonempty. -/
theorem JAtZ.scReply_ne (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} (hq : q ∈ Z.C)
    (hne : Lst q ≠ []) : L.mem s (P1.scReplyA q) ≠ 0#u64 := by
  obtain ⟨-, hLR, -, hSW⟩ := J.call.stack q hq
  obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil hne
  have hd : d ∈ Z.R := hLR d (by rw [hds]; exact List.mem_cons_self ..)
  rw [hSW.1, hds]
  exact (J.rp.align d hd).2.1

/-- **The idle thread holds no call stack** (P1's `idle`: the `REPLY` word
of an SC bound to the idle thread is 0). -/
theorem JAtZ.idle_noStack (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : Fl4Spec.ObjRef}
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap q = some (.schedContext y n)) {r : Fl4Spec.ObjRef}
    (hr : r ∈ y.scReplies) (hyt : y.scTcb = some σ.idleThread) : False := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨q', hq', rfl⟩ := J.obj.sc q y n hk
  obtain ⟨⟨y1, n1, hk1, hyL⟩, -, -, -⟩ := J.call.stack q' hq'
  rw [hk] at hk1; cases hk1
  have hne : Lst q' ≠ [] := by
    intro e; rw [hyL, e] at hr; simp at hr
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hqS : q' ∈ P1.Heap.scs H := ⟨_, (hJ.sc q' y n (J.c0 q' hq') hk).2⟩
  have h24 : L.mem s (scW q' 24#u64) = L.idleW s := by
    obtain ⟨y', n', hk', hx⟩ := hs.scs q' hq'
    rw [hk] at hk'; cases hk'
    have h := hx.tcb
    rw [hyt, hs.idleTh] at h
    obtain ⟨-, hbv⟩ := Notif.optRef_some h.symm
    have e := P1.eq_of_bv hbv
    rw [e]
    unfold nodeW P1.LawfulStore.idleW
    rw [hc.cur]
  have := J.blk.2.2.1.2.1.idle q' hqS (by rw [scTcbA_eq]; exact h24)
  exact J.scReply_ne hq' hne this

/-- A dead SC holds no call stack: it is in `Z.C`, its ghost stack empty and
its `REPLY` word 0. -/
theorem JAtZ.dead_sc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q' : U64} (hq' : q' ∈ D)
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap q'.bv = some (.schedContext y n)) :
    q' ∈ Z.C ∧ Lst q' = [] ∧ L.mem s (P1.scReplyA q') = 0#u64 ∧ y.scReplies = [] := by
  obtain ⟨q2, hq2, e2⟩ := J.obj.sc _ y n hk
  obtain rfl : q2 = q' := P1.eq_of_bv e2
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hz := (hJ.sc q2 y n (J.c0 q2 hq2) hk).2
  have h0 := ((J.jcov.dead q2 hq').2.2.2.2 _ hz).2.1
  have hL : Lst q2 = [] := by
    by_contra hne; exact J.scReply_ne hq2 hne h0
  obtain ⟨⟨y1, n1, hk1, hyL⟩, -⟩ := J.call.stack q2 hq2
  rw [hk] at hk1; cases hk1
  exact ⟨hq2, hL, h0, by rw [hyL, hL]; rfl⟩

/-- A notification outside `W` across an `LK W` step. -/
theorem lk_ntfnAt {W : Fl4Spec.ObjRef → Prop} {σ σ' : Fl4Spec.State Unit} (h : LK W σ σ') {p : Fl4Spec.ObjRef}
    (hp : ¬ W p) {x : Fl4Spec.Notification} (hk : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) := by
  have h1 := (h p).resolve_left hp
  rw [hk] at h1
  cases e : σ'.kheap p with
  | none => rw [e] at h1; exact h1.elim
  | some o =>
    rw [e] at h1
    have h2 : LObj (.notification x) o := h1
    obtain ⟨y, rfl, hy⟩ := h2.2.2 x rfl
    exact ⟨y, rfl, hy⟩

/-- An SC outside `W` across an `LK W` step. -/
theorem lk_scAt {W : Fl4Spec.ObjRef → Prop} {σ σ' : Fl4Spec.State Unit} (h : LK W σ σ') {p : Fl4Spec.ObjRef}
    (hp : ¬ W p) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext x n)) :
    ∃ y, σ'.kheap p = some (.schedContext y n) ∧ (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧
      (y.scNtfn = x.scNtfn ∨ y.scNtfn = none) := by
  have h1 := (h p).resolve_left hp
  rw [hk] at h1
  cases e : σ'.kheap p with
  | none => rw [e] at h1; exact h1.elim
  | some o =>
    rw [e] at h1
    have h2 : LObj (.schedContext x n) o := h1
    obtain ⟨y, rfl, hy1, hy2⟩ := h2.2.1 x n rfl
    exact ⟨y, rfl, hy1, hy2⟩

/-! ## The scheduler after the step (spec side) -/

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` after `reply_remove`**
(module docstring). -/
theorem JAtZ.replyRemoveJD (hT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {r t : U64} {x : Fl4Spec.Tcb} (hr : r ∈ Z.R) (ht : t ∈ Z.T) (hk : σ.kheap t.bv = some (.tcb x))
    (hst : x.tcbState = .blockedOnReply r.bv) :
    ipc.reply_remove st arI s a r t ⦃ res => res.2 = a ∧ ∃ σ' V' Ac' Lst' D',
      Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.1 res.2 σ' ∧
      SlotsSame Z.th (L.mem s) (L.mem res.1) ∧ L.ksb res.1 = L.ksb s ∧
      D' = D ∧ (∃ x', σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive) ∧
      (∀ q y n, σ'.kheap q = some (.schedContext y n) → y.scTcb = some t.bv → Fl4Spec.scActive y = true) ⦄ := by
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
  have hdc := J.rmCore hr ht
  -- the popped reply's SC goes back bound to another thread, or to none
  have hdon : ∀ sc ∈ Z.C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
      x.tcbSchedContext = none → (∃ f, f ∈ Z.T ∧ y.scTcb = some f.bv ∧ f ≠ t) ∨ y.scTcb = none := by
    intro sc hsc y n hky _ hxn
    cases hyt : y.scTcb with
    | none => exact Or.inr rfl
    | some g =>
      left
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hqS : sc ∈ P1.Heap.scs H := ⟨_, (hJ.sc sc y n (J.c0 sc hsc) hky).2⟩
      obtain ⟨u, hu, eu, xu, hku, hxu⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hsc hqS (J.c0 sc hsc) hky hyt
      refine ⟨u, hu, by rw [eu], fun e => ?_⟩
      subst e
      rw [← eu, hk] at hku
      cases hku
      rw [hxn] at hxu
      cases hxu
  refine WP.spec_mono (WP.spec_and
    (Ipc.remove_topJ (ar := arI) J.ip hI J.call J.rp J.nsc J.inv J.c0 J.obj.sc J.rfree hr ht hk hst hkr hrt hdon)
    (P1.ipc.reply_remove.kwA (Es := P1.EH H) hT s a r t J.blk hrH htH hrt_m hst_m hdc)) ?_
  rintro ⟨s', a'⟩ ⟨⟨rfl, σ5, σ', Lst', x5, xr5, hrm, hsp, hk5t, hk5r, hσ', hIR, hF, hN', hI', hCR', hRP', hRF',
    hcs, hw0⟩, hblk, -, hfoot, -, -⟩
  dsimp only at hrm hsp hk5t hk5r hσ' hIR hF hN' hI' hCR' hRP' hRF' hcs hw0 hblk hfoot ⊢
  refine ⟨rfl, ?_⟩
  have hmem : ((), σ') ∈ (Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ).1 := by rw [hrm]; exact Set.mem_singleton _
  have hks : L.ksb s' = L.ksb s := hF.2
  have hw := J.rmW_of hw0
  -- the spec's step: the call-stack part, then the unlink
  have hK : ScTKw (fun _ => False) σ σ5 := NKT.of_eq (nkt_replyRemoveSc t.bv r.bv) hsp
  obtain ⟨q, hqk, hQ, hD, hL⟩ := rmSc_donV hk hsp
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
  have hsF : Vs.rsF σ' = Vs.rsF σ := Vs.rsf_replyRemove t.bv r.bv σ ((), σ') hmem
  simp only [Vs.rsF, Prod.mk.injEq] at hsF
  obtain ⟨hidle', hcsc', hcons', htime', hisc'⟩ := hsF
  have hRQ : RelQ.RQK σ σ' := RelQ.rq_replyRemove' t.bv r.bv σ ((), σ') hmem
  have hCK : Fl4Proofs.P3.CKeep σ σ' := nkc_replyRemove t.bv r.bv σ ((), σ') hmem
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
  have hiso : IpcSorted σ' := QPK.QPS.sorted (QPK.qp_replyRemove t.bv r.bv σ ((), σ') hmem) J.isorted
  -- the frames
  obtain ⟨k1, k2, kb⟩ := J.rmW_keeps hw
  have hyk : YKeep σ σ' := (YK.yk_replyRemove' t.bv r.bv σ ((), σ') hmem).ykeep
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
  -- the receiver's SCs after are active (`remove_act`, from `BlockedScActive` before)
  have hact : ∀ q y n, σ'.kheap q = some (.schedContext y n) → y.scTcb = some t.bv → Fl4Spec.scActive y = true :=
    remove_act J.bsa hk hst hsp (fun q y n hq => by
      have h1 : q ≠ t.bv := by rintro rfl; rw [kt'] at hq; cases hq
      have h2 : q ≠ r.bv := by rintro rfl; rw [kr'] at hq; cases hq
      rw [ko' q h1 h2] at hq; exact hq)
  exact ⟨σ', Z.vs, Ac, Lst', D, hrm, J.cs_frameI hks hX3 hw (fun b hb => RmW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.rmW_nv hb) harch hao szk hF.1 hkb
    ((IpcFrKeep.of_otk hK.kh).trans (IpcFrKeep.of_upd2 hk5t kt' rfl rfl hk5r kr'
      (IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) ko'))
    hC R hKd hCK.orig (J.idleW_keep hIR.2.2.1 hidle' hisc').1 J.zD, hF.1, hks, rfl, ⟨_, kt', rfl⟩, hact⟩

/-- **`reply_remove` at `J`** (`replyRemoveJD` without the dead set kept and
the thread's `Inactive` after). -/
theorem JAtZ.replyRemoveJ (hT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {r t : U64} {x : Fl4Spec.Tcb} (hr : r ∈ Z.R) (ht : t ∈ Z.T) (hk : σ.kheap t.bv = some (.tcb x))
    (hst : x.tcbState = .blockedOnReply r.bv) :
    ipc.reply_remove st arI s a r t ⦃ res => res.2 = a ∧ ∃ σ' V' Ac' Lst' D',
      Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.1 res.2 σ' ∧
      SlotsSame Z.th (L.mem s) (L.mem res.1) ∧ L.ksb res.1 = L.ksb s ⦄ :=
  WP.spec_mono (J.replyRemoveJD hT hr ht hk hst) fun _ ⟨h1, σ', V', Ac', Lst', D', h2, h3, h4, h5, _⟩ =>
    ⟨h1, σ', V', Ac', Lst', D', h2, h3, h4, h5⟩

end

end

end Fl4Proofs.P3
