/-
P3 (DESIGN.md §9), VSpace: **the reply of the invocations that reply
themselves, for the composite relation** (`GetAddress`,
`TestAndClearAccessed`): FL4's `vspace::reply1` (the badge, `MR0` and
message-info registers of the current thread, then `set_thread_state
Running`) against the spec's `reply_from_kernel` and `set_thread_state
Running`.

* `sagree_wr_reg`, `ntfn_upd_fieldsNE`: the scheduler and notification
  relations across a write to a TCB register word.
* `regw_top`: a register write of the current thread keeps the ASID and
  page-table relations and `TopSR` (the endpoint relation by
  `Endp.write_reg_rel`, the scheduler relation by `SAgree`, the others by
  frames), with the spec's `as_user (set_register r v)`.
* `sts_top`: `set_thread_state ts` of the current, runnable thread
  (`restart_top` for any `ts` below 3).

`TopSR`'s `OthersRel` carries the endpoint and notification relations
separately; moving it to `IpcRel` (with the TCBs' SC words) is a follow-up.
-/
import Fl4Proofs.P3.VsTopX
import Fl4Proofs.P3.VsTopInst
import Fl4Proofs.P3.TcbRel
import Fl4Proofs.P3.EpFaultNone
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A write to a register word of a TCB keeps what `SchedRel` reads. -/
theorem sagree_wr_reg {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t a : U64} (ht : t ∈ T) (ha : Aligned a)
    (h1 : t.val + 256 ≤ a.val) (h2 : a.val < t.val + 448) (v : U64) : SAgree st T C c s (L.wr s a v) := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hta := hc.tcbs t ht
  have hN := hc.node
  have hal := hta.align
  have hko := hc.ksOut t ht
  have hnd := hN.disj t ht
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun o ho h8 _ _ _ _ _ => ?_, fun y hy K hK => ?_, ?_, ?_,
    fun sc hsc b hb hin => ?_⟩
  · refine L.mem_wr_ne ha (nodeAt_aligned hN ho h8) ?_
    rw [nodeAt_val hN ho]; omega
  · obtain ⟨k1, k2, -⟩ := schedField_ok hK
    have hya := hc.tcbs y hy
    refine L.mem_wr_ne ha (field_aligned hya k1 k2) ?_
    rw [tfield_val hya k1]
    by_cases e : y = t
    · subst e; rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
    · have hyl := hya.align
      have : y.val ≠ t.val := fun h => e (UScalar.eq_of_val_eq h)
      omega
  · have hkf := hN.fits
    refine L.mem_wr_ne ha ?_ ?_
    · have := hN.align
      unfold Aligned curDomA
      simp only [LawfulStore.nodeBase] at hkf this
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold curDomA
      simp only [LawfulStore.nodeBase] at hkf
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · have hkf := hN.fits
    refine L.mem_wr_ne ha ?_ ?_
    · have := hN.align
      unfold Aligned dtA
      simp only [LawfulStore.nodeBase] at hkf this
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold dtA
      simp only [LawfulStore.nodeBase] at hkf
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · obtain ⟨-, -, h3, -⟩ := hS.scOutIn hsc hin
    have := h3 t ht
    exact L.mem_wr_ne ha hb (by omega)

/-- **The scheduler relation across a TCB register write**, with the spec's
register update. -/
theorem SchedRel.wr_reg {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t a : U64} (ht : t ∈ T) (ha : Aligned a)
    (h1 : t.val + 256 ≤ a.val) (h2 : a.val < t.val + 448) (v : U64) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (w : Fl4Spec.Word) :
    SchedRel st N T C c (L.wr s a v) (updK σ t.bv (.tcb (setReg x r w))) := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hN := hc.node
  have ho : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      nodeW st (L.wr s a v) c o = nodeW st s c o := by
    intro o h8 h88
    have hta := hc.tcbs t ht
    have hnd := hN.disj t ht
    unfold nodeW
    rw [nodeAt_ksb (L.ksb_wr _ _ _)]
    refine L.mem_wr_ne ha (nodeAt_aligned hN h8 h88) ?_
    rw [nodeAt_val hN h8]; omega
  exact hS.of_sagree (sagree_wr_reg hS ht ha h1 h2 v) (ho _ (by simp [layout.node.SCHED_ACTION])
    (by simp [layout.node.SCHED_ACTION])) (ho _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
    (NtfnStep.weak (NtfnStep.tcb hk x.tcbState (setReg x r w).tcbArch))

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- **The notification relation across a register write** of a TCB: the
relation reads only the badge register of the TCB's registers. -/
theorem ntfn_wr_reg {S : Type} {st : machine.Store S} [L : LawfulStore st] (hPn : NPlaced T N)
    (hPe : EPlaced T E R B) {s : S} {σ : Fl4Spec.State Unit} (hR : NtfnStateRel N T (L.mem s) σ) {t : U64}
    (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (v : U64) :
    NtfnStateRel N T (L.mem (L.wr s (regA t (regIdx r)) v)) (updK σ t.bv (.tcb (setReg x r v.bv))) := by
  have hta := hPe.tcb t ht
  have hx := hR.at_tcb ht hk
  have ha := a_reg hta r
  have hrv := regA_val hta (regIdx_lt r)
  have hri := regIdx_lt r
  let P : Nat → Prop := fun u => u ≠ (regA t (regIdx r)).val
  have hA : ∀ b, Aligned b → P b.val → L.mem (L.wr s (regA t (regIdx r)) v) b = L.mem s b :=
    fun b hb hp => L.mem_wr_ne ha.1 hb (Ne.symm hp)
  refine hR.upd_tcb ht _ (fun n hn => nwordsEq_of (hPn.ntfn n hn) P hA fun k hk => ?_)
    (fun y hy hne => by
      have := tcb_disj hPe ht hy hne
      exact tfieldsEq_of (hPn.tcb y hy) P hA (by show _ ≠ _; omega) (by show _ ≠ _; omega)
        (by show _ ≠ _; omega) (by show _ ≠ _; omega))
    (fun y hy => by
      have hd : y = t ∨ (y.val + 4096 ≤ t.val ∨ t.val + 4096 ≤ y.val) := by
        by_cases e : y = t
        · exact Or.inl e
        · exact Or.inr (by have := tcb_disj hPe ht hy e; omega)
      rcases hd with rfl | hd
      · exact tlinksEq_of (hPn.tcb y hy) P hA (by show _ ≠ _; omega) (by show _ ≠ _; omega)
      · exact tlinksEq_of (hPn.tcb y hy) P hA (by show _ ≠ _; omega) (by show _ ≠ _; omega))
    (Or.inr ⟨hA _ (a_st hta).1 (by show _ ≠ _; rw [val_st hta]; omega),
      hA _ (a_blk hta).1 (by show _ ≠ _; rw [val_blk hta]; omega)⟩) ⟨?_, ?_, ?_, ?_⟩
  · have := hPn.disj n hn t ht; show _ ≠ _; omega
  · rw [hA _ (a_st hta).1 (by show _ ≠ _; rw [val_st hta]; omega)]; exact hx.st
  · intro n hn
    rw [hA _ (a_blk hta).1 (by show _ ≠ _; rw [val_blk hta]; omega)]; exact hx.blk n hn
  · show (L.mem _ (badgeRegA t)).bv = badgeOf (setReg x r v.bv)
    by_cases e : r = Fl4Spec.badge_register
    · subst e; rw [badgeOf_setReg, badgeRegA_eq_regA, rd_wr_eq ha.1]
    · have hb := a_reg hta Fl4Spec.badge_register
      rw [badgeRegA_eq_regA, hA _ hb.1 (by
        show _ ≠ _; rw [regA_val hta (regIdx_lt _)]
        intro h; exact e (regIdx_inj (by omega)).symm), ← badgeRegA_eq_regA]
      have : badgeOf (setReg x r v.bv) = badgeOf x := by
        simp only [badgeOf, setReg, setRegUc, Fl4Spec.archTcbContextSet, Fl4Spec.archTcbContextGet]
        exact Function.update_of_ne (Ne.symm e) _ _
      rw [this]; exact hx.badge
  · rw [setReg_prio, hA _ (a_prio hta).1 (by show _ ≠ _; rw [val_prio hta]; omega)]; exact hx.prio

end

/-! ### The spec's reply of one word -/

section Spec
open Fl4Spec

/-- The TCB after `reply_from_kernel (0, [v])`. -/
def replyTcb (x : Tcb) (v : Word) : Tcb :=
  setReg (setReg (setReg x badge_register 0) (mrIdx 0) v) msg_info_register
    (messageInfoToData ⟨natToLen 1, 0, 0, 0⟩)

theorem withRegs_one (x : Tcb) (v : Word) :
    withRegs x (mrRegs x.tcbArch.tcbContext.userRegs [v]) = setReg x (mrIdx 0) v := by
  have h0 : mrRegs x.tcbArch.tcbContext.userRegs [] = x.tcbArch.tcbContext.userRegs := by
    funext reg; simp [mrRegs]
  have h1 := mrRegs_snoc_lt x.tcbArch.tcbContext.userRegs [] v (by simp)
  simp only [List.nil_append, h0, List.length_nil] at h1
  rw [h1]; rfl

theorem setUm_self {Z : Type} (σ : State Z) : setUm σ σ.machineState.underlyingMemory = σ := rfl

/-- **`reply_from_kernel (0, [v])`**: one outcome, the TCB's badge, `MR0` and
message-info registers set. -/
theorem replyFromKernel_one {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (v : Word) :
    replyFromKernel (Z := Unit) t (0, [v]) σ = ({((), updK σ t (.tcb (replyTcb x v)))}, False) := by
  have hkA : (updK σ t (.tcb (setReg x badge_register 0))).kheap t = some (.tcb (setReg x badge_register 0)) := by
    simp
  set xA := setReg x badge_register 0
  set xB := setReg xA (mrIdx 0) v
  have hB : ∀ buf, setMrs (Z := Unit) t buf [v] (updK σ t (.tcb xA)) =
      ({(natToLen 1, updK (updK σ t (.tcb xA)) t (.tcb xB))}, False) := by
    intro buf
    cases buf with
    | none =>
      rw [setMrs_eqN hkA [v]]
      unfold mrStateN; rw [withRegs_one]; rfl
    | some p =>
      rw [setMrs_eq hkA p [v] (by intro q hq; simp [mrPairs] at hq)]
      unfold mrState
      rw [withRegs_one]
      rfl
  have hkB : (updK (updK σ t (.tcb xA)) t (.tcb xB)).kheap t = some (.tcb xB) := by simp
  unfold replyFromKernel
  rw [nd_pure_bind']
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hk true), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk),
    nd_bind_one (hB _)]
  unfold setMessageInfo
  rw [Notif.asUser_setRegister_eq _ _ hkB]
  simp only [Vs.updK_updK]
  rfl

end Spec

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-! ### The CSpace side -/

theorem KFoot.updK' {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (x' : Fl4Spec.Tcb) : KFoot σ (Notif.updK σ t (.tcb x')) := by
  refine ⟨rfl, rfl, fun o hne => ?_, rfl⟩
  rw [Notif.updK_kheap] at hne ⊢
  by_cases e : o = t
  · subst e; exact Or.inr (Or.inr ⟨x, x', hk, by rw [Function.update_self]⟩)
  · rw [Function.update_of_ne e] at hne; exact absurd rfl hne

/-- The CSpace relation reads only a TCB's caps. -/
theorem StateRel.tcb_upd {Z : Type} {th : TypedHeap} {m : U64 → U64} {σ σ1 : Fl4Spec.State Z}
    (hR : StateRel th m σ) {t : Fl4Spec.ObjRef} {tcb y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb tcb))
    (h1 : σ1.kheap = Function.update σ.kheap t (some (.tcb y)))
    (hy : ∀ i, Fl4Spec.tcbCnodeMap y i = Fl4Spec.tcbCnodeMap tcb i) : StateRel th m σ1 := by
  refine ⟨fun p r hp => ?_, fun t' ht' => ?_⟩
  · obtain ⟨cs, hk', hwf, hs⟩ := hR.cnode p r hp
    have hne : p.bv ≠ t := by intro e; rw [e, hk] at hk'; cases hk'
    exact ⟨cs, by rw [h1, Function.update_of_ne hne]; exact hk', hwf, hs⟩
  · obtain ⟨tcb', hk', hs⟩ := hR.tcb t' ht'
    by_cases he : t'.bv = t
    · rw [he, hk] at hk'
      cases hk'
      exact ⟨y, by rw [h1, he, Function.update_self], fun i hi => by rw [hy]; exact hs i hi⟩
    · exact ⟨tcb', by rw [h1, Function.update_of_ne he]; exact hk', hs⟩

/-- **The CSpace relation, `FinInv` and `MdbOKV` across a step** that keeps the
slot words and changes only TCBs, with the new `StateRel`. -/
theorem cspace_step {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {ksb : U64}
    (hCR : CRel th m σ G) (hFI : FinInv th m σ G) (hMO : MdbOKV ksb m G) (hSS : SlotsSame th m m')
    (hK : KFoot σ σ') (hSt : StateRel th m' σ') :
    CRel th m' σ' G ∧ FinInv th m' σ' G ∧ MdbOKV ksb m' G :=
  ⟨⟨hSt, SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy), hCR.2.2.1.of_same hSS,
      hCR.2.2.2.1.of_same hSS hK.1 hK.2.1, MdbInv.of_same hCR.2.2.1 hCR.2.2.2.2 hSS⟩,
    hFI.of_same hCR.2.2.1 hSS (KFoot.ksub hK), MdbOKV.of_same hCR.2.2.1 hSS hMO⟩

/-- A write to a TCB word past its cap slots keeps the slot words. -/
theorem slotsSame_tcbw {th : TypedHeap} (hP : Placed th) (s : S) {t w : U64} (ht : th t = some .tcb)
    (hw1 : t.val + 192 ≤ w.val) (hw2 : w.val < t.val + 4096) (hwa : Aligned w) (v : U64) :
    SlotsSame th (L.mem s) (L.mem (L.wr s w v)) := by
  refine slotsSame_wr hP s v hwa (fun a ha => ?_)
  obtain ⟨p, k, hk, h1, h2, h3⟩ := slot_in_object hP ha
  by_cases hpt : p = t
  · subst hpt; rw [ht] at hk; cases hk
    have := h3 rfl; simp [tcbSlots] at this; omega
  · have e4 : objSize ObjKind.tcb = 4096 := rfl
    rcases hP.disj p t k .tcb hk ht hpt with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **A register write of the current, runnable thread** for the composite
relation (see the module docstring). -/
theorem regw_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hcur : ct.bv = σ.curThread) (hk : σ.kheap ct.bv = some (.tcb x))
    (r : Fl4Spec.Register) (v : U64) :
    VsRel P (L.mem (L.wr s (Endp.regA ct (Endp.regIdx r)) v)) (L.ksb (L.wr s (Endp.regA ct (Endp.regIdx r)) v))
        (Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv))) ∧
      (PtRel L4 L3 L2 L1 (L.mem s) σ →
        PtRel L4 L3 L2 L1 (L.mem (L.wr s (Endp.regA ct (Endp.regIdx r)) v))
          (Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv)))) ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR (L.wr s (Endp.regA ct (Endp.regIdx r)) v) a
        (Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv))) ∧
      L.ksb (L.wr s (Endp.regA ct (Endp.regIdx r)) v) = L.ksb s ∧
      ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b →
        L.mem (L.wr s (Endp.regA ct (Endp.regIdx r)) v) b = L.mem s b := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT : ct ∈ T := by
    have : ct = Sched.nodeW st s c layout.node.CUR_THREAD := eq_of_bv (hcur.trans hs.curThread)
    rw [this]; exact hc.curT
  have hta := hc.tcbs ct hT
  set w := Endp.regA ct (Endp.regIdx r) with hw
  set σ1 := Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv)) with hσ1
  have ha := Endp.a_reg hta r
  have hrv : w.val = ct.val + 256 + 8 * (Endp.regIdx r).val := Endp.regA_val hta (Endp.regIdx_lt r)
  have hri := Endp.regIdx_lt r
  have hO1 : OObj st N T C E R B c s σ w := Or.inr (Or.inr (Or.inl ⟨ct, hT, by omega, by omega⟩))
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut ct hT
  have hksb : L.ksb (L.wr s w v) = L.ksb s := L.ksb_wr _ _ _
  have hmem : ∀ b, Aligned b → b ≠ w → L.mem (L.wr s w v) b = L.mem s b :=
    fun b hb h => Notif.rd_wr_ne ha.1 hb (Ne.symm h)
  have hmV : ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem (L.wr s w v) b = L.mem s b :=
    fun b hb hv => hmem b hb (fun e => hP.disj _ hO1 (e ▸ hv))
  have hmK : ∀ b : U64, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 →
      L.mem (L.wr s w v) b = L.mem s b :=
    fun b hb h1 h2 => hmem b hb (fun e => by rw [e, hrv] at h1 h2; have := hta.fits; omega)
  have hkp : ∀ q : Fl4Spec.ObjRef, (∀ y, σ.kheap q ≠ some (.tcb y)) → σ1.kheap q = σ.kheap q := by
    intro q hq
    rw [hσ1, Notif.updK_kheap, Function.update_of_ne]
    intro e; subst e; exact hq x hk
  have hVs : VsRel P (L.mem (L.wr s w v)) (L.ksb (L.wr s w v)) σ1 := by
    rw [hksb]
    refine hR.frame (fun b hb => hmV b (VsWrite.aligned hP.vs hb) (vsWrite_vobj hP.vs hb))
      rfl (fun p hp => hkp _ (fun y hy => ?_))
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    rw [hf] at hy; cases hy
  have hPt' : PtRel L4 L3 L2 L1 (L.mem s) σ → PtRel L4 L3 L2 L1 (L.mem (L.wr s w v)) σ1 := fun hPt => by
    refine hPt.frame (fun b hb => hmV b (PtWAll.aligned hP.pt hb) ?_) (fun q hq => hkp _ (fun y hy => ?_))
    · obtain ⟨q, hq, i, hi, rfl⟩ := hb
      exact table_vobj hP.pt hq hi _
    · obtain ⟨ao, hao⟩ := hPt.arch hq
      rw [hao] at hy; cases hy
  have hEp' := (Endp.write_reg_rel hP.ep s σ hEp hT hk r v).1
  have hN' := Endp.ntfn_wr_reg hSch.placed hP.ep hNt hT hk r v
  have hS' := Sched.SchedRel.wr_reg hSch hT ha.1 (a := w) (by rw [hrv]; omega) (by rw [hrv]; omega) v hk r v.bv
  have hKr' : KRootRel (L.mem (L.wr s w v)) (L.ksb (L.wr s w v)) σ1 := by
    unfold KRootRel globCr3 at hKr ⊢
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hksb, hmK _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega)]
    exact hKr
  refine ⟨hVs, hPt', ⟨⟨hS', hEp', hN', ?_, ?_, hKr', hAr⟩, ?_⟩, hksb, hmV⟩
  · rw [hksb]; exact IrqRel.ksFrame hIrq hkf hka hmK rfl rfl
  · rw [hksb]; exact IoRel.ksFrame hIo hkf hka hmK rfl
  · refine ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun y hy => ?_, fun y h1 h2 => ?_, hP.po, hP.ps,
      by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd, by rw [hksb]; exact hP.tko⟩
    · rw [hksb]
      refine hP.disj y (OObj.of_kh hksb (fun q z n hq => ?_) hy)
      rw [hσ1, Notif.updK_kheap] at hq
      by_cases e : q = ct.bv
      · subst e; rw [Function.update_self] at hq; cases hq
      · rwa [Function.update_of_ne e] at hq
    · have : L.nodeBase (L.wr s w v) c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
      rw [this] at h1 h2; exact hP.nodeE y h1 h2

set_option maxHeartbeats 4000000 in
/-- **`set_thread_state ts` of the current, runnable thread** for the
composite relation (`restart_top` for any `ts` below 3 and its code). -/
theorem sts_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hcur : ct.bv = σ.curThread) (hk : σ.kheap ct.bv = some (.tcb x))
    (hrun : Fl4Spec.runnable x.tcbState = true) (ts : Fl4Spec.ThreadState) (hts : Notif.tsCode ts < 3)
    (code : U64) (hv : code.val = Notif.tsCode ts) :
    sched.set_thread_state st s ct code ⦃ s' =>
      VsRel P (L.mem s') (L.ksb s') (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv) ∧
      (PtRel L4 L3 L2 L1 (L.mem s) σ →
        PtRel L4 L3 L2 L1 (L.mem s') (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv)) ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a
        (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv) ∧
      L.ksb s' = L.ksb s ∧
      ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem s' b = L.mem s b ⦄ := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT : ct ∈ T := by
    have : ct = Sched.nodeW st s c layout.node.CUR_THREAD := eq_of_bv (hcur.trans hs.curThread)
    rw [this]; exact hc.curT
  have hta := hc.tcbs ct hT
  have hN := hc.node
  have hcpu0 : L.cpu s = c := hc.cur
  have hqN := runnable_not_ntfnQ hNt hT hk hrun
  have hqE := Endp.not_queued hEp hT hk (by
    cases e : x.tcbState <;> simp_all [Notif.tsCode, Fl4Spec.runnable])
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv with hσ1
  obtain ⟨hist, hinode, harch, hms⟩ := stsAct_updK_fields σ ct.bv (.tcb { x with tcbState := ts })
  rw [← hσ1] at hist hinode harch hms
  -- the two words
  have hW1v : (stA ct).val = ct.val + 3328 := by rw [stA_eq]; exact Notif.tfield_val hta (by decide)
  have hW1a : Aligned (stA ct) := by
    unfold Aligned; rw [hW1v]; have := hta.align; omega
  set W2 := L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION with hW2
  have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have hoff8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  have hW2v : W2.val = L.nodeBase s c + layout.node.SCHED_ACTION.val := by
    rw [hW2, hcpu0]; exact nodeAt_val hN hoff
  have hW2a : Aligned W2 := by rw [hW2, hcpu0]; exact nodeAt_aligned hN hoff hoff8
  have hO1 : OObj st N T C E R B c s σ (stA ct) := by
    rw [stA_eq]; exact tcb_oobj hT hta (by decide) (by decide)
  have hO2 : OObj st N T C E R B c s σ W2 := Or.inl (by rw [hW2v]; omega)
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut ct hT
  refine WP.spec_mono (WP.spec_and (Sched.set_thread_state_refines s σ hNt hSch hT hk hqN _ ts hv
    (fun n h => by rw [h] at hts; simp [Notif.tsCode] at hts)) (set_thread_state_cases s ct code)) ?_
  rintro s' ⟨⟨σ', hst, hN', hS'⟩, hcase⟩
  have e1 : σ' = σ1 := by
    rw [Notif.setThreadState_eq ts hk] at hst
    have := congrArg Prod.fst hst
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e1
  have hksb : L.ksb s' = L.ksb s := by rcases hcase with rfl | rfl <;> simp
  have hmem : ∀ b, Aligned b → b ≠ stA ct → b ≠ W2 → L.mem s' b = L.mem s b := by
    intro b hb h1 h2
    rcases hcase with rfl | rfl
    · rw [L.mem_wr _ _ _ _ hW1a hb, if_neg (Ne.symm h1)]
    · rw [L.mem_wr _ _ _ _ (by rw [← hW2]; exact hW2a) hb, if_neg (by rw [← hW2]; exact Ne.symm h2),
        L.mem_wr _ _ _ _ hW1a hb, if_neg (Ne.symm h1)]
  have hmV : ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem s' b = L.mem s b :=
    fun b hb hv => hmem b hb (fun e => hP.disj _ hO1 (e ▸ hv)) (fun e => hP.disj _ hO2 (e ▸ hv))
  have hmK : ∀ b : U64, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 →
      L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hmem b hb (fun e => by rw [e, hW1v] at h1 h2; omega)
      (fun e => by rw [e, hW2v, hnb] at h1 h2; omega)
  have hkp : ∀ q : Fl4Spec.ObjRef, (∀ y, σ.kheap q ≠ some (.tcb y)) → σ1.kheap q = σ.kheap q := by
    intro q hq
    rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_of_ne]
    intro e; subst e; exact hq x hk
  -- the ASID and page-table relations
  have hVs : VsRel P (L.mem s') (L.ksb s') σ1 := by
    rw [hksb]
    refine hR.frame (fun b hb => hmV b (VsWrite.aligned hP.vs hb) (vsWrite_vobj hP.vs hb))
      (by rw [harch]) (fun p hp => hkp _ (fun y hy => ?_))
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    rw [hf] at hy; cases hy
  have hPt' : PtRel L4 L3 L2 L1 (L.mem s) σ → PtRel L4 L3 L2 L1 (L.mem s') σ1 := fun hPt => by
    refine hPt.frame (fun b hb => hmV b (PtWAll.aligned hP.pt hb) ?_) (fun q hq => hkp _ (fun y hy => ?_))
    · obtain ⟨q, hq, i, hi, rfl⟩ := hb
      exact table_vobj hP.pt hq hi _
    · obtain ⟨ao, hao⟩ := hPt.arch hq
      rw [hao] at hy; cases hy
  -- the endpoint relation
  have hEp1 := Endp.write_state_rel hP.ep s σ hEp hT hk hqE ts hts _ hv
  have hEp' : Endp.EpStateRel T E R B (L.mem s') σ1 := by
    obtain ⟨hR1, -, -⟩ := hEp1
    have hR1' : Endp.EpStateRel T E R B (L.mem (L.wr s (stA ct) code)) σ1 :=
      Endp.EpStateRel.frame hR1 hP.ep (fun _ _ _ => rfl) (Endp.KView.stsAct' _ _)
    rcases hcase with rfl | rfl
    · exact hR1'
    · refine Endp.EpStateRel.frame hR1' hP.ep (fun b hb hf => ?_) (Endp.KView.refl _)
      rw [L.mem_wr _ _ _ _ (by rw [← hW2]; exact hW2a) hb, if_neg]
      intro e
      have hb' : b = W2 := by rw [hW2]; simpa using e.symm
      subst hb'
      exact hP.nodeE _ (by rw [hW2v]; omega) (by rw [hW2v]; omega) hf
  have hKr' : KRootRel (L.mem s') (L.ksb s') σ1 := by
    unfold KRootRel globCr3 at hKr ⊢
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hksb, hmK _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega), harch]
    exact hKr
  refine ⟨hVs, hPt', ⟨⟨hS', hEp', hN', ?_, ?_, hKr', by rw [harch]; exact hAr⟩, ?_⟩, hksb, hmV⟩
  · rw [hksb]; exact IrqRel.ksFrame hIrq hkf hka hmK hist hinode
  · rw [hksb]; exact IoRel.ksFrame hIo hkf hka hmK (by rw [harch])
  · refine ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun y hy => ?_, fun y h1 h2 => ?_, hP.po, hP.ps,
      by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd, by rw [hksb]; exact hP.tko⟩
    · rw [hksb]
      refine hP.disj y (OObj.of_kh hksb (fun q z n hq => ?_) hy)
      rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap] at hq
      by_cases e : q = ct.bv
      · subst e; rw [Function.update_self] at hq; cases hq
      · rwa [Function.update_of_ne e] at hq
    · have : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
      rw [this] at h1 h2; exact hP.nodeE y h1 h2


/-! ### The bundle carried through the reply -/

/-- The domain-schedule words lie below `ksb + 256`. -/
theorem domSame_low {m m' : U64 → U64} {kb : U64} (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (h : ∀ b : U64, Aligned b → kb.val ≤ b.val → b.val < kb.val + 256 → m' b = m b) : DomSame m m' kb := by
  have hw : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → m' (ksW kb o) = m (ksW kb o) := fun o ho h8 => by
    have hv := ksW_val (kb := kb) (o := o) (by omega)
    exact h _ (ksW_al hkf hka ho h8) (by omega) (by omega)
  refine ⟨hw _ (by decide) (by decide), fun i hi => ⟨hw _ ?_ ?_, hw _ ?_ ?_⟩⟩ <;>
    first | (rw [entOff_val hi]; omega) | (rw [durOff_val hi]; omega)

/-- The relations the reply keeps: the CSpace relation, `FinInv`, `MdbOKV`,
the domain schedule and `FinX` at `TopSR`. -/
def RInv {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (c : U64) (AR : A → Fl4Spec.Cr3 → Prop) (G : MdbGhost) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ MdbOKV (L.ksb s) (L.mem s) G ∧
    DomRel (L.mem s) (L.ksb s) σ ∧ FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ

theorem RInv.relTop {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ) :
    RelTopM (L := L) s σ :=
  ⟨th, G, h.2.2.2.2.1.2.pl, h.1, h.2.1, h.2.2.2.1, h.2.2.1⟩

theorem TopSR.cur_mem {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {ct : U64} (hcur : ct.bv = σ.curThread) : ct ∈ T := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.1.1.lists
  have : ct = Sched.nodeW st s c layout.node.CUR_THREAD := eq_of_bv (hcur.trans hs.curThread)
  rw [this]; exact hc.curT

/-- **A register write of the current thread keeps `RInv`.** -/
theorem regw_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (r : Fl4Spec.Register) (v : U64) :
    RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G (L.wr s (Endp.regA ct (Endp.regIdx r)) v) a
      (Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv))) := by
  obtain ⟨hCR, hFI, hMO, hDom, hS, hR, hPt, hPI, hCur⟩ := hI
  obtain ⟨hR', hPt', hS', hksb, hmV⟩ := regw_top s a σ ct x hS hR hcur hk r v
  have hT := hS.cur_mem hcur
  obtain ⟨Q, R0, hc, -⟩ := hS.1.1.lists
  have hta := hc.tcbs ct hT
  have ha := Endp.a_reg hta r
  have hrv := Endp.regA_val hta (Endp.regIdx_lt r)
  have hri := Endp.regIdx_lt r
  have hSS := slotsSame_tcbw (st := st) hS.2.pl s htcb (w := Endp.regA ct (Endp.regIdx r)) (by omega) (by omega) ha.1 v
  have hK := KFoot.updK' hk (Notif.setReg x r v.bv)
  have hSt : StateRel th (L.mem (L.wr s (Endp.regA ct (Endp.regIdx r)) v))
      (Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv))) :=
    (StateRel.tcb_upd (y := Notif.setReg x r v.bv) hCR.1 hk rfl (fun _ => rfl)).of_caps (fun y hy => hSS.capAt hy)
  obtain ⟨hCR', hFI', hMO'⟩ := cspace_step hCR hFI hMO hSS hK hSt
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hS.2.vs.ksb_fit; omega
  have hka := hS.2.vs.ksb_al
  have hko := hc.ksOut ct hT
  have hDom' : DomRel (L.mem (L.wr s (Endp.regA ct (Endp.regIdx r)) v)) (L.ksb s)
      (Notif.updK σ ct.bv (.tcb (Notif.setReg x r v.bv))) :=
    hDom.of_same (domSame_low hkf hka fun b hb h1 h2 =>
      Notif.rd_wr_ne ha.1 hb (fun e => by rw [← e, hrv] at h1 h2; omega)) rfl rfl
  refine ⟨hCR', hFI', by rw [hksb]; exact hMO', by rw [hksb]; exact hDom', hS', hR', hPt' hPt, ?_,
    CurOK.of_same hCur hSS rfl⟩
  intro q hq lo hl
  have hw : VsWrite P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
  rw [hmV _ (hw.aligned hS.2.vs) (vsWrite_vobj hS.2.vs hw)]
  exact hPI q hq lo hl

/-- **`set_thread_state ts` of the current, runnable thread keeps `RInv`.** -/
theorem sts_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (ts : Fl4Spec.ThreadState) (hts : Notif.tsCode ts < 3) (code : U64) (hv : code.val = Notif.tsCode ts) :
    sched.set_thread_state st s ct code ⦃ s' =>
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s' a
        (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv) ∧
      L.mem s' (stA ct) = code ∧ L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION =
        L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ⦄ := by
  obtain ⟨hCR, hFI, hMO, hDom, hS, hR, hPt, hPI, hCur⟩ := hI
  have hT := hS.cur_mem hcur
  obtain ⟨Q, R0, hc, -⟩ := hS.1.1.lists
  have hta := hc.tcbs ct hT
  have hko := hc.ksOut ct hT
  have hN := hc.node
  have hcpu0 : L.cpu s = c := hc.cur
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hS.2.vs.ksb_fit; omega
  have hka := hS.2.vs.ksb_al
  have hW1v : (stA ct).val = ct.val + 3328 := by rw [stA_eq]; exact Notif.tfield_val hta (by decide)
  have hW1a : Aligned (stA ct) := by unfold Aligned; rw [hW1v]; have := hta.align; omega
  have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have hoff8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  set W2 := L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION with hW2
  have hW2v : W2.val = L.nodeBase s c + layout.node.SCHED_ACTION.val := by
    rw [hW2, hcpu0]; exact nodeAt_val hN hoff
  have hW2a : Aligned W2 := by rw [hW2, hcpu0]; exact nodeAt_aligned hN hoff hoff8
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  refine WP.spec_mono (WP.spec_and (WP.spec_and (sts_top s a σ ct x hS hR hcur hk hrun ts hts code hv)
    (set_thread_state_slots th hS.2.pl s ct code htcb hact)) (set_thread_state_cases s ct code)) ?_
  rintro s' ⟨⟨⟨hR', hPt', hS', hksb, hmV⟩, hSS⟩, hcase⟩
  have hmem : ∀ b, Aligned b → b ≠ stA ct → b ≠ W2 → L.mem s' b = L.mem s b := by
    intro b hb h1 h2
    rcases hcase with rfl | rfl
    · rw [L.mem_wr _ _ _ _ hW1a hb, if_neg (Ne.symm h1)]
    · rw [L.mem_wr _ _ _ _ (by rw [← hW2]; exact hW2a) hb, if_neg (by rw [← hW2]; exact Ne.symm h2),
        L.mem_wr _ _ _ _ hW1a hb, if_neg (Ne.symm h1)]
  have hst' : L.mem s' (stA ct) = code := by
    rcases hcase with rfl | rfl
    · rw [L.mem_wr _ _ _ _ hW1a hW1a, if_pos rfl]
    · rw [L.mem_wr _ _ _ _ (by rw [← hW2]; exact hW2a) hW1a, if_neg, L.mem_wr _ _ _ _ hW1a hW1a, if_pos rfl]
      intro e; rw [← hW2] at e
      have := congrArg UScalar.val e; rw [hW1v, hW2v, hnb] at this
      have := hN.disj ct hT; omega
  have hcpu : L.cpu s' = L.cpu s := by rcases hcase with rfl | rfl <;> simp
  have hK := KFoot.sts hk { x with tcbState := ts }
  have hSt := (hCR.1.tcb_state hk (ts := ts) (σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv)
    (by rw [Notif.stsAct_kheap, Notif.updK_kheap])).of_caps (fun y hy => hSS.capAt hy)
  obtain ⟨hCR', hFI', hMO'⟩ := cspace_step hCR hFI hMO hSS hK hSt
  have hdl : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv).domainList = σ.domainList ∧
      (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv).domainStartIndex =
        σ.domainStartIndex := by
    unfold Notif.stsAct; split <;> exact ⟨rfl, rfl⟩
  have hct : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv).curThread = σ.curThread := by
    unfold Notif.stsAct; split <;> rfl
  have hDom' : DomRel (L.mem s') (L.ksb s) (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := ts })) ct.bv) :=
    hDom.of_same (domSame_low hkf hka fun b hb h1 h2 => hmem b hb
      (fun e => by rw [e, hW1v] at h1 h2; omega) (fun e => by rw [e, hW2v, hnb] at h1 h2; omega)) hdl.1 hdl.2
  refine ⟨⟨hCR', hFI', by rw [hksb]; exact hMO', by rw [hksb]; exact hDom', hS', hR', hPt' hPt, ?_,
    CurOK.of_same hCur hSS hct⟩, hst', by rw [hcpu]; exact Sched.nodeAt_ksb hksb _ _⟩
  intro q hq lo hl
  have hw : VsWrite P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
  rw [hmV _ (hw.aligned hS.2.vs) (vsWrite_vobj hS.2.vs hw)]
  exact hPI q hq lo hl

/-- The spec's `reply_from_kernel (0, [v])` then `Running`, after the state
of a `Restart` thread is read (`specTail`). -/
theorem specTail_restart {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hrs : x.tcbState = .restart) (call : Bool) (v : Fl4Spec.Word) :
    specTail call t [v] σ = Fl4Spec.setThreadState (Z := Unit) t .running
      (if call then Notif.updK σ t (.tcb (Endp.replyTcb x v)) else σ) := by
  unfold specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk)]
  simp only [hrs]
  cases call
  · rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind']; rfl
  · unfold Fl4Spec.NonDet.when; simp only [↓reduceIte]; rw [nd_bind_one (Endp.replyFromKernel_one hk v)]

theorem msg_info_one_bv : (Fl4Spec.messageInfoToData
    ⟨(1#u64 : U64).bv, 0, 0, (0#u64 : U64).bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩) =
    Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ := by
  congr 1

set_option maxHeartbeats 4000000 in
/-- **`reply1` of the current, runnable thread keeps `RInv`**: the reply
registers when called, then `Running`. -/
theorem reply1_core {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrx : Fl4Spec.runnable x.tcbState = true)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s2 a (Notif.stsAct (Notif.updK σ ct.bv
        (.tcb { (if call then Endp.replyTcb x v.bv else x) with tcbState := .running })) ct.bv) ⦄ := by
  have hrs : x.tcbState = x.tcbState := rfl
  have hrun : ∀ y : Fl4Spec.Tcb, y.tcbState = x.tcbState → Fl4Spec.runnable y.tcbState = true := by
    intro y h; rw [h]; exact hrx
  have hne : sched.TS_RUNNING ≠ sched.TS_RESTART := by unfold sched.TS_RUNNING sched.TS_RESTART; decide
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  unfold vspace.reply1
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (sts_inv s a σ hI ct htcb hcur hk (hrun x hrs) hact .running (by decide) _ hcode) ?_
    rintro s' ⟨hI', hst', -⟩
    exact ⟨by rw [hst']; exact hne, hI'⟩
  · simp only [↓reduceIte]
    have hin : (do
        let buf ← msg.lookup_ipc_buffer st s true ct
        let s2 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
        let (n, s3) ← msg.set_mr st s2 ct buf 0#u64 v
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
        msg.set_msg_info st s3 ct mi) ⦃ s3 => ∃ w : U64,
          s3 = L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
            (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
          w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true ct L.total) ?_
      rintro buf -
      refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
      rintro s1 rfl
      have hset : ∀ s1 : S, msg.set_mr st s1 ct buf 0#u64 v ⦃ r =>
          r = (1#u64, L.wr s1 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) ⦄ := by
        intro s1
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ v) ?_
        rintro s2 rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (hset _) ?_
      rintro r rfl
      unfold msginfo.MessageInfo.new
      simp only [bind_ok]
      refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 1#u64 (by decide)) ?_
      rintro s3 ⟨w, rfl, hw⟩
      refine ⟨w, ?_, by rw [hw]; exact msg_info_one_bv⟩
      rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
    refine WP.spec_bind hin ?_
    rintro s3 ⟨w, rfl, hw⟩
    have hI1 := regw_inv s a σ hI ct htcb hcur hk Fl4Spec.badge_register 0#u64
    set xA := Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv
    have hkA : (Notif.updK σ ct.bv (.tcb xA)).kheap ct.bv = some (.tcb xA) := by simp
    have hcurA : ct.bv = (Notif.updK σ ct.bv (.tcb xA)).curThread := hcur
    have hI2 := regw_inv _ a _ hI1 ct htcb hcurA hkA (Endp.mrIdx 0) v
    set xB := Notif.setReg xA (Endp.mrIdx 0) v.bv
    have hkB : (Notif.updK (Notif.updK σ ct.bv (.tcb xA)) ct.bv (.tcb xB)).kheap ct.bv = some (.tcb xB) := by simp
    have hI3 := regw_inv _ a _ hI2 ct htcb hcurA hkB Fl4Spec.msg_info_register w
    have hxC : Notif.setReg xB Fl4Spec.msg_info_register w.bv = Endp.replyTcb x v.bv := by
      rw [hw]; rfl
    rw [updK_updK, updK_updK, hxC] at hI3
    have hkC : (Notif.updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb x v.bv)) := by simp
    have hact3 : OutsideObjects th (L.nodeAt (L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register))
        0#u64) (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v)
        (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w)
        (L.cpu (L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
          (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v)
          (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w)) layout.node.SCHED_ACTION) := by
      simp only [L.cpu_wr]; rw [Sched.nodeAt_ksb (s := s) (by simp [L.ksb_wr])]; exact hact
    refine WP.spec_mono (sts_inv _ a _ hI3 ct htcb hcur hkC (hrun _ hrs) hact3 .running (by decide) _ hcode) ?_
    rintro s' ⟨hI', hst', -⟩
    rw [updK_updK] at hI'
    exact ⟨by rw [hst']; exact hne, hI'⟩

/-- **`reply1` of the current, `Restart` thread keeps `RInv`**, against the
spec's `specTail` (the reply when called, then `Running`). -/
theorem reply1_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail call ct.bv [v.bv] σ).1, RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s2 a z.2 ⦄ := by
  refine WP.spec_mono (reply1_core s a σ hI ct htcb hcur hk (by rw [hrs]; rfl) hact call v) ?_
  rintro s2 ⟨hne, hI2⟩
  refine ⟨hne, ((), _), ?_, hI2⟩
  rw [specTail_restart hk hrs call v.bv]
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Notif.setThreadState_eq .running hk]; exact Set.mem_singleton _
  · simp only [↓reduceIte]
    have hkC : (Notif.updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb x v.bv)) := by simp
    rw [Notif.setThreadState_eq .running hkC, updK_updK]; exact Set.mem_singleton _

/-- `reply1` keeps the kernel base. -/
theorem reply1_ksb (s : S) (ct : U64) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => L.ksb s2 = L.ksb s ⦄ := by
  unfold vspace.reply1
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (set_thread_state_cases s ct sched.TS_RUNNING) ?_
    rintro s' (rfl | rfl) <;> simp
  · simp only [↓reduceIte]
    have hin : (do
        let buf ← msg.lookup_ipc_buffer st s true ct
        let s2 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
        let (n, s3) ← msg.set_mr st s2 ct buf 0#u64 v
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
        msg.set_msg_info st s3 ct mi) ⦃ s3 => L.ksb s3 = L.ksb s ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true ct L.total) ?_
      rintro buf -
      refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
      rintro s1 rfl
      have hset : ∀ s1 : S, msg.set_mr st s1 ct buf 0#u64 v ⦃ r =>
          r = (1#u64, L.wr s1 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) ⦄ := by
        intro s1
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ v) ?_
        rintro s2 rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (hset _) ?_
      rintro r rfl
      unfold msginfo.MessageInfo.new
      simp only [bind_ok]
      refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 1#u64 (by decide)) ?_
      rintro s3 ⟨w, rfl, -⟩
      simp
    refine WP.spec_bind hin ?_
    rintro s3 h3
    refine WP.spec_mono (set_thread_state_cases s3 ct sched.TS_RUNNING) ?_
    rintro s' (rfl | rfl) <;> simp [h3]

/-- A TCB update with the action kept keeps the SC objects. -/
theorem szKeep_stsAct_tcb (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (y : Fl4Spec.Tcb) :
    Sched.SzKeep σ (Notif.stsAct (Notif.updK σ t (.tcb y)) t) := by
  intro p x n hp
  rw [Notif.stsAct_kheap, Notif.updK_kheap] at hp
  by_cases e : p = t
  · subst e; simp at hp
  · rw [Function.update_of_ne e] at hp; exact ⟨x, hp⟩

/-- **`GetAddrHypX` at `FinX` of the composite relation is a theorem**: from
the CSpace relation, `FinInv`, `MdbOKV` and the domain schedule at `s`,
`set_thread_state Restart` then `reply1` (`restart_full`/`sts_inv`, then
`reply1_inv`). -/
theorem getAddrHypX_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDom : DomRel (L.mem s) (L.ksb s) σ) (ct p : U64) (call : Bool)
    (hcur : ct.bv = σ.curThread) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap ct.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    GetAddrHypX (L := L) (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s σ ar ct p call := by
  intro hX
  have hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s ar σ := ⟨hCR, hFI, hMO, hDom, hX⟩
  obtain ⟨x, hk, -⟩ := hCR.1.tcb ct htcb
  have hcode : sched.TS_RESTART.val = Notif.tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (sts_inv s ar σ hI ct htcb hcur hk (hrun x hk) hact .restart (by decide) _ hcode) ?_
  rintro s1 ⟨hI1, -, hnode⟩
  set σR := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv
  have hkR : σR.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by simp [σR, Notif.stsAct_kheap]
  have hcurR : ct.bv = σR.curThread := by
    rw [hcur]; show σ.curThread = (Notif.stsAct _ _).curThread; unfold Notif.stsAct; split <;> rfl
  have hact1 : OutsideObjects th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := by rw [hnode]; exact hact
  refine WP.spec_bind (reply1_inv s1 ar σR hI1 ct htcb hcurR hkR rfl hact1 call _) ?_
  rintro s2 ⟨hne, z, hz, hI2⟩
  simp only [WP.spec_ok]
  refine ⟨trivial, hne, fun σ1 hσ1 => ?_⟩
  have e : σ1 = σR := by
    rw [Notif.setThreadState_eq .restart hk] at hσ1
    have := congrArg Prod.fst hσ1
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e
  rw [← paddr_bv]
  exact ⟨z, hz, hI2.relTop, hI2.2.2.2.2⟩

/-- `reply1_inv` with the kernel base and the SC objects kept. -/
theorem reply1_invT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (call : Bool) (v : U64) :
    vspace.reply1 st s ct call v ⦃ s2 => L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧ L.ksb s2 = L.ksb s ∧
      ∃ z ∈ (specTail call ct.bv [v.bv] σ).1, RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s2 a z.2 ∧
        Sched.SzKeep σ z.2 ⦄ := by
  refine WP.spec_mono (WP.spec_and (reply1_core s a σ hI ct htcb hcur hk (by rw [hrs]; rfl) hact call v)
    (reply1_ksb s ct call v)) ?_
  rintro s2 ⟨⟨hne, hI2⟩, hks⟩
  refine ⟨hne, hks, ((), _), ?_, hI2, szKeep_stsAct_tcb _ _ _⟩
  rw [specTail_restart hk hrs call v.bv]
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Notif.setThreadState_eq .running hk]; exact Set.mem_singleton _
  · simp only [↓reduceIte]
    have hkC : (Notif.updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb x v.bv)) := by simp
    rw [Notif.setThreadState_eq .running hkC, updK_updK]; exact Set.mem_singleton _

theorem SzKeep.trans' {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : Sched.SzKeep σ1 σ2) (h2 : Sched.SzKeep σ2 σ3) :
    Sched.SzKeep σ1 σ3 := fun p x n hp => by
  obtain ⟨x2, h⟩ := h2 p x n hp
  exact h1 p x2 n h

/-- **`GetAddrHypX` at `FinXT`.** -/
theorem getAddrHypX_topT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDom : DomRel (L.mem s) (L.ksb s) σ) (ct p : U64) (call : Bool)
    (hcur : ct.bv = σ.curThread) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap ct.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    GetAddrHypX (L := L) (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s σ ar ct p call := by
  intro hX
  have hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s ar σ := ⟨hCR, hFI, hMO, hDom, hX.1⟩
  obtain ⟨x, hk, -⟩ := hCR.1.tcb ct htcb
  have hcode : sched.TS_RESTART.val = Notif.tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (WP.spec_and (sts_inv s ar σ hI ct htcb hcur hk (hrun x hk) hact .restart (by decide) _ hcode)
    (set_thread_state_cases s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨⟨hI1, -, hnode⟩, hcs⟩
  have hks1 : L.ksb s1 = L.ksb s := by rcases hcs with rfl | rfl <;> simp
  set σR := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv
  have hkR : σR.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by simp [σR, Notif.stsAct_kheap]
  have hcurR : ct.bv = σR.curThread := by
    rw [hcur]; show σ.curThread = (Notif.stsAct _ _).curThread; unfold Notif.stsAct; split <;> rfl
  have hact1 : OutsideObjects th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := by rw [hnode]; exact hact
  refine WP.spec_bind (reply1_invT s1 ar σR hI1 ct htcb hcurR hkR rfl hact1 call _) ?_
  rintro s2 ⟨hne, hks2, z, hz, hI2, hz2⟩
  simp only [WP.spec_ok]
  refine ⟨trivial, hne, fun σ1 hσ1 => ?_⟩
  have e : σ1 = σR := by
    rw [Notif.setThreadState_eq .restart hk] at hσ1
    have := congrArg Prod.fst hσ1
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e
  rw [← paddr_bv]
  exact ⟨z, hz, hI2.relTop, hI2.2.2.2.2, ⟨G, hI2.1, hI2.2.1, hI2.2.2.1⟩, hks2.trans hks1,
    SzKeep.trans' (szKeep_stsAct_tcb _ _ _) hz2⟩

/-! ### `TestAndClearAccessed`: the spec's `Restart` that FL4 omits -/

theorem schedulable_updK_tcb {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {y y' : Fl4Spec.Tcb}
    (h1 : Fl4Spec.runnable y.tcbState = Fl4Spec.runnable y'.tcbState)
    (h2 : y.tcbSchedContext = y'.tcbSchedContext) :
    Fl4Spec.schedulable t (Notif.updK σ t (.tcb y)) = Fl4Spec.schedulable t (Notif.updK σ t (.tcb y')) := by
  simp only [Fl4Spec.schedulable, Fl4Spec.tcbsOf, Fl4Spec.tcbsOfKh, Fl4Spec.scsOf, Fl4Spec.scsOfKh,
    Fl4Spec.optPred, Fl4Spec.optMap, Fl4Spec.optMapSome, Notif.updK_kheap, Function.update_self, Fl4Spec.tcbOf, h1, h2]
  have hr : (Notif.updK σ t (.tcb y)).releaseQueue = (Notif.updK σ t (.tcb y')).releaseQueue := rfl
  rw [hr]
  congr 2
  rcases y'.tcbSchedContext with _ | p
  · rfl
  · by_cases e : p = t
    · subst e; simp [Function.update_self, Fl4Spec.scOf]
    · simp [Function.update_of_ne e]

/-- Setting a thread's state twice: the first `set_thread_state_act` is
absorbed when the TCB's schedulability is the same. -/
theorem stsAct_twice {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {y1 y2 : Fl4Spec.Tcb}
    (hs : Fl4Spec.schedulable t (Notif.updK σ t (.tcb y1)) = Fl4Spec.schedulable t (Notif.updK σ t (.tcb y2))) :
    Notif.stsAct (Notif.updK (Notif.stsAct (Notif.updK σ t (.tcb y1)) t) t (.tcb y2)) t =
      Notif.stsAct (Notif.updK σ t (.tcb y2)) t := by
  by_cases c : t = (Notif.updK σ t (.tcb y1)).curThread ∧
      (Notif.updK σ t (.tcb y1)).schedulerAction = .resumeCurThread ∧
      ¬ Fl4Spec.schedulable t (Notif.updK σ t (.tcb y1)) = true
  · have e1 : Notif.stsAct (Notif.updK σ t (.tcb y1)) t =
        { Notif.updK σ t (.tcb y1) with schedulerAction := .chooseNewThread } := by
      unfold Notif.stsAct; rw [if_pos c]
    have c2 : t = (Notif.updK σ t (.tcb y2)).curThread ∧
        (Notif.updK σ t (.tcb y2)).schedulerAction = .resumeCurThread ∧
        ¬ Fl4Spec.schedulable t (Notif.updK σ t (.tcb y2)) = true := ⟨c.1, c.2.1, hs ▸ c.2.2⟩
    rw [e1]
    unfold Notif.stsAct
    rw [if_pos c2, if_neg (by rintro ⟨-, h, -⟩; exact absurd h (by simp [Notif.updK]))]
    simp [Notif.updK, Function.update_idem]
  · have e1 : Notif.stsAct (Notif.updK σ t (.tcb y1)) t = Notif.updK σ t (.tcb y1) := by
      unfold Notif.stsAct; rw [if_neg c]
    rw [e1, updK_updK]

/-- **`TacHypX` at `FinX` of the composite relation is a theorem**: FL4
replies without `Restart` from the state with the accessed bit cleared; the
spec's `Restart` before its reply is absorbed by the final `Running`
(`stsAct_twice`). -/
theorem tacHypX_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDom : DomRel (L.mem s) (L.ksb s) σ) (ct : U64) (call : Bool)
    (hcur : ct.bv = σ.curThread) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap ct.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    TacHypX (L := L) (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) L4 L3 L2 L1
      s σ ar ct call := by
  intro b hb hba v _ hX
  set s' := L.wr s b (L.mem s b &&& ~~~32#u64) with hs'
  have hPl := hX.1.2.pl
  have hSS : SlotsSame th (L.mem s) (L.mem s') := by
    refine slotsSame_wr hPl s _ hba (fun a ha => ?_)
    obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hPl ha
    have := (hX.1.2.po b hb).2 p k hk
    omega
  have hksb : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hSt : StateRel th (L.mem s') σ := hCR.1.of_caps (fun y hy => hSS.capAt hy)
  have hK0 : KFoot σ σ := ⟨rfl, rfl, fun o h => absurd rfl h, rfl⟩
  obtain ⟨hCR', hFI', hMO'⟩ := cspace_step hCR hFI hMO hSS hK0 hSt
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hX.1.2.vs.ksb_fit; rw [hksb] at this; omega
  have hka : (L.ksb s).val % 8 = 0 := by have := hX.1.2.vs.ksb_al; rw [hksb] at this; exact this
  have hDom' : DomRel (L.mem s') (L.ksb s) σ := by
    refine hDom.of_same (domSame_low hkf hka fun b' hb' h1 h2 => ?_) rfl rfl
    refine Notif.rd_wr_ne hba hb' (fun e => ?_)
    subst e
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    refine hX.1.2.disj _ (Or.inr (Or.inl ⟨by rw [hksb]; omega, by rw [hksb]; omega⟩))
      (table_vobj hX.1.2.pt hq hi _)
  have hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s' ar σ :=
    ⟨hCR', hFI', by rw [hksb]; exact hMO', by rw [hksb]; exact hDom', hX⟩
  obtain ⟨x, hk, -⟩ := hCR.1.tcb ct htcb
  have hact' : OutsideObjects th (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) := by
    rw [L.cpu_wr, Sched.nodeAt_ksb hksb]; exact hact
  refine WP.spec_mono (reply1_core s' ar σ hI ct htcb hcur hk (hrun x hk) hact' call v) ?_
  rintro s2 ⟨hne, hI2⟩
  refine ⟨hne, fun σ1 hσ1 => ?_⟩
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hk] at hσ1
    have := congrArg Prod.fst hσ1
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e
  have hk1 : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { x with tcbState := .restart }) := by simp [Notif.stsAct_kheap]
  refine ⟨((), Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { (if call then Endp.replyTcb x v.bv else x) with tcbState := .running })) ct.bv), ?_, hI2.relTop,
    hI2.2.2.2.2⟩
  rw [specTail_restart hk1 rfl call v.bv]
  have hsch : ∀ y : Fl4Spec.Tcb, y.tcbSchedContext = x.tcbSchedContext → Fl4Spec.runnable y.tcbState = true →
      Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) =
        Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb y)) := fun y h1 h2 =>
    schedulable_updK_tcb (by rw [h2]; rfl) h1.symm
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Notif.setThreadState_eq .running hk1, stsAct_twice (hsch { x with tcbState := .running } rfl rfl)]
    exact Set.mem_singleton _
  · simp only [↓reduceIte]
    have hkC : (Notif.updK (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ct.bv
        (.tcb (Endp.replyTcb { x with tcbState := .restart } v.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb { x with tcbState := .restart } v.bv)) := by simp
    rw [Notif.setThreadState_eq .running hkC, updK_updK]
    have ey : ({ Endp.replyTcb { x with tcbState := .restart } v.bv with tcbState := .running } : Fl4Spec.Tcb) =
        { Endp.replyTcb x v.bv with tcbState := .running } := rfl
    rw [ey, stsAct_twice (hsch { Endp.replyTcb x v.bv with tcbState := .running } rfl rfl)]
    exact Set.mem_singleton _

set_option maxHeartbeats 4000000 in
/-- **`TacHypX` at `FinXT`.** -/
theorem tacHypX_topT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDom : DomRel (L.mem s) (L.ksb s) σ) (ct : U64) (call : Bool)
    (hcur : ct.bv = σ.curThread) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap ct.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true) :
    TacHypX (L := L) (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) L4 L3 L2 L1
      s σ ar ct call := by
  intro b hb hba v _ hXT
  have hX := hXT.1
  set s' := L.wr s b (L.mem s b &&& ~~~32#u64) with hs'
  have hPl := hX.1.2.pl
  have hSS : SlotsSame th (L.mem s) (L.mem s') := by
    refine slotsSame_wr hPl s _ hba (fun a ha => ?_)
    obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hPl ha
    have := (hX.1.2.po b hb).2 p k hk
    omega
  have hksb : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hSt : StateRel th (L.mem s') σ := hCR.1.of_caps (fun y hy => hSS.capAt hy)
  have hK0 : KFoot σ σ := ⟨rfl, rfl, fun o h => absurd rfl h, rfl⟩
  obtain ⟨hCR', hFI', hMO'⟩ := cspace_step hCR hFI hMO hSS hK0 hSt
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hX.1.2.vs.ksb_fit; rw [hksb] at this; omega
  have hka : (L.ksb s).val % 8 = 0 := by have := hX.1.2.vs.ksb_al; rw [hksb] at this; exact this
  have hDom' : DomRel (L.mem s') (L.ksb s) σ := by
    refine hDom.of_same (domSame_low hkf hka fun b' hb' h1 h2 => ?_) rfl rfl
    refine Notif.rd_wr_ne hba hb' (fun e => ?_)
    subst e
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    refine hX.1.2.disj _ (Or.inr (Or.inl ⟨by rw [hksb]; omega, by rw [hksb]; omega⟩))
      (table_vobj hX.1.2.pt hq hi _)
  have hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s' ar σ :=
    ⟨hCR', hFI', by rw [hksb]; exact hMO', by rw [hksb]; exact hDom', hX⟩
  obtain ⟨x, hk, -⟩ := hCR.1.tcb ct htcb
  have hact' : OutsideObjects th (L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION) := by
    rw [L.cpu_wr, Sched.nodeAt_ksb hksb]; exact hact
  refine WP.spec_mono (WP.spec_and (reply1_core s' ar σ hI ct htcb hcur hk (hrun x hk) hact' call v)
    (reply1_ksb s' ct call v)) ?_
  rintro s2 ⟨⟨hne, hI2⟩, hks2⟩
  refine ⟨hne, fun σ1 hσ1 => ?_⟩
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [Notif.setThreadState_eq .restart hk] at hσ1
    have := congrArg Prod.fst hσ1
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst e
  have hk1 : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { x with tcbState := .restart }) := by simp [Notif.stsAct_kheap]
  refine ⟨((), Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { (if call then Endp.replyTcb x v.bv else x) with tcbState := .running })) ct.bv), ?_, hI2.relTop,
    hI2.2.2.2.2, ⟨G, hI2.1, hI2.2.1, hI2.2.2.1⟩, hks2.trans hksb, szKeep_stsAct_tcb _ _ _⟩
  rw [specTail_restart hk1 rfl call v.bv]
  have hsch : ∀ y : Fl4Spec.Tcb, y.tcbSchedContext = x.tcbSchedContext → Fl4Spec.runnable y.tcbState = true →
      Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) =
        Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb y)) := fun y h1 h2 =>
    schedulable_updK_tcb (by rw [h2]; rfl) h1.symm
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Notif.setThreadState_eq .running hk1, stsAct_twice (hsch { x with tcbState := .running } rfl rfl)]
    exact Set.mem_singleton _
  · simp only [↓reduceIte]
    have hkC : (Notif.updK (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ct.bv
        (.tcb (Endp.replyTcb { x with tcbState := .restart } v.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb { x with tcbState := .restart } v.bv)) := by simp
    rw [Notif.setThreadState_eq .running hkC, updK_updK]
    have ey : ({ Endp.replyTcb { x with tcbState := .restart } v.bv with tcbState := .running } : Fl4Spec.Tcb) =
        { Endp.replyTcb x v.bv with tcbState := .running } := rfl
    rw [ey, stsAct_twice (hsch { Endp.replyTcb x v.bv with tcbState := .running } rfl rfl)]
    exact Set.mem_singleton _

end

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core Classical Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **`decode_invocation_frame_capX` without the reply hypotheses**: they are
`getAddrHypX_top` and `tacHypX_top`, from the domain schedule's relation. -/
theorem decode_invocation_frame_capXR [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hU : UtInv (L.mem s) G) (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hDom : DomRel (L.mem s) (L.ksb s) σ) :
    (lbl ≠ fl4_abi.label.X86PageGetAddress ∧ lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed ∧
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) ∨
    DecOKRMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct :=
  decode_invocation_frame_capX arI th s ar σ G hCR hFI hU hMO hA hS hPI hCur hR hPt hVC lbl slbl hlbl length buf ct hct
    hcur htcb hact hrun args hlen hargs hpc hidx hcap hAl hno extra excaps hext hxs blk call don fp ci buffer
    (Vs.getAddrHypX_topT s ar σ G hCR hFI hMO hDom ct p call hcur.symm htcb hact (fun x hk => hrun x (hcur ▸ hk)))
    (Vs.tacHypX_topT s ar σ G hCR hFI hMO hDom ct call hcur.symm htcb hact (fun x hk => hrun x (hcur ▸ hk)))

end

end

end Fl4Proofs.P3
