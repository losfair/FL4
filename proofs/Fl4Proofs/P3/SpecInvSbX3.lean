/-
P3 (DESIGN.md §9), invariant line G1 (sb2): **the binding gap performs**: the SC
bind and the TCB `threadControlSched` keep `ScInv` from the decode's facts
(spec side only; imports SpecInvSbE).

* `bindOK_of`: the decode's `BindOK` (SpecInvSbX2) holds at the perform state's
  binding view (the binding frame `Rel` keeps `bv`).
* **`sg_scBind`**: `invoke_sched_context` Bind (a TCB: `sched_context_bind_tcb`
  with both ends unbound, sb1's `sikp_schedContextBindTcb`; a notification: a
  frame).
* `bq_installTcbCap3`: `install_tcb_cap` of the fault-handler slot keeps the
  binding view when that slot holds a null or endpoint cap (`VfhAll`, the
  entry's fault handlers are valid; sb2's `sbp_capDelete_fh`).
* **`sg_tcSched`**: `invoke_tcb` threadControlSched (the bind after the
  installs finds both ends still unbound; the unbind reads the pair it clears).
-/
import Fl4Proofs.P3.SpecInvSbE
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem bindOK_of {σe σ : State Unit} {inv : Fl4Invocation} (hD : DecFrom σe inv) (hR : Rel σe σ) :
    BindOK (bv σ.kheap) inv := by
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hR0, -, -, hm⟩ := hD
  have h := okb_fl4Decode (bv σ0.kheap) fp label args ci sl cap ex buf σ0 rfl inv s0 hm
  rwa [hR0.bv, ← hR.bv] at h

/-! ## SC bind -/

theorem sg_scBind (blk call don : Bool) (c : ObjRef) (cap : Cap) (σ : State Unit) (hI : ScInv σ)
    (hB : BindOK (bv σ.kheap) (.invokeSchedContext (.invokeSchedContextBind c cap))) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don
      (.invokeSchedContext (.invokeSchedContextBind c cap))).run σ).1, ScInv y.2 := by
  intro y hy
  cases cap
  case threadCap t =>
    simp only [fl4PerformInvocation, invokeSchedContext, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    show ScInv x.2
    obtain ⟨z, hz, hx⟩ := hx
    have hz' := sikp_schedContextBindTcb c t σ (Or.inl hB.2) (Or.inl hB.1) hI z hz
    rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hx)).2]; exact hz'
  case notificationCap n b r =>
    simp only [fl4PerformInvocation, invokeSchedContext, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    exact (sik_of_sbk fun _ => by sb_auto) σ hI x hx
  all_goals
    simp only [fl4PerformInvocation, invokeSchedContext, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    exact hx.elim

/-! ## threadControlSched -/

/-- `ScInv` with a fixed binding view. -/
def BQ (B : ObjRef → BV) (s : State Unit) : Prop := ScInv s ∧ bv s.kheap = B

theorem ik_bq {B : ObjRef → BV} {α : Type} {m : NonDet (State Unit) α} (h : ∀ h0, SBK h0 m) : IK (BQ B) m :=
  fun _ hσ _ hx => ⟨scInv_of_br hσ.1 (br_mem_of_sbk h hx), (bv_of_br (br_mem_of_sbk h hx)).trans hσ.2⟩

theorem capAt_fh {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    SInvU.capAt σ (t, tcbCnodeIndex 3) = some x.tcbFaultHandler := by
  show (match σ.kheap t with | some o => SInvU.capView o (tcbCnodeIndex 3) | none => none) = _
  rw [hk]
  show tcbCnodeMap x (tcbCnodeIndex 3) = _
  unfold tcbCnodeMap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

/-- `install_tcb_cap` of the fault-handler slot holding a null or endpoint cap. -/
theorem bq_installTcbCap3 {B : ObjRef → BV} (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr))
    (σ : State Unit) (hσ : BQ B σ) (hF : ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → FhC c) :
    ∀ y ∈ ((installTcbCap (Z := Unit) t sl 3 fh).run σ).1, BQ B y.2 := by
  intro y hy
  unfold installTcbCap at hy
  rcases fh with _ | ⟨nc, src⟩
  · rw [SInvU.mem_ret_ok hy]; exact hσ
  · try dsimp only at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hb := sbp_capDelete_fh _ σ hF z hz
      have hz' : BQ B z.2 := ⟨scInv_of_br hσ.1 hb, (bv_of_br hb).trans hσ.2⟩
      exact (ike_unlessE _ (ike_liftE (ik_bq (B := B) fun _ =>
        sb_checkCapAt _ _ _ (sb_checkCapAt _ _ _ (sb_capInsert _ _ _))))) z.2 hz' y hy
    · have hb := sbp_capDelete_fh _ σ hF z hz
      exact ⟨scInv_of_br hσ.1 hb, (bv_of_br hb).trans hσ.2⟩

theorem sg_tcSched (blk call don : Bool) (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr))
    (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef)) (σ : State Unit) (hI : ScInv σ)
    (hB : BindOK (bv σ.kheap) (.invokeTCB (.threadControlSched t sl fh mcp prio sc)))
    (hF : ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → FhC c) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don
      (.invokeTCB (.threadControlSched t sl fh mcp prio sc))).run σ).1, ScInv y.2 := by
  have hfin : ∀ s, BQ (bv σ.kheap) s → ∀ x ∈ (NonDet.maybeM (fun scopt =>
      match scopt with
      | none => do
          let scPtrOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
          let scPtr ← NonDet.assertOpt scPtrOpt
          schedContextUnbindTcb scPtr
      | some scPtr => schedContextBindTcb scPtr t) sc s).1, ScInv x.2 := by
    intro s hs x hx
    rcases sc with _ | _ | c
    · rw [Set.mem_singleton_iff.1 hx]; exact hs.1
    · refine (?_ : SIK _) s hs.1 x hx
      unfold NonDet.maybeM
      si_auto
    · have hc : bv s.kheap c = .s none := by rw [hs.2]; exact hB.1
      have ht : bv s.kheap t = .t none := by rw [hs.2]; exact hB.2
      exact sikp_schedContextBindTcb c t s (Or.inl ht) (Or.inl hc) hs.1 x hx
  intro y hy
  simp only [fl4PerformInvocation, invokeTcb] at hy
  have h0 : BQ (bv σ.kheap) σ := ⟨hI, rfl⟩
  obtain ⟨z1, hz1, ⟨u1, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · exact (bq_installTcbCap3 t sl fh σ h0 hF z1 hz1).1
  have h1 := bq_installTcbCap3 t sl fh σ h0 hF z1 hz1
  obtain ⟨z2, hz2, ⟨u2, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2; rw [hx] at he; cases he
  obtain ⟨x2, hx2, rfl⟩ := SInvU.mem_liftE' hz2
  have h2 : BQ (bv σ.kheap) x2.2 := (ik_bq fun _ => by sb_auto) z1.2 h1 x2 hx2
  obtain ⟨z3, hz3, ⟨u3, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3; rw [hx] at he; cases he
  obtain ⟨x3, hx3, rfl⟩ := SInvU.mem_liftE' hz3
  have h3 : BQ (bv σ.kheap) x3.2 := (ik_bq fun _ => by sb_auto) x2.2 h2 x3 hx3
  obtain ⟨z4, hz4, ⟨u4, -, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz4; rw [hx] at he; cases he
  obtain ⟨x4, hx4, rfl⟩ := SInvU.mem_liftE' hz4
  rw [SInvU.mem_ret_ok hy]
  exact hfin x3.2 h3 x4 hx4

end

end Fl4Proofs.P3.SInvB
