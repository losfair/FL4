/-
P3 (DESIGN.md §9), invariant line G1 (rd12a, KENTRY-PLAN rd11a handoff 3-4):
**`OsBody` for Recv / Wait / NBWait / NBRecv** (spec side only).

* `ik_asUserGet` (`as_user t (get_register r)` reads only: rd's
  `Endp.asUser_getRegister_eq` once `t` is read as a TCB), `ik_lookupReply`;
  `nq_ct` (nq3's `NQ [ct]` at a body start).
* **`ss4_handleRecv blk cr σb (BS) (Suff) (EB true) (RcvS σb ct)`**: ctq's
  `eb_handleRecv_hr` walk with the pinned start state as invariant (every read
  of the prefix keeps the state): endpoint → B's `kr_receiveIpc`; notification
  → rd11a's `ke_receiveSignal`; a lookup fault → `handle_fault ct` by rd11b's
  `ss4_end` (CP: `cp_handleFault`, ct not runnable: `nr_handleFault` from
  `nb0_of_bs`, CB at the handler's outcome: ctq7's `eb_handleFault_p`).
* `RcvB σ` (ctq's `EB true` and rd8e's `RcvS` at the body start of a `true`
  front: carried facts, pinned to the given entry), **`osBody_recv`**,
  `osBody_of12`, top **`kentry_rdyOff12`** (rd11b's `kentry_rdyOff3j` with
  `OsBody` for the four receive syscalls discharged from `RcvB`).
-/
import Fl4Proofs.P3.SpecInvRd12aB
import Fl4Proofs.P3.SpecInvRd11bB
import Fl4Proofs.P3.SpecInvCqB3
import Fl4Proofs.P3.SpecInvCqE3
import Fl4Proofs.P3.SpecInvNtfnQH3
open Classical

namespace Fl4Proofs.P3.SInvR.A12a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.A11

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The reads of the prefix -/

theorem mem_getsThe12 {α : Type} {f : State Unit → Option α} {σ : State Unit} {x : α × State Unit}
    (h : x ∈ (NonDet.getsThe f σ).1) : f σ = some x.1 ∧ x.2 = σ := by
  unfold NonDet.getsThe at h
  revert h
  cases e : f σ with
  | none => intro h; simp [NonDet.assertOpt, NonDet.fail] at h
  | some a =>
    intro h
    simp only [NonDet.assertOpt, NonDet.pure] at h
    rw [Set.mem_singleton_iff] at h
    subst h; exact ⟨rfl, rfl⟩

theorem getTcb_some12 {t : ObjRef} {σ : State Unit} {tcb : Tcb} (h : getTcb (Z := Unit) t σ = some tcb) :
    σ.kheap t = some (.tcb tcb) := by
  revert h
  unfold getTcb readObject
  rcases e : σ.kheap t with _ | k
  · simp
  · cases k <;> simp_all

/-- **`as_user t (get_register r)` reads only.** -/
theorem ik_asUserGet (a : ObjRef) (r : Register) (σb : State Unit) :
    IK (fun s => s = σb) (asUser (Z := Unit) a (getRegister r)) := by
  intro s hs y hy
  have hy0 := hy
  unfold asUser at hy0
  obtain ⟨⟨tcb, s1⟩, h1, -⟩ := hy0
  obtain ⟨e1, -⟩ := mem_getsThe12 h1
  rw [Endp.asUser_getRegister_eq (getTcb_some12 e1)] at hy
  rw [Set.mem_singleton_iff.1 hy]; exact hs

theorem ik_lookupReply (σb : State Unit) : IKE (fun s => s = σb) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first
    | (with_reducible exact ik_asUserGet _ _ _)
    | (with_reducible exact SInvQ.pk_capFaultLookupCap _ _ _ _)
    | ik_step0 | ik_unfold)

/-- nq3's `NQ [ct]` at a body start (ct running). -/
theorem nq_ct {s : State Unit} (h : A10.BS s) : NQ [s.curThread] s := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  refine nq_cons h.nq fun x hx => ?_
  rw [hct] at hx; cases hx
  rcases hst with h1 | h1
  · exact ok_of_active (by rw [h1]; first | rfl | decide | simp [activeSt])
  · rw [h1]; exact ⟨fun h => h, rfl⟩

/-! ## `handle_recv` -/

/-- **`SS4` after `handle_recv`** from the body-start facts, ctq's `EB true`
and rd8e's `RcvS` of ct. -/
theorem ss4_handleRecv (blk cr : Bool) (σb : State Unit) (hB : A10.BS σb) (hSf : Suff σb)
    (hE : SInvQ.EB true σb) (hS : B8e.RcvS σb σb.curThread) :
    ∀ y ∈ (handleRecv (Z := Unit) blk cr σb).1, A10.SS4 y.2 := by
  have hb : ∀ x, σb.kheap σb.curThread = some (.tcb x) → x.tcbSchedContext = some σb.curSc := hB.cs
  have hN : NQ [σb.curThread] σb := nq_ct hB
  have h0 : B0 σb := b0_of_bs hB
  have hRIP : ∀ cp rc, HK (fun s => s = σb) A10.SS4 (receiveIpc (Z := Unit) σb.curThread cp blk rc) := by
    intro cp rc s hs y hy
    rw [hs] at hy
    exact ss4_of_kr hB hSf (kr_receiveIpc σb h0 cp blk rc σb (KP.refl σb) hb hS hE.2 hy)
  have hRS : ∀ cp, HK (fun s => s = σb) A10.SS4 (receiveSignal (Z := Unit) σb.curThread cp blk) := by
    intro cp s hs y hy
    rw [hs] at hy
    exact ss4_of_ke hB hSf (ke_receiveSignal σb cp blk σb (KP.refl σb) hb hy)
  have hHF : ∀ e, HK (fun s => s = σb) A10.SS4 (handleFault (Z := Unit) σb.curThread e) := by
    intro e s hs z hz
    rw [hs] at hz
    have hE1 := SInvQ.eb_handleFault_p (k := true) σb.curThread e σb (SInvQ.npq_ct hE) hN
      (List.mem_singleton_self _) hE z hz
    exact A11b.ss4_end (A10.ss4_of_bs hB hSf).1
      (A11b.cp_handleFault _ e σb σb.curSc σb ⟨rfl, A8.CW.refl _ _⟩ z hz)
      (A11b.cfk_handleFault _ e σb z hz) (A11b.nr_handleFault _ e σb (A11b.nb0_of_bs hB) z hz) hE1.2.2 hB.ni
  unfold handleRecv
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  obtain ⟨y2, h2, hy⟩ := hy
  have e2 : y2.2 = σb := by
    refine (?_ : IK (fun s => s = σb) _) σb rfl y2 h2
    unfold NonDet.liftM
    exact ik_bind (ik_asUserGet _ _ σb) fun _ => ik_pure _
  rw [e2] at hy
  refine hk_catch (I := fun s => s = σb) (Q0 := A10.SS4) ?_ hHF σb rfl y hy
  refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
  split
  · (try dsimp only)
    split
    · (try dsimp only)
      split
      · refine hkr_bind (ik_lookupReply σb) (fun rc => ?_)
        exact hkr_liftE (hRIP _ rc)
      · refine hkr_bind (ik_pure _) (fun rc => ?_)
        exact hkr_liftE (hRIP _ rc)
    · exact hkr_throw _
  · (try dsimp only)
    split
    · refine hkr_bind (by repeat' (first | ik_step0 | ik_unfold)) (fun bt => ?_)
      split
      · exact hkr_liftE (hRS _)
      · exact hkr_throw _
    · exact hkr_throw _
  · exact hkr_throw _

/-! ## `OsBody` -/

/-- The receive syscalls (each body is `withoutPreemption (handle_recv blk cr)`). -/
abbrev IsRecv (c : Syscall) : Prop :=
  c = .sysRecv ∨ c = .sysWait ∨ c = .sysNBWait ∨ c = .sysNBRecv

/-- **The receive body's start facts**, pinned to the given entry: ctq's `EB
true` (ctq17's `EvP` at a `true` front outcome, `eb_fl4HandleEvent_sys`'s walk)
and rd8e's `RcvS` of ct (rd8e handoff 2's entry facts) at every `true` front
outcome. Carried facts, not premises. -/
abbrev RcvB (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → SInvQ.EB true v.2 ∧ B8e.RcvS v.2 v.2.curThread

theorem osBody_hr (rep : Bool) (c : Syscall) (blk cr : Bool)
    (hc : ∀ s, (A8.bodyRun rep c s).1 = (ExceptT.run (NonDetE.handleE
      (withoutPreemption (Z := Unit) (handleRecv blk cr)) (fun _ => withoutPreemption (Z := Unit) preemptionPath)) s).1)
    {σ : State Unit} (h : A8.EF σ) (hR : RcvB σ) : A9.OsBody rep c σ := by
  intro v hv ht y hy
  obtain ⟨hB, hSf⟩ := A10.bs_front h hv ht
  obtain ⟨hE, hS⟩ := hR v hv ht
  rw [hc] at hy
  obtain ⟨w, hw, e⟩ := A10.mem_handleE_wp hy
  rw [e]
  obtain ⟨a1, a2, a3, a4⟩ := ss4_handleRecv blk cr v.2 hB hSf hE hS w hw
  exact ⟨a1, a2, a3, a4, nq_handleRecv v.2.curThread blk cr v.2 ⟨nq_ct hB, rfl⟩ w hw⟩

/-- **`OsBody` for Recv / Wait / NBWait / NBRecv** from rd8a's `EF` and `RcvB`. -/
theorem osBody_recv (rep : Bool) (c : Syscall) (hc : IsRecv c) {σ : State Unit} (h : A8.EF σ)
    (hR : RcvB σ) : A9.OsBody rep c σ := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact osBody_hr rep _ true true (fun _ => rfl) h hR
  · exact osBody_hr rep _ true false (fun _ => rfl) h hR
  · exact osBody_hr rep _ false false (fun _ => rfl) h hR
  · exact osBody_hr rep _ false true (fun _ => rfl) h hR

/-- `OsBody` for the receive syscalls from `RcvB`, the rest given. -/
theorem osBody_of12 (rep : Bool) (c : Syscall) {σ : State Unit} (h : A8.EF σ)
    (hR : IsRecv c → RcvB σ) (hO : c ≠ .sysYield → ¬ IsRecv c → A9.OsBody rep c σ) :
    c ≠ .sysYield → A9.OsBody rep c σ := fun hy => by
  by_cases e : IsRecv c
  · exact osBody_recv rep c e h (hR e)
  · exact hO hy e

section Q
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **The syscall entry** (rd12a top): rd11b's `kentry_rdyOff3j` with `OsBody`
for Recv / Wait / NBWait / NBRecv discharged from `RcvB` at the FaultIP
outcome. Remaining: rd8e/f's `RdBody`, `OsBody` for the six invocation
syscalls (Send / NBSend / Call / ReplyRecv / NBSendRecv / NBSendWait; rd12b),
`RcvB` (ctq / rd8e carried facts); the rest are the carried entry facts. -/
theorem kentry_rdyOff12 (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : SInvQ.RB σ) (h4 : SInvQ.T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : SInv.Iu σ.curThread σ) (hIL : SInv.IL [σ.curThread] σ) (hJ : SInvL.Js I σ.curThread d Nq σ σ)
    (hE : SInvL.EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (SInvU.uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ (IsRecv c → RcvB w.2) ∧
        (c ≠ .sysYield → ¬ IsRecv c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A11b.kentry_rdyOff3j hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, osBody_of12 rep c (A8.ef_fip h w hw) (hW w hw).2.1 (hW w hw).2.2⟩

end Q

end

end Fl4Proofs.P3.SInvR.A12a
