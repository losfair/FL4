/-
P3 (DESIGN.md §9), invariant line G1 (ctq17): **the syscall event keeps the
ready-queue bundle** (spec side only, outside the JAtZ cone; KENTRY-PLAN
ctq15 handoff 3, first half).

* `EvP C N S I d Nq σe s`: SpecInvCqN2's `SH C N S` with ctq14's `CKN` (for
  ctq8's `hB` at `check_budget_restart` / `handle_yield`: ctq11's
  `bc_of_ck` with sb2's ScBackS), nq3's `Iu C` (NQ [C] after the first
  phase: `nq_fl4HandleInvocationR`) and ctq11's `JR` (RT after the first
  phase: `rt_fl4HandleInvocationR`), each kept by the event's front
  (`update_time_stamp`, a restarting `check_budget_restart` leaves the state,
  `get_cap_reg`): `evp_auto`.
* **`eb_fl4HandleSyscall`**: every outcome of every syscall has `EB false`:
  the invocations by `eb_fl4HandleInvocationR` (first phase `fp = true`
  only for ReplyRecv / NBSendRecv / NBSendWait, none blocking), then their
  `handle_recv` by ctq10's `eb_handleRecv_res` (ResSc from RT, NQ [ct], ct
  kept, `EB true` from the shell's `ok` outcome); Recv / Wait / NBWait /
  NBRecv by `eb_handleRecv_res`; Yield by ctq8's `eb_handleYield_p`.
* **`eb_fl4HandleEvent_sys`**: with `update_time_stamp` and
  `check_budget_restart` (ctq8's `eb_checkBudgetRestart_p`: no restart ⇒
  `EB false`).
-/
import Fl4Proofs.P3.SpecInvCqN2
import Fl4Proofs.P3.SpecInvCqHS
import Fl4Proofs.P3.SpecInvNtfnQH3
open Classical

namespace Fl4Proofs.P3.SInvQ.P17
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13 Fl4Proofs.P3.SInvQ.P15

noncomputable section

set_option maxHeartbeats 2000000

section E
variable {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit}

/-- **The facts at the start of a syscall.** -/
abbrev EvP (C N S : ObjRef) (I : ObjRef × ObjRef) (d : Prop) (Nq : Irq → ObjRef) (σe s : State Unit) : Prop :=
  SH C N S s ∧ R14.CKN s ∧ Iu C s ∧ R11.JR I C d Nq σe s

theorem evp_of {α : Type} {m : NonDet (State Unit) α} (h1 : IK (SH C N S) m) (h2 : R14.CKK m)
    (h3 : IK (Iu C) m) (h4 : IK (R11.JR I C d Nq σe) m) : IK (EvP C N S I d Nq σe) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2.1 y hy, h4 σ h.2.2.2 y hy⟩

macro "evp_auto" : tactic => `(tactic| exact evp_of (by sh_auto) (by ck_auto) (by iu_auto) (by jr_auto))

/-- ctq8's `hB` from `EvP`. -/
theorem hb_of_evp {s : State Unit} (h : EvP C N S I d Nq σe s) : schedulable s.curThread s = true → BC s :=
  fun hs => R11.bc_of_ck (R14.ckn_ck h.2.1) h.1.2.1.back hs

/-- `handle_recv` from the carried facts. -/
theorem eb_recv (blk cr : Bool) (s : State Unit) (hc : s.curThread = C) (hE : EB true s) (hR : R11.RT s)
    (hN : NQ [C] s) : ∀ y ∈ (handleRecv (Z := Unit) blk cr s).1, EB false y.2 :=
  fun y hy => eb_handleRecv_res blk cr s (R11.resSc_of_rt hR) (by rw [hc]; exact hN) y hE hy

set_option maxHeartbeats 16000000 in
/-- **Every syscall**: every outcome `EB false`. -/
theorem eb_fl4HandleSyscall (hnd : numDomains = 1) (hE : EF Nq σe) (hI2 : I.2 = σe.idleSc)
    (hI1 : IrqOutV (fun _ => I.1) (uV σe)) (hCN : C ≠ N) (rep : Bool) (c : Syscall) (σ : State Unit)
    (hσ : EvP C N S I d Nq σe σ) : ∀ y ∈ ((fl4HandleSyscall (Z := Unit) rep c).run σ).1, EB false y.2 := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef) (s : State Unit), (fp = true → bl = false) →
      EvP C N S I d Nq σe s → ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr).run s).1,
        RQ (EB fp) y :=
    fun cl bl dn fp cptr s hfb hs => eb_fl4HandleInvocationR hnd C N S rep cl bl dn fp cptr hfb hCN s hs.1
  have hCap : ∀ reg, HKE (EvP C N S I d Nq σe) (EvP C N S I d Nq σe)
      (withoutPreemption (Z := Unit) (getCapReg reg)) := fun reg => hk_liftE (hk_of_ik (by evp_auto))
  -- a first-phase invocation, then `handle_recv`
  have hSR : ∀ (reg : Register) (b : Bool), HKE (EvP C N S I d Nq σe) (EB false) (do
      let cptr ← withoutPreemption (Z := Unit) (getCapReg reg)
      fl4HandleInvocationR rep false false true true cptr
      withoutPreemption (handleRecv true b)) := by
    intro reg b
    refine hke_bind (hCap reg) (fun cptr => ?_) (fun s h => eb_weak h.1.1.1)
    intro s hs y hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
    · have hE1 : EB true z.2 := (hInv false false true true cptr s (fun _ => rfl) hs z hz).2 a ha
      have hR : R11.RT z.2 := R11.rt_fl4HandleInvocationR hE hI2 hI1 rep false false true true cptr s hs.2.2.2 z hz
      have hN : NQ [C] z.2 := (nq_fl4HandleInvocationR C rep false false true true cptr s hs.2.2.1 z hz).2 rfl
      have hc : z.2.curThread = C :=
        ct_fl4HandleInvocationR (cq := C) rep false false true true cptr s hs.1.1.2.1 z hz
      unfold withoutPreemption at hy
      obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
      exact eb_recv true b z.2 hc hE1 hR hN v hv
    · exact (hInv false false true true cptr s (fun _ => rfl) hs z hz).1
  -- `handle_recv` alone
  have hRv : ∀ (blk cr : Bool), HKE (EvP C N S I d Nq σe) (EB false)
      (withoutPreemption (Z := Unit) (handleRecv blk cr)) := fun blk cr =>
    hk_liftE fun s hs y hy => eb_recv blk cr s hs.1.1.2.1 hs.1.1.1 hs.1.2.2.2.1 hs.1.1.2.2.2 y hy
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (hCap _) (fun cptr s hs y hy => (hInv _ _ _ _ cptr s (fun h => by cases h) hs y hy).1)
      (fun s h => eb_weak h.1.1.1) σ hσ
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (hCap _) (fun cptr s hs y hy => (hInv _ _ _ _ cptr s (fun h => by cases h) hs y hy).1)
      (fun s h => eb_weak h.1.1.1) σ hσ
  case sysCall =>
    simp only [fl4HandleSyscall]
    exact hke_bind (hCap _) (fun cptr s hs y hy => (hInv _ _ _ _ cptr s (fun h => by cases h) hs y hy).1)
      (fun s h => eb_weak h.1.1.1) σ hσ
  case sysYield =>
    simp only [fl4HandleSyscall]
    exact hk_liftE (fun s hs y hy => eb_handleYield_p s (hb_of_evp hs) (nq_weak_nil _ hs.1.1.2.2.2) hs.1.1.1 y hy)
      σ hσ
  case sysReplyRecv => simp only [fl4HandleSyscall]; exact hSR _ _ σ hσ
  case sysNBSendRecv => simp only [fl4HandleSyscall]; exact hSR _ _ σ hσ
  case sysNBSendWait => simp only [fl4HandleSyscall]; exact hSR _ _ σ hσ
  all_goals (simp only [fl4HandleSyscall]; exact hRv _ _ σ hσ)

set_option maxHeartbeats 8000000 in
/-- **The syscall event**: every outcome `EB false`. -/
theorem eb_fl4HandleEvent_sys (hnd : numDomains = 1) (hE : EF Nq σe) (hI2 : I.2 = σe.idleSc)
    (hI1 : IrqOutV (fun _ => I.1) (uV σe)) (hCN : C ≠ N) (rep : Bool) (c : Syscall) (σ : State Unit)
    (hσ : EvP C N S I d Nq σe σ) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1, EB false y.2 := by
  simp only [fl4HandleEvent]
  refine hke_bind (R := EvP C N S I d Nq σe) (hk_liftE (hk_of_ik (by evp_auto))) (fun _ => ?_)
    (fun s h => eb_weak h.1.1.1) σ hσ
  intro σ1 hσ1 y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [SInv.checkBudgetRestart_true hw hr] at hy
      exact eb_fl4HandleSyscall hnd hE hI2 hI1 hCN rep c σ1 hσ1 y hy
    · rename_i hr
      rw [Set.mem_singleton_iff.1 hy]
      have h1 := eb_checkBudgetRestart_p σ1 (hb_of_evp hσ1) (nq_weak_nil _ hσ1.1.1.2.2.2) hσ1.1.1.1 w hw
      cases hw1 : w.1
      · rw [hw1] at h1; exact h1
      · exact absurd hw1 hr
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

end E

end

end Fl4Proofs.P3.SInvQ.P17
