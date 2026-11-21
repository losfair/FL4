/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive ∧ NtfnScB across
`handle_syscall` and the syscall event** (sl2 handoff 4, third part; spec side
only, given `SlGap`).

* `sl_fl4HandleSyscall`: one arm per syscall. The pin of the shell is vi2's
  `Pinned c`; each invocation's pin `don ∧ ¬calling` implies it (`js_weak`).
  ReplyRecv / NBSendRecv / NBSendWait: after the first-phase invocation the
  receive needs sl2's `SAP I [ct] [ct] False ct`: `SL I [ct]` is this line's post,
  ScInv is sb2's `sb_handleInvocationR` (from the entry's `EntryOK`), IfLiveT
  with `ct` named is il2's `il_fl4HandleInvocationR` (`perfGapIL`), the current
  thread the CT family.
* `sl_fl4HandleEvent_sys`: `check_budget_restart` returns `true` only from an
  unchanged state.
-/
import Fl4Proofs.P3.SpecInvSlE2
import Fl4Proofs.P3.SpecInvNtfnQLX
import Fl4Proofs.P3.SpecInvSbT
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

section Y
variable {I : ObjRef × ObjRef} {ct : ObjRef} {N : Irq → ObjRef} {σe : State Unit}

theorem js_weak {d d' : Prop} (hd : d' → d) {s : State Unit} (h : Js I ct d N σe s) : Js I ct d' N σe s :=
  ⟨⟨⟨h.1.1.1, h.1.1.2.1, fun h' => h.1.1.2.2 (hd h')⟩, h.1.2⟩, h.2⟩

theorem js_sln {d : Prop} {s : State Unit} (h : Js I ct d N σe s) : SLN I [] s :=
  ⟨sl_mono h.1.1.1 (fun _ h => by cases h), h.1.2.2⟩

theorem js_ju {d : Prop} {s : State Unit} (h : Js I ct d N σe s) (hE : EF N σe) : Ju N ct s :=
  ⟨h.1.2.1, h.2.1, h.2.2.1, p3_of_view h.2.2.2.2.2.1 hE.1, h.2.2.2.1⟩

theorem js_rel {d : Prop} {s : State Unit} (h : Js I ct d N σe s) : SInvB.Rel σe s :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- A first-phase invocation then `handle_recv`. -/
theorem sl_sendRecv (hG : SlGap) (hE : EF N σe) (hEO : SInvB.EntryOK σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe)) (rep : Bool)
    (reg : Register) (b r : Bool) :
    HKE (Js I ct True N σe) (SLN I []) (do
      let cptr ← withoutPreemption (Z := Unit) (getCapReg reg)
      fl4HandleInvocationR rep false false true true cptr
      withoutPreemption (handleRecv b r)) := by
  refine hke_bind (R := Js I ct True N σe) (hk_liftE (hk_of_ik (by js_auto))) (fun cptr => ?_) (fun s h => js_sln h)
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · have hJS := sl_fl4HandleInvocationR hG I N σe hE hI2 hI1 ct rep false false true true cptr σ
      (js_weak (fun _ => trivial) hσ) z hz
    have hSI : SInvB.ScInv z.2 := SInvB.sb_handleInvocationR SInvB.scGap rep false false true true cptr σe hEO σ
      hσ.1.1.2.1 (js_rel hσ) z hz
    have hIL : IL [ct] z.2 :=
      (il_fl4HandleInvocationR perfGapIL N ct rep false false true true cptr σ (js_ju hσ hE) z hz).2 rfl
    have hct : z.2.curThread = ct :=
      ct_fl4HandleInvocationR (cq := ct) rep false false true true cptr σ hσ.2.2.1 z hz
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy
    exact sl_handleRecv ct b r z.2 ⟨⟨⟨hJS.2 rfl, hSI, fun h => h.elim⟩, hIL, hJS.1.2⟩, hct⟩ w hw
  · exact (sl_fl4HandleInvocationR hG I N σe hE hI2 hI1 ct rep false false true true cptr σ
      (js_weak (fun _ => trivial) hσ) z hz).1

set_option maxHeartbeats 8000000 in
theorem sl_fl4HandleSyscall (hG : SlGap) (hE : EF N σe) (hEO : SInvB.EntryOK σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe))
    (rep : Bool) (c : Syscall) :
    HKE (Js I ct (SInvI.Pinned c) N σe) (SLN I []) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn : Bool) (cptr : CapRef), (dn = true ∧ cl = false → SInvI.Pinned c) →
      HKE (Js I ct (SInvI.Pinned c) N σe) (SLN I []) (fl4HandleInvocationR (Z := Unit) rep cl bl dn false cptr) :=
    fun cl bl dn cptr hd σ hσ y hy =>
      (sl_fl4HandleInvocationR hG I N σe hE hI2 hI1 ct rep cl bl dn false cptr σ (js_weak hd hσ) y hy).1
  have hRecv : ∀ b r, HKE (Js I ct (SInvI.Pinned c) N σe) (SLN I []) (withoutPreemption (Z := Unit) (handleRecv b r)) :=
    fun b r => hk_liftE (fun s h y hy => sl_handleRecv ct b r s
      ⟨⟨⟨h.1.1.1, h.1.1.2.1, fun h' => h'.elim⟩, h.1.2⟩, h.2.2.1⟩ y hy)
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Js I ct _ N σe) (hk_liftE (hk_of_ik (by js_auto)))
      (fun cptr => hInv _ _ _ cptr (fun h => absurd h.1 (by decide))) (fun s h => js_sln h)
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Js I ct _ N σe) (hk_liftE (hk_of_ik (by js_auto)))
      (fun cptr => hInv _ _ _ cptr (fun h => absurd h.1 (by decide))) (fun s h => js_sln h)
  case sysCall =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Js I ct _ N σe) (hk_liftE (hk_of_ik (by js_auto)))
      (fun cptr => hInv _ _ _ cptr (fun h => absurd h.2 (by decide))) (fun s h => js_sln h)
  case sysYield =>
    simp only [fl4HandleSyscall]
    refine hk_liftE (fun s h y hy => ⟨?_, ?_⟩)
    · unfold handleYield at hy
      refine (?_ : HK (SAP I [ct] [ct] False ct) (SL I []) _) s ⟨⟨h.1.1.1, h.1.1.2.1, fun h' => h'.elim⟩, h.1.2⟩ y hy
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun _ => ?_
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun _ => ?_
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun _ => ?_
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun _ => ?_
      refine shk_bind (R := SL I []) (shk_post (sl_chargeBudget (I := I) (K := [ct]) (L := [ct]) (t := ct) _ _)
        fun _ h => sl_mono (K' := []) h (fun _ h => by cases h)) fun _ => ?_
      exact shk_ik (by sl_auto) fun _ h => h
    · exact nb_handleYield s h.1.2.2 y hy
  case sysReplyRecv =>
    exact fun σ hσ y hy => sl_sendRecv hG hE hEO hI2 hI1 rep _ _ _ σ (js_weak (fun _ => Or.inl rfl) hσ) y hy
  case sysNBSendRecv =>
    exact fun σ hσ y hy => sl_sendRecv hG hE hEO hI2 hI1 rep _ _ _ σ (js_weak (fun _ => Or.inr (Or.inl rfl)) hσ) y hy
  case sysNBSendWait =>
    exact fun σ hσ y hy => sl_sendRecv hG hE hEO hI2 hI1 rep _ _ _ σ (js_weak (fun _ => Or.inr (Or.inr rfl)) hσ) y hy
  all_goals
    simp only [fl4HandleSyscall]
    exact hRecv _ _

/-- The syscall event. -/
theorem sl_fl4HandleEvent_sys (hG : SlGap) (hE : EF N σe) (hEO : SInvB.EntryOK σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe))
    (rep : Bool) (c : Syscall) :
    HKE (Js I ct (SInvI.Pinned c) N σe) (SLN I []) (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hke_bind (R := Js I ct _ N σe) (hk_liftE (hk_of_ik (by js_auto))) (fun _ => ?_) (fun s h => js_sln h)
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [SInv.checkBudgetRestart_true hw hr] at hy
      exact sl_fl4HandleSyscall hG hE hEO hI2 hI1 rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]
      exact ⟨sl_mono (sl_checkBudgetRestart (I := I) (K := [ct]) (L := [ct]) (t := ct) σ
        ⟨⟨hσ.1.1.1, hσ.1.1.2.1, fun h => h.elim⟩, hσ.1.2⟩ w hw) (fun _ h => by cases h),
        nb_checkBudgetRestart σ hσ.1.2.2 w hw⟩
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

end Y

end

end Fl4Proofs.P3.SInvL
