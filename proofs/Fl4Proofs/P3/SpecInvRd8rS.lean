/-
P3 (DESIGN.md §9), invariant line G1 (rd8r, KENTRY-PLAN rd8p handoff 1-2):
**`CurHold` at every error outcome of the syscall event, and rd8j's `PreR`
from carried entry facts** (spec side only, outside the JAtZ cone).

* Shell invariant `JH := R18.JE ∧ HO` (ctq18's `JE` = sl3's `Js` ∧ `EB true` ∧
  `Simple`, only for the current thread `ct` and `NQ [ct]` that `Js` names). It is
  kept by `update_time_stamp`, `check_budget_restart` on its `true` outcome, the
  front (`jh_auto`: ctq18's `je_auto` and the generated `ho_` family) and the
  Restart write of `ct` (`ho_setThreadState_ct`). At the perform it gives
  SpecInvRd8rC's `HQ` (`HO`, and `NQ []` from `Js`'s `NQ [ct]`), so
  `hqx_fl4PerformInvocation` gives `HO` at every error outcome. The other phases
  never error (ctq16's `NE`, ctq18's `er_syscall_post`).
* `ho_entry`: `HO` at the event start from `CtExit`, `CurScT` and sb2's `ScBackS`:
  the SC's back pointer makes `ct` the only TCB bound to `cur_sc`, and `ct` is
  running (or the idle thread).
* **`preR_of2`**: rd8p's `preR_of` without its two event-level inputs: `hEN`
  (`EB true ∧ NQ []` at the error outcomes) from ctq18's `ebr_fl4HandleEvent` and
  nq3's `nq_fl4HandleEvent_sys`; `hH` (`CurHold`) from `HO` (`curHold_of_ho`).
* **`kcall_rdyOff6p`**: rd8m's `kcall_rdyOff6m` without the `PreR` input.
-/
import Fl4Proofs.P3.SpecInvRd8rC
import Fl4Proofs.P3.SpecInvRd8pB
import Fl4Proofs.P3.SpecInvRd8mE
open Classical

namespace Fl4Proofs.P3.SInvR.B8r
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.R16 Fl4Proofs.P3.SInvQ.R18 Fl4Proofs.P3.SInvR
  Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The triple -/

/-- From `P`, every error outcome has `HO`. -/
def HXR (P : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, P σ → ∀ y ∈ (m.run σ).1, ∀ e, y.1 = .error e → HO y.2

theorem hxr_of_ne {P : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : NE m) : HXR P m :=
  fun σ _ y hy e he => absurd he (h σ y hy e)

theorem hxr_bind_ike {P : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : IKE P m) (hP : ∀ s, P s → HO s) (hg : ∀ a, HXR P (g a)) :
    HXR P (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a z.2 (hm σ hσ z hz) y hy e he
  · exact hP _ (hm σ hσ z hz)

theorem hxr_bind_ne {P : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : HXR P m) (hg : ∀ a, NE (g a)) : HXR P (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
  · exact absurd he (hg a z.2 y hy e)
  · exact hm σ hσ z hz e' he'

theorem hxr_gets_bind {P : State Unit → Prop} {ε β γ : Type} {g : State Unit → β}
    {k : β → NonDetE (State Unit) ε γ}
    (h : ∀ σ, P σ → ∀ y ∈ ((k (g σ)).run σ).1, ∀ e, y.1 = .error e → HO y.2) :
    HXR P (NonDetE.liftE (NonDet.gets g) >>= k) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    obtain rfl := mem_gets hw
    simp only [Except.ok.injEq] at ha; subst ha
    exact h σ hσ y hy
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-! ## The shell invariant -/

section S
variable {I : ObjRef × ObjRef} {N : Irq → ObjRef} {σe : State Unit} {ct : ObjRef} {d : Prop}

/-- The shell invariant: ctq18's `JE` and `HO`. -/
abbrev JH (I : ObjRef × ObjRef) (ct : ObjRef) (d : Prop) (N : Irq → ObjRef) (σe s : State Unit) : Prop :=
  JE I ct d N σe s ∧ HO s

theorem jh_ofK {α : Type} {m : NonDet (State Unit) α} (h1 : IK (JE I ct d N σe) m) (h2 : HOK m) :
    IK (JH I ct d N σe) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

macro "jh_auto" : tactic => `(tactic| ((refine jh_ofK ?_ ?_); je_auto; ho_auto))

set_option maxHeartbeats 16000000 in
/-- **Every error outcome of `handle_invocation` from a `JH` state has `HO`.** -/
theorem hxr_fl4HandleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    HXR (JH I ct d N σe) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine hxr_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.1.1.2.2.1
  simp only [hc, withoutPreemption]
  refine hxr_bind_ike (P := JH I ct d N σe) (?_ : IKE (JH I ct d N σe) _) (fun s h => h.2)
    (fun info => ?_) σ hσ
  · exact ike_liftE (by jh_auto)
  intro σ' hσ' y0 hy0
  refine er_syscall_post (I := JH I ct d N σe) (Q := HO) ?_ ?_ y0 hy0
  · intro a s has w hw
    have hs : JH I ct d N σe s := by
      refine (?_ : IKE (JH I ct d N σe) _) σ' hσ' _ has
      jh_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (JH I ct d N σe) _) s hs w hw
    jh_auto
  · intro a s b s' has hbs hI y hy e he
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      have hJ1 : Js I ct d N σe w.2 := js_sts s' hI.1.1 w hw
      have hO1 : HO w.2 := ho_setThreadState_ct ct .restart s' hI.1.1.2.2.1.symm trivial hI.2 w hw
      obtain ⟨r, s1⟩ := w
      dsimp only at hJ1 hO1
      obtain ⟨z2, hz2, ⟨rp, -, hy⟩ | ⟨e2, he2, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨v, -, rfl⟩ := ft_mem_liftE hy
        cases he
      · exact hqx_fl4PerformInvocation blocking calling don b s1 ⟨hO1, nq_weak_nil _ hJ1.2.1⟩ z2 hz2 e2 he2
    · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
      cases he'

/-- **`handle_syscall`.** -/
theorem hxr_fl4HandleSyscall (rep : Bool) (c : Syscall) :
    HXR (JH I ct d N σe) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef),
      HXR (JH I ct d N σe) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => hxr_fl4HandleInvocationR rep cl bl dn fp cptr
  have hCap : ∀ reg, IKE (JH I ct d N σe) (withoutPreemption (Z := Unit) (getCapReg reg)) :=
    fun reg => ike_liftE (by jh_auto)
  cases c
  all_goals simp only [fl4HandleSyscall]
  all_goals first
    | exact hxr_bind_ike (hCap _) (fun _ h => h.2) fun cptr => hInv _ _ _ _ cptr
    | exact hxr_bind_ike (hCap _) (fun _ h => h.2) fun cptr =>
        hxr_bind_ne (hInv _ _ _ _ cptr) fun _ => ne_withoutPreemption _
    | exact hxr_of_ne (ne_withoutPreemption _)

/-- **Every error outcome of the event from a `JH` state has `HO`.** -/
theorem hxr_fl4HandleEvent (rep : Bool) (ev : Event) :
    HXR (JH I ct d N σe) (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c =>
    simp only [fl4HandleEvent]
    refine hxr_bind_ike (ike_liftE (?_ : IK (JH I ct d N σe) (updateTimeStamp (Z := Unit)))) (fun _ h => h.2)
      fun _ => ?_
    · jh_auto
    intro σ hσ y hy e he
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      simp only [Except.ok.injEq] at hr
      subst hr
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        rw [Fl4Proofs.P3.SInv.checkBudgetRestart_true hw ht] at hy
        exact hxr_fl4HandleSyscall rep c σ hσ y hy e he
      · obtain rfl := Set.mem_singleton_iff.1 hy
        cases he
    · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
      cases he'
  | _ => exact hxr_of_ne (ne_fl4HandleEvent_other rep _ fun c h => by cases h)

end S

/-! ## The entry and `PreR` -/

/-- **`HO` at the event start**: `ct` is the only TCB bound to `cur_sc`. -/
theorem ho_entry {σ : State Unit} (hX : SInvAll.CtExit σ) (hC : CurScT σ) (hS : SInvB.ScBackS σ) : HO σ := by
  intro t x hx hc
  obtain ⟨x0, hx0, hs0⟩ := hX
  obtain ⟨y1, k1, h1, e1, -⟩ := hS t x _ hx hc
  obtain ⟨y2, k2, h2, e2, -⟩ := hS _ x0 _ hx0 (hC x0 hx0)
  rw [h1] at h2
  cases h2
  rw [e1] at e2
  cases e2
  have ex : x = x0 := by rw [hx] at hx0; cases hx0; rfl
  subst ex
  rcases hs0 with h | h <;> rw [h] <;> first | exact rfl | exact trivial

/-- **rd8j's `PreR` from carried entry facts** (module docstring): rd8p's
`preR_of` with `hEN` and `hH` discharged. -/
theorem preR_of2 (rep : Bool) (c : Syscall) (σ : State Unit) {I : ObjRef × ObjRef} {d : Prop}
    {Nq : Irq → ObjRef} (hEF : A8.EF σ) (h1 : SInvQ.T1 σ)
    (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) (hE : SInvB.EntryOK σ)
    (hPs : ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hF : SysF I d Nq σ) (hJ : JE I σ.curThread d Nq σ σ) : B8j.PreR rep c σ := by
  refine B8p.preR_of rep c σ hEF h1 hEB hIO hV hE hPs hPr (fun y hy e he => ?_) (fun y hy e he => ?_)
  · exact ⟨ebr_fl4HandleEvent hF.2.2.2.1 hF.2.2.2.2.1 rep _ σ hJ y hy e he,
      nq_fl4HandleEvent_sys σ.curThread rep c σ hF.1 y hy⟩
  · exact curHold_of_ho (hxr_fl4HandleEvent rep _ σ ⟨hJ, ho_entry hEF.ct hEF.cs hE.sc.back⟩ y hy e he)

/-! ## The top -/

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event**: rd8m's
`kcall_rdyOff6m` without the `PreR` input (`preR_of2`). -/
theorem kcall_rdyOff6p (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hRS : σ.schedulerAction = .resumeCurThread)
    (hPs : ∀ c, ev = .syscallEvent c → ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ c, ev = .syscallEvent c → ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hRc : ∀ c, ev = .syscallEvent c → B8m.RcvIn rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hRA : ∀ c, ev = .syscallEvent c → A13a.RecvTA rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine B8m.kcall_rdyOff6m hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hIO hRS hPs hPr (fun c e => ?_)
    hRc hP hRA hRdF
  subst e
  obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS _ rfl
  have hσ := P17.evp_start (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ
  exact preR_of2 rep c σ (hEF (by intro h; cases h)) (SInvQ.tq_t1 hX.1.1.1) ⟨⟨hX.1, h4⟩, hR⟩ hIO
    hX10.eo.vfh hX10.eo (hPs c rfl) (hPr c rfl) (hS c rfl) ⟨hσ.2.2.2.1, hσ.1.1.1, hσ.1.1.2.2.1⟩

end

end Fl4Proofs.P3.SInvR.B8r
