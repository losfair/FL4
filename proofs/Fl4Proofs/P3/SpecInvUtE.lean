/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut3): **`UtInv'` across the
kernel entries** (spec side only; imports only Fl4Spec via SpecInvUtG).

* The performs that need the decode's facts (`InvOKV`, SpecInvUtD): untyped
  retype (ut2's `invokeUntyped_utInv'` / `invokeUntyped_reset_utInv'`), CNode
  insert / move / rotate (SpecInvUtMv), MakePool (SpecInvUtMp), SetIRQHandler;
  every other perform by the generated frames (SpecInvUtG). `uiP_fl4Perform`.
* The invocation shell (`fl4HandleInvocationR`, a copy of invC's
  `dpe_handleInvocationR`): the lookups give the invoked cap in its slot and
  the extra caps in theirs, the decode `InvOKV` (`okv_fl4Decode`), and every
  step before the perform keeps the view, so the facts and `DetypeOK` hold at
  the perform.
* `DetypeOK` [J] is a premise of the syscall entry state only (ut2's; l4v
  `untyped_children_in_mdb` + `if_unsafe_then_cap` + `mdb_cte_at`): it reaches
  the perform because the steps before it keep the view (the budget check
  `checkBudgetRestart` keeps it whenever it lets the syscall run,
  `checkBudget_true`). The other events need no premise.
* Tops: `kentry_utInv`, `kcall_utInv` (every event), `kcall_utInv_other`
  (interrupts, faults, unknown syscalls: no premise).
-/
import Fl4Proofs.P3.SpecInvUtG
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Membership helpers -/

theorem mem_ret_bindE {ε α β : Type} {m : NonDetE (State Unit) ε α} {b : β} {σ : State Unit}
    {y : Except ε β × State Unit} (hy : y ∈ ((m >>= fun _ => NonDetE.returnOk b).run σ).1) :
    ∃ z ∈ (m.run σ).1, y.2 = z.2 := by
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact ⟨z, hz, by rw [Set.mem_singleton_iff.1 hy]⟩
  · exact ⟨z, hz, rfl⟩

/-! ## CNode -/

/-- **`invoke_cnode` keeps `UtInv'`** from the decode's facts. -/
theorem uiP_invokeCnode (ci : CnodeInvocation) (σ : State Unit) (hI : UtInv' σ) (hok : CnOKV (uV σ) ci) :
    ∀ y ∈ ((invokeCnode (Z := Unit) ci).run σ).1, UtInv' y.2 := by
  intro y hy
  cases ci with
  | revokeCall d => exact ui_capRevoke d σ hI y hy
  | deleteCall d => exact ui_capDelete d σ hI y hy
  | insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact hv_capInsert c src dest σ ⟨hI, hok⟩ x hx
  | moveCall c src dest =>
    obtain ⟨c0, hs, hd, hr, hne⟩ := hok
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (hv_capMove hI hs hd hr hne σ rfl x hx).1
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, hr1, hr2, h21, h23, h3⟩ := hok
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · exact hv_capSwap (Ne.symm h21) hr1 hr2 σ ⟨hI, h1, h2⟩ x hx
    · rename_i h13
      obtain ⟨x1, hx1, hx⟩ := hx
      obtain ⟨hI1, hs1, hd1, hoth⟩ := hv_capMove hI h2 (h3 h13) hr2 h23 σ rfl x1 hx1
      have h1' : (uV x1.2).2.1 s1 = some c1' := by
        rw [hoth s1 (Ne.symm h21) h13]; exact h1
      exact (hv_capMove hI1 h1' hs1 hr1 (Ne.symm h21) x1.2 rfl x hx).1
  | cancelBadgedSendsCall cap =>
    cases cap
    case endpointCap ep b r =>
      exact (show IKE UtInv' (withoutPreemption (Z := Unit) (NonDet.when (b ≠ 0) (cancelBadgedSends ep b))) by
        ui_auto) σ hI y hy
    all_goals
      obtain ⟨x, hx, -⟩ := mem_liftE' (show y ∈ ((NonDetE.liftE (ε := Unit)
        (NonDet.fail : NonDet (State Unit) Unit)).run σ).1 from hy)
      exact hx.elim

/-! ## The performs -/

theorem uiP_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (hI : UtInv' σ)
    (hD : DetypeOK σ) (hok : InvOKV (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, UtInv' y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    obtain ⟨h1, h2⟩ := hok
    cases ui with
    | retype s reset base rb ty sz slots dev =>
      cases reset
      · exact invokeUntyped_utInv' hI (utRetOK_of_V h1) (destNull_of_V h2) z hz
      · exact invokeUntyped_reset_utInv' hI hD (utRetOK_of_V h1) (destNull_of_V h2) z hz
  | invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact uiP_invokeCnode ci σ hI hok z hz
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    cases i with
    | setIRQHandler irq c sl =>
      have hnu : ∀ d b n f, c ≠ .untypedCap d b n f := hok
      exact (show IKE UtInv' (NonDetE.liftE (ε := Unit) (invokeIrqHandler (Z := Unit) (.setIRQHandler irq c sl))) by
        refine ike_liftE ?_; simp only [invokeIrqHandler]; ui_auto) σ hI z hz
    | _ => exact (show IKE UtInv' (NonDetE.liftE (ε := Unit) (invokeIrqHandler (Z := Unit) _)) by
        refine ike_liftE ?_; simp only [invokeIrqHandler]; ui_auto) σ hI z hz
  | invokeArchObject ai =>
    cases ai with
    | spec i =>
      cases i with
      | invokeASIDControl a =>
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
        obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
        obtain ⟨z, hz, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hx]
        exact makePool_utInv' hI hD (mpOK_of_V hok) z hz
      | _ =>
        exact (show IKE UtInv' _ by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]; ui_auto) σ hI y hy
    | _ => exact (show IKE UtInv' _ by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; ui_auto) σ hI y hy
  | _ => exact (show IKE UtInv' _ by simp only [fl4PerformInvocation]; ui_auto) σ hI y hy

/-! ## The invocation shell -/

/-- The `syscall` shell, pointwise (invC's copy of sch12's `syscall_post`). -/
theorem syscall_postU {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ : State Unit} {I Q : State Unit → Prop}
    (h1 : ∀ w ∈ ((ExceptT.run mF) σ).1, I w.2)
    (h2 : ∀ f s, I s → ∀ v ∈ (hF f s).1, Q v.2)
    (h3 : ∀ a s, (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → ∀ w ∈ ((ExceptT.run (mE a)) s).1, I w.2)
    (h4 : ∀ e s, I s → ∀ v ∈ (hE e s).1, Q v.2)
    (h5 : ∀ a s b s', (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → (.ok b, s') ∈ ((ExceptT.run (mE a)) s).1 →
      I s' → ∀ y ∈ ((mFin b).run s').1, Q y.2) :
    ∀ y ∈ ((syscall mF hF mE hE mFin).run σ).1, Q y.2 := by
  intro y hy
  unfold syscall withoutPreemption at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE' hy
  · obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, hv, rfl⟩ := mem_liftE' hy
      exact h2 f s (h1 _ hw) v hv
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE' hy
      · obtain ⟨w, hw', rfl⟩ := mem_liftE' hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, hv, rfl⟩ := mem_liftE' hy
          exact h4 e s' (h3 a s hw _ hw') v hv
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy
      · obtain ⟨w, -, rfl⟩ := mem_liftE' hz
        cases he
  · obtain ⟨w, -, rfl⟩ := mem_liftE' hz
    cases he

/-- `UtInv'` kept from a state that also satisfies `DetypeOK`. -/
def IKD {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, UtInv' σ → DetypeOK σ → ∀ y ∈ (m σ).1, UtInv' y.2

abbrev IKDE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKD (ExceptT.run m)

theorem ikd_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IK UtInv' m) : IKD m :=
  fun σ hI _ y hy => h σ hI y hy

theorem ikde_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hg : ∀ a, IKDE (g a)) : IKDE (m >>= g) := by
  intro σ hI hD y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · have hv : uV z.2 = uV σ := hm (uV σ) σ rfl z hz
    exact hg a z.2 (utInv'_of_view hv hI) (detypeOK_view hv hD) y hy
  · exact utInv'_of_view (hm (uV σ) σ rfl z hz) hI

theorem ikde_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKDE m) (hg : ∀ a, IKE UtInv' (g a)) : IKDE (m >>= g) := by
  intro σ hI hD y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm σ hI hD z hz) y hy
  · exact hm σ hI hD z hz

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `UtInv'`**, from `DetypeOK` at its start. -/
theorem uiD_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKDE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikde_bind_uk (fun _ => by uk_auto) fun thread => ikde_bind_uk (fun _ => by uk_auto) fun info => ?_
  intro σ hI hD y hy
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hOk : OkV (uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ).2.1 p.2 = some p.1) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCaps _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := fun s => UtInv' s ∧ uV s = uV σ) (Q := UtInv')
    (fun w hw => ⟨utInv'_of_view (hF _ σ rfl w hw) hI, hF _ σ rfl w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK UtInv' (NonDet.when blocking (handleFault thread f)) by ui_auto) s hs.1 v hv
  · intro a s has w hw
    have hs : UtInv' s ∧ uV s = uV σ := ⟨utInv'_of_view (hF _ σ rfl _ has) hI, hF _ σ rfl _ has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    exact ⟨utInv'_of_view (hE _ s rfl w hw) hs.1, (hE _ s rfl w hw).trans hs.2⟩
  · intro e s hs v hv
    exact (ik_utInv'_of_uk fun _ => by uk_auto) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    have hdec : InvOKV (uV σ) b := by
      have := okv_bind_uk (P := InvOKV (uV σ)) (fun _ => ike_liftE (uk_getMrs _ _ _)) (fun args =>
        okv_fl4Decode (w := uV σ) fp info.miLabel args cptr sl cap ex buf hc hex) s hvs b s' hbs
      exact this
    have hD' : DetypeOK s' := detypeOK_view hI'.2 hD
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := (show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2
      have hI1 : UtInv' s1 := utInv'_of_view hz' hI'.1
      have hok1 : InvOKV (uV s1) b := by rw [hv1]; exact hdec
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := uiP_fl4Perform blocking calling don b s1 hI1 (detypeOK_view hz' hD') hok1 _ hz2
        exact (ike_utInv'_of_uk fun _ => by uk_auto) s2 hs2 y hy
      · exact uiP_fl4Perform blocking calling don b s1 hI1 (detypeOK_view hz' hD') hok1 _ hz2
    · exact utInv'_of_view ((show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz) hI'.1

/-! ## The syscall paths -/

set_option maxHeartbeats 4000000 in
theorem uiD_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKDE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall]
  all_goals first
    | exact ikde_bind_uk (fun _ => by uk_auto) fun _ => uiD_handleInvocationR _ _ _ _ _ _
    | exact ikde_bind_uk (fun _ => by uk_auto) fun _ =>
        ikde_bind (uiD_handleInvocationR _ _ _ _ _ _) fun _ => by ui_auto
    | exact ikd_of_ik (by ui_auto)

/-- **The budget check keeps the view whenever it lets the syscall run.** -/
theorem checkBudget_true {σ : State Unit} {x : Bool × State Unit} (hx : x ∈ (checkBudget (Z := Unit) σ).1)
    (ht : x.1 = true) : uV x.2 = uV σ := by
  unfold checkBudget at hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx1
  obtain ⟨x2, hx2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx
  have hv3 := uk_mem (fun _ => uk_getScRefillSufficient _ _) hx3
  dsimp only at hx
  split at hx
  · obtain ⟨x4, hx4, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hx4
    rw [Set.mem_singleton_iff.1 hx]; exact hv3
  · obtain ⟨x4, hx4, hx⟩ := hx
    obtain ⟨x5, hx5, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx] at ht
    cases ht

theorem checkBudgetRestart_true {σ : State Unit} {x : Bool × State Unit}
    (hx : x ∈ (checkBudgetRestart (Z := Unit) σ).1) (ht : x.1 = true) : uV x.2 = uV σ := by
  unfold checkBudgetRestart at hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨x2, hx2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx
  have hv3 := uk_mem (fun _ => uk_getThreadState _) hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx] at ht ⊢
  have hv4 := uk_mem (fun _ => by uk_auto : ∀ v, UK v (NonDet.when (¬x1.1 = true ∧ runnable x3.1)
    (setThreadState (Z := Unit) x1.2.curThread .restart))) hx4
  rw [hv4, hv3, checkBudget_true hx1 ht]

set_option maxHeartbeats 4000000 in
theorem ui_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : IKE UtInv' (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; ui_auto

set_option maxHeartbeats 4000000 in
theorem uiD_fl4HandleEvent (rep : Bool) (ev : Event) : IKDE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikde_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) fun _ => ?_
    intro σ hI hD y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : UtInv' x.2 := ui_checkBudgetRestart σ hI x hx
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        have hv := checkBudgetRestart_true hx ht
        exact uiD_fl4HandleSyscall rep c x.2 hIx (detypeOK_view hv hD) y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hIx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikd_of_ik (ui_handleEvent_other ev fun c e => h ⟨c, e⟩)

theorem ikd_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKD m) (hg : ∀ a, IK UtInv' (g a)) : IKD (m >>= g) := by
  intro σ hI hD y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm σ hI hD x hx) y hy

theorem ikd_bind_uk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ v, UK v m) (hg : ∀ a, IKD (g a)) : IKD (m >>= g) := by
  intro σ hI hD y ⟨x, hx, hy⟩
  have hv := uk_mem hm hx
  exact hg x.1 x.2 (utInv'_of_view hv hI) (detypeOK_view hv hD) y hy

set_option maxHeartbeats 4000000 in
theorem uiD_fl4CallKernel (rep : Bool) (ev : Event) : IKD (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikd_bind ?_ fun _ => by ui_auto
  intro σ hI hD y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := uiD_fl4HandleEvent rep ev σ hI hD z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE UtInv' (withoutPreemption (Z := Unit) preemptionPath) by ui_auto) s hz' y hy

theorem ui_fl4CallKernel_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IK UtInv' (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind ?_ fun _ => by ui_auto
  refine ike_handleE ?_ fun _ => by ui_auto
  rw [fl4HandleEvent_other rep ev h]
  exact ui_handleEvent_other ev h

/-! ## Tops -/

/-- **`UtInv'` across the syscall entry**, from `DetypeOK` [J] at the entry
state (a stepping stone: not a carried invariant, see the module docstring). -/
theorem kentry_utInv (c : Syscall) {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, UtInv' y.2 := by
  unfold fl4KernelEntrySyscall
  exact ikd_bind_uk (fun _ => ik_gets _) (fun ct => ikd_bind_uk (fun _ => uk_fl4SyscallFaultIP ct)
    fun _ => uiD_fl4CallKernel true _) σ hI hDT

/-- **`UtInv'` across every kernel event** (`fl4CallKernel rep ev`; `DetypeOK`
[J] is used only by a syscall's invocation). -/
theorem kcall_utInv (rep : Bool) (ev : Event) {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, UtInv' y.2 :=
  uiD_fl4CallKernel rep ev σ hI hDT

/-- **`UtInv'` across interrupts, faults and the other non-syscall events**, with no premise. -/
theorem kcall_utInv_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hI : UtInv' σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, UtInv' y.2 :=
  ui_fl4CallKernel_other rep ev h σ hI

end

end Fl4Proofs.P3.SInvU
