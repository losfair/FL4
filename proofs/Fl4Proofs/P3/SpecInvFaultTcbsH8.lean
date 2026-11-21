/-
P3 (DESIGN.md §9), invariant line G1 (ft3): **`B` across the syscall
shell's pieces** (spec side only). With `ct` the current thread, the syscall
runs in `B [ct] [ct] [ct] (· = ct)`: `ct` has no fault, is exempt (so active or
in a fault state, which `fqX` keeps for exempt threads) and is in no
notification queue and not BlockedOnNotification.

* `fl4PerformInvocation` (after `set_thread_state ct Restart`, so `NoRpl [ct]`):
  the endpoint send is `b_sendIpc` with `ct` the sender (made exempt twice,
  `b_addE`), the reply is `b_doReplyTransfer`, the rest is uniform (`b_autoE`).
* `ft_syscall_post` (sch12's `syscall_post`, SpecInvDom's copy), the
  exception-monad pre/posts (`HKE`, result-dependent `HKR` with `okErr`).
* `handle_yield`, `preemption_path`: from `B [] [] [ct] (· = ct)` (the charge
  with `L = []` is an `IK`: `b_chargeBudget_nil`, `b_checkBudget_nil`).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH7
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L E K : List ObjRef} {C : ObjRef → Prop}

/-! ## Exception-monad pre/post combinators -/

theorem ft_mem_bindE {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem ft_mem_liftE {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

/-- The `syscall` shell, pointwise (SpecInvDom's `syscall_post'`, copied: that
module is outside this line's import closure). -/
theorem ft_syscall_post {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
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
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
      exact h2 f s (h1 _ hw) v hv
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
      · obtain ⟨w, hw', rfl⟩ := ft_mem_liftE hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
          exact h4 e s' (h3 a s hw _ hw') v hv
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy
      · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
        cases he
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-- `HK` over the run of an exception computation (any result). -/
abbrev HKE (P Q : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  HK P Q (ExceptT.run m)

theorem hk_liftE {P Q : State Unit → Prop} {ε α : Type} {m : NonDet (State Unit) α} (h : HK P Q m) :
    HKE P Q (NonDetE.liftE (ε := ε) m) := by
  intro σ hσ y hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact h σ hσ x hx

theorem hke_bind {P R Q : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : HKE P R m) (hg : ∀ a, HKE R Q (g a)) (hRQ : ∀ s, R s → Q s) :
    HKE P Q (m >>= g) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hg a s (hm σ hσ _ hz) y hy
  · exact hRQ _ (hm σ hσ _ hz)

theorem hke_gets_bind {P Q : State Unit → Prop} {ε β γ : Type} {g : State Unit → β}
    {k : β → NonDetE (State Unit) ε γ} (h : ∀ σ, P σ → ∀ y ∈ ((k (g σ)).run σ).1, Q y.2) :
    HKE P Q (NonDetE.liftE (NonDet.gets g) >>= k) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    obtain rfl := mem_gets hw
    simp only [Except.ok.injEq] at ha; subst ha
    exact h σ hσ y hy
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-- The post of `ok` results and the post of errors. -/
def okErr (Q0 I : State Unit → Prop) {ε α : Type} : Except ε α → State Unit → Prop
  | .ok _, s => Q0 s
  | .error _, s => I s

/-- Pre/post depending on the result. -/
def HKR (P : State Unit → Prop) {ε α : Type} (Q : Except ε α → State Unit → Prop)
    (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, P σ → ∀ y ∈ ((ExceptT.run m) σ).1, Q y.1 y.2

section R
variable {I Q0 : State Unit → Prop} {ε : Type}

theorem hkr_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKE I m) (hg : ∀ a, HKR I (okErr Q0 I) (g a)) : HKR I (okErr Q0 I) (m >>= g) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hg a s (hm σ hσ _ hz) y hy
  · exact hm σ hσ _ hz

theorem hkr_liftE {α : Type} {m : NonDet (State Unit) α} (h : HK I Q0 m) :
    HKR I (okErr Q0 I) (NonDetE.liftE (ε := ε) m) := by
  intro σ hσ y hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact h σ hσ x hx

theorem hkr_throw {α : Type} (e : ε) : HKR I (okErr Q0 I) (NonDetE.throwError e : NonDetE (State Unit) ε α) := by
  intro σ hσ y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact hσ

theorem hk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α}
    (hm : HKR I (okErr Q0 I) m) (hh : ∀ e, HK I Q0 (h e)) : HK I Q0 (NonDetE.catch m h) := by
  intro σ hσ y ⟨z, hz, hy⟩
  have := hm σ hσ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact this
  | error e => exact hh e s this y hy

end R

/-! ## The current thread's invariant -/

theorem i0_dropE {ct : ObjRef} {σ : State Unit} (h : B [ct] [ct] K C σ) : B [ct] [] K C σ :=
  b_dropE h fun x hx => Or.inl ((h.1.1 ct _ hx).2.1 (List.mem_singleton_self _))

theorem i0_q1 {ct : ObjRef} {σ : State Unit} (h : B [ct] [ct] K C σ) : B [] [] K C σ :=
  b_mono (i0_dropE h) (fun _ h => by simp at h) (fun _ h => h) id

theorem q1_q0 {σ : State Unit} (h : B [] [] K C σ) : B [] [] [] C σ :=
  b_mono h (fun _ h => h) (fun _ h => by simp at h) id

/-! ## The budget charge with `L = []` -/

theorem b_chargeBudget_nil (n : Ticks) (cto : Bool) (c : ObjRef) (hcK : c ∈ K) :
    BK [] [] K (· = c) (chargeBudget (Z := Unit) n cto) :=
  fun σ hσ y hy => b_chargeBudget n cto c hcK (fun h => by simp at h) σ hσ y hy
macro_rules | `(tactic| b_leaf) => `(tactic| (with_reducible refine b_chargeBudget_nil _ _ _ ?_; simp))

theorem b_checkBudget_nil (c : ObjRef) (hcK : c ∈ K) : BK [] [] K (· = c) (checkBudget (Z := Unit)) :=
  fun σ hσ y hy => (b_checkBudget c hcK (fun h => by simp at h) hσ hy).2
macro_rules | `(tactic| b_leaf) => `(tactic| (with_reducible refine b_checkBudget_nil _ ?_; simp))

theorem b_preemptionPath (ct : ObjRef) : BK [] [] [ct] (· = ct) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; b_autoE

theorem b_handleYield (ct : ObjRef) : BK [] [] [ct] (· = ct) (handleYield (Z := Unit)) := by
  unfold handleYield; b_autoE

/-! ## `perform_invocation` -/

set_option maxHeartbeats 4000000 in
theorem b_fl4PerformInvocation (ct : ObjRef) (bl call don : Bool) (i : Fl4Invocation) :
    HKE (fun σ => B [ct] [ct] [ct] (· = ct) σ ∧ NoRpl [ct] σ) (B [ct] [ct] [ct] (· = ct))
      (fl4PerformInvocation (Z := Unit) bl call don i) := by
  cases i
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    refine hk_liftE ?_
    intro σ hσ0 y ⟨y1, h1, hy⟩
    have hσ := hσ0.1
    rw [mem_gets h1] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hc : σ.curThread = ct := hσ.1.2
    have hE : B [ct] [ct, ct] [ct] (· = ct) σ :=
      b_addE hσ fun x hx => (hσ.1.1 ct _ hx).2.2 (List.mem_singleton_self _)
    have h2' : y2 ∈ (sendIpc (Z := Unit) bl call bd g gr don ct ep σ).1 := by rw [← hc]; exact h2
    have hb2 := b_sendIpc bl call bd g gr don ct ep (List.mem_singleton_self _)
      (Or.inr (List.mem_singleton_self _)) σ hE y2 h2'
    rw [Set.mem_singleton_iff.1 hy]; exact hb2
  case invokeReply r g =>
    simp only [fl4PerformInvocation]
    refine hk_liftE ?_
    intro σ hσ y ⟨y1, h1, hy⟩
    rw [mem_gets h1] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := b_doReplyTransfer _ r g σ hσ y2 h2
    rw [Set.mem_singleton_iff.1 hy]; exact hb2
  case invokeTCB i =>
    simp only [fl4PerformInvocation]
    exact hk_pre (hk_of_ik (b_invokeTcb i)) fun _ h => h.1
  case invokeCNode i =>
    simp only [fl4PerformInvocation]
    exact hk_pre (hk_of_ik (ike_bind (b_invokeCnode i) fun _ => ike_returnOk _)) fun _ h => h.1
  case invokeIRQHandler i =>
    simp only [fl4PerformInvocation]
    exact hk_pre (hk_of_ik (ike_bind (ike_liftE (b_invokeIrqHandler i)) fun _ => ike_returnOk _)) fun _ h => h.1
  case invokeNotification ep bd =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact hk_pre (hk_of_ik (ike_bind (ike_liftE (b_sendSignal ep bd)) fun _ => ike_returnOk _)) fun _ h => h.1
  all_goals
    simp only [fl4PerformInvocation]
    exact hk_pre (hk_of_ik (b_of_gfE fun _ _ => by fg_auto)) fun _ h => h.1

end

end Fl4Proofs.P3.SInv
