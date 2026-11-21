theorem gk_syscall {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    (h1 : GKE mF) (h2 : ∀ f, GK (hF f)) (h3 : ∀ a, GKE (mE a)) (h4 : ∀ e, GK (hE e))
    (h5 : ∀ b, GKE (mFin b)) : GKE (syscall (Z := Unit) mF hF mE hE mFin) := by
  unfold syscall
  refine gke_bind (gke_withoutPreemption h1) fun r => ?_
  cases r with
  | error f => exact gke_withoutPreemption (h2 f)
  | ok a =>
    refine gke_bind (gke_withoutPreemption (h3 a)) fun r => ?_
    cases r with
    | error e => exact gke_withoutPreemption (h4 e)
    | ok b => exact h5 b
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_syscall ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))
