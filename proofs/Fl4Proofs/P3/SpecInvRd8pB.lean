/-
P3 (DESIGN.md §9), invariant line G1 (rd8p, KENTRY-PLAN rd8m handoff 2):
**rd8j's `PreR` from carried facts** (spec side only, outside the JAtZ cone).

* `err_liftE_bind` / `err_wp_bind` / `err_bind_ne`, **`err_syscall`**: an
  error outcome of `fl4_handle_syscall` is an error outcome of the shell
  `fl4HandleInvocationR` after `get_cap_reg`, with the send flags (`sendArgs`)
  or the send-receive flags (`srArgs`, first phase). The receive tail of the
  send-receive syscalls and every other syscall are `withoutPreemption`, so
  they never error (ctq16's `NE`).
* **`ev_of_body`**: an outcome of the syscall body after a `true` front is an
  outcome of the event `fl4HandleEvent rep (.syscallEvent c)`. Event-level
  error facts therefore apply at the body's error outcomes.
* `ErrE rep c σ P`: `P` at every error (preemption) outcome of the event.
* **`preR_of`**: `PreR rep c σ` from
  - `Rdy` at the error outcome: rd8j's `rd_shellAt` with `InvIn` (the same
    pinned inputs as `rdBody_send` / rd8m's `rdBody_sr`);
  - `ScInv`: sb2's `sb_fl4HandleEvent` (every outcome);
  - `CKN`: ctq16's `ckx_fl4HandleEvent` (from `CtExit ∧ CurScT`, inside `EF`);
  - `EB true ∧ NQ []` at the event's error outcomes (`hEN`): proved by ctq18's
    `eb_fl4HandleEvent_err` (its first two conjuncts) from ctq's event-start
    bundle;
  - `CurHold` at the event's error outcomes (`hH`): rd8p's narrowed carried
    fact (SpecInvRd8pA), the one input left open;
  then rd8p's `rd_preemptionPath`.
-/
import Fl4Proofs.P3.SpecInvRd8pA
import Fl4Proofs.P3.SpecInvRd8jC
import Fl4Proofs.P3.CnodeRevoke
import Fl4Proofs.P3.IrqIssue
open Classical

namespace Fl4Proofs.P3.SInvR.B8p
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The error outcomes of the syscall -/

theorem err_liftE_bind {ε α β : Type} {m : NonDet (State Unit) α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} {z : Except ε β × State Unit} (h : z ∈ ((NonDetE.liftE m >>= f).run s).1) :
    ∃ g ∈ (m s).1, z ∈ ((f g.1).run g.2).1 := by
  obtain ⟨u, hu, ⟨a, ha, h⟩ | ⟨e', he', -⟩⟩ := ft_mem_bindE h
  · obtain ⟨g, hg, rfl⟩ := ft_mem_liftE hu
    simp only [Except.ok.injEq] at ha
    subst ha
    exact ⟨g, hg, h⟩
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hu
    cases he'

theorem err_wp_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → PMonad Unit β}
    {s : State Unit} {z : Except Unit β × State Unit} (h : z ∈ ((withoutPreemption (Z := Unit) m >>= f).run s).1) :
    ∃ g ∈ (m s).1, z ∈ ((f g.1).run g.2).1 := by
  unfold withoutPreemption at h
  exact err_liftE_bind h

theorem err_bind_ne {ε α : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε α}
    {s : State Unit} {z : Except ε α × State Unit} (h : z ∈ ((m >>= f).run s).1) {e : ε} (he : z.1 = .error e)
    (hf : ∀ a, R16.NE (f a)) : z ∈ (m.run s).1 := by
  obtain ⟨u, hu, ⟨a, -, h⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE h
  · exact absurd he (hf a u.2 z h e)
  · obtain ⟨u1, u2⟩ := u
    simp only at he'
    subst he'
    exact hu

/-- **An error outcome of the syscall is one of the shell after `get_cap_reg`.** -/
theorem err_syscall {rep : Bool} {c : Syscall} {s : State Unit} {z : Except Unit Unit × State Unit}
    (hz : z ∈ ((fl4HandleSyscall (Z := Unit) rep c).run s).1) {e : Unit} (he : z.1 = .error e) :
    ∃ r cl bl dn fp, ((A12b.sendArgs c = some (r, cl, bl, dn) ∧ fp = false) ∨
        (∃ cr, A12b.srArgs c = some (r, cr) ∧ cl = false ∧ bl = false ∧ dn = true ∧ fp = true)) ∧
      ∃ g ∈ (getCapReg (Z := Unit) r s).1,
        z ∈ ((fl4HandleInvocationR (Z := Unit) rep cl bl dn fp g.1).run g.2).1 := by
  cases c <;> simp only [fl4HandleSyscall] at hz <;> first
    | (obtain ⟨g, hg, h⟩ := err_liftE_bind hz
       exact ⟨_, _, _, _, _, Or.inl ⟨rfl, rfl⟩, g, hg, h⟩)
    | (obtain ⟨g, hg, h⟩ := err_wp_bind hz
       exact ⟨_, _, _, _, _, Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl⟩, g, hg,
         err_bind_ne h he fun _ => R16.ne_withoutPreemption _⟩)
    | exact absurd he (R16.ne_withoutPreemption _ s z hz e)

/-- **The body after a `true` front is part of the event.** -/
theorem ev_of_body {rep : Bool} {c : Syscall} {σ : State Unit} {v : Bool × State Unit}
    (hv : v ∈ (A8.front σ).1) (ht : v.1 = true) {z : Except Unit Unit × State Unit}
    (hz : z ∈ ((fl4HandleSyscall (Z := Unit) rep c).run v.2).1) :
    z ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1 := by
  obtain ⟨w, hw, hv'⟩ := hv
  simp only [fl4HandleEvent]
  refine Fl4Proofs.P3.mem_bindE_ok (Fl4Proofs.P3.mem_liftE hw) ?_
  refine Fl4Proofs.P3.mem_bindE_ok (Fl4Proofs.P3.mem_liftE hv') ?_
  show z ∈ ((NonDetE.whenE v.1 (fl4HandleSyscall (Z := Unit) rep c)).run v.2).1
  rw [ht]
  unfold NonDetE.whenE
  first | exact hz | (rw [if_pos rfl]; exact hz) | simpa using hz

/-! ## `PreR` -/

/-- `P` at every error (preemption) outcome of the syscall event. -/
def ErrE (rep : Bool) (c : Syscall) (σ : State Unit) (P : State Unit → Prop) : Prop :=
  ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1, ∀ e, y.1 = .error e → P y.2

/-- **rd8j's `PreR` from carried facts** (module docstring). -/
theorem preR_of (rep : Bool) (c : Syscall) (σ : State Unit) (hEF : A8.EF σ) (h1 : SInvQ.T1 σ)
    (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) (hE : SInvB.EntryOK σ)
    (hPs : ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hEN : ErrE rep c σ fun s => SInvQ.EB true s ∧ NQ [] s) (hH : ErrE rep c σ CurHold) :
    B8j.PreR rep c σ := by
  intro v hv ht z hz e he y hy
  have hzE := ev_of_body hv ht hz
  obtain ⟨hRB, hRT, hO, hS, hF⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  obtain ⟨r, cl, bl, dn, fp, hcase, g, hg, hzg⟩ := err_syscall hz he
  have hP : B8j.InvIn r fp σ := by
    rcases hcase with ⟨hs, rfl⟩ | ⟨cr, hs, -, -, -, rfl⟩
    · exact hPs r cl bl dn hs
    · exact hPr r cr hs
  have hR : Rdy z.2 := B8j.rd_shellAt hRB hRT hO hS hF rep cl bl dn fp r hg (hP v hv ht g hg) z hzg
  have hSc : SInvB.ScInv z.2 := SInvB.sb_fl4HandleEvent SInvB.scGap rep _ σ hE z hzE
  have hK : R14.CKN z.2 :=
    R16.ckx_fl4HandleEvent σ.curThread rep _ σ ⟨R16.ckn_of_exit hEF.ct hEF.cs, rfl⟩ z hzE e he
  obtain ⟨hEBz, hNz⟩ := hEN z hzE e he
  exact (rd_preemptionPath hR hNz hSc hK hEBz (hH z hzE e he) y hy).1

end

end Fl4Proofs.P3.SInvR.B8p
