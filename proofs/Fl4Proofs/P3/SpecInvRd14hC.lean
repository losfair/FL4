/-
P3 (DESIGN.md §9), invariant line G1 (rd14h, rd14g handoff, closing step):
**`PerfF` for every invocation and the readiness tops with no per-arm input**
(spec side only).

* `CF14h := CF14g3 ∨ CovCfg ∨ CovDR ∨ CovTC`, **`armFW_cf14h`** (rd14g F's
  `armFV_cf14g3`, SpecInvRd14hB's configure arm, SpecInvRd14hA's deletion arms),
  **`cf_all`** (every `Fl4Invocation` is in `CF14h`, by cases),
  **`armFW_all : ArmFW (fun _ => True)`**.
* Tops **`kcall_rdyOff9`** / **`kentry_rdyOff9`**: rd8w's `kcall_rdyOffW` /
  `kentry_rdyOffW` with rd14g B's `brR_ku armAKU_all` (no `PerfA` input) and
  `brF_kw armFW_all` (no `PerfF` input): from `SInvW` at the entry alone (and
  `numDomains = 1`, as every rd8w top), every outcome of the kernel call /
  syscall entry has `SInvW`. No `QR` / `QF` / `InvFc` / `InvRc` input.
-/
import Fl4Proofs.P3.SpecInvRd14hB
open Classical

namespace Fl4Proofs.P3.SInvR.A14h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f Fl4Proofs.P3.SInvR.A14g

noncomputable section

set_option maxHeartbeats 1000000

def CF14h (b : Fl4Invocation) : Prop := CF14g3 b ∨ A14d.CovCfg b ∨ CovDR b ∨ CovTC b

theorem armFW_cf14h : ArmFW CF14h :=
  (armFW_of armFV_cf14g3).or (armFW_cfg.or ((armFW_of armFV_covDR).or (armFW_of armFV_covTC)))

/-- One invocation in one of `CF14h`'s ten parts. -/
macro "cf_close" : tactic => `(tactic| first
  | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl True.intro))))
  | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl True.intro)))))
  | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr True.intro)))))
  | exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl True.intro))))
  | exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr True.intro))))
  | exact Or.inl (Or.inl (Or.inr (Or.inl True.intro)))
  | exact Or.inl (Or.inl (Or.inr (Or.inr True.intro)))
  | exact Or.inl (Or.inr True.intro)
  | exact Or.inr (Or.inl True.intro)
  | exact Or.inr (Or.inr (Or.inl True.intro))
  | exact Or.inr (Or.inr (Or.inr True.intro)))

/-- **Every invocation is covered.** -/
theorem cf_all (b : Fl4Invocation) : CF14h b := by
  cases b with
  | invokeTCB i => cases i <;> cf_close
  | invokeCNode i => cases i <;> cf_close
  | invokeIRQHandler i => cases i <;> cf_close
  | invokeArchObject i =>
    cases i with
    | spec j => cases j <;> cf_close
    | _ => cf_close
  | _ => cf_close

/-- **`ArmFW` for every invocation.** -/
theorem armFW_all : ArmFW (fun _ => True) :=
  fun σ0 s u h0 b I _ hB hS hi hN hz ho hr hRB hF hL hG hD hu =>
    armFW_cf14h σ0 s u h0 b I (cf_all b) hB hS hi hN hz ho hr hRB hF hL hG hD hu

/-! ## Tops -/

section Tops
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19
open Fl4Proofs.P3.SInvR.B8w

variable {σ : State Unit}

set_option maxHeartbeats 4000000 in
/-- **The readiness line closed**: `SInvW` at the entry gives `SInvW` at every outcome of the
kernel call, no per-arm input. -/
theorem kcall_rdyOff9 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffW hnd rep ev h hev (brR_ku armAKU_all) (brF_kw armFW_all)
    (fun c e => qu_ofW h hev c e (invRc_all c σ))
    (fun c e => ⟨qfu_ofW h hev c e (invFc_true c σ), nf_ofW h (hev (by rw [e]; intro h; cases h))⟩)

set_option maxHeartbeats 4000000 in
/-- **The syscall entry**, no per-arm input. -/
theorem kentry_rdyOff9 (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 := by
  refine kentry_rdyOffW hnd c h hct (brR_ku armAKU_all) (brF_kw armFW_all) fun w hw =>
    ⟨qu_fip c h hct w hw (invRc_all c w.2), qfu_fip c h hct w hw (invFc_true c w.2), ?_⟩
  have hc : cfS w.2 = cfS σ :=
    (by unfold fl4SyscallFaultIP; cfk_auto : CFK (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ w hw
  have ect : w.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc
  rw [ect]
  exact (nf_of_tv _ fun _ => by unfold fl4SyscallFaultIP; tv_auto) σ (nf_ofW h hct) w hw

end Tops

end

end Fl4Proofs.P3.SInvR.A14h
