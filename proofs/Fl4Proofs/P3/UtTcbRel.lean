/-
P3 (DESIGN.md §9), untyped: **a new TCB and `default_tcb`** (handoff/utj.md
"uttypes", ut37; l4v `retype_region` of `TCBObject`s, `default_tcb` with
`new_context`).

* `winZero_tcbF`: after a TCB retype (`WinZero` with the creation words
  `InT`), a new TCB's words in `[F, F + 272)` (state, IPC fields, fault,
  domain .. scheduler fields, links) are zero, but the domain word and the
  debug links;
* `tcbRel_default`: those words zero and `init_context`'s registers (`ctxW`)
  give `TcbRel` with `default_tcb d` (inactive, no fault, no bound
  notification, no SC, priority 0, `new_context`); `ctxW_newContext`. This
  needs Fl4Spec's documented deviation `selCS3` = 0x33, `selDS3` = 0x2b
  (FL4's Linux selector layout, Machine.lean).
-/
import Fl4Proofs.P3.UtTcbRetC
import Fl4Proofs.P3.UtTcbSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **A new TCB's fields after a TCB retype are zero**, but the domain word
and the debug links (`InT`'s exceptions in `[F, F + 272)`). -/
theorem winZero_tcbF {m : U64 → U64} {A win : Nat} {T : Prop} (hWZ : WinZero m A 4096 win T)
    (hfit : A + win * 4096 ≤ 2 ^ 64) {j : Nat} (hj : j < win) (w : U64) (hw : P1.Aligned w)
    (h1 : (bT A j).val + 3328 ≤ w.val) (h2 : w.val < (bT A j).val + 3600) (h3 : w.val ≠ (bT A j).val + 3432)
    (h4 : w.val ≠ (bT A j).val + 3576) (h5 : w.val ≠ (bT A j).val + 3584) : m w = 0#u64 := by
  have hb := bT_v hj hfit
  rw [hb] at h1 h2 h3 h4 h5
  have hjk : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
  rcases hWZ w hw (by omega) (by omega) with h | ⟨-, j', hj', hin⟩
  · exact h
  · exfalso
    have e : (⟨BitVec.ofNat 64 (A + j' * 4096)⟩ : U64).val = A + j' * 4096 := bT_v hj' hfit
    unfold InT at hin
    rw [e] at hin
    obtain ⟨g1, g2, g3, g4⟩ := hin
    rcases Nat.lt_trichotomy j' j with hl | rfl | hl
    · omega
    · omega
    · omega

/-- **A new TCB's VCPU word is zero** (KENTRY-PLAN g2b): creation writes
no VCPU word (`InT`). -/
theorem winZero_vcpu {m : U64 → U64} {A win : Nat} {T : Prop} (hWZ : WinZero m A 4096 win T)
    (hfit : A + win * 4096 ≤ 2 ^ 64) {j : Nat} (hj : j < win) (w : U64) (hw : P1.Aligned w)
    (h1 : w.val = (bT A j).val + 3664) : m w = 0#u64 := by
  have hb := bT_v hj hfit
  rw [hb] at h1
  have hjk : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
  rcases hWZ w hw (by omega) (by omega) with h | ⟨-, j', hj', hin⟩
  · exact h
  · exfalso
    have e : (⟨BitVec.ofNat 64 (A + j' * 4096)⟩ : U64).val = A + j' * 4096 := bT_v hj' hfit
    unfold InT at hin
    rw [e] at hin
    obtain ⟨g1, g2, g3, g4⟩ := hin
    rcases Nat.lt_trichotomy j' j with hl | rfl | hl
    · have : (j' + 1) * 4096 ≤ j * 4096 := Nat.mul_le_mul_right _ hl
      omega
    · omega
    · have : (j + 1) * 4096 ≤ j' * 4096 := Nat.mul_le_mul_right _ hl
      omega

section Rel
open Fl4Spec

/-- **A zeroed TCB with `init_context`'s registers is `default_tcb`.** -/
theorem tcbRel_default {R : Set U64} {m : U64 → U64} {t : U64} (ht : TcbOk t) (d : Domain)
    (hreg : ∀ r : U64, r.val < 24 → m (regA t r) = ctxW r.val)
    (hz : ∀ w : U64, P1.Aligned w → t.val + 3328 ≤ w.val → w.val < t.val + 3472 → w.val ≠ t.val + 3432 →
      m w = 0#u64) :
    Ipc.TcbRel R m t (defaultTcb d) := by
  obtain ⟨g1, g2⟩ := ht
  have z : ∀ K : U64, 3328 ≤ K.val → K.val < 3472 → K.val ≠ 3432 → K.val % 8 = 0 →
      m (core.num.U64.wrapping_add t K) = 0#u64 := by
    intro K k1 k2 k3 k4
    have hv : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
      rw [core.num.U64.wrapping_add_val_eq]
      have : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    exact hz _ (by show _ % 8 = 0; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)
  have hst : m (tStA t) = 0#u64 := by
    unfold tStA; rw [show layout.tcb.STATE = 3328#u64 by unfold layout.tcb.STATE layout.tcb.F; rfl]
    exact z _ (by decide) (by decide) (by decide) (by decide)
  have hfl : m (tFaultA t) = 0#u64 := z _ (by decide) (by decide) (by decide) (by decide)
  have hbd : m (tBoundA t) = 0#u64 := z _ (by decide) (by decide) (by decide) (by decide)
  have hpr : m (prioA t) = 0#u64 := z _ (by decide) (by decide) (by decide) (by decide)
  have hsc : m (scA t) = 0#u64 := z _ (by decide) (by decide) (by decide) (by decide)
  refine ⟨by rw [hst]; rfl, fun e h => by simp [Fl4Spec.defaultTcb, Fl4Spec.epBlocked] at h,
    fun n h => by simp [Fl4Spec.defaultTcb] at h, fun e dd h => by simp [Fl4Spec.defaultTcb] at h,
    fun e r dd h => by simp [Fl4Spec.defaultTcb] at h, fun r h => by simp [Fl4Spec.defaultTcb] at h, fun r => ?_,
    by rw [hpr]; rfl,
    ⟨fun _ => rfl, fun _ => hfl⟩, ⟨fun h => by rw [hfl] at h; exact absurd h (by decide), fun ⟨b, h⟩ => by cases h⟩,
    by rw [hbd, optRef_zero]; rfl, hfl, by rw [hsc, optRef_zero]; rfl⟩
  rw [hreg _ (regIdx_lt r)]
  cases r <;> first | rfl |
    (simp only [Fl4Spec.defaultTcb, Fl4Spec.defaultArchTcb, Fl4Spec.newContext, ctxW, regIdx, Function.update,
      Fl4Spec.selCS3, Fl4Spec.selDS3]; decide)

/-- **`init_context`'s registers are `new_context`'s** (with Fl4Spec's
selectors in FL4's layout, Machine.lean `selCS3`/`selDS3`). -/
theorem ctxW_newContext (r : Register) : (ctxW (regIdx r).val).bv = newContext.userRegs r := by
  cases r <;> first | rfl |
    (simp only [Fl4Spec.newContext, ctxW, regIdx, Function.update, Fl4Spec.selCS3, Fl4Spec.selDS3]; decide)

end Rel

end

end Fl4Proofs.P3
