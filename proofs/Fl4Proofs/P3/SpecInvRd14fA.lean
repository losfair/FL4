/-
P3 (DESIGN.md §9), invariant line G1 (rd14e-3, lead decision on rd14e-2's
handoff): **the arm interface with cur_sc not the idle SC** (spec side only).

* **`ArmAKV C`**: rd14d's `ArmAKB` with `σ0.curSc ≠ σ0.idleSc` at the front
  state (the deletion arms ending in rd14d's widened `TW` need it);
  `armAKV_of` (`ArmAKB` gives it), `ArmAKV.or`.
* `front_ci` (a `true` front outcome keeps cur_sc and the idle SC),
  **`perfR_ofKV`**, **`invR_ofKV`**, and the bridge in rd8w's `BrR` shape
  **`brR_kv : ∀ c σ, A8.EF σ → (InvRc C c σ ∧ σ.curSc ≠ σ.idleSc) → InvR c σ`**
  (the fact is discharged at the tops from `hX10.vi`).
-/
import Fl4Proofs.P3.SpecInvRd14eC
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-- rd14d's `ArmAKB` with cur_sc not the idle SC. -/
def ArmAKV (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (bl cl dn : Bool) (b : Fl4Invocation), C b →
    A10.BS σ0 → Suff σ0 → σ0.curSc ≠ σ0.idleSc → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b →
    SInvB.BR h0 s.kheap → u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfA σ0 bl cl dn b u.2

theorem armAKV_of {C : Fl4Invocation → Prop} (h : ArmAKB C) : ArmAKV C :=
  fun σ0 s u h0 bl cl dn b hc hB hS _ hz ho hr hu => h σ0 s u h0 bl cl dn b hc hB hS hz ho hr hu

theorem ArmAKV.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmAKV C1) (h2 : ArmAKV C2) :
    ArmAKV (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 bl cl dn b hc hB hS hi hz ho hr hu =>
    hc.elim (fun c => h1 σ0 s u h0 bl cl dn b c hB hS hi hz ho hr hu)
      (fun c => h2 σ0 s u h0 bl cl dn b c hB hS hi hz ho hr hu)

/-- A `true` front outcome keeps cur_sc and the idle SC. -/
theorem front_ci {σ : State Unit} (h : A8.EF σ) {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1)
    (ht : v.1 = true) : v.2.curSc = σ.curSc ∧ v.2.idleSc = σ.idleSc := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨-, -, h3⟩ := rd_front h.rdy h.off h.vmt h.sc h.cs hct hst h.q h.si h.cb h.hb h.ca h.ni hv
  obtain ⟨y, hy, e, -⟩ := h3 ht
  obtain ⟨-, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨-, -, -, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  rw [e]; exact ⟨ec, ei⟩

/-- **`PerfRc` gives rd12b's `PerfR`** for any `C` with `ArmAKV C`. -/
theorem perfR_ofKV {C : Fl4Invocation → Prop} (hA : ArmAKV C) {σ0 σ : State Unit} (hB : A10.BS σ0)
    (hS : Suff σ0) (hi : σ0.curSc ≠ σ0.idleSc) (hz : KZ σ0 σ) {calling blocking don fp : Bool} {cptr : CapRef}
    (h : PerfRc C σ0 calling blocking don fp cptr σ) : PerfR σ0 calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    rw [et] at hu
    obtain ⟨h0, hok, hbr⟩ := bindOK_invE hb
    exact hA σ0 s' u h0 blocking calling don b hc hB hS hi hz2 hok hbr hu
  · exact hP

/-- **`InvRc` gives rd12b's `InvR`** for any `C` with `ArmAKV C`. -/
theorem invR_ofKV {C : Fl4Invocation → Prop} (hA : ArmAKV C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (hi : σ.curSc ≠ σ.idleSc) (h : InvRc C c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  obtain ⟨ec, ei⟩ := front_ci hEF hv ht
  have hi' : v.2.curSc ≠ v.2.idleSc := by rw [ec, ei]; exact hi
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_ofKV hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg =>
      perfR_ofKV hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) ((h v hv ht).2 r cr hc g hg)⟩

/-- **rd8w's `BrR (fun c σ => InvRc C c σ ∧ σ.curSc ≠ σ.idleSc)`** for any `ArmAKV C`. -/
theorem brR_kv {C : Fl4Invocation → Prop} (hA : ArmAKV C) :
    ∀ (c : Syscall) (σ : State Unit), A8.EF σ → (InvRc C c σ ∧ σ.curSc ≠ σ.idleSc) → InvR c σ :=
  fun _ _ hEF h => invR_ofKV hA hEF h.2 h.1

/-- rd14e's covered set as an `ArmAKV`. -/
theorem armAKV_c14e2 : ArmAKV A14e.C14e2 := armAKV_of A14e.armAKB_c14e2

end

end Fl4Proofs.P3.SInvR.A14f
