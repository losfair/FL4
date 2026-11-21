/-
P3 (DESIGN.md §9), invariant line G1 (vfh2): **the arch performs keep `VS`**
(spec side only, outside the JAtZ cone), from the decode's facts at the anchor.

* `VArch σ0 i`: the slots an arch invocation writes are no fault-handler slots
  of the anchor and the caps it writes are `CnOk` (they are arch caps): the
  page / page-table / page-directory / PDPT map and unmap invocations write the
  invoked cap's own slot `cte` (it holds an arch cap at the decode, so is no
  fault-handler slot: `vfh_notBad_old`), the IO port control issue and FL4's
  DeriveSubframe write target slots of a looked-up CNode (full); ASID control
  (MakePool) is a retype and is NOT covered here (`VArch` asks for nothing and
  `vs_fl4ArchPerform` excludes it); ASID pool assignment re-reads its slot
  (pinned, `vs_performAsidPoolInvocation`).
* `vs_performPageInvocation`, `vs_performPageTableInvocation`,
  `vs_performPageDirectoryInvocation`, `vs_performPdptInvocation`,
  `vs_performIoportControlInvocation`, `vs_performDeriveSubframe`,
  `vs_performAsidPoolInvocation`, `vs_fl4ArchPerform` (all but MakePool).
-/
import Fl4Proofs.P3.SpecInvVfhT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

theorem vfh_arch_ok {σ : State Unit} (a : ArchCap) : CnOk σ (.archObjectCap a) := cnOk_of_nc fun _ _ _ e => by cases e

theorem vfh_not_arch (a : ArchCap) : ¬ validFaultHandler (.archObjectCap a) := vfh_not (by simp) rfl

theorem vs_performPageInvocationUnmap {σ0 : State Unit} (cap : ArchCap) (sl : CslotPtr) (h1 : ¬ vfh_Bad σ0 sl) :
    IK (VS σ0) (performPageInvocationUnmap (Z := Unit) cap sl) := by
  cases cap with
  | pageCap d b r t sz m =>
    simp only [performPageInvocationUnmap]
    cases m <;> (dsimp only; repeat' (first | exact vs_setCap_nb h1 (vfh_arch_ok _) | hv_leaf | ik_step0 | ik_unfold))
  | _ => simp only [performPageInvocationUnmap]; exact ik_fail

theorem vs_performPageInvocation {σ0 : State Unit} (i : PageInvocation)
    (h : ∀ c sl e v, i = .pageMap c sl e v → ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c)
    (h' : ∀ c sl, i = .pageUnmap c sl → ¬ vfh_Bad σ0 sl) : IK (VS σ0) (performPageInvocation (Z := Unit) i) := by
  cases i with
  | pageMap c sl e v =>
    obtain ⟨h1, h2⟩ := h c sl e v rfl
    simp only [performPageInvocation]
    refine ik_bind (vs_setCap_nb h1 h2) fun _ => ?_
    hv_auto
  | pageUnmap c sl =>
    have h1 := h' c sl rfl
    cases c with
    | pageCap d b r t sz m =>
      simp only [performPageInvocation]
      cases m with
      | none => dsimp only; hv_auto
      | some am =>
        cases t <;> dsimp only <;> first
          | exact ik_bind (vs_performPageInvocationUnmap _ _ h1) fun _ => ik_pure _
          | exact ik_bind ik_fail fun _ => ik_pure _
          | hv_auto
    | _ => simp only [performPageInvocation]; exact ik_fail
  | pageGetAddr p => simp only [performPageInvocation]; hv_auto

theorem vs_performPageTableInvocation {σ0 : State Unit} (i : PageTableInvocation)
    (h : ∀ c sl p q v, i = .pageTableMap c sl p q v → ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c)
    (h' : ∀ c sl, i = .pageTableUnmap c sl → ¬ vfh_Bad σ0 sl) :
    IK (VS σ0) (performPageTableInvocation (Z := Unit) i) := by
  cases i with
  | pageTableMap c sl p q v =>
    obtain ⟨h1, h2⟩ := h c sl p q v rfl
    simp only [performPageTableInvocation]
    refine ik_bind (vs_setCap_nb h1 h2) fun _ => ?_
    hv_auto
  | pageTableUnmap c sl =>
    have h1 := h' c sl rfl
    cases c with
    | archObjectCap a =>
      cases a with
      | pageTableCap p m =>
        simp only [performPageTableInvocation]
        cases m <;> (dsimp only; repeat' (first | exact vs_setCap_nb h1 (vfh_arch_ok _) | hv_leaf | ik_step0 | ik_unfold))
      | _ => simp only [performPageTableInvocation]; exact ik_fail
    | _ => simp only [performPageTableInvocation]; exact ik_fail

theorem vs_performPageDirectoryInvocation {σ0 : State Unit} (i : PageDirectoryInvocation)
    (h : ∀ c sl p q v, i = .pageDirectoryMap c sl p q v → ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c)
    (h' : ∀ c sl, i = .pageDirectoryUnmap c sl → ¬ vfh_Bad σ0 sl) :
    IK (VS σ0) (performPageDirectoryInvocation (Z := Unit) i) := by
  cases i with
  | pageDirectoryMap c sl p q v =>
    obtain ⟨h1, h2⟩ := h c sl p q v rfl
    simp only [performPageDirectoryInvocation]
    refine ik_bind (vs_setCap_nb h1 h2) fun _ => ?_
    hv_auto
  | pageDirectoryUnmap c sl =>
    have h1 := h' c sl rfl
    cases c with
    | archObjectCap a =>
      cases a with
      | pageDirectoryCap p m =>
        simp only [performPageDirectoryInvocation]
        cases m <;> (dsimp only; repeat' (first | exact vs_setCap_nb h1 (vfh_arch_ok _) | hv_leaf | ik_step0 | ik_unfold))
      | _ => simp only [performPageDirectoryInvocation]; exact ik_fail
    | _ => simp only [performPageDirectoryInvocation]; exact ik_fail

theorem vs_performPdptInvocation {σ0 : State Unit} (i : PdptInvocation)
    (h : ∀ c sl p q v, i = .pdptMap c sl p q v → ¬ vfh_Bad σ0 sl ∧ CnOk σ0 c)
    (h' : ∀ c sl, i = .pdptUnmap c sl → ¬ vfh_Bad σ0 sl) :
    IK (VS σ0) (performPdptInvocation (Z := Unit) i) := by
  cases i with
  | pdptMap c sl p q v =>
    obtain ⟨h1, h2⟩ := h c sl p q v rfl
    simp only [performPdptInvocation]
    refine ik_bind (vs_setCap_nb h1 h2) fun _ => ?_
    hv_auto
  | pdptUnmap c sl =>
    have h1 := h' c sl rfl
    cases c with
    | archObjectCap a =>
      cases a with
      | pdPointerTableCap p m =>
        simp only [performPdptInvocation]
        cases m <;> (dsimp only; repeat' (first | exact vs_setCap_nb h1 (vfh_arch_ok _) | hv_leaf | ik_step0 | ik_unfold))
      | _ => simp only [performPdptInvocation]; exact ik_fail
    | _ => simp only [performPdptInvocation]; exact ik_fail

theorem vs_performIoportControlInvocation {σ0 : State Unit} (i : IoPortControlInvocation)
    (h : ∀ f l d c, i = .ioPortControlInvocation f l d c → ¬ vfh_Bad σ0 d) :
    IK (VS σ0) (performIoportControlInvocation (Z := Unit) i) := by
  cases i with
  | ioPortControlInvocation f l d c =>
    have h1 := h f l d c rfl
    simp only [performIoportControlInvocation]
    refine ik_bind (by hv_auto) fun _ => ik_pure_bind ?_
    exact vs_capInsert _ _ (fun hb => (h1 hb).elim) (vfh_arch_ok _)

theorem vfh_ik_mapMx_mem {P : State Unit → Prop} {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ xs : List α, (∀ a ∈ xs, IK P (g a)) → IK P (NonDet.mapMx g xs)
  | [], _ => ik_pure' _
  | a :: xs, h => ik_bind' (h a (by simp)) fun _ => vfh_ik_mapMx_mem xs fun b hb => h b (by simp [hb])

theorem vs_performDeriveSubframe {σ0 : State Unit} (iv : Fl4SubframeInvocation)
    (h : ∀ d ∈ iv.dests, ¬ vfh_Bad σ0 d) : IK (VS σ0) (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe
  refine vfh_ik_mapMx_mem _ fun d hd => vs_capInsert _ _ (fun hb => (h d.2 ?_ hb).elim) (vfh_arch_ok _)
  exact (List.of_mem_zip hd).2

/-- ASID pool assignment re-reads its slot and writes only over a PML4 cap. -/
theorem vs_performAsidPoolInvocation {σ0 : State Unit} (i : AsidPoolInvocation) :
    IK (VS σ0) (performAsidPoolInvocation (Z := Unit) i) := by
  cases i with
  | assign asid pool sl =>
    simp only [performAsidPoolInvocation]
    intro σ
    refine ikp_getCap_bind fun c hc => ?_
    split
    · intro hσ x hx
      refine vs_pin hσ (ik_bind (vs_setCap_nb (vfh_notBad_old hσ.1 hc (by
          first | exact vfh_not_arch _ | (subst_vars; exact vfh_not_arch _))) (vfh_arch_ok _))
        fun _ => by hv_auto) x hx
    · exact ikp_of_ik ik_fail σ

end

end Fl4Proofs.P3.SInv
