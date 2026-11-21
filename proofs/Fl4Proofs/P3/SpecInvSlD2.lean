/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive across deletion, the
final-cap facts** (sl2 handoff 2; spec side only).

* `tunb_finThread`: a final thread cap's `finalise_cap` leaves its thread
  unbound (`TUnb`): `unbind_from_sc` reads the thread's SC, which is bound back
  to it (sb1's `ScBackS`), so `sched_context_unbind_tcb` clears the thread's
  binding; `suspend` / `prepare_thread_delete` keep it (sb1's frame `BR`).
* `scd_finSc`: a final SC cap's `finalise_cap` leaves the SC with no TCB (unless
  it is the idle SC: `sched_context_unbind_all_tcbs` skips it), no notification
  and an empty reply stack (`ScB` with `QD`), kept by `_yield_from` /
  `set_inactive` (the frame family `ScB`: SC `p`'s binding fields).
* `other_scCap`: a non-final SC cap has another SC cap to its SC (`ScKind`).
-/
import Fl4Proofs.P3.SpecInvSlD
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem ik_true {α : Type} {m : NonDet (State Unit) α} : IK (fun _ => True) m := fun _ _ _ _ => trivial

/-! ## A final thread cap -/

/-- The thread `t` is a TCB bound to no SC. -/
def TUnb (t : ObjRef) (σ : State Unit) : Prop := ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = none

theorem tunb_br {t : ObjRef} {σ σ' : State Unit} (h : TUnb t σ) (hb : SInvB.BR σ.kheap σ'.kheap) : TUnb t σ' := by
  obtain ⟨x, hx, e⟩ := h
  obtain ⟨x', hx', e'⟩ := hb.tcb t x hx
  exact ⟨x', hx', e'.trans e⟩

theorem ik_tunb {α : Type} {m : NonDet (State Unit) α} (h : ∀ h0, SInvB.SBK h0 m) (t : ObjRef) : IK (TUnb t) m :=
  fun _ hσ _ hx => tunb_br hσ (SInvB.br_mem_of_sbk h hx)

theorem tunb_dead {t : ObjRef} {σ : State Unit} (h : TUnb t σ) : ∀ o, σ.kheap t = some o → ¬ liveO o := by
  obtain ⟨x, hx, e⟩ := h
  intro o ho hl
  rw [hx] at ho; cases ho
  exact hl e

theorem tunb_updSc {t : ObjRef} (c : ObjRef) (f : SchedContext → SchedContext) :
    IK (TUnb t) (updateSchedContext (Z := Unit) c f) := by
  intro σ h x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  obtain ⟨xt, hxt, ht⟩ := h
  have hne : t ≠ c := fun e' => by subst e'; rw [hxt] at hk; cases hk
  rw [e]
  exact ⟨xt, by show Function.update _ c _ t = _; rw [Function.update_of_ne hne]; exact hxt, ht⟩

theorem tunb_setTcbSc (t : ObjRef) : HK (fun _ => True) (TUnb t)
    (setTcbObjRef (Z := Unit) tcbSchedContextUpdate t none) := by
  intro σ _ x hx
  obtain ⟨xt, -, e⟩ := SInvB.mem_threadSet hx
  rw [e]
  exact ⟨_, by show Function.update _ t _ t = _; rw [Function.update_self], rfl⟩

/-- `sched_context_unbind_tcb c` where `c`'s TCB is `t`. -/
theorem tunb_unbindTcb (t c : ObjRef) (σ : State Unit) (hB : SInvB.ScBackS σ) (xt : Tcb)
    (hxt : σ.kheap t = some (.tcb xt)) (ha : xt.tcbSchedContext = some c) :
    ∀ y ∈ (schedContextUnbindTcb (Z := Unit) c σ).1, TUnb t y.2 := by
  obtain ⟨yc, k, hyc, hyt, -⟩ := hB t xt c hxt ha
  unfold schedContextUnbindTcb
  intro y ⟨z1, hz1, hy⟩
  obtain ⟨e1, n1, hk1⟩ := SInvB.mem_getSchedContext' hz1
  obtain ⟨sc, s1⟩ := z1
  simp only at e1 hk1; subst s1
  rw [hyc] at hk1; cases hk1
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨e2, e2'⟩ := SInvB.mem_assertOpt' hz2
  obtain ⟨tp, s2⟩ := z2
  simp only at e2 e2'; subst s2
  have etp : tp = t := Option.some.inj (e2.symm.trans hyt)
  subst tp
  refine (?_ : HK (fun _ => True) (TUnb t) _) σ trivial y hy
  dsimp only
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_bind (tunb_setTcbSc t) fun _ => ?_
  exact shk_ik (tunb_updSc _ _) fun _ h => h

theorem tunb_unbindFromSc (t : ObjRef) : HK SInvB.ScInv (TUnb t) (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc
  intro σ hI x ⟨y1, hy1, hx⟩
  obtain ⟨e1, xt, hxt, ha⟩ := SInvB.mem_getTcbSc hy1
  obtain ⟨a, s1⟩ := y1
  simp only at e1 ha; subst s1
  cases a with
  | none =>
    obtain ⟨y2, hy2, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hy2] at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨xt, hxt, ha⟩
  | some c =>
    obtain ⟨y2, hy2, hx⟩ := hx
    have h2 : TUnb t y2.2 := tunb_unbindTcb t c σ hI.back xt hxt ha y2 hy2
    exact ik_tunb (fun _ => by sb_auto) t y2.2 h2 x hx

/-- **A final thread cap's `finalise_cap` leaves its thread unbound.** -/
theorem tunb_finThread (t : ObjRef) :
    HK SInvB.ScInv (TUnb t) (finaliseCap (Z := Unit) (.threadCap t) true) := by
  simp only [finaliseCap, NonDet.when, ↓reduceIte]
  refine shk_ikbind (SInvB.sik_of_sbk fun _ => SInvB.sb_unbindNotification _) fun _ => ?_
  refine shk_bind (tunb_unbindFromSc t) fun _ => ?_
  refine shk_ikbind (ik_tunb (fun _ => SInvB.sb_suspend _) t) fun _ => ?_
  refine shk_ikbind (ik_tunb (fun _ => SInvB.sb_prepareThreadDelete _) t) fun _ => ?_
  exact shk_pure _ fun _ h => h

/-! ## The binding fields of one SC: the frame `ScB` -/

/-- SC `p` with binding fields satisfying `P`. -/
def ScB (p : ObjRef) (P : Option ObjRef → Option ObjRef → List ObjRef → Prop) (σ : State Unit) : Prop :=
  ∃ y n, σ.kheap p = some (.schedContext y n) ∧ P y.scTcb y.scNtfn y.scReplies

section B
variable {p : ObjRef} {P : Option ObjRef → Option ObjRef → List ObjRef → Prop}

theorem scb_setObject_nsc (q : ObjRef) (o : KernelObject) (σ : State Unit)
    (hq : ∀ o0, σ.kheap q = some o0 → ∀ y n, o0 ≠ .schedContext y n) :
    IKp (ScB p P) σ (setObject (Z := Unit) q o) := by
  intro h x hx
  obtain ⟨old, hk, -, e⟩ := SInvB.mem_setObject hx
  rw [e]
  obtain ⟨y, n, hy, hP⟩ := h
  have hne : p ≠ q := fun e' => by subst e'; exact hq old hk y n (Option.some.inj (hk.symm.trans hy))
  exact ⟨y, n, by show Function.update _ q _ p = _; rw [Function.update_of_ne hne]; exact hy, hP⟩

theorem scb_threadSet (f : Tcb → Tcb) (t : ObjRef) : IK (ScB p P) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => scb_setObject_nsc _ _ σ fun o0 hk y n e => ?_
  rw [getTcb_kheap hx] at hk; cases hk; cases e

theorem scb_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IK (ScB p P) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => scb_setObject_nsc _ _ σ fun o0 hk y n e => ?_
  rw [getTcb_kheap hx] at hk; cases hk; cases e

theorem scb_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK (ScB p P) (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (scb_setObject_nsc _ _ σ fun o0 hk y n e => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hk; cases hk; cases e

theorem scb_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) :
    IK (ScB p P) (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (scb_setObject_nsc _ _ σ fun o0 hk y n e => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hk; cases hk; cases e
  · repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem scb_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (q : ObjRef) (e : α) :
    IK (ScB p P) (setSimpleKo (Z := Unit) f q e) := by
  unfold setSimpleKo
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  refine scb_setObject_nsc q (f e) σ (fun o0 hk' y n e' => ?_) hσ x hx
  rw [hk] at hk'; cases hk'
  exact (SInvB.simple_not hsimp).2 y n e'

theorem scb_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, P y.scTcb y.scNtfn y.scReplies → P (f y).scTcb (f y).scNtfn (f y).scReplies) :
    IK (ScB p P) (updateSchedContext (Z := Unit) q f) := by
  intro σ h x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  obtain ⟨y0, n0, hy0, hP⟩ := h
  by_cases eq : p = q
  · subst eq
    rw [hk] at hy0; cases hy0
    exact ⟨f y, n, by show Function.update _ p _ p = _; rw [Function.update_self], hf y hP⟩
  · exact ⟨y0, n0, by show Function.update _ q _ p = _; rw [Function.update_of_ne eq]; exact hy0, hP⟩

/-- An update of SC `p` establishing `Q` from `P`. -/
theorem scb_updTrans {Q : Option ObjRef → Option ObjRef → List ObjRef → Prop} (f : SchedContext → SchedContext)
    (hf : ∀ y, P y.scTcb y.scNtfn y.scReplies → Q (f y).scTcb (f y).scNtfn (f y).scReplies) :
    HK (ScB p P) (ScB p Q) (updateSchedContext (Z := Unit) p f) := by
  intro σ h x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  obtain ⟨y0, n0, hy0, hP⟩ := h
  rw [hk] at hy0; cases hy0
  exact ⟨f y, n, by show Function.update _ p _ p = _; rw [Function.update_self], hf y hP⟩

end B

syntax "scb_leaf" : tactic
macro_rules | `(tactic| scb_leaf) => `(tactic| fail "no scb_leaf")
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact ik_doMachineOp (fun _ _ h => h) _)
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact scb_threadSet _ _)
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact scb_archThreadSet _ _)
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact scb_asUser _ _)
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact scb_setMrs _ _ _)
macro_rules | `(tactic| scb_leaf) => `(tactic| with_reducible exact scb_setSimpleKo _ _ _)
macro_rules | `(tactic| scb_leaf) => `(tactic| ((with_reducible refine scb_updateSchedContext _ _ ?_); intro _ h; exact h))

macro "scb_auto" : tactic => `(tactic| repeat' (first | scb_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## A final SC cap -/

section S
variable (I2 p : ObjRef)

/-- No TCB unless idle. -/
def QA (t : Option ObjRef) (_ : Option ObjRef) (_ : List ObjRef) : Prop := t = none ∨ p = I2
/-- … and no notification. -/
def QAB (t n : Option ObjRef) (_ : List ObjRef) : Prop := (t = none ∨ p = I2) ∧ n = none
/-- … and no replies: not live, or idle. -/
def QD (t n : Option ObjRef) (r : List ObjRef) : Prop := (t = none ∨ p = I2) ∧ n = none ∧ r = []

theorem scb_unbindTcb_none (σ : State Unit) :
    ∀ x ∈ (schedContextUnbindTcb (Z := Unit) p σ).1, ScB p (QA I2 p) x.2 := by
  intro x hx
  unfold schedContextUnbindTcb at hx
  refine (?_ : HK (fun _ => True) (ScB p (QA I2 p)) _) σ trivial x hx
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  refine shk_ikbind ik_true fun _ => ?_
  intro s _ y hy
  obtain ⟨y0, n, hk, e⟩ := SInvB.mem_updateSchedContext hy
  rw [e]
  exact ⟨_, n, by show Function.update _ p _ p = _; rw [Function.update_self], Or.inl rfl⟩

theorem scd1_unbindAllTcbs :
    HK (fun s => s.idleSc = I2) (ScB p (QA I2 p)) (schedContextUnbindAllTcbs (Z := Unit) p) := by
  unfold schedContextUnbindAllTcbs
  intro σ hI x ⟨y1, hy1, hx⟩
  obtain ⟨e1, n1, hk1⟩ := SInvB.mem_getSchedContext' hy1
  obtain ⟨sc, s1⟩ := y1
  simp only at e1 hk1; subst s1
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · exact scb_unbindTcb_none I2 p σ x hx
  · rename_i hc
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨sc, n1, hk1, ?_⟩
    by_cases h0 : sc.scTcb = none
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [← hI]
      by_contra hne
      exact hc ⟨h0, hne⟩

theorem scd2_unbindNtfn : HK (ScB p (QA I2 p)) (ScB p (QAB I2 p)) (schedContextUnbindNtfn (Z := Unit) p) := by
  unfold schedContextUnbindNtfn
  intro σ h x ⟨y1, hy1, hx⟩
  unfold getScObjRef at hy1
  obtain ⟨z, hz, hy1⟩ := hy1
  obtain ⟨ez, nz, hkz⟩ := SInvB.mem_getSchedContext' hz
  rw [Set.mem_singleton_iff.1 hy1] at hx
  rw [ez] at hx
  dsimp only at hx
  cases hn : z.1.scNtfn with
  | none =>
    rw [hn] at hx
    rw [Set.mem_singleton_iff.1 hx]
    obtain ⟨y0, n0, hy0, hQ⟩ := h
    rw [hkz] at hy0; cases hy0
    exact ⟨_, _, hkz, hQ, hn⟩
  | some nt =>
    rw [hn] at hx
    refine (?_ : HK (ScB p (QA I2 p)) (ScB p (QAB I2 p)) (doUnbindNtfnSc (Z := Unit) nt p)) σ h x hx
    refine shk_ikbind (by scb_auto) fun _ => ?_
    exact scb_updTrans _ fun y hP => ⟨hP, rfl⟩

theorem scd3_unbindReply : HK (ScB p (QAB I2 p)) (ScB p (QD I2 p)) (schedContextUnbindReply (Z := Unit) p) := by
  unfold schedContextUnbindReply
  intro σ h x ⟨y1, hy1, hx⟩
  obtain ⟨z, hz, hy1⟩ := hy1
  obtain ⟨ez, nz, hkz⟩ := SInvB.mem_getSchedContext' hz
  rw [Set.mem_singleton_iff.1 hy1] at hx
  rw [ez] at hx
  dsimp only at hx
  unfold NonDet.unless at hx
  split at hx
  · rename_i he
    rw [Set.mem_singleton_iff.1 hx]
    obtain ⟨y0, n0, hy0, hQ⟩ := h
    rw [hkz] at hy0; cases hy0
    exact ⟨_, _, hkz, hQ.1, hQ.2, he⟩
  · refine (?_ : HK (ScB p (QAB I2 p)) (ScB p (QD I2 p)) _) σ h x hx
    refine shk_ikbind (by scb_auto) fun _ => ?_
    exact scb_updTrans _ fun y hP => ⟨hP.1, hP.2, rfl⟩

/-- **A final SC cap's `finalise_cap` leaves the SC not live, or idle.** -/
theorem scd_finSc (b : Nat) :
    HK (fun s => s.idleSc = I2) (ScB p (QD I2 p)) (finaliseCap (Z := Unit) (.schedContextCap p b) true) := by
  simp only [finaliseCap, NonDet.when, ↓reduceIte]
  refine shk_bind (scd1_unbindAllTcbs I2 p) fun _ => ?_
  refine shk_bind (scd2_unbindNtfn I2 p) fun _ => ?_
  refine shk_bind (scd3_unbindReply I2 p) fun _ => ?_
  refine shk_ikbind (by unfold schedContextUnbindYieldFrom; scb_auto) fun _ => ?_
  refine shk_ikbind (by unfold schedContextSetInactive; scb_auto) fun _ => ?_
  exact shk_pure _ fun _ h => h

theorem scd_dead (I1 : ObjRef) {σ : State Unit} (h : ScB p (QD I2 p) σ) :
    ∀ o, σ.kheap p = some o → liveO o → p = I1 ∨ p = I2 := by
  obtain ⟨y, n, hy, ht, hn, hr⟩ := h
  intro o ho hl
  rw [hy] at ho; cases ho
  rcases hl with hl | hl | hl
  · rcases ht with ht | ht
    · exact absurd ht hl
    · exact Or.inr ht
  · exact absurd hn hl
  · exact absurd hr hl

end S

/-! ## A non-final SC cap -/

theorem nonfinal_other' {σ : State Unit} {c : Cap} {sl : CslotPtr} (hnf : ¬ isFinalCap' (Z := Unit) c σ)
    (hs : SInvU.capAt σ sl = some c) {r : ObjRef} (hg : genObjRefs c = {GenObjRef.objRef r}) :
    ∃ s' c', s' ≠ sl ∧ SInvU.capAt σ s' = some c' ∧ r ∈ objRefs c' := by
  by_contra hno
  apply hnf
  refine ⟨sl, Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨c', hc', hov⟩ := hx
    have hcx : SInvU.capAt σ x = some c' :=
      (SInvU.getCap_capAt (x := (c', σ)) (by rw [hc']; exact Set.mem_singleton _)).2
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hov
    rw [hg]
    ext g
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl hg'
    exact hno ⟨x, c', hne, hcx, SInvU.objRef_mem_gen hg'⟩
  · rw [Set.mem_singleton_iff.1 hx]
    refine ⟨c, (SInvU.getCap_set_capAt σ sl c).2 hs, ?_⟩
    intro e
    have : GenObjRef.objRef r ∈ genObjRefs c ∩ genObjRefs c := by rw [hg]; exact ⟨rfl, rfl⟩
    rw [e] at this; exact this

/-- **A non-final SC cap has another SC cap to its SC** (`ScKind`). -/
theorem other_scCap {σ : State Unit} (hK : ScKind σ) {s : CslotPtr} {p : ObjRef} {b : Nat}
    (hs : SInvU.capAt σ s = some (.schedContextCap p b)) (hnf : ¬ isFinalCap' (Z := Unit) (.schedContextCap p b) σ) :
    ∃ s' b', s' ≠ s ∧ SInvU.capAt σ s' = some (.schedContextCap p b') := by
  have hg : genObjRefs (.schedContextCap p b) = {GenObjRef.objRef p} := by
    simp [genObjRefs, objRefs, capIrqs, capIrqOpt, archCapSetMap]
  obtain ⟨s', c', hne, hc', hr⟩ := nonfinal_other' hnf hs hg
  obtain ⟨b', rfl⟩ := hK s p b s' c' hs hc' hr
  exact ⟨s', b', hne, hc'⟩

/-- A non-final SC cap's `finalise_cap` writes nothing. -/
theorem finSc_false_eq (p : ObjRef) (b : Nat) {σ : State Unit} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) (.schedContextCap p b) false σ).1) : y.2 = σ ∧ y.1.1 = .nullCap := by
  have h : IK (fun s => s = σ) (finaliseCap (Z := Unit) (.schedContextCap p b) false) := by
    simp only [finaliseCap, NonDet.when, Bool.false_eq_true, ↓reduceIte]
    repeat' ik_step0
  exact ⟨h σ rfl y hy, SInvU.finaliseCap_null (c := .schedContextCap p b) (by simp [SInvU.sRefs]) false σ y hy⟩

end

end Fl4Proofs.P3.SInvL
