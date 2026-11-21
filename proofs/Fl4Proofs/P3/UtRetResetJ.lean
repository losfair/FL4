/-
P3 (DESIGN.md §9), untyped: **the retype with a reset at `J`** (handoff/utj.md
Round 13, item 3d): FL4's restart, then `untyped::retype` with `reset = true`
(`reset_untyped`, then the retype body from the reset's state), against the
spec's restart and `invoke_untyped` with a reset (`reset_untyped_cap`, then
the invocation without one from its outcome, `invoke_reset_ok`; a preempted
reset is the invocation's error outcome, `invoke_reset_err`).

* `retype_reset_wp`: FL4's `untyped::retype` with a reset is `reset_untyped`,
  then (on `Ok`) the retype without one.
* `khT`/`entF`, `reset_khT`, `ent_reset`: every outcome of the spec's reset of
  a used cap keeps every object's type but its region's (`delete_objects`), and
  the current thread, the idle thread and the scheduler action.
* `utRetPostJ_of_reset`/`utRetPostJ_of_preempt`: `UtRetPostJ` of the
  invocation with a reset from a body's `UtBodyPost` after the reset, or a
  preempted reset.
* `UtBodyHyp`: a retype body (UtEpRet's `JAtZ.utEpBodyJ` shape) for one
  invocation's arguments, from any `JAtZ` state.
* `JAtZ.utResetJ`: the composition at `J`: the restart (`JAtZ.restartJ`), the
  reset (`JAtZ.reset_untypedJ`; an unused cap, free index 0, resets nothing:
  `retype_reset_unused`), then the body at the reset's state, whose
  premises are re-established there: `Entered` (`ent_reset`), the arguments'
  `RetCtx` (the destination CNode off the region, `cnode_off_childless`; its
  slots and the node cap's slot kept, `ResetJPost`'s slot frame),
  `BufObjHyp`/`ArchFitHyp` (`reset_khT`, `SpecFree`), the kept references
  (the dropped heap has no object in the region).
  Premises: those of `JAtZ.reset_untypedJ` at the restart's state (`PPPlat`,
  `resetChunkBits = 16` [P]; `VsReachMiss` [J], here with no extra roots), the
  no-reset retype's (`BufObjHyp`, `ArchFitHyp`, `RegionUnrefJ` [J]), `hRd0`
  [J] (as the CNode decodes, for `PPR0`).
-/
import Fl4Proofs.P3.UtEpRet
import Fl4Proofs.P3.UtResetTopJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's retype with a reset** (`untyped::retype`, `reset = true`):
`reset_untyped`, then on `Ok` the retype without a reset from its state; an
error ends the retype with it. -/
theorem retype_reset_wp {A' : Type} (arI : machine.Arch A') (s : S) (a : A') (slot base nt us dest off win : U64)
    (dev : Bool) {P Q : core.result.Result Unit error.Exc × S × A' → Prop}
    (hr : untyped.reset_untyped st arI s a slot ⦃ P ⦄)
    (hok : ∀ s1 a1, P (.Ok (), s1, a1) → untyped.retype st arI s1 a1 slot false base nt us dest off win dev ⦃ Q ⦄)
    (herr : ∀ e s1 a1, P (.Err e, s1, a1) → Q (.Err e, s1, a1)) :
    untyped.retype st arI s a slot true base nt us dest off win dev ⦃ Q ⦄ := by
  unfold untyped.retype
  simp only [↓reduceIte]
  refine WP.spec_bind hr ?_
  rintro ⟨r, s1, a1⟩ hP
  cases r with
  | Ok u =>
    cases u
    have h := hok s1 a1 hP
    unfold untyped.retype at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
    exact h
  | Err e =>
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    simp only [bind_tc_ok, bind_ok]
    exact (WP.spec_ok _).2 (herr e s1 a1 hP)

end

/-! ## The spec's reset: what it keeps -/

section SpecKeep
open Fl4Spec Fl4Proofs.P3.Vs

/-- The heap's object types. -/
def khT (σ : State Unit) : ObjRef → Option AType := fun o => (σ.kheap o).map aType

/-- The current thread, the idle thread and the scheduler action. -/
def entF (σ : State Unit) : ObjRef × ObjRef × SchedulerAction := (σ.curThread, σ.idleThread, σ.schedulerAction)

theorem kt_dmo {α : Type} (mop : NonDet MachineState α) : FK khT (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem kt_deo (eop : DetExtMonad Unit) : FK khT (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

theorem kt_setObject (p : ObjRef) (o : KernelObject) : FK khT (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext o'
  unfold khT
  by_cases e : o' = p
  · subst e; simp only [Function.update_self, hk, Option.map_some]; exact congrArg some hty.symm
  · simp only [Function.update_of_ne e]

theorem kt_setCap (cap : Cap) (sl : CslotPtr) : FK khT (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat (first | exact kt_setObject _ _ | dk_step0)

theorem kt_pp : FKE khT (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact kt_dmo _
    | exact kt_deo _
    | dk_step0)

theorem ent_dmo {α : Type} (mop : NonDet MachineState α) : FK entF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem ent_deo (eop : DetExtMonad Unit) : FK entF (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

theorem ent_setObject (p : ObjRef) (o : KernelObject) : FK entF (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0

theorem ent_setCap (cap : Cap) (sl : CslotPtr) : FK entF (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat (first | exact ent_setObject _ _ | dk_step0)

theorem ent_getCap (sl : CslotPtr) : FK entF (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat dk_step0

theorem ent_pp : FKE entF (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact ent_dmo _
    | exact ent_deo _
    | dk_step0)

/-- **The reset keeps the current thread, the idle thread and the scheduler
action** (its outcomes, preempted or not). -/
theorem ent_reset (sl : CslotPtr) : FKE entF (resetUntypedCap (Z := Unit) sl) := by
  unfold resetUntypedCap
  refine dke_bind (dke_liftE (ent_getCap _)) (fun cap => ?_)
  refine dke_bind (dke_returnOk _) (fun _ => dke_bind (dke_returnOk _) (fun _ => ?_))
  refine dke_ite _ (dke_returnOk _) ?_
  refine dke_bind (dke_liftE ?_) (fun _ => dke_bind (dke_returnOk _) (fun _ => ?_))
  · unfold deleteObjects
    exact dk_bind (ent_dmo _) (fun _ => dk_modify (fun σ => rfl))
  apply dke_ite
  · refine dke_bind (dke_liftE (dk_bind (dk_unless _ (ent_dmo _)) (fun _ => ent_setCap _ _))) (fun _ => ?_)
    unfold archPostResetUntyped; exact dke_liftE (dk_pure _)
  · refine dke_bind (dke_mapMEx (fun i => ?_) _) (fun _ => ?_)
    · exact dke_bind (dke_liftE (ent_dmo _)) (fun _ => dke_bind (dke_liftE (ent_setCap _ _)) (fun _ => ent_pp))
    · unfold archPostResetUntyped; exact dke_liftE (dk_pure _)

theorem fke_nall {β ε α : Type} {f : State Unit → β} {m : NonDetE (State Unit) ε α} (h : FKE f m) (s : State Unit) :
    NAll m.run s (fun x => f x.2 = f s) := fun x hx => h s x hx

/-- **The reset of a used cap keeps every object's type but its region's**,
which it deletes (`delete_objects`), on every outcome. -/
theorem reset_khT {sl : CslotPtr} {σ : State Unit} {dev : Bool} {pu : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dev pu sz fi, σ)}, False)) (hfi : fi ≠ 0) :
    NAll (resetUntypedCap (Z := Unit) sl).run σ (fun y => khT y.2 = khT (detype (regionSet pu sz) σ)) := by
  unfold resetUntypedCap
  apply nallE_bind
  refine nall_det (run_liftE hg) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nallE_bind
  apply nall_liftE
  intro y hy
  have hD : khT y.2 = khT (detype (regionSet pu sz) σ) := by
    unfold deleteObjects at hy
    obtain ⟨z, hz1, hz⟩ := hy
    rw [Set.mem_singleton_iff.1 hz]
    have e := kt_dmo _ σ z hz1
    funext o
    have e2 := congrFun e o
    simp only [khT, detype] at e2 ⊢
    split_ifs <;> simp_all
  dsimp only
  refine NAll.mono (P := fun x => khT x.2 = khT y.2) ?_ (fun x hx => hx.trans hD)
  refine fke_nall ?_ y.2
  apply dke_ite
  · refine dke_bind (dke_liftE (dk_bind (dk_unless _ (kt_dmo _)) (fun _ => kt_setCap _ _))) (fun _ => ?_)
    unfold archPostResetUntyped; exact dke_liftE (dk_pure _)
  · refine dke_bind (dke_mapMEx (fun i => ?_) _) (fun _ => ?_)
    · exact dke_bind (dke_liftE (kt_dmo _)) (fun _ => dke_bind (dke_liftE (kt_setCap _ _)) (fun _ => kt_pp))
    · unfold archPostResetUntyped; exact dke_liftE (dk_pure _)

end SpecKeep

section Comp
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem aType_arch {ko : Fl4Spec.KernelObject} {ao : Fl4Spec.ArchKernelObj}
    (h : Fl4Spec.aType ko = Fl4Spec.aType (.archObj ao)) : ∃ ao', ko = .archObj ao' := by
  cases ko <;> simp only [Fl4Spec.aType] at h <;> first | exact ⟨_, rfl⟩ | (split_ifs at h <;> cases h) | cases h

/-- **`UtRetPostJ` with a done reset**: the body's outcome after the reset. -/
theorem utRetPostJ_of_reset {σ σ1 σ2 : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.ok (), σ2) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (h : UtBodyPost (L := L) arI AR σ2 (.retype sl false base rb t us slots dev) res) :
    UtRetPostJ (L := L) arI AR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  have hy := invoke_reset_ok Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr (mem_of_run hrun)
  refine ⟨σ1, hst1, (.ok [], σ'), mem_bindE_ok hy (mem_returnOk []), ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

/-- **`UtRetPostJ` with a preempted reset**: the invocation's error outcome,
`JAtPre`, the relations from `XTopAt` there. -/
theorem utRetPostJ_of_preempt {σ σ1 σ' : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.error (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (he : res.1 = .Err .Preempted) (hpre : JAtPre (L := L) arI AR res.2.1 res.2.2 σ') {Z' : XSets}
    (hX : XTopAt (L := L) AR Z' res.2.1 res.2.2 σ') :
    UtRetPostJ (L := L) arI AR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX.rel
  refine ⟨σ1, hst1, (.error (), σ'), mem_bindE_err (invoke_reset_err Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr),
    ⟨Z'.th, Z'.G, Or.inr ⟨he, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ?_⟩
  rw [if_pos he]
  exact hpre

variable (arI) in
/-- **A retype body for one invocation's arguments** (UtEpRet's
`JAtZ.utEpBodyJ` shape): from any `JAtZ` state, entered, the source a CNode
slot's RAM untyped cap of free index `fi = fiv`, the arguments' `RetCtx` there
(any `reset` flag), `BufObjHyp`, `ArchFitHyp` and the kept references to a
range of the cap's free part, FL4's retype without a reset ends in
`UtBodyPost`. -/
def UtBodyHyp (AR : A → Fl4Spec.Cr3 → Prop) (pp : U64) (idx : List Bool) (p sb nt us dest off win : U64)
    (t : Fl4Spec.ApiObjectType) (r : Nat) (fiv : U64) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ → Entered σ →
    ∀ rs, Z.th pp = some (.cnode rs) → idx.length = rs →
    ∀ fi : U64, capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) → Z.c = 0#u64 →
    ∀ reset : Bool, RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r reset fiv → fiv = fi →
    BufObjHyp Z.B σ → ArchFitHyp H σ →
    (∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s) →
    UtFreeZ σ (p.val + fi.val) (p.val + 2 ^ sb.val) → UtNodesAt (L.ksb s) p sb →
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      UtBodyPost (L := L) arI AR σ (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false) res ⦄

/-- `JAtZ.utEpBodyJ` as `UtBodyHyp` (endpoints, notifications, replies, VSpace
tables, frames). -/
theorem utEp_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11)) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU hZ0 hKN =>
    J.utEpBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU hZ0 hKN

/-- UtScRet's `JAtZ.utScBodyJ` as `UtBodyHyp` (SCs). -/
theorem utSc_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 5) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utScBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtUtRet's `JAtZ.utUtBodyJ` as `UtBodyHyp` (untypeds). -/
theorem utUt_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 0) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utUtBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtPmRet's `JAtZ.utPmBodyJ` as `UtBodyHyp` (PML4s). -/
theorem utPm_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 8) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utPmBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtTcbRet's `JAtZ.utTcbBodyJ` as `UtBodyHyp` (TCBs). -/
theorem utTcb_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 1) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utTcbBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtCnRet's `JAtZ.utCnBodyJ` as `UtBodyHyp` (CNodes). -/
theorem utCn_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 4) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utCnBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

set_option maxHeartbeats 8000000 in
/-- **The retype with a reset at `J`** (module docstring). -/
theorem JAtZ.utResetJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64} (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r true fiv)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s))
    (hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv) (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) true
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype (pp.bv, idx) true p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, ⟨-, -, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have hcv := capV_of_capAt hcap
  have U := J.utc _ p sb fi false hAs hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfit := U.pfit
  have hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx) := by
    have e := hctx.resetEq; exact of_decide_eq_true e.symm
  have hfiv0 : fiv = 0#u64 := by rw [hctx.fidx]; rfl
  -- the restart
  obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hks1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hKN1 : UtNodesAt (L.ksb s1) p sb := by rw [hks1]; exact hUN _ hxG p sb fi hcv
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : σ1.kheap (L.curW s).bv = some (.tcb { x1 with tcbState := .restart }) := by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hni1 : Entered σ1 :=
    ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact J.restart_keeps_resume hni hkx hcur⟩
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hctx1 : RetCtx (L := L) Z.th s1 σ1 (pp.bv, idx) sb fi false nt us dest off win t r true fiv :=
    ⟨hctx.ty, hctx.size, ⟨hctx.cnode.1, hctx.cnode.2.1, hctx.cnode.2.2.1, by
        obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
        exact ⟨y, rr, gs, g, hy, (hSS1.capAt hy).trans hcy⟩⟩, hctx.window,
      fun i h1 h2 => (hSS1.capAt ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩).trans
        (hctx.empty i h1 h2),
      by rw [hσ1cdt]; exact hctx.resetEq, hctx.fidx, hctx.sizeBits, hctx.memory, hctx.device⟩
  have hBO1 : BufObjHyp Z.B σ1 := fun wp hw => by
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hw
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hkx] at hk; cases hk
      exact ⟨_, _, hσ1c, h1, by simpa [Fl4Spec.objBits] using h2⟩
    · exact ⟨o, ko, by rw [hσ1k o ho]; exact hk, h1, h2⟩
  have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hσ1c] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  have hnc1 : ¬ ∃ y, σ1.cdt y = some (pp.bv, idx) := by rw [hσ1cdt]; exact hnc
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
      ({(.untypedCap false p.bv sb.val fi.val, σ1)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  rw [hs1]; simp only [bind_ok]
  by_cases hf0 : fi.val = 0
  · -- an unused cap: the reset does nothing (`retype_reset_unused`)
    have hfi : fi = 0#u64 := UScalar.eq_of_val_eq (by rw [hf0]; rfl)
    subst hfi
    rw [retype_reset_unused arI s1 ar _ _ nt us dest off win false hcap1]
    have hU0 := invokeUntyped_reset_unused Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv
      (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false σ1 hg1
    have hRU1 : ∀ lo hi : Nat, p.val + (0#u64 : U64).val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
        KeptRefsP3 (L := L) H (RegionD H lo hi) s1 ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s1 :=
      fun lo hi h1 h2 => hRU s1 hs1 lo hi (J.free_dead hxG hcv h1 h2)
    have hms1 : σ1.machineState = σ.machineState := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
    have hZ1 : UtFreeZ σ1 (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := fun a h1 h2 => by
      rw [hms1]; exact hUZ _ hxG p sb _ hcv a h1 h2
    refine WP.spec_mono (hB Z H Cs Ac1 Lst1 D1 s1 ar σ1 J1 hni1 rs hpp hidx 0#u64 hcap1 hc0 true hctx1 hfiv0 hBO1
      hAF1 hRU1 hZ1 hKN1) (fun res h => ?_)
    obtain ⟨σ', hrun, hok, hrel, hJ⟩ := h
    exact utRetPostJ_of_body hst1 ⟨σ', by rw [hU0]; exact hrun, hok, hrel, hJ⟩
  -- a used cap: `reset_untyped` at the restart's state
  have hnd' : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr (pp.bv, idx)) := nodesc_of_cdt hP hC hAs hnc
  have hRD := (dead_childless J.jcov J.ut hI hxG hcv hnd').2
  obtain ⟨hKR, hDT⟩ := hRU s1 hs1 p.val (p.val + 2 ^ sb.val) (fun q k hq hr =>
    (hRD q k hq (by unfold RegionD MeetsR at hr; rw [hq] at hr; simpa using hr)).1)
  have hres1 : σ1.schedulerAction ≠ .chooseNewThread := by rw [hni1.2]; simp
  have hR0 : PPR0 σ := J.ppr0_start arI hni hRd0 hnq
  have hR01 : PPR0 σ1 := by
    rw [he1]
    have h := hR0.of_ppk (PPK.updTcbSc (y := { x1 with tcbState := .restart }) hkx rfl (hi := fun _ => Or.inr hcur.symm))
    unfold Notif.stsAct; split_ifs
    all_goals first | exact h | exact ⟨⟨h.1.1, fun u e => (by cases e), h.1.2.2⟩, h.2⟩
  refine retype_reset_wp arI s1 ar _ _ nt us dest off win false
    (J1.reset_untypedJ hAK hA hnd hPP hrcb hc0 hR01 hres1 hpp hidx hcap1 hnc1 hf0 hKR hDT hAF1
      J1.vsc.needR.1 J1.vsc.needR.2.1 J1.vsc.needR.2.2.1 J1.vsc.needR.2.2.2.1 J1.vsc.needR.2.2.2.2
      (hVM s1 hs1) Vs.needR_roots) ?_ ?_
  swap
  · intro e s2 a2 hpost
    rcases hpost with ⟨h, -⟩ | ⟨he, σ', hmem, hpre, Z', hX⟩
    · simp at h
    · exact utRetPostJ_of_preempt hst1 hmem he hpre hX
  intro s2 a2 hpost
  rcases hpost with ⟨-, σ2, Ac2, Lst2, D2, hmem, J2, hcap2, hkb2, -, -, hnc2, -, hz2, hSl2⟩ | ⟨h, -⟩
  swap
  · simp at h
  -- the spec's reset kept the entry fields and the old objects' types off the region
  have he := ent_reset (pp.bv, idx) σ1 (.ok (), σ2) hmem
  simp only [entF, Prod.mk.injEq] at he
  obtain ⟨hct2, hid2, hsa2⟩ := he
  have hni2 : Entered σ2 := ⟨by rw [hct2, hid2]; exact hni1.1, by rw [hsa2]; exact hni1.2⟩
  have hkT := reset_khT hg1 hf0 (.ok (), σ2) hmem
  have hkT' : ∀ o, (σ2.kheap o).map Fl4Spec.aType =
      if o ∈ regionSet p.bv sb.val then none else (σ1.kheap o).map Fl4Spec.aType := by
    intro o
    have e := congrFun hkT o
    simp only [khT, Fl4Spec.detype] at e
    rw [e]; split_ifs <;> rfl
  -- the source CNode, the destination CNode and the node cap's slot: off the region
  have hxout := U.ns hnc _ hxG
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    obtain ⟨q, j, hj, hq, he'⟩ := hAs.at
    have : pp = q := bv_inj hq
    subst this
    exact hj.obj_out hP U.nostr (by rw [← he']; exact hxout)
  have hpp2 : restrictTh Z.th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs) := by
    rw [restrictTh_out hppout]; exact hpp
  obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
  have hyG : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, hcy, by simp⟩
  have hdo := cnode_off_childless J.ut hI hxG hcv hnd' hyG (capV_of_capAt hcy)
  have hdest2 : restrictTh Z.th p.val (p.val + 2 ^ sb.val) dest = some (.cnode r) := by
    rw [restrictTh_out hdo]; exact hctx.cnode.1
  have hy2 : IsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) y := IsSlot.restrict hP U.nostr hy (U.ns hnc y hyG)
  have hyx : y ≠ cslotAddr (pp.bv, idx) := by
    rintro rfl; exact absurd (hcap.symm.trans hcy) (by simp)
  have hcapy : capAt (L.mem s2) y = ok (.CNode dest rr gs g) :=
    (hSl2 y hy2 hyx).trans ((hSS1.capAt hy).trans hcy)
  have hwin2 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    have hi : IsSlot Z.th (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
      ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩
    have hi2 : IsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
      ⟨dest, i, Or.inl ⟨r, hdest2, by have := hctx.window.2.2; omega⟩, rfl⟩
    have hne : slotAddr dest.bv (BitVec.ofNat 64 i) ≠ cslotAddr (pp.bv, idx) := by
      intro e; have h0 := hctx.empty i h1 h2; rw [e, hcap] at h0; simp at h0
    exact (hSl2 _ hi2 hne).trans ((hSS1.capAt hi).trans (hctx.empty i h1 h2))
  have hctx2 : RetCtx (L := L) (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) s2 σ2 (pp.bv, idx) sb 0#u64 false nt us
      dest off win t r true fiv :=
    ⟨hctx.ty, hctx.size, ⟨hdest2, hctx.cnode.2.1, hctx.cnode.2.2.1, y, rr, gs, g, hy2, hcapy⟩, hctx.window, hwin2,
      (decide_eq_true hnc2).symm, by rw [hfiv0]; rfl, hctx.sizeBits, hctx.memory, hctx.device⟩
  -- the IPC-buffer words kept: in objects off the region, kept with their type
  have hBO2 : BufObjHyp (KeepB (KBOf p sb) Z.B) σ2 := by
    intro wp hw
    obtain ⟨hwB, -, hw1⟩ := hw
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO1 wp hwB
    have hoff : o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
      rcases J1.sfree _ hxG p sb fi (capV_of_capAt hcap1) o ko hk with h | ⟨h3, h4⟩
      · exact h
      · exfalso; have := U.fiLe; rcases hw1 with e | e <;> omega
    have hnr : o ∉ regionSet p.bv sb.val := by
      rw [regionSet_iff' p o sb.val hsb hfit]
      have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko); omega
    have e := hkT' o
    rw [if_neg hnr, hk] at e
    cases h2' : σ2.kheap o with
    | none => rw [h2'] at e; cases e
    | some ko' =>
      rw [h2'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨o, ko', h2', h1, by rw [objBits_of_aType e]; exact h2⟩
  -- the arch objects: the old ones, `H`'s kept
  have hAF2 : ArchFitHyp (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) σ2 := by
    intro o ao n h hH
    rw [P1.Heap.drop_eq_some] at hH
    have e := hkT' o
    rw [h] at e
    split_ifs at e with hr
    · cases e
    · cases h1 : σ1.kheap o with
      | none => rw [h1] at e; cases e
      | some ko1 =>
        rw [h1] at e
        simp only [Option.map_some, Option.some.injEq] at e
        obtain ⟨ao1, rfl⟩ := aType_arch e.symm
        rw [objBits_of_aType e]; exact hAF1 o ao1 n h1 hH.2
  -- the kept references: the dropped heap has no object in the region
  have hRU2 : ∀ lo hi : Nat, p.val + (0#u64 : U64).val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) (H.drop (RegionD H p.val (p.val + 2 ^ sb.val)))
        (RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) lo hi) s2 ∧
      DbgTimerKept (L := L) (H.drop (RegionD H p.val (p.val + 2 ^ sb.val)))
        (RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) lo hi) Cs s2 := by
    intro lo hi h1 h2
    have e0 : (0#u64 : U64).val = 0 := rfl
    have hK : ∀ x, (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) x ≠ none →
        ¬ RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) lo hi x := by
      intro x hx hr
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hx
      obtain ⟨hnr, hHx⟩ := P1.Heap.drop_eq_some.1 hk
      have hr' : P1.MeetsR lo hi x.val
          (x.val + 2 ^ ((H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) x).elim 0 HKind.bits)) := hr
      have hnr' : ¬ P1.MeetsR p.val (p.val + 2 ^ sb.val) x.val (x.val + 2 ^ ((H x).elim 0 HKind.bits)) := hnr
      rw [hk] at hr'
      rw [hHx] at hnr'
      simp only [Option.elim, P1.MeetsR] at hr' hnr'
      omega
    exact ⟨⟨fun _ _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _,
      fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _⟩,
      fun _ _ _ => ⟨hK _, hK _, hK _, hK _, hK _⟩, fun _ _ => ⟨hK _, hK _, hK _⟩⟩
  have hZ2 : UtFreeZ σ2 (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := fun a h1 h2 => hz2 a (by
    have e0 : (0#u64 : U64).val = 0 := rfl
    omega) h2
  have hKN2 : UtNodesAt (L.ksb s2) p sb := by rw [hkb2]; exact hKN1
  exact WP.spec_mono (hB _ _ Cs Ac2 Lst2 D2 s2 a2 σ2 J2 hni2 rs hpp2 hidx 0#u64 hcap2 hc0 true hctx2 hfiv0 hBO2 hAF2
    hRU2 hZ2 hKN2) (fun res h => utRetPostJ_of_reset hst1 hmem h)


variable (arI) in
/-- **[W] The retype of a RAM untyped at `J`, outside the proved types**
(UtEpRet's `JUtRetHypR` narrowed by the reset): asked only of an object type
other than endpoints, notifications, replies, PDPTs, page tables, page
directories, frames (UtEpRet's `JAtZ.utEpJ`), untypeds (UtUtRet's
`JAtZ.utUtJ`), SCs (UtScRet's `JAtZ.utScJ`) and PML4s (UtPmRet's
`JAtZ.utPmJ`), CNodes (UtCnRet's `JAtZ.utCnJ`) and TCBs (UtTcbRet's
`JAtZ.utTcbJ`), with or without a reset (`JAtZ.utResetJ`): the VCPU/EPT
types (14..18, also `JUtPath.vtx` [scope]). l4v: `invoke_untyped_corres` with
`invoke_untyped_invs`. -/
def JUtRetHypR2 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (sl : Fl4Spec.CslotPtr) (p sb fi ct : U64) (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi false nt us dest off win t r reset fiv →
    (nt.val ≠ 2 ∧ nt.val ≠ 3 ∧ nt.val ≠ 6 ∧ nt.val ≠ 7 ∧ nt.val ≠ 12 ∧ nt.val ≠ 13 ∧
      nt.val ≠ 9 ∧ nt.val ≠ 10 ∧ nt.val ≠ 11 ∧
      nt.val ≠ 0 ∧ nt.val ≠ 5 ∧ nt.val ≠ 8 ∧ nt.val ≠ 4 ∧ nt.val ≠ 1) →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄

/-- **`JUtRetHypR` from its narrowed form**: the reset retypes of the proved
types by `JAtZ.utResetJ` with their bodies (`utEp_bodyHyp`, `utUt_bodyHyp`,
`utSc_bodyHyp`, `utPm_bodyHyp`, `utCn_bodyHyp`, `utTcb_bodyHyp`), the rest `JUtRetHypR2` [W]. Premises of the
reset: `PPPlat`, `resetChunkBits = 16` [P], `hRd0` [J], `VsReachMiss` [J] at
the restart's state (no extra roots), `ArchFitHyp`/`RegionUnrefJ` [J]. -/
theorem JAtZ.jUtRetHypR_of {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s))
    {blk call don : Bool} {argsU : List U64}
    (hR : JUtRetHypR2 (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU) :
    JUtRetHypR (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx hcase
  by_cases hcov : nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨
      nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11 ∨ nt.val = 0 ∨ nt.val = 5 ∨ nt.val = 8 ∨ nt.val = 4 ∨ nt.val = 1
  · have hrs : reset = true := by
      rcases hcase with h | h
      · exact h
      · exfalso; omega
    subst hrs
    obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    have hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv := by
      rcases (show (nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨
          nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) ∨
          nt.val = 0 ∨ nt.val = 5 ∨ nt.val = 8 ∨ nt.val = 4 ∨ nt.val = 1 by omega) with
        h | h | h | h | h | h
      · exact utEp_bodyHyp (by omega)
      · exact utUt_bodyHyp h
      · exact utSc_bodyHyp h
      · exact utPm_bodyHyp h
      · exact utCn_bodyHyp h
      · exact utTcb_bodyHyp h
    exact J.utResetJ hni hct hpp rfl hcap hc0 hctx hBO hAF hRU hAK hA hnd hPP hrcb hRd0 hnq hVM hUZ hUN hB blk call don
  · exact hR nt us dest off win t r reset fiv hh hctx (by omega)

end Comp

end

end Fl4Proofs.P3
