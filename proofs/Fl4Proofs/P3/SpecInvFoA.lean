/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4 F5, fo1): **FpuOwnOK, l4v
X64 `valid_cur_fpu`, carried with "the owner holds a thread cap"**, the
combinators and the owner writers up to `schedule` (spec side only).

* **`FT σ`**: the FPU owner `t` (if any) is a TCB and some slot holds
  `threadCap t`. `FpuOwnOK` (ScArchF; restated as `FpuOwnOKS`) is its first half
  (`fpuOwnOK_of_ft`).
  The second half is what the untyped reset's / MakePool's `delete_objects`
  needs: the region of a childless untyped holds no object a cap names (ut4's
  UtCh), so not the owner. In l4v it is `arch_tcb_live` (`tcb_cur_fpu`) +
  `if_live_then_nonz_cap`; here typed as IfLiveT is (an Inactive thread can own
  the FPU: `suspend` releases nothing; `finalise_cap` of its final thread cap
  runs `prepare_thread_delete` = `fpu_release` before the Zombie replaces it).
* `oL σ`: the owner as a list. `FT` is IfLiveT's carried `K` at `oL σ`:
  `ILF K σ := IL K σ ∧ FT σ`, `FN K σ := ILN K σ ∧ FT σ`. **`fo_ik` / `fo_ikn`**:
  a function keeping `IL (L ++ K)` for every `L` (il1/il2's families) and the
  owner with its TCB-ness (`OIK`, SpecInvFoG*) keeps `ILF K` / `FN K`.
* Owner writers: `fo_setOwner` (`set_x64_current_fpu_owner n`: the new owner
  holds a thread cap before, it is a TCB after the `arch_thread_set`),
  `fo_switchLocalFpuOwner`, `fo_fpuRelease` (+ `fpuRelease_ne`: the owner is
  not the released thread after), `fo_lazyFpuRestore` (the thread in `K`),
  `fo_archSwitchToThread`, `fo_switchToThread`, **`fo_guardedSwitchTo`**
  (`schedulable` ⇒ runnable ⇒ live ⇒ a thread cap by IfLiveT),
  `fo_chooseThread`, `fo_scheduleChooseNewThread`, **`fo_schedule`**.
-/
import Fl4Proofs.P3.SpecInvFoG6
import Fl4Proofs.P3.SpecInvNtfnQLW
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The invariant -/

/-- **FT**: the FPU owner is a TCB holding a thread cap. -/
def FT (σ : State Unit) : Prop :=
  ∀ t, σ.archState.x64CurrentFpuOwner = some t → TcbAt σ t ∧ HasTC σ t

/-- **`FpuOwnOKS`**: ScArchF's `FpuOwnOK` restated (the same definition; ScArchF lies in
the scheduler cone, so it is not imported here: `fpuOwnOKS_iff` in SpecInvFoBridge). -/
def FpuOwnOKS (σ : State Unit) : Prop :=
  ∀ o, σ.archState.x64CurrentFpuOwner = some o → ∃ x, σ.kheap o = some (.tcb x)

theorem fpuOwnOK_of_ft {σ : State Unit} (h : FT σ) : FpuOwnOKS σ :=
  fun o e => (h o e).1

/-- The owner as a list. -/
def oL (σ : State Unit) : List ObjRef := σ.archState.x64CurrentFpuOwner.toList

def ILF (K : List ObjRef) (σ : State Unit) : Prop := IL K σ ∧ FT σ
def FN (K : List ObjRef) (σ : State Unit) : Prop := ILN K σ ∧ FT σ

theorem mem_oL {σ : State Unit} {t : ObjRef} : t ∈ oL σ ↔ σ.archState.x64CurrentFpuOwner = some t := by
  unfold oL
  cases σ.archState.x64CurrentFpuOwner <;> simp [eq_comm]

theorem il_oL {K : List ObjRef} {σ : State Unit} (h : IL K σ) (hF : FT σ) : IL (oL σ ++ K) σ :=
  ⟨h.1, fun t ht => (List.mem_append.1 ht).elim (fun h' => (hF t (mem_oL.1 h')).2) (h.2 t)⟩

theorem ft_back {K : List ObjRef} {σ y : State Unit} (hI : IL (oL σ ++ K) y) (hO : OI σ.archState.x64CurrentFpuOwner y) :
    ILF K y := by
  refine ⟨il_app_right hI, fun t ht => ?_⟩
  rw [hO.1] at ht
  exact ⟨hO.2 t ht, hI.2 t (List.mem_append_left _ (mem_oL.2 ht))⟩

theorem fo_ik {α : Type} {K : List ObjRef} {m : NonDet (State Unit) α} (hI : ∀ L, ILK (L ++ K) m)
    (hO : ∀ q, OIK q m) : IK (ILF K) m := by
  intro σ hσ y hy
  exact ft_back (hI (oL σ) σ (il_oL hσ.1 hσ.2) y hy) (hO _ σ ⟨rfl, fun t ht => (hσ.2 t ht).1⟩ y hy)

theorem fo_ikp {α : Type} {K : List ObjRef} {m : NonDet (State Unit) α} (σ : State Unit)
    (hI : ∀ L, IKp (IL (L ++ K)) σ m) (hO : ∀ q, OIK q m) : IKp (ILF K) σ m := by
  intro hσ y hy
  exact ft_back (hI (oL σ) (il_oL hσ.1 hσ.2) y hy) (hO _ σ ⟨rfl, fun t ht => (hσ.2 t ht).1⟩ y hy)

theorem fo_ikn {α : Type} {K : List ObjRef} {m : NonDet (State Unit) α} (hI : ∀ L, IK (ILN (L ++ K)) m)
    (hO : ∀ q, OIK q m) : IK (FN K) m := by
  intro σ hσ y hy
  have h := hI (oL σ) σ ⟨il_oL hσ.1.1 hσ.2, hσ.1.2⟩ y hy
  have h2 := ft_back h.1 (hO _ σ ⟨rfl, fun t ht => (hσ.2 t ht).1⟩ y hy)
  exact ⟨⟨h2.1, h.2⟩, h2.2⟩

theorem fn_ilf {K : List ObjRef} {σ : State Unit} (h : FN K σ) : ILF K σ := ⟨h.1.1, h.2⟩

theorem ilf_mono {K K' : List ObjRef} {σ : State Unit} (h : ILF K σ) (hK : ∀ u ∈ K', u ∈ K) : ILF K' σ :=
  ⟨il_mono h.1 hK, h.2⟩

theorem ilf_tail {K : List ObjRef} {σ : State Unit} {t : ObjRef} (h : ILF (t :: K) σ) : ILF K σ :=
  ⟨il_tail h.1, h.2⟩

/-- `ILF` reads the heap and the arch state only. -/
theorem ilf_of_eq {K : List ObjRef} {σ σ' : State Unit} (ek : σ'.kheap = σ.kheap)
    (ea : σ'.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner) (h : ILF K σ) : ILF K σ' := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [ek]
  refine ⟨il_of_kheap ek h.1, fun t ht => ?_⟩
  rw [ea] at ht
  obtain ⟨⟨x, hx⟩, ⟨s, hs⟩⟩ := h.2 t ht
  exact ⟨⟨x, by rw [ek]; exact hx⟩, ⟨s, by rw [hc]; exact hs⟩⟩

/-- A membership goal `t ∈ L ++ K` from `t ∈ K`. -/
macro "fo_mem" : tactic => `(tactic| first
  | assumption
  | (exact List.mem_append_right _ (by assumption))
  | (intro _ h; exact List.mem_append_right _ (by simp_all))
  | simp_all)

/-- A leaf: il1/il2's `IL` lemma and the generated `OI` lemma. -/
syntax "fo_leaf" : tactic
macro_rules | `(tactic| fo_leaf) => `(tactic| (refine fo_ik (fun _ => ?_) (fun _ => ?_) <;> (first | il_leaf | oi_leaf) <;> fo_mem))

/-! ## `arch_thread_set` names a TCB -/

theorem mem_archThreadSet_tcb {f : ArchTcb → ArchTcb} {t : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (archThreadSet (Z := Unit) f t σ).1) :
    TcbAt y.2 t ∧ y.2.archState = σ.archState := by
  unfold archThreadSet at h
  obtain ⟨z, hz, h⟩ := h
  unfold NonDet.getsThe at hz
  cases e : getTcb (Z := Unit) t σ with
  | none => rw [e] at hz; exact hz.elim
  | some x =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨k, -, -, e2⟩ := mem_setObjectF h
    rw [e2]
    exact ⟨⟨_, Function.update_self _ _ _⟩, rfl⟩

/-! ## The owner writers -/

theorem fo_setOwner (n : Option ObjRef) {K : List ObjRef} :
    HK (IL (n.toList ++ K)) (ILF K) (setX64CurrentFpuOwner (Z := Unit) n) := by
  intro σ hσ y hy
  unfold setX64CurrentFpuOwner at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz1
  dsimp only at hy
  obtain ⟨z2, hz2, hy⟩ := hy
  have h2 : IL (n.toList ++ K) z2.2 :=
    ik_maybeM (fun a => il_archThreadSet _ a) _ σ hσ z2 hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  dsimp only at hy
  have h3 : IL (n.toList ++ K) ({ z2.2 with archState := { z2.2.archState with x64CurrentFpuOwner := n } }) :=
    il_of_kheap rfl h2
  cases n with
  | none =>
    simp only [NonDet.maybeM] at hy
    have e : y.2 = _ := (Prod.ext_iff.1 (Set.mem_singleton_iff.1 hy)).2
    rw [e]
    exact ⟨il_app_right h3, fun t ht => by simp at ht⟩
  | some t =>
    simp only [NonDet.maybeM] at hy
    have h4 := il_archThreadSet (K := [t] ++ K) _ t _ h3 y hy
    obtain ⟨hT, ea⟩ := mem_archThreadSet_tcb hy
    refine ⟨il_app_right h4, fun u hu => ?_⟩
    rw [ea] at hu
    obtain rfl : t = u := Option.some.inj hu
    exact ⟨hT, h4.2 t (by simp)⟩

/-- `set_x64_current_fpu_owner n` sets the owner to `n`. -/
theorem hk_setOwner (n : Option ObjRef) :
    HK (fun _ => True) (fun s => s.archState.x64CurrentFpuOwner = n) (setX64CurrentFpuOwner (Z := Unit) n) := by
  intro σ _ y hy
  unfold setX64CurrentFpuOwner at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz1
  dsimp only at hy
  obtain ⟨z2, -, hy⟩ := hy
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  dsimp only at hy
  cases n with
  | none =>
    simp only [NonDet.maybeM] at hy
    rw [(Prod.ext_iff.1 (Set.mem_singleton_iff.1 hy)).2]
  | some t =>
    simp only [NonDet.maybeM] at hy
    rw [(mem_archThreadSet_tcb hy).2]

theorem hk_switchLocal (n : Option ObjRef) :
    HK (fun _ => True) (fun s => s.archState.x64CurrentFpuOwner = n) (switchLocalFpuOwner (Z := Unit) n) := by
  cases n <;> (unfold switchLocalFpuOwner; dsimp only) <;>
    repeat' (first
      | exact hk_setOwner _
      | (refine hk_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_))

theorem fo_switchLocalFpuOwner (n : Option ObjRef) {K : List ObjRef} :
    HK (IL (n.toList ++ K)) (ILF K) (switchLocalFpuOwner (Z := Unit) n) := by
  cases n <;> (unfold switchLocalFpuOwner; dsimp only) <;>
    repeat' (first
      | exact fo_setOwner _
      | (refine hk_bind (hk_of_ik ?_) fun _ => ?_; il_auto))

theorem fo_fpuRelease (t : ObjRef) {K : List ObjRef} : IK (ILF K) (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease
  refine ik_gets_bind fun σ => ?_
  unfold NonDet.when
  split
  · intro hσ y hy
    exact fo_switchLocalFpuOwner none σ hσ.1 y hy
  · exact ikp_of_ik (ik_pure' _) σ

/-- After `fpu_release t`, `t` is not the owner. -/
theorem fpuRelease_ne (t : ObjRef) {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (fpuRelease (Z := Unit) t σ).1) : y.2.archState.x64CurrentFpuOwner ≠ some t := by
  unfold fpuRelease at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rw [hk_switchLocal none _ trivial y hy]; simp
  · rename_i hne
    rw [(Prod.ext_iff.1 (Set.mem_singleton_iff.1 hy)).2]
    exact hne

theorem fo_lazyFpuRestore (t : ObjRef) {K : List ObjRef} :
    HK (ILF (t :: K)) (ILF K) (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore
  refine hk_bind (hk_of_ik (by unfold threadGet; repeat' ik_step0)) fun flags => ?_
  split
  · exact fun σ h y hy => ilf_tail (fo_ik (fun _ => il_doMachineOp _) (fun _ => by oi_auto) σ h y hy)
  · refine hk_bind (hk_of_ik (ik_gets _)) fun cur => ?_
    split
    · exact fun σ h y hy => ilf_tail (fo_ik (fun _ => il_doMachineOp _) (fun _ => by oi_auto) σ h y hy)
    · exact fun σ h y hy => fo_switchLocalFpuOwner (some t) σ h.1 y hy

/-- `arch_prepare_next_domain` (= `switch_local_fpu_owner none`). -/
theorem fo_archPrepareNextDomain {K : List ObjRef} : IK (ILF K) (archPrepareNextDomain (Z := Unit)) :=
  fun σ h y hy => fo_switchLocalFpuOwner none σ h.1 y hy

theorem hk_ilf_frame {α : Type} {K K' : List ObjRef} {m : NonDet (State Unit) α} (hI : ∀ L, ILK (L ++ K) m)
    (hO : ∀ q, OIK q m) : HK (ILF K) (ILF K) m := hk_of_ik (fo_ik hI hO)

theorem fo_archSwitchToThread (t : ObjRef) {K : List ObjRef} :
    HK (ILF (t :: K)) (ILF K) (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread
  exact hk_bind (hk_of_ik (fo_ik (fun _ => il_setVmRoot _) (fun _ => oi_setVmRoot _))) fun _ => fo_lazyFpuRestore t

theorem fo_switchToThread (t : ObjRef) {K : List ObjRef} :
    HK (ILF (t :: K)) (ILF K) (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  refine hk_bind (hk_of_ik ik_get) fun _ => hk_bind (hk_of_ik (ik_assert _)) fun _ =>
    hk_bind (fo_archSwitchToThread t) fun _ => hk_bind (hk_of_ik (fo_ik (fun _ => il_tcbSchedAction _ _)
      (fun _ => oi_tcbSchedAction _ _))) fun _ => hk_of_ik ?_
  exact ik_modify fun σ h => ilf_of_eq rfl rfl h

theorem sched_tcb {σ : State Unit} {t : ObjRef} (hs : schedulable (Z := Unit) t σ = true) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ runnable x.tcbState = true := by
  have hr := sched_runnable hs
  unfold schedulable at hs
  simp only [decide_eq_true_eq] at hs
  have h1 := hs.1
  cases e : σ.kheap t with
  | none => simp [optPred, optMapSome, optMap, tcbsOf, tcbsOfKh, e] at h1
  | some o =>
    cases o with
    | tcb x => exact ⟨x, rfl, hr x e⟩
    | _ => simp [optPred, optMapSome, optMap, tcbsOf, tcbsOfKh, e, tcbOf] at h1

/-- **`guarded_switch_to`**: the target is schedulable, so runnable, so live, so it holds a thread cap. -/
theorem fo_guardedSwitchTo (t : ObjRef) {K : List ObjRef} : IK (ILF K) (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  refine ik_bind (by unfold threadGet; repeat' ik_step0) fun _ => ik_bind (ik_assertOpt _) fun _ => ?_
  refine ik_gets_bind fun σ => ?_
  intro hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hsch, rfl⟩ := hz
  have hK : ILF (t :: K) σ := by
    refine ⟨⟨hσ.1.1, fun u hu => ?_⟩, hσ.2⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · obtain ⟨x, hx, hr⟩ := sched_tcb hsch
      exact hσ.1.1 u x hx (runnable_live hr)
    · exact hσ.1.2 u hu
  refine (?_ : HK (ILF (t :: K)) (ILF K) _) σ hK y hy
  refine hk_bind (hk_of_ik (ik_gets _)) fun _ => hk_bind (hk_of_ik (by unfold threadGet; repeat' ik_step0))
    fun _ => hk_bind (hk_of_ik (ik_assert _)) fun _ => fo_switchToThread t

theorem fo_chooseThread {K : List ObjRef} : IK (ILF K) (chooseThread (Z := Unit)) := by
  unfold chooseThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ?_
  split
  · exact fo_ik (fun _ => il_switchToIdleThread) (fun _ => oi_switchToIdleThread)
  · exact fo_guardedSwitchTo _

theorem fo_scheduleChooseNewThread {K : List ObjRef} : IK (ILF K) (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_when _ (ik_bind fo_archPrepareNextDomain fun _ =>
    fo_ik (fun _ => il_nextDomain) (fun _ => oi_nextDomain))) fun _ => ik_bind fo_chooseThread fun _ => ?_
  exact fo_ik (fun _ => il_setSchedulerAction _) (fun _ => oi_setSchedulerAction _)

macro "fo_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact fo_scheduleChooseNewThread
  | with_reducible exact fo_guardedSwitchTo _
  | with_reducible exact fo_chooseThread
  | fo_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

/-- **`schedule` keeps `ILF K`**. -/
theorem fo_schedule {K : List ObjRef} : IK (ILF K) (schedule (Z := Unit)) := by
  unfold schedule; fo_auto

theorem fo_domainSetStart {K : List ObjRef} (i : Nat) : IK (ILF K) (domainSetStart (Z := Unit) i) :=
  fo_ik (fun _ => il_domainSetStart _) (fun _ => by unfold domainSetStart; oi_auto)

end

end Fl4Proofs.P3.SInvF
