/-
P3 (DESIGN.md §9), invariant line G1 (il1): **IfLiveT, l4v
`if_live_then_nonz_cap` for TCBs** (spec side only, outside the JAtZ cone).

* `liveSt s`: the thread state is neither Inactive nor IdleThreadState (l4v
  `live (TCB t)`, the thread-state part).
* `HasTC σ t`: some slot holds `threadCap t`.
* **`IfLiveT σ`**: every live TCB has a thread cap. This is l4v's
  `if_live_then_nonz_cap` at TCBs with the cap typed: in l4v the cap is a
  `ThreadCap` or a `Zombie` (`valid_cap`); here Zombies are not counted, since
  `finalise_cap` suspends a thread (Inactive) before its final thread cap is
  replaced by a Zombie, and nothing makes a thread live again without a
  thread cap to it (resume / write-registers decode it from a thread cap).
  Typing the cap makes every removal of a cap other than a thread cap free.
  `ifLiveT_objRefs`: the untyped form (some cap with `t ∈ objRefs`), so
  `IfLiveT → IfLiveB` (SpecInvNtfnQH2's [J] premise; see SpecInvNtfnQLT).
* Carried form `IL K σ := IfLiveT σ ∧ ∀ t ∈ K, HasTC σ t` (`K`: threads known
  to hold a thread cap — read in a live state, or named by a decoded thread
  cap), the `NQ K` pattern of SpecInvNtfnQ. It reads the heap only.
* Leaves: `il_update` (one heap write keeping the caps, a new live state only
  at a live TCB or a thread of `K`), `il_of_frame` (a `UK` frame + a state
  frame), `setObject` / `set_simple_ko` / `thread_set` / `arch_thread_set` /
  `as_user` / `set_mrs` / `set_thread_state` (live only at `K`) /
  `option_update_thread` / machine and extended ops; `il_setCap_p` (the slot's
  old cap is no thread cap, or the same, or another slot holds it, or the
  thread is not live and not in `K`); `il_capInsert` (the destination is
  asserted null, `set_untyped_cap_as_full` rewrites an untyped cap);
  `il_rds` (a state read of a live state adds the thread to `K`).
-/
import Fl4Proofs.P3.SpecInvNtfnQ
import Fl4Proofs.P3.SpecInvUtR
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- l4v `live (TCB t)`, the thread-state part. -/
def liveSt : ThreadState → Prop
  | .inactive => False
  | .idleThreadState => False
  | _ => True

theorem liveSt_of_ipcBlk {s : ThreadState} (h : isBoN s ∨ epBlocked s ≠ none) : liveSt s := by
  cases s <;> simp_all [liveSt, isBoN, epBlocked]

/-- Some slot holds a thread cap to `t`. -/
def HasTC (σ : State Unit) (t : ObjRef) : Prop := ∃ s, SInvU.capAt σ s = some (.threadCap t)

/-- **IfLiveT** (l4v `if_live_then_nonz_cap` at TCBs, the cap typed: see the module docstring). -/
def IfLiveT (σ : State Unit) : Prop :=
  ∀ t y, σ.kheap t = some (.tcb y) → liveSt y.tcbState → HasTC σ t

theorem ifLiveT_objRefs {σ : State Unit} (h : IfLiveT σ) {t : ObjRef} {y : Tcb}
    (hy : σ.kheap t = some (.tcb y)) (hl : liveSt y.tcbState) :
    ∃ s c, SInvU.capAt σ s = some c ∧ t ∈ objRefs c := by
  obtain ⟨s, hs⟩ := h t y hy hl
  exact ⟨s, _, hs, by simp [objRefs]⟩

/-- The carried form: `IfLiveT` and the threads of `K` hold a thread cap. -/
def IL (K : List ObjRef) (σ : State Unit) : Prop := IfLiveT σ ∧ ∀ t ∈ K, HasTC σ t

abbrev ILK {α : Type} (K : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (IL K) m
abbrev ILKE {ε α : Type} (K : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (IL K) m

theorem il_nil_iff (σ : State Unit) : IL [] σ ↔ IfLiveT σ :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ h => by simp at h⟩⟩

theorem il_mono {K K' : List ObjRef} {σ : State Unit} (h : IL K σ) (hK : ∀ u ∈ K', u ∈ K) : IL K' σ :=
  ⟨h.1, fun u hu => h.2 u (hK u hu)⟩

theorem il_tail {K : List ObjRef} {σ : State Unit} {t : ObjRef} (h : IL (t :: K) σ) : IL K σ :=
  il_mono h fun _ h => List.mem_cons_of_mem _ h

theorem il_consT {K : List ObjRef} {σ : State Unit} (h : IL K σ) {t : ObjRef} (ht : HasTC σ t) :
    IL (t :: K) σ := by
  refine ⟨h.1, fun u hu => ?_⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ht
  · exact h.2 u hu

/-- A live TCB joins `K`. -/
theorem il_consR {K : List ObjRef} {σ : State Unit} (h : IL K σ) {t : ObjRef} {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hl : liveSt x.tcbState) : IL (t :: K) σ :=
  il_consT h (h.1 t x hx hl)

/-- `IL` reads the heap only. -/
theorem il_of_kheap {K : List ObjRef} {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) (h : IL K σ) : IL K σ' := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by
    funext sl; unfold SInvU.capAt; rw [e]
  have hT : ∀ t, HasTC σ' t ↔ HasTC σ t := fun t => by unfold HasTC; rw [hc]
  exact ⟨fun t y ht hl => (hT t).2 (h.1 t y (e ▸ ht) hl), fun t ht => (hT t).2 (h.2 t ht)⟩

/-! ## One heap write -/

/-- When a heap write at `p` (old object `o0`, new `o`) keeps `IL K`: the caps
are kept, a live new TCB was live before or is a thread of `K`. -/
def ILOK (K : List ObjRef) (p : ObjRef) (o0 o : KernelObject) : Prop :=
  SInvU.capView o = SInvU.capView o0 ∧
    ∀ y', o = .tcb y' → liveSt y'.tcbState → p ∈ K ∨ ∃ y, o0 = .tcb y ∧ liveSt y.tcbState

theorem il_update {K : List ObjRef} {σ : State Unit} {p : ObjRef} {o0 o : KernelObject} (h : IL K σ)
    (hp : σ.kheap p = some o0) (hok : ILOK K p o0 o) :
    IL K { σ with kheap := Function.update σ.kheap p (some o) } := by
  have hc : SInvU.capAt { σ with kheap := Function.update σ.kheap p (some o) } = SInvU.capAt σ :=
    congrArg (fun w : SInvU.UView => w.2.1) (SInvU.uV_update hp hok.1)
  have hT : ∀ t, HasTC { σ with kheap := Function.update σ.kheap p (some o) } t ↔ HasTC σ t :=
    fun t => by unfold HasTC; rw [hc]
  refine ⟨fun t y ht hl => (hT t).2 ?_, fun t ht => (hT t).2 (h.2 t ht)⟩
  dsimp only at ht
  rw [Function.update_apply] at ht
  split_ifs at ht with e
  · subst e
    rcases hok.2 y (Option.some.inj ht) hl with hK | ⟨y0, e0, hl0⟩
    · exact h.2 t hK
    · subst e0; exact h.1 t y0 hp hl0
  · exact h.1 t y ht hl

/-! ## Frames -/

/-- The live TCBs of the result hold a thread cap at `σ0`. -/
def LQ (σ0 : State Unit) (p : ObjRef) (x : Tcb) : Prop := liveSt x.tcbState → HasTC σ0 p

/-- **A `UK` frame and a state frame give `IL K`**: every outcome keeps the
caps, and its live TCBs had a thread cap at the start. -/
theorem il_of_frame {K : List ObjRef} {α : Type} {m : NonDet (State Unit) α} (hu : ∀ v, SInvU.UK v m)
    (ht : ∀ σ0, IL K σ0 → IK (TP (LQ σ0)) m) : ILK K m := by
  intro σ hσ y hy
  have hc : SInvU.capAt y.2 = SInvU.capAt σ :=
    congrArg (fun w : SInvU.UView => w.2.1) (hu (SInvU.uV σ) σ rfl y hy)
  have hT : ∀ t, HasTC y.2 t ↔ HasTC σ t := fun t => by unfold HasTC; rw [hc]
  have h0 : TP (LQ σ) σ := fun p x hp hl => hσ.1 p x hp hl
  have h1 := ht σ hσ σ h0 y hy
  exact ⟨fun t x hx hl => (hT t).2 (h1 t x hx hl), fun t ht' => (hT t).2 (hσ.2 t ht')⟩

/-- The state-keeping TCB writes keep `LQ`. -/
theorem lq_arch {σ0 : State Unit} {t : ObjRef} (x : Tcb) (a : ArchTcb) (h : LQ σ0 t x) :
    LQ σ0 t { x with tcbArch := a } := h

section W
variable {K : List ObjRef}

theorem il_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : IL K σ → ∀ o0, σ.kheap p = some o0 → aType o0 = aType o → ILOK K p o0 o) :
    IKp (IL K) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, e2⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at e2 hk; subst y2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact il_update hσ hk (ho hσ y1 hk hty)

/-- `setObject` of an object that is no TCB, of the old object's type, with the old caps. -/
theorem il_setObject (p : ObjRef) (o : KernelObject) (h1 : ∀ y, o ≠ .tcb y)
    (ho : ∀ old, aType old = aType o → SInvU.capView o = SInvU.capView old) :
    ILK K (setObject (Z := Unit) p o) :=
  fun σ => il_setObject_p p o σ fun _ o0 _ hty => ⟨ho o0 hty, fun y' e => absurd e (h1 y')⟩

theorem il_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    ILK K (setSimpleKo (Z := Unit) f p e) :=
  il_of_frame (fun v => SInvU.uk_setSimpleKo f p e) fun _ _ => tp_setSimpleKo f p e

theorem il_threadSet (f : Tcb → Tcb) (t : ObjRef) (hc : ∀ x, tcbCnodeMap (f x) = tcbCnodeMap x)
    (hs : ∀ x, (f x).tcbState = x.tcbState) : ILK K (threadSet (Z := Unit) f t) :=
  il_of_frame (fun v => SInvU.uk_threadSet f t hc) fun _ _ =>
    tp_threadSet f t fun x h hl => h (by rw [← hs x]; exact hl)

theorem il_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : ILK K (archThreadSet (Z := Unit) f t) :=
  il_of_frame (fun v => SInvU.uk_archThreadSet f t) fun _ _ => tp_archThreadSet f t fun x a h => h

theorem il_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : ILK K (asUser (Z := Unit) t u) :=
  il_of_frame (fun v => SInvU.uk_asUser t u) fun _ _ => tp_asUser t u fun x a h => h

theorem il_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : ILK K (setMrs (Z := Unit) t b ms) :=
  il_of_frame (fun v => SInvU.uk_setMrs t b ms) fun _ _ => tp_setMrs t b ms fun x a h => h

theorem il_doMachineOp {α : Type} (mop : NonDet MachineState α) : ILK K (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem il_doExtendedOp (eop : DetExtMonad Unit) : ILK K (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) _

theorem il_setThreadStateAct (t : ObjRef) : ILK K (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

/-- `set_thread_state`: a live state only at a thread of `K`. -/
theorem il_setThreadState (t : ObjRef) (ts : ThreadState) (h : liveSt ts → t ∈ K) :
    ILK K (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind ?_ fun _ => il_setThreadStateAct t
  exact il_of_frame (fun v => SInvU.uk_threadSet _ t fun _ => rfl) fun σ0 h0 =>
    tp_threadSet _ t fun x _ hl => h0.2 t (h hl)

theorem il_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (hc : ∀ a x, tcbCnodeMap (fn a x) = tcbCnodeMap x) (hs : ∀ a x, (fn a x).tcbState = x.tcbState) :
    ILK K (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact il_threadSet _ _ (hc _) (hs _)

/-! ## `set_cap` -/

/-- The TCB states of `σ0`, as a `TP` predicate. -/
def StQ (σ0 : State Unit) (p : ObjRef) (x : Tcb) : Prop := ∃ y, σ0.kheap p = some (.tcb y) ∧ y.tcbState = x.tcbState

/-- When overwriting the cap in `sl` by `c` keeps `IL K`: the old cap is no
thread cap, or the same one, or another slot holds it, or its thread is not
live and not in `K`. -/
def TcSafe (K : List ObjRef) (σ : State Unit) (sl : CslotPtr) (c : Cap) : Prop :=
  ∀ t, SInvU.capAt σ sl = some (.threadCap t) →
    c = .threadCap t ∨ (∃ s, s ≠ sl ∧ SInvU.capAt σ s = some (.threadCap t)) ∨
      (t ∉ K ∧ ∀ y, σ.kheap t = some (.tcb y) → ¬ liveSt y.tcbState)

theorem tcSafe_of_not {K : List ObjRef} {σ : State Unit} {sl : CslotPtr} {c : Cap}
    (h : ∀ t, SInvU.capAt σ sl ≠ some (.threadCap t)) : TcSafe K σ sl c :=
  fun t ht => absurd ht (h t)

theorem il_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hs : IL K σ → TcSafe K σ sl c) :
    IKp (IL K) σ (setCap (Z := Unit) c sl) := by
  intro hσ y hy
  obtain ⟨-, hne, hsl, -, -⟩ := SInvU.setCap_out hy
  have h0 : TP (StQ σ) σ := fun p x hp => ⟨x, hp, rfl⟩
  have h1 : TP (StQ σ) y.2 :=
    tp_setCap c sl (fun p x h => ⟨h, h, h, h, h, h⟩) σ h0 y hy
  -- a thread cap of `σ` survives unless it sat in `sl`
  have hkeep : ∀ t, HasTC σ t → (∀ s, s ≠ sl → SInvU.capAt σ s ≠ some (.threadCap t)) →
      SInvU.capAt σ sl = some (.threadCap t) → c ≠ .threadCap t →
      (t ∉ K ∧ ∀ y, σ.kheap t = some (.tcb y) → ¬ liveSt y.tcbState) := by
    intro t _ hno hsl' hc
    rcases hs hσ t hsl' with e | ⟨s, hs1, hs2⟩ | h
    · exact absurd e hc
    · exact absurd hs2 (hno s hs1)
    · exact h
  have hsurv : ∀ t, HasTC σ t → ¬ (t ∉ K ∧ ∀ y, σ.kheap t = some (.tcb y) → ¬ liveSt y.tcbState) →
      HasTC y.2 t := by
    intro t ⟨s, hs0⟩ hn
    by_cases es : s = sl
    · subst es
      rcases hsl with e | e
      · exact ⟨s, e ▸ hs0⟩
      · by_cases hc : c = .threadCap t
        · exact ⟨s, hc ▸ e⟩
        · by_cases hex : ∃ s', s' ≠ s ∧ SInvU.capAt σ s' = some (.threadCap t)
          · obtain ⟨s', h1', h2'⟩ := hex
            exact ⟨s', (hne s' h1').trans h2'⟩
          · exact absurd (hkeep t ⟨s, hs0⟩ (fun s' h1' h2' => hex ⟨s', h1', h2'⟩) hs0 hc) hn
    · exact ⟨s, (hne s es).trans hs0⟩
  refine ⟨fun t x hx hl => ?_, fun t ht => hsurv t (hσ.2 t ht) fun h => h.1 ht⟩
  obtain ⟨y0, hy0, e⟩ := h1 t x hx
  have hl0 : liveSt y0.tcbState := e ▸ hl
  exact hsurv t (hσ.1 t y0 hy0 hl0) fun h => h.2 y0 hy0 hl0

/-- `set_cap` over a slot holding no thread cap. -/
theorem il_setCap_nt (c : Cap) (sl : CslotPtr) (σ : State Unit)
    (h : ∀ t, SInvU.capAt σ sl ≠ some (.threadCap t)) : IKp (IL K) σ (setCap (Z := Unit) c sl) :=
  il_setCap_p c sl σ fun _ => tcSafe_of_not h

/-! ## `cap_insert` -/

theorem isUntypedCap_nt {c : Cap} (h : isUntypedCap c) (t : ObjRef) : c ≠ .threadCap t := by
  rintro rfl; simp [isUntypedCap] at h

/-- **`cap_insert`**: the destination is asserted null; `set_untyped_cap_as_full`
rewrites the source's untyped cap. -/
theorem il_capInsert (newCap : Cap) (src dest : CslotPtr) : ILK K (capInsert (Z := Unit) newCap src dest) := by
  intro σ hσ x hx
  unfold capInsert at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨srcCap, s1⟩ := y1
  simp only at e1 hc1; subst s1
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨e3, hc3⟩ := SInvU.getCap_capAt hy3
  obtain ⟨oldCap, s3⟩ := y3
  simp only at e3 hc3; subst s3
  obtain ⟨y4, ⟨ha, rfl⟩, hx⟩ := hx
  simp only at ha
  obtain ⟨y5, hy5, hx⟩ := hx
  have h5 : IL K y5.2 := by
    unfold setUntypedCapAsFull at hy5
    split at hy5
    · rename_i hu
      exact il_setCap_nt _ _ σ (fun t e => isUntypedCap_nt hu.1 t (Option.some.inj (hc1.symm.trans e)))
        hσ y5 hy5
    · exact ik_pure () σ hσ y5 hy5
  obtain ⟨y6, hy6, hx⟩ := hx
  have hd : SInvU.capAt y5.2 dest = SInvU.capAt σ dest := by
    unfold setUntypedCapAsFull at hy5
    split at hy5
    · rcases (SInvU.setCap_out hy5) with ⟨-, hne, hsl, -, -⟩
      by_cases e : dest = src
      · subst e
        rename_i hu
        have e0 : srcCap = .nullCap := Option.some.inj (hc1.symm.trans (hc3.trans (by rw [ha])))
        subst e0; simp [isUntypedCap] at hu
      · exact hne dest e
    · rw [Set.mem_singleton_iff.1 hy5]
  have h6 : IL K y6.2 := il_setCap_nt _ _ y5.2 (fun t e => by
    rw [hd, hc3, ha] at e; cases e) h5 y6 hy6
  refine (?_ : ILK K _) y6.2 h6 x hx
  repeat' (first | (with_reducible exact il_doExtendedOp _) | ik_step0 | ik_unfold)

/-! ## `empty_slot` of a slot holding no thread cap -/

theorem il_emptySlot_p (slot : CslotPtr) (info : Cap) (σ : State Unit)
    (h : ∀ t, SInvU.capAt σ slot ≠ some (.threadCap t)) (hp : ILK K (postCapDeletion (Z := Unit) info)) : IKp (IL K) σ (emptySlot (Z := Unit) slot info) := by
  unfold emptySlot
  intro hσ x hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨c, s1⟩ := y1
  simp only at e1 hc1; subst s1
  dsimp only at hx
  split at hx
  · exact ik_pure () σ hσ x hx
  · have hQ : ∀ s : State Unit, (IL K s ∧ s.kheap = σ.kheap) → IKp (IL K) s (setCap (Z := Unit) .nullCap slot) :=
      fun s hs => il_setCap_nt _ _ s (fun t e => h t (by rw [← e]; unfold SInvU.capAt; rw [hs.2]))
    refine (?_ : HK (fun s => IL K s ∧ s.kheap = σ.kheap) (IL K) _) σ ⟨hσ, rfl⟩ x hx
    repeat' (first
      | (exact fun s hs => ikp_bind (hQ s hs) (fun _ => hp) hs.1)
      | (refine hk_bind (hk_of_ik (by repeat' (first | ik_step0 | ik_unfold | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)))) fun _ => ?_))

end W

/-! ## The automation -/

set_option maxErrors 2000

macro "il_side" : tactic => `(tactic| first
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro _ h; cases h; done)
  | (intro _ h; cases h; rfl)
  | (intro _ _ h; cases h; done)
  | (intro old hty; exact SInvU.cv_noCap (fun _ _ h => by cases h) (fun _ h => by cases h) hty)
  | (intro h; cases h; done)
  | (intro _; first | assumption | (simp; done) | (exact List.mem_cons_of_mem _ (by assumption)) | (simp_all; done)))

syntax "il_leaf" : tactic
macro_rules | `(tactic| il_leaf) => `(tactic| fail "no il_leaf")

macro "il_auto" : tactic => `(tactic| repeat' (first | il_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_doMachineOp _)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_doExtendedOp _)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_setObject _ _ ?_ ?_) <;> il_side))
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setSimpleKo _ _ _)
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_threadSet _ _ ?_ ?_) <;> il_side))
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archThreadSet _ _)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_asUser _ _)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setMrs _ _ _)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_capInsert _ _ _)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setThreadStateAct _)
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_optionUpdateThread _ _ _ ?_ ?_) <;> intro _ _ <;> rfl))
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_setThreadState _ _ ?_); il_side))

/-! ## Reads adding a thread to `K` -/

theorem ikp_ilcons {K : List ObjRef} {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α}
    {x : Tcb} (hx : σ.kheap t = some (.tcb x)) (hl : liveSt x.tcbState) (hm : ILK (t :: K) m) :
    IKp (IL K) σ m :=
  fun hσ y hy => il_tail (hm σ (il_consR hσ hx hl) y hy)

theorem liveSt_eq {a b : ThreadState} (h : a = b) (hb : liveSt b) : liveSt a := h ▸ hb

/-- A state read: a live state adds the thread to `K` (`True.intro` checks liveness at once). -/
macro "il_rds" : tactic => `(tactic| (show IK _ (getThreadState (Z := Unit) _ >>= _); unfold getThreadState; refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hs : x.tcbState <;> (try dsimp only) <;> first | (refine ikp_ilcons hx (liveSt_eq hs True.intro) ?_) | (refine ikp_of_ik ?_ σ)))

/-- `il_auto` with state reads (`il_rds`) and explicit `if` splits (nq2_auto's shape). -/
macro "il2_auto" : tactic => `(tactic| repeat' (first | il_leaf | (with_reducible exact ik_fail_bind) | il_rds | (with_reducible apply ike_ite) | (with_reducible apply ike_whenE) | (with_reducible apply ike_unlessE) | (with_reducible apply ike_liftE) | (show IK _ (ite _ _ _); split <;> try (rename_i hsplit; simp at hsplit; done)) | (show IK _ (ite _ _ _ >>= _); split <;> try (rename_i hsplit; simp at hsplit; done)) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (exfalso; contradiction)))

end

end Fl4Proofs.P3.SInv
