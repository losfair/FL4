/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sb1; KENTRY-PLAN off1's R5):
**the SC↔TCB binding as a carried spec invariant: definitions and the frame kit**
(spec side only; imports only Fl4Spec via SpecInvNativeScopeT, outside the JAtZ cone).

* `ScBackS` is SpecFinOut's `Sched.ScBack` restated over Fl4Spec only (the
  bridge `scBackS_iff` lives outside this closure): every TCB's SC exists, is
  bound back to it, and has refills when sporadic or active.
* `ScFwd` is the converse: every SC's `scTcb = some u` names a TCB whose
  `tcbSchedContext` is that SC. `ScSym := ScBackS ∧ ScFwd` is l4v's `sym_refs`
  restricted to the SC/TCB binding (`tcb_sched_context` / `sc_tcb`, with
  `valid_objs`' existence of the referenced objects).
* `RNE` (l4v `valid_sched_context`'s refill clause, `valid_refills` of active
  SCs): every SC that is sporadic or active has a refill. It is carried with
  `ScSym` because binding an unbound SC (bind, donation) would otherwise create
  an `ScBack` binding to an SC without refills. `ScInv := ScSym ∧ RNE`.
* The frame: `BR h h'` (binding view kept: the same TCB / SC addresses, the same
  `tcbSchedContext` / `scTcb`, refills kept non-empty, the refill clause kept).
  `ScInv` depends only on the heap and is kept along `BR` (`scInv_of_br`).
  `SBK h0 m := IK (BRs h0) m` is the family every spec function not writing a
  binding (and not retyping or detyping) satisfies; `sik_of_sbk` lifts it to
  `IK ScInv`.
* Leaves: `sb_setObject_p` (state-pinned: the old object at the address agrees
  with the new one in kind and binding), `sb_setSimpleKo`, `sb_threadSet` (an
  update keeping `tcbSchedContext`), `sb_archThreadSet`, `sb_asUser`,
  `sb_setMrs`, `sb_setCap`, `sb_updateSchedContext` (an update keeping `scKeep`),
  `sb_setThreadState`, `sb_optionUpdateThread`.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- The refill clause of `ScBack`: a sporadic or active SC has a refill. -/
def rneQ (y : SchedContext) : Prop := (y.scSporadic = true ∨ scActive y = true) → y.scRefills ≠ []

/-- **`Sched.ScBack` over Fl4Spec** (SpecFinOut; same statement). -/
def ScBackS (σ : State Unit) : Prop :=
  ∀ u xu c, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext = some c →
    ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scTcb = some u ∧
      ((y.scSporadic = true ∨ scActive y = true) → y.scRefills ≠ [])

/-- **The converse of `ScBack`**: an SC's TCB is a TCB bound to that SC. -/
def ScFwd (σ : State Unit) : Prop :=
  ∀ p y n u, σ.kheap p = some (.schedContext y n) → y.scTcb = some u →
    ∃ x, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some p

/-- **ScSym [J]** (l4v `sym_refs` of the SC/TCB binding with the referenced
objects' existence, `valid_objs`): `ScBack` and its converse. -/
def ScSym (σ : State Unit) : Prop := ScBackS σ ∧ ScFwd σ

/-- **RNE [J]** (l4v `valid_sched_context` / `valid_refills`): every sporadic or
active SC has a refill. -/
def RNE (σ : State Unit) : Prop := ∀ p y n, σ.kheap p = some (.schedContext y n) → rneQ y

/-- **The carried invariant.** -/
def ScInv (σ : State Unit) : Prop := ScSym σ ∧ RNE σ

theorem ScInv.sym {σ : State Unit} (h : ScInv σ) : ScSym σ := h.1
theorem ScInv.back {σ : State Unit} (h : ScInv σ) : ScBackS σ := h.1.1
theorem ScInv.fwd {σ : State Unit} (h : ScInv σ) : ScFwd σ := h.1.2

/-! ## The binding frame -/

/-- What an SC update keeps. -/
def scKeep (y y' : SchedContext) : Prop :=
  y'.scTcb = y.scTcb ∧ (y.scRefills ≠ [] → y'.scRefills ≠ []) ∧ (rneQ y → rneQ y')

theorem scKeep_of {y y' : SchedContext} (h1 : y'.scTcb = y.scTcb) (h2 : y'.scRefills = y.scRefills)
    (h3 : y'.scSporadic = y.scSporadic) (h4 : y'.scRefillMax = y.scRefillMax) : scKeep y y' := by
  refine ⟨h1, fun h => by rw [h2]; exact h, fun h ho => ?_⟩
  rw [h2]; refine h ?_
  simpa [scActive, h3, h4] using ho

theorem scKeep_ne {y y' : SchedContext} (h1 : y'.scTcb = y.scTcb) (h2 : y'.scRefills ≠ []) : scKeep y y' :=
  ⟨h1, fun _ => h2, fun _ _ => h2⟩

theorem scKeep_refl (y : SchedContext) : scKeep y y := ⟨rfl, id, id⟩

theorem scKeep_trans {y1 y2 y3 : SchedContext} (h1 : scKeep y1 y2) (h2 : scKeep y2 y3) : scKeep y1 y3 :=
  ⟨h2.1.trans h1.1, fun h => h2.2.1 (h1.2.1 h), fun h => h2.2.2 (h1.2.2 h)⟩

/-- **The binding frame** on heaps. -/
structure BR (h h' : KHeap) : Prop where
  tcb : ∀ p x, h p = some (.tcb x) → ∃ x', h' p = some (.tcb x') ∧ x'.tcbSchedContext = x.tcbSchedContext
  tcb' : ∀ p x', h' p = some (.tcb x') → ∃ x, h p = some (.tcb x)
  sc : ∀ p y n, h p = some (.schedContext y n) → ∃ y' n', h' p = some (.schedContext y' n') ∧ scKeep y y'
  sc' : ∀ p y' n', h' p = some (.schedContext y' n') → ∃ y n, h p = some (.schedContext y n)

theorem BR.refl (h : KHeap) : BR h h :=
  ⟨fun _ x hx => ⟨x, hx, rfl⟩, fun _ x hx => ⟨x, hx⟩, fun _ y n hy => ⟨y, n, hy, scKeep_refl y⟩,
    fun _ y n hy => ⟨y, n, hy⟩⟩

theorem BR.trans {h1 h2 h3 : KHeap} (a : BR h1 h2) (b : BR h2 h3) : BR h1 h3 := by
  refine ⟨fun p x hx => ?_, fun p x hx => ?_, fun p y n hy => ?_, fun p y n hy => ?_⟩
  · obtain ⟨x2, h2x, e2⟩ := a.tcb p x hx
    obtain ⟨x3, h3x, e3⟩ := b.tcb p x2 h2x
    exact ⟨x3, h3x, e3.trans e2⟩
  · obtain ⟨x2, h2x⟩ := b.tcb' p x hx; exact a.tcb' p x2 h2x
  · obtain ⟨y2, n2, h2y, k2⟩ := a.sc p y n hy
    obtain ⟨y3, n3, h3y, k3⟩ := b.sc p y2 n2 h2y
    exact ⟨y3, n3, h3y, scKeep_trans k2 k3⟩
  · obtain ⟨y2, n2, h2y⟩ := b.sc' p y n hy; exact a.sc' p y2 n2 h2y

/-- **`ScInv` is kept along the frame.** -/
theorem scInv_of_br {σ σ' : State Unit} (hI : ScInv σ) (hb : BR σ.kheap σ'.kheap) : ScInv σ' := by
  obtain ⟨⟨hB, hF⟩, hR⟩ := hI
  refine ⟨⟨fun u xu c hk hc => ?_, fun p y n u hk hu => ?_⟩, fun p y n hk => ?_⟩
  · obtain ⟨x0, hx0⟩ := hb.tcb' u xu hk
    obtain ⟨x1, hx1, e1⟩ := hb.tcb u x0 hx0
    rw [hk] at hx1; cases hx1
    obtain ⟨y, k, hky, hyt, -⟩ := hB u x0 c hx0 (by rw [← e1]; exact hc)
    obtain ⟨y', n', hy', k1, -, k3⟩ := hb.sc c y k hky
    exact ⟨y', n', hy', by rw [k1, hyt], k3 (hR c y k hky)⟩
  · obtain ⟨y0, n0, hy0⟩ := hb.sc' p y n hk
    obtain ⟨y1, n1, hy1, k1, -⟩ := hb.sc p y0 n0 hy0
    rw [hk] at hy1; cases hy1
    obtain ⟨x, hx, hxc⟩ := hF p y0 n0 u hy0 (by rw [← k1]; exact hu)
    obtain ⟨x', hx', e⟩ := hb.tcb u x hx
    exact ⟨x', hx', by rw [e]; exact hxc⟩
  · obtain ⟨y0, n0, hy0⟩ := hb.sc' p y n hk
    obtain ⟨y1, n1, hy1, -, -, k3⟩ := hb.sc p y0 n0 hy0
    rw [hk] at hy1; cases hy1
    exact k3 (hR p y0 n0 hy0)

/-- An object replaced by one of the same kind and binding. -/
def ObjKeep (old : Option KernelObject) (o : KernelObject) : Prop :=
  (∀ x, old = some (.tcb x) → ∃ x', o = .tcb x' ∧ x'.tcbSchedContext = x.tcbSchedContext) ∧
  (∀ x', o = .tcb x' → ∃ x, old = some (.tcb x)) ∧
  (∀ y n, old = some (.schedContext y n) → ∃ y' n', o = .schedContext y' n' ∧ scKeep y y') ∧
  (∀ y' n', o = .schedContext y' n' → ∃ y n, old = some (.schedContext y n))

theorem objKeep_tcb {x x' : Tcb} (e : x'.tcbSchedContext = x.tcbSchedContext) :
    ObjKeep (some (.tcb x)) (.tcb x') := by
  unfold ObjKeep
  refine ⟨fun _ h => ?_, fun _ _ => ⟨x, rfl⟩, fun _ _ h => ?_, fun _ _ h => ?_⟩
  · cases h; exact ⟨x', rfl, e⟩
  · cases h
  · cases h

theorem objKeep_sc {y y' : SchedContext} {n : Nat} (k : scKeep y y') :
    ObjKeep (some (.schedContext y n)) (.schedContext y' n) := by
  unfold ObjKeep
  refine ⟨fun _ h => ?_, fun _ h => ?_, fun _ _ h => ?_, fun _ _ _ => ⟨y, n, rfl⟩⟩
  · cases h
  · cases h
  · cases h; exact ⟨y', n, rfl, k⟩

theorem objKeep_other {old o : KernelObject} (h1 : ∀ x, old ≠ .tcb x) (h2 : ∀ y n, old ≠ .schedContext y n)
    (h1' : ∀ x, o ≠ .tcb x) (h2' : ∀ y n, o ≠ .schedContext y n) : ObjKeep (some old) o := by
  unfold ObjKeep
  exact ⟨fun x h => absurd (Option.some.inj h) (h1 x), fun x h => absurd h (h1' x),
    fun y n h => absurd (Option.some.inj h) (h2 y n), fun y n h => absurd h (h2' y n)⟩

theorem br_update {h : KHeap} {p : ObjRef} {o : KernelObject} (hk : ObjKeep (h p) o) :
    BR h (Function.update h p (some o)) := by
  obtain ⟨k1, k2, k3, k4⟩ := hk
  refine ⟨fun q x hx => ?_, fun q x hx => ?_, fun q y n hy => ?_, fun q y n hy => ?_⟩
  · by_cases e : q = p
    · subst e
      obtain ⟨x', rfl, ex⟩ := k1 x hx
      exact ⟨x', by simp, ex⟩
    · exact ⟨x, by rw [Function.update_of_ne e]; exact hx, rfl⟩
  · by_cases e : q = p
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hx
      exact k2 x hx
    · rw [Function.update_of_ne e] at hx; exact ⟨x, hx⟩
  · by_cases e : q = p
    · subst e
      obtain ⟨y', n', rfl, ky⟩ := k3 y n hy
      exact ⟨y', n', by simp, ky⟩
    · exact ⟨y, n, by rw [Function.update_of_ne e]; exact hy, scKeep_refl y⟩
  · by_cases e : q = p
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hy
      exact k4 y n hy
    · rw [Function.update_of_ne e] at hy; exact ⟨y, n, hy⟩

/-- A simple-type object (endpoint, notification, reply) is no TCB and no SC. -/
theorem simple_not {o : KernelObject} (h : isSimpleType o) : (∀ x, o ≠ .tcb x) ∧ (∀ y n, o ≠ .schedContext y n) := by
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  refine ⟨fun x e => ?_, fun y n e => ?_⟩ <;> subst e
  · rcases h with h | h | h <;> simp [aType] at h
  · rcases h with h | h | h <;> simp only [aType] at h <;> split_ifs at h <;> cases h

theorem objKeep_simple {old o : KernelObject} (h : isSimpleType old) (ht : aType old = aType o) :
    ObjKeep (some old) o := by
  have h' : isSimpleType o := by unfold isSimpleType; rw [← ht]; exact h
  exact objKeep_other (simple_not h).1 (simple_not h).2 (simple_not h').1 (simple_not h').2

/-! ## The family -/

/-- The frame from a fixed heap. -/
def BRs (h0 : KHeap) (s : State Unit) : Prop := BR h0 s.kheap

/-- **The frame family**: every outcome keeps the binding view of the start heap. -/
abbrev SBK (h0 : KHeap) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (BRs h0) m
abbrev SBKE (h0 : KHeap) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (BRs h0) m

/-- The invariant family. -/
abbrev SIK {α : Type} (m : NonDet (State Unit) α) : Prop := IK ScInv m
abbrev SIKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE ScInv m

theorem sik_of_sbk {α : Type} {m : NonDet (State Unit) α} (h : ∀ h0, SBK h0 m) : SIK m :=
  fun σ hσ x hx => scInv_of_br hσ (h σ.kheap σ (BR.refl _) x hx)

theorem sike_of_sbke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ h0, SBKE h0 m) : SIKE m :=
  sik_of_sbk h

/-- From a one-step frame. -/
theorem sbk_of_step {h0 : KHeap} {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ σ x, x ∈ (m σ).1 → BR σ.kheap x.2.kheap) : SBK h0 m :=
  fun σ hσ x hx => BR.trans hσ (h σ x hx)

theorem br_mem_of_sbk {α : Type} {m : NonDet (State Unit) α} (h : ∀ h0, SBK h0 m) {σ : State Unit}
    {x : α × State Unit} (hx : x ∈ (m σ).1) : BR σ.kheap x.2.kheap :=
  h σ.kheap σ (BR.refl _) x hx

/-! ## Membership of the heap writes -/

theorem mem_setObject {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ old, σ.kheap p = some old ∧ aType old = aType o ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨y1, hk, hty, rfl⟩

theorem mem_updateSchedContext {p : ObjRef} {f : SchedContext → SchedContext} {σ : State Unit}
    {x : Unit × State Unit} (hx : x ∈ (updateSchedContext (Z := Unit) p f σ).1) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some (.schedContext (f y) n)) } := by
  unfold updateSchedContext at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨o, y2⟩ := y
  simp only at hk hs; subst y2
  cases o with
  | schedContext sc n =>
    obtain ⟨old, h1, -, e⟩ := mem_setObject hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-! ## The leaves -/

section Leaves
variable {h0 : KHeap}

theorem sb_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ old, σ.kheap p = some old → aType old = aType o → ObjKeep (some old) o) :
    IKp (BRs h0) σ (setObject (Z := Unit) p o) := by
  intro hσ x hx
  obtain ⟨old, hk, hty, e⟩ := mem_setObject hx
  show BR h0 x.2.kheap
  rw [e]
  have hk' : ObjKeep (σ.kheap p) o := by rw [hk]; exact ho old hk hty
  exact BR.trans hσ (br_update hk')

/-- An arch object written over an object of the same type (by `setObject`'s
type assertion, an arch object). -/
theorem sb_setObject_arch (p : ObjRef) (ao : ArchKernelObj) : SBK h0 (setObject (Z := Unit) p (.archObj ao)) :=
  fun σ => sb_setObject_p p _ σ fun old _ hty => by
    refine objKeep_other (fun x h => ?_) (fun y n h => ?_) (fun _ h => by cases h) (fun _ _ h => by cases h)
    · subst h; simp [aType] at hty
    · subst h; simp only [aType] at hty; split_ifs at hty <;> cases hty

theorem sb_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    SBK h0 (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  refine sb_setObject_p p (f e) σ (fun old hk' hty => ?_) hσ x hx
  rw [hk] at hk'; cases hk'
  exact objKeep_simple hsimp hty

theorem sb_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) :
    SBK h0 (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => sb_setObject_p _ _ σ fun old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact objKeep_tcb (hf x)

theorem sb_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : SBK h0 (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => sb_setObject_p _ _ σ fun old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact objKeep_tcb rfl

theorem sb_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : SBK h0 (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (sb_setObject_p _ _ σ fun old hk _ => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hk; cases hk
  exact objKeep_tcb rfl

macro "sb_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold))

theorem sb_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : SBK h0 (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (sb_setObject_p _ _ σ fun old hk _ => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hk; cases hk
    exact objKeep_tcb rfl
  · sb_mach

theorem sb_setCap (c : Cap) (sl : CslotPtr) : SBK h0 (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst y2
  have hok : ∀ o', ObjKeep (some obj) o' → x ∈ ((setObject (Z := Unit) o o') σ).1 → BRs h0 x.2 :=
    fun o' hk' hx' => sb_setObject_p o o' σ (fun old hk2 _ => by rw [hk] at hk2; cases hk2; exact hk') hσ x hx'
  cases obj with
  | cnode sz cn =>
    dsimp only at hx
    split_ifs at hx
    · obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hz] at hx
      exact hok _ (objKeep_other (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
          (fun _ _ h => by cases h)) hx
    · obtain ⟨z, hz, -⟩ := hx; exact hz.elim
  | tcb t =>
    dsimp only at hx
    split_ifs at hx <;> obtain ⟨z, hz, hx⟩ := hx <;> first
      | exact hz.elim
      | (rw [Set.mem_singleton_iff.1 hz] at hx; refine hok _ ?_ hx; exact objKeep_tcb rfl)
  | _ => dsimp only at hx; obtain ⟨z, hz, -⟩ := hx; exact hz.elim

theorem sb_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, scKeep y (f y)) :
    SBK h0 (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, hk, e⟩ := mem_updateSchedContext hx
  show BR h0 x.2.kheap
  rw [e]
  have hk' : ObjKeep (σ.kheap p) (.schedContext (f y) n) := by rw [hk]; exact objKeep_sc (hf y)
  exact BR.trans hσ (br_update hk')

theorem sb_setThreadState (t : ObjRef) (ts : ThreadState) : SBK h0 (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (sb_threadSet _ _ fun _ => rfl) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold)

theorem sb_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbSchedContext = x.tcbSchedContext) : SBK h0 (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact sb_threadSet _ _ (h _)

end Leaves

/-! ## `sb_auto` -/

/-- The side conditions of the leaves. -/
macro "sb_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro _ h; exact h)
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro _; exact scKeep_of rfl rfl rfl rfl)
  | (intro _; exact scKeep_ne rfl (List.cons_ne_nil _ _))
  | (intro _; exact scKeep_ne rfl (by simp [scRefillsUpdate]))
  | (intro _; exact scKeep_ne rfl (by simp)))

syntax "sb_leaf" : tactic
macro_rules | `(tactic| sb_leaf) => `(tactic| fail "no sb_leaf")

macro "sb_auto" : tactic => `(tactic| repeat' (first | sb_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| sb_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); sb_side))
macro_rules | `(tactic| sb_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); sb_side))
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setSimpleKo _ _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setObject_arch _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| ((with_reducible refine sb_threadSet _ _ ?_); sb_side))
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archThreadSet _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_asUser _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setMrs _ _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setCap _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| ((with_reducible refine sb_updateSchedContext _ _ ?_); sb_side))
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setThreadState _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| ((with_reducible refine sb_optionUpdateThread _ _ _ ?_); sb_side))

end

end Fl4Proofs.P3.SInvB
