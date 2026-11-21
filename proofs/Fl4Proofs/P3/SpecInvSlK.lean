/-
P3 (DESIGN.md §9), invariant line G1 (sl1): **ScLive carried, the typed form
and its frame kit** (spec side only, outside the JAtZ cone).

sb2's `ScLive [J]` (SpecInvSbE: every bound TCB or SC is named by some cap, or
lies outside every cap's range; l4v `if_live_then_nonz_cap` at bound objects and
`valid_global_refs`) is carried in a typed form, il1's IL pattern:

* `liveO o`: a TCB with an SC (`tcb_sched_context ≠ None`), or an SC with a TCB,
  a notification or a reply stack (`sc_tcb ≠ None ∨ sc_ntfn ≠ None ∨ sc_replies ≠
  []`): the binding part of l4v's `live`. The SC's notification and reply stack
  are counted because `maybe_donate_sc` donates a notification's SC and
  `reply_remove` the SC of a reply stack, either possibly bound to no TCB.
* `NCap p c`: `c` is a thread cap or an SC cap to `p` (the cap typed, as il1's
  `HasTC`: every removal of another kind of cap is then free). `HasN σ p`.
* **`ScLiveT I σ`** (`I = (idle thread, idle SC)`, fixed parameters): every live
  object other than `I.1` / `I.2` is named by a thread or SC cap.
* Carried form **`SL I K σ := ScLiveT I σ ∧ ∀ p ∈ K, HasN σ p`** (`K`: objects
  known to be named: read live, or named by a decoded cap). It reads the heap only.
  The idle thread / idle SC are outside every cap's range (sg1's `IdleOutV`, and
  `IrqOutV (fun _ => σ.idleSc)`): SpecInvSlT turns `SL` into `ScLive`.
* Leaves: `sl_update` (one heap write keeping the caps, a new live object only at
  a live one or at `K`), `sl_setObject_p`, `setObject` / `set_simple_ko` /
  `thread_set` / `arch_thread_set` / `as_user` / `set_mrs` /
  `update_sched_context` (keeping liveness) / `set_thread_state` /
  `option_update_thread`, machine and extended ops; **`sl_setCap_p`** with
  `NSafe` (the slot's old cap is no thread/SC cap, or the same, or another slot
  names its object, or the object is not live, not idle, not in `K`);
  `sl_capInsert`; `sl_emptySlot_p`.
-/
import Fl4Proofs.P3.SpecInvNtfnQL
import Fl4Proofs.P3.SpecInvSbK
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- The binding part of l4v's `live` for an SC. -/
def scLv (y : SchedContext) : Prop := y.scTcb ≠ none ∨ y.scNtfn ≠ none ∨ y.scReplies ≠ []

/-- The binding part of l4v's `live`: a TCB with an SC, an SC with a TCB, a
notification or replies. -/
def liveO : KernelObject → Prop
  | .tcb x => x.tcbSchedContext ≠ none
  | .schedContext y _ => scLv y
  | _ => False

/-- A thread cap or an SC cap to `p`. -/
def NCap (p : ObjRef) : Cap → Prop
  | .threadCap t => t = p
  | .schedContextCap c _ => c = p
  | _ => False

/-- Some slot holds a thread or SC cap to `p`. -/
def HasN (σ : State Unit) (p : ObjRef) : Prop := ∃ s c, SInvU.capAt σ s = some c ∧ NCap p c

/-- **The typed ScLive** (`I`: the idle thread and the idle SC). -/
def ScLiveT (I : ObjRef × ObjRef) (σ : State Unit) : Prop :=
  ∀ p o, σ.kheap p = some o → liveO o → p ≠ I.1 → p ≠ I.2 → HasN σ p

/-- Named by a thread / SC cap, or idle. -/
def Nm (I : ObjRef × ObjRef) (σ : State Unit) (p : ObjRef) : Prop := HasN σ p ∨ p = I.1 ∨ p = I.2

/-- **The carried form.** -/
def SL (I : ObjRef × ObjRef) (K : List ObjRef) (σ : State Unit) : Prop := ScLiveT I σ ∧ ∀ p ∈ K, Nm I σ p

abbrev SLK (I : ObjRef × ObjRef) (K : List ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (SL I K) m
abbrev SLKE (I : ObjRef × ObjRef) (K : List ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  IKE (SL I K) m

theorem ncap_objRefs {p : ObjRef} {c : Cap} (h : NCap p c) : p ∈ objRefs c := by
  cases c <;> simp_all [NCap, objRefs]

theorem hasN_of_tc {σ : State Unit} {t : ObjRef} (h : HasTC σ t) : HasN σ t := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, _, hs, rfl⟩

theorem sl_nil_iff {I : ObjRef × ObjRef} (σ : State Unit) : SL I [] σ ↔ ScLiveT I σ :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ h => by simp at h⟩⟩

theorem sl_mono {I : ObjRef × ObjRef} {K K' : List ObjRef} {σ : State Unit} (h : SL I K σ)
    (hK : ∀ u ∈ K', u ∈ K) : SL I K' σ :=
  ⟨h.1, fun u hu => h.2 u (hK u hu)⟩

theorem sl_tail {I : ObjRef × ObjRef} {K : List ObjRef} {σ : State Unit} {t : ObjRef} (h : SL I (t :: K) σ) :
    SL I K σ :=
  sl_mono h fun _ h => List.mem_cons_of_mem _ h

theorem sl_cons {I : ObjRef × ObjRef} {K : List ObjRef} {σ : State Unit} (h : SL I K σ) {t : ObjRef}
    (ht : Nm I σ t) : SL I (t :: K) σ := by
  refine ⟨h.1, fun u hu => ?_⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ht
  · exact h.2 u hu

theorem nm_of_live {I : ObjRef × ObjRef} {σ : State Unit} (h : ScLiveT I σ) {t : ObjRef}
    {o : KernelObject} (ho : σ.kheap t = some o) (hl : liveO o) : Nm I σ t := by
  by_cases h1 : t = I.1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : t = I.2
  · exact Or.inr (Or.inr h2)
  exact Or.inl (h t o ho hl h1 h2)

/-- A live object joins `K`. -/
theorem sl_consL {I : ObjRef × ObjRef} {K : List ObjRef} {σ : State Unit} (h : SL I K σ) {t : ObjRef}
    {o : KernelObject} (ho : σ.kheap t = some o) (hl : liveO o) : SL I (t :: K) σ :=
  sl_cons h (nm_of_live h.1 ho hl)

theorem hasN_of_nm {I : ObjRef × ObjRef} {σ : State Unit} {t : ObjRef} (h : Nm I σ t) (h1 : t ≠ I.1)
    (h2 : t ≠ I.2) : HasN σ t := by
  rcases h with h | e | e
  · exact h
  · exact absurd e h1
  · exact absurd e h2

/-- `SL` reads the heap only. -/
theorem sl_of_kheap {I : ObjRef × ObjRef} {K : List ObjRef} {σ σ' : State Unit} (e : σ'.kheap = σ.kheap)
    (h : SL I K σ) : SL I K σ' := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by
    funext sl; unfold SInvU.capAt; rw [e]
  have hT : ∀ t, HasN σ' t ↔ HasN σ t := fun t => by unfold HasN; rw [hc]
  exact ⟨fun t o ht hl h1 h2 => (hT t).2 (h.1 t o (e ▸ ht) hl h1 h2), fun t ht => (h.2 t ht).imp_left (hT t).2⟩

/-! ## One heap write -/

/-- When a heap write at `p` (old `o0`, new `o`) keeps `SL I K`: the caps are
kept, a live new object was live before or is in `K`. -/
def SLOK (K : List ObjRef) (p : ObjRef) (o0 o : KernelObject) : Prop :=
  SInvU.capView o = SInvU.capView o0 ∧ (liveO o → p ∈ K ∨ liveO o0)

theorem sl_update {I : ObjRef × ObjRef} {K : List ObjRef} {σ : State Unit} {p : ObjRef} {o0 o : KernelObject}
    (h : SL I K σ) (hp : σ.kheap p = some o0) (hok : SLOK K p o0 o) :
    SL I K { σ with kheap := Function.update σ.kheap p (some o) } := by
  have hc : SInvU.capAt { σ with kheap := Function.update σ.kheap p (some o) } = SInvU.capAt σ :=
    congrArg (fun w : SInvU.UView => w.2.1) (SInvU.uV_update hp hok.1)
  have hT : ∀ t, HasN { σ with kheap := Function.update σ.kheap p (some o) } t ↔ HasN σ t :=
    fun t => by unfold HasN; rw [hc]
  refine ⟨fun t y ht hl h1 h2 => (hT t).2 ?_, fun t ht => (h.2 t ht).imp_left (hT t).2⟩
  dsimp only at ht
  rw [Function.update_apply] at ht
  split_ifs at ht with e
  · subst e
    cases Option.some.inj ht
    rcases hok.2 hl with hK | hl0
    · exact hasN_of_nm (h.2 t hK) h1 h2
    · exact h.1 t o0 hp hl0 h1 h2
  · exact h.1 t y ht hl h1 h2

theorem slok_of {K : List ObjRef} {p : ObjRef} {o0 o : KernelObject} (hc : SInvU.capView o = SInvU.capView o0)
    (hl : liveO o → liveO o0) : SLOK K p o0 o :=
  ⟨hc, fun h => Or.inr (hl h)⟩

section W
variable {I : ObjRef × ObjRef} {K : List ObjRef}

theorem sl_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : SL I K σ → ∀ o0, σ.kheap p = some o0 → aType o0 = aType o → SLOK K p o0 o) :
    IKp (SL I K) σ (setObject (Z := Unit) p o) := by
  intro hσ x hx
  obtain ⟨old, hk, hty, e⟩ := SInvB.mem_setObject hx
  rw [e]
  exact sl_update hσ hk (ho hσ old hk hty)

/-- `setObject` of an object that is not live, of the old object's type, with the old caps. -/
theorem sl_setObject (p : ObjRef) (o : KernelObject) (h1 : ¬ liveO o)
    (ho : ∀ old, aType old = aType o → SInvU.capView o = SInvU.capView old) :
    SLK I K (setObject (Z := Unit) p o) :=
  fun σ => sl_setObject_p p o σ fun _ o0 _ hty => ⟨ho o0 hty, fun h => absurd h h1⟩

theorem simple_notCnode {o : KernelObject} (h : isSimpleType o) : ∀ sz cs, o ≠ .cnode sz cs := by
  intro sz cs e; subst e
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> simp only [aType] at h <;> split_ifs at h <;> cases h

theorem simple_notLive {o : KernelObject} (h : isSimpleType o) : ¬ liveO o := by
  obtain ⟨h1, h2⟩ := SInvB.simple_not h
  cases o with
  | tcb x => exact absurd rfl (h1 x)
  | schedContext y n => exact absurd rfl (h2 y n)
  | _ => exact id

theorem sl_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    SLK I K (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  refine sl_setObject_p p (f e) σ (fun _ old hk' hty => ?_) hσ x hx
  rw [hk] at hk'; cases hk'
  have hs' : isSimpleType (f e) := by unfold isSimpleType; rw [← hty]; exact hsimp
  exact slok_of (SInvU.cv_noCap (simple_notCnode hs') (SInvB.simple_not hs').1 hty)
    fun h => absurd h (simple_notLive hs')

theorem sl_threadSet (f : Tcb → Tcb) (t : ObjRef) (hc : ∀ x, tcbCnodeMap (f x) = tcbCnodeMap x)
    (hs : ∀ x, (f x).tcbSchedContext ≠ none → x.tcbSchedContext ≠ none) :
    SLK I K (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => sl_setObject_p _ _ σ fun _ old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact slok_of (hc x) (hs x)

theorem sl_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : SLK I K (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => sl_setObject_p _ _ σ fun _ old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact slok_of rfl id

theorem sl_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : SLK I K (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (sl_setObject_p _ _ σ fun _ old hk _ => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hk; cases hk
  exact slok_of rfl id

theorem sl_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : SLK I K (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (sl_setObject_p _ _ σ fun _ old hk _ => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hk; cases hk
    exact slok_of rfl id
  · repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

/-- An SC update that makes no SC live. -/
theorem sl_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, scLv (f y) → scLv y) :
    SLK I K (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  exact sl_update hσ hk (slok_of rfl (hf y))

theorem sl_doMachineOp {α : Type} (mop : NonDet MachineState α) : SLK I K (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem sl_doExtendedOp (eop : DetExtMonad Unit) : SLK I K (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) _

theorem sl_setThreadStateAct (t : ObjRef) : SLK I K (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem sl_setThreadState (t : ObjRef) (ts : ThreadState) : SLK I K (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (sl_threadSet _ t (fun _ => rfl) fun _ h => h) fun _ => sl_setThreadStateAct t

theorem sl_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (hc : ∀ a x, tcbCnodeMap (fn a x) = tcbCnodeMap x)
    (hs : ∀ a x, (fn a x).tcbSchedContext ≠ none → x.tcbSchedContext ≠ none) :
    SLK I K (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact sl_threadSet _ _ (hc _) (hs _)

/-! ## `set_cap` -/

/-- `set_cap` writes no live object. -/
theorem setCap_live {c : Cap} {sl : CslotPtr} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setCap (Z := Unit) c sl σ).1) :
    ∀ p o, y.2.kheap p = some o → liveO o → ∃ o0, σ.kheap p = some o0 ∧ liveO o0 := by
  obtain ⟨oref, r⟩ := sl
  unfold setCap at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨obj, z2⟩ := z
  simp only at hk hs; subst z2
  have key : ∀ o', (liveO o' → liveO obj) → y ∈ ((setObject (Z := Unit) oref o') σ).1 →
      ∀ p o, y.2.kheap p = some o → liveO o → ∃ o0, σ.kheap p = some o0 ∧ liveO o0 := by
    intro o' hl hy' p o hp ho
    obtain ⟨old, h1, -, e⟩ := SInvB.mem_setObject hy'
    rw [e] at hp
    dsimp only at hp
    rw [Function.update_apply] at hp
    split_ifs at hp with ep
    · subst ep; cases hp; exact ⟨obj, hk, hl ho⟩
    · exact ⟨o, hp, ho⟩
  cases obj with
  | cnode sz cn =>
    dsimp only at hy
    split_ifs at hy
    · obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hz] at hy
      refine key _ ?_ hy; exact fun h => False.elim h
    · obtain ⟨z, hz, -⟩ := hy; exact hz.elim
  | tcb t =>
    dsimp only at hy
    split_ifs at hy <;> obtain ⟨z, hz, hy⟩ := hy <;> first
      | exact hz.elim
      | (rw [Set.mem_singleton_iff.1 hz] at hy; refine key _ ?_ hy; exact id)
  | _ => dsimp only at hy; obtain ⟨z, hz, -⟩ := hy; exact hz.elim

/-- When overwriting the cap in `sl` by `c` keeps `SL I K`: the old cap is no
thread/SC cap, or names the object `c` names, or another slot names its object,
or its object is not live (or idle) and not in `K`. -/
def NSafe (I : ObjRef × ObjRef) (K : List ObjRef) (σ : State Unit) (sl : CslotPtr) (c : Cap) : Prop :=
  ∀ p c0, SInvU.capAt σ sl = some c0 → NCap p c0 →
    NCap p c ∨ (∃ s c', s ≠ sl ∧ SInvU.capAt σ s = some c' ∧ NCap p c') ∨
      (p ∉ K ∧ ∀ o, σ.kheap p = some o → liveO o → p = I.1 ∨ p = I.2)

theorem nSafe_of_not {σ : State Unit} {sl : CslotPtr} {c : Cap}
    (h : ∀ p c0, SInvU.capAt σ sl = some c0 → ¬ NCap p c0) : NSafe I K σ sl c :=
  fun p c0 hc hn => absurd hn (h p c0 hc)

theorem sl_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hs : SL I K σ → NSafe I K σ sl c) :
    IKp (SL I K) σ (setCap (Z := Unit) c sl) := by
  intro hσ y hy
  obtain ⟨-, hne, hsl, -, -⟩ := SInvU.setCap_out hy
  have hlv := setCap_live hy
  -- a name of `σ` survives unless it sat in `sl`
  have hsurv : ∀ t, HasN σ t → ¬ (t ∉ K ∧ ∀ o, σ.kheap t = some o → liveO o → t = I.1 ∨ t = I.2) →
      HasN y.2 t := by
    intro t ⟨s, c0, hs0, hn0⟩ hn
    by_cases es : s = sl
    · subst es
      rcases hsl with e | e
      · exact ⟨s, c0, e ▸ hs0, hn0⟩
      · rcases hs hσ t c0 hs0 hn0 with hc | ⟨s', c', h1', h2', h3'⟩ | h
        · exact ⟨s, c, e, hc⟩
        · exact ⟨s', c', (hne s' h1').trans h2', h3'⟩
        · exact absurd h hn
    · exact ⟨s, c0, (hne s es).trans hs0, hn0⟩
  refine ⟨fun t o ht hl h1 h2 => ?_, fun t ht => ?_⟩
  swap
  · rcases hσ.2 t ht with hn | e | e
    · exact Or.inl (hsurv t hn fun h => h.1 ht)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  obtain ⟨o0, ho0, hl0⟩ := hlv t o ht hl
  refine hsurv t (hσ.1 t o0 ho0 hl0 h1 h2) fun h => ?_
  rcases h.2 o0 ho0 hl0 with e | e
  · exact h1 e
  · exact h2 e

/-- `set_cap` over a slot holding no thread / SC cap. -/
theorem sl_setCap_nt (c : Cap) (sl : CslotPtr) (σ : State Unit)
    (h : ∀ p c0, SInvU.capAt σ sl = some c0 → ¬ NCap p c0) : IKp (SL I K) σ (setCap (Z := Unit) c sl) :=
  sl_setCap_p c sl σ fun _ => nSafe_of_not h

/-! ## `cap_insert` -/

theorem isUntypedCap_nn {c : Cap} (h : isUntypedCap c) (p : ObjRef) : ¬ NCap p c := by
  cases c <;> simp_all [isUntypedCap, NCap]

/-- **`cap_insert`**: the destination is asserted null; `set_untyped_cap_as_full`
rewrites the source's untyped cap. -/
theorem sl_capInsert (newCap : Cap) (src dest : CslotPtr) : SLK I K (capInsert (Z := Unit) newCap src dest) := by
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
  have h5 : SL I K y5.2 := by
    unfold setUntypedCapAsFull at hy5
    split at hy5
    · rename_i hu
      exact sl_setCap_nt _ _ σ (fun p c0 e => by
        rw [← Option.some.inj (hc1.symm.trans e)]; exact isUntypedCap_nn hu.1 p) hσ y5 hy5
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
  have h6 : SL I K y6.2 := sl_setCap_nt _ _ y5.2 (fun p c0 e => by
    rw [hd, hc3, ha] at e; cases e; exact id) h5 y6 hy6
  refine (?_ : SLK I K _) y6.2 h6 x hx
  repeat' (first | (with_reducible exact sl_doExtendedOp _) | ik_step0 | ik_unfold)

/-! ## `empty_slot` of a slot holding no thread / SC cap -/

theorem sl_emptySlot_p (slot : CslotPtr) (info : Cap) (σ : State Unit)
    (h : ∀ p c0, SInvU.capAt σ slot = some c0 → ¬ NCap p c0) (hp : SLK I K (postCapDeletion (Z := Unit) info)) :
    IKp (SL I K) σ (emptySlot (Z := Unit) slot info) := by
  unfold emptySlot
  intro hσ x hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨c, s1⟩ := y1
  simp only at e1 hc1; subst s1
  dsimp only at hx
  split at hx
  · exact ik_pure () σ hσ x hx
  · have hQ : ∀ s : State Unit, (SL I K s ∧ s.kheap = σ.kheap) →
        IKp (SL I K) s (setCap (Z := Unit) .nullCap slot) :=
      fun s hs => sl_setCap_nt _ _ s (fun p c0 e => h p c0 (by rw [← e]; unfold SInvU.capAt; rw [hs.2]))
    refine (?_ : HK (fun s => SL I K s ∧ s.kheap = σ.kheap) (SL I K) _) σ ⟨hσ, rfl⟩ x hx
    repeat' (first
      | (exact fun s hs => ikp_bind (hQ s hs) (fun _ => hp) hs.1)
      | (refine hk_bind (hk_of_ik (by repeat' (first | ik_step0 | ik_unfold | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)))) fun _ => ?_))

end W

/-! ## The automation -/

set_option maxErrors 2000

/-- An SC field update other than the binding fields keeps `scLv`. -/
theorem scLv_keep {y y' : SchedContext} (h1 : y'.scTcb = y.scTcb) (h2 : y'.scNtfn = y.scNtfn)
    (h3 : y'.scReplies = y.scReplies) : scLv y' → scLv y := by
  unfold scLv; rw [h1, h2, h3]; exact id

/-- A reply-stack update that shrinks the empty stack to the empty stack. -/
theorem scLv_replies {g : List ObjRef → List ObjRef} (hg : g [] = []) (y : SchedContext) :
    scLv (scRepliesUpdate g y) → scLv y := by
  unfold scLv scRepliesUpdate
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr fun e => h ?_)
    dsimp only; rw [e]; exact hg

macro "sl_side" : tactic => `(tactic| first
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro _ h; exact h)
  | (intro _ h; exact absurd rfl h)
  | (intro _ h; exact scLv_keep rfl rfl rfl h)
  | (intro _; unfold scLv; simp only [scTcbUpdate, scNtfnUpdate, scRepliesUpdate, ne_eq]; intro h; tauto)
  | (exact scLv_replies rfl)
  | (intro old hty; exact SInvU.cv_noCap (fun _ _ h => by cases h) (fun _ h => by cases h) hty)
  | (intro h; exact h)
  | (exact id))

syntax "sl_leaf" : tactic
macro_rules | `(tactic| sl_leaf) => `(tactic| fail "no sl_leaf")

macro "sl_auto" : tactic => `(tactic| repeat' (first | sl_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doMachineOp _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doExtendedOp _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| sl_leaf) => `(tactic| ((with_reducible refine sl_setObject _ _ ?_ ?_) <;> sl_side))
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setSimpleKo _ _ _)
macro_rules | `(tactic| sl_leaf) => `(tactic| ((with_reducible refine sl_threadSet _ _ ?_ ?_) <;> sl_side))
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archThreadSet _ _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_asUser _ _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setMrs _ _ _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_capInsert _ _ _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setThreadStateAct _)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setThreadState _ _)
macro_rules | `(tactic| sl_leaf) => `(tactic| ((with_reducible refine sl_updateSchedContext _ _ ?_); sl_side))
macro_rules | `(tactic| sl_leaf) => `(tactic| ((with_reducible refine sl_optionUpdateThread _ _ _ ?_ ?_) <;> intro _ _ <;> first | rfl | (intro h; exact h)))

end

end Fl4Proofs.P3.SInvL
