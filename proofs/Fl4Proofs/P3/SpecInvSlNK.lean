/-
P3 (DESIGN.md §9), invariant line G1 (sl2): **NtfnScB, the notification → SC
back pointer, and its frame kit** (spec side only, outside the JAtZ cone).

`maybe_donate_sc` donates a notification's SC, which may be bound to no TCB; the
SC is live (`scLv`: `sc_ntfn ≠ None`) only if the back pointer holds. l4v gets
it from `sym_refs` of `ntfn_sc` / `sc_ntfn`. Carried here is the half that is
read:

* **`NtfnScB σ`**: a notification's SC is an SC whose notification is that
  notification. The converse half (an SC's notification points back) is not
  needed: every writer that clears a pointer reads it at the state it clears,
  and this half alone gives uniqueness (two notifications pointing to `c` would
  both be `c`'s notification), which is what the unbinding writers need.
* `NBOK o0 o`: a heap write keeping the notification's `ntfnSc` (`nscO`) and the
  SC's `scNtfn` (`scnO`), with the kind (notification / SC / other) kept.
  `nb_update`, `nb_setObject_p`, `nb_setSimpleKo_p` (state-pinned: the new
  notification's SC is the old one's), leaves `nb_setSimpleKo` (a constructor
  that is never a notification: endpoints, replies), `nb_updateSkObjRef` (a
  field update keeping `ntfnSc`), `nb_threadSet` and the TCB writers,
  `nb_updateSchedContext` (keeping `scNtfn`), `nb_setCap`, `nb_capInsert`.
* Writers read-modify-writing a notification at one state: `nb_tcbNtfnDequeue`,
  `nb_tcbNtfnAppend`, `nb_reorderNtfn`; the unbinding writers
  `nb_schedContextUnbindNtfn`, `nb_schedContextMaybeUnbindNtfn`.
-/
import Fl4Proofs.P3.SpecInvSlK
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- The SC pointer of a notification object. -/
def nscO : KernelObject → Option (Option ObjRef)
  | .notification n => some n.ntfnSc
  | _ => none

/-- The notification pointer of an SC object. -/
def scnO : KernelObject → Option (Option ObjRef)
  | .schedContext y _ => some y.scNtfn
  | _ => none

/-- **NtfnScB** (l4v `sym_refs` of `ntfn_sc` / `sc_ntfn`, the half read by
`maybe_donate_sc`): a notification's SC is an SC bound back to it. -/
def NtfnScB (σ : State Unit) : Prop :=
  ∀ n ntf c, σ.kheap n = some (.notification ntf) → ntf.ntfnSc = some c →
    ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scNtfn = some n

abbrev NBK {α : Type} (m : NonDet (State Unit) α) : Prop := IK NtfnScB m
abbrev NBKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE NtfnScB m

theorem nb_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) (h : NtfnScB σ) : NtfnScB σ' := by
  intro n ntf c hn hc
  rw [e] at hn ⊢
  exact h n ntf c hn hc

/-- Two notifications pointing to one SC are equal. -/
theorem nb_uniq {σ : State Unit} (h : NtfnScB σ) {n n' c : ObjRef} {a a' : Notification}
    (hn : σ.kheap n = some (.notification a)) (ha : a.ntfnSc = some c)
    (hn' : σ.kheap n' = some (.notification a')) (ha' : a'.ntfnSc = some c) : n' = n := by
  obtain ⟨y, k, hy, hyn⟩ := h n a c hn ha
  obtain ⟨y', k', hy', hyn'⟩ := h n' a' c hn' ha'
  rw [hy] at hy'
  simp only [Option.some.injEq, KernelObject.schedContext.injEq] at hy'
  obtain ⟨rfl, rfl⟩ := hy'
  rw [hyn] at hyn'
  exact (Option.some.inj hyn').symm

/-! ## One heap write -/

/-- A heap write keeping the notification / SC pointers (and the kinds). -/
def NBOK (o0 o : KernelObject) : Prop := nscO o = nscO o0 ∧ scnO o = scnO o0

theorem nb_update {σ : State Unit} {p : ObjRef} {o0 o : KernelObject} (h : NtfnScB σ)
    (hp : σ.kheap p = some o0) (hok : NBOK o0 o) :
    NtfnScB { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro n ntf c hn hc
  dsimp only at hn ⊢
  rw [Function.update_apply] at hn
  split_ifs at hn with en
  · subst en
    cases hn
    have h1 := hok.1
    cases o0 with
    | notification a =>
      simp only [nscO, Option.some.injEq] at h1
      obtain ⟨y, k, hy, hyn⟩ := h n a c hp (h1 ▸ hc)
      have hcn : c ≠ n := by intro e; subst e; rw [hp] at hy; cases hy
      exact ⟨y, k, by rw [Function.update_apply, if_neg hcn]; exact hy, hyn⟩
    | _ => simp [nscO] at h1
  · obtain ⟨y, k, hy, hyn⟩ := h n ntf c hn hc
    by_cases ec : c = p
    · subst ec
      rw [hy] at hp; cases hp
      have h2 := hok.2
      cases o with
      | schedContext y' k' =>
        simp only [scnO, Option.some.injEq] at h2
        exact ⟨y', k', by rw [Function.update_apply, if_pos rfl], h2.trans hyn⟩
      | _ => simp [scnO] at h2
    · exact ⟨y, k, by rw [Function.update_apply, if_neg ec]; exact hy, hyn⟩

theorem nbok_tcb (x x' : Tcb) : NBOK (.tcb x) (.tcb x') := ⟨rfl, rfl⟩

/-- The old object of a TCB write is a TCB. -/
theorem nbok_tcbA (x : Tcb) : ∀ old, aType old = aType (.tcb x) → NBOK old (.tcb x) := by
  intro old hty
  cases old with
  | tcb y => exact ⟨rfl, rfl⟩
  | cnode sz cs => simp only [aType] at hty; split_ifs at hty <;> cases hty
  | schedContext y n => simp only [aType] at hty; split_ifs at hty <;> cases hty
  | _ => simp [aType] at hty

section W

theorem nb_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ o0, σ.kheap p = some o0 → aType o0 = aType o → NBOK o0 o) :
    IKp NtfnScB σ (setObject (Z := Unit) p o) := by
  intro hσ x hx
  obtain ⟨old, hk, hty, e⟩ := SInvB.mem_setObject hx
  rw [e]
  exact nb_update hσ hk (ho old hk hty)

/-- `setObject` of an object of the old kind with the same pointers. -/
theorem nb_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ old, aType old = aType o → NBOK old o) :
    NBK (setObject (Z := Unit) p o) :=
  fun σ => nb_setObject_p p o σ fun o0 _ hty => ho o0 hty

/-- The old object of an arch write is an arch object. -/
theorem nbok_arch (a : ArchKernelObj) : ∀ old, aType old = aType (.archObj a) → NBOK old (.archObj a) := by
  intro old hty
  cases old with
  | archObj b => exact ⟨rfl, rfl⟩
  | cnode sz cs => simp only [aType] at hty; split_ifs at hty <;> cases hty
  | schedContext y n => simp only [aType] at hty; split_ifs at hty <;> cases hty
  | _ => simp [aType] at hty

theorem mem_setSimpleKoN {α : Type} [Nonempty α] {f : α → KernelObject} {p : ObjRef} {e : α} {σ : State Unit}
    {y : Unit × State Unit} (h : y ∈ (setSimpleKo (Z := Unit) f p e σ).1) :
    ∃ o0, σ.kheap p = some o0 ∧ isSimpleType o0 ∧ (∃ e0, f e0 = o0) ∧
      y.2 = { σ with kheap := Function.update σ.kheap p (some (f e)) } := by
  unfold setSimpleKo setObject at h
  obtain ⟨y1, hy1, h⟩ := h
  obtain ⟨hk, e2⟩ := mem_getObject hy1
  obtain ⟨o0, s1⟩ := y1
  simp only at hk e2; subst s1
  obtain ⟨z, ⟨hs, rfl⟩, h⟩ := h
  obtain ⟨z, ⟨hpi, rfl⟩, h⟩ := h
  obtain ⟨y3, hy3, h⟩ := h
  obtain ⟨hk3, e3⟩ := mem_getObject hy3
  obtain ⟨o3, s3⟩ := y3
  simp only at e3 hk3; subst s3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, h⟩ := h
  obtain ⟨w, hw, h⟩ := h
  rw [Set.mem_singleton_iff.1 hw] at h
  refine ⟨o0, hk, hs, ?_, by rw [Set.mem_singleton_iff.1 h]⟩
  cases e0 : partialInv f o0 with
  | none => exact absurd e0 hpi
  | some a => exact ⟨a, partialInv_eqG e0⟩

theorem simple_scnO {o : KernelObject} (h : isSimpleType o) : scnO o = none := by
  cases o with
  | schedContext y n => exact absurd rfl ((SInvB.simple_not h).2 y n)
  | _ => rfl

/-- **`set_simple_ko`, state-pinned**: the new object's SC pointer is the old one's. -/
theorem nb_setSimpleKo_p {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) (σ : State Unit)
    (he : ∀ o0, σ.kheap p = some o0 → nscO (f e) = nscO o0) :
    IKp NtfnScB σ (setSimpleKo (Z := Unit) f p e) := by
  intro hσ y hy
  obtain ⟨o0, hk, hs, -, e1⟩ := mem_setSimpleKoN hy
  obtain ⟨-, -, -, hs', -⟩ := mem_setSimpleKo hy
  rw [e1]
  exact nb_update hσ hk ⟨he o0 hk, by rw [simple_scnO hs', simple_scnO hs]⟩

/-- `set_simple_ko` of a constructor that is never a notification. -/
theorem nb_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (hf : ∀ a, nscO (f a) = none)
    (p : ObjRef) (e : α) : NBK (setSimpleKo (Z := Unit) f p e) := by
  intro σ hσ y hy
  obtain ⟨o0, hk, hs, ⟨e0, he0⟩, e1⟩ := mem_setSimpleKoN hy
  obtain ⟨-, -, -, hs2, -⟩ := mem_setSimpleKo hy
  rw [e1]
  exact nb_update hσ hk ⟨by rw [hf, ← he0, hf], by rw [simple_scnO hs2, simple_scnO hs]⟩

/-- `update_sk_obj_ref` with a field update keeping the notification's SC. -/
theorem nb_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (hf : ∀ g x, nscO (C (f g x)) = nscO (C x))
    (ref : ObjRef) (new : Option ObjRef) : NBK (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, e⟩ := mem_getSimpleKo hz
  obtain ⟨a, s⟩ := z
  simp only at hk e; subst s
  exact nb_setSimpleKo_p C ref _ σ (fun o0 h0 => by rw [hk] at h0; cases h0; exact hf _ _) hσ y hy

theorem nb_threadSet (f : Tcb → Tcb) (t : ObjRef) : NBK (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => nb_setObject_p _ _ σ fun old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact nbok_tcb _ _

theorem nb_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : NBK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => nb_setObject_p _ _ σ fun old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact nbok_tcb _ _

theorem nb_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : NBK (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (nb_setObject_p _ _ σ fun old hk _ => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hk; cases hk
  exact nbok_tcb _ _

theorem nb_doMachineOp {α : Type} (mop : NonDet MachineState α) : NBK (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem nb_doExtendedOp (eop : DetExtMonad Unit) : NBK (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) _

theorem nb_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : NBK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (nb_setObject_p _ _ σ fun old hk _ => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hk; cases hk
    exact nbok_tcb _ _
  · repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

/-- An SC update keeping the SC's notification. -/
theorem nb_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, (f y).scNtfn = y.scNtfn) :
    NBK (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  exact nb_update hσ hk ⟨rfl, by simp only [scnO, hf]⟩

theorem nb_setThreadStateAct (t : ObjRef) : NBK (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem nb_setThreadState (t : ObjRef) (ts : ThreadState) : NBK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (nb_threadSet _ t) fun _ => nb_setThreadStateAct t

theorem nb_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    NBK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact nb_threadSet _ _

/-- `set_cap` writes a CNode or a TCB of the old kind. -/
theorem nb_setCap (c : Cap) (sl : CslotPtr) : NBK (setCap (Z := Unit) c sl) := by
  intro σ hσ y hy
  obtain ⟨oref, r⟩ := sl
  unfold setCap at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨obj, z2⟩ := z
  simp only at hk hs; subst z2
  have key : ∀ o', NBOK obj o' → y ∈ ((setObject (Z := Unit) oref o') σ).1 → NtfnScB y.2 := by
    intro o' hok hy'
    obtain ⟨old, h1, -, e⟩ := SInvB.mem_setObject hy'
    rw [h1] at hk; cases hk
    rw [e]; exact nb_update hσ h1 hok
  cases obj with
  | cnode sz cn =>
    dsimp only at hy
    split_ifs at hy
    · obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hz] at hy
      refine key _ ?_ hy; exact ⟨rfl, rfl⟩
    · obtain ⟨z, hz, -⟩ := hy; exact hz.elim
  | tcb t =>
    dsimp only at hy
    split_ifs at hy <;> obtain ⟨z, hz, hy⟩ := hy <;> first
      | exact hz.elim
      | (rw [Set.mem_singleton_iff.1 hz] at hy; refine key _ ?_ hy; exact ⟨rfl, rfl⟩)
  | _ => dsimp only at hy; obtain ⟨z, hz, -⟩ := hy; exact hz.elim

theorem nb_setUntypedCapAsFull (srcCap newCap : Cap) (src : CslotPtr) :
    NBK (setUntypedCapAsFull (Z := Unit) srcCap newCap src) := by
  unfold setUntypedCapAsFull
  split
  · exact nb_setCap _ _
  · exact ik_pure _

theorem nb_capInsert (newCap : Cap) (src dest : CslotPtr) : NBK (capInsert (Z := Unit) newCap src dest) := by
  unfold capInsert
  repeat' (first | (with_reducible exact nb_setCap _ _) | (with_reducible exact nb_setUntypedCapAsFull _ _ _) | (with_reducible exact nb_doExtendedOp _) | (with_reducible exact ik_getObject _) | ik_step0 | ik_unfold)

end W

/-! ## Notifications read-modify-written at one state -/

theorem nscO_ntfnObj (a : Notification) (g : Ntfn → Ntfn) :
    nscO (.notification (ntfnObjUpdate g a)) = nscO (.notification a) := rfl

/-- `tcb_append` (an ordered insert) reads only. -/
theorem tcbAppend_st {t : ObjRef} {qs : List ObjRef} {σ : State Unit} {y : List ObjRef × State Unit}
    (h : y ∈ (tcbAppend (Z := Unit) t qs σ).1) : y.2 = σ ∧ True :=
  ⟨(show IK (fun s => s = σ) (tcbAppend (Z := Unit) t qs) by
    unfold tcbAppend orderedInsert; repeat' (first | ik_step0 | ik_unfold)) σ rfl y h, trivial⟩

theorem nb_tcbNtfnDequeue (t n : ObjRef) : NBK (tcbNtfnDequeue (Z := Unit) t n) := by
  intro σ hσ y hy
  unfold tcbNtfnDequeue at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst s1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  exact nb_setSimpleKo_p _ _ _ σ (fun o0 h0 => by rw [hk] at h0; cases h0; rfl) hσ y hy

theorem nb_tcbNtfnAppend (t n : ObjRef) : NBK (tcbNtfnAppend (Z := Unit) t n) := by
  intro σ hσ y hy
  unfold tcbNtfnAppend at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst s1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, -⟩ := tcbAppend_st hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs; subst s2
  exact nb_setSimpleKo_p _ _ _ σ (fun o0 h0 => by rw [hk] at h0; cases h0; rfl) hσ y hy

theorem nb_reorderNtfn (n t : ObjRef) : NBK (reorderNtfn (Z := Unit) n t) := by
  intro σ hσ y hy
  unfold reorderNtfn at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst s1
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, -⟩ := tcbAppend_st hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs; subst s2
  exact nb_setSimpleKo_p _ _ _ σ (fun o0 h0 => by rw [hk] at h0; cases h0; rfl) hσ y hy

/-! ## Unbinding a notification from its SC -/

/-- Clearing the notification `n`'s SC pointer and then the SC `c`'s
notification, where `c`'s notification is `n` (read at the start). -/
theorem nb_doUnbind (n c : ObjRef) (σ : State Unit)
    (hc : ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scNtfn = some n) :
    IKp NtfnScB σ (doUnbindNtfnSc (Z := Unit) n c) := by
  intro hσ y hy
  obtain ⟨y1, hy1, hy⟩ := hy
  -- the notification write
  unfold setNtfnObjRef updateSkObjRef at hy1
  obtain ⟨z, hz, hy1⟩ := hy1
  obtain ⟨hk, e⟩ := mem_getSimpleKo hz
  obtain ⟨a, s⟩ := z
  simp only at hk e; subst s
  obtain ⟨o0, hk0, -, -, e1⟩ := mem_setSimpleKoN hy1
  rw [hk] at hk0; cases hk0
  -- the SC write
  obtain ⟨y', k', hy', e2⟩ := SInvB.mem_updateSchedContext hy
  obtain ⟨yc, kc, hyc, hycn⟩ := hc
  have hcn : c ≠ n := by intro e; subst e; rw [hk] at hyc; cases hyc
  rw [e1] at hy'
  dsimp only at hy'
  rw [Function.update_apply, if_neg hcn, hyc] at hy'
  simp only [Option.some.injEq, KernelObject.schedContext.injEq] at hy'
  obtain ⟨rfl, rfl⟩ := hy'
  rw [e2, e1]
  intro m ntf d hm hd
  dsimp only at hm ⊢
  by_cases emc : m = c
  · subst emc; rw [Function.update_apply, if_pos rfl] at hm; cases hm
  rw [Function.update_apply, if_neg emc] at hm
  by_cases emn : m = n
  · subst emn
    rw [Function.update_apply, if_pos rfl] at hm
    cases hm
    simp [ntfnScUpdate] at hd
  rw [Function.update_apply, if_neg emn] at hm
  obtain ⟨yd, kd, hyd, hydn⟩ := hσ m ntf d hm hd
  by_cases edc : d = c
  · subst edc
    rw [hyc] at hyd
    simp only [Option.some.injEq, KernelObject.schedContext.injEq] at hyd
    obtain ⟨rfl, rfl⟩ := hyd
    rw [hycn] at hydn
    exact absurd (Option.some.inj hydn).symm emn
  · have hdn : d ≠ n := by intro e; subst e; rw [hk] at hyd; cases hyd
    refine ⟨yd, kd, ?_, hydn⟩
    rw [Function.update_apply, if_neg edc, Function.update_apply, if_neg hdn]
    exact hyd

theorem nb_schedContextUnbindNtfn (c : ObjRef) : NBK (schedContextUnbindNtfn (Z := Unit) c) := by
  unfold schedContextUnbindNtfn getScObjRef
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨z1, hz1, hz⟩ := hz
  unfold getSchedContext at hz1
  obtain ⟨w, hw, hz1⟩ := hz1
  obtain ⟨hkw, ew⟩ := mem_getObject hw
  obtain ⟨o, s⟩ := w
  simp only at hkw ew; subst s
  cases o with
  | schedContext yc kc =>
    rw [Set.mem_singleton_iff.1 hz1] at hz
    rw [Set.mem_singleton_iff.1 hz] at hy
    dsimp only at hy
    cases e : yc.scNtfn with
    | none => rw [e] at hy; exact (Set.mem_singleton_iff.1 hy) ▸ hσ
    | some n =>
      rw [e] at hy
      exact nb_doUnbind n c σ ⟨yc, kc, hkw, e⟩ hσ y hy
  | _ => exact hz1.elim

theorem nb_schedContextMaybeUnbindNtfn (n : ObjRef) : NBK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn getNtfnObjRef getSkObjRef
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨z1, hz1, hz⟩ := hz
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hz1
  obtain ⟨a, s1⟩ := z1
  simp only at hk e1; subst s1
  rw [Set.mem_singleton_iff.1 hz] at hy
  dsimp only at hy
  cases e : a.ntfnSc with
  | none => rw [e] at hy; exact (Set.mem_singleton_iff.1 hy) ▸ hσ
  | some c =>
    rw [e] at hy
    exact nb_doUnbind n c σ (hσ n a c hk e) hσ y hy

/-! ## The automation -/

set_option maxErrors 2000

syntax "nb_leaf" : tactic
macro_rules | `(tactic| nb_leaf) => `(tactic| fail "no nb_leaf")

macro "nb_auto" : tactic => `(tactic| repeat' (first | nb_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doMachineOp _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doExtendedOp _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setObject _ _ (nbok_arch _))
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setObject _ _ (nbok_tcbA _))
macro_rules | `(tactic| nb_leaf) => `(tactic| ((with_reducible refine nb_setSimpleKo _ ?_ _ _); intro _; rfl))
macro_rules | `(tactic| nb_leaf) => `(tactic| ((with_reducible refine nb_updateSkObjRef _ _ ?_ _ _); intro _ _; rfl))
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_threadSet _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archThreadSet _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_asUser _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setMrs _ _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setCap _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capInsert _ _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setUntypedCapAsFull _ _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setThreadStateAct _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setThreadState _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| ((with_reducible refine nb_updateSchedContext _ _ ?_); intro _; rfl))
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_optionUpdateThread _ _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbNtfnDequeue _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbNtfnAppend _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_reorderNtfn _ _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindNtfn _)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextMaybeUnbindNtfn _)

end

end Fl4Proofs.P3.SInvL
