/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctnq1): **T4, FL4's one
domain: every TCB's domain is the current domain, 0** (spec side only;
imports only Fl4Spec via SpecInvNativeScopeT, outside the JAtZ cone).

* `T4 σ := DLOK (domain list) ∧ curDomain = 0 ∧ TI dom0 σ`. `DLOK` is
  ScNextDom's `DomListOK` (l4v `valid_domain_list` and the one-domain entries)
  restated over the three fields (`DomListOK` itself is a structure on the
  state, so it is not definitionally kept by a `modify` of another field; the
  conversion is `dlok_iff` in SpecInvQDom). It is needed for `next_domain`:
  the new index stays in range, so the new `curDomain` is a list entry's
  domain, 0. l4v: `valid_domain_list` plus FL4's `numDomains = 1`, under which
  l4v's `valid_queues`/`ct_in_cur_domain` domain facts are uniform.
* The TCB writers as leaves (`q4_setObject` … `q4_deleteObjects`: copies of
  SpecInvNativeScopeT's `ti_*` keeping the other two conjuncts, which do not
  read the heap); a new TCB is `defaultTcb curDomain` (`q4_retypeRegionWith`
  reads `curDomain = 0`); `next_domain` (`q4_nextDomain`). The writers that
  change a domain (`thread_set_domain` from `set_domain`,
  `domain_schedule_configure`, `domain_set_start`) are the Domain invocation's
  and are handled with the decode's checks in SpecInvQDom.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- A TCB in domain 0. -/
def dom0 (x : Tcb) : Prop := x.tcbDomain = 0

/-- ScNextDom's `DomListOK`, over the domain list, its start and the index. -/
abbrev DLOK (l : List (Domain × DomainDuration)) (st i : Nat) : Prop :=
  1 < l.length ∧ (∀ e ∈ l, e.2 = 0 → e.1 = 0) ∧ st < l.length ∧ l[st]? ≠ some domainEndMarker ∧
    l[l.length - 1]? = some domainEndMarker ∧ i < l.length - 1 ∧ ∀ e ∈ l, e.1 = 0

/-- **T4 [J]: FL4's one domain** (l4v: `valid_domain_list`, every TCB's
`tcb_domain` below `numDomains = 1`, `cur_domain` the domain list's entry). -/
abbrev T4 (σ : State Unit) : Prop :=
  DLOK σ.domainList σ.domainStartIndex σ.domainIndex ∧ σ.curDomain = 0 ∧ TI dom0 σ

abbrev Q4K {α : Type} (m : NonDet (State Unit) α) : Prop := IK T4 m
abbrev Q4KE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE T4 m

/-! ## The TCB writers -/

theorem q4_update {σ : State Unit} (h : T4 σ) (p : ObjRef) (o : KernelObject)
    (ho : ∀ t, o = .tcb t → dom0 t) : T4 { σ with kheap := Function.update σ.kheap p (some o) } :=
  ⟨h.1, h.2.1, ti_update h.2.2 p o ho⟩

theorem q4_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : T4 σ → ∀ t, o = .tcb t → dom0 t) : IKp T4 σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨y1, y2⟩ := y
  have e2 : y2 = σ := by
    unfold getObject NonDet.getsThe at hy
    cases e : readObject p σ with
    | none => rw [e] at hy; exact hy.elim
    | some a => rw [e] at hy; exact (Prod.mk.inj (Set.mem_singleton_iff.1 hy)).2
  subst e2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact q4_update hσ p o (ho hσ)

theorem q4_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → dom0 t) :
    Q4K (setObject (Z := Unit) p o) :=
  fun σ => q4_setObject_p p o σ (fun _ => ho)

theorem q4_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    Q4K (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hk3, hs3⟩ := mem_getObject hy3
  obtain ⟨obj', y3⟩ := y3
  simp only at hk3 hs3 hsimp; subst hs3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine q4_update hσ p _ fun t ht => ?_
  exfalso
  rw [ht] at hty
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  rcases hsimp with h | h | h <;> rw [h] at hty <;> simp [aType] at hty

theorem q4_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, dom0 x → dom0 (f x)) :
    Q4K (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => q4_setObject_p _ _ σ fun hσ t' ht => ?_
  cases ht
  exact hf x (hσ.2.2 _ _ (getTcb_kheap hx))

theorem q4_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) :
    Q4K (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => q4_setObject_p _ _ σ fun hσ t' ht => ?_
  cases ht
  have h4 := hσ.2.2 _ _ (getTcb_kheap hx); exact h4

theorem q4_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : Q4K (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (q4_setObject_p _ _ σ fun hσ t' ht => ?_) fun _ => ik_pure _
  cases ht
  have h4 := hσ.2.2 _ _ (getTcb_kheap hx); exact h4

/-- The rest of `setMrs` after the register write: IPC-buffer stores. -/
macro "q4_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold))

theorem q4_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : Q4K (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (q4_setObject_p _ _ σ fun hσ t' ht => ?_) fun _ => ?_
  · cases ht
    have h4 := hσ.2.2 _ _ (getTcb_kheap hx); exact h4
  · q4_mach

theorem q4_setCap (c : Cap) (sl : CslotPtr) : Q4K (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun _ t ht => by cases ht)
    · exact ikp_fail_bind
  · rename_i tcb
    have hq : T4 σ → dom0 tcb := fun hσ => hσ.2.2 _ _ hk
    split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun hσ t ht => by cases ht; exact hq hσ)
    split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun hσ t ht => by cases ht; exact hq hσ)
    split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun hσ t ht => by cases ht; exact hq hσ)
    split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun hσ t ht => by cases ht; exact hq hσ)
    split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun hσ t ht => by cases ht; exact hq hσ)
    split
    · exact ikp_pure_bind (q4_setObject_p _ _ σ fun hσ t ht => by cases ht; exact hq hσ)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

/-- A new TCB is `defaultTcb curDomain`, in domain 0 by `T4`. -/
theorem q4_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat)
    (ty : ApiObjectType) (dev : Bool) : Q4K (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith
  refine ik_bind (ik_pure _) fun _ => ik_bind (ik_pure _) fun ptrs => ik_bind ?_ fun _ => ik_pure _
  unfold NonDet.when
  split
  · rename_i hty
    refine ik_gets_bind fun σ => ikp_gets_bind (ikp_pure_bind (ikp_modify fun hσ => ?_))
    refine ⟨hσ.1, hσ.2.1, ti_foldr_update _ _ (fun t ht => ?_) _ hσ.2.2⟩
    rw [defaultObject_tcb hty ht]; exact hσ.2.1
  · exact ik_pure' _

theorem q4_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    Q4K (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact q4_retypeRegionWith _ _ _ _ _ _

theorem q4_deleteObjects (ptr : Word) (bits : Nat) : Q4K (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ =>
    ik_modify fun _ h => ⟨h.1, h.2.1, ti_detype _ h.2.2⟩

/-! ## `next_domain` -/

/-- **`next_domain` keeps T4**: the new index is the start or the old index
plus one, both in range (invC's `dp_nextDomain`), so the new current domain is
a list entry's, 0. -/
theorem q4_nextDomain : Q4K (nextDomain (Z := Unit)) := by
  unfold nextDomain
  refine ik_bind ?_ fun _ => ik_doExtendedOp (fun _ _ h => h) _
  intro σ hσ x hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  obtain ⟨⟨hlen, hz, hst, hstNE, hlast, hidx, hdom⟩, -, hti⟩ := hσ
  have key : ∀ k, k < σ.domainList.length - 1 →
      DLOK σ.domainList σ.domainStartIndex k ∧ (the σ.domainList[k]?).1 = 0 := by
    intro k hk
    refine ⟨⟨hlen, hz, hst, hstNE, hlast, hk, hdom⟩, ?_⟩
    rw [List.getElem?_eq_getElem (by omega)]
    exact hdom _ (List.getElem_mem _)
  have hk : (if the σ.domainList[σ.domainIndex + 1]? = domainEndMarker then σ.domainStartIndex
      else σ.domainIndex + 1) < σ.domainList.length - 1 := by
    split
    · refine Nat.lt_of_le_of_ne (by omega) fun hc => hstNE ?_
      rw [hc]; exact hlast
    · rename_i hne
      refine Nat.lt_of_le_of_ne (by omega) fun e => hne ?_
      rw [e, hlast]; rfl
  obtain ⟨h1, h2⟩ := key _ hk
  exact ⟨h1, h2, hti⟩

/-! ## The leaves and `q4_auto` -/

/-- The side conditions of the TCB-writer leaves. -/
macro "q4_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _; simp [dom0]; done)
  | (intro _ hx; simpa [dom0] using hx)
  | (intro _ _ _; simp [dom0]; done)
  | (intro _ _ hx; simpa [dom0] using hx)
  | (simp; done)
  | decide)

syntax "q4_leaf" : tactic
macro_rules | `(tactic| q4_leaf) => `(tactic| fail "no q4_leaf")

macro "q4_auto" : tactic => `(tactic| repeat' (first | q4_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| q4_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); q4_side))
macro_rules | `(tactic| q4_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); q4_side))
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| q4_leaf) => `(tactic| ((with_reducible refine q4_setObject _ _ ?_); q4_side))
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_setSimpleKo _ _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| ((with_reducible refine q4_threadSet _ _ ?_); q4_side))
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_archThreadSet _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_asUser _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_setMrs _ _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_setCap _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_deleteObjects _ _)
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_nextDomain)

theorem q4_setThreadState (t : ObjRef) (ts : ThreadState) : Q4K (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (q4_threadSet _ _ fun _ h => h) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; q4_auto
macro_rules | `(tactic| q4_leaf) => `(tactic| with_reducible exact q4_setThreadState _ _)

theorem q4_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, dom0 x → dom0 (fn v x)) : Q4K (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact q4_threadSet _ _ (h _)
macro_rules | `(tactic| q4_leaf) => `(tactic| ((with_reducible refine q4_optionUpdateThread _ _ _ ?_); q4_side))

end

end Fl4Proofs.P3.SInvQ
