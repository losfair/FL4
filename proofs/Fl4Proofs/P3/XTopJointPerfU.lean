/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch26): **the Untyped and ASID
control performs keep `CQ` and `BI`** (spec side only), for `JMidPerfHypQ` /
`JMidPerfHypB` [W] (XTopJointMidRunQ, XTopJointChooseB).

The spec's `retype_region` and `delete_objects` write the heap at addresses
given by the invocation without any freeness check (l4v keeps the region free
by `valid_untyped` / `descendants_range_in`, invariants of the state). So the
two performs keep `CQ` / `BI` only where the region they touch (`D`: the reset
or deleted region and the new objects' addresses) avoids `ct` and every SC
some TCB is bound to (`RegC ct D`). Every other step is a frame of `ctV`, `qV`
and `sV` (MidRunK / MidRunQ / ChooseF leaves).

* `PW I m`: every outcome of `m` from an `I` state is `I`; combinators;
  `pw_of` (an `I` determined by `ctV`, `qV`, `sV` (`IStable`) is kept by any
  frame of the three).
* `pw_deleteObjects`, `pw_retypeRegionWith`: from `I` kept by `detype R` /
  by writing an object with no SC binding (`TPN`) at an address of the
  region.
* `ib_detype`/`ib_upd` (`IB D := CQ ∧ BI ∧ RegC D`), `iq_detype`/`iq_upd`
  (`IQ D := CQ ∧ ct ∉ D`): the two invariants for `R ⊆ D` / `p ∈ D`.
* `ut_post` (FL4's `invoke_untyped`, `invokeUntypedWith fl4ObjBitsApi`, with
  the reset), `asid_post` (`perform_asid_control_invocation`).
-/
import Fl4Proofs.P3.XTopJointChooseB
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

macro "kf_auto2" : tactic => `(tactic| repeat' (first | kf_leaf | dk_step0 | fv_unfold))

/-! ## Invariant-carrying steps -/

/-- Every outcome of `m` from an `I` state is `I`. -/
def PW (I : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, I σ → x ∈ (m σ).1 → I x.2

/-- `PW` for the exception monad. -/
def PWE (I : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := PW I (ExceptT.run m)

/-- `I` is determined by `ctV ct`, `qV` and `sV`. -/
def IStable (ct : ObjRef) (I : State Unit → Prop) : Prop :=
  ∀ σ σ', ctV ct σ' = ctV ct σ → qV σ' = qV σ → sV σ' = sV σ → I σ → I σ'

section
variable {I : State Unit → Prop}

theorem pw_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : PW I m)
    (hf : ∀ a, PW I (f a)) : PW I (m >>= f) :=
  fun σ x hs ⟨y, hy, hx⟩ => hf y.1 y.2 x (hm σ y hs hy) hx

theorem pw_bind' {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : PW I m)
    (hf : ∀ a, PW I (f a)) : PW I (NonDet.bind m f) := pw_bind hm hf

theorem pw_pure {α : Type} (a : α) : PW I (pure a : NonDet (State Unit) α) :=
  fun σ x hs hx => by rw [Set.mem_singleton_iff.1 hx]; exact hs

theorem pw_pure' {α : Type} (a : α) : PW I (NonDet.pure a : NonDet (State Unit) α) := pw_pure a

theorem pw_pure_bind {α β : Type} {a : α} {f : α → NonDet (State Unit) β} (h : PW I (f a)) :
    PW I (pure a >>= f) :=
  fun σ x hs ⟨y, hy, hx⟩ => by
    rw [Set.mem_singleton_iff.1 hy] at hx
    exact h σ x hs hx

theorem pw_pure_bind' {α β : Type} {a : α} {f : α → NonDet (State Unit) β} (h : PW I (f a)) :
    PW I (NonDet.bind (NonDet.pure a) f) := pw_pure_bind h

theorem pw_of {ct : ObjRef} (hI : IStable ct I) {α : Type} {m : NonDet (State Unit) α} (h1 : KF ct m)
    (h2 : QV m) (h3 : SV m) : PW I m :=
  fun σ x hs hx => hI σ x.2 (h1 σ x hx) (h2 σ x hx) (h3 σ x hx) hs

theorem pwe_of {ct : ObjRef} (hI : IStable ct I) {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : KFE ct m)
    (h2 : QVE m) (h3 : SVE m) : PWE I m :=
  pw_of hI h1 h2 h3

variable {ε : Type}

theorem pwe_bind {α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hm : PWE I m) (hf : ∀ a, PWE I (f a)) : PWE I (m >>= f) := by
  unfold PWE; rw [ExceptT.run_bind]
  refine pw_bind hm fun r => ?_
  cases r with
  | ok a => exact hf a
  | error e => exact pw_pure _

theorem pwe_liftE {α : Type} {m : NonDet (State Unit) α} (h : PW I m) : PWE I (NonDetE.liftE (ε := ε) m) := by
  unfold PWE NonDetE.liftE; rw [ExceptT.run_lift]
  exact pw_bind h fun _ => pw_pure _

theorem pwe_returnOk {α : Type} (a : α) : PWE I (NonDetE.returnOk a : NonDetE (State Unit) ε α) := pw_pure _

theorem pwe_returnOk_bind {α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : PWE I (f a)) :
    PWE I (NonDetE.returnOk a >>= f) := by
  unfold PWE; rw [ExceptT.run_bind]
  intro σ x hs ⟨y, hy, hx⟩
  obtain rfl : y = (.ok a, σ) := hy
  exact h σ x hs hx

theorem pwe_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : PWE I m) :
    PWE I (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; split
  · exact h
  · exact pw_pure _

end

/-! ## The two non-frame steps -/

/-- A new object binds no SC to a thread (its TCB SC field, if any, is `none`). -/
def TPN (o : KernelObject) : Prop := ∀ s, tP (some o) = some s → s = none

theorem tpn_default (ty : ApiObjectType) (hne : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain) :
    TPN (defaultObject ty dev n d) := by
  intro s hs
  cases ty <;> simp_all [defaultObject, tP, defaultTcb]

/-- The addresses `retype_region` writes. -/
def rtPtrs (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) :
    List ObjRef :=
  (List.range n).map fun p => ptrAdd ptr (p * 2 ^ bitsApi ty oBits)

/-- The region `delete_objects ptr bits` detypes. -/
def rgn (ptr : Word) (bits : Nat) : Set ObjRef := {x | ptr ≤ x ∧ x ≤ ptr + 2 ^ bits - 1}

section
variable {I : State Unit → Prop} {ct : ObjRef}

theorem pw_deleteObjects (hI : IStable ct I) (ptr : Word) (bits : Nat)
    (hD : ∀ σ, I σ → I (detype (rgn ptr bits) σ)) : PW I (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  first
    | refine pw_bind (pw_of hI (kf_doMachineOp _) (qv_doMachineOp _) (sck_doMachineOp _)) fun _ => ?_
    | refine pw_bind' (pw_of hI (kf_doMachineOp _) (qv_doMachineOp _) (sck_doMachineOp _)) fun _ => ?_
  intro σ x hs hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hD σ hs

theorem pw_fold (ps : List ObjRef) (o : KernelObject) (ho : TPN o)
    (hU : ∀ σ p, p ∈ ps → I σ → I { σ with kheap := Function.update σ.kheap p (some o) }) :
    ∀ σ, I σ → I { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some o)) σ.kheap } := by
  induction ps with
  | nil => exact fun σ hs => hs
  | cons p rest ih =>
    intro σ hs
    have h1 := ih (fun σ q hq hs => hU σ q (List.mem_cons_of_mem _ hq) hs) σ hs
    exact hU { σ with kheap := rest.foldr (fun p kh => Function.update kh p (some o)) σ.kheap } p
      (List.mem_cons_self ..) h1

theorem pw_retypeRegionWith (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat)
    (ty : ApiObjectType) (dev : Bool)
    (hU : ∀ σ p o, p ∈ rtPtrs bitsApi ptr n oBits ty → TPN o → I σ →
      I { σ with kheap := Function.update σ.kheap p (some o) }) :
    PW I (retypeRegionWith (Z := Unit) bitsApi ptr n oBits ty dev) := by
  unfold retypeRegionWith
  first | refine pw_pure_bind ?_ | refine pw_pure_bind' ?_
  first | refine pw_pure_bind ?_ | refine pw_pure_bind' ?_
  first | refine pw_bind ?_ fun _ => pw_pure _ | refine pw_bind' ?_ fun _ => pw_pure' _
  unfold NonDet.when
  split
  · next hne =>
    intro σ x hs hx
    obtain ⟨y1, h1, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 h1] at hx
    obtain ⟨y2, h2, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 h2] at hx
    obtain ⟨y3, h3, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 h3] at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact pw_fold _ _ (tpn_default ty hne dev oBits σ.curDomain)
      (fun σ' p hp hs' => hU σ' p _ hp (tpn_default ty hne dev oBits σ.curDomain) hs') σ hs
  · exact pw_pure' _

end

/-! ## The two invariants -/

/-- The touched region `D` avoids `ct` and every SC a TCB is bound to. -/
def RegC (ct : ObjRef) (D : Set ObjRef) (σ : State Unit) : Prop :=
  ct ∉ D ∧ ∀ u p, (mV σ u).1 = some (some p) → p ∉ D

/-- `CQ ∧ BI ∧ RegC D`. -/
def IB (ct : ObjRef) (D : Set ObjRef) (σ : State Unit) : Prop := CQ ct σ ∧ BI ct σ ∧ RegC ct D σ

/-- `CQ ∧ ct ∉ D`. -/
def IQ (ct : ObjRef) (D : Set ObjRef) (σ : State Unit) : Prop := CQ ct σ ∧ ct ∉ D

section
variable {ct : ObjRef} {D : Set ObjRef}

theorem nq_of_qV {σ σ' : State Unit} (e : qV σ' = qV σ) (h : PPNQ.NQ ct σ) : PPNQ.NQ ct σ' := by
  simp only [qV, Prod.mk.injEq] at e
  exact ⟨by rw [e.1]; exact h.1, by rw [e.2]; exact h.2⟩

theorem mV_of_sV {σ σ' : State Unit} (e : sV σ' = sV σ) : mV σ' = mV σ := by
  unfold sV at e
  simp only [Prod.mk.injEq] at e
  exact e.2.2.2

theorem ib_stable : IStable ct (IB ct D) := by
  intro σ σ' e1 e2 e3 ⟨hq, hb, hr⟩
  refine ⟨⟨CtRs.of_ctV e1 hq.1, nq_of_qV e2 hq.2⟩, BI.of_sV e3 hb, hr.1, ?_⟩
  rw [mV_of_sV e3]; exact hr.2

theorem iq_stable : IStable ct (IQ ct D) :=
  fun σ σ' e1 e2 _ ⟨hq, hd⟩ => ⟨⟨CtRs.of_ctV e1 hq.1, nq_of_qV e2 hq.2⟩, hd⟩

/-- `BIV` across a change of the view inside `X`, where `X` avoids `ct` and
every bound SC, and the new entries of `X` bind no SC. -/
theorem biv_frame {c i : ObjRef} {rq : List ObjRef} {M M' : MT} (h : BIV ct c i rq M)
    (hdis : ∀ q, (M' q).1 = none ∨ (M' q).2 = none) (X : Set ObjRef) (hct : ct ∉ X)
    (hsame : ∀ q, q ∉ X → M' q = M q) (hX : ∀ q s, q ∈ X → (M' q).1 = some s → s = none)
    (hnp : ∀ u p, (M u).1 = some (some p) → p ∉ X) : BIV ct c i rq M' := by
  refine ⟨hdis, ?_, ?_, ?_⟩
  · rw [hsame ct hct]; exact h.ex
  · intro s hs
    rw [hsame ct hct] at hs
    rcases h.cur s hs with h1 | ⟨e, ⟨tm, htm⟩, hpos, hrq⟩
    · exact Or.inl h1
    · have hc : c ∉ X := hnp ct c (e ▸ hs)
      right
      rw [hsame c hc]
      exact ⟨e, ⟨tm, htm⟩, hpos, hrq⟩
  · intro u p hu
    by_cases hux : u ∈ X
    · cases hX u _ hux hu
    · rw [hsame u hux] at hu
      have hp : p ∉ X := hnp u p hu
      rw [hsame p hp]
      exact h.back u p hu

theorem regc_frame {σ σ' : State Unit} (h : RegC ct D σ) (X : Set ObjRef)
    (hsame : ∀ q, q ∉ X → mV σ' q = mV σ q) (hX : ∀ q s, q ∈ X → (mV σ' q).1 = some s → s = none) :
    RegC ct D σ' := by
  refine ⟨h.1, fun u p hu => ?_⟩
  by_cases hux : u ∈ X
  · cases hX u _ hux hu
  · rw [hsame u hux] at hu
    exact h.2 u p hu

theorem mV_detype_out {R : Set ObjRef} {σ : State Unit} {q : ObjRef} (hq : q ∉ R) :
    mV (detype R σ) q = mV σ q := by
  simp only [mV, detype, if_neg hq]

theorem mV_detype_in {R : Set ObjRef} {σ : State Unit} {q : ObjRef} (hq : q ∈ R) {s : Option ObjRef}
    (h : (mV (detype R σ) q).1 = some s) : s = none := by
  simp only [mV, detype, if_pos hq] at h
  cases h

theorem ctV_detype {R : Set ObjRef} {σ : State Unit} (hct : ct ∉ R) : ctV ct (detype R σ) = ctV ct σ := by
  simp only [ctV, detype, if_neg hct]

theorem ib_detype {R : Set ObjRef} (hRD : R ⊆ D) {σ : State Unit} (h : IB ct D σ) : IB ct D (detype R σ) := by
  obtain ⟨hq, hb, hr⟩ := h
  have hct : ct ∉ R := fun h' => hr.1 (hRD h')
  refine ⟨⟨CtRs.of_ctV (ctV_detype hct) hq.1, hq.2⟩, ?_, ?_⟩
  · exact biv_frame hb (mV_dis _) R hct (fun q hq => mV_detype_out hq) (fun q s hq h => mV_detype_in hq h)
      (fun u p hu hp => hr.2 u p hu (hRD hp))
  · exact regc_frame hr R (fun q hq => mV_detype_out hq) (fun q s hq h => mV_detype_in hq h)

theorem iq_detype {R : Set ObjRef} (hRD : R ⊆ D) {σ : State Unit} (h : IQ ct D σ) : IQ ct D (detype R σ) := by
  obtain ⟨hq, hd⟩ := h
  have hct : ct ∉ R := fun h' => hd (hRD h')
  exact ⟨⟨CtRs.of_ctV (ctV_detype hct) hq.1, hq.2⟩, hd⟩

theorem ctV_upd {σ : State Unit} {p : ObjRef} {o : KernelObject} (hp : p ≠ ct) :
    ctV ct { σ with kheap := Function.update σ.kheap p (some o) } = ctV ct σ := by
  simp only [ctV, Function.update_of_ne (Ne.symm hp)]

theorem mV_upd_out {σ : State Unit} {p q : ObjRef} {o : KernelObject} (hq : q ∉ ({p} : Set ObjRef)) :
    mV { σ with kheap := Function.update σ.kheap p (some o) } q = mV σ q := by
  rw [mV_upd, Function.update_of_ne (fun e => hq (Set.mem_singleton_iff.2 e))]

theorem mV_upd_in {σ : State Unit} {p q : ObjRef} {o : KernelObject} (ho : TPN o) (hq : q ∈ ({p} : Set ObjRef))
    {s : Option ObjRef} (h : (mV { σ with kheap := Function.update σ.kheap p (some o) } q).1 = some s) :
    s = none := by
  rw [Set.mem_singleton_iff.1 hq, mV_upd, Function.update_self] at h
  exact ho s h

theorem ib_upd {σ : State Unit} {p : ObjRef} (hp : p ∈ D) {o : KernelObject} (ho : TPN o) (h : IB ct D σ) :
    IB ct D { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨hq, hb, hr⟩ := h
  have hpc : p ≠ ct := fun e => hr.1 (e ▸ hp)
  have hct : ct ∉ ({p} : Set ObjRef) := fun e => hpc (Set.mem_singleton_iff.1 e).symm
  refine ⟨⟨CtRs.of_ctV (ctV_upd hpc) hq.1, hq.2⟩, ?_, ?_⟩
  · exact biv_frame hb (mV_dis _) {p} hct (fun q hq => mV_upd_out hq) (fun q s hq h => mV_upd_in ho hq h)
      (fun u p' hu hp' => hr.2 u p' hu ((Set.mem_singleton_iff.1 hp') ▸ hp))
  · exact regc_frame hr {p} (fun q hq => mV_upd_out hq) (fun q s hq h => mV_upd_in ho hq h)

theorem iq_upd {σ : State Unit} {p : ObjRef} (hp : p ∈ D) {o : KernelObject} (h : IQ ct D σ) :
    IQ ct D { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨hq, hd⟩ := h
  have hpc : p ≠ ct := fun e => hd (e ▸ hp)
  exact ⟨⟨CtRs.of_ctV (ctV_upd hpc) hq.1, hq.2⟩, hd⟩

end

/-! ## The Untyped perform -/

section
variable {I : State Unit → Prop} {ct : ObjRef}

theorem ro_getCap' (sl : CslotPtr) : RO (getCap (Z := Unit) sl) := by
  ro_auto

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The reset keeps `I`** where `I` survives the detype of the region of the
cap at `sl` (pointwise at the start state): after the cap read, a frame but
the `delete_objects` of the cap's region. -/
theorem reset_post (hI : IStable ct I) (sl : CslotPtr) (σ : State Unit) (hs : I σ)
    (hD : ∀ c, (c, σ) ∈ (getCap (Z := Unit) sl σ).1 → ∀ σ', I σ' → I (detype (rgn (objRefOf c) (Fl4Spec.bitsOf c)) σ')) :
    ∀ x ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1, I x.2 := by
  intro x hx
  unfold resetUntypedCap at hx
  obtain ⟨z, hz, ⟨c, hc, hx⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hx
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
  simp only [Except.ok.injEq] at hc
  subst hc
  have e : w.2 = σ := ro_getCap' sl σ w hw
  have hw' : (w.1, σ) ∈ (getCap (Z := Unit) sl σ).1 := by
    obtain ⟨a, b⟩ := w
    simp only at e
    subst e
    exact hw
  have hD' := hD w.1 hw'
  rw [e] at hx
  refine (?_ : PWE I _) σ x hs hx
  refine pwe_returnOk_bind ?_
  refine pwe_returnOk_bind ?_
  split
  · exact pwe_returnOk _
  · refine pwe_bind (pwe_liftE (pw_deleteObjects hI _ _ hD')) fun _ => ?_
    exact pwe_of hI (by kf_auto2) (by qv_auto2) (by sck_auto2)

/-- The region FL4's `invoke_untyped` touches from `σ`: the reset region of
the source cap at `sl` (if `reset`) and the new objects' addresses. -/
def utD (sl : CslotPtr) (σ : State Unit) (reset : Bool) (rb : ObjRef) (ty : ApiObjectType) (objSz n : Nat) :
    Set ObjRef :=
  {x | (reset = true ∧ ∃ c, (c, σ) ∈ (getCap (Z := Unit) sl σ).1 ∧ x ∈ rgn (objRefOf c) (Fl4Spec.bitsOf c)) ∨
    x ∈ rtPtrs fl4ObjBitsApi rb n objSz ty}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **FL4's `invoke_untyped` keeps `I`** (pointwise): from `I` kept by the
reset's detype and by the new objects. -/
theorem ut_post (hI : IStable ct I) (srcSlot : CslotPtr) (reset : Bool) (base rb : ObjRef) (ty : ApiObjectType)
    (objSz : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit) (hs : I σ)
    (hD : reset = true → ∀ c, (c, σ) ∈ (getCap (Z := Unit) srcSlot σ).1 → ∀ σ', I σ' →
      I (detype (rgn (objRefOf c) (Fl4Spec.bitsOf c)) σ'))
    (hU : ∀ σ' p o, p ∈ rtPtrs fl4ObjBitsApi rb slots.length objSz ty → TPN o → I σ' →
      I { σ' with kheap := Function.update σ'.kheap p (some o) }) :
    ∀ x ∈ ((fl4InvokeUntyped (Z := Unit) (.retype srcSlot reset base rb ty objSz slots dev)).run σ).1, I x.2 := by
  intro x hx
  unfold fl4InvokeUntyped invokeUntypedWith at hx
  obtain ⟨z, hz, hr⟩ := mem_bindE_inv' hx
  have hz2 : I z.2 := by
    cases reset
    · exact (pw_pure (Except.ok ()) : PW I _) σ z hs hz
    · exact reset_post hI srcSlot σ hs (hD rfl) z hz
  rcases hr with ⟨u, -, hx⟩ | ⟨e, -, rfl⟩
  swap
  · exact hz2
  refine (pwe_liftE ?_ : PWE I _) z.2 x hz2 hx
  first
    | refine pw_bind (pw_of hI (kf_getCap _) (qv_getCap _) (sck_getCap _)) fun cap => ?_
    | refine pw_bind' (pw_of hI (kf_getCap _) (qv_getCap _) (sck_getCap _)) fun cap => ?_
  first | refine pw_pure_bind ?_ | refine pw_pure_bind' ?_
  first | refine pw_pure_bind ?_ | refine pw_pure_bind' ?_
  first
    | refine pw_bind (pw_of hI (kf_setCap _ _) (qv_setCap _ _) (sck_setCap _ _)) fun _ => ?_
    | refine pw_bind' (pw_of hI (kf_setCap _ _) (qv_setCap _ _) (sck_setCap _ _)) fun _ => ?_
  first
    | refine pw_bind (pw_retypeRegionWith _ _ _ _ _ _ hU) fun _ => ?_
    | refine pw_bind' (pw_retypeRegionWith _ _ _ _ _ _ hU) fun _ => ?_
  exact pw_of hI (by kf_auto2) (by qv_auto2) (by sck_auto2)

/-! ## The ASID control perform -/

/-- The region `perform_asid_control_invocation` touches. -/
def asidD (frame : ObjRef) : Set ObjRef :=
  {x | x ∈ rgn frame page_bits ∨ x ∈ rtPtrs objBitsApi frame 1 0 (.archObject .asidPoolObj)}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pw_asidControl (hI : IStable ct I) (frame : ObjRef) (slot parent : CslotPtr) (base : Asid)
    (hD : ∀ σ', I σ' → I (detype (rgn frame page_bits) σ'))
    (hU : ∀ σ' p o, p ∈ rtPtrs objBitsApi frame 1 0 (.archObject .asidPoolObj) → TPN o → I σ' →
      I { σ' with kheap := Function.update σ'.kheap p (some o) }) :
    PW I (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  unfold performAsidControlInvocation
  first
    | refine pw_bind (pw_deleteObjects hI _ _ hD) fun _ => ?_
    | refine pw_bind' (pw_deleteObjects hI _ _ hD) fun _ => ?_
  first
    | refine pw_bind (pw_of hI (kf_getCap _) (qv_getCap _) (sck_getCap _)) fun _ => ?_
    | refine pw_bind' (pw_of hI (kf_getCap _) (qv_getCap _) (sck_getCap _)) fun _ => ?_
  first
    | refine pw_bind (pw_of hI (kf_setCap _ _) (qv_setCap _ _) (sck_setCap _ _)) fun _ => ?_
    | refine pw_bind' (pw_of hI (kf_setCap _ _) (qv_setCap _ _) (sck_setCap _ _)) fun _ => ?_
  first
    | refine pw_bind (pw_retypeRegionWith objBitsApi _ _ _ _ _ hU) fun _ => ?_
    | refine pw_bind' (pw_retypeRegionWith objBitsApi _ _ _ _ _ hU) fun _ => ?_
  exact pw_of hI (by kf_auto2) (by qv_auto2) (by sck_auto2)

end

end

end Fl4Proofs.P3.MidRun
