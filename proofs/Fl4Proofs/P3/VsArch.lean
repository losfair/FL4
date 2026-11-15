/-
P3 (DESIGN.md §9), VSpace: **the x86 arch relation**, from one interface.

FL4's `machine::Arch` is the trusted boundary. The spec keeps the current
address space in `x64_current_cr3` and models the TLB and paging-structure
caches as the opaque `machine_state_rest`, changed only by `machine_op_lift`
of underspecified operations (`invalidateASID`,
`invalidateTranslationSingleASID`, `invalidateLocalPageStructureCacheASID`).
Those operations never fail (`ignore_failure`), always have an outcome, and
change nothing but `machine_state_rest`: the abstract spec says nothing
about the TLB beyond that, so the relation can only track CR3.

`ArchRefines ar AR`, with `AR : A → Cr3 → Prop` (FL4's arch state against
the spec's CR3), is the one assumption on the x86 backend, an obligation
per `Arch` method the VSpace code uses:
* `set_vspace a ptr asid` yields CR3 `make_cr3 (addrFromPPtr ptr) asid`;
* `invalidate_page`, `invalidate_asid`, `invalidate_page_structures` keep
  CR3 (they flush caches only).

From it, for `SR := TopSR … AR`: every flush hypothesis of the VSpace
structures (`flushOK_top` … `flushTbl_top`, `inval_top`), and `VsRootHyps`
(`vsRootHyps_top`; the kernel root through `KRootRel`).
-/
import Fl4Proofs.P3.VsTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

/-- **The x86 backend's obligations** (see the module docstring). -/
structure ArchRefines {A : Type} (ar : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  setVspace : ∀ a c (ptr asid : U64), AR a c →
    ar.set_vspace a ptr asid ⦃ a' => AR a' (Fl4Spec.makeCr3 (Fl4Spec.addrFromPPtr ptr.bv) asid.bv) ⦄
  invPage : ∀ a c (asid vaddr : U64), AR a c → ar.invalidate_page a asid vaddr ⦃ a' => AR a' c ⦄
  invAsid : ∀ a c (asid : U64), AR a c → ar.invalidate_asid a asid ⦃ a' => AR a' c ⦄
  invEpt : ∀ a c (root mask : U64), AR a c → ar.invalidate_ept a root mask ⦃ a' => AR a' c ⦄
  invPS : ∀ a c (asid : U64), AR a c → ar.invalidate_page_structures a asid ⦃ a' => AR a' c ⦄

/-! ## The spec's machine operations -/

section Spec
open Fl4Spec

/-- A machine operation that never fails, has an outcome, and keeps the
memory. -/
def MOK (mop : NonDet MachineState Unit) : Prop :=
  ∀ ms, ¬ (mop ms).2 ∧ (∃ y, y ∈ (mop ms).1) ∧ ∀ y ∈ (mop ms).1, y.2.underlyingMemory = ms.underlyingMemory

theorem machineOpLift_ok (f : MachineRestMonad Unit) : MOK (machineOpLift f) := by
  intro ms
  have hig : ¬ (ignoreFailure f ms.machineStateRest).2 ∧ ∃ y, y ∈ (ignoreFailure f ms.machineStateRest).1 := by
    unfold ignoreFailure
    split_ifs with h
    · exact ⟨id, _, rfl⟩
    · exact ⟨id, Set.nonempty_iff_ne_empty.2 h⟩
  unfold machineOpLift machineRestLift
  simp only [nd_bind_apply', NonDet.gets, NonDet.selectF, NonDet.modify, Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp only [not_or, not_exists, not_and]
    refine ⟨id, fun x hx => ?_⟩
    obtain ⟨rfl⟩ := hx
    refine ⟨hig.1, fun y hy => ?_⟩
    simp [pure, NonDet.pure]
  · obtain ⟨⟨r, mr⟩, hy⟩ := hig.2
    exact ⟨((), { ms with machineStateRest := mr }), _, rfl, ((r, mr), ms), ⟨hy, rfl⟩, _, rfl, by
      simp [pure, NonDet.pure]⟩
  · rintro y ⟨x, rfl, z, ⟨-, rfl⟩, w, rfl, hw⟩
    simp only [pure, NonDet.pure, Set.mem_singleton_iff] at hw
    subst hw; rfl

/-- A spec operation that only changes the machine state, keeping the
memory, never fails, and has an outcome. -/
def SOK (m : SMonad Unit Unit) : Prop :=
  ∀ σ : State Unit, ¬ (m σ).2 ∧ (∃ y, y ∈ (m σ).1) ∧
    ∀ y ∈ (m σ).1, ∃ ms, y.2 = { σ with machineState := ms } ∧ ms.underlyingMemory = σ.machineState.underlyingMemory

theorem doMachineOp_ok {mop : NonDet MachineState Unit} (h : MOK mop) : SOK (doMachineOp (Z := Unit) mop) := by
  intro σ
  obtain ⟨h1, ⟨y, hy⟩, h3⟩ := h σ.machineState
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · unfold doMachineOp
    simp only [nd_bind_apply', NonDet.gets, NonDet.selectF, NonDet.modify, Set.mem_setOf_eq,
      Set.mem_singleton_iff, not_or, not_exists, not_and]
    refine ⟨id, fun x hx => ?_⟩
    obtain ⟨rfl⟩ := hx
    refine ⟨h1, fun w _ => ?_⟩
    simp [pure, NonDet.pure]
  · obtain ⟨r, ms⟩ := y
    cases r
    refine ⟨((), { σ with machineState := ms }), ?_⟩
    unfold doMachineOp
    simp only [nd_bind_apply', NonDet.gets, NonDet.selectF, NonDet.modify, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨_, rfl, (((), ms), σ), ⟨hy, rfl⟩, _, rfl, by simp [pure, NonDet.pure]⟩
  · obtain ⟨u, σz⟩ := z
    cases u
    obtain ⟨ms, hms, rfl⟩ := doMachineOp_mem' hz
    exact ⟨ms, rfl, h3 _ hms⟩

theorem SOK.pure : SOK (fun σ => NonDet.pure (σ := State Unit) () σ) := by
  intro σ
  refine ⟨id, ⟨_, rfl⟩, fun y hy => ⟨σ.machineState, ?_, rfl⟩⟩
  simp only [NonDet.pure, Set.mem_singleton_iff] at hy; rw [hy]

theorem SOK.mapMx {α : Type} (g : α → SMonad Unit Unit) (hg : ∀ x, SOK (g x)) :
    ∀ l : List α, SOK (NonDet.mapMx g l) := by
  intro l
  induction l with
  | nil => exact SOK.pure
  | cons x l ih =>
    intro σ
    obtain ⟨h1, ⟨y, hy⟩, h3⟩ := hg x σ
    simp only [NonDet.mapMx, NonDet.bind]
    refine ⟨?_, ?_, ?_⟩
    · rintro (h | ⟨z, hz, h⟩)
      · exact h1 h
      · obtain ⟨ms, e, -⟩ := h3 z hz
        exact (ih z.2).1 h
    · obtain ⟨y', hy'⟩ := (ih y.2).2.1
      exact ⟨y', y, hy, hy'⟩
    · rintro w ⟨z, hz, hw⟩
      obtain ⟨ms, e, hum⟩ := h3 z hz
      obtain ⟨ms', e', hum'⟩ := (ih z.2).2.2 w hw
      refine ⟨ms', ?_, ?_⟩
      · rw [e', e]
      · rw [hum', e, hum]

theorem invPSCA_ok (vs : ObjRef) (asid : Asid) : SOK (invalidatePageStructureCacheAsid (Z := Unit) vs asid) :=
  doMachineOp_ok (machineOpLift_ok _)
theorem flushAll_ok (vs : ObjRef) (asid : Asid) : SOK (flushAll (Z := Unit) vs asid) :=
  doMachineOp_ok (machineOpLift_ok _)
theorem hwAsidInvalidate_ok (asid : Asid) (vs : ObjRef) : SOK (hwAsidInvalidate (Z := Unit) asid vs) :=
  doMachineOp_ok (machineOpLift_ok _)
theorem invTSA_ok (v asid : Data) : SOK (doMachineOp (Z := Unit) (invalidateTranslationSingleASID v asid)) :=
  doMachineOp_ok (machineOpLift_ok _)

/-- `flush_table` of a page table, at an aligned address. -/
theorem flushTable_ok {σ : State Unit} {vs : ObjRef} {v : VSpaceRef} {pt : ObjRef} {asid : Asid}
    (hal : v &&& mask (ptTranslationBits + pageBits) = 0) {f : BitVec 9 → PTE}
    (hk : σ.kheap pt = some (.archObj (.pageTable f))) :
    ¬ (flushTable (Z := Unit) vs v pt asid σ).2 ∧ (∃ y, y ∈ (flushTable (Z := Unit) vs v pt asid σ).1) ∧
      ∀ y ∈ (flushTable (Z := Unit) vs v pt asid σ).1, ∃ ms, y.2 = { σ with machineState := ms } ∧
        ms.underlyingMemory = σ.machineState.underlyingMemory := by
  have ha : NonDet.assert (σ := State Unit) (v &&& mask (ptTranslationBits + pageBits) = 0) σ = ({((), σ)}, False) := by
    simp [NonDet.assert, hal]
  have hg : getPt (Z := Unit) pt σ = ({(f, σ)}, False) := by
    unfold getPt; rw [nd_bind_one (getObject_eq hk)]; rfl
  unfold flushTable
  rw [nd_bind_one ha, nd_bind_one hg]
  refine SOK.mapMx _ (fun index => ?_) _ σ
  intro σ'
  rw [nd_pure_bind']
  have hm : ∀ e : PTE, SOK (match e with
      | .invalidPTE => pure ()
      | _ => doMachineOp (Z := Unit) (invalidateTranslationSingleASID (v + ucast 64 index <<< pageBits)
          (ucast 64 asid))) := by
    intro e; cases e <;> first | exact SOK.pure | exact invTSA_ok _ _
  exact hm (f index) σ'

end Spec

/-! ## The relation across machine operations and CR3 changes -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The composite relation with another machine state (same memory) and a
CR3 the arch state is related to. -/
theorem TopSR.machine {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (ms : Fl4Spec.MachineState)
    (hum : ms.underlyingMemory = σ.machineState.underlyingMemory) (cr : Fl4Spec.Cr3) (hA : AR a' cr) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a'
      (cr3Upd { σ with machineState := ms } cr) :=
  TopSR.step (Rw := fun _ => False) (Rg := fun _ => False) hS rfl rfl (fun _ _ _ _ => rfl) (fun _ h => h.elim)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ hq => absurd rfl hq⟩
    (fun _ h => h.elim) (fun wp _ => by show Endp.loadWordAt ms.underlyingMemory _ = _; rw [hum]) (fun _ => hA)

theorem TopSR.cr3 {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (cr : Fl4Spec.Cr3) (hA : AR a' cr) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' (cr3Upd σ cr) :=
  TopSR.step (Rw := fun _ => False) (Rg := fun _ => False) hS rfl rfl (fun _ _ _ _ => rfl) (fun _ h => h.elim)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ hq => absurd rfl hq⟩
    (fun _ h => h.elim) (fun wp _ => rfl) (fun _ => hA)

theorem TopSR.machine' {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (ms : Fl4Spec.MachineState)
    (hum : ms.underlyingMemory = σ.machineState.underlyingMemory) (hA : AR a' σ.archState.x64CurrentCr3) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' { σ with machineState := ms } :=
  TopSR.step (Rw := fun _ => False) (Rg := fun _ => False) hS rfl rfl (fun _ _ _ _ => rfl) (fun _ h => h.elim)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ hq => absurd rfl hq⟩
    (fun _ h => h.elim) (fun wp _ => by show Endp.loadWordAt ms.underlyingMemory _ = _; rw [hum]) (fun _ => hA)

/-- From an `SOK` operation and an arch step keeping CR3: an outcome related
to the new arch state. -/
theorem flush_of_sok {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {m : Fl4Spec.SMonad Unit Unit} (hm : SOK m)
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit} (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hA : AR a' σ.archState.x64CurrentCr3) :
    ∃ σ', ((), σ') ∈ (m σ).1 ∧ TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' := by
  obtain ⟨-, ⟨⟨u, σ'⟩, hy⟩, h3⟩ := hm σ
  obtain ⟨ms, e, hum⟩ := h3 _ hy
  cases u
  simp only at e
  subst e
  exact ⟨_, hy, TopSR.machine' hS ms hum hA⟩

variable {A : Type} {ar : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines ar AR)
include hA

/-! ## The flush hypotheses -/

omit hA in
theorem flushOK_top (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) (σ : Fl4Spec.State Unit) :
    ¬ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid σ).2 := (invPSCA_ok vs asid σ).1

omit hA in
theorem noFlush_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ' :=
  flush_of_sok (invPSCA_ok _ _) hS hS.1.2.2.2.2.2.2

theorem flushPage_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid vaddr : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_page a asid vaddr ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧
        TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ :=
  WP.spec_mono (hA.invPage a _ asid vaddr hS.1.2.2.2.2.2.2) fun _ h => flush_of_sok (invPSCA_ok _ _) hS h

theorem flushAsid_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_asid a asid ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧
        TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ :=
  WP.spec_mono (hA.invAsid a _ asid hS.1.2.2.2.2.2.2) fun _ h => flush_of_sok (invPSCA_ok _ _) hS h

theorem flushPS_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_page_structures a asid ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧
        TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ :=
  WP.spec_mono (hA.invPS a _ asid hS.1.2.2.2.2.2.2) fun _ h => flush_of_sok (invPSCA_ok _ _) hS h

omit hA in
theorem flushAllOK_top (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) :
    ¬ (Fl4Spec.flushAll (Z := Unit) vs asid σ).2 := (flushAll_ok vs asid σ).1

theorem flushAllH_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (asid : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_asid a asid ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.flushAll (Z := Unit) vs asid.bv σ).1 ∧
        TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ :=
  WP.spec_mono (hA.invAsid a _ asid hS.1.2.2.2.2.2.2) fun _ h => flush_of_sok (flushAll_ok _ _) hS h

omit hA in
theorem flushPgOK_top (σ : Fl4Spec.State Unit) (v asid : Fl4Spec.Data) :
    ¬ (Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.invalidateTranslationSingleASID v asid) σ).2 :=
  (invTSA_ok v asid σ).1

theorem flushPg_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (asid vaddr : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_page a asid vaddr ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.doMachineOp (Z := Unit)
        (Fl4Spec.invalidateTranslationSingleASID vaddr.bv (Fl4Spec.ucast 64 asid.bv)) σ).1 ∧
        TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ :=
  WP.spec_mono (hA.invPage a _ asid vaddr hS.1.2.2.2.2.2.2) fun _ h => flush_of_sok (invTSA_ok _ _) hS h

omit hA in
theorem invalOK_top (asid vs : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) :
    ¬ (Fl4Spec.hwAsidInvalidate (Z := Unit) asid vs σ).2 := (hwAsidInvalidate_ok asid vs σ).1

theorem inval_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (asid : U64) (vs : Fl4Spec.ObjRef)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_asid a asid ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.hwAsidInvalidate (Z := Unit) asid.bv vs σ).1 ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ :=
  WP.spec_mono (hA.invAsid a _ asid hS.1.2.2.2.2.2.2) fun _ h => flush_of_sok (hwAsidInvalidate_ok _ _) hS h

/-- Nested TLB invalidation preserves the native machine view. -/
theorem invEpt_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (root mask : U64)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    ar.invalidate_ept a root mask ⦃ a' => TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ ⦄ := by
  rcases hS with ⟨⟨hs, he, hn, hi, ho, hk, har⟩, hp⟩
  exact WP.spec_mono (hA.invEpt a _ root mask har)
    (fun _ har' => ⟨⟨hs, he, hn, hi, ho, hk, har'⟩, hp⟩)

omit hA in
theorem flushTblOK_top (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (v : Fl4Spec.VSpaceRef) (pt : Fl4Spec.ObjRef)
    (asid : Fl4Spec.Asid) (hal : v &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (hk : ∃ f, σ.kheap pt = some (.archObj (.pageTable f))) : ¬ (Fl4Spec.flushTable (Z := Unit) vs v pt asid σ).2 := by
  obtain ⟨f, hf⟩ := hk; exact (flushTable_ok hal hf).1

set_option maxRecDepth 8000 in
theorem flushTbl_top (s : S) (a : A) (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (v : Fl4Spec.VSpaceRef)
    (pt : Fl4Spec.ObjRef) (asid : U64) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hal : v &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (hk : ∃ f, σ.kheap pt = some (.archObj (.pageTable f))) :
    ar.invalidate_asid a asid ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.flushTable (Z := Unit) vs v pt asid.bv σ).1 ∧
        TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a' σ' ⦄ := by
  obtain ⟨f, hf⟩ := hk
  refine WP.spec_mono (hA.invAsid a _ asid hS.1.2.2.2.2.2.2) fun a' h => ?_
  obtain ⟨-, ⟨⟨u, σ'⟩, hy⟩, h3⟩ := flushTable_ok (vs := vs) (asid := asid.bv) hal hf
  obtain ⟨ms, e, hum⟩ := h3 _ hy
  cases u
  simp only at e
  subst e
  exact ⟨_, hy, TopSR.machine' hS ms hum h⟩

/-! ## `set_vm_root` -/

/-- **`VsRootHyps` for the composite relation.** -/
theorem vsRootHyps_top : VsRootHyps st A ar (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  setVs s a σ ptr asid hS := WP.spec_mono (hA.setVspace a _ ptr asid hS.1.2.2.2.2.2.2) fun _ h =>
    TopSR.cr3 hS _ h
  setKernel s a σ hS := by
    unfold vspace.set_kernel_vm_root
    rw [kernel_root_eq]
    apply ok_bind_spec
    refine WP.spec_bind (hA.setVspace a _ _ 0#u64 hS.1.2.2.2.2.2.2) fun a' h => (WP.spec_ok _).2 ⟨rfl, ?_⟩
    have hk := hS.1.2.2.2.2.2.1
    unfold KRootRel at hk
    exact TopSR.cr3 hS _ (by rw [← hk]; exact h)

end

end

end Fl4Proofs.P3.Vs
