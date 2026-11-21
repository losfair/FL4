/-
P3 (DESIGN.md §9), VT-x: **the VT-x finalisation steps of the deletion at
`J`** (XTopJointDelR's `JFrVtHyp`, `jFrVt_of`, and `jFinAt_vt`), from
XTopJointFinVtOps' steps and XTopJointFinVt's frames `JAtZ.vtJ`/`vtHJ`. The
spec does not model the VT-x objects (DESIGN §5): its `finalise_cap` of an
EPT-mapped frame (an unmap of an ASID with no native root), an IO port, an
EPT or a VCPU cap keeps the state; FL4's writes land in VT-x words.

* `JVtHyps` [J]: at every `JAtZ` state of the typed heap:
  - `io`: the VCPU list's placement (`VtIoPlace`, as P1's `IoPortPlaceAt`;
    no l4v counterpart, the VT-x port's list);
  - `ept`: the EPT walks' placement (`VtEptPlace`, as P1's `EptPlace.find`;
    l4v `valid_vspace_objs` for the EPT tables);
  - `eptFr`: an EPT-mapped frame cap's ASID names no native PML4 in the
    spec (`find_vspace_for_asid` fails: its pool entry is guest-tagged,
    `nativeAsidRoot`; l4v `valid_cap` of the mapped frame, its mapping in the
    EPT of the ASID);
  (an EPT cap's range holding no object of `H` but `other` ones and its
    table non-null are no longer premises: `JAtZ.ept_obj`, `JAtZ.ept_ne0`,
    from `JPlaced.cobj`, ScPlace's `CapObjH`);
  - `vcpu` (`VtVcpuPlace`): a VCPU cap's VCPU is bound to no thread (its
    `TCB` word zero: l4v `sym_refs` of the VCPU–TCB binding, the threads
    being native, ScPlace's `JState.vcpu`), its list neighbours' link words
    VT-x words (the list's placement), its range holding no object of `H`
    but `other` ones (`pspace_distinct`).
* `JAtZ.frVtJ`: an EPT-mapped frame cap's `ept::unmap`, an owned IO port
  cap's `revoke_ports` (final or not), `JAtZ` after, the spec state kept.
* `JAtZ.finEptJ`: a final EPT cap's finalisation but a mapped root's
  (`EptK`: nothing when unmapped, `ept::unmap` of the entry of a mapped
  non-root table), the slot ready after (`EmptyReady.of_apartO`).
* `JAtZ.finVcpuJ`: a final VCPU cap's `vcpu::finalise` (`VcpuK`: the
  unlink from the VCPU list, `vcpu_finalise_vt`; `JAtZ.vtHJ`), the slot
  ready after.
* A final mapped EPT root cap is the VSpace finalisations' (VsFin's
  `fin_ept_root`, XTopJointFinVs's `JAtZ.finEptRootJ`): FL4's
  `vspace::delete_asid` clears the guest-tagged ASID pool entry, as the
  spec's `arch_finalise_cap` of a mapped level-0 `EPTCap` does by
  `deleteAsid`.
-/
import Fl4Proofs.P3.XTopJointFinVtOps
import Fl4Proofs.P3.XTopJointFinFrIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A slot is ready when no object of `H` but `other` ones meets its
cap's range** (`EmptyReady.of_apart` with the `other` objects, dead for
`DeadP`). -/
theorem EmptyReady.of_apartO {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64}
    (hap : ∀ q k, H q = some k → (∀ z, k ≠ .other z) →
      q.val + 2 ^ k.bits ≤ baseF (capV (L.mem s) x) ∨ topF (capV (L.mem s) x) < q.val) :
    EmptyReady (L := L) H G s x := by
  intro _ _
  refine fun lo hi hlh h1 h2 => Or.inr fun q hq => ?_
  · cases hk : H q with
    | none => exact deadP_none hk
    | some k =>
      by_cases ho : ∃ z, k = .other z
      · obtain ⟨z, rfl⟩ := ho
        exact ⟨fun e => (by rw [hk] at e; cases e), fun e => (by rw [hk] at e; cases e),
          fun e => (by rw [hk] at e; cases e), fun e => (by rw [hk] at e; cases e),
          fun z' e => (by rw [hk] at e; cases e)⟩
      · exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hap q k hk (fun z e => ho ⟨z, e⟩) with h | h <;> omega

/-- **A VCPU cap's VCPU at a `JAtZ` state** [J] (module docstring): bound to
no thread, its list neighbours' link words VT-x words, its range apart from
`H`'s objects but `other` ones. -/
structure VtVcpuPlace (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) (v : U64) :
    Prop where
  tcb0 : L.mem s (vTcbA v) = 0#u64
  prev : L.mem s (vPrevA v) ≠ 0#u64 → VtOut (L := L) Z H Cs s σ (P1.vNextA (L.mem s (vPrevA v)))
  next : L.mem s (P1.vNextA v) ≠ 0#u64 → VtOut (L := L) Z H Cs s σ (vPrevA (L.mem s (P1.vNextA v)))
  apart : ∀ q k, H q = some k → (∀ z, k ≠ .other z) →
    q.val + 2 ^ k.bits ≤ baseF (.Vcpu v) ∨ topF (.Vcpu v) < q.val

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VT-x placement facts at `J`** [J] (module docstring), at every
`JAtZ` state of the typed heap. -/
structure JVtHyps (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- The VCPU list's placement (as P1's `IoPortPlaceAt`), at a state with a
  VT-x cap in a slot (g2a: an owned IO-port cap's finalisation). -/
  io : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ x, IsSlot Z.th x → ¬ Vs.NativeCap (capV (L.mem s) x) → VtIoPlace (L := L) Z H Cs s σ
  /-- The EPT walks' placement (as P1's `EptPlace.find`), at a state with a
  VT-x cap in a slot (g2a: an EPT or EPT-mapped frame cap's finalisation). -/
  ept : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ x, IsSlot Z.th x → ¬ Vs.NativeCap (capV (L.mem s) x) → VtEptPlace (L := L) Z H Cs s σ
  /-- An EPT-mapped frame cap's ASID names no native PML4 in the spec. -/
  eptFr : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ x p sz r d asid va, IsSlot Z.th x → capV (L.mem s) x = .Frame p sz r d true true asid va →
      ∃ e, ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.error e, σ)}, False)
  /-- A VCPU cap's VCPU (`VtVcpuPlace`). -/
  vcpu : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ x v, IsSlot Z.th x → capV (L.mem s) x = .Vcpu v → VtVcpuPlace (L := L) Z H Cs s σ v

/-- **`JVtHyps` is a theorem** (g2a): every field's hypotheses name a VT-x cap
in a slot of a `JAtZ` state, which `JAtZ.ext.nat` (`JExt`, every slot's cap
`Vs.NativeCap`) rules out. So `JDelParts.vt` needs no premise. -/
theorem JVtHyps.ofExt (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : JVtHyps (L := L) arI AR th where
  io := fun _ _ _ _ _ _ _ _ _ _ J x hx hn => absurd (J.ext.nat x hx) hn
  ept := fun _ _ _ _ _ _ _ _ _ _ J x hx hn => absurd (J.ext.nat x hx) hn
  eptFr := fun _ _ _ _ _ _ _ _ _ _ J x _ _ _ _ _ _ hx hc => by
    have h := J.ext.nat x hx; rw [hc] at h; exact ((h : ¬ (true = true ∧ true = true)) ⟨rfl, rfl⟩).elim
  vcpu := fun _ _ _ _ _ _ _ _ _ _ J x _ hx hc => by
    have h := J.ext.nat x hx; rw [hc] at h; exact (h : False).elim

/-- **The post of a VT-x finalisation step at `J`**: the caps returned, the
spec's `finalise_cap` at the same state, `JAtZ` after at the same sets, the
slots and the kernel-state base kept. -/
abbrev VtPost (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S)
    (σ : Fl4Spec.State Unit) (c : capability.Cap) (b : Bool) (r : (capability.Cap × capability.Cap) × S × A) :
    Prop :=
  r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
    ((absCap r.1.1, absCap r.1.2), σ) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
    (∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ) ∧
    SlotsSame Z.th (L.mem s) (L.mem r.2.1) ∧ L.ksb r.2.1 = L.ksb s

end

/-- An EPT cap but a mapped root's. -/
def EptK (c : capability.Cap) : Prop := ∃ p lv m asid va, c = .Ept p lv m asid va ∧ ¬ (m = true ∧ lv = 0#u64)

/-- A VCPU cap. -/
def VcpuK (c : capability.Cap) : Prop := ∃ v, c = .Vcpu v

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- A slot's EPT or frame cap's objects (`JPlaced.cobj`). -/
theorem JAtZ.cobj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : IsSlot Z.th x) : Sched.CapObjH H (Sched.idleScW (L := L) s) (capV (L.mem s) x) := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl; exact hJ.cobj x hx

/-- **An EPT cap's range holds no object of `H` but `other` ones** (l4v
`valid_cap` with `pspace_distinct`; `JPlaced.cobj`). -/
theorem JAtZ.ept_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x p lv asid va : U64} {m : Bool} (hx : IsSlot Z.th x) (hcv : capV (L.mem s) x = .Ept p lv m asid va) :
    ∀ q k, H q = some k → (∀ z, k ≠ .other z) →
      q.val + 2 ^ k.bits ≤ baseF (.Ept p lv m asid va) ∨ topF (.Ept p lv m asid va) < q.val := by
  have h := J.cobj hx; rw [hcv] at h; exact h.2

/-- **An EPT cap names a non-null table** (l4v `valid_cap`: no object at 0;
`JPlaced.cobj`, `H` holding nothing at 0). -/
theorem JAtZ.ept_ne0 {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x p lv asid va : U64} {m : Bool} (hx : IsSlot Z.th x) (hcv : capV (L.mem s) x = .Ept p lv m asid va) :
    p ≠ 0#u64 := by
  have h := J.cobj hx; rw [hcv] at h
  obtain ⟨⟨n, hH, -⟩, -⟩ := h
  rintro rfl; rw [J.kern.h0] at hH; cases hH

set_option maxHeartbeats 4000000 in
/-- **The VT-x work of a finalisation at `J`** (module docstring), final or
not, from `ArchRefines` [P], `ARKeep` [P] and `JVtHyps` [J]. -/
theorem JAtZ.frVtJ [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (hK : ARKeep arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) Z.th s σ G)
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FrVtK c) (b : Bool) :
    objects.finalise_cap st arI s a c b false ⦃ VtPost (L := L) arI AR Z H Cs s σ c b ⦄ := by
  have hcv := capV_of_capAt hc
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  rcases hk with ⟨p, sz, r, d, asid, va, rfl⟩ | ⟨f, l, o, rfl, ho⟩
  · -- an EPT-mapped frame: `ept::unmap`, the spec's `unmap_page` doing nothing
    obtain ⟨e, hfv⟩ := hV.eptFr Z H Cs Ac Lst D s a σ rfl J _ p sz r d asid va hA'.isSlot hcv
    have hun : ((), σ) ∈ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv va.bv p.bv σ).1 := by
      rw [Vs.unmapPage_noVs hfv]; exact Set.mem_singleton _
    have hm : ((absCap .Null, absCap .Null), σ) ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Frame p sz r d true true asid va)) b σ).1 := by
      cases b <;> exact mem_bind_nd hun (Set.mem_singleton _)
    obtain ⟨i, hi⟩ : ∃ i, capability.FrameSize.bits sz = ok i := by cases sz <;> exact ⟨_, rfl⟩
    simp only [objects.finalise_cap, objects.finalise_cap_object, P1.plain_retire, bind_ok, ↓reduceIte, hi,
      ite_self]
    split
    · refine WP.spec_bind (ept_unmap_vt hA a har asid va p i false (X := VtOut (L := L) Z H Cs s σ)
        (fun x hx => hx.al) (hV.ept Z H Cs Ac Lst D s a σ rfl J _ hA'.isSlot (by rw [hcv]; simp [Vs.NativeCap]) asid)) ?_
      rintro ⟨s1, a1⟩ ⟨hw, har1⟩
      obtain ⟨J1, hSS, hks⟩ := J.vtJ hw har1
      try simp only [uncurry_apply_pair]
      exact (WP.spec_ok _).2 ⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, D, J1⟩, hSS, hks⟩
    · obtain ⟨J1, hSS, hks⟩ := J.vtJ (P1.WritesIn.refl s _) har
      try simp only [P1.plain_retire, ite_self, bind_ok, uncurry_apply_pair]
      exact (WP.spec_ok _).2 ⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, D, J1⟩, hSS, hks⟩
  · -- an owned IO port cap: `revoke_ports`
    have P := hV.io Z H Cs Ac Lst D s a σ rfl J _ hA'.isSlot (by rw [hcv]; exact ho)
    obtain ⟨c', ac, hc', hca, -⟩ := hDS.1.1.abs_cap hA'
    have hcw : CapWf (.IoPort f l o) := by rw [hc] at hc'; rw [eq_of_ok_eq hc']; exact hca.1
    simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    refine WP.spec_bind (revoke_ports_vt hK J P o f l) ?_
    rintro ⟨s1, a1⟩ ⟨hw, har1⟩
    obtain ⟨J1, hSS, hks⟩ := J.vtJ (hw.mono fun x hx => VIoW.vt P hx) har1
    try simp only [uncurry_apply_pair]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 ⟨rfl, trivial, trivial, Set.mem_singleton _, ⟨Ac, Lst, D, J1⟩, hSS, hks⟩
    · simp only [↓reduceIte]
      exact (WP.spec_ok _).2 ⟨rfl, trivial, hcw, Set.mem_singleton _, ⟨Ac, Lst, D, J1⟩, hSS, hks⟩

set_option maxHeartbeats 4000000 in
/-- **A final EPT cap's finalisation at `J`, but a mapped root's** (module
docstring), the slot ready after; from `ArchRefines` [P] and `JVtHyps` [J]. -/
theorem JAtZ.finEptJ (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {c : capability.Cap}
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : EptK c) :
    objects.finalise_cap st arI s a c true false ⦃ r =>
      VtPost (L := L) arI AR Z H Cs s σ c true r ∧ EmptyReady (L := L) H G r.2.1 (cslotAddr sl) ⦄ := by
  obtain ⟨p, lv, m, asid, va, rfl, hnr⟩ := hk
  have hcv := capV_of_capAt hc
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  have hap := J.ept_obj hA'.isSlot hcv
  have hm : ((absCap .Null, absCap .Null), σ) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Ept p lv m asid va)) true σ).1 := by
    cases m
    · exact Set.mem_singleton _
    · have hlv : ¬ lv.val = 0 := fun e => hnr ⟨rfl, UScalar.eq_of_val_eq (by rw [e]; rfl)⟩
      exact mem_bind_nd (x := ((), σ)) (show ((), σ) ∈ (Fl4Spec.NonDet.when (lv.val = 0)
        (Fl4Spec.deleteAsid (Z := Unit) asid.bv p.bv) σ).1 by rw [nd_when_false hlv]; exact Set.mem_singleton _)
        (Set.mem_singleton _)
  cases m
  · have he : objects.finalise_cap st arI s a (.Ept p lv false asid va) true false = ok ((.Null, .Null), s, a) := by
      simp [objects.finalise_cap, objects.finalise_cap_object, ept.finalise]
    rw [he, WP.spec_ok]
    obtain ⟨J1, hSS, hks⟩ := J.vtJ (P1.WritesIn.refl s _) har
    exact ⟨⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, D, J1⟩, hSS, hks⟩,
      EmptyReady.of_apartO (by rw [hcv]; exact hap)⟩
  · have hl0 : lv ≠ 0#u64 := fun e => hnr ⟨rfl, e⟩
    simp only [objects.finalise_cap, objects.finalise_cap_object, ept.finalise, bind_ok, ↓reduceIte, hl0]
    refine WP.spec_bind (ept_unmap_vt hA a har asid va p lv true (X := VtOut (L := L) Z H Cs s σ)
      (fun x hx => hx.al) (hV.ept Z H Cs Ac Lst D s a σ rfl J _ hA'.isSlot (by rw [hcv]; simp [Vs.NativeCap]) asid)) ?_
    rintro ⟨s1, a1⟩ ⟨hw, har1⟩
    obtain ⟨J1, hSS, hks⟩ := J.vtJ hw har1
    try simp only [uncurry_apply_pair]
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Ept p lv true asid va := by rw [hSS.capV hA'.isSlot, hcv]
    exact (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, D, J1⟩, hSS, hks⟩,
      EmptyReady.of_apartO (by rw [hcv1]; exact hap)⟩

set_option maxHeartbeats 4000000 in
/-- **A final VCPU cap's finalisation at `J`** (module docstring:
`vcpu_finalise_vt`, `JAtZ.vtHJ`), the slot ready after; from `ARKeep` [P]
and `JVtHyps` [J]. -/
theorem JAtZ.finVcpuJ (hK : ARKeep arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {c : capability.Cap}
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : VcpuK c) :
    objects.finalise_cap st arI s a c true false ⦃ r =>
      VtPost (L := L) arI AR Z H Cs s σ c true r ∧ EmptyReady (L := L) H G r.2.1 (cslotAddr sl) ⦄ := by
  obtain ⟨v, rfl⟩ := hk
  have hcv := capV_of_capAt hc
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨h0, hp, hn, hap⟩ := hV.vcpu Z H Cs Ac Lst D s a σ rfl J _ v hA'.isSlot hcv
  have hha : P1.Aligned (P1.vHeadA st s) := by
    have hf := J.kern.ksbFit
    have hal := J.kern.ksbAl
    have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val hf
    unfold P1.Aligned; rw [hv]; omega
  have hm : ((absCap .Null, absCap .Null), σ) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Vcpu v)) true σ).1 := Set.mem_singleton _
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (vcpu_finalise_vt hK v a har h0 hha (X := VtOut (L := L) Z H Cs s σ)
    (fun h => ⟨hp h, (hp h).al⟩) (fun h => ⟨hn h, (hn h).al⟩)) ?_
  rintro ⟨s1, a1⟩ ⟨hw, har1⟩
  obtain ⟨J1, hSS, hks⟩ := J.vtHJ hw har1
  try simp only [uncurry_apply_pair]
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Vcpu v := by rw [hSS.capV hA'.isSlot, hcv]
  exact (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, hm, J1, hSS, hks⟩,
    EmptyReady.of_apartO (by rw [hcv1]; exact hap)⟩

end

end

end Fl4Proofs.P3
