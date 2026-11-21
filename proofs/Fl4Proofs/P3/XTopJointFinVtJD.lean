/-
P3 (DESIGN.md §9), CSpace: **the VT-x finalisations at `J` keeping the dead
set** (XTopJointFinVtJ's `JAtZ.finEptJ` and `JAtZ.finVcpuJ` with `VtPostD`:
`VtPost` at the same dead set; `JAtZ.vtJ` keeps it, `JAtZ.vtHJD`), for the
loop at `WJL` (XTopJointWJLFin).
-/
import Fl4Proofs.P3.XTopJointFinVtJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`VtPost` at the same dead set.** -/
abbrev VtPostD (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S)
    (σ : Fl4Spec.State Unit) (c : capability.Cap) (b : Bool) (r : (capability.Cap × capability.Cap) × S × A) :
    Prop :=
  r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
    ((absCap r.1.1, absCap r.1.2), σ) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
    (∃ (Ac' : Set U64) (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.2.1 r.2.2 σ) ∧
    SlotsSame Z.th (L.mem s) (L.mem r.2.1) ∧ L.ksb r.2.1 = L.ksb s

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A final EPT cap's finalisation at `J`, but a mapped root's** (module
docstring), the slot ready after; from `ArchRefines` [P] and `JVtHyps` [J]. -/
theorem JAtZ.finEptJD (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {c : capability.Cap}
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : EptK c) :
    objects.finalise_cap st arI s a c true false ⦃ r =>
      VtPostD (L := L) arI AR Z H Cs D s σ c true r ∧ EmptyReady (L := L) H G r.2.1 (cslotAddr sl) ⦄ := by
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
    exact ⟨⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, J1⟩, hSS, hks⟩,
      EmptyReady.of_apartO (by rw [hcv]; exact hap)⟩
  · have hl0 : lv ≠ 0#u64 := fun e => hnr ⟨rfl, e⟩
    simp only [objects.finalise_cap, objects.finalise_cap_object, ept.finalise, bind_ok, ↓reduceIte, hl0]
    refine WP.spec_bind (ept_unmap_vt hA a har asid va p lv true (X := VtOut (L := L) Z H Cs s σ)
      (fun x hx => hx.al) (hV.ept Z H Cs Ac Lst D s a σ rfl J _ hA'.isSlot (by rw [hcv]; simp [Vs.NativeCap]) asid)) ?_
    rintro ⟨s1, a1⟩ ⟨hw, har1⟩
    obtain ⟨J1, hSS, hks⟩ := J.vtJ hw har1
    try simp only [uncurry_apply_pair]
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Ept p lv true asid va := by rw [hSS.capV hA'.isSlot, hcv]
    exact (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, J1⟩, hSS, hks⟩,
      EmptyReady.of_apartO (by rw [hcv1]; exact hap)⟩

set_option maxHeartbeats 4000000 in
/-- **A final VCPU cap's finalisation at `J`** (module docstring:
`vcpu_finalise_vt`, `JAtZ.vtHJ`), the slot ready after; from `ARKeep` [P]
and `JVtHyps` [J]. -/
theorem JAtZ.finVcpuJD (hK : ARKeep arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {c : capability.Cap}
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : VcpuK c) :
    objects.finalise_cap st arI s a c true false ⦃ r =>
      VtPostD (L := L) arI AR Z H Cs D s σ c true r ∧ EmptyReady (L := L) H G r.2.1 (cslotAddr sl) ⦄ := by
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
  obtain ⟨J1, hSS, hks⟩ := J.vtHJD hw har1
  try simp only [uncurry_apply_pair]
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Vcpu v := by rw [hSS.capV hA'.isSlot, hcv]
  exact (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, hm, J1, hSS, hks⟩,
    EmptyReady.of_apartO (by rw [hcv1]; exact hap)⟩

set_option maxHeartbeats 4000000 in
/-- `JAtZ.frVtJ` at the same dead set. -/
theorem JAtZ.frVtJD [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (hK : ARKeep arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : JVtHyps (L := L) arI AR Z.th)
    {G : MdbGhost} {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) Z.th s σ G)
    (hA' : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FrVtK c) (b : Bool) :
    objects.finalise_cap st arI s a c b false ⦃ VtPostD (L := L) arI AR Z H Cs D s σ c b ⦄ := by
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
      exact (WP.spec_ok _).2 ⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, J1⟩, hSS, hks⟩
    · obtain ⟨J1, hSS, hks⟩ := J.vtJ (P1.WritesIn.refl s _) har
      try simp only [P1.plain_retire, ite_self, bind_ok, uncurry_apply_pair]
      exact (WP.spec_ok _).2 ⟨rfl, trivial, trivial, hm, ⟨Ac, Lst, J1⟩, hSS, hks⟩
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
      exact (WP.spec_ok _).2 ⟨rfl, trivial, trivial, Set.mem_singleton _, ⟨Ac, Lst, J1⟩, hSS, hks⟩
    · simp only [↓reduceIte]
      exact (WP.spec_ok _).2 ⟨rfl, trivial, hcw, Set.mem_singleton _, ⟨Ac, Lst, J1⟩, hSS, hks⟩

end

end

end Fl4Proofs.P3
