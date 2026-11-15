/-
P3 (DESIGN.md §9), VSpace: **`delete_asid` and `delete_asid_pool` without
the address-space switch as a hypothesis**: the switch is `set_vm_root_rel`.

`VsHyps` has the arch and other-subsystem hypotheses only (`stable`,
`invalOK`, `inval`, the current thread `curT`, and `root`: `set_vspace` /
`set_kernel_vm_root` against l4v's CR3). The relation carried is
`SRV th P SR := SR ∧ StateRel th ∧ Placed th ∧ VsSlotsDisj th P ∧ CurOK th`:
`CurOK` says the current thread is a TCB of the typed heap whose mapped
vtable cap has a non-zero ASID (l4v `valid_cap`). `VsHyps.toR` gives the
hypotheses of VsDel/VsDelPool for `SRV`.
-/
import Fl4Proofs.P3.VsRoot
import Fl4Proofs.P3.VsDelPool
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The current thread: a TCB of the typed heap, whose mapped vtable cap has
a non-zero ASID. -/
def CurOK (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ t : U64, t.bv = σ.curThread ∧ th t = some .tcb ∧
    ∀ p asid, capAt (L.mem s) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64

/-- `SR` with the CSpace relation, the placement and the current thread. -/
def SRV {A : Type} (th : TypedHeap) (P : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ StateRel th (L.mem s) σ ∧ Placed th ∧ VsSlotsDisj th P (L.ksb s) ∧ CurOK st th s σ

/-- The hypotheses of the ASID deletions (see the module docstring). -/
structure VsHyps (A : Type) (ar : machine.Arch A) (P : Set U64) (th : TypedHeap)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  stable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (VsWrite P (L.ksb s)) → VsStep σ σ' → SR s' a σ'
  invalOK : ∀ (asid vs : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit), ¬ (Fl4Spec.hwAsidInvalidate (Z := Unit) asid vs σ).2
  inval : ∀ s a σ (asid : U64) (vs : Fl4Spec.ObjRef), VsRel P (L.mem s) (L.ksb s) σ → SR s a σ →
    ar.invalidate_asid a asid ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.hwAsidInvalidate (Z := Unit) asid.bv vs σ).1 ∧
      SR s a' σ' ⦄
  invEpt : ∀ s a σ (root mask : U64), SR s a σ →
    ar.invalidate_ept a root mask ⦃ a' => SR s a' σ ⦄
  curT : ∀ s a σ, SR s a σ → sched.cur_thread st s ⦃ ct => ct.bv = σ.curThread ⦄
  root : VsRootHyps st A ar SR

end Defs

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A write to non-slot words keeps every slot's cap. -/
theorem capAt_of_writes {th : TypedHeap} (hPl : Placed th) {s s' : S} {W : U64 → Prop} (hW : WritesIn st s s' W)
    (hWs : ∀ b, W b → ¬ SlotW th b) (x : U64) (hx : IsSlot th x) : capAt (L.mem s') x = capAt (L.mem s) x := by
  obtain ⟨p, i, hpi, rfl⟩ := hx
  unfold capAt
  rw [hW.2.2 _ (hpi.al hPl) (fun h => hWs _ h ⟨_, ⟨p, i, hpi, rfl⟩, Or.inl rfl⟩),
    hW.2.2 _ (hpi.al8 hPl) (fun h => hWs _ h ⟨_, ⟨p, i, hpi, rfl⟩, Or.inr rfl⟩)]

theorem StateRel.ms {th : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit} (h : StateRel th m σ)
    (ms : Fl4Spec.MachineState) : StateRel th m { σ with machineState := ms } := ⟨h.cnode, h.tcb⟩

theorem StateRel.cr3 {th : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit} (h : StateRel th m σ)
    (c : Fl4Spec.Cr3) : StateRel th m (cr3Upd σ c) := ⟨h.cnode, h.tcb⟩

theorem StateRel.tab {th : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit} (h : StateRel th m σ)
    (t : Fl4Spec.AsidHighIndex → Option Fl4Spec.ObjRef) :
    StateRel th m { σ with archState := { σ.archState with x64AsidTable := t } } := ⟨h.cnode, h.tcb⟩

theorem VsRel.cr3 {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit} (h : VsRel P m ksb σ)
    (c : Fl4Spec.Cr3) : VsRel P m ksb (cr3Upd σ c) := ⟨h.1, h.2, h.3⟩

/-- **The hypotheses of VsDel/VsDelPool, for `SRV`.** -/
theorem VsHyps.toR {A : Type} {ar : machine.Arch A} {P : Set U64} {th : TypedHeap}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsHyps st A ar P th SR) :
    VsHypsR st A ar P (SRV st th P SR) where
  stable s s' a σ σ' := by
    rintro ⟨hS, hSt, hPl, hD, t, ht1, ht2, ht3⟩ hW hst
    have hWs : ∀ b, VsWrite P (L.ksb s) b → ¬ SlotW th b := hD
    have hcap := capAt_of_writes hPl hW hWs
    have hSt' : StateRel th (L.mem s') σ := StateRel.of_caps hSt hcap
    refine ⟨hH.stable s s' a σ σ' hS hW hst, ?_, hPl, by rw [hW.1]; exact hD, t, ?_, ht2, ?_⟩
    · rcases hst with ⟨p, f, f', hk, rfl⟩ | ⟨tb, rfl⟩
      · exact Vs.StateRel.upd_other hSt' hk _
      · exact Vs.StateRel.tab hSt' tb
    · rcases hst with ⟨p, f, f', hk, rfl⟩ | ⟨tb, rfl⟩ <;> exact ht1
    · intro p asid h
      rw [hcap _ ⟨t, 1, Or.inr ⟨ht2, by decide⟩, rfl⟩] at h
      exact ht3 p asid h
  invalOK := hH.invalOK
  inval s a σ asid vs hR := by
    rintro ⟨hS, hSt, hPl, hD, hC⟩
    refine WP.spec_mono (hH.inval s a σ asid vs hR hS) ?_
    rintro a' ⟨σ', hm, hS'⟩
    obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
    exact ⟨_, hm, hS', Vs.StateRel.ms hSt ms, hPl, hD, hC⟩
  invEpt s a σ root mask := by
    rintro ⟨hS, hSt, hPl, hD, hC⟩
    exact WP.spec_mono (hH.invEpt s a σ root mask hS)
      (fun _ hS' => ⟨hS', hSt, hPl, hD, hC⟩)
  vmRoot s a σ hR := by
    rintro ⟨hS, hSt, hPl, hD, t, ht1, ht2, ht3⟩
    refine WP.spec_bind (hH.curT s a σ hS) ?_
    rintro ct hct
    have htc : t = ct := eq_of_bv (ht1.trans hct.symm)
    subst htc
    refine WP.spec_mono (set_vm_root_rel hH.root s a σ hSt hR hS ht2 ht3) ?_
    rintro ⟨s', a'⟩ ⟨h1, c, hall, hS'⟩
    simp only at h1
    subst h1
    have hspec : ∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState = σ.archState →
        σ'.curThread = σ.curThread → specVmRootCur σ' = ({((), cr3Upd σ' c)}, False) := by
      intro σ' hk ha hc
      unfold specVmRootCur
      rw [nd_bind_one (show Fl4Spec.NonDet.gets _ σ' = ({(σ'.curThread, σ')}, False) from rfl), hc, ← ht1]
      exact hall σ' hk ha
    refine ⟨rfl, fun ms => ?_, cr3Upd σ c, ?_, VsRel.cr3 hR c, hS', Vs.StateRel.cr3 hSt c, hPl, hD, t, ht1, ht2, ht3⟩
    · rw [hspec { σ with machineState := ms } rfl rfl rfl]; exact id
    · rw [hspec σ rfl rfl rfl]; rfl

/-- **`delete_asid`** refines l4v `delete_asid` (see VsDel), with the
address-space switch proved. -/
theorem delete_asid_rel {A : Type} {ar : machine.Arch A} {P : Set U64} {th : TypedHeap}
    {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hP : VsPlaced P (L.ksb s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : SRV st th P SR s a σ) (asid root : U64) (hr0 : root ≠ 0#u64) :
    vspace.delete_asid st ar s a asid root ⦃ r =>
      ¬ (Fl4Spec.deleteAsid (Z := Unit) asid.bv root.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.deleteAsid (Z := Unit) asid.bv root.bv σ).1 ∧
        VsRel P (L.mem r.1) (L.ksb r.1) σ' ∧ SRV st th P SR r.1 r.2 σ' ∧ VsZeroW st P s r.1 ⦄ :=
  delete_asid_relR hH.toR s a σ hP hR hS asid root hr0

/-- **`delete_asid_pool`** refines l4v `delete_asid_pool` (see VsDelPool),
with the address-space switch proved. -/
theorem delete_asid_pool_rel {A : Type} {ar : machine.Arch A} {P : Set U64} {th : TypedHeap}
    {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hP : VsPlaced P (L.ksb s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : SRV st th P SR s a σ) (base pool : U64) (hb : base.val % 512 = 0)
    (hp0 : pool ≠ 0#u64) :
    vspace.delete_asid_pool st ar s a base pool ⦃ r =>
      ¬ (Fl4Spec.deleteAsidPool (Z := Unit) base.bv pool.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.deleteAsidPool (Z := Unit) base.bv pool.bv σ).1 ∧
        VsRel P (L.mem r.1) (L.ksb r.1) σ' ∧ SRV st th P SR r.1 r.2 σ' ∧ VsZeroW st P s r.1 ⦄ :=
  delete_asid_pool_relR hH.toR s a σ hP hR hS base pool hb hp0

end

end

end Fl4Proofs.P3.Vs
