/-
P3 (DESIGN.md §9), VSpace: **`set_vm_root`** against l4v `set_vm_root`.

l4v reads the thread's vtable cap; for a mapped PML4 cap whose ASID's
lookup (`find_vspace_for_asid`) gives that PML4 it switches CR3 to it
(`make_cr3 (addrFromPPtr pml4) asid`, only if different), otherwise to the
global PML4 with ASID 0. FL4 does the same with `Arch::set_vspace`; the
correspondence of `set_vspace` (and of `set_kernel_vm_root`, FL4's switch to
the kernel's root) with the spec's CR3 is a hypothesis on the arch relation
(`VsRootHyps`).

* `setVmRoot_mapped`, `setVmRoot_other`: the spec's single outcome, a new
  CR3 (`cr3Upd σ (rootCr3 …)`);
* `set_vm_root_rel`: FL4's `set_vm_root t` keeps memory and is matched by it.
-/
import Fl4Proofs.P3.VsAssignRel
import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

/-- The state with CR3 `c`. -/
def cr3Upd (σ : State Unit) (c : Cr3) : State Unit :=
  { σ with archState := { σ.archState with x64CurrentCr3 := c } }

/-- The global address space's CR3. -/
def globCr3 (σ : State Unit) : Cr3 := makeCr3 (addrFromKPPtr σ.archState.x64GlobalPml4) 0

/-- The CR3 `set_vm_root` switches to, given the lookup's result. -/
def rootCr3 (σ : State Unit) (p : ObjRef) (asid : Asid) : Except LookupFailure ObjRef → Cr3
  | .ok r => if p = r then makeCr3 (addrFromPPtr p) asid else globCr3 σ
  | .error _ => globCr3 σ

theorem tcbCnodeMap_one (x : Tcb) : tcbCnodeMap x (tcbCnodeIndex 1) = some x.tcbVtable := by
  unfold tcbCnodeMap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self]

theorem getCap_tcb_one {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    getCap (Z := Unit) (t, tcbCnodeIndex 1) σ = ({(x.tcbVtable, σ)}, False) := by
  unfold getCap
  dsimp only
  rw [nd_bind_one (getObject_eq hk)]
  dsimp only
  rw [nd_pure_bind', tcbCnodeMap_one]
  rfl

theorem cr3Upd_self (σ : State Unit) : cr3Upd σ σ.archState.x64CurrentCr3 = σ := rfl

theorem global_eq (σ : State Unit) :
    (do
      let g ← NonDet.gets fun s : State Unit => s.archState.x64GlobalPml4
      setCurrentVspaceRoot (Z := Unit) (addrFromKPPtr g) 0) σ = ({((), cr3Upd σ (globCr3 σ))}, False) := by
  rw [nd_bind_one (show NonDet.gets _ σ = ({(σ.archState.x64GlobalPml4, σ)}, False) from rfl)]
  rfl

theorem catch_ok {α ε : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} {σ σ' : State Unit}
    {a : α} (hm : ExceptT.run m σ = ({(.ok a, σ')}, False)) : NonDetE.catch m h σ = ({(a, σ')}, False) := by
  unfold NonDetE.catch
  rw [nd_bind_one' hm]
  rfl

theorem catch_err {α ε : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} {σ σ' : State Unit}
    {e : ε} (hm : ExceptT.run m σ = ({(.error e, σ')}, False)) : NonDetE.catch m h σ = h e σ' := by
  unfold NonDetE.catch
  rw [nd_bind_one' hm]

theorem setVmRoot_other {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hv : ∀ p asid, x.tcbVtable ≠ .archObjectCap (.pml4Cap p (some asid))) :
    setVmRoot (Z := Unit) t σ = ({((), cr3Upd σ (globCr3 σ))}, False) := by
  unfold setVmRoot
  rw [nd_pure_bind', nd_bind_one (getCap_tcb_one hk)]
  have hm : ∀ (c : Cap), (∀ p asid, c ≠ .archObjectCap (.pml4Cap p (some asid))) →
      NonDetE.catch (match c with
        | .archObjectCap (.pml4Cap pml4 (some asid)) => do
            let pml4' ← findVspaceForAsid (Z := Unit) asid
            NonDetE.whenE (pml4 ≠ pml4') <| NonDetE.throwError .invalidRoot
            let curCr3 ← NonDetE.liftE getCurrentCr3
            NonDetE.whenE (curCr3 ≠ makeCr3 (addrFromPPtr pml4) asid) <|
              NonDetE.liftE <| setCurrentCr3 <| makeCr3 (addrFromPPtr pml4) asid
        | _ => NonDetE.throwError .invalidRoot)
        (fun _ => do
          let globalPml4 ← NonDet.gets fun s : State Unit => s.archState.x64GlobalPml4
          setCurrentVspaceRoot (addrFromKPPtr globalPml4) 0) σ = ({((), cr3Upd σ (globCr3 σ))}, False) := by
    intro c hc
    rw [catch_err (e := LookupFailure.invalidRoot) (σ' := σ)]
    · exact global_eq σ
    · cases c
      all_goals try rfl
      rename_i ac
      cases ac
      all_goals try rfl
      rename_i p o
      cases o
      · rfl
      · rename_i asid; exact absurd rfl (hc p asid)
  exact hm _ hv

theorem setVmRoot_mapped {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {p asid : ObjRef} (hv : x.tcbVtable = .archObjectCap (.pml4Cap p (some asid)))
    {res : Except LookupFailure ObjRef} (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(res, σ)}, False)) :
    setVmRoot (Z := Unit) t σ = ({((), cr3Upd σ (rootCr3 σ p asid res))}, False) := by
  unfold setVmRoot
  rw [nd_pure_bind', nd_bind_one (getCap_tcb_one hk), hv]
  dsimp only
  cases res with
  | error e =>
    rw [catch_err (runE_bind_err hf)]
    exact global_eq σ
  | ok r =>
    by_cases hpr : p = r
    · subst hpr
      have h1 := runE_bind_ok (f := fun pml4' => do
          NonDetE.whenE (p ≠ pml4') <| NonDetE.throwError (σ := State Unit) LookupFailure.invalidRoot
          let curCr3 ← NonDetE.liftE getCurrentCr3
          NonDetE.whenE (curCr3 ≠ makeCr3 (addrFromPPtr p) asid) <|
            NonDetE.liftE <| setCurrentCr3 <| makeCr3 (addrFromPPtr p) asid) hf
      rw [runE_bind_ok (runE_whenE_false (by simp) _ σ),
        runE_bind_ok (runE_liftE (show getCurrentCr3 (Z := Unit) σ = ({(σ.archState.x64CurrentCr3, σ)}, False) from rfl))] at h1
      by_cases hc : σ.archState.x64CurrentCr3 = makeCr3 (addrFromPPtr p) asid
      · rw [runE_whenE_false (by simpa using hc)] at h1
        rw [catch_ok h1]
        simp only [rootCr3, ↓reduceIte]
        rw [← hc, cr3Upd_self]
      · rw [runE_whenE_true hc, runE_liftE (show setCurrentCr3 (Z := Unit) (makeCr3 (addrFromPPtr p) asid) σ =
          ({((), cr3Upd σ (makeCr3 (addrFromPPtr p) asid))}, False) from rfl)] at h1
        rw [catch_ok h1]
        simp only [rootCr3, ↓reduceIte]
    · have h1 := runE_bind_ok (f := fun pml4' => do
          NonDetE.whenE (p ≠ pml4') <| NonDetE.throwError (σ := State Unit) LookupFailure.invalidRoot
          let curCr3 ← NonDetE.liftE getCurrentCr3
          NonDetE.whenE (curCr3 ≠ makeCr3 (addrFromPPtr p) asid) <|
            NonDetE.liftE <| setCurrentCr3 <| makeCr3 (addrFromPPtr p) asid) hf
      have h2 := h1.trans (runE_bind_err (by rw [runE_whenE_true hpr]; exact runE_throw _ σ))
      rw [catch_err h2, global_eq]
      simp only [rootCr3, hpr, ↓reduceIte]

end Spec


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

unseal Aeneas.Std.Result

/-- `find_vspace_for_asid`, against l4v in every state related to FL4's. -/
theorem find_vspace_for_asid_all {P : Set U64} (s : S) (asid : U64) (h0 : asid ≠ 0#u64) :
    vspace.find_vspace_for_asid st s asid ⦃ r => ∀ σ : Fl4Spec.State Unit, VsRel P (L.mem s) (L.ksb s) σ →
      ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(fvRes r, σ)}, False) ⦄ := by
  have heq : ∃ r, vspace.find_vspace_for_asid st s asid = ok r := by
    refine Aeneas.Data.Coinductive.DWP.induction (θ := WP.effectWP)
      (P := fun (m : Result (core.result.Result U64 error.LookupFault)) (_ : Unit) => ∃ r, m = ok r) (fun v _ _ => ⟨v, rfl⟩) ?_
      (P0.vspace.find_vspace_for_asid.p0 st s asid L.total)
    intro effect k u hf
    exact False.elim hf
  obtain ⟨r, heq⟩ := heq
  rw [heq, WP.spec_ok]
  intro σ hR
  have hr := find_vspace_for_asid_rel s σ hR asid h0
  rwa [heq, WP.spec_ok] at hr

end


section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The arch side of switching address space: FL4's `Arch::set_vspace ptr
asid` is l4v's CR3 `make_cr3 (addrFromPPtr ptr) asid`, and FL4's
`set_kernel_vm_root` is l4v's switch to the global PML4. -/
structure VsRootHyps (A : Type) (ar : machine.Arch A) (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  setVs : ∀ s a σ (ptr asid : U64), SR s a σ → ar.set_vspace a ptr asid ⦃ a' =>
    SR s a' (cr3Upd σ (Fl4Spec.makeCr3 (Fl4Spec.addrFromPPtr ptr.bv) asid.bv)) ⦄
  setKernel : ∀ s a σ, SR s a σ → vspace.set_kernel_vm_root st ar s a ⦃ r => r.1 = s ∧ SR s r.2 (cr3Upd σ (globCr3 σ)) ⦄

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem tcb_slot_vtable (t : U64) : obj.Tcb.slot t layout.tcb.SLOT_VTABLE = ok (slotOf t 1) := by
  unfold obj.Tcb.slot layout.tcb.SLOT_VTABLE layout.cte.SIZE
  simp only [lift, bind_ok]
  congr 1

/-- **`set_vm_root t`** keeps memory and refines l4v `set_vm_root t`: in
every state with the same heap and arch state (l4v's `set_vm_root` reads
nothing else), the spec's single outcome sets CR3 to `c`, and FL4's arch
state is related to the one with CR3 `c`. -/
theorem set_vm_root_rel {A : Type} {ar : machine.Arch A} {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsRootHyps st A ar SR) {th : TypedHeap} {P : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hSt : StateRel th (L.mem s) σ) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : SR s a σ) {t : U64}
    (ht : th t = some .tcb)
    (hasid : ∀ p asid, capAt (L.mem s) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64) :
    vspace.set_vm_root st ar s a t ⦃ r => r.1 = s ∧ ∃ c : Fl4Spec.Cr3,
      (∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState = σ.archState →
        Fl4Spec.setVmRoot (Z := Unit) t.bv σ' = ({((), cr3Upd σ' c)}, False)) ∧
      SR s r.2 (cr3Upd σ c) ⦄ := by
  obtain ⟨x, hkx, hsl⟩ := hSt.tcb t ht
  obtain ⟨c, ac, hc, hac, hca⟩ := hsl 1 (by decide)
  rw [tcbCnodeMap_one] at hac
  have hv : x.tcbVtable = absCap c := by injection hac with h; rw [h, hca.2]
  have hc' : capAt (L.mem s) (slotOf t 1) = ok c := hc
  have kern : (∀ p asid, x.tcbVtable ≠ .archObjectCap (.pml4Cap p (some asid))) →
      vspace.set_kernel_vm_root st ar s a ⦃ r => r.1 = s ∧ ∃ c : Fl4Spec.Cr3,
        (∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState = σ.archState →
          Fl4Spec.setVmRoot (Z := Unit) t.bv σ' = ({((), cr3Upd σ' c)}, False)) ∧
        SR s r.2 (cr3Upd σ c) ⦄ := fun hv' =>
    WP.spec_mono (hH.setKernel s a σ hS) fun r ⟨h1, h2⟩ => ⟨h1, globCr3 σ, fun σ' hk ha => by
      rw [setVmRoot_other (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv']
      unfold globCr3; rw [ha], h2⟩
  have hVs : ∀ σ' : Fl4Spec.State Unit, σ'.kheap = σ.kheap → σ'.archState = σ.archState →
      VsRel P (L.mem s) (L.ksb s) σ' := fun σ' hk ha =>
    hR.frame (fun _ _ => rfl) (by rw [ha]) (fun p _ => by rw [hk])
  unfold vspace.set_vm_root
  rw [tcb_slot_vtable]
  apply ok_bind_spec
  rw [slot_cap_eq, hc']
  apply ok_bind_spec
  cases c with
  | Pml4 ptr b asid =>
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact kern (by rw [hv]; simp [absCap])
    | true =>
      simp only [↓reduceIte]
      have hv1 : x.tcbVtable = .archObjectCap (.pml4Cap ptr.bv (some asid.bv)) := by rw [hv]; rfl
      refine WP.spec_bind (find_vspace_for_asid_all (P := P) s asid (hasid ptr asid hc')) ?_
      rintro r hr
      cases r with
      | Ok r1 =>
        dsimp only
        by_cases hpr : r1 = ptr
        · subst hpr
          simp only [↓reduceIte]
          refine WP.spec_bind (hH.setVs s a σ r1 asid hS) fun a1 h => (WP.spec_ok _).2 ⟨rfl, _, fun σ' hk ha => ?_, h⟩
          rw [setVmRoot_mapped (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv1 (hr σ' (hVs σ' hk ha))]
          simp [rootCr3, fvRes]
        · simp only [hpr, ↓reduceIte]
          refine WP.spec_mono (hH.setKernel s a σ hS) fun r ⟨h1, h2⟩ => ⟨h1, globCr3 σ, fun σ' hk ha => ?_, h2⟩
          rw [setVmRoot_mapped (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv1 (hr σ' (hVs σ' hk ha))]
          have hne : ptr.bv ≠ r1.bv := fun h => hpr (eq_of_bv h).symm
          simp only [rootCr3, fvRes, hne, ↓reduceIte]
          unfold globCr3; rw [ha]
      | Err e =>
        dsimp only
        refine WP.spec_mono (hH.setKernel s a σ hS) fun r ⟨h1, h2⟩ => ⟨h1, globCr3 σ, fun σ' hk ha => ?_, h2⟩
        rw [setVmRoot_mapped (show σ'.kheap t.bv = _ by rw [hk]; exact hkx) hv1 (hr σ' (hVs σ' hk ha))]
        simp only [rootCr3, fvRes]
        unfold globCr3; rw [ha]
  | _ => exact kern (by rw [hv]; simp [absCap])

end

end

end Fl4Proofs.P3.Vs
