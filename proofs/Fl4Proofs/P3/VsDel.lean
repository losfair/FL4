/-
P3 (DESIGN.md §9), VSpace: **`delete_asid`** against l4v `delete_asid`.

The TLB invalidation and the address-space switch are hypotheses (`VsHypsR`):
* `inval`: FL4's `Arch::invalidate_asid a asid` is matched by one outcome of
  l4v `hw_asid_invalidate asid vspace` (a machine operation), keeping `SR`;
  `invalOK`: the spec's machine operation does not fail;
* `vmRoot`: FL4's `set_vm_root` of the current thread is matched by one
  outcome of l4v `set_vm_root cur_thread`, which fails in no machine state;
* `stable`: `SR` (the other subsystems and the arch state) is kept by writes
  to the ASID table and pool words and the matching spec changes.

`VsPlaced` places the ghost pools: 4K-aligned, not overlapping the table.
-/
import Fl4Proofs.P3.VsRel
import Fl4Proofs.P3.CapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section
attribute [local instance_reducible] UScalar.cMax UScalar.rMax U64.rMax

/-- Placement of the ASID table and the ghost pools. -/
structure VsPlaced (P : Set U64) (ksb : U64) : Prop where
  ksb_al : ksb.val % 8 = 0
  ksb_fit : ksb.val + 288000 + 16384 ≤ 2 ^ 64
  pal : ∀ p ∈ P, p.val % 4096 = 0 ∧ p.val + 4096 ≤ 2 ^ 64
  ptab : ∀ p ∈ P, p.val + 4096 ≤ ksb.val + 288000 ∨ ksb.val + 288000 + 16384 ≤ p.val

theorem atA_val {ksb hi : U64} (hk : ksb.val + 288000 + 16384 ≤ 2 ^ 64) (h : hi.val < 2048) :
    (atA ksb hi).val = ksb.val + 288000 + 8 * hi.val := by
  unfold atA
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  omega

theorem peA_val {p lo : U64} (hp : p.val + 4096 ≤ 2 ^ 64) (h : lo.val < 512) :
    (peA p lo).val = p.val + 8 * lo.val := by
  unfold peA
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  omega

/-- The words of the ASID table and the pools. -/
def VsWrite (P : Set U64) (ksb : U64) (b : U64) : Prop :=
  (∃ hi : U64, hi.val < 2048 ∧ b = atA ksb hi) ∨ (∃ p ∈ P, ∃ lo : U64, lo.val < 512 ∧ b = peA p lo)

/-- The spec changes of the ASID code: an ASID pool's contents, or the ASID
table. -/
def VsStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  (∃ p f f', σ.kheap p = some (.archObj (.asidPool f)) ∧ σ' = updK σ p (.archObj (.asidPool f'))) ∨
  (∃ t, σ' = { σ with archState := { σ.archState with x64AsidTable := t } })

section Spec
open Fl4Spec

/-- The spec's `set_vm_root` of the current thread. -/
def specVmRootCur : SMonad Unit Unit := do
  let tcb ← NonDet.gets fun s : State Unit => s.curThread
  setVmRoot tcb

/-- Deleting either kind of ASID entry; guest cache state is outside the
native machine-state relation, while its pool slot remains observable. -/
def daBody (asid : Asid) (root poolPtr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : SMonad Unit Unit :=
  match pool (asidLowBitsOf asid) with
  | none => pure ()
  | some entry => NonDet.when (asidEntryRoot entry = root) <| do
      if entry &&& 1 = 0 then hwAsidInvalidate asid root else pure ()
      let pool' ← pure (Function.update pool (asidLowBitsOf asid) none)
      setAsidPool poolPtr pool'
      if entry &&& 1 = 0 then specVmRootCur else pure ()

theorem nd_mem_bind {σ' α β : Type} {m : NonDet σ' α} {f : α → NonDet σ' β} {s s1 s2 : σ'} {a : α} {b : β}
    (h1 : (a, s1) ∈ (m s).1) (h2 : (b, s2) ∈ (f a s1).1) : (b, s2) ∈ ((m >>= f) s).1 := by
  rw [nd_bind_apply']; exact ⟨(a, s1), h1, h2⟩

theorem nd_nofail_bind {σ' α β : Type} {m : NonDet σ' α} {f : α → NonDet σ' β} {s : σ'}
    (h1 : ¬ (m s).2) (h2 : ∀ x ∈ (m s).1, ¬ (f x.1 x.2).2) : ¬ ((m >>= f) s).2 := by
  rw [nd_bind_apply']
  rintro (h | ⟨x, hx, hf⟩)
  · exact h1 h
  · exact h2 x hx hf

/-- The outcomes of a machine operation only change the machine state. -/
theorem doMachineOp_mem {α : Type} {mop : NonDet MachineState α} {σ σ' : State Unit} {r : α}
    (h : (r, σ') ∈ (doMachineOp (Z := Unit) mop σ).1) : ∃ ms, σ' = { σ with machineState := ms } := by
  unfold doMachineOp at h
  simp only [nd_bind_apply', NonDet.gets, NonDet.selectF, NonDet.modify, Set.mem_setOf_eq,
    Set.mem_singleton_iff] at h
  obtain ⟨x, rfl, y, ⟨-, hy⟩, z, rfl, hz⟩ := h
  subst hy
  simp only [pure, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
  exact ⟨_, hz.2⟩

theorem ndpure_bind {σ' α β : Type} (a : α) (f : α → NonDet σ' β) (s : σ') :
    (NonDet.pure a >>= f) s = f a s := nd_pure_bind' a f s

theorem setAsidPool_eq {σ : State Unit} {p : ObjRef} {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) (f' : AsidLowIndex → Option ObjRef) :
    setAsidPool (Z := Unit) p f' σ = ({((), updK σ p (.archObj (.asidPool f')))}, False) :=
  setObject_eq hk rfl

end Spec

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The ASID deletions' memory effect**: the kernel base and core kept;
a word changed only if it is an ASID-table or pool word, and then to 0. -/
def VsZeroW (P : Set U64) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
    ∀ b, Aligned b → L.mem s' b ≠ L.mem s b → VsWrite P (L.ksb s) b ∧ L.mem s' b = 0#u64

/-- The arch effects and the other subsystems (see the module docstring). -/
structure VsHypsR (A : Type) (ar : machine.Arch A) (P : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  stable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (VsWrite P (L.ksb s)) → VsStep σ σ' → SR s' a σ'
  invalOK : ∀ (asid vs : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit), ¬ (Fl4Spec.hwAsidInvalidate (Z := Unit) asid vs σ).2
  inval : ∀ s a σ (asid : U64) (vs : Fl4Spec.ObjRef), VsRel P (L.mem s) (L.ksb s) σ → SR s a σ →
    ar.invalidate_asid a asid ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.hwAsidInvalidate (Z := Unit) asid.bv vs σ).1 ∧
      SR s a' σ' ⦄
  invEpt : ∀ s a σ (root mask : U64), SR s a σ →
    ar.invalidate_ept a root mask ⦃ a' => SR s a' σ ⦄
  vmRoot : ∀ s a σ, VsRel P (L.mem s) (L.ksb s) σ → SR s a σ →
    (do
      let ct ← sched.cur_thread st s
      vspace.set_vm_root st ar s a ct) ⦃ r => r.1 = s ∧
      (∀ ms, ¬ (specVmRootCur { σ with machineState := ms }).2) ∧
      ∃ σ', ((), σ') ∈ (specVmRootCur σ).1 ∧ VsRel P (L.mem r.1) (L.ksb r.1) σ' ∧ SR r.1 r.2 σ' ⦄

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem VsZeroW.refl (P : Set U64) (s : S) : VsZeroW st P s s :=
  ⟨rfl, rfl, fun _ _ h => absurd rfl h⟩

/-- One zero write to an ASID-table or pool word. -/
theorem VsZeroW.wr {P : Set U64} (s : S) {b : U64} (hb : Aligned b) (hw : VsWrite P (L.ksb s) b) :
    VsZeroW st P s (L.wr s b 0#u64) := by
  refine ⟨by simp, by simp, fun c hc hne => ?_⟩
  by_cases e : b = c
  · subst e; exact ⟨hw, L.mem_wr_same hb⟩
  · exact absurd (L.mem_wr_ne hb hc (fun h => e (UScalar.eq_of_val_eq h))) hne

theorem ucast9_inj {a b : U64} (ha : a.val < 512) (hb : b.val < 512)
    (h : (Fl4Spec.ucast 9 a.bv : BitVec 9) = Fl4Spec.ucast 9 b.bv) : a = b := by
  apply UScalar.eq_of_val_eq
  have := congrArg BitVec.toNat h
  simp only [Fl4Spec.ucast, BitVec.toNat_setWidth] at this
  show a.bv.toNat = b.bv.toNat
  have e1 : a.bv.toNat % 2 ^ 9 = a.bv.toNat := Nat.mod_eq_of_lt (by show a.val < _; omega)
  have e2 : b.bv.toNat % 2 ^ 9 = b.bv.toNat := Nat.mod_eq_of_lt (by show b.val < _; omega)
  omega

/-- The relation after a write to word `lo` of the pool at `p`. -/
theorem VsRel.upd_entry {P : Set U64} {m m' : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit}
    (hP : VsPlaced P ksb) (hR : VsRel P m ksb σ) {p : U64} (hp : p ∈ P) {f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef}
    (hk : σ.kheap p.bv = some (.archObj (.asidPool f))) {lo : U64} (hlo : lo.val < 512) (v : U64)
    (hm : ∀ b, Aligned b → b ≠ peA p lo → m' b = m b) (hme : m' (peA p lo) = v) :
    VsRel P m' ksb (updK σ p.bv (.archObj (.asidPool (Function.update f (Fl4Spec.ucast 9 lo.bv) (optRef v))))) := by
  obtain ⟨pa, pf⟩ := hP.pal p hp
  have hpv := peA_val pf hlo
  have htab : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi) := by
    intro hi h
    have hv := atA_val hP.ksb_fit h
    refine hm _ (by show _ % 8 = 0; rw [hv]; have := hP.ksb_al; omega) fun e => ?_
    have := congrArg UScalar.val e
    rw [hv, hpv] at this
    have := hP.ptab p hp; omega
  refine ⟨fun hi h => ?_, fun hi h h0 => ?_, fun q hq => ?_⟩
  · rw [htab hi h]; exact hR.table hi h
  · rw [htab hi h] at h0 ⊢; exact hR.tmem hi h h0
  · obtain ⟨g, hg, hgf⟩ := hR.pool q hq
    obtain ⟨qa, qf⟩ := hP.pal q hq
    by_cases e : q = p
    · subst e
      rw [hk] at hg; injection hg with hg; injection hg with hg; injection hg with hg; subst hg
      refine ⟨Function.update f (Fl4Spec.ucast 9 lo.bv) (optRef v), by simp, fun lo' h' => ?_⟩
      by_cases el : lo' = lo
      · subst el; rw [Function.update_self, hme]
      · rw [Function.update_of_ne (fun h => el (ucast9_inj h' hlo h)), hgf lo' h']
        refine congrArg optRef (hm _ (by show _ % 8 = 0; rw [peA_val qf h']; omega) fun e => el ?_).symm
        have := congrArg UScalar.val e
        rw [peA_val qf h', hpv] at this
        exact UScalar.eq_of_val_eq (by omega)
    · have hb : q.bv ≠ p.bv := bv_inj e
      refine ⟨g, by simp [hb, hg], fun lo' h' => ?_⟩
      rw [hgf lo' h']
      refine congrArg optRef (hm _ (by show _ % 8 = 0; rw [peA_val qf h']; omega) fun e' => ?_).symm
      have := congrArg UScalar.val e'
      rw [peA_val qf h', hpv] at this
      have : q.val ≠ p.val := fun h => e (UScalar.eq_of_val_eq h)
      omega

/-- The relation is about the kheap, the arch state and memory only. -/
theorem VsRel.ms {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    (ms : Fl4Spec.MachineState) : VsRel P m ksb { σ with machineState := ms } := ⟨hR.1, hR.2, hR.3⟩

theorem optRef_eq_some {w r : U64} (hr : r ≠ 0#u64) : optRef w = some r.bv ↔ w = r := by
  unfold optRef
  constructor
  · intro h
    split at h
    · cases h
    · injection h with h; exact UScalar.eq_of_val_eq (by have := congrArg BitVec.toNat h; exact this)
  · rintro rfl; rw [if_neg hr]

/-- Clearing the tag leaves every native root unchanged. -/
theorem clear_native_tag (w : U64) (h : w &&& 1#u64 = 0#u64) :
    w &&& ~~~1#u64 = w := by
  have hb := congrArg UScalar.bv h
  change w.bv &&& 1#64 = 0#64 at hb
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  change w.bv &&& ~~~1#64 = w.bv
  bv_decide

theorem daBody_native {σ : Fl4Spec.State Unit} (asid root pool : U64)
    (f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef) (v : U64)
    (hfe : f (Fl4Spec.asidLowBitsOf asid.bv) = optRef v) (htag : v &&& 1#u64 = 0#u64) :
    daBody asid.bv root.bv pool.bv f σ =
      Fl4Spec.NonDet.when (f (Fl4Spec.asidLowBitsOf asid.bv) = some root.bv) (do
        Fl4Spec.hwAsidInvalidate asid.bv root.bv
        let pool' ← pure (Function.update f (Fl4Spec.asidLowBitsOf asid.bv) none)
        Fl4Spec.setAsidPool pool.bv pool'
        specVmRootCur) σ := by
  unfold daBody
  rw [hfe]
  by_cases h0 : v = 0#u64
  · subst v; simp [optRef, Fl4Spec.NonDet.when, Fl4Spec.NonDet.pure]
  · have ht : (v.bv : Fl4Spec.ObjRef) &&& 1 = 0 := by
      change v.bv &&& 1#64 = 0#64
      exact (tag_bv_iff v).mpr htag
    have hm : Fl4Spec.asidEntryRoot v.bv = v.bv := by
      have h := congrArg UScalar.bv (clear_native_tag v htag)
      exact h
    simp only [optRef, if_neg h0, hm, if_pos ht, Option.some.injEq]

theorem daBody_nested {σ : Fl4Spec.State Unit} (asid root pool : U64)
    (f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef) (v : U64)
    (hk : σ.kheap pool.bv = some (.archObj (.asidPool f)))
    (hfe : f (Fl4Spec.asidLowBitsOf asid.bv) = optRef v) (htag : v &&& 1#u64 ≠ 0#u64) :
    daBody asid.bv root.bv pool.bv f σ =
      (if v &&& ~~~1#u64 = root then
        ({((), updK σ pool.bv (.archObj (.asidPool
          (Function.update f (Fl4Spec.asidLowBitsOf asid.bv) none))))}, False)
      else ({((), σ)}, False)) := by
  have h0 : v ≠ 0#u64 := by intro h; subst v; simp at htag
  have ht : ¬ (v.bv : Fl4Spec.ObjRef) &&& 1 = 0 := by
    change ¬ v.bv &&& 1#64 = 0#64
    exact fun h => htag ((tag_bv_iff v).mp h)
  have hm : Fl4Spec.asidEntryRoot v.bv = root.bv ↔ v &&& ~~~1#u64 = root := by
    change (v &&& ~~~1#u64).bv = root.bv ↔ v &&& ~~~1#u64 = root
    exact (UScalar.eq_equiv_bv_eq _ _).symm
  unfold daBody
  rw [hfe]
  simp only [optRef, if_neg h0, if_neg ht, hm, Fl4Spec.NonDet.when]
  split_ifs
  · rw [nd_pure_bind', nd_bind_one (setAsidPool_eq hk _)]
    simp [Fl4Spec.NonDet.pure]
  · simp [Fl4Spec.NonDet.pure]

/-- The nested TLB operation preserves memory and the native view. -/
theorem ept_invalidate_native {A : Type} {ar : machine.Arch A} {P : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsHypsR st A ar P SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hS : SR s a σ) (root : U64) :
    ept.invalidate st ar s a root ⦃ r => r.1 = s ∧ SR s r.2 σ ⦄ := by
  have hC : ept.CORES = ok 4080#u64 := by unfold ept.CORES; rfl
  unfold ept.invalidate
  simp only [hC, lift, bind_ok,
    shr_eq _ 32#i32 (by decide) (by decide),
    show (4080#u64 + 8#u64 : Result U64) = ok 4088#u64 from rfl]
  step with LawfulStore.read_spec
  step with LawfulStore.read_spec
  refine WP.spec_bind (hH.invEpt s a σ _ _ hS) ?_
  intro a' hS'
  exact (WP.spec_ok _).2 ⟨rfl, hS'⟩

/-- **`delete_asid`** (FL4 `vspace::delete_asid asid root`, `root ≠ 0`)
refines l4v `delete_asid asid root`: the spec does not fail, and FL4's outcome
is matched by one of the spec's. -/
theorem delete_asid_relR {A : Type} {ar : machine.Arch A} {P : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsHypsR st A ar P SR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hP : VsPlaced P (L.ksb s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : SR s a σ) (asid root : U64) (hr0 : root ≠ 0#u64) :
    vspace.delete_asid st ar s a asid root ⦃ r =>
      ¬ (Fl4Spec.deleteAsid (Z := Unit) asid.bv root.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.deleteAsid (Z := Unit) asid.bv root.bv σ).1 ∧
        VsRel P (L.mem r.1) (L.ksb r.1) σ' ∧ SR r.1 r.2 σ' ∧ VsZeroW st P s r.1 ⦄ := by
  unfold vspace.delete_asid
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro pool rfl
  have hiv : i.val = asid.val >>> 9 := by simpa using hi
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have htab := hR.table _ hlt
  rw [hi_bv asid i hiv] at htab
  have hspec0 : Fl4Spec.deleteAsid (Z := Unit) asid.bv root.bv σ =
      (match σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf asid.bv) with
       | none => return ()
       | some poolPtr => do
          let pool ← Fl4Spec.getAsidPool poolPtr
          daBody asid.bv root.bv poolPtr pool) σ := by
    unfold Fl4Spec.deleteAsid
    rw [nd_bind_one (show Fl4Spec.NonDet.gets _ σ = ({(σ.archState.x64AsidTable, σ)}, False) from rfl)]
    rfl
  by_cases hp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · rw [hp, show optRef 0#u64 = none from optRef_zero] at htab
    simp only [hp, ↓reduceIte, WP.spec_ok]
    rw [hspec0, htab]
    exact ⟨by simp [pure, Fl4Spec.NonDet.pure], σ, by simp [pure, Fl4Spec.NonDet.pure], hR, hS, VsZeroW.refl P s⟩
  · simp only [hp, ↓reduceIte]
    set w := L.mem s (atA (L.ksb s) (i &&& 2047#u64)) with hw
    have hwP := hR.tmem _ hlt hp
    obtain ⟨f, hkf, hf⟩ := hR.pool _ hwP
    rw [optRef, if_neg hp] at htab
    have hlo := and_lt asid 9 511#u64 rfl (by decide)
    have hfe := hf _ hlo
    rw [lo_bv] at hfe
    have hspec1 : Fl4Spec.deleteAsid (Z := Unit) asid.bv root.bv σ =
        daBody asid.bv root.bv w.bv f σ := by
      rw [hspec0, htab]
      dsimp only
      rw [nd_bind_one (getAsidPool_eq hkf)]
    rw [hspec1]
    unfold lift
    apply ok_bind_spec
    apply ok_bind_spec
    apply ok_bind_spec
    step as ⟨v, hv⟩
    have hv' : v = L.mem s (peA w (asid &&& 511#u64)) := hv
    subst hv'
    change f (Fl4Spec.asidLowBitsOf asid.bv) = optRef (L.mem s (peA w (asid &&& 511#u64))) at hfe
    by_cases htag : L.mem s (peA w (asid &&& 511#u64)) &&& 1#u64 = 0#u64
    · rw [daBody_native asid root w f _ hfe htag]
      have hclear := clear_native_tag (L.mem s (peA w (asid &&& 511#u64))) htag
      simp only [lift, bind_ok, hclear, htag, bne_iff_ne, ne_eq, not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hvr : L.mem s (peA w (asid &&& 511#u64)) = root
      · have hc : f (Fl4Spec.asidLowBitsOf asid.bv) = some root.bv := by rw [hfe, optRef_eq_some hr0]; exact hvr
        simp only [hvr, ↓reduceIte, Fl4Spec.NonDet.when, hc]
        refine WP.spec_bind (hH.inval s a σ asid root.bv hR hS) ?_
        rintro a1 ⟨σ1, hm1, hS1⟩
        obtain ⟨ms1, rfl⟩ := doMachineOp_mem hm1
        step as ⟨s1, hs1⟩
        subst hs1
        obtain ⟨wa, wf⟩ := hP.pal w hwP
        have hea : Aligned (peA w (asid &&& 511#u64)) := by show _ % 8 = 0; rw [peA_val wf hlo]; omega
        set σ2 := updK { σ with machineState := ms1 } w.bv
          (.archObj (.asidPool (Function.update f (Fl4Spec.asidLowBitsOf asid.bv) none)))
        have hR2 : VsRel P (L.mem (L.wr s (peA w (asid &&& 511#u64)) 0#u64)) (L.ksb s) σ2 := by
          have := (hR.ms ms1).upd_entry hP hwP (show ({ σ with machineState := ms1 } : Fl4Spec.State Unit).kheap w.bv = _
            from hkf) hlo 0#u64 (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
          rw [lo_bv, optRef_zero] at this
          exact this
        have hW : WritesIn st s (L.wr s (peA w (asid &&& 511#u64)) 0#u64) (VsWrite P (L.ksb s)) :=
          ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hea hb (fun e => hn (Or.inr ⟨w, hwP, _, hlo, (UScalar.eq_of_val_eq e).symm⟩))⟩
        have hS2 := hH.stable _ _ a1 _ σ2 hS1 hW (Or.inl ⟨w.bv, f, _, hkf, rfl⟩)
        refine WP.spec_mono (hH.vmRoot _ a1 σ2 (by rw [LawfulStore.ksb_wr]; exact hR2) hS2) ?_
        rintro ⟨s3, a3⟩ ⟨e3, hnf, σ3, hm3, hR3, hS3⟩
        simp only at e3
        subst e3
        refine ⟨?_, σ3, ?_, hR3, hS3, VsZeroW.wr s hea (Or.inr ⟨w, hwP, _, hlo, rfl⟩)⟩
        · refine nd_nofail_bind (hH.invalOK _ _ σ) fun x hx => ?_
          obtain ⟨r, σ''⟩ := x
          obtain ⟨ms, rfl⟩ := doMachineOp_mem hx
          dsimp only
          rw [ndpure_bind, nd_bind_one (setAsidPool_eq (show ({ σ with machineState := ms } : Fl4Spec.State Unit).kheap
            w.bv = _ from hkf) _)]
          exact hnf ms
        · refine nd_mem_bind hm1 ?_
          rw [ndpure_bind, nd_bind_one (setAsidPool_eq (show ({ σ with machineState := ms1 } : Fl4Spec.State Unit).kheap
            w.bv = _ from hkf) _)]
          exact hm3
      · simp only [hvr, ↓reduceIte, WP.spec_ok]
        have hc : ¬ f (Fl4Spec.asidLowBitsOf asid.bv) = some root.bv := by rw [hfe, optRef_eq_some hr0]; exact hvr
        rw [nd_when_false hc]
        exact ⟨by simp [pure, Fl4Spec.NonDet.pure], σ, by simp [pure, Fl4Spec.NonDet.pure], hR, hS, VsZeroW.refl P s⟩

    · rw [daBody_nested asid root w f _ hkf hfe htag]
      by_cases hvr : L.mem s (peA w (asid &&& 511#u64)) &&& ~~~1#u64 = root
      · simp only [hvr, ↓reduceIte, bne_iff_ne]
        rw [if_pos htag]
        refine WP.spec_bind (ept_invalidate_native hH s a σ hS root) ?_
        rintro ⟨s1, a1⟩ ⟨hs1, hS1⟩
        dsimp only at hs1
        subst s1
        step as ⟨s2, hs2⟩
        subst hs2
        obtain ⟨wa, wf⟩ := hP.pal w hwP
        have hea : Aligned (peA w (asid &&& 511#u64)) := by
          show _ % 8 = 0; rw [peA_val wf hlo]; omega
        have hew := VsZeroW.wr (st := st) (P := P) s hea (Or.inr ⟨w, hwP, asid &&& 511#u64, hlo, rfl⟩)
        set σG := updK σ w.bv (.archObj (.asidPool
          (Function.update f (Fl4Spec.asidLowBitsOf asid.bv) none)))
        have hR' : VsRel P (L.mem (L.wr s (peA w (asid &&& 511#u64)) 0#u64)) (L.ksb s) σG := by
          have h := hR.upd_entry hP hwP hkf hlo 0#u64
            (fun b hb hne => L.mem_wr_ne hea hb (fun e => hne (UScalar.eq_of_val_eq e).symm))
            (L.mem_wr_same hea)
          rw [lo_bv, optRef_zero] at h
          exact h
        have hS' := hH.stable s (L.wr s (peA w (asid &&& 511#u64)) 0#u64) a1 σ σG hS1
          ((writesIn_wr hea).mono fun b hb => Or.inr ⟨w, hwP, asid &&& 511#u64, hlo, hb⟩)
          (Or.inl ⟨w.bv, f, _, hkf, rfl⟩)
        exact ⟨by simp, σG, by simp [σG], by simpa only [L.ksb_wr, peA] using hR', hS', hew⟩
      · simp only [hvr, ↓reduceIte, WP.spec_ok]
        exact ⟨by simp, σ, by simp, hR, hS, VsZeroW.refl P s⟩

end

end

end Fl4Proofs.P3.Vs
