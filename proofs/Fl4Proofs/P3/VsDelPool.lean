/-
P3 (DESIGN.md §9), VSpace: **`delete_asid_pool`** against l4v
`delete_asid_pool`, with the hypotheses of `VsDel` (`VsHypsR`).

FL4 invalidates the ASIDs of the non-empty entries of the pool (one
`Arch::invalidate_asid` each, in order), clears the table entry, and
switches to the current thread's address space; l4v does the same with
`hw_asid_invalidate` over `[0 .e. 2^asid_low_bits - 1]`.
-/
import Fl4Proofs.P3.VsDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec

/-- Running `mapM` on a list with one more element. -/
theorem mapM_snoc_mem {σ' α β : Type} (f : α → NonDet σ' β) (x : α) :
    ∀ (l : List α) (s s1 s2 : σ') (rs : List β) (r : β), (rs, s1) ∈ (NonDet.mapM f l s).1 →
      (r, s2) ∈ (f x s1).1 → (rs ++ [r], s2) ∈ (NonDet.mapM f (l ++ [x]) s).1
  | [], s, s1, s2, rs, r, h1, h2 => by
    simp only [NonDet.mapM, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    show _ ∈ ((NonDet.bind (f x) fun b => NonDet.bind (NonDet.pure []) fun bs => NonDet.pure (b :: bs)) _).1
    exact ⟨(r, s2), h2, ([], s2), rfl, rfl⟩
  | a :: l, s, s1, s2, rs, r, h1, h2 => by
    obtain ⟨⟨b, t1⟩, hb, ⟨bs, t2⟩, hbs, hr⟩ := h1
    simp only [NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨(b, t1), hb, (bs ++ [r], s2), mapM_snoc_mem f x l t1 _ s2 bs r hbs h2, rfl⟩

/-- A `mapM` of steps that do not fail and only change the machine state. -/
theorem mapM_ms {β α : Type} (f : α → NonDet (State Unit) β) (hf : ∀ x σ, ¬ (f x σ).2)
    (hfm : ∀ x σ r σ', (r, σ') ∈ (f x σ).1 → ∃ ms, σ' = { σ with machineState := ms }) :
    ∀ (l : List α) (σ : State Unit), ¬ (NonDet.mapM f l σ).2 ∧
      ∀ rs σ', (rs, σ') ∈ (NonDet.mapM f l σ).1 → ∃ ms, σ' = { σ with machineState := ms }
  | [], σ => ⟨fun h => h, fun rs σ' h => by
      simp only [NonDet.mapM, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      exact ⟨σ.machineState, h.2⟩⟩
  | a :: l, σ => by
    refine ⟨?_, ?_⟩
    · rintro (h | ⟨⟨b, t1⟩, hb, h⟩)
      · exact hf a σ h
      · obtain ⟨ms, rfl⟩ := hfm a σ b t1 hb
        rcases h with h | ⟨⟨bs, t2⟩, -, h⟩
        · exact (mapM_ms f hf hfm l _).1 h
        · exact h
    · rintro rs σ' ⟨⟨b, t1⟩, hb, ⟨bs, t2⟩, hbs, hr⟩
      simp only [NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      obtain ⟨ms, rfl⟩ := hfm a σ b t1 hb
      obtain ⟨ms', h'⟩ := (mapM_ms f hf hfm l _).2 bs _ hbs
      exact ⟨ms', h'⟩

/-- The step of l4v `delete_asid_pool`'s loop. -/
def dpStep (base : Asid) (pool : AsidLowIndex → Option ObjRef) (offset : Asid) : SMonad Unit Unit :=
  NonDet.when (nativeAsidRoot (pool (ucast asidLowLen offset)) ≠ none) <|
    hwAsidInvalidate (base + offset) (the (nativeAsidRoot (pool (ucast asidLowLen offset))))

theorem dpStep_ms (base : Asid) (pool : AsidLowIndex → Option ObjRef) (x : Asid) (σ : State Unit) (r : Unit)
    (σ' : State Unit) (h : (r, σ') ∈ (dpStep base pool x σ).1) : ∃ ms, σ' = { σ with machineState := ms } := by
  unfold dpStep NonDet.when at h
  split at h
  · exact doMachineOp_mem h
  · simp only [NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact ⟨σ.machineState, h.2⟩

/-- The offsets of l4v's loop. -/
def dpOffs : List Asid := uptoEnum 0 (((1 : Asid) <<< asidLowBits) - 1)

theorem dpOffs_eq : dpOffs = (List.range' 0 512).map (BitVec.ofNat 64) := by
  unfold dpOffs uptoEnum
  rw [show (((1 : Asid) <<< asidLowBits) - 1).toNat = 511 by decide]
  rfl

theorem dpOffs_take_succ (i : Nat) (hi : i < 512) :
    dpOffs.take (i + 1) = dpOffs.take i ++ [BitVec.ofNat 64 i] := by
  rw [List.take_succ, dpOffs_eq]
  simp [List.getElem?_range', hi]

theorem dpOffs_take_512 : dpOffs.take 512 = dpOffs := by
  rw [List.take_of_length_le]; rw [dpOffs_eq]; simp

/-- The spec's loop reaches `σ'` from `σ` after `n` offsets. -/
def dpReach (base : Asid) (pool : AsidLowIndex → Option ObjRef) (n : Nat) (σ σ' : State Unit) : Prop :=
  ∃ rs, (rs, σ') ∈ (NonDet.mapM (dpStep base pool) (dpOffs.take n) σ).1

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem ucast_inj (k : Nat) {a b : U64} (ha : a.val < 2 ^ k) (hb : b.val < 2 ^ k)
    (h : (Fl4Spec.ucast k a.bv : BitVec k) = Fl4Spec.ucast k b.bv) : a = b := by
  apply UScalar.eq_of_val_eq
  have := congrArg BitVec.toNat h
  simp only [Fl4Spec.ucast, BitVec.toNat_setWidth] at this
  show a.bv.toNat = b.bv.toNat
  have e1 : a.bv.toNat % 2 ^ k = a.bv.toNat := Nat.mod_eq_of_lt (by show a.val < _; omega)
  have e2 : b.bv.toNat % 2 ^ k = b.bv.toNat := Nat.mod_eq_of_lt (by show b.val < _; omega)
  omega

/-- The relation after clearing word `hi` of the ASID table. -/
theorem VsRel.upd_table {P : Set U64} {m m' : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit}
    (hP : VsPlaced P ksb) (hR : VsRel P m ksb σ) {hi : U64} (hhi : hi.val < 2048)
    (hm : ∀ b, Aligned b → b ≠ atA ksb hi → m' b = m b) (hme : m' (atA ksb hi) = 0#u64) :
    VsRel P m' ksb { σ with archState := { σ.archState with x64AsidTable := Function.update σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) none } } := by
  have hv := atA_val hP.ksb_fit hhi
  have hoth : ∀ hi' : U64, hi'.val < 2048 → hi' ≠ hi → m' (atA ksb hi') = m (atA ksb hi') := by
    intro hi' h' hne
    refine hm _ (by show _ % 8 = 0; rw [atA_val hP.ksb_fit h']; have := hP.ksb_al; omega) fun e => hne ?_
    have := congrArg UScalar.val e
    rw [atA_val hP.ksb_fit h', hv] at this
    exact UScalar.eq_of_val_eq (by omega)
  refine ⟨fun hi' h' => ?_, fun hi' h' h0 => ?_, fun q hq => ?_⟩
  · show Function.update σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) none (Fl4Spec.ucast 11 hi'.bv) = _
    by_cases e : hi' = hi
    · subst e; rw [Function.update_self, hme]; rfl
    · rw [Function.update_of_ne (fun h => e (ucast_inj 11 h' hhi h)), hoth hi' h' e]; exact hR.table hi' h'
  · by_cases e : hi' = hi
    · subst e; exact absurd hme h0
    · rw [hoth hi' h' e] at h0 ⊢; exact hR.tmem hi' h' h0
  · obtain ⟨g, hg, hgf⟩ := hR.pool q hq
    obtain ⟨qa, qf⟩ := hP.pal q hq
    refine ⟨g, hg, fun lo h => ?_⟩
    rw [hgf lo h]
    refine congrArg optRef (hm _ (by show _ % 8 = 0; rw [peA_val qf h]; omega) fun e => ?_).symm
    have := congrArg UScalar.val e
    rw [peA_val qf h, hv] at this
    have := hP.ptab q hq
    omega

/-- The FL4 loop of `delete_asid_pool`: one invalidation per non-empty
entry, each matched by the spec's. -/
theorem delete_asid_pool_loop_rel {A : Type} {ar : machine.Arch A} {P : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsHypsR st A ar P SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hP : VsPlaced P (L.ksb s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : SR s a σ) {pool : U64} (hp : pool ∈ P)
    {f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef} (hkf : σ.kheap pool.bv = some (.archObj (.asidPool f)))
    (base : U64) :
    vspace.delete_asid_pool_loop st ar s a base pool 0#u64 ⦃ r => r.1 = s ∧ ∃ ms,
      dpReach base.bv f 512 σ { σ with machineState := ms } ∧ SR s r.2 { σ with machineState := ms } ⦄ := by
  obtain ⟨pa, pf⟩ := hP.pal pool hp
  have hgf : ∀ lo : U64, lo.val < 512 → Fl4Spec.nativeAsidRoot (f (Fl4Spec.ucast 9 lo.bv)) = nativeRef (L.mem s (peA pool lo)) := by
    obtain ⟨f, hg, hgf⟩ := hR.pool pool hp
    rw [hkf] at hg; injection hg with hg; injection hg with hg; injection hg with hg; subst hg
    intro lo hlo
    rw [hgf lo hlo, nativeAsidRoot_optRef]
  unfold vspace.delete_asid_pool_loop
  apply loop.spec_decr_nat (measure := fun x => 512 - x.2.2.val)
    (inv := fun x => x.1 = s ∧ x.2.2.val ≤ 512 ∧ ∃ ms,
      dpReach base.bv f x.2.2.val σ { σ with machineState := ms } ∧ SR s x.2.1 { σ with machineState := ms })
  · rintro ⟨s1, a1, i⟩ ⟨hs1, hi5, ms, ⟨rs, hm⟩, hS1⟩
    dsimp only at hs1
    subst s1
    unfold vspace.delete_asid_pool_loop.body
    simp only at hi5 hm hS1 ⊢
    by_cases h1 : i < 512#u64
    · have hi : i.val < 512 := by have := (gt_iff_val).1 h1; simpa using this
      simp only [h1, ↓reduceIte]
      step as ⟨i1, hi1⟩
      unfold lift
      apply ok_bind_spec
      step as ⟨v, hv⟩
      have he : core.num.U64.wrapping_add pool i1 = peA pool i := by
        apply UScalar.eq_of_val_eq
        rw [peA_val pf hi]
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hi1]; omega
      rw [he] at hv
      try simp only [lift, bind_ok]
      have hgi := hgf i hi
      have hib : (i.bv : BitVec 64) = BitVec.ofNat 64 i.val := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
      have hstep : Fl4Spec.NonDet.mapM (dpStep base.bv f) (dpOffs.take (i.val + 1)) σ =
          Fl4Spec.NonDet.mapM (dpStep base.bv f) (dpOffs.take i.val ++ [BitVec.ofNat 64 i.val]) σ := by
        rw [dpOffs_take_succ i.val hi]
      have hstay (hc : Fl4Spec.nativeAsidRoot (f (Fl4Spec.ucast Fl4Spec.asidLowLen (BitVec.ofNat 64 i.val))) = none) :
          dpReach base.bv f (i.val + 1) σ { σ with machineState := ms } := by
        refine ⟨rs ++ [()], ?_⟩
        rw [hstep]
        refine mapM_snoc_mem _ _ _ _ _ _ _ _ hm ?_
        unfold dpStep
        rw [nd_when_false (by rw [hc]; simp)]
        exact rfl
      refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = s ∧ ∃ ms2,
        dpReach base.bv f (i.val + 1) σ { σ with machineState := ms2 } ∧
          SR s r.2 { σ with machineState := ms2 }) ?_ ?_
      · by_cases htag : v &&& 1#u64 = 0#u64
        · simp only [htag, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          by_cases h0 : v = 0#u64
          · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
            simp only [bind_ok, bind_tc_ok, WP.spec_ok]
            refine ⟨trivial, ms, hstay ?_, hS1⟩
            rw [← hib, hgi, ← hv, h0]; exact nativeRef_zero
          · have hc : Fl4Spec.nativeAsidRoot (f (Fl4Spec.ucast Fl4Spec.asidLowLen (BitVec.ofNat 64 i.val))) = some v.bv := by
              rw [← hib, hgi, ← hv]
              simp only [nativeRef, htag, ↓reduceIte, optRef, if_neg h0]
            simp only [bne_iff_ne, if_pos h0]
            refine WP.spec_bind (hH.inval s a1 _ (core.num.U64.wrapping_add base i) v.bv (hR.ms ms) hS1) ?_
            rintro a2 ⟨σ2, hm2, hS2⟩
            obtain ⟨ms2, rfl⟩ := doMachineOp_mem hm2
            refine (WP.spec_ok _).2 ⟨rfl, ms2, ⟨rs ++ [()], ?_⟩, hS2⟩
            rw [hstep]
            refine mapM_snoc_mem _ _ _ _ _ _ _ _ hm ?_
            unfold dpStep
            have hw : Fl4Spec.NonDet.when (Fl4Spec.nativeAsidRoot (f (Fl4Spec.ucast Fl4Spec.asidLowLen (BitVec.ofNat 64 i.val))) ≠ none)
                (Fl4Spec.hwAsidInvalidate (Z := Unit) (base.bv + BitVec.ofNat 64 i.val)
                  (Fl4Spec.the (Fl4Spec.nativeAsidRoot (f (Fl4Spec.ucast Fl4Spec.asidLowLen (BitVec.ofNat 64 i.val)))))) =
                Fl4Spec.hwAsidInvalidate (Z := Unit) (base.bv + BitVec.ofNat 64 i.val) v.bv := by
              unfold Fl4Spec.NonDet.when; rw [if_pos (by rw [hc]; simp), hc]; rfl
            rw [hw]
            have hb : (core.num.U64.wrapping_add base i).bv = base.bv + BitVec.ofNat 64 i.val := by
              rw [← hib]; rfl
            rw [← hb]
            exact hm2
        · simp only [bne_iff_ne, if_pos htag]
          refine WP.spec_mono (ept_invalidate_native hH s a1 { σ with machineState := ms } hS1 _) ?_
          rintro ⟨s2, a2⟩ ⟨hs2, hS2⟩
          exact ⟨hs2, ms, hstay (by rw [← hib, hgi, ← hv]; simp [nativeRef, htag]), hS2⟩
      · rintro ⟨s2, a2⟩ ⟨hs2, ms2, hm2, hS2⟩
        dsimp only at hs2
        subst s2
        step as ⟨i2, hi2⟩
        have hi2' : i2.val = i.val + 1 := by simpa using hi2
        refine ⟨by omega, ⟨ms2, ?_, hS2⟩, by omega⟩
        rw [hi2']; exact hm2
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hi : i.val = 512 := by
        have : ¬ i.val < 512 := fun h => h1 ((gt_iff_val).2 (by simpa using h))
        omega
      rw [hi] at hm
      exact ⟨trivial, ms, ⟨rs, hm⟩, hS1⟩
  · refine ⟨rfl, by simp, σ.machineState, ⟨[], ?_⟩, hS⟩
    simp [Fl4Spec.NonDet.mapM, Fl4Spec.NonDet.pure]


/-- The tail of l4v `delete_asid_pool`: clear the table entry, then switch
address space. -/
def dpRest (t : Fl4Spec.AsidHighIndex → Option Fl4Spec.ObjRef) (h : Fl4Spec.AsidHighIndex) : Fl4Spec.SMonad Unit Unit := do
  let asidTable' ← pure (Function.update t h none)
  Fl4Spec.NonDet.modify fun s => { s with archState := { s.archState with x64AsidTable := asidTable' } }
  let tcb ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
  Fl4Spec.setVmRoot tcb

theorem dpRest_eq (t : Fl4Spec.AsidHighIndex → Option Fl4Spec.ObjRef) (h : Fl4Spec.AsidHighIndex)
    (σ : Fl4Spec.State Unit) :
    dpRest t h σ = specVmRootCur { σ with archState := { σ.archState with x64AsidTable := Function.update t h none } } := by
  unfold dpRest
  rw [nd_pure_bind', nd_bind_one (show Fl4Spec.NonDet.modify _ σ = _ from rfl)]
  rfl

theorem dpStep_nofail {A : Type} {ar : machine.Arch A} {P : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsHypsR st A ar P SR) (base : Fl4Spec.Asid) (pool : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef)
    (x : Fl4Spec.Asid) (σ : Fl4Spec.State Unit) : ¬ (dpStep base pool x σ).2 := by
  unfold dpStep Fl4Spec.NonDet.when
  split
  · exact hH.invalOK _ _ σ
  · exact fun h => h

/-- **`delete_asid_pool`** (FL4 `vspace::delete_asid_pool base pool`, for an
ASID-pool cap: `base` 512-aligned, `pool ≠ 0`) refines l4v
`delete_asid_pool base pool`: the spec does not fail, and FL4's outcome is
matched by one of the spec's. -/
theorem delete_asid_pool_relR {A : Type} {ar : machine.Arch A} {P : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsHypsR st A ar P SR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hP : VsPlaced P (L.ksb s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : SR s a σ) (base pool : U64) (hb : base.val % 512 = 0)
    (hp0 : pool ≠ 0#u64) :
    vspace.delete_asid_pool st ar s a base pool ⦃ r =>
      ¬ (Fl4Spec.deleteAsidPool (Z := Unit) base.bv pool.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.deleteAsidPool (Z := Unit) base.bv pool.bv σ).1 ∧
        VsRel P (L.mem r.1) (L.ksb r.1) σ' ∧ SR r.1 r.2 σ' ∧ VsZeroW st P s r.1 ⦄ := by
  have hlow : Fl4Spec.asidLowBitsOf base.bv = 0 := by
    unfold Fl4Spec.asidLowBitsOf Fl4Spec.asidLowLen Fl4Spec.ucast
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    show base.val % 2 ^ 9 = 0 % 2 ^ 9
    omega
  have hspec0 : Fl4Spec.deleteAsidPool (Z := Unit) base.bv pool.bv σ =
      Fl4Spec.NonDet.when (σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv) = some pool.bv) (do
        let pl ← Fl4Spec.getAsidPool pool.bv
        let _ ← Fl4Spec.NonDet.mapM (dpStep base.bv pl) dpOffs
        dpRest σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv)) σ := by
    unfold Fl4Spec.deleteAsidPool
    rw [nd_bind_one (assert_true' hlow σ),
      nd_bind_one (show Fl4Spec.NonDet.gets _ σ = ({(σ.archState.x64AsidTable, σ)}, False) from rfl)]
    rfl
  unfold vspace.delete_asid_pool
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro w rfl
  have hiv : i.val = base.val >>> 9 := by simpa using hi
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have htab := hR.table _ hlt
  rw [hi_bv base i hiv] at htab
  by_cases hw : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = pool
  · have hne : (L.mem s (atA (L.ksb s) (i &&& 2047#u64)) != pool) = false := by simp [hw]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hpP : pool ∈ P := hw ▸ hR.tmem _ hlt (hw ▸ hp0)
    obtain ⟨f, hkf, -⟩ := hR.pool pool hpP
    have hc : σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv) = some pool.bv := by
      rw [htab, optRef_eq_some hp0]; exact hw
    have hspec1 : Fl4Spec.deleteAsidPool (Z := Unit) base.bv pool.bv σ =
        (Fl4Spec.NonDet.mapM (dpStep base.bv f) dpOffs >>= fun _ =>
          dpRest σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv)) σ := by
      rw [hspec0]
      unfold Fl4Spec.NonDet.when
      rw [if_pos hc, nd_bind_one (getAsidPool_eq hkf)]
    refine WP.spec_bind (delete_asid_pool_loop_rel hH s a σ hP hR hS hpP hkf base) ?_
    rintro ⟨sloop, a1⟩ ⟨hsl, ms, ⟨rs, hm⟩, hS1⟩
    dsimp only at hsl
    subst sloop
    rw [dpOffs_take_512] at hm
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = base.val >>> 9 := by simpa using hi2
    refine WP.spec_bind (set_asid_table_spec s i2 0#u64) ?_
    rintro s1 rfl
    have hlt2 := and_lt i2 11 2047#u64 rfl (by decide)
    have hv := atA_val (hi := i2 &&& 2047#u64) hP.ksb_fit hlt2
    have hea : Aligned (atA (L.ksb s) (i2 &&& 2047#u64)) := by
      show _ % 8 = 0; rw [hv]; have := hP.ksb_al; omega
    set σT : Fl4Spec.State Unit := { ({ σ with machineState := ms } : Fl4Spec.State Unit) with archState := { σ.archState with x64AsidTable := Function.update σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv) none } }
    have hRT : VsRel P (L.mem (L.wr s (atA (L.ksb s) (i2 &&& 2047#u64)) 0#u64)) (L.ksb s) σT := by
      have := (hR.ms ms).upd_table hP hlt2 (m' := L.mem (L.wr s (atA (L.ksb s) (i2 &&& 2047#u64)) 0#u64))
        (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
      rw [hi_bv base i2 hi2v] at this
      exact this
    have hW : WritesIn st s (L.wr s (atA (L.ksb s) (i2 &&& 2047#u64)) 0#u64) (VsWrite P (L.ksb s)) :=
      ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hea hb
        (fun e => hn (Or.inl ⟨_, hlt2, (UScalar.eq_of_val_eq e).symm⟩))⟩
    have hST := hH.stable _ _ a1 _ σT hS1 hW (Or.inr ⟨_, rfl⟩)
    refine WP.spec_mono (hH.vmRoot _ a1 σT (by rw [LawfulStore.ksb_wr]; exact hRT) hST) ?_
    rintro ⟨s3, a3⟩ ⟨e3, hnf, σ3, hm3, hR3, hS3⟩
    simp only at e3
    subst e3
    rw [hspec1]
    refine ⟨?_, σ3, ?_, hR3, hS3, VsZeroW.wr s hea (Or.inl ⟨_, hlt2, rfl⟩)⟩
    · have hM := mapM_ms (dpStep base.bv f) (dpStep_nofail hH base.bv f) (dpStep_ms base.bv f) dpOffs σ
      refine nd_nofail_bind hM.1 fun x hx => ?_
      obtain ⟨ms', hms'⟩ := hM.2 x.1 x.2 hx
      rw [dpRest_eq, hms']
      exact hnf ms'
    · refine nd_mem_bind hm ?_
      rw [dpRest_eq]
      exact hm3
  · have hne : (L.mem s (atA (L.ksb s) (i &&& 2047#u64)) != pool) = true := by simp [hw]
    simp only [hne, ↓reduceIte, WP.spec_ok]
    have hc : ¬ σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv) = some pool.bv := by
      rw [htab, optRef_eq_some hp0]; exact hw
    rw [hspec0, nd_when_false hc]
    exact ⟨by simp [pure, Fl4Spec.NonDet.pure], σ, by simp [pure, Fl4Spec.NonDet.pure], hR, hS, VsZeroW.refl P s⟩

end

end

end Fl4Proofs.P3.Vs
