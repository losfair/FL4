/-
P3 (DESIGN.md §9), untyped: **retype of PML4s**. FL4's `create_object`
for a PML4 copies the kernel's global mappings into its upper half
(`vspace::copy_global_mappings`): it writes only words of the new object
and keeps `ksb` (`copy_gm_frame`). The spec's `init_arch_objects` copies the
global PML4's entries into each new PML4 (`copyGlobalMappings`): one
outcome, changing only the new PML4 objects, given the global PML4 object
(`initArch_pml4`).
-/
import Fl4Proofs.P3.UntypedRetypeReset
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem kernel_root_eq (s : S) :
    vspace.kernel_root st s = ok (L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT)) := by
  unfold vspace.kernel_root obj.ks_get; simp [L.ks_base_eq, L.read_eq, lift]

theorem entry_addr_val (table i : U64) (hi : i.val < 512) (ht : table.val + 4096 ≤ 2 ^ 64) :
    ∃ a, vspace.entry_addr table i = ok a ∧ a.val = table.val + 8 * i.val := by
  refine ⟨core.num.U64.wrapping_add table (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64),
    by unfold vspace.entry_addr; simp [lift], ?_⟩
  have h1 : (i &&& 511#u64).val = i.val := by
    simp only [UScalar.val_and]
    rw [show (511#u64 : U64).val = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, h1]
  simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
  omega

theorem entry_ok (s : S) (table i : U64) : ∃ v, vspace.entry st s table i = ok v := by
  unfold vspace.entry; simp [lift, L.read_eq]

/-- **FL4's `copy_global_mappings`** into the object at `base` (4 KiB,
aligned) writes only words of its upper half and keeps `ksb`. -/
theorem copy_gm_frame (s : S) (base : U64) (hal : base.val % 8 = 0) (hfit : base.val + 4096 ≤ 2 ^ 64) :
    vspace.copy_global_mappings st s base ⦃ s' => L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
      ∀ w : U64, P1.Aligned w → ¬ (base.val ≤ w.val ∧ w.val < base.val + 4096) → L.mem s' w = L.mem s w ⦄ := by
  unfold vspace.copy_global_mappings
  rw [kernel_root_eq]
  simp only [bind_ok]
  unfold vspace.copy_global_mappings_loop
  refine loop.spec_decr_nat (measure := fun x => 512 - x.2.val)
    (inv := fun x => x.2.val ≤ 512 ∧ L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s ∧
      ∀ w : U64, P1.Aligned w → ¬ (base.val ≤ w.val ∧ w.val < base.val + 4096) → L.mem x.1 w = L.mem s w)
    _ _ _ ?_ ⟨by simp, rfl, rfl, fun _ _ _ => rfl⟩
  rintro ⟨s1, i⟩ ⟨hi, hk, hc, hm⟩
  simp only at hi hk hc hm ⊢
  unfold vspace.copy_global_mappings_loop.body
  by_cases hlt : i < 512#u64
  · rw [if_pos hlt]
    have hlt' : i.val < 512 := hlt
    obtain ⟨v, hv⟩ := entry_ok (L := L) s1 (L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT)) i
    obtain ⟨a, ha, hav⟩ := entry_addr_val base i hlt' hfit
    rw [hv, ha]
    simp only [bind_ok, L.write_eq]
    obtain ⟨i2, hi2, hi2v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [hi2]
    simp only [bind_ok]
    have hi2' : i2.val = i.val + 1 := by rw [hi2v]; rfl
    refine (WP.spec_ok _).2 ?_
    simp only
    refine ⟨⟨by omega, by simp [hk], by simp [hc], fun w hw hout => ?_⟩, by omega⟩
    rw [L.mem_wr_ne (by unfold P1.Aligned; rw [hav]; omega) hw (by rw [hav]; omega)]
    exact hm w hw hout
  · rw [if_neg hlt]
    exact (WP.spec_ok _).2 ⟨hk, hc, hm⟩


/-- `create_object` for a PML4: the cap, the kernel's global mappings
copied into the object, nothing else written. -/
theorem create_object_pml4 {A' : Type} (arI : machine.Arch A') (s : S) (ar : A') (nt base us : U64) (dev : Bool)
    (hnt : nt.val = 8) (hal : base.val % 8 = 0) (hfit : base.val + 4096 ≤ 2 ^ 64) :
    objects.create_object st arI s ar nt base us dev ⦃ res =>
      res.1 = newCapOf nt.val base us dev ∧ res.2.2 = ar ∧ L.ksb res.2.1 = L.ksb s ∧ L.cpu res.2.1 = L.cpu s ∧
      ∀ w : U64, P1.Aligned w → ¬ (base.val ≤ w.val ∧ w.val < base.val + 4096) → L.mem res.2.1 w = L.mem s w ⦄ := by
  have hnt' : nt = 8#u64 := UScalar.eq_of_val_eq hnt
  subst hnt'
  unfold objects.create_object
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.X86EptPml4,
    show ¬ (8#u64 : U64) = 14#u64 by decide, show ¬ (8#u64 : U64) ≥ 15#u64 by decide, ↓reduceIte]
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint, fl4_abi.consts.object.Notification,
    fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped, fl4_abi.consts.object.SchedContext,
    fl4_abi.consts.object.Reply, fl4_abi.consts.object.X86Pdpt, fl4_abi.consts.object.X64Pml4,
    fl4_abi.consts.object.X64HugePage, fl4_abi.consts.object.X86Page4K, fl4_abi.consts.object.X86LargePage,
    fl4_abi.consts.object.X86PageTable, fl4_abi.consts.object.X86PageDirectory]
  simp only [show ¬ (8#u64 : U64) = 1#u64 by decide, show ¬ (8#u64 : U64) = 2#u64 by decide,
    show ¬ (8#u64 : U64) = 3#u64 by decide, show ¬ (8#u64 : U64) = 4#u64 by decide,
    show ¬ (8#u64 : U64) = 0#u64 by decide, show ¬ (8#u64 : U64) = 5#u64 by decide,
    show ¬ (8#u64 : U64) = 6#u64 by decide, show ¬ (8#u64 : U64) = 10#u64 by decide,
    show ¬ (8#u64 : U64) = 11#u64 by decide, show ¬ (8#u64 : U64) = 9#u64 by decide,
    show ¬ (8#u64 : U64) = 12#u64 by decide, show ¬ (8#u64 : U64) = 13#u64 by decide,
    show ¬ (8#u64 : U64) = 7#u64 by decide, ↓reduceIte]
  apply WP.spec_bind (copy_gm_frame (L := L) s base hal hfit)
  rintro s1 ⟨hk, hc, hm⟩
  exact (WP.spec_ok _).2 ⟨rfl, rfl, hk, hc, hm⟩


theorem create_loop_rel_gen {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val ≤ 13) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hslo : ∀ a, IsSlot th' a → a.val + 32 ≤ base.val ∨ base.val + win.val * 2 ^ zOf nt.val us.val ≤ a.val)
    (hzlo : base.val + win.val * 2 ^ zOf nt.val us.val ≤ zlo)
    (hco : ∀ (s1 : S) (a1 : A') (i : Nat), i < win.val →
      objects.create_object st arI s1 a1 nt ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ⦃ res =>
        res.1 = newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ∧ res.2.2 = a1 ∧
        L.ksb res.2.1 = L.ksb s1 ∧ ∀ w : U64, P1.Aligned w → ¬ (base.val + i * 2 ^ zOf nt.val us.val ≤ w.val ∧
          w.val < base.val + i * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val) → L.mem res.2.1 w = L.mem s1 w ⦄)
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1
        win.val ∧ L.ksb res.1 = L.ksb s ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ zOf nt.val us.val := Nat.one_le_two_pow
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1
        x.2.2.val ∧ L.ksb x.1 = L.ksb s) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hks⟩
    simp only at ha hiw hI hks ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val :=
        Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 2 ^ zOf nt.val us.val := by
        rw [hv2, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 =
          ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3]
      obtain ⟨⟨c1, s1', a1'⟩, hco1, hc1, ha1, hks1, hfr1⟩ := spec_exists (hco s1 a1 i.val hit')
      simp only at hc1 ha1 hks1 hfr1
      subst hc1 ha1
      rw [hco1]
      simp only [bind_ok, uncurry_apply_pair]
      have hbi : base.val + i.val * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val ≤
          base.val + win.val * 2 ^ zOf nt.val us.val := by omega
      have hS1 : SlotsSame th' (L.mem s1) (L.mem s1') := slotsSame_out hP' (lo := base.val + i.val * 2 ^ zOf nt.val us.val)
        (hi := base.val + i.val * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val)
        (fun a ha => by rcases hslo a ha with h | h <;> [left; right] <;> omega)
        (fun w hw ho => hfr1 w hw (by omega))
      have hdsl : ∀ j, j < win.val → IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
        fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hI := LoopInv.of_same (s' := s1') hdsl
        (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩) (by omega) hI hS1
        (fun w hw h1 h2 => hfr1 w hw (by omega))
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      obtain ⟨s3, hs3e, hs3⟩ := spec_exists (loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht hn hus hz
        hsc off.val win.val base.val hwin hfit hhigh hpA hAp hnewcv zlo zhi hzs G0 m0 hsrcd s1' i.val hit' hI)
      obtain ⟨s3', hs3', hk3⟩ := spec_exists (insert_new_cap_ksb (L := L) s1' (cslotAddr (pp.bv, idx))
        (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)))
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev))
      rw [hs3e] at hs3'; cases eq_of_ok_eq hs3'
      rw [hs3e]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hs3, by rw [hk3, hks1, hks], by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hks⟩
  · exact ⟨rfl, by simp, hinv, rfl⟩


end

/-! ## The loop with a per-object frame (PML4s) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_new_objects`' write frame, each object writing only its own
window slot** (`create_loop_rel_gen`; PML4s, by `create_object_pml4`):
slot words and the window. -/
theorem create_loop_frame_gen {A' : Type} (arI : machine.Arch A') (ar : A') (th' : TypedHeap) (hP' : Placed th')
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val ≤ 13) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (hsc : nt.val = 5 → 7 ≤ us.val)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 2 ^ zOf nt.val us.val ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val)
    (hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev))
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hslo : ∀ a, IsSlot th' a → a.val + 32 ≤ base.val ∨ base.val + win.val * 2 ^ zOf nt.val us.val ≤ a.val)
    (hzlo : base.val + win.val * 2 ^ zOf nt.val us.val ≤ zlo)
    (hco : ∀ (s1 : S) (a1 : A') (i : Nat), i < win.val →
      objects.create_object st arI s1 a1 nt ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ⦃ res =>
        res.1 = newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev ∧ res.2.2 = a1 ∧
        L.ksb res.2.1 = L.ksb s1 ∧ L.cpu res.2.1 = L.cpu s1 ∧ ∀ w : U64, P1.Aligned w → ¬ (base.val + i * 2 ^ zOf nt.val us.val ≤ w.val ∧
          w.val < base.val + i * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val) → L.mem res.2.1 w = L.mem s1 w ⦄)
    (th0 : TypedHeap) (hG0 : ∀ x ∈ G0.chains.flatten, IsSlot th0 x)
    (hds0 : ∀ j, j < win.val → IsSlot th0 (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))))
    (hs0 : IsSlot th0 (cslotAddr (pp.bv, idx)))
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1
        win.val ∧ L.ksb res.1 = L.ksb s ∧ WFrame (L := L) s res.1 (fun w => SlotSpan th0 w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val)) ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ zOf nt.val us.val := Nat.one_le_two_pow
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0
      (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1
        x.2.2.val ∧ L.ksb x.1 = L.ksb s ∧ WFrame (L := L) s x.1 (fun w => SlotSpan th0 w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val))) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hks, hW1⟩
    simp only at ha hiw hI hks hW1 ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val :=
        Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 2 ^ zOf nt.val us.val := by
        rw [hv2, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 =
          ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3]
      obtain ⟨⟨c1, s1', a1'⟩, hco1, hc1, ha1, hks1, hcp1, hfr1⟩ := spec_exists (hco s1 a1 i.val hit')
      simp only at hc1 ha1 hks1 hfr1
      subst hc1 ha1
      rw [hco1]
      simp only [bind_ok, uncurry_apply_pair]
      have hbi : base.val + i.val * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val ≤
          base.val + win.val * 2 ^ zOf nt.val us.val := by omega
      have hS1 : SlotsSame th' (L.mem s1) (L.mem s1') := slotsSame_out hP' (lo := base.val + i.val * 2 ^ zOf nt.val us.val)
        (hi := base.val + i.val * 2 ^ zOf nt.val us.val + 2 ^ zOf nt.val us.val)
        (fun a ha => by rcases hslo a ha with h | h <;> [left; right] <;> omega)
        (fun w hw ho => hfr1 w hw (by omega))
      have hdsl : ∀ j, j < win.val → IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
        fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
      have hI := LoopInv.of_same (s' := s1') hdsl
        (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩) (by omega) hI hS1
        (fun w hw h1 h2 => hfr1 w hw (by omega))
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      have hW2 : WFrame (L := L) s s1' (fun w => SlotSpan th0 w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val)) :=
        hW1.trans ⟨hks1, hcp1, fun w hw hnp => hfr1 w hw (fun h => hnp (Or.inr ⟨by omega, by omega⟩))⟩
      obtain ⟨σi, Gi, -, -, -, hMi, -, -, hcsi, -, -, -, -, hmemG, -⟩ := id hI
      have hss : IsSlot th' (cslotAddr (pp.bv, idx)) :=
        AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
      have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hMi.members _).2 ⟨hss, _, hcsi, by simp⟩
      have hnx : nextOf (L.mem s1') (cslotAddr (pp.bv, idx)) = 0#u64 ∨
          IsSlot th' (nextOf (L.mem s1') (cslotAddr (pp.bv, idx))) := by
        rcases hMi.next_mem hsm with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ((hMi.members _).1 h1).1
      obtain ⟨s3f, hs3f, hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s1'
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev) _ _ hss
        (hdsl i.val hit') hnx)
      obtain ⟨s3, hs3e, hs3⟩ := spec_exists (loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht hn hus hz
        hsc off.val win.val base.val hwin hfit hhigh hpA hAp hnewcv zlo zhi hzs G0 m0 hsrcd s1' i.val hit' hI)
      obtain ⟨s3', hs3', hk3⟩ := spec_exists (insert_new_cap_kc (L := L) s1' (cslotAddr (pp.bv, idx))
        (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)))
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev))
      rw [hs3e] at hs3'; cases eq_of_ok_eq hs3'
      rw [hs3e] at hs3f
      have e3 := eq_of_ok_eq hs3f
      subst e3
      have hW3 : WFrame (L := L) s s3 (fun w => SlotSpan th0 w ∨
          (base.val ≤ w.val ∧ w.val < base.val + win.val * 2 ^ zOf nt.val us.val)) :=
        hW2.trans ⟨hk3.1, hk3.2, fun w hw hnp => hfr w hw (fun a ha hin => by
          refine hnp (Or.inl ⟨a, ?_, hin.1, hin.2⟩)
          rcases ha with e | e | ⟨h0, e⟩
          · rw [e]; exact hs0
          · rw [e]; exact hds0 i.val hit'
          · rw [e]
            rcases hMi.next_mem hsm with h | ⟨h1, -⟩
            · exact absurd h h0
            · rcases hmemG _ h1 with hg | ⟨j, hj, e'⟩
              · exact hG0 _ hg
              · rw [e']; exact hds0 j (by omega))⟩
      rw [hs3e]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hs3, by rw [hk3.1, hks1, hks], hW3, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hks, hW1⟩
  · exact ⟨rfl, by simp, hinv, rfl, WFrame.refl s _⟩

end


end

/-! ## The spec's `init_arch_objects` for PML4s -/

section
open Fl4Spec

theorem ndb_one {σ' α β : Type} {m : NonDet σ' α} {s s' : σ'} {a : α} (h : m s = ({(a, s')}, False))
    (f : α → NonDet σ' β) : NonDet.bind m f s = f a s' := nd_bind_one h f

/-- A PML4 object at `p`. -/
def HasPm (σ : State Unit) (p : ObjRef) : Prop := ∃ pt, σ.kheap p = some (.archObj (.pageMapL4 pt))

theorem getObject_det {σ : State Unit} {p : ObjRef} {o : KernelObject} (hk : σ.kheap p = some o) :
    getObject (Z := Unit) p σ = ({(o, σ)}, False) := by
  simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt]; rfl

theorem getPml4_det {σ : State Unit} {p : ObjRef} {pt : BitVec 9 → PML4E}
    (h : σ.kheap p = some (.archObj (.pageMapL4 pt))) : getPml4 (Z := Unit) p σ = ({(pt, σ)}, False) := by
  unfold getPml4
  rw [nd_bind_single (getObject_det h)]
  rfl

theorem setPml4_det {σ : State Unit} {p : ObjRef} (h : HasPm σ p) (pt' : BitVec 9 → PML4E) :
    setPml4 (Z := Unit) p pt' σ =
      ({((), { σ with kheap := Function.update σ.kheap p (some (.archObj (.pageMapL4 pt'))) })}, False) := by
  obtain ⟨pt, hk⟩ := h
  unfold setPml4 setObject
  rw [nd_bind_single (getObject_det hk)]
  have he : aType (.archObj (.pageMapL4 pt)) = aType (.archObj (.pageMapL4 pt')) := rfl
  have ha : NonDet.assert (σ := State Unit) (aType (.archObj (.pageMapL4 pt)) = aType (.archObj (.pageMapL4 pt'))) σ =
      ({((), σ)}, False) := by simp only [NonDet.assert, he, true_and, not_true_eq_false]; rfl
  rw [nd_bind_single ha]
  rw [nd_bind_single (show (NonDet.get : NonDet (State Unit) (State Unit)) σ = ({(σ, σ)}, False) from rfl)]
  rfl

theorem pml4_base {g off : ObjRef} (hg : g.toNat % 4096 = 0) (hfit : g.toNat + 4096 ≤ 2 ^ 64) (ho : off.toNat < 4096) :
    (g + off) &&& ~~~(mask pml4Bits : ObjRef) = g := by
  have hm : ~~~(mask pml4Bits : ObjRef) = BitVec.allOnes 64 <<< 12 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hm, ← BitVec.shiftLeft_ushiftRight]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := g.toNat + off.toNat) (by omega)]
  omega

theorem getPml4e_det {σ : State Unit} {g off : ObjRef} (h : HasPm σ g) (hg : g.toNat % 4096 = 0)
    (hfit : g.toNat + 4096 ≤ 2 ^ 64) (ho : off.toNat < 4096) :
    ∃ e, getPml4e (Z := Unit) (g + off) σ = ({(e, σ)}, False) := by
  obtain ⟨pt, hk⟩ := h
  unfold getPml4e
  rw [nd_pure_bind, nd_pure_bind, pml4_base hg hfit ho, nd_bind_single (getPml4_det hk)]
  exact ⟨_, rfl⟩

theorem storePml4e_det {σ : State Unit} {g off : ObjRef} (h : HasPm σ g) (hg : g.toNat % 4096 = 0)
    (hfit : g.toNat + 4096 ≤ 2 ^ 64) (ho : off.toNat < 4096) (e : PML4E) :
    ∃ pt', storePml4e (Z := Unit) (g + off) e σ =
      ({((), { σ with kheap := Function.update σ.kheap g (some (.archObj (.pageMapL4 pt'))) })}, False) := by
  obtain ⟨pt, hk⟩ := h
  unfold storePml4e
  rw [nd_pure_bind, nd_pure_bind, pml4_base hg hfit ho, nd_bind_single (getPml4_det hk), nd_pure_bind]
  exact ⟨_, setPml4_det ⟨pt, hk⟩ _⟩

theorem uptoEnum_lt {a b x : Word} (hb : b.toNat < 512) (hx : x ∈ uptoEnum a b) : (x <<< wordSizeBits).toNat < 4096 := by
  unfold uptoEnum at hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range'] at hj
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  show (j % 2 ^ 64 * 2 ^ 3) % 2 ^ 64 < 4096
  rw [Nat.mod_eq_of_lt (a := j) (by omega)]; omega

/-- **`copy_global_mappings` in the spec**: one outcome, only the new PML4
changed (still a PML4). -/
theorem copyGM_det (σ : State Unit) (pm : ObjRef) (hg : HasPm σ σ.archState.x64GlobalPml4)
    (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0) (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hn : HasPm σ pm) (hna : pm.toNat % 4096 = 0) (hnf : pm.toNat + 4096 ≤ 2 ^ 64) :
    ∃ k, copyGlobalMappings (Z := Unit) pm σ = ({((), { σ with kheap := k })}, False) ∧
      (∀ x, x ≠ pm → k x = σ.kheap x) ∧ HasPm { σ with kheap := k } pm := by
  unfold copyGlobalMappings
  rw [nd_bind_single (show (NonDet.gets fun s : State Unit => s.archState.x64GlobalPml4) σ =
    ({(σ.archState.x64GlobalPml4, σ)}, False) from rfl)]
  rw [nd_pure_bind, nd_pure_bind, nd_pure_bind]
  have hlist : ∀ x ∈ uptoEnum (getPml4Index pptr_base) ((1 : Word) <<< ptTranslationBits - 1),
      (x <<< wordSizeBits).toNat < 4096 := fun x hx => uptoEnum_lt (by decide) hx
  generalize uptoEnum (getPml4Index pptr_base) ((1 : Word) <<< ptTranslationBits - 1) = L at hlist
  suffices ∀ (k0 : ObjRef → Option KernelObject), (∀ x, x ≠ pm → k0 x = σ.kheap x) →
      HasPm { σ with kheap := k0 } pm → HasPm { σ with kheap := k0 } σ.archState.x64GlobalPml4 →
      ∃ k, NonDet.mapMx (fun index : Word => do
          let offset ← pure (index <<< wordSizeBits)
          let pme ← getPml4e (Z := Unit) (σ.archState.x64GlobalPml4 + offset)
          storePml4e (pm + offset) pme) L { σ with kheap := k0 } = ({((), { σ with kheap := k })}, False) ∧
        (∀ x, x ≠ pm → k x = σ.kheap x) ∧ HasPm { σ with kheap := k } pm by
    exact this σ.kheap (fun _ _ => rfl) hn hg
  induction L with
  | nil => intro k0 h1 h2 _; exact ⟨k0, rfl, h1, h2⟩
  | cons i L ih =>
    intro k0 h1 h2 h3
    have hi := hlist i (List.mem_cons_self ..)
    obtain ⟨e, he⟩ := getPml4e_det h3 hga hgf hi
    obtain ⟨pt', hst⟩ := storePml4e_det (e := e) h2 hna hnf hi
    have hstep : (do
        let offset ← pure (i <<< wordSizeBits)
        let pme ← getPml4e (Z := Unit) (σ.archState.x64GlobalPml4 + offset)
        storePml4e (pm + offset) pme : NonDet (State Unit) Unit) { σ with kheap := k0 } =
        ({((), { σ with kheap := Function.update k0 pm (some (.archObj (.pageMapL4 pt'))) })}, False) := by
      rw [nd_pure_bind, nd_bind_single he]; exact hst
    simp only [NonDet.mapMx]
    rw [ndb_one hstep]
    have h3' : HasPm { σ with kheap := Function.update k0 pm (some (.archObj (.pageMapL4 pt'))) }
        σ.archState.x64GlobalPml4 := by
      by_cases hgp : σ.archState.x64GlobalPml4 = pm
      · exact ⟨pt', by simp [hgp]⟩
      · obtain ⟨q, hq⟩ := h3; exact ⟨q, by simp only [Function.update_of_ne hgp]; exact hq⟩
    exact ih (fun x hx => hlist x (List.mem_cons_of_mem _ hx)) _
      (fun x hx => by simp only [Function.update_of_ne hx]; exact h1 x hx) ⟨pt', by simp⟩ h3'

/-- **`init_arch_objects` for new PML4s** (aligned, distinct from the
global PML4): one outcome, only the new PML4s changed. -/
theorem initArch_pml4 (σ : State Unit) (dev : Bool) (ptr : ObjRef) (n sz : Nat) (refs : List ObjRef)
    (hg : HasPm σ σ.archState.x64GlobalPml4)
    (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0) (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgr : σ.archState.x64GlobalPml4 ∉ refs)
    (hr : ∀ q ∈ refs, HasPm σ q ∧ q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64) :
    ∃ k, initArchObjects (Z := Unit) (.archObject .pml4Obj) dev ptr n sz refs σ = ({((), { σ with kheap := k })}, False) ∧
      ∀ x, x ∉ refs → k x = σ.kheap x := by
  unfold initArchObjects
  simp only [NonDet.when, ↓reduceIte]
  suffices ∀ (L : List ObjRef) (k0 : ObjRef → Option KernelObject), (∀ q ∈ L, q ∈ refs) →
      (∀ x, x ∉ refs → k0 x = σ.kheap x) → (∀ q ∈ refs, HasPm { σ with kheap := k0 } q) →
      ∃ k, NonDet.mapMx copyGlobalMappings L { σ with kheap := k0 } = ({((), { σ with kheap := k })}, False) ∧
        ∀ x, x ∉ refs → k x = σ.kheap x by
    exact this refs σ.kheap (fun _ h => h) (fun _ _ => rfl) (fun q hq => (hr q hq).1)
  intro L
  induction L with
  | nil => intro k0 _ h1 _; exact ⟨k0, rfl, h1⟩
  | cons q L ih =>
    intro k0 hL h1 h2
    have hq := hL q (List.mem_cons_self ..)
    have hg0 : HasPm { σ with kheap := k0 } σ.archState.x64GlobalPml4 := by
      obtain ⟨pt, hpt⟩ := hg; exact ⟨pt, by show k0 _ = _; rw [h1 _ hgr]; exact hpt⟩
    obtain ⟨k1, hk1, hk1o, hH⟩ := copyGM_det { σ with kheap := k0 } q hg0 hga hgf (h2 q hq) (hr q hq).2.1 (hr q hq).2.2
    simp only [NonDet.mapMx]
    rw [ndb_one hk1]
    refine ih k1 (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (fun x hx => ?_) (fun r hr' => ?_)
    · rw [hk1o x (fun e => hx (e ▸ hq))]; exact h1 x hx
    · by_cases hrq : r = q
      · subst hrq; exact hH
      · obtain ⟨pt, hpt⟩ := h2 r hr'
        exact ⟨pt, by show k1 r = _; rw [hk1o r hrq]; exact hpt⟩

end

/-! ## Retype of PML4s -/

theorem StateRel.of_agree {th : TypedHeap} {mem : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : StateRel th mem σ)
    (hk : ∀ q kd, th q = some kd → 1 ≤ objSize kd → σ'.kheap q.bv = σ.kheap q.bv) : StateRel th mem σ' :=
  ⟨fun p r hp => by rw [hk p _ hp (objSize_pos_cnode r)]; exact h.cnode p r hp,
    fun t ht => by rw [hk t _ ht (by simp [objSize])]; exact h.tcb t ht⟩

theorem invokeUntyped_noreset_init (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (srcSl : Fl4Spec.CslotPtr)
    (base retypeBase : Fl4Spec.ObjRef) (t : Fl4Spec.ApiObjectType) (us : Nat) (slots : List Fl4Spec.CslotPtr)
    (dev : Bool) (σ σa σb0 σb σf : Fl4Spec.State Unit) (capS : Fl4Spec.Cap) (ptrs : List Fl4Spec.ObjRef)
    (hg : Fl4Spec.getCap (Z := Unit) srcSl σ = ({(capS, σ)}, False))
    (hs : Fl4Spec.setCap (Z := Unit) (.untypedCap dev base (Fl4Spec.bitsOf capS)
      (Fl4Spec.unat (retypeBase + (BitVec.ofNat 64 slots.length <<< bitsApi t us) - base))) srcSl σ =
        ({((), σa)}, False))
    (hr : Fl4Spec.retypeRegionWith (Z := Unit) bitsApi retypeBase slots.length us t dev σa = ({(ptrs, σb0)}, False))
    (hi : Fl4Spec.initArchObjects (Z := Unit) t dev retypeBase slots.length us ptrs σb0 = ({((), σb)}, False))
    (hm : Fl4Spec.NonDet.mapMx (Fl4Spec.createCap (Z := Unit) t us srcSl dev) (slots.zip ptrs) σb =
      ({((), σf)}, False)) :
    (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype srcSl false base retypeBase t us slots dev)).run σ =
      ({(.ok (), σf)}, False) := by
  unfold Fl4Spec.invokeUntypedWith
  simp only [Fl4Spec.NonDetE.whenE, Bool.false_eq_true, ↓reduceIte, ndE_pure_bind]
  apply run_liftE'
  show (Fl4Spec.getCap srcSl >>= _) σ = _
  rw [nd_bind_single hg]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) _) >>= _) σ = _
  rw [nd_pure_bind]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) _) >>= _) σ = _
  rw [nd_pure_bind]
  show (Fl4Spec.setCap _ _ >>= _) σ = _
  rw [nd_bind_one hs]
  show (Fl4Spec.retypeRegionWith _ _ _ _ _ _ >>= _) σa = _
  rw [nd_bind_one hr]
  show (Fl4Spec.initArchObjects _ _ _ _ _ _ >>= _) σb0 = _
  rw [nd_bind_one hi]
  exact hm

theorem setCap_other {σ σ' : Fl4Spec.State Unit} {pb : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    {idx : List Bool} {a : Fl4Spec.Cap} (hk : σ.kheap pb = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs)
    (hidx : idx.length = r) (h : Fl4Spec.setCap (Z := Unit) a (pb, idx) σ = ({((), σ')}, False)) {x : Fl4Spec.ObjRef}
    (hx : x ≠ pb) : σ'.kheap x = σ.kheap x ∧ σ'.archState = σ.archState := by
  have h1 := (setCap_cnode (Z := Unit) a hk hwf hidx).symm.trans h
  have e : setCnodeSlot σ pb r cs idx a = σ' := by simpa using h1
  rw [← e]; exact ⟨by simp [setCnodeSlot, Function.update_of_ne hx], rfl⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`untyped::retype` (no reset) refines `invoke_untyped` for PML4s**
(type 8): as `retype_full`, the spec's `init_arch_objects` copying the
global mappings into the new PML4s (the global PML4 a PML4 object of the
spec, aligned, outside the untyped region), FL4's `create_object` doing the
same in each new object. -/
theorem retype_full_pml4 {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 8) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi (.archObject .pml4Obj) us.val = zOf nt.val us.val)
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val)) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) (.archObject .pml4Obj) us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧ ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s) σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
        WFrame (L := L) s res.2.1 (fun w => SlotSpan th w ∨ ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ≤ w.val ∧
          w.val < (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)) ∧
        ∃ A k w dslot cj, RetExp th th' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
          A = (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX th th' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC th dslot w ⦄ := by
  -- sizes and the region
  have htP : t = .archObject .pml4Obj := by rw [hnt] at ht; simpa [objTypeOf, Fl4Spec.archDataToObjType] using ht.symm
  subst htP
  have hz47 : zOf nt.val us.val ≤ 47 := by simp [zOf, hnt]
  have hz12 : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by omega
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  set z := zOf nt.val us.val with hzdef
  have hz : z < 64 := by omega
  set k := 2 ^ z with hkdef
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  obtain ⟨hA1, hA2, hA3, hA4⟩ := retype_region p fi sb.val z win.val hsb hz hpal hpfit hfi hw1 hmem
  rw [← hkdef] at hA2 hA3 hA4
  set Ab := Fl4Spec.alignUp (p.bv + fi.bv) z with hAbdef
  set A := Ab.toNat with hAdef
  set aligned : U64 := ⟨Ab⟩ with halig
  have halv : aligned.val = A := rfl
  have hn14 : nt.val < 14 := by omega
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th src := hAs.isSlot
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hcv0 := capV_of_capAt hcap
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi dev hsb hpfit
  -- FL4: the cap update, then the loop
  obtain ⟨total, htot, hret⟩ := retype_noreset_eq (L := L) arI s ar src aligned nt us dest off win dev hn14 hus hz
    p sb fi dev hcap
  rw [hret]
  set nfi := core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p with hnfi
  set srcC' : capability.Cap := .Untyped p sb nfi dev with hsrcC'
  have he' : EncWf srcC' := by
    have : EncWf (capability.Cap.Untyped p sb fi dev) := by rw [capAt_words] at hcap; exact decode_encWf hcap
    exact ⟨this.1, this.2⟩
  obtain ⟨s1, hs1, hU1⟩ := spec_exists (set_cap_upd (L := L) hP s hs srcC' he')
  obtain ⟨s1', hs1', σa, hσa, hR1, hV1, hcdt1, hio1⟩ := spec_exists
    (retype_set_untyped_rel (L := L) th s σ hR hV hP hpp hidx hcap aligned total win z htot)
  rw [hs1] at hs1'; have e := eq_of_ok_eq hs1'; subst e
  rw [hs1]; simp only [bind_ok]
  obtain ⟨hcs1, hco1, hlk1, hfr1⟩ := hU1
  have hupd : CapShapeUpd th (L.mem s) (L.mem s1) src :=
    { links := hlk1, caps := hco1
      shp := by rw [hcs1, hcv0]; rfl
      bdg := by rw [hcs1, hcv0]; rfl
      nn := by rw [hcs1]; simp [srcC'] }
  have hM1 := hupd.mdbLinks hM hsrcm
  have hI1 := hupd.mdbInv hM hI
  have hC1 := hupd.cdtRel hC hcdt1 hio1
  -- the spec's pieces
  have hgs : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hwl : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hss : Fl4Spec.setCap (Z := Unit) (.untypedCap dev p.bv (Fl4Spec.bitsOf (.untypedCap dev p.bv sb.val fi.val))
      (Fl4Spec.unat (Ab + (BitVec.ofNat 64 (windowSlots dest r off.val win.val).length <<< bitsApi (.archObject .pml4Obj) us.val) - p.bv)))
      (pp.bv, idx) σ = ({((), σa)}, False) := by
    rw [hwl, hb]; exact hσa
  have hrr := retypeRegionWith_eq bitsApi Ab win.val us.val (.archObject .pml4Obj) dev σa
  rw [hb] at hrr
  rw [← hwl] at hrr
  -- the free region after the cap update
  have hzero1 : ZeroRegion (L.mem s1) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    have hne : w.val ≠ src.val ∧ w.val ≠ src.val + 8 := by
      rcases hfree q kq hq with h | h <;> constructor <;> omega
    rw [hfr1 w hw hne.1 hne.2]; exact hzero w hw h1 h2
  have hrf : RegionFree th A (A + win.val * k) := by
    intro q kd hq
    rcases hfree q kd hq with h | h
    · left; omega
    · right; omega
  have hnn : ∀ q kd, th q = some kd → 1 ≤ objSize kd → ¬ NewP A k win.val q :=
    fun q kd hq hs1 => not_newP hk1 hrf hq hs1
  have key : ∀ (th' : TypedHeap) (σb : Fl4Spec.State Unit), Placed th' → StateRel th' (L.mem s1) σb →
      SlotsValid th' (L.mem s1) → MdbLinks th' (L.mem s1) G → CdtRel th' (L.mem s1) σb G →
      ∀ σb0 : Fl4Spec.State Unit,
      Fl4Spec.retypeRegionWith (Z := Unit) bitsApi Ab (windowSlots dest r off.val win.val).length us.val
        (.archObject .pml4Obj) dev σa = ({(regionPtrs Ab (windowSlots dest r off.val win.val).length k, σb0)}, False) →
      Fl4Spec.initArchObjects (Z := Unit) (.archObject .pml4Obj) dev Ab (windowSlots dest r off.val win.val).length
        us.val (regionPtrs Ab (windowSlots dest r off.val win.val).length k) σb0 = ({((), σb)}, False) →
      th' pp = some (.cnode rs) → th' dest = some (.cnode r) →
      (∀ i, i < win.val → CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * k)⟩ us dev)) →
      (∀ a, IsSlot th' a → a.val + 32 ≤ A + win.val * k ∨ p.val + 2 ^ sb.val ≤ a.val) →
      (∀ a, IsSlot th' a → a.val + 32 ≤ A ∨ A + win.val * k ≤ a.val) →
      (FinInv th (L.mem s) σ G → KTyped th' σb) →
      (∀ q kd, th' q = some kd → (th q = some kd ∧ (NewQ A k win.val (cjOf nt.val us dev aligned.val k) q →
        objSize kd = 0)) ∨ (NewQ A k win.val (cjOf nt.val us dev aligned.val k) q ∧ objSize kd ≤ k)) →
      (∀ q, th' q = if (∃ i, i < win.val ∧ q.val = A + i * k) ∧ (thKindN nt.val us.val).isSome then
        thKindN nt.val us.val else th q) →
      (do
        let (s2, a2) ← objects.create_new_objects st arI s1 ar nt src dest off win aligned us dev
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a2)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv Ab (.archObject .pml4Obj) us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧ ZeroRegion (L.mem res.2.1) (A + win.val * k) (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s) σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
        WFrame (L := L) s res.2.1 (fun w => SlotSpan th w ∨ (A ≤ w.val ∧ w.val < A + win.val * k)) ∧
        ∃ A k w dslot cj, RetExp th th' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
          A = Ab.toNat ∧ k = 2 ^ z ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX th th' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC th dslot w ⦄ := by
    intro th' σb hP' hR' hV' hM' hC' σb0 hrb hini hpp' hdest' hcv' hzs hslo hKb hth hthE
    have hbA : (BitVec.ofNat 64 aligned.val : BitVec 64) = Ab := by
      rw [← bv_eq_ofNat]
    have hsrc1 : capAt (L.mem s1) src = ok srcC' := by rw [capAt_capV, hcs1]
    have hsrcd : ∀ j, j < win.val → src ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) := by
      intro j hj e
      have := hempty (off.val + j) (by omega) (by omega)
      rw [← e, hcap] at this; cases eq_of_ok_eq this
    -- the loop invariant at the start
    have hinv0 : LoopInv (L := L) th' (pp.bv, idx) srcC' σb
        (Fl4Spec.createCap (Z := Unit) (.archObject .pml4Obj) us.val (pp.bv, idx) dev)
        ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val k))
        aligned.val k win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
        (A + win.val * k) (p.val + 2 ^ sb.val) G (L.mem s1) (cjOf nt.val us dev aligned.val k) s1 0 := by
      refine ⟨σb, G, fun σf h => h, hR', hV', hM', hC', hI1, hsrc1, ?_, ?_, ?_,
        fun w hw h1 h2 => hzero1 w hw (by omega) h2, fun x hx => Or.inl hx, fun x hx => hx,
        fun j hj => absurd hj (by omega), fun x _ => rfl, fun y x => ⟨Or.inl, by
          rintro (h | ⟨j, hj, -⟩)
          · exact h
          · omega⟩, fun h => h, fun ch hch => ⟨ch, hch, fun z hz => hz⟩, fun x _ => rfl⟩
      · intro j _ hj
        have hj' : off.val + j < 2 ^ r := by omega
        have hd : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
          ⟨dest, off.val + j, Or.inl ⟨r, hdest, hj'⟩, rfl⟩
        have hnull := hempty (off.val + j) (by omega) (by omega)
        have hne : slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) ≠ src := by
          intro e; rw [e, hcap] at hnull; cases eq_of_ok_eq hnull
        rw [capAt_capV, hco1 _ hd hne, ← capAt_capV]; exact hnull
      · intro x hx hp
        have hxs : IsSlot th x := ((hM.members x).1 hx).1
        by_cases hxa : x = src
        · subst hxa
          rw [hcs1]
          refine ⟨?_, Or.inr ⟨rfl, ⟨le_refl _, le_refl _⟩⟩⟩
          obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
          rw [e1, e2, hsb', hst']; have := Nat.one_le_two_pow (n := sb.val); omega
        · rw [hco1 x hxs hxa] at hp ⊢
          refine ⟨hU.reg x hx hp, ?_⟩
          rcases hU.noov src hsrcm p sb fi dev hcv0 x hx hp with h | ⟨hu, hw⟩
          · left; unfold DisjR at h ⊢; simp only [Nat.zero_mul, Nat.add_zero]; omega
          · right; refine ⟨hu, ?_⟩
            obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
            unfold Within at hw ⊢; rw [hcv0] at hw; rw [e1, e2]; exact hw
      · intro y hy
        obtain ⟨hp1, hp2, hp3⟩ := hU.inc src hsrcm p sb fi dev hcv0 y hy
        have hym := (desc_mem hM hy).1
        have hys : IsSlot th y := ((hM.members y).1 hym).1
        have hya : y ≠ src := by
          intro e; subst e
          rw [hcv0, hst'] at hp3
          have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
            rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
            simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
            have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
            rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
              rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
            omega
          rw [this, Nat.shiftRight_eq_div_pow, show 2 ^ sb.val - fi.val = 0 by omega] at hmem
          simp at hmem; omega
        rw [hco1 y hys hya]
        unfold DisjR; left; simp only [Nat.zero_mul, Nat.add_zero]; omega
    obtain ⟨⟨s2, a2⟩, hres, ha2, hfin, hks2', hW2⟩ := spec_exists (create_loop_frame_gen (L := L) arI ar th' hP' hpp' hidx hsb hpfit σb
      hdest' (by omega) nt us dev _ ht (by omega) hus hz hsc off win aligned hwin
      (by simp only [← hzdef, ← hkdef, halv]; omega) (by simp only [halv]; omega) (by simp only [halv]; omega)
      (by simp only [← hzdef, ← hkdef, halv]; omega) hcv' (A + win.val * k) (p.val + 2 ^ sb.val) hzs G (L.mem s1)
      hsrcd (by simp only [halv, ← hzdef, ← hkdef]; exact hslo) (by simp only [halv, ← hzdef, ← hkdef]; omega)
      (fun s2 a2 i hi => by
        have hk4 : 2 ^ zOf nt.val us.val = 4096 := by simp [zOf, hnt]
        have hlt : (i + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hi
        rw [Nat.add_mul, Nat.one_mul] at hlt
        have hkk : k = 4096 := hk4
        rw [hkk] at hA2 hA3
        have hval : (BitVec.ofNat 64 (aligned.val + i * 2 ^ zOf nt.val us.val)).toNat = A + i * 4096 := by
          rw [hk4, halv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine WP.spec_mono (create_object_pml4 (L := L) arI s2 a2 nt _ us dev hnt
          (by show (BitVec.ofNat 64 _).toNat % 8 = 0; rw [hval]; omega)
          (by show (BitVec.ofNat 64 _).toNat + 4096 ≤ _; rw [hval]; omega)) ?_
        rintro res ⟨h1, h2, h3, hc, h4⟩
        refine ⟨h1, h2, h3, hc, fun w hw ho => h4 w hw ?_⟩
        show ¬ ((BitVec.ofNat 64 _).toNat ≤ w.val ∧ w.val < (BitVec.ofNat 64 _).toNat + 4096)
        rw [hval]; rw [hk4, halv] at ho; exact ho)
      th (fun x hx => ((hM.members x).1 hx).1) (fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩) hs
      s1 hinv0)
    rw [hres]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    simp only at ha2 hfin
    obtain ⟨σf, Gf, hchain, hRf, hVf, hMf, hCf, hIf, -, -, -, -, hZf, hT1, hT1b, hT2a, hT2b, hT3, hFf, hChf, hRvf⟩ := hfin
    have hdrop : ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val k)).drop
        win.val = [] := by
      apply List.drop_of_length_le; simp [windowSlots, regionPtrs]
    rw [hdrop] at hchain
    have hmx := hchain σf (mapMx_nil _ _)
    have hfiL : fi.val < 2 ^ sb.val := by
      have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
        rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
        simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
        have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
        rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
          rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
        omega
      rw [this, Nat.shiftRight_eq_div_pow] at hmem
      by_contra hc
      rw [show 2 ^ sb.val - fi.val = 0 by omega] at hmem; simp at hmem; omega
    have hnfiv : nfi.val = A + win.val * k - p.val := by
      rw [← hA4]
      show (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p).bv.toNat = _
      rw [core.num.U64.wrapping_sub_bv_eq, core.num.U64.wrapping_add_bv_eq, htot, ← bv_eq_ofNat]
    have hzv : zOf nt.val us.val < 64 := by omega
    have hkk : 2 ^ zOf nt.val us.val = k := rfl
    have hRD : RetypeDelta th (L.mem s) (L.mem s1) (L.mem s2) G Gf src p sb fi nfi dev A k win.val
          (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) (cjOf nt.val us dev aligned.val k) := by
      refine ⟨hM, hsrcm, hcv0, hcs1, fun x hx hxs => hco1 x ((hM.members x).1 hx).1 hxs, hfiL, hA1,
        by omega, by omega, by omega, fun j _ => physF_newCap _ _ _ _, fun j hj => ?_, fun j hj => ?_,
        fun j hj hu => ?_, fun j hj hm => ?_, fun j l hj hl he => ?_, hT1, hT1b, hT2a, hT2b, hT3⟩
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨c1, -⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c1]; show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨-, c2⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c2, hkk]; show (BitVec.ofNat 64 (A + j * k)).toNat + _ - 1 = _; simp; omega
      · unfold cjOf at hu ⊢
        rw [halv] at hu ⊢
        obtain ⟨hn0, he⟩ := isUt_newCap hu
        refine ⟨us, dev, he, ?_⟩
        show 2 ^ us.val = 2 ^ zOf nt.val us.val
        simp [zOf, hn0]
      · obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 hm
        rw [hempty (off.val + j) (by omega) (by omega)] at h0
        exact hn0 (eq_of_ok_eq h0).symm
      · have hj' : IsSlotAt th dest (off.val + j) := Or.inl ⟨r, hdest, by omega⟩
        have hl' : IsSlotAt th dest (off.val + l) := Or.inl ⟨r, hdest, by omega⟩
        by_contra hne
        rcases hj'.apart hP hl' (fun ⟨_, h2⟩ => hne (by omega)) with h | h <;>
          (change slotOf dest (off.val + j) = slotOf dest (off.val + l) at he; rw [he] at h; omega)
    have hks2 : L.ksb s2 = L.ksb s := by
      obtain ⟨s1k, hs1k, k1⟩ := spec_exists (set_cap_ksb (L := L) src s srcC')
      rw [hs1] at hs1k; cases eq_of_ok_eq hs1k
      rw [hks2', k1]
    have hW : WFrame (L := L) s s2 (fun w => SlotSpan th w ∨ (A ≤ w.val ∧ w.val < A + win.val * k)) := by
      have hs' : IsSlot th src := hs
      obtain ⟨s1k, hs1k, k1⟩ := spec_exists (set_cap_kc (L := L) src s srcC')
      rw [hs1] at hs1k; cases eq_of_ok_eq hs1k
      refine WFrame.trans (s2 := s1) ⟨k1.1, k1.2, fun w hw hn => hfr1 w hw
        (fun e => hn (Or.inl ⟨src, hs', by omega, by omega⟩)) (fun e => hn (Or.inl ⟨src, hs', by omega, by omega⟩))⟩
        (hW2.mono fun w h => by rw [halv] at h; exact h)
    refine ⟨rfl, ha2, σf, Gf, th', ?_, hP', hRf, hVf, hMf, hCf, hIf, ⟨hRD.utinv hU, MdbStep.retype hRD hI hChf
          (fun z hz => by rw [hRvf z hz, hupd.rv ((hM.members z).1 hz).1])
          (cjOf_vplaced rfl hA2 (by omega) (by omega))⟩, hZf,
      fun hFI => ⟨(hKb hFI).sub (ksub_of_eq (nks_mapMx (nks_createCap _ _ _ _) _) hmx),
        hFf (hFI.fm.recap hM.tree.nodup src (by rw [hcs1, hcv0]; exact CapSim.of_shape rfl rfl)
          (fun z hz hzs => hco1 z ((hM.members z).1 hz).1 hzs))⟩, hks2, hW, A, k, win.val, _, _,
      hRD.toExp hU hMf hth, rfl, rfl, rfl, fun j hj hu => (isUt_newCap (by unfold cjOf at hu; exact hu)).1, ⟨hthE, hrf⟩, rfl, fun j hj => ⟨dest, r, hdest, off.val + j, by omega, rfl⟩⟩
    · rw [hbA] at hmx
      exact invokeUntyped_noreset_init bitsApi (pp.bv, idx) p.bv Ab _ us.val _ dev σ σa σb0 σb σf _ _ hgs hss hrb
        hini (by rw [hwl]; exact hmx)
  have hzeroA : ZeroRegion (L.mem s1) A (A + win.val * k) := fun w hw h1 h2 => hzero1 w hw (by omega) (by omega)
  have hzsOld : ∀ a, IsSlot th a → a.val + 32 ≤ A + win.val * k ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hfitA : A + win.val * k ≤ 2 ^ 64 := by omega
  have hio1' : ∀ sl, σa.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  have h4 : ¬ nt.val = 4 := by omega
  -- PML4s: the typed heap stays; the spec copies the global mappings
  have hcvo : ∀ i, i < win.val → CapValid th (newCapOf nt.val ⟨BitVec.ofNat 64 (A + i * k)⟩ us dev) := by
    intro i hi
    have hlt : A + i * k < 2 ^ 64 := by
      have : (i + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hi
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have hv : (⟨BitVec.ofNat 64 (A + i * k)⟩ : U64).val = A + i * k := by
      show (BitVec.ofNat 64 (A + i * k)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    apply newCapOf_ind (CapValid th) <;> intros <;> first | trivial | omega |
      (simp only [CapValid]; intro he; have h0 : A + i * k = 0 := hv.symm.trans (congrArg UScalar.val he); omega)
  have h4096 : k = 4096 := by rw [hkdef, hzdef]; simp [zOf, hnt]
  obtain ⟨hR', hC'⟩ := extend_other_rel th (L.mem s1) σa G hR1 hC1 Ab A win.val k rfl hk1 hfitA hrf
    (Fl4Spec.defaultObject (.archObject .pml4Obj) dev us.val σa.curDomain)
  set σb0 := regionHeap σa (regionPtrs Ab win.val k) (Fl4Spec.defaultObject (.archObject .pml4Obj) dev us.val σa.curDomain)
    with hσb0
  have hrefs : ∀ q ∈ regionPtrs Ab win.val k, ∃ i, i < win.val ∧ q.toNat = A + i * k := by
    intro q hq
    obtain ⟨i, hi, he⟩ := (mem_regionPtrs Ab A k win.val rfl hk1 hfitA ⟨q⟩).1 hq
    exact ⟨i, hi, he⟩
  -- the spec state after `set_cap`: only the CNode changed
  obtain ⟨cs0, hk0, hwf0, -⟩ := hR.cnode pp rs hpp
  have hglob : σ.archState.x64GlobalPml4 ∉ regionPtrs Ab win.val k := by
    intro hq
    obtain ⟨i, hi, he⟩ := hrefs _ hq
    have : i * k < win.val * k := Nat.mul_lt_mul_of_pos_right hi (by omega)
    exact hgreg ⟨by omega, by omega⟩
  have hgne : σ.archState.x64GlobalPml4 ≠ pp.bv := by
    intro e; obtain ⟨pt, hpt⟩ := hgpm; rw [e, hk0] at hpt; cases hpt
  have hσae := setCap_other hk0 hwf0 hidx hσa hgne
  have hσb0a : σb0.archState = σ.archState := hσae.2
  have hg0 : HasPm σb0 σb0.archState.x64GlobalPml4 := by
    obtain ⟨pt, hpt⟩ := hgpm
    refine ⟨pt, ?_⟩
    rw [hσb0a]
    show (regionHeap σa _ _).kheap _ = _
    simp only [regionHeap, foldr_update_apply, if_neg hglob]
    rw [hσae.1]; exact hpt
  obtain ⟨kb, hini, hkb⟩ := initArch_pml4 σb0 dev Ab win.val us.val (regionPtrs Ab win.val k) hg0
    (by rw [hσb0a]; exact hga) (by rw [hσb0a]; exact hgf) (by rw [hσb0a]; exact hglob)
    (fun q hq => by
      obtain ⟨i, hi, he⟩ := hrefs q hq
      have : (i + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hi
      rw [Nat.add_mul, Nat.one_mul] at this
      have hA2' := hA2
      have hfitA' := hfitA
      rw [h4096] at hA2' hfitA' this
      refine ⟨⟨fun _ => .invalidPML4E, ?_⟩, by rw [he, h4096]; omega, by rw [he, h4096]; omega⟩
      show (regionHeap σa _ _).kheap q = _
      simp only [regionHeap, foldr_update_apply, if_pos hq]; rfl)
  refine key th { σb0 with kheap := kb } hP (StateRel.of_agree hR' (fun q kd hq hs1 => ?_)) hV1 hM1
    (hC'.of_cdt rfl rfl) σb0 ?_ ?_ hpp hdest hcvo hzsOld ?_ ?_ (th_same_shape hk1 hrf)
    (fun q => by simp [thKindN, hnt])
  · show kb q.bv = _
    apply hkb
    intro hq'
    obtain ⟨i, hi, he⟩ := hrefs _ hq'
    have : i * k < win.val * k := Nat.mul_lt_mul_of_pos_right hi (by omega)
    rcases hrf q kd hq with h | h <;> rw [show q.bv.toNat = q.val from rfl] at he <;> omega
  · rw [hrr]; simp only [ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, hwl]; rfl
  · rw [hwl]; exact hini
  · intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hrf q kq hq with h | h
    · left; omega
    · right; omega
  · intro hFI
    have hKa : KTyped th σa := hFI.kt.sub (ksub_of_eq (nks_setCap _ _) hσa)
    exact (ktyped_region hKa Ab A win.val k rfl hk1 hfitA hrf (fun _ _ _ _ => rfl) _
      (fun q _ => ⟨fun r cs he _ => by simp [Fl4Spec.defaultObject] at he,
        fun t he => by simp [Fl4Spec.defaultObject] at he⟩)).sub
      (ksub_of_eq (nks_initArchObjects _ _ _ _ _ _) hini)


/-- **`untyped::retype` with a reset refines `invoke_untyped` with
`reset = True`** for PML4s (`retype_reset_gen` with `retype_full_pml4`),
the global PML4 a PML4 object of the spec outside the region. -/
theorem retype_reset_pml4 (ar : A') (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false)) (hfi0 : fi.val ≠ 0)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame) {E : S → Prop} (hPP : PPHyp (L := L) arI th p sb E)
    (hEk : EKept (L := L) E p sb (cslotAddr (pp.bv, idx))) (hE : E s) (hEksb : ∀ t, E t → L.ksb t = L.ksb s)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 8) (hus : us.val < 64)
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val))
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r))
    (hdout : ¬ (p.val ≤ dest.val ∧ dest.val < p.val + 2 ^ sb.val)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - (0 : BitVec 64)).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) true
      ⟨Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
          (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) false)).run σ (fun _ => True) ∧
      ((res.1 = .Err .Preempted ∧ ∃ σ' f,
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) false)).run σ (TopP (.error ()) σ') ∧
          ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb false
            (L.mem res.2.1) σ' f ∧ MdbStep (L.mem s) G (L.mem res.2.1) G ∧
          (FinInv th (L.mem s) σ G → FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G) ∧
          L.ksb res.2.1 = L.ksb s ∧ untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok res ∧
          ∀ dslot cj, RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s)
            (L.mem res.2.1) G G p.val 1 0 dslot cj (cslotAddr (pp.bv, idx))) ∨
       (res.1 = .Ok () ∧ ∃ σ' G' th'',
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) false)).run σ (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧
          (FinInv th (L.mem s) σ G → FinInv th'' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
          (∃ t1 a1, untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), t1, a1) ∧
            WFrame (L := L) t1 res.2.1 (fun w => SlotSpan (restrictTh th p.val (p.val + 2 ^ sb.val)) w ∨
              ((Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ≤ w.val ∧
                w.val < (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val))) ∧
          ∃ A k w dslot cj, RetExp th th'' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
            A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us false A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w)) ⦄ := by
  have htP : t = .archObject .pml4Obj := by rw [hnt] at ht; simpa [objTypeOf, Fl4Spec.archDataToObjType] using ht.symm
  subst htP
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hcv := capV_of_capAt hcap
  have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten :=
    (hM.members _).2 ⟨AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩, _, hcap, by simp⟩
  have hrx := hU.reg _ hxm (by rw [hcv]; exact physF_ut _ _ _ _)
  rw [hcv] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  refine retype_reset_gen arI ar th s σ G hR hV hP hM hC hI hU hpp hidx hcap hfi0 hnd hpal hsb4 hN hns hzero hrcb hppS
    hPP hEk hE _ nt us dest off win bitsApi _ (.archObject .pml4Obj) us.val _ (fun th'' t1 res => WFrame (L := L) t1 res.2.1 (fun w => SlotSpan (restrictTh th p.val (p.val + 2 ^ sb.val)) w ∨
              ((Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ≤ w.val ∧
                w.val < (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)))
    (fun th'' A k w dslot cj => A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us false A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w) ?_ hEksb
  intro t1 a1 σt hRR hZ hF hio harch hkh _
  obtain ⟨hdest', he1⟩ := reset_window hP hdest hdout (by rw [hcap]; simp) off win hwin hempty hF
  have hcap1 : capAt (L.mem t1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 false) := by
    rw [capAt_capV, hRR.cap]
  have hpp' : restrictTh th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs) := by
    obtain ⟨q, j, hj, hq, he⟩ := (show AbsSlot th (pp.bv, idx) from ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩).at
    have : pp = q := bv_inj hq
    subst this
    rw [restrictTh_out (hj.obj_out hP hN (by rw [← he]; exact hns _ hxm))]; exact hpp
  have hgne : σ.archState.x64GlobalPml4 ≠ pp.bv := by
    intro e; obtain ⟨pt, hpt⟩ := hgpm; obtain ⟨cs, hk, -⟩ := hR.cnode pp rs hpp; rw [e, hk] at hpt; cases hpt
  have hgout : σ.archState.x64GlobalPml4 ∉ regionSet p.bv sb.val := by
    rw [show σ.archState.x64GlobalPml4 = (⟨σ.archState.x64GlobalPml4⟩ : U64).bv from rfl, regionSet_iff _ _ _ hsb hfit]
    exact hgreg
  refine WP.spec_mono (retype_full_pml4 (L := L) arI a1 _ t1 σt G hRR.R hRR.V hP.restrict hRR.M hRR.C hRR.I hRR.U
    (fun sl h => horig sl (by rw [← hio]; exact h)) hpp' hidx hcap1 hpal hfit (by simp) hhigh nt us _ ht hnt hus
    hdest' hr off win hwin hw1 hmem he1 (by simpa using RegionFree.restrict hN) (hZ rfl) bitsApi hb
    (by rw [harch]; obtain ⟨pt, hpt⟩ := hgpm; exact ⟨pt, by rw [hkh _ hgout hgne]; exact hpt⟩)
    (by rw [harch]; exact hga) (by rw [harch]; exact hgf) (by rw [harch]; exact hgreg)) ?_
  rintro res ⟨h1, -, σ', G', th'', hrun, h⟩
  exact ⟨h1, σ', G', th'', hrun, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩



/-- `set_thread_state` keeps the arch state (and changes the heap only at
the thread). -/
theorem setThreadState_arch (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (tcb : Fl4Spec.Tcb)
    (hk : σ.kheap t = some (.tcb tcb)) (ts : Fl4Spec.ThreadState) :
    ∃ σ1, Fl4Spec.setThreadState (Z := Unit) t ts σ = ({((), σ1)}, False) ∧
      σ1.kheap = Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })) ∧
      σ1.archState = σ.archState := by
  set σ0 : Fl4Spec.State Unit := { σ with kheap := Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })) }
  have hg : Fl4Spec.NonDet.getsThe (Fl4Spec.getTcb (Z := Unit) t) σ = ({(tcb, σ)}, False) := by
    simp [Fl4Spec.NonDet.getsThe, Fl4Spec.getTcb, Fl4Spec.readObject, hk, Fl4Spec.NonDet.assertOpt]; rfl
  have ho : Fl4Spec.getObject (Z := Unit) t σ = ({(.tcb tcb, σ)}, False) := by
    simp [Fl4Spec.getObject, Fl4Spec.NonDet.getsThe, Fl4Spec.readObject, hk, Fl4Spec.NonDet.assertOpt]; rfl
  have ha : (Fl4Spec.NonDet.assert (Fl4Spec.aType (.tcb tcb) = Fl4Spec.aType (.tcb { tcb with tcbState := ts })) :
      Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) σ = ({((), σ)}, False) := by
    simp [Fl4Spec.NonDet.assert, Fl4Spec.aType]
  have h1 : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t σ = ({((), σ0)}, False) := by
    unfold Fl4Spec.threadSet
    rw [nd_bind_single hg]
    unfold Fl4Spec.setObject
    rw [nd_bind_single ho, nd_bind_single ha, nd_bind_single (show Fl4Spec.NonDet.get σ = ({(σ, σ)}, False) from rfl)]
    rfl
  unfold Fl4Spec.setThreadState
  rw [nd_bind_one h1]
  unfold Fl4Spec.setThreadStateAct
  rw [nd_bind_single (show Fl4Spec.NonDet.gets _ σ0 = _ from rfl),
    nd_bind_single (show Fl4Spec.NonDet.gets _ σ0 = _ from rfl),
    nd_bind_single (show Fl4Spec.NonDet.gets _ σ0 = _ from rfl)]
  unfold Fl4Spec.NonDet.when
  split
  · exact ⟨_, rfl, rfl, rfl⟩
  · exact ⟨σ0, rfl, rfl, rfl⟩

/-- **The success continuation of `decode` for PML4s**, resets included
(`RetPostN`), the global PML4 a PML4 object of the spec, aligned, outside
the untyped region. -/
theorem retype_cont_pml4N {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ct : U64) (hcur : σ.curThread = ct.bv) (hct : sched.cur_thread st s = ok ct) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    -- the reset of a used region
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64)
    (hn8 : nt.val = 8) (hb : bitsApi t us.val = zOf nt.val us.val)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val))
    (hctx : RetCtx (L := L) th s σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev) ⦃ res =>
      RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
  have htP : t = .archObject .pml4Obj := by
    have := hctx.ty; rw [hn8] at this; simpa [objTypeOf, Fl4Spec.archDataToObjType] using this.symm
  have hgct : σ.archState.x64GlobalPml4 ≠ ct.bv := by
    intro e; obtain ⟨pt, hpt⟩ := hgpm; obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb; rw [e, hkt] at hpt; cases hpt
  by_cases hcase : reset = true ∧ fi.val ≠ 0
  case neg =>
    have hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0 := by
      intro hnc
      by_contra hf
      exact hcase ⟨by rw [hctx.resetEq]; simpa using hnc, hf⟩
    have hactZ' : ¬ (p.val + fi.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
        (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val) := fun h => hactZ ⟨by omega, h.2⟩
    obtain ⟨ht, ⟨hus, hz47, hsB, hsC, hsD⟩, ⟨hdest, hr64, -⟩, ⟨hw1, -, hwin⟩, hempty, hreset, hfiv, -, hmem, -⟩ := hctx
    -- set_thread_state
    have htf := hP.fits ct _ htcb
    have hta := hP.align ct _ htcb
    have hstv : (stA ct).val = ct.val + 3328 := by
      rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
    obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th hP s ct sched.TS_RESTART htcb hact)
    obtain ⟨s2', hs2', hF⟩ := spec_exists (set_thread_state_frame (L := L) s ct sched.TS_RESTART
      (by unfold P1.Aligned; rw [hstv]; omega) hact.1)
    rw [hs2] at hs2'; have := eq_of_ok_eq hs2'; subst this
    rw [hs2]; simp only [bind_ok]
    obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
    obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hSS (t := ct.bv) hkt .restart
    have hI1 := MdbInv.of_same hM hI hSS
    have hU1 := UtInv.of_same hM hU hSS
    have hcap1 : capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev) := by
      rw [hSS.capAt (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩)]; exact hcap
    have hempty1 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
        capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
      intro i h1 h2
      rw [hSS.capAt ⟨dest, i, Or.inl ⟨r, hdest, by omega⟩, rfl⟩]; exact hempty i h1 h2
    have hzero1 : ZeroRegion (L.mem s2) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      rw [hF w hw (by
        rw [hstv]; intro e
        have e4 : objSize ObjKind.tcb = 4096 := rfl
        rcases hfree ct _ htcb with h | h <;> omega) (by
        intro e; exact hactZ' (by rw [← e]; exact ⟨h1, h2⟩))]
      exact hzero w hw h1 h2
    have horig1 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
    have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by omega
    have hct0 : nt.val = 4 → us.val ≠ 0 := fun h e => hsB ⟨h, e⟩
    obtain ⟨s2', hs2', hk2⟩ := spec_exists (sts_ksb_ret (L := L) s ct sched.TS_RESTART)
    rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
    have hDW2 : L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
      nodeAt_ksb hk2 _ _
    have hDWm2 : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
      hF _ hDWal hDWne.1 hDWne.2
    obtain ⟨σ1', hst1', hk1', harch1'⟩ := setThreadState_arch σ ct.bv tcb hkt .restart
    rw [hst1] at hst1'
    have e1 : σ1 = σ1' := by have := congrArg (fun x => x.1) hst1'; simpa using this
    subst e1
    have hgpm1 : HasPm σ1 σ1.archState.x64GlobalPml4 := by
      rw [harch1']; obtain ⟨pt, hpt⟩ := hgpm; exact ⟨pt, by rw [hk1', Function.update_of_ne hgct]; exact hpt⟩
    have hfiv' : fiv = fi := by
      rw [hfiv]
      cases hrs : reset
      · rfl
      · rw [hrs] at hreset
        have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
        exact (UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl))
    subst hfiv'
    have hfull := retype_full_pml4 (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 horig1 hpp hidx hcap1 hpal hpfit
      hfi hhigh nt us _ ht hn8 hus hdest (by omega) off win hwin hw1 hmem hempty1 hfree hzero1 bitsApi (by rw [← htP]; exact hb) hgpm1
      (by rw [harch1']; exact hga) (by rw [harch1']; exact hgf) (by rw [harch1']; exact hgreg)
    rw [← htP] at hfull
    have hWA2 : (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 :=
      (retype_region p fiv sb.val (zOf nt.val us.val) win.val (capAt_untyped_inv hcap) (by omega) hpal hpfit hfi hw1 hmem).2.1
    have hRB0 : reset = true → (∃ p sb d, capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 d)) ∧
      untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), s2, ar) := by
      intro hrs
      have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by rw [hrs] at hreset; simpa using hreset.symm
      have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl)
      rw [hf0] at hcap1
      exact ⟨⟨_, _, _, hcap1⟩, reset_untyped_unused arI s2 ar _ hcap1⟩
    have hpost : ∀ res, (res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
          (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
            (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ1 = ({(.ok (), σ')}, False) ∧
          Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
          MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧ ZeroRegion (L.mem res.2.1)
            ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
            (p.val + 2 ^ sb.val) ∧
          (FinInv th (L.mem s2) σ1 G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s2 ∧
          WFrame (L := L) s2 res.2.1 (fun w => SlotSpan th w ∨ ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ≤ w.val ∧
            w.val < (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)) ∧
          ∃ A k w dslot cj, RetExp th th' (L.mem s2) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
            A = (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX th th' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC th dslot w) →
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) reset p.bv
            (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ1 =
          (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
            (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ1 →
        RetPost (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res := by
      rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w, dslot,
        cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩ he
      exact ⟨h1, h2, σ1, by rw [hcur]; exact hst1, σ', G', th', he.trans hrun, hP', hR', hV', hM', hC', hI', hU',
      MdbStep.same_left hM hSS hSt', fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)),
      by rw [hks, hk2], _, _, _, dslot, cj, hE.same_left hM hSS,
      ⟨⟨ct, s2, hct, hs2, Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s2, th, _, _, Or.inl ⟨rfl, rfl, rfl, rfl, hRB0⟩, le_rfl, le_rfl, hthx.2, fun a h => h, ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC,
        hWf.mono fun v hv => hv.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr ⟨htP, h⟩),
        fun ⟨_, hne⟩ => absurd htP hne, fun hT => absurd (htP.symm.trans hT) (by simp)⟩⟩, fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩
    rcases Bool.eq_false_or_eq_true reset with hrs | hrs <;> subst hrs
    · have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
      have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl)
      have hcap0 := hcap1; rw [hf0] at hcap0
      rw [retype_reset_unused (L := L) arI s2 ar _ _ nt us dest off win dev hcap0]
      have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 = ({(.untypedCap dev p.bv sb.val 0, σ1)}, False) := by
        obtain ⟨c, a, hc, hca, hg⟩ := hR1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
        rw [hcap0] at hc; have := eq_of_ok_eq hc; subst this
        rw [hg, hca.abs]; rfl
      exact WP.spec_mono hfull (fun res h => (hpost res h (invokeUntyped_reset_unused bitsApi _ _ _ _ us.val _ dev σ1 hg)).toN)
    · exact WP.spec_mono hfull (fun res h => (hpost res h rfl).toN)

  obtain ⟨hrs, hfi0⟩ := hcase
  have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by
    have := hctx.resetEq; rw [hrs] at this; simpa using this.symm
  obtain ⟨horigR, hcnR, hheadR⟩ := hRst hnc hfi0
  have hdev : dev = false := by
    cases hd : dev
    · rfl
    · exact absurd hn8 (dev_nt hctx.ty (hctx.device hd)).2.2
  subst hdev hrs
  have hfv : fiv = 0#u64 := by rw [hctx.fidx]; rfl
  subst hfv
  obtain ⟨ht, ⟨hus, hz47, hsB, hsC, hsD⟩, ⟨hdest, hr64, -⟩, ⟨hw1, -, hwin⟩, hempty, hreset, hfiv, -, hmem, -⟩ := hctx
  -- set_thread_state
  have htf := hP.fits ct _ htcb
  have hta := hP.align ct _ htcb
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th hP s ct sched.TS_RESTART htcb hact)
  obtain ⟨s2', hs2', hF⟩ := spec_exists (set_thread_state_frame (L := L) s ct sched.TS_RESTART
    (by unfold P1.Aligned; rw [hstv]; omega) hact.1)
  rw [hs2] at hs2'; have := eq_of_ok_eq hs2'; subst this
  rw [hs2]; simp only [bind_ok]
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hSS (t := ct.bv) hkt .restart
  have hI1 := MdbInv.of_same hM hI hSS
  have hU1 := UtInv.of_same hM hU hSS
  have hcap1 : capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) := by
    rw [hSS.capAt (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩)]; exact hcap
  have hempty1 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    rw [hSS.capAt ⟨dest, i, Or.inl ⟨r, hdest, by omega⟩, rfl⟩]; exact hempty i h1 h2
  have hzero1 : ZeroRegion (L.mem s2) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hF w hw (by
      rw [hstv]; intro e
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hfree ct _ htcb with h | h <;> omega) (by
      intro e; exact hactZ (by rw [← e]; exact ⟨by omega, h2⟩))]
    exact hzero w hw h1 h2
  have horig1 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by omega
  have hct0 : nt.val = 4 → us.val ≠ 0 := fun h e => hsB ⟨h, e⟩
  obtain ⟨s2', hs2', hk2⟩ := spec_exists (sts_ksb_ret (L := L) s ct sched.TS_RESTART)
  rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
  have hDW2 : L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    nodeAt_ksb hk2 _ _
  have hDWm2 : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hF _ hDWal hDWne.1 hDWne.2
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hnd := nodesc_of_cdt hP hC1 hAs (by rw [hcdt1]; exact hnc)
  have horig2 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl := by
    rw [hio1]; exact horigR
  have hdout := hcnR dest r hdest
  have hPP2 : PPHyp (L := L) arI th p sb (fun t => L.ksb t = L.ksb s2 ∧
      L.mem t (L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS) = L.mem s2 (L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS)) := by
    rw [hDW2]; exact hPP _ _
  have hsbW : sb.val < 64 := capAt_untyped_inv hcap
  have hWR := retype_region p 0#u64 sb.val (zOf nt.val us.val) win.val hsbW (by omega) hpal hpfit (by simp) hw1 hmem
  have hWA2 : (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 := hWR.2.1
  have hWLO : p.val ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat := by have := hWR.1; rwa [show (0#u64 : U64).val = 0 from rfl, Nat.add_zero] at this
  have hWHI : (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val := hWR.2.2.1
  have hp8W : p.val % 8 = 0 := by
    have h8 : 8 ∣ 2 ^ sb.val := by
      have := Nat.pow_dvd_pow 2 (show 3 ≤ sb.val by omega); simpa using this
    have := Nat.mod_mod_of_dvd p.val h8; rw [hpal, Nat.zero_mod] at this; exact this.symm
  have hpost : ∀ res : core.result.Result Unit error.Exc × S × A', (NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
          (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) false)).run σ1 (fun _ => True) ∧
      ((res.1 = .Err .Preempted ∧ ∃ σ' f,
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) false)).run σ1 (TopP (.error ()) σ') ∧
          ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb false
            (L.mem res.2.1) σ' f ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G ∧
          (FinInv th (L.mem s2) σ1 G → FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G) ∧
          L.ksb res.2.1 = L.ksb s2 ∧ untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok res ∧
          ∀ dslot cj, RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s2)
            (L.mem res.2.1) G G p.val 1 0 dslot cj (cslotAddr (pp.bv, idx))) ∨
       (res.1 = .Ok () ∧ ∃ σ' G' th'',
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) false)).run σ1 (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧
          (FinInv th (L.mem s2) σ1 G → FinInv th'' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s2 ∧
          (∃ t1 a1, untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), t1, a1) ∧
            WFrame (L := L) t1 res.2.1 (fun w => SlotSpan (restrictTh th p.val (p.val + 2 ^ sb.val)) w ∨
              ((Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ≤ w.val ∧
                w.val < (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val))) ∧
          ∃ A k w dslot cj, RetExp th th'' (L.mem s2) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
            A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us false A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w))) →
      RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi (L.ksb s) (.retype (pp.bv, idx) true p.bv
        (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
        false) res := by
    rintro res ⟨hNS, ⟨h1, σ', f, hhas, hRR, hSt, hFr, hks, hrs, hE⟩ | ⟨h1, σ', G', th'', hhas, hP'', hR'', hV'', hM'', hC'',
        hI'', ⟨hU'', hSt⟩, hFin, hks, ⟨t1, a1, hr, hWf⟩, A, k, w, dslot, cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩⟩
    · exact ⟨σ1, by rw [hcur]; exact hst1, hNS, .error (), σ', G, _, Or.inr ⟨h1, rfl⟩, hhas, hP.restrict,
        hRR.R, hRR.V, hRR.M, hRR.C, hRR.I, hRR.U, MdbStep.same_left hM hSS hSt,
        fun hFI => hFr (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)), by rw [hks, hk2],
        p.val, 1, 0, fun _ => 0#u64, fun _ => .Null, (hE _ _).same_left hM hSS, ⟨⟨ct, s2, hct, hs2, Or.inl ⟨h1, hrs⟩⟩, fun e => by rw [h1] at e; cases e⟩⟩
    · exact ⟨σ1, by rw [hcur]; exact hst1, hNS, .ok (), σ', G', th'', Or.inl ⟨h1, rfl⟩, hhas, hP'', hR'', hV'', hM'',
        hC'', hI'', hU'', MdbStep.same_left hM hSS hSt,
        fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)), by rw [hks, hk2],
        _, _, _, dslot, cj, hE.same_left hM hSS, ⟨⟨ct, s2, hct, hs2, Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, t1, (restrictTh th p.val (p.val + 2 ^ sb.val)), _, _, Or.inr ⟨a1, p, sb, _, _, hr, hcap1, hcap, hp8W, hsb4,
          (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩, hnd, rfl, rfl, rfl, rfl⟩, hWLO, hWHI,
          by simpa using RegionFree.restrict hN,
          fun a h => h.of_restrict, ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, (fun j hj => let ⟨q, r, hq, i, hi, e⟩ := hdsC j hj; ⟨q, r, (restrictTh_some hq).1, i, hi, e⟩), hWf.mono fun v hv => hv.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr ⟨htP, h⟩),
          fun ⟨_, hne⟩ => absurd htP hne, fun hT => absurd (htP.symm.trans hT) (by simp)⟩⟩, fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩
  obtain ⟨σ1', hst1', hk1', harch1'⟩ := setThreadState_arch σ ct.bv tcb hkt .restart
  rw [hst1] at hst1'
  have e1 : σ1 = σ1' := by have := congrArg (fun x => x.1) hst1'; simpa using this
  subst e1
  have hgpm1 : HasPm σ1 σ1.archState.x64GlobalPml4 := by
    rw [harch1']; obtain ⟨pt, hpt⟩ := hgpm; exact ⟨pt, by rw [hk1', Function.update_of_ne hgct]; exact hpt⟩
  refine WP.spec_mono (retype_reset_pml4 (L := L) (arI := arI) ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 hpp hidx hcap1 hfi0 hnd
    hpal hsb4 hhigh hN (hns hnc) hzero1 hrcb hppS hPP2
    (ekept_dw hP hAs.isSlot (L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS) (by rw [hDW2]; exact hDWal) (by rw [hDW2]; exact hDWreg)
      (by rw [hDW2]; exact hDWobj _ hAs.isSlot) hpfit _ _) ⟨rfl, rfl⟩ (fun _ h => h.1) horig2
    nt us _ ht hn8 hus hgpm1 (by rw [harch1']; exact hga) (by rw [harch1']; exact hgf)
    (by rw [harch1']; exact hgreg) hdest hdout (by omega) off win hwin hw1 hmem hempty1 bitsApi hb) hpost

/-- **FL4's untyped `Retype` refines FL4's spec, for every object type,
resets included**
(`fl4DecodeUntypedInvocation`, `set_thread_state Restart`,
`fl4InvokeUntyped`; `Z = Unit`), for every type (0..13: the non-arch types,
frames, page tables and PML4s, these with the spec's global PML4 a PML4
object, aligned, outside the untyped region): `decode` ends with
the error the spec's decode throws, or the spec decodes an invocation and
`RetPostN` holds (no failure; an outcome of FL4's kind, done or preempted in
the reset, related to FL4's result).

Beyond the hypotheses of `untyped_retype_refines_fl4` (with `hunused`
dropped, and the scheduler-action and debug-list words outside the whole
region): for the reset of a used region (`hRst`, when the cap has no
children and `fi ≠ 0`) the spec's original
slots, the CNodes of the typed heap and the debug-list head TCB are outside
the region (l4v: nothing reachable is there); no linked slot is in it and no
object straddles it; the region is at least 16 bytes; the chunk size is FL4's;
and the preemption points are opaque (`hppS`, `hPP`). -/
theorem untyped_retype_refines_fl4P [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (th : TypedHeap) (s : S) (ar : A')
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hnt : ∀ x, args.head? = some x → x.val ≤ 13)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val)) :
    untyped.decode st arI s ar lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocation slbl (args.map UScalar.bv) (pp.bv, idx)
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPostN (L := L) th (L.mem s) G σ arI ar s Fl4Spec.fl4ObjBitsApi (L.ksb s)) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refines_fl4 arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen hargs
    (fun x hx => Or.inl (by have := hnt x hx; omega))
    _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  have hn := hnt nt hnt0
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hctx.ty us.val).2.1
  by_cases h8 : nt.val = 8
  · exact retype_cont_pml4N arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx hcap hpal hpfit hfi
      hhigh hactZ hfree hzero hsb4 hN hns hrcb hppS hPP hRst Fl4Spec.fl4ObjBitsApi nt us dest off win t r reset fiv h8 hb
      hDWal hDWobj hDWreg hDWne hhead hgpm hga hgf hgreg hctx
  · exact retype_cont_allN arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx hcap hpal hpfit hfi
      hhigh hactZ hfree hzero hsb4 hN hns hrcb hppS hPP hRst Fl4Spec.fl4ObjBitsApi nt us dest off win t r reset fiv
      ⟨hn, h8⟩ hb hDWal hDWobj hDWreg hDWne hhead hctx


end

end Fl4Proofs.P3
