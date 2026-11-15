/-
P3 (DESIGN.md §9), untyped: pieces of the success path of `Retype`
(`untyped::retype`, `objects::create_new_objects`) against l4v
`invoke_untyped` (Fl4Spec/Retype.lean), for the non-arch object types but
the TCB:

* `create_object` makes no memory write and returns the cap `newCapOf`,
  which is related to the spec's `default_cap` (`newCap_rel`);
* the untyped cap's new free index (`retype_free_index`): FL4's
  `free_ref - ptr` is the spec's `unat (free_ref - base)`, so the updated
  untyped caps are related;
* the space accounting (`retype_region`): with the untyped's base aligned to
  its size and the window that `decode` accepted, the new objects lie
  between the old free index and the end of the region, aligned to their
  size, and the new free index does not pass the end;
* the ghost typed heap grows by the new CNodes (`extendTh`), and stays
  `Placed` when the region held no objects before (`Placed.extend`).
-/
import Fl4Proofs.P3.UntypedDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## New caps -/

/-- The cap `create_object` returns for the non-arch types (FL4 type
numbers 0..6). -/
def newCapOf (n : Nat) (base us : U64) (dev : Bool) : capability.Cap :=
  if n = 2 then .Endpoint base 0#u64 true true true true
  else if n = 3 then .Notification base 0#u64 true true
  else if n = 4 then .CNode base us 0#u64 0#u64
  else if n = 0 then .Untyped base us 0#u64 dev
  else if n = 5 then .SchedContext base us
  else if n = 1 then .Thread base
  else if n = 7 then .Pdpt base false 0#u64 0#u64
  else if n = 8 then .Pml4 base false 0#u64
  else if n = 9 then .Frame base .Huge 3#u64 dev false false 0#u64 0#u64
  else if n = 10 then .Frame base .Small 3#u64 dev false false 0#u64 0#u64
  else if n = 11 then .Frame base .Large 3#u64 dev false false 0#u64 0#u64
  else if n = 12 then .PageTable base false 0#u64 0#u64
  else if n = 13 then .PageDirectory base false 0#u64 0#u64
  else .Reply base true

theorem ite_prop' {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {a b : α} (ha : c → P a) (hb : ¬ c → P b) :
    P (ite c a b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- The cases of `newCapOf`. -/
theorem newCapOf_ind (P : capability.Cap → Prop) (n : Nat) (base us : U64) (dev : Bool)
    (h2 : n = 2 → P (.Endpoint base 0#u64 true true true true)) (h3 : n = 3 → P (.Notification base 0#u64 true true))
    (h4 : n = 4 → P (.CNode base us 0#u64 0#u64)) (h0 : n = 0 → P (.Untyped base us 0#u64 dev))
    (h5 : n = 5 → P (.SchedContext base us)) (h1 : n = 1 → P (.Thread base))
    (h7 : n = 7 → P (.Pdpt base false 0#u64 0#u64)) (h8 : n = 8 → P (.Pml4 base false 0#u64))
    (h9 : n = 9 → P (.Frame base .Huge 3#u64 dev false false 0#u64 0#u64))
    (h10 : n = 10 → P (.Frame base .Small 3#u64 dev false false 0#u64 0#u64))
    (h11 : n = 11 → P (.Frame base .Large 3#u64 dev false false 0#u64 0#u64))
    (h12 : n = 12 → P (.PageTable base false 0#u64 0#u64)) (h13 : n = 13 → P (.PageDirectory base false 0#u64 0#u64))
    (h6 : P (.Reply base true)) : P (newCapOf n base us dev) := by
  unfold newCapOf
  exact ite_prop' h2 fun _ => ite_prop' h3 fun _ => ite_prop' h4 fun _ => ite_prop' h0 fun _ => ite_prop' h5 fun _ =>
    ite_prop' h1 fun _ => ite_prop' h7 fun _ => ite_prop' h8 fun _ => ite_prop' h9 fun _ => ite_prop' h10 fun _ =>
    ite_prop' h11 fun _ => ite_prop' h12 fun _ => ite_prop' h13 fun _ => h6

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`create_object` for types 0, 2..7 and 9..13** (all but TCBs and
PML4s) writes nothing and returns `newCapOf`. -/
theorem create_object_eq {A : Type} (arI : machine.Arch A) (s : S) (ar : A) (nt base us : U64) (dev : Bool)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) :
    objects.create_object st arI s ar nt base us dev = ok (newCapOf nt.val base us dev, s, ar) := by
  have h14 : nt ≠ 14#u64 := by rcases hn with h | ⟨h, h', h''⟩ <;> scalar_tac
  have h15 : ¬ nt ≥ 15#u64 := by rcases hn with h | ⟨h, h', h''⟩ <;> scalar_tac
  unfold objects.create_object newCapOf
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.X86EptPml4, h14, h15, ↓reduceIte]
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint, fl4_abi.consts.object.Notification,
    fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped, fl4_abi.consts.object.SchedContext,
    fl4_abi.consts.object.Reply, fl4_abi.consts.object.X86Pdpt, fl4_abi.consts.object.X64Pml4,
    fl4_abi.consts.object.X64HugePage, fl4_abi.consts.object.X86Page4K, fl4_abi.consts.object.X86LargePage,
    fl4_abi.consts.object.X86PageTable, fl4_abi.consts.object.X86PageDirectory, capability.VM_READ_WRITE,
    u64_eq_iff]
  have e : ∀ n : Nat, n < 2 ^ 64 → ((⟨BitVec.ofNat 64 n⟩ : U64)).val = n := fun n h => by
    show (BitVec.ofNat 64 n).toNat = n; simp; omega
  generalize hv : nt.val = n at *
  rcases hn with rfl | ⟨h1, h2, h3⟩
  · simp
  · interval_cases n <;> simp_all

end

theorem rightsOf_univ : rightsOf true true true true = Set.univ := by
  ext x; cases x <;> simp [rightsOf]

theorem rightsOf_rw : rightsOf true true false false = {.allowRead, .allowWrite} := by
  ext x; cases x <;> simp [rightsOf]

/-- **The new caps are the spec's default caps** (`default_cap`), and
well-formed, given the size checks `decode` made. -/
theorem newCap_rel {n : Nat} {t : Fl4Spec.ApiObjectType} (ht : objTypeOf n = some t)
    (hn : n ≤ 13) (base us : U64) (dev : Bool) (hus : us.val < 64)
    (hsc : n = 5 → 7 ≤ us.val) :
    CapRel (newCapOf n base us dev) (Fl4Spec.defaultCap t base.bv us.val dev) := by
  unfold objTypeOf Fl4Spec.archDataToObjType at ht
  interval_cases n <;> simp at ht <;> subst ht
  · exact ⟨trivial, rfl⟩
  · exact ⟨trivial, rfl⟩
  · exact ⟨trivial, by simp [newCapOf, absCap, Fl4Spec.defaultCap]; exact rightsOf_univ⟩
  · exact ⟨trivial, by simp [newCapOf, absCap, Fl4Spec.defaultCap]; exact rightsOf_rw⟩
  · refine ⟨⟨hus, by decide, by decide⟩, ?_⟩
    simp [newCapOf, absCap, Fl4Spec.defaultCap]
  · exact ⟨hsc rfl, by simp [newCapOf, absCap, Fl4Spec.defaultCap]⟩
  · exact ⟨trivial, by simp [newCapOf, absCap, Fl4Spec.defaultCap, replyRights]⟩
  all_goals first
    | exact ⟨trivial, by simp [newCapOf, absCap, Fl4Spec.defaultCap, Fl4Spec.archDefaultCap]⟩
    | exact ⟨by simp [newCapOf, CapWf], by simp [newCapOf, absCap, Fl4Spec.defaultCap, Fl4Spec.archDefaultCap,
        vmRightsOf, frameSizeOf]⟩

theorem ite_ne_of {α : Type} {c : Prop} [Decidable c] {a b x : α} (ha : a ≠ x) (hb : b ≠ x) : ite c a b ≠ x := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

theorem newCap_ne_null (n : Nat) (base us : U64) (dev : Bool) : newCapOf n base us dev ≠ .Null := by
  apply newCapOf_ind (fun c => c ≠ .Null) <;> intros <;> exact fun h => capability.Cap.noConfusion h

/-! ## The untyped cap's free index -/

/-- `object_size` is `zOf` for the type numbers below 14. -/
theorem object_size_eq (nt us : U64) (hn : nt.val < 14) (hus : us.val < 64) :
    objects.object_size nt us = ok (some ⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩) := by
  have h14 : nt ≠ 14#u64 := by scalar_tac
  have h15 : ¬ nt ≥ 15#u64 := by scalar_tac
  unfold objects.object_size
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.X86EptPml4, h14, h15, ↓reduceIte]
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint,
    fl4_abi.consts.object.Notification, fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped,
    fl4_abi.consts.object.SchedContext, fl4_abi.consts.object.Reply, fl4_abi.consts.object.X86Page4K,
    fl4_abi.consts.object.X86LargePage, fl4_abi.consts.object.X64HugePage, fl4_abi.consts.object.X86PageTable,
    fl4_abi.consts.object.X86PageDirectory, fl4_abi.consts.object.X86Pdpt, fl4_abi.consts.object.X64Pml4,
    fl4_abi.consts.bits.TCB, fl4_abi.consts.bits.ENDPOINT, fl4_abi.consts.bits.NOTIFICATION,
    fl4_abi.consts.bits.SLOT, fl4_abi.consts.bits.REPLY, lift, bind_ok, u64_eq_iff]
  have e : ∀ x : U64, x = ⟨BitVec.ofNat 64 x.val⟩ := fun x => UScalar.eq_of_val_eq (by
    show x.val = (BitVec.ofNat 64 x.val).toNat; simp)
  generalize hv : nt.val = n at *
  interval_cases n <;> simp [zOf] <;> first | rfl | (exact e us) | skip

/-- **The free index after a retype**: FL4 stores `free_ref - ptr` (a byte
offset, as l4v's `get_free_index`), which is the spec's
`unat (free_ref - base)`, so the updated untyped caps are related. -/
theorem retype_free_index (aligned ptr win total sb : U64) (dev : Bool) (z : Nat)
    (htot : total.bv = win.bv <<< z) :
    CapRel (.Untyped ptr sb (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) ptr) dev)
      (.untypedCap dev ptr.bv sb.val
        (Fl4Spec.unat ((aligned.bv + (BitVec.ofNat 64 win.val <<< z)) - ptr.bv))) := by
  refine ⟨trivial, ?_⟩
  simp only [absCap]
  congr 1
  show (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) ptr).bv.toNat = _
  rw [core.num.U64.wrapping_sub_bv_eq, core.num.U64.wrapping_add_bv_eq, htot, ← bv_eq_ofNat]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`retype` without a reset**, in closed form: the untyped cap at `slot`
gets the free index `base + (win << z) - ptr`, then `create_new_objects`. -/
theorem retype_noreset_eq {A : Type} (arI : machine.Arch A) (s : S) (ar : A) (slot base nt us dest off win : U64)
    (dev : Bool) (hn : nt.val < 14) (hus : us.val < 64) (hz : zOf nt.val us.val < 64)
    (p sb fi : U64) (dev' : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev')) :
    ∃ total : U64, total.bv = win.bv <<< zOf nt.val us.val ∧
      untyped.retype st arI s ar slot false base nt us dest off win dev = (do
        let s1 ← obj.Slot.set_cap st slot s
          (.Untyped p sb (core.num.U64.wrapping_sub (core.num.U64.wrapping_add base total) p) dev')
        let (s2, a2) ← objects.create_new_objects st arI s1 ar nt slot dest off win base us dev
        ok (.Ok (), s2, a2)) := by
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  obtain ⟨total, htot, htb⟩ : ∃ total, (win <<< ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64)) =
      ok total ∧ total.bv = win.bv <<< zOf nt.val us.val := by
    have := spec_exists (UScalar.ShiftLeft_spec win ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
    obtain ⟨v, hv, -, hb⟩ := this
    exact ⟨v, hv, by rw [hb, h63]⟩
  refine ⟨total, htb, ?_⟩
  unfold untyped.retype
  simp only [Bool.false_eq_true, ↓reduceIte, object_size_eq nt us hn hus, lift, bind_ok,
    core.option.Option.unwrap_or, htot, slot_cap_eq, hcap]

/-- **The untyped cap update of a retype refines the spec's** `set_cap
(UntypedCap dev base bits (unat (free_ref - base)))` at the source slot (a
CNode slot), with the state relation kept and the CDT unchanged. -/
theorem retype_set_untyped_rel (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    {pp : U64} {r : Nat} (hpp : th pp = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p sb fi : U64} {dev : Bool} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (base total win : U64) (z : Nat) (htot : total.bv = win.bv <<< z) :
    obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s
      (.Untyped p sb (core.num.U64.wrapping_sub (core.num.U64.wrapping_add base total) p) dev) ⦃ s' =>
      ∃ σ', Fl4Spec.setCap (Z := Unit)
          (.untypedCap dev p.bv sb.val (Fl4Spec.unat ((base.bv + (BitVec.ofNat 64 win.val <<< z)) - p.bv)))
          (pp.bv, idx) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧
        σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap ⦄ := by
  have he : EncWf (.Untyped p sb fi dev) := by rw [capAt_words] at hcap; exact decode_encWf hcap
  refine WP.spec_mono (set_cap_refines th s σ hR hV hP hpp hidx _ _
    (retype_free_index base p win total sb dev z htot) trivial ⟨he.1, he.2⟩) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, -, -⟩
  exact ⟨σ', h1, h2, h3, h4, h5⟩

end

/-! ## Space accounting -/

/-- `align_up` on numbers (no wrap-around). -/
theorem alignUp_toNat (x : BitVec 64) (z : Nat) (hz : z < 64) (hx : x.toNat + 2 ^ z ≤ 2 ^ 64) :
    (Fl4Spec.alignUp x z).toNat = (x.toNat + 2 ^ z - 1) / 2 ^ z * 2 ^ z := by
  have hpz : 2 ^ z < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hz
  have hp1 : 1 ≤ 2 ^ z := Nat.one_le_two_pow
  unfold Fl4Spec.alignUp
  have hm : ~~~(BitVec.ofNat 64 (2 ^ z) - 1) = BitVec.allOnes 64 <<< z := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
      BitVec.toNat_allOnes]
    rw [Nat.mod_eq_of_lt hpz, Nat.shiftLeft_eq]
    have h1 : (2 ^ 64 - 1 + 2 ^ z) % 2 ^ 64 = 2 ^ z - 1 := by omega
    have h2 : (2 ^ 64 - 1) * 2 ^ z = 2 ^ 64 * (2 ^ z - 1) + (2 ^ 64 - 2 ^ z) := by omega
    have e1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    rw [e1, h1, h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hm, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hpz]
  have hy : (2 ^ 64 - (1 : BitVec 64).toNat + (x.toNat + 2 ^ z) % 2 ^ 64) % 2 ^ 64 = x.toNat + 2 ^ z - 1 := by
    simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    rcases Nat.lt_or_ge (x.toNat + 2 ^ z) (2 ^ 64) with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have : x.toNat + 2 ^ z = 2 ^ 64 := by omega
      rw [this, Nat.mod_self]; omega
  rw [hy, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))]

/-- The space accounting on numbers: `A` the aligned start, `k = 2^z` the
object size, `M = 2^sb` the region size. -/
theorem region_nat (P F M k win : Nat) (sb z : Nat) (hM : M = 2 ^ sb) (hk : k = 2 ^ z)
    (hP : P % M = 0) (hF : F ≤ M) (hw1 : 1 ≤ win) (hw : win ≤ (M - F) / k) :
    P + F ≤ (P + F + k - 1) / k * k ∧ (P + F + k - 1) / k * k % k = 0 ∧
      (P + F + k - 1) / k * k + win * k ≤ P + M := by
  have hkpos : 0 < k := by rw [hk]; exact Nat.two_pow_pos z
  have hwk : win * k ≤ M - F := by
    calc win * k ≤ (M - F) / k * k := Nat.mul_le_mul_right _ hw
      _ ≤ M - F := Nat.div_mul_le_self _ _
  have hkle : k ≤ M := by
    have : 1 * k ≤ win * k := Nat.mul_le_mul_right _ hw1
    omega
  have hzs : z ≤ sb := by
    by_contra h
    have : 2 ^ sb < 2 ^ z := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hkM : k ∣ M := by rw [hk, hM]; exact Nat.pow_dvd_pow 2 hzs
  have hkP : k ∣ P := Nat.dvd_trans hkM (Nat.dvd_of_mod_eq_zero hP)
  obtain ⟨m, rfl⟩ := hkM
  obtain ⟨q, rfl⟩ := hkP
  have hA : (k * q + F + k - 1) / k * k = k * q + (F + k - 1) / k * k := by
    rw [show k * q + F + k - 1 = (F + k - 1) + k * q by omega, Nat.add_mul_div_left _ _ hkpos, Nat.add_mul,
      Nat.mul_comm q k]
    omega
  rw [hA]
  have hd := Nat.div_add_mod (F + k - 1) k
  have hr := Nat.mod_lt (F + k - 1) hkpos
  generalize hc : (F + k - 1) / k = c at hd ⊢
  generalize (F + k - 1) % k = r at hd hr
  have hck : k * c = c * k := Nat.mul_comm _ _
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, Nat.mul_mod_right]
  · have hkm : k * m = m * k := Nat.mul_comm _ _
    have h1 : c * k + win * k < (m + 1) * k := by rw [Nat.add_mul]; omega
    rw [← Nat.add_mul] at h1
    have h2 : c + win < m + 1 := Nat.lt_of_mul_lt_mul_right h1
    have h3 : (c + win) * k ≤ m * k := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at h3
    omega

/-- **The space accounting of a retype.** For an untyped cap at `p` of
size `2^sb` (aligned to its size, not wrapping) with free index `fiv`
(at most the size), and a window of `win ≥ 1` objects of size `2^z` that
`decode` accepted (`RetCtx.memory`): the objects start at the aligned
free reference `A`, past the old free index, aligned to their size, and end
inside the region; the new free index `unat (A + win·2^z - p)` is at most
the size and at least the old one. -/
theorem retype_region (p fiv : U64) (sb z win : Nat) (hsb : sb < 64) (hz : z < 64)
    (hP : p.val % 2 ^ sb = 0) (hPM : p.val + 2 ^ sb ≤ 2 ^ 64) (hF : fiv.val ≤ 2 ^ sb) (hw1 : 1 ≤ win)
    (hw : win ≤ ((1#64 <<< sb : BitVec 64) - fiv.bv).toNat >>> z) :
    p.val + fiv.val ≤ (Fl4Spec.alignUp (p.bv + fiv.bv) z).toNat ∧
    (Fl4Spec.alignUp (p.bv + fiv.bv) z).toNat % 2 ^ z = 0 ∧
    (Fl4Spec.alignUp (p.bv + fiv.bv) z).toNat + win * 2 ^ z ≤ p.val + 2 ^ sb ∧
    Fl4Spec.unat ((Fl4Spec.alignUp (p.bv + fiv.bv) z + (BitVec.ofNat 64 win <<< z)) - p.bv) =
      (Fl4Spec.alignUp (p.bv + fiv.bv) z).toNat + win * 2 ^ z - p.val := by
  have hM : 2 ^ sb < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
  have hk1 : 1 ≤ 2 ^ z := Nat.one_le_two_pow
  have hfb : ((1#64 <<< sb : BitVec 64) - fiv.bv).toNat = 2 ^ sb - fiv.val := by
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fiv.bv.toNat = fiv.val from rfl]
    rw [show (1 % 2 ^ 64 * 2 ^ sb) % 2 ^ 64 = 2 ^ sb by
      rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM]]
    omega
  rw [hfb, Nat.shiftRight_eq_div_pow] at hw
  obtain ⟨h1, h2, h3⟩ := region_nat p.val fiv.val (2 ^ sb) (2 ^ z) win sb z rfl rfl hP hF hw1 hw
  have hwk : win * 2 ^ z ≤ 2 ^ sb - fiv.val :=
    le_trans (Nat.mul_le_mul_right _ hw) (Nat.div_mul_le_self _ _)
  have hk : 1 * 2 ^ z ≤ win * 2 ^ z := Nat.mul_le_mul_right _ hw1
  have hx : (p.bv + fiv.bv).toNat = p.val + fiv.val := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by show p.val + fiv.val < 2 ^ 64; omega)
  have hA := alignUp_toNat (p.bv + fiv.bv) z hz (by rw [hx]; omega)
  rw [hx] at hA
  rw [hA]
  refine ⟨h1, h2, h3, ?_⟩
  generalize (p.val + fiv.val + 2 ^ z - 1) / 2 ^ z * 2 ^ z = A at h1 h2 h3 hA
  have hW : (BitVec.ofNat 64 win <<< z).toNat = win * 2 ^ z := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hwin : win < 2 ^ 64 := by
      have : win ≤ win * 2 ^ z := Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [Nat.mod_eq_of_lt hwin, Nat.mod_eq_of_lt (by omega)]
  simp only [Fl4Spec.unat, BitVec.toNat_sub, BitVec.toNat_add, hA, hW, show p.bv.toNat = p.val from rfl]
  rcases Nat.lt_or_ge (A + win * 2 ^ z) (2 ^ 64) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : A + win * 2 ^ z = 2 ^ 64 := by omega
    rw [this, Nat.mod_self]; omega

/-! ## The ghost typed heap grows -/

/-- The typed heap after creating `n` objects of kind `kd`, `k` bytes
apart, from address `A` (`retype_region`'s `ptrs`). -/
def extendTh (th : TypedHeap) (A k n : Nat) (kd : ObjKind) : TypedHeap := fun q =>
  if ∃ i, i < n ∧ q.val = A + i * k then some kd else th q

/-- Hypothesis on the concrete state: no object of the typed heap meets the
bytes `lo .. hi` (the untyped region past its free index; l4v gets this from
`valid_untyped` and `caps_no_overlap`). -/
def RegionFree (th : TypedHeap) (lo hi : Nat) : Prop :=
  ∀ q kd, th q = some kd → q.val + objSize kd ≤ lo ∨ hi ≤ q.val

theorem extendTh_old {th : TypedHeap} {A k n : Nat} {kd : ObjKind} {q : U64}
    (h : ¬ ∃ i, i < n ∧ q.val = A + i * k) : extendTh th A k n kd q = th q := by
  simp only [extendTh, if_neg h]

theorem extendTh_new {th : TypedHeap} {A k n : Nat} {kd : ObjKind} {q : U64}
    (h : ∃ i, i < n ∧ q.val = A + i * k) : extendTh th A k n kd q = some kd := by
  simp only [extendTh, if_pos h]

/-- **`Placed` is kept** when the new objects lie in a free region of the
kernel half, are 32-byte aligned and do not overlap (each `k ≥ objSize kd`
bytes from the next). -/
theorem Placed.extend {th : TypedHeap} (hP : Placed th) {A k n lo hi : Nat} {kd : ObjKind}
    (hfree : RegionFree th lo hi) (hlo : lo ≤ A) (hhi : A + n * k ≤ hi) (hhi64 : hi ≤ 2 ^ 64)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ lo) (hA : A % 32 = 0) (hk : k % 32 = 0) (hsz : objSize kd ≤ k) :
    Placed (extendTh th A k n kd) := by
  have newv : ∀ q : U64, (∃ i, i < n ∧ q.val = A + i * k) → ∃ i, i < n ∧ q.val = A + i * k ∧
      q.val + objSize kd ≤ A + (i + 1) * k ∧ A + (i + 1) * k ≤ hi := by
    rintro q ⟨i, hi', he⟩
    refine ⟨i, hi', he, ?_, ?_⟩
    · rw [he, Nat.add_mul, Nat.one_mul]; omega
    · have : (i + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hi'
      omega
  constructor
  · intro q kq hq
    by_cases h : ∃ i, i < n ∧ q.val = A + i * k
    · obtain ⟨i, -, he⟩ := h
      rw [he, Nat.add_mod, hA, Nat.mul_mod, hk]; simp
    · rw [extendTh_old h] at hq; exact hP.align q kq hq
  · intro q kq hq
    by_cases h : ∃ i, i < n ∧ q.val = A + i * k
    · rw [extendTh_new h] at hq; cases hq
      obtain ⟨i, -, -, h1, h2⟩ := newv q h; omega
    · rw [extendTh_old h] at hq; exact hP.fits q kq hq
  · intro q r kq kr hq hr hne
    by_cases h1 : ∃ i, i < n ∧ q.val = A + i * k <;> by_cases h2 : ∃ i, i < n ∧ r.val = A + i * k
    · rw [extendTh_new h1] at hq; rw [extendTh_new h2] at hr; cases hq; cases hr
      obtain ⟨i, -, hi1, hi2, -⟩ := newv q h1
      obtain ⟨j, -, hj1, hj2, -⟩ := newv r h2
      have hij : i ≠ j := by
        rintro rfl; exact hne (UScalar.eq_of_val_eq (by rw [hi1, hj1]))
      rcases Nat.lt_or_gt_of_ne hij with hl | hl
      · left
        have : (i + 1) * k ≤ j * k := Nat.mul_le_mul_right _ hl
        omega
      · right
        have : (j + 1) * k ≤ i * k := Nat.mul_le_mul_right _ hl
        omega
    · rw [extendTh_new h1] at hq; rw [extendTh_old h2] at hr; cases hq
      obtain ⟨i, -, hi1, hi2, hi3⟩ := newv q h1
      have hi0 : A + i * k ≥ A := Nat.le_add_right _ _
      rcases hfree r kr hr with h | h
      · right; omega
      · left; omega
    · rw [extendTh_old h1] at hq; rw [extendTh_new h2] at hr; cases hr
      obtain ⟨j, -, hj1, hj2, hj3⟩ := newv r h2
      have hj0 : A + j * k ≥ A := Nat.le_add_right _ _
      rcases hfree q kq hq with h | h
      · left; omega
      · right; omega
    · rw [extendTh_old h1] at hq; rw [extendTh_old h2] at hr; exact hP.disj q r kq kr hq hr hne
  · intro q kq hq
    by_cases h : ∃ i, i < n ∧ q.val = A + i * k
    · obtain ⟨i, -, he⟩ := h
      have : A + i * k ≥ A := Nat.le_add_right _ _
      omega
    · rw [extendTh_old h] at hq; exact hP.high q kq hq

end
end Fl4Proofs.P3
