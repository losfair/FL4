/-
P3 (DESIGN.md §9), untyped: helper facts for `untyped::decode` against l4v
`decode_untyped_invocation` (Fl4Spec/Decode.lean).

* the object type numbers (`fl4_abi::consts::object`, 0..18) as the spec's
  `data_to_obj_type` numbering (`objTypeOf`), and the object size FL4's
  `object_size` gives (`zOf`), which is `obj_bits_api` for every type but
  the TCB (FL4 TCBs are 4 KiB, `bits::TCB = 12`; the spec's X64 `tcb_bits`
  is 11);
* the spec's pieces with one, state-preserving outcome: `data_to_obj_type`,
  `mapME_x ensure_empty`, `const_on_failure False (ensure_no_children ..)`;
* `nat_to_cref` slots as FL4 slot addresses;
* FL4's `retype_size`, `ensure_empty_slots`, `align_up`, `retype_dest` in
  closed form.
-/
import Fl4Proofs.P3.CnodeOther
import Fl4Spec.Ext.TcbSize
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open Fl4Spec Classical
noncomputable section
def objTypeOf (n : Nat) : Option ApiObjectType :=
  if n = 0 then some .untyped else if n = 1 then some .tcbObject
  else if n = 2 then some .endpointObject else if n = 3 then some .notificationObject
  else if n = 4 then some .capTableObject else if n = 5 then some .schedContextObject
  else if n = 6 then some .replyObject
  else (archDataToObjType (n - 7)).map .archObject

def zOf (n us : Nat) : Nat :=
  if n = 0 ∨ n = 5 then us else if n = 1 then 12 else
        if n = 2 then 4 else if n = 3 then 6 else if n = 4 then 5 + us else
        if n = 6 then 5 else if n = 9 then 30 else if n = 10 then 12 else
        if n = 11 then 21 else if n = 14 then 15 else 12

theorem objTypeOf_none (n : Nat) : objTypeOf n = none ↔ 19 ≤ n := by
  unfold objTypeOf archDataToObjType
  constructor
  · intro h; by_contra hn; interval_cases n <;> simp at h
  · intro h; simp only [show ¬ n = 0 by omega, show ¬ n = 1 by omega, show ¬ n = 2 by omega, show ¬ n = 3 by omega,
      show ¬ n = 4 by omega, show ¬ n = 5 by omega, show ¬ n = 6 by omega, show ¬ n - 7 = 0 by omega,
      show ¬ n - 7 = 1 by omega, show ¬ n - 7 = 2 by omega, show ¬ n - 7 = 3 by omega, show ¬ n - 7 = 4 by omega,
      show ¬ n - 7 = 5 by omega, show ¬ n - 7 = 6 by omega,
      show ¬ n - 7 = 7 by omega, show ¬ n - 7 = 8 by omega, show ¬ n - 7 = 9 by omega,
      show ¬ n - 7 = 10 by omega, show ¬ n - 7 = 11 by omega, ↓reduceIte, Option.map_none]

theorem objTypeOf_some {n : Nat} {t : ApiObjectType} (h : objTypeOf n = some t) (h1 : n ≠ 1) (us : Nat) :
    n < 19 ∧ objBitsApi t us = zOf n us ∧ (isFrameType t = true ↔ n = 9 ∨ n = 10 ∨ n = 11) ∧
      (t = .untyped ↔ n = 0) ∧ (t = .capTableObject ↔ n = 4) ∧ (t = .schedContextObject ↔ n = 5) := by
  have hn : n < 19 := by
    by_contra hc; have := (objTypeOf_none n).2 (by omega); rw [this] at h; cases h
  refine ⟨hn, ?_⟩
  unfold objTypeOf archDataToObjType at h
  interval_cases n <;> simp at h <;> subst h <;> first | omega | (simp [objBitsApi, zOf, objBits, archKobjSize,
    defaultArchObject, pageBitsForSize, tableSize, isFrameType, archIsFrameType, endpointBits, ntfnBits, replyBits,
    slotBits, ptTranslationBits, wordSizeBits, pageBits] <;> omega)

/-- With FL4's object sizes (`Fl4Spec/Ext/TcbSize.lean`), `zOf` is
`obj_bits_api` for every type, the TCB included. -/
theorem objTypeOf_fl4 {n : Nat} {t : ApiObjectType} (h : objTypeOf n = some t) (us : Nat) :
    n < 19 ∧ fl4ObjBitsApi t us = zOf n us ∧ (isFrameType t = true ↔ n = 9 ∨ n = 10 ∨ n = 11) ∧
      (t = .untyped ↔ n = 0) ∧ (t = .capTableObject ↔ n = 4) ∧ (t = .schedContextObject ↔ n = 5) ∧
      (t = .tcbObject ↔ n = 1) := by
  have hn : n < 19 := by
    by_contra hc; have := (objTypeOf_none n).2 (by omega); rw [this] at h; cases h
  refine ⟨hn, ?_⟩
  unfold objTypeOf archDataToObjType at h
  interval_cases n <;> simp at h <;> subst h <;> first | omega | (simp [fl4ObjBitsApi, fl4TcbBits, objBitsApi, zOf,
    objBits, archKobjSize, defaultArchObject, pageBitsForSize, tableSize, isFrameType, archIsFrameType, endpointBits,
    ntfnBits, replyBits, slotBits, ptTranslationBits, wordSizeBits, pageBits] <;> omega)
end

section
open Fl4Spec

theorem dataToObjType_run (x : Data) (σ : State Unit) :
    (dataToObjType (Z := Unit) x).run σ =
      ({(match objTypeOf x.toNat with | some t => .ok t | none => .error (.invalidArgument 0), σ)}, False) := by
  unfold dataToObjType objTypeOf
  simp only [NonDetE.returnOk, ndE_pure_bind, dataToNat, unat]
  split_ifs <;> try rfl
  cases h : archDataToObjType (x.toNat - 7) <;> rfl
end

section
open Fl4Spec

theorem mapMEx_ensureEmpty_run (σ : State Unit) (caps : CslotPtr → Cap) :
    ∀ (slots : List CslotPtr), (∀ sl ∈ slots, getCap (Z := Unit) sl σ = ({(caps sl, σ)}, False)) →
    (NonDetE.mapMEx (ensureEmpty (Z := Unit)) slots).run σ =
      ({(if ∀ sl ∈ slots, caps sl = .nullCap then .ok () else .error .deleteFirst, σ)}, False)
  | [], _ => by simp [NonDetE.mapMEx]
  | sl :: rest, h => by
    unfold NonDetE.mapMEx
    have h1 := ensureEmpty_run sl σ (h sl (by simp))
    by_cases hn : caps sl = .nullCap
    · rw [if_pos hn] at h1
      rw [run_bind_ok h1, mapMEx_ensureEmpty_run σ caps rest (fun x hx => h x (by simp [hx]))]
      simp [hn]
    · rw [if_neg hn] at h1
      rw [run_bind_error h1]
      simp [hn]

theorem constOnFailure_run (σ : State Unit) (sl : CslotPtr) :
    constOnFailure (Z := Unit) false (do ensureNoChildren sl; NonDetE.returnOk true : SEMonad Unit Bool) σ =
      ({(decide (¬ ∃ x, σ.cdt x = some sl), σ)}, False) := by
  unfold constOnFailure NonDetE.catch
  by_cases hx : ∃ x, σ.cdt x = some sl
  · have h := ensureNoChildren_run (Z := Unit) σ sl
    rw [if_pos hx] at h
    rw [nd_bind_single' (run_bind_error h _)]
    simp [hx]; rfl
  · have h := ensureNoChildren_run (Z := Unit) σ sl
    rw [if_neg hx] at h
    rw [nd_bind_single' (by rw [run_bind_ok h]; rfl)]
    simp [hx]; rfl

end

section
open fl4_core

/-- The object size `object_size` gives, for every object type, with FL4's TCB size. -/
theorem retype_size_cases (nt us : U64) :
    untyped.retype_size nt us = ok (
      if nt.val ≥ 19 then .Err (.Sys (.InvalidArgument 0#u64)) else
      let z : Nat := zOf nt.val us.val
      if us.val ≥ 64 ∨ z > 47 then .Err (.Sys (.RangeError 0#u64 47#u64))
      else if nt.val = 4 ∧ us.val = 0 then .Err (.Sys (.InvalidArgument 1#u64))
      else if nt.val = 0 ∧ us.val < 4 then .Err (.Sys (.InvalidArgument 1#u64))
      else if nt.val = 5 ∧ us.val < 7 then .Err (.Sys (.InvalidArgument 1#u64))
      else .Ok ⟨BitVec.ofNat 64 z⟩) := by
  simp only [untyped.retype_size, objects.object_size, error.invalid_arg, error.range,
    fl4_abi.consts.object.Count, fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint,
    fl4_abi.consts.object.Notification, fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped,
    fl4_abi.consts.object.SchedContext, fl4_abi.consts.object.Reply, fl4_abi.consts.object.X86Page4K,
    fl4_abi.consts.object.X86LargePage, fl4_abi.consts.object.X64HugePage, fl4_abi.consts.object.X86PageTable,
    fl4_abi.consts.object.X86PageDirectory, fl4_abi.consts.object.X86Pdpt, fl4_abi.consts.object.X64Pml4,
    fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.bits.VCPU,
    fl4_abi.consts.bits.TCB, fl4_abi.consts.bits.ENDPOINT, fl4_abi.consts.bits.NOTIFICATION,
    fl4_abi.consts.bits.SLOT, fl4_abi.consts.bits.REPLY, fl4_abi.consts.bits.MAX_UNTYPED,
    fl4_abi.consts.bits.MIN_UNTYPED, fl4_abi.consts.bits.MIN_SCHED_CONTEXT, lift, bind_ok]
  by_cases h14 : nt.val ≥ 19
  · have : nt ≥ 19#u64 := by scalar_tac
    simp [this, h14]
  · have : ¬ nt ≥ 19#u64 := by scalar_tac
    simp only [this, ↓reduceIte, h14]
    have hn : nt.val < 19 := by omega
    simp only [u64_eq_iff]
    generalize hv : nt.val = n at *
    interval_cases n
    all_goals simp [zOf]
    all_goals try simp only [show (15#u64).val = 15 from rfl]
    all_goals (split_ifs <;> (try simp_all) <;> (try rfl) <;>
      (try (simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at *; omega)) <;>
      (try (congr 2; apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega)) <;> (try omega))
    all_goals try norm_num [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
    all_goals (
      have hsum : 5 + us.val < 18446744073709551616 := by omega
      simp only [Nat.mod_eq_of_lt hsum, show ¬ 47 < 5 + us.val by omega, ↓reduceIte]
      congr 2)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `ensure_empty_slots cnode from to`: `Ok` iff every slot of the range is
null, else `DeleteFirst`. -/
theorem ensure_empty_slots_eq (s : S) (cnode fr tp : U64) (hle : fr.val ≤ tp.val) :
    untyped.ensure_empty_slots st s cnode fr tp = ok
      (if ∀ i : Nat, fr.val ≤ i → i < tp.val → capAt (L.mem s) (slotAddr cnode.bv (BitVec.ofNat 64 i)) = ok .Null
       then .Ok () else .Err (.Sys .DeleteFirst)) := by
  unfold untyped.ensure_empty_slots untyped.ensure_empty_slots_loop
  let P : Nat → Prop := fun i => ∀ j : Nat, fr.val ≤ j → j < i →
    capAt (L.mem s) (slotAddr cnode.bv (BitVec.ofNat 64 j)) = ok .Null
  let rv : Nat → core.result.Result Unit error.Exc := fun i => if P i then .Ok () else .Err (.Sys .DeleteFirst)
  apply spec_eq_ok
  refine loop.spec_decr_nat (measure := fun x => tp.val - x.2.val)
    (inv := fun x => fr.val ≤ x.2.val ∧ x.2.val ≤ tp.val ∧ x.1 = rv x.2.val) _ _ _ ?_ ?_
  · rintro ⟨r, i⟩ ⟨h1, h2, hr⟩
    unfold untyped.ensure_empty_slots_loop.body
    simp only at h1 h2 hr ⊢
    by_cases hit : i < tp
    · rw [if_pos hit]
      have hit' : i.val < tp.val := hit
      by_cases hP : P i.val
      · have hro : r = .Ok () := by rw [hr]; simp [rv, hP]
        subst hro
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        rw [show obj.Slot.index cnode i = ok (slotAddr cnode.bv i.bv) from spec_eq_ok (slot_index_spec cnode i)]
        simp only [bind_ok]
        unfold cdt.ensure_empty_slot
        obtain ⟨c, hc⟩ := capAt_total (L.mem s) (slotAddr cnode.bv i.bv)
        rw [slot_cap_eq, hc]
        simp only [bind_ok]
        obtain ⟨i1, hi1, hv⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        have hiv : i.bv = BitVec.ofNat 64 i.val := by simp
        rw [hiv] at hc
        simp only [cap_is_null_eq]
        have hi1v : i1.val = i.val + 1 := by simpa using hv
        have hPs : P i1.val ↔ c = .Null := by
          rw [hi1v]
          constructor
          · intro h; have := h i.val h1 (by omega); rw [hc] at this; simpa using this
          · rintro rfl j hj1 hj2
            by_cases hj : j = i.val
            · rw [hj]; exact hc
            · exact hP j hj1 (by omega)
        cases hn : isNullB c
        · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, hi1, WP.spec_ok]
          have hcn : c ≠ .Null := by intro e; subst e; simp [isNullB] at hn
          refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
          simp only [rv]; rw [if_neg (fun h => hcn (hPs.1 h))]
        · simp only [↓reduceIte, bind_ok, hi1, WP.spec_ok]
          have hcn : c = .Null := by cases c <;> simp_all [isNullB]
          refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
          simp only [rv]; rw [if_pos (hPs.2 hcn)]
      · have hre : r = .Err (.Sys .DeleteFirst) := by rw [hr]; simp [rv, hP]
        subst hre
        simp only [core.result.Result.is_ok, Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
        exact (if_neg (fun h => hP (fun j a b => h j a (by omega)))).symm
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = tp.val := by have : ¬ i.val < tp.val := hit; omega
      rw [hr, this]
  · exact ⟨le_refl _, hle, by simp [rv, P]; intro j h1 h2; omega⟩

theorem align_up_eq (v a : U64) (ha : a.val < 64) :
    untyped.align_up v a = ok ⟨Fl4Spec.alignUp v.bv a.val⟩ := by
  apply spec_eq_ok
  unfold untyped.align_up
  simp only [lift, bind_ok]
  have h63 : (a &&& 63#u64).val = a.val := by
    have : (a &&& 63#u64).val = a.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod a.val 6
    omega
  step*
  rw [UScalar.eq_equiv_bv_eq]
  have e1 : i1.bv = BitVec.ofNat 64 (2 ^ a.val) := by
    apply BitVec.eq_of_toNat_eq
    show i1.val = _
    rw [i1_post, h63, Nat.one_shiftLeft]
    simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
  simp only [UScalar.bv_and, UScalar.bv_not, core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq, e1,
    Fl4Spec.alignUp]
  congr 1
  simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]

end
end

section
open fl4_core
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `retype_dest`'s range checks on a CNode of radix `r` (below 64). -/
def destRes (ptr : U64) (r : Nat) (off win : U64) : core.result.Result U64 error.Exc :=
  if off.val > 2 ^ r - 1 then .Err (.Sys (.RangeError 0#u64 ⟨BitVec.ofNat 64 (2 ^ r - 1)⟩))
  else if win.val < 1 ∨ win.val > 256 then .Err (.Sys (.RangeError 1#u64 256#u64))
  else if win.val > 2 ^ r - off.val then .Err (.Sys (.RangeError 1#u64 ⟨BitVec.ofNat 64 (2 ^ r - off.val)⟩))
  else .Ok ptr

/-- Every untyped cap read from memory has a size below 64. -/
theorem decode_untyped_inv {w0 w1 p sb fi : U64} {dev : Bool}
    (h : capability.Cap.decode w0 w1 = ok (.Untyped p sb fi dev)) : sb.val < 64 := by
  unfold capability.Cap.decode at h
  simp only [shr_eq _ 59#i32 (by decide) (by decide), unpack_ptr_eq, bind_ok] at h
  split at h
  all_goals simp [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
    shr_eq _ 58#i32 (by decide) (by decide), shr_eq _ 16#i32 (by decide) (by decide),
    shr_eq _ 53#i32 (by decide) (by decide), lift, bit_eq, from_code_eq,
    unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)] at h
  case h_1 =>
    obtain ⟨-, rfl, -, -⟩ := h
    simp only [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  all_goals split_ifs at h <;> simp_all

theorem capAt_untyped_inv {mem : U64 → U64} {a p sb fi : U64} {dev : Bool}
    (h : capAt mem a = ok (.Untyped p sb fi dev)) : sb.val < 64 := decode_untyped_inv h

/-- `retype_dest` after reading the node cap. -/
def tailOf (dep off win : U64) : capability.Cap → core.result.Result U64 error.Exc
  | .CNode ptr r _ _ => destRes ptr r.val off win
  | _ => .Err (.Sys (.FailedLookup false (.MissingCapability dep)))

theorem u64_ofNat_eq (x : U64) (n : Nat) (h : x.val = n) : x = ⟨BitVec.ofNat 64 n⟩ := by
  apply UScalar.eq_of_val_eq
  have : x.val < 2 ^ 64 := by have := x.hBounds; simpa [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] using this
  show x.val = (BitVec.ofNat 64 n).toNat
  simp; omega

theorem cnode_tail (dep off win : U64) (c : capability.Cap) (hc : CapWf c) :
    (do
      let o ← untyped.cnode_of c
      match o with
      | none =>
        ok (core.result.Result.Err (error.Exc.Sys (error.SysError.FailedLookup
          false (error.LookupFault.MissingCapability dep))))
      | some x =>
        let (dest, radix) := x
        let i ← lift (radix &&& 63#u64)
        let node_size ← 1#u64 <<< i
        let i1 ← lift (core.num.U64.wrapping_sub node_size 1#u64)
        if off > i1
        then
          let i2 ← lift (core.num.U64.wrapping_sub node_size 1#u64)
          error.range Std.U64 0#u64 i2
        else
          if win < 1#u64
          then error.range Std.U64 1#u64 untyped.RETYPE_FAN_OUT_LIMIT
          else
            if win > untyped.RETYPE_FAN_OUT_LIMIT
            then error.range Std.U64 1#u64 untyped.RETYPE_FAN_OUT_LIMIT
            else
              let i2 ← lift (core.num.U64.wrapping_sub node_size off)
              if win > i2
              then
                let i3 ← lift (core.num.U64.wrapping_sub node_size off)
                error.range Std.U64 1#u64 i3
              else ok (core.result.Result.Ok dest) : Result (core.result.Result U64 error.Exc)) =
      ok (tailOf dep off win c) := by
  cases c <;> try (simp only [untyped.cnode_of, bind_ok]; rfl)
  case CNode ptr r gs g =>
  have hr : r.val < 64 := hc.1
  have h63 : (r &&& 63#u64).val = r.val := by
    have : (r &&& 63#u64).val = r.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod r.val 6
    omega
  simp only [untyped.cnode_of, lift, bind_ok, uncurry_apply_pair]
  apply spec_eq_ok
  have hp : 2 ^ r.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr
  have hp1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  step
  have hns : node_size.val = 2 ^ r.val := by
    rw [node_size_post, h63, Nat.one_shiftLeft]
    simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  have hs1 : (core.num.U64.wrapping_sub node_size 1#u64).val = 2 ^ r.val - 1 := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hns]; omega
  simp only [tailOf, destRes, untyped.RETYPE_FAN_OUT_LIMIT, error.range]
  by_cases c1 : off.val > 2 ^ r.val - 1
  · have : off > core.num.U64.wrapping_sub node_size 1#u64 := by scalar_tac
    simp only [this, ↓reduceIte, c1, bind_ok, WP.spec_ok]
    rw [u64_ofNat_eq _ _ hs1]
  have : ¬ off > core.num.U64.wrapping_sub node_size 1#u64 := by scalar_tac
  simp only [this, ↓reduceIte, c1]
  have hso : (core.num.U64.wrapping_sub node_size off).val = 2 ^ r.val - off.val := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hns]; omega
  by_cases c2 : win.val < 1
  · have : win < 1#u64 := by scalar_tac
    simp [this, c2]
  have : ¬ win < 1#u64 := by scalar_tac
  simp only [this, ↓reduceIte, c2, false_or]
  by_cases c3 : win.val > 256
  · have : win > 256#u64 := by scalar_tac
    simp [this, c3]
  have : ¬ win > 256#u64 := by scalar_tac
  simp only [this, ↓reduceIte, c3]
  by_cases c4 : win.val > 2 ^ r.val - off.val
  · have : win > core.num.U64.wrapping_sub node_size off := by scalar_tac
    simp only [this, ↓reduceIte, c4, bind_ok, WP.spec_ok]
    rw [u64_ofNat_eq _ _ hso]
  have : ¬ win > core.num.U64.wrapping_sub node_size off := by scalar_tac
  simp only [this, ↓reduceIte, c4, bind_ok, WP.spec_ok]

/-- `retype_dest` in closed form, depth 0: `tailOf` the root cap. -/
theorem retype_dest_zero (s : S) (x0 idx off win : U64) (c : capability.Cap) (hc : capAt (L.mem s) x0 = ok c)
    (hcw : CapWf c) :
    untyped.retype_dest st s x0 idx 0#u64 off win = ok (tailOf 0#u64 off win c) := by
  unfold untyped.retype_dest
  simp only [↓reduceIte, slot_cap_eq, hc, bind_ok]
  exact cnode_tail _ _ _ c hcw

/-- `retype_dest` in closed form, depth not 0, the lookup finds slot `v`:
`tailOf` the cap there. -/
theorem retype_dest_ok (s : S) (x0 idx dep off win : U64) (h0 : dep ≠ 0#u64) (c : capability.Cap)
    (hc : capAt (L.mem s) x0 = ok c) (v : U64) (hl : cspace.lookup_target_slot st s c idx dep = ok (.Ok v))
    (c' : capability.Cap) (hc' : capAt (L.mem s) v = ok c') (hw : CapWf c') :
    untyped.retype_dest st s x0 idx dep off win = ok (tailOf dep off win c') := by
  unfold untyped.retype_dest
  simp only [h0, ↓reduceIte, slot_cap_eq, hc, hl, hc', bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  exact cnode_tail _ _ _ c' hw

/-- `retype_dest`, depth not 0, the lookup fails with `e`. -/
theorem retype_dest_err (s : S) (x0 idx dep off win : U64) (h0 : dep ≠ 0#u64) (c : capability.Cap)
    (hc : capAt (L.mem s) x0 = ok c) (e : error.Exc) (hl : cspace.lookup_target_slot st s c idx dep = ok (.Err e)) :
    untyped.retype_dest st s x0 idx dep off win = ok (.Err e) := by
  unfold untyped.retype_dest
  simp only [h0, ↓reduceIte, slot_cap_eq, hc, hl, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok]

end

section
open Fl4Spec

theorem objSize_untyped (d : Bool) (p : BitVec 64) (n f : Nat) :
    Fl4Spec.objSize (.untypedCap d p n f) = 1#64 <<< n := by
  unfold Fl4Spec.objSize
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq]

theorem natToCref_eq (r i : Nat) (hr : r ≤ 64) : natToCref r i = bitsOf (i % 2 ^ 64) r := by
  unfold natToCref
  rw [show wordBits = 64 from rfl, toBl_drop _ _ hr]
  simp

@[simp] theorem natToCref_length (r i : Nat) (hr : r ≤ 64) : (natToCref r i).length = r := by
  rw [natToCref_eq _ _ hr, length_bitsOf]

/-- Slot `i` of a CNode of radix `r` (`nat_to_cref r i`) is at FL4's slot
address `p + 32 i`. -/
theorem cslotAddr_natToCref (p : BitVec 64) (r i : Nat) (hr : r ≤ 64) (hi : i < 2 ^ r) :
    cslotAddr (p, natToCref r i) = slotAddr p (BitVec.ofNat 64 i) := by
  unfold cslotAddr
  simp only
  rw [natToCref_eq _ _ hr, ofBl_bitsOf_eq]
  have h1 : i < 2 ^ 64 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hr)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hi]

end
end Fl4Proofs.P3
