/-
P3 (DESIGN.md §9), CSpace: FL4's two-word capability encoding as functions
of the words, and its round trip.

* `decodeF`, `encodeF`: `Cap::decode` / `Cap::encode` on `BitVec 64`
  words, with `decode_eq`, `encode_eq` (the extracted code computes them).
* `EncWf c`: the fields of `c` fit their encoding (canonical pointer, field
  widths). `decode_encode`: `Cap::decode` after `Cap::encode` is the
  identity under `EncWf`.
-/
import Fl4Proofs.P3.CapRel
open Aeneas Aeneas.Std Result
open fl4_core
namespace Fl4Proofs.P3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

theorem bit_val (w : U64) (n : U64) (hn : n.val < 64) : capability.bit w n = ok (w.bv.getLsbD n.val) := by
  rw [bit_eq]
  have : (n &&& 63#u64).val = n.val := by
    have : (n &&& 63#u64).val = n.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod n.val 6
    omega
  rw [this]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq, BitVec.toNat_eq]
  simp [Nat.and_one_is_mod, BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]


def M48 : BitVec 64 := 0xffffffffffff#64

/-- `unpack_ptr` on words. -/
def unpackF (w : BitVec 64) : BitVec 64 :=
  if (w &&& M48) &&& 0x800000000000#64 = 0#64 then w &&& M48 else (w &&& M48) ||| 0xffff000000000000#64

def frameSizeF (c : U64) : capability.FrameSize :=
  if c = 1#u64 then .Large else if c = 2#u64 then .Huge else .Small

/-- `Cap::decode` as a function of the words. -/
def decodeF (w0 w1 : BitVec 64) : capability.Cap :=
  let p : U64 := ⟨unpackF w0⟩
  match (w0 >>> 59).toNat with
  | 1 => .Untyped p ⟨(w0 >>> 48) &&& 63#64⟩ ⟨w1⟩ (w0.getLsbD 54)
  | 2 => .Endpoint p ⟨w1⟩ (w0.getLsbD 48) (w0.getLsbD 49) (w0.getLsbD 50) (w0.getLsbD 51)
  | 3 => .Notification p ⟨w1⟩ (w0.getLsbD 48) (w0.getLsbD 49)
  | 4 => .Reply p (w0.getLsbD 48)
  | 5 => .CNode p ⟨(w0 >>> 48) &&& 63#64⟩ ⟨w1 >>> 58⟩ ⟨w1 &&& 0x03ffffffffffffff#64⟩
  | 6 => .Thread p
  | 7 => .IrqControl
  | 8 => .IrqHandler ⟨w1⟩
  | 9 => .Zombie p ⟨(w0 >>> 48) &&& 255#64⟩ ⟨w1⟩
  | 10 => .Domain
  | 11 => .SchedContext p ⟨(w0 >>> 48) &&& 63#64⟩
  | 12 => .SchedControl ⟨w1⟩
  | 13 => .Frame p (frameSizeF ⟨(w0 >>> 48) &&& 3#64⟩) ⟨(w0 >>> 50) &&& 3#64⟩ (w0.getLsbD 52) (w0.getLsbD 53) (w0.getLsbD 58)
      ⟨asidF w0 54 w1⟩ ⟨w1 &&& M48⟩
  | 14 => .PageTable p (w0.getLsbD 48) ⟨asidF w0 49 w1⟩ ⟨w1 &&& M48⟩
  | 15 => .PageDirectory p (w0.getLsbD 48) ⟨asidF w0 49 w1⟩ ⟨w1 &&& M48⟩
  | 16 => .Pdpt p (w0.getLsbD 48) ⟨asidF w0 49 w1⟩ ⟨w1 &&& M48⟩
  | 17 => .Pml4 p (w0.getLsbD 48) ⟨w1⟩
  | 18 => .AsidControl
  | 19 => .AsidPool p ⟨w1⟩
  | 22 => .Vcpu p
  | 23 => .Ept p ⟨(w0 >>> 53) &&& 63#64⟩ (w0.getLsbD 48) ⟨asidF w0 49 w1⟩ ⟨w1 &&& M48⟩
  | 20 => .IoPortControl
  | 21 => .IoPort ⟨w1 &&& 0xffff#64⟩ ⟨(w1 >>> 16) &&& 0xffff#64⟩
      (if w0 &&& M48 = 0#64 then 0#u64 else p)
  | _ => .Null

theorem decode_eq (w0 w1 : U64) : capability.Cap.decode w0 w1 = ok (decodeF w0.bv w1.bv) := by
  unfold capability.Cap.decode
  simp only [shr_eq _ 59#i32 (by decide) (by decide), unpack_ptr_eq, bind_ok]
  split <;> rename_i heq
  case h_1 =>
    have htk : (w0.bv >>> 59).toNat = 1 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_2 =>
    have htk : (w0.bv >>> 59).toNat = 2 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_3 =>
    have htk : (w0.bv >>> 59).toNat = 3 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_4 =>
    have htk : (w0.bv >>> 59).toNat = 4 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_5 =>
    have htk : (w0.bv >>> 59).toNat = 5 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_6 =>
    have htk : (w0.bv >>> 59).toNat = 6 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_7 =>
    have htk : (w0.bv >>> 59).toNat = 7 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_8 =>
    have htk : (w0.bv >>> 59).toNat = 8 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_9 =>
    have htk : (w0.bv >>> 59).toNat = 9 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_10 =>
    have htk : (w0.bv >>> 59).toNat = 10 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_11 =>
    have htk : (w0.bv >>> 59).toNat = 11 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_12 =>
    have htk : (w0.bv >>> 59).toNat = 12 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_13 =>
    have htk : (w0.bv >>> 59).toNat = 13 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_14 =>
    have htk : (w0.bv >>> 59).toNat = 14 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_15 =>
    have htk : (w0.bv >>> 59).toNat = 15 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_16 =>
    have htk : (w0.bv >>> 59).toNat = 16 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_17 =>
    have htk : (w0.bv >>> 59).toNat = 17 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_18 =>
    have htk : (w0.bv >>> 59).toNat = 18 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_19 =>
    have htk : (w0.bv >>> 59).toNat = 19 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_20 =>
    have htk : (w0.bv >>> 59).toNat = 22 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_21 =>
    have htk : (w0.bv >>> 59).toNat = 23 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_22 =>
    have htk : (w0.bv >>> 59).toNat = 20 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    all_goals rfl
  case h_23 =>
    have htk : (w0.bv >>> 59).toNat = 21 := congrArg UScalar.val heq
    try simp only [decodeF, htk]
    try simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
      shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide),
      shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok, capability.PTR_MASK,
      bit_val _ 48#u64 (by decide), bit_val _ 49#u64 (by decide), bit_val _ 50#u64 (by decide),
      bit_val _ 51#u64 (by decide), bit_val _ 52#u64 (by decide), bit_val _ 53#u64 (by decide),
      bit_val _ 54#u64 (by decide), bit_val _ 58#u64 (by decide), from_code_eq,
      unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)]
    simp only [UScalar.eq_equiv_bv_eq]
    change (if w0.bv &&& M48 = 0#64 then _ else _) = _
    split <;> rfl
  case h_24 =>
    simp only [decodeF]
    split <;> rename_i hk
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 1#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 2#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 3#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 4#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 5#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 6#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 7#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 8#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 9#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 10#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 11#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 12#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 13#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 14#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 15#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 16#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 17#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 18#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 19#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 22#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 23#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 20#u64) hk) (by assumption)
    · exact absurd (UScalar.eq_of_val_eq (i := (⟨w0.bv >>> I32.toNat 59#i32⟩ : U64)) (j := 21#u64) hk) (by assumption)
    · rfl

theorem shl_u64_eq (x i : U64) (h : i.val < 64) : x <<< i = ok ⟨x.bv <<< i.val⟩ := by
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
  simp [h, BitVec.shiftLeft_eq]

theorem b_eq (v : Bool) (n : U64) (h : n.val < 64) :
    capability.b v n = ok ⟨if v then 1#64 <<< n.val else 0#64⟩ := by
  unfold capability.b
  have : (n &&& 63#u64).val = n.val := by
    have : (n &&& 63#u64).val = n.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod n.val 6
    omega
  cases v
  · rfl
  · simp only [lift, bind_ok, ite_true]
    rw [shl_u64_eq _ _ (by omega), this]; rfl

/-- `asid_high`. -/
def asidHiF (asid : U64) (sh : Nat) : BitVec 64 := ((asid.bv >>> 16) &&& 0xf#64) <<< sh

theorem asid_high_eq (asid sh : U64) (h : sh.val < 64) :
    capability.asid_high asid sh = ok ⟨asidHiF asid sh.val⟩ := by
  unfold capability.asid_high
  have : (sh &&& 63#u64).val = sh.val := by
    have : (sh &&& 63#u64).val = sh.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod sh.val 6
    omega
  simp only [shr_eq _ 16#i32 (by decide) (by decide), lift, bind_ok]
  rw [shl_u64_eq _ _ (by omega), this]; rfl

def codeF : capability.FrameSize → BitVec 64
  | .Small => 0#64
  | .Large => 1#64
  | .Huge => 2#64

theorem code_eq (sz : capability.FrameSize) : capability.FrameSize.code sz = ok ⟨codeF sz⟩ := by
  cases sz <;> rfl

def tagF (k : Nat) : BitVec 64 := BitVec.ofNat 64 k <<< 59
def packF (p : U64) : BitVec 64 := p.bv &&& 0xffffffffffff#64
def bF (v : Bool) (n : Nat) : BitVec 64 := if v then 1#64 <<< n else 0#64

/-- `Cap::encode` on words. -/
def encodeF : capability.Cap → BitVec 64 × BitVec 64
  | .Null => (0#64, 0#64)
  | .Untyped p sb fi dev => (tagF 1 ||| packF p ||| ((sb.bv &&& 63#64) <<< 48) ||| bF dev 54, fi.bv)
  | .Endpoint p badge s r g gr =>
    (tagF 2 ||| packF p ||| bF s 48 ||| bF r 49 ||| bF g 50 ||| bF gr 51, badge.bv)
  | .Notification p badge s r => (tagF 3 ||| packF p ||| bF s 48 ||| bF r 49, badge.bv)
  | .Reply p g => (tagF 4 ||| packF p ||| bF g 48, 0#64)
  | .CNode p r gs g => (tagF 5 ||| packF p ||| ((r.bv &&& 63#64) <<< 48),
      ((gs.bv &&& 63#64) <<< 58) ||| (g.bv &&& 0x03ffffffffffffff#64))
  | .Thread p => (tagF 6 ||| packF p, 0#64)
  | .IrqControl => (tagF 7, 0#64)
  | .IrqHandler irq => (tagF 8, irq.bv)
  | .Zombie p zt n => (tagF 9 ||| packF p ||| ((zt.bv &&& 255#64) <<< 48), n.bv)
  | .Domain => (tagF 10, 0#64)
  | .SchedContext p sb => (tagF 11 ||| packF p ||| ((sb.bv &&& 63#64) <<< 48), 0#64)
  | .SchedControl cpu => (tagF 12, cpu.bv)
  | .Frame p sz r dev m ept asid va =>
    (tagF 13 ||| packF p ||| (codeF sz <<< 48) ||| ((r.bv &&& 3#64) <<< 50) ||| bF dev 52 ||| bF m 53 ||| bF ept 58 ||| asidHiF asid 54,
      ((asid.bv &&& 0xffff#64) <<< 48) ||| (va.bv &&& 0xffffffffffff#64))
  | .PageTable p m asid va => (tagF 14 ||| packF p ||| bF m 48 ||| asidHiF asid 49,
      ((asid.bv &&& 0xffff#64) <<< 48) ||| (va.bv &&& 0xffffffffffff#64))
  | .PageDirectory p m asid va => (tagF 15 ||| packF p ||| bF m 48 ||| asidHiF asid 49,
      ((asid.bv &&& 0xffff#64) <<< 48) ||| (va.bv &&& 0xffffffffffff#64))
  | .Pdpt p m asid va => (tagF 16 ||| packF p ||| bF m 48 ||| asidHiF asid 49,
      ((asid.bv &&& 0xffff#64) <<< 48) ||| (va.bv &&& 0xffffffffffff#64))
  | .Pml4 p m asid => (tagF 17 ||| packF p ||| bF m 48, asid.bv)
  | .AsidControl => (tagF 18, 0#64)
  | .AsidPool p base => (tagF 19 ||| packF p, base.bv)
  | .IoPortControl => (tagF 20, 0#64)
  | .Vcpu p => (tagF 22 ||| packF p, 0#64)
  | .Ept p level m asid va =>
      (tagF 23 ||| packF p ||| bF m 48 ||| asidHiF asid 49 ||| ((level.bv &&& 63#64) <<< 53),
        ((asid.bv &&& 0xffff#64) <<< 48) ||| (va.bv &&& M48))
  | .IoPort f l vcpu => (tagF 21 ||| packF vcpu, (f.bv &&& 0xffff#64) ||| ((l.bv &&& 0xffff#64) <<< 16))

theorem encode_eq (c : capability.Cap) :
    capability.Cap.encode c = ok (⟨(encodeF c).1⟩, ⟨(encodeF c).2⟩) := by
  cases c <;>
    simp only [capability.Cap.encode, encodeF, tagF, packF, bF, codeF, asidHiF, M48, capability.tag, capability.pack_ptr, lift, bind_ok, capability.PTR_MASK,
      shl_eq _ 59#i32 (by decide) (by decide), shl_eq _ 48#i32 (by decide) (by decide),
      shl_eq _ 50#i32 (by decide) (by decide), shl_eq _ 53#i32 (by decide) (by decide), shl_eq _ 58#i32 (by decide) (by decide),
      shl_eq _ 16#i32 (by decide) (by decide),
      b_eq _ 48#u64 (by decide), b_eq _ 49#u64 (by decide), b_eq _ 50#u64 (by decide),
      b_eq _ 51#u64 (by decide), b_eq _ 52#u64 (by decide), b_eq _ 53#u64 (by decide),
      b_eq _ 54#u64 (by decide), b_eq _ 58#u64 (by decide), code_eq, asid_high_eq _ 54#u64 (by decide), asid_high_eq _ 49#u64 (by decide)] <;> rfl

@[simp] theorem getElem_bF (v : Bool) (n i : Nat) (h : i < 64) :
    (bF v n)[i] = (v && decide (i = n)) := by
  cases v
  · simp [bF]
  · simp only [bF, ite_true, BitVec.getElem_shiftLeft, Bool.true_and]
    by_cases hin : i < n
    · simp [hin]; omega
    · simp [hin, BitVec.getElem_one]; omega

set_option hygiene false in
/-- An equation of 64-bit words, bit by bit. -/
macro "bvext" : tactic => `(tactic| (
  apply BitVec.eq_of_getElem_eq; intro i hi
  have hi' : i < 64 := by simpa using hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft,
    tagF, packF, getElem_bF, encodeF, M48, asidF, asidHiF]
  interval_cases i <;> simp [*, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_eq_getElem]))

theorem unpack_gen (w : BitVec 64) (p : U64) (hp : Canonical p)
    (hlow : ∀ j (hj : j < 64), j < 48 → w[j] = p.bv[j]) : unpackF w = p.bv := by
  unfold unpackF M48
  rcases hp with hp | hp <;> split <;> rename_i hc
  · apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and]
    interval_cases i <;> simp [hlow, hp]
  · exfalso; apply hc
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and]
    interval_cases i <;> simp [hlow, hp]
  · exfalso
    have := congrArg (fun x : BitVec 64 => x[47]) hc
    simp [hlow, hp] at this
  · apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    interval_cases i <;> simp [hlow, hp]

theorem tag_gen {w : BitVec 64} {k : Nat} (h : w >>> 59 = BitVec.ofNat 64 k) (hk : k < 32) :
    (w >>> 59).toNat = k := by
  rw [h, BitVec.toNat_ofNat]; omega

/-- The fields of a cap fit their encoding. -/
def EncWf : capability.Cap → Prop
  | .Untyped p sb _ _ => Canonical p ∧ sb.val < 64
  | .Endpoint p .. => Canonical p
  | .Notification p .. => Canonical p
  | .Reply p _ => Canonical p
  | .CNode p r gs g => Canonical p ∧ r.val < 64 ∧ gs.val < 64 ∧ g.val < 2 ^ 58
  | .Thread p => Canonical p
  | .Zombie p zt _ => Canonical p ∧ zt.val < 256
  | .SchedContext p sb => Canonical p ∧ sb.val < 64
  | .Frame p _ r _ _ _ asid va => Canonical p ∧ r.val < 4 ∧ asid.val < 2 ^ 20 ∧ va.val < 2 ^ 48
  | .PageTable p _ asid va => Canonical p ∧ asid.val < 2 ^ 20 ∧ va.val < 2 ^ 48
  | .PageDirectory p _ asid va => Canonical p ∧ asid.val < 2 ^ 20 ∧ va.val < 2 ^ 48
  | .Pdpt p _ asid va => Canonical p ∧ asid.val < 2 ^ 20 ∧ va.val < 2 ^ 48
  | .Pml4 p _ _ => Canonical p
  | .AsidPool p _ => Canonical p
  | .Vcpu p => Canonical p
  | .Ept p level _ asid va => Canonical p ∧ level.val < 64 ∧ asid.val < 2 ^ 20 ∧ va.val < 2 ^ 48
  | .IoPort f l vcpu => f.val < 2 ^ 16 ∧ l.val < 2 ^ 16 ∧ Canonical vcpu
  | _ => True

theorem hb {x : U64} {k : Nat} (h : x.val < 2 ^ k) : ∀ j (hj : j < 64), k ≤ j → x.bv[j] = false :=
  high_bits_false (by simpa using h)

set_option hygiene false in
/-- Close the field equations of a decoded cap. -/
macro "fields" : tactic => `(tactic| (
  all_goals first
    | rfl
    | (rw [UScalar.eq_equiv_bv_eq]; bvext)
    | (simp [*, tagF, packF, asidF, asidHiF, BitVec.getElem_shiftLeft, BitVec.getElem_and, getElem_bF])))

theorem frameSizeF_codeF (sz : capability.FrameSize) (x : BitVec 64) (h : x = codeF sz) :
    frameSizeF ⟨x⟩ = sz := by
  subst h; cases sz <;> simp [frameSizeF, codeF, UScalar.eq_equiv_bv_eq]

theorem codeF_hb (sz : capability.FrameSize) : ∀ j (hj : j < 64), 2 ≤ j → (codeF sz)[j] = false :=
  high_bits_false (by cases sz <;> decide)

theorem rt_Null (hc : EncWf .Null) :
    decodeF (encodeF .Null).1 (encodeF .Null).2 = .Null := by
  rfl

theorem rt_Untyped (p : _) (sb : _) (fi : _) (dev : _) (hc : EncWf (.Untyped p sb fi dev)) :
    decodeF (encodeF (.Untyped p sb fi dev)).1 (encodeF (.Untyped p sb fi dev)).2 = (.Untyped p sb fi dev) := by
  obtain ⟨hp, h1⟩ := hc; have h1 := hb (k := 6) h1
  have htag := tag_gen (w := (encodeF (.Untyped p sb fi dev)).1) (k := 1) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Untyped p sb fi dev)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Endpoint (p : _) (badge : _) (s : _) (r : _) (g : _) (gr : _) (hc : EncWf (.Endpoint p badge s r g gr)) :
    decodeF (encodeF (.Endpoint p badge s r g gr)).1 (encodeF (.Endpoint p badge s r g gr)).2 = (.Endpoint p badge s r g gr) := by
  have hp := hc
  have htag := tag_gen (w := (encodeF (.Endpoint p badge s r g gr)).1) (k := 2) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Endpoint p badge s r g gr)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Notification (p : _) (badge : _) (s : _) (r : _) (hc : EncWf (.Notification p badge s r)) :
    decodeF (encodeF (.Notification p badge s r)).1 (encodeF (.Notification p badge s r)).2 = (.Notification p badge s r) := by
  have hp := hc
  have htag := tag_gen (w := (encodeF (.Notification p badge s r)).1) (k := 3) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Notification p badge s r)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Reply (p : _) (g : _) (hc : EncWf (.Reply p g)) :
    decodeF (encodeF (.Reply p g)).1 (encodeF (.Reply p g)).2 = (.Reply p g) := by
  have hp := hc
  have htag := tag_gen (w := (encodeF (.Reply p g)).1) (k := 4) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Reply p g)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_CNode (p : _) (r : _) (gs : _) (g : _) (hc : EncWf (.CNode p r gs g)) :
    decodeF (encodeF (.CNode p r gs g)).1 (encodeF (.CNode p r gs g)).2 = (.CNode p r gs g) := by
  obtain ⟨hp, h1, h2, h3⟩ := hc; have h1 := hb (k := 6) h1; have h2 := hb (k := 6) h2; have h3 := hb (k := 58) h3
  have htag := tag_gen (w := (encodeF (.CNode p r gs g)).1) (k := 5) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.CNode p r gs g)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Thread (p : _) (hc : EncWf (.Thread p)) :
    decodeF (encodeF (.Thread p)).1 (encodeF (.Thread p)).2 = (.Thread p) := by
  have hp := hc
  have htag := tag_gen (w := (encodeF (.Thread p)).1) (k := 6) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Thread p)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_IrqControl  (hc : EncWf .IrqControl) :
    decodeF (encodeF .IrqControl).1 (encodeF .IrqControl).2 = .IrqControl := by
  have htag := tag_gen (w := (encodeF .IrqControl).1) (k := 7) (by bvext) (by decide)
  simp only [decodeF, htag]
  all_goals clear htag
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_IrqHandler (irq : _) (hc : EncWf (.IrqHandler irq)) :
    decodeF (encodeF (.IrqHandler irq)).1 (encodeF (.IrqHandler irq)).2 = (.IrqHandler irq) := by
  have htag := tag_gen (w := (encodeF (.IrqHandler irq)).1) (k := 8) (by bvext) (by decide)
  simp only [decodeF, htag]
  all_goals clear htag
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Zombie (p : _) (zt : _) (n : _) (hc : EncWf (.Zombie p zt n)) :
    decodeF (encodeF (.Zombie p zt n)).1 (encodeF (.Zombie p zt n)).2 = (.Zombie p zt n) := by
  obtain ⟨hp, h1⟩ := hc; have h1 := hb (k := 8) h1
  have htag := tag_gen (w := (encodeF (.Zombie p zt n)).1) (k := 9) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Zombie p zt n)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Domain  (hc : EncWf .Domain) :
    decodeF (encodeF .Domain).1 (encodeF .Domain).2 = .Domain := by
  have htag := tag_gen (w := (encodeF .Domain).1) (k := 10) (by bvext) (by decide)
  simp only [decodeF, htag]
  all_goals clear htag
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_SchedContext (p : _) (sb : _) (hc : EncWf (.SchedContext p sb)) :
    decodeF (encodeF (.SchedContext p sb)).1 (encodeF (.SchedContext p sb)).2 = (.SchedContext p sb) := by
  obtain ⟨hp, h1⟩ := hc; have h1 := hb (k := 6) h1
  have htag := tag_gen (w := (encodeF (.SchedContext p sb)).1) (k := 11) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.SchedContext p sb)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_SchedControl (cpu : _) (hc : EncWf (.SchedControl cpu)) :
    decodeF (encodeF (.SchedControl cpu)).1 (encodeF (.SchedControl cpu)).2 = (.SchedControl cpu) := by
  have htag := tag_gen (w := (encodeF (.SchedControl cpu)).1) (k := 12) (by bvext) (by decide)
  simp only [decodeF, htag]
  all_goals clear htag
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Frame (p : _) (sz : _) (r : _) (dev : _) (m : _) (ept : _) (asid : _) (va : _) (hc : EncWf (.Frame p sz r dev m ept asid va)) :
    decodeF (encodeF (.Frame p sz r dev m ept asid va)).1 (encodeF (.Frame p sz r dev m ept asid va)).2 = (.Frame p sz r dev m ept asid va) := by
  obtain ⟨hp, h1, h2, h3⟩ := hc; have h1 := hb (k := 2) h1; have h2 := hb (k := 20) h2; have h3 := hb (k := 48) h3
  have h4 := codeF_hb sz
  have htag := tag_gen (w := (encodeF (.Frame p sz r dev m ept asid va)).1) (k := 13) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Frame p sz r dev m ept asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF]
    interval_cases j <;> simp [h4])
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  simp only [encodeF]
  congr 1
  · apply frameSizeF_codeF; bvext
  all_goals fields

theorem rt_PageTable (p : _) (m : _) (asid : _) (va : _) (hc : EncWf (.PageTable p m asid va)) :
    decodeF (encodeF (.PageTable p m asid va)).1 (encodeF (.PageTable p m asid va)).2 = (.PageTable p m asid va) := by
  obtain ⟨hp, h2, h3⟩ := hc; have h2 := hb (k := 20) h2; have h3 := hb (k := 48) h3
  have htag := tag_gen (w := (encodeF (.PageTable p m asid va)).1) (k := 14) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.PageTable p m asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_PageDirectory (p : _) (m : _) (asid : _) (va : _) (hc : EncWf (.PageDirectory p m asid va)) :
    decodeF (encodeF (.PageDirectory p m asid va)).1 (encodeF (.PageDirectory p m asid va)).2 = (.PageDirectory p m asid va) := by
  obtain ⟨hp, h2, h3⟩ := hc; have h2 := hb (k := 20) h2; have h3 := hb (k := 48) h3
  have htag := tag_gen (w := (encodeF (.PageDirectory p m asid va)).1) (k := 15) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.PageDirectory p m asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Pdpt (p : _) (m : _) (asid : _) (va : _) (hc : EncWf (.Pdpt p m asid va)) :
    decodeF (encodeF (.Pdpt p m asid va)).1 (encodeF (.Pdpt p m asid va)).2 = (.Pdpt p m asid va) := by
  obtain ⟨hp, h2, h3⟩ := hc; have h2 := hb (k := 20) h2; have h3 := hb (k := 48) h3
  have htag := tag_gen (w := (encodeF (.Pdpt p m asid va)).1) (k := 16) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Pdpt p m asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Pml4 (p : _) (m : _) (asid : _) (hc : EncWf (.Pml4 p m asid)) :
    decodeF (encodeF (.Pml4 p m asid)).1 (encodeF (.Pml4 p m asid)).2 = (.Pml4 p m asid) := by
  have hp := hc
  have htag := tag_gen (w := (encodeF (.Pml4 p m asid)).1) (k := 17) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Pml4 p m asid)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_AsidControl  (hc : EncWf .AsidControl) :
    decodeF (encodeF .AsidControl).1 (encodeF .AsidControl).2 = .AsidControl := by
  have htag := tag_gen (w := (encodeF .AsidControl).1) (k := 18) (by bvext) (by decide)
  simp only [decodeF, htag]
  all_goals clear htag
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_AsidPool (p : _) (base : _) (hc : EncWf (.AsidPool p base)) :
    decodeF (encodeF (.AsidPool p base)).1 (encodeF (.AsidPool p base)).2 = (.AsidPool p base) := by
  have hp := hc
  have htag := tag_gen (w := (encodeF (.AsidPool p base)).1) (k := 19) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.AsidPool p base)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  all_goals clear htag hun
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_IoPortControl  (hc : EncWf .IoPortControl) :
    decodeF (encodeF .IoPortControl).1 (encodeF .IoPortControl).2 = .IoPortControl := by
  have htag := tag_gen (w := (encodeF .IoPortControl).1) (k := 20) (by bvext) (by decide)
  simp only [decodeF, htag]
  all_goals clear htag
  try simp only [encodeF]
  all_goals (try congr 1)
  all_goals fields

theorem rt_Vcpu (p : U64) (hc : EncWf (.Vcpu p)) :
    decodeF (encodeF (.Vcpu p)).1 (encodeF (.Vcpu p)).2 = .Vcpu p := by
  have htag := tag_gen (w := (encodeF (.Vcpu p)).1) (k := 22) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Vcpu p)).1 p hc (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]

theorem rt_Ept (p level : U64) (m : Bool) (asid va : U64) (hc : EncWf (.Ept p level m asid va)) :
    decodeF (encodeF (.Ept p level m asid va)).1 (encodeF (.Ept p level m asid va)).2 = .Ept p level m asid va := by
  obtain ⟨hp, h1, h2, h3⟩ := hc
  have h1 := hb (k := 6) h1; have h2 := hb (k := 20) h2; have h3 := hb (k := 48) h3
  have htag := tag_gen (w := (encodeF (.Ept p level m asid va)).1) (k := 23) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Ept p level m asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF, M48]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  clear htag hun
  simp only [encodeF]
  congr 1 <;> fields

theorem rt_IoPort (f l vcpu : U64) (hc : EncWf (.IoPort f l vcpu)) :
    decodeF (encodeF (.IoPort f l vcpu)).1 (encodeF (.IoPort f l vcpu)).2 = .IoPort f l vcpu := by
  obtain ⟨h1, h2, hp⟩ := hc; have h1 := hb (k := 16) h1; have h2 := hb (k := 16) h2
  have htag := tag_gen (w := (encodeF (.IoPort f l vcpu)).1) (k := 21) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.IoPort f l vcpu)).1 vcpu hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, BitVec.getElem_and, BitVec.getElem_shiftLeft]
    interval_cases j <;> simp)
  simp only [decodeF, htag, hun]
  have hv : (if (encodeF (.IoPort f l vcpu)).1 &&& M48 = 0#64 then 0#u64 else vcpu) = vcpu := by
    split <;> rename_i h
    · have hz : unpackF (encodeF (.IoPort f l vcpu)).1 = 0#64 := by
        unfold unpackF
        simp [h]
      rw [hun] at hz
      exact (by rw [UScalar.eq_equiv_bv_eq]; exact hz.symm)
    · rfl
  rw [hv]
  simp only [encodeF]
  congr 1 <;> fields

/-- `Cap::decode` after `Cap::encode`, on words, is the identity on caps whose
fields fit (`EncWf`). -/
theorem decodeF_encodeF (c : capability.Cap) (hc : EncWf c) :
    decodeF (encodeF c).1 (encodeF c).2 = c := by
  cases c with
  | Null  => exact rt_Null  hc
  | Untyped p sb fi dev => exact rt_Untyped p sb fi dev hc
  | Endpoint p badge s r g gr => exact rt_Endpoint p badge s r g gr hc
  | Notification p badge s r => exact rt_Notification p badge s r hc
  | Reply p g => exact rt_Reply p g hc
  | CNode p r gs g => exact rt_CNode p r gs g hc
  | Thread p => exact rt_Thread p hc
  | IrqControl  => exact rt_IrqControl  hc
  | IrqHandler irq => exact rt_IrqHandler irq hc
  | Zombie p zt n => exact rt_Zombie p zt n hc
  | Domain  => exact rt_Domain  hc
  | SchedContext p sb => exact rt_SchedContext p sb hc
  | SchedControl cpu => exact rt_SchedControl cpu hc
  | Frame p sz r dev m ept asid va => exact rt_Frame p sz r dev m ept asid va hc
  | PageTable p m asid va => exact rt_PageTable p m asid va hc
  | PageDirectory p m asid va => exact rt_PageDirectory p m asid va hc
  | Pdpt p m asid va => exact rt_Pdpt p m asid va hc
  | Pml4 p m asid => exact rt_Pml4 p m asid hc
  | AsidControl  => exact rt_AsidControl  hc
  | AsidPool p base => exact rt_AsidPool p base hc
  | IoPortControl  => exact rt_IoPortControl  hc
  | Vcpu p => exact rt_Vcpu p hc
  | Ept p level m asid va => exact rt_Ept p level m asid va hc
  | IoPort f l vcpu => exact rt_IoPort f l vcpu hc

/-- **`Cap::decode` after `Cap::encode` is the identity** on caps whose fields
fit their encoding. -/
theorem decode_encode (c : capability.Cap) (hc : EncWf c) :
    ∃ w0 w1, capability.Cap.encode c = ok (w0, w1) ∧ capability.Cap.decode w0 w1 = ok c :=
  ⟨_, _, encode_eq c, by rw [decode_eq]; exact congrArg ok (decodeF_encodeF c hc)⟩

/-! ## Decoded caps fit their encoding -/

theorem unpackF_canonical (w : BitVec 64) : Canonical ⟨unpackF w⟩ := by
  unfold unpackF M48
  split <;> rename_i h
  · left; intro j hj hj'
    show (w &&& 0xffffffffffff#64)[j] = false
    by_cases h47 : j = 47
    · subst h47
      have := congrArg (fun x : BitVec 64 => x[47]) h
      simpa using this
    · simp only [BitVec.getElem_and]; interval_cases j <;> simp_all
  · right; intro j hj hj'
    show (w &&& 0xffffffffffff#64 ||| 0xffff000000000000#64)[j] = true
    by_cases h47 : j = 47
    · subst h47
      by_contra hc
      apply h
      apply BitVec.eq_of_getElem_eq; intro i hi
      simp only [BitVec.getElem_and, BitVec.getElem_or] at hc ⊢
      interval_cases i <;> simp_all
    · simp only [BitVec.getElem_and, BitVec.getElem_or]; interval_cases j <;> simp_all

theorem lt_and (x m : BitVec 64) (k : Nat) (h : m.toNat < 2 ^ k) : ((⟨x &&& m⟩ : U64)).val < 2 ^ k := by
  show (x &&& m).toNat < 2 ^ k
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right h

theorem lt_shr (x : BitVec 64) (k : Nat) (hk : k ≤ 64) : ((⟨x >>> k⟩ : U64)).val < 2 ^ (64 - k) := by
  show (x >>> k).toNat < _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
  rwa [show 64 - k + k = 64 by omega]

theorem lt_asidF (w0 w1 : BitVec 64) (sh : Nat) : ((⟨asidF w0 sh w1⟩ : U64)).val < 2 ^ 20 := by
  show (asidF w0 sh w1).toNat < 2 ^ 20
  unfold asidF
  rw [BitVec.toNat_or]
  apply Nat.or_lt_two_pow
  · rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
    have : ((w0 >>> sh).toNat &&& (0xf#64).toNat) < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · exact Nat.lt_of_lt_of_le (lt_shr w1 48 (by decide)) (by decide)

/-- Every cap `Cap::decode` produces fits its encoding. -/
theorem decodeF_encWf (w0 w1 : BitVec 64) : EncWf (decodeF w0 w1) := by
  have hp := unpackF_canonical w0
  unfold decodeF
  split
  case h_1 => exact ⟨hp, lt_and _ _ 6 (by decide)⟩
  case h_2 => exact hp
  case h_3 => exact hp
  case h_4 => exact hp
  case h_5 => exact ⟨hp, lt_and _ _ 6 (by decide), lt_shr _ 58 (by decide), lt_and _ _ 58 (by decide)⟩
  case h_6 => exact hp
  case h_7 => trivial
  case h_8 => trivial
  case h_9 => exact ⟨hp, lt_and _ _ 8 (by decide)⟩
  case h_10 => trivial
  case h_11 => exact ⟨hp, lt_and _ _ 6 (by decide)⟩
  case h_12 => trivial
  case h_13 => exact ⟨hp, lt_and _ _ 2 (by decide), lt_asidF _ _ _, lt_and _ _ 48 (by decide)⟩
  case h_14 => exact ⟨hp, lt_asidF _ _ _, lt_and _ _ 48 (by decide)⟩
  case h_15 => exact ⟨hp, lt_asidF _ _ _, lt_and _ _ 48 (by decide)⟩
  case h_16 => exact ⟨hp, lt_asidF _ _ _, lt_and _ _ 48 (by decide)⟩
  case h_17 => exact hp
  case h_18 => trivial
  case h_19 => exact hp
  case h_20 => exact hp
  case h_21 => exact ⟨hp, lt_and _ _ 6 (by decide), lt_asidF _ _ _, lt_and _ _ 48 (by decide)⟩
  case h_22 => trivial
  case h_23 =>
    refine ⟨lt_and _ _ 16 (by decide), lt_and _ _ 16 (by decide), ?_⟩
    split
    · left; intro j hj hj'; simp
    · exact hp
  case h_24 => trivial

theorem decode_encWf {w0 w1 : U64} {c : capability.Cap} (h : capability.Cap.decode w0 w1 = ok c) : EncWf c := by
  rw [decode_eq] at h
  have : decodeF w0.bv w1.bv = c := by simpa using h
  rw [← this]; exact decodeF_encWf _ _

end Fl4Proofs.P3
