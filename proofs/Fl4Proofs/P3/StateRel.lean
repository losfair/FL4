/-
P3 (DESIGN.md §9), CSpace: the part of the state relation that CSpace
lookup needs.

FL4's kernel memory is untyped: a `LawfulStore` view `mem : U64 → U64`
(P1/Store.lean). Which addresses are slots of which CNode is not visible in
memory; it is a property of the reachable states (P1's "well-typed heap"
invariant, not yet stated). Here it is a ghost map, `TypedHeap`, from
object pointers to the kind of object there, and the hypotheses on it are
explicit definitions:

* `CapValid th c` (l4v `valid_cap`, the part lookup needs): a CNode cap
  points at a CNode of its radix, which is not 0; a thread cap points at a
  TCB.
* `SlotsValid th mem`: every cap stored in a slot of a CNode or TCB of `th`
  is `CapValid` (l4v `valid_objs` / `caps_of_state_valid`).

The relation itself:

* `StateRel th mem σ`: every CNode of radix `r` in `th` is a `cnode r cs`
  in the spec's heap at the same pointer, well formed, and slot `idx`
  (a list of `r` bits) is the 32-byte slot at `ptr + 32 * of_bl idx` whose
  decoded cap is `CapRel`-related to `cs idx`; every TCB in `th` is a `tcb`
  in the spec's heap whose six cap slots (`tcb_cnode_map`) are related to
  FL4's six TCB slots (layout.rs `tcb::SLOT_*`, at `t + 32 * i`).

Pointers are the identity (`U64.bv`): FL4's object handles are kernel
virtual addresses and so are l4v `obj_ref`s.

The layout hypotheses writes need (`Placed`) are in Layout.lean, the CDT
part of the relation (`MdbLinks`, `CdtRel`) in Mdb.lean. Nothing here relates
the other objects or the scheduler state; that is for the later P3
subsystems.
-/
import Fl4Proofs.P3.CapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Slots -/

/-- Address of slot `i` of the object at `p` (`Slot::index`, `Tcb::slot`:
`p + i * cte::SIZE`, wrapping). -/
def slotAddr (p i : BitVec 64) : U64 := ⟨p + i * 32#64⟩

/-- The address of an abstract slot: CNode or TCB pointer and the slot
index as a bit list (big-endian, l4v `of_bl`). -/
def cslotAddr (sl : Fl4Spec.CslotPtr) : U64 := slotAddr sl.1 (Fl4Spec.ofBl sl.2)

/-- The cap stored in the slot at `a` (`Slot::cap`: words `a` and `a + 8`). -/
def capAt (mem : U64 → U64) (a : U64) : Result capability.Cap :=
  capability.Cap.decode (mem a) (mem (core.num.U64.wrapping_add a 8#u64))

/-- The slot at `a` holds a cap related to the abstract slot contents. -/
def SlotRel (mem : U64 → U64) (a : U64) (oc : Option Fl4Spec.Cap) : Prop :=
  ∃ c ac, capAt mem a = ok c ∧ oc = some ac ∧ CapRel c ac

/-! ## The typed heap (ghost) -/

/-- The kind of object at a pointer. Only CNodes and TCBs matter to CSpace;
the rest are `other` (with their size in bytes) until their subsystems are
related. -/
inductive ObjKind where
  | cnode (radix : Nat)
  | tcb
  | other (size : Nat)
deriving DecidableEq

/-- Ghost typed heap: which pointers are objects, and of which kind. -/
abbrev TypedHeap := U64 → Option ObjKind

/-- The size in bits of a frame of size `sz` (4 KiB, 2 MiB, 1 GiB). -/
def frameBitsN : capability.FrameSize → Nat
  | .Small => 12
  | .Large => 21
  | .Huge => 30

/-- Hypothesis: `c` points at an object of the right kind (l4v `valid_cap`
for CNode and thread caps; CNodes have radix at least 1, as seL4's retype
enforces, `untyped.rs`: `CapTable && user_size == 0` is rejected), and a
frame cap's frame is aligned to its size (l4v `cap_aligned`). -/
def CapValid (th : TypedHeap) : capability.Cap → Prop
  | .CNode p r _ _ => th p = some (.cnode r.val) ∧ r.val ≠ 0
  | .Thread p => th p = some .tcb
  | .Frame p sz _ _ _ _ _ _ => p.val % 2 ^ frameBitsN sz = 0
  | _ => True

/-- Number of cap slots of a TCB (layout.rs `tcb::SLOT_CTABLE` ..
`SLOT_EPT`; l4v `tcb_cnode_map`). -/
def tcbSlots : Nat := 6

/-- Hypothesis: every cap in a slot of a CNode or TCB is `CapValid`. -/
structure SlotsValid (th : TypedHeap) (mem : U64 → U64) : Prop where
  cnode : ∀ p r, th p = some (.cnode r) → ∀ i : Nat, i < 2 ^ r → ∀ c,
    capAt mem (slotAddr p.bv (BitVec.ofNat 64 i)) = ok c → CapValid th c
  tcb : ∀ t, th t = some .tcb → ∀ i : Nat, i < tcbSlots → ∀ c,
    capAt mem (slotAddr t.bv (BitVec.ofNat 64 i)) = ok c → CapValid th c

/-! ## The relation -/

/-- The CSpace part of the state relation between FL4 memory `mem` with
ghost typed heap `th` and the abstract state `σ`. -/
structure StateRel {Z : Type} (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Z) : Prop where
  cnode : ∀ p r, th p = some (.cnode r) → ∃ cs, σ.kheap p.bv = some (.cnode r cs) ∧
    Fl4Spec.wellFormedCnodeN r cs ∧
    ∀ idx : List Bool, idx.length = r → SlotRel mem (slotAddr p.bv (Fl4Spec.ofBl idx)) (cs idx)
  tcb : ∀ t, th t = some .tcb → ∃ tcb, σ.kheap t.bv = some (.tcb tcb) ∧
    ∀ i : Nat, i < tcbSlots →
      SlotRel mem (slotAddr t.bv (BitVec.ofNat 64 i)) (Fl4Spec.tcbCnodeMap tcb (Fl4Spec.tcbCnodeIndex i))

/-! ## Reading a related slot -/

theorem ofBl_bitsOf_eq (x n : Nat) :
    (Fl4Spec.ofBl (bitsOf x n) : BitVec 64) = BitVec.ofNat 64 (x % 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [ofBl_bitsOf, BitVec.toNat_ofNat]

/-- Slot `bitsOf v r` of a related CNode: the cap there is related to the
spec's, and valid. -/
theorem StateRel.cnode_slot {Z : Type} {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) {p : U64} {r : Nat} (hp : th p = some (.cnode r))
    (v : Nat) :
    ∃ cs c a, σ.kheap p.bv = some (.cnode r cs) ∧ Fl4Spec.wellFormedCnodeN r cs ∧ cs (bitsOf v r) = some a ∧
      capAt mem (slotAddr p.bv (BitVec.ofNat 64 (v % 2 ^ r))) = ok c ∧ CapRel c a ∧ CapValid th c := by
  obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p r hp
  obtain ⟨c, a, hc, ha, hca⟩ := hs (bitsOf v r) (by simp)
  rw [ofBl_bitsOf_eq] at hc
  exact ⟨cs, c, a, hk, hwf, ha, hc, hca, hV.cnode p r hp _ (Nat.mod_lt _ (by positivity)) c hc⟩

end

end Fl4Proofs.P3
