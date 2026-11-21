/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut1): **the untyped
free-region invariant of the spec** (spec side only, outside the JAtZ cone;
imports only Fl4Spec via SpecInvUtK).

`retype_region` writes its objects without looking at the heap and
`delete_objects` removes every object of a range, so every per-object
invariant (SpecGlob, FpuOwnOK, ctnq1's T1/T2) needs l4v's untyped facts. This
module states them over the cap state of SpecInvUtK (`uV`), so every function
of the generated frames SpecInvUtF1..F4 keeps them (`ik_utInv_of_uk`):

* `UtFree` (l4v `valid_untyped`'s object/usable-range clause, base-pointer
  form): no heap address lies in the free part `[base + freeIndex, base +
  2^bits)` of any untyped cap in any slot.
* `UtWf` (l4v `valid_cap` of an `UntypedCap`): `bits ≤ untyped_max_bits`, the
  base aligned to its size, `freeIndex ≤ 2^bits`.
* `UtDisj` (l4v `untyped_inc`'s usable-range clause): the free parts of two
  untyped caps in different slots are disjoint (a copy makes its source full,
  `set_untyped_cap_as_full`).
* `UtDesc` (l4v `untyped_inc`): untyped caps in different slots whose regions
  overlap are CDT ancestor and descendant, and the descendant's region misses
  the ancestor's free part. With `ensure_no_children` this makes a reset safe
  (`UtDesc.noKids`: a childless untyped's region meets no other free part).
* `UtOrig` (l4v `is_original_cap` of untyped caps, `cap_insert` /
  `is_cap_revocable`): every untyped cap is original, so its copies are its
  children.

Proved here: the view frame (`utInv_view`, `ik_utInv_of_uk`), boot
(`boot_utInv`: the initial state holds only null caps), and the two
consequences the per-object invariants need:
* (i) `retype_keeps_old` / `utRet_fresh` / `utRet_fresh_reset`: a retype at
  the region the decode chose (`UtRetOK`, the decode's checks; `utRet_region`
  the space accounting) writes only addresses that held no object, so every old
  object is kept;
* (ii) `deleteObjects_kheap` / `deleteObjects_range`: `delete_objects` of an
  untyped's region removes exactly the objects inside the region and keeps
  every other object (and the rest of the state but the memory).

FINDING (vacuity, not a counterexample): `initASt` holds no untyped cap (all
its caps are null, `init_capAt`), and no spec operation creates an untyped
cap except a retype from an untyped cap, so in Fl4Spec's reachable states
there is no untyped cap and every untyped invocation fails at the cap lookup.
The invariants are therefore stated and preserved for arbitrary states (the
boot lemma is the only place this matters); a boot state with untyped caps
(FL4's root task gets them) would need `UtInv` at that state.
-/
import Fl4Proofs.P3.SpecInvUtK
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- The bytes of an untyped region `[b, b + 2^n)`, as numbers. -/
def utR (b : ObjRef) (n : Nat) : Set Nat := {k | b.toNat ≤ k ∧ k < b.toNat + 2 ^ n}

/-- Its free part `[b + fi, b + 2^n)`. -/
def utFr (b : ObjRef) (n fi : Nat) : Set Nat := {k | b.toNat + fi ≤ k ∧ k < b.toNat + 2 ^ n}

/-- `UtFree` on the view. -/
def UtFreeV (w : UView) : Prop :=
  ∀ sl dev b n fi, w.2.1 sl = some (.untypedCap dev b n fi) → ∀ p, w.1 p = true → p.toNat ∉ utFr b n fi

/-- `UtWf` on the view. -/
def UtWfV (w : UView) : Prop :=
  ∀ sl dev b n fi, w.2.1 sl = some (.untypedCap dev b n fi) →
    n ≤ untypedMaxBits ∧ b.toNat % 2 ^ n = 0 ∧ fi ≤ 2 ^ n

/-- `UtDisj` on the view. -/
def UtDisjV (w : UView) : Prop :=
  ∀ s1 s2 d1 b1 n1 f1 d2 b2 n2 f2, s1 ≠ s2 →
    w.2.1 s1 = some (.untypedCap d1 b1 n1 f1) → w.2.1 s2 = some (.untypedCap d2 b2 n2 f2) →
    ∀ k, k ∈ utFr b1 n1 f1 → k ∉ utFr b2 n2 f2

/-- `UtDesc` on the view: two untyped caps in different slots whose regions
overlap are in the CDT ancestor relation, and the descendant's region misses the
ancestor's free part. -/
def UtDescV (w : UView) : Prop :=
  ∀ s1 s2 d1 b1 n1 f1 d2 b2 n2 f2, s1 ≠ s2 →
    w.2.1 s1 = some (.untypedCap d1 b1 n1 f1) → w.2.1 s2 = some (.untypedCap d2 b2 n2 f2) →
    (∃ k, k ∈ utR b1 n1 ∧ k ∈ utR b2 n2) →
    (s2 ∈ descendantsOf s1 w.2.2.1 ∧ ∀ k, k ∈ utR b2 n2 → k ∉ utFr b1 n1 f1) ∨
      (s1 ∈ descendantsOf s2 w.2.2.1 ∧ ∀ k, k ∈ utR b1 n1 → k ∉ utFr b2 n2 f2)

/-- `UtOrig` on the view. -/
def UtOrigV (w : UView) : Prop :=
  ∀ sl dev b n fi, w.2.1 sl = some (.untypedCap dev b n fi) → w.2.2.2 sl = true

/-- **UtFree [J]** (l4v `valid_untyped`: no object in an untyped cap's usable range). -/
abbrev UtFree (σ : State Unit) : Prop := UtFreeV (uV σ)
/-- **UtWf [J]** (l4v `valid_cap` of `UntypedCap`). -/
abbrev UtWf (σ : State Unit) : Prop := UtWfV (uV σ)
/-- **UtDisj [J]** (l4v `untyped_inc`, usable ranges). -/
abbrev UtDisj (σ : State Unit) : Prop := UtDisjV (uV σ)
/-- **UtDesc [J]** (l4v `untyped_inc`: overlapping untyped caps are nested in the CDT). -/
abbrev UtDesc (σ : State Unit) : Prop := UtDescV (uV σ)
/-- **UtOrig [J]** (l4v: untyped caps are original). -/
abbrev UtOrig (σ : State Unit) : Prop := UtOrigV (uV σ)

/-- The carried bundle. -/
def UtInvV (w : UView) : Prop := UtFreeV w ∧ UtWfV w ∧ UtDisjV w ∧ UtDescV w ∧ UtOrigV w

/-- **The untyped invariant** (the five facts above). -/
abbrev UtInv (σ : State Unit) : Prop := UtInvV (uV σ)

theorem utInv_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hI : UtInv σ) : UtInv σ' := by
  show UtInvV (uV σ'); rw [h]; exact hI

/-- A slot with no CDT child has no descendant. -/
theorem desc_noKids {t : Cdt} {s s' : CslotPtr} (h : ∀ c, t c ≠ some s) : s' ∉ descendantsOf s t := by
  intro hd
  have hd' : Relation.TransGen (parentOf t) s s' := hd
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 hd'
  exact h c hc

/-- **What a reset relies on**: if an untyped slot has no CDT child, no other
untyped cap's free part meets its region (UtDesc). -/
theorem UtDesc.noKids {σ : State Unit} (hD : UtDesc σ) {s1 : CslotPtr} {d1 : Bool} {b1 : ObjRef} {n1 f1 : Nat}
    (hc1 : capAt σ s1 = some (.untypedCap d1 b1 n1 f1)) (hk : ∀ c, σ.cdt c ≠ some s1) {s2 : CslotPtr}
    (hne : s1 ≠ s2) {d2 : Bool} {b2 : ObjRef} {n2 f2 : Nat} (hc2 : capAt σ s2 = some (.untypedCap d2 b2 n2 f2)) :
    ∀ k, k ∈ utR b1 n1 → k ∉ utFr b2 n2 f2 := by
  intro k hk1 hk2
  rcases hD s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 ⟨k, hk1, ⟨by have := hk2.1; omega, hk2.2⟩⟩ with
    ⟨hd, -⟩ | ⟨-, hr⟩
  · exact desc_noKids hk hd
  · exact hr k hk1 hk2

/-- Every function of the generated frames keeps the untyped invariant. -/
theorem ik_utInv_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK UtInv m :=
  ik_of_uk (fun _ _ e hI => utInv_view e hI) h

theorem ike_utInv_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE UtInv m :=
  ik_utInv_of_uk h

/-! ## Boot -/

theorem init_cv {p : ObjRef} {o : KernelObject} (hp : initKheap p = some o) {i : CnodeIndex} {c : Cap}
    (h : capView o i = some c) : c = .nullCap := by
  simp only [initKheap, Function.update_apply] at hp
  split_ifs at hp <;> (try cases hp)
  all_goals first
    | (cases h; done)
    | (simp only [capView, tcbCnodeMap, Function.update_apply] at h; split_ifs at h <;> (cases h; first | rfl | done))
    | (rw [capView_cnode] at h; split_ifs at h <;> (try simp only [emptyCnode] at h) <;> (try split_ifs at h) <;>
        (cases h; first | rfl | done))

/-- The initial state holds only null caps. -/
theorem init_capAt {sl : CslotPtr} {c : Cap} (h : capAt (initASt (Z := Unit)) sl = some c) : c = .nullCap := by
  obtain ⟨p, i⟩ := sl
  unfold capAt at h
  split at h
  · rename_i o ho; exact init_cv ho h
  · cases h

/-- **(d) boot**: the untyped invariant holds in the initial state (vacuously:
it has no untyped cap). -/
theorem boot_utInv : UtInv (initASt (Z := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sl _ _ _ _ hc; cases init_capAt hc
  · intro sl _ _ _ _ hc; cases init_capAt hc
  · intro s1 _ _ _ _ _ _ _ _ _ _ hc; cases init_capAt hc
  · intro s1 _ _ _ _ _ _ _ _ _ _ hc; cases init_capAt hc
  · intro sl _ _ _ _ hc; cases init_capAt hc

/-! ## Arithmetic -/

theorem pow2_word' {n : Nat} (hn : n < 64) : ((2 : Word) ^ n) = BitVec.ofNat 64 (2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_pow, BitVec.toNat_ofNat]
  have : (2 : BitVec 64).toNat = 2 := rfl
  rw [this]

/-- An aligned region does not wrap. -/
theorem fit_of_aligned {b : Word} {n : Nat} (hn : n ≤ 64) (h : b.toNat % 2 ^ n = 0) :
    b.toNat + 2 ^ n ≤ 2 ^ 64 := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
  have h64 : (2 : Nat) ^ 64 = 2 ^ n * 2 ^ (64 - n) := by rw [← Nat.pow_add]; congr 1; omega
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [hq] at hb ⊢; rw [h64] at hb ⊢
  have : q < 2 ^ (64 - n) := Nat.lt_of_mul_lt_mul_left hb
  calc 2 ^ n * q + 2 ^ n = 2 ^ n * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ 2 ^ n * 2 ^ (64 - n) := Nat.mul_le_mul_left _ this

theorem UtWf.fit {σ : State Unit} (hW : UtWf σ) {sl : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : capAt σ sl = some (.untypedCap dev b n fi)) : n < 64 ∧ b.toNat + 2 ^ n ≤ 2 ^ 64 := by
  obtain ⟨h1, h2, -⟩ := hW sl dev b n fi hc
  have : n < 64 := by unfold untypedMaxBits at h1; omega
  exact ⟨this, fit_of_aligned (by omega) h2⟩

/-- The byte range `delete_objects` removes. -/
def delR (ptr : Word) (bits : Nat) : Set ObjRef := {x | ptr ≤ x ∧ x ≤ ptr + 2 ^ bits - 1}

theorem mem_delR_iff {b : Word} {n : Nat} (hn : n < 64) (hfit : b.toNat + 2 ^ n ≤ 2 ^ 64) (p : Word) :
    p ∈ delR b n ↔ p.toNat ∈ utR b n := by
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hlt : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have hc : (b + 2 ^ n - 1).toNat = b.toNat + 2 ^ n - 1 := by
    rw [pow2_word' hn, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have e1 : (1 : Word).toNat = 1 := rfl
    rw [e1]
    rcases Nat.lt_or_ge (b.toNat + 2 ^ n) (2 ^ 64) with h | h
    · rw [Nat.mod_eq_of_lt h] <;> omega
    · have : b.toNat + 2 ^ n = 2 ^ 64 := by omega
      rw [this, Nat.mod_self] <;> omega
  simp only [delR, utR, Set.mem_setOf_eq, BitVec.le_def, hc]
  omega

/-! ## (ii) `delete_objects` -/

theorem deleteObjects_out {ptr : Word} {bits : Nat} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) ptr bits σ).1) :
    ∃ ms, y.2 = detype (delR ptr bits) { σ with machineState := ms } := by
  unfold deleteObjects at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : ∃ ms, z.2 = { σ with machineState := ms } :=
    ik_doMachineOp (P := fun τ => ∃ ms, τ = { σ with machineState := ms })
      (fun τ ms ⟨ms0, e⟩ => ⟨ms, by rw [e]⟩) _ σ ⟨σ.machineState, rfl⟩ z hz
  obtain ⟨ms, e⟩ := hz'
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact ⟨ms, by show detype _ z.2 = _; rw [e]; rfl⟩

/-- **(ii) `delete_objects` removes exactly the objects of its range.** -/
theorem deleteObjects_kheap {ptr : Word} {bits : Nat} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) ptr bits σ).1) :
    (∀ p, y.2.kheap p = if p ∈ delR ptr bits then none else σ.kheap p) ∧
      y.2.cdt = σ.cdt ∧ y.2.isOriginalCap = σ.isOriginalCap ∧ y.2.curDomain = σ.curDomain := by
  obtain ⟨ms, e⟩ := deleteObjects_out hy
  rw [e]; exact ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- **(ii) at an untyped cap's region** (UtWf): the removed objects are those at
the addresses of the region `[b, b + 2^n)`, every other object is kept. -/
theorem deleteObjects_range {σ τ : State Unit} (hW : UtWf τ) {sl : CslotPtr} {dev : Bool} {b : ObjRef}
    {n fi : Nat} (hc : capAt τ sl = some (.untypedCap dev b n fi)) {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) b n σ).1) :
    ∀ p, y.2.kheap p = if p.toNat ∈ utR b n then none else σ.kheap p := by
  obtain ⟨hn, hfit⟩ := hW.fit hc
  intro p
  rw [(deleteObjects_kheap hy).1 p]
  by_cases h : p.toNat ∈ utR b n
  · rw [if_pos ((mem_delR_iff hn hfit p).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((mem_delR_iff hn hfit p).1 h')), if_neg h]

/-- After `delete_objects` of the region no object lies in it. -/
theorem deleteObjects_empty {σ τ : State Unit} (hW : UtWf τ) {sl : CslotPtr} {dev : Bool} {b : ObjRef}
    {n fi : Nat} (hc : capAt τ sl = some (.untypedCap dev b n fi)) {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) b n σ).1) : ∀ p, p.toNat ∈ utR b n → y.2.kheap p = none := by
  intro p hp; rw [deleteObjects_range hW hc hy p, if_pos hp]

/-! ## (i) `retype_region` -/

/-- The addresses `retype_region` writes. -/
def retPtrs (rb : ObjRef) (n o : Nat) : List ObjRef := (List.range n).map fun k => ptrAdd rb (k * 2 ^ o)

theorem foldr_upd (ps : List ObjRef) (o : KernelObject) (kh : KHeap) (q : ObjRef) :
    (ps.foldr (fun p kh => Function.update kh p (some o)) kh) q = if q ∈ ps then some o else kh q := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    simp only [List.foldr_cons, List.mem_cons]
    by_cases e : q = a
    · subst e; simp
    · rw [Function.update_of_ne e, ih]; simp [e]

/-- The heap after `retype_region` writes `o` at `ps`. -/
def retKh (σ : State Unit) (ps : List ObjRef) (o : KernelObject) : KHeap :=
  fun q => if q ∈ ps then some o else σ.kheap q

/-- The outcome of `retype_region`. -/
theorem retypeRegionWith_out {bA : ApiObjectType → Nat → Nat} {rb : ObjRef} {n oB : Nat} {ty : ApiObjectType}
    {dev : Bool} {σ : State Unit} {y : List ObjRef × State Unit}
    (hy : y ∈ (retypeRegionWith (Z := Unit) bA rb n oB ty dev σ).1) :
    y.1 = retPtrs rb n (bA ty oB) ∧ (y.2 = σ ∨ (ty ≠ .untyped ∧
      y.2 = { σ with kheap := retKh σ (retPtrs rb n (bA ty oB)) (defaultObject ty dev oB σ.curDomain) })) := by
  unfold retypeRegionWith at hy
  obtain ⟨a1, h1, hy⟩ := hy; obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨a2, h2, hy⟩ := hy; obtain rfl := Set.mem_singleton_iff.1 h2
  obtain ⟨a3, h3, hy⟩ := hy; obtain rfl := Set.mem_singleton_iff.1 hy
  refine ⟨rfl, ?_⟩
  unfold NonDet.when at h3
  split at h3
  · rename_i hty
    right
    obtain ⟨b1, g1, h3⟩ := h3; obtain rfl := Set.mem_singleton_iff.1 g1
    obtain ⟨b2, g2, h3⟩ := h3; obtain rfl := Set.mem_singleton_iff.1 g2
    obtain ⟨b3, g3, h3⟩ := h3; obtain rfl := Set.mem_singleton_iff.1 g3
    obtain rfl := Set.mem_singleton_iff.1 h3
    refine ⟨hty, ?_⟩
    exact congrArg (fun kh => ({ σ with kheap := kh } : State Unit)) (funext fun q => foldr_upd _ _ _ q)
  · left; obtain rfl := Set.mem_singleton_iff.1 h3; rfl

/-- **The written addresses are fresh**: by UtFree, past the free index of an
untyped cap and inside its region no address holds an object. -/
theorem retPtrs_fresh {σ : State Unit} (hF : UtFree σ) {sl : CslotPtr} {dev : Bool} {b rb : ObjRef}
    {bits fi n o : Nat} (hc : capAt σ sl = some (.untypedCap dev b bits fi)) (hfit : b.toNat + 2 ^ bits ≤ 2 ^ 64)
    (h1 : b.toNat + fi ≤ rb.toNat) (h2 : rb.toNat + n * 2 ^ o ≤ b.toNat + 2 ^ bits) :
    ∀ q ∈ retPtrs rb n o, σ.kheap q = none := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
  have hk' := List.mem_range.1 hk
  have hkn : (k + 1) * 2 ^ o ≤ n * 2 ^ o := Nat.mul_le_mul_right _ hk'
  have e : (k + 1) * 2 ^ o = k * 2 ^ o + 2 ^ o := Nat.succ_mul k (2 ^ o)
  have hy := Nat.two_pow_pos o
  have htn : (ptrAdd rb (k * 2 ^ o)).toNat = rb.toNat + k * 2 ^ o := by
    unfold ptrAdd
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k * 2 ^ o < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  cases h : σ.kheap (ptrAdd rb (k * 2 ^ o)) with
  | none => rfl
  | some ob =>
    exfalso
    refine hF sl dev b bits fi hc _ (show (σ.kheap _).isSome = true by rw [h]; rfl) ?_
    show b.toNat + fi ≤ _ ∧ _ < _
    rw [htn]; omega

/-- **(i) `retype_region` at a free part keeps every old object.** -/
theorem retype_keeps_old {σ : State Unit} (hF : UtFree σ) {sl : CslotPtr} {dev : Bool} {b rb : ObjRef}
    {bits fi n oB : Nat} {bA : ApiObjectType → Nat → Nat} {ty : ApiObjectType} {dev' : Bool}
    (hc : capAt σ sl = some (.untypedCap dev b bits fi)) (hfit : b.toNat + 2 ^ bits ≤ 2 ^ 64)
    (h1 : b.toNat + fi ≤ rb.toNat) (h2 : rb.toNat + n * 2 ^ bA ty oB ≤ b.toNat + 2 ^ bits)
    {y : List ObjRef × State Unit} (hy : y ∈ (retypeRegionWith (Z := Unit) bA rb n oB ty dev' σ).1) :
    ∀ q, σ.kheap q ≠ none → y.2.kheap q = σ.kheap q := by
  intro q hq
  rcases (retypeRegionWith_out hy).2 with e | ⟨-, e⟩
  · rw [e]
  · rw [e]
    show retKh σ _ _ q = _
    unfold retKh
    rw [if_neg (fun hm => hq (retPtrs_fresh hF hc hfit h1 h2 q hm))]

/-! ## The region the decode chooses -/

/-- `align_up` on numbers (no wrap-around); UntypedRetype's `alignUp_toNat`
(copied: UntypedRetype is in the FL4 cone). -/
theorem ut_alignUp_toNat (x : BitVec 64) (z : Nat) (hz : z < 64) (hx : x.toNat + 2 ^ z ≤ 2 ^ 64) :
    (alignUp x z).toNat = (x.toNat + 2 ^ z - 1) / 2 ^ z * 2 ^ z := by
  have hpz : 2 ^ z < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hz
  have hp1 : 1 ≤ 2 ^ z := Nat.one_le_two_pow
  unfold alignUp
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
    · rw [Nat.mod_eq_of_lt h] <;> omega
    · have : x.toNat + 2 ^ z = 2 ^ 64 := by omega
      rw [this, Nat.mod_self] <;> omega
  rw [hy, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))]

/-- UntypedRetype's `region_nat` (copied). -/
theorem ut_region_nat (P F M k win : Nat) (sb z : Nat) (hM : M = 2 ^ sb) (hk : k = 2 ^ z)
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

/-- **The space accounting of the decode** (UntypedRetype's `retype_region`
over the spec's words): an untyped cap at `b` of size `2^sb`, aligned and not
wrapping, free index `F ≤ 2^sb`, and a window of `win ≥ 1` objects of size
`2^z` that the decode's `NotEnoughMemory` check accepted: the objects start at
the aligned free reference, past the free index, aligned, and end inside the
region. -/
theorem ut_region (d : Bool) (b : ObjRef) (F fi' sb z win : Nat) (hsb : sb < 64) (hz : z < 64)
    (hP : b.toNat % 2 ^ sb = 0) (hfit : b.toNat + 2 ^ sb ≤ 2 ^ 64) (hF : F ≤ 2 ^ sb) (hw1 : 1 ≤ win)
    (hw : win ≤ ((objSize (.untypedCap d b sb fi') - BitVec.ofNat 64 F) >>> z).toNat) :
    b.toNat + F ≤ (alignUp (getFreeRef b F) z).toNat ∧ (alignUp (getFreeRef b F) z).toNat % 2 ^ z = 0 ∧
      (alignUp (getFreeRef b F) z).toNat + win * 2 ^ z ≤ b.toNat + 2 ^ sb := by
  have hM : 2 ^ sb < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
  have hF64 : F < 2 ^ 64 := by omega
  have hfb : (objSize (.untypedCap d b sb fi') - BitVec.ofNat 64 F).toNat = 2 ^ sb - F := by
    show ((1 : Word) <<< sb - BitVec.ofNat 64 F).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have e1 : (1 : Word).toNat = 1 := rfl
    rw [e1, Nat.one_mul, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt hF64]
    omega
  rw [BitVec.toNat_ushiftRight, hfb, Nat.shiftRight_eq_div_pow] at hw
  obtain ⟨h1, h2, h3⟩ := ut_region_nat b.toNat F (2 ^ sb) (2 ^ z) win sb z rfl rfl hP hF hw1 hw
  have hwk : win * 2 ^ z ≤ 2 ^ sb - F :=
    le_trans (Nat.mul_le_mul_right _ hw) (Nat.div_mul_le_self _ _)
  have hk : 1 * 2 ^ z ≤ win * 2 ^ z := Nat.mul_le_mul_right _ hw1
  have hz1 : 1 ≤ 2 ^ z := Nat.one_le_two_pow
  have hx : (getFreeRef b F).toNat = b.toNat + F := by
    unfold getFreeRef
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt (by omega)]
  have hA := ut_alignUp_toNat (getFreeRef b F) z hz (by rw [hx]; omega)
  rw [hx] at hA
  rw [hA]
  exact ⟨h1, h2, h3⟩

/-- **The decode's checks on an untyped retype** (`decode_untyped_invocation`
with FL4's object sizes): the source slot holds an untyped cap `(dev, base,
bits, fi)`, the object size is at most `untyped_max_bits`, the window is
nonempty, the retype base is the aligned free reference (from free index 0 if
`reset`), the window fits in the free bytes (`NotEnoughMemory`), and a reset
slot has no CDT child (`ensure_no_children`). -/
def UtRetOK (σ : State Unit) : UntypedInvocation → Prop
  | .retype srcSlot reset base rb ty sz slots dev =>
    ∃ bits fi, capAt σ srcSlot = some (.untypedCap dev base bits fi) ∧
      fl4ObjBitsApi ty sz ≤ untypedMaxBits ∧ 1 ≤ slots.length ∧
      rb = alignUp (getFreeRef base (if reset then 0 else fi)) (fl4ObjBitsApi ty sz) ∧
      slots.length ≤ ((objSize (.untypedCap dev base bits fi) -
        BitVec.ofNat 64 (if reset then 0 else fi)) >>> fl4ObjBitsApi ty sz).toNat ∧
      (reset = true → ∀ c, σ.cdt c ≠ some srcSlot)

/-- `UtRetOK` reads only the view. -/
theorem utRetOK_view {σ σ' : State Unit} (h : uV σ' = uV σ) {ui : UntypedInvocation} (hok : UtRetOK σ ui) :
    UtRetOK σ' ui := by
  cases ui with
  | retype srcSlot reset base rb ty sz slots dev =>
    obtain ⟨bits, fi, hc, h1⟩ := hok
    have hcap : capAt σ' = capAt σ := congrArg (fun w : UView => w.2.1) h
    have hcdt : σ'.cdt = σ.cdt := congrArg (fun w : UView => w.2.2.1) h
    refine ⟨bits, fi, by rw [hcap]; exact hc, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun hr c => ?_⟩
    rw [hcdt]; exact h1.2.2.2.2 hr c

/-- **The region of a decoded retype** (UtWf + `UtRetOK`). -/
theorem utRet_region {σ : State Unit} (hW : UtWf σ) {srcSlot : CslotPtr} {reset : Bool} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype srcSlot reset base rb ty sz slots dev)) :
    ∃ bits fi, capAt σ srcSlot = some (.untypedCap dev base bits fi) ∧ base.toNat + 2 ^ bits ≤ 2 ^ 64 ∧
      base.toNat + (if reset then 0 else fi) ≤ rb.toNat ∧ rb.toNat % 2 ^ fl4ObjBitsApi ty sz = 0 ∧
      rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz ≤ base.toNat + 2 ^ bits := by
  obtain ⟨bits, fi, hc, ho, hw1, hrb, hw, -⟩ := hok
  obtain ⟨hn, hfit⟩ := hW.fit hc
  obtain ⟨-, hal, hfi⟩ := hW srcSlot dev base bits fi hc
  have hz : fl4ObjBitsApi ty sz < 64 := by unfold untypedMaxBits at ho; omega
  have hF : (if reset then 0 else fi) ≤ 2 ^ bits := by split <;> omega
  obtain ⟨h1, h2, h3⟩ := ut_region dev base _ fi bits _ _ hn hz hal hfit hF hw1 hw
  rw [← hrb] at h1 h2 h3
  exact ⟨bits, fi, hc, hfit, h1, h2, h3⟩

/-- **(i) at the decode's region, no reset**: every address the retype writes
held no object (UtFree). -/
theorem utRet_fresh {σ : State Unit} (hI : UtInv σ) {srcSlot : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype srcSlot false base rb ty sz slots dev)) :
    ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none := by
  obtain ⟨bits, fi, hc, hfit, h1, -, h3⟩ := utRet_region hI.2.1 hok
  exact retPtrs_fresh hI.1 hc hfit h1 h3

/-- **(i) at the decode's region, after a reset**: once the region holds no
object (`deleteObjects_empty`, or UtFree with free index 0), every address the
retype writes held no object. -/
theorem utRet_fresh_reset {σ τ : State Unit} (hW : UtWf σ) {srcSlot : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype srcSlot true base rb ty sz slots dev)) {bits fi : Nat}
    (hc : capAt σ srcSlot = some (.untypedCap dev base bits fi))
    (hE : ∀ q, q.toNat ∈ utR base bits → τ.kheap q = none) :
    ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), τ.kheap q = none := by
  obtain ⟨bits', fi', hc', hfit, h1, -, h3⟩ := utRet_region hW hok
  rw [hc] at hc'; cases hc'
  intro q hq
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
  have hk' := List.mem_range.1 hk
  have hkn : (k + 1) * 2 ^ fl4ObjBitsApi ty sz ≤ slots.length * 2 ^ fl4ObjBitsApi ty sz :=
    Nat.mul_le_mul_right _ hk'
  have e : (k + 1) * 2 ^ fl4ObjBitsApi ty sz = k * 2 ^ fl4ObjBitsApi ty sz + 2 ^ fl4ObjBitsApi ty sz :=
    Nat.succ_mul _ _
  have hy := Nat.two_pow_pos (fl4ObjBitsApi ty sz)
  simp only [if_true] at h1
  apply hE
  unfold ptrAdd
  show base.toNat ≤ _ ∧ _ < _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k * 2 ^ fl4ObjBitsApi ty sz < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

end

end Fl4Proofs.P3.SInvU
