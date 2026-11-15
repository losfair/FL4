/-
P3 (DESIGN.md §9), CSpace: the cap transformations of the CNode Copy, Mint,
Move and Mutate invocations against the spec's.

* `Rights::from_word` is l4v `data_to_rights` (`rightsW_spec`);
* `mask_cap_rights` is l4v `mask_cap` (`mask_rel`), and `mask_cap` with all
  rights is the identity on related caps (`maskCap_all`);
* `update_cap_data` is l4v `update_cap_data` (`update_rel`): badges for
  unbadged endpoint and notification caps (`badge_bits = 64`, so the spec's
  mask is the identity), guard and guard size for CNode caps
  (`cnode_padding_bits = 0`, so the spec's guard is the next 58 bits);
* `derive_cap` is l4v `derive_cap` (`derive_rel`), for an untyped cap
  under the explicit hypothesis that FL4's `ensure_no_children` decides
  the spec's `∃ c, cdt c = some slot` (`NoChildrenRel`).

Each FL4 result is also shown to stay `CapWf`, `EncWf` and `CapValid`, and
to be of the source's badge kind (`SameBadgeKind`), as `insert_refines`
needs.
-/
import Fl4Proofs.P3.InsertRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Rights -/

/-- `Rights::from_word w`. -/
def rightsW (w : U64) : capability.Rights :=
  { write := (w &&& 1#u64) != 0#u64, read := (w &&& 2#u64) != 0#u64,
    grant := (w &&& 4#u64) != 0#u64, grant_reply := (w &&& 8#u64) != 0#u64 }

theorem from_word_eq (w : U64) : capability.Rights.from_word w = ok (rightsW w) := by
  simp [capability.Rights.from_word, rightsW, lift]

theorem and_pow_ne (w : U64) (k : Nat) (hk : k < 64) (c : U64) (hc : c.bv = BitVec.twoPow 64 k) :
    ((w &&& c) != 0#u64) = w.bv.getLsbD k := by
  have : (w &&& c).bv = w.bv &&& BitVec.twoPow 64 k := by rw [← hc]; rfl
  have h2 : BitVec.twoPow 64 k ≠ 0#64 := by
    intro h; have := congrArg (fun x => x.getLsbD k) h
    simp only [BitVec.getLsbD_twoPow, BitVec.getLsbD_zero] at this
    simp [hk] at this
  rw [BitVec.and_twoPow] at this
  cases hb : w.bv.getLsbD k
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at this
    simp [bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq, this]
  · simp only [hb, ↓reduceIte] at this
    have h3 : (w &&& c) ≠ 0#u64 := by
      intro e; rw [UScalar.eq_equiv_bv_eq, this] at e; exact h2 e
    simpa [bne_iff_ne] using h3

theorem rightsW_write (w : U64) : (rightsW w).write = w.bv.getLsbD 0 := and_pow_ne w 0 (by decide) _ (by decide)
theorem rightsW_read (w : U64) : (rightsW w).read = w.bv.getLsbD 1 := and_pow_ne w 1 (by decide) _ (by decide)
theorem rightsW_grant (w : U64) : (rightsW w).grant = w.bv.getLsbD 2 := and_pow_ne w 2 (by decide) _ (by decide)
theorem rightsW_grant_reply (w : U64) : (rightsW w).grant_reply = w.bv.getLsbD 3 :=
  and_pow_ne w 3 (by decide) _ (by decide)

/-- `data_to_rights` of a word: its low four bits. -/
theorem dataToRights_eq (w : BitVec 64) :
    Fl4Spec.dataToRights w = rightsOf (w.getLsbD 0) (w.getLsbD 1) (w.getLsbD 2) (w.getLsbD 3) := by
  ext x; cases x <;> simp [Fl4Spec.dataToRights, rightsOf, Fl4Spec.dataTo16, BitVec.getLsbD_setWidth]

theorem rightsW_spec (w : U64) :
    rightsOf (rightsW w).write (rightsW w).read (rightsW w).grant (rightsW w).grant_reply =
      Fl4Spec.dataToRights w.bv := by
  rw [dataToRights_eq, rightsW_write, rightsW_read, rightsW_grant, rightsW_grant_reply]

/-! ## `mask_cap_rights` -/

theorem rightsOf_inter (a b c d a' b' c' d' : Bool) :
    rightsOf a b c d ∩ rightsOf a' b' c' d' = rightsOf (a && a') (b && b') (c && c') (d && d') := by
  ext x; cases x <;> simp [rightsOf]

theorem rightsOf_ntfn (a b c d : Bool) :
    rightsOf a b c d \ {.allowGrant, .allowGrantReply} = rightsOf a b false false := by
  ext x; cases x <;> simp [rightsOf]

theorem replyRights_mask (g a b c d : Bool) :
    (replyRights g ∩ rightsOf a b c d) \ {.allowRead, .allowGrantReply} ∪ {.allowWrite} = replyRights (g && c) := by
  ext x; cases g <;> cases c <;> cases x <;> simp [replyRights, rightsOf]

theorem vm_mask (v : U64) (hv : 1 ≤ v.val ∧ v.val ≤ 3) (r : capability.Rights) :
    ∃ m, capability.mask_vm_rights v r = ok m ∧ 1 ≤ m.val ∧ m.val ≤ 3 ∧
      vmRightsOf m = Fl4Spec.validateVmRights (vmRightsOf v ∩ rightsOf r.write r.read r.grant r.grant_reply) := by
  have h3 : v.val = 1 ∨ v.val = 2 ∨ v.val = 3 := by omega
  have e1 : capability.VM_KERNEL_ONLY = 1#u64 := by simp [capability.VM_KERNEL_ONLY]
  have e2 : capability.VM_READ_ONLY = 2#u64 := by simp [capability.VM_READ_ONLY]
  have e3 : capability.VM_READ_WRITE = 3#u64 := by simp [capability.VM_READ_WRITE]
  have hv' : v = 1#u64 ∨ v = 2#u64 ∨ v = 3#u64 := by
    rcases h3 with h | h | h <;> [left; (right; left); (right; right)] <;> (apply UScalar.eq_of_val_eq; simpa using h)
  unfold capability.mask_vm_rights
  rw [e1, e2, e3]
  rcases hv' with rfl | rfl | rfl <;> cases hr : r.read <;> cases hw : r.write <;>
    simp [vmRightsOf, Fl4Spec.validateVmRights, Fl4Spec.vmReadWrite, Fl4Spec.vmReadOnly,
      Fl4Spec.vmKernelOnly, rightsOf, hr, hw]

theorem SameBadgeKind.trans {a b c : capability.Cap} (h1 : SameBadgeKind a b) (h2 : SameBadgeKind b c) :
    SameBadgeKind a c := by
  cases a <;> cases b <;> cases c <;> simp_all [SameBadgeKind]

/-- `mask_cap_rights r` is l4v `mask_cap` with the rights of `r`. -/
theorem mask_rel (r : capability.Rights) (c : capability.Cap) (hc : CapWf c) :
    ∃ c', capability.mask_cap_rights r c = ok c' ∧ CapWf c' ∧
      absCap c' = Fl4Spec.maskCap (rightsOf r.write r.read r.grant r.grant_reply) (absCap c) ∧
      (EncWf c → EncWf c') ∧ (∀ th, CapValid th c → CapValid th c') ∧ SameBadgeKind c' c ∧
      (c' = .Null ↔ c = .Null) := by
  cases c
  case Frame p sz v dev m ept asid va =>
    obtain ⟨mv, hm, h1, h2, hmv⟩ := vm_mask v hc r
    refine ⟨.Frame p sz mv dev m ept asid va, by simp [capability.mask_cap_rights, hm],
      (show 1 ≤ mv.val ∧ mv.val ≤ 3 from ⟨h1, h2⟩), ?_, ?_, fun _ h => h, trivial, by simp⟩
    · simp [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, Fl4Spec.acapRightsUpdate,
        Fl4Spec.ArchCap.acapRights, hmv]
    · simp only [EncWf]; intro ⟨a, b, c, d⟩; exact ⟨a, by omega, c, d⟩
  case Endpoint p b s rc g gr =>
    refine ⟨.Endpoint p b (s && r.write) (rc && r.read) (g && r.grant) (gr && r.grant_reply), ?_, trivial, ?_,
      fun h => h, fun _ h => h, trivial, by simp⟩
    · cases s <;> cases rc <;> cases g <;> cases gr <;> simp [capability.mask_cap_rights]
    · simp [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, rightsOf_inter]
  case Notification p b s rc =>
    refine ⟨.Notification p b (s && r.write) (rc && r.read), ?_, trivial, ?_,
      fun h => h, fun _ h => h, trivial, by simp⟩
    · cases s <;> cases rc <;> simp [capability.mask_cap_rights]
    · simp [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, rightsOf_inter, rightsOf_ntfn]
  case Reply p g =>
    refine ⟨.Reply p (g && r.grant), ?_, trivial, ?_, fun h => h, fun _ h => h, trivial, by simp⟩
    · cases g <;> simp [capability.mask_cap_rights]
    · simp only [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, replyRights_mask]
  all_goals
    refine ⟨_, rfl, hc, ?_, fun h => h, fun _ h => h, by simp [SameBadgeKind], Iff.rfl⟩
    simp [absCap, Fl4Spec.maskCap, Fl4Spec.capRightsUpdate, Fl4Spec.acapRightsUpdate]

/-- With all rights, `mask_cap` leaves a related cap alone (Move, Mutate). -/
theorem maskCap_all (c : capability.Cap) (hc : CapWf c) :
    Fl4Spec.maskCap Fl4Spec.allRights (absCap c) = absCap c := by
  cases c
  case Frame p sz v dev m ept asid va =>
    have h3 : v.val = 1 ∨ v.val = 2 ∨ v.val = 3 := by simp only [CapWf] at hc; omega
    simp only [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, Fl4Spec.acapRightsUpdate,
      Fl4Spec.ArchCap.acapRights, Fl4Spec.allRights, Set.inter_univ]
    rcases h3 with h | h | h <;>
      simp [vmRightsOf, h, Fl4Spec.validateVmRights, Fl4Spec.vmReadWrite, Fl4Spec.vmReadOnly, Fl4Spec.vmKernelOnly]
  case Notification p b s r =>
    simp only [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, Fl4Spec.allRights,
      Set.inter_univ, rightsOf_ntfn]
  case Reply p g =>
    simp only [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, Fl4Spec.allRights,
      Set.inter_univ]
    congr 1; ext x; cases g <;> cases x <;> simp [replyRights]
  all_goals simp [absCap, Fl4Spec.maskCap, Fl4Spec.capRights, Fl4Spec.capRightsUpdate, Fl4Spec.acapRightsUpdate,
    Fl4Spec.allRights]

/-! ## `update_cap_data` -/

theorem objects_mask_eq (b : U64) : objects.mask b = cspace.mask b := rfl

theorem cap_is_null_null : capability.Cap.is_null .Null = ok true := rfl
theorem cap_is_null_ne {c : capability.Cap} (h : c ≠ .Null) : capability.Cap.is_null c = ok false := by
  cases c <;> simp_all <;> rfl

theorem spec_exists {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem spec_mask_and (x : BitVec 64) (n : Nat) (hn : n < 64) :
    (x &&& (Fl4Spec.mask n : BitVec 64)).toNat = x.toNat % 2 ^ n := by
  have hp : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have hm : (Fl4Spec.mask n : BitVec 64).toNat = 2 ^ n - 1 := by
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [Fl4Spec.mask]
    rw [BitVec.toNat_sub, Nat.one_shiftLeft]
    simp; omega
  rw [BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem spec_mask_64 (x : BitVec 64) : x &&& (Fl4Spec.mask 64 : BitVec 64) = x := by
  have : (Fl4Spec.mask 64 : BitVec 64) = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.mask]
  rw [this, BitVec.and_allOnes]

/-- The spec's `update_cap_data` on a CNode cap: guard size the low 6 bits
of the word, guard the next bits (`cnode_padding_bits = 0`). -/
theorem update_cnode_spec (pr : Bool) (w : U64) (p : BitVec 64) (r : Nat) (gd : List Bool) :
    Fl4Spec.updateCapData pr w.bv (.cnodeCap p r gd) =
      if w.val % 64 + r > 64 then .nullCap else .cnodeCap p r (bitsOf (w.val / 64) (w.val % 64)) := by
  have hsG : ((w.bv >>> 0) &&& (Fl4Spec.mask 6 : BitVec 64)).toNat = w.val % 64 := by
    rw [spec_mask_and _ _ (by decide)]; simp
  have h58 : ((w.bv >>> 6) &&& (Fl4Spec.mask 58 : BitVec 64)).toNat = w.val / 64 := by
    rw [spec_mask_and _ _ (by decide), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    apply Nat.mod_eq_of_lt
    have := w.hBounds; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at this ⊢; omega
  simp only [Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap, Fl4Spec.isCnodeCap,
    Fl4Spec.theCnodeCap, Fl4Spec.updateCnodeCapData, Fl4Spec.cnodePaddingBits, Fl4Spec.cnodeGuardSizeBits,
    Fl4Spec.wordBits, Fl4Spec.unat, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, hsG]
  have hl : w.val % 64 ≤ 64 := by omega
  rw [toBl_drop _ _ hl, h58]

/-- `update_cap_data preserve w` is l4v `update_cap_data preserve w`. -/
theorem update_rel (pr : Bool) (w : U64) (c : capability.Cap) (hc : CapWf c) (he : EncWf c) :
    ∃ c', objects.update_cap_data pr w c = ok c' ∧ CapWf c' ∧
      absCap c' = Fl4Spec.updateCapData pr w.bv (absCap c) ∧ EncWf c' ∧
      (∀ th, CapValid th c → CapValid th c') ∧ SameBadgeKind c' c := by
  cases c
  case Endpoint p b s r g gr =>
    by_cases hp : pr
    · subst hp
      exact ⟨.Null, rfl, trivial, by simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap], trivial,
        fun _ _ => trivial, trivial⟩
    · by_cases hb : b = 0#u64
      · refine ⟨.Endpoint p w s r g gr, by simp [objects.update_cap_data, hp, hb], trivial, ?_, he,
          fun _ h => h, trivial⟩
        have : b.bv = 0#64 := by rw [hb]; rfl
        simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.capEpBadge, Fl4Spec.badgeUpdate,
          this, hp, Fl4Spec.badgeBits, spec_mask_64]
      · refine ⟨.Null, by simp [objects.update_cap_data, hp, hb], trivial, ?_, trivial, fun _ _ => trivial, trivial⟩
        have : b.bv ≠ 0#64 := by intro e; exact hb (UScalar.eq_of_val_eq (by simpa using congrArg BitVec.toNat e))
        simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.capEpBadge, this]
  case Notification p b s r =>
    by_cases hp : pr
    · subst hp
      exact ⟨.Null, rfl, trivial, by simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap],
        trivial, fun _ _ => trivial, trivial⟩
    · by_cases hb : b = 0#u64
      · refine ⟨.Notification p w s r, by simp [objects.update_cap_data, hp, hb], trivial, ?_, he,
          fun _ h => h, trivial⟩
        have : b.bv = 0#64 := by rw [hb]; rfl
        simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap, Fl4Spec.capEpBadge,
          Fl4Spec.badgeUpdate, this, hp, Fl4Spec.badgeBits, spec_mask_64]
      · refine ⟨.Null, by simp [objects.update_cap_data, hp, hb], trivial, ?_, trivial, fun _ _ => trivial, trivial⟩
        have : b.bv ≠ 0#64 := by intro e; exact hb (UScalar.eq_of_val_eq (by simpa using congrArg BitVec.toNat e))
        simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap, Fl4Spec.capEpBadge, this]
  case CNode ptr radix gs g =>
    obtain ⟨hr, hgs, hg⟩ := hc
    obtain ⟨hcan, -, -, hg58⟩ := he
    have hG : (w &&& 63#u64).val = w.val % 64 := by
      simp; exact Nat.and_two_pow_sub_one_eq_mod w.val 6
    have hGl : (w &&& 63#u64).val < 64 := by rw [hG]; omega
    have hsum : (core.num.U64.wrapping_add (w &&& 63#u64) radix).val = w.val % 64 + radix.val := by
      rw [core.num.U64.wrapping_add_val_eq, hG]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hspec := update_cnode_spec pr w ptr.bv radix.val (bitsOf g.val gs.val)
    unfold objects.update_cap_data
    simp only [lift, bind_ok, absCap]
    rw [hspec]
    by_cases hgt : w.val % 64 + radix.val > 64
    · have : core.num.U64.wrapping_add (w &&& 63#u64) radix > 64#u64 := by scalar_tac
      simp only [this, ↓reduceIte, hgt]
      exact ⟨.Null, rfl, trivial, rfl, trivial, fun _ _ => trivial, trivial⟩
    · have : ¬ core.num.U64.wrapping_add (w &&& 63#u64) radix > 64#u64 := by scalar_tac
      simp only [this, ↓reduceIte, hgt]
      rw [shr_eq _ _ (by decide) (by decide), objects_mask_eq]
      simp only [bind_ok]
      obtain ⟨m, hm1, hm2⟩ := spec_exists (mask_spec (w &&& 63#u64) hGl)
      rw [hm1]; simp only [bind_ok]
      have hgv : ((⟨w.bv >>> 6⟩ : U64) &&& m).val = (w.val / 64) % 2 ^ (w.val % 64) := by
        have : ((⟨w.bv >>> 6⟩ : U64) &&& m).val = (w.bv >>> 6).toNat &&& m.val := by
          show ((w.bv >>> 6) &&& m.bv).toNat = _
          rw [BitVec.toNat_and]; rfl
        rw [this, hm2, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hG]
        simp
      refine ⟨.CNode ptr radix (w &&& 63#u64) (⟨w.bv >>> 6⟩ &&& m), rfl, ⟨hr, hGl, ?_⟩, ?_, ⟨hcan, hr, hGl, ?_⟩,
        fun _ h => h, trivial⟩
      · rw [hgv, hG]; exact Nat.mod_lt _ (by positivity)
      · simp only [absCap, hgv, hG, bitsOf_mod]
      · rw [hgv]
        have := w.hBounds; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at this
        have : w.val / 64 < 2 ^ 58 := by omega
        exact lt_of_le_of_lt (Nat.mod_le _ _) this
  all_goals
    refine ⟨_, rfl, hc, ?_, he, fun _ h => h, by simp [SameBadgeKind]⟩
    simp [absCap, Fl4Spec.updateCapData, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap, Fl4Spec.isCnodeCap,
      Fl4Spec.isArchCap, Fl4Spec.archUpdateCapData, Fl4Spec.Cap.theArchCap]

/-! ## Spec monad steps -/

section
variable {σ ε α : Type}

@[simp] theorem run_returnOk (a : α) (s : σ) :
    (Fl4Spec.NonDetE.returnOk a : Fl4Spec.NonDetE σ ε α).run s = ({(.ok a, s)}, False) := rfl

@[simp] theorem run_throwError (e : ε) (s : σ) :
    (Fl4Spec.NonDetE.throwError e : Fl4Spec.NonDetE σ ε α).run s = ({(.error e, s)}, False) := rfl

end

/-! ## `derive_cap` -/

/-- FL4's `derive_cap` outcome against the spec's: a related cap that keeps
the properties `insert_refines` needs, or a related error. -/
def DeriveRel (c : capability.Cap) : core.result.Result capability.Cap error.Exc →
    Except Fl4Spec.SyscallError Fl4Spec.Cap → Prop
  | .Ok c', .ok a => CapWf c' ∧ absCap c' = a ∧ EncWf c' ∧ (∀ th, CapValid th c → CapValid th c') ∧
      SameBadgeKind c' c
  | .Err e, .error e' => SysErrRel e e'
  | _, _ => False

section
variable {Z : Type} [Fl4Spec.StateExt Z] {S : Type} {st : machine.Store S}

/-- Hypothesis (an MDB invariant, not proved here): at slot `slot`, FL4's
`ensure_no_children` (a non-null `next` that `is_mdb_parent_of` the slot)
decides whether the spec's `cdt` has a child of `sl`. -/
def NoChildrenRel (s : S) (σ : Fl4Spec.State Z) (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) : Prop :=
  cdt.ensure_no_children st s slot =
    ok (if ∃ x, σ.cdt x = some sl then .Err (.Sys .RevokeFirst) else .Ok ())

theorem ensureNoChildren_run (σ : Fl4Spec.State Z) (sl : Fl4Spec.CslotPtr) :
    (Fl4Spec.ensureNoChildren (Z := Z) sl).run σ =
      ({(if ∃ x, σ.cdt x = some sl then .error .revokeFirst else .ok (), σ)}, False) := by
  unfold Fl4Spec.ensureNoChildren
  rw [run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Z => s.cdt) (s := σ) rfl)]
  by_cases h : ∃ x, σ.cdt x = some sl
  · simp only [Fl4Spec.NonDetE.whenE, h, ↓reduceIte]; rfl
  · simp only [Fl4Spec.NonDetE.whenE, h, ↓reduceIte]; rfl

/-- `derive_cap` is l4v `derive_cap`; for an untyped cap under
`NoChildrenRel`. Neither changes the state. -/
theorem derive_rel (s : S) (σ : Fl4Spec.State Z) (slot : obj.Slot) (sl : Fl4Spec.CslotPtr)
    (c : capability.Cap) (hc : CapWf c) (he : EncWf c)
    (hnc : (match c with | .Untyped .. => True | _ => False) → NoChildrenRel (st := st) s σ slot sl) :
    ∃ r, objects.derive_cap st s slot c = ok r ∧ ∃ r',
      (Fl4Spec.deriveCap (Z := Z) sl (absCap c)).run σ = ({(r', σ)}, False) ∧ DeriveRel c r r' := by
  cases c
  case Untyped p sb fi dev =>
    have h := hnc trivial
    unfold objects.derive_cap
    rw [h]
    simp only [bind_ok, absCap, Fl4Spec.deriveCap]
    rw [ExceptT.run_bind, nd_bind_single (ensureNoChildren_run σ sl)]
    by_cases hx : ∃ x, σ.cdt x = some sl
    · simp only [hx, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from]
      exact ⟨.Err (.Sys .RevokeFirst), by simp, _, rfl, show SysErrRel (.Sys .RevokeFirst) .revokeFirst from trivial⟩
    · simp only [hx, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, trivial⟩
  case Frame p sz v dev m ept asid va =>
    refine ⟨_, rfl, _, rfl, ?_⟩
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨hcan, hv, -, -⟩ := he
    refine ⟨⟨h1, h2⟩, ?_, ⟨hcan, hv, by simp, by simp⟩, fun _ h => h, trivial⟩
    simp [absCap]
  case PageTable p m asid va =>
    cases m
    · exact ⟨_, rfl, _, rfl, trivial⟩
    · exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, trivial⟩
  case PageDirectory p m asid va =>
    cases m
    · exact ⟨_, rfl, _, rfl, trivial⟩
    · exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, trivial⟩
  case Pdpt p m asid va =>
    cases m
    · exact ⟨_, rfl, _, rfl, trivial⟩
    · exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, trivial⟩
  case Pml4 p m asid =>
    cases m
    · exact ⟨_, rfl, _, rfl, trivial⟩
    · exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, trivial⟩
  case Ept p level m asid va =>
    cases m
    · exact ⟨_, rfl, _, rfl, trivial⟩
    · exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, trivial⟩
  case IrqControl => exact ⟨_, rfl, _, rfl, trivial, rfl, trivial, fun _ _ => trivial, trivial⟩
  case Zombie => exact ⟨_, rfl, _, rfl, trivial, rfl, trivial, fun _ _ => trivial, trivial⟩
  case IoPortControl => exact ⟨_, rfl, _, rfl, trivial, rfl, trivial, fun _ _ => trivial, trivial⟩
  all_goals exact ⟨_, rfl, _, rfl, hc, rfl, he, fun _ h => h, by simp [SameBadgeKind]⟩

end

end

end Fl4Proofs.P3
