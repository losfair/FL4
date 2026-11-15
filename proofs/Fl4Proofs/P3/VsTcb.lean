/-
P3 (DESIGN.md §9), VSpace: **the VSpace side of the TCB invocations**.

* `is_valid_vtable_root_eq`: FL4's vtable check (`decode_set_space`,
  `decode_tcb_configure`) is l4v's `is_valid_vtable_root` of the related cap;
* `check_valid_ipc_buffer_rel`: FL4's IPC-buffer check (`derive_for_buffer`)
  against l4v `check_valid_ipc_buffer` (the same error, or success);
  `msg_align_bits` is 10, FL4's `IPC_BUFFER` bits;
* the address-space switch after a vtable change: `set_vm_root` (VsRoot,
  VsDelRoot) needs the thread's mapped vtable cap to have a non-zero ASID
  (`CurOK`; l4v `valid_cap`). `MappedAsid` states it for every slot of the
  typed heap; it gives `CurOK` for any thread of the heap (`curOK_of`), and
  is kept by `set_cap` and `cdt::insert` of a cap that satisfies it
  (`MappedAsid.set_cap`, `MappedAsid.insert`), and `derive_cap` keeps it
  (`derive_mapOk`).
-/
import Fl4Proofs.P3.VsDelRoot
import Fl4Proofs.P3.VsFrameMapRel
import Fl4Proofs.P3.UntypedSuccess
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

/-! ## The vtable check -/

theorem is_valid_vtable_root_eq (c : capability.Cap) :
    vspace.is_valid_vtable_root c = ok (decide (Fl4Spec.isValidVtableRoot (absCap c))) := by
  cases c <;> simp [vspace.is_valid_vtable_root, absCap, Fl4Spec.isValidVtableRoot]
  case Pml4 p b asid => cases b <;> simp

/-! ## The IPC-buffer check -/

theorem msgAlignBits_eq : Fl4Spec.msgAlignBits = 10 := by
  unfold Fl4Spec.msgAlignBits
  have h : Nat.find (⟨7, by decide⟩ : ∃ n, Fl4Spec.maxIpcLength ≤ 2 ^ n) = 7 := by
    rw [Nat.find_eq_iff]
    refine ⟨by decide, fun n hn => ?_⟩
    interval_cases n <;> decide
  rw [h]; rfl

theorem isAligned10_iff (v : U64) : Fl4Spec.isAligned v.bv 10 ↔ (v &&& 1023#u64) = 0#u64 := by
  unfold Fl4Spec.isAligned
  constructor
  · intro h
    apply UScalar.eq_of_val_eq
    show (v.bv &&& (1023#64)).toNat = 0
    rw [BitVec.toNat_and, show (1023#64 : BitVec 64).toNat = 2 ^ 10 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_zero_of_dvd h
  · intro h
    have := congrArg UScalar.val h
    change (v.bv &&& (1023#64)).toNat = 0 at this
    rw [BitVec.toNat_and, show (1023#64 : BitVec 64).toNat = 2 ^ 10 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at this
    exact Nat.dvd_of_mod_eq_zero this


theorem ipc_shift : (1#u64 <<< fl4_abi.consts.bits.IPC_BUFFER : Result U64) = ok 1024#u64 := by
  unfold fl4_abi.consts.bits.IPC_BUFFER; rfl

/-- **FL4's IPC-buffer check refines l4v `check_valid_ipc_buffer`**: the
same success, or a related error (`IllegalOperation`, `AlignmentError`). -/
theorem check_valid_ipc_buffer_rel (vptr : U64) (c : capability.Cap) (σ : Fl4Spec.State Unit) :
    ∃ r, vspace.check_valid_ipc_buffer vptr c = ok r ∧
      ((r = .Ok () ∧ ExceptT.run (Fl4Spec.checkValidIpcBuffer (Z := Unit) vptr.bv (absCap c)) σ =
          ({(.ok (), σ)}, False)) ∨
       (∃ e e', r = .Err e ∧ MapErrRel e e' ∧
          ExceptT.run (Fl4Spec.checkValidIpcBuffer (Z := Unit) vptr.bv (absCap c)) σ = ({(.error e', σ)}, False))) := by
  have ill : ∀ c' : Fl4Spec.Cap, (∀ d sz r m fs mp, c' ≠ .archObjectCap (.pageCap d sz r m fs mp) ∨ d = true) →
      ExceptT.run (Fl4Spec.checkValidIpcBuffer (Z := Unit) vptr.bv c') σ =
        ({(.error .illegalOperation, σ)}, False) := by
    intro c' h
    unfold Fl4Spec.checkValidIpcBuffer
    cases c' with
    | archObjectCap ac =>
      cases ac with
      | pageCap d q r m fs mp =>
        cases d
        · rcases h false q r m fs mp with h | h
          · exact absurd rfl h
          · cases h
        · rfl
      | _ => rfl
    | _ => rfl
  cases c
  case Frame p sz r dev m ept a v =>
    cases dev
    case true =>
      refine ⟨_, rfl, Or.inr ⟨_, .illegalOperation, rfl, Or.inl (Or.inl trivial), ill _ ?_⟩⟩
      intro d q r' m' fs mp
      by_cases e : absCap (.Frame p sz r true m ept a v) = .archObjectCap (.pageCap d q r' m' fs mp)
      · right; simp [absCap] at e; exact e.1
      · left; exact e
    case false =>
      have hsp : Fl4Spec.checkValidIpcBuffer (Z := Unit) vptr.bv (absCap (.Frame p sz r false m ept a v)) =
          (do Fl4Spec.NonDetE.whenE (¬ Fl4Spec.isAligned vptr.bv 10) (Fl4Spec.NonDetE.throwError .alignmentError)
              Fl4Spec.NonDetE.returnOk ()) := by
        unfold Fl4Spec.checkValidIpcBuffer; rw [msgAlignBits_eq]; rfl
      generalize hD : ExceptT.run (Fl4Spec.checkValidIpcBuffer (Z := Unit) vptr.bv
        (absCap (.Frame p sz r false m ept a v))) σ = D
      have hFL : vspace.check_valid_ipc_buffer vptr (.Frame p sz r false m ept a v) =
          ok (if (vptr &&& 1023#u64) != 0#u64 then .Err (.Sys .AlignmentError) else .Ok ()) := by
        simp only [vspace.check_valid_ipc_buffer, Bool.false_eq_true, ↓reduceIte, ipc_shift, bind_ok]
        have h1 : (1024#u64 - 1#u64 : Result U64) = ok 1023#u64 := rfl
        rw [h1]
        simp only [bind_ok, lift]
        split <;> rfl
      rw [hFL]
      by_cases hal : (vptr &&& 1023#u64) = 0#u64
      · refine ⟨_, rfl, Or.inl ⟨by simp [hal], ?_⟩⟩
        rw [← hD, hsp, runE_bind_ok (runE_whenE_false (by rw [not_not, isAligned10_iff]; exact hal) _ σ)]; rfl
      · refine ⟨_, rfl, Or.inr ⟨_, .alignmentError, by simp [hal], Or.inr ⟨rfl, rfl⟩, ?_⟩⟩
        rw [← hD, hsp]
        exact runE_bind_err (by rw [runE_whenE_true (by rw [isAligned10_iff]; exact hal)]; rfl)
  all_goals
    refine ⟨_, rfl, Or.inr ⟨_, .illegalOperation, rfl, Or.inl (Or.inl trivial), ill _ (fun d sz r m fs mp =>
      Or.inl (by simp [absCap]))⟩⟩


/-! ## Mapped vtable caps have a non-zero ASID -/

/-- A mapped PML4 cap has a non-zero ASID (l4v `valid_cap`). -/
def MapOk (c : capability.Cap) : Prop := ∀ p asid, c = .Pml4 p true asid → asid ≠ 0#u64

/-- Every slot of the typed heap holds a `MapOk` cap. -/
def MappedAsid (th : TypedHeap) (mem : U64 → U64) : Prop :=
  ∀ a, IsSlot th a → ∀ c, capAt mem a = ok c → MapOk c

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`CurOK` for any thread of the typed heap**, so `set_vm_root` after a
vtable change (VsRoot, VsDelRoot) needs only `MappedAsid`. -/
theorem curOK_of {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hM : MappedAsid th (L.mem s)) {t : U64}
    (hcur : t.bv = σ.curThread) (ht : th t = some .tcb) : CurOK st th s σ :=
  ⟨t, hcur, ht, fun p asid h => hM _ ⟨t, 1, Or.inr ⟨ht, by decide⟩, rfl⟩ _ h p asid rfl⟩

theorem MappedAsid.of_capV {th : TypedHeap} {m m' : U64 → U64} (hM : MappedAsid th m) {a : U64} {c : capability.Cap}
    (hc : MapOk c) (h1 : capV m' a = c) (h2 : ∀ x, IsSlot th x → x ≠ a → capV m' x = capV m x) : MappedAsid th m' := by
  intro x hx c' hc'
  rw [capAt_capV] at hc'
  have e := eq_of_ok_eq hc'
  by_cases hxa : x = a
  · subst hxa; rw [h1] at e; subst e; exact hc
  · rw [h2 x hx hxa] at e; exact hM x hx c' (by rw [capAt_capV, e])

/-- `set_cap` of a `MapOk` cap keeps `MappedAsid`. -/
theorem MappedAsid.set_cap {th : TypedHeap} (hP : Placed th) {s : S} (hM : MappedAsid th (L.mem s)) {a : U64}
    (ha : IsSlot th a) (c : capability.Cap) (he : EncWf c) (hc : MapOk c) :
    obj.Slot.set_cap st a s c ⦃ s' => MappedAsid th (L.mem s') ⦄ :=
  WP.spec_mono (set_cap_upd (L := L) hP s ha c he) fun _ ⟨h1, h2, _⟩ => hM.of_capV hc h1 h2

/-- `cdt::insert` of a `MapOk` cap keeps `MappedAsid` (the source's cap may
become a full untyped cap). -/
theorem MappedAsid.of_insWords {th : TypedHeap} {s s' : S} (hM : MappedAsid th (L.mem s)) {c srcC : capability.Cap}
    {src dest : U64} (hW : InsWords (L := L) th s s' c srcC src dest) (he : EncWf c) (hes : EncWf srcC)
    (hsrcC : capAt (L.mem s) src = ok srcC) (hc : MapOk c) : MappedAsid th (L.mem s') := by
  intro x hx c' hc'
  rw [hW.capAt' hx he hes hsrcC] at hc'
  by_cases h1 : x = dest
  · rw [if_pos h1] at hc'; cases eq_of_ok_eq hc'; exact hc
  · rw [if_neg h1] at hc'
    by_cases h2 : x = src
    · rw [if_pos h2] at hc'
      cases hf : fullF srcC c with
      | none => rw [hf] at hc'; cases eq_of_ok_eq hc'; exact hM src (h2 ▸ hx) _ hsrcC
      | some c'' =>
        rw [hf] at hc'; cases eq_of_ok_eq hc'
        unfold fullF at hf
        split at hf
        · split_ifs at hf; cases hf; intro p asid h; cases h
        · cases hf
    · rw [if_neg h2] at hc'; exact hM x hx c' hc'

/-- `derive_cap` keeps `MapOk` (it does not change a PML4 cap). -/
theorem derive_mapOk (s : S) (slot : obj.Slot) {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c')) (hc : MapOk c) : MapOk c' := by
  cases c <;> simp [objects.derive_cap] at h
  all_goals first
    | (subst h; exact hc)
    | (obtain ⟨-, rfl⟩ := h; exact hc)
    | (intro p asid e; subst h; cases e)
    | (intro p asid e; rw [← h] at e; cases e)
    | (split_ifs at h <;> simp at h; subst h; exact hc)
    | (generalize cdt.ensure_no_children st s slot = r at h
       intro p asid e; subst e
       cases r with
       | ret v =>
         cases v <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
       | _ => simp at h)

end

end

end Fl4Proofs.P3.Vs
