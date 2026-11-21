/-
P3 (DESIGN.md §9), CSpace: the caps CNode Copy, Mint, Move, Mutate and
Rotate put in a slot are **unmapped table caps only if their source is**
(`copied_tabun`, `update_tabun`): with `copied_vcap`/`update_vcap` this is
what `VCapW.transfer` needs to keep the weakened VSpace cap field
(`JAtZ.vsc`) across them. FL4's `derive_cap` returns a mapped table cap
unchanged and errs on an unmapped one; `mask_cap_rights` and
`update_cap_data` keep a table cap.
-/
import Fl4Proofs.P3.CnodeKey
import Fl4Proofs.P3.VsCapWBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem mask_tabun {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c')
    (hT : Vs.TabUn c') : Vs.TabUn c := by
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m ept a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h; exact hT)
  all_goals (repeat' split at h) <;> (simp at h; subst h; exact hT)

theorem update_tabun {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (hT : Vs.TabUn c') : Vs.TabUn c := by
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; exact hT
    · revert h; generalize d >>> 6#i32 = x; cases x <;> simp
      generalize objects.mask (d &&& 63#u64) = y; cases y <;> simp
      intro h; subst h; exact hT
  all_goals (repeat' split at h) <;> (simp at h; subst h; exact hT)

theorem derive_tabun {S : Type} {st : machine.Store S} {s : S} {slot : obj.Slot} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c')) (hT : Vs.TabUn c') : False := by
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    revert h; generalize cdt.ensure_no_children st s slot = r
    cases r with
    | ret v =>
      cases v <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      intro h; subst h; exact hT
    | _ => simp
  case Frame p sz r dv m ept a va =>
    simp only [objects.derive_cap] at h; simp at h; subst h; exact hT
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h) <;> (simp at h; try subst h) <;> first | exact hT | simp_all [Vs.TabUn]

section
variable {S : Type} {st : machine.Store S}

/-- **The cap `copied_cap` produces is an unmapped table cap only if the
source is** (a derived cap is never one; a moved cap is the source; a
mutated one keeps the source's table cap). -/
theorem copied_tabun {s : S} {lbl length buf src : U64} {srcC nc : capability.Cap} {mv : Bool}
    (h : cnode.copied_cap st s lbl length buf src srcC = ok (.Ok (nc, mv))) (hT : Vs.TabUn nc) :
    Vs.TabUn srcC := by
  unfold cnode.copied_cap at h
  obtain ⟨ct, -, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · simp [error.truncated] at h
    obtain ⟨i, -, h⟩ := bind_ok_inv h
    obtain ⟨r, -, h⟩ := bind_ok_inv h
    obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
    obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
    cases r1 with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
    | Ok v =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (derive_tabun hr1 hT).elim
  · split at h
    · split at h
      · simp [error.truncated] at h
      obtain ⟨i, -, h⟩ := bind_ok_inv h
      obtain ⟨r, -, h⟩ := bind_ok_inv h
      obtain ⟨d, -, h⟩ := bind_ok_inv h
      obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
      obtain ⟨c2, hc2, h⟩ := bind_ok_inv h
      obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
      cases r1 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] at h
      | Ok v =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (derive_tabun hr1 hT).elim
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hT
      · split at h
        · simp [error.truncated] at h
        obtain ⟨d, -, h⟩ := bind_ok_inv h
        obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact update_tabun hc1 hT

end

section
variable {th : TypedHeap} {m m' : U64 → U64}

/-- **An insert keeps the slots placed** (`cdt::insert` of a copied cap: the
destination gets `c`, placed when the source is (`VCapW.transfer`), the
source set full if untyped). -/
theorem vsSlotsT_insert {src dest : U64} (hs : IsSlot th src) {c : capability.Cap}
    (hc : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y) (hd : capV m' dest = c)
    (hsC : capV m' src = (fullF (capV m src) c).getD (capV m src))
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV m src) → Vs.VCapOK P L4 L3 L2 L1 c)
    (hu : Vs.TabUn c → Vs.TabUn (capV m src)) (hk : okey c = okey (capV m src))
    (hn : Vs.NativeCap (capV m src) → Vs.NativeCap c) : Vs.VsSlotsT th m m' := by
  refine Vs.VsSlotsT.of_some (fun y => y = src ∨ y = dest) (fun y hy hn => hc y hy (fun e => hn (Or.inl e))
    (fun e => hn (Or.inr e))) ?_ ?_ ?_
  · intro y hy e P L4 L3 L2 L1 h
    by_cases e2 : y = dest
    · subst e2; rw [hd]; exact h.copy hs hv hu
    · have e1 : y = src := e.resolve_right e2
      subst e1
      rw [hsC]
      cases hf : fullF (capV m y) c with
      | none => exact h y hy
      | some u =>
        simp only [Option.getD_some]
        unfold fullF at hf
        split at hf
        · split_ifs at hf; cases hf; trivial
        · cases hf
  · intro y hy e U h
    by_cases e2 : y = dest
    · subst e2; rw [hd]; exact (h src hs).of_okey hk
    · have e1 : y = src := e.resolve_right e2
      subst e1
      rw [hsC]
      cases hf : fullF (capV m y) c with
      | none => exact h y hy
      | some u =>
        simp only [Option.getD_some]
        unfold fullF at hf
        split at hf
        · split_ifs at hf; cases hf; trivial
        · cases hf
  · intro y hy e h
    by_cases e2 : y = dest
    · subst e2; rw [hd]; exact hn (h src hs)
    · have e1 : y = src := e.resolve_right e2
      subst e1
      rw [hsC]
      cases hf : fullF (capV m y) c with
      | none => exact h y hy
      | some u =>
        simp only [Option.getD_some]
        unfold fullF at hf
        split at hf
        · split_ifs at hf; cases hf; trivial
        · cases hf

/-- **A move keeps the slots placed**: the destination gets `c`, placed
when the source is, the source emptied. -/
theorem vsSlotsT_move {src dest : U64} (hs : IsSlot th src) {c : capability.Cap}
    (hc : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y) (hd : capV m' dest = c)
    (hsC : capV m' src = .Null)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV m src) → Vs.VCapOK P L4 L3 L2 L1 c)
    (hu : Vs.TabUn c → Vs.TabUn (capV m src)) (hk : okey c = okey (capV m src))
    (hn : Vs.NativeCap (capV m src) → Vs.NativeCap c) : Vs.VsSlotsT th m m' := by
  refine Vs.VsSlotsT.of_some (fun y => y = src ∨ y = dest) (fun y hy hn => hc y hy (fun e => hn (Or.inl e))
    (fun e => hn (Or.inr e))) ?_ ?_ ?_
  · intro y hy e P L4 L3 L2 L1 h
    by_cases e2 : y = dest
    · subst e2; rw [hd]; exact h.copy hs hv hu
    · have e1 : y = src := e.resolve_right e2
      subst e1; rw [hsC]; trivial
  · intro y hy e U h
    by_cases e2 : y = dest
    · subst e2; rw [hd]; exact (h src hs).of_okey hk
    · have e1 : y = src := e.resolve_right e2
      subst e1; rw [hsC]; trivial
  · intro y hy e h
    by_cases e2 : y = dest
    · subst e2; rw [hd]; exact hn (h src hs)
    · have e1 : y = src := e.resolve_right e2
      subst e1; rw [hsC]; trivial

/-- **A swap keeps the slots placed**: `s2` gets `c1`, placed when `s1`'s
cap is, and `s1` gets `c2`, placed when `s2`'s is. -/
theorem vsSlotsT_swap {s1 s2 : U64} (hs1 : IsSlot th s1) (hs2 : IsSlot th s2) {c1 c2 : capability.Cap}
    (hc : ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV m' y = capV m y) (hd2 : capV m' s2 = c1)
    (hd1 : capV m' s1 = c2)
    (hv1 : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV m s1) → Vs.VCapOK P L4 L3 L2 L1 c1)
    (hu1 : Vs.TabUn c1 → Vs.TabUn (capV m s1))
    (hv2 : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV m s2) → Vs.VCapOK P L4 L3 L2 L1 c2)
    (hu2 : Vs.TabUn c2 → Vs.TabUn (capV m s2)) (hk1 : okey c1 = okey (capV m s1))
    (hk2 : okey c2 = okey (capV m s2)) (hn1 : Vs.NativeCap (capV m s1) → Vs.NativeCap c1)
    (hn2 : Vs.NativeCap (capV m s2) → Vs.NativeCap c2) : Vs.VsSlotsT th m m' := by
  refine Vs.VsSlotsT.of_some (fun y => y = s1 ∨ y = s2) (fun y hy hn => hc y hy (fun e => hn (Or.inl e))
    (fun e => hn (Or.inr e))) ?_ ?_ ?_
  · intro y hy e P L4 L3 L2 L1 h
    by_cases e2 : y = s2
    · subst e2; rw [hd2]; exact h.copy hs1 hv1 hu1
    · have e1 : y = s1 := e.resolve_right e2
      subst e1; rw [hd1]; exact h.copy hs2 hv2 hu2
  · intro y hy e U h
    by_cases e2 : y = s2
    · subst e2; rw [hd2]; exact (h s1 hs1).of_okey hk1
    · have e1 : y = s1 := e.resolve_right e2
      subst e1; rw [hd1]; exact (h s2 hs2).of_okey hk2
  · intro y hy e h
    by_cases e2 : y = s2
    · subst e2; rw [hd2]; exact hn1 (h s1 hs1)
    · have e1 : y = s1 := e.resolve_right e2
      subst e1; rw [hd1]; exact hn2 (h s2 hs2)

end

end

end Fl4Proofs.P3
