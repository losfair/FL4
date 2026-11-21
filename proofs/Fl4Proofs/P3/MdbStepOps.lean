/-
P3 (DESIGN.md §9): **FL4's slot operations as `MdbStep`s**: `cdt::insert`
of a derived cap (`insert_mstep`), of a control cap's child
(`insert_ctl_mstep`), `cdt::move_cap` (`move_mstep`), `cdt::swap`
(`swap_mstep`) and `cdt::empty_slot` (`empty_mstep`).
-/
import Fl4Proofs.P3.MdbStep
import Fl4Proofs.P3.MdbOps
import Fl4Proofs.P3.CtlIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **The VSpace side facts of the cap operations** (`MdbStep`'s `hv`):
`mask_cap_rights`, `update_cap_data` and `derive_cap` keep a cap well
placed (they keep the VSpace caps but for a frame's rights, or clear a
frame's mapping). -/
theorem mask_vcap {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c')
    (P L4 L3 L2 L1 : Set U64) (hv : Vs.VCapOK P L4 L3 L2 L1 c) : Vs.VCapOK P L4 L3 L2 L1 c' := by
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m ept a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h; exact hv)
  all_goals (repeat' split at h) <;> (simp at h; subst h; exact hv)

theorem update_vcap {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (P L4 L3 L2 L1 : Set U64) (hv : Vs.VCapOK P L4 L3 L2 L1 c) : Vs.VCapOK P L4 L3 L2 L1 c' := by
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; trivial
    · revert h; generalize d >>> 6#i32 = x; cases x <;> simp
      generalize objects.mask (d &&& 63#u64) = y; cases y <;> simp
      intro h; subst h; trivial
  all_goals (repeat' split at h) <;> (simp at h; subst h; exact hv)

theorem derive_vcap {S : Type} {st : machine.Store S} {s : S} {slot : obj.Slot} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c'))
    (P L4 L3 L2 L1 : Set U64) (hv : Vs.VCapOK P L4 L3 L2 L1 c) : Vs.VCapOK P L4 L3 L2 L1 c' := by
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    revert h; generalize cdt.ensure_no_children st s slot = r
    cases r with
    | ret v =>
      cases v <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      intro h; subst h; trivial
    | _ => simp
  case Frame p sz r dv m ept a va =>
    simp only [objects.derive_cap] at h; simp at h; subst h
    simp only [Vs.VCapOK] at hv ⊢; exact ⟨fun e => absurd e (by decide), hv.2.1, fun e => absurd e (by decide)⟩
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h) <;> (simp at h; try subst h; exact hv)

/-- **Nativeness of the cap operations** (g2a, as the `_vcap` lemmas): `mask_cap_rights`,
`update_cap_data` and `derive_cap` keep a cap native. -/
theorem mask_nat {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c')
    (hv : Vs.NativeCap c) : Vs.NativeCap c' := by
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m ept a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h; exact hv)
  all_goals (repeat' split at h) <;> (simp at h; subst h; exact hv)

theorem update_nat {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (hv : Vs.NativeCap c) : Vs.NativeCap c' := by
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; trivial
    · revert h; generalize d >>> 6#i32 = x; cases x <;> simp
      generalize objects.mask (d &&& 63#u64) = y; cases y <;> simp
      intro h; subst h; trivial
  all_goals (repeat' split at h) <;> (simp at h; subst h; exact hv)

theorem derive_nat {S : Type} {st : machine.Store S} {s : S} {slot : obj.Slot} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c'))
    (hv : Vs.NativeCap c) : Vs.NativeCap c' := by
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    revert h; generalize cdt.ensure_no_children st s slot = r
    cases r with
    | ret v =>
      cases v <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      intro h; subst h; trivial
    | _ => simp
  case Frame p sz r dv m ept a va =>
    simp only [objects.derive_cap] at h; simp at h; subst h
    simp [Vs.NativeCap]
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h) <;> (simp at h; try subst h; exact hv)

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a derived cap is an `MdbStep`** (`MdbStep.insert`),
for a cap equal to the source if that is untyped. -/
theorem insert_mstep (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hI : MdbInv (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC)
    (hbd : badgeF c = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y src) (hzb : isZb srcC = false)
    (hkey : okey c = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 c) :
    cdt.insert st s c src dest ⦃ s' => (isUt srcC = true → c = srcC) →
      MdbStep (L.mem s) G (L.mem s') (insG G src dest (isPF (revOf (L.mem s) src) srcC c (revF c srcC))) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW hutc
  have hctx : InsCtx th (L.mem s) (L.mem s') G src dest c ((fullF srcC c).getD srcC) :=
    { hM := hM, hI := hI, hsrc := hsrc, hd := hd, hdest := hdest
      hnext := fun a ha => hW.nextOf' hP ha hd hne hNc
      hcap := fun a ha => by
        have := hW.capAt' ha he hes hsrcC
        rw [capAt_capV] at this
        by_cases h1 : a = dest
        · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
        · by_cases h2 : a = src
          · subst h2; simp only [h1, ↓reduceIte] at this ⊢; simpa using this
          · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this
      hrev := fun a ha => by rw [hW.revOf' ha hne, hcv]
      hfb := fun a ha => by rw [hW.fbOf' ha hne, hcv]
      hsh := by rw [hcv]; exact hsh
      hbd := by rw [hcv]; exact hbd
      hsh1 := by rw [hcv]; exact (fullF_shape srcC c).1
      hbd1 := by rw [hcv]; exact (fullF_shape srcC c).2
      hut := by rw [hcv]; exact hut
      hzb := by rw [hcv]; exact hzb }
  refine MdbStep.insert hctx (by rw [hcv]) (by rw [hcv]; exact hutc) (by rw [hcv]; exact hkey) _ (fun hu => ?_) (by rw [hcv]; exact hv)
  rw [hcv] at hu
  have hr := hI.utrev src hsrc (by rw [hcv]; exact hu)
  have hss := hI.self src hsrc (by rw [hcv]; exact hzb)
  unfold srM at hss; rw [hcv] at hss
  rw [hutc hu, hr]
  obtain ⟨q, sz, f, d, rfl⟩ : ∃ q sz f d, srcC = .Untyped q sz f d := by cases srcC <;> simp_all [isUt]
  simp [isPF, hss, isBadged]

/-- **`cdt::insert` of a control cap's child is an `MdbStep`**
(`MdbStep.nonphys`). -/
theorem insert_ctl_mstep (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC) (c : capability.Cap) (he : EncWf c) (hctl : CtlPair srcC c)
    (b : Bool) :
    cdt.insert st s c src dest ⦃ s' => MdbStep (L.mem s) G (L.mem s') (insG G src dest b) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hfull, -⟩ := hctl.facts
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW
  have hcap : ∀ a, IsSlot th a → a ≠ dest → capV (L.mem s') a = capV (L.mem s) a := by
    intro a ha had
    have := hW.capAt' ha he hes hsrcC
    rw [capAt_capV, if_neg had] at this
    by_cases h2 : a = src
    · subst h2; simp only [↓reduceIte, hfull, Option.getD_none] at this; rw [hcv]; simpa using this
    · simp only [h2, ↓reduceIte] at this; rw [capAt_capV] at this; simpa using this
  have hcd : capV (L.mem s') dest = c := by
    have := hW.capAt' hd he hes hsrcC
    rw [capAt_capV] at this; simpa using this
  have hphys : ∀ x, CtlPair x c → physF x = false ∧ physF c = false ∧ Fl4Spec.objRefs (absCap c) = ∅ := by
    intro x h
    rcases h.cases with ⟨rfl, i, rfl⟩ | ⟨rfl, f, l, vcpu, rfl⟩ <;>
      exact ⟨ok_inj (phys_eq _).symm, ok_inj (phys_eq _).symm, by
        simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef]⟩
  obtain ⟨h1, h2, h3⟩ := hphys srcC hctl
  exact MdbStep.nonphys hM b hsrc hdest (by rw [hcv]; exact h1) hcd h2 h3
    (fun z hz => hcap z (hslot z hz) (fun e => hdest (e ▸ hz)))
    (fun z hz => by rw [hW.revOf' (hslot z hz) hne, if_neg (fun (e : z = dest) => hdest (e ▸ hz))])

/-- **`cdt::move_cap` is an `MdbStep`** (`MdbStep.rename`), for a new cap of
the old one's shape and object, equal to it if untyped. -/
theorem move_mstep (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrcm : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdestm : dest ∉ G.chains.flatten) {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC) (hkey : okey c = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 c) :
    cdt.move_cap st s c src dest ⦃ s' => (isUt srcC = true → c = srcC) →
      MdbStep (L.mem s) G (L.mem s') (renG G (Equiv.swap src dest)) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrcm
  have hne : src ≠ dest := fun e => hdestm (e ▸ hsrcm)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src) := by
    by_cases h0 : prevOf (L.mem s) src = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrcm h0
      refine Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrcm with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  apply WP.spec_mono (move_mem hP s c _ _ hs hd hne hpv hnx)
  intro s' hW hutc
  have hcv := capV_of_capAt hsrcC
  have hdne : ∀ a, a ∈ G.chains.flatten → a ≠ dest := fun a h e => hdestm (e ▸ h)
  have hcd : capV (L.mem s') dest = c := capV_of_capAt (c := c) (by rw [hW.capAt' hd he hne]; simp)
  have hco : ∀ a ∈ G.chains.flatten, a ≠ src → capV (L.mem s') a = capV (L.mem s) a := by
    intro a ha has
    have := hW.capAt' (hslot a ha) he hne
    rw [if_neg (hdne a ha), if_neg has, capAt_capV, capAt_capV] at this
    simpa using this
  refine MdbStep.rename hM _ (fun a ha => ?_) (fun a ha P L4 L3 L2 L1 hok => ?_)
  · by_cases has : a = src
    · rw [has, Equiv.swap_apply_left, hcd, hcv, hW.revOf' hd hne, if_pos rfl]
      exact ⟨CapAlike.of_shape hsh hkey hutc, rfl⟩
    · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha), hW.revOf' (hslot a ha) hne, if_neg (hdne a ha),
        if_neg has, hco a ha has]
      exact ⟨CapAlike.refl _, rfl⟩
  · by_cases has : a = src
    · rw [has, Equiv.swap_apply_left, hcd]; rw [has, hcv] at hok; exact hv _ _ _ _ _ hok
    · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha), hco a ha has]; exact hok

/-- **`cdt::swap` is an `MdbStep`** (`MdbStep.rename`), for new caps of the
old ones' shapes and objects, equal to them if untyped. -/
theorem swap_mstep (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {s1 s2 : U64} (hm1 : s1 ∈ G.chains.flatten) (hm2 : s2 ∈ G.chains.flatten)
    (hne : s1 ≠ s2) (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2)
    (hsh1 : shape c1 = shape (capV (L.mem s) s1)) (hk1 : okey c1 = okey (capV (L.mem s) s1))
    (hsh2 : shape c2 = shape (capV (L.mem s) s2)) (hk2 : okey c2 = okey (capV (L.mem s) s2))
    (hv1 : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV (L.mem s) s1) → Vs.VCapOK P L4 L3 L2 L1 c1)
    (hv2 : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV (L.mem s) s2) → Vs.VCapOK P L4 L3 L2 L1 c2) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => (isUt (capV (L.mem s) s1) = true → c1 = capV (L.mem s) s1) →
      (isUt (capV (L.mem s) s2) = true → c2 = capV (L.mem s) s2) →
      MdbStep (L.mem s) G (L.mem s') (renG G (Equiv.swap s1 s2)) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hNx : ∀ a, a ∈ G.chains.flatten → nextOf (L.mem s) a = 0#u64 ∨ IsSlot th (nextOf (L.mem s) a) := by
    intro a ha; rcases hM.next_mem ha with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr (hslot _ h)]
  have hPx : ∀ a, a ∈ G.chains.flatten → prevOf (L.mem s) a = 0#u64 ∨ IsSlot th (prevOf (L.mem s) a) := by
    intro a ha; by_cases h : prevOf (L.mem s) a = 0#u64
    · exact Or.inl h
    · exact Or.inr (hslot _ (hM.prev_link ha h).1)
  apply WP.spec_mono (swap_fields hP s c1 c2 _ _ (hslot _ hm1) (hslot _ hm2) hne he1 he2 (hPx _ hm1) (hNx _ hm1)
    (hPx _ hm2) (hNx _ hm2))
  intro s' hW hut1 hut2
  have hq2 : capV (L.mem s') s2 = c1 := by
    have h := (hW _ (hslot _ hm2)).1
    rw [capAt_capV, if_pos rfl] at h; simpa using h
  have hq1 : capV (L.mem s') s1 = c2 := by
    have h := (hW _ (hslot _ hm1)).1
    rw [capAt_capV, if_neg hne, if_pos rfl] at h; simpa using h
  have hqo : ∀ a ∈ G.chains.flatten, a ≠ s1 → a ≠ s2 → capV (L.mem s') a = capV (L.mem s) a := by
    intro a ha e1 e2
    have h := (hW _ (hslot _ ha)).1
    rw [capAt_capV, if_neg e2, if_neg e1, capAt_capV] at h; simpa using h
  refine MdbStep.rename hM _ (fun a ha => ?_) (fun a ha P L4 L3 L2 L1 hok => ?_)
  · by_cases e1 : a = s1
    · rw [e1, Equiv.swap_apply_left, (hW _ (hslot _ hm2)).2.2.2.1, if_pos rfl, hq2]
      exact ⟨CapAlike.of_shape hsh1 hk1 hut1, rfl⟩
    · by_cases e2 : a = s2
      · rw [e2, Equiv.swap_apply_right, (hW _ (hslot _ hm1)).2.2.2.1, if_neg hne, if_pos rfl, hq1]
        exact ⟨CapAlike.of_shape hsh2 hk2 hut2, rfl⟩
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2, (hW _ (hslot _ ha)).2.2.2.1, if_neg e2, if_neg e1,
          hqo a ha e1 e2]
        exact ⟨CapAlike.refl _, rfl⟩
  · by_cases e1 : a = s1
    · subst e1; rw [Equiv.swap_apply_left, hq2]; exact hv1 _ _ _ _ _ hok
    · by_cases e2 : a = s2
      · subst e2; rw [Equiv.swap_apply_right, hq1]; exact hv2 _ _ _ _ _ hok
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2, hqo a ha e1 e2]; exact hok

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-- **`cdt::empty_slot` is an `MdbStep`** (`MdbStep.remove`). -/
theorem empty_mstep {th : TypedHeap} (hP : Placed th) (s : S) (a : A) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) {x : U64} (hxm : x ∈ G.chains.flatten)
    {c : capability.Cap} (hc : capAt (L.mem s) x = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a x .Null ⦃ r => MdbStep (L.mem s) G (L.mem r.1) (remG G x) ⦄ := by
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hx := hslot x hxm
  have hnx : nextOf (L.mem s) x = 0#u64 ∨ (IsSlot th (nextOf (L.mem s) x) ∧ nextOf (L.mem s) x ≠ x) := by
    rcases hM.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s) x = 0#u64 ∨ (IsSlot th (prevOf (L.mem s) x) ∧ prevOf (L.mem s) x ≠ x) := by
    by_cases h0 : prevOf (L.mem s) x = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hx.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM.prev_ne_next hP hxm
  apply WP.spec_mono (empty_slot_mem hP s a _ hx c hc hcn hpv hnx hPN)
  rintro r ⟨hW, -⟩
  refine MdbStep.remove hM x (fun y hy hyx => ?_) (fun y hy hyx => ?_)
  · have := hW.capAt' (hslot y hy); rw [if_neg hyx, capAt_capV, capAt_capV] at this; simpa using this
  · rw [hW.revOf' (hslot y hy), if_neg hyx]

end

end

end Fl4Proofs.P3
