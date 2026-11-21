/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **`create_cap` keeps
`UtInv'`** (spec side only).

`create_cap src (dest, oref)` makes `dest` a CDT child of `src`, sets its
original flag and writes the new object's default cap there. With `dest` a CDT
leaf (`CdtOK`: it held a null cap) the descendant relation between the other
slots is unchanged (`lu_tg`).
* `utInv'_cc`: a cap that is not untyped (every object type but `untyped`).
* `utInv'_ccU`: an untyped cap `(dev, p, bits, 0)` whose region lies inside the
  source's region and outside its (raised) free part, holds no object, and meets
  the region of another untyped cap only if that cap is an ancestor of the source
  whose free part misses the source's region (l4v `untyped_inc` for the new cap).
-/
import Fl4Proofs.P3.SpecInvUtC
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## A CDT leaf update -/

theorem lu_noKid {t : Cdt} {d : CslotPtr} {v : Option CslotPtr} (hk : ∀ c, t c ≠ some d) (hv : v ≠ some d)
    (c : CslotPtr) : Function.update t d v c ≠ some d := by
  by_cases e : c = d
  · subst e; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne e]; exact hk c

theorem lu_tg {t : Cdt} {d : CslotPtr} {v : Option CslotPtr} (hk : ∀ c, t c ≠ some d) (hv : v ≠ some d)
    {x y : CslotPtr} (hy : y ≠ d) :
    Relation.TransGen (parentOf (Function.update t d v)) x y ↔ Relation.TransGen (parentOf t) x y := by
  constructor
  · intro h
    induction h with
    | @single b h =>
      have h' : Function.update t d v b = some x := h
      rw [Function.update_of_ne hy] at h'
      exact Relation.TransGen.single h'
    | @tail b y _ hby ih =>
      have h' : Function.update t d v y = some b := hby
      have hb : b ≠ d := fun e => lu_noKid hk hv y (e ▸ h')
      rw [Function.update_of_ne hy] at h'
      exact Relation.TransGen.tail (ih hb) h'
  · intro h
    induction h with
    | @single b h =>
      have h' : t b = some x := h
      exact Relation.TransGen.single (show Function.update t d v b = some x by rw [Function.update_of_ne hy]; exact h')
    | @tail b y _ hby ih =>
      have h' : t y = some b := hby
      have hb : b ≠ d := fun e => hk y (e ▸ h')
      exact Relation.TransGen.tail (ih hb) (show Function.update t d v y = some b by rw [Function.update_of_ne hy]; exact h')

theorem lu_acyc {t : Cdt} {d : CslotPtr} {v : Option CslotPtr} (hk : ∀ c, t c ≠ some d) (hv : v ≠ some d)
    (hA : ∀ x, ¬ Relation.TransGen (parentOf t) x x) : ∀ x, ¬ Relation.TransGen (parentOf (Function.update t d v)) x x := by
  intro x hx
  by_cases e : x = d
  · subst e; obtain ⟨c, hc⟩ := tg_first hx; exact lu_noKid hk hv c hc
  · exact hA x ((lu_tg hk hv e).1 hx)

/-! ## `create_cap` -/

/-- The view after `create_cap src (dest, _)` writing `dc`. -/
def vCC (src dest : CslotPtr) (dc : Cap) (w : UView) : UView :=
  vCap dest dc (vOrig dest true (vCdt (Function.update w.2.2.1 dest (some src)) w))

theorem hv_createCap (ty : ApiObjectType) (bits : Nat) (src : CslotPtr) (dev : Bool) (dest : CslotPtr)
    (oref : ObjRef) (w : UView) :
    HV (· = w) (· = vCC src dest (defaultCap ty oref bits dev) w) (createCap (Z := Unit) ty bits src dev (dest, oref)) := by
  unfold createCap
  refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w1 hw1 => ?_
  subst hw1
  refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w2 hw2 => ?_
  subst hw2
  refine hv_bind (hv_setCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_bind (hv_setOriginal _ _ _) fun _ => ?_
  exact hv_setCap _ _ _

theorem vCC_cap {src dest : CslotPtr} {dc : Cap} {w : UView} (sl : CslotPtr) :
    (vCC src dest dc w).2.1 sl = if sl = dest then some dc else w.2.1 sl := by
  unfold vCC vCap vOrig vCdt
  by_cases e : sl = dest
  · subst e; simp
  · simp [e]

theorem cdt_cc {w : UView} (hO : CdtOKV w) (hA : CdtAcycV w) {src dest : CslotPtr} {dc : Cap}
    (hne : dest ≠ src) (hk : ∀ c, w.2.2.1 c ≠ some dest) (hs : ∃ c, w.2.1 src = some c ∧ c ≠ .nullCap) :
    CdtOKV (vCC src dest dc w) ∧ CdtAcycV (vCC src dest dc w) := by
  have hv : (some src : Option CslotPtr) ≠ some dest := fun e => hne (Option.some.inj e).symm
  refine ⟨fun c q h => ?_, lu_acyc hk hv hA⟩
  have h' : Function.update w.2.2.1 dest (some src) c = some q := h
  rw [vCC_cap]
  by_cases e : c = dest
  · subst e; rw [Function.update_self] at h'; obtain rfl := Option.some.inj h'
    rw [if_neg (Ne.symm hne)]; exact hs
  · rw [Function.update_of_ne e] at h'
    have hq : q ≠ dest := fun e' => hk c (e' ▸ h')
    rw [if_neg hq]; exact hO c q h'

/-- **`create_cap` of a cap that is not untyped keeps `UtInv'`.** -/
theorem utInv'_cc {w : UView} (hI : UtInv'V w) {src dest : CslotPtr} {dc : Cap} (hne : dest ≠ src)
    (hk : ∀ c, w.2.2.1 c ≠ some dest) (hs : ∃ c, w.2.1 src = some c ∧ c ≠ .nullCap)
    (hnu : ∀ d b n f, dc ≠ .untypedCap d b n f) : UtInv'V (vCC src dest dc w) := by
  obtain ⟨hU, hO, hA⟩ := hI
  have hv : (some src : Option CslotPtr) ≠ some dest := fun e => hne (Option.some.inj e).symm
  have hnd : ∀ sl d b n f, (vCC src dest dc w).2.1 sl = some (.untypedCap d b n f) → sl ≠ dest := by
    intro sl d b n f h e; subst e; rw [vCC_cap, if_pos rfl] at h; exact hnu d b n f (Option.some.inj h)
  have hcap : ∀ sl, sl ≠ dest → (vCC src dest dc w).2.1 sl = w.2.1 sl := fun sl h => by rw [vCC_cap, if_neg h]
  refine ⟨utInvV_shrinkD (w := w) ⟨fun p hp => Or.inl hp, fun sl d b n f h => ?_,
    fun s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 h1 h2 hd => ?_, fun sl d b n f h ho => ?_⟩ hU, cdt_cc hO hA hne hk hs⟩
  · rw [hcap sl (hnd sl d b n f h)] at h; exact same_capV hU.2.1 h
  · exact (lu_tg hk hv (hnd s2 _ _ _ _ h2)).2 hd
  · show Function.update w.2.2.2 dest true sl = true
    rw [Function.update_of_ne (hnd sl d b n f h)]; exact ho

theorem utFr_sub {b : ObjRef} {n f k : Nat} (h : k ∈ utFr b n f) : k ∈ utR b n := ⟨by have := h.1; omega, h.2⟩

theorem utFr_zero {b : ObjRef} {n k : Nat} : k ∈ utFr b n 0 ↔ k ∈ utR b n := by
  simp only [utFr, utR, Set.mem_setOf_eq, Nat.add_zero]

/-- **`create_cap` of a new untyped cap keeps `UtInv'`.** -/
theorem utInv'_ccU {w : UView} (hI : UtInv'V w) {src dest : CslotPtr} (hne : dest ≠ src)
    (hk : ∀ c, w.2.2.1 c ≠ some dest) {dS : Bool} {bS : ObjRef} {nS fS : Nat}
    (hs : w.2.1 src = some (.untypedCap dS bS nS fS)) {dev : Bool} {p : ObjRef} {bits : Nat}
    (hR : ∀ k ∈ utR p bits, k ∈ utR bS nS ∧ k ∉ utFr bS nS fS)
    (hE : ∀ q, w.1 q = true → q.toNat ∉ utR p bits)
    (hWf : bits ≤ untypedMaxBits ∧ p.toNat % 2 ^ bits = 0)
    (hAn : ∀ sl d b n f, sl ≠ src → sl ≠ dest → w.2.1 sl = some (.untypedCap d b n f) →
      (∃ k, k ∈ utR p bits ∧ k ∈ utR b n) →
      src ∈ descendantsOf sl w.2.2.1 ∧ ∀ k ∈ utR bS nS, k ∉ utFr b n f) :
    UtInv'V (vCC src dest (.untypedCap dev p bits 0) w) := by
  obtain ⟨⟨hF, hW, hD, hDe, hOr⟩, hO, hA⟩ := hI
  have hv : (some src : Option CslotPtr) ≠ some dest := fun e => hne (Option.some.inj e).symm
  have hcap : ∀ sl, sl ≠ dest → (vCC src dest (.untypedCap dev p bits 0) w).2.1 sl = w.2.1 sl := fun sl h => by rw [vCC_cap, if_neg h]
  have hdst : (vCC src dest (.untypedCap dev p bits 0) w).2.1 dest = some (.untypedCap dev p bits 0) := by rw [vCC_cap, if_pos rfl]
  have hcdt : (vCC src dest (.untypedCap dev p bits 0) w).2.2.1 = Function.update w.2.2.1 dest (some src) := rfl
  have hdesc : ∀ x y, y ≠ dest → y ∈ descendantsOf x w.2.2.1 → y ∈ descendantsOf x (vCC src dest (.untypedCap dev p bits 0) w).2.2.1 :=
    fun x y hy h => by rw [hcdt]; exact (lu_tg hk hv hy).2 h
  have hsrc' : (vCC src dest (.untypedCap dev p bits 0) w).2.1 src = some (.untypedCap dS bS nS fS) := by rw [hcap src (Ne.symm hne)]; exact hs
  -- the new cap against any other untyped cap `s` of the new view
  have side : ∀ s d b n f, s ≠ dest → (vCC src dest (.untypedCap dev p bits 0) w).2.1 s = some (.untypedCap d b n f) →
      (∀ k, k ∈ utR p bits → k ∉ utFr b n f) ∧
      ((∃ k, k ∈ utR p bits ∧ k ∈ utR b n) →
        dest ∈ descendantsOf s (vCC src dest (.untypedCap dev p bits 0) w).2.2.1 ∧ ∀ k, k ∈ utR p bits → k ∉ utFr b n f) := by
    intro s d b n f hs1 hc
    rw [hcap s hs1] at hc
    by_cases e : s = src
    · subst e; rw [hs] at hc; cases hc
      refine ⟨fun k hk => (hR k hk).2, fun _ => ⟨?_, fun k hk => (hR k hk).2⟩⟩
      exact Relation.TransGen.single (show Function.update w.2.2.1 dest (some s) dest = some s by
        rw [Function.update_self])
    · have hno : ∀ k, k ∈ utR p bits → k ∉ utFr b n f := by
        intro k hk hk2
        obtain ⟨-, h2⟩ := hAn s d b n f e hs1 hc ⟨k, hk, utFr_sub hk2⟩
        exact h2 k (hR k hk).1 hk2
      refine ⟨hno, fun hov => ⟨?_, hno⟩⟩
      obtain ⟨h1, -⟩ := hAn s d b n f e hs1 hc hov
      have h1' := hdesc s src (Ne.symm hne) h1
      exact Relation.TransGen.tail h1' (show Function.update w.2.2.1 dest (some src) dest = some src by
        rw [Function.update_self])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, (cdt_cc hO hA hne hk ⟨_, hs, by intro h; cases h⟩).1,
    (cdt_cc hO hA hne hk ⟨_, hs, by intro h; cases h⟩).2⟩
  · intro sl d b n f hc q hq hk2
    by_cases e : sl = dest
    · subst e; rw [hdst] at hc; cases hc
      exact hE q hq (utFr_zero.1 hk2)
    · rw [hcap sl e] at hc; exact hF sl d b n f hc q hq hk2
  · intro sl d b n f hc
    by_cases e : sl = dest
    · subst e; rw [hdst] at hc; cases hc; exact ⟨hWf.1, hWf.2, Nat.zero_le _⟩
    · rw [hcap sl e] at hc; exact hW sl d b n f hc
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 k hk1 hk2
    by_cases e1 : s1 = dest
    · subst e1; rw [hdst] at hc1; cases hc1
      exact (side s2 d2 b2 n2 f2 (Ne.symm hne') hc2).1 k (utFr_zero.1 hk1) hk2
    · by_cases e2 : s2 = dest
      · subst e2; rw [hdst] at hc2; cases hc2
        exact (side s1 d1 b1 n1 f1 hne' hc1).1 k (utFr_zero.1 hk2) hk1
      · rw [hcap s1 e1] at hc1; rw [hcap s2 e2] at hc2
        exact hD s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 k hk1 hk2
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 hov
    by_cases e1 : s1 = dest
    · subst e1; rw [hdst] at hc1; cases hc1
      exact Or.inr ((side s2 d2 b2 n2 f2 (Ne.symm hne') hc2).2 hov)
    · by_cases e2 : s2 = dest
      · subst e2; rw [hdst] at hc2; cases hc2
        obtain ⟨k, h1, h2⟩ := hov
        exact Or.inl ((side s1 d1 b1 n1 f1 hne' hc1).2 ⟨k, h2, h1⟩)
      · rw [hcap s1 e1] at hc1; rw [hcap s2 e2] at hc2
        rcases hDe s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 hov with ⟨hd, hr⟩ | ⟨hd, hr⟩
        · exact Or.inl ⟨hdesc s1 s2 e2 hd, hr⟩
        · exact Or.inr ⟨hdesc s2 s1 e1 hd, hr⟩
  · intro sl d b n f hc
    show Function.update w.2.2.2 dest true sl = true
    by_cases e : sl = dest
    · subst e; rw [Function.update_self]
    · rw [Function.update_of_ne e]; rw [hcap sl e] at hc; exact hOr sl d b n f hc

end

end Fl4Proofs.P3.SInvU
