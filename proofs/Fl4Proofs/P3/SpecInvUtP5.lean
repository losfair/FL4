/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut8): **the retype tail of
`invoke_untyped` keeps `NV N`, and the untyped decode's destination facts**
(spec side only; imports SpecInvUtP4).

* `UtOKN` / **`okv_decodeUntypedN`**: the destination slots are
  `(objRefOf nc, nat_to_cref (bitsOf nc) i)` for a window `[off, off + win)` inside
  a CNode cap `nc` held in a slot (`isCnodeCap`); with CnBits they are
  `DestRefV` and pairwise distinct (`natToCref_inj`).
* **`nv_tail`**: the free-index raise (`nv_setUt`), `retype_region` (new objects'
  slots are null, `default_null`), `init_arch_objects` and the `create_cap` loop
  (`nv_ccLoop`) keep `NV N`, from a state where no cap and no object meets the new
  objects' range `[rb, rb + n·2^o)`, no cap meets the free part above the new free
  index, and every other untyped cap overlapping the range is an ancestor of the
  source whose free part misses it.
-/
import Fl4Proofs.P3.SpecInvUtP4
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-! ## Slot indices -/

theorem natToCref_inj {L i j : Nat} (hL : L ≤ 64) (hi : i < 2 ^ L) (hj : j < 2 ^ L)
    (h : natToCref L i = natToCref L j) : i = j := by
  have h2 : 2 ^ L ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hL
  rw [natToCref_ubits _ _ hL, natToCref_ubits _ _ hL, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < L
  · have hl : L - 1 - (L - 1 - t) = t := by omega
    have hlt : L - 1 - t < (ubits i L).length := by rw [ubits_length]; omega
    have hlt' : L - 1 - t < (ubits j L).length := by rw [ubits_length]; omega
    have e1 := getElem_ubits i L _ hlt
    have e2 := getElem_ubits j L _ hlt'
    rw [hl] at e1 e2
    rw [← e1, ← e2]
    exact List.getElem_of_eq h hlt
  · have hp : 2 ^ L ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-! ## The untyped decode's destinations -/

theorem okv_bind_held {ε β : Type} {w : UView} {P : β → Prop} {m : NonDetE (State Unit) ε Cap}
    {g : Cap → NonDetE (State Unit) ε β} (hm : ∀ v, UKE v m) (hq : OkV w (fun c => ∃ s, w.2.1 s = some c) m)
    (hg : ∀ c s, w.2.1 s = some c → OkV w P (g c)) : OkV w P (m >>= g) :=
  okv_bind hm hq fun c ⟨s, hs⟩ => hg c s hs

theorem okv_getCapE {w : UView} {ε : Type} (sl : CslotPtr) :
    OkV w (fun c => ∃ s, w.2.1 s = some c) (NonDetE.liftE (ε := ε) (getCap (Z := Unit) sl)) := by
  intro σ hσ a s hs
  obtain ⟨x, hx, e⟩ := mem_liftE' hs
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact ⟨sl, by rw [← hσ]; exact (getCap_capAt hx).2⟩

/-- What the retype's `create_cap` loop needs from the decode. -/
def UtOKN (w : UView) : UntypedInvocation → Prop
  | .retype _ _ _ _ _ sz slots _ => sz < 64 ∧ ∃ s1 nc off win, w.2.1 s1 = some nc ∧ isCnodeCap nc = true ∧
      off + win ≤ 2 ^ bitsOf nc ∧
      slots = ((List.range' off (off + win - off)).map (natToCref (bitsOf nc))).map fun cref => (objRefOf nc, cref)

theorem okv_ite' {ε α : Type} {w : UView} {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE (State Unit) ε α}
    (h1 : c → OkV w P m1) (h2 : ¬ c → OkV w P m2) : OkV w P (if c then m1 else m2) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem okv_ifunit_bind {ε β : Type} {w : UView} {P : β → Prop} {c : Prop} [Decidable c] {e : ε}
    {g : Unit → NonDetE (State Unit) ε β} (hg : c → OkV w P (g ())) :
    OkV w P ((if c then NonDetE.returnOk () else NonDetE.throwError e) >>= g) := by
  by_cases hc : c
  · rw [if_pos hc]; exact okv_returnOk_bind (hg hc)
  · rw [if_neg hc]; exact okv_throw_bind _

macro "okvu_step" : tactic => `(tactic| first
  | exact okv_throw _ | exact okv_throw' _ | exact okv_liftE_fail | exact okv_throw_bind _
  | (refine okv_returnOk_bind ?_) | (refine okv_pure_bind ?_)
  | (refine okv_whenE_bind fun _ => ?_) | (refine okv_unlessE_bind fun _ => ?_)
  | (refine okv_bind_held (fun _ => by uk_auto) ?_ fun _ _ _ => ?_)
  | (exact okv_returnOk (root0 (by assumption) (by omega)))
  | (refine okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun _ => okv_getCapE _)
  | (refine okv_ifunit_bind fun _ => ?_)
  | (dsimp only)
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_)
  | (refine okv_ite' (fun _ => ?_) (fun _ => ?_))
  | split)

set_option maxHeartbeats 2000000 in
theorem okv_decodeUntypedN {w : UView} (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (ex : List Cap)
    (hcps : ∀ c ∈ ex, ∃ s, w.2.1 s = some c) :
    OkV w (UtOKN w) (decodeUntypedInvocationWith (Z := Unit) fl4ObjBitsApi label args slot cap ex) := by
  unfold decodeUntypedInvocationWith
  repeat' okvu_step
  all_goals first
    | exact okv_throw _
    | exact okv_returnOk ⟨by simp only [wordBits] at *; omega, _, _, _, _, by assumption, by assumption, by omega, rfl⟩

/-- The destinations of a decoded retype are distinct CNode slots reached through a held CNode cap. -/
theorem utDest_of {w : UView} (hB : CnBitsV w) {slots : List CslotPtr} {s1 : CslotPtr} {nc : Cap} {off win : Nat}
    (hs1 : w.2.1 s1 = some nc) (hcn : isCnodeCap nc = true) (hle : off + win ≤ 2 ^ bitsOf nc)
    (he : slots = ((List.range' off (off + win - off)).map (natToCref (bitsOf nc))).map fun cref => (objRefOf nc, cref)) :
    slots.Nodup ∧ ∀ d ∈ slots, DestRefV w d := by
  obtain ⟨ptr, bits, g, rfl⟩ : ∃ ptr bits g, nc = .cnodeCap ptr bits g := by
    cases nc <;> first | exact ⟨_, _, _, rfl⟩ | (simp [isCnodeCap] at hcn)
  have hb : bits ≤ 64 := hB s1 _ hs1 bits rfl
  simp only [bitsOf, objRefOf] at hle he
  subst he
  refine ⟨?_, fun d hd => ?_⟩
  · show List.Pairwise (· ≠ ·) _
    rw [List.range'_eq_map_range, List.pairwise_map, List.pairwise_map, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (R := (· < ·)) (fun {i j} hi hj hij => ?_) List.pairwise_lt_range
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    intro h
    injection h with _ h2
    have := natToCref_inj hb (by omega) (by omega) h2
    omega
  · obtain ⟨cref, hcref, rfl⟩ := List.mem_map.1 hd
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hcref
    exact ⟨s1, _, hs1, rfl, fun _ _ _ e => (by cases e), natToCref_len bits i hb⟩

/-! ## Facts about the tail -/

/-- A new object's slots hold null caps. -/
theorem default_null {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (dm : Domain)
    (i : CnodeIndex) {c : Cap} (h : capView (defaultObject ty dev n dm) i = some c) : c = .nullCap := by
  cases ty with
  | untyped => exact absurd rfl hty
  | capTableObject =>
    simp only [defaultObject, capView_cnode] at h
    split_ifs at h <;> (try simp only [emptyCnode] at h) <;> (try split_ifs at h) <;>
      first | (cases h; rfl) | cases h
  | tcbObject =>
    simp only [defaultObject, capView_tcb, tcbCnodeMap, defaultTcb, Function.update_apply] at h
    split_ifs at h <;> first | (cases h; rfl) | cases h
  | _ => cases h

theorem pw_zip2 {α β : Type} {R : β → β → Prop} :
    ∀ (l1 : List α) (l2 : List β), l1.Nodup → l2.Pairwise R → (l1.zip l2).Pairwise (fun a b => a.1 ≠ b.1 ∧ R a.2 b.2)
  | [], _, _, _ => List.Pairwise.nil
  | _ :: _, [], _, _ => List.Pairwise.nil
  | a :: as, b :: bs, h1, h => by
    rw [List.nodup_cons] at h1
    rw [List.pairwise_cons] at h
    rw [List.zip_cons_cons]
    refine List.Pairwise.cons (fun x hx => ⟨fun e => h1.1 ?_, h.1 _ (List.of_mem_zip hx).2⟩) (pw_zip2 as bs h1.2 h.2)
    have e' : a = x.1 := e
    rw [e']; exact (List.of_mem_zip hx).1

theorem zip_rng {slots : List CslotPtr} {rb : ObjRef} {o : Nat} {x : CslotPtr × ObjRef}
    (hx : x ∈ slots.zip (retPtrs rb slots.length o)) (hfit : rb.toNat + slots.length * 2 ^ o ≤ 2 ^ 64) :
    rb.toNat ≤ x.2.toNat ∧ x.2.toNat + 2 ^ o ≤ rb.toNat + slots.length * 2 ^ o := by
  obtain ⟨k, hk, hxk⟩ := retPtrs_mem (List.of_mem_zip hx).2
  have hpo := Nat.two_pow_pos o
  have m2 : (k + 1) * 2 ^ o ≤ slots.length * 2 ^ o := Nat.mul_le_mul_right _ hk
  have e2 : (k + 1) * 2 ^ o = k * 2 ^ o + 2 ^ o := Nat.succ_mul _ _
  have hxt : x.2.toNat = rb.toNat + k * 2 ^ o := by rw [hxk]; exact ptrAdd_toNat (by omega)
  omega

theorem retPtrs_rng {rb : ObjRef} {n o : Nat} {q : ObjRef} (hq : q ∈ retPtrs rb n o)
    (hfit : rb.toNat + n * 2 ^ o ≤ 2 ^ 64) : rb.toNat ≤ q.toNat ∧ q.toNat < rb.toNat + n * 2 ^ o := by
  obtain ⟨k, hk, hxk⟩ := retPtrs_mem hq
  have hpo := Nat.two_pow_pos o
  have m2 : (k + 1) * 2 ^ o ≤ n * 2 ^ o := Nat.mul_le_mul_right _ hk
  have e2 : (k + 1) * 2 ^ o = k * 2 ^ o + 2 ^ o := Nat.succ_mul _ _
  have hxt : q.toNat = rb.toNat + k * 2 ^ o := by rw [hxk]; exact ptrAdd_toNat (by omega)
  omega

theorem capAt_some_heap {σ : State Unit} {sl : CslotPtr} {c : Cap} (h : capAt σ sl = some c) :
    (σ.kheap sl.1).isSome = true := by
  unfold capAt at h; cases e : σ.kheap sl.1 with
  | none => rw [e] at h; cases h
  | some _ => rfl

/-! ## The tail -/

set_option maxHeartbeats 2000000 in
/-- **The retype tail keeps `NV N`.** -/
theorem nv_tail {σ : State Unit} (hN : NV N (uV σ)) (hF : UtFitV (uV σ)) {s : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool} {bits fi0 : Nat}
    (hc : capAt σ s = some (.untypedCap dev base bits fi0))
    (hbits : bits < 64) (hfit : base.toNat + 2 ^ bits ≤ 2 ^ 64) (hsz : sz < 64)
    (hlo : base.toNat ≤ rb.toNat)
    (hhi : rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz ≤ base.toNat + 2 ^ bits)
    (hfree : ∀ s' c r, capAt σ s' = some c → r ∈ capRng c →
      r.toNat ∉ utFr base bits (rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat))
    (hfr : ∀ s' c r, capAt σ s' = some c → r ∈ capRng c →
      ¬ (rb.toNat ≤ r.toNat ∧ r.toNat < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz))
    (hheap : ∀ q, (σ.kheap q).isSome = true →
      ¬ (rb.toNat ≤ q.toNat ∧ q.toNat < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz))
    (hanc : ∀ u d b n f, u ≠ s → capAt σ u = some (.untypedCap d b n f) → ∀ k, rb.toNat ≤ k →
      k < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz → k ∈ utR b n →
      s ∈ descendantsOf u σ.cdt ∧ k ∉ utFr b n f)
    (hdst : ∀ d ∈ slots, capAt σ d = some .nullCap ∧ DestRefV (uV σ) d ∧ ∀ x, σ.cdt x ≠ some d)
    (hnd : slots.Nodup) :
    ∀ y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi (.retype s false base rb ty sz slots dev)) σ).1,
      NV N (uV y.2) := by
  intro y hy
  have hfi : unat (rb + (BitVec.ofNat 64 slots.length <<< (fl4ObjBitsApi ty sz)) - base) =
      rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat := fi_new hbits hlo hhi hfit
  have hfitR : rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64 := by omega
  simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
  replace hy := run_returnOk_bind_mem hy
  obtain ⟨x, hx, e⟩ := run_liftE_mem hy
  rw [e]
  -- getCap
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1 hc1; subst s1
  rw [hc] at hc1; cases hc1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  -- the free-index raise
  obtain ⟨x4, hx4, hx⟩ := hx
  have hv4 := hv_setCap _ _ (uV σ) σ rfl x4 hx4
  simp only [bitsOf] at hv4
  rw [hfi] at hv4
  have hN4 : NV N (uV x4.2) := by rw [hv4]; exact nv_setUt hN hc hfree
  have hkey4 : ∀ q, (x4.2.kheap q).isSome = (σ.kheap q).isSome :=
    fun q => congrFun (congrArg (fun w : UView => w.1) hv4) q
  have hcap4 : ∀ sl, capAt x4.2 sl = if sl = s then
      some (.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat))
      else capAt σ sl := by
    intro sl; show (uV x4.2).2.1 sl = _; rw [hv4, vCap_cap]; rfl
  have hcdt4 : x4.2.cdt = σ.cdt := congrArg (fun w : UView => w.2.2.1) hv4
  -- retype_region
  obtain ⟨x5, hx5, hx⟩ := hx
  obtain ⟨hy5, h5⟩ := retypeRegionWith_out hx5
  have hnew : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), (x4.2.kheap q).isSome = false := by
    intro q hq
    rw [hkey4]
    cases e : σ.kheap q with
    | none => rfl
    | some _ => exact absurd (retPtrs_rng hq hfitR) (hheap q (by rw [e]; rfl))
  -- the caps after the retype
  have hsame : ∀ sl, (σ.kheap sl.1).isSome = true → capAt x5.2 sl = capAt x4.2 sl := by
    intro sl hsl
    rcases h5 with e5 | ⟨-, e5⟩
    · rw [e5]
    · rw [e5]
      have hm : sl.1 ∉ retPtrs rb slots.length (fl4ObjBitsApi ty sz) := fun hm => by
        have := hnew _ hm; rw [hkey4, hsl] at this; cases this
      unfold capAt retKh; try dsimp only
      rw [if_neg hm]
  have hnewc : ∀ sl c, capAt x5.2 sl = some c → (σ.kheap sl.1).isSome = false → c = .nullCap ∧ ty ≠ .untyped := by
    intro sl c hsl hn
    have h4n : capAt x4.2 sl = none := by
      rw [hcap4, if_neg]
      · unfold capAt; cases e : σ.kheap sl.1 with
        | none => rfl
        | some _ => rw [e] at hn; cases hn
      · intro e; subst e; rw [capAt_some_heap hc] at hn; cases hn
    rcases h5 with e5 | ⟨hty, e5⟩
    · rw [e5, h4n] at hsl; cases hsl
    · rw [e5] at hsl
      unfold capAt retKh at hsl; try dsimp only at hsl
      split_ifs at hsl with hm
      · exact ⟨default_null hty _ _ _ _ hsl, hty⟩
      · unfold capAt at h4n; rw [h4n] at hsl; cases hsl
  -- init_arch_objects
  obtain ⟨x6, hx6, hx⟩ := hx
  have hv6 : uV x6.2 = uV x5.2 := uk_initArchObjects (uvw := uV x5.2) _ _ _ _ _ _ x5.2 rfl x6 hx6
  rw [hy5] at hx
  have hcdt6 : (uV x6.2).2.2.1 = σ.cdt := by
    rw [hv6]; show x5.2.cdt = _
    rcases h5 with e5 | ⟨-, e5⟩ <;> rw [e5] <;> exact hcdt4
  -- the caps of the loop's start, against σ
  have hold6 : ∀ sl c, (uV x6.2).2.1 sl = some c → c ≠ .nullCap →
      (sl = s ∧ c = .untypedCap dev base bits (rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat)) ∨
        (sl ≠ s ∧ capAt σ sl = some c) := by
    intro sl c hsl hn
    rw [hv6] at hsl
    have hsl' : capAt x5.2 sl = some c := hsl
    by_cases hh : (σ.kheap sl.1).isSome = true
    · rw [hsame sl hh, hcap4] at hsl'
      split_ifs at hsl' with e
      · exact Or.inl ⟨e, (Option.some.inj hsl').symm⟩
      · exact Or.inr ⟨e, hsl'⟩
    · exact absurd (hnewc sl c hsl' (by simpa using hh)).1 hn
  have hkeep6 : ∀ sl, (σ.kheap sl.1).isSome = true → sl ≠ s → (uV x6.2).2.1 sl = capAt σ sl := by
    intro sl hh hs
    rw [hv6]; show capAt x5.2 sl = _
    rw [hsame sl hh, hcap4, if_neg hs]
  have hs6 : (uV x6.2).2.1 s = some (.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat)) := by
    rw [hv6]; show capAt x5.2 s = _
    rw [hsame s (capAt_some_heap hc), hcap4, if_pos rfl]
  have hN6 : NV N (uV x6.2) := by
    rw [hv6]
    refine nv_sameNN (by show x5.2.cdt = x4.2.cdt; rcases h5 with e5 | ⟨-, e5⟩ <;> rw [e5]) (fun sl c hsl hn => ?_)
      (fun sl c hsl hn => ?_) hN4
    · have hsl' : capAt x5.2 sl = some c := hsl
      by_cases hh : (σ.kheap sl.1).isSome = true
      · rw [hsame sl hh] at hsl'; exact hsl'
      · exact absurd (hnewc sl c hsl' (by simpa using hh)).1 hn
    · have hsl' : capAt x4.2 sl = some c := hsl
      have hh : (σ.kheap sl.1).isSome = true := by rw [← hkey4]; exact capAt_some_heap hsl'
      show capAt x5.2 sl = _; rw [hsame sl hh]; exact hsl'
  -- the loop
  have hxr : ∀ x ∈ slots.zip (retPtrs rb slots.length (fl4ObjBitsApi ty sz)), rb.toNat ≤ x.2.toNat ∧ x.2.toNat + 2 ^ fl4ObjBitsApi ty sz ≤
      rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz := fun x hx => zip_rng hx hfitR
  have hinR : ∀ x ∈ slots.zip (retPtrs rb slots.length (fl4ObjBitsApi ty sz)), ∀ k ∈ utR x.2 (fl4ObjBitsApi ty sz),
      rb.toNat ≤ k ∧ k < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz := by
    intro x hx k hk
    have := hxr x hx; have := hk.1; have := hk.2; omega
  have hdout : ∀ d ∈ slots, ¬ (rb.toNat ≤ d.1.toNat ∧ d.1.toNat < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz) :=
    fun d hd => hheap d.1 (capAt_some_heap (hdst d hd).1)
  refine nv_ccLoop ty sz s dev dev base bits _ hsz hbits hfit _ (uV x6.2) hN6 ?_ hs6
    (pw_zip2 _ _ hnd (retPtrs_pw hfitR)) ?_ ?_ ?_ x6.2 rfl _ hx
  · -- fit
    intro u d b n f hu
    rcases hold6 u _ hu ut_nn with ⟨-, e⟩ | ⟨-, hu'⟩
    · cases e; exact ⟨hbits, hfit⟩
    · exact hF u d b n f hu'
  · intro x hx y hy hm
    exact hdout x.1 (List.of_mem_zip hx).1 (hinR y hy _ hm)
  · intro x hx
    refine ⟨by have := hxr x hx; omega, fun k hk => ?_⟩
    have := hinR x hx k hk
    refine ⟨by simp only [utR, Set.mem_setOf_eq]; omega, fun hm => ?_⟩
    have := hm.1; omega
  · intro x hx
    obtain ⟨hdn, hdr, hdk⟩ := hdst x.1 (List.of_mem_zip hx).1
    have hdh := capAt_some_heap hdn
    have hds : x.1 ≠ s := fun e => by rw [e, hc] at hdn; cases hdn
    refine ⟨by rw [hkeep6 _ hdh hds]; exact hdn, ?_, by rw [hcdt6]; exact hdk, hds, ?_, ?_, ?_⟩
    · obtain ⟨s1, c1, hs1, hr1, hz1, hsh1⟩ := hdr
      have hs1s : s1 ≠ s := fun e => by
        rw [e] at hs1; have hs1' : capAt σ s = some c1 := hs1; rw [hc] at hs1'; cases hs1'; simp [sRefs] at hr1
      refine ⟨s1, c1, ?_, hr1, hz1, hsh1⟩
      rw [hkeep6 _ (capAt_some_heap (show capAt σ s1 = some c1 from hs1)) hs1s]; exact hs1
    · intro s' c r hs' hr hm
      rcases hold6 s' c hs' (capRng_nn hr) with ⟨-, rfl⟩ | ⟨-, hs''⟩
      · rw [capRng_ut] at hr; exact hr
      · exact hfr s' c r hs'' hr (hinR x hx _ hm)
    · intro y' c hy' hm
      have hh : (σ.kheap y'.1).isSome = false := by
        cases e : σ.kheap y'.1 with
        | none => rfl
        | some _ => exact absurd (hinR x hx _ hm) (hheap _ (by rw [e]; rfl))
      have hy'' : capAt x5.2 y' = some c := by rw [hv6] at hy'; exact hy'
      obtain ⟨h1, h2⟩ := hnewc y' c hy'' hh
      exact ⟨h1, by simp [h2]⟩
    · intro u d b n f hu hus k hk hkb
      rcases hold6 u _ hus ut_nn with ⟨e, -⟩ | ⟨-, hus'⟩
      · exact absurd e hu
      · rw [hcdt6]
        have := hinR x hx k hk
        exact hanc u d b n f hu hus' k this.1 this.2 hkb

end

end Fl4Proofs.P3.SInvU
