/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut8): **`perfGap : PerfGap`
and `UtInv3` across the kernel entries with no premise** (spec side only;
imports SpecInvUtP5).

* The reset (`reset_untyped_cap` of a childless untyped): `RNV` (`NV N`, the
  source still holds its untyped cap, the CDT unchanged, every non-null cap is the
  source's or one of the decode state's, every slot outside the region and not the
  source unchanged) holds at every outcome (`nv_reset`; `rnv_setCap`: the
  free-index writes keep it, since no cap covers the childless untyped's region).
* **`p3_invokeUntyped`**: `invoke_untyped` keeps `P3 N` from the decode's facts
  (`UtRetOKV ∧ DestNullV ∧ UtOKN`), with or without reset: `UtInv'` by ut2's
  `invokeUntyped_utInv'` / `invokeUntyped_reset_utInv'` (`detypeOK_of`), `NV N` by
  `nv_tail` (after the reset, at its outcome, from `RNV` and ut2's `RSV`).
* `GapOKN` / `okv_fl4DecodeG`: the decode establishes the untyped and arch facts.
* **`perfGap : PerfGap`**, **`kentry_utInv2`**, **`kcall_utInv2`** (no premise).
-/
import Fl4Proofs.P3.SpecInvUtP5
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The reset -/

/-- The reset's carried facts for `NV N` (decode state `σ0`, source `src`, region `(b, n)`). -/
def RNV (N : Irq → ObjRef) (σ0 : State Unit) (src : CslotPtr) (dev : Bool) (b : ObjRef) (n : Nat) (w : UView) : Prop :=
  NV N w ∧ (∃ f, w.2.1 src = some (.untypedCap dev b n f)) ∧ w.2.2.1 = σ0.cdt ∧
  (∀ s c, w.2.1 s = some c → c ≠ .nullCap → s = src ∨ capAt σ0 s = some c) ∧
  (∀ s, s ≠ src → s.1 ∉ delR b n → w.2.1 s = capAt σ0 s)

section Rnv
variable {N : Irq → ObjRef} {σ0 : State Unit} {src : CslotPtr} {dev : Bool} {b : ObjRef} {n : Nat}

theorem rnv_setCap (hClr : ∀ s c r, capAt σ0 s = some c → r ∈ capRng c → r ∉ delR b n)
    (hpd : ∀ r, r ∈ delR b n ↔ r.toNat ∈ utR b n) {f' : Nat} :
    IK (fun s => RNV N σ0 src dev b n (uV s)) (setCap (Z := Unit) (.untypedCap dev b n f') src) := by
  intro σ hσ y hy
  have e := hv_setCap _ _ (uV σ) σ rfl y hy
  show RNV N σ0 src dev b n (uV y.2)
  rw [e]
  obtain ⟨hN, ⟨f, hf⟩, hcdt, hsub, hkeep⟩ := hσ
  refine ⟨nv_setUt hN hf ?_, ⟨f', by rw [vCap_cap, if_pos rfl]⟩, hcdt, ?_, ?_⟩
  · intro s c r hs hr hm
    rcases hsub s c hs (capRng_nn hr) with rfl | hs0
    · rw [hf] at hs; cases hs; rw [capRng_ut] at hr; exact hr
    · exact hClr s c r hs0 hr ((hpd r).2 (utFr_sub hm))
  · intro s c hs hn
    rw [vCap_cap] at hs
    split_ifs at hs with e
    · exact Or.inl e
    · exact hsub s c hs hn
  · intro s hs hd
    rw [vCap_cap, if_neg hs]; exact hkeep s hs hd

theorem rnv_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) :
    IK (fun s => RNV N σ0 src dev b n (uV s)) m :=
  ik_of_uk (fun _ _ e h => by rw [e]; exact h) h

end Rnv

macro "rnv_auto" : tactic => `(tactic| repeat' (first
  | (exact rnv_setCap (by assumption) (by assumption))
  | (exact ik_doMachineOp (fun _ _ h => h) _)
  | (exact rnv_uk fun _ => uk_preemptionPoint)
  | (exact rnv_uk fun _ => uk_archPostResetUntyped _ _)
  | (refine ike_mapMEx_mem _ fun _ _ => ?_)
  | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE)))

variable {N : Irq → ObjRef}

/-- **`reset_untyped_cap` of a childless untyped keeps `RNV`** (every outcome). -/
theorem nv_reset {σ : State Unit} (hP : P3 N σ) {src : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some src) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) src) σ).1, RNV N σ src dev b n (uV y.2) := by
  obtain ⟨⟨hI, hN⟩, hO⟩ := hP
  obtain ⟨hn, hfit⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc
  have hpd := mem_delR_iff hn hfit
  have hClr := clear_of_childless hN hc hk
  have hRN := regNull_of hN.1 hN.2.1 src dev b n fi hc hk
  have hsout : src.1 ∉ delR b n := fun h => by cases hRN src _ hc h
  intro y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s⟩ := x
  obtain ⟨hs, hcx⟩ := getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨⟨hN, hO⟩, ⟨fi, hc⟩, rfl, fun s c hs _ => Or.inr hs, fun s _ _ => rfl⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    simp only [bitsOf, objRefOf] at hz
    obtain ⟨hk', hcdt, -, -⟩ := deleteObjects_kheap hz
    have hcapz : ∀ sl, capAt z.2 sl = if sl.1 ∈ delR b n then none else capAt σ sl := by
      intro sl; unfold capAt; rw [hk' sl.1]; split_ifs <;> rfl
    have hz0 : RNV N σ src dev b n (uV z.2) := by
      refine ⟨nv_sameNN (w := uV σ) hcdt (fun s c hs hn => ?_) (fun s c hs hn => ?_) ⟨hN, hO⟩,
        ⟨fi, by show capAt z.2 src = _; rw [hcapz, if_neg hsout]; exact hc⟩, hcdt, fun s c hs _ => ?_,
        fun s _ hd => by show capAt z.2 s = _; rw [hcapz, if_neg hd]⟩
      · have hs' : capAt z.2 s = some c := hs
        rw [hcapz] at hs'; split_ifs at hs'; exact hs'
      · show capAt z.2 s = some c
        rw [hcapz, if_neg]; · exact hs
        intro h; exact hn (hRN s c hs h)
      · right
        have hs' : capAt z.2 s = some c := hs
        rw [hcapz] at hs'; split_ifs at hs'; exact hs'
    refine (?_ : IKE (fun s => RNV N σ src dev b n (uV s)) _) z.2 hz0 y hy
    rnv_auto

/-! ## `invoke_untyped` -/

theorem run_returnOk_bind_mem' {ε α β : Type} {a : α} {g : α → NonDetE (State Unit) ε β}
    {σ : State Unit} {y : Except ε β × State Unit} (hy : y ∈ (ExceptT.run (g a) σ).1) :
    y ∈ (ExceptT.run (NonDetE.returnOk a >>= g) σ).1 := by
  rw [ExceptT.run_bind]
  exact ⟨(.ok a, σ), rfl, hy⟩

/-- What the untyped perform needs from the decode. -/
def UtGapOK (w : UView) (ui : UntypedInvocation) : Prop := UtRetOKV w ui ∧ DestNullV w ui ∧ UtOKN w ui

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps `P3 N`** from the decode's facts. -/
theorem p3_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hP : P3 N σ) (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, P3 N y.2 := by
  intro y hy
  obtain ⟨h1, h2, h3⟩ := hok
  obtain ⟨⟨hI, hN⟩, hO⟩ := hP
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hok' := h1
  obtain ⟨bits, fi, hc, ho, hw1, hrb, hw, hr⟩ := hok'
  have hc' : capAt σ s = some (.untypedCap dev base bits fi) := hc
  obtain ⟨bits', fi', hc'', hfit, h1r, hal, h3r⟩ := utRet_region hI.1.2.1 (utRetOK_of_V h1)
  rw [hc'] at hc''; cases hc''
  obtain ⟨hbits, -⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc'
  obtain ⟨hsz, s1, nc, off, win, hs1, hcn, hle, he⟩ := h3
  obtain ⟨hnd, hDR⟩ := utDest_of hN.2.2.2.2.2.2 hs1 hcn hle he
  have hpd := mem_delR_iff hbits hfit
  have hF : UtFitV (uV σ) := fun u d b n f h => UtWf.fit (σ := σ) hI.1.2.1 h
  have hdst0 : ∀ d ∈ slots, capAt σ d = some .nullCap ∧ DestRefV (uV σ) d ∧ ∀ x, σ.cdt x ≠ some d := by
    intro d hd
    have hn : capAt σ d = some .nullCap := h2 d hd
    refine ⟨hn, hDR d hd, fun x hx => ?_⟩
    obtain ⟨c', hc1, hcn'⟩ := hI.2.1 x d hx
    have hc1' : capAt σ d = some c' := hc1
    rw [hn] at hc1'; cases hc1'; exact hcn' rfl
  -- UtInv'
  have hU : UtInv' y.2 := by
    cases reset
    · exact invokeUntyped_utInv' hI (utRetOK_of_V h1) (destNull_of_V h2) y hy
    · exact invokeUntyped_reset_utInv' hI (detypeOK_of ⟨hI, hN⟩) (utRetOK_of_V h1) (destNull_of_V h2) y hy
  refine (fun hNV : NV N (uV y.2) => ⟨⟨hU, hNV.1⟩, hNV.2⟩) ?_
  cases reset
  · -- no reset
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1r
    have hfi1 : fi ≤ rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat := by omega
    refine nv_tail ⟨hN, hO⟩ hF hc' hbits hfit hsz (by omega) h3r ?_ ?_ ?_ ?_ hdst0 hnd y hy
    · intro s' c r hs' hr hm
      exact hN.2.2.1 s dev base bits fi hc s' c r hs' hr (utFr_mono hfi1 hm)
    · intro s' c r hs' hr hm
      exact hN.2.2.1 s dev base bits fi hc s' c r hs' hr ⟨by omega, by omega⟩
    · intro q hq hm
      exact hI.1.1 s dev base bits fi hc q hq ⟨by omega, by omega⟩
    · intro u d b n f hu hus k hk1 hk2 hkb
      have hkf : k ∈ utFr base bits fi := ⟨by omega, by omega⟩
      rcases hI.1.2.2.2.1 s u dev base bits fi d b n f (Ne.symm hu) hc hus ⟨k, utFr_sub hkf, hkb⟩ with
        ⟨-, hr'⟩ | ⟨hd, hr'⟩
      · exact absurd hkf (hr' k hkb)
      · exact ⟨hd, hr' k (utFr_sub hkf)⟩
  · -- reset
    have hk : ∀ c, σ.cdt c ≠ some s := hr rfl
    simp only [↓reduceIte, Nat.add_zero] at h1r
    have hClr := clear_of_childless hN hc hk
    have hRN := regNull_of hN.1 hN.2.1 s dev base bits fi hc hk
    simp only [invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hRz := nv_reset ⟨⟨hI, hN⟩, hO⟩ hc' hk z hz
    have hPz := reset_utInv' hI (detypeOK_of ⟨hI, hN⟩) hc' hk z hz
    obtain ⟨r, s2⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hRz.1)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hRz.1)
    | ok u => ?_
    try dsimp only at hy
    have hy' : y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi
        (.retype s false base rb ty sz slots dev)) s2).1 := by
      simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte]
      exact run_returnOk_bind_mem' hy
    obtain ⟨hNz, ⟨f2, hf2⟩, hcdtz, hsub, hkeep⟩ := hRz
    obtain ⟨hIz, hRS⟩ := hPz
    change RSV s dev base bits σ.cdt (uV s2) at hRS
    obtain ⟨-, hR2, hR3, -, hR5, -, -⟩ := hRS
    have hclr2 : ∀ s' c r, capAt s2 s' = some c → r ∈ capRng c → r ∉ delR base bits := by
      intro s' c r hs' hr
      rcases hsub s' c hs' (capRng_nn hr) with rfl | hs0
      · have hs'' : (uV s2).2.1 s' = some c := hs'
        rw [hf2] at hs''; cases hs''; rw [capRng_ut] at hr; exact hr.elim
      · exact hClr s' c r hs0 hr
    refine nv_tail hNz (fun u d b n f h => UtWf.fit (σ := s2) hIz.1.2.1 h) hf2 hbits hfit hsz (by omega) h3r
      ?_ ?_ ?_ ?_ ?_ hnd y hy'
    · intro s' c r hs' hr hm
      exact hclr2 s' c r hs' hr ((hpd r).2 (utFr_sub hm))
    · intro s' c r hs' hr hm
      exact hclr2 s' c r hs' hr ((hpd r).2 ⟨by omega, by omega⟩)
    · intro q hq hm
      exact hR2 q hq ⟨by omega, by omega⟩
    · intro u d b n f hu hus k hk1 hk2 hkb
      obtain ⟨hA, hB⟩ := hR5 u d b n f hu hus
      have hkr : k ∈ utR base bits := ⟨by omega, by omega⟩
      rw [show s2.cdt = σ.cdt from hR3]
      exact ⟨hB ⟨k, hkr, hkb⟩, hA k hkr⟩
    · intro d hd
      obtain ⟨hn, ⟨t1, c1, ht1, hr1, hz1, hsh1⟩, hl⟩ := hdst0 d hd
      have hds : d ≠ s := fun e => by rw [e, hc'] at hn; cases hn
      have hdout : d.1 ∉ delR base bits := hClr t1 c1 d.1 ht1 (sRefs_sub_capRng _ hr1)
      have ht1s : t1 ≠ s := fun e => by
        rw [e] at ht1; have ht1' : capAt σ s = some c1 := ht1; rw [hc'] at ht1'; cases ht1'; simp [sRefs] at hr1
      have ht1out : t1.1 ∉ delR base bits := fun h => sRefs_nn hr1 (hRN t1 c1 ht1 h)
      refine ⟨?_, ⟨t1, c1, ?_, hr1, hz1, hsh1⟩, ?_⟩
      · show (uV s2).2.1 d = _; rw [hkeep d hds hdout]; exact hn
      · rw [hkeep t1 ht1s ht1out]; exact ht1
      · show ∀ x, (uV s2).2.2.1 x ≠ some d
        rw [hcdtz]; exact hl

/-! ## The decode and `PerfGap` -/

/-- The decode facts of the untyped and arch performs. -/
def GapOKN (w : UView) : Fl4Invocation → Prop
  | .invokeUntyped ui => UtGapOK w ui
  | .invokeArchObject ai => ArchOKN w ai
  | _ => True

set_option maxHeartbeats 4000000 in
theorem okv_fl4DecodeG {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : w.2.1 sl = some cap)
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (GapOKN w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  have hcps : ∀ c ∈ ex.map Prod.fst, ∃ s, w.2.1 s = some c := by
    intro c h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨p.2, hex p hp⟩
  cases cap with
  | untypedCap d p n f =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_mono (okv_and (okv_decodeUntyped label args sl _ hc)
      (okv_decodeUntypedN label args sl _ _ hcps)) fun _ h => ⟨h.1.1, h.1.2, h.2⟩)
  | archObjectCap ac =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_fl4ArchDecodeN label args ci sl ac ex hc hex)
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

/-- **The untyped and arch performs keep `P3 N`** (ut7's remaining obligation, proved). -/
theorem perfGap : PerfGap := by
  intro N blk call don inv σ hgap hI hN hD
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) inv :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv inv s0 hmem
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact p3_invokeUntyped ui σ hI hf z hz
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    by_cases hm : ∃ a, ai = .spec (.invokeASIDControl a)
    · obtain ⟨a, rfl⟩ := hm
      simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      exact p3_makePool hI hf z hz
    · exact p3_fl4ArchPerform ai (fun a e => hm ⟨a, e⟩) σ hI hf y hy
  | _ => exact (hgap : False).elim

/-- **`UtInv3` across the syscall entry** (no premise). -/
theorem kentry_utInv2 (c : Syscall) {σ : State Unit} (hI : UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, UtInv3 y.2 :=
  kentry_utInv2_of perfGap c hI

/-- **`UtInv3` across every kernel event** (no premise). -/
theorem kcall_utInv2 (rep : Bool) (ev : Event) {σ : State Unit} (hI : UtInv3 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, UtInv3 y.2 :=
  kcall_utInv2_of perfGap rep ev hI

end

end Fl4Proofs.P3.SInvU
