/-
P3 (DESIGN.md §9), invariant line G1 (ctq3): **TQ across the untyped retype,
its reset and MakePool** (spec side only, outside the JAtZ cone).

* No reset: `retype_region` writes only addresses holding no object (ut1's
  `utRet_fresh`), and TQ puts every queued thread at a TCB, so no queued
  thread is overwritten (`tqx_retypeRegionWith_p`; ctq2's `q1_of_keep` is the
  same argument for T1).
* Reset / MakePool: `delete_objects` of a childless untyped cap's region.
  **`rqDet_of_live`**: a queued thread is runnable (TQ), so live, so some cap
  names it (`IfLiveTN`), so it is outside every childless untyped's region
  (ut4's UtCh in `UtInv''`: a cap naming an object of an untyped's region is
  a CDT descendant of that untyped) — nq2's `nqDet_of_live` for the ready
  queues.
* `IfLiveTN` is nq3's statement of IfLiveT (KENTRY-PLAN nq3) verbatim; the
  il1 line's `IfLiveT` (every live TCB holds a thread cap) implies it.
-/
import Fl4Proofs.P3.SpecInvCqJ
import Fl4Proofs.P3.SpecInvNtfnQH2
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **IfLiveTN [J]** (l4v `if_live_then_nonz_cap` at TCBs inside an untyped
region; nq3's IfLiveT statement, KENTRY-PLAN nq3): a TCB whose state is
neither Inactive nor IdleThreadState and that lies in some untyped cap's
region is named by some cap. -/
def IfLiveTN (σ : State Unit) : Prop :=
  ∀ t y, σ.kheap t = some (.tcb y) → y.tcbState ∉ ({.inactive, .idleThreadState} : Set ThreadState) →
    SInvU.InUtV (SInvU.uV σ) t → ∃ s c, SInvU.capAt σ s = some c ∧ t ∈ objRefs c

/-- **No queued thread in a childless untyped's region.** -/
theorem rqDet_of_live {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : IfLiveTN σ) (hR : RQd σ)
    {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) :
    ∀ d p t, t ∈ σ.readyQueues d p → t ∉ SInvU.delR b n := by
  intro d p t ht hm
  obtain ⟨y, hy, -, -, hr⟩ := hR d p t ht
  have hl : y.tcbState ∉ ({.inactive, .idleThreadState} : Set ThreadState) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h] at hr <;> simp [runnable] at hr
  obtain ⟨s, c, hs, hr'⟩ := hL t y hy hl ⟨u, dev, b, n, fi, hc, hm⟩
  exact SInvU.desc_noKids hk (hU.2.1 u dev b n fi hc s c t hs (SInvU.objRefs_sub_capRng c hr') hm)

theorem rqd_fresh {σ : State Unit} (h : RQd σ) {q : ObjRef} (hq : σ.kheap q = none) :
    ∀ d p, q ∉ σ.readyQueues d p := fun d p hp => by
  obtain ⟨x, hx, -⟩ := h d p q hp
  rw [hq] at hx; cases hx

/-- `reset_untyped_cap` of a slot whose untyped region holds no queued thread. -/
theorem tq_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi))
    (hD : ∀ d p t, t ∈ σ.readyQueues d p → t ∉ SInvU.delR b n) :
    IKp TQ σ (ExceptT.run (resetUntypedCap (Z := Unit) s)) := by
  intro hσ y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := SInvU.run_liftE_bind_mem hy
  obtain ⟨cap, s'⟩ := x
  obtain ⟨hs, hcx⟩ := SInvU.getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := SInvU.run_returnOk_bind_mem hy
  replace hy := SInvU.run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hσ
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hz0 : TQ z.2 := tqx_deleteObjects_p b n σ hD hσ z hz
    refine (?_ : TQKE _) z.2 hz0 y hy
    try dsimp only
    tq_auto

/-- The untyped retype's body after the reset, from a state where the retype addresses hold no object. -/
theorem tq_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit) (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) :
    IKp TQ σ (do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) := by
  intro hσ x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : TQ x4.2 := tqx_setCap _ _ _ hσ x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := tqx_retypeRegionWith_p (X := TT) fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by
      have hn : x4.2.kheap q = none := by have := hk4 q; rw [hfr q hq] at this; simpa using this
      exact rqd_fresh hb4.1 hn) hb4 x5 hx5
  refine (?_ : TQK _) x5.2 hb5 _ hx
  tq_auto

/-- **`invoke_untyped`** from the decode's facts (`UtRetOK`, ut1), `UtInv`
and, for a reset, no queued thread in the source untyped's region. -/
theorem tq_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hI : SInvU.UtInv σ)
    (hok : SInvU.UtRetOK σ ui)
    (hD : ∀ u dev b n fi, SInvU.capAt σ u = some (.untypedCap dev b n fi) → (∀ c, σ.cdt c ≠ some u) →
      ∀ d p t, t ∈ σ.readyQueues d p → t ∉ SInvU.delR b n) :
    IKp TQ σ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui)) := by
  intro hσ y hy
  cases ui with
  | retype s reset base rb ty sz slots dev =>
    cases reset
    · have hfr := SInvU.utRet_fresh hI hok
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
      replace hy := SInvU.run_returnOk_bind_mem hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact tq_utBody s base rb ty sz slots dev σ hfr hσ x hx
    · have hok' := hok
      obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := hok'
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
      rw [ExceptT.run_bind] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have hbz := tq_resetUntypedCap s hc (hD _ _ _ _ _ hc (hr rfl)) hσ z hz
      have hfz := SInvU.utRet_fresh_after_reset hI hok z hz
      obtain ⟨r, s1⟩ := z
      cases r with
      | error e =>
        first
          | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
          | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
      | ok u =>
        try dsimp only at hy
        obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
        exact tq_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-- **MakePool** (`perform_asid_control_invocation`): the frame region holds
no queued thread, and it contains the frame. -/
theorem tq_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit)
    (hD : ∀ d p t, t ∈ σ.readyQueues d p → t ∉ SInvU.delR frame page_bits)
    (hf : frame ∈ SInvU.delR frame page_bits) :
    IKp TQ σ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  intro hσ y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := tqx_deleteObjects_p (X := TT) frame page_bits σ hD hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := deleteObjects_out h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hf]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : TQ y3.2 := tqx_setCap _ _ _ hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := tqx_retypeRegionWith_p (X := TT) objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'
    exact rqd_fresh hb3.1 hn3) hb3 y4 h4
  refine (?_ : TQK _) y4.2 hb4 y hy
  tq_auto

/-- MakePool's facts from the decode's (the parent slot holds a childless
untyped cap of page size at the frame: nq3's `NqDec`). -/
theorem rqMp_of {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : IfLiveTN σ) (hR : RQd σ) {parent : CslotPtr}
    {dev : Bool} {frame : ObjRef} {fi : Nat}
    (hc : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi))
    (hk : ∀ c, σ.cdt c ≠ some parent) :
    (∀ d p t, t ∈ σ.readyQueues d p → t ∉ SInvU.delR frame page_bits) ∧ frame ∈ SInvU.delR frame page_bits := by
  refine ⟨rqDet_of_live hU hL hR hc hk, ?_⟩
  obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc
  exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩

end

end Fl4Proofs.P3.SInvQ
