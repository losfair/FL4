/-
P3 (DESIGN.md §9), invariant line G1 (sb2): **`scGap : ScGap`** and the tops
**`kentry_scInv` / `kcall_scInv`** with no gap (spec side only; imports
SpecInvSbX4).

* `gapOK_of`: ut8's decode facts `GapOKN` at the perform state (the decode's
  view equals it through `Rel`).
* `si_tcSched_nb`: a `threadControlSched` with no new SC (no bind) keeps
  `ScInv` by the SIK family.
* **`scGap`**: untyped (`sc_invokeUntyped`: ut1's freshness; the reset's region
  holds no bound object by `ScLive` + UtCh), MakePool (`sc_makePool`, the same),
  the other arch performs (frames), SC bind (`sg_scBind`), threadControlSched
  (`sg_tcSched`: the old fault handler of a TCB is valid by the entry's
  `VfhAll`, so its `cap_delete` keeps the binding).
* Tops (premises: `ScInv` (carried), `UtInv3` (ut8, carried), `VfhAll` (vfh3,
  carried), **`ScLive` [J]** (not carried yet; KENTRY-PLAN sb2)).
-/
import Fl4Proofs.P3.SpecInvSbX4
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem gapOK_of {σe σ : State Unit} {inv : Fl4Invocation} (hD : DecFrom σe inv) (hR : Rel σe σ) :
    SInvU.GapOKN (SInvU.uV σ) inv := by
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hR0, hc, hex, hm⟩ := hD
  have hv : SInvU.uV σ0 = SInvU.uV σ := hR0.1.trans hR.1.symm
  exact SInvU.okv_fl4DecodeG (w := SInvU.uV σ) fp label args ci sl cap ex buf (by rw [← hv]; exact hc)
    (fun p hp => by rw [← hv]; exact (hex p hp).1) σ0 hv inv s0 hm

theorem si_tcSched_nb (blk call don : Bool) (t : ObjRef) (sl : CslotPtr) (fh : Option (Cap × CslotPtr))
    (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef)) (h : ∀ c, sc ≠ some (some c)) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.threadControlSched t sl fh mcp prio sc))) := by
  rcases sc with _ | _ | c
  · simp only [fl4PerformInvocation, invokeTcb]
    refine ike_bind (si_installTcbCap _ _ _ _) fun _ => ike_bind (ike_liftE (sik_of_sbk fun _ => by sb_auto)) fun _ =>
      ike_bind (ike_liftE (sik_of_sbk fun _ => by sb_auto)) fun _ => ike_bind (ike_liftE ?_) fun _ => ike_returnOk _
    unfold NonDet.maybeM; exact ik_pure _
  · simp only [fl4PerformInvocation, invokeTcb]
    refine ike_bind (si_installTcbCap _ _ _ _) fun _ => ike_bind (ike_liftE (sik_of_sbk fun _ => by sb_auto)) fun _ =>
      ike_bind (ike_liftE (sik_of_sbk fun _ => by sb_auto)) fun _ => ike_bind (ike_liftE ?_) fun _ => ike_returnOk _
    unfold NonDet.maybeM
    (try dsimp only)
    exact ik_bind (sik_of_sbk fun _ => by sb_auto) fun _ => ik_bind (ik_assertOpt _) fun _ => sik_schedContextUnbindTcb _
  · exact absurd rfl (h c)

/-- **The gap is closed.** -/
theorem scGap : ScGap := by
  intro blk call don inv σe σ hg hE hD hI hR y hy
  have hU : SInvU.UtInv'' σ := by show SInvU.UtInv''V (SInvU.uV σ); rw [hR.1]; exact hE.ut.1
  have hL : ScLive σ := scLive_keep hE.live hR.1 hR.2
  have hB := bindOK_of hD hR
  cases inv with
  | invokeUntyped ui =>
    have hf := gapOK_of hD hR
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := SInvU.mem_ret_bindE hy
    rw [e]
    exact sc_invokeUntyped ui σ hU.ut'.ut (by cases ui; exact hf.1)
      (fun s dev b n fi hc hk => unb_of_live hU hL hc hk) hI z hz
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    by_cases hm : ∃ a, ai = .spec (.invokeASIDControl a)
    · obtain ⟨a, rfl⟩ := hm
      have hf := gapOK_of hD hR
      cases a with
      | makePool frame slot parent base =>
        obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hf
        have hfr : frame ∈ SInvU.delR frame page_bits := by
          obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.ut'.ut.2.1 hc
          exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
        simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
        obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
        obtain ⟨z, hz, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hx]
        exact sc_makePool frame slot parent base σ (unb_of_live hU hL hc hk) hfr hI z hz
    · exact si_archNonMP ai (fun a e => hm ⟨a, e⟩) σ hI y hy
  | invokeSchedContext i =>
    cases i with
    | invokeSchedContextBind c cap => exact sg_scBind blk call don c cap σ hI hB y hy
    | _ => exact (hg : False).elim
  | invokeTCB i =>
    cases i with
    | threadControlSched t sl fh mcp prio sc =>
      rcases sc with _ | _ | c
      · exact si_tcSched_nb blk call don t sl fh mcp prio none (fun _ h => by cases h) σ hI y hy
      · exact si_tcSched_nb blk call don t sl fh mcp prio (some none) (fun _ h => by cases h) σ hI y hy
      · refine sg_tcSched blk call don t sl fh mcp prio _ σ hI hB (fun c0 hc0 => ?_) y hy
        obtain ⟨x, hx, -⟩ := bv_t.1 hB.2
        obtain ⟨x0, hx0⟩ := hR.2.tcb' t x hx
        rw [hR.capAt, capAt_fh hx0] at hc0
        cases hc0
        exact fhC_of_valid (hE.vfh t x0 hx0)
    | _ => exact (hg : False).elim
  | _ => exact (hg : False).elim

/-! ## Tops -/

/-- **`ScInv` across the syscall entry.** Premises: `ScInv`, `UtInv3`, `VfhAll`
(carried by sb1/sb2, ut8, vfh3) and **`ScLive` [J]** (l4v `if_live_then_nonz_cap`
at bound TCBs / SCs with `valid_global_refs`; not carried yet). -/
theorem kentry_scInv (c : Syscall) {σ : State Unit} (hI : ScInv σ) (hU : SInvU.UtInv3 σ) (hV : VfhAll σ)
    (hL : ScLive σ) : ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScInv y.2 :=
  kentry_scInv_of scGap c ⟨hI, hU, hV, hL⟩

/-- **`ScInv` across every kernel event.** -/
theorem kcall_scInv (rep : Bool) (ev : Event) {σ : State Unit} (hI : ScInv σ) (hU : SInvU.UtInv3 σ)
    (hV : VfhAll σ) (hL : ScLive σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScInv y.2 :=
  kcall_scInv_of scGap rep ev ⟨hI, hU, hV, hL⟩

theorem kentry_scSym (c : Syscall) {σ : State Unit} (hI : ScInv σ) (hU : SInvU.UtInv3 σ) (hV : VfhAll σ)
    (hL : ScLive σ) : ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScSym y.2 :=
  fun y hy => (kentry_scInv c hI hU hV hL y hy).1

theorem kcall_scSym (rep : Bool) (ev : Event) {σ : State Unit} (hI : ScInv σ) (hU : SInvU.UtInv3 σ)
    (hV : VfhAll σ) (hL : ScLive σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScSym y.2 :=
  fun y hy => (kcall_scInv rep ev hI hU hV hL y hy).1

end

end Fl4Proofs.P3.SInvB
