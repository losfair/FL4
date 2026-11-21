/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut3): **AsidControl
MakePool keeps `UtInv'`** (spec side only; imports only Fl4Spec via
SpecInvUtMv).

`perform_asid_control_invocation (MakePool frame slot parent base)` detypes the
parent untyped's region (`detype_PR`: the reset's detype step, under the same
`DetypeOK` [J]), sets the parent's free index to the maximum (`ik_PR_setCap`),
retypes one ASID pool at `frame` (fresh by the reset facts `RSV`), inserts the
pool cap (`ik_capInsert_nonUt`) and writes the ASID table (not in the view).
The decode's facts (`MpOK`): the parent holds an untyped cap of the frame's
4K region, with no CDT child (`ensure_no_children`).
-/
import Fl4Proofs.P3.SpecInvUtMv
import Fl4Proofs.P3.SpecInvUtRsI
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **The detype of a childless untyped cap's region** leaves `UtInv'` and the
reset's facts `RSV` (the first half of `reset_utInv'`). -/
theorem detype_PR {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) {src : CslotPtr} {dev : Bool}
    {b : ObjRef} {n fi : Nat} (hc : capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some src)
    {z : Unit × State Unit} (hz : z ∈ (deleteObjects (Z := Unit) b n σ).1) : PR src dev b n σ.cdt z.2 := by
  obtain ⟨hn, hfit⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc
  obtain ⟨hk', hcdt, -, -⟩ := deleteObjects_kheap hz
  have hcapz : ∀ sl, capAt z.2 sl = if sl.1 ∈ delR b n then none else capAt σ sl := by
    intro sl; unfold capAt; rw [hk' sl.1]; split_ifs <;> rfl
  refine ⟨⟨ik_deleteObjects_utInv b n σ hI.1 z hz, fun c q h => ?_, fun x hx => ?_⟩, ?_⟩
  · have h' : σ.cdt c = some q := by rw [← hcdt]; exact h
    obtain ⟨cap, hcq, hcn⟩ := hI.2.1 c q h'
    refine ⟨cap, ?_, hcn⟩
    show capAt z.2 q = _
    rw [hcapz, if_neg (hDT src dev b n fi hc hk c q h')]; exact hcq
  · have hx' : Relation.TransGen (parentOf σ.cdt) x x := by rw [← hcdt]; exact hx
    exact hI.2.2 x hx'
  · refine rsv_mk hI hc hk ?_ (fun q hq hm => ?_) hcdt (fun s2 c hc2 => ?_)
    · by_cases hm : src.1 ∈ delR b n
      · right; show (z.2.kheap src.1).isSome = false; rw [hk', if_pos hm]; rfl
      · left; exact ⟨fi, by show capAt z.2 src = _; rw [hcapz, if_neg hm]; exact hc⟩
    · have hq' : (z.2.kheap q).isSome = true := hq
      rw [hk', if_pos ((mem_delR_iff hn hfit q).2 hm)] at hq'; cases hq'
    · have hc2' : capAt z.2 s2 = some c := hc2
      rw [hcapz] at hc2'
      split_ifs at hc2'
      exact hc2'

/-- **What the MakePool decode checks**, at the state of the perform. -/
def MpOK (σ : State Unit) : AsidControlInvocation → Prop
  | .makePool frame _slot parent _base =>
    ∃ dev fi, capAt σ parent = some (.untypedCap dev frame page_bits fi) ∧ ∀ c, σ.cdt c ≠ some parent

theorem mpOK_view {σ σ' : State Unit} (h : uV σ' = uV σ) {a : AsidControlInvocation} (hm : MpOK σ a) : MpOK σ' a := by
  cases a with
  | makePool frame slot parent base =>
    obtain ⟨dev, fi, hc, hk⟩ := hm
    have hcap : capAt σ' = capAt σ := congrArg (fun w : UView => w.2.1) h
    have hcdt : σ'.cdt = σ.cdt := congrArg (fun w : UView => w.2.2.1) h
    exact ⟨dev, fi, by rw [hcap]; exact hc, by rw [hcdt]; exact hk⟩

/-- **MakePool keeps `UtInv'`.** -/
theorem makePool_utInv' {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) {a : AsidControlInvocation}
    (hm : MpOK σ a) : ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, UtInv' y.2 := by
  intro y hy
  cases a with
  | makePool frame slot parent base =>
    obtain ⟨dev, fi, hc, hk⟩ := hm
    unfold performAsidControlInvocation at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hP := detype_PR hI hDT hc hk hz
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hxs, hxc⟩ := getCap_capAt hx
    obtain ⟨pcap, s1⟩ := x
    simp only at hxs hxc; subst hxs
    obtain ⟨hR1, hR2, hR3, hR4, hR5, hR6, hR7⟩ := hP.2
    have hex : (z.2.kheap parent.1).isSome = true := by
      unfold capAt at hxc; cases e : z.2.kheap parent.1 with
      | none => rw [e] at hxc; cases hxc
      | some _ => rfl
    obtain ⟨f, hf⟩ := hR1.resolve_right (fun e => by
      have e' : (z.2.kheap parent.1).isSome = false := e; rw [hex] at e'; cases e')
    have hpc : pcap = .untypedCap dev frame page_bits f := Option.some.inj (hxc.symm.trans hf)
    subst hpc
    obtain ⟨z2, hz2, hy⟩ := hy
    have hP2 : PR parent dev frame page_bits σ.cdt z2.2 :=
      ik_PR_setCap (f := 2 ^ page_bits) (le_refl _) z.2 hP z2 hz2
    obtain ⟨z3, hz3, hy⟩ := hy
    obtain ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7⟩ := hP2.2
    have hc2 : capAt z2.2 parent = some (.untypedCap dev frame page_bits (2 ^ page_bits)) := by
      have := (hv_setCap _ _ (uV z.2)) z.2 rfl z2 hz2
      show (uV z2.2).2.1 parent = _
      rw [this, vCap_cap, if_pos rfl]; rfl
    have hnew : ∀ q ∈ retPtrs frame 1 (objBitsApi (.archObject .asidPoolObj) 0), z2.2.kheap q = none ∧
        ∀ sl d b m f, capAt z2.2 sl = some (.untypedCap d b m f) → q.toNat ∉ utFr b m f := by
      intro q hq
      simp only [retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton, Nat.zero_mul] at hq
      subst hq
      have hq0 : (ptrAdd frame 0).toNat = frame.toNat := by
        unfold ptrAdd; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt frame.isLt]
      have hin : (ptrAdd frame 0).toNat ∈ utR frame page_bits := by
        rw [hq0]; exact ⟨le_refl _, by have : 0 < 2 ^ page_bits := Nat.two_pow_pos _; omega⟩
      refine ⟨?_, fun sl d b m f' hsl hm => ?_⟩
      · cases e : z2.2.kheap (ptrAdd frame 0) with
        | none => rfl
        | some _ => exact absurd hin (hS2 _ (by show (z2.2.kheap _).isSome = true; rw [e]; rfl))
      · by_cases e : sl = parent
        · subst e; rw [hc2] at hsl; cases hsl
          have := hm.1; have := hm.2; omega
        · exact (hS5 sl d b m f' e hsl).1 _ hin hm
    have hret := utInv'_retype (bA := objBitsApi) hP2.1 hnew (y := z3) hz3
    refine (ik_bind (ik_capInsert_nonUt _ (fun _ _ _ _ h => by cases h) parent slot) fun _ => ?_) z3.2 hret.1 y hy
    repeat' ik_step0

end

end Fl4Proofs.P3.SInvU
