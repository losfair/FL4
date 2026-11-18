/-
P3: **P1's `UtRetypeP3` from P3's retype** (the untyped family's retype
for P1's kernel entry), against `run (hP3 : UtP3Ok …)`.

* `UtP3Ok`: what the joint simulation knows at the untyped decode's start
  state: the relations (`StateRel`, `SlotsValid`, `Placed`, `MdbLinks`,
  `CdtRel`, `MdbInv`, `UtInv`), the joint cover `JCovD`, the invoked slot an
  abstract slot holding the untyped cap, and the extra caps related.
* `dest_of_retype_dest`, `retCtx_of_args`: P1's decode facts (`UtArgs`) and
  the relations give the CSpace proofs' `RetCtx` (the arguments `retype`
  gets, as `untyped_decode_refines_with` derives them).
-/
import Fl4Proofs.P3.RetypePlace
import Fl4Proofs.P1.QueueUtRetype
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The destination CNode of a successful `retype_dest`**: a CNode of the
typed heap, of radix `r` (below 64, nonzero), the window within it. -/
theorem dest_of_retype_dest {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s))
    {x : U64} {c : capability.Cap} {a : Fl4Spec.Cap} (hc : capAt (L.mem s) x = ok c) (hca : CapRel c a)
    (hcv : CapValid th c) {idx dep off win dest : U64}
    (h : untyped.retype_dest st s x idx dep off win = ok (.Ok dest)) :
    ∃ r : Nat, th dest = some (.cnode r) ∧ r < 64 ∧ r ≠ 0 ∧ 1 ≤ win.val ∧ win.val ≤ 256 ∧
      off.val + win.val ≤ 2 ^ r := by
  -- the node cap, and `retype_dest` as its tail
  have key : ∃ nc, CapWf nc ∧ CapValid th nc ∧ untyped.retype_dest st s x idx dep off win = ok (tailOf dep off win nc) := by
    by_cases h0 : dep = 0#u64
    · subst h0; exact ⟨c, hca.1, hcv, retype_dest_zero s x idx off win c hc hca.1⟩
    obtain ⟨r, hr, e1, -, hrel⟩ := spec_exists
      (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false c a hca hcv idx dep)
    have hl' : cspace.lookup_target_slot st s c idx dep = ok r := hr
    cases r with
    | Err e =>
      rw [retype_dest_err s x idx dep off win h0 c hc e hl'] at h; simp only [ok.injEq, reduceCtorEq] at h
    | Ok v =>
      cases e1 with
      | error _ => exact hrel.elim
      | ok sl' =>
        obtain ⟨rfl, pp, hpp1, hpp, -⟩ := hrel
        obtain ⟨c', a', hc', hca', -⟩ := hR.slot_cap hpp1 hpp
        have hcv' : CapValid th c' := hV.abs ⟨pp, hpp1, Or.inl hpp⟩ hc'
        exact ⟨c', hca'.1, hcv', retype_dest_ok s x idx dep off win h0 c hc _ hl' c' hc' hca'.1⟩
  obtain ⟨nc, hw, hv, he⟩ := key
  rw [he] at h
  cases nc with
  | CNode ptr r gs g =>
    obtain ⟨hth, hr0⟩ := hv
    have hr64 : r.val < 64 := hw.1
    have hpow1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
    simp only [tailOf, destRes] at h
    split_ifs at h with e1 e2 e3 <;> simp only [ok.injEq, reduceCtorEq, core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨r.val, hth, hr64, hr0, by omega, by omega, by omega⟩
  | _ => simp only [tailOf, ok.injEq, reduceCtorEq] at h

/-- **`RetCtx` from P1's decode facts** (`UtArgs`'s parts, the extra cap at
`x` related): the arguments `retype` gets, as `untyped_decode_refines_with`
derives them; the aligned base is the spec's. -/
theorem retCtx_of_args {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot th sl) {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev))
    {x : U64} {c : capability.Cap} {a : Fl4Spec.Cap} (hc : capAt (L.mem s) x = ok c) (hca : CapRel c a)
    (hcv : CapValid th c) {idx dep val nt us dest off win aligned : U64} {reset : Bool}
    (hsz : untyped.retype_size nt us = ok (.Ok val))
    (hdst : untyped.retype_dest st s x idx dep off win = ok (.Ok dest))
    (hemp : untyped.ensure_empty_slots st s dest off (core.num.U64.wrapping_add off win) = ok (.Ok ()))
    (hrs : reset = true ↔ ∃ v, cdt.ensure_no_children st s (cslotAddr sl) = ok (.Ok v))
    (hal : untyped.align_up (core.num.U64.wrapping_add p (if reset then 0#u64 else fi)) val = ok aligned)
    (hmem : ∃ i2 i4, (1#u64 <<< (sb &&& 63#u64) : Result U64) = ok i2 ∧
      (core.num.U64.wrapping_sub i2 (if reset then 0#u64 else fi) >>> (val &&& 63#u64) : Result U64) = ok i4 ∧
      win.val ≤ i4.val)
    (hdev : dev = true → objects.is_frame_type nt = ok true ∨ nt = fl4_abi.consts.object.Untyped)
    (fiv : U64) (hfivd : fiv = if reset then 0#u64 else fi) :
    ∃ t r, RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv ∧
      aligned = ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ := by
  rw [← hfivd] at hal hmem
  -- the size
  rw [retype_size_cases] at hsz
  have h19 : ¬ nt.val ≥ 19 := fun h => by simp [h] at hsz
  simp only [h19, ↓reduceIte] at hsz
  by_cases hsA : us.val ≥ 64 ∨ zOf nt.val us.val > 47
  · rw [if_pos hsA] at hsz; simp only [ok.injEq, reduceCtorEq] at hsz
  rw [if_neg hsA] at hsz
  by_cases hsB : nt.val = 4 ∧ us.val = 0
  · rw [if_pos hsB] at hsz; simp only [ok.injEq, reduceCtorEq] at hsz
  rw [if_neg hsB] at hsz
  by_cases hsC : nt.val = 0 ∧ us.val < 4
  · rw [if_pos hsC] at hsz; simp only [ok.injEq, reduceCtorEq] at hsz
  rw [if_neg hsC] at hsz
  by_cases hsD : nt.val = 5 ∧ us.val < 7
  · rw [if_pos hsD] at hsz; simp only [ok.injEq, reduceCtorEq] at hsz
  rw [if_neg hsD] at hsz
  simp only [ok.injEq, core.result.Result.Ok.injEq] at hsz
  subst hsz
  obtain ⟨t, ht⟩ : ∃ t, objTypeOf nt.val = some t := by
    cases h : objTypeOf nt.val with
    | none => exact absurd ((objTypeOf_none _).1 h) h19
    | some t => exact ⟨t, rfl⟩
  obtain ⟨-, -, hfr, hut, -, -, -⟩ := objTypeOf_fl4 ht us.val
  have hz47 : zOf nt.val us.val ≤ 47 := by omega
  have hzv : (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val = zOf nt.val us.val := by
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat = _
    simp; omega
  -- the destination
  obtain ⟨r, hth, hr64, hr0, hw1, hw2, hwin⟩ := dest_of_retype_dest hR hV hc hca hcv hdst
  have hpow : 2 ^ r < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
  have hsum : (core.num.U64.wrapping_add off win).val = off.val + win.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  rw [ensure_empty_slots_eq s dest off _ (by omega), hsum] at hemp
  have hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    by_contra hn
    rw [if_neg hn] at hemp
    simp only [ok.injEq, reduceCtorEq] at hemp
  -- the reset
  have hnc : NoChildrenRel (st := st) s σ (cslotAddr sl) sl :=
    noChildren_of_adj th hP s σ G hM hC (hI.parentAdj (th := th)) sl hAs
      ((hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩)
  unfold NoChildrenRel at hnc
  have hrEq : reset = decide (¬ ∃ x, σ.cdt x = some sl) := by
    rw [hnc] at hrs
    by_cases hch : ∃ x, σ.cdt x = some sl
    · rw [if_pos hch] at hrs
      have : reset = false := by
        cases reset
        · rfl
        · obtain ⟨v, hv⟩ := hrs.1 rfl; simp only [ok.injEq, reduceCtorEq] at hv
      rw [this]; simp [hch]
    · rw [if_neg hch] at hrs
      rw [hrs.2 ⟨(), rfl⟩]; simp [hch]
  -- the memory
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨i2, i4, e2, e4, hwi⟩ := hmem
  have h63 : (sb &&& 63#u64).val = sb.val := by
    have : (sb &&& 63#u64).val = sb.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod sb.val 6
    omega
  have hz63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    omega
  have hs2 := U64.ShiftLeft_spec 1#u64 (sb &&& 63#u64) (by rw [h63]; exact hsb)
  rw [e2, WP.spec_ok] at hs2
  have hp64 : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
  have hi2 : i2.bv = 1#64 <<< sb.val := by rw [hs2.2, h63]; rfl
  have hs4 := U64.ShiftRight_spec (core.num.U64.wrapping_sub i2 fiv) ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64)
    (by rw [hz63]; omega)
  rw [e4, WP.spec_ok] at hs4
  have hFB : (core.num.U64.wrapping_sub i2 fiv).bv = 1#64 <<< sb.val - fiv.bv := by
    rw [core.num.U64.wrapping_sub_bv_eq]; exact congrArg (· - fiv.bv) hi2
  have hi4 : i4.val = (1#64 <<< sb.val - fiv.bv).toNat >>> zOf nt.val us.val := by
    rw [hs4.1, hz63, ← hFB]; rfl
  refine ⟨t, r, ⟨ht, ⟨by omega, hz47, hsB, hsC, hsD⟩, ⟨hth, hr64, hr0⟩, ⟨hw1, hw2, hwin⟩, hempty, hrEq, hfivd,
    hsb, by rw [← hi4]; exact hwi, fun hd => ?_⟩, ?_⟩
  · rcases hdev hd with h | h
    · rw [is_frame_type_eq] at h
      simp only [ok.injEq, decide_eq_true_eq] at h
      exact Or.inl (hfr.2 h)
    · exact Or.inr (hut.2 (by rw [h]; unfold fl4_abi.consts.object.Untyped; rfl))
  · rw [align_up_eq _ _ (by rw [hzv]; omega), hzv, core.num.U64.wrapping_add_bv_eq] at hal
    simp only [ok.injEq] at hal
    exact hal.symm

/-! ## What the joint simulation knows at the untyped decode -/

/-- **The invoked untyped cap's facts** (l4v `valid_untyped`, `valid_cap`
and the kernel's placement, as the CSpace retype proofs take them): the
region aligned, fitting and high, its free part free of objects and zero,
at least 16 bytes, no object straddling it and no linked slot in it, the
reset's conditions, the debug-list head and the global PML4 off it, and the
preemption point's hypothesis over it. -/
structure UtCapP3 {A' : Type} (arI : machine.Arch A') (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p sb fi : U64) : Prop where
  pal : p.val % 2 ^ sb.val = 0
  pfit : p.val + 2 ^ sb.val ≤ 2 ^ 64
  fiLe : fi.val ≤ 2 ^ sb.val
  high : 2 ^ 64 - 2 ^ 47 ≤ p.val
  actZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
    (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val)
  free : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val)
  zero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val)
  sb4 : 4 ≤ sb.val
  nostr : NoStraddle th p.val (p.val + 2 ^ sb.val)
  /-- No MDB slot in the cap's free part [p+fi, p+2^sb) (l4v `valid_untyped`'s
  free-index part: what is retyped from the cap lies below `p + fi`). -/
  nsFree : ∀ a ∈ G.chains.flatten, a.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ a.val
  /-- No MDB slot anywhere in the region when the cap has no children: a CNode
  retyped from the cap can hold slots in the region only while the cap has a
  descendant (the CNode's caps). Used by the reset, which only runs then. -/
  ns : (¬ ∃ x, σ.cdt x = some sl) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val
  pp : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
    L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0)
  rst : (¬ ∃ x, σ.cdt x = some sl) → fi.val ≠ 0 →
    (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
    (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
    ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val)
  dwReg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val)
  gReg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val)

/-- **The joint state at the untyped decode** (`UtP3Ok`'s witness): the
relations, the joint cover, the invoked slot (a CNode slot holding the
untyped cap) and the extra caps related, the current thread's, the debug
list head and the global PML4's facts, and the invoked cap's (`UtCapP3`). -/
structure UtJoint {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64) (s : S) (slot : obj.Slot)
    (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize) (th : TypedHeap) (G : MdbGhost)
    (D : Set U64) (σ : Fl4Spec.State Unit) (pp : U64) (rs : Nat) (idx : List Bool) : Prop where
  jcov : JCovD (L := L) th H G D Cs s
  rel : StateRel th (L.mem s) σ
  valid : SlotsValid th (L.mem s)
  placed : Placed th
  links : MdbLinks th (L.mem s) G
  cdt : CdtRel th (L.mem s) σ G
  mdb : MdbInv (L.mem s) G
  ut : UtInv (L.mem s) G
  orig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl
  /-- No spec object in an untyped cap's free part (`SpecFree`, l4v `valid_untyped`). -/
  sfree : SpecFree (L.mem s) G σ
  cur : σ.curThread = (L.curW s).bv
  curT : th (L.curW s) = some .tcb
  act : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
  node : th pp = some (.cnode rs)
  idxLen : idx.length = rs
  slotEq : slot = cslotAddr (pp.bv, idx)
  capEq : capAt (L.mem s) slot = ok cap
  extraRel : ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ c a, capAt (L.mem s) x = ok c ∧ CapRel c a ∧ CapValid th c
  utc : ∀ p sb fi dev, cap = .Untyped p sb fi dev → UtCapP3 (L := L) arI th s σ G (pp.bv, idx) p sb fi
  dwAl : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
  dwObj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32)
  dwNe : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA (L.curW s)).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val
  head : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
    (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
      TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))
  gpm : HasPm σ σ.archState.x64GlobalPml4
  ga : σ.archState.x64GlobalPml4.toNat % 4096 = 0
  gf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64
  /-- P1's heap: well formed, no object at null, off the kernel-global area
  and the nodes, which do not wrap. -/
  heap : HeapOK H
  h0 : H 0#u64 = none
  hks : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val
  hnd : ∀ p k, H p = some k → ∀ c ∈ Cs, p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val
  ksbFit : (L.ksb s).val + 13568 ≤ 2 ^ 64
  ksbAl : (L.ksb s).val % 8 = 0
  nodeFit : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64
  cpuCs : L.cpu s ∈ Cs
  /-- The current thread is `H`'s TCB, and the current SC an `H` object not dead. -/
  curH : H (L.curW s) = some .tcb
  cscH : H (L.cscW s) ≠ none
  cscLive : L.cscW s ∉ D
  /-- The joint placement (`JPlaced`): the typed heap's objects in `H`'s. -/
  jpl : ∃ Tr C, JPlaced (L := L) th H Tr C s σ

/-- **P3's facts at the untyped decode** (P1's `UtRetypeP3.run` premise):
some joint state (`UtJoint`) at `s`, for the invoked `slot`, `cap` and the
extra caps. -/
def UtP3Ok {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64) (s : S) (slot : obj.Slot)
    (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∃ th G D σ pp rs idx, UtJoint (L := L) arI H Cs s slot cap extra th G D σ pp rs idx

/-- **The retype after the restart, at P3's relations** (`retype_cont_allN`,
`retype_cont_pml4N` for the native types): from the joint state at the
decode's start `s0`, the restart's equation and P1's decode facts, the
retype from `s` ends as `RetPostN` names (the spec's `invoke_untyped` of the
decoded invocation). -/
theorem retype_postN {A' : Type} (arI : machine.Arch A') {H : Heap} {Cs : Set U64} {s0 s : S} {ar : A'}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {p sb fi : U64} {dev reset : Bool}
    {aligned nt us dest off win : U64} {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit}
    {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot (.Untyped p sb fi dev) extra th G D σ pp rs idx)
    (hrs : sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s)
    (hA : UtArgs st s0 extra slot p sb fi dev reset aligned nt us dest off win)
    (hnt : nt.val ≤ 13) (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame) :
    untyped.retype st arI s ar slot reset aligned nt us dest off win dev ⦃ res =>
      ∃ t r fiv, RetCtx (L := L) th s0 σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv ∧
        aligned = ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ ∧
        RetPostN (L := L) th (L.mem s0) G σ arI ar s0 Fl4Spec.fl4ObjBitsApi (L.ksb s0) (.retype (pp.bv, idx) reset
          p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
          dev) res ⦄ := by
  obtain ⟨x, hxe, hx0, idx', dep, val, hsz, -, hdst, hemp, hrsE, hal, hmem, hdev⟩ := hA
  obtain ⟨c, a, hc, hca, hcv⟩ := J.extraRel x hxe hx0
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [J.idxLen] using J.node)⟩
  have hcap : capAt (L.mem s0) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev) := by
    rw [← J.slotEq]; exact J.capEq
  rw [J.slotEq] at hrsE
  obtain ⟨fiv, hfiv⟩ : ∃ fiv : U64, fiv = if reset then 0#u64 else fi := ⟨_, rfl⟩
  obtain ⟨t, r, hctx, haleq⟩ := retCtx_of_args J.rel J.valid J.placed J.links J.cdt J.mdb hAs hcap hc hca hcv hsz hdst
    hemp hrsE hal hmem hdev fiv hfiv
  have U := J.utc p sb fi dev rfl
  have hct : sched.cur_thread st s0 = ok (L.curW s0) := cur_thread_eq s0
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hctx.ty us.val).2.1
  have run : ∀ {P : core.result.Result Unit error.Exc × S × A' → Prop},
      (do
        let s2 ← sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART
        untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
          ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev)
        ⦃ P ⦄ →
      untyped.retype st arI s ar slot reset aligned nt us dest off win dev ⦃ P ⦄ := by
    intro P h
    rw [hrs, bind_ok, ← haleq, ← J.slotEq] at h; exact h
  refine WP.spec_mono (run ?_) fun res h => ⟨t, r, fiv, hctx, haleq, h⟩
  by_cases h8 : nt.val = 8
  · exact retype_cont_pml4N arI ar th s0 σ G J.rel J.valid J.placed J.links J.cdt J.mdb J.ut J.orig (L.curW s0) J.cur
      hct J.curT J.act J.node J.idxLen hcap U.pal U.pfit U.fiLe U.high U.actZ U.free U.zero U.sb4 U.nostr U.ns hrcb
      hppS U.pp U.rst Fl4Spec.fl4ObjBitsApi nt us dest off win t r reset fiv h8 hb J.dwAl J.dwObj U.dwReg J.dwNe J.head
      J.gpm J.ga J.gf U.gReg hctx
  · exact retype_cont_allN arI ar th s0 σ G J.rel J.valid J.placed J.links J.cdt J.mdb J.ut J.orig (L.curW s0) J.cur
      hct J.curT J.act J.node J.idxLen hcap U.pal U.pfit U.fiLe U.high U.actZ U.free U.zero U.sb4 U.nostr U.ns hrcb
      hppS U.pp U.rst Fl4Spec.fl4ObjBitsApi nt us dest off win t r reset fiv ⟨hnt, h8⟩ hb J.dwAl J.dwObj U.dwReg J.dwNe
      J.head hctx

/-! ## `DropOK` -/

/-- **[KeptRefsP3] The links of kept objects name no dropped object**
(`DropOK`'s reference fields with spec counterparts): replies' next/prev,
SCs' reply heads, the TCB↔notification bound links, SCs' notifications,
yield-to/from. P3's, from l4v `sym_refs` through the relations (CallRel,
NtfnStateRel, YieldRel, `SchedValid`): a link to a dropped (dead) object has
a spec back-link, a word of the dead object, which is 0. Named, to be
discharged (bound/SC-notification links, then the call stacks, then yield). -/
def KeptRefsP3 (H : Heap) (D : U64 → Prop) (s : S) : Prop :=
  (∀ r ∈ H.replies, ¬ D r → headBit (L.mem s (rNextA r)) = false →
    KeptRef H D (L.mem s (rNextA r) &&& ~~~1#u64)) ∧
  (∀ r ∈ H.replies, ¬ D r → KeptRef H D (L.mem s (rPrevA r) &&& ~~~1#u64)) ∧
  (∀ c ∈ H.scs, ¬ D c → KeptRef H D (L.mem s (scReplyA c))) ∧
  (∀ t ∈ H.tcbs, ¬ D t → KeptRef H D (L.mem s (boundA t))) ∧
  (∀ c ∈ H.scs, ¬ D c → KeptRef H D (L.mem s (scNtfnA c))) ∧
  (∀ n ∈ H.ntfns, ¬ D n → KeptRef H D (L.mem s (ntfnBtA n))) ∧
  (∀ t ∈ H.tcbs, ¬ D t → KeptRef H D (L.mem s (yieldA t))) ∧
  (∀ c ∈ H.scs, ¬ D c → KeptRef H D (L.mem s (scYieldFromA c)))

/-- **[W] [DbgTimerKept] The timer trees and debug lists name no dropped
object** (`DropOK`'s `tl` and `node`): FL4's own structures, with no spec
counterpart. Needs the P3 invariant "the timer trees' and debug lists'
members are live TCBs" (finalisation removes a TCB from both:
`timer.remove`, `debug_remove`). Named. -/
def DbgTimerKept (H : Heap) (D : U64 → Prop) (Cs : Set U64) (s : S) : Prop :=
  (∀ y ∈ H.tcbs, ¬ D y → KeptRef H D (L.mem s (tlA y)) ∧ KeptRef H D (L.mem s (trA y)) ∧
    KeptRef H D (L.mem s (tpA y)) ∧ KeptRef H D (L.mem s (dnA y)) ∧ KeptRef H D (L.mem s (dpA y))) ∧
  (∀ c ∈ Cs, KeptRef H D (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) ∧
    KeptRef H D (L.mem s (L.nodeAt s c layout.node.TIMER_MIN)) ∧
    KeptRef H D (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS)))

/-- **`DropOK` of a region** from its parts: the heap well formed, the
region's objects dead, the current thread and SC off it, the heap's objects
off the kernel-global area and the nodes, and the kept links
(`KeptRefsP3`, `DbgTimerKept`). -/
theorem dropOK_of {H : Heap} {Cs : Set U64} {s : S} {lo hi : Nat} (hH : HeapOK H) (h0 : H 0#u64 = none)
    (hdead : ∀ q k, H q = some k → RegionD H lo hi q → DeadQ st H s q)
    (hcur : ¬ RegionD H lo hi (L.curW s)) (hcsc : ¬ RegionD H lo hi (L.cscW s))
    (hks : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val)
    (hnd : ∀ p k, H p = some k → ∀ c ∈ Cs, p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val)
    (hK : KeptRefsP3 (L := L) H (RegionD H lo hi) s) (hT : DbgTimerKept (L := L) H (RegionD H lo hi) Cs s)
    (hksf : (L.ksb s).val + 13568 ≤ 2 ^ 64) :
    DropOK st H (RegionD H lo hi) Cs s := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hK
  obtain ⟨t1, t2⟩ := hT
  refine ⟨hH, h0, hdead, hcur, hcsc, fun o ho _ p k hp _ hin => ?_, fun c hc b h1 h2 p k hp _ hin => ?_,
    k1, k2, k3, k4, k5, k6, k7, k8, t1, t2⟩
  · have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      simp only [core.num.U64.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by rw [show UScalar.size UScalarTy.U64 = 2 ^ 64 by simp [U64.size, U64.numBits]]; omega)
    unfold InObj at hin; rw [hv] at hin; have := hks p k hp; omega
  · unfold InObj at hin; have := hnd p k hp c hc; omega

/-- **The objects meeting an untyped cap's free part are dead** (or, for a
cap with no children, its whole region): uncovered (`ut_free_fi`,
`ut_free`), so in `JCovD`'s dead set. -/
theorem region_deadP {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}
    (hJ : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64} {d : Bool} (hcx : capV (L.mem s) x = .Untyped p sb fi d)
    {lo hi : Nat} (hlo : p.val + fi.val ≤ lo ∨ ((∀ y, ¬ Mdb.Desc G.par y x) ∧ p.val ≤ lo))
    (hhi : hi ≤ p.val + 2 ^ sb.val) :
    ∀ q k, H q = some k → RegionD H lo hi q → q ∈ D ∧ DeadP (L := L) H s q := by
  intro q k hq hm
  unfold RegionD at hm
  rw [hq] at hm
  simp only [Option.elim] at hm
  unfold MeetsR at hm
  rcases hJ.h q k hq with hc | hd
  · exfalso
    have h1 := Nat.one_le_two_pow (n := k.bits)
    rcases hlo with hlo | ⟨hnd, hlo⟩
    · rcases ut_free_fi hU hx hcx (by omega) hc with e | e <;> omega
    · rcases ut_free hU hI hx hcx hnd (by omega) hc with e | e <;> omega
  · exact ⟨hd, hJ.dead q hd⟩

/-- A field word of an object: inside it and aligned. -/
theorem field_in {q K : U64} {b : Nat} (hal : q.val % 2 ^ b = 0) (hfit : q.val + 2 ^ b ≤ 2 ^ 64) (hb : 3 ≤ b)
    (hK : K.val < 2 ^ b) (hK8 : K.val % 8 = 0) :
    q.val ≤ (core.num.U64.wrapping_add q K).val ∧ (core.num.U64.wrapping_add q K).val < q.val + 2 ^ b ∧
      (core.num.U64.wrapping_add q K).val % 8 = 0 := by
  have hv : (core.num.U64.wrapping_add q K).val = q.val + K.val := by
    simp only [core.num.U64.wrapping_add_val_eq]
    exact Nat.mod_eq_of_lt (by rw [show UScalar.size UScalarTy.U64 = 2 ^ 64 by simp [U64.size, U64.numBits]]; omega)
  have h8 : 8 ∣ 2 ^ b := by
    have : 2 ^ b = 2 ^ 3 * 2 ^ (b - 3) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have hq8 : q.val % 8 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h8 (Nat.dvd_of_mod_eq_zero hal))
  rw [hv]; omega

/-- **`DeadQ` from `DeadP` across a step keeping the object's words**: the
object's words and the idle word kept, the action word naming no TCB. -/
theorem deadQ_keep {H : Heap} {s0 s : S} {q : U64} {k : HKind} (hH : HeapOK H) (hq : H q = some k)
    (hd : DeadP (L := L) H s0 q)
    (hw : ∀ w : U64, q.val ≤ w.val → w.val < q.val + 2 ^ k.bits → w.val % 8 = 0 → L.mem s w = L.mem s0 w)
    (hi : L.idleW s = L.idleW s0) (hact : H q = some .tcb → q ≠ L.actionW s) : DeadQ st H s q := by
  have hal := hH.align q k hq
  have hfit := hH.fits q k hq
  have kw : ∀ K : U64, 3 ≤ k.bits → K.val < 2 ^ k.bits → K.val % 8 = 0 →
      L.mem s (core.num.U64.wrapping_add q K) = L.mem s0 (core.num.U64.wrapping_add q K) := fun K hb hK hK8 =>
    let h := field_in hal hfit hb hK hK8; hw _ h.1 h.2.1 h.2.2
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  refine ⟨fun hq' => ?_, fun hq' => ?_, fun hq' => ?_, fun hq' => ?_, fun z hq' => ?_⟩
  · rw [hq] at hq'; cases hq'
    obtain ⟨a1, a2, a3, -, a5⟩ := d1 hq
    have b12 : (HKind.tcb).bits = 12 := rfl
    refine ⟨?_, ?_, ?_, hact hq, by rw [hi]; exact a5⟩
    · unfold P1.stA; rw [kw _ (by simp [b12]) (by simp [b12, layout.tcb.STATE, layout.tcb.F]) (by simp [layout.tcb.STATE, layout.tcb.F])]; exact a1
    · unfold P1.scA; rw [kw _ (by simp [b12]) (by simp [b12]) (by simp)]; exact a2
    · unfold P1.boundA; rw [kw _ (by simp [b12]) (by simp [b12]) (by simp)]; exact a3
  · rw [hq] at hq'; cases hq'
    have b4 : (HKind.ep).bits = 4 := rfl
    unfold LawfulStore.epState epTSA
    rw [kw _ (by simp [b4]) (by simp [b4, layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])]
    exact d2 hq
  · rw [hq] at hq'; cases hq'
    have b6 : (HKind.ntfn).bits = 6 := rfl
    obtain ⟨a1, a2, a3⟩ := d3 hq
    refine ⟨?_, ?_, ?_⟩
    · unfold LawfulStore.epState epTSA
      rw [kw _ (by simp [b6]) (by simp [b6, layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])]
      exact a1
    · unfold ntfnBtA; rw [kw _ (by simp [b6]) (by simp [b6, layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])]
      exact a2
    · unfold ntfnScA; rw [kw _ (by simp [b6]) (by simp [b6, layout.ntfn.SC]) (by simp [layout.ntfn.SC])]; exact a3
  · rw [hq] at hq'; cases hq'
    have b5 : (HKind.reply).bits = 5 := rfl
    unfold rTcbA; rw [kw _ (by simp [b5]) (by simp [b5, layout.reply.TCB]) (by simp [layout.reply.TCB])]
    exact d4 hq
  · rw [hq] at hq'; cases hq'
    have hz : 7 ≤ z := hH.scmin q z hq
    have b7 : (2 : Nat) ^ 7 ≤ 2 ^ (HKind.sc z).bits := Nat.pow_le_pow_right (by norm_num) hz
    obtain ⟨a1, a2, a3⟩ := d5 z hq
    refine ⟨?_, ?_, ?_⟩
    · unfold scTcbA; rw [kw _ (by show 3 ≤ z; omega) (by simp [layout.sc.TCB]; omega) (by simp [layout.sc.TCB])]
      exact a1
    · unfold scReplyA; rw [kw _ (by show 3 ≤ z; omega) (by simp [layout.sc.REPLY]; omega) (by simp [layout.sc.REPLY])]
      exact a2
    · unfold scNtfnA; rw [kw _ (by show 3 ≤ z; omega) (by simp [layout.sc.NTFN]; omega) (by simp [layout.sc.NTFN])]
      exact a3

/-- **The restart keeps the words of every other object**: it writes the
current thread's state word (inside that TCB) and the current core's
scheduler-action word (in its node, which no object meets). -/
theorem restart_keeps_obj {H : Heap} {s0 s : S} {c q : U64} {k : HKind} (hH : HeapOK H)
    (hfr : Frame2 (L := L) s0 s (stA c) (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION))
    (hq : H q = some k) (hc : H c = some .tcb) (hqc : q ≠ c)
    (hnd : q.val + 2 ^ k.bits ≤ L.nodeBase s0 (L.cpu s0) ∨ L.nodeBase s0 (L.cpu s0) + 4288 ≤ q.val)
    (hnf : (L.ksb s0).val + 13568 + ((L.cpu s0).val + 1) * 4288 ≤ 2 ^ 64) :
    ∀ w : U64, q.val ≤ w.val → w.val < q.val + 2 ^ k.bits → w.val % 8 = 0 → L.mem s w = L.mem s0 w := by
  intro w h1 h2 h8
  have hcfit := hH.fits c .tcb hc
  have hcal := hH.align c .tcb hc
  have b12 : (HKind.tcb).bits = 12 := rfl
  rw [b12] at hcfit hcal
  have hst : (stA c).val = c.val + 3328 := by
    unfold stA
    simp only [core.num.U64.wrapping_add_val_eq, layout.tcb.STATE, layout.tcb.F]
    exact Nat.mod_eq_of_lt (by rw [show UScalar.size UScalarTy.U64 = 2 ^ 64 by simp [U64.size, U64.numBits]]; simp; omega)
  have hav := nodeAt_val' (L := L) (s := s0) (off := layout.node.SCHED_ACTION) hnf (by simp [layout.node.SCHED_ACTION])
  refine hfr w h8 (fun e => ?_) (fun e => ?_)
  · rcases hH.disj q k c .tcb hq hc hqc with h | h <;> (try simp only [b12] at h) <;> omega
  · unfold LawfulStore.nodeBase at hnd
    have : layout.node.SCHED_ACTION.val = 16 := by simp [layout.node.SCHED_ACTION]
    omega

theorem runnable_ne_inactive {v : U64} (h : Runnable v) : v ≠ sched.TS_INACTIVE := by
  rintro rfl
  rcases h with h | h | h <;> revert h <;>
    simp [sched.TS_INACTIVE, sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM]

/-- **`DropOK` of a dead range after the restart** (its objects dead at the
decode's start, `region_deadP` or `retype_window_dead`, carried across the
restart by `deadQ_keep`, `restart_keeps_obj`), the kept links named
(`KeptRefsP3`, `DbgTimerKept`). -/
theorem dead_dropOK {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s0 s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {p sb fi : U64} {dev : Bool}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot (.Untyped p sb fi dev) extra th G D σ pp rs idx)
    {lo hi : Nat} (RD : ∀ q k, H q = some k → RegionD H lo hi q → q ∈ D ∧ DeadP (L := L) H s0 q)
    (hfr : Frame2 (L := L) s0 s (stA (L.curW s0)) (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION))
    (hks : L.ksb s = L.ksb s0) (hcpu : L.cpu s = L.cpu s0)
    (hcw : L.curW s = L.curW s0) (hcs : L.cscW s = L.cscW s0) (hact : ∀ y ∈ H.tcbs, L.actionW s ≠ y)
    (hrun : Runnable (L.mem s0 (stA (L.curW s0))))
    (hKR : KeptRefsP3 (L := L) H (RegionD H lo hi) s) (hDT : DbgTimerKept (L := L) H (RegionD H lo hi) Cs s) :
    DropOK st H (RegionD H lo hi) Cs s := by
  -- the current thread is not dead
  have hcurN : ∀ k, H (L.curW s0) = some k → ¬ RegionD H lo hi (L.curW s0) := by
    intro k hk hr
    have hd := (RD _ k hk hr).2
    exact runnable_ne_inactive hrun (hd.1 J.curH).1
  have hnb : ∀ c, L.nodeBase s c = L.nodeBase s0 c := fun c => by simp [LawfulStore.nodeBase, hks]
  -- the idle word
  have hidle : L.idleW s = L.idleW s0 := by
    unfold LawfulStore.idleW
    rw [show L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD = L.nodeAt s0 (L.cpu s0) layout.node.IDLE_THREAD by
      simp [LawfulStore.nodeAt, hks, hcpu]]
    have hiv := nodeAt_val' (L := L) (s := s0) (off := layout.node.IDLE_THREAD) J.nodeFit
      (by simp [layout.node.IDLE_THREAD])
    have hav := nodeAt_val' (L := L) (s := s0) (off := layout.node.SCHED_ACTION) J.nodeFit
      (by simp [layout.node.SCHED_ACTION])
    have hcf := J.heap.fits _ _ J.curH
    have hst : (stA (L.curW s0)).val = (L.curW s0).val + 3328 := by
      unfold stA
      simp only [core.num.U64.wrapping_add_val_eq, layout.tcb.STATE, layout.tcb.F]
      have hs64 : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size, U64.numBits]
      simp only [HKind.bits] at hcf
      exact Nat.mod_eq_of_lt (by rw [hs64]; simp; omega)
    have hn := J.hnd _ _ J.curH (L.cpu s0) J.cpuCs
    simp only [HKind.bits] at hn hcf
    unfold LawfulStore.nodeBase at hn
    have hka := J.ksbAl
    refine hfr _ (by unfold P1.Aligned; rw [hiv]; simp [layout.node.IDLE_THREAD]; omega) (fun e => ?_) (fun e => ?_)
    · rw [hiv, hst] at e; simp [layout.node.IDLE_THREAD] at e; omega
    · rw [hiv, hav] at e; simp [layout.node.IDLE_THREAD, layout.node.SCHED_ACTION] at e
  refine dropOK_of J.heap J.h0 (fun q k hq hr => ?_) (fun hr => ?_) (fun hr => ?_)
    (fun p' k hp => by rw [hks]; exact J.hks p' k hp) (fun p' k hp c hc => by rw [hnb]; exact J.hnd p' k hp c hc)
    hKR hDT (by rw [hks]; exact J.ksbFit)
  · obtain ⟨-, hdp⟩ := RD q k hq hr
    have hqc : q ≠ L.curW s0 := by rintro rfl; exact hcurN k hq hr
    exact deadQ_keep J.heap hq hdp (restart_keeps_obj J.heap hfr hq J.curH hqc (J.hnd q k hq _ J.cpuCs) J.nodeFit)
      hidle (fun hqt e => hact q hqt e.symm)
  · rw [hcw] at hr; exact hcurN _ J.curH hr
  · rw [hcs] at hr
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 J.cscH
    exact J.cscLive (RD _ k hk hr).1

/-- The invoked slot is in the MDB, its cap the untyped cap. -/
theorem UtJoint.slot_mem {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {cap : capability.Cap}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s slot cap extra th G D σ pp rs idx) (hc : cap ≠ .Null) :
    AbsSlot th (pp.bv, idx) ∧ slot ∈ G.chains.flatten ∧ capV (L.mem s) slot = cap := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [J.idxLen] using J.node)⟩
  exact ⟨hAs, (J.links.members _).2 ⟨by rw [J.slotEq]; exact hAs.isSlot, _, J.capEq, hc⟩, capV_of_capAt J.capEq⟩

/-- **The reset's facts** (P1's `ResetOK`, after the restart): the untyped
cap at its slot, placed and sized, its region's objects droppable (dead: a
cap with no children covers nothing), the region off the nodes. -/
theorem resetOK_of {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s0 s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {p sb fi : U64} {dev : Bool}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot (.Untyped p sb fi dev) extra th G D σ pp rs idx)
    (hfr : Frame2 (L := L) s0 s (stA (L.curW s0)) (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION))
    (hks : L.ksb s = L.ksb s0) (hcpu : L.cpu s = L.cpu s0)
    (hcw : L.curW s = L.curW s0) (hcs : L.cscW s = L.cscW s0) (hact : ∀ y ∈ H.tcbs, L.actionW s ≠ y)
    (hrun : Runnable (L.mem s0 (stA (L.curW s0))))
    (hcapS : obj.Slot.cap st slot s = ok (.Untyped p sb fi dev))
    (hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx))
    (hKR : (∀ q k, H q = some k → RegionD H p.val (p.val + 2 ^ sb.val) q → q ∈ D) →
      KeptRefsP3 (L := L) H (RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : (∀ q k, H q = some k → RegionD H p.val (p.val + 2 ^ sb.val) q → q ∈ D) →
      DbgTimerKept (L := L) H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s) :
    ResetOK st H Cs s slot p sb fi dev := by
  obtain ⟨hAs, hx, hcx⟩ := J.slot_mem (by simp)
  have U := J.utc p sb fi dev rfl
  have hnd : ∀ y, ¬ Mdb.Desc G.par y slot := by
    intro y
    refine Mdb.not_desc_of_no_child fun z hz => hnc ?_
    exact (J.cdt.has_child_iff J.placed hAs).2 ⟨z, by rw [← J.slotEq]; exact hz⟩
  have RD := region_deadP J.jcov J.ut J.mdb hx hcx (lo := p.val) (hi := p.val + 2 ^ sb.val) (Or.inr ⟨hnd, le_rfl⟩) le_rfl
  obtain ⟨hk1, hk2⟩ := J.jcov.ks slot hx p sb fi dev hcx
  refine ⟨hcapS, U.pal, U.pfit, dead_dropOK J RD hfr hks hcpu hcw hcs hact hrun (hKR fun q k hq hr => (RD q k hq hr).1)
    (hDT fun q k hq hr => (RD q k hq hr).1), ⟨fun c hc => ?_, ?_⟩,
    U.fiLe, U.sb4, capAt_untyped_inv J.capEq⟩
  · have : L.nodeBase s c = L.nodeBase s0 c := by simp [LawfulStore.nodeBase, hks]
    rw [this]; rcases hk2 c hc with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [hks]; rcases hk1 with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- **A new object's size is the retype's object size** (`newKind`'s bits
are `zOf`'s). -/
theorem newKind_bits {n us : Nat} {kd : HKind} (h : newKind n us = some kd) : kd.bits = zOf n us := by
  by_cases hn : n < 19
  · interval_cases n <;> simp [newKind] at h <;> subst h <;> simp [zOf, HKind.bits] <;> omega
  · have : newKind n us = none := by
      unfold newKind; simp only [show ¬ n = 1 by omega, show ¬ n = 2 by omega, show ¬ n = 3 by omega,
        show ¬ n = 4 by omega, show ¬ n = 5 by omega, show ¬ n = 6 by omega, show ¬ n = 14 by omega, ↓reduceIte]
      rw [if_neg (by omega)]
    rw [this] at h; cases h

/-- **Slot words are P1's cap-slot words** when every slot lies in an
object of the heap: a TCB (its first 192 bytes, `TLow`) or an untracked one
(`Ω` off the frame words). -/
theorem slotCapW_of_in {th' : TypedHeap} {H' : Heap} (hP : Placed th') (hH : HeapOK H')
    (hin : ∀ a, IsSlot th' a → ∃ q k, H' q = some k ∧ q.val ≤ a.val ∧ a.val + 32 ≤ q.val + 2 ^ k.bits ∧
      (k = .tcb → a.val + 32 ≤ q.val + 192) ∧ (k = .tcb ∨ ∃ z, k = .other z)) :
    SlotCapW th' H'.tcbs H'.omega H'.frame := by
  rintro b ⟨a, ha, o, ho, rfl⟩
  obtain ⟨q, k, hq, h1, h2, h3, h4⟩ := hin a ha
  have hv := slot_word_val hP ha ho
  obtain ⟨ho1, ho2⟩ := ho.lt
  have hal := ha.align hP
  have hfit := hH.fits q k hq
  rcases h4 with rfl | ⟨z, rfl⟩
  · left
    have h3' := h3 rfl
    simp only [HKind.bits] at hfit h2
    refine ⟨q, hq, ⟨BitVec.ofNat 64 ((wordOf a o).val - q.val)⟩, ?_, ?_⟩
    · show (BitVec.ofNat 64 ((wordOf a o).val - q.val)).toNat < 192
      rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · apply UScalar.eq_of_val_eq
      rw [wa_val q _ (by omega), hv]; omega
  · right
    have hb8 : (wordOf a o).val % 8 = 0 := by rw [hv]; omega
    refine ⟨⟨hb8, q, _, hq, Or.inr (Or.inr (Or.inl ⟨z, rfl⟩)), by unfold InObj; rw [hv]; omega⟩, ?_⟩
    rintro ⟨-, p', k', hp', hk', hin'⟩
    have hne : p' ≠ q := by
      rintro rfl; rw [hq] at hp'; cases hp'
      rcases hk' with h | ⟨z', h⟩ | ⟨h, -⟩ <;> cases h
    unfold InObj at hin'
    rcases hH.disj p' k' q _ hp' hq hne with e | e <;> rw [hv] at hin' <;> omega

/-! ## The debug lists after a retype of no TCBs -/

/-- **`DbgLinksOK` for a retype creating no TCB**: the write frame misses
the kept TCBs' debug links and the cores' list heads, which are typed
(`TimerOK`) and name no dropped object (`DropOK`'s `tl`, `node`). -/
theorem dbgLinks_nonTcb {H1 : Heap} {Cs : Set U64} {sR s' : S} {lo hi A k w n : Nat} {Pw : U64 → Prop}
    (hn : n ≠ 1) (hP : DropOK st H1 (RegionD H1 lo hi) Cs sR) (hTm : TimerOK st H1.tcbs Cs sR)
    (hW : WFrame (L := L) sR s' Pw)
    (hfr : ∀ v, Pw v → (∀ y ∈ H1.tcbs, ¬ RegionD H1 lo hi y → v ≠ dnA y ∧ v ≠ dpA y) ∧
      ∀ c ∈ Cs, v ≠ L.nodeAt sR c layout.node.DEBUG_TCBS)
    (hal : ∀ y ∈ H1.tcbs, P1.Aligned (dnA y) ∧ P1.Aligned (dpA y))
    (hnal : ∀ c ∈ Cs, P1.Aligned (L.nodeAt sR c layout.node.DEBUG_TCBS)) :
    DbgLinksOK st H1 Cs s' lo hi A k w n := by
  have kept : ∀ x, Tz H1.tcbs x → KeptRef H1 (RegionD H1 lo hi) x → NewTcbRef H1 lo hi A k w n x := by
    intro x hz hk
    rcases hz with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hx, hk (by rw [show H1 x = some .tcb from hx]; simp)⟩)
  have hna : ∀ c, L.nodeAt s' c layout.node.DEBUG_TCBS = L.nodeAt sR c layout.node.DEBUG_TCBS := fun c => by
    simp [LawfulStore.nodeAt, hW.1]
  refine ⟨fun y hy hy0 => ?_, fun c hc => ?_⟩
  · rcases hy with h0 | ⟨hyt, hyD⟩ | ⟨h1, -⟩
    · exact absurd h0 hy0
    · obtain ⟨-, -, -, k4, k5⟩ := hP.tl y hyt hyD
      have e4 : L.mem s' (dnA y) = L.mem sR (dnA y) :=
        hW.2.2 _ (hal y hyt).1 (fun h => ((hfr _ h).1 y hyt hyD).1 rfl)
      have e5 : L.mem s' (dpA y) = L.mem sR (dpA y) :=
        hW.2.2 _ (hal y hyt).2 (fun h => ((hfr _ h).1 y hyt hyD).2 rfl)
      rw [e4, e5]
      exact ⟨kept _ (hTm.dn y hyt) k4, kept _ (hTm.dp y hyt) k5⟩
    · exact absurd h1 hn
  · rw [hna, hW.2.2 _ (hnal c hc) (fun h => (hfr _ h).2 c hc rfl)]
    exact kept _ (hTm.dh c hc) (hP.node c hc).2.2

/-- A word of a TCB of `H`. -/
theorem tcb_word {H : Heap} (hH : HeapOK H) {y K : U64} (hy : H y = some .tcb) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add y K).val = y.val + K.val := by
  have hf := hH.fits y .tcb hy
  simp only [HKind.bits] at hf
  simp only [core.num.U64.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (by rw [show UScalar.size UScalarTy.U64 = 2 ^ 64 by simp [U64.size, U64.numBits]]; omega)

/-- **A slot word is not a TCB's debug link, nor in a node** (`JPlaced`: the
slot in an `H` object, a TCB's within its first 192 bytes). -/
theorem slot_word_off {th : TypedHeap} {H : Heap} {Tr C Cs : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hJP : JPlaced (L := L) th H Tr C s σ)
    (hnd : ∀ p k, H p = some k → ∀ c ∈ Cs, p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val)
    {v : U64} (hv : SlotSpan th v) :
    (∀ y, H y = some .tcb → v ≠ dnA y ∧ v ≠ dpA y) ∧ (∀ c ∈ Cs, v.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ v.val) := by
  obtain ⟨a, ha, h1, h2⟩ := hv
  obtain ⟨q, kq, hq, e1, e2, e3, -⟩ := hJP.slot_in ha
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · have hdn : (dnA y).val = y.val + 3576 := tcb_word hJP.heap hy (by simp)
    have hdp : (dpA y).val = y.val + 3584 := tcb_word hJP.heap hy (by simp)
    by_cases hyq : y = q
    · subst hyq; rw [hy] at hq; cases hq
      have := e3 rfl
      exact ⟨fun e => by rw [e, hdn] at h1 h2; omega, fun e => by rw [e, hdp] at h1 h2; omega⟩
    · have hd := hJP.heap.disj y .tcb q kq hy hq hyq
      rw [show (2 : Nat) ^ HKind.tcb.bits = 4096 from rfl] at hd
      exact ⟨fun e => by rw [e, hdn] at h1 h2; omega, fun e => by rw [e, hdp] at h1 h2; omega⟩
  · have := hnd q kq hq c hc; omega

/-! ## The creation -/

set_option maxHeartbeats 1000000 in
/-- **P1's `CreateOK` from the creation's facts at its start `sR`** (the
window as the region): the window droppable and off the nodes, the timer
trees typed, the slots P1's cap-slot words and off the debug links and the
nodes, the creation's frame (`retFrame_writesIn`), the window zero
(`winInit_of_winZero`), the debug lists (`dbgLinks_nonTcb`, or the named TCB
case), the window placed. -/
theorem createOK_core {H1 : Heap} {Cs : Set U64} {sR s' : S} {thR : TypedHeap} {A k w n us : Nat}
    {T pml4 Z : Prop} (hP : Placed thR) (hH : HeapOK H1)
    (hDrop : DropOK st H1 (RegionD H1 A (A + w * k)) Cs sR) (hRON : RegionOffNodes st Cs sR A (A + w * k))
    (hTm : TimerOK st H1.tcbs Cs sR) (hSC : SlotCapW thR H1.tcbs H1.omega H1.frame)
    (hsoff : ∀ v, SlotSpan thR v → (∀ y, H1 y = some .tcb → v ≠ dnA y ∧ v ≠ dpA y) ∧
      (∀ c ∈ Cs, v.val < L.nodeBase sR c ∨ L.nodeBase sR c + 4288 ≤ v.val))
    (hW : WFrame (L := L) sR s' (fun v => ((T ∧ TcbLoopW thR A w (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
      (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan thR v) ∨
      (pml4 ∧ A ≤ v.val ∧ v.val < A + w * k)))
    (hWZ : Z → WinZero (L.mem s') A k w T)
    (hk : k = 2 ^ zOf n us) (hAk : A % k = 0) (hTn : T ↔ n = 1)
    (hZ : (newKind n us).isSome → (∀ z, newKind n us ≠ some (.other z)) → Z)
    (hn5 : n = 5 → 7 ≤ us) (hk12 : n = 1 → zOf n us = 12)
    (hDbgT : n = 1 → DbgLinksOK st H1 Cs s' A (A + w * k) A k w n)
    (h0Cs : 0#u64 ∈ Cs) (hfitW : A + w * k ≤ 2 ^ 64) (hpos : 0 < A) :
    CreateOK st H1 Cs sR s' := by
  have hkd : ∀ kd, newKind n us = some kd → 2 ^ kd.bits = k := fun kd h => by rw [newKind_bits h, hk]
  refine ⟨A, A + w * k, A, k, w, n, us, le_rfl, le_rfl, fun kd h => (hkd kd h).le, hDrop, hRON, ?_, ?_, ?_, ?_⟩
  · -- the frame
    exact retFrame_writesIn hW hP hSC ⟨0#u64, h0Cs, rfl⟩ (fun hne => (hTm.dh _ h0Cs).resolve_left hne)
      (fun hT => by rw [hk, hk12 (hTn.1 hT)]; rfl) hfitW
  · -- the window's words
    refine winInit_of_winZero (fun hs ho w hw h1 h2 => ?_) (fun h1 => by rw [hk, hk12 h1]; rfl) hfitW
    exact ((hWZ (hZ hs ho)) w hw h1 h2).imp id (fun ⟨hT, hj⟩ => ⟨hTn.1 hT, hj⟩)
  · -- the debug lists
    by_cases hn1 : n = 1
    · exact hDbgT hn1
    have hnT : ¬ T := fun h => hn1 (hTn.1 h)
    refine dbgLinks_nonTcb hn1 hDrop hTm hW (fun v hv => ?_) (fun y hy => ?_) (fun c hc => ?_)
    · rcases hv with (⟨hT, -⟩ | hsl) | ⟨-, h1, h2⟩
      · exact absurd hT hnT
      · obtain ⟨o1, o2⟩ := hsoff v hsl
        refine ⟨fun y hy _ => o1 y hy, fun c hc e => ?_⟩
        have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
        have := o2 c hc
        rw [e, hv0] at this
        have : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
        omega
      · refine ⟨fun y hy hyD => ?_, fun c hc e => ?_⟩
        · have hdn : (dnA y).val = y.val + 3576 := tcb_word hH hy (by simp)
          have hdp : (dpA y).val = y.val + 3584 := tcb_word hH hy (by simp)
          unfold RegionD at hyD; rw [show H1 y = some .tcb from hy] at hyD
          simp only [Option.elim, MeetsR, HKind.bits] at hyD
          exact ⟨fun e => by rw [e, hdn] at h1 h2; omega, fun e => by rw [e, hdp] at h1 h2; omega⟩
        · have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
          rw [e, hv0] at h1 h2
          have := hRON.1 c hc
          have : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
          omega
    · have hal := hH.align y .tcb hy
      simp only [HKind.bits] at hal
      have hdn : (dnA y).val = y.val + 3576 := tcb_word hH hy (by simp)
      have hdp : (dpA y).val = y.val + 3584 := tcb_word hH hy (by simp)
      unfold P1.Aligned
      rw [hdn, hdp]; omega
    · exact nodeAt_aligned (hTm.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS])
  · -- the window's placement
    refine ⟨fun kd h => ?_, hfitW, hpos, hn5⟩
    rw [← hkd kd h] at hAk ⊢
    exact ⟨hAk, Nat.mod_self _⟩

/-! ## The creation without a reset -/

/-- **P1's `CreateOK` for a retype without a reset** (`createOK_core` over
`H` from the restart): the window in the source cap's free part
(`RetExp.usrc`), its objects dead (`retype_window_dead`) and droppable
(`dead_dropOK`), the window off the nodes, the slots in `H`'s objects. -/
theorem createOK_noreset {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s0 s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {p sb fi : U64} {dev : Bool}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot (.Untyped p sb fi dev) extra th G D σ pp rs idx)
    (hfr : Frame2 (L := L) s0 s (stA (L.curW s0)) (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION))
    (hks : L.ksb s = L.ksb s0) (hcpu : L.cpu s = L.cpu s0)
    (hcw : L.curW s = L.curW s0) (hcs : L.cscW s = L.cscW s0) (hact : ∀ y ∈ H.tcbs, L.actionW s ≠ y)
    (hrun : Runnable (L.mem s0 (stA (L.curW s0)))) (hTm : TimerOK st H.tcbs Cs s)
    {th' : TypedHeap} {m' : U64 → U64} {G' : MdbGhost} {A k w : Nat} {dslot : Nat → U64}
    {cj : Nat → capability.Cap} (hE : RetExp th th' (L.mem s0) m' G G' A k w dslot cj slot)
    {s' : S} {n us : Nat} {T pml4 Z : Prop}
    (hW : WFrame (L := L) s s' (fun v => ((T ∧ TcbLoopW th A w (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan th v) ∨
      (pml4 ∧ A ≤ v.val ∧ v.val < A + w * k)))
    (hWZ : Z → WinZero (L.mem s') A k w T)
    (hk : k = 2 ^ zOf n us) (hAk : A % k = 0) (hTn : T ↔ n = 1)
    (hZ : (newKind n us).isSome → (∀ z, newKind n us ≠ some (.other z)) → Z)
    (hn5 : n = 5 → 7 ≤ us) (hk12 : n = 1 → zOf n us = 12)
    (hKR : (∀ q kd, H q = some kd → RegionD H A (A + w * k) q → q ∈ D) →
      KeptRefsP3 (L := L) H (RegionD H A (A + w * k)) s)
    (hDT : (∀ q kd, H q = some kd → RegionD H A (A + w * k) q → q ∈ D) →
      DbgTimerKept (L := L) H (RegionD H A (A + w * k)) Cs s)
    (hDbgT : n = 1 → DbgLinksOK st H Cs s' A (A + w * k) A k w n)
    (h0Cs : 0#u64 ∈ Cs) :
    CreateOK st H Cs s s' := by
  obtain ⟨Tr, C, hJP⟩ := J.jpl
  obtain ⟨-, hx, hcx⟩ := J.slot_mem (by simp)
  obtain ⟨-, p0, sb0, fi0, fi1, d0, hc0, -, hpA, -, hAs, -, -⟩ := hE.usrc
  rw [hcx] at hc0
  simp only [capability.Cap.Untyped.injEq] at hc0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hc0
  have U := J.utc p sb fi dev rfl
  obtain ⟨hk1, hk2⟩ := J.jcov.ks slot hx p sb fi dev hcx
  have hfitW : A + w * k ≤ 2 ^ 64 := le_trans hAs U.pfit
  have hpos : 0 < A := by have := U.high; omega
  have hnb : ∀ c, L.nodeBase s c = L.nodeBase s0 c := fun c => by simp [LawfulStore.nodeBase, hks]
  have RD : ∀ q kd, H q = some kd → RegionD H A (A + w * k) q → q ∈ D ∧ DeadP (L := L) H s0 q := by
    intro q kd hq hr
    refine (retype_window_dead J.jcov J.ut J.mdb hE).1 q kd hq ?_
    unfold RegionD at hr; rw [hq] at hr; simp only [Option.elim] at hr
    unfold MeetsR at hr; unfold MeetsW; omega
  have hRON : RegionOffNodes st Cs s A (A + w * k) := by
    refine ⟨fun c hc => ?_, ?_⟩
    · rw [hnb]; rcases hk2 c hc with h | h <;> omega
    · rw [hks]; rcases hk1 with h | h <;> omega
  refine createOK_core J.placed J.heap (dead_dropOK J RD hfr hks hcpu hcw hcs hact hrun
    (hKR fun q kd hq hr => (RD q kd hq hr).1) (hDT fun q kd hq hr => (RD q kd hq hr).1)) hRON hTm
    (slotCapW_of_in J.placed J.heap (fun a ha => hJP.slot_in ha)) (fun v hv => ?_) hW hWZ hk hAk hTn hZ hn5 hk12
    hDbgT h0Cs hfitW hpos
  obtain ⟨o1, o2⟩ := slot_word_off hJP J.hnd hv
  exact ⟨o1, fun c hc => by rw [hnb]; exact o2 c hc⟩

/-! ## The creation after a reset -/

/-- **`DropOK` of a range no object meets** (the window after a reset, over
the heap without the untyped's region): nothing to drop. -/
theorem dropOK_none {H1 : Heap} {Cs : Set U64} {s : S} {lo hi : Nat} (hH : HeapOK H1) (h0 : H1 0#u64 = none)
    (hno : ∀ q k, H1 q = some k → ¬ RegionD H1 lo hi q)
    (hcur : H1 (L.curW s) ≠ none) (hcsc : H1 (L.cscW s) ≠ none) :
    DropOK st H1 (RegionD H1 lo hi) Cs s := by
  have nd : ∀ x, H1 x ≠ none → ¬ RegionD H1 lo hi x := fun x hx => by
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hx; exact hno x k hk
  have kr : ∀ x, KeptRef H1 (RegionD H1 lo hi) x := fun x hx => nd x hx
  refine ⟨hH, h0, fun q k hq hD => absurd hD (hno q k hq), nd _ hcur, nd _ hcsc,
    fun _ _ _ p k hp hD => absurd hD (hno p k hp), fun _ _ _ _ _ p k hp hD => absurd hD (hno p k hp),
    fun _ _ _ _ => kr _, fun _ _ _ => kr _, fun _ _ _ => kr _, fun _ _ _ => kr _, fun _ _ _ => kr _,
    fun _ _ _ => kr _, fun _ _ _ => kr _, fun _ _ _ => kr _, fun _ _ _ => ⟨kr _, kr _, kr _, kr _, kr _⟩,
    fun _ _ => ⟨kr _, kr _, kr _⟩⟩

/-- **The slots of the restricted typed heap lie in kept objects** (the
heap without the region's objects): a slot's object is outside the region
(`restrictTh`, `NoStraddle`), its `H` object (`JPlaced`) the same range. -/
theorem slotIn_restrict {th : TypedHeap} {H : Heap} {Tr C : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hJP : JPlaced (L := L) th H Tr C s σ) {lo hi : Nat} (hN : NoStraddle th lo hi) :
    ∀ a, IsSlot (restrictTh th lo hi) a → ∃ q k, H.drop (RegionD H lo hi) q = some k ∧ q.val ≤ a.val ∧
      a.val + 32 ≤ q.val + 2 ^ k.bits ∧ (k = .tcb → a.val + 32 ≤ q.val + 192) ∧ (k = .tcb ∨ ∃ z, k = .other z) := by
  rintro a ⟨q, i, hqi, rfl⟩
  have hv := hqi.val hJP.pl.restrict
  have hout : ∀ kq, restrictTh th lo hi q = some kq → q.val + objSize kq ≤ lo ∨ hi ≤ q.val :=
    fun kq h => restrict_obj_out hN h
  rcases hqi with ⟨r, hq, hi'⟩ | ⟨hq, hi'⟩
  · have hH := hJP.cnode q r (restrictTh_some hq).1
    have ho := hout _ hq
    simp only [objSize] at ho
    have e : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
    refine ⟨q, _, Heap.drop_eq_some.2 ⟨?_, hH⟩, by rw [hv]; omega, ?_, fun e => (by cases e), Or.inr ⟨_, rfl⟩⟩
    · unfold RegionD; rw [hH]; simp only [Option.elim, MeetsR, HKind.bits]; rw [e]; omega
    · rw [hv]; simp only [HKind.bits]; rw [e]
      have : i + 1 ≤ 2 ^ r := hi'
      nlinarith
  · have hH := (hJP.tcb q).1 (restrictTh_some hq).1
    have ho := hout _ hq
    simp only [objSize] at ho
    refine ⟨q, _, Heap.drop_eq_some.2 ⟨?_, hH⟩, by rw [hv]; omega, ?_, fun _ => ?_, Or.inl rfl⟩
    · unfold RegionD; rw [hH]; simp only [Option.elim, MeetsR, HKind.bits]; omega
    · rw [hv]; simp only [HKind.bits, tcbSlots] at hi' ⊢; omega
    · rw [hv]; simp only [tcbSlots] at hi'; omega

/-- **The spec's `invoke_untyped` without a reset does not fail**: every
outcome is `ok` (`liftE`). -/
theorem invokeUntyped_noreset_ok (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (sl : Fl4Spec.CslotPtr)
    (b rb : Fl4Spec.ObjRef) (t : Fl4Spec.ApiObjectType) (us : Nat) (slots : List Fl4Spec.CslotPtr) (dev : Bool)
    (σ : Fl4Spec.State Unit) :
    ∀ x ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl false b rb t us slots dev)).run σ).1,
      x.1 = .ok () := by
  unfold Fl4Spec.invokeUntypedWith
  simp only [Fl4Spec.NonDetE.whenE, Bool.false_eq_true, ↓reduceIte, ndE_pure_bind]
  intro x hx
  unfold Fl4Spec.NonDetE.liftE at hx
  rw [ExceptT.run_lift] at hx
  obtain ⟨y, -, hy⟩ := hx
  rw [Set.mem_singleton_iff.1 hy]

/-- **P1's `CreateOK` after a reset** (`createOK_core` over the heap without
the untyped's region, `utHeap`): nothing in the window to drop
(`dropOK_none`), the window off the nodes, the slots of the typed heap at the
creation in kept objects. -/
theorem createOK_reset {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s0 sR : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {p sb fi : U64} {dev : Bool}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot (.Untyped p sb fi dev) extra th G D σ pp rs idx)
    (hksR : L.ksb sR = L.ksb s0)
    (hcurR : H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) (L.curW sR) ≠ none)
    (hcscR : H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) (L.cscW sR) ≠ none)
    (hTm : TimerOK st (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))).tcbs Cs sR)
    {thR : TypedHeap} (hPR : Placed thR) (hsub : ∀ a, IsSlot thR a → IsSlot th a)
    (hslot : ∀ a, IsSlot thR a → ∃ q k, H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) q = some k ∧
      q.val ≤ a.val ∧ a.val + 32 ≤ q.val + 2 ^ k.bits ∧ (k = .tcb → a.val + 32 ≤ q.val + 192) ∧
      (k = .tcb ∨ ∃ z, k = .other z))
    {A k w : Nat} (hlo : p.val ≤ A) (hhi : A + w * k ≤ p.val + 2 ^ sb.val)
    {s' : S} {n us : Nat} {T pml4 Z : Prop}
    (hW : WFrame (L := L) sR s' (fun v => ((T ∧ TcbLoopW thR A w (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
      (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan thR v) ∨
      (pml4 ∧ A ≤ v.val ∧ v.val < A + w * k)))
    (hWZ : Z → WinZero (L.mem s') A k w T)
    (hk : k = 2 ^ zOf n us) (hAk : A % k = 0) (hTn : T ↔ n = 1)
    (hZ : (newKind n us).isSome → (∀ z, newKind n us ≠ some (.other z)) → Z)
    (hn5 : n = 5 → 7 ≤ us) (hk12 : n = 1 → zOf n us = 12)
    (hDbgT : n = 1 → DbgLinksOK st (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) Cs s' A (A + w * k) A k w n)
    (h0Cs : 0#u64 ∈ Cs) :
    CreateOK st (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) Cs sR s' := by
  obtain ⟨Tr, C, hJP⟩ := J.jpl
  obtain ⟨-, hx, hcx⟩ := J.slot_mem (by simp)
  have U := J.utc p sb fi dev rfl
  obtain ⟨hk1, hk2⟩ := J.jcov.ks slot hx p sb fi dev hcx
  have hfitW : A + w * k ≤ 2 ^ 64 := le_trans hhi U.pfit
  have hpos : 0 < A := by have := U.high; omega
  have hnb : ∀ c, L.nodeBase sR c = L.nodeBase s0 c := fun c => by simp [LawfulStore.nodeBase, hksR]
  have hH1 : HeapOK (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) := J.heap.drop
  have hno : ∀ q kd, H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) q = some kd →
      ¬ RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) A (A + w * k) q := by
    intro q kd hq hr
    obtain ⟨hnr, hq'⟩ := Heap.drop_eq_some.1 hq
    have e1 : RegionD (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))) A (A + w * k) q =
        MeetsR A (A + w * k) q.val (q.val + 2 ^ kd.bits) := by rw [RegionD, hq]; rfl
    have e2 : RegionD H p.val (p.val + 2 ^ sb.val) q = MeetsR p.val (p.val + 2 ^ sb.val) q.val (q.val + 2 ^ kd.bits) := by
      unfold RegionD; rw [hq']; rfl
    rw [e1] at hr; rw [e2] at hnr
    simp only [MeetsR] at hr hnr; omega
  have hRON : RegionOffNodes st Cs sR A (A + w * k) := by
    refine ⟨fun c hc => ?_, ?_⟩
    · rw [hnb]; rcases hk2 c hc with h | h <;> omega
    · rw [hksR]; rcases hk1 with h | h <;> omega
  refine createOK_core hPR hH1 (dropOK_none hH1 (HeapOK.drop0 J.h0) hno hcurR hcscR) hRON hTm
    (slotCapW_of_in hPR hH1 hslot) (fun v hv => ?_) hW hWZ hk hAk hTn hZ hn5 hk12 hDbgT h0Cs hfitW hpos
  obtain ⟨a, ha, h1, h2⟩ := hv
  obtain ⟨o1, o2⟩ := slot_word_off hJP J.hnd ⟨a, hsub a ha, h1, h2⟩
  exact ⟨fun y hy => o1 y (Heap.drop_eq_some.1 hy).2, fun c hc => by rw [hnb]; exact o2 c hc⟩

/-- **An unused untyped cap's region holds no slot** (`SpecFree` with free
index 0): every slot's object is a spec object, outside the region, so kept
by `restrictTh`. -/
theorem UtJoint.slots_unused {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {p sb : U64} {dev : Bool}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s slot (.Untyped p sb 0#u64 dev) extra th G D σ pp rs idx) :
    ∀ a, IsSlot th a → IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) a := by
  obtain ⟨-, hx, hcx⟩ := J.slot_mem (by simp)
  have hout : ∀ (q : U64) ko, σ.kheap q.bv = some ko → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) := by
    intro q ko hk ⟨h1, h2⟩
    have e : q.bv.toNat = q.val := rfl
    have hb := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
    have := J.sfree slot hx p sb 0#u64 dev hcx q.bv ko hk
    rw [e] at this
    simp only [UScalar.val, show (0#u64 : U64).bv.toNat = 0 from rfl] at this ⊢
    rcases this with (h | h) | ⟨-, h⟩ <;> simp only [UScalar.val] at h1 h2 <;> omega
  rintro a ⟨q, i, hqi, rfl⟩
  refine ⟨q, i, ?_, rfl⟩
  have hn : ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) := by
    rcases hqi with ⟨r, hq, -⟩ | ⟨hq, -⟩
    · obtain ⟨cs, hk, -⟩ := J.rel.cnode q r hq; exact hout q _ hk
    · obtain ⟨tc, hk, -⟩ := J.rel.tcb q hq; exact hout q _ hk
  unfold IsSlotAt; rw [restrictTh_out hn]; exact hqi

/-! ## The run -/

/-- **The restart from the decode's start**: its frame (`Frame2`), the
kernel-global base and the core kept, the invoked slot's cap kept. -/
theorem UtJoint.restart {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s0 s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {cap : capability.Cap}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot cap extra th G D σ pp rs idx)
    (hrs : sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s) :
    Frame2 (L := L) s0 s (stA (L.curW s0)) (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION) ∧
      L.ksb s = L.ksb s0 ∧ L.cpu s = L.cpu s0 ∧ capAt (L.mem s) slot = ok cap := by
  have htf := J.placed.fits _ _ J.curT
  have hta := J.placed.align _ _ J.curT
  have hstv : (stA (L.curW s0)).val = (L.curW s0).val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th J.placed s0 (L.curW s0)
    sched.TS_RESTART J.curT J.act)
  obtain ⟨s2', hs2', hF⟩ := spec_exists (set_thread_state_frame (L := L) s0 (L.curW s0) sched.TS_RESTART
    (by unfold P1.Aligned; rw [hstv]; omega) J.act.1)
  obtain ⟨s2k, hs2k, hk2⟩ := spec_exists (sts_ksb_ret (L := L) s0 (L.curW s0) sched.TS_RESTART)
  obtain ⟨s2c, hs2c, hc2⟩ := spec_exists (sts_cpu (L := L) s0 (L.curW s0) sched.TS_RESTART)
  rw [hrs] at hs2 hs2' hs2k hs2c
  cases eq_of_ok_eq hs2; cases eq_of_ok_eq hs2'; cases eq_of_ok_eq hs2k; cases eq_of_ok_eq hs2c
  refine ⟨hF, hk2, hc2, ?_⟩
  rw [hSS.capAt (by rw [J.slotEq]; exact AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [J.idxLen] using J.node)⟩)]
  exact J.capEq

/-- **The reset's heap** (P1's `resetP1Step_holds` on the reset's
equation): the timer trees typed over `H` without the region, the current
thread, SC and action kept. -/
theorem reset_heap {A' : Type} {arI : machine.Arch A'} (hA : P0.ArchTotal arI) {H : Heap} {Cs Ac : Set U64}
    {s sR : S} {ar a1 : A'} {x p sb fi : U64} {dev : Bool}
    (hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s)
    (hx : CapSlotW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) x)
    (hR : ResetOK st H Cs s x p sb fi dev)
    (heq : untyped.reset_untyped st arI s ar x = ok (.Ok (), sR, a1)) :
    TimerOK st (H.drop (RegionD H p.val (p.val + 2 ^ sb.val))).tcbs Cs sR ∧ ResetKeeps st s sR := by
  obtain ⟨hcap, hpal, hfit, hdrop, hnode, hfi⟩ := hR
  obtain ⟨r', hr', H1, Ac1, hb1, hsh, -, hk⟩ := spec_exists (resetP1Step_holds (st := st) hA H Cs Ac s ar x p sb fi
    dev hb hcap hx hpal hfit hdrop hnode hfi)
  rw [heq] at hr'; cases eq_of_ok_eq hr'
  have e : H1 = H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) := by
    funext q; rw [hsh q]; unfold Heap.drop RegionD; split_ifs <;> rfl
  subst e
  exact ⟨hb1.2.2.1.2.2.tm, hk⟩

/-- The new kinds that are not untracked: TCBs, endpoints, notifications,
SCs and replies. -/
theorem newKind_core {n us : Nat} (hs : (newKind n us).isSome) (ho : ∀ z, newKind n us ≠ some (.other z)) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 6 := by
  unfold newKind at hs ho; split_ifs at hs ho <;> simp_all

theorem utHeap_false (H : Heap) (p sb : U64) : utHeap H false p sb = H := rfl
theorem utHeap_true (H : Heap) (p sb : U64) :
    utHeap H true p sb = H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) := rfl

/-- **[J] [RegionUnref] No live object's link points into a dead region**
(the consequence of l4v `sym_refs`, `valid_replies` and `valid_untyped` that
l4v's retype and `detype` proofs use): after the restart from a joint state,
for any range whose `H` objects are all dead (`D`), the kept objects' links
name none of them: the spec-side links (`KeptRefsP3`: bound notifications,
SC notifications, reply stacks, yield-to/from) and FL4's own timer trees and
debug lists (`DbgTimerKept`). Named; deferred to the invariant-preservation
phase. Routes found: (1) spec `sym_refs` fragments for the bound links
(TCB↔notification, SC↔notification) plus l4v `valid_replies` for the reply
stacks, as `SchedValid` fields through the relations; or (2) P1-side
symmetries in `ScExtra` (next to `nsc`) for the bound links; and (3) for
yield, `DeadP` extended with the TCB's `yieldA` and the SC's `scYieldFromA`
(cleared by finalisation) plus the missing direction "yield-to names a
yield-from"; the timer/debug part needs "the timer trees' and debug lists'
members are live TCBs" ([W]). -/
def RegionUnref {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64) : Prop :=
  ∀ (s0 s : S) (slot : obj.Slot) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (th : TypedHeap) (G : MdbGhost) (D : Set U64) (σ : Fl4Spec.State Unit) (pp : U64) (rs : Nat) (idx : List Bool),
    UtJoint (L := L) arI H Cs s0 slot cap extra th G D σ pp rs idx →
    sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    ∀ lo hi : Nat, (∀ q k, H q = some k → RegionD H lo hi q → q ∈ D) →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s

/-- **[DbgLinksOK for new TCBs]** (named): a TCB retype's creation links the
new TCBs into core 0's debug list (`debug_insert` in the creation loop), so
the debug links after it name null, kept TCBs or the new ones. -/
def UtDbgTcbP {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64)
    (P3Ok : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop :=
  ∀ (s0 s : S) (a : A') (extra : Aeneas.Std.Array obj.Slot 3#usize) (slot ptr sb fi : U64) (dev reset : Bool)
    (aligned nt us dest off win : U64),
    P3Ok s0 slot (.Untyped ptr sb fi dev) extra →
    sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    UtArgs st s0 extra slot ptr sb fi dev reset aligned nt us dest off win → nt.val = 1 →
    untyped.retype st arI s a slot reset aligned nt us dest off win dev ⦃ r s' a' => r = .Ok () →
      DbgLinksOK st (utHeap H reset ptr sb) Cs s' aligned.val (aligned.val + win.val * 4096) aligned.val 4096
        win.val 1 ⦄

/-- `UtDbgTcbP` at `UtP3Ok`. -/
abbrev UtDbgTcb {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64) : Prop :=
  UtDbgTcbP (L := L) arI H Cs (UtP3Ok (L := L) arI H Cs)

/-- P1's `UtRetypeP3.run` conclusion. -/
def UtRunPost {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64) (s : S) (a : A') (slot ptr sb fi : U64)
    (dev reset : Bool) (aligned nt us dest off win : U64) : Prop :=
  (reset = true → ResetOK st H Cs s slot ptr sb fi dev) ∧
  untyped.retype st arI s a slot reset aligned nt us dest off win dev ⦃ r s' a' =>
    (reset = true ∧ r ≠ .Ok () ∧ untyped.reset_untyped st arI s a slot = ok (r, s', a')) ∨
    (r = .Ok () ∧ ∃ sR, ((reset = false ∧ sR = s) ∨
        (reset = true ∧ ∃ a1, untyped.reset_untyped st arI s a slot = ok (.Ok (), sR, a1))) ∧
      CreateOK st (utHeap H reset ptr sb) Cs sR s') ⦄

/-- **[The VT-x types]** (named): the retype of the VT-x objects (types 14
to 18: VMCS, EPT tables), outside `retype_cont_allN`'s native types. -/
def UtVtxP {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs U : Set U64)
    (P3Ok : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop :=
  ∀ (Ac : Set U64) (s0 s : S) (a : A') (extra : Aeneas.Std.Array obj.Slot 3#usize) (slot ptr sb fi : U64)
    (dev reset : Bool) (aligned nt us dest off win : U64),
    P3Ok s0 slot (.Untyped ptr sb fi dev) extra →
    sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    DecPre st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits U Ac s0 (.Untyped ptr sb fi dev) extra →
    CapSlotW H.tcbs H.omega H.frame slot →
    UtArgs st s0 extra slot ptr sb fi dev reset aligned nt us dest off win →
    Cur0 st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s0 s →
    13 < nt.val → UtRunPost (L := L) arI H Cs s a slot ptr sb fi dev reset aligned nt us dest off win

/-- `UtVtxP` at `UtP3Ok`. -/
abbrev UtVtx {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs U : Set U64) : Prop :=
  UtVtxP (L := L) arI H Cs U (UtP3Ok (L := L) arI H Cs)

/-- **A state predicate gives the joint state and the region facts** after
the restart: some `UtJoint` at the decode's start, and `RegionUnref`'s
conclusion for its dead set. -/
def UtOkRU {A' : Type} (arI : machine.Arch A') (H : Heap) (Cs : Set U64)
    (P3Ok : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop :=
  ∀ (s0 s : S) (slot : obj.Slot) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    P3Ok s0 slot cap extra → sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    ∃ th G D σ pp rs idx, UtJoint (L := L) arI H Cs s0 slot cap extra th G D σ pp rs idx ∧
      ∀ lo hi : Nat, (∀ q k, H q = some k → RegionD H lo hi q → q ∈ D) →
        KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s

theorem utOkRU_of {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64}
    (hRU : RegionUnref (L := L) arI H Cs) : UtOkRU (L := L) arI H Cs (UtP3Ok (L := L) arI H Cs) := by
  rintro s0 s slot cap extra ⟨th, G, D, σ, pp, rs, idx, J⟩ hrs
  exact ⟨th, G, D, σ, pp, rs, idx, J, hRU _ _ _ _ _ _ _ _ _ _ _ _ J hrs⟩

set_option maxHeartbeats 4000000 in
/-- **P1's `UtRetypeP3` with `UtP3Ok` as `P3Ok`**: the reset's facts
(`resetOK_of`), and the retype's outcome from `retype_postN`: the reset's
preemption (a retype without a reset does not fail,
`invokeUntyped_noreset_ok`), or the creation over `H` without a reset
(`createOK_noreset`), over `H` without the region after a reset
(`createOK_reset`, the unused region's slots kept, `UtJoint.slots_unused`).
Named: the kept links (`RegionUnref`), the new TCBs' debug links
(`UtDbgTcb`), the VT-x types (`UtVtx`). -/
theorem utRetypeP3_gen [P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (hA : P0.ArchTotal arI) (H : Heap) (Cs U : Set U64)
    (Adm : PSets → Prop) (hAdm : ∀ H' : Heap, HeapOK H' → H' 0#u64 = none → Adm (PSets.ofHeap H'))
    (h0Cs : 0#u64 ∈ Cs) (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (P3Ok : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop)
    (hOk : UtOkRU (L := L) arI H Cs P3Ok) (hDbg : UtDbgTcbP (L := L) arI H Cs P3Ok)
    (hVtx : UtVtxP (L := L) arI H Cs U P3Ok) :
    UtRetypeP3 st arI Adm H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits U P3Ok := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hAdm, h0Cs, ?_⟩
  · intro Ac s a len slot buf ptr sb fi dev extra h
    simp at h
  intro Ac s0 s a extra slot ptr sb fi dev reset aligned nt us dest off win hP3 hrs hDP hCSW hUA hC0
  by_cases hnt : 13 < nt.val
  · exact hVtx Ac s0 s a extra slot ptr sb fi dev reset aligned nt us dest off win hP3 hrs hDP hCSW hUA hC0 hnt
  have hP3' := hP3
  obtain ⟨th, G, D, σ, pp, rs, idx, J, hRUJ⟩ := hOk _ _ _ _ _ hP3 hrs
  obtain ⟨hfr, hks, hcpu, hcapS⟩ := J.restart hrs
  obtain ⟨-, Ac', hbx, hcw, hcs, -, hact, -⟩ := hC0
  have hrun := hDP.run
  have hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac' s := ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  have hTm : TimerOK st H.tcbs Cs s := hbx.2.2.1.2.2.tm
  obtain ⟨⟨r0, s', a'⟩, hv, t, r, fiv, hctx, haleq, hRP⟩ :=
    spec_exists (retype_postN (ar := a) arI J hrs hUA (by omega) hrcb hppS)
  -- the reset's facts
  have hcapS' : obj.Slot.cap st slot s = ok (.Untyped ptr sb fi dev) := by rw [slot_cap_eq]; exact hcapS
  have hnc : reset = true → ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := fun h => by
    have := hctx.resetEq; rw [h] at this; simpa using this.symm
  have hROK : reset = true → ResetOK st H Cs s slot ptr sb fi dev := fun h =>
    resetOK_of J hfr hks hcpu hcw hcs hact hrun hcapS' (hnc h) (fun hd => (hRUJ _ _ hd).1)
      (fun hd => (hRUJ _ _ hd).2)
  refine ⟨hROK, ?_⟩
  rw [hv, WP.spec_ok]
  -- the outcome
  obtain ⟨σ1, -, -, e, σ', G', th', he, hhas, -, -, -, -, -, -, -, -, -, hksv, A, k, w, dslot, cj, hE, hRF, -⟩ :=
    hRP
  obtain ⟨ct, s1, hct, hs1, hbr⟩ := hRF
  rw [cur_thread_eq (L := L) s0] at hct; cases eq_of_ok_eq hct
  rw [show sched.set_thread_state st s0 (L.mem s0 (L.nodeAt s0 (L.cpu s0) layout.node.CUR_THREAD))
    sched.TS_RESTART = ok s from hrs] at hs1
  have e1 := eq_of_ok_eq hs1; subst s1
  have hx : cslotAddr (pp.bv, idx) = slot := J.slotEq.symm
  simp only [invSrc] at hE; rw [hx] at hE
  have hfo := objTypeOf_fl4 hctx.ty us.val
  rcases hbr with ⟨hErr, hres⟩ | ⟨hOk, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, hlo, hhi, -, hsl, -, -, hW, hWZ, -⟩
  · -- the reset preempted
    left
    have hr0 : r0 = .Err .Preempted := hErr
    have hR : reset = true := by
      cases reset
      · exfalso
        have he' : e = .error () := by
          rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact absurd (hr0.symm.trans h1) (by simp)
          · exact h2
        obtain ⟨y, hy, hy1, -⟩ := hhas
        have := invokeUntyped_noreset_ok _ _ _ _ _ _ _ _ _ y hy
        rw [hy1, he'] at this; cases this
      · rfl
    refine ⟨hR, by rw [hr0]; simp, ?_⟩
    rw [← hx]; exact hres
  · right
    have hr0 : r0 = .Ok () := hOk
    refine ⟨hr0, ?_⟩
    have hk : k = 2 ^ zOf nt.val us.val := by rw [ek, hfo.2.1]
    have hTn : t = .tcbObject ↔ nt.val = 1 := hfo.2.2.2.2.2.2
    have hZ : (newKind nt.val us.val).isSome → (∀ z, newKind nt.val us.val ≠ some (.other z)) →
        dev = false ∧ t ≠ .archObject .pml4Obj := by
      intro hs ho
      have hc := newKind_core hs ho
      refine ⟨?_, ?_⟩
      · cases hd : dev
        · rfl
        · rcases hctx.device hd with h | h
          · have := hfo.2.2.1.1 h; omega
          · have := hfo.2.2.2.1.1 h; omega
      · intro ht; have := hctx.ty; rw [ht] at this
        rcases hc with h | h | h | h | h <;> rw [h] at this <;> simp [objTypeOf] at this
    have hn5 : nt.val = 5 → 7 ≤ us.val := fun h => by have := hctx.size.2.2.2.2; omega
    have hk12 : nt.val = 1 → zOf nt.val us.val = 12 := fun h => by rw [h]; rfl
    have hAal : A = aligned.val := by rw [eA, haleq]; rfl
    have hwin : w = win.val := by rw [ew]; simp [windowSlots]
    have hDbgT : nt.val = 1 → DbgLinksOK st (utHeap H reset ptr sb) Cs s' A (A + w * k) A k w nt.val := by
      intro h1
      obtain ⟨v', hv', hpost⟩ := spec_exists (hDbg s0 s a extra slot ptr sb fi dev reset aligned nt us dest off win
        hP3' hrs hUA h1)
      rw [hv] at hv'; cases eq_of_ok_eq hv'
      have := hpost hr0
      rw [hAal, hwin, hk, hk12 h1, h1]; exact this
    rcases hor with ⟨hsR, rfl, rfl, rfl, hRB⟩ |
      ⟨a1, p', sb', fi', d', hreset, -, hcs', -, -, -, -, rfl, rfl, rfl, hRB⟩
    · -- no reset, or the reset of an unused region
      subst sR
      cases reset
      · refine ⟨s, Or.inl ⟨rfl, rfl⟩, ?_⟩
        rw [utHeap_false]
        exact createOK_noreset J hfr hks hcpu hcw hcs hact hrun hTm hE hW hWZ hk hAk hTn hZ hn5 hk12
          (fun hd => (hRUJ _ _ hd).1) (fun hd => (hRUJ _ _ hd).2)
          (fun h => by have := hDbgT h; rw [utHeap_false] at this; exact this) h0Cs
      · obtain ⟨⟨p0, sb0, d0, hc0⟩, hres⟩ := hRB rfl
        rw [hx, hcapS] at hc0
        simp only [ok.injEq, capability.Cap.Untyped.injEq] at hc0
        obtain ⟨-, -, rfl, -⟩ := hc0
        have hROK' := hROK rfl
        have hres' : untyped.reset_untyped st arI s a slot = ok (.Ok (), s, a) := by rw [← hx]; exact hres
        obtain ⟨hTm', -⟩ := reset_heap hA hb hCSW hROK' hres'
        refine ⟨s, Or.inr ⟨rfl, a, hres'⟩, ?_⟩
        rw [utHeap_true]
        obtain ⟨Tr, C, hJP⟩ := J.jpl
        have U := J.utc ptr sb 0#u64 dev rfl
        obtain ⟨-, p0, sb0, fi0, fi1, d0, hc0, -, hpA, -, hAs, -, -⟩ := hE.usrc
        rw [capV_of_capAt J.capEq] at hc0
        simp only [capability.Cap.Untyped.injEq] at hc0
        obtain ⟨rfl, rfl, -, -⟩ := hc0
        refine createOK_reset J hks ?_ ?_ hTm' J.placed (fun a h => h)
          (fun a ha => slotIn_restrict hJP U.nostr a (J.slots_unused a ha)) hpA hAs hW hWZ hk hAk hTn hZ hn5 hk12
          (fun h => by have := hDbgT h; rw [utHeap_true] at this; exact this) h0Cs
        · rw [Heap.drop_of_not hROK'.2.2.2.1.cur, hcw, J.curH]; simp
        · rw [Heap.drop_of_not hROK'.2.2.2.1.csc, hcs]; exact J.cscH
    · -- the reset of a used region
      subst hRB
      rw [hx, J.capEq] at hcs'
      simp only [ok.injEq, capability.Cap.Untyped.injEq] at hcs'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcs'
      have hROK' := hROK rfl
      have hres' : untyped.reset_untyped st arI s a slot = ok (.Ok (), sR, a1) := by rw [← hx]; exact hreset
      obtain ⟨hTm', hRK⟩ := reset_heap hA hb hCSW hROK' hres'
      refine ⟨sR, Or.inr ⟨rfl, a1, hres'⟩, ?_⟩
      rw [utHeap_true]
      obtain ⟨Tr, C, hJP⟩ := J.jpl
      have U := J.utc ptr sb fi dev rfl
      refine createOK_reset J (hW.1.symm.trans hksv) ?_ ?_ hTm' J.placed.restrict hsl (slotIn_restrict hJP U.nostr)
        hlo hhi hW hWZ hk hAk hTn hZ hn5 hk12
        (fun h => by have := hDbgT h; rw [utHeap_true] at this; exact this) h0Cs
      · rw [hRK.1, Heap.drop_of_not hROK'.2.2.2.1.cur, hcw, J.curH]; simp
      · rw [hRK.2.1, Heap.drop_of_not hROK'.2.2.2.1.csc, hcs]; exact J.cscH


/-- **P1's `UtRetypeP3` with `UtP3Ok` as `P3Ok`** (`utRetypeP3_gen`). -/
theorem utRetypeP3_of [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (hA : P0.ArchTotal arI) (H : Heap) (Cs U : Set U64)
    (Adm : PSets → Prop) (hAdm : ∀ H' : Heap, HeapOK H' → H' 0#u64 = none → Adm (PSets.ofHeap H'))
    (h0Cs : 0#u64 ∈ Cs) (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hRU : RegionUnref (L := L) arI H Cs) (hDbg : UtDbgTcb (L := L) arI H Cs)
    (hVtx : UtVtx (L := L) arI H Cs U) :
    UtRetypeP3 st arI Adm H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits U
      (UtP3Ok (L := L) arI H Cs) :=
  utRetypeP3_gen arI hA H Cs U Adm hAdm h0Cs hrcb hppS _ (utOkRU_of hRU) hDbg hVtx

end

end

end Fl4Proofs.P3.Sched
