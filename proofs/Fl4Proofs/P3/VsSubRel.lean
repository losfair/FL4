/-
P3 (DESIGN.md §9), VSpace: **`DeriveSubframe` refines the l4h 0029 model**
(Fl4Spec/Ext/VSpace: `decodeDeriveSubframe`, `performDeriveSubframe`).

* `sub_step`: one `cdt::insert` of a 4 KiB alias against the spec's
  `cap_insert`: the CSpace relations (`insert_refines'`), `MdbInv`
  (`InsFCtx.inv`), `UtInv` (`utinv_alias`), the ASID and page-table
  relations (the insert writes slot words only), and `SR` (hypothesis
  `VsSubHyps.insStable`).
* `insert_subframes_rel`: the loop against `mapM_x cap_insert`.
* `subframe_dest_rel`: the node lookup and range checks against
  `subframeNode` and the CNode checks of the decode.
* `derive_subframe_rel`: the decode and the invocation, for the node cap
  present as the first extra cap. Hypotheses beyond the relations: the large
  current thread runnable (`hrun`), and every
  linked cap is disjoint from it, a non-revocable frame, or inside it
  (`hno`, the range fact `MdbInv` needs for the aliases).
-/
import Fl4Proofs.P3.VsSubMdb
import Fl4Proofs.P3.FinFrame
import Fl4Proofs.P3.FinSpec
import Fl4Proofs.P3.VsArch
import Fl4Proofs.P3.VsFrameInv
import Fl4Proofs.P3.VsCapOps
import Fl4Proofs.P3.VsMdbInv
import Fl4Spec.Ext.VSpace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section Spec
open Fl4Spec

/-- An alias is in the large frame's region (l4v `same_region_as`). -/
theorem sameRegion_alias {p q : ObjRef} (hpq : p.toNat ≤ q.toNat) (hq : q.toNat + 4096 ≤ p.toNat + 2 ^ 21)
    (hfit : p.toNat + 2 ^ 21 ≤ 2 ^ 64) (R R' : CapRights) (mt : VMMapType) (mp : Option (Asid × VSpaceRef)) :
    sameRegionAs (.archObjectCap (.pageCap false p R mt .x64LargePage mp))
      (.archObjectCap (.pageCap false q R' .vmNoMap .x64SmallPage none)) := by
  refine ⟨false, q, R', .vmNoMap, .x64SmallPage, none, rfl, ?_⟩
  have h1 : ((1 : Word) <<< pageBitsForSize .x64LargePage) = BitVec.ofNat 64 (2 ^ 21) := rfl
  have h2 : ((1 : Word) <<< pageBitsForSize .x64SmallPage) = BitVec.ofNat 64 4096 := rfl
  simp only [h1, h2]
  have hp := p.isLt; have hq' := q.isLt
  refine ⟨BitVec.le_def.2 hpq, ?_, ?_⟩ <;> bv_omega

end Spec

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The slot words of the typed heap. -/
def SlotWord (th : TypedHeap) (b : U64) : Prop := ∃ x k, IsSlot th x ∧ Off k ∧ b = wordOf x k

/-- A spec `cap_insert` into a CNode slot: the slot set, the CDT and the
original flags changed. -/
def InsStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ p r cs idx a cdt io, σ.kheap p = some (.cnode r cs) ∧
    σ' = { setCnodeSlot σ p r cs idx a with cdt := cdt, isOriginalCap := io }

/-- The hypotheses of `DeriveSubframe`: the Restart before the inserts, and
`SR` kept by an insert. -/
structure VsSubHyps (A : Type) (P L4 L3 L2 L1 : Set U64) (th : TypedHeap) (SR : S → A → Fl4Spec.State Unit → Prop) :
    Prop where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), SR s a σ → VsRel P (L.mem s) (L.ksb s) σ →
    PtRel L4 L3 L2 L1 (L.mem s) σ → ct.bv = σ.curThread → σ.kheap ct.bv = some (.tcb x) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄
  insStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (SlotWord th) → InsStep σ σ' → SR s' a σ'

/-- The relations the loop carries, for the large frame cap `srcC` at `src`
(revocable bit `rv`). -/
structure SubRel {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (src : U64) (srcC : capability.Cap) (rv : Bool) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop where
  R : StateRel th (L.mem s) σ
  V : SlotsValid th (L.mem s)
  M : MdbLinks th (L.mem s) G
  C : CdtRel th (L.mem s) σ G
  I : MdbInv (L.mem s) G
  U : UtInv (L.mem s) G
  vs : VsRel P (L.mem s) (L.ksb s) σ
  pt : PtRel L4 L3 L2 L1 (L.mem s) σ
  sr : SR s a σ
  cap : capAt (L.mem s) src = ok srcC
  rev : revOf (L.mem s) src = rv
  no : ∀ x ∈ G.chains.flatten, Disj (capV (L.mem s) x) srcC ∨
    (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨ Within srcC (capV (L.mem s) x)
  F : FinInv th (L.mem s) σ G
  /-- The caps of the MDB naming a page of the large frame are frame caps in
  its chain (the aliases, and copies of the large frame). -/
  fr : ∀ w ∈ G.chains.flatten, ∀ q vm : U64, baseF srcC ≤ q.val → q.val < baseF srcC + 2 ^ 21 →
    Ovl (absCap (.Frame q .Small vm false false false 0#u64 0#u64)) (absCap (capV (L.mem s) w)) →
    isFrame (capV (L.mem s) w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch
  /-- The frame invariant (`Vs.FrameInv`). -/
  FR : Vs.FrameInv (L.mem s) G
  /-- The VSpace cap-placement invariant (`VsCapsIn`). -/
  VC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G

end Hyps



section Spec2
open Fl4Spec


private theorem sf_nd_assoc {σ α β γ : Type} (m : NonDet σ α) (f : α → NonDet σ β)
    (g : β → NonDet σ γ) (s : σ) : ((m >>= f) >>= g) s = (m >>= fun a => f a >>= g) s := by
  simp only [nd_bind_apply]
  refine Prod.ext (Set.ext fun r => ?_) (propext ?_)
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨x, ⟨y, hy, hx⟩, hr⟩; exact ⟨y, hy, x, hx, hr⟩
    · rintro ⟨y, hy, x, hx, hr⟩; exact ⟨x, ⟨y, hy, hx⟩, hr⟩
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ((h | ⟨y, hy, h⟩) | ⟨x, ⟨y, hy, hx⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, Or.inl h⟩
      · exact Or.inr ⟨y, hy, Or.inr ⟨x, hx, h⟩⟩
    · rintro (h | ⟨y, hy, h | ⟨x, hx, h⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨y, hy, h⟩)
      · exact Or.inr ⟨x, ⟨y, hy, hx⟩, h⟩

private theorem sf_rbind_assoc {σ ε α β γ : Type} (m : NonDetE σ ε α) (f : α → NonDetE σ ε β)
    (g : β → NonDetE σ ε γ) (s : σ) : ((m >>= f) >>= g).run s = (m >>= fun a => f a >>= g).run s := by
  simp only [ExceptT.run_bind]
  rw [sf_nd_assoc]
  refine congrArg (fun k => (ExceptT.run m >>= k) s) (funext fun x => ?_)
  cases x with
  | ok a => rfl
  | error e => exact nd_pure_bind _ _

/-- The decode after the node lookup. -/
def sfTail (cte : CslotPtr) (p : ObjRef) (r : VMRights) (depth nOff off count mask : Data) (nc : Cap) :
    SEMonad Unit Fl4SubframeInvocation :=
  match nc with
  | .cnodeCap ptr bits _ => do
      let size := 2 ^ bits
      NonDetE.whenE (size - 1 < unat nOff) <|
        NonDetE.throwError (.rangeError 0 (BitVec.ofNat 64 (size - 1)))
      NonDetE.whenE (size - unat nOff < unat count) <|
        NonDetE.throwError (.rangeError 1 (BitVec.ofNat 64 (size - unat nOff)))
      let dests := (List.range' (unat nOff) (unat count)).map fun i => (ptr, natToCref bits i)
      NonDetE.mapMEx ensureEmpty dests
      NonDetE.returnOk ⟨cte, p + off, maskVmRights r (dataToRights mask), dests⟩
  | _ => NonDetE.throwError (.failedLookup false (.missingCapability (unat depth)))

/-- The decode after the frame check. -/
def sfAfter (cte : CslotPtr) (p : ObjRef) (r : VMRights) (index depth nOff off count mask : Data) (nc0 : Cap) :
    SEMonad Unit Fl4SubframeInvocation := do
  NonDetE.whenE (2 ^ 21 ≤ unat off ∨ unat off % 4096 ≠ 0) <| NonDetE.throwError (.invalidArgument 3)
  NonDetE.whenE (unat count < 1 ∨ (2 ^ 21 - unat off) / 4096 < unat count) <|
    NonDetE.throwError (.rangeError 1 (BitVec.ofNat 64 ((2 ^ 21 - unat off) / 4096)))
  let nc ← subframeNode nc0 index depth
  sfTail cte p r depth nOff off count mask nc

theorem decodeSub_main {a0 a1 a2 a3 a4 a5 : Data} {rest : List Data} {nc : Cap} {nsl : CslotPtr}
    {ex : List (Cap × CslotPtr)} (cte : CslotPtr) (p : ObjRef) (r : VMRights) (mt : VMMapType)
    (mp : Option (Asid × VSpaceRef)) :
    decodeDeriveSubframe (Z := Unit) (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest) cte
      (.pageCap false p r mt .x64LargePage mp) ((nc, nsl) :: ex) = sfAfter cte p r a0 a1 a2 a3 a4 a5 nc := by
  unfold decodeDeriveSubframe
  rw [if_neg (by simp)]
  rfl

theorem decodeSub_trunc {args : List Data} {excaps : List (Cap × CslotPtr)} (h : excaps = [] ∨ args.length < 6)
    (cte : CslotPtr) (cap : ArchCap) (σ : State Unit) :
    ExceptT.run (decodeDeriveSubframe (Z := Unit) args cte cap excaps) σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodeDeriveSubframe
  rw [if_pos (by rcases h with rfl | h; exacts [Or.inl rfl, Or.inr h])]; rfl

theorem decodeSub_illegal {args : List Data} {excaps : List (Cap × CslotPtr)} (h1 : excaps ≠ []) (h2 : 6 ≤ args.length)
    (cte : CslotPtr) {cap : ArchCap} (hc : ∀ p r mt mp, cap ≠ .pageCap false p r mt .x64LargePage mp) (σ : State Unit) :
    ExceptT.run (decodeDeriveSubframe (Z := Unit) args cte cap excaps) σ = ({(.error .illegalOperation, σ)}, False) := by
  unfold decodeDeriveSubframe
  rw [if_neg (by simp [List.length_eq_zero_iff, h1]; omega)]
  split
  · rename_i p r mt mp; exact absurd rfl (hc p r mt mp)
  · rfl


section
variable {cte : CslotPtr} {p : ObjRef} {r : VMRights} {index depth nOff off count mask : Data} {nc0 : Cap}
  {σ : State Unit}

theorem sfAfter_inv3 (h : 2 ^ 21 ≤ unat off ∨ unat off % 4096 ≠ 0) :
    ExceptT.run (sfAfter cte p r index depth nOff off count mask nc0) σ = ({(.error (.invalidArgument 3), σ)}, False) := by
  unfold sfAfter; rw [runE_bind_err (by rw [runE_whenE_true h]; rfl)]

theorem sfAfter_range (h1 : ¬ (2 ^ 21 ≤ unat off ∨ unat off % 4096 ≠ 0))
    (h2 : unat count < 1 ∨ (2 ^ 21 - unat off) / 4096 < unat count) :
    ExceptT.run (sfAfter cte p r index depth nOff off count mask nc0) σ =
      ({(.error (.rangeError 1 (BitVec.ofNat 64 ((2 ^ 21 - unat off) / 4096))), σ)}, False) := by
  unfold sfAfter; rw [runE_bind_ok (runE_whenE_false h1 _ σ), runE_bind_err (by rw [runE_whenE_true h2]; rfl)]

theorem sfAfter_go (h1 : ¬ (2 ^ 21 ≤ unat off ∨ unat off % 4096 ≠ 0))
    (h2 : ¬ (unat count < 1 ∨ (2 ^ 21 - unat off) / 4096 < unat count)) :
    ExceptT.run (sfAfter cte p r index depth nOff off count mask nc0) σ =
      ExceptT.run (subframeNode nc0 index depth >>= sfTail cte p r depth nOff off count mask) σ := by
  unfold sfAfter; rw [runE_bind_ok (runE_whenE_false h1 _ σ), runE_bind_ok (runE_whenE_false h2 _ σ)]

theorem subframeNode_zero {β : Type} (f : Cap → SEMonad Unit β) :
    ExceptT.run (subframeNode nc0 index 0 >>= f) σ = ExceptT.run (f nc0) σ := by
  unfold subframeNode; rw [if_pos rfl]; exact runE_ret_bind _ _ _

theorem subframeNode_err {β : Type} (f : Cap → SEMonad Unit β) (hd : depth ≠ 0) {e : SyscallError}
    (h : (lookupTargetSlot (Z := Unit) nc0 (toBl index) (unat depth)).run σ = ({(.error e, σ)}, False)) :
    ExceptT.run (subframeNode nc0 index depth >>= f) σ = ({(.error e, σ)}, False) := by
  unfold subframeNode; rw [if_neg hd, sf_rbind_assoc]; exact runE_bind_err h

theorem subframeNode_ok {β : Type} (f : Cap → SEMonad Unit β) (hd : depth ≠ 0) {sl : CslotPtr} {c : Cap}
    (h : (lookupTargetSlot (Z := Unit) nc0 (toBl index) (unat depth)).run σ = ({(.ok sl, σ)}, False))
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) :
    ExceptT.run (subframeNode nc0 index depth >>= f) σ = ExceptT.run (f c) σ := by
  unfold subframeNode; rw [if_neg hd, sf_rbind_assoc, runE_bind_ok h, runE_bind_ok (runE_liftE hg)]

theorem sfTail_notcn (h : ∀ q b g, nc0 ≠ .cnodeCap q b g) :
    ExceptT.run (sfTail cte p r depth nOff off count mask nc0) σ =
      ({(.error (.failedLookup false (.missingCapability (unat depth))), σ)}, False) := by
  unfold sfTail; split
  · rename_i q b g; exact absurd rfl (h q b g)
  · rfl

theorem sfTail_r0 {q : ObjRef} {b : Nat} {g : List Bool} (h : 2 ^ b - 1 < unat nOff) :
    ExceptT.run (sfTail cte p r depth nOff off count mask (.cnodeCap q b g)) σ =
      ({(.error (.rangeError 0 (BitVec.ofNat 64 (2 ^ b - 1))), σ)}, False) := by
  unfold sfTail; dsimp only; rw [runE_bind_err (by rw [runE_whenE_true h]; rfl)]

theorem sfTail_r1 {q : ObjRef} {b : Nat} {g : List Bool} (h0 : ¬ 2 ^ b - 1 < unat nOff)
    (h : 2 ^ b - unat nOff < unat count) :
    ExceptT.run (sfTail cte p r depth nOff off count mask (.cnodeCap q b g)) σ =
      ({(.error (.rangeError 1 (BitVec.ofNat 64 (2 ^ b - unat nOff))), σ)}, False) := by
  unfold sfTail; dsimp only
  rw [runE_bind_ok (runE_whenE_false h0 _ σ), runE_bind_err (by rw [runE_whenE_true h]; rfl)]

theorem sfTail_go {q : ObjRef} {b : Nat} {g : List Bool} (h0 : ¬ 2 ^ b - 1 < unat nOff)
    (h1 : ¬ 2 ^ b - unat nOff < unat count) :
    ExceptT.run (sfTail cte p r depth nOff off count mask (.cnodeCap q b g)) σ =
      ExceptT.run (do
        NonDetE.mapMEx ensureEmpty ((List.range' (unat nOff) (unat count)).map fun i => (q, natToCref b i))
        NonDetE.returnOk (⟨cte, p + off, maskVmRights r (dataToRights mask),
          (List.range' (unat nOff) (unat count)).map fun i => (q, natToCref b i)⟩ : Fl4SubframeInvocation)) σ := by
  unfold sfTail; dsimp only
  rw [runE_bind_ok (runE_whenE_false h0 _ σ), runE_bind_ok (runE_whenE_false h1 _ σ)]

end

end Spec2


/-- An address of a canonical, 2 MiB-aligned window is canonical. -/
theorem canonical_window {p q : U64} (hc : Canonical p) (hal : p.val % 2 ^ 21 = 0) (h1 : p.val ≤ q.val)
    (h2 : q.val < p.val + 2 ^ 21) : Canonical q := by
  have hd : q.bv.toNat / 2 ^ 21 = p.bv.toNat / 2 ^ 21 := by
    show q.val / 2 ^ 21 = p.val / 2 ^ 21; omega
  have key : ∀ j (hj : j < 64), 21 ≤ j → q.bv[j] = p.bv[j] := by
    intro j hj h21
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat]
    have e1 := Nat.testBit_div_two_pow (x := q.bv.toNat) (n := 21) (i := j - 21)
    have e2 := Nat.testBit_div_two_pow (x := p.bv.toNat) (n := 21) (i := j - 21)
    rw [show j - 21 + 21 = j by omega] at e1 e2
    rw [← e1, ← e2, hd]
  rcases hc with h | h
  · left; intro j hj h47; rw [key j hj (by omega)]; exact h j hj h47
  · right; intro j hj h47; rw [key j hj (by omega)]; exact h j hj h47

section Step
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **One alias insert** (see the module docstring). -/
theorem sub_step {A : Type} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {mm : Bool} {rv : Bool} (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hVP : VsPlaced P (L.ksb s))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hS : SubRel st th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr .Large rt false mm false fa fv) rv s a σ G)
    (hal : ptr.val % 2 ^ 21 = 0)
    {dp : U64} {r : Nat} (hdp : th dp = some (.cnode r)) (hr : r < 64) {k : Nat} (hk : k < 2 ^ r)
    (hdst : capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 k)) = ok .Null)
    {q vm : U64} (hq1 : ptr.val ≤ q.val) (hq2 : q.val + 4096 ≤ ptr.val + 2 ^ 21) (hvm : 1 ≤ vm.val ∧ vm.val ≤ 3)
    (hqal : q.val % 4096 = 0) :
    cdt.insert st s (.Frame q .Small vm false false false 0#u64 0#u64) (cslotAddr (pp.bv, idx))
      (slotAddr dp.bv (BitVec.ofNat 64 k)) ⦃ s' => ∃ σ',
        Fl4Spec.capInsert (Z := Unit) (absCap (.Frame q .Small vm false false false 0#u64 0#u64)) (pp.bv, idx)
          (dp.bv, Fl4Spec.natToCref r k) σ = ({((), σ')}, False) ∧
        SubRel st th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr .Large rt false mm false fa fv) rv s' a σ'
          (insG G (cslotAddr (pp.bv, idx)) (slotAddr dp.bv (BitVec.ofNat 64 k)) rv) ∧
        L.ksb s' = L.ksb s ∧
        MdbStep (L.mem s) G (L.mem s') (insG G (cslotAddr (pp.bv, idx)) (slotAddr dp.bv (BitVec.ofNat 64 k)) rv) ∧
        ∀ y, IsSlot th y → y ≠ slotAddr dp.bv (BitVec.ofNat 64 k) → capAt (L.mem s') y = capAt (L.mem s) y ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI, hU, hvs, hpt, hsr, hcap, hrev, hno, hFI, hfr, hFR, hVC⟩ := hS
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  set dest := slotAddr dp.bv (BitVec.ofNat 64 k) with hdestdef
  set c : capability.Cap := .Frame q .Small vm false false false 0#u64 0#u64 with hcdef
  set srcC : capability.Cap := .Frame ptr .Large rt false mm false fa fv with hsrcCdef
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th src := hAs.isSlot
  have hd : IsSlot th dest := ⟨dp, k, Or.inl ⟨r, hdp, hk⟩, rfl⟩
  have hdest' : cslotAddr (dp.bv, Fl4Spec.natToCref r k) = dest := cslotAddr_natToCref dp.bv r k (by omega) hk
  have hlen : (Fl4Spec.natToCref r k).length = r := natToCref_length r k (by omega)
  have hsd : src ≠ dest := by
    intro e; rw [e, hdst] at hcap; have := eq_of_ok_eq hcap; rw [hsrcCdef] at this; cases this
  have hes : EncWf srcC := by rw [capAt_words] at hcap; exact decode_encWf hcap
  have hfit : ptr.val + 2 ^ 21 ≤ 2 ^ 64 := by have : ptr.val < 2 ^ 64 := ptr.hBounds; omega
  have hcp : Canonical ptr := by have h := hes; rw [hsrcCdef] at h; exact h.1
  have he : EncWf c := ⟨canonical_window hcp hal hq1 (by omega), by omega, by decide, by decide⟩
  have hwf : CapWf c := ⟨hvm.1, hvm.2⟩
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hdestm : dest ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members dest).1 h
    rw [hdst] at h0; exact hn (eq_of_ok_eq h0).symm
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨((hM.members _).1 h1).1, fun e => hdestm (e ▸ h1), h2⟩
  have hnx' : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx' with h | h
    · rw [h]; exact canonical_zero
    · exact h.canonical hPl
  -- the spec's caps and the insert
  obtain ⟨cS, aS, hcS, hcaS, hgs⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
  rw [hcap] at hcS; cases eq_of_ok_eq hcS
  obtain ⟨cD, aD, hcD, hcaD, hgd⟩ := hR.slot_cap (sl := (dp.bv, Fl4Spec.natToCref r k)) (p := dp) rfl
    (by rw [hlen]; exact hdp)
  rw [hdest', hdst] at hcD; cases eq_of_ok_eq hcD
  rw [hcaS.abs] at hgs; rw [hcaD.abs] at hgd
  obtain ⟨csd, hkd, hwfd, -⟩ := hR.cnode dp r hdp
  set A := absCap c with hAdef
  have hsetd := setCap_cnode (Z := Unit) A hkd hwfd hlen
  have hci := capInsert_eq hgs hgd (setUntyped_skip (by simp [Fl4Spec.isUntypedCap, hAdef, absCap])) hsetd rfl rfl
  have hbs : baseF srcC = ptr.val := (frame_range ptr .Large rt false mm fa fv false).1
  have hov : ∀ w ∈ G.chains.flatten, Ovl (absCap c) (absCap (capV (L.mem s) w)) →
      isFrame (capV (L.mem s) w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch :=
    fun w hw h => hfr w hw q vm (by rw [hbs]; exact hq1) (by rw [hbs]; omega) h
  refine WP.spec_mono (WP.spec_and (insert_frame_fin (L := L) hPl s σ _ G hM hFI hsrcm hd hdestm hcap rfl c he rfl hov
      A (pp.bv, idx) (dp.bv, Fl4Spec.natToCref r k) _ (by rw [hci]; exact Set.mem_singleton _) rfl)
    (WP.spec_and (insert_mem (L := L) hPl s c src dest hs hd hsd srcC hcap hnx)
    (WP.spec_and (insert_frame2 (L := L) hPl s c src dest hs hd srcC hcap hnx')
      (by
        have h := insert_refines' (L := L) th s σ G hR hV hPl hM hC hpp hdp hidx hlen hcap (by simp)
          (by rw [hdest']; exact hdst) c A ⟨hwf, rfl⟩ (by rw [hcdef]; show q.val % 2 ^ 12 = 0; simpa using hqal) he (by simp) trivial
        rw [hdest'] at h; exact h)))) ?_
  rintro s' ⟨hFin, hW, hF, hins⟩
  have hnd : ∀ y, ¬ Mdb.Desc G.par y src → True := fun _ _ => trivial
  have hio : σ.isOriginalCap (pp.bv, idx) = rv := by rw [hC.orig (pp.bv, idx) hAs, hrev]
  have hsr' : Fl4Spec.sameRegionAs (absCap srcC) A := by
    simp only [hsrcCdef, hAdef, hcdef, absCap, Bool.false_eq_true, ↓reduceIte]
    exact sameRegion_alias (by show ptr.val ≤ q.val; exact hq1) (by show q.val + 4096 ≤ ptr.val + 2 ^ 21; exact hq2)
      hfit _ _ _ _
  obtain ⟨σ', G'', hci', hR', hV', hM', hC', hG''⟩ := hins (fun hn y hy => by
    cases hrv : rv
    · obtain ⟨z, hz⟩ := desc_tail_child hy
      have := hI.orig z src hz
      rw [hrev, hrv] at this; cases this
    · exact absurd (by rw [hio, hrv]; exact ⟨rfl, hsr', trivial⟩) hn)
  have hb : decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (pp.bv, idx)) A
      (decide (Fl4Spec.isCapRevocable A (absCap srcC)))) = rv := by
    rw [hio]
    cases rv
    · simp [Fl4Spec.shouldBeParentOf]
    · exact decide_eq_true ⟨rfl, hsr', trivial⟩
  rw [hb] at hG''
  subst hG''
  have e1 : σ' = capInsertState σ (setCnodeSlot σ dp.bv r csd (Fl4Spec.natToCref r k) A) A (absCap srcC)
      (pp.bv, idx) (dp.bv, Fl4Spec.natToCref r k) := by
    rw [hci] at hci'
    have := congrArg Prod.fst hci'
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  -- the alias's range
  have hsF : isFrame (capV (L.mem s) src) = true := by rw [capV_of_capAt hcap]; rfl
  obtain ⟨bs, ts⟩ := frame_range ptr .Large rt false mm fa fv false
  obtain ⟨bc, tc⟩ := frame_range q .Small vm false false 0#u64 0#u64 false
  have hmL : (maskF (fbitsF .Large)).val = 2 ^ 21 - 1 := by
    rw [maskF_val (by rw [fbitsF_val]; decide), fbitsF_val]; rfl
  have hmS : (maskF (fbitsF .Small)).val = 2 ^ 12 - 1 := by
    rw [maskF_val (by rw [fbitsF_val]; decide), fbitsF_val]; rfl
  have tsv : topF srcC = ptr.val + 2 ^ 21 - 1 := by
    rw [ts]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmL]
    omega
  have tcv : topF c = q.val + 4095 := by
    rw [tc]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmS]
    omega
  have hcr : baseF c ≤ topF c := by rw [bc, tcv]; omega
  have hcin : Within c (capV (L.mem s) src) := by
    rw [capV_of_capAt hcap]; unfold Within; rw [bs, bc, tsv, tcv]; omega
  -- the MDB invariants
  have hctx : InsFCtx th (L.mem s) (L.mem s') G src dest c :=
    { hM := hM, hI := hI, hsrc := hsrcm, hd := hd, hdest := hdestm
      hnext := fun y hy => hW.nextOf' hPl hy hd hsd hNc
      hcap := fun y hy => by
        have h := hW.capAt' hy he hes hcap
        rw [capAt_capV] at h
        by_cases h1 : y = dest
        · rw [if_pos h1] at h ⊢; exact eq_of_ok_eq h
        · rw [if_neg h1] at h ⊢
          by_cases h2 : y = src
          · rw [if_pos h2] at h; subst h2; rw [capV_of_capAt hcap]; exact eq_of_ok_eq h
          · rw [if_neg h2, capAt_capV] at h; exact eq_of_ok_eq h
      hrev := fun y hy => by rw [hW.revOf' hy hsd]; rfl
      hfb := fun y hy => by rw [InsWords.fbOf' hW hy hsd]; rfl
      hsF := hsF, hcF := rfl, hcr := hcr, hcin := hcin
      hno := fun x hx => by rw [capV_of_capAt hcap]; exact hno x hx }
  have hrv' : revOf (L.mem s) src = rv := hrev
  have hI' : MdbInv (L.mem s') (insG G src dest rv) := by rw [← hrv']; exact hctx.inv
  have hU' : UtInv (L.mem s') (insG G src dest rv) :=
    utinv_alias hM hI hU rv hsrcm hsF hdestm rfl hcin hcr hctx.cd (fun y hy => hctx.cz hy)
  -- the other relations
  have hslotw : ∀ b, OutsideObjects th b → ¬ SlotWord th b := by
    rintro b hb ⟨x, kk, hx, hkk, rfl⟩
    obtain ⟨o, ko, hko, h1, h2, -⟩ := slot_in_object hPl hx
    have := hkk.lt
    have hf := hx.fit hPl
    have hv := wordOf_val (a := x) (k := kk) (by omega)
    exact hb.2 o ko hko ⟨by omega, by omega⟩
  have hmem : ∀ b, OutsideObjects th b → L.mem s' b = L.mem s b := fun b hb => hF.2.2 b hb.1 (hslotw b hb)
  have hkh : ∀ x : Fl4Spec.ObjRef, x ≠ dp.bv → σ'.kheap x = σ.kheap x := by
    intro x hx; rw [e1]; show (Function.update σ.kheap dp.bv _) x = _; rw [Function.update_of_ne hx]
  have hvs' : VsRel P (L.mem s') (L.ksb s') σ' := by
    rw [hF.1]
    refine hvs.frame (fun b hb => hmem b (hVO b hb)) (by rw [e1]; rfl) (fun p hp => hkh _ ?_)
    obtain ⟨f, hf, -⟩ := hvs.pool p hp
    exact kheap_ne hf hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hpt' : PtRel L4 L3 L2 L1 (L.mem s') σ' := by
    refine hpt.frame (fun b hb => hmem b (hPO b hb)) (fun q hq => hkh _ ?_)
    obtain ⟨ao, hao⟩ := hpt.arch hq
    exact kheap_ne hao hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hsr2 : SR s' a σ' := hH.insStable s s' a σ σ' hsr ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb hn⟩
    ⟨dp.bv, r, csd, _, A, _, _, hkd, by rw [e1]; rfl⟩
  have hcap' : capAt (L.mem s') src = ok srcC := by
    rw [hW.capAt' hs he hes hcap, if_neg hsd, if_pos rfl]; rfl
  have hFI' : FinInv th (L.mem s') σ' (insG G src dest rv) := by rw [e1]; exact hFin rv
  have hfr' : ∀ w ∈ (insG G src dest rv).chains.flatten, ∀ q' vm' : U64, baseF srcC ≤ q'.val →
      q'.val < baseF srcC + 2 ^ 21 →
      Ovl (absCap (.Frame q' .Small vm' false false false 0#u64 0#u64)) (absCap (capV (L.mem s') w)) →
      isFrame (capV (L.mem s') w) = true ∧ ∃ ch ∈ (insG G src dest rv).chains, src ∈ ch ∧ w ∈ ch := by
    intro w hw q' vm' h1 h2 hov'
    rcases (mem_flatten_ins hsrcm).1 hw with rfl | hw0
    · obtain ⟨ch, hch, hsc⟩ := List.mem_flatten.1 hsrcm
      refine ⟨by rw [hctx.cd, hcdef]; rfl, Mdb.insAfter src dest ch, List.mem_map.2 ⟨ch, hch, rfl⟩,
        (mem_insAfter hsc).2 (Or.inr hsc), (mem_insAfter hsc).2 (Or.inl rfl)⟩
    · rw [hctx.cz hw0] at hov' ⊢
      obtain ⟨hf, ch, hch, hs1, hw1⟩ := hfr w hw0 q' vm' h1 h2 hov'
      exact ⟨hf, Mdb.insAfter src dest ch, List.mem_map.2 ⟨ch, hch, rfl⟩,
        (mem_insAfter hs1).2 (Or.inr hs1), (mem_insAfter hs1).2 (Or.inr hw1)⟩
  have hFR' : Vs.FrameInv (L.mem s') (insG G src dest rv) :=
    hFR.insert_alias hsrcm hdestm rv (capV_of_capAt hcap) hctx.cd (hctx.cz hsrcm) (fun z hz _ => hctx.cz hz)
      hq1 (by omega) (Vs.large_aligned hV hM)
  have hVC' : VsCapsIn P L4 L3 L2 L1 (L.mem s') (insG G src dest rv) :=
    hVC.insert_copy hsrcm rv (by rw [hctx.cd]; exact vcap_alias (hVC.at hM hs hcap (by simp)) hq1 hq2 hqal)
      (fun h => by rw [hctx.cz hsrcm]; exact h) (fun z hz _ _ => hctx.cz hz)
  have hMS : MdbStep (L.mem s) G (L.mem s') (insG G src dest rv) :=
    MdbStep.frameAlias hM hI rv hsrcm hdestm (capV_of_capAt hcap) hctx.cd hq1 (by omega)
      (by rw [hctx.cd]; exact hcin) (by rw [hctx.cd]; exact hcr) (Vs.large_aligned hV hM)
      (fun z hz => hctx.cz hz) hctx.rd (fun z hz => hctx.rz hz) hq2 hqal
  refine ⟨σ', hci', ⟨hR', hV', hM', hC', hI', hU', hvs', hpt', hsr2, hcap', by rw [hctx.rz hsrcm]; exact hrev,
    fun x hx => ?_, hFI', hfr', hFR', hVC'⟩, hF.1, hMS, fun y hy hyd => ?_⟩
  · rcases (hctx.memI x).1 (by rw [← hrv'] at hx; exact hx) with rfl | hx
    · right; left; rw [hctx.cd, hctx.rd]; exact ⟨rfl, rfl⟩
    · rw [hctx.cz hx, hctx.rz hx]; exact hno x hx
  · rw [hW.capAt' hy he hes hcap, if_neg hyd]
    by_cases h2 : y = src
    · rw [if_pos h2, h2, hcap]; rfl
    · rw [if_neg h2]


/-- The spec's insert of alias `d.1` into slot `d.2`. -/
def subIns (src : Fl4Spec.CslotPtr) (base : Fl4Spec.ObjRef) (R : Fl4Spec.VMRights) (d : Nat × Fl4Spec.CslotPtr) :
    Fl4Spec.SMonad Unit Unit :=
  Fl4Spec.capInsert (.archObjectCap (.pageCap false (base + BitVec.ofNat 64 (d.1 * 4096)) R .vmNoMap
    .x64SmallPage none)) src d.2

/-- The spec's list of inserts. -/
def subList (dp : U64) (r first count : Nat) : List (Nat × Fl4Spec.CslotPtr) :=
  (List.range count).zip ((List.range' first count).map fun j => (dp.bv, Fl4Spec.natToCref r j))

theorem subList_drop (dp : U64) (r first count i : Nat) (hi : i < count) :
    (subList dp r first count).drop i = (i, (dp.bv, Fl4Spec.natToCref r (first + i))) ::
      (subList dp r first count).drop (i + 1) := by
  have hl : i < (subList dp r first count).length := by simp [subList]; omega
  rw [List.drop_eq_getElem_cons hl]
  congr 1
  simp [subList, List.getElem_zip, List.getElem_range, List.getElem_range']

theorem subList_drop_all (dp : U64) (r first count : Nat) : (subList dp r first count).drop count = [] := by
  apply List.drop_of_length_le; simp [subList]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **The alias loop** (`insert_subframes`) against the spec's inserts. -/
theorem insert_subframes_rel {A : Type} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {mm : Bool} {rv : Bool} (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hVP : VsPlaced P (L.ksb s))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hS : SubRel st th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr .Large rt false mm false fa fv) rv s a σ G)
    (hal : ptr.val % 2 ^ 21 = 0)
    {dp : U64} {r : Nat} (hdp : th dp = some (.cnode r)) (hr : r < 64) {first count base vm : U64}
    (hfc : first.val + count.val ≤ 2 ^ r) (hb1 : ptr.val ≤ base.val) (hb2 : base.val + count.val * 4096 ≤ ptr.val + 2 ^ 21)
    (hvm : 1 ≤ vm.val ∧ vm.val ≤ 3) (hbal : base.val % 4096 = 0)
    (hempty : ∀ j : Nat, first.val ≤ j → j < first.val + count.val →
      capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok .Null) :
    vspace.insert_subframes st s (cslotAddr (pp.bv, idx)) dp first base count vm ⦃ s' => ∃ σ' G',
      Fl4Spec.NonDet.mapMx (subIns (pp.bv, idx) base.bv (vmRightsOf vm)) (subList dp r first.val count.val) σ =
        ({((), σ')}, False) ∧
      SubRel st th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr .Large rt false mm false fa fv) rv s' a σ' G' ∧
      L.ksb s' = L.ksb s ∧ MdbStep (L.mem s) G (L.mem s') G' ⦄ := by
  have hfit : ptr.val + 2 ^ 21 ≤ 2 ^ 64 := by have : ptr.val < 2 ^ 64 := ptr.hBounds; omega
  set Lst := subList dp r first.val count.val with hLst
  set g := subIns (pp.bv, idx) base.bv (vmRightsOf vm) with hg
  unfold vspace.insert_subframes vspace.insert_subframes_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => count.val - x.2.val)
    (inv := fun x : S × U64 => x.2.val ≤ count.val ∧ ∃ σi Gi,
      SubRel st th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr .Large rt false mm false fa fv) rv x.1 a σi Gi ∧
      MdbStep (L.mem s) G (L.mem x.1) Gi ∧ L.ksb x.1 = L.ksb s ∧
      (∀ j : Nat, first.val + x.2.val ≤ j → j < first.val + count.val →
        capAt (L.mem x.1) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok .Null) ∧
      ∀ σf, Fl4Spec.NonDet.mapMx g (Lst.drop x.2.val) σi = ({((), σf)}, False) →
        Fl4Spec.NonDet.mapMx g Lst σ = ({((), σf)}, False))
  · rintro ⟨si, i⟩ ⟨hic, σi, Gi, hSi, hMSi, hksi, hemp, hcont⟩
    unfold vspace.insert_subframes_loop.body
    simp only at hic hksi hemp hcont ⊢
    by_cases hlt : i < count
    · have hlt' : i.val < count.val := hlt
      rw [if_pos hlt]
      step as ⟨i1, hi1⟩
      simp only [lift, bind_ok]
      rw [show obj.Slot.index dp (core.num.U64.wrapping_add first i) =
        ok (slotAddr dp.bv (core.num.U64.wrapping_add first i).bv) from spec_eq_ok (slot_index_spec _ _)]
      simp only [bind_ok]
      have hk2 : first.val + i.val < 2 ^ r := by omega
      have hfiv : (core.num.U64.wrapping_add first i).bv = BitVec.ofNat 64 (first.val + i.val) := by
        apply BitVec.eq_of_toNat_eq
        have : 2 ^ r < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        try (rw [Nat.mod_eq_of_lt (by omega)])
      have hi1v : i1.val = i.val * 4096 := by
        rw [hi1]; simp [Nat.shiftLeft_eq, U64.size_def, U64.numBits]
        try (rw [Nat.mod_eq_of_lt (by omega)])
        try omega
      have hqv : (core.num.U64.wrapping_add base i1).val = base.val + i.val * 4096 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hi1v]; omega
      rw [hfiv]
      refine WP.spec_bind (sub_step (L := L) hH hPl hPP hpp hidx si a σi Gi (by rw [hksi]; exact hVP)
        (by rw [hksi]; exact hVO) hPO hSi hal hdp hr hk2 (hemp _ (by omega) (by omega))
        (q := core.num.U64.wrapping_add base i1) (by rw [hqv]; omega) (by
          rw [hqv]; have := Nat.mul_le_mul_right 4096 (show i.val + 1 ≤ count.val by omega)
          rw [Nat.add_mul] at this; omega) hvm (by rw [hqv]; omega)) ?_
      rintro s2 ⟨σ2, hci, hS2, hks2, hMS2, hoth⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = i.val + 1 := by simpa using hi4
      refine ⟨by omega, ⟨σ2, _, hS2, hMSi.trans hMS2, hks2.trans hksi, fun j h1 h2 => ?_, fun σf hf => hcont σf ?_⟩, by omega⟩
      · have hne : slotAddr dp.bv (BitVec.ofNat 64 j) ≠ slotAddr dp.bv (BitVec.ofNat 64 (first.val + i.val)) := by
          intro e
          have hj : IsSlotAt th dp j := Or.inl ⟨r, hdp, by omega⟩
          have hk' : IsSlotAt th dp (first.val + i.val) := Or.inl ⟨r, hdp, hk2⟩
          rcases hj.apart hPl hk' (fun ⟨_, h3⟩ => by omega) with h | h <;>
            (change slotOf dp j = slotOf dp (first.val + i.val) at e; rw [e] at h; omega)
        rw [hoth _ ⟨dp, j, Or.inl ⟨r, hdp, by omega⟩, rfl⟩ hne]
        exact hemp j (by omega) h2
      · rw [subList_drop dp r first.val count.val i.val hlt']
        rw [hi4v] at hf
        have hgi : g (i.val, (dp.bv, Fl4Spec.natToCref r (first.val + i.val))) σi = ({((), σ2)}, False) := by
          rw [hg]; unfold subIns
          have e : (base.bv + BitVec.ofNat 64 (i.val * 4096)) = (core.num.U64.wrapping_add base i1).bv := by
            apply BitVec.eq_of_toNat_eq
            rw [show (core.num.U64.wrapping_add base i1).bv.toNat = (core.num.U64.wrapping_add base i1).val from rfl, hqv]
            simp [BitVec.toNat_add]; omega
          rw [e]; exact hci
        rw [mapMx_cons_one hgi]; exact hf
    · rw [if_neg hlt]
      have hic' : i.val = count.val := by
        have : ¬ i.val < count.val := hlt
        omega
      refine (WP.spec_ok _).2 ⟨σi, Gi, hcont σi ?_, hSi, hksi, hMSi⟩
      rw [hic', subList_drop_all]; rfl
  · exact ⟨by simp, σ, G, hS, MdbStep.refl hS.M, rfl, fun j h1 h2 => hempty j (by simpa using h1) h2, fun σf hf => by simpa using hf⟩




theorem wsub_val {n m : U64} (h : m.val ≤ n.val) : (core.num.U64.wrapping_sub n m).val = n.val - m.val := by
  rw [core.num.U64.wrapping_sub_val_eq]
  have hb : n.val < 2 ^ 64 := n.hBounds
  have hm : m.val < 2 ^ 64 := m.hBounds
  have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size, U64.numBits]
  rw [hs, show n.val + (2 ^ 64 - m.val) = (n.val - m.val) + 2 ^ 64 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem ofNat_bv {n : Nat} {x : U64} (h : x.val = n) : BitVec.ofNat 64 n = x.bv := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, show x.bv.toNat = x.val from rfl, h]
  exact Nat.mod_eq_of_lt (by rw [← h]; exact x.hBounds)


/-- The post of the node part of the decode, against the spec's outcome `E`. -/
def SfPost (th : TypedHeap) (σ : Fl4Spec.State Unit)
    (E : Set (Except Fl4Spec.SyscallError Fl4Spec.Fl4SubframeInvocation × Fl4Spec.State Unit) × Prop)
    (cte : Fl4Spec.CslotPtr) (p : Fl4Spec.ObjRef) (r : Fl4Spec.VMRights) (a2 a3 a4 a5 : U64) :
    core.result.Result U64 error.Exc → Prop
  | .Err e => ∃ e', SysErrRel e e' ∧ E = ({(.error e', σ)}, False)
  | .Ok dest => ∃ rr : Nat, th dest = some (.cnode rr) ∧ rr < 64 ∧ a2.val + a4.val ≤ 2 ^ rr ∧
      E = ExceptT.run (do
          Fl4Spec.NonDetE.mapMEx Fl4Spec.ensureEmpty
            ((List.range' a2.val a4.val).map fun i => (dest.bv, Fl4Spec.natToCref rr i))
          Fl4Spec.NonDetE.returnOk (⟨cte, p + a3.bv, Fl4Spec.maskVmRights r (Fl4Spec.dataToRights a5.bv),
            (List.range' a2.val a4.val).map fun i => (dest.bv, Fl4Spec.natToCref rr i)⟩ :
              Fl4Spec.Fl4SubframeInvocation)) σ

set_option maxHeartbeats 4000000 in
/-- **The node part of the decode** (`subframe_dest`) against `subframeNode`
and `sfTail`. -/
theorem subframe_dest_rel {th : TypedHeap} (s : S) (σ : Fl4Spec.State Unit) (hSt : StateRel th (L.mem s) σ)
    (hSV : SlotsValid th (L.mem s)) {y : U64} {nc : capability.Cap} {nc' : Fl4Spec.Cap}
    (hcy : capAt (L.mem s) y = ok nc) (hnr : CapRel nc nc') (hnv : CapValid th nc)
    (cte : Fl4Spec.CslotPtr) (p : Fl4Spec.ObjRef) (r : Fl4Spec.VMRights) (a0 a1 a2 a3 a4 a5 : U64) :
    vspace.subframe_dest st s y a0 a1 a2 a4 ⦃ res => SfPost th σ
      (ExceptT.run (Fl4Spec.subframeNode nc' a0.bv a1.bv >>= sfTail cte p r a1.bv a2.bv a3.bv a4.bv a5.bv) σ)
      cte p r a2 a3 a4 a5 res ⦄ := by
  generalize hE : ExceptT.run (Fl4Spec.subframeNode nc' a0.bv a1.bv >>=
    sfTail cte p r a1.bv a2.bv a3.bv a4.bv a5.bv) σ = E
  unfold vspace.subframe_dest
  rw [slot_cap_eq, hcy]; simp only [bind_ok]
  by_cases hd : a1 = 0#u64
  · subst hd
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [show U64.bv 0#u64 = (0 : BitVec 64) from rfl, subframeNode_zero] at hE
    obtain ⟨HWF, rfl⟩ := hnr
    have HNV := hnv
    clear hcy hnv

    cases nc
    case CNode q rad gs g =>
      obtain ⟨hr64, -, -⟩ := HWF
      obtain ⟨hth, -⟩ := HNV
      simp only [vspace.cnode_of, bind_ok, lift, uncurry_apply_pair]
      obtain ⟨z, hz, hzv⟩ := shl_radix hr64
      rw [hz]; simp only [bind_ok]
      have hpos : 1 ≤ 2 ^ rad.val := Nat.one_le_two_pow
      have hlt : 2 ^ rad.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
      have hz1 : (core.num.U64.wrapping_sub z 1#u64).val = 2 ^ rad.val - 1 := by
        rw [wsub_val (by rw [hzv]; exact hpos), hzv]; rfl
      by_cases h0 : a2 > core.num.U64.wrapping_sub z 1#u64
      · rw [if_pos h0]
        simp only [error.range, bind_ok, WP.spec_ok]
        have h0' : 2 ^ rad.val - 1 < a2.val := by rw [← hz1]; exact h0
        exact ⟨.rangeError 0 (BitVec.ofNat 64 (2 ^ rad.val - 1)), ⟨rfl, ofNat_bv hz1⟩, by rw [← hE]; exact sfTail_r0 h0'⟩
      rw [if_neg h0]
      have h0' : ¬ 2 ^ rad.val - 1 < a2.val := by rw [← hz1]; exact h0
      have hz2 : (core.num.U64.wrapping_sub z a2).val = 2 ^ rad.val - a2.val := by
        rw [wsub_val (by rw [hzv]; omega), hzv]
      by_cases h1 : a4 > core.num.U64.wrapping_sub z a2
      · rw [if_pos h1]
        simp only [error.range, bind_ok, WP.spec_ok]
        have h1' : 2 ^ rad.val - a2.val < a4.val := by rw [← hz2]; exact h1
        exact ⟨.rangeError 1 (BitVec.ofNat 64 (2 ^ rad.val - a2.val)), ⟨rfl, ofNat_bv hz2⟩, by rw [← hE]; exact sfTail_r1 h0' h1'⟩
      rw [if_neg h1]
      have h1' : ¬ 2 ^ rad.val - a2.val < a4.val := by rw [← hz2]; exact h1
      simp only [WP.spec_ok]
      exact ⟨rad.val, hth, hr64, by omega, by rw [← hE]; exact sfTail_go h0' h1'⟩
    all_goals
      simp only [vspace.cnode_of, bind_ok, vspace.failed_lookup, WP.spec_ok]
      exact ⟨.failedLookup false (.missingCapability (0#u64 : U64).val), ⟨rfl, rfl⟩,
        by rw [← hE, sfTail_notcn (fun _ _ _ h => by simp [absCap] at h)]; rfl⟩
  have hd' : (a1 != 0#u64) = true := by simpa using hd
  have hdb : a1.bv ≠ 0 := fun h => hd (UScalar.eq_of_val_eq (by
    have := congrArg BitVec.toNat h; simpa using this))
  simp only [hd', ↓reduceIte]
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hSt hSV false nc nc' hnr hnv a0 a1)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) nc' (Fl4Spec.toBl a0.bv) (Fl4Spec.unat a1.bv)).run σ =
      ({(e1, σ)}, False) := he1
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      rw [subframeNode_err _ hdb hlt] at hE; exact ⟨e', hrel1, hE.symm⟩
  | Ok val =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd⟩ := hrel1
      obtain ⟨c2, a2', hc2, hca2, hg2⟩ := hSt.slot_cap (Z := Unit) hpd1 hpd
      have HNV : CapValid th c2 := hSV.abs ⟨pd, hpd1, Or.inl hpd⟩ hc2
      simp only [bind_ok]
      rw [slot_cap_eq, hc2]; simp only [bind_ok]
      rw [subframeNode_ok _ hdb hlt hg2] at hE
      obtain ⟨HWF, rfl⟩ := hca2
      clear hc2 hg2

      cases c2
      case CNode q rad gs g =>
        obtain ⟨hr64, -, -⟩ := HWF
        obtain ⟨hth, -⟩ := HNV
        simp only [vspace.cnode_of, bind_ok, lift, uncurry_apply_pair]
        obtain ⟨z, hz, hzv⟩ := shl_radix hr64
        rw [hz]; simp only [bind_ok]
        have hpos : 1 ≤ 2 ^ rad.val := Nat.one_le_two_pow
        have hlt : 2 ^ rad.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
        have hz1 : (core.num.U64.wrapping_sub z 1#u64).val = 2 ^ rad.val - 1 := by
          rw [wsub_val (by rw [hzv]; exact hpos), hzv]; rfl
        by_cases h0 : a2 > core.num.U64.wrapping_sub z 1#u64
        · rw [if_pos h0]
          simp only [error.range, bind_ok, WP.spec_ok]
          have h0' : 2 ^ rad.val - 1 < a2.val := by rw [← hz1]; exact h0
          exact ⟨.rangeError 0 (BitVec.ofNat 64 (2 ^ rad.val - 1)), ⟨rfl, ofNat_bv hz1⟩, by rw [← hE]; exact sfTail_r0 h0'⟩
        rw [if_neg h0]
        have h0' : ¬ 2 ^ rad.val - 1 < a2.val := by rw [← hz1]; exact h0
        have hz2 : (core.num.U64.wrapping_sub z a2).val = 2 ^ rad.val - a2.val := by
          rw [wsub_val (by rw [hzv]; omega), hzv]
        by_cases h1 : a4 > core.num.U64.wrapping_sub z a2
        · rw [if_pos h1]
          simp only [error.range, bind_ok, WP.spec_ok]
          have h1' : 2 ^ rad.val - a2.val < a4.val := by rw [← hz2]; exact h1
          exact ⟨.rangeError 1 (BitVec.ofNat 64 (2 ^ rad.val - a2.val)), ⟨rfl, ofNat_bv hz2⟩, by rw [← hE]; exact sfTail_r1 h0' h1'⟩
        rw [if_neg h1]
        have h1' : ¬ 2 ^ rad.val - a2.val < a4.val := by rw [← hz2]; exact h1
        simp only [WP.spec_ok]
        exact ⟨rad.val, hth, hr64, by omega, by rw [← hE]; exact sfTail_go h0' h1'⟩
      all_goals
        simp only [vspace.cnode_of, bind_ok, vspace.failed_lookup, WP.spec_ok]
        exact ⟨.failedLookup false (.missingCapability a1.val), ⟨rfl, rfl⟩,
          by rw [← hE, sfTail_notcn (fun _ _ _ h => by simp [absCap] at h)]; rfl⟩

/-- The spec's emptiness check of the run, against FL4's slots. -/
theorem sfDests_run {th : TypedHeap} (s : S) (σ : Fl4Spec.State Unit) (hR : StateRel th (L.mem s) σ)
    {dp : U64} {r : Nat} (hdp : th dp = some (.cnode r)) (hr : r < 64) (first count : Nat)
    (hfc : first + count ≤ 2 ^ r) :
    (Fl4Spec.NonDetE.mapMEx (Fl4Spec.ensureEmpty (Z := Unit))
      ((List.range' first count).map fun i => (dp.bv, Fl4Spec.natToCref r i))).run σ =
      ({(if ∀ j : Nat, first ≤ j → j < first + count →
          capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok .Null
        then .ok () else .error .deleteFirst, σ)}, False) := by
  let caps : Fl4Spec.CslotPtr → Fl4Spec.Cap := fun sl =>
    if h : ∃ a, Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False) then h.choose else .nullCap
  have hj : ∀ j, j < 2 ^ r → ∃ c, capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok c ∧
      CapRel c (caps (dp.bv, Fl4Spec.natToCref r j)) ∧
      Fl4Spec.getCap (Z := Unit) (dp.bv, Fl4Spec.natToCref r j) σ =
        ({(caps (dp.bv, Fl4Spec.natToCref r j), σ)}, False) := by
    intro j hjr
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (dp.bv, Fl4Spec.natToCref r j)) (p := dp) rfl
      (by rw [natToCref_length r j (by omega)]; exact hdp)
    have hex : ∃ a, Fl4Spec.getCap (Z := Unit) (dp.bv, Fl4Spec.natToCref r j) σ = ({(a, σ)}, False) := ⟨a, hg⟩
    have hca' : caps (dp.bv, Fl4Spec.natToCref r j) = a := by
      simp only [caps, dif_pos hex]
      have h2 : (({(hex.choose, σ)}, False) : Set _ × Prop) = ({(a, σ)}, False) := hex.choose_spec.symm.trans hg
      have := congrArg Prod.fst h2
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, and_true] at this
      exact this
    rw [cslotAddr_natToCref dp.bv r j (by omega) hjr] at hc
    exact ⟨c, hc, hca' ▸ hca, hca' ▸ hg⟩
  have hiff : (∀ sl ∈ (List.range' first count).map (fun i => (dp.bv, Fl4Spec.natToCref r i)),
      caps sl = .nullCap) ↔ ∀ j : Nat, first ≤ j → j < first + count →
        capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok .Null := by
    simp only [List.mem_map, List.mem_range'_1, forall_exists_index, and_imp]
    constructor
    · intro h j h1 h2
      obtain ⟨c, hc, hca, -⟩ := hj j (by omega)
      have := h _ j h1 h2 rfl
      rw [hc, (hca.null_iff).1 this]
    · rintro h _ i hi1 hi2 rfl
      obtain ⟨c, hc, hca, -⟩ := hj i (by omega)
      rw [h _ hi1 hi2] at hc
      exact (hca.null_iff).2 (eq_of_ok_eq hc).symm
  rw [mapMEx_ensureEmpty_run σ caps _ (fun sl hsl => by
    simp only [List.mem_map, List.mem_range'_1] at hsl
    obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := hsl
    exact (hj j (by omega)).choose_spec.2.2), if_congr hiff rfl rfl]

/-- `ensure_empty_run dest first count`: `Ok` iff the slots are null, else
`DeleteFirst`. -/
theorem ensure_empty_run_eq (s : S) (dest first count : U64) (hfit : first.val + count.val < 2 ^ 64) :
    vspace.ensure_empty_run st s dest first count = ok
      (if ∀ j : Nat, first.val ≤ j → j < first.val + count.val →
          capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 j)) = ok .Null
       then .Ok () else .Err (.Sys .DeleteFirst)) := by
  apply spec_eq_ok
  unfold vspace.ensure_empty_run vspace.ensure_empty_run_loop
  apply loop.spec_decr_nat (measure := fun i : U64 => count.val - i.val)
    (inv := fun i : U64 => i.val ≤ count.val ∧ ∀ j : Nat, first.val ≤ j → j < first.val + i.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 j)) = ok .Null)
  · rintro i ⟨hic, hall⟩
    unfold vspace.ensure_empty_run_loop.body
    by_cases hlt : i < count
    · have hlt' : i.val < count.val := hlt
      rw [if_pos hlt]
      simp only [lift, bind_ok]
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add first i) =
        ok (slotAddr dest.bv (core.num.U64.wrapping_add first i).bv) from spec_eq_ok (slot_index_spec _ _)]
      simp only [bind_ok]
      have hfiv : (core.num.U64.wrapping_add first i).bv = BitVec.ofNat 64 (first.val + i.val) := by
        apply BitVec.eq_of_toNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        try (rw [Nat.mod_eq_of_lt (by omega)])
      rw [hfiv]
      unfold cdt.ensure_empty_slot
      obtain ⟨c, hc⟩ := capAt_total (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 (first.val + i.val)))
      rw [slot_cap_eq, hc]
      simp only [bind_ok, cap_is_null_eq]
      cases hn : isNullB c
      · have hcn : c ≠ .Null := by intro e; subst e; simp [isNullB] at hn
        simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        rw [if_neg]
        intro h
        have := h (first.val + i.val) (by omega) (by omega)
        rw [hc] at this; exact hcn (eq_of_ok_eq this)
      · have hcn : c = .Null := by cases c <;> simp_all [isNullB]
        simp only [↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i.val + 1 := by simpa using hi2
        refine ⟨by omega, fun j h1 h2 => ?_, by omega⟩
        by_cases hj : j = first.val + i.val
        · rw [hj, hc, hcn]
        · exact hall j h1 (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      have : i.val = count.val := by have : ¬ i.val < count.val := hlt; omega
      rw [if_pos (fun j h1 h2 => hall j h1 (by omega))]
  · exact ⟨by simp, fun j h1 h2 => by simp at h2; omega⟩


/-- The post of `DeriveSubframe`'s decode and perform, against the spec's
decode outcome `D`: an error, as the spec's single outcome, the state
unchanged; or the spec's single invocation, performed after the Restart with
no failure, and the loop relations at the result. -/
def SubDecPost {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (src : U64) (srcC : capability.Cap) (rv : Bool) (G0 : MdbGhost) (σ : Fl4Spec.State Unit)
    (D : Set (Except Fl4Spec.SyscallError Fl4Spec.Fl4SubframeInvocation × Fl4Spec.State Unit) × Prop)
    (s : S) (a : A) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e e', res.1 = .Err e ∧ SysErrRel e e' ∧ D = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
  (res.1 = .Ok () ∧ res.2.2 = a ∧ ∃ iv, D = ({(.ok iv, σ)}, False) ∧ ∃ σ' G',
    ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      Fl4Spec.performDeriveSubframe iv) σ).1 ∧
    ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
      Fl4Spec.performDeriveSubframe iv) σ).2 ∧
    SubRel st th P L4 L3 L2 L1 SR src srcC rv res.2.1 a σ' G' ∧ L.ksb res.2.1 = L.ksb s ∧
    MdbStep (L.mem s) G0 (L.mem res.2.1) G')

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`DeriveSubframe` refines the l4h 0029 model** (decode and perform, for
the node cap present as the first extra cap; see the module docstring). -/
theorem derive_subframe_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {sz : capability.FrameSize} {dev mm : Bool}
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Frame ptr sz rt dev mm false fa fv))
    (hno : sz = .Large → dev = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame ptr sz rt dev mm false fa fv) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame ptr sz rt dev mm false fa fv) (capV (L.mem s) x))
    (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ex : Array obj.Slot 3#usize) {y : obj.Slot} (hex0 : vspace.extra ex 0#usize = ok (some y))
    {nc : capability.Cap} (hcy : capAt (L.mem s) y = ok nc) {nc' : Fl4Spec.Cap} (hnr : CapRel nc nc')
    (hnv : CapValid th nc) (nsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    vspace.derive_subframe st ar s a length (cslotAddr (pp.bv, idx)) (.Frame ptr sz rt dev mm false fa fv) buf ex ⦃ res =>
      SubDecPost (L := L) th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr sz rt dev mm false fa fv)
        (revOf (L.mem s) (cslotAddr (pp.bv, idx))) G σ
        (ExceptT.run (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pp.bv, idx)
          (.pageCap dev ptr.bv (vmRightsOf rt) (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
            (if mm then some (fa.bv, fv.bv) else none)) ((nc', nsl) :: rest)) σ) s a res ⦄ := by
  generalize hD : ExceptT.run (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pp.bv, idx)
    (.pageCap dev ptr.bv (vmRightsOf rt) (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
      (if mm then some (fa.bv, fv.bv) else none)) ((nc', nsl) :: rest)) σ = D
  obtain ⟨cS, aS, hcS, hcaS, -⟩ := hSt.slot_cap (Z := Unit) (sl := (pp.bv, idx)) (p := pp) rfl
    (by simpa [hidx] using hpp)
  rw [hcap] at hcS; cases eq_of_ok_eq hcS
  have hrt : 1 ≤ rt.val ∧ rt.val ≤ 3 := hcaS.1
  unfold vspace.derive_subframe
  rw [hct]; apply ok_bind_spec
  rw [hex0]; simp only [bind_ok]
  by_cases hl6 : length >= 6#u64
  swap
  · rw [if_neg hl6]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, trivial, ?_, rfl, rfl⟩)
    rw [← hD]
    exact decodeSub_trunc (Or.inr (by rw [List.length_map, ← hlen]; scalar_tac)) _ _ σ
  rw [if_pos hl6]
  have hill : (∀ p r mt mp, (Fl4Spec.ArchCap.pageCap dev ptr.bv (vmRightsOf rt)
      (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz) (if mm then some (fa.bv, fv.bv) else none)) ≠
      .pageCap false p r mt .x64LargePage mp) → D = ({(.error .illegalOperation, σ)}, False) := fun h => by
    rw [← hD]; exact decodeSub_illegal (by simp) (by rw [List.length_map, ← hlen]; scalar_tac) _ h σ
  cases sz <;> cases dev
  all_goals try
    simp only [vspace.large_ram_frame, error.illegal, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, trivial,
      hill (fun p r mt mp h => by simp [frameSizeOf] at h), rfl, rfl⟩)
  simp only [vspace.large_ram_frame, Bool.false_eq_true, ↓reduceIte, bind_ok]
  have hal' : ptr.val % 2 ^ 21 = 0 := by
    have h := hSV.cnode pp rs hpp (blVal 0 idx) (hidx ▸ blVal_lt idx) _
      (by rw [show slotAddr pp.bv (BitVec.ofNat 64 (blVal 0 idx)) = cslotAddr (pp.bv, idx) from
        (slotAddr_ofBl pp idx).symm]; exact hcap)
    exact h
  have hfit : ptr.val + 2 ^ 21 ≤ 2 ^ 64 := by have : ptr.val < 2 ^ 64 := ptr.hBounds; omega
  have hno' := hno rfl rfl
  have hfr0' := hFR.alias_ov ((hM.members _).2 ⟨AbsSlot.isSlot (th := th) (sl := (pp.bv, idx)) ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩, _, hcap, by simp⟩) (capV_of_capAt hcap)
  clear hill hno
  obtain ⟨a0, a1, a2, a3, a4, a5, rs', rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5 r, args = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: r := by
    have : 6 ≤ args.length := by rw [← hlen]; scalar_tac
    match args, this with
    | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: r, _ => exact ⟨a0, a1, a2, a3, a4, a5, r, rfl⟩
  rw [hargs 0#u64 a0 rfl, hargs 1#u64 a1 rfl, hargs 2#u64 a2 rfl, hargs 3#u64 a3 rfl, hargs 4#u64 a4 rfl]
  simp only [bind_ok]
  simp only [List.map_cons, frameSizeOf] at hD
  rw [decodeSub_main] at hD
  simp only [uncurry_apply_pair]
  step as ⟨i, hi⟩
  have hiv : i.val = 2097152 := by
    rw [hi]; simp [Nat.shiftLeft_eq, U64.size_def, U64.numBits]
  have hu3 : Fl4Spec.unat a3.bv = a3.val := rfl
  have hu4 : Fl4Spec.unat a4.bv = a4.val := rfl
  by_cases ho1 : a3 >= i
  · rw [if_pos ho1]; simp only [error.invalid_arg, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 3, rfl, rfl, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_inv3 (Or.inl (by rw [hu3]; have : i.val ≤ a3.val := ho1; omega))
  rw [if_neg ho1]
  have ho1' : a3.val < 2097152 := by have : ¬ i.val ≤ a3.val := ho1; omega
  simp only [lift, bind_ok]
  have hand : (a3 &&& 4095#u64).val = a3.val % 4096 := by
    rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod a3.val 12
  by_cases ho2 : (a3 &&& 4095#u64) != 0#u64
  · rw [if_pos ho2]; simp only [error.invalid_arg, bind_ok]
    have hne : (a3 &&& 4095#u64).val ≠ 0 := fun h => (bne_iff_ne.1 ho2) (UScalar.eq_of_val_eq (by rw [h]; rfl))
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 3, rfl, rfl, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_inv3 (Or.inr (by rw [hu3, ← hand]; exact hne))
  rw [if_neg ho2]
  have ho2' : a3.val % 4096 = 0 := by
    have : ¬ (a3 &&& 4095#u64).val ≠ 0 := fun hne => ho2 (bne_iff_ne.2 (fun e => hne (by rw [e]; rfl)))
    omega
  have hinv : ¬ (2 ^ 21 ≤ Fl4Spec.unat a3.bv ∨ Fl4Spec.unat a3.bv % 4096 ≠ 0) := by rw [hu3]; omega
  step as ⟨i2, hi2⟩
  step as ⟨mx, hmx⟩
  have hmxv : mx.val = (2 ^ 21 - a3.val) / 4096 := by
    rw [hmx, hi2, hiv, Nat.shiftRight_eq_div_pow]; rfl
  have hmxe : BitVec.ofNat 64 ((2 ^ 21 - Fl4Spec.unat a3.bv) / 4096) = mx.bv := ofNat_bv (by rw [hu3, hmxv])
  by_cases hc1 : a4 < 1#u64
  · rw [if_pos hc1]; simp only [error.range, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .rangeError 1 (BitVec.ofNat 64 ((2 ^ 21 - Fl4Spec.unat a3.bv) / 4096)),
      rfl, ⟨rfl, hmxe⟩, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_range hinv (Or.inl (by rw [hu4]; scalar_tac))
  rw [if_neg hc1]
  by_cases hc2 : a4 > mx
  · rw [if_pos hc2]; simp only [error.range, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .rangeError 1 (BitVec.ofNat 64 ((2 ^ 21 - Fl4Spec.unat a3.bv) / 4096)),
      rfl, ⟨rfl, hmxe⟩, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_range hinv (Or.inr (by rw [hu4, hu3, ← hmxv]; exact hc2))
  rw [if_neg hc2]
  have hc1' : 1 ≤ a4.val := by scalar_tac
  have hc2' : a4.val ≤ mx.val := by scalar_tac
  have hrng : ¬ (Fl4Spec.unat a4.bv < 1 ∨ (2 ^ 21 - Fl4Spec.unat a3.bv) / 4096 < Fl4Spec.unat a4.bv) := by
    rw [hu3, hu4, ← hmxv]; omega
  rw [sfAfter_go hinv hrng] at hD
  -- the node
  refine WP.spec_bind (subframe_dest_rel (L := L) s σ hSt hSV hcy hnr hnv (pp.bv, idx) ptr.bv (vmRightsOf rt)
    a0 a1 a2 a3 a4 a5) ?_
  rintro r hr
  rw [hD] at hr
  cases r with
  | Err e =>
    obtain ⟨e', he, hE⟩ := hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨e, e', rfl, he, hE, rfl, rfl⟩)
  | Ok dest =>
    obtain ⟨rr, hdp, hr64, hfc, hE⟩ := hr
    have hrr : 2 ^ rr < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [ensure_empty_run_eq (L := L) s dest a2 a4 (by omega)]
    have hdr := sfDests_run (L := L) s σ hSt hdp hr64 a2.val a4.val hfc
    by_cases hemp : ∀ j : Nat, a2.val ≤ j → j < a2.val + a4.val →
        capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 j)) = ok .Null
    swap
    · rw [if_neg hemp]
      rw [if_neg hemp] at hdr
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, trivial, by rw [hE]; exact runE_bind_err hdr, rfl, rfl⟩)
    rw [if_pos hemp]
    rw [if_pos hemp] at hdr
    rw [runE_bind_ok hdr, runE_ret] at hE
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hargs 5#u64 a5 rfl, bind_ok, from_word_eq, bind_ok]
    obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hrt (rightsW a5)
    rw [hm, bind_ok]
    -- the Restart
    have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
    refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hS hR hPt hcur hkt' hrun)
      (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact)) ?_
    rintro s1 ⟨⟨hR1, hPt1, hS1, hksb1⟩, hSS⟩
    set σ1 := Fl4Proofs.P3.Notif.stsAct (Fl4Proofs.P3.Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart }))
      ct.bv with hσ1
    have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) :=
      Notif.setThreadState_eq .restart hkt'
    obtain ⟨σ1', hst', hSt1, hSV1, hM1, hC1, -, -⟩ := restart_rel hSt hSV hM hC hSS hkt' .restart
    have e1 : σ1' = σ1 := by
      rw [hst] at hst'
      have := congrArg Prod.fst hst'
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    rw [e1] at hSt1 hC1
    clear e1 hst' σ1'
    have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
    have hs : IsSlot th (cslotAddr (pp.bv, idx)) := hAs.isSlot
    have hSub1 : SubRel st th P L4 L3 L2 L1 SR (cslotAddr (pp.bv, idx)) (.Frame ptr .Large rt false mm false fa fv)
        (revOf (L.mem s) (cslotAddr (pp.bv, idx))) s1 a σ1 G :=
      { R := hSt1, V := hSV1, M := hM1, C := hC1, I := MdbInv.of_same hM hI hSS, U := UtInv.of_same hM hU hSS
        vs := hR1, pt := hPt1, sr := hS1, cap := by rw [hSS.capAt hs]; exact hcap, rev := hSS.revOf hs
        no := fun x hx => by
          have hxs := ((hM.members x).1 hx).1
          rw [hSS.capV hxs, hSS.revOf hxs]; exact hno' x hx
        F := hFI.of_same hM hSS ((ksub_of_eq (setThreadState_nks _ _) hst).trans (KSub.of_kheap rfl))
        fr := fun w hw q vm h1 h2 hov => by
          have hws := ((hM.members w).1 hw).1
          rw [hSS.capV hws] at hov ⊢
          rw [(frame_range ptr .Large rt false mm fa fv false).1] at h1 h2
          exact hfr0' w hw q vm h1 h2 hov
        FR := hFR.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1)
        VC := hVC.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1) }
    have hbv : (core.num.U64.wrapping_add ptr a3).val = ptr.val + a3.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hdiv : a4.val * 4096 ≤ 2 ^ 21 - a3.val := by
      calc a4.val * 4096 ≤ (2 ^ 21 - a3.val) / 4096 * 4096 :=
            Nat.mul_le_mul_right 4096 (by rw [← hmxv]; exact hc2')
        _ ≤ 2 ^ 21 - a3.val := Nat.div_mul_le_self _ _
    refine WP.spec_bind (insert_subframes_rel (L := L) hH hPl hPP hpp hidx s1 a σ1 G (by rw [hksb1]; exact hVP)
      (by rw [hksb1]; exact hVO) hPO hSub1 hal' hdp hr64 hfc (by rw [hbv]; omega) (by rw [hbv]; omega)
      ⟨hm1, hm3⟩ (by rw [hbv]; omega) (fun j h1 h2 => by
        rw [hSS.capAt ⟨dest, j, Or.inl ⟨rr, hdp, by omega⟩, rfl⟩]; exact hemp j h1 h2)) ?_
    rintro s2 ⟨σ', G', hmap, hSR2, hks2, hMS2⟩
    have hbase : (core.num.U64.wrapping_add ptr a3).bv = ptr.bv + a3.bv := core.num.U64.wrapping_add_bv_eq _ _
    have hrights : vmRightsOf m = Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights a5.bv) := by
      rw [hmv, rightsW_spec]; rfl
    have hperf : Fl4Spec.performDeriveSubframe (Z := Unit)
        ⟨(pp.bv, idx), ptr.bv + a3.bv, Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights a5.bv),
          (List.range' a2.val a4.val).map fun i => (dest.bv, Fl4Spec.natToCref rr i)⟩ =
        Fl4Spec.NonDet.mapMx (subIns (pp.bv, idx) (core.num.U64.wrapping_add ptr a3).bv (vmRightsOf m))
          (subList dest rr a2.val a4.val) := by
      unfold Fl4Spec.performDeriveSubframe subIns subList
      simp only [List.length_map, List.length_range', hbase, hrights]
    have hrun2 : (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performDeriveSubframe (Z := Unit)
          ⟨(pp.bv, idx), ptr.bv + a3.bv, Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights a5.bv),
            (List.range' a2.val a4.val).map fun i => (dest.bv, Fl4Spec.natToCref rr i)⟩) σ =
        ({((), σ')}, False) := by
      rw [← hcur, nd_bind_one hst, hperf]; exact hmap
    exact (WP.spec_ok _).2 (Or.inr ⟨rfl, rfl, _, hE, σ', G', by rw [hrun2]; rfl, by rw [hrun2]; exact id, hSR2,
      hks2.trans hksb1, (MdbStep.of_same hM hSS).trans hMS2⟩)

end Step

end

end Fl4Proofs.P3.Vs
