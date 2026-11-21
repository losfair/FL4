/-
P3 (DESIGN.md §9), VSpace: **`JAtZ` across a native VSpace cap's map,
unmap or ASID assignment** (toward removing XTopJointVsCap's `JPostHyp`).

* `VsXW Z kb x`: the words such a step writes after the caller's restart:
  the VSpace words (XTopJointFinVs's `VsW`: the page-table words, the
  ASID-table and pool words) and the two cap words of the invoked slot `x`
  (a CNode slot; its MDB words are kept, VsFoot's `SlotFoot`).
* `JAtZ.cslot_other`: a CNode slot lies in its CNode, an `other` object of
  `H` (`JPlaced.cnode`), so its words miss every other object of `H`
  (`JAtZ.cslotW_obj`, `HeapOK.disj`) and every core's node (`JKern.hnd`).
* `JPlaced.ofShape`, `DelInv.ofShape`, `coverKept_ofShape`, `utKept_ofShape`:
  the CSpace facts of `JAtZ` across a step changing every slot's cap at most
  to one of the same shape (`shape`: a remapped frame or table cap,
  VsFoot's `MdbLike`) and keeping the slots' MDB words.
* `JAtZ.vsx_utc`: the untyped caps' facts (XTopJointFinVs's `vs_utc` with
  the slot's words: a CNode slot misses every untyped cap's free part,
  `RegionFree`).
* `JAtZ.vsStepJ`: `JAtZ` after such a step, at the same sets, the dead set
  and P1's sets, from `XTopAt` after and the spec's frame `VsSFr`
  (XTopJointVsMapSpec: arch objects of the same arch type, CNodes and TCBs'
  caps; `VsSFr.mid` splits it into an `ArFr` and a `CnStep` step for the
  scheduler's invariants), as XTopJointFinVs's `finVsJb` and
  XTopJointRest's `jowes_slotOf`.
-/
import Fl4Proofs.P3.XTopJointVsMapSpec
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.XTopJointFpu
import Fl4Proofs.P3.XTopJointVsCap
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The words of a VSpace invocation after the restart** (module
docstring). -/
def VsXW (Z : XSets) (kb x b : U64) : Prop := VsW Z kb b ∨ b = x ∨ b = wordOf x 8#u64

/-! ## Caps of the same shape -/

theorem isUt_shape (c : capability.Cap) : isUt (shape c) = isUt c := by cases c <;> rfl

theorem null_of_shape {c d : capability.Cap} (h : shape c = shape d) (hd : d = .Null) : c = .Null := by
  subst hd; cases c <;> simp_all [shape]

theorem fh_of_shape {c d : capability.Cap} (h : shape c = shape d)
    (hd : d = .Null ∨ ∃ ep b0 b1 b2 b3 b4, d = .Endpoint ep b0 b1 b2 b3 b4) :
    c = .Null ∨ ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4 := by
  rcases hd with rfl | ⟨ep, b0, b1, b2, b3, b4, rfl⟩
  · exact Or.inl (null_of_shape h rfl)
  · right; cases c <;> simp_all [shape]

section
variable {th : TypedHeap} {m m' : U64 → U64}

/-- **`DelInv` across a step keeping every slot's shape and links.** -/
theorem DelInv.ofShape (hD : DelInv th m) (hS : ∀ a, IsSlot th a → shape (capV m' a) = shape (capV m a))
    (hl : ∀ a, IsSlot th a → m' (wordOf a 16#u64) = m (wordOf a 16#u64) ∧ m' (wordOf a 24#u64) = m (wordOf a 24#u64)) :
    DelInv th m' := by
  refine DelInv.of_kept hD id (fun y hy p zt n h => ⟨hy, ?_⟩) (fun y y' _ _ hne _ _ _ _ _ _ _ _ => hne)
    (fun y hy h0 => ?_)
  · have e := zombie_of_shape (hS y hy) h
    show capV m y = _
    rw [e]; exact h
  · have h0' : capV m y = .Null := null_of_shape (hS y hy).symm h0
    obtain ⟨n1, n2⟩ := hD.nc y hy h0'
    refine ⟨?_, ?_⟩
    · unfold prevOf; rw [(hl y hy).1]; exact n1
    · unfold nextOf at n2 ⊢; rw [(hl y hy).2]; exact n2

theorem coverKept_ofShape (hS : ∀ a, IsSlot th a → shape (capV m' a) = shape (capV m a)) : CoverKept th m m' := by
  intro y hy hp hu
  obtain ⟨hb, ht, hph⟩ := range_of_shape (hS y hy)
  refine ⟨y, hy, by rw [hph]; exact hp, ?_, hb, ht⟩
  rw [← isUt_shape, hS y hy, isUt_shape]; exact hu

theorem utKept_ofShape (hS : ∀ a, IsSlot th a → shape (capV m' a) = shape (capV m a))
    (hU : ∀ a, IsSlot th a → isUt (capV m a) = true → capV m' a = capV m a) : UtKept th m m' := by
  intro x hx p sb fi d h
  have hu : isUt (capV m x) = true := by rw [← isUt_shape, ← hS x hx, isUt_shape, h]; rfl
  exact ⟨x, hx, fi, by rw [← hU x hx hu]; exact h, Or.inl le_rfl⟩

theorem typedKept_ofShape (hS : ∀ a, IsSlot th a → shape (capV m' a) = shape (capV m a)) : TypedKept th m m' :=
  fun a ha => Or.inr ⟨a, ha, hS a ha⟩

end

/-! ## `JPlaced` across a step keeping the caps' shapes -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`JPlaced` after a step changing each slot's cap at most to one of the
same shape** (`JPlaced.slotTF` with the spec's SCs kept rather than every
object but the CNodes). -/
theorem Sched.JPlaced.ofShape {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ) (hsz : SzKeep σ σ') (hk : L.ksb s' = L.ksb s) (hL : IntLayout th (L.ksb s))
    (hS : ∀ a, IsSlot th a → shape (capV (L.mem s') a) = shape (capV (L.mem s) a))
    (hB : ∀ t, th t = some .tcb → BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))))
    (hiw : idleScW (L := L) s' = idleScW (L := L) s) :
    JPlaced (L := L) th H Tr C s' σ' := by
  have hirqS : ∀ i : U64, i.val < 128 → IsSlot th (nodeA (L.ksb s) i) := fun i hi => by
    have hA : AbsSlot th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
    have := hA.isSlot; rwa [cslotAddr_nil] at this
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk' => ?_, by rw [hk]; exact h.ks, by rw [hk]; exact h.ksIn,
    fun a ha => capTyped_of_shape (hS a ha) (h.typed a ha),
    fun i hi => by rw [hk]; exact capTyped_of_shape (hS _ (hirqS i hi)) (h.irq i hi),
    fun t ht => ?_, hB, fun a ha => by rw [hiw]; exact capObjH_of_shape (hS a ha) (h.cobj a ha)⟩
  · obtain ⟨y0, hk0⟩ := hsz c.bv y n hk'
    exact h.sc c y0 n hc hk0
  · have hs : IsSlot th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) :=
      AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
    exact fh_of_shape (hS _ hs) (h.fh t ht)

end

/-! ## The invoked slot's words -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A CNode slot lies in its CNode, an `other` object of `H`.** -/
theorem JAtZ.cslot_other {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r) :
    H pc = some (.other (r + 5)) ∧ pc.val ≤ (cslotAddr (pc.bv, idx)).val ∧
      (cslotAddr (pc.bv, idx)).val + 32 ≤ pc.val + 2 ^ (r + 5) ∧ pc.val + 2 ^ (r + 5) ≤ 2 ^ 64 := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hAt : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  obtain ⟨q0, i0, hi0, hq1, hq2⟩ := AbsSlot.at hAt
  have hq0 : q0 = pc := P1.eq_of_bv hq1.symm
  subst hq0
  have hv := hi0.val hJ.pl
  have hfit := hJ.pl.fits q0 _ hpc
  simp only [objSize] at hfit
  have e5 : (2 : Nat) ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
  rcases hi0 with ⟨r', hp', hlt⟩ | ⟨hp', -⟩
  · rw [hpc] at hp'
    cases hp'
    have : i0 + 1 ≤ 2 ^ r := hlt
    refine ⟨hJ.cnode q0 r hpc, by rw [hq2, hv]; omega, by rw [hq2, hv, e5]; omega, by rw [e5]; omega⟩
  · rw [hpc] at hp'; cases hp'

/-- The invoked slot's cap words by value. -/
theorem JAtZ.cslotW_val {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {b : U64} (hb : b = cslotAddr (pc.bv, idx) ∨ b = wordOf (cslotAddr (pc.bv, idx)) 8#u64) :
    pc.val ≤ b.val ∧ b.val + 8 ≤ pc.val + 2 ^ (r + 5) ∧ (cslotAddr (pc.bv, idx)).val ≤ b.val ∧
      b.val + 8 ≤ (cslotAddr (pc.bv, idx)).val + 32 := by
  obtain ⟨-, h1, h2, h3⟩ := J.cslot_other hpc hidx
  rcases hb with rfl | rfl
  · omega
  · have h8 : (8#u64 : U64).val = 8 := by first | rfl | simp | decide
    rw [wordOf_val (by omega)]; omega

/-- **The invoked slot's words miss every object of `H` but the `other`
ones.** -/
theorem JAtZ.cslotW_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {b : U64} (hb : b = cslotAddr (pc.bv, idx) ∨ b = wordOf (cslotAddr (pc.bv, idx)) 8#u64)
    {p : U64} {k : P1.HKind} (hp : H p = some k) (hk : ∀ z, k ≠ .other z) :
    b.val + 8 ≤ p.val ∨ p.val + 2 ^ k.bits ≤ b.val := by
  obtain ⟨hH, -, -, -⟩ := J.cslot_other hpc hidx
  obtain ⟨g1, g2, -, -⟩ := J.cslotW_val hpc hidx hb
  have hne : p ≠ pc := fun e => by subst e; rw [hp] at hH; cases hH; exact hk _ rfl
  rcases J.kern.heap.disj p _ pc _ hp hH hne with h | h
  · right; omega
  · simp only [P1.HKind.bits] at h; left; omega

/-- **The invoked slot's words miss every core's node.** -/
theorem JAtZ.cslotW_node {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {b : U64} (hb : b = cslotAddr (pc.bv, idx) ∨ b = wordOf (cslotAddr (pc.bv, idx)) 8#u64)
    {c : U64} (hc : c ∈ Cs) : b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val := by
  obtain ⟨hH, -, -, -⟩ := J.cslot_other hpc hidx
  obtain ⟨g1, g2, -, -⟩ := J.cslotW_val hpc hidx hb
  rcases J.kern.hnd pc _ hH c hc with h | h
  · simp only [P1.HKind.bits] at h; left; omega
  · right; omega

theorem JAtZ.cslotW_al {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {b : U64} (hb : b = cslotAddr (pc.bv, idx) ∨ b = wordOf (cslotAddr (pc.bv, idx)) 8#u64) :
    P1.Aligned b := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have h32 := hA.isSlot.align hJ.pl
  obtain ⟨-, -, h1, h2⟩ := J.cslotW_val hpc hidx hb
  unfold P1.Aligned
  rcases hb with rfl | rfl
  · omega
  · have : (wordOf (cslotAddr (pc.bv, idx)) 8#u64).val = (cslotAddr (pc.bv, idx)).val + 8 := by
      obtain ⟨-, -, g, g'⟩ := J.cslot_other hpc hidx
      have h8 : (8#u64 : U64).val = 8 := by first | rfl | simp | decide
      rw [wordOf_val (by omega), h8]
    omega

/-! ## The frames of tables outside the sets -/

/-- **Off-set table frames** (`PtW X`, written by the Unmap of a mapped table
cap whose table is in no set): every `q ∈ X` 4 KiB-aligned and a spec arch
object of a page (l4v `valid_cap`'s `typ_at`). -/
def TabsArch (X : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ q ∈ X, q.val % 4096 = 0 ∧ ∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12

theorem TabsArch.empty (σ : Fl4Spec.State Unit) : TabsArch ∅ σ := fun _ h => h.elim

/-- A word of an off-set table frame by value. -/
theorem tabW_val {X : Set U64} {σ : Fl4Spec.State Unit} (hX : TabsArch X σ) {b : U64} (hb : PtW X b) :
    ∃ q ∈ X, ∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12 ∧
      q.val % 4096 = 0 ∧ q.val ≤ b.val ∧ b.val + 8 ≤ q.val + 4096 ∧ b.val % 8 = 0 := by
  obtain ⟨q, hq, i, hi, rfl⟩ := hb
  obtain ⟨hqa, ao, hao, hb⟩ := hX q hq
  have hv := peA_val (tbl_fit hqa) hi
  exact ⟨q, hq, ao, hao, hb, hqa, by omega, by omega, by omega⟩

/-- **An off-set table word misses every object of `H` but the `other`
ones** (the table is an `other` object of `H`, `SpecCover.arch`,
`HeapOK.disj`). -/
theorem JAtZ.tabObjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {X : Set U64} (hX : TabsArch X σ) {b : U64} (hb : PtW X b) {p : U64} {k : P1.HKind}
    (hp : H p = some k) (hk : ∀ z, k ≠ .other z) : b.val < p.val ∨ p.val + 2 ^ k.bits ≤ b.val := by
  obtain ⟨q, -, ao, hao, -, -, g1, g2, -⟩ := tabW_val hX hb
  obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hao
  have hne : p ≠ q := fun e => hk n (by subst e; exact Option.some.inj (hp.symm.trans hH))
  have h4 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rcases J.kern.heap.disj p k q _ hp hH hne with h | h
  · right; omega
  · simp only [P1.HKind.bits] at h
    left; omega

/-- **An off-set table word misses every core's node.** -/
theorem JAtZ.tabNodeW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {X : Set U64} (hX : TabsArch X σ) {b : U64} (hb : PtW X b) {c : U64} (hc : c ∈ Cs) :
    b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val := by
  obtain ⟨q, -, ao, hao, -, -, g1, g2, -⟩ := tabW_val hX hb
  obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hao
  have h4 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rcases J.kern.hnd q _ hH c hc with h | h
  · simp only [P1.HKind.bits] at h
    left; omega
  · right; omega

theorem tabW_al {X : Set U64} {σ : Fl4Spec.State Unit} (hX : TabsArch X σ) {b : U64} (hb : PtW X b) :
    P1.Aligned b := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := tabW_val hX hb
  exact h

/-- **A VSpace word or an off-set table word misses every object of `H` but
the `other` ones.** -/
theorem JAtZ.vsObjWX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s) {X : Set U64} (hX : TabsArch X σ) {b : U64}
    (hb : VsW Z (L.ksb s) b ∨ PtW X b) {p : U64} {k : P1.HKind}
    (hp : H p = some k) (hk : ∀ z, k ≠ .other z) : b.val < p.val ∨ p.val + 2 ^ k.bits ≤ b.val :=
  hb.elim (fun hb => J.vsObjW Ap hb hp hk) (fun hb => J.tabObjW hX hb hp hk)

theorem JAtZ.vsNodeWX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {X : Set U64} (hX : TabsArch X σ) {b : U64} (hb : VsW Z (L.ksb s) b ∨ PtW X b) {c : U64} (hc : c ∈ Cs) :
    b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val :=
  hb.elim (fun hb => J.vsNodeW hb hc) (fun hb => J.tabNodeW hX hb hc)

theorem JAtZ.vsW_alX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {X : Set U64} (hX : TabsArch X σ) {b : U64} (hb : VsW Z (L.ksb s) b ∨ PtW X b) : P1.Aligned b :=
  hb.elim (fun hb => J.vsW_al hb) (fun hb => tabW_al hX hb)

/-- **A word of `VsXW` misses every object of `H` but the `other` ones.** -/
theorem JAtZ.vsxObjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s) {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r))
    (hidx : idx.length = r) {b : U64} (hb : VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b) {p : U64} {k : P1.HKind}
    (hp : H p = some k) (hk : ∀ z, k ≠ .other z) : b.val < p.val ∨ p.val + 2 ^ k.bits ≤ b.val := by
  rcases hb with hb | hb
  · exact J.vsObjW Ap hb hp hk
  · rcases J.cslotW_obj hpc hidx hb hp hk with e | e
    · left; omega
    · exact Or.inr e

/-- **A word of `VsXW` misses every core's node.** -/
theorem JAtZ.vsxNodeW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r))
    (hidx : idx.length = r) {b : U64} (hb : VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b) {c : U64} (hc : c ∈ Cs) :
    b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val := by
  rcases hb with hb | hb
  · exact J.vsNodeW hb hc
  · exact J.cslotW_node hpc hidx hb hc

/-- `VsXW` or an off-set table word misses every object of `H` but the `other` ones. -/
theorem JAtZ.vsxObjWX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s) {X : Set U64} (hX : TabsArch X σ) {pc : U64} {r : Nat} {idx : List Bool}
    (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r) {b : U64}
    (hb : VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b ∨ PtW X b) {p : U64} {k : P1.HKind}
    (hp : H p = some k) (hk : ∀ z, k ≠ .other z) : b.val < p.val ∨ p.val + 2 ^ k.bits ≤ b.val :=
  hb.elim (fun hb => J.vsxObjW Ap hpc hidx hb hp hk) (fun hb => J.tabObjW hX hb hp hk)

theorem JAtZ.vsxNodeWX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {X : Set U64} (hX : TabsArch X σ) {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r))
    (hidx : idx.length = r) {b : U64} (hb : VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b ∨ PtW X b) {c : U64}
    (hc : c ∈ Cs) : b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val :=
  hb.elim (fun hb => J.vsxNodeW hpc hidx hb hc) (fun hb => J.tabNodeW hX hb hc)

theorem JAtZ.vsxW_al {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r))
    (hidx : idx.length = r) {b : U64} (hb : VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b) : P1.Aligned b := by
  rcases hb with hb | hb
  · exact J.vsW_al hb
  · exact J.cslotW_al hpc hidx hb

/-- **The untyped caps' facts after a VSpace map, unmap or assignment**
(`vs_utc` with the invoked slot's words: a CNode slot misses every untyped
cap's free part, `RegionFree`; the untyped caps kept, `hUt`). -/
theorem JAtZ.vsx_utcX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {X : Set U64} (hX : TabsArch X σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (fun b => VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b ∨ PtW X b))
    (hVR1 : VsRel Z.P (L.mem s') (L.ksb s) σ')
    (hTN : ∀ i, σ.archState.x64AsidTable i = none → σ'.archState.x64AsidTable i = none)
    (hUt : ∀ y, IsSlot Z.th y → isUt (capV (L.mem s') y) = true → capV (L.mem s') y = capV (L.mem s) y)
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hUt _ hsl.isSlot (by rw [capV_of_capAt hcap]; rfl)]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have hfi := U.fiLe
  have hVR := J.xtop.fin.2.1
  have hPt := J.xtop.fin.2.2.1
  -- a spec object of `2 ^ 12` bytes at a frame
  have spec4k : ∀ (q : U64) (ko : Fl4Spec.KernelObject), σ.kheap q.bv = some ko → Fl4Spec.objBits ko = 12 →
      ∀ w : U64, q.val ≤ w.val → w.val < q.val + 4096 → w.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.val := by
    intro q ko hk hb w h1 h2
    have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) q.bv ko hk
    simp only [hb, UScalar.bv_toNat] at this
    omega
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [hgp]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    by_cases hb : VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) w ∨ PtW X w
    swap
    · rw [hw.mem_eq hal hb]; exact U.zero (B g) w hal h1 h2
    rcases hb with ((⟨q, hq, i, hi, rfl⟩ | ⟨⟨hi, hh, rfl⟩ | ⟨q, hq, lo, hl, rfl⟩⟩) | hx) | hxt
    · exfalso
      have hf := tbl_fit (J.xtop.fin.1.2.pt q hq)
      have hv := peA_val hf hi
      have key : ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = 12 := by
        rcases hq with hq | hq | hq | hq
        · obtain ⟨f, hk, -⟩ := hPt.l4 q hq; exact ⟨_, hk, rfl⟩
        · obtain ⟨f, hk, -⟩ := hPt.l3 q hq; exact ⟨_, hk, rfl⟩
        · obtain ⟨f, hk, -⟩ := hPt.l2 q hq; exact ⟨_, hk, rfl⟩
        · obtain ⟨f, hk, -⟩ := hPt.l1 q hq; exact ⟨_, hk, rfl⟩
      obtain ⟨ko, hk, hb⟩ := key
      rcases spec4k q ko hk hb (peA q i) (by omega) (by omega) with e | e <;> omega
    · have h0 : L.mem s (atA (L.ksb s) hi) = 0#u64 := U.zero (B g) _ hal h1 h2
      have t0 := hVR.table hi hh
      rw [h0] at t0
      have t0' : σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) = none := by rw [t0]; simp [optRef]
      have t1 := hVR1.table hi hh
      rw [hTN _ t0'] at t1
      by_contra hne
      simp [optRef, hne] at t1
    · exfalso
      obtain ⟨-, hf⟩ := J.xtop.fin.1.2.vs.pal q hq
      have hv := peA_val hf hl
      obtain ⟨f, hk, -⟩ := hVR.pool q hq
      rcases spec4k q _ hk rfl (peA q lo) (by omega) (by omega) with e | e <;> omega
    · exfalso
      obtain ⟨g1, g2, -, -⟩ := J.cslotW_val hpc hidx hx
      have e5 : (2 : Nat) ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
      rcases U.free pc _ hpc with e | e
      · simp only [objSize] at e; omega
      · omega
    · exfalso
      obtain ⟨q, -, ao, hao, hb12, -, g1, g2, -⟩ := tabW_val hX hxt
      rcases spec4k q _ hao hb12 w (by omega) (by omega) with e | e <;> omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

/-- `vsx_utcX` without off-set table frames. -/
theorem JAtZ.vsx_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx))))
    (hVR1 : VsRel Z.P (L.mem s') (L.ksb s) σ')
    (hTN : ∀ i, σ.archState.x64AsidTable i = none → σ'.archState.x64AsidTable i = none)
    (hUt : ∀ y, IsSlot Z.th y → isUt (capV (L.mem s') y) = true → capV (L.mem s') y = capV (L.mem s) y)
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi :=
  J.vsx_utcX hpc hidx (TabsArch.empty σ) (hw.mono fun _ h => Or.inl h) hVR1 hTN hUt hcdt horig hgp hDbg

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a VSpace map, unmap or ASID assignment after the
restart** (module docstring): FL4 writes the VSpace words and the invoked
CNode slot's cap words (`VsXW`), that slot's cap of the same shape after and
no untyped cap, the other slots kept (`hcap`), the slots' MDB words kept
(`hl`); the spec steps by `VsSFr`; `XTopAt` after at the same sets. At the
same dead set and P1's sets. `vsStepJX`: also writing the frames `X` of
tables outside the sets (`TabsArch`: spec arch objects, so `other` objects
of `H`, apart from every other object, node and untyped free part), with
the table sets `L3'`, `L2'`, `L1'` after (`XTopAt` and the slots' placement there). -/
theorem JAtZ.vsStepJX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {X : Set U64} (hXa : TabsArch X σ) {L3' L2' L1' : Set U64}
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (hX' : XTopAt (L := L) AR (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) s' a' σ') (F : VsSFr σ σ')
    (hW : P1.WritesIn st s s' (fun b => VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b ∨ PtW X b))
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s) y)
    (hsh : shape (capV (L.mem s') (cslotAddr (pc.bv, idx))) = shape (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hok : okey (capV (L.mem s') (cslotAddr (pc.bv, idx))) = okey (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hnu : isUt (capV (L.mem s) (cslotAddr (pc.bv, idx))) = false)
    (hvf : Vs.vtF (capV (L.mem s') (cslotAddr (pc.bv, idx))) = Vs.vtF (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hl : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s (wordOf y 24#u64))
    (hvc : Vs.VsSlotsW Z.th Z.P Z.L4 L3' L2' L1' (L.mem s')) :
    JAtZ (L := L) arI AR (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) H Cs Ac Lst D s' a' σ' := by
  set x := cslotAddr (pc.bv, idx) with hxdef
  have hkb : L.ksb s' = L.ksb s := hW.1
  have hcpu : L.cpu s' = L.cpu s := hW.2.1
  obtain ⟨σm, F1, C2⟩ := F.mid
  -- the slots' caps: the same shape everywhere
  have hS : ∀ y, IsSlot Z.th y → shape (capV (L.mem s') y) = shape (capV (L.mem s) y) := by
    intro y hy
    by_cases e : y = x
    · rw [e]; exact hsh
    · rw [hcap y hy e]
  have hUt : ∀ y, IsSlot Z.th y → isUt (capV (L.mem s') y) = true → capV (L.mem s') y = capV (L.mem s) y := by
    intro y hy hu
    by_cases e : y = x
    · exfalso
      rw [e, ← isUt_shape, hsh, isUt_shape, hnu] at hu; cases hu
    · exact hcap y hy e
  have hUK : UtKept Z.th (L.mem s) (L.mem s') := utKept_ofShape hS fun y hy _ => by
    by_cases e : y = x
    · exfalso
      have : isUt (capV (L.mem s) y) = true := by assumption
      rw [e, hnu] at this; cases this
    · exact hcap y hy e
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := coverKept_ofShape hS
  have hDel : DelInv Z.th (L.mem s') := J.del.ofShape hS hl
  -- `XTopAt` after: its relations
  obtain ⟨-, ⟨-, -, hM', -, -⟩, hFI', -, hMO', -, -⟩ := hX'.rel
  have hVR1 : VsRel Z.P (L.mem s') (L.ksb s) σ' := by have := hX'.fin.2.1; rwa [hkb] at this
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w : U64, P1.Aligned w → p.val ≤ w.val →
      w.val < p.val + 2 ^ k.bits → L.mem s' w = L.mem s w := fun p k hp hk w hal g1 g2 =>
    hW.mem_eq hal fun hb => by rcases J.vsxObjWX Ap hXa hpc hidx hb hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w : U64, P1.Aligned w → t.val ≤ w.val → w.val < t.val + 4096 →
      L.mem s' w = L.mem s w := fun t ht w hal g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w hal g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
  have k2 : ∀ t ∈ Z.T, L.mem s' (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s' w = L.mem s w := fun q z hq w hal g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w hal g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s' (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s' (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by rcases J.vsxNodeWX hXa hpc hidx hb J.kern.cs0 with e | e <;> omega
  -- the spec's frames
  have hlook : ∀ {p : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject}, (∀ a, ko ≠ .archObj a) →
      (∀ r cs, ko ≠ .cnode r cs) → (∀ x, ko ≠ .tcb x) → (σ'.kheap p = some ko ↔ σ.kheap p = some ko) :=
    fun ha hc ht => F.look ha hc ht
  have lsc : ∀ {p : Fl4Spec.ObjRef} {y : Fl4Spec.SchedContext} {n : Nat},
      (σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n)) :=
    hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
  -- the dead stay dead
  have hAI : Sched.ActIdle σ' := (J.act.ar F1).cn C2
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.yld⟩,
    fun p x n hp => ⟨x, lsc.2 hp, rfl⟩, fun p y n hp => ⟨y, lsc.1 hp, rfl⟩⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_keep hX'.fin.1.1.1 hX'.ipc
      (fun x hx _ => let ⟨y, hy, hc⟩ := F.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
      (fun x hx => (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx)
      (fun x hx => ⟨x, (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx,
        Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx, rfl⟩)
      (fun x n hx => ⟨x, lsc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q) (fun z hz _ => hOut q z hz) F.idle hAI.1
      (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- P1's `BlkOK`: the VSpace words untracked, the slot's words cap-slot words
  have hslw : ∀ b, (b = x ∨ b = wordOf x 8#u64) → SlotWd Z.th b := by
    have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
    rintro b (rfl | rfl)
    · exact ⟨x, hA.isSlot, 0#u64, Or.inl rfl, (wordOf_zero x).symm⟩
    · exact ⟨x, hA.isSlot, 8#u64, Or.inr (Or.inl rfl), rfl⟩
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    refine (P1.blk_of_capw_untracked J.blk hW fun b hb0 => ?_).1
    have hb1 : (VsW Z (L.ksb s) b ∨ PtW X b) ∨ (b = x ∨ b = wordOf x 8#u64) := by
      rcases hb0 with (hb | hb) | hb
      · exact Or.inl (Or.inl hb)
      · exact Or.inr hb
      · exact Or.inl (Or.inr hb)
    rcases hb1 with hb | hb
    · refine Or.inr ⟨⟨J.vsW_alX hXa hb, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, fun hf => ?_⟩
      · rcases J.vsObjWX Ap hXa hb (p := t) (k := .tcb) ht (fun _ e => by cases e) with e | e
        · left; omega
        · right; simpa [P1.HKind.bits] using e
      · rcases J.vsNodeWX hXa hb hc with e | e <;> omega
      · rcases he with he | he
        · have hb8 : b.val % 8 = 0 := J.vsW_alX hXa hb
          have ha := hHk.align e _ he
          simp only [P1.HKind.bits] at ha
          rcases J.vsObjWX Ap hXa hb he (fun _ e => by cases e) with e | e
          · left; omega
          · right; simp only [P1.HKind.bits] at e; omega
        · have hb8 : b.val % 8 = 0 := J.vsW_alX hXa hb
          have ha := hHk.align e _ he
          simp only [P1.HKind.bits] at ha
          rcases J.vsObjWX Ap hXa hb he (fun _ e => by cases e) with e | e
          · left; omega
          · right; simp only [P1.HKind.bits] at e; omega
      · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
        have hko : ∀ z, k ≠ .other z := by
          rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
        obtain ⟨g1, g2⟩ := hin
        rcases J.vsObjWX Ap hXa hb hp hko with e | e <;> omega
    · exact Or.inl (J.slotCapW P1.tlow_slots b (hslw b hb))
  -- the spec's keeps
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, lsc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq, rfl, rfl⟩,
    fun p x n hp => ⟨x, lsc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 (F1.khrb.trans C2.toHStep.khrb)
  have hidl : Sched.IdleKeep (L := L) s s' := J.idleW_keep hX'.fin.1.1.1 F.idle F.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := ⟨Tr, Cq, hJ.ofShape F.szKeep hkb J.intL hS (fun t ht => by
    have hs : IsSlot Z.th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) :=
      AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
    rw [hcap _ hs (fun e => cnode_slot_ne_tcb J.xtop.rel.1 hpc hidx ht 2 (by decide) e.symm)]
    exact hJ.bfs t ht) hidl.2⟩
  have hjc := J.jcov_cover hkb hM' hCK hUK hdead hidl
  have hJC := J.jcs_slot hM' hMO' hFI' hUK F.ksz hDel
  -- `JKern`
  have hkern : JKern (L := L) H Cs D Z.th s' σ' := by
    have K := J.kern
    have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hkb
    obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨Q', R', hc', hs'⟩ := hX'.fin.1.1.1.lists
    have ecw : L.curW s' = L.curW s := by
      apply P1.eq_of_bv
      have h1 := hs'.curThread; have h2 := hs.curThread
      unfold P1.LawfulStore.curW
      rw [hcpu, hna, hc.cur]
      unfold nodeW at h1 h2
      rw [hna] at h1
      rw [← h1, ← h2, F.ct]
    have ecs : L.cscW s' = L.cscW s := by
      apply P1.eq_of_bv
      have h1 := hs'.curSc; have h2 := hs.curSc
      unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
      rw [hcpu, hna, hc.cur]
      unfold nodeW at h1 h2
      rw [hna] at h1
      rw [← h1, ← h2, F.csc]
    have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hkb]
    refine ⟨fun sl h => K.orig sl (by rw [← F.orig]; exact h), by rw [ecw, F.ct]; exact K.cur,
      by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
      by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
      by rw [F.arch]; exact F.hasPm K.gpm, by rw [F.arch]; exact K.ga, by rw [F.arch]; exact K.gf,
      K.heap, K.h0, by rw [hkb]; exact K.hks, by rw [hkb]; exact K.hksIn,
      fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
      by rw [hkb]; exact K.ksbFit, by rw [hkb]; exact K.ksbAl, by rw [hkb, hcpu]; exact K.nodeFit,
      by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
      K.csLt, K.cs0⟩
    rw [hna, hDbg]; exact K.head
  have hutc := J.vsx_utcX hpc hidx hXa hW hVR1 (fun i h => by rw [F.arch]; exact h) hUt F.cdt F.orig
    (by rw [F.arch]) hDbg
  have R : JRest (L := L) arI (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk,
      J.mcp.frame k1 (fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.mcp⟩),
      J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.buf⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, hjc, hkern, hutc, (J.nsc.ar F1).cn C2.toHStep, (J.inv.ar F1).cn C2,
      CurInvW.cn (CurInvW.ar J.cur F1) C2, (J.own.ar F1).cn C2.toHStep, (J.off.ar F1).cn C2.toHStep, hAI,
      (J.bsa.ar F1).cn C2.toHStep, (J.isorted.ar F1).cn C2.toHStep,
      (J.curRun.ar F1).cn C2.toHStep (Or.inr C2.act), hblk⟩
  -- the buffer fields (`JBuf`): objects kept, arch objects of the same type,
  -- CNode slots or TCB caps changed (each TCB's buffer slot kept: the
  -- invoked slot is a CNode slot); the invoked slot's cap of the same object
  -- key (`hok`, so the same frame range)
  have hbf : JBuf (L := L) Z s' σ' := by
    obtain ⟨-, ⟨hSR', -⟩, -⟩ := hX'.rel
    have hfk : IpcFrKeep σ σ' := by
      refine IpcFrKeep.of_slot2 (th := Z.th) (mem := L.mem s) (mem' := L.mem s') (fun p => ?_) J.xtop.rel.2.1.1
        hSR' (fun t x0 hx => ?_) (fun q hq => ?_)
      · rcases F.kh p with e | h | h | ⟨x0, y0, h1, h2, hco⟩
        · exact Or.inl e
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨x0, y0, h1, h2, hco.2.1⟩))
      · rcases F.kh t with e | ⟨a0, a1, -, h2, -⟩ | ⟨r0, cs, cs', -, h2⟩ | ⟨x1, y1, h1, -, -⟩
        · exact J.thOfTcb (by rw [← e]; exact hx)
        · rw [hx] at h2; cases h2
        · rw [hx] at h2; cases h2
        · exact J.thOfTcb h1
      · left
        have hs : IsSlot Z.th (slotOf q 2) := ⟨q, 2, Or.inr ⟨hq, by simp [tcbSlots]⟩, rfl⟩
        have he : cslotAddr (q.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf q 2 := by
          show slotAddr q.bv (Fl4Spec.ofBl _) = _
          rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]
        have hne : slotOf q 2 ≠ x := fun e =>
          cnode_slot_ne_tcb J.xtop.rel.1 hpc hidx hq 2 (by decide) (by rw [he, e])
        rw [capAt_capV, capAt_capV, hcap _ hs hne]
    refine ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, fun y hy => ?_⟩
    by_cases e : y = x
    · rw [e]
      exact Vs.FrIn.of_okey hok ((J.fcap x (by rw [← e]; exact hy)).mono fun _ => UFr.keep hfk.page)
    · rw [hcap y hy e]; exact (J.fcap y hy).mono fun _ => UFr.keep hfk.page
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => J.vsxObjWX Ap hXa hpc hidx hb hp (fun z h => by cases h))
      (fun c hc => J.vsxNodeWX hXa hpc hidx hb hc)
  have hLS := LiveDN.simX J J.live hX' rfl rfl rfl (fun p hp => R.jcov.dead p (J.zD p hp)) F.idle hKd
    (fun sl h => by first | rwa [F.orig] at h | rwa [← F.orig] at h)
    (fun y hy => LSim.of_shape (hS y hy))
  exact J.cs_frameV (V' := (Z.P, Z.L4, L3', L2', L1')) hkb hX' F.kback hbf ⟨hJC.del, hJC.ut, hJC.finM, hJC.sfree⟩ R
    hvc ⟨fun y hy => by
      by_cases e : y = x
      · subst e; exact (J.ext.nat _ hy).of_vtF hvf
      · rw [hcap y hy e]; exact J.ext.nat y hy,
      J.ext.vkeep (fun t ht => tcbK t (J.thT t ht) _ (Sched.tVcpuA_aligned J.ip.e.tcb (J.thT t ht)) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega))⟩
    hLS.1 (fun p hp => J.zD p (hLS.2 p hp))

set_option maxHeartbeats 4000000 in
/-- **`vsStepJX` at the same sets, no off-set table frame written.** -/
theorem JAtZ.vsStepJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (hX' : XTopAt (L := L) AR Z s' a' σ') (F : VsSFr σ σ')
    (hW : P1.WritesIn st s s' (VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx))))
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s) y)
    (hsh : shape (capV (L.mem s') (cslotAddr (pc.bv, idx))) = shape (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hok : okey (capV (L.mem s') (cslotAddr (pc.bv, idx))) = okey (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hnu : isUt (capV (L.mem s) (cslotAddr (pc.bv, idx))) = false)
    (hvf : Vs.vtF (capV (L.mem s') (cslotAddr (pc.bv, idx))) = Vs.vtF (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hl : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s (wordOf y 24#u64))
    (hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s')) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a' σ' :=
  J.vsStepJX Ap hpc hidx (TabsArch.empty σ) (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX' F (hW.mono fun _ h => Or.inl h) hcap hsh hok hnu hvf hl hvc

end


/-! ## From the decode's post to `JAt` -/

section
open Fl4Spec in
/-- **The spec's outcome of a map, unmap or assignment after the restart is
a `VsSFr` step** (XTopJointVsMapSpec's `fv_perform*`). -/
theorem vsSFr_of_post {σ σ1 σ' : Fl4Spec.State Unit}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : (∃ iv, MapSpec σ iv σ' ∨ PtMapSpec σ iv σ' ∨ PdMapSpec σ iv σ' ∨ PdptMapSpec σ iv σ') ∨
      ∃ asid ptr sl, AssignSpec σ asid ptr sl σ') : VsSFr σ1 σ' := by
  rcases h with ⟨iv, h | h | h | h⟩ | ⟨asid, ptr, sl, h⟩
  · cases iv with
    | invokePage pi =>
      obtain ⟨h1, -⟩ := h
      rw [Notif.nd_bind_one hst] at h1
      exact VsSFr.of_fk (fv_performPageInvocation pi) h1
    | _ => exact h.elim
  · cases iv with
    | invokePageTable pi =>
      obtain ⟨h1, -⟩ := h
      rw [Notif.nd_bind_one hst] at h1
      exact VsSFr.of_fk (fv_performPageTableInvocation pi) h1
    | _ => exact h.elim
  · cases iv with
    | invokePageDirectory pi =>
      obtain ⟨h1, -⟩ := h
      rw [Notif.nd_bind_one hst] at h1
      exact VsSFr.of_fk (fv_performPageDirectoryInvocation pi) h1
    | _ => exact h.elim
  · cases iv with
    | invokePDPT pi =>
      obtain ⟨h1, -⟩ := h
      rw [Notif.nd_bind_one hst] at h1
      exact VsSFr.of_fk (fv_performPdptInvocation pi) h1
    | _ => exact h.elim
  · unfold AssignSpec at h
    rw [Notif.nd_bind_one hst] at h
    have hm : ((), σ') ∈ (performAsidPoolInvocation (Z := Unit) (.assign asid ptr sl) σ1).1 := by rw [h]; rfl
    exact VsSFr.of_fk (fv_performAsidPoolInvocation _) hm
end

theorem Sched.ActRel.det {w w' : U64} {a : Fl4Spec.SchedulerAction} (h : ActRel w a) (h' : ActRel w' a) : w = w' := by
  cases a with
  | resumeCurThread => exact h.trans h'.symm
  | chooseNewThread => exact h.trans h'.symm
  | switchThread t => exact P1.eq_of_bv (h.2.2.trans h'.2.2.symm)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`JAt` after a VSpace map, unmap or ASID assignment** (module
docstring): from `JAtZ` at the decode's entry, its post (`FinXR` at the
entry's sets, VsTopX's `VsJPost`): the caller's restart at `J`
(`JAtZ.restartJ`), the spec's step after it a `VsSFr` step
(`vsSFr_of_post`), FL4's writes after it in `VsXW` (the TCBs' state words
and the action word pinned by `XTopAt` at both states, the spec keeping the
TCBs' states and the action; the other slots' words by `SlotFoot`), then
`JAtZ.vsStepJ`. -/
theorem JAtZ.vsPostJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hF : FinXR (L := L) AR Z s' a' σ')
    (hV : VsJPost (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.G s ar σ s' a' σ') : JAt (L := L) arI AR s' a' σ' := by
  rcases hV with ⟨rfl, rfl, rfl⟩ | ⟨hW0, ⟨pc, r, idx, c, hpc, hidx, hc0, hnu, hTI, hSF, hLk, hsp⟩, hCR', hFI', hMO'⟩
  · exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨s1, σ1, x1, -, hst1, hk, hcur, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hP := J.xtop.rel.1
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hact := J.kern.act
  -- FL4's restart
  have hF2 : Frame2 (L := L) s s1 (P1.stA ct) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have h := set_thread_state_frame (L := L) s ct sched.TS_RESTART (stA_al hP htcb) hact.1
    rw [hs1, WP.spec_ok] at h; exact h
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s ct sched.TS_RESTART htcb hact
    rw [hs1, WP.spec_ok] at h; exact h
  have hkc1 : L.ksb s1 = L.ksb s ∧ L.cpu s1 = L.cpu s := by
    have h := set_thread_state_cases (L := L) s ct sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h
    rcases h with rfl | rfl <;> simp
  -- the spec's step and `XTopAt` after
  have F : VsSFr σ1 σ' := vsSFr_of_post hst1 hsp
  have hks' : L.ksb s' = L.ksb s := hW0.1
  have hX' : XTopAt (L := L) AR Z s' a' σ' := by
    obtain ⟨hFin, ⟨G0, hPl, -, -, hD, -, hIA, hSA⟩, hE⟩ := hF
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFin
    exact ⟨hFin, ⟨hPl, hCR', hFI', hD, by rw [hks']; exact hMO', hIA, hSA⟩, IpcRel.of hNt hEp (sched_sc hSch), hE⟩
  -- the TCBs' state words and the action word, pinned
  have pinS : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s1 (P1.stA t) := by
    intro t ht
    have htT := J.thT t ht
    obtain ⟨y1, hk1, hR1⟩ := J1.xtop.ipc.tcb t htT
    obtain ⟨y, hky, hRy⟩ := hX'.ipc.tcb t htT
    obtain ⟨y', hy', hc⟩ := F.tcbF hk1
    rw [hky] at hy'; cases hy'
    have h1 : (L.mem s' (tStA t)).val = (L.mem s1 (tStA t)).val := by rw [hRy.st, hR1.st, hc.st]
    rw [stA_tStA]; exact UScalar.eq_of_val_eq h1
  have pinA : L.mem s' (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) =
      L.mem s1 (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have a1 := J1.xtop.fin.1.1.1.act
    have a2 := hX'.fin.1.1.1.act
    rw [F.act] at a2
    have e := ActRel.det a2 a1
    obtain ⟨Q, R, hc, -⟩ := J.xtop.fin.1.1.1.lists
    unfold nodeW at e
    rw [P1.nodeAt_of_ksb hks', P1.nodeAt_of_ksb hkc1.1, ← hc.cur] at e
    exact e
  -- the slots
  have hSlot : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s1 (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s1 (wordOf y 24#u64) ∧
      (y ≠ cslotAddr (pc.bv, idx) → L.mem s' y = L.mem s1 y ∧ L.mem s' (wordOf y 8#u64) = L.mem s1 (wordOf y 8#u64)) := by
    intro y hy
    obtain ⟨a0, a8, a16, a24⟩ := hSS1 y hy
    obtain ⟨b16, b24, bx⟩ := hSF y hy
    exact ⟨by rw [b16, a16], by rw [b24, a24], fun hne => ⟨by rw [(bx hne).1, a0], by rw [(bx hne).2, a8]⟩⟩
  -- FL4's writes after the restart
  have hW : P1.WritesIn st s1 s' (VsXW Z (L.ksb s1) (cslotAddr (pc.bv, idx))) := by
    refine ⟨hks'.trans hkc1.1.symm, hW0.2.1.trans hkc1.2.symm, fun b hb hn => ?_⟩
    have hslw : ∀ y, IsSlot Z.th y → ∀ k : U64, Off k → b = wordOf y k → L.mem s' b = L.mem s1 b := by
      intro y hy k hk e
      subst e
      obtain ⟨h16, h24, hne⟩ := hSlot y hy
      rcases hk with rfl | rfl | rfl | rfl
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inr (Or.inl (by rw [wordOf_zero, ex])))).elim
        · rw [wordOf_zero]; exact (hne ex).1
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inr (Or.inr (by rw [ex])))).elim
        · exact (hne ex).2
      · exact h16
      · exact h24
    by_cases hb0 : VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s b
    · rcases hb0 with ⟨y, hy, e | e⟩ | ⟨y, k, hy, hk, e⟩ | hpt | hvw | ⟨t, ht, e⟩ | e
      · exact hslw y hy 0#u64 (Or.inl rfl) (by rw [wordOf_zero]; exact e)
      · exact hslw y hy 8#u64 (Or.inr (Or.inl rfl)) e
      · exact hslw y hy k hk e
      · exact (hn (Or.inl (Or.inl hpt))).elim
      · exact (hn (Or.inl (Or.inr (by rw [hkc1.1]; exact hvw)))).elim
      · subst e; exact pinS t ht
      · subst e; exact pinA
    · have e0 : L.mem s' b = L.mem s b := hW0.2.2 b hb hb0
      have e1 : L.mem s1 b = L.mem s b := hF2 b hb (fun e => hb0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ct, htcb, UScalar.eq_of_val_eq e⟩)))))) (fun e => hb0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (UScalar.eq_of_val_eq e)))))))
      rw [e0, e1]
  -- the invoked slot's cap
  have hcv0 : capV (L.mem s) (cslotAddr (pc.bv, idx)) = c := capV_of_capAt hc0
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr (pc.bv, idx)) = c := by rw [hSS1.capV hA.isSlot]; exact hcv0
  have hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s1) y := by
    intro y hy hne
    obtain ⟨-, -, h⟩ := hSlot y hy
    unfold capV; rw [(h hne).1, (h hne).2]
  have Ap : VsApart (L := L) Z H Cs s1 := jVsApartHyp arI Z H Cs Ac1 Lst1 D1 s1 ar σ1 rfl J1
  -- the VSpace caps placed: the invoked slot's new cap from its old one
  -- (`VsLike`, `JAtZ.vsc` and the post's `TabIn`), the other slots kept
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') := by
    intro y hy
    by_cases e : y = cslotAddr (pc.bv, idx)
    · rw [e]
      have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 c := by
        by_cases hn : c = .Null
        · subst hn; trivial
        · have hw := J.vsc _ hA.isSlot
          rw [capV_of_capAt hc0] at hw
          exact hw.okTab hTI
      exact (hLk.2 _ _ _ _ _ hok).toW
    · rw [hcap y hy e]; exact J1.vsc y hy
  have J' := J1.vsStepJ Ap hpc hidx hX' F hW hcap (by rw [hcv1]; exact hLk.1.1) (by rw [hcv1]; exact hLk.1.2.1)
    (by rw [hcv1]; exact hnu) (by rw [hcv1]; exact hLk.1.2.2.2)
    (fun y hy => ⟨(hSlot y hy).1, (hSlot y hy).2.1⟩) hvc
  exact ⟨Z, H, Cs, Ac1, Lst1, D1, J'⟩


set_option maxHeartbeats 8000000 in
/-- **`JAt` after a PML4 flush** (VsTopX's `VsJFlush`): the caller's restart
at `J` (`JAtZ.restartJ`, the same FL4 and spec states by determinism), then
the flush, an arch step keeping FL4's store (XTopJointFpu's `JAtZ.arFrS`:
the spec's machine state only). -/
theorem JAtZ.vsFlushJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hF : FinXR (L := L) AR Z s' a' σ') (hV : VsJFlush (L := L) Z.th Z.G s ar σ s' a' σ') :
    JAt (L := L) arI AR s' a' σ' := by
  rcases hV with ⟨rfl, rfl, rfl⟩ | ⟨ct', σ1, ms, hct', hs, hst, rfl, hCR', hFI', hMO'⟩
  · exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have e : ct = ct' := eq_of_ok_eq (hct.symm.trans hct')
  subst e
  obtain ⟨s1, σ1', -, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have e1 : s' = s1 := eq_of_ok_eq (hs.symm.trans hs1)
  subst e1
  have e2 : σ1' = σ1 := by
    rw [hst] at hst1
    have := congrArg (fun q => ((), σ1') ∈ q.1) hst1
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e2
  have hks' : L.ksb s' = L.ksb s := by
    have h := set_thread_state_cases (L := L) s ct sched.TS_RESTART
    rw [hs, WP.spec_ok] at h
    rcases h with h | h <;> rw [h] <;> simp
  have hX' : XTopAt (L := L) AR Z s' a' { σ1' with machineState := ms } := by
    obtain ⟨hFin, ⟨G0, hPl, -, -, hD, -, hIA, hSA⟩, hE⟩ := hF
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFin
    exact ⟨hFin, ⟨hPl, hCR', hFI', hD, by rw [hks']; exact hMO', hIA, hSA⟩, IpcRel.of hNt hEp (sched_sc hSch), hE⟩
  exact ⟨Z, H, Cs, Ac1, Lst1, D1, J1.arFrS
    ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hX'⟩

end


/-! ## The native table and pool caps at `JAt`, no per-op premise -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A page table cap at `JAt`** (`decode_invocation_page_table_thX`). -/
theorem decode_invocation_page_tableJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    (hok0 : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageTable ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.imp arI (decode_invocation_page_table_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap hok0 extra excaps hex.hext blk call don fp ci buffer hex.hxs
    hX.esa hIA.dom) fun _ _ _ h => J.vsPostJ hni hct h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **A page directory cap at `JAt`** (`decode_invocation_page_directory_thX`). -/
theorem decode_invocation_page_directoryJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap →
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    (hok0 : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageDirectory ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.PageDirectory ptr mp asid0 va0) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
      buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.imp arI (decode_invocation_page_directory_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap hok0 extra excaps hex.hext blk call don fp ci buffer hex.hxs
    hX.esa hIA.dom) fun _ _ _ h => J.vsPostJ hni hct h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **A PDPT cap at `JAt`** (`decode_invocation_pdpt_thX`). -/
theorem decode_invocation_pdptJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0))
    (hok0 : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.Pdpt ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk
      call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.imp arI (decode_invocation_pdpt_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap hok0 extra excaps hex.hext blk call don fp ci buffer hex.hxs
    hX.esa hIA.dom) fun _ _ _ h => J.vsPostJ hni hct h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **An ASID pool cap at `JAt`** (`decode_invocation_asid_pool_thX`). -/
theorem decode_invocation_asid_poolJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (ptr base : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), Z.th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hsl : IsSlot Z.th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base)) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  exact XCap.imp arI (decode_invocation_asid_pool_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hX.fin.1 hX.fin.2.1
    hX.fin.2.2.1 hX.fin.2.2.2.1 hX.fin.2.2.2.2 hVC lbl slbl hlA length buf ct hct hcur htcb J.kern.act
    (J.curRun.run hni) ptr base extra excaps hNative hext slot blk call don fp args ci sl buffer hsl hcap hX.esa
    hIA.dom) fun _ _ _ h => J.vsPostJ hni hct h.1 h.2


set_option maxHeartbeats 4000000 in
/-- **A native frame cap at `JAt`**, Map and Unmap with no per-op premise
(`JAtZ.vsPostJ`); `DeriveSubframe`, `GetAddress` and `TestAndClearAccessed`
with XTopJointStep's `JPostHyp` [W] (`decode_invocation_frame_thX`; `hno` [J]
as there). -/
theorem decode_invocation_frameJV [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hlGA : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress →
      lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : lbl = fl4_abi.label.X86PageDeriveSubframe ∨ lbl = fl4_abi.label.X86PageGetAddress ∨
      lbl = fl4_abi.label.X86PageTestAndClearAccessed →
      JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk
        call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
      buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have h := decode_invocation_frame_thX arI Z.th s ar σ Z.G hCR hFI J.ut hMO hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlbl hlGA length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap (Or.inl trivial) hno extra excaps hex.hext hex.hxs
    blk call don fp ci buffer hDR hX.esa hIA.dom
  by_cases hc : lbl = fl4_abi.label.X86PageDeriveSubframe ∨ lbl = fl4_abi.label.X86PageGetAddress ∨
      lbl = fl4_abi.label.X86PageTestAndClearAccessed
  · exact XCap.jatR arI (XCap.imp arI h fun _ _ _ h => h.1) J (hR hc)
  · have h1 : lbl ≠ fl4_abi.label.X86PageDeriveSubframe := fun e => hc (Or.inl e)
    have h2 : lbl ≠ fl4_abi.label.X86PageGetAddress := fun e => hc (Or.inr (Or.inl e))
    have h3 : lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed := fun e => hc (Or.inr (Or.inr e))
    exact XCap.imp arI h fun _ _ _ h => J.vsPostJ hni hct h.1 (h.2 h1 h2 h3)

set_option maxHeartbeats 4000000 in
/-- **A PML4 cap at `JAt`** (`decode_invocation_pml4_thX`; the ASID
invalidation total by `ArchTotal`). -/
theorem decode_invocation_pml4JV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (h0 : mp = true → asid ≠ 0#u64) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.Pml4 p mp asid) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hinv : ∀ (a : A) (asid : U64), ∃ a', arI.invalidate_asid a asid = ok a' := fun a asid => by
    obtain ⟨r, hr, -⟩ := spec_exists (hT.invalidate_asid a asid)
    exact ⟨r, hr⟩
  exact XCap.imp arI (decode_invocation_pml4_thX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 lbl slbl hlbl ct hct hcur htcb J.kern.act
    (J.curRun.run hni) hinv p asid mp h0 length slot buf blk call don fp extra args ci sl excaps buffer hX.esa hIA.dom)
    fun _ _ _ h => J.vsFlushJ hni hct h.1 h.2
end

end

end Fl4Proofs.P3
