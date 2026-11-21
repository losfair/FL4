/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut4): **the carried facts
that replace the per-entry premise `DetypeOK`** (spec side only; imports only
Fl4Spec via SpecInvUtE).

ut2/ut3's `DetypeOK σ` (no CDT parent slot lies in an object inside the region
of a childless untyped cap) is not inductive on its own. l4v gets it from
`untyped_children_in_mdb` + `if_unsafe_then_cap` + `mdb_cte_at`. The facts
below are those, on the view `uV` (so every generated `UK` frame keeps them),
in the narrowest form their preservation needs:

* `UtChV` [J] (l4v `untyped_children_in_mdb`): a cap whose `objRefs` meet the
  region of an untyped cap sits in a CDT descendant of that untyped's slot.
* `IfUnsafeV` [J] (l4v `if_unsafe_then_cap`, restricted to objects inside some
  untyped region — l4v's `valid_global_refs` keeps the IRQ node and the other
  kernel objects outside every untyped range): a non-null slot of such an object
  is referenced by a slot-holding cap (`sRefs`: CNode, thread, Zombie caps).
* `CapFreeV` [J] (l4v `valid_caps` + `valid_untyped`): no cap references an
  address in an untyped's free part (what makes a new untyped child's region
  unreferenced).
* `CapKindV` [J] (l4v `valid_caps`, cap typing): a cap referencing an object
  that some slot-holding cap references is itself slot-holding (so a non-final
  CNode/thread cap leaves another slot-holding reference behind).
* `CnShapeV` [J] (l4v `valid_cap` sizes + the Zombie part of `valid_cap` /
  `zombies_final`): the non-null slots of an object referenced by a
  slot-holding cap lie in that cap's slot range (a CNode cap's `bits`, a TCB's
  six, a Zombie's first `n`).
* `ZFinalV` [J] (l4v `zombies_final`): no other slot references a Zombie's
  object.

* `CnBitsV` [J] (ut5; l4v `valid_cap` sizes): CNode / CNode-Zombie caps have at
  most 64 radix bits.

`regNull_of`: UtCh + IfUnsafe give **RegNull** (every slot of an object inside a
childless untyped's region holds a null cap), and `detypeOK_of`: RegNull +
CdtOK give `DetypeOK`. `UtInv''` = `UtInv'` ∧ the seven; `boot_utInv''`.
-/
import Fl4Proofs.P3.SpecInvUtE
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- The objects whose slots a cap gives access to (l4v `cte_refs`, object part):
CNode, thread and Zombie caps. -/
def sRefs : Cap → Set ObjRef
  | .cnodeCap r _ _ => {r}
  | .threadCap r => {r}
  | .zombie r _ _ => {r}
  | _ => ∅

theorem sRefs_sub (c : Cap) : sRefs c ⊆ objRefs c := by
  intro r hr
  cases c <;> simp_all [sRefs, objRefs]

/-- The addresses an arch cap covers (l4v `cap_range` / `obj_refs` of arch caps):
a frame cap its whole frame, any other its object. -/
def acRng : ArchCap → Set ObjRef
  | .pageCap _ x _ _ sz _ => {r | ∃ k, k < 2 ^ pageBitsForSize sz ∧ r = x + BitVec.ofNat 64 k}
  | a => {r | aobjRef a = some r}

/-- **The addresses a cap covers** (ut6; l4v `cap_range`): `objRefs`, except that a
frame cap covers its whole frame (`DeriveSubframe` makes caps to interior pages,
so the region facts must speak of every address of a frame, not only its base). -/
def capRng : Cap → Set ObjRef
  | .archObjectCap a => acRng a
  | c => objRefs c

theorem objRefs_sub_capRng (c : Cap) : objRefs c ⊆ capRng c := by
  intro r hr
  cases c with
  | archObjectCap a =>
    cases a <;> simp_all [capRng, acRng, objRefs, aobjRef]
    exact ⟨0, Nat.two_pow_pos _, by simp⟩
  | _ => simpa [capRng] using hr

theorem capRng_nn {c : Cap} {r : ObjRef} (h : r ∈ capRng c) : c ≠ .nullCap := by
  rintro rfl; simp [capRng, objRefs] at h

theorem capRng_ut {d : Bool} {b : ObjRef} {n fi : Nat} : capRng (.untypedCap d b n fi) = ∅ := by
  simp [capRng, objRefs]

/-- The slot range of a slot-holding cap. -/
def SlotShape : Cap → CnodeIndex → Prop
  | .cnodeCap _ bits _, i => i.length = bits
  | .threadCap _, i => ∃ k, k < 6 ∧ i = tcbCnodeIndex k
  | .zombie _ b n, i => ∃ k, k < n ∧ i = natToCref (zombieCteBits b) k
  | _, _ => True

/-- An object inside the region of some untyped cap. -/
def InUtV (w : UView) (q : ObjRef) : Prop :=
  ∃ u dev b n fi, w.2.1 u = some (.untypedCap dev b n fi) ∧ q ∈ delR b n

/-- **UtCh [J]** (l4v `untyped_children_in_mdb`). -/
def UtChV (w : UView) : Prop :=
  ∀ u dev b n fi, w.2.1 u = some (.untypedCap dev b n fi) →
    ∀ s c r, w.2.1 s = some c → r ∈ capRng c → r ∈ delR b n → s ∈ descendantsOf u w.2.2.1

/-- **IfUnsafe [J]** (l4v `if_unsafe_then_cap`, inside untyped regions). -/
def IfUnsafeV (w : UView) : Prop :=
  ∀ p c, w.2.1 p = some c → c ≠ .nullCap → InUtV w p.1 → ∃ s c', w.2.1 s = some c' ∧ p.1 ∈ sRefs c'

/-- **CapFree [J]** (l4v `valid_caps` + `valid_untyped`). -/
def CapFreeV (w : UView) : Prop :=
  ∀ u dev b n fi, w.2.1 u = some (.untypedCap dev b n fi) →
    ∀ s c r, w.2.1 s = some c → r ∈ capRng c → r.toNat ∉ utFr b n fi

/-- The shape of a slot-holding cap: a CNode's (or CNode Zombie's) size, `none` for a TCB. -/
def shp : Cap → Option (Option Nat)
  | .cnodeCap _ bits _ => some (some bits)
  | .threadCap _ => some none
  | .zombie _ b _ => some b
  | _ => none

theorem shp_of_sRefs {c : Cap} {r : ObjRef} (h : r ∈ sRefs c) : ∃ x, shp c = some x := by
  cases c <;> simp_all [sRefs, shp]

theorem sRefs_of_shp {c : Cap} {r : ObjRef} (hr : r ∈ objRefs c) {x : Option Nat} (h : shp c = some x) :
    r ∈ sRefs c := by
  cases c <;> simp_all [sRefs, shp, objRefs]

theorem sRefs_sub_capRng (c : Cap) : sRefs c ⊆ capRng c :=
  fun _ h => objRefs_sub_capRng c (sRefs_sub c h)

/-- A slot-holding cap covers exactly its object. -/
theorem capRng_of_shp {c : Cap} {x : Option Nat} (h : shp c = some x) : capRng c = objRefs c := by
  cases c <;> simp_all [shp, capRng]

theorem objRefs_of_capRng_shp {c : Cap} {r : ObjRef} (hr : r ∈ capRng c) {x : Option Nat} (h : shp c = some x) :
    r ∈ objRefs c := by rw [← capRng_of_shp h]; exact hr

/-- **CapKind [J]** (l4v `valid_caps`, the typing of references): a cap referencing
an object that a slot-holding cap references is slot-holding of the same shape. -/
def CapKindV (w : UView) : Prop :=
  ∀ s c s' c' r, w.2.1 s = some c → w.2.1 s' = some c' → r ∈ capRng c → r ∈ sRefs c' → shp c = shp c'

/-- **CnShape [J]** (l4v `valid_cap` sizes, Zombie ranges). -/
def CnShapeV (w : UView) : Prop :=
  ∀ s c r, w.2.1 s = some c → r ∈ sRefs c → ∀ i c', w.2.1 (r, i) = some c' → c' ≠ .nullCap → SlotShape c i

/-- **ZFinal [J]** (l4v `zombies_final`). -/
def ZFinalV (w : UView) : Prop :=
  ∀ s r b n, w.2.1 s = some (.zombie r b n) → ∀ s' c', s' ≠ s → w.2.1 s' = some c' → r ∉ objRefs c'

/-- The size bound of a slot-holding cap's CNode (`none`: not a CNode / TCB). -/
def CapBitsOK (c : Cap) : Prop := ∀ b, shp c = some (some b) → b ≤ 64

/-- **CnBits [J]** (l4v `valid_cap` CNodeCap: `cap_table_at bits` with `valid_cs_size`,
`bits < word_bits - cte_level_bits`; Zombie: `valid_cap` ZombieCap's size): CNode and
CNode-Zombie caps have at most 64 radix bits (so their slot indices are `natToCref`
images; ut5). -/
def CnBitsV (w : UView) : Prop := ∀ s c, w.2.1 s = some c → CapBitsOK c

/-- The seven new facts. -/
def UtNV (w : UView) : Prop :=
  UtChV w ∧ IfUnsafeV w ∧ CapFreeV w ∧ CapKindV w ∧ CnShapeV w ∧ ZFinalV w ∧ CnBitsV w

/-- **The strengthened untyped invariant** `UtInv'' = UtInv' ∧` the six. -/
def UtInv''V (w : UView) : Prop := UtInv'V w ∧ UtNV w

abbrev UtInv'' (σ : State Unit) : Prop := UtInv''V (uV σ)

theorem UtInv''.ut' {σ : State Unit} (h : UtInv'' σ) : UtInv' σ := h.1

/-! ## RegNull and DetypeOK -/

/-- **RegNull**: every slot of an object inside a childless untyped's region is null. -/
def RegNullV (w : UView) : Prop :=
  ∀ u dev b n fi, w.2.1 u = some (.untypedCap dev b n fi) → (∀ c, w.2.2.1 c ≠ some u) →
    ∀ p c, w.2.1 p = some c → p.1 ∈ delR b n → c = .nullCap

theorem regNull_of {w : UView} (hC : UtChV w) (hU : IfUnsafeV w) : RegNullV w := by
  intro u dev b n fi hu hk p c hp hr
  by_contra hne
  obtain ⟨s, c', hs, hr'⟩ := hU p c hp hne ⟨u, dev, b, n, fi, hu, hr⟩
  exact desc_noKids hk (hC u dev b n fi hu s c' p.1 hs (sRefs_sub_capRng c' hr') hr)

theorem detypeOK_of_V {w : UView} (hO : CdtOKV w) (hR : RegNullV w) :
    ∀ u dev b n fi, w.2.1 u = some (.untypedCap dev b n fi) → (∀ c, w.2.2.1 c ≠ some u) →
      ∀ c p, w.2.2.1 c = some p → p.1 ∉ delR b n := by
  intro u dev b n fi hu hk c p hp hr
  obtain ⟨cap, hcap, hne⟩ := hO c p hp
  exact hne (hR u dev b n fi hu hk p cap hcap hr)

/-- **`DetypeOK` from the carried invariant**: ut2/ut3's [J] premise is a consequence of `UtInv''`. -/
theorem detypeOK_of {σ : State Unit} (h : UtInv'' σ) : DetypeOK σ :=
  detypeOK_of_V h.1.2.1 (regNull_of h.2.1 h.2.2.1)

/-! ## View frames and boot -/

theorem ik_utInv''_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK UtInv'' m :=
  ik_of_uk (fun _ _ e hI => by show UtInv''V _; rw [e]; exact hI) h

theorem ike_utInv''_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE UtInv'' m :=
  ik_utInv''_of_uk h

theorem boot_utNV : UtNV (uV (initASt (Z := Unit))) := by
  have h0 : ∀ sl c, (uV (initASt (Z := Unit))).2.1 sl = some c → c = .nullCap := fun _ _ h => init_capAt h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u dev b n fi hu; cases h0 _ _ hu
  · intro p c hp hne; exact absurd (h0 _ _ hp) hne
  · intro u dev b n fi hu; cases h0 _ _ hu
  · intro s c s' c' r _ hs' _ hr'; rw [h0 _ _ hs'] at hr'; simp [sRefs] at hr'
  · intro s c r hs hr; rw [h0 _ _ hs] at hr; simp [sRefs] at hr
  · intro s r b n hs; cases h0 _ _ hs
  · intro s c hs b hb; rw [h0 _ _ hs] at hb; simp [shp] at hb

/-- **(boot)** `UtInv''` holds at `initASt` (a non-vacuity check; G4 starts from any `UtInv''` state). -/
theorem boot_utInv'' : UtInv'' (initASt (Z := Unit)) := ⟨boot_utInv', boot_utNV⟩

/-! ## `empty_slot` -/

/-- Removing the cap `c` of slot `s` loses no reference that `IfUnsafe` needs:
each object it gives slot access to keeps another slot-holding reference, or
has no non-null slot besides `s` (l4v: `cap_removeable` after finalisation). -/
def SafeDelV (w : UView) (s : CslotPtr) (c : Cap) : Prop :=
  ∀ r, r ∈ sRefs c → (∃ s' c', s' ≠ s ∧ w.2.1 s' = some c' ∧ r ∈ sRefs c') ∨
    (∀ i c', (r, i) ≠ s → w.2.1 (r, i) = some c' → c' = .nullCap)

theorem safeDel_of_sRefs {w : UView} {s : CslotPtr} {c : Cap} (h : sRefs c = ∅) : SafeDelV w s c := by
  intro r hr; rw [h] at hr; exact hr.elim

theorem vEs_cap {w : UView} {s sl : CslotPtr} {c : Cap} (h : (vEs s w).2.1 sl = some c) (hc : c ≠ .nullCap) :
    sl ≠ s ∧ w.2.1 sl = some c := by
  have hne : sl ≠ s := by
    intro e; subst e; simp [vEs, vCap] at h; exact hc h.symm
  refine ⟨hne, ?_⟩
  have : (vEs s w).2.1 sl = w.2.1 sl := Function.update_of_ne hne _ _
  rw [← this]; exact h

theorem objRefs_nn {c : Cap} {r : ObjRef} (h : r ∈ objRefs c) : c ≠ .nullCap := by
  rintro rfl; simp [objRefs] at h

theorem sRefs_nn {c : Cap} {r : ObjRef} (h : r ∈ sRefs c) : c ≠ .nullCap := by
  rintro rfl; simp [sRefs] at h

theorem utN_vEs {w : UView} (hI : UtInv'V w) (hN : UtNV w) {s : CslotPtr} {c : Cap} (hc : w.2.1 s = some c)
    (hSD : SafeDelV w s c) : UtNV (vEs s w) := by
  obtain ⟨-, -, hA⟩ := hI
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  have hut : ∀ u d b n f, (vEs s w).2.1 u = some (.untypedCap d b n f) → u ≠ s ∧ w.2.1 u = some (.untypedCap d b n f) :=
    fun u d b n f h => vEs_cap h (by intro e; cases e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u d b n f hu s' c' r hs' hr hrd
    obtain ⟨hus, hu⟩ := hut u d b n f hu
    obtain ⟨hss, hs'⟩ := vEs_cap hs' (capRng_nn hr)
    exact (es_tg_new hA (hC u d b n f hu s' c' r hs' hr hrd) hus).1 hss
  · intro p c1 hp hne hin
    obtain ⟨hps, hpw⟩ := vEs_cap hp hne
    obtain ⟨u, d, b, n, f, hu, hr⟩ := hin
    obtain ⟨s0, c0, hs0, hr0⟩ := hU p c1 hpw hne ⟨u, d, b, n, f, (hut u d b n f hu).2, hr⟩
    by_cases e : s0 = s
    · subst e
      rw [hc] at hs0; cases hs0
      rcases hSD p.1 hr0 with ⟨s', c', hne', hs', hr'⟩ | hnull
      · refine ⟨s', c', ?_, hr'⟩
        show Function.update _ s0 _ s' = _
        rw [Function.update_of_ne hne']; exact hs'
      · exact absurd (hnull p.2 c1 hps hpw) hne
    · refine ⟨s0, c0, ?_, hr0⟩
      show Function.update _ s _ s0 = _
      rw [Function.update_of_ne e]; exact hs0
  · intro u d b n f hu s' c' r hs' hr
    exact hF u d b n f (hut u d b n f hu).2 s' c' r (vEs_cap hs' (capRng_nn hr)).2 hr
  · intro s1 c1 s2 c2 r h1 h2 hr1 hr2
    exact hK s1 c1 s2 c2 r (vEs_cap h1 (capRng_nn hr1)).2 (vEs_cap h2 (sRefs_nn hr2)).2 hr1 hr2
  · intro s1 c1 r h1 hr i c2 h2 hne
    exact hS s1 c1 r (vEs_cap h1 (sRefs_nn hr)).2 hr i c2 (vEs_cap h2 hne).2 hne
  · intro s1 r b n h1 s' c' hne h2
    obtain ⟨-, h1⟩ := vEs_cap h1 (by intro e; cases e)
    intro hr
    exact hZ s1 r b n h1 s' c' hne (vEs_cap h2 (objRefs_nn hr)).2 hr
  · intro s1 c1 h1
    by_cases hn : c1 = .nullCap
    · subst hn; intro b hb; simp [shp] at hb
    · exact hB s1 c1 (vEs_cap h1 hn).2

theorem hv_pre {P P' Q : UView → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HV P Q m)
    (hp : ∀ w, P' w → P w) : HV P' Q m := fun σ hσ y hy => h σ (hp _ hσ) y hy

/-- **`empty_slot` keeps `UtInv''`** when the removal is safe (`SafeDelV`). -/
theorem hv_emptySlotN (s : CslotPtr) (info : Cap) :
    HV (fun w => UtInv''V w ∧ ∀ c, w.2.1 s = some c → SafeDelV w s c) UtInv''V (emptySlot (Z := Unit) s info) := by
  unfold emptySlot
  refine hv_getCap_bind fun w c hw hc => ?_
  split
  · exact hv_ret _ hw.1
  · rename_i hnn
    refine hv_mono (Q := (· = vEs s w)) ?_ (fun _ e => e ▸ ⟨utInv'_vEs hw.1.1 hc hnn, utN_vEs hw.1.1 hw.1.2 hc (hw.2 c hc)⟩)
    refine hv_gets_bind (fun w => w.2.2.1 s) (fun _ => rfl) fun w1 hw1 => ?_
    subst hw1
    refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w2 hw2 => ?_
    subst hw2
    refine hv_pure_bind ?_
    refine hv_bind (hv_setCdt _ _) fun _ => ?_
    refine hv_bind (hv_doExtendedOp _) fun _ => ?_
    refine hv_bind (hv_setOriginal _ _ _) fun _ => ?_
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    exact hv_uk fun _ => uk_postCapDeletion _

/-- `fast_finalise` has no outcome for a slot-holding cap. -/
theorem fastFinalise_sRefs {c : Cap} (h : sRefs c ≠ ∅) (b : Bool) (σ : State Unit) :
    ((fastFinalise (Z := Unit) c b) σ).1 = ∅ := by
  cases c <;> first | (exact absurd rfl h) | rfl

/-- **`cap_delete_one` keeps `UtInv''`** (no premise: it removes only caps that give no slot access). -/
theorem ik_capDeleteOneN (sl : CslotPtr) : IK UtInv'' (capDeleteOne (Z := Unit) sl) := by
  show HV UtInv''V UtInv''V _
  unfold capDeleteOne
  refine hv_getCap_bind fun w c hw hc => ?_
  unfold NonDet.unless
  split
  · exact hv_ret _ hw
  · refine hv_bind (hv_uk fun _ => uk_isFinalCap c) fun fin => ?_
    by_cases hs : sRefs c = ∅
    · refine hv_bind (R := (· = w)) (hv_uk fun _ => uk_fastFinalise c fin) fun _ => ?_
      refine hv_pre (hv_emptySlotN sl .nullCap) fun w' e => ?_
      subst e
      exact ⟨hw, fun c' hc' => by rw [hc] at hc'; cases hc'; exact safeDel_of_sRefs hs⟩
    · intro σ _ y hy
      obtain ⟨z, hz, -⟩ := hy
      rw [fastFinalise_sRefs hs] at hz; exact hz.elim

end

end Fl4Proofs.P3.SInvU
