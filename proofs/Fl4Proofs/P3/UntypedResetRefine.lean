/-
P3 (DESIGN.md §9), untyped: **FL4's `untyped::reset_untyped` refines l4v
`reset_untyped_cap`** (CSpace side). The relation along the way
(`ResetRel`): the CSpace relations for the typed heap without the region
and the untyped cap with the current free index. FL4's steps against the
spec's: zeroing a chunk (`reset_zero_step`), lowering the free index
(`reset_set_step`), the preemption point (opaque, `PPHyp`).
-/
import Fl4Proofs.P3.UntypedResetSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The CSpace relations during the reset: for the restricted typed heap
`th'`, the ghost tree `G`, the untyped cap at `x` with free index `f`. -/
structure ResetRel (th' : TypedHeap) (G : MdbGhost) (x p sb : U64) (dev : Bool) (mem : U64 → U64)
    (σ : Fl4Spec.State Unit) (f : U64) : Prop where
  R : StateRel th' mem σ
  V : SlotsValid th' mem
  M : MdbLinks th' mem G
  C : CdtRel th' mem σ G
  I : MdbInv mem G
  U : UtInv mem G
  cap : capV mem x = .Untyped p sb f dev

section
variable {th' : TypedHeap} {G : MdbGhost} {x p sb : U64} {dev : Bool}

theorem ResetRel.of_same {mem mem' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {f : U64}
    (h : ResetRel th' G x p sb dev mem σ f) (hS : SlotsSame th' mem mem') (hx : IsSlot th' x)
    (hK : KSame σ σ') : ResetRel th' G x p sb dev mem' σ' f where
  R := (StateRel.of_kheap h.R hK.1).of_caps (fun _ ha => hS.capAt ha)
  V := h.V.of_caps (fun _ ha => hS.capAt ha)
  M := h.M.of_same hS
  C := h.C.of_same hS hK.2.1 hK.2.2.1
  I := MdbInv.of_same h.M h.I hS
  U := UtInv.of_same h.M h.U hS
  cap := by rw [hS.capV hx]; exact h.cap

theorem SlotsSame.of_restrict {th : TypedHeap} {lo hi : Nat} {m m' : U64 → U64} (h : SlotsSame th m m') :
    SlotsSame (restrictTh th lo hi) m m' := fun a ha => h a ha.of_restrict

/-- Slot words of a heap whose slots are outside `[lo, hi)` keep their
values when only words in `[lo, hi)` change. -/
theorem slotsSame_out {th : TypedHeap} (hP : Placed th) {m m' : U64 → U64} {lo hi : Nat}
    (hout : ∀ a, IsSlot th a → a.val + 32 ≤ lo ∨ hi ≤ a.val)
    (hm : ∀ w : U64, P1.Aligned w → (w.val < lo ∨ hi ≤ w.val) → m' w = m w) : SlotsSame th m m' := by
  intro a ha
  have hf := ha.fit hP
  have hal := ha.align hP
  have ho := hout a ha
  have w : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → m' (wordOf a k) = m (wordOf a k) := by
    intro k hk hk8
    have hv := wordOf_val (a := a) (k := k) (by omega)
    exact hm _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {G : MdbGhost} {x p sb : U64} {dev : Bool}

/-- **Zeroing part of the region** keeps the relation (no slot of the
restricted heap is there). -/
theorem reset_zero_step (hP : Placed th) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    {s : S} {σ : Fl4Spec.State Unit} {f : U64}
    (h : ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G x p sb dev (L.mem s) σ f)
    (hx : IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) x)
    (a n : U64) (ha : P1.Aligned a) (hn : n.val % 8 = 0) (h1 : p.val ≤ a.val) (h2 : a.val + n.val ≤ p.val + 2 ^ sb.val)
    (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) :
    ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G x p sb dev (L.mem (L.zr s a n)) σ f ∧
      ∀ w : U64, P1.Aligned w → L.mem (L.zr s a n) w = if a.val ≤ w.val ∧ w.val < a.val + n.val then 0#u64 else L.mem s w := by
  have hz := fun w hw => L.mem_zr s a n w ha hn (by omega) hw
  refine ⟨h.of_same (slotsSame_out hP.restrict (fun b hb => hb.restrict_words hP hN) (fun w hw ho => ?_)) hx
    (KSame.refl _), hz⟩
  rw [hz w hw, if_neg (by omega)]

/-- **Setting the untyped cap's free index** (to `f' ≤ 2 ^ sb`): the spec's
`set_cap`, the relation for the new index. -/
theorem reset_set_step (hP : Placed th) {pp : U64} {rs : Nat}
    (hpp : restrictTh th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {s : S} {σ : Fl4Spec.State Unit} {f : U64}
    (h : ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev (L.mem s) σ f)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx))) (f' : U64) (hf' : f'.val ≤ 2 ^ sb.val) :
    obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s (.Untyped p sb f' dev) ⦃ s' =>
      ∃ cs, σ.kheap pp.bv = some (.cnode rs cs) ∧ Fl4Spec.wellFormedCnodeN rs cs ∧
        ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev (L.mem s')
          (setCnodeSlot σ pp.bv rs cs idx (.untypedCap dev p.bv sb.val f'.val)) f' ∧
        (∀ w : U64, P1.Aligned w → w.val ≠ (cslotAddr (pp.bv, idx)).val →
          w.val ≠ (cslotAddr (pp.bv, idx)).val + 8 → L.mem s' w = L.mem s w) ∧
        (∀ y, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) y → y ≠ cslotAddr (pp.bv, idx) →
          capV (L.mem s') y = capV (L.mem s) y) ∧
        LinksKeep (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s) (L.mem s') ⦄ := by
  set th' := restrictTh th p.val (p.val + 2 ^ sb.val)
  set xs := cslotAddr (pp.bv, idx)
  have hP' : Placed th' := hP.restrict
  obtain ⟨cs, hk, hwf, -⟩ := h.R.cnode pp rs hpp
  have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot th' xs := hAs.isSlot
  have hcap0 : capAt (L.mem s) xs = ok (.Untyped p sb f dev) := by rw [capAt_capV, h.cap]
  have he0 : EncWf (capability.Cap.Untyped p sb f dev) := by rw [capAt_words] at hcap0; exact decode_encWf hcap0
  have he : EncWf (capability.Cap.Untyped p sb f' dev) := ⟨he0.1, he0.2⟩
  have hxm : xs ∈ G.chains.flatten := (h.M.members xs).2 ⟨hxs, _, hcap0, by simp⟩
  obtain ⟨s1, hs1, hU1⟩ := spec_exists (set_cap_upd (L := L) hP' s hxs _ he)
  obtain ⟨s1', hs1', σ', hσ', hR1, hV1, hcdt1, hio1, -, hfr⟩ := spec_exists
    (set_cap_refines th' s σ h.R h.V hP' hpp hidx (.Untyped p sb f' dev) (.untypedCap dev p.bv sb.val f'.val)
      ⟨trivial, rfl⟩ trivial he)
  rw [hs1] at hs1'; have e := eq_of_ok_eq hs1'; subst e
  rw [hs1, WP.spec_ok]
  have hσe : σ' = setCnodeSlot σ pp.bv rs cs idx (.untypedCap dev p.bv sb.val f'.val) := by
    have := (setCap_cnode (Z := Unit) (.untypedCap dev p.bv sb.val f'.val) hk hwf hidx).symm.trans hσ'
    simpa using this.symm
  subst hσe
  obtain ⟨hcs1, hco1, hlk1, -⟩ := hU1
  have hupd : CapShapeUpd th' (L.mem s) (L.mem s1) xs :=
    { links := hlk1, caps := hco1
      shp := by rw [hcs1, h.cap]; rfl
      bdg := by rw [hcs1, h.cap]; rfl
      nn := by rw [hcs1]; simp }
  refine ⟨cs, hk, hwf, ⟨hR1, hV1, hupd.mdbLinks h.M hxm, hupd.cdtRel h.C hcdt1 hio1, hupd.mdbInv h.M h.I,
    UtInv.reset_fi h.M h.I h.U hxm h.cap hnd hcs1 hf' (fun z hz hzx => hco1 z ((h.M.members z).1 hz).1 hzx),
    hcs1⟩, hfr, hco1, hlk1⟩

end

end

theorem regionSet_iff (p q : U64) (n : Nat) (hn : n < 64) (hfit : p.val + 2 ^ n ≤ 2 ^ 64) :
    q.bv ∈ regionSet p.bv n ↔ p.val ≤ q.val ∧ q.val < p.val + 2 ^ n := by
  have h2 : ((2 : BitVec 64) ^ n).toNat = 2 ^ n := by
    rw [BitVec.toNat_pow]
    have : (2 : BitVec 64).toNat = 2 := rfl
    rw [this]; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)
  have h1 : (p.bv + 2 ^ n - 1).toNat = p.val + 2 ^ n - 1 := by
    have := Nat.one_le_two_pow (n := n)
    rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
    show (2 ^ 64 - 1 + (p.val + 2 ^ n) % 2 ^ 64) % 2 ^ 64 = _
    rcases Nat.lt_or_ge (p.val + 2 ^ n) (2 ^ 64) with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have : p.val + 2 ^ n = 2 ^ 64 := by omega
      rw [this, Nat.mod_self]; omega
  show (p.bv ≤ q.bv ∧ q.bv ≤ p.bv + 2 ^ n - 1) ↔ _
  rw [BitVec.le_def, BitVec.le_def, h1]
  show p.val ≤ q.val ∧ q.val ≤ _ ↔ _
  have := Nat.one_le_two_pow (n := n)
  omega

theorem reset_chunk_eq : untyped.RESET_CHUNK = 65536#u64 := by unfold untyped.RESET_CHUNK; rfl
theorem reset_chunk_bits_eq : untyped.RESET_CHUNK_BITS = 16#u64 := by unfold untyped.RESET_CHUNK_BITS; rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (arI : machine.Arch A')
variable {th : TypedHeap} {G : MdbGhost} {p sb : U64} {dev : Bool}

/-- **Hypothesis on FL4's preemption point** (the scheduler's, not proved
here): it keeps the slot words, the words of the region and a property
`E` of the state (for the retype after it: `ksb` and the debug-list head), and returns
`Ok` or `Preempted`, the latter only when the spec's preemption point can
preempt too (keeping the CSpace parts of the state).

[W-false] not true in reachable states (gap K10: the spec cannot preempt
from every state — no error outcome at a state with no pending IRQ and an
active, sufficient current SC, while FL4 preempts on an insufficient SC
without consulting the IRQ line; ∀ ksb: a state with `ksb = slot - 40` has
the `WORK_UNITS` write on a slot word); only the pre-J XTop reset path uses
it (explicit argument of `retype_cont_allN`/`retype_cont_pml4N`/`retype_postN`/
`utRetypeP3_gen`, not a field of `UtCapP3`); superseded by the J-level reset
(the preemption point at a related state, `JAtZ.ppJ`/`jPreemptHyp_of`). -/
def PPHyp (th : TypedHeap) (p sb : U64) (E : S → Prop) : Prop :=
  ∀ (s : S) (a : A'), E s → sched.preemption_point st arI s a ⦃ r =>
    SlotsSame th (L.mem s) (L.mem r.2.1) ∧
    (∀ w : U64, P1.Aligned w → p.val ≤ w.val → w.val < p.val + 2 ^ sb.val → L.mem r.2.1 w = L.mem s w) ∧
    E r.2.1 ∧
    (r.1 = .Ok () ∨ (r.1 = .Err .Preempted ∧ ∀ σ1 : Fl4Spec.State Unit,
      NHas (Fl4Spec.preemptionPoint (Z := Unit)).run σ1 (fun y => y.1 = .error () ∧ KSame σ1 y.2))) ⦄

/-- What the reset ends with: the spec's outcome of the same kind (`Ok` or
preempted) with the CSpace parts of `σ'`, the relation for the free index
`f` (0 if done), and the region zero above it. -/
def ResetPost (σ : Fl4Spec.State Unit) (pp : U64) (idx : List Bool) (th' : TypedHeap) (G : MdbGhost) (x : U64)
    (m0 : U64 → U64) (E : S → Prop) (res : core.result.Result Unit error.Exc × S × A') (zero : Bool) : Prop :=
  ∃ σ' f, ((res.1 = .Ok () ∧ f = 0#u64 ∧
      NHas (Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ (TopP (.ok ()) σ')) ∨
    (res.1 = .Err .Preempted ∧ NHas (Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ (TopP (.error ()) σ'))) ∧
    ResetRel th' G x p sb dev (L.mem res.2.1) σ' f ∧
    (zero = true → ZeroRegion (L.mem res.2.1) (p.val + f.val) (p.val + 2 ^ sb.val)) ∧
    (∀ y, IsSlot th' y → y ≠ x → capV (L.mem res.2.1) y = capV m0 y) ∧ LinksKeep th' m0 (L.mem res.2.1) ∧
    E res.2.1

/-- A property of the state kept by zeroing part of the region and by
writing the untyped cap's slot. -/
def EKept (E : S → Prop) (p sb x : U64) : Prop :=
  (∀ s1 a n, P1.Aligned a → n.val % 8 = 0 → p.val ≤ a.val → a.val + n.val ≤ p.val + 2 ^ sb.val → E s1 →
    E (L.zr s1 a n)) ∧
  (∀ s1 c, E s1 → obj.Slot.set_cap st x s1 c ⦃ s' => E s' ⦄)

/-- **The chunk loop** from offset `o` (a multiple of the chunk, the region
zero above `o` plus a chunk), the spec's chunks `o / 2^16, .., 0` left. -/
theorem reset_loop (hP : Placed th) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hp16 : p.val % 65536 = 0) (hrcb : Fl4Spec.resetChunkBits = 16)
    {E : S → Prop} (hPP : PPHyp (L := L) arI th p sb E) {pp : U64} {rs : Nat}
    (hpp : restrictTh th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    (hEk : EKept (L := L) E p sb (cslotAddr (pp.bv, idx)))
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx))) (σ0 : Fl4Spec.State Unit)
    (s : S) (a : A') (o : U64) (ho1 : o.val % 65536 = 0) (ho2 : o.val + 65536 ≤ 2 ^ sb.val)
    (σk : Fl4Spec.State Unit) (f : U64)
    (hRR : ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev (L.mem s) σk f)
    (hZ : ZeroRegion (L.mem s) (p.val + o.val + 65536) (p.val + 2 ^ sb.val))
    (hK : RCont dev p.bv sb.val pp.bv idx σ0 (o.val / 65536) σk) (m0 : U64 → U64)
    (hF : ∀ y, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) y → y ≠ cslotAddr (pp.bv, idx) →
      capV (L.mem s) y = capV m0 y) (hLk : LinksKeep (restrictTh th p.val (p.val + 2 ^ sb.val)) m0 (L.mem s))
    (hE : E s) :
    untyped.reset_untyped_loop st arI s a (cslotAddr (pp.bv, idx)) p sb dev o ⦃ res =>
      ResetPost (L := L) (p := p) (sb := sb) (dev := dev) σ0 pp idx (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx))
        m0 E res true ⦄ := by
  set th' := restrictTh th p.val (p.val + 2 ^ sb.val)
  set xs := cslotAddr (pp.bv, idx) with hxsdef
  have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot th' xs := hAs.isSlot
  have hxo := hxs.restrict_words hP hN
  have hxf := hxs.fit hP.restrict
  have hxa := hxs.align hP.restrict
  unfold untyped.reset_untyped_loop
  refine loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => x.2.2.val % 65536 = 0 ∧ x.2.2.val + 65536 ≤ 2 ^ sb.val ∧ ∃ σk f,
      ResetRel th' G xs p sb dev (L.mem x.1) σk f ∧
      ZeroRegion (L.mem x.1) (p.val + x.2.2.val + 65536) (p.val + 2 ^ sb.val) ∧
      RCont dev p.bv sb.val pp.bv idx σ0 (x.2.2.val / 65536) σk ∧
      (∀ y, IsSlot th' y → y ≠ xs → capV (L.mem x.1) y = capV m0 y) ∧ LinksKeep th' m0 (L.mem x.1) ∧ E x.1)
    _ _ _ ?_ ?_
  rotate_left
  · exact ⟨ho1, ho2, σk, f, hRR, hZ, hK, fun y hy hyx => hF y hy hyx, hLk, hE⟩
  rintro ⟨s1, a1, o⟩ ⟨ho1, ho2, σk, f, hRR, hZ, hK, hF, hLk, hE⟩
  simp only at ho1 ho2 hRR hZ hK hF hLk hE ⊢
  unfold untyped.reset_untyped_loop.body
  have hiv : (core.num.U64.wrapping_add p o).val = p.val + o.val := by
    rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  simp only [lift, bind_ok, L.clear_free_eq]
  have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
  obtain ⟨hRR1, hz1⟩ := reset_zero_step hP hN hRR hxs (core.num.U64.wrapping_add p o) untyped.RESET_CHUNK
    (by unfold P1.Aligned; rw [hiv]; omega) (by rw [hC]) (by rw [hiv]; omega) (by rw [hiv, hC]; omega) hfit
  set s1z := L.zr s1 (core.num.U64.wrapping_add p o) untyped.RESET_CHUNK
  have hZ1 : ZeroRegion (L.mem s1z) (p.val + o.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hz1 w hw]
    split_ifs with hc
    · rfl
    · rw [hiv, hC] at hc; exact hZ w hw (by omega) h2
  obtain ⟨s2, hs2, cs, hk, hwf, hRR2, hfr2, hco2, hlk2⟩ := spec_exists (reset_set_step (L := L) hP hpp hidx hRR1 hnd o (by omega))
  have hE1 : E s1z := hEk.1 _ _ _ (by unfold P1.Aligned; rw [hiv]; omega) (by rw [hC])
    (by rw [hiv]; omega) (by rw [hiv, hC]; omega) hE
  obtain ⟨s2', hs2', hE2⟩ := spec_exists (hEk.2 s1z (.Untyped p sb o dev) hE1)
  rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
  rw [hs2]
  simp only [bind_ok]
  rw [← hxsdef] at hfr2 hco2
  have hS1 : SlotsSame th' (L.mem s1) (L.mem s1z) :=
    slotsSame_out hP.restrict (fun b hb => hb.restrict_words hP hN) (fun w hw ho => by
      rw [hz1 w hw, if_neg (by rw [hiv, hC]; omega)])
  have hF2 : ∀ y, IsSlot th' y → y ≠ xs → capV (L.mem s2) y = capV m0 y := fun y hy hyx => by
    rw [hco2 y hy hyx, hS1.capV hy]; exact hF y hy hyx
  have hL2 : LinksKeep th' m0 (L.mem s2) := (hLk.trans (LinksKeep.of_same hS1)).trans hlk2
  have hZ2 : ZeroRegion (L.mem s2) (p.val + o.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hfr2 w hw (by omega) (by omega)]; exact hZ1 w hw h1 h2
  have hk0 : o.val / 65536 * 2 ^ Fl4Spec.resetChunkBits = o.val := by rw [hrcb]; omega
  by_cases ho0 : o = 0#u64
  · rw [if_pos ho0]
    have hov : o.val = 0 := by rw [ho0]; rfl
    rw [hov] at hK
    refine (WP.spec_ok _).2 ⟨setCnodeSlot σk pp.bv rs cs idx (.untypedCap dev p.bv sb.val o.val), 0#u64,
      Or.inl ⟨rfl, rfl, ?_⟩, ?_, fun _ => ?_, hF2, hL2, hE2⟩
    · have := RCont.done hrcb (by show (p.bv.toNat) % 8 = 0; show p.val % 8 = 0; omega) hidx hK hk hwf
      rw [hov]; simpa using this
    · rw [ho0] at hRR2 ⊢; exact hRR2
    · simpa [hov] using hZ2
  · rw [if_neg ho0]
    have ho0' : o.val ≠ 0 := fun e => ho0 (UScalar.eq_of_val_eq e)
    -- #52: the cap just written reads back as the untyped cap, so the
    -- doomed-transaction exit (`as_untyped` = `none`) is not taken.
    have hcap2 : obj.Slot.cap st xs s2 = ok (.Untyped p sb o dev) := by
      rw [slot_cap_eq, capAt_capV, hRR2.cap]
    simp only [hcap2, bind_ok, untyped.as_untyped, core.option.Option.is_none, Bool.false_eq_true,
      ↓reduceIte]
    obtain ⟨⟨r, s3, a2⟩, hp3, hS3, hreg3, hE3, hr3⟩ := spec_exists (hPP s2 a1 hE2)
    rw [hp3]
    simp only [bind_ok]
    have hS3' : SlotsSame th' (L.mem s2) (L.mem s3) := hS3.of_restrict
    have hZ3 : ZeroRegion (L.mem s3) (p.val + o.val) (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      rw [hreg3 w hw (by omega) h2]; exact hZ2 w hw h1 h2
    have hRR3 := hRR2.of_same hS3' hxs (KSame.refl _)
    have hF3 : ∀ y, IsSlot th' y → y ≠ xs → capV (L.mem s3) y = capV m0 y := fun y hy hyx => by
      rw [hS3'.capV hy]; exact hF2 y hy hyx
    have hL3 : LinksKeep th' m0 (L.mem s3) := hL2.trans (LinksKeep.of_same hS3')
    rcases hr3 with hok | ⟨herr, hppE⟩
    · simp only at hok; subst hok
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
      set k := o.val / 65536 with hkdef
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1] at hK
      obtain ⟨σn, hKS, hK'⟩ := RCont.step hrcb (by show p.val % 8 = 0; omega) hidx hK hk hwf
      have hov : (k - 1 + 1) * 2 ^ Fl4Spec.resetChunkBits = o.val := by rw [← hk1, hrcb]; omega
      rw [hov] at hKS
      have hsv : (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val = o.val - 65536 := by
        show (BitVec.ofNat 64 (max 0 (o.val - untyped.RESET_CHUNK.val))).toNat = _
        rw [hC]; simp; omega
      refine (WP.spec_ok _).2 ⟨⟨by rw [hsv]; omega, by rw [hsv]; omega, σn, o, hRR3.of_same (SlotsSame.refl _ _) hxs hKS,
        ?_, ?_, hF3, hL3, hE3⟩, ?_⟩
      · rw [hsv, show p.val + (o.val - 65536) + 65536 = p.val + o.val by omega]; exact hZ3
      · rw [hsv, show (o.val - 65536) / 65536 = k - 1 by omega]; exact hK'
      · show (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val < o.val
        rw [hsv]; omega
    · simp only at herr; subst herr
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      simp only [bind_tc_ok, bind_ok]
      refine (WP.spec_ok _).2 ⟨setCnodeSlot σk pp.bv rs cs idx (.untypedCap dev p.bv sb.val o.val), o,
        Or.inr ⟨rfl, ?_⟩, hRR3, fun _ => hZ3, hF3, hL3, hE3⟩
      have := RCont.preempt hrcb (by show p.val % 8 = 0; omega) hidx hppE hK hk hwf
      rw [hk0] at this; exact this

end



/-- No descendants in the ghost tree from the spec's "no CDT children"
(what `decode` checks to set `reset`). -/
theorem nodesc_of_cdt {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hP : Placed th) (hC : CdtRel th mem σ G) {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot th sl)
    (hno : ¬ ∃ sl', σ.cdt sl' = some sl) : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr sl) := by
  intro y hd
  obtain ⟨z, hz⟩ := desc_tail_child hd
  obtain ⟨sl', hAs', he⟩ := hC.par_slot z _ hz
  have h1 := hC.cdt sl' hAs'
  rw [he, hz] at h1
  obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.1 h1
  have hAq := (hC.cdt_slot sl' q hq).2
  exact hno ⟨sl', by rw [hq, cslotAddr_inj hP hAq hAs hqe]⟩

/-- **A CNode named by a cap of the MDB misses a childless untyped cap's
region** (as ScPlaceUt's `ut_free`; l4v `untyped_children_in_mdb`: a cap
meeting the region descends from the untyped cap): the reset's destination
CNode, named by the decode's node cap, survives the region's reset. -/
theorem cnode_off_childless {mem : U64 → U64} {G : MdbGhost} (hU : UtInv mem G) (hI : MdbInv mem G) {x : U64}
    (hx : x ∈ G.chains.flatten) {p sb fi : U64} {d : Bool} (hcx : capV mem x = .Untyped p sb fi d)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x) {y : U64} (hy : y ∈ G.chains.flatten) {q r gs g : U64}
    (hcy : capV mem y = .CNode q r gs g) : ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) := by
  have hsb := capV_ut_sb hcx
  have hreg := hU.reg x hx (by rw [hcx]; exact ok_inj (phys_eq _).symm)
  rw [hcx] at hreg
  obtain ⟨b1, t1, -⟩ := ut_range hsb hreg
  have hpy : physF (capV mem y) = true := by rw [hcy]; exact ok_inj (phys_eq _).symm
  have hregy := hU.reg y hy hpy
  have hby : baseF (capV mem y) = q.val := by
    rw [hcy]; unfold baseF; rw [show ptrF (.CNode q r gs g) = q from ok_inj (ptr_eq _).symm]
  have hyx : y ≠ x := by rintro rfl; rw [hcx] at hcy; cases hcy
  by_cases hdj : Disj (capV mem y) (capV mem x)
  · unfold Disj at hdj
    rw [hcx, b1, t1] at hdj
    have := Nat.one_le_two_pow (n := sb.val)
    omega
  · rcases hU.drange x hx p sb fi d hcx y hy hyx hpy hdj with h | h
    · exact absurd h (hnd y)
    · have := hI.anc_ut h (by rw [hcx]; rfl)
      rw [hcy] at this; simp [isUt] at this

theorem and_not_mask (x m : U64) (hm : m.val = 65535) : (x &&& ~~~m).val = x.val / 65536 * 65536 := by
  have hmb : m.bv = 65535#64 := BitVec.eq_of_toNat_eq hm
  show (x.bv &&& ~~~m.bv).toNat = _
  rw [hmb, show ~~~(65535#64 : BitVec 64) = BitVec.allOnes 64 <<< 16 by decide,
    ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 : x.bv.toNat < 2 ^ 64 := x.bv.isLt
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) h1)]
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (arI : machine.Arch A')

/-- **FL4's `reset_untyped` refines l4v `reset_untyped_cap`** (CSpace side),
for an untyped cap `Untyped p sb fi dev` (`fi ≠ 0`) in a CNode slot with no
descendants (as `decode` checks before asking for a reset). The spec does
not fail, and has an outcome of the kind FL4 returns (done, or preempted at
a chunk) whose heap, CDT and original bits are related to FL4's result for
the typed heap without the region (l4v `detype`): `StateRel`, `SlotsValid`,
`MdbLinks`, `CdtRel`, `MdbInv`, `UtInv`, the cap with the free index `f`
reached (0 when done), and for a non-device region the region zero above
`f`.

Hypotheses beyond the relations: no linked slot in the region (`hns`; l4v
derives it from `if_unsafe_then_cap`), no object straddling its bounds
(`hN`), the region zero above `fi` (`hzero`, as retype keeps it), the
cap aligned to its size of at least 16 bytes, the chunk size of the
configuration 16 bits (`hrcb`, FL4's `RESET_CHUNK_BITS`), and the
preemption points opaque (`hppS`: the spec's does not fail and keeps the
CSpace parts; `hPP`: FL4's keeps the slots and the region, and preempts
only when the spec can). -/
theorem reset_untyped_refines (th : TypedHeap) (s : S) (a : A') (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev)) (hfi0 : fi.val ≠ 0)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame) {E : S → Prop} (hPP : PPHyp (L := L) arI th p sb E)
    (hEk : EKept (L := L) E p sb (cslotAddr (pp.bv, idx))) (hE : E s) :
    untyped.reset_untyped st arI s a (cslotAddr (pp.bv, idx)) ⦃ res =>
      NSat (Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ (fun _ => True) ∧
      ResetPost (L := L) (p := p) (sb := sb) (dev := dev) σ pp idx (restrictTh th p.val (p.val + 2 ^ sb.val)) G
        (cslotAddr (pp.bv, idx)) (L.mem s) E res (!dev) ⦄ := by
  set th' := restrictTh th p.val (p.val + 2 ^ sb.val)
  set x := cslotAddr (pp.bv, idx) with hxdef
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hcv := capV_of_capAt hcap
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot th x := hAs.isSlot
  have hxm : x ∈ G.chains.flatten := (hM.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hrx := hU.reg x hxm (by rw [hcv]; exact physF_ut _ _ _ _)
  rw [hcv] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  have hfib : fi.val ≤ 2 ^ sb.val := hU.fib x hxm _ _ _ _ hcv
  have hxout := hns x hxm
  have hxs' : IsSlot th' x := hxs.restrict hP hN hxout
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    obtain ⟨q, j, hj, hq, he⟩ := hAs.at
    have : pp = q := bv_inj hq
    subst this
    exact hj.obj_out hP hN (by rw [← he]; exact hxout)
  have hpp' : th' pp = some (.cnode rs) := by
    show restrictTh th _ _ pp = _; rw [restrictTh_out hppout]; exact hpp
  have hpb : pp.bv ∉ regionSet p.bv sb.val := by rw [regionSet_iff _ _ _ hsb hfit]; exact hppout
  obtain ⟨cs, hk, hwf, -⟩ := hR.cnode pp rs hpp
  have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 hsb4; simpa using this
  have hmod : ∀ d, d ∣ 2 ^ sb.val → p.val % d = 0 := by
    intro d hd; have := Nat.mod_mod_of_dvd p.val hd; rw [hpal, Nat.zero_mod] at this; exact this.symm
  have hp8 : p.bv.toNat % 8 = 0 := hmod 8 (dvd_trans (by norm_num) h16)
  have hNS := reset_nsat hk hwf hidx hg hfi0 hp8 hpb hrcb hppS
  -- the relation after `delete_objects`
  have rel0 : ∀ σD, KSame (Fl4Spec.detype (regionSet p.bv sb.val) σ) σD →
      ResetRel th' G x p sb dev (L.mem s) σD fi := by
    intro σD hD
    obtain ⟨h1, h2, h3, h4⟩ := detype_rel (σd := σD) hR hV hP hM hC hI hU hxm hcv hnd hN hns
      (fun q hq => by rw [hD.1]; simp only [Fl4Spec.detype]; rw [if_neg (by rw [regionSet_iff _ _ _ hsb hfit]; exact hq)])
      hD.2.1 hD.2.2.1
    exact ⟨h1, h2, h3, h4, hI, hU, hcv⟩
  have hcsD : ∀ σD, KSame (Fl4Spec.detype (regionSet p.bv sb.val) σ) σD → σD.kheap pp.bv = some (.cnode rs cs) :=
    fun σD hD => detype_hasCN hk hpb hD
  -- FL4
  unfold untyped.reset_untyped
  rw [slot_cap_eq, hcap]
  have hfi0' : ¬ (fi = 0#u64) := fun e => hfi0 (by rw [e]; rfl)
  simp only [bind_ok, untyped.as_untyped, hfi0', ↓reduceIte]
  cases dev
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hsm : sb < untyped.RESET_CHUNK_BITS
    · -- a small region: zero it, then the free index 0
      rw [if_pos hsm]
      have hsm' : sb.val < 16 := by rw [reset_chunk_bits_eq] at hsm; exact hsm
      have h63 : (sb &&& 63#u64).val = sb.val := by
        have : (sb &&& 63#u64).val = sb.val % 64 := by
          simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
        rw [this]; omega
      obtain ⟨i1, hi1, hv1, -⟩ := spec_exists (UScalar.ShiftLeft_spec (1#u64 : U64) (sb &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      have hi1v : i1.val = 2 ^ sb.val := by
        rw [hv1, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
        exact Nat.pow_lt_pow_right (by decide) hsb
      simp only [lift, bind_ok, hi1, L.clear_free_eq]
      obtain ⟨σD, hD, hhas⟩ := reset_small hk hwf hidx hg hfi0 hp8 hpb hrcb (Or.inr (by rw [hrcb]; exact hsm'))
      obtain ⟨hRR1, hz1⟩ := reset_zero_step hP hN (rel0 σD hD) hxs' p i1
        hp8 (by rw [hi1v]; omega) (le_refl _) (by rw [hi1v]) hfit
      obtain ⟨s2, hs2, cs', hk', hwf', hRR2, hfr2, hco2, hlk2⟩ := spec_exists
        (reset_set_step (L := L) hP hpp' hidx hRR1 hnd 0#u64 (by simp))
      have hE1 : E (L.zr s p i1) := hEk.1 _ _ _ hp8 (by rw [hi1v]; omega) (le_refl _) (by rw [hi1v]) hE
      obtain ⟨s2', hs2', hE2⟩ := spec_exists (hEk.2 _ (.Untyped p sb 0#u64 false) hE1)
      rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
      rw [← hxdef] at hs2 hfr2 hco2
      have hS1 : SlotsSame th' (L.mem s) (L.mem (L.zr s p i1)) :=
        slotsSame_out hP.restrict (fun b hb => hb.restrict_words hP hN) (fun w hw ho => by
          rw [hz1 w hw, if_neg (by rw [hi1v]; omega)])
      rw [hs2]
      simp only [bind_ok]
      have e : cs' = cs := by rw [hcsD σD hD] at hk'; cases hk'; rfl
      subst e
      refine (WP.spec_ok _).2 ⟨hNS, setCnodeSlot σD pp.bv rs cs' idx (.untypedCap false p.bv sb.val 0), 0#u64,
        Or.inl ⟨rfl, rfl, hhas⟩, hRR2, fun _ => ?_, fun y hy hyx => by rw [hco2 y hy hyx, hS1.capV hy],
        (LinksKeep.of_same hS1).trans hlk2, hE2⟩
      intro w hw h1 h2
      have h1' : p.val ≤ w.val := by simpa using h1
      have hxw := hxs'.restrict_words hP hN
      rw [hfr2 w hw (by omega) (by omega), hz1 w hw, if_pos (by rw [hi1v]; omega)]
    · -- the chunked reset
      rw [if_neg hsm]
      have hsb16 : 16 ≤ sb.val := by rw [reset_chunk_bits_eq] at hsm; exact Nat.le_of_not_lt hsm
      have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
      obtain ⟨i, hi, hiv, -⟩ := spec_exists (U64.sub_spec (x := fi) (y := 1#u64)
        (by have : (1#u64 : U64).val = 1 := rfl; rw [this]; omega))
      obtain ⟨i1, hi1, hi1v, -⟩ := spec_exists (U64.sub_spec (x := untyped.RESET_CHUNK) (y := 1#u64)
        (by have : (1#u64 : U64).val = 1 := rfl; rw [this, hC]; omega))
      rw [hi, hi1]
      simp only [bind_ok, lift]
      have hi1v' : i1.val = 65535 := by rw [hi1v, hC]; rfl
      have hov : (i &&& ~~~i1).val = (fi.val - 1) / 65536 * 65536 := by
        rw [and_not_mask i i1 hi1v', hiv]; rfl
      have hdv : 65536 ∣ 2 ^ sb.val := by
        have := Nat.pow_dvd_pow 2 hsb16; simpa using this
      obtain ⟨t, ht⟩ := hdv
      have hq : (fi.val - 1) / 65536 < t := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      have hqa := Nat.lt_div_mul_add (a := fi.val - 1) (b := 65536) (by decide)
      obtain ⟨σD, hD, hK⟩ := reset_init hk hwf hidx hg hfi0 hp8 hpb hrcb
        (by rw [hrcb]; simp; omega) hfib
      rw [hrcb] at hK
      refine WP.spec_mono (reset_loop arI hP hN hfit (hmod 65536 ⟨t, ht⟩) hrcb hPP hpp' hidx hEk hnd σ s a (i &&& ~~~i1)
        (by rw [hov]; omega) (by rw [hov, ht]; nlinarith) σD fi (rel0 σD hD)
        (fun w hw h1 h2 => hzero w hw (by rw [hov] at h1; omega) h2)
        (by rw [hov, Nat.mul_div_cancel _ (by decide)]; simpa using hK) (L.mem s) (fun _ _ _ => rfl)
        (LinksKeep.refl _ _) hE)
        (fun res hres => ⟨hNS, hres⟩)
  · -- a device region: the free index 0, nothing zeroed
    simp only [↓reduceIte]
    obtain ⟨σD, hD, hhas⟩ := reset_small hk hwf hidx hg hfi0 hp8 hpb hrcb (Or.inl rfl)
    obtain ⟨s2, hs2, cs', hk', hwf', hRR2, -, hco2, hlk2⟩ := spec_exists
      (reset_set_step (L := L) hP hpp' hidx (rel0 σD hD) hnd 0#u64 (by simp))
    obtain ⟨s2', hs2', hE2⟩ := spec_exists (hEk.2 _ (.Untyped p sb 0#u64 true) hE)
    rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
    rw [← hxdef] at hs2 hco2
    simp only [bind_ok]
    rw [hs2]
    simp only [bind_ok]
    have e : cs' = cs := by rw [hcsD σD hD] at hk'; cases hk'; rfl
    subst e
    refine (WP.spec_ok _).2 ⟨hNS, setCnodeSlot σD pp.bv rs cs' idx (.untypedCap true p.bv sb.val 0), 0#u64,
      Or.inl ⟨rfl, rfl, hhas⟩, hRR2, fun h => by simp at h, hco2, hlk2, hE2⟩

end

end Fl4Proofs.P3
