/-
P3 (DESIGN.md §9), VSpace: **the VSpace MDB invariant** `VsMdbInv`:
`VsCapInv` (every VSpace cap of the MDB placed in its ghost set, the sets
existential) and `UtKsOut` (the untyped regions apart from the
kernel-global area), with one step lemma per `MdbStep` constructor (`keep`,
`recap`, `setFi`, `insert`, `nonphys`, `remove`, `rename`, `frameAlias`,
`pool`, `retype`; `trans` is composition).

The step lemmas take the constructors' facts as plain hypotheses (no
reference to `MdbStep`, `CapAlike`, `InsCtx` or `RetypeDelta`), so the
statements survive renames there. Beyond the constructors' facts:
* `recap`, `rename`, `insert`: the new caps well placed when the old ones
  are (`hv`): VSpace caps keep their shape (pointer, size) but the mapping
  fields are the operation's;
* `frameAlias`: the alias 4 KiB aligned and inside the window (`hq2`,
  `hqal`; from `Within` and `CapValid`);
* `pool`: the pool's base (`hb`);
* `retype`: the new caps placed in new ghost sets (`hvc`), and the new
  untyped caps inside the parent's region (`hin`).

The base case (boot) is not done: there is no P3 state relation for boot.
-/
import Fl4Proofs.P3.VsCapOps
import Fl4Proofs.P3.MdbStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- **The VSpace MDB invariant.** -/
def VsMdbInv (ksb : U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  VsCapInv mem G ∧ UtKsOut ksb mem G

/-- The VSpace caps are physical: a non-physical cap is well placed. -/
theorem vcap_nonphys {P L4 L3 L2 L1 : Set U64} {c : capability.Cap} (h : physF c = false) :
    VCapOK P L4 L3 L2 L1 c := by
  cases c <;> simp only [VCapOK] <;> first
    | trivial
    | (rw [show physF _ = true from ok_inj (phys_eq _).symm] at h; cases h)

theorem utOut_nonphys {ksb : U64} {c : capability.Cap} (h : physF c = false) : UtOut ksb c := by
  cases c <;> simp only [UtOut]
  rw [physF_ut] at h; cases h

theorem utOut_of_shape {ksb : U64} {c' c : capability.Cap} (hsh : shape c' = shape c) (h : UtOut ksb c) :
    UtOut ksb c' := by
  cases c' <;> cases c <;> simp_all [shape, UtOut]

theorem utOut_of_ut {ksb : U64} {c' c : capability.Cap}
    (hut : ∀ p sb fi d, c' = .Untyped p sb fi d ↔ c = .Untyped p sb fi d) (h : UtOut ksb c) : UtOut ksb c' := by
  cases hc' : c' with
  | Untyped p sb fi d => rw [hc'] at hut; rw [(hut p sb fi d).1 rfl] at h; exact h
  | _ => simp [UtOut]

section
variable {ksb : U64} {mem mem' : U64 → U64} {G : MdbGhost}

/-- `VsCapsIn` with one slot's cap replaced, the slot possibly outside
the MDB. -/
theorem VsCapsIn.recap' {P L4 L3 L2 L1 : Set U64} (h : VsCapsIn P L4 L3 L2 L1 mem G) (x0 : U64)
    (hv : VCapOK P L4 L3 L2 L1 (capV mem x0) → VCapOK P L4 L3 L2 L1 (capV mem' x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : VsCapsIn P L4 L3 L2 L1 mem' G := by
  intro x hx
  by_cases e : x = x0
  · subst e; exact hv (h x hx)
  · rw [hc x hx e]; exact h x hx

/-- **The invariant from every MDB cap** (the shape a boot proof would
take: the root task's caps placed in the boot ghost sets, the boot untypeds
apart from the kernel-global area). -/
theorem VsMdbInv.intro {P L4 L3 L2 L1 : Set U64}
    (hv : ∀ x ∈ G.chains.flatten, VCapOK P L4 L3 L2 L1 (capV mem x))
    (hu : ∀ x ∈ G.chains.flatten, UtOut ksb (capV mem x)) : VsMdbInv ksb mem G :=
  ⟨⟨P, L4, L3, L2, L1, hv⟩, utKsOut_iff.2 hu⟩

/-- **`keep`**: the MDB's caps kept. -/
theorem VsMdbInv.keep (h : VsMdbInv ksb mem G) (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) :
    VsMdbInv ksb mem' G := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  exact ⟨⟨P, L4, L3, L2, L1, hV.of_caps hc⟩, hU.of_caps hc⟩

/-- **`recap`**: one slot's cap replaced (the same untyped cap if either is
one, well placed when the old one is). -/
theorem VsMdbInv.recap (h : VsMdbInv ksb mem G) (x0 : U64)
    (hut : ∀ p sb fi d, capV mem' x0 = .Untyped p sb fi d ↔ capV mem x0 = .Untyped p sb fi d)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 (capV mem x0) → VCapOK P L4 L3 L2 L1 (capV mem' x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : VsMdbInv ksb mem' G := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  refine ⟨⟨P, L4, L3, L2, L1, hV.recap' x0 (hv _ _ _ _ _) hc⟩, ?_⟩
  rw [utKsOut_iff] at hU ⊢
  intro x hx
  by_cases e : x = x0
  · subst e; exact utOut_of_ut hut (hU x hx)
  · rw [hc x hx e]; exact hU x hx

/-- **`setFi`**: an untyped cap's free index changed. -/
theorem VsMdbInv.setFi (h : VsMdbInv ksb mem G) {x p sb fi f : U64} {d : Bool}
    (hcx : capV mem x = .Untyped p sb fi d) (hcx' : capV mem' x = .Untyped p sb f d)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) : VsMdbInv ksb mem' G := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  refine ⟨⟨P, L4, L3, L2, L1, hV.recap' x (fun _ => by rw [hcx']; trivial) hc⟩, ?_⟩
  rw [utKsOut_iff] at hU ⊢
  intro z hz
  by_cases e : z = x
  · subst e; have := hU z hz; rw [hcx] at this; rw [hcx']; exact this
  · rw [hc z hz e]; exact hU z hz

/-- **`insert`**: a derived cap `c` inserted after `src` (`src`'s cap now
`c1`), both of `src`'s shape and well placed when it is. -/
theorem VsMdbInv.insert (h : VsMdbInv ksb mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    {c c1 : capability.Cap} (hcd : capV mem' dest = c) (hcs : capV mem' src = c1)
    (hsh : shape c = shape (capV mem src)) (hsh1 : shape c1 = shape (capV mem src))
    (hv : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 (capV mem src) → VCapOK P L4 L3 L2 L1 c)
    (hv1 : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 (capV mem src) → VCapOK P L4 L3 L2 L1 c1)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ src → z ≠ dest → capV mem' z = capV mem z) :
    VsMdbInv ksb mem' (insG G src dest b) := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  have hdl : ∀ z ∈ G.chains.flatten, z ≠ dest → z ≠ src → capV mem' z = capV mem z :=
    fun z hz h1 h2 => hc z hz h2 h1
  refine ⟨⟨P, L4, L3, L2, L1, hV.insert hsrc b (by rw [hcd]; exact hv _ _ _ _ _ (hV src hsrc))
    fun z hz hzd hok => ?_⟩, hU.insert hsrc b (by rw [hcd]; exact utOut_of_shape hsh ((utKsOut_iff.1 hU) src hsrc))
    fun z hz hzd hok => ?_⟩
  · by_cases e : z = src
    · subst e; rw [hcs]; exact hv1 _ _ _ _ _ hok
    · rw [hdl z hz hzd e]; exact hok
  · by_cases e : z = src
    · subst e; rw [hcs]; exact utOut_of_shape hsh1 hok
    · rw [hdl z hz hzd e]; exact hok

/-- **`nonphys`**: a non-physical cap inserted, the MDB's caps kept. -/
theorem VsMdbInv.nonphys (h : VsMdbInv ksb mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    {c : capability.Cap} (hcd : capV mem' dest = c) (hcp : physF c = false)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : VsMdbInv ksb mem' (insG G src dest b) := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  refine ⟨⟨P, L4, L3, L2, L1, hV.insert hsrc b (by rw [hcd]; exact vcap_nonphys hcp)
    fun z hz _ hok => by rw [hc z hz]; exact hok⟩,
    hU.insert hsrc b (by rw [hcd]; exact utOut_nonphys hcp) fun z hz _ hok => by rw [hc z hz]; exact hok⟩

/-- **`remove`**: a slot removed from its chain. -/
theorem VsMdbInv.remove {th : TypedHeap} (hM : MdbLinks th mem G) (h : VsMdbInv ksb mem G) (x : U64)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) : VsMdbInv ksb mem' (remG G x) := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  exact ⟨⟨P, L4, L3, L2, L1, hV.remove hM x hc⟩, hU.remove hM x hc⟩

/-- **`rename`**: the slots renamed along `e`, the caps moved alike. -/
theorem VsMdbInv.rename (h : VsMdbInv ksb mem G) (e : U64 ≃ U64)
    (hut : ∀ z ∈ G.chains.flatten, ∀ p sb fi d,
      capV mem' (e z) = .Untyped p sb fi d ↔ capV mem z = .Untyped p sb fi d)
    (hv : ∀ z ∈ G.chains.flatten, ∀ P L4 L3 L2 L1 : Set U64,
      VCapOK P L4 L3 L2 L1 (capV mem z) → VCapOK P L4 L3 L2 L1 (capV mem' (e z))) :
    VsMdbInv ksb mem' (renG G e) := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  refine ⟨⟨P, L4, L3, L2, L1, fun x hx => ?_⟩, ?_⟩
  · have hx0 := (mem_renG e x).1 hx
    have := hv _ hx0 P L4 L3 L2 L1 (hV _ hx0)
    rwa [Equiv.apply_symm_apply] at this
  · rw [utKsOut_iff] at hU ⊢
    intro x hx
    have hx0 := (mem_renG e x).1 hx
    have := utOut_of_ut (hut _ hx0) (hU _ hx0)
    rwa [Equiv.apply_symm_apply] at this

/-- **`frameAlias`**: a 4 KiB alias of a page of `src`'s well-placed large
RAM frame, inside the window and 4 KiB aligned. -/
theorem VsMdbInv.frameAlias (h : VsMdbInv ksb mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    {ptr rt fa fv q0 vm : U64} {mm : Bool} (hsC : capV mem src = .Frame ptr .Large rt false mm false fa fv)
    (hcd : capV mem' dest = .Frame q0 .Small vm false false false 0#u64 0#u64)
    (hq1 : ptr.val ≤ q0.val) (hq2 : q0.val + 4096 ≤ ptr.val + 2 ^ 21) (hqal : q0.val % 4096 = 0)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : VsMdbInv ksb mem' (insG G src dest b) := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  have hs := hV src hsrc
  rw [hsC] at hs
  refine ⟨⟨P, L4, L3, L2, L1, hV.insert hsrc b (by rw [hcd]; exact vcap_alias hs hq1 hq2 hqal)
    fun z hz _ hok => by rw [hc z hz]; exact hok⟩,
    hU.insert hsrc b (by rw [hcd]; trivial) fun z hz _ hok => by rw [hc z hz]; exact hok⟩

/-- **`pool`**: an ASID pool cap inserted after an untyped cap; the pool
set grown by its pool. -/
theorem VsMdbInv.pool (h : VsMdbInv ksb mem G) {x val q bs : U64} (hx : x ∈ G.chains.flatten)
    (hcf : capV mem' val = .AsidPool q bs) (hb : bs.val % 512 = 0 ∧ bs.val < 2 ^ 20 ∧ q ≠ 0#u64)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : VsMdbInv ksb mem' (insG G x val true) := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  refine ⟨⟨Insert.insert q P, L4, L3, L2, L1, hV.insert_fresh (Set.subset_insert _ _) subset_rfl subset_rfl subset_rfl
    subset_rfl hx true (by rw [hcf]; exact ⟨⟨Set.mem_insert _ _, hb.2.2⟩, hb.1, hb.2.1⟩) (by rw [hc x hx]; exact id)
    fun z hz _ _ => hc z hz⟩,
    hU.insert hx true (by rw [hcf]; trivial) fun z hz _ hok => by rw [hc z hz]; exact hok⟩

/-- **`retype`**: the source untyped cap's free index changed, the new caps
`cj j` in new slots, well placed in new ghost sets (unioned with the old),
the new untyped caps inside the source's region. -/
theorem VsMdbInv.retype {mem0 memf : U64 → U64} {G0 Gf : MdbGhost} (h : VsMdbInv ksb mem0 G0)
    {src p sb fi nfi : U64} {dev : Bool} {w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hsrc : src ∈ G0.chains.flatten) (hcs : capV mem0 src = .Untyped p sb fi dev) (hcsf : capV memf src = .Untyped p sb nfi dev)
    (hold : ∀ x ∈ G0.chains.flatten, x ≠ src → capV memf x = capV mem0 x)
    (hF1 : ∀ x ∈ Gf.chains.flatten, x ∈ G0.chains.flatten ∨ ∃ j, j < w ∧ x = dslot j)
    (hnew : ∀ j, j < w → capV memf (dslot j) = cj j)
    {Pn L4n L3n L2n L1n : Set U64} (hvc : ∀ j, j < w → VCapOK Pn L4n L3n L2n L1n (cj j))
    (hin : ∀ j, j < w → ∀ q us f d, cj j = .Untyped q us f d → p.val ≤ q.val ∧ q.val + 2 ^ us.val ≤ p.val + 2 ^ sb.val) :
    VsMdbInv ksb memf Gf := by
  obtain ⟨⟨P, L4, L3, L2, L1, hV⟩, hU⟩ := h
  rw [utKsOut_iff] at hU
  refine ⟨⟨P ∪ Pn, L4 ∪ L4n, L3 ∪ L3n, L2 ∪ L2n, L1 ∪ L1n, fun x hx => ?_⟩, utKsOut_iff.2 fun x hx => ?_⟩
  · rcases hF1 x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases e : x = src
      · subst e; rw [hcsf]; trivial
      · rw [hold x hx0 e]
        exact (hV x hx0).mono Set.subset_union_left Set.subset_union_left Set.subset_union_left
          Set.subset_union_left Set.subset_union_left
    · rw [hnew j hj]
      exact (hvc j hj).mono Set.subset_union_right Set.subset_union_right Set.subset_union_right
        Set.subset_union_right Set.subset_union_right
  · rcases hF1 x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases e : x = src
      · subst e; rw [hcsf]; have := hU x hx0; rw [hcs] at this; exact this
      · rw [hold x hx0 e]; exact hU x hx0
    · rw [hnew j hj]
      cases hcj : cj j with
      | Untyped q us f d =>
        obtain ⟨h1, h2⟩ := hin j hj q us f d hcj
        have := hU src hsrc; rw [hcs] at this
        exact utOut_within this h1 h2
      | _ => simp [UtOut]

end


/-! ## The remaps -/

section
variable {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} {x : U64} {c : capability.Cap}

theorem slotFoot_capV (hM : MdbLinks th m G) (hF : SlotFoot th m m' x) :
    ∀ z ∈ G.chains.flatten, z ≠ x → capV m' z = capV m z := fun z hz hne => by
  have hzs := ((hM.members z).1 hz).1
  unfold capV; rw [((hF z hzs).2.2 hne).1, ((hF z hzs).2.2 hne).2]

theorem slotFoot_revOf (hM : MdbLinks th m G) (hF : SlotFoot th m m' x) :
    ∀ z ∈ G.chains.flatten, revOf m' z = revOf m z := fun z hz => by
  have hzs := ((hM.members z).1 hz).1
  unfold revOf; rw [(hF z hzs).2.1]

/-- **A remap as an MDB step** (`MdbStep.recap`): one slot's non-untyped cap
replaced by an `MdbLike` one, `SlotFoot`. -/
theorem mstep_remap (hM : MdbLinks th m G) (hF : SlotFoot th m m' x) (hcx : capAt m x = ok c)
    (hL : VsLike (capV m' x) c) (hu : isUt c = false) : MdbStep m G m' G := by
  have hcv : capV m x = c := capV_of_capAt hcx
  refine MdbStep.recap hM x ?_ (fun P L4 L3 L2 L1 hv => hL.2 P L4 L3 L2 L1 (hcv ▸ hv))
    (slotFoot_capV hM hF) (slotFoot_revOf hM hF)
  rw [hcv]
  exact CapAlike.of_shape hL.1.1 hL.1.2.1 (fun h => by rw [hu] at h; cases h)

/-- **A remap keeps the VSpace MDB invariant** (`VsMdbInv.recap`). -/
theorem VsMdbInv.remap {ksb : U64} (h : VsMdbInv ksb m G) (hM : MdbLinks th m G) (hF : SlotFoot th m m' x)
    (hcx : capAt m x = ok c) (hL : VsLike (capV m' x) c) (hu : isUt c = false) : VsMdbInv ksb m' G := by
  have hcv : capV m x = c := capV_of_capAt hcx
  have ha := CapAlike.of_shape (c' := capV m' x) (c := c) hL.1.1 hL.1.2.1 (fun h => by rw [hu] at h; cases h)
  refine h.recap x (fun p sb fi d => by rw [hcv]; exact ha.ut p sb fi d) (fun P L4 L3 L2 L1 hv => ?_)
    (slotFoot_capV hM hF)
  rw [hcv] at hv; exact hL.2 _ _ _ _ _ hv

end

end

end Fl4Proofs.P3.Vs
