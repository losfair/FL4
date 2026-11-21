/-
P3 (DESIGN.md §9), untyped: **`LiveDN` after a retype that creates no
container** (KENTRY-PLAN g2j; the retype sites of `JAtZ.add_frame` /
`add_frameB` supply `JAtZ.live` / `JAtZ.zD` after from here).

* `createCap_cdt`, `cdt_mapMx_createCap`, `invokeUntyped_cdt_slots`: every
  destination slot of the spec's `invoke_untyped` retype has the source slot
  as its CDT parent after (`create_cap`'s `set_cdt`; the later `create_cap`s
  write other slots' CDT entries only, the destinations distinct).
* `tcbs_hout`: P1's heap after a creation of no TCB (`HOut` over the window,
  no TCB of `H` meeting it) has the same TCBs.
* `not_newQ_of_off`: an object off the window is no new object.
* `JAtZ.ret_liveN`: `LiveDN` and `zD` after the retype, from LiveFrame's
  `LiveDN.wstepR` (the window's slots written into the destination CNode,
  named by a CNode cap; the source untyped cap's free index changed, a
  `shape`-preserving change; every other slot kept): the window's slots are
  non-null after (their CDT parent the source, so MDB members, `CdtRel`), and
  hold no zombie (the new caps, `RetExp.gmem` / `newc`); the debug lists'
  TCBs are the same (`tcbs_hout`), so `DbgWF` after is `dbgWFL_step`'s.
-/
import Fl4Proofs.P3.UtEpSets
import Fl4Proofs.P3.UtEpJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc Fl4Proofs.P1

noncomputable section

/-! ## The spec: the destinations' CDT parent -/

section Spec
open Fl4Spec

/-- `create_cap` sets its destination's CDT parent to the untyped slot. -/
theorem createCap_cdt (t : ApiObjectType) (bits : Nat) (u : CslotPtr) (dev : Bool) (dst : CslotPtr) (o : ObjRef)
    (σ : State Unit) : ∀ y ∈ (createCap (Z := Unit) t bits u dev (dst, o) σ).1, y.2.cdt dst = some u := by
  unfold createCap
  rintro y ⟨y1, hy1, hy⟩
  rw [Set.mem_singleton_iff.1 hy1] at hy
  obtain ⟨y2, hy2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy2] at hy
  obtain ⟨y3, hy3, hy⟩ := hy
  have h3 : y3.2.cdt dst = some u := by
    unfold setCdt at hy3
    obtain ⟨y4, hy4, hy3⟩ := hy3
    rw [Set.mem_singleton_iff.1 hy4] at hy3
    rw [Set.mem_singleton_iff.1 hy3]
    simp
  have hk := (ncd_bind (d := fun sl => sl ≠ dst) (ncd_doExtendedOp _)
    (fun _ => ncd_bind (ncd_setOriginal _ _) (fun _ => ncd_setCap _ _))) y3.2 y hy
  rw [hk dst (fun h => h rfl)]
  exact h3

/-- **`mapM_x create_cap`**: each destination's CDT parent is the untyped slot
after (a later `create_cap` at the same destination sets the same parent). -/
theorem cdt_mapMx_createCap (t : ApiObjectType) (bits : Nat) (u : CslotPtr) (dev : Bool) :
    ∀ (l : List (CslotPtr × ObjRef)) σ y,
      y ∈ (NonDet.mapMx (createCap (Z := Unit) t bits u dev) l σ).1 → ∀ a ∈ l, y.2.cdt a.1 = some u := by
  intro l
  induction l with
  | nil => intro _ _ _ a ha; simp at ha
  | cons a l ih =>
    intro σ y hy b hb
    obtain ⟨x, hx, hy⟩ := hy
    by_cases hbl : ∃ c ∈ l, c.1 = b.1
    · obtain ⟨c, hc, e⟩ := hbl
      rw [← e]; exact ih x.2 y hy c hc
    rcases List.mem_cons.1 hb with rfl | hb
    · have hk := ncd_mapMx_mem (d := (· ∈ l.map Prod.fst)) l
        (fun c hc => ncd_createCap t bits u dev c (List.mem_map_of_mem hc)) x.2 y hy
      rw [hk b.1 (fun h => hbl (by obtain ⟨c, hc, e⟩ := List.mem_map.1 h; exact ⟨c, hc, e⟩))]
      obtain ⟨d0, o0⟩ := b
      exact createCap_cdt t bits u dev d0 o0 σ x hx
    · exact absurd ⟨b, hb, rfl⟩ hbl

/-- **The spec's retype: every destination's CDT parent is the source slot
after** (module docstring), on its `Ok` outcomes. -/
theorem invokeUntyped_cdt_slots (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (rs : Bool)
    (pb rb : ObjRef) (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool)
    (σ : State Unit) :
    NAll (invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ
      (fun y => y.1 = .ok () → ∀ d ∈ slots, y.2.cdt d = some sl) := by
  unfold invokeUntypedWith
  apply nallE_bind
  intro x _
  rcases x with ⟨e | u, σr⟩
  · intro h; cases h
  dsimp only
  apply nall_liftE
  apply nall_bind; intro x1 _
  apply nall_bind; intro x2 _
  apply nall_bind; intro x3 _
  apply nall_bind; intro x4 _
  apply nall_bind
  refine nall_det (retypeRegionWith_eq bitsApi rb slots.length us t dev x4.2) ?_
  apply nall_bind; intro x5 _
  intro y hy _ d hd
  have hz : ((slots.zip (regionPtrs rb slots.length (2 ^ bitsApi t us))).map Prod.fst) = slots := by
    rw [List.map_fst_zip]; simp [regionPtrs]
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ slots.zip (regionPtrs rb slots.length (2 ^ bitsApi t us)), a.1 = d := by
    rw [← hz] at hd; exact List.mem_map.1 hd
  exact cdt_mapMx_createCap t us sl dev _ x5.2 y hy a ha

end Spec

/-! ## P1's heap after a creation of no TCB -/

section
variable {H H' : Heap} {A k w : Nat} {K : Option HKind}

theorem tcbs_hout (h : HOut H H' A (A + w * k) A k w K) (hK : K ≠ some .tcb) (hk : 1 ≤ k)
    (hT : ∀ q, H q = some .tcb → q.val + 4096 ≤ A ∨ A + w * k ≤ q.val) : H'.tcbs = H.tcbs := by
  ext q
  simp only [Heap.tcbs, Set.mem_setOf_eq]
  rw [h q]
  constructor
  · intro h1
    by_cases c1 : NewAt A k w q ∧ K.isSome
    · rw [if_pos c1] at h1; exact absurd h1 hK
    rw [if_neg c1] at h1
    by_cases c2 : ∃ kd, H q = some kd ∧ MeetsR A (A + w * k) q.val (q.val + 2 ^ kd.bits)
    · rw [if_pos c2] at h1; cases h1
    · rw [if_neg c2] at h1; exact h1
  · intro h1
    have hb := hT q h1
    rw [if_neg (fun ⟨hn, _⟩ => by have := newAt_bd hk hn; omega), if_neg, h1]
    rintro ⟨kd, hq, hm⟩
    rw [h1] at hq; cases hq
    unfold MeetsR at hm
    simp only [HKind.bits] at hm
    omega

theorem newKind_ne_tcb {n us : Nat} (h : n ≠ 1) : newKind n us ≠ some .tcb := by
  intro e
  unfold newKind at e
  rw [if_neg h] at e
  split_ifs at e <;> simp_all

theorem not_newQ_of_off {cj : Nat → capability.Cap} {q : U64} (hk : 1 ≤ k) (h : q.val + 4096 ≤ A ∨ A + w * k ≤ q.val) :
    ¬ NewQ A k w cj q := by
  rintro ⟨j, hj, e, -⟩
  have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

end

/-! ## A typed heap grown by objects whose slots are empty -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem isSlotAt_old {th th' : TypedHeap} (hold : ∀ q k, th q = some k → th' q = some k) {q : U64} {i : Nat}
    (hq : th q ≠ none) (h : IsSlotAt th' q i) : IsSlotAt th q i := by
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hq
  have e := hold q k hk
  unfold IsSlotAt at h ⊢
  rw [e] at h; rw [hk]; exact h

theorem isSlotAt_grow {th th' : TypedHeap} (hold : ∀ q k, th q = some k → th' q = some k) {q : U64} {i : Nat}
    (h : IsSlotAt th q i) : IsSlotAt th' q i := by
  rcases h with ⟨r, hr, hi⟩ | ⟨ht, hi⟩
  · exact Or.inl ⟨r, hold q _ hr, hi⟩
  · exact Or.inr ⟨hold q _ ht, hi⟩

/-- The new objects' slots: empty and not original. -/
def NewEmpty (th th' : TypedHeap) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ q, th q = none → ∀ i, IsSlotAt th' q i →
    capV m (slotOf q i) = .Null ∧ ∀ x, cslotAddr x = slotOf q i → σ.isOriginalCap x = false

theorem NewEmpty.isSlot {th th' : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit}
    (h : NewEmpty th th' m σ) (hold : ∀ q k, th q = some k → th' q = some k) {y : U64} (hy : IsSlot th' y)
    (hn : capV m y ≠ .Null) : IsSlot th y := by
  obtain ⟨q, i, hqi, rfl⟩ := hy
  by_cases hq : th q = none
  · exact absurd (h q hq i hqi).1 hn
  · exact ⟨q, i, isSlotAt_old hold hq hqi, rfl⟩

theorem NewEmpty.refl (th : TypedHeap) (m : U64 → U64) (σ : Fl4Spec.State Unit) : NewEmpty th th m σ :=
  fun q hq i hqi => by
    exfalso
    rcases hqi with ⟨r, hr, -⟩ | ⟨hr, -⟩ <;> rw [hq] at hr <;> cases hr

/-- A spec slot at a new object's slot is no slot of the smaller heap. -/
theorem not_absSlot_new {th th' : TypedHeap} (hP' : Placed th') (hold : ∀ q k, th q = some k → th' q = some k)
    {q : U64} {i : Nat} (hq : th q = none) (hqi : IsSlotAt th' q i) {x : Fl4Spec.CslotPtr}
    (hx : cslotAddr x = slotOf q i) : ¬ AbsSlot th x := fun hA => by
  obtain ⟨p, j, hpj, -, he⟩ := hA.at
  obtain ⟨e, -⟩ := slotOf_inj hP' (isSlotAt_grow hold hpj) hqi (he.symm.trans hx)
  subst e
  rcases hpj with ⟨r, hr, -⟩ | ⟨hr, -⟩ <;> rw [hq] at hr <;> cases hr

/-- **`MdbLinks` at the smaller heap** (the new slots empty, so no member). -/
theorem MdbLinks.restrictE {th th' : TypedHeap} {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit}
    (hM : MdbLinks th' m G) (hold : ∀ q k, th q = some k → th' q = some k) (hE : NewEmpty th th' m σ) :
    MdbLinks th m G := by
  refine ⟨hM.tree, hM.ne_nil, hM.chain, hM.head, hM.last, fun a => ?_⟩
  rw [hM.members a]
  constructor
  · rintro ⟨hy, c, hc, hn⟩
    exact ⟨hE.isSlot hold hy (by rw [capV_of_capAt hc]; exact hn), c, hc, hn⟩
  · rintro ⟨⟨q, i, hqi, rfl⟩, c, hc, hn⟩
    exact ⟨⟨q, i, isSlotAt_grow hold hqi, rfl⟩, c, hc, hn⟩

/-- **`LiveDN` at a typed heap grown by objects whose slots are empty** (the
new slots in no use; no zombie in them). -/
theorem LiveDN.extendE {th th' : TypedHeap} {H : P1.Heap} {Cs : Set U64} {G : MdbGhost} {s : S}
    {σ : Fl4Spec.State Unit} (hL : LiveDN (L := L) th H Cs G s σ)
    (hold : ∀ q k, th q = some k → th' q = some k) (hE : NewEmpty th th' (L.mem s) σ) :
    LiveDN (L := L) th' H Cs G s σ := by
  obtain ⟨hLJ, hDW, hN⟩ := hL
  have hnu : ∀ q, th q = none → ∀ i, IsSlotAt th' q i → ¬ InUse (L.mem s) σ (slotOf q i) := by
    rintro q hq i hqi (hu | ⟨x, hx, ho⟩)
    · exact hu (hE q hq i hqi).1
    · rw [(hE q hq i hqi).2 x hx] at ho; cases ho
  have hzold : ∀ y, IsSlot th' y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n → IsSlot th y :=
    fun y hy p zt n hz => hE.isSlot hold hy (by rw [hz]; exact fun h => by cases h)
  refine ⟨⟨fun q i hqi hu => ?_, hLJ.dbg, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => hLJ.zdead y (hzold y hy p zt n hz) p zt n hz hzt⟩, hDW, fun sl hA h => ?_⟩
  · by_cases hq : th q = none
    · exact absurd hu (hnu q hq i hqi)
    · exact hLJ.slots q i (isSlotAt_old hold hq hqi) hu
  · by_cases hp : th p = none
    · exact hnu p hp i hpi hu
    · exact hLJ.zslots y (hzold y hy p zt n hz) p zt n hz i (isSlotAt_old hold hp hpi) hni hu
  · obtain ⟨p, i, hpi, h1, hxe⟩ := hA.at
    by_cases hp : th p = none
    · exact (hE p hp i hpi).2 sl hxe
    · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hp
      have e := hold p k hk
      obtain ⟨p', h1', h2⟩ := hA
      have hpp : p' = p := P1.eq_of_bv (h1'.symm.trans h1)
      subst hpp
      refine hN sl ⟨p', h1', ?_⟩ h
      rw [hk]; rw [e] at h2; exact h2

/-- `ZTcb` at the grown heap (the new slots empty). -/
theorem ZTcb.of_extendE {th th' : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    (hold : ∀ q k, th q = some k → th' q = some k) (hE : NewEmpty th th' (L.mem s) σ) {p : U64}
    (hp : p ∈ ZTcb (L := L) th' s) : p ∈ ZTcb (L := L) th s := by
  obtain ⟨y, hy, zt, n, hz, h65⟩ := hp
  exact ⟨y, hE.isSlot hold hy (by rw [hz]; exact fun h => by cases h), zt, n, hz, h65⟩

end

/-! ## `LiveDN` after the retype -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} {arI : machine.Arch A'}
variable {AR : A' → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`LiveDN` and `zD` after a retype creating no container** (module
docstring). -/
theorem JAtZ.ret_liveN {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {a' : A'} {σ' : Fl4Spec.State Unit} {D' : Set U64}
    {th' : TypedHeap} (hX' : XTopAt (L := L) AR Z' s' a' σ') (hth : Z'.th = th') (hT : Z'.T = Z.T) (hc : Z'.c = Z.c)
    (hold : ∀ q k, Z.th q = some k → th' q = some k) (hNE : NewEmpty Z.th th' (L.mem s') σ')
    (hTH : P1.Heap.tcbs H' = P1.Heap.tcbs H)
    (hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s')
    (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H' s' p)
    (hnew : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D')
    (hid : σ'.idleThread = σ.idleThread)
    {Aw k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G Z'.G Aw k w dslot cj xs)
    (hcjZ : ∀ j, j < w → ∀ p zt n, cj j ≠ .Zombie p zt n)
    (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧ sl.2.length = r ∧ DestCap Z.th (L.mem s) p)
    (hxs : IsSlot Z.th xs)
    (hcapK : ∀ y, IsSlot Z.th y → y ≠ xs → (∀ d ∈ W, y ≠ cslotAddr d) → capV (L.mem s') y = capV (L.mem s) y)
    (hWn : ∀ d ∈ W, capV (L.mem s) (cslotAddr d) = .Null)
    {src : Fl4Spec.CslotPtr} (hcdt : ∀ d ∈ W, σ'.cdt d = some src)
    (horgK : ∀ sl, sl ∉ W → σ'.isOriginalCap sl = σ.isOriginalCap sl) :
    LiveDN (L := L) Z'.th H' Cs Z'.G s' σ' ∧ ∀ p ∈ ZTcb (L := L) Z'.th s', p ∈ D' := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := J.live
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hM := J.xtop.rel.2.1.2.2.1
  have hM'' : MdbLinks th' (L.mem s') Z'.G := by rw [← hth]; exact hX'.rel.2.1.2.2.1
  have hM' : MdbLinks Z.th (L.mem s') Z'.G := hM''.restrictE hold hNE
  have hC' : CdtRel th' (L.mem s') σ' Z'.G := by rw [← hth]; exact hX'.rel.2.1.2.2.2.1
  have hDW' : DbgWF (P1.Heap.tcbs H') Cs (L.mem s') (dbgHd (L := L) s') :=
    ⟨lst, by rw [hTH]; exact dbgWFL_step J.xtop hX' hT hc hTe hDW hdk⟩
  -- the source cap: an untyped cap, its region kept
  obtain ⟨-, p0, sb0, fi0, fi1, d0, hs0, hs1, -⟩ := hE.usrc
  have hxW : ∀ d ∈ W, xs ≠ cslotAddr d := fun d hd e => by
    have := hWn d hd; rw [← e, hs0] at this; cases this
  -- the window's slots after: MDB members (their CDT parent), new caps
  have hWG : ∀ d ∈ W, cslotAddr d ∈ Z'.G.chains.flatten := fun d hd => by
    obtain ⟨p, r, h1, hp, hl, -⟩ := hW d hd
    have hA : AbsSlot th' d := ⟨p, h1, Or.inl (by rw [hl]; exact hold _ _ hp)⟩
    have e := hC'.cdt d hA
    rw [hcdt d hd] at e
    exact (hM'.tree.par_mem _ _ e.symm).1
  have hWc : ∀ d ∈ W, capV (L.mem s') (cslotAddr d) ≠ .Null ∧
      ∀ p zt n, capV (L.mem s') (cslotAddr d) ≠ .Zombie p zt n := fun d hd => by
    have hm := hWG d hd
    refine ⟨fun h0 => ?_, fun p zt n hz => ?_⟩
    · obtain ⟨-, c0, h1, hn⟩ := (hM'.members _).1 hm
      rw [capV_of_capAt h1] at h0; exact hn h0
    · rcases hE.gmem _ hm with h0 | ⟨j, hj, ej⟩
      · obtain ⟨-, c0, h1, hn⟩ := (hM.members _).1 h0
        have := hWn d hd; rw [capV_of_capAt h1] at this; exact hn this
      · rw [ej, hE.newc j hj] at hz; exact hcjZ j hj p zt n hz
  have hZf : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n := fun y hy p zt n h => by
    by_cases ex : y = xs
    · rw [ex, hs1] at h; cases h
    by_cases eW : ∃ d ∈ W, y = cslotAddr d
    · obtain ⟨d, hd, rfl⟩ := eW; exact absurd h ((hWc d hd).2 p zt n)
    · push_neg at eW
      exact ⟨y, hy, by rw [← hcapK y hy ex eW]; exact h⟩
  have hLv := LiveDN.wstepR J ⟨hL, ⟨lst, hDW⟩, hN⟩ hM' hDW' hdead hid hdk W hW
    (fun y hy hne => by
      by_cases ex : y = xs
      · rw [ex, hs0, hs1]; exact LSim.of_shape rfl
      · rw [hcapK y hy ex hne]; exact LSim.rfl' _)
    (fun sl h => by
      by_cases hs : sl ∈ W
      · exact Or.inr hs
      · exact Or.inl (by rw [← horgK sl hs]; exact h))
    (fun sl hsl h => absurd h (hWc sl hsl).1)
    hZf
    (fun y0 hy0 hn => by
      by_cases eW : ∃ d ∈ W, y0 = cslotAddr d
      · obtain ⟨d, hd, rfl⟩ := eW; exact absurd (hWn d hd) hn
      push_neg at eW
      by_cases ex : y0 = xs
      · rw [ex]
        exact ⟨xs, hxs, (by rw [hs1]; exact fun h => by cases h), (by rw [hs0, hs1]; rfl)⟩
      · exact ⟨y0, hy0, by rw [hcapK y0 hy0 ex eW]; exact hn, by rw [hcapK y0 hy0 ex eW]⟩)
  rw [hth]
  exact ⟨hLv.extendE hold hNE, fun p hp => hnew p (ZTcb.of_zombies hZf (ZTcb.of_extendE hold hNE hp))⟩

end

end

end Fl4Proofs.P3
