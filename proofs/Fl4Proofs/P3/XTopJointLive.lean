/-
P3 (DESIGN.md §9), CSpace: **the liveness invariant of FL4's caps at `J`**
(`LiveJ`), behind the deletion's slot readiness: carried through the
deletion loop by `WJL` (XTopJointWJL) from XTopJointEntry's `JEntryAt.live`.

* `RefsObj q c`: the cap `c` names the CNode or TCB `q` as a container (a
  CNode cap, a thread cap or a zombie to it; l4v `obj_refs` / `zobj_refs`).
* `InUse m σ y`: the slot `y` holds a cap or an original bit.
* `dbgNth m n h`: the `n`-th TCB of the debug list from `h` (`0` past its end).
* `LiveJ th H G s σ` [J], on a `JAtZ` state, in four parts:
  - `slots`: the container of a slot in use is named by a cap of the MDB,
    or the slot lies in the kernel-state block (`KsSlot`: the IRQ node's
    one-slot CNodes, which no cap names; l4v `if_unsafe_then_cap`:
    `cte_wp_at ((≠) NullCap) p s → ex_cte_cap_wp_to (appropriate_cte_cap) p s`,
    where an IRQ node slot is covered by the IRQ state / handler cap, not a
    CNode cap; KENTRY-PLAN g2d/g2e: `SetIRQHandler` fills such a slot);
  - `dbg`: a TCB on core 0's debug list other than the spec's idle thread is
    named by a thread cap of the MDB (FL4's debug list holds the TCBs not yet
    finalised, and the idle threads since boot, `init_core_state` under
    `DEBUG_BUILD`; l4v `if_live_then_nonz_cap` for a live TCB, the idle
    thread exempt as not `live`; at a `JAtZ` state the spec's idle thread is
    the idle word, `JAtZ.idleThread_bv`);
  - `zslots`: a zombie of count `n` leaves its object's slots from `n` on
    unused (l4v: `rec_del` deletes a zombie's slots from the last, the count
    the number not yet deleted; `zombies_final`, `cap_removeable`);
  - `zdead`: a TCB zombie's TCB is dead (`DeadP`; l4v: `finalise_cap` of a
    thread cap leaves it not `live`, and nothing names it after).
  `LiveJ` reads the state, the MDB ghost and `H` only (no dead set), so that
  it can later become a field of `JAtZ`.
* `ReadyLive th s σ G x`: the readiness the emptied slot `x` adds to
  `EmptyReady`: every other slot in use, and core 0's debug-list head unless
  it is the idle word, live without `x` (`SlotLiveAt`, `OtherCov`; what
  `DelUtFact` after reads, XTopJointEmptyUt, the idle head by `JCovD.idleOut`).
* `JAtZ.ref_cover`: a cap naming a container covers each of its slots.
* `JAtZ.readyLive`: `ReadyLive` at `x` from `LiveJ`, when every cap at `x`
  naming a container in use, or a thread on the debug list, has another such
  cap elsewhere; `readyLive_noRef` (`x`'s cap names no container),
  `readyLive_key` (another cap alike `x`'s: a non-final cap, `other_keyN`),
  `readyLive_zombie` (a removable zombie: its slots unused, `zslots`).
-/
import Fl4Proofs.P3.XTopJointZombie
import Fl4Proofs.P3.XTopJointEmptyUt
import Fl4Proofs.P3.XTopJointFinThread
import Fl4Proofs.P3.XTopJointDelLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The emptied slot's liveness readiness** (module docstring). -/
def ReadyLive (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (x : U64) : Prop :=
  (∀ y, IsSlot th y → y ≠ x → InUse (L.mem s) σ y → SlotLiveAt (L.mem s) G (L.ksb s) x y) ∧
  (dbgHead (L := L) s ≠ 0#u64 → dbgHead (L := L) s ≠ L.idleW s →
    OtherCov (L.mem s) G x (dbgHead (L := L) s).val ((dbgHead (L := L) s).val + 1))

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The spec's idle thread is the idle word at `J`** (XTopJointDelR's
`JAtZ.idleThread_eq`, here for XTopJointLive's readers). -/
theorem JAtZ.idleThread_bv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    σ.idleThread = (L.idleW s).bv := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  unfold P1.LawfulStore.idleW
  have h2 := hs.idleTh
  unfold nodeW at h2
  rw [hc.cur, ← h2]

/-- A word other than the idle word is not the spec's idle thread. -/
theorem JAtZ.bv_ne_idleThread (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {w : U64} (h : w ≠ L.idleW s) :
    w.bv ≠ σ.idleThread := fun e => h (P1.eq_of_bv (e.trans J.idleThread_bv))

/-- **A cap naming a container covers each of its slots.** -/
theorem JAtZ.ref_cover (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y : U64}
    (hy : y ∈ Z.G.chains.flatten) {q : U64} (hr : RefsObj q (capV (L.mem s) y)) {i : Nat}
    (hqi : IsSlotAt Z.th q i) :
    physF (capV (L.mem s) y) = true ∧ isUt (capV (L.mem s) y) = false ∧
      baseF (capV (L.mem s) y) ≤ (slotOf q i).val ∧ (slotOf q i).val + 1 ≤ topF (capV (L.mem s) y) + 1 := by
  have hP := J.xtop.rel.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hys : IsSlot Z.th y := ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  obtain ⟨sl, hA, rfl⟩ := hys.abs
  have hcv : CapValid Z.th (capV (L.mem s) (cslotAddr sl)) := J.xtop.rel.2.1.2.1.abs hA (capAt_capV _ _)
  have hzw := J.del.zwf (cslotAddr sl) hA.isSlot
  have hv : (slotOf q i).val = q.val + 32 * i := hqi.val hP
  obtain ⟨k, hk, hs⟩ := hqi.size
  generalize hc : capV (L.mem s) (cslotAddr sl) = c at hr hcv hzw ⊢
  have hph : ∀ c : capability.Cap, (∃ p r gs g, c = .CNode p r gs g) ∨ (∃ p, c = .Thread p) ∨
      (∃ p zt n, c = .Zombie p zt n) → physF c = true := by
    rintro c (⟨p, r, gs, g, rfl⟩ | ⟨p, rfl⟩ | ⟨p, zt, n, rfl⟩) <;> exact ok_inj (phys_eq _).symm
  -- the TCB case, for thread caps and TCB zombies
  have tcbCase : ∀ c : capability.Cap, (c = .Thread q ∨ ∃ n, c = .Zombie q capability.ZOMBIE_TCB n) →
      Z.th q = some .tcb → physF c = true ∧ isUt c = false ∧ baseF c ≤ (slotOf q i).val ∧
        (slotOf q i).val + 1 ≤ topF c + 1 := by
    intro c hc' hth
    rw [hth] at hk; cases hk
    have hHq : H q = some .tcb := (hJ.tcb q).1 hth
    obtain ⟨r1, r2⟩ := range_thread q (J.kern.heap.fits q _ hHq)
    have h1 : 1 ≤ 2 ^ 12 := Nat.one_le_two_pow
    simp only [objSize] at hs
    have e12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    rcases hc' with rfl | ⟨n, rfl⟩
    · exact ⟨hph _ (Or.inr (Or.inl ⟨q, rfl⟩)), rfl, by rw [r1]; omega, by rw [r2]; omega⟩
    · have al : CapAlike (.Zombie q capability.ZOMBIE_TCB n) (.Thread q) := capAlike_zombie_thread
      exact ⟨hph _ (Or.inr (Or.inr ⟨_, _, _, rfl⟩)), rfl, by rw [al.base, r1]; omega, by rw [al.top, r2]; omega⟩
  -- the CNode case, for CNode caps and CNode zombies
  have cnCase : ∀ (c : capability.Cap) (r : U64), (∃ gs g, c = .CNode q r gs g) ∨ (∃ n, c = .Zombie q r n) →
      Z.th q = some (.cnode r.val) → physF c = true ∧ isUt c = false ∧ baseF c ≤ (slotOf q i).val ∧
        (slotOf q i).val + 1 ≤ topF c + 1 := by
    intro c r hc' hth
    rw [hth] at hk; cases hk
    have hHq : H q = some (.other (r.val + 5)) := hJ.cnode q r.val hth
    have hlt : r.val + 5 < 64 := J.kern.heap.lt64 q _ hHq
    have hne : r ≠ capability.ZOMBIE_TCB := fun e => by rw [e, zombie_tcb_val] at hlt; omega
    obtain ⟨r1, r2⟩ := range_zombieCn q r 0#u64 hne hlt (J.kern.heap.fits q _ hHq)
    have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
    have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
    simp only [objSize] at hs
    rcases hc' with ⟨gs, g, rfl⟩ | ⟨n, rfl⟩
    · have al : CapAlike (.Zombie q r 0#u64) (.CNode q r gs g) := capAlike_zombie_cnode hne
      exact ⟨hph _ (Or.inl ⟨_, _, _, _, rfl⟩), rfl, by rw [← al.base, r1]; omega, by rw [← al.top, r2]; omega⟩
    · have al : CapAlike (.Zombie q r n) (.Zombie q r 0#u64) := capAlike_zombie_zombie
      exact ⟨hph _ (Or.inr (Or.inr ⟨_, _, _, rfl⟩)), rfl, by rw [al.base, r1]; omega, by rw [al.top, r2]; omega⟩
  cases c with
  | CNode p r gs g =>
    simp only [RefsObj] at hr; subst hr
    exact cnCase _ r (Or.inl ⟨gs, g, rfl⟩) hcv.1
  | Thread p =>
    simp only [RefsObj] at hr; subst hr
    exact tcbCase _ (Or.inl rfl) hcv
  | Zombie p zt n =>
    simp only [RefsObj] at hr; subst hr
    rcases hzw p zt n rfl with ⟨h65, hth, -⟩ | ⟨h65, hth, -⟩
    · have hz : zt = capability.ZOMBIE_TCB := UScalar.eq_of_val_eq (by rw [zombie_tcb_val]; exact h65)
      subst hz
      exact tcbCase _ (Or.inr ⟨n, rfl⟩) hth
    · exact cnCase _ zt (Or.inr ⟨n, rfl⟩) hth
  | _ => simp [RefsObj] at hr

/-- **A thread cap of the MDB covers its TCB's first word.** -/
theorem JAtZ.thread_coverF (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y : U64}
    (hy : y ∈ Z.G.chains.flatten) {w : U64} (hT : capV (L.mem s) y = .Thread w) :
    physF (capV (L.mem s) y) = true ∧ isUt (capV (L.mem s) y) = false ∧
      baseF (capV (L.mem s) y) ≤ w.val ∧ w.val + 1 ≤ topF (capV (L.mem s) y) + 1 := by
  have hP := J.xtop.rel.1
  have hys : IsSlot Z.th y := ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  obtain ⟨sl, hA, hsl⟩ := hys.abs
  have hcv : CapValid Z.th (capV (L.mem s) y) := by
    rw [← hsl]; exact J.xtop.rel.2.1.2.1.abs hA (capAt_capV _ _)
  rw [hT] at hcv
  have hqi : IsSlotAt Z.th w 0 := Or.inr ⟨hcv, by decide⟩
  have hv : (slotOf w 0).val = w.val := by rw [hqi.val hP]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := J.ref_cover hy (q := w) (by rw [hT]; rfl) hqi
  rw [hv] at h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem JAtZ.thread_cover (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y : U64}
    (hy : y ∈ Z.G.chains.flatten) {w : U64} (hT : capV (L.mem s) y = .Thread w) :
    Covered (L.mem s) Z.G w.val (w.val + 1) :=
  let ⟨h1, h2, h3, h4⟩ := J.thread_coverF hy hT
  ⟨y, hy, h1, h2, h3, h4⟩

/-- **`ReadyLive` from `LiveJ`** (module docstring): the slots in use and the
debug-list head are named by caps; a cap at `x` naming one has another
elsewhere. -/
theorem JAtZ.readyLive (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hL : LiveJ (L := L) Z.th H Z.G s σ)
    {x : U64}
    (hc1 : ∀ q i, IsSlotAt Z.th q i → slotOf q i ≠ x → InUse (L.mem s) σ (slotOf q i) →
      RefsObj q (capV (L.mem s) x) → ∃ y ∈ Z.G.chains.flatten, y ≠ x ∧ RefsObj q (capV (L.mem s) y))
    (hc2 : ∀ w, capV (L.mem s) x = .Thread w → ∃ y ∈ Z.G.chains.flatten, y ≠ x ∧ capV (L.mem s) y = .Thread w) :
    ReadyLive (L := L) Z.th s σ Z.G x := by
  have hP := J.xtop.rel.1
  refine ⟨fun y hy hyx hu => ?_, fun h0 hi0 => ?_⟩
  · obtain ⟨q, i, hqi, rfl⟩ := hy
    rcases hL.slots q i hqi hu with ⟨y', hy', hr⟩ | hb
    rotate_left
    · exact Or.inr hb
    obtain ⟨y'', hy'', hne, hr''⟩ : ∃ y ∈ Z.G.chains.flatten, y ≠ x ∧ RefsObj q (capV (L.mem s) y) := by
      by_cases e : y' = x
      · subst e; exact hc1 q i hqi hyx hu hr
      · exact ⟨y', hy', e, hr⟩
    obtain ⟨h1, h2, h3, h4⟩ := J.ref_cover hy'' hr'' hqi
    exact Or.inl ⟨y'', hy'', hne, h1, h2, h3, h4⟩
  · obtain ⟨y', hy', hT⟩ := hL.dbg 0 h0 (J.bv_ne_idleThread hi0)
    obtain ⟨y'', hy'', hne, hT''⟩ : ∃ y ∈ Z.G.chains.flatten, y ≠ x ∧
        capV (L.mem s) y = .Thread (dbgHead (L := L) s) := by
      by_cases e : y' = x
      · subst e; exact hc2 _ hT
      · exact ⟨y', hy', e, hT⟩
    obtain ⟨h1, h2, h3, h4⟩ := J.thread_coverF hy'' hT''
    exact ⟨y'', hy'', hne, h1, h2, h3, h4⟩

/-- `ReadyLive` when `x`'s cap names no container and is no thread cap. -/
theorem JAtZ.readyLive_noRef (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveJ (L := L) Z.th H Z.G s σ) {x : U64} (hn : ∀ q, ¬ RefsObj q (capV (L.mem s) x)) :
    ReadyLive (L := L) Z.th s σ Z.G x :=
  J.readyLive hL (fun q _ _ _ _ h => absurd h (hn q)) (fun w h => absurd (by rw [h]; rfl) (hn w))

/-- `ReadyLive` when another cap of the MDB has `x`'s cap's key (`okey`;
a CNode or thread cap not final). -/
theorem JAtZ.readyLive_key (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveJ (L := L) Z.th H Z.G s σ) {x y : U64} (hy : y ∈ Z.G.chains.flatten) (hne : y ≠ x)
    (hk : okey (capV (L.mem s) y) = okey (capV (L.mem s) x)) (hkn : okey (capV (L.mem s) x) ≠ none) :
    ReadyLive (L := L) Z.th s σ Z.G x := by
  refine J.readyLive hL (fun q _ _ _ _ hr => ⟨y, hy, hne, ?_⟩) (fun w hw => ⟨y, hy, hne, ?_⟩)
  · generalize capV (L.mem s) x = c at hr hk hkn
    generalize capV (L.mem s) y = d at hk ⊢
    cases c <;> simp only [RefsObj] at hr <;> subst hr <;> cases d <;> simp_all [okey, RefsObj]
  · rw [hw] at hk
    generalize capV (L.mem s) y = d at hk ⊢
    cases d <;> simp_all [okey]

/-- `ReadyLive` at a removable zombie (its count `0`, or `1` at its own first
slot): its object's slots unused but its own (`zslots`). -/
theorem JAtZ.readyLive_zombie (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveJ (L := L) Z.th H Z.G s σ) {x : U64} (hx : IsSlot Z.th x) {p zt n : U64}
    (hz : capV (L.mem s) x = .Zombie p zt n) (hrm : n.val = 0 ∨ (n.val = 1 ∧ p = x)) :
    ReadyLive (L := L) Z.th s σ Z.G x := by
  have hP := J.xtop.rel.1
  refine J.readyLive hL (fun q i hqi hne hu hr => ?_) (fun w h => by rw [hz] at h; cases h)
  rw [hz] at hr
  simp only [RefsObj] at hr
  subst hr
  exfalso
  have hlt : ¬ n.val ≤ i := fun h => hL.zslots x hx p zt n hz i hqi h hu
  rcases hrm with h0 | ⟨h1, hpx⟩
  · omega
  · have hi : i = 0 := by omega
    subst hi
    apply hne
    have hv := hqi.val hP
    apply UScalar.eq_of_val_eq
    rw [hv, ← hpx]; simp


/-- **`other_key` for any cap needing a finalisation decision**, not a
zombie (a CNode cap too): a non-final one has another cap of its key in the
MDB. -/
theorem other_keyN {th : TypedHeap} (hP : Placed th) {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {c : capability.Cap}
    (hcv : capV (L.mem s) (cslotAddr sl) = c) (hNF : NeedsFin c) (hzc : isZb c = false)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    ∃ y ∈ G.chains.flatten, y ≠ cslotAddr sl ∧ okey (capV (L.mem s) y) = okey c := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hF⟩ := hDS
  have hne : Fl4Spec.genObjRefs (absCap (capV (L.mem s) (cslotAddr sl))) ≠ ∅ := by
    rw [hcv]; exact needsFin_refs hNF
  rw [← hcv] at hfin
  have hcn : c ≠ .Null := by rintro rfl; rcases hNF with ⟨h, -⟩ | ⟨_, _, _, _, h⟩ | h <;> cases h
  have hx : cslotAddr sl ∈ G.chains.flatten :=
    (hM.members _).2 ⟨hA.isSlot, _, capAt_capV _ _, by rw [hcv]; exact hcn⟩
  have hzx : isZb (capV (L.mem s) (cslotAddr sl)) = false := by rw [hcv]; exact hzc
  by_contra hno
  apply hfin
  refine (final_iff hP hR hM hF hA hne).2 fun y hy hyx hov => hno ⟨y, hy, hyx, ?_⟩
  have hzy : isZb (capV (L.mem s) y) = false := by
    cases h : isZb (capV (L.mem s) y)
    · rfl
    · exact absurd hov.symm (hF.fm.zfin y hy _ hx hyx h)
  rw [← hcv]
  exact (hF.fm.key _ hx y hy (Ne.symm hyx) hov hzx hzy (by rw [hcv, hNF.nf]; simp)).symm

end

end

end Fl4Proofs.P3
