/-
P3 (DESIGN.md §9), untyped: **`LiveDN` after the TCB retype** (KENTRY-PLAN g2j;
g2f's "retype loop invariant": seL4's `tcbDebugAppend` before the thread caps'
insert).

FL4's TCB retype links the new TCBs `bT A (w-1), …, bT A 0` in front of core
0's debug list (UtTcbLoopC's `TcbC`: each new TCB's `DEBUG_NEXT` the one
created before it, the first one's the old head; `DEBUG_PREV` the one after,
the last one's null; the old head's `DEBUG_PREV` the first new TCB; the head
word the last new TCB).

* `newL`: the new TCBs in list order; `nextIn_newL`, `prevA_newL`,
  `nextIn_append_not_mem`, `prevA_newL_append`: the list functions over
  `newL A w ++ l`.
* `DbgWFL.prepend`: the debug lists after prepending fresh TCBs to one core's
  list (every other list and link word kept).
* `LiveDN.wstepRD`: LiveFrame's `LiveDN.wstepR` with the debug-list walk's
  thread caps given after (in place of `DbgKeep`, which the append breaks).
-/
import Fl4Proofs.P3.UtRetLive
import Fl4Proofs.P3.UtTcbLoopC
import Fl4Proofs.P3.DbgWF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc Fl4Proofs.P1

noncomputable section

/-! ## Lists -/

/-- The new TCBs in list order (the last created first). -/
def newL (A : Nat) : Nat → List U64
  | 0 => []
  | j + 1 => bT A j :: newL A j

theorem mem_newL {A w : Nat} {x : U64} : x ∈ newL A w ↔ ∃ j, j < w ∧ x = bT A j := by
  induction w with
  | zero => simp [newL]
  | succ w ih =>
    simp only [newL, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨w, by omega, rfl⟩
      · exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases e : j = w
      · exact Or.inl (by rw [e])
      · exact Or.inr ⟨j, by omega, rfl⟩

theorem nodup_newL {A w : Nat} (hinj : ∀ i j, i < w → j < w → bT A i = bT A j → i = j) : (newL A w).Nodup := by
  induction w with
  | zero => exact List.nodup_nil
  | succ w ih =>
    refine List.nodup_cons.2 ⟨fun h => ?_, ih fun i j hi hj e => hinj i j (by omega) (by omega) e⟩
    obtain ⟨j, hj, e⟩ := mem_newL.1 h
    have := hinj w j (by omega) (by omega) e
    omega

theorem headD_newL_append {A w : Nat} (l : List U64) :
    (newL A w ++ l).headD 0#u64 = if w = 0 then l.headD 0#u64 else bT A (w - 1) := by
  cases w with
  | zero => rfl
  | succ w => simp [newL]

theorem nextIn_append_not_mem {nl l : List U64} {x : U64} (hx : x ∉ nl) : nextIn (nl ++ l) x = nextIn l x := by
  induction nl with
  | nil => rfl
  | cons a r ih =>
    have hax : a ≠ x := fun e => hx (by rw [e]; exact List.mem_cons_self ..)
    simp only [List.cons_append, nextIn, if_neg hax]
    exact ih (fun h => hx (List.mem_cons_of_mem _ h))

theorem prevA_newL_append {A w : Nat} {l : List U64} {x : U64} (hx : x ∉ newL A w) (q : U64) :
    prevA q (newL A w ++ l) x = prevA (if w = 0 then q else bT A 0) l x := by
  induction w generalizing q with
  | zero => rfl
  | succ w ih =>
    have hax : bT A w ≠ x := fun e => hx (by rw [← e]; exact List.mem_cons_self ..)
    simp only [newL, List.cons_append, prevA, if_neg hax]
    rw [ih (fun h => hx (List.mem_cons_of_mem _ h))]
    by_cases hw : w = 0
    · subst hw; simp
    · simp [hw]

theorem nextIn_newL {A w : Nat} (hinj : ∀ i j, i < w → j < w → bT A i = bT A j → i = j) (l : List U64)
    {j : Nat} (hj : j < w) : nextIn (newL A w ++ l) (bT A j) = if j = 0 then l.headD 0#u64 else bT A (j - 1) := by
  induction w with
  | zero => omega
  | succ w ih =>
    simp only [newL, List.cons_append, nextIn]
    by_cases e : j = w
    · subst e
      rw [if_pos rfl, headD_newL_append]
    · have hne : bT A w ≠ bT A j := fun h => e (hinj j w (by omega) (by omega) h.symm)
      rw [if_neg hne]
      exact ih (fun i k hi hk h => hinj i k (by omega) (by omega) h) (by omega)

theorem prevA_newL {A w : Nat} (hinj : ∀ i j, i < w → j < w → bT A i = bT A j → i = j) (l : List U64)
    {j : Nat} (hj : j < w) (q : U64) : prevA q (newL A w ++ l) (bT A j) = if j + 1 < w then bT A (j + 1) else q := by
  induction w generalizing q with
  | zero => omega
  | succ w ih =>
    simp only [newL, List.cons_append, prevA]
    by_cases e : j = w
    · subst e
      rw [if_pos rfl, if_neg (by omega)]
    · have hne : bT A w ≠ bT A j := fun h => e (hinj j w (by omega) (by omega) h.symm)
      rw [if_neg hne, ih (fun i k hi hk h => hinj i k (by omega) (by omega) h) (by omega)]
      by_cases h2 : j + 1 < w
      · rw [if_pos h2, if_pos (by omega)]
      · have : j + 1 = w := by omega
        rw [if_neg h2, if_pos (by omega), this]

/-! ## The debug lists after prepending fresh TCBs -/

set_option maxHeartbeats 1000000 in
/-- **Prepending fresh TCBs to core `c0`'s debug list** (module docstring). -/
theorem DbgWFL.prepend {T Cs : Set U64} {m m' hd : U64 → U64} {lst : U64 → List U64}
    (hW : DbgWFL T Cs m hd lst) {c0 : U64} (hc0 : c0 ∈ Cs) (nl : List U64) (hnd : nl.Nodup)
    (hdis : ∀ x ∈ nl, x ∉ T) (hz : (0#u64 : U64) ∉ nl)
    (hhd0 : m' (hd c0) = (nl ++ lst c0).headD 0#u64)
    (hhd : ∀ c ∈ Cs, c ≠ c0 → m' (hd c) = m (hd c))
    (hnn : ∀ x ∈ nl, m' (dnA x) = nextIn (nl ++ lst c0) x)
    (hnp : ∀ x ∈ nl, m' (dpA x) = prevA 0#u64 (nl ++ lst c0) x)
    (hna : ∀ x ∈ nl, m' (affA x) = c0)
    (hTn : ∀ y ∈ T, m' (dnA y) = m (dnA y))
    (hTp : ∀ y ∈ T, (lst c0 = [] ∨ y ≠ (lst c0).headD 0#u64) → m' (dpA y) = m (dpA y))
    (hTp0 : lst c0 ≠ [] → m' (dpA ((lst c0).headD 0#u64)) = prevA 0#u64 (nl ++ lst c0) ((lst c0).headD 0#u64))
    (hTa : ∀ y ∈ T, m' (affA y) = m (affA y)) :
    DbgWFL (T ∪ {x | x ∈ nl}) Cs m' hd (Function.update lst c0 (nl ++ lst c0)) := by
  have hlT : ∀ c ∈ Cs, ∀ x ∈ lst c, x ∈ T := fun c hc x hx => (hW.mem c hc x hx).1
  have hnl : ∀ c ∈ Cs, ∀ x ∈ lst c, x ∉ nl := fun c hc x hx h => hdis x h (hlT c hc x hx)
  -- `prevA` over the prefixed list at an old member
  have hpv : ∀ x ∈ lst c0, prevA 0#u64 (nl ++ lst c0) x =
      if x = (lst c0).headD 0#u64 then prevA 0#u64 (nl ++ lst c0) x else prevA 0#u64 (lst c0) x := by
    intro x hx
    split_ifs with hh
    · rfl
    · have hxn := hnl c0 hc0 x hx
      cases e : lst c0 with
      | nil => rw [e] at hx; simp at hx
      | cons a r =>
        rw [e] at hh hx
        have hax : a ≠ x := fun h => hh (by simp [h])
        -- the accumulator does not matter at a non-head member
        have key : ∀ (q : U64) (u : List U64), x ∉ u → prevA q (u ++ a :: r) x = prevA 0#u64 (a :: r) x := by
          intro q u hu
          induction u generalizing q with
          | nil => simp only [List.nil_append, prevA, if_neg hax]
          | cons c u' ihu =>
            have hcx : c ≠ x := fun h => hu (by rw [h]; exact List.mem_cons_self ..)
            simp only [List.cons_append, prevA, if_neg hcx]
            exact ihu c (fun h => hu (List.mem_cons_of_mem _ h))
        exact key 0#u64 nl hxn
  refine ⟨fun c hc => ?_, fun c hc x hx => ?_, fun c hc x hx => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc x hx => ?_, fun y hy hn => ?_⟩
  · -- head
    by_cases e : c = c0
    · subst e; rw [Function.update_self]; exact hhd0
    · rw [Function.update_of_ne e, hhd c hc e]; exact hW.head c hc
  · -- next
    by_cases e : c = c0
    · subst e
      rw [Function.update_self] at hx ⊢
      rcases List.mem_append.1 hx with h | h
      · exact hnn x h
      · rw [hTn x (hlT c hc x h), hW.next c hc x h, nextIn_append_not_mem (hnl c hc x h)]
    · rw [Function.update_of_ne e] at hx ⊢
      rw [hTn x (hlT c hc x hx)]; exact hW.next c hc x hx
  · -- prev
    by_cases e : c = c0
    · subst e
      rw [Function.update_self] at hx ⊢
      rcases List.mem_append.1 hx with h | h
      · exact hnp x h
      · have hne : lst c ≠ [] := fun e => by rw [e] at h; simp at h
        by_cases hh : x = (lst c).headD 0#u64
        · rw [hh]; exact hTp0 hne
        · rw [hpv x h, if_neg hh, hTp x (hlT c hc x h) (Or.inr hh)]; exact hW.prev c hc x h
    · rw [Function.update_of_ne e] at hx ⊢
      have hx0 : x ∉ lst c0 := fun h => e (hW.disj hc hc0 hx h)
      have hxz : x ≠ 0#u64 := fun h => hW.zero c hc (by rw [← h]; exact hx)
      refine (hTp x (hlT c hc x hx) ?_).trans (hW.prev c hc x hx)
      cases e2 : lst c0 with
      | nil => exact Or.inl rfl
      | cons a r =>
        right
        rw [e2] at hx0
        intro h; simp only [List.headD_cons] at h; exact hx0 (by rw [h]; exact List.mem_cons_self ..)
  · -- nodup
    by_cases e : c = c0
    · subst e
      rw [Function.update_self]
      exact List.nodup_append.2 ⟨hnd, hW.nodup c hc, fun a ha b hb e => hnl c hc b hb (e ▸ ha)⟩
    · rw [Function.update_of_ne e]; exact hW.nodup c hc
  · -- zero
    by_cases e : c = c0
    · subst e
      rw [Function.update_self]
      intro h
      rcases List.mem_append.1 h with h | h
      · exact hz h
      · exact hW.zero c hc h
    · rw [Function.update_of_ne e]; exact hW.zero c hc
  · -- mem
    by_cases e : c = c0
    · subst e
      rw [Function.update_self] at hx
      rcases List.mem_append.1 hx with h | h
      · exact ⟨Or.inr h, hna x h⟩
      · exact ⟨Or.inl (hlT c hc x h), by rw [hTa x (hlT c hc x h)]; exact (hW.mem c hc x h).2⟩
    · rw [Function.update_of_ne e] at hx
      exact ⟨Or.inl (hlT c hc x hx), by rw [hTa x (hlT c hc x hx)]; exact (hW.mem c hc x hx).2⟩
  · -- off
    rcases hy with hy | hy
    · have hn' : ∀ c ∈ Cs, y ∉ lst c := fun c hc h => by
        by_cases e : c = c0
        · subst e
          exact hn c hc (by rw [Function.update_self]; exact List.mem_append_right _ h)
        · exact hn c hc (by rw [Function.update_of_ne e]; exact h)
      obtain ⟨h1, h2⟩ := hW.off y hy hn'
      refine ⟨by rw [hTn y hy]; exact h1, ?_⟩
      rw [hTp y hy ?_]
      · exact h2
      cases e2 : lst c0 with
      | nil => exact Or.inl rfl
      | cons a r =>
        right
        have := hn' c0 hc0
        rw [e2] at this
        intro h; simp only [List.headD_cons] at h; exact this (by rw [h]; exact List.mem_cons_self ..)
    · exact absurd (by rw [Function.update_self]; exact List.mem_append_left _ hy) (hn c0 hc0)

/-! ## `LiveDN` with the debug walk's thread caps given -/

section
open Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **LiveFrame's `LiveDN.wstepR` with the debug walk's thread caps after
given** (module docstring): the kernel-state base kept in place of `DbgKeep`. -/
theorem LiveDN.wstepRD {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {G' : MdbGhost} {s' : S}
    {σ' : Fl4Spec.State Unit} (hM' : MdbLinks Z.th (L.mem s') G')
    {H' : P1.Heap} (hDW' : DbgWF (P1.Heap.tcbs H') Cs (L.mem s') (dbgHd (L := L) s'))
    (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H' s' p)
    (hks : L.ksb s' = L.ksb s)
    (hdbg : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') ≠ 0#u64 →
      (dbgNth (L.mem s') n (dbgHead (L := L) s')).bv ≠ σ'.idleThread →
      ∃ y ∈ G'.chains.flatten, capV (L.mem s') y = .Thread (dbgNth (L.mem s') n (dbgHead (L := L) s')))
    (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧ sl.2.length = r ∧
      DestCap Z.th (L.mem s) p)
    (hcW : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → LSim (capV (L.mem s') y) (capV (L.mem s) y))
    (hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W)
    (hNO : ∀ sl ∈ W, capV (L.mem s') (cslotAddr sl) = .Null → σ'.isOriginalCap sl = false)
    (hZ : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n)
    (hK2 : ∀ y0, IsSlot Z.th y0 → capV (L.mem s) y0 ≠ .Null →
      ∃ y, IsSlot Z.th y ∧ capV (L.mem s') y ≠ .Null ∧ shape (capV (L.mem s') y) = shape (capV (L.mem s) y0)) :
    LiveDN (L := L) Z.th H' Cs G' s' σ' := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hP : Placed Z.th := J.xtop.rel.1
  have hM := J.xtop.rel.2.1.2.2.1
  have hFI := J.xtop.rel.2.2.1
  have hmemS : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ Z.G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  have hinG' : ∀ y, IsSlot Z.th y → capV (L.mem s') y ≠ .Null → y ∈ G'.chains.flatten := fun y hy hn =>
    (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
  -- the written slots
  have hWat : ∀ sl ∈ W, ∃ p r i, Z.th p = some (.cnode r) ∧ IsSlotAt Z.th p i ∧ cslotAddr sl = slotOf p i ∧
      AbsSlot Z.th sl ∧ DestCap Z.th (L.mem s) p := fun sl hsl => by
    obtain ⟨p, r, h1, hp, hl, hDL⟩ := hW sl hsl
    have hA : AbsSlot Z.th sl := ⟨p, h1, Or.inl (by rw [hl]; exact hp)⟩
    obtain ⟨p', i, hpi, h1', hxe⟩ := hA.at
    have e : p' = p := P1.eq_of_bv (h1'.symm.trans h1)
    subst e
    exact ⟨p', r, i, hp, hpi, hxe, hA, hDL⟩
  -- a live container stays covered
  have hcov : ∀ p r i, Z.th p = some (.cnode r) → IsSlotAt Z.th p i → DestCap Z.th (L.mem s) p →
      (∃ y ∈ G'.chains.flatten, RefsObj p (capV (L.mem s') y)) ∨ KsSlot (L.ksb s') (slotOf p i) := by
    intro p r i hp hpi hDL
    obtain ⟨y, r', gs, g, hy, hc⟩ := hDL
    obtain ⟨y', hy', hn', hsh⟩ := hK2 y hy (by rw [hc]; exact fun h => by cases h)
    exact Or.inl ⟨y', hinG' y' hy' hn', (shape_refs hsh p).2 (by rw [hc]; rfl)⟩
  -- no zombie names a live container
  have hnz : ∀ p r, Z.th p = some (.cnode r) → DestCap Z.th (L.mem s) p →
      ∀ y, IsSlot Z.th y → ∀ zt n, capV (L.mem s) y ≠ .Zombie p zt n := by
    intro p r hp hDL y hy zt n hz
    obtain ⟨y1, r', gs, g, hy1, hc⟩ := hDL
    have hne : y1 ≠ y := fun e => by rw [e, hz] at hc; cases hc
    exact FinInv.zombie_alone hFI hM hy hz y1 hy1 hne (refsObj_objRefs (by rw [hc]; rfl))
  -- a slot off `W` in use after was in use before
  have hU : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := by
    intro y hy hyW hu
    rcases hu with hu | ⟨x, hx, ho⟩
    · exact Or.inl fun h => hu (((hcW y hy hyW).1).2 h)
    · rcases hoW x ho with ho' | hxW
      · exact Or.inr ⟨x, hx, ho'⟩
      · exact (hyW x hxW hx.symm).elim
  have hL' : LiveJ (L := L) Z.th H' G' s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
      fun y hy p zt n hz hzt => ?_⟩
    · by_cases hyW : ∀ sl ∈ W, slotOf q i ≠ cslotAddr sl
      · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hyW hu) with ⟨y, hy, hr⟩ | hb
        · obtain ⟨y', hy', hn', hsh⟩ := hK2 y (hmemS y hy) (hmemN y hy)
          exact Or.inl ⟨y', hinG' y' hy' hn', (shape_refs hsh q).2 hr⟩
        · exact Or.inr (by rw [hks]; exact hb)
      · push_neg at hyW
        obtain ⟨sl, hsl, e⟩ := hyW
        obtain ⟨p, r, i', hp, hpi, hxe, -, hDL⟩ := hWat sl hsl
        obtain ⟨e1, e2⟩ := slotOf_inj hP hqi hpi (e.trans hxe)
        subst e1; subst e2
        exact hcov q r i hp hqi hDL
    · exact hdbg k hk hki
    · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
      by_cases hyW : ∀ sl ∈ W, slotOf p i ≠ cslotAddr sl
      · exact hL.zslots y0 hy0 p zt n hz0 i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hyW hu)
      · push_neg at hyW
        obtain ⟨sl, hsl, e⟩ := hyW
        obtain ⟨p', r, i', hp, hpi', hxe, -, hDL⟩ := hWat sl hsl
        obtain ⟨e1, -⟩ := slotOf_inj hP hpi hpi' (e.trans hxe)
        subst e1
        exact hnz p r hp hDL y0 hy0 zt n hz0
    · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
      exact hdead p ⟨y0, hy0, zt, n, hz0, hzt⟩
  refine ⟨hL', hDW', fun sl hA h => ?_⟩
  by_cases hsW : sl ∈ W
  · exact hNO sl hsW h
  · have hne : ∀ sl' ∈ W, cslotAddr sl ≠ cslotAddr sl' := fun sl' hsl' e => by
      obtain ⟨-, -, -, -, -, -, hA', -⟩ := hWat sl' hsl'
      exact hsW (by rw [cslotAddr_inj hP hA hA' e]; exact hsl')
    have h0 : capV (L.mem s) (cslotAddr sl) = .Null := ((hcW _ hA.isSlot hne).1).1 h
    cases ho : σ'.isOriginalCap sl
    · rfl
    · rcases hoW sl ho with ho' | hm
      · rw [hN sl hA h0] at ho'; cases ho'
      · exact absurd hm hsW

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} {arI : machine.Arch A'}
variable {AR : A' → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **UtRetLive's `JAtZ.ret_liveN` with `DbgWF` and the debug walk's thread
caps after given** (the TCB retype appends to the debug list). -/
theorem JAtZ.ret_liveND {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {a' : A'} {σ' : Fl4Spec.State Unit} {D' : Set U64}
    {th' : TypedHeap} (hX' : XTopAt (L := L) AR Z' s' a' σ') (hth : Z'.th = th')
    (hold : ∀ q k, Z.th q = some k → th' q = some k) (hNE : NewEmpty Z.th th' (L.mem s') σ')
    (hks : L.ksb s' = L.ksb s) (hDW' : DbgWF (P1.Heap.tcbs H') Cs (L.mem s') (dbgHd (L := L) s'))
    (hdbg : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') ≠ 0#u64 →
      (dbgNth (L.mem s') n (dbgHead (L := L) s')).bv ≠ σ'.idleThread →
      ∃ y ∈ Z'.G.chains.flatten, capV (L.mem s') y = .Thread (dbgNth (L.mem s') n (dbgHead (L := L) s')))
    (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H' s' p)
    (hnew : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D')
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
  have hLv := LiveDN.wstepRD J ⟨hL, ⟨lst, hDW⟩, hN⟩ hM' hDW' hdead hks hdbg W hW
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
