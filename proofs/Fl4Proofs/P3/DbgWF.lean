/-
P3 (DESIGN.md §9), CSpace: **the well-formedness of FL4's per-core debug
lists of TCBs** (`DbgWF` [J], FL4-only: seL4 C's `tcbDebugAppend` /
`tcbDebugRemove` rely on it; l4v does not model the debug list).

* `nextIn l x`, `prevA q l x`: the successor and predecessor of `x` in the
  list `l` (`0` / `q` at the ends).
* `DbgWFL T Cs m hd lst`: for each core `c ∈ Cs`, the list `lst c` from the
  core's head word `hd c` is a finite, duplicate-free list of nonzero TCBs of
  affinity `c` whose `DEBUG_NEXT` / `DEBUG_PREV` words are their successor and
  predecessor in it (the head's predecessor and the last's successor `0`); a
  TCB of `T` on no list has null debug links. `DbgWF`: some such lists.
  The lists of different cores are disjoint (`DbgWFL.disj`, from the
  affinities).
* `dbgRmM m hd0 t`: the words after FL4's `debug_remove t` (`debug_remove_mem`:
  every aligned word of the state after); `dbgRm_wf`: `DbgWFL` after with
  `t` erased from its core's list, every other list as it was (the list
  surgery: exactly `t` removed, the rest in order).
* `DbgApart`: the TCBs' debug and affinity words and the cores' head words
  pairwise apart (`dbgApart_of`, from `TcbPlaced` and `NodePlaced`).
-/
import Fl4Proofs.P3.LiveDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1

/-! ## Successor and predecessor in a list -/

theorem nextIn_mem (l : List U64) (x : U64) : nextIn l x = 0#u64 ∨ nextIn l x ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a r ih =>
    unfold nextIn
    split
    · cases r with
      | nil => exact Or.inl rfl
      | cons b r' => exact Or.inr (by simp)
    · rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem prevA_mem {l : List U64} {x : U64} (hx : x ∈ l) (q : U64) : prevA q l x = q ∨ prevA q l x ∈ l := by
  induction l generalizing q with
  | nil => simp at hx
  | cons a r ih =>
    unfold prevA
    split
    · exact Or.inl rfl
    · rename_i hax
      have hxr : x ∈ r := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hax
        · exact h
      rcases ih hxr a with h | h
      · exact Or.inr (by rw [h]; simp)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem prevA_acc (q q' : U64) (r : List U64) (x : U64) :
    prevA q r x = prevA q' r x ∨ (prevA q r x = q ∧ prevA q' r x = q') := by
  cases r with
  | nil => exact Or.inl rfl
  | cons b r' =>
    unfold prevA
    split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl

theorem headD_erase (l : List U64) (t : U64) :
    (l.erase t).headD 0#u64 = if l.headD 0#u64 = t then nextIn l t else l.headD 0#u64 := by
  cases l with
  | nil => simp [nextIn]
  | cons a r =>
    by_cases hat : a = t
    · subst hat; simp [nextIn]
    · simp [List.erase_cons, hat, nextIn]

theorem nextIn_erase {l : List U64} {t x : U64} (hnd : l.Nodup) (ht0 : t ≠ 0#u64) (hx : x ∈ l) (hxt : x ≠ t) :
    nextIn (l.erase t) x = if nextIn l x = t then nextIn l t else nextIn l x := by
  induction l with
  | nil => simp at hx
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.1 hnd
    by_cases hat : a = t
    · subst hat
      have hax : a ≠ x := fun e => hxt e.symm
      have hxr : x ∈ r := (List.mem_cons.1 hx).resolve_left (fun e => hax e.symm)
      simp only [List.erase_cons_head]
      have hn : nextIn (a :: r) x = nextIn r x := by simp [nextIn, hax]
      rw [hn]
      have hna : nextIn r x ≠ a := by
        rcases nextIn_mem r x with h | h
        · rw [h]; exact fun e => ht0 e.symm
        · exact fun e => ha (e ▸ h)
      rw [if_neg hna]
    · have he : (a :: r).erase t = a :: r.erase t := by simp [List.erase_cons, hat]
      rw [he]
      by_cases hax : a = x
      · subst hax
        have h1 : nextIn (a :: r.erase t) a = (r.erase t).headD 0#u64 := by simp [nextIn]
        have h2 : nextIn (a :: r) a = r.headD 0#u64 := by simp [nextIn]
        have h3 : nextIn (a :: r) t = nextIn r t := by simp [nextIn, hat]
        rw [h1, h2, h3, headD_erase]
      · have hxr : x ∈ r := (List.mem_cons.1 hx).resolve_left (fun e => hax e.symm)
        have h1 : nextIn (a :: r.erase t) x = nextIn (r.erase t) x := by simp [nextIn, hax]
        have h2 : nextIn (a :: r) x = nextIn r x := by simp [nextIn, hax]
        have h3 : nextIn (a :: r) t = nextIn r t := by simp [nextIn, hat]
        rw [h1, h2, h3, ih hr hxr]

theorem prevA_erase {l : List U64} {t x q : U64} (hnd : l.Nodup) (ht0 : t ≠ 0#u64) (hq : q ≠ t) (hx : x ∈ l)
    (hxt : x ≠ t) : prevA q (l.erase t) x = if prevA q l x = t then prevA q l t else prevA q l x := by
  induction l generalizing q with
  | nil => simp at hx
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.1 hnd
    by_cases hat : a = t
    · subst hat
      have hax : a ≠ x := fun e => hxt e.symm
      have hxr : x ∈ r := (List.mem_cons.1 hx).resolve_left (fun e => hax e.symm)
      simp only [List.erase_cons_head]
      have h1 : prevA q (a :: r) x = prevA a r x := by simp [prevA, hax]
      have h2 : prevA q (a :: r) a = q := by simp [prevA]
      rw [h1, h2]
      rcases prevA_acc q a r x with h | ⟨h3, h4⟩
      · rw [← h]
        have hne : prevA q r x ≠ a := by
          intro e
          rcases prevA_mem hxr q with h5 | h5
          · exact hq (e ▸ h5).symm
          · exact ha (e ▸ h5)
        rw [if_neg hne]
      · rw [h3, h4, if_pos rfl]
    · have he : (a :: r).erase t = a :: r.erase t := by simp [List.erase_cons, hat]
      rw [he]
      by_cases hax : a = x
      · subst hax
        simp [prevA, hq]
      · have hxr : x ∈ r := (List.mem_cons.1 hx).resolve_left (fun e => hax e.symm)
        have h1 : prevA q (a :: r.erase t) x = prevA a (r.erase t) x := by simp [prevA, hax]
        have h2 : prevA q (a :: r) x = prevA a r x := by simp [prevA, hax]
        have h3 : prevA q (a :: r) t = prevA a r t := by simp [prevA, hat]
        rw [h1, h2, h3, ih hr hat hxr]

/-- The successor of `x` is `t`: then `x` is `t`'s predecessor. -/
theorem prevA_of_next {l : List U64} {t x : U64} (hnd : l.Nodup) (ht0 : t ≠ 0#u64) (hx : x ∈ l)
    (h : nextIn l x = t) (q : U64) : prevA q l t = x := by
  induction l generalizing q with
  | nil => simp at hx
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.1 hnd
    have htr : t ∈ r → a ≠ t := fun h' e => ha (e ▸ h')
    by_cases hax : a = x
    · subst hax
      have h' : r.headD 0#u64 = t := by simpa [nextIn] using h
      cases r with
      | nil => exact absurd h'.symm ht0
      | cons b r' =>
        simp only [List.headD_cons] at h'
        subst h'
        have hab : a ≠ b := htr (by simp)
        simp [prevA, hab]
    · have hxr : x ∈ r := (List.mem_cons.1 hx).resolve_left (fun e => hax e.symm)
      have h' : nextIn r x = t := by simpa [nextIn, hax] using h
      have htm : t ∈ r := by
        rcases nextIn_mem r x with e | e
        · rw [h'] at e; exact absurd e ht0
        · rw [h'] at e; exact e
      have hat : a ≠ t := htr htm
      have := ih hr hxr h' a
      simp [prevA, hat, this]

/-- `x` is `t`'s predecessor, not the sentinel `q`: then `t` is `x`'s successor. -/
theorem next_of_prevA {l : List U64} {t x q : U64} (hnd : l.Nodup) (ht : t ∈ l) (hq : q ∉ l)
    (h : prevA q l t = x) (hxq : x ≠ q) : nextIn l x = t := by
  induction l generalizing q with
  | nil => simp at ht
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.1 hnd
    by_cases hat : a = t
    · subst hat; simp [prevA] at h; exact absurd h.symm hxq
    · have htr : t ∈ r := (List.mem_cons.1 ht).resolve_left (fun e => hat e.symm)
      have h' : prevA a r t = x := by simpa [prevA, hat] using h
      by_cases hxa : x = a
      · subst hxa
        -- `t` heads `r`
        cases r with
        | nil => simp at htr
        | cons b r' =>
          by_cases hbt : b = t
          · subst hbt; simp [nextIn]
          · have htr' : t ∈ r' := (List.mem_cons.1 htr).resolve_left (fun e => hbt e.symm)
            have h2 : prevA b r' t = x := by simpa [prevA, hbt] using h'
            rcases prevA_mem htr' b with e | e
            · rw [h2] at e; subst e; exact absurd (by simp) ha
            · rw [h2] at e; exact absurd (List.mem_cons_of_mem _ e) ha
      · have := ih hr htr ha h' hxa
        have hax : a ≠ x := fun e => hxa e.symm
        simp [nextIn, hax, this]

/-- The head of a list has the sentinel as predecessor. -/
theorem prevA_head {l : List U64} {t q : U64} (h : l.headD 0#u64 = t) : prevA q l t = q ∨ l = [] := by
  cases l with
  | nil => exact Or.inr rfl
  | cons a r => simp only [List.headD_cons] at h; subst h; simp [prevA]

/-! ## The invariant -/

/-- The lists of different cores are disjoint. -/
theorem DbgWFL.disj {T Cs : Set U64} {m hd : U64 → U64} {lst : U64 → List U64} (h : DbgWFL T Cs m hd lst)
    {c c' : U64} (hc : c ∈ Cs) (hc' : c' ∈ Cs) {x : U64} (hx : x ∈ lst c) (hx' : x ∈ lst c') : c = c' :=
  (h.mem c hc x hx).2.symm.trans (h.mem c' hc' x hx').2

/-- The words of the debug lists pairwise apart (module docstring). -/
structure DbgApart (T Cs : Set U64) (hd : U64 → U64) : Prop where
  dn_inj : ∀ y ∈ T, ∀ y' ∈ T, dnA y = dnA y' → y = y'
  dp_inj : ∀ y ∈ T, ∀ y' ∈ T, dpA y = dpA y' → y = y'
  dn_dp : ∀ y ∈ T, ∀ y' ∈ T, dnA y ≠ dpA y'
  hd_dn : ∀ c ∈ Cs, ∀ y ∈ T, hd c ≠ dnA y
  hd_dp : ∀ c ∈ Cs, ∀ y ∈ T, hd c ≠ dpA y
  af_dn : ∀ y ∈ T, ∀ y' ∈ T, affA y ≠ dnA y'
  af_dp : ∀ y ∈ T, ∀ y' ∈ T, affA y ≠ dpA y'
  af_hd : ∀ y ∈ T, ∀ c ∈ Cs, affA y ≠ hd c

/-- A word written. -/
def updW (m : U64 → U64) (w v : U64) : U64 → U64 := fun b => if w = b then v else m b

/-- **The words after `debug_remove t`** (FL4's code, `hd0` the head word
of `t`'s core). -/
def dbgRmM (m : U64 → U64) (hd0 t : U64) : U64 → U64 :=
  let m1 := if m hd0 = t then updW m hd0 (m (dnA t))
    else if m (dpA t) ≠ 0#u64 then updW m (dnA (m (dpA t))) (m (dnA t)) else m
  let m2 := if m (dnA t) ≠ 0#u64 then updW m1 (dpA (m (dnA t))) (m (dpA t)) else m1
  updW (updW m2 (dpA t) 0#u64) (dnA t) 0#u64

/-- `dbgRmM` word by word. -/
theorem dbgRmM_eq (m : U64 → U64) (hd0 t b : U64) :
    dbgRmM m hd0 t b =
      if dnA t = b then 0#u64 else if dpA t = b then 0#u64
      else if m (dnA t) ≠ 0#u64 ∧ dpA (m (dnA t)) = b then m (dpA t)
      else if m hd0 = t ∧ hd0 = b then m (dnA t)
      else if m hd0 ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ dnA (m (dpA t)) = b then m (dnA t)
      else m b := by
  by_cases h1 : m hd0 = t <;> by_cases h2 : m (dpA t) ≠ 0#u64 <;> by_cases h3 : m (dnA t) ≠ 0#u64 <;>
    simp [dbgRmM, updW, h1, h2, h3]

section Words
variable {T Cs : Set U64} {hd : U64 → U64} (hA : DbgApart T Cs hd) {m : U64 → U64} {t : U64} {c0 : U64}
  (ht : t ∈ T) (hc0 : c0 ∈ Cs) (hpT : m (dpA t) ≠ 0#u64 → m (dpA t) ∈ T)
  (hnT : m (dnA t) ≠ 0#u64 → m (dnA t) ∈ T)
include hA ht hc0 hpT hnT

theorem dbgRmM_dn {x : U64} (hx : x ∈ T) (hxt : x ≠ t) :
    dbgRmM m (hd c0) t (dnA x) =
      if m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ m (dpA t) = x then m (dnA t) else m (dnA x) := by
  have e1 : dnA t ≠ dnA x := fun e => hxt (hA.dn_inj x hx t ht e.symm)
  have e2 : dpA t ≠ dnA x := fun e => hA.dn_dp x hx t ht e.symm
  have c3 : ¬ (m (dnA t) ≠ 0#u64 ∧ dpA (m (dnA t)) = dnA x) := fun h' => hA.dn_dp x hx _ (hnT h'.1) h'.2.symm
  have c4 : ¬ (m (hd c0) = t ∧ hd c0 = dnA x) := fun h' => hA.hd_dn c0 hc0 x hx h'.2
  rw [dbgRmM_eq, if_neg e1, if_neg e2, if_neg c3, if_neg c4]
  by_cases hc : m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ m (dpA t) = x
  · rw [if_pos ⟨hc.1, hc.2.1, by rw [hc.2.2]⟩, if_pos hc]
  · rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, hA.dn_inj _ (hpT h'.2.1) x hx h'.2.2⟩), if_neg hc]

theorem dbgRmM_dp {x : U64} (hx : x ∈ T) (hxt : x ≠ t) :
    dbgRmM m (hd c0) t (dpA x) = if m (dnA t) ≠ 0#u64 ∧ m (dnA t) = x then m (dpA t) else m (dpA x) := by
  have e1 : dnA t ≠ dpA x := hA.dn_dp t ht x hx
  have e2 : dpA t ≠ dpA x := fun e => hxt (hA.dp_inj x hx t ht e.symm)
  have c4 : ¬ (m (hd c0) = t ∧ hd c0 = dpA x) := fun h' => hA.hd_dp c0 hc0 x hx h'.2
  have c5 : ¬ (m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ dnA (m (dpA t)) = dpA x) :=
    fun h' => hA.dn_dp _ (hpT h'.2.1) x hx h'.2.2
  rw [dbgRmM_eq, if_neg e1, if_neg e2]
  by_cases hc : m (dnA t) ≠ 0#u64 ∧ m (dnA t) = x
  · rw [if_pos ⟨hc.1, by rw [hc.2]⟩, if_pos hc]
  · rw [if_neg (fun h' => hc ⟨h'.1, hA.dp_inj _ (hnT h'.1) x hx h'.2⟩), if_neg c4, if_neg c5, if_neg hc]

theorem dbgRmM_hd {c : U64} (hc : c ∈ Cs) :
    dbgRmM m (hd c0) t (hd c) = if m (hd c0) = t ∧ hd c0 = hd c then m (dnA t) else m (hd c) := by
  have e1 : dnA t ≠ hd c := fun e => hA.hd_dn c hc t ht e.symm
  have e2 : dpA t ≠ hd c := fun e => hA.hd_dp c hc t ht e.symm
  have c3 : ¬ (m (dnA t) ≠ 0#u64 ∧ dpA (m (dnA t)) = hd c) := fun h' => hA.hd_dp c hc _ (hnT h'.1) h'.2.symm
  have c5 : ¬ (m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ dnA (m (dpA t)) = hd c) :=
    fun h' => hA.hd_dn c hc _ (hpT h'.2.1) h'.2.2.symm
  rw [dbgRmM_eq, if_neg e1, if_neg e2, if_neg c3]
  by_cases h' : m (hd c0) = t ∧ hd c0 = hd c
  · rw [if_pos h', if_pos h']
  · rw [if_neg h', if_neg c5, if_neg h']

theorem dbgRmM_af {x : U64} (hx : x ∈ T) : dbgRmM m (hd c0) t (affA x) = m (affA x) := by
  have e1 : dnA t ≠ affA x := fun e => hA.af_dn x hx t ht e.symm
  have e2 : dpA t ≠ affA x := fun e => hA.af_dp x hx t ht e.symm
  have c3 : ¬ (m (dnA t) ≠ 0#u64 ∧ dpA (m (dnA t)) = affA x) := fun h' => hA.af_dp x hx _ (hnT h'.1) h'.2.symm
  have c4 : ¬ (m (hd c0) = t ∧ hd c0 = affA x) := fun h' => hA.af_hd x hx c0 hc0 h'.2.symm
  have c5 : ¬ (m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ dnA (m (dpA t)) = affA x) :=
    fun h' => hA.af_dn x hx _ (hpT h'.2.1) h'.2.2.symm
  rw [dbgRmM_eq, if_neg e1, if_neg e2, if_neg c3, if_neg c4, if_neg c5]

theorem dbgRmM_dnt : dbgRmM m (hd c0) t (dnA t) = 0#u64 := by
  rw [dbgRmM_eq, if_pos rfl]

theorem dbgRmM_dpt : dbgRmM m (hd c0) t (dpA t) = 0#u64 := by
  rw [dbgRmM_eq, if_neg (hA.dn_dp t ht t ht), if_pos rfl]

end Words

/-- **`debug_remove t` keeps the debug lists well formed, removing exactly
`t`** (module docstring): `t`'s core's list loses `t` (`List.erase`), the
other lists are kept. -/
theorem dbgRm_wf {T Cs : Set U64} {hd m : U64 → U64} {lst : U64 → List U64} (h : DbgWFL T Cs m hd lst)
    (hA : DbgApart T Cs hd) {t : U64} (ht : t ∈ T) (ht0 : t ≠ 0#u64) (hc0 : m (affA t) ∈ Cs)
    (hpT : m (dpA t) ≠ 0#u64 → m (dpA t) ∈ T) (hnT : m (dnA t) ≠ 0#u64 → m (dnA t) ∈ T) :
    DbgWFL T Cs (dbgRmM m (hd (m (affA t))) t) hd (fun c => (lst c).erase t) := by
  generalize hc0d : m (affA t) = c0 at hc0 ⊢
  -- `t` is on no list but `c0`'s
  have hoff : ∀ c ∈ Cs, c ≠ c0 → t ∉ lst c := fun c hc hne htc => hne ((h.mem c hc t htc).2.symm.trans hc0d)
  have hnz : ∀ c ∈ Cs, ∀ x ∈ lst c, x ≠ 0#u64 := fun c hc x hx e => h.zero c hc (e ▸ hx)
  by_cases htl : t ∈ lst c0
  swap
  · -- on no list: the links null, nothing changes but `t`'s null links
    have hz := h.off t ht fun c hc htc => by
      by_cases e : c = c0
      · subst e; exact htl htc
      · exact hoff c hc e htc
    have hhd : m (hd c0) ≠ t := by
      rw [h.head c0 hc0]
      cases e : lst c0 with
      | nil => exact fun e' => ht0 e'.symm
      | cons a r => intro e'; simp only [List.headD_cons] at e'; exact htl (by rw [e, e']; simp)
    have hM : dbgRmM m (hd c0) t = m := by
      funext b
      unfold dbgRmM updW
      simp only [hz.1, hz.2, hhd, if_false, ne_eq, not_true_eq_false]
      by_cases e1 : dnA t = b
      · subst e1; simp [hz.1]
      · by_cases e2 : dpA t = b
        · subst e2; simp [e1, hz.2]
        · simp [e1, e2]
    rw [hM]
    have hl : ∀ c ∈ Cs, (lst c).erase t = lst c := fun c hc => List.erase_of_not_mem (by
      by_cases e : c = c0
      · subst e; exact htl
      · exact hoff c hc e)
    refine ⟨fun c hc => by rw [hl c hc]; exact h.head c hc, fun c hc x hx => by rw [hl c hc] at hx ⊢; exact h.next c hc x hx,
      fun c hc x hx => by rw [hl c hc] at hx ⊢; exact h.prev c hc x hx, fun c hc => by rw [hl c hc]; exact h.nodup c hc,
      fun c hc => by rw [hl c hc]; exact h.zero c hc, fun c hc x hx => by rw [hl c hc] at hx; exact h.mem c hc x hx,
      fun y hy hn => h.off y hy fun c hc => by rw [← hl c hc]; exact hn c hc⟩
  -- on `c0`'s list
  have hnd0 := h.nodup c0 hc0
  have hn0 : m (dnA t) = nextIn (lst c0) t := h.next c0 hc0 t htl
  have hp0 : m (dpA t) = prevA 0#u64 (lst c0) t := h.prev c0 hc0 t htl
  have hnm : m (dnA t) = 0#u64 ∨ m (dnA t) ∈ lst c0 := by rw [hn0]; exact nextIn_mem _ _
  have hpm : m (dpA t) = 0#u64 ∨ m (dpA t) ∈ lst c0 := by rw [hp0]; exact prevA_mem htl _
  have hW := fun {x} => dbgRmM_dn hA ht hc0 hpT hnT (x := x)
  have hWp := fun {x} => dbgRmM_dp hA ht hc0 hpT hnT (x := x)
  have hWh := fun {c} => dbgRmM_hd hA ht hc0 hpT hnT (c := c)
  have hWa := fun {x} => dbgRmM_af hA ht hc0 hpT hnT (x := x)
  -- a member of another core's list is not `t`'s neighbour
  have hfar : ∀ c ∈ Cs, c ≠ c0 → ∀ x ∈ lst c, x ∉ lst c0 := fun c hc hne x hx hx0 => hne (h.disj hc hc0 hx hx0)
  refine ⟨?_, ?_, ?_, fun c hc => (h.nodup c hc).erase t, fun c hc h0 => h.zero c hc (List.mem_of_mem_erase h0), ?_, ?_⟩
  · -- the heads
    intro c hc
    rw [hWh hc, headD_erase, ← h.head c hc]
    by_cases e : c = c0
    · subst e
      by_cases hh : m (hd c) = t
      · rw [if_pos ⟨hh, rfl⟩, if_pos hh, hn0]
      · rw [if_neg (fun h' => hh h'.1), if_neg hh]
    · have hh : m (hd c) ≠ t := by
        rw [h.head c hc]
        cases e' : lst c with
        | nil => exact fun e'' => ht0 e''.symm
        | cons a r => intro e''; simp only [List.headD_cons] at e''; exact hoff c hc e (by rw [e', e'']; simp)
      rw [if_neg hh]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hh (by rw [← h2]; exact h1)
  · -- the successors
    intro c hc x hx
    obtain ⟨hxt, hxl⟩ := (h.nodup c hc).mem_erase_iff.1 hx
    have hxT := (h.mem c hc x hxl).1
    have hx0 := hnz c hc x hxl
    rw [hW hxT hxt, nextIn_erase (h.nodup c hc) ht0 hxl hxt, ← h.next c hc x hxl]
    by_cases e : c = c0
    · subst e
      have hiff : m (dnA x) = t ↔ (m (hd c) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ m (dpA t) = x) := by
        constructor
        · intro hq
          rw [h.next c hc x hxl] at hq
          have hpx : prevA 0#u64 (lst c) t = x := prevA_of_next hnd0 ht0 hxl hq 0#u64
          refine ⟨fun hh => ?_, by rw [hp0, hpx]; exact hx0, by rw [hp0, hpx]⟩
          rw [h.head c hc] at hh
          rcases prevA_head (q := 0#u64) hh with e' | e'
          · exact hx0 (hpx.symm.trans e')
          · rw [e'] at htl; simp at htl
        · rintro ⟨-, h2, h3⟩
          rw [h.next c hc x hxl]
          exact next_of_prevA hnd0 htl (h.zero c hc) (by rw [← hp0]; exact h3) hx0
      by_cases hq : m (dnA x) = t
      · rw [if_pos (hiff.1 hq), if_pos hq, hn0]
      · rw [if_neg (fun h' => hq (hiff.2 h')), if_neg hq]
    · have hq : m (dnA x) ≠ t := by
        rw [h.next c hc x hxl]
        rcases nextIn_mem (lst c) x with e' | e'
        · rw [e']; exact fun e'' => ht0 e''.symm
        · exact fun e'' => hoff c hc e (e'' ▸ e')
      have hc' : ¬ (m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ m (dpA t) = x) := by
        rintro ⟨-, h2, h3⟩
        rcases hpm with e' | e'
        · exact h2 e'
        · exact hfar c hc e x hxl (h3 ▸ e')
      rw [if_neg hc', if_neg hq]
  · -- the predecessors
    intro c hc x hx
    obtain ⟨hxt, hxl⟩ := (h.nodup c hc).mem_erase_iff.1 hx
    have hxT := (h.mem c hc x hxl).1
    have hx0 := hnz c hc x hxl
    rw [hWp hxT hxt, prevA_erase (h.nodup c hc) ht0 (fun e => ht0 e.symm) hxl hxt, ← h.prev c hc x hxl]
    by_cases e : c = c0
    · subst e
      have hiff : m (dpA x) = t ↔ (m (dnA t) ≠ 0#u64 ∧ m (dnA t) = x) := by
        constructor
        · intro hq
          rw [h.prev c hc x hxl] at hq
          have hnx : nextIn (lst c) t = x := next_of_prevA hnd0 hxl (h.zero c hc) hq ht0
          exact ⟨by rw [hn0, hnx]; exact hx0, by rw [hn0, hnx]⟩
        · rintro ⟨-, h3⟩
          rw [h.prev c hc x hxl]
          exact prevA_of_next hnd0 hx0 htl (by rw [← hn0]; exact h3) 0#u64
      by_cases hq : m (dpA x) = t
      · rw [if_pos (hiff.1 hq), if_pos hq, hp0]
      · rw [if_neg (fun h' => hq (hiff.2 h')), if_neg hq]
    · have hq : m (dpA x) ≠ t := by
        rw [h.prev c hc x hxl]
        rcases prevA_mem hxl 0#u64 with e' | e'
        · rw [e']; exact fun e'' => ht0 e''.symm
        · exact fun e'' => hoff c hc e (e'' ▸ e')
      have hc' : ¬ (m (dnA t) ≠ 0#u64 ∧ m (dnA t) = x) := by
        rintro ⟨h2, h3⟩
        rcases hnm with e' | e'
        · exact h2 e'
        · exact hfar c hc e x hxl (h3 ▸ e')
      rw [if_neg hc', if_neg hq]
  · -- the members
    intro c hc x hx
    have hxl := List.mem_of_mem_erase hx
    obtain ⟨hxT, hxa⟩ := h.mem c hc x hxl
    exact ⟨hxT, by rw [hWa hxT]; exact hxa⟩
  · -- the TCBs on no list
    intro y hy hn
    by_cases hyt : y = t
    · subst hyt
      exact ⟨dbgRmM_dnt hA hy hc0 hpT hnT, dbgRmM_dpt hA hy hc0 hpT hnT⟩
    · have hn' : ∀ c ∈ Cs, y ∉ lst c := fun c hc hyl => hn c hc ((List.mem_erase_of_ne hyt).2 hyl)
      have hz := h.off y hy hn'
      rw [hW hy hyt, hWp hy hyt]
      have c1 : ¬ (m (hd c0) ≠ t ∧ m (dpA t) ≠ 0#u64 ∧ m (dpA t) = y) := by
        rintro ⟨-, h2, h3⟩
        rcases hpm with e' | e'
        · exact h2 e'
        · exact hn' c0 hc0 (h3 ▸ e')
      have c2 : ¬ (m (dnA t) ≠ 0#u64 ∧ m (dnA t) = y) := by
        rintro ⟨h2, h3⟩
        rcases hnm with e' | e'
        · exact h2 e'
        · exact hn' c0 hc0 (h3 ▸ e')
      rw [if_neg c1, if_neg c2]
      exact hz

section Store
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The debug words apart, from the TCBs' and the nodes' placement. -/
theorem dbgApart_of {T Cs : Set U64} {s : S} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) :
    DbgApart T Cs (dbgHd (L := L) s) := by
  have hne : ∀ {y y' K1 K2 : U64}, y ∈ T → y' ∈ T → K1.val < 4096 → K2.val < 4096 → K1.val = K2.val →
      core.num.U64.wrapping_add y K1 = core.num.U64.wrapping_add y' K2 → y = y' := by
    intro y y' K1 K2 hy hy' h1 h2 hk e
    by_contra hn
    exact field_ne (hT y hy) (hT y' hy') h1 h2 (fun e' => absurd e' hn) e
  have hne2 : ∀ {y y' K1 K2 : U64}, y ∈ T → y' ∈ T → K1.val < 4096 → K2.val < 4096 → K1.val ≠ K2.val →
      core.num.U64.wrapping_add y K1 ≠ core.num.U64.wrapping_add y' K2 :=
    fun hy hy' h1 h2 hk => field_ne (hT _ hy) (hT _ hy') h1 h2 (fun _ => hk)
  have hnd : ∀ {c y K : U64}, c ∈ Cs → y ∈ T → K.val < 4096 →
      L.nodeAt s c layout.node.DEBUG_TCBS ≠ core.num.U64.wrapping_add y K :=
    fun hc hy hK => node_ne_field (hN _ hc) (by simp [debug_val]) hy (hT _ hy) hK
  exact ⟨fun y hy y' hy' e => hne (K1 := 3576#u64) (K2 := 3576#u64) hy hy' (by simp) (by simp) rfl e,
    fun y hy y' hy' e => hne (K1 := 3584#u64) (K2 := 3584#u64) hy hy' (by simp) (by simp) rfl e,
    fun y hy y' hy' => hne2 (K1 := 3576#u64) (K2 := 3584#u64) hy hy' (by simp) (by simp) (by simp),
    fun c hc y hy => hnd (K := 3576#u64) hc hy (by simp), fun c hc y hy => hnd (K := 3584#u64) hc hy (by simp),
    fun y hy y' hy' => hne2 (K1 := 3520#u64) (K2 := 3576#u64) hy hy' (by simp) (by simp) (by simp),
    fun y hy y' hy' => hne2 (K1 := 3520#u64) (K2 := 3584#u64) hy hy' (by simp) (by simp) (by simp),
    fun y hy c hc e => hnd (K := 3520#u64) hc hy (by simp) e.symm⟩

/-- **FL4's `debug_remove t`, word by word** (`dbgRmM`, every aligned word;
the kernel-state base kept). -/
theorem debug_remove_mem {T Cs : Set U64} (s : S) (t : U64) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s) (hcpu : L.mem s (affA t) ∈ Cs) (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' => L.ksb s' = L.ksb s ∧ ∀ b, Aligned b →
      L.mem s' b = dbgRmM (L.mem s) (dbgHd (L := L) s (L.mem s (affA t))) t b ⦄ := by
  have hal : ∀ y ∈ T, Aligned (dnA y) ∧ Aligned (dpA y) := fun y hy =>
    ⟨field_aligned (hT y hy) (by simp) (by simp), field_aligned (hT y hy) (by simp) (by simp)⟩
  have hb0 : Aligned (L.nodeAt s (L.mem s (affA t)) layout.node.DEBUG_TCBS) :=
    nodeAt_aligned (hN _ hcpu) (by simp [debug_val]) (by simp [debug_val])
  have tpv : Tz T (L.mem s (dpA t)) := hD.dp t ht
  have tnx : Tz T (L.mem s (dnA t)) := hD.dn t ht
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  subst ecpu ehd enx epv
  refine WP.spec_bind (Pₘ := fun s1 => L.ksb s1 = L.ksb s ∧ ∀ b, Aligned b → L.mem s1 b =
      (if L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.DEBUG_TCBS) = t
        then updW (L.mem s) (L.nodeAt s (L.mem s (affA t)) layout.node.DEBUG_TCBS) (L.mem s (dnA t))
        else if L.mem s (dpA t) ≠ 0#u64 then updW (L.mem s) (dnA (L.mem s (dpA t))) (L.mem s (dnA t))
        else L.mem s) b) ?_ ?_
  · split
    · rename_i hht
      refine WP.spec_mono (obj.node_set.spec s _ _ _) fun s1 e => ?_
      subst e
      refine ⟨by simp, fun b hb => ?_⟩
      rw [L.mem_wr _ _ _ _ hb0 hb]; rfl
    · rename_i hht
      split
      · rename_i hp
        have hp' : L.mem s (dpA t) ≠ 0#u64 := by simpa using hp
        have hpT := tpv.ne0 hp'
        refine WP.spec_mono (obj.Tcb.set_debug_next.wr s _ _) fun s1 e => ?_
        subst e
        refine ⟨by simp, fun b hb => ?_⟩
        rw [L.mem_wr _ _ _ _ (hal _ hpT).1 hb, if_pos hp']; rfl
      · rename_i hp
        have hp' : ¬ L.mem s (dpA t) ≠ 0#u64 := by simpa using hp
        exact (WP.spec_ok _).2 ⟨rfl, fun b _ => by rw [if_neg hp']⟩
  rintro s1 ⟨hk1, h1⟩
  refine WP.spec_bind (Pₘ := fun s2 => L.ksb s2 = L.ksb s ∧ ∀ b, Aligned b → L.mem s2 b =
      (if L.mem s (dnA t) ≠ 0#u64 then updW (fun b => L.mem s1 b) (dpA (L.mem s (dnA t))) (L.mem s (dpA t))
        else fun b => L.mem s1 b) b) ?_ ?_
  · split
    · rename_i hn
      have hn' : L.mem s (dnA t) ≠ 0#u64 := by simpa using hn
      have hnT := tnx.ne0 hn'
      refine WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 _ _) fun s2 e => ?_
      subst e
      refine ⟨by simp [hk1], fun b hb => ?_⟩
      rw [L.mem_wr _ _ _ _ (hal _ hnT).2 hb, if_pos hn']; rfl
    · rename_i hn
      have hn' : ¬ L.mem s (dnA t) ≠ 0#u64 := by simpa using hn
      exact (WP.spec_ok _).2 ⟨hk1, fun b _ => by rw [if_neg hn']⟩
  rintro s2 ⟨hk2, h2⟩
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  refine ⟨by simp [hk2], fun b hb => ?_⟩
  rw [L.mem_wr _ _ _ _ (hal t ht).1 hb, L.mem_wr _ _ _ _ (hal t ht).2 hb, h2 b hb]
  unfold dbgRmM updW
  by_cases hn : L.mem s (dnA t) ≠ 0#u64
  · simp only [if_pos hn]
    by_cases e : dpA (L.mem s (dnA t)) = b
    · simp [e]
    · simp only [if_neg e]; rw [h1 b hb]; rfl
  · simp only [if_neg hn]; rw [h1 b hb]; rfl

/-- **`debug_remove t` at the state level** (module docstring): the lists
after are the lists before with `t` erased. -/
theorem debug_remove_wf {T Cs : Set U64} (s : S) (t : U64) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s) (hcpu : L.mem s (affA t) ∈ Cs) (ht : t ∈ T)
    {lst : U64 → List U64} (hW : DbgWFL T Cs (L.mem s) (dbgHd (L := L) s) lst) :
    objects.debug_remove st s t ⦃ s' => L.ksb s' = L.ksb s ∧
      DbgWFL T Cs (L.mem s') (dbgHd (L := L) s') (fun c => (lst c).erase t) ⦄ := by
  refine WP.spec_mono (debug_remove_mem s t hT hN hD hcpu ht) fun s' ⟨hk, hm⟩ => ⟨hk, ?_⟩
  have hA := dbgApart_of (L := L) hT hN
  have h1 := dbgRm_wf hW hA ht (by have := (hT t ht).ne0; intro e; exact this (by rw [e]; rfl)) hcpu
    (fun h => (hD.dp t ht).ne0 h) (fun h => (hD.dn t ht).ne0 h)
  refine h1.congr (fun y hy => ⟨hm _ (field_aligned (hT y hy) (by simp) (by simp)),
    hm _ (field_aligned (hT y hy) (by simp) (by simp)), hm _ (field_aligned (hT y hy) (by simp) (by simp))⟩)
    (fun c hc => by rw [dbgHd_of_ksb hk]; exact hm _ (nodeAt_aligned (hN c hc) (by simp [debug_val]) (by simp [debug_val])))

end Store

section Walk
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-! ## Debug-list walks (moved from XTopJointWJLFinT, KENTRY-PLAN g2i) -/

/-- `dbgNth` one step further, from the end. -/
theorem dbgNth_succ' (m : U64 → U64) (n : Nat) (h : U64) :
    dbgNth m (n + 1) h = (if dbgNth m n h = 0#u64 then 0#u64 else m (P1.dnA (dbgNth m n h))) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    by_cases h0 : h = 0#u64
    · subst h0; simp [dbgNth]
    · rw [show dbgNth m (n + 1 + 1) h = dbgNth m (n + 1) (m (P1.dnA h)) by simp [dbgNth, h0], ih,
        show dbgNth m (n + 1) h = dbgNth m n (m (P1.dnA h)) by simp [dbgNth, h0]]

/-- **A debug-list walk stays on the list** (`DbgWFL`). -/
theorem dbgNth_mem_wf {T Cs : Set U64} {m hd : U64 → U64} {lst : U64 → List U64}
    (hW : DbgWFL T Cs m hd lst) {c : U64} (hc : c ∈ Cs) (n : Nat) :
    dbgNth m n (m (hd c)) = 0#u64 ∨ dbgNth m n (m (hd c)) ∈ lst c := by
  induction n with
  | zero =>
    show m (hd c) = 0#u64 ∨ m (hd c) ∈ lst c
    rw [hW.head c hc]
    cases lst c with
    | nil => exact Or.inl rfl
    | cons a r => exact Or.inr (by simp)
  | succ n ih =>
    rw [dbgNth_succ']
    split
    · exact Or.inl rfl
    · rename_i h0
      rw [hW.next c hc _ (ih.resolve_left h0)]
      exact nextIn_mem _ _

theorem nextIn_getElem {l : List U64} (hnd : l.Nodup) {i : Nat} (hi : i + 1 < l.length) :
    nextIn l (l[i]'(by omega)) = l[i + 1] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.1 hnd
    cases i with
    | zero =>
      cases r with
      | nil => simp at hi
      | cons b r' => simp [nextIn]
    | succ j =>
      have hj : j + 1 < r.length := by simp at hi; omega
      have hne : a ≠ r[j] := fun e => ha (by rw [e]; exact List.getElem_mem _)
      simp only [List.getElem_cons_succ, nextIn, if_neg hne]
      exact ih hr hj

theorem headD_getElem0 (l : List U64) (hi : 0 < l.length) : l.headD 0#u64 = l[0] := by
  cases l with
  | nil => simp at hi
  | cons a r => rfl

/-- **A debug-list walk visits the list in order** (`DbgWFL`). -/
theorem dbgNth_getElem_wf {T Cs : Set U64} {m hd : U64 → U64} {lst : U64 → List U64}
    (hW : DbgWFL T Cs m hd lst) {c : U64} (hc : c ∈ Cs) :
    ∀ i (hi : i < (lst c).length), dbgNth m i (m (hd c)) = (lst c)[i] := by
  intro i
  induction i with
  | zero =>
    intro hi
    show m (hd c) = _
    rw [hW.head c hc]
    exact headD_getElem0 _ hi
  | succ i ih =>
    intro hi
    have hi' : i < (lst c).length := by omega
    rw [dbgNth_succ', ih hi']
    have hz : (lst c)[i] ≠ 0#u64 := fun e => hW.zero c hc (by rw [← e]; exact List.getElem_mem hi')
    rw [if_neg hz, hW.next c hc _ (List.getElem_mem hi')]
    exact nextIn_getElem (hW.nodup c hc) hi

/-- **`LiveJ.of_sameZ` with the debug list shrunk** (module docstring): every
debug-list member after one before. -/
theorem LiveJ.of_sameDbg {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hmem : ∀ y ∈ G.chains.flatten, IsSlot th y) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hid : σ'.idleThread = σ.idleThread) (hks : L.ksb s' = L.ksb s)
    (hdbg : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') ≠ 0#u64 → ∃ k,
      dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) ∧
      dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ 0#u64)
    (hdead : ∀ p ∈ ZTcb (L := L) th s, DeadP (L := L) H s' p) :
    LiveJ (L := L) th H G s' σ' := by
  have hU : ∀ y, IsSlot th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    unfold InUse at hu ⊢
    rw [hSS.capV hy, horig] at hu
    exact hu
  refine ⟨fun q i hqi hu => ?_, fun n hn hni => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => ?_⟩
  · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu) with ⟨y, hy, hr⟩ | hb
    · exact Or.inl ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
    · exact Or.inr (by rw [hks]; exact hb)
  · obtain ⟨k, hk, hk0⟩ := hdbg n hn
    obtain ⟨y, hy, hr⟩ := hL.dbg k hk0 (by rw [← hk, ← hid]; exact hni)
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy), hk]; exact hr⟩
  · exact hL.zslots y hy p zt n (by rw [← hSS.capV hy]; exact hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
  · exact hdead p ⟨y, hy, zt, n, by rw [← hSS.capV hy]; exact hz, hzt⟩

end Walk

end Fl4Proofs.P3
