/-
P3 (DESIGN.md §9), invariant line G1 (sb1): **the binding writers** (spec side
only; imports the generated frames SpecInvSbF4).

* The binding view `bv k p` (a TCB's `tcbSchedContext`, an SC's `scTcb`, or
  neither) and `SymB` (both directions of the binding on the view);
  `scInv_iff : ScInv σ ↔ SymB (bv σ.kheap) ∧ RNE σ`. `BR` keeps the view
  exactly (`bv_of_br`) and `RNE` (`rne_of_br`).
* The two writes (`wr_tcbSc`: `set_tcb_obj_ref tcb_sched_context_update`,
  `wr_scTcb`: `set_sc_obj_ref sc_tcb_update`) update the view at one address.
* The view algebra: `symB_unbind` (unbinding a bound pair), `symB_bind` (binding
  two unbound objects, or a pair already bound to each other).
* The writers: `sik_schedContextUnbindTcb`, `sik_maybeReturnSc`,
  `sik_schedContextSetInactive` (no premise: the bound pair is read from the
  state), `sikp_schedContextDonate` (the receiving TCB unbound: every caller
  tests it, l4v `sched_context_donate`'s precondition
  `bound_sc_tcb_at ((=) None) dest`), `sikp_schedContextBindTcb` (both
  unbound or bound to each other: the decode's test, l4v
  `sched_context_bind_tcb`'s precondition).
-/
import Fl4Proofs.P3.SpecInvSbF4
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The binding view -/

inductive BV where
  | t (o : Option ObjRef)
  | s (o : Option ObjRef)
  | o

def bv (k : KHeap) (p : ObjRef) : BV :=
  match k p with
  | some (.tcb x) => .t x.tcbSchedContext
  | some (.schedContext y _) => .s y.scTcb
  | _ => .o

theorem bv_t {k : KHeap} {u : ObjRef} {o : Option ObjRef} :
    bv k u = .t o ↔ ∃ x, k u = some (.tcb x) ∧ x.tcbSchedContext = o := by
  unfold bv
  rcases h : k u with _ | ob
  · simp
  · cases ob <;> simp

theorem bv_s {k : KHeap} {u : ObjRef} {o : Option ObjRef} :
    bv k u = .s o ↔ ∃ y n, k u = some (.schedContext y n) ∧ y.scTcb = o := by
  unfold bv
  rcases h : k u with _ | ob
  · simp
  · cases ob <;> simp

/-- Both directions of the binding on the view. -/
def SymB (b : ObjRef → BV) : Prop :=
  (∀ u c, b u = .t (some c) → b c = .s (some u)) ∧ (∀ p u, b p = .s (some u) → b u = .t (some p))

theorem scInv_iff {σ : State Unit} : ScInv σ ↔ SymB (bv σ.kheap) ∧ RNE σ := by
  constructor
  · rintro ⟨⟨hB, hF⟩, hR⟩
    refine ⟨⟨fun u c h => ?_, fun p u h => ?_⟩, hR⟩
    · obtain ⟨x, hx, hc⟩ := bv_t.1 h
      obtain ⟨y, k, hy, hyt, -⟩ := hB u x c hx hc
      exact bv_s.2 ⟨y, k, hy, hyt⟩
    · obtain ⟨y, n, hy, hu⟩ := bv_s.1 h
      obtain ⟨x, hx, hxc⟩ := hF p y n u hy hu
      exact bv_t.2 ⟨x, hx, hxc⟩
  · rintro ⟨⟨hB, hF⟩, hR⟩
    refine ⟨⟨fun u xu c hk hc => ?_, fun p y n u hk hu => ?_⟩, hR⟩
    · obtain ⟨y, k, hy, hyt⟩ := bv_s.1 (hB u c (bv_t.2 ⟨xu, hk, hc⟩))
      exact ⟨y, k, hy, hyt, hR c y k hy⟩
    · obtain ⟨x, hx, hxc⟩ := bv_t.1 (hF p u (bv_s.2 ⟨y, n, hk, hu⟩))
      exact ⟨x, hx, hxc⟩

theorem bv_of_br {k k' : KHeap} (h : BR k k') : bv k' = bv k := by
  funext q
  have A : ∀ o, bv k q = .t o ↔ bv k' q = .t o := by
    intro o; constructor
    · intro hb
      obtain ⟨x, hx, e⟩ := bv_t.1 hb
      obtain ⟨x', hx', e'⟩ := h.tcb q x hx
      exact bv_t.2 ⟨x', hx', e'.trans e⟩
    · intro hb
      obtain ⟨x', hx', e⟩ := bv_t.1 hb
      obtain ⟨x, hx⟩ := h.tcb' q x' hx'
      obtain ⟨x'', hx'', e''⟩ := h.tcb q x hx
      rw [hx'] at hx''; cases hx''
      exact bv_t.2 ⟨x, hx, e''.symm.trans e⟩
  have B : ∀ o, bv k q = .s o ↔ bv k' q = .s o := by
    intro o; constructor
    · intro hb
      obtain ⟨y, n, hy, e⟩ := bv_s.1 hb
      obtain ⟨y', n', hy', k1, -⟩ := h.sc q y n hy
      exact bv_s.2 ⟨y', n', hy', k1.trans e⟩
    · intro hb
      obtain ⟨y', n', hy', e⟩ := bv_s.1 hb
      obtain ⟨y, n, hy⟩ := h.sc' q y' n' hy'
      obtain ⟨y'', n'', hy'', k1, -⟩ := h.sc q y n hy
      rw [hy'] at hy''
      simp only [Option.some.injEq, KernelObject.schedContext.injEq] at hy''
      obtain ⟨rfl, rfl⟩ := hy''
      exact bv_s.2 ⟨y, n, hy, k1.symm.trans e⟩
  cases hb : bv k q with
  | t o => exact (A o).1 hb
  | s o => exact (B o).1 hb
  | o =>
    cases hb' : bv k' q with
    | t o => rw [(A o).2 hb'] at hb; cases hb
    | s o => rw [(B o).2 hb'] at hb; cases hb
    | o => rfl

theorem rne_of_br {σ σ' : State Unit} (hb : BR σ.kheap σ'.kheap) (hR : RNE σ) : RNE σ' := by
  intro p y n hk
  obtain ⟨y0, n0, hy0⟩ := hb.sc' p y n hk
  obtain ⟨y1, n1, hy1, -, -, k3⟩ := hb.sc p y0 n0 hy0
  rw [hk] at hy1; cases hy1
  exact k3 (hR p y0 n0 hy0)

/-! ## Membership -/

theorem mem_gets' {α : Type} {f : State Unit → α} {σ : State Unit} {y : α × State Unit}
    (h : y ∈ (NonDet.gets f σ).1) : y = (f σ, σ) := Set.mem_singleton_iff.1 h

theorem mem_assertOpt' {α : Type} {o : Option α} {σ : State Unit} {y : α × State Unit}
    (h : y ∈ (NonDet.assertOpt o σ).1) : o = some y.1 ∧ y.2 = σ := by
  cases o with
  | none => exact h.elim
  | some a => rw [Set.mem_singleton_iff.1 h]; exact ⟨rfl, rfl⟩

theorem mem_getSchedContext' {p : ObjRef} {σ : State Unit} {y : SchedContext × State Unit}
    (h : y ∈ (getSchedContext (Z := Unit) p σ).1) : y.2 = σ ∧ ∃ n, σ.kheap p = some (.schedContext y.1 n) := by
  unfold getSchedContext at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨o, z2⟩ := z
  simp only at hk hs; subst z2
  cases o with
  | schedContext sc n =>
    rw [Set.mem_singleton_iff.1 h]; exact ⟨rfl, n, hk⟩
  | _ => exact h.elim

theorem mem_getTcbSc {p : ObjRef} {σ : State Unit} {y : Option ObjRef × State Unit}
    (h : y ∈ (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext p σ).1) :
    y.2 = σ ∧ ∃ x, σ.kheap p = some (.tcb x) ∧ x.tcbSchedContext = y.1 := by
  unfold getTcbObjRef threadGet at h
  obtain ⟨z, hz, h⟩ := h
  unfold NonDet.getsThe at hz
  cases e : getTcb p σ with
  | none => rw [e] at hz; exact hz.elim
  | some x =>
    rw [e] at hz
    rw [Set.mem_singleton_iff.1 hz] at h
    rw [Set.mem_singleton_iff.1 h]
    exact ⟨rfl, x, getTcb_kheap e, rfl⟩

theorem mem_getScTcb {p : ObjRef} {σ : State Unit} {y : Option ObjRef × State Unit}
    (h : y ∈ (getScObjRef (Z := Unit) SchedContext.scTcb p σ).1) :
    y.2 = σ ∧ ∃ sc n, σ.kheap p = some (.schedContext sc n) ∧ sc.scTcb = y.1 := by
  unfold getScObjRef at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨e, n, hk⟩ := mem_getSchedContext' hz
  rw [Set.mem_singleton_iff.1 h]
  exact ⟨e, z.1, n, hk, rfl⟩

theorem mem_threadSet {f : Tcb → Tcb} {t : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ y.2 = { σ with kheap := Function.update σ.kheap t (some (.tcb (f x))) } := by
  unfold threadSet at h
  obtain ⟨z, hz, h⟩ := h
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some x =>
    rw [e] at hz
    rw [Set.mem_singleton_iff.1 hz] at h
    obtain ⟨old, -, -, e2⟩ := mem_setObject h
    exact ⟨x, getTcb_kheap e, e2⟩

theorem mem_bind_sbk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ h0, SBK h0 m) {σ : State Unit} {x : β × State Unit} (hx : x ∈ ((m >>= g) σ).1) :
    ∃ y : α × State Unit, BR σ.kheap y.2.kheap ∧ x ∈ (g y.1 y.2).1 := by
  obtain ⟨y, hy, hx⟩ := hx
  exact ⟨y, br_mem_of_sbk hm hy, hx⟩

/-! ## The two writes on the view -/

theorem bv_upd_tcb {k : KHeap} {t : ObjRef} {x : Tcb} :
    bv (Function.update k t (some (.tcb x))) = Function.update (bv k) t (.t x.tcbSchedContext) := by
  funext q
  by_cases e : q = t
  · subst e; simp [bv]
  · simp only [bv, Function.update_of_ne e]

theorem bv_upd_sc {k : KHeap} {c : ObjRef} {y : SchedContext} {n : Nat} :
    bv (Function.update k c (some (.schedContext y n))) = Function.update (bv k) c (.s y.scTcb) := by
  funext q
  by_cases e : q = c
  · subst e; simp [bv]
  · simp only [bv, Function.update_of_ne e]

theorem wr_tcbSc {t : ObjRef} {v : Option ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (setTcbObjRef (Z := Unit) tcbSchedContextUpdate t v σ).1) :
    (∃ o, bv σ.kheap t = .t o) ∧ bv y.2.kheap = Function.update (bv σ.kheap) t (.t v) ∧ (RNE σ → RNE y.2) := by
  obtain ⟨x, hk, e⟩ := mem_threadSet h
  rw [e]
  refine ⟨⟨_, bv_t.2 ⟨x, hk, rfl⟩⟩, bv_upd_tcb, fun hR p y' n hp => ?_⟩
  by_cases ep : p = t
  · subst ep; simp at hp
  · rw [show ({ σ with kheap := Function.update σ.kheap t (some (.tcb (tcbSchedContextUpdate (fun _ => v) x))) } :
        State Unit).kheap p = σ.kheap p from Function.update_of_ne ep _ _] at hp
    exact hR p y' n hp

theorem wr_scTcb {c : ObjRef} {v : Option ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (setScObjRef (Z := Unit) scTcbUpdate c v σ).1) :
    (∃ o, bv σ.kheap c = .s o) ∧ bv y.2.kheap = Function.update (bv σ.kheap) c (.s v) ∧ (RNE σ → RNE y.2) := by
  obtain ⟨sc, n, hk, e⟩ := mem_updateSchedContext h
  rw [e]
  refine ⟨⟨_, bv_s.2 ⟨sc, n, hk, rfl⟩⟩, bv_upd_sc, fun hR p y' n' hp => ?_⟩
  by_cases ep : p = c
  · subst ep
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact hR p sc n hk
  · rw [show ({ σ with kheap := Function.update σ.kheap c (some (.schedContext (scTcbUpdate (fun _ => v) sc) n)) } :
        State Unit).kheap p = σ.kheap p from Function.update_of_ne ep _ _] at hp
    exact hR p y' n' hp

/-! ## The view algebra -/

theorem symB_unbind {b : ObjRef → BV} (h : SymB b) {t c : ObjRef} (ht : b t = .t (some c)) :
    SymB (Function.update (Function.update b t (.t none)) c (.s none)) := by
  have hc : b c = .s (some t) := h.1 t c ht
  have htc : t ≠ c := by rintro rfl; rw [ht] at hc; cases hc
  obtain ⟨hB, hF⟩ := h
  refine ⟨fun u c' hu => ?_, fun p u hp => ?_⟩
  · by_cases e1 : u = c
    · subst e1; simp at hu
    · rw [Function.update_of_ne e1] at hu
      by_cases e2 : u = t
      · subst e2; simp at hu
      · rw [Function.update_of_ne e2] at hu
        have h1 := hB u c' hu
        have hc' : c' ≠ c := by rintro rfl; rw [hc] at h1; cases h1; exact e2 rfl
        have hct : c' ≠ t := by rintro rfl; rw [ht] at h1; cases h1
        rw [Function.update_of_ne hc', Function.update_of_ne hct]; exact h1
  · by_cases e1 : p = c
    · subst e1; simp at hp
    · rw [Function.update_of_ne e1] at hp
      by_cases e2 : p = t
      · subst e2; simp at hp
      · rw [Function.update_of_ne e2] at hp
        have h1 := hF p u hp
        have hu1 : u ≠ t := by rintro rfl; rw [ht] at h1; cases h1; exact e1 rfl
        have hu2 : u ≠ c := by rintro rfl; rw [hc] at h1; cases h1
        rw [Function.update_of_ne hu2, Function.update_of_ne hu1]; exact h1

theorem symB_bind {b : ObjRef → BV} (h : SymB b) {t c : ObjRef}
    (ht : b t = .t none ∨ b t = .t (some c)) (hc : b c = .s none ∨ b c = .s (some t)) :
    SymB (Function.update (Function.update b t (.t (some c))) c (.s (some t))) := by
  have htc : t ≠ c := by
    rintro rfl; rcases ht with ht | ht <;> rcases hc with hc | hc <;> rw [ht] at hc <;> cases hc
  obtain ⟨hB, hF⟩ := h
  refine ⟨fun u c' hu => ?_, fun p u hp => ?_⟩
  · by_cases e1 : u = c
    · subst e1; simp at hu
    · rw [Function.update_of_ne e1] at hu
      by_cases e2 : u = t
      · subst e2; simp at hu; subst hu; simp
      · rw [Function.update_of_ne e2] at hu
        have h1 := hB u c' hu
        have hc' : c' ≠ c := by
          rintro rfl; rcases hc with hc | hc <;> rw [hc] at h1 <;> cases h1; exact e2 rfl
        have hct : c' ≠ t := by rintro rfl; rcases ht with ht | ht <;> rw [ht] at h1 <;> cases h1
        rw [Function.update_of_ne hc', Function.update_of_ne hct]; exact h1
  · by_cases e1 : p = c
    · subst e1; simp at hp; subst hp
      rw [Function.update_of_ne htc]; simp
    · rw [Function.update_of_ne e1] at hp
      by_cases e2 : p = t
      · subst e2; simp at hp
      · rw [Function.update_of_ne e2] at hp
        have h1 := hF p u hp
        have hu1 : u ≠ t := by
          rintro rfl; rcases ht with ht | ht <;> rw [ht] at h1 <;> cases h1; exact e1 rfl
        have hu2 : u ≠ c := by rintro rfl; rcases hc with hc | hc <;> rw [hc] at h1 <;> cases h1
        rw [Function.update_of_ne hu2, Function.update_of_ne hu1]; exact h1

/-! ## The writers -/

theorem sik_schedContextUnbindTcb (scPtr : ObjRef) : SIK (schedContextUnbindTcb (Z := Unit) scPtr) := by
  intro σ hσ x hx
  rw [scInv_iff] at hσ ⊢
  unfold schedContextUnbindTcb at hx
  obtain ⟨⟨sc, s1⟩, hy1, hx⟩ := hx
  obtain ⟨e1, n, hk⟩ := mem_getSchedContext' hy1
  simp only at e1 hk; subst s1
  obtain ⟨⟨tp, s2⟩, hy2, hx⟩ := hx
  obtain ⟨e2, e2'⟩ := mem_assertOpt' hy2
  simp only at e2 e2'; subst s2
  obtain ⟨⟨cur, s3⟩, hy3, hx⟩ := hx
  have e3 := (Prod.mk.inj (mem_gets' hy3)).2
  (try simp only at e3); subst s3
  obtain ⟨y4, hb4, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y5, hb5, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y6, hb6, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y7, hy7, hx⟩ := hx
  obtain ⟨-, w1, r1⟩ := wr_tcbSc hy7
  obtain ⟨-, w2, r2⟩ := wr_scTcb hx
  have hb : BR σ.kheap y6.2.kheap := BR.trans hb4 (BR.trans hb5 hb6)
  have hcs : bv σ.kheap scPtr = .s (some tp) := bv_s.2 ⟨sc, n, hk, e2⟩
  have hts : bv σ.kheap tp = .t (some scPtr) := hσ.1.2 scPtr tp hcs
  refine ⟨?_, r2 (r1 (rne_of_br hb hσ.2))⟩
  rw [w2, w1, bv_of_br hb]
  exact symB_unbind hσ.1 hts

theorem bv_upd_keep {p : ObjRef} {f : SchedContext → SchedContext}
    {σ : State Unit} {x : Unit × State Unit} (hx : x ∈ (updateSchedContext (Z := Unit) p f σ).1)
    (hf : ∀ y, (f y).scTcb = y.scTcb) :
    bv x.2.kheap = bv σ.kheap ∧ (∀ q, q ≠ p → x.2.kheap q = σ.kheap q) := by
  obtain ⟨y, n, hk, e⟩ := mem_updateSchedContext hx
  rw [e]
  refine ⟨?_, fun q hq => Function.update_of_ne hq _ _⟩
  show bv (Function.update σ.kheap p (some (.schedContext (f y) n))) = bv σ.kheap
  rw [bv_upd_sc, hf y]
  exact Function.update_eq_self_iff.2 (bv_s.2 ⟨y, n, hk, rfl⟩).symm

theorem sik_schedContextSetInactive (p : ObjRef) : SIK (schedContextSetInactive (Z := Unit) p) := by
  intro σ hσ x hx
  rw [scInv_iff] at hσ ⊢
  unfold schedContextSetInactive at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨b1, o1⟩ := bv_upd_keep hy1 (fun _ => rfl)
  obtain ⟨b2, o2⟩ := bv_upd_keep hy2 (fun _ => rfl)
  obtain ⟨b3, o3⟩ := bv_upd_keep hy3 (fun _ => rfl)
  obtain ⟨b4, o4⟩ := bv_upd_keep hx (fun _ => rfl)
  refine ⟨by rw [b4, b3, b2, b1]; exact hσ.1, fun q y n hq => ?_⟩
  by_cases e : q = p
  · subst e
    obtain ⟨a4, n4, k4, e4⟩ := mem_updateSchedContext hx
    obtain ⟨a3, n3, k3, e3⟩ := mem_updateSchedContext hy3
    obtain ⟨a2, n2, k2, e2⟩ := mem_updateSchedContext hy2
    rw [e4] at hq
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hq
    obtain ⟨rfl, -⟩ := hq
    rw [e3] at k4
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at k4
    obtain ⟨rfl, -⟩ := k4
    rw [e2] at k3
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at k3
    obtain ⟨rfl, -⟩ := k3
    intro h
    rcases h with h | h
    · cases h
    · simp [scActive, activeSc, scSporadicUpdate, scBudgetUpdate, scRefillMaxUpdate] at h
  · rw [o4 q e, o3 q e, o2 q e, o1 q e] at hq
    exact hσ.2 q y n hq

theorem sik_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : SIK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  intro σ hσ x hx
  rw [scInv_iff] at hσ ⊢
  unfold maybeReturnSc at hx
  obtain ⟨⟨nsc, s1⟩, hy1, hx⟩ := hx
  have e1 : s1 = σ := (show IK (fun s => s = σ) (getNtfnObjRef (Z := Unit) Notification.ntfnSc ntfnPtr) by
    rd_auto) σ rfl _ hy1
  subst s1
  obtain ⟨⟨tsc, s2⟩, hy2, hx⟩ := hx
  obtain ⟨e2, xt, hxt, htsc⟩ := mem_getTcbSc hy2
  simp only at e2 htsc; subst s2
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · rename_i hc
    obtain ⟨⟨sp, s3⟩, hy3, hx⟩ := hx
    obtain ⟨e3, e3'⟩ := mem_assertOpt' hy3
    simp only at e3 e3'; subst s3
    obtain ⟨y4, hy4, hx⟩ := hx
    obtain ⟨-, w4, r4⟩ := wr_tcbSc hy4
    obtain ⟨y5, hy5, hx⟩ := hx
    obtain ⟨-, w5, r5⟩ := wr_scTcb hy5
    have hb := br_mem_of_sbk (fun _ => by sb_auto) hx
    have hts : bv σ.kheap tcbPtr = .t (some sp) := bv_t.2 ⟨xt, hxt, by rw [htsc, ← hc.1, e3]⟩
    refine ⟨?_, rne_of_br hb (r5 (r4 hσ.2))⟩
    rw [bv_of_br hb, w5, w4]
    exact symB_unbind hσ.1 hts
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

theorem finish_donate {B1 : ObjRef → BV} {t c : ObjRef} (hS : SymB (Function.update B1 c (.s none)))
    (ht : B1 t = .t none) (htc : t ≠ c) :
    SymB (Function.update (Function.update B1 c (.s (some t))) t (.t (some c))) := by
  have h := symB_bind hS (t := t) (c := c) (Or.inl (by rw [Function.update_of_ne htc]; exact ht))
    (Or.inl (by simp))
  have e : Function.update (Function.update B1 c (.s (some t))) t (.t (some c)) =
      Function.update (Function.update (Function.update B1 c (.s none)) t (.t (some c))) c (.s (some t)) := by
    funext q
    by_cases h1 : q = t
    · subst h1; simp [Function.update_apply, htc]
    · by_cases h2 : q = c
      · subst h2; simp [Function.update_apply, h1]
      · simp [Function.update_apply, h1, h2]
  rw [e]; exact h

/-- **`sched_context_donate` to an unbound TCB** (or to the SC's own TCB). -/
theorem sikp_schedContextDonate (c t : ObjRef) (σ : State Unit)
    (ht : bv σ.kheap t = .t none ∨ bv σ.kheap t = .t (some c)) :
    ScInv σ → ∀ x, x ∈ (schedContextDonate (Z := Unit) c t σ).1 → ScInv x.2 := by
  intro hσ x hx
  rw [scInv_iff] at hσ ⊢
  unfold schedContextDonate at hx
  obtain ⟨⟨fo, s1⟩, hy1, hx⟩ := hx
  obtain ⟨e1, sc, n, hk, hfo⟩ := mem_getScTcb hy1
  simp only at e1 hfo; subst s1
  have hcs : bv σ.kheap c = .s fo := bv_s.2 ⟨sc, n, hk, hfo⟩
  have htc : t ≠ c := by rintro rfl; rcases ht with ht | ht <;> rw [ht] at hcs <;> cases hcs
  obtain ⟨⟨u, s2⟩, hy2, hx⟩ := hx
  have W : RNE s2 ∧ SymB (Function.update (bv s2.kheap) c (.s none)) ∧ bv s2.kheap t = .t none ∧
      bv s2.kheap c = bv σ.kheap c := by
    dsimp only at hy2
    unfold NonDet.when at hy2
    split at hy2
    · rename_i hne
      obtain ⟨⟨f, s3⟩, hy3, hy2⟩ := hy2
      obtain ⟨e3, e3'⟩ := mem_assertOpt' hy3
      simp only at e3 e3'; subst s3
      obtain ⟨y4, hb4, hy2⟩ := mem_bind_sbk (fun _ => by sb_auto) hy2
      obtain ⟨y5, hb5, hy2⟩ := mem_bind_sbk (fun _ => by sb_auto) hy2
      obtain ⟨y6, hy6, hy2⟩ := hy2
      obtain ⟨-, w6, r6⟩ := wr_tcbSc hy6
      have hb7 := br_mem_of_sbk (fun _ => by sb_auto) hy2
      have hb45 : BR σ.kheap y5.2.kheap := BR.trans hb4 hb5
      have hfc : bv σ.kheap f = .t (some c) := hσ.1.2 c f (by rw [hcs, e3])
      have hfc' : f ≠ c := by rintro rfl; rw [hfc] at hcs; cases hcs
      have hv : bv s2.kheap = Function.update (bv σ.kheap) f (.t none) := by
        rw [bv_of_br hb7, w6, bv_of_br hb45]
      refine ⟨rne_of_br hb7 (r6 (rne_of_br hb45 hσ.2)), ?_, ?_, ?_⟩
      · rw [hv]; exact symB_unbind hσ.1 hfc
      · rw [hv]
        by_cases etf : t = f
        · subst etf; simp
        · rw [Function.update_of_ne etf]
          rcases ht with ht | ht
          · exact ht
          · exfalso; have := hσ.1.1 t c ht; rw [hcs, e3] at this; cases this; exact etf rfl
      · rw [hv, Function.update_of_ne (Ne.symm hfc')]
    · rename_i hn
      have hn' : fo = none := by simpa using hn
      have e2 := (Prod.mk.inj (Set.mem_singleton_iff.1 hy2)).2
      (try simp only at e2); subst s2
      refine ⟨hσ.2, ?_, ?_, rfl⟩
      · rw [show Function.update (bv σ.kheap) c (.s none) = bv σ.kheap from
          Function.update_eq_self_iff.2 (by rw [hcs, hn'])]
        exact hσ.1
      · rcases ht with ht | ht
        · exact ht
        · exfalso; have := hσ.1.1 t c ht; rw [hcs, hn'] at this; cases this
  obtain ⟨y8, hy8, hx⟩ := hx
  obtain ⟨-, w8, r8⟩ := wr_scTcb hy8
  obtain ⟨-, w9, r9⟩ := wr_tcbSc hx
  refine ⟨?_, r9 (r8 W.1)⟩
  rw [w9, w8]
  exact finish_donate W.2.1 W.2.2.1 htc

/-- **`sched_context_bind_tcb` of two unbound objects** (or of a pair already bound
to each other: the decode's test). -/
theorem sikp_schedContextBindTcb (c t : ObjRef) (σ : State Unit)
    (ht : bv σ.kheap t = .t none ∨ bv σ.kheap t = .t (some c))
    (hc : bv σ.kheap c = .s none ∨ bv σ.kheap c = .s (some t)) :
    ScInv σ → ∀ x, x ∈ (schedContextBindTcb (Z := Unit) c t σ).1 → ScInv x.2 := by
  intro hσ x hx
  rw [scInv_iff] at hσ ⊢
  unfold schedContextBindTcb at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨-, w1, r1⟩ := wr_tcbSc hy1
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨-, w2, r2⟩ := wr_scTcb hy2
  have hb := br_mem_of_sbk (fun _ => by sb_auto) hx
  refine ⟨?_, rne_of_br hb (r2 (r1 hσ.2))⟩
  rw [bv_of_br hb, w2, w1]
  exact symB_bind hσ.1 ht hc

end

end Fl4Proofs.P3.SInvB
