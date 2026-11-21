/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch23 (c1)): **the first-phase
spec fact `jMidChooseFact`**: from the dispatch state (`CQ ∧ NQ` of
XTopJointMidRunQ, `CurInv`, `Sched.Inv`), every outcome of the first-phase
invocation `fl4HandleInvocationR rep false false don true cptr` satisfies
`CtOK`: `CurInv`, or the current thread holds no SC.

* `BIV ct c i rq M` on the SC view (`sV`, XTopJointChooseF): `ct` holds a TCB;
  its SC field is `none`, or the current SC `c`, which is an SC, active
  unless it is the idle SC `i`, with `ct` out of the release queue `rq`;
  every TCB's SC is an SC bound back to that TCB (`Inv.back`); no reference
  is both a TCB and an SC. `BI ct σ := BIV ct` of `sV σ`. Every `SV` frame
  keeps it (`BI.of_sV`).
* `PC ct m` / `PCP ct P m`: every outcome of `m` from a `CQ ∧ BI` state (with
  `P`) is `CQ ∧ BI` (PQ-style, carrying the invariant through the steps).
* Hand lemmas: `bi_donate` (`schedContextDonate sc t`, `t ≠ ct`: the old
  holder of `sc` loses its SC field; if it was `ct`, `ct` becomes SC-less),
  `pcp_postpone` / `pcp_resume` (the thread enqueued in the release queue is
  the TCB holding `sc`, `≠ ct`, by `back`), `pc_maybeDonateSc`,
  `pc_replyRemove`, `pc_replyPush`, `pc_sendIpc`, `pc_sendFaultIpc`,
  `pc_handleTimeout`, `pc_sendSignal` (from `NQ`), `pc_doReplyTransfer`.
* `perf_firstB`: every `FirstInv` perform but `PerfW` keeps `CQ ∧ BI`.
  `JMidPerfHypB` [W]: the `PerfW` performs (Untyped, IRQ handler set / clear,
  ASID control) keep `BI` at the states where they start on a run of the
  invocation from the dispatch state (`MidPerfAt`), never for an arbitrary
  state. l4v: `invoke_untyped`, `invoke_irq_handler`,
  `perform_asid_control_invocation` keep `sym_refs` of the SC/TCB binding
  (`valid_objs`, `sym_refs (state_refs_of)`), `cur_sc_tcb_are_bound`,
  `cur_sc_active` and `ct_not_in_release_q` (none of them binds an SC to a
  thread, writes the current SC, or enqueues the current thread in the
  release queue; the retyped region is free).
* `midRunB_shell`, `jMidChooseFact`.
-/
import Fl4Proofs.P3.XTopJointChooseF
import Fl4Proofs.P3.ScCur
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-! ## The invariant on the SC view -/

abbrev MT := ObjRef → Option (Option ObjRef) × Option (Option ObjRef × Nat)

/-- The SC invariant on the view (module docstring). -/
structure BIV (ct c i : ObjRef) (rq : List ObjRef) (M : MT) : Prop where
  dis : ∀ q, (M q).1 = none ∨ (M q).2 = none
  ex : ∃ s, (M ct).1 = some s
  cur : ∀ s, (M ct).1 = some s → s = none ∨ (s = some c ∧ (∃ tm, (M c).2 = some tm) ∧
    (c ≠ i → ∀ tm, (M c).2 = some tm → 0 < tm.2) ∧ ct ∉ rq)
  back : ∀ u p, (M u).1 = some (some p) → ∃ m, (M p).2 = some (some u, m)

/-- The SC invariant of a state. -/
def BI (ct : ObjRef) (σ : State Unit) : Prop := BIV ct σ.curSc σ.idleSc σ.releaseQueue (mV σ)

theorem BI.of_sV {ct : ObjRef} {σ σ' : State Unit} (e : sV σ' = sV σ) (h : BI ct σ) : BI ct σ' := by
  unfold sV at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  unfold BI; rw [e1, e2, e3, e4]; exact h

theorem BIV.rq {ct c i : ObjRef} {rq rq' : List ObjRef} {M : MT} (h : BIV ct c i rq M)
    (hs : ct ∉ rq → ct ∉ rq') : BIV ct c i rq' M :=
  ⟨h.dis, h.ex, fun s hs' => (h.cur s hs').imp_right fun ⟨a, b, c, d⟩ => ⟨a, b, c, hs d⟩, h.back⟩

theorem mV_upd (σ : State Unit) (p : ObjRef) (o : KernelObject) :
    mV { σ with kheap := Function.update σ.kheap p (some o) } =
      Function.update (mV σ) p (tP (some o), cP (some o)) := by
  funext q
  unfold mV
  dsimp only
  by_cases hq : q = p
  · subst hq; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]

theorem mV_tP {σ : State Unit} {u : ObjRef} {x : Tcb} (hk : σ.kheap u = some (.tcb x)) :
    mV σ u = (some x.tcbSchedContext, none) := by
  unfold mV; rw [hk]; rfl

theorem mV_cP {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) : mV σ p = (none, some (y.scTcb, y.scRefillMax)) := by
  unfold mV; rw [hk]; rfl

theorem mV_dis (σ : State Unit) (q : ObjRef) : (mV σ q).1 = none ∨ (mV σ q).2 = none := by
  unfold mV
  cases σ.kheap q with
  | none => exact Or.inl rfl
  | some k => cases k <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem tP_some {σ : State Unit} {u : ObjRef} {s : Option ObjRef} (h : (mV σ u).1 = some s) :
    ∃ x, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = s := by
  unfold mV at h
  revert h
  cases hk : σ.kheap u with
  | none => intro h; cases h
  | some k =>
    intro h
    cases k
    case tcb x => exact ⟨x, rfl, Option.some.inj h⟩
    all_goals cases h

theorem cP_some {σ : State Unit} {p : ObjRef} {tc : Option ObjRef} {m : Nat} (h : (mV σ p).2 = some (tc, m)) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ y.scTcb = tc ∧ y.scRefillMax = m := by
  unfold mV at h
  revert h
  cases hk : σ.kheap p with
  | none => intro h; cases h
  | some k =>
    intro h
    cases k
    case schedContext y n =>
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      exact ⟨y, n, rfl, h'.1, h'.2⟩
    all_goals cases h

theorem mV_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) : mV σ' = mV σ := by
  unfold mV; rw [e]

theorem BI.of_parts {ct : ObjRef} {σ σ' : State Unit} (hb : BI ct σ) (h1 : σ'.curSc = σ.curSc)
    (h2 : σ'.idleSc = σ.idleSc) (h3 : mV σ' = mV σ) (h4 : ct ∉ σ.releaseQueue → ct ∉ σ'.releaseQueue) :
    BI ct σ' := by
  unfold BI; rw [h1, h2, h3]; exact hb.rq h4

/-! ## Membership of the SC writes -/

theorem mem_threadSet' {f : Tcb → Tcb} {t : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ x0, σ.kheap t = some (.tcb x0) ∧ x.2 = { σ with kheap := Function.update σ.kheap t (some (.tcb (f x0))) } := by
  obtain ⟨⟨tcb, s1⟩, h1, hx⟩ := h
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  obtain ⟨-, e⟩ := setObject_out hx
  exact ⟨tcb, getTcb_some e1, e⟩

theorem mem_updSc' {p : ObjRef} {f : SchedContext → SchedContext} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (updateSchedContext (Z := Unit) p f σ).1) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some (.schedContext (f y) n)) } := by
  obtain ⟨⟨k, s1⟩, h1, hx⟩ := h
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  simp only [readObject] at e1
  cases k with
  | schedContext y n =>
    obtain ⟨-, e⟩ := setObject_out hx
    exact ⟨y, n, e1, e⟩
  | _ => exact hx.elim

/-- The SC-field write of a TCB. -/
theorem mem_setTcbSc {u : ObjRef} {v : Option ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (setTcbObjRef (Z := Unit) tcbSchedContextUpdate u v σ).1) :
    (∃ s, mV σ u = (some s, none)) ∧ x.2.curSc = σ.curSc ∧ x.2.idleSc = σ.idleSc ∧
      x.2.releaseQueue = σ.releaseQueue ∧ mV x.2 = Function.update (mV σ) u (some v, none) := by
  obtain ⟨x0, hk, e⟩ := mem_threadSet' h
  rw [e]
  exact ⟨⟨_, mV_tP hk⟩, rfl, rfl, rfl, by rw [mV_upd]; rfl⟩

/-- The bound-TCB write of an SC. -/
theorem mem_setScTcb {p : ObjRef} {v : Option ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (setScObjRef (Z := Unit) scTcbUpdate p v σ).1) :
    (∃ tc m, mV σ p = (none, some (tc, m)) ∧ mV x.2 = Function.update (mV σ) p (none, some (v, m))) ∧
      x.2.curSc = σ.curSc ∧ x.2.idleSc = σ.idleSc ∧ x.2.releaseQueue = σ.releaseQueue := by
  obtain ⟨y, n, hk, e⟩ := mem_updSc' h
  rw [e]
  exact ⟨⟨_, _, mV_cP hk, by rw [mV_upd]; rfl⟩, rfl, rfl, rfl⟩

theorem mem_getScObjRef {f : SchedContext → Option ObjRef} {p : ObjRef} {σ : State Unit}
    {x : Option ObjRef × State Unit} (h : x ∈ (getScObjRef (Z := Unit) f p σ).1) :
    x.2 = σ ∧ ∃ y n, σ.kheap p = some (.schedContext y n) ∧ x.1 = f y := by
  obtain ⟨⟨y, s1⟩, h1, h2⟩ := h
  obtain ⟨⟨k, s0⟩, h0, h1⟩ := h1
  obtain ⟨e0, e0'⟩ := mem_getsThe' h0
  simp only at e0 e0'
  subst e0'
  simp only [readObject] at e0
  cases k with
  | schedContext y' n =>
    have h1 := mem_pure' h1
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have h2 := mem_pure' h2
    subst h2
    exact ⟨rfl, _, _, e0, rfl⟩
  | _ => exact h1.elim

theorem mem_getTcbSc {t : ObjRef} {σ : State Unit} {x : Option ObjRef × State Unit}
    (h : x ∈ (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ).1) : x.2 = σ ∧ (mV σ t).1 = some x.1 := by
  obtain ⟨⟨tcb, s1⟩, h1, h2⟩ := h
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  have h2 := mem_pure' h2
  subst h2
  exact ⟨rfl, by rw [mV_tP (getTcb_some e1)]⟩

theorem mem_modify' {g : State Unit → State Unit} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (NonDet.modify g σ).1) : x = ((), g σ) := Set.mem_singleton_iff.1 h

theorem mem_gets' {α : Type} {g : State Unit → α} {σ : State Unit} {x : α × State Unit}
    (h : x ∈ (NonDet.gets g σ).1) : x = (g σ, σ) := Set.mem_singleton_iff.1 h

/-- The release-queue removal. -/
theorem mem_relRemove {t : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (tcbReleaseRemove (Z := Unit) t σ).1) :
    mV x.2 = mV σ ∧ x.2.curSc = σ.curSc ∧ x.2.idleSc = σ.idleSc ∧
      x.2.releaseQueue = tcbSchedDequeue t σ.releaseQueue := by
  unfold tcbReleaseRemove at h
  obtain ⟨⟨qs, s1⟩, h1, ⟨⟨u, s2⟩, h2, ⟨⟨qs', s3⟩, h3, hx⟩⟩⟩ := h
  have h1 := mem_gets' h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, h1s⟩ := h1
  rw [h1s] at h2
  have e2 : s2.kheap = σ.kheap ∧ s2.curSc = σ.curSc ∧ s2.idleSc = σ.idleSc ∧
      s2.releaseQueue = σ.releaseQueue := by
    unfold NonDet.when at h2
    split at h2
    · have h2 := mem_modify' h2
      simp only [Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have h2 := mem_pure' h2
      simp only [Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      exact ⟨rfl, rfl, rfl, rfl⟩
  have h3 := mem_pure' h3
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hx := mem_modify' hx
  subst hx
  exact ⟨mV_of_kheap e2.1, e2.2.1, e2.2.2.1, rfl⟩

theorem mem_orderedInsert {α β : Type} [Nonempty β] {t : α} {ts : List α} {f : α → RMonad Unit β}
    {R : β → β → Prop} {σ : State Unit} {x : List α × State Unit}
    (h : x ∈ (orderedInsert (Z := Unit) t ts f R σ).1) : ∀ a ∈ x.1, a = t ∨ a ∈ ts := by
  unfold orderedInsert at h
  obtain ⟨⟨v, s1⟩, -, ⟨⟨vs, s2⟩, -, ⟨⟨z, s3⟩, h3, ⟨⟨z', s4⟩, h4, hx⟩⟩⟩⟩ := h
  have h3 := mem_pure' h3
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have h4 := mem_pure' h4
  simp only [Prod.mk.injEq] at h4
  obtain ⟨rfl, rfl⟩ := h4
  have hx := mem_pure' hx
  subst hx
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨⟨b, w⟩, hb, rfl⟩ := ha
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with (hb | hb) | hb
  · first
      | exact Or.inr (List.of_mem_zip ((List.takeWhile_sublist _).subset hb)).1
      | exact Or.inr (List.of_mem_zip ((List.takeWhile_prefix _).subset hb)).1
  · simp only [Prod.mk.injEq] at hb; exact Or.inl hb.1
  · first
      | exact Or.inr (List.of_mem_zip (List.mem_of_mem_dropWhile hb)).1
      | exact Or.inr (List.of_mem_zip ((List.dropWhile_suffix _).subset hb)).1

/-- The release-queue insertion. -/
theorem mem_relEnqueue {t : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (tcbReleaseEnqueue (Z := Unit) t σ).1) :
    mV x.2 = mV σ ∧ x.2.curSc = σ.curSc ∧ x.2.idleSc = σ.idleSc ∧
      ∀ a ∈ x.2.releaseQueue, a = t ∨ a ∈ σ.releaseQueue := by
  unfold tcbReleaseEnqueue at h
  obtain ⟨⟨q, s1⟩, h1, ⟨⟨q', s2⟩, h2, ⟨⟨u, s3⟩, h3, hx⟩⟩⟩ := h
  have h1 := mem_gets' h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, h1s⟩ := h1
  rw [h1s] at h2
  have e2 := sck_readyTimesAppend' t σ.releaseQueue σ _ h2
  have hm : ∀ a ∈ q', a = t ∨ a ∈ σ.releaseQueue := by
    unfold readyTimesAppend at h2
    exact mem_orderedInsert h2
  unfold sV at e2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨e2a, e2b, -, e2d⟩ := e2
  have h3 := mem_modify' h3
  simp only [Prod.mk.injEq] at h3
  obtain ⟨-, rfl⟩ := h3
  have e4 : x.2.kheap = s2.kheap ∧ x.2.curSc = s2.curSc ∧ x.2.idleSc = s2.idleSc ∧
      x.2.releaseQueue = q' := by
    unfold NonDet.when at hx
    split at hx
    · have hx := mem_modify' hx
      subst hx
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have hx := mem_pure' hx
      subst hx
      exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨(mV_of_kheap e4.1).trans e2d, e4.2.1.trans e2a, e4.2.2.1.trans e2b, ?_⟩
  rw [e4.2.2.2]; exact hm

/-! ## `schedContextDonate` -/

set_option maxHeartbeats 1000000 in
/-- The view-level donation (module docstring). -/
theorem biv_donate {ct c i sc t : ObjRef} {rq rq1 : List ObjRef} {M0 M1 M2 M3 : MT} {so2 : Option ObjRef}
    {m2 : Nat} {st : Option ObjRef} (hB : BIV ct c i rq M0) (ht : t ≠ ct)
    (hrq : ∀ a ∈ rq1, a ∈ rq)
    (hM1 : ∀ q, M1 q = M0 q ∨ (M1 q = (some none, none) ∧ ∃ s, M0 q = (some s, none)))
    (h0 : ∀ tc m, M1 sc = (none, some (tc, m)) → tc = none ∨ ∃ f, tc = some f ∧ M1 f = (some none, none))
    (h2s : M1 sc = (none, some (so2, m2))) (h2 : M2 = Function.update M1 sc (none, some (some t, m2)))
    (h3t : M2 t = (some st, none)) (h3 : M3 = Function.update M2 t (some (some sc), none)) :
    BIV ct c i rq1 M3 := by
  have hts : t ≠ sc := by
    intro e; subst e
    rw [h2, Function.update_self] at h3t
    cases h3t
  have hM1t : M1 t = (some st, none) := by rw [h2, Function.update_of_ne hts] at h3t; exact h3t
  have hM0t2 : (M0 t).2 = none := by
    rcases hM1 t with e | ⟨-, s, e'⟩
    · rw [← e, hM1t]
    · rw [e']
  have hM1sc : M1 sc = M0 sc := by
    rcases hM1 sc with e | ⟨e, -⟩
    · exact e
    · rw [h2s] at e; cases e
  have hM3 : ∀ q, M3 q = if q = t then (some (some sc), none) else if q = sc then (none, some (some t, m2))
      else M1 q := by
    intro q; rw [h3, h2]; simp only [Function.update_apply]
  -- a reference with an SC in `M0` keeps it in `M1`
  have hkeep2 : ∀ q tm, (M0 q).2 = some tm → M1 q = M0 q := by
    intro q tm hq
    rcases hM1 q with e | ⟨-, s, e'⟩
    · exact e
    · rw [e'] at hq; cases hq
  have hctsc : ct ≠ sc := by
    intro e; subst e
    obtain ⟨s, hs⟩ := hB.ex
    rw [← hM1sc, h2s] at hs; cases hs
  refine ⟨fun q => ?_, ?_, fun s hs => ?_, fun u p hu => ?_⟩
  · rw [hM3]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
    · rcases hM1 q with e | ⟨e, -⟩
      · rw [e]; exact hB.dis q
      · rw [e]; exact Or.inr rfl
  · rw [hM3, if_neg (Ne.symm ht), if_neg hctsc]
    rcases hM1 ct with e | ⟨e, -⟩
    · rw [e]; exact hB.ex
    · rw [e]; exact ⟨_, rfl⟩
  · rw [hM3, if_neg (Ne.symm ht), if_neg hctsc] at hs
    rcases hM1 ct with e | ⟨e, -⟩
    · rw [e] at hs
      rcases hB.cur s hs with h | ⟨hsc, ⟨tm, htm⟩, hpos, hnr⟩
      · exact Or.inl h
      · right
        have hct : c ≠ t := by intro e'; subst e'; rw [htm] at hM0t2; cases hM0t2
        refine ⟨hsc, ?_, ?_, fun hm => hnr (hrq _ hm)⟩
        · rw [hM3, if_neg hct]
          split_ifs
          · exact ⟨_, rfl⟩
          · rw [hkeep2 c tm htm]; exact ⟨tm, htm⟩
        · intro hci tm' htm'
          rw [hM3, if_neg hct] at htm'
          split_ifs at htm' with hcs
          · subst hcs
            rw [← hM1sc, h2s] at htm
            cases htm
            cases htm'
            exact hpos hci (so2, m2) (by rw [← hM1sc, h2s])
          · rw [hkeep2 c tm htm, htm] at htm'
            cases htm'
            exact hpos hci tm htm
    · rw [e] at hs; cases hs; exact Or.inl rfl
  · by_cases hut : u = t
    · subst hut
      rw [hM3, if_pos rfl] at hu
      obtain rfl : sc = p := by simpa using hu
      rw [hM3, if_neg (Ne.symm hts), if_pos rfl]
      exact ⟨m2, rfl⟩
    by_cases hus : u = sc
    · subst hus
      rw [hM3, if_neg hut, if_pos rfl] at hu
      simp at hu
    rw [hM3, if_neg hut, if_neg hus] at hu
    · rcases hM1 u with e | ⟨e, -⟩
      swap
      · rw [e] at hu; simp at hu
      rw [e] at hu
      obtain ⟨m, hm⟩ := hB.back u p hu
      have hpt : p ≠ t := by intro e'; subst e'; rw [hm] at hM0t2; cases hM0t2
      rw [hM3, if_neg hpt]
      split_ifs with hps
      · subst hps
        rw [← hM1sc, h2s] at hm
        have h5 : so2 = some u := by simp only [Option.some.injEq, Prod.mk.injEq] at hm; exact hm.1
        rcases h0 _ _ h2s with h | ⟨f, hf, hf'⟩
        · rw [h5] at h; cases h
        · rw [h5] at hf; cases hf
          rw [← e, hf'] at hu; simp at hu
      · rw [hkeep2 p _ hm]; exact ⟨m, hm⟩

set_option maxHeartbeats 2000000 in
/-- **`schedContextDonate sc t` keeps `BI`** for `t ≠ ct`, and `t` holds `sc`
afterwards. -/
theorem bi_donate {ct sc t : ObjRef} (ht : t ≠ ct) {σ : State Unit} {x : Unit × State Unit}
    (hB : BI ct σ) (hx : x ∈ (schedContextDonate (Z := Unit) sc t σ).1) :
    BI ct x.2 ∧ (mV x.2 t).1 = some (some sc) := by
  unfold schedContextDonate at hx
  obtain ⟨⟨fo, s1⟩, h1, ⟨⟨u1, s2⟩, h2, ⟨⟨u3, s3⟩, h3, hx⟩⟩⟩ := hx
  obtain ⟨e1, y, n, hk, e1'⟩ := mem_getScObjRef h1
  simp only at e1 e1'
  subst e1'
  subst s1
  have hM0 := mV_cP hk
  have K : s2.curSc = σ.curSc ∧ s2.idleSc = σ.idleSc ∧ (∀ a ∈ s2.releaseQueue, a ∈ σ.releaseQueue) ∧
      (∀ q, mV s2 q = mV σ q ∨ (mV s2 q = (some none, none) ∧ ∃ s, mV σ q = (some s, none))) ∧
      (∀ tc m, mV s2 sc = (none, some (tc, m)) → tc = none ∨ ∃ f, tc = some f ∧ mV s2 f = (some none, none)) := by
    unfold NonDet.when at h2
    split at h2
    · next hne =>
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hne
      try dsimp only at hf
      obtain ⟨⟨f', sa⟩, ha, ⟨⟨_, sb⟩, hb, ⟨⟨_, sc'⟩, hc, ⟨⟨_, sd⟩, hd, he⟩⟩⟩⟩ := h2
      rw [hf] at ha
      have ha := mem_pure' ha
      simp only [Prod.mk.injEq] at ha
      obtain ⟨h5, h6⟩ := ha
      subst f'
      subst sa
      try dsimp only at hb
      try dsimp only at hc
      try dsimp only at hd
      try dsimp only at he
      have eb := sck_tcbSchedAction _ _ _ _ hb
      obtain ⟨ec1, ec2, ec3, ec4⟩ := mem_relRemove hc
      obtain ⟨⟨sf, ed1⟩, ed2, ed3, ed4, ed5⟩ := mem_setTcbSc hd
      have ee := sck_testReschedule _ _ _ he
      unfold sV at eb ee
      simp only [Prod.mk.injEq] at eb ee
      obtain ⟨eb1, eb2, eb3, eb4⟩ := eb
      obtain ⟨ee1, ee2, ee3, ee4⟩ := ee
      have hM2 : mV s2 = Function.update (mV σ) f (some none, none) := by
        rw [ee4, ed5, ec1, eb4] <;> rfl
      have hfsc : f ≠ sc := by
        intro e; subst e
        rw [ec1, eb4, hM0] at ed1; cases ed1
      refine ⟨by rw [ee1, ed2, ec2, eb1], by rw [ee2, ed3, ec3, eb2], fun a ha => ?_, fun q => ?_, fun tc m hm => ?_⟩
      · rw [ee3, ed4, ec4, eb3] at ha
        exact (List.mem_filter.1 ha).1
      · rw [hM2]
        by_cases hq : q = f
        · subst hq
          rw [Function.update_self]
          rw [ec1, eb4] at ed1
          exact Or.inr ⟨rfl, sf, ed1⟩
        · rw [Function.update_of_ne hq]; exact Or.inl rfl
      · rw [hM2, Function.update_of_ne (Ne.symm hfsc), hM0] at hm
        obtain ⟨-, h5⟩ := Prod.mk.inj hm
        obtain ⟨h6, -⟩ := Prod.mk.inj (Option.some.inj h5)
        rw [← h6, hf]
        right
        exact ⟨f, rfl, by rw [hM2, Function.update_self]⟩
    · next hne =>
      have h2 := mem_pure' h2
      simp only [Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      simp only [ne_eq, Decidable.not_not] at hne
      refine ⟨rfl, rfl, fun a ha => ha, fun q => Or.inl rfl, fun tc m hm => ?_⟩
      rw [hM0] at hm
      obtain ⟨-, h5⟩ := Prod.mk.inj hm
      obtain ⟨h6, -⟩ := Prod.mk.inj (Option.some.inj h5)
      rw [← h6, hne]
      exact Or.inl rfl
  obtain ⟨Kc, Ki, Kr, KM, K0⟩ := K
  obtain ⟨⟨to3, m3, e3a, e3b⟩, c3, i3, r3⟩ := mem_setScTcb h3
  obtain ⟨⟨st, e4a⟩, c4, i4, r4, e4b⟩ := mem_setTcbSc hx
  have hB' : BIV ct σ.curSc σ.idleSc x.2.releaseQueue (mV x.2) :=
    biv_donate hB ht (fun a ha => Kr a (by rw [← r3, ← r4]; exact ha)) KM K0 e3a e3b e4a e4b
  refine ⟨?_, by rw [e4b, Function.update_self]⟩
  unfold BI
  rw [c4, c3, Kc, i4, i3, Ki]
  exact hB'

/-! ## The invariant-carrying frame `PC` -/

/-- Every outcome of `m` from a `CQ ∧ BI` state with `P` is `CQ ∧ BI`. -/
def PCP (ct : ObjRef) (P : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, CQ ct σ → BI ct σ → P σ → x ∈ (m σ).1 → CQ ct x.2 ∧ BI ct x.2

abbrev PC (ct : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := PCP ct (fun _ => True) m

/-- The state is unchanged. -/
abbrev RO {α : Type} (m : NonDet (State Unit) α) : Prop := FK (fun σ : State Unit => σ) m

macro "ro_auto" : tactic => `(tactic| repeat' (first | dk_step0 | fv_unfold))

section
variable {ct : ObjRef}

theorem pcp_of {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h1 : PQ ct m) (h2 : SV m) :
    PCP ct P m :=
  fun σ x hq hb _ hx => ⟨h1 σ x hq hx, BI.of_sV (h2 σ x hx) hb⟩

theorem pcp_mk {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h1 : PQ ct m)
    (h2 : ∀ σ x, CQ ct σ → BI ct σ → P σ → x ∈ (m σ).1 → BI ct x.2) : PCP ct P m :=
  fun σ x hq hb hp hx => ⟨h1 σ x hq hx, h2 σ x hq hb hp hx⟩

theorem pcp_weak {P Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : PCP ct Q m)
    (hPQ : ∀ σ, P σ → Q σ) : PCP ct P m :=
  fun σ x hq hb hp hx => h σ x hq hb (hPQ σ hp) hx

theorem pcp_bind {P : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : PCP ct P m) (hf : ∀ a, PC ct (f a)) : PCP ct P (m >>= f) :=
  fun σ x hq hb hp ⟨y, hy, hx⟩ => by
    obtain ⟨a, b⟩ := hm σ y hq hb hp hy
    exact hf y.1 y.2 x a b trivial hx

theorem pcp_bind' {P : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : PCP ct P m) (hf : ∀ a, PC ct (f a)) :
    PCP ct P (NonDet.bind m f) := pcp_bind hm hf

theorem pcp_bind_ro {P : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : RO m) (hf : ∀ a, PCP ct P (f a)) : PCP ct P (m >>= f) :=
  fun σ x hq hb hp ⟨y, hy, hx⟩ => by
    have e : y.2 = σ := hm σ y hy
    rw [← e] at hq hb hp
    exact hf y.1 y.2 x hq hb hp hx

theorem pcp_bind_ro' {P : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : RO m) (hf : ∀ a, PCP ct P (f a)) :
    PCP ct P (NonDet.bind m f) := pcp_bind_ro hm hf

theorem pcp_pure {P : State Unit → Prop} {α : Type} (a : α) : PCP ct P (pure a : NonDet (State Unit) α) :=
  fun σ x hq hb _ hx => by rw [mem_pure' hx]; exact ⟨hq, hb⟩

theorem pcp_pure' {P : State Unit → Prop} {α : Type} (a : α) : PCP ct P (NonDet.pure a : NonDet (State Unit) α) :=
  pcp_pure a

theorem pcp_pure_bind {P : State Unit → Prop} {α β : Type} {a : α} {f : α → NonDet (State Unit) β}
    (h : PCP ct P (f a)) : PCP ct P (pure a >>= f) :=
  fun σ x hq hb hp ⟨y, hy, hx⟩ => by
    have hy := mem_pure' hy
    subst hy
    exact h σ x hq hb hp hx

theorem pcp_fail_bind {P : State Unit → Prop} {α β : Type} {f : α → NonDet (State Unit) β} :
    PCP ct P (NonDet.fail >>= f) :=
  fun _ _ _ _ _ ⟨_, hy, _⟩ => hy.elim

theorem pcp_threadGet_bind {P : State Unit → Prop} {α β : Type} (f : Tcb → α) (t : ObjRef)
    {k : α → NonDet (State Unit) β}
    (hk : ∀ tcb, (t = ct → runnable tcb.tcbState = true ∧ tcb.tcbFault = none) → PCP ct P (k (f tcb))) :
    PCP ct P (threadGet (Z := Unit) f t >>= k) := by
  intro σ x hs hb hp ⟨⟨a, s1⟩, ⟨⟨tcb, s0⟩, h0, h1⟩, hx⟩
  obtain ⟨e0, e0'⟩ := mem_getsThe' h0
  simp only at e0 e0'
  subst e0'
  have h1 := mem_pure' h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hk tcb (fun e => by subst e; exact hs.1.2 tcb (getTcb_some e0)) _ x hs hb hp hx

theorem pcp_gts_bind {P : State Unit → Prop} {β : Type} (t : ObjRef) {k : ThreadState → NonDet (State Unit) β}
    (hk : ∀ ts, (t = ct → runnable ts = true) → PCP ct P (k ts)) :
    PCP ct P (getThreadState (Z := Unit) t >>= k) := by
  unfold getThreadState
  exact pcp_threadGet_bind _ t fun tcb h => hk _ fun e => (h e).1

/-- A read of `t`'s SC field, the value recorded. -/
theorem pcp_getTcbSc_bind {P : State Unit → Prop} {β : Type} (t : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ so, PCP ct (fun σ => P σ ∧ (mV σ t).1 = some so) (k so)) :
    PCP ct P (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= k) :=
  fun σ x hq hb hp ⟨y, hy, hx⟩ => by
    obtain ⟨e, hv⟩ := mem_getTcbSc hy
    rw [← e] at hq hb hp hv
    exact hk y.1 y.2 x hq hb ⟨hp, hv⟩ hx

theorem pcp_assertOpt_bind {P : State Unit → Prop} {α β : Type} (o : Option α) {k : α → NonDet (State Unit) β}
    (hk : ∀ a, o = some a → PCP ct P (k a)) : PCP ct P (NonDet.assertOpt o >>= k) := by
  cases o with
  | none => exact fun _ _ _ _ _ ⟨_, hy, _⟩ => hy.elim
  | some a =>
    intro σ x hq hb hp ⟨y, hy, hx⟩
    have hy := mem_pure' hy
    subst hy
    exact hk a rfl σ x hq hb hp hx

end

macro "pc_step" : tactic => `(tactic| first
  | (refine pcp_of ?h1 ?h2
     case h2 => (sck_auto2; done)
     case h1 => (pq_step; done))
  | exact pcp_of (pq_of (dk_pure _) (PPNQ.qk_pure _)) (dk_pure _)
  | exact pcp_of (pq_of (dk_pure' _) (PPNQ.qk_pure' _)) (dk_pure' _))

/-- Step through binds and branches with `pc_step` and the donating lemmas. -/
macro "pc_auto" : tactic => `(tactic| repeat' (first
  | pc_step
  | exact pc_replyPush _ _ _ _ (by assumption) (by assumption)
  | exact pc_donate _ _ (by assumption)
  | (refine pcp_bind ?_ fun _ => ?_)
  | (refine pcp_bind' ?_ fun _ => ?_)
  | split
  | (unfold NonDet.when)))

/-! ## Release-queue writers and the donating operations -/

section
variable {ct : ObjRef}

/-- **`postpone sc` keeps `BI`** where `sc` is the SC of a thread `≠ ct`. -/
theorem pcp_postpone (sc : ObjRef) :
    PCP ct (fun σ => ∃ u, u ≠ ct ∧ (mV σ u).1 = some (some sc)) (postpone (Z := Unit) sc) := by
  refine pcp_mk (pq_of (kf_postpone' _) (qk_postponeQ _)) fun σ x _ hb ⟨u, hu, hus⟩ hx => ?_
  unfold postpone at hx
  obtain ⟨⟨tc, s1⟩, h1, ⟨⟨tp, s2⟩, h2, ⟨⟨_, s3⟩, h3, ⟨⟨_, s4⟩, h4, hx⟩⟩⟩⟩ := hx
  obtain ⟨e1, y, n, hk, e1'⟩ := mem_getScObjRef h1
  simp only at e1 e1'
  subst e1'
  rw [e1] at h2
  obtain ⟨m, hm⟩ := hb.back u sc hus
  rw [mV_cP hk] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  rw [hm.1] at h2
  have h2 := mem_pure' h2
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have e3 := sck_tcbSchedAction _ _ _ _ h3
  obtain ⟨e4a, e4b, e4c, e4d⟩ := mem_relEnqueue h4
  have hx2 := mem_modify' hx
  have ek : x.2.kheap = s4.kheap := by rw [hx2]
  have ec : x.2.curSc = s4.curSc := by rw [hx2]
  have ei : x.2.idleSc = s4.idleSc := by rw [hx2]
  have er : x.2.releaseQueue = s4.releaseQueue := by rw [hx2]
  unfold sV at e3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨e3a, e3b, e3c, e3d⟩ := e3
  refine BI.of_parts hb (ec.trans (e4b.trans e3a)) (ei.trans (e4c.trans e3b)) ((mV_of_kheap ek).trans (e4a.trans e3d))
    fun hn hm' => ?_
  rw [er] at hm'
  rcases e4d _ hm' with h | h
  · exact hu h.symm
  · rw [e3c] at h; exact hn h

set_option maxRecDepth 20000 in
/-- **`schedContextResume sc` keeps `BI`** where `sc` is the SC of a thread `≠ ct`. -/
theorem pcp_resume (sc : ObjRef) :
    PCP ct (fun σ => ∃ u, u ≠ ct ∧ (mV σ u).1 = some (some sc)) (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume
  refine pcp_bind_ro (by ro_auto) fun _ => ?_
  refine pcp_bind_ro (by ro_auto) fun _ => ?_
  refine pcp_bind_ro (by ro_auto) fun _ => ?_
  unfold NonDet.when
  split
  · refine pcp_bind_ro (by ro_auto) fun _ => ?_
    refine pcp_bind_ro (by ro_auto) fun _ => ?_
    refine pcp_bind_ro (by ro_auto) fun _ => ?_
    split
    · refine pcp_bind_ro (by ro_auto) fun _ => ?_
      refine pcp_bind_ro (by ro_auto) fun _ => ?_
      refine pcp_bind_ro (by ro_auto) fun _ => ?_
      refine pcp_bind_ro (by ro_auto) fun _ => ?_
      exact pcp_postpone sc
    · exact pcp_pure' _
  · exact pcp_pure' _

theorem pc_donate (sc t : ObjRef) (ht : t ≠ ct) : PC ct (schedContextDonate (Z := Unit) sc t) :=
  pcp_mk (pq_of (kf_schedContextDonate' _ _) (PPNQ.qk_schedContextDonate' _ _))
    fun _ x _ hb _ hx => (bi_donate ht hb hx).1

set_option maxRecDepth 20000 in
/-- **`maybeDonateSc t n` keeps `BI`** for `t ≠ ct`. -/
theorem pc_maybeDonateSc (t n : ObjRef) (ht : t ≠ ct) : PC ct (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc
  refine pcp_bind_ro (by ro_auto) fun _ => ?_
  unfold NonDet.when
  split
  · refine pcp_bind_ro' (by ro_auto) fun o => ?_
    cases o with
    | none => exact pcp_pure' _
    | some scPtr =>
      dsimp only [NonDet.maybeM]
      refine pcp_bind_ro (by ro_auto) fun _ => ?_
      split
      · intro σ x hq hb _ ⟨y, hy, hx⟩
        obtain ⟨hb', ht'⟩ := bi_donate ht hb hy
        have hq' := pq_of (kf_schedContextDonate' _ _) (PPNQ.qk_schedContextDonate' _ _) σ y hq hy
        exact pcp_resume scPtr y.2 x hq' hb' ⟨t, ht, ht'⟩ hx
      · exact pcp_pure' _
  · exact pcp_pure' _

set_option maxRecDepth 20000 in
/-- **`replyRemove caller r` keeps `BI`** for `caller ≠ ct`. -/
theorem pc_replyRemove (caller r : ObjRef) (hc : caller ≠ ct) : PC ct (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun o => ?_
  cases o with
  | none => dsimp only; pc_step
  | some scPtr =>
    dsimp only
    refine pcp_bind (by pc_step) fun _ => ?_
    refine pcp_bind (by pc_step) fun _ => ?_
    refine pcp_bind (by pc_step) fun _ => ?_
    refine pcp_bind ?_ fun _ => by pc_step
    unfold NonDet.when
    split
    · exact pc_donate _ _ hc
    · pc_step

set_option maxRecDepth 20000 in
/-- **`replyPush caller callee r d` keeps `BI`** for `caller, callee ≠ ct`. -/
theorem pc_replyPush (caller callee r : ObjRef) (d : Bool) (hc : caller ≠ ct) (hd : callee ≠ ct) :
    PC ct (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  unfold NonDet.when
  split
  · refine pcp_bind (by pc_step) fun _ => ?_
    exact pc_donate _ _ hd
  · pc_step

end

/-! ## The IPC operations -/

section
variable {ct : ObjRef}
set_option maxRecDepth 20000

set_option maxHeartbeats 4000000 in
/-- The receive branch of `send_ipc` (pq_sendIpc_recv with `BI`). -/
theorem pc_sendIpc_recv (call : Bool) (badge : Badge) (g gr d : Bool) (thread ep dest : ObjRef)
    (hth : thread ≠ ct ∨ call = false) :
    PC ct (do
      tcbEpDequeue (Z := Unit) dest ep
      let recvState ← getThreadState dest
      let reply ← match recvState with
        | .blockedOnReceive _ reply _data => pure reply
        | _ => NonDet.fail
      doIpcTransfer thread (some ep) badge g dest
      NonDet.maybeM (replyUnlinkTcb dest) reply
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext dest
      let fault ← threadGet Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (g ∨ gr) ∧ reply ≠ none then
          replyPush thread dest (the reply) d
        else
          setThreadState thread .inactive
      else NonDet.when (d ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef Tcb.tcbSchedContext thread
        schedContextDonate (the threadSc) dest
      setThreadState dest .running
      let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_gts_bind dest fun ts hts => ?_
  cases ts
  case blockedOnReceive e r dt =>
    have hd : dest ≠ ct := fun e => by have := hts e; simp [runnable] at this
    refine pcp_bind (by pc_step) fun reply => ?_
    refine pcp_bind (by pc_step) fun _ => ?_
    refine pcp_bind (by pc_step) fun _ => ?_
    refine pcp_bind (by pc_step) fun scOpt => ?_
    refine pcp_threadGet_bind _ thread fun tf htf => ?_
    simp only [letFun]
    by_cases hc : (call ∨ tf.tcbFault ≠ none)
    · have ht : thread ≠ ct := by
        rcases hth with h | hcall
        · exact h
        · intro e
          have h2 := (htf e).2
          subst hcall
          simp only [h2] at hc
          simp at hc
      rw [if_pos hc]
      split
      · refine pcp_bind (pc_replyPush _ _ _ _ ht hd) fun _ => ?_
        pc_auto
      · pc_auto
    · rw [if_neg hc]
      first
        | (refine pcp_bind ?_ fun _ => ?_
           · unfold NonDet.when
             split
             · refine pcp_bind (by pc_step) fun _ => ?_
               exact pc_donate _ _ hd
             · pc_step
           · pc_auto
           done)
        | (try unfold NonDet.when
           split
           · refine pcp_bind (by pc_step) fun _ => ?_
             first
               | exact pc_donate _ _ hd
               | (refine pcp_bind (pc_donate _ _ hd) fun _ => ?_
                  pc_auto)
           · pc_auto
           done)
  all_goals exact pcp_fail_bind

/-- **`send_ipc` keeps `CQ ∧ BI`** from a sender `≠ ct`, or non-blocking and
non-calling from any sender. -/
theorem pc_sendIpc (block call : Bool) (badge : Badge) (g gr d : Bool) (thread ep : ObjRef)
    (hth : thread ≠ ct ∨ (block = false ∧ call = false)) :
    PC ct (sendIpc (Z := Unit) block call badge g gr d thread ep) := by
  unfold sendIpc
  refine pcp_bind (by pc_step) fun e => ?_
  have hr : thread ≠ ct ∨ call = false := hth.imp_right (·.2)
  cases e with
  | idleEP =>
    cases block
    · pc_step
    · exact pcp_of (pq_of (kf_sendIpcBlocked' _ _ _ _ _ _ (hth.resolve_right (by simp)))
        (qk_sendIpcBlockedQ _ _ _ _ _ _)) (sck_sendIpcBlocked _ _ _ _ _ _)
  | sendEP q =>
    cases block
    · pc_step
    · exact pcp_of (pq_of (kf_sendIpcBlocked' _ _ _ _ _ _ (hth.resolve_right (by simp)))
        (qk_sendIpcBlockedQ _ _ _ _ _ _)) (sck_sendIpcBlocked _ _ _ _ _ _)
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact fun _ _ _ _ _ hx => hx.elim
    | cons dest q => cases block <;> exact pc_sendIpc_recv call badge g gr d thread ep dest hr

theorem pc_sendFaultIpc (tptr : ObjRef) (hc : Cap) (f : Fault) (d : Bool) (ht : tptr ≠ ct) :
    PC ct (sendFaultIpc (Z := Unit) tptr hc f d) := by
  unfold sendFaultIpc
  split
  · refine pcp_bind (pcp_of (pq_of (kf_threadSet_ne _ _ ht) (PPNQ.qk_threadSet' _ _)) (by sck_auto2)) fun _ => ?_
    exact pcp_bind (pc_sendIpc _ _ _ _ _ _ _ _ (Or.inl ht)) fun _ => by pc_step
  · pc_step
  · exact fun _ _ _ _ _ hx => hx.elim

theorem pc_handleTimeout (tptr : ObjRef) (ex : Fault) (ht : tptr ≠ ct) :
    PC ct (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  refine pcp_bind (by pc_step) fun _ => ?_
  exact pcp_bind (pc_sendFaultIpc _ _ _ _ ht) fun _ => by pc_step

set_option maxHeartbeats 4000000 in
/-- The tail of `do_reply_transfer` (pq_drt_tail with `BI`). -/
theorem pc_drt_tail (receiver : ObjRef) (hd : receiver ≠ ct) (fault : Option Fault) :
    PC ct (do
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext receiver
      let state ← getThreadState receiver
      NonDet.when (scOpt ≠ none ∧ runnable state) <| do
        let scPtr ← NonDet.assertOpt scOpt
        let sc ← getSchedContext scPtr
        let curtime ← NonDet.gets fun s : State Unit => s.curTime
        if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
        then possibleSwitchTo receiver
        else do
          let tcb ← NonDet.getsThe (getTcb receiver)
          if isEpCap tcb.tcbTimeoutHandler ∧
             ¬(fault.elim false isTimeoutFault = true)
          then handleTimeout receiver (.timeout sc.scBadge)
          else postpone scPtr) := by
  refine pcp_getTcbSc_bind receiver fun so => ?_
  refine pcp_bind_ro (by ro_auto) fun _ => ?_
  unfold NonDet.when
  split
  · refine pcp_assertOpt_bind so fun scPtr hso => ?_
    refine pcp_bind_ro (by ro_auto) fun _ => ?_
    refine pcp_bind_ro (by ro_auto) fun _ => ?_
    split
    · pc_step
    · refine pcp_bind_ro (by ro_auto) fun _ => ?_
      split
      · exact pcp_weak (pc_handleTimeout _ _ hd) fun _ _ => trivial
      · exact pcp_weak (pcp_postpone scPtr) fun σ ⟨_, h⟩ => ⟨receiver, hd, by rw [h, hso]⟩
  · exact pcp_pure' _

/-- **`do_reply_transfer` keeps `CQ ∧ BI`**: the receiver is `BlockedOnReply`. -/
theorem pc_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    PC ct (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine pcp_bind (by pc_step) fun recvOpt => ?_
  cases recvOpt with
  | none => exact pcp_pure' _
  | some receiver =>
    refine pcp_gts_bind receiver fun ts hts => ?_
    cases ts
    case blockedOnReply r =>
      have hd : receiver ≠ ct := fun e => by have := hts e; simp [runnable] at this
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (pc_replyRemove _ _ hd) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun fault => ?_
      simp only [letFun]
      split
      all_goals repeat (first
        | exact pc_drt_tail receiver hd _
        | refine pcp_bind (by pc_step) fun _ => ?_)
    all_goals pc_step

set_option maxHeartbeats 4000000 in
/-- **`send_signal` keeps `CQ ∧ BI`**, from a state where `ct` waits on no
notification (`NQ`). -/
theorem pc_sendSignal (n : ObjRef) (b : Badge) :
    ∀ σ x, CQ ct σ → BI ct σ → NQ ct σ → x ∈ (sendSignal (Z := Unit) n b σ).1 → CQ ct x.2 ∧ BI ct x.2 := by
  intro σ x hs hb hq hx
  unfold sendSignal at hx
  obtain ⟨⟨nt, s1⟩, h1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := getSimpleKo_mem h1
  simp only at e1 hk
  subst e1
  rcases hno : nt.ntfnObj with _ | q | b' <;> rcases hbt : nt.ntfnBoundTcb with _ | tcb <;>
    simp only [hno, hbt] at hx
  · exact (pcp_of (P := fun _ => True) (pq_of (kf_setSimpleKo _ _ _) (PPNQ.qk_setSimpleKo' _ _ _))
      (sck_setSimpleKo_ntfn _ _)) _ x hs hb trivial hx
  · refine (pcp_gts_bind (P := fun _ => True) tcb fun ts hts => ?_) _ x hs hb trivial hx
    split
    · next hrb =>
      have hd : tcb ≠ ct := fun e => by
        have := hts e; cases ts <;> simp_all [runnable, receiveBlocked]
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (pc_maybeDonateSc _ _ hd) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      pc_step
    · exact pcp_of (pq_of (kf_setSimpleKo _ _ _) (PPNQ.qk_setSimpleKo' _ _ _)) (sck_setSimpleKo_ntfn _ _)
  all_goals try exact (pcp_of (P := fun _ => True) (pq_of (kf_setSimpleKo _ _ _) (PPNQ.qk_setSimpleKo' _ _ _))
      (sck_setSimpleKo_ntfn _ _)) _ x hs hb trivial hx
  all_goals
    have hq' : ct ∉ q := hq n nt q hk hno
    unfold updateWaitingNtfn at hx
    refine (?_ : PC ct _) _ x hs hb trivial hx
    by_cases hqe : q = []
    · subst hqe; exact fun _ _ _ _ _ ⟨y, hy, _⟩ => absurd rfl hy.1
    · have hd : the q.head? ≠ ct := fun e => hq' (e ▸ the_head_mem hqe)
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_pure_bind ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (pc_maybeDonateSc _ _ hd) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      refine pcp_bind (by pc_step) fun _ => ?_
      pc_step

end

/-! ## The perform, the shell and the fact -/

section
variable {ct : ObjRef}

theorem pc_post {α : Type} {m : NonDet (State Unit) α} (h : PC ct m) {σ : State Unit} (hs : CQ ct σ)
    (hb : BI ct σ) : ∀ y ∈ (m σ).1, CQ ct y.2 ∧ BI ct y.2 :=
  fun y hy => h σ y hs hb trivial hy

theorem pce_post {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : KFE ct m) (h2 : QVE m) (h3 : SVE m)
    {σ : State Unit} (hs : CQ ct σ) (hb : BI ct σ) : ∀ y ∈ (m.run σ).1, CQ ct y.2 ∧ BI ct y.2 :=
  fun y hy => ⟨⟨CtRs.of_ctV (h1 σ y hy) hs.1, qk_of_qv h2 σ y hy hs.2⟩, BI.of_sV (h3 σ y hy) hb⟩

set_option maxRecDepth 20000 in
/-- **The perform of a first-phase invocation but `PerfW` keeps `CQ ∧ BI`**
from `CQ ∧ NQ ∧ BI` (module docstring). -/
theorem perf_firstB (don : Bool) (inv : Fl4Invocation) (hf : FirstInv inv) (hw : ¬ PerfW inv) {σ : State Unit}
    (hs : CQ ct σ) (hq : NQ ct σ) (hb : BI ct σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don inv).run σ).1, CQ ct y.2 ∧ BI ct y.2 := by
  cases inv with
  | invokeUntyped i => exact absurd trivial hw
  | invokeEndpoint ep badge g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    refine post_liftE (Q := fun s => CQ ct s ∧ BI ct s) ?_
    refine pc_post ?_ hs hb
    refine pcp_bind_ro (dk_gets _) fun thread => ?_
    exact pcp_bind (pc_sendIpc false false badge g gr don thread ep (Or.inr ⟨rfl, rfl⟩)) fun _ => pcp_pure _
  | invokeNotification ep badge =>
    simp only [fl4PerformInvocation, withoutPreemption]
    have h1 := post_liftE (ε := Unit) (Q := fun s => CQ ct s ∧ BI ct s)
      (fun x hx => pc_sendSignal ep badge σ x hs hb hq hx)
    refine post_bindE (R := fun s => CQ ct s ∧ BI ct s) h1 (fun _ h => h) fun _ s' hm y hy => ?_
    rw [NonDetE.returnOk, ExceptT.run_pure] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact h1 _ hm
  | invokeReply reply grant =>
    simp only [fl4PerformInvocation]
    refine post_liftE (Q := fun s => CQ ct s ∧ BI ct s) ?_
    refine pc_post ?_ hs hb
    refine pcp_bind_ro (dk_gets _) fun sender => ?_
    exact pcp_bind (pc_doReplyTransfer sender reply grant) fun _ => pcp_pure _
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation]
    exact pce_post (by kf_auto) (by qv_auto2) (by sck_auto2) hs hb
  | invokeIRQHandler i =>
    cases i with
    | aCKIrq irq =>
      simp only [fl4PerformInvocation, invokeIrqHandler]
      exact pce_post (by kf_auto) (by qv_auto2) (by sck_auto2) hs hb
    | _ => exact absurd trivial hw
  | invokeArchObject i =>
    cases i with
    | spec i =>
      cases i with
      | invokeASIDControl _ => exact absurd trivial hw
      | _ =>
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
        exact pce_post (by kf_auto) (by qv_auto2) (by sck_auto2) hs hb
    | _ =>
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
      exact pce_post (by kf_auto) (by qv_auto2) (by sck_auto2) hs hb
  | _ => exact absurd hf id

end

/-- **[W] The `PerfW` performs keep `BI`** (module docstring): the Untyped,
IRQ handler set / clear and ASID control performs, at the states where they
start on a run of ReplyRecv / NBSendRecv / NBSendWait's invocation from the
dispatch state `σ` (`MidPerfAt`) and where `BI` holds. l4v:
`invoke_untyped`, `invoke_irq_handler`, `perform_asid_control_invocation`
keep the symmetric SC/TCB binding (`sym_refs (state_refs_of)`,
`valid_objs`), `cur_sc_tcb_are_bound`, `cur_sc_active` and
`ct_not_in_release_q`. -/
def JMidPerfHypB (don : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfW inv → BI σ.curThread σ1 →
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don inv).run σ1).1, BI σ.curThread y.2

/-- `BI` across an `fV`-, `qV`- and `sV`-frame. -/
theorem fqb_I {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : FV ct m) (h2 : QV m) (h3 : SV m)
    {σ : State Unit} (hI : (CQ ct σ ∧ NQ ct σ) ∧ BI ct σ) :
    ∀ x ∈ (m σ).1, (CQ ct x.2 ∧ NQ ct x.2) ∧ BI ct x.2 :=
  fun x hx => ⟨fq_I h1 h2 hI.1 x hx, BI.of_sV (h3 σ x hx) hI.2⟩

theorem fqbe_I {ct : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : FVE ct m) (h2 : QVE m)
    (h3 : SVE m) {σ : State Unit} (hI : (CQ ct σ ∧ NQ ct σ) ∧ BI ct σ) :
    ∀ x ∈ (m.run σ).1, (CQ ct x.2 ∧ NQ ct x.2) ∧ BI ct x.2 :=
  fqb_I h1 h2 h3 hI

theorem bi_setThreadState {ct t : ObjRef} {ts : ThreadState} {s : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setThreadState (Z := Unit) t ts s).1) (hb : BI ct s) : BI ct x.2 :=
  BI.of_sV (sck_setThreadState t ts s x hx) hb

set_option maxHeartbeats 1000000 in
/-- **The shell with `CQ ∧ BI`**: from `CQ ∧ NQ ∧ BI` at the entry, every
outcome of the first-phase non-blocking non-calling invocation is `CQ ∧ BI`. -/
theorem midRunB_shell (rep don : Bool) (cptr : CapRef) (σ : State Unit) (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hb : BI σ.curThread σ) (hW : JMidPerfHypQ don cptr σ)
    (hWB : JMidPerfHypB don cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep false false don true cptr).run σ).1,
      CQ σ.curThread y.2 ∧ BI σ.curThread y.2 := by
  intro y hy
  unfold fl4HandleInvocationR at hy
  obtain ⟨z, hz, ⟨t, ht, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
  obtain rfl : w = (σ.curThread, σ) := hw
  simp only [Except.ok.injEq] at ht
  subst ht
  obtain ⟨z, hz, ⟨info, hi, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨⟨info', σa⟩, hia, rfl⟩ := mem_liftE_inv' hz
  simp only [Except.ok.injEq] at hi
  subst hi
  have hIa := fqb_I (fv_getMessageInfo (ct := σ.curThread) _) (qv_getMessageInfo' _) (sck_getMessageInfo' _)
    ⟨⟨hs, hq⟩, hb⟩ _ hia
  refine syscall_post (mF := midF σ.curThread info' cptr) (mE := midE σ.curThread info' cptr)
    (I := fun s => (CQ σ.curThread s ∧ NQ σ.curThread s) ∧ BI σ.curThread s)
    (Q := fun s => CQ σ.curThread s ∧ BI σ.curThread s)
    (fun w hw => fqbe_I (fve_midF _ _ _) (qve_midF _ _ _) (scke_midF _ _ _) hIa w hw) ?_
    (fun a s has w hw => fqbe_I (fve_midE _ _ _ a) (qve_midE _ _ _ a) (scke_midE _ _ _ a)
      (fqbe_I (fve_midF _ _ _) (qve_midF _ _ _) (scke_midF _ _ _) hIa _ has) w hw) ?_ ?_ y hy
  · intro f s hI v hv
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte] at hv
    obtain rfl : v = ((), s) := hv
    exact ⟨hI.1.1, hI.2⟩
  · intro e s hI v hv
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte] at hv
    obtain rfl : v = ((), s) := hv
    exact ⟨hI.1.1, hI.2⟩
  · intro a s b s' has hbs hI y hy
    have hFI : FirstInv b := okAll_midE _ _ _ a s _ hbs b rfl
    refine post_bindE (R := fun s => (CQ σ.curThread s ∧ NQ σ.curThread s) ∧ BI σ.curThread s)
      (Q := fun s => CQ σ.curThread s ∧ BI σ.curThread s) ?_
      (fun _ h => ⟨h.1.1, h.2⟩) ?_ y hy
    · unfold withoutPreemption
      exact post_liftE (Q := fun s => (CQ σ.curThread s ∧ NQ σ.curThread s) ∧ BI σ.curThread s) fun x hx =>
        ⟨⟨pq_setThreadState_run _ _ rfl s' x hI.1.1 hx, NQ.of_nV (nv_setThreadState _ _ s' x hx) hI.1.2⟩,
          bi_setThreadState hx hI.2⟩
    intro u s1 h1 y hy
    obtain ⟨⟨u', s1'⟩, h1', e1⟩ := mem_liftE_inv' h1
    simp only [Prod.mk.injEq] at e1
    obtain ⟨-, rfl⟩ := e1
    have hI1 : (CQ σ.curThread s1 ∧ NQ σ.curThread s1) ∧ BI σ.curThread s1 :=
      ⟨⟨pq_setThreadState_run _ _ rfl s' _ hI.1.1 h1', NQ.of_nV (nv_setThreadState _ _ s' _ h1') hI.1.2⟩,
        bi_setThreadState h1' hI.2⟩
    have hA : MidPerfAt cptr σ b s1 := ⟨info', σa, a, s, s', hia, has, hbs, h1'⟩
    have hP : ∀ z ∈ ((fl4PerformInvocation (Z := Unit) false false don b).run s1).1,
        CQ σ.curThread z.2 ∧ BI σ.curThread z.2 := by
      by_cases hw : PerfW b
      · exact fun z hz => ⟨hW b s1 hA hw z hz, hWB b s1 hA hw hI1.2 z hz⟩
      · exact perf_firstB don b hFI hw hI1.1.1 hI1.1.2 hI1.2
    refine post_bindE (R := fun s => CQ σ.curThread s ∧ BI σ.curThread s) hP (fun _ h => h) ?_ y hy
    intro r s2 h2 y hy
    have hs2 : CQ σ.curThread s2 ∧ BI σ.curThread s2 := hP (.ok r, s2) h2
    unfold withoutPreemption at hy
    refine post_liftE (Q := fun s => CQ σ.curThread s ∧ BI σ.curThread s) ?_ y hy
    refine pc_post ?_ hs2.1 hs2.2
    refine pcp_gts_bind _ fun ts _ => ?_
    split
    · refine pcp_bind (by pc_step) fun _ => ?_
      exact pcp_of (fun σ x hs hx => pq_setThreadState_run _ _ rfl σ x hs hx) (sck_setThreadState _ _)
    · pc_step

/-- **`CurInv`, or the current thread holds no SC.** -/
def CtOK (σ : State Unit) : Prop :=
  Sched.CurInv σ ∨ ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ x.tcbSchedContext = none

/-- `CQ ∧ BI` give `CtOK`. -/
theorem ctOK_of {σ : State Unit} (hs : CQ σ.curThread σ) (hb : BI σ.curThread σ) : CtOK σ := by
  obtain ⟨s, hs0⟩ := hb.ex
  obtain ⟨x, hk, hxs⟩ := tP_some hs0
  rcases hb.cur s hs0 with h | ⟨hsc, ⟨⟨tc, m⟩, htm⟩, hpos, hnr⟩
  · exact Or.inr ⟨x, hk, hxs.trans h⟩
  · left
    obtain ⟨y, n, hky, -, hm⟩ := cP_some htm
    refine ⟨⟨x, hk, hxs.trans hsc, Fl4Proofs.P3.Notif.NotIpcBlk.of_runnable (hs.1.2 x hk).1⟩, ⟨y, n, hky⟩, fun hci y' n' hk' => ?_, hnr⟩
    rw [hky] at hk'
    cases hk'
    have := hpos hci (tc, m) htm
    unfold scActive activeSc
    simp only [decide_eq_true_eq]
    rw [hm]; exact this

/-- `BI` at a state with `CurInv` and `Inv.back`. -/
theorem bi_of {σ : State Unit} (hC : Sched.CurInv σ) (hI : Sched.Inv σ) : BI σ.curThread σ := by
  obtain ⟨xt, hkt, hst, -⟩ := hC.tcb
  refine ⟨mV_dis σ, ⟨_, by rw [mV_tP hkt]⟩, fun s hs => ?_, fun u p hu => ?_⟩
  · rw [mV_tP hkt] at hs
    cases hs
    right
    obtain ⟨y, n, hky⟩ := hC.sc
    refine ⟨hst, ⟨_, by rw [mV_cP hky]⟩, fun hci tm htm => ?_, hC.notRel⟩
    rw [mV_cP hky] at htm
    cases htm
    have := hC.active hci y n hky
    unfold scActive activeSc at this
    simpa using this
  · obtain ⟨x, hk, hx⟩ := tP_some hu
    obtain ⟨y, n, hky, hyt⟩ := hI.back u x p hk hx
    exact ⟨y.scRefillMax, by rw [mV_cP hky, hyt]⟩

/-- **(c1) The first-phase spec fact** (module docstring): from the dispatch
state, every outcome of the first-phase invocation satisfies `CtOK`
(`CurInv`, or the current thread holds no SC). -/
theorem jMidChooseFact (rep don : Bool) (cptr : CapRef) (σ : State Unit) (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hC : Sched.CurInv σ) (hI : Sched.Inv σ) (hW : JMidPerfHypQ don cptr σ)
    (hWB : JMidPerfHypB don cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep false false don true cptr).run σ).1, CtOK y.2 := by
  intro y hy
  obtain ⟨h1, h2⟩ := midRunB_shell rep don cptr σ hs hq (bi_of hC hI) hW hWB y hy
  have e : y.2.curThread = σ.curThread := h1.1.1
  rw [← e] at h1 h2
  exact ctOK_of h1 h2

end

end Fl4Proofs.P3.MidRun
