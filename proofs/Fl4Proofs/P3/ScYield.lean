/-
P3 (DESIGN.md §9), scheduling contexts: **the yield-to relation**
(`YieldRel`), relating each TCB's `YIELD_TO` word to the spec's
`tcb_yield_to` and the spec's yield-to/yield-from pairs (l4v `sym_refs`
for `tcb_yield_to`/`sc_yield_from`); the SC side (`sc_yield_from` and the
SC's `YIELD_FROM` word) is part of `SchedRel` (`ScRel1.yieldFrom`). It is a
separate relation (not in `SchedSpec`) so that the scheduler proofs need not
carry it; `YieldRel.frame` moves it across steps that keep the yield words
(`NY`) and the spec's yield fields (`YKeep`).
* `SchedRel.set_yt`, `SchedRel.set_sc_yf`: the two writes of the yield-to
  pairing;
* `Inv.ytUpd`, `KView.ytUpd`: the spec side of `tcb_yield_to := v`;
* `Inv.setRunnable`: setting a runnable state keeps `Inv`;
* `dequeue_ny`, `enqueue_ny`, `reschedule_required_ny`,
  `set_thread_state_ny`: the queue and state code keeps the yield words.
-/
import Fl4Proofs.P3.ScBind
import Fl4Proofs.P3.ScConsumed
import Fl4Proofs.P3.ScScheduleTop
import Fl4Proofs.P3.ScCallFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The spec's yield fields are kept: every TCB's `tcb_yield_to`, every
SC's `sc_yield_from` (and size), both ways. -/
def YKeep (σ σ' : State Unit) : Prop :=
  (∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbYieldTo = x.tcbYieldTo) ∧
  (∀ p x n, σ.kheap p = some (.schedContext x n) → ∃ y, σ'.kheap p = some (.schedContext y n) ∧
    y.scYieldFrom = x.scYieldFrom) ∧
  (∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ x, σ.kheap p = some (.schedContext x n) ∧
    y.scYieldFrom = x.scYieldFrom)

theorem YKeep.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : YKeep σ σ' :=
  ⟨fun p x hp => ⟨x, by rw [h]; exact hp, rfl⟩, fun p x n hp => ⟨x, by rw [h]; exact hp, rfl⟩,
    fun p y n hp => ⟨y, by rw [← h]; exact hp, rfl⟩⟩

theorem YKeep.refl (σ : State Unit) : YKeep σ σ := YKeep.of_kheap rfl

theorem YKeep.trans {σ σ1 σ2 : State Unit} (h1 : YKeep σ σ1) (h2 : YKeep σ1 σ2) : YKeep σ σ2 := by
  refine ⟨fun p x hp => ?_, fun p x n hp => ?_, fun p y n hp => ?_⟩
  · obtain ⟨y, hy, e⟩ := h1.1 p x hp; obtain ⟨z, hz, e'⟩ := h2.1 p y hy; exact ⟨z, hz, e'.trans e⟩
  · obtain ⟨y, hy, e⟩ := h1.2.1 p x n hp; obtain ⟨z, hz, e'⟩ := h2.2.1 p y n hy; exact ⟨z, hz, e'.trans e⟩
  · obtain ⟨x, hx, e⟩ := h2.2.2 p y n hp; obtain ⟨w, hw, e'⟩ := h1.2.2 p x n hx; exact ⟨w, hw, e.trans e'⟩

theorem YKeep.updTcb {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    (e : x'.tcbYieldTo = x.tcbYieldTo) : YKeep σ (updK σ p (.tcb x')) := by
  refine ⟨fun q y hq => ?_, fun q y n hq => ?_, fun q y n hq => ?_⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
    · exact ⟨y, by simp [updK, h, hq], rfl⟩
  · have h : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp [updK, h, hq], rfl⟩
  · have h : q ≠ p := by rintro rfl; simp [updK] at hq
    exact ⟨y, by simpa [updK, h] using hq, rfl⟩

theorem YKeep.updSc {σ : State Unit} {p : ObjRef} {x x' : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (e : x'.scYieldFrom = x.scYieldFrom) :
    YKeep σ (updSc σ p x' n) := by
  refine ⟨fun q y hq => ?_, fun q y m hq => ?_, fun q y m hq => ?_⟩
  · have h : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp [updK, h, hq], rfl⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
    · exact ⟨y, by simp [updK, h, hq], rfl⟩
  · by_cases h : q = p
    · subst h; simp [updK] at hq; obtain ⟨rfl, rfl⟩ := hq; exact ⟨x, hk, e⟩
    · exact ⟨y, by simpa [updK, h] using hq, rfl⟩

theorem YKeep.stsAct {σ : State Unit} (t : ObjRef) : YKeep σ (Fl4Proofs.P3.Notif.stsAct σ t) :=
  YKeep.of_kheap (by unfold Fl4Proofs.P3.Notif.stsAct; split <;> rfl)

/-- **Replacing a TCB by one with the same state and SC keeps `Inv`.** -/
theorem Inv.tcbUpd {σ : State Unit} (h : Inv σ) {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (x' : Tcb) (est : x'.tcbState = x.tcbState) (esc : x'.tcbSchedContext = x.tcbSchedContext) :
    Inv (updK σ p (.tcb x')) := by
  set σ' := updK σ p (.tcb x')
  have ko : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', updK, hq]
  have kp : σ'.kheap p = some (.tcb x') := by simp [σ', updK]
  have kf : ∀ q y, σ.kheap q = some (.tcb y) → ∃ y', σ'.kheap q = some (.tcb y') ∧
      y'.tcbState = y.tcbState ∧ y'.tcbSchedContext = y.tcbSchedContext := by
    intro q y hq
    by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq; exact ⟨_, kp, est, esc⟩
    · exact ⟨y, by rw [ko q e]; exact hq, rfl, rfl⟩
  have kb : ∀ q y', σ'.kheap q = some (.tcb y') → ∃ y, σ.kheap q = some (.tcb y) ∧
      y'.tcbState = y.tcbState ∧ y'.tcbSchedContext = y.tcbSchedContext := by
    intro q y' hq
    by_cases e : q = p
    · subst e; rw [kp] at hq; cases hq; exact ⟨x, hk, est, esc⟩
    · exact ⟨y', by rw [← ko q e]; exact hq, rfl, rfl⟩
  have ks : ∀ q y m, σ'.kheap q = some (.schedContext y m) ↔ σ.kheap q = some (.schedContext y m) := by
    intro q y m
    by_cases e : q = p
    · subst e; rw [kp, hk]; simp
    · rw [ko q e]
  have kn' : ∀ q y, σ'.kheap q = some (.notification y) ↔ σ.kheap q = some (.notification y) := by
    intro q y
    by_cases e : q = p
    · subst e; rw [kp, hk]; simp
    · rw [ko q e]
  have rt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
    intro u hu
    obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := h.rel u hu
    obtain ⟨xu', h1', -, e2⟩ := kf u xu h1
    have hne := h.ne scp yu nu h4
    rw [specRt_eq h1' (e2.trans h2) ((ks _ _ _).2 h4) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u y hy hc => ?_, fun q y m hy => ?_,
    fun u y q hy hq => ?_, fun q y q' hy hq => ?_, fun q y m hy => ?_, fun q y m hy => ?_⟩
  · obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    obtain ⟨xu', h1', e1, e2⟩ := kf u xu h1
    exact ⟨xu', scp, yu, nu, h1', e2.trans h2, by rw [e1]; exact h3, (ks _ _ _).2 h4, h5⟩
  · obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rel u hu
    obtain ⟨xu', h1', e1, e2⟩ := kf u xu h1
    exact ⟨xu', scp, yu, nu, h1', e2.trans h2, by rw [e1]; exact h3, (ks _ _ _).2 h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt a ha, rt b hb]; exact hab
  · intro x' scp yu nu h1 h2 h3 h4 h5
    obtain ⟨y0, hy0, e1, -⟩ := kb u y hy
    obtain ⟨x0, hx0, -, e2⟩ := kb u x' h1
    exact h.rd u y0 hy0 (by rw [← e1]; exact hc) x0 scp yu nu hx0 (by rw [← e2]; exact h2) ((ks _ _ _).1 h3) h4 h5
  · exact h.refills q y m ((ks _ _ _).1 hy)
  · obtain ⟨y0, hy0, -, e2⟩ := kb u y hy
    obtain ⟨yq, mq, h1, h2⟩ := h.back u y0 q hy0 (by rw [← e2]; exact hq)
    exact ⟨yq, mq, (ks _ _ _).2 h1, h2⟩
  · obtain ⟨yq, mq, h1⟩ := h.ntfnSc q y q' ((kn' _ _).1 hy) hq
    exact ⟨yq, mq, (ks _ _ _).2 h1⟩
  · exact h.ne q y m ((ks _ _ _).1 hy)
  · exact h.rr q y m ((ks _ _ _).1 hy)

/-- **Changing a TCB's `tcb_yield_to` keeps `Inv`.** -/
theorem Inv.ytUpd {σ : State Unit} (h : Inv σ) {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (v : Option ObjRef) : Inv (updK σ p (.tcb { x with tcbYieldTo := v })) :=
  h.tcbUpd hk _ rfl rfl

theorem KView.ytUpd {σ : State Unit} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (v : Option ObjRef) : KView σ (updK σ p (.tcb { x with tcbYieldTo := v })) := by
  refine ⟨fun q z hq => ?_, fun q z hq => ?_⟩
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, this, hq]
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq
      exact ⟨{ x with tcbYieldTo := v }, by simp [updK], rfl, rfl, rfl⟩
    · exact ⟨z, by simp [updK, e, hq], rfl, rfl, rfl⟩

theorem NtfnStepW.ytUpd {σ : State Unit} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x))
    (v : Option ObjRef) : NtfnStepW σ (updK σ p (.tcb { x with tcbYieldTo := v })) := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; exact Or.inr (Or.inr (Or.inl ⟨x, { x with tcbYieldTo := v }, hk, by simp [updK], rfl⟩))
  · exact Or.inl (by simp [updK, e])

/-- Setting a runnable state keeps the invariant. -/
theorem Inv.setRunnable {σ : State Unit} (h : Inv σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hrun : runnable x.tcbState = true) {ts : ThreadState}
    (hts : runnable ts = true) :
    Inv (stsAct (updK σ p (.tcb { x with tcbState := ts })) p) := by
  have h1 : Inv (updK σ p (.tcb { x with tcbState := ts })) := by
    refine h.stable (NtfnStep.tcb hk ts x.tcbArch) fun q y z hy hz => ?_
    by_cases e : q = p
    · subst e
      rw [hk] at hy; cases hy
      simp only [updK_kheap, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hz
      subst hz
      refine Or.inr ⟨hts, fun e => ?_, Or.inl (Or.inl hrun)⟩
      rw [e] at hrun; cases hrun
    · simp only [updK_kheap, ne_eq, e, not_false_eq_true, Function.update_of_ne] at hz
      rw [hy] at hz; cases hz; exact Or.inl rfl
  exact h1.qchange (qchange_stsAct _ _)

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **The yield-to relation**: each TCB's `YIELD_TO` word is its
`tcb_yield_to`, and the spec's yield-to and yield-from links pair up. -/
structure YieldRel (T C : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop where
  tcb : ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ x.tcbYieldTo = optRef (m (yieldA t))
  toSc : ∀ t ∈ T, m (yieldA t) ≠ 0#u64 → m (yieldA t) ∈ C ∧
    ∃ y n, σ.kheap (m (yieldA t)).bv = some (.schedContext y n) ∧ y.scYieldFrom = some t.bv
  frm : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ p, y.scYieldFrom = some p →
    ∃ t ∈ T, t.bv = p ∧ m (yieldA t) = sc

theorem YieldRel.frame {T C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : YieldRel T C m σ)
    (hm : ∀ t ∈ T, m' (yieldA t) = m (yieldA t)) (hk : YKeep σ σ') : YieldRel T C m' σ' := by
  refine ⟨fun t ht => ?_, fun t ht h0 => ?_, fun sc hsc y n hy p hp => ?_⟩
  · obtain ⟨x, hx, e⟩ := h.tcb t ht
    obtain ⟨x', hx', e'⟩ := hk.1 _ x hx
    exact ⟨x', hx', by rw [e', e, hm t ht]⟩
  · rw [hm t ht] at h0 ⊢
    obtain ⟨h1, y, n, hy, e⟩ := h.toSc t ht h0
    obtain ⟨y', hy', e'⟩ := hk.2.1 _ y n hy
    exact ⟨h1, y', n, hy', e'.trans e⟩
  · obtain ⟨x, hx, e⟩ := hk.2.2 _ y n hy
    obtain ⟨t, ht, e1, e2⟩ := h.frm sc hsc x n hx p (e ▸ hp)
    exact ⟨t, ht, e1, by rw [hm t ht]; exact e2⟩

/-- A `YIELD_TO` word of `T`. -/
def YW (T : Set U64) (b : U64) : Prop := ∃ y ∈ T, b = yieldA y

/-- **The footprint of YieldTo**: `KFoot` and the `YIELD_TO` words. -/
def TFoot (st : machine.Store S) [L : LawfulStore st] (T N C : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  KFoot st T N C c s σ b ∨ YW T b

theorem WritesIn.tfoot_of_kfoot {T N C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (h : WritesIn st s s' (KFoot st T N C c s σ)) : WritesIn st s s' (TFoot st T N C c s σ) :=
  h.mono fun _ hb => Or.inl hb

theorem WritesIn.tfoot_trans {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ σ1 : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (TFoot st T N C c s σ)) (hz : SzKeepC C σ σ1)
    (h2 : WritesIn st s1 s2 (TFoot st T N C c s1 σ1)) : WritesIn st s s2 (TFoot st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | ((hb | hb | ⟨sc, hsc, x, n, hk', ho, hne⟩) | hb)
    · exact hb
    · exact Or.inl (KFoot.of_sfoot ((SFoot.ksb h1.1).1 hb))
    · exact Or.inl (KFoot.of_nw hb)
    · obtain ⟨x0, hk0⟩ := hz sc hsc x n hk'
      exact Or.inl (KFoot.of_sw ⟨sc, hsc, x0, n, hk0, ho, hne⟩)
    · exact Or.inr hb

theorem WritesIn.tfoot_sfoot {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (TFoot st T N C c s σ)) (h2 : WritesIn st s1 s2 (SFoot st T c s1)) :
    WritesIn st s s2 (TFoot st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact Or.inl (KFoot.of_sfoot ((SFoot.ksb h1.1).1 hb))

theorem WritesIn.tfoot_of_sfoot {T N C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (h : WritesIn st s s' (SFoot st T c s)) : WritesIn st s s' (TFoot st T N C c s σ) :=
  h.mono fun _ hb => Or.inl (KFoot.of_sfoot hb)

/-- A write of `KFoot` words (of the start's spec) after a footprint. -/
theorem WritesIn.tfoot_add {T N C : Set U64} {c : U64} {s s1 s2 : S} {σ : Fl4Spec.State Unit}
    (h1 : WritesIn st s s1 (TFoot st T N C c s σ)) (h2 : WritesIn st s1 s2 (TFoot st T N C c s σ)) :
    WritesIn st s s2 (TFoot st T N C c s σ) :=
  (h1.trans h2).mono fun b hb => by rcases hb with hb | hb <;> exact hb

theorem WritesIn.yw_trans {T : Set U64} {s s1 s2 : S} (h1 : WritesIn st s s1 (fun b => ¬ YW T b))
    (h2 : WritesIn st s1 s2 (fun b => ¬ YW T b)) : WritesIn st s s2 (fun b => ¬ YW T b) :=
  (h1.trans h2).mono fun b hb => by rcases hb with hb | hb <;> exact hb

theorem WritesIn.yield_keep {T : Set U64} {s s' : S} (hT : TcbPlaced T) (h : WritesIn st s s' (fun b => ¬ YW T b)) :
    ∀ y ∈ T, L.mem s' (yieldA y) = L.mem s (yieldA y) := fun y hy =>
  h.mem_eq (field_aligned (hT y hy) (K := 3472#u64) (by simp) (by simp)) fun hn => hn ⟨y, hy, rfl⟩

/-- A TCB word at another offset is no `YIELD_TO` word. -/
theorem not_yw_tfield {T : Set U64} (hT : TcbPlaced T) {w K : U64} (hw : w ∈ T) (hK : K.val < 4096)
    (hK' : K ≠ 3472#u64) : ¬ YW T (core.num.U64.wrapping_add w K) := by
  rintro ⟨y, hy, e⟩
  rw [show yieldA y = core.num.U64.wrapping_add y 3472#u64 from rfl, tt_eq_iff (hT w hw) (hT y hy) hK (by simp)] at e
  exact hK' e.2

theorem not_yw_node {T : Set U64} {s : S} {c o : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288) :
    ¬ YW T (L.nodeAt s c o) := by
  rintro ⟨y, hy, e⟩
  exact nodeAt_ne_tfield hN ho hy (hT y hy) (K := 3472#u64) (by simp) e

theorem qfoot_yw {T : Set U64} {c : U64} {s : S} {W : List U64} {P : Nat → Prop} {t b : U64}
    (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T) (ht : t ∈ T) (hN : NodePlaced st T s c) (hcpu : L.cpu s = c)
    (h : L.QFoot s W c P t b) : ¬ YW T b := by
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩
  · rw [e]; exact not_yw_tfield hT (hW w hw) (by simp [nextOff]) (by simp [nextOff])
  · rw [e]; exact not_yw_tfield hT (hW w hw) (by simp [prevOff]) (by simp [prevOff])
  · rw [e]; exact not_yw_node hT hN ho
  · rw [e]; exact not_yw_tfield hT ht (by simp) (by simp)
  · rw [e, hcpu]; exact not_yw_node hT hN ho

theorem dequeue_yw {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => WritesIn st s s' (fun b => ¬ YW T b) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  refine WP.spec_mono (sched.dequeue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) (hc.queued t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_yw hc.tcbs (fun w hw' => (hc.ready.1.rel _ hp).mem w hw') ht hc.node hc.cur hb

theorem enqueue_yw {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => WritesIn st s s' (fun b => ¬ YW T b) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ Q (L.mem s (prioA t)) :=
    fun h0 hm => ((hc.queued t ht).2 hm) h0
  refine WP.spec_mono (sched.enqueue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) hnq) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_yw hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact (hc.ready.1.rel _ hp).mem w hw'

theorem set_action_yw {N T C : Set U64} {c : U64} {s s1 : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (h1 : WritesIn st s s1 (fun b => ¬ YW T b)) (v : U64) :
    sched.set_action st s1 v ⦃ s' => WritesIn st s s' (fun b => ¬ YW T b) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
  rintro s' rfl
  have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
  refine WritesIn.yw_trans h1 ((writesIn_wr ?_).mono fun b hb => ?_)
  · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN ho (by simp [layout.node.SCHED_ACTION])
  · rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact not_yw_node hc.tcbs hN ho

theorem reschedule_required_yw {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) :
    sched.reschedule_required st s ⦃ s' => WritesIn st s s' (fun b => ¬ YW T b) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.reschedule_required
  step with sched.action.spec' as ⟨act, hact'⟩
  rw [hc.cur] at hact'
  have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
  have e1 : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl
  by_cases h1 : act = sched.ACTION_RESUME_CURRENT
  · have : (act != sched.ACTION_RESUME_CURRENT) = false := by simpa using h1
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact set_action_yw hS (WritesIn.refl _ _) _
  have g1 : (act != sched.ACTION_RESUME_CURRENT) = true := by simpa using h1
  by_cases h2 : act = sched.ACTION_CHOOSE_NEW
  · have : (act != sched.ACTION_CHOOSE_NEW) = false := by simpa using h2
    simp only [g1, this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact set_action_yw hS (WritesIn.refl _ _) _
  have g2 : (act != sched.ACTION_CHOOSE_NEW) = true := by simpa using h2
  simp only [g1, g2, ↓reduceIte]
  have hT : act ∈ T := by
    rw [hact']
    rcases hS.actW with h | h | h
    · rw [hact', h] at h1; exact absurd e0.symm h1
    · rw [hact', h] at h2; exact absurd e1.symm h2
    · exact h
  step with sched.is_schedulable.spec' as ⟨b, _hb⟩
  by_cases hb : b = true
  · rw [ite_eq_left hb]; exact WP.spec_bind (enqueue_yw hS hT) fun s1 h1 => set_action_yw hS h1 _
  · rw [ite_eq_right hb]; simp only [bind_ok]; exact set_action_yw hS (WritesIn.refl _ _) _

/-- `schedule_tcb` writes at most the action word. -/
theorem schedule_tcb_yw {N T C : Set U64} {c : U64} {s s1 : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (h1 : WritesIn st s s1 (fun b => ¬ YW T b)) (t : U64) :
    sched.schedule_tcb st s1 t ⦃ s' => WritesIn st s s' (fun b => ¬ YW T b) ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec' as ⟨t1, _ht1⟩
  step as ⟨b, _hb⟩
  split
  · step with sched.action.spec' as ⟨i, _hi⟩
    split
    · step with sched.is_schedulable.spec' as ⟨b1, _hb1⟩
      split
      · exact (WP.spec_ok _).mpr h1
      · exact set_action_yw hS h1 _
    · exact (WP.spec_ok _).mpr h1
  · exact (WP.spec_ok _).mpr h1

theorem tStA_not_yw {T : Set U64} (hT : TcbPlaced T) {t : U64} (ht : t ∈ T) : ¬ YW T (tStA t) := by
  rw [tStA_eq]; exact not_yw_tfield hT ht (by simp) (by simp)

theorem set_thread_state_yw {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => WritesIn st s s' (fun b => ¬ YW T b) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hA : Aligned (tStA t) := by rw [tStA_eq]; exact field_aligned (hc.tcbs t ht) (by simp) (by simp)
  unfold sched.set_thread_state
  step
  subst s1_post
  rw [show stA t = tStA t from rfl]
  exact schedule_tcb_yw hS ((writesIn_wr hA).mono fun b hb => hb ▸ tStA_not_yw hc.tcbs ht) t

/-- An SC word is no `YIELD_TO` word. -/
theorem not_yw_scin {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc a : U64} (hsc : sc ∈ C) (hin : ScIn st s sc a) : ¬ YW T a := by
  rintro ⟨y, hy, rfl⟩
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hta := hc.tcbs y hy
  have := (hS.scOutIn hsc hin).2.2.1 y hy
  rw [show (yieldA y).val = y.val + 3472 from by
    have := hta.fits; simp [yieldA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega] at this
  omega

theorem scYieldFromA_eq (sc : U64) : scYieldFromA sc = scW sc 56#u64 := by
  unfold scYieldFromA scW layout.sc.YIELD_FROM; rfl

/-- Writing an SC's `YIELD_FROM` word (`sc_yield_from := v`). -/
theorem SchedRel.set_sc_yf {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) :
    SchedRel st N T C c (L.wr s (scYieldFromA sc) v) (updSc σ sc.bv { x with scYieldFrom := optRef v } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scYieldFromA sc) v)) ∧
      KView σ (updSc σ sc.bv { x with scYieldFrom := optRef v } n) ∧
      WritesIn st s (L.wr s (scYieldFromA sc) v) (fun b => ¬ YW T b) := by
  rw [scYieldFromA_eq]
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hW', ep, em, hrs, hw, hv, hwr⟩ := hx.wr_hdr (K := 56#u64) (by simp [HdrK]) v
  have hx' : ScRel1 st (L.wr s (scW sc 56#u64) v) sc { x with scYieldFrom := optRef v } n :=
    ⟨hW', by rw [ep]; exact hx.period, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge, by rw [hv],
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, by rw [em]; exact hx.max,
      by rw [hrs]; exact hx.refills⟩
  exact ⟨hS.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx',
    scin_footEq hS hsc hwr, KView.of_sc hk, hwr.mono fun b hb => not_yw_scin hS hsc hb⟩

/-- **Writing a TCB word the scheduler and notification relations do not
read** (offset `K`: no `SchedField`, not the state, block, badge register or
`Ep` links), with the spec's TCB replaced by one with the same state, badge,
domain, SC and priority. -/
theorem SchedRel.set_tw {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    {K : U64} (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hKs : ¬ SchedField K)
    (hK1 : K ≠ 3328#u64) (hK2 : K ≠ 3336#u64) (hK3 : K ≠ 256#u64) (hK4 : K ≠ 3496#u64) (hK6 : K ≠ 3504#u64)
    (x' : Fl4Spec.Tcb) (est : x'.tcbState = x.tcbState) (eb : badgeOf x' = badgeOf x)
    (ed : x'.tcbDomain = x.tcbDomain) (esc : x'.tcbSchedContext = x.tcbSchedContext)
    (ep : x'.tcbPriority = x.tcbPriority) (v : U64) :
    SchedRel st N T C c (L.wr s (core.num.U64.wrapping_add t K) v) (updK σ t.bv (.tcb x')) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (core.num.U64.wrapping_add t K) v)) ∧
      KView σ (updK σ t.bv (.tcb x')) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hta := hc.tcbs t ht
  have hA : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK h8
  have hv : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta hK
  have hns : ∀ K' : U64, SchedField K' → K' ≠ K := fun K' h e => hKs (e ▸ h)
  set s' := L.wr s (core.num.U64.wrapping_add t K) v
  have hk' : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have nfo : ∀ b : U64, Aligned b → b ≠ core.num.U64.wrapping_add t K → L.mem s' b = L.mem s b :=
    fun b hb hne => rd_wr_ne hA hb (Ne.symm hne)
  have nout : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => nfo _ (nodeAt_aligned hN ho h8) (nodeAt_ne_tfield hN ho ht hta hK)
  have tf : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → K' ≠ K) →
      L.mem s' (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') := by
    intro y hy K' h1 h2 h3
    refine nfo _ (field_aligned (hc.tcbs y hy) h1 h2) ?_
    rw [Ne, tt_eq_iff (hc.tcbs y hy) hta h1 hK]
    rintro ⟨rfl, rfl⟩; exact h3 rfl rfl
  have hcag : CAgree st T c s s' := ⟨hk', L.cpu_wr _ _ _, fun o ho h8 _ _ _ _ _ => nout o ho h8,
    fun y hy K' hK' => by
      have hsf : SchedField K' := by rcases hK' with h | h | h | h | h <;> simp [SchedField, h]
      obtain ⟨h1, h2, -⟩ := schedField_ok hsf
      exact tf y hy K' h1 h2 (fun _ => hns K' hsf)⟩
  have hscw : ∀ sc ∈ C, ScAgree st s s' sc := fun sc hsc a ha hin => nfo a ha (fun e => by
    have := (hS.scOutIn hsc hin).2.2.1 t ht
    rw [e, hv] at this
    omega)
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk']; exact nout o ho h8
  have hdom : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := nfo _ (curDomA_aligned hN) (fun e => by
    have h1 := hc.ksOut t ht
    have := congrArg UScalar.val e
    rw [curDomA_val hN, hv] at this
    omega)
  have hdt : L.mem s' (dtA st s) = L.mem s (dtA st s) := nfo _ (dtA_aligned hN) (fun e => by
    have h1 := hc.ksOut t ht
    have := congrArg UScalar.val e
    rw [dtA_val hN, hv] at this
    omega)
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk']; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk']; exact hS.domNW, by rw [dtA_ksb hk']; exact hS.dtNW,
    scOut_transfer hk' (SzKeep.updK hk fun _ _ e => by cases e) hS.scOut,
    scDisj_transfer (SzKeep.updK hk fun _ _ e => by cases e) hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc.agree hcag, ?_⟩, ?_, ?_⟩
  · refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
      by rw [nw _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
      by rw [dtA_ksb hk', hdt]; exact hs.domTime,
      by rw [nw layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
    · rw [nw _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
    · rw [nw _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hs.curSc
    · rw [nw _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]; exact hs.curTime
    · rw [nw _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]; exact hs.consumed
    · rw [curDomA_ksb hk', hdom]; exact hs.curDom
    · obtain ⟨z, hkz, h1, h2, h3, h4⟩ := hs.tcb y hy
      have ed' : L.mem s' (domA y) = L.mem s (domA y) :=
        tf y hy (3432#u64) (by simp) (by simp) (fun _ => hns _ (by simp [SchedField]))
      have ep' : L.mem s' (prioA y) = L.mem s (prioA y) :=
        tf y hy (3448#u64) (by simp) (by simp) (fun _ => hns _ (by simp [SchedField]))
      have es' : L.mem s' (scA y) = L.mem s (scA y) :=
        tf y hy (3464#u64) (by simp) (by simp) (fun _ => hns _ (by simp [SchedField]))
      by_cases e : y = t
      · subst e
        rw [hk] at hkz; cases hkz
        exact ⟨x', by simp [updK], ed.trans h1, by rw [ed']; exact h2,
          by rw [es', esc]; exact h3, by rw [ep', ep]; exact h4⟩
      · exact ⟨z, by simp [updK, bv_inj e, hkz], h1, by rw [ed']; exact h2, by rw [es']; exact h3,
          by rw [ep']; exact h4⟩
    · have es : L.mem s' (scA y) = L.mem s (scA y) :=
        tf y hy (3464#u64) (by simp) (by simp) (fun _ => hns _ (by simp [SchedField]))
      rw [es]; exact hs.scMem y hy
    · obtain ⟨z, m, hkz, hz⟩ := hs.scs sc hsc
      have : sc.bv ≠ t.bv := by intro e; rw [e, hk] at hkz; cases hkz
      exact ⟨z, m, by simp [updK, this, hkz], hz.agree (hscw sc hsc)⟩
  · intro a ha hf
    refine nfo a ha (fun e => ?_)
    subst e
    rcases hf with ⟨n0, hn0, h1, h2⟩ | ⟨y, hy, e | e | e | e | e | e⟩
    · have := hS.placed.disj n0 hn0 t ht
      rw [hv] at h1 h2
      omega
    all_goals first
      | (rw [tStA_eq] at e)
      | (rw [tBlockA_eq] at e)
      | (rw [badgeRegA_eq] at e)
      | (rw [prioA_eq'] at e)
      | (rw [nextEp_eq] at e)
      | (rw [prevEp_eq] at e)
    all_goals (rw [tt_eq_iff hta (hc.tcbs y hy) hK (by simp)] at e; obtain ⟨-, e⟩ := e)
    all_goals first
      | exact hK1 e | exact hK2 e | exact hK3 e | exact hK4 e | exact hK6 e
      | exact hns _ (by simp [SchedField]) e.symm
  · refine ⟨fun p z hp => ?_, fun p z hp => ?_⟩
    · have : p ≠ t.bv := by rintro rfl; rw [hk] at hp; cases hp
      simp [updK, this, hp]
    · by_cases e : p = t.bv
      · subst e; rw [hk] at hp; cases hp
        exact ⟨x', by simp [updK], est, eb, ep⟩
      · exact ⟨z, by simp [updK, e, hp], rfl, rfl, rfl⟩

/-- Writing a TCB's `YIELD_TO` word (`tcb_yield_to := v`). -/
theorem SchedRel.set_yt {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (v : U64) :
    SchedRel st N T C c (L.wr s (yieldA t) v) (updK σ t.bv (.tcb { x with tcbYieldTo := optRef v })) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (yieldA t) v)) ∧
      KView σ (updK σ t.bv (.tcb { x with tcbYieldTo := optRef v })) :=
  hS.set_tw ht hk (K := 3472#u64) (by simp) (by simp) (by simp [SchedField]) (by decide) (by decide) (by decide)
    (by decide) (by decide) { x with tcbYieldTo := optRef v } rfl rfl rfl rfl rfl v

theorem yieldA_aligned {T : Set U64} (hT : TcbPlaced T) {t : U64} (ht : t ∈ T) : Aligned (yieldA t) :=
  field_aligned (hT t ht) (K := 3472#u64) (by simp) (by simp)

theorem yieldA_inj {T : Set U64} (hT : TcbPlaced T) {t y : U64} (ht : t ∈ T) (hy : y ∈ T)
    (e : yieldA y = yieldA t) : y = t :=
  ((tt_eq_iff (hT y hy) (hT t ht) (K1 := 3472#u64) (K2 := 3472#u64) (by simp) (by simp)).1 e).1

end

end

end Fl4Proofs.P3.Sched
