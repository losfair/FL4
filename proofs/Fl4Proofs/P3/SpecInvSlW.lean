/-
P3 (DESIGN.md §9), invariant line G1 (sl1): **the binding writers keep `SL I K`**
when the objects they make live are in `K` (spec side only).

* `sl_threadSetK` / `sl_updateSchedContextK`: any TCB / SC update at an object of
  `K` (keeping the TCB's caps).
* `sl_schedContextDonate c t (c ∈ K) (t ∈ K)` (the donor is unbound first: free),
  `sl_schedContextBindTcb c t`, `sl_schedContextBindNtfn c n (c ∈ K)`,
  `sl_bindScReply c r (c ∈ K)`.
* `sl_replyPush`: the callee in `K`; the caller's SC is read bound to the
  caller, so (`ScBackS`, sb1) it is bound back and live: it joins `K` by
  `sl_consL` before `bind_sc_reply` makes its reply stack non-empty.
* `sl_maybeDonateSc`: the woken thread in `K`, the notification's SC named
  (`NSc`: l4v `sym_refs` of `ntfn_sc`/`sc_ntfn` + if_live at the SC; not carried yet).
* `sl_replyRemove`: the caller in `K`; the SC holding the reply on its stack
  (`sc_with_reply`) is live, so it joins `K` at the read.
-/
import Fl4Proofs.P3.SpecInvSlF6
import Fl4Proofs.P3.SpecInvSbW
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

section W
variable {I : ObjRef × ObjRef} {K : List ObjRef}

theorem sl_threadSetK (f : Tcb → Tcb) (t : ObjRef) (ht : t ∈ K) (hc : ∀ x, tcbCnodeMap (f x) = tcbCnodeMap x) :
    SLK I K (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => sl_setObject_p _ _ σ fun _ old hk _ => ?_
  rw [getTcb_kheap hx] at hk; cases hk
  exact ⟨hc x, fun _ => Or.inl ht⟩

theorem sl_updateSchedContextK (p : ObjRef) (f : SchedContext → SchedContext) (hp : p ∈ K) :
    SLK I K (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  exact sl_update hσ hk ⟨rfl, fun _ => Or.inl hp⟩

/-- `sl_auto` with the `K` writers at `c` / `t`. -/
macro "slk_auto" hc:term:max ht:term:max : tactic => `(tactic| repeat' (first | sl_leaf | (with_reducible exact sl_updateSchedContextK _ _ $hc) | ((with_reducible refine sl_threadSetK _ _ $ht ?_); intro _; rfl) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem sl_schedContextDonate (c t : ObjRef) (hc : c ∈ K) (ht : t ∈ K) :
    SLK I K (schedContextDonate (Z := Unit) c t) := by
  unfold schedContextDonate; slk_auto hc ht

theorem sl_schedContextBindTcb (c t : ObjRef) (hc : c ∈ K) (ht : t ∈ K) :
    SLK I K (schedContextBindTcb (Z := Unit) c t) := by
  unfold schedContextBindTcb; slk_auto hc ht

theorem sl_schedContextBindNtfn (c n : ObjRef) (hc : c ∈ K) :
    SLK I K (schedContextBindNtfn (Z := Unit) c n) := by
  unfold schedContextBindNtfn; slk_auto hc hc

theorem sl_bindScReply (c r : ObjRef) (hc : c ∈ K) : SLK I K (bindScReply (Z := Unit) c r) := by
  unfold bindScReply; slk_auto hc hc

theorem ik_when_of {P : State Unit → Prop} (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit}
    (h : Q → IK P m) : IK P (NonDet.when Q m) := by
  unfold NonDet.when
  by_cases hq : Q
  · rw [if_pos hq]; exact h hq
  · rw [if_neg hq]; exact ik_pure' _

theorem the_mem {a : Option ObjRef} (h : a ≠ none) (K : List ObjRef) : the a ∈ a.toList ++ K := by
  cases a with
  | none => exact absurd rfl h
  | some c => simp [the]

/-- **`reply_push`**: the callee in `K`; the caller's SC, read bound to the caller,
is bound back (`ScBackS`), so live: it joins `K` before `bind_sc_reply`. -/
theorem sl_replyPush (caller callee r : ObjRef) (d : Bool) (hce : callee ∈ K) :
    HK (fun σ => SL I K σ ∧ SInvB.ScBackS σ) (SL I K) (replyPush (Z := Unit) caller callee r d) := by
  intro σ ⟨hσ, hB⟩ x hx
  unfold replyPush at hx
  obtain ⟨⟨a, s1⟩, hy1, hx⟩ := hx
  obtain ⟨e1, xa, hxa, ha⟩ := SInvB.mem_getTcbSc hy1
  simp only at e1 ha; subst s1
  have h0 : SL I (a.toList ++ K) σ := by
    cases a with
    | none => exact hσ
    | some c =>
      obtain ⟨y, k, hy, hyt, -⟩ := hB caller xa c hxa ha
      exact sl_consL hσ hy (Or.inl (by rw [hyt]; simp))
  have hce' : callee ∈ a.toList ++ K := List.mem_append_right _ hce
  refine sl_mono ((?_ : SLK I (a.toList ++ K) _) σ h0 x hx) fun u hu => List.mem_append_right _ hu
  repeat' (first
    | (refine ik_when_of _ fun hc => ik_bind (sl_bindScReply _ _ (the_mem hc.1 _)) fun _ =>
        sl_schedContextDonate _ _ (the_mem hc.1 _) hce')
    | sl_leaf | ik_step0 | ik_unfold)

theorem theL_spec {α : Type} [Nonempty α] {P : α → Prop} (h : ∃! x, P x) : P (The P) := by
  unfold The; rw [dif_pos h]; exact (Classical.choose_spec h).1

theorem scWithReply_memL {σ : State Unit} {r p : ObjRef} (h : scWithReply r σ = some p) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ r ∈ y.scReplies := by
  unfold scWithReply partialInv at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  have := theL_spec hex
  simpa using this

/-- **`reply_remove`**: the caller in `K`; the SC whose reply stack holds the
reply is live (its stack is not empty), so it joins `K` at the read. -/
theorem sl_replyRemove (caller r : ObjRef) (hc : caller ∈ K) : SLK I K (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove
  refine ik_bind (by sl_auto) fun reply => ik_bind (ik_assert _) fun _ => ik_gets_bind fun σ => ?_
  cases e : scWithReply r σ with
  | none => exact ikp_of_ik (by sl_auto) σ
  | some p =>
    obtain ⟨y, n, hy, hr⟩ := scWithReply_memL e
    intro hσ x hx
    have h1 : SL I (p :: K) σ := sl_consL hσ hy (Or.inr (Or.inr (List.ne_nil_of_mem hr)))
    have hp : p ∈ p :: K := List.mem_cons.2 (Or.inl rfl)
    have hc' : caller ∈ p :: K := List.mem_cons_of_mem _ hc
    refine sl_tail ((?_ : SLK I (p :: K) _) σ h1 x hx)
    slk_auto hp hc'

/-- The notification's SC is named (l4v `sym_refs` of `ntfn_sc` / `sc_ntfn` with
`if_live_then_nonz_cap` at the SC: NOT carried yet, see KENTRY-PLAN sl1). -/
def NSc (I : ObjRef × ObjRef) (n : ObjRef) (σ : State Unit) : Prop :=
  ∀ ntf c, σ.kheap n = some (.notification ntf) → ntf.ntfnSc = some c → Nm I σ c

theorem mem_getNtfnSc {n : ObjRef} {σ : State Unit} {y : Option ObjRef × State Unit}
    (h : y ∈ (getNtfnObjRef (Z := Unit) Notification.ntfnSc n σ).1) :
    y.2 = σ ∧ ∃ a, σ.kheap n = some (.notification a) ∧ a.ntfnSc = y.1 := by
  unfold getNtfnObjRef getSkObjRef at h
  obtain ⟨⟨a, s3⟩, h3, h⟩ := h
  obtain ⟨hk, hs⟩ := mem_getSimpleKo h3
  simp only at hk hs; subst s3
  rw [Set.mem_singleton_iff.1 h]
  exact ⟨rfl, a, hk, rfl⟩

/-- **`maybe_donate_sc`**: the woken thread in `K`; the notification's SC named (`NSc`). -/
theorem sl_maybeDonateSc (t n : ObjRef) (ht : t ∈ K) :
    HK (fun σ => SL I K σ ∧ NSc I n σ) (SL I K) (maybeDonateSc (Z := Unit) t n) := by
  intro σ ⟨hσ, hN⟩ x hx
  unfold maybeDonateSc at hx
  obtain ⟨⟨a, s1⟩, hy1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvB.mem_getTcbSc hy1
  simp only at e1; subst s1
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · obtain ⟨⟨b, s2⟩, hy2, hx⟩ := hx
    obtain ⟨e2, ntf, hk, hb⟩ := mem_getNtfnSc hy2
    simp only at e2 hb; subst s2
    cases b with
    | none => rw [Set.mem_singleton_iff.1 hx]; exact hσ
    | some c =>
      have h1 : SL I (c :: K) σ := sl_cons hσ (hN ntf c hk hb)
      have hc : c ∈ c :: K := List.mem_cons.2 (Or.inl rfl)
      have ht' : t ∈ c :: K := List.mem_cons_of_mem _ ht
      refine sl_tail ((?_ : SLK I (c :: K) (NonDet.maybeM _ (some c))) σ h1 x hx)
      unfold NonDet.maybeM
      dsimp only
      slk_auto hc ht'
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

end W

end

end Fl4Proofs.P3.SInvL
