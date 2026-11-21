/-
P3 (DESIGN.md §9), invariant line G1 (vih3): **the deletion path of
`ValidIrqMasks ∧ ValidIrqHandlers`** (spec side only; outside the `JAtZ` cone).

The deletion is the only place an IRQ line becomes inactive: `rec_del`'s
`CTEDeleteCall` empties the slot with the cleanup cap `IRQHandlerCap irq` that
`finalise_cap` returned for a *final* handler cap, and `post_cap_deletion`
sets the line inactive. l4v carries `is_final_cap'` from `finalise_slot`
through `deleting_irq_handler` (which only empties the IRQ-node slot) to
`empty_slot`. Here:

* `Uniq irq sl σ`: `sl` is the only slot holding `irqHandlerCap irq`
  (`final_handler_unique` gives it from finality); a `WLH` predicate kept by
  `set_cap NullCap` anywhere.
* `HT Q Post m`: Hoare triples with the result (`Post` reads the outcome).
* `vi_emptySlot_p`: `empty_slot sl c` keeps `VI` when a handler cleanup cap's
  line is named only by `sl`; `vi_capDeleteOne_u` (`cap_delete_one`: cleanup
  `NullCap`, no IRQ state change) keeps `VI ∧ U` for every `WLH` `U` kept by
  `set_cap NullCap` (so `Uniq` survives `deleting_irq_handler`);
  `rv_finaliseCap`: the remainder is never a handler cap and the cleanup cap
  is a handler cap only for the finalised handler cap itself.
* `vi_recDel`: **`rec_del` keeps `VI`, and a `FinaliseSlotCall slot` returning
  the cleanup cap `IRQHandlerCap irq` ends with `Uniq irq slot`** — by the
  least-fixed-point argument with a result-dependent post (`ht_lfp`).
  `vi_capDelete`, `vi_capRevoke`.
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersW
open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-- `sl` is the only slot naming `irq`. -/
def Uniq (irq : Irq) (sl : CslotPtr) (σ : State Unit) : Prop :=
  ∀ p cref, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → (p, cref) = sl

instance (irq : Irq) (sl : CslotPtr) : WLH (Uniq irq sl) :=
  wlh_of_hV fun _ _ e h p cref hc => h p cref (by rw [← hV_cap e]; exact hc)

theorem uniq_setCap_null {irq : Irq} {sl sl' : CslotPtr} {σ : State Unit} {x : Unit × State Unit}
    (h : Uniq irq sl σ) (hx : x ∈ (setCap (Z := Unit) .nullCap sl' σ).1) : Uniq irq sl x.2 := by
  obtain ⟨o, r⟩ := sl'
  intro p cref hc
  rcases (vih_setCap_out hx).2 p cref _ hc with ⟨-, -, e⟩ | ⟨-, h0⟩
  · cases e
  · exact h p cref h0

/-! ## Hoare triples with results -/

def HT {α : Type} (Q : State Unit → Prop) (Post : α → State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, Q σ → ∀ x, x ∈ (m σ).1 → Post x.1 x.2

section HTs
variable {Q : State Unit → Prop}

theorem ht_bind {α β : Type} {Q' : α → State Unit → Prop} {Post : β → State Unit → Prop}
    {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : HT Q Q' m) (hg : ∀ a, HT (Q' a) Post (g a)) :
    HT Q Post (m >>= g) := by
  intro σ h x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm σ h y hy) x hx

theorem ht_ik {α : Type} {m : NonDet (State Unit) α} (h : IK Q m) : HT Q (fun _ => Q) m := h

theorem ht_mono {α : Type} {Q2 : State Unit → Prop} {P1 P2 : α → State Unit → Prop} {m : NonDet (State Unit) α}
    (h : HT Q P1 m) (hq : ∀ σ, Q2 σ → Q σ) (hp : ∀ a σ, P1 a σ → P2 a σ) : HT Q2 P2 m :=
  fun σ hσ x hx => hp _ _ (h σ (hq σ hσ) x hx)

/-- The exception bind: the continuation from `.ok` outcomes; errors propagate. -/
theorem hte_bind {ε α β : Type} {Q' : Except ε α → State Unit → Prop} {Post : Except ε β → State Unit → Prop}
    {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : HT Q Q' m.run)
    (hg : ∀ a, HT (Q' (.ok a)) Post (g a).run) (he : ∀ e σ, Q' (.error e) σ → Post (.error e) σ) :
    HT Q Post (m >>= g).run := by
  intro σ h x hx
  obtain ⟨z, hz, ⟨a, ha, hx⟩ | ⟨e, he', rfl⟩⟩ := mem_bindE_inv' hx
  · obtain ⟨r, s⟩ := z; simp only at ha; subst ha
    exact hg a s (hm σ h _ hz) x hx
  · obtain ⟨r, s⟩ := z; simp only at he'; subst he'
    exact he e s (hm σ h _ hz)

theorem hte_liftE {ε α : Type} {P : α → State Unit → Prop} {m : NonDet (State Unit) α} (h : HT Q P m) :
    HT Q (fun r s => ∃ a, r = (.ok a : Except ε α) ∧ P a s) (NonDetE.liftE (ε := ε) m).run := by
  intro σ hσ x hx
  obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
  exact ⟨y.1, rfl, h σ hσ y hy⟩

theorem hte_returnOk {ε α : Type} {P : Except ε α → State Unit → Prop} {a : α} (h : ∀ σ, Q σ → P (.ok a) σ) :
    HT Q P (NonDetE.returnOk a : NonDetE (State Unit) ε α).run := by
  intro σ hσ x hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact h σ hσ

end HTs

/-- `HT` of the least fixed point: a pre-fixed point argument with a
result-dependent post (`ik_lfp` generalised). -/
theorem ht_lfp {ι α : Type} {F : (ι → NonDet (State Unit) α) → ι → NonDet (State Unit) α}
    (Q : State Unit → Prop) (Post : ι → α → State Unit → Prop)
    (hF : ∀ f : ι → NonDet (State Unit) α, (∀ k, HT Q (Post k) (f k)) → ∀ k, HT Q (Post k) (F f k)) (i : ι) :
    HT Q (Post i) (NonDet.lfp F i) := by
  intro σ hσ x hx
  let f : ι → NonDet (State Unit) α := fun k t => ({y | Q t → Post k y.1 y.2}, True)
  have hf : ∀ k t, F f k t ≤ f k t := fun k t =>
    ⟨fun y hy => fun ht => hF f (fun k' t' ht' z hz => hz ht') k t ht y hy, fun _ => trivial⟩
  exact (ik_lfp_le F f hf i σ).1 hx hσ

/-! ## Result values -/

/-- Every outcome's value satisfies `Pr`. -/
def RV {α : Type} (Pr : α → Prop) (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → Pr x.1

section RVs
theorem rv_bind {α β : Type} {Pr : β → Prop} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hg : ∀ a, RV Pr (g a)) : RV Pr (m >>= g) := fun σ x ⟨y, _, hx⟩ => hg y.1 y.2 x hx
theorem rv_pure {α : Type} {Pr : α → Prop} {a : α} (h : Pr a) : RV Pr (pure a : NonDet (State Unit) α) :=
  fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]; exact h
theorem rv_liftM {α β : Type} {Pr : β → Prop} {g : α → β} {m : NonDet (State Unit) α} (h : ∀ a, Pr (g a)) :
    RV Pr (NonDet.liftM g m) := by
  intro σ x hx; unfold NonDet.liftM at hx; obtain ⟨y, _, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx]; exact h _
theorem rv_fail {α : Type} {Pr : α → Prop} : RV Pr (NonDet.fail : NonDet (State Unit) α) := fun _ _ hx => hx.elim

theorem ht_of_ik_rv {α : Type} {P : State Unit → Prop} {Pr : α → Prop} {m : NonDet (State Unit) α}
    (h1 : IK P m) (h2 : RV Pr m) : HT P (fun a s => P s ∧ Pr a) m :=
  fun σ hσ x hx => ⟨h1 σ hσ x hx, h2 σ x hx⟩
end RVs

/-- The result facts of `finalise_cap`'s literal returns. -/
theorem rv_fc_pure {c : Cap} {a : Cap × Cap} (h1 : ∀ irq, a.1 ≠ .irqHandlerCap irq)
    (h2 : ∀ irq, a.2 = .irqHandlerCap irq → c = .irqHandlerCap irq) :
    RV (fun r : Cap × Cap => (∀ irq, r.1 ≠ .irqHandlerCap irq) ∧
      (∀ irq, r.2 = .irqHandlerCap irq → c = .irqHandlerCap irq)) (pure a : NonDet (State Unit) (Cap × Cap)) :=
  rv_pure (And.intro h1 h2)

macro "rv_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible refine rv_fc_pure (fun _ h => ?_) (fun _ h => ?_) <;> (try split at h) <;> simp_all; done)
  | (with_reducible refine rv_liftM (fun _ => And.intro (fun _ h => ?_) (fun _ h => ?_)) <;> simp_all; done)
  | (with_reducible exact rv_fail)
  | (with_reducible refine rv_bind fun _ => ?_)
  | split))

/-- **`finalise_cap`'s results**: the remainder is no handler cap; a handler
cleanup cap comes only from the finalised handler cap. -/
theorem rv_finaliseCap (c : Cap) (fin : Bool) :
    RV (fun r : Cap × Cap => (∀ irq, r.1 ≠ .irqHandlerCap irq) ∧
      (∀ irq, r.2 = .irqHandlerCap irq → c = .irqHandlerCap irq)) (finaliseCap (Z := Unit) c fin) := by
  cases c with
  | irqHandlerCap irq =>
    simp only [finaliseCap]; split
    · exact rv_bind fun _ => rv_fc_pure (fun _ h => by simp_all) (fun _ h => by simp_all)
    · exact rv_fc_pure (fun _ h => by simp_all) (fun _ h => by simp_all)
  | archObjectCap a =>
    simp only [finaliseCap]; unfold archFinaliseCap
    rv_auto
  | _ => simp only [finaliseCap]; rv_auto

/-! ## `empty_slot` and `cap_delete_one` -/

theorem vi_postCapDeletion_tail {c : Cap} {sl : CslotPtr} {σ : State Unit} (h : VI σ)
    (hu : ∀ irq, c = .irqHandlerCap irq → Uniq irq sl σ) :
    ∀ x ∈ ((setCap (Z := Unit) .nullCap sl >>= fun _ => postCapDeletion (Z := Unit) c) σ).1, VI x.2 := by
  rintro x ⟨y, hy, hx⟩
  have h1 : VI y.2 := vh_setCap .nullCap sl (fun _ _ => ca_noH (fun _ h => by cases h) _) σ h y hy
  cases c with
  | irqHandlerCap irq =>
    have hn := setCap_null_unique (hu irq rfl) hy
    simp only [postCapDeletion, deletedIrqHandler] at hx
    exact ⟨vim_sis _ _ _ h1.1 x hx, h1.2.1.hk (hk_setIrqState_inactive hn x hx), trivial⟩
  | archObjectCap a =>
    simp only [postCapDeletion] at hx; exact (hv_archPostCapDeletion a : IKH VI _) _ h1 x hx
  | _ => simp only [postCapDeletion] at hx; exact (ik_pure () : IKH VI _) _ h1 x hx

/-- `VI` and the uniqueness of a handler cleanup cap's line. -/
def ESQ (c : Cap) (sl : CslotPtr) (s : State Unit) : Prop :=
  VI s ∧ ∀ irq, c = .irqHandlerCap irq → Uniq irq sl s

instance (c : Cap) (sl : CslotPtr) : WLH (ESQ c sl) :=
  have : WLH (fun s : State Unit => ∀ irq, c = .irqHandlerCap irq → Uniq irq sl s) :=
    wlh_of_hV fun σ σ' e h irq hc p cref hc' => h irq hc p cref (by rw [← hV_cap e]; exact hc')
  inferInstanceAs (WLH fun s => VI s ∧ ∀ irq, c = .irqHandlerCap irq → Uniq irq sl s)

/-- **`empty_slot`** with the cleanup cap's line named only by the emptied slot. -/
theorem vi_emptySlot_p (sl : CslotPtr) (c : Cap) (σ : State Unit)
    (hu : ∀ irq, c = .irqHandlerCap irq → Uniq irq sl σ) : IKp VI σ (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot
  refine ikp_getCap_bind fun cap _ => ?_
  split
  · exact ikp_of_ik (ik_pure _) σ
  · intro h x hx
    have key : ∀ s, ESQ c sl s → ∀ x ∈ ((setCap (Z := Unit) .nullCap sl >>= fun _ => postCapDeletion (Z := Unit) c) s).1,
        VI x.2 := fun s hs => vi_postCapDeletion_tail hs.1 hs.2
    obtain ⟨y1, hy1, hx⟩ := hx
    obtain ⟨y2, hy2, hx⟩ := hx
    obtain ⟨y3, hy3, hx⟩ := hx
    obtain ⟨y4, hy4, hx⟩ := hx
    obtain ⟨y5, hy5, hx⟩ := hx
    obtain ⟨y6, hy6, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hy1
    obtain rfl := Set.mem_singleton_iff.1 hy2
    obtain rfl := Set.mem_singleton_iff.1 hy3
    have q4 : ESQ c sl y4.2 := hv_setCdt (P := ESQ c sl) _ _ ⟨h, hu⟩ y4 hy4
    have q5 : ESQ c sl y5.2 := ik_doExtendedOp (P := ESQ c sl)
      (fun σ e h => WLH.view σ { σ with exst := e } (by rfl) (by rfl) h) _ _ q4 y5 hy5
    have q6 : ESQ c sl y6.2 := hv_setOriginal (P := ESQ c sl) _ _ _ q5 y6 hy6
    exact key _ q6 x hx

section U
variable {U : State Unit → Prop} [WLH U]

theorem vhu_setCap_null (hU : ∀ sl σ x, U σ → x ∈ (setCap (Z := Unit) .nullCap sl σ).1 → U x.2) (sl : CslotPtr) :
    IKH (fun σ => VI σ ∧ U σ) (setCap (Z := Unit) .nullCap sl) :=
  fun σ h x hx => ⟨vh_setCap .nullCap sl (fun _ _ => ca_noH (fun _ h => by cases h) _) σ h.1 x hx, hU sl σ x h.2 hx⟩

/-- **`cap_delete_one`** (cleanup `NullCap`: no IRQ state change) keeps `VI ∧ U`. -/
theorem vi_capDeleteOne_u (hU : ∀ sl σ x, U σ → x ∈ (setCap (Z := Unit) .nullCap sl σ).1 → U x.2)
    (sl : CslotPtr) : IKH (fun σ => VI σ ∧ U σ) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne emptySlot
  simp only [postCapDeletion]
  repeat' (first | (with_reducible exact vhu_setCap_null hU _) | hv_leaf | ik_step0 | ik_unfold)

end U

theorem vi_capDeleteOne (sl : CslotPtr) : IKH VI (capDeleteOne (Z := Unit) sl) := by
  have : WLH (fun _ : State Unit => True) := wlh_of_hV fun _ _ _ _ => trivial
  intro σ h x hx
  exact (vi_capDeleteOne_u (U := fun _ => True) (fun _ _ _ _ _ => trivial) sl σ ⟨h, trivial⟩ x hx).1

theorem vi_deletingIrqHandler_uniq (irq : Irq) (sl : CslotPtr) :
    IKH (fun σ => VI σ ∧ Uniq irq sl σ) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler
  exact ik_bind (ik_gets _) fun s => vi_capDeleteOne_u (fun _ _ _ h hx => uniq_setCap_null h hx) s

theorem vi_deletingIrqHandler (irq : Irq) : IKH VI (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler
  exact ik_bind (ik_gets _) fun s => vi_capDeleteOne s

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_capDeleteOne _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_deletingIrqHandler _)

/-- `finalise_cap` keeps `VI`. -/
theorem vi_finaliseCap (c : Cap) (fin : Bool) : IKH VI (finaliseCap (Z := Unit) c fin) := by
  cases c <;> unfold finaliseCap <;> hv_auto

/-! ## `rec_del` -/

/-- The post of `rec_del`: `VI`, and a `FinaliseSlotCall slot` returning a
handler cleanup cap leaves its line named only by `slot`. -/
def RDPost (k : RecDelCall) (r : Except Unit (Bool × Cap)) (s : State Unit) : Prop :=
  VI s ∧ ∀ sl e, k = .finaliseSlotCall sl e → ∀ b irq, r = .ok (b, .irqHandlerCap irq) → Uniq irq sl s

theorem ik_of_ht_rd {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (h : ∀ k, HT VI (RDPost k) (f k)) (k : RecDelCall) : IKHE (ε := Unit) VI (f k : PMonad Unit (Bool × Cap)) :=
  fun σ hσ x hx => (h k σ hσ x hx).1

theorem ht_of_ik_rd {k : RecDelCall} {m : NonDet (State Unit) (Except Unit (Bool × Cap))} (h : IK VI m)
    (hk : ∀ sl e, k ≠ .finaliseSlotCall sl e) : HT VI (RDPost k) m :=
  fun σ hσ x hx => ⟨h σ hσ x hx, fun sl e e' => absurd e' (hk sl e)⟩

set_option maxHeartbeats 4000000 in
/-- The `FinaliseSlotCall` step. -/
theorem ht_recDelF_fin {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, HT VI (RDPost k) (f k)) (slot : CslotPtr) (ex : Bool) :
    HT VI (RDPost (.finaliseSlotCall slot ex)) (recDelF (Z := Unit) f (.finaliseSlotCall slot ex)).run := by
  have hrec' := ik_of_ht_rd hrec
  have post_ok : ∀ s b c, VI s → (∀ irq, c = .irqHandlerCap irq → Uniq irq slot s) →
      RDPost (.finaliseSlotCall slot ex) (.ok (b, c)) s := by
    intro s b c h hu
    refine ⟨h, fun sl e he b' irq hr => ?_⟩
    simp only [RecDelCall.finaliseSlotCall.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    exact hu irq hr.2
  have post_err : ∀ e s, VI s → RDPost (.finaliseSlotCall slot ex) (.error e) s :=
    fun e s h => ⟨h, fun _ _ _ _ _ hr => by cases hr⟩
  unfold recDelF withoutPreemption
  -- the cap read
  refine hte_bind (Q' := fun r s => ∃ c, r = .ok c ∧ VI s ∧ capOpt (s.kheap slot.1) slot.2 = some c)
    (fun σ h x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      obtain ⟨o, r⟩ := slot
      obtain ⟨e1, e2⟩ := vih_mem_getCap hy
      exact ⟨y.1, rfl, by rw [e1]; exact h, by rw [e1]; exact e2⟩) (fun cap => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  refine ht_mono (Q := fun s => VI s ∧ capOpt (s.kheap slot.1) slot.2 = some cap) ?_
    (fun s ⟨c, hc, h, hs⟩ => by cases hc; exact ⟨h, hs⟩) (fun _ _ h => h)
  split
  · exact hte_returnOk fun s h => post_ok s _ _ h.1 (fun _ h' => by cases h')
  -- finality
  refine hte_bind (Q' := fun r s => ∃ b, r = .ok b ∧ VI s ∧ capOpt (s.kheap slot.1) slot.2 = some cap ∧
      (b = true → isFinalCap' (Z := Unit) cap s))
    (fun σ h x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      unfold isFinalCap at hy
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨_, rfl, h.1, h.2, fun hb => of_decide_eq_true hb⟩) (fun fin => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  refine ht_mono (Q := fun s => VI s ∧ capOpt (s.kheap slot.1) slot.2 = some cap ∧
      (fin = true → isFinalCap' (Z := Unit) cap s)) ?_
    (fun s ⟨c, hc, h⟩ => by cases hc; exact h) (fun _ _ h => h)
  -- finalise_cap: remainder no handler cap, cleanup's line named only by `slot`
  refine hte_bind (Q' := fun r s => ∃ rc, r = .ok rc ∧ VI s ∧ (∀ irq, rc.1 ≠ .irqHandlerCap irq) ∧
      (∀ irq, rc.2 = .irqHandlerCap irq → Uniq irq slot s)) ?_ (fun rc => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  · intro σ h x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    refine ⟨y.1, rfl, vi_finaliseCap cap fin σ h.1 y hy, (rv_finaliseCap cap fin σ y hy).1, fun irq hc => ?_⟩
    have hcap := (rv_finaliseCap cap fin σ y hy).2 irq hc
    subst hcap
    cases fin with
    | false =>
      simp only [finaliseCap] at hy
      rw [if_neg (by simp)] at hy
      rw [Set.mem_singleton_iff.1 hy] at hc; cases hc
    | true =>
      have hu := final_handler_unique (h.2.2 rfl) h.2.1
      simp only [finaliseCap, if_true] at hy
      obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (vi_deletingIrqHandler_uniq irq slot σ ⟨h.1, hu⟩ z hz).2
  obtain ⟨rem, cl⟩ := rc
  refine ht_mono (Q := fun s => VI s ∧ (∀ irq, rem ≠ .irqHandlerCap irq) ∧
      (∀ irq, cl = .irqHandlerCap irq → Uniq irq slot s)) ?_
    (fun s ⟨c, hc, h⟩ => by cases hc; exact h) (fun _ _ h => h)
  dsimp only
  split
  · exact hte_returnOk fun s h => post_ok s _ _ h.1 h.2.2
  split
  · refine hte_bind (Q' := fun r s => ∃ u, r = .ok u ∧ VI s) ?_ (fun _ => ?_)
      (fun e s ⟨_, he, _⟩ => by cases he)
    · intro σ h x hx
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      exact ⟨_, rfl, vh_setCap rem slot (fun _ _ => ca_noH h.2.1 _) σ h.1 y hy⟩
    · exact ht_mono (hte_returnOk (Q := VI) fun s h => post_ok s _ _ h (fun _ h' => by cases h'))
        (fun s ⟨_, hc, h⟩ => h) (fun _ _ h => h)
  · refine hte_bind (Q' := fun r s => ∃ u, r = .ok u ∧ VI s) ?_ (fun _ => ?_)
      (fun e s ⟨_, he, _⟩ => by cases he)
    · intro σ h x hx
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      exact ⟨_, rfl, vh_setCap rem slot (fun _ _ => ca_noH h.2.1 _) σ h.1 y hy⟩
    refine ht_mono (Q := VI) ?_ (fun s ⟨_, _, h⟩ => h) (fun _ _ h => h)
    refine hte_bind (Q' := fun r s => VI s) (fun σ h x hx => hrec' _ σ h x hx) (fun _ => ?_) (fun e s h => post_err e s h)
    refine hte_bind (Q' := fun r s => VI s) (fun σ h x hx => hv_preemptionPoint σ h x hx) (fun _ => ?_)
      (fun e s h => post_err e s h)
    exact hrec _

set_option maxHeartbeats 4000000 in
/-- One step of `rec_del`, its recursive calls satisfying `RDPost`. -/
theorem ht_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, HT VI (RDPost k) (f k)) (k : RecDelCall) : HT VI (RDPost k) (recDelF (Z := Unit) f k) := by
  have hrec' := ik_of_ht_rd hrec
  cases k with
  | finaliseSlotCall sl e => exact ht_recDelF_fin hrec sl e
  | cTEDeleteCall sl e =>
    have hk : ∀ sl' e', RecDelCall.cTEDeleteCall sl e ≠ .finaliseSlotCall sl' e' := fun _ _ h => by cases h
    show HT VI (RDPost _) (recDelF (Z := Unit) f (.cTEDeleteCall sl e)).run
    unfold recDelF withoutPreemption
    refine hte_bind (Q' := RDPost (.finaliseSlotCall sl e)) (hrec _) (fun r => ?_)
      (fun er s h => ⟨h.1, fun _ _ h' => absurd h' (hk _ _)⟩)
    obtain ⟨b, cl⟩ := r
    dsimp only
    refine hte_bind (Q' := fun r s => VI s) ?_ (fun _ => hte_returnOk fun s h => ⟨h, fun _ _ h' => absurd h' (hk _ _)⟩)
      (fun er s h => ⟨h, fun _ _ h' => absurd h' (hk _ _)⟩)
    intro σ h x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    unfold NonDet.when at hy
    split at hy
    · exact vi_emptySlot_p sl cl σ (fun irq hc => h.2 sl e rfl b irq (by rw [hc])) h.1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact h.1
  | reduceZombieCall c sl e =>
    refine ht_of_ik_rd ?_ (fun _ _ h => by cases h)
    show IKHE VI (recDelF (Z := Unit) f (.reduceZombieCall c sl e))
    unfold recDelF withoutPreemption
    split <;> (try (exfalso; simp_all; done)) <;> hv_auto
    all_goals exact hrec' _

/-- **`rec_del`** (module docstring). -/
theorem vi_recDel (k : RecDelCall) : HT VI (RDPost k) (recDel (Z := Unit) k) := by
  unfold recDel
  exact ht_lfp VI RDPost (fun f hf k => ht_recDelF hf k) k

theorem vi_recDelE (k : RecDelCall) : IKHE (ε := Unit) VI (recDel (Z := Unit) k) :=
  fun σ h x hx => (vi_recDel k σ h x hx).1

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_recDelE _)

theorem vi_capDelete (sl : CslotPtr) : IKHE (ε := Unit) VI (capDelete (Z := Unit) sl) := by
  unfold capDelete; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_capDelete _)

theorem vi_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IKH VI (f k)) (sl : CslotPtr) : IKHE (ε := Unit) VI (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKHE (ε := Unit) VI (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  hv_auto
  all_goals exact hrec' _

theorem vi_capRevoke (sl : CslotPtr) : IKHE (ε := Unit) VI (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => vi_capRevokeF hf k) sl

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_capRevoke _)

end

end Fl4Proofs.P3.SInvV
