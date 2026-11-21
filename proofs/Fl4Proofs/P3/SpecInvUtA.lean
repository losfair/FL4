/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut3): **hand-written
`IK UtInv'` leaves for the generated ancestor frames** (spec side only; imports
only Fl4Spec via SpecInvUtD).

* The VSpace map performs (`perform_page_invocation`, `perform_page_table`,
  `_directory`, `_pdpt_invocation`) write the invocation's cap with `set_cap`
  and then fail unless it is the matching arch cap: for a null or untyped cap
  they have no outcome (`ik_of_empty`), for any other cap `hv_setCap_nn`.
* `ik_checkCapAt_ins`: the TCB installs' `check_cap_at newCap src (check_cap_at
  (ThreadCap t) slot (cap_insert newCap src dest))`; `same_object_as` of an
  untyped cap is `False`, so an untyped `newCap` is never inserted.
* `finaliseCap_nu`: `finalise_cap`'s remainder is never untyped (null or a
  zombie), so `rec_del`'s `set_cap remainder` of a non-removable remainder is a
  `set_cap` of a non-null cap that is not untyped.
* The IPC cap transfer: `get_receive_slots` returns at most one slot, the
  extra caps are still in their slots when they are derived (`copy_mrs` and
  the badge writes keep the view), and `derive_cap` of an untyped cap ran
  `ensure_no_children` (`okv_deriveCap`): `ui_transferCapsLoop`,
  `ui_transferCaps`, `ui_doNormalTransfer`.
-/
import Fl4Proofs.P3.SpecInvUtDA
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Computations without an outcome -/

theorem ik_of_empty {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : ∀ s, (m s).1 = ∅) :
    IK P m := fun σ _ x hx => by rw [h σ] at hx; exact hx.elim

theorem nd_bind_empty {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (h : ∀ a s, (g a s).1 = ∅) (s : State Unit) : ((m >>= g) s).1 = ∅ := by
  apply Set.subset_empty_iff.1
  rintro x ⟨y, -, hx⟩
  rw [h] at hx; exact hx

theorem nd_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} (s : State Unit) :
    ((NonDet.fail >>= g) s).1 = ∅ := by
  apply Set.subset_empty_iff.1
  rintro x ⟨y, hy, -⟩
  exact hy

theorem not_nnu {c : Cap} (h : ¬ NNU c) : c = .nullCap ∨ ∃ d b n f, c = .untypedCap d b n f := by
  by_cases e : c = .nullCap
  · exact Or.inl e
  · refine Or.inr ?_
    by_contra hu
    exact h ⟨e, fun d b n f e' => hu ⟨d, b, n, f, e'⟩⟩

/-- Side conditions: a cap that is not null and not untyped / not untyped. -/
macro "nnu_side" : tactic => `(tactic| first | assumption | exact And.intro (fun h => nomatch h) (fun _ _ _ _ h => nomatch h))
macro "nu_side" : tactic => `(tactic| first | assumption | exact fun _ _ _ _ h => nomatch h)

/-- The leaves usable before the generated frames. -/
macro "ui0_leaf" : tactic => `(tactic| first
  | (refine ik_setCap_nn _ ?_ _; nnu_side)
  | (refine ik_utInv'_of_uk fun _ => ?_; uk_leaf; done)
  | (refine ike_utInv'_of_uk fun _ => ?_; uk_leaf; done)
  | exact ik_emptySlot' _ _ | exact ik_capSwapForDelete _ _
  | (refine ik_capInsert_nonUt _ ?_ _ _; nu_side))

macro "ui0_auto" : tactic => `(tactic| repeat' (first | ui0_leaf | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## The VSpace map performs -/

macro "ui_mapfail" : tactic => `(tactic| (
  apply ik_of_empty
  intro s
  repeat' (first | exact nd_fail_bind _ | (apply nd_bind_empty; intro _ _) | (dsimp only) | split)))

theorem ui_performPageTableInvocation (iv : PageTableInvocation) :
    IK UtInv' (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap ctSlot pde pdSlot vspace =>
    by_cases hc : NNU cap
    · simp only [performPageTableInvocation]; ui0_auto
    · rcases not_nnu hc with rfl | ⟨d, b, n, f, rfl⟩ <;> (simp only [performPageTableInvocation]; ui_mapfail)
  | pageTableUnmap cap ctSlot => unfold performPageTableInvocation; ui0_auto

theorem ui_performPageDirectoryInvocation (iv : PageDirectoryInvocation) :
    IK UtInv' (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap ctSlot pdpte pdptSlot vspace =>
    by_cases hc : NNU cap
    · simp only [performPageDirectoryInvocation]; ui0_auto
    · rcases not_nnu hc with rfl | ⟨d, b, n, f, rfl⟩ <;> (simp only [performPageDirectoryInvocation]; ui_mapfail)
  | pageDirectoryUnmap cap ctSlot => unfold performPageDirectoryInvocation; ui0_auto

theorem ui_performPdptInvocation (iv : PdptInvocation) :
    IK UtInv' (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap ctSlot pml4e pml4Slot vspace =>
    by_cases hc : NNU cap
    · simp only [performPdptInvocation]; ui0_auto
    · rcases not_nnu hc with rfl | ⟨d, b, n, f, rfl⟩ <;> (simp only [performPdptInvocation]; ui_mapfail)
  | pdptUnmap cap ctSlot => unfold performPdptInvocation; ui0_auto

theorem ui_performPageInvocation (iv : PageInvocation) :
    IK UtInv' (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap ctSlot entries vspace =>
    by_cases hc : NNU cap
    · simp only [performPageInvocation]; ui0_auto
    · rcases not_nnu hc with rfl | ⟨d, b, n, f, rfl⟩ <;> (simp only [performPageInvocation]; ui_mapfail)
  | _ => unfold performPageInvocation; ui0_auto

/-! ## The TCB installs -/

theorem ik_checkCapAt_ins (c : Cap) (src : CslotPtr) (t : Cap) (sl dest : CslotPtr) :
    IK UtInv' (checkCapAt (Z := Unit) c src (checkCapAt t sl (capInsert c src dest))) := by
  by_cases hu : ∃ d b n f, c = .untypedCap d b n f
  · obtain ⟨d, b, n, f, rfl⟩ := hu
    unfold checkCapAt
    refine ik_bind (ik_utInv'_of_uk fun _ => uk_getCap _) fun c' => ?_
    unfold NonDet.when
    rw [if_neg (by simp [sameObjectAs])]
    exact ik_pure' _
  · have hnu : ∀ d b n f, c ≠ .untypedCap d b n f := fun d b n f e => hu ⟨d, b, n, f, e⟩
    unfold checkCapAt
    refine ik_bind (ik_utInv'_of_uk fun _ => uk_getCap _) fun c' => ik_when _ ?_
    refine ik_bind (ik_utInv'_of_uk fun _ => uk_getCap _) fun c'' => ik_when _ ?_
    exact ik_capInsert_nonUt c hnu src dest

/-! ## `finalise_cap`'s remainder -/

/-- Every outcome's value satisfies `Q`. -/
def OV {α : Type} (Q : α → Prop) (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → Q x.1

section OVc
variable {α β : Type} {Q : β → Prop}

theorem ov_bind {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (h : ∀ a, OV Q (g a)) :
    OV Q (m >>= g) := by
  rintro σ x ⟨y, -, hx⟩; exact h y.1 y.2 x hx

theorem ov_bind' {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (h : ∀ a, OV Q (g a)) :
    OV Q (NonDet.bind m g) := ov_bind h

theorem ov_pure {b : β} (h : Q b) : OV Q (pure b : NonDet (State Unit) β) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact h

theorem ov_pure' {b : β} (h : Q b) : OV Q (NonDet.pure b : NonDet (State Unit) β) := ov_pure h

theorem ov_liftM {f : α → β} {m : NonDet (State Unit) α} (h : ∀ a, Q (f a)) : OV Q (NonDet.liftM f m) :=
  ov_bind' fun a => ov_pure' (h a)

theorem ov_fail : OV Q (NonDet.fail : NonDet (State Unit) β) := fun _ _ hx => hx.elim

theorem ov_ite {c : Prop} [Decidable c] {m1 m2 : NonDet (State Unit) β} (h1 : OV Q m1) (h2 : OV Q m2) :
    OV Q (if c then m1 else m2) := by
  split <;> assumption

end OVc

/-- The remainder is not untyped. -/
def RemNU (p : Cap × Cap) : Prop := ∀ d b n f, p.1 ≠ .untypedCap d b n f

macro "ov_auto" : tactic => `(tactic| repeat' (first
  | (refine ov_bind fun _ => ?_) | (refine ov_bind' fun _ => ?_)
  | (refine ov_liftM fun _ => ?_)
  | exact ov_fail
  | (refine ov_pure ?_) | (refine ov_pure' ?_)
  | (refine ov_ite ?_ ?_)
  | (show RemNU _; intro _ _ _ _ h; first | cases h | (split at h <;> cases h))
  | split))

theorem finaliseCap_nu (c : Cap) (fin : Bool) : OV RemNU (finaliseCap (Z := Unit) c fin) := by
  cases c <;> simp only [finaliseCap, archFinaliseCap] <;> ov_auto

/-! ## The IPC cap transfer -/

theorem uk_mem {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) : uV x.2 = uV σ := h (uV σ) σ rfl x hx

theorem utInv'_of_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hI : UtInv' σ) : UtInv' σ' := by
  show UtInv'V (uV σ'); rw [h]; exact hI

theorem capAt_of_view {σ σ' : State Unit} (h : uV σ' = uV σ) : capAt σ' = capAt σ :=
  congrArg (fun w : UView => w.2.1) h

theorem getReceiveSlots_len (t : ObjRef) (b : Option ObjRef) : OV (fun l : List CslotPtr => l.length ≤ 1)
    (getReceiveSlots (Z := Unit) t b) := by
  cases b with
  | none => unfold getReceiveSlots; exact ov_pure (by simp)
  | some buf =>
    unfold getReceiveSlots
    refine ov_bind fun ct => ?_
    intro σ x hx
    unfold emptyOnFailure NonDetE.catch at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨r, s⟩ := z
    cases r with
    | error e => rw [Set.mem_singleton_iff.1 hx]; simp
    | ok l =>
      rw [Set.mem_singleton_iff.1 hx]
      have key : OkV (uV σ) (fun l : List CslotPtr => l.length ≤ 1) (do
          let cnode ← unifyFailure (Z := Unit) (lookupCap t ct.ctReceiveRoot)
          let slot ← unifyFailure (Z := Unit) (lookupTargetSlot cnode ct.ctReceiveIndex (unat ct.ctReceiveDepth))
          let cap ← NonDetE.liftE (getCap (Z := Unit) slot)
          NonDetE.whenE (cap ≠ .nullCap) (NonDetE.throwError ())
          NonDetE.returnOk [slot]) := by
        refine okv_bind_uk (fun _ => by uk_auto) fun _ => okv_bind_uk (fun _ => by uk_auto) fun _ =>
          okv_liftE_getCap_bind fun _ _ => okv_whenE_bind fun _ => okv_returnOk (by simp)
      exact key σ rfl l s hz

/-- **The transfer loop keeps `UtInv'`** while every remaining extra cap is in
its slot (needed only while a receive slot is left; there is at most one). -/
theorem ui_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (caps : List (Cap × CslotPtr)) (n : Nat) (slots : List CslotPtr) (mi : MessageInfo) (σ : State Unit),
      UtInv' σ → slots.length ≤ 1 → (slots ≠ [] → ∀ p ∈ caps, capAt σ p.2 = some p.1) →
      ∀ y ∈ (transferCapsLoop (Z := Unit) ep rb n caps slots mi σ).1, UtInv' y.2
  | [], n, slots, mi, σ, hI, _, _, y, hy => by
    unfold transferCapsLoop at hy; rw [Set.mem_singleton_iff.1 hy]; exact hI
  | (cap, slot) :: more, n, slots, mi, σ, hI, hl, hc, y, hy => by
    have ih := ui_transferCapsLoop ep rb more (n + 1)
    unfold transferCapsLoop constOnFailure NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hyz : y.2 = z.2 := by
      obtain ⟨r, s⟩ := z
      cases r <;> (rw [Set.mem_singleton_iff.1 hy])
    rw [hyz]
    clear hy hyz
    replace hz := run_returnOk_bind_mem hz
    try dsimp only at hz
    split at hz
    · obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
      have hv := uk_mem (fun _ => uk_setExtraBadge _ _ _) hx
      obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
      refine ih slots _ x.2 (utInv'_of_view hv hI) hl (fun hne p hp => ?_) w hw
      rw [capAt_of_view hv]; exact hc hne p (List.mem_cons.2 (Or.inr hp))
    · split at hz
      · rename_i hne
        obtain ⟨z0, hz0, ⟨c', hc', hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
        · obtain ⟨r0, s0⟩ := z0
          simp only at hc'; subst hc'
          have hv0 : uV s0 = uV σ := uk_deriveCap slot cap σ rfl _ hz0
          have hd := okv_deriveCap slot cap σ rfl c' s0 hz0
          obtain ⟨z1, hz1, ⟨u, hu, hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
          · have hs1 : z1.2 = s0 := by
              unfold NonDetE.whenE at hz1
              split at hz1 <;> (rw [Set.mem_singleton_iff.1 hz1])
            obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
            rw [hs1] at hx
            have hI0 := utInv'_of_view hv0 hI
            have hok : CIOK (uV s0) c' slot := by
              intro d b n f e
              have e0 := (hd.1 d b n f).2 e
              have hcs := hc hne (cap, slot) (List.mem_cons.2 (Or.inl rfl))
              refine ⟨?_, ?_⟩
              · show capAt s0 slot = _
                rw [capAt_of_view hv0, (hd.1 d b n f).1 e0]; exact hcs
              · have := hd.2 d b n f e
                intro x hx; rw [hv0] at hx; exact this x hx
            have hIx := hv_capInsert c' slot (the slots.head?) s0 ⟨hI0, hok⟩ x hx
            obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
            have htl : slots.tail = [] := by
              cases slots with
              | nil => rfl
              | cons a t => simp only [List.length_cons] at hl; simp only [List.tail_cons]; exact List.eq_nil_of_length_eq_zero (by omega)
            refine ih slots.tail _ x.2 hIx (by rw [htl]; simp) (fun h => absurd htl h) w hw
          · have hs1 : z1.2 = s0 := by
              unfold NonDetE.whenE at hz1
              split at hz1 <;> (rw [Set.mem_singleton_iff.1 hz1])
            show UtInv' z1.2
            rw [hs1]; exact utInv'_of_view hv0 hI
        · exact utInv'_of_view (uk_deriveCap slot cap σ rfl _ hz0) hI
      · rw [Set.mem_singleton_iff.1 hz]; exact hI

theorem ui_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (recv : ObjRef)
    (rbuf : Option ObjRef) (σ : State Unit) (hI : UtInv' σ) (hc : ∀ p ∈ caps, capAt σ p.2 = some p.1) :
    ∀ y ∈ (transferCaps (Z := Unit) info caps ep recv rbuf σ).1, UtInv' y.2 := by
  intro y hy
  unfold transferCaps at hy
  obtain ⟨x, hx, hy⟩ := hy
  have hv := uk_mem (fun _ => uk_getReceiveSlots _ _) hx
  have hlen := getReceiveSlots_len recv rbuf σ x hx
  obtain ⟨x2, hx2, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx2
  dsimp only at hy
  cases rbuf with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact utInv'_of_view hv hI
  | some b =>
    exact ui_transferCapsLoop ep b caps 0 x.1 _ x.2 (utInv'_of_view hv hI) hlen
      (fun _ p hp => by rw [capAt_of_view hv]; exact hc p hp) y hy

/-- **The normal IPC transfer keeps `UtInv'`.** -/
theorem ui_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (recv : ObjRef) (rbuf : Option ObjRef) :
    IK UtInv' (doNormalTransfer (Z := Unit) sender sbuf ep badge grant recv rbuf) := by
  intro σ hI y hy
  unfold doNormalTransfer at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  have hv1 := uk_mem (fun _ => uk_getMessageInfo _) hx1
  have hI1 : UtInv' x1.2 := utInv'_of_view hv1 hI
  have tail : ∀ (caps : List (Cap × CslotPtr)) (s : State Unit), UtInv' s → (∀ p ∈ caps, capAt s p.2 = some p.1) →
      ∀ y ∈ ((do
        let mrsTransferred ← copyMrs (Z := Unit) sender sbuf recv rbuf x1.1.miLength
        let mi' ← transferCaps x1.1 caps ep recv rbuf
        setMessageInfo recv { miLength := mrsTransferred, miExtraCaps := mi'.miExtraCaps, miCapsUnwrapped := mi'.miCapsUnwrapped, miLabel := x1.1.miLabel }
        asUser recv (setRegister badge_register badge)) s).1, UtInv' y.2 := by
    intro caps s hs hc y hy
    obtain ⟨x3, hx3, hy⟩ := hy
    have hv3 := uk_mem (fun _ => uk_copyMrs _ _ _ _ _) hx3
    obtain ⟨x4, hx4, hy⟩ := hy
    have hI4 := ui_transferCaps _ _ _ _ _ x3.2 (utInv'_of_view hv3 hs)
      (fun p hp => by rw [capAt_of_view hv3]; exact hc p hp) x4 hx4
    exact (ik_utInv'_of_uk fun _ => by uk_auto) x4.2 hI4 y hy
  simp only at hy
  split at hy
  · obtain ⟨x2, hx2, hy⟩ := hy
    unfold NonDetE.catch at hx2
    obtain ⟨z, hz, hx2⟩ := hx2
    have hvz : uV z.2 = uV x1.2 := uk_lookupExtraCaps _ _ _ x1.2 rfl z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      exact tail [] s (utInv'_of_view hvz hI1) (fun p hp => absurd hp List.not_mem_nil) y hy
    | ok l =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      refine tail l s (utInv'_of_view hvz hI1) (fun p hp => ?_) y hy
      have := okv_lookupExtraCaps sender sbuf x1.1 x1.2 rfl l s hz p hp
      rw [capAt_of_view hvz]; exact this
  · obtain ⟨x2, hx2, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hx2
    exact tail [] x1.2 hI1 (fun p hp => absurd hp List.not_mem_nil) y hy

/-- A bind whose first step's `.ok` values satisfy `Q`. -/
theorem ike_bind_v {P : State Unit → Prop} {ε α γ : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε γ} {Q : α → Prop} (hm : IKE P m)
    (hv : ∀ σ x, x ∈ (m.run σ).1 → ∀ a, x.1 = .ok a → Q a) (hg : ∀ a, Q a → IKE P (g a)) : IKE P (m >>= g) := by
  unfold IKE; rw [ExceptT.run_bind]
  intro σ hσ y ⟨x, hx, hy⟩
  obtain ⟨r, s⟩ := x
  cases r with
  | ok a => exact hg a (hv σ _ hx a rfl) s (hm σ hσ _ hx) y hy
  | error e => rw [Set.mem_singleton_iff.1 hy]; exact hm σ hσ _ hx

end

end Fl4Proofs.P3.SInvU
