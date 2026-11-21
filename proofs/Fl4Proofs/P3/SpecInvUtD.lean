/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut3): **the decode's facts
for `UtInv'`, carried to the perform** (spec side only; imports only Fl4Spec
via SpecInvUtMp).

Every decode function keeps the view `uV` (the generated `UK` frames), so a
fact checked by the decode on the view at its start holds at its end and,
across `set_thread_state Restart` (also `UK`), at the perform.
* `OkV w P m`: every `.ok` outcome of `m` from a state of view `w` satisfies
  `P` (combinators over `UK` steps; leaves `get_cap`, `ensure_empty`,
  `ensure_no_children`, `derive_cap`, `lookup_cap_and_slot`,
  `lookup_extra_caps`).
* `InvOKV w inv`: what the perform of `inv` needs, read on the view: an untyped
  retype `UtRetOK ∧ DestNull` (ut1/ut2's), CNode insert `CIOK`, move / rotate
  the `CapRel` facts and the null destination, AsidControl MakePool `MpOK`, the
  IRQ handler's notification cap not untyped. `okv_fl4Decode`: every `.ok`
  decode outcome satisfies it, given that the invoked slot holds the invoked
  cap and every extra cap is in its slot (the shell's lookups).
-/
import Fl4Proofs.P3.SpecInvUtMp
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `OkV` -/

/-- Every `.ok` outcome of `m` from a state of view `w` satisfies `P`. -/
def OkV {ε α : Type} (w : UView) (P : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, uV σ = w → ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → P a

theorem mem_bindE' {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem mem_liftE' {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

section OkVc
variable {ε α β : Type} {w : UView}

theorem okv_bind {P : β → Prop} {Q : α → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hq : OkV w Q m) (hg : ∀ a, Q a → OkV w P (g a)) : OkV w P (m >>= g) := by
  intro σ hσ b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hb
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have hv : uV s' = w := by rw [← hσ]; exact hm (uV σ) σ rfl _ hz
    exact hg a (hq σ hσ a s' hz) s' hv b s hy
  · simp at he

theorem okv_triv {P : α → Prop} {m : NonDetE (State Unit) ε α} (h : ∀ a, P a) : OkV w P m :=
  fun _ _ a _ _ => h a

theorem okv_mono {P Q : α → Prop} {m : NonDetE (State Unit) ε α} (h : OkV w Q m) (hq : ∀ a, Q a → P a) :
    OkV w P m := fun σ hσ a s hs => hq a (h σ hσ a s hs)

theorem okv_bind_uk {P : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hg : ∀ a, OkV w P (g a)) : OkV w P (m >>= g) :=
  okv_bind (Q := fun _ => True) hm (okv_triv fun _ => trivial) fun a _ => hg a

theorem okv_returnOk {P : α → Prop} {a : α} (h : P a) : OkV w P (NonDetE.returnOk a : NonDetE (State Unit) ε α) := by
  intro σ _ b s hb
  have e := Set.mem_singleton_iff.1 hb
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, -⟩ := e; exact h

theorem okv_pure {P : α → Prop} {a : α} (h : P a) : OkV w P (pure a : NonDetE (State Unit) ε α) := okv_returnOk h

theorem okv_throw {P : α → Prop} (e : ε) : OkV w P (NonDetE.throwError e : NonDetE (State Unit) ε α) := by
  intro σ _ b s hb
  have e := Set.mem_singleton_iff.1 hb; simp at e

theorem okv_throw' {P : α → Prop} (e : ε) : OkV w P (throw e : NonDetE (State Unit) ε α) := okv_throw e

theorem okv_throw_bind {P : β → Prop} (e : ε) {g : α → NonDetE (State Unit) ε β} :
    OkV w P (NonDetE.throwError e >>= g) := by
  intro σ _ b s hb
  rw [ExceptT.run_bind] at hb
  obtain ⟨z, hz, hb⟩ := hb
  obtain rfl := Set.mem_singleton_iff.1 hz
  have e := Set.mem_singleton_iff.1 hb; simp at e

theorem okv_liftE_fail {P : α → Prop} : OkV w P (NonDetE.liftE (ε := ε) (NonDet.fail : NonDet (State Unit) α)) := by
  intro σ _ b s hb
  obtain ⟨x, hx, -⟩ := mem_liftE' hb
  exact hx.elim

theorem okv_returnOk_bind {P : β → Prop} {a : α} {g : α → NonDetE (State Unit) ε β} (h : OkV w P (g a)) :
    OkV w P (NonDetE.returnOk a >>= g) := by
  intro σ hσ b s hb
  rw [ExceptT.run_bind] at hb
  obtain ⟨z, hz, hb⟩ := hb
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact h σ hσ b s hb

theorem okv_pure_bind {P : β → Prop} {a : α} {g : α → NonDetE (State Unit) ε β} (h : OkV w P (g a)) :
    OkV w P ((pure a : NonDetE (State Unit) ε α) >>= g) := okv_returnOk_bind h

theorem okv_whenE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (hg : ¬ c → OkV w P (g ())) : OkV w P (NonDetE.whenE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.whenE
  by_cases hc : c
  · rw [if_pos hc]
    intro σ _ b s hb
    rw [ExceptT.run_bind] at hb
    obtain ⟨z, hz, hb⟩ := hb
    obtain rfl := Set.mem_singleton_iff.1 hz
    have e := Set.mem_singleton_iff.1 hb; simp at e
  · rw [if_neg hc]; exact okv_pure_bind (hg hc)

theorem okv_unlessE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (hg : c → OkV w P (g ())) : OkV w P (NonDetE.unlessE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.unlessE
  by_cases hc : c
  · rw [if_pos hc]; exact okv_pure_bind (hg hc)
  · rw [if_neg hc]
    intro σ _ b s hb
    rw [ExceptT.run_bind] at hb
    obtain ⟨z, hz, hb⟩ := hb
    obtain rfl := Set.mem_singleton_iff.1 hz
    have e := Set.mem_singleton_iff.1 hb; simp at e

theorem okv_whenE {c : Prop} [Decidable c] {e : ε} (P : Unit → Prop) (hg : ¬ c → P ()) :
    OkV w P (NonDetE.whenE c (NonDetE.throwError e)) := by
  unfold NonDetE.whenE
  by_cases hc : c
  · rw [if_pos hc]; exact okv_throw e
  · rw [if_neg hc]; exact okv_pure (hg hc)

theorem okv_ite {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE (State Unit) ε α} (h1 : OkV w P m1)
    (h2 : OkV w P m2) : OkV w P (if c then m1 else m2) := by
  split <;> assumption

theorem okv_liftME {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α} (h : OkV w (fun a => P (f a)) m) :
    OkV w P (NonDetE.liftME f m) := by
  unfold NonDetE.liftME
  intro σ hσ b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hb
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have e := Set.mem_singleton_iff.1 hy
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h σ hσ _ _ hz
  · simp at he

theorem okv_liftE_bind {P : β → Prop} {Q : α → Prop} {m : NonDet (State Unit) α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UK v m) (hq : ∀ σ, uV σ = w → ∀ x ∈ (m σ).1, Q x.1) (hg : ∀ a, Q a → OkV w P (g a)) :
    OkV w P (NonDetE.liftE m >>= g) := by
  refine okv_bind (Q := Q) (fun v => ike_liftE (hm v)) ?_ hg
  intro σ hσ a s hs
  obtain ⟨x, hx, e⟩ := mem_liftE' hs
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact hq σ hσ x hx

theorem okv_liftE_getCap_bind {P : β → Prop} {sl : CslotPtr} {g : Cap → NonDetE (State Unit) ε β}
    (hg : ∀ c, w.2.1 sl = some c → OkV w P (g c)) : OkV w P (NonDetE.liftE (getCap (Z := Unit) sl) >>= g) :=
  okv_liftE_bind (fun _ => uk_getCap sl) (fun σ hσ x hx => by
    rw [← hσ]; exact (getCap_capAt hx).2) hg

end OkVc

/-! ## Leaves -/

theorem okv_ensureEmpty {w : UView} (sl : CslotPtr) :
    OkV w (fun _ => w.2.1 sl = some .nullCap) (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty
  refine okv_liftE_getCap_bind fun c hc => okv_whenE _ fun hn => ?_
  rw [hc, not_not.1 hn]

theorem okv_ensureNoChildren {w : UView} (sl : CslotPtr) :
    OkV w (fun _ => ∀ c, w.2.2.1 c ≠ some sl) (ensureNoChildren (Z := Unit) sl) := by
  unfold ensureNoChildren
  refine okv_liftE_bind (Q := fun t => t = w.2.2.1) (fun _ => ik_gets _) (fun σ hσ x hx => ?_) fun t ht => ?_
  · obtain rfl := Set.mem_singleton_iff.1 hx; rw [← hσ]; rfl
  · subst ht
    exact okv_whenE _ fun hn c hc => hn ⟨c, hc⟩

theorem okv_mapMEx_ensureEmpty {w : UView} :
    ∀ slots : List CslotPtr, OkV w (fun _ => ∀ d ∈ slots, w.2.1 d = some .nullCap)
      (NonDetE.mapMEx (ensureEmpty (Z := Unit)) slots)
  | [] => by unfold NonDetE.mapMEx; exact okv_pure fun d hd => absurd hd (List.not_mem_nil)
  | a :: as => by
    unfold NonDetE.mapMEx
    refine okv_bind (fun _ => uk_ensureEmpty a) (okv_ensureEmpty a) fun _ ha => ?_
    refine okv_mono (okv_mapMEx_ensureEmpty as) fun _ h d hd => ?_
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ha
    · exact h d hd

/-- `const_on_failure False (ensure_no_children; return True)` returns `True`
only if the slot has no CDT child. -/
theorem okv_reset_bind {β : Type} {ε : Type} {w : UView} {sl : CslotPtr} {P : β → Prop}
    {g : Bool → NonDetE (State Unit) ε β}
    (hg : ∀ r, (r = true → ∀ c, w.2.2.1 c ≠ some sl) → OkV w P (g r)) :
    OkV w P (NonDetE.liftE (constOnFailure (Z := Unit) false
      (ensureNoChildren (Z := Unit) sl >>= fun _ => NonDetE.returnOk true)) >>= g) := by
  refine okv_liftE_bind (fun _ => uk_constOnFailure _ _ (fun σ hσ x hx => by
      obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hx
      · obtain ⟨r, s'⟩ := z; simp only at ha; subst ha
        have e := Set.mem_singleton_iff.1 hy; rw [e]; exact uk_ensureNoChildren sl σ hσ _ hz
      · rw [he]; exact uk_ensureNoChildren sl σ hσ _ hz)) (fun σ hσ x hx => ?_) hg
  intro hr
  unfold constOnFailure NonDetE.catch at hx
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨r, s'⟩ := z
  cases r with
  | error e => obtain rfl := Set.mem_singleton_iff.1 hx; cases hr
  | ok a =>
    have hok := (okv_bind (P := fun _ => ∀ c, w.2.2.1 c ≠ some sl) (fun _ => uk_ensureNoChildren sl)
      (okv_ensureNoChildren sl) fun _ h => okv_returnOk h) σ hσ a s' hz
    exact hok

/-! ## The decode's cap transformations keep untyped caps and make none -/

/-- `c` is `c0` if either is untyped. -/
def UtKeep (c0 c : Cap) : Prop :=
  ∀ d b n f, (c0 = .untypedCap d b n f → c = c0) ∧ (c = .untypedCap d b n f → c0 = .untypedCap d b n f)

theorem utKeep_refl (c : Cap) : UtKeep c c := fun _ _ _ _ => ⟨fun _ => rfl, id⟩

theorem utKeep_trans {c0 c1 c2 : Cap} (h1 : UtKeep c0 c1) (h2 : UtKeep c1 c2) : UtKeep c0 c2 := by
  intro d b n f
  refine ⟨fun e => ?_, fun e => (h1 d b n f).2 ((h2 d b n f).2 e)⟩
  have e1 := (h1 d b n f).1 e
  rw [(h2 d b n f).1 (e1.trans e), e1]

theorem utKeep_nonUt {c0 c : Cap} (h0 : ∀ d b n f, c0 ≠ .untypedCap d b n f)
    (h : ∀ d b n f, c ≠ .untypedCap d b n f) : UtKeep c0 c :=
  fun d b n f => ⟨fun e => absurd e (h0 d b n f), fun e => absurd e (h d b n f)⟩

theorem utKeep_mask (r : CapRights) (c : Cap) : UtKeep c (maskCap r c) := by
  intro d b n f
  cases c <;> simp [maskCap, capRightsUpdate]

theorem utKeep_upd (p : Bool) (x : Data) (c : Cap) : UtKeep c (updateCapData p x c) := by
  intro d b n f
  constructor
  · intro e; subst e; simp [updateCapData, isEpCap, isNtfnCap, isCnodeCap, isArchCap]
  · intro e
    unfold updateCapData at e
    split_ifs at e <;> first
      | (cases c <;> simp_all [badgeUpdate, isEpCap, isNtfnCap]; done)
      | (cases c <;> simp_all [archUpdateCapData, isArchCap]; done)
      | (cases c <;> simp_all [isEpCap, isNtfnCap, isCnodeCap, isArchCap]; done)
      | (simp only at e; split at e <;> simp_all)

theorem capRel_of_keep {c0 c : Cap} (h0 : c0 ≠ .nullCap) (h1 : c ≠ .nullCap) (hk : UtKeep c0 c) : CapRel c0 c := by
  refine ⟨h0, h1, ?_⟩
  by_cases hu : ∃ d b n f, c0 = .untypedCap d b n f
  · obtain ⟨d, b, n, f, e⟩ := hu; exact Or.inl ((hk d b n f).1 e)
  · refine Or.inr ⟨fun d b n f e => hu ⟨d, b, n, f, (hk d b n f).2 e⟩, fun d b n f e => hu ⟨d, b, n, f, e⟩⟩

theorem okv_archDeriveCap {w : UView} (c : ArchCap) :
    OkV w (fun c' => ∀ d b n f, c' ≠ .untypedCap d b n f) (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap
  split <;> first | exact okv_throw _ | exact okv_returnOk (fun _ _ _ _ h => by cases h) | (refine okv_returnOk ?_; intro _ _ _ _ h; cases h)

/-- **`derive_cap`**: the derived cap is untyped only as the source's own
untyped cap, after `ensure_no_children`. -/
theorem okv_deriveCap {w : UView} (sl : CslotPtr) (c : Cap) :
    OkV w (fun c' => UtKeep c c' ∧ ∀ d b n f, c' = .untypedCap d b n f → ∀ x, w.2.2.1 x ≠ some sl)
      (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap
  split
  · refine okv_mono (okv_archDeriveCap _) fun c' h => ⟨utKeep_nonUt (fun _ _ _ _ e => by cases e) h,
      fun d b n f e => absurd e (h d b n f)⟩
  · refine okv_bind (fun _ => uk_ensureNoChildren sl) (okv_ensureNoChildren sl) fun _ hk => okv_returnOk ?_
    exact ⟨utKeep_refl _, fun _ _ _ _ _ => hk⟩
  · exact okv_returnOk ⟨utKeep_nonUt (fun _ _ _ _ e => by cases e) (fun _ _ _ _ e => by cases e),
      fun _ _ _ _ e => by cases e⟩
  · exact okv_returnOk ⟨utKeep_nonUt (fun _ _ _ _ e => by cases e) (fun _ _ _ _ e => by cases e),
      fun _ _ _ _ e => by cases e⟩
  · rename_i h1 h2 h3 h4
    exact okv_returnOk ⟨utKeep_refl _, fun d b n f e => absurd e (h2 d b n f)⟩

theorem okv_lookupCapAndSlot {w : UView} (t : ObjRef) (cp : CapRef) :
    OkV w (fun p => w.2.1 p.2 = some p.1) (lookupCapAndSlot (Z := Unit) t cp) := by
  unfold lookupCapAndSlot
  refine okv_bind_uk (fun _ => uk_lookupSlotForThread _ _) fun x => ?_
  obtain ⟨sl, cr⟩ := x
  exact okv_liftE_getCap_bind fun c hc => okv_returnOk hc

theorem okv_capFaultOnFailure {w : UView} {α : Type} {P : α → Prop} (cp : ObjRef) (rp : Bool)
    {m : LFMonad Unit α} (h : OkV w P m) : OkV w P (capFaultOnFailure (Z := Unit) cp rp m) := by
  intro σ hσ a s hs
  unfold capFaultOnFailure NonDetE.handleE at hs
  rw [ExceptT.run_mk] at hs
  obtain ⟨z, hz, hs⟩ := hs
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok b =>
    have e := Set.mem_singleton_iff.1 hs
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h σ hσ _ _ hz
  | error e =>
    have e' := Set.mem_singleton_iff.1 hs; simp at e'

theorem okv_lookupExtraCaps {w : UView} (t : ObjRef) (buf : Option Data) (mi : MessageInfo) :
    OkV w (fun l => ∀ p ∈ l, w.2.1 p.2 = some p.1) (lookupExtraCaps (Z := Unit) t buf mi) := by
  unfold lookupExtraCaps
  refine okv_liftE_bind (fun _ => uk_getExtraCptrs _ _) (Q := fun _ => True) (fun _ _ _ _ => trivial) fun cps _ => ?_
  induction cps with
  | nil => unfold NonDetE.mapME; exact okv_pure fun p hp => absurd hp List.not_mem_nil
  | cons a as ih =>
    unfold NonDetE.mapME
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun p hp => ?_
    refine okv_bind (fun _ => ike_mapME (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _)) _)
      ih fun ps hps => okv_pure ?_
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hp
    · exact hps q hq

/-! ## What the perform needs -/

/-- `UtRetOK` on the view. -/
def UtRetOKV (w : UView) : UntypedInvocation → Prop
  | .retype srcSlot reset base rb ty sz slots dev =>
    ∃ bits fi, w.2.1 srcSlot = some (.untypedCap dev base bits fi) ∧
      fl4ObjBitsApi ty sz ≤ untypedMaxBits ∧ 1 ≤ slots.length ∧
      rb = alignUp (getFreeRef base (if reset then 0 else fi)) (fl4ObjBitsApi ty sz) ∧
      slots.length ≤ ((objSize (.untypedCap dev base bits fi) -
        BitVec.ofNat 64 (if reset then 0 else fi)) >>> fl4ObjBitsApi ty sz).toNat ∧
      (reset = true → ∀ c, w.2.2.1 c ≠ some srcSlot)

/-- `DestNull` on the view. -/
def DestNullV (w : UView) : UntypedInvocation → Prop
  | .retype _ _ _ _ _ _ slots _ => ∀ d ∈ slots, w.2.1 d = some .nullCap

theorem utRetOK_of_V {σ : State Unit} {ui : UntypedInvocation} (h : UtRetOKV (uV σ) ui) : UtRetOK σ ui := by
  cases ui; exact h

theorem destNull_of_V {σ : State Unit} {ui : UntypedInvocation} (h : DestNullV (uV σ) ui) : DestNull σ ui := by
  cases ui; exact h

/-- What CNode Copy/Mint, Move/Mutate and Rotate need. -/
def CnOKV (w : UView) : CnodeInvocation → Prop
  | .insertCall c src _dest => CIOK w c src
  | .moveCall c src dest => ∃ c0, w.2.1 src = some c0 ∧ w.2.1 dest = some .nullCap ∧ CapRel c0 c ∧ src ≠ dest
  | .rotateCall c1 c2 s1 s2 s3 => ∃ c1' c2', w.2.1 s1 = some c1' ∧ w.2.1 s2 = some c2' ∧ CapRel c1' c1 ∧
      CapRel c2' c2 ∧ s2 ≠ s1 ∧ s2 ≠ s3 ∧ (s1 ≠ s3 → w.2.1 s3 = some .nullCap)
  | _ => True

/-- `MpOK` on the view. -/
def MpOKV (w : UView) : AsidControlInvocation → Prop
  | .makePool frame _slot parent _base =>
    ∃ dev fi, w.2.1 parent = some (.untypedCap dev frame page_bits fi) ∧ ∀ c, w.2.2.1 c ≠ some parent

theorem mpOK_of_V {σ : State Unit} {a : AsidControlInvocation} (h : MpOKV (uV σ) a) : MpOK σ a := by
  cases a; exact h

def ArchOKV (w : UView) : Fl4ArchInvocation → Prop
  | .spec (.invokeASIDControl a) => MpOKV w a
  | _ => True

def IrqHOKV : IrqHandlerInvocation → Prop
  | .setIRQHandler _ c _ => ∀ d b n f, c ≠ .untypedCap d b n f
  | _ => True

/-- **What the perform of an invocation needs from its decode** (on the view). -/
def InvOKV (w : UView) : Fl4Invocation → Prop
  | .invokeUntyped ui => UtRetOKV w ui ∧ DestNullV w ui
  | .invokeCNode ci => CnOKV w ci
  | .invokeArchObject ai => ArchOKV w ai
  | .invokeIRQHandler i => IrqHOKV i
  | _ => True

/-! ## The decodes -/

macro "okv_step" : tactic => `(tactic| first
  | exact okv_throw _ | exact okv_throw' _ | exact okv_liftE_fail
  | (refine okv_returnOk_bind ?_) | (refine okv_pure_bind ?_)
  | (refine okv_whenE_bind fun _ => ?_) | (refine okv_unlessE_bind fun _ => ?_)
  | (refine okv_liftE_getCap_bind fun _ _ => ?_)
  | (refine okv_bind (fun _ => uk_ensureEmpty _) (okv_ensureEmpty _) fun _ _ => ?_)
  | (refine okv_bind (fun _ => uk_ensureNoChildren _) (okv_ensureNoChildren _) fun _ _ => ?_)
  | (refine okv_bind (fun _ => ike_mapMEx (fun _ => uk_ensureEmpty _) _) (okv_mapMEx_ensureEmpty _) fun _ _ => ?_)
  | (refine okv_reset_bind fun _ _ => ?_)
  | (dsimp only)
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_)
  | (refine okv_ite ?_ ?_))

set_option maxHeartbeats 4000000 in
/-- **The untyped decode's checks** (`UtRetOK ∧ DestNull`). -/
theorem okv_decodeUntyped {w : UView} (label : Data) (args : List Data) (slot : CslotPtr) {dev : Bool}
    {p : ObjRef} {n f : Nat} (ex : List Cap) (hc : w.2.1 slot = some (.untypedCap dev p n f)) :
    OkV w (fun ui => UtRetOKV w ui ∧ DestNullV w ui)
      (decodeUntypedInvocationWith (Z := Unit) fl4ObjBitsApi label args slot (.untypedCap dev p n f) ex) := by
  unfold decodeUntypedInvocationWith
  repeat' okv_step
  all_goals first
    | exact okv_throw _
    | (refine okv_returnOk ⟨⟨n, f, hc, ?_, ?_, rfl, ?_, ?_⟩, ?_⟩
       all_goals (simp only [freeIndexOf, unat, objRefOf, List.length_map, List.length_range'] at *)
       all_goals first | assumption | omega | (intro; assumption) | (simp_all; done) | skip)

set_option maxHeartbeats 4000000 in
/-- **The CNode decode's checks.** -/
theorem okv_decodeCnode {w : UView} (label : Data) (args : List Data) (cap : Cap) (ex : List Cap) :
    OkV w (CnOKV w) (decodeCnodeInvocation (Z := Unit) label args cap ex) := by
  unfold decodeCnodeInvocation
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind
    (okv_returnOk_bind (okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun destSlot => ?_)))
  refine okv_ite ?_ (okv_ite (okv_returnOk trivial) (okv_ite (okv_returnOk trivial) (okv_ite ?_ (okv_ite ?_ (okv_throw _)))))
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))
    refine okv_bind (fun _ => uk_ensureEmpty _) (okv_ensureEmpty _) fun _ hd => ?_
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun hnn => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun x => ?_
    obtain ⟨rights, capData, isMove⟩ := x
    dsimp only
    refine okv_returnOk_bind ?_
    have hk1 : UtKeep srcCap (match capData with
        | some x => updateCapData isMove x (maskCap rights srcCap)
        | none => maskCap rights srcCap) := by
      cases capData with
      | none => exact utKeep_mask _ _
      | some x => exact utKeep_trans (utKeep_mask _ _) (utKeep_upd _ _ _)
    cases isMove
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine okv_bind (fun _ => uk_deriveCap _ _) (okv_deriveCap _ _) fun nc hnc => okv_whenE_bind fun _ => okv_returnOk ?_
      intro d b n f e
      have hku := utKeep_trans hk1 hnc.1
      have e0 := (hku d b n f).2 e
      refine ⟨?_, hnc.2 d b n f e⟩
      rw [(hku d b n f).1 e0]; exact hsc
    · simp only [↓reduceIte]
      refine okv_returnOk_bind (okv_whenE_bind fun hnn2 => okv_returnOk ?_)
      refine ⟨srcCap, hsc, hd, capRel_of_keep hnn hnn2 hk1, ?_⟩
      intro e; subst e; rw [hd] at hsc; exact hnn (Option.some.inj hsc).symm
  · repeat' okv_step
    all_goals exact okv_returnOk trivial
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind
      (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))))))
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_bind_uk (fun _ => uk_lookupPivotSlot _ _ _) fun pivotSlot => ?_
    refine okv_whenE_bind fun hpv => ?_
    refine okv_bind (Q := fun _ => srcSlot ≠ destSlot → w.2.1 destSlot = some .nullCap) (fun _ => by uk_auto) ?_
      fun _ hd => ?_
    · unfold NonDetE.unlessE
      split
      · rename_i hc; exact okv_pure fun h => absurd hc h
      · exact okv_mono (okv_ensureEmpty _) fun _ h _ => h
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun hn1 => ?_
    refine okv_liftE_getCap_bind fun pivCap hpc => okv_whenE_bind fun hn2 => ?_
    refine okv_returnOk_bind (okv_returnOk_bind (okv_whenE_bind fun hn3 => okv_whenE_bind fun hn4 => okv_returnOk ?_))
    exact ⟨srcCap, pivCap, hsc, hpc, capRel_of_keep hn1 hn3 (utKeep_upd _ _ _),
      capRel_of_keep hn2 hn4 (utKeep_upd _ _ _), fun e => hpv (Or.inl e), fun e => hpv (Or.inr e), hd⟩

/-- **The IRQ handler decode**: SetIRQHandler's cap is a notification cap. -/
theorem okv_decodeIrqHandler {w : UView} (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) :
    OkV w IrqHOKV (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first | exact okv_throw _ | exact okv_returnOk trivial | split)
  all_goals (refine okv_returnOk ?_; intro d b n f e; subst e; simp_all [isNtfnCap])


end

end Fl4Proofs.P3.SInvU
