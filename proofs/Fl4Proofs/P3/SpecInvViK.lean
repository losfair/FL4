/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi3): **the decode's target facts**
for vi2's `ViGap` (spec side only; imports SpecInvViH and sb2's SpecInvSbX2 for the
frame-free outcome predicate `OkA`).

* `Held w c`: the cap `c` is in some slot of the view `w`.
* `TcbTg w i` / `ScTg w i` / **`TgOK w inv`**: the threads a TCB invocation suspends,
  reprioritises, rebinds or binds a notification to are named by a held thread cap; the
  SC a `threadControlSched` binds is named by a held SC cap; an SC invocation's SC (Bind,
  UnbindObject) is named by a held SC cap and a Bind's object cap is held.
  (l4v: `decode_tcb_invocation` / `decode_sched_context_invocation` work on the invoked
  cap and the extra caps, which `lookup_extra_caps` read from slots.)
* **`tg_fl4Decode`**: every `.ok` outcome of `fl4DecodeInvocation` from the invoked cap in
  its slot and extra caps in their slots satisfies `TgOK` (one lemma per decoder that
  builds a target; the others by the `tg_auto` traversal).
-/
import Fl4Proofs.P3.SpecInvViH
import Fl4Proofs.P3.SpecInvSbX2
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvB (OkA okA_bind okA_bindQ okA_triv okA_returnOk okA_throw okA_ite okA_liftME)

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The facts -/

/-- The cap `c` is held in some slot of `w`. -/
def Held (w : UView) (c : Cap) : Prop := ∃ s, w.2.1 s = some c

/-- The TCB invocation targets the perform needs to be non-idle / not the idle SC. -/
def TcbTg (w : UView) : TcbInvocation → Prop
  | .readRegisters s _ _ _ => Held w (.threadCap s)
  | .copyRegisters _ s _ _ _ _ _ => Held w (.threadCap s)
  | .threadControlSched t _ _ _ _ sc =>
      Held w (.threadCap t) ∧ ∀ c, sc = some (some c) → ∃ sz, Held w (.schedContextCap c sz)
  | .suspend t => Held w (.threadCap t)
  | .notificationControl t _ => Held w (.threadCap t)
  | _ => True

/-- The SC invocation facts. -/
def ScTg (w : UView) : SchedContextInvocation → Prop
  | .invokeSchedContextBind p c => (∃ sz, Held w (.schedContextCap p sz)) ∧ Held w c
  | .invokeSchedContextUnbindObject p _ => ∃ sz, Held w (.schedContextCap p sz)
  | _ => True

/-- **The decode's target facts.** -/
def TgOK (w : UView) : Fl4Invocation → Prop
  | .invokeTCB i => TcbTg w i
  | .invokeSchedContext i => ScTg w i
  | _ => True

/-! ## `OkA` steps keeping values -/

section OkAc
variable {ε α β : Type}

theorem okA_returnOk_bind {P : β → Prop} {a : α} {g : α → NonDetE (State Unit) ε β} (h : OkA P (g a)) :
    OkA P (NonDetE.returnOk a >>= g) := by
  intro σ c s hc
  rw [ExceptT.run_bind] at hc
  obtain ⟨z, hz, hc⟩ := hc
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact h σ c s hc

theorem okA_throw_bind {P : β → Prop} (e : ε) {g : α → NonDetE (State Unit) ε β} :
    OkA P (NonDetE.throwError e >>= g) := by
  intro σ c s hc
  rw [ExceptT.run_bind] at hc
  obtain ⟨z, hz, hc⟩ := hc
  obtain rfl := Set.mem_singleton_iff.1 hz
  have e := Set.mem_singleton_iff.1 hc; simp at e

theorem okA_whenE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (hg : ¬ c → OkA P (g ())) : OkA P (NonDetE.whenE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.whenE
  by_cases hc : c
  · rw [if_pos hc]; exact okA_throw_bind e
  · rw [if_neg hc]; exact okA_returnOk_bind (hg hc)

theorem okA_unlessE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (hg : c → OkA P (g ())) : OkA P (NonDetE.unlessE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.unlessE
  by_cases hc : c
  · rw [if_pos hc]; exact okA_returnOk_bind (hg hc)
  · rw [if_neg hc]; exact okA_throw_bind e

end OkAc

/-! ## Held caps -/

theorem held_of_mem {w : UView} {ex : List (Cap × CslotPtr)} (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1)
    {q : Cap × CslotPtr} (h : q ∈ ex) : Held w q.1 := ⟨q.2, hex q h⟩

theorem held_of_fst {w : UView} {ex : List (Cap × CslotPtr)} (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1)
    {c : Cap} (h : c ∈ ex.map Prod.fst) : Held w c := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
  exact held_of_mem hex hq

theorem held_head {w : UView} {ex : List (Cap × CslotPtr)} (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1)
    {c : Cap} {l : List Cap} (h : ex.map Prod.fst = c :: l) : Held w c :=
  held_of_fst hex (by rw [h]; exact List.mem_cons_self ..)

theorem the_mem {α : Type} [Nonempty α] {l : List α} {i : Nat} (h : i < l.length) : the l[i]? ∈ l := by
  rw [List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem the_head_mem {α : Type} [Nonempty α] {l : List α} (h : ¬ l.length = 0) : the l.head? ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self ..

/-! ## The traversal -/

macro "tg_close" : tactic => `(tactic| first
  | exact True.intro
  | assumption
  | (exact ⟨‹Held _ _›, fun _ h => Option.noConfusion h⟩)
  | (exact held_head (by assumption) (by assumption)))

/-- The decoder traversal: value-keeping steps only on their literal shapes (`with_reducible`),
the other binds drop their value. -/
macro "tg_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact okA_throw _)
  | (with_reducible exact okA_throw_bind _)
  | ((with_reducible refine okA_returnOk ?_); tg_close)
  | (with_reducible refine okA_returnOk_bind ?_)
  | (with_reducible refine okA_whenE_bind fun _ => ?_)
  | (with_reducible refine okA_unlessE_bind fun _ => ?_)
  | (dsimp only)
  | (refine okA_bind fun _ => ?_)
  | (refine okA_ite ?_ ?_)
  | (unfold rangeCheck)
  | split))

variable {w : UView}

/-- `decode_update_sc`'s new SC is the SC cap's. -/
theorem tgA_decodeUpdateSc (cap : Cap) (slot : CslotPtr) (scCap : Cap) :
    OkA (fun r : Option (Option ObjRef) => ∀ c, r = some (some c) → ∃ sz, scCap = .schedContextCap c sz)
      (decodeUpdateSc (Z := Unit) cap slot scCap) := by
  unfold decodeUpdateSc
  refine okA_returnOk_bind ?_
  refine okA_bind fun tcbSc => ?_
  (try dsimp only)
  cases scCap
  case nullCap =>
    refine okA_bind fun _ => okA_whenE_bind fun _ => okA_returnOk_bind (okA_returnOk ?_)
    intro c hc
    split_ifs at hc <;> cases hc
  case schedContextCap scp sz =>
    refine okA_returnOk_bind ?_
    refine okA_bind fun _ => okA_whenE_bind fun _ => okA_bind fun _ => okA_bind fun _ =>
      okA_whenE_bind fun _ => okA_returnOk_bind (okA_returnOk ?_)
    intro c hc
    split_ifs at hc
    simp only [Option.some.injEq] at hc
    subst hc
    exact ⟨sz, rfl⟩
  all_goals exact okA_throw_bind _

theorem tg_setSchedParams {p : ObjRef} (hp : Held w (.threadCap p)) {ex : List (Cap × CslotPtr)}
    (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) (args : List Data) (sl : CslotPtr) :
    OkA (TcbTg w) (decodeSetSchedParams (Z := Unit) args (.threadCap p) sl ex) := by
  unfold decodeSetSchedParams
  refine okA_whenE_bind fun _ => okA_whenE_bind fun h3 => ?_
  refine okA_returnOk_bind (okA_returnOk_bind (okA_returnOk_bind (okA_returnOk_bind (okA_returnOk_bind ?_))))
  (try dsimp only)
  split
  · refine okA_returnOk_bind ?_
    refine okA_bind fun _ => ?_
    refine okA_bind fun _ => ?_
    refine okA_bindQ (tgA_decodeUpdateSc _ _ _) fun r hr => ?_
    refine okA_bind fun fh => okA_returnOk ?_
    refine ⟨hp, fun c hc => ?_⟩
    obtain ⟨sz, e⟩ := hr c hc
    refine ⟨sz, ?_⟩
    rw [← e]
    exact held_of_mem hex (the_mem (by omega))
  · exact okA_throw_bind _

set_option maxHeartbeats 4000000 in
theorem tg_decodeTcb {p : ObjRef} (hp : Held w (.threadCap p)) {ex : List (Cap × CslotPtr)}
    (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) (label : Data) (args : List Data) (sl : CslotPtr) :
    OkA (TcbTg w) (decodeTcbInvocation (Z := Unit) label args (.threadCap p) sl ex) := by
  unfold decodeTcbInvocation
  split
  case h_1 => unfold decodeReadRegisters; tg_auto
  case h_2 => unfold decodeWriteRegisters; tg_auto
  case h_3 =>
    unfold decodeCopyRegisters
    split
    · refine okA_returnOk_bind (okA_returnOk_bind (okA_returnOk_bind (okA_returnOk_bind ?_)))
      (try dsimp only)
      refine okA_whenE_bind fun _ => ?_
      refine okA_bindQ (Q := fun t => Held w (.threadCap t)) ?_ fun t ht => ?_
      · split
        · exact okA_returnOk (held_head hex (by assumption))
        · exact okA_throw _
      · exact okA_returnOk_bind (okA_returnOk ht)
    · exact okA_throw _
  case h_4 => exact okA_returnOk hp
  case h_5 => exact okA_returnOk trivial
  case h_6 => unfold decodeTcbConfigure; tg_auto
  case h_7 =>
    unfold decodeSetPriority
    refine okA_whenE_bind fun _ => okA_returnOk_bind ?_
    (try dsimp only)
    split
    swap
    · exact okA_throw_bind _
    refine okA_returnOk_bind (okA_bind fun _ => okA_returnOk ?_)
    exact (show Held w (.threadCap p) ∧ ∀ c, (none : Option (Option ObjRef)) = some (some c) →
      ∃ sz, Held w (.schedContextCap c sz) from ⟨hp, fun c h => by cases h⟩)
  case h_8 =>
    unfold decodeSetMcpriority
    refine okA_whenE_bind fun _ => okA_returnOk_bind ?_
    (try dsimp only)
    split
    swap
    · exact okA_throw_bind _
    refine okA_returnOk_bind (okA_bind fun _ => okA_returnOk ?_)
    exact (show Held w (.threadCap p) ∧ ∀ c, (none : Option (Option ObjRef)) = some (some c) →
      ∃ sz, Held w (.schedContextCap c sz) from ⟨hp, fun c h => by cases h⟩)
  case h_9 => exact tg_setSchedParams hp hex args sl
  case h_10 => unfold decodeSetTimeoutEp; tg_auto
  case h_11 => unfold decodeSetIpcBuffer; tg_auto
  case h_12 => unfold decodeSetSpace; tg_auto
  case h_13 => unfold decodeBindNotification; tg_auto
  case h_14 => unfold decodeUnbindNotification; tg_auto
  case h_15 => unfold decodeSetTlsBase; tg_auto
  case h_16 => unfold decodeSetFlags; tg_auto
  case h_17 => exact okA_throw _

theorem tg_scBind {p : ObjRef} (hs : ∃ sz, Held w (.schedContextCap p sz)) {cs : List Cap}
    (hcs : ∀ c ∈ cs, Held w c) : OkA (ScTg w) (decodeSchedContextBind (Z := Unit) p cs) := by
  unfold decodeSchedContextBind
  refine okA_whenE_bind fun h0 => okA_returnOk_bind ?_
  have hm : Held w (the cs.head?) := hcs _ (the_head_mem h0)
  refine okA_bind fun _ => ?_
  (try dsimp only)
  split
  all_goals repeat' (first
    | exact okA_throw _
    | exact okA_throw_bind _
    | (exact okA_returnOk ⟨hs, hm⟩)
    | (exact okA_returnOk ⟨hs, by rw [← ‹the cs.head? = _›]; exact hm⟩)
    | (refine okA_returnOk_bind ?_)
    | (refine okA_whenE_bind fun _ => ?_)
    | (dsimp only)
    | (refine okA_bind fun _ => ?_))

theorem tg_scUnbindObj {p : ObjRef} (hs : ∃ sz, Held w (.schedContextCap p sz)) (cs : List Cap) :
    OkA (ScTg w) (decodeSchedContextUnbindObject (Z := Unit) p cs) := by
  unfold decodeSchedContextUnbindObject
  refine okA_whenE_bind fun _ => okA_returnOk_bind ?_
  (try dsimp only)
  split
  all_goals repeat' (first
    | exact okA_throw _
    | exact okA_throw_bind _
    | (exact okA_returnOk hs)
    | (refine okA_returnOk_bind ?_)
    | (refine okA_whenE_bind fun _ => ?_)
    | (dsimp only)
    | (refine okA_bind fun _ => ?_))

theorem tg_decodeSc {p : ObjRef} (hs : ∃ sz, Held w (.schedContextCap p sz)) {cs : List Cap}
    (hcs : ∀ c ∈ cs, Held w c) (label : Data) :
    OkA (ScTg w) (decodeSchedContextInvocation (Z := Unit) label p cs) := by
  unfold decodeSchedContextInvocation
  split
  · exact okA_returnOk trivial
  · exact tg_scBind hs hcs
  · exact tg_scUnbindObj hs cs
  · tg_auto
  · unfold decodeSchedContextYieldTo; tg_auto
  · exact okA_throw _

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `TgOK` of the decode view.** -/
theorem tg_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : w.2.1 sl = some cap)
    (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) :
    OkA (TgOK w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    refine okA_ite (okA_throw _) ?_
    unfold fl4DecodeTcbInvocation
    refine okA_ite (okA_liftME (okA_triv fun _ => trivial)) ?_
    split
    · exact okA_liftME (okA_triv fun _ => trivial)
    · exact okA_liftME (tg_decodeTcb ⟨sl, hc⟩ hex label args sl)
  | schedContextCap sc sz =>
    unfold fl4DecodeInvocation
    exact okA_ite (okA_throw _) (okA_liftME (tg_decodeSc ⟨sz, sl, hc⟩ (fun c h => held_of_fst hex h) label))
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okA_throw _ | exact okA_returnOk trivial
      | (exact okA_liftME (okA_triv fun _ => trivial))
      | (refine okA_ite ?_ ?_)
      | (dsimp only)
      | split)

/-- `TgOK` of a decoded invocation (ut7's `DecodedFrom`). -/
theorem tgOK_of {w : UView} {inv : Fl4Invocation} (hD : DecodedFrom w inv) : TgOK w inv := by
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, -, hc, hex, hmem⟩ := hD
  exact tg_fl4Decode fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 inv s0 hmem

end

end Fl4Proofs.P3.SInvI
