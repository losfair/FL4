/-
P3 (DESIGN.md §9), invariant line G1 (sb2): **the decode's binding facts**
(spec side only; imports SpecInvSbX1).

The two binds of the invocation layer find both ends unbound at their decode
(ut8's decode-carry pattern, on the binding view `bv` instead of the cap view):

* `BindOK b inv`: an SC bind to a TCB (`decode_sched_context_bind`: `sc_tcb sc =
  None`, `tcb_sched_context t = None`) and a `threadControlSched` with a new SC
  (`decode_update_sc`: the TCB's SC and the SC's TCB both `None` when they
  differ) have both ends unbound in `b`.
* `OkB b P m` (every `.ok` outcome of `m` from a state with binding view `b`
  satisfies `P`, the steps keeping the frame `BR`) and the frame-free `OkA P m`
  (every `.ok` outcome satisfies `P`, no state read: used for the decoders whose
  outcomes are other constructors).
* **`okb_fl4Decode`**: every decoded invocation satisfies `BindOK` of the decode
  state's binding view.
-/
import Fl4Proofs.P3.SpecInvSbX1
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **The decode's binding facts.** -/
def BindOK (b : ObjRef → BV) : Fl4Invocation → Prop
  | .invokeSchedContext (.invokeSchedContextBind c (.threadCap t)) => b c = .s none ∧ b t = .t none
  | .invokeTCB (.threadControlSched t _ _ _ _ (some (some c))) => b c = .s none ∧ b t = .t none
  | _ => True

/-! ## `OkA`: outcomes only -/

def OkA {ε α : Type} (P : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → P a

section OkAc
variable {ε α β : Type}

theorem okA_bindQ {P : β → Prop} {Q : α → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hq : OkA Q m) (hg : ∀ a, Q a → OkA P (g a)) : OkA P (m >>= g) := by
  intro σ b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hb
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    exact hg a (hq σ a s' hz) s' b s hy
  · simp at he

theorem okA_bind {P : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hg : ∀ a, OkA P (g a)) : OkA P (m >>= g) := by
  intro σ b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hb
  · exact hg a z.2 b s hy
  · simp at he

theorem okA_triv {P : α → Prop} {m : NonDetE (State Unit) ε α} (h : ∀ a, P a) : OkA P m :=
  fun _ a _ _ => h a

theorem okA_returnOk {P : α → Prop} {a : α} (h : P a) : OkA P (NonDetE.returnOk a : NonDetE (State Unit) ε α) := by
  intro σ b s hb
  have e := Set.mem_singleton_iff.1 hb
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, -⟩ := e; exact h

theorem okA_throw {P : α → Prop} (e : ε) : OkA P (NonDetE.throwError e : NonDetE (State Unit) ε α) := by
  intro σ b s hb
  have e := Set.mem_singleton_iff.1 hb; simp at e

theorem okA_ite {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE (State Unit) ε α} (h1 : OkA P m1)
    (h2 : OkA P m2) : OkA P (if c then m1 else m2) := by
  split <;> assumption

theorem okA_liftME {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α} (h : OkA (fun a => P (f a)) m) :
    OkA P (NonDetE.liftME f m) := by
  unfold NonDetE.liftME
  exact okA_bindQ h fun a ha => okA_returnOk ha

end OkAc

/-! ## `OkB`: outcomes from a binding view -/

def OkB {ε α : Type} (b : ObjRef → BV) (P : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, bv σ.kheap = b → ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → P a

section OkBc
variable {ε α β : Type} {b : ObjRef → BV}

theorem okb_of_okA {P : α → Prop} {m : NonDetE (State Unit) ε α} (h : OkA P m) : OkB b P m :=
  fun σ _ a s hs => h σ a s hs

theorem okb_bind {P : β → Prop} {Q : α → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ h0, SBKE h0 m) (hq : OkB b Q m) (hg : ∀ a, Q a → OkB b P (g a)) : OkB b P (m >>= g) := by
  intro σ hσ c s hc
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hc
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have hv : bv s'.kheap = b := by
      rw [bv_of_br (br_mem_of_sbk (m := ExceptT.run m) hm hz)]; exact hσ
    exact hg a (hq σ hσ a s' hz) s' hv c s hy
  · simp at he

theorem okb_bind_sb {P : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ h0, SBKE h0 m) (hg : ∀ a, OkB b P (g a)) : OkB b P (m >>= g) :=
  okb_bind (Q := fun _ => True) hm (fun _ _ _ _ _ => trivial) fun a _ => hg a

theorem okb_returnOk {P : α → Prop} {a : α} (h : P a) : OkB b P (NonDetE.returnOk a : NonDetE (State Unit) ε α) :=
  okb_of_okA (okA_returnOk h)

theorem okb_throw {P : α → Prop} (e : ε) : OkB b P (NonDetE.throwError e : NonDetE (State Unit) ε α) :=
  okb_of_okA (okA_throw e)

theorem okb_returnOk_bind {P : β → Prop} {a : α} {g : α → NonDetE (State Unit) ε β} (h : OkB b P (g a)) :
    OkB b P (NonDetE.returnOk a >>= g) := by
  intro σ hσ c s hc
  rw [ExceptT.run_bind] at hc
  obtain ⟨z, hz, hc⟩ := hc
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact h σ hσ c s hc

theorem okb_throw_bind {P : β → Prop} (e : ε) {g : α → NonDetE (State Unit) ε β} :
    OkB b P (NonDetE.throwError e >>= g) := by
  intro σ _ c s hc
  rw [ExceptT.run_bind] at hc
  obtain ⟨z, hz, hc⟩ := hc
  obtain rfl := Set.mem_singleton_iff.1 hz
  have e := Set.mem_singleton_iff.1 hc; simp at e

theorem okb_whenE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (hg : ¬ c → OkB b P (g ())) : OkB b P (NonDetE.whenE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.whenE
  by_cases hc : c
  · rw [if_pos hc]; exact okb_throw_bind e
  · rw [if_neg hc]; exact okb_returnOk_bind (hg hc)

theorem okb_liftE_bind {P : β → Prop} {Q : α → Prop} {m : NonDet (State Unit) α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ h0, SBK h0 m) (hq : ∀ σ, bv σ.kheap = b → ∀ x ∈ (m σ).1, Q x.1) (hg : ∀ a, Q a → OkB b P (g a)) :
    OkB b P (NonDetE.liftE m >>= g) := by
  refine okb_bind (Q := Q) (fun h0 => ike_liftE (hm h0)) ?_ hg
  intro σ hσ a s hs
  obtain ⟨x, hx, e⟩ := SInvU.mem_liftE' hs
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact hq σ hσ x hx

theorem okb_ite {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE (State Unit) ε α} (h1 : OkB b P m1)
    (h2 : OkB b P m2) : OkB b P (if c then m1 else m2) := by
  split <;> assumption

theorem okb_liftME {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α} (h : OkB b (fun a => P (f a)) m) :
    OkB b P (NonDetE.liftME f m) := by
  intro σ hσ c s hc
  unfold NonDetE.liftME at hc
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hc
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have e := Set.mem_singleton_iff.1 hy
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h σ hσ _ _ hz
  · simp at he

end OkBc

/-! ## The decoders -/

theorem bv_getSc {p : ObjRef} {σ : State Unit} {x : SchedContext × State Unit}
    (hx : x ∈ (getSchedContext (Z := Unit) p σ).1) : bv σ.kheap p = .s x.1.scTcb := by
  obtain ⟨-, n, hk⟩ := mem_getSchedContext' hx
  exact bv_s.2 ⟨_, n, hk, rfl⟩

theorem bv_getTcbSc {p : ObjRef} {σ : State Unit} {x : Option ObjRef × State Unit}
    (hx : x ∈ (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext p σ).1) : bv σ.kheap p = .t x.1 := by
  obtain ⟨-, x', hk, e⟩ := mem_getTcbSc hx
  exact bv_t.2 ⟨x', hk, e⟩

theorem bv_getScTcb {p : ObjRef} {σ : State Unit} {x : Option ObjRef × State Unit}
    (hx : x ∈ (getScObjRef (Z := Unit) SchedContext.scTcb p σ).1) : bv σ.kheap p = .s x.1 := by
  obtain ⟨-, sc, n, hk, e⟩ := mem_getScTcb hx
  exact bv_s.2 ⟨sc, n, hk, e⟩

/-- Frame-free traversal of a decoder whose outcomes satisfy `P` by construction. -/
macro "okA_auto" : tactic => `(tactic| repeat' (first
  | exact okA_throw _
  | exact okA_returnOk trivial
  | exact okA_liftME (okA_triv fun _ => trivial)
  | (refine okA_bind fun _ => ?_)
  | (refine okA_ite ?_ ?_)
  | (unfold NonDetE.whenE)
  | (unfold NonDetE.unlessE)
  | (dsimp only)
  | split))

theorem okb_decodeSchedContextBind (b : ObjRef → BV) (scPtr : ObjRef) (excaps : List Cap) :
    OkB b (fun a => BindOK b (.invokeSchedContext a)) (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind
  refine okb_whenE_bind fun _ => okb_returnOk_bind ?_
  refine okb_liftE_bind (Q := fun sc => b scPtr = .s sc.scTcb) (fun _ => by sb_auto)
    (fun σ hσ x hx => by rw [← hσ]; exact bv_getSc hx) fun sc hsc => ?_
  (try dsimp only)
  split
  · rename_i tcbPtr heq
    refine okb_whenE_bind fun h1 => ?_
    refine okb_liftE_bind (Q := fun o => b tcbPtr = .t o) (fun _ => by sb_auto)
      (fun σ hσ x hx => by rw [← hσ]; exact bv_getTcbSc hx) fun o ho => ?_
    refine okb_whenE_bind fun h2 => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_whenE_bind fun _ => okb_returnOk ?_
    rw [heq]
    exact ⟨by rw [hsc, not_not.1 h1], by rw [ho, not_not.1 h2]⟩
  · rename_i ntfnPtr bd rs heq
    refine okb_whenE_bind fun _ => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_whenE_bind fun _ => okb_returnOk ?_
    rw [heq]; trivial
  · exact okb_throw_bind _

theorem okb_decodeSchedContextInvocation (b : ObjRef → BV) (label : Data) (scPtr : ObjRef) (excaps : List Cap) :
    OkB b (fun a => BindOK b (.invokeSchedContext a)) (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation
  split
  · exact okb_returnOk trivial
  · exact okb_decodeSchedContextBind b scPtr excaps
  all_goals refine okb_of_okA ?_
  all_goals first
    | exact okA_throw _
    | (unfold decodeSchedContextUnbindObject; okA_auto)
    | (unfold decodeSchedContextYieldTo; okA_auto)
    | okA_auto

/-- `decode_update_sc`'s new SC: both ends unbound. -/
def UscOK (b : ObjRef → BV) (t : ObjRef) (r : Option (Option ObjRef)) : Prop :=
  ∀ c, r = some (some c) → b c = .s none ∧ b t = .t none

theorem okb_decodeUpdateSc (b : ObjRef → BV) (cap : Cap) (slot : CslotPtr) (scCap : Cap) :
    OkB b (UscOK b (objRefOf cap)) (decodeUpdateSc (Z := Unit) cap slot scCap) := by
  unfold decodeUpdateSc
  refine okb_returnOk_bind ?_
  refine okb_liftE_bind (Q := fun o => b (objRefOf cap) = .t o) (fun _ => by sb_auto)
    (fun σ hσ x hx => by rw [← hσ]; exact bv_getTcbSc hx) fun tcbSc ht => ?_
  (try dsimp only)
  cases scCap
  case nullCap =>
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_whenE_bind fun _ => okb_returnOk_bind (okb_returnOk ?_)
    intro c hc
    split_ifs at hc <;> cases hc
  case schedContextCap scp sz =>
    refine okb_returnOk_bind ?_
    refine okb_liftE_bind (Q := fun o => b (objRefOf (.schedContextCap scp sz)) = .s o) (fun _ => by sb_auto)
      (fun σ hσ x hx => by rw [← hσ]; exact bv_getScTcb hx) fun scTcb hs => ?_
    refine okb_whenE_bind fun h1 => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_whenE_bind fun _ => okb_returnOk_bind (okb_returnOk ?_)
    intro c hc
    split_ifs at hc with hne
    simp only [Option.some.injEq] at hc
    subst hc
    have h2 : ¬ (tcbSc ≠ none ∨ scTcb ≠ none) := fun h => h1 ⟨hne, h⟩
    push_neg at h2
    exact ⟨by rw [hs, h2.2], by rw [ht, h2.1]⟩
  all_goals exact okb_throw_bind _

theorem okb_decodeSetSchedParams (b : ObjRef → BV) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (extraCaps : List (Cap × CslotPtr)) :
    OkB b (fun a => BindOK b (.invokeTCB a)) (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams
  refine okb_whenE_bind fun _ => okb_whenE_bind fun _ => ?_
  refine okb_returnOk_bind (okb_returnOk_bind (okb_returnOk_bind (okb_returnOk_bind (okb_returnOk_bind ?_))))
  (try dsimp only)
  split
  · refine okb_returnOk_bind ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun _ => ?_
    refine okb_bind (fun _ => by sb_auto) (okb_decodeUpdateSc b cap slot _) fun r hr => ?_
    refine okb_bind_sb (fun _ => by sb_auto) fun fh => okb_returnOk ?_
    rcases r with _ | _ | c
    · trivial
    · trivial
    · exact hr c rfl
  · exact okb_throw_bind _

set_option maxHeartbeats 4000000 in
theorem okb_decodeTcbInvocation (b : ObjRef → BV) (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) :
    OkB b (fun a => BindOK b (.invokeTCB a)) (decodeTcbInvocation (Z := Unit) label args cap slot excs) := by
  unfold decodeTcbInvocation
  split
  case h_9 => exact okb_decodeSetSchedParams b args cap slot excs
  all_goals refine okb_of_okA ?_
  all_goals first
    | exact okA_throw _
    | exact okA_returnOk trivial
    | (unfold decodeReadRegisters; okA_auto)
    | (unfold decodeWriteRegisters; okA_auto)
    | (unfold decodeCopyRegisters; okA_auto)
    | (unfold decodeTcbConfigure; okA_auto)
    | (unfold decodeSetPriority; okA_auto)
    | (unfold decodeSetMcpriority; okA_auto)
    | (unfold decodeSetTimeoutEp; okA_auto)
    | (unfold decodeSetIpcBuffer; okA_auto)
    | (unfold decodeSetSpace; okA_auto)
    | (unfold decodeBindNotification; okA_auto)
    | (unfold decodeUnbindNotification; okA_auto)
    | (unfold decodeSetTlsBase; okA_auto)
    | (unfold decodeSetFlags; okA_auto)

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `BindOK` of the decode state's binding view.** -/
theorem okb_fl4Decode (b : ObjRef → BV) (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkB b (BindOK b) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    refine okb_ite (okb_throw _) ?_
    unfold fl4DecodeTcbInvocation
    refine okb_ite (okb_of_okA (okA_liftME (okA_triv fun _ => trivial))) ?_
    split
    · exact okb_of_okA (okA_liftME (okA_triv fun _ => trivial))
    · exact okb_liftME (okb_decodeTcbInvocation b label args _ sl ex)
  | schedContextCap sc sz =>
    unfold fl4DecodeInvocation
    exact okb_ite (okb_throw _) (okb_liftME (okb_decodeSchedContextInvocation b label sc _))
  | _ =>
    unfold fl4DecodeInvocation
    refine okb_of_okA ?_
    repeat' (first
      | exact okA_throw _ | exact okA_returnOk trivial
      | (exact okA_liftME (okA_triv fun _ => trivial))
      | (refine okA_ite ?_ ?_)
      | (dsimp only)
      | split)

end

end Fl4Proofs.P3.SInvB
