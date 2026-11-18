/-
P3 (DESIGN.md §9): **the top level of decode and invocation**,
`syscall::decode_invocation` against FL4's dispatcher `fl4DecodeInvocation`
(`Fl4Spec/Ext/Invocation`), then `set_thread_state Restart` and
`fl4PerformInvocation`.

`TopPost` is the result for every cap: FL4 returned the spec's error with
the state unchanged, or the spec decodes an invocation, restarts the
thread, and has an outcome of the invocation of FL4's kind (done, or
preempted), whose state is related to FL4's (the CSpace relation `CRel`,
with `MdbInv`, and `FinInv`) for some placed typed heap and ghost tree.

`decode_invocation_refines` is the dispatch: the null and zombie caps are
the spec's `InvalidCapability 0`; every other cap type is a hypothesis
(one per type). The hypotheses for the CSpace and untyped caps are this
module's branch theorems (`decode_invocation_untyped`, `_cnode`,
`_irq_control`, `_irq_handler`, `_ioport_control`, `_ioport`), from the
decode refinements of those caps, and the domain cap's is
`decode_invocation_domain` (DomDecode.lean); the others (endpoint,
notification, reply, TCB, scheduling context and control, the VSpace caps)
are for their modules.
-/
import Fl4Proofs.P3.CnodeDecode
import Fl4Proofs.P3.IrqDecode
import Fl4Proofs.P3.IoDecode
import Fl4Proofs.P3.IoPortTop
import Fl4Proofs.P3.UntypedPml4
import Fl4Spec.Ext.Invocation
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The spec's decode `m` has the outcome `inv`, the state unchanged, and
no failure (one of its outcomes: the spec may choose, e.g. a free ASID). -/
def DecOut {α : Type} (m : Fl4Spec.SEMonad Unit α) (σ : Fl4Spec.State Unit) (inv : α) : Prop :=
  ((.ok inv, σ) : Except Fl4Spec.SyscallError α × Fl4Spec.State Unit) ∈ (m.run σ).1 ∧ ¬ (m.run σ).2

/-- **A decode with a single outcome** has it as one of its outcomes. -/
theorem DecOut.of_eq {α : Type} {m : Fl4Spec.SEMonad Unit α} {σ : Fl4Spec.State Unit} {inv : α}
    (h : m.run σ = ({(.ok inv, σ)}, False)) : DecOut m σ inv := by
  unfold DecOut; rw [h]; exact ⟨rfl, id⟩

/-- `liftME` of an outcome. -/
theorem DecOut.liftME {α β : Type} {f : α → β} {m : Fl4Spec.SEMonad Unit α} {σ : Fl4Spec.State Unit} {inv : α}
    (h : DecOut m σ inv) : DecOut (Fl4Spec.NonDetE.liftME f m) σ (f inv) := by
  unfold DecOut Fl4Spec.NonDetE.liftME
  rw [ExceptT.run_bind]
  refine ⟨⟨(.ok inv, σ), h.1, rfl⟩, ?_⟩
  rintro (hf | ⟨⟨r, σ'⟩, -, hf⟩)
  · exact h.2 hf
  · cases r <;> exact hf

/-- **The result of `decode_invocation`** (see the module docstring). -/
def TopPost (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G')

/-- The spec's decode of a cap, as `decode_invocation` calls it. -/
abbrev specDec (fp : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation :=
  Fl4Spec.fl4DecodeInvocation fp slbl args ci sl (absCap c) excaps buffer

/-- The spec's `InvalidCapability 0`, FL4's state and result unchanged. -/
theorem top_invalid {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation}
    {s : S} {a : A} (h : m.run σ = ({(.error (.invalidCapability 0), σ)}, False)) :
    (ok ((.Err (.Sys (.InvalidCapability 0#u64)), s, a) : core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      TopPost (L := L) σ blk call don m s res ⦄ := by
  rw [WP.spec_ok]
  exact Or.inl ⟨_, rfl, rfl, _, h, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- `liftME` of a decode with a single outcome. -/
theorem top_of_lift {α : Type} {f : α → Fl4Spec.Fl4Invocation} {m : Fl4Spec.SEMonad Unit α}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f inv)).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G')) :
    TopPost (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f m) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err hr, he⟩
  · exact Or.inr ⟨f inv, DecOut.of_eq (run_liftME_ok hr), rest⟩

/-- Two `liftME`s of a decode with a single outcome. -/
theorem top_of_lift2 {α β : Type} {f : α → Fl4Spec.Fl4Invocation} {g : β → α} {m : Fl4Spec.SEMonad Unit β}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f (g inv))).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G')) :
    TopPost (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f (Fl4Spec.NonDetE.liftME g m)) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err (run_liftME_err hr), he⟩
  · exact Or.inr ⟨f (g inv), DecOut.of_eq (run_liftME_ok (run_liftME_ok hr)), rest⟩

/-- `liftME` of a decode outcome (`DecOut`: the spec may have several). -/
theorem top_of_liftM {α : Type} {f : α → Fl4Spec.Fl4Invocation} {m : Fl4Spec.SEMonad Unit α}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, DecOut m σ inv ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f inv)).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G')) :
    TopPost (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f m) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err hr, he⟩
  · exact Or.inr ⟨f inv, hr.liftME, rest⟩

/-- Two `liftME`s of a decode outcome (`DecOut`). -/
theorem top_of_lift2M {α β : Type} {f : α → Fl4Spec.Fl4Invocation} {g : β → α} {m : Fl4Spec.SEMonad Unit β}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, DecOut m σ inv ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f (g inv))).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G')) :
    TopPost (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f (Fl4Spec.NonDetE.liftME g m)) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err (run_liftME_err hr), he⟩
  · exact Or.inr ⟨f (g inv), hr.liftME.liftME, rest⟩

/-- The null cap. -/
theorem decode_invocation_null (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    syscall.decode_invocation st arI s ar lbl length slot .Null blk call don fp buf extra ⦃ res =>
      TopPost (L := L) σ blk call don (specDec fp slbl args ci sl .Null excaps buffer) s res ⦄ := by
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  exact top_invalid rfl

/-- A zombie cap. -/
theorem decode_invocation_zombie (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (p zt n : U64) :
    syscall.decode_invocation st arI s ar lbl length slot (.Zombie p zt n) blk call don fp buf extra ⦃ res =>
      TopPost (L := L) σ blk call don (specDec fp slbl args ci sl (.Zombie p zt n) excaps buffer) s res ⦄ := by
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  exact top_invalid rfl

/-- The statement for one cap: FL4's `decode_invocation` against the
spec's dispatcher, `TopPost`. -/
abbrev DecOK (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPost (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

/-- **A CNode cap** (`cnode_decode_refines`). -/
theorem decode_invocation_cnode (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hEp : CancelEpHyp (L := L) th s σ)
    (E : S → Fl4Spec.State Unit → Prop) (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHyp (L := L) arI μ th E) (hPP : RPPHyp (L := L) arI th E)
    (hE : ∀ s1 σ1, SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 σ1)
    (hEF : ∀ s1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 σ1 → FinInv th (L.mem s1) σ1 G1)
    (hfew : μ (L.mem s) G < 2 ^ 64 - 1)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (cnode_decode_refines arI th s ar σ G hR hV hP hM hC lbl slbl hlbl length buf ct hct args
      hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 x1 hx0 hx1 _ hex hI hFI hact hcur htcb hEp E μ hμ hD hPP hE hEF hfew) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_lift (f := Fl4Spec.Fl4Invocation.invokeCNode)
    rcases hq with ⟨e, he, rfl, e', he1, he2⟩ | ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR, hF, -⟩
    · exact Or.inl ⟨e, he, rfl, e', he1, Or.inl he2⟩
    · refine Or.inr ⟨inv, hrun, σ1, hst, ?_⟩
      rcases hcase with ⟨he, hx⟩ | ⟨he, hx⟩
      · exact ⟨(.ok [], σ'), mem_bindE_ok hx (Set.mem_singleton _), th, G', Or.inl ⟨he, [], rfl⟩, hP, hCR, hF⟩
      · exact ⟨(.error (), σ'), mem_bindE_err hx, th, G', Or.inr ⟨he, rfl⟩, hP, hCR, hF⟩
  · exact top_invalid rfl

/-- **An IRQ handler cap** (`irq_handler_decode_refines`). -/
theorem decode_invocation_irq_handler (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length slot (.IrqHandler irq) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (irq_handler_decode_refines arI th hP hO hPD hK s ar σ G hDS hL hIR lbl slbl hlbl ct hct hcur
    htcb hact hmask irq hirq hok extra x0 hx0 excaps hex hxn hFR) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply top_of_lift (f := Fl4Spec.Fl4Invocation.invokeIRQHandler)
  cases r0 with
  | Err e => obtain ⟨rfl, ⟨e', h1, h2⟩, -⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hCR, hF, -, -⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok [], σ'), mem_bindE_ok (mem_liftE hx) (Set.mem_singleton _), th, G',
      Or.inl ⟨rfl, [], rfl⟩, hP, hCR, hF⟩

/-- **The IRQ control cap** (`irq_control_decode_refines`): the remapped
label of FL4 is the spec's `fl4RemappedLabel`. -/
theorem decode_invocation_irq_control (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have e : specDec fp slbl (args.map UScalar.bv) ci (ps.bv, idxs) .IrqControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeIRQControl
        (Fl4Spec.decodeFl4IrqControl (decide (lbl.val = 72)) slbl (args.map UScalar.bv) (ps.bv, idxs)
          (excaps.map Prod.fst)) := by
    rw [hrm]; rfl
  rw [e]
  refine WP.spec_mono (irq_control_decode_refines arI th hP s ar σ G hCR hL hIR hHA hFI hFR lbl slbl hlbl length buf ct
    hct args hlen hargs hcur htcb hact hact2 extra x0 hx0 _ hex hps hls hsrcC nA hnum hnA hmask hAR) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply top_of_lift
  cases r0 with
  | Err e => obtain ⟨rfl, ⟨e', h1, h2⟩, -⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hCR', -, hF, -, -⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok [], σ'), mem_bindE_ok hx (Set.mem_singleton _), th, G',
      Or.inl ⟨rfl, [], rfl⟩, hP, hCR', hF⟩

/-- **The IO port control cap** (`ioport_control_decode_refines`). -/
theorem decode_invocation_ioport_control (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hL : IoLayout th (L.ksb s))
    (hIo : IoRel (L.mem s) (L.ksb s) σ) (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (ioport_control_decode_refines arI th hP s ar σ G hCR hL hIo hPA hFI hFR lbl slbl hlbl length buf
    ct hct args hlen hargs hcur htcb hact hact3 extra x0 hx0 _ hex hps hls hsrcC .ioPortControlCap) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply top_of_lift2 (f := Fl4Spec.Fl4Invocation.invokeArchObject) (g := Fl4Spec.Fl4ArchInvocation.spec)
  cases r0 with
  | Err e => obtain ⟨rfl, ⟨e', h1, h2⟩, -⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hCR', -, hF, -, -⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok [], σ'), hx, th, G', Or.inl ⟨rfl, [], rfl⟩, hP, hCR', hF⟩

/-- **An IO port cap** (`ioport_decode_refines`; `In` not called). -/
theorem decode_invocation_ioport (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hcall : 64 ≤ lbl.val ∧ lbl.val ≤ 66 → call = false)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a'))
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a')
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (ioport_decode_refines arI th hP s ar σ G hCR hFI lbl slbl hlbl length buf ct hct args hlen
    hargs hcur htcb hact first last hfl hl16 call hcall hin hout) ?_
  rintro ⟨r0, s', a'⟩ hq
  apply top_of_lift2 (f := Fl4Spec.Fl4Invocation.invokeArchObject) (g := Fl4Spec.Fl4ArchInvocation.spec)
  cases r0 with
  | Err e => obtain ⟨rfl, e', h1, h2⟩ := hq; exact Or.inl ⟨e, rfl, rfl, e', h1, h2⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', rr, hx, hCR', hF⟩ := hq
    exact Or.inr ⟨inv, hrun, σ1, hst, (.ok rr, σ'), hx, th, G', Or.inl ⟨rfl, rr, rfl⟩, hP, hCR', hF⟩

/-- **An untyped cap** (`untyped_retype_refines_fl4P`, every object type,
resets included). -/
theorem decode_invocation_untyped [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hnt : ∀ x, args.head? = some x → x.val ≤ 13)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val))
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci (pp.bv, idx) excaps buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (untyped_retype_refines_fl4P arI th s ar σ G hR hV hP hM hC hI hU horig lbl slbl hlbl length
    buf ct hct args hlen hargs hnt hcur htcb hact hpp hidx hcap hpal hpfit hfi hhigh hactZ hfree hzero hsb4 hN hns
    hrcb hppS hPP hRst extra x0 hx0 _ hex hfan hDWal hDWobj hDWreg hDWne hhead hgpm hga hgf hgreg) ?_
  rintro res hq
  apply top_of_lift (f := Fl4Spec.Fl4Invocation.invokeUntyped)
  rcases hq with ⟨e, e', rfl, h1, h2⟩ | ⟨inv, hrun, σ1, hst, -, ev, σ', G', th', hcase, ⟨⟨y1, y2⟩, hy, hy1, hK⟩,
    hP', hR', hV', hM', hC', hI', -, -, hFin, -⟩
  · exact Or.inl ⟨e, rfl, rfl, e', h1, Or.inl h2⟩
  · refine Or.inr ⟨inv, hrun, σ1, hst, ?_⟩
    simp only at hy1 hK
    subst hy1
    have hCR : CRel th' (L.mem res.2.1) y2 G' :=
      ⟨hR'.of_kheap hK.1, hV', hM', hC'.of_cdt hK.2.1 hK.2.2.1, hI'⟩
    have hF : FinInv th' (L.mem res.2.1) y2 G' :=
      (hFin hFI).of_same hM' (SlotsSame.refl _ _) (KSub.of_kheap hK.1)
    rcases hcase with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · exact ⟨(.ok [], y2), mem_bindE_ok hy (Set.mem_singleton _), th', G', Or.inl ⟨he, [], rfl⟩, hP', hCR, hF⟩
    · exact ⟨(.error (), y2), mem_bindE_err hy, th', G', Or.inr ⟨he, rfl⟩, hP', hCR, hF⟩

/-- **The dispatch of `decode_invocation`**: for every cap, from one
statement per cap type (`DecOK`), the null and zombie caps aside. The
CSpace and untyped ones are `decode_invocation_untyped`, `_cnode`,
`_irq_control`, `_irq_handler`, `_ioport_control` and `_ioport`. -/
theorem decode_invocation_refines (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (cap : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef)
    (hUntyped : ∀ p sb fi d, cap = .Untyped p sb fi d →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hEndpoint : ∀ p b sd r g gr, cap = .Endpoint p b sd r g gr →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hNotification : ∀ p b sd r, cap = .Notification p b sd r →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hReply : ∀ p g, cap = .Reply p g →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hCNode : ∀ p r gs g, cap = .CNode p r gs g →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hThread : ∀ p, cap = .Thread p →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hIrqControl : cap = .IrqControl →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hIrqHandler : ∀ i, cap = .IrqHandler i →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hDomain : cap = .Domain →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hSchedContext : ∀ p sb, cap = .SchedContext p sb →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hSchedControl : ∀ c, cap = .SchedControl c →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hFrame : ∀ p sz r d m ept asid va, cap = .Frame p sz r d m ept asid va →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hPageTable : ∀ p m asid va, cap = .PageTable p m asid va →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hPageDirectory : ∀ p m asid va, cap = .PageDirectory p m asid va →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hPdpt : ∀ p m asid va, cap = .Pdpt p m asid va →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hPml4 : ∀ p m asid, cap = .Pml4 p m asid →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hAsidControl : cap = .AsidControl →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hAsidPool : ∀ p b, cap = .AsidPool p b →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hVcpu : ∀ p, cap = .Vcpu p →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hEpt : ∀ p level m asid va, cap = .Ept p level m asid va →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hIoPortControl : cap = .IoPortControl →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer)
    (hIoPort : ∀ f l vcpu, cap = .IoPort f l vcpu →
      DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOK (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  cases cap with
  | Null =>
    exact decode_invocation_null arI s ar σ lbl length slot blk call don fp buf extra ct hct slbl args ci sl
      excaps buffer
  | Zombie p zt n =>
    exact decode_invocation_zombie arI s ar σ lbl length slot blk call don fp buf extra ct hct slbl
      args ci sl excaps buffer p zt n
  | Untyped => exact hUntyped _ _ _ _ rfl
  | Endpoint => exact hEndpoint _ _ _ _ _ _ rfl
  | Notification => exact hNotification _ _ _ _ rfl
  | Reply => exact hReply _ _ rfl
  | CNode => exact hCNode _ _ _ _ rfl
  | Thread => exact hThread _ rfl
  | IrqControl => exact hIrqControl rfl
  | IrqHandler => exact hIrqHandler _ rfl
  | Domain => exact hDomain rfl
  | SchedContext => exact hSchedContext _ _ rfl
  | SchedControl => exact hSchedControl _ rfl
  | Frame => exact hFrame _ _ _ _ _ _ _ _ rfl
  | PageTable => exact hPageTable _ _ _ _ rfl
  | PageDirectory => exact hPageDirectory _ _ _ _ rfl
  | Pdpt => exact hPdpt _ _ _ _ rfl
  | Pml4 => exact hPml4 _ _ _ rfl
  | AsidControl => exact hAsidControl rfl
  | AsidPool => exact hAsidPool _ _ rfl
  | IoPortControl => exact hIoPortControl rfl
  | Vcpu => exact hVcpu _ rfl
  | Ept => exact hEpt _ _ _ _ _ rfl
  | IoPort => exact hIoPort _ _ _ rfl

end

end

end Fl4Proofs.P3
