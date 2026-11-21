/-
P3 (DESIGN.md §9), CSpace: **the J decodes of the `Steps`-producing caps
with the primitive steps' closure proved** (XTopJointRest's `jStepHyps`; a
notification cap's deletion is no primitive step, StepSem), and the liveness
facts of an emptied slot.

* `DelLive`: the liveness facts the empty-slot path reads (XTopJointDelR's
  `JEmptyUtHyp` (a), (b)): every slot in use but the emptied one covered by
  another cap or in the kernel-state block (`SlotLiveAt`), core 0's
  debug-list head, when not null, covered by another cap. `DelLive.of_same`:
  across a step keeping the slots, the kernel base, the original bits and
  the debug word.
* `decode_invocation_{irq_control, ioport_control, domain}J`: XTopJointStep's
  J decodes with `jStepHyps` (the IRQ handler cap's in XTopJointIrqL).
-/
import Fl4Proofs.P3.XTopJointEmptyUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The liveness facts of emptying the slot `sl`** (module docstring;
`JEmptyUtHyp`'s (a), (b)). -/
def DelLive (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) : Prop :=
  (∀ y, IsSlot th y → y ≠ cslotAddr sl →
    (capV (L.mem s) y ≠ .Null ∨ ∃ x, cslotAddr x = y ∧ σ.isOriginalCap x = true) →
    SlotLiveAt (L.mem s) G (L.ksb s) (cslotAddr sl) y) ∧
  (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
    OtherCov (L.mem s) G (cslotAddr sl) (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val
      ((L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val + 1))

theorem OtherCov.of_same {m m' : U64 → U64} {G : MdbGhost} {x : U64} {lo hi : Nat}
    (h : OtherCov m G x lo hi) (he : ∀ y ∈ G.chains.flatten, capV m' y = capV m y) : OtherCov m' G x lo hi := by
  obtain ⟨y, hy, hyx, h1, h2, h3, h4⟩ := h
  exact ⟨y, hy, hyx, by rw [he y hy]; exact h1, by rw [he y hy]; exact h2, by rw [he y hy]; exact h3,
    by rw [he y hy]; exact h4⟩

/-- **`DelLive` across a step keeping the slots** (module docstring). -/
theorem DelLive.of_same {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} (h : DelLive (L := L) th s σ G sl) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hG : ∀ y ∈ G.chains.flatten, IsSlot th y) (hks : L.ksb s' = L.ksb s)
    (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hdbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    DelLive (L := L) th s' σ' G sl := by
  have he : ∀ y ∈ G.chains.flatten, capV (L.mem s') y = capV (L.mem s) y := fun y hy => hSS.capV (hG y hy)
  have hna : L.nodeAt s' 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    nodeAt_ksb hks _ _
  refine ⟨fun y hy hne hu => ?_, fun h0 => ?_⟩
  · have hu' : capV (L.mem s) y ≠ .Null ∨ ∃ x, cslotAddr x = y ∧ σ.isOriginalCap x = true := by
      rcases hu with hu | ⟨x, hx, ho⟩
      · exact Or.inl (by rw [← hSS.capV hy]; exact hu)
      · exact Or.inr ⟨x, hx, by rw [← horig]; exact ho⟩
    rcases h.1 y hy hne hu' with hc | hk
    · exact Or.inl (hc.of_same he)
    · exact Or.inr (by rw [hks]; exact hk)
  · rw [hna, hdbg] at h0 ⊢
    exact (h.2 h0).of_same he

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The IRQ control cap at `JAt`**
(`decode_invocation_irq_controlJ_step`, `jStepHyps`). -/
theorem decode_invocation_irq_controlJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    (hHA : HandlersActive (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct :=
  decode_invocation_irq_controlJ_step arI s ar σ J hni hARI hT (jStepHyps arI) hZB hHA lbl slbl hlbl hrm
    length buf ct hct args hlen hargs hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA hAR blk call don fp ci
    buffer

/-- **The IO port control cap at `JAt`**. -/
theorem decode_invocation_ioport_controlJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct :=
  decode_invocation_ioport_controlJ_step arI s ar σ J hni hARI hT (jStepHyps arI) hZB hPA lbl slbl hlbl
    length buf ct hct args hlen hargs hact3 extra x0 hx0 excaps hex hps hls hsrcC blk call don fp ci buffer

/-- **The domain cap at `JAt`**. -/
theorem decode_invocation_domainJ [Fl4Proofs.P1.PlainStore st] (hcfg : DomConfig) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects Z.th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel Z.th (L.mem s) x0 excs)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .Domain blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excs buffer ct :=
  decode_invocation_domainJ_step arI hcfg s ar σ J hni hARI (jStepHyps arI) hZB ct hct hksO hactK lbl slbl hlbl
    length buf args hlen hargs extra x0 hx0 excs hex slot blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3
