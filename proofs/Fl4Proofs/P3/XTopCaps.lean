/-
P3 (DESIGN.md §9): **`XTop` from the decodes' primitive steps** and the
per-cap discharges of TopXAll's named `XCap` hypotheses.

* `QX`: `XTop`'s instance of `StepClosed` (StepSem): from `XTopAt` at a typed
  heap and the IPC objects outside the kernel-global block (`KsApart`),
  `XTopAt` after (the current thread need not stay runnable: a thread may
  delete itself; the restart takes its own `runnable`); `stepClosed_xtop`, by
  XTopStep's `restart`, `ksStep` and `slotStep`, given `ARMask` (the arch
  relation kept by the interrupt decodes' arch operations, a named
  hypothesis: `ArchRefines` has no such clause).
* `XDelNtfnHyp`: the named premise for a notification cap's deletion (the
  IRQ handler invocations' `IrqSteps`, XTopIrqH; no primitive step since
  StepSem's `StepClosed` lost its deletion field). `stepClosed_xtop` and
  `Steps.xtop` keep it as an unused argument for their callers.
* `decode_invocation_irq_controlX`, `decode_invocation_ioport_controlX`:
  `IrqXHyp` / `IoXHyp` for the IRQ control and IO port control caps, from
  `CPost`'s / `IoCPost`'s `Steps`.
-/
import Fl4Proofs.P3.XTopStep
import Fl4Proofs.P3.RetypeBridge
import Fl4Proofs.P3.DecodeTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Hypothesis: the arch relation is kept by the interrupt and IO port
decodes' arch operations** (an IRQ's mask, an IOAPIC pin's programming, a
port access). -/
def ARMask (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ a c a', AR a c → ArchIrqStep arI a a' → AR a' c

/-- **Hypothesis: `XTopAt` is kept by deleting a notification cap**
(`delete_one`: the notification's finalisation when the cap is final,
`cancel_all_signals` and `unbind_maybe_notification`, then the slot
emptied), at sets whose TCBs include the typed heap's. The single named
finalisation premise of the IRQ handler invocations at `XTop`
(XTopIrqH's `IrqSteps.xtop`); the null cap's deletion is proved
(`IrqSteps.of_del`). To discharge it: the CSpace
side from `delete_one_refines`/`delete_one_keep` (DelOne, with `FinObjHyp`,
`PostDelHyp`, `NtfnKeepHyp`), the kernel-global base and domain words from
`delete_one_dk4` (IrqDom), and the scheduler/IPC side from the
notification finalisation at the IPC relation (`cancel_all_signals`,
`unbind_maybe_notification`) lifted by `IRel.xtop` (IpcXTop). -/
def XDelNtfnHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
    Z.th = th → XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) →
    (∀ t, th t = some .tcb → t ∈ Z.T) → AbsSlot th sl → capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
    cdt.delete_one st arI s a (cslotAddr sl) = ok (s', a') → ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 →
    ∃ G' V', XTopAt (L := L) AR (Z.mv G' V') s' a' σ' ∧ L.ksb s' = L.ksb s

/-- **`XTop`'s instance of `StepClosed`** (module docstring). -/
def QX (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ Z : XSets, Z.th = th → XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) →
    (∀ t, th t = some .tcb → t ∈ Z.T) →
    ∃ G' V', XTopAt (L := L) AR (Z.mv G' V') s' a' σ' ∧ L.ksb s' = L.ksb s

theorem stepClosed_xtop {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (_hDel : XDelNtfnHyp (L := L) arI AR th) :
    StepClosed (L := L) arI th (QX (L := L) AR th) := by
  refine ⟨fun s1 a1 σ1 s2 a2 σ2 s3 a3 σ3 h1 h2 Z hth hX hK hTh => ?_,
    fun s a σ ct x s1 hcur hk htcb hrun hs1 Z hth hX hK hTh => ?_,
    fun s s' a a' σ σ' hw hO hdk hdl hds hirq hio harch Z hth hX hK hTh => ?_,
    fun s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci _ _ _ _ hw hCR hFI hMO hTS _ _ _ _ _ _ _ Z hth hX hK hTh => ?_,
    fun s s' a σ σ' hS Z hth hX hK hTh => ?_,
    fun s s' a σ σ' G' hcn hkc _ _ _ hw hCR hFI hMO hTS _ _ _ _ _ _ _ _ _ _ _ _ Z hth hX hK hTh => ?_⟩
  · obtain ⟨G1, V1, hX1, hk1⟩ := h1 Z hth hX hK hTh
    obtain ⟨G2, V2, hX2, hk2⟩ := h2 (Z.mv G1 V1) hth hX1 (by rw [hk1]; exact hK) hTh
    exact ⟨G2, V2, hX2, hk2.trans hk1⟩
  · have h := XTopAt.restart hX hcur hk hrun
    rw [hs1, WP.spec_ok] at h
    obtain ⟨hX1, -, hk1⟩ := h
    exact ⟨Z.G, Z.vs, hX1, hk1⟩
  · have hD := hX.rel.2.2.2.1
    have hAR := hX.fin.1.1.2.2.2.2.2.2
    exact ⟨Z.G, Z.vs, XTopAt.ksStep hX hK hw hO (hirq hX.fin.1.1.2.2.2.1) (hio hX.fin.1.1.2.2.2.2.1)
      (hD.frame (fun o ho => hdk.2 o ho) hdl hds) (by rw [hO.cr3]; exact hAM _ _ _ hAR harch), hw.1⟩
  · subst hth
    have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [hci]; rfl
    have hcn := capInsert_nkn c _ _ σ _ hmem
    have hSt := hX.rel.2.1.1
    have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko c _ _ σ _ hmem) (by
      rintro p (rfl | hp)
      · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
    have hPl := hX.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    exact ⟨G', Z.vs, XTopAt.slotStep hX hw' hcn hkc hCR hFI hMO hTS, hw.1⟩
  · subst hth
    exact ⟨Z.G, Z.vs, hX.schedStep hK hTh hS, hS.2.1 Z.N Z.T Z.C Z.c hTh hX.fin.1.1.1
      hX.fin.1.1.2.2.1 |>.2.1.1⟩
  · subst hth
    have hPl := hX.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    exact ⟨G', Z.vs, XTopAt.slotStep hX hw' hcn hkc hCR hFI hMO hTS, hw.1⟩

/-- **`XTop` after a run of primitive steps.** -/
theorem Steps.xtop {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (hDel : XDelNtfnHyp (L := L) arI AR th) {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (h : Steps (L := L) arI th s a σ s' a' σ') {Z : XSets} (hth : Z.th = th)
    (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hTh : ∀ t, th t = some .tcb → t ∈ Z.T) :
    XTop (L := L) AR s' a' σ' :=
  let ⟨_, _, hX', _⟩ := h _ (stepClosed_xtop arI hAM hDel) Z hth hX hK hTh
  ⟨_, hX'⟩

/-- **`IrqXHyp` for the IRQ control cap**: every label (the legacy, MSI,
IOAPIC and remapped issues, the errors), from `CPost`'s `Steps`; beyond
`decode_invocation_irq_control`'s hypotheses, `XTopAt` at its typed heap,
`KsApart`, the current thread runnable and `ARMask`. -/
theorem decode_invocation_irq_controlXS {AR : A → Fl4Spec.Cr3 → Prop}
    (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hL : IntLayout th (L.ksb s))
    (hHA : HandlersActive (L.mem s) (L.ksb s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) {Z : XSets} (hth : Z.th = th) (hG : Z.G = G) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hC : CurRun σ) (X : S → A → Fl4Spec.State Unit → Prop) (hXa : X s ar σ)
    (hXS : ∀ s' a' σ', Steps (L := L) arI th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s a σ, X s a σ → XTop (L := L) AR s a σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI X s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  subst hth hG
  have hP := hX0.rel.1
  have hCR := hX0.rel.2.1
  have hFI := hX0.rel.2.2.1
  have hFR := hX0.rel.2.2.2.2.1
  have hIR := hX0.fin.1.1.2.2.2.1
  have htcb : Z.th ct = some .tcb := by
    obtain ⟨t, htb, hth, -⟩ := hX0.fin.2.2.2.2
    rwa [← P1.eq_of_bv (htb.trans hcur)]
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have e : specDec fp slbl (args.map UScalar.bv) ci (ps.bv, idxs) .IrqControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeIRQControl
        (Fl4Spec.decodeFl4IrqControl (decide (lbl.val = 72)) slbl (args.map UScalar.bv) (ps.bv, idxs)
          (excaps.map Prod.fst)) := by
    rw [hrm]; rfl
  rw [e]
  refine WP.spec_mono (irq_control_decode_refines arI Z.th hP s ar σ Z.G hCR hL hIR hHA hFI hFR lbl slbl hlbl length buf ct
    hct args hlen hargs hcur htcb hact hact2 extra x0 hx0 _ hex hps hls hsrcC nA hnum hnA hmask hAR) ?_
  rintro ⟨r0, s', a'⟩ hq
  cases r0 with
  | Err e =>
    obtain ⟨rfl, ⟨e', h1, h2⟩, rfl⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, h2⟩, hXa⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, -, -, -, -, -, -, hstp⟩ := hq
    have hXp := hXS _ _ _ (hstp hC)
    obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXp
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, hXp⟩

/-- **`IrqXHyp` for the IRQ control cap** (`decode_invocation_irq_controlXS`
at `XTop`, `Steps.xtop`): beyond `decode_invocation_irq_control`'s
hypotheses, `XTopAt` at its typed heap, `KsApart`, the current thread
runnable and `ARMask`. -/
theorem decode_invocation_irq_controlX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR)
    (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hL : IntLayout th (L.ksb s))
    (hHA : HandlersActive (L.mem s) (L.ksb s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) {Z : XSets} (hth : Z.th = th) (hG : Z.G = G) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR th) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct :=
  decode_invocation_irq_controlXS arI th s ar σ G hL hHA lbl slbl hlbl hrm length buf ct hct args hlen hargs hcur
    hact hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA hmask hAR hth hG hX0 hC _ ⟨Z, hX0⟩
    (fun _ _ _ h => h.xtop arI hAM hDel hth hX0 hKA hTh) (fun _ _ _ h => h) blk call don fp ci buffer

/-- **`IoXHyp` for the IO port control cap**: every label, from `IoCPost`'s
`Steps`; beyond `decode_invocation_ioport_control`'s hypotheses, `XTopAt`
at its typed heap, `KsApart`, the current thread runnable and `ARMask`. -/
theorem decode_invocation_ioport_controlXS {AR : A → Fl4Spec.Cr3 → Prop}
    (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) (hL : IoLayout th (L.ksb s))
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    {Z : XSets} (hth : Z.th = th) (hG : Z.G = G) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hC : CurRun σ) (X : S → A → Fl4Spec.State Unit → Prop) (hXa : X s ar σ)
    (hXS : ∀ s' a' σ', Steps (L := L) arI th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s a σ, X s a σ → XTop (L := L) AR s a σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI X s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  subst hth hG
  have hP := hX0.rel.1
  have hCR := hX0.rel.2.1
  have hFI := hX0.rel.2.2.1
  have hFR := hX0.rel.2.2.2.2.1
  have hIo := hX0.fin.1.1.2.2.2.2.1
  have htcb : Z.th ct = some .tcb := by
    obtain ⟨t, htb, hth, -⟩ := hX0.fin.2.2.2.2
    rwa [← P1.eq_of_bv (htb.trans hcur)]
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (ioport_control_decode_refines arI Z.th hP s ar σ Z.G hCR hL hIo hPA hFI hFR lbl slbl hlbl length buf
    ct hct args hlen hargs hcur htcb hact hact3 extra x0 hx0 _ hex hps hls hsrcC .ioPortControlCap) ?_
  rintro ⟨r0, s', a'⟩ hq
  cases r0 with
  | Err e =>
    obtain ⟨rfl, ⟨e', h1, h2⟩, rfl⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err (run_liftME_err h1), h2⟩, hXa⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, -, -, -, -, -, -, hstp⟩ := hq
    have hXp := hXS _ _ _ (hstp hC)
    obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXp
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok (run_liftME_ok hrun)), σ1, hst, (.ok [], σ'), hx,
      ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1, hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩,
      hXp⟩

/-- **`IoXHyp` for the IO port control cap**
(`decode_invocation_ioport_controlXS` at `XTop`, `Steps.xtop`). -/
theorem decode_invocation_ioport_controlX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR)
    (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) (hL : IoLayout th (L.ksb s))
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    {Z : XSets} (hth : Z.th = th) (hG : Z.G = G) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR th) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct :=
  decode_invocation_ioport_controlXS arI th s ar σ G hL hPA lbl slbl hlbl length buf ct hct args hlen hargs hcur hact
    hact3 extra x0 hx0 excaps hex hps hls hsrcC hth hG hX0 hC _ ⟨Z, hX0⟩
    (fun _ _ _ h => h.xtop arI hAM hDel hth hX0 hKA hTh) (fun _ _ _ h => h) blk call don fp ci buffer

end

end

end Fl4Proofs.P3
