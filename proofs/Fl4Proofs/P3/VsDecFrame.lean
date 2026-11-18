/-
P3 (DESIGN.md §9), VSpace: **frame caps at the top of `decode_invocation`**
(DecodeTop's `DecOK`, `TopPost`).

* `crel_after`: the CSpace relation, `MdbInv` and `FinInv` after a VSpace
  invocation with the footprint of VsFoot (VsMdb `Recap.carry`).
* `perf_page_mem`: an outcome of the spec's Restart and page invocation
  (`MapSpec`) as an outcome of `fl4PerformInvocation`.
* `decode_invocation_frame`: a frame cap, every label. `Map` (each page
  size, with and without the extra cap) and `Unmap` are this module's;
  `GetAddress`, `TestAndClearAccessed` and `DeriveSubframe` are named
  hypotheses (`hGA`, `hTAC`, `hDS`: the first two reply inside decode, the
  last waits on `FinInv`'s frame-alias relaxation); every other label is
  l4v's `IllegalOperation`.
-/
import Fl4Proofs.P3.VsDecTop
import Fl4Proofs.P3.HandleTop
import Fl4Proofs.P3.VsMakePoolRel
import Fl4Proofs.P3.VsSubRel
import Fl4Proofs.P3.VsMdb
import Fl4Proofs.P3.SpecCnK
import Fl4Proofs.P3.VsFrameMapLRel
import Fl4Proofs.P3.VsFrameUnmapRel
import Fl4Proofs.P3.VsPdptUnmapRel
import Fl4Proofs.P3.VsPdUnmapRel
import Fl4Proofs.P3.VsPtUnmapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

/-- **The CSpace relation and `FinInv` after a VSpace invocation** with
the footprint of VsFoot. -/
theorem crel_after {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {x : U64}
    {c : capability.Cap} (hCR : CRel th m σ G) (hFI : FinInv th m σ G) (hcx : capAt m x = ok c)
    (hSt' : StateRel th m' σ') (hSV' : SlotsValid th m') (hF : SlotFoot th m m' x)
    (hL : MdbLike (capV m' x) c) (hK : KFoot σ σ') : CRel th m' σ' G ∧ FinInv th m' σ' G := by
  obtain ⟨-, -, hM, hC, hI⟩ := hCR
  have hcv : capV m x = c := by rw [capAt_capV] at hcx; simpa using hcx
  obtain ⟨hM', hC', hI', hFI'⟩ := Recap.carry hM hC hI hFI hF (by rw [hcv]; exact hL) hK
  exact ⟨⟨hSt', hSV', hM', hC', hI'⟩, hFI'⟩

/-- **`FrameInv` after a VSpace invocation** with the footprint of VsFoot
(the frame and page-table map/unmap, Assign, the flushes: every perform
whose post gives `SlotFoot` and `MdbLike`). -/
theorem frameinv_after {th : TypedHeap} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} {G : MdbGhost} {x : U64}
    {c : capability.Cap} (hCR : CRel th m σ G) (hFR : FrameInv m G) (hcx : capAt m x = ok c)
    (hF : SlotFoot th m m' x) (hL : MdbLike (capV m' x) c) : FrameInv m' G := by
  have hcv : capV m x = c := by rw [capAt_capV] at hcx; simpa using hcx
  exact hFR.after hCR.2.2.1 hF (by rw [hcv]; exact hL)

/-- `crel_after` and `frameinv_after` together. -/
theorem crelF_after {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {x : U64}
    {c : capability.Cap} (hCR : CRel th m σ G) (hFI : FinInv th m σ G) (hFR : FrameInv m G) (hcx : capAt m x = ok c)
    (hSt' : StateRel th m' σ') (hSV' : SlotsValid th m') (hF : SlotFoot th m m' x)
    (hL : MdbLike (capV m' x) c) (hK : KFoot σ σ') :
    CRel th m' σ' G ∧ FinInv th m' σ' G ∧ FrameInv m' G :=
  ⟨(crel_after hCR hFI hcx hSt' hSV' hF hL hK).1, (crel_after hCR hFI hcx hSt' hSV' hF hL hK).2,
    frameinv_after hCR hFR hcx hF hL⟩

/-- `crel_after` and the MDB invariants (`MdbStep.ok` of a remap). -/
theorem crelM_after {k : U64} {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {x : U64}
    {c : capability.Cap} (hCR : CRel th m σ G) (hFI : FinInv th m σ G) (hMO : MdbOKV k m G) (hcx : capAt m x = ok c)
    (hSt' : StateRel th m' σ') (hSV' : SlotsValid th m') (hF : SlotFoot th m m' x)
    (hL : VsLike (capV m' x) c) (hK : KFoot σ σ') (hu : isUt c = false) :
    CRel th m' σ' G ∧ FinInv th m' σ' G ∧ MdbOKV k m' G :=
  ⟨(crel_after hCR hFI hcx hSt' hSV' hF hL.1 hK).1, (crel_after hCR hFI hcx hSt' hSV' hF hL.1 hK).2,
    (Vs.mstep_remap hCR.2.2.1 hF hcx hL hu).okv hMO⟩

/-- A page invocation's outcome after the Restart. -/
theorem perf_page_mem {σ σ1 σ' : Fl4Spec.State Unit} {iv : Fl4Spec.ArchInvocation} (blk call don : Bool)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : MapSpec σ iv σ') :
    ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeArchObject (.spec iv))).run σ1).1 := by
  cases iv with
  | invokePage pi =>
    obtain ⟨h1, -⟩ := h
    rw [nd_bind_one hst] at h1
    exact mem_liftE (ε := Unit) (x := ([], σ')) h1
  | _ => exact h.elim

/-- An outcome of the spec's Restart and a table invocation, for `fl4PerformInvocation`. -/
theorem perf_tbl_mem {σ σ1 σ' : Fl4Spec.State Unit} {iv : Fl4Spec.ArchInvocation} (blk call don : Bool)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : PtMapSpec σ iv σ' ∨ PdMapSpec σ iv σ' ∨ PdptMapSpec σ iv σ') :
    ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeArchObject (.spec iv))).run σ1).1 := by
  cases iv with
  | invokePageTable pi =>
    rcases h with ⟨h1, -⟩ | h | h
    · rw [nd_bind_one hst] at h1
      exact mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) h1 (Set.mem_singleton _))
    · exact h.elim
    · exact h.elim
  | invokePageDirectory pi =>
    rcases h with h | ⟨h1, -⟩ | h
    · exact h.elim
    · rw [nd_bind_one hst] at h1
      exact mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) h1 (Set.mem_singleton _))
    · exact h.elim
  | invokePDPT pi =>
    rcases h with h | h | ⟨h1, -⟩
    · exact h.elim
    · exact h.elim
    · rw [nd_bind_one hst] at h1
      exact mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) h1 (Set.mem_singleton _))
  | _ => rcases h with h | h | h <;> exact h.elim

/-- FL4's finality test against the spec's, for a table cap in a slot. -/
theorem fin_iff_of {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap} (hP : Placed th)
    {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hN : NeedsFin c) (hz : isZb c = false)
    (hne : c ≠ .Null) (hr : Fl4Spec.genObjRefs (absCap c) ≠ ∅) :
    finF (L.mem s) (cslotAddr sl) = true ↔ Fl4Spec.isFinalCap' (absCap c) σ := by
  obtain ⟨hR, -, hM, -, hI⟩ := hCR
  have hcv : capV (L.mem s) (cslotAddr sl) = c := by rw [capAt_capV] at hc; simpa using hc
  have hx : cslotAddr sl ∈ G.chains.flatten := (hM.members _).2 ⟨hA.isSlot, c, hc, hne⟩
  rw [finF_iff hP hM hI hFI hx (by rw [hcv]; exact hN) (by rw [hcv]; exact hz),
    ← hcv, final_iff hP hR hM hFI hA (by rw [hcv]; exact hr)]

theorem decodeAssign_bad {lbl : Fl4Spec.Data}
    (hl : Fl4Spec.invocationType lbl = .archInvocationLabel .x64ASIDPoolAssign)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (p base : Fl4Spec.ObjRef)
    {c : Fl4Spec.Cap} (hc : ∀ pb, c ≠ .archObjectCap (.pml4Cap pb none)) (sl : Fl4Spec.CslotPtr)
    (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) lbl args xs cte (.asidPoolCap p base) ((c, sl) :: rest)) σ =
      ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold Fl4Spec.archDecodeInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  split
  · rename_i pb h; exact absurd h (hc pb)
  · rfl

theorem decodeAssign_trunc {lbl : Fl4Spec.Data}
    (hl : Fl4Spec.invocationType lbl = .archInvocationLabel .x64ASIDPoolAssign)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (p base : Fl4Spec.ObjRef)
    (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) lbl args xs cte (.asidPoolCap p base) []) σ =
      ({(.error .truncatedMessage, σ)}, False) := by
  unfold Fl4Spec.archDecodeInvocation
  dsimp only
  rw [if_pos hl, if_neg (by simp)]; rfl

theorem decodeAssign_illegal {lbl : Fl4Spec.Data}
    (hl : Fl4Spec.invocationType lbl ≠ .archInvocationLabel .x64ASIDPoolAssign)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (p base : Fl4Spec.ObjRef)
    (ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) lbl args xs cte (.asidPoolCap p base) ex) σ =
      ({(.error .illegalOperation, σ)}, False) := by
  unfold Fl4Spec.archDecodeInvocation
  dsimp only
  rw [if_neg hl]; rfl

theorem decodeMP_trunc {lbl : Fl4Spec.Data}
    (hl : Fl4Spec.invocationType lbl = .archInvocationLabel .x64ASIDControlMakePool)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr)
    (ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (h : ex.length ≤ 1) (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) lbl args xs cte .asidControlCap ex) σ =
      ({(.error .truncatedMessage, σ)}, False) := by
  unfold Fl4Spec.archDecodeInvocation
  dsimp only
  rw [if_pos hl, if_neg (by omega)]; rfl

theorem decodeMP_illegal {lbl : Fl4Spec.Data}
    (hl : Fl4Spec.invocationType lbl ≠ .archInvocationLabel .x64ASIDControlMakePool)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr)
    (ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) lbl args xs cte .asidControlCap ex) σ =
      ({(.error .illegalOperation, σ)}, False) := by
  unfold Fl4Spec.archDecodeInvocation
  dsimp only
  rw [if_neg hl]; rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- Label agreement for native frame invocations, excluding EPT mapping. -/
structure FrameLabel (lbl : U64) (slbl : Fl4Spec.Data) : Prop where
  native : lbl ≠ fl4_abi.label.X86PageMapEPT
  ds : Fl4Spec.dataToNat slbl = Fl4Spec.fl4DeriveSubframeLabel → lbl = fl4_abi.label.X86PageDeriveSubframe
  dsr : lbl = fl4_abi.label.X86PageDeriveSubframe → Fl4Spec.dataToNat slbl = Fl4Spec.fl4DeriveSubframeLabel
  tac : Fl4Spec.dataToNat slbl = Fl4Spec.fl4TestAndClearLabel → lbl = fl4_abi.label.X86PageTestAndClearAccessed
  map : lbl = fl4_abi.label.X86PageMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap
  unmap : lbl = fl4_abi.label.X86PageUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageUnmap
  ga : lbl = fl4_abi.label.X86PageGetAddress →
    Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress
  tacr : lbl = fl4_abi.label.X86PageTestAndClearAccessed →
    Fl4Spec.dataToNat slbl = Fl4Spec.fl4TestAndClearLabel
  other : lbl ≠ fl4_abi.label.X86PageMap → lbl ≠ fl4_abi.label.X86PageUnmap →
    lbl ≠ fl4_abi.label.X86PageGetAddress → lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed →
    lbl ≠ fl4_abi.label.X86PageDeriveSubframe →
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageMap ∧
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageUnmap ∧
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageGetAddress


set_option maxHeartbeats 8000000 in
/-- **A frame cap**, every label (see the module docstring): `DecOK`, or
`DecOKR` for the labels that reply in the decode (`GetAddress`,
`TestAndClearAccessed`). -/
theorem decode_invocation_frameX [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      X s' a' σ')
    (hH1 : VsFrameHyps st A arI th P L4 L3 L2 L1 SR) (hHL : VsFrameHypsL st A arI th P L4 L3 L2 L1 SR)
    (hHU : VsFrameUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hfm : m = true → asid ≠ 0#u64)
    (hpaS : sz = .Small → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaL : sz = .Large → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaH : sz = .Huge → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hGA : lbl = fl4_abi.label.X86PageGetAddress →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct)
    (hTAC : lbl = fl4_abi.label.X86PageTestAndClearAccessed →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct)
    (hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) :
    (lbl ≠ fl4_abi.label.X86PageGetAddress ∧ lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed ∧
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) ∨
    ((lbl = fl4_abi.label.X86PageGetAddress ∨ lbl = fl4_abi.label.X86PageTestAndClearAccessed) ∧
    DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) := by
  by_cases hga : lbl = fl4_abi.label.X86PageGetAddress
  · exact Or.inr ⟨Or.inl hga, hGA hga⟩
  by_cases htac : lbl = fl4_abi.label.X86PageTestAndClearAccessed
  · exact Or.inr ⟨Or.inr htac, hTAC htac⟩
  by_cases hds : lbl = fl4_abi.label.X86PageDeriveSubframe
  · exact Or.inl ⟨hga, htac, hDS hds⟩
  refine Or.inl ⟨hga, htac, ?_⟩
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  obtain ⟨cS, aS, hcS, hcaS, -⟩ := hSt.slot_cap (Z := Unit) (sl := (pc.bv, idx)) (p := pc) rfl
    (by simpa [hidx] using hpc)
  rw [hcap] at hcS; cases eq_of_ok_eq hcS
  have hfw : CapWf (.Frame p sz rt d m false asid va) := hcaS.1
  have hfe : EncWf (.Frame p sz rt d m false asid va) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  have hfcv : CapValid th (.Frame p sz rt d m false asid va) :=
    hSV.cnode pc r hpc (blVal 0 idx) (hidx ▸ blVal_lt idx) _
      (by rw [show slotAddr pc.bv (BitVec.ofNat 64 (blVal 0 idx)) = cslotAddr (pc.bv, idx) from
        (slotAddr_ofBl pc idx).symm]; exact hcap)
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hPV1 : ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b := fun b ⟨q, hq, i, hi, e⟩ =>
    hPV b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) := rfl
  rw [hspec]
  have hd : Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
        (args.map UScalar.bv) ci (pc.bv, idx) (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) := by
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_neg (fun h => hds (hlbl.ds h)), if_neg (fun h => htac (hlbl.tac h))]
  rw [hd]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  by_cases hmap : lbl = fl4_abi.label.X86PageMap
  · subst hmap
    have hl := hlbl.map rfl
    unfold vspace.decode_frame
    simp only [vspace.as_frame, bind_ok, hlbl.native, Bool.false_eq_true, ↓reduceIte, ite_self]
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, hcx, hvr, rfl, hvc⟩
    · unfold vspace.decode_page_map
      rw [hct, hex]
      simp only [bind_ok, error.truncated, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage,
        decodeMap_trunc hl _ _ _ _ _ _ _ _ _ (by simp) σ, Or.inl trivial⟩) hX0
    have post : ∀ res, ((∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) ((vc', xsl) :: rest)) σ = ({(.error e', σ)}, False) ∧
          res.2.1 = s ∧ res.2.2 = ar) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv)
          ci (pc.bv, idx) (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) ((vc', xsl) :: rest)) σ = ({(.ok iv, σ)}, False) ∧
        MapSpec σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf ⟨p, sz, rt, d, m, false, asid, va⟩) ∧
        KFoot σ σ')) →
        TopPostMX (L := L) X σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
            (args.map UScalar.bv) ci (pc.bv, idx) (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) ((vc', xsl) :: rest))))
          s res ∧ FootQ Q s res := by
      rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, hSt', hSV', hR', hPt', hSRq, hF, hL, hK⟩)
      · exact topMQX_err (⟨e, h1, h2, e', hdec, he.elim id (fun ⟨h3, h4⟩ => h3 ▸ h4 ▸ hAl)⟩) (by rw [h2, h2a]; exact hX0)
      · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_page_mem blk call don hst1 hms,
          (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
          (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
    cases sz
    · exact WP.spec_mono (frame_map_rel hH1 s ar σ hP hVP hD hPP hPS hPV1 hPO hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt)
        htcb hact ⟨p, .Small, rt, d, m, false, asid, va⟩ rfl hfw hfe hfcv hfm (hpaS rfl) hpc hidx hl length buf args hlen
        hargs ci extra hex hcx hvr xsl rest hvc) post
    · exact WP.spec_mono (frame_map_large_rel hHL s ar σ hP hVP hD hPP hPS hPV hPO hSt hSV hR hPt hS ct hct hcur'
        hkt (hrun _ hkt) htcb hact ⟨p, .Large, rt, d, m, false, asid, va⟩ rfl hfw hfe hfcv hfm (hpaL rfl) hpc hidx hl length buf args
        hlen hargs ci extra hex hcx hvr xsl rest hvc) post
    · exact WP.spec_mono (frame_map_huge_rel hHL s ar σ hP hVP hD hPP hPS hPV hPO hSt hSV hR hPt hS ct hct hcur'
        hkt (hrun _ hkt) htcb hact ⟨p, .Huge, rt, d, m, false, asid, va⟩ rfl hfw hfe hfcv hfm (hpaH rfl) hpc hidx hl length buf args
        hlen hargs ci extra hex hcx hvr xsl rest hvc) post
  by_cases hunmap : lbl = fl4_abi.label.X86PageUnmap
  · subst hunmap
    have hl := hlbl.unmap rfl
    refine WP.spec_mono (frame_unmap_rel hHU s ar σ hP hVP hD hPP hPS hPV hPI hPO hSt hSV hR hPt hS ct hct hcur'
      hkt (hrun _ hkt) htcb hact ⟨p, sz, rt, d, m, false, asid, va⟩ hfw hfe hfm hpc hidx hcap hl length buf call extra
      (args.map UScalar.bv) ci excaps) ?_
    rintro res ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK⟩
    exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_page_mem blk call don hst1 hms,
      (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
      (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2, o3⟩ := hlbl.other hmap hunmap hga htac hds
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, hmap, hunmap, hga, htac, hds, hlbl.native, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) σ = _
  unfold Fl4Spec.decodePageInvocation frameACapG; dsimp only
  rw [if_neg o1, if_neg o2, if_neg o3]; rfl


/-- **A frame cap**, every label (see the module docstring): `DecOK`, or
`DecOKR` for the labels that reply in the decode (`GetAddress`,
`TestAndClearAccessed`). -/
theorem decode_invocation_frame [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hH1 : VsFrameHyps st A arI th P L4 L3 L2 L1 SR) (hHL : VsFrameHypsL st A arI th P L4 L3 L2 L1 SR)
    (hHU : VsFrameUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hfm : m = true → asid ≠ 0#u64)
    (hpaS : sz = .Small → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaL : sz = .Large → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaH : sz = .Huge → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hGA : lbl = fl4_abi.label.X86PageGetAddress →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct)
    (hTAC : lbl = fl4_abi.label.X86PageTestAndClearAccessed →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct)
    (hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKMQ (L := L) arI Q s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) :
    (lbl ≠ fl4_abi.label.X86PageGetAddress ∧ lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed ∧
    DecOKMQ (L := L) arI Q s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) ∨
    ((lbl = fl4_abi.label.X86PageGetAddress ∨ lbl = fl4_abi.label.X86PageTestAndClearAccessed) ∧
    DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct) := by
  exact (decode_invocation_frameX arI th hP s ar σ G hCR hFI hMO hQ (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) hH1 hHL hHU hS hVP hD hPP hPS hPV hPO hPI hR hPt lbl slbl hlbl length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hfm hpaS hpaL hpaH hAl extra excaps hext blk call don fp ci buffer hGA hTAC (fun h => DecOKMQ.toXT arI (hDS h))).imp (fun h => ⟨h.1, h.2.1, DecOKMQX.toMQ arI h.2.2⟩) id

set_option maxHeartbeats 8000000 in
/-- **A PageTable cap**, every label (`Map`, `Unmap`; any other l4v's `IllegalOperation`). -/
theorem decode_invocation_page_tableX (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      X s' a' σ')
    (hHM : VsPtMapHyps st A arI th P L4 L3 L2 L1 SR) (hHU : VsPtUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0)) (hpL : ptr ∈ L1)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hfe : EncWf (.PageTable ptr mp asid0 va0) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hAs : AbsSlot th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.PageTable ptr mp asid0 va0) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci (pc.bv, idx) (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))
          excaps)) := rfl
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hne : ¬ fl4_abi.label.X86PageTableMap = fl4_abi.label.X86PageTableUnmap := by
    unfold fl4_abi.label.X86PageTableMap fl4_abi.label.X86PageTableUnmap; decide
  by_cases hm : lbl = fl4_abi.label.X86PageTableMap
  · subst hm
    have hl := hlM rfl
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, hcx, hvr, rfl, hvc⟩
    · unfold vspace.decode_table
      simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
      have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) []) σ =
          ({(.error .truncatedMessage, σ)}, False) := ptDecode_trunc hl _ _ _ _ _ (by simp) σ
      cases mp
      · simp only [Bool.false_eq_true, ↓reduceIte]
        unfold vspace.decode_table_map
        rw [hct, hex]
        simp only [bind_ok, error.truncated, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
      · simp only [↓reduceIte]
        rw [hex]
        simp only [bind_ok, error.truncated, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
    refine WP.spec_mono (pt_map_rel hHM s ar σ hP hVP hD hPP hPS (fun b hb => hPV b (let ⟨q, hq, i, hi, e⟩ := hb; ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩)) hSt hSV hR hPt hS
      ct hct hcur' hkt (hrun _ hkt) htcb hact hPO ptr asid0 va0 mp hpL hfe hpa hpc hidx hl length buf args hlen hargs ci extra
      hex hcx hvr xsl rest hvc) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, hSt', hSV', hR', hPt', hSRq, hF, hL, hK⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 (Or.inl hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  by_cases hu : lbl = fl4_abi.label.X86PageTableUnmap
  · subst hu
    have hl := hlU rfl
    have hfinR := fin_iff_of hP hCR hFI hAs hcap (Or.inl ⟨trivial, rfl⟩) rfl (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.PageTable ptr mp asid0 va0)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    refine WP.spec_mono (pt_unmap_rel hHU s ar σ hP hVP hD hPP hPS (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩) hPI hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt) htcb
      hact hPO ptr asid0 va0 mp hpL hfe hm0 hpc hidx hcap hl length buf (args.map UScalar.bv) ci extra excaps
      (is_final_eq s _) hfinR) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 (Or.inl hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2⟩ := hlO hm hu
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, hm, hu, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePageTableInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) excaps) σ = _
  unfold Fl4Spec.decodePageTableInvocation; dsimp only
  rw [if_neg o1, if_neg o2]; rfl

/-- **A PageTable cap**, every label (`Map`, `Unmap`; any other l4v's `IllegalOperation`). -/
theorem decode_invocation_page_table (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hHM : VsPtMapHyps st A arI th P L4 L3 L2 L1 SR) (hHU : VsPtUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0)) (hpL : ptr ∈ L1)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQ (L := L) arI Q s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  exact DecOKMQX.toMQ arI (decode_invocation_page_tableX arI th hP s ar σ G hCR hFI hMO hQ (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) hHM hHU hS hVP hD hPP hPS hPV hPO hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer)

set_option maxHeartbeats 8000000 in
/-- **A PageDirectory cap**, every label (`Map`, `Unmap`; any other l4v's `IllegalOperation`). -/
theorem decode_invocation_page_directoryX (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      X s' a' σ')
    (hHM : VsPdMapHyps st A arI th P L4 L3 L2 L1 SR) (hHU : VsPdUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0)) (hpL : ptr ∈ L2)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hfe : EncWf (.PageDirectory ptr mp asid0 va0) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hAs : AbsSlot th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.PageDirectory ptr mp asid0 va0) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci (pc.bv, idx) (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))
          excaps)) := rfl
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hne : ¬ fl4_abi.label.X86PageDirectoryMap = fl4_abi.label.X86PageDirectoryUnmap := by
    unfold fl4_abi.label.X86PageDirectoryMap fl4_abi.label.X86PageDirectoryUnmap; decide
  by_cases hm : lbl = fl4_abi.label.X86PageDirectoryMap
  · subst hm
    have hl := hlM rfl
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, hcx, hvr, rfl, hvc⟩
    · unfold vspace.decode_table
      simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
      have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) []) σ =
          ({(.error .truncatedMessage, σ)}, False) := pdDecode_trunc hl _ _ _ _ _ (by simp) σ
      cases mp
      · simp only [Bool.false_eq_true, ↓reduceIte]
        unfold vspace.decode_table_map
        rw [hct, hex]
        simp only [bind_ok, error.truncated, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
      · simp only [↓reduceIte]
        rw [hex]
        simp only [bind_ok, error.truncated, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
    refine WP.spec_mono (pd_map_rel hHM s ar σ hP hVP hD hPP hPS (fun b hb => hPV b (let ⟨q, hq, i, hi, e⟩ := hb; ⟨q, Or.inr (Or.inl hq), i, hi, e⟩)) hSt hSV hR hPt hS
      ct hct hcur' hkt (hrun _ hkt) htcb hact hPO ptr asid0 va0 mp hpL hfe hpa hpc hidx hl length buf args hlen hargs ci extra
      hex hcx hvr xsl rest hvc) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, hSt', hSV', hR', hPt', hSRq, hF, hL, hK⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 ((Or.inr ∘ Or.inl) hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  by_cases hu : lbl = fl4_abi.label.X86PageDirectoryUnmap
  · subst hu
    have hl := hlU rfl
    have hfinR := fin_iff_of hP hCR hFI hAs hcap (Or.inl ⟨trivial, rfl⟩) rfl (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.PageDirectory ptr mp asid0 va0)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    refine WP.spec_mono (pd_unmap_rel hHU s ar σ hP hVP hD hPP hPS (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) hPI hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt) htcb
      hact hPO ptr asid0 va0 mp hpL hfe hm0 hpc hidx hcap hl length buf (args.map UScalar.bv) ci extra excaps
      (is_final_eq s _) hfinR) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 ((Or.inr ∘ Or.inl) hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2⟩ := hlO hm hu
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, hm, hu, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePageDirectoryInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) excaps) σ = _
  unfold Fl4Spec.decodePageDirectoryInvocation; dsimp only
  rw [if_neg o1, if_neg o2]; rfl

/-- **A PageDirectory cap**, every label (`Map`, `Unmap`; any other l4v's `IllegalOperation`). -/
theorem decode_invocation_page_directory (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hHM : VsPdMapHyps st A arI th P L4 L3 L2 L1 SR) (hHU : VsPdUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0)) (hpL : ptr ∈ L2)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQ (L := L) arI Q s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  exact DecOKMQX.toMQ arI (decode_invocation_page_directoryX arI th hP s ar σ G hCR hFI hMO hQ (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) hHM hHU hS hVP hD hPP hPS hPV hPO hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer)

set_option maxHeartbeats 8000000 in
/-- **A Pdpt cap**, every label (`Map`, `Unmap`; any other l4v's `IllegalOperation`). -/
theorem decode_invocation_pdptX (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      X s' a' σ')
    (hHM : VsPdptMapHyps st A arI th P L4 L3 L2 L1 SR) (hHU : VsPdptUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0)) (hpL : ptr ∈ L3)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hfe : EncWf (.Pdpt ptr mp asid0 va0) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hAs : AbsSlot th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.Pdpt ptr mp asid0 va0) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci (pc.bv, idx) (.pdPointerTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))
          excaps)) := rfl
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hne : ¬ fl4_abi.label.X86PDPTMap = fl4_abi.label.X86PDPTUnmap := by
    unfold fl4_abi.label.X86PDPTMap fl4_abi.label.X86PDPTUnmap; decide
  by_cases hm : lbl = fl4_abi.label.X86PDPTMap
  · subst hm
    have hl := hlM rfl
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, hcx, hvr, rfl, hvc⟩
    · unfold vspace.decode_table
      simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
      have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (.pdPointerTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) []) σ =
          ({(.error .truncatedMessage, σ)}, False) := pdptDecode_trunc hl _ _ _ _ _ (by simp) σ
      cases mp
      · simp only [Bool.false_eq_true, ↓reduceIte]
        unfold vspace.decode_table_map
        rw [hct, hex]
        simp only [bind_ok, error.truncated, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
      · simp only [↓reduceIte]
        rw [hex]
        simp only [bind_ok, error.truncated, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
    refine WP.spec_mono (pdpt_map_rel hHM s ar σ hP hVP hD hPP hPS (fun b hb => hPV b (let ⟨q, hq, i, hi, e⟩ := hb; ⟨q, Or.inl hq, i, hi, e⟩)) hSt hSV hR hPt hS
      ct hct hcur' hkt (hrun _ hkt) htcb hact hPO ptr asid0 va0 mp hpL hfe hpa hpc hidx hl length buf args hlen hargs ci extra
      hex hcx hvr xsl rest hvc) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, hSt', hSV', hR', hPt', hSRq, hF, hL, hK⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 ((Or.inr ∘ Or.inr) hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  by_cases hu : lbl = fl4_abi.label.X86PDPTUnmap
  · subst hu
    have hl := hlU rfl
    have hfinR := fin_iff_of hP hCR hFI hAs hcap (Or.inl ⟨trivial, rfl⟩) rfl (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.Pdpt ptr mp asid0 va0)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    refine WP.spec_mono (pdpt_unmap_rel hHU s ar σ hP hVP hD hPP hPS (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inl hq, i, hi, e⟩) (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) hPI hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt) htcb
      hact hPO ptr asid0 va0 mp hpL hfe hm0 hpc hidx hcap hl length buf (args.map UScalar.bv) ci extra excaps
      (is_final_eq s _) hfinR) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 ((Or.inr ∘ Or.inr) hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2⟩ := hlO hm hu
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, hm, hu, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePdptInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pdPointerTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) excaps) σ = _
  unfold Fl4Spec.decodePdptInvocation; dsimp only
  rw [if_neg o1, if_neg o2]; rfl


/-- **A Pdpt cap**, every label (`Map`, `Unmap`; any other l4v's `IllegalOperation`). -/
theorem decode_invocation_pdpt (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hHM : VsPdptMapHyps st A arI th P L4 L3 L2 L1 SR) (hHU : VsPdptUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0)) (hpL : ptr ∈ L3)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQ (L := L) arI Q s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  exact DecOKMQX.toMQ arI (decode_invocation_pdptX arI th hP s ar σ G hCR hFI hMO hQ (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) hHM hHU hS hVP hD hPP hPS hPV hPO hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer)

set_option maxHeartbeats 8000000 in
/-- **`DeriveSubframe` on a frame cap** (`derive_subframe_rel`; the node cap
absent: `TruncatedMessage`). -/
theorem decode_invocation_frame_dsX (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ' G', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' → MdbOKV (L.ksb s) (L.mem s') G' →
      Sched.SzKeep σ σ' → X s' a' σ')
    (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) (hS : SR s ar σ) (hPP : PtPlaced L4 L3 L2 L1)
    (hVP : VsPlaced P (L.ksb s))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageDeriveSubframe)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct)) (hrun : Fl4Spec.runnable xct.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ y nc nc' nsl rest, vspace.extra extra 0#usize = ok (some y) ∧ capAt (L.mem s) y = ok nc ∧
        CapRel nc nc' ∧ CapValid th nc ∧ excaps = (nc', nsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  subst hl
  have hCR0 := hCR
  obtain ⟨hSt, hSV, hM, hC, hI⟩ := hCR0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hkt0 : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur']; exact hkt
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.deriveSubframe
          (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pc.bv, idx)
            (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps)) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_pos (hlbl.dsr rfl)]
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  have n1 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageGetAddress := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageGetAddress; decide
  have n4 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageTestAndClearAccessed := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageTestAndClearAccessed; decide
  have n5 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageMapEPT := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageMapEPT; decide
  simp only [vspace.as_frame, bind_ok, n1, n2, n3, n4, n5, ↓reduceIte]
  rcases hext with ⟨hex, rfl⟩ | ⟨y, nc, nc', nsl, rest, hex, hcy, hnr, hnv, rfl⟩
  · unfold vspace.derive_subframe
    rw [hct, hex]
    simp only [bind_ok, error.truncated, WP.spec_ok]
    exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, decodeSub_trunc (Or.inl rfl) _ _ σ, Or.inl trivial⟩) hX0
  refine WP.spec_mono (derive_subframe_rel (L := L) (ar := arI) hH hP hPP hpc hidx s ar σ G hSt hSV hM hC hI hU hR hPt
    hS hVP hVO hPO hcap hno hFI hMO.1.1 hVC ct hct hcur' hkt hrun htcb hact length buf args hlen hargs extra hex hcy hnr hnv
    nsl rest) ?_
  rintro res (⟨e, e', h1, he, hD, h2, h2a⟩ | ⟨h1, h1a, iv, hD, σ', G', hmem, -, hSub, -, hMS⟩)
  · exact topMQX_err (⟨e, h1, h2, e', hD, Or.inl he⟩) (by rw [h2, h2a]; exact hX0)
  · have hmem' := hmem
    rw [nd_bind_one hst1] at hmem'
    have hsz : Sched.SzKeep σ σ' := fun p x n hp => by
      obtain ⟨x0, h0⟩ := Ipc.CnK.szKeep (Ipc.performDeriveSubframe_nkn iv _ _ hmem') p x n hp
      rw [Notif.stsAct_kheap, Notif.updK_kheap] at h0
      by_cases e : p = ct.bv
      · subst e; simp at h0
      · rw [Function.update_of_ne e] at h0; exact ⟨x0, h0⟩
    exact ⟨topMX_of_lift2 ⟨iv, hD, _, hst1, (.ok [], σ'),
      mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) hmem' (Set.mem_singleton _)), ⟨th, G',
      Or.inl ⟨h1, [], rfl⟩, hP, ⟨hSub.R, hSub.V, hSub.M, hSub.C, hSub.I⟩, hSub.F, hMS.okv hMO⟩,
      by rw [h1a]; exact hXs _ ar _ G' hSub.sr hSub.vs hSub.pt ⟨hSub.R, hSub.V, hSub.M, hSub.C, hSub.I⟩ hSub.F (hMS.okv hMO) hsz⟩,
      Or.inr (hQ _ _ _ hSub.sr)⟩


/-- **`DeriveSubframe` on a frame cap** (`derive_subframe_rel`; the node cap
absent: `TruncatedMessage`). -/
theorem decode_invocation_frame_ds (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) (hS : SR s ar σ) (hPP : PtPlaced L4 L3 L2 L1)
    (hVP : VsPlaced P (L.ksb s))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageDeriveSubframe)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct)) (hrun : Fl4Spec.runnable xct.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ y nc nc' nsl rest, vspace.extra extra 0#usize = ok (some y) ∧ capAt (L.mem s) y = ok nc ∧
        CapRel nc nc' ∧ CapValid th nc ∧ excaps = (nc', nsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQ (L := L) arI Q s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  exact DecOKMQX.toMQ arI (decode_invocation_frame_dsX arI th hP s ar σ G hCR hFI hU hQ (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) hH hS hPP hVP hVO hPO hR hPt lbl slbl hlbl hl length buf ct hct hcur htcb hact hkt hrun args hlen hargs hpc hidx hcap hno hMO hVC extra excaps hext blk call don fp ci buffer)

set_option maxHeartbeats 8000000 in
/-- **An ASID pool cap**, every label (`Assign`: `assign_rel`; the others
l4v's `IllegalOperation`). -/
theorem decode_invocation_asid_poolX (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hH : VsInvHyps st A th P SR) (hS : SR s ar σ) (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (ptr base : U64) (hb : base.val % 512 = 0) (hb20 : base.val < 2 ^ 20)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest ∧
        ∀ p1 a1, vc = .Pml4 p1 false a1 → p1 ≠ 0#u64)
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' →
      (∀ b, VsWrite P (L.ksb s) b → L.mem s' b ≠ L.mem s b → ∃ x p1 a1, vspace.extra extra 0#usize = ok (some x) ∧
        capAt (L.mem s) x = ok (.Pml4 p1 false a1) ∧ L.mem s' b = p1) →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      X s' a' σ')
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl args ci sl (.AsidPool ptr base) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          args ci sl (.asidPoolCap ptr.bv base.bv) excaps)) := rfl
  rw [hspec]
  by_cases hl : lbl = fl4_abi.label.X86ASIDPoolAssign
  swap
  · unfold vspace.decode
    rw [hct]; simp only [bind_ok]
    have : (lbl != fl4_abi.label.X86ASIDPoolAssign) = true := by simpa using hl
    simp only [this, ↓reduceIte, error.illegal, bind_ok, WP.spec_ok]
    exact topMQX_err (⟨_, rfl, rfl, .illegalOperation,
      decodeAssign_illegal (fun h => hl (hlA.2 h)) _ _ _ _ _ _ σ, Or.inl trivial⟩) hX0
  subst hl
  have hl' := hlA.1 rfl
  rcases hext with ⟨hex, rfl⟩ | ⟨pc, r, idx, vc, vc', rest, hpc, hidx, hex, hcx, hvr, rfl, hp0⟩
  · unfold vspace.decode
    rw [hct]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hex]; simp only [bind_ok, error.truncated, WP.spec_ok]
    exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, decodeAssign_trunc hl' _ _ _ _ _ σ, Or.inl trivial⟩) hX0
  by_cases hpm : ∃ p1 a1, vc = .Pml4 p1 false a1
  swap
  · have hbad : ∀ pb, vc' ≠ .archObjectCap (.pml4Cap pb none) := by
      intro pb h; rw [← hvr.2] at h
      cases vc <;> simp_all [absCap]
    unfold vspace.decode
    rw [hct]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hex]; simp only [bind_ok]
    rw [slot_cap_eq, hcx]; simp only [bind_ok]
    have hres : ∀ v : Bool, v = true ∨ (∀ p1 a1, vc ≠ .Pml4 p1 v a1) → True := fun _ _ => trivial
    clear hres
    cases vc
    case Ept p1 level mapped asid va =>
      exact False.elim (hNative _ hex _ _ _ _ _ hcx)
    case Pml4 p1 b a1 =>
      cases b
      · exact absurd ⟨p1, a1, rfl⟩ hpm
      · simp only [↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .invalidCapability 1, decodeAssign_bad hl' _ _ _ _ _ hbad _ _ σ,
          Or.inr ⟨1#u64, rfl, rfl⟩⟩) hX0
    all_goals
      simp only [error.invalid_cap, bind_ok, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .invalidCapability 1, decodeAssign_bad hl' _ _ _ _ _ hbad _ _ σ,
        Or.inr ⟨1#u64, rfl, rfl⟩⟩) hX0
  obtain ⟨p1, a1, rfl⟩ := hpm
  have hvc' : vc' = .archObjectCap (.pml4Cap p1.bv none) := by rw [← hvr.2]; rfl
  subst hvc'
  have hcan : Canonical p1 := by
    have h := hcx; rw [capAt_words] at h; exact (decode_encWf h)
  refine WP.spec_mono (assign_rel (L := L) (ar := arI) hH s ar σ hP hVP hD hSt hSV hR hS hkt (hrun _ hkt) ptr base hb hb20 hl' args ci sl
    rest length slot call buf extra hpc hidx hex hcx hcan (hp0 p1 a1 rfl)
    (fun ct' h => by rw [show ct' = ct from P1.eq_of_bv (h.trans hcur)]; exact htcb) hact hVO) ?_
  rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, hnf, asid, σ', hmem, hAS, hSt', hSV', hR', hSRq, hF, hL, hK, hAW⟩)
  · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
  · refine ⟨topMX_of_lift2M ⟨_, ⟨hmem, hnf⟩, _, hst1, (.ok [], σ'), ?_,
      (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR'
        (fun b hb hne => ⟨_, p1, a1, hex, hcx, hAW b hb hne⟩) h3.1 h3.2.1 h3.2.2 hK⟩)
      (crelM_after hCR hFI hMO hcx hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
    have h2 := hAS
    unfold AssignSpec at h2
    rw [nd_bind_one hst1] at h2
    exact mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [h2]; rfl) (Set.mem_singleton _))


/-- **An ASID pool cap**, every label (`Assign`: `assign_rel`; the others
l4v's `IllegalOperation`). -/
theorem decode_invocation_asid_pool (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    (hH : VsInvHyps st A th P SR) (hS : SR s ar σ) (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (ptr base : U64) (hb : base.val % 512 = 0) (hb20 : base.val < 2 ^ 20)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest ∧
        ∀ p1 a1, vc = .Pml4 p1 false a1 → p1 ≠ 0#u64)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQ (L := L) arI Q s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  exact DecOKMQX.toMQ arI (decode_invocation_asid_poolX arI th hP s ar σ G hCR hFI hMO hQ hH hS hVP hD hR hVO lbl slbl hlA length buf ct hct hcur htcb hact hrun ptr base hb hb20 extra excaps hNative hext (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) slot blk call don fp args ci sl buffer)

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap**, every label (`MakePool`: `makepool_rel`; the
others l4v's `IllegalOperation`). -/
theorem decode_invocation_asid_controlX (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s') {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK) (hS : SR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOK s σ p)
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hXs : ∀ s' a' σ' (p : U64) (th' : TypedHeap) (G' : MdbGhost), SR s' a' σ' →
      VsRel (insert p P) (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' → σ'.curThread = σ.curThread →
      (∀ L4' : Set U64, Vs.PoolsIn P L4' (L.mem s) → Vs.PoolsIn (insert p P) L4' (L.mem s')) →
      CRel th' (L.mem s') σ' G' → FinInv th' (L.mem s') σ' G' → MdbOKV (L.ksb s) (L.mem s') G' →
      th' = restrictTh th p.val (p.val + 4096) → L.ksb s' = L.ksb s →
      (∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n)) →
      MpRegion th G P L4 L3 L2 L1 (L.ksb s) p →
      (∃ x fi, x ∈ G.chains.flatten ∧ capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false ∧
        ∀ y, ¬ Mdb.Desc G.par y x) → X s' a' σ')
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, hM, hC, hI⟩ := hCR0
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl .AsidControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci sl .asidControlCap excaps)) := rfl
  rw [hspec]
  by_cases hl : lbl = fl4_abi.label.X86ASIDControlMakePool
  swap
  · unfold vspace.decode
    rw [hct]; simp only [bind_ok]
    have : (lbl != fl4_abi.label.X86ASIDControlMakePool) = true := by simpa using hl
    simp only [this, ↓reduceIte, error.illegal, bind_ok, WP.spec_ok]
    exact topMQX_err (⟨_, rfl, rfl, .illegalOperation,
      decodeMP_illegal (fun h => hl (hlM.2 h)) _ _ _ _ σ, Or.inl trivial⟩) hX0
  subst hl
  have hl' := hlM.1 rfl
  rcases hext with ⟨o0, o1, h0, h1, hn, hlen1⟩ |
    ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, hpp, hidx, hex0, hex1, hcx, hur, hcy, hrr, hrv, rfl, hRg⟩
  · unfold vspace.decode
    rw [hct]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [h0, h1]; simp only [bind_ok]
    rcases hn with rfl | rfl
    · simp only [error.truncated, bind_ok, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, decodeMP_trunc hl' _ _ _ _ hlen1 σ, Or.inl trivial⟩) hX0
    · cases o0 <;> simp only [error.truncated, bind_ok, WP.spec_ok] <;>
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, decodeMP_trunc hl' _ _ _ _ hlen1 σ, Or.inl trivial⟩) hX0
  have hd := makepool_rel (L := L) (ar := arI) hH s ar σ G hP hSt hSV hM hC hI hU hR hPt hS hVP hPP hVO hPO hPV ct hct
    hcur.symm hkt (hrun _ hkt) htcb hact hl' length buf args hlen hargs ci sl slot call extra hpp hidx hex0 hex1 hcx hur hcy hrr hrv
    ysl rest hRg hFI hMO.1.1
  refine WP.spec_mono hd ?_
  rintro res (⟨e, e', h1, he, hD, h2, h2a⟩ | ⟨h1, p, dest, ps, base, hmem, hnf, σ', th', G', hm, hnf', hP', hSt', hSV',
    hM', hC', hI', -, hR', hPt', hSRq, hF', -, -, hMSp, -, hcur', hth', hk', hscs, hRgp, hxu, hPI'⟩)
  · exact topMQX_err (⟨e, h1, h2, e', hD, he⟩) (by rw [h2, h2a]; exact hX0)
  · have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
        ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
      rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
    have hm' := hm
    rw [nd_bind_one hst1] at hm'
    exact ⟨topMX_of_lift2M ⟨_, ⟨hmem, hnf⟩, _, hst1, (.ok [], σ'),
      mem_liftE (ε := Unit) (x := ([], σ')) (mem_bind_nd (x := ((), σ')) hm' (Set.mem_singleton _)), ⟨th', G',
      Or.inl ⟨h1, [], rfl⟩, hP', ⟨hSt', hSV', hM', hC', hI'⟩, hF', hMSp.okv hMO⟩,
      hXs _ _ _ p th' G' hSRq hR' hPt' hcur' hPI' ⟨hSt', hSV', hM', hC', hI'⟩ hF' (hMSp.okv hMO) hth' hk' hscs hRgp hxu⟩, Or.inr (hQ _ _ _ hSRq)⟩

/-- **The ASID control cap**, every label (`MakePool`: `makepool_rel`; the
others l4v's `IllegalOperation`). -/
theorem decode_invocation_asid_control (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s') {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK) (hS : SR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOK s σ p)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQ (L := L) arI Q s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excaps buffer := by
  exact DecOKMQX.toMQ arI (decode_invocation_asid_controlX arI th hP s ar σ G hCR hFI hU hMO hQ hH hS hR hPt hVP hPP hVO hPO hPV lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hext (X := fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) slot blk call don fp ci sl buffer)

end

end

end Fl4Proofs.P3
