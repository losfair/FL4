/-
P3 (DESIGN.md §9), VSpace: **the VSpace producers at `FinXR`** (TopXAll's
`VsThX`): the post's CSpace relation at the producer's own typed heap.

The producers of VsTopX run at `FinXT` (`FinX` with `CRel`, `FinInv` and
`MdbOKV` at the entry's typed heap `th`, the kernel base and the SC objects
kept); with the domain schedule (`DomFrame`, VsDomF) and the empty spec
result (`OkAll NilInv`, PerformNil) they give `DecOKDMX`, and `FinXT` with
`DomRel` and the entry's apartness facts is `FinXR` at the sets with `th`
(`FinXT.toXR`): `IpcApart` from the post's `TopPlaced` with the entry's
domain-word distance (`IpcApart.of_topD`), `ScApart` from `TopPlaced`, and
`EpSchedApart` by its monotonicity (the kernel base and the SC sizes kept).
-/
import Fl4Proofs.P3.TopXAll
import Fl4Proofs.P3.VsReplyTop
import Fl4Proofs.P3.PerformNil
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`DecOKMX` with the domain schedule and an empty spec result** gives
`DecOKDMX`, for any `X₂` that `X₁` with `DomRel` implies. -/
theorem DecOKMX.toXD {X₁ X₂ : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef}
    (h : DecOKMX (L := L) arI X₁ s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hF : DomFrame (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hm : OkAll NilInv (specDec fp slbl args ci sl c excaps buffer))
    (hD0 : DomRel (L.mem s) (L.ksb s) σ)
    (hX : ∀ s' a' σ', X₁ s' a' σ' → DomRel (L.mem s') (L.ksb s') σ' → X₂ s' a' σ') :
    DecOKDMX (L := L) arI X₂ s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer := by
  refine WP.spec_mono (WP.spec_and h hF.1) ?_
  rintro res ⟨hq, hkb, hw⟩
  rcases hq with ⟨e, h1, h2, h3, hx⟩ | ⟨inv, h1, σ1, h2, y, hy, ⟨th', G', h3, h4, h5, h6, h7⟩, hx⟩
  · refine Or.inl ⟨e, h1, h2, h3, hX _ _ _ hx ?_⟩
    rw [h2]; exact hD0
  · obtain ⟨hl, hst⟩ := hF.2 inv σ1 h1 h2 y hy
    have hDy : DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 := by rw [hkb]; exact hD0.frame hw hl hst
    refine Or.inr ⟨inv, h1, σ1, h2, y, hy, ⟨th', G', ?_, h4, h5, h6, hDy, by rw [hkb]; exact h7⟩, hX _ _ _ hx hDy⟩
    rcases h3 with ⟨a, rr, b⟩ | hh
    · exact Or.inl ⟨a, by rw [b, perform_nil blk call don (h1.okAll hm) σ1 y hy rr b]⟩
    · exact Or.inr hh

/-- **`DecOKRMX` lifted** to any `X₂` that `X₁` with `DomRel` implies (the
reply's post carries `RelTopM`). -/
theorem DecOKRMX.toXR {X₁ X₂ : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : DecOKRMX (L := L) arI X₁ s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hD0 : DomRel (L.mem s) (L.ksb s) σ)
    (hX : ∀ s' a' σ', X₁ s' a' σ' → DomRel (L.mem s') (L.ksb s') σ' → X₂ s' a' σ') :
    DecOKRMX (L := L) arI X₂ s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  refine WP.spec_mono h ?_
  rintro res (⟨e, h1, h2, h3, hx⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩)
  · refine Or.inl ⟨e, h1, h2, h3, hX _ _ _ hx ?_⟩
    rw [h2]; exact hD0
  · have hD : DomRel (L.mem res.2.1) (L.ksb res.2.1) z.2 := by
      obtain ⟨th', G', -, -, -, hD, -⟩ := h6; exact hD
    exact Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, hX _ _ _ h7 hD⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`IpcApart` from `TopPlaced`** and the IPC words' distance from the
domain words (a fact of the sets and the kernel base alone). -/
theorem IpcApart.of_topD {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hP : Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    IpcApart th N T E R B (L.ksb s) c := by
  refine ⟨fun a ha x hx ⟨h1, h2⟩ => ?_, fun a h1 h2 x hx ⟨h3, h4⟩ =>
    hP.disj a (Or.inl ⟨h1, h2⟩) (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h3 h4), hdom,
    fun a h1 h2 x hx ⟨h3, h4⟩ =>
    hP.disj a (Or.inr (Or.inl ⟨h1, h2⟩)) (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h3 h4),
    by have := hP.vs.ksb_fit; omega, hP.vs.ksb_al⟩
  refine hP.disj a ?_ (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h1 h2)
  rcases ha with h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · obtain ⟨n, hn, h1, h2⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- The sets of `FinXR` for a typed heap. -/
def xsetsOf (th : TypedHeap) (G : MdbGhost) (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (c : U64) : XSets :=
  ⟨th, G, P, L4, L3, L2, L1, N, T, C, E, R, B, c⟩

/-- **`FinXT` with `DomRel` is `FinXR`** at the sets with its typed heap, from
the entry's endpoint-scheduler apartness and the IPC words' distance from
the domain words. -/
theorem FinXT.toXR {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {AR : A → Fl4Spec.Cr3 → Prop} (G0 : MdbGhost)
    {s0 : S} {σ0 : Fl4Spec.State Unit} (hEA : EpSchedApart st T C E R B c s0 σ0)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s0).val ∨ (L.ksb s0).val + 256 ≤ a.val)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s0) σ0 s a σ)
    (hD : DomRel (L.mem s) (L.ksb s) σ) :
    FinXR (L := L) AR (xsetsOf th G0 P L4 L3 L2 L1 N T C E R B c) s a σ := by
  obtain ⟨hF, ⟨G, hCR, hFI, hMO⟩, hk, hz⟩ := h
  refine ⟨hF, ⟨G, hF.1.2.pl, hCR, hFI, hD, hMO, IpcApart.of_topD hF.1.2 (by rw [hk]; exact hdom),
    ScApart.of_top hF.1.2⟩, hEA.mono hk hz⟩

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A page_table cap at `FinXR`** (`VsThX`): `decode_invocation_page_table_capX`
at `FinXT`, its `DomFrame` and empty result. -/
theorem decode_invocation_page_table_thX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
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
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c)) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp buf extra slbl (args.map UScalar.bv) ci
      (pc.bv, idx) excaps buffer ct :=
  Or.inl (DecOKMX.toXD arI (decode_invocation_page_table_capX arI th s ar σ G hCR hFI hMO hA hS hPI hCur hR hPt hVC lbl
      slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap extra excaps hext blk call
      don fp ci buffer hxs)
    (domFrame_page_table arI th s ar σ G hCR hFI hMO hA hS hPI hR hPt hVC lbl slbl hlM hlU hlO length buf ct hct hcur
      htcb hact hrun args hlen hargs hpc hidx hcap extra excaps hext blk call don fp ci buffer hxs)
    (okAll_specDec_pageTable fp slbl (args.map UScalar.bv) ci (pc.bv, idx) ptr mp asid0 va0 excaps buffer) hDR
    (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))

set_option maxHeartbeats 8000000 in
/-- **A page_directory cap at `FinXR`** (`VsThX`): `decode_invocation_page_directory_capX`
at `FinXT`, its `DomFrame` and empty result. -/
theorem decode_invocation_page_directory_thX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
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
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c)) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp buf extra slbl (args.map UScalar.bv) ci
      (pc.bv, idx) excaps buffer ct :=
  Or.inl (DecOKMX.toXD arI (decode_invocation_page_directory_capX arI th s ar σ G hCR hFI hMO hA hS hPI hCur hR hPt hVC lbl
      slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap extra excaps hext blk call
      don fp ci buffer hxs)
    (domFrame_page_directory arI th s ar σ G hCR hFI hMO hA hS hPI hR hPt hVC lbl slbl hlM hlU hlO length buf ct hct hcur
      htcb hact hrun args hlen hargs hpc hidx hcap extra excaps hext blk call don fp ci buffer hxs)
    (okAll_specDec_pageDirectory fp slbl (args.map UScalar.bv) ci (pc.bv, idx) ptr mp asid0 va0 excaps buffer) hDR
    (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))

set_option maxHeartbeats 8000000 in
/-- **A pdpt cap at `FinXR`** (`VsThX`): `decode_invocation_pdpt_capX`
at `FinXT`, its `DomFrame` and empty result. -/
theorem decode_invocation_pdpt_thX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
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
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c)) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp buf extra slbl (args.map UScalar.bv) ci
      (pc.bv, idx) excaps buffer ct :=
  Or.inl (DecOKMX.toXD arI (decode_invocation_pdpt_capX arI th s ar σ G hCR hFI hMO hA hS hPI hCur hR hPt hVC lbl
      slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap extra excaps hext blk call
      don fp ci buffer hxs)
    (domFrame_pdpt arI th s ar σ G hCR hFI hMO hA hS hPI hR hPt hVC lbl slbl hlM hlU hlO length buf ct hct hcur
      htcb hact hrun args hlen hargs hpc hidx hcap extra excaps hext blk call don fp ci buffer hxs)
    (okAll_specDec_pdpt fp slbl (args.map UScalar.bv) ci (pc.bv, idx) ptr mp asid0 va0 excaps buffer) hDR
    (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))


set_option maxHeartbeats 8000000 in
/-- **An ASID pool cap at `FinXR`** (`VsThX`). -/
theorem decode_invocation_asid_pool_thX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPI : PoolsIn P L4 (L.mem s))
    (hCur : CurOK st th s σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (ptr base : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hsl : IsSlot th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c)) s ar σ lbl length
      slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps buffer ct :=
  Or.inl (DecOKMX.toXD arI (decode_invocation_asid_pool_capX arI th s ar σ G hCR hFI hMO hS hR hPt hPI hCur hVC lbl
      slbl hlA length buf ct hct hcur htcb hact hrun ptr base extra excaps hNative hext slot blk call don fp args ci
      sl buffer hsl hcap)
    (domFrame_asid_pool arI th s ar σ G hCR hFI hMO hS hR hVC lbl slbl hlA length buf ct hct hcur htcb hact hrun
      ptr base extra excaps hNative hext slot blk call don fp args ci sl buffer hsl hcap)
    (okAll_specDec_asidPool fp slbl args ci sl ptr base excaps buffer) hDR
    (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of a frame cap's decode**, its label neither
`GetAddress` nor `TestAndClearAccessed` (from `decode_invocation_frame_capD`). -/
theorem domFrame_frame [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hlga : lbl ≠ fl4_abi.label.X86PageGetAddress) (hltac : lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed) :
    DomFrame (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don
      fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20 := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4, fun p' a' e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (hxs x h1) h2 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨hv1, -, hv3⟩ := hv
      exact ⟨hv1, (hv3 rfl).1, (hv3 rfl).2⟩
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hextS : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ y nc nc' nsl rest, vspace.extra extra 0#usize = ok (some y) ∧ capAt (L.mem s) y = ok nc ∧
        CapRel nc nc' ∧ CapValid th nc ∧ excaps = (nc', nsl) :: rest := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · have hv := Vs.capValid_slot hCR.2.1 (hxs x h1)
      rw [capAt_capV] at h2; cases eq_of_ok_eq h2
      exact Or.inr ⟨x, _, vc', xsl, rest, h1, capAt_capV _ _, h3, hv, h4⟩
  have hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKMQ (L := L) arI (fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) s ar σ lbl length (cslotAddr (pc.bv, idx))
        (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
        buffer := fun hl => by
    have := decode_invocation_frame_ds (L := L) arI th hS.2.pl s ar σ G hCR hFI hU
      (SR := FootSRc st th (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s))
      (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2.1)
      (VsSubHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl
        (Vs.vsSubHyps_top (st := st) (L := L) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1)
          (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR)))
      ⟨hS, P1.WritesIn.refl _ _, fun t ht => by
        have e := P1.eq_of_bv (ht.trans hcur); subst e; exact htcb, hact⟩
      hS.2.pt hS.2.vs hS.2.vo hS.2.po hR hPt lbl slbl hlbl hl length buf ct hct hcur htcb hact hkt (hrun _ hkt)
      args hlen hargs (pc := pc) (r := r) (idx := idx) hpc hidx (p := p) (sz := sz) (rt := rt) (asid := asid)
      (va := va) (d := d) (m := m) hcap hno hMO hVC extra excaps hextS blk call don fp ci buffer
    exact this
  have h := decode_invocation_frame arI th hS.2.pl s ar σ G hCR hFI hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s))
    (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2)
    (VsFrameHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsFrameHyps_top hA))
    (VsFrameHypsL.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsFrameHypsL_top hA))
    (VsFrameUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsFrameUnmapHyps_top hA)) ⟨hS, P1.WritesIn.refl _ _⟩
    hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlbl length buf ct hct hcur htcb hact hrun
    args hlen hargs hpc hidx hcap hok.1 (fun e => by subst e; exact hok.2) (fun e => by subst e; exact hok.2)
    (fun e => by subst e; exact hok.2) hAl extra excaps hext' blk call don fp ci buffer
    (fun h => absurd h hlga) (fun h => absurd h hltac) hDS
  rcases h with ⟨-, -, h⟩ | ⟨e, -⟩
  · exact ⟨WP.spec_mono h fun res hr => dom_of_foot hS hr.2, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  · exact absurd e (by rintro (e | e) <;> contradiction)


set_option maxHeartbeats 8000000 in
/-- **A frame cap at `FinXR`** (`VsThX`), every label: `GetAddress` and
`TestAndClearAccessed` reply in the decode (`DecOKRMX`). `hlGA`: the ABI's
`GetAddress` label is the only one the spec reads as `x64PageGetAddress`. -/
theorem decode_invocation_frame_thX [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hU : UtInv (L.mem s) G) (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hlGA : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress → lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hDom : DomRel (L.mem s) (L.ksb s) σ)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c)) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv)
      ci (pc.bv, idx) excaps buffer ct := by
  rcases decode_invocation_frame_capXR arI th s ar σ G hCR hFI hU hMO hA hS hPI hCur hR hPt hVC lbl slbl hlbl length
      buf ct hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hAl hno extra excaps hext hxs blk call don fp ci
      buffer hDom with ⟨hga, htac, h⟩ | h
  · exact Or.inl (DecOKMX.toXD arI h
      (domFrame_frame arI th s ar σ G hCR hFI hU hMO hA hS hPI hR hPt hVC lbl slbl hlbl length buf ct hct hcur htcb
        hact hrun args hlen hargs hpc hidx hcap hAl hno extra excaps hext hxs blk call don fp ci buffer hga htac)
      (okAll_specDec_frameCap fp slbl (args.map UScalar.bv) ci (pc.bv, idx) p sz rt d m false asid va excaps buffer
        (fun e => htac (hlbl.tac e)) (fun e => hga (hlGA e))) hDom
      (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))
  · exact Or.inr (DecOKRMX.toXR arI h hDom (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of a PML4 cap's decode** (from `decode_invocation_pml4D`). -/
theorem domFrame_pml4 (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hinv : ∀ (a : A) (asid : U64), ∃ a', arI.invalidate_asid a asid = ok a')
    (p asid : U64) (mp : Bool) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DomFrame (L := L) arI s ar σ lbl length slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  refine ⟨?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  by_cases hl : lbl = fl4_abi.label.X86PML4Flush
  swap
  · rw [if_neg hl]
    simp only [error.illegal, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => trivial⟩
  rw [if_pos hl]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => trivial⟩
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (set_thread_state_frame s ct sched.TS_RESTART (Vs.stA_al hP htcb) hact.1)
    (set_thread_state_cpu s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨hF, hk, hc⟩
  obtain ⟨a', ha'⟩ := hinv ar asid
  rw [ha']; simp only [bind_ok, WP.spec_ok]
  refine dom_of_foot hS (Or.inr ⟨hk, hc, fun b hb hn => hF b hb (fun e => hn ?_) (fun e => hn ?_)⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ct, htcb, UScalar.eq_of_val_eq e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq e)))))


set_option maxHeartbeats 8000000 in
/-- **A PML4 cap at `FinXR`** (`VsThX`). `hinv`: the platform's ASID
invalidation always succeeds. -/
theorem decode_invocation_pml4_thX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (hinv : ∀ (a : A) (asid : U64), ∃ a', arI.invalidate_asid a asid = ok a')
    (p asid : U64) (mp : Bool) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c)) s ar σ lbl length
      slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl excaps buffer ct :=
  Or.inl (DecOKMX.toXD arI (decode_invocation_pml4_capX arI th s ar σ G hCR hFI hMO hA hS hPI hCur hR hPt lbl slbl
      hlbl ct hct hcur htcb hact hrun p asid mp length slot buf blk call don fp extra args ci sl excaps buffer)
    (domFrame_pml4 arI th hS.2.pl s ar σ G hCR hFI hMO hS lbl slbl hlbl ct hct hcur htcb hact hinv p asid mp length
      slot buf blk call don fp extra args ci sl excaps buffer)
    (okAll_specDec_pml4 fp slbl args ci sl p mp asid excaps buffer) hDR
    (fun _ _ _ hx hd => FinXT.toXR G hEA hdom hx hd))

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of the ASID control cap's decode** (from
`decode_invocation_asid_control_capD`). -/
theorem domFrame_asid_control (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
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
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKTop (L := L) N T C E R B c s σ p)
    (hUK : Vs.UtKsOut (L.ksb s) (L.mem s) G)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DomFrame (L := L) arI s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl (args.map UScalar.bv) ci
      sl excaps buffer := by
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hextK : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
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
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKF (RegOKTop (L := L) N T C E R B c) (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568)) s σ p := by
    rcases hext with h | ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hRg⟩
    · exact Or.inl h
    · exact Or.inr ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
        fun p fi e hc => ⟨(hRg p fi e hc).1, (hRg p fi e hc).2, fun b hb1 hb2 => Or.inr (by
          have hk := hUK.pool hCR.2.2.1 (AbsSlot.isSlot (th := th) (sl := (pp.bv, idx))
            ⟨pp, rfl, Or.inl (by simpa [h2] using h1)⟩) (by rw [h5, e])
          rcases hk with h | h <;> omega)⟩⟩
  have h := decode_invocation_asid_control arI th hS.2.pl s ar σ G hCR hFI hU hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568)))
    (Q := fun s' => P1.WritesIn st s s' (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568))) (fun _ _ _ h => h.2)
    (VsMpHyps.foot (s0 := s) (fun _ h => Or.inl h.toW) hS.2.pl (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))) vsMpHyps_top) ⟨hS, P1.WritesIn.refl _ _⟩ hR hPt hS.2.vs hS.2.pt
    hS.2.vo hS.2.po hS.2.pv lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hextK slot
    blk call don fp ci sl buffer
  refine ⟨WP.spec_mono h fun res hr => ?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  rcases hr.2 with e | hw
  · rw [e]; exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hw.1, fun o ho => hw.2.2 _ ?_ ?_⟩
    · have := hS.2.vs.ksb_fit
      exact ksW_al (by omega) hS.2.vs.ksb_al (domOffs_lt' ho).1 (domOffs_lt' ho).2
    · rintro (h | h)
      · exact dom_not_foot hS ho h
      · apply h
        have := hS.2.vs.ksb_fit
        have hb : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by have := (domOffs_lt' ho).1; omega)
        have := (domOffs_lt' ho).1
        rw [hb]; omega


set_option maxHeartbeats 8000000 in
/-- **The ASID control cap at `FinXR`** (`VsThX`), at the sets of each
outcome (`MakePool` re-picks the typed heap and the pool set). -/
theorem decode_invocation_asid_control_thX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPI : PoolsIn P L4 (L.mem s))
    (hCur : CurOK st th s σ)
    (hMP : MpPlacedHyp st th P L4 L3 L2 L1 N T C E R B c AR s σ G)
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
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKTop (L := L) N T C E R B c s σ p)
    (hUK : Vs.UtKsOut (L.ksb s) (L.mem s) G)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (fun s' a' σ' => ∃ Z, FinXR (L := L) AR Z s' a' σ') s ar σ lbl length slot .AsidControl blk
      call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct :=
  Or.inl (DecOKMX.toXD arI (decode_invocation_asid_control_capX arI th s ar σ G hCR hFI hU hMO hS hR hPt hPI hCur
      hMP lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hext slot blk call don fp ci
      sl buffer)
    (domFrame_asid_control arI th s ar σ G hCR hFI hU hMO hS hR hPt lbl slbl hlM length buf ct hct hcur htcb hact hrun
      args hlen hargs extra excaps hext hUK slot blk call don fp ci sl buffer)
    (okAll_specDec_asidControl fp slbl (args.map UScalar.bv) ci sl excaps buffer) hDR
    (fun _ _ _ ⟨th', P', hx⟩ hd => ⟨_, FinXT.toXR G hEA hdom hx hd⟩))


/-- A producer at fixed sets gives it at some sets (the pointwise shape the
ASID control cap needs). -/
theorem XCap.exZ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI (FinXR (L := L) AR Z) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl
      excaps buffer ct) :
    XCap (L := L) arI (fun s' a' σ' => ∃ Z, FinXR (L := L) AR Z s' a' σ') s ar σ lbl length slot c blk call don fp
      buf extra slbl args ci sl excaps buffer ct :=
  h.imp arI fun _ _ _ hx => ⟨Z, hx⟩

end

end

end Fl4Proofs.P3
