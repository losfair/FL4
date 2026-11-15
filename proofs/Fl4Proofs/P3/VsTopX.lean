/-
P3 (DESIGN.md §9), VSpace: **the VSpace invariants after the decode tops**
(`DecOKMX` with `FinX`: `TopSR`, `VsRel`, `PtRel`, `PoolsIn`, `CurOK`), so they
compose across entries.

The decode wrappers (VsDecFrame's `…X`) carry an extra relation `X` on the
outcome inside `TopPostMX`; here they run at `SR := FootSR TopSR s
(VsFootW0 …)`: the writes since the entry are in the VSpace footprint
without the ASID-table and pool words (`VsFootW0`; the hypothesis
structures through `.foot`). Then after the outcome:
* `TopSR`, `VsRel`, `PtRel`: from the relational posts;
* `PoolsIn`: the pool words are not written (`foot0_not_vs`,
  `PoolsIn.of_writes`);
* `CurOK`: the current thread kept (`KFoot`), its vtable cap placed by the
  MDB's VSpace invariant (`MdbOKV`'s `VsMdbInv`, `CurOK.of_inv`).

Covered (`…_capX`): the page-table, page-directory and PDPT caps (every
label); the frame caps, every label but `GetAddress` and
`TestAndClearAccessed` (their posts are the `GetAddrHyp` / `TacHyp`
hypotheses' `RelTopM`); the PML4 caps (`Flush`, any other); the ASID pool
caps (`Assign`: the pool word written is the extra cap's PML4, in `L4` by
the cap invariant; `PtRel` carried through `VsInvHyps.ptTop`); the ASID
control cap (`MakePool`: `FinXE`, the invariants at the new typed heap and
the pool set grown by the new pool; the re-indexing of `TopSR` is the named
hypothesis `MpPlacedHyp`).
-/
import Fl4Proofs.P3.VsDomF
import Fl4Proofs.P3.VsFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
  {A : Type} {AR : A → Fl4Spec.Cr3 → Prop}

/-- **The VSpace footprint without the pool words misses the pool words.** -/
theorem foot0_not_vs {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {b : U64}
    (hb : VsFootW0 st th L4 L3 L2 L1 s b) : ¬ VsWrite P (L.ksb s) b := by
  intro hv
  have hO := hS.2.vo b hv
  rcases hb with ⟨x, hx, e⟩ | ⟨x, k, hx, hk, e⟩ | hpt | ⟨t, ht, e⟩ | e
  · exact hS.2.sd b hv ⟨x, hx, e⟩
  · obtain ⟨o, kk, hkk, h1, h2, -⟩ := slot_in_object hS.2.pl hx
    have hw := slot_word_val hS.2.pl hx hk
    have := hk.lt
    exact hO.2 o kk hkk ⟨by rw [e, hw]; omega, by rw [e, hw]; omega⟩
  · exact hS.2.pv b hpt hv
  · have hf := hS.2.pl.fits t _ ht
    have hsv : (stA t).val = t.val + 3328 := by
      rw [stA_eq]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      simp [objSize] at hf; omega
    refine hO.2 t _ ht ⟨by rw [e, hsv]; omega, ?_⟩
    rw [e, hsv]; simp [objSize]
  · obtain ⟨Q, R', hc, -⟩ := hS.1.1.lists
    have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
    have hsa := P1.nodeAt_val (hc.cur ▸ hc.node) hoff
    have hOO : OObj st N T C E R B c s σ b := by
      left; rw [e, hsa, hc.cur]; constructor <;> omega
    exact hS.2.disj b hOO (vsWrite_vobj hS.2.vs hv)

/-- **`CurOK` from the MDB's VSpace invariant** and the current thread kept. -/
theorem CurOK.of_inv' {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {k : U64}
    (hC : CurOK st th s σ) (hc : σ'.curThread = σ.curThread) (hM : MdbLinks th (L.mem s') G)
    (hV : VsMdbInv k (L.mem s') G) : CurOK st th s' σ' := by
  obtain ⟨t, h1, h2, -⟩ := hC
  obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hV
  refine ⟨t, h1.trans hc.symm, h2, fun p asid h => ?_⟩
  have hv := hVC.at hM ⟨t, 1, Or.inr ⟨h2, by decide⟩, rfl⟩ h (by simp)
  simp only [VCapOK] at hv
  exact (hv.2.2 trivial).1

theorem CurOK.of_inv {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {k : U64}
    (hC : CurOK st th s σ) (hK : KFoot σ σ') (hM : MdbLinks th (L.mem s') G) (hV : VsMdbInv k (L.mem s') G) :
    CurOK st th s' σ' :=
  CurOK.of_inv' hC hK.2.2.2 hM hV

/-- `VsSubHyps` with the current thread kept. -/
theorem VsSubHyps.cur {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsSubHyps st A P L4 L3 L2 L1 th SR)
    (c0 : Fl4Spec.ObjRef) : VsSubHyps st A P L4 L3 L2 L1 th (fun s a σ => SR s a σ ∧ σ.curThread = c0) where
  restart := fun s a σ ct x h hR hPt hcur hk hrun => WP.spec_mono (hH.restart s a σ ct x h.1 hR hPt hcur hk hrun)
    fun _ ⟨a1, a2, a3, a4⟩ => ⟨a1, a2, ⟨a3, (stsAct_updK_cur _ _ _ _).trans h.2⟩, a4⟩
  insStable := fun s s' a σ σ' h hw hI => ⟨hH.insStable s s' a σ σ' h.1 hw hI, (insStep_cur hI).trans h.2⟩

/-- `FinX` at the entry. -/
theorem vs_x0 {s : S} {a : A} {σ : Fl4Spec.State Unit} (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPI : PoolsIn P L4 (L.mem s))
    (hCur : CurOK st th s σ) : FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ :=
  ⟨hS, hR, hPt, hPI, hCur⟩

/-- **`FinX` after an outcome** of the footprint without the pool words. -/
theorem vs_x_after {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {k : U64}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hSR : FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW0 st th L4 L3 L2 L1 s) s' a' σ')
    (hR' : VsRel P (L.mem s') (L.ksb s') σ') (hPt' : PtRel L4 L3 L2 L1 (L.mem s') σ')
    (hCR' : CRel th (L.mem s') σ' G) (hMO' : MdbOKV k (L.mem s') G) (hK : KFoot σ σ') :
    FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a' σ' :=
  ⟨hSR.1, hR', hPt', Vs.PoolsIn.of_writes hPI hSR.2 hS.2.vs (fun _ hb => foot0_not_vs hS hb),
    CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩

variable (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A page-table cap with the composite relation** (`decode_invocation_page_table`; the placement from `TopPlaced`). -/
theorem decode_invocation_page_table_topX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
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
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_page_tableX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vs_x0 hS hR hPt hPI hCur) (fun _ _ _ hSR hR' hPt' hCR' hMO' hK => vs_x_after hS hPI hCur hSR hR' hPt' hCR' hMO' hK) ((vsPtMapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ((vsPtUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer) (fun _ _ _ h => h)

set_option maxHeartbeats 8000000 in
/-- **A page-table cap at `TopSR` with `VsCapsIn`** (`decode_invocation_page_table_top`; the table's placement and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_page_table_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
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
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
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
  exact decode_invocation_page_table_topX arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hCur := hCur) (hR := hR) (hPt := hPt) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (hpL := hok.1) (hpa := hok.2.1) (hm0 := hok.2.2) (extra := extra) (excaps := excaps) (hext := hext') (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer)

set_option maxHeartbeats 8000000 in
/-- **A page-directory cap with the composite relation** (`decode_invocation_page_directory`; the placement from `TopPlaced`). -/
theorem decode_invocation_page_directory_topX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
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
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_page_directoryX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vs_x0 hS hR hPt hPI hCur) (fun _ _ _ hSR hR' hPt' hCR' hMO' hK => vs_x_after hS hPI hCur hSR hR' hPt' hCR' hMO' hK) ((vsPdMapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ((vsPdUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer) (fun _ _ _ h => h)

set_option maxHeartbeats 8000000 in
/-- **A page-directory cap at `TopSR` with `VsCapsIn`** (`decode_invocation_page_directory_top`; the table's placement and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_page_directory_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
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
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
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
  exact decode_invocation_page_directory_topX arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hCur := hCur) (hR := hR) (hPt := hPt) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (hpL := hok.1) (hpa := hok.2.1) (hm0 := hok.2.2) (extra := extra) (excaps := excaps) (hext := hext') (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer)

set_option maxHeartbeats 8000000 in
/-- **A PDPT cap with the composite relation** (`decode_invocation_pdpt`; the placement from `TopPlaced`). -/
theorem decode_invocation_pdpt_topX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
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
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_pdptX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vs_x0 hS hR hPt hPI hCur) (fun _ _ _ hSR hR' hPt' hCR' hMO' hK => vs_x_after hS hPI hCur hSR hR' hPt' hCR' hMO' hK) ((vsPdptMapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ((vsPdptUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer) (fun _ _ _ h => h)

set_option maxHeartbeats 8000000 in
/-- **A PDPT cap at `TopSR` with `VsCapsIn`** (`decode_invocation_pdpt_top`; the table's placement and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_pdpt_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
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
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
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
  exact decode_invocation_pdpt_topX arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hCur := hCur) (hR := hR) (hPt := hPt) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (hpL := hok.1) (hpa := hok.2.1) (hm0 := hok.2.2) (extra := extra) (excaps := excaps) (hext := hext') (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer)

set_option maxHeartbeats 8000000 in
/-- **A frame cap's `Map` and `Unmap` `DeriveSubframe` (and any label but `GetAddress`,
`TestAndClearAccessed`) at `TopSR` with `VsCapsIn`**, `FinX`
after. -/
theorem decode_invocation_frame_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hU : UtInv (L.mem s) G) (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hnGA : lbl ≠ fl4_abi.label.X86PageGetAddress) (hnTAC : lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed)
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
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
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
  have hX0 := vs_x0 hS hR hPt hPI hCur
  have hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKMQX (L := L) arI (fun _ => True) (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR))
        s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := fun hl => by
    have hext'' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
        ∃ y nc nc' nsl rest, vspace.extra extra 0#usize = ok (some y) ∧ capAt (L.mem s) y = ok nc ∧
          CapRel nc nc' ∧ CapValid th nc ∧ excaps = (nc', nsl) :: rest := by
      rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
      · exact Or.inl h
      · have hv := Vs.capValid_slot hCR.2.1 (hxs x h1)
        rw [capAt_capV] at h2; cases eq_of_ok_eq h2
        exact Or.inr ⟨x, _, vc', xsl, rest, h1, capAt_capV _ _, h3, hv, h4⟩
    obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
    have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
    exact decode_invocation_frame_dsX (L := L) arI th hS.2.pl s ar σ G hCR hFI hU (fun _ _ _ _ => trivial) hX0
      (fun _ _ _ G' hSR hR' hPt' hCR' hMO' => ⟨hSR.1.1, hR', hPt',
        Vs.PoolsIn.of_writes hPI hSR.2.1 hS.2.vs (fun _ hb => foot0_not_vs hS hb),
        CurOK.of_inv' hCur hSR.1.2 hCR'.2.2.1 hMO'.2.2⟩)
      (Vs.VsSubHyps.foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl
        (VsSubHyps.cur (Vs.vsSubHyps_top (st := st) (L := L) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2)
          (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR)) σ.curThread))
      ⟨⟨hS, rfl⟩, P1.WritesIn.refl _ _, fun t ht => by rw [P1.eq_of_bv (ht.trans hcur)]; exact htcb, hact⟩
      hS.2.pt hS.2.vs hS.2.vo hS.2.po hR hPt lbl slbl hlbl hl length buf ct hct hcur htcb hact hkt
      (hrun _ hkt) args hlen hargs (pc := pc) (r := r) (idx := idx) hpc hidx (p := p) (sz := sz) (rt := rt)
      (asid := asid) (va := va) (d := d) (m := m) hcap hno hMO hVC extra excaps hext'' blk call don fp ci buffer
  have h := decode_invocation_frameX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial)
    hX0
    (fun _ _ _ hSR hR' hPt' hCR' hMO' hK => vs_x_after hS hPI hCur hSR hR' hPt' hCR' hMO' hK)
    ((vsFrameHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl)
    ((vsFrameHypsL_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl)
    ((vsFrameUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl)
    ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlbl length buf ct
    hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hok.1 (fun e => by subst e; exact hok.2)
    (fun e => by subst e; exact hok.2) (fun e => by subst e; exact hok.2) hAl extra excaps hext' blk call don fp ci
    buffer (fun h => absurd h hnGA) (fun h => absurd h hnTAC) hDS
  rcases h with ⟨-, -, h⟩ | ⟨h, -⟩
  · exact DecOKMQX.toX arI h (fun _ _ _ h => h)
  · rcases h with h | h
    · exact absurd h hnGA
    · exact absurd h hnTAC

set_option maxHeartbeats 8000000 in
/-- **A PML4 cap at `TopSR`** (`Flush`, any other label), `FinX` after. -/
theorem decode_invocation_pml4_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (p asid : U64) (mp : Bool) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length
      slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl excaps buffer := by
  have hX0 := vs_x0 hS hR hPt hPI hCur
  unfold DecOKMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl args ci sl (.Pml4 p mp asid) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
          (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps) := rfl
  rw [hspec]
  by_cases hl : lbl = fl4_abi.label.X86PML4Flush
  swap
  · rw [if_neg hl]
    have hd : Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
        (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps =
        Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args ci sl
          (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps) := by
      unfold Fl4Spec.fl4ArchDecodeInvocation; dsimp only; rw [if_neg (fun h => hl (hlbl.1 h))]
    rw [hd]
    simp only [error.illegal, bind_ok, WP.spec_ok]
    refine (topMQX_err (Q := fun _ => True) ?_ hX0).1
    exact ⟨_, rfl, rfl, .illegalOperation, rfl, Or.inl trivial⟩
  rw [if_pos hl]
  have hd : Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl
      (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.pml4Flush
        (Fl4Spec.decodePml4Flush (Z := Unit) (.pml4Cap p.bv (if mp then some asid.bv else none))) := by
    unfold Fl4Spec.fl4ArchDecodeInvocation; dsimp only; rw [if_pos (hlbl.2 hl)]
  rw [hd]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    refine (topMQX_err (Q := fun _ => True) ?_ hX0).1
    exact ⟨_, rfl, rfl, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  simp only [↓reduceIte]
  obtain ⟨hSt, hSV, hM, hC, hI⟩ := hCR
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  refine WP.spec_bind (WP.spec_and (set_thread_state_slots th hS.2.pl s ct sched.TS_RESTART htcb hact)
    (restart_full (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) s ar σ ct xct hSt hSV hR hS hcur.symm hkt0 htcb hact
      (hrun _ hkt))) ?_
  rintro s1 ⟨hSS, hSt1, hSV1, hR1, hPt1, hS1, hk1, hPI1⟩
  refine WP.spec_bind (flushAllH_top hA s1 ar _ p.bv asid hS1) ?_
  rintro a' ⟨σ', hy, hS'⟩
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hy
  simp only [WP.spec_ok]
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv
  have hK1 : KFoot σ σ1 := KFoot.sts hkt0 _
  have hK : KFoot σ { σ1 with machineState := ms } := hK1.trans (KFoot.ms _ ms)
  have h0 : (([] : List Fl4Spec.Data), { σ1 with machineState := ms }) ∈
      ((do Fl4Spec.flushAll (Z := Unit) p.bv asid.bv; pure [] : Fl4Spec.SMonad Unit (List Fl4Spec.Data)) σ1).1 :=
    mem_bind_nd (x := ((), { σ1 with machineState := ms })) hy (Set.mem_singleton _)
  have hmem : ((.ok [], { σ1 with machineState := ms }) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeArchObject (.pml4Flush (.flush p.bv asid.bv)))).run σ1).1 :=
    mem_liftE (ε := Unit) h0
  have hCR' : CRel th (L.mem s1) { σ1 with machineState := ms } G :=
    ⟨Vs.StateRel.ms hSt1 ms, hSV1, hM.of_same hSS, hC.of_same hSS hK.1 hK.2.1, MdbInv.of_same hM hI hSS⟩
  have hMO' : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hM hSS hMO
  refine topMX_of_lift2 ⟨.flush p.bv asid.bv, rfl, σ1, hst1, _, hmem, ⟨th, G,
    Or.inl ⟨rfl, [], rfl⟩, hS.2.pl, hCR', hFI.of_same hM hSS (KFoot.ksub hK), hMO'⟩, ?_⟩
  refine ⟨hS', hR1.ms ms, (hPt1 hPt).same_heap rfl, ?_, CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩
  exact hPI1 hPI

/-! ## `Assign` -/

omit arI in
/-- A page-table word is neither a TCB's state word nor the core's
scheduler-action word. -/
theorem ptw_not_sts {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {ct b : U64} (htcb : th ct = some .tcb)
    (hb : PtWAll L4 L3 L2 L1 b) :
    b.val ≠ (stA ct).val ∧ b.val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val := by
  constructor
  · intro e
    have hO := hS.2.po b hb
    have hf := hS.2.pl.fits ct _ htcb
    have hsv : (stA ct).val = ct.val + 3328 := by
      rw [stA_eq]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      simp [objSize] at hf; omega
    refine hO.2 ct _ htcb ⟨by rw [e, hsv]; omega, ?_⟩
    rw [e, hsv]; simp [objSize]
  · intro e
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    have hV := table_vobj (th := th) (P := P) hS.2.pt hq hi (L.ksb s)
    obtain ⟨Q, R', hc, -⟩ := hS.1.1.lists
    have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
    have hsa := P1.nodeAt_val (hc.cur ▸ hc.node) hoff
    have hOO : OObj st N T C E R B c s σ (peA q i) := by
      left; rw [e, hsa, hc.cur]; constructor <;> omega
    exact hS.2.disj _ hOO hV

omit arI in
/-- `VsInvHyps` with `PtRel` carried (the ASID invocations write no
page-table word and change no table). -/
theorem VsInvHyps.ptTop {s0 : S} {W : U64 → Prop}
    (hH : VsInvHyps st A th P (FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W)) :
    VsInvHyps st A th P (fun s a σ => FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s a σ ∧
      PtRel L4 L3 L2 L1 (L.mem s) σ) where
  curT := fun s a σ h => hH.curT s a σ h.1
  restart := fun s a σ ct x h1 h2 h3 h hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h.1 hcur hk htcb hact hrun)
      (set_thread_state_frame s ct sched.TS_RESTART (stA_al h.1.1.2.pl htcb) hact.1))
      fun s' ⟨⟨a1, a2, a3, a4, a5⟩, hF⟩ => ⟨a1, a2, a3, ⟨a4, h.2.frame
        (fun b hb => hF b (PtWAll.aligned h.1.1.2.pt hb) (ptw_not_sts h.1.1 htcb hb).1 (ptw_not_sts h.1.1 htcb hb).2)
        (fun q hq => by
          obtain ⟨ao, hao⟩ := h.2.arch hq
          have : q.bv ≠ ct.bv := kheap_ne hao hk (fun _ h1 h2 => by subst h1; cases h2)
          rw [stsAct_kheap, updK_kheap, Function.update_of_ne this])⟩, a5⟩
  capStable := fun s s' a σ σ' h hw hst => ⟨hH.capStable s s' a σ σ' h.1 hw hst, h.2.frame
    (fun b hb => hw.2.2 b (PtWAll.aligned h.1.1.2.pt hb) (h.1.1.2.ps b hb))
    (fun q hq => by
      obtain ⟨p, r, cs, idx, a', hk, rfl⟩ := hst
      obtain ⟨ao, hao⟩ := h.2.arch hq
      have : q.bv ≠ p := kheap_ne hao hk (fun _ h1 h2 => by subst h1; cases h2)
      simp [setCnodeSlot, this])⟩
  vsStable := fun s s' a σ σ' h hw hst => ⟨hH.vsStable s s' a σ σ' h.1 hw hst, h.2.frame
    (fun b hb => hw.2.2 b (PtWAll.aligned h.1.1.2.pt hb) (h.1.1.2.pv b hb))
    (by
      rcases hst with ⟨p, f, f', hk, rfl⟩ | ⟨t, rfl⟩
      · intro q hq
        rw [updK_kheap, Function.update_of_ne (h.2.not_pool hk hq)]
      · intro q _; rfl)⟩

set_option maxHeartbeats 8000000 in
/-- **An ASID pool cap at `TopSR` with `VsCapsIn`** (`Assign`, any other
label), `FinX` after: the pool word written is the PML4 of the extra cap, in
`L4` by the cap invariant. -/
theorem decode_invocation_asid_pool_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
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
    (hsl : IsSlot th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))  :
    DecOKMX (L := L) arI (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) s ar σ lbl length
      slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps buffer := by
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest ∧
        ∀ p1 a1, vc = .Pml4 p1 false a1 → p1 ≠ 0#u64 := by
    rcases hext with h | ⟨pc, r, idx, vc, vc', rest, h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨pc, r, idx, vc, vc', rest, h1, h2, h3, h4, h5, h6, fun p1 a1 e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (AbsSlot.isSlot (th := th) (sl := (pc.bv, idx))
        ⟨pc, rfl, Or.inl (by simpa [h2] using h1)⟩) h4 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨-, hv2, -⟩ := hv
      exact hv2
  -- the extra cap's PML4 is in `L4`
  have hL4 : ∀ x p1 a1, vspace.extra extra 0#usize = ok (some x) → capAt (L.mem s) x = ok (.Pml4 p1 false a1) →
      p1 ∈ L4 := by
    intro x p1 a1 hx hcx
    rcases hext with ⟨h, -⟩ | ⟨pc, r, idx, vc, vc', rest, h1, h2, h3, -, -, -⟩
    · have := eq_of_ok_eq (h.symm.trans hx); cases this
    · have := Option.some.inj (eq_of_ok_eq (h3.symm.trans hx)); subst this
      have hv := hVC.at hCR.2.2.1 (AbsSlot.isSlot (th := th) (sl := (pc.bv, idx))
        ⟨pc, rfl, Or.inl (by simpa [h2] using h1)⟩) hcx (by simp)
      simp only [VCapOK] at hv
      exact hv.1
  have hH := VsInvHyps.ptTop (L1 := L1) (L2 := L2) (L3 := L3) (L4 := L4) (A := A) (N := N) (T := T) (C := C)
    (E := E) (R := R) (B := B) (c := c) (AR := AR)
    (Vs.VsInvHyps.foot (s0 := s) (W := VsFootW st th P L4 L3 L2 L1 s) (fun _ h => h.toW) hS.2.pl
      (fun _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) (vsInvHyps_top curT_top))
  refine DecOKMQX.toX arI (decode_invocation_asid_poolX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial)
    hH ⟨⟨hS, P1.WritesIn.refl _ _⟩, hPt⟩ hS.2.vs hS.2.sd hR hS.2.vo
    lbl slbl hlA length buf ct hct hcur htcb hact hrun ptr base hok.2.1 hok.2.2 extra excaps hNative hext'
    (X := FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) (vs_x0 hS hR hPt hPI hCur)
    (fun s' a' σ' hSR hR' hAW hCR' hMO' hK => ⟨hSR.1.1, hR', hSR.2, fun p hp lo hl hne => ?_,
      CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩)
    slot blk call don fp args ci sl buffer) (fun _ _ _ h => h)
  by_cases e : L.mem s' (peA p lo) = L.mem s (peA p lo)
  · rw [e] at hne ⊢; exact hPI p hp lo hl hne
  · obtain ⟨x, p1, a1, hx, hcx, hv⟩ := hAW _ (Or.inr ⟨p, hp, lo, hl, rfl⟩) e
    rw [hv]; exact fun _ => hL4 x p1 a1 hx hcx

/-! ## `MakePool` -/

omit arI in
/-- **The named hypothesis of `MakePool`'s re-indexing**: at the outcome, the
composite relation at the old typed heap and pool set gives it at the new
typed heap `th'` and the pool set grown by the new pool `p`, and the TCBs
stay TCBs of `th'`. (The global invariant over the typed heap and the ghost
sets is not designed yet.) -/
structure MpPlacedHyp (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (th : TypedHeap)
    (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (AR : A → Fl4Spec.Cr3 → Prop)
    (p : U64) (th' : TypedHeap) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop where
  top : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a' σ' →
    TopSR st th' (insert p P) L4 L3 L2 L1 N T C E R B c AR s' a' σ'
  tcb : ∀ t : U64, th t = some .tcb → th' t = some .tcb

/-- The VSpace invariants for some typed heap and pool set. -/
def FinXE (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (L4 L3 L2 L1 N T C E R : Set U64)
    (B : Set (U64 × Fl4Spec.Word)) (c : U64) (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th P, FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap at `TopSR`** (`MakePool`, any other label): `FinX`
after at the new typed heap and the grown pool set (`FinXE`), the
re-indexing a named hypothesis (`MpPlacedHyp`). -/
theorem decode_invocation_asid_control_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPI : PoolsIn P L4 (L.mem s))
    (hCur : CurOK st th s σ)
    (hMP : ∀ p th' s' a' σ', MpPlacedHyp st th P L4 L3 L2 L1 N T C E R B c AR p th' s' a' σ')
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
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKTop (L := L) N T C E R B c s σ p)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMX (L := L) arI (FinXE st L4 L3 L2 L1 N T C E R B c AR) s ar σ lbl length slot .AsidControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_asid_controlX arI th hS.2.pl s ar σ G hCR hFI hU hMO (fun _ _ _ _ => trivial)
    vsMpHyps_top hS hR hPt hS.2.vs hS.2.pt
    hS.2.vo hS.2.po hS.2.pv lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hext
    (X := FinXE st L4 L3 L2 L1 N T C E R B c AR) ⟨th, P, vs_x0 hS hR hPt hPI hCur⟩
    (fun s' a' σ' p th' G' hSR hR' hPt' hcur' hPI' hCR' hMO' =>
      ⟨th', insert p P, (hMP p th' s' a' σ').top hSR, hR', hPt', hPI' L4 hPI, by
        obtain ⟨t, h1, h2, -⟩ := hCur
        obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hMO'.2.2
        have h2' := (hMP p th' s' a' σ').tcb t h2
        refine ⟨t, h1.trans hcur'.symm, h2', fun q asid h => ?_⟩
        have hv := hVC.at hCR'.2.2.1 ⟨t, 1, Or.inr ⟨h2', by decide⟩, rfl⟩ h (by simp)
        simp only [VCapOK] at hv
        exact (hv.2.2 trivial).1⟩)
    slot blk call don fp ci sl buffer) (fun _ _ _ h => h)

end

end

end Fl4Proofs.P3
