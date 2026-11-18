/-
P3 (DESIGN.md §9), VSpace: **the decode wrappers at `TopSR` with the cap
invariant** (`VsCapsIn`, VsCapInv): the table, frame and ASID pool caps'
placement (`hpL`, `hpa`, `hm0`, `hfm`, `hpaS`/`hpaL`/`hpaH`, `hb`) and the
extra PML4 cap's shape from the invariant, the extra cap's slot a slot of
the typed heap (`hxs`).
-/
import Fl4Proofs.P3.VsFrameFull
import Fl4Proofs.P3.VsCapInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A page-table cap at `TopSR` with `VsCapsIn`** (`decode_invocation_page_table_top`; the table's placement and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_page_table_cap (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
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
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
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
  exact Vs.decode_invocation_page_table_top arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (hpL := hok.1) (hpa := hok.2.1) (hm0 := hok.2.2) (extra := extra) (excaps := excaps) (hext := hext') (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer)

set_option maxHeartbeats 8000000 in
/-- **A page-directory cap at `TopSR` with `VsCapsIn`** (`decode_invocation_page_directory_top`; the table's placement and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_page_directory_cap (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
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
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
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
  exact Vs.decode_invocation_page_directory_top arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (hpL := hok.1) (hpa := hok.2.1) (hm0 := hok.2.2) (extra := extra) (excaps := excaps) (hext := hext') (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer)

set_option maxHeartbeats 8000000 in
/-- **A PDPT cap at `TopSR` with `VsCapsIn`** (`decode_invocation_pdpt_top`; the table's placement and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_pdpt_cap (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
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
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
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
  exact Vs.decode_invocation_pdpt_top arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (hpL := hok.1) (hpa := hok.2.1) (hm0 := hok.2.2) (extra := extra) (excaps := excaps) (hext := hext') (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer)

set_option maxHeartbeats 8000000 in
/-- **A frame cap, every label, at `TopSR` with `VsCapsIn`** (`decode_invocation_frame_full`; `hfm`, `hpaS`/`hpaL`/`hpaH` and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_frame_cap [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
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
    (hga : GetAddrHyp (L := L) s σ ar ct p call) (htac : TacHyp (L := L) L4 L3 L2 L1 s σ ct call)  :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ∨
    DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
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
  exact decode_invocation_frame_full arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hU := hU) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlbl := hlbl) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d) (m := m) (hcap := hcap) (hfm := hok.1) (hpaS := (fun e => by subst e; exact hok.2)) (hpaL := (fun e => by subst e; exact hok.2)) (hpaH := (fun e => by subst e; exact hok.2)) (hAl := hAl) (hno := hno) (extra := extra) (excaps := excaps) (hext := hext') (hxs := hxs) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hga := hga) (htac := htac)

set_option maxHeartbeats 8000000 in
/-- **An ASID pool cap at `TopSR` with `VsCapsIn`** (`decode_invocation_asid_pool_top`; `hb` and the extra PML4 cap's shape from the invariant). -/
theorem decode_invocation_asid_pool_cap (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
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
    DecOKM (L := L) arI s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
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
  exact Vs.decode_invocation_asid_pool_top arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hS := hS) (hR := hR) (lbl := lbl) (slbl := slbl) (hlA := hlA) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (ptr := ptr) (base := base) (hb := hok.2.1) (hb20 := hok.2.2) (extra := extra) (excaps := excaps) (hNative := hNative) (hext := hext') (slot := slot) (blk := blk) (call := call) (don := don) (fp := fp) (args := args) (ci := ci) (sl := sl) (buffer := buffer)

end

end

end Fl4Proofs.P3
