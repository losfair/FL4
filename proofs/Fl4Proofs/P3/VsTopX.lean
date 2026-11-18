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
label); the native frame caps, every label (`GetAddress` and
`TestAndClearAccessed` reply in the decode, `DecOKRMX`: the reply
hypotheses `GetAddrHypX` / `TacHypX` keep `FinX`, and `FinX` holds after
the accessed-bit clear, `finX_clr5`); the PML4 caps (`Flush`, any other);
the ASID pool caps (`Assign` of a native root: the pool word written is the
extra cap's PML4, in `L4` by the cap invariant; `PtRel` carried through
`VsInvHyps.ptTop`); the ASID control cap (`MakePool`: `FinXE`, the
invariants at the new typed heap and the pool set grown by the new pool;
the re-indexing of `TopSR`, `MpPlacedHyp`, proved from the joint placement
invariant at the entry by `mpPlacedHyp_of`).

Guest-tagged pool entries (bit 0 set, nested roots): `PoolsIn` constrains
the native entries only, `VsRel` relates every entry word to the spec's
pool (a tagged entry is occupied in both), and native lookup rejects tagged
entries on both sides (`find_vspace_for_asid_L4`).
-/
import Fl4Proofs.P3.VsDomF
import Fl4Proofs.P3.VsFin
import Fl4Proofs.P3.ScPlaceUt
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

/-- The spec's step of a VSpace invocation keeps the SC objects. -/
theorem KFoot.szKeep {σ σ' : Fl4Spec.State Unit} (h : KFoot σ σ') : Sched.SzKeep σ σ' := by
  intro p x n hp
  by_cases e : σ'.kheap p = σ.kheap p
  · exact ⟨x, by rw [← e]; exact hp⟩
  · rcases h.2.2.1 p e with ⟨ao, ao', -, h2⟩ | ⟨r, cs, cs', -, -, h2⟩ | ⟨t, t', -, h2⟩ <;> rw [hp] at h2 <;> cases h2

/-- **`FinX` with the CSpace relation at its own typed heap**, the kernel
base `k` and the SC objects of `σ0` kept: what `FinXR` needs after a
VSpace producer (TopXAll's `VsThX`). -/
def FinXT (th : TypedHeap) (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (AR : A → Fl4Spec.Cr3 → Prop) (k : U64) (σ0 : Fl4Spec.State Unit) (s : S) (a : A) (σ : Fl4Spec.State Unit) :
    Prop :=
  FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ ∧
    (∃ G, CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ MdbOKV (L.ksb s) (L.mem s) G) ∧
    L.ksb s = k ∧ Sched.SzKeep σ0 σ

theorem FinXT.fin {k : U64} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR k σ0 s a σ) :
    FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ := h.1

/-- `FinXT` at the entry. -/
theorem vs_x0T {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPI : PoolsIn P L4 (L.mem s))
    (hCur : CurOK st th s σ) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) :
    FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ s a σ :=
  ⟨vs_x0 hS hR hPt hPI hCur, ⟨G, hCR, hFI, hMO⟩, rfl, Sched.SzKeep.of_kheap rfl⟩

/-- **`FinXT` after an outcome** of the footprint without the pool words. -/
theorem vs_x_afterT {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hSR : FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW0 st th L4 L3 L2 L1 s) s' a' σ')
    (hR' : VsRel P (L.mem s') (L.ksb s') σ') (hPt' : PtRel L4 L3 L2 L1 (L.mem s') σ')
    (hCR' : CRel th (L.mem s') σ' G) (hFI' : FinInv th (L.mem s') σ' G) (hMO' : MdbOKV (L.ksb s) (L.mem s') G)
    (hK : KFoot σ σ') :
    FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ s' a' σ' :=
  ⟨vs_x_after hS hPI hCur hSR hR' hPt' hCR' hMO' hK, ⟨G, hCR', hFI', by rw [hSR.2.1]; exact hMO'⟩, hSR.2.1,
    KFoot.szKeep hK⟩

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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_page_tableX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vs_x0T hS hR hPt hPI hCur hCR hFI hMO) (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK => vs_x_afterT hS hPI hCur hSR hR' hPt' hCR' hFI' hMO' hK) ((vsPtMapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ((vsPtUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_page_directoryX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vs_x0T hS hR hPt hPI hCur hCR hFI hMO) (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK => vs_x_afterT hS hPI hCur hSR hR' hPt' hCR' hFI' hMO' hK) ((vsPdMapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ((vsPdUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_pdptX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vs_x0T hS hR hPt hPI hCur hCR hFI hMO) (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK => vs_x_afterT hS hPI hCur hSR hR' hPt' hCR' hFI' hMO' hK) ((vsPdptMapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ((vsPdptUnmapHyps_top hA).foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
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

/-! ## The accessed-bit clear of `TestAndClearAccessed` -/

theorem hA_clr5 (w : U64) : hA (w &&& ~~~32#u64) = hA w := by
  unfold hA; rw [clr5 w _ (by decide)]

theorem PML4ERel_clr5 {L3 : Set U64} {w : U64} {x : Fl4Spec.PML4E} (h : PML4ERel L3 w x) :
    PML4ERel L3 (w &&& ~~~32#u64) x := by
  cases x with
  | invalidPML4E => show ¬ eP _; rw [eP_clr5]; exact h
  | pdPointerTablePML4E t a r =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨(eP_clr5 w).2 h1, by rw [eA_clr5]; exact h2, ?_⟩
    unfold eT; rw [eA_clr5]; exact h3

theorem PDPTERel_clr5 {L2 : Set U64} {w : U64} {x : Fl4Spec.PDPTE} (h : PDPTERel L2 w x) :
    PDPTERel L2 (w &&& ~~~32#u64) x := by
  cases x with
  | invalidPDPTE => show ¬ eP _; rw [eP_clr5]; exact h
  | pageDirectoryPDPTE t a r =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨(eP_clr5 w).2 h1, by rw [eS_clr5]; exact h2, by rw [eA_clr5]; exact h3, ?_⟩
    unfold eT; rw [eA_clr5]; exact h4
  | hugePagePDPTE f a r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨(eP_clr5 w).2 h1, (eS_clr5 w).2 h2, by rw [hA_clr5]; exact h3, ?_, ?_⟩
    · unfold PteRights at *; rw [bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide)]; exact h4
    · unfold PteAttrsH at *
      rw [bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide)]
      exact h5

/-- **`PtRel` after clearing the accessed bit of one entry.** -/
theorem PtRel.clr5 {m m' : U64 → U64} {σ0 : Fl4Spec.State Unit} (hR : PtRel L4 L3 L2 L1 m σ0) {b : U64}
    (hm : ∀ x, PtWAll L4 L3 L2 L1 x → x ≠ b → m' x = m x) (hb : m' b = m b &&& ~~~32#u64) :
    PtRel L4 L3 L2 L1 m' σ0 := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l4 q hq
    refine ⟨g, hg, fun j hj => ?_⟩
    by_cases e : peA q j = b
    · rw [e, hb]; exact PML4ERel_clr5 (e ▸ hgf j hj)
    · rw [hm _ ⟨q, Or.inl hq, j, hj, rfl⟩ e]; exact hgf j hj
  · obtain ⟨g, hg, hgf⟩ := hR.l3 q hq
    refine ⟨g, hg, fun j hj => ?_⟩
    by_cases e : peA q j = b
    · rw [e, hb]; exact PDPTERel_clr5 (e ▸ hgf j hj)
    · rw [hm _ ⟨q, Or.inr (Or.inl hq), j, hj, rfl⟩ e]; exact hgf j hj
  · obtain ⟨g, hg, hgf⟩ := hR.l2 q hq
    refine ⟨g, hg, fun j hj => ?_⟩
    by_cases e : peA q j = b
    · rw [e, hb]; exact PDERel_clr5 (e ▸ hgf j hj)
    · rw [hm _ ⟨q, Or.inr (Or.inr (Or.inl hq)), j, hj, rfl⟩ e]; exact hgf j hj
  · obtain ⟨g, hg, hgf⟩ := hR.l1 q hq
    refine ⟨g, hg, fun j hj => ?_⟩
    by_cases e : peA q j = b
    · rw [e, hb]; exact PTERel_clr5 (e ▸ hgf j hj)
    · rw [hm _ ⟨q, Or.inr (Or.inr (Or.inr hq)), j, hj, rfl⟩ e]; exact hgf j hj

theorem OStep.refl' (σ0 : Fl4Spec.State Unit) : OStep (fun _ => False) σ0 σ0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd rfl h⟩

/-- **`FinX` after the accessed-bit clear** (the spec unchanged: the bit is
invisible to the relations). -/
theorem finX_clr5 {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ) {b : U64}
    (hb : PtWAll L4 L3 L2 L1 b) (hal : P1.Aligned b) :
    FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)
      (L.wr s b (L.mem s b &&& ~~~32#u64)) a σ := by
  obtain ⟨hS, hR, hPt, hPI, hCur⟩ := hX
  set s' := L.wr s b (L.mem s b &&& ~~~32#u64)
  have hks : L.ksb s' = L.ksb s := by simp [s']
  have hm : ∀ x, P1.Aligned x → x ≠ b → L.mem s' x = L.mem s x :=
    fun x hx hne => L.mem_wr_ne hal hx (fun h => hne (UScalar.eq_of_val_eq h).symm)
  have hW : P1.WritesIn st s s' (fun x => x = b) := ⟨hks, by simp [s'], fun x hx hn => hm x hx hn⟩
  have hvs : ∀ x, VsWrite P (L.ksb s) x → L.mem s' x = L.mem s x :=
    fun x hx => hm x (VsWrite.aligned hS.2.vs hx) (fun e => hS.2.pv b hb (e ▸ hx))
  have hcap : ∀ x, IsSlot th x → capAt (L.mem s') x = capAt (L.mem s) x :=
    fun x hx => capAt_wr_nonslot (L := L) hS.2.pl s hal (hS.2.ps b hb) _ x hx
  refine ⟨TopSR.step0 hS (fun x e => by
      obtain ⟨q, hq, i, hi, rfl⟩ := hb; rw [e]; exact table_vobj hS.2.pt hq hi _) hW (OStep.refl' σ) rfl rfl,
    by rw [hks]; exact hR.frame hvs rfl (fun _ _ => rfl),
    Fl4Proofs.P3.PtRel.clr5 hPt (fun x hx hne => hm x (PtWAll.aligned hS.2.pt hx) hne) (L.mem_wr_same hal),
    fun q hq lo hl hne => ?_, ?_⟩
  · have hw : VsWrite P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvs _ hw] at hne ⊢; exact hPI q hq lo hl hne
  · obtain ⟨t, h1, h2, h3⟩ := hCur
    exact ⟨t, h1, h2, fun q asid h => h3 q asid (by rw [← hcap _ ⟨t, 1, Or.inr ⟨h2, by decide⟩, rfl⟩]; exact h)⟩

/-- **`FinXT` after the accessed-bit clear.** -/
theorem finXT_clr5 {k : U64} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR k σ0 s a σ) {b : U64}
    (hb : PtWAll L4 L3 L2 L1 b) (hal : P1.Aligned b) :
    FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR k σ0 (L.wr s b (L.mem s b &&& ~~~32#u64)) a σ := by
  obtain ⟨hF, ⟨G, hCR, hFI, hMO⟩, hk, hz⟩ := hX
  have hPl := hF.1.2.pl
  have hSS : SlotsSame th (L.mem s) (L.mem (L.wr s b (L.mem s b &&& ~~~32#u64))) := by
    refine slotsSame_wr hPl s _ hal (fun a ha => ?_)
    obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hPl ha
    have := (hF.1.2.po b hb).2 p k hk
    omega
  have hksb : L.ksb (L.wr s b (L.mem s b &&& ~~~32#u64)) = L.ksb s := L.ksb_wr _ _ _
  refine ⟨finX_clr5 hF hb hal, ⟨G, ⟨hCR.1.of_caps (fun y hy => hSS.capAt hy),
      SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy), hCR.2.2.1.of_same hSS,
      hCR.2.2.2.1.of_same hSS rfl rfl, MdbInv.of_same hCR.2.2.1 hCR.2.2.2.2 hSS⟩,
    hFI.of_same hCR.2.2.1 hSS (KSub.refl σ), by rw [hksb]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO⟩,
    hksb.trans hk, hz⟩

set_option maxHeartbeats 8000000 in
/-- **A frame cap, every label, at `TopSR` with `VsCapsIn`**, `FinX` after;
`GetAddress` and `TestAndClearAccessed` reply in the decode (`DecOKRMX`,
from the reply hypotheses `GetAddrHypX` / `TacHypX` keeping `FinX`). -/
theorem decode_invocation_frame_capX [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hU : UtInv (L.mem s) G) (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
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
    (hga : GetAddrHypX (L := L) (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s σ ar ct p call)
    (htac : TacHypX (L := L) (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) L4 L3 L2 L1
      s σ ar ct call) :
    (lbl ≠ fl4_abi.label.X86PageGetAddress ∧ lbl ≠ fl4_abi.label.X86PageTestAndClearAccessed ∧
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) ∨
    DecOKRMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length
      (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX0' := vs_x0T hS hR hPt hPI hCur hCR hFI hMO
  obtain ⟨xct0, hkt0', -⟩ := hCR.1.tcb ct htcb
  by_cases hga' : lbl = fl4_abi.label.X86PageGetAddress
  · exact Or.inr (decode_invocation_frame_getaddrX (L := L) arI s ar σ lbl slbl hlbl hga' length buf ct hct hcur
      hkt0' _ blk call don fp hga hX0' extra _ ci _ excaps buffer)
  by_cases htac' : lbl = fl4_abi.label.X86PageTestAndClearAccessed
  · exact Or.inr (decode_invocation_frame_tacX (L := L) arI s ar σ hR hPt hS.2.pt hPI lbl slbl hlbl htac' length buf
      ct hct hcur hkt0' _ blk call don fp htac hX0' (fun b hb hal => finXT_clr5 hX0' hb hal) extra _ ci _ excaps
      buffer)
  refine Or.inl ⟨hga', htac', ?_⟩
  have hnGA := hga'
  have hnTAC := htac'
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
  have hX0 := vs_x0T hS hR hPt hPI hCur hCR hFI hMO
  have hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKMQX (L := L) arI (fun _ => True) (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ)
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
      (fun _ _ _ G' hSR hR' hPt' hCR' hFI' hMO' hsz => ⟨⟨hSR.1.1, hR', hPt',
        Vs.PoolsIn.of_writes hPI hSR.2.1 hS.2.vs (fun _ hb => foot0_not_vs hS hb),
        CurOK.of_inv' hCur hSR.1.2 hCR'.2.2.1 hMO'.2.2⟩, ⟨G', hCR', hFI', by rw [hSR.2.1.1]; exact hMO'⟩,
        hSR.2.1.1, hsz⟩)
      (Vs.VsSubHyps.foot (s0 := s) (W := VsFootW0 st th L4 L3 L2 L1 s) (fun _ h => h) hS.2.pl
        (VsSubHyps.cur (Vs.vsSubHyps_top (st := st) (L := L) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2)
          (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR)) σ.curThread))
      ⟨⟨hS, rfl⟩, P1.WritesIn.refl _ _, fun t ht => by rw [P1.eq_of_bv (ht.trans hcur)]; exact htcb, hact⟩
      hS.2.pt hS.2.vs hS.2.vo hS.2.po hR hPt lbl slbl hlbl hl length buf ct hct hcur htcb hact hkt
      (hrun _ hkt) args hlen hargs (pc := pc) (r := r) (idx := idx) hpc hidx (p := p) (sz := sz) (rt := rt)
      (asid := asid) (va := va) (d := d) (m := m) hcap hno hMO hVC extra excaps hext'' blk call don fp ci buffer
  have h := decode_invocation_frameX arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial)
    hX0
    (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK => vs_x_afterT hS hPI hCur hSR hR' hPt' hCR' hFI' hMO' hK)
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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length
      slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl excaps buffer := by
  have hX0 := vs_x0T hS hR hPt hPI hCur hCR hFI hMO
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
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_slots th hS.2.pl s ct sched.TS_RESTART htcb hact)
    (set_thread_state_cases s ct sched.TS_RESTART))
    (restart_full (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) s ar σ ct xct hSt hSV hR hS hcur.symm hkt0 htcb hact
      (hrun _ hkt))) ?_
  rintro s1 ⟨⟨hSS, hcs⟩, hSt1, hSV1, hR1, hPt1, hS1, hk1, hPI1⟩
  have hks1 : L.ksb s1 = L.ksb s := by rcases hcs with rfl | rfl <;> simp
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
  exact ⟨⟨hS', hR1.ms ms, (hPt1 hPt).same_heap rfl, hPI1 hPI, CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩,
    ⟨G, hCR', hFI.of_same hM hSS (KFoot.ksub hK), by rw [hks1]; exact hMO'⟩, hks1, KFoot.szKeep hK⟩

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
    DecOKMX (L := L) arI (FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length
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
    (X := FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) (vs_x0T hS hR hPt hPI hCur hCR hFI hMO)
    (fun s' a' σ' hSR hR' hAW hCR' hFI' hMO' hK => ⟨⟨hSR.1.1, hR', hSR.2, fun p hp lo hl hne => ?_,
      CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩, ⟨G, hCR', hFI', by rw [hSR.1.2.1]; exact hMO'⟩, hSR.1.2.1,
      KFoot.szKeep hK⟩)
    slot blk call don fp args ci sl buffer) (fun _ _ _ h => h)
  by_cases e : L.mem s' (peA p lo) = L.mem s (peA p lo)
  · rw [e] at hne ⊢; exact hPI p hp lo hl hne
  · obtain ⟨x, p1, a1, hx, hcx, hv⟩ := hAW _ (Or.inr ⟨p, hp, lo, hl, rfl⟩) e
    rw [hv]; exact fun _ => hL4 x p1 a1 hx hcx

/-! ## `MakePool` -/

omit arI in
/-- **`MakePool`'s re-indexing**: from the facts of the step (the new typed
heap is `th` without the page, the kernel-state base kept, no new SC, the
page's `MpRegion`, its source untyped cap childless in the MDB), the
composite relation at the old typed heap and pool set gives it at the new
typed heap `th'` and the pool set grown by the new pool `p`, and the TCBs
stay TCBs of `th'`. Proved from the joint placement invariant at the entry
by `mpPlacedHyp_of`: the page holds no object of `th` (`th' = th`) and no
word the other relations read at the outcome (`disj`), and `vs`, `pv`,
`vo`, `sd` come from `MpRegion` and the page being outside every object. -/
def MpPlacedHyp (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (th : TypedHeap)
    (P L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (AR : A → Fl4Spec.Cr3 → Prop)
    (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∀ (p : U64) (th' : TypedHeap) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit),
    th' = restrictTh th p.val (p.val + 4096) → L.ksb s' = L.ksb s →
    (∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n)) →
    MpRegion th G P L4 L3 L2 L1 (L.ksb s) p →
    (∃ x fi, x ∈ G.chains.flatten ∧ capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false ∧
      ∀ y, ¬ Mdb.Desc G.par y x) →
    (TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a' σ' →
      TopSR st th' (insert p P) L4 L3 L2 L1 N T C E R B c AR s' a' σ') ∧
    ∀ t : U64, th t = some .tcb → th' t = some .tcb

/-- **`MpPlacedHyp` from the joint placement invariant at the entry**
(`Sched.JCov`, `Sched.JPlaced`, the other relations' sets drawn from P1's
heap `H`, the IPC-buffer words covered): the childless untyped region holds
no object of `th` (`restrictTh_childless`, so `th' = th`) and no word the
other relations read at the outcome (`oobj_out`); the rest from `MpRegion`. -/
theorem mpPlacedHyp_of {H : P1.Heap} {G : MdbGhost} {Cs Tr C0 : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hJC : Sched.JCov (L := L) th H G Cs s) (hJP : Sched.JPlaced (L := L) th H Tr C0 s σ)
    (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G) (hc : c ∈ Cs)
    (hT : ∀ t ∈ T, H t = some .tcb) (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply)
    (hN : ∀ n ∈ N, H n = some .ntfn) (hC : ∀ q ∈ C, q ≠ 0#u64)
    (hB : ∀ wp ∈ B, Sched.Covered (L.mem s) G wp.1.val (wp.1.val + 8)) :
    MpPlacedHyp st th P L4 L3 L2 L1 N T C E R B c AR s σ G := by
  intro p th' s' a' σ' hth hk hsc hRg ⟨x, fi, hx, hcx, hnd⟩
  have h2 : 2 ^ (fl4_abi.consts.bits.ASID_POOL).val = 4096 := by unfold fl4_abi.consts.bits.ASID_POOL; rfl
  have hrt := Sched.restrictTh_childless hJC hU hI hx hcx hnd
  rw [h2] at hrt
  rw [hrt] at hth
  subst th'
  refine ⟨fun hS => ?_, fun t ht => ht⟩
  obtain ⟨hO, hTP⟩ := hS
  obtain ⟨hpal, hpfit, hp0, -, -, -, hPo, hLo, hTo⟩ := hRg
  -- the page holds no object of `th`
  have hout : ∀ q k, th q = some k → q.val + objSize k ≤ p.val ∨ p.val + 4096 ≤ q.val := by
    intro q k hq
    have := Sched.ut_free hU hI hx hcx hnd (by omega) (hJC.th q k hq)
    rw [h2] at this
    omega
  have hoob := Sched.oobj_out hJC hJP hU hI hx hcx hnd hc hT hE hR hN hC hB hk hsc
  rw [h2] at hoob
  have hpool : ∀ b, VsWrite (insert p P) (L.ksb s') b → VsWrite P (L.ksb s') b ∨
      (p.val ≤ b.val ∧ b.val < p.val + 4096 ∧ b.val % 8 = 0) := by
    rintro b (h | ⟨q, hq, lo, hl, rfl⟩)
    · exact Or.inl (Or.inl h)
    · rcases hq with rfl | hq
      · right; rw [peA_val hpfit hl]; refine ⟨by omega, by omega, by omega⟩
      · exact Or.inl (Or.inr ⟨q, hq, lo, hl, rfl⟩)
  refine ⟨hO, ⟨hTP.ep, ?_, hTP.pt, hTP.pl, fun a ha hv => ?_, hTP.nodeE, hTP.po, hTP.ps, fun b hb hw => ?_,
    fun b hw => ?_, fun b hw hsw => ?_, hTP.tko⟩⟩
  · -- `vs`
    refine ⟨hTP.vs.ksb_al, hTP.vs.ksb_fit, fun q hq => ?_, fun q hq => ?_⟩
    · rcases hq with rfl | hq
      · exact ⟨hpal, hpfit⟩
      · exact hTP.vs.pal q hq
    · rcases hq with rfl | hq
      · rw [hk]; exact hTo
      · exact hTP.vs.ptab q hq
  · -- `disj`
    rcases hv with h | h | ⟨q, hq, h1, h2'⟩ | h
    · exact hTP.disj a ha (Or.inl h)
    · exact hTP.disj a ha (Or.inr (Or.inl h))
    · rcases hq with (rfl | hq) | hq
      · exact hoob a h1 h2' ha
      · exact hTP.disj a ha (Or.inr (Or.inr (Or.inl ⟨q, Or.inl hq, h1, h2'⟩)))
      · exact hTP.disj a ha (Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, h1, h2'⟩)))
    · exact hTP.disj a ha (Or.inr (Or.inr (Or.inr h)))
  · -- `pv`
    rcases hpool b hw with h | ⟨h1, h2', -⟩
    · exact hTP.pv b hb h
    · obtain ⟨q, hq, i, hi, rfl⟩ := hb
      have hqa := hTP.pt q hq
      rw [peA_val (tbl_fit hqa) hi] at h1 h2'
      have := hLo q hq; omega
  · -- `vo`
    rcases hpool b hw with h | ⟨h1, h2', h8⟩
    · exact hTP.vo b h
    · refine ⟨h8, fun q k hq hin => ?_⟩
      have := hout q k hq; omega
  · -- `sd`
    rcases hpool b hw with h | ⟨h1, h2', -⟩
    · exact hTP.sd b h hsw
    · obtain ⟨y, hy, hb⟩ := hsw
      obtain ⟨q, i, hqi, rfl⟩ := hy
      have hv := hqi.val hTP.pl
      obtain ⟨k, hk', hs⟩ := hqi.size
      have := hout q k hk'
      have hf := hTP.pl.fits q k hk'
      rcases hb with rfl | rfl
      · rw [hv] at h1 h2'; omega
      · have : (core.num.U64.wrapping_add (slotOf q i) 8#u64).val = (slotOf q i).val + 8 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; rw [hv]; omega
        rw [this, hv] at h1 h2'; omega

/-- The VSpace invariants for some typed heap and pool set. -/
def FinXE (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (L4 L3 L2 L1 N T C E R : Set U64)
    (B : Set (U64 × Fl4Spec.Word)) (c : U64) (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th P, FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ

/-- `FinXT` for some typed heap and pool set (`MakePool` re-picks them). -/
def FinXET (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (L4 L3 L2 L1 N T C E R : Set U64)
    (B : Set (U64 × Fl4Spec.Word)) (c : U64) (AR : A → Fl4Spec.Cr3 → Prop) (k : U64) (σ0 : Fl4Spec.State Unit)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th P, FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR k σ0 s a σ

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap at `TopSR`** (`MakePool`, any other label): `FinX`
after at the new typed heap and the grown pool set (`FinXE`), the
re-indexing by `MpPlacedHyp` (from `mpPlacedHyp_of`). -/
theorem decode_invocation_asid_control_capX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
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
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMX (L := L) arI (FinXET st L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length slot .AsidControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer :=
  DecOKMQX.toX arI (decode_invocation_asid_controlX arI th hS.2.pl s ar σ G hCR hFI hU hMO (fun _ _ _ _ => trivial)
    vsMpHyps_top hS hR hPt hS.2.vs hS.2.pt
    hS.2.vo hS.2.po hS.2.pv lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hext
    (X := FinXET st L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) ⟨th, P, vs_x0T hS hR hPt hPI hCur hCR hFI hMO⟩
    (fun s' a' σ' p th' G' hSR hR' hPt' hcur' hPI' hCR' hFI' hMO' hth hk hsc hRg hxu =>
      ⟨th', insert p P, ⟨(hMP p th' s' a' σ' hth hk hsc hRg hxu).1 hSR, hR', hPt', hPI' L4 hPI, by
        obtain ⟨t, h1, h2, -⟩ := hCur
        obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hMO'.2.2
        have h2' := (hMP p th' s' a' σ' hth hk hsc hRg hxu).2 t h2
        refine ⟨t, h1.trans hcur'.symm, h2', fun q asid h => ?_⟩
        have hv := hVC.at hCR'.2.2.1 ⟨t, 1, Or.inr ⟨h2', by decide⟩, rfl⟩ h (by simp)
        simp only [VCapOK] at hv
        exact (hv.2.2 trivial).1⟩, ⟨G', hCR', hFI', by rw [hk]; exact hMO'⟩, hk,
        fun q y n hq => hsc ⟨q⟩ y n hq⟩)
    slot blk call don fp ci sl buffer) (fun _ _ _ h => h)


/-- **The ASID control cap at `TopSR`**, the placement facts of `MakePool`
(`MpPlacedHyp`, the region's `RegOKTop`) from the joint placement invariant
at the entry (`mpPlacedHyp_of`, `regOKTop_childless`). -/
theorem decode_invocation_asid_control_capJ (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPI : PoolsIn P L4 (L.mem s))
    (hCur : CurOK st th s σ)
    {H : P1.Heap} {Cs Tr C0 : Set U64} (hJC : Sched.JCov (L := L) th H G Cs s)
    (hJP : Sched.JPlaced (L := L) th H Tr C0 s σ) (hc : c ∈ Cs)
    (hT : ∀ t ∈ T, H t = some .tcb) (hE : ∀ e ∈ E, H e = some .ep) (hRp : ∀ r ∈ R, H r = some .reply)
    (hN : ∀ n ∈ N, H n = some .ntfn) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hB : ∀ wp ∈ B, Sched.Covered (L.mem s) G wp.1.val (wp.1.val + 8))
    (hB2 : ∀ wp ∈ B, wp.2.toNat + 8 ≤ 2 ^ 64 ∧ Sched.Covered (L.mem s) G wp.2.toNat (wp.2.toNat + 8))
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
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKMX (L := L) arI (FinXET st L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ) s ar σ lbl length slot .AsidControl blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer :=
  decode_invocation_asid_control_capX arI th s ar σ G hCR hFI hU hMO hS hR hPt hPI hCur
    (mpPlacedHyp_of hJC hJP hU hCR.2.2.2.2 hc hT hE hRp hN hC0 hB) lbl slbl hlM length buf ct hct hcur htcb hact hrun
    args hlen hargs extra excaps (by
      rcases hext with h | ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hRg⟩
      · exact Or.inl h
      · refine Or.inr ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
          fun p fi e hch => ⟨hRg p fi e hch, ?_⟩⟩
        have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [h2] using h1)⟩
        have hnd := nodesc_of_cdt hS.2.pl hCR.2.2.2.1 hAs hch
        have hcv : capV (L.mem s) (cslotAddr (pp.bv, idx)) = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false := by
          rw [capV_of_capAt h5, e]
        have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten :=
          (hCR.2.2.1.members _).2 ⟨hAs.isSlot, _, h5, by rw [e]; simp⟩
        obtain ⟨hpal, hpfit, -⟩ := hRg p fi e hch
        exact Sched.regOKTop_childless hJC hJP hU hCR.2.2.2.2 hxm hcv hnd
          (by unfold fl4_abi.consts.bits.ASID_POOL; rfl) hpal hpfit hc hT hE hRp hN hC0 hB hB2)
    slot blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3
