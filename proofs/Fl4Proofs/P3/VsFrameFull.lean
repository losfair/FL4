/-
P3 (DESIGN.md §9), VSpace: **a frame cap, every label, at `TopSR`**
(`decode_invocation_frame_full`): `DecOK`, or `DecOKR` for `GetAddress` and
`TestAndClearAccessed`, from the Ep-side reply hypotheses `GetAddrHyp` and
`TacHyp` only (and `DeriveSubframe`'s MDB facts: `UtInv`, the window's
`hno`, `FrameInv`; the extra cap valid from `SlotsValid`, its slot a slot
of the typed heap, `hxs`).
-/
import Fl4Proofs.P3.VsDecReply
import Fl4Proofs.P3.VsTopInst
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A frame cap, every label, at `TopSR`** (see the module docstring). -/
theorem decode_invocation_frame_full [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
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
    (hfm : m = true → asid ≠ 0#u64)
    (hpaS : sz = .Small → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaL : sz = .Large → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaH : sz = .Huge → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hga : GetAddrHyp (L := L) s σ ar ct p call) (htac : TacHyp (L := L) L4 L3 L2 L1 s σ ct call) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ∨
    DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hGA : lbl = fl4_abi.label.X86PageGetAddress →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := fun hl => by
    have := decode_invocation_frame_getaddr (L := L) arI s ar σ lbl slbl hlbl hl length buf ct hct hcur hkt0
      (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d) (m := m)
      (cslotAddr (pc.bv, idx)) blk call don fp hga extra (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer
    exact this
  have hTAC : lbl = fl4_abi.label.X86PageTestAndClearAccessed →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := fun hl => by
    have := decode_invocation_frame_tac (L := L) arI s ar σ hR hPt hS.2.pt hPI lbl slbl hlbl hl length buf ct hct
      hcur hkt0 (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d) (m := m)
      (cslotAddr (pc.bv, idx)) blk call don fp htac extra (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer
    exact this
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ y nc nc' nsl rest, vspace.extra extra 0#usize = ok (some y) ∧ capAt (L.mem s) y = ok nc ∧
        CapRel nc nc' ∧ CapValid th nc ∧ excaps = (nc', nsl) :: rest := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4, -⟩
    · exact Or.inl h
    · have hv := Vs.capValid_slot hCR.2.1 (hxs x h1)
      rw [capAt_capV] at h2; cases eq_of_ok_eq h2
      exact Or.inr ⟨x, _, vc', xsl, rest, h1, capAt_capV _ _, h3, hv, h4⟩
  have hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := fun hl => by
    have := DecOKMQ.toM arI <| decode_invocation_frame_ds (L := L) arI th hS.2.pl s ar σ G hCR hFI hU (fun _ _ _ _ => trivial)
      (Vs.vsSubHyps_top (st := st) (L := L) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1)
        (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR)) hS hS.2.pt
      hS.2.vs hS.2.vo hS.2.po hR hPt lbl slbl hlbl hl length buf ct hct hcur htcb hact hkt (hrun _ hkt) args hlen
      hargs (pc := pc) (r := r) (idx := idx) hpc hidx (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va)
      (d := d) (m := m) hcap hno hMO hVC extra excaps hext' blk call don fp ci buffer
    exact this
  exact Vs.decode_invocation_frame_top (L := L) arI th s ar σ G hCR hFI hMO hA hS hPI hR hPt lbl slbl hlbl length buf ct
    hct hcur htcb hact hrun args hlen hargs hpc hidx hcap hfm hpaS hpaL hpaH hAl extra excaps hext blk call don fp ci
    buffer hGA hTAC hDS


end

end

end Fl4Proofs.P3
