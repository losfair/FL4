/-
P3 (DESIGN.md §9), IO ports: **the whole of `ioport::decode_control`**,
every label, against l4v's `decode_ioport_control_invocation`, then
`set_thread_state Restart` and `arch_perform_invocation`
(`ioport_control_decode_refines`), from `ioport_control_refines` (the
issue label) and `ioport_control_other` (every other label, the spec's
`IllegalOperation` with the state unchanged).
-/
import Fl4Proofs.P3.IoControl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`ioport::decode_control`, every label.** -/
theorem ioport_control_decode_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hL : IoLayout th (L.ksb s)) (hIo : IoRel (L.mem s) (L.ksb s) σ)
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl) (ac : Fl4Spec.ArchCap) :
    ioport.decode_control st arI s ar lbl length (cslotAddr (ps.bv, idxs)) buf extra ⦃ res =>
      IoCPost (L := L) th (L.ksb s) σ
        (Fl4Spec.decodeIoportControlInvocation slbl (args.map UScalar.bv) (ps.bv, idxs) ac excaps) s res ⦄ := by
  by_cases h63 : lbl.val = 63
  · have e : lbl = fl4_abi.label.X86IOPortControlIssue :=
      UScalar.eq_of_val_eq (by rw [h63]; simp [fl4_abi.label.X86IOPortControlIssue])
    subst e
    exact ioport_control_refines arI th hP s ar σ G hCR hL hIo hPA hFI hFR slbl (hlbl.1 h63) length buf ct hct args hlen
      hargs hcur htcb hact hact3 extra x0 hx0 excaps hex hps hls hsrcC ac
  exact ioport_control_other arI th s ar σ lbl h63 slbl (fun h => h63 (hlbl.2 h)) length _ buf extra _ _ ac excaps

end

end

end Fl4Proofs.P3
