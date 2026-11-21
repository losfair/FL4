/-
P1: the kernel entry from the decode gaps that remain after the
SchedContext, Domain and CNode families (`InvGaps2`), their named narrower
steps (`ScYieldGap`, `CnodeGaps`), the CDT placement facts (`CdtHyps`) and
`P3Place`.
-/
import Fl4Proofs.P1.QueueDecCnode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- The families whose decode P1 still does not prove, and the named steps
inside the families it does. -/
structure InvGaps2 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  untyped : DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok .untyped
  reply : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .reply
  thread : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread
  irqControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqControl
  irqHandler : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler
  schedControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedControl
  vspace : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ept
  ioPortControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPortControl
  ioPort : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPort
  /-- SchedContext `YieldTo`. -/
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- CNode `Delete` and `Revoke`. -/
  cnode : CnodeGaps st ar T Cs Ω H Sg Rp Scs Nt Z U

theorem InvGaps2.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (G : InvGaps2 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨G.untyped, G.reply, decGap_cnode C G.cnode, G.thread, G.irqControl, G.irqHandler, decGap_domain hA,
    decGap_sc hA E G.yield, G.schedControl, G.vspace, G.vcpu, G.ept, G.ioPortControl, G.ioPort⟩

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps2`, `CdtHyps`
and `P3Place` of every admissible tuple. -/
theorem kernel_entry.entry_of2 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXG st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ CdtHyps st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z P3Ok ∧
      InvGaps2 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_old st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of hA TX (fun σ h' => ⟨(GF σ h').1, (GF σ h').2.2.1.gaps hA (GF σ h').1.xfer (GF σ h').2.1,
    (GF σ h').2.2.2⟩) hσ s a hP h

end

end Fl4Proofs.P1
