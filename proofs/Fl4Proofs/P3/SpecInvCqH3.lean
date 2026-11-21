/-
P3 (DESIGN.md §9), invariant line G1 (ctq14): ctq12's deletion-cone perform
arms with the four hypotheses discharged (`ebCapDeleteH`, `ebCapRevokeH`,
`ebCapDeleteOneH`, `ebCancelBadgedSendsH`, SpecInvCqH1/H2): CNode, IRQ
handler, ThreadControlCaps and its `install_tcb_cap` / `install_tcb_frame_cap`
steps, now without premises (spec side only, outside the JAtZ cone).
-/
import Fl4Proofs.P3.SpecInvCqH2
import Fl4Proofs.P3.SpecInvCqC4
open Classical

namespace Fl4Proofs.P3.SInvQ.R14
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12

noncomputable section

/-- **The CNode arm** (ctq12's `eb_perfCnode`, no hypotheses). -/
theorem eb_perfCnodeD (C : ObjRef) (bl call don : Bool) (i : CnodeInvocation) :
    HKEr (DK C) (DK C) (fl4PerformInvocation (Z := Unit) bl call don (.invokeCNode i)) :=
  P12.eb_perfCnode ebCapDeleteH ebCapRevokeH ebCancelBadgedSendsH C bl call don i

/-- **The IRQ handler arm** (ctq12's `eb_perfIrqHandler`, no hypothesis). -/
theorem eb_perfIrqHandlerD (C : ObjRef) (bl call don : Bool) (i : IrqHandlerInvocation) :
    HKEr (DK C) (DK C) (fl4PerformInvocation (Z := Unit) bl call don (.invokeIRQHandler i)) :=
  P12.eb_perfIrqHandler ebCapDeleteOneH C bl call don i

theorem dk_installTcbCapD (C target : ObjRef) (slot : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    HKEr (DK C) (DK C) (installTcbCap (Z := Unit) target slot n o) :=
  P12.dk_installTcbCap ebCapDeleteH C target slot n o

theorem dk_installTcbFrameCapD (C target : ObjRef) (slot : CslotPtr)
    (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    HKEr (DK C) (DK C) (installTcbFrameCap (Z := Unit) target slot b) :=
  P12.dk_installTcbFrameCap ebCapDeleteH C target slot b

/-- **ThreadControlCaps** (ctq12's `eb_perfTcbCaps`, no hypothesis). -/
theorem eb_perfTcbCapsD (C : ObjRef) (bl call don : Bool) (target : Word) (slot : CslotPtr)
    (fh th cr vr : Option (Cap × CslotPtr)) (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    HKEr (DK C) (DK C)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.threadControlCaps target slot fh th cr vr buf))) :=
  P12.eb_perfTcbCaps ebCapDeleteH C bl call don target slot fh th cr vr buf

end

end Fl4Proofs.P3.SInvQ.R14
