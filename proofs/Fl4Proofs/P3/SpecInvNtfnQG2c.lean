/- nq3: invoke_tcb (see SpecInvNtfnQG2). -/
import Fl4Proofs.P3.SpecInvNtfnQG2a
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}
/-! ## `invoke_tcb`, one constructor at a time -/

theorem nq_invokeTcb_wr (d : Word) (r : Bool) (v : List Word) (a : ArchCopyRegisterSets) :
    NQKE Kq (invokeTcb (Z := Unit) (.writeRegisters d r v a)) := by
  simp only [invokeTcb]; nq2_auto

theorem nq_invokeTcb_rd (s : Word) (sp : Bool) (n : Word) (a : ArchCopyRegisterSets) :
    NQKE Kq (invokeTcb (Z := Unit) (.readRegisters s sp n a)) := by
  simp only [invokeTcb]; nq2_auto

set_option maxHeartbeats 8000000 in
theorem nq_invokeTcb_copy (d s : Word) (b1 b2 b3 b4 : Bool) (a : ArchCopyRegisterSets) :
    NQKE Kq (invokeTcb (Z := Unit) (.copyRegisters d s b1 b2 b3 b4 a)) := by
  simp only [invokeTcb]; nq2_auto

theorem nq_invokeTcb_caps (t : Word) (sl : CslotPtr) (fh th cr vr : Option (Cap × CslotPtr))
    (bf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    NQKE Kq (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr bf)) := by
  simp only [invokeTcb]; nq2_auto

theorem nq_invokeTcb_suspend (t : ObjRef) : NQKE Kq (invokeTcb (Z := Unit) (.suspend t)) := by
  simp only [invokeTcb]; nq2_auto

theorem nq_invokeTcb_resume (t : ObjRef) : NQKE Kq (invokeTcb (Z := Unit) (.resume t)) := by
  simp only [invokeTcb]; nq2_auto

theorem nq_invokeTcb_ntfn (t : ObjRef) (n : Option ObjRef) : NQKE Kq (invokeTcb (Z := Unit) (.notificationControl t n)) := by
  cases n <;> simp only [invokeTcb] <;> nq2_auto

theorem nq_invokeTcb_tls (t : ObjRef) (b : Word) : NQKE Kq (invokeTcb (Z := Unit) (.setTLSBase t b)) := by
  simp only [invokeTcb]; nq2_auto

theorem nq_invokeTcb_flags (t : ObjRef) (c s : TcbFlags) : NQKE Kq (invokeTcb (Z := Unit) (.setFlags t c s)) := by
  simp only [invokeTcb]; nq2_auto

/-- ThreadControlSched: `set_priority` may move its target (BlockedOnSend /
BlockedOnReceive) in its endpoint queue, so only the target leaves `K`. -/
theorem nq_invokeTcb_sched (target : Word) (slot : CslotPtr) (fh : Option (Cap × CslotPtr))
    (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef)) :
    HKE (NQ Kq) (NQ (Kq.filter (· ≠ target))) (invokeTcb (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) := by
  cases prio with
  | none =>
    refine fun σ hσ y hy => nq_filter_of ((?_ : NQKE Kq (invokeTcb (Z := Unit)
      (.threadControlSched target slot fh mcp none sc))) σ hσ y hy)
    simp only [invokeTcb, NonDet.maybeM]
    nq2_auto
  | some p =>
    obtain ⟨p1, p2⟩ := p
    simp only [invokeTcb, NonDet.maybeM]
    refine hke_bind (hk_of_ik (by nq2_auto)) (fun _ => ?_) nq_filter_post
    refine hke_bind (hk_of_ik (by nq2_auto)) (fun _ => ?_) nq_filter_post
    exact hke_bind (R := NQ (Kq.filter (· ≠ target))) (hk_liftE (nq_setPriority target p1))
      (fun _ => hk_of_ik (by nq2_auto)) (fun _ h => h)

/-- `invoke_tcb`: only a ThreadControlSched target may leave `K`. -/
theorem nq_invokeTcb (a0 : TcbInvocation) : HKE (NQ Kq) (NQ []) (invokeTcb (Z := Unit) a0) := by
  cases a0
  case threadControlSched target slot fh mcp prio sc =>
    exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_sched target slot fh mcp prio sc σ hσ y hy)
  case writeRegisters => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_wr _ _ _ _ σ hσ y hy)
  case readRegisters => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_rd _ _ _ _ σ hσ y hy)
  case copyRegisters => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_copy _ _ _ _ _ _ _ σ hσ y hy)
  case threadControlCaps => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_caps _ _ _ _ _ _ _ σ hσ y hy)
  case suspend => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_suspend _ σ hσ y hy)
  case resume => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_resume _ σ hσ y hy)
  case notificationControl => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_ntfn _ _ σ hσ y hy)
  case setTLSBase => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_tls _ _ σ hσ y hy)
  case setFlags => exact fun σ hσ y hy => nq_weak_nil _ (nq_invokeTcb_flags _ _ _ σ hσ y hy)


end

end Fl4Proofs.P3.SInv
