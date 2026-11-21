/-
P3 (DESIGN.md §9), invariant line G1 (ctq15): **the perform-state facts from
the decode state**: the invocation shell's `set_thread_state ct Restart`
takes `PD C N inv` (the carried facts and the decode facts at the decode's
outcome state) to SpecInvCqM4's `PF C N inv` (`pf_restart`), and
`eb_restartPerform` composes it with `eb_fl4PerformInvocation`.

Across the Restart write: `EB true` (runnable state), ct (`CTh`), no switch
pending (`NSw`), NQ [C] (nq's `nq_setThreadState`, Restart blocks on no
notification), ScInv along sb2's binding frame, `C` a runnable TCB
(`q3_setThreadState_out`), the idle TCB's state (sch11's `KF N`, `C ≠ N`),
`IdleIs N`, ctq11's `RT` (hence `ResSc`), the untyped view (`UtInv''`,
`GapOKN`), il2's `IL [C]` (hence `IfLiveTN`), the domain list (`DomInvOK`),
`ScD` (`scD_of_br`); `TcbP` / `SetDom0` do not mention the state.
-/
import Fl4Proofs.P3.SpecInvCqM4
import Fl4Proofs.P3.SpecInvCqGS
open Classical

namespace Fl4Proofs.P3.SInvQ.P15
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13
  Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 2000000

/-- **The facts at the decode's outcome state.** -/
abbrev PD (C N : ObjRef) (inv : Fl4Invocation) (s : State Unit) : Prop :=
  DK C s ∧ SInvB.ScInv s ∧ (∀ x, s.kheap s.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) ∧
    SInvG.IdleIs N s ∧ C ≠ N ∧ R11.RT s ∧ SInvU.UtInv'' s ∧ IL [C] s ∧ TcbP inv ∧ ScD s inv ∧ SetDom0 inv ∧
    DomInvOK s inv ∧ SInvU.GapOKN (SInvU.uV s) inv

/-- The idle TCB's state across a state write of another thread. -/
theorem idleSt_keep {C N : ObjRef} (hCN : C ≠ N) (ts : ThreadState) {s : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) C ts s).1) (hN : s.idleThread = N) (hN' : y.2.idleThread = N)
    (h : ∀ x, s.kheap s.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) :
    ∀ x, y.2.kheap y.2.idleThread = some (.tcb x) → x.tcbState = .idleThreadState := by
  intro x hx
  rw [hN'] at hx
  have ef := MidRun.kf_setThreadState (ct := N) C ts hCN s y hy
  unfold MidRun.ctV at ef
  have ef2 := (Prod.mk.inj ef).2
  rw [hx] at ef2
  cases h3 : s.kheap N with
  | none => rw [h3] at ef2; simp [MidRun.tsV] at ef2
  | some o =>
    rw [h3] at ef2
    cases o <;> simp [MidRun.tsV] at ef2
    rename_i x0
    rw [ef2.1]
    exact h x0 (by rw [hN, h3])

/-- **`set_thread_state ct Restart` takes `PD` to `PF`.** -/
theorem pf_restart (C N : ObjRef) (inv : Fl4Invocation) (s : State Unit) (h : PD C N inv s) :
    ∀ y ∈ (setThreadState (Z := Unit) C .restart s).1, PF C N inv y.2 := by
  intro y hy
  obtain ⟨hDK, hI, hId, hN', hCN, hRT, hU, hIL, hT, hSc, h0, hDo, hG⟩ := h
  have hE : EB true y.2 := eb_setThreadState_r (k := true) C .restart rfl s hDK.1 y hy
  have hC : CTh C y.2 := Fl4Proofs.P3.SInvQ.ct_setThreadState C C .restart s hDK.2.1 y hy
  have hS : Simple y.2 := fun u =>
    (show IK (NSw u) (setThreadState (Z := Unit) C .restart) by unfold setThreadState; p12_nsw_auto)
      s (hDK.2.2.1 u) y hy
  have hNQ : NQ [C] y.2 := nq_setThreadState C .restart (List.mem_singleton_self C) (fun h => h) s hDK.2.2.2 y hy
  have hb : SInvB.BR s.kheap y.2.kheap :=
    SInvB.sb_setThreadState (h0 := s.kheap) C .restart s (SInvB.BR.refl _) y hy
  obtain ⟨x, -, hx'⟩ := q3_setThreadState_out hy
  have hN1 : SInvG.IdleIs N y.2 := SInvG.idk_setThreadState C .restart s hN' y hy
  have hv : SInvU.uV y.2 = SInvU.uV s := SInvU.uk_setThreadState (v := SInvU.uV s) C .restart s rfl y hy
  refine ⟨⟨⟨hE, hC, hS, hNQ⟩, SInvB.scInv_of_br hI hb, ⟨_, hx', rfl⟩,
    idleSt_keep hCN .restart hy hN' hN1 hId⟩, hN1, hCN,
    R11.resSc_of_rt (R11.rt_setThreadState C .restart s hRT y hy), ?_, ?_, hT,
    scD_of_br hSc (hC.trans hDK.2.1.symm) hb, h0,
    domInvOK_of_dlV (SInvDom.dl_setThreadState C .restart s y hy) hDo, ?_⟩
  · show SInvU.UtInv''V (SInvU.uV y.2); rw [hv]; exact hU
  · exact ifLiveTN_of_ifLiveT (il_setThreadState (K := [C]) C .restart (fun _ => List.mem_singleton_self C)
      s hIL y hy).1
  · rw [hv]; exact hG

/-- **The Restart write then the perform**: every outcome `EB false`, an `ok`
one `EB fp` (first phase: an `FPArm` invocation). -/
theorem eb_restartPerform (hD : EbCapDeleteH) (hR : EbCapRevokeH) (hO : EbCapDeleteOneH)
    (hB : EbCancelBadgedSendsH) (C N : ObjRef) (fp bl call don : Bool) (inv : Fl4Invocation)
    (hfp : fp = true → FPArm inv) (s : State Unit) (h : PD C N inv s) :
    ∀ w ∈ (setThreadState (Z := Unit) C .restart s).1,
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don inv).run w.2).1,
        EB false y.2 ∧ (∀ a, y.1 = .ok a → EB fp y.2) :=
  fun w hw => eb_fl4PerformInvocation hD hR hO hB C N fp bl call don inv hfp w.2 (pf_restart C N inv s h w hw)

end

end Fl4Proofs.P3.SInvQ.P15
