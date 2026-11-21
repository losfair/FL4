/-
P3 (DESIGN.md §9), invariant line G1 (ctq15): **every perform arm, one
statement** (spec side only, outside the JAtZ cone): `eb_fl4PerformInvocation`
dispatches on the invocation to ctq12 / ctq13 / ctq15's arm lemmas.

* `PF C N inv s`: the facts at the perform state — ctq12's `PE C` (DK: `EB
  true`, ct = `C`, no switch pending, NQ [C]; ScInv; `C` runnable (the shell's
  Restart write); the idle TCB in its idle state), sg1's `IdleIs N` with
  `C ≠ N`, ctq10's `ResSc`, `UtInv''`, `IfLiveTN` and the decode facts
  (`TcbP`, `ScD`: SpecInvCqM3; `SetDom0` / `DomInvOK`: SpecInvQDom's; ut8's
  `GapOKN`).
* Outcome: every outcome `EB false`, an `ok` one `EB fp` when `fp = true →
  FPArm inv` (SpecInvCqM3's `okd_fp`): the first-phase arms keep `EB true`
  (Endpoint, Notification, Reply, CNode / IRQ handler via DK) or `EB k`
  (IRQ control, Untyped, MakePool, the other arch arms); every other arm runs
  with `fp = false` and gives `EB false`.
* The four deletion-cone facts are taken as ctq12's named hypotheses
  (`EbCapDeleteH`, `EbCapRevokeH`, `EbCapDeleteOneH`, `EbCancelBadgedSendsH`):
  ctq14 proved them (SInvQ.R14 on int/j2 2961c236); the lead instantiates
  them at merge.
-/
import Fl4Proofs.P3.SpecInvCqM2
import Fl4Proofs.P3.SpecInvCqM3
open Classical

namespace Fl4Proofs.P3.SInvQ.P15
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13
  Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 2000000

theorem ebk_of_true {k : Bool} {s : State Unit} (h : EB true s) : EB k s := by
  cases k
  · exact eb_weak h
  · exact h

theorem eb_fin {fp : Bool} {inv : Fl4Invocation} {s : State Unit} (hfp : fp = true → FPArm inv) (hn : ¬ FPArm inv)
    (h : EB false s) : EB fp s := by
  cases fp
  · exact h
  · exact absurd (hfp rfl) hn

/-- **The facts at the perform state.** -/
abbrev PF (C N : ObjRef) (inv : Fl4Invocation) (s : State Unit) : Prop :=
  PE C s ∧ SInvG.IdleIs N s ∧ C ≠ N ∧ ResSc s ∧ SInvU.UtInv'' s ∧ IfLiveTN s ∧ TcbP inv ∧ ScD s inv ∧
    SetDom0 inv ∧ DomInvOK s inv ∧ SInvU.GapOKN (SInvU.uV s) inv

set_option maxHeartbeats 8000000 in
/-- **Every perform arm**: every outcome `EB false`, an `ok` one `EB fp`
(first-phase arms keep `EB true` / `EB k`). -/
theorem eb_fl4PerformInvocation (hD : EbCapDeleteH) (hR : EbCapRevokeH) (hO : EbCapDeleteOneH)
    (hB : EbCancelBadgedSendsH) (C N : ObjRef) (fp bl call don : Bool) (inv : Fl4Invocation)
    (hfp : fp = true → FPArm inv) :
    HKEr (PF C N inv) (EB fp) (fl4PerformInvocation (Z := Unit) bl call don inv) := by
  intro σ hσ y hy
  obtain ⟨hPE, hN', hCN, hRS, hU, hL, hT, hSc, h0, hDo, hG⟩ := hσ
  have hDK : DK C σ := hPE.1
  have hE : EB true σ := hDK.1
  have hS : Simple σ := hDK.2.2.1
  have hci : σ.curThread ≠ σ.idleThread := by
    have e1 : σ.curThread = C := hDK.2.1
    have e2 : σ.idleThread = N := hN'
    rw [e1, e2]; exact hCN
  have hRP : RPq σ := ⟨eb_weak hE, hS, hPE.2.1, hci⟩
  have hRn : RnH σ.curThread σ.kheap := by
    have e1 : σ.curThread = C := hDK.2.1
    rw [e1]; exact hPE.2.2.1
  -- an `EBKE fp` arm
  have kE : ∀ {m : NonDetE (State Unit) Unit (List Data)}, EBKE fp m → y ∈ (m.run σ).1 →
      EB false y.2 ∧ (∀ a, y.1 = .ok a → EB fp y.2) := fun h hm =>
    ⟨eb_weak (h σ (ebk_of_true hE) y hm), fun _ _ => h σ (ebk_of_true hE) y hm⟩
  cases inv with
  | invokeUntyped ui =>
    have q := eb_perfUntyped fp bl call don ui σ ⟨ebk_of_true hE, hU, hL, SInvU.utRetOK_of_V hG.1⟩ y hy
    exact ⟨eb_weak q, fun _ _ => q⟩
  | invokeEndpoint ep bd g gr =>
    have q := eb_perfEndpoint C bl call don ep bd g gr σ hPE y hy
    exact ⟨eb_weak q, fun _ _ => ebk_of_true q⟩
  | invokeNotification n bd =>
    obtain ⟨q1, q2⟩ := eb_perfNtfn C bl call don n bd σ hPE y hy
    exact ⟨q1, fun a ha => ebk_of_true (q2 a ha)⟩
  | invokeReply r g =>
    have q := eb_perfReply C bl call don r g σ hPE y hy
    exact ⟨eb_weak q, fun _ _ => ebk_of_true q⟩
  | invokeTCB i =>
    cases i with
    | writeRegisters dest b vs a =>
      have q := eb_perfWriteRegisters bl call don dest b vs a σ hRP y hy
      exact ⟨q, fun _ _ => eb_fin hfp (fun h => h) q⟩
    | readRegisters t b n a =>
      have q := eb_perfReadRegisters (k := fp) bl call don t b n a σ ⟨ebk_of_true hE, hS⟩ y hy
      exact ⟨eb_weak q, fun _ _ => q⟩
    | copyRegisters dest src sS rT tF tI a =>
      have q := eb_perfCopyRegisters bl call don dest src sS rT tF tI a σ hRP y hy
      exact ⟨q, fun _ _ => eb_fin hfp (fun h => h) q⟩
    | threadControlCaps target slot fh th cr vr buf =>
      obtain ⟨q1, q2⟩ := eb_perfTcbCaps hD C bl call don target slot fh th cr vr buf σ hDK y hy
      exact ⟨q1, fun a ha => ebk_of_true (q2 a ha).1⟩
    | threadControlSched target slot fh mcp prio sc =>
      obtain ⟨q1, q2⟩ := eb_perfTcbSched hD C N hCN bl call don target slot fh mcp prio sc hT σ ⟨hDK, hN'⟩ y hy
      exact ⟨q1, fun a ha => eb_fin hfp (fun h => h) (q2 a ha)⟩
    | suspend t =>
      have q := eb_perfSuspend (k := fp) bl call don t σ ⟨ebk_of_true hE, hS⟩ y hy
      exact ⟨eb_weak q, fun _ _ => q⟩
    | resume t =>
      have q := eb_perfResume bl call don t σ hRP y hy
      exact ⟨q, fun _ _ => eb_fin hfp (fun h => h) q⟩
    | notificationControl t n => exact kE (eb_perfNtfnControl bl call don t n) hy
    | setTLSBase t b => exact kE (eb_perfTls bl call don t b) hy
    | setFlags t c s => exact kE (eb_perfSetFlags bl call don t c s) hy
  | invokeFl4TCB i => exact kE (eb_perfFl4Tcb bl call don i) hy
  | invokeDomain i =>
    have q := eb_perfDomain bl call don i h0 σ ⟨eb_weak hE, hDo⟩ y hy
    exact ⟨q, fun _ _ => eb_fin hfp (fun h => h) q⟩
  | invokeSchedContext i =>
    cases i with
    | invokeSchedContextConsumed p => exact kE (eb_perfScConsumed bl call don p) hy
    | invokeSchedContextBind sc c =>
      have q := eb_perfScBind bl call don sc c σ ⟨eb_weak hE, fun t e => by
        obtain ⟨x, hx, hn⟩ := (hSc : ∀ t, c = .threadCap t → ∃ x, σ.kheap t = some (.tcb x) ∧
          x.tcbSchedContext = none) t e
        exact an_of_resSc hS hRS hx hn⟩ y hy
      exact ⟨q, fun _ _ => eb_fin hfp (fun h => h) q⟩
    | invokeSchedContextUnbindObject p c => exact kE (eb_perfScUnbindObject bl call don p c) hy
    | invokeSchedContextUnbind p => exact kE (eb_perfScUnbind bl call don p) hy
    | invokeSchedContextYieldTo sc =>
      have q := eb_perfScYieldTo bl call don sc σ ⟨hE, hS, hRn, hSc⟩ y hy
      exact ⟨q, fun _ _ => eb_fin hfp (fun h => h) q⟩
  | invokeSchedControl i =>
    obtain ⟨q1, q2⟩ := eb_perfSchedControl bl call don i σ ⟨eb_weak hE, hS⟩ y hy
    exact ⟨q1, fun a ha => eb_fin hfp (fun h => h) (q2 a ha)⟩
  | invokeCNode i =>
    obtain ⟨q1, q2⟩ := eb_perfCnode hD hR hB C bl call don i σ hDK y hy
    exact ⟨q1, fun a ha => ebk_of_true (q2 a ha).1⟩
  | invokeIRQControl i => exact kE (eb_perfIrqControl bl call don i) hy
  | invokeIRQHandler i =>
    obtain ⟨q1, q2⟩ := eb_perfIrqHandler hO C bl call don i σ hDK y hy
    exact ⟨q1, fun a ha => ebk_of_true (q2 a ha).1⟩
  | invokeArchObject ai =>
    cases ai with
    | spec i =>
      cases i with
      | invokeASIDControl a =>
        cases a with
        | makePool frame slot parent base =>
          have q := eb_perfMakePool fp bl call don frame slot parent base σ ⟨ebk_of_true hE, hU, hL, hG⟩ y hy
          exact ⟨eb_weak q, fun _ _ => q⟩
      | _ => exact kE (eb_perfArchNoPool bl call don _ (fun o h => by cases h)) hy
    | _ => exact kE (eb_perfArchNoPool bl call don _ (fun o h => by cases h)) hy

end

end Fl4Proofs.P3.SInvQ.P15
