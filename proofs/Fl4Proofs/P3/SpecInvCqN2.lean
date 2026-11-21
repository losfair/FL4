/-
P3 (DESIGN.md §9), invariant line G1 (ctq17): **the invocation shell keeps
the ready-queue bundle** (spec side only, outside the JAtZ cone; KENTRY-PLAN
ctq15 handoff 1-2).

* Item 2: ctq12's four deletion-cone hypotheses are ctq14's theorems
  (`R14.ebCapDeleteH` …): `eb_fl4PerformInvocationT`, `eb_restartPerformT`.
* `RQ Q y`: the outcome `y` has `EB false`, and `Q` when it is `ok` (ctq12's
  `HKEr` pointwise); `syscall_r` is SpecInvDom's `syscall_post'` with a
  result-sensitive post.
* `SH C N S`: the facts the shell carries from the event start to the
  decode's outcome state: ctq12's `DK C` (EB true, ct = C, no switch
  pending, NQ [C]), sb2's ScInv, vi3's `VI N S false` (the idle TCB in its
  idle state, `idleThread = N`), ctq11's `RT`, `UtInv''`, il2's `IL [C]`.
  `sh_of`: one generated leaf family each (`sh_auto`), the no-switch half by ctq18's generated `Simple` family (SpecInvCqEr0, `R18.SMK`).
* **`eb_fl4HandleInvocationR`**: from `SH C N S` and `C ≠ N`, every outcome
  of `fl4HandleInvocationR` has `EB false`, an `ok` one `EB fp`. The fault
  branch is `handle_fault` (ctq7's `eb_handleFault_p`; not run in the first
  phase: `hfb`), the error branch the error reply, the decode's outcome gets
  SpecInvCqM5's `PD` (decode facts `okd_fp` / `okd_tcbP` / `okd_sc` /
  `okq_fl4Decode` / `okd_fl4Decode`, ut8's `okv_fl4DecodeG` for `GapOKN`),
  then `eb_restartPerformT`, then the post (`get_thread_state`; Restart:
  the reply and `set_thread_state ct Running`).
-/
import Fl4Proofs.P3.SpecInvCqM5
import Fl4Proofs.P3.SpecInvCqEr0
import Fl4Proofs.P3.SpecInvCqH2
import Fl4Proofs.P3.SpecInvViG6
import Fl4Proofs.P3.SpecInvNtfnQL5
import Fl4Proofs.P3.SpecInvNtfnQF5
import Fl4Proofs.P3.SpecInvNtfnQC4
import Fl4Proofs.P3.SpecInvSbF4
import Fl4Proofs.P3.SpecInvUtF4
import Fl4Proofs.P3.SpecInvUtP6
import Fl4Proofs.P3.SpecInvUtO5
import Fl4Proofs.P3.SpecInvCqGF5
import Fl4Proofs.P3.SpecInvCqRF4
import Fl4Proofs.P3.SpecInvCqSF4
import Fl4Proofs.P3.SpecInvCqYF4
import Fl4Proofs.P3.SpecInvQDom
open Classical

namespace Fl4Proofs.P3.SInvQ.P17
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13 Fl4Proofs.P3.SInvQ.P15 Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Item 2: the deletion cone -/

/-- ctq15's `eb_fl4PerformInvocation` with ctq14's deletion-cone theorems. -/
theorem eb_fl4PerformInvocationT (C N : ObjRef) (fp bl call don : Bool) (inv : Fl4Invocation)
    (hfp : fp = true → FPArm inv) :
    HKEr (PF C N inv) (EB fp) (fl4PerformInvocation (Z := Unit) bl call don inv) :=
  eb_fl4PerformInvocation R14.ebCapDeleteH R14.ebCapRevokeH R14.ebCapDeleteOneH R14.ebCancelBadgedSendsH
    C N fp bl call don inv hfp

/-- ctq15's `eb_restartPerform` with ctq14's deletion-cone theorems. -/
theorem eb_restartPerformT (C N : ObjRef) (fp bl call don : Bool) (inv : Fl4Invocation)
    (hfp : fp = true → FPArm inv) (s : State Unit) (h : PD C N inv s) :
    ∀ w ∈ (setThreadState (Z := Unit) C .restart s).1,
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don inv).run w.2).1,
        EB false y.2 ∧ (∀ a, y.1 = .ok a → EB fp y.2) :=
  eb_restartPerform R14.ebCapDeleteH R14.ebCapRevokeH R14.ebCapDeleteOneH R14.ebCancelBadgedSendsH
    C N fp bl call don inv hfp s h

/-! ## The result-sensitive post and `syscall` -/

/-- Every outcome `EB false`, an `ok` one `Q`. -/
abbrev RQ (Q : State Unit → Prop) {ε α : Type} (y : Except ε α × State Unit) : Prop :=
  EB false y.2 ∧ ∀ a, y.1 = .ok a → Q y.2

/-- The `syscall` shell with a post on the whole outcome. -/
theorem syscall_r {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ : State Unit} {I : State Unit → Prop} {Q : Except Unit γ × State Unit → Prop}
    (h1 : ∀ w ∈ ((ExceptT.run mF) σ).1, I w.2)
    (h2 : ∀ f s, I s → ∀ v ∈ (hF f s).1, Q (.ok v.1, v.2))
    (h3 : ∀ a s, (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → ∀ w ∈ ((ExceptT.run (mE a)) s).1, I w.2)
    (h4 : ∀ e s, I s → ∀ v ∈ (hE e s).1, Q (.ok v.1, v.2))
    (h5 : ∀ a s b s', (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → (.ok b, s') ∈ ((ExceptT.run (mE a)) s).1 →
      I s' → ∀ y ∈ ((mFin b).run s').1, Q y) :
    ∀ y ∈ ((syscall mF hF mE hE mFin).run σ).1, Q y := by
  intro y hy
  unfold syscall withoutPreemption at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
      exact h2 f s (h1 _ hw) v hv
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
      · obtain ⟨w, hw', rfl⟩ := ft_mem_liftE hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
          exact h4 e s' (h3 a s hw _ hw') v hv
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy
      · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
        cases he
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-! ## The shell's carried facts -/

/-- **The facts the shell carries to the decode's outcome.** -/
abbrev SH (C N S : ObjRef) (s : State Unit) : Prop :=
  DK C s ∧ SInvB.ScInv s ∧ SInvI.VI N S false s ∧ R11.RT s ∧ SInvU.UtInv'' s ∧ IL [C] s

theorem sh_of {α : Type} {C N S : ObjRef} {m : NonDet (State Unit) α} (h1 : EBK true m) (h2 : IK (CTh C) m)
    (h3 : R18.SMK m) (h4 : IK (NQ [C]) m) (h5 : ∀ h0, IK (SInvB.BRs h0) m) (h6 : IK (SInvI.VI N S false) m)
    (h7 : IK R11.RT m) (h8 : ∀ v, IK (fun σ => SInvU.uV σ = v) m) (h9 : IK (IL [C]) m) :
    IK (SH C N S) m := by
  intro σ hσ y hy
  obtain ⟨⟨hE, hC, hS, hN⟩, hI, hV, hR, hU, hL⟩ := hσ
  refine ⟨⟨h1 σ hE y hy, h2 σ hC y hy, h3 σ hS y hy, h4 σ hN y hy⟩,
    SInvB.scInv_of_br hI (h5 σ.kheap σ (SInvB.BR.refl _) y hy), h6 σ hV y hy, h7 σ hR y hy, ?_, h9 σ hL y hy⟩
  show SInvU.UtInv''V (SInvU.uV y.2)
  rw [h8 (SInvU.uV σ) σ rfl y hy]; exact hU

macro "sh_auto" : tactic => `(tactic| exact sh_of (by eb_auto) (by ct_auto) (by sm_auto) (by nq2_auto)
  (fun _ => by sb_auto) (by vi_auto) (by rt_auto) (fun _ => by uk_auto) (by il_auto))

/-- The idle TCB's state from `VI`. -/
theorem idleSt_of_vi {N S : ObjRef} {s : State Unit} (hV : SInvI.VI N S false s) :
    ∀ x, s.kheap s.idleThread = some (.tcb x) → x.tcbState = .idleThreadState := by
  intro x hx
  have h := SInvI.vi_obj hV hx
  simp only [SInvI.ObjOK] at h
  exact (h.1 hV.1).1

/-! ## The shell -/

set_option maxHeartbeats 16000000 in
/-- **The invocation shell**: from `SH C N S` (and `C ≠ N`), every outcome has
`EB false`, an `ok` one `EB fp` (the first phase never blocks: `hfb`). -/
theorem eb_fl4HandleInvocationR (hnd : numDomains = 1) (C N S : ObjRef) (rep calling blocking don fp : Bool)
    (cptr : CapRef) (hfb : fp = true → blocking = false) (hCN : C ≠ N) (σ : State Unit) (hσ : SH C N S σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, RQ (EB fp) y := by
  unfold fl4HandleInvocationR
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
  obtain rfl := mem_gets hw
  simp only [Except.ok.injEq] at ha; subst ha
  have hc : σ.curThread = C := hσ.1.2.1
  simp only [hc] at hy
  obtain ⟨z, hz, ⟨info, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · unfold withoutPreemption at hz; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he
  unfold withoutPreemption at hz
  obtain ⟨w0, hw0, rfl⟩ := ft_mem_liftE hz
  simp only [Except.ok.injEq] at ha; subst ha
  have hσ1 : SH C N S w0.2 := (show IK (SH C N S) (getMessageInfo (Z := Unit) C) by sh_auto) σ hσ w0 hw0
  have hF : IKE (SH C N S) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) C cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false C
       let extracaps ← lookupExtraCaps C buffer w0.1
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by sh_auto
  have hFu : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) C cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false C
       let extracaps ← lookupExtraCaps C buffer w0.1
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hOk : OkV (uV w0.2) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV w0.2).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV w0.2).2.1 p.2 = some p.1 ∧ DestRefV (uV w0.2) p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) C cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false C
       let extracaps ← lookupExtraCaps C buffer w0.1
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_r (I := SH C N S) (Q := RQ (EB fp)) (fun v hv => hF w0.2 hσ1 v hv) ?_ ?_ ?_ ?_ y hy
  · -- the fault branch
    intro f s hs v hv
    have hE : EB fp v.2 := by
      cases fp
      · unfold NonDet.when at hv
        split at hv
        · have hT : NPQ C s := by have h := npq_ct hs.1.1; rwa [hs.1.2.1] at h
          exact eb_handleFault_p (k := false) (K := [C]) C f s hT hs.1.2.2.2
            (by rw [hs.1.2.1]; exact List.mem_singleton_self C) (eb_weak hs.1.1) v hv
        · rw [Set.mem_singleton_iff.1 hv]; exact eb_weak hs.1.1
      · have hb := hfb rfl
        subst hb
        unfold NonDet.when at hv
        split at hv
        · rename_i h; exact absurd h (by decide)
        · rw [Set.mem_singleton_iff.1 hv]; exact hs.1.1
    exact ⟨eb_weak hE, fun _ _ => hE⟩
  · -- the lookups, then `get_mrs` and the decode
    intro a s has w hw
    have hs : SH C N S s := hF w0.2 hσ1 _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (SH C N S) _) s hs w hw
    sh_auto
  · -- the error reply
    intro e s hs v hv
    have hE : EB true v.2 := (show EBK true (NonDet.when calling <|
      fl4ReplyFromKernelError (Z := Unit) rep C (msgFromSyscallError e)) by eb_auto) s hs.1.1 v hv
    exact ⟨eb_weak hE, fun _ _ => ebk_of_true hE⟩
  · -- the decode's outcome: the Restart write, the perform, the post
    intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hfpA : fp = true → FPArm b :=
      okdAt_bind (P := fun _ inv => fp = true → FPArm inv) (fun _ s1 _ => okd_fp fp _ _ _ _ _ _ _ s1) b s' hbs
    have hT : TcbP b :=
      okdAt_bind (P := fun _ inv => TcbP inv) (fun _ s1 _ => okd_tcbP fp _ _ _ _ _ _ _ s1) b s' hbs
    have hSc : ScD s' b :=
      okdAt_bind (P := fun s inv => ScD s inv) (fun _ s1 _ => okd_sc fp _ _ _ _ _ _ _ s1) b s' hbs
    have h0 : SetDom0 b :=
      okdAt_bind (P := fun _ inv => SetDom0 inv) (fun _ s1 _ => okq_fl4Decode hnd _ _ _ _ _ _ _ _ s1) b s' hbs
    have hDo : DomInvOK s' b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode hnd _ _ _ _ _ _ _ _ s1) b s' hbs
    -- GapOKN from the decode, as ctq11's rt_fl4HandleInvocationR
    have hvs : uV s = uV w0.2 := hFu _ w0.2 rfl _ has
    obtain ⟨hcap, hex⟩ := hOk w0.2 rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV w0.2 := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hv' : uV s' = uV w0.2 :=
      (uk_fl4DecodeInvocation (uvw := uV x0.2) _ _ _ _ _ _ _ _ x0.2 rfl _ hb0).trans hvx
    have hG0 : GapOKN (uV w0.2) b :=
      okv_fl4DecodeG fp _ _ _ _ _ _ _ hcap (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    have hG : GapOKN (uV s') b := by rw [hv']; exact hG0
    have hPD : PD C N b s' := ⟨hI.1, hI.2.1, idleSt_of_vi hI.2.2.1, hI.2.2.1.1, hCN, hI.2.2.2.1,
      hI.2.2.2.2.1, hI.2.2.2.2.2, hT, hSc, h0, hDo, hG⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
    swap
    · unfold withoutPreemption at hz; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he
    unfold withoutPreemption at hz
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
    · have hP := eb_restartPerformT C N fp blocking calling don b hfpA s' hPD w hw z2 hz2
      have hE2 : EB fp z2.2 := hP.2 rp hr
      unfold withoutPreemption at hy
      obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
      obtain ⟨v1, hv1, hv⟩ := hv
      have e1 : EB fp v1.2 := (show EBK fp (getThreadState (Z := Unit) C) by eb_auto) _ hE2 v1 hv1
      obtain ⟨st, s3⟩ := v1
      have hE3 : EB fp v.2 := by
        cases st
        all_goals dsimp only at hv e1
        all_goals first
          | (rw [Set.mem_singleton_iff.1 hv]; exact e1)
          | (obtain ⟨v2, hv2, hv⟩ := hv
             exact eb_setThreadState_r C .running rfl _
               ((show EBK fp (NonDet.when calling (replyFromKernel (Z := Unit) C (0, rp))) by eb_auto)
                 _ e1 v2 hv2) v hv)
      exact ⟨eb_weak hE3, fun _ _ => hE3⟩
    · exact ⟨(eb_restartPerformT C N fp blocking calling don b hfpA s' hPD w hw z2 hz2).1,
        fun a h => by cases h⟩

end

end Fl4Proofs.P3.SInvQ.P17
