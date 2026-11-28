/-
P3 (p3J gen 36): **the arch caps are unreachable in `midDecRest` / `invDecRest`, and the Domain cap's decode leaf
is proved for both classes** (one leaf, generic in the flags).

* **Arch caps.** `absCap` sends every FL4 arch cap (Frame, PageTable, PageDirectory, Pdpt, Pml4, Vcpu, Ept,
  AsidControl, AsidPool, IoPortControl, IoPort, TdxControl) to the spec's `archObjectCap` (CapRel `absCap`), which
  `SInvCk.KW` excludes (P3JCkW `KW`: `archObjectCap _ => False`). So among the caps `KW ∧ ¬ Reply ∧ ¬ Easy ∧ ¬ Ep`
  only CNode, Thread, IrqHandler, Domain and SchedContext are left (`restCap_of`). (Gen 34 / 35's lists of the
  remaining caps named the arch caps too; they never needed a leaf: on a `CKI` state the looked-up cap is `KW`.)
* **`decDomSt`** (the leaf at a dispatch state, any `blk` / `call` / `don` / `fp`): DomSched's
  `decode_invocation_domainXS` (XTopJointStep's `decode_invocation_domainJ_step` route) at
  `X := JStab (Z.mv Z.G V') H Cs ∧ WritesIn s' · (ProjW H Cs s')`: the decode errors at the dispatch state itself,
  every success outcome a run of primitive steps, closed by P3JStepFt's **`Steps.jatZW`** (`JAtZ` and the `ProjW`
  footprint; `ZNoBlk` from `SpecGlob` by `JAtZ.zNoBlk`). `DomConfig` is `numDomains = 1` (the tops' `hnd`); the
  label, the arguments and the extra caps from the front facts (`JAtZ.frontJ`, `JAtZ.argsJ`), the canonical label
  (`dom_canon`, `XCapP.lbl_congr`), `MR` by `XCapP.mrT` (a Domain cap is `QuietF`), never preempted.
* **`midDecDom_of`** / **`invDecDom_of`**: `MidDecStW` / `InvDecStW` at `KW ∧ · = .Domain` (the dispatch state's
  `Entered` and `SpecGlob` from `SInvX` and `BudgetAt`: `BudgetAt.entered`, `BudgetAt.shape27`, `specGlob_disp`).
* `midDecRest_of_dom` / `invDecRest_of_dom`: gen 35's `midDecRest` / `invDecRest` predicates from the Domain leaf
  and the four left (`IsRestCap`: CNode, Thread, IrqHandler, SchedContext).
* **`DispStabFootLo` [J]** {invDecRest, midDecRest at `KW ∧ IsRestCap`, midSpec, midRecvSw};
  **`dispStabFootLj_of_Lo`** (reads `ARIface`, a premise every top already has), top
  **`kernel_entry_runMcWKR_sysLo`** (globals as `_sysLj`).

Premise honesty: `DispStabFootLo.invDecRest` / `.midDecRest` are `DispStabFootLj`'s at a smaller cap predicate
(`IsRestCap cp → ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp`; `InvDecStW` / `MidDecStW` antitone), the other
two fields verbatim, so `DispStabFootLo` is implied by `DispStabFootLj` (and conversely by
`dispStabFootLj_of_Lo`, given the tops' platform facts).

Named premise: `DispStabFootLo` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStepFt
import Fl4Proofs.P3.P3JInvLeaf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 36) The caps left after Reply / Null / Zombie / Notification / Endpoint / Domain among the `KW` caps. -/
def IsRestCap : capability.Cap → Prop
  | .CNode .. => True
  | .Thread _ => True
  | .IrqHandler _ => True
  | .SchedContext .. => True
  | _ => False

/-- (p3J gen 36) **Only CNode / Thread / IrqHandler / Domain / SchedContext are left** (module docstring). -/
theorem restCap_of {cp : capability.Cap} (hK : SInvCk.KW (absCap cp)) (hR : ¬ IsReplyCap cp) (hE : ¬ IsEasyCap cp)
    (hP : ¬ IsEpCap cp) (hD : cp ≠ .Domain) : IsRestCap cp := by
  cases cp <;> simp_all [SInvCk.KW, absCap, IsReplyCap, IsEasyCap, IsEpCap, IsRestCap]

theorem restCap_not {cp : capability.Cap} (h : IsRestCap cp) :
    ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp := by
  cases cp <;> simp_all [IsReplyCap, IsEasyCap, IsEpCap, IsRestCap]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 36) **The Domain cap's decode at a dispatch state, any flags** (module docstring). -/
theorem decDomSt (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsg : SpecGlob σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) .Domain bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hq : QuietF .Domain := by simp [QuietF]
  refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
    (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  obtain ⟨sl', hl', hd⟩ := dom_canon info.label
  refine XCapP.lbl_congr arI (specDec_dom hd) ?_
  have hX := J.xtop
  have hex := ExtraOK.relS hX.rel.1 (hXO e exs he hexs)
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hP := hX.fin.1.2
  have hkf : (L.ksb s').val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hC := J.curRun.run hnib
  have hAc : Notif.ActReady σb := J.inv.actReady
  refine XCap.toPN arI ?_ (specDec_noPreK (by trivial))
  exact decode_invocation_domainXS arI ⟨hnd⟩ _ hX.rel.1 s' a' σb _ hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 ct hct
    hcur (hX.curTcb hcur).1 J.kern.act hkf hP.vs.ksb_al J.ksOut J.actK info.label sl' hl' (msgLen info buf) buf
    argsU hLen hArgs e _ (exAt_idx0 e) exs hex (domSetHyp_of hX J.thT hC hAc hcur)
    (domResHyp_of hX J.ks J.thT hC hAc hcur) (domStallHyp_of arI hX.fin.1.1.1 J.thT) hC hX0
    (fun _ _ _ h => by
      obtain ⟨⟨G', V'', Ac'', Lst'', D'', J', -⟩, hw⟩ :=
        Steps.jatZW arI hARI.toMask (jStepHyps arI) h rfl J (J.zNoBlk hsg)
      exact ⟨⟨G', V'', Ac'', Lst'', D'', J'⟩, hw⟩)
    (fun _ _ _ h => by obtain ⟨⟨_, _, _, _, _, J'⟩, -⟩ := h; exact ⟨_, J'.xtop⟩)
    (cslotAddr sl) bl call don fp ci sl buffer

/-- (p3J gen 36) The dispatch state's `Entered` and `SpecGlob` (module docstring). -/
theorem dispEnteredSg (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hX : SInvX σ)
    (hni : σ.curThread ≠ σ.idleThread) (hBA : BudgetAt σ σb true) : Entered σb ∧ SpecGlob σb := by
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib : Entered σb := BudgetAt.entered hnd hk0 (hX.entered hni) hBA
  obtain ⟨-, ek, -, en0, ei0, -⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  exact ⟨hnib, specGlob_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    (SInvR.G5.sinvX_sg hX) hk0 rfl ek' en0 ei0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 36) **The mid decode leaf of the Domain cap** (module docstring). -/
theorem midDecDom_of (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ cp = .Domain) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, rfl⟩ := hW
  obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
  exact decDomSt hA hnd hARI hMT hKD J hnib hsg hMb hct a1 a2 a3 a4 a5 a6 a7 sl he hexs _ _ _ _ _

set_option maxHeartbeats 4000000 in
/-- (p3J gen 36) **The invoking class's decode leaf of the Domain cap** (module docstring). -/
theorem invDecDom_of (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) :
    InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ cp = .Domain) Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, rfl⟩ := hW
  obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
  exact decDomSt hA hnd hARI hMT hKD J hnib hsg hMb hct a1 a2 a3 a4 a5 a6 a7 sl he hexs _ _ _ _ _

/-- (p3J gen 36) **gen 35's `midDecRest` from the Domain leaf and the four left** (module docstring). -/
theorem midDecRest_of_dom (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap cp) Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR
      (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hD : cp = .Domain
  · exact midDecDom_of hA hnd hARI hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hD⟩
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs
      ⟨hW.1, restCap_of hW.1 hW.2.1 hW.2.2.1 hW.2.2.2 hD⟩

/-- (p3J gen 36) **gen 35's `invDecRest` from the Domain leaf and the four left** (module docstring). -/
theorem invDecRest_of_dom (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap cp) Z H Cs s a σ n call bl don) :
    InvDecStW (L := L) arI AR MR
      (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hD : cp = .Domain
  · exact invDecDom_of hA hnd hARI hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hD⟩
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs
      ⟨hW.1, restCap_of hW.1 hW.2.1 hW.2.2.1 hW.2.2.2 hD⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 36) **`DispStabFootLo` [J]**: `DispStabFootLj` with `invDecRest` / `midDecRest` restricted to the CNode,
Thread, IrqHandler and SchedContext caps (module docstring). -/
structure DispStabFootLo (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLj.invDecRest` for the caps `IsRestCap`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap cp) Z H Cs s a σ n call bl don
  /-- `DispStabFootLj.midDecRest` for the caps `IsRestCap`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap cp) Z H Cs s a σ n c
  /-- `DispStabFootLj.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLj.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 36) **`DispStabFootLo → DispStabFootLj`** (module docstring). -/
theorem dispStabFootLj_of_Lo (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLo (L := L) arI AR MR s a σ) :
    DispStabFootLj (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact invDecRest_of_dom hA hnd hARI (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midDecRest_of_dom hA hnd hARI (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 36) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLo` only** (`hLo` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLo [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLo : DispStabFootLo (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLj hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLj_of_Lo hARI hA hnd hM hIp hKD hLo)

end

end Fl4Proofs.P3.Mc
