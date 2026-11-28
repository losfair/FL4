/-
P3 (p3J gen 46): **the Thread cap's decode leaf at stable ghosts at SetSpace (11), for both classes, with the
stable preempted exit**: the first install label closed. FL4 `tcb.rs` `decode_set_space` / `thread_control_caps`
(the fault handler's and the two roots' installs, each a `delete_one` of the TCB slot + `cap_insert`) at
P3JDelSp's `tcb_set_spaceJSt` (XTopJointMRTcbM's `tcb_set_spaceJMG` at the stable installs' `TcbInsWG`).
The rest set {CNode at Revoke / Delete, Thread at 5, 8–10, or SetEPTRoot}.

* The start's facts at a dispatch state: `Entered` / `SpecGlob` (`dispEnteredSg`), `PPR0` (P3JCapIrq's
  `ppr0_disp`), `LiveDN` (`JAtZ.live`), `NativeScope` (`BudgetAt.nativeScopeM`), `ValidMachineTime` (`BudgetAt.vmt`),
  **`BudgetAt.vimD`** (`ValidIrqMasks`, SInvA's `vim` across the FaultIP write and the budget step), `MR`, `CKI`,
  `RR` (`MidDecStWL`'s intro hypotheses), and **`ncHyp_of_cki`** (no untyped cap in a slot at a `CKI` state, so
  `NcHyp` is vacuous; `kw_not_ut`).
* **`decThSspSt`** (any flags): the dispatch leaf (`XcRel` by `ExtraOK.xc`, the arguments by `JAtZ.argsJ`).
* `ThHard18 l`: `ThHard17 l ∧ l ≠ TCBSetSpace`. `IsRestCap26`. `restCap25_of26`, `restCap26_of`.
  **`midDecRest25_of_ssp`** / **`invDecRest25_of_ssp`**, `midDecStWL_of_25` / `invDecStWL_of_25`.
* **`DispStabFootLzs` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap26`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzr_of_Lzs`** (under the tops' platform facts and `IrqPlatK`), **`dispStabFootLzs_of_Lzr`**; top
  **`kernel_entry_runMcWKR_sysLzs`**: `_sysLzr`'s globals plus **`IrqPlatK` [P]** (`take_pending_irq` /
  `ack_irq` keep `AR`): a preempted SetSpace runs `after_invocation`'s `check_interrupt` (P3JPreSt's
  `JHole.afterInvSt`), which takes and acknowledges a pending line; the stable interrupt top
  `kernel_entry_runMcWKR_irqJ` already takes the same platform fact.

Premise honesty: `DispStabFootLzs`'s decode fields are `DispStabFootLzr`'s at the smaller antecedent
(`IsRestCap26 → IsRestCap25`), midSpec / midRecvSw verbatim; both directions proved (`_of_Lzs` under the platform
facts, `_of_Lzr` unconditionally).

Named premises: `DispStabFootLzs` [J]; global `IrqPlatK` [P] (above). No sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JThFpuR
import Fl4Proofs.P3.P3JDelSp
import Fl4Proofs.P3.P3JCapIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 46) A `KW` cap is no untyped cap. -/
theorem kw_not_ut {c : capability.Cap} (h : SInvCk.KW (absCap c)) : isUt c = false := by
  cases c <;> simp_all [isUt, absCap, SInvCk.KW]

/-- (p3J gen 46) **`ValidIrqMasks` at a dispatch state** (SInvA's `vim`; the FaultIP write and the budget step
keep the interrupt states and the masks). -/
theorem BudgetAt.vimD (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hV : SInvV.ValidIrqMasks σ) (hk : σ.kheap σ.curThread = some (.tcb x)) (h : BudgetAt σ σb true) :
    ValidIrqMasks σb := by
  obtain ⟨⟨σu, hu, ebu⟩, -⟩ := BudgetAt.shape27 hnd hk h
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  rw [ebu, e]
  intro i hi
  exact hV i hi

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 46) **`NcHyp` at a `CKI` state** (no slot holds an untyped cap). -/
theorem ncHyp_of_cki {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) (x0 x1 x2 : U64) : NcHyp (st := st) Z.th s σ x0 x1 x2 := by
  intro x _ sl hAs e hu
  subst e
  rw [kw_not_ut (Mc.kw_of_cki J hC hAs.isSlot)] at hu
  cases hu

set_option maxHeartbeats 4000000 in
/-- (p3J gen 46) **The Thread cap's decode at a dispatch state at SetSpace, any flags** (module docstring). -/
theorem decThSspSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsg : SpecGlob σb)
    (hP0 : PPR0 σb) (hCb : SInvCk.CKI σb) (hRRb : SInvRr.RR σb) (hNSb : NativeScope σb)
    (hMb : MR a' σb.machineState) (hVTb : ValidMachineTime σb) (hVIb : ValidIrqMasks σb)
    {ct : U64} (hct : sched.cur_thread st s' = ok ct)
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
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBSetSpace) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : MidX (L := L) arI AR MR Z H Cs s' s' a' σb := ⟨JStab.mv J.stab, hMb, P1.WritesIn.refl _ _⟩
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hXc := ExtraOK.xc J.xtop.rel.1 (hXO e exs he hexs)
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetSpace
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  exact xcapP_of_tcb arI s' a' σb hX0 _ _ (cslotAddr sl) p bl call don fp buf e ct hct sl' _ ci sl exs buffer
    (tcb_set_spaceJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
      ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen hArgs
      (J.stallT p hpT) call sl hAs e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) (exAt_idx1 e) (exAt_idx2 e)
      exs hXc (ncHyp_of_cki J hCb _ _ _) bl don ci buffer)

end

/-- (p3J gen 46) The Thread labels left after SetSpace. -/
def ThHard18 (l : U64) : Prop := ThHard17 l ∧ l ≠ fl4_abi.label.TCBSetSpace

/-- (p3J gen 46) The caps left after the SetSpace leaf, with the message label. -/
def IsRestCap26 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard18 l
  | _, _ => False

theorem restCap25_of26 {cp : capability.Cap} {l : U64} (h : IsRestCap26 cp l) : IsRestCap25 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap26_of {cp : capability.Cap} {l : U64} (h : IsRestCap25 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSetSpace) : IsRestCap26 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

/-- (p3J gen 46) The dispatch state's facts the SetSpace leaf reads, from the entry's `SInvX` (module docstring). -/
theorem dispSspFacts {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {V' : XVs} {s' : S} {a' : A}
    (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hX : SInvX σ)
    (hni : σ.curThread ≠ σ.idleThread) (hBA : BudgetAt σ σb true)
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) :
    Entered σb ∧ SpecGlob σb ∧ PPR0 σb ∧ NativeScope σb ∧ ValidMachineTime σb ∧ ValidIrqMasks σb := by
  obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  exact ⟨hnib, hsg, ppr0_disp arI hnd hX hBA J hnib, BudgetAt.nativeScopeM hX.nativeScope hBA,
    BudgetAt.vmt hnd hBA, BudgetAt.vimD hnd hX.sb.1.1.vim hk0 hBA⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 46) **`MidDecStWL` at `KW ∧ IsRestCap25` from the SetSpace leaf** (module docstring). -/
theorem midDecRest25_of_ssp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap25 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetSpace
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThSspSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap26_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 46) **`InvDecStWL` at `KW ∧ IsRestCap25` from the SetSpace leaf** (module docstring). -/
theorem invDecRest25_of_ssp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap25 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetSpace
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThSspSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap26_of hW.2 hS⟩

/-- (p3J gen 46) `MidDecStWL` at `KW ∧ IsRestCap25` gives it at `KW ∧ IsRestCap26` (antitone). -/
theorem midDecStWL_of_25 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap25 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap25_of26 hW.2⟩

/-- (p3J gen 46) `InvDecStWL` at `KW ∧ IsRestCap25` gives it at `KW ∧ IsRestCap26` (antitone). -/
theorem invDecStWL_of_25 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap25 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap25_of26 hW.2⟩

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

/-- (p3J gen 46) **`DispStabFootLzs` [J]**: `DispStabFootLzr` with `invDecRest` / `midDecRest` restricted to
`IsRestCap26` (`IsRestCap25` minus the Thread caps at SetSpace; module docstring). -/
structure DispStabFootLzs (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzr.invDecRest` at `KW ∧ IsRestCap26`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzr.midDecRest` at `KW ∧ IsRestCap26`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzr.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzr.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 46) **`DispStabFootLzs → DispStabFootLzr`** under the tops' platform facts and `IrqPlatK` (module
docstring). -/
theorem dispStabFootLzr_of_Lzs [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzs (L := L) arI AR MR s a σ) :
    DispStabFootLzr (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest25_of_ssp hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest25_of_ssp hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 46) **`DispStabFootLzr → DispStabFootLzs`** (the honesty claim: `DispStabFootLzs` is implied). -/
theorem dispStabFootLzs_of_Lzr {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzr (L := L) arI AR MR s a σ) : DispStabFootLzs (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_25 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_25 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 46) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzs` only** (`hLzs` [J];
`hIA : IrqPlatK` [P] added to `_sysLzr`'s globals; module docstring). -/
theorem kernel_entry_runMcWKR_sysLzs [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzs : DispStabFootLzs (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzr hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzr_of_Lzs hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hLzs)

end

end Fl4Proofs.P3.Mc
