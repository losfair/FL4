/-
P3 (p3J gen 38): **the SchedContext leaf for both classes (every label but Unbind / YieldTo) and the top
without it** (P3JScLeaf's `decScSt`).

* **`MidDecStWL` / `InvDecStWL`**: P3JMidDecK's `MidDecStW` / P3JInvLeaf's `InvDecStW` with the antecedent
  `W cp info.label` (the looked-up cap and the message label) for `W cp`; `MidDecStW W` is
  `MidDecStWL (fun cp _ => W cp)` (`midDecStW_iff_WL`, `invDecStW_iff_WL`: `Iff.rfl`).
* `IsRestCap4 cp l`: CNode, Thread, or a SchedContext cap with `l` = `SchedContextUnbind` (42) /
  `SchedContextYieldTo` (45). `restCap4_of`, `restCap3_of4`.
* **`midDecRest3_of_sc`** / **`invDecRest3_of_sc`**: gen 37's `midDecRest` / `invDecRest` predicates
  (`MidDecStW` / `InvDecStW` at `KW ∧ IsRestCap3`) from `decScSt` (a SchedContext cap, label neither Unbind nor
  YieldTo; the dispatch state's `Entered` by `dispEnteredSg`) and `MidDecStWL` / `InvDecStWL` at
  `KW ∧ IsRestCap4`.
* **`DispStabFootLt` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap4` (label-aware), midSpec, midRecvSw
  verbatim}; **`dispStabFootLs_of_Lt`** (with the tops' platform facts `TimeAgree`, `hmax`, `htu`, which every top
  already has), **`dispStabFootLt_of_Ls`** (the honesty claim, proved); top **`kernel_entry_runMcWKR_sysLt`**
  (globals verbatim as `_sysLs`).

Premise honesty: `DispStabFootLt`'s decode fields are `DispStabFootLs`'s at a smaller antecedent
(`IsRestCap4 cp l → IsRestCap3 cp`; `MidDecStW` / `InvDecStW` antitone), midSpec / midRecvSw verbatim, so
`DispStabFootLt` is implied by `DispStabFootLs` (`dispStabFootLt_of_Ls`), and conversely implies it given the
tops' platform facts (`dispStabFootLs_of_Lt`). No new kind of premise.

Named premise: `DispStabFootLt` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JScLeaf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 38) The caps left after the SchedContext leaf, with the message label: CNode, Thread, and a
SchedContext cap invoked with Unbind or YieldTo. -/
def IsRestCap4 : capability.Cap → U64 → Prop
  | .CNode .., _ => True
  | .Thread _, _ => True
  | .SchedContext .., l => l = fl4_abi.label.SchedContextUnbind ∨ l = fl4_abi.label.SchedContextYieldTo
  | _, _ => False

theorem restCap3_of4 {cp : capability.Cap} {l : U64} (h : IsRestCap4 cp l) : IsRestCap3 cp := by
  cases cp
  all_goals first | trivial | exact False.elim h

theorem restCap4_of {cp : capability.Cap} {l : U64} (h : IsRestCap3 cp)
    (hS : ¬ ∃ p sb, cp = .SchedContext p sb ∧ l ≠ fl4_abi.label.SchedContextUnbind ∧
      l ≠ fl4_abi.label.SchedContextYieldTo) :
    IsRestCap4 cp l := by
  cases cp
  case SchedContext p sb =>
    show l = _ ∨ l = _
    by_contra hc
    push_neg at hc
    exact hS ⟨p, sb, rfl, hc.1, hc.2⟩
  all_goals first | trivial | exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 38) **`MidDecStW` with the antecedent on the cap and the message label** (module docstring). -/
def MidDecStWL (W : capability.Cap → U64 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
      msg.msg_info st s' ct = ok info →
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False) →
      msg.lookup_ipc_buffer st s' false ct = ok buf →
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False) →
      ipc.lookup_extra_caps st s' ct buf info = ok r2 →
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False) →
      Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False) →
      ∀ (sl : Fl4Spec.CslotPtr) (cp : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
        (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) = ok cp → Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap cp, σb)}, False) →
        r2 = .Ok e → er = .ok exs → W cp info.label →
        XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
          info.label (msgLen info buf) (cslotAddr sl) cp false false true true buf e mi.miLabel
          (argsU.map UScalar.bv) (Fl4Spec.toBl (L.mem s' (regA ct rg)).bv) sl exs buffer ct

/-- (p3J gen 38) **`InvDecStW` with the antecedent on the cap and the message label** (module docstring). -/
def InvDecStWL (W : capability.Cap → U64 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (call bl don : Bool) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct, sched.cur_thread st s' = ok ct → InvSys n call bl don →
    ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
      msg.msg_info st s' ct = ok info →
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False) →
      msg.lookup_ipc_buffer st s' false ct = ok buf →
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False) →
      ipc.lookup_extra_caps st s' ct buf info = ok r2 →
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False) →
      Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False) →
      ∀ (sl : Fl4Spec.CslotPtr) (cp : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
        (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) = ok cp → Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap cp, σb)}, False) →
        r2 = .Ok e → er = .ok exs → W cp info.label →
        XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
          info.label (msgLen info buf) (cslotAddr sl) cp bl call don false buf e mi.miLabel
          (argsU.map UScalar.bv) (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) sl exs buffer ct

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

/-- (p3J gen 38) `MidDecStW W` is `MidDecStWL` at a label-blind antecedent. -/
theorem midDecStW_iff_WL {W : capability.Cap → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall} :
    MidDecStW (L := L) arI AR MR W Z H Cs s a σ n c ↔ MidDecStWL (L := L) arI AR MR (fun cp _ => W cp) Z H Cs s a σ n c :=
  Iff.rfl

/-- (p3J gen 38) `InvDecStW W` is `InvDecStWL` at a label-blind antecedent. -/
theorem invDecStW_iff_WL {W : capability.Cap → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} :
    InvDecStW (L := L) arI AR MR W Z H Cs s a σ n call bl don ↔
      InvDecStWL (L := L) arI AR MR (fun cp _ => W cp) Z H Cs s a σ n call bl don :=
  Iff.rfl

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **gen 37's `midDecRest` from the SchedContext leaf and the label-aware three left** (module
docstring). -/
theorem midDecRest3_of_sc (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p sb, cp = .SchedContext p sb ∧ info.label ≠ fl4_abi.label.SchedContextUnbind ∧
      info.label ≠ fl4_abi.label.SchedContextYieldTo
  · obtain ⟨p, sb, rfl, hu, hy⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScSt hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs hu hy _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap4_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **gen 37's `invDecRest` from the SchedContext leaf and the label-aware three left** (module
docstring). -/
theorem invDecRest3_of_sc (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p sb, cp = .SchedContext p sb ∧ info.label ≠ fl4_abi.label.SchedContextUnbind ∧
      info.label ≠ fl4_abi.label.SchedContextYieldTo
  · obtain ⟨p, sb, rfl, hu, hy⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScSt hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs hu hy _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap4_of hW.2 hS⟩

/-- (p3J gen 38) `MidDecStW` at `KW ∧ IsRestCap3` gives `MidDecStWL` at `KW ∧ IsRestCap4` (antitone). -/
theorem midDecStWL_of_3 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap3_of4 hW.2⟩

/-- (p3J gen 38) `InvDecStW` at `KW ∧ IsRestCap3` gives `InvDecStWL` at `KW ∧ IsRestCap4` (antitone). -/
theorem invDecStWL_of_3 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap3_of4 hW.2⟩

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

/-- (p3J gen 38) **`DispStabFootLt` [J]**: `DispStabFootLs` with `invDecRest` / `midDecRest` restricted to the
CNode and Thread caps and the SchedContext caps invoked with Unbind / YieldTo (module docstring). -/
structure DispStabFootLt (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLs.invDecRest` at `KW ∧ IsRestCap4`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLs.midDecRest` at `KW ∧ IsRestCap4`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLs.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLs.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 38) **`DispStabFootLt → DispStabFootLs`** given the tops' platform facts (module docstring). -/
theorem dispStabFootLs_of_Lt (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLt (L := L) arI AR MR s a σ) :
    DispStabFootLs (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest3_of_sc hA hnd hARI (MachPlatF.toT hM hIp) hKD hT hmax htu hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest3_of_sc hA hnd hARI (MachPlatF.toT hM hIp) hKD hT hmax htu hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 38) **`DispStabFootLs → DispStabFootLt`** (the honesty claim: `DispStabFootLt` is implied). -/
theorem dispStabFootLt_of_Ls {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLs (L := L) arI AR MR s a σ) : DispStabFootLt (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_3 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_3 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLt` only** (`hLt` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLt : DispStabFootLt (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLs hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLs_of_Lt hARI hA hnd hM hIp hKD hT hmax htu hLt)

end

end Fl4Proofs.P3.Mc
