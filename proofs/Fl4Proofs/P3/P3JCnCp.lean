/-
P3 (p3J gen 39): **the CNode cap's decode leaf at stable ghosts for both classes, every label but Revoke / Delete /
CancelBadgedSends** (the copy family Copy / Mint / Move / Mutate / Rotate, labels 28–32, and every illegal label).

* Footprint route. No whole-decode footprint of FL4's CNode decode exists (no analogue of ScDecodeAll's
  `sc_decode_refines` / `UFoot`), but the copy family needs none: XTopCnode's `decode_invocation_cnode_copyXS` takes
  its step closure as a hypothesis (`Steps … → X`), and every one of its success outcomes is a run of primitive steps
  (`Steps`), whose `ProjW` footprint is P3JStepFt's **`Steps.jatZW`** (gen 36). The illegal labels error at the
  dispatch state itself (XTopJointLiveCn's `decode_invocation_cnode_illegalXG`, `X` at the start state;
  `P1.WritesIn.refl`).
* **`decCnCpSt`** (any `blk` / `call` / `don` / `fp`): at
  `X := JStab (Z.mv Z.G V') H Cs ∧ WritesIn s' · (ProjW H Cs s')`; the label, arguments and extra caps from the front
  facts (`JAtZ.frontJ`, `JAtZ.argsJ`, `ExtraOK.rel2`), the canonical label (`cnode_canon`, `specDec_cnode`,
  `XCapP.lbl_congr`), never preempted (`cnode_noPre_of`: the label is neither 25 nor 26), `MR` by `XCapP.mrT` with
  `MKD.decode_cnode_nrd` / `MachT.dec_cnode_q` (neither Revoke nor Delete). StPostInvLeaf's `decode_cnodeCopyJSt` is the
  same route at `JStab Z` without the footprint (Copy / Mint only).
* `CnHard l`: `l` is 25 (Revoke), 26 (Delete) or 27 (CancelBadgedSends). `IsRestCap7 cp l`: a CNode cap with
  `CnHard l`, or a Thread cap. `restCap6_of7`, `restCap7_of`.
* **`midDecRest6_of_cn`** / **`invDecRest6_of_cn`**: gen 38's `MidDecStW` / `InvDecStW` at `KW ∧ IsRestCap6` from
  `decCnCpSt` and `MidDecStWL` / `InvDecStWL` at `KW ∧ IsRestCap7`; `midDecStWL_of_6` / `invDecStWL_of_6` (antitone).
* **`DispStabFootLz` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap7` (label-aware), midSpec, midRecvSw verbatim};
  **`dispStabFootLy_of_Lz`** (the tops' platform facts), **`dispStabFootLz_of_Ly`** (honesty, proved); top
  **`kernel_entry_runMcWKR_sysLz`** (globals verbatim as `_sysLy`).

Premise honesty: `DispStabFootLz`'s decode fields are `DispStabFootLy`'s at a smaller antecedent
(`IsRestCap7 cp l → IsRestCap6 cp`), midSpec / midRecvSw verbatim, so `DispStabFootLz` is implied by
`DispStabFootLy` (`dispStabFootLz_of_Ly`) and implies it given the tops' platform facts (`dispStabFootLy_of_Lz`).

Named premise: `DispStabFootLz` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JScYld
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 39) The CNode labels left: Revoke (25), Delete (26), CancelBadgedSends (27). -/
def CnHard (l : U64) : Prop := 25 ≤ l.val ∧ l.val ≤ 27

/-- (p3J gen 39) The caps left after the CNode copy-family / illegal leaf, with the message label. -/
def IsRestCap7 : capability.Cap → U64 → Prop
  | .CNode .., l => CnHard l
  | .Thread _, _ => True
  | _, _ => False

theorem restCap6_of7 {cp : capability.Cap} {l : U64} (h : IsRestCap7 cp l) : IsRestCap6 cp := by
  cases cp
  all_goals first | trivial | exact False.elim h

theorem restCap7_of {cp : capability.Cap} {l : U64} (h : IsRestCap6 cp)
    (hS : ¬ ∃ p r gs g, cp = .CNode p r gs g ∧ ¬ CnHard l) : IsRestCap7 cp l := by
  cases cp
  case CNode p r gs g =>
    show CnHard l
    by_contra hc
    exact hS ⟨p, r, gs, g, rfl, hc⟩
  all_goals first | trivial | exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **The CNode cap's decode at a dispatch state, any flags, any label but 25–27** (module
docstring). -/
theorem decCnCpSt (hA : P0.ArchTotal arI) (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
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
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p r gs g : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.CNode p r gs g))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs) (hl : ¬ CnHard info.label)
    (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.CNode p r gs g) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  unfold CnHard at hl
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  obtain ⟨sl', hl', hd⟩ := cnode_canon info.label
  refine XCapP.lbl_congr arI (specDec_cnode p r gs g hd) ?_
  have hr : info.label ≠ fl4_abi.label.CNodeRevoke := fun e => by rw [e, lbl_revoke_val] at hl; omega
  have hd' : info.label ≠ fl4_abi.label.CNodeDelete := fun e => by rw [e, lbl_delete_val] at hl; omega
  have hsr : Fl4Spec.genInvocationType sl' ≠ .cnodeRevoke := by
    rw [hl']; unfold cnodeLabelOf
    split_ifs <;> first | (intro e; cases e; done) | (exfalso; omega)
  have hsd : Fl4Spec.genInvocationType sl' ≠ .cnodeDelete := by
    rw [hl']; unfold cnodeLabelOf
    split_ifs <;> first | (intro e; cases e; done) | (exfalso; omega)
  refine XCapP.mrT hMT ?_ (MKD.decode_cnode_nrd L.total hA hKD hr hd' hMb)
    (fun inv hdc => MachT.dec_cnode_q fp sl' _ ci sl _ _ _ exs buffer hsr hsd σb _ hdc.1 inv rfl)
  have hX := J.xtop
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .CNode p r gs g := capV_of_capAt hc
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hex := ExtraOK.rel2 hX.rel.1 (hXO e exs he hexs)
  by_cases hcp : 28 ≤ info.label.val ∧ info.label.val ≤ 32
  · exact XCap.toPN arI (decode_invocation_cnode_copyXS arI s' a' σb hX (J.curRun.run hnib)
      (X := fun s1 a1 σ1 => JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
        P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) hX0
      (fun _ _ _ h => by
        obtain ⟨⟨G', V'', Ac'', Lst'', D'', J', -⟩, hw⟩ :=
          Steps.jatZW arI hARI.toMask (jStepHyps arI) h rfl J (J.zNoBlk hsg)
        exact ⟨⟨G', V'', Ac'', Lst'', D'', J'⟩, hw⟩)
      (fun _ _ _ h => by obtain ⟨⟨_, _, _, _, _, J'⟩, -⟩ := h; exact ⟨_, J'.xtop⟩)
      info.label hcp sl' hl' (msgLen info buf) buf ct hct argsU hLen hArgs p r gs g hwf hcv
      ⟨cslotAddr sl, hAs.isSlot, hsc⟩ e (exAt e 0) (exAt e 1) (exAt_idx0 e) (exAt_idx1 e) exs hex J.kern.act hcur
      (cslotAddr sl) bl call don fp ci sl buffer) (cnode_noPre_of hl' (by omega))
  · have hlo : info.label.val < 25 ∨ 32 < info.label.val := by omega
    exact XCap.toPN arI (decode_invocation_cnode_illegalXG arI
      (X := fun s1 a1 σ1 => JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
        P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) s' a' σb hX0
      info.label hlo sl' hl' (msgLen info buf) buf ct hct _ p r gs g e exs
      (cslotAddr sl) bl call don fp ci sl buffer) (cnode_noPre_of hl' (by omega))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **`MidDecStW` at `KW ∧ IsRestCap6` from the CNode copy-family / illegal leaf** (module
docstring). -/
theorem midDecRest6_of_cn (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p r gs g, cp = .CNode p r gs g ∧ ¬ CnHard info.label
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
    exact decCnCpSt hA hARI hMT hKD J hnib hsg hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap7_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **`InvDecStW` at `KW ∧ IsRestCap6` from the CNode copy-family / illegal leaf** (module
docstring). -/
theorem invDecRest6_of_cn (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p r gs g, cp = .CNode p r gs g ∧ ¬ CnHard info.label
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
    exact decCnCpSt hA hARI hMT hKD J hnib hsg hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap7_of hW.2 hS⟩

/-- (p3J gen 39) `MidDecStW` at `KW ∧ IsRestCap6` gives `MidDecStWL` at `KW ∧ IsRestCap7` (antitone). -/
theorem midDecStWL_of_6 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap6_of7 hW.2⟩

/-- (p3J gen 39) `InvDecStW` at `KW ∧ IsRestCap6` gives `InvDecStWL` at `KW ∧ IsRestCap7` (antitone). -/
theorem invDecStWL_of_6 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap6 cp) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap6_of7 hW.2⟩

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

/-- (p3J gen 39) **`DispStabFootLz` [J]**: `DispStabFootLy` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete / CancelBadgedSends and the Thread caps (module docstring). -/
structure DispStabFootLz (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLy.invDecRest` at `KW ∧ IsRestCap7`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLy.midDecRest` at `KW ∧ IsRestCap7`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap7 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLy.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLy.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 39) **`DispStabFootLz → DispStabFootLy`** given the tops' platform facts (module docstring). -/
theorem dispStabFootLy_of_Lz (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLz (L := L) arI AR MR s a σ) :
    DispStabFootLy (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest6_of_cn hA hnd hARI (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest6_of_cn hA hnd hARI (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 39) **`DispStabFootLy → DispStabFootLz`** (the honesty claim: `DispStabFootLz` is implied). -/
theorem dispStabFootLz_of_Ly {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLy (L := L) arI AR MR s a σ) : DispStabFootLz (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_6 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_6 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLz` only** (`hLz` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLz [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLz : DispStabFootLz (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLy hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLy_of_Lz hARI hA hnd hM hIp hKD hLz)

end

end Fl4Proofs.P3.Mc
