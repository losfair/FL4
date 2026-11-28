/-
P3 (p3J gen 50): **the invoking class at the invoked slot only (`LookAt`), one flat per-cap summary lemma; label 88
(`TCBSetEPTRoot`) per entry from the entry's own `SysK6`; `KNo88` retired from the newest top**.

Architect ruling (gen 50): no copy of the 28 `DispStabFootL*` layers; one flat summary lemma under `LookAt`, fed
straight into P3JLook's `handle_invocation_refinesMXPL`; the two `LookAt` twins gen 49 named; everything above
`DispStabFoot` reused.

* **`invDecFlat`**: the decode leaf `XCapP (MidX …) (MidXP …)` of the invoking class at every looked-up cap that is
  not a Thread cap at label 88 (`InvDecStWL` at `¬ (Thread ∧ label = 88)`), one flat lemma: `KW` from `CKI`,
  then one `by_cases` per family with one call of the existing per-cap leaf theorem in each positive branch
  (`invDecReply_of`, `invDecEasy_of`, `invDecEp_of`, `invDecDom_of`, `invDecIrq_of`, `decScSt`, `decScStY`,
  `decScStAll`, `decCnCpSt`, `decCnCbsSt`, the Thread leaves `decThIllSt` … `decThFpuRSt`, `decThSspSt`,
  `decThInsSt`, `decCnDelSt`, `decThSspPSt` — the same calls the onion's conversion lemmas make), the residual
  tracked by the existing `restCap*_of` lemmas; what is left is `IsRestCap29` = Thread @ 88 (`thHard20_ept`),
  excluded by the antecedent. No new structure, no layer.
* **`XCapP.errKeepEq`**: where the spec's decode has no outcome, `XCapP X XP` keeps only its error branches,
  in which FL4's store and the spec state are the decode's own (`res.2.1 = s`, `σ`), plus any arch fact `Q` FL4's
  error outcomes keep (P3JVtxMR's `XCapP.mrN` with the two equalities recorded).
* **`xcapP_ept_midSt`**: at Thread @ 88, the entry's `JVtxScope` (`XCapP JAt JAtPre`, P3JVtxMR's D1 method)
  gives the stable decode leaf `XCapP (MidX …) (MidXP …)`: only error branches (`specDec_ept_noOk`), store and
  spec state unchanged, `AR` from the outcome's `JAt` (`JAtZ.archJ`), `MR` by `MKE.decode_thread_ept`.
* **`InvDecStL` [J-shape]**: P3JInvCls's `InvDecSt` with `LookAt ct cptr σb sl cp` (the invoked slot) after its
  last hypothesis. **`invDecStL_of_k6`**: `InvDecStL` from the entry's `SysK6` (whose `KDispHypsKVU44w (¬ NK6)`
  field, JBootQ1Disp's `JPathAtMU44w`, already asks `LookAt` and gives `JVtxScope` exactly at an invoked Thread
  cap with label 88) plus `invDecFlat`. **`invDecStL_of_no88L`**: the same from `KNo88L` instead of `SysK6`.
* `LookAt` twins: **`invInvHIL`** (P3JInvCls's `invInvHI` on `handle_invocation_refinesMXPL`, the decode premise
  `InvDecStL`; the rest of the proof as there), **`dispInv_stFtL`** (`dispInv_stFt` on `invInvHIL`).
* **`midDecRestLn_of`**: `DispStabFootLn.midDecRest`'s statement from the existing mid conversion lemmas
  (`midDecRest_of_dom` … `midDecRest28_of_ssp`) applied to gen 48's `midDecStWL29`: no copy, one term.
* **`KNo88L` [S]** (defined, not used by the new top): at every dispatch state of an entry, if the message label
  is 88, the slot the spec's `lookupCapAndSlot` returns for the CAP register (`LookAt`) does not hold a Thread
  cap. **`kNo88L_of_kNo88`**: `KNo88 → KNo88L` (the converse fails: `KNo88L` excludes only the looked-up slot).
  **`kNo88L_of_label`**: not vacuous (every state whose message label is not 88).
* **`dispStabFootLn_of_Lzx`**: `DispStabFootLzx` [J] {midRecvSw} gives P3JMidEp's `DispStabFootLn` with the
  globals (inv by `dispInv_stFtL` + `invDecStL_of_k6`, midDecRest by `midDecRestLn_of`, midSpec by
  `midSpecAt_of`, midRecvSw verbatim) — the assembly; above it P3JMidEp's `kernel_entry_runMcWKR_sysLn`
  (→ … → P3JSysStTop `kernel_entry_runMcWKR_sysD` → `_sysWC` → `kernel_entry_runCK`) as-is.
* Top **`kernel_entry_runMcWKR_sysLzy`**: globals verbatim as `_sysLzx`, [J] `DispStabFootLzx` = {midRecvSw},
  **no [S]**: `KNo88` gone, and no `KNo88L` needed — label 88 is excluded per entry, at the invoked slot, by the
  entry's own `SysK6` antecedent the top already had (its `JVtxScope` [scope] at Thread @ 88 via `LookAt`,
  XTopJointEntry; this is the ruling's "proper native scope"). `kernel_entry_runMcWKR_sysLzx_of_Lzy`: the new
  top implies the old (drop `hNo`); the old does not give the new (it needs `KNo88`, which the new top does not
  have).

Named premises: `DispStabFootLzx` [J] (P3JMidSpec, reused), `KNo88L` [S] (defined for the comparison only; not a
premise of the new top); globals as `_sysLzx`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (p3J gen 50) **`XCapP` at a cap the spec cannot decode keeps only its error branches** (module docstring):
there FL4's store and the spec state are the decode's own, and FL4's error outcomes keep `Q`. -/
theorem XCapP.errKeepEq {X XP XP' : S → A → Fl4Spec.State Unit → Prop} {Q : A → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (hno : ∀ inv, ¬ DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv)
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      r.1 = .Err .Preempted ∨ r.1 = .Ok () ∨ Q r.2.2 ⦄) :
    XCapP (L := L) arI (fun s1 a1 σ1 => s1 = s ∧ σ1 = σ ∧ X s1 a1 σ1 ∧ Q a1) XP' s ar σ lbl length slot c blk
      call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono (WP.spec_and h hW) ?_)
    rintro r ⟨h1, h2⟩
    unfold TopPostDMXP TopPostDMX at h1 ⊢
    rcases h1 with ⟨e, he, hs, ⟨e', hrun, hrel⟩, hX⟩ | ⟨inv, hd, -⟩
    · have hp : r.1 ≠ .Err .Preempted := by
        rw [he]; intro h; exact errRel_ne_preempted hrel (by cases h; rfl)
      have hQ : Q r.2.2 := by
        rcases h2 with h2 | h2 | h2
        · exact absurd h2 hp
        · rw [he] at h2; cases h2
        · exact h2
      refine Or.inl ⟨e, he, hs, ⟨e', hrun, hrel⟩, ?_⟩
      simp only [if_neg hp] at hX ⊢
      first | exact ⟨hs, rfl, hX, hQ⟩ | exact ⟨hs, trivial, hX, hQ⟩ | exact ⟨hs, hX, hQ⟩
    · exact absurd hd (hno inv)
  · refine Or.inr (WP.spec_mono (WP.spec_and h hW) ?_)
    rintro r ⟨h1, h2⟩
    unfold TopPostRMX at h1 ⊢
    rcases h1 with ⟨e, he, hs, ⟨e', hrun, hrel⟩, hX⟩ | ⟨-, -, inv, hd, -⟩
    · have hp : r.1 ≠ .Err .Preempted := by
        rw [he]; intro h; exact errRel_ne_preempted hrel (by cases h; rfl)
      have hQ : Q r.2.2 := by
        rcases h2 with h2 | h2 | h2
        · exact absurd h2 hp
        · rw [he] at h2; cases h2
        · exact h2
      exact Or.inl ⟨e, he, hs, ⟨e', hrun, hrel⟩, hs, rfl, hX, hQ⟩
    · exact absurd hd (hno inv)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 50) **`InvDecSt` at the invoked slot** (module docstring): P3JInvCls's `InvDecSt` with
`LookAt ct cptr σb sl cp` (the spec's `lookupCapAndSlot` of the CAP register returns `sl` / `cp`) after its last
hypothesis — the decode premise of `handle_invocation_refinesMXPL`. -/
def InvDecStL (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (call bl don : Bool) : Prop :=
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
        r2 = .Ok e → er = .ok exs → LookAt ct (L.mem s' (Endp.regA ct layout.reg.CAP)) σb sl cp →
        XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
          info.label (msgLen info buf) (cslotAddr sl) cp bl call don false buf e mi.miLabel
          (argsU.map UScalar.bv) (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) sl exs buffer ct

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **The Thread cap at label 88: the entry's `JVtxScope` gives the stable decode leaf**
(module docstring). -/
theorem xcapP_ept_midSt (hA : P0.ArchTotal arI) (hKD : MRKeepD arI MR) [VxE Z] {V' : XVs} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hMb : MR a' σb.machineState)
    {lbl length slot : U64} {p : U64} {blk call don : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} (hl : lbl = fl4_abi.label.TCBSetEPTRoot) (hsl : slbl = lbl.bv)
    (h : XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s' a' σb lbl length slot (.Thread p) blk
      call don false buf extra slbl args ci sl excaps buffer ct) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb lbl length
      slot (.Thread p) blk call don false buf extra slbl args ci sl excaps buffer ct := by
  subst hsl; subst hl
  refine XCapP.monoX (XCapP.errKeepEq arI (XP' := MidXP (L := L) arI AR MR Z H Cs s')
    (Q := fun a1 => MR a1 σb.machineState)
    (fun inv hd => specDec_ept_noOk false _ ci sl excaps buffer p σb _ hd.1 inv rfl) h
    (MKE.decode_thread_ept (st := st) (s := s') (length := length) (slot := slot) (p := p) (blk := blk)
      (call := call) (don := don) (fp := false) (buf := buf) (extra := extra) L.total hA hKD hMb)) ?_
  rintro s1 a1 σ1 ⟨rfl, rfl, ⟨Z', H', Cs', Ac'', Lst'', D'', J', -⟩, hm⟩
  exact ⟨JStab.mv (J.archJ J'.xtop.fin.1.1.2.2.2.2.2.2).stab, hm, P1.WritesIn.refl _ _⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **The flat per-cap summary of the invoking class's decode leaves** (module docstring): every
looked-up cap that is not a Thread cap at label 88, one existing leaf per family. -/
theorem invDecFlat [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hPA : PPPlatA arI AR)
    [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ)
    (hni : σ.curThread ≠ σ.idleThread) (hIB : SpecIrqB σ) :
    InvDecStWL (L := L) arI AR MR (fun cp l => ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSetEPTRoot) Z H Cs s
      a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  have hK : SInvCk.KW (absCap cp) := by
    obtain ⟨o, i⟩ := sl
    exact hCb o i (absCap cp) ((getCap_set_iff σb o i (absCap cp)).1 (congrArg Prod.fst hget))
  have hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄ := ⟨hmax, htu⟩
  -- Reply / Null, Zombie, Notification / Endpoint / Domain / IrqHandler (InvDecStW leaves)
  by_cases h1 : IsReplyCap cp
  · exact invDecReply_of hA hnd hmax htu hT hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct
      hn info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, h1⟩
  by_cases h2 : IsEasyCap cp
  · exact invDecEasy_of hA hnd hT hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, h2⟩
  by_cases h3 : IsEpCap cp
  · exact invDecEp_of hA hnd hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, h3⟩
  by_cases h4 : cp = .Domain
  · exact invDecDom_of hA hnd hARI hMT hKD hX hni σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, h4⟩
  have w0 : IsRestCap cp := restCap_of hK h1 h2 h3 h4
  by_cases h5 : ∃ i, cp = .IrqHandler i
  · exact invDecIrq_of hA hnd hARI hMT hKD hX hni hIB σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn
      info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hK, h5⟩
  have w3 : IsRestCap3 cp := restCap3_of w0 h5
  -- SchedContext
  by_cases h6 : ∃ p sb, cp = .SchedContext p sb ∧ info.label ≠ fl4_abi.label.SchedContextUnbind ∧
      info.label ≠ fl4_abi.label.SchedContextYieldTo
  · obtain ⟨p, sb, rfl, hu, hy⟩ := h6
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScSt hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs hu hy _ _ _ _ _ _
  have w4 : IsRestCap4 cp info.label := restCap4_of w3 h6
  by_cases h7 : ∃ p sb, cp = .SchedContext p sb ∧ info.label = fl4_abi.label.SchedContextUnbind
  · obtain ⟨p, sb, rfl, hu⟩ := h7
    have hy : info.label ≠ fl4_abi.label.SchedContextYieldTo := lbl_ne hu (by simp)
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScStY hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs hy _ _ _ _ _ _
  have w5 : IsRestCap5 cp info.label := restCap5_of w4 h7
  by_cases h8 : ∃ p sb, cp = .SchedContext p sb ∧ info.label = fl4_abi.label.SchedContextYieldTo
  · obtain ⟨p, sb, rfl, -⟩ := h8
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScStAll hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs _ _ _ _ _ _
  have w6 : IsRestCap6 cp := restCap6_of w5 h8
  -- CNode (copy family / illegal, CancelBadgedSends)
  by_cases h9 : ∃ p r gs g, cp = .CNode p r gs g ∧ ¬ CnHard info.label
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := h9
    obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
    exact decCnCpSt hA hARI hMT hKD J hnib hsg hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w7 : IsRestCap7 cp info.label := restCap7_of w6 h9
  by_cases h10 : ∃ p r gs g, cp = .CNode p r gs g ∧ info.label.val = 27
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := h10
    obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
    exact decCnCbsSt hA hARI hMT hKD J hnib hsg (epQPre_of_sinv hnd hX.sb (hX.entered hni) hX.epQAll hBA) hMb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w8 : IsRestCap8 cp info.label := restCap8_of w7 h10
  -- Thread, label by label
  by_cases h11 : ∃ p, cp = .Thread p ∧ ¬ ThHard info.label
  · obtain ⟨p, rfl, hl⟩ := h11
    exact decThIllSt J hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc e exs hl _ _ _ _ _ _
  have w9 : IsRestCap9 cp info.label := restCap9_of w8 h11
  by_cases h12 : ∃ p, cp = .Thread p ∧ ThTls info.label
  · obtain ⟨p, rfl, hl⟩ := h12
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThTlsSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  have w10 : IsRestCap10 cp info.label := restCap10_of w9 h12
  by_cases h13 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetMCPriority
  · obtain ⟨p, rfl, hl⟩ := h13
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThMcpSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w11 : IsRestCap11 cp info.label := restCap11_of w10 h13
  by_cases h14 : ∃ p, cp = .Thread p ∧ ThBp info.label
  · obtain ⟨p, rfl, hl⟩ := h14
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThBpSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w12 : IsRestCap12 cp info.label := restCap12_of w11 h14
  by_cases h15 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBBindNotification
  · obtain ⟨p, rfl, hl⟩ := h15
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThBindSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w13 : IsRestCap13 cp info.label := restCap13_of w12 h15
  by_cases h16 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBConfigureSingleStepping
  · obtain ⟨p, rfl, hl⟩ := h16
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThSsSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w14 : IsRestCap14 cp info.label := restCap14_of w13 h16
  by_cases h17 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetFlags
  · obtain ⟨p, rfl, hl⟩ := h17
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFlgSt hA hMT hKD hARI.toARKeep J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w15 : IsRestCap15 cp info.label := restCap15_of w14 h17
  by_cases h18 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBWriteFPU
  · obtain ⟨p, rfl, hl⟩ := h18
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFpuWSt hA hMT hKD hARI.toARKeep J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w16 : IsRestCap16 cp info.label := restCap16_of w15 h18
  by_cases h19 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetPriority
  · obtain ⟨p, rfl, hl⟩ := h19
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThPrioSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w17 : IsRestCap17 cp info.label := restCap17_of w16 h19
  by_cases h20 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSuspend
  · obtain ⟨p, rfl, hl⟩ := h20
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThSusSt hA hMT hKD J hnib hsgb hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc hget e exs hl _ _ _ _ _
  have w18 : IsRestCap18 cp info.label := restCap18_of w17 h20
  by_cases h21 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBResume
  · obtain ⟨p, rfl, hl⟩ := h21
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThResSt hA hT hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc e exs hl _ _ _ _ _
  have w19 : IsRestCap19 cp info.label := restCap19_of w18 h21
  by_cases h22 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetTimer
  · obtain ⟨p, rfl, hl⟩ := h22
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThTmSt hA hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  have w20 : IsRestCap20 cp info.label := restCap20_of w19 h22
  by_cases h23 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBWriteRegisters
  · obtain ⟨p, rfl, hl⟩ := h23
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThWrSt hA hT hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc e exs hl _ _ _ _ _
  have w21 : IsRestCap21 cp info.label := restCap21_of w20 h23
  by_cases h24 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBCopyRegisters
  · obtain ⟨p, rfl, hl⟩ := h24
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThCpSt hA hT hMT hKD J hnib hsgb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w22 : IsRestCap22 cp info.label := restCap22_of w21 h24
  by_cases h25 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBGetBreakpoint
  · obtain ⟨p, rfl, hl⟩ := h25
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThGbSt hA hT hMT hKD J hnib hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w23 : IsRestCap23 cp info.label := restCap23_of w22 h25
  by_cases h26 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBReadRegisters
  · obtain ⟨p, rfl, hl⟩ := h26
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThRrSt hA hT hMT hKD J hnib hsgb hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc hget he hexs hl _ _ _ _ _
  have w24 : IsRestCap24 cp info.label := restCap24_of w23 h26
  by_cases h27 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBReadFPU
  · obtain ⟨p, rfl, hl⟩ := h27
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFpuRSt hA hT hMT hKD J hnib hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w25 : IsRestCap25 cp info.label := restCap25_of w24 h27
  by_cases h28 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetSpace
  · obtain ⟨p, rfl, hl⟩ := h28
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThSspSt hARI hA hticks hnd hMT hKD hIP hT hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w26 : IsRestCap26 cp info.label := restCap26_of w25 h28
  by_cases h29 : ∃ p, cp = .Thread p ∧ IsInsLbl info.label
  · obtain ⟨p, rfl, hl⟩ := h29
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThInsSt hARI hA hticks hnd hMT hKD hIP hT hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w27 : IsRestCap27 cp info.label := restCap27_of w26 h29
  -- CNode Revoke / Delete
  by_cases h30 : ∃ p r gs g, cp = .CNode p r gs g ∧ CnDel info.label
  · obtain ⟨p, r, gs, g, rfl, hl⟩ := h30
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decCnDelSt hARI hA hticks hnd hMT hKD hIP hT hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  have w28 : IsRestCap28 cp info.label := restCap28_of w27 h30
  -- Thread SetSchedParams
  by_cases h31 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetSchedParams
  · obtain ⟨p, rfl, hl⟩ := h31
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThSspPSt hARI hA hticks hnd hMT hKD hIP hT hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc hget he hexs hl _ _ _ _ _
  have w29 : IsRestCap29 cp info.label := restCap29_of w28 h31
  -- what is left is a Thread cap at label 88, excluded
  cases cp
  case Thread p => exact absurd ⟨p, rfl, thHard20_ept w29⟩ hW
  all_goals exact False.elim w29

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **`InvDecStL` from the entry's `SysK6` and the flat summary** (module docstring): the invoked
Thread cap at label 88 by `xcapP_ept_midSt` on `SysK6`'s `JVtxScope` (asked exactly at the `LookAt` slot), every
other cap by `invDecFlat`. -/
theorem invDecStL_of_k6 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hPA : PPPlatA arI AR)
    [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ)
    (hni : σ.curThread ≠ σ.idleThread) (hIB : SpecIrqB σ)
    (hk6 : Mc.SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl)) :
    InvDecStL (L := L) arI AR MR Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hLk
  by_cases h88 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetEPTRoot
  · obtain ⟨p, rfl, hl⟩ := h88
    have hP := (hk6 σb hBA V' Ac' Lst' D' s' a' hKF J).inv ct call bl don hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl (.Thread p) e exs hsl hc hget he hexs trivial hLk (fun h => h p rfl hl)
    obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct a1 a2 a3 a4 a5 a6
    exact xcapP_ept_midSt hA hKD J hMb hl hLb.symm (hP hl)
  · exact invDecFlat hARI hA hnd hMT hKD hIP hT hmax htu hPA hX hni hIB σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb
      hRRb ct hct hn info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs h88

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **The invoking class's invocation at `MidX` / `MidXP` on the invoked slot** (P3JInvCls's
`invInvHI` on `handle_invocation_refinesMXPL`, decode premise `InvDecStL`; module docstring). -/
theorem invInvHIL [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (hD : InvDecStL (L := L) arI AR MR Z H Cs s a σ n call bl don) (σb : Fl4Spec.State Unit)
    (hBA : BudgetAt σ σb true)
    (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
    (hKF : KFrontB (L := L) arI s a s' a') (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb)
    (hMb : MR a' σb.machineState) (hCb : SInvCk.CKI σb) (hRRb : SInvRr.RR σb)
    (ct : U64) (hct : sched.cur_thread st s' = ok ct) (hn : InvSys n call bl don) :
    syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        call bl don false (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hXt := J.xtop
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib : Entered σb := BudgetAt.entered hnd hk0 (hX.entered hni) hBA
  obtain ⟨-, ek, ect, -, -, eq⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨hvfh, -⟩ := SInvAll.sinvB_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    hX.sb hni hk0 rfl rfl ek' ect
  have hq : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect, eq]; exact hX.ctQ
  have hblk := J.blk
  have hNB := Mc.noBufCap_cki J hCb
  have hF : ∀ {f : error.Fault} {f' : Fl4Spec.Fault}, FaultCorrG f f' →
      faults.handle_fault st arI s' a' ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σb).1,
        RelTopM (L := L) r.1 z.2 ∧ MidX (L := L) arI AR MR Z H Cs s' r.1 r.2 z.2 ⦄ := by
    intro f f' hcf
    refine WP.spec_mono (WP.spec_and (WP.spec_and (J.faultHypJZGSt hA hnib hct hq hvfh hcf)
      (MKD.faults_handle_fault L.total hA hKD hMb)) (Mc.faultProjW hA J hCb hnib hq hct f)) ?_
    rintro r ⟨⟨⟨z, hz, h1, h2⟩, h3⟩, h4⟩
    exact ⟨z, hz, h1, JStab.mv h2, msF_mrT hMT h3 (congrArg Prod.fst (MachT.mtk_handleFaultG _ _ σb z hz)), h4⟩
  refine handle_invocation_refinesMXPL arI (MidX (L := L) arI AR MR Z H Cs s')
    (MidXP (L := L) arI AR MR Z H Cs s') true s' a' σb
    Z.th Z.G hXt.rel.1 hXt.rel.2.1 hXt.rel.2.2.1 hXt.rel.2.2.2.1 hXt.rel.2.2.2.2.1 ?x0 ct hct hcur htcb
    call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er
    her ?rr (argsU.map UScalar.bv) hmrs ?fl ?repS ?repF ?pk ?dec
  case x0 => exact ⟨JStab.mv J.stab, hMb, P1.WritesIn.refl _ _⟩
  case rr =>
    exact (J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her).imp id
      fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ => hF (FaultCorrG.cap hcf)⟩
  case fl => exact fun _ lf lf' hl => hF (FaultCorrG.cap (capFaultCorr_lookup _ hl))
  case repS =>
    intro s1 a1 σ' _ hXs hc
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J'⟩, hR', hW1⟩ := hXs
    have hct' : ct ∈ (Z.mv G1 V1).T := TopSR.cur_mem J'.xtop.fin.1 hc.symm
    refine WP.spec_mono (WP.spec_and (WP.spec_and (J'.flTailJSt hc call) (MKD.fl_tail L.total hA hKD hR'))
      (Mc.flTailProjWc J'.kern.heap J'.blk (J'.zH.1 ct hct') call)) ?_
    rintro res ⟨⟨⟨h1, z, hz, h2, h3⟩, h4⟩, h5⟩
    exact ⟨h1, z, hz, h2, JStab.mv h3, msF_mrT hMT h4 (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz)),
      hW1.projW_trans h5⟩
  case repF =>
    intro a1 e e' hX1 he
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J''⟩, hR', -⟩ := hX1
    have hFt : ((if call then do
          let s2 ← syscall.reply_error st s' ct e
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s', a1)) :
        Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
          P1.WritesIn st s' res.2.1 (Mc.ProjW (L := L) H Cs s') ⦄ := by
      cases call
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]; exact P1.WritesIn.refl _ _
      · simp only [↓reduceIte]
        exact WP.spec_bind (Mc.replyErrProjW J.kern.heap hblk hNB (J.zH.1 ct hctT) e) fun s2 h2 => (WP.spec_ok _).2 h2
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      ((J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJSt hcur call e e' he)
      (MKD.reply_err_tail (e := e) (t := ct) (s := s') (is_call := call) L.total hA hKD hR')) hFt) ?_
    rintro res ⟨⟨⟨h1, z, hz, h2, h3⟩, h4⟩, h5⟩
    exact ⟨h1, z, hz, h2, JStab.mv h3, msF_mrT hMT h4
      (congrArg Prod.fst (MachT.mtk_when (MachT.mtk_fl4ReplyFromKernelErrorG _ _ _) σb z hz)), h5⟩
  case pk => exact midPK J hcur bl call don
  case dec =>
    intro sl cp e exs hsl hc hget he hexs hLk
    exact hD σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      hinfo hmi hbuf hbuffer hr2 her hmrs sl cp e exs hsl hc hget he hexs hLk

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **The invoking class of `DispStabFootAt` from `InvDecStL`** (P3JInvCls's `dispInv_stFt` on
`invInvHIL`; module docstring). -/
theorem dispInv_stFtL [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) (hn : InvSys n call bl don)
    (hD : InvDecStL (L := L) arI AR MR Z H Cs s a σ n call bl don) :
    SInvR.G5.DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl) := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb
  have hct' := cur_thread_eq (L := L) s'
  generalize L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = ct at hct'
  exact dispatch_invSt J' hct' hn
    (invInvHIL hA hnd hMT hKD hX hni hD σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb ct hct' hn)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **`DispStabFootLn.midDecRest`'s statement from the existing mid conversions and
`midDecStWL29`** (module docstring; one term, no copy). -/
theorem midDecRestLn_of [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hPA : PPPlatA arI AR)
    [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ)
    (hni : σ.curThread ≠ σ.idleThread) (hIB : SpecIrqB σ) :
    MidDecStW (L := L) arI AR MR
      (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp) Z H Cs s a σ n c :=
  midDecRest_of_dom hA hnd hARI hMT hKD hX hni <|
  midDecRest_of_irq hA hnd hARI hMT hKD hX hni hIB <|
  midDecRest3_of_sc hA hnd hARI hMT hKD hT hmax htu hX hni <|
  midDecRest4_of_scU hA hnd hARI hMT hKD hT hmax htu hX hni <|
  midDecRest5_of_scY hA hnd hARI hMT hKD hT hmax htu hX hni <|
  midDecRest6_of_cn hA hnd hARI hMT hKD hX hni <|
  midDecRest7_of_cbs hA hnd hARI hMT hKD hX hni <|
  midDecRest8_of_th <|
  midDecRest9_of_tls hA hnd hMT hKD hX hni <|
  midDecRest10_of_mcp hA hnd hMT hKD hX hni <|
  midDecRest11_of_bp hA hnd hMT hKD hX hni <|
  midDecRest12_of_bind hA hnd hMT hKD hX hni <|
  midDecRest13_of_ss hA hnd hMT hKD hX hni <|
  midDecRest14_of_flg hA hnd hMT hKD hARI.toARKeep hX hni <|
  midDecRest15_of_fpuw hA hnd hMT hKD hARI.toARKeep hX hni <|
  midDecRest16_of_prio hA hnd hMT hKD hX hni <|
  midDecRest17_of_sus hA hnd hMT hKD hX hni <|
  midDecRest18_of_res hA hT hnd hMT hKD hX hni <|
  midDecRest19_of_tm hA hnd hMT hKD hX hni <|
  midDecRest20_of_wr hA hT hnd hMT hKD hX hni <|
  midDecRest21_of_cp hA hT hnd hMT hKD hX hni <|
  midDecRest22_of_gb hA hT hnd hMT hKD hX hni <|
  midDecRest23_of_rr hA hT hnd hMT hKD hX hni <|
  midDecRest24_of_fpur hA hT hnd hMT hKD hX hni <|
  midDecRest25_of_ssp hARI hA ⟨hmax, htu⟩ hnd hMT hKD hIP hT hPA hX hni <|
  midDecRest26_of_ins hARI hA ⟨hmax, htu⟩ hnd hMT hKD hIP hT hPA hX hni <|
  midDecRest27_of_cnd hARI hA ⟨hmax, htu⟩ hnd hMT hKD hIP hT hPA hX hni <|
  midDecRest28_of_ssp hARI hA ⟨hmax, htu⟩ hnd hMT hKD hIP hT hPA hX hni <|
  midDecStWL29

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

/-- (p3J gen 50) **`KNo88L` [S]: label 88 out of scope at the invoked slot only** (module docstring): at every
dispatch state of an entry, if the current thread's message label is 88 (`TCBSetEPTRoot`), the slot the spec's
`lookupCapAndSlot` returns for the CAP register (`LookAt`) does not hold a Thread cap. Defined for the comparison
with `KNo88`; the new top `kernel_entry_runMcWKR_sysLzy` does not need it (the entry's `SysK6` covers the case). -/
def KNo88L (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
    ∀ (ct : U64) (info : msginfo.MessageInfo), sched.cur_thread st s' = ok ct → msg.msg_info st s' ct = ok info →
      info.label = fl4_abi.label.TCBSetEPTRoot →
      ∀ (sl : Fl4Spec.CslotPtr) (p : U64), (∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) = ok (.Thread p) →
        ¬ LookAt ct (L.mem s' (Endp.regA ct layout.reg.CAP)) σb sl (.Thread p)

variable {arI AR MR}

/-- (p3J gen 50) **`KNo88 → KNo88L`** (the converse fails: `KNo88L` speaks only of the looked-up slot). -/
theorem kNo88L_of_kNo88 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : KNo88 (L := L) arI AR s a σ) :
    KNo88L (L := L) arI AR s a σ :=
  fun Z H Cs Ac Lst D J σb hBA s' a' hKF ct info hct hinfo hl sl p hsl hc _ =>
    h Z H Cs Ac Lst D J σb hBA s' a' hKF ct info hct hinfo hl sl p hsl hc

/-- (p3J gen 50) **`KNo88L` is not vacuous**: a state whose current message label at every dispatch state is not
88 satisfies it. -/
theorem kNo88L_of_label {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
      ∀ (ct : U64) (info : msginfo.MessageInfo), sched.cur_thread st s' = ok ct →
        msg.msg_info st s' ct = ok info → info.label ≠ fl4_abi.label.TCBSetEPTRoot) :
    KNo88L (L := L) arI AR s a σ :=
  fun _ _ _ _ _ _ _ σb hBA s' a' hKF ct info hct hinfo hl _ _ _ _ _ => h σb hBA s' a' hKF ct info hct hinfo hl

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **`InvDecStL` from `KNo88L`** instead of the entry's `SysK6` (the 88 case vacuous). -/
theorem invDecStL_of_no88L [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hPA : PPPlatA arI AR)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ)
    (hni : σ.curThread ≠ σ.idleThread) (hIB : SpecIrqB σ) (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : KNo88L (L := L) arI AR s a σ) :
    InvDecStL (L := L) arI AR MR Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hLk
  by_cases h88 : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetEPTRoot
  · obtain ⟨p, rfl, hl⟩ := h88
    exact absurd hLk (hN Z H Cs Ac Lst D J0 σb hBA s' a' hKF ct info hct a1 hl sl p hsl hc)
  · exact invDecFlat hARI hA hnd hMT hKD hIP hT hmax htu hPA hX hni hIB σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb
      hRRb ct hct hn info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs h88

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **`DispStabFootLzx` gives `DispStabFootLn`** with the globals (the assembly; module docstring). -/
theorem dispStabFootLn_of_Lzx [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzx (L := L) arI AR MR s a σ) :
    DispStabFootLn (L := L) arI AR MR s a σ where
  inv := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact dispInv_stFtL hA hnd (MachPlatF.toT hM hIp) hKD hX hct hi
      (invDecStL_of_k6 hARI hA hnd (MachPlatF.toT hM hIp) hKD hIA hT hmax htu ⟨hPAi, hT.mb⟩ hX hct
        (specIrqB_run hnd hR) hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    have := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midDecRestLn_of hARI hA hnd (MachPlatF.toT hM hIp) hKD hIA hT hmax htu ⟨hPAi, hT.mb⟩ hX hct
      (specIrqB_run hnd hR)
  midSpec := fun hR _ _ _ _ _ _ J _ _ _ hct _ _ _ => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midSpecAt_of hnd J hX hct
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzx` only and no scope
premise** (`hLzx` [J] = {midRecvSw}; globals verbatim as `_sysLzx`; label 88 excluded per entry, at the invoked
slot, by the entry's own `SysK6` antecedent; module docstring). -/
theorem kernel_entry_runMcWKR_sysLzy [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzx : DispStabFootLzx (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLn hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLn_of_Lzx hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hLzx)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 50) **The new top gives the previous one** (`_sysLzx` = `_sysLzy` plus the dropped `hNo : KNo88`). -/
theorem kernel_entry_runMcWKR_sysLzx_of_Lzy [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (_hNo : KNo88 (L := L) arI AR s a σ)
    (hLzx : DispStabFootLzx (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzy hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR hLzx

end

end Fl4Proofs.P3.Mc
