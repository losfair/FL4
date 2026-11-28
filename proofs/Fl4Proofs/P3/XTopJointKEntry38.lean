/-
P3 (DESIGN.md §9), invariant line G4 (g4d, KENTRY-PLAN g4d; g4b's handoff):
**`MR` at the chosen outcome of the invoking dispatch** (g4b's `JDispMRI`
[W]), carried through the invocation's posts instead of asked.

* `JAtM` := `JAt ∧ MR` at the spec outcome. `TopPostDMXP.mr` / `XCapP.mr`:
  a decode's `XCapP X XP` gives `XCapP (X ∧ MR) XP` when FL4's decode keeps
  `MR` at the dispatch state's machine state (MachKeepG4d's
  `MKD.decode_quiet`, `MKD.decode_cnode_nrd`) and the spec's decode yields
  only `QInv` invocations, whose perform (and the reply tail) keep the four
  machine fields (MachFieldFamI): every related outcome then has `MR`
  (`MachPlat.frame`).
* CNode Revoke / Delete: the deletion loop's invariant `EJLM` already carries
  `MRV` (mr6), so `cn_del_topJLMM` keeps it at the ok exit
  (`decode_invocation_cnode_{revoke,delete}JLMM`, `decode_invocation_cnodeJ_RDM`).
* `decOK_JMM`: the decode of every cap at `JAtM`: the quiet kinds (`QuietF`)
  and CNode at the other labels by `XCapP.mr` on `decOK_JMU`; CNode Revoke /
  Delete by `decode_invocation_cnodeJ_RDM`; Vcpu / Ept refuted by `J.ext.nat`;
  the loud kinds (`LoudF`: Thread, Untyped, IrqControl, IrqHandler, IoPort)
  from `JDecMRL` [W] (below).
* `handle_invocation_entryJMUM`: `handle_invocation_entryJMU` at `JAtM`
  (`handle_invocation_refinesMXP` is generic in `X`): the lookup fault and
  the extra caps' fault (`handle_fault`: `MKD.faults_handle_fault`,
  `mtk_handleFaultG`), the success tail (`flTail` writes no arch state,
  `mtk_specTailG`), the error reply (arch state kept,
  `mtk_fl4ReplyFromKernelErrorG`).
* The preemption path to `PPQJIM`: `JAtZ.handleIrqJIANM` (`handleIrqJIAN` with
  `MR`: the mask by `MachPlat.mask`, `mask_mr`; the acknowledgement by
  `MachPlat.ack`; the signal by `MKD.notification_send_signal` and
  `mtk_sendSignal'`), `afterInv_of_mcsIMNM`, `jPreemptRestHypEQ_ofIMM`,
  `hPre_ofZQIMNM` (every branch of `hPre_ofZQIMN` ends in `PPQJIM`).
* The dispatch: `invoke_afterJMUNM`, `dispatch_invokeJMUNM`,
  `dispatch_invokeJAllMUNM` (Send / NBSend / Call), `hiPostMid_M`,
  `mid_invRecvJMUNM`, `dispatch_midJMUNM` (ReplyRecv / NBSendRecv /
  NBSendWait: the receive by `MKD.syscall_handle_recv`, `mtk_handleRecvG`),
  `dispatch_all13PUNM` (every native syscall, `DispPostRM`).
* NEW TOPS `kernel_entryJ13PUGMD`, **`kernel_entryJ38`** = `kernel_entryJ37`
  without `hDM` (`JDispMRI`), with `hDL : JDecMRL` [W] at the same dispatch
  states; **`kernel_entry_reachMD`** = `kernel_entry_reachMI` with `hDL` for
  `hDM`.
-/
import Fl4Proofs.P3.XTopJointKEntry37
import Fl4Proofs.P3.MachKeepG4d
import Fl4Proofs.P3.MachFieldFamI
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JAt` with `MR` at the spec state** (module docstring). -/
abbrev JAtM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  JAt (L := L) arI AR s a σ ∧ MR a σ.machineState

/-- **[W] The loud cap kinds' decode at `JAtM`** (module docstring):
`JPreDecHypKM`'s shape (asked at the dispatch state, at the decode's own
values) for the native caps that are not `QuietF` (CNode, Thread, Untyped,
IrqControl, IrqHandler, IoPort), with `MR` at the chosen outcome of a
non-preempted invocation. l4v: `invoke_cnode_corres`, `invoke_tcb_corres`,
`invoke_untyped_corres`, `invoke_irq_control_corres`,
`invoke_irq_handler_corres`, the IO port `corres` with the machine state
shared (`do_machine_op` of `maskInterrupt`, `in8`/`out8`,
`preemption_point`). -/
def JDecMRL (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c → (LoudF c ∧ Vs.NativeCap c) →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

end

/-! ## Adding `MR` to a decode's post -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

theorem msF_restart {σ σ1 : Fl4Spec.State Unit}
    (h : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) :
    MachF.msF σ1 = MachF.msF σ :=
  congrArg Prod.fst (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single h))

theorem msF_qperf {inv : Fl4Spec.Fl4Invocation} (hq : MachT.QInv inv) {b c d : Bool} {σ1 : Fl4Spec.State Unit}
    {y : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) b c d inv).run σ1).1) :
    MachF.msF y.2 = MachF.msF σ1 :=
  congrArg Prod.fst (MachT.qInv_perform b c d inv hq σ1 y hy)

/-- **`TopPostDMXP` with `MR`** (module docstring). -/
theorem TopPostDMXP.mr (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMXP (L := L) X XP σ blk call don m s res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ inv, DecOut m σ inv → MachT.QInv inv) :
    TopPostDMXP (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) XP σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢; exact ⟨h4, hR⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢
      exact ⟨h4, msF_mr hM hR ((msF_qperf (hq inv h1) hy).trans (msF_restart h2))⟩

/-- **`TopPostRMX` with `MR`.** -/
theorem TopPostRMX.mr (hM : MachPlat arI MR) {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostRMX (L := L) X σ blk call don m ct s res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ inv, DecOut m σ inv → MachT.QInv inv) :
    TopPostRMX (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · exact Or.inl ⟨e, h1, h2, h3, h4, hR⟩
  · refine Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, msF_mr hM hR ?_⟩
    exact ((congrArg Prod.fst (MachT.mtk_specTailG call ct.bv rr σy z hz)).trans
      (msF_qperf (hq inv h3) h5)).trans (msF_restart h4)

/-- **`XCapP` with `MR`** (module docstring). -/
theorem XCapP.mr (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      MR r.2.2 σ.machineState ⦄)
    (hq : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → MachT.QInv inv) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mr hM h2 hq)
  · exact Or.inr (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mr hM h2 hq)

/-- The quiet FL4 kinds are quiet spec kinds. -/
theorem quietS_of {c : capability.Cap} (h : QuietF c) : MachT.QuietS (absCap c) := by
  cases c <;> simp only [QuietF] at h <;> simp [absCap, MachT.QuietS]

/-- **`MR` added to a post naming one spec outcome**, when FL4 keeps `MR` at
`σ0`'s machine state and every outcome keeps `msF`. -/
theorem spec_mrz (hM : MachPlat arI MR) {α β : Type} {m : Result α} {M : Set (β × Fl4Spec.State Unit)}
    {Q : α → β × Fl4Spec.State Unit → Prop} {g : α → A} {σ0 : Fl4Spec.State Unit}
    (h1 : m ⦃ r => ∃ z ∈ M, Q r z ⦄) (h2 : m ⦃ r => MR (g r) σ0.machineState ⦄)
    (h3 : ∀ z ∈ M, MachF.msF z.2 = MachF.msF σ0) :
    m ⦃ r => ∃ z ∈ M, Q r z ∧ MR (g r) z.2.machineState ⦄ :=
  WP.spec_mono (WP.spec_and h1 h2) fun _ ⟨⟨z, hz, hq⟩, hr⟩ => ⟨z, hz, hq, msF_mr hM hr (h3 z hz)⟩

end

/-! ## CNode Revoke / Delete at `JAtM` (the loop invariant carries `MRV`) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A Delete's or Revoke's outcome at `EJL`** (`cn_del_topJ` at `EJL`). -/
theorem cn_del_topJLMM {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hR : MR ar σ.machineState)
    {kb : U64} {K : Nat} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : PInvPostW (L := L) Z.th σ Z.G m (EJLM (L := L) arI AR MR Z H Cs kb K) (EJPM (L := L) arI AR MR Z H Cs kb K) s ar
      res) :
    TopPostDMXP (L := L) (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases hq with ⟨e, rfl, rfl, rfl, e', h1, h2⟩ |
    ⟨inv, hrun, σ1, hst, σ', G', hcase, hCR', hFI', -, hE'⟩
  · have hne : e ≠ .Preempted := by rintro rfl; cases e' <;> exact h2.elim
    refine Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ?_⟩
    simp only [core.result.Result.Err.injEq, hne, if_false]
    exact ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hR⟩
  · rcases hcase with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · obtain ⟨-, ⟨⟨V, Ac', Lst', D', J', -⟩, -⟩, hmv'⟩ := hE'
      have hX' := J'.xtop
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ?_⟩
      simp only [reduceCtorEq, if_false]
      exact ⟨⟨_, H, Cs, Ac', Lst', D', J', inferInstance⟩, hmv'.1⟩
    · obtain ⟨-, ⟨-, -, -, -, -, -, hDom, hMO⟩, hPre⟩ := hE'
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.error (), σ'),
        mem_bindE_err hx, ⟨Z.th, G', Or.inr ⟨rfl, rfl⟩, J.xtop.rel.1, hCR', hFI', hDom, hMO⟩, ?_⟩
      simp only [if_true]
      exact hPre

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Revoke label** (25): `cnode_revoke_refinesW` at
`EJL` (`JDelHypL`, `rppHyp_fullW` of `jPreemptHypL`, `EJL.restart`), then
`cn_del_topJL`. -/
theorem decode_invocation_cnode_revokeJLMM (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hMP : MachPlat arI MR) (hmv : MRV MR ar σ) (hJD : JDelHypLM (L := L) arI AR MR Z.th)
    (hJP : ∀ kb, PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPM (L := L) arI AR MR Z H Cs kb) Z.th)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.CNodeRevoke length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  have hfew : psiD (L.mem s) Z.G < 2 ^ 64 - 1 := by
    have := hDE.2.1 Z.G hM
    omega
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_revoke_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJLM (L := L) arI AR MR Z H Cs (L.ksb s) K)
      (EJPM (L := L) arI AR MR Z H Cs (L.ksb s) K)
      psiD psiD_slotsSame (hJD Z H Cs (L.ksb s) K rfl hK hK6)
      (rppHyp_fullW arI (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) (WJPM (L := L) arI AR MR Z H Cs (L.ksb s)) Z.th K
        (hJP (L.ksb s)))
      (EJLM.restart arI J hni hMP hmv hsg hP0 hLv hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩) hfew)
      fun res h => cn_del_topJLMM arI J hmv.1 h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hmv.1⟩

set_option maxHeartbeats 4000000 in
/-- **`XCap` at `JAt` at the Delete label** (26), for any cap: as
`decode_invocation_cnode_revokeJL`, by `cnode_delete_refinesW` at `EJL`. -/
theorem decode_invocation_cnode_deleteJLMM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hMP : MachPlat arI MR) (hmv : MRV MR ar σ) (hJD : JDelHypLM (L := L) arI AR MR Z.th) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ fl4_abi.label.CNodeDelete length slot (.CNode p r gs g) blk call
      don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, -⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  have hP := hX.rel.1
  unfold XCapP
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_delete_refinesW arI Z.th s ar σ Z.G hR hV hP hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI J.kern.act hcur htcb (EJLM (L := L) arI AR MR Z H Cs (L.ksb s) K)
      (EJPM (L := L) arI AR MR Z H Cs (L.ksb s) K)
      psiD (hJD Z H Cs (L.ksb s) K rfl hK hK6) (EJLM.restart arI J hni hMP hmv hsg hP0 hLv hDE hct)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩)
      (fun _ _ _ G1 hCR hE1 => ⟨hE1.1.2.2.1, hE1.1.2.2.2 G1 hCR.2.2.1⟩))
      fun res h => cn_del_topJLMM arI J hmv.1 h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hmv.1⟩

set_option maxHeartbeats 4000000 in
/-- **`decode_invocation_cnodeJ_stepsLM` at Revoke / Delete with `JAtM`
after** (the deletion loop's invariant `EJLM` carries `MRV`). -/
theorem decode_invocation_cnodeJ_RDM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hJDP : JDelParts (L := L) arI AR Z.th)
    (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hQ : ∀ e, Sched.EpQPre σ e)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hrd : 25 ≤ lbl.val ∧ lbl.val ≤ 26) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl)
      (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ : JStepHyps (L := L) arI AR Z.th := jStepHyps arI
  have hX := J.xtop
  have hJP : ∀ kb, PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPM (L := L) arI AR MR Z H Cs kb) Z.th :=
    fun kb => jPreemptHypLM arI hARI.toARKeep hT hnd hMP hPA Z H Cs kb rfl
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hJD := hJDP.jDelHypLM arI hT hnd hMP hKD hPA hARI.toMask
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  rcases (show lbl.val = 25 ∨ lbl.val = 26 by omega) with h | h
  · have e : lbl = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
    subst e
    exact decode_invocation_cnode_revokeJLMM arI s ar σ J hni hMP hmv hJD hJP hsg hP0 hLv slbl (by rw [hlbl]; simp [cnodeLabelOf])
      length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer
  · have e : lbl = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
    subst e
    exact decode_invocation_cnode_deleteJLMM arI s ar σ J hni hMP hmv hJD hsg hP0 hLv slbl (by rw [hlbl]; simp [cnodeLabelOf])
      length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps (cslotAddr sl) blk call don fp ci sl buffer

end

/-! ## The decode of every cap at `JAtM` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`decOK_JMU` at `JAtM`** (module docstring). -/
theorem decOK_JMM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length))
    (c : capability.Cap) (hc : capAt (L.mem s) (cslotAddr sl) = ok c)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra) (hLb : lbl.bv = slbl)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5)
    (hN : JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState) (hVT : ValidMachineTime σ)
    (hVI : ValidIrqMasks σ) (hNs : NativeScope σ) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hNat : Vs.NativeCap c := by
    obtain ⟨p, h1', h2'⟩ := id hsl
    have hx : IsSlot Z.th (cslotAddr sl) := AbsSlot.isSlot ⟨p, h1', Or.inl h2'⟩
    have := J.ext.nat _ hx
    rwa [capV_of_capAt hc] at this
  have hX0 := decOK_JMU arI s ar σ J hG hE ct hct lbl length blk call don fp buf extra slbl argsU hlen hargs
    hbuf hl ci sl hsl c hc excaps buffer hXO hXN hLb hA5 hN hPD hR hVT hVI hNs
  by_cases hq : QuietF c
  · by_cases hfbc : ∃ p m a', c = .Pml4 p m a' ∧ lbl = fl4_abi.label.X86PML4FrameBatch
    · -- the FrameBatch label on a PML4 cap: the batch keeps `MR` (XTopJointVsFb)
      obtain ⟨p, mp, asid, rfl, hlb⟩ := hfbc
      have hAs : AbsSlot Z.th sl := by
        obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
      have hok := (J.vsc.caps J.xtop.rel.2.1.2.2.1).at J.xtop.rel.2.1.2.2.1 hAs.isSlot hc (by simp)
      have hW := WP.spec_mono (decode_invocation_pml4_fbJVM arI s ar σ J hE.ni hG.delParts.archRef hG.tot lbl lbl.bv
        hlb ((pml4fb_label lbl).2 hlb) ct hct p asid mp (fun h => (hok.2.2 h).1) length buf blk call don fp argsU hlen
        hargs hbuf hl (fun h => (hok.2.2 h).2) hE.live hE.sg (J.ppr0_start arI hE.ni hE.rd0 hE.ctnq) hG.delParts
        hG.nd hG.ari hKD hR sl hAs hc extra excaps hXO hXN ci buffer) (fun _ h => h.2)
      exact XCapP.mr hM hX0 hW
        (fun inv hd => MachT.dec_quiet fp slbl _ ci sl (absCap _) excaps buffer (quietS_of hq) σ _ hd.1 inv rfl)
    · exact XCapP.mr hM hX0 (MKD.decode_quiet L.total hA hKD hq hR (fun p m a' hc' hl' => hfbc ⟨p, m, a', hc', hl'⟩))
        (fun inv hd => MachT.dec_quiet fp slbl _ ci sl (absCap c) excaps buffer (quietS_of hq) σ _ hd.1 inv rfl)
  by_cases hlo : LoudF c
  · exact hDL hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc ⟨hlo, hNat⟩
      excaps buffer hXO hXN hLb hA5 hN
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
  have hPl : Placed Z.th := J.xtop.rel.1
  cases c <;> simp only [QuietF, LoudF, not_true_eq_false, not_false_eq_true] at hq hlo
  case Vcpu p => exact absurd hNat (by simp [Vs.NativeCap])
  case Ept p l m asid va => exact absurd hNat (by simp [Vs.NativeCap])
  case CNode p r gs g =>
    have hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g := capV_of_capAt hc
    subst hLb
    obtain ⟨sl', hl', hd⟩ := cnode_canon lbl
    refine XCapP.lbl_congr arI (specDec_cnode p r gs g hd) ?_
    by_cases hrd : 25 ≤ lbl.val ∧ lbl.val ≤ 26
    · exact decode_invocation_cnodeJ_RDM arI s ar σ J hE.ni hG.ari hG.tot hG.delParts hE.sg hE.live hG.nd hM hKD
        hG.ppA ⟨hR, hVT, hVI⟩ hE.rd0 hE.ctnq lbl sl' hl' length buf ct hct argsU hlen hargs sl hAs p r gs g hsc extra
        (exAt extra 0) (exAt extra 1) (exAt_idx0 extra) (exAt_idx1 extra) excaps (ExtraOK.rel2 hPl hXO) hE.epQ
        blk call don fp ci buffer hrd
    · have hr : lbl ≠ fl4_abi.label.CNodeRevoke := fun e => hrd (by subst e; simp)
      have hd' : lbl ≠ fl4_abi.label.CNodeDelete := fun e => hrd (by subst e; simp)
      have hsr : Fl4Spec.genInvocationType sl' ≠ .cnodeRevoke := by
        rw [hl']; unfold cnodeLabelOf
        split_ifs <;> first | (intro e; cases e; done) | exact absurd (by omega) hrd
      have hsd : Fl4Spec.genInvocationType sl' ≠ .cnodeDelete := by
        rw [hl']; unfold cnodeLabelOf
        split_ifs <;> first | (intro e; cases e; done) | exact absurd (by omega) hrd
      exact XCapP.mr hM (XCapP.lbl_congr arI (specDec_cnode p r gs g hd).symm hX0)
        (MKD.decode_cnode_nrd L.total hA hKD hr hd' hR)
        (fun inv hdc => MachT.dec_cnode_q fp sl' _ ci sl _ _ _ excaps buffer hsr hsd σ _ hdc.1 inv rfl)

end

/-! ## `handle_invocation` at `JAtM` -/

section
variable {S A C : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

/-- `flTail` writes no arch state. -/
theorem MKD.fl_tail {s : S} {a : A} {t : U64} {call : Bool} (h : AR a c₀) :
    flTail (st := st) t call s a ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold Fl4Proofs.P3.flTail; mkd_walk

/-- The error reply writes no arch state. -/
theorem MKD.reply_err_tail {s : S} {a : A} {t : U64} {e : error.SysError} {is_call : Bool} (h : AR a c₀) :
    ((if is_call then do
        let s2 ← syscall.reply_error st s t e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ r => AR r.2.2 c₀ ⦄ := by
  mkd_walk

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`handle_invocation_entryJMU` at `JAtM`** (module docstring). -/
theorem handle_invocation_entryJMUM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct is_call blocking can_donate first_phase cptr)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hNs : NativeScope σ) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) true σ is_call blocking can_donate
        first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  have hA := hG.tot
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  have hF : ∀ {f : error.Fault} {f' : Fl4Spec.Fault}, CapFaultCorr f f' →
      faults.handle_fault st arI s ar ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
        RelTopM (L := L) r.1 z.2 ∧ JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ := fun hcf =>
    WP.spec_mono (spec_mrz hM (J.faultHypJZ hA hE.ni hct hE.ctnq hE.vfh hcf)
      (MKD.faults_handle_fault L.total hA hKD hR)
      (fun z hz => congrArg Prod.fst (MachT.mtk_handleFaultG _ _ σ z hz)))
      fun _ ⟨z, hz, ⟨h1, h2⟩, h3⟩ => ⟨z, hz, h1, h2, h3⟩
  refine handle_invocation_refinesMXP arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) true s ar σ Z.th Z.G
    hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hR⟩ ct hct hcur htcb
    is_call blocking can_donate first_phase cptr info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    ((J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf
      hbuffer hr2 her).imp id fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ => hF hcf⟩)
    (argsU.map UScalar.bv) hmrs
    (fun _ lf lf' hl => hF (capFaultCorr_lookup cptr hl))
    (fun s1 a1 σ' _ ⟨⟨_, _, _, _, _, _, J', _⟩, hR'⟩ hc =>
      WP.spec_mono (WP.spec_and (J'.flTailJ hc is_call) (MKD.fl_tail L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3, msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz))⟩)
    (fun a1 e e' ⟨⟨_, _, _, _, _, _, J'', _⟩, hR'⟩ he =>
      WP.spec_mono (WP.spec_and ((J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJ hcur is_call e e' he)
        (MKD.reply_err_tail (e := e) (t := ct) (s := s) (is_call := is_call) L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3, msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_when (MachT.mtk_fl4ReplyFromKernelErrorG _ _ _) σ z hz))⟩)
    (fun inv σ1 y hst hy => by
      rw [perfCurKeep _ _ _ inv σ1 y hy]
      obtain ⟨x, hk⟩ := (J.xtop.curTcb hcur).2
      rw [hcur] at hst
      have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
        rw [hst]; exact Set.mem_singleton _
      rw [Notif.setThreadState_eq .restart hk] at hm
      have e : σ1 = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      rw [e, Sched.stsAct_rec]; exact hcur) ?_
  obtain ⟨hLen, hArgs, hA5⟩ := J.argsJ J.xferH.1 J.xferH.2.1
    hct hinfo hmi hbuf hbuffer hmrs
  intro sl c e exs hsl hc hget h1 h2
  have hl : argsU.length ≤ 120 := by
    have hm := Endp.msg_info_spec (L := L) s ct
    rw [hinfo, WP.spec_ok] at hm
    have h120 := hm.2.2.2
    have h4 : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
    rw [← hLen]; unfold msgLen
    split_ifs <;> omega
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct
    hinfo hmi hbuf hbuffer hr2 her
  have hXN : ExtraNamed Z.th (L.mem s) e := by
    have h := lookup_extra_named Z.th s σ J.dstate.1.1 J.dstate.1.2.1 htcb buf info
    rw [hr2, WP.spec_ok] at h
    exact h e h1
  exact decOK_JMM arI s ar σ J hG hE ct hct info.label (msgLen info buf) blocking is_call can_donate first_phase
    buf e mi.miLabel argsU hLen hArgs hbuf hl (Fl4Spec.toBl cptr.bv) sl hsl c hc exs buffer
    (hXO e exs h1 h2) hXN hLb hA5 (hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs hsl hc hget h1 h2)
    hPD hDL hR hVT hVI hNs hM hKD hA

end



/-! ## The preemption path with `MR` at the chosen outcome -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}
open Fl4Proofs.P1

/-- FL4's `mask_irq w true` is the spec's mask of line `i` at a related state. -/
theorem mask_mr (hM : MachPlat arI MR) {a a1 : A} {σ : Fl4Spec.State Unit} {w : U64} {i : Fl4Spec.Irq}
    (hR : MR a σ.machineState) (ha : arI.mask_irq a w true = ok a1) (hw : w.val < 256)
    (hiw : (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = i) : MR a1 (maskMs σ i true).machineState := by
  have h := hM.mask a w true σ.machineState hR hw
  rw [ha, WP.spec_ok] at h
  unfold maskMs
  rw [← hiw, show (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = w.bv.setWidth 8 from BitVec.ofNat_toNat 8 w.bv]
  exact h

set_option maxHeartbeats 16000000 in
/-- **`handleIrqJIAN` with `MR` at the chosen outcome**: the mask by
`MachPlat.mask` (`mask_mr`), the acknowledgement by `MachPlat.ack`, the
signal by `MKD.notification_send_signal` and `mtk_sendSignal'`. -/
theorem JAtZ.handleIrqJIANM (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hN : NativeScope σ) (hR : MR a σ.machineState)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      σ.interruptStates i = .irqInactive ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ := by
  have hX := J.xtop
  have hIR : IrqRel (L.mem s) (L.ksb s) σ := hX.fin.1.1.2.2.2.1
  have hARa : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hiw : (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = i := by
    apply BitVec.eq_of_toNat_eq; simp [hwi]
  -- the acknowledgement keeps `JAt`
  have hack : ∀ (s1 : S) (a1 : A) (z : Unit × Fl4Spec.State Unit),
      z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1 → JAtM (L := L) arI AR MR s1 a1 z.2 →
      (do let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
        σ.interruptStates i = .irqInactive ∨
          ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ := by
    rintro s1 a1 z hz ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1, _⟩, hR1⟩
    refine WP.spec_bind (WP.spec_and (hIP.ackAR a1 w _ J1.xtop.fin.1.1.2.2.2.2.2.2) (hM.ack a1 w _ hR1)) ?_
    rintro a2 ⟨hA2, hR2⟩
    obtain ⟨Lst2, J2⟩ := J1.msArJ z.2.machineState a2 rfl (fun _ => hA2)
    exact (WP.spec_ok _).2 (Or.inr ⟨z, hz, ⟨Z1, H1, Cs1, Ac1, Lst2, D1, J2, inferInstance⟩, hR2⟩)
  unfold interrupt.handle_interrupt
  rw [irq_max_eq]
  simp only [bind_ok]
  by_cases hbig : w > 127#u64
  · -- above FL4's maximum
    rw [if_pos hbig]
    have hgt : i > Fl4Spec.maxIRQ := by
      have : 127 < w.val := hbig
      show (125 : BitVec 8) < i
      rw [BitVec.lt_def]; simp; omega
    obtain ⟨a1, ha1⟩ := maskIrq_total arI hAT a w true
    rw [ha1]
    simp only [bind_ok]
    have hA1 : AR a1 σ.archState.x64CurrentCr3 := hARI.mask _ _ _ hARa (Or.inr (Or.inl ⟨w, true, ha1⟩))
    obtain ⟨Lst1, J1⟩ := J.msArJ (maskMs σ i true).machineState a1 rfl (fun _ => hA1)
    exact hack s a1 _ (mem_hi_big hgt σ) ⟨⟨Z, H, Cs, Ac, Lst1, D, J1, inferInstance⟩, mask_mr hM hR ha1 (by rw [hwi]; exact i.isLt) hiw⟩
  · rw [if_neg hbig]
    have hw : w.val ≤ 125 := by
      have : ¬ 127 < w.val := hbig
      omega
    have hw128 : w.val < 128 := by omega
    have hle : ¬ i > Fl4Spec.maxIRQ := by
      show ¬ (125 : BitVec 8) < i
      rw [BitVec.lt_def]; simp; omega
    have hst : σ.interruptStates i = irqSt (L.mem s (irqStA (L.ksb s) w)) := by
      rw [← hiw]; exact hIR.st w hw128
    rw [irq_state_eq']
    simp only [bind_ok, irqSig_eq, irqTimer_eq, irqIpi_eq, irqInactive_eq]
    set v := L.mem s (irqStA (L.ksb s) w) with hv
    -- the branches before the acknowledgement
    have key : ∀ m : Result (S × A), m ⦃ r => σ.interruptStates i = .irqInactive ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ →
        (do let (s1, a1) ← m; let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
          σ.interruptStates i = .irqInactive ∨
            ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ := by
      intro m hm
      refine WP.spec_bind hm ?_
      rintro ⟨s1, a1⟩ (hf | ⟨z, hz, hJ1⟩)
      · refine WP.spec_bind (hAT.ack_irq a1 w) ?_
        intro a2 _
        exact (WP.spec_ok _).2 (Or.inl hf)
      · exact hack s1 a1 z hz hJ1
    refine key _ ?_
    by_cases h1 : v = 1#u64
    · -- a signal line
      rw [if_pos h1]
      have hsig : σ.interruptStates i = .irqSignal := by rw [hst, h1]; rfl
      have hL : IntLayout Z.th (L.ksb s) := J.intL
      have hnode := hL.node w hw128
      obtain ⟨cs, hkc, hwf, hsl⟩ := hX.rel.2.1.1.cnode _ 0 hnode
      obtain ⟨c, ac, hcap, hcs, hCR⟩ := hsl [] rfl
      rw [show slotAddr (nodeA (L.ksb s) w).bv (Fl4Spec.ofBl []) = nodeA (L.ksb s) w from
        cslotAddr_nil _] at hcap
      have hgc : Fl4Spec.getCap (Z := Unit) (σ.interruptIrqNode i, []) σ = ({(ac, σ)}, False) := by
        rw [← hiw, hIR.node w hw128]; exact getCap_cnode hkc hwf hcs
      have hac : ac = absCap c := hCR.abs
      rw [irq_slot_eq]
      simp only [bind_ok]
      rw [slot_cap_eq, hcap]
      simp only [bind_ok]
      -- the mask after the cap's case
      have hmask : ∀ (s3 : S) (a2 : A) (σ1 : Fl4Spec.State Unit),
          ((), σ1) ∈ (Fl4Spec.NonDet.when (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)
            (Fl4Spec.sendSignal (Z := Unit) (Fl4Spec.objRefOf ac) (Fl4Spec.capEpBadge ac)) σ).1 →
          JAtM (L := L) arI AR MR s3 a2 σ1 →
          (do let a3 ← arI.mask_irq a2 w true; ok (s3, a3)) ⦃ r =>
            σ.interruptStates i = .irqInactive ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ := by
        rintro s3 a2 σ1 h1' ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1, _⟩, hR1⟩
        obtain ⟨a3, ha3⟩ := maskIrq_total arI hAT a2 w true
        rw [ha3]
        simp only [bind_ok, WP.spec_ok]
        have hA3 := hARI.mask _ _ _ J1.xtop.fin.1.1.2.2.2.2.2.2 (Or.inr (Or.inl ⟨w, true, ha3⟩))
        obtain ⟨Lst3, J3⟩ := J1.msArJ (maskMs σ1 i true).machineState a3 rfl (fun _ => hA3)
        exact Or.inr ⟨((), maskMs σ1 i true), mem_hi_signal hle hsig hgc h1', ⟨Z1, H1, Cs1, Ac1, Lst3, D1, J3, inferInstance⟩,
          mask_mr hM hR1 ha3 (by rw [hwi]; exact i.isLt) hiw⟩
      have hnone : ∀ (hP : ¬ (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)),
          (do let a3 ← arI.mask_irq a w true; ok (s, a3)) ⦃ r =>
            σ.interruptStates i = .irqInactive ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAtM (L := L) arI AR MR r.1 r.2 z.2 ⦄ :=
        fun hP => hmask s a σ (mem_when_false hP _ σ) ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hR⟩
      cases c with
      | Notification p b sd rv =>
        cases sd with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
          exact hnone (by rw [hac]; simp [absCap, Fl4Spec.isNtfnCap, Fl4Spec.capRights, Fl4Spec.AllowSend, rightsOf])
        | true =>
          simp only [↓reduceIte]
          have hP : Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac := by
            rw [hac]; exact ⟨rfl, rfl⟩
          have hobj : Fl4Spec.objRefOf ac = p.bv := by rw [hac]; rfl
          have hbd : Fl4Spec.capEpBadge ac = b.bv := by rw [hac]; rfl
          have hwhen : ∀ σ1, ((), σ1) ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ).1 →
              ((), σ1) ∈ (Fl4Spec.NonDet.when (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)
                (Fl4Spec.sendSignal (Z := Unit) (Fl4Spec.objRefOf ac) (Fl4Spec.capEpBadge ac)) σ).1 := by
            intro σ1 h; unfold Fl4Spec.NonDet.when; rw [if_pos hP, hobj, hbd]; exact h
          have hA : AbsSlot Z.th ((nodeA (L.ksb s) w).bv, []) := ⟨_, rfl, Or.inl hnode⟩
          have hpN := (J.slotN hA (by rw [cslotAddr_nil]; exact hcap)).1
          refine WP.spec_bind (WP.spec_and (J.signal_atN hAT hmb hN p b hpN)
            (MKD.notification_send_signal L.total hAT hKD hR)) ?_
          rintro ⟨s2, a2⟩ ⟨⟨σ', V', Ac', Lst'', D', hsp, -, J'⟩, hR2⟩
          exact hmask s2 a2 σ' (hwhen σ' (by rw [hsp]; rfl)) ⟨⟨_, H, Cs, Ac', Lst'', D', J', inferInstance⟩, msF_mr hM hR2
            (congrArg Prod.fst (MachT.mtk_sendSignal' p.bv b.bv σ ((), σ') (by rw [hsp]; exact Set.mem_singleton _)))⟩
      | _ =>
        simp only [bind_ok]
        exact hnone (by rw [hac]; simp [absCap, Fl4Spec.isNtfnCap])
    rw [if_neg h1]
    by_cases h2 : v = 2#u64
    · -- the timer line
      rw [if_pos h2]
      have htm : σ.interruptStates i = .irqTimer := by rw [hst, h2]; rfl
      step with P1.LawfulStore.cur_cpu_spec as ⟨cc, ecc⟩
      step with P1.obj.node_set.spec as ⟨s2, es2⟩
      step with P1.obj.node_set.spec as ⟨s3, es3⟩
      subst es2 es3 ecc
      have J2 := J.reprogramJ
      obtain ⟨Ac3, Lst3, D3, J3⟩ := J2.armedJ (L.cpu_wr _ _ _) 0#u64
      try simp only [WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_timer hle htm, ⟨Z, H, Cs, Ac3, Lst3, D3, J3, inferInstance⟩, hR⟩
    rw [if_neg h2]
    by_cases h3 : v = 3#u64
    · -- an IPI state on a line other than the IPI lines: reserved, nothing
      rw [if_pos h3]
      have hres : σ.interruptStates i = .irqReserved := by rw [hst, h3]; rfl
      unfold smp.handle_ipi
      rw [irq_resched_eq]
      have hne : ¬ w = 127#u64 := fun e => h127 (by rw [e]; rfl)
      simp only [bind_ok, hne, ↓reduceIte, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hR⟩
    rw [if_neg h3]
    by_cases h0 : v = 0#u64
    · -- an inactive line: the spec fails
      have hin : σ.interruptStates i = .irqInactive := by rw [hst, h0]; rfl
      obtain ⟨a1, ha1⟩ := maskIrq_total arI hAT a w true
      simp only [h0, ↓reduceIte, ha1, bind_ok, WP.spec_ok]
      exact Or.inl hin
    · have hres : σ.interruptStates i = .irqReserved := by
        rw [hst]; unfold irqSt; simp [h0, h1, h2]
      simp only [h0, ↓reduceIte, bind_ok, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hR⟩


set_option maxHeartbeats 16000000 in
/-- **`afterInv_of_mcsIMN` with `MR` at the chosen outcome** (`PPQJIM`): the
IRQ take moves `MR` (`MachPlat.takeAt`), the handler by `handleIrqJIANM`. -/
theorem afterInv_of_mcsIMNM (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧ NativeScope σ' ⦄)
    (hM : MachPlat arI MR) (hIP : IrqPlatA arI AR) (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJIM (L := L) arI AR MR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, ⟨Z', H', Cs', Ac', Lst', D', J', _⟩, hR1, hVI, hN'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hM.takeAt hR1) (hIP.takeAR a1 _ hAR1)) (hM.noIpi a1 _ hR1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum, hR2⟩, hAR2⟩, h126, h127⟩
  obtain ⟨Lst2, J2⟩ := J'.msArJ ms a2 hum (fun _ => hAR2)
  unfold syscall.check_interrupt
  by_cases hw : w = syscall.NO_IRQ
  · have hirq : irq = none := hnone.1 hw
    subst hirq
    have e : (w != syscall.NO_IRQ) = false := by simp [hw]
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ⟨rfl, ⟨((), { σ' with machineState := ms }),
      hm _ (mem_maybeHandle_none hIq), ⟨Z', H', Cs', Ac', Lst2, D', J2, inferInstance⟩, hR2⟩⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, hmask⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    refine WP.spec_bind (J2.handleIrqJIANM hM hKD hARI hAT hIP hmbA hN' hR2 w i hwi h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ, hRz⟩)
    · exact absurd hf (gai_active hVI hIq i rfl)
    · exact (WP.spec_ok _).2 ⟨rfl, ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ, hRz⟩⟩



set_option maxHeartbeats 4000000 in
/-- **`jPreemptRestHypEQ_ofIM` ending in `PPQJIM`.** -/
theorem jPreemptRestHypEQ_ofIMM (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAtV (L := L) arI AR s a σ → NativeScope σ →
      MR a σ.machineState → ValidIrqMasks σ →
      σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ → CtNQ σ →
      CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
      ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
        Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
      ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
      syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJIM (L := L) arI AR MR σ (r.2.1, r.2.2) ⦄ := by
  have hK := hKD.toK
  intro s a σ hJ hn hR hV hi hs hf hc hg hnq hC hsc hnsuf hcov
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, _⟩ := hJ
  have hnt : ¬ NoTmoSend σ := fun h => hcov (Or.inl ⟨hC, hi, hs σ.curThread, h⟩)
  unfold NoTmoSend at hnt
  simp only [not_or, not_forall] at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨x0, n0, hk0, hp0⟩⟩ := hnt
  have hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := by
    intro x n hk; rw [hk0] at hk; cases hk; exact hp0
  obtain ⟨p, bd, r, hth⟩ : ∃ p bd r, xt.tcbTimeoutHandler = .endpointCap p bd r := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    obtain ⟨x1, -, -, -, hk1, -, hr1, -, -, -⟩ := schedulable_inv hsc
    rw [hkt] at hk1; cases hk1
    have hvm := hn _ _ hkt
    revert hr1 hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  have hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread := by
    rcases e : σ.schedulerAction with _ | u | _
    · exact Or.inl rfl
    · exact absurd e (hs u)
    · exact Or.inr rfl
  by_cases hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe
  · exact WP.spec_mono (afterInv_of_mcsIMNM hKD (mcsNS hn (Hh.mcsPPJAM hA (hmrt a) (hPA.minBudget a) hC hi hres hnq hsc hnsuf hkt
      hrr hth hper hcb hM hK hR hV)) hM hIA hARI hA hPA.minBudget _) fun _ h => h
  · simp only [not_forall] at hcb
    obtain ⟨xe, hke, hncb⟩ := hcb
    obtain ⟨q, rfl⟩ : ∃ q, xe = .recvEP q := by
      revert hncb; cases xe <;> simp [Endp.CanBlock]
    exact WP.spec_mono (afterInv_of_mcsIMNM hKD (mcsNS hn (Hh.mcsPPJRM hA hmax htu (hmrt a) (hPA.minBudget a) hC hi hres hnq hsc
      hnsuf hkt hrr hth hper ⟨q, hke⟩ hM hK hR hV)) hM hIA hARI hA hPA.minBudget _) fun _ h => h


set_option maxHeartbeats 4000000 in
/-- **`hPre_ofZQIMN` with `MR` at the chosen outcome** (`PPQJIM`): every
branch through `afterInv_of_mcsIMNM`. -/
theorem hPre_ofZQIMNM (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJIM (L := L) arI AR MR σ1 (r.2.1, r.2.2) ⦄ := by
  have hK := hKD.toK
  intro s1 a1 σ1 _ h hN1
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs, _⟩, hni, hns, hfr, hct, hcg, hnq, hR, -, hV⟩ :=
    jAtPreMV_holeQ hARI.toARKeep hA hnd hM hPA h
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact afterInv_of_mcsIMNM hKD (WP.spec_mono (Hh.mcsPPJZM hTs hA hnd (hmrt a1) (hPA.minBudget a1) hc hM hK hR hV)
      fun _ ⟨σ', h1, h2, hJ, hR', hV', hn⟩ => ⟨σ', h1, h2, hJ, hR', hV', hn hN1⟩) hM hIA hARI hA hPA.minBudget _
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcsIMNM hKD (mcsNS hN1 (Hh.mcsPPJIM hi hA hM hK hR hV)) hM hIA hARI hA hPA.minBudget _)
      fun _ h => h
  by_cases hC : CurInv σ1
  · cases hsc : Fl4Spec.schedulable σ1.curThread σ1 with
    | true =>
      by_cases hsuf : ∀ y n, σ1.kheap σ1.curSc = some (.schedContext y n) →
          Fl4Spec.refillSufficient σ1.consumedTime (Fl4Spec.refillHd y) = true
      · exact WP.spec_mono (afterInv_of_mcsIMNM hKD (mcsNS hN1 (Hh.mcsPPJSM hTs hA hnd (hPA.minBudget a1) hC hni hsc hsuf hM hK hR hV))
          hM hIA hARI hA hPA.minBudget _) fun _ h => h
      · exact jPreemptRestHypEQ_ofIMM hARI hA hM hKD hPA hIA hmrt hmax htu s1 a1 σ1
          ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, inferInstance⟩
          hN1 hR hV hni hns hfr hct hcg hnq hC hsc hsuf
          fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi
    | false =>
      exact WP.spec_mono (afterInv_of_mcsIMNM hKD (mcsNS hN1 (Hh.mcsPPJCM hA (hmrt a1) (hPA.minBudget a1) hC hni hns hsc hM hK hR hV))
        hM hIA hARI hA hPA.minBudget _) fun _ h => h
  · have hsch : Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1 with
      | false => rfl
      | true => exact absurd (curInv_of_sched hct e) hC
    exact WP.spec_mono (afterInv_of_mcsIMNM hKD (mcsNS hN1 (Hh.mcsPPJUM hA (hmrt a1) (hPA.minBudget a1) hC hct hfr hcg hsch hi
      hM hK hR hV)) hM hIA hARI hA hPA.minBudget _) fun _ h => h


end


/-! ## The invoking dispatch with `MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
theorem invoke_afterJMUNM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (call bl don : Bool)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQJIM (L := L) arI AR MR σ1 (r.2.1, r.2.2) ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call bl don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => DispPostRM (L := L) arI AR MR (DispInv call bl don) σ r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have top : ∀ y, y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false
      (Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv)).run σ).1 → y ∈ ((DispInv call bl don).run σ).1 :=
    fun y hy => mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (handle_invocation_entryJMUM arI s ar σ J ct hct call bl don false _ hG hE hP hPD hDL hR hVT hVI hN hM hKD) ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
  rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
  · show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    refine hok ?_
    have hXM := ifP_X (X := JAtM (L := L) arI AR MR) (XP := JAtPreMV (L := L) arI AR MR) (fun h => by cases h) hX
    exact ⟨y, top y hy, Or.inl ⟨hy1, hrel, hXM.1.toRE, hXM.2⟩⟩
  · rw [if_pos rfl] at hX
    refine WP.spec_bind (hPre s1 a1 y.2 hrel hX (SInv.ns_fl4HandleInvocationR true call bl don false _ σ hN y hy)) ?_
    rintro ⟨b, s2, a2⟩ hQ
    refine hok ?_
    exact ⟨y, top y hy, Or.inr ⟨hy1, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_invokeJMUNM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQJIM (L := L) arI AR MR σ1 (r.2.1, r.2.2) ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r => DispPostRM (L := L) arI AR MR (DispInv call bl don) σ r ⦄ := by
  have h := invoke_afterJMUNM arI s ar σ J ct hct call bl don hG hE hP hPD hDL hR hVT hVI hN hM hKD hPre
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  have n65 : fl4_abi.syscall.SysNBSend ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysNBSend fl4_abi.syscall.SysSend; decide
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl]; exact h
  · rw [if_neg n65, if_pos rfl]; exact h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact h



end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`HIPostMXP.mid` at `JAtM`**: the mid state at `Ok` with `MR` at the same
outcome. -/
theorem hiPostMid_M {σ : Fl4Spec.State Unit} {don : Bool} {cptr : Fl4Spec.CapRef}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : HIPostMXP (L := L) (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) true σ false false don true cptr res)
    (hM : JMidRunHyp true don cptr σ) (hE : MidEntry σ) :
    ∃ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false don true cptr).run σ).1,
      (res.1 = .Ok () ∧ y.1 = .ok () ∧ JMid (L := L) arI AR res.2.1 res.2.2 y.2 ∧ MR res.2.2 y.2.machineState) ∨
      (res.1 = .Err .Preempted ∧ y.1 = .error () ∧ RelTopM (L := L) res.2.1 y.2 ∧
        JAtPre (L := L) arI AR res.2.1 res.2.2 y.2) := by
  obtain ⟨y, hy, hc, hR, hX⟩ := h
  refine ⟨y, hy, ?_⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hJ := ifP_X (X := JAtM (L := L) arI AR MR) (XP := JAtPreMV (L := L) arI AR MR)
      (by rw [h1]; intro e; cases e) hX
    have hC := hM hE y hy h2
    obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J, _⟩, hMR⟩ := hJ
    exact Or.inl ⟨h1, h2, ⟨hR, ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hC, curRun_ne_idle hC J.act.2⟩, hMR⟩
  · rw [h1, if_pos rfl] at hX
    exact Or.inr ⟨h1, h2, hR, hX.toPre⟩

set_option maxHeartbeats 4000000 in
theorem mid_invRecvJMUNM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool)
    (hrg : regIdx sr = rg)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct rg))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ r =>
      DispPostRM (L := L) arI AR MR (DispMid sr cr) σ r ⦄ := by
  have hMP := hM
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs sr) =
      Fl4Spec.toBl (L.mem s (regA ct rg)).bv := by
    rw [← hrg, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' sr
  rw [hcp] at hreg
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJMUM arI s ar σ J ct hct false false true true _ hG hE hP
    hPD hDL hR0 hVT hVI hN hM hKD)
    fun res h => And.intro (hiPostMid_M h (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) h) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM, hMm⟩ | ⟨hr1, hy1, hrel, hX⟩⟩, hMV⟩
  · dsimp only at hr1 hy1 hM
    subst hr1 hy1
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    show (if true = true then syscall.handle_recv st arI s1 a1 true cr else ok (s1, a1)) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_mono (spec_mrz hMP (hR _ hy rfl s1 a1 hM) (MKD.syscall_handle_recv L.total hA hKD hMm)
      (fun z hz => congrArg Prod.fst (MachT.mtk_handleRecvG true cr _ z hz))) ?_
    rintro r ⟨z, hz, ⟨hrl, hJ⟩, hMz⟩
    exact ⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
      Or.inl ⟨rfl, hrl, hJ, hMz⟩⟩
  · dsimp only at hr1
    subst hr1
    obtain ⟨⟨u', σm'⟩, hy', hc', hrel', hX'⟩ := hMV
    have hu' : u' = .error () := by
      rcases hc' with ⟨h1, -⟩ | ⟨-, h2⟩
      · cases h1
      · exact h2
    subst hu'
    rw [if_pos rfl] at hX'
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Err .Preempted)
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    refine WP.spec_bind (hPre_ofZQIMNM hARI hA hnd hMP hKD hPA hIA hmrt hG.maxTU hG.tu s1 a1 σm' hrel' hX'
      (SInv.ns_fl4HandleInvocationR true false false true true _ σ hN _ hy')) ?_
    rintro ⟨b, s2, a2⟩ ⟨hb, hQ⟩
    dsimp only at hb; subst hb
    show (if false = true then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [if_neg (by decide)]
    exact hok ⟨_, mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_err hy'), Or.inr ⟨rfl, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_midJMUNM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (c : Fl4Spec.Syscall) (rg : U64)
    (sr : Fl4Spec.Register) (cr : Bool) (hn : MidSysR number c rg sr cr)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have h := mid_invRecvJMUNM s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hPD hDL hR0 hVT hVI hN hARI hA hnd hM hKD hPA hIA hmrt
  rw [fl4HandleSyscall_mid hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 rfl
  rcases hn with ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide), if_pos rfl]
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysReplyRecv; decide), if_pos rfl]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NBSEND_RECV_DEST) ?_
    rintro c2 rfl
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysReplyRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSendRecv; decide), if_pos rfl]
    exact h

set_option maxHeartbeats 4000000 in
/-- **The invoking dispatches ending in `PPQJI` under `MachPlat`**
(`dispatch_invokeJAll` with mr3's `hPre_ofZQIM`; no `PPPlat`/`IrqPlat`). -/
theorem dispatch_invokeJAllMUNM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAtM (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hDL : JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct)
    (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ := by
  rw [fl4HandleSyscall_inv hn]
  exact dispatch_invokeJMUNM arI s ar σ J ct hct number call bl don hn hG hE hP hPD hDL hR hVT hVI hN hM hKD
    fun s1 a1 σ1 h1 h2 h3 => WP.spec_mono (hPre_ofZQIMNM hARI hA hnd hM hKD hPA hIA hmrt hG.maxTU hG.tu s1 a1 σ1 h1 h2 h3)
      fun _ h => h.2

end

/-! ## Every native dispatch with `MR` at the chosen outcome -/

/-! ## The tops -/

end

end Fl4Proofs.P3
