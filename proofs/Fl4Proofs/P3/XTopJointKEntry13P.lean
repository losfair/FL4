/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr4): **`kernel_entryJ13P`, the
kernel entry under `MachPlat`, with no `PPPlat` / `IrqPlat` anywhere below it**
(irq1 NEXT (3), mr3 NEXT (c)). Every top up to `kernel_entryJ15M` takes
`PPPlat` (false: `PPPlat.false`) and `IrqPlat` (degenerate), directly and
through `JEntryGlob.pp`, so they are vacuous; this one is not (`j13P_platform`).

* The budget step under `MachPlat`: FL4's `check_budget_restart` has no
  clock/IRQ arch op after the timestamp (`MK.sched_check_budget`, `MRKeep` [P]),
  `MachF.mfk_checkBudgetRestart` (spec: the MR fields and the interrupt table
  kept), `budget_ok_mr` (FL4's `budget_ok` = one clock read), `budget_mr_at`
  (at the spec's budget outcome `σb`: `MR a1 σb.ms` and `ValidIrqMasks σb`).
* `JEntryGlobM`: `JEntryGlob` with `pp : PPPlat` replaced by its arch-only part
  `ppA : PPPlatA` [P].
* `JPreDecHyp` [W] (THE remaining path-restricted premise of mr3 NEXT (b)):
  at the dispatch state, with `MR ar σ.ms ∧ ValidMachineTime σ ∧
  ValidIrqMasks σ` there, the decode and invocation of a CNode, Thread or
  Untyped cap (exactly the cap kinds whose spec decode can yield a
  preemptible invocation, `NoPreKind`/`PreInv`) refines with `JAt` after and
  `JAtPreMV` after a preempted invocation (`XCapP … JAtPreMV`). Not ∀σ: it is
  asked only at the decode's own values (the hypotheses of `decOK_J`) at the
  state `kernel_entryJ13P` dispatches from. l4v: `invoke_cnode_corres`
  (revoke/delete), `invoke_tcb_corres` (threadControlCaps/Sched),
  `invoke_untyped_corres` (`reset_untyped_cap`) with the machine state shared
  (`preemption_point_corres`, `do_machine_op` corres) and `valid_machine_time`,
  `valid_irq_masks` kept. These three families are proved at `J` but only from
  `PPPlat` (their loops call `ppJD`); mr4's `JAtZ.reset_loopJM` (UtResetLoopJM)
  is the first loop redone under `MachPlat`.
* `decOK_JM`: `decOK_J` with `JEntryGlobM` and `JAtPreMV`; every other cap
  kind by its existing J lemma (none preempts: `XCapP.reXP` /
  `specDec_noPreK` move `XP`).
* `handle_invocation_entryJM`, `invoke_afterJM`, `dispatch_invokeJM`,
  `dispatch_invokeJAllM` (preemption path by mr3's `hPre_ofZQIM`),
  `mid_invRecvJM`, `dispatch_midJM`, `KDispHyps13P` (= `KDispHyps15M` with
  `JEntryGlobM`, `JPreDecHyp`, and `ValidMachineTime` [J] at the dispatch
  state), `dispatch_all13P`, `kernel_entryJ13P`.
-/
import Fl4Proofs.P3.XTopJointKEntry15M
import Fl4Proofs.P3.XTopJointMRHole2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

namespace MachF
open Fl4Spec Fl4Proofs.P3.Vs

/-- **The spec's budget check keeps the MR fields and the interrupt table.** -/
theorem mfk_checkBudgetRestart : MFK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  mfk_auto
  all_goals exact mfk_checkBudget

end MachF


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {MR : A → Fl4Spec.MachineState → Prop}

/-- **FL4's `budget_ok` reads the clock once** (`update_timestamp_mr`, then
`check_budget_restart` by `MRKeep`). -/
theorem budget_ok_mr (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hA : P0.ArchTotal arI) {a : A}
    {ms : Fl4Spec.MachineState} (hR : MR a ms) (s : S) :
    syscall.budget_ok st arI s a ⦃ r => MR r.2.2 (gctState ms) ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (update_timestamp_mr hM hR s) ?_
  rintro ⟨s1, a1⟩ h1
  have hS := L.total
  unfold sched.check_budget_restart
  refine WP.spec_bind (MK.sched_check_budget hS hA hK h1) ?_
  rintro ⟨r, s2, a2⟩ h2
  simp only at h2
  mk_walk

/-- **`MR` and `ValidIrqMasks` at the spec's budget outcome**: the
timestamp's one clock read (`updateTimeStamp_eq'`) and `checkBudgetRestart`
keeping `msF`. -/
theorem budget_mr_at (hM : MachPlat arI MR) (hnd : Fl4Spec.numDomains = 1) {σ0 σb : Fl4Spec.State Unit} {b : Bool}
    (hmem : (b, σb) ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0).1)
    {a1 : A} (hR : MR a1 (gctState σ0.machineState)) (hVI : ValidIrqMasks σ0) :
    MR a1 σb.machineState ∧ ValidIrqMasks σb := by
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hmem
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hms : σu.machineState = gctState σ0.machineState := by rw [e]
  have his : σu.interruptStates = σ0.interruptStates := by rw [e]
  have hk := MachF.mfk_checkBudgetRestart σu _ h2
  have hRu : MR a1 σu.machineState := hms ▸ hR
  refine ⟨msF_mr hM hRu hk, msF_vim (σ := σu) ?_ hk⟩
  intro i hi
  rw [hms]
  exact hVI i (his ▸ hi)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`XCapP` at another `XP`** when the cap's spec decode yields no
invocation with a preemption point (`TopPostDMX.not_preempted`). -/
theorem XCapP.reXP {X XP XP' : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hnp : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → ¬ NoPre.PreInv inv) :
    XCapP (L := L) arI X XP' s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono h fun res hr => ?_)
    have hne := TopPostDMX.not_preempted hr hnp
    have hI : ∀ s a σ, (if res.1 = .Err .Preempted then XP s a σ else X s a σ) →
        (if res.1 = .Err .Preempted then XP' s a σ else X s a σ) := fun s a σ hx => by
      rw [if_neg hne] at hx ⊢; exact hx
    exact match hr with
    | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, hI _ _ _ h4⟩
    | Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩ => Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hI _ _ _ h4⟩
  · exact Or.inr h

variable {arI} in
/-- `HIPostMXP` at `JAtPreMV` gives it at `JAtPre`. -/
theorem HIPostMXP.toPreMV {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}
    {X : S → A → Fl4Spec.State Unit → Prop} {rep : Bool} {σ : Fl4Spec.State Unit} {c b d f : Bool}
    {cptr : Fl4Spec.CapRef} {res : core.result.Result Unit error.Exc × S × A}
    (h : HIPostMXP (L := L) X (JAtPreMV (L := L) arI AR MR) rep σ c b d f cptr res) :
    HIPostMXP (L := L) X (JAtPre (L := L) arI AR) rep σ c b d f cptr res := by
  obtain ⟨y, hy, hc, hR, hX⟩ := h
  refine ⟨y, hy, hc, hR, ?_⟩
  by_cases hp : res.1 = .Err .Preempted
  · rw [if_pos hp] at hX ⊢; exact hX.toPre
  · rw [if_neg hp] at hX ⊢; exact hX

/-- **[P]/[J]/[W] The global premises without `PPPlat`** (module docstring):
`JEntryGlob`'s fields, `pp` replaced by `ppA`. -/
structure JEntryGlobM (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [P] the arch relation's interface (`ARKeep`, `ARMask`). -/
  ari : ARIface arI AR
  /-- [P] the arch operations total. -/
  tot : P0.ArchTotal arI
  /-- [J]/[P] XTopJointDelR's `JDelParts`: the deletion's named steps (its
  own fields tagged there): platform and scope facts only. Every deletion
  runs at `WJL` from `JEntryAt.live` (CNode, IRQ handler: `JDelParts.jDelHypL`;
  the Thread cap's installs: XTopJointTcbInsL's `tcbInsW_wjl`). -/
  delParts : JDelParts (L := L) arI AR th
  /-- [P] one domain. -/
  nd : Fl4Spec.numDomains = 1
  /-- [P] the arch-only part of the preemption point's platform (`PPPlatA`:
  the IRQ read keeps `AR`, `min_budget`); the clock and the IRQ line are
  `MachPlat`'s, at the top. -/
  ppA : PPPlatA arI AR
  /-- [P] the domain configuration (`DomConfig`). -/
  dom : DomConfig
  /-- [P] the port-in values (`PortInVal`, the IO port decode for a call). -/
  portIn : PortInVal arI
  /-- [P] the platform's timer agreement (`TimeAgree`; the Thread cap's
  SetSchedParams, `bind_tcb_refines`). -/
  timeAg : TimeAgree arI
  /-- [P] the platform's timer constants for a timeout fault's consumed time
  (`maxTicksToUs`, `ticks_to_us` at every arch state; as `JSchedCPath`'s
  `max`/`tu`): the reply's `do_fault_transfer` of a replier with a timeout
  fault and an SC (`JAtZ.xferAllJ`). -/
  maxTU : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄


/-- **[W] The preempting cap kinds' decode and invocation at the dispatch
state** (module docstring): with `MR`, `ValidMachineTime` and
`ValidIrqMasks` at the dispatch state, a CNode, Thread or Untyped cap's
decode at the front end's values (`decOK_J`'s hypotheses) gives `XCapP` with
`JAtPreMV` after a preempted invocation. -/
def JPreDecHyp (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c → (NoPreKind c → False) →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPath (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c blk call
      don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable {arI} in
set_option maxHeartbeats 4000000 in
/-- **The notification cap's leaf at `J` with `NativeScope` at the invocation's
state** (g3e): `notifLeafJ` with no `SignalRestJHyp`. The spec's restart writes
`Restart` (`SInv.ns_setThreadState`), so `NativeScope` holds at the restart
state, where `JAtZ.signal_atN` (g3b) signals. -/
theorem notifLeafJN (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hN : NativeScope σ) (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← notification.send_signal st arI s1 ar p b
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1) := by
  intro _
  have hpN := (J.slotN hA hc).1
  obtain ⟨s1, σ1', x, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hN1 := SInv.ns_setThreadState σ.curThread .restart (by intro e; cases e) σ hN _
    (by rw [hst1]; exact Set.mem_singleton _)
  obtain rfl := restart_out_eq hst1 hst
  rw [hs1]
  simp only [bind_ok]
  refine WP.spec_bind (J1.signal_atN hAT hmb hN1 p b hpN) ?_
  rintro ⟨s2, a1⟩ ⟨σ', V', Ac', Lst', D', hsp, -, J'⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ((), σ'), by rw [hsp]; exact Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J'⟩

set_option maxHeartbeats 4000000 in
theorem decOK_JM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
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
    (hN : JPath (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c)
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState) (hVT : ValidMachineTime σ)
    (hVI : ValidIrqMasks σ) (hNs : NativeScope σ) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c blk call
      don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨σ1, hst⟩ := XTop.restart (L := L) (show XTop (L := L) AR s ar σ from ⟨Z, J.xtop⟩)
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hsc : capV (L.mem s) (cslotAddr sl) = c := capV_of_capAt hc
  have hni := hE.ni
  have hLv := hE.live
  have hP0 := J.ppr0_start arI hni hE.rd0 hE.ctnq
  have hPl : Placed Z.th := J.xtop.rel.1
  cases c
  case Null =>
    refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  case Zombie p zt n =>
    refine XCap.toPN arI (Or.inl ?_) (specDec_noPreK (by trivial))
    unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  case Endpoint p b sd rv g gr =>
    exact XCap.toPN arI (Or.inl (decode_endpointDMX arI _ s ar σ lbl length _ p b sd rv g gr blk call don fp buf extra
      slbl _ ci sl excaps buffer ct hct hX0 hst fun _ => sendLeafJ2 hG.tot J hni hE.ctnq hE.cnf hct hAs hc hst blk call g gr don
        hX0)) (specDec_noPreK (by trivial))
  case Notification p b sd rv =>
    exact XCap.toPN arI (Or.inl (decode_notificationDMX arI _ s ar σ lbl length _ p b sd rv blk call don fp buf extra
      slbl _ ci sl excaps buffer ct hct hX0 hst fun _ => notifLeafJN hG.tot hG.ppA.minBudget J hNs
        hni hct hAs hc hst hX0)) (specDec_noPreK (by trivial))
  case Reply p g =>
    exact XCap.toPN arI (Or.inl (decode_replyDMX arI _ s ar σ lbl length _ p g blk call don fp buf extra slbl _ ci sl
      excaps buffer ct hct hst (replyLeafJ hG.tot hG.maxTU hG.tu hG.ppA.minBudget J hni hct hAs hc hst
        (runTmoP_recv _ hG.tot hG.maxTU hG.tu) hX0))) (specDec_noPreK (by trivial))
  case CNode p r gs g =>
    exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc (fun h => h)
      excaps buffer hXO hXN hLb hA5 hN
  case Thread p =>
    exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc (fun h => h)
      excaps buffer hXO hXN hLb hA5 hN
  case IoPort first last z =>
    have hOpen := hN
    by_cases h0 : z = 0#u64
    · subst h0 hLb
      exact (decode_invocation_ioportJ arI s ar σ J hni hG.ari hG.tot (J.zNoBlk hE.sg) lbl lbl.bv (port_label lbl) length buf ct
        hct argsU hlen hargs sl hAs first last hsc call (fun _ => hG.portIn) blk don fp extra ci excaps buffer).toPN
        arI (specDec_noPreK (by trivial))
    · exact XCapP.reXP arI (hOpen h0) (specDec_noPreK (by trivial))
  case IrqControl =>
    subst hLb
    have hex := ExtraOK.rel1 hPl hXO
    obtain ⟨nA, hnum, hnA⟩ := hE.ioapics
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    exact (decode_invocation_irq_controlJ arI s ar σ J hni hG.ari hG.tot (J.zNoBlk hE.sg) hE.handlers lbl lbl.bv (irqControl_label lbl)
      (irqControl_remap lbl) length buf ct hct argsU hlen hargs J.act2 extra _ (exAt_idx0 extra) excaps hex hth0 rfl hc nA hnum hnA hE.archIrq
      blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
  case IoPortControl =>
    subst hLb
    have hex := ExtraOK.rel1 hPl hXO
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    exact (decode_invocation_ioport_controlJ arI s ar σ J hni hG.ari hG.tot (J.zNoBlk hE.sg) hE.ports lbl lbl.bv (ioControl_label lbl)
      length buf ct hct argsU hlen hargs J.act3 extra _ (exAt_idx0 extra) excaps hex hth0 rfl hc blk call don fp ci
      buffer).toPN arI (specDec_noPreK (by trivial))
  case IrqHandler irq =>
    subst hLb
    obtain ⟨sl', hl', hd⟩ := irqH_canon lbl
    refine XCapP.lbl_congr arI (specDec_irqH irq hd) ?_
    have hx0 := exAt_idx0 extra
    have hex : lbl.val = 35 → ExtraSRel Z.th (L.mem s) (exAt extra 0) excaps := fun _ => ExtraOK.relS hPl hXO
    have hirq : irq.val < 128 := (slot_cap_wf J.xtop hAs hsc).1
    -- SetNotification's extra slot is no IRQ node slot (JEntryIrq: the
    -- lookup's CNode is named by a cap, `SpecGlob.ref`)
    have hxn : lbl.val = 35 → exAt extra 0 ≠ nodeA (L.ksb s) irq := fun _ => J.irqExtraNe hE.sg hXN hirq
    exact (decode_invocation_irq_handlerJL arI s ar σ J hni hE.sg hP0 hLv hG.ari hG.tot
      lbl sl' hl' ct hct sl hAs irq hsc
      (irqSlotOK_of_spec J.intL J.dstate.1.1 J.xtop.fin.1.1.2.2.2.1 hE.sg.irqNode hirq)
      extra _ hx0 excaps hex hxn J.domPlaced (J.irqDelP1J hni hct hirq) length buf blk call
      don fp _ ci buffer).toPN arI (specDec_noPreK (by trivial))
  case Domain =>
    subst hLb
    obtain ⟨sl', hl', hd⟩ := dom_canon lbl
    refine XCapP.lbl_congr arI (specDec_dom hd) ?_
    have hex := ExtraOK.relS hPl hXO
    exact (decode_invocation_domainJ arI hG.dom s ar σ J hni hG.ari (J.zNoBlk hE.sg) ct hct J.ksOut J.actK lbl sl' hl' length
      buf argsU hlen hargs extra _ (exAt_idx0 extra) excaps hex _ blk call don fp ci sl buffer).toPN arI (specDec_noPreK (by trivial))
  case SchedContext p sb =>
    obtain ⟨hP, hY⟩ := hN
    obtain ⟨hpC, hpi, hsb, hssz, hback, hbn⟩ := J.scCtxCap arI hAs.isSlot hc
    subst hLb
    obtain ⟨sl', hlbl, hsame, hd⟩ := sc_canon lbl
    refine XCapP.lbl_congr arI (specDec_sc p sb hd) ?_
    by_cases hl : ScJLabel s lbl p
    swap
    · by_cases hu : lbl = fl4_abi.label.SchedContextUnbind
      · exact (decode_invocation_sched_context_unbindJ s ar σ J hni lbl sl' hlbl hu sb hpC hpi hback hct extra
          excaps length (cslotAddr sl) buf blk call don fp _ ci sl buffer).toPN arI (specDec_noPreK (by trivial))
      by_cases hy : lbl = fl4_abi.label.SchedContextYieldTo
      · have hYP := hY hy
        exact (decode_invocation_sched_context_yieldJ s ar σ J hni hG.tot hYP.mb hYP.max hYP.tu lbl sl' hlbl hy sb
          hpC hback hct extra excaps length (cslotAddr sl) buf blk call don fp _ ci sl buffer).toPN arI (specDec_noPreK (by trivial))
      · exact (decode_invocation_sched_context_otherJ s ar σ J lbl sl' hlbl (fun h => hl (Or.inl h))
          (fun h => hl (Or.inr (Or.inl h))) (fun h => hl (Or.inr (Or.inr h))) hu hy sb (fun h0 => (hback h0).1) hct
          extra excaps length (cslotAddr sl) buf blk call don fp _ ci sl buffer).toPN arI (specDec_noPreK (by trivial))
    have hN := hP hl
    obtain rfl : sl' = lbl.bv := hsame (by rcases hl with h | h | h <;> rw [h] <;> simp)
    have hex := ExtraOK.rel1 hPl hXO
    have hx0 := exAt_idx0 extra
    generalize exAt extra 0 = x0 at hex hx0
    have hxS : x0 ≠ 0#u64 → IsSlot Z.th x0 := fun h => by
      rcases hex with ⟨e, -⟩ | ⟨-, hs, -⟩
      · exact absurd e h
      · exact hs
    obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hni hct
    have hcs := ct_schedulable (J.curInv (by rw [hni.2]; simp)) J.act J.inv (hcur ▸ hkc) hrun
    rw [hcur] at hcs
    exact (decode_invocation_sched_contextJ s ar σ J hni.2 hN.tm hN.mb hN.max hN.tu Ipc.msgOK_holds lbl lbl.bv hlbl sb hpC
      hpi hl hback hbn hct hcs extra x0 hx0 excaps hex length (cslotAddr sl) buf blk call don fp _ ci sl buffer hc
      hAs.isSlot hsb hssz hxS hN.arch (hN.rest H Cs Ac Lst D J) (fun l44 =>
        sc_consumedReplyJ s ar σ J hni hG.tot hN.max hN.tu lbl lbl.bv hlbl l44 sb hpC hback hct extra
          excaps length (cslotAddr sl) buf blk call don fp)).toPN arI (specDec_noPreK (by trivial))
  case SchedControl cpu =>
    have hN : JSchedCPath (L := L) arI AR Z s ar σ lbl length cpu blk call don fp buf extra slbl argsU sl excaps ct := hN
    subst hLb
    have hex := ExtraOK.rel1 hPl hXO
    have hx0 := exAt_idx0 extra
    generalize exAt extra 0 = x0 at hex hx0
    have hxS : x0 ≠ 0#u64 → IsSlot Z.th x0 := fun h => by
      rcases hex with ⟨e, -⟩ | ⟨-, hs, -⟩
      · exact absurd e h
      · exact hs
    exact (decode_invocation_sched_controlJ s ar σ J hni hN.tm hN.mb hN.max hN.tu Ipc.msgOK_holds lbl lbl.bv (schedControl_label lbl) cpu length
      buf ct hN.core hct argsU hlen hargs extra x0 hx0 excaps hex
      (fun h _ _ hc => (J.scCtlExtra arI (hxS h) hc).1) (fun h _ _ hc => (J.scCtlExtra arI (hxS h) hc).2.1)
      (fun h _ _ hc => (J.scCtlExtra arI (hxS h) hc).2.2) (cslotAddr sl) blk call don fp ci sl
      buffer hN.arch (hN.rest H Cs Ac Lst D J)).toPN arI (specDec_noPreK (by trivial))
  case PageTable ptr mp asid va =>
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0 hLb
    obtain ⟨hlM, hlU, hlO⟩ := pt_label lbl
    have hw : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageTable ptr mp asid va) := by
      have h := J.vsc _ hAs.isSlot; rwa [capV_of_capAt hc] at h
    by_cases hoff : mp = true ∧ ptr ∉ Z.L1
    · obtain ⟨rfl, hnL⟩ := hoff
      have ht := hE.vsTyp _ hAs.isSlot
      rw [capV_of_capAt hc] at ht
      obtain ⟨hTy, hqa, hfr⟩ := ht hnL
      exact (decode_invocation_page_tableJO arI s ar σ J hni hG.delParts.archRef lbl lbl.bv hlM hlU hlO length buf ct hct argsU hlen
        hargs hth0 rfl hc hw hTy hqa hfr extra excaps (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
    have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageTable ptr mp asid va) := hw.okTab (by
      cases mp with
      | false => exact hw.1 rfl
      | true => exact Classical.byContradiction fun hn => hoff ⟨rfl, hn⟩)
    have hVC := (J.vsc.caps J.xtop.rel.2.1.2.2.1)
    exact (decode_invocation_page_tableJV arI s ar σ J hni hG.delParts.archRef hVC lbl lbl.bv hlM hlU hlO length
      buf ct hct argsU hlen hargs hth0 rfl hc hok extra excaps (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
  case PageDirectory ptr mp asid va =>
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0 hLb
    obtain ⟨hlM, hlU, hlO⟩ := pd_label lbl
    have hw : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageDirectory ptr mp asid va) := by
      have h := J.vsc _ hAs.isSlot; rwa [capV_of_capAt hc] at h
    by_cases hoff : mp = true ∧ ptr ∉ Z.L2
    · obtain ⟨rfl, hnL⟩ := hoff
      have ht := hE.vsTyp _ hAs.isSlot
      rw [capV_of_capAt hc] at ht
      obtain ⟨hTy, hqa, hfr⟩ := ht hnL
      exact (decode_invocation_page_directoryJO arI s ar σ J hni hG.delParts.archRef lbl lbl.bv hlM hlU hlO length buf ct hct argsU hlen
        hargs hth0 rfl hc hw hTy hqa hfr extra excaps (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
    have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageDirectory ptr mp asid va) := hw.okTab (by
      cases mp with
      | false => exact hw.1 rfl
      | true => exact Classical.byContradiction fun hn => hoff ⟨rfl, hn⟩)
    have hVC := (J.vsc.caps J.xtop.rel.2.1.2.2.1)
    exact (decode_invocation_page_directoryJV arI s ar σ J hni hG.delParts.archRef hVC lbl lbl.bv hlM hlU hlO
      length buf ct hct argsU hlen hargs hth0 rfl hc hok extra excaps (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
  case Pdpt ptr mp asid va =>
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0 hLb
    obtain ⟨hlM, hlU, hlO⟩ := pdpt_label lbl
    have hw : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.Pdpt ptr mp asid va) := by
      have h := J.vsc _ hAs.isSlot; rwa [capV_of_capAt hc] at h
    by_cases hoff : mp = true ∧ ptr ∉ Z.L3
    · obtain ⟨rfl, hnL⟩ := hoff
      have ht := hE.vsTyp _ hAs.isSlot
      rw [capV_of_capAt hc] at ht
      obtain ⟨hTy, hqa, hfr⟩ := ht hnL
      exact (decode_invocation_pdptJO arI s ar σ J hni hG.delParts.archRef lbl lbl.bv hlM hlU hlO length buf ct hct argsU hlen
        hargs hth0 rfl hc hw hTy hqa hfr extra excaps (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
    have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.Pdpt ptr mp asid va) := hw.okTab (by
      cases mp with
      | false => exact hw.1 rfl
      | true => exact Classical.byContradiction fun hn => hoff ⟨rfl, hn⟩)
    have hVC := (J.vsc.caps J.xtop.rel.2.1.2.2.1)
    exact (decode_invocation_pdptJV arI s ar σ J hni hG.delParts.archRef hVC lbl lbl.bv hlM hlU hlO length buf ct
      hct argsU hlen hargs hth0 rfl hc hok extra excaps (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
  case Pml4 p mp asid =>
    have hok := (J.vsc.caps J.xtop.rel.2.1.2.2.1).atOK J.xtop.rel.2.1.2.2.1 hAs.isSlot hc (by simp) (by simp)
    subst hLb
    exact (decode_invocation_pml4JV arI s ar σ J hni hG.delParts.archRef hG.tot lbl lbl.bv (pml4_label lbl) ct hct p asid mp
      (fun h => (hok.2.2 h).1) length
      (cslotAddr sl) buf blk call don fp extra _ ci sl excaps buffer).toPN arI (specDec_noPreK (by trivial))
  case AsidPool ptr base =>
    have hN : JPoolPath (L := L) AR Z s ar σ lbl length (.AsidPool ptr base) blk call don fp buf extra slbl argsU ci
      sl excaps buffer ct := hN
    subst hLb
    exact (decode_invocation_asid_poolJV arI s ar σ J hni (J.vsc.caps J.xtop.rel.2.1.2.2.1) lbl lbl.bv
      (pool_label lbl) length buf ct hct ptr base extra excaps hN.native (ExtraOK.poolExtra hPl hXO) (cslotAddr sl) blk call don fp _ ci sl buffer
      hAs.isSlot hc).toPN arI (specDec_noPreK (by trivial))
  case Frame p sz rt d m ep asid va =>
    obtain ⟨hV, hF⟩ := hN
    cases ep
    · by_cases hEP : lbl = fl4_abi.label.X86PageMapEPT
      · exact XCapP.reXP arI (hV (Or.inr hEP)) (specDec_noPreK (by trivial))
      have hF := hF rfl
      have hVC := (J.vsc.caps J.xtop.rel.2.1.2.2.1)
      obtain ⟨sl1, idxs⟩ := sl
      obtain ⟨p0, hp0, hth0⟩ := hsl
      try simp only at hp0 hth0
      subst hp0
      subst hLb
      exact (decode_invocation_frameJS arI s ar σ J hni hG.delParts.archRef hVC lbl lbl.bv (frame_label lbl hEP)
        (getAddress_label lbl).2 length buf ct hct argsU hlen hargs hth0 rfl hc hF.hno extra excaps
        (ExtraOK.vsExtra hPl hXO) blk call don fp ci buffer).toPN arI (specDec_noPreK (by trivial))
    · exact XCapP.reXP arI (hV (Or.inl rfl)) (specDec_noPreK (by trivial))
  case AsidControl =>
    have hN : JAsidCPath (L := L) AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer
      ct := hN
    subst hLb
    exact (decode_invocation_asid_controlJD arI s ar σ J hni hN.heapH.1 hN.heapH.2
      lbl lbl.bv (makePool_label lbl) length buf ct hct hN.vsReach argsU hlen hargs extra excaps
      (ExtraOK.mpExtra hPl hXO) (cslotAddr sl) blk call don fp ci sl buffer).toPN arI (specDec_noPreK (by trivial))
  case Untyped p sb fi dev =>
    exact hPD hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc (fun h => h)
      excaps buffer hXO hXN hLb hA5 hN
  all_goals exact XCapP.reXP arI hN (specDec_noPreK (by trivial))

set_option maxHeartbeats 4000000 in
/-- **One invocation at `J` under `MachPlat`** (module docstring):
`handle_invocation_entryJ` with `JEntryGlobM` and `JPreDecHyp`, `JAtPreMV` after
a preempted invocation. -/
theorem handle_invocation_entryJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct is_call blocking can_donate first_phase cptr)
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hNs : NativeScope σ) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) true σ is_call blocking can_donate
        first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  refine handle_invocation_refinesMXP arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) true s ar σ Z.th Z.G
    hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨Z, H, Cs, Ac, Lst, D, J⟩ ct hct hcur htcb
    is_call blocking can_donate first_phase cptr info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    ((J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf
      hbuffer hr2 her).imp id fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ =>
      J.faultHypJZ hG.tot hE.ni hct hE.ctnq hE.vfh hcf⟩)
    (argsU.map UScalar.bv) hmrs
    (fun _ lf lf' hl => J.faultHypJZ hG.tot hE.ni hct hE.ctnq hE.vfh
      (capFaultCorr_lookup cptr hl))
    (fun s1 a1 σ' _ ⟨_, _, _, _, _, _, J'⟩ hc => J'.flTailJ hc is_call)
    (fun a1 e e' ⟨_, _, _, _, _, _, J''⟩ he =>
      (J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJ hcur
        is_call e e' he)
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
  exact decOK_JM arI s ar σ J hG hE ct hct info.label (msgLen info buf) blocking is_call can_donate first_phase
    buf e mi.miLabel argsU hLen hArgs hbuf hl (Fl4Spec.toBl cptr.bv) sl hsl c hc exs buffer
    (hXO e exs h1 h2) hXN hLb hA5 (hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs hsl hc hget h1 h2)
    hPD hR hVT hVI hNs

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
theorem invoke_afterJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (call bl don : Bool)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hNs : NativeScope σ)
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call bl don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
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
  refine WP.spec_bind (handle_invocation_entryJM arI s ar σ J ct hct call bl don false _ hG hE hP hPD hR hVT hVI hNs) ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
  rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
  · show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    refine hok ?_
    exact ⟨y, top y hy, Or.inl ⟨hy1, hrel, ifP_X (fun h => by cases h) hX⟩⟩
  · rw [if_pos rfl] at hX
    refine WP.spec_bind (hPre s1 a1 y.2 hrel hX) ?_
    rintro ⟨b, s2, a2⟩ hQ
    refine hok ?_
    exact ⟨y, top y hy, Or.inr ⟨hy1, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_invokeJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hNs : NativeScope σ)
    (Q : Fl4Spec.State Unit → S × A → Prop)
    (hPre : ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => Q σ1 (r.2.1, r.2.2) ⦄) :
    syscall.dispatch_syscall st arI s ar number ⦃ r => DispPost (L := L) arI AR Q (DispInv call bl don) σ r ⦄ := by
  have h := invoke_afterJM arI s ar σ J ct hct call bl don hG hE hP hPD hR hVT hVI hNs Q hPre
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

set_option maxHeartbeats 4000000 in
theorem mid_invRecvJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool)
    (hrg : regIdx sr = rg)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct rg))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (DispMid sr cr) σ r ⦄ := by
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
  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJM arI s ar σ J ct hct false false true true _ hG hE hP
    hPD hR0 hVT hVI (hNS s ar σ ⟨Z, H, Cs, Ac, Lst, D, s, ar, σ, J.toHole⟩))
    fun res h => And.intro (h.toPreMV.mid arI (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) h) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM⟩ | ⟨hr1, hy1, hrel, hX⟩⟩, hMV⟩
  · dsimp only at hr1 hy1 hM
    subst hr1 hy1
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    show (if true = true then syscall.handle_recv st arI s1 a1 true cr else ok (s1, a1)) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_mono (hR _ hy rfl s1 a1 hM) ?_
    rintro r ⟨z, hz, hrl, hJ⟩
    exact ⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
      Or.inl ⟨rfl, hrl, hJ⟩⟩
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
    refine WP.spec_bind (hPre_ofZQIM hARI hA hnd hM hMK hPA hIA hmrt hNS hG.maxTU hG.tu s1 a1 σm' hrel' hX') ?_
    rintro ⟨b, s2, a2⟩ ⟨hb, hQ⟩
    dsimp only at hb; subst hb
    show (if false = true then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [if_neg (by decide)]
    exact hok ⟨_, mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_err hy'), Or.inr ⟨rfl, hQ⟩⟩

set_option maxHeartbeats 4000000 in
theorem dispatch_midJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (c : Fl4Spec.Syscall) (rg : U64)
    (sr : Fl4Spec.Register) (cr : Bool) (hn : MidSysR number c rg sr cr)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct false false true true (L.mem s (regA ct rg)))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ)
    (hR : JMidRecvHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) cr σ)
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have h := mid_invRecvJM s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hPD hR0 hVT hVI hARI hA hnd hM hMK hPA hIA hmrt hNS
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
theorem dispatch_invokeJAllM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ := by
  rw [fl4HandleSyscall_inv hn]
  exact dispatch_invokeJM arI s ar σ J ct hct number call bl don hn hG hE hP hPD hR hVT hVI
    (hNS s ar σ ⟨Z, H, Cs, Ac, Lst, D, s, ar, σ, J.toHole⟩) _
    fun s1 a1 σ1 h1 h2 => WP.spec_mono (hPre_ofZQIM hARI hA hnd hM hMK hPA hIA hmrt hNS hG.maxTU hG.tu s1 a1 σ1 h1 h2)
      fun _ h => h.2

variable (arI) in
/-- **The dispatch premises under `MachPlat`** (module docstring):
`KDispHyps15M` with `JEntryGlobM` for `JEntryGlob`, `JPreDecHyp` [W] beside
each invocation's path, and `ValidMachineTime` [J] at the dispatch state (l4v
`valid_machine_time`, kept by `check_budget_restart`). -/
structure KDispHyps13P (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JPreDecHyp (L := L) arI AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp6 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JPreDecHyp (L := L) arI AR MR Z H Cs D s a σ ct
  vmt : ValidMachineTime σ

set_option maxHeartbeats 4000000 in
/-- **Every native dispatch at `J` under `MachPlat`** (`dispatch_all9M` with
`KDispHyps13P`; the mid receive leaves narrowed as `KDispHyps15M.to14M` …
`to9M`). -/
theorem dispatch_all13P [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13P (L := L) arI AR MR Z H Cs D s a σ n c)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJAllM s a σ J _ hct n call bl don hi hG hE hP hPD hR hK.vmt hVI hARI hA hnd
      hM hMK hPA hIA hmrt hNS) fun _ h => h.toR
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hPA.minBudget a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJM s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD hR hK.vmt hVI hARI hA hnd hM hMK hPA hIA hmrt hNS

set_option maxHeartbeats 16000000 in
theorem kernel_entryJ13P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps13P (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hPF := kPreFinHypJI_of hFin hA hnd hmb hNS hNSR hT hmax htu
  have hvm := hvm_of_ns hNS
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hBud : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart)
          (faultIPSt σ σ.curThread x) = ({(true, σ')}, False) ∧
        σ'.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σ'.curThread = (faultIPSt σ σ.curThread x).curThread ∧
        σ'.curSc = (faultIPSt σ σ.curThread x).curSc ∧
        σ'.schedulerAction = (faultIPSt σ σ.curThread x).schedulerAction ∧
        σ'.idleThread = (faultIPSt σ σ.curThread x).idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget (faultIPSt σ σ.curThread x)).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
    rcases hBu.tmo with hnt | ⟨hnq, xt, hkt, hrr, p, bd, rr, hth, hper, hcb⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
          obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl, _, Ac', Lst', D', J'⟩
          unfold specBudget faultIPSt
          rw [he]; exact Set.mem_singleton _⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb)) fun r ⟨h1, h2⟩ =>
          ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩⟩
  refine WP.spec_bind (WP.spec_and hBud (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨hTr, hFa⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1 J'.toR
    exact WP.spec_mono (jat_finishJR s2 a1 σb J'.toR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR H Cs) hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    refine WP.spec_bind (dispatch_all13P s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hMRσb hVIσb hARI hA hnd hM hMK hPA hIA hmrt hNS hmax htu) ?_
    rintro ⟨s3, a2⟩ ⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2 JmR
      exact WP.spec_mono (jat_finishJR s3 a2 σm JmR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR Hm Csm) hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (hPF σ1 hPA (s3, a2) hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩


/-- **The platform premises of `kernel_entryJ13P` are satisfiable by a
platform that raises interrupts** (module docstring): the model platform
(`modelArch`, arch state = spec machine state, `modelMR`) satisfies
`MachPlat` and `MRKeep`, and its `take_pending_irq` reports the spec's line
whenever the spec has one (unlike `IrqPlat.take`/`PPPlat`, which only a
platform that never interrupts satisfies, and `PPPlat.now`, which none does). -/
theorem j13P_platform :
    MachPlat modelArch modelMR ∧ MRKeep modelArch modelMR ∧
      ∀ (ms : Fl4Spec.MachineState) (i : Fl4Spec.Irq), gaiLine true ms = some i →
        modelArch.take_pending_irq ms ⦃ r => r.1 ≠ syscall.NO_IRQ ∧ r.1.val = i.toNat ⦄ :=
  ⟨modelArch_machPlat, modelArch_mrKeep modelMR, fun _ _ h => modelArch_take_some h⟩

end

end

end Fl4Proofs.P3
