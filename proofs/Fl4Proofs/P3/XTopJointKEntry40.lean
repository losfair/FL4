/-
P3 (DESIGN.md §9), invariant line G4 (g4j, KENTRY-PLAN g4j; g4h's handoff):
**`JDecMRL2` discharged: the Thread and Untyped caps' decodes with `MR` at the
chosen outcome.**

* Thread, the five installing labels: XTopJointMRTcbM's `…JMM` copies (the
  install loop's invariant `WMR MR WJL` carries `MR` to the outcome).
* Thread, the other non-VT-x labels: `XCapP.mrG` (`f := id`) on mr7's
  `decode_invocation_threadJ_stepMT`: FL4 by `MKD.decode_thread_nonins`
  (MachKeepG4j), spec by `perfF_tcbN` (the decode yields a TCB or FL4-TCB
  invocation that is not `NoPre.PreInv`, `dec_thread_kind` /
  `thread_noPre_of`; their performs keep `msFT`, `qInvT_perform`).
  `decode_invocation_threadJ_stepMMT`: every label but SetEPTRoot.
* `JDecMRLK K` (`JDecMRL2`'s shape for the caps / labels / arguments `K`
  names), `LoudT` (Untyped, Thread at SetEPTRoot), `jDecMRL2_ofT`:
  `JDecMRLK LoudT → JDecMRL2` at a dispatch state (the Thread case as
  `jPreDecHyp_of18U`, by `decode_invocation_threadJ_stepMMT`).
* Untyped (native object types): XTopJointUtMR's
  `decode_invocation_untypedJMM`, the no-reset runs by `jUtRetHypDMM_of`
  (FL4 `MKD.untyped_retype_nr`, spec `perf_ut_nr`); `jDecMRLK_ofU`:
  `JDecMRLK VtxK → JUtResetHyp → JDecMRLK LoudT`, where
  - **`VtxK`** [scope]: the VT-x decodes (a Thread cap at SetEPTRoot, an
    Untyped cap retyping types 14..18), the scope of XTopJointEntry's
    `JVtxScope` / KEntry20P's `JVtxHypM`, here with `MR` at the outcome;
  - **`JUtResetHyp`** [W]: the retype runs whose decode chose to reset the
    untyped first (`JUtResetMR`), at the dispatch state, at the decode's
    own values (l4v `invoke_untyped_corres` with `reset_untyped_cap`).
* Copies with `hDL : JDecMRLK VtxK ∧ JUtResetHyp` for `JDecMRL2`:
  `dispatch_all13PUNM3`, `kernel_entryJ13PUGMD3`, NEW TOPS
  **`kernel_entryJ40`** and **`kernel_entry_reachMD3`** (`kernel_entryJ39` /
  `kernel_entry_reachMD2` with that `hDL`; the old ones kept).
-/
import Fl4Proofs.P3.XTopJointKEntry39
import Fl4Proofs.P3.XTopJointMRTcbL
import Fl4Proofs.P3.XTopJointMRTcbM
import Fl4Proofs.P3.MachKeepG4j
import Fl4Proofs.P3.XTopJointUtMR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec side of the Thread cap's non-installing labels -/

section
open Fl4Spec

/-- A Thread cap decodes to a TCB or FL4-TCB invocation. -/
theorem dec_thread_kind (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (q : ObjRef)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    NoPre.OkP (fun inv => (∃ i, inv = .invokeTCB i) ∨ (∃ i, inv = .invokeFl4TCB i))
      (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl (.threadCap q) ex buf) := by
  simp only [fl4DecodeInvocation, fl4DecodeTcbInvocation, NonDetE.throwError]
  repeat' (first
    | exact NoPre.okP_throw
    | exact NoPre.okP_liftME fun x => Or.inl ⟨x, rfl⟩
    | exact NoPre.okP_liftME fun x => Or.inr ⟨x, rfl⟩
    | split)

theorem MachT.mkf_fl4FpuToFrameG4j (f : Word) : MachF.MKF (fl4FpuToFrame f) := by
  unfold fl4FpuToFrame
  refine MachF.mkf_bind (MachF.mkf_gets _) fun _ => MachF.mkf_bind ?_ fun _ => MachF.mkf_modify fun _ => rfl
  intro ms x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem MachT.mtk_fl4FpuToFrameG4j (f : Word) : MachT.MTK (doMachineOp (Z := Unit) (fl4FpuToFrame f)) :=
  MachT.mtk_doMachineOp (MachT.mkf_fl4FpuToFrameG4j f)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_fl4FpuToFrameG4j _)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_setMcpriorityG4j _ _)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_setPriorityG4j _ _)

theorem MachT.mtk_restartG4j (t : ObjRef) : MachT.MTK (Fl4Spec.restart (Z := Unit) t) := by
  unfold Fl4Spec.restart; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_restartG4j _)

theorem MachT.mtk_bindNotificationG4j (t n : ObjRef) : MachT.MTK (Fl4Spec.bindNotification (Z := Unit) t n) := by
  unfold Fl4Spec.bindNotification; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_bindNotificationG4j _ _)

theorem MachT.mtk_archPostSetFlagsG4j (t : ObjRef) (f : TcbFlags) :
    MachT.MTK (Fl4Spec.archPostSetFlags (Z := Unit) t f) := by
  unfold Fl4Spec.archPostSetFlags; (try split) <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_archPostSetFlagsG4j _ _)

theorem MachT.mtk_setFlagsG4j (t : ObjRef) (f : TcbFlags) : MachT.MTK (Fl4Spec.setFlags (Z := Unit) t f) := by
  unfold Fl4Spec.setFlags; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact MachT.mtk_setFlagsG4j _ _)

set_option maxHeartbeats 4000000 in
/-- **A TCB or FL4-TCB invocation that cannot be preempted keeps `msFT`**
(module docstring). -/
theorem qInvT_perform (b c d : Bool) (inv : Fl4Invocation)
    (hk : (∃ i, inv = .invokeTCB i) ∨ (∃ i, inv = .invokeFl4TCB i)) (hn : ¬ NoPre.PreInv inv) :
    MachT.MTKE (fl4PerformInvocation (Z := Unit) b c d inv) := by
  rcases hk with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · cases i with
    | threadControlCaps => exact (hn trivial).elim
    | threadControlSched t sl fh mcp pr sc =>
      cases fh with
      | some _ => exact (hn trivial).elim
      | none => simp only [fl4PerformInvocation, invokeTcb, installTcbCap]; mtk_auto
    | notificationControl t n => cases n <;> simp only [fl4PerformInvocation, invokeTcb] <;> mtk_auto
    | _ => simp only [fl4PerformInvocation, invokeTcb]; mtk_auto
  · cases i <;> simp only [fl4PerformInvocation, invokeFl4Tcb] <;> (try split) <;> mtk_auto

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`PerfF id` of the Thread cap at a label that installs no cap** (module
docstring). -/
theorem perfF_tcbN {slbl : Fl4Spec.Data} {lbl : U64} (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (hl : lbl.val ≠ 5 ∧ lbl.val ≠ 8 ∧ lbl.val ≠ 9 ∧ lbl.val ≠ 10 ∧ lbl.val ≠ 11) (σ : Fl4Spec.State Unit)
    (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (p : U64) :
    PerfF id σ blk call don (specDec fp slbl args ci sl (.Thread p) excaps buffer) := by
  intro inv hd σ1 hst y hy _
  have e1 := congrArg Prod.fst (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single hst))
  simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e1
  have hnp := thread_noPre_of (fp := fp) (args := args) (ci := ci) (sl := sl) (excaps := excaps) (buffer := buffer)
    (σ := σ) (p := p) hlbl hl inv hd
  have hk := dec_thread_kind fp slbl args ci sl p.bv excaps buffer σ _ hd.1 inv rfl
  have e2 := congrArg Prod.fst (qInvT_perform blk call don inv hk hnp σ1 y hy)
  simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e2
  simp only [id, MachF.mF, e2.1, e2.2.1, e2.2.2.1, e2.2.2.2.1, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1]

end

/-! ## The Thread cap at `JAtM` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAtM` after** (module docstring): the five installing
labels by XTopJointMRTcbM, every other non-VT-x label by `XCapP.mrG` on
`decode_invocation_threadJ_stepMT` (FL4 `MKD.decode_thread_nonins`, spec
`perfF_tcbN`); the stalls by `JAtZ.stallT` (no `hstall'`). -/
theorem decode_invocation_threadJ_stepMMT [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
  have hJ0M : JAtM (L := L) arI AR MR s ar σ := ⟨hJ0, hmv.1⟩
  have hX := decode_invocation_threadJ_stepMT arI s ar σ J hni hARI hT hFl hfnz lbl length p blk call don fp buf extra ct
    hct slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hNative hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc
    hnc0 hcapC hA5 hGb hFJ hmb hidS hbuf hl hJDP hsg hLv hnd hMP hKD hPA hmv hRd0 hnq hTA
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ Z.T := J.thT p hp
  -- WriteRegisters: the caller's buffer mapped (`lookup_buf_full`, `BufCover`), the arguments after its restart
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hctH : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ Z.T := J.thT ct hctH
  have hbm : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp := by
    intro hb0
    obtain ⟨x, hk, hwx⟩ := J.buf ct hctT
    have hL := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hctH hk (J.xferH.1) false
    rw [hbuf, WP.spec_ok] at hL
    cases hq : Endp.ipcBufOf false x with
    | none => exact absurd (hL.1.2 hq) hb0
    | some q => exact ⟨q, J.xferH.2.1 ct hctT x false q hk hq buf (hL.2 hwx q hq)⟩
  have hWR : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x := by
    intro s1 h1 i x hx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨sp, hsp⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
      by_cases hb : buf = 0#u64
      · exact ⟨0, fun h => absurd hb h⟩
      · obtain ⟨sp, h⟩ := hbm hb; exact ⟨sp, fun _ => h⟩
    rw [J.argsRestart (J.xferH.2.2) hctT hctH hsp (by omega) h1]
    exact hargs i x hx
  -- the cap installs' deletion at `J` (as `decode_invocation_cnodeJ_stepsL`)
  have hHp := tcbInsWM_wjl (L := L) (MR := MR) (Z := Z) (H := H) (Cs := Cs) arI hT hJDP.archRef hJDP.arKeep hJDP.vt
    hJDP.thr hnd hMP hKD hPA hARI.toMask
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hR : RestartWJ (st := st) Z s ar σ (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) :=
    fun _ hct s1 σ1 h1 h2 => ⟨WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2,
      mrv_keep hMP hmv (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single h2))⟩
  by_cases h9 : lbl = fl4_abi.label.TCBSetTimeoutEndpoint
  · subst h9
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_timeoutJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 excaps hXc _ blk don ci buffer)
  by_cases h11 : lbl = fl4_abi.label.TCBSetSpace
  · subst h11
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_spaceJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer)
  by_cases h10 : lbl = fl4_abi.label.TCBSetIPCBuffer
  · subst h10
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_ipcJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 excaps hXc hnc0 hfnz blk don ci buffer)
  by_cases h5 : lbl = fl4_abi.label.TCBConfigure
  · subst h5
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_configureJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (J.stallT p hpT) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc hfnz blk don ci buffer)
  -- the first extra cap's thread among the TCBs (as `decode_invocation_threadJAt`)
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  by_cases h8 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst h8
    exact xcapP_of_tcb arI s ar σ hJ0M _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_sched_paramsJMM arI s ar σ J hni hsg hP0 hHp hmv.1 (fun _ _ _ _ _ h => h.2.1) hMP hKD hR hT hARI.toARKeep hTA p hp slbl
        (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hpI (J.stallT p hpT) call sl hAs hsc extra
        x0 x1 x2 hx0 hx1 hx2 excaps hXc hcapT hcapC blk don ci buffer)
  have hv : ∀ {c : U64}, lbl ≠ c → lbl.val ≠ c.val := fun hn e => hn (UScalar.eq_of_val_eq e)
  have hl5 : lbl.val ≠ 5 ∧ lbl.val ≠ 8 ∧ lbl.val ≠ 9 ∧ lbl.val ≠ 10 ∧ lbl.val ≠ 11 :=
    ⟨by have := hv h5; simpa [fl4_abi.label.TCBConfigure] using this,
      by have := hv h8; simpa [fl4_abi.label.TCBSetSchedParams] using this,
      by have := hv h9; simpa [fl4_abi.label.TCBSetTimeoutEndpoint] using this,
      by have := hv h10; simpa [fl4_abi.label.TCBSetIPCBuffer] using this,
      by have := hv h11; simpa [fl4_abi.label.TCBSetSpace] using this⟩
  exact XCapP.mrG (f := id) hMP hX
    (WP.spec_mono (MKD.decode_thread_nonins L.total hT hKD ⟨hNative, h5, h8, h10, h11, h9⟩ hmv.1)
      fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σ blk call don fp (argsU.map UScalar.bv) ci sl excaps buffer p)


end

/-! ## `JDecMRL2` from the Thread cap's proof -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JDecMRL2` for the caps and labels `K` names** (`K c lbl argsU`). -/
def JDecMRLK (K : capability.Cap → U64 → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c → K c lbl argsU →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- `JDecMRLK` with the IRQ ack's `IrqAckU` (moved from IrqFixC in collapse A, Q). -/
def JDecMRLKQ (K : capability.Cap → U64 → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  JDecMRLK (L := L) arI K AR MR Z H Cs D s ar σ ct ∧ IrqAckU (L := L) arI MR Z s ar σ

/-- **The caps left after the Thread cap** (module docstring): a Thread cap
at SetEPTRoot (a VT-x label, [scope]) and every Untyped cap. -/
def LoudT : capability.Cap → U64 → List U64 → Prop
  | .Thread _, lbl, _ => lbl = fl4_abi.label.TCBSetEPTRoot
  | .Untyped .., _, _ => True
  | _, _, _ => False

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`JDecMRL2` with the Thread cap proved** (module docstring): the Thread
cap at every label but SetEPTRoot by `decode_invocation_threadJ_stepMMT`
(the front-end facts as `jPreDecHyp_of18U`), the rest by `JDecMRLK LoudT`. -/
theorem jDecMRL2_ofT [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hR3 : JDecMRLK (L := L) arI LoudT AR MR Z H Cs D s ar σ ct) :
    JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hcl excaps buffer
    hXO hXN hLb hA5 hN
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hPl : Placed Z.th := J.xtop.rel.1
  have hsc : capV (L.mem s) (cslotAddr sl) = c := capV_of_capAt hc
  have hni := hE.ni
  have hLv := hE.live
  cases c
  case Thread p =>
    obtain ⟨hEpt, hN⟩ := hN
    by_cases hn : lbl = fl4_abi.label.TCBSetEPTRoot
    · exact hR3 hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc
        hn excaps buffer hXO hXN hLb hA5 ⟨hEpt, hN⟩
    have hFr := (hN hn).hFr
    subst hLb
    obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon lbl
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    have hx0 := exAt_idx0 extra
    have hx1 := exAt_idx1 extra
    have hx2 := exAt_idx2 extra
    have hXc := ExtraOK.xc hPl hXO
    -- the untyped extra caps' children at their abstract names: CRel's
    -- `MdbLinks`/`CdtRel`/`MdbInv.parentAdj` (`noChildren_of_adj`)
    have hnc : NcHyp (st := st) Z.th s σ (exAt extra 0) (exAt extra 1) (exAt extra 2) := by
      obtain ⟨-, -, hM, hC, hI⟩ := J.dstate.1
      intro x _ sl0 hAs0 hx hu
      subst hx
      refine noChildren_of_adj Z.th hPl s σ Z.G hM hC (hI.parentAdj (th := Z.th)) sl0 hAs0
        ((hM.members _).2 ⟨hAs0.isSlot, capV (L.mem s) (cslotAddr sl0), capAt_capV _ _, ?_⟩)
      intro h0; rw [h0] at hu; simp [isUt] at hu
    have hnc0 : ∀ sl0 : Fl4Spec.CslotPtr, AbsSlot Z.th sl0 → exAt extra 0 = cslotAddr sl0 →
        isUt (capV (L.mem s) (exAt extra 0)) = true → NoChildrenRel (st := st) s σ (exAt extra 0) sl0 :=
      fun sl0 hA h hu => hnc _ (by simp) sl0 hA h hu
    have hcapC : exAt extra 1 ≠ 0#u64 → ∀ q b, capV (L.mem s) (exAt extra 1) = .SchedContext q b → q ∈ Z.C := by
      -- the slot `XcRel` names, a slot of a CNode of `Z.th` (`JAtZ.scCtxCap`)
      intro h1 q b hq
      obtain ⟨hz, he⟩ := hXc.2 1 _ rfl
      rcases hee : excaps[1]? with _ | e
      · exact absurd (hz.2 (List.getElem?_eq_none_iff.1 hee)) h1
      · obtain ⟨ex, -, ps, hps, hps1⟩ := he e hee
        have hAs1 : AbsSlot Z.th e.2 := ⟨ps, hps1, Or.inl hps⟩
        rw [ex] at hq
        exact (J.scCtxCap arI hAs1.isSlot (by rw [capAt_capV, hq])).1
    have hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
        q ≠ L.idleW s := by
      -- no cap but a frame cap names the idle thread (`SpecGlob.idle`)
      intro sl' q hAs' hsc' e
      obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.dstate.1.1.abs_cap hAs'
      rw [capAt_capV, hsc'] at hc0; cases eq_of_ok_eq hc0
      rw [hca0.abs] at hg0
      have ha0 := (getCap_set_iff σ sl'.1 sl'.2 _).1 (congrArg Prod.fst hg0)
      apply hE.sg.idle sl'.1 sl'.2 _ ha0 (by simp [IsPageCap, absCap])
      rw [JAtZ.idleThread_eq arI J, ← e]; simp [absCap, Fl4Spec.objRefs]
    have hpI : p ≠ L.idleW s := hidS sl p hAs hsc
    exact decode_invocation_threadJ_stepMMT arI s ar σ J hni hG.ari hG.tot hE.flags hE.fnz lbl length p blk call don fp buf extra ct hct sl' hlbl argsU hlen hargs ci sl
      hAs hsc excaps buffer hext hn J.cwOut hpI _ _ _ hx0 hx1 hx2 hXc hnc hnc0 hcapC hA5 (getBpHyp_of s ct p)
      (fun h => hFr h _ hx0) hG.ppA.minBudget hidS hbuf hl hG.delParts hE.sg hLv hG.nd hM hKD hG.ppA ⟨hR, hVT, hVI⟩ hE.rd0 hE.ctnq hG.timeAg
  case Untyped p sb fi dev =>
    exact hR3 hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc trivial
      excaps buffer hXO hXN hLb hA5 hN
  all_goals exact (show False from hcl.1).elim

set_option maxHeartbeats 4000000 in
/-- `jDecMRL2_ofT` carrying `IrqAckU` (`JDecMRLKQ`; moved from IrqFixC in collapse A, Q). -/
theorem jDecMRL2_ofTQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hR3 : JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct) :
    JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct :=
  ⟨jDecMRL2_ofT arI s ar σ J hG hE ct hct hM hKD hR3.1, hR3.2⟩

end

/-! ## `JDecMRLK LoudT` from the Untyped cap's no-reset proof -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VT-x decodes** [scope] (module docstring): a Thread cap at
SetEPTRoot, an Untyped cap retyping a VT-x object type (14..18). -/
def VtxK : capability.Cap → U64 → List U64 → Prop
  | .Thread _, lbl, _ => lbl = fl4_abi.label.TCBSetEPTRoot
  | .Untyped .., _, argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _, _ => False

/-- **[W] The retypes with a reset, `MR` at the outcome, at the dispatch
state** (module docstring): `JDecMRLK`'s front-end facts for an Untyped cap
retyping a native type, concluding XTopJointUtMR's `JUtResetMR` (only the runs
whose decode chose to reset the untyped first). -/
def JUtResetHyp (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c →
    ∀ (p sb fi : U64) (dev : Bool), c = .Untyped p sb fi dev → (∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val) →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    JUtResetMR (L := L) arI AR MR Z.th s ar σ sl p sb fi dev ct blk call don argsU

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`JDecMRLK LoudT` from the scope premise and `JUtResetHyp`** (module
docstring): an Untyped cap retyping a native type by
`decode_invocation_untypedJMM` (the front-end facts as `jPreDecHyp_of14U`),
its no-reset runs by `jUtRetHypDMM_of`; the VT-x decodes by `hVx`. -/
theorem jDecMRLK_ofU [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hVx : JDecMRLK (L := L) arI VtxK AR MR Z H Cs D s ar σ ct)
    (hUR : JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRLK (L := L) arI LoudT AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hK excaps buffer
    hXO hXN hLb hA5 hN
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hPl : Placed Z.th := J.xtop.rel.1
  have hN0 := hN
  cases c
  case Thread p =>
    exact hVx hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc hK
      excaps buffer hXO hXN hLb hA5 hN
  case Untyped p sb fi dev =>
    by_cases hv : ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
    · exact hVx hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc hv
        excaps buffer hXO hXN hLb hA5 hN0
    have hNat : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val :=
      fun x hx => Classical.byContradiction fun hn => hv ⟨x, hx, by omega, by omega⟩
    obtain ⟨hDv, hU⟩ := hN
    have hex := ExtraOK.rel1 hPl hXO
    have hx0 := exAt_idx0 extra
    generalize exAt extra 0 = x0 at hex hx0
    cases dev
    · have hN := hU rfl
      exact decode_invocation_untypedJMM s ar σ J hR lbl slbl (by rw [← hLb]; exact genInvocationType_untyped_iff lbl)
        length buf ct hct argsU hlen hargs hNat sl hAs p sb fi hc extra x0 hx0 excaps hex hN.fan blk call don fp ci
        buffer (jUtRetHypDMM_of hM hKD hG.tot (J.jUtRetHypM hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0
          hG.ari.toARKeep hG.tot hG.nd hM hG.ppA hN.rcb hE.rd0 hE.ctnq hN.vsReach hE.urz hE.utks hR hVT hVI hNat)
          (hUR hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc p sb fi false rfl
            hNat excaps buffer hXO hXN hLb hA5 hN0) hR)
    · have hN := hDv rfl
      exact decode_invocation_untypedJMM s ar σ J hR lbl slbl (by rw [← hLb]; exact genInvocationType_untyped_iff lbl)
        length buf ct hct argsU hlen hargs hNat sl hAs p sb fi hc extra x0 hx0 excaps hex hN.fan blk call don fp ci
        buffer (jUtRetHypDMM_of hM hKD hG.tot (J.jUtRetHypDevM hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2
          hN.core0 hN.devApart hN.devFree hN.devGpm hN.rcb hN.vsReach)
          (hUR hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc p sb fi true rfl
            hNat excaps buffer hXO hXN hLb hA5 hN0) hR)
  all_goals exact (show False from hK).elim

set_option maxHeartbeats 4000000 in
/-- `jDecMRLK_ofU` carrying `IrqAckU` (`JDecMRLKQ`; moved from IrqFixC in collapse A, Q). -/
theorem jDecMRLK_ofUQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hVx : JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s ar σ ct)
    (hUR : JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct :=
  ⟨jDecMRLK_ofU arI s ar σ J hG hE ct hct hM hKD hVx.1 hUR, hVx.2⟩

end
/-! ## Every native dispatch with `MR` at the chosen outcome -/

/-! ## The tops -/

end


end Fl4Proofs.P3
