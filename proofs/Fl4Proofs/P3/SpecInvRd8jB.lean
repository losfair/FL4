/-
P3 (DESIGN.md §9), invariant line G1 (rd8j, KENTRY-PLAN rd8h handoff 2):
**`handle_invocation` keeps `Rdy`: the shell** (spec side only, outside the
JAtZ cone).

* **The shell carry `JS C I σ0 s := KZ σ0 s ∧ uV s = uV σ0 ∧ RB C I s`**:
  rd12b's `KZ` (rd8c's BK view, `cfS`, the action: so ct, Simple, `RdyT ct`,
  `OffReady`, `Suff` transport from σ0), ut's cap view (so slot 3 of a TCB and
  `IrqOutV` transport), rd8f's bundle `RB`. `js_of` builds it from the
  per-step families (rd / tq / sa / q4 / rb / nq / q1 / sb / gk / uk / isk /
  kz); `js_getMessageInfo`, `js_getCapReg`, `js_invF`, `js_invE`.
* **`rb_restart`**: the Restart write keeps `RB C I` (Restart is runnable, not
  BlockedOn*); `PFacts`: at the perform, `RB ct I ∧ RdyT ct ∧ OffReady ∧ Suff ∧
  NtfnQB` (`pfacts_restart`).
* `PerfRest σ iv`: the perform inputs no decode / carried fact gives here
  (Untyped and ASIDControl: goal item 4; Reply: rd8i's BlockedScActive;
  DomainSet: `SR`). **`perfOK_of`**: rd8h's `PerfOK` at the perform from
  `PerfRest`, rd8c's `bindRel_perform` (SC bind), `rdTi_perform` (TCB:
  BindRel for a new SC; the slot-3 `FhC` from `FhAll` at the shell's start
  through the cap view: `FhAll` from VfhAll by `fhAll_of_vfh`), `okv_fl4DecodeCfgD` (SchedControl).
* `rd_invPost` (the Restart check, kernel reply, Running write).
* **`rd_fl4HandleInvocationR`**: every outcome of `fl4HandleInvocationR` keeps
  `Rdy` from `RB ct I ∧ RdyT ct ∧ OffReady ∧ Suff ∧ FhAll` at its start and the
  pinned `PerfIn` (`PerfRest` at every Restart state the run reaches): fault
  branch by rd8h's `rd_hf`, error reply by rd's leaf, the perform by rd8h's
  `rd_fl4PerformInvocation`.
-/
import Fl4Proofs.P3.SpecInvRd8jA
import Fl4Proofs.P3.SpecInvRd8jK
import Fl4Proofs.P3.SpecInvVfhAll
open Classical

namespace Fl4Proofs.P3.SInvR.B8j
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The carry -/

/-- **The shell carry** (module docstring). -/
def JS (C I : ObjRef) (σ0 s : State Unit) : Prop :=
  A12b.KZ σ0 s ∧ SInvU.uV s = SInvU.uV σ0 ∧ B8f.RB C I s

variable {C I : ObjRef} {σ0 : State Unit}

theorem js_of {α : Type} {m : NonDet (State Unit) α} (hR : IK Rdy m) (hT : SInvQ.TQK m) (hA : SInvQ.SAK m)
    (h4 : SInvQ.Q4K m) (hB : SInvQ.RBK true m) (hN : NQK [C] m) (hQ : SInvQ.Q1K m) (hS : ∀ h0, SInvB.SBK h0 m)
    (hG : SInvV.GK m) (hU : ∀ v, SInvU.UK v m) (hI : SInvL.IsK I m) (hZ : ∀ V, A12b.KZK V m) :
    IK (JS C I σ0) m := by
  intro σ h y hy
  obtain ⟨hz, hu, hR0, ⟨hE, hct, hsi, hnq⟩, h1, hsc, hvm, hio, his⟩ := h
  have hz' : A12b.KZ σ y.2 := hZ σ σ rfl y hy
  have hu' : SInvU.uV y.2 = SInvU.uV σ := hU (SInvU.uV σ) σ rfl y hy
  refine ⟨A12b.kz_trans hz hz', hu'.trans hu, hR σ hR0 y hy,
    ⟨SInvQ.eb_of hT hA h4 hB σ hE y hy, (A12b.kz_curThread hz').trans hct,
      fun t => by rw [kz_act hz']; exact hsi t, hN σ hnq y hy⟩,
    hQ σ h1 y hy, SInvB.sik_of_sbk hS σ hsc y hy, hG _ SInvV.wl_vmt σ hvm y hy, ?_, hI σ his y hy⟩
  show SInvU.IrqOutV (fun _ => I) (SInvU.uV y.2)
  rw [hu']; exact hio

theorem js_getMessageInfo (t : ObjRef) : IK (JS C I σ0) (getMessageInfo (Z := Unit) t) :=
  js_of (rd_getMessageInfo t) (SInvQ.tq_getMessageInfo t) (SInvQ.sa_getMessageInfo t)
    (SInvQ.q4_getMessageInfo t) (SInvQ.rb_getMessageInfo t) (nq_getMessageInfo t) (SInvQ.q1_getMessageInfo t)
    (fun _ => SInvB.sb_getMessageInfo t) (SInvV.gk_of_mtk (MachT.mtk_getMessageInfo' t)) (fun _ => SInvU.uk_getMessageInfo t)
    (SInvL.isk_getMessageInfo t) (fun _ => A12b.kz_getMessageInfo t)

theorem js_getCapReg (r : Register) : IK (JS C I σ0) (getCapReg (Z := Unit) r) :=
  js_of (rd_getCapReg r) (SInvQ.tq_getCapReg r) (SInvQ.sa_getCapReg r) (SInvQ.q4_getCapReg r)
    (SInvQ.rb_getCapReg r) (nq_getCapReg r) (SInvQ.q1_getCapReg r) (fun _ => SInvB.sb_getCapReg r)
    (SInvV.gk_getCapReg r) (fun _ => SInvU.uk_getCapReg r) (SInvL.isk_getCapReg r) (fun _ => A12b.kz_getCapReg r)

/-- `A12b.invF` from its three leaves (no whnf of the shell). -/
theorem ike_invF {P : State Unit → Prop} (t : ObjRef) (cptr : CapRef) (info : MessageInfo)
    (h1 : IKE P (capFaultOnFailure (Z := Unit) (ofBl cptr) false (lookupCapAndSlot t cptr)))
    (h2 : IK P (lookupIpcBuffer (Z := Unit) false t)) (h3 : ∀ b, IKE P (lookupExtraCaps (Z := Unit) t b info)) :
    IKE P (A12b.invF t cptr info) := by
  unfold A12b.invF
  refine ike_bind h1 fun x => ?_
  obtain ⟨cap, slot⟩ := x
  (try dsimp only)
  exact ike_bind (ike_liftE h2) fun b => ike_bind (h3 b) fun _ => ike_returnOk _

/-- `A12b.invE` from `get_mrs` and the decode. -/
theorem ike_invE {P : State Unit → Prop} (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) (h1 : ∀ b, IK P (getMrs (Z := Unit) t b info))
    (h2 : ∀ args sl cap ex buf, IKE P (fl4DecodeInvocation (Z := Unit) fp info.miLabel args cptr sl cap ex buf)) :
    IKE P (A12b.invE fp cptr t info a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold A12b.invE
  (try dsimp only)
  exact ike_bind (ike_liftE (h1 buf)) fun args => h2 args sl cap ex buf

theorem rd_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : RdKE (A12b.invF t cptr info) :=
  ike_invF t cptr info (rd_capFaultOnFailure _ _ _ (rd_lookupCapAndSlot _ _)) (rd_lookupIpcBuffer _ _)
    (fun _ => rd_lookupExtraCaps _ _ _)

theorem rd_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : RdKE (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => rd_getMrs _ _ _) (fun _ _ _ _ _ => rd_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem tq_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvQ.TQKE (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvQ.tq_capFaultOnFailure _ _ _ (SInvQ.tq_lookupCapAndSlot _ _)) (SInvQ.tq_lookupIpcBuffer _ _)
    (fun _ => SInvQ.tq_lookupExtraCaps _ _ _)

theorem tq_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvQ.TQKE (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvQ.tq_getMrs _ _ _) (fun _ _ _ _ _ => SInvQ.tq_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem sa_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvQ.SAKE (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvQ.sa_capFaultOnFailure _ _ _ (SInvQ.sa_lookupCapAndSlot _ _)) (SInvQ.sa_lookupIpcBuffer _ _)
    (fun _ => SInvQ.sa_lookupExtraCaps _ _ _)

theorem sa_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvQ.SAKE (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvQ.sa_getMrs _ _ _) (fun _ _ _ _ _ => SInvQ.sa_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem q4_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvQ.Q4KE (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvQ.q4_capFaultOnFailure _ _ _ (SInvQ.q4_lookupCapAndSlot _ _)) (SInvQ.q4_lookupIpcBuffer _ _)
    (fun _ => SInvQ.q4_lookupExtraCaps _ _ _)

theorem q4_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvQ.Q4KE (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvQ.q4_getMrs _ _ _) (fun _ _ _ _ _ => SInvQ.q4_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem rb_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvQ.RBKE true (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvQ.rb_capFaultOnFailure _ _ _ (SInvQ.rb_lookupCapAndSlot _ _)) (SInvQ.rb_lookupIpcBuffer _ _)
    (fun _ => SInvQ.rb_lookupExtraCaps _ _ _)

theorem rb_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvQ.RBKE true (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvQ.rb_getMrs _ _ _) (fun _ _ _ _ _ => SInvQ.rb_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem nq_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : NQKE [C] (A12b.invF t cptr info) :=
  ike_invF t cptr info (nq_capFaultOnFailure _ _ _ (nq_lookupCapAndSlot _ _)) (nq_lookupIpcBuffer _ _)
    (fun _ => nq_lookupExtraCaps _ _ _)

theorem nq_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : NQKE [C] (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => nq_getMrs _ _ _) (fun _ _ _ _ _ => nq_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem q1_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvQ.Q1KE (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvQ.q1_capFaultOnFailure _ _ _ (SInvQ.q1_lookupCapAndSlot _ _)) (SInvQ.q1_lookupIpcBuffer _ _)
    (fun _ => SInvQ.q1_lookupExtraCaps _ _ _)

theorem q1_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvQ.Q1KE (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvQ.q1_getMrs _ _ _) (fun _ _ _ _ _ => SInvQ.q1_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem sb_invF (h0 : KHeap) (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvB.SBKE h0 (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvB.sb_capFaultOnFailure _ _ _ (SInvB.sb_lookupCapAndSlot _ _)) (SInvB.sb_lookupIpcBuffer _ _)
    (fun _ => SInvB.sb_lookupExtraCaps _ _ _)

theorem sb_invE (h0 : KHeap) (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvB.SBKE h0 (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvB.sb_getMrs _ _ _) (fun _ _ _ _ _ => SInvB.sb_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem uk_invF (v : SInvU.UView) (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvU.UKE v (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvU.uk_capFaultOnFailure _ _ _ (SInvU.uk_lookupCapAndSlot _ _)) (SInvU.uk_lookupIpcBuffer _ _)
    (fun _ => SInvU.uk_lookupExtraCaps _ _ _)

theorem uk_invE (v : SInvU.UView) (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvU.UKE v (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvU.uk_getMrs _ _ _) (fun _ _ _ _ _ => SInvU.uk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem isk_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvL.IsKE I (A12b.invF t cptr info) :=
  ike_invF t cptr info (SInvL.isk_capFaultOnFailure _ _ _ (SInvL.isk_lookupCapAndSlot _ _)) (SInvL.isk_lookupIpcBuffer _ _)
    (fun _ => SInvL.isk_lookupExtraCaps _ _ _)

theorem isk_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvL.IsKE I (A12b.invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => SInvL.isk_getMrs _ _ _) (fun _ _ _ _ _ => SInvL.isk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem gk_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : SInvV.GKE (A12b.invF t cptr info) := by
  intro P hP
  exact ike_invF t cptr info
    (SInvV.gk_of_mtk (MachT.mtke_capFaultOnFailure' _ _ (MachT.mtk_lookupCapAndSlot' _ _)) P hP)
    (SInvV.gk_of_mtk (MachT.mtk_lookupIpcBuffer' _ _) P hP) (fun b => SInvV.gk_of_mtk (MachT.mtk_lookupExtraCaps' _ b _) P hP)

theorem gk_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : SInvV.GKE (A12b.invE fp cptr t info a) := by
  intro P hP
  exact ike_invE fp cptr t info a (fun b => SInvV.gk_of_mtk (MachT.mtk_getMrs' _ b _) P hP)
    (fun _ _ _ _ _ => SInvV.gk_fl4DecodeInvocation _ _ _ _ _ _ _ _ P hP)

theorem js_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : IKE (JS C I σ0) (A12b.invF t cptr info) :=
  js_of (rd_invF t cptr info) (tq_invF t cptr info) (sa_invF t cptr info) (q4_invF t cptr info)
    (rb_invF t cptr info) (nq_invF t cptr info) (q1_invF t cptr info) (fun h0 => sb_invF h0 t cptr info)
    (gk_invF t cptr info) (fun v => uk_invF v t cptr info) (isk_invF t cptr info) (fun _ => A12b.kz_invF t cptr info)

theorem js_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : IKE (JS C I σ0) (A12b.invE fp cptr t info a) :=
  js_of (rd_invE fp cptr t info a) (tq_invE fp cptr t info a) (sa_invE fp cptr t info a)
    (q4_invE fp cptr t info a) (rb_invE fp cptr t info a) (nq_invE fp cptr t info a) (q1_invE fp cptr t info a)
    (fun h0 => sb_invE h0 fp cptr t info a) (gk_invE fp cptr t info a) (fun v => uk_invE v fp cptr t info a)
    (isk_invE fp cptr t info a) (fun _ => A12b.kz_invE fp cptr t info a)

/-! ## The Restart write and the perform-level facts -/

/-- **`set_thread_state C Restart` keeps `RB C I`.** -/
theorem rb_restart (s : State Unit) (h : B8f.RB C I s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) C .restart s).1) : B8f.RB C I u.2 := by
  obtain ⟨hR0, ⟨hE, hct, hsi, hnq⟩, h1, hsc, hvm, hio, his⟩ := h
  have hv : SInvU.uV u.2 = SInvU.uV s := SInvU.uk_setThreadState C .restart s rfl u hu
  refine ⟨rd_setThreadState C .restart trivial s hR0 u hu,
    ⟨SInvQ.eb_setThreadState_r (k := true) C .restart rfl s hE u hu, SInvQ.ct_setThreadState C C .restart s hct u hu,
      SInvQ.R18.sm_setThreadState C .restart s hsi u hu,
      nq_setThreadState C .restart (List.mem_singleton_self _) (fun h => h) s hnq u hu⟩,
    SInvQ.q1_setThreadState C .restart s h1 u hu,
    SInvB.sik_of_sbk (fun _ => SInvB.sb_setThreadState C .restart) s hsc u hu,
    SInvV.gk_of_mtk (MachT.mtk_setThreadState' C .restart) _ SInvV.wl_vmt s hvm u hu, ?_,
    SInvL.isk_setThreadState C .restart s his u hu⟩
  show SInvU.IrqOutV (fun _ => I) (SInvU.uV u.2)
  rw [hv]; exact hio

theorem offReady_svcf {s s' : State Unit} (hO : Sched.OffReady s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) :
    Sched.OffReady s' := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, -, -, -, e6⟩ := hc'
  intro y n hy
  rw [e2] at hy
  obtain ⟨y0, n0, hy0, er, -⟩ := (A8.cw_of_svs (c := s.curSc) hS).1 y n hy
  have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
  rw [e1, e6, hh]; exact hO y0 n0 hy0

theorem suff_svcf {s s' : State Unit} (hS0 : Suff s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : Suff s' := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, -, -, e5, -⟩ := hc'
  intro y n hy ha hne
  rw [e2] at hy hne
  rw [e5] at hne
  obtain ⟨y0, n0, hy0, er, em⟩ := (A8.cw_of_svs (c := s.curSc) hS).1 y n hy
  have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
  have ha0 : scActive y0 = true := by simp only [scActive, ← em]; exact ha
  rw [e1, hh]; exact hS0 y0 n0 hy0 ha0 hne

/-- The perform-level facts of rd8h's `rd_fl4PerformInvocation`. -/
def PFacts (I : ObjRef) (s : State Unit) : Prop :=
  B8f.RB s.curThread I s ∧ RdyT s s.curThread ∧ Sched.OffReady s ∧ Suff s ∧ SInv.NtfnQB s

/-- **The perform-level facts after the Restart write** from the shell carry. -/
theorem pfacts_restart {σ s : State Unit} (hRT : RdyT σ σ.curThread) (hO : Sched.OffReady σ) (hS : Suff σ)
    (hJ : JS σ.curThread I σ s) {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) σ.curThread .restart s).1) : PFacts I u.2 := by
  obtain ⟨hz, -, hRB⟩ := hJ
  have hv := SVK.sv_setThreadState' σ.curThread .restart s u hu
  have hc := cfk_setThreadState' σ.curThread .restart s u hu
  have hS1 : SVK.SVS σ u.2 := (svs_kz hz).trans hv
  have hc1 : cfS u.2 = cfS σ := hc.trans (kz_cfS hz)
  have ect : u.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc1
  have hRB' := rb_restart s hRB hu
  refine ⟨by rw [ect]; exact hRB', by rw [ect]; exact rdyT_svs hRT hS1, offReady_svcf hO hS1 hc1,
    suff_svcf hS hS1 hc1, hRB'.2.1.2.2.2.1.1⟩

/-! ## The fault-handler slot -/

/-- Slot 3 of every TCB holds a null or endpoint cap (from VfhAll). -/
def FhAll (σ : State Unit) : Prop :=
  ∀ t, (∃ x, σ.kheap t = some (.tcb x)) → ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c

theorem fhAll_of_vfh {σ : State Unit} (h : VfhAll σ) : FhAll σ := by
  intro t ⟨x, hx⟩ c hc
  rw [SInvB.capAt_fh hx] at hc
  cases hc
  exact SInvB.fhC_of_valid (h t x hx)

theorem fhAll_svu {s s' : State Unit} (hF : FhAll s) (hS : SVK.SVS s s') (hu : SInvU.uV s' = SInvU.uV s) :
    FhAll s' := by
  intro t ⟨x, hx⟩ c hc
  have e := hS.1 t
  rw [hx] at e
  obtain ⟨x0, hx0, -⟩ := SVK.sv_tcb (o := s.kheap t) e.symm
  have hcap : SInvU.capAt s' (t, tcbCnodeIndex 3) = SInvU.capAt s (t, tcbCnodeIndex 3) :=
    congrFun (congrArg (fun v : SInvU.UView => v.2.1) hu) _
  rw [hcap] at hc
  exact hF t ⟨x0, hx0⟩ c hc

theorem fhAll_js {σ0 s : State Unit} (hF : FhAll σ0) (hJ : JS C I σ0 s) : FhAll s :=
  fhAll_svu hF (svs_kz hJ.1) hJ.2.1

/-! ## The perform inputs -/

/-- **The perform inputs left** (pinned to the perform state): Untyped and
ASIDControl (goal item 4), Reply (rd8i's `BlockedScActive`), DomainSet (`SR`). -/
def PerfRest (σ : State Unit) : Fl4Invocation → Prop
  | .invokeUntyped i => ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) i).run σ).1, Rdy y.2
  | .invokeDomain (.invokeDomainSet t _) => SR t σ
  | .invokeReply _ _ => Sched.BlockedScActive σ
  | .invokeArchObject i => B8h.ArchOK σ i
  | _ => True

/-- **rd8h's `PerfOK` at the perform** (module docstring). -/
theorem perfOK_of {σ sd s' : State Unit} (hJd : JS σ.curThread I σ sd) (hF : FhAll σ)
    {fp : Bool} {label : Data} {args : List Data} {ci : CapRef} {sl : CslotPtr} {cap : Cap}
    {ex : List (Cap × CslotPtr)} {buf : Option ObjRef} {b : Fl4Invocation}
    (hdec : ((.ok b, s') : Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run sd).1)
    (hJ' : JS σ.curThread I σ s') {u : Unit × State Unit}
    (hu : u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1) (hR : PerfRest u.2 b) :
    B8h.PerfOK u.2 b := by
  have hN : SInvB.RNE sd := hJd.2.2.2.2.2.1.2
  cases b with
  | invokeUntyped i => exact hR
  | invokeTCB i =>
    have hT : RdTi u.2 i := rdTi_perform hN hdec σ.curThread hu
    cases i with
    | threadControlSched t sl' fh mcp prio sc =>
      refine ⟨fun hf c hc => ?_, tcbOK_bind_of hT⟩
      obtain ⟨xu, hxu⟩ := tcbOK_tcb_of hT hf
      have hF' : FhAll u.2 := fhAll_svu (fhAll_js hF hJ') (SVK.sv_setThreadState' σ.curThread .restart s' u hu)
        (SInvU.uk_setThreadState σ.curThread .restart s' rfl u hu)
      exact hF' t ⟨xu, hxu⟩ c hc
    | _ => trivial
  | invokeDomain d => cases d <;> first | exact hR | trivial
  | invokeReply r g => exact hR
  | invokeSchedContext i =>
    cases i with
    | invokeSchedContextBind p o =>
      cases o with
      | threadCap t => exact B8c.bindRel_perform hN hdec σ.curThread hu
      | _ => trivial
    | _ => trivial
  | invokeSchedControl i => exact B8c.okv_fl4DecodeCfgD fp label args ci sl cap ex buf sd rfl _ s' hdec
  | invokeArchObject i => exact hR
  | _ => trivial

/-! ## The post -/

theorem rd_invPost (calling : Bool) (t : ObjRef) (reply : List Data) (s : State Unit) (hR : Rdy s) :
    ∀ y ∈ (A12b.invPost calling t reply s).1, Rdy y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, -, rfl⟩ := SInvQ.q1_mem_threadGet (by unfold getThreadState at hw; exact hw)
  dsimp only at hy
  revert hy
  generalize x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have h1 : Rdy u.2 := by
      unfold NonDet.when at hu
      split at hu
      · exact rd_replyFromKernel _ _ s hR u hu
      · rw [Set.mem_singleton_iff.1 hu]; exact hR
    exact rd_setThreadState t .running trivial u.2 h1 y hy
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact hR)

/-! ## The shell -/

/-- **The perform inputs, pinned to the shell's run from σ**: `PerfRest` at
every Restart state reached through the lookups' and the decode's `ok`
outcomes. -/
def PerfIn (fp : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((A12b.invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((A12b.invE fp cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, PerfRest u.2 b

set_option maxHeartbeats 4000000 in
/-- **`handle_invocation` keeps `Rdy`** (module docstring). -/
theorem rd_fl4HandleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) (I : ObjRef)
    (σ : State Unit) (hRB : B8f.RB σ.curThread I σ) (hRT : RdyT σ σ.curThread) (hO : Sched.OffReady σ)
    (hS : Suff σ) (hF : FhAll σ) (hP : PerfIn fp cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, Rdy y.2 := by
  rw [A12b.fl4HandleInvocationR_eq]
  intro y hy
  obtain ⟨z, hz1, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz1; cases he
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz1
  obtain rfl := mem_gets hw
  simp only [Except.ok.injEq] at ha; subst ha
  obtain ⟨z, hz2, ⟨info, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  swap
  · unfold withoutPreemption at hz2; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz2; cases he
  unfold withoutPreemption at hz2
  obtain ⟨w0, hw0, rfl⟩ := ft_mem_liftE hz2
  simp only [Except.ok.injEq] at ha; subst ha
  have hJ0 : JS σ.curThread I σ σ := ⟨rfl, rfl, hRB⟩
  have hJw : JS σ.curThread I σ w0.2 := js_getMessageInfo _ σ hJ0 w0 hw0
  refine SInvQ.P17.syscall_r (I := JS σ.curThread I σ) (Q := fun y => Rdy y.2)
    (fun v hv => js_invF _ _ _ w0.2 hJw v hv) ?_ ?_ ?_ ?_ y hy
  · -- the fault branch
    intro f s hs v hv
    obtain ⟨hz, -, hR0, ⟨-, -, hsi, -⟩, h1, hsc, -⟩ := hs
    unfold NonDet.when at hv
    split at hv
    · exact B8h.rd_hf σ.curThread f s ⟨hR0, rdyT_svs hRT (svs_kz hz), h1, hsi, hsc⟩ v hv
    · rw [Set.mem_singleton_iff.1 hv]; exact hR0
  · -- the decode
    intro a s hs w hw
    exact js_invE _ _ _ _ a s (js_invF _ _ _ w0.2 hJw _ hs) w hw
  · -- the error reply
    intro e s hs v hv
    unfold NonDet.when at hv
    split at hv
    · exact rd_fl4ReplyFromKernelError _ _ _ s hs.2.2.1 v hv
    · rw [Set.mem_singleton_iff.1 hv]; exact hs.2.2.1
  · -- the finalise phase
    intro a s b s' has hbs hJ y hy
    have hJs : JS σ.curThread I σ s := js_invF _ _ _ w0.2 hJw _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    -- split get_mrs from the decode
    have hbs' := hbs
    unfold A12b.invE at hbs'
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e0, -, he0⟩⟩ := ft_mem_bindE hbs'
    swap
    · simp at he0
    obtain ⟨x0, hx0, e0⟩ := ft_mem_liftE hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hJd : JS σ.curThread I σ x0.2 := js_of (m := getMrs (Z := Unit) σ.curThread buf w0.1)
      (rd_getMrs _ _ _) (SInvQ.tq_getMrs _ _ _) (SInvQ.sa_getMrs _ _ _) (SInvQ.q4_getMrs _ _ _)
      (SInvQ.rb_getMrs _ _ _) (nq_getMrs _ _ _) (SInvQ.q1_getMrs _ _ _) (fun _ => SInvB.sb_getMrs _ _ _)
      (SInvV.gk_of_mtk (MachT.mtk_getMrs' _ _ _)) (fun _ => SInvU.uk_getMrs _ _ _) (SInvL.isk_getMrs _ _ _)
      (fun _ => A12b.kz_getMrs _ _ _) s hJs x0 hx0
    unfold A12b.invFin at hy
    obtain ⟨z, hz, ⟨u0, -, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
    swap
    · unfold withoutPreemption at hz; obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz; cases he
    unfold withoutPreemption at hz
    obtain ⟨u, hu, rfl⟩ := ft_mem_liftE hz
    have hPF := pfacts_restart hRT hO hS hJ hu
    have hOK : B8h.PerfOK u.2 b :=
      perfOK_of hJd hF hb0 hJ hu (hP w0 hw0 _ s b s' has hbs u hu)
    have hperf := B8h.rd_fl4PerformInvocation blocking calling don b I u.2 hPF.1 hPF.2.1 hPF.2.2.1
      hPF.2.2.2.1 hPF.2.2.2.2 hOK
    obtain ⟨z2, hz2, ⟨rp, -, hy⟩ | ⟨e2, -, rfl⟩⟩ := ft_mem_bindE hy
    · unfold withoutPreemption at hy
      obtain ⟨v, hv, rfl⟩ := ft_mem_liftE hy
      exact rd_invPost calling σ.curThread rp z2.2 (hperf z2 hz2) v hv
    · exact hperf z2 hz2

end

end Fl4Proofs.P3.SInvR.B8j
