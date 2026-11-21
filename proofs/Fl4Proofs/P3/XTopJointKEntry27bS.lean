/-
P3 (DESIGN.md §9), invariant line G3 (INV-PLAN §4, KENTRY-PLAN g3c): **the spec
facts `kernel_entryJ27b` reads at the dispatch state and at the states where a
first-phase perform starts** (spec side only, outside the JAtZ cone).

The dispatch state σb of a syscall entry is reached from the entry state σ by the
`FaultIP` write (`fipSt σ x`: ct's TCB `x` with one register changed) and
`update_time_stamp` (a passing `check_budget_restart` changes nothing). The
first-phase invocation of ReplyRecv / NBSendRecv / NBSendWait then runs
`getMessageInfo`, the fault phase `midF'`, the decode phase `midE'` and
`set_thread_state ct Restart` (`MidAt`, the body of XTopJointMidRunS's
`MidPerfAt`) before its perform.

* `disp_uv` / `disp_node`: σb has σ's cap / CDT / object view `uV` and IRQ node
  (ut1's `UK`, ut7's `NK` families); `disp_vfc`: `VfhV ∧ CnDom` at σb (vfh3's
  family). So `UtInv''` (`SInv.utInv''_of_view`), `SpecGlobS.irq` and every other
  view-only fact of `SInvB σ` hold at σb.
* `epQAll_disp`: `EpQAll σ` gives `EpQAll σb` (JEntryAt.epQ): σb's heap is σ's with
  ct's registers changed (same SC binding and fault), the clock only advances
  (`ValidMachineTime`) so ready heads stay ready, and the scheduler action is σ's
  `resume_cur_thread` (Entered), so `ActReady σb` is vacuous.
* `vfh_mid`: the current thread's handler is valid after the first phase from σb
  (JMidVfhHyp; vfh3's `vfh_handleInvocationR`).
* `midAt_facts`: the first phase keeps `uV` and the node, and its decode result
  satisfies ut8's `InvOKV` at σb's view (`okv_fl4Decode`, with the slot facts of
  `okv_lookupCapAndSlot` / `okv_lookupExtraCaps`, as vfh3's shell).
* `irqSlot_of`: the IRQ node slots hold null or notification caps at such a state
  (JPerfIrqSlotHyp; `SpecGlobS.irq` on the unchanged view).
* `Out σ q`: `q` holds an object and is named by a cap (`capRng`) or lies outside
  every cap's range (`covR`). `out_ct` (l4v `if_live_then_nonz_cap` for the active
  current thread: `IfLiveT`), `out_bound` (a TCB-bound SC: `ScBack` + sl's typed
  `ScLiveT`, or the idle thread / idle SC: `IdleOutV` / `IdleScOutV`).
  `out_not_delR`: an `Out` object misses a childless untyped's region (vfh3's
  `vfh_noRef`). `out_ut`: it misses the region an Untyped retype touches
  (`UtSet`: the reset region of the source cap if `reset`, the new objects'
  addresses; the latter are fresh by UtFree, or inside the reset region).
  `out_mp`: it misses MakePool's region (`MpSet`). These give JPerfRegHyp.
-/
import Fl4Proofs.P3.SpecInvAllB
import Fl4Proofs.P3.SpecInvEqA
import Fl4Proofs.P3.SpecInvRdD

open Classical

namespace Fl4Proofs.P3.SInvK
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The dispatch state -/

/-- The state after the `FaultIP` write (XTopJointKEntry's `faultIPSt σ σ.curThread x`,
the same body). -/
abbrev fipSt (σ : State Unit) (x : Tcb) : State Unit :=
  Notif.updK σ σ.curThread (.tcb (Notif.setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))

section
variable {σ σ0 σb : State Unit}

theorem disp_uv (h0 : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    (hu : ((), σb) ∈ (updateTimeStamp (Z := Unit) σ0).1) : SInvU.uV σb = SInvU.uV σ :=
  SInvU.uk_updateTimeStamp σ0 (SInvU.uk_fl4SyscallFaultIP σ.curThread σ rfl _ h0) _ hu

theorem disp_node (h0 : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    (hu : ((), σb) ∈ (updateTimeStamp (Z := Unit) σ0).1) : σb.interruptIrqNode = σ.interruptIrqNode :=
  SInvU.nk_updateTimeStamp (N := σ.interruptIrqNode) σ0
    (SInvU.nk_fl4SyscallFaultIP (N := σ.interruptIrqNode) σ.curThread σ
      (show SInvU.NodeIs σ.interruptIrqNode σ from rfl) _ h0) _ hu

theorem disp_vfc (h0 : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    (hu : ((), σb) ∈ (updateTimeStamp (Z := Unit) σ0).1) (hV : SInv.VfhAll σ) (hC : SInv.CnDom σ) :
    SInv.VfC σb := by
  have h1 : SInv.VfC σ0 :=
    (by vfc_auto : SInv.IK SInv.VfC (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ
      ⟨(SInv.vfhV_iff σ).2 hV, hC⟩ _ h0
  exact (by vfc_auto : SInv.IK SInv.VfC (updateTimeStamp (Z := Unit))) σ0 h1 _ hu

end

/-! ## `EpQAll` at the dispatch state -/

set_option maxHeartbeats 2000000 in
/-- **`EpQAll` at the dispatch state** (module docstring). -/
theorem epQAll_disp {σ σb : State Unit} (hS : SInvAll.SInvB σ) (ha : σ.schedulerAction = .resumeCurThread)
    {x : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x))
    (hu : ((), σb) ∈ (updateTimeStamp (Z := Unit) (fipSt σ x)).1) (hE : SInvE.EpQAll σ) :
    SInvE.EpQAll σb := by
  obtain ⟨ek, -, et, -⟩ := SInvO.uts_off hu
  obtain ⟨-, ea, -, -⟩ := SInvR.qa_updateTimeStamp (fipSt σ x).readyQueues (fipSt σ x).schedulerAction
    (fipSt σ x).releaseQueue (fipSt σ x).idleSc (fipSt σ x) ⟨rfl, rfl, rfl, rfl⟩ _ hu
  have ht : σ.curTime.toNat ≤ σb.curTime.toNat := by
    have hv := hS.1.1.vmt
    have a1 : σ.curTime.toNat ≤ σ.machineState.lastMachineTime.toNat := BitVec.le_def.mp hv.1
    have a2 : σ.machineState.lastMachineTime.toNat ≤ SInvV.gctN σ.machineState := by
      unfold SInvV.gctN; exact le_min hv.2 (Nat.le_add_right _ _)
    rw [et, SInvV.gctN_toNat]
    exact Nat.le_trans a1 a2
  have hkn : ∀ p, p ≠ σ.curThread → σb.kheap p = σ.kheap p := fun p hp => by
    rw [ek]; exact Function.update_of_ne hp _ _
  have hkc : σb.kheap σ.curThread =
      some (.tcb (Notif.setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2))) := by
    rw [ek]; exact Function.update_self _ _ _
  have hsc : ∀ c y k, σ.kheap c = some (.schedContext y k) → σb.kheap c = some (.schedContext y k) := by
    intro c y k h
    have hc : c ≠ σ.curThread := by rintro rfl; rw [hk] at h; cases h
    rw [hkn c hc]; exact h
  have hok : ∀ z, Sched.ScOK σ z → Sched.ScOK σb z := by
    intro z h c hc
    obtain ⟨y, k, hy, h1, h2, h3⟩ := h c hc
    exact ⟨y, k, hsc c y k hy, h1,
      fun hA => ⟨SInvR.ready_of_nat (Nat.le_trans (SInvR.nat_of_ready (h2 hA).1) ht), (h2 hA).2⟩, h3⟩
  have hT : ∀ u xu, σb.kheap u = some (.tcb xu) → ∃ x0, σ.kheap u = some (.tcb x0) ∧
      xu.tcbSchedContext = x0.tcbSchedContext ∧ xu.tcbFault = x0.tcbFault := by
    intro u xu h
    by_cases hu : u = σ.curThread
    · subst hu; rw [hkc] at h; cases h; exact ⟨x, hk, rfl, rfl⟩
    · rw [hkn u hu] at h; exact ⟨xu, h, rfl, rfl⟩
  have hT' : ∀ u x0, σ.kheap u = some (.tcb x0) → ∃ xu, σb.kheap u = some (.tcb xu) ∧
      xu.tcbSchedContext = x0.tcbSchedContext ∧ xu.tcbFault = x0.tcbFault := by
    intro u x0 h
    by_cases hu : u = σ.curThread
    · subst hu; rw [hk] at h; cases h; exact ⟨_, hkc, rfl, rfl⟩
    · rw [← hkn u hu] at h; exact ⟨x0, h, rfl, rfl⟩
  intro e y hy
  have he : e ≠ σ.curThread := by rintro rfl; rw [hkc] at hy; cases hy
  rw [hkn e he] at hy
  obtain ⟨hm, hb, -⟩ := hE e y hy
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · obtain ⟨x0, hx0, hc0⟩ := hm u hu
    obtain ⟨xu, hxu, hs, hf⟩ := hT' u x0 hx0
    refine ⟨xu, hxu, fun hn => ?_⟩
    rw [hf] at hn
    have h1 := hok x0 (hc0 hn)
    intro c hc
    rw [hs] at hc
    exact h1 c hc
  · intro u xu c h1 h2
    obtain ⟨x0, hx0, hs, -⟩ := hT u xu h1
    rw [hs] at h2
    obtain ⟨y', k', hy', h3, h4⟩ := hb u x0 c hx0 h2
    exact ⟨y', k', hsc c y' k' hy', h3, h4⟩
  · intro t htt
    have e1 : σb.schedulerAction = σ.schedulerAction := ea
    rw [e1, ha] at htt
    cases htt

/-! ## The first phase -/

/-- **[J] JMidVfhHyp's body at the dispatch state** (module docstring). -/
theorem vfh_mid {σ σ0 σb : State Unit} (hS : SInvAll.SInvB σ)
    (h0 : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    (hu : ((), σb) ∈ (updateTimeStamp (Z := Unit) σ0).1) (cptr : CapRef) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σb).1, y.1 = .ok () →
      ∀ x, y.2.kheap y.2.curThread = some (.tcb x) → validFaultHandler x.tcbFaultHandler := by
  intro y hy _ x hx
  have hU : SInvU.UtInv'' σb := SInv.utInv''_of_view (disp_uv h0 hu) hS.1.1.ut.1
  have h := SInv.vfh_handleInvocationR true false false true true cptr σb
    (disp_vfc h0 hu hS.1.1.vfh hS.1.1.cnDom) hU y hy
  exact (SInv.vfhV_iff _).1 h.1 _ x hx

/-- The fault phase of the first-phase invocation (XTopJointMidRunS's `midF`, the
same body). -/
def midF' (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- The first-phase decode phase (XTopJointMidRunS's `midE`, the same body). -/
def midE' (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4Invocation :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs thread buffer info
    fl4DecodeInvocation true info.miLabel args cptr slot cap extracaps buffer

/-- **Where the first-phase perform of `inv` starts** (XTopJointMidRunS's
`MidPerfAt`, the same body). -/
def MidAt (cptr : CapRef) (σ : State Unit) (inv : Fl4Invocation) (σ1 : State Unit) : Prop :=
  ∃ info σa a σb σc, (info, σa) ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1 ∧
    ((.ok a, σb) : Except Fault _ × State Unit) ∈ ((midF' σ.curThread info cptr).run σa).1 ∧
    ((.ok inv, σc) : Except SyscallError _ × State Unit) ∈ ((midE' σ.curThread info cptr a).run σb).1 ∧
    ((), σ1) ∈ (setThreadState (Z := Unit) σ.curThread .restart σc).1

set_option maxHeartbeats 4000000 in
/-- **The first phase keeps the view and the node; its decode result is `InvOKV`**
(module docstring). -/
theorem midAt_facts {cptr : CapRef} {σ σ1 : State Unit} {inv : Fl4Invocation} (hA : MidAt cptr σ inv σ1) :
    SInvU.uV σ1 = SInvU.uV σ ∧ σ1.interruptIrqNode = σ.interruptIrqNode ∧ SInvU.InvOKV (SInvU.uV σ) inv := by
  obtain ⟨info, σa, a, σb, σc, hia, hb, hc, h1⟩ := hA
  have ua : SInvU.uV σa = SInvU.uV σ := SInvU.uk_getMessageInfo _ σ rfl _ hia
  have na : σa.interruptIrqNode = σ.interruptIrqNode :=
    SInvU.nk_getMessageInfo (N := σ.interruptIrqNode) _ σ (show SInvU.NodeIs _ σ from rfl) _ hia
  have hFu : ∀ v, SInvU.UKE v (midF' σ.curThread info cptr) := fun _ => by unfold midF'; uk_auto
  have hFn : ∀ N, SInvU.NKE N (midF' σ.curThread info cptr) := fun _ => by unfold midF'; nk_auto
  have ub : SInvU.uV σb = SInvU.uV σa := hFu _ σa rfl _ hb
  have nb : σb.interruptIrqNode = σa.interruptIrqNode :=
    hFn σa.interruptIrqNode σa (show SInvU.NodeIs _ σa from rfl) _ hb
  have hOk : SInvU.OkV (SInvU.uV σa) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (SInvU.uV σa).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (SInvU.uV σa).2.1 p.2 = some p.1)
      (midF' σ.curThread info cptr) := by
    unfold midF'
    refine SInvU.okv_bind (fun _ => SInvU.uk_capFaultOnFailure _ _ _ (SInvU.uk_lookupCapAndSlot _ _))
      (SInvU.okv_capFaultOnFailure _ _ (SInvU.okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine SInvU.okv_bind_uk (fun _ => SInv.ike_liftE (SInvU.uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine SInvU.okv_bind (fun _ => SInvU.uk_lookupExtraCaps _ _ _) (SInvU.okv_lookupExtraCaps _ _ _)
      fun ex hex => SInvU.okv_returnOk ?_
    exact ⟨hx, hex⟩
  obtain ⟨hcap, hex⟩ := hOk σa rfl a σb hb
  obtain ⟨sl, cap, ex, buf⟩ := a
  have hc' : ((.ok inv, σc) : Except SyscallError _ × State Unit) ∈ ((do
      let args ← NonDetE.liftE <| getMrs (Z := Unit) σ.curThread buf info
      fl4DecodeInvocation true info.miLabel args cptr sl cap ex buf).run σb).1 := hc
  have hEu : ∀ v, SInvU.UKE v (do
      let args ← NonDetE.liftE <| getMrs (Z := Unit) σ.curThread buf info
      fl4DecodeInvocation true info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
  have hEn : ∀ N, SInvU.NKE N (do
      let args ← NonDetE.liftE <| getMrs (Z := Unit) σ.curThread buf info
      fl4DecodeInvocation true info.miLabel args cptr sl cap ex buf) := fun _ => by nk_auto
  have uc : SInvU.uV σc = SInvU.uV σb := hEu _ σb rfl _ hc'
  have nc : σc.interruptIrqNode = σb.interruptIrqNode :=
    hEn σb.interruptIrqNode σb (show SInvU.NodeIs _ σb from rfl) _ hc'
  have hd : SInvU.InvOKV (SInvU.uV σa) inv :=
    SInvU.okv_bind_uk (P := SInvU.InvOKV (SInvU.uV σa)) (fun _ => SInv.ike_liftE (SInvU.uk_getMrs _ _ _))
      (fun args => SInvU.okv_fl4Decode true info.miLabel args cptr sl cap ex buf hcap hex) σb ub inv σc hc'
  have u1 : SInvU.uV σ1 = SInvU.uV σc := SInvU.uk_setThreadState _ _ σc rfl _ h1
  have n1 : σ1.interruptIrqNode = σc.interruptIrqNode :=
    SInvU.nk_setThreadState (N := σc.interruptIrqNode) _ _ σc (show SInvU.NodeIs _ σc from rfl) _ h1
  refine ⟨u1.trans (uc.trans (ub.trans ua)), n1.trans (nc.trans (nb.trans na)), ?_⟩
  rw [ua] at hd
  exact hd

/-- **[J] JPerfIrqSlotHyp's body at a state with σ's view and node** (module docstring). -/
theorem irqSlot_of {σ σ1 : State Unit} (hG : SInvG.SpecGlobS σ) (hv : SInvU.uV σ1 = SInvU.uV σ)
    (hn : σ1.interruptIrqNode = σ.interruptIrqNode) :
    ∀ irq c σ', (c, σ') ∈ (getCap (Z := Unit) (σ1.interruptIrqNode irq, []) σ1).1 →
      c = .nullCap ∨ ∃ r b rs, c = .notificationCap r b rs := by
  intro irq c σ' h
  have h2 : SInvU.capAt σ1 (σ1.interruptIrqNode irq, []) = some c := (SInvU.getCap_capAt h).2
  have hcap : SInvU.capAt σ1 = SInvU.capAt σ := congrArg (fun w : SInvU.UView => w.2.1) hv
  rw [hcap, hn] at h2
  exact hG.irq irq c h2

/-! ## The touched regions -/

/-- `q` holds an object, and is named by a cap or lies outside every cap's range. -/
def Out (σ : State Unit) (q : ObjRef) : Prop :=
  σ.kheap q ≠ none ∧ ((∃ s c, SInvU.capAt σ s = some c ∧ q ∈ SInvU.capRng c) ∨
    ∀ s c, SInvU.capAt σ s = some c → q ∉ SInvU.covR c)

/-- **The current thread** (l4v `if_live_then_nonz_cap`: it is active, so named). -/
theorem out_ct {σ : State Unit} (hS : SInvAll.SInvB σ) (hct : σ.curThread ≠ σ.idleThread) :
    Out σ σ.curThread := by
  obtain ⟨x, hx, ha⟩ := (hS.entryJ hct).ctAct
  refine ⟨(by rw [hx]; exact fun h => by cases h), Or.inl ?_⟩
  obtain ⟨s, c, hs, hr⟩ := SInv.ifLiveT_objRefs hS.1.1.live hx (SInv.live_of_active ha)
  exact ⟨s, c, hs, SInvU.objRefs_sub_capRng c hr⟩

/-- **An SC a TCB is bound to** (l4v `sym_refs` + `if_live_then_nonz_cap`, or the
idle SC / idle thread, outside every cap's range by `valid_global_refs`). -/
theorem out_bound {σ : State Unit} (hS : SInvAll.SInvB σ) {u p : ObjRef} {x : Tcb}
    (hu : σ.kheap u = some (.tcb x)) (hp : x.tcbSchedContext = some p) : Out σ p := by
  obtain ⟨y, k, hy, hyt, -⟩ := hS.1.1.scInv.back u x p hu hp
  refine ⟨(by rw [hy]; exact fun h => by cases h), ?_⟩
  by_cases h1 : p = σ.idleThread
  · right
    intro s c hs
    rw [h1]
    exact hS.1.1.idleOut (default : Irq) s c hs
  by_cases h2 : p = σ.idleSc
  · right
    intro s c hs
    rw [h2]
    exact hS.1.1.idleSc (default : Irq) s c hs
  left
  have hl : SInvL.liveO (.schedContext y k) := Or.inl (by rw [hyt]; exact Option.some_ne_none u)
  obtain ⟨s, c, hs, hn⟩ := hS.1.1.sl.1.1 p (.schedContext y k) hy hl h1 h2
  refine ⟨s, c, hs, SInvU.objRefs_sub_capRng c ?_⟩
  cases c <;> simp only [SInvL.NCap] at hn
  all_goals first | exact hn.elim | (subst hn; simp [objRefs])

/-- **An `Out` object misses a childless untyped's region** (vfh3's `vfh_noRef`). -/
theorem out_not_delR {σ : State Unit} (hU : SInvU.UtInv'' σ) {u : CslotPtr} {dev : Bool} {b : ObjRef}
    {n fi : Nat} (hu : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u)
    {q : ObjRef} (hq : Out σ q) : q ∉ SInvU.delR b n := by
  rcases hq.2 with ⟨s, c, hs, hr⟩ | h
  · exact SInv.vfh_noRef hU hu hk hs hr
  · exact h u _ hu

/-- The region an Untyped retype touches from `τ` (XTopJointPerfU's `utD`, the same
body). -/
def UtSet (τ : State Unit) (src : CslotPtr) (reset : Bool) (rb : ObjRef) (ty : ApiObjectType) (sz n : Nat) :
    Set ObjRef :=
  {x | (reset = true ∧ ∃ c, (c, τ) ∈ (getCap (Z := Unit) src τ).1 ∧ x ∈ SInvU.delR (objRefOf c) (Fl4Spec.bitsOf c)) ∨
    x ∈ SInvU.retPtrs rb n (fl4ObjBitsApi ty sz)}

set_option maxHeartbeats 2000000 in
/-- **An `Out` object misses an Untyped retype's region** (module docstring). -/
theorem out_ut {σ τ : State Unit} (hU : SInvU.UtInv'' σ) (hv : SInvU.uV τ = SInvU.uV σ)
    {src : CslotPtr} {reset : Bool} {base rb : ObjRef} {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr}
    {dev : Bool} (hok : SInvU.UtRetOKV (SInvU.uV σ) (.retype src reset base rb ty sz slots dev))
    {q : ObjRef} (hq : Out σ q) : q ∉ UtSet τ src reset rb ty sz slots.length := by
  have hok' : SInvU.UtRetOK σ (.retype src reset base rb ty sz slots dev) := SInvU.utRetOK_of_V hok
  obtain ⟨bits, fi, hc, -, -, -, -, hnk⟩ := hok'
  have hcap : SInvU.capAt τ = SInvU.capAt σ := congrArg (fun w : SInvU.UView => w.2.1) hv
  have hW : SInvU.UtWf σ := hU.1.1.2.1
  obtain ⟨hn, hfit⟩ := hW.fit hc
  have hD : reset = true → q ∉ SInvU.delR base bits := fun hr => out_not_delR hU hc (hnk hr) hq
  rintro (⟨hr, c, hgc, hx⟩ | hx)
  · have h2 : SInvU.capAt τ src = some c := (SInvU.getCap_capAt hgc).2
    rw [hcap, hc] at h2
    cases h2
    exact hD hr hx
  · cases reset
    · exact hq.1 (SInvU.utRet_fresh hU.1.1 (SInvU.utRetOK_of_V hok) q hx)
    · apply hD rfl
      rw [SInvU.mem_delR_iff hn hfit]
      by_contra hnq
      let τ' : State Unit := { σ with kheap := fun r => if r.toNat ∈ SInvU.utR base bits then none else σ.kheap r }
      have h3 := SInvU.utRet_fresh_reset (τ := τ') hW (SInvU.utRetOK_of_V hok) hc
        (fun r hr => by simp only [τ', if_pos hr]) q hx
      simp only [τ', if_neg hnq] at h3
      exact hq.1 h3

/-- The region MakePool touches (XTopJointPerfU's `asidD`, the same body). -/
def MpSet (frame : ObjRef) : Set ObjRef :=
  {x | x ∈ SInvU.delR frame page_bits ∨ x ∈ SInvU.retPtrs frame 1 (objBitsApi (.archObject .asidPoolObj) 0)}

/-- **An `Out` object misses MakePool's region** (`MpOKV`: a childless page-sized
untyped at `frame`). -/
theorem out_mp {σ : State Unit} (hU : SInvU.UtInv'' σ) {frame : ObjRef} {slot parent : CslotPtr} {base : Asid}
    (hok : SInvU.MpOKV (SInvU.uV σ) (.makePool frame slot parent base)) {q : ObjRef} (hq : Out σ q) :
    q ∉ MpSet frame := by
  obtain ⟨dev, fi, hc, hk⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hD := out_not_delR hU hc' hk hq
  rintro (hx | hx)
  · exact hD hx
  · obtain ⟨k, hk1, rfl⟩ := List.mem_map.1 hx
    have hk0 : k = 0 := by have := List.mem_range.1 hk1; omega
    subst hk0
    apply hD
    have hW : SInvU.UtWf σ := hU.1.1.2.1
    obtain ⟨hn, hfit⟩ := hW.fit hc'
    rw [SInvU.mem_delR_iff hn hfit]
    have e : ptrAdd frame (0 * 2 ^ objBitsApi (.archObject .asidPoolObj) 0) = frame := by
      unfold ptrAdd; simp
    rw [e]
    exact ⟨le_refl _, Nat.lt_add_of_pos_right (Nat.two_pow_pos _)⟩

end

end Fl4Proofs.P3.SInvK
