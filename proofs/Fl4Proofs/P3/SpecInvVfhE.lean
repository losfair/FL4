/-
P3 (DESIGN.md §9), invariant line G1 (vfh3): **`VfhAll ∧ CnDom` across the
kernel entries** (spec side only, outside the JAtZ cone; vfh2 handoff steps 3
and 4).

* `vfh_fl4Perform`: every perform keeps `VfC := VfhV ∧ CnDom` from the decode's
  facts at the decode state `σ0` (`VInv σ0`, SpecInvVfhX; the perform state has
  `σ0`'s caps, `hV σ = hV σ0`), ut3's `InvOKV` (`UtRetOK`, `MpOK`) and the
  carried `UtInv''` (retype and MakePool, SpecInvVfhR); every other perform by
  the frames and the writer leaves (`IK (VS σ0)`).
* The invocation shell (`vfh_handleInvocationR`, ut3's `uiD_handleInvocationR`
  with `VfC` in place of `UtInv'`): the lookups give the invoked cap in its slot
  and the extra caps in theirs (ut3's `okv_lookupCapAndSlot` /
  `okv_lookupExtraCaps` on the untyped view), every step before the perform
  keeps both views, so the decode's facts and `UtInv''` hold at the perform.
* `IKV m`: `VfC` kept from a state that also satisfies `UtInv''` (only the
  syscall's invocation reads it); the syscalls, the events (the budget check
  keeps the view whenever the syscall runs: ut3's `checkBudgetRestart_true`),
  `fl4CallKernel`, the syscall entry.
* **`kentry_vfhAll`**, **`kcall_vfhAll`** (`hU : UtInv3 σ`, a G1 field whose
  preservation is ut7's), `kcall_vfhAll_other` (non-syscall events, no `hU`).
-/
import Fl4Proofs.P3.SpecInvVfhR
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-- The single-state predicate the entry keeps. -/
abbrev VfC (σ : State Unit) : Prop := VfhV σ ∧ CnDom σ

theorem ik_vfc_of {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ0, IK (VS σ0) m) : IK VfC m :=
  fun σ hσ y hy => (h σ σ (VS.refl hσ) y hy).cur

theorem ike_vfc_of {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ σ0, IKE (VS σ0) m) : IKE VfC m :=
  ik_vfc_of h

macro "vfc_auto" : tactic => `(tactic| first
  | exact ike_vfc_of fun _ => by hv_auto
  | exact ik_vfc_of fun _ => by hv_auto)

/-! ## Views -/

theorem vfh_Bad_view {σ σ0 : State Unit} (e : SInvV.hV σ = SInvV.hV σ0) {sl : CslotPtr} :
    vfh_Bad σ sl ↔ vfh_Bad σ0 sl := by
  unfold vfh_Bad; rw [SInvV.hV_cap e]

theorem dRef_view {σ σ0 : State Unit} (e : SInvV.hV σ = SInvV.hV σ0) {p : ObjRef} (h : DRef σ0 p) : DRef σ p := by
  obtain ⟨s, r, g, h⟩ := h
  exact ⟨s, r, g, by rw [SInvV.hV_cap e]; exact h⟩

theorem vUt_view {σ σ0 : State Unit} (e : SInvV.hV σ = SInvV.hV σ0) {ui : UntypedInvocation} (h : VUt σ0 ui) :
    VUt σ ui := by
  cases ui
  exact fun d hd => ⟨fun hb => (h d hd).1 ((vfh_Bad_view e).1 hb), dRef_view e (h d hd).2⟩

theorem vMp_view {σ σ0 : State Unit} (e : SInvV.hV σ = SInvV.hV σ0) {a : AsidControlInvocation} (h : VMp σ0 a) :
    VMp σ a := by
  cases a
  exact ⟨fun hb => h.1 ((vfh_Bad_view e).1 hb), dRef_view e h.2⟩

theorem utInv''_of_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hU : UtInv'' σ) : UtInv'' σ' := by
  show UtInv''V _; rw [h]; exact hU

/-! ## The performs -/

set_option maxHeartbeats 8000000 in
/-- **Every perform keeps `VfC`** from the decode's facts. -/
theorem vfh_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ0 σ : State Unit)
    (e : SInvV.hV σ = SInvV.hV σ0) (hv : VfhV σ) (hd : CnDom σ) (hU : UtInv'' σ) (hok : InvOKV (uV σ) inv)
    (hi : VInv σ0 inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, VfC y.2 := by
  have hS : VS σ0 σ := ⟨hv, domK_view e, hd⟩
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e'⟩ := mem_ret_bindE hy
    rw [e']
    exact vfh_fl4InvokeUntyped ui σ hv hd hU (utRetOK_of_V hok.1) (vUt_view e hi) z hz
  | invokeCNode i =>
    refine ((show IKE (VS σ0) (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) by
      simp only [fl4PerformInvocation]
      exact ike_bind (vs_invokeCnode i hi) fun _ => ike_returnOk _) σ hS y hy).cur
  | invokeTCB i =>
    refine ((show IKE (VS σ0) (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) by
      simp only [fl4PerformInvocation]
      exact vs_invokeTcb i hi) σ hS y hy).cur
  | invokeIRQControl i =>
    refine ((show IKE (VS σ0) (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQControl i)) by
      simp only [fl4PerformInvocation]
      exact ike_bind (vs_invokeFl4IrqControl i hi) fun _ => ike_returnOk _) σ hS y hy).cur
  | invokeIRQHandler i =>
    refine ((show IKE (VS σ0) (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQHandler i)) by
      simp only [fl4PerformInvocation]
      exact ike_bind (ike_liftE (vs_invokeIrqHandler i hi)) fun _ => ike_returnOk _) σ hS y hy).cur
  | invokeArchObject ai =>
    cases ai with
    | spec i =>
      cases i with
      | invokeASIDControl a =>
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
        obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
        obtain ⟨z, hz, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hx]
        exact vfh_makePool a σ hv hd hU (mpOK_of_V hok) (vMp_view e hi) z hz
      | invokePageTable i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (vs_performPageTableInvocation i' (fun c sl p q v e => by subst e; exact hi)
            (fun c sl e => by subst e; exact hi)) fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokePageDirectory i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (vs_performPageDirectoryInvocation i' (fun c sl p q v e => by subst e; exact hi)
            (fun c sl e => by subst e; exact hi)) fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokePDPT i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (vs_performPdptInvocation i' (fun c sl p q v e => by subst e; exact hi)
            (fun c sl e => by subst e; exact hi)) fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokePage i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          exact ike_liftE (vs_performPageInvocation i' (fun c sl e v h => by subst h; exact hi)
            (fun c sl h => by subst h; exact hi))) σ hS y hy).cur
      | invokeIOPortControl i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (vs_performIoportControlInvocation i' (fun f l d c h => by subst h; exact hi))
            fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokeASIDPool i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (vs_performAsidPoolInvocation i') fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokeIOPort i' =>
        refine ((show IKE (VS σ0) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          hv_auto) σ hS y hy).cur
    | deriveSubframe iv =>
      refine ((show IKE (VS σ0) _ by
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
        refine ike_liftE (ik_bind (vs_performDeriveSubframe iv hi) fun _ => ?_)
        hv_auto) σ hS y hy).cur
    | _ =>
      refine ((show IKE (VS σ0) _ by
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
        hv_auto) σ hS y hy).cur
  | _ =>
    refine ((show IKE (VS σ0) _ by simp only [fl4PerformInvocation]; hv_auto) σ hS y hy).cur

/-! ## The invocation shell -/

/-- `VfC` kept from a state that also satisfies `UtInv''`. -/
def IKV {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, VfC σ → UtInv'' σ → ∀ y ∈ (m σ).1, VfC y.2

abbrev IKVE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKV (ExceptT.run m)

theorem ikv_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IK VfC m) : IKV m :=
  fun σ hI _ y hy => h σ hI y hy

theorem ikve_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hm' : IKE VfC m) (hg : ∀ a, IKVE (g a)) : IKVE (m >>= g) := by
  intro σ hI hU y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm' σ hI z hz) (utInv''_of_view (hm (uV σ) σ rfl z hz) hU) y hy
  · exact hm' σ hI z hz

theorem ikve_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKVE m) (hg : ∀ a, IKE VfC (g a)) : IKVE (m >>= g) := by
  intro σ hI hU y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm σ hI hU z hz) y hy
  · exact hm σ hI hU z hz

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `VfC`**, from `UtInv''` at its start. -/
theorem vfh_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKVE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikve_bind_uk (fun _ => by uk_auto) (by vfc_auto) fun thread =>
    ikve_bind_uk (fun _ => by uk_auto) (by vfc_auto) fun info => ?_
  intro σ hI hU y hy
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hFv : IKE VfC (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by vfc_auto
  have hOk : OkV (uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ).2.1 p.2 = some p.1) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCaps _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := fun s => VfC s ∧ uV s = uV σ) (Q := VfC)
    (fun w hw => ⟨hFv σ hI w hw, hF _ σ rfl w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK VfC (NonDet.when blocking (handleFault thread f)) by vfc_auto) s hs.1 v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hs : VfC s ∧ uV s = uV σ := ⟨hFv σ hI _ has, hF _ σ rfl _ has⟩
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEv : IKE VfC (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by vfc_auto
    exact ⟨hEv s hs.1 w hw, (hE _ s rfl w hw).trans hs.2⟩
  · intro e s hs v hv
    exact (by vfc_auto : IK VfC _) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    have hs : VfC s := hFv σ hI _ has
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := by
      rw [← vfh_capAt]; show (uV s).2.1 sl = some cap; rw [hvs]; exact hc
    have hexs : ∀ p ∈ ex, capOpt (s.kheap p.2.1) p.2.2 = some p.1 := by
      intro p hp
      rw [← vfh_capAt]; show (uV s).2.1 p.2 = some p.1; rw [hvs]; exact hex p hp
    have hdec : InvOKV (uV σ) b := by
      have := okv_bind_uk (P := InvOKV (uV σ)) (fun _ => ike_liftE (uk_getMrs _ _ _)) (fun args =>
        okv_fl4Decode (w := uV σ) fp info.miLabel args cptr sl cap ex buf hc hex) s hvs b s' hbs
      exact this
    have hvi : SInvV.hV s' = SInvV.hV s ∧ VInv s b :=
      SInvV.okv_bind (Q := fun _ => True) (SInvV.okv_frame fun v => by hv_auto)
        (fun args _ => vfh_okv_fl4Decode s hs.1 hs.2 fp info.miLabel args cptr sl cap ex buf hcap hexs)
        s rfl b s' hbs
    have hU' : UtInv'' s' := utInv''_of_view hI'.2 hU
    have hTS : ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart)) := fun _ => by uk_auto
    have hTSh : ∀ v, SInv.IKE (fun x => SInvV.hV x = v) (withoutPreemption (Z := Unit) (setThreadState thread .restart)) :=
      fun _ => by hv_auto
    have hTSv : IKE VfC (withoutPreemption (Z := Unit) (setThreadState thread .restart)) := by vfc_auto
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := hTS _ s' rfl z hz
      have hzh : SInvV.hV z.2 = SInvV.hV s' := hTSh _ s' rfl z hz
      have hzv : VfC z.2 := hTSv s' hI'.1 z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2
      have hok1 : InvOKV (uV s1) b := by rw [hv1]; exact hdec
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := vfh_fl4Perform blocking calling don b s s1 (hzh.trans hvi.1) hzv.1 hzv.2
          (utInv''_of_view hz' hU') hok1 hvi.2 _ hz2
        exact (by vfc_auto : IKE VfC _) s2 hs2 y hy
      · exact vfh_fl4Perform blocking calling don b s s1 (hzh.trans hvi.1) hzv.1 hzv.2
          (utInv''_of_view hz' hU') hok1 hvi.2 _ hz2
    · exact hTSv s' hI'.1 z hz

/-! ## The syscall paths -/

set_option maxHeartbeats 8000000 in
theorem vfh_capRegL (r : Register) : IKE VfC (NonDetE.liftE (ε := Unit) (getCapReg (Z := Unit) r)) := by
  vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_capRegLU (r : Register) : ∀ v, UKE v (NonDetE.liftE (ε := Unit) (getCapReg (Z := Unit) r)) :=
  fun _ => by uk_auto

set_option maxHeartbeats 8000000 in
theorem vfh_capRegW (r : Register) : IKE VfC (withoutPreemption (Z := Unit) (getCapReg (Z := Unit) r)) := by
  vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_capRegWU (r : Register) : ∀ v, UKE v (withoutPreemption (Z := Unit) (getCapReg (Z := Unit) r)) :=
  fun _ => by uk_auto

set_option maxHeartbeats 8000000 in
theorem vfh_recvW (a b : Bool) : IKE VfC (withoutPreemption (Z := Unit) (handleRecv (Z := Unit) a b)) := by
  vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_yieldW : IKE VfC (withoutPreemption (Z := Unit) (handleYield (Z := Unit))) := by
  vfc_auto

theorem vfh_sysInv (rep calling blocking don fp : Bool) (r : Register) :
    IKVE (do
      let cptr ← NonDetE.liftE <| getCapReg (Z := Unit) r
      fl4HandleInvocationR rep calling blocking don fp cptr) :=
  ikve_bind_uk (vfh_capRegLU r) (vfh_capRegL r) fun _ => vfh_handleInvocationR _ _ _ _ _ _

theorem vfh_sysInvRecv (rep calling blocking don fp a b : Bool) (r : Register) :
    IKVE (do
      let c ← withoutPreemption <| getCapReg (Z := Unit) r
      fl4HandleInvocationR rep calling blocking don fp c
      withoutPreemption <| handleRecv a b) :=
  ikve_bind_uk (vfh_capRegWU r) (vfh_capRegW r) fun _ =>
    ikve_bind (vfh_handleInvocationR _ _ _ _ _ _) fun _ => vfh_recvW a b

theorem vfh_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKVE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c
  · exact vfh_sysInv rep true true true false cap_register
  · exact vfh_sysInvRecv rep false false true true true true replyRegister
  · exact vfh_sysInvRecv rep false false true true true true nbsendRecvDest
  · exact vfh_sysInvRecv rep false false true true true false replyRegister
  · exact vfh_sysInv rep false true false false cap_register
  · exact vfh_sysInv rep false false false false cap_register
  · exact ikv_of_ik (vfh_recvW true true)
  · exact ikv_of_ik vfh_yieldW
  · exact ikv_of_ik (vfh_recvW false true)
  · exact ikv_of_ik (vfh_recvW true false)
  · exact ikv_of_ik (vfh_recvW false false)

set_option maxHeartbeats 8000000 in
theorem vfh_he_unknown (n : Nat) : IKE VfC (handleEvent (Z := Unit) (.unknownSyscall n)) := by
  simp only [handleEvent]; vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_he_ulf (w1 w2 : Word) : IKE VfC (handleEvent (Z := Unit) (.userLevelFault w1 w2)) := by
  simp only [handleEvent]; vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_he_interrupt : IKE VfC (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent]; vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_he_vm (t : VMFaultType) : IKE VfC (handleEvent (Z := Unit) (.vmFaultEvent t)) := by
  simp only [handleEvent]; vfc_auto

set_option maxHeartbeats 8000000 in
theorem vfh_he_hyp (t : HypFaultType) : IKE VfC (handleEvent (Z := Unit) (.hypervisorEvent t)) := by
  simp only [handleEvent]; vfc_auto

theorem vfh_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : IKE VfC (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | unknownSyscall n => exact vfh_he_unknown n
  | userLevelFault w1 w2 => exact vfh_he_ulf w1 w2
  | interrupt => exact vfh_he_interrupt
  | vmFaultEvent t => exact vfh_he_vm t
  | hypervisorEvent t => exact vfh_he_hyp t

set_option maxHeartbeats 4000000 in
theorem vfh_fl4HandleEvent (rep : Bool) (ev : Event) : IKVE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikve_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (by vfc_auto) fun _ => ?_
    intro σ hI hU y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : VfC x.2 := (by vfc_auto : IK VfC (checkBudgetRestart (Z := Unit))) σ hI x hx
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        have hv := checkBudgetRestart_true hx ht
        exact vfh_fl4HandleSyscall rep c x.2 hIx (utInv''_of_view hv hU) y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hIx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikv_of_ik (vfh_handleEvent_other ev fun c e => h ⟨c, e⟩)

theorem ikv_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKV m) (hg : ∀ a, IK VfC (g a)) : IKV (m >>= g) := by
  intro σ hI hU y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm σ hI hU x hx) y hy

theorem ikv_bind_uk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ v, UK v m) (hm' : IK VfC m) (hg : ∀ a, IKV (g a)) : IKV (m >>= g) := by
  intro σ hI hU y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm' σ hI x hx) (utInv''_of_view (uk_mem hm hx) hU) y hy

set_option maxHeartbeats 4000000 in
theorem vfh_fl4CallKernel (rep : Bool) (ev : Event) : IKV (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikv_bind ?_ fun _ => by vfc_auto
  intro σ hI hU y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := vfh_fl4HandleEvent rep ev σ hI hU z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE VfC (withoutPreemption (Z := Unit) preemptionPath) by vfc_auto) s hz' y hy

set_option maxHeartbeats 4000000 in
theorem vfh_fl4CallKernel_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IK VfC (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind ?_ fun _ => by vfc_auto
  refine ike_handleE ?_ fun _ => by vfc_auto
  rw [fl4HandleEvent_other rep ev h]
  exact vfh_handleEvent_other ev h

/-! ## Tops -/

/-- **`VfhAll ∧ CnDom` across the syscall entry.** `hU : UtInv3 σ` is a G1 field
(the untyped invariant with the IRQ-node fact; preservation: ut7); only its
`UtInv''` part is read, by the untyped retype and MakePool. -/
theorem kentry_vfhAll (c : Syscall) {σ : State Unit} (hV : VfhAll σ) (hC : CnDom σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, VfhAll y.2 ∧ CnDom y.2 := by
  intro y hy
  unfold fl4KernelEntrySyscall at hy
  have h := ikv_bind_uk (fun _ => ik_gets _) (by vfc_auto) (fun ct => ikv_bind_uk (fun _ => uk_fl4SyscallFaultIP ct)
    (by vfc_auto) fun _ => vfh_fl4CallKernel true _) σ ⟨(vfhV_iff σ).2 hV, hC⟩ hU.1 y hy
  exact ⟨(vfhV_iff _).1 h.1, h.2⟩

/-- **`VfhAll ∧ CnDom` across every kernel event** (`hU` read only by a
syscall's untyped / MakePool invocation; G1 field, preservation: ut7). -/
theorem kcall_vfhAll (rep : Bool) (ev : Event) {σ : State Unit} (hV : VfhAll σ) (hC : CnDom σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, VfhAll y.2 ∧ CnDom y.2 := by
  intro y hy
  have h := vfh_fl4CallKernel rep ev σ ⟨(vfhV_iff σ).2 hV, hC⟩ hU.1 y hy
  exact ⟨(vfhV_iff _).1 h.1, h.2⟩

/-- **`VfhAll ∧ CnDom` across interrupts, faults and the other non-syscall events**, no other fact. -/
theorem kcall_vfhAll_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hV : VfhAll σ) (hC : CnDom σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, VfhAll y.2 ∧ CnDom y.2 := by
  intro y hy
  have h' := vfh_fl4CallKernel_other rep ev h σ ⟨(vfhV_iff σ).2 hV, hC⟩ y hy
  exact ⟨(vfhV_iff _).1 h'.1, h'.2⟩

end

end Fl4Proofs.P3.SInv
