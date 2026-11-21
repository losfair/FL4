/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut7): **`UtInv3` across the
kernel entries with no `DetypeOK`, reduced to the untyped and arch performs**
(spec side only; imports SpecInvUtO5 and SpecInvUtNK6).

* `InvOKN w inv`: the decode facts the hand-written performs need (CNode
  `CnOKN`, IRQ control `Fl4IrqCOKN`, IRQ handler `IrqHOKN`);
  **`okv_fl4DecodeN`** establishes them (the invoked cap in its slot, every extra
  cap in its slot, which is a CSpace lookup: `okv_lookupExtraCapsN`).
* `DecodedFrom w inv`: `inv` is an `.ok` outcome of `fl4DecodeInvocation` from a
  state of view `w` whose invoked slot / extra-cap slots hold the decoded caps.
* **`PerfGap`** (the REMAINING obligation, not an invariant premise): the
  performs of untyped and arch invocations keep `P3 N` from a `P3 N` state with
  node `N`, for an invocation decoded from that state's view. It is a ∀-states
  statement about two families of performs (the untyped retype / reset, MakePool,
  the VSpace map / unmap performs, DeriveSubframe; IO-port control and ASID-pool
  assign are already proved, SpecInvUtO5), all believed true (l4v
  `invoke_untyped_invs`, `perform_asid_control_invocation` / `arch_perform_invocation`
  `invs`), each to be proved with its decode facts (ut7 handoff).
* `p3P_fl4Perform` (every other perform), the shell `p3N_handleInvocationR`
  (`IKN`: `P3 N` kept from a `P3 N` state whose node is `N`; the node is carried
  by the `NK` frames), the events, and the tops **`kentry_utInv2_of`** /
  **`kcall_utInv2_of`** (`UtInv3` kept, given `PerfGap`).
-/
import Fl4Proofs.P3.SpecInvUtO5
import Fl4Proofs.P3.SpecInvUtNK6
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Decode facts -/

/-- **What the hand-written performs need from the decode** (on the view). -/
def InvOKN (w : UView) : Fl4Invocation → Prop
  | .invokeCNode ci => CnOKN w ci
  | .invokeIRQControl i => Fl4IrqCOKN w i
  | .invokeIRQHandler i => IrqHOKN w i
  | _ => True

set_option maxHeartbeats 4000000 in
theorem okv_fl4DecodeN {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : w.2.1 sl = some cap)
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1 ∧ DestRefV w p.2) :
    OkV w (InvOKN w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  have hcps : ∀ c ∈ ex.map Prod.fst, ∃ s, w.2.1 s = some c := by
    intro c h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨p.2, (hex p hp).1⟩
  cases cap with
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_decodeCnodeN label args _ _ ⟨sl, hc⟩))
  | irqControlCap =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_decodeFl4IrqControlN _ label args sl _ hc hcps)
  | irqHandlerCap irq =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_decodeIrqHandlerN label irq ex hex)
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

/-- `inv` was decoded from a state of view `w`. -/
def DecodedFrom (w : UView) (inv : Fl4Invocation) : Prop :=
  ∃ (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ0 s0 : State Unit),
    uV σ0 = w ∧ w.2.1 sl = some cap ∧ (∀ p ∈ ex, w.2.1 p.2 = some p.1 ∧ DestRefV w p.2) ∧
    (Except.ok inv, s0) ∈ ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ0).1

/-- The invocations whose performs are not yet proved for `P3`. -/
def GapInv : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeArchObject _ => True
  | _ => False

/-- **The remaining obligation** (ut7 handoff; not an invariant premise): the untyped
and arch performs keep `P3 N` for an invocation decoded from the state's view. -/
def PerfGap : Prop :=
  ∀ (N : Irq → ObjRef) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit), GapInv inv →
    P3 N σ → NodeIs N σ → DecodedFrom (uV σ) inv →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, P3 N y.2

variable {N : Irq → ObjRef}

/-! ## The performs -/

theorem p3P_fl4Perform (hG : PerfGap) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hI : P3 N σ) (hN : NodeIs N σ) (hok : InvOKN (uV σ) inv) (hD : DecodedFrom (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, P3 N y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui => exact hG N blk call don (.invokeUntyped ui) σ trivial hI hN hD y hy
  | invokeArchObject ai => exact hG N blk call don (.invokeArchObject ai) σ trivial hI hN hD y hy
  | invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact p3_invokeCnode ci σ hI hok z hz
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact p3_invokeFl4IrqControl i σ hI hok z hz
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    cases i with
    | setIRQHandler irq c sl =>
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      exact p3_setIRQHandler irq c sl σ hI hN hok x hx
    | _ => exact (show IKE (P3 N) (NonDetE.liftE (ε := Unit) (invokeIrqHandler (Z := Unit) _)) by
        refine ike_liftE ?_; simp only [invokeIrqHandler]; un_auto) σ hI z hz
  | _ => exact (show IKE (P3 N) _ by simp only [fl4PerformInvocation]; un_auto) σ hI y hy

/-! ## The invocation shell -/

/-- `P3 N` kept from a `P3 N` state whose IRQ node is `N`. -/
def IKN {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ (N : Irq → ObjRef) σ, P3 N σ → NodeIs N σ → ∀ y ∈ (m σ).1, P3 N y.2

abbrev IKNE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKN (ExceptT.run m)

theorem ikn_of_ik {α : Type} {m : NonDet (State Unit) α} (h : ∀ N, IK (P3 N) m) : IKN m :=
  fun N σ hI _ y hy => h N σ hI y hy

theorem ikne_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hmN : ∀ N, NKE N m) (hg : ∀ a, IKNE (g a)) : IKNE (m >>= g) := by
  intro N σ hI hN y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N z.2 (p3_of_view (hm (uV σ) σ rfl z hz) hI) (hmN N σ hN z hz) y hy
  · exact p3_of_view (hm (uV σ) σ rfl z hz) hI

theorem ikne_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKNE m) (hg : ∀ a, ∀ N, IKE (P3 N) (g a)) : IKNE (m >>= g) := by
  intro N σ hI hN y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N z.2 (hm N σ hI hN z hz) y hy
  · exact hm N σ hI hN z hz

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `P3 N`** (given `PerfGap`). -/
theorem p3N_handleInvocationR (hG : PerfGap) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKNE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikne_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun thread =>
    ikne_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun info => ?_
  intro N σ hI hN y hy
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hFN : NKE N (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by nk_auto
  have hOk : OkV (uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ).2.1 p.2 = some p.1 ∧ DestRefV (uV σ) p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := fun s => P3 N s ∧ uV s = uV σ ∧ NodeIs N s) (Q := P3 N)
    (fun w hw => ⟨p3_of_view (hF _ σ rfl w hw) hI, hF _ σ rfl w hw, hFN σ hN w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK (P3 N) (NonDet.when blocking (handleFault thread f)) by un_auto) s hs.1 v hv
  · intro a s has w hw
    have hs : P3 N s ∧ uV s = uV σ ∧ NodeIs N s :=
      ⟨p3_of_view (hF _ σ rfl _ has) hI, hF _ σ rfl _ has, hFN σ hN _ has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEN : NKE N (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by nk_auto
    exact ⟨p3_of_view (hE _ s rfl w hw) hs.1, (hE _ s rfl w hw).trans hs.2.1, hEN s hs.2.2 w hw⟩
  · intro e s hs v hv
    exact (p3_of_uk fun _ => by uk_auto) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    -- the decode's facts and the decoded-from witness
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV σ := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hdec : InvOKN (uV σ) b :=
      okv_fl4DecodeN fp info.miLabel x0.1 cptr sl cap ex buf hc hex x0.2 hvx b s' hb0
    have hDF : DecodedFrom (uV σ) b := ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hc, hex, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := (show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz
      have hzN : NodeIs N z.2 := (show NKE N (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by nk_auto) s' hI'.2.2 z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2.1
      have hI1 : P3 N s1 := p3_of_view hz' hI'.1
      have hok1 : InvOKN (uV s1) b := by rw [hv1]; exact hdec
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := p3P_fl4Perform hG blocking calling don b s1 hI1 hzN hok1 hDF1 _ hz2
        exact (p3e_of_uk fun _ => by uk_auto) s2 hs2 y hy
      · exact p3P_fl4Perform hG blocking calling don b s1 hI1 hzN hok1 hDF1 _ hz2
    · exact p3_of_view ((show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz) hI'.1

/-! ## The syscall paths and events -/

set_option maxHeartbeats 4000000 in
theorem p3N_fl4HandleSyscall (hG : PerfGap) (rep : Bool) (c : Syscall) : IKNE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall]
  all_goals first
    | exact ikne_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun _ => p3N_handleInvocationR hG _ _ _ _ _ _
    | exact ikne_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun _ =>
        ikne_bind (p3N_handleInvocationR hG _ _ _ _ _ _) fun _ _ => by un_auto
    | exact ikn_of_ik fun _ => by un_auto

set_option maxHeartbeats 4000000 in
theorem un_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : IKE (P3 N) (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; un_auto

set_option maxHeartbeats 4000000 in
theorem p3N_fl4HandleEvent (hG : PerfGap) (rep : Bool) (ev : Event) : IKNE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikne_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (fun _ => by nk_auto) fun _ => ?_
    intro N σ hI hN y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : P3 N x.2 := un_checkBudgetRestart σ hI x hx
      have hNx : NodeIs N x.2 := (show NK N (checkBudgetRestart (Z := Unit)) by nk_auto) σ hN x hx
      unfold NonDetE.whenE at hy
      split at hy
      · exact p3N_fl4HandleSyscall hG rep c N x.2 hIx hNx y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hIx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikn_of_ik fun _ => un_handleEvent_other ev fun c e => h ⟨c, e⟩

theorem ikn_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKN m) (hg : ∀ a, ∀ N, IK (P3 N) (g a)) : IKN (m >>= g) := by
  intro N σ hI hN y ⟨x, hx, hy⟩
  exact hg x.1 N x.2 (hm N σ hI hN x hx) y hy

theorem ikn_bind_uk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ v, UK v m) (hmN : ∀ N, NK N m) (hg : ∀ a, IKN (g a)) : IKN (m >>= g) := by
  intro N σ hI hN y ⟨x, hx, hy⟩
  exact hg x.1 N x.2 (p3_of_view (uk_mem hm hx) hI) (hmN N σ hN x hx) y hy

set_option maxHeartbeats 4000000 in
theorem p3N_fl4CallKernel (hG : PerfGap) (rep : Bool) (ev : Event) : IKN (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikn_bind ?_ fun _ _ => by un_auto
  intro N σ hI hN y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := p3N_fl4HandleEvent hG rep ev N σ hI hN z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE (P3 N) (withoutPreemption (Z := Unit) preemptionPath) by un_auto) s hz' y hy

/-! ## Tops -/

set_option maxHeartbeats 4000000 in
theorem p3N_kentry (hG : PerfGap) (c : Syscall) : IKN (fl4KernelEntrySyscall (Z := Unit) true c) := by
  unfold fl4KernelEntrySyscall
  exact ikn_bind_uk (fun _ => ik_gets _) (fun _ => ik_gets _) fun ct => ikn_bind_uk
    (fun _ => uk_fl4SyscallFaultIP ct) (fun _ => nk_fl4SyscallFaultIP ct) fun _ => p3N_fl4CallKernel hG true _

/-- **`UtInv3` across the syscall entry, given `PerfGap`** (no `DetypeOK`). -/
theorem kentry_utInv2_of (hG : PerfGap) (c : Syscall) {σ : State Unit} (hI : UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, UtInv3 y.2 := by
  intro y hy
  have hN : NodeIs σ.interruptIrqNode y.2 := nk_fl4KernelEntrySyscall true c σ rfl y hy
  have hP : P3 σ.interruptIrqNode y.2 := p3N_kentry hG c σ.interruptIrqNode σ (utInv3_iff.1 hI) rfl y hy
  show P3 y.2.interruptIrqNode y.2
  rw [show y.2.interruptIrqNode = σ.interruptIrqNode from hN]; exact hP

/-- **`UtInv3` across every kernel event, given `PerfGap`** (no `DetypeOK`). -/
theorem kcall_utInv2_of (hG : PerfGap) (rep : Bool) (ev : Event) {σ : State Unit} (hI : UtInv3 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, UtInv3 y.2 := by
  intro y hy
  have hN : NodeIs σ.interruptIrqNode y.2 := nk_fl4CallKernel rep ev σ rfl y hy
  have hP := p3N_fl4CallKernel hG rep ev σ.interruptIrqNode σ (utInv3_iff.1 hI) rfl y hy
  show P3 y.2.interruptIrqNode y.2
  rw [show y.2.interruptIrqNode = σ.interruptIrqNode from hN]; exact hP

/-- **`UtInv3` across interrupts, faults and the other non-syscall events**, with no premise. -/
theorem kcall_utInv2_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (hI : UtInv3 σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, UtInv3 y.2 := by
  intro y hy
  have hN : NodeIs σ.interruptIrqNode y.2 := nk_fl4CallKernel rep ev σ rfl y hy
  have hP : P3 σ.interruptIrqNode y.2 := by
    unfold fl4CallKernel at hy
    refine (ik_bind ?_ fun _ => by un_auto) σ (utInv3_iff.1 hI) y hy
    refine ike_handleE ?_ fun _ => by un_auto
    rw [fl4HandleEvent_other rep ev h]
    exact un_handleEvent_other ev h
  show P3 y.2.interruptIrqNode y.2
  rw [show y.2.interruptIrqNode = σ.interruptIrqNode from hN]; exact hP

end

end Fl4Proofs.P3.SInvU
