/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sg1): **SpecGlob across the
kernel entries** (spec side only, outside the JAtZ cone; imports SpecInvSgD).

* `SgOKN w inv` (a rotate's source / pivot are lookup destinations, a VSpace map's
  slot holds an arch cap) and `okv_fl4DecodeS`; with ut7's `InvOKN` and ut8's
  `GapOKN` they are every decode fact the performs need.
* `sgP_fl4Perform` (every perform keeps `S N M` from a state whose node is `N`), the
  invocation shell `sgN_handleInvocationR` (ut7's `p3N_handleInvocationR` with
  `S N M`), the syscalls, the events, `fl4CallKernel`, the syscall entry (`IKS`).
* **`SpecGlobS σ`**: SpecGlob (SpecGlob.lean) stated on `capAt` (the same three
  clauses; SpecGlob's module lies in the JAtZ cone, the bridge is
  SpecInvSgBridge). **`IdleOutV σ := IrqOutV (fun _ => σ.idleThread) (uV σ)` [J]**
  (l4v `valid_global_refs` for the idle thread: `idle_thread_ptr ∈ global_refs`,
  outside the `cap_range` of every cap, untyped regions included; the same
  statement UtInv3 makes for the IRQ node, ut6's `IrqOutV`): the extra fact carried
  with SpecGlob. It makes SpecGlob inductive: a retype creates caps only inside
  its untyped's region, which holds neither the idle thread nor an IRQ-node CNode.
* **`kentry_specGlob (c) (hG : SpecGlobS σ) (hI : IdleOutV σ) (hU : UtInv3 σ) :
  ∀ y ∈ (fl4KernelEntrySyscall true c σ).1, SpecGlobS y.2 ∧ IdleOutV y.2`**,
  **`kcall_specGlob (rep ev)`** (every event), `boot_specGlob` (non-vacuity only).
  `hU` is a hypothesis (UtInv3 is itself carried: ut8's `kentry_utInv2`).
-/
import Fl4Proofs.P3.SpecInvSgD
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Decode facts -/

/-- sg1's decode facts beyond ut7's `InvOKN` and ut8's `GapOKN`. -/
def SgOKN (w : UView) : Fl4Invocation → Prop
  | .invokeCNode ci => RotOKN w ci
  | .invokeArchObject ai => Fl4ArchSlN w ai
  | _ => True

set_option maxHeartbeats 4000000 in
theorem okv_fl4DecodeS {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : w.2.1 sl = some cap)
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (SgOKN w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  have hcps : ∀ c ∈ ex.map Prod.fst, ∃ s, w.2.1 s = some c := by
    intro c h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨p.2, hex p hp⟩
  cases cap with
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_decodeCnodeRot label args _ _ hcps))
  | archObjectCap ac =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_fl4ArchDecodeSl label args ci sl ac ex hc)
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

variable {N M : Irq → ObjRef}

/-! ## The performs -/

set_option maxHeartbeats 4000000 in
theorem sgP_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hI : S N M σ) (hN : NodeIs N σ) (hok : InvOKN (uV σ) inv) (hg : GapOKN (uV σ) inv) (hs : SgOKN (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, S N M y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact sg_invokeUntyped ui σ hI hg z hz
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    by_cases hm : ∃ a, ai = .spec (.invokeASIDControl a)
    · obtain ⟨a, rfl⟩ := hm
      simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      exact sg_makePool hI hg z hz
    · exact sg_fl4ArchPerform ai (fun a e => hm ⟨a, e⟩) σ hI hg hs y hy
  | invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact sg_invokeCnode ci σ hI hok hs z hz
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact sg_invokeFl4IrqControl i σ hI hok z hz
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    cases i with
    | setIRQHandler irq c sl =>
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      exact sg_setIRQHandler irq c sl σ hI hN hok x hx
    | _ => exact (show IKE (S N M) (NonDetE.liftE (ε := Unit) (invokeIrqHandler (Z := Unit) _)) by
        refine ike_liftE ?_; simp only [invokeIrqHandler]; sg_auto) σ hI z hz
  | _ => exact (show IKE (S N M) _ by simp only [fl4PerformInvocation]; sg_auto) σ hI y hy

/-! ## The invocation shell -/

/-- `S N M` kept from an `S N M` state whose IRQ node is `N`. -/
def IKS {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ (N M : Irq → ObjRef) σ, S N M σ → NodeIs N σ → ∀ y ∈ (m σ).1, S N M y.2

abbrev IKSE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKS (ExceptT.run m)

theorem iks_of_ik {α : Type} {m : NonDet (State Unit) α} (h : ∀ N M, IK (S N M) m) : IKS m :=
  fun N M σ hI _ y hy => h N M σ hI y hy

theorem ikse_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hmN : ∀ N, NKE N m) (hg : ∀ a, IKSE (g a)) : IKSE (m >>= g) := by
  intro N M σ hI hN y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N M z.2 (s_of_view (hm (uV σ) σ rfl z hz) hI) (hmN N σ hN z hz) y hy
  · exact s_of_view (hm (uV σ) σ rfl z hz) hI

theorem ikse_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKSE m) (hg : ∀ a, ∀ N M, IKE (S N M) (g a)) : IKSE (m >>= g) := by
  intro N M σ hI hN y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N M z.2 (hm N M σ hI hN z hz) y hy
  · exact hm N M σ hI hN z hz

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `S N M`.** -/
theorem sgN_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKSE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikse_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun thread =>
    ikse_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun info => ?_
  intro N M σ hI hN y hy
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
  refine syscall_postU (I := fun s => S N M s ∧ uV s = uV σ ∧ NodeIs N s) (Q := S N M)
    (fun w hw => ⟨s_of_view (hF _ σ rfl w hw) hI, hF _ σ rfl w hw, hFN σ hN w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK (S N M) (NonDet.when blocking (handleFault thread f)) by sg_auto) s hs.1 v hv
  · intro a s has w hw
    have hs : S N M s ∧ uV s = uV σ ∧ NodeIs N s :=
      ⟨s_of_view (hF _ σ rfl _ has) hI, hF _ σ rfl _ has, hFN σ hN _ has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEN : NKE N (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by nk_auto
    exact ⟨s_of_view (hE _ s rfl w hw) hs.1, (hE _ s rfl w hw).trans hs.2.1, hEN s hs.2.2 w hw⟩
  · intro e s hs v hv
    exact (s_of_uk fun _ => by uk_auto) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
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
    have hdg : GapOKN (uV σ) b :=
      okv_fl4DecodeG fp info.miLabel x0.1 cptr sl cap ex buf hc (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    have hds : SgOKN (uV σ) b :=
      okv_fl4DecodeS fp info.miLabel x0.1 cptr sl cap ex buf hc (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := (show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz
      have hzN : NodeIs N z.2 := (show NKE N (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by nk_auto) s' hI'.2.2 z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2.1
      have hI1 : S N M s1 := s_of_view hz' hI'.1
      have hok1 : InvOKN (uV s1) b := by rw [hv1]; exact hdec
      have hg1 : GapOKN (uV s1) b := by rw [hv1]; exact hdg
      have hs1 : SgOKN (uV s1) b := by rw [hv1]; exact hds
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := sgP_fl4Perform blocking calling don b s1 hI1 hzN hok1 hg1 hs1 _ hz2
        exact (se_of_uk fun _ => by uk_auto) s2 hs2 y hy
      · exact sgP_fl4Perform blocking calling don b s1 hI1 hzN hok1 hg1 hs1 _ hz2
    · exact s_of_view ((show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz) hI'.1

/-! ## The syscall paths and events -/

set_option maxHeartbeats 4000000 in
theorem sgN_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKSE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall]
  all_goals first
    | exact ikse_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun _ => sgN_handleInvocationR _ _ _ _ _ _
    | exact ikse_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun _ =>
        ikse_bind (sgN_handleInvocationR _ _ _ _ _ _) fun _ _ _ => by sg_auto
    | exact iks_of_ik fun _ _ => by sg_auto

set_option maxHeartbeats 4000000 in
theorem sg_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKE (S N M) (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; sg_auto

set_option maxHeartbeats 4000000 in
theorem sgN_fl4HandleEvent (rep : Bool) (ev : Event) : IKSE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikse_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (fun _ => by nk_auto) fun _ => ?_
    intro N M σ hI hN y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : S N M x.2 := sg_checkBudgetRestart σ hI x hx
      have hNx : NodeIs N x.2 := (show NK N (checkBudgetRestart (Z := Unit)) by nk_auto) σ hN x hx
      unfold NonDetE.whenE at hy
      split at hy
      · exact sgN_fl4HandleSyscall rep c N M x.2 hIx hNx y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hIx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact iks_of_ik fun _ _ => sg_handleEvent_other ev fun c e => h ⟨c, e⟩

theorem iks_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKS m) (hg : ∀ a, ∀ N M, IK (S N M) (g a)) : IKS (m >>= g) := by
  intro N M σ hI hN y ⟨x, hx, hy⟩
  exact hg x.1 N M x.2 (hm N M σ hI hN x hx) y hy

theorem iks_bind_uk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ v, UK v m) (hmN : ∀ N, NK N m) (hg : ∀ a, IKS (g a)) : IKS (m >>= g) := by
  intro N M σ hI hN y ⟨x, hx, hy⟩
  exact hg x.1 N M x.2 (s_of_view (uk_mem hm hx) hI) (hmN N σ hN x hx) y hy

set_option maxHeartbeats 4000000 in
theorem sgN_fl4CallKernel (rep : Bool) (ev : Event) : IKS (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine iks_bind ?_ fun _ _ _ => by sg_auto
  intro N M σ hI hN y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := sgN_fl4HandleEvent rep ev N M σ hI hN z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE (S N M) (withoutPreemption (Z := Unit) preemptionPath) by sg_auto) s hz' y hy

set_option maxHeartbeats 4000000 in
theorem sgN_kentry (c : Syscall) : IKS (fl4KernelEntrySyscall (Z := Unit) true c) := by
  unfold fl4KernelEntrySyscall
  exact iks_bind_uk (fun _ => ik_gets _) (fun _ => ik_gets _) fun ct => iks_bind_uk
    (fun _ => uk_fl4SyscallFaultIP ct) (fun _ => nk_fl4SyscallFaultIP ct) fun _ => sgN_fl4CallKernel true _

/-! ## SpecGlob -/

/-- A frame cap. -/
def IsFrameCap : Cap → Prop
  | .archObjectCap (.pageCap ..) => True
  | _ => False

/-- **SpecGlob** (SpecGlob.lean's three clauses, on `capAt`). -/
structure SpecGlobS (σ : State Unit) : Prop where
  irq : ∀ irq a, capAt σ (σ.interruptIrqNode irq, []) = some a →
    a = .nullCap ∨ ∃ r b rs, a = .notificationCap r b rs
  ref : ∀ p cref a, capAt σ (p, cref) = some a → ¬ IsFrameCap a → ∀ irq, σ.interruptIrqNode irq ∉ objRefs a
  idle : ∀ p cref a, capAt σ (p, cref) = some a → ¬ IsFrameCap a → σ.idleThread ∉ objRefs a

/-- **The idle thread lies outside every cap's range [J]** (l4v `valid_global_refs`,
`idle_thread_ptr ∈ global_refs`; module docstring). -/
def IdleOutV (σ : State Unit) : Prop := IrqOutV (fun _ => σ.idleThread) (uV σ)

theorem notIn_objRefs {K : Irq → ObjRef} {w : UView} (h : IrqOutV K w) {s : CslotPtr} {a : Cap}
    (hs : w.2.1 s = some a) (irq : Irq) : K irq ∉ objRefs a :=
  fun hr => h irq s a hs (capRng_sub_covR _ (objRefs_sub_capRng _ hr))

/-- `SpecGlobS ∧ IdleOutV` from the family at the state's node and idle thread. -/
theorem specGlob_of_S {σ : State Unit} (hS : S σ.interruptIrqNode (fun _ => σ.idleThread) σ) :
    SpecGlobS σ ∧ IdleOutV σ :=
  ⟨⟨fun irq a ha => hS.2.2 irq a ha, fun p cref a ha _ irq => notIn_objRefs hS.1.2 ha irq,
    fun p cref a ha _ => notIn_objRefs hS.2.1 ha (default : Irq)⟩, hS.2.1⟩

theorem S_of_specGlob {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ) (hU : UtInv3 σ) :
    S σ.interruptIrqNode (fun _ => σ.idleThread) σ :=
  ⟨hU, hI, fun irq a ha => hG.irq irq a ha⟩

/-- **SpecGlob across the syscall entry** (with the idle thread's range fact; `hU`: UtInv3,
itself carried by ut8's `kentry_utInv2`). -/
theorem kentry_specGlob (c : Syscall) {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SpecGlobS y.2 ∧ IdleOutV y.2 := by
  intro y hy
  have hN : NodeIs σ.interruptIrqNode y.2 := nk_fl4KernelEntrySyscall true c σ rfl y hy
  have hT : IdleIs σ.idleThread y.2 := idk_fl4KernelEntrySyscall true c σ rfl y hy
  have hS := sgN_kentry c σ.interruptIrqNode (fun _ => σ.idleThread) σ (S_of_specGlob hG hI hU) rfl y hy
  have e1 : y.2.interruptIrqNode = σ.interruptIrqNode := hN
  have e2 : y.2.idleThread = σ.idleThread := hT
  rw [← e1, ← e2] at hS
  exact specGlob_of_S hS

/-- **SpecGlob across every kernel event.** -/
theorem kcall_specGlob (rep : Bool) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ)
    (hU : UtInv3 σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SpecGlobS y.2 ∧ IdleOutV y.2 := by
  intro y hy
  have hN : NodeIs σ.interruptIrqNode y.2 := nk_fl4CallKernel rep ev σ rfl y hy
  have hT : IdleIs σ.idleThread y.2 := idk_fl4CallKernel rep ev σ rfl y hy
  have hS := sgN_fl4CallKernel rep ev σ.interruptIrqNode (fun _ => σ.idleThread) σ (S_of_specGlob hG hI hU) rfl y hy
  have e1 : y.2.interruptIrqNode = σ.interruptIrqNode := hN
  have e2 : y.2.idleThread = σ.idleThread := hT
  rw [← e1, ← e2] at hS
  exact specGlob_of_S hS

/-- Boot (non-vacuity only: the initial state holds null caps). -/
theorem boot_specGlob : SpecGlobS (initASt (Z := Unit)) ∧ IdleOutV (initASt (Z := Unit)) := by
  refine ⟨⟨fun irq a ha => Or.inl (init_capAt ha), fun p cref a ha _ irq => ?_, fun p cref a ha _ => ?_⟩,
    boot_irqOut _⟩
  · rw [init_capAt ha]; simp [objRefs]
  · rw [init_capAt ha]; simp [objRefs]

end

end Fl4Proofs.P3.SInvG
