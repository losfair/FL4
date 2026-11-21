/-
P3 (DESIGN.md §9), invariant line G1 (rd8v): **`VB` carried across the syscall entry and every
kernel event** (KENTRY-PLAN rd8s handoff 3-4; spec side only, outside the JAtZ cone).

* `VSC E c := VE E ∧ ScInv ∧ ct = c`, `ik_vsc` / `ike_vsc`, `vsc_invF` / `vsc_invE` (rd12b's
  phases), **`ht_invFin`** (the Restart write of ct, the perform with ct kept, the post on ct),
  **`ht_fl4HandleInvocationR : HTE (VE E ∧ ScInv) (VE E)`** (rd12b's `fl4HandleInvocationR_eq` +
  `P17.syscall_r`; the fault branch by `ht_ct`), **`ht_fl4HandleSyscall`**, `ve_gets_ct`,
  **`ht_fl4HandleEvent`**, `hte_handleE`, **`ht_fl4CallKernel`**, **`ht_fl4KernelEntrySyscall`**.
* Tops: **`kcall_vb`** / **`kentry_vb`** (`VB` at every outcome from `VB ∧ ScInv` at the entry
  state: VB is taken only there), **`SInvCRBV := SInvCRB ∧ VB`** with **`boot_sinvCRBV`**,
  **`kentry_sinvCRBV`** / **`kcall_sinvCRBV`** (rd8l's premises, nothing added).
-/
import Fl4Proofs.P3.SpecInvRd8vB
import Fl4Proofs.P3.SpecInvRd8lD
open Classical

namespace Fl4Proofs.P3.SInvR.B8v
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q Fl4Proofs.P3.SInvR.B8s

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

/-! ## `VE`, `ScInv` and the current thread -/

abbrev VSC (E : ObjRef → Prop) (c : ObjRef) (s : State Unit) : Prop :=
  VE E s ∧ SInvB.ScInv s ∧ s.curThread = c

theorem ik_vsc {c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : VEK E m) (h2 : SInvB.SIK m)
    (h3 : SInv.CTK c m) : IK (VSC E c) m :=
  fun σ h x hx => ⟨h1 σ h.1 x hx, h2 σ h.2.1 x hx, h3 σ h.2.2 x hx⟩

theorem ike_vsc {c : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : VEKE E m) (h2 : SInvB.SIKE m)
    (h3 : SInv.CTKE c m) : IKE (VSC E c) m :=
  ik_vsc h1 h2 h3

set_option maxHeartbeats 4000000 in
theorem vsc_invF (c t : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    IKE (VSC E c) (A12b.invF t cptr info) := by
  have h1 : VEKE E (A12b.invF t cptr info) := by unfold A12b.invF; ve_auto
  have h2 : SInvB.SIKE (A12b.invF t cptr info) := SInvB.sik_of_sbk fun _ => by unfold A12b.invF; sb_auto
  have h3 : SInv.CTKE c (A12b.invF t cptr info) := by unfold A12b.invF; ct_auto
  exact ike_vsc h1 h2 h3

set_option maxHeartbeats 4000000 in
theorem vsc_invE (c : ObjRef) (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) :
    IKE (VSC E c) (A12b.invE fp cptr t info a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  have h1 : VEKE E (A12b.invE fp cptr t info (sl, cap, ex, buf)) := by unfold A12b.invE; ve_auto
  have h2 : SInvB.SIKE (A12b.invE fp cptr t info (sl, cap, ex, buf)) := by unfold A12b.invE; si_auto
  have h3 : SInv.CTKE c (A12b.invE fp cptr t info (sl, cap, ex, buf)) := by unfold A12b.invE; ct_auto
  exact ike_vsc h1 h2 h3

/-- The finalise phase: ct's Restart write (ct exempt as ct), the perform (ct kept), the post. -/
theorem ht_invFin (calling blocking don : Bool) (t : ObjRef) (b : Fl4Invocation) :
    HTE (VSC E t) (VE E) (A12b.invFin calling blocking don t b) := by
  unfold A12b.invFin
  refine hte_bind (R := VSC E t) ?_ (fun _ => ?_) (fun _ h => h.1)
  · unfold withoutPreemption
    refine hte_liftE ?_
    intro s hs x hx
    exact ⟨ht_ct t (ve_setThreadState_in t _) (by ct_auto) s ⟨hs.1, hs.2.2⟩ x hx, si_sts t _ s hs.2.1 x hx,
      (by ct_auto : SInv.CTK t (setThreadState (Z := Unit) t .restart)) s hs.2.2 x hx⟩
  · refine hte_bind (R := fun s => VE E s ∧ s.curThread = t) ?_ (fun _ => ?_) (fun _ h => h.1)
    · exact ht_conseq (fun s h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) (fun _ h => h)
        (hte_and (C := fun s => s.curThread = t) (ht_fl4PerformInvocation blocking calling don b) (by ct_auto))
    · unfold withoutPreemption
      exact hte_liftE (ht_ct t (by ve_auto) (by ct_auto))

/-! ## The invocation shell -/

/-- **`fl4_handle_invocation` keeps `VE E`** (from carried `ScInv`). -/
theorem ht_fl4HandleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    HTE (VS E) (VE E) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  rw [A12b.fl4HandleInvocationR_eq]
  intro σ ⟨hv, hsi⟩ y hy
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
  have hJ0 : VSC E σ.curThread w0.2 :=
    ik_vsc (by ve_auto) (by si_auto) (by ct_auto) σ ⟨hv, hsi, rfl⟩ w0 hw0
  refine SInvQ.P17.syscall_r (I := VSC E σ.curThread) (Q := fun y => VE E y.2)
    (fun v hv => vsc_invF σ.curThread _ _ _ w0.2 hJ0 v hv) ?_ ?_ ?_ ?_ y hy
  · -- the fault branch: `handle_fault ct`
    intro f s hs v hv
    show VE E v.2
    unfold NonDet.when at hv
    split at hv
    · exact ht_ct σ.curThread (ve_handleFault σ.curThread f) (by ct_auto) s ⟨hs.1, hs.2.2⟩ v hv
    · rw [Set.mem_singleton_iff.1 hv]; exact hs.1
  · -- the decode
    intro a s hs w hw
    exact vsc_invE σ.curThread _ _ _ _ a s (vsc_invF σ.curThread _ _ _ w0.2 hJ0 _ hs) w hw
  · -- the error reply
    intro e s hs v hv
    exact (show VEK E (NonDet.when calling (fl4ReplyFromKernelError (Z := Unit) rep σ.curThread
      (msgFromSyscallError e))) by ve_auto) s hs.1 v hv
  · -- the finalise phase
    intro a s b s' has hbs hs' y hy
    exact ht_invFin calling blocking don σ.curThread b s' hs' y hy

/-! ## Syscalls, events, the entry -/

/-- **Every syscall arm keeps `VE E`** (from carried `ScInv`). -/
theorem ht_fl4HandleSyscall (rep : Bool) (c : Syscall) :
    HTE (VS E) (VE E) (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    exact ht_fl4HandleInvocationR _ _ _ _ _ _
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    exact ht_fl4HandleInvocationR _ _ _ _ _ _
  case sysCall =>
    simp only [fl4HandleSyscall]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    exact ht_fl4HandleInvocationR _ _ _ _ _ _
  case sysReplyRecv =>
    simp only [fl4HandleSyscall, withoutPreemption]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    refine hte_bind (ht_fl4HandleInvocationR _ _ _ _ _ _) (fun _ => ?_) (fun _ h => h)
    exact ht_ik (ike_liftE (ve_handleRecv _ _))
  case sysNBSendRecv =>
    simp only [fl4HandleSyscall, withoutPreemption]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    refine hte_bind (ht_fl4HandleInvocationR _ _ _ _ _ _) (fun _ => ?_) (fun _ h => h)
    exact ht_ik (ike_liftE (ve_handleRecv _ _))
  case sysNBSendWait =>
    simp only [fl4HandleSyscall, withoutPreemption]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    refine hte_bind (ht_fl4HandleInvocationR _ _ _ _ _ _) (fun _ => ?_) (fun _ h => h)
    exact ht_ik (ike_liftE (ve_handleRecv _ _))
  case sysRecv =>
    simp only [fl4HandleSyscall, withoutPreemption]
    exact hte_ve (ike_liftE (ve_handleRecv _ _))
  case sysYield => exact hte_ve (by simp only [fl4HandleSyscall, withoutPreemption]; ve_auto)
  case sysNBRecv =>
    simp only [fl4HandleSyscall, withoutPreemption]
    exact hte_ve (ike_liftE (ve_handleRecv _ _))
  case sysWait =>
    simp only [fl4HandleSyscall, withoutPreemption]
    exact hte_ve (ike_liftE (ve_handleRecv _ _))
  case sysNBWait =>
    simp only [fl4HandleSyscall, withoutPreemption]
    exact hte_ve (ike_liftE (ve_handleRecv _ _))

/-- **Every kernel event keeps `VE E`** (from carried `ScInv`). -/
theorem ht_fl4HandleEvent (rep : Bool) (ev : Event) : HTE (VS E) (VE E) (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev
  case syscallEvent c =>
    simp only [fl4HandleEvent]
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun _ => ?_) (fun _ h => h.1)
    refine hte_bind (hte_liftE (ht_vs (by ve_auto) (by si_auto))) (fun r => ?_) (fun _ h => h.1)
    unfold NonDetE.whenE
    split
    · exact ht_fl4HandleSyscall rep c
    · exact hte_ve (by ve_auto)
  case interrupt =>
    rw [fl4HandleEvent_other rep _ (fun c h => by cases h)]
    simp only [handleEvent, withoutPreemption]
    exact hte_liftE (ht_conseq (fun _ h => h.1) (fun _ h => h) (ht_ik (by ve_auto)))
  case unknownSyscall n =>
    rw [fl4HandleEvent_other rep _ (fun c h => by cases h)]
    simp only [handleEvent, withoutPreemption]
    refine hte_liftE (ht_conseq (fun _ h => h.1) (fun _ h => h) (ht_ik ?_))
    refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
    unfold NonDet.when
    split
    · exact ve_gets_ct fun t => ht_ct t (by ve_auto) (by ct_auto)
    · exact ik_pure _
  case userLevelFault w1 w2 =>
    rw [fl4HandleEvent_other rep _ (fun c h => by cases h)]
    simp only [handleEvent, withoutPreemption]
    refine hte_liftE (ht_conseq (fun _ h => h.1) (fun _ h => h) (ht_ik ?_))
    refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
    unfold NonDet.when
    split
    · exact ve_gets_ct fun t => ht_ct t (by ve_auto) (by ct_auto)
    · exact ik_pure _
  case vmFaultEvent ft =>
    rw [fl4HandleEvent_other rep _ (fun c h => by cases h)]
    simp only [handleEvent, withoutPreemption]
    refine hte_liftE (ht_conseq (fun _ h => h.1) (fun _ h => h) (ht_ik ?_))
    refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
    unfold NonDet.when
    split
    · exact ve_gets_ct fun t => ht_ct t (by ve_auto) (by ct_auto)
    · exact ik_pure _
  case hypervisorEvent ft =>
    rw [fl4HandleEvent_other rep _ (fun c h => by cases h)]
    simp only [handleEvent, withoutPreemption]
    refine hte_liftE (ht_conseq (fun _ h => h.1) (fun _ h => h) (ht_ik ?_))
    refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
    unfold NonDet.when
    split
    · exact ve_gets_ct fun t => ht_ct t (by ve_auto) (by ct_auto)
    · exact ik_pure _

theorem hte_handleE {P Q : State Unit → Prop} {ε ε' α : Type} {m : NonDetE (State Unit) ε α}
    {h : ε → NonDetE (State Unit) ε' α} (hm : HTE P Q m) (hh : ∀ e, HTE Q Q (h e)) :
    HTE P Q (NonDetE.handleE m h) := by
  intro σ hσ y ⟨z, hz, hy⟩
  have hq := hm σ hσ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hq
  | error e => exact hh e s hq y hy

/-- **`call_kernel`** keeps `VE E` (from carried `ScInv`): the event (preemption errors by
`preemption_path`), FL4's timers, `schedule`, `activate_thread`. -/
theorem ht_fl4CallKernel (rep : Bool) (ev : Event) : HT (VS E) (VE E) (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ht_bind (R := VE E) ?_ fun _ =>
    ht_ik (ik_bind ve_fl4Awaken fun _ => ik_bind ve_schedule fun _ => ve_activateThread)
  exact hte_handleE (ht_fl4HandleEvent rep ev) fun _ => ht_ik (by unfold withoutPreemption; ve_auto)

/-- **The syscall entry** keeps `VE E` (from carried `ScInv`). -/
theorem ht_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    HT (VS E) (VE E) (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by unfold fl4SyscallFaultIP; ve_auto) (by unfold fl4SyscallFaultIP; si_auto)) fun _ => ?_
  exact ht_fl4CallKernel rep _

/-! ## Tops -/

/-- **`VB` at every outcome of every kernel event** from `VB` and sb2's `ScInv` at the entry. -/
theorem kcall_vb (rep : Bool) (ev : Event) {σ : State Unit} (hV : B8n.VB σ) (hI : SInvB.ScInv σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, B8n.VB y.2 :=
  fun y hy => vb_ve.2 (ht_fl4CallKernel (E := fun _ => False) rep ev σ ⟨vb_ve.1 hV, hI⟩ y hy)

/-- **`VB` at every outcome of the syscall entry** from `VB` and sb2's `ScInv` at the entry. -/
theorem kentry_vb (rep : Bool) (c : Syscall) {σ : State Unit} (hV : B8n.VB σ) (hI : SInvB.ScInv σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, B8n.VB y.2 :=
  fun y hy => vb_ve.2 (ht_fl4KernelEntrySyscall (E := fun _ => False) rep c σ ⟨vb_ve.1 hV, hI⟩ y hy)

/-- **The bundle**: rd8l's `SInvCRB` and `VB` (l4v `valid_blocked`). -/
abbrev SInvCRBV (σ : State Unit) : Prop := B8l.SInvCRB σ ∧ B8n.VB σ

/-- **`SInvCRBV` at boot** (non-vacuity). -/
theorem boot_sinvCRBV : SInvCRBV (initASt (Z := Unit)) := ⟨B8l.boot_sinvCRB, B8n.boot_vb⟩

/-- **`SInvCRBV` across the syscall entry** (exactly `kentry_sinvCRB`'s premises). -/
theorem kentry_sinvCRBV (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCRBV σ)
    (hct : σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvR.CAx r.2)
    (hI : SInvB.ScInv σ) (hL : SInvB.ScLive σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hA : SInvR.CAx σ)
    (hR : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ z ∈ (updateTimeStamp (Z := Unit) w.2).1,
      B8l.RR true z.2 c) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvCRBV y.2 :=
  fun y hy => ⟨B8l.kentry_sinvCRB hnd c h.1 hct hCA hI hL hO hA hR y hy, kentry_vb true c h.2 hI y hy⟩

/-- **`SInvCRBV` across every kernel event** (exactly `kcall_sinvCRB`'s premises). -/
theorem kcall_sinvCRBV (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCRBV σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvR.CAx r.2)
    (hI : SInvB.ScInv σ) (hL : SInvB.ScLive σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hA : SInvR.CAx σ)
    (hR : ∀ c, ev = .syscallEvent c → ∀ z ∈ (updateTimeStamp (Z := Unit) σ).1, B8l.RR rep z.2 c) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvCRBV y.2 :=
  fun y hy => ⟨B8l.kcall_sinvCRB hnd rep ev h.1 hev hCA hI hL hO hA hR y hy, kcall_vb rep ev h.2 hI y hy⟩

end

end Fl4Proofs.P3.SInvR.B8v
