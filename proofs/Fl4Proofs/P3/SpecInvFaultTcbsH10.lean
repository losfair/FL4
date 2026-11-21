/-
P3 (DESIGN.md §9), invariant line G1 (ft3): **FaultTcbsS (with NQB) kept by
the syscall entry and by every kernel event** (spec side only; l4v
`fault_tcbs_valid_states`, with the `valid_ntfn` part NQB).

* Events: a syscall or user fault runs from `B [ct] [ct] [ct] (· = ct)`
  (`checkBudgetRestart` first: a `true` result left the state unchanged, a
  `false` one ends with `B [] [] [ct]`); an interrupt from `B [] [] [ct]`
  (the current thread may be idle). `ok` results end in `B [] [] [] (· = ct)`,
  errors (preemption, from `perform_invocation`) in `B [] [] [ct] (· = ct)`,
  which `preemption_path` needs (`ct ∈ K` for the charge).
* `fl4CallKernel`: the handler, `preemption_path` on an error, `fl4Awaken`,
  `schedule` (the frame at `C := ⊤`), `activate_thread` (`E = []`); the end
  is `B [] [] [] ⊤ ↔ FaultTcbsS ∧ NQB`.
* **[J] `CtEntry σ`** (per entry, l4v `ct_active` + `valid_ntfn`'s queue
  states): the current thread is active (Running / Restart) and in no
  notification queue. True at every syscall / user-fault entry from user mode
  (the thread that trapped runs). For interrupts `CtEntryI`: active or idle,
  in no queue (l4v `ct_running or ct_idle`). Carried invariant that would
  discharge it at G4: `ct_active` from the J layer's `JEntryAt` (ct Running),
  and "ct in no notification queue" = `JAtZ`'s `not_in_ntfnQueue` / CtNQR
  (invC2); see KENTRY-PLAN ft3.
* Tops: `kentry_faultTcbsS`, `kcall_faultTcbsS`, and the weak form
  (`kentry_faultTcbs`, `kcall_faultTcbs`: FaultTcbs carried as FaultTcbsS ∧
  NQB). Boot: `boot_B` / `boot_faultTcbsS` / `boot_nqb`.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH9
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Result-dependent posts with separate error posts -/

section G
variable {P Q0 Qe : State Unit → Prop} {ε : Type}

theorem hkrG_bind {R : State Unit → Prop} {α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : HKE P R m) (hg : ∀ a, HKR R (okErr Q0 Qe) (g a))
    (hRe : ∀ s, R s → Qe s) : HKR P (okErr Q0 Qe) (m >>= g) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hg a s (hm σ hσ _ hz) y hy
  · exact hRe _ (hm σ hσ _ hz)

theorem hkrG_liftE {α : Type} {m : NonDet (State Unit) α} (h : HK P Q0 m) :
    HKR P (okErr Q0 Qe) (NonDetE.liftE (ε := ε) m) := by
  intro σ hσ y hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact h σ hσ x hx

theorem hkrG_of_hke {R : State Unit → Prop} {α : Type} {m : NonDetE (State Unit) ε α} (h : HKE P R m)
    (h0 : ∀ s, R s → Q0 s) (he : ∀ s, R s → Qe s) : HKR P (okErr Q0 Qe) m := by
  intro σ hσ y hy
  have := h σ hσ y hy
  obtain ⟨r, s⟩ := y
  cases r with
  | ok a => exact h0 s this
  | error e => exact he s this

theorem hkr_of_ike {I : State Unit → Prop} {α : Type} {m : NonDetE (State Unit) ε α} (h : IKE I m)
    (h0 : ∀ s, I s → Q0 s) : HKR I (okErr Q0 I) m :=
  hkrG_of_hke (fun σ hσ y hy => h σ hσ y hy) h0 fun _ h => h

end G

/-! ## `handle_syscall` -/

theorem b_q1_of_filter {ct : ObjRef} {σ : State Unit} (h : B ([ct].filter (· ≠ ct)) [] [ct] (· = ct) σ) :
    B [] [] [ct] (· = ct) σ :=
  b_mono h (fun _ h => by simp at h) (fun _ h => h) id

set_option maxHeartbeats 4000000 in
theorem b_fl4HandleSyscall (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKR (B [ct] [ct] [ct] (· = ct)) (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct)))
      (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef), HKR (B [ct] [ct] [ct] (· = ct))
      (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct))) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => hkrG_of_hke (b_fl4HandleInvocationR ct rep cl bl dn fp cptr)
      (fun s h => h.elim (fun h => q1_q0 (i0_q1 h)) (fun h => q1_q0 h.2)) (fun s h => h.elim i0_q1 (fun h => h.2))
  have hRecv : ∀ b r, HKR (B [ct] [ct] [ct] (· = ct)) (ε := Unit) (α := Unit)
      (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct))) (withoutPreemption (Z := Unit) (handleRecv b r)) :=
    fun b r => hkrG_liftE (b_handleRecv ct b r)
  have hRR : ∀ (m : SMonad Unit CapRef) (hm : GF (· = ct) m) (bl : Bool),
      HKR (B [ct] [ct] [ct] (· = ct)) (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct))) (do
        let cp ← withoutPreemption (Z := Unit) m
        fl4HandleInvocationR rep false false true true cp
        withoutPreemption <| handleRecv true bl) := by
    intro m hm bl
    refine hkrG_bind (R := B [ct] [ct] [ct] (· = ct)) (hk_liftE (hk_of_ik (b_of_gf hm))) (fun cp => ?_)
      (fun s h => i0_q1 h)
    refine hkrG_bind (R := fun s => B [ct] [ct] [ct] (· = ct) s ∨ (false = true ∧ B [] [] [ct] (· = ct) s))
      (b_fl4HandleInvocationR ct rep false false true true cp) (fun _ => ?_) (fun s h => h.elim i0_q1 (fun h => h.2))
    exact hkrG_liftE (hk_pre (b_handleRecv ct true bl) fun s h => h.resolve_right (by simp))
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    refine hkrG_bind (R := B [ct] [ct] [ct] (· = ct)) (hk_liftE (hk_of_ik (b_of_gf fun F S => ?_)))
      (fun cptr => hInv _ _ _ _ cptr) (fun s h => i0_q1 h)
    fg_auto
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    refine hkrG_bind (R := B [ct] [ct] [ct] (· = ct)) (hk_liftE (hk_of_ik (b_of_gf fun F S => ?_)))
      (fun cptr => hInv _ _ _ _ cptr) (fun s h => i0_q1 h)
    fg_auto
  case sysCall =>
    simp only [fl4HandleSyscall]
    refine hkrG_bind (R := B [ct] [ct] [ct] (· = ct)) (hk_liftE (hk_of_ik (b_of_gf fun F S => ?_)))
      (fun cptr => hInv _ _ _ _ cptr) (fun s h => i0_q1 h)
    fg_auto
  case sysYield =>
    simp only [fl4HandleSyscall]
    exact hkrG_liftE fun s hs z hz => q1_q0 (b_handleYield ct s (i0_q1 hs) z hz)
  case sysReplyRecv =>
    simp only [fl4HandleSyscall]
    refine hRR _ (fun F S => ?_) true
    fg_auto
  case sysNBSendRecv =>
    simp only [fl4HandleSyscall]
    refine hRR _ (fun F S => ?_) true
    fg_auto
  case sysNBSendWait =>
    simp only [fl4HandleSyscall]
    refine hRR _ (fun F S => ?_) false
    fg_auto
  all_goals
    simp only [fl4HandleSyscall]
    exact hRecv _ _

/-! ## The events -/

theorem b_fl4HandleEvent_sys (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKR (B [ct] [ct] [ct] (· = ct)) (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct)))
      (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hkrG_bind (R := B [ct] [ct] [ct] (· = ct)) (hk_liftE (hk_of_ik (b_of_gf fun F S => ?_)))
    (fun _ => ?_) (fun s h => i0_q1 h)
  · fg_auto
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    obtain ⟨e1, hb1⟩ := b_checkBudgetRestart (L := [ct]) (E := []) (K := [ct]) ct (List.mem_singleton_self _)
      (List.mem_singleton_self _) (by simp) hσ hw
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [e1 hr] at hy
      exact b_fl4HandleSyscall ct rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]
      exact q1_q0 (b_q1_of_filter hb1)
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-- A user-fault event: the budget check, then `F ct` on the current thread. -/
theorem b_evShell (ct : ObjRef) (F : ObjRef → SMonad Unit Unit)
    (hF : HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [ct] (· = ct)) (F ct)) :
    HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [] (· = ct)) (do
      updateTimeStamp (Z := Unit)
      let restart ← checkBudgetRestart
      NonDet.when restart <| do
        let thread ← NonDet.gets fun s : State Unit => s.curThread
        F thread) := by
  intro σ hσ y ⟨y1, h1, hy⟩
  have hb1 := (b_of_gf (fun _ _ => by fg_auto) : BK [ct] [ct] [ct] (· = ct) (updateTimeStamp (Z := Unit))) σ hσ y1 h1
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, hb2⟩ := b_checkBudgetRestart (L := [ct]) (E := []) (K := [ct]) ct (List.mem_singleton_self _)
    (List.mem_singleton_self _) (by simp) hb1 h2
  (try dsimp only at hy)
  unfold NonDet.when at hy
  split at hy
  · rename_i hr
    rw [e2 hr] at hy
    obtain ⟨y3, h3, hy⟩ := hy
    rw [mem_gets h3] at hy
    have hc : y1.2.curThread = ct := hb1.1.2
    (try dsimp only at hy)
    rw [hc] at hy
    exact q1_q0 (hF _ hb1 y hy)
  · rw [Set.mem_singleton_iff.1 hy]
    exact q1_q0 (b_q1_of_filter hb2)

theorem b_handleFault_q1 (ct : ObjRef) (f : Fault) :
    HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [ct] (· = ct)) (handleFault (Z := Unit) ct f) :=
  fun s hs z hz => b_q1_of_filter (b_handleFault (L := [ct]) (E := []) (K := [ct]) (C := (· = ct)) ct f
    (List.mem_singleton_self _) s hs z hz)

set_option maxHeartbeats 4000000 in
/-- Every event but the interrupt, from `B [ct] [ct] [ct] (· = ct)`. -/
theorem b_fl4HandleEvent_user (ct : ObjRef) (rep : Bool) (ev : Event) (hev : ev ≠ .interrupt) :
    HKR (B [ct] [ct] [ct] (· = ct)) (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct)))
      (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev
  case syscallEvent c => exact b_fl4HandleEvent_sys ct rep c
  case interrupt => exact absurd rfl hev
  case unknownSyscall n =>
    simp only [fl4HandleEvent, handleEvent, withoutPreemption]
    exact hkrG_liftE (b_evShell ct _ (b_handleFault_q1 ct _))
  case userLevelFault w1 w2 =>
    simp only [fl4HandleEvent, handleEvent, withoutPreemption]
    exact hkrG_liftE (b_evShell ct _ (b_handleFault_q1 ct _))
  case vmFaultEvent ft =>
    simp only [fl4HandleEvent, handleEvent, withoutPreemption]
    refine hkrG_liftE (b_evShell ct _ ?_)
    refine hk_catch (I := B [ct] [ct] [ct] (· = ct)) (hkr_of_ike (b_of_gfE fun F S => ?_) fun s h => i0_q1 h)
      fun e => b_handleFault_q1 ct e
    fg_auto
  case hypervisorEvent ht =>
    simp only [fl4HandleEvent, handleEvent, withoutPreemption]
    refine hkrG_liftE (b_evShell ct _ (hk_post (hk_of_ik (b_of_gf fun F S => ?_)) fun s h => i0_q1 h))
    fg_auto

/-- The interrupt event, from `B [] [] [ct] (· = ct)`. -/
theorem b_fl4HandleEvent_irq (ct : ObjRef) (rep : Bool) :
    HKR (B [] [] [ct] (· = ct)) (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct)))
      (fl4HandleEvent (Z := Unit) rep .interrupt) := by
  simp only [fl4HandleEvent, handleEvent, withoutPreemption]
  refine hkrG_liftE (hk_post (hk_of_ik ?_) fun s h => q1_q0 h)
  b_autoE

/-! ## The kernel call -/

theorem b_fl4CallKernel (ct : ObjRef) (rep : Bool) (ev : Event) {P : State Unit → Prop}
    (h : HKR P (okErr (B [] [] [] (· = ct)) (B [] [] [ct] (· = ct))) (fl4HandleEvent (Z := Unit) rep ev)) :
    HK P (B [] [] [] (fun _ => True)) (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  intro σ hσ y ⟨y1, h1, hy⟩
  have hq : B [] [] [] (· = ct) y1.2 := by
    unfold NonDetE.handleE at h1
    rw [ExceptT.run_mk] at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' := h σ hσ z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) h1
      exact q1_q0 (b_preemptionPath ct s hz' w hw)
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 := b_fl4Awaken _ hq y2 h2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 := b_of_gf (L := []) (E := []) (K := []) (C := fun _ => True) (fun _ _ => fg_schedule) _
    (b_mono hb2 (fun _ h => h) (fun _ h => h) (fun _ => trivial)) y3 h3
  exact b_activateThread _ hb3 y hy

/-! ## The entry premise and the tops -/

/-- **[J] CtEntry** (l4v `ct_active` and `valid_ntfn`'s queue states): the
current thread is active and in no notification queue. -/
def CtEntry (σ : State Unit) : Prop :=
  (∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) ∧ ¬ queued σ σ.curThread

/-- **[J] CtEntryI** (interrupt entry; l4v `ct_running s ∨ ct_idle s`): the
current thread is active or idle and in no notification queue. -/
def CtEntryI (σ : State Unit) : Prop :=
  (∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ x.tcbState = .idleThreadState) ∧
    ¬ queued σ σ.curThread

/-- The entry premise of an event. -/
def CtEntryEv (ev : Event) (σ : State Unit) : Prop :=
  if ev = .interrupt then CtEntryI σ else CtEntry σ

theorem b_consK {L E K : List ObjRef} {C : ObjRef → Prop} {σ : State Unit} (h : B L E K C σ) {t : ObjRef}
    (hq : ¬ queued σ t) (hn : ∀ x, σ.kheap t = some (.tcb x) → ¬ isBoN x.tcbState) : B L E (t :: K) C σ := by
  refine ⟨h.1, h.2.1, fun u hu => ?_⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ⟨hq, hn⟩
  · exact h.2.2 u hu

theorem b_entry_of {σ : State Unit} (h : FaultTcbsS σ ∧ NQB σ) (hJ : CtEntry σ) :
    B [σ.curThread] [σ.curThread] [σ.curThread] (· = σ.curThread) σ := by
  have h0 : B [] [] [] (· = σ.curThread) σ := b_mono ((b_nil_iff σ).2 h) (fun _ h => h) (fun _ h => h) fun _ => rfl
  have hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none := by
    intro x hx
    by_contra hf
    have h1 := h.1 _ x hx hf
    have h2 := hJ.1 x hx
    revert h1 h2; cases x.tcbState <;> simp [faultTcbSt, activeSt]
  refine b_consK (b_addE (b_cons h0 hnf) fun x hx => Or.inl (hJ.1 x hx)) hJ.2 fun x hx => ?_
  have := hJ.1 x hx
  revert this; cases x.tcbState <;> simp [activeSt, isBoN]

theorem b_entryI_of {σ : State Unit} (h : FaultTcbsS σ ∧ NQB σ) (hJ : CtEntryI σ) :
    B [] [] [σ.curThread] (· = σ.curThread) σ := by
  have h0 : B [] [] [] (· = σ.curThread) σ := b_mono ((b_nil_iff σ).2 h) (fun _ h => h) (fun _ h => h) fun _ => rfl
  refine b_consK h0 hJ.2 fun x hx => ?_
  rcases hJ.1 x hx with h1 | h1
  · revert h1; cases x.tcbState <;> simp [activeSt, isBoN]
  · rw [h1]; exact fun h => h

/-- **FaultTcbsS and NQB kept by every kernel event** (`fl4CallKernel rep ev`),
under the per-entry premise `CtEntryEv ev` [J]. -/
theorem kcall_faultTcbsS (rep : Bool) (ev : Event) {σ : State Unit} (hJ : CtEntryEv ev σ)
    (h : FaultTcbsS σ ∧ NQB σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, FaultTcbsS y.2 ∧ NQB y.2 := by
  intro y hy
  refine (b_nil_iff _).1 ?_
  unfold CtEntryEv at hJ
  split at hJ
  · rename_i hev
    subst hev
    exact b_fl4CallKernel σ.curThread rep _ (b_fl4HandleEvent_irq σ.curThread rep) σ (b_entryI_of h hJ) y hy
  · rename_i hev
    exact b_fl4CallKernel σ.curThread rep ev (b_fl4HandleEvent_user σ.curThread rep ev hev) σ (b_entry_of h hJ) y hy

/-- **FaultTcbsS and NQB kept by the syscall entry** (`fl4KernelEntrySyscall`),
under the entry premise `CtEntry` [J]. -/
theorem kentry_faultTcbsS (rep : Bool) (c : Syscall) {σ : State Unit} (hJ : CtEntry σ)
    (h : FaultTcbsS σ ∧ NQB σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, FaultTcbsS y.2 ∧ NQB y.2 := by
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hI := b_entry_of h hJ
  have hb2 := (b_of_gf (fun _ _ => by fg_auto) : BK [σ.curThread] [σ.curThread] [σ.curThread] (· = σ.curThread)
    (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ hI y2 h2
  exact (b_nil_iff _).1 (b_fl4CallKernel σ.curThread rep _ (b_fl4HandleEvent_sys σ.curThread rep c) y2.2 hb2 y hy)

/-- **FaultTcbs (the slice the top consumes) after the syscall entry**, carried
as FaultTcbsS ∧ NQB. -/
theorem kentry_faultTcbs (rep : Bool) (c : Syscall) {σ : State Unit} (hJ : CtEntry σ)
    (h : FaultTcbsS σ ∧ NQB σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, FaultTcbs y.2 :=
  fun y hy => (kentry_faultTcbsS rep c hJ h y hy).1.weak

/-- **FaultTcbs after every kernel event**, carried as FaultTcbsS ∧ NQB. -/
theorem kcall_faultTcbs (rep : Bool) (ev : Event) {σ : State Unit} (hJ : CtEntryEv ev σ)
    (h : FaultTcbsS σ ∧ NQB σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, FaultTcbs y.2 :=
  fun y hy => (kcall_faultTcbsS rep ev hJ h y hy).1.weak

/-- The carried pair at boot. -/
theorem boot_faultTcbsS_nqb : FaultTcbsS (initASt (Z := Unit)) ∧ NQB (initASt (Z := Unit)) :=
  ⟨boot_faultTcbsS, boot_nqb⟩

end

end Fl4Proofs.P3.SInv
