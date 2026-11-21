/-
P3 (DESIGN.md §9), invariant line G1 (sl4): **`SL I [] ∧ NtfnScB` across
`fl4CallKernel`** (every event) and the tops **`kentry_scLive` / `kcall_scLive`**
(spec side only).

* `SAQ I t := SAP I [] [] False t ∧ NQ []` after the handler: its parts come from
  this line (`SLN I []`), il2 (`IL []`), nq3 (`NQ []`) and sb2 (`ScInv`, from the
  entry's `EntryOK`). The preemption path charges the budget (`sl_chargeBudget` /
  `sl_checkBudget`: a timeout fault never donates) and then handles an interrupt
  (`sli_maybeHandleInterrupt`); then `fl4_awaken` (`sli_fl4Awaken`), `schedule`,
  `activate_thread` (the SL family).
* The interrupt event (`sl_handleEvent_int`) and the fault events
  (`sl_handleEvent_other`: `handle_fault` donates only from a bound thread, read
  at its state).
* Tops: the premises are the carried invariants (`UtInv3`, `VfhAll`, `SpecGlobS ∧
  IdleOutV`, `NtfnQB ∧ EpQB`, `IfLiveT`, `ScInv`, `IdleScOutV`, `NtfnScB`,
  ScLiveT itself), l4v's `ct_active`, vi2's `CtSc` [J] for the pinned syscalls
  (lead decision) and `ScKind` (carried by SpecInvSlK* below the tops).
-/
import Fl4Proofs.P3.SpecInvSlA
import Fl4Proofs.P3.SpecInvSlE3
import Fl4Proofs.P3.SpecInvNtfnQLX
import Fl4Proofs.P3.SpecInvSbT
import Fl4Proofs.P3.SpecInvViM
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

section C
variable {I : ObjRef × ObjRef} {t : ObjRef}

/-- After the handler. -/
def SAQ (I : ObjRef × ObjRef) (t : ObjRef) (s : State Unit) : Prop := SAP I [] [] False t s ∧ NQ [] s

theorem saq_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I [] m) (h2 : ILK [] m)
    (h3 : ∀ h0, SInvB.SBK h0 m) (h4 : NBK m) (h5 : NQK [] m) : IK (SAQ I t) m :=
  fun σ h x hx => ⟨sap_ik h1 h2 h3 h4 σ h.1 x hx, h5 σ h.2 x hx⟩

macro "saq_auto" : tactic => `(tactic| exact saq_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)
  (by nq_auto))

theorem saq_sli {s : State Unit} (h : SAQ I t s) : SLI I [] [] s := ⟨⟨h.1.1.1, h.1.2.2⟩, h.1.2.1, h.2⟩

theorem saq_charge (n : Ticks) (cto : Bool) : HK (SAQ I t) (SLI I [] []) (chargeBudget (Z := Unit) n cto) :=
  fun σ h y hy => ⟨⟨sl_chargeBudget n cto σ h.1 y hy, nb_chargeBudget n cto σ h.1.2.2 y hy⟩,
    il_chargeBudget n cto σ h.1.2.1 y hy, nq_chargeBudget n cto σ h.2 y hy⟩

theorem saq_check : HK (SAQ I t) (SLI I [] []) (checkBudget (Z := Unit)) :=
  fun σ h y hy => ⟨⟨sl_checkBudget σ h.1 y hy, nb_checkBudget σ h.1.2.2 y hy⟩,
    il_checkBudget σ h.1.2.1 y hy, nq_checkBudget σ h.2 y hy⟩

theorem saq_preemptionPath : HK (SAQ I t) (SLN I []) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath
  have htail : HK (SLI I [] []) (SLN I []) (maybeHandleInterrupt (Z := Unit) true) :=
    fun s hs z hz => (sli_maybeHandleInterrupt true s hs z hz).1
  have htail' : HK (SAQ I t) (SLN I []) (maybeHandleInterrupt (Z := Unit) true) :=
    hk_pre htail fun _ h => saq_sli h
  refine hk_bind (hk_of_ik (by saq_auto)) fun ct => ?_
  refine hk_bind (hk_of_ik (by saq_auto)) fun sched => ?_
  cases sched
  · refine hk_bind (hk_of_ik (by saq_auto)) fun csc => ?_
    refine hk_bind (hk_of_ik (by saq_auto)) fun active => ?_
    cases active
    · refine hk_bind (hk_of_ik (by saq_auto)) fun _ => ?_
      first | exact htail' | exact hk_pure_bind htail'
    · refine hk_bind (hk_of_ik (by saq_auto)) fun _ => ?_
      refine hk_bind (saq_charge _ _) fun _ => ?_
      first | exact htail | exact hk_pure_bind htail
  · refine hk_bind saq_check fun _ => ?_
    first | exact htail | exact hk_pure_bind htail

/-- **`fl4CallKernel` at a state whose handler outcomes are `SLN I []`, `IL []`,
`NQ []` and `ScInv`.** -/
theorem sl_fl4CallKernel_at (t : ObjRef) {rep : Bool} {ev : Event} {σ : State Unit}
    (h1 : ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, SLN I [] y.2)
    (h2 : ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, IL [] y.2)
    (h3 : ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, NQ [] y.2)
    (h4 : ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, SInvB.ScInv y.2) :
    ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, SLN I [] y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  have hb1 : SLI I [] [] y1.2 := by
    unfold NonDetE.handleE at hy1
    obtain ⟨z, hz, hy1⟩ := hy1
    have hq : SAQ I t z.2 := ⟨⟨⟨(h1 z hz).1, h4 z hz, fun h => h.elim⟩, h2 z hz, (h1 z hz).2⟩, h3 z hz⟩
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 hy1]; exact saq_sli hq
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) hy1
      exact ⟨saq_preemptionPath s hq w hw, iln_preemptionPath s ⟨hq.1.2.1, hq.2⟩ w hw⟩
  obtain ⟨y2, hy2, hy⟩ := hy
  have hb2 := sli_fl4Awaken y1.2 hb1 y2 hy2
  refine sln_ik (?_ : SLK I [] _) (?_ : NBK _) y2.2 hb2.1 y hy
  · sl_auto
  · nb_auto

set_option maxHeartbeats 8000000 in
/-- The interrupt event. -/
theorem sl_handleEvent_int : HKE (SAQ I t) (SLN I []) (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent, withoutPreemption]
  refine hk_liftE ?_
  exact hk_bind (hk_of_ik (by saq_auto)) fun _ => hk_bind saq_check fun _ =>
    fun s hs z hz => (sli_maybeHandleInterrupt false s hs z hz).1

/-- Every event other than a syscall or an interrupt. -/
theorem sl_handleEvent_other (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) (hi : ev ≠ .interrupt) :
    HKE (SAQ I t) (SLN I []) (handleEvent (Z := Unit) ev) := by
  have hF : ∀ (m : SMonad Unit Unit) (hm : IK (SAQ I t) m) (F : ObjRef → SMonad Unit Unit)
      (hF : ∀ th s, SAQ I t s → ∀ z ∈ (F th s).1, SLN I [] z.2),
      HK (SAQ I t) (SLN I []) (do
        m
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          F thread) := by
    intro m hm F hF σ hσ y ⟨y1, h1, hy⟩
    have hb1 : SAQ I t y1.2 := hm σ hσ y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    (try dsimp only at hy)
    unfold NonDet.when at hy
    split at hy
    · rename_i hr
      have e2 : y2.2 = y1.2 := SInv.checkBudgetRestart_true h2 hr
      obtain ⟨y3, h3, hy⟩ := hy
      rw [mem_gets h3] at hy
      (try dsimp only at hy)
      rw [e2] at hy
      exact hF _ _ hb1 y hy
    · rw [Set.mem_singleton_iff.1 hy]
      exact ⟨sl_checkBudgetRestart y1.2 hb1.1 y2 h2, nb_checkBudgetRestart y1.2 hb1.1.2.2 y2 h2⟩
  have hHF : ∀ f th s, SAQ I t s → ∀ z ∈ (handleFault (Z := Unit) th f s).1, SLN I [] z.2 :=
    fun f th s hs z hz => ⟨sl_handleFault th f s hs.1 z hz, nb_handleFault th f s hs.1.2.2 z hz⟩
  have hsln : ∀ s, SAQ I t s → SLN I [] s := fun s h => ⟨h.1.1.1, h.1.2.2⟩
  cases ev with
  | syscallEvent c => exact absurd rfl (hev c)
  | interrupt => exact absurd rfl hi
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (by saq_auto) _ fun th => hHF _ th)
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (by saq_auto) _ fun th => hHF _ th)
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (by saq_auto) _ ?_)
    intro th s hs z hz
    exact hk_catch (I := SAQ I t) (Q0 := SLN I []) (hkr_of_ike (by saq_auto) hsln) (fun e => hHF e th) s hs z hz
  | hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (by saq_auto) _ ?_)
    intro th s hs z hz
    refine hsln _ ((?_ : IK (SAQ I t) _) s hs z hz)
    saq_auto

end C

/-! ## The tops -/

theorem idleP_kentry {rep : Bool} {c : Syscall} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1) : idleP y.2 = idleP σ := by
  have h1 : y.2.idleThread = σ.idleThread := SInvG.idk_fl4KernelEntrySyscall (N := σ.idleThread) rep c σ rfl y hy
  have h2 : y.2.idleSc = σ.idleSc := isk_fl4KernelEntrySyscall (N := σ.idleSc) rep c σ rfl y hy
  simp only [idleP, h1, h2]

theorem idleP_kcall {rep : Bool} {ev : Event} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1) : idleP y.2 = idleP σ := by
  have h1 : y.2.idleThread = σ.idleThread := SInvG.idk_fl4CallKernel (N := σ.idleThread) rep ev σ rfl y hy
  have h2 : y.2.idleSc = σ.idleSc := isk_fl4CallKernel (N := σ.idleSc) rep ev σ rfl y hy
  simp only [idleP, h1, h2]

/-- The carried bundle of this line. -/
def SlB (σ : State Unit) : Prop := ScLiveT (idleP σ) σ ∧ IdleScOutV σ ∧ NtfnScB σ ∧ SInvB.ScInv σ

/-- The other lines' carried facts the tops read. -/
structure SlE (σ : State Unit) : Prop where
  ut : UtInv3 σ
  vfh : VfhAll σ
  sg : SInvG.SpecGlobS σ ∧ SInvG.IdleOutV σ
  nq : NtfnQB σ ∧ EpQB σ
  il : IfLiveT σ
  kind : ScKind σ

theorem entryOK_of {σ : State Unit} (h : SlB σ) (hE : SlE σ) : SInvB.EntryOK σ :=
  ⟨h.2.2.2, hE.ut, hE.vfh, scLive_of h.1 hE.sg.2 h.2.1⟩

set_option maxHeartbeats 8000000 in
/-- A syscall event from a handler state `s` related to the entry `σe` by the shell invariant. -/
theorem sl_kcall_sysJ (rep : Bool) (c : Syscall) {σe s : State Unit} {ct : ObjRef}
    (hJ : Js (idleP σe) ct (SInvI.Pinned c) σe.interruptIrqNode σe s) (hEF : EF σe.interruptIrqNode σe)
    (hEO : SInvB.EntryOK σe) (hI1 : SInvG.IdleOutV σe) (hI : Iu ct s) (hEs : SInvB.EntryOK s) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep (.syscallEvent c)) s).1, SLN (idleP σe) [] y.2 :=
  sl_fl4CallKernel_at (I := idleP σe) σe.idleThread
    (sl_fl4HandleEvent_sys (I := idleP σe) slGap hEF hEO rfl hI1 rep c s hJ)
    (il_fl4HandleEvent_sys perfGapIL _ ct rep c s (js_ju hJ hEF))
    (nq_fl4HandleEvent_sys ct rep c s hI)
    (SInvB.sb_fl4HandleEvent SInvB.scGap rep _ s hEs)

/-- The entry's shell facts. -/
theorem sl_entryFacts (c : Syscall) {σ : State Unit} (h : SlB σ) (hE : SlE σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    Js (idleP σ) σ.curThread (SInvI.Pinned c) σ.interruptIrqNode σ σ ∧ EF σ.interruptIrqNode σ ∧
      SInvB.EntryOK σ ∧ Iu σ.curThread σ := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  have hTC : HasTC σ σ.curThread := hE.il _ x0 hx0 (live_of_active ha0)
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 hE.nq) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 hE.il) hTC
  exact ⟨⟨⟨⟨sl_cons ⟨h.1, fun _ h => by cases h⟩ (Or.inl (hasN_of_tc hTC)), h.2.2.2, fun hp => hct hp⟩, hL, h.2.2.1⟩,
      hNQ, rfl, rfl, rfl, rfl, SInvB.BR.refl _⟩, ⟨hE.ut, hE.kind, h.2.1, hE.vfh⟩, entryOK_of h hE,
    ⟨hNQ, rfl, hE.ut.1.1.1, nqDet_of_live hE.ut.1 (ifLiveB_of hE.il)⟩⟩

set_option maxHeartbeats 8000000 in
/-- **ScLiveT ∧ NtfnScB kept by every kernel event** (the current thread a TCB,
active, or idle for an interrupt). -/
theorem kcall_scLive (rep : Bool) (ev : Event) {σ : State Unit} (h : SlB σ) (hE : SlE σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScLiveT (idleP y.2) y.2 ∧ NtfnScB y.2 := by
  intro y hy
  rw [idleP_kcall hy]
  refine (fun h' : SLN (idleP σ) [] y.2 => ⟨h'.1.1, h'.2⟩) ?_
  obtain ⟨x0, hx0, ha0⟩ := ha
  have hNQ : NQ [σ.curThread] σ := by
    refine nq_cons ((nq_nil_iff σ).2 hE.nq) fun x hx => ?_
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  have hEO := entryOK_of h hE
  have hQ : SAQ (idleP σ) σ.idleThread σ :=
    ⟨⟨⟨⟨h.1, fun _ h => by cases h⟩, h.2.2.2, fun h => h.elim⟩, (il_nil_iff σ).2 hE.il, h.2.2.1⟩,
      (nq_nil_iff σ).2 hE.nq⟩
  have hS4 := SInvB.sb_fl4HandleEvent SInvB.scGap rep ev σ hEO
  by_cases hint : ev = .interrupt
  · subst hint
    exact sl_fl4CallKernel_at (I := idleP σ) σ.idleThread
      (by simp only [fl4HandleEvent]; exact sl_handleEvent_int σ hQ)
      (by simp only [fl4HandleEvent]; exact il_handleEvent_int σ ⟨(il_nil_iff σ).2 hE.il, (nq_nil_iff σ).2 hE.nq⟩)
      (nq_fl4HandleEvent_other σ.curThread rep .interrupt (fun c e => by cases e) σ ⟨hNQ, rfl⟩) hS4 y hy
  have hact : activeSt x0.tcbState := by
    rcases ha0 with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hint
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    obtain ⟨hJ, hEF, hEO', hI⟩ := sl_entryFacts c h hE ⟨x0, hx0, hact⟩ (hct c rfl)
    exact sl_kcall_sysJ rep c hJ hEF hEO' hE.sg.2 hI hEO' y hy
  · have hev : ∀ c, ev ≠ .syscallEvent c := fun c e => hs ⟨c, e⟩
    have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 hE.il) (hE.il _ x0 hx0 (live_of_active hact))
    exact sl_fl4CallKernel_at (I := idleP σ) σ.idleThread
      (by rw [fl4HandleEvent_other rep ev hev]; exact sl_handleEvent_other ev hev hint σ hQ)
      (by rw [fl4HandleEvent_other rep ev hev]
          exact il_handleEvent_other σ.curThread ev hev hint σ ⟨⟨hL, nq_weak_nil _ hNQ⟩, rfl⟩)
      (nq_fl4HandleEvent_other σ.curThread rep ev hev σ ⟨hNQ, rfl⟩) hS4 y hy

set_option maxHeartbeats 8000000 in
/-- **ScLiveT ∧ NtfnScB kept by the syscall entry.** -/
theorem kentry_scLive (c : Syscall) {σ : State Unit} (h : SlB σ) (hE : SlE σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScLiveT (idleP y.2) y.2 ∧ NtfnScB y.2 := by
  intro y hy
  rw [idleP_kentry hy]
  refine (fun h' : SLN (idleP σ) [] y.2 => ⟨h'.1.1, h'.2⟩) ?_
  obtain ⟨x0, hx0, ha0⟩ := ha
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨hJ, hEF, hEO, hI⟩ := sl_entryFacts c h hE ⟨x0, hx0, ha0⟩ hct
  have hJ2 : Js (idleP σ) σ.curThread (SInvI.Pinned c) σ.interruptIrqNode σ y2.2 := by
    refine (?_ : IK (Js (idleP σ) σ.curThread (SInvI.Pinned c) σ.interruptIrqNode σ) _) σ hJ y2 h2
    js_auto
  have hI2 : Iu σ.curThread y2.2 := by
    refine (?_ : IK (Iu σ.curThread) _) σ hI y2 h2
    iu_auto
  have hE2 : SInvB.EntryOK y2.2 := SInvB.entryOK_keep hEO (SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) h2)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) h2)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl y2 h2)
    ((show IK VfhAll (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)) σ hE.vfh y2 h2)
  exact sl_kcall_sysJ true c hJ2 hEF hEO hE.sg.2 hI2 hE2 y hy

/-- **The line's bundle `ScLiveT ∧ IdleScOutV ∧ NtfnScB ∧ ScInv` kept by the syscall entry.** -/
theorem kentry_slB (c : Syscall) {σ : State Unit} (h : SlB σ) (hE : SlE σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SlB y.2 := fun y hy =>
  ⟨(kentry_scLive c h hE ha hct y hy).1, kentry_idleScOutV c hE.sg.1 hE.sg.2 hE.ut h.2.1 y hy,
    (kentry_scLive c h hE ha hct y hy).2,
    SInvB.kentry_scInv c h.2.2.2 hE.ut hE.vfh (scLive_of h.1 hE.sg.2 h.2.1) y hy⟩

/-- **The line's bundle kept by every kernel event.** -/
theorem kcall_slB (rep : Bool) (ev : Event) {σ : State Unit} (h : SlB σ) (hE : SlE σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SlB y.2 := fun y hy =>
  ⟨(kcall_scLive rep ev h hE ha hct y hy).1, kcall_idleScOutV rep ev hE.sg.1 hE.sg.2 hE.ut h.2.1 y hy,
    (kcall_scLive rep ev h hE ha hct y hy).2,
    SInvB.kcall_scInv rep ev h.2.2.2 hE.ut hE.vfh (scLive_of h.1 hE.sg.2 h.2.1) y hy⟩

end

end Fl4Proofs.P3.SInvL
