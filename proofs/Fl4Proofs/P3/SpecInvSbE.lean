/-
P3 (DESIGN.md §9), invariant line G1 (sb1, sb2): **`ScInv` (ScSym ∧ RNE) across
the syscall entry and every kernel event, reduced to the decode-dependent
performs** (spec side only; imports SpecInvSbX2 and the untyped line's
SpecInvUtO6 for the cap view `uV` and its frames).

* `EntryOK σ`: `ScInv σ` with the facts the remaining performs need from the
  entry state: `UtInv3` (ut8, carried), `VfhAll` (vfh3, carried) and
  **`ScLive` [J]** (l4v `if_live_then_nonz_cap` at bound TCBs and SCs — l4v's
  `live` holds for a TCB with `tcb_sched_context ≠ None` and for an SC with
  `sc_tcb ≠ None` — and `valid_global_refs` for the idle pair: a bound TCB or
  SC is named by some cap, or lies outside every cap's range). With UtInv3's
  UtCh it gives the reset's / MakePool's detype facts (sb2: it replaces sb1's
  non-inductive `DetypeScOK`). Not carried yet (handoff, KENTRY-PLAN sb2).
* `GapInv`: the performs reading decode facts: untyped (retype freshness from
  UtInv3, reset detype from ScLive), arch (MakePool: detype + retype), SC bind,
  TCB `threadControlSched` (its bind, after `install_tcb_cap` of the fault
  handler slot: VfhAll). SchedControl configure is decode-free (sb2:
  `si_invokeSchedControlConfigureFlags`).
* **`ScGap`** (the obligation discharged by `scGap`, SpecInvSbT): those performs
  keep `ScInv` at a state related to an `EntryOK` state by the cap view and the
  binding frame, for an invocation decoded (`DecFrom`) from such a state (l4v
  `invoke_untyped_invs`, `perform_asid_control_invocation_invs`,
  `invoke_sched_context_invs`, `invoke_tcb_invs`).
* The shell `sb_handleInvocationR` (every other perform by the SIK family), the
  syscall paths, the events, and the tops `kentry_scInv_of` / `kcall_scInv_of`.
-/
import Fl4Proofs.P3.SpecInvSbN
import Fl4Proofs.P3.SpecInvUtO6
import Fl4Proofs.P3.SpecInvVfhAll
import Fl4Proofs.P3.SpecInvOffReady
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The entry facts and the gap -/

/-- A bound TCB or SC. -/
def Bound (b : BV) : Prop := ∃ o, b = .t (some o) ∨ b = .s (some o)

/-- **ScLive [J]** (l4v `if_live_then_nonz_cap` at bound TCBs / SCs, and
`valid_global_refs` for the idle thread and idle SC): a bound TCB or SC is named
by a cap, or lies outside every cap's range. -/
def ScLive (σ : State Unit) : Prop :=
  ∀ p, Bound (bv σ.kheap p) →
    (∃ s c, SInvU.capAt σ s = some c ∧ p ∈ objRefs c) ∨ (∀ s c, SInvU.capAt σ s = some c → p ∉ SInvU.covR c)

/-- What the entry state carries. -/
structure EntryOK (σ : State Unit) : Prop where
  sc : ScInv σ
  ut : SInvU.UtInv3 σ
  vfh : VfhAll σ
  live : ScLive σ

/-- Same cap view and binding frame from `σe`. -/
def Rel (σe s : State Unit) : Prop := SInvU.uV s = SInvU.uV σe ∧ BR σe.kheap s.kheap

theorem Rel.bv {σe s : State Unit} (h : Rel σe s) : bv s.kheap = bv σe.kheap := bv_of_br h.2

theorem Rel.capAt {σe s : State Unit} (h : Rel σe s) : SInvU.capAt s = SInvU.capAt σe :=
  congrArg (fun w : SInvU.UView => w.2.1) h.1

/-- The performs left to `ScGap`. -/
def GapInv : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeArchObject _ => True
  | .invokeSchedContext (.invokeSchedContextBind _ _) => True
  | .invokeTCB (.threadControlSched _ _ _ _ _ _) => True
  | _ => False

/-- `inv` is an `.ok` decode outcome from a state related to `σe`, of a cap held in
its slot with extra caps held in theirs (ut7's `DecodedFrom`, with the binding frame). -/
def DecFrom (σe : State Unit) (inv : Fl4Invocation) : Prop :=
  ∃ (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ0 s0 : State Unit),
    Rel σe σ0 ∧ SInvU.capAt σ0 sl = some cap ∧
    (∀ p ∈ ex, SInvU.capAt σ0 p.2 = some p.1 ∧ SInvU.DestRefV (SInvU.uV σ0) p.2) ∧
    (Except.ok inv, s0) ∈ ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ0).1

/-- **The gap obligation** (see the module docstring; discharged by `scGap`). -/
def ScGap : Prop :=
  ∀ (blk call don : Bool) (inv : Fl4Invocation) (σe σ : State Unit), GapInv inv → EntryOK σe →
    DecFrom σe inv → ScInv σ → Rel σe σ →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, ScInv y.2

theorem scLive_keep {σ σ' : State Unit} (h : ScLive σ) (hu : SInvU.uV σ' = SInvU.uV σ)
    (hb : BR σ.kheap σ'.kheap) : ScLive σ' := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := congrArg (fun w : SInvU.UView => w.2.1) hu
  intro p hp
  rw [bv_of_br hb] at hp
  rw [hc]
  exact h p hp

theorem entryOK_keep {σ σ' : State Unit} (hE : EntryOK σ) (hu : SInvU.uV σ' = SInvU.uV σ)
    (hb : BR σ.kheap σ'.kheap) (hn : σ'.interruptIrqNode = σ.interruptIrqNode) (hv : VfhAll σ') : EntryOK σ' := by
  refine ⟨scInv_of_br hE.sc hb, ⟨?_, ?_⟩, hv, scLive_keep hE.live hu hb⟩
  · show SInvU.UtInv''V (SInvU.uV σ'); rw [hu]; exact hE.ut.1
  · show SInvU.IrqOutV σ'.interruptIrqNode (SInvU.uV σ'); rw [hu, hn]; exact hE.ut.2

/-! ## The performs outside the gap -/

/-- Every perform outside the gap keeps `ScInv` (one case per constructor). -/
theorem si_performNG (blk call don : Bool) (inv : Fl4Invocation) (h : ¬ GapInv inv) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeUntyped i => exact absurd trivial h
  | invokeArchObject i => exact absurd trivial h
  | invokeEndpoint ep b g gr => exact si_pfEndpoint blk call don ep b g gr
  | invokeNotification n b => exact si_pfNtfn blk call don n b
  | invokeReply r g => exact si_pfReply blk call don r g
  | invokeTCB i => exact si_pfTcb blk call don i fun a b c d e f hi => h (by subst hi; trivial)
  | invokeFl4TCB i => exact si_pfFl4Tcb blk call don i
  | invokeDomain i => exact si_pfDomain blk call don i
  | invokeSchedContext i => exact si_pfSc blk call don i fun c cap hi => h (by subst hi; trivial)
  | invokeSchedControl i => exact si_pfSchedControl blk call don i
  | invokeCNode i => exact si_pfCnode blk call don i
  | invokeIRQControl i => exact si_pfIrqC blk call don i
  | invokeIRQHandler i => exact si_pfIrqH blk call don i

/-! ## The shell -/

/-- Kept from a state related to `σe`. -/
def SIKR (σe : State Unit) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, ScInv σ → Rel σe σ → ∀ y ∈ (m.run σ).1, ScInv y.2

theorem rel_step {σe s : State Unit} {α : Type} {m : NonDet (State Unit) α} (hu : ∀ v, SInvU.UK v m)
    (hs : ∀ h0, SBK h0 m) (hR : Rel σe s) {x : α × State Unit} (hx : x ∈ (m s).1) : Rel σe x.2 :=
  ⟨(hu _ s rfl x hx).trans hR.1, hR.2.trans (br_mem_of_sbk hs hx)⟩

theorem sikr_bind {σe : State Unit} {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hu : ∀ v, SInvU.UKE v m) (hs : ∀ h0, SBKE h0 m) (hg : ∀ a, SIKR σe (g a)) : SIKR σe (m >>= g) := by
  intro σ hI hR y hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · exact hg a z.2 (scInv_of_br hI (br_mem_of_sbk hs hz)) (rel_step hu hs hR hz) y hy
  · exact scInv_of_br hI (br_mem_of_sbk hs hz)

theorem sikr_bind' {σe : State Unit} {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : SIKR σe m) (hg : ∀ a, SIKE (g a)) : SIKR σe (m >>= g) := by
  intro σ hI hR y hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · exact hg a z.2 (hm σ hI hR z hz) y hy
  · exact hm σ hI hR z hz

theorem sikr_of_sik {σe : State Unit} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : SIKE m) : SIKR σe m :=
  fun σ hI _ y hy => h σ hI y hy

/-- **The invocation keeps `ScInv`** (given `ScGap`), from a state related to an `EntryOK` state. -/
theorem sb_handleInvocationR (hG : ScGap) (rep calling blocking don fp : Bool) (cptr : CapRef) (σe : State Unit)
    (hE : EntryOK σe) : SIKR σe (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine sikr_bind (fun _ => by uk_auto) (fun _ => by sb_auto) fun thread =>
    sikr_bind (fun _ => by uk_auto) (fun _ => by sb_auto) fun info => ?_
  intro σ hI hR y hy
  have hFu : ∀ v, SInvU.UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hFs : ∀ h0, SBKE h0 (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by sb_auto
  have hOk : SInvU.OkV (SInvU.uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (SInvU.uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (SInvU.uV σ).2.1 p.2 = some p.1 ∧
        SInvU.DestRefV (SInvU.uV σ) p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine SInvU.okv_bind (fun _ => SInvU.uk_capFaultOnFailure _ _ _ (SInvU.uk_lookupCapAndSlot _ _))
      (SInvU.okv_capFaultOnFailure _ _ (SInvU.okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine SInvU.okv_bind_uk (fun _ => ike_liftE (SInvU.uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine SInvU.okv_bind (fun _ => SInvU.uk_lookupExtraCaps _ _ _) (SInvU.okv_lookupExtraCapsN _ _ _)
      fun ex hex => SInvU.okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine SInvU.syscall_postU (I := fun s => ScInv s ∧ Rel σe s) (Q := ScInv)
    (fun w hw => ⟨scInv_of_br hI (br_mem_of_sbk hFs hw), rel_step hFu hFs hR hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show SIK (NonDet.when blocking (handleFault (Z := Unit) thread f)) by si_auto) s hs.1 v hv
  · intro a s has w hw
    have hs : ScInv s ∧ Rel σe s := ⟨scInv_of_br hI (br_mem_of_sbk hFs has), rel_step hFu hFs hR has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hEu : ∀ v, SInvU.UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEs : ∀ h0, SBKE h0 (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by sb_auto
    exact ⟨scInv_of_br hs.1 (br_mem_of_sbk hEs hw), rel_step hEu hEs hs.2 hw⟩
  · intro e s hs v hv
    exact (sik_of_sbk fun _ => by sb_auto) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hs : Rel σe s := rel_step hFu hFs hR has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := SInvU.mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hx0R : Rel σe x0.2 :=
      rel_step (fun _ => by uk_auto : ∀ v, SInvU.UK v (getMrs (Z := Unit) thread buf info))
        (fun _ => by sb_auto) hs hx0
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    have hvx : SInvU.uV x0.2 = SInvU.uV σ := hx0R.1.trans hR.1.symm
    have hcx : SInvU.capAt x0.2 = SInvU.capAt σ := congrArg (fun w : SInvU.UView => w.2.1) hvx
    have hDF : DecFrom σe b := ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hx0R,
      by rw [hcx]; exact hc, fun p hp => ⟨by rw [hcx]; exact (hex p hp).1, by rw [hvx]; exact (hex p hp).2⟩, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hzR : Rel σe z.2 := rel_step (m := ExceptT.run (withoutPreemption (Z := Unit) (setThreadState thread .restart)))
        (fun _ => by uk_auto) (fun _ => by sb_auto) hI'.2 hz
      have hzI : ScInv z.2 := scInv_of_br hI'.1
        (br_mem_of_sbk (m := ExceptT.run (withoutPreemption (Z := Unit) (setThreadState thread .restart)))
          (fun _ => by sb_auto) hz)
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hP : ∀ w ∈ ((fl4PerformInvocation (Z := Unit) blocking calling don b).run s1).1, ScInv w.2 := by
        by_cases hg : GapInv b
        · exact hG blocking calling don b σe s1 hg hE hDF hzI hzR
        · exact si_performNG blocking calling don b hg s1 hzI
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        exact (sike_of_sbke fun _ => by sb_auto) s2 (hP _ hz2) y hy
      · exact hP _ hz2
    · have hz' : ScInv z.2 := scInv_of_br hI'.1
        (br_mem_of_sbk (m := ExceptT.run (withoutPreemption (Z := Unit) (setThreadState thread .restart)))
          (fun _ => by sb_auto) hz)
      exact hz'

/-! ## The syscall paths and events -/

theorem sikr_getCapReg {σe : State Unit} {β : Type} (reg : Register) {g : CapRef → NonDetE (State Unit) Unit β}
    (hg : ∀ a, SIKR σe (g a)) : SIKR σe (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= g) :=
  sikr_bind (fun _ => ike_liftE (SInvU.uk_getCapReg reg)) (fun _ => ike_liftE (sb_getCapReg reg)) hg

/-- The syscalls, one arm each (nq3's `nq_fl4HandleSyscall` structure). -/
theorem sb_fl4HandleSyscall (hG : ScGap) (rep : Bool) (c : Syscall) (σe : State Unit) (hE : EntryOK σe) :
    SIKR σe (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef), SIKR σe (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => sb_handleInvocationR hG rep cl bl dn fp cptr σe hE
  have hRecv : ∀ b r, SIKR σe (withoutPreemption (Z := Unit) (handleRecv b r)) :=
    fun b r => sikr_of_sik (ike_liftE (si_handleRecv b r))
  have hSR : ∀ (reg : Register) (cl dn fp : Bool) (b r : Bool), SIKR σe (do
      let cptr ← withoutPreemption (Z := Unit) (getCapReg reg)
      fl4HandleInvocationR rep cl false dn fp cptr
      withoutPreemption (handleRecv b r)) :=
    fun reg cl dn fp b r => sikr_getCapReg reg fun cptr =>
      sikr_bind' (hInv _ _ _ _ cptr) fun _ => ike_liftE (si_handleRecv b r)
  cases c
  case sysSend => simp only [fl4HandleSyscall]; exact sikr_getCapReg _ fun cptr => hInv _ _ _ _ cptr
  case sysNBSend => simp only [fl4HandleSyscall]; exact sikr_getCapReg _ fun cptr => hInv _ _ _ _ cptr
  case sysCall => simp only [fl4HandleSyscall]; exact sikr_getCapReg _ fun cptr => hInv _ _ _ _ cptr
  case sysYield => simp only [fl4HandleSyscall]; exact sikr_of_sik (ike_liftE si_handleYield)
  case sysReplyRecv => exact hSR _ _ _ _ _ _
  case sysNBSendRecv => exact hSR _ _ _ _ _ _
  case sysNBSendWait => exact hSR _ _ _ _ _ _
  all_goals (simp only [fl4HandleSyscall]; exact hRecv _ _)

/-- `check_budget_restart` letting the syscall run changes nothing. -/
theorem checkBudget_true_eq {σ : State Unit} {x : Bool × State Unit} (hx : x ∈ (checkBudget (Z := Unit) σ).1)
    (ht : x.1 = true) : x.2 = σ := by
  unfold checkBudget at hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx1
  obtain ⟨x2, hx2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx
  have hv3 : x3.2 = σ := (show IK (fun s => s = σ) (getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime) by
    rd_auto) σ rfl x3 hx3
  dsimp only at hx
  split at hx
  · obtain ⟨x4, hx4, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hx4
    rw [Set.mem_singleton_iff.1 hx]; exact hv3
  · obtain ⟨x4, hx4, hx⟩ := hx
    obtain ⟨x5, hx5, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx] at ht
    cases ht

theorem checkBudgetRestart_true_eq {σ : State Unit} {x : Bool × State Unit}
    (hx : x ∈ (checkBudgetRestart (Z := Unit) σ).1) (ht : x.1 = true) : x.2 = σ := by
  unfold checkBudgetRestart at hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨x2, hx2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx
  have hv3 : x3.2 = x1.2 := (show IK (fun s => s = x1.2) (getThreadState (Z := Unit) x1.2.curThread) by
    rd_auto) x1.2 rfl x3 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx] at ht ⊢
  have h1 := checkBudget_true_eq hx1 ht
  rw [ht] at hx4
  simp only [Bool.not_true, false_and, NonDet.when, if_false] at hx4
  rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hx4)).2, hv3, h1]

macro "kh_auto" : tactic => `(tactic| repeat' (first | ik_step0 | ik_unfold |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _)))

theorem sb_fl4HandleEvent (hG : ScGap) (rep : Bool) (ev : Event) (σ : State Unit) (hE : EntryOK σ) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ScInv y.2 := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    intro y hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, he0, rfl⟩⟩ := SInvU.mem_bindE' hy
    · obtain ⟨z1, hz1, rfl⟩ := SInvU.mem_liftE' hz
      have hE1 : EntryOK z1.2 := entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_updateTimeStamp) hz1)
        (br_mem_of_sbk (fun _ => by sb_auto) hz1)
        ((show SInvU.NK σ.interruptIrqNode (updateTimeStamp (Z := Unit)) from SInvU.nk_updateTimeStamp) σ rfl z1 hz1)
        ((show IK VfhAll (updateTimeStamp (Z := Unit)) by unfold updateTimeStamp; kh_auto) σ hE.vfh z1 hz1)
      obtain ⟨z2, hz2, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2
        simp only [Except.ok.injEq] at hr; subst hr
        have hIx : ScInv x.2 := si_checkBudgetRestart z1.2 hE1.sc x hx
        unfold NonDetE.whenE at hy
        split at hy
        · rename_i ht
          have e := checkBudgetRestart_true_eq hx ht
          rw [e] at hy
          exact sb_fl4HandleSyscall hG rep c z1.2 hE1 z1.2 hE1.sc ⟨rfl, BR.refl _⟩ y hy
        · rw [Set.mem_singleton_iff.1 hy]; exact hIx
      · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2; cases he
    · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz; cases he0
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact si_handleEvent_other ev (fun c e => h ⟨c, e⟩) σ hE.sc

theorem sb_fl4CallKernel (hG : ScGap) (rep : Bool) (ev : Event) (σ : State Unit) (hE : EntryOK σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScInv y.2 := by
  unfold fl4CallKernel
  intro y hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : ScInv z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw' := sb_fl4HandleEvent hG rep ev σ hE w hw
    obtain ⟨r, s⟩ := w
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 hz]; exact hw'
    | error e => exact (ike_liftE si_preemptionPath : SIKE (withoutPreemption (Z := Unit) preemptionPath)) s hw' z hz
  exact (show SIK (do fl4Awaken (Z := Unit); schedule; activateThread) by si_auto) z.2 hz' y hy

/-! ## Tops -/

/-- **`ScInv` across the syscall entry, given `ScGap`.** -/
theorem kentry_scInv_of (hG : ScGap) (c : Syscall) {σ : State Unit} (hE : EntryOK σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScInv y.2 := by
  unfold fl4KernelEntrySyscall
  intro y ⟨z, hz, hy⟩
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hy⟩ := hy
  have hE' : EntryOK w.2 := entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw)
    (br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    ((show IK VfhAll (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)) σ hE.vfh w hw)
  exact sb_fl4CallKernel hG true _ w.2 hE' y hy

/-- **`ScInv` across every kernel event, given `ScGap`.** -/
theorem kcall_scInv_of (hG : ScGap) (rep : Bool) (ev : Event) {σ : State Unit} (hE : EntryOK σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScInv y.2 :=
  sb_fl4CallKernel hG rep ev σ hE

/-- The goal's statement: `ScSym` (ScBack and its converse) at every outcome. -/
theorem kentry_scSym_of (hG : ScGap) (c : Syscall) {σ : State Unit} (hE : EntryOK σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScSym y.2 :=
  fun y hy => (kentry_scInv_of hG c hE y hy).1

theorem kcall_scSym_of (hG : ScGap) (rep : Bool) (ev : Event) {σ : State Unit} (hE : EntryOK σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScSym y.2 :=
  fun y hy => (kcall_scInv_of hG rep ev hE y hy).1

/-! ## Boot (non-vacuity) -/

theorem initKheap_idleThread : ∃ x, initKheap idleThreadPtr = some (.tcb x) ∧ x.tcbSchedContext = some idleScPtr := by
  unfold initKheap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self]
  exact ⟨_, rfl, rfl⟩

theorem init_tcb {u : ObjRef} {x : Tcb} (h : initKheap u = some (.tcb x)) :
    u = idleThreadPtr ∧ x.tcbSchedContext = some idleScPtr := by
  by_cases e : u = idleThreadPtr
  · subst e
    obtain ⟨x0, h0, hs⟩ := initKheap_idleThread
    rw [h0] at h; cases h; exact ⟨rfl, hs⟩
  · exfalso
    unfold initKheap at h
    simp only [Function.update_apply, e, if_false] at h
    split_ifs at h <;> cases h

theorem init_sc {p : ObjRef} {y : SchedContext} {n : Nat} (h : initKheap p = some (.schedContext y n)) :
    p = idleScPtr ∧ y.scTcb = some idleThreadPtr ∧ rneQ y := by
  by_cases e : p = idleScPtr
  · subst e
    rw [SInvV.initKheap_idleSc] at h
    simp only [Option.some.injEq, KernelObject.schedContext.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl, fun _ => List.cons_ne_nil _ _⟩
  · exfalso
    unfold initKheap at h
    simp only [Function.update_apply, e, if_false] at h
    split_ifs at h <;> cases h

/-- **Boot**: the initial state's only binding is the idle thread with the idle SC. -/
theorem boot_scInv : ScInv (initASt (Z := Unit)) := by
  rw [scInv_iff]
  refine ⟨⟨fun u c h => ?_, fun p u h => ?_⟩, fun p y n hp => (init_sc hp).2.2⟩
  · obtain ⟨x, hx, hc⟩ := bv_t.1 h
    obtain ⟨rfl, h2⟩ := init_tcb hx
    rw [h2] at hc; cases hc
    exact bv_s.2 ⟨_, 0, SInvV.initKheap_idleSc, rfl⟩
  · obtain ⟨y, n, hy, hu⟩ := bv_s.1 h
    obtain ⟨rfl, h2, -⟩ := init_sc hy
    rw [h2] at hu; cases hu
    obtain ⟨x0, h0, hs⟩ := initKheap_idleThread
    exact bv_t.2 ⟨x0, h0, hs⟩

theorem boot_scSym : ScSym (initASt (Z := Unit)) := boot_scInv.1

/-- `ScLive` at boot (the idle pair is bound and no cap covers anything: the initial
state holds only null caps). -/
theorem boot_scLive : ScLive (initASt (Z := Unit)) := by
  intro p _
  refine Or.inr fun s c h => ?_
  rw [SInvU.init_capAt h]
  simp [SInvU.covR, SInvU.capRng, objRefs]

theorem boot_entryOK : EntryOK (initASt (Z := Unit)) :=
  ⟨boot_scInv, SInvU.boot_utInv3, boot_vfhAll, boot_scLive⟩

end

end Fl4Proofs.P3.SInvB
