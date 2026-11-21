/-
P3 (DESIGN.md §9), invariant line G1 (rd8n): **rd8j's `PerfRest` Untyped and
ASIDControl inputs discharged** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd8j handoff 3).

* `PerfRestN σ iv`: what is left of rd8j's `PerfRest` — DomainSet's `SR t`
  and Reply's `BlockedScActive`; `PerfInN` its run-pinned form (rd8j's
  `PerfIn` shape).
* `UF σ := UtInv'' σ ∧ ScLiveT (idleThread, idleSc) σ ∧ IdleOutV σ`: the
  carried facts (ut8, sl, sg / vi3) the retype / detype proofs need beside
  rd8f's `RB` (which brings `Rdy`, `ValidMachineTime`, `ScInv`, `IdleScOutV`).
* The shell keeps them: `UtInv''` / `IdleOutV` read the cap view (rd8j's `JS`
  keeps it), `ScLiveT` reads TCB bindings and whole SCs (`live_kz` along rd12b's
  `KZ` view; `sl_setThreadState` for the Restart write); the idle pointers by
  `cfS`. **`uf_restart`.**
* The decode's `GapOKN` (ut8's `okv_fl4DecodeG`, the lookups' slot facts as in
  ctq17's shell) gives `UtRetOK` / `MpOKN` at the perform. **`perfRest_of`**
  (rd8n A's `rd_fl4InvokeUntyped` / `archOK_asid`), **`perfIn_of : RB ct I σ →
  UF σ → PerfInN fp cptr σ → PerfIn fp cptr σ`**, and the shell top
  **`rd_fl4HandleInvocationRN`** (rd8j's `rd_fl4HandleInvocationR` with
  `UF σ` and `PerfInN` in place of `PerfIn`).
-/
import Fl4Proofs.P3.SpecInvRd8nA
import Fl4Proofs.P3.SpecInvRd8jB
import Fl4Proofs.P3.SpecInvUtO5
import Fl4Proofs.P3.SpecInvUtP6
open Classical

namespace Fl4Proofs.P3.SInvR.B8n
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8j Fl4Proofs.P3.SInvR.A12b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The inputs left -/

/-- **What is left of rd8j's `PerfRest`**: DomainSet (`SR`) and Reply (`BlockedScActive`). -/
def PerfRestN (σ : State Unit) : Fl4Invocation → Prop
  | .invokeDomain (.invokeDomainSet t _) => SR t σ
  | .invokeReply _ _ => Sched.BlockedScActive σ
  | _ => True

/-- `PerfRestN` pinned to the shell's run from σ (rd8j's `PerfIn` shape). -/
def PerfInN (fp : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE fp cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, PerfRestN u.2 b

/-- **The carried facts beside rd8f's `RB`** (module docstring). -/
def UF (σ : State Unit) : Prop :=
  SInvU.UtInv'' σ ∧ SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ ∧ SInvG.IdleOutV σ

/-! ## The carry -/

theorem tcbV_some {o : Option KernelObject} {a : ThreadState × Option Fault × Option ObjRef}
    (h : B8c.tcbV o = some a) : ∃ x, o = some (.tcb x) ∧ a = (x.tcbState, x.tcbFault, x.tcbSchedContext) := by
  rcases o with _ | o
  · cases h
  · cases o <;> first | (cases h; done) | exact ⟨_, rfl, (Option.some.inj h).symm⟩

theorem scO_some {o : Option KernelObject} {y : SchedContext} {n : Nat} (h : scO o = some (y, n)) :
    o = some (.schedContext y n) := by
  rcases o with _ | o
  · cases h
  · cases o <;> first | (cases h; done) | (cases h; rfl)

/-- A live object along `KZ` was a live object. -/
theorem live_kz {σ0 s : State Unit} (hz : A12b.KZ σ0 s) {p : ObjRef} {o : KernelObject}
    (hp : s.kheap p = some o) (hl : SInvL.liveO o) : ∃ o', σ0.kheap p = some o' ∧ SInvL.liveO o' := by
  have e1 : B8c.tcbV (s.kheap p) = B8c.tcbV (σ0.kheap p) := congrArg (fun v => v.1.1 p) hz
  have e2 : SInvE.scAt s p = SInvE.scAt σ0 p := congrArg (fun v => v.1.2.1 p) hz
  rw [scAt_eq, scAt_eq, hp] at e2
  rw [hp] at e1
  cases o
  case tcb x =>
    obtain ⟨x0, hx0, ea⟩ := tcbV_some (a := (x.tcbState, x.tcbFault, x.tcbSchedContext)) e1.symm
    refine ⟨_, hx0, ?_⟩
    show x0.tcbSchedContext ≠ none
    have : x.tcbSchedContext = x0.tcbSchedContext := congrArg (fun p => p.2.2) ea
    rw [← this]; exact hl
  case schedContext y n => exact ⟨_, scO_some (y := y) (n := n) e2.symm, hl⟩
  all_goals exact (hl : False).elim

theorem scLiveT_kz {σ0 s : State Unit} {I : ObjRef × ObjRef} (h : SInvL.ScLiveT I σ0) (hz : A12b.KZ σ0 s)
    (hu : SInvU.uV s = SInvU.uV σ0) : SInvL.ScLiveT I s := by
  intro p o hp hl h1 h2
  obtain ⟨o', hp', hl'⟩ := live_kz hz hp hl
  obtain ⟨sl, c, hs, hn⟩ := h p o' hp' hl' h1 h2
  have hc : SInvU.capAt s = SInvU.capAt σ0 := congrArg (fun w : SInvU.UView => w.2.1) hu
  exact ⟨sl, c, by rw [hc]; exact hs, hn⟩

/-- **`UF` at the perform**, from `UF` at the shell start and rd8j's `JS` at the decode's outcome. -/
theorem uf_restart {I : ObjRef} {σ s' : State Unit} (hF : UF σ) (hJ : JS σ.curThread I σ s')
    {u : Unit × State Unit} (hu : u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1) : UF u.2 := by
  obtain ⟨hz, hv, -⟩ := hJ
  have hc : cfS s' = cfS σ := kz_cfS hz
  have hc' : cfS u.2 = cfS s' := cfk_setThreadState' σ.curThread .restart s' u hu
  have hv' : SInvU.uV u.2 = SInvU.uV s' := SInvU.uk_setThreadState σ.curThread .restart s' rfl u hu
  have eit : u.2.idleThread = σ.idleThread := congrArg (fun p => p.2.2.2.1) (hc'.trans hc)
  have eis : u.2.idleSc = σ.idleSc := congrArg (fun p => p.2.2.2.2.1) (hc'.trans hc)
  obtain ⟨hU, hL, hI⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · show SInvU.UtInv''V _; rw [hv', hv]; exact hU
  · have hL1 : SInvL.ScLiveT (σ.idleThread, σ.idleSc) s' := scLiveT_kz hL hz hv
    have hL2 := (SInvL.sl_setThreadState (I := (σ.idleThread, σ.idleSc)) (K := []) σ.curThread .restart s'
      ⟨hL1, fun _ h => by simp at h⟩ u hu).1
    rw [eit, eis]; exact hL2
  · show SInvU.IrqOutV (fun _ => u.2.idleThread) (SInvU.uV u.2)
    rw [hv', hv, eit]; exact hI

/-! ## The perform inputs -/

/-- **rd8j's `PerfRest` from the carried facts, the decode's `GapOKN` and `PerfRestN`.** -/
theorem perfRest_of {C I : ObjRef} {u : State Unit} {b : Fl4Invocation} (hRB : B8f.RB C I u) (hF : UF u)
    (hG : SInvU.GapOKN (SInvU.uV u) b) (hP : PerfRestN u b) : PerfRest u b := by
  obtain ⟨hR, -, -, hSI, hv, hIO, hI⟩ := hRB
  have hO : SInvU.IO (fun _ => u.idleSc) u := by rw [hI]; exact hIO
  obtain ⟨hU, hL, hIt⟩ := hF
  cases b with
  | invokeUntyped i => exact rd_fl4InvokeUntyped i u hR hv hU hL hIt hSI.back hO (SInvU.utRetOK_of_V hG.1)
  | invokeDomain d => cases d <;> first | exact hP | trivial
  | invokeReply r g => exact hP
  | invokeArchObject i =>
    cases i with
    | spec j =>
      cases j
      case invokeASIDControl o => exact archOK_asid o u hR hU hL hIt hSI.back hO hG
      all_goals trivial
    | _ => trivial
  | _ => trivial

set_option maxHeartbeats 4000000 in
/-- **rd8j's `PerfIn` from `RB ct I`, `UF` at the shell start and `PerfInN`.** -/
theorem perfIn_of (fp : Bool) (cptr : CapRef) (I : ObjRef) (σ : State Unit) (hRB : B8f.RB σ.curThread I σ)
    (hF : UF σ) (hN : PerfInN fp cptr σ) : PerfIn fp cptr σ := by
  intro w0 hw0 a s b s' has hbs u hu
  have hJ0 : JS σ.curThread I σ σ := ⟨rfl, rfl, hRB⟩
  have hJw : JS σ.curThread I σ w0.2 := js_getMessageInfo _ σ hJ0 w0 hw0
  have hJs : JS σ.curThread I σ s := js_invF _ _ _ w0.2 hJw _ has
  have hJ' : JS σ.curThread I σ s' := js_invE _ _ _ _ a s hJs _ hbs
  have hRB' : B8f.RB σ.curThread I u.2 := rb_restart s' hJ'.2.2 hu
  have hUF : UF u.2 := uf_restart hF hJ' hu
  have hP := hN w0 hw0 a s b s' has hbs u hu
  -- GapOKN from the decode, as ctq17's shell
  have hOk : SInvU.OkV (SInvU.uV w0.2) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (SInvU.uV w0.2).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (SInvU.uV w0.2).2.1 p.2 = some p.1 ∧
        SInvU.DestRefV (SInvU.uV w0.2) p.2) (invF σ.curThread cptr w0.1) := by
    unfold invF
    refine SInvU.okv_bind (fun _ => SInvU.uk_capFaultOnFailure _ _ _ (SInvU.uk_lookupCapAndSlot _ _))
      (SInvU.okv_capFaultOnFailure _ _ (SInvU.okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine SInvU.okv_bind_uk (fun _ => ike_liftE (SInvU.uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine SInvU.okv_bind (fun _ => SInvU.uk_lookupExtraCaps _ _ _) (SInvU.okv_lookupExtraCapsN _ _ _)
      fun ex hex => SInvU.okv_returnOk ?_
    exact ⟨hx, hex⟩
  obtain ⟨hcap, hex⟩ := hOk w0.2 rfl _ s has
  have hvs : SInvU.uV s = SInvU.uV w0.2 := uk_invF (SInvU.uV w0.2) σ.curThread cptr w0.1 w0.2 rfl _ has
  obtain ⟨sl, cap, ex, buf⟩ := a
  have hbs' := hbs
  unfold invE at hbs'
  obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e0, -, he0⟩⟩ := SInvU.mem_bindE' hbs'
  swap
  · simp at he0
  obtain ⟨x0, hx0, e0⟩ := SInvU.mem_liftE' hz0
  subst e0
  simp only [Except.ok.injEq] at ha0
  subst ha0
  have hvx : SInvU.uV x0.2 = SInvU.uV w0.2 :=
    (SInvU.uk_getMrs (uvw := SInvU.uV s) _ _ _ s rfl x0 hx0).trans hvs
  have hv' : SInvU.uV s' = SInvU.uV w0.2 :=
    (SInvU.uk_fl4DecodeInvocation (uvw := SInvU.uV x0.2) _ _ _ _ _ _ _ _ x0.2 rfl _ hb0).trans hvx
  have hG0 : SInvU.GapOKN (SInvU.uV w0.2) b :=
    SInvU.okv_fl4DecodeG fp _ _ _ _ _ _ _ hcap (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
  have huv : SInvU.uV u.2 = SInvU.uV s' := SInvU.uk_setThreadState σ.curThread .restart s' rfl u hu
  have hG : SInvU.GapOKN (SInvU.uV u.2) b := by rw [huv, hv']; exact hG0
  exact perfRest_of hRB' hUF hG hP

/-- **`handle_invocation` keeps `Rdy`** with the Untyped / ASIDControl inputs discharged: rd8j's
`rd_fl4HandleInvocationR` with `UF σ` (carried facts) and `PerfInN` (DomainSet / Reply only). -/
theorem rd_fl4HandleInvocationRN (rep calling blocking don fp : Bool) (cptr : CapRef) (I : ObjRef)
    (σ : State Unit) (hRB : B8f.RB σ.curThread I σ) (hRT : RdyT σ σ.curThread) (hO : Sched.OffReady σ)
    (hS : Suff σ) (hF : FhAll σ) (hU : UF σ) (hP : PerfInN fp cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, Rdy y.2 :=
  rd_fl4HandleInvocationR rep calling blocking don fp cptr I σ hRB hRT hO hS hF (perfIn_of fp cptr I σ hRB hU hP)

end

end Fl4Proofs.P3.SInvR.B8n
