/-
P3 (DESIGN.md §9), invariant line G1 (rd8j, KENTRY-PLAN rd8h handoff 2,
second half): **rd9's `RdBody` for Send / NBSend / Call** (spec side only,
outside the JAtZ cone).

* **`front_facts`**: after a `true` syscall front, `RB ct I ∧ RdyT ct ∧ OffReady
  ∧ Suff ∧ FhAll` with `I` the idle SC, from rd8a's `EF`, ctq's `T1` and `EB
  true` (its `SQ4` / `RBk true`), ut7 / vi3's `IdleScOutV` and invA's `VfhAll`
  at the entry (rd_front / rd10's `bs_uts`; `NQ [ct]` from BS's `NQ []` with ct
  Running or idle).
* `body_rdy`: the body (with the preemption path on its error outcomes) from
  `Rdy` at the handled computation's outcomes and at the preemption path's.
* **`rd_shellAt`**: `rd_fl4HandleInvocationR` after `get_cap_reg`.
* Pinned inputs (to the given entry's run; no ∀-states): `InvIn r fp σ` (rd8j's
  `PerfIn` at every `get_cap_reg` outcome after a `true` front) and `PreR rep c
  σ` (`Rdy` after `preemption_path` at every error outcome of the syscall
  after a `true` front: the error outcomes are the perform's preemption points;
  l4v: `preemption_path` / `check_budget` / `charge_budget` / `handle_interrupt`
  keep valid_sched from the preempted state).
* **`rdBody_send`**: `RdBody rep c σ` for c ∈ Send / NBSend / Call.
-/
import Fl4Proofs.P3.SpecInvRd8jB
open Classical

namespace Fl4Proofs.P3.SInvR.B8j
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-- **The shell's start facts after a `true` front** (module docstring). -/
theorem front_facts {σ : State Unit} (hEF : A8.EF σ) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ)
    (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1)
    (ht : v.1 = true) :
    B8f.RB v.2.curThread σ.idleSc v.2 ∧ RdyT v.2 v.2.curThread ∧ Sched.OffReady v.2 ∧ Suff v.2 ∧ FhAll v.2 := by
  obtain ⟨xt, hct, hst⟩ := hEF.ct
  obtain ⟨-, -, h3⟩ := rd_front hEF.rdy hEF.off hEF.vmt hEF.sc hEF.cs hct hst hEF.q hEF.si hEF.cb hEF.hb
    hEF.ca hEF.ni hv
  obtain ⟨w, hw, e, hSf⟩ := h3 ht
  rw [e]
  have hB := A10.bs_uts hEF hw
  obtain ⟨ek, -, -, -⟩ := SInvO.uts_off hw
  obtain ⟨eq, -, -, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ w hw
  have h1w : SInvQ.T1 w.2 := by
    intro d p u hu; rw [eq] at hu; rw [ek]; exact h1 d p u hu
  have hH := B8h.hb_bs hB h1w
  obtain ⟨x, hx, hxs⟩ := hB.ct
  have hu : SInvU.uV w.2 = SInvU.uV σ := SInvU.uk_updateTimeStamp σ rfl w hw
  refine ⟨⟨hB.rdy, ⟨SInvQ.eb_of SInvQ.tq_updateTimeStamp SInvQ.sa_updateTimeStamp SInvQ.q4_updateTimeStamp
      SInvQ.rb_updateTimeStamp σ hEB w hw, rfl, hB.si, nq_consR hB.nq hx ?_ ?_⟩, h1w, hB.sc,
      SInvV.gk_updateTimeStamp _ SInvV.wl_vmt σ hEF.vmt w hw, ?_, ei⟩, hH.2.1, hB.off, hSf, ?_⟩
  · rcases hxs with h | h <;> rw [h] <;> exact fun h => h
  · rcases hxs with h | h <;> rw [h] <;> rfl
  · show SInvU.IrqOutV (fun _ => σ.idleSc) (SInvU.uV w.2)
    rw [hu]; exact hIO
  · refine fhAll_of_vfh ?_
    intro t x' hx'
    rw [ek] at hx'
    exact hV t x' hx'

/-- The body from `Rdy` at the handled computation's outcomes and after the
preemption path at its error outcomes. -/
theorem body_rdy {m : PMonad Unit Unit} {s : State Unit} (h : ∀ z ∈ (m.run s).1, Rdy z.2)
    (hp : ∀ z ∈ (m.run s).1, ∀ e, z.1 = .error e → ∀ y ∈ (preemptionPath (Z := Unit) z.2).1, Rdy y.2) :
    ∀ y ∈ (ExceptT.run (NonDetE.handleE m fun _ => withoutPreemption (Z := Unit) preemptionPath) s).1,
      Rdy y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, rfl⟩ | ⟨e, he, hy⟩⟩ := A12b.mem_handleE_cases hy
  · exact h z hz
  · unfold withoutPreemption at hy
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy
    exact hp z hz e he w hw

/-- **The shell after `get_cap_reg`** from the shell's start facts at `s0`. -/
theorem rd_shellAt {s0 : State Unit} {I : ObjRef} (hRB : B8f.RB s0.curThread I s0) (hRT : RdyT s0 s0.curThread)
    (hO : Sched.OffReady s0) (hS : Suff s0) (hF : FhAll s0) (rep cl bl dn fp : Bool) (r : Register)
    {g : CapRef × State Unit} (hg : g ∈ (getCapReg (Z := Unit) r s0).1) (hP : PerfIn fp g.1 g.2) :
    ∀ z ∈ ((fl4HandleInvocationR (Z := Unit) rep cl bl dn fp g.1).run g.2).1, Rdy z.2 := by
  have hJ : JS s0.curThread I s0 g.2 := js_getCapReg r s0 ⟨rfl, rfl, hRB⟩ g hg
  have ect : g.2.curThread = s0.curThread := A12b.kz_curThread hJ.1
  have hS1 := svs_kz hJ.1
  have hc1 := kz_cfS hJ.1
  exact rd_fl4HandleInvocationR rep cl bl dn fp g.1 I g.2 (by rw [ect]; exact hJ.2.2)
    (by rw [ect]; exact rdyT_svs hRT hS1) (offReady_svcf hO hS1 hc1) (suff_svcf hS hS1 hc1) (fhAll_js hF hJ) hP

/-- **The perform inputs, pinned to the entry's run** (module docstring). -/
def InvIn (r : Register) (fp : Bool) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfIn fp g.1 g.2

/-- **`Rdy` after the preemption path, pinned to the entry's run** (module docstring). -/
def PreR (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ z ∈ ((fl4HandleSyscall (Z := Unit) rep c).run v.2).1,
    ∀ e, z.1 = .error e → ∀ y ∈ (preemptionPath (Z := Unit) z.2).1, Rdy y.2

/-- **rd9's `RdBody` for Send / NBSend / Call** (module docstring). -/
theorem rdBody_send (rep : Bool) (c : Syscall) {r : Register} {calling blocking don : Bool}
    (hc : A12b.sendArgs c = some (r, calling, blocking, don)) (σ : State Unit) (hEF : A8.EF σ) (h1 : SInvQ.T1 σ)
    (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) (hP : InvIn r false σ)
    (hPre : PreR rep c σ) : A9.RdBody rep c σ := by
  intro v hv ht y hy
  obtain ⟨hRB, hRT, hO, hS, hF⟩ := front_facts hEF h1 hEB hIO hV hv ht
  refine body_rdy (fun z hz => ?_) (fun z hz e he => hPre v hv ht z hz e he) y hy
  have hsh : ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ z ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don false g.1).run g.2).1, Rdy z.2 :=
    fun g hg => rd_shellAt hRB hRT hO hS hF rep calling blocking don false r hg (hP v hv ht g hg)
  cases c <;> simp only [A12b.sendArgs, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hc <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc <;> simp only [fl4HandleSyscall] at hz <;>
    · obtain ⟨u, hu, ⟨a, ha, hz⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hz
      swap
      · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hu; cases he
      obtain ⟨g, hg, rfl⟩ := ft_mem_liftE hu
      simp only [Except.ok.injEq] at ha; subst ha
      exact hsh g hg z hz

end

end Fl4Proofs.P3.SInvR.B8j
