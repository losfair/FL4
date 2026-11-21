/-
P3 (DESIGN.md §9), invariant line G1 (rd8m, KENTRY-PLAN rd8j handoff 1 and 4):
**rd9's `RdBody` for ReplyRecv / NBSendRecv / NBSendWait and for Yield, so
`RdBody` for every syscall** (spec side only, outside the JAtZ cone).

* **`sr_core`**: the send-receive body (`get_cap_reg`, the first-phase
  invocation, `handle_recv`) keeps `Rdy` from `Rdy` at the invocation outcomes
  and rd8m-C's `RHN ct` at its `ok` outcomes.
* `RcvIn rep c σ` (pinned to the entry's run, no ∀-states): at every `ok`
  first-phase invocation outcome of the shell's run, `ScInv`, ct a TCB not
  BlkR, `RT ct` (rd14a's `RecvTB` without `Rdy`, which is proved here by rd8j's
  `rd_shellAt`; `Simple` is not asked: rd14a's FINDING).
* **`rdBody_sr`**: from the entry facts of rd8j's `rdBody_send`, ctq17's `EvP`
  (for ctq's `EB true` at the invocation outcome), `InvIn r true`, `PreR`,
  `RcvIn`.
* **`rdBody_yield`**: `charge_budget` from rd10's body start `BS` (rd's
  `rd_chargeBudget`: cur_sc active with refills, `Excl`, ct bound to it,
  `ScFwd`), then the `sc_consumed` write. No input.
* **`rdBody_all`**: `RdBody rep c σ` for every `c`.
-/
import Fl4Proofs.P3.SpecInvRd8mC
import Fl4Proofs.P3.SpecInvRd8jC
import Fl4Proofs.P3.SpecInvRd13aA
open Classical

namespace Fl4Proofs.P3.SInvR.B8m
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-- **The send-receive body** from facts at the first-phase invocation outcomes. -/
theorem sr_core {s : State Unit} {r : Register} {cr rep : Bool}
    (hsh : ∀ g ∈ (getCapReg (Z := Unit) r s).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, Rdy t.2)
    (hrc : ∀ g ∈ (getCapReg (Z := Unit) r s).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        RHN t.2.curThread t.2) :
    ∀ z ∈ (((do
      let p ← withoutPreemption (Z := Unit) (getCapReg r)
      fl4HandleInvocationR (Z := Unit) rep false false true true p
      withoutPreemption (Z := Unit) (handleRecv true cr)) : PMonad Unit Unit).run s).1, Rdy z.2 := by
  intro z hz
  obtain ⟨u, hu, ⟨a, ha, hz⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hz
  swap
  · unfold withoutPreemption at hu
    obtain ⟨w, -, rfl⟩ := ft_mem_liftE hu; cases he
  unfold withoutPreemption at hu
  obtain ⟨g, hg, rfl⟩ := ft_mem_liftE hu
  simp only [Except.ok.injEq] at ha; subst ha
  obtain ⟨t, ht, ⟨a, ha, hz⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hz
  · unfold withoutPreemption at hz
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    cases a
    exact rd_handleRecvN t.2.curThread true cr t.2 (hrc g hg t ht ha) w hw
  · exact hsh g hg t ht

/-- The facts at the first-phase invocation outcomes not carried here (rd14a's
`RecvTB` without `Rdy`), pinned to the entry's run. -/
def RcvIn (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, A12b.srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        SInvB.ScInv t.2 ∧ (∃ x, t.2.kheap t.2.curThread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧
          B8d.RT t.2 t.2.curThread

/-- **rd9's `RdBody` for ReplyRecv / NBSendRecv / NBSendWait** (module docstring). -/
theorem rdBody_sr (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {r : Register} {cr : Bool}
    (hc : A12b.srArgs c = some (r, cr)) (σ : State Unit) {N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop}
    {Nq : Irq → ObjRef} {σe : State Unit}
    (hEF : A8.EF σ) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (hσ : SInvQ.P17.EvP σ.curThread N S I d Nq σe σ) (hCN : σ.curThread ≠ N)
    (hP : B8j.InvIn r true σ) (hPre : B8j.PreR rep c σ) (hRc : RcvIn rep c σ) : A9.RdBody rep c σ := by
  intro v hv ht y hy
  obtain ⟨hRB, hRT, hO, hS, hF⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  refine B8j.body_rdy (fun z hz => ?_) (fun z hz e he => hPre v hv ht z hz e he) y hy
  have hsh : ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, Rdy t.2 :=
    fun g hg => B8j.rd_shellAt hRB hRT hO hS hF rep false false true true r hg (hP v hv ht g hg)
  have hrc : ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        RHN t.2.curThread t.2 := by
    intro g hg t ht' hok
    have hg' : SInvQ.P17.EvP σ.curThread N S I d Nq σe g.2 :=
      A13a.evp_getCapReg r v.2 (A13a.evp_front hσ hv ht) g hg
    have hE1 : SInvQ.EB true t.2 :=
      (SInvQ.P17.eb_fl4HandleInvocationR hnd σ.curThread N S rep false false true true g.1 (fun _ => rfl) hCN
        g.2 hg'.1 t ht').2 () hok
    obtain ⟨hI, hb, hT⟩ := hRc v hv ht r cr hc g hg t ht' hok
    exact rhn_of (hsh g hg t ht') hI hb hT hE1
  cases c <;> simp only [A12b.srArgs, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hc <;>
    obtain ⟨rfl, rfl⟩ := hc <;> exact sr_core hsh hrc z hz

/-- **rd9's `RdBody` for Yield** from rd8a's `EF` (no input). -/
theorem rdBody_yield (rep : Bool) (σ : State Unit) (hEF : A8.EF σ) : A9.RdBody rep .sysYield σ := by
  intro v hv ht y hy
  obtain ⟨h, -⟩ := A10.bs_front hEF hv ht
  obtain ⟨w, hw, e⟩ := A10.mem_handleE_wp (m := handleYield (Z := Unit)) hy
  rw [e]
  unfold handleYield at hw
  rw [Notif.nd_gets_bind] at hw
  obtain ⟨w1, hw1, hw⟩ := hw
  obtain ⟨n1, hk1, e1⟩ := SInvE.mem_getSchedContext hw1
  rw [e1] at hw
  beta_reduce at hw
  rw [Notif.nd_gets_bind] at hw
  obtain ⟨w2, hw2, hw⟩ := hw
  obtain ⟨-, rfl⟩ := SInvE.mem_getRefillHead hk1 hw2
  obtain ⟨w3, hw3, hw⟩ := hw
  beta_reduce at hw
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨xa, c0, y0, n, hxa, hca, hky, hact⟩ := h.ca h.ni
  rw [hct] at hxa; cases hxa
  have hb : xt.tcbSchedContext = some v.2.curSc := h.cs xt hct
  rw [hb] at hca; cases hca
  obtain ⟨y1, k1, hy1, -, hne⟩ := h.sc.back v.2.curThread xt v.2.curSc hct hb
  rw [hky] at hy1; cases hy1
  have hne' : y0.scRefills ≠ [] := hne (Or.inr hact)
  have r3 := (rd_chargeBudget h.rdy hky hact hne'
    (fun _ _ => excl_entry h.sc.back h.cs hct hst h.q h.si) hct hb h.sc.fwd _ false hw3).1
  exact rd_updateSchedContext v.2.curSc (scConsumedUpdate fun _ => w1.1.scConsumed + v.2.consumedTime)
    (fun _ => ⟨rfl, rfl, rfl⟩) w3.2 r3 w hw

/-- **rd9's `RdBody` for every syscall** (rd9 / rd10's `hRdB` discharged up to
the pinned inputs: rd8j's `InvIn` / `PreR`, this module's `RcvIn`). -/
theorem rdBody_all (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit) {N S : ObjRef}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe : State Unit}
    (hEF : A8.EF σ) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (hσ : SInvQ.P17.EvP σ.curThread N S I d Nq σe σ) (hCN : σ.curThread ≠ N)
    (hRS : σ.schedulerAction = .resumeCurThread)
    (hPs : ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hPre : B8j.PreR rep c σ) (hRc : RcvIn rep c σ) : A9.RdBody rep c σ := by
  cases hcs : A12b.sendArgs c with
  | some a =>
    obtain ⟨r, cl, bl, dn⟩ := a
    exact B8j.rdBody_send rep c hcs σ hEF h1 hEB hIO hV (hPs r cl bl dn hcs) hPre
  | none =>
  cases hcr : A12b.srArgs c with
  | some a =>
    obtain ⟨r, cr⟩ := a
    exact rdBody_sr hnd rep c hcr σ hEF h1 hEB hIO hV hσ hCN (hPr r cr hcr) hPre hRc
  | none =>
    cases c
    all_goals first
      | (simp [A12b.sendArgs] at hcs; done)
      | (simp [A12b.srArgs] at hcr; done)
      | exact rdBody_yield rep σ hEF
      | exact B8h.rdBody_recv rep _ (by simp) σ hEF h1 hEB.2 hRS

end

end Fl4Proofs.P3.SInvR.B8m
