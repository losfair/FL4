/-
P3 (DESIGN.md §9), invariant line G1 (rd8n): **`VB` (l4v `valid_blocked`)
and DomainSet's `SR t` from it** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd8j handoff 3, rd8h's set_domain finding).

* **`VB σ` [J]** (l4v `valid_blocked`, MCS form): a `schedulable` thread (runnable,
  bound to an active SC, not in the release queue) that is neither the current
  thread nor the switch target is in a ready queue. With `R1` (Rdy) it gives
  rd8h's `SR t` for every `t` (**`sr_of_vb`**: ct by `RdyT ct`, a switch target
  excluded by `Simple`). `boot_vb`: at boot no TCB is runnable (`init_tcbSt`).
* The shell carry to the perform: `VB` reads the scheduling part of each TCB /
  SC (rd12b's `KZ` view keeps it: `sched_kz`), the queues (the lookups and the
  decode keep them: rd8n Q's `qv_` family, `qv_invF` / `qv_invE`), the current
  thread and the action (`KZ`'s `cfS` / action): **`vb_kz`**; the Restart write
  of ct changes only ct's TCB (`vb_restart`, `Simple` from rd8f's `RB`).
* **`perfInN_of`**: rd8n B's `PerfInN` from `VB` at the shell start and the
  Reply input alone (`PerfInB`: rd8i / rd8l's `BlockedScActive`, pinned);
  **`rd_fl4HandleInvocationRV`**: `handle_invocation` keeps `Rdy` from `RB ct I`,
  `RdyT ct`, `OffReady`, `Suff`, `FhAll`, `UF`, `VB` and `PerfInB`.
* NOT done here (rd8n handoff): `VB` carried across every writer of the entry
  (generated family + hand writers), the front (`update_time_stamp` /
  `check_budget_restart`), and the tops `kentry_sr` / `kcall_sr`.
-/
import Fl4Proofs.P3.SpecInvRd8nB
import Fl4Proofs.P3.SpecInvRd8nQ
open Classical

namespace Fl4Proofs.P3.SInvR.B8n
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8j Fl4Proofs.P3.SInvR.A12b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- **VB [J]** (l4v `valid_blocked`, MCS): a schedulable thread that is neither the current
thread nor the switch target is in a ready queue. -/
def VB (σ : State Unit) : Prop :=
  ∀ t, schedulable t σ = true → t ≠ σ.curThread → σ.schedulerAction ≠ .switchThread t →
    ∃ d p, t ∈ σ.readyQueues d p

/-- **rd8h's `SR t` from `VB`** (`R1` for a queued thread, `RdyT ct` for ct, no switch target). -/
theorem sr_of_vb {σ : State Unit} (hV : VB σ) (h1 : R1 σ) (hS : SInvQ.Simple σ) (hct : RdyT σ σ.curThread)
    (t : ObjRef) : SR t σ := by
  intro hs
  by_cases e : t = σ.curThread
  · rw [e]; exact hct
  obtain ⟨d, p, hq⟩ := hV t hs e (hS t)
  exact h1 d p t hq

/-- **`VB` at boot**: no TCB is runnable. -/
theorem boot_vb : VB (initASt (Z := Unit)) := by
  intro t hs _ _
  obtain ⟨x, -, -, -, hx, -, hr, -, -, -⟩ := Sched.schedulable_inv hs
  have e := init_tcbSt (u := t) hx
  rw [e] at hr; simp [runnable] at hr

/-! ## The shell carry -/

/-- `schedulable` along rd12b's `KZ` view and the release queue. -/
theorem sched_kz {σ0 s : State Unit} (hz : A12b.KZ σ0 s) (hr : s.releaseQueue = σ0.releaseQueue) {t : ObjRef}
    (h : schedulable t s = true) : schedulable t σ0 = true := by
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv h
  have e1 : B8c.tcbV (s.kheap t) = B8c.tcbV (σ0.kheap t) := congrArg (fun v => v.1.1 t) hz
  have e2 : SInvE.scAt s scp = SInvE.scAt σ0 scp := congrArg (fun v => v.1.2.1 scp) hz
  rw [scAt_eq, scAt_eq, hy] at e2
  rw [hx] at e1
  obtain ⟨x0, hx0, ea⟩ := tcbV_some (a := (x.tcbState, x.tcbFault, x.tcbSchedContext)) e1.symm
  have hy0 := scO_some (y := y) (n := n) e2.symm
  have es : x0.tcbState = x.tcbState := (congrArg (fun p => p.1) ea).symm
  have ec : x0.tcbSchedContext = x.tcbSchedContext := (congrArg (fun p => p.2.2) ea).symm
  exact Sched.schedulable_of hx0 (by rw [ec]; exact hsc) (by rw [es]; exact hrn) hy0 ha (by rw [← hr]; exact hq)

/-- **`VB` along `KZ` and the queues.** -/
theorem vb_kz {σ0 s : State Unit} (hV : VB σ0) (hz : A12b.KZ σ0 s) (hq : QVv s = QVv σ0) : VB s := by
  have er : s.releaseQueue = σ0.releaseQueue := congrArg (fun p => p.2) hq
  have eq : s.readyQueues = σ0.readyQueues := congrArg (fun p => p.1) hq
  intro t ht hne hsw
  rw [kz_curThread hz] at hne
  rw [kz_act hz] at hsw
  obtain ⟨d, p, hm⟩ := hV t (sched_kz hz er ht) hne hsw
  exact ⟨d, p, by rw [eq]; exact hm⟩

theorem qv_invF (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : QVKE V (invF t cptr info) :=
  ike_invF t cptr info (by qv_auto) (by qv_auto) (fun _ => by qv_auto)

theorem qv_invE (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : QVKE V (invE fp cptr t info a) :=
  ike_invE fp cptr t info a (fun _ => by qv_auto) (fun _ _ _ _ _ => by qv_auto)

/-- **`VB` across the Restart write of the current thread** (no switch target after it). -/
theorem vb_restart {C : ObjRef} {s : State Unit} (hV : VB s) (hS : SInvQ.Simple s) (hC : s.curThread = C)
    {u : Unit × State Unit} (hu : u ∈ (setThreadState (Z := Unit) C .restart s).1) : VB u.2 := by
  have ect : u.2.curThread = s.curThread :=
    congrArg (fun p => p.2.2.1) (cfk_setThreadState' C .restart s u hu)
  have hq : QVv u.2 = QVv s := qv_setThreadState (V := QVv s) C .restart s rfl u hu
  have er : u.2.releaseQueue = s.releaseQueue := congrArg (fun p => p.2) hq
  have eq : u.2.readyQueues = s.readyQueues := congrArg (fun p => p.1) hq
  have hu' := hu
  unfold setThreadState at hu'
  obtain ⟨z, hz, hu'⟩ := hu'
  obtain ⟨x1, hx1, e⟩ := SInv.mem_threadSet hz
  have ek : u.2.kheap = z.2.kheap := kh_setThreadStateAct _ C z.2 rfl u hu'
  have hk : ∀ q, q ≠ C → u.2.kheap q = s.kheap q := by
    intro q hqC; rw [ek, e]; exact Function.update_of_ne hqC _ _
  have hkC : ∃ x, u.2.kheap C = some (.tcb x) := by
    rw [ek, e]; exact ⟨_, Function.update_self _ _ _⟩
  intro t ht hne hsw
  rw [ect, hC] at hne
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hqr⟩ := Sched.schedulable_inv ht
  have hscp : scp ≠ C := by
    rintro rfl; obtain ⟨x', hx'⟩ := hkC; rw [hx'] at hy; cases hy
  have hs0 : schedulable t s = true :=
    Sched.schedulable_of (by rw [← hk t hne]; exact hx) hsc hrn (by rw [← hk scp hscp]; exact hy) ha
      (by rw [← er]; exact hqr)
  obtain ⟨d, p, hm⟩ := hV t hs0 (by rw [hC]; exact hne) (hS t)
  exact ⟨d, p, by rw [eq]; exact hm⟩

/-! ## The perform inputs -/

/-- **The Reply input alone** (rd8i / rd8l's `BlockedScActive`). -/
def PerfRestB (σ : State Unit) : Fl4Invocation → Prop
  | .invokeReply _ _ => Sched.BlockedScActive σ
  | _ => True

/-- `PerfRestB` pinned to the shell's run from σ. -/
def PerfInB (fp : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE fp cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, PerfRestB u.2 b

set_option maxHeartbeats 4000000 in
/-- **rd8n B's `PerfInN` from `VB` at the shell start** (DomainSet's `SR t` by `sr_of_vb` at the
perform) and the Reply input. -/
theorem perfInN_of (fp : Bool) (cptr : CapRef) (I : ObjRef) (σ : State Unit) (hRB : B8f.RB σ.curThread I σ)
    (hRT : RdyT σ σ.curThread) (hO : Sched.OffReady σ) (hS : Suff σ) (hV : VB σ) (hB : PerfInB fp cptr σ) :
    PerfInN fp cptr σ := by
  intro w0 hw0 a s b s' has hbs u hu
  have hJ0 : JS σ.curThread I σ σ := ⟨rfl, rfl, hRB⟩
  have hJw : JS σ.curThread I σ w0.2 := js_getMessageInfo _ σ hJ0 w0 hw0
  have hJs : JS σ.curThread I σ s := js_invF _ _ _ w0.2 hJw _ has
  have hJ' : JS σ.curThread I σ s' := js_invE _ _ _ _ a s hJs _ hbs
  have hq0 : QVv w0.2 = QVv σ := qv_getMessageInfo (V := QVv σ) σ.curThread σ rfl w0 hw0
  have hq1 : QVv s = QVv σ := qv_invF (V := QVv σ) σ.curThread cptr w0.1 w0.2 hq0 _ has
  have hq2 : QVv s' = QVv σ := qv_invE (V := QVv σ) fp cptr σ.curThread w0.1 a s hq1 _ hbs
  have hV' : VB s' := vb_kz hV hJ'.1 hq2
  have hSi : SInvQ.Simple s' := hJ'.2.2.2.1.2.2.1
  have hVu : VB u.2 := vb_restart hV' hSi (kz_curThread hJ'.1) hu
  have hP : PFacts I u.2 := pfacts_restart hRT hO hS hJ' hu
  have hBu := hB w0 hw0 a s b s' has hbs u hu
  cases b with
  | invokeDomain d =>
    cases d with
    | invokeDomainSet t dd =>
      exact sr_of_vb hVu hP.1.1.1 hP.1.2.1.2.2.1 hP.2.1 t
    | _ => trivial
  | invokeReply r g => exact hBu
  | _ => trivial

/-- **`handle_invocation` keeps `Rdy`** with every perform input but Reply's discharged: rd8j's
`rd_fl4HandleInvocationR` with carried facts (`UF`, `VB`) and `PerfInB` (Reply only). -/
theorem rd_fl4HandleInvocationRV (rep calling blocking don fp : Bool) (cptr : CapRef) (I : ObjRef)
    (σ : State Unit) (hRB : B8f.RB σ.curThread I σ) (hRT : RdyT σ σ.curThread) (hO : Sched.OffReady σ)
    (hS : Suff σ) (hF : FhAll σ) (hU : UF σ) (hV : VB σ) (hP : PerfInB fp cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run σ).1, Rdy y.2 :=
  rd_fl4HandleInvocationRN rep calling blocking don fp cptr I σ hRB hRT hO hS hF hU
    (perfInN_of fp cptr I σ hRB hRT hO hS hV hP)

end

end Fl4Proofs.P3.SInvR.B8n
