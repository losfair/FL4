/-
P3 (DESIGN.md §9), invariant line G1 (rd8h, lead item after rd11b):
**`handle_fault` keeps `Rdy`: rd11b's `RdF` discharged** (spec side only,
outside the JAtZ cone).

* `HB t s := Rdy ∧ RdyT t ∧ T1 ∧ Simple ∧ ScInv` (the faulting thread `t`
  ready).
* `fh_facts`: a write of `t`'s TCB keeping its SC, domain and priority keeps
  `RdyT t`, `T1` and sb2's `ScFwd`.
* `rd_sendFaultIpc`: the fault write (rd's `rd_threadSet_r`: `t` is `RdyT`),
  then rd8d's `rd_sendIpc_d` (sender `RdyT`, `T1`, `Simple`, `ScFwd` at that
  state); a null handler returns.
* **`rd_hf`**: `handle_fault t ex` from `HB t` (no handler: rd's
  `set_thread_state Inactive`).
* `hb_handleVmFault`: `HB t` along `handle_vm_fault` (a machine read and a
  register read of `t`, then the fault), so the caught `handle_fault` starts
  from `HB t`.
* `hb_bs`: rd10's `BS` (the true front outcome) gives `HB ct` with `T1`: ct is
  bound to an active SC (`CAx`), that SC is `cur_sc` (`CurScT`), whose head
  is not after the current time (`OffReady`).
* **`rd_handleFault ev σ (hEF : A8.EF σ) (h1 : T1 σ) : A11b.RdF ev σ`**
  (`T1` across update_time_stamp: heap and queues fixed).
-/
import Fl4Proofs.P3.SpecInvRd8hB
import Fl4Proofs.P3.SpecInvRd11bB
import Fl4Proofs.P3.SpecInvRd8dA
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

/-- The faulting thread's bundle. -/
def HB (t : ObjRef) (s : State Unit) : Prop :=
  Rdy s ∧ RdyT s t ∧ T1 s ∧ Simple s ∧ SInvB.ScInv s

theorem fh_facts {s s' : State Unit} {t : ObjRef} {x x' : Tcb} (hx : s.kheap t = some (.tcb x))
    (hk' : s'.kheap = Function.update s.kheap t (some (.tcb x'))) (hq : s'.readyQueues = s.readyQueues)
    (htm : s'.curTime = s.curTime)
    (hsc : x'.tcbSchedContext = x.tcbSchedContext) (hd : x'.tcbDomain = x.tcbDomain)
    (hp : x'.tcbPriority = x.tcbPriority) (hT : RdyT s t) (h1 : T1 s) (hF : SInvB.ScFwd s) :
    RdyT s' t ∧ T1 s' ∧ SInvB.ScFwd s' := by
  have hk : ∀ q, q ≠ t → s'.kheap q = s.kheap q := fun q hq => by rw [hk']; exact Function.update_of_ne hq _ _
  have ht : s'.kheap t = some (.tcb x') := by rw [hk']; exact Function.update_self _ _ _
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x0, c, y, n, hx0, hc, hy, ha, hr⟩ := hT
    rw [hx] at hx0; cases hx0
    have hct : c ≠ t := by rintro rfl; rw [hx] at hy; cases hy
    exact ⟨x', c, y, n, ht, hsc.trans hc, by rw [hk c hct]; exact hy, ha, by rw [htm]; exact hr⟩
  · intro d p u hu
    rw [hq] at hu
    obtain ⟨x0, hx0, h1d, h1p⟩ := h1 d p u hu
    by_cases e : u = t
    · subst e; rw [hx] at hx0; cases hx0; exact ⟨x', ht, hd.trans h1d, hp.trans h1p⟩
    · exact ⟨x0, by rw [hk u e]; exact hx0, h1d, h1p⟩
  · intro p y n u hy hu
    have hpt : p ≠ t := by rintro rfl; rw [ht] at hy; cases hy
    rw [hk p hpt] at hy
    obtain ⟨x0, hx0, hs0⟩ := hF p y n u hy hu
    by_cases e : u = t
    · subst e; rw [hx] at hx0; cases hx0; exact ⟨x', ht, hsc.trans hs0⟩
    · exact ⟨x0, by rw [hk u e]; exact hx0, hs0⟩

/-- **`send_fault_ipc`** from `HB t`. -/
theorem rd_sendFaultIpc (t : ObjRef) (cap : Cap) (ex : Fault) (cd : Bool) (s : State Unit) (h : HB t s) :
    ∀ y ∈ (sendFaultIpc (Z := Unit) t cap ex cd s).1, Rdy y.2 := by
  intro y hy
  unfold sendFaultIpc at hy
  cases cap
  case endpointCap r b rs =>
    obtain ⟨w1, hw1, hy⟩ := hy
    have r1 : Rdy w1.2 := rd_threadSet_r (fun tcb => { tcb with tcbFault := some ex }) t s (fun _ => rfl) h.2.1 h.1 w1 hw1
    obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hw1
    obtain ⟨f1, f2, f3⟩ := fh_facts hx (x' := { x with tcbFault := some ex }) (s' := w1.2) (by rw [e])
      (by rw [e]) (by rw [e]) rfl rfl rfl h.2.1 h.2.2.1 h.2.2.2.2.1.2
    have hA : Simple w1.2 := by rw [e]; exact h.2.2.2.1
    obtain ⟨w2, hw2, hy⟩ := hy
    have r2 := B8d.rd_sendIpc_d true false _ _ _ cd t _ w1.2 f1 f2 hA f3 r1 w2 hw2
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact r2
  case nullCap => rw [Set.mem_singleton_iff.1 hy]; exact h.1
  all_goals exact hy.elim

/-- **`handle_fault t ex`** from `HB t`. -/
theorem rd_hf (t : ObjRef) (ex : Fault) (s : State Unit) (h : HB t s) :
    ∀ z ∈ (handleFault (Z := Unit) t ex s).1, Rdy z.2 := by
  intro z hz
  unfold handleFault at hz
  obtain ⟨w0, hw0, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hw0
  obtain ⟨⟨cap, s1⟩, hw1, hz⟩ := hz
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hw1
  simp only at e1; subst e1
  obtain ⟨w2, hw2, hz⟩ := hz
  obtain ⟨xt, -, rfl⟩ := q1_mem_threadGet hw2
  obtain ⟨⟨b, s3⟩, hw3, hz⟩ := hz
  have r3 : Rdy s3 := rd_sendFaultIpc t cap ex _ s1 h _ hw3
  obtain ⟨w4, hw4, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  unfold NonDet.unless at hw4
  split_ifs at hw4
  · rw [Set.mem_singleton_iff.1 hw4]; exact r3
  · unfold handleNoFault at hw4
    exact rd_setThreadState t .inactive trivial s3 r3 w4 hw4

theorem hb_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (hR : RdK m) (hS : SVK.SVM m) (hQ : Q1K m)
    (hI : SInvB.SIK m) : IK (HB t) m := by
  intro s h y hy
  refine ⟨hR s h.1 y hy, rdyT_svs h.2.1 (hS s y hy), hQ s h.2.2.1 y hy, fun u e => ?_, hI s h.2.2.2.2 y hy⟩
  rcases (hS s y hy).2.2 with h' | h' <;> rw [h'] at e
  · exact h.2.2.2.1 u e
  · cases e

theorem hb_handleVmFault (t : ObjRef) (ft : VMFaultType) : IKE (HB t) (handleVmFault (Z := Unit) t ft) := by
  unfold handleVmFault
  refine ike_bind (ike_liftE (ik_doMachineOp (fun _ _ h => h) _)) fun _ => ?_
  refine ike_bind (ike_liftE (hb_of (rd_asUser _ _) (SVK.sv_asUser' _ _) (q1_asUser _ _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_asUser _ _))) fun _ => ?_
  split <;> exact ike_throw _

/-- rd10's `BS` and `T1` give `HB ct`. -/
theorem hb_bs {s : State Unit} (h : A10.BS s) (h1 : T1 s) : HB s.curThread s := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha⟩ := h.ca h.ni
  have hcs : c = s.curSc := by have := h.cs x hx; rw [hc] at this; exact Option.some.inj this
  subst hcs
  have hr : refillReady s.curTime (refillHd y) = true := ready_of_nat (by have := h.off y n hy; omega)
  exact ⟨h.rdy, ⟨x, _, y, n, hx, hc, hy, ha, hr⟩, h1, h.si, h.sc⟩

/-- **rd11b's `RdF` discharged**: `Rdy` after every fault event's handler at a
`true` front outcome, from rd8a's `EF` and ctq's `T1` at the entry. -/
theorem rd_handleFault (ev : Event) (σ : State Unit) (hEF : A8.EF σ) (h1 : T1 σ) : A11b.RdF ev σ := by
  intro v hv ht z hz
  obtain ⟨xt, hct, hst⟩ := hEF.ct
  obtain ⟨-, -, h3⟩ := rd_front hEF.rdy hEF.off hEF.vmt hEF.sc hEF.cs hct hst hEF.q hEF.si hEF.cb hEF.hb
    hEF.ca hEF.ni hv
  obtain ⟨y, hy, e, -⟩ := h3 ht
  have hB := A10.bs_uts hEF hy
  obtain ⟨ek, -, -, -⟩ := SInvO.uts_off hy
  obtain ⟨eq, -, -, -⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  have h1y : T1 y.2 := by
    intro d p u hu; rw [eq] at hu; rw [ek]; exact h1 d p u hu
  have hH : HB y.2.curThread y.2 := hb_bs hB h1y
  rw [e] at hz
  cases ev with
  | unknownSyscall n => exact rd_hf _ _ _ hH z hz
  | userLevelFault w1 w2 => exact rd_hf _ _ _ hH z hz
  | vmFaultEvent ft =>
    simp only [A11b.FH, NonDetE.catch] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw' : HB _ w.2 := hb_handleVmFault _ ft y.2 hH w hw
    rcases w with ⟨_ | a, s1⟩
    · exact rd_hf _ _ _ hw' z hz
    · rw [Set.mem_singleton_iff.1 hz]; exact hw'.1
  | hypervisorEvent hf => exact rd_handleHypervisorFault y.2.curThread hf y.2 hH.1 z hz
  | syscallEvent c => rw [Set.mem_singleton_iff.1 hz]; exact hH.1
  | interrupt => rw [Set.mem_singleton_iff.1 hz]; exact hH.1

end

end Fl4Proofs.P3.SInvR.B8h
