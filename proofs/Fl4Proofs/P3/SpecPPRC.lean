/-
P3 (DESIGN.md §9), CSpace: **the spec's `finalise_cap` keeps `Chg`**
(ScPPR, kp13; l4v `cur_sc_chargeable`), the part of `PPR0` that SpecPPR's
`TR` cannot see for the finalisations that restart threads.

* Finalisations restarting no thread (`NoRestartCap`): SpecPPR's `TR` with
  `chg` (`chg_finaliseCapW`): links only cleared, states set `Inactive`, an
  SC donated only to a `reply_remove` caller which ends inactive.
* An endpoint (`cancel_all_ipc`): IpcFinEpInv's frame `EFr` (`Chg.of_efr`):
  only threads blocked on the endpoint change state, so an inactive thread
  stays inactive. The queued threads' blocking (`EpQB`) is the J layer's
  (IpcCancelAllIpc's `ep_queue_blocked`).
* A notification (unbinds and `cancel_all_signals`): IpcFinNtfnInv's
  `finNtfn_spec` frame `NFr` (`Chg.of_nfr`).
* An IRQ handler: `cap_delete_one` of the handler's slot (reads, then
  `fast_finalise` of the cap there as above, then `empty_slot`).
-/
import Fl4Proofs.P3.SpecPPR
import Fl4Proofs.P3.IpcFinEpInv
import Fl4Proofs.P3.IpcFinNtfnInv
open Classical

namespace Fl4Proofs.P3.PPS
open Fl4Spec

noncomputable section

/-- `Chg` across endpoint `e`'s finalisation frame. -/
theorem Chg.of_efr {e : ObjRef} {P : ObjRef → Prop} {σ σ' : State Unit} (hC : Chg σ) (F : Sched.EFr e P σ σ') :
    Chg σ' := by
  intro u y hu hs
  rw [F.sk.csc] at hs
  rw [F.sk.ct]
  rcases F.kh u with e' | ⟨o, o', h1, h2, hc⟩
  · rw [e'] at hu; exact hC u y hu hs
  · rw [h2] at hu; cases hu
    rcases hc with ⟨x, st, rfl, e2, hst⟩ | ⟨_, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    rcases hC u x h1 hs with h | h
    · exact Or.inl h
    · right
      show st = .inactive
      rw [hst.st (by rw [h]; simp [epBlocked])]; exact h

/-- `Chg` across notification `r`'s finalisation frame. -/
theorem Chg.of_nfr {q : Bool} {r : ObjRef} {σ σ' : State Unit} (hC : Chg σ) (F : Sched.NFr q r σ σ') :
    Chg σ' := by
  intro u y hu hs
  rw [F.sk.csc] at hs
  rw [F.sk.ct]
  rcases F.kh u with e' | ⟨o, o', h1, h2, hc⟩
  · rw [e'] at hu; exact hC u y hu hs
  · rw [h2] at hu; cases hu
    rcases hc with ⟨x, st, bn, ar, rfl, e2, hst, -⟩ | ⟨_, _, _, _, -, e2, -⟩ | ⟨_, _, -, e2, -⟩ <;> cases e2
    rcases hC u x h1 hs with h | h
    · exact Or.inl h
    · right
      show st = .inactive
      rcases hst with ⟨e3, -⟩ | ⟨-, e3, -⟩
      · rw [e3]; exact h
      · rw [h] at e3; cases e3

/-- **The endpoints' queued threads blocked on them, with `EpPre`** (the J
layer's: `JAtZ.epFinPre`, IpcCancelAllIpc's `ep_queue_blocked`). -/
def EpQB (σ : State Unit) : Prop :=
  ∀ e x, σ.kheap e = some (.endpoint x) → Sched.EpPre σ e ∧
    ∀ u ∈ x.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧ epBlocked xu.tcbState = some e

theorem chg_cancelAllIpc {σ σ' : State Unit} {e : ObjRef} (hI : Sched.Inv σ) (hB : Sched.BlockedScActive σ)
    (hQ : EpQB σ) (hC : Chg σ) (hm : ((), σ') ∈ (cancelAllIpc (Z := Unit) e σ).1) : Chg σ' := by
  have hm0 := hm
  unfold cancelAllIpc at hm0
  obtain ⟨⟨x, σ1⟩, h1, -⟩ := hm0
  obtain ⟨hk, -⟩ := Sched.getEndpoint_mem h1
  obtain ⟨-, -, F, -⟩ := Sched.inv_cancelAllIpc (P := fun _ => True) hI hB (hQ e x hk).1
    (fun x' hx' u hu => by
      obtain ⟨xu, h1, h2⟩ := (hQ e x' hx').2 u hu
      exact ⟨xu, h1, h2, fun _ => trivial⟩) hm
  exact Chg.of_efr hC F

theorem getNtfnRef_mem {σ : State Unit} {r : ObjRef} {f : Notification → Option ObjRef}
    {x : Option ObjRef × State Unit} (hx : x ∈ (getNtfnObjRef (Z := Unit) f r σ).1) :
    ∃ n, σ.kheap r = some (.notification n) := by
  unfold getNtfnObjRef getSkObjRef getSimpleKo at hx
  obtain ⟨⟨n, σ2⟩, h2, -⟩ := hx
  obtain ⟨⟨o, σ1⟩, h1, hx⟩ := h2
  have e1 : σ1 = σ := Sched.getsThe_state h1
  subst σ1
  have hko : σ.kheap r = some o := by
    simp only [getObject, NonDet.getsThe, readObject] at h1
    cases hk : σ.kheap r with
    | none => rw [hk] at h1; exact h1.elim
    | some v => rw [hk] at h1; rw [(Prod.mk.inj (Set.mem_singleton_iff.1 h1)).1]
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy
  simp only at hx
  revert hx
  cases hpi : partialInv KernelObject.notification o with
  | none => intro hx; exact hx.elim
  | some a =>
    intro _
    exact ⟨a, by rw [hko, ← Sched.partialInv_eq hpi]⟩

/-- **A final notification cap's work keeps `Chg`.** -/
theorem chg_ntfnBody {σ σ' : State Unit} {r : ObjRef} (hI : Sched.Inv σ) (hB : Sched.BlockedScActive σ)
    (hV : Sched.SchedValid σ) (hC : Chg σ)
    (hm : ((), σ') ∈ ((do
      schedContextMaybeUnbindNtfn (Z := Unit) r
      unbindMaybeNotification (Z := Unit) r
      cancelAllSignals (Z := Unit) r) σ).1) : Chg σ' := by
  obtain ⟨⟨⟨⟩, σ1⟩, h1, hm⟩ := hm
  obtain ⟨⟨⟨⟩, σ2⟩, h2, h3⟩ := hm
  have h10 := h1
  unfold schedContextMaybeUnbindNtfn at h10
  obtain ⟨z, hz, -⟩ := h10
  obtain ⟨n, hkn⟩ := getNtfnRef_mem hz
  obtain ⟨-, -, F, -⟩ := Sched.finNtfn_spec hI hB hV hkn (fun c hc => hI.ntfnSc r n c hkn hc)
    (fun t ht => hV.ntfnTcb r n t hkn ht) h1 h2 h3
  exact Chg.of_nfr hC F

/-- **`fast_finalise` keeps `Chg`** (`cap_delete_one`'s). -/
theorem chg_fastFinalise {σ : State Unit} {cp : Cap} {b : Bool} {y : Unit × State Unit}
    (hI : Sched.Inv σ) (hB : Sched.BlockedScActive σ) (hV : Sched.SchedValid σ) (hQ : EpQB σ) (hC : Chg σ)
    (hm : y ∈ (fastFinalise (Z := Unit) cp b σ).1) : Chg y.2 := by
  have hct := (Vs.dk_fastFinalise' cp b).ct hm
  cases cp with
  | replyCap r _ =>
    simp only [fastFinalise] at hm
    exact Chg.of_tr hC (tks_when _ (tks_replyBody r) (E := fun _ => False) (W := True) σ rfl
      (rqRun_of_inv hI) y hm) hct
  | endpointCap r _ _ =>
    simp only [fastFinalise, NonDet.when] at hm
    split at hm
    · obtain ⟨⟨⟩, σ'⟩ := y; exact chg_cancelAllIpc hI hB hQ hC hm
    · rw [Set.mem_singleton_iff.1 hm]; exact hC
  | notificationCap r _ _ =>
    simp only [fastFinalise, NonDet.when] at hm
    split at hm
    · obtain ⟨⟨⟩, σ'⟩ := y; exact chg_ntfnBody hI hB hV hC hm
    · rw [Set.mem_singleton_iff.1 hm]; exact hC
  | nullCap =>
    simp only [fastFinalise] at hm
    rw [Set.mem_singleton_iff.1 hm]; exact hC
  | _ => simp only [fastFinalise] at hm; exact hm.elim

/-- **`deleting_irq_handler` keeps `Chg`.** -/
theorem chg_deletingIrqHandler {σ : State Unit} {irq : Irq} {y : Unit × State Unit}
    (hI : Sched.Inv σ) (hB : Sched.BlockedScActive σ) (hV : Sched.SchedValid σ) (hQ : EpQB σ) (hC : Chg σ)
    (hm : y ∈ (deletingIrqHandler (Z := Unit) irq σ).1) : Chg y.2 := by
  unfold deletingIrqHandler getIrqSlot at hm
  obtain ⟨y0, hy0, hm⟩ := hm
  have e0 : y0.2 = σ := Vs.dk_gets (f := fun s : State Unit => s) _ σ y0 hy0
  unfold capDeleteOne at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  have e1 : y1.2 = y0.2 := fk_getCapG (fun s => s) _ _ y1 hy1
  unfold NonDet.unless at hm
  beta_reduce at hm
  split at hm
  · rw [Set.mem_singleton_iff.1 hm]; simp only; rw [e1, e0]; exact hC
  · obtain ⟨y2, hy2, hm⟩ := hm
    have e2 : y2.2 = y1.2 := Vs.dk_gets (f := fun s : State Unit => s) _ _ y2 hy2
    obtain ⟨y3, hy3, hm⟩ := hm
    rw [e2, e1, e0] at hy3
    have hC3 := chg_fastFinalise hI hB hV hQ hC hy3
    exact Chg.of_tr hC3 (tk_emptySlot' (E := fun _ => False) (W := True) _ _ y3.2 rfl y hm)
      ((Vs.dk_emptySlot' _ _).ct hm)

/-- **`finalise_cap` keeps `Chg`** from an `Inv` state with the queue facts
(module docstring). -/
theorem chg_finaliseCap {cp : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hI : Sched.Inv σ) (hB : Sched.BlockedScActive σ) (hV : Sched.SchedValid σ) (hQ : EpQB σ) (hC : Chg σ)
    (hx : x ∈ (finaliseCap (Z := Unit) cp b σ).1) : Chg x.2 := by
  have hct := (Vs.dk_finaliseCap cp b).ct hx
  cases cp with
  | endpointCap r _ _ =>
    simp only [finaliseCap, NonDet.liftM, NonDet.when] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    split at hy
    · obtain ⟨⟨⟩, σ'⟩ := y; exact chg_cancelAllIpc hI hB hQ hC hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hC
  | notificationCap r _ _ =>
    simp only [finaliseCap, NonDet.liftM, NonDet.when] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    split at hy
    · obtain ⟨⟨⟩, σ'⟩ := y; exact chg_ntfnBody hI hB hV hC hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hC
  | irqHandlerCap irq =>
    simp only [finaliseCap] at hx
    split at hx
    · obtain ⟨y, hy, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      exact chg_deletingIrqHandler hI hB hV hQ hC hy
    · rw [Set.mem_singleton_iff.1 hx]; exact hC
  | nullCap => exact chg_finaliseCapW hI hx trivial hC hct
  | untypedCap _ _ _ _ => exact chg_finaliseCapW hI hx trivial hC hct
  | replyCap _ _ => exact chg_finaliseCapW hI hx trivial hC hct
  | cnodeCap _ _ _ => exact chg_finaliseCapW hI hx trivial hC hct
  | threadCap _ => exact chg_finaliseCapW hI hx trivial hC hct
  | domainCap => exact chg_finaliseCapW hI hx trivial hC hct
  | schedContextCap _ _ => exact chg_finaliseCapW hI hx trivial hC hct
  | schedControlCap => exact chg_finaliseCapW hI hx trivial hC hct
  | zombie _ _ _ => exact chg_finaliseCapW hI hx trivial hC hct
  | irqControlCap => exact chg_finaliseCapW hI hx trivial hC hct
  | archObjectCap _ => exact chg_finaliseCapW hI hx trivial hC hct

end

end Fl4Proofs.P3.PPS
