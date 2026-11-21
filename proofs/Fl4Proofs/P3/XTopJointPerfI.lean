/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch28): **the IRQ handler set /
clear performs keep `CQ` and `BI`** (spec side), removing XTopJointPerfW's
`JPerfIrqHypQ` / `JPerfIrqHypB` [W].

`invoke_irq_handler`'s set / clear run `cap_delete_one` of the IRQ's node
slot (then, for set, `cap_insert` of the given cap into it). From a state
where that slot holds null or a notification cap (`IrqSlotNC`), the deletion
is `fast_finalise` of a notification cap: the two unbinds
(`sched_context_maybe_unbind_ntfn`, `unbind_maybe_notification`: they write
only the notification's SC / bound-TCB fields, the SC's notification field
and the TCB's bound notification) and `cancel_all_signals` (restarts the
threads queued on the notification, `≠ ct` as `ct` waits on no notification:
MidRun's `NQ`, kept by the unbinds via the notification view `nV`), then
`empty_slot` with a null cleanup. All of it is an `sV` frame (`BI` kept) and
keeps `CQ` (`KF` + `QK`, the restarted threads `≠ ct`).

* `IrqSlotNC σ`: every IRQ node slot holds null or a notification cap.
  `JPerfIrqSlotHyp cptr σ` [J]: `IrqSlotNC` at the `MidPerfAt` states of the
  IRQ handler performs (l4v `valid_irq_node` / the IRQ handler slots' contents
  (`cte_wp_at (is_ntfn_cap or null)` of the IRQ node, kept by every
  operation); FL4's `IrqSlotOK` / SpecGlob's `irq` at the dispatch state; the
  first phase writes no cap). True in reachable states.
* `nv_*`: the unbinds keep `nV`; `cq_cancelAllSignals`, `cq_ntfnFin`,
  `sck_ntfnFin`, `post_capDeleteOne`, `irqH_post`.
* `jPerfIrqHypQ_of`, `jPerfIrqHypB_of`; `jMidPerfHypQ_of2` / `jMidPerfHypB_of2`
  (`JMidPerfHypQ` / `JMidPerfHypB` from `JPerfRegHyp` [J] + `JPerfIrqSlotHyp`
  [J]).
-/
import Fl4Proofs.P3.XTopJointPerfW
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-! ## The notification view across the unbinds -/

theorem aType_eq_ntfn {o : KernelObject} (h : aType o = .aNTFN) : ∃ n, o = .notification n := by
  cases o with
  | notification n => exact ⟨n, rfl⟩
  | cnode sz cs => by_cases hw : wellFormedCnodeN sz cs <;> simp [aType, hw] at h
  | schedContext y n => by_cases hw : validSchedContextSize n <;> simp [aType, hw] at h
  | _ => simp [aType] at h

theorem nv_setObject_nn (p : ObjRef) (o : KernelObject) (ho : ∀ n, o ≠ .notification n) :
    FK nV (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨⟨k, hk, hA⟩, e⟩ := setObject_out hx
  have hk' : ∀ n, k ≠ .notification n := by
    intro n hn
    subst hn
    obtain ⟨n', rfl⟩ := aType_eq_ntfn (hA.symm.trans rfl)
    exact ho n' rfl
  rw [e]
  funext q
  unfold nV
  simp only [Function.update_apply]
  by_cases hq : q = p
  · subst hq
    rw [if_pos rfl, hk]
    cases o <;> cases k <;> simp_all
  · rw [if_neg hq]

theorem nv_updSk_ntfn (g : (Option ObjRef → Option ObjRef) → Notification → Notification)
    (hg : ∀ f n, (g f n).ntfnObj = n.ntfnObj) (r : ObjRef) (v : Option ObjRef) :
    FK nV (updateSkObjRef (Z := Unit) KernelObject.notification g r v) := by
  intro σ x hx
  obtain ⟨⟨n, s1⟩, h1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := getSimpleKo_mem h1
  simp only at e1 hk hx
  subst e1
  have e := Notif.setNotification_eq (Z := Unit) (g (fun _ => v) n) hk
  simp only [setNotification] at e
  rw [e] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext q
  unfold nV
  by_cases hq : q = r
  · subst hq; simp [Notif.updK, hk, hg]
  · simp [Notif.updK, Function.update_of_ne hq]

theorem nv_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (r : ObjRef) :
    FK nV (getSkObjRef (Z := Unit) C f r) := by
  unfold getSkObjRef getSimpleKo; repeat' dk_step0

theorem nv_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) :
    FK nV (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  refine dk_bind (dk_getObject _) fun o => ?_
  cases o with
  | schedContext sc n => exact nv_setObject_nn _ _ (fun _ h => by cases h)
  | _ => exact dk_fail

theorem nv_threadSet (f : Tcb → Tcb) (t : ObjRef) : FK nV (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact dk_bind (dk_getsThe _) fun _ => nv_setObject_tcb _ _

theorem nv_schedContextMaybeUnbindNtfn (n : ObjRef) : FK nV (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn
  refine dk_bind (nv_getSkObjRef KernelObject.notification Notification.ntfnSc n) fun o => ?_
  refine dk_maybeM (fun sc => ?_) o
  exact dk_bind (nv_updSk_ntfn ntfnScUpdate (fun _ _ => rfl) n none) fun _ =>
    nv_updateSchedContext sc (scNtfnUpdate fun _ => none)

theorem nv_unbindMaybeNotification (n : ObjRef) : FK nV (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification
  refine dk_bind (nv_getSkObjRef KernelObject.notification Notification.ntfnBoundTcb n) fun o => ?_
  refine dk_maybeM (fun t => ?_) o
  exact dk_bind (nv_updSk_ntfn ntfnBoundTcbUpdate (fun _ _ => rfl) n none) fun _ =>
    nv_threadSet (tcbBoundNotificationUpdate fun _ => none) t

/-! ## The SC view (`BI`) -/

theorem sck_schedContextMaybeUnbindNtfn (n : ObjRef) : SV (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; sck_auto2

theorem sck_unbindMaybeNotification (n : ObjRef) : SV (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; sck_auto2

theorem sck_removeAndRestartNtfnQueuedThread (t n : ObjRef) :
    SV (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; sck_auto2

theorem sck_cancelAllSignals (n : ObjRef) : SV (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals
  repeat' (first | exact sck_removeAndRestartNtfnQueuedThread _ _ | sck_leaf | dk_step0 | fv_unfold)

theorem sck_emptySlotN (sl : CslotPtr) : SV (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot postCapDeletion; sck_auto2

/-- **A notification cap's `fast_finalise` is an `sV` frame.** -/
theorem sck_ntfnFin (r : ObjRef) (b : Badge) (rs : CapRights) (fin : Bool) :
    SV (fastFinalise (Z := Unit) (.notificationCap r b rs) fin) := by
  simp only [fastFinalise, NonDet.when]
  split
  · exact dk_bind (sck_schedContextMaybeUnbindNtfn r) fun _ =>
      dk_bind (sck_unbindMaybeNotification r) fun _ => sck_cancelAllSignals r
  · exact dk_pure' _

/-! ## `CQ` across `cancel_all_signals` -/

section
variable {ct : ObjRef}

theorem pq_mapMx_mem {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ (xs : List α), (∀ a ∈ xs, PQ ct (g a)) → PQ ct (NonDet.mapMx g xs)
  | [], _ => pq_of (dk_pure' _) (PPNQ.qk_pure' _)
  | a :: xs', h => pq_bind (h a (List.mem_cons_self ..)) fun _ =>
      pq_mapMx_mem xs' fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem pq_removeAndRestartNtfnQueuedThread {t : ObjRef} (n : ObjRef) (ht : t ≠ ct) :
    PQ ct (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  refine pq_of ?_ (PPNQ.qk_removeAndRestartNtfnQueuedThread n ht)
  unfold removeAndRestartNtfnQueuedThread
  exact dk_bind (kf_tcbNtfnDequeue' _ _) fun _ => dk_bind (kf_setThreadState _ _ ht) fun _ =>
    dk_bind (kf_getTcbObjRef' _ _) fun _ => dk_bind (kf_ifSporadicCurScAssertRefillUnblockCheck' _) fun _ =>
      kf_possibleSwitchTo' _

/-- **`cancel_all_signals` keeps `CQ`** from a state where `ct` waits on no
notification. -/
theorem cq_cancelAllSignals (r : ObjRef) (σ : State Unit) (x : Unit × State Unit) (hs : CQ ct σ ∧ NQ ct σ)
    (hx : x ∈ (cancelAllSignals (Z := Unit) r σ).1) : CQ ct x.2 := by
  unfold cancelAllSignals at hx
  obtain ⟨⟨n, s1⟩, h1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := getSimpleKo_mem h1
  simp only at e1 hk hx
  subst e1
  have hc : ∀ q, n.ntfnObj = .waitingNtfn q → ct ∉ q := fun q hq => hs.2 r n q hk hq
  revert hx hc
  rcases n with ⟨o, b, sc⟩
  cases o with
  | waitingNtfn q =>
    intro hx hc
    exact (pq_bind (pq_mapMx_mem _ fun t ht => pq_removeAndRestartNtfnQueuedThread r
      (fun h => hc q rfl (by subst h; exact ht))) fun _ =>
        pq_of (kf_rescheduleRequired') PPNQ.qk_rescheduleRequired') _ x hs.1 hx
  | _ => intro hx _; rw [Set.mem_singleton_iff.1 hx]; exact hs.1

theorem pwq_of {α : Type} {m : NonDet (State Unit) α} (h1 : KF ct m) (h2 : PPNQ.QK ct m) (h3 : FK nV m) :
    PW (fun σ => CQ ct σ ∧ NQ ct σ) m :=
  fun σ x hs hx => ⟨⟨CtRs.of_ctV (h1 σ x hx) hs.1.1, h2 σ x hx hs.1.2⟩, NQ.of_nV (h3 σ x hx) hs.2⟩

/-- **A notification cap's `fast_finalise` keeps `CQ`** from `CQ ∧ NQ`. -/
theorem cq_ntfnFin {r : ObjRef} {b : Badge} {rs : CapRights} {fin : Bool} {σ : State Unit}
    {y : Unit × State Unit} (hs : CQ ct σ ∧ NQ ct σ)
    (hy : y ∈ (fastFinalise (Z := Unit) (.notificationCap r b rs) fin σ).1) : CQ ct y.2 := by
  simp only [fastFinalise, NonDet.when] at hy
  split at hy
  · obtain ⟨y1, h1, hy⟩ := hy
    obtain ⟨y2, h2, h3⟩ := hy
    have i1 := pwq_of (kf_schedContextMaybeUnbindNtfn' r) (PPNQ.qk_schedContextMaybeUnbindNtfn' r)
      (nv_schedContextMaybeUnbindNtfn r) σ y1 hs h1
    have i2 := pwq_of (kf_unbindMaybeNotification' r) (PPNQ.qk_unbindMaybeNotification' r)
      (nv_unbindMaybeNotification r) _ y2 i1 h2
    exact cq_cancelAllSignals r _ y i2 h3
  · rw [Set.mem_singleton_iff.1 hy]; exact hs.1

end

/-! ## `cap_delete_one` of an IRQ slot and the perform -/

/-- Every IRQ node slot holds null or a notification cap. -/
def IrqSlotNC (σ : State Unit) : Prop :=
  ∀ irq c σ', (c, σ') ∈ (getCap (Z := Unit) (σ.interruptIrqNode irq, []) σ).1 →
    c = .nullCap ∨ ∃ r b rs, c = .notificationCap r b rs

/-- **`cap_delete_one` of a slot holding null or a notification cap.** -/
theorem post_capDeleteOne {I I2 : State Unit → Prop} {sl : CslotPtr} {σ : State Unit} (hs : I σ)
    (hI2 : ∀ s, I s → I2 s)
    (hc : ∀ c σ', (c, σ') ∈ (getCap (Z := Unit) sl σ).1 → c = .nullCap ∨ ∃ r b rs, c = .notificationCap r b rs)
    (hF : ∀ r b rs fin σ' y, I σ' → y ∈ (fastFinalise (Z := Unit) (.notificationCap r b rs) fin σ').1 → I2 y.2)
    (hE : PW I2 (emptySlot (Z := Unit) sl .nullCap)) :
    ∀ x ∈ (capDeleteOne (Z := Unit) sl σ).1, I2 x.2 := by
  intro x hm
  unfold capDeleteOne at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  have e1 : y1.2 = σ := fk_getCapG (fun s => s) _ _ y1 hy1
  have hc1 := hc y1.1 y1.2 hy1
  unfold NonDet.unless at hm
  beta_reduce at hm
  split at hm
  · rw [Set.mem_singleton_iff.1 hm]; simp only; rw [e1]; exact hI2 _ hs
  · rename_i hn
    rcases hc1 with h0 | ⟨r, b, rs, h0⟩
    · exact absurd h0 hn
    obtain ⟨y2, hy2, hm⟩ := hm
    have e2 : y2.2 = y1.2 := Vs.dk_gets (f := fun s : State Unit => s) _ _ y2 hy2
    obtain ⟨y3, hy3, hm⟩ := hm
    rw [e2, e1, h0] at hy3
    exact hE y3.2 x (hF r b rs _ σ y3 hs hy3) hm

/-- **The IRQ handler set / clear perform** from an `I` state whose IRQ node
slots hold null or notification caps. -/
theorem irqH_post {I I2 : State Unit → Prop} (hI2 : ∀ s, I s → I2 s)
    (hF : ∀ r b rs fin σ' y, I σ' → y ∈ (fastFinalise (Z := Unit) (.notificationCap r b rs) fin σ').1 → I2 y.2)
    (hE : ∀ sl, PW I2 (emptySlot (Z := Unit) sl .nullCap))
    (hC : ∀ c s d, PW I2 (capInsert (Z := Unit) c s d))
    {don : Bool} {i : IrqHandlerInvocation} (hW : PerfW (.invokeIRQHandler i)) {σ1 : State Unit}
    (hs : I σ1) (hc : IrqSlotNC σ1) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don (.invokeIRQHandler i)).run σ1).1, I2 y.2 := by
  have hm : ∀ x ∈ (invokeIrqHandler (Z := Unit) i σ1).1, I2 x.2 := by
    intro x hx
    cases i with
    | aCKIrq irq => exact hW.elim
    | setIRQHandler irq cap slot =>
      simp only [invokeIrqHandler] at hx
      obtain ⟨y0, hy0, hx⟩ := hx
      obtain rfl : y0 = ((σ1.interruptIrqNode irq, []), σ1) := hy0
      obtain ⟨y1, hy1, hx⟩ := hx
      exact hC _ _ _ y1.2 x (post_capDeleteOne hs hI2 (hc irq) hF (hE _) y1 hy1) hx
    | clearIRQHandler irq =>
      simp only [invokeIrqHandler] at hx
      obtain ⟨y0, hy0, hx⟩ := hx
      obtain rfl : y0 = ((σ1.interruptIrqNode irq, []), σ1) := hy0
      exact post_capDeleteOne hs hI2 (hc irq) hF (hE _) x hx
  simp only [fl4PerformInvocation]
  have h1 := post_liftE (ε := Unit) hm
  refine post_bindE (R := I2) h1 (fun _ h => h) fun _ s' hmm y hy => ?_
  rw [NonDetE.returnOk, ExceptT.run_pure] at hy
  rw [Set.mem_singleton_iff.1 hy]
  exact h1 _ hmm

/-! ## The premises -/

/-- **[J] The IRQ node slots hold null or notification caps** at the states
where the IRQ handler performs start on a run of the first-phase invocation
from the dispatch state `σ` (module docstring; l4v `valid_irq_node` with the
IRQ handler slots' contents, FL4's `IrqSlotOK`). -/
def JPerfIrqSlotHyp (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ i σ1, MidPerfAt cptr σ (.invokeIRQHandler i) σ1 → IrqSlotNC σ1

/-- **`JPerfIrqHypQ` holds** from `CQ ∧ NQ` at the dispatch state and the
IRQ slot fact. -/
theorem jPerfIrqHypQ_of {don : Bool} {cptr : CapRef} {σ : State Unit} (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hIs : JPerfIrqSlotHyp cptr σ) : JPerfIrqHypQ don cptr σ := by
  intro i σ1 hA hW y hy
  exact irqH_post (I := fun s => CQ σ.curThread s ∧ NQ σ.curThread s) (fun _ h => h.1)
    (fun _ _ _ _ _ _ hs' hy' => cq_ntfnFin hs' hy')
    (fun _ => pq_of (kf_emptySlot' _ _) (PPNQ.qk_emptySlot' _ _))
    (fun _ _ _ => pq_of (kf_capInsert _ _ _) (qk_of_qv (qv_capInsert _ _ _)))
    hW (midPerfAt_cq hA hs hq) (hIs i σ1 hA) y hy

/-- **`JPerfIrqHypB` holds** from the IRQ slot fact. -/
theorem jPerfIrqHypB_of {don : Bool} {cptr : CapRef} {σ : State Unit} (hIs : JPerfIrqSlotHyp cptr σ) :
    JPerfIrqHypB don cptr σ := by
  intro i σ1 hA hW hb y hy
  exact irqH_post (I := BI σ.curThread) (fun _ h => h)
    (fun r b rs fin σ' y hs' hy' => BI.of_sV (sck_ntfnFin r b rs fin σ' y hy') hs')
    (fun sl s x h hx => BI.of_sV (sck_emptySlotN sl s x hx) h)
    (fun c s d s' x h hx => BI.of_sV (sck_capInsert c s d s' x hx) h)
    hW hb (hIs i σ1 hA) y hy

/-- **`JMidPerfHypQ` from the two [J] facts** (`JPerfRegHyp`, `JPerfIrqSlotHyp`). -/
theorem jMidPerfHypQ_of2 {don : Bool} {cptr : CapRef} {σ : State Unit} (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hR : JPerfRegHyp cptr σ) (hIs : JPerfIrqSlotHyp cptr σ) :
    JMidPerfHypQ don cptr σ :=
  jMidPerfHypQ_of hs hq hR (jPerfIrqHypQ_of hs hq hIs)

/-- **`JMidPerfHypB` from the two [J] facts.** -/
theorem jMidPerfHypB_of2 {don : Bool} {cptr : CapRef} {σ : State Unit} (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hR : JPerfRegHyp cptr σ) (hIs : JPerfIrqSlotHyp cptr σ) :
    JMidPerfHypB don cptr σ :=
  jMidPerfHypB_of hs hq hR (jPerfIrqHypB_of hIs)

end

end Fl4Proofs.P3.MidRun
