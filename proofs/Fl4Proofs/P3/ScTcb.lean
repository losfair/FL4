/-
P3 (DESIGN.md §9), scheduling contexts: **the scheduler-side TCB labels** of
`tcb::decode` with the MDB invariants (`TcbOKF`, TcbDecode.lean; every path
keeps the slot words, so `MdbOKV.of_same`; SetSchedParams' install by
`install_okQ` at `MdbOK`), discharging the per-label hypotheses of `tcb_decode_cspace`
(TcbCtl.lean):

* `tcb_set_mcp_refines`: SetMCPriority (l4v `decode_set_mcpriority`,
  `set_mcpriority`), fully;
* `tcb_set_prio_refines`: SetPriority (l4v `decode_set_priority`,
  `set_priority`), the scheduler step as `SetPrioHyp`;
* `tcb_bind_ntfn_refines`, `tcb_unbind_ntfn_refines`: Bind/UnbindNotification
  (l4v `decode_bind_notification`, `decode_unbind_notification`,
  `bind_notification`, `unbind_notification`), fully;
* `tcb_set_sched_params_refines`: SetSchedParams (l4v
  `decode_set_sched_params`, `decode_update_sc`, `check_handler_ep`; the
  fault-handler install by the CSpace side's `install_ok`), the scheduler step
  after the install as `SchedTailHyp`.

The decode checks are proved on both sides; the hypotheses are only the FL4
scheduler step's slot footprint and the existence of a spec outcome: that the
spec's step keeps the CSpace (`CK`: CNodes, TCB caps, kinds, CDT, original
flags; weaker than `SOK` since `reorder_ep` changes an endpoint) is proved
(`presC_setPriority`, `presC_setMcpriority`, `presC_scStep`), and `CRel` and
`FinInv` follow by `crel_of_ck`.

FL4-side helpers, for reuse by the other TCB labels:
* `tcb_arg_eq`: `tcb::arg` is the caller's syscall argument;
* `thread_arg_thread`, `thread_arg_other`: `tcb::thread_arg` of a thread cap
  and of anything else (`InvalidCapability pos`);
* `check_prio_eq`: `tcb::check_prio` against the authority's `MCP` word, and
  `checkPrio_run`, the spec's `check_prio` under `McpRel`;
* `mcp_slots`, `tcbw_slots`, `ntfnw_slots`: TCB words past the slots and a
  notification's words keep the cap slots;
* `restart_keeps`: the caller's restart keeps another TCB word;
* `set_mcp_eq`, `tcs_mcp`, `tcs_prio`, `tcs_fault_eq` (with `schedTail`):
  `thread_control_sched` by its flags;
* `tcb_bound_eq`, `ntfn_head_eq`, `ntfn_bound_eq`, `bind_ntfn_eq`,
  `unbind_ntfn_eq`: the bound-notification words;
* `decode_mcp_eq`, `decode_prio_eq`, `decode_ssp_eq`: `tcb::decode` at the
  label.

Spec side: `absCap_thread`, `absCap_ntfn`, `StateRel.updTcb`, `crel_updTcb`;
`CK` and `PresC` with their combinators; `bindNotification_eq`,
`unbindNotification_eq`, `restart_kheap`, `restart_tcb`; `dus_null`,
`dus_sc`, `dus_other` (l4v `decode_update_sc`); `invoke_mcp_run`,
`invoke_prio_mem` (`invoke_tcb`).
-/
import Fl4Proofs.P3.TcbCtl
import Fl4Proofs.P3.ScMcp
import Fl4Proofs.P3.ScKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

/-! ## The spec -/

section Spec
open Fl4Spec

theorem absCap_thread {c : capability.Cap} {r : ObjRef} (h : absCap c = .threadCap r) :
    ∃ q, c = .Thread q ∧ r = q.bv := by
  cases c <;> simp [absCap] at h ⊢
  all_goals first | exact h.symm | skip

/-- The CSpace relation across a TCB update keeping the TCB's caps. -/
theorem StateRel.updTcb {th : TypedHeap} {m : U64 → U64} {σ : State Unit} (hR : StateRel th m σ)
    {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x)) (hc : tcbCnodeMap y = tcbCnodeMap x) :
    StateRel th m (Notif.updK σ t (.tcb y)) := by
  refine ⟨fun p rr hp => ?_, fun t' ht' => ?_⟩
  · obtain ⟨cs, hk', hwf, hs⟩ := hR.cnode p rr hp
    have hne : p.bv ≠ t := by intro e; rw [e, hk] at hk'; cases hk'
    exact ⟨cs, by simp only [Notif.updK, Function.update_of_ne hne]; exact hk', hwf, hs⟩
  · obtain ⟨tcb', hk', hs⟩ := hR.tcb t' ht'
    by_cases he : t'.bv = t
    · rw [he, hk] at hk'
      cases hk'
      exact ⟨y, by simp only [Notif.updK, he, Function.update_self], fun i hi => by rw [hc]; exact hs i hi⟩
    · exact ⟨tcb', by simp only [Notif.updK, Function.update_of_ne he]; exact hk', hs⟩

/-- **`CRel` and `FinInv` across a TCB update keeping its caps** and a
memory step keeping the slots. -/
theorem crel_updTcb {th : TypedHeap} {m m' : U64 → U64} {σ : State Unit} {G : MdbGhost}
    (hC : CRel th m σ G) (hFI : FinInv th m σ G) (hS : SlotsSame th m m') {t : ObjRef} {x y : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hc : tcbCnodeMap y = tcbCnodeMap x) :
    CRel th m' (Notif.updK σ t (.tcb y)) G ∧ FinInv th m' (Notif.updK σ t (.tcb y)) G := by
  obtain ⟨hR, hV, hM, hCd, hI⟩ := hC
  have hcap : ∀ a, IsSlot th a → capAt m' a = capAt m a := fun a ha => hS.capAt ha
  exact ⟨⟨(StateRel.updTcb hR hk hc).of_caps hcap, hV.of_caps hcap, hM.of_same hS, hCd.of_same hS rfl rfl,
    hI.of_same hM hS⟩, hFI.of_same hM hS (ksub_updK_tcb hk)⟩

/-! ### What a scheduler step keeps of the CSpace (`CK`) -/

/-- **A step keeping the CSpace**: every CNode, every TCB's caps, the
objects' kinds (`KSub`), the CDT and the original-cap flags. Weaker than
`SOK`: endpoints may change (`reorder_ep`). -/
structure CK (σ σ' : State Unit) : Prop where
  cn : ∀ p r cs, σ.kheap p = some (.cnode r cs) → σ'.kheap p = some (.cnode r cs)
  tc : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ tcbCnodeMap y = tcbCnodeMap x
  ks : KSub σ σ'
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap

theorem CK.refl (σ : State Unit) : CK σ σ := ⟨fun _ _ _ h => h, fun _ x h => ⟨x, h, rfl⟩, KSub.refl σ, rfl, rfl⟩

theorem CK.trans {σ1 σ2 σ3 : State Unit} (h1 : CK σ1 σ2) (h2 : CK σ2 σ3) : CK σ1 σ3 := by
  refine ⟨fun p r cs h => h2.cn p r cs (h1.cn p r cs h), fun p x h => ?_, h1.ks.trans h2.ks,
    h2.cdt.trans h1.cdt, h2.orig.trans h1.orig⟩
  obtain ⟨y, hy, e⟩ := h1.tc p x h
  obtain ⟨z, hz, e'⟩ := h2.tc p y hy
  exact ⟨z, hz, e'.trans e⟩

theorem SOK.ck {f : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') : CK σ σ' := by
  refine ⟨fun p r cs hp => ?_, fun p x hp => ?_, h.ksub, h.cdt, h.orig⟩
  · obtain ⟨o', h1, h2⟩ := h.fwd hp; rw [h2.cnode_inv] at h1; exact h1
  · obtain ⟨o', h1, h2⟩ := h.fwd hp
    obtain ⟨y, rfl, e1, e2, e3, e4, e5, e6, -, -⟩ := h2.tcb_inv
    exact ⟨y, h1, tcbCnodeMap_congr e1 e2 e3 e4 e5 e6⟩

/-- An update of an object that is neither a CNode nor a TCB, to another
such object. -/
theorem CK.updOther {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h1 : ∀ r cs, o ≠ .cnode r cs) (h2 : ∀ x, o ≠ .tcb x) (h1' : ∀ r cs, o' ≠ .cnode r cs)
    (h2' : ∀ x, o' ≠ .tcb x) : CK σ (Notif.updK σ p o') := by
  refine ⟨fun q r cs hq => ?_, fun q x hq => ?_, fun q => ?_, rfl, rfl⟩
  · have hne : q ≠ p := by
      rintro rfl; rw [hk] at hq; exact h1 r cs (Option.some.inj hq)
    simp only [Notif.updK, Function.update_of_ne hne]; exact hq
  · have hne : q ≠ p := by
      rintro rfl; rw [hk] at hq; exact h2 x (Option.some.inj hq)
    exact ⟨x, by simp only [Notif.updK, Function.update_of_ne hne]; exact hq, rfl⟩
  · by_cases e : q = p
    · subst e
      refine ⟨fun r cs h _ => ?_, fun t h => ?_, fun h => ?_⟩
      · simp only [Notif.updK, Function.update_self, Option.some.injEq] at h; exact absurd h (h1' r cs)
      · simp only [Notif.updK, Function.update_self, Option.some.injEq] at h; exact absurd h (h2' t)
      · rw [hk] at h; cases h
    · simp only [Notif.updK, Function.update_of_ne e]; exact KSub.refl σ q

theorem CK.stateRel {th : TypedHeap} {m : U64 → U64} {σ σ' : State Unit} (h : CK σ σ') (hR : StateRel th m σ) :
    StateRel th m σ' := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p r hp
    exact ⟨cs, h.cn _ _ _ hk, hwf, hs⟩
  · obtain ⟨x, hk, hs⟩ := hR.tcb t ht
    obtain ⟨y, hy, e⟩ := h.tc _ x hk
    exact ⟨y, hy, fun i hi => by rw [e]; exact hs i hi⟩

/-- **`CRel` and `FinInv` across a step** keeping the slots and `CK`. -/
theorem crel_of_ck {th : TypedHeap} {m m' : U64 → U64} {σ σ' : State Unit} {G : MdbGhost}
    (hC : CRel th m σ G) (hFI : FinInv th m σ G) (hS : SlotsSame th m m') (hk : CK σ σ') :
    CRel th m' σ' G ∧ FinInv th m' σ' G := by
  obtain ⟨hR, hV, hM, hCd, hI⟩ := hC
  have hcap : ∀ x, IsSlot th x → capAt m' x = capAt m x := fun x hx => hS.capAt hx
  exact ⟨⟨((hk.stateRel hR).of_caps hcap), hV.of_caps hcap, hM.of_same hS, hCd.of_same hS hk.cdt hk.orig,
    hI.of_same hM hS⟩, hFI.of_same hM hS hk.ks⟩

/-- Every outcome of `m` keeps the CSpace (`CK`). -/
def PresC {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → CK σ x.2

theorem presC_of_pres {f : Bool × Bool} {α : Type} {m : NonDet (State Unit) α} (h : Pres f m) : PresC m :=
  fun σ x hx => (h σ x hx).ck

theorem presC_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : PresC m)
    (hg : ∀ a, PresC (g a)) : PresC (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem presC_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, PresC (g a)) (o : Option α) :
    PresC (NonDet.maybeM g o) := by
  cases o
  · exact presC_of_pres (f := (false, false)) (pres_pure' _)
  · exact h _

theorem pres_getSimpleKo {f : Bool × Bool} {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    Pres f (getSimpleKo (Z := Unit) C p) := by
  unfold getSimpleKo; pres_auto

theorem pres_tcbAppend {f : Bool × Bool} (t : ObjRef) (qs : List ObjRef) : Pres f (tcbAppend (Z := Unit) t qs) := by
  unfold tcbAppend orderedInsert; pres_auto

/-- `set_endpoint` keeps the CSpace. -/
theorem presC_setEndpoint (p : ObjRef) (e : Endpoint) : PresC (setEndpoint (Z := Unit) p e) := by
  show PresC (setSimpleKo (Z := Unit) KernelObject.endpoint p e)
  unfold setSimpleKo
  refine presC_bind (presC_of_pres (f := (false, false)) (pres_getObject _)) fun _ =>
    presC_bind (presC_of_pres (f := (false, false)) (pres_assert _)) fun _ =>
    presC_bind (presC_of_pres (f := (false, false)) (pres_assert _)) fun _ => ?_
  intro σ x hx
  obtain ⟨k, hk, hty, e'⟩ := setObject_mem hx
  rw [e']
  cases k <;> simp only [aType, reduceCtorEq] at hty
  all_goals first | (split_ifs at hty) | skip
  exact CK.updOther hk (fun _ _ => by simp) (fun _ => by simp) (fun _ _ => by simp) (fun _ => by simp)

theorem pres_reorderNtfn {f : Bool × Bool} (n t : ObjRef) : Pres f (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn
  refine pres_bind (pres_getSimpleKo _ _) fun _ => ?_
  refine pres_bind (pres_assert _) fun _ => pres_bind (pres_pure _) fun _ => pres_bind (pres_assert _) fun _ =>
    pres_bind (pres_pure _) fun _ => pres_bind (pres_tcbAppend _ _) fun _ => ?_
  show Pres f (setSimpleKo (Z := Unit) KernelObject.notification n _)
  unfold setSimpleKo; pres_auto

theorem presC_reorderEp (e t : ObjRef) : PresC (reorderEp (Z := Unit) e t) := by
  unfold reorderEp
  refine presC_bind (presC_of_pres (f := (false, false)) (pres_getSimpleKo _ _)) fun _ => ?_
  refine presC_bind (presC_of_pres (f := (false, false)) (pres_assert _)) fun _ =>
    presC_bind (presC_of_pres (f := (false, false)) (pres_pure _)) fun _ =>
    presC_bind (presC_of_pres (f := (false, false)) (pres_assert _)) fun _ =>
    presC_bind (presC_of_pres (f := (false, false)) (pres_pure _)) fun _ =>
    presC_bind (presC_of_pres (f := (false, false)) (pres_tcbAppend _ _)) fun _ => presC_setEndpoint _ _

theorem pres_threadSetPriority {f : Bool × Bool} (t : ObjRef) (pr : Priority) :
    Pres f (threadSetPriority (Z := Unit) t pr) := by
  unfold threadSetPriority; pres_auto

/-- **`set_priority` keeps the CSpace** (l4v `set_priority`): the ready-queue
steps keep `SOK`, `reorder_ntfn` too, `reorder_ep` changes an endpoint. -/
theorem presC_setPriority (t : ObjRef) (pr : Priority) : PresC (setPriority (Z := Unit) t pr) := by
  unfold setPriority getThreadState
  refine presC_bind (presC_of_pres (f := (false, false)) (pres_threadGet _ _ _)) fun ts => ?_
  split
  · refine presC_of_pres (f := (false, false)) ?_
    refine pres_bind (pres_threadGet _ _ _) fun _ => pres_bind (pres_threadGet _ _ _) fun _ => ?_
    unfold getTcbQueue
    refine pres_bind (pres_bind (pres_gets _) fun _ => pres_pure _) fun _ => pres_bind (pres_gets _) fun _ => ?_
    split
    · exact pres_bind (pres_tcbSchedAction _ _ _) fun _ => pres_bind (pres_threadSetPriority _ _) fun _ =>
        pres_bind (pres_tcbSchedAction _ _ _) fun _ => pres_rescheduleRequired _
    · exact pres_threadSetPriority _ _
  · exact presC_bind (presC_of_pres (f := (false, false)) (pres_threadSetPriority _ _)) fun _ =>
      presC_bind (presC_maybeM (fun e => presC_reorderEp e t) _) fun _ =>
      presC_maybeM (fun n => presC_of_pres (f := (false, false)) (pres_reorderNtfn n t)) _

/-- A TCB update keeping its caps keeps the CSpace. -/
theorem CK.updTcb {σ : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (hc : tcbCnodeMap y = tcbCnodeMap x) : CK σ (Notif.updK σ p (.tcb y)) := by
  refine ⟨fun q r cs hq => ?_, fun q x' hq => ?_, ksub_updK_tcb hk, rfl, rfl⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp only [Notif.updK, Function.update_of_ne hne]; exact hq
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq
      exact ⟨y, by simp [Notif.updK], hc⟩
    · exact ⟨x', by simp only [Notif.updK, Function.update_of_ne e]; exact hq, rfl⟩

/-- `set_ntfn_obj_ref` on a notification. -/
theorem setNtfnObjRef_eq {σ : State Unit} {n : ObjRef} {xn : Notification}
    (hn : σ.kheap n = some (.notification xn)) (g : (Option ObjRef → Option ObjRef) → Notification → Notification)
    (v : Option ObjRef) :
    setNtfnObjRef (Z := Unit) g n v σ = ({((), Notif.updK σ n (.notification (g (fun _ => v) xn)))}, False) := by
  show updateSkObjRef KernelObject.notification g n v σ = _
  unfold updateSkObjRef
  rw [nd_bind_one (Notif.getNotification_eq hn)]
  exact Notif.setNotification_eq _ hn

/-- **The spec's `bind_notification`**: the notification's bound TCB and the
TCB's bound notification. -/
theorem bindNotification_eq {σ : State Unit} {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hn : σ.kheap n = some (.notification xn)) (ht : σ.kheap t = some (.tcb xt)) :
    bindNotification (Z := Unit) t n σ = ({((), Notif.updK (Notif.updK σ n
      (.notification (ntfnBoundTcbUpdate (fun _ => some t) xn))) t
        (.tcb (tcbBoundNotificationUpdate (fun _ => some n) xt)))}, False) := by
  have hne : t ≠ n := by rintro rfl; rw [hn] at ht; cases ht
  unfold bindNotification
  rw [nd_bind_one (setNtfnObjRef_eq hn _ _)]
  exact Notif.threadSet_eq _ (by simp only [Notif.updK, Function.update_of_ne hne]; exact ht)

/-- **The spec's `unbind_notification`** of a TCB bound to `n`. -/
theorem unbindNotification_eq {σ : State Unit} {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hn : σ.kheap n = some (.notification xn)) (ht : σ.kheap t = some (.tcb xt))
    (hb : xt.tcbBoundNotification = some n) :
    unbindNotification (Z := Unit) t σ = ({((), Notif.updK (Notif.updK σ n
      (.notification (ntfnBoundTcbUpdate (fun _ => none) xn))) t
        (.tcb (tcbBoundNotificationUpdate (fun _ => none) xt)))}, False) := by
  have hne : t ≠ n := by rintro rfl; rw [hn] at ht; cases ht
  unfold unbindNotification
  rw [nd_bind_one (m := getTcbObjRef (Z := Unit) Tcb.tcbBoundNotification t) (Notif.threadGet_eq _ ht), hb]
  show (setNtfnObjRef ntfnBoundTcbUpdate n none >>= fun _ => setTcbObjRef tcbBoundNotificationUpdate t none) σ = _
  rw [nd_bind_one (setNtfnObjRef_eq hn _ _)]
  exact Notif.threadSet_eq _ (by simp only [Notif.updK, Function.update_of_ne hne]; exact ht)

/-- The bound-object steps keep the CSpace. -/
theorem ck_bound {σ : State Unit} {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hn : σ.kheap n = some (.notification xn)) (ht : σ.kheap t = some (.tcb xt)) (v w : Option ObjRef) :
    CK σ (Notif.updK (Notif.updK σ n (.notification (ntfnBoundTcbUpdate (fun _ => v) xn))) t
      (.tcb (tcbBoundNotificationUpdate (fun _ => w) xt))) := by
  have hne : t ≠ n := by rintro rfl; rw [hn] at ht; cases ht
  refine (CK.updOther hn (fun _ _ => by simp) (fun _ => by simp) (fun _ _ => by simp) (fun _ => by simp)).trans
    (CK.updTcb (by simp only [Notif.updK, Function.update_of_ne hne]; exact ht) ?_)
  unfold tcbCnodeMap tcbBoundNotificationUpdate; rfl

end Spec

/-! ## FL4 -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem tcb_arg_eq (s : S) (c : tcb.Ctx) {ct : U64} (hct : sched.cur_thread st s = ok ct) {i x : U64}
    (h : msg.syscall_arg st s ct c.buf i = ok x) : tcb.arg st s c i = ok x := by
  unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact h

theorem thread_arg_thread (s : S) {x q : U64} (pos : U64) (h : capV (L.mem s) x = .Thread q) :
    tcb.thread_arg st s x pos = ok (.Ok q) := by
  unfold tcb.thread_arg; rw [slot_cap_eq, capAt_capV, h]; simp only [bind_ok]

theorem thread_arg_other (s : S) {x : U64} (pos : U64) (h : ∀ q, capV (L.mem s) x ≠ .Thread q) :
    tcb.thread_arg st s x pos = ok (.Err (.Sys (.InvalidCapability pos))) := by
  unfold tcb.thread_arg; rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc : capV (L.mem s) x <;> simp only [error.invalid_cap]
  exact absurd hc (h _)

theorem check_prio_eq (s : S) (v q : U64) :
    tcb.check_prio st s v q = if v > L.mem s (mcpA q)
      then ok (.Err (.Sys (.RangeError 0#u64 (L.mem s (mcpA q))))) else ok (.Ok ()) := by
  unfold tcb.check_prio
  obtain ⟨w, hw, rfl⟩ := spec_exists (obj.Tcb.mcp.spec' (L := L) s q)
  rw [hw]; simp only [bind_ok]
  split <;> rfl

/-- **Writing a TCB's `MCP` word keeps the cap slots** (offset 3440, past the
slots). -/
theorem mcp_slots {th : TypedHeap} (hP : Placed th) (s : S) {t : U64} (v : U64) (ht : th t = some .tcb) :
    SlotsSame th (L.mem s) (L.mem (L.wr s (mcpA t) v)) := by
  have htf := hP.fits t _ ht
  have hta := hP.align t _ ht
  simp only [objSize] at htf
  have hv : (mcpA t).val = t.val + 3440 := by
    unfold mcpA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine slotsSame_wr hP s v (by unfold P1.Aligned; rw [hv]; omega) (fun a ha => ?_)
  obtain ⟨p, k, hk, h1, h2, h3⟩ := slot_in_object hP ha
  rw [hv]
  by_cases hpt : p = t
  · subst hpt; rw [ht] at hk; cases hk
    have := h3 rfl; simp [tcbSlots] at this; omega
  · have e4 : objSize ObjKind.tcb = 4096 := rfl
    rcases hP.disj p t k .tcb hk ht hpt with h | h <;> omega

theorem set_mcp_eq (s : S) (t v : U64) : obj.Tcb.set_mcp st t s v = ok (L.wr s (mcpA t) v) := by
  obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Tcb.set_mcp.wr (L := L) s t v); exact hw

/-- `thread_control_sched` with only `SCHED_UPDATE_MCP`: the `MCP` write. -/
theorem tcs_mcp {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t v sc : U64) (slot : obj.Slot)
    (fh : capability.Cap × obj.Slot) (pr : U64) :
    tcb.thread_control_sched st ar s a t slot fh v pr sc tcb.SCHED_UPDATE_MCP =
      ok (.Ok (), L.wr s (mcpA t) v, a) := by
  unfold tcb.thread_control_sched
  simp only [lift, bind_ok, tcb.SCHED_UPDATE_MCP, tcb.SCHED_UPDATE_FAULT, tcb.SCHED_UPDATE_PRIO,
    tcb.SCHED_UPDATE_SC]
  simp only [show (4#u64 &&& 2#u64) = 0#u64 by decide, show (4#u64 &&& 4#u64) = 4#u64 by decide,
    show (4#u64 &&& 8#u64) = 0#u64 by decide, show (4#u64 &&& 1#u64) = 0#u64 by decide]
  simp [set_mcp_eq]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem decode_mcp_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetMCPriority p c = tcb.decode_set_priority st arI s ar p c false := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSuspend_val, lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte, decide_false]
  rfl

theorem nd_bind_congr {σ' α β : Type} {m m' : Fl4Spec.NonDet σ' α} {f : α → Fl4Spec.NonDet σ' β} {s : σ'}
    (h : m s = m' s) : (m >>= f) s = (m' >>= f) s := by
  show Fl4Spec.NonDet.bind m f s = Fl4Spec.NonDet.bind m' f s
  unfold Fl4Spec.NonDet.bind; rw [h]

/-- The spec's `set_mcpriority` invocation through `invoke_tcb`. -/
theorem invoke_mcp_run {σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ1.kheap t = some (.tcb x)) (sl : Fl4Spec.CslotPtr) (m : Fl4Spec.Priority) (q : Fl4Spec.ObjRef)
    (blk call don : Bool) :
    ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeTCB (.threadControlSched t sl none (some (m, q)) none none))).run σ1) =
      ({(.ok [], Notif.updK σ1 t (.tcb { x with tcbMcpriority := m }))}, False) := by
  show (Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched t sl none (some (m, q)) none none)).run σ1 = _
  simp only [Fl4Spec.invokeTcb, Fl4Spec.installTcbCap]
  rw [retOk_bind]
  rw [run_bind_ok_st (run_liftE' (show Fl4Spec.NonDet.maybeM (fun (x : Fl4Spec.Priority × Fl4Spec.ObjRef) =>
      Fl4Spec.setMcpriority (Z := Unit) t x.1) (some (m, q)) σ1 = _ from Notif.threadSet_eq _ hk))]
  rw [run_bind_ok_st (run_liftE' (m := Fl4Spec.NonDet.maybeM _ none) (a := ()) rfl),
    run_bind_ok_st (run_liftE' (m := Fl4Spec.NonDet.maybeM _ none) (a := ()) rfl)]; rfl

/-- **`tcb::decode` at `TCBSetMCPriority`** (`TcbOK`): l4v's
`decode_set_mcpriority` (the authority's MCP check, by `McpRel`), the
restart and `invoke_tcb ThreadControlSched` (`set_mcpriority`), with the
CSpace relation and `FinInv` after. -/
theorem tcb_set_mcp_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetMCPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    {T : Set U64} (hM : McpRel T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetMCPriority p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetMcpriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF
  rw [decode_mcp_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetMcpriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, hrc, -, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
      have hfr1 := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
      rw [hrc]; simp only [bind_ok, tcs_mcp]
      refine (WP.spec_ok _).2 ?_
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      obtain ⟨x, hkx, -⟩ := hDS1.1.1.tcb p hp
      obtain ⟨hC2, hF2⟩ := crel_updTcb hDS1.1 hDS1.2.2 (mcp_slots hP s1 y0 hp) hkx
        (y := { x with tcbMcpriority := Fl4Spec.ucast 8 y0.bv }) (by unfold Fl4Spec.tcbCnodeMap; rfl)
      refine Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_, th, G, Or.inl ⟨rfl, [], rfl⟩, hP, hC2, hF2,
        MdbOKV.of_same hDS1.1.2.2.1 (mcp_slots hP s1 y0 hp) hfr1⟩
      rw [invoke_mcp_run hkx]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _

end

/-! ## SetPriority -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `thread_control_sched` with only `SCHED_UPDATE_PRIO`: `set_priority`. -/
theorem tcs_prio (ar : machine.Arch A) (s : S) (a : A) (t v sc mcp : U64) (slot : obj.Slot)
    (fh : capability.Cap × obj.Slot) :
    tcb.thread_control_sched st ar s a t slot fh mcp v sc tcb.SCHED_UPDATE_PRIO =
      (sched.set_priority st s t v >>= fun s4 => ok (.Ok (), s4, a)) := by
  unfold tcb.thread_control_sched
  simp only [lift, bind_ok, tcb.SCHED_UPDATE_MCP, tcb.SCHED_UPDATE_FAULT, tcb.SCHED_UPDATE_PRIO,
    tcb.SCHED_UPDATE_SC]
  simp only [show (8#u64 &&& 2#u64) = 0#u64 by decide, show (8#u64 &&& 4#u64) = 0#u64 by decide,
    show (8#u64 &&& 8#u64) = 8#u64 by decide, show (8#u64 &&& 1#u64) = 0#u64 by decide]
  (try simp); rfl

theorem decode_prio_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetPriority p c = tcb.decode_set_priority st arI s ar p c true := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSuspend_val, lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte, decide_false]
  rfl

/-- The spec's `set_priority` invocation through `invoke_tcb`: an outcome of
`set_priority` gives one of the invocation. -/
theorem invoke_prio_mem {σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} (sl : Fl4Spec.CslotPtr)
    (pr : Fl4Spec.Priority) (q : Fl4Spec.ObjRef) (blk call don : Bool) {y : Unit × Fl4Spec.State Unit}
    (hy : y ∈ (Fl4Spec.setPriority (Z := Unit) t pr σ1).1) :
    (.ok [], y.2) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeTCB (.threadControlSched t sl none none (some (pr, q)) none))).run σ1).1 := by
  show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched t sl none none (some (pr, q)) none)).run σ1).1
  simp only [Fl4Spec.invokeTcb, Fl4Spec.installTcbCap]
  rw [retOk_bind, run_bind_ok_st (run_liftE' (m := Fl4Spec.NonDet.maybeM _ none) (a := ()) rfl)]
  refine mem_bindE_ok (mem_liftE (m := Fl4Spec.NonDet.maybeM (fun (x : Fl4Spec.Priority × Fl4Spec.ObjRef) =>
    Fl4Spec.setPriority (Z := Unit) t x.1) (some (pr, q))) hy) ?_
  rw [run_bind_ok_st (run_liftE' (m := Fl4Spec.NonDet.maybeM _ none) (a := ()) rfl)]
  exact Set.mem_singleton _

/-- **The scheduler step of SetPriority** (for the scheduler-queue
refinement to come): FL4's `set_priority` after the caller's restart keeps
every slot word, and the spec's `set_priority` has an outcome (that it keeps
the CSpace is `presC_setPriority`). -/
def SetPrioHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ s1 σ1 (t v : U64), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → th t = some .tcb →
    v.val < 256 → sched.set_priority st s1 t v ⦃ s2 => SlotsSame th (L.mem s1) (L.mem s2) ∧
      ∃ y, y ∈ (Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ1).1 ⦄

/-- **`tcb::decode` at `TCBSetPriority`** (`TcbOK`): l4v's
`decode_set_priority` (the authority's MCP check, by `McpRel`), the restart
and `invoke_tcb ThreadControlSched` (`set_priority`, from `SetPrioHyp`),
with the CSpace relation and `FinInv` after. -/
theorem tcb_set_prio_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    {T : Set U64} (hM : McpRel T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (hH : SetPrioHyp (L := L) th s σ ct)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetPriority p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetPriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF
  rw [decode_prio_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetPriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, hrc, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
      have hfr1 := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      rw [hrc]; simp only [bind_ok, tcs_prio]
      refine WP.spec_bind (hH s1 σ1 p y0 hs1 (by rw [← hcur]; exact hst1) hp hlt) ?_
      rintro s2 ⟨hS2, y, hy⟩
      refine (WP.spec_ok _).2 ?_
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      obtain ⟨hC2, hF2⟩ := crel_of_ck hDS1.1 hDS1.2.2 hS2 (presC_setPriority _ _ σ1 y hy)
      exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], y.2), invoke_prio_mem ssl _ q.bv blk call don hy,
        th, G, Or.inl ⟨rfl, [], rfl⟩, hP, hC2, hF2, MdbOKV.of_same hDS1.1.2.2.1 hS2 hfr1⟩
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _

end

/-! ## Bind/UnbindNotification: FL4 helpers -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem tcb_bound_eq (s : S) (t : U64) : obj.Tcb.bound_ntfn st t s = ok (L.mem s (P1.boundA t)) := by
  have h : obj.Tcb.bound_ntfn st t s ⦃ v => v = L.mem s (P1.boundA t) ⦄ := by
    unfold obj.Tcb.bound_ntfn; step*; simp_all [P1.boundA]
  obtain ⟨w, hw, rfl⟩ := spec_exists h; exact hw

theorem ntfn_head_eq (s : S) (n : U64) : obj.Ntfn.head st n s = ok (L.mem s (P1.epHeadA n)) := by
  have h : obj.Ntfn.head st n s ⦃ v => v = L.mem s (P1.epHeadA n) ⦄ := by
    unfold obj.Ntfn.head; step*; simp_all [P1.epHeadA, layout.ntfn.HEAD, layout.ep.HEAD]
  obtain ⟨w, hw, rfl⟩ := spec_exists h; exact hw

theorem ntfn_bound_eq (s : S) (n : U64) : obj.Ntfn.bound_tcb st n s = ok (L.mem s (Notif.nBoundA n)) := by
  obtain ⟨w, hw, rfl⟩ := spec_exists (Notif.obj.Ntfn.bound_tcb.spec (L := L) s n); exact hw

/-- FL4's `bind_notification`: the two bound words. -/
theorem bind_ntfn_eq (s : S) (t n : U64) :
    notification.bind_notification st s t n = ok (L.wr (L.wr s (Notif.nBoundA n) t) (P1.boundA t) n) := by
  unfold notification.bind_notification
  obtain ⟨s1, h1, rfl⟩ := spec_exists (P1.obj.Ntfn.set_bound_tcb.wr (L := L) s n t)
  rw [h1]; simp only [bind_ok]
  obtain ⟨s2, h2, rfl⟩ := spec_exists (P1.obj.Tcb.set_bound_ntfn.wr (L := L) (L.wr s (P1.ntfnBtA n) t) t n)
  exact h2

/-- FL4's `unbind_notification` of a bound TCB: the two bound words cleared. -/
theorem unbind_ntfn_eq (s : S) (t : U64) (h0 : L.mem s (P1.boundA t) ≠ 0#u64) :
    notification.unbind_notification st s t =
      ok (L.wr (L.wr s (Notif.nBoundA (L.mem s (P1.boundA t))) 0#u64) (P1.boundA t) 0#u64) := by
  unfold notification.unbind_notification
  rw [tcb_bound_eq]
  simp only [bind_ok, bne_iff_ne, ne_eq, h0, not_false_eq_true, ↓reduceIte]
  obtain ⟨s1, h1, rfl⟩ := spec_exists (P1.obj.Ntfn.set_bound_tcb.wr (L := L) s (L.mem s (P1.boundA t)) 0#u64)
  rw [h1]; simp only [bind_ok]
  obtain ⟨s2, h2, rfl⟩ := spec_exists (P1.obj.Tcb.set_bound_ntfn.wr (L := L)
    (L.wr s (P1.ntfnBtA (L.mem s (P1.boundA t))) 0#u64) t 0#u64)
  exact h2

/-- **A write to a TCB word past the slots keeps the cap slots.** -/
theorem tcbw_slots {th : TypedHeap} (hP : Placed th) (s : S) {t : U64} (v : U64) (ht : th t = some .tcb)
    (K : U64) (hK1 : 192 ≤ K.val) (hK2 : K.val + 8 ≤ 4096) (hK8 : K.val % 8 = 0) :
    SlotsSame th (L.mem s) (L.mem (L.wr s (core.num.U64.wrapping_add t K) v)) := by
  have htf := hP.fits t _ ht
  have hta := hP.align t _ ht
  simp only [objSize] at htf
  have hv : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine slotsSame_wr hP s v (by unfold P1.Aligned; rw [hv]; omega) (fun a ha => ?_)
  obtain ⟨p, k, hk, h1, h2, h3⟩ := slot_in_object hP ha
  rw [hv]
  by_cases hpt : p = t
  · subst hpt; rw [ht] at hk; cases hk
    have := h3 rfl; simp [tcbSlots] at this; omega
  · have e4 : objSize ObjKind.tcb = 4096 := rfl
    rcases hP.disj p t k .tcb hk ht hpt with h | h <;> omega

/-- **A write to one of a notification's first five words keeps the cap
slots**, when the notifications lie apart from the slots. -/
theorem ntfnw_slots {th : TypedHeap} (hP : Placed th) (s : S) {n : U64} (v : U64) (hn : Notif.NAddr n)
    (hNA : ∀ a, IsSlot th a → a.val + 32 ≤ n.val ∨ n.val + 40 ≤ a.val)
    (K : U64) (hK : K.val + 8 ≤ 40) (hK8 : K.val % 8 = 0) :
    SlotsSame th (L.mem s) (L.mem (L.wr s (core.num.U64.wrapping_add n K) v)) := by
  have hv : (core.num.U64.wrapping_add n K).val = n.val + K.val := Notif.nfield_val hn (by omega)
  have := hn.align
  refine slotsSame_wr hP s v (by unfold P1.Aligned; rw [hv]; omega) (fun a ha => ?_)
  have := hNA a ha
  rw [hv]; omega

/-- The caller's restart keeps a word of a TCB other than the caller's state
word. -/
theorem restart_keeps {th : TypedHeap} (hP : Placed th) {s s1 : S} {ct t : U64}
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) (hct : th ct = some .tcb)
    (ht : th t = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (K : U64) (hK1 : K.val ≠ 3328) (hK2 : K.val + 8 ≤ 4096) (hK8 : K.val % 8 = 0) :
    L.mem s1 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := by
  have htf := hP.fits t _ ht
  have hta := hP.align t _ ht
  have hcf := hP.fits ct _ hct
  have hca := hP.align ct _ hct
  simp only [objSize] at htf hcf
  have hv : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hsv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hA : P1.Aligned (core.num.U64.wrapping_add t K) := by unfold P1.Aligned; rw [hv]; omega
  have hS : P1.Aligned (stA ct) := by unfold P1.Aligned; rw [hsv]; omega
  have hne1 : (stA ct).val ≠ (core.num.U64.wrapping_add t K).val := by
    rw [hsv, hv]
    by_cases e : ct = t
    · subst e; omega
    · have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hP.disj ct t _ _ hct ht e with h | h <;> rw [e4] at h <;> omega
  have hne2 := out_ne hact ht (w := core.num.U64.wrapping_add t K) (by rw [hv]; omega)
  have hc := set_thread_state_cases (L := L) s ct sched.TS_RESTART
  rw [hs1, WP.spec_ok] at hc
  rcases hc with rfl | rfl
  · exact L.mem_wr_ne hS hA hne1
  · rw [L.mem_wr_ne hact.1 hA (Ne.symm hne2), L.mem_wr_ne hS hA hne1]

end

/-! ## BindNotification -/

section Spec
open Fl4Spec

theorem absCap_ntfn {c : capability.Cap} {r : ObjRef} {b : Badge} {rs : CapRights}
    (h : absCap c = .notificationCap r b rs) :
    ∃ p bb w rv, c = .Notification p bb w rv ∧ r = p.bv ∧ rs = rightsOf w rv false false := by
  cases c <;> simp [absCap] at h ⊢
  all_goals first | (obtain ⟨h1, -, h3⟩ := h; exact ⟨h1.symm, h3.symm⟩) | skip

theorem run_throw_bind {α β : Type} (e : SyscallError) (f : α → SEMonad Unit β) (σ : State Unit) :
    ((NonDetE.throwError e : SEMonad Unit α) >>= f).run σ = ({(.error e, σ)}, False) := run_bind_error (m := NonDetE.throwError e) rfl f

theorem allowRecv_mem (w r : Bool) : AllowRecv ∈ rightsOf w r false false ↔ r = true := Iff.rfl

/-- The spec's state after the caller's restart: only the caller's TCB
changes. -/
theorem restart_kheap {σ σ1 : State Unit} {ct : ObjRef} {x : Tcb} (hk : σ.kheap ct = some (.tcb x))
    (h : setThreadState (Z := Unit) ct .restart σ = ({((), σ1)}, False)) :
    σ1.kheap = Function.update σ.kheap ct (some (.tcb { x with tcbState := .restart })) := by
  obtain ⟨σ1', h1, h2, -⟩ := setThreadState_eq σ ct x hk .restart
  rw [h] at h1
  have := congrArg Prod.fst h1
  simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
  rw [this]; exact h2

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`tcb::decode` at `TCBBindNotification`** (`TcbOK`): l4v's
`decode_bind_notification` (the target's bound notification, by `hbnd`; the
notification's queue and bound TCB, by `NtfnStateRel`), the restart and
`invoke_tcb (NotificationControl t (Some n))` (`bind_notification`), with
the CSpace relation and `FinInv` after. -/
theorem tcb_bind_ntfn_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbBindNotification)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    {N T : Set U64} (hNR : Notif.NtfnStateRel N T (L.mem s) σ) (hNP : Notif.NPlaced T N)
    (hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ N)
    (hNA : ∀ a, IsSlot th a → ∀ n ∈ N, a.val + 32 ≤ n.val ∨ n.val + 40 ≤ a.val)
    (hbnd : ∀ xp, σ.kheap p.bv = some (.tcb xp) → xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)))
    (blk don : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBBindNotification p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_bind_notification st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_bind_notification tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  obtain ⟨xp, hkp, -⟩ := hDS.1.1.tcb p hp
  have hbp := hbnd xp hkp
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length = 0 := by have := ((hX.2 0 x0 hx0').1).1 h0; omega
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    simp only [Fl4Spec.decodeBindNotification]
    rw [whenE_pos hl]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  have hhd : excaps.head? = some e := by rw [List.head?_eq_getElem?]; exact he
  simp only [h0, ↓reduceIte, show length >= 0#u64 from by scalar_tac, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, tcb_bound_eq]
  -- the spec up to the bound-notification check
  have hsp0 : ∀ (k : Option Fl4Spec.ObjRef → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      ((Fl4Spec.NonDetE.whenE (excaps.length = 0) (Fl4Spec.NonDetE.throwError .truncatedMessage) >>= fun _ =>
        Fl4Spec.NonDetE.liftE (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv) >>= k) :
          Fl4Spec.SEMonad Unit _).run σ = (k (Notif.optRef (L.mem s (P1.boundA p)))).run σ := by
    intro k
    rw [whenE_neg hexl, retOk_bind,
      lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
        (Notif.threadGet_eq _ hkp), hbp]
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  swap
  · -- already bound
    simp only [bne_iff_ne, ne_eq, hb0, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    simp only [Fl4Spec.decodeBindNotification]
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hb0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hsp1 : (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps).run σ = (do
      let (ntfnptr, rights) ← (match (absCap (capV (L.mem s) x0)) with
        | .notificationCap ptr _ r => Fl4Spec.NonDetE.returnOk (ptr, r)
        | _ => Fl4Spec.NonDetE.throwError .illegalOperation : Fl4Spec.SEMonad Unit _)
      Fl4Spec.NonDetE.whenE (Fl4Spec.AllowRecv ∉ rights) <| Fl4Spec.NonDetE.throwError .illegalOperation
      let ntfn ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getNotification ntfnptr
      match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
      | .idleNtfn, none => Fl4Spec.NonDetE.returnOk ()
      | .activeNtfn _, none => Fl4Spec.NonDetE.returnOk ()
      | _, _ => Fl4Spec.NonDetE.throwError .illegalOperation
      Fl4Spec.NonDetE.returnOk <| Fl4Spec.TcbInvocation.notificationControl p.bv (some ntfnptr)).run σ := by
    simp only [Fl4Spec.decodeBindNotification]
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    rw [retOk_bind, hhd, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc
    cases cc <;> rfl
  unfold tcb.bindable_ntfn
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc : capV (L.mem s) x0
  case Notification q b w r =>
    rw [hc] at hsp1
    simp only [absCap] at hsp1
    rw [retOk_bind] at hsp1
    have hqN := hcapN h0 q b w r hc
    obtain ⟨xn, hkn, hrn⟩ := hNR.ntfn q hqN
    by_cases hr : r = true
    swap
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
      apply run_liftME_err
      rw [hsp1, whenE_pos (by simp only [allowRecv_mem]; exact hr)]
      exact run_throw_bind _ _ _
    rw [whenE_neg (by simp only [allowRecv_mem, not_not]; exact hr), retOk_bind] at hsp1
    simp only [hr, ↓reduceIte, ntfn_head_eq, bind_ok]
    have hbt := hrn.bound
    have hob := hrn.obj
    by_cases hh : L.mem s (P1.epHeadA q) = 0#u64
    swap
    · -- a waiting notification
      simp only [bne_iff_ne, ne_eq, hh, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
      apply run_liftME_err
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn)]
      have hw : ∃ qs, xn.ntfnObj = .waitingNtfn qs := by
        revert hob
        cases xn.ntfnObj with
        | idleNtfn => intro hob; exact absurd (by have := hob.2.head; simpa [Notif.qOf] using this) hh
        | activeNtfn b => intro hob; exact absurd (by have := hob.2.1.head; simpa [Notif.qOf] using this) hh
        | waitingNtfn qs => intro _; exact ⟨qs, rfl⟩
      obtain ⟨qs, hqs⟩ := hw
      rw [hqs]
      exact run_throw_bind _ _ _
    simp only [hh, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ntfn_bound_eq, bind_ok]
    have hnw : ∀ qs, xn.ntfnObj ≠ .waitingNtfn qs := by
      intro qs hq
      rw [hq] at hob
      obtain ⟨-, xs, hxs, -, hqr, -⟩ := hob
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxs
      have h1 := hqr.head
      have := hqr.ne0 hNP.tcb y (by simp)
      simp only [Notif.qOf, List.headD_cons] at h1
      rw [hh] at h1
      exact this h1.symm
    by_cases hnb : L.mem s (Notif.nBoundA q) = 0#u64
    swap
    · -- a bound notification
      simp only [bne_iff_ne, ne_eq, hnb, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
      apply run_liftME_err
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn), hbt]
      simp only [Notif.optRef, hnb, ↓reduceIte]
      generalize xn.ntfnObj = o
      cases o <;> exact run_throw_bind _ _ _
    obtain ⟨s1, σ1, hrc, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    simp only [hnb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok, hrc, bind_ntfn_eq]
    refine (WP.spec_ok _).2 ?_
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps)).run σ =
        ({(.ok (.invokeTCB (.notificationControl p.bv (some q.bv))), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn), hbt]
      simp only [Notif.optRef, hnb, ↓reduceIte]
      cases ho : xn.ntfnObj with
      | waitingNtfn qs => exact absurd ho (hnw qs)
      | idleNtfn => exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
      | activeNtfn b => exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
    obtain ⟨xc, hkc, -⟩ := hDS.1.1.tcb ct htcb
    have hk1 := restart_kheap hkc (by rw [← hcur]; exact hst1)
    have hqc : q.bv ≠ ct.bv := by intro e; rw [e, hkc] at hkn; cases hkn
    have hkn1 : σ1.kheap q.bv = some (.notification xn) := by rw [hk1, Function.update_of_ne hqc]; exact hkn
    obtain ⟨xp1, hkp1, -⟩ := hDS1.1.1.tcb p hp
    have hrun : (Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeTCB (.notificationControl p.bv (some q.bv)))).run σ1 =
        ({(.ok [], Notif.updK (Notif.updK σ1 q.bv
          (.notification (Fl4Spec.ntfnBoundTcbUpdate (fun _ => some p.bv) xn))) p.bv
            (.tcb (Fl4Spec.tcbBoundNotificationUpdate (fun _ => some q.bv) xp1)))}, False) := by
      show (Fl4Spec.invokeTcb (Z := Unit) (.notificationControl p.bv (some q.bv))).run σ1 = _
      simp only [Fl4Spec.invokeTcb]
      exact run_liftE' (by rw [nd_bind_one (bindNotification_eq hkn1 hkp1)]; rfl)
    have hS2a : SlotsSame th (L.mem s1) (L.mem (L.wr s1 (Notif.nBoundA q) p)) := by
      rw [Notif.nBoundA_eq]
      exact ntfnw_slots hP s1 p (hNP.ntfn q hqN) (fun a ha => hNA a ha q hqN) 24#u64 (by simp) (by simp)
    have hS2b : SlotsSame th (L.mem (L.wr s1 (Notif.nBoundA q) p))
        (L.mem (L.wr (L.wr s1 (Notif.nBoundA q) p) (P1.boundA p) q)) := by
      unfold P1.boundA
      exact tcbw_slots hP _ q hp 3368#u64 (by simp) (by simp) (by simp)
    obtain ⟨hC2, hF2⟩ := crel_of_ck hDS1.1 hDS1.2.2 (hS2a.trans hS2b) (ck_bound hkn1 hkp1 _ _)
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), by rw [hrun]; exact Set.mem_singleton _, th, G,
      Or.inl ⟨rfl, [], rfl⟩, hP, hC2, hF2, MdbOKV.of_same hDS1.1.2.2.1
        (hS2a.trans hS2b) (MdbOKV.of_same hDS.1.2.2.1 hS1 hFR)⟩
  all_goals
    rw [hc] at hsp1
    simp only [error.illegal, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    rw [hsp1]
    exact run_throw_bind _ _ _

end


/-! ## UnbindNotification -/

section Spec
open Fl4Spec

/-- The caller's restart keeps every TCB's bound notification. -/
theorem restart_tcb {σ σ1 : State Unit} {ct t : ObjRef} {xc xt : Tcb} (hkc : σ.kheap ct = some (.tcb xc))
    (hkt : σ.kheap t = some (.tcb xt)) (h : setThreadState (Z := Unit) ct .restart σ = ({((), σ1)}, False)) :
    ∃ y, σ1.kheap t = some (.tcb y) ∧ y.tcbBoundNotification = xt.tcbBoundNotification := by
  rw [restart_kheap hkc h]
  by_cases e : t = ct
  · subst e; rw [hkc] at hkt; cases hkt
    exact ⟨_, Function.update_self .., rfl⟩
  · exact ⟨xt, by rw [Function.update_of_ne e]; exact hkt, rfl⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`tcb::decode` at `TCBUnbindNotification`** (`TcbOK`): l4v's
`decode_unbind_notification` (the target's bound notification, by `hbnd`),
the restart and `invoke_tcb (NotificationControl t None)`
(`unbind_notification`), with the CSpace relation and `FinInv` after. -/
theorem tcb_unbind_ntfn_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbUnbindNotification)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    {N T : Set U64} (hNR : Notif.NtfnStateRel N T (L.mem s) σ) (hNP : Notif.NPlaced T N)
    (hNA : ∀ a, IsSlot th a → ∀ n ∈ N, a.val + 32 ≤ n.val ∨ n.val + 40 ≤ a.val)
    (hbnd : ∀ xp, σ.kheap p.bv = some (.tcb xp) → xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)))
    (hbN : L.mem s (P1.boundA p) ≠ 0#u64 → L.mem s (P1.boundA p) ∈ N)
    (blk don : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBUnbindNotification p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  show (do
    let i ← obj.Tcb.bound_ntfn st p s
    if (i : U64).val = (0#u64).val then do
        let r ← error.illegal Unit
        ok (r, s, ar)
      else do
        let s2 ← tcb.restart_caller st s
        let s3 ← notification.unbind_notification st s2 p
        ok (core.result.Result.Ok (), s3, ar)) ⦃ r => TopPostM (L := L) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (Fl4Spec.Cap.threadCap p.bv))) s r ⦄
  rw [tcb_bound_eq]
  simp only [bind_ok, ← u64_eq_iff]
  obtain ⟨xp, hkp, -⟩ := hDS.1.1.tcb p hp
  have hbp := hbnd xp hkp
  have hsp0 : (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)).run σ =
      ((match Notif.optRef (L.mem s (P1.boundA p)) with
        | none => Fl4Spec.NonDetE.throwError .illegalOperation
        | some _ => Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.notificationControl p.bv none)).run σ := by
    simp only [Fl4Spec.decodeUnbindNotification]
    rw [lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
      (Notif.threadGet_eq _ hkp), hbp]
    generalize Notif.optRef (L.mem s (P1.boundA p)) = o
    cases o <;> rfl
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  · simp only [hb0, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_throw_bind _ _ _
  simp only [hb0, ↓reduceIte]
  set n := L.mem s (P1.boundA p) with hn
  have hnN := hbN hb0
  obtain ⟨xn, hkn, -⟩ := hNR.ntfn n hnN
  obtain ⟨s1, σ1, hrc, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  have hb1 : L.mem s1 (P1.boundA p) = n := by
    unfold P1.boundA
    exact restart_keeps hP hs1 htcb hp hact 3368#u64 (by simp) (by simp) (by simp)
  rw [hrc]; simp only [bind_ok]
  rw [unbind_ntfn_eq s1 p (by rw [hb1]; exact hb0), hb1]
  simp only [bind_ok]
  refine (WP.spec_ok _).2 ?_
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.notificationControl p.bv none)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
  obtain ⟨xc, hkc, -⟩ := hDS.1.1.tcb ct htcb
  have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
    rw [← hcur]; exact hst1
  have hk1 := restart_kheap hkc hst1'
  have hnc : n.bv ≠ ct.bv := by intro e; rw [e, hkc] at hkn; cases hkn
  have hkn1 : σ1.kheap n.bv = some (.notification xn) := by rw [hk1, Function.update_of_ne hnc]; exact hkn
  obtain ⟨xp1, hkp1, hbx⟩ := restart_tcb hkc hkp hst1'
  have hbx1 : xp1.tcbBoundNotification = some n.bv := by
    rw [hbx, hbp]; simp only [Notif.optRef, hb0, ↓reduceIte]
  have hrun : (Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeTCB (.notificationControl p.bv none))).run σ1 =
      ({(.ok [], Notif.updK (Notif.updK σ1 n.bv
        (.notification (Fl4Spec.ntfnBoundTcbUpdate (fun _ => none) xn))) p.bv
          (.tcb (Fl4Spec.tcbBoundNotificationUpdate (fun _ => none) xp1)))}, False) := by
    show (Fl4Spec.invokeTcb (Z := Unit) (.notificationControl p.bv none)).run σ1 = _
    simp only [Fl4Spec.invokeTcb]
    exact run_liftE' (by rw [nd_bind_one (unbindNotification_eq hkn1 hkp1 hbx1)]; rfl)
  have hS2a : SlotsSame th (L.mem s1) (L.mem (L.wr s1 (Notif.nBoundA n) 0#u64)) := by
    rw [Notif.nBoundA_eq]
    exact ntfnw_slots hP s1 0#u64 (hNP.ntfn n hnN) (fun a ha => hNA a ha n hnN) 24#u64 (by simp) (by simp)
  have hS2b : SlotsSame th (L.mem (L.wr s1 (Notif.nBoundA n) 0#u64))
      (L.mem (L.wr (L.wr s1 (Notif.nBoundA n) 0#u64) (P1.boundA p) 0#u64)) := by
    unfold P1.boundA
    exact tcbw_slots hP _ 0#u64 hp 3368#u64 (by simp) (by simp) (by simp)
  obtain ⟨hC2, hF2⟩ := crel_of_ck hDS1.1 hDS1.2.2 (hS2a.trans hS2b) (ck_bound hkn1 hkp1 _ _)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), by rw [hrun]; exact Set.mem_singleton _, th, G,
    Or.inl ⟨rfl, [], rfl⟩, hP, hC2, hF2, MdbOKV.of_same hDS1.1.2.2.1
      (hS2a.trans hS2b) (MdbOKV.of_same hDS.1.2.2.1 hS1 hFR)⟩

end


/-! ## SetSchedParams -/

section Spec
open Fl4Spec

/-- The SC step of `invoke_tcb ThreadControlSched`. -/
def scStep (t : ObjRef) (sco : Option (Option ObjRef)) : SMonad Unit Unit :=
  NonDet.maybeM (fun scopt =>
      match scopt with
      | none => do
          let scPtrOpt ← getTcbObjRef Tcb.tcbSchedContext t
          let scPtr ← NonDet.assertOpt scPtrOpt
          schedContextUnbindTcb scPtr
      | some scPtr => schedContextBindTcb scPtr t) sco

theorem presC_threadSet {g : Tcb → Tcb} (hg : ∀ x, tcbCnodeMap (g x) = tcbCnodeMap x) (t : ObjRef) :
    PresC (threadSet (Z := Unit) g t) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact CK.updTcb hk (hg _)

theorem presC_setMcpriority (t : ObjRef) (m : Priority) : PresC (setMcpriority (Z := Unit) t m) :=
  presC_threadSet (fun x => by unfold tcbCnodeMap; rfl) t

theorem presC_scStep (t : ObjRef) (sco : Option (Option ObjRef)) : PresC (scStep t sco) := by
  unfold scStep
  refine presC_maybeM (fun scopt => ?_) sco
  cases scopt with
  | none => exact presC_of_pres (f := (false, false)) (pres_bind (pres_threadGet _ _ _) fun _ =>
      pres_bind (pres_assertOpt _) fun _ => pres_schedContextUnbindTcb _ _)
  | some q => exact presC_of_pres (f := (false, false)) (pres_schedContextBindTcb _ _ _)

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- What `thread_control_sched` does after the fault-handler install, with
`SCHED_UPDATE_MCP` and `SCHED_UPDATE_PRIO` (and `SCHED_UPDATE_SC` when
`scf`). -/
def schedTail (s2 : S) (a1 : A) (t mcp prio sc : U64) (scf : Bool) :
    Result (core.result.Result Unit error.Exc × S × A) := do
  let s3 ← obj.Tcb.set_mcp st t s2 mcp
  let s4 ← sched.set_priority st s3 t prio
  if scf then
    let b ← obj.Sc.is_null sc
    if b then
      let i4 ← obj.Tcb.sc st t s4
      let b1 ← obj.Sc.is_null i4
      if b1 then ok (core.result.Result.Ok (), s4, a1)
      else
        let s5 ← schedcontext.unbind_tcb st s4 i4
        ok (core.result.Result.Ok (), s5, a1)
    else
      let (s5, a2) ← schedcontext.bind_tcb st arI s4 a1 sc t
      ok (core.result.Result.Ok (), s5, a2)
  else ok (core.result.Result.Ok (), s4, a1)

/-- `thread_control_sched` with `SCHED_UPDATE_FAULT`, `_MCP`, `_PRIO` (and
`_SC` when `scf`): the fault-handler install, then `schedTail`. -/
theorem tcs_fault_eq (s : S) (a : A) (t : U64) (slot : obj.Slot) (c : capability.Cap) (s1 : obj.Slot)
    (mcp prio sc : U64) (scf : Bool) :
    tcb.thread_control_sched st arI s a t slot (c, s1) mcp prio sc
      (if scf then (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC)
        else (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT)) =
      (do
        let (r, s2, a1) ← tcb.install_tcb_cap st arI s a t slot layout.tcb.SLOT_FAULT_HANDLER c s1
        match r with
        | .Ok _ => schedTail (st := st) arI s2 a1 t mcp prio sc scf
        | .Err e => ok (.Err e, s2, a1)) := by
  unfold tcb.thread_control_sched schedTail
  have f1 : ((4#u64 ||| 8#u64 ||| 2#u64) &&& 2#u64 != 0#u64) = true := by decide
  have f2 : ((4#u64 ||| 8#u64 ||| 2#u64) &&& 4#u64 != 0#u64) = true := by decide
  have f3 : ((4#u64 ||| 8#u64 ||| 2#u64) &&& 8#u64 != 0#u64) = true := by decide
  have f4 : ((4#u64 ||| 8#u64 ||| 2#u64) &&& 1#u64 != 0#u64) = false := by decide
  have g1 : ((4#u64 ||| 8#u64 ||| 2#u64 ||| 1#u64) &&& 2#u64 != 0#u64) = true := by decide
  have g2 : ((4#u64 ||| 8#u64 ||| 2#u64 ||| 1#u64) &&& 4#u64 != 0#u64) = true := by decide
  have g3 : ((4#u64 ||| 8#u64 ||| 2#u64 ||| 1#u64) &&& 8#u64 != 0#u64) = true := by decide
  have g4 : ((4#u64 ||| 8#u64 ||| 2#u64 ||| 1#u64) &&& 1#u64 != 0#u64) = true := by decide
  cases scf <;>
  simp only [lift, bind_ok, tcb.SCHED_UPDATE_MCP, tcb.SCHED_UPDATE_FAULT, tcb.SCHED_UPDATE_PRIO,
    tcb.SCHED_UPDATE_SC, Bool.false_eq_true, ↓reduceIte, f1, f2, f3, f4, g1, g2, g3, g4, uncurry_apply_pair] <;>
  congr 1 <;>
  funext x <;>
  obtain ⟨r, s2, a1⟩ := x <;>
  cases r <;> simp only [bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]

end


section Spec
open Fl4Spec

theorem runE_bind_congr {α β : Type} {m m' : SEMonad Unit α} {f : α → SEMonad Unit β} {σ : State Unit}
    (h : m.run σ = m'.run σ) : (m >>= f).run σ = (m' >>= f).run σ := by
  rw [ExceptT.run_bind, nd_bind_congr h, ExceptT.run_bind]

/-- l4v `decode_update_sc` with a null SC cap. -/
theorem dus_null {σ : State Unit} {p : ObjRef} {xp : Tcb} (hkp : σ.kheap p = some (.tcb xp)) (sl : CslotPtr) :
    (decodeUpdateSc (Z := Unit) (.threadCap p) sl .nullCap).run σ =
      ((NonDetE.whenE (p = σ.curThread) (NonDetE.throwError .illegalOperation) >>= fun _ =>
        (NonDetE.returnOk (if xp.tcbSchedContext ≠ none then some none else none) :
          SEMonad Unit (Option (Option ObjRef)))) : SEMonad Unit _).run σ := by
  simp only [decodeUpdateSc, objRefOf]
  rw [retOk_bind, lE_bind (m := getTcbObjRef (Z := Unit) Tcb.tcbSchedContext p) (Notif.threadGet_eq _ hkp),
    lE_bind (m := NonDet.gets fun s : State Unit => s.curThread) rfl]
  by_cases h : p = σ.curThread
  · rw [whenE_pos h, run_throw_bind, run_throw_bind]
  · rw [whenE_neg h, retOk_bind, retOk_bind, retOk_bind]

/-- l4v `decode_update_sc` with an SC cap. -/
theorem dus_sc {σ : State Unit} {p sc : ObjRef} {xp : Tcb} {y : SchedContext} {n : Nat}
    (hkp : σ.kheap p = some (.tcb xp)) (hks : σ.kheap sc = some (.schedContext y n)) (hne : scActive y = true → y.scRefills ≠ [])
    (sl : CslotPtr) (sz : Nat) :
    (decodeUpdateSc (Z := Unit) (.threadCap p) sl (.schedContextCap sc sz)).run σ =
      ((NonDetE.whenE (xp.tcbSchedContext ≠ some sc ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none))
          (NonDetE.throwError .illegalOperation) >>= fun _ =>
        NonDetE.whenE (ipcQueuedThreadState xp.tcbState ∧ ¬ scReleased σ.curTime y)
          (NonDetE.throwError .illegalOperation) >>= fun _ =>
        (NonDetE.returnOk (if xp.tcbSchedContext ≠ some sc then some (some sc) else none) :
          SEMonad Unit (Option (Option ObjRef)))) : SEMonad Unit _).run σ := by
  simp only [decodeUpdateSc, objRefOf]
  rw [retOk_bind, lE_bind (m := getTcbObjRef (Z := Unit) Tcb.tcbSchedContext p) (Notif.threadGet_eq _ hkp),
    retOk_bind, lE_bind (m := getScObjRef (Z := Unit) SchedContext.scTcb sc)
    (by unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl)]
  by_cases h1 : (xp.tcbSchedContext ≠ some sc ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none))
  · rw [whenE_pos h1, run_throw_bind, run_throw_bind]
  · rw [whenE_neg h1, retOk_bind, retOk_bind,
      lE_bind (m := isBlocked (Z := Unit) p)
        (show (getThreadState (Z := Unit) p >>= fun x => pure (ipcQueuedThreadState x)) σ = _ by
        rw [nd_bind_one (Notif.getThreadState_eq hkp)]; rfl),
      lE_bind (m := getScReleased (Z := Unit) sc) (getScReleased_eq hks hne)]
    by_cases h2 : ipcQueuedThreadState xp.tcbState = true ∧ ¬scReleased σ.curTime y = true
    · rw [whenE_pos h2]; simp only [retOk_bind, run_throw_bind]
    · rw [whenE_neg h2]; simp only [retOk_bind]

/-- l4v `decode_update_sc` with any other cap: `InvalidCapability 2`. -/
theorem dus_other {σ : State Unit} {p : ObjRef} {xp : Tcb} (hkp : σ.kheap p = some (.tcb xp)) (sl : CslotPtr)
    {cp : Cap} (h1 : cp ≠ .nullCap) (h2 : ∀ a b, cp ≠ .schedContextCap a b) :
    (decodeUpdateSc (Z := Unit) (.threadCap p) sl cp).run σ = ({(.error (.invalidCapability 2), σ)}, False) := by
  cases cp
  all_goals first
    | exact absurd rfl h1
    | exact absurd rfl (h2 _ _)
    | (simp only [decodeUpdateSc, objRefOf]
       rw [retOk_bind, lE_bind (m := getTcbObjRef (Z := Unit) Tcb.tcbSchedContext p) (Notif.threadGet_eq _ hkp)]
       exact run_throw_bind _ _ _)

/-- **What `decode_update_sc` checked** of the target `p` and the SC step
`sco` (an unbind: the target is not current and has an SC; a bind: the
target has no SC, the SC has no TCB, and a queued target's SC is released). -/
def ScDec (σ : State Unit) (p : ObjRef) (sco : Option (Option ObjRef)) : Prop :=
  ∃ x, σ.kheap p = some (.tcb x) ∧
    (sco = some none → p ≠ σ.curThread ∧ x.tcbSchedContext ≠ none) ∧
    (∀ v, sco = some (some v) → x.tcbSchedContext = none ∧ ∃ y n, σ.kheap v = some (.schedContext y n) ∧
      y.scTcb = none ∧ (ipcQueuedThreadState x.tcbState = true → scReleased σ.curTime y = true))

end Spec


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem flagsF : (tcb.UPDATE_FAULT &&& tcb.UPDATE_TIMEOUT) = 0#u64 ∧ (tcb.UPDATE_FAULT &&& tcb.UPDATE_SPACE) = 0#u64 ∧
    (tcb.UPDATE_FAULT &&& tcb.UPDATE_IPC_BUFFER) = 0#u64 := by
  simp only [tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]; decide

/-- `thread_control_caps` with only `UPDATE_FAULT`: the fault-handler install. -/
theorem tcc_fault_eq (s : S) (a : A) (t : U64) (slot : obj.Slot) (fh tmh cr vr buf : capability.Cap × obj.Slot)
    (addr : U64) :
    tcb.thread_control_caps st arI s a t slot fh tmh cr vr addr buf tcb.UPDATE_FAULT =
      (do
        let (r, s2, a1) ← tcb.install_tcb_cap st arI s a t slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2
        ok (r, s2, a1)) := by
  unfold tcb.thread_control_caps
  have f1 : (tcb.UPDATE_FAULT &&& tcb.UPDATE_FAULT != 0#u64) = true := by simp only [tcb.UPDATE_FAULT]; decide
  have f2 : (tcb.UPDATE_FAULT &&& tcb.UPDATE_TIMEOUT != 0#u64) = false := by
    simp only [tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT]; decide
  have f3 : (tcb.UPDATE_FAULT &&& tcb.UPDATE_SPACE != 0#u64) = false := by
    simp only [tcb.UPDATE_FAULT, tcb.UPDATE_SPACE]; decide
  have f4 : (tcb.UPDATE_FAULT &&& tcb.UPDATE_IPC_BUFFER != 0#u64) = false := by
    simp only [tcb.UPDATE_FAULT, tcb.UPDATE_IPC_BUFFER]; decide
  obtain ⟨c, s1⟩ := fh
  simp only [lift, bind_ok, f1, f2, f3, f4, Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair]
  congr 1
  funext x
  obtain ⟨r, s2, a1⟩ := x
  cases r <;> simp only [bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
    bind_tc_ok]

/-- **The scheduler step of SetSchedParams** (for the scheduler-queue and
SC refinements to come): after the caller's restart and an Ok install of
the fault handler, FL4's `set_mcp`, `set_priority` and SC bind/unbind
(`schedTail`) keep every slot word and succeed, and the spec's
`set_mcpriority`, `set_priority` and SC step have an outcome (that they
keep the CSpace is `presC_setMcpriority`, `presC_setPriority`,
`presC_scStep`). The SC arguments are those of a decoded SetSchedParams,
with `decode_update_sc`'s checks (`ScDec`); the target is not the idle
thread (l4v `valid_global_refs`) and the fault handler's source is a slot.
Discharged by `schedTailHyp_disch` (ScInstPost). -/
def SchedTailHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p mcp prio scv x2 : U64) (scf : Bool) (ssl : Fl4Spec.CslotPtr)
    (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (q : Fl4Spec.ObjRef) (sco : Option (Option Fl4Spec.ObjRef))
    (s2 : S) (a1 : A) (σ2 : Fl4Spec.State Unit) (G2 : MdbGhost),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    th p = some .tcb → mcp.val < 256 → prio.val < 256 →
    (sco = none ↔ scf = false) → (sco = some none → scv = 0#u64) →
    (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) →
    ScDec σ p.bv sco → p ≠ L.idleW s → IsSlot th x2 →
    tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
      ok (.Ok (), s2, a1) →
    (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
    DState (L := L) th s2 σ2 G2 →
    schedTail (st := st) arI s2 a1 p mcp prio scv scf ⦃ r => SlotsSame th (L.mem s2) (L.mem r.2.1) ∧
      r.1 = .Ok () ∧ ∃ σa σb σc, ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 ∧
        ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 prio.bv) σa).1 ∧
        ((), σc) ∈ (scStep p.bv sco σb).1 ⦄

/-- **SetSchedParams after its checks**: the caller's restart, the
fault-handler install (`install_ok`, the CSpace side's) and the scheduler
step (`SchedTailHyp`), against `invoke_tcb ThreadControlSched`; a preempted
install is the spec's preempted install. -/
theorem ssp_tail [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl) (x2 : U64) (e2 : Fl4Spec.Cap × Fl4Spec.CslotPtr)
    (hxe2 : x2 = cslotAddr e2.2) (he21 : e2.1 = absCap (capV (L.mem s) x2)) (ps : U64)
    (hps : th ps = some (.cnode e2.2.2.length)) (hps1 : e2.2.1 = ps.bv)
    (hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2)))
    (y0 y1 scv : U64) (hy0 : y0.val < 256) (hy1 : y1.val < 256) (scf : Bool) (q : Fl4Spec.ObjRef)
    (sco : Option (Option Fl4Spec.ObjRef)) (h1 : sco = none ↔ scf = false) (h2 : sco = some none → scv = 0#u64)
    (h3 : ∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64)
    (hD : ScDec σ p.bv sco) (hpI : p ≠ L.idleW s)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (hdec : DecOut m σ (.invokeTCB (.threadControlSched p.bv ssl (some e2) (some (Fl4Spec.ucast 8 y0.bv, q))
      (some (Fl4Spec.ucast 8 y1.bv, q)) sco)))
    (hH : SchedTailHyp (L := L) arI th s σ ct) (blk call don : Bool) :
    (do
      let s1 ← tcb.restart_caller st s
      tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (capV (L.mem s) x2, x2) y0 y1 scv
        (if scf then (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC)
          else (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT))) ⦃ res =>
      TopPostM (L := L) σ blk call don m s res ⦄ := by
  obtain ⟨s1, σ1, hrc, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  rw [hrc]; simp only [bind_ok]; rw [tcs_fault_eq]
  have hxs : IsSlot th x2 := by rw [hxe2]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1) x2 = capV (L.mem s) x2 := hS1.capV hxs
  have hnf := vfh_not_frame hv
  obtain ⟨hO, hPP, hPD, K, hK, hK6, hB⟩ := hT
  have hok : NewCapOK th (L.mem s1) (capV (L.mem s) x2) e2.2 := by
    rw [← hc1, hxe2]; exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe2, hc1]; exact hnf)
  have hI := install_okQ arI (Q := MdbOKV (L.ksb s)) (MdbOKV.step _) th hP hO hPP hPD K hK hK6 hB s1 s1 ar σ1 G
    hDS1 (MdbOKV.of_same hDS.1.2.2.1 hS1 hFR) p hp 3 (by simp [tcbSlots])
    layout.tcb.SLOT_FAULT_HANDLER (by simp [layout.tcb.SLOT_FAULT_HANDLER]) (InstFr.refl _ _ _) ssl hAs
    (capV (L.mem s) x2) e2.2 hok (fun _ => vfh_ep hv)
  rw [← hxe2] at hI
  obtain ⟨⟨r, s2, a1⟩, hins, σ', G', hc, hDS', hfr2⟩ := spec_exists hI
  have he2 : e2 = (absCap (capV (L.mem s) x2), e2.2) := by rw [← he21]
  rw [hins]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hc with ⟨hr, hx, -⟩ | ⟨hr, hx⟩
  · simp only at hr; subst hr
    rw [← he2] at hx
    refine WP.spec_mono (hH s1 σ1 ar p y0 y1 scv x2 scf ssl e2 q sco s2 a1 σ' G' hs1 (by rw [← hcur]; exact hst1)
      hp hy0 hy1 h1 h2 h3 hD hpI hxs hins hx hDS') ?_
    rintro ⟨r5, s5, a5⟩ ⟨hS5, hr5, σa, σb, σc, ha, hb, hcc⟩
    simp only at hr5 hS5; subst hr5
    obtain ⟨hC2, hF2⟩ := crel_of_ck hDS'.1 hDS'.2.2 hS5 ((presC_setMcpriority _ _ σ' _ ha).trans
      ((presC_setPriority _ _ σa _ hb).trans (presC_scStep _ _ σb _ hcc)))
    refine Or.inr ⟨_, hdec, σ1, hst1, (.ok [], σc), ?_, th, G', Or.inl ⟨rfl, [], rfl⟩, hP, hC2, hF2,
      MdbOKV.of_same hDS'.1.2.2.1 hS5 hfr2⟩
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
      (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1).1
    simp only [Fl4Spec.invokeTcb]
    exact mem_bindE_ok hx (mem_bindE_ok (mem_liftE ha) (mem_bindE_ok (mem_liftE hb)
      (mem_bindE_ok (mem_liftE hcc) (Set.mem_singleton _))))
  · simp only at hr; subst hr
    rw [← he2] at hx
    refine (WP.spec_ok _).2 (Or.inr ⟨_, hdec, σ1, hst1, (.error (), σ'), ?_, th, G', Or.inr ⟨rfl, rfl⟩, hP,
      hDS'.1, hDS'.2.2, hfr2⟩)
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) (.threadControlSched p.bv ssl (some e2)
      (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ1).1
    simp only [Fl4Spec.invokeTcb]
    exact mem_bindE_err hx

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem decode_ssp_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetSchedParams p c = tcb.decode_set_sched_params st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSuspend_val, lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- The spec's `check_prio` against the authority's `MCP` word. -/
theorem checkPrio_run {s : S} {σ : Fl4Spec.State Unit} {T : Set U64} (hM : McpRel T (L.mem s) σ) {q : U64}
    (hq : q ∈ T) (v : Fl4Spec.Data) :
    (Fl4Spec.checkPrio (Z := Unit) v q.bv).run σ =
      (Fl4Spec.NonDetE.whenE (v > (L.mem s (mcpA q)).bv)
        (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
  obtain ⟨xq, hkq, hmq⟩ := hM q hq
  have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
    apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
    have := xq.tcbMcpriority.isLt; omega
  unfold Fl4Spec.checkPrio
  rw [lE_bind (Notif.threadGet_eq _ hkq), hu]

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`tcb::decode` at `TCBSetSchedParams`** (`TcbOK`): l4v's
`decode_set_sched_params` (the authority's MCP checks by `McpRel`; the SC
checks of `decode_update_sc` by `SchedRel`, `NtfnStateRel`; the fault
handler), the restart and `invoke_tcb ThreadControlSched` (`ssp_tail`: the
CSpace side's install, then `SchedTailHyp`), with the CSpace relation and
`FinInv` after. -/
theorem tcb_set_sched_params_refines [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
   
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSchedParams)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (hpI : p ≠ L.idleW s)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    {N T C : Set U64} {c : U64} (hS : SchedRel st N T C c s σ) (hR : Notif.NtfnStateRel N T (L.mem s) σ)
    (hpT : p ∈ T) (hM : McpRel T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ C) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    (hH : SchedTailHyp (L := L) arI th s σ ct)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetSchedParams p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF
  rw [decode_ssp_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostM (L := L) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSchedParams
    by_cases ha : args.length < 2
    · rw [whenE_pos (by simpa using ha)]
      exact run_throw_bind _ _ _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_throw_bind _ _ _
  unfold tcb.decode_set_sched_params tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  have ha1 := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 1#u64 y1 (by simp))
  simp only [ha0, ha1, bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexl : ¬ excaps.length < 3 := by
    have := (List.getElem?_eq_some_iff.1 he2).1; omega
  -- the spec up to the authority's cap
  have hspec0 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = ((match e0.1 with
        | .threadCap tcbPtr => Fl4Spec.NonDetE.returnOk tcbPtr
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.checkPrio (Z := Unit) y0.bv q >>= fun _ => Fl4Spec.checkPrio (Z := Unit) y1.bv q >>= fun _ =>
        Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q)) (some (Fl4Spec.ucast 8 y1.bv, q)) sco)).run σ := by
    unfold Fl4Spec.decodeSetSchedParams
    rw [whenE_neg (by simp), retOk_bind, whenE_neg hexl, retOk_bind, retOk_bind, retOk_bind, retOk_bind,
      retOk_bind, retOk_bind, he0, he1, he2, the_some, the_some, the_some]
    generalize e0.1 = cc
    cases cc <;> rfl
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  swap
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩)
    apply run_liftME_err
    rw [hspec0, he01]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_throw_bind _ _ _
  obtain ⟨q, hq⟩ := hth
  rw [thread_arg_thread s 1#u64 hq]
  simp only [bind_ok, check_prio_eq]
  have hqT := hcapT h0 q hq
  have he0' : e0.1 = .threadCap q.bv := by rw [he01, hq]; rfl
  rw [he0'] at hspec0
  simp only [] at hspec0
  rw [retOk_bind] at hspec0
  have hcp0 := checkPrio_run hM hqT y0.bv
  have hcp1 := checkPrio_run hM hqT y1.bv
  obtain ⟨xq, hkq, hmq⟩ := hM q hqT
  have hmq8 : (L.mem s (mcpA q)).val < 256 := by rw [hmq]; exact xq.tcbMcpriority.isLt
  by_cases hg0 : y0 > L.mem s (mcpA q)
  · rw [ite_eq_left hg0]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg0)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg0]
  simp only [bind_ok]
  by_cases hg1 : y1 > L.mem s (mcpA q)
  · rw [ite_eq_left hg1]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩)
    apply run_liftME_err
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hg1)]
    exact run_throw_bind _ _ _
  rw [ite_eq_right hg1]
  simp only [bind_ok]
  have hy0 : y0.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y0.val := hg0; omega
  have hy1 : y1.val < 256 := by have : ¬ (L.mem s (mcpA q)).val < y1.val := hg1; omega
  have hspec1 : (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1 >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rw [hspec0, runE_bind_congr hcp0, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg0), retOk_bind,
      runE_bind_congr hcp1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hg1), retOk_bind]
  obtain ⟨Q, R', hcL, hsL⟩ := hS.lists
  obtain ⟨xp, hkp, -, -, hxts, -⟩ := hsL.tcb p hpT
  have hsc0 : obj.Tcb.sc st p s = ok (L.mem s (P1.scA p)) := by
    obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Tcb.sc.spec (L := L) s p); exact hw
  -- after the SC check: the fault handler, the restart and the invocation
  have hafter : ∀ (scv : U64) (sco : Option (Option Fl4Spec.ObjRef)),
      (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl e1.1).run σ = ({(.ok sco, σ)}, False) →
      (sco = none ↔ (L.mem s (P1.scA p) != scv) = false) → (sco = some none → scv = 0#u64) →
      (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) → ScDec σ p.bv sco →
      (do
        let i ← lift (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO)
        let flags ← lift (i ||| tcb.SCHED_UPDATE_FAULT)
        if (L.mem s (P1.scA p) != scv) = true then do
            let flags1 ← lift (flags ||| tcb.SCHED_UPDATE_SC)
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags1
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)
          else do
            let fh ← obj.Slot.cap st x2 s
            let b ← faults.valid_fault_handler fh
            if b = true then do
                let s1 ← tcb.restart_caller st s
                tcb.thread_control_sched st arI s1 ar p (cslotAddr ssl) (fh, x2) y0 y1 scv flags
              else do
                let r7 ← error.invalid_cap Unit 3#u64
                ok (r7, s, ar)) ⦃ res => TopPostM (L := L) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
    intro scv sco hdus hs1 hs2 hs3 hD
    simp only [lift, bind_ok, slot_cap_eq, capAt_capV, vfh_eq]
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x2))
    · simp only [decide_eq_true hv, ↓reduceIte]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (.threadControlSched p.bv ssl (some e2)
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he21]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e2) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]; rfl
      by_cases hscf : (L.mem s (P1.scA p) != scv) = true
      · simp only [hscf, ↓reduceIte]
        have h1' : sco = none ↔ true = false := by rw [hs1, hscf]
        have := ssp_tail arI th hP hT s ar σ G hDS hFR p hp ct hct hcur htcb hact ssl hAs x2 e2 hxe2 he21 ps2 hps2 hps21
          hv y0 y1 scv hy0 hy1 true q.bv sco h1' hs2 hs3 hD hpI _ (DecOut.of_eq hdec) hH blk call don
        simp only [↓reduceIte] at this
        exact this
      · simp only [Bool.not_eq_true] at hscf
        simp only [hscf, Bool.false_eq_true, ↓reduceIte]
        have h1' : sco = none ↔ false = false := by rw [hs1, hscf]
        have := ssp_tail arI th hP hT s ar σ G hDS hFR p hp ct hct hcur htcb hact ssl hAs x2 e2 hxe2 he21 ps2 hps2 hps21
          hv y0 y1 scv hy0 hy1 false q.bv sco h1' hs2 hs3 hD hpI _ (DecOut.of_eq hdec) hH blk call don
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        exact this
    · simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      have hiv : ∀ (scf : Bool), (ok ((.Err (.Sys (.InvalidCapability 3#u64)) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostM (L := L) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
        intro _
        refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 3, ?_, Or.inr ⟨3#u64, rfl, rfl⟩⟩)
        apply run_liftME_err
        rw [hspec1, run_bind_ok_st hdus]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he21]; exact hv)]
        exact run_bind_error (run_throw_bind _ _ _) _
      split <;> exact hiv true
  have hpre : ∀ cp : Fl4Spec.Cap, e1.1 = cp →
      (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl cp >>= fun sco =>
        Fl4Spec.checkHandlerEp (Z := Unit) 3 e2 >>= fun fh =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl (some fh)
          (some (Fl4Spec.ucast 8 y0.bv, q.bv)) (some (Fl4Spec.ucast 8 y1.bv, q.bv)) sco)).run σ := by
    rintro cp rfl; exact hspec1
  unfold tcb.sched_params_sc
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc1 : capV (L.mem s) x1
  case Null =>
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    rw [hct]
    simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
    by_cases hpc : p = ct
    · simp only [decide_eq_true hpc, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
      apply run_liftME_err
      rw [hspec1]
      refine run_bind_error ?_ _
      rw [dus_null hkp ssl, whenE_pos (by rw [hcur, hpc])]
      exact run_throw_bind _ _ _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte, bind_ok, hsc0]
      have hpc' : ¬ p.bv = σ.curThread := by rw [hcur]; intro e; exact hpc (P1.eq_of_bv e)
      refine hafter 0#u64 _ (by rw [he11, hc1]; simp only [absCap]; rw [dus_null hkp ssl, whenE_neg hpc', retOk_bind]; rfl)
        ?_ (fun _ => rfl) (fun v h => by split at h <;> cases h)
        ⟨xp, hkp, fun h => ⟨hpc', fun e => (by simp [e] at h)⟩, fun v h => (by split at h <;> cases h)⟩
      rw [hxts]
      by_cases hz : L.mem s (P1.scA p) = 0#u64
      · simp [hz, Notif.optRef_zero]
      · simp [hz, Notif.optRef_ne hz]
  case SchedContext ptr sz =>
    rw [he11, hc1] at hspec1
    simp only [absCap] at hspec1
    have hpC := hcapC h1 ptr sz hc1
    have hptr0 := hC0 ptr hpC
    obtain ⟨y, n, hks, hx⟩ := hsL.scs ptr hpC
    have hne : Fl4Spec.scActive y = true → y.scRefills ≠ [] := fun ha => by
      rw [(hx.strong ha).refills]; exact refills_ne (hx.strong ha).wf
    have hdus := dus_sc hkp hks hne ssl (sz.val - Fl4Spec.minSchedContextBits)
    have hst := (hR.at_tcb hpT hkp).st
    have hxt' : y.scTcb = Notif.optRef (L.mem s (scW ptr 24#u64)) := hx.tcb
    have hcons : (((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = none ↔
          (L.mem s (P1.scA p) != ptr) = false) ∧
        ((if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some none → ptr = 0#u64) ∧
        (∀ v, (if xp.tcbSchedContext ≠ some ptr.bv then some (some ptr.bv) else none) = some (some v) →
          v = ptr.bv ∧ ptr ≠ 0#u64)) := by
      rw [hxts]
      refine ⟨?_, (fun h => by split at h <;> cases h), (fun v h => by split at h <;> cases h; exact ⟨rfl, hptr0⟩)⟩
      simp only [ne_eq, bv_optRef_some hptr0]
      by_cases e : L.mem s (P1.scA p) = ptr <;> simp [e]
    have hillT : (Fl4Spec.decodeUpdateSc (Z := Unit) (.threadCap p.bv) ssl
          (.schedContextCap ptr.bv (sz.val - Fl4Spec.minSchedContextBits))).run σ =
          ({(.error .illegalOperation, σ)}, False) →
        (ok ((.Err (.Sys .IllegalOperation) : core.result.Result Unit error.Exc), s, ar) :
          Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostM (L := L) σ blk call don
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetSchedParams (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)) s res ⦄ := by
      intro h
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩)
      apply run_liftME_err
      rw [hspec1]
      exact run_bind_error h _
    simp only [hsc0, bind_ok]
    by_cases hip : L.mem s (P1.scA p) = ptr
    · -- the thread's own SC
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hxts, hip, Notif.optRef_ne hptr0]; simp
      rw [if_neg (show ¬ (L.mem s (P1.scA p) != ptr) = true by simp [hip])]
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h),
              fun v h => (by rw [if_neg (by rw [hxts, hip, Notif.optRef_ne hptr0]; simp)] at h; cases h)⟩
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

    · have hne1 : (L.mem s (P1.scA p) != ptr) = true := by simp [hip]
      simp only [hne1, ↓reduceIte]
      by_cases hi0 : L.mem s (P1.scA p) = 0#u64
      swap
      · have : (L.mem s (P1.scA p) != 0#u64) = true := by simp [hi0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hxts, Ne, bv_optRef_some hptr0]; exact hip,
          Or.inl (by rw [hxts, Notif.optRef_ne hi0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (P1.scA p) != 0#u64) = false := by simp [hi0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hscT : obj.Sc.tcb st ptr s = ok (L.mem s (scW ptr 24#u64)) := by
        obtain ⟨w, hw, rfl⟩ := spec_exists (P1.obj.Sc.tcb.spec (L := L) s ptr); rw [scTcbA_eq] at hw; exact hw
      simp only [hscT, bind_ok]
      have hx0n : xp.tcbSchedContext = none := by rw [hxts, hi0, Notif.optRef_zero]
      by_cases ht0 : L.mem s (scW ptr 24#u64) = 0#u64
      swap
      · have : (L.mem s (scW ptr 24#u64) != 0#u64) = true := by simp [ht0]
        simp only [this, ↓reduceIte, error.illegal, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine hillT ?_
        rw [hdus, whenE_pos ⟨by rw [hx0n]; simp, Or.inr (by rw [hxt', Notif.optRef_ne ht0]; simp)⟩]
        exact run_throw_bind _ _ _
      have : (L.mem s (scW ptr 24#u64) != 0#u64) = false := by simp [ht0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hc1' : ¬ (xp.tcbSchedContext ≠ some ptr.bv ∧ (xp.tcbSchedContext ≠ none ∨ y.scTcb ≠ none)) := by
        rw [hx0n, hxt', ht0, Notif.optRef_zero]; simp
      obtain ⟨bb, hbb, rfl⟩ := spec_exists (is_blocked_spec s p xp.tcbState hst)
      rw [hbb]; simp only [bind_ok]
      by_cases hb : Fl4Spec.ipcQueuedThreadState xp.tcbState = true
      · simp only [hb, ↓reduceIte]
        obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sc_released_refines s σ hS hpC hks)
        rw [hb1e]; simp only [bind_ok]
        rw [getScReleased_eq hks hne] at hb1
        have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
        by_cases hr : b1 = true
        · simp only [hr, ↓reduceIte, bind_ok]
          refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
            ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun _ => by rw [← hr, eb])⟩)⟩⟩
          rw [he11, hc1]; simp only [absCap]
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by rw [eb, hr]; simp), retOk_bind]; rfl
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine hillT ?_
          rw [hdus, whenE_neg hc1', retOk_bind, whenE_pos ⟨hb, by rw [eb]; simpa using hr⟩
]
          exact run_throw_bind _ _ _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        refine hafter _ _ ?_ hcons.1 hcons.2.1 hcons.2.2
          ⟨xp, hkp, fun h => (by split at h <;> cases h), fun v h => ⟨hx0n, (by
              have hv : v = ptr.bv := (by split at h <;> cases h; rfl)
              subst hv
              exact ⟨y, n, hks, (by rw [hxt', ht0, Notif.optRef_zero]), (fun hq => absurd hq hb)⟩)⟩⟩
        rw [he11, hc1]; simp only [absCap]
        rw [hdus, whenE_neg hc1', retOk_bind, whenE_neg (by simp [hb]), retOk_bind]; rfl

  all_goals
    rw [he11, hc1] at hspec1
    simp only [error.invalid_cap, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 2, ?_, Or.inr ⟨2#u64, rfl, rfl⟩⟩)
    apply run_liftME_err
    rw [hspec1]
    exact run_bind_error (dus_other hkp ssl (by simp [absCap]) (by simp [absCap])) _

end

end

end Fl4Proofs.P3.Sched
