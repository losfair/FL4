/-
P3 (DESIGN.md §9), invariant line G1 (rd8j, KENTRY-PLAN rd8h handoff 1):
**`BindRel` for ThreadControlSched's new SC from the decode** (spec side only,
outside the JAtZ cone).

* `okp_bind` / `okp_bind_pin` / `pin_checkPrio`: OkP combinators for a step
  whose `ok` outcomes keep the state (`check_prio` only reads the MCP).
* **`okp_decodeUpdateSc`**: `decode_update_sc` returns `some (some c)` only
  when the TCB's SC is none, `c`'s `sc_tcb` is none and ¬ (blocked ∧ ¬
  released) at the decode's state (l4v Decode_A.decode_update_sc), i.e.
  rd8b's `BindRel σ c t` (`BlkR` states are `ipc_queued`, sb2's `RNE` for the
  released read).
* `RdTi σ i` / `RdT σ iv`: a ThreadControlSched with a new SC satisfies
  `BindRel` at `σ`; **`okp_fl4DecodeRdT`**: every decode outcome from `σ`
  satisfies `RdT σ` (walk: fl4DecodeInvocation .threadCap →
  fl4DecodeTcbInvocation → decodeTcbInvocation .tcbSetSchedParams →
  decodeSetSchedParams → decodeUpdateSc).
* **`rdTi_perform`**: a decoded TCB invocation satisfies `RdTi` at the perform
  (after the shell's `set_thread_state ct Restart`), by rd8c's `bindRel_bk`
  along the decode's BK view and `bindRel_setThreadState`.
-/
import Fl4Proofs.P3.SpecInvRd8cD
import Fl4Proofs.P3.SpecInvRd8hP
open Classical

namespace Fl4Proofs.P3.SInvR.B8j
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvB

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Combinators -/

section OkPj
variable {ε α β : Type} {σ : State Unit}

theorem okp_bind {P : β → Prop} {Q : α → Prop} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : OkP σ Q m) (hg : ∀ a, Q a → OkA P (g a)) :
    OkP σ P (m >>= g) := by
  intro c s hc
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hc
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    exact hg a (hm a s' hz) s' c s hy
  · simp at he

theorem okp_bind_pin {P : β → Prop} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → s = σ) (hg : ∀ a, OkP σ P (g a)) :
    OkP σ P (m >>= g) := by
  intro c s hc
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hc
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have e := hm a s' hz
    subst e
    exact hg a c s hy
  · simp at he

end OkPj

theorem pin_checkPrio (p : Data) (t : ObjRef) (σ : State Unit) :
    ∀ a s, ((.ok a, s) : Except SyscallError Unit × State Unit) ∈ ((checkPrio (Z := Unit) p t).run σ).1 →
      s = σ := by
  intro a s h
  unfold checkPrio at h
  obtain ⟨z, hz, ⟨m, hm, h⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' h
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
    obtain ⟨x', -, rfl⟩ := SInvQ.q1_mem_threadGet hx
    unfold NonDetE.whenE at h
    split at h
    · unfold NonDetE.throwError at h
      rw [ExceptT.run_throw] at h
      have e := Set.mem_singleton_iff.1 h
      simp at e
    · rw [ExceptT.run_pure] at h
      have e := Set.mem_singleton_iff.1 h
      simp only [Prod.mk.injEq] at e
      exact e.2
  · simp at he

/-! ## `decode_update_sc` -/

theorem okp_decodeUpdateSc (σ : State Unit) (hN : SInvB.RNE σ) (cap : Cap) (slot : CslotPtr) (scCap : Cap) :
    OkP σ (fun r => (∃ x, σ.kheap (objRefOf cap) = some (.tcb x)) ∧
        ∀ c, r = some (some c) → BindRel σ c (objRefOf cap))
      (decodeUpdateSc (Z := Unit) cap slot scCap) := by
  unfold decodeUpdateSc
  refine okp_returnOk_bind ?_
  refine okp_liftE_bind (Q := fun o => ∃ x, σ.kheap (objRefOf cap) = some (.tcb x) ∧ o = x.tcbSchedContext)
    (fun y hy => ?_) fun tcbSc ⟨x, hx, ho⟩ => ?_
  · unfold getTcbObjRef at hy
    obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hy
    exact ⟨rfl, x, hx, rfl⟩
  (try dsimp only)
  cases scCap
  case nullCap =>
    refine okp_liftE_bind (Q := fun _ => True) (fun y hy => ⟨by rw [Set.mem_singleton_iff.1 hy], trivial⟩)
      fun _ _ => ?_
    refine okp_whenE_bind fun _ => okp_returnOk_bind (okp_returnOk ⟨⟨x, hx⟩, fun c hc => ?_⟩)
    split_ifs at hc <;> cases hc
  case schedContextCap scp sz =>
    refine okp_returnOk_bind ?_
    refine okp_liftE_bind (Q := fun o => ∃ y n, σ.kheap (objRefOf (Cap.schedContextCap scp sz)) =
        some (.schedContext y n) ∧ o = y.scTcb) (fun z hz => ?_) fun scTcb ⟨y, n, hy, hs⟩ => ?_
    · obtain ⟨e, y, n, hk, h⟩ := SInvQ.cq5_mem_getScObjRef hz
      exact ⟨e, y, n, hk, h⟩
    refine okp_whenE_bind fun h1 => ?_
    refine okp_liftE_bind (Q := fun bl => bl = ipcQueuedThreadState x.tcbState) (fun z hz => ?_)
      fun bl hbl => ?_
    · unfold isBlocked NonDet.liftM getThreadState at hz
      obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨x', hx', rfl⟩ := SInvQ.q1_mem_threadGet hw
      rw [hx] at hx'; cases hx'
      rw [Set.mem_singleton_iff.1 hz]
      exact ⟨rfl, rfl⟩
    refine okp_liftE_bind (Q := fun r => r = scReleased σ.curTime y) (fun z hz => ?_) fun r hr => ?_
    · rw [Sched.getScReleased_eq hy (fun ha => hN _ y n hy (Or.inr ha))] at hz
      obtain rfl := Set.mem_singleton_iff.1 hz
      exact ⟨rfl, rfl⟩
    refine okp_whenE_bind fun h3 => okp_returnOk_bind (okp_returnOk ⟨⟨x, hx⟩, fun c hc => ?_⟩)
    split_ifs at hc with hne
    simp only [Option.some.injEq] at hc
    subst hc
    have h2 : ¬ (tcbSc ≠ none ∨ scTcb ≠ none) := fun h => h1 ⟨hne, h⟩
    push_neg at h2
    refine ⟨fun y' n' hy' => ?_, fun x' hx' => ?_⟩
    · rw [hy] at hy'; cases hy'; rw [← hs]; exact h2.2
    · rw [hx] at hx'; cases hx'
      refine ⟨by rw [← ho]; exact h2.1, fun hb => ⟨y, n, hy, ?_⟩⟩
      have hq : ipcQueuedThreadState x.tcbState = true := blkR_ipcQueued hb
      subst hbl; subst hr
      by_contra hn
      exact h3 ⟨hq, hn⟩
  all_goals exact okp_throw_bind _

/-! ## The TCB decode -/

/-- **ThreadControlSched's new SC** satisfies `BindRel` at the decode's state. -/
def RdTi (σ : State Unit) : TcbInvocation → Prop
  | .threadControlSched t _ (some _) _ _ sc =>
    (∃ x, σ.kheap t = some (.tcb x)) ∧ ∀ c, sc = some (some c) → BindRel σ c t
  | .threadControlSched t _ none _ _ (some (some c)) => BindRel σ c t
  | _ => True

/-- `RdTi` on the decoded invocation. -/
def RdT (σ : State Unit) : Fl4Invocation → Prop
  | .invokeTCB i => RdTi σ i
  | _ => True

theorem okp_decodeSetSchedParams (σ : State Unit) (hN : SInvB.RNE σ) (args : List Data) (cap : Cap)
    (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) :
    OkP σ (RdTi σ) (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams
  refine okp_whenE_bind fun _ => okp_whenE_bind fun _ => ?_
  refine okp_returnOk_bind (okp_returnOk_bind (okp_returnOk_bind (okp_returnOk_bind (okp_returnOk_bind ?_))))
  (try dsimp only)
  split
  · refine okp_returnOk_bind ?_
    refine okp_bind_pin (pin_checkPrio _ _ σ) fun _ => ?_
    refine okp_bind_pin (pin_checkPrio _ _ σ) fun _ => ?_
    refine okp_bind (okp_decodeUpdateSc σ hN cap slot _) fun r hr => ?_
    exact okA_bind fun fh => okA_returnOk hr
  · exact okp_throw_bind _

set_option maxHeartbeats 4000000 in
theorem okp_decodeTcbInvocation (σ : State Unit) (hN : SInvB.RNE σ) (label : Data) (args : List Data)
    (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) :
    OkP σ (RdTi σ) (decodeTcbInvocation (Z := Unit) label args cap slot excs) := by
  unfold decodeTcbInvocation
  split
  case h_9 => exact okp_decodeSetSchedParams σ hN args cap slot excs
  all_goals refine okp_of_okA ?_
  all_goals first
    | exact okA_throw _
    | exact okA_returnOk trivial
    | (unfold decodeReadRegisters; okA_auto)
    | (unfold decodeWriteRegisters; okA_auto)
    | (unfold decodeCopyRegisters; okA_auto)
    | (unfold decodeTcbConfigure; okA_auto)
    | (unfold decodeSetPriority; okA_auto)
    | (unfold decodeSetMcpriority; okA_auto)
    | (unfold decodeSetTimeoutEp; okA_auto)
    | (unfold decodeSetIpcBuffer; okA_auto)
    | (unfold decodeSetSpace; okA_auto)
    | (unfold decodeBindNotification; okA_auto)
    | (unfold decodeUnbindNotification; okA_auto)
    | (unfold decodeSetTlsBase; okA_auto)
    | (unfold decodeSetFlags; okA_auto)

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `RdT` of the decode's state.** -/
theorem okp_fl4DecodeRdT (σ : State Unit) (hN : SInvB.RNE σ) (fp : Bool) (label : Data) (args : List Data)
    (ci : CapRef) (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkP σ (RdT σ) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    refine okp_ite (okp_throw _) ?_
    unfold fl4DecodeTcbInvocation
    refine okp_ite (okp_of_okA (okA_liftME (okA_triv fun _ => trivial))) ?_
    split
    · exact okp_of_okA (okA_liftME (okA_triv fun _ => trivial))
    · exact okp_liftME (okp_decodeTcbInvocation σ hN label args _ sl ex)
  | _ =>
    unfold fl4DecodeInvocation
    refine okp_of_okA ?_
    repeat' (first
      | exact okA_throw _ | exact okA_returnOk trivial
      | (exact okA_liftME (okA_triv fun _ => trivial))
      | (refine okA_ite ?_ ?_)
      | (dsimp only)
      | split)

/-- **A decoded TCB invocation satisfies `RdTi` at the perform** (after the
shell's `set_thread_state ct Restart`); `RNE` (sb2's `ScInv`) at the decode's
state. -/
theorem rdTi_perform {σ : State Unit} (hN : SInvB.RNE σ) {fp : Bool} {label : Data} {args : List Data}
    {ci : CapRef} {sl : CslotPtr} {cap : Cap} {ex : List (Cap × CslotPtr)} {buf : Option ObjRef}
    {i : TcbInvocation} {s : State Unit}
    (h : ((.ok (.invokeTCB i), s) : Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1)
    (c0 : ObjRef) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) c0 .restart s).1) :
    RdTi y.2 i := by
  have hD : RdTi σ i := okp_fl4DecodeRdT σ hN fp label args ci sl cap ex buf _ s h
  have hV : BKv s = BKv σ := bk_fl4DecodeInvocation (V := BKv σ) fp label args ci sl cap ex buf σ rfl _ h
  have hT : ∀ t, (∃ x, σ.kheap t = some (.tcb x)) → ∃ x, y.2.kheap t = some (.tcb x) := by
    intro t ⟨x, hx⟩
    have e := congrFun (congrArg (fun v : BKw => v.1) hV) t
    simp only [BKv] at e
    rw [hx] at e
    obtain ⟨x1, hx1, -⟩ := tcbV_some e
    have e2 := (SVK.sv_setThreadState' c0 .restart s y hy).1 t
    rw [hx1] at e2
    obtain ⟨x2, hx2, -⟩ := SVK.sv_tcb e2
    exact ⟨x2, hx2⟩
  cases i <;> try trivial
  rename_i t sl' fh mcp prio sc
  rcases fh with _ | f
  · rcases sc with _ | _ | c
    · trivial
    · trivial
    · exact bindRel_setThreadState (bindRel_bk hV hD) hy
  · exact ⟨hT t hD.1, fun c hc => bindRel_setThreadState (bindRel_bk hV (hD.2 c hc)) hy⟩

/-- ThreadControlSched's `TcbOK` binding half from `RdTi`. -/
theorem tcbOK_bind_of {σ : State Unit} {t : ObjRef} {sl : CslotPtr} {fh mcp prio}
    {sc : Option (Option ObjRef)} (h : RdTi σ (.threadControlSched t sl fh mcp prio sc)) :
    ∀ c, sc = some (some c) → BindRel σ c t := by
  intro c hc
  subst hc
  rcases fh with _ | f
  · exact h
  · exact h.2 c rfl

/-- ThreadControlSched with a fault handler: the target is a TCB. -/
theorem tcbOK_tcb_of {σ : State Unit} {t : ObjRef} {sl : CslotPtr} {fh mcp prio}
    {sc : Option (Option ObjRef)} (h : RdTi σ (.threadControlSched t sl fh mcp prio sc)) (hf : fh ≠ none) :
    ∃ x, σ.kheap t = some (.tcb x) := by
  rcases fh with _ | f
  · exact absurd rfl hf
  · exact h.1

end

end Fl4Proofs.P3.SInvR.B8j
