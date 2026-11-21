/-
P3 (DESIGN.md §9), invariant line G1 (il2): **IfLiveT across
`perform_invocation`** (il1 handoff step 3; spec side only).

* `ILP N K σ := ILN K σ ∧ P3 N σ` (IfLiveT with NtfnQB ∧ EpQB and ut7's `P3`,
  i.e. UtInv3 at the IRQ node `N`): what a perform that deletes caps needs.
* `il_doReplyTransfer` (the receiver is read BlockedOnReply, so it joins `K`).
* `il_capMove`, `il_capSwapR` (a moved / swapped cap keeps its thread-cap-ness:
  ut5's `RefEq`, `refEq_tc`), **`il_invokeCnode`** from ut7's `CnOKN`.
* `ilp_installTcbCap`, `ilp_installTcbFrameCap` (cap_delete, then a checked
  insert), **`il_invokeTcb`**: a resumed / register-written / register-copied
  target must hold a thread cap (`tcbRT`, in `K`).
* The decode's facts: `TgI cap i` (a TCB invocation's restart target is the
  invoked thread cap's thread: `okv_tgI`), `FpI fp i` (a first-phase decode,
  ReplyRecv / NBSendRecv / NBSendWait's send phase, never yields a CNode or TCB
  invocation: `okv_fpI`).
* **`il_fl4PerformInvocation (hG : PerfGapIL)`**: post `IL []`, and `IL K` for a
  first-phase invocation (only CNode / TCB invocations remove thread caps).
  `PerfGapIL` [P]: the untyped and arch performs keep `IL K` (they write no
  thread cap: untyped / MakePool detype only null slots, ut4's RegNull; retype
  at fresh addresses, default TCBs Inactive; arch performs rewrite arch caps)
  — the analogue of ut7's `PerfGap`, discharged by the il2 handoff.
-/
import Fl4Proofs.P3.SpecInvNtfnQLD
import Fl4Proofs.P3.SpecInvUtP6
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

/-- IfLiveT, NtfnQB ∧ EpQB and UtInv3 at the IRQ node `N`. -/
def ILP (N : Irq → ObjRef) (K : List ObjRef) (σ : State Unit) : Prop := ILN K σ ∧ P3 N σ

theorem ilp_ilu {N : Irq → ObjRef} {σ : State Unit} (h : ILP N [] σ) : ILU σ := ⟨h.1, h.2.1⟩

theorem il_nil_of {K : List ObjRef} {σ : State Unit} (h : IL K σ) : IL [] σ := il_mono h fun _ h => by cases h

/-! ## `do_reply_transfer` -/

set_option maxHeartbeats 4000000 in
/-- `do_reply_transfer`: the receiver is read BlockedOnReply, so it joins `K`. -/
theorem il_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    ILK Kq (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine ik_bind (by il_auto) fun recvOpt => ?_
  refine ik_maybeM (fun receiver => ?_) recvOpt
  unfold getThreadState
  refine ik_threadGet_bind fun σ x hx => ?_
  (try dsimp only)
  cases hs : x.tcbState
  case blockedOnReply r =>
    refine ikp_ilcons hx (liveSt_eq hs True.intro) ?_
    (try dsimp only)
    refine ik_bind (ik_assert _) fun _ => ?_
    refine ik_bind (by il_auto) fun _ => ?_
    refine ik_bind (by il_auto) fun scOpt => ?_
    refine ik_bind (by il_auto) fun _ => ?_
    refine ik_bind (by il_auto) fun fault => ?_
    cases fault <;> (try dsimp only) <;> il2_auto
  all_goals exact ikp_of_ik (by (try dsimp only); il_auto) σ

/-! ## Moves and swaps -/

theorem refEq_tc {c0 c : Cap} (h : RefEq c0 c) : ∀ t, c0 = .threadCap t → c = .threadCap t := by
  rintro t rfl
  rcases h with rfl | ⟨-, ho, hsh, hz, -, -, -, -⟩
  · rfl
  · cases c with
    | threadCap r =>
      have : r = t := by simpa [objRefs] using ho
      rw [this]
    | zombie r b n => exact absurd rfl (hz r b n)
    | _ => simp [shp] at hsh

theorem tp_capMove (σ0 : State Unit) (c : Cap) (src dest : CslotPtr) :
    IK (TP (StQ σ0)) (capMove (Z := Unit) c src dest) := by
  unfold capMove
  repeat' (first
    | ((with_reducible refine tp_setCap _ _ ?_); exact fun p x h => ⟨h, h, h, h, h, h⟩)
    | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _)
    | ik_step0 | ik_unfold)

/-- The caps after `cap_move`. -/
theorem capMove_caps {c : Cap} {src dest : CslotPtr} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (capMove (Z := Unit) c src dest σ).1) (x : CslotPtr) :
    SInvU.capAt y.2 x = if x = src then some .nullCap else if x = dest then some c else SInvU.capAt σ x := by
  unfold capMove at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hv1 := hv_setCap c dest (uV σ) σ rfl y1 h1
  have hv2 := hv_setCap .nullCap src (uV y1.2) y1.2 rfl y2 h2
  have hk : SInvU.capAt y.2 = SInvU.capAt y2.2 := by
    refine (?_ : IK (fun s => SInvU.capAt s = SInvU.capAt y2.2) _) y2.2 rfl y hy
    repeat' (first | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)
  rw [hk]
  show (uV y2.2).2.1 x = _
  rw [hv2, vCap_cap, hv1, vCap_cap]
  rfl

theorem il_of_caps {K : List ObjRef} {σ σ' : State Unit} (hσ : IL K σ) (hs : TP (StQ σ) σ')
    (hT : ∀ t, HasTC σ t → HasTC σ' t) : IL K σ' := by
  refine ⟨fun t x hx hl => ?_, fun t ht => hT t (hσ.2 t ht)⟩
  obtain ⟨y0, hy0, e⟩ := hs t x hx
  exact hT t (hσ.1 t y0 hy0 (e ▸ hl))

/-- **`cap_move`** of a cap that keeps the source cap's thread-cap-ness, into a null slot. -/
theorem il_capMove (c0 c : Cap) (src dest : CslotPtr) (σ : State Unit) (hs : SInvU.capAt σ src = some c0)
    (hd : SInvU.capAt σ dest = some .nullCap) (hr : ∀ t, c0 = .threadCap t → c = .threadCap t) :
    IKp (IL Kq) σ (capMove (Z := Unit) c src dest) := by
  intro hσ y hy
  have hcap := capMove_caps hy
  refine il_of_caps hσ (tp_capMove σ c src dest σ (fun p x hp => ⟨x, hp, rfl⟩) y hy) ?_
  rintro t ⟨x, hx⟩
  by_cases e1 : x = src
  · subst e1
    rw [hs] at hx; cases hx
    have hne : dest ≠ x := fun e => by rw [e, hs] at hd; cases hd
    exact ⟨dest, by rw [hcap, if_neg hne, if_pos rfl, hr t rfl]⟩
  · by_cases e2 : x = dest
    · subst e2; rw [hd] at hx; cases hx
    · exact ⟨x, by rw [hcap, if_neg e1, if_neg e2]; exact hx⟩

/-- **`cap_swap`** of caps keeping the read caps' thread-cap-ness. -/
theorem il_capSwapR (c1 c2 c1' c2' : Cap) (s1 s2 : CslotPtr) (σ : State Unit) (hne : s1 ≠ s2)
    (h1 : SInvU.capAt σ s1 = some c1') (h2 : SInvU.capAt σ s2 = some c2')
    (r1 : ∀ t, c1' = .threadCap t → c1 = .threadCap t) (r2 : ∀ t, c2' = .threadCap t → c2 = .threadCap t) :
    IKp (IL Kq) σ (capSwap (Z := Unit) c1 s1 c2 s2) := by
  intro hσ y hy
  have hv : uV y.2 = vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) (uV σ))) :=
    capSwap_view hne c1 c2 σ rfl y hy
  have hcap : ∀ x, SInvU.capAt y.2 x =
      if x = s2 then some c1 else if x = s1 then some c2 else SInvU.capAt σ x := by
    intro x
    show (uV y.2).2.1 x = _
    rw [hv, vCap_cap, vCap_cap]
    split_ifs with e2 e1 <;> first
      | rfl
      | (show (uV σ).2.1 (sw s1 s2 x) = _; unfold sw; rw [if_neg e1, if_neg e2]; rfl)
  refine il_of_caps hσ (tp_capSwap σ c1 c2 s1 s2 σ (fun p x hp => ⟨x, hp, rfl⟩) y hy) ?_
  rintro t ⟨x, hx⟩
  by_cases e1 : x = s1
  · subst e1
    rw [h1] at hx; cases hx
    exact ⟨s2, by rw [hcap, if_pos rfl, r1 t rfl]⟩
  · by_cases e2 : x = s2
    · subst e2
      rw [h2] at hx; cases hx
      exact ⟨s1, by rw [hcap, if_neg hne, if_pos rfl, r2 t rfl]⟩
    · exact ⟨x, by rw [hcap, if_neg e2, if_neg e1]; exact hx⟩

/-! ## `invoke_cnode` -/

theorem il_invokeCnode (N : Irq → ObjRef) (i : CnodeInvocation) (σ : State Unit) (hσ : ILP N [] σ)
    (hok : CnOKN (uV σ) i) : ∀ y ∈ ((invokeCnode (Z := Unit) i).run σ).1, IL [] y.2 := by
  cases i
  case revokeCall s => exact fun y hy => (ilu_capRevoke s σ (ilp_ilu hσ) y hy).1.1
  case deleteCall s => exact fun y hy => (ilu_capDelete s σ (ilp_ilu hσ) y hy).1.1
  case insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact il_capInsert c src dest σ hσ.1.1 x hx
  case moveCall c src dest =>
    obtain ⟨c0, hs, hd, hr, -, -, -⟩ := hok
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact il_capMove c0 c src dest σ hs hd (refEq_tc hr) hσ.1.1 x hx
  case rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, r1, -, r2, -, h21, h23, -, h3⟩ := hok
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · exact il_capSwapR c1 c2 c1' c2' s1 s2 σ (Ne.symm h21) h1 h2 (refEq_tc r1) (refEq_tc r2) hσ.1.1 x hx
    · rename_i e13
      obtain ⟨x1, hx1, hx⟩ := hx
      have hcaps := capMove_caps hx1
      have hL1 : IL [] x1.2 := il_capMove c2' c2 s2 s3 σ h2 (h3 e13) (refEq_tc r2) hσ.1.1 x1 hx1
      have h1' : SInvU.capAt x1.2 s1 = some c1' := by
        rw [hcaps, if_neg (Ne.symm h21), if_neg e13]; exact h1
      have h2' : SInvU.capAt x1.2 s2 = some .nullCap := by rw [hcaps, if_pos rfl]
      exact il_capMove c1' c1 s1 s2 x1.2 h1' h2' (refEq_tc r1) hL1 x hx
  case cancelBadgedSendsCall c =>
    intro y hy
    cases c
    case endpointCap ep b g =>
      simp only [invokeCnode, withoutPreemption] at hy
      exact (ike_liftE (ik_when _ (iln_cancelBadgedSends ep b)) σ hσ.1 y hy).1
    all_goals
      simp only [invokeCnode] at hy
      exact (ike_liftE ik_fail) σ hσ.1.1 y hy

/-! ## `invoke_tcb` -/

theorem ilp_installTcbCap (N : Irq → ObjRef) (target : ObjRef) (slot : CslotPtr) (n : Nat)
    (o : Option (Cap × CslotPtr)) (hn : n < 6) : IKE (ILP N []) (installTcbCap (Z := Unit) target slot n o) := by
  intro σ hσ y hy
  refine ⟨⟨?_, nq_installTcbCap target slot n o σ hσ.1.2 y hy⟩, p3_installTcbCap target slot n o hn σ hσ.2 y hy⟩
  revert y hy
  refine (?_ : HKE (ILP N []) (IL []) (installTcbCap (Z := Unit) target slot n o)) σ hσ
  cases o with
  | none => exact fun σ h y hy => ike_returnOk _ σ h.1.1 y hy
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine hke_bind (R := IL []) (fun σ h y hy => (ilu_capDelete _ σ (ilp_ilu h) y hy).1.1)
      (fun _ => hk_of_ik ?_) (fun _ h => h)
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (il_checkCapAt _ _ _ (il_checkCapAt _ _ _ (il_capInsert _ _ _)))

theorem ilp_installTcbFrameCap (N : Irq → ObjRef) (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (ILP N []) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  intro σ hσ y hy
  refine ⟨⟨?_, nq_installTcbFrameCap target slot buffer σ hσ.1.2 y hy⟩,
    un_installTcbFrameCap target slot buffer σ hσ.2 y hy⟩
  revert y hy
  refine (?_ : HKE (ILP N []) (IL []) (installTcbFrameCap (Z := Unit) target slot buffer)) σ hσ
  cases buffer with
  | none => exact fun σ h y hy => ike_returnOk _ σ h.1.1 y hy
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    simp only [installTcbFrameCap]
    exact hke_bind (R := IL []) (fun σ h y hy => (ilu_capDelete _ σ (ilp_ilu h) y hy).1.1)
      (fun _ => hk_of_ik (by il_auto)) (fun _ h => h)

/-- The threads a TCB invocation may make live (restart). -/
def tcbRT : TcbInvocation → List ObjRef
  | .resume t => [t]
  | .copyRegisters dest _ _ _ _ _ _ => [dest]
  | .writeRegisters dest _ _ _ => [dest]
  | _ => []

/-- **`invoke_tcb`**: its restart target holds a thread cap (in `K`). -/
theorem il_invokeTcb (N : Irq → ObjRef) (ti : TcbInvocation) (σ : State Unit) (K : List ObjRef)
    (hσ : ILP N K σ) (hK : ∀ t ∈ tcbRT ti, t ∈ K) :
    ∀ y ∈ ((invokeTcb (Z := Unit) ti).run σ).1, IL [] y.2 := by
  have h0 : ILP N [] σ := ⟨⟨il_nil_of hσ.1.1, hσ.1.2⟩, hσ.2⟩
  cases ti
  case threadControlCaps target slot fh th cr vr buf =>
    intro y hy
    have key : IKE (ILP N []) (invokeTcb (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) := by
      simp only [invokeTcb]
      exact ike_bind (ilp_installTcbCap N _ _ 3 _ (by decide)) fun _ =>
        ike_bind (ilp_installTcbCap N _ _ 4 _ (by decide)) fun _ =>
        ike_bind (ilp_installTcbCap N _ _ 0 _ (by decide)) fun _ =>
        ike_bind (ilp_installTcbCap N _ _ 1 _ (by decide)) fun _ =>
        ike_bind (ilp_installTcbFrameCap N _ _ _) fun _ => ike_returnOk _
    exact (key σ h0 y hy).1.1
  case threadControlSched target slot fh mcp prio sc =>
    intro y hy
    have key : HKE (ILP N []) (IL []) (invokeTcb (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) := by
      simp only [invokeTcb]
      exact hke_bind (R := IL []) (fun σ h y hy => (ilp_installTcbCap N _ _ 3 _ (by decide) σ h y hy).1.1)
        (fun _ => hk_of_ik (by il_auto)) (fun _ h => h)
    exact key σ h0 y hy
  case resume t =>
    have ht : t ∈ K := hK t (List.mem_singleton_self _)
    intro y hy
    refine il_nil_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    simp only [invokeTcb]; il_auto
  case copyRegisters dest src b1 b2 b3 b4 a =>
    have ht : dest ∈ K := hK dest (List.mem_singleton_self _)
    intro y hy
    refine il_nil_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    simp only [invokeTcb]; il_auto
  case writeRegisters dest r v a =>
    have ht : dest ∈ K := hK dest (List.mem_singleton_self _)
    intro y hy
    refine il_nil_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    simp only [invokeTcb]; il_auto
  case notificationControl t n =>
    intro y hy
    refine il_nil_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    cases n <;> simp only [invokeTcb] <;> il_auto
  all_goals
    intro y hy
    refine il_nil_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    simp only [invokeTcb]; il_auto

/-! ## The decode's facts -/

/-- A TCB invocation's restart target is `p`. -/
def TgT (p : ObjRef) : TcbInvocation → Prop
  | .resume t => t = p
  | .copyRegisters dest _ _ _ _ _ _ => dest = p
  | .writeRegisters dest _ _ _ => dest = p
  | _ => True

/-- A TCB invocation came from a thread cap `cap = threadCap p` with restart target `p`. -/
def TgI (cap : Cap) : Fl4Invocation → Prop
  | .invokeTCB ti => ∃ p, cap = .threadCap p ∧ TgT p ti
  | _ => True

/-- Not a CNode or TCB invocation (the only ones removing thread caps). -/
def NoDelI : Fl4Invocation → Prop
  | .invokeCNode _ => False
  | .invokeTCB _ => False
  | _ => True

macro "tg_step" : tactic => `(tactic| first
  | exact okv_throw _ | exact okv_throw' _ | exact okv_liftE_fail
  | exact okv_returnOk trivial | exact okv_returnOk rfl
  | (refine okv_returnOk_bind ?_) | (refine okv_pure_bind ?_)
  | (refine okv_whenE_bind fun _ => ?_) | (refine okv_unlessE_bind fun _ => ?_)
  | (refine okv_ite ?_ ?_)
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_)
  | (dsimp only) | split)

set_option maxHeartbeats 8000000 in
/-- The TCB decode of `threadCap p`: every restart target is `p`. -/
theorem okv_tcbDec {w : UView} (label : Data) (args : List Data) (p : ObjRef) (sl : CslotPtr)
    (ex : List (Cap × CslotPtr)) : OkV w (TgT p) (decodeTcbInvocation (Z := Unit) label args (.threadCap p) sl ex) := by
  unfold decodeTcbInvocation
  split
  all_goals first
    | (exact okv_throw _)
    | (exact okv_returnOk trivial)
    | (exact okv_returnOk rfl)
    | (set_option maxHeartbeats 40000000 in
       (first
        | unfold decodeReadRegisters | unfold decodeWriteRegisters | unfold decodeCopyRegisters
        | unfold decodeTcbConfigure | unfold decodeSetPriority | unfold decodeSetMcpriority
        | unfold decodeSetSchedParams | unfold decodeSetTimeoutEp | unfold decodeSetIpcBuffer
        | unfold decodeSetSpace | unfold decodeBindNotification | unfold decodeUnbindNotification
        | unfold decodeSetTlsBase | unfold decodeSetFlags)
       repeat' tg_step)

theorem okv_tgI {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkV w (TgI cap) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    refine okv_ite (okv_throw _) ?_
    unfold fl4DecodeTcbInvocation
    refine okv_ite (okv_liftME (okv_triv fun _ => trivial)) ?_
    split
    · exact okv_liftME (okv_triv fun _ => trivial)
    · exact okv_liftME (okv_mono (okv_tcbDec label args p sl ex) fun ti h => ⟨p, rfl, h⟩)
  | _ =>
    unfold fl4DecodeInvocation
    dsimp only
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_))

theorem okv_fpI {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkV w (fun i => fp = true → NoDelI i) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    exact okv_ite' (fun _ => okv_throw _) (fun hf => okv_triv fun _ h => absurd h hf)
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite' (fun _ => okv_throw _) (fun hf => okv_triv fun _ h => absurd h hf)
  | _ =>
    unfold fl4DecodeInvocation
    dsimp only
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk (fun _ => trivial)
      | (exact okv_liftME (okv_triv fun _ _ => trivial))
      | (refine okv_ite ?_ ?_))

/-! ## `perform_invocation` -/

/-- The restart targets of an invocation. -/
def invRT : Fl4Invocation → List ObjRef
  | .invokeTCB ti => tcbRT ti
  | _ => []

/-- **[P] The untyped and arch performs keep `IL K`** (ut7's `PerfGap` pattern;
not an invariant premise but an unproved lemma about two perform families):
they remove no thread cap — reset / MakePool detype only null slots (ut4's
`RegNull`) and objects no cap names, retype writes fresh addresses with
Inactive default TCBs and null slots, `create_cap` / the pool cap go into null
slots, the arch performs rewrite the invoked arch cap. l4v:
`invoke_untyped_invs`, `perform_asid_control_invocation_invs`,
`arch_perform_invocation_invs` (their `if_live_then_nonz_cap` parts). -/
def PerfGapIL : Prop :=
  ∀ (N : Irq → ObjRef) (K : List ObjRef) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit),
    GapInv inv → ILP N K σ → NodeIs N σ → DecodedFrom (uV σ) inv →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, IL K y.2

theorem il_app {K L : List ObjRef} {σ : State Unit} (h : IL K σ) (hL : ∀ t ∈ L, HasTC σ t) : IL (L ++ K) σ :=
  ⟨h.1, fun t ht => (List.mem_append.1 ht).elim (hL t) (h.2 t)⟩

theorem ilQ_of {K : List ObjRef} {fp : Bool} {s : State Unit} (h : IL K s) : IL [] s ∧ (fp = true → IL K s) :=
  ⟨il_nil_of h, fun _ => h⟩

set_option maxHeartbeats 4000000 in
/-- **`perform_invocation` keeps IfLiveT**, and `K` after a first-phase decode. -/
theorem il_fl4PerformInvocation (hG : PerfGapIL) (N : Irq → ObjRef) (bl call don fp : Bool) (i : Fl4Invocation)
    (σ : State Unit) (K : List ObjRef) (hσ : ILP N K σ) (hN : NodeIs N σ) (hct : σ.curThread ∈ K)
    (hT : ∀ t ∈ invRT i, HasTC σ t) (hF : fp = true → NoDelI i) (hok : InvOKN (uV σ) i)
    (hD : DecodedFrom (uV σ) i) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don i).run σ).1, IL [] y.2 ∧ (fp = true → IL K y.2) := by
  intro y hy
  cases i
  case invokeUntyped ui => exact ilQ_of (hG N K bl call don (.invokeUntyped ui) σ trivial hσ hN hD y hy)
  case invokeArchObject ai => exact ilQ_of (hG N K bl call don (.invokeArchObject ai) σ trivial hσ hN hD y hy)
  case invokeCNode ci =>
    refine ⟨?_, fun h => (hF h).elim⟩
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact il_invokeCnode N ci σ ⟨⟨il_nil_of hσ.1.1, hσ.1.2⟩, hσ.2⟩ hok z hz
  case invokeTCB ti =>
    refine ⟨?_, fun h => (hF h).elim⟩
    simp only [fl4PerformInvocation] at hy
    exact il_invokeTcb N ti σ (tcbRT ti ++ K) ⟨⟨il_app hσ.1.1 hT, hσ.1.2⟩, hσ.2⟩
      (fun t ht => List.mem_append_left _ ht) y hy
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    obtain ⟨z1, h1, hz⟩ := hx
    rw [mem_gets h1] at hz
    obtain ⟨z2, h2, hz⟩ := hz
    have hb := il_sendIpc bl call bd g gr don σ.curThread ep hct σ hσ.1.1 z2 h2
    rw [Set.mem_singleton_iff.1 hz]; exact ilQ_of hb
  case invokeNotification ep bd =>
    refine ilQ_of ((?_ : HKE (ILN K) (IL K) _) σ hσ.1 y hy)
    simp only [fl4PerformInvocation, withoutPreemption]
    exact hke_bind (R := IL K) (hk_liftE (fun s h z hz => (iln_sendSignal ep bd s h z hz).1))
      (fun _ => hk_of_ik (ike_returnOk _)) (fun _ h => h)
  case invokeReply rp gr =>
    refine ilQ_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    simp only [fl4PerformInvocation]
    exact ike_liftE (ik_bind (ik_gets _) fun _ => ik_bind (il_doReplyTransfer _ _ _) fun _ => ik_pure _)
  case invokeIRQHandler ih =>
    refine ilQ_of ((?_ : IKE (ILN K) _) σ hσ.1 y hy).1
    simp only [fl4PerformInvocation]
    exact ike_bind (ike_liftE (iln_invokeIrqHandler ih)) fun _ => ike_returnOk _
  all_goals
    refine ilQ_of ((?_ : ILKE K _) σ hσ.1.1 y hy)
    simp only [fl4PerformInvocation, withoutPreemption]
    il_auto

end

end Fl4Proofs.P3.SInv
