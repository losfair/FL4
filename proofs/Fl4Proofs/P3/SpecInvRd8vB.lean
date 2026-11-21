/-
P3 (DESIGN.md §9), invariant line G1 (rd8v): **`VE` across the deletion recursion, retype / detype
and the perform layer** (KENTRY-PLAN rd8s handoff 2-3; spec side only, outside the JAtZ cone).

* `HTE P Q m` (`HT` over `ExceptT.run`), `hte_bind`, `hte_liftE`, `hte_ve`, `hte_and`.
* Retype / detype (rd8q's family skipped them): **`ve_retypeRegionWith`** (every written object is
  a `defaultObject`: an Inactive unbound TCB, an inactive SC or neither, so `OKV` holds over any old
  object), **`ve_deleteObjects`** (detype only removes objects: no thread becomes schedulable);
  then `ve_resetUntypedCap`, `ve_invokeUntypedWith`, `ve_performAsidControlInvocation`,
  `ve_archPerformInvocation`, `ve_fl4ArchPerformInvocation` by `ve_auto`.
* The deletion recursion by the least fixed point (`ik_lfp`, sb2's `si_recDelF` skeleton):
  **`ve_recDelF`**, **`ve_recDel`**, `ve_capDelete`, **`ve_capRevokeF`**, **`ve_capRevoke`**; then
  `ve_installTcbCap`, `ve_installTcbFrameCap`, **`ve_invokeCnode`**, **`ve_invokeTcb`**.
* The perform layer: **`ht_performInvocation`** / **`ht_fl4PerformInvocation`** :
  `HTE (VE E ∧ ScInv) (VE E)` (the Reply arm by `ht_doReplyTransfer`, the SchedControl arm by
  rd8s's `ht_invokeSchedControlConfigureFlags`, every other arm `VEKE E`).
-/
import Fl4Proofs.P3.SpecInvRd8vA
open Classical

namespace Fl4Proofs.P3.SInvR.B8v
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q Fl4Proofs.P3.SInvR.B8s

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

/-! ## Hoare triples over exception computations -/

/-- `HT` over the run of an exception computation (every result). -/
abbrev HTE (P Q : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  HT P Q (ExceptT.run m)

theorem hte_bind {P R Q : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : HTE P R m) (hg : ∀ a, HTE R Q (g a)) (hRQ : ∀ s, R s → Q s) :
    HTE P Q (m >>= g) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hg a s (hm σ hσ _ hz) y hy
  · exact hRQ _ (hm σ hσ _ hz)

theorem hte_liftE {P Q : State Unit → Prop} {ε α : Type} {m : NonDet (State Unit) α} (h : HT P Q m) :
    HTE P Q (NonDetE.liftE (ε := ε) m) := by
  intro σ hσ y hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact h σ hσ x hx

theorem hte_ve {ε α : Type} {m : NonDetE (State Unit) ε α} (h : VEKE E m) : HTE (VS E) (VE E) m :=
  fun σ h' x hx => h σ h'.1 x hx

theorem hte_and {P Q C : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : HTE P Q m)
    (hc : IKE C m) : HTE (fun s => P s ∧ C s) (fun s => Q s ∧ C s) m :=
  fun σ h' x hx => ⟨h σ h'.1 x hx, hc σ h'.2 x hx⟩

/-! ## Retype and detype -/

/-- A default object is an `OKV` write over any old object. -/
theorem okv_default (type : ApiObjectType) (ht : type ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain)
    (old : Option KernelObject) : OKV old (defaultObject type dev n d) := by
  cases type with
  | untyped => exact absurd rfl ht
  | tcbObject => exact okv_nr rfl
  | schedContextObject =>
    refine ⟨fun _ e => (by cases e), fun y m e ha => ?_⟩
    simp only [defaultObject] at e
    injection e with e _
    subst e
    exact absurd ha (by decide)
  | _ => exact okv_ntb (fun _ e => by cases e) (fun _ _ e => by cases e)

theorem ve_foldr {σ : State Unit} (h : VE E σ) (o : KernelObject) (ho : ∀ old, OKV old o) (ptrs : List ObjRef) :
    VE E { σ with kheap := ptrs.foldr (fun p kh => Function.update kh p (some o)) σ.kheap } := by
  induction ptrs with
  | nil => exact h
  | cons p ps ih => exact ve_upd ih p o (ho _)

/-- **`retype_region`** keeps `VE E` (no premise). -/
theorem ve_retypeRegionWith (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (num oBits : Nat)
    (type : ApiObjectType) (dev : Bool) : VEK E (retypeRegionWith (Z := Unit) bitsApi ptr num oBits type dev) := by
  unfold retypeRegionWith
  intro σ hσ x hx
  obtain ⟨y1, h1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at hx
  obtain ⟨y2, h2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h2] at hx
  obtain ⟨y3, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  try dsimp only at h3
  unfold NonDet.when at h3
  split at h3
  · rename_i ht
    obtain ⟨y4, h4, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 h4] at h3
    obtain ⟨y5, h5, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 h5] at h3
    obtain ⟨y6, h6, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 h6] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact ve_foldr hσ _ (okv_default type ht dev oBits _) _
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

theorem ve_retypeRegion (ptr : ObjRef) (num oBits : Nat) (type : ApiObjectType) (dev : Bool) :
    VEK E (retypeRegion (Z := Unit) ptr num oBits type dev) :=
  ve_retypeRegionWith objBitsApi ptr num oBits type dev

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_retypeRegion _ _ _ _ _)

theorem ve_detype {σ : State Unit} (h : VE E σ) (S : Set ObjRef) : VE E (detype S σ) := by
  refine ve_of h rfl rfl (fun _ _ _ _ hu => hu) fun t _ hs => ?_
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv hs
  simp only [detype] at hx hy hq
  split_ifs at hx hy
  exact Sched.schedulable_of hx hsc hrn hy ha hq

/-- **`delete_objects`** keeps `VE E` (no premise). -/
theorem ve_deleteObjects (ptr : Word) (bits : Nat) : VEK E (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (by ve_auto) fun _ => ?_
  intro σ hσ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ve_detype hσ _

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_deleteObjects _ _)

theorem ve_resetUntypedCap (sl : CslotPtr) : VEKE E (resetUntypedCap (Z := Unit) sl) := by
  unfold resetUntypedCap; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_resetUntypedCap _)

theorem ve_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) :
    VEKE E (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; ve_auto

theorem ve_invokeUntyped (ui : UntypedInvocation) : VEKE E (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeUntypedWith _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeUntyped _)

theorem ve_performAsidControlInvocation (iv : AsidControlInvocation) :
    VEK E (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_performAsidControlInvocation _)

theorem ve_archPerformInvocation (i : ArchInvocation) : VEKE E (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_archPerformInvocation _)

theorem ve_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : VEKE E (fl4ArchPerformInvocation (Z := Unit) i) := by
  unfold fl4ArchPerformInvocation; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_fl4ArchPerformInvocation _)

/-! ## The deletion recursion -/

/-- One step of `rec_del`, its recursive calls keeping `VE E`. -/
theorem ve_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, VEK E (f k)) (k : RecDelCall) : VEKE E (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, VEKE (ε := Unit) E (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ve_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ve_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ve_auto
    all_goals exact hrec' _

/-- **`rec_del`** keeps `VE E` (fuel / least-fixed-point induction over the steps). -/
theorem ve_recDel (c : RecDelCall) : VEKE E (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ve_recDelF hf k) c

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_recDel _)

theorem ve_capDelete (slot : CslotPtr) : VEKE E (capDelete (Z := Unit) slot) := by
  unfold capDelete; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_capDelete _)

/-- One step of `cap_revoke`, its recursive calls keeping `VE E`. -/
theorem ve_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, VEK E (f k)) (sl : CslotPtr) : VEKE E (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, VEKE (ε := Unit) E (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ve_auto
  all_goals exact hrec' _

/-- **`cap_revoke`** keeps `VE E`. -/
theorem ve_capRevoke (sl : CslotPtr) : VEKE E (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ve_capRevokeF hf k) sl

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_capRevoke _)

theorem ve_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    VEKE E (installTcbCap (Z := Unit) target slot n o) := by
  unfold installTcbCap; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_installTcbCap _ _ _ _)

theorem ve_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (o : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    VEKE E (installTcbFrameCap (Z := Unit) target slot o) := by
  unfold installTcbFrameCap; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_installTcbFrameCap _ _ _)

theorem ve_invokeCnode (i : CnodeInvocation) : VEKE E (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeCnode _)

set_option maxHeartbeats 4000000 in
theorem ve_invokeTcb (i : TcbInvocation) : VEKE E (invokeTcb (Z := Unit) i) := by
  cases i <;> simp only [invokeTcb] <;> ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeTcb _)

/-! ## The perform layer -/

/-- A step on ct read just before. -/
theorem ve_gets_ct {α : Type} {k : ObjRef → NonDet (State Unit) α}
    (h : ∀ t, HT (fun s => VE E s ∧ s.curThread = t) (VE E) (k t)) :
    VEK E (NonDet.gets (fun s : State Unit => s.curThread) >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ.curThread σ ⟨hσ, rfl⟩ x hx

/-- The Endpoint arm: `send_ipc` from ct (ct exempt as ct). -/
theorem ve_endpointArm (block call : Bool) (badge : Badge) (g gr d : Bool) (ep : ObjRef) :
    VEK E (do
      let thread ← NonDet.gets fun s : State Unit => s.curThread
      sendIpc (Z := Unit) block call badge g gr d thread ep
      return ([] : List Data)) :=
  ve_gets_ct fun t => ht_bind (ht_ct t (ve_sendIpc block call badge g gr d t ep) (by ct_auto))
    fun _ => ht_ik (by ve_auto)

/-- The Reply arm: `do_reply_transfer` from ct. -/
theorem ht_replyArm (reply : ObjRef) (grant : Bool) :
    HT (VS E) (VE E) (do
      let sender ← NonDet.gets fun s : State Unit => s.curThread
      doReplyTransfer (Z := Unit) sender reply grant
      return ([] : List Data)) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact ht_bind (ht_doReplyTransfer _ reply grant) (fun _ => ht_ik (by ve_auto)) σ hσ x hx

/-- **`perform_invocation`** keeps `VE E` (from carried `ScInv`). -/
theorem ht_performInvocation (b c d : Bool) (i : Invocation) :
    HTE (VS E) (VE E) (performInvocation (Z := Unit) b c d i) := by
  cases i
  case invokeReply r g =>
    simp only [performInvocation]
    exact hte_liftE (ht_replyArm r g)
  case invokeSchedControl iv =>
    simp only [performInvocation]
    exact hte_bind (hte_liftE (ht_invokeSchedControlConfigureFlags iv)) (fun _ => ht_ik (by ve_auto)) fun _ h => h
  case invokeEndpoint ep badge g gr =>
    simp only [performInvocation, withoutPreemption]
    exact hte_ve (ike_liftE (ve_endpointArm _ _ _ _ _ _ _))
  all_goals exact hte_ve (by simp only [performInvocation]; ve_auto)

/-- **`fl4_perform_invocation`** keeps `VE E` (from carried `ScInv`). -/
theorem ht_fl4PerformInvocation (b c d : Bool) (i : Fl4Invocation) :
    HTE (VS E) (VE E) (fl4PerformInvocation (Z := Unit) b c d i) := by
  cases i
  case invokeReply r g =>
    simp only [fl4PerformInvocation]
    exact hte_liftE (ht_replyArm r g)
  case invokeSchedControl iv =>
    simp only [fl4PerformInvocation]
    exact hte_bind (hte_liftE (ht_invokeSchedControlConfigureFlags iv)) (fun _ => ht_ik (by ve_auto)) fun _ h => h
  case invokeEndpoint ep badge g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact hte_ve (ike_liftE (ve_endpointArm _ _ _ _ _ _ _))
  all_goals exact hte_ve (by simp only [fl4PerformInvocation]; ve_auto)

end

end Fl4Proofs.P3.SInvR.B8v
