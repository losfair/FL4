/-
P3 (DESIGN.md §9), invariant line G1 (sl2): **ScLive across `send_ipc` and the
fault / timeout senders** (sl1 handoff 1, first part; spec side only).

The facts read at intermediate states are carried beside `SL I K`:

* **`SBP I K d t`**: `SL I K`, sb1's `ScInv` (its `ScBackS` makes an SC read
  bound to a thread live) and, when `d`, the pin `PinB t` (the thread `t` is
  bound: vi2's `CtSc` at the current thread, kept by sb1's binding frame
  `SBK`, whose relation `BR` keeps every TCB's `tcbSchedContext`);
  **`SAP I K d t`** adds il2's `IL []` (IfLiveT: a live thread holds a thread
  cap). Prefix steps keep them by the three families (`sbp_ik`, `sap_ik`).
* `send_ipc`: the receiver read BlockedOnReceive is live, so (IfLiveT at that
  state) named: it joins `K`; `reply_push` with sl1's `sl_replyPush`; the
  direct (non-call) donation reads the sender's SC, bound by the pin (lead
  decision: vi2's `CtSc` [J] for the pinned syscalls, the sender being the
  current thread), and bound back to the sender (`ScBackS`), hence live.
* `send_fault_ipc` donates when its `canDonate` argument says so (pinned);
  `handle_fault` reads the faulting thread's SC first and donates only when it
  is bound (vi2's argument): the pin holds at that read; `handle_timeout` never
  donates.
-/
import Fl4Proofs.P3.SpecInvSlW
import Fl4Proofs.P3.SpecInvSlN6
import Fl4Proofs.P3.SpecInvNtfnQLW
import Fl4Proofs.P3.SpecInvSbG6
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Pre/post combinators -/

section C
variable {P Q R : State Unit → Prop}

theorem shk_bind {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : HK P Q m) (hk : ∀ a, HK Q R (k a)) : HK P R (m >>= k) :=
  fun σ h x ⟨y, hy, hx⟩ => hk y.1 y.2 (hm σ h y hy) x hx

theorem shk_ikbind {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : IK P m) (hk : ∀ a, HK P R (k a)) : HK P R (m >>= k) :=
  fun σ h x ⟨y, hy, hx⟩ => hk y.1 y.2 (hm σ h y hy) x hx

theorem shk_ik {α : Type} {m : NonDet (State Unit) α} (h : IK Q m) (hp : ∀ s, P s → Q s) : HK P Q m :=
  fun σ hσ x hx => h σ (hp σ hσ) x hx

theorem shk_post {α : Type} {m : NonDet (State Unit) α} (h : HK P Q m) (hq : ∀ s, Q s → R s) : HK P R m :=
  fun σ hσ x hx => hq _ (h σ hσ x hx)

theorem shk_pre {α : Type} {m : NonDet (State Unit) α} (h : HK Q R m) (hp : ∀ s, P s → Q s) : HK P R m :=
  fun σ hσ x hx => h σ (hp σ hσ) x hx

theorem shk_pure_bind {α β : Type} {a : α} {k : α → NonDet (State Unit) β} (h : HK P R (k a)) :
    HK P R ((pure a : NonDet (State Unit) α) >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hσ x hx

theorem shk_fail_bind {α β : Type} {k : α → NonDet (State Unit) β} :
    HK P R ((NonDet.fail : NonDet (State Unit) α) >>= k) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

theorem shk_fail {α : Type} : HK P R (NonDet.fail : NonDet (State Unit) α) :=
  fun _ _ _ hy => hy.elim

theorem shk_pure {α : Type} (a : α) (hp : ∀ s, P s → R s) : HK P R (pure a : NonDet (State Unit) α) := by
  intro σ hσ x hx
  rw [Set.mem_singleton_iff.1 hx]; exact hp σ hσ

end C

/-! ## The carried facts -/

/-- **The pin**: the thread `t` is bound (vi2's `CtSc` at the current thread). -/
def PinB (t : ObjRef) (σ : State Unit) : Prop := ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ none

theorem pinB_br {t : ObjRef} {σ σ' : State Unit} (h : PinB t σ) (hb : SInvB.BR σ.kheap σ'.kheap) :
    PinB t σ' := by
  intro x' hx'
  obtain ⟨x, hx⟩ := hb.tcb' t x' hx'
  obtain ⟨x2, hx2, e⟩ := hb.tcb t x hx
  rw [hx'] at hx2; cases hx2
  rw [e]; exact h x hx

/-- `SL I K`, `ScInv` and the pin when `d`. -/
def SBP (I : ObjRef × ObjRef) (K : List ObjRef) (d : Prop) (t : ObjRef) (σ : State Unit) : Prop :=
  SL I K σ ∧ SInvB.ScInv σ ∧ (d → PinB t σ)

/-- … with il2's `IL L` (IfLiveT and the threads of `L` named) and `NtfnScB`. -/
def SAP (I : ObjRef × ObjRef) (K L : List ObjRef) (d : Prop) (t : ObjRef) (σ : State Unit) : Prop :=
  SBP I K d t σ ∧ IL L σ ∧ NtfnScB σ

section S
variable {I : ObjRef × ObjRef} {K L : List ObjRef} {d : Prop} {t : ObjRef}

theorem sbp_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I K m) (h3 : ∀ h0, SInvB.SBK h0 m) :
    IK (SBP I K d t) m := by
  intro σ ⟨hs, hi, hp⟩ x hx
  have hb := SInvB.br_mem_of_sbk h3 hx
  exact ⟨h1 σ hs x hx, SInvB.scInv_of_br hi hb, fun hd => pinB_br (hp hd) hb⟩

theorem sap_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I K m) (h2 : ILK L m)
    (h3 : ∀ h0, SInvB.SBK h0 m) (h4 : NBK m) : IK (SAP I K L d t) m :=
  fun σ h x hx => ⟨sbp_ik h1 h3 σ h.1 x hx, h2 σ h.2.1 x hx, h4 σ h.2.2 x hx⟩

theorem sbp_sl {α : Type} {m : NonDet (State Unit) α} (h : SLK I K m) : HK (SBP I K d t) (SL I K) m :=
  fun σ h' x hx => h σ h'.1 x hx

theorem sap_sl {α : Type} {m : NonDet (State Unit) α} (h : SLK I K m) : HK (SAP I K L d t) (SL I K) m :=
  fun σ h' x hx => h σ h'.1.1 x hx

/-- A thread read live joins `K` (IfLiveT at that state). -/
theorem sbp_of_live {σ : State Unit} (h : SAP I K L d t σ) {u : ObjRef} {x : Tcb}
    (hx : σ.kheap u = some (.tcb x)) (hl : liveSt x.tcbState) : SBP I (u :: K) d t σ :=
  ⟨sl_cons h.1.1 (Or.inl (hasN_of_tc (h.2.1.1 u x hx hl))), h.1.2.1, h.1.2.2⟩

/-- … and stays in `IL`'s list. -/
theorem sap_of_live {σ : State Unit} (h : SAP I K L d t σ) {u : ObjRef} {x : Tcb}
    (hx : σ.kheap u = some (.tcb x)) (hl : liveSt x.tcbState) : SAP I (u :: K) (u :: L) d t σ :=
  ⟨sbp_of_live h hx hl, il_consR h.2.1 hx hl, h.2.2⟩

theorem sap_tail {σ : State Unit} {u : ObjRef} (h : SAP I (u :: K) L d t σ) : SAP I K L d t σ :=
  ⟨⟨sl_tail h.1.1, h.1.2.1, h.1.2.2⟩, h.2⟩

theorem sap_mono {σ : State Unit} {L' : List ObjRef} (h : SAP I K L d t σ) (hL : ∀ u ∈ L', u ∈ L) :
    SAP I K L' d t σ :=
  ⟨h.1, il_mono h.2.1 hL, h.2.2⟩

/-- One prefix step kept by the four families. -/
macro "sap_step" : tactic => `(tactic| refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun _ => ?_)

theorem sbp_tail {σ : State Unit} {u : ObjRef} (h : SBP I (u :: K) d t σ) : SBP I K d t σ :=
  ⟨sl_tail h.1, h.2.1, h.2.2⟩

end S

/-! ## `send_ipc` -/

section Send
variable {I : ObjRef × ObjRef} {K L : List ObjRef} {d : Prop} {t : ObjRef}

/-- The receiver arm's tail. -/
theorem sl_sendIpc_tail (dest : ObjRef) :
    SLK I K (do
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  sl_auto

/-- **The direct donation**: the pinned sender's SC is bound back to it, so live. -/
theorem sl_donate (thread dest : ObjRef) (hd : dest ∈ K) :
    HK (SBP I K True thread) (SL I K) (do
      let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
      schedContextDonate (the threadSc) dest) := by
  intro σ ⟨hs, hi, hp⟩ x ⟨y, hy, hx⟩
  obtain ⟨e1, xa, hxa, ha⟩ := SInvB.mem_getTcbSc hy
  obtain ⟨a, s1⟩ := y
  simp only at e1 ha; subst s1
  cases a with
  | none => exact absurd ha (hp trivial xa hxa)
  | some c =>
    obtain ⟨yc, k, hyc, hyt, -⟩ := hi.back thread xa c hxa ha
    have h1 : SL I (c :: K) σ := sl_consL hs hyc (Or.inl (by rw [hyt]; simp))
    exact sl_tail (sl_schedContextDonate c dest (List.mem_cons.2 (Or.inl rfl))
      (List.mem_cons_of_mem _ hd) σ h1 x hx)

/-- The receiver arm after the receiver's state read (`dest ∈ K`). -/
theorem sl_sendIpc_rcv (call : Bool) (bd : Badge) (g gr cd : Bool) (thread ep dest : ObjRef)
    (reply : Option ObjRef) (hd : dest ∈ K) :
    HK (SBP I K (cd = true ∧ call = false) thread) (SL I K) (do
      doIpcTransfer (Z := Unit) thread (some ep) bd g dest
      NonDet.maybeM (replyUnlinkTcb dest) reply
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext dest
      let fault ← threadGet Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (g ∨ gr) ∧ reply ≠ none then
          replyPush thread dest (the reply) cd
        else
          setThreadState thread .inactive
      else NonDet.when (cd ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef Tcb.tcbSchedContext thread
        schedContextDonate (the threadSc) dest
      setThreadState dest .running
      let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  refine shk_ikbind (sbp_ik (sl_doIpcTransfer _ _ _ _ _) fun _ => SInvB.sb_doIpcTransfer _ _ _ _ _) fun _ => ?_
  refine shk_ikbind (sbp_ik (by sl_auto) fun _ => by sb_auto) fun _ => ?_
  refine shk_ikbind (sbp_ik (sl_getTcbObjRef _ _) fun _ => SInvB.sb_getTcbObjRef _ _) fun scOpt => ?_
  refine shk_ikbind (sbp_ik (sl_threadGet _ _) fun _ => SInvB.sb_threadGet _ _) fun fault => ?_
  have htl : IK (SL I K) (do
        setThreadState (Z := Unit) dest .running
        let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
        ifSporadicCurScTestRefillUnblockCheck destSc
        possibleSwitchTo dest) := sl_sendIpc_tail dest
  by_cases hc : (call = true ∨ fault ≠ none)
  · rw [if_pos hc]
    by_cases hg : ((g = true ∨ gr = true) ∧ reply ≠ none)
    · rw [if_pos hg]
      exact shk_bind (shk_pre (sl_replyPush thread dest _ cd hd) fun s h => ⟨h.1, h.2.1.back⟩) fun _ => htl
    · rw [if_neg hg]
      exact shk_bind (sbp_sl (sl_setThreadState _ _)) fun _ => htl
  · rw [if_neg hc]
    unfold NonDet.when
    by_cases hw : (cd = true ∧ scOpt = none)
    · rw [if_pos hw]
      have hcall : call = false := by
        cases call
        · rfl
        · exact absurd (Or.inl rfl) hc
      exact shk_bind (shk_pre (sl_donate thread dest hd) fun s h => ⟨h.1, h.2.1, fun _ => h.2.2 ⟨hw.1, hcall⟩⟩)
        fun _ => htl
    · rw [if_neg hw]
      exact shk_pure_bind (shk_ik htl fun s h => h.1)

set_option maxHeartbeats 4000000 in
/-- **`send_ipc`**: pre `SAP` with the sender pinned when the send may donate. -/
theorem sl_sendIpc (bl call : Bool) (bd : Badge) (g gr cd : Bool) (thread ep : ObjRef) :
    HK (SAP I K L (cd = true ∧ call = false) thread) (SL I K) (sendIpc (Z := Unit) bl call bd g gr cd thread ep) := by
  unfold sendIpc
  refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun e => ?_
  rcases e with _ | q | (_ | ⟨dest, q⟩) <;> cases bl <;> dsimp only
  · exact shk_pure _ fun s h => h.1.1
  · exact sap_sl (sl_sendIpcBlocked _ _ _ _ _ _)
  · exact shk_pure _ fun s h => h.1.1
  · exact sap_sl (sl_sendIpcBlocked _ _ _ _ _ _)
  · exact shk_fail
  · exact shk_fail
  all_goals
    refine shk_ikbind (sap_ik (sl_tcbEpDequeue _ _) (il_tcbEpDequeue _ _) (fun _ => SInvB.sb_tcbEpDequeue _ _)
      (nb_tcbEpDequeue _ _)) fun _ => ?_
    intro σ hσ x ⟨y, hy, hx⟩
    unfold getThreadState at hy
    obtain ⟨xd, hxd, rfl⟩ := mem_threadGet hy
    dsimp only at hx
    cases hs : xd.tcbState with
    | blockedOnReceive e0 reply d0 =>
      rw [hs] at hx
      have h1 : SBP I (dest :: K) (cd = true ∧ call = false) thread σ :=
        sbp_of_live hσ hxd (liveSt_eq hs True.intro)
      obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hz] at hx
      exact sl_tail (sl_sendIpc_rcv call bd g gr cd thread ep dest reply (List.mem_cons.2 (Or.inl rfl)) σ h1 x hx)
    | _ => rw [hs] at hx; obtain ⟨z, hz, -⟩ := hx; exact hz.elim

/-! ## Faults and timeouts -/

/-- `send_fault_ipc` (never a call): pinned when it may donate. -/
theorem sl_sendFaultIpc (tptr : ObjRef) (hc : Cap) (f : Fault) (cd : Bool) :
    HK (SAP I K L (cd = true) tptr) (SL I K) (sendFaultIpc (Z := Unit) tptr hc f cd) := by
  unfold sendFaultIpc
  split
  · sap_step
    refine shk_bind (shk_pre (sl_sendIpc (L := L) true false _ _ _ cd tptr _) fun s h =>
      ⟨⟨h.1.1, h.1.2.1, fun hd => h.1.2.2 hd.1⟩, h.2⟩) fun _ => ?_
    exact shk_pure _ fun s h => h
  · exact shk_pure _ fun s h => h.1.1
  · exact shk_fail

theorem sl_handleTimeout (tptr : ObjRef) (ex : Fault) :
    HK (SAP I K L d t) (SL I K) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  sap_step
  sap_step
  refine shk_pure_bind ?_
  sap_step
  refine shk_bind (shk_pre (sl_sendFaultIpc (I := I) (K := K) (L := L) tptr _ ex false) fun s h =>
    ⟨⟨h.1.1, h.1.2.1, fun hd => by cases hd⟩, h.2⟩) fun _ => ?_
  exact shk_pure _ fun s h => h

/-- **`handle_fault`**: it donates only when the faulting thread is bound, read
at that state (the pin holds there). -/
theorem sl_handleFault (thread : ObjRef) (ex : Fault) :
    HK (SAP I K L d t) (SL I K) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault
  refine shk_pure_bind ?_
  refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun hc => ?_
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hz
  obtain ⟨w, hw, hy⟩ := hy
  (try dsimp only at hw)
  have hpin : SAP I K L (decide (x.tcbSchedContext ≠ none) = true) thread σ :=
    ⟨⟨hσ.1.1, hσ.1.2.1, fun hd x' hx' => by
      rw [hx] at hx'; cases hx'; exact of_decide_eq_true hd⟩, hσ.2⟩
  have hw' : SL I K w.2 := sl_sendFaultIpc thread hc ex _ σ hpin w hw
  obtain ⟨u, hu, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  unfold NonDet.unless at hu
  split at hu
  · rw [Set.mem_singleton_iff.1 hu]; exact hw'
  · unfold handleNoFault at hu
    exact sl_setThreadState _ _ w.2 hw' u hu

end Send

end

end Fl4Proofs.P3.SInvL
