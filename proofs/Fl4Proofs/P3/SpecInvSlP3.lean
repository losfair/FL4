/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive ∧ NtfnScB across
`perform_invocation`** given the untyped / arch gap (sl2 handoff 3; spec side only).

* The perform state carries `SPF I K L d t N` (sl2's `SAP` — `SL I K`, ScInv, the
  pin when `d`, IfLiveT with `L`, NtfnScB — with nq1's `NQ []`, ut7's `P3 N` /
  `NodeIs N`, the fixed idle SC, `ScKind` and `IdleScOutV`), and the decode's
  facts: ut7's `InvOKN`, `InvNF`, vi3's `TgOK`, `NBind`, `TcbFh`, il2's `NoDelI`
  for a first-phase decode.
* **`SlGap`** (an intermediate definition, the analogue of il2's `PerfGapIL`):
  the untyped and arch performs keep `SL I K ∧ NtfnScB`; to be discharged
  (SpecInvSlU: detype of a childless untyped's region, fresh default objects,
  `create_cap` into null slots; the arch cap rewrites).
* **`sl_fl4PerformInvocation`**: one case per invocation kind.
-/
import Fl4Proofs.P3.SpecInvSlP2
import Fl4Proofs.P3.SpecInvSlQ
import Fl4Proofs.P3.SpecInvSlR
import Fl4Proofs.P3.SpecInvSlT
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-- The perform state's carried facts. -/
def SPF (I : ObjRef × ObjRef) (K L : List ObjRef) (d : Prop) (t : ObjRef) (N : Irq → ObjRef) (σ : State Unit) :
    Prop :=
  SAP I K L d t σ ∧ NQ [] σ ∧ P3 N σ ∧ NodeIs N σ ∧ IdleScIs I.2 σ ∧ ScKind σ ∧ IdleScOutV σ

/-- The performs left to `SlGap`. -/
def SlGapInv : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeArchObject _ => True
  | _ => False

/-- **The untyped / arch gap** (see the module docstring). -/
def SlGap : Prop :=
  ∀ (I : ObjRef × ObjRef) (N : Irq → ObjRef) (K L : List ObjRef) (d : Prop) (t : ObjRef) (blk call don : Bool)
    (inv : Fl4Invocation) (σ : State Unit), SlGapInv inv → SPF I K L d t N σ → IrqOutV (fun _ => I.1) (uV σ) →
      DecodedFrom (uV σ) inv →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, SL I K y.2 ∧ NtfnScB y.2

/-! ## `invoke_sched_context` keeps NtfnScB -/

theorem nb_invokeSchedContext (iv : SchedContextInvocation) (σ : State Unit) (hB : NBindS σ iv) (hσ : NtfnScB σ) :
    ∀ y ∈ (invokeSchedContext (Z := Unit) iv σ).1, NtfnScB y.2 := by
  cases iv
  case invokeSchedContextBind p cap =>
    simp only [invokeSchedContext]
    cases cap
    case notificationCap n b r =>
      intro y ⟨z, hz, hy⟩
      have h1 := nb_bindNtfn p n σ hσ hB z hz
      rw [Set.mem_singleton_iff.1 hy]; exact h1
    case threadCap t => exact (ik_bind (nb_schedContextBindTcb _ _) fun _ => ik_pure _) σ hσ
    all_goals exact ik_fail σ hσ
  all_goals exact (by simp only [invokeSchedContext]; nb_auto : NBK _) σ hσ

/-! ## `perform_invocation` -/

set_option maxHeartbeats 8000000 in
/-- **`perform_invocation` keeps `SL I [] ∧ NtfnScB`, and `SL I K` after a
first-phase decode** (given `SlGap`). -/
theorem sl_fl4PerformInvocation (hG : SlGap) (I : ObjRef × ObjRef) (N : Irq → ObjRef) (bl call don fp : Bool)
    (i : Fl4Invocation) (σ : State Unit) (K L : List ObjRef)
    (hσ : SPF I K L (don = true ∧ call = false) σ.curThread N σ) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hF : fp = true → NoDelI i) (hok : InvOKN (uV σ) i) (hnf : InvNF (uV σ) i) (hT : SInvI.TgOK (uV σ) i)
    (hB : NBind σ i) (hFh : ∀ ti, i = .invokeTCB ti → TcbFh σ ti) (hD : DecodedFrom (uV σ) i) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don i).run σ).1,
      (SL I [] y.2 ∧ NtfnScB y.2) ∧ (fp = true → SL I K y.2) := by
  have hS : SL I K σ := hσ.1.1.1
  have hNB : NtfnScB σ := hσ.1.2.2
  have hS0 : SL I [] σ := sl_mono hS fun _ h => by cases h
  have hDX : DX I σ := ⟨hS0, hσ.1.1.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2.1⟩
  have hSDP : SDP I N σ := ⟨⟨⟨il_nil_of hσ.1.2.1, hσ.2.1⟩, hσ.2.2.1⟩, hDX⟩
  have fin : ∀ {β : Type} (y : β × State Unit), SL I K y.2 → NtfnScB y.2 →
      (SL I [] y.2 ∧ NtfnScB y.2) ∧ (fp = true → SL I K y.2) :=
    fun y h1 h2 => ⟨⟨sl_mono h1 (fun _ h => by cases h), h2⟩, fun _ => h1⟩
  intro y hy
  cases i
  case invokeUntyped ui =>
    obtain ⟨h1, h2⟩ := hG I N K L _ σ.curThread bl call don (.invokeUntyped ui) σ trivial hσ hI1 hD y hy
    exact fin y h1 h2
  case invokeArchObject ai =>
    obtain ⟨h1, h2⟩ := hG I N K L _ σ.curThread bl call don (.invokeArchObject ai) σ trivial hσ hI1 hD y hy
    exact fin y h1 h2
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    obtain ⟨z1, h1, hz⟩ := hx
    rw [mem_gets h1] at hz
    obtain ⟨z2, h2, hz⟩ := hz
    have hb := sl_sendIpc bl call bd g gr don σ.curThread ep σ hσ.1 z2 h2
    have hn := nb_sendIpc bl call bd g gr don σ.curThread ep σ hNB z2 h2
    rw [Set.mem_singleton_iff.1 hz]; exact fin _ hb hn
  case invokeNotification ep bd =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hz
    rw [e]
    have h := sli_sendSignal (I := I) (K := K) (L := L) ep bd σ ⟨⟨hS, hNB⟩, ⟨hσ.1.2.1, hσ.2.1⟩⟩ x hx
    exact fin _ h.1.1 h.1.2
  case invokeReply rp gr =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    obtain ⟨z1, h1, hz⟩ := hx
    rw [mem_gets h1] at hz
    obtain ⟨z2, h2, hz⟩ := hz
    have hb := sl_doReplyTransfer (I := I) (K := K) (L := L) (t := σ.curThread) σ.curThread rp gr σ
      ⟨⟨hS, hσ.1.1.2.1, fun h => h.elim⟩, hσ.1.2⟩ z2 h2
    have hn := nb_doReplyTransfer σ.curThread rp gr σ hNB z2 h2
    rw [Set.mem_singleton_iff.1 hz]; exact fin _ hb hn
  case invokeTCB ti =>
    refine ⟨⟨?_, ?_⟩, fun h => (hF h).elim⟩
    · simp only [fl4PerformInvocation] at hy
      exact sl_invokeTcb ti σ hSDP hT (hFh ti rfl) y hy
    · simp only [fl4PerformInvocation] at hy
      exact nb_invokeTcb ti σ hNB y hy
  case invokeCNode ci =>
    refine ⟨⟨?_, ?_⟩, fun h => (hF h).elim⟩
    · simp only [fl4PerformInvocation] at hy
      obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
      rw [e]
      exact sl_invokeCnode I ci σ ⟨⟨⟨il_nil_of hσ.1.2.1, hσ.2.1⟩, hσ.2.2.1.1⟩, hDX⟩ hok hnf z hz
    · simp only [fl4PerformInvocation] at hy
      obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
      rw [e]
      exact nb_invokeCnode ci σ hNB z hz
  case invokeIRQHandler ih =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hz
    rw [e]
    exact fin _ (sl_invokeIrqHandler ih σ ⟨hS, il_nil_of hσ.1.2.1⟩ x hx) (nb_invokeIrqHandler ih σ hNB x hx)
  case invokeSchedContext iv =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact fin _ (sl_invokeSchedContext iv σ hT hS x hx) (nb_invokeSchedContext iv σ hB hNB x hx)
  all_goals
    refine fin y ((?_ : SLKE I K _) σ hS y hy) ((?_ : NBKE _) σ hNB y hy)
    all_goals simp only [fl4PerformInvocation, withoutPreemption]
    · sl_auto
    · nb_auto

end

end Fl4Proofs.P3.SInvL
