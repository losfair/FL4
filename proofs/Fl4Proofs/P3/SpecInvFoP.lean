/-
P3 (DESIGN.md §9), invariant line G1 (fo1): **`FT` across
`perform_invocation`** (spec side only): il2's SpecInvNtfnQLP with the owner.

* `FP N K σ := FN K σ ∧ P3 N σ` (il2's `ILP` with `FT`).
* `fo_invokeCnode` (delete / revoke: SpecInvFoD; moves / swaps / insert / badged
  sends: il2's `IL` lemmas at `K = oL σ` and the OI frames), `fo_installTcbCap`,
  `fo_installTcbFrameCap`.
* **`fo_archPostSetFlags`**: `arch_post_set_flags t` releases the FPU, or (`t`
  the current thread) restores `t`'s FPU, making `t` the owner: the current
  thread holds a thread cap (it is in `K`: the shell's IL [ct]).
  `fo_invokeTcb` (restart targets in `K` as il2, the current thread in `K`).
* `fo2_auto`: `fo_leaf` plus the owner writers `fpu_release`,
  `domain_set_start` (`invoke_fl4_tcb`'s SetFlags, `invoke_set_domain`).
* `oi_archPerform`, **`fo_fl4ArchPerform`** (MakePool: SpecInvFoU),
  **`fo_fl4PerformInvocation`**: post `ILF []`, and `ILF K` after a
  first-phase decode (il2's `il_fl4PerformInvocation` without `PerfGapIL`).
-/
import Fl4Proofs.P3.SpecInvFoU
import Fl4Proofs.P3.SpecInvNtfnQLS
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

def FP (N : Irq → ObjRef) (K : List ObjRef) (σ : State Unit) : Prop := FN K σ ∧ P3 N σ

theorem fp_fu {N : Irq → ObjRef} {σ : State Unit} (h : FP N [] σ) : FU σ := ⟨h.1, h.2.1⟩

theorem ilf_nil {K : List ObjRef} {σ : State Unit} (h : ILF K σ) : ILF [] σ := ilf_mono h fun _ h => by cases h

theorem ilfQ {K : List ObjRef} {fp : Bool} {s : State Unit} (h : ILF K s) : ILF [] s ∧ (fp = true → ILF K s) :=
  ⟨ilf_nil h, fun _ => h⟩

macro "fo2_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact fo_fpuRelease _
  | with_reducible exact fo_domainSetStart _
  | fo_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

/-! ## `invoke_cnode` -/

theorem fo_invokeCnode (N : Irq → ObjRef) (i : CnodeInvocation) (σ : State Unit) (hσ : FP N [] σ)
    (hok : CnOKN (uV σ) i) : ∀ y ∈ ((invokeCnode (Z := Unit) i).run σ).1, ILF [] y.2 := by
  have h0 : ILF [] σ := fn_ilf hσ.1
  cases i
  case revokeCall s => exact fun y hy => fn_ilf (fou_capRevoke s σ (fp_fu hσ) y hy).1
  case deleteCall s => exact fun y hy => fn_ilf (fou_capDelete s σ (fp_fu hσ) y hy).1
  case insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact fo_ik (fun _ => il_capInsert c src dest) (fun _ => oi_capInsert _ _ _) σ h0 x hx
  case moveCall c src dest =>
    obtain ⟨c0, hs, hd, hr, -, -, -⟩ := hok
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact ilf_pt (y := x) h0 (il_capMove c0 c src dest σ hs hd (refEq_tc hr)) (fun _ => oi_capMove _ _ _) hx
  case rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, r1, -, r2, -, h21, h23, -, h3⟩ := hok
    simp only [invokeCnode, withoutPreemption]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · exact ilf_pt (y := x) h0 (il_capSwapR c1 c2 c1' c2' s1 s2 σ (Ne.symm h21) h1 h2 (refEq_tc r1) (refEq_tc r2))
        (fun _ => oi_capSwap _ _ _ _) hx
    · rename_i e13
      obtain ⟨x1, hx1, hx⟩ := hx
      have hcaps := capMove_caps hx1
      have hL1 : ILF [] x1.2 :=
        ilf_pt h0 (il_capMove c2' c2 s2 s3 σ h2 (h3 e13) (refEq_tc r2)) (fun _ => oi_capMove _ _ _) hx1
      have h1' : SInvU.capAt x1.2 s1 = some c1' := by
        rw [hcaps, if_neg (Ne.symm h21), if_neg e13]; exact h1
      have h2' : SInvU.capAt x1.2 s2 = some .nullCap := by rw [hcaps, if_pos rfl]
      exact ilf_pt (y := x) hL1 (il_capMove c1' c1 s1 s2 x1.2 h1' h2' (refEq_tc r1)) (fun _ => oi_capMove _ _ _) hx
  case cancelBadgedSendsCall c =>
    intro y hy
    cases c
    case endpointCap ep b g =>
      simp only [invokeCnode, withoutPreemption] at hy
      exact fn_ilf ((ike_liftE (ik_when _ (fo_ikn (fun _ => iln_cancelBadgedSends ep b)
        (fun _ => oi_cancelBadgedSends _ _)))) σ hσ.1 y hy)
    all_goals
      simp only [invokeCnode] at hy
      exact (ike_liftE ik_fail) σ h0 y hy

/-! ## `invoke_tcb` -/

theorem fo_installTcbCap (N : Irq → ObjRef) (target : ObjRef) (slot : CslotPtr) (n : Nat)
    (o : Option (Cap × CslotPtr)) (hn : n < 6) : IKE (FP N []) (installTcbCap (Z := Unit) target slot n o) := by
  intro σ hσ y hy
  have hF : ILF [] y.2 := by
    revert y hy
    refine (?_ : HKE (FP N []) (ILF []) (installTcbCap (Z := Unit) target slot n o)) σ hσ
    cases o with
    | none => exact fun σ h y hy => ike_returnOk _ σ (fn_ilf h.1) y hy
    | some p =>
      obtain ⟨c, src⟩ := p
      simp only [installTcbCap]
      refine hke_bind (R := ILF []) (fun σ h y hy => fn_ilf (fou_capDelete _ σ (fp_fu h) y hy).1)
        (fun _ => hk_of_ik ?_) (fun _ h => h)
      unfold NonDetE.unlessE
      split
      · exact ike_returnOk _
      · exact ike_liftE (fo_ik (fun _ => il_checkCapAt _ _ _ (il_checkCapAt _ _ _ (il_capInsert _ _ _)))
          (fun _ => oi_checkCapAt _ _ _ (oi_checkCapAt _ _ _ (oi_capInsert _ _ _))))
  exact ⟨⟨⟨hF.1, nq_installTcbCap target slot n o σ hσ.1.1.2 y hy⟩, hF.2⟩,
    p3_installTcbCap target slot n o hn σ hσ.2 y hy⟩

theorem fo_installTcbFrameCap (N : Irq → ObjRef) (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (FP N []) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  intro σ hσ y hy
  have hF : ILF [] y.2 := by
    revert y hy
    refine (?_ : HKE (FP N []) (ILF []) (installTcbFrameCap (Z := Unit) target slot buffer)) σ hσ
    cases buffer with
    | none => exact fun σ h y hy => ike_returnOk _ σ (fn_ilf h.1) y hy
    | some p =>
      obtain ⟨ptr, frame⟩ := p
      simp only [installTcbFrameCap]
      exact hke_bind (R := ILF []) (fun σ h y hy => fn_ilf (fou_capDelete _ σ (fp_fu h) y hy).1)
        (fun _ => hk_of_ik (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto))) (fun _ h => h)
  exact ⟨⟨⟨hF.1, nq_installTcbFrameCap target slot buffer σ hσ.1.1.2 y hy⟩, hF.2⟩,
    un_installTcbFrameCap target slot buffer σ hσ.2 y hy⟩

/-- **`arch_post_set_flags`**: the restored thread is the current thread, which is in `K`. -/
theorem fo_archPostSetFlags (t : ObjRef) (flags : TcbFlags) {K : List ObjRef} :
    HK (fun s => ILF K s ∧ s.curThread ∈ K) (ILF K) (archPostSetFlags (Z := Unit) t flags) := by
  intro σ ⟨h, hc⟩ y hy
  unfold archPostSetFlags at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [mem_gets hz] at hy
  dsimp only at hy
  split at hy
  · exact fo_fpuRelease t σ h y hy
  · unfold NonDet.when at hy
    split at hy
    · rename_i e
      exact fo_lazyFpuRestore t σ (ilf_mono h fun u hu => by
        rcases List.mem_cons.1 hu with rfl | hu
        · rw [e]; exact hc
        · exact hu) y hy
    · obtain rfl := Set.mem_singleton_iff.1 hy; exact h

/-- **`invoke_tcb`**: restart targets and the current thread hold a thread cap (in `K`). -/
theorem fo_invokeTcb (N : Irq → ObjRef) (ti : TcbInvocation) (σ : State Unit) (K : List ObjRef)
    (hσ : FP N K σ) (hK : ∀ t ∈ tcbRT ti, t ∈ K) (hct : σ.curThread ∈ K) :
    ∀ y ∈ ((invokeTcb (Z := Unit) ti).run σ).1, ILF [] y.2 := by
  have h0 : FP N [] σ := ⟨⟨⟨il_nil_of hσ.1.1.1, hσ.1.1.2⟩, hσ.1.2⟩, hσ.2⟩
  have hF : ILF K σ := fn_ilf hσ.1
  cases ti
  case threadControlCaps target slot fh th cr vr buf =>
    intro y hy
    have key : IKE (FP N []) (invokeTcb (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) := by
      simp only [invokeTcb]
      exact ike_bind (fo_installTcbCap N _ _ 3 _ (by decide)) fun _ =>
        ike_bind (fo_installTcbCap N _ _ 4 _ (by decide)) fun _ =>
        ike_bind (fo_installTcbCap N _ _ 0 _ (by decide)) fun _ =>
        ike_bind (fo_installTcbCap N _ _ 1 _ (by decide)) fun _ =>
        ike_bind (fo_installTcbFrameCap N _ _ _) fun _ => ike_returnOk _
    exact fn_ilf (key σ h0 y hy).1
  case threadControlSched target slot fh mcp prio sc =>
    intro y hy
    have key : HKE (FP N []) (ILF []) (invokeTcb (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) := by
      simp only [invokeTcb]
      exact hke_bind (R := ILF []) (fun σ h y hy => fn_ilf (fo_installTcbCap N _ _ 3 _ (by decide) σ h y hy).1)
        (fun _ => hk_of_ik (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto))) (fun _ h => h)
    exact key σ h0 y hy
  case resume t =>
    have ht : t ∈ oL σ ++ K := List.mem_append_right _ (hK t (List.mem_singleton_self _))
    intro y hy
    refine ilf_nil (ilf_pt hF (ikp_of_ik ?_ σ) (fun _ => ?_) hy)
    · simp only [invokeTcb]; il_auto
    · simp only [invokeTcb]; oi_auto
  case copyRegisters dest src b1 b2 b3 b4 a =>
    have ht : dest ∈ oL σ ++ K := List.mem_append_right _ (hK dest (List.mem_singleton_self _))
    intro y hy
    refine ilf_nil (ilf_pt hF (ikp_of_ik ?_ σ) (fun _ => ?_) hy)
    · simp only [invokeTcb]; il_auto
    · simp only [invokeTcb]; oi_auto
  case writeRegisters dest r v a =>
    have ht : dest ∈ oL σ ++ K := List.mem_append_right _ (hK dest (List.mem_singleton_self _))
    intro y hy
    refine ilf_nil (ilf_pt hF (ikp_of_ik ?_ σ) (fun _ => ?_) hy)
    · simp only [invokeTcb]; il_auto
    · simp only [invokeTcb]; oi_auto
  case notificationControl t n =>
    intro y hy
    refine ilf_nil (ilf_pt hF (ikp_of_ik ?_ σ) (fun _ => ?_) hy)
    · cases n <;> simp only [invokeTcb] <;> il_auto
    · cases n <;> simp only [invokeTcb] <;> oi_auto
  case setFlags tcb clr st =>
    intro y hy
    refine ilf_nil ((?_ : HKE (fun s => ILF K s ∧ s.curThread ∈ K) (ILF K) _) σ ⟨hF, hct⟩ y hy)
    simp only [invokeTcb]
    refine hk_liftE ?_
    refine hk_bind (hk_of_ik (by unfold threadGet; repeat' ik_step0)) fun flags => ?_
    refine hk_bind (hk_of_ik (ik_pure _)) fun nf => ?_
    refine hk_bind (hk_of_ik ?_) fun _ => hk_bind (fo_archPostSetFlags tcb nf) fun _ => hk_of_ik (ik_pure _)
    intro s hs z hz
    exact ⟨fo_ik (fun _ => il_setFlags _ _) (fun _ => oi_setFlags _ _) s hs.1 z hz,
      by rw [ct_setFlags (cq := s.curThread) tcb nf s rfl z hz]; exact hs.2⟩
  all_goals
    intro y hy
    refine ilf_nil (ilf_pt hF (ikp_of_ik ?_ σ) (fun _ => ?_) hy)
    · simp only [invokeTcb]; il_auto
    · simp only [invokeTcb]; oi_auto

/-! ## Arch performs -/

theorem oi_archPerform {Qo : Option ObjRef} (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a) :
    OIKE Qo (archPerformInvocation (Z := Unit) i) := by
  cases i
  case invokeASIDControl a => exact absurd rfl (hm a)
  all_goals (simp only [archPerformInvocation]; oi_auto)

theorem fo_fl4ArchPerform (N : Irq → ObjRef) (K : List ObjRef) (ai : Fl4ArchInvocation) (σ : State Unit)
    (hσ : FP N K σ) (hD : DecodedFrom (uV σ) (.invokeArchObject ai)) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) ai).run σ).1, ILF K y.2 := by
  intro y hy
  have hF : ILF K σ := fn_ilf hσ.1
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) (.invokeArchObject ai) :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
  have hok : ArchOKN (uV σ) ai := hf
  cases ai with
  | spec i =>
    by_cases hm : ∃ a, i = .invokeASIDControl a
    · obtain ⟨a, rfl⟩ := hm
      cases a with
      | makePool frame slot parent base =>
        simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
        obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
        obtain ⟨z, hz, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hx]
        exact fo_makePool frame slot parent base σ hF hσ.2.1 hok z hz
    · simp only [fl4ArchPerformInvocation] at hy
      exact ft_back (il_archPerform i (fun a e => hm ⟨a, e⟩) σ (il_oL hF.1 hF.2) hok y hy)
        (oi_archPerform i (fun a e => hm ⟨a, e⟩) σ ⟨rfl, fun t ht => (hF.2 t ht).1⟩ y hy)
  | deriveSubframe iv =>
    simp only [fl4ArchPerformInvocation, archNoReturn, performDeriveSubframe] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact fo_ik (fun _ => by il_auto) (fun _ => by oi_auto) σ hF x hx
  | _ =>
    refine fo_ik (fun _ => ?_) (fun _ => ?_) σ hF y hy
    · simp only [fl4ArchPerformInvocation, archNoReturn]; il_auto
    · simp only [fl4ArchPerformInvocation, archNoReturn]; oi_auto

/-! ## `perform_invocation` -/

set_option maxHeartbeats 4000000 in
/-- **`perform_invocation` keeps `FT`** (with IfLiveT), and `ILF K` after a first-phase decode. -/
theorem fo_fl4PerformInvocation (N : Irq → ObjRef) (bl call don fp : Bool) (i : Fl4Invocation)
    (σ : State Unit) (K : List ObjRef) (hσ : FP N K σ) (hct : σ.curThread ∈ K)
    (hT : ∀ t ∈ invRT i, HasTC σ t) (hF : fp = true → NoDelI i) (hok : InvOKN (uV σ) i)
    (hD : DecodedFrom (uV σ) i) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don i).run σ).1, ILF [] y.2 ∧ (fp = true → ILF K y.2) := by
  intro y hy
  have h0 : ILF K σ := fn_ilf hσ.1
  cases i
  case invokeUntyped ui =>
    obtain ⟨fp', label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
    have hf : GapOKN (uV σ) (.invokeUntyped ui) :=
      okv_fl4DecodeG fp' label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact ilfQ (fo_invokeUntyped ui σ h0 hσ.2.1 hf z hz)
  case invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    exact ilfQ (fo_fl4ArchPerform N K ai σ hσ hD y hy)
  case invokeCNode ci =>
    refine ⟨?_, fun h => (hF h).elim⟩
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact fo_invokeCnode N ci σ ⟨⟨⟨il_nil_of hσ.1.1.1, hσ.1.1.2⟩, hσ.1.2⟩, hσ.2⟩ hok z hz
  case invokeTCB ti =>
    refine ⟨?_, fun h => (hF h).elim⟩
    simp only [fl4PerformInvocation] at hy
    exact fo_invokeTcb N ti σ (tcbRT ti ++ K) ⟨⟨⟨il_app hσ.1.1.1 hT, hσ.1.1.2⟩, hσ.1.2⟩, hσ.2⟩
      (fun t ht => List.mem_append_left _ ht) (List.mem_append_right _ hct) y hy
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    obtain ⟨z1, h1, hz⟩ := hx
    rw [mem_gets h1] at hz
    obtain ⟨z2, h2, hz⟩ := hz
    have hb : ILF K z2.2 := ft_back
      (il_sendIpc bl call bd g gr don σ.curThread ep (Kq := oL σ ++ K) (List.mem_append_right _ hct) σ
        (il_oL h0.1 h0.2) z2 h2)
      (oi_sendIpc _ _ _ _ _ _ _ _ σ ⟨rfl, fun t ht => (h0.2 t ht).1⟩ z2 h2)
    rw [Set.mem_singleton_iff.1 hz]; exact ilfQ hb
  case invokeNotification ep bd =>
    refine ilfQ ((?_ : HKE (FN K) (ILF K) _) σ hσ.1 y hy)
    simp only [fl4PerformInvocation, withoutPreemption]
    exact hke_bind (R := ILF K) (hk_liftE (fun s h z hz =>
        fn_ilf (fo_ikn (fun _ => iln_sendSignal ep bd) (fun _ => oi_sendSignal _ _) s h z hz)))
      (fun _ => hk_of_ik (ike_returnOk _)) (fun _ h => h)
  case invokeReply rp gr =>
    refine ilfQ ((?_ : IKE (ILF K) _) σ h0 y hy)
    simp only [fl4PerformInvocation]
    exact ike_liftE (ik_bind (ik_gets _) fun _ =>
      ik_bind (fo_ik (fun _ => il_doReplyTransfer _ _ _) (fun _ => oi_doReplyTransfer _ _ _)) fun _ => ik_pure _)
  case invokeIRQHandler ih =>
    refine ilfQ (fn_ilf ((?_ : IKE (FN K) _) σ hσ.1 y hy))
    simp only [fl4PerformInvocation]
    exact ike_bind (ike_liftE (fo_ikn (fun _ => iln_invokeIrqHandler ih) (fun _ => oi_invokeIrqHandler _)))
      fun _ => ike_returnOk _
  all_goals
    refine ilfQ ((?_ : IKE (ILF K) _) σ h0 y hy)
    simp only [fl4PerformInvocation, withoutPreemption]
    fo2_auto

end

end Fl4Proofs.P3.SInvF
