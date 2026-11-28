/-
P3 (p3J gen 41): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at Suspend (12), for
both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–5, 8–11, 13, 17, 22, 24, or SetEPTRoot}.

* `MR` without the IrqFix copies: **`mF_mrT`**, **`TopPostDMXP.mrGT`**, **`TopPostRMX.mrGT`**, **`XCapP.mrGT`** —
  XTopJointKEntry39's `mF_mr` / `TopPostDMXP.mrG` / `TopPostRMX.mrG` / `XCapP.mrG` (proof text unchanged) from
  `MachPlatT` instead of `MachPlat` (they read only the `frame` field, which both records have). Gen 40's leaves used
  IrqFixXport's transported copy of `XCapP.mrG`; new files reference none of the transported namespaces.
* **`JAtZ.suspendProjW`**: `suspend` of a thread of `Z.T` at a `JAtZ` state writes only `ProjW` (P3JSusFt's
  `sched.suspend.kwN0` through P3JMcKwN's `kwN_projW`).
* **`tcb_suspendJSt`**: XTopJointTcb's `tcb_suspendJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts: the restart by `stsProjW`, `suspend` by `suspendProjW` beside
  XTopJointSuspend's `JAtZ.suspendJ`).
* **`JAtZ.capNotIdle`**: a thread cap read at a slot of a state with `SpecGlob` does not name the idle thread (l4v
  `valid_global_refs`; the spec's `SpecGlob.idle`, as XTopJointDelR's `jFinAt_thread`). `SpecGlob σb` at the dispatch
  state is P3JCapDom's `dispEnteredSg`, so the non-stable chain's `hpI` (StallNarrowTcb) is no premise here.
* **`decThSusSt`** (any flags): the dispatch leaf (as P3JThPrio's `decThPrioSt`; never preempted).
* `ThHard10 l`: `ThHard9 l ∧ l ≠ TCBSuspend`. `IsRestCap18`. `restCap17_of18`, `restCap18_of`.
  **`midDecRest17_of_sus`** / **`invDecRest17_of_sus`**, `midDecStWL_of_17` / `invDecStWL_of_17`.
* **`DispStabFootLzk` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap18`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzj_of_Lzk`** (under the tops' platform facts), **`dispStabFootLzk_of_Lzj`**; top
  **`kernel_entry_runMcWKR_sysLzk`** (globals verbatim as `_sysLzj`).

Premise honesty: `DispStabFootLzk`'s decode fields are `DispStabFootLzj`'s at the smaller antecedent
(`IsRestCap18 → IsRestCap17`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzk` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSusFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## `MR` from `MachPlatT` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

theorem mF_mrT (hM : MachPlat arI MR) {a : A} {ms ms' : Fl4Spec.MachineState} (hR : MR a ms)
    (h : MachF.mF ms' = MachF.mF ms) : MR a ms' := by
  simp only [MachF.mF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2

theorem TopPostDMXP.mrGT (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop}
    {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : TopPostDMXP (L := L) X XP σ blk call don m s res)
    (hR : MR res.2.2 (if res.1 = .Ok () then f σ.machineState else σ.machineState))
    (hq : PerfF f σ blk call don m) :
    TopPostDMXP (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) XP σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    dsimp only at h4 ⊢
    rw [h1] at hR
    rw [if_neg (by simp)] at hR
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢; exact ⟨h4, hR⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢
      obtain ⟨th', G', hc, -⟩ := h3
      have hc' : res.1 = .Ok () ∧ y.1 = .ok [] := hc.resolve_right fun ⟨e, _⟩ => hp e
      rw [if_pos hc'.1] at hR
      exact ⟨h4, mF_mrT hM hR (hq inv h1 σ1 h2 y hy ⟨_, hc'.2⟩)⟩

theorem TopPostRMX.mrGT (hM : MachPlat arI MR) {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : TopPostRMX (L := L) X σ blk call don m ct s res)
    (hR : MR res.2.2 (if res.1 = .Ok () then f σ.machineState else σ.machineState))
    (hq : PerfF f σ blk call don m) :
    TopPostRMX (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · rw [h1, if_neg (by simp)] at hR
    exact Or.inl ⟨e, h1, h2, h3, h4, hR⟩
  · rw [if_pos h1] at hR
    refine Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, mF_mrT hM hR ?_⟩
    have e1 := congrArg Prod.fst (MachT.mtk_specTailG call ct.bv rr σy z hz)
    simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e1
    have e2 := hq inv h3 σ1 h4 _ h5 ⟨rr, rfl⟩
    rw [← e2]
    simp only [MachF.mF, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1]

/-- (p3J gen 41) **`XCapP` with `MR`, from `MachPlatT`** (XTopJointKEntry39's `XCapP.mrG`; module docstring). -/
theorem XCapP.mrGT (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      MR r.2.2 (if r.1 = .Ok () then f σ.machineState else σ.machineState) ⦄)
    (hq : PerfF f σ blk call don (specDec fp slbl args ci sl c excaps buffer)) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrGT hM h2 hq)
  · exact Or.inr (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrGT hM h2 hq)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 41) **`suspend` of a thread of `Z.T` writes only `ProjW`** (module docstring). -/
theorem JAtZ.suspendProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) :
    sched.suspend st arI s a t ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  refine WP.spec_mono (P1.sched.suspend.kwN0 (ar := arI) s a t J.blk (J.zH.1 t ht)) ?_
  rintro ⟨s', a'⟩ F
  simp only [WP.uncurry'_pair] at F ⊢
  exact (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

/-- (p3J gen 41) **A thread cap read at a slot does not name the idle thread** (`SpecGlob.idle`; module
docstring). -/
theorem JAtZ.capNotIdle {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hsg : SpecGlob σ) {sl : Fl4Spec.CslotPtr} {p : U64}
    (hget : Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap (.Thread p), σ)}, False)) : p ≠ L.idleW s := by
  intro e
  have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hget)
  apply hsg.idle sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap])
  rw [J.idleThread_bv, ← e]; simp [absCap, Fl4Spec.objRefs]

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **Suspend at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_suspendJ`; module
docstring). -/
theorem tcb_suspendJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    [VxE Z] (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (hpI : p ≠ L.idleW s) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSuspend)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBSuspend p c blk call don slbl args
      ci sl excaps buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.suspend p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  have hid0 := J.ne_idle hpI
  have hctT : ct ∈ Z.T := J.thT ct (J.xtop.curTcb (J.curEq hct).1).1
  obtain ⟨s1, σ1, x, hrc1, hst, -, -, -, hns, hid1, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  unfold TcbOKX
  rw [decode_suspend_eq arI s ar p c hstall, hrc1]
  simp only [bind_ok]
  refine WP.spec_bind (WP.spec_and (J1.suspendJ (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
    (jCancel_reply arI) hpT (fun u h => (hns u h).elim) (by rw [hid1]; exact hid0)) (J1.suspendProjW hpT)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨-, σ', hsus, V, Ac', Lst', D', J2⟩, W2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.suspend p.bv))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hsus]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac', Lst', D', J2⟩, W1.projW_trans W2⟩⟩

end

/-- (p3J gen 41) The Thread labels left after Suspend. -/
def ThHard10 (l : U64) : Prop := ThHard9 l ∧ l ≠ fl4_abi.label.TCBSuspend

/-- (p3J gen 41) The caps left after the Suspend leaf, with the message label. -/
def IsRestCap18 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard10 l
  | _, _ => False

theorem restCap17_of18 {cp : capability.Cap} {l : U64} (h : IsRestCap18 cp l) : IsRestCap17 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap18_of {cp : capability.Cap} {l : U64} (h : IsRestCap17 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSuspend) : IsRestCap18 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem sus_nonIns : TcbNonIns fl4_abi.label.TCBSuspend := by
  unfold TcbNonIns fl4_abi.label.TCBSuspend fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The Thread cap's decode at a dispatch state at Suspend, any flags** (module docstring). -/
theorem decThSusSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsgb : SpecGlob σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    (hget : Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap (.Thread p), σb)}, False))
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hl : info.label = fl4_abi.label.TCBSuspend) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  have hpI : p ≠ L.idleW s' := J.capNotIdle hsgb hget
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSuspend
  have hl5 : fl4_abi.label.TCBSuspend.val ≠ 5 ∧ fl4_abi.label.TCBSuspend.val ≠ 8 ∧
      fl4_abi.label.TCBSuspend.val ≠ 9 ∧ fl4_abi.label.TCBSuspend.val ≠ 10 ∧
      fl4_abi.label.TCBSuspend.val ≠ 11 := by simp [fl4_abi.label.TCBSuspend]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine XCapP.mrGT (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD sus_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_suspendJSt s' a' σb J hnib p hpT hpI sl' (by rw [hlbl]; simp [tcbLabelOf]) (J.stallT p hpT) ct hct
      _ bl call don _ ci sl exs buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`MidDecStWL` at `KW ∧ IsRestCap17` from the Suspend leaf** (module docstring). -/
theorem midDecRest17_of_sus (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSuspend
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThSusSt hA hMT hKD J hnib hsgb hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc hget e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap18_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`InvDecStWL` at `KW ∧ IsRestCap17` from the Suspend leaf** (module docstring). -/
theorem invDecRest17_of_sus (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSuspend
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThSusSt hA hMT hKD J hnib hsgb hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc hget e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap18_of hW.2 hS⟩

/-- (p3J gen 41) `MidDecStWL` at `KW ∧ IsRestCap17` gives it at `KW ∧ IsRestCap18` (antitone). -/
theorem midDecStWL_of_17 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap17_of18 hW.2⟩

/-- (p3J gen 41) `InvDecStWL` at `KW ∧ IsRestCap17` gives it at `KW ∧ IsRestCap18` (antitone). -/
theorem invDecStWL_of_17 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap17 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap17_of18 hW.2⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 41) **`DispStabFootLzk` [J]**: `DispStabFootLzj` with `invDecRest` / `midDecRest` restricted to
`IsRestCap18` (`IsRestCap17` minus the Thread caps at Suspend; module docstring). -/
structure DispStabFootLzk (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzj.invDecRest` at `KW ∧ IsRestCap18`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzj.midDecRest` at `KW ∧ IsRestCap18`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzj.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzj.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 41) **`DispStabFootLzk → DispStabFootLzj`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzj_of_Lzk (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzk (L := L) arI AR MR s a σ) :
    DispStabFootLzj (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest17_of_sus hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest17_of_sus hA hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 41) **`DispStabFootLzj → DispStabFootLzk`** (the honesty claim: `DispStabFootLzk` is implied). -/
theorem dispStabFootLzk_of_Lzj {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzj (L := L) arI AR MR s a σ) : DispStabFootLzk (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_17 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_17 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzk` only** (`hLzk` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzk [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzk : DispStabFootLzk (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzj hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzj_of_Lzk hA hnd hM hIp hKD hLzk)

end

end Fl4Proofs.P3.Mc
