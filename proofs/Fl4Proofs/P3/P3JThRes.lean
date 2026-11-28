/-
P3 (p3J gen 41): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at Resume (13), for
both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–5, 8–11, 17, 22, 24, or SetEPTRoot}.

* **`JAtZ.restartProjW`**: `restart` of a thread of `Z.T` at a `JAtZ` state writes only `ProjW` (P3JRstFt's
  `sched.restart.kwN0` through P3JMcKwN's `kwN_projW`).
* **`tcb_resumeJSt`**: XTopJointTcb's `tcb_resumeJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts: the restart of the caller by `stsProjW`, the target's `restart` by
  `restartProjW` beside XTopJointRestart's `JAtZ.restartTcbJ`).
* **`decThResSt`** (any flags): the dispatch leaf (as P3JThSus's `decThSusSt`; never preempted). The platform's
  `MIN_BUDGET` ([P] in the non-stable chain, `hmb`) is ScPlatform's `TimeAgree.mb` of the tops' existing
  `TimeAgree` (`hT`): no new premise.
* `ThHard11 l`: `ThHard10 l ∧ l ≠ TCBResume`. `IsRestCap19`. `restCap18_of19`, `restCap19_of`.
  **`midDecRest18_of_res`** / **`invDecRest18_of_res`**, `midDecStWL_of_18` / `invDecStWL_of_18`.
* **`DispStabFootLzl` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap19`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzk_of_Lzl`** (under the tops' platform facts, incl. `TimeAgree`), **`dispStabFootLzl_of_Lzk`**;
  top **`kernel_entry_runMcWKR_sysLzl`** (globals verbatim as `_sysLzk`).

Premise honesty: `DispStabFootLzl`'s decode fields are `DispStabFootLzk`'s at the smaller antecedent
(`IsRestCap19 → IsRestCap18`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzl` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThSus
import Fl4Proofs.P3.P3JRstFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 41) **`restart` of a thread of `Z.T` writes only `ProjW`** (module docstring). -/
theorem JAtZ.restartProjW (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    sched.restart st arI s a t ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨⟨Q0, R0, h0⟩, hB, hX, hS, -⟩ := J.blk
  refine WP.spec_mono (P1.sched.restart.kwN0 hAT s a t Q0 R0 h0 (J.zH.1 t ht) hB hX hS) ?_
  rintro ⟨s', a'⟩ F
  simp only [WP.uncurry'_pair] at F ⊢
  exact (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **Resume at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_resumeJ`; module
docstring). -/
theorem tcb_resumeJSt (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (x0 : U64) (hxS : IsSlot Z.th x0)
    (hcap : capAt (L.mem s) x0 = ok (.Thread p))
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbResume)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBResume p c blk call don slbl args
      ci sl excaps buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.resume p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  have hctT : ct ∈ Z.T := J.thT ct (J.xtop.curTcb (J.curEq hct).1).1
  obtain ⟨s1, σ1, x, hrc1, hst, hk, hcur, -, hns, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  obtain ⟨-, x', hk', hrun⟩ := J.curRunnable hni hct
  rw [hk] at hk'; cases hk'
  -- the slots kept by the caller's restart
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := XTopAt.restart J.xtop hcur hk hrun
    rw [hs1, WP.spec_ok] at h; exact h.2.1
  have hcap1 : capAt (L.mem s1) x0 = ok (.Thread p) := by
    rw [capAt_capV, hSS.capV hxS, ← capAt_capV]; exact hcap
  unfold TcbOKX
  rw [decode_resume_eq arI s ar p c hstall, hrc1]
  simp only [bind_ok]
  refine WP.spec_bind (WP.spec_and (J1.restartTcbJ hAT (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
    (jCancel_reply arI) (hmb ar) hpT hxS hcap1 (fun u h => hns u h)) (J1.restartProjW hAT hpT)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨-, σ', hres, V, Ac', Lst', D', J2⟩, W2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.resume p.bv))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hres]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac', Lst', D', J2⟩, W1.projW_trans W2⟩⟩

end

/-- (p3J gen 41) The Thread labels left after Resume. -/
def ThHard11 (l : U64) : Prop := ThHard10 l ∧ l ≠ fl4_abi.label.TCBResume

/-- (p3J gen 41) The caps left after the Resume leaf, with the message label. -/
def IsRestCap19 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard11 l
  | _, _ => False

theorem restCap18_of19 {cp : capability.Cap} {l : U64} (h : IsRestCap19 cp l) : IsRestCap18 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap19_of {cp : capability.Cap} {l : U64} (h : IsRestCap18 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBResume) : IsRestCap19 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem res_nonIns : TcbNonIns fl4_abi.label.TCBResume := by
  unfold TcbNonIns fl4_abi.label.TCBResume fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The Thread cap's decode at a dispatch state at Resume, any flags** (module docstring). -/
theorem decThResSt (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb)
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
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hl : info.label = fl4_abi.label.TCBResume) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBResume
  have hl5 : fl4_abi.label.TCBResume.val ≠ 5 ∧ fl4_abi.label.TCBResume.val ≠ 8 ∧
      fl4_abi.label.TCBResume.val ≠ 9 ∧ fl4_abi.label.TCBResume.val ≠ 10 ∧
      fl4_abi.label.TCBResume.val ≠ 11 := by simp [fl4_abi.label.TCBResume]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine XCapP.mrGT (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD res_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_resumeJSt hA hT.mb s' a' σb J hnib p hpT (cslotAddr sl) hAs.isSlot hc sl'
      (by rw [hlbl]; simp [tcbLabelOf]) (J.stallT p hpT) ct hct _ bl call don _ ci sl exs buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`MidDecStWL` at `KW ∧ IsRestCap18` from the Resume leaf** (module docstring). -/
theorem midDecRest18_of_res (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap19 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBResume
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThResSt hA hT hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap19_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`InvDecStWL` at `KW ∧ IsRestCap18` from the Resume leaf** (module docstring). -/
theorem invDecRest18_of_res (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap19 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBResume
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThResSt hA hT hMT hKD J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc e exs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap19_of hW.2 hS⟩

/-- (p3J gen 41) `MidDecStWL` at `KW ∧ IsRestCap18` gives it at `KW ∧ IsRestCap19` (antitone). -/
theorem midDecStWL_of_18 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap19 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap18_of19 hW.2⟩

/-- (p3J gen 41) `InvDecStWL` at `KW ∧ IsRestCap18` gives it at `KW ∧ IsRestCap19` (antitone). -/
theorem invDecStWL_of_18 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap18 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap19 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap18_of19 hW.2⟩

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

/-- (p3J gen 41) **`DispStabFootLzl` [J]**: `DispStabFootLzk` with `invDecRest` / `midDecRest` restricted to
`IsRestCap19` (`IsRestCap18` minus the Thread caps at Resume; module docstring). -/
structure DispStabFootLzl (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzk.invDecRest` at `KW ∧ IsRestCap19`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap19 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzk.midDecRest` at `KW ∧ IsRestCap19`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap19 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzk.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzk.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 41) **`DispStabFootLzl → DispStabFootLzk`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzk_of_Lzl (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzl (L := L) arI AR MR s a σ) :
    DispStabFootLzk (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest18_of_res hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest18_of_res hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 41) **`DispStabFootLzk → DispStabFootLzl`** (the honesty claim: `DispStabFootLzl` is implied). -/
theorem dispStabFootLzl_of_Lzk {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzk (L := L) arI AR MR s a σ) : DispStabFootLzl (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_18 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_18 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzl` only** (`hLzl` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzl [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzl : DispStabFootLzl (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzk hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzk_of_Lzl hA hT hnd hM hIp hKD hLzl)

end

end Fl4Proofs.P3.Mc
