/-
P3 (p3J gen 38): **the SchedContext Unbind leaf at stable ghosts, for both classes; the top without it**.

* `JAtZ.scUnbindJSt`, **`decScUnbindJSt`**: ScJointUnbind's `JAtZ.scUnbindJ` / `decode_invocation_sched_context_unbindJ`
  with `JStab Z H Cs` for `JAt` (the same proofs: the restart is at `Z`, `unbind_all_tcbs` / `unbind_ntfn` /
  `unbind_reply` each at `Z.mv Z.G V`, peeled by `JStab.mv`).
* **`decScStY`** (any flags): P3JScLeaf's `decScSt` for every label but YieldTo (Unbind by `decScUnbindJSt`, its
  `Entered` / SC facts as `decScSt`'s; the footprint P3JScFt's `scDecFootJ`, which covers every label).
* `IsRestCap5 cp l`: CNode, Thread, or a SchedContext cap with `l` = `SchedContextYieldTo`; `restCap4_of5`,
  `restCap5_of`. **`midDecRest4_of_scU`** / **`invDecRest4_of_scU`**: P3JScTop's `MidDecStWL` / `InvDecStWL` at
  `KW ∧ IsRestCap4` from the Unbind leaf and those at `KW ∧ IsRestCap5`; `midDecStWL_of_4`, `invDecStWL_of_4`
  (antitone).
* **`DispStabFootLu` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap5`, midSpec, midRecvSw verbatim};
  **`dispStabFootLt_of_Lu`** (the tops' platform facts), **`dispStabFootLu_of_Lt`** (honesty, proved); top
  **`kernel_entry_runMcWKR_sysLu`** (globals verbatim as `_sysLt`).

Premise honesty: `DispStabFootLu`'s decode fields are `DispStabFootLt`'s at a smaller antecedent
(`IsRestCap5 cp l → IsRestCap4 cp l`), midSpec / midRecvSw verbatim: implied by `DispStabFootLt`
(`dispStabFootLu_of_Lt`); conversely implies it given the tops' platform facts (`dispStabFootLt_of_Lu`).

Named premise: `DispStabFootLu` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JScTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 38) **Unbind's invocation at `J`, at stable ghosts** (ScJointUnbind's `JAtZ.scUnbindJ`, the same
proof; its steps keep `Z.G`, each moving only the VSpace sets). -/
theorem JAtZ.scUnbindJSt {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {sc : U64} (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.unbind_all_tcbs st arI s2 a sc
      let s4 ← schedcontext.unbind_ntfn st s3 sc
      let s5 ← schedcontext.unbind_reply st s4 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ σ0 σ' : Fl4Spec.State Unit,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind sc.bv) σ0 = ({([], σ')}, False) ∧
        JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 σ' ⦄ := by
  obtain ⟨s1, σ1, x, -, he0, -, hcur, -, hns, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hs1]; simp only [bind_ok]
  have hp0 : sc ≠ 0#u64 := J1.c0 sc hsc
  have hpi1 : sc.bv ≠ σ1.idleSc := by
    rw [((pres_setThreadState (f := (true, true)) _ _).of_eq he0).isc]; exact hpi
  obtain ⟨hna, hidle⟩ := J1.scWordsNS hsc hp0 hpi1 hns
  refine WP.spec_bind (JAtZ.unbindAllJ arI J1 hsc hp0 hpi1 hna hidle) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, he2, V2, Ac2, Lst2, D2, J2⟩
  refine WP.spec_bind (JAtZ.unbindNtfnJ arI J2 hsc hp0) ?_
  rintro s3 ⟨σ3, he3, V3, Ac3, Lst3, D3, J3⟩
  refine WP.spec_bind (JAtZ.unbindReplyJ arI J3 hsc hp0) ?_
  rintro s4 ⟨σ4, he4, V4, Ac4, Lst4, D4, J4⟩
  rw [WP.spec_ok]
  refine ⟨rfl, σ1, σ4, by rw [← hcur]; exact he0, ?_, JStab.mv (JStab.mv (JStab.mv J4.stab))⟩
  show (Fl4Spec.schedContextUnbindAllTcbs sc.bv >>= _) σ1 = _
  rw [nd_bind_one he2, nd_bind_one he3, nd_bind_one he4]; rfl

set_option maxHeartbeats 8000000 in
/-- (p3J gen 38) **The SchedContext cap's Unbind, `XCap` at stable ghosts** (ScJointUnbind's
`decode_invocation_sched_context_unbindJ`, the same proof with `JStab Z H Cs` for `JAt`). -/
theorem decScUnbindJSt (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l42 : lbl = fl4_abi.label.SchedContextUnbind)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JStab (L := L) arI AR Z H Cs) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  left
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hctT).ne0 (by rw [e]; rfl)
  obtain ⟨y, n, hk, hx⟩ := hs.scs sc hsc
  have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbind := by
    rw [hlbl, l42]; unfold scLabelOf; simp
  have hpre : (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = (do
      let scx ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getSchedContext sc.bv
      let ctPtr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
      Fl4Spec.NonDetE.whenE (scx.scTcb = some ctPtr) <| Fl4Spec.NonDetE.throwError .illegalOperation
      Fl4Spec.NonDetE.returnOk <| .invokeSchedContextUnbind sc.bv :
        Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation).run σ := by
    unfold Fl4Spec.decodeSchedContextInvocation; rw [hg]
  rw [lE_bind (getSchedContext_eq hk), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
    ({(σ.curThread, σ)}, False) from rfl), hcur] at hpre
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, J.stab⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold schedcontext.decode
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0).1
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok]
  have l44 : lbl ≠ fl4_abi.label.SchedContextConsumed := lbl_ne l42 (by simp)
  have l41 : lbl ≠ fl4_abi.label.SchedContextBind := lbl_ne l42 (by simp)
  have l43 : lbl ≠ fl4_abi.label.SchedContextUnbindObject := lbl_ne l42 (by simp)
  rw [ite_eq_right l44, ite_eq_right l41, ite_eq_right l43, ite_eq_left l42]
  step with P1.obj.Sc.tcb.spec as ⟨i1, hi1⟩
  rw [scTcbA_eq] at hi1
  subst hi1
  by_cases he : L.mem s (scW sc 24#u64) = ct
  · rw [ite_eq_left he]
    refine illegal_ok s a _ (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, J.stab⟩)
    exact run_liftME_err (by
      rw [hpre]; exact wE_pos (by rw [hx.tcb]; exact (bv_optRef_some hct0).2 he) _ _ σ)
  rw [ite_eq_right he]
  have hrun : (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
      ({(.ok (.invokeSchedContextUnbind sc.bv), σ)}, False) := by
    rw [hpre, wE_neg (fun h => he ((bv_optRef_some hct0).1 (hx.tcb ▸ h)))]; rfl
  refine WP.spec_mono (JAtZ.scUnbindJSt J hni hct hsc hpi) ?_
  rintro r ⟨h1, σ0, σ', he0, he1, G', V', Ac', Lst', D', J'⟩
  obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
  exact Or.inr ⟨.invokeSchedContext (.invokeSchedContextUnbind sc.bv), DecOut.of_eq (run_liftME_ok hrun), σ0,
    by rw [hcur]; exact he0, (.ok [], σ'),
    mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind sc.bv)) (s := σ0)
      (x := ([], σ')) (by rw [he1]; exact Set.mem_singleton _),
    ⟨(Z.mv G' V').th, (Z.mv G' V').G, Or.inl ⟨h1, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ⟨G', V', Ac', Lst', D', J'⟩⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 38) The caps left after the Unbind leaf, with the message label: CNode, Thread, and a SchedContext cap
invoked with YieldTo. -/
def IsRestCap5 : capability.Cap → U64 → Prop
  | .CNode .., _ => True
  | .Thread _, _ => True
  | .SchedContext .., l => l = fl4_abi.label.SchedContextYieldTo
  | _, _ => False

theorem restCap4_of5 {cp : capability.Cap} {l : U64} (h : IsRestCap5 cp l) : IsRestCap4 cp l := by
  cases cp
  case SchedContext p sb => exact Or.inr h
  all_goals first | trivial | exact False.elim h

theorem restCap5_of {cp : capability.Cap} {l : U64} (h : IsRestCap4 cp l)
    (hS : ¬ ∃ p sb, cp = .SchedContext p sb ∧ l = fl4_abi.label.SchedContextUnbind) : IsRestCap5 cp l := by
  cases cp
  case SchedContext p sb =>
    rcases (h : l = _ ∨ l = _) with e | e
    · exact absurd ⟨p, sb, rfl, e⟩ hS
    · exact e
  all_goals first | trivial | exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The SchedContext cap's decode at a dispatch state, any flags, any label but YieldTo** (module
docstring). -/
theorem decScStY (hA : P0.ArchTotal arI) (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.SchedContext p sb))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs) (hy : info.label ≠ fl4_abi.label.SchedContextYieldTo)
    (args : List Fl4Spec.Data) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.SchedContext p sb) bl call don fp buf e mi.miLabel
      args ci sl exs buffer ct := by
  by_cases hu : info.label ≠ fl4_abi.label.SchedContextUnbind
  · exact decScSt hA hARI hMT hKD hT hmax htu J hnib hMb hct hinfo hmi hbuf hbuffer hr2 her sl hsl hc he hexs hu hy
      args bl call don fp ci
  rw [not_not] at hu
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hq : QuietF (.SchedContext p sb) := by simp [QuietF]
  refine XCapP.mrT hMT ?_ (MKD.decode_quiet L.total hA hKD hq hMb (fun _ _ _ h => by cases h))
    (fun inv hd => MachT.dec_quiet _ _ _ _ _ _ _ _ (quietS_of hq) σb _ hd.1 inv rfl)
  have hX := J.xtop
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  obtain ⟨hpC, hpi, -, -, hback, hbn⟩ := J.scCtxCap arI hAs.isSlot hc
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  obtain ⟨sl', hlbl, -, hd⟩ := sc_canon info.label
  refine XCapP.lbl_congr arI (specDec_sc p sb hd) ?_
  refine XCap.toPN arI ?_ (specDec_noPreK (by trivial))
  have hex := ExtraOK.rel1 hX.rel.1 (hXO e exs he hexs)
  have hx0 := exAt_idx0 e
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hnib hct
  have hcs := ct_schedulable (J.curInv (by rw [hnib.2]; simp)) J.act J.inv (hcur ▸ hkc) hrun
  rw [hcur] at hcs
  refine XCap.andW (X := JStab (L := L) arI AR (Z.mv Z.G V') H Cs)
    (Q := fun s1 => P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ?_
    (scDecFootJ J hT (hT.mb a') hmax (htu a') info.label sl' hlbl sb hpC hpi hback hbn hct hcs e (exAt e 0) hx0
      exs hex (msgLen info buf) (cslotAddr sl) buf bl call don fp)
  exact decScUnbindJSt s' a' σb J hnib info.label sl' hlbl hu sb hpC hpi hback hct e exs (msgLen info buf)
    (cslotAddr sl) buf bl call don fp args ci sl buffer

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **`MidDecStWL` at `KW ∧ IsRestCap4` from the Unbind leaf** (module
docstring). -/
theorem midDecRest4_of_scU (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p sb, cp = .SchedContext p sb ∧ info.label = fl4_abi.label.SchedContextUnbind
  · obtain ⟨p, sb, rfl, hu⟩ := hS
    have hy : info.label ≠ fl4_abi.label.SchedContextYieldTo := lbl_ne hu (by simp)
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScStY hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs hy _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap5_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **`InvDecStWL` at `KW ∧ IsRestCap4` from the Unbind leaf** (module
docstring). -/
theorem invDecRest4_of_scU (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p sb, cp = .SchedContext p sb ∧ info.label = fl4_abi.label.SchedContextUnbind
  · obtain ⟨p, sb, rfl, hu⟩ := hS
    have hy : info.label ≠ fl4_abi.label.SchedContextYieldTo := lbl_ne hu (by simp)
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decScStY hA hARI hMT hKD hT hmax htu J hnib hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc he hexs hy _ _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap5_of hW.2 hS⟩

/-- (p3J gen 38) `MidDecStWL` at `KW ∧ IsRestCap4` gives it at `KW ∧ IsRestCap5` (antitone). -/
theorem midDecStWL_of_4 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap4_of5 hW.2⟩

/-- (p3J gen 38) `InvDecStWL` at `KW ∧ IsRestCap4` gives it at `KW ∧ IsRestCap5` (antitone). -/
theorem invDecStWL_of_4 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap4 cp l) Z H Cs s a σ n call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap4_of5 hW.2⟩

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

/-- (p3J gen 38) **`DispStabFootLu` [J]**: `DispStabFootLt` with `invDecRest` / `midDecRest` restricted to the
CNode and Thread caps and the SchedContext caps invoked with YieldTo (module docstring). -/
structure DispStabFootLu (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLt.invDecRest` at `KW ∧ IsRestCap5`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLt.midDecRest` at `KW ∧ IsRestCap5`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap5 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLt.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLt.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 38) **`DispStabFootLu → DispStabFootLt`** given the tops' platform facts (module docstring). -/
theorem dispStabFootLt_of_Lu (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLu (L := L) arI AR MR s a σ) :
    DispStabFootLt (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest4_of_scU hA hnd hARI (MachPlatF.toT hM hIp) hKD hT hmax htu hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest4_of_scU hA hnd hARI (MachPlatF.toT hM hIp) hKD hT hmax htu hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 38) **`DispStabFootLt → DispStabFootLu`** (the honesty claim: `DispStabFootLu` is implied). -/
theorem dispStabFootLu_of_Lt {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLt (L := L) arI AR MR s a σ) : DispStabFootLu (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_4 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_4 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLu` only** (`hLu` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLu [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLu : DispStabFootLu (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLt hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLt_of_Lu hARI hA hnd hM hIp hKD hT hmax htu hLu)

end

end Fl4Proofs.P3.Mc
