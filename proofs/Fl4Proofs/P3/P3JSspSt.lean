/-
P3 (p3J gen 47): **the Thread cap's decode leaf at stable ghosts at SetSchedParams (8), for both classes, with its
`ProjW` footprint and the stable preempted exit**: the last TCB install label. FL4 `tcb.rs`
`decode_set_sched_params` / `thread_control_sched` (the caller's restart, the fault handler's install — a
`delete_one` of TCB slot 3 + `cap_insert` —, then `set_mcp`, `set_priority` and the SC step: none,
`schedcontext::unbind_tcb` or `schedcontext::bind_tcb`) at XTopJointMRTcbM's `tcb_set_sched_paramsJMG` with
P3JDelSp's stable installs (`tcbInsWG_st`) and the post-install steps' relation `Rf s s' := WritesIn s s' (ProjW H Cs
s)`.

* The post-install steps' footprints at stable ghosts: `set_mcp` P3JThMcp's `JAtZ.mcpProjW`, `set_priority`
  P3JThPrio's `JAtZ.setPrioProjW`, **`JAtZ.unbindTcbProjW`** (ScUnbind's `unbind_tcb_refines`: `SFoot` and the SC's
  word 24, inside `KFoot`, so inside P3JScFt's `UFoot` / `ProjW`), **`JAtZ.bindTcbProjW`** (ScBind's
  `bind_tcb_refines`: `KFoot`; its blocked-thread release check as XTopJointTcbSsp's `JAtZ.bindTcbJ` derives it);
  composed by `projW_trans`.
* **`tcb_set_sched_paramsJSt`**: start at `Z.mv G V` (a dispatch state), exits `MidX Z` / `MidXP Z` (the Ok exit:
  the final `JAtZ` gives `JStab`, the install's `WJSt` gives the footprint up to the install, `Rf` the rest).
* **`decThSspPSt`** (any flags, label 8): the dispatch leaf; the decode's side facts as XTopJointKEntry40 derives
  them (`hcapT` by `CapValid`, `hcapC` by `JAtZ.scCtxCap`, `hpI` by P3JThSus's `JAtZ.capNotIdle`).
* `ThHard20 l`: `ThHard19 l ∧ l ≠ TCBSetSchedParams`. `IsRestCap29`: Thread caps at `ThHard20`. `restCap28_of29`,
  `restCap29_of`. **`midDecRest28_of_ssp`** / **`invDecRest28_of_ssp`**, `midDecStWL_of_28` / `invDecStWL_of_28`.
* **`DispStabFootLzv` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap29`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzu_of_Lzv`** (under the tops' platform facts and `IrqPlatK`), **`dispStabFootLzv_of_Lzu`**
  (unconditional); top **`kernel_entry_runMcWKR_sysLzv`** (globals verbatim as `_sysLzu`).

Premise honesty: `DispStabFootLzv`'s decode fields are `DispStabFootLzu`'s at the smaller antecedent
(`IsRestCap29 → IsRestCap28`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzv` [J]; globals as `_sysLzu`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCnDelSt
import Fl4Proofs.P3.P3JScFt
import Fl4Proofs.P3.P3JThPrio
import Fl4Proofs.P3.P3JThMcp
import Fl4Proofs.P3.P3JThSus
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`unbind_tcb` of a thread's SC writes only `ProjW`** (module docstring). -/
theorem JAtZ.unbindTcbProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t i : U64} {x : Fl4Spec.Tcb}
    (ht : t ∈ Z.T) (hiC : i ∈ Z.C) (hk : σ.kheap t.bv = some (.tcb x)) (hsp : x.tcbSchedContext = some i.bv) :
    schedcontext.unbind_tcb st s i ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y, n, hky, -⟩ := hs.scs i hiC
  obtain ⟨y', n', hky', hyt⟩ := J.inv.back t.bv x i.bv hk hsp
  rw [hky] at hky'; cases hky'
  refine WP.spec_mono (unbind_tcb_refines s σ hS hR J.nsc J.inv hiC hky ht hyt) ?_
  rintro s' ⟨σ', he, hS', hR', hN', hI', -, hw5, -⟩
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) :=
    Sched.WritesIn.kfoot_of_sfoot_scw hS hiC (K := 24#u64) (by simp) (by simp) (by decide) hw5
  exact hWk.mono fun _ hb => uFoot_projW J (Or.inl (Or.inl hb))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`bind_tcb` writes only `ProjW`** (module docstring; the release check as `JAtZ.bindTcbJ`). -/
theorem JAtZ.bindTcbProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hTA : TimeAgree arI)
    {sc t : U64} (hsC : sc ∈ Z.C) (ht : t ∈ Z.T) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext y n)) (hy0 : y.scTcb = none)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none)
    (hrel : Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scReleased σ.curTime y = true) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  have hsc0 : sc ≠ 0#u64 := J.c0 sc hsC
  have hact_of : Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scActive y = true := fun h => by
    have h1 := hrel h
    unfold Fl4Spec.scReleased at h1; simp only [Bool.and_eq_true] at h1; exact h1.1
  have hblk : Fl4Spec.runnable xt.tcbState = false → inClassR xt.tcbState xt.tcbFault → Fl4Spec.scActive y = true →
      released σ y := by
    intro hr hcl ha
    have hq : Fl4Spec.ipcQueuedThreadState xt.tcbState = true := by
      rcases hcl.cls with h | ⟨m, h⟩ | ⟨e, d, h⟩ | ⟨e, r, d, h⟩
      · rw [h] at hr; cases hr
      all_goals rw [h]; rfl
    have h1 := hrel hq
    unfold Fl4Spec.scReleased at h1; simp only [Bool.and_eq_true] at h1
    exact ⟨h1.2, J.inv.suff hk ha⟩
  refine WP.spec_mono (bind_tcb_refines s a σ hS hR J.nsc J.inv hsC hsc0 hk hy0 ht hkt hxt0 hblk hTA) ?_
  rintro ⟨s', a'⟩ ⟨σ', he, hS', hR', hN', hI', -, hwk⟩
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := hwk
  exact hWk.mono fun _ hb => uFoot_projW J (Or.inl (Or.inl hb))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **SetSchedParams (8) at stable ghosts, with its `ProjW` footprint and the stable preempted exit**
(XTopJointMRTcbM's `tcb_set_sched_paramsJMG` at `tcbInsWG_st`, `Rf := WritesIn · · (ProjW H Cs ·)`; module
docstring). -/
theorem tcb_set_sched_paramsJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSchedParams)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hpI : p ≠ L.idleW s)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (hpsl : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.TCBSetSchedParams p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci ssl excaps buffer :=
  tcb_set_sched_paramsJMG (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s)
    (Rf := fun s1 s2 => P1.WritesIn st s1 s2 (Mc.ProjW (L := L) H Cs s1)) arI s ar σ J hni hsg hP0
    (tcbInsWG_st hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask s)
    ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩ (fun _ _ _ _ _ h => h.1.1.2.1)
    (fun _ _ _ h e => msF_mrC hMT.toC h e) hKD
    (restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN) hT hARI.toARKeep hTA
    (fun _ _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩)
    (fun _ _ _ h1 h2 => h1.projW_trans h2)
    (fun _ _ _ _ s' _ _ J' _ ht v => J'.mcpProjW ht s' v)
    (fun _ _ _ _ _ _ _ J' _ _ ht v hv _ hp1 => J'.setPrioProjW ht v hv hp1)
    (fun _ _ _ _ _ _ _ J' _ _ _ ht hi hk hsp _ _ => J'.unbindTcbProjW ht hi hk hsp)
    (fun _ _ _ _ _ _ _ J' _ _ hsC ht _ _ hk hy0 _ hkt hxt0 hrel _ _ _ _ _ _ _ _ _ _ _ _ =>
      J'.bindTcbProjW hTA hsC ht hk hy0 hkt hxt0 hrel)
    (fun _ _ _ _ _ h _ _ _ _ _ _ _ _ J' hmr hrf => ⟨JStab.mv (JStab.mv J'.stab), hmr, h.1.2.projW_trans hrf⟩)
    p hp slbl hlbl length buf ct hct args hlen hargs hpI hstall call ssl hAs hpsl extra x0 x1 x2 hx0 hx1 hx2
    excaps hXc hcapT hcapC blk don ci buffer

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **The Thread cap's decode at a dispatch state at SetSchedParams, any flags** (module docstring;
as P3JThIns's `decThInsSt`). -/
theorem decThSspPSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsg : SpecGlob σb)
    (hP0 : PPR0 σb) (hCb : SInvCk.CKI σb) (hRRb : SInvRr.RR σb) (hNSb : NativeScope σb)
    (hMb : MR a' σb.machineState) (hVTb : ValidMachineTime σb) (hVIb : ValidIrqMasks σb)
    {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    (hget : Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap (.Thread p), σb)}, False))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBSetSchedParams) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : MidX (L := L) arI AR MR Z H Cs s' s' a' σb := ⟨JStab.mv J.stab, hMb, P1.WritesIn.refl _ _⟩
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  have hpI : p ≠ L.idleW s' := J.capNotIdle hsg hget
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hXc := ExtraOK.xc J.xtop.rel.1 (hXO e exs he hexs)
  have hcapT : exAt e 0 ≠ 0#u64 → ∀ q, capV (L.mem s') (exAt e 0) = .Thread q → q ∈ Z.T := by
    intro hx q hcq
    have h0 := hXc.2 0 (exAt e 0) rfl
    obtain ⟨e0, he0⟩ : ∃ e0, exs[0]? = some e0 := by
      rcases exs with _ | ⟨e0, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e0, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e0 he0
    have hA0 : AbsSlot Z.th e0.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hcq]))
  have hcapC : exAt e 1 ≠ 0#u64 → ∀ q b, capV (L.mem s') (exAt e 1) = .SchedContext q b → q ∈ Z.C := by
    intro h1 q b hq
    obtain ⟨hz, hee1⟩ := hXc.2 1 _ rfl
    rcases hee : exs[1]? with _ | e1
    · exact absurd (hz.2 (List.getElem?_eq_none_iff.1 hee)) h1
    · obtain ⟨ex, -, ps, hps, hps1⟩ := hee1 e1 hee
      have hAs1 : AbsSlot Z.th e1.2 := ⟨ps, hps1, Or.inl hps⟩
      rw [ex] at hq
      exact (J.scCtxCap arI hAs1.isSlot (by rw [capAt_capV, hq])).1
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetSchedParams
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  exact xcapP_of_tcb arI s' a' σb hX0 _ _ (cslotAddr sl) p bl call don fp buf e ct hct sl' _ ci sl exs buffer
    (tcb_set_sched_paramsJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
      ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen
      hArgs hpI (J.stallT p hpT) call sl hAs hsc e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) (exAt_idx1 e)
      (exAt_idx2 e) exs hXc hcapT hcapC bl don ci buffer)

end

/-- (p3J gen 47) The Thread labels left after SetSchedParams. -/
def ThHard20 (l : U64) : Prop := ThHard19 l ∧ l ≠ fl4_abi.label.TCBSetSchedParams

/-- (p3J gen 47) The caps left after the SetSchedParams leaf, with the message label. -/
def IsRestCap29 : capability.Cap → U64 → Prop
  | .Thread _, l => ThHard20 l
  | _, _ => False

theorem restCap28_of29 {cp : capability.Cap} {l : U64} (h : IsRestCap29 cp l) : IsRestCap28 cp l := by
  cases cp
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap29_of {cp : capability.Cap} {l : U64} (h : IsRestCap28 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBSetSchedParams) : IsRestCap29 cp l := by
  cases cp
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`MidDecStWL` at `KW ∧ IsRestCap28` from the SetSchedParams leaf** (module docstring). -/
theorem midDecRest28_of_ssp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetSchedParams
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThSspPSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc hget he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap29_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`InvDecStWL` at `KW ∧ IsRestCap28` from the SetSchedParams leaf** (module docstring). -/
theorem invDecRest28_of_ssp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBSetSchedParams
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThSspPSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc hget he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap29_of hW.2 hS⟩

/-- (p3J gen 47) `MidDecStWL` at `KW ∧ IsRestCap28` gives it at `KW ∧ IsRestCap29` (antitone). -/
theorem midDecStWL_of_28 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap28_of29 hW.2⟩

/-- (p3J gen 47) `InvDecStWL` at `KW ∧ IsRestCap28` gives it at `KW ∧ IsRestCap29` (antitone). -/
theorem invDecStWL_of_28 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap28 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap28_of29 hW.2⟩

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

/-- (p3J gen 47) **`DispStabFootLzv` [J]**: `DispStabFootLzu` with `invDecRest` / `midDecRest` restricted to
`IsRestCap29` (`IsRestCap28` minus the Thread caps at SetSchedParams; module docstring). -/
structure DispStabFootLzv (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzu.invDecRest` at `KW ∧ IsRestCap29`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzu.midDecRest` at `KW ∧ IsRestCap29`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzu.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzu.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 47) **`DispStabFootLzv → DispStabFootLzu`** under the tops' platform facts and `IrqPlatK` (module
docstring). -/
theorem dispStabFootLzu_of_Lzv [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzv (L := L) arI AR MR s a σ) :
    DispStabFootLzu (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest28_of_ssp hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest28_of_ssp hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 47) **`DispStabFootLzu → DispStabFootLzv`** (the honesty claim: `DispStabFootLzv` is implied). -/
theorem dispStabFootLzv_of_Lzu {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzu (L := L) arI AR MR s a σ) : DispStabFootLzv (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_28 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_28 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzv` only** (`hLzv` [J];
globals verbatim as `_sysLzu`; module docstring). -/
theorem kernel_entry_runMcWKR_sysLzv [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzv : DispStabFootLzv (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzu hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzu_of_Lzv hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hLzv)

end

end Fl4Proofs.P3.Mc
