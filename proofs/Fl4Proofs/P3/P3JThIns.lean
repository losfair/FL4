/-
P3 (p3J gen 47): **the Thread cap's decode leaf at stable ghosts at SetTimeoutEndpoint (9), SetIPCBuffer (10) and
Configure (5), for both classes, with the stable preempted exit**: the remaining TCB install labels but
SetSchedParams. FL4 `tcb.rs` `decode_set_timeout_ep` / `decode_set_ipc_buffer` / `decode_configure` (each a
`thread_control_caps` run: `delete_one` of a TCB slot + `cap_insert`, the IPC buffer's word) at XTopJointMRTcbM's
`tcb_set_timeoutJMG` / `tcb_set_ipcJMG` / `tcb_configureJMG` with P3JDelSp's stable installs (`tcbInsWG_st`), as
P3JDelSp's `tcb_set_spaceJSt` did for SetSpace (11). The rest set {CNode at Revoke / Delete, Thread at 8 or 88}.

* **`tcb_set_timeoutJSt`**, **`tcb_set_ipcJSt`**, **`tcb_configureJSt`**: start at `Z.mv G V` (a dispatch state),
  exits `MidX Z` / `MidXP Z`. The untyped-source premises (`NcHyp`, IPCBuffer's one-slot form) are vacuous at `CKI`
  (P3JThSsp's `ncHyp_of_cki`, `kw_not_ut`); `FrNZ` is XTopJointKEntry35E's `JAtZ.fnzJ`.
* **`decThInsSt`** (any flags, labels 9 / 10 / 5): the dispatch leaf, as P3JThSsp's `decThSspSt`.
* `ThHard19 l`: `ThHard18 l` and `l` none of the three. `IsRestCap27`. `restCap26_of27`, `restCap27_of`.
  **`midDecRest26_of_ins`** / **`invDecRest26_of_ins`**, `midDecStWL_of_26` / `invDecStWL_of_26`.
* **`DispStabFootLzt` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap27`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzs_of_Lzt`** (under the tops' platform facts and `IrqPlatK`), **`dispStabFootLzt_of_Lzs`**
  (unconditional); top **`kernel_entry_runMcWKR_sysLzt`** (globals verbatim as `_sysLzs`).

Premise honesty: `DispStabFootLzt`'s decode fields are `DispStabFootLzs`'s at the smaller antecedent
(`IsRestCap27 → IsRestCap26`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzt` [J]; globals as `_sysLzs` (`IrqPlatK` [P] among them). No sorry. New module; no
existing statement changed.
-/
import Fl4Proofs.P3.P3JThSsp
import Fl4Proofs.P3.XTopJointKEntry35E
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
/-- (p3J gen 47) **SetTimeoutEndpoint (9) at stable ghosts, with its `ProjW` footprint and the stable preempted
exit** (XTopJointMRTcbM's `tcb_set_timeoutJMG` at `tcbInsWG_st`; module docstring). -/
theorem tcb_set_timeoutJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTimeoutEndpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (args : List Fl4Spec.Data) (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.TCBSetTimeoutEndpoint p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl args ci
      ssl excaps buffer :=
  tcb_set_timeoutJMG (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s) arI s ar σ
    J hni hsg hP0
    (tcbInsWG_st hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask s)
    ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩ (fun _ _ _ _ _ h => (midX_of_wjst h).mv)
    (fun _ _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩)
    (restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN) p hp slbl hlbl length buf ct hct hstall
    call ssl hAs extra x0 x1 x2 hx0 excaps hX args blk don ci buffer

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **SetIPCBuffer (10) at stable ghosts, with its `ProjW` footprint and the stable preempted exit**
(XTopJointMRTcbM's `tcb_set_ipcJMG` at `tcbInsWG_st`; the untyped-source premise vacuous at `CKI`; module
docstring). -/
theorem tcb_set_ipcJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.TCBSetIPCBuffer p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci ssl excaps buffer :=
  tcb_set_ipcJMG (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s) arI s ar σ J
    hni hsg hP0
    (tcbInsWG_st hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask s)
    ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩ (fun _ _ _ _ _ h => (midX_of_wjst h).mv)
    (fun _ _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩)
    (restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN) p hp slbl hlbl length buf ct hct args hlen hargs hstall
    call ssl hAs extra x0 x1 x2 hx0 excaps hX
    (fun sl hsl e hu => by
      subst e
      rw [kw_not_ut (Mc.kw_of_cki J hC hsl.isSlot)] at hu
      cases hu)
    J.fnzJ blk don ci buffer

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **Configure (5) at stable ghosts, with its `ProjW` footprint and the stable preempted exit**
(XTopJointMRTcbM's `tcb_configureJMG` at `tcbInsWG_st`; module docstring). -/
theorem tcb_configureJSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR)
    {G : MdbGhost} {V : XVs} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s ar σ) [VxE (Z.mv G V)] (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ) (hMV : MRV MR ar σ) (hC : SInvCk.CKI σ) (hRN : RrNs σ)
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKXP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s) (MidXP (L := L) arI AR MR Z H Cs s) s ar σ
      fl4_abi.label.TCBConfigure p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv)
      ci ssl excaps buffer :=
  tcb_configureJMG (Xo := MidX (L := L) arI AR MR Z H Cs s) (Xp := MidXP (L := L) arI AR MR Z H Cs s) arI s ar σ J
    hni hsg hP0
    (tcbInsWG_st hT hARI.toARKeep hticks hnd hMT.toC hKD hPA hARI.toMask s)
    ⟨JStab.mv J.stab, hMV.1, P1.WritesIn.refl _ _⟩ (fun _ _ _ _ _ h => (midX_of_wjst h).mv)
    (fun _ _ _ _ _ h => ⟨h.1.1.1.1.1, (midXP_of_wjstp hARI hT hnd hMT hKD hIP hTA hPA h).mv⟩)
    (restartWJSt hMT.toC J hni hsg hP0 hLv hMV hC hRN) p hp slbl hlbl length buf ct hct args hlen hargs hstall
    call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX (ncHyp_of_cki J hC _ _ _) J.fnzJ blk don ci buffer

/-- (p3J gen 47) The three install labels of this module. -/
def IsInsLbl (l : U64) : Prop :=
  l = fl4_abi.label.TCBSetTimeoutEndpoint ∨ l = fl4_abi.label.TCBSetIPCBuffer ∨ l = fl4_abi.label.TCBConfigure

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **The Thread cap's decode at a dispatch state at SetTimeoutEndpoint / SetIPCBuffer / Configure,
any flags** (module docstring; as P3JThSsp's `decThSspSt`). -/
theorem decThInsSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : IsInsLbl info.label) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : MidX (L := L) arI AR MR Z H Cs s' s' a' σb := ⟨JStab.mv J.stab, hMb, P1.WritesIn.refl _ _⟩
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hXc := ExtraOK.xc J.xtop.rel.1 (hXO e exs he hexs)
  rcases hl with hl | hl | hl <;> rw [hl]
  · obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetTimeoutEndpoint
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    exact xcapP_of_tcb arI s' a' σb hX0 _ _ (cslotAddr sl) p bl call don fp buf e ct hct sl' _ ci sl exs buffer
      (tcb_set_timeoutJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
        ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct
        (J.stallT p hpT) call sl hAs e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) exs hXc _ bl don ci buffer)
  · obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBSetIPCBuffer
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    exact xcapP_of_tcb arI s' a' σb hX0 _ _ (cslotAddr sl) p bl call don fp buf e ct hct sl' _ ci sl exs buffer
      (tcb_set_ipcJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
        ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen
        hArgs (J.stallT p hpT) call sl hAs e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) exs hXc bl don ci
        buffer)
  · obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBConfigure
    refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
    exact xcapP_of_tcb arI s' a' σb hX0 _ _ (cslotAddr sl) p bl call don fp buf e ct hct sl' _ ci sl exs buffer
      (tcb_configureJSt hARI hA hticks hnd hMT hKD hIP hTA hPA s' a' σb J hnib hsg hP0 J.live
        ⟨hMb, hVTb, hVIb⟩ hCb ⟨hRRb, hNSb⟩ p hp sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU hLen
        hArgs (J.stallT p hpT) call sl hAs e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) (exAt_idx1 e)
        (exAt_idx2 e) exs hXc bl don ci buffer)

end

/-- (p3J gen 47) The Thread labels left after SetTimeoutEndpoint / SetIPCBuffer / Configure. -/
def ThHard19 (l : U64) : Prop := ThHard18 l ∧ ¬ IsInsLbl l

/-- (p3J gen 47) The caps left after the three install leaves, with the message label. -/
def IsRestCap27 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard19 l
  | _, _ => False

theorem restCap26_of27 {cp : capability.Cap} {l : U64} (h : IsRestCap27 cp l) : IsRestCap26 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap27_of {cp : capability.Cap} {l : U64} (h : IsRestCap26 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ IsInsLbl l) : IsRestCap27 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`MidDecStWL` at `KW ∧ IsRestCap26` from the three install leaves** (module docstring). -/
theorem midDecRest26_of_ins [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ IsInsLbl info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThInsSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap27_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **`InvDecStWL` at `KW ∧ IsRestCap26` from the three install leaves** (module docstring). -/
theorem invDecRest26_of_ins [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIP : IrqPlatA arI AR)
    (hTA : TimeAgree arI) (hPA : PPPlatA arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ IsInsLbl info.label
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsg, hP0, hNSb, hVTb, hVIb⟩ := dispSspFacts hnd hX hni hBA J
    exact decThInsSt hARI hA hticks hnd hMT hKD hIP hTA hPA J hnib hsg hP0 hCb hRRb hNSb hMb hVTb hVIb hct
      a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap27_of hW.2 hS⟩

/-- (p3J gen 47) `MidDecStWL` at `KW ∧ IsRestCap26` gives it at `KW ∧ IsRestCap27` (antitone). -/
theorem midDecStWL_of_26 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap26_of27 hW.2⟩

/-- (p3J gen 47) `InvDecStWL` at `KW ∧ IsRestCap26` gives it at `KW ∧ IsRestCap27` (antitone). -/
theorem invDecStWL_of_26 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap26 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap26_of27 hW.2⟩

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

/-- (p3J gen 47) **`DispStabFootLzt` [J]**: `DispStabFootLzs` with `invDecRest` / `midDecRest` restricted to
`IsRestCap27` (`IsRestCap26` minus the Thread caps at SetTimeoutEndpoint / SetIPCBuffer / Configure; module
docstring). -/
structure DispStabFootLzt (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzs.invDecRest` at `KW ∧ IsRestCap27`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzs.midDecRest` at `KW ∧ IsRestCap27`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap27 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzs.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzs.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 47) **`DispStabFootLzt → DispStabFootLzs`** under the tops' platform facts and `IrqPlatK` (module
docstring). -/
theorem dispStabFootLzs_of_Lzt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzt (L := L) arI AR MR s a σ) :
    DispStabFootLzs (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest26_of_ins hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest26_of_ins hARI hA ⟨hmax, htu⟩ hnd (MachPlatF.toT hM hIp) hKD hIA hT ⟨hPAi, hT.mb⟩ hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 47) **`DispStabFootLzs → DispStabFootLzt`** (the honesty claim: `DispStabFootLzt` is implied). -/
theorem dispStabFootLzt_of_Lzs {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzs (L := L) arI AR MR s a σ) : DispStabFootLzt (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_26 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_26 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 47) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzt` only** (`hLzt` [J];
globals verbatim as `_sysLzs`, `hIA : IrqPlatK` [P] among them; module docstring). -/
theorem kernel_entry_runMcWKR_sysLzt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzt : DispStabFootLzt (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzs hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzs_of_Lzt hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hLzt)

end

end Fl4Proofs.P3.Mc
