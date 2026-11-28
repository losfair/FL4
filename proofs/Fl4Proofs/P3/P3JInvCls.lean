/-
P3 (p3J gen 35): **the invoking class (Send / NBSend / Call) of the syscall clause reduced to its per-cap decode
leaf** (the stable invoke skeleton with footprint, gen 32/33's mid skeleton for `handle_invocation call bl don
false` on the CAP register, then `after_invocation`).

* **`InvDecSt` [J]**: at every dispatch state of the entry (as `DispStabFootAt`) and every number `n` of the class
  with its flags (`InvSys n call bl don`), for the front reads and every slot / cap the lookup can find (P3JMidInv's
  `MidDecSt` binder chain), the decode leaf `XCapP (MidX …) (MidXP …)` of the cap at `blocking = bl`,
  `is_call = call`, `can_donate = don`, `first_phase = false` (P3JMidInv's `MidX` / `MidXP`: `JStab Z H Cs`, `MR`,
  footprint `ProjW H Cs s'`; the preempted half through `after_invocation`).
* **`invInvHI`**: the invocation at `MidX` / `MidXP` by XTopJointEntry's `handle_invocation_refinesMXP` in gen 33's
  `refine … ?_` shape. Leaves: the front reads (`JAtZ.frontEx`), the extra caps (`JAtZ.extraJ`) and the lookup
  fault (`capFaultCorr_lookup`) — with `blocking` these run `handle_fault`: StPostFault's `JAtZ.faultHypJZGSt`
  (stable), `MKD.faults_handle_fault` (`MR`), P3JMcFlt's `faultProjW` (footprint; the dispatch state is `Entered`,
  its current thread in no ready queue, its fault handler valid: `BudgetAt.entered`, `BudgetAt.shape27`,
  `SInvX.ctQ`, `sinvB_disp`); the success tail (StPostIoLeaf's `JAtZ.flTailJSt`, `MKD.fl_tail`, P3JInvFt's
  `flTailProjWc`); the error reply (StPostIoLeaf's `replyFailJSt`, `MKD.reply_err_tail`, P3JInvFt's
  `replyErrProjW` with `NoBufCap` by `noBufCap_cki`); the current thread kept (P3JMidInv's `midPK`); the decode by
  `InvDecSt`.
* `inv_afterSt`, `dispatch_invSt`, **`dispInv_stFt`**: `after_invocation` and the if-chain (XTopJointDispatch's
  `invoke_afterJ` / `dispatch_invokeJ` shape; `JStabR` by `JAtZ.toR`): the inv class of `DispStabFootAt` from
  `InvDecSt`.
* **`DispStabFootLi` [J]** {invDec, midDecRest, midSpec, midRecvSw}: P3JMidEp's `DispStabFootLn` with `inv`
  replaced by `invDec`; **`dispStabFootLn_of_Li`**, top **`kernel_entry_runMcWKR_sysLi`** (globals as `_sysLn`).

Premise honesty: `invDec` (`InvDecSt`) speaks of a sub-call of `inv`'s call (the decode and perform of the looked-up
cap inside `handle_invocation`); it implies `inv` (`dispInv_stFt`) and is **not implied by it**, exactly as gen 33's
`midDec` against `midInv`. Justification that it is not false on reachable states: it is `inv` with the proved
skeleton removed; the decode leaves are where the non-stable chain's per-cap premises sit (XTopJointKEntry23P's
`decOK_JMU`, every arm ending at `Z.mv G' V'` with the entry's `H` / `Cs` but the untyped retype, which `CKI`
excludes: no untyped cap is in any slot); the preempted arms are `MidXP` (the non-stable `JAtPreMV`); the footprint
of every non-retype decode lies in `ProjW` (P1's per-family footprints are `KW` / `IpcW` words of `H`'s objects).
Removed from the [J] content: the front reads, the lookup and its fault, the extra caps and their fault, the success
tail, the error reply and `after_invocation` of the invoking class.

Named premises: `InvDecSt` [J], `DispStabFootLi` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JInvFt
import Fl4Proofs.P3.P3JMidEp
import Fl4Proofs.P3.StPostIoLeaf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 35) **`InvDecSt` [J]**: the decode leaf of the invoking class at every dispatch state of the entry
(module docstring). -/
def InvDecSt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (call bl don : Bool) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct, sched.cur_thread st s' = ok ct → InvSys n call bl don →
    ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64),
      msg.msg_info st s' ct = ok info →
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False) →
      msg.lookup_ipc_buffer st s' false ct = ok buf →
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False) →
      ipc.lookup_extra_caps st s' ct buf info = ok r2 →
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False) →
      Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False) →
      ∀ (sl : Fl4Spec.CslotPtr) (cp : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
        (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) = ok cp → Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap cp, σb)}, False) →
        r2 = .Ok e → er = .ok exs →
        XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
          info.label (msgLen info buf) (cslotAddr sl) cp bl call don false buf e mi.miLabel
          (argsU.map UScalar.bv) (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) sl exs buffer ct

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The invoking class's invocation at `MidX` / `MidXP`** (module docstring). -/
theorem invInvHI [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (hD : InvDecSt (L := L) arI AR MR Z H Cs s a σ n call bl don) (σb : Fl4Spec.State Unit) (hBA : BudgetAt σ σb true)
    (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
    (hKF : KFrontB (L := L) arI s a s' a') (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb)
    (hMb : MR a' σb.machineState) (hCb : SInvCk.CKI σb) (hRRb : SInvRr.RR σb)
    (ct : U64) (hct : sched.cur_thread st s' = ok ct) (hn : InvSys n call bl don) :
    syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        call bl don false (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hXt := J.xtop
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib : Entered σb := BudgetAt.entered hnd hk0 (hX.entered hni) hBA
  obtain ⟨-, ek, ect, -, -, eq⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨hvfh, -⟩ := SInvAll.sinvB_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    hX.sb hni hk0 rfl rfl ek' ect
  have hq : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect, eq]; exact hX.ctQ
  have hblk := J.blk
  have hNB := Mc.noBufCap_cki J hCb
  have hF : ∀ {f : error.Fault} {f' : Fl4Spec.Fault}, FaultCorrG f f' →
      faults.handle_fault st arI s' a' ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σb).1,
        RelTopM (L := L) r.1 z.2 ∧ MidX (L := L) arI AR MR Z H Cs s' r.1 r.2 z.2 ⦄ := by
    intro f f' hcf
    refine WP.spec_mono (WP.spec_and (WP.spec_and (J.faultHypJZGSt hA hnib hct hq hvfh hcf)
      (MKD.faults_handle_fault L.total hA hKD hMb)) (Mc.faultProjW hA J hCb hnib hq hct f)) ?_
    rintro r ⟨⟨⟨z, hz, h1, h2⟩, h3⟩, h4⟩
    exact ⟨z, hz, h1, JStab.mv h2, msF_mrT hMT h3 (congrArg Prod.fst (MachT.mtk_handleFaultG _ _ σb z hz)), h4⟩
  refine handle_invocation_refinesMXP arI (MidX (L := L) arI AR MR Z H Cs s')
    (MidXP (L := L) arI AR MR Z H Cs s') true s' a' σb
    Z.th Z.G hXt.rel.1 hXt.rel.2.1 hXt.rel.2.2.1 hXt.rel.2.2.2.1 hXt.rel.2.2.2.2.1 ?x0 ct hct hcur htcb
    call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er
    her ?rr (argsU.map UScalar.bv) hmrs ?fl ?repS ?repF ?pk ?dec
  case x0 => exact ⟨JStab.mv J.stab, hMb, P1.WritesIn.refl _ _⟩
  case rr =>
    exact (J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her).imp id
      fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ => hF (FaultCorrG.cap hcf)⟩
  case fl => exact fun _ lf lf' hl => hF (FaultCorrG.cap (capFaultCorr_lookup _ hl))
  case repS =>
    intro s1 a1 σ' _ hXs hc
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J'⟩, hR', hW1⟩ := hXs
    have hct' : ct ∈ (Z.mv G1 V1).T := TopSR.cur_mem J'.xtop.fin.1 hc.symm
    refine WP.spec_mono (WP.spec_and (WP.spec_and (J'.flTailJSt hc call) (MKD.fl_tail L.total hA hKD hR'))
      (Mc.flTailProjWc J'.kern.heap J'.blk (J'.zH.1 ct hct') call)) ?_
    rintro res ⟨⟨⟨h1, z, hz, h2, h3⟩, h4⟩, h5⟩
    exact ⟨h1, z, hz, h2, JStab.mv h3, msF_mrT hMT h4 (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz)),
      hW1.projW_trans h5⟩
  case repF =>
    intro a1 e e' hX1 he
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J''⟩, hR', -⟩ := hX1
    have hFt : ((if call then do
          let s2 ← syscall.reply_error st s' ct e
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
        else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s', a1)) :
        Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
          P1.WritesIn st s' res.2.1 (Mc.ProjW (L := L) H Cs s') ⦄ := by
      cases call
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]; exact P1.WritesIn.refl _ _
      · simp only [↓reduceIte]
        exact WP.spec_bind (Mc.replyErrProjW J.kern.heap hblk hNB (J.zH.1 ct hctT) e) fun s2 h2 => (WP.spec_ok _).2 h2
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      ((J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJSt hcur call e e' he)
      (MKD.reply_err_tail (e := e) (t := ct) (s := s') (is_call := call) L.total hA hKD hR')) hFt) ?_
    rintro res ⟨⟨⟨h1, z, hz, h2, h3⟩, h4⟩, h5⟩
    exact ⟨h1, z, hz, h2, JStab.mv h3, msF_mrT hMT h4
      (congrArg Prod.fst (MachT.mtk_when (MachT.mtk_fl4ReplyFromKernelErrorG _ _ _) σb z hz)), h5⟩
  case pk => exact midPK J hcur bl call don
  case dec =>
    intro sl cp e exs hsl hc hget he hexs
    exact hD σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      hinfo hmi hbuf hbuffer hr2 her hmrs sl cp e exs hsl hc hget he hexs

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The invocation and `after_invocation` at a dispatch state** (`invoke_afterJ`'s shape). -/
theorem inv_afterSt {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σb : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) [VxE Z] {ct : U64}
    (hct : sched.cur_thread st s' = ok ct) {n : I64} {call bl don : Bool} (hn : InvSys n call bl don)
    (hInv : syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        call bl don false (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) res ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => SInvR.G5.DispPostSt (L := L) arI AR MR Z H Cs (invSysOf call bl) σb s' r ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σb.kheap σb.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have top : ∀ y, y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true call bl don false
      (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv)).run σb).1 →
      y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true (invSysOf call bl)).run σb).1 := fun y hy => by
    rw [fl4HandleSyscall_inv hn]; exact mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy
  have hok : ∀ {α : Type} {x : α} {P : α → Prop}, P x → ok x ⦃ P ⦄ := fun h => by rw [WP.spec_ok]; exact h
  refine WP.spec_bind hInv ?_
  rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, -, hXr⟩
  rcases hres with ⟨h1, hy1⟩ | ⟨h1, hy1⟩
  · dsimp only at h1 hXr; subst h1
    rw [if_neg (fun h => by cases h)] at hXr
    obtain ⟨⟨G1, V1, Ac1, Lst1, D1, J1⟩, hMm, hW1⟩ := hXr
    show (do
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    exact hok ⟨⟨y, top y hy, Or.inl ⟨hy1, ⟨G1, V1, Ac1, Lst1, D1, J1.toR⟩, hMm⟩⟩, hW1⟩
  · dsimp only at h1 hXr; subst h1
    rw [if_pos rfl] at hXr
    obtain ⟨-, hAI⟩ := hXr
    refine WP.spec_bind hAI ?_
    rintro ⟨b, s2, a2⟩ ⟨-, ⟨z, hz, hJz, hMz⟩, hW2⟩
    exact hok ⟨⟨y, top y hy, Or.inr ⟨hy1, z, hz, hJz, hMz⟩⟩, hW2⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **`dispatch_syscall` for the invoking class at a dispatch state** (`dispatch_invokeJ`'s
if-chain). -/
theorem dispatch_invSt {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σb : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) [VxE Z] {ct : U64}
    (hct : sched.cur_thread st s' = ok ct) {number : I64} {call bl don : Bool} (hn : InvSys number call bl don)
    (hInv : syscall.handle_invocation st arI s' a' call bl don false (L.mem s' (Endp.regA ct layout.reg.CAP)) ⦃ res =>
      HIPostMXP (L := L) (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') true σb
        call bl don false (Fl4Spec.toBl (L.mem s' (Endp.regA ct layout.reg.CAP)).bv) res ⦄) :
    syscall.dispatch_syscall st arI s' a' number ⦃ r =>
      SInvR.G5.DispPostSt (L := L) arI AR MR Z H Cs (invSysOf call bl) σb s' r ⦄ := by
  have h := inv_afterSt J hct hn hInv
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.REPLY) ?_
  rintro c1 -
  have n65 : fl4_abi.syscall.SysNBSend ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysNBSend fl4_abi.syscall.SysSend; decide
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_pos rfl]; exact h
  · rw [if_neg n65, if_pos rfl]; exact h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact h

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The invoking class of `DispStabFootAt` from `InvDecSt`** (module docstring). -/
theorem dispInv_stFt [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread) (hn : InvSys n call bl don)
    (hD : InvDecSt (L := L) arI AR MR Z H Cs s a σ n call bl don) :
    SInvR.G5.DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl) := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb
  have hct' := cur_thread_eq (L := L) s'
  generalize L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = ct at hct'
  exact dispatch_invSt J' hct' hn
    (invInvHI hA hnd hMT hKD hX hni hD σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb ct hct' hn)

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

/-- (p3J gen 35) **`DispStabFootLi` [J]**: `DispStabFootLn` with the invoking class reduced to its decode leaf
(module docstring). -/
structure DispStabFootLi (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class's decode leaf (`InvDecSt`), under `DispStabFootLn.inv`'s conditions. -/
  invDec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecSt (L := L) arI AR MR Z H Cs s a σ n call bl don
  /-- `DispStabFootLn.midDecRest`, verbatim. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStW (L := L) arI AR MR
          (fun cp => SInvCk.KW (absCap cp) ∧ ¬ IsReplyCap cp ∧ ¬ IsEasyCap cp ∧ ¬ IsEpCap cp) Z H Cs s a σ n c
  /-- `DispStabFootLn.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLn.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 35) **`DispStabFootLi → DispStabFootLn`** (module docstring). -/
theorem dispStabFootLn_of_Li [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLi (L := L) arI AR MR s a σ) :
    DispStabFootLn (L := L) arI AR MR s a σ where
  inv := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    haveI := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact dispInv_stFt hA hnd (MachPlatF.toT hM hIp) hKD hX hct hi
      (h.invDec hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := h.midDecRest
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLi` only** (`hLi` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLi [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLi : DispStabFootLi (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLn hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLn_of_Li hA hnd hM hIp hKD hLi)

end

end Fl4Proofs.P3.Mc
