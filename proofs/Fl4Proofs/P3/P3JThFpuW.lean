/-
P3 (p3J gen 40): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at WriteFPU (23), for
both classes**; the rest set {CNode at Revoke / Delete, Thread at 2–24 other than 7 / 14 / 15 / 16 / 18 / 19 / 20 /
21 / 23, or SetEPTRoot}.

* `JAtZ.copyFpuProjW`: the copy into a thread's FPU image (`tcb.copy_words` to offset 512, 337 words, so below
  3208 < 4096) writes only `ProjW` (`copy_words_inv`, `tcbWordProjW`).
* **`tcb_write_fpuJSt`**: XTopJointTcb's `tcb_write_fpuJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts: XTopTcbFpu's `fpu_refinesX` at that `X`; the restart by `stsProjW`, the copy
  by `copyFpuProjW`; `fpu_flush` / `fpu_sanitise` / `fpu_reload` touch only the arch state).
* **`decThFpuWSt`** (any flags): the dispatch leaf. Its inputs of the non-stable chain are derived at the dispatch
  state: `XcRel` by `ExtraOK.xc`, the arguments by `JAtZ.argsJ`; `ARKeep` [P] from the tops' `ARIface`.
* `ThHard8 l`: `ThHard7 l ∧ l ≠ TCBWriteFPU`. `IsRestCap16`. `restCap15_of16`, `restCap16_of`.
  **`midDecRest15_of_fpuw`** / **`invDecRest15_of_fpuw`**, `midDecStWL_of_15` / `invDecStWL_of_15`.
* **`DispStabFootLzi` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap16`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzh_of_Lzi`** (under the tops' platform facts), **`dispStabFootLzi_of_Lzh`**; top
  **`kernel_entry_runMcWKR_sysLzi`** (globals verbatim as `_sysLzh`).

Premise honesty: `DispStabFootLzi`'s decode fields are `DispStabFootLzh`'s at the smaller antecedent
(`IsRestCap16 → IsRestCap15`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzi` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThFlg
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 40) **The copy into a thread's FPU image writes only `ProjW`** (module docstring). -/
theorem JAtZ.copyFpuProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (src : U64) :
    tcb.copy_words st s src (core.num.U64.wrapping_add t layout.tcb.FPU) 337#u64 ⦃ s' =>
      P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hpf := (J.ip.e.tcb t ht).fits
  have hfpu : (core.num.U64.wrapping_add t layout.tcb.FPU).val = t.val + 512 := by
    unfold layout.tcb.FPU
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine copy_words_inv (fun s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s)) s src _ _
    (P1.WritesIn.refl _ _) ?_
  rintro s2 i W hi v
  have hiv : (core.num.U64.wrapping_mul i 8#u64).val = 8 * i.val := by
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    have : i.val < 337 := hi
    omega
  have hi' : i.val < 337 := hi
  refine W.projW_trans (J.tcbWordProjW ht (Kv := 512 + 8 * i.val) ⟨by omega, by omega⟩ ?_ s2 v)
  have h1 : (core.num.U64.wrapping_add t layout.tcb.FPU).val + (core.num.U64.wrapping_mul i 8#u64).val < 2 ^ 64 := by
    rw [hfpu, hiv]; omega
  clear h1
  unfold layout.tcb.FPU
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

set_option maxHeartbeats 8000000 in
/-- (p3J gen 40) **WriteFPU at stable ghosts, with its `ProjW` footprint** (XTopJointTcb's `tcb_write_fpuJ`;
module docstring). -/
theorem tcb_write_fpuJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (hK : ARKeep arI AR) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .writeFpu)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBWriteFPU p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, J.del, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) false (args.map UScalar.bv) p.bv excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [(decode_fpu_eq arI s ar p _ hstall).2, hdec0]
  refine fpu_refinesX arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s))
    (fun _ _ _ ⟨⟨_, _, _, _, _, J'⟩, _⟩ => ⟨_, J'.xtop⟩) Z.th hX.rel.1
    s ar σ Z.G hDS hX.rel.2.2.2.2.1 p false length buf ct hct args hlen hargs hcur htcb J.kern.act call slot extra
    x0 x1 x2 hx0 excaps hXc ⟨J.stab, P1.WritesIn.refl _ _⟩ blk don ?_
  intro s1 σ1 x ptr offset r asid va m ep sz hs1 hst1 hx hxn hl ho hc hpass
  obtain ⟨s1', σ1', -, hrc1, hst1', -, -, -, -, -, -, hs1', Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1' (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J (J.thT ct htcb) sched.TS_RESTART
    rw [hs1', WP.spec_ok] at h; exact h
  have e1 : s1' = s1 := by
    have := hs1'.symm.trans hs1
    simpa using this
  have e2 : σ1' = σ1 := by
    rw [hcur] at hst1'
    have h := (Prod.mk.inj (hst1'.symm.trans hst1)).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 h)
  subst e1 e2
  have hAR1 := J1.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨hr1, hr3, hm, hlt, hrm⟩ := hpass
  have hvk : capability.VM_KERNEL_ONLY = 1#u64 := by simp only [capability.VM_KERNEL_ONLY]
  have hvrw : capability.VM_READ_WRITE = 3#u64 := by simp only [capability.VM_READ_WRITE]
  obtain ⟨z, hzv, hzf⟩ := fshift_eq sz
  have hge : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 := by scalar_tac
  have hsz : fl4_abi.consts.FPU_STATE_SIZE + 7#u64 = ok 2703#u64 := by
    unfold fl4_abi.consts.FPU_STATE_SIZE
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.add_spec (x := 2696#u64) (y := 7#u64) (by scalar_tac))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  have hwd : (2703#u64 : U64) / 8#u64 = ok 337#u64 := by
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.div_spec (x := 2703#u64) (y := 8#u64) (by decide))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  unfold tcb.fpu_transfer
  rw [extra_eq _ 0#usize (by decide) hx]
  simp only [hxn, ↓reduceIte, hge, bind_ok]
  rw [ho]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]; simp only [bind_ok, hvk, hvrw, hzf]
  simp only [Bool.false_eq_true, ↓reduceIte, hr1]
  have hp' : offset.val % 64 = 0 ∧ offset.val < z.val ∧ 2696 ≤ z.val - offset.val := by
    unfold FpuPass.fl4Spec_fpu Fl4Spec.fl4FpuStateSize at hrm
    exact ⟨hm, hzv ▸ hlt, hzv ▸ hrm⟩
  rw [off_pass _ _ offset z hp']
  rw [hrc1]; simp only [bind_ok]
  refine WP.spec_bind (hK.fpu_flush ar p _ hAR1) fun a1 ha1 => ?_
  simp only [hsz, hwd, bind_ok, lift, obj.Tcb.fpu_addr]
  refine WP.spec_bind (WP.spec_and ((J1.archJ ha1).copyFpuJ hpT _) (J1.copyFpuProjW hpT _)) ?_
  rintro s2 ⟨⟨V2, J2⟩, W2⟩
  try simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (hK.fpu_sanitise a1 p _ ha1) fun a2 ha2 => ?_
  refine WP.spec_bind (hK.fpu_reload a2 p _ ha2) fun a3 ha3 => ?_
  exact (WP.spec_ok _).2 ⟨rfl, σ1', rfl, ⟨_, _, Ac1, Lst1, D1, J2.archJ ha3⟩, W1.projW_trans W2⟩

end

/-- (p3J gen 40) The Thread labels left after WriteFPU. -/
def ThHard8 (l : U64) : Prop := ThHard7 l ∧ l ≠ fl4_abi.label.TCBWriteFPU

/-- (p3J gen 40) The caps left after the WriteFPU leaf, with the message label. -/
def IsRestCap16 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard8 l
  | _, _ => False

theorem restCap15_of16 {cp : capability.Cap} {l : U64} (h : IsRestCap16 cp l) : IsRestCap15 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap16_of {cp : capability.Cap} {l : U64} (h : IsRestCap15 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBWriteFPU) : IsRestCap16 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem fpuw_nonIns : TcbNonIns fl4_abi.label.TCBWriteFPU := by
  unfold TcbNonIns fl4_abi.label.TCBWriteFPU fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The Thread cap's decode at a dispatch state at WriteFPU, any flags** (module
docstring). -/
theorem decThFpuWSt (hA : P0.ArchTotal arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) (hK : ARKeep arI AR)
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
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBWriteFPU) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  have hXc := ExtraOK.xc J.xtop.rel.1 (hXO e exs he hexs)
  rw [hl]
  obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon fl4_abi.label.TCBWriteFPU
  have hl5 : fl4_abi.label.TCBWriteFPU.val ≠ 5 ∧
      fl4_abi.label.TCBWriteFPU.val ≠ 8 ∧
      fl4_abi.label.TCBWriteFPU.val ≠ 9 ∧ fl4_abi.label.TCBWriteFPU.val ≠ 10 ∧
      fl4_abi.label.TCBWriteFPU.val ≠ 11 := by simp [fl4_abi.label.TCBWriteFPU]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine Fl4Proofs.P3.XCapP.mrG (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD fpuw_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hg, he'⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .writeFpu by
      simp [tcbExtOf])
    exact tcb_write_fpuJSt s' a' σb J hnib hK p hpT sl' hg he' _ buf ct hct argsU hLen hArgs (J.stallT p hpT)
      call _ e (exAt e 0) (exAt e 1) (exAt e 2) (exAt_idx0 e) exs hXc bl don ci sl buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`MidDecStWL` at `KW ∧ IsRestCap15` from the WriteFPU leaf** (module docstring). -/
theorem midDecRest15_of_fpuw (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hK : ARKeep arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBWriteFPU
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFpuWSt hA hMT hKD hK J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap16_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **`InvDecStWL` at `KW ∧ IsRestCap15` from the WriteFPU leaf** (module docstring). -/
theorem invDecRest15_of_fpuw (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hK : ARKeep arI AR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBWriteFPU
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThFpuWSt hA hMT hKD hK J hnib hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap16_of hW.2 hS⟩

/-- (p3J gen 40) `MidDecStWL` at `KW ∧ IsRestCap15` gives it at `KW ∧ IsRestCap16` (antitone). -/
theorem midDecStWL_of_15 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap15_of16 hW.2⟩

/-- (p3J gen 40) `InvDecStWL` at `KW ∧ IsRestCap15` gives it at `KW ∧ IsRestCap16` (antitone). -/
theorem invDecStWL_of_15 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap15 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap15_of16 hW.2⟩

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

/-- (p3J gen 40) **`DispStabFootLzi` [J]**: `DispStabFootLzh` with `invDecRest` / `midDecRest` restricted to the
CNode caps at Revoke / Delete and the Thread caps at the TCB invocations (2–24) other than SetMCPriority /
Bind- and UnbindNotification / Set- and UnsetBreakpoint / ConfigureSingleStepping / SetTLSBase / SetFlags /
WriteFPU, or SetEPTRoot
(module docstring). -/
structure DispStabFootLzi (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzh.invDecRest` at `KW ∧ IsRestCap16`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzh.midDecRest` at `KW ∧ IsRestCap16`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap16 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzh.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzh.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 40) **`DispStabFootLzi → DispStabFootLzh`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzh_of_Lzi (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzi (L := L) arI AR MR s a σ) :
    DispStabFootLzh (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest15_of_fpuw hA hnd (MachPlatF.toT hM hIp) hKD hARI.toARKeep hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest15_of_fpuw hA hnd (MachPlatF.toT hM hIp) hKD hARI.toARKeep hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 40) **`DispStabFootLzh → DispStabFootLzi`** (the honesty claim: `DispStabFootLzi` is implied). -/
theorem dispStabFootLzi_of_Lzh {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzh (L := L) arI AR MR s a σ) : DispStabFootLzi (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_15 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_15 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 40) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzi` only** (`hLzi` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzi [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzi : DispStabFootLzi (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzh hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzh_of_Lzi hARI hA hnd hM hIp hKD hLzi)

end

end Fl4Proofs.P3.Mc
