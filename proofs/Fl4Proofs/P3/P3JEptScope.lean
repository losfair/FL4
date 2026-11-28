/-
P3 (p3J gen 48): **the last Thread label, `TCBSetEPTRoot` (88), out of the native top as a scope condition; the
decode fields of `DispStabFoot*` gone**. Architect ruling (option (a)): label 88 is a non-native extension label,
covered by the mmuAD / virt lines against the extension spec (`fl4DecodeInvocationV` + `VmEptState`; seam
P3JVtxBridge's `decodeV_eq_of_noVtx`); the native chain stays on the ported spec, which has no TCB label 88
(P3JVtxMR `specDec_ept_noOk`).

* **`thHard20_ept`**: `ThHard20 l → l = TCBSetEPTRoot` (every label 2–24 is excluded by `ThHard2` … `ThHard20`),
  so `IsRestCap29 cp l` is exactly "a Thread cap at label 88".
* **The mid class at Thread @ 88 is proved** (no scope needed): ReplyRecv / NBSendRecv / NBSendWait decode in the
  first phase, where FL4 (`syscall.rs` `decode_invocation`, `Cap::Thread` with `first_phase`) and the spec both
  return `InvalidCapability 0` with the state unchanged. **`decThEptMidSt`** (P3JThIll's `decThIllSt`, its
  first-phase branch, at label 88), **`midDecStWL29`**: `MidDecStWL` at `KW ∧ IsRestCap29`, unconditionally.
* **The invoking class at Thread @ 88** (Send / NBSend / Call, `fp = false`): FL4 `tcb.rs:410-420` returns
  `TruncatedMessage` when `extra[0]` is null, the ported spec `illegalOperation`; `ErrRel` does not relate them,
  so `XCapP` fails there and the field cannot be proved against the ported spec (**`specDec_ept_run`**: the spec's
  single outcome `illegalOperation`; **`not_xcapP_ept_trunc`**: wherever FL4's decode returns `TruncatedMessage`,
  `XCapP` fails for every `X`, `XP` — the FL4 run itself, `tcb.rs:411`, is read off the code, not proved). It is
  scoped out:
  **`KNo88` [S]** (below) makes `InvDecStWL` at `KW ∧ IsRestCap29` vacuous (**`invDecStWL29_of_no88`**).
* **`DispStabFootLzw` [J]** {midSpec, midRecvSw — `DispStabFootLzv`'s, verbatim}; **`dispStabFootLzv_of_Lzw`**
  (under `KNo88`), **`dispStabFootLzw_of_Lzv`** (unconditional); top **`kernel_entry_runMcWKR_sysLzw`**
  (globals verbatim as `_sysLzv`, plus `KNo88` [S]).

**Status (Architect ruling, gen 49): `KNo88` is transitional,
over-wide [S]; the proper native scope, via `LookAt`, excludes
only entries whose invoked slot holds a Thread cap with label = 88.** It is accepted as a transitional top premise.

**The scope condition, exactly.** `KNo88 s a σ` [S]: at every dispatch state of an entry from `(s, a, σ)` (every
`σb` with `BudgetAt σ σb true`, every `KFrontB` state `s'`, at every ghost set `Z` with `JAtZ Z … s a σ`), if the
current thread's message label is `TCBSetEPTRoot` (88), then no slot of a typed CNode of `Z` holds a Thread cap.
What it excludes, honestly:
* every invocation of a Thread cap with label 88 (the invoked slot is a typed CNode slot holding that cap), i.e.
  the calls the ruling scopes out;
* **and more**: every entry from a state whose current message label is 88 while some typed CNode slot holds a
  Thread cap, whatever cap is invoked and whichever syscall is entered (an endpoint `Send` with label 88, or a
  `Recv` whose message register happens to carry label 88). The extra exclusion is forced by the existing
  chain, not chosen: `InvDecStWL` / `MidDecStWL` (P3JScTop, the shape of every `DispStabFoot*` decode field since
  gen 32) quantify over **every** typed CNode slot `sl` with its cap `cp`, not only the invoked one (no `LookAt`
  antecedent, unlike JBootQ1Disp's `JPathAtMU44w`), so `DispStabFootLzv.invDecRest` asks `XCapP` at every
  Thread cap of every CNode whenever the message label is 88 — false at a label-88 message with no extra cap
  (the `TruncatedMessage` / `illegalOperation` mismatch above). Hence **`DispStabFootLzv` (and every earlier
  `DispStabFoot*`) is false at such states**; and the condition is per state, not per entry, because the
  `DispStabFoot*` fields are asked for every syscall number. Narrowing the exclusion to the ruling's (the invoked
  cap only, per entry) needs the decode fields re-stated with `LookAt ct cptr σb sl cp` and the consumers
  re-proved on P3JLook's `handle_invocation_refinesMXPL` — a re-statement of the chain (the collapse's job).
* Not vacuous: every state whose current message label is not 88 satisfies it (`kNo88_of_label`), as does every
  state whose typed CNodes hold no Thread cap.

Premise honesty: `DispStabFootLzw` is `DispStabFootLzv` without its two decode fields (implied by it,
`dispStabFootLzw_of_Lzv`); with `KNo88` it implies it (`dispStabFootLzv_of_Lzw`: the mid field proved, the
invoking field vacuous). `KNo88` is not implied by `DispStabFootLzv` (nor conversely).

Named premises: `DispStabFootLzw` [J], `KNo88` [S]; globals as `_sysLzv`. No sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JSspSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 48) **The Thread labels left after SetSchedParams are exactly `TCBSetEPTRoot`** (module docstring). -/
theorem thHard20_ept {l : U64} (h : ThHard20 l) : l = fl4_abi.label.TCBSetEPTRoot := by
  obtain ⟨h, n8⟩ := h
  obtain ⟨h, nI⟩ := h
  obtain ⟨h, n11⟩ := h
  obtain ⟨h, n22⟩ := h
  obtain ⟨h, n2⟩ := h
  obtain ⟨h, n17⟩ := h
  obtain ⟨h, n4⟩ := h
  obtain ⟨h, n3⟩ := h
  obtain ⟨h, n24⟩ := h
  obtain ⟨h, n13⟩ := h
  obtain ⟨h, n12⟩ := h
  obtain ⟨h, n6⟩ := h
  obtain ⟨h, n23⟩ := h
  obtain ⟨h, n21⟩ := h
  obtain ⟨h, n19⟩ := h
  obtain ⟨h, n14⟩ := h
  obtain ⟨h, nB⟩ := h
  obtain ⟨h, n7⟩ := h
  obtain ⟨h, nT⟩ := h
  rcases h with hr | he
  · exfalso
    have v : ∀ k : U64, l ≠ k → l.val ≠ k.val := fun k hk hv => hk (UScalar.eq_of_val_eq hv)
    have a8 := v _ n8
    have a9 := v _ (fun e => nI (Or.inl e))
    have a10 := v _ (fun e => nI (Or.inr (Or.inl e)))
    have a5 := v _ (fun e => nI (Or.inr (Or.inr e)))
    have a11 := v _ n11
    have a22 := v _ n22
    have a2 := v _ n2
    have a17 := v _ n17
    have a4 := v _ n4
    have a3 := v _ n3
    have a24 := v _ n24
    have a13 := v _ n13
    have a12 := v _ n12
    have a6 := v _ n6
    have a23 := v _ n23
    have a21 := v _ n21
    have a19 := v _ n19
    have a14 := v _ n14
    have a16 := v _ (fun e => nB (Or.inl e))
    have a18 := v _ (fun e => nB (Or.inr e))
    have a7 := v _ n7
    have a15 := v _ (fun e => nT (Or.inl e))
    have a20 := v _ (fun e => nT (Or.inr e))
    simp [fl4_abi.label.TCBSetSchedParams, fl4_abi.label.TCBSetTimeoutEndpoint, fl4_abi.label.TCBSetIPCBuffer,
      fl4_abi.label.TCBConfigure, fl4_abi.label.TCBSetSpace, fl4_abi.label.TCBWriteFPU,
      fl4_abi.label.TCBReadRegisters, fl4_abi.label.TCBGetBreakpoint, fl4_abi.label.TCBCopyRegisters,
      fl4_abi.label.TCBWriteRegisters, fl4_abi.label.TCBSetTimer, fl4_abi.label.TCBResume,
      fl4_abi.label.TCBSuspend, fl4_abi.label.TCBSetPriority, fl4_abi.label.TCBReadFPU,
      fl4_abi.label.TCBSetFlags, fl4_abi.label.TCBConfigureSingleStepping,
      fl4_abi.label.TCBBindNotification, fl4_abi.label.TCBSetBreakpoint, fl4_abi.label.TCBUnsetBreakpoint,
      fl4_abi.label.TCBSetMCPriority, fl4_abi.label.TCBUnbindNotification, fl4_abi.label.TCBSetTLSBase]
      at a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    omega
  · exact he

/-- (p3J gen 48) **The ported spec's decode of a Thread cap at label 88, second phase**: the single outcome
`illegalOperation`, the state unchanged (no TCB label 88; as XTopTcb's `tcb_illegalX`'s spec half). -/
theorem specDec_ept_run (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (p : U64)
    (σ : Fl4Spec.State Unit) :
    (specDec false fl4_abi.label.TCBSetEPTRoot.bv args ci sl (.Thread p) excaps buffer).run σ =
      ({(.error .illegalOperation, σ)}, False) := by
  obtain ⟨sl', hg, hx, hd⟩ := tcb_canon fl4_abi.label.TCBSetEPTRoot
  obtain ⟨-, -, hti, hte⟩ := tcb_out fl4_abi.label.TCBSetEPTRoot (by rw [lbl_ept_val]; omega)
  rw [hti] at hg
  have hx' := hx hg
  rw [hte] at hx'
  rw [specDec_thread p hd]
  show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) sl' args (.threadCap p.bv) sl excaps buffer).run σ = _
  rw [fl4DecodeTcb_spec' (by rw [hg]; decide) hx']
  apply run_liftME_err
  unfold Fl4Spec.decodeTcbInvocation
  rw [hg]
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (p3J gen 48) **Remark (falsity, module docstring)**: wherever FL4's decode of a Thread cap at label 88 in the
second phase returns `TruncatedMessage` (`tcb.rs:411`, `extra[0]` null), `XCapP` there fails for every `X`, `XP`:
the spec's only outcome is `illegalOperation` (`specDec_ept_run`), which `ErrRel` does not relate to
`TruncatedMessage`. So the invoking class's decode field at Thread @ 88 is not provable against the ported spec. -/
theorem not_xcapP_ept_trunc {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {length slot : U64} {p : U64} {blk call don : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {ct : U64} {s1 : S} {a1 : A}
    (hd : syscall.decode_invocation st arI s ar fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don
      false buf extra = ok (.Err (.Sys .TruncatedMessage), s1, a1)) :
    ¬ XCapP (L := L) arI X XP s ar σ fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don false buf
      extra fl4_abi.label.TCBSetEPTRoot.bv args ci sl excaps buffer ct := by
  have hrun := specDec_ept_run args ci sl excaps buffer p σ
  have herr : ∀ e e', (.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc) = .Err e →
      (specDec false fl4_abi.label.TCBSetEPTRoot.bv args ci sl (.Thread p) excaps buffer).run σ =
        ({(.error e', σ)}, False) → ¬ ErrRel e e' := by
    intro e e' he hr hrel
    cases he
    rw [hrun] at hr
    have h1 := (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hr))
    cases h1
    rcases hrel with h | ⟨n, h1, -⟩
    · simp [SysErrRel] at h
    · cases h1
  have hnok : ∀ inv, ¬ DecOut (specDec false fl4_abi.label.TCBSetEPTRoot.bv args ci sl (.Thread p) excaps buffer)
      σ inv := by
    intro inv hdo
    have hm := hdo.1
    rw [hrun] at hm
    cases (Set.mem_singleton_iff.1 hm)
  intro h
  rcases h with h | h
  · have h' := spec_ok_post h hd
    unfold TopPostDMXP TopPostDMX at h'
    rcases h' with ⟨e, he, -, ⟨e', hr, hrel⟩, -⟩ | ⟨inv, hdo, -⟩
    · exact herr e e' he hr hrel
    · exact hnok inv hdo
  · have h' := spec_ok_post h hd
    unfold TopPostRMX at h'
    rcases h' with ⟨e, he, -, ⟨e', hr, hrel⟩, -⟩ | ⟨hok, -⟩
    · exact herr e e' he hr hrel
    · cases hok

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 48) **The Thread cap's first-phase decode at a dispatch state at `TCBSetEPTRoot`** (module docstring):
FL4 and the spec both return `InvalidCapability 0`, the state unchanged (P3JThIll's `decThIllSt`, first-phase
branch). -/
theorem decThEptMidSt [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb)
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
    (sl : Fl4Spec.CslotPtr) {p : U64}
    (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hl : info.label = fl4_abi.label.TCBSetEPTRoot) (args : List Fl4Spec.Data) (bl call don : Bool)
    (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don true buf e mi.miLabel
      args ci sl exs buffer ct := by
  have h88 : info.label.val = 88 := by rw [hl]; exact lbl_ept_val
  have hX0 : (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s')) ∧ MR a' σb.machineState :=
    ⟨⟨J.stab, P1.WritesIn.refl _ _⟩, hMb⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  rw [← hLb]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon info.label
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  have hl5 : info.label.val ≠ 5 ∧ info.label.val ≠ 8 ∧ info.label.val ≠ 9 ∧ info.label.val ≠ 10 ∧
      info.label.val ≠ 11 := ⟨by omega, by omega, by omega, by omega, by omega⟩
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  simp only [↓reduceIte]
  rw [WP.spec_ok]
  exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 48) **`MidDecStWL` at `KW ∧ IsRestCap29`, proved** (module docstring: the mid class at Thread @ 88
is a first-phase error on both sides). -/
theorem midDecStWL29 [VxE Z] {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, hW⟩ := hW
  cases cp
  case Thread p => exact decThEptMidSt J hMb hct a1 a2 a3 a4 a5 a6 sl e exs (thHard20_ept hW) _ _ _ _ _
  all_goals exact False.elim hW

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

/-- (p3J gen 48) **`KNo88` [S]: label 88 (`TCBSetEPTRoot`, a non-native extension label) is out of the native
top's scope** (module docstring, which states exactly what it excludes): at every dispatch state of an entry, if
the current thread's message label is 88, no slot of a typed CNode holds a Thread cap. (p3J gen 49, Architect
ruling) transitional, over-wide [S]; the proper native scope, via `LookAt`, excludes
only entries whose invoked slot holds a Thread cap with label = 88. -/
def KNo88 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
    ∀ (ct : U64) (info : msginfo.MessageInfo), sched.cur_thread st s' = ok ct → msg.msg_info st s' ct = ok info →
      info.label = fl4_abi.label.TCBSetEPTRoot →
      ∀ (sl : Fl4Spec.CslotPtr) (p : U64), (∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length)) →
        capAt (L.mem s') (cslotAddr sl) ≠ ok (.Thread p)

/-- (p3J gen 48) **`DispStabFootLzw` [J]**: `DispStabFootLzv` without its decode fields (module docstring). -/
structure DispStabFootLzw (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzv.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzv.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 48) **Not vacuous**: a state whose current message label at every dispatch state is not 88
satisfies `KNo88`. -/
theorem kNo88_of_label {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
      ∀ (ct : U64) (info : msginfo.MessageInfo), sched.cur_thread st s' = ok ct →
        msg.msg_info st s' ct = ok info → info.label ≠ fl4_abi.label.TCBSetEPTRoot) :
    KNo88 (L := L) arI AR s a σ := by
  intro Z H Cs Ac Lst D _ σb hBA s' a' hKF ct info hct hinfo hl
  exact absurd hl (h σb hBA s' a' hKF ct info hct hinfo)

/-- (p3J gen 48) **`InvDecStWL` at `KW ∧ IsRestCap29` is vacuous under `KNo88`** (module docstring). -/
theorem invDecStWL29_of_no88 {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : KNo88 (L := L) arI AR s a σ) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap29 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, hW⟩ := hW
  cases cp
  case Thread p =>
    exact absurd hc (hN Z H Cs Ac Lst D J0 σb hBA s' a' hKF ct info hct a1 (thHard20_ept hW) sl p hsl)
  all_goals exact False.elim hW

/-- (p3J gen 48) **`DispStabFootLzw → DispStabFootLzv`** under `KNo88` (module docstring). -/
theorem dispStabFootLzv_of_Lzw {s : S} {a : A} {σ : Fl4Spec.State Unit} (hN : KNo88 (L := L) arI AR s a σ)
    (h : DispStabFootLzw (L := L) arI AR MR s a σ) : DispStabFootLzv (L := L) arI AR MR s a σ where
  invDecRest := fun _ _ _ _ _ _ _ J _ _ _ _ _ _ _ _ _ => invDecStWL29_of_no88 J hN
  midDecRest := fun _ _ _ _ _ _ _ _ hV _ _ _ _ _ _ => by
    haveI := hV
    exact midDecStWL29
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 48) **`DispStabFootLzv → DispStabFootLzw`** (the honesty claim: `DispStabFootLzw` is implied). -/
theorem dispStabFootLzw_of_Lzv {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzv (L := L) arI AR MR s a σ) : DispStabFootLzw (L := L) arI AR MR s a σ :=
  ⟨h.midSpec, h.midRecvSw⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 48) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with label 88 scoped out (`hNo` [S]) and
`DispStabFootLzw` only** (`hLzw` [J]; globals verbatim as `_sysLzv`; module docstring). (p3J gen 49, Architect
ruling) `hNo : KNo88` is transitional, over-wide [S]; the proper native scope, via `LookAt`, excludes
only entries whose invoked slot holds a Thread cap with label = 88. -/
theorem kernel_entry_runMcWKR_sysLzw [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hNo : KNo88 (L := L) arI AR s a σ)
    (hLzw : DispStabFootLzw (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzv hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzv_of_Lzw hNo hLzw)

end

end Fl4Proofs.P3.Mc
