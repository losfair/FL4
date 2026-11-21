/-
P3 (DESIGN.md §9), IO ports: **the IO port cap with `JAt` after, every
label** (XTopJointStep's per-op premise `JPostHyp` narrowed, at `In`, to the
reply step `JReplyHyp`).

* `JReplyHyp` (proved: XTopJointReply's `jReplyHyp`): from `JAtZ` at a state whose current thread is
  `Restart`, FL4's `vspace::reply1` (the reply registers, when called, and
  `set_thread_state Running`) against the spec's success tail (`specTail`),
  `JAt` at every outcome related by `XTop` (l4v: `reply_from_kernel` and
  `set_thread_state Running` keep the invariants; the step-level shape of
  CSpace's `JStepHyps.restart`).
* `portInTail_jat`: `In`'s tail (XTopPortIn's `portInTail_xtop`) at `JAt`:
  the restart and the port access as primitive steps (`stepClosed_jat`,
  `JStepHyps`), `reply1` by VSpace's `reply1_invT` with `XTop` rebuilt, then
  `JReplyHyp`.
* `decode_invocation_ioport_inJ`: the `In` labels' `DecOKRMX` at `JAt` (as
  `decode_invocation_ioport_inX`, the decode errors at the start's `JAtZ`).
* `decode_invocation_ioportJ_steps` (moved here from XTopJointStep): every
  label of the IO port cap at `JAt`; `Out`, the errors and the other labels
  by their primitive steps, `In` by `decode_invocation_ioport_inJ`.
-/
import Fl4Proofs.P3.XTopJointStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The reply step at `J`** (module docstring); proved by XTopJointReply's
`jReplyHyp`. -/
def JReplyHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (ct : U64) (x : Fl4Spec.Tcb) (call : Bool) (v : U64), σ.curThread = ct.bv →
      σ.kheap ct.bv = some (.tcb x) → x.tcbState = .restart →
      ∀ (s2 : S) (z : Unit × Fl4Spec.State Unit), vspace.reply1 st s ct call v = ok s2 →
        z ∈ (specTail call ct.bv [v.bv] σ).1 → XTop (L := L) AR s2 a z.2 → JAt (L := L) arI AR s2 a z.2

set_option maxHeartbeats 8000000 in
/-- **The `In` tail at `JAt`** (module docstring). -/
theorem portInTail_jat (hAM : ARMask arI AR) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hRep : JReplyHyp (L := L) arI AR Z.th) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (port z : U64) (call : Bool)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (hval : call = true → PortInVal arI) :
    portInTail (st := st) arI s ar ct port z call ⦃ res => res.1 = .Ok () ∧
      L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧ ∀ σ1,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
          (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData z.val)))).run σ1).1 ∧
        ∃ w ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) res.2.1 w.2 ∧
          JAt (L := L) arI AR res.2.1 res.2.2 w.2 ⦄ := by
  have hX := J.xtop
  obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
  set σ1 := Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv with hσ1
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) :=
    Notif.setThreadState_eq .restart hk
  unfold portInTail
  have hts := WP.spec_and (set_thread_state_cpu (L := L) s ct sched.TS_RESTART)
    (spec_self (set_thread_state_cpu (L := L) s ct sched.TS_RESTART))
  refine WP.spec_bind hts ?_
  rintro s1 ⟨⟨hk1, hc1⟩, hr1⟩
  obtain ⟨v, a1, hv⟩ := hin ar port z
  rw [hv]; simp only [bind_ok]
  -- the spec's `In`
  obtain ⟨rr, ms, hu, hmem, hrr⟩ : ∃ rr, ∃ ms : Fl4Spec.MachineState,
      ms.underlyingMemory = σ1.machineState.underlyingMemory ∧
      (.ok rr, { σ1 with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val) (inData z.val)))).run σ1).1 ∧
      specTail call ct.bv rr { σ1 with machineState := ms } =
        specTail call ct.bv [v.bv] { σ1 with machineState := ms } := by
    cases call
    · obtain ⟨r, ms, hu, hmem⟩ := port_in_perform σ1 (BitVec.ofNat 16 port.val) z.val
      refine ⟨[r], ms, hu, hmem, ?_⟩
      have hky : ({ σ1 with machineState := ms } : Fl4Spec.State Unit).kheap ct.bv =
          some (.tcb { x with tcbState := .restart }) := by
        show σ1.kheap ct.bv = _; rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
      rw [specTail_restart hky rfl false r, specTail_restart hky rfl false v.bv]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · obtain ⟨ms, hu, hmem⟩ := hval rfl ar a1 port z v hv σ1
      exact ⟨[v.bv], ms, hu, hmem, rfl⟩
  set σy : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσy
  -- the restart and the access, as primitive steps
  have hstp : Steps (L := L) arI Z.th s ar σ s1 a1 σy :=
    ((Steps.restart arI hcur hk htcb hr1 (by rw [hcur]; exact hst) hC).trans arI
      (Steps.ksSpec arI (s := s1) (σ := σ1) (σ' := σy) (by constructor <;> first | rfl | exact hu) rfl rfl
        (fun h => ⟨h.st, h.node⟩) (fun h => h))).trans arI
      (Steps.arch arI (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨port, z, v, hv⟩))))))
  obtain ⟨G', V', Ac', Lst', D', J', -⟩ := hstp _ (stepClosed_jat arI hAM hJS) Z H Cs Ac Lst D rfl J hZB
  -- `reply1`
  set Z' : XSets := Z.mv G' V'
  have hXy := J'.xtop
  have hI : Vs.RInv (L := L) Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 Z'.N Z'.T Z'.C Z'.E Z'.R Z'.B Z'.c AR Z'.G s1 a1 σy :=
    ⟨hXy.rel.2.1, hXy.rel.2.2.1, hXy.rel.2.2.2.2.1, hXy.rel.2.2.2.1, hXy.fin⟩
  have hkY : σy.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    show σ1.kheap ct.bv = _; rw [hσ1, Notif.stsAct_kheap, Notif.updK_kheap, Function.update_self]
  have hcurY : ct.bv = σy.curThread := by
    show ct.bv = σ1.curThread; rw [hσ1, stsAct_cur]; exact hcur.symm
  have hR1 := Vs.reply1_invT s1 a1 σy hI ct htcb hcurY hkY rfl J'.kern.act call v
  refine spec_bind_assoc (WP.spec_and hR1 (spec_self hR1)) ?_
  rintro s3 ⟨⟨hne, hks3, w, hw, hI3, hz3⟩, heq⟩
  rw [WP.spec_ok]
  refine ⟨rfl, hne, fun σ1' hσ1' => ?_⟩
  have e : σ1' = σ1 := by
    rw [hst] at hσ1'
    exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hσ1'))).2).symm
  subst e
  have hSch := hI3.2.2.2.2.1.1.1
  have hXT : XTop (L := L) AR s3 a1 w.2 := ⟨Z', hI3.2.2.2.2, ⟨hXy.rel.1, hI3.1, hI3.2.1,
    hI3.2.2.2.1, hI3.2.2.1, by rw [hks3]; exact hXy.rel.2.2.2.2.2.1, hXy.rel.2.2.2.2.2.2.mono hz3⟩,
    IpcRel.of hI3.2.2.2.2.1.1.2.2.1 hI3.2.2.2.2.1.1.2.1 (sched_sc hSch), hXy.esa.mono hks3 hz3⟩
  refine ⟨rr, σy, hmem, w, by rw [hrr]; exact hw, hI3.relTop, ?_⟩
  exact hRep Z' H Cs Ac' Lst' D' s1 a1 σy rfl J' ct _ call v hcurY.symm hkY rfl s3 w heq hw hXT

set_option maxHeartbeats 8000000 in
/-- **IOPort `In`** (labels 64..66, any `call`) at `JAt`: the replying shape
(`DecOKRMX`), from `portInTail_jat` (as `decode_invocation_ioport_inX`). -/
theorem decode_invocation_ioport_inJ (hAM : ARMask arI AR) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hRep : JReplyHyp (L := L) arI AR Z.th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s)) (lbl : U64) (hl : 64 ≤ lbl.val ∧ lbl.val ≤ 66)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl)))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536)
    (hC : CurRun σ)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a')) (call : Bool)
    (hval : call = true → PortInVal arI)
    (slot : U64) (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKRMX (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.IoPort first last 0#u64) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hsz : portSz lbl = 1 ∨ portSz lbl = 2 ∨ portSz lbl = 4 := by unfold portSz; split_ifs <;> simp
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.IoPort first last 0#u64) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec
        (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
          (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)))) := rfl
  rw [hspec, decode_in_eq slbl _ _ hsz hlbl]
  unfold ioport.decode
  simp only
  rw [hct, port_size_eq lbl ⟨hl.1, by omega⟩, is_port_in_eq lbl ⟨hl.1, by omega⟩]
  simp only [bind_ok]
  have hszU : (if lbl.val = 64 ∨ lbl.val = 67 then 1#u64 else if lbl.val = 65 ∨ lbl.val = 68 then 2#u64
      else 4#u64) = ⟨BitVec.ofNat 64 (portSz lbl)⟩ := by
    unfold portSz; split_ifs <;> rfl
  rw [hszU]
  have hsz0 : ¬ (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64) = 0#u64 := by
    rw [u64_eq_iff]; show ¬ (BitVec.ofNat 64 (portSz lbl)).toNat = 0
    rcases hsz with h | h | h <;> rw [h] <;> decide
  rw [if_neg hsz0, decide_eq_true (by omega : lbl.val ≤ 66)]
  simp only [↓reduceIte]
  -- the argument
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, run_liftME_err (run_liftME_err ?_), Or.inl trivial⟩, hJ0⟩
    unfold Fl4Spec.argsAtLeast
    rw [whenE_pos (show 1 > (args.map UScalar.bv).length by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), lift, bind_ok]
  unfold Fl4Spec.argsAtLeast
  rw [whenE_neg (show ¬ 1 > ((y0 :: rest).map UScalar.bv).length by simp), retOk_bind, retOk_bind]
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  have g0 : (y0.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  rw [hmap, g0, the_some]
  set port := y0 &&& 65535#u64 with hport
  have hpv : port.val < 65536 := by rw [hport, and_ffff]; omega
  have hp16 : (Fl4Spec.ucast 16 y0.bv : BitVec 16) = BitVec.ofNat 16 port.val := by
    apply BitVec.eq_of_toNat_eq; rw [ucast16_toNat, BitVec.toNat_ofNat, hport, and_ffff]; omega
  rw [hp16]
  have hszv : (⟨BitVec.ofNat 64 (portSz lbl)⟩ : U64).val = portSz lbl := by
    show (BitVec.ofNat 64 (portSz lbl)).toNat = _
    rw [BitVec.toNat_ofNat]; rcases hsz with h | h | h <;> rw [h]
  rw [allowed_eq first last port _ hl16 hpv (by rw [hszv]; exact hsz)]
  simp only [hszv, bind_ok]
  have hens := ensure_run first last hfl hl16 port hpv hsz σ
  by_cases hc : port.val < first.val ∨ port.val + portSz lbl - 1 > last.val
  · rw [if_pos hc]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok]
    rw [if_pos hc] at hens
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err (run_liftME_err (run_bind_error hens _)),
      Or.inl trivial⟩, hJ0⟩
  rw [if_neg hc]
  rw [if_neg hc] at hens
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_mono (portInTail_jat arI hAM hJS hRep J hZB hC hcur port ⟨BitVec.ofNat 64 (portSz lbl)⟩
    call hin hval) ?_
  rintro res ⟨hres, hne, hall⟩
  obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
  have hst : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)}, False) :=
    Notif.setThreadState_eq .restart hk
  obtain ⟨rr, σy, hy, z, hz, hRT, hXT⟩ := hall _ hst
  rw [hszv] at hy
  refine Or.inr ⟨hres, hne, .invokeArchObject (.spec (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 port.val)
    (inData (portSz lbl))))), ?_, _, by rw [hcur]; exact hst, rr, σy, hy, z, hz, hRT, hXT⟩
  exact DecOut.of_eq (run_liftME_ok (run_liftME_ok ((run_bind_ok hens _).trans rfl)))

set_option maxHeartbeats 4000000 in
/-- **An IO port cap, `JAt` after, every label**: `Out`, the errors and the
other labels by their primitive steps (`decode_invocation_ioportXS`,
`Steps.jat` with `JStepHyps`), `In` (64..66, whose reply writes the caller's
message words) by `decode_invocation_ioport_inJ` from `JReplyHyp` [J]. -/
theorem decode_invocation_ioportJ_steps [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) (hJ : JStepHyps (L := L) arI AR Z.th)
    (hRep : JReplyHyp (L := L) arI AR Z.th) (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (first last : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .IoPort first last 0#u64) (call : Bool)
    (hval : call = true → PortInVal arI)
    (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨⟨-, hl, hfl⟩, -⟩ := slot_cap_wf hX hAs hsc
  have hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a') := by
    intro a p z
    obtain ⟨⟨v, a'⟩, h, -⟩ := spec_exists (hT.port_in a p z)
    exact ⟨v, a', h⟩
  have hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a' := by
    intro a p z d
    obtain ⟨a', h, -⟩ := spec_exists (hT.port_out a p z d)
    exact ⟨a', h⟩
  exact decode_invocation_ioportXS arI Z.th hX.rel.1 s ar σ lbl slbl hlbl length buf ct hct args hlen hargs hcur
    (hX.curTcb hcur).1 J.kern.act first last hfl (by simpa using hl) call hout rfl hX (J.curRun.run hni)
    ⟨Z, H, Cs, Ac, Lst, D, J⟩ (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J hZB) (fun _ _ _ h => JAt.xtop arI h)
    (cslotAddr sl) blk don fp extra ci sl excaps buffer
    (fun hI => Or.inr (decode_invocation_ioport_inJ arI hARI.toMask hJ hRep s ar σ J hZB lbl hI slbl (hlbl.1 hI) length
      buf ct hct args hlen hargs hcur first last hfl (by simpa using hl) (J.curRun.run hni) hin call hval
      (cslotAddr sl) blk don fp extra ci sl excaps buffer))

end

end

end Fl4Proofs.P3
