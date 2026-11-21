/-
P3 (DESIGN.md §9), TCB invocations: **FL4's TCB extensions** (`Ext/Tcb`,
the dispatcher's `fl4DecodeTcbInvocation`) at their FL4 labels: `TcbOK`
against the spec's extension decoders and `invokeFl4Tcb`.

FL4 reads the extension arguments with `arg(i)` whatever the message
length; the spec's `fl4GetMr` is that read, and their agreement is the
hypothesis `ArgRel` (the message registers, P1's). The effects the
abstract model does not keep (debug registers, the l4h timer queue, the
FPU image) are one hypothesis per label (FL4 frame conditions: every slot
word kept).
-/
import Fl4Proofs.P3.TcbCtl
import Fl4Proofs.P3.HandleTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The spec's decoder of an extension label. -/
theorem fl4DecodeTcb_ext {label : Fl4Spec.Data} (h1 : Fl4Spec.genInvocationType label = .invalidInvocation)
    {l : Fl4Spec.Fl4TcbExtLabel} (h2 : Fl4Spec.fl4TcbExtLabelOf label = some l) {args : List Fl4Spec.Data}
    {cap : Fl4Spec.Cap} {slot : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} :
    Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4TcbExt l args (Fl4Spec.objRefOf cap) excaps buffer) := by
  unfold Fl4Spec.fl4DecodeTcbInvocation
  rw [if_neg (by rw [h1]; decide), h2]

/-- The spec's decoder of `SetFlags` (FL4's). -/
theorem fl4DecodeTcb_flags {label : Fl4Spec.Data} (h1 : Fl4Spec.genInvocationType label = .tcbSetFlags)
    {args : List Fl4Spec.Data} {cap : Fl4Spec.Cap} {slot : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} :
    Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetFlags args (Fl4Spec.objRefOf cap)) := by
  unfold Fl4Spec.fl4DecodeTcbInvocation
  rw [if_pos h1]

/-- The spec's ReadFPU step (`Fl4Spec.fl4FpuToFrame F`) has the outcome
with any user memory agreeing outside the 2696 bytes at `F`, the rest of the
machine state kept. -/
theorem fpuToFrame_mem (F : Fl4Spec.Word) (ms : Fl4Spec.MachineState) (um : Fl4Spec.Word64 → Fl4Spec.Word8)
    (h : ∀ a : Fl4Spec.Word64, Fl4Spec.fl4FpuStateSize ≤ (a - F).toNat → um a = ms.underlyingMemory a) :
    ((), { ms with underlyingMemory := um }) ∈ (Fl4Spec.fl4FpuToFrame F ms).1 := by
  unfold Fl4Spec.fl4FpuToFrame
  exact mem_bind_nd (x := (ms.underlyingMemory, ms)) rfl (mem_bind_nd (x := (um, ms)) ⟨h, rfl⟩ rfl)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Hypothesis (P1's): FL4's argument reads are the spec's** `fl4GetMr`,
for the first `k` arguments. -/
def ArgRel (s : S) (σ : Fl4Spec.State Unit) (ct buf : U64) (buffer : Option Fl4Spec.ObjRef) (k : Nat) : Prop :=
  ∀ i : U64, i.val < k → ∃ x, msg.syscall_arg st s ct buf i = ok x ∧
    Fl4Spec.fl4GetMr (Z := Unit) ct.bv buffer i.val σ = ({(x.bv, σ)}, False)

theorem arg_rel {s : S} {σ : Fl4Spec.State Unit} {ct buf : U64} {buffer : Option Fl4Spec.ObjRef} {k : Nat}
    (hA : ArgRel (st := st) s σ ct buf buffer k) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (c : tcb.Ctx) (hc : c.buf = buf) (i : U64) (hi : i.val < k) :
    ∃ x, tcb.arg st s c i = ok x ∧
      (Fl4Spec.fl4Arg (Z := Unit) buffer i.val).run σ = ({(.ok x.bv, σ)}, False) := by
  obtain ⟨x, hx, hg⟩ := hA i hi
  refine ⟨x, by unfold tcb.arg; rw [hct, hc]; simp only [bind_ok]; exact hx, ?_⟩
  unfold Fl4Spec.fl4Arg
  rw [run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread) rfl)]
  show (Fl4Spec.NonDetE.liftE (Fl4Spec.fl4GetMr (Z := Unit) σ.curThread buffer i.val)).run σ = _
  rw [hcur]
  exact run_liftE hg

/-- **An outcome of the spec's invocation after the restart, FL4's slots
kept, is a `TopPost` outcome.** -/
theorem top_of_post {th : TypedHeap} (hP : Placed th) {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {inv : Fl4Spec.Fl4Invocation} {G : MdbGhost} {s s1 s2 : S}
    {a : A} (hdec : DecOut m σ inv)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hDS1 : DState (L := L) th s1 σ1 G) (hfr : MdbOKV (L.ksb s) (L.mem s1) G)
    (h : RegPost (L := L) th s1 σ1 (Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv) s2) :
    TopPostM (L := L) σ blk call don m s (.Ok (), s2, a) := by
  obtain ⟨hS, y, hy, ⟨rr, hrr⟩, hR, hcdt, hio, hK⟩ := h
  obtain ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, -, hF1⟩ := hDS1
  exact Or.inr ⟨_, hdec, σ1, hst, y, hy, th, G, Or.inl ⟨rfl, rr, hrr⟩, hP,
    ⟨(hR _ hR1).of_caps (fun x hx => hS.capAt hx), hV1.of_caps (fun x hx => hS.capAt hx), hM1.of_same hS,
      hC1.of_same hS hcdt hio, MdbInv.of_same hM1 hI1 hS⟩, hF1.of_same hM1 hS hK, MdbOKV.of_same hM1 hS hfr⟩

/-- `RegPost` of an invocation with an outcome keeping the spec's state. -/
theorem regPost_same {th : TypedHeap} {s1 s2 : S} {σ1 : Fl4Spec.State Unit}
    {m : Fl4Spec.PMonad Unit (List Fl4Spec.Data)} {rr : List Fl4Spec.Data} (hS : SlotsSame th (L.mem s1) (L.mem s2))
    (hy : (.ok rr, σ1) ∈ (m.run σ1).1) : RegPost (L := L) th s1 σ1 m s2 :=
  ⟨hS, _, hy, ⟨rr, rfl⟩, fun _ h => h, rfl, rfl, KSub.refl _⟩

theorem check_bp_eq (bp : U64) :
    debug.check_bp_num bp = ok (if bp ≥ 4#u64 then .Err (.Sys (.RangeError 0#u64 3#u64)) else .Ok ()) := by
  unfold debug.check_bp_num; simp only [debug.N_REGS]; split <;> rfl

theorem bv_ge4 (bp : U64) : (bp.bv ≥ Fl4Spec.fl4NDebugRegs) ↔ bp ≥ 4#u64 := by
  unfold Fl4Spec.fl4NDebugRegs
  rw [GE.ge, GE.ge, BitVec.le_def, UScalar.bv_toNat]
  show (4 : BitVec 64).toNat ≤ bp.val ↔ _
  rw [show (4 : BitVec 64).toNat = 4 from rfl]; scalar_tac

theorem checkBp_run (σ : Fl4Spec.State Unit) (bp : U64) :
    (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv).run σ =
      if bp ≥ 4#u64 then ({(.error (.rangeError 0 3), σ)}, False) else ({(.ok (), σ)}, False) := by
  unfold Fl4Spec.fl4CheckBpNum
  by_cases h : bp ≥ 4#u64
  · rw [whenE_pos ((bv_ge4 bp).2 h), if_pos h]; rfl
  · rw [whenE_neg (fun h' => h ((bv_ge4 bp).1 h')), if_neg h]; rfl

theorem bp_err : ErrRel (.Sys (.RangeError 0#u64 3#u64)) (.rangeError 0 3) := Or.inl ⟨rfl, rfl⟩


/-! ## UnsetBreakpoint -/

/-- **The debug-register work of UnsetBreakpoint** (P1's): FL4's
`unset_breakpoint` after the restart keeps every slot word. -/
def UnsetBpHyp (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1 bp, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    debug.unset_breakpoint st s1 p bp ⦃ s2 => SlotsSame th (L.mem s1) (L.mem s2) ⦄

theorem decode_unset_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBUnsetBreakpoint p c = (do
      let bp ← tcb.arg st s c 0#u64
      let r ← debug.check_bp_num bp
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => do
        let s2 ← tcb.restart_caller st s
        let s3 ← debug.unset_breakpoint st s2 p bp
        ok (core.result.Result.Ok (), s3, ar)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s, ar)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBUnsetBreakpoint`** (`TcbOK`): the breakpoint
number's check, the restart, and the debug-register work (`UnsetBpHyp`). -/
theorem tcb_unset_bp_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .unsetBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1) (hU : UnsetBpHyp (L := L) th s ct p)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBUnsetBreakpoint p ⟨length, buf, call, slot, extra⟩ blk call don
      slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKF
  rw [decode_unset_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  simp only [bind_ok]
  have hsp : (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.unsetBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4UnsetBreakpoint
    exact run_bind_ok hbs _
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, bp_err⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.unsetBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    refine WP.spec_bind (hU s1 bp hs1) ?_
    intro s2 hS2
    exact (WP.spec_ok _).2 (top_of_post hP (DecOut.of_eq hdec) hst1 hDS1 hfr1 (regPost_same hS2 (rr := []) rfl))


/-! ## SetTimer -/

/-- SetTimer leaves the spec's state as it is among its outcomes (the
reprogram flag not set). -/
theorem setTimer_mem (blk call don : Bool) (σ1 : Fl4Spec.State Unit) (t d b : Fl4Spec.Data) :
    ((.ok [], σ1) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB (.setTimer t d b))).run σ1).1 := by
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
  refine mem_liftE (x := ([], σ1)) ?_
  refine mem_bind_nd (x := (false, σ1)) ⟨trivial, rfl⟩ ?_
  refine mem_bind_nd (x := ((), σ1)) ?_ rfl
  show ((), σ1) ∈ ({((), { σ1 with reprogramTimer := σ1.reprogramTimer || false })} : Set _)
  rw [Bool.or_false]; rfl

/-- **The timer work of SetTimer** (P1's): FL4's `timer::insert` after the
restart keeps every slot word. -/
def SetTimerHyp (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1 deadline badge, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    timer.insert st s1 p deadline badge ⦃ s2 => SlotsSame th (L.mem s1) (L.mem s2) ⦄

theorem decode_timer_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetTimer p c = (
      if c.length < 2#u64 then do
        let r ← error.truncated Unit
        ok (r, s, ar)
      else do
        let deadline ← tcb.arg st s c 0#u64
        let badge ← tcb.arg st s c 1#u64
        let s2 ← tcb.restart_caller st s
        let s3 ← timer.insert st s2 p deadline badge
        ok (core.result.Result.Ok (), s3, ar)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBSetTimer`** (`TcbOK`): the length check, the
restart, and the timer work (`SetTimerHyp`). -/
theorem tcb_set_timer_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setTimer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (hT : SetTimerHyp (L := L) th s ct p)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetTimer p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetTimer (Z := Unit) (args.map UScalar.bv) p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKF
  rw [decode_timer_eq arI s ar p _ hstall, hdec0]
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeFl4SetTimer
    rw [whenE_pos (by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok]
  obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4SetTimer (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.setTimer p.bv y0.bv y1.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4SetTimer
    rw [whenE_neg (by simp), retOk_bind]
    rfl
  refine WP.spec_bind (hT s1 y0 y1 hs1) ?_
  intro s2 hS2
  exact (WP.spec_ok _).2 (top_of_post hP (DecOut.of_eq hdec) hst1 hDS1 hfr1 (regPost_same hS2 (rr := [])
    (setTimer_mem blk call don σ1 p.bv y0.bv y1.bv)))


/-! ## GetBreakpoint (not called) -/

/-- **The debug-register read of GetBreakpoint** (P1's): total after the
restart. -/
def GetBpHyp (s : S) (ct p : U64) : Prop :=
  ∀ s1 bp, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → ∃ r, debug.get_breakpoint st s1 p bp = ok r

theorem decode_getbp_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBGetBreakpoint p c =
      (tcb.decode_get_breakpoint st s p c >>= fun x => ok (x.1, x.2, ar)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBGetBreakpoint`, not called** (`TcbOK`): the
breakpoint number's check, the restart, the read (`GetBpHyp`) and the
caller's `Running`. -/
theorem tcb_get_bp_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .getBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1) (hG : GetBpHyp (st := st) s ct p)
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBGetBreakpoint p ⟨length, buf, false, slot, extra⟩ blk false don
      slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKF
  rw [decode_getbp_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, false, slot, extra⟩ rfl 0#u64 (by decide)
  have hsp : (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.getBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4GetBreakpoint
    exact run_bind_ok hbs _
  unfold tcb.decode_get_breakpoint
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, bp_err⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, hk1, hc1⟩ :=
      restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
    rw [hrc1]; simp only [bind_ok]
    obtain ⟨r1, hr1⟩ := hG s1 bp hs1
    rw [hr1]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.getBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    have hact1 : OutsideObjects th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := by
      rw [hc1]; simp only [P1.LawfulStore.nodeAt, hk1]; exact hact
    refine WP.spec_bind (Pₘ := fun x : core.result.Result Unit error.Exc × S =>
        x.1 = .Ok () ∧ SlotsSame th (L.mem s1) (L.mem x.2))
      (WP.spec_bind (set_thread_state_slots th hP s1 ct sched.TS_RUNNING htcb hact1)
        (fun s2 hS2 => (WP.spec_ok _).2 ⟨rfl, hS2⟩)) ?_
    rintro ⟨r, s2⟩ ⟨hr, hS2⟩
    simp only at hr; subst hr
    exact (WP.spec_ok _).2 (top_of_post hP (DecOut.of_eq hdec) hst1 hDS1 hfr1
      (regPost_same hS2 (rr := [0, 0, 0, 0, 0]) (mem_liftE (x := ([0, 0, 0, 0, 0], σ1)) ⟨rfl, rfl⟩)))

/-! ## ConfigureSingleStepping (not called) -/

/-- **The debug-register work of ConfigureSingleStepping** (P1's): FL4's
`configure_single_stepping` after the restart keeps every slot word, the
kernel base and the core. -/
def SingleStepHyp (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1 bp n (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    debug.configure_single_stepping st arI s1 a p bp n false ⦃ r =>
      SlotsSame th (L.mem s1) (L.mem r.2.1) ∧ L.ksb r.2.1 = L.ksb s1 ∧ L.cpu r.2.1 = L.cpu s1 ⦄

theorem decode_step_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBConfigureSingleStepping p c =
      tcb.decode_configure_single_stepping st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- `as_user` of a computation with one outcome. -/
theorem asUser_det1 {α : Type} {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) {f : Fl4Spec.UserMonad α} {a : α} {uc' : Fl4Spec.UserContext}
    (hf : f (Fl4Spec.archTcbContextGet x.tcbArch) = ({(a, uc')}, False)) :
    Fl4Spec.asUser (Z := Unit) t f σ =
      ({(a, Notif.updK σ t (.tcb { x with tcbArch := Fl4Spec.archTcbContextSet uc' x.tcbArch }))}, False) := by
  unfold Fl4Spec.asUser
  show (Fl4Spec.NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (Notif.getTcb_eq hk)]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) Fl4Spec.UserContext) >>= _) σ = _
  rw [Notif.nd_pure_bind']
  show (Fl4Spec.NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show Fl4Spec.NonDet.selectF (σ := Fl4Spec.State Unit) (f (Fl4Spec.archTcbContextGet x.tcbArch)) σ =
      (({((a, uc'), σ)}), False) by
    rw [hf]; simp only [Fl4Spec.NonDet.selectF]
    ext ⟨a', b⟩ <;> simp)]
  show ((pure _ : Fl4Spec.NonDet (Fl4Spec.State Unit) Fl4Spec.Tcb) >>= _) σ = _
  rw [Notif.nd_pure_bind']
  exact (nd_bind_one (Notif.setObject_eq (o' := Fl4Spec.KernelObject.tcb
    { x with tcbArch := Fl4Spec.archTcbContextSet uc' x.tcbArch }) hk rfl) _).trans rfl

theorem mem_whenP_t {σ : Fl4Spec.State Unit} {P : Prop} [Decidable P] {m : Fl4Spec.SMonad Unit Unit}
    {z : Unit × Fl4Spec.State Unit} (h : P → z ∈ (m σ).1) (h' : ¬ P → z = ((), σ)) :
    z ∈ (Fl4Spec.NonDet.when P m σ).1 := by
  unfold Fl4Spec.NonDet.when
  by_cases hp : P
  · rw [if_pos hp]; exact h hp
  · rw [if_neg hp, h' hp]; rfl

/-- The trap flag (bit 8 of `FLAGS`). -/
def tfMask : Fl4Spec.Word := ~~~((1 : Fl4Spec.Word) <<< 8)

/-- **The spec's state after ConfigureSingleStepping**: with no instruction
count, the target's trap flag cleared. -/
def cssState (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (n : Fl4Spec.Data) :
    Fl4Spec.State Unit :=
  if n = 0 then Notif.updK σ t (.tcb (Notif.setReg x .flags (x.tcbArch.tcbContext.userRegs .flags &&& tfMask)))
  else σ

/-- The spec's ConfigureSingleStepping has the outcome `[0]` at `cssState`. -/
theorem css_mem {σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ1.kheap t = some (.tcb x)) (bp n : Fl4Spec.Data) :
    ((.ok [0], cssState σ1 t x n) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.invokeFl4Tcb (Z := Unit) (.configureSingleStepping t bp n)).run σ1).1 := by
  unfold Fl4Spec.invokeFl4Tcb
  refine mem_liftE (x := ([0], cssState σ1 t x n)) ?_
  refine mem_bind_nd (x := ((), cssState σ1 t x n)) (mem_whenP_t (fun h => ?_) (fun h => ?_)) ⟨Or.inl rfl, rfl⟩
  · rw [asUser_det1 hk (a := ()) (uc' := ⟨(Fl4Spec.archTcbContextGet x.tcbArch).userFpuState,
      Function.update (Fl4Spec.archTcbContextGet x.tcbArch).userRegs .flags
        (x.tcbArch.tcbContext.userRegs .flags &&& tfMask)⟩) (by
      rw [nd_bind_one (show Fl4Spec.getRegister .flags (Fl4Spec.archTcbContextGet x.tcbArch) =
        ({((Fl4Spec.archTcbContextGet x.tcbArch).userRegs .flags, Fl4Spec.archTcbContextGet x.tcbArch)}, False)
        from rfl)]
      rfl)]
    simp only [cssState, h, ↓reduceIte]
    rfl
  · simp only [cssState, h, ↓reduceIte]

/-- `cssState` keeps the CSpace (`StateRel`, the CDT, `KSub`). -/
theorem cssState_rel {σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ1.kheap t = some (.tcb x)) (n : Fl4Spec.Data) :
    (∀ th mm, StateRel th mm σ1 → StateRel th mm (cssState σ1 t x n)) ∧
      (cssState σ1 t x n).cdt = σ1.cdt ∧ (cssState σ1 t x n).isOriginalCap = σ1.isOriginalCap ∧
      KSub σ1 (cssState σ1 t x n) := by
  unfold cssState
  split
  · exact ⟨fun _ _ h => h.set_reg hk _ _, rfl, rfl, ksub_updK_tcb hk⟩
  · exact ⟨fun _ _ h => h, rfl, rfl, KSub.refl _⟩

/-- **`tcb::decode` at `TCBConfigureSingleStepping`, not called**
(`TcbOK`): no checks; the restart, the debug-register work
(`SingleStepHyp`) and the caller's `Running`. -/
theorem tcb_single_step_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .configureSingleStepping)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 2) (hS : SingleStepHyp (L := L) arI th s ct p)
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBConfigureSingleStepping p ⟨length, buf, false, slot, extra⟩ blk
      false don slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKF
  rw [decode_step_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, false, slot, extra⟩ rfl 0#u64 (by decide)
  obtain ⟨n, hn, hns⟩ := arg_rel hA hct hcur ⟨length, buf, false, slot, extra⟩ rfl 1#u64 (by decide)
  unfold tcb.decode_configure_single_stepping
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [hn]; simp only [bind_ok]
  obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, hk1, hc1⟩ :=
    restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4ConfigureSingleStepping
    rw [run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 0).run σ = _ from hbs),
      run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 1).run σ = _ from hns)]
    rfl
  refine WP.spec_bind (hS s1 bp n ar hs1) ?_
  rintro ⟨consumed, s2, a2⟩ ⟨hS2, hk2, hc2⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hact2 : OutsideObjects th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
    simp only at hk2 hc2
    rw [hc2, hc1]; simp only [P1.LawfulStore.nodeAt, hk2, hk1]; exact hact
  refine WP.spec_bind (set_thread_state_slots th hP s2 ct sched.TS_RUNNING htcb hact2) ?_
  intro s3 hS3
  obtain ⟨xp, hkp, -⟩ := hDS1.1.1.tcb p hp
  obtain ⟨hR, hcdt, hio, hK⟩ := cssState_rel hkp n.bv
  exact (WP.spec_ok _).2 (top_of_post hP (DecOut.of_eq hdec) hst1 hDS1 hfr1
    ⟨hS2.trans hS3, _, css_mem hkp bp.bv n.bv, ⟨[0], rfl⟩, hR th, hcdt, hio, hK⟩)


/-! ## SetFlags -/

/-- **The flags work of SetFlags, not called** (P1's and the scheduler's):
FL4's `decode_set_flags` past its length check, against the spec's FL4
SetFlags from the restart's states. -/
def SetFlagsHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64) (c : tcb.Ctx) : Prop :=
  ∀ s1 σ1 (clear set : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    tcb.arg st s c 0#u64 = ok clear → tcb.arg st s c 1#u64 = ok set → ¬ c.length < 2#u64 →
    tcb.decode_set_flags st arI s a p c ⦃ r => r.1 = .Ok () ∧
      RegPost (L := L) th s1 σ1 (Fl4Spec.invokeFl4Tcb (Z := Unit) (.setFlags p.bv clear.bv set.bv)) r.2.1 ⦄

/-- **The flags work and the reply of SetFlags, called** (P1's): FL4's
`decode_set_flags` past its length check, the caller no longer `Restart`,
against the spec's FL4 SetFlags and `handle_invocation`'s reply. -/
def SetFlagsCallHyp (s : S) (σ : Fl4Spec.State Unit) (ct p : U64) (c : tcb.Ctx) (blk don : Bool) : Prop :=
  ∀ s1 σ1 (clear set : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    tcb.arg st s c 0#u64 = ok clear → tcb.arg st s c 1#u64 = ok set → ¬ c.length < 2#u64 →
    tcb.decode_set_flags st arI s a p c ⦃ res => res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk true don
        (.invokeFl4TCB (.setFlags p.bv clear.bv set.bv))).run σ1).1 ∧
      ∃ z ∈ (specTail true ct.bv rr σy).1, RelTopM (L := L) res.2.1 z.2 ⦄

theorem decode_flags_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetFlags p c = tcb.decode_set_flags st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

theorem setFlags_dec (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (p : U64)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4SetFlags (Z := Unit) args p.bv) := by
  show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
  rw [fl4DecodeTcb_flags hlbl]; rfl

theorem setFlags_trunc (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (args : List Fl4Spec.Data) (h : args.length < 2) :
    (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4SetFlags (Z := Unit) args p)).run σ =
      ({(.error .truncatedMessage, σ)}, False) := by
  apply run_liftME_err
  unfold Fl4Spec.decodeFl4SetFlags
  rw [whenE_pos h]
  exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
    Fl4Spec.SEMonad Unit Unit)) rfl _

theorem setFlags_ok (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (y0 y1 : Fl4Spec.Data) (rest : List Fl4Spec.Data) :
    (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4SetFlags (Z := Unit) (y0 :: y1 :: rest) p)).run σ =
      ({(.ok (.invokeFl4TCB (.setFlags p y0 y1)), σ)}, False) := by
  apply run_liftME_ok
  unfold Fl4Spec.decodeFl4SetFlags
  rw [whenE_neg (by simp), retOk_bind]
  rfl

/-- **`tcb::decode` at `TCBSetFlags`, not called** (`TcbOK`): the length
check, the restart, and the flags work (`SetFlagsHyp`). -/
theorem tcb_set_flags_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hF : SetFlagsHyp (L := L) arI th s σ ct p ⟨length, buf, false, slot, extra⟩) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetFlags p ⟨length, buf, false, slot, extra⟩ blk false don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  unfold TcbOKF
  rw [decode_flags_eq arI s ar p _ hstall, setFlags_dec slbl hlbl]
  by_cases h1 : length < 2#u64
  · unfold tcb.decode_set_flags
    simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage,
      setFlags_trunc σ p.bv _ (by rw [List.length_map, ← hlen]; scalar_tac), Or.inl trivial⟩)
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, false, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, false, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨s1, σ1, -, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
  refine WP.spec_mono (hF s1 σ1 y0 y1 ar hs1 (by rw [← hcur]; exact hst1) ha0 ha1 h1) ?_
  rintro ⟨r, s2, a2⟩ ⟨hr, h2⟩
  simp only at hr; subst hr
  exact top_of_post hP (DecOut.of_eq (setFlags_ok σ p.bv _ _ _)) hst1 hDS1 hfr1 h2

/-- The statement for `tcb::decode` at a label whose decode replies itself
(`call` true): `TopPostRM`. -/
abbrev TcbOKR (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64) (p : U64) (c : tcb.Ctx)
    (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPostRM (L := L) σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) ct s res ⦄

/-- **The Thread cap, its decode replying itself** (`DecOKRM`). -/
theorem decode_invocation_thread_r (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (h : fp = false → TcbOKR (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer ct) :
    DecOKRM (L := L) arI s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer
      ct := by
  unfold DecOKRM syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h rfl
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **`tcb::decode` at `TCBSetFlags`, called** (`TcbOKR`): the length
check, the restart, and the flags work with FL4's reply
(`SetFlagsCallHyp`). -/
theorem tcb_set_flags_call (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (hF : SetFlagsCallHyp (L := L) arI s σ ct p ⟨length, buf, true, slot, extra⟩ blk don)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKR (L := L) arI s ar σ fl4_abi.label.TCBSetFlags p ⟨length, buf, true, slot, extra⟩ blk true don slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  unfold TcbOKR
  rw [decode_flags_eq arI s ar p _ hstall, setFlags_dec slbl hlbl]
  by_cases h1 : length < 2#u64
  · unfold tcb.decode_set_flags
    simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage,
      setFlags_trunc σ p.bv _ (by rw [List.length_map, ← hlen]; scalar_tac), Or.inl trivial⟩)
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, true, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, true, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨s1, σ1, -, hs1, hst1, -, -, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  refine WP.spec_mono (hF s1 σ1 y0 y1 ar hs1 (by rw [← hcur]; exact hst1) ha0 ha1 h1) ?_
  rintro res ⟨hres, hne, rr, σy, hy, z, hz, hRT⟩
  exact Or.inr ⟨hres, hne, _, DecOut.of_eq (setFlags_ok σ p.bv _ _ _), σ1, hst1, rr, σy, hy, z, hz, hRT⟩


/-! ## ReadRegisters, called -/

/-- **The register work and the reply of ReadRegisters, called** (P1's):
FL4's `read_registers` replying itself after the restart, the caller no
longer `Restart`, against the spec's ReadRegisters and `handle_invocation`'s
reply. -/
def ReadRegsCallHyp (s : S) (σ : Fl4Spec.State Unit) (ct p : U64) (blk don : Bool) : Prop :=
  ∀ s1 σ1 (flags n : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    tcb.read_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n true ⦃ r =>
      L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ rr σy, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk true don
        (.invokeTCB (.readRegisters p.bv (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
      ∃ z ∈ (specTail true ct.bv rr σy).1, RelTopM (L := L) r.1 z.2 ⦄

/-- **`tcb::decode` at `TCBReadRegisters`, called** (`TcbOKR`): the decode
checks as `tcb_read_regs_refines`, the restart, and the register work with
FL4's reply (`ReadRegsCallHyp`). -/
theorem tcb_read_regs_call (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbReadRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (hR : ReadRegsCallHyp (L := L) arI s σ ct p blk don)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKR (L := L) arI s ar σ fl4_abi.label.TCBReadRegisters p ⟨length, buf, true, slot, extra⟩ blk true don slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeReadRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKR
  rw [decode_read_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_read_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp at h; scalar_tac
    | [_], h => exfalso; simp at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, true, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, true, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok, nregs_eq]
  have hsp : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      (Fl4Spec.decodeReadRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    intro _
    simp only [Fl4Spec.decodeReadRegisters, List.map_cons, nregs_spec, retOk_bind]
  rw [hsp (fun _ => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.suspend 0))]
  have hrng := range20_iff y1
  by_cases hr : 1 ≤ y1.val ∧ y1.val ≤ 20
  · have hn1 : ¬ y1 < 1#u64 := by scalar_tac
    have hn2 : ¬ y1 > 20#u64 := by scalar_tac
    simp only [hn1, hn2, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
    have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ = ({(.ok (), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_pos (hrng.2 hr)]; rfl
    by_cases hpc : p = ct
    · subst hpc
      simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
      refine (WP.spec_ok _).2 ?_
      apply Or.inl
      refine ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩
      apply run_liftME_err
      rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
      rw [hrc1]; simp only [bind_ok, lift]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
            let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
            Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
            Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
              Fl4Spec.ArchDefaultExtraRegisters))).run σ =
          ({(.ok (.invokeTCB (.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
            Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
        apply run_liftME_ok
        rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
          s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc), retOk_bind]
        rfl
      refine WP.spec_bind (hR s1 σ1 y0 y1 ar hs1 (by rw [← hcur]; exact hst1)) ?_
      rintro ⟨s2, a2⟩ ⟨hne, rr, σy, hy, z, hz, hRT⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, rr, σy, hy, z, hz, hRT⟩)
  · have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ =
        ({(.error (.rangeError 1 (BitVec.ofNat 64 20)), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_neg (fun h => hr (hrng.1 h))]; rfl
    have herr : ErrRel (.Sys (.RangeError 1#u64 20#u64)) (.rangeError 1 (BitVec.ofNat 64 20)) :=
      Or.inl ⟨rfl, rfl⟩
    by_cases hn1 : y1 < 1#u64
    · simp only [hn1, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr⟩)
      exact run_liftME_err (run_bind_error hrc _)
    · have hn2 : y1 > 20#u64 := by scalar_tac
      simp only [hn1, hn2, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr⟩)
      exact run_liftME_err (run_bind_error hrc _)


/-! ## ReadFPU, WriteFPU -/

theorem fsize_eq (sz : capability.FrameSize) : ∃ v : U64,
    (do let i ← capability.FrameSize.bits sz; let i1 ← lift (i &&& 63#u64); (1#u64 <<< i1 : Result U64)) = ok v ∧
      v.val = 2 ^ frameBitsN sz := by
  cases sz <;> simp only [capability.FrameSize.bits, bind_ok, lift]
  · obtain ⟨z, hz, hv, -⟩ := spec_exists (U64.ShiftLeft_spec 1#u64 (12#u64 &&& 63#u64) (by decide))
    exact ⟨z, hz, by rw [hv]; simp [Nat.shiftLeft_eq, UScalar.val_and, U64.size, U64.numBits, frameBitsN]⟩
  · obtain ⟨z, hz, hv, -⟩ := spec_exists (U64.ShiftLeft_spec 1#u64 (21#u64 &&& 63#u64) (by decide))
    exact ⟨z, hz, by rw [hv]; simp [Nat.shiftLeft_eq, UScalar.val_and, U64.size, U64.numBits, frameBitsN]⟩
  · obtain ⟨z, hz, hv, -⟩ := spec_exists (U64.ShiftLeft_spec 1#u64 (30#u64 &&& 63#u64) (by decide))
    exact ⟨z, hz, by rw [hv]; simp [Nat.shiftLeft_eq, UScalar.val_and, U64.size, U64.numBits, frameBitsN]⟩

theorem frame_rights (r : U64) (h1 : 1 ≤ r.val) (h3 : r.val ≤ 3) :
    (vmRightsOf r = Fl4Spec.vmKernelOnly ↔ r = 1#u64) ∧ (vmRightsOf r = Fl4Spec.vmReadWrite ↔ r = 3#u64) := by
  unfold vmRightsOf
  have : r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by omega
  rcases this with h | h | h <;>
    simp [h, u64_eq_iff, Fl4Spec.vmKernelOnly, Fl4Spec.vmReadWrite, Fl4Spec.vmReadOnly] <;>
    (intro h'; first
      | simpa using Set.ext_iff.1 h' .allowRead
      | simpa using Set.ext_iff.1 h' .allowWrite
      | simpa using (Set.ext_iff.1 h' .allowWrite).symm
      | simpa using (Set.ext_iff.1 h' .allowRead).symm)

theorem fshift_eq (sz : capability.FrameSize) : ∃ z : U64, z.val = 2 ^ frameBitsN sz ∧
    ∀ {α : Type} (f : U64 → Result α),
      (do let i ← capability.FrameSize.bits sz; let i1 ← lift (i &&& 63#u64); let size1 ← (1#u64 <<< i1 : Result U64)
          f size1) = f z := by
  obtain ⟨z, hz, hzv⟩ := fsize_eq sz
  refine ⟨z, hzv, fun f => ?_⟩
  cases sz <;> simp only [capability.FrameSize.bits, lift, bind_ok] at hz ⊢ <;> rw [hz] <;> simp only [bind_ok]

theorem off_fail {α : Type} (e : α) (K : Result α) (y0 z : U64)
    (hfail : ¬ (y0.val % 64 = 0 ∧ y0.val < z.val ∧ 2696 ≤ z.val - y0.val)) :
    (do
      let i2 ← y0 % 64#u64
      if i2 != 0#u64 then ok e
      else if y0 >= z then ok e
      else do
        let i3 ← z - y0
        if i3 < fl4_abi.consts.FPU_STATE_SIZE then ok e else K) = ok e := by
  obtain ⟨m, hm, hmv⟩ := spec_exists (UScalar.rem_spec y0 (y := 64#u64) (by decide))
  rw [hm]; simp only [bind_ok]
  by_cases h1 : m != 0#u64
  · simp only [h1, ↓reduceIte]
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  have hm0 : y0.val % 64 = 0 := by
    have e1 : m.val = y0.val % 64 := by rw [hmv]; rfl
    have e2 : m.val = 0 := by simpa using h1
    omega
  by_cases h2 : y0 >= z
  · simp only [h2, ↓reduceIte]
  simp only [h2, ↓reduceIte]
  have h2' : y0.val < z.val := by scalar_tac
  obtain ⟨d, hd, hdv⟩ := spec_exists (U64.sub_spec (x := z) (y := y0) (by scalar_tac))
  rw [hd]; simp only [bind_ok]
  have hfps : (fl4_abi.consts.FPU_STATE_SIZE).val = 2696 := by unfold fl4_abi.consts.FPU_STATE_SIZE; rfl
  have h3 : d < fl4_abi.consts.FPU_STATE_SIZE := by
    have : ¬ 2696 ≤ z.val - y0.val := fun h => hfail ⟨hm0, h2', h⟩
    scalar_tac
  simp only [h3, ↓reduceIte]

/-- The FPU transfer's checks passing (FL4's `fpu_transfer`). -/
def FpuPass (toFrame : Bool) (offset r : U64) (sz : capability.FrameSize) : Prop :=
  r ≠ 1#u64 ∧ (toFrame = true → r = 3#u64) ∧ offset.val % 64 = 0 ∧ offset.val < 2 ^ frameBitsN sz ∧
    fl4Spec_fpu ≤ 2 ^ frameBitsN sz - offset.val
where fl4Spec_fpu : Nat := Fl4Spec.fl4FpuStateSize

/-- **The FPU work of ReadFPU and WriteFPU** (P1's and the arch's): FL4's
`fpu_transfer` whose checks pass ends `Ok`, every slot word kept from the
restart's state. -/
def FpuHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64) (c : tcb.Ctx) (toFrame : Bool) : Prop :=
  ∀ s1 σ1 (a : A) (x ptr offset r asid va : U64) (m ep : Bool) (sz : capability.FrameSize),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    Aeneas.Std.Array.index_usize c.extra 0#usize = ok x → x ≠ 0#u64 → ¬ c.length < 1#u64 →
    tcb.arg st s c 0#u64 = ok offset → capV (L.mem s) x = .Frame ptr sz r false m ep asid va →
    FpuPass toFrame offset r sz →
    tcb.fpu_transfer st arI s a p c toFrame ⦃ res => res.1 = .Ok () ∧ SlotsSame th (L.mem s1) (L.mem res.2.1) ⦄

/-- **FL4's `fpu_transfer`** against the spec's `decodeFl4FpuTransfer`, the
restart and `invokeFl4Tcb`: the checks proved, the work `FpuHyp`. -/
theorem fpu_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (toFrame : Bool) (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hF : FpuHyp (L := L) arI th s σ ct p ⟨length, buf, call, slot, extra⟩ toFrame) (blk don : Bool) :
    tcb.fpu_transfer st arI s ar p ⟨length, buf, call, slot, extra⟩ toFrame ⦃ res =>
      TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame (args.map UScalar.bv) p.bv excaps)) s res ⦄ := by
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : excaps = [] ∨ args = [] →
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame (args.map UScalar.bv) p.bv excaps)).run σ =
        ({(.error .truncatedMessage, σ)}, False) := by
    intro h
    apply run_liftME_err
    unfold Fl4Spec.decodeFl4FpuTransfer
    rw [whenE_pos (by rcases h with h | h <;> simp [h])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage,
      htr (Or.inl (List.eq_nil_of_length_eq_zero (by omega))), Or.inl trivial⟩)
  by_cases hl : length < 1#u64
  · unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, error.truncated, bind_ok,
      show ¬ (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 by show ¬ length >= 1#u64; scalar_tac]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage,
      htr (Or.inr (List.eq_nil_of_length_eq_zero (by scalar_tac))), Or.inl trivial⟩)
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args, hlen with
    | y0 :: rest, _ => exact ⟨_, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨erest, rfl⟩ : ∃ erest, excaps = e0 :: erest := by
    match excaps, he0 with
    | a :: r, h => simp at h; exact ⟨r, by rw [h]⟩
  have hspec : (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv
      (e0 :: erest)) =
      (match absCap (capV (L.mem s) x0) with
      | .archObjectCap (.pageCap dev base rights _ sz _) =>
        if dev ∨ rights = Fl4Spec.vmKernelOnly ∨ (toFrame ∧ rights ≠ Fl4Spec.vmReadWrite)
        then Fl4Spec.NonDetE.throwError (.invalidCapability 1)
        else do
          let size := 2 ^ Fl4Spec.pageBitsForSize sz
          Fl4Spec.NonDetE.whenE (y0.bv.toNat % 64 ≠ 0 ∨ y0.bv.toNat ≥ size ∨
              size - y0.bv.toNat < Fl4Spec.fl4FpuStateSize) <|
            Fl4Spec.NonDetE.throwError (.invalidArgument 0)
          Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.fpuTransfer p.bv toFrame (base + y0.bv))
      | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1)) := by
    unfold Fl4Spec.decodeFl4FpuTransfer
    rw [whenE_neg (by simp), retOk_bind, retOk_bind]
    simp only [List.map_cons, List.getElem?_cons_zero, the_some]
    rw [he01]; rfl
  have hcwf := (slot_wf hDS.1.1 hps0 hps01).1
  rw [← hxe0] at hcwf
  generalize hc : capV (L.mem s) x0 = c at hcwf hspec
  -- the checks passing: FL4's work
  have hfr : ∀ ptr sz r m ep asid va, c = .Frame ptr sz r false m ep asid va → FpuPass toFrame y0 r sz →
      tcb.fpu_transfer st arI s ar p ⟨length, buf, call, slot, extra⟩ toFrame ⦃ res =>
        TopPostM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
          (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv (e0 :: erest)))
          s res ⦄ := by
    intro ptr sz r m ep asid va hcf hpass
    subst hcf
    obtain ⟨s1, σ1, -, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
    obtain ⟨hr1, hr3, hm, hlt, hrm⟩ := hpass
    obtain ⟨hw1, hw3⟩ := hcwf
    have hrg := frame_rights r hw1 hw3
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv (e0 :: erest))).run σ =
        ({(.ok (.invokeFl4TCB (.fpuTransfer p.bv toFrame (ptr.bv + y0.bv))), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec]
      simp only [absCap]
      rw [if_neg (by
        rintro (h | h | ⟨h1, h2⟩)
        · cases h
        · exact hr1 (hrg.1.1 h)
        · exact h2 (hrg.2.2 (hr3 h1)))]
      rw [whenE_neg (by
        have hb : Fl4Spec.pageBitsForSize (frameSizeOf sz) = frameBitsN sz := by cases sz <;> rfl
        rw [hb, UScalar.bv_toNat]
        unfold FpuPass.fl4Spec_fpu at hrm
        omega), retOk_bind]
      rfl
    refine WP.spec_mono (hF s1 σ1 ar x0 ptr y0 r asid va m ep sz hs1 (by rw [← hcur]; exact hst1) hx0 h0 hl ha0 hc
      ⟨hr1, hr3, hm, hlt, hrm⟩) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, hS2⟩
    simp only at hr2; subst hr2
    refine top_of_post hP (DecOut.of_eq hdec) hst1 hDS1 hfr1 (regPost_same hS2 (rr := []) ?_)
    cases toFrame
    · rfl
    · show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
      refine mem_liftE (x := ([], σ1)) ?_
      refine mem_bind_nd (x := ((), { σ1 with machineState := σ1.machineState })) ?_ (Set.mem_singleton_iff.2 rfl)
      exact dmo_ex _ σ1 (fpuToFrame_mem _ σ1.machineState σ1.machineState.underlyingMemory fun _ _ => rfl)
  have hge : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 := by show length >= 1#u64; scalar_tac
  have hic : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.Fl4TcbInvocation),
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.Fl4TcbInvocation)).run σ =
        ({(.error (.invalidCapability 1), σ)}, False) := fun _ => run_liftME_err rfl
  have herr1 : ErrRel (.Sys (.InvalidCapability 1#u64)) (.invalidCapability 1) := Or.inr ⟨1#u64, rfl, rfl⟩
  cases c
  case Frame ptr sz r dev m ept asid va =>
    by_cases hpass : dev = false ∧ FpuPass toFrame y0 r sz
    · obtain ⟨rfl, hp⟩ := hpass; exact hfr _ _ _ _ _ _ _ rfl hp
    have hvk : capability.VM_KERNEL_ONLY = 1#u64 := by simp only [capability.VM_KERNEL_ONLY]
    have hvrw : capability.VM_READ_WRITE = 3#u64 := by simp only [capability.VM_READ_WRITE]
    obtain ⟨hw1, hw3⟩ := hcwf
    have hrg := frame_rights r hw1 hw3
    have hrun : ∀ tf : Bool, (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        ((Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidArgument 0) : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.fpuTransfer p.bv tf (ptr.bv + y0.bv)))).run σ =
        ({(.error (.invalidArgument 0), σ)}, False) := fun _ =>
      run_liftME_err (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidArgument 0) :
        Fl4Spec.SEMonad Unit Unit)) rfl _)
    have herr0 : ErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) := Or.inl rfl
    have hb : Fl4Spec.pageBitsForSize (frameSizeOf sz) = frameBitsN sz := by cases sz <;> rfl
    obtain ⟨z, hzv, hzf⟩ := fshift_eq sz
    unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, hge, bind_ok]
    rw [ha0]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]; simp only [bind_ok, hvk, hvrw, hzf]
    by_cases hd : dev = true
    · simp only [hd, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr1⟩)
      rw [hspec]; simp only [absCap]
      rw [if_pos (Or.inl hd)]; exact hic (fun _ => Fl4Spec.NonDetE.returnOk default)
    simp only [Bool.not_eq_true] at hd; subst hd
    by_cases hr1 : r = 1#u64
    · have hk : vmRightsOf r = Fl4Spec.vmKernelOnly := hrg.1.2 hr1
      simp only [hr1, ↓reduceIte, error.invalid_cap, bind_ok, Bool.false_eq_true]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr1⟩)
      rw [hspec]; simp only [absCap]
      rw [if_pos (Or.inr (Or.inl hk))]; exact hic (fun _ => Fl4Spec.NonDetE.returnOk default)
    have hk : vmRightsOf r ≠ Fl4Spec.vmKernelOnly := fun h => hr1 (hrg.1.1 h)
    simp only [hr1, ↓reduceIte, Bool.false_eq_true]
    have hoff : (toFrame = true → r = 3#u64) →
        ¬ (y0.val % 64 = 0 ∧ y0.val < z.val ∧ 2696 ≤ z.val - y0.val) := by
      intro h3 h
      exact hpass ⟨rfl, hr1, h3, h.1, hzv ▸ h.2.1, by unfold FpuPass.fl4Spec_fpu Fl4Spec.fl4FpuStateSize; rw [← hzv]; exact h.2.2⟩
    have hoffS : (toFrame = true → r = 3#u64) →
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
          (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame ((y0 :: rest).map UScalar.bv) p.bv (e0 :: erest))).run σ =
          ({(.error (.invalidArgument 0), σ)}, False) := by
      intro h3
      rw [hspec]; simp only [absCap]
      rw [if_neg (by
        rintro (h | h | ⟨h1, h2⟩)
        · cases h
        · exact hk h
        · exact h2 (hrg.2.2 (h3 h1))), hb, whenE_pos (by
          have := hoff h3; rw [UScalar.bv_toNat, ← hzv]; unfold Fl4Spec.fl4FpuStateSize; omega)]
      exact hrun toFrame
    cases toFrame
    · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_arg, bind_ok]
      rw [off_fail _ _ y0 z (hoff (fun h => by cases h))]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, hoffS (fun h => by cases h), herr0⟩)
    · by_cases hr3 : r = 3#u64
      · simp only [↓reduceIte, hr3, bne_self_eq_false, Bool.false_eq_true, error.invalid_arg, bind_ok]
        rw [off_fail _ _ y0 z (hoff (fun _ => hr3))]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, hoffS (fun _ => hr3), herr0⟩)
      · simp only [↓reduceIte, bne_iff_ne, ne_eq, hr3, not_false_eq_true, error.invalid_cap, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr1⟩)
        rw [hspec]; simp only [absCap]
        rw [if_pos (Or.inr (Or.inr ⟨trivial, fun h => hr3 (hrg.2.1 h)⟩))]
        exact hic (fun _ => Fl4Spec.NonDetE.returnOk default)
  all_goals
    unfold tcb.fpu_transfer
    rw [extra_eq _ 0#usize (by decide) hx0]
    simp only [h0, ↓reduceIte, hge, bind_ok]
    rw [ha0]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]
    simp only [bind_ok, error.invalid_cap]
    rw [hspec]
    simp only [absCap]
    try split_ifs
    all_goals exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, hic (fun _ => Fl4Spec.NonDetE.returnOk default),
      herr1⟩)


theorem decode_fpu_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBReadFPU p c = tcb.fpu_transfer st arI s ar p c true ∧
    tcb.decode st arI s ar fl4_abi.label.TCBWriteFPU p c = tcb.fpu_transfer st arI s ar p c false := by
  constructor <;>
  · unfold tcb.decode
    rw [hstall]
    simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    rfl

/-- **`tcb::decode` at `TCBReadFPU` / `TCBWriteFPU`** (`TcbOK`, `toFrame`
for ReadFPU): `fpu_refines`. -/
theorem tcb_fpu_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (toFrame : Bool) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some (if toFrame then .readFpu else .writeFpu))
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hF : FpuHyp (L := L) arI th s σ ct p ⟨length, buf, call, slot, extra⟩ toFrame) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ (if toFrame then fl4_abi.label.TCBReadFPU else fl4_abi.label.TCBWriteFPU) p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) toFrame (args.map UScalar.bv) p.bv excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]
    cases toFrame <;> rfl
  unfold TcbOKF
  have he := decode_fpu_eq arI s ar p ⟨length, buf, call, slot, extra⟩ hstall
  rw [hdec0]
  cases toFrame
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [he.2]
    exact fpu_refines arI th hP s ar σ G hDS hFR p false length buf ct hct args hlen hargs hcur htcb hact call slot extra
      x0 x1 x2 hx0 excaps hX hF blk don
  · simp only [↓reduceIte]; rw [he.1]
    exact fpu_refines arI th hP s ar σ G hDS hFR p true length buf ct hct args hlen hargs hcur htcb hact call slot extra
      x0 x1 x2 hx0 excaps hX hF blk don


/-! ## SetBreakpoint -/

/-- **SetBreakpoint** (P1's): FL4's `set_breakpoint_checked` (3343 lines of
extracted control flow for its argument checks), against the spec's
`decodeFl4SetBreakpoint`, the restart and `invokeFl4Tcb`. Its checks are
on the arguments alone (no cap, no slot); the debug registers it writes
are outside the slots. -/
def SetBpHyp (σ : Fl4Spec.State Unit) (s : S) (ar : A) (p : U64) (c : tcb.Ctx) (blk call don : Bool)
    (buffer : Option Fl4Spec.ObjRef) : Prop :=
  tcb.set_breakpoint_checked st s p c ⦃ x => TopPostM (L := L) σ blk call don
    (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv))
    s (x.1, x.2, ar) ⦄

theorem decode_setbp_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetBreakpoint p c =
      (tcb.set_breakpoint_checked st s p c >>= fun x => ok (x.1, x.2, ar)) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val, lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val, lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val, lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val, lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val, lbl_tcbSetTLSBase_val, lbl_tcbSetFlags_val, lbl_tcbReadFPU_val, lbl_tcbWriteFPU_val, lbl_tcbSetTimer_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBSetBreakpoint`** (`TcbOK`), from `SetBpHyp`. -/
theorem tcb_set_bp_refines (s : S) (ar : A) (σ : Fl4Spec.State Unit) (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setBreakpoint)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hB : SetBpHyp (L := L) σ s ar p c blk call don buffer) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetBreakpoint p c blk call don slbl args ci sl excaps buffer := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKF
  rw [decode_setbp_eq arI s ar p _ hstall, hdec0]
  exact WP.spec_bind hB (fun x hx => (WP.spec_ok _).2 hx)

/-! ## Every label -/

theorem ext_lbl {slbl : Fl4Spec.Data} {lbl : U64} (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hg : tcbLabelOf lbl = .invalidInvocation) {l : Fl4Spec.Fl4TcbExtLabel} (hl : tcbExtOf lbl = some l) :
    Fl4Spec.genInvocationType slbl = .invalidInvocation ∧ Fl4Spec.fl4TcbExtLabelOf slbl = some l := by
  have h1 : Fl4Spec.genInvocationType slbl = .invalidInvocation := by rw [hlbl, hg]
  exact ⟨h1, by rw [hext h1, hl]⟩

/-- **`tcb::decode`, native labels, the CSpace-side and the extension labels
proved**: `tcb_decode_cspace` with FL4's extensions discharged here (their
work as `SetBpHyp`, `UnsetBpHyp`, `GetBpHyp`, `SingleStepHyp`,
`SetTimerHyp`, `FpuHyp`, `SetFlagsHyp`; the argument reads `ArgRel`).
GetBreakpoint, ConfigureSingleStepping and SetFlags called reply in the
decode: those cases are hypotheses here (`DecOKRM`: `tcb_set_flags_call`). -/
theorem tcb_decode_ext [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcw : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) th s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    -- the work of the CSpace-side labels
    (hres : TlsResHyp (L := L) th s σ ct) (hBuf : ∀ v : U64, BufHyp (L := L) (A := A) th p v v.bv)
    (hRead : ReadRegsHyp (L := L) arI th s σ ct p) (hWrite : WriteRegsHyp (L := L) arI th s σ ct p buf args)
    (hCopy : CopyRegsHyp (L := L) arI th s σ ct p)
    -- the work of the extension labels
    (hA : ArgRel (st := st) s σ ct buf buffer 2)
    (hB : SetBpHyp (L := L) σ s ar p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don buffer)
    (hU : UnsetBpHyp (L := L) th s ct p) (hG : GetBpHyp (st := st) s ct p) (hS : SingleStepHyp (L := L) arI th s ct p)
    (hTm : SetTimerHyp (L := L) th s ct p)
    (hFr : FpuHyp (L := L) arI th s σ ct p ⟨length, buf, call, cslotAddr ssl, extra⟩ true)
    (hFw : FpuHyp (L := L) arI th s σ ct p ⟨length, buf, call, cslotAddr ssl, extra⟩ false)
    (hF : call = false → SetFlagsHyp (L := L) arI th s σ ct p ⟨length, buf, call, cslotAddr ssl, extra⟩)
    -- the decodes replying themselves, called
    (hGetCall : call = true → lbl = fl4_abi.label.TCBGetBreakpoint → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hStepCall : call = true → lbl = fl4_abi.label.TCBConfigureSingleStepping → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hFlagsCall : call = true → lbl = fl4_abi.label.TCBSetFlags → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    -- the scheduler-side labels
    (hSetPriority : lbl = fl4_abi.label.TCBSetPriority → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hSetMCPriority : lbl = fl4_abi.label.TCBSetMCPriority → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hSetSchedParams : lbl = fl4_abi.label.TCBSetSchedParams → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hSuspend : lbl = fl4_abi.label.TCBSuspend → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hResume : lbl = fl4_abi.label.TCBResume → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hBindNotification : lbl = fl4_abi.label.TCBBindNotification → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hUnbindNotification : lbl = fl4_abi.label.TCBUnbindNotification → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer) :
    TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hA1 : ArgRel (st := st) s σ ct buf buffer 1 := fun i hi => hA i (by omega)
  refine tcb_decode_cspace arI th hP hT s ar σ G hDS hFR lbl p hp slbl hlbl hNative hext length buf ct hct args hlen hargs hcur
    htcb hact hcw hstall' call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hnc blk don ci buffer hres hBuf hRead
    hWrite hCopy hSetPriority hSetMCPriority hSetSchedParams hSuspend hResume hBindNotification hUnbindNotification
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
      simp [tcbExtOf])
    exact tcb_set_bp_refines arI s ar σ p slbl hg he (hstall' p) _ blk call don _ ci ssl excaps buffer hB
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .getBreakpoint by
      simp [tcbExtOf])
    cases call
    · exact tcb_get_bp_refines arI th hP s ar σ G hDS hFR p slbl hg he length buf ct hct hcur htcb hact (hstall' p)
        buffer hA1 hG _ extra blk don _ ci ssl excaps
    · exact hGetCall rfl rfl
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
      simp [tcbExtOf])
    exact tcb_unset_bp_refines arI th hP s ar σ G hDS hFR p slbl hg he length buf ct hct hcur htcb hact (hstall' p)
      buffer hA1 hU call _ extra blk don _ ci ssl excaps
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .configureSingleStepping by
      simp [tcbExtOf])
    cases call
    · exact tcb_single_step_refines arI th hP s ar σ G hDS hFR p hp slbl hg he length buf ct hct hcur htcb hact (hstall' p)
        buffer hA hS _ extra blk don _ ci ssl excaps
    · exact hStepCall rfl rfl
  · rintro rfl
    cases call
    · exact tcb_set_flags_refines arI th hP s ar σ G hDS hFR p slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        args hlen hargs hcur htcb hact (hstall' p) _ extra (hF rfl) blk don ci ssl excaps buffer
    · exact hFlagsCall rfl rfl
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .readFpu by
      simp [tcbExtOf])
    exact tcb_fpu_refines arI th hP s ar σ G hDS hFR p true slbl hg he length buf ct hct args hlen hargs hcur htcb hact
      (hstall' p) call _ extra x0 x1 x2 hx0 excaps hX hFr blk don ci ssl buffer
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .writeFpu by
      simp [tcbExtOf])
    exact tcb_fpu_refines arI th hP s ar σ G hDS hFR p false slbl hg he length buf ct hct args hlen hargs hcur htcb hact
      (hstall' p) call _ extra x0 x1 x2 hx0 excaps hX hFw blk don ci ssl buffer
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setTimer by
      simp [tcbExtOf])
    exact tcb_set_timer_refines arI th hP s ar σ G hDS hFR p slbl hg he length buf ct hct args hlen hargs hcur htcb hact
      (hstall' p) hTm call _ extra blk don ci ssl excaps buffer

end

end

end Fl4Proofs.P3
