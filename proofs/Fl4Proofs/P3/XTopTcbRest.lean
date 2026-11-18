/-
P3 (DESIGN.md §9), TCB invocations: **TcbXRest from the proved wrappers**
(`tcbXRest_of`), and the Thread cap's `XCap` at `XTop` with only the IPC/Sc
side's leaves, the labels still open and the [J]/[P] facts as premises
(`decode_invocation_threadXL`).

* Proved here from XTopTcbSched: SetMCPriority, SetTLSBase,
  UnsetBreakpoint; the decodes of Read/Write/CopyRegisters, SetPriority,
  SetSchedParams, Suspend, Resume, Bind/UnbindNotification over their
  leaves (`ReadRegsXHyp`, `WriteRegsXHyp`, `CopyRegsXHyp`, `SetPrioXLeaf`,
  `SchedTailXHyp`, `SuspendXLeaf`, `ResumeXLeaf`, `BindXLeaf`, `UnbindXLeaf`).
* `TcbXOpen`: FL4's debug, FPU, timer labels and SetFlags; its data labels
  (GetBreakpoint, ConfigureSingleStepping, SetFlags) are proved in
  XTopTcbData (`tcbXOpen_of`), the other four [W] (`TcbXOpen4`).
-/
import Fl4Proofs.P3.XTopTcbTls
import Fl4Proofs.P3.IpcSetPrioX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The Thread cap's labels still open** [W]: FL4's debug, FPU and timer
labels and SetFlags. -/
structure TcbXOpen (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop where
  setBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  getBreakpoint : lbl = fl4_abi.label.TCBGetBreakpoint →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  configureSingleStepping : lbl = fl4_abi.label.TCBConfigureSingleStepping →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  setFlags : lbl = fl4_abi.label.TCBSetFlags →
    TcbOKRX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer ct
  readFPU : lbl = fl4_abi.label.TCBReadFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  writeFPU : lbl = fl4_abi.label.TCBWriteFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setTimer : lbl = fl4_abi.label.TCBSetTimer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer

/-- **The IPC/Sc side's leaves of the Thread cap** [W], at the decode's
state: one per label whose invocation is theirs. -/
structure TcbXIpc (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (p ct buf : U64) (argsU : List U64) (blk call don : Bool) : Prop where
  readRegs : p ≠ ct → ReadRegsXHyp (L := L) arI AR s σ ct p blk call don
  writeRegs : WriteRegsXHyp (L := L) arI AR s σ ct p buf argsU blk call don
  copyRegs : CopyRegsXHyp (L := L) arI AR th s σ ct p blk call don
  setPrio : ∀ σ1 (v : U64), Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    v.val < 256 → SetPrioXLeaf (L := L) AR s ar σ σ1 p v
  schedTail : SchedTailXHyp (L := L) arI AR th s σ ct
  suspend : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    SuspendXLeaf (L := L) arI AR s ar σ σ1 p
  resume : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    ResumeXLeaf (L := L) arI AR s ar σ σ1 p
  bind : ∀ q, (∃ x b w r, IsSlot th x ∧ capV (L.mem s) x = .Notification q b w r) →
    L.mem s (P1.boundA p) = 0#u64 → L.mem s (Notif.nBoundA q) = 0#u64 → ∀ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    BindXLeaf (L := L) AR s ar σ σ1 p q
  unbind : L.mem s (P1.boundA p) ≠ 0#u64 → ∀ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    UnbindXLeaf (L := L) AR s ar σ σ1 p

set_option maxHeartbeats 4000000 in
/-- **`TcbXRest` from the wrappers**: the IPC/Sc leaves (`TcbXIpc`), the
labels still open (`TcbXOpen`) and the facts the decodes read:
`McpRel` [J] with the authority among `Z.T` [J], the SC cap's object in
`Z.C` and no null SC [J], the notification cap's in `Z.N` [J], the target
not the idle thread [J], `ArgRel` [J] for UnsetBreakpoint's argument,
`ActReady` at `WX` [J], `BufWordRel` (a per-`Z` relation), the core's `CUR_THREAD` word outside
the objects [J], the deletion premises at `XTop` and `DelBound`, the stall
the identity at every TCB [P]. -/
theorem tcbXRest_of [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (lbl length : U64) (p : U64) (hp : Z.th p = some .tcb)
    (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hM : McpRel Z.T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C) (hC0 : ∀ q ∈ Z.C, q ≠ 0#u64)
    (hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ Z.N)
    (hAr1 : ArgRel (st := st) s σ ct buf buffer 1)
    (hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don)
    (hO : TcbXOpen (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer ct) :
    TcbXRest (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hpT : p ∈ Z.T := hTh p hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hO.setBreakpoint, hO.getBreakpoint, ?_,
    hO.configureSingleStepping, ?_, hO.setFlags, hO.readFPU, hO.writeFPU, hO.setTimer⟩
  · rintro rfl
    exact tcb_read_regsX arI s ar σ hX hC hDI p slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
      hargs hcur hact (hstall' p) call _ extra blk don ci sl excaps buffer hI.readRegs
  · rintro rfl
    exact tcb_write_regsX arI s ar σ hX hC hDI p slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
      hargs hcur hact (hstall' p) call _ extra blk don ci sl excaps buffer hI.writeRegs
  · rintro rfl
    exact tcb_copy_regsX arI s ar σ hX hC hDI p slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
      hargs hcur hact (hstall' p) hstall' call sl extra x0 x1 x2 hx0 excaps hXc blk don ci buffer hI.copyRegs
  · rintro rfl
    exact tcb_set_prioX arI s ar σ hX hDI p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
      hargs hcur hact (hstall' p) call sl extra x0 x1 x2 hx0 excaps hXc hM hcapT hI.setPrio blk don ci buffer
  · rintro rfl
    exact tcb_set_mcpX arI s ar σ hX hC hDI p hp hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
      hlen hargs hcur hact (hstall' p) call sl extra x0 x1 x2 hx0 excaps hXc hM hcapT blk don ci buffer
  · rintro rfl
    exact tcb_set_sched_paramsX arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB p hp slbl
      (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hcur hact hpI (hstall' p) call sl hAs
      extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hM hcapT hcapC hC0 hI.schedTail blk don ci buffer
  · rintro rfl
    exact tcb_suspendX arI s ar σ ⟨Z, hX⟩ p slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) _ blk call don _ ci
      sl excaps buffer hI.suspend
  · rintro rfl
    exact tcb_resumeX arI s ar σ ⟨Z, hX⟩ p slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) _ blk call don _ ci
      sl excaps buffer hI.resume
  · rintro rfl
    exact tcb_bind_ntfnX arI s ar σ hX p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf (hstall' p) call _
      extra x0 x1 x2 hx0 excaps hXc hcapN blk don _ ci sl buffer (fun q _ hq => hI.bind q hq)
  · rintro rfl
    exact tcb_unbind_ntfnX arI s ar σ hX p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) length buf call _
      extra blk don _ ci sl excaps buffer hI.unbind
  · rintro rfl
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
      simp [tcbExtOf])
    exact tcb_unset_bpX arI s ar σ hX hC hDI p hpT slbl hg he length buf ct hct hcur hact (hstall' p) buffer hAr1
      call _ extra blk don _ ci sl excaps
  · rintro rfl
    exact tcb_set_tlsX arI s ar σ hX hKA hC hTh hA hBT hP0 p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
      argsU hlen hargs hcur hact hcw (hstall' p) call _ extra blk don ci sl excaps buffer

set_option maxHeartbeats 4000000 in
/-- **The Thread cap's `XCap` at `XTop`, every label, from the IPC/Sc
leaves** (`decode_invocation_threadXC` with `tcbXRest_of`): beyond the
CSpace labels' premises, `tcbXRest_of`'s. -/
theorem decode_invocation_threadXL [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (lbl length : U64) (p : U64) (hp : Z.th p = some .tcb)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hM : McpRel Z.T (L.mem s) σ) (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C) (hC0 : ∀ q ∈ Z.C, q ≠ 0#u64)
    (hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ Z.N)
    (hAr1 : ArgRel (st := st) s σ ct buf buffer 1)
    (hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don)
    (hO : TcbXOpen (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl (argsU.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct :=
  decode_invocation_threadXC arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB hA lbl length p hp blk call don fp buf
    extra ct hct hcur slbl hlbl argsU hlen hargs ci sl hAs excaps buffer hext (hstall' p) hNative hact x0 x1 x2 hx0
    hx1 hx2 hXc hnc hnc0
    (tcbXRest_of arI s ar σ hX hKA hC hTh hDI hXF hXP hXD hKB hA hBT hP0 lbl length p hp blk call don buf extra ct hct
      hcur slbl hlbl argsU hlen hargs ci sl hAs excaps buffer hext hstall' hact hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hM
      hcapT hcapC hC0 hcapN hAr1 hI hO)

end

end

end Fl4Proofs.P3
