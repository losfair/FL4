/-
P3 (DESIGN.md §9), TCB invocations: **the CSpace TCB labels at `XTop`**
(TcbXLeaves' SetTimeoutEndpoint, SetSpace, SetIPCBuffer, Configure), by the
W-threading of ThreadControl's cap installs (TcbCaps' `*W` theorems, TcbCtl's
`tcb_*_refinesW`) at `WX`.

* `TopPostW.toX`: a `TopPostW` outcome at `WX` is a `TopPostDMX` outcome at
  `XTop`.
* `WX.restart`: `WX` after the caller's restart (`XTopAt.restart'`).
* `tcb_set_timeoutX`, `tcb_set_spaceX`, `tcb_set_ipcX`, `tcb_configureX`: the
  leaves (`TcbOKX` at `XTop`); the IPC-buffer step (`BufHypW` at `WX`) a
  premise of the last two.
-/
import Fl4Proofs.P3.XTopTcb
import Fl4Proofs.P3.TcbCtl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A `TopPostW` outcome at `WX` is a `TopPostDMX` outcome at `XTop`**
(the failure's state at `XTop` given). -/
theorem TopPostW.toX {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {ar : A}
    {res : core.result.Result Unit error.Exc × S × A} (hX0 : XTop (L := L) AR s ar σ)
    (h : TopPostW (L := L) (WX (L := L) AR th) th σ blk call don m s ar res) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don m s res := by
  obtain ⟨r, s', a'⟩ := res
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, G', h3, -, Z', -, -, hX', -, -⟩
  · simp only at h2 h3; subst h2 h3
    exact Or.inl ⟨e, h1, rfl, h4, hX0⟩
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, ⟨Z'.th, Z'.G, h3, hX'.rel.1, hX'.rel.2.1, hX'.rel.2.2.1, hX'.rel.2.2.2.1,
      hX'.rel.2.2.2.2.1⟩, ⟨Z', hX'⟩⟩

/-- **`WX` after the caller's restart.** -/
theorem WX.restart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) {ct : U64} (hcur : σ.curThread = ct.bv) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      WX (L := L) AR Z.th s1 ar σ1 Z.G := by
  intro s1 σ1 hs1 _ hst
  have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
  obtain ⟨hX1, hk1, -⟩ := hX.restart' hC hcur hs1 hst'
  exact ⟨Z, rfl, rfl, hX1, by rw [hk1]; exact hKA, hTh⟩

/-- The CSpace bound of the deletes (`TcHyps`' part): a bound `K` on CNode
sizes with the fuel enough for every ghost tree of the typed heap. -/
abbrev DelBound (th : TypedHeap) : Prop :=
  ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
    ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1

/-- **TcbXLeaves' SetTimeoutEndpoint at `XTop`.** Beyond
`tcb_set_timeout_refines`' premises: `XTopAt` with `KsApart`, the typed
heap's TCBs in `Z.T`, the caller runnable, `DelInv` [J], the deletion's
premises at `XTop` (`XFinHyps`, `XPreemptHyp`, `XPostDelHyp`) and the bound. -/
theorem tcb_set_timeoutX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTimeoutEndpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (args : List Fl4Spec.Data) (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetTimeoutEndpoint p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl args ci ssl excaps buffer :=
  WP.spec_mono (tcb_set_timeout_refinesW arI (WX (L := L) AR Z.th) Z.th hX.rel.1 (delHypsW_X arI hXF hXP hXD) hKB
    s ar σ Z.G ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩ p hp slbl hlbl length buf ct hct hcur (hX.curTcb hcur).1 hact hstall
    call ssl hAs extra x0 x1 x2 hx0 excaps hXc args blk don ci buffer (WX.restart hX hKA hC hTh hcur))
    fun _ h => h.toX ⟨Z, hX⟩

/-- **TcbXLeaves' SetSpace at `XTop`**, as `tcb_set_timeoutX`. -/
theorem tcb_set_spaceX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (p : U64) (hp : Z.th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSpace)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetSpace p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer :=
  WP.spec_mono (tcb_set_space_refinesW arI (WX (L := L) AR Z.th) Z.th hX.rel.1 (delHypsW_X arI hXF hXP hXD) hKB
    s ar σ Z.G ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩ p hp slbl hlbl length buf ct hct args hlen hargs hcur
    (hX.curTcb hcur).1 hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer
    (WX.restart hX hKA hC hTh hcur))
    fun _ h => h.toX ⟨Z, hX⟩

/-- **TcbXLeaves' SetIPCBuffer at `XTop`**, as `tcb_set_timeoutX`, with the
IPC-buffer step at `WX` (`BufHypW`). -/
theorem tcb_set_ipcX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (p : U64) (hp : Z.th p = some .tcb)
    (hBuf : ∀ v : U64, BufHypW (L := L) (WX (L := L) AR Z.th) Z.th p v v.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetIPCBuffer p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer :=
  WP.spec_mono (tcb_set_ipc_refinesW arI (WX (L := L) AR Z.th) Z.th hX.rel.1 (delHypsW_X arI hXF hXP hXD) hKB
    s ar σ Z.G ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩ p hp hBuf slbl hlbl length buf ct hct args hlen hargs hcur
    (hX.curTcb hcur).1 hact hstall call ssl hAs extra x0 x1 x2 hx0 excaps hXc hnc blk don ci buffer
    (WX.restart hX hKA hC hTh hcur))
    fun _ h => h.toX ⟨Z, hX⟩

/-- **TcbXLeaves' Configure at `XTop`** (its cap installs; MCS Configure has
no scheduling part), as `tcb_set_ipcX`. -/
theorem tcb_configureX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ)
    (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDI : DelInv Z.th (L.mem s))
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th) (hKB : DelBound Z.th)
    (p : U64) (hp : Z.th p = some .tcb)
    (hBuf : ∀ v : U64, BufHypW (L := L) (WX (L := L) AR Z.th) Z.th p v v.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBConfigure p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer :=
  WP.spec_mono (tcb_configure_refinesW arI (WX (L := L) AR Z.th) Z.th hX.rel.1 (delHypsW_X arI hXF hXP hXD) hKB
    s ar σ Z.G ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩ p hp hBuf slbl hlbl length buf ct hct args hlen hargs hcur
    (hX.curTcb hcur).1 hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer
    (WX.restart hX hKA hC hTh hcur))
    fun _ h => h.toX ⟨Z, hX⟩

end

end

end Fl4Proofs.P3
