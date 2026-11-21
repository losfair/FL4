/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **the Thread cap's decode
at `MachPlat`**: XTopJointTcb's `decode_invocation_threadJ_step` with the
five installing labels (SetTimeoutEndpoint, SetSpace, SetIPCBuffer,
Configure, SetSchedParams) by XTopJointMRTcb's copies at `WMR MR WJL` /
`WJPM`, so the Thread cap's decode ends in `XCapP JAt (JAtPreMV MR)` from
`MRV MR ar σ` at the decode's state and `MachPlat` [P] + `MRKeepD` [P] +
`PPPlatA` [P]: no `PPPlat`.

* `BufHypW.mrv`: TcbCaps' `BufHypW` at `W` gives it at `WMR MR W` (the IPC
  buffer's `threadSet` and the tail's `rescheduleRequired` keep `msFT`).
* `insWJ_wjlM`: XTopJointTcbInstall's `InsWJ` at `WMR MR WJL` (the insert's
  `capInsert` keeps `msFT`: `mtk_capInsert`); `tcbInsWM_wjl`: `TcbInsWM` at
  `WMR MR WJL` with XTopJointMRDel's `delHypsJLM`.
* `decode_invocation_threadJ_stepM` (generated: scratch/mr7/gentcbl.py +
  headTL.lean): the copy, with the caller's restart keeping `MRV`
  (`mtk_setThreadState'`) and `PPPlatA.minBudget` for `PPPlat.minBudget`.
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.XTopJointMRTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`BufHypW` with `MRV` beside the invariant** (module docstring). -/
theorem BufHypW.mrv {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t addr : U64}
    {ptr : Fl4Spec.VSpaceRef} (hM : MachPlat arI MR) (h : BufHypW (L := L) W th t addr ptr) :
    BufHypW (L := L) (WMR MR W) th t addr ptr := by
  refine ⟨fun s a σ G hDS hW hnull => ?_, fun s a σ G hDS hW => ?_⟩
  · refine WP.spec_mono (h.ipc s a σ G hDS hW.1 hnull) ?_
    rintro s' ⟨hSS, σ', hm, hCR, hK, hW'⟩
    exact ⟨hSS, σ', hm, hCR, hK, ⟨hW', mrv_keep hM hW.2 (MachT.mtk_threadSet' _ _ σ ((), σ') hm)⟩⟩
  · refine WP.spec_mono (h.tail s a σ G hDS hW.1) ?_
    rintro res ⟨h1, h2, hSS, σ', hm, hCR, hK, hW'⟩
    refine ⟨h1, h2, hSS, σ', hm, hCR, hK, ⟨hW', ?_⟩⟩
    rw [h2]
    exact mrv_keep hM hW.2 (dke_bind (dke_liftE (dk_gets _))
      (fun _ => dke_liftE (dk_when _ MachT.mtk_rescheduleRequired')) σ _ hm)

/-- **`InsWJ` at `WMR MR WJL`** (module docstring). -/
theorem insWJ_wjlM (hM : MachPlat arI MR) (kb : U64) :
    InsWJ (L := L) arI AR Z H Cs kb (WMR MR (WJL (L := L) arI AR Z H Cs kb)) := by
  have h0 := insWJ_wjl (L := L) arI (AR := AR) (Z := Z) (H := H) (Cs := Cs) kb
  refine ⟨fun s a σ G h => h0.wjr s a σ G h.1, ?_, fun t ht addr => (h0.buf t ht addr).mrv hM⟩
  intro s s' a σ σ' G G' t n c src hDS hW hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive
  exact ⟨h0.ins s s' a σ σ' G G' t n c src hDS hW.1 hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive,
    mrv_keep hM hW.2 (MachT.mtk_capInsert c src _ σ ((), σ') (mem_of_single hci))⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`TcbInsWM` at `WMR MR WJL`** (module docstring). -/
theorem tcbInsWM_wjl [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR Z.th) (hF : JThreadFinHypsU (L := L) arI AR Z.th)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) :
    TcbInsWM (L := L) arI AR MR Z H Cs (fun kb => WMR MR (WJL (L := L) arI AR Z H Cs kb))
      (RdLO (L := L) (A := A) Z.th H) (RzJ (L := L) (A := A) H) :=
  ⟨fun kb => insWJ_wjlM hM kb, fun kb => delHypsJLM arI hT hAR hK hV hF hnd hM hKD hPA hAM Z H Cs kb rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAt` after** (module docstring): every label proved at
`J` (no per-op `JPostHyp`, no X-level `TcbXIpc`). -/
theorem decode_invocation_threadJ_stepM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ Z.T := J.thT p hp
  -- WriteRegisters: the caller's buffer mapped (`lookup_buf_full`, `BufCover`), the arguments after its restart
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hctH : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ Z.T := J.thT ct hctH
  have hbm : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp := by
    intro hb0
    obtain ⟨x, hk, hwx⟩ := J.buf ct hctT
    have hL := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hctH hk (J.xferH.1) false
    rw [hbuf, WP.spec_ok] at hL
    cases hq : Endp.ipcBufOf false x with
    | none => exact absurd (hL.1.2 hq) hb0
    | some q => exact ⟨q, J.xferH.2.1 ct hctT x false q hk hq buf (hL.2 hwx q hq)⟩
  have hWR : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x := by
    intro s1 h1 i x hx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨sp, hsp⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
      by_cases hb : buf = 0#u64
      · exact ⟨0, fun h => absurd hb h⟩
      · obtain ⟨sp, h⟩ := hbm hb; exact ⟨sp, fun _ => h⟩
    rw [J.argsRestart (J.xferH.2.2) hctT hctH hsp (by omega) h1]
    exact hargs i x hx
  -- the cap installs' deletion at `J` (as `decode_invocation_cnodeJ_stepsL`)
  have hHp := tcbInsWM_wjl (L := L) (MR := MR) (Z := Z) (H := H) (Cs := Cs) arI hT hJDP.archRef hJDP.arKeep hJDP.vt
    hJDP.thr hnd hMP hKD hPA hARI.toMask
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hR : RestartWJ (st := st) Z s ar σ (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) :=
    fun _ hct s1 σ1 h1 h2 => ⟨WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2,
      mrv_keep hMP hmv (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single h2))⟩
  by_cases h9 : lbl = fl4_abi.label.TCBSetTimeoutEndpoint
  · subst h9
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_timeoutJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        (hstall' p) call sl hAs extra x0 x1 x2 hx0 excaps hXc _ blk don ci buffer)
  by_cases h11 : lbl = fl4_abi.label.TCBSetSpace
  · subst h11
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_spaceJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        argsU hlen hargs (hstall' p) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer)
  by_cases h10 : lbl = fl4_abi.label.TCBSetIPCBuffer
  · subst h10
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_ipcJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (hstall' p) call sl hAs extra x0 x1 x2 hx0 excaps hXc hnc0 hfnz blk don ci buffer)
  by_cases h5 : lbl = fl4_abi.label.TCBConfigure
  · subst h5
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_configureJM arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (hstall' p) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc hfnz blk don ci buffer)
  -- the first extra cap's thread among the TCBs (as `decode_invocation_threadJAt`)
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  by_cases h8 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst h8
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_sched_paramsJM arI s ar σ J hni hsg hP0 hHp hR hT hARI.toARKeep hTA p hp slbl
        (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hpI (hstall' p) call sl hAs hsc extra
        x0 x1 x2 hx0 hx1 hx2 excaps hXc hcapT hcapC blk don ci buffer)
  have hv : ∀ {c : U64}, lbl ≠ c → lbl.val ≠ c.val := fun hn e => hn (UScalar.eq_of_val_eq e)
  have hnpT := thread_noPre_of (fp := fp) (args := argsU.map UScalar.bv) (ci := ci) (sl := sl) (excaps := excaps)
    (buffer := buffer) (σ := σ) (p := p) hlbl
    ⟨by have := hv h5; simpa [fl4_abi.label.TCBConfigure] using this,
      by have := hv h8; simpa [fl4_abi.label.TCBSetSchedParams] using this,
      by have := hv h9; simpa [fl4_abi.label.TCBSetTimeoutEndpoint] using this,
      by have := hv h10; simpa [fl4_abi.label.TCBSetIPCBuffer] using this,
      by have := hv h11; simpa [fl4_abi.label.TCBSetSpace] using this⟩
  refine XCap.toPN arI (decode_invocation_threadX arI s ar σ hJ0 lbl length (cslotAddr sl) p blk call don fp buf extra
    ct hct slbl hlbl _ ci sl excaps buffer hext (hstall' p) hNative
    {
      readRegisters := fun h => by
        subst h
        exact tcb_read_regsJ arI s ar σ J hni p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf])
          length buf ct hct argsU hlen hargs (hstall' p) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      writeRegisters := fun h => by
        subst h
        exact tcb_write_regsJ arI hT hmb s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl
          (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hbm hWR (hstall' p) call
          (cslotAddr sl) extra blk don ci sl excaps buffer,
      copyRegisters := fun h => by
        subst h
        exact tcb_copy_regsJ arI hT hmb s ar σ J hni hidS p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf
          ct hct argsU hlen hargs hstall' call sl hAs hsc extra x0 x1 x2 hx0 excaps hXc blk don ci buffer,
      configure := fun h => absurd h h5,
      setPriority := fun h => by
        subst h
        exact tcb_set_prioJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
          hargs (hstall' p) call sl extra x0 x1 x2 hx0 excaps hXc hcapT blk don ci buffer,
      setMCPriority := fun h => by
        subst h
        exact tcb_set_mcpJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
          hargs (hstall' p) call sl extra x0 x1 x2 hx0 excaps hXc hcapT blk don ci buffer,
      setSchedParams := fun h => absurd h h8,
      setTimeoutEndpoint := fun h => absurd h h9,
      setIPCBuffer := fun h => absurd h h10,
      setSpace := fun h => absurd h h11,
      suspend := fun h => by
        subst h
        exact tcb_suspendJ arI s ar σ J hni p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct _
          blk call don _ ci sl excaps buffer,
      resume := fun h => by
        subst h
        exact tcb_resumeJ arI hT hPA.minBudget s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl
          (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct _ blk call don _ ci sl excaps buffer,
      bindNotification := fun h => by
        subst h
        exact tcb_bind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf (hstall' p) ct
          hct hAs.isSlot hsc call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc blk don _ ci sl buffer,
      unbindNotification := fun h => by
        subst h
        exact tcb_unbind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct
          length buf call (cslotAddr sl) extra blk don _ ci sl excaps buffer,
      setBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
          simp [tcbExtOf])
        exact tcb_set_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct (hstall' p) buffer hA5 call
          (cslotAddr sl) extra blk don _ ci sl excaps,
      getBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .getBreakpoint by
          simp [tcbExtOf])
        exact tcb_get_bpJ arI s ar σ J hni p slbl hg he length buf ct hct (hstall' p) buffer
          (fun i hi => hA5 i (by omega)) hGb call (cslotAddr sl) extra blk don _ ci sl excaps,
      unsetBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
          simp [tcbExtOf])
        exact tcb_unset_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct
          (hstall' p) buffer (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      configureSingleStepping := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf])
          (show tcbExtOf _ = some .configureSingleStepping by simp [tcbExtOf])
        exact tcb_single_stepJ arI s ar σ J hni p hp slbl hg he length buf ct hct (hstall' p) buffer
          (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      setTLSBase := fun h => by
        subst h
        exact tcb_set_tlsJ arI s ar σ J hni p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs hcw (hstall' p) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      setFlags := fun h => by
        subst h
        exact tcb_set_flagsJ arI s ar σ J hni hFl p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs (hstall' p) hARI.toARKeep call (cslotAddr sl) extra blk don ci sl excaps buffer,
      readFPU := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .readFpu by
          simp [tcbExtOf])
        exact tcb_read_fpuJ arI s ar σ J hni hARI.toARKeep p hpT slbl hg he length buf ct hct argsU hlen hargs
          (hstall' p) call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc (hFJ rfl) blk don ci sl buffer,
      writeFPU := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .writeFpu by
          simp [tcbExtOf])
        exact tcb_write_fpuJ arI s ar σ J hni hARI.toARKeep p hpT slbl hg he length buf ct hct argsU hlen hargs
          (hstall' p) call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc blk don ci sl buffer,
      setTimer := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setTimer by
          simp [tcbExtOf])
        exact tcb_set_timerJ arI s ar σ J hni p hpT slbl hg he length buf ct hct argsU hlen hargs (hstall' p) call
          (cslotAddr sl) extra blk don ci sl excaps buffer }) hnpT


end

end

end Fl4Proofs.P3
