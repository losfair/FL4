/-
P3 (DESIGN.md §9), TCB invocations, CSpace side: **the ThreadControl
labels** of `tcb::decode` (`TcbOK`) against l4v's decoders and
`invoke_tcb ThreadControlCaps`, through `thread_control_caps_refines`.

* The extra caps of the invocation (`XcRel`): FL4's three extra slots
  against the spec's looked-up extra caps (CNode slots, in order, `0` past
  the end).
* `valid_fault_handler` is the spec's `valid_fault_handler` (`vfh_eq`).
* The restart of the caller keeps `DState` (`restart_dstate`).
* An `InstPost` of `tcCapsSpec` after the restart is a `TopPost` outcome
  of the spec's ThreadControlCaps invocation (`top_of_inst`).
* SetTimeoutEndpoint (`tcb_set_timeout_refines`), SetIPCBuffer
  (`tcb_set_ipc_refines`, the buffer frame by `derive_cap` and
  `check_valid_ipc_buffer`), SetSpace (`tcb_set_space_refines`: the roots by
  `roots_rel`: `slot_cap_long_running_delete` (`lrd_rel`), `derive_with_data`
  (`dwd_rel`), the CNode and vtable checks; the fault handler) and
  Configure's cap installs (`tcb_configure_refines`, the buffer by
  `buf_rel`), all through `thread_control_caps_refines` (`tc_refines`).
* Read/Write/CopyRegisters (`tcb_read_regs_refines`,
  `tcb_write_regs_refines`, `tcb_copy_regs_refines`): the decode checks
  and the restart; the register and scheduler work is one hypothesis per
  label (`ReadRegsHyp`, `WriteRegsHyp`, `CopyRegsHyp`, over `RegPost`).
* `tcb_decode_cspace`: `tcb_decode_refines` with all of these discharged.
-/
import Fl4Proofs.P3.TcbTls
import Fl4Proofs.P3.VsTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem let_pair2 {α β γ : Type} (x : α) (y : β) (f : α → β → Result γ) (Q : γ → Prop)
    (h : f x y ⦃ res => Q res ⦄) : (let (s1, a1) := (x, y); f s1 a1) ⦃ res => Q res ⦄ := h

/-! ## Fault handlers -/

/-- FL4's `valid_fault_handler` is the spec's. -/
theorem vfh_eq (c : capability.Cap) :
    faults.valid_fault_handler c = ok (decide (Fl4Spec.validFaultHandler (absCap c))) := by
  cases c <;> simp [faults.valid_fault_handler, Fl4Spec.validFaultHandler, absCap, Fl4Spec.isEpCap,
    Fl4Spec.hasHandlerRights, Fl4Spec.capRights, rightsOf, Fl4Spec.AllowSend]
  rename_i w r g gr
  cases w <;> cases g <;> cases gr <;> simp [Set.eq_empty_iff_forall_notMem]


/-! ## The extra caps -/

/-- FL4's extra slots `x0 x1 x2` against the spec's extra caps: in order,
`0` past the end; each a CNode slot of the typed heap whose cap is the
spec's. -/
def XcRel (th : TypedHeap) (mem : U64 → U64) (x0 x1 x2 : U64) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    Prop :=
  excaps.length ≤ 3 ∧ ∀ (i : Nat) (x : U64), [x0, x1, x2][i]? = some x →
    (x = 0#u64 ↔ excaps.length ≤ i) ∧ ∀ e, excaps[i]? = some e →
      x = cslotAddr e.2 ∧ e.1 = absCap (capV mem x) ∧ ∃ ps, th ps = some (.cnode e.2.2.length) ∧ e.2.1 = ps.bv

theorem extra_eq (c : tcb.Ctx) (i : Usize) (hi : i.val < 3) {x : U64} (hx : Array.index_usize c.extra i = ok x) :
    tcb.extra c i = ok (if x = 0#u64 then none else some x) := by
  unfold tcb.extra
  rw [if_neg (by scalar_tac)]
  simp only [hx, is_null_eq, bind_ok]
  by_cases h : x = 0#u64 <;> simp [h]

/-- The extra cap `i` of an `XcRel`. -/
theorem XcRel.get {th : TypedHeap} {mem : U64 → U64} {x0 x1 x2 : U64} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (h : XcRel th mem x0 x1 x2 excaps) {i : Nat} {x : U64} (hx : [x0, x1, x2][i]? = some x) (hne : x ≠ 0#u64) :
    ∃ e, excaps[i]? = some e ∧ x = cslotAddr e.2 ∧ e.1 = absCap (capV mem x) ∧
      ∃ ps, th ps = some (.cnode e.2.2.length) ∧ e.2.1 = ps.bv := by
  obtain ⟨h1, h2⟩ := h.2 i x hx
  have hl : i < excaps.length := by
    by_contra hc; exact hne (h1.2 (by omega))
  exact ⟨excaps[i], List.getElem?_eq_getElem hl, h2 _ (List.getElem?_eq_getElem hl)⟩

/-- A slot's own cap, as the new cap of an install from that slot. -/
theorem newCapOK_self {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} (hR : StateRel th mem σ)
    (hV : SlotsValid th mem) {sl : Fl4Spec.CslotPtr} {ps : U64} (hps : th ps = some (.cnode sl.2.length))
    (h1 : sl.1 = ps.bv) (hnf : isFrame (capV mem (cslotAddr sl)) = false) :
    NewCapOK th mem (capV mem (cslotAddr sl)) sl := by
  obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode ps _ hps
  obtain ⟨c, a, hc, -, hrel⟩ := hs sl.2 rfl
  have hc' : capAt mem (cslotAddr sl) = ok c := by
    obtain ⟨o, i⟩ := sl; simp only at h1; subst h1; exact hc
  rw [capAt_capV] at hc'
  have e : capV mem (cslotAddr sl) = c := Result.ok_injective hc'
  have hA : AbsSlot th sl := ⟨ps, h1, Or.inl hps⟩
  refine ⟨ps, _, hps, h1, rfl, ?_, hV.abs hA (capAt_capV _ _), decode_encWf (w0 := mem (cslotAddr sl))
    (w1 := mem (core.num.U64.wrapping_add (cslotAddr sl) 8#u64)) ?_, (fun h => by rw [hnf] at h; cases h),
    rfl, Or.inl rfl, rfl, fun _ _ _ _ _ h => h⟩
  · rw [e]; exact hrel.1
  · have := capAt_capV mem (cslotAddr sl); unfold capAt at this; exact this

/-- The cap of a CNode slot of the typed heap is well-formed. -/
theorem slot_wf {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} (hR : StateRel th mem σ)
    {sl : Fl4Spec.CslotPtr} {ps : U64} (hps : th ps = some (.cnode sl.2.length)) (h1 : sl.1 = ps.bv) :
    CapWf (capV mem (cslotAddr sl)) ∧ EncWf (capV mem (cslotAddr sl)) := by
  obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode ps _ hps
  obtain ⟨c, a, hc, -, hrel⟩ := hs sl.2 rfl
  have hc' : capAt mem (cslotAddr sl) = ok c := by
    obtain ⟨o, i⟩ := sl; simp only at h1; subst h1; exact hc
  rw [capAt_capV] at hc'
  have e : capV mem (cslotAddr sl) = c := Result.ok_injective hc'
  refine ⟨by rw [e]; exact hrel.1, decode_encWf (w0 := mem (cslotAddr sl))
    (w1 := mem (core.num.U64.wrapping_add (cslotAddr sl) 8#u64)) ?_⟩
  have := capAt_capV mem (cslotAddr sl); unfold capAt at this; exact this

theorem isUt_of_match {c : capability.Cap} (h : match c with | .Untyped .. => True | _ => False) :
    isUt c = true := by
  cases c <;> simp_all [isUt]

/-! ## The restart -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The caller's restart keeps `DState`.** -/
theorem restart_dstate (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    ∃ s1 σ1, tcb.restart_caller st s = ok s1 ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      SlotsSame th (L.mem s) (L.mem s1) ∧ DState (L := L) th s1 σ1 G ∧ σ1.curThread = σ.curThread ∧
      L.ksb s1 = L.ksb s ∧ L.cpu s1 = L.cpu s := by
  obtain ⟨s1, hs1, hS1, hk1, hc1⟩ := spec_exists (WP.spec_and
    (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact) (set_thread_state_cpu s ct sched.TS_RESTART))
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hF⟩ := hDS
  obtain ⟨x, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS1 (t := ct.bv) hkt .restart
  refine ⟨s1, σ1, by unfold tcb.restart_caller; rw [hct]; simp only [bind_ok]; exact hs1, hs1,
    by rw [hcur]; exact hst1, hS1,
    DState.of_same ⟨⟨hR, hV, hM, hC, hI⟩, hD, hF⟩ hS1 ⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS1⟩
      (ksub_of_eq (setThreadState_nks _ _) hst1),
    by rw [setThreadState_curThread hkt hst1, hcur], hk1, hc1⟩

/-- The spec's ThreadControlCaps invocation of FL4's flags. -/
abbrev tcInv (t : U64) (ssl : Fl4Spec.CslotPtr) (flags : U64) (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (ptr : Fl4Spec.VSpaceRef) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr)) : Fl4Spec.Fl4Invocation :=
  .invokeTCB (.threadControlCaps t.bv ssl
    (optArg ((flags &&& tcb.UPDATE_FAULT) ≠ 0#u64) fh) (optArg ((flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) tmh)
    (optArg ((flags &&& tcb.UPDATE_SPACE) ≠ 0#u64) cr) (optArg ((flags &&& tcb.UPDATE_SPACE) ≠ 0#u64) vr)
    (if (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 then some (ptr, frameOf bfr) else none))

/-- **An install after the restart is a `TopPost` outcome** of the spec's
ThreadControlCaps invocation. -/
theorem top_of_inst {th : TypedHeap} (hP : Placed th) {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {t : U64} {ssl : Fl4Spec.CslotPtr} {flags : U64}
    {fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr} {ptr : Fl4Spec.VSpaceRef}
    {bfr : Option (capability.Cap × Fl4Spec.CslotPtr)} {s s1 : S} {res : core.result.Result Unit error.Exc × S × A}
    (hdec : DecOut m σ (tcInv t ssl flags fh tmh cr vr ptr bfr))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hkb : L.ksb s1 = L.ksb s)
    (h : InstPostQ (L := L) (MdbOKV (L.ksb s1)) th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s1 σ1 res) :
    TopPostM (L := L) σ blk call don m s res := by
  obtain ⟨σ', G', hc, hDS', hMO'⟩ := h
  rw [hkb] at hMO'
  refine Or.inr ⟨_, hdec, σ1, hst, ?_⟩
  rcases hc with ⟨hr, hx, -⟩ | ⟨hr, hx⟩
  · exact ⟨tcRet (.ok (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx, th, G', Or.inl ⟨hr, [], rfl⟩,
      hP, hDS'.1, hDS'.2.2, hMO'⟩
  · exact ⟨tcRet (.error (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx, th, G', Or.inr ⟨hr, rfl⟩,
      hP, hDS'.1, hDS'.2.2, hMO'⟩

/-- **A TCB decode's outcome with an invariant `W`** (the W-threading): the
error with the state and the arch state unchanged, or an outcome of the
spec's invocation after the restart (done with an empty result, or
preempted) with `DState` at the typed heap `th` and `W` after. -/
def TopPostW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (σ : Fl4Spec.State Unit)
    (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (s : S) (ar : A)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ res.2.2 = ar ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ G',
      ((res.1 = .Ok () ∧ y.1 = .ok []) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      DState (L := L) th res.2.1 y.2 G' ∧ W res.2.1 res.2.2 y.2 G')

/-- `TopPostW` at the MDB invariants gives `TopPostM`. -/
theorem TopPostW.toM {th : TypedHeap} (hP : Placed th) {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {ar : A}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostW (L := L) (WQ (L := L) (A := A) (MdbOKV (L.ksb s))) th σ blk call don m s ar res) :
    TopPostM (L := L) σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, -, h3⟩ | ⟨inv, h1, σ1, h2, y, hy, G', h3, hDS, hW⟩
  · exact Or.inl ⟨e, h1, h2, h3⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, th, G', ?_, hP, hDS.1, hDS.2.2, hW⟩
    rcases h3 with ⟨a, b⟩ | h
    · exact Or.inl ⟨a, [], b⟩
    · exact Or.inr h

/-- **An install after the restart is a `TopPostW` outcome** of the spec's
ThreadControlCaps invocation. -/
theorem top_of_instW {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {t : U64} {ssl : Fl4Spec.CslotPtr} {flags : U64}
    {fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr} {ptr : Fl4Spec.VSpaceRef}
    {bfr : Option (capability.Cap × Fl4Spec.CslotPtr)} {s s1 : S} {ar : A}
    {res : core.result.Result Unit error.Exc × S × A}
    (hdec : DecOut m σ (tcInv t ssl flags fh tmh cr vr ptr bfr))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : InstPostW (L := L) W th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s1 σ1 res) :
    TopPostW (L := L) W th σ blk call don m s ar res := by
  obtain ⟨σ', G', hc, hDS', hW'⟩ := h
  refine Or.inr ⟨_, hdec, σ1, hst, ?_⟩
  rcases hc with ⟨hr, hx, -⟩ | ⟨hr, hx⟩
  · exact ⟨tcRet (.ok (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx, G', Or.inl ⟨hr, rfl⟩, hDS', hW'⟩
  · exact ⟨tcRet (.error (), σ'), tcCapsSpec_mem t ssl flags fh tmh cr vr ptr bfr hx, G', Or.inr ⟨hr, rfl⟩, hDS', hW'⟩

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

end

/-! ## Constants -/

theorem cslot_zero : cslotAddr ((0 : BitVec 64), ([] : List Bool)) = 0#u64 := by
  simp [cslotAddr, slotAddr, Fl4Spec.ofBl]; rfl

theorem flags_T : ((tcb.UPDATE_TIMEOUT &&& tcb.UPDATE_FAULT) ≠ 0#u64) = False ∧
    ((tcb.UPDATE_TIMEOUT &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) = True ∧
    ((tcb.UPDATE_TIMEOUT &&& tcb.UPDATE_SPACE) ≠ 0#u64) = False ∧
    ((tcb.UPDATE_TIMEOUT &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64) = False := by
  simp only [tcb.UPDATE_TIMEOUT, tcb.UPDATE_FAULT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  decide

/-- A valid fault handler is null or an endpoint cap. -/
theorem vfh_ep {c : capability.Cap} (h : Fl4Spec.validFaultHandler (absCap c)) :
    c ≠ .Null → ∃ e b x1 x2 x3 x4, c = .Endpoint e b x1 x2 x3 x4 := by
  intro hn
  cases c <;> simp_all [absCap, Fl4Spec.validFaultHandler, Fl4Spec.isEpCap]

/-- A valid fault handler is no frame cap. -/
theorem vfh_not_frame {c : capability.Cap} (h : Fl4Spec.validFaultHandler (absCap c)) : isFrame c = false := by
  cases c <;> simp_all [isFrame, absCap, Fl4Spec.validFaultHandler, Fl4Spec.isEpCap]


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The deletion hypotheses of `thread_control_caps_refines`. -/
def TcHyps (th : TypedHeap) : Prop :=
  FinObjHyp (L := L) arI th ∧ PPHypD (L := L) arI th ∧ PostDelHyp (L := L) arI th ∧
    ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
      ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1

theorem tc_refinesW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th)
    (hH : DelHypsW (L := L) arI W th)
    (hKB : ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
      ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : W s a σ G)
    (t : U64) (ht : th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) vr.1 vr.2)
    (hfhE : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → fh.1 ≠ .Null →
      ∃ e b x1 x2 x3 x4, fh.1 = .Endpoint e b x1 x2 x3 x4)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHypW (L := L) W th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s) c sl) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPostW (L := L) W th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ := by
  obtain ⟨K, hK, hK6, hB⟩ := hKB
  exact thread_control_caps_refinesW arI W th hP hH K hK hK6 hB s a σ G hDS hMO t ht ssl hAs flags fh tmh cr vr
    hfh htmh hcr hvr hfhE addr ptr hBuf bc0 bfr hbfr


theorem tc_refines [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    (t : U64) (ht : th t = some .tcb) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl) (flags : U64)
    (fh tmh cr vr : capability.Cap × Fl4Spec.CslotPtr)
    (hfh : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → NewCapOK th (L.mem s) fh.1 fh.2)
    (htmh : (flags &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64 → NewCapOK th (L.mem s) tmh.1 tmh.2)
    (hcr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) cr.1 cr.2)
    (hvr : (flags &&& tcb.UPDATE_SPACE) ≠ 0#u64 → NewCapOK th (L.mem s) vr.1 vr.2)
    (hfhE : (flags &&& tcb.UPDATE_FAULT) ≠ 0#u64 → fh.1 ≠ .Null →
      ∃ e b x1 x2 x3 x4, fh.1 = .Endpoint e b x1 x2 x3 x4)
    (addr : U64) (ptr : Fl4Spec.VSpaceRef)
    (hBuf : (flags &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64 → BufHyp (L := L) (A := A) th t addr ptr)
    (bc0 : capability.Cap) (bfr : Option (capability.Cap × Fl4Spec.CslotPtr))
    (hbfr : ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s) c sl) :
    tcb.thread_control_caps st arI s a t (cslotAddr ssl) (fh.1, cslotAddr fh.2) (tmh.1, cslotAddr tmh.2)
      (cr.1, cslotAddr cr.2) (vr.1, cslotAddr vr.2) addr (bufArg bc0 bfr) flags ⦃ res =>
      InstPostQ (L := L) (MdbOKV (L.ksb s)) th t (tcCapsSpec t ssl flags fh tmh cr vr ptr bfr) s σ res ⦄ := by
  obtain ⟨hO, hPP, hPD, K, hK, hK6, hB⟩ := hT
  exact thread_control_caps_mdbOK arI th hP hO hPP hPD K hK hK6 hB s a σ G hDS hMO t ht ssl hAs flags fh tmh cr vr
    hfh htmh hcr hvr hfhE addr ptr hBuf bc0 bfr hbfr

theorem decode_timeout_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetTimeoutEndpoint p c =
      tcb.decode_set_timeout_endpoint st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBSetTimeoutEndpoint`** (`TcbOK`): l4v's
`decode_set_timeout_ep`, the restart and `invoke_tcb ThreadControlCaps`
installing the timeout handler. -/
theorem tcb_set_timeout_refinesW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th) (hH : DelHypsW (L := L) arI W th)
    (hKB : ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
      ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTimeoutEndpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (args : List Fl4Spec.Data) (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hWr : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W s1 ar σ1 G) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetTimeoutEndpoint p ⟨length, buf, call, cslotAddr ssl, extra⟩ ⦃ res =>
      TopPostW (L := L) W th σ blk call don (specDec false slbl args ci ssl (.Thread p) excaps buffer) s ar res ⦄ := by
  have hdec0 : specDec false slbl args ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_timeout_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_timeout_endpoint tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTimeoutEp
    rw [whenE_pos (by omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 0#u64 := by scalar_tac
  simp only [h0, ↓reduceIte, if_pos hge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, slot_cap_eq,
    capAt_capV, vfh_eq]
  have hspec0 : ∀ v : Prop, [Decidable v] → v = Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0)) →
      (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps).run σ =
        (Fl4Spec.checkHandlerEp (Z := Unit) 1 e >>= fun handler =>
          Fl4Spec.NonDetE.returnOk (.threadControlCaps p.bv ssl none (some handler) none none none)).run σ := by
    intro v _ _
    unfold Fl4Spec.decodeSetTimeoutEp
    rw [whenE_neg (by have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega),
      retOk_bind, retOk_bind, he, the_some]
    rfl
  by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0))
  · rw [decide_eq_true hv]; simp only [↓reduceIte]
    obtain ⟨s1, σ1, hrc, hsts, hst1, hS1, hDS1, -, hkb1, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : W s1 ar σ1 G := hWr s1 σ1 hsts hS1 hst1
    rw [hrc]; simp only [bind_ok]
    have hxs : IsSlot th x0 := by rw [hxe]; exact AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTimeoutEp (Z := Unit) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.ok (tcInv p ssl tcb.UPDATE_TIMEOUT (.Null, (0, [])) (capV (L.mem s) x0, e.2) (.Null, (0, []))
          (.Null, (0, [])) (0 : BitVec 64) none), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec0 _ rfl]
      unfold Fl4Spec.checkHandlerEp
      rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he1]; exact hv)]
      show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e) >>= _).run σ = _
      rw [retOk_bind, retOk_bind]
      obtain ⟨e1, e2⟩ := e
      simp only at he1
      subst he1
      simp only [tcInv, optArg, flags_T, ↓reduceIte]
      rfl
    have hcs := cslot_zero
    have hnf := vfh_not_frame hv
    have hc1 : capV (L.mem s1) x0 = capV (L.mem s) x0 := hS1.capV hxs
    have hT' := tc_refinesW arI W th hP hH hKB s1 ar σ1 G hDS1 hfr1 p hp ssl hAs (hfhE := fun _ h => absurd rfl h) tcb.UPDATE_TIMEOUT (.Null, (0, []))
      (capV (L.mem s) x0, e.2) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_T.1 h).elim)
      (fun _ => by
        show NewCapOK th (L.mem s1) (capV (L.mem s) x0) e.2
        rw [← hc1, hxe]
        exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps hps1 (by rw [← hxe, hc1]; exact hnf))
      (fun h => (Eq.mp flags_T.2.2.1 h).elim) (fun h => (Eq.mp flags_T.2.2.1 h).elim) 0#u64 0
      (fun h => (Eq.mp flags_T.2.2.2 h).elim) .Null none (fun _ _ h => by cases h)
    simp only [cslot_zero, ← hxe] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instW (DecOut.of_eq hdec) hst1 h)
  · rw [decide_eq_false hv]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, rfl, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩
    apply run_liftME_err
    rw [hspec0 _ rfl]
    unfold Fl4Spec.checkHandlerEp
    rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he1]; exact hv)]
    exact run_bind_error (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
      Fl4Spec.SEMonad Unit Unit)) rfl _) _


theorem tcb_set_timeout_refines [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTimeoutEndpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (args : List Fl4Spec.Data) (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetTimeoutEndpoint p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl args ci ssl excaps buffer := by
  obtain ⟨hO, hPP, hPD, hKB⟩ := hT
  exact WP.spec_mono (tcb_set_timeout_refinesW arI (WQ (L := L) (MdbOKV (L.ksb s))) th hP (delHypsW_Q arI (MdbOKV.step _) hO hPP hPD) hKB
    s ar σ G hDS  (hWr := fun _ _ _ hS _ => MdbOKV.of_same hDS.1.2.2.1 hS hFR) p hp slbl hlbl length buf ct hct hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 excaps hX args blk don ci buffer)
    fun _ h => h.toM hP

end


/-! ## The IPC buffer's cap -/

theorem flags_B : ((tcb.UPDATE_IPC_BUFFER &&& tcb.UPDATE_FAULT) ≠ 0#u64) = False ∧
    ((tcb.UPDATE_IPC_BUFFER &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) = False ∧
    ((tcb.UPDATE_IPC_BUFFER &&& tcb.UPDATE_SPACE) ≠ 0#u64) = False ∧
    ((tcb.UPDATE_IPC_BUFFER &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64) = True := by
  simp only [tcb.UPDATE_TIMEOUT, tcb.UPDATE_FAULT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  decide

theorem ErrRel.of_map {e : error.Exc} {e' : Fl4Spec.SyscallError} (h : Vs.MapErrRel e e') : ErrRel e e' := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h
  · exact Or.inl trivial

theorem bv_le_add_pow (x : BitVec 64) (n : Nat) (hn : n < 64) (h : x.toNat % 2 ^ n = 0) :
    x ≤ x + 2 ^ n - 1 := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
  have h64 : 2 ^ 64 = 2 ^ n * 2 ^ (64 - n) := by rw [← Nat.pow_add]; congr 1; omega
  have hq' : q < 2 ^ (64 - n) := by
    have := x.isLt; rw [hq, h64] at this; exact Nat.lt_of_mul_lt_mul_left this
  have hb : x.toNat + 2 ^ n ≤ 2 ^ 64 := by
    rw [hq, h64]
    calc 2 ^ n * q + 2 ^ n = 2 ^ n * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ 2 ^ n * 2 ^ (64 - n) := Nat.mul_le_mul_left _ hq'
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hpn : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have t1 : (1 : BitVec 64).toNat = 1 := rfl
  have t2 : (2 : BitVec 64).toNat = 2 := rfl
  have e : ((2 : BitVec 64) ^ n).toNat = 2 ^ n := by
    rw [BitVec.toNat_pow, t2]; exact Nat.mod_eq_of_lt hpn
  rw [BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_add, e, t1]
  generalize 2 ^ n = N at hp hpn hb ⊢
  have := x.isLt
  simp only [Nat.reducePow] at *
  omega

/-- An aligned frame cap is the same object as itself (its frame does not
wrap). -/
theorem frame_so_refl {th : TypedHeap} {p : U64} {sz : capability.FrameSize} {r : U64} {d m : Bool} {a va : U64}
    (h : CapValid th (.Frame p sz r d m false a va)) :
    Fl4Spec.sameObjectAs (absCap (.Frame p sz r d m false a va)) (absCap (.Frame p sz r d m false a va)) := by
  have hal : p.val % 2 ^ frameBitsN sz = 0 := h
  rw [← UScalar.bv_toNat] at hal
  simp only [absCap, Fl4Spec.sameObjectAs, Fl4Spec.sameAobjectAs, true_and]
  cases sz
  · exact bv_le_add_pow _ 12 (by decide) hal
  · exact bv_le_add_pow _ 21 (by decide) hal
  · exact bv_le_add_pow _ 30 (by decide) hal

/-- A cap that passes `check_valid_ipc_buffer` is a non-device frame. -/
theorem check_ok_frame {vptr : U64} {c : capability.Cap} (h : vspace.check_valid_ipc_buffer vptr c = ok (.Ok ())) :
    ∃ p sz r m ep a va, c = .Frame p sz r false m ep a va := by
  cases c <;> simp [vspace.check_valid_ipc_buffer, error.illegal] at h
  case Frame p sz r d m ept a va =>
    cases d
    · exact ⟨p, sz, r, m, ept, a, va, rfl⟩
    · simp at h

/-- `derive_cap` to a frame cap: the frame of the source, unmapped. -/
theorem derive_frame_inv {S : Type} {st : machine.Store S} {s : S} {slot : obj.Slot} {c : capability.Cap}
    {p : U64} {sz : capability.FrameSize} {r : U64} {d m ep : Bool} {a va : U64}
    (hnc : isUt c = true → ∃ x, cdt.ensure_no_children st s slot = ok x)
    (h : objects.derive_cap st s slot c = ok (.Ok (.Frame p sz r d m ep a va))) :
    ep = false ∧ ∃ m0 ep0 a0 va0, c = .Frame p sz r d m0 ep0 a0 va0 := by
  cases c <;> simp [objects.derive_cap] at h
  case Untyped =>
    obtain ⟨x, hx⟩ := hnc rfl
    rw [hx] at h
    cases x <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  case Frame =>
    obtain ⟨rfl, rfl, rfl, rfl, -, hep, -⟩ := h
    exact ⟨hep, _, _, _, _, rfl⟩
  all_goals (split at h <;> simp at h)


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem decode_ipc_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetIPCBuffer p c =
      tcb.decode_set_ipc_buffer st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBSetIPCBuffer`** (`TcbOK`): l4v's
`decode_set_ipc_buffer` (the buffer's frame cap derived and checked), the
restart and `invoke_tcb ThreadControlCaps` installing the buffer; the
buffer's word and the scheduler are P1's (`BufHyp`, for every address). -/
theorem tcb_set_ipc_refinesW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th) (hH : DelHypsW (L := L) arI W th)
    (hKB : ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
      ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (p : U64) (hp : th p = some .tcb) (hBuf : ∀ v : U64, BufHypW (L := L) W th p v v.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hWr : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W s1 ar σ1 G) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetIPCBuffer p ⟨length, buf, call, cslotAddr ssl, extra⟩ ⦃ res =>
      TopPostW (L := L) W th σ blk call don (specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer) s ar res ⦄ := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_ipc_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_ipc_buffer tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  -- the truncated cases
  have htr : args = [] ∨ excaps = [] →
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.error .truncatedMessage, σ)}, False) := by
    intro h
    apply run_liftME_err
    unfold Fl4Spec.decodeSetIpcBuffer
    by_cases ha : args = []
    · subst ha
      rw [whenE_pos (by simp)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · have he : excaps = [] := h.resolve_left ha
      subst he
      rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (by simp)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
  have htrS : ∀ (P : Prop) (res : core.result.Result Unit error.Exc × S × A), res = (.Err (.Sys .TruncatedMessage), s, ar) →
      (args = [] ∨ excaps = []) → TopPostW (L := L) W th σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s ar res := by
    rintro - res rfl h
    exact Or.inl ⟨_, rfl, rfl, rfl, .truncatedMessage, htr h, Or.inl trivial⟩
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (htrS True _ rfl (Or.inr (List.eq_nil_of_length_eq_zero (by omega))))
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hX.get hx0' h0
  by_cases h1 : length < 1#u64
  · have hge : ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 := by
      show ¬ length >= 1#u64; scalar_tac
    simp only [h0, ↓reduceIte, if_neg hge, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (htrS True _ rfl (Or.inl ?_))
    exact List.eq_nil_of_length_eq_zero (by scalar_tac)
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 := by
    show length >= 1#u64; scalar_tac
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  simp only [h0, ↓reduceIte, if_pos hge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  -- the spec, up to the buffer
  obtain ⟨e1, e2⟩ := e
  simp only at hxe he1 hps hps1
  subst he1 hxe
  have hspec : (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      excaps).run σ =
      ((if y0.bv = 0 then Fl4Spec.NonDetE.returnOk none else do
          let bc ← Fl4Spec.deriveCap (Z := Unit) e2 (absCap (capV (L.mem s) (cslotAddr e2)))
          Fl4Spec.checkValidIpcBuffer y0.bv bc
          Fl4Spec.NonDetE.returnOk (some (bc, e2)) : Fl4Spec.SEMonad Unit _) >>= fun nb =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none none none
          (some (y0.bv, nb)))).run σ := by
    unfold Fl4Spec.decodeSetIpcBuffer
    have hne : excaps ≠ [] := List.ne_nil_of_mem (List.mem_of_getElem? he)
    rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simpa using hne), retOk_bind, retOk_bind]
    rw [show (List.map UScalar.bv (y0 :: rest))[0]? = some y0.bv from rfl, the_some, retOk_bind, he, the_some]
    rfl
  obtain ⟨s1, σ1, hrc, hsts, hst1, hS1, hDS1, -, hkb1, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
  have hfr1 : W s1 ar σ1 G := hWr s1 σ1 hsts hS1 hst1
  have hxs : IsSlot th (cslotAddr e2) := AbsSlot.isSlot ⟨ps, hps1, Or.inl hps⟩
  have hc1 : capV (L.mem s1) (cslotAddr e2) = capV (L.mem s) (cslotAddr e2) := hS1.capV hxs
  have hcwf := slot_wf hDS.1.1 hps hps1
  have hcv0 : CapValid th (capV (L.mem s) (cslotAddr e2)) :=
    hDS.1.2.1.abs ⟨ps, hps1, Or.inl hps⟩ (capAt_capV _ _)
  by_cases hy : y0 = 0#u64
  · -- no frame
    have hy' : y0.bv = 0 := by rw [hy]; rfl
    have hdfb : tcb.derive_for_buffer st s y0 (cslotAddr e2) = ok (.Ok (capV (L.mem s) (cslotAddr e2), 0#u64)) := by
      unfold tcb.derive_for_buffer; rw [if_pos hy]; simp [slot_cap_eq, capAt_capV]
    rw [hdfb]; simp only [bind_ok, hrc]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl excaps)).run σ =
        ({(.ok (tcInv p ssl tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
          (.Null, (0, [])) y0.bv none), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec, if_pos hy', retOk_bind]
      simp only [tcInv, optArg, flags_B, ↓reduceIte, frameOf]
      rfl
    have hT' := tc_refinesW arI W th hP hH hKB s1 ar σ1 G hDS1 hfr1 p hp ssl hAs (hfhE := fun _ h => absurd rfl h) tcb.UPDATE_IPC_BUFFER (.Null, (0, []))
      (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_B.1 h).elim)
      (fun h => (Eq.mp flags_B.2.1 h).elim) (fun h => (Eq.mp flags_B.2.2.1 h).elim)
      (fun h => (Eq.mp flags_B.2.2.1 h).elim) y0 y0.bv (fun _ => hBuf y0) (capV (L.mem s) (cslotAddr e2)) none
      (fun _ _ h => by cases h)
    simp only [cslot_zero, bufArg] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instW (DecOut.of_eq hdec) hst1 h)
  -- a frame: derived and checked
  have hy' : ¬ y0.bv = 0 := fun h => hy (UScalar.eq_of_val_eq (by
    have := congrArg BitVec.toNat h; simpa using this))
  unfold tcb.derive_for_buffer
  rw [if_neg hy]
  simp only [slot_cap_eq, capAt_capV, bind_ok]
  generalize capV (L.mem s) (cslotAddr e2) = c0 at hcwf hcv0 hc1 hnc hspec ⊢
  obtain ⟨r, hr, r', hr', hrel⟩ := derive_rel (st := st) s σ (cslotAddr e2) e2 c0
    hcwf.1 hcwf.2 (fun h => hnc e2 rfl (by cases c0 <;> simp_all [isUt]))
  simp only [hr, bind_ok]
  cases r with
  | Err er =>
    cases r' with
    | ok _ => exact hrel.elim
    | error er' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, er', ?_, Or.inl hrel⟩)
      apply run_liftME_err
      rw [hspec, if_neg hy']
      exact run_bind_error (run_bind_error hr' _) _
  | Ok c' =>
    cases r' with
    | error _ => exact hrel.elim
    | ok a =>
      obtain ⟨hwf', ha, hev', hcv', -⟩ := hrel
      obtain ⟨rc, hrc', hcase⟩ := Vs.check_valid_ipc_buffer_rel y0 c' σ
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hrc']
      rcases hcase with ⟨rfl, hck⟩ | ⟨er, er', rfl, hmer, hck⟩
      · simp only [bind_ok, hrc]
        obtain ⟨q, sz, rr, m, ep, aa, va, rfl⟩ := check_ok_frame hrc'
        obtain ⟨rfl, m0, ep0, a0, va0, hc0⟩ := derive_frame_inv (fun h => ⟨_, hnc e2 rfl h⟩) hr
        have hcvc : CapValid th (capability.Cap.Frame q sz rr false m false aa va) := hcv' th hcv0
        have hok : NewCapOK th (L.mem s1) (.Frame q sz rr false m false aa va) e2 := by
          refine ⟨ps, _, hps, hps1, rfl, hwf', hcvc, hev', fun _ => frame_so_refl hcvc, ?_, ?_, ?_, ?_⟩
          · rw [hc1, hc0]; rfl
          · rw [hc1, hc0]; exact Or.inl rfl
          · rw [hc1, hc0]; rfl
          · rw [hc1]; exact derive_vcap hr
        have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
            (Fl4Spec.decodeSetIpcBuffer (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
              excaps)).run σ =
            ({(.ok (tcInv p ssl tcb.UPDATE_IPC_BUFFER (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, []))
              (.Null, (0, [])) y0.bv (some (.Frame q sz rr false m false aa va, e2))), σ)}, False) := by
          apply run_liftME_ok
          rw [← ha] at hr'
          have hin : ((do
              let bc ← Fl4Spec.deriveCap (Z := Unit) e2 (absCap c0)
              Fl4Spec.checkValidIpcBuffer y0.bv bc
              Fl4Spec.NonDetE.returnOk (some (bc, e2)) : Fl4Spec.SEMonad Unit _)).run σ =
              ({(.ok (some (absCap (.Frame q sz rr false m false aa va), e2)), σ)}, False) := by
            rw [run_bind_ok hr', run_bind_ok hck]; rfl
          rw [hspec, if_neg hy', run_bind_ok hin]
          simp only [tcInv, optArg, flags_B, ↓reduceIte, frameOf]
          rfl
        have hT' := tc_refinesW arI W th hP hH hKB s1 ar σ1 G hDS1 hfr1 p hp ssl hAs (hfhE := fun _ h => absurd rfl h) tcb.UPDATE_IPC_BUFFER (.Null, (0, []))
          (.Null, (0, [])) (.Null, (0, [])) (.Null, (0, [])) (fun h => (Eq.mp flags_B.1 h).elim)
          (fun h => (Eq.mp flags_B.2.1 h).elim) (fun h => (Eq.mp flags_B.2.2.1 h).elim)
          (fun h => (Eq.mp flags_B.2.2.1 h).elim) y0 y0.bv (fun _ => hBuf y0) .Null
          (some (.Frame q sz rr false m false aa va, e2)) (fun c sl h => by cases h; exact hok)
        simp only [cslot_zero, bufArg] at hT'
        exact WP.spec_mono hT' (fun res h => top_of_instW (DecOut.of_eq hdec) hst1 h)
      · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, er', ?_, ErrRel.of_map hmer⟩)
        apply run_liftME_err
        rw [hspec, if_neg hy']
        rw [← ha] at hr'
        exact run_bind_error ((run_bind_ok hr' _).trans (run_bind_error hck _)) _


theorem tcb_set_ipc_refines [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (hBuf : ∀ v : U64, BufHyp (L := L) (A := A) th p v v.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetIPCBuffer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetIPCBuffer p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  obtain ⟨hO, hPP, hPD, hKB⟩ := hT
  exact WP.spec_mono (tcb_set_ipc_refinesW arI (WQ (L := L) (MdbOKV (L.ksb s))) th hP (delHypsW_Q arI (MdbOKV.step _) hO hPP hPD) hKB
    s ar σ G hDS (hBuf := fun v => (hBuf v).w (MdbOKV.step _)) (hWr := fun _ _ _ hS _ => MdbOKV.of_same hDS.1.2.2.1 hS hFR) p hp slbl hlbl length buf ct hct args hlen hargs hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 excaps hX hnc blk don ci buffer)
    fun _ h => h.toM hP

end


/-! ## SetSpace and Configure: the roots -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`slot_cap_long_running_delete` of a TCB slot** is the spec's. -/
theorem lrd_rel (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots) :
    ∃ b, cdt.slot_cap_long_running_delete st s (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = ok b ∧
      Fl4Spec.slotCapLongRunningDelete (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(b, σ)}, False) := by
  have hA : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  obtain ⟨c, a, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  have ha := hca.abs
  subst ha
  unfold cdt.slot_cap_long_running_delete Fl4Spec.slotCapLongRunningDelete
  rw [slot_cap_eq, hc, nd_bind_one hg]
  simp only [bind_ok]
  by_cases hnull : c = .Null
  · subst hnull
    exact ⟨false, by simp [capability.Cap.is_null], rfl⟩
  obtain ⟨b', hb', hnf, -⟩ := finalHyp_full th hP s σ G _ c hDS hA hc hnull
  rw [is_final_with_cap_eq _ _ _ hc, hb']
  cases c
  case Null => exact absurd rfl hnull
  case CNode p r gs g =>
    have e := hnf (Or.inr (Or.inl ⟨p, r, gs, g, rfl⟩))
    refine ⟨b', by cases b' <;> simp [capability.Cap.is_null], ?_⟩
    simp only [absCap, Fl4Spec.isFinalCap, Notif.nd_gets_bind, Fl4Spec.longRunningDelete, Bool.and_true]
    rw [e]; rfl
  case Thread p =>
    have e := hnf (Or.inl ⟨trivial, rfl⟩)
    refine ⟨b', by cases b' <;> simp [capability.Cap.is_null], ?_⟩
    simp only [absCap, Fl4Spec.isFinalCap, Notif.nd_gets_bind, Fl4Spec.longRunningDelete, Bool.and_true]
    rw [e]; rfl
  case Zombie p zt nn =>
    have e := hnf (Or.inr (Or.inr rfl))
    refine ⟨b', by cases b' <;> simp [capability.Cap.is_null], ?_⟩
    simp only [absCap, Fl4Spec.isFinalCap, Notif.nd_gets_bind, Fl4Spec.longRunningDelete, Bool.and_true]
    rw [e]; rfl
  all_goals
    refine ⟨false, by simp [capability.Cap.is_null], ?_⟩
    simp only [absCap, Fl4Spec.isFinalCap, Notif.nd_gets_bind, Fl4Spec.longRunningDelete, Bool.and_false]
    try split_ifs
    all_goals rfl

end


/-- `update_cap_data`: what a CNode, PML4 or untyped result came from. -/
theorem upd_inv {pr : Bool} {w : U64} {c0 c1 : capability.Cap} (h : objects.update_cap_data pr w c0 = ok c1) :
    (∀ p r gs g, c1 = .CNode p r gs g → ∃ gs0 g0, c0 = .CNode p r gs0 g0) ∧
    (∀ p m a, c1 = .Pml4 p m a → c0 = c1) ∧ (isUt c1 = true → c0 = c1) := by
  cases c0 <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    rw [shr_eq w 6#i32 (by decide) (by decide), mask_eq] at h
    simp only [bind_ok] at h
    split at h
    · have := Result.ok_injective h; subst this; simp [isUt]
    · have := Result.ok_injective h; subst this
      refine ⟨fun p' r' gs' g' e => ?_, fun p' m a e => (by cases e), fun hu => (by simp [isUt] at hu)⟩
      cases e; exact ⟨_, _, rfl⟩
  all_goals
    first
    | (have := Result.ok_injective h; subst this; simp [isUt])
    | (split at h <;> (have := Result.ok_injective h; subst this; simp [isUt]))
    | (split at h <;> (try split at h) <;> (have := Result.ok_injective h; subst this; simp [isUt]))


/-- `derive_cap` to a CNode or PML4 cap: the source cap itself. -/
theorem derive_root_inv {S : Type} {st : machine.Store S} {s : S} {slot : obj.Slot} {c c' : capability.Cap}
    (hnc : isUt c = true → ∃ x, cdt.ensure_no_children st s slot = ok x)
    (h : objects.derive_cap st s slot c = ok (.Ok c')) :
    (∀ p r gs g, c' = .CNode p r gs g → c = c') ∧ (∀ p m a, c' = .Pml4 p m a → c = c') := by
  cases c <;> simp only [objects.derive_cap] at h
  case Untyped =>
    obtain ⟨x, hx⟩ := hnc rfl
    rw [hx] at h
    cases x <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    subst h; exact ⟨fun _ _ _ _ e => (by cases e), fun _ _ _ e => (by cases e)⟩
  all_goals
    first
    | (have := Result.ok_injective h; cases this
       refine ⟨fun _ _ _ _ e => ?_, fun _ _ _ e => ?_⟩ <;> first | rfl | cases e)
    | (split at h <;> (have := Result.ok_injective h; cases this) <;>
       refine ⟨fun _ _ _ _ e => ?_, fun _ _ _ e => ?_⟩ <;> first | rfl | cases e)

/-- `derive_with_data` against the spec's `derive_cap` of the (maybe
updated) cap: a related cap (a CNode or PML4 result from the same object),
or a related error. -/
def DwdRel (c0 : capability.Cap) : core.result.Result capability.Cap error.Exc →
    Except Fl4Spec.SyscallError Fl4Spec.Cap → Prop
  | .Ok c', .ok a => CapWf c' ∧ absCap c' = a ∧ EncWf c' ∧ (∀ th, CapValid th c0 → CapValid th c') ∧
      (∀ p r gs g, c' = .CNode p r gs g → ∃ gs0 g0, c0 = .CNode p r gs0 g0) ∧
      (∀ p m a, c' = .Pml4 p m a → c0 = c')
  | .Err e, .error e' => SysErrRel e e'
  | _, _ => False

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem dwd_rel (s : S) (σ : Fl4Spec.State Unit) (slot : U64) (sl : Fl4Spec.CslotPtr) (c0 : capability.Cap)
    (hcap : capAt (L.mem s) slot = ok c0) (hc : CapWf c0) (he : EncWf c0)
    (hnc : isUt c0 = true → NoChildrenRel (st := st) s σ slot sl) (data : U64) :
    ∃ r, tcb.derive_with_data st s slot data = ok r ∧ ∃ r',
      (Fl4Spec.deriveCap (Z := Unit) sl ((if data.bv = 0 then id else Fl4Spec.updateCapData false data.bv)
        (absCap c0))).run σ = ({(r', σ)}, False) ∧ DwdRel c0 r r' := by
  unfold tcb.derive_with_data
  rw [slot_cap_eq, hcap]
  simp only [bind_ok]
  by_cases hd : data = 0#u64
  · have hd' : data.bv = 0 := by rw [hd]; rfl
    simp only [hd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    obtain ⟨r, hr, r', hr', hrel⟩ := derive_rel (Z := Unit) (st := st) s σ slot sl c0 hc he
      (fun h => hnc (by cases c0 <;> simp_all [isUt]))
    refine ⟨r, hr, r', by simp only [show U64.bv 0#u64 = 0 from rfl, ↓reduceIte, id]; exact hr', ?_⟩
    cases r <;> cases r' <;> simp only [DeriveRel, DwdRel] at hrel ⊢
    · have hinv := derive_root_inv (fun h => ⟨_, hnc h⟩) hr
      obtain ⟨h1, h2, h3, h4, -⟩ := hrel
      refine ⟨h1, h2, h3, h4, fun p r gs g e => ⟨gs, g, (hinv.1 p r gs g e).trans e⟩,
        fun p m a e => hinv.2 p m a e⟩
    · exact hrel
  · have hd' : ¬ data.bv = 0 := fun h => hd (UScalar.eq_of_val_eq (by
      have := congrArg BitVec.toNat h; simpa using this))
    obtain ⟨c1, hu, hw1, ha1, he1, hcv1, -⟩ := update_rel false data c0 hc he
    have hui := upd_inv hu
    simp only [bne_iff_ne, ne_eq, hd, not_false_eq_true, ↓reduceIte, hu, bind_ok, hd']
    rw [← ha1]
    obtain ⟨r, hr, r', hr', hrel⟩ := derive_rel (Z := Unit) (st := st) s σ slot sl c1 hw1 he1
      (fun h => hnc (by
        have hu1 : isUt c1 = true := by cases c1 <;> simp_all [isUt]
        rw [hui.2.2 hu1]; exact hu1))
    refine ⟨r, hr, r', hr', ?_⟩
    cases r <;> cases r' <;> simp only [DeriveRel, DwdRel] at hrel ⊢
    · have hinv := derive_root_inv (fun h => ⟨_, hnc (by rw [hui.2.2 h]; exact h)⟩) hr
      obtain ⟨h1, h2, h3, h4, -⟩ := hrel
      refine ⟨h1, h2, h3, fun th h => h4 th (hcv1 th h), fun p r gs g e => ?_, fun p m a e => ?_⟩
      · exact hui.1 p r gs g ((hinv.1 p r gs g e).trans e)
      · rw [hui.2.1 p m a ((hinv.2 p m a e).trans e)]; exact hinv.2 p m a e
    · exact hrel

end


theorem tcb_slot_ct (t : U64) :
    obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 0)) := by
  rw [spec_eq_ok (tcb_slot_spec t _), tcb_root_eq t _ (n := 0) (by decide) (by simp [layout.tcb.SLOT_CTABLE])]

theorem tcb_slot_vt (t : U64) :
    obj.Tcb.slot t layout.tcb.SLOT_VTABLE = ok (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 1)) := by
  rw [spec_eq_ok (tcb_slot_spec t _), tcb_root_eq t _ (n := 1) (by decide) (by simp [layout.tcb.SLOT_VTABLE])]

theorem is_cnode_eq (c : capability.Cap) : tcb.is_cnode c = ok (Fl4Spec.isCnodeCap (absCap c)) := by
  cases c <;> simp [tcb.is_cnode, absCap, Fl4Spec.isCnodeCap]

theorem liftM_not_run {m : Fl4Spec.NonDet (Fl4Spec.State Unit) Bool} {σ : Fl4Spec.State Unit} {b : Bool}
    (h : m σ = ({(b, σ)}, False)) :
    (Fl4Spec.NonDetE.liftE (ε := Fl4Spec.SyscallError) (Fl4Spec.NonDet.liftM not m)).run σ =
      ({(.ok (!b), σ)}, False) :=
  run_liftE (by unfold Fl4Spec.NonDet.liftM; exact (Notif.nd_bind_one' h _).trans rfl)

/-- The spec's `decode_cv_space` of two arguments and two extra caps, after
its long-running-delete checks. -/
theorem cv_spec (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (slot : Fl4Spec.CslotPtr) (cd vd : Fl4Spec.Data)
    (ec ev : Fl4Spec.Cap × Fl4Spec.CslotPtr) (b0 b1 : Bool)
    (hs0 : Fl4Spec.slotCapLongRunningDelete (Z := Unit) (p, Fl4Spec.tcbCnodeIndex 0) σ = ({(b0, σ)}, False))
    (hs1 : Fl4Spec.slotCapLongRunningDelete (Z := Unit) (p, Fl4Spec.tcbCnodeIndex 1) σ = ({(b1, σ)}, False)) :
    (Fl4Spec.decodeCvSpace (Z := Unit) [cd, vd] (.threadCap p) slot [ec, ev]).run σ =
      if b0 = true ∨ b1 = true then ({(.error .illegalOperation, σ)}, False) else
      ((do
        let c' ← Fl4Spec.deriveCap ec.2 ((if cd = 0 then id else Fl4Spec.updateCapData false cd) ec.1)
        Fl4Spec.NonDetE.unlessE (Fl4Spec.isCnodeCap c') (Fl4Spec.NonDetE.throwError .illegalOperation)
        let v' ← Fl4Spec.deriveCap ev.2 ((if vd = 0 then id else Fl4Spec.updateCapData false vd) ev.1)
        Fl4Spec.NonDetE.unlessE (Fl4Spec.isValidVtableRoot v') (Fl4Spec.NonDetE.throwError .illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p slot none none (some (c', ec.2))
          (some (v', ev.2)) none) : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation)).run σ := by
  unfold Fl4Spec.decodeCvSpace
  rw [whenE_neg (by simp)]
  simp only [retOk_bind, List.getElem?_cons_zero, List.getElem?_cons_succ, the_some, Fl4Spec.getTcbCtablePtr,
    Fl4Spec.getTcbVtablePtr, Fl4Spec.objRefOf]
  rw [run_bind_ok (liftM_not_run hs0), run_bind_ok (liftM_not_run hs1)]
  unfold Fl4Spec.NonDetE.unlessE
  by_cases h : b0 = true ∨ b1 = true
  · rw [if_pos h, if_neg (by cases b0 <;> cases b1 <;> simp_all)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  · rw [if_neg h, if_pos (by cases b0 <;> cases b1 <;> simp_all)]
    show ((pure () : Fl4Spec.SEMonad Unit Unit) >>= _).run σ = _
    rw [show (pure () : Fl4Spec.SEMonad Unit Unit) = Fl4Spec.NonDetE.returnOk () from rfl, retOk_bind]


theorem cnode_of_abs {c : capability.Cap} (h : Fl4Spec.isCnodeCap (absCap c) = true) :
    ∃ p r gs g, c = .CNode p r gs g := by
  cases c <;> simp [absCap, Fl4Spec.isCnodeCap] at h
  exact ⟨_, _, _, _, rfl⟩

theorem pml4_of_abs {c : capability.Cap} (h : Fl4Spec.isValidVtableRoot (absCap c)) :
    ∃ q a, c = .Pml4 q true a := by
  cases c <;> simp [absCap, Fl4Spec.isValidVtableRoot] at h
  case Pml4 q m a => cases m <;> simp at h; exact ⟨_, _, rfl⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's `derive_roots` is the spec's `decode_cv_space`** (two arguments,
two extra caps): the derived CSpace and VSpace roots, each a new cap of an
install from its slot (`NewCapOK`), or the same error. -/
theorem roots_rel (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (p : U64) (hp : th p = some .tcb) (cdata vdata : U64)
    (ec ev : Fl4Spec.Cap × Fl4Spec.CslotPtr)
    (hec : ec.1 = absCap (capV (L.mem s) (cslotAddr ec.2)))
    (hecs : ∃ ps, th ps = some (.cnode ec.2.2.length) ∧ ec.2.1 = ps.bv)
    (hev : ev.1 = absCap (capV (L.mem s) (cslotAddr ev.2)))
    (hevs : ∃ ps, th ps = some (.cnode ev.2.2.length) ∧ ev.2.1 = ps.bv)
    (hncc : isUt (capV (L.mem s) (cslotAddr ec.2)) = true → NoChildrenRel (st := st) s σ (cslotAddr ec.2) ec.2)
    (hncv : isUt (capV (L.mem s) (cslotAddr ev.2)) = true → NoChildrenRel (st := st) s σ (cslotAddr ev.2) ev.2)
    (slot : Fl4Spec.CslotPtr) :
    ∃ r, tcb.derive_roots st s p cdata vdata (cslotAddr ec.2) (cslotAddr ev.2) = ok r ∧
      ((∃ cc vc, r = .Ok (cc, vc) ∧
          (Fl4Spec.decodeCvSpace (Z := Unit) [cdata.bv, vdata.bv] (.threadCap p.bv) slot [ec, ev]).run σ =
            ({(.ok (.threadControlCaps p.bv slot none none (some (absCap cc, ec.2)) (some (absCap vc, ev.2))
              none), σ)}, False) ∧
          NewCapOK th (L.mem s) cc ec.2 ∧ NewCapOK th (L.mem s) vc ev.2) ∨
       (∃ e e', r = .Err e ∧
          (Fl4Spec.decodeCvSpace (Z := Unit) [cdata.bv, vdata.bv] (.threadCap p.bv) slot [ec, ev]).run σ =
            ({(.error e', σ)}, False) ∧ ErrRel e e')) := by
  obtain ⟨b0, hb0, hs0⟩ := lrd_rel th hP s σ G hDS p hp 0 (by decide)
  obtain ⟨b1, hb1, hs1⟩ := lrd_rel th hP s σ G hDS p hp 1 (by decide)
  have hcv := cv_spec σ p.bv slot cdata.bv vdata.bv ec ev b0 b1 hs0 hs1
  unfold tcb.derive_roots
  rw [tcb_slot_ct]; simp only [bind_ok]; rw [hb0]
  simp only [bind_ok]
  by_cases h0 : b0 = true
  · simp only [h0, ↓reduceIte, error.illegal]
    exact ⟨_, rfl, Or.inr ⟨_, .illegalOperation, rfl, by rw [hcv, if_pos (Or.inl h0)], Or.inl trivial⟩⟩
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  rw [tcb_slot_vt]; simp only [bind_ok]; rw [hb1]; simp only [bind_ok]
  by_cases h1 : b1 = true
  · simp only [h1, ↓reduceIte, error.illegal]
    exact ⟨_, rfl, Or.inr ⟨_, .illegalOperation, rfl, by rw [hcv, if_pos (Or.inr h1)], Or.inl trivial⟩⟩
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp_all)] at hcv
  obtain ⟨psc, hpsc, hpsc1⟩ := hecs
  obtain ⟨psv, hpsv, hpsv1⟩ := hevs
  have hwc := slot_wf hDS.1.1 hpsc hpsc1
  have hwv := slot_wf hDS.1.1 hpsv hpsv1
  have hvc : CapValid th (capV (L.mem s) (cslotAddr ec.2)) :=
    hDS.1.2.1.abs ⟨psc, hpsc1, Or.inl hpsc⟩ (capAt_capV _ _)
  have hvv : CapValid th (capV (L.mem s) (cslotAddr ev.2)) :=
    hDS.1.2.1.abs ⟨psv, hpsv1, Or.inl hpsv⟩ (capAt_capV _ _)
  obtain ⟨rc, hrc, rc', hrc', hrelc⟩ := dwd_rel s σ (cslotAddr ec.2) ec.2 _ (capAt_capV _ _) hwc.1 hwc.2 hncc cdata
  rw [hrc]
  rw [← hec] at hrc'
  have ill : ∀ {α : Type} (k : Unit → Fl4Spec.SEMonad Unit α),
      ((Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation : Fl4Spec.SEMonad Unit Unit) >>= k).run σ =
        ({(.error .illegalOperation, σ)}, False) := fun k =>
    run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl k
  cases rc with
  | Err e =>
    cases rc' with
    | ok _ => exact hrelc.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact ⟨_, rfl, Or.inr ⟨e, e', rfl, by rw [hcv]; exact run_bind_error hrc' _, Or.inl hrelc⟩⟩
  | Ok c' =>
    cases rc' with
    | error _ => exact hrelc.elim
    | ok a =>
      obtain ⟨hw', ha', he', hcv', hcn, -⟩ := hrelc
      subst ha'
      rw [run_bind_ok hrc'] at hcv
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, is_cnode_eq]
      unfold Fl4Spec.NonDetE.unlessE at hcv
      by_cases hcn' : Fl4Spec.isCnodeCap (absCap c') = true
      · simp only [hcn', ↓reduceIte] at hcv ⊢
        rw [show (pure () : Fl4Spec.SEMonad Unit Unit) = Fl4Spec.NonDetE.returnOk () from rfl, retOk_bind] at hcv
        obtain ⟨rv, hrv, rv', hrv', hrelv⟩ := dwd_rel s σ (cslotAddr ev.2) ev.2 _ (capAt_capV _ _) hwv.1 hwv.2 hncv
          vdata
        rw [hrv]
        rw [← hev] at hrv'
        have hokc : NewCapOK th (L.mem s) c' ec.2 := by
          obtain ⟨q, r, gs, g, rfl⟩ := cnode_of_abs hcn'
          obtain ⟨gs0, g0, hc0⟩ := hcn _ _ _ _ rfl
          refine ⟨psc, _, hpsc, hpsc1, rfl, hw', hcv' th hvc, he', fun h => (by cases h), ?_, ?_, ?_, ?_⟩ <;>
            rw [hc0]
          · rfl
          · exact Or.inl rfl
          · rfl
          · exact fun _ _ _ _ _ _ => trivial
        cases rv with
        | Err e =>
          cases rv' with
          | ok _ => exact hrelv.elim
          | error e' =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok]
            exact ⟨_, rfl, Or.inr ⟨e, e', rfl, by rw [hcv]; exact run_bind_error hrv' _, Or.inl hrelv⟩⟩
        | Ok v' =>
          cases rv' with
          | error _ => exact hrelv.elim
          | ok av =>
            obtain ⟨hwv', hav, hev', hcvv', -, hpm⟩ := hrelv
            subst hav
            rw [run_bind_ok hrv'] at hcv
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Vs.is_valid_vtable_root_eq]
            by_cases hvr : Fl4Spec.isValidVtableRoot (absCap v')
            · simp only [hvr, decide_true, ↓reduceIte] at hcv ⊢
              rw [retOk_bind] at hcv
              have hokv : NewCapOK th (L.mem s) v' ev.2 := by
                obtain ⟨q, aa, rfl⟩ := pml4_of_abs hvr
                have hv0 := hpm _ _ _ rfl
                refine ⟨psv, _, hpsv, hpsv1, rfl, hwv', hcvv' th hvv, hev', fun h => (by cases h), ?_, ?_, ?_, ?_⟩ <;>
                  rw [hv0]
                · exact Or.inl rfl
                · exact fun _ _ _ _ _ h => h
              exact ⟨_, rfl, Or.inl ⟨c', v', rfl, hcv, hokc, hokv⟩⟩
            · simp only [hvr, decide_false, Bool.false_eq_true, ↓reduceIte, error.illegal] at hcv ⊢
              exact ⟨_, rfl, Or.inr ⟨_, .illegalOperation, rfl, by rw [hcv]; exact ill _, Or.inl trivial⟩⟩
      · simp only [hcn', Bool.false_eq_true, ↓reduceIte, error.illegal] at hcv ⊢
        exact ⟨_, rfl, Or.inr ⟨_, .illegalOperation, rfl, by rw [hcv]; exact ill _, Or.inl trivial⟩⟩

end


theorem NewCapOK.of_same {th : TypedHeap} {m m' : U64 → U64} {c : capability.Cap} {sl : Fl4Spec.CslotPtr}
    (hS : SlotsSame th m m') (h : NewCapOK th m c sl) : NewCapOK th m' c sl := by
  obtain ⟨ps, rs, hps, h1, hl, hw, hv, he, hf, hsh, hbd, hk, hvk⟩ := h
  have hx : IsSlot th (cslotAddr sl) := AbsSlot.isSlot ⟨ps, h1, Or.inl (hl ▸ hps)⟩
  rw [← hS.capV hx] at hsh hbd hk hvk
  exact ⟨ps, rs, hps, h1, hl, hw, hv, he, hf, hsh, hbd, hk, hvk⟩

theorem flags_SF : (((tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) &&& tcb.UPDATE_FAULT) ≠ 0#u64) = True ∧
    (((tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) = False ∧
    (((tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) &&& tcb.UPDATE_SPACE) ≠ 0#u64) = True ∧
    (((tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64) = False := by
  simp only [tcb.UPDATE_TIMEOUT, tcb.UPDATE_FAULT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  decide

theorem flags_SB : (((tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) &&& tcb.UPDATE_FAULT) ≠ 0#u64) = False ∧
    (((tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) &&& tcb.UPDATE_TIMEOUT) ≠ 0#u64) = False ∧
    (((tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) &&& tcb.UPDATE_SPACE) ≠ 0#u64) = True ∧
    (((tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) &&& tcb.UPDATE_IPC_BUFFER) ≠ 0#u64) = True := by
  simp only [tcb.UPDATE_TIMEOUT, tcb.UPDATE_FAULT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The untyped extra caps' MDB condition (`NoChildrenRel`, for
`derive_cap` of an untyped cap). -/
def NcHyp (s : S) (σ : Fl4Spec.State Unit) (x0 x1 x2 : U64) : Prop :=
  ∀ x ∈ [x0, x1, x2], ∀ sl : Fl4Spec.CslotPtr, x = cslotAddr sl → isUt (capV (L.mem s) x) = true →
    NoChildrenRel (st := st) s σ x sl

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem decode_space_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetSpace p c = tcb.decode_set_space st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBSetSpace`** (`TcbOK`): l4v's `decode_set_space`
(the roots' checks and derivations, `decode_cv_space`, and the fault
handler), the restart and `invoke_tcb ThreadControlCaps` installing the
fault handler and the roots. -/
theorem tcb_set_space_refinesW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th) (hH : DelHypsW (L := L) arI W th)
    (hKB : ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
      ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (p : U64) (hp : th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSpace)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hWr : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W s1 ar σ1 G) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetSpace p ⟨length, buf, call, cslotAddr ssl, extra⟩ ⦃ res =>
      TopPostW (L := L) W th σ blk call don (specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer) s ar res ⦄ := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetSpace (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_space_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 2 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostW (L := L) W th σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSpace (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s ar res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetSpace
    rw [whenE_pos (by simpa using h)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  unfold tcb.decode_set_space tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 2#u64 ↔ 2 ≤ args.length := by
    show length >= 2#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 2 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hl with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexc : excaps = [e0, e1, e2] := by
    have h3 := hX.1
    match excaps, he0, he1, he2, h3 with
    | [a, b, c], h0', h1', h2', _ => simp at h0' h1' h2'; rw [h0', h1', h2']
  subst hexc
  subst hxe1 hxe2
  obtain ⟨r, hr, hcase⟩ := roots_rel th hP s σ G hDS p hp y0 y1 e1 e2 he11 ⟨ps1, hps1, hps11⟩ he21
    ⟨ps2, hps2, hps21⟩ (hnc _ (by simp) e1.2 rfl) (hnc _ (by simp) e2.2 rfl) ssl
  rw [hr]
  have hspec : (Fl4Spec.decodeSetSpace (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
      [e0, e1, e2]).run σ =
      (Fl4Spec.decodeCvSpace (Z := Unit) [y0.bv, y1.bv] (.threadCap p.bv) ssl [e1, e2] >>= fun space =>
        Fl4Spec.checkHandlerEp (Z := Unit) 1 e0 >>= fun fh =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl (some fh) none
            space.tcNewCroot space.tcNewVroot none)).run σ := by
    unfold Fl4Spec.decodeSetSpace
    rw [whenE_neg (by simp), retOk_bind]
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, the_some, retOk_bind]
    rfl
  rcases hcase with ⟨cc, vc, rfl, hcv, hokc, hokv⟩ | ⟨e, e', rfl, hcv, herr⟩
  · simp only [slot_cap_eq, capAt_capV, vfh_eq, bind_ok]
    rw [run_bind_ok hcv] at hspec
    by_cases hv : Fl4Spec.validFaultHandler (absCap (capV (L.mem s) x0))
    · rw [decide_eq_true hv]; simp only [↓reduceIte, lift, bind_ok]
      obtain ⟨s1, σ1, hrc, hsts, hst1, hS1, hDS1, -, hkb1, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
      have hfr1 : W s1 ar σ1 G := hWr s1 σ1 hsts hS1 hst1
      rw [hrc]; simp only [bind_ok]
      have hxs : IsSlot th x0 := by rw [hxe0]; exact AbsSlot.isSlot ⟨ps0, hps01, Or.inl hps0⟩
      have hc1 : capV (L.mem s1) x0 = capV (L.mem s) x0 := hS1.capV hxs
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetSpace (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            [e0, e1, e2])).run σ =
          ({(.ok (tcInv p ssl (tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT) (capV (L.mem s) x0, e0.2) (.Null, (0, []))
            (cc, e1.2) (vc, e2.2) (0 : BitVec 64) none), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec]
        unfold Fl4Spec.checkHandlerEp
        rw [Fl4Spec.NonDetE.unlessE, if_pos (by rw [he01]; exact hv)]
        show ((Fl4Spec.NonDetE.returnOk () >>= fun _ => Fl4Spec.NonDetE.returnOk e0) >>= _).run σ = _
        rw [retOk_bind, retOk_bind]
        obtain ⟨e01, e02⟩ := e0
        simp only at he01
        subst he01
        simp only [optArg, flags_SF, ↓reduceIte]
        rfl
      have hT' := tc_refinesW arI W th hP hH hKB s1 ar σ1 G hDS1 hfr1 p hp ssl hAs (hfhE := fun _ => vfh_ep hv) (tcb.UPDATE_SPACE ||| tcb.UPDATE_FAULT)
        (capV (L.mem s) x0, e0.2) (.Null, (0, [])) (cc, e1.2) (vc, e2.2)
        (fun _ => by
          show NewCapOK th (L.mem s1) (capV (L.mem s) x0) e0.2
          rw [← hc1, hxe0]
          exact newCapOK_self hDS1.1.1 hDS1.1.2.1 hps0 hps01 (by rw [← hxe0, hc1]; exact vfh_not_frame hv))
        (fun h => (Eq.mp flags_SF.2.1 h).elim) (fun _ => hokc.of_same hS1) (fun _ => hokv.of_same hS1)
        0#u64 0 (fun h => (Eq.mp flags_SF.2.2.2 h).elim) .Null none (fun _ _ h => by cases h)
      simp only [cslot_zero, ← hxe0, bufArg] at hT'
      exact WP.spec_mono hT' (fun res h => top_of_instW (DecOut.of_eq hdec) hst1 h)
    · rw [decide_eq_false hv]; simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 ?_
      apply Or.inl
      refine ⟨_, rfl, rfl, rfl, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩
      apply run_liftME_err
      rw [hspec]
      unfold Fl4Spec.checkHandlerEp
      rw [Fl4Spec.NonDetE.unlessE, if_neg (by rw [he01]; exact hv)]
      exact run_bind_error (run_bind_error (m := (Fl4Spec.NonDetE.throwError
        (Fl4Spec.SyscallError.invalidCapability 1) : Fl4Spec.SEMonad Unit Unit)) rfl _) _
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, e', ?_, herr⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error hcv _


theorem tcb_set_space_refines [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetSpace)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetSpace p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  obtain ⟨hO, hPP, hPD, hKB⟩ := hT
  exact WP.spec_mono (tcb_set_space_refinesW arI (WQ (L := L) (MdbOKV (L.ksb s))) th hP (delHypsW_Q arI (MdbOKV.step _) hO hPP hPD) hKB
    s ar σ G hDS  (hWr := fun _ _ _ hS _ => MdbOKV.of_same hDS.1.2.2.1 hS hFR) p hp slbl hlbl length buf ct hct args hlen hargs hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hnc blk don ci buffer)
    fun _ h => h.toM hP

end


/-- The spec's IPC-buffer frame of `decode_set_ipc_buffer`: none for a zero
address, else the derived and checked frame cap. -/
noncomputable def bufSpec (v : Fl4Spec.Data) (e : Fl4Spec.Cap × Fl4Spec.CslotPtr) :
    Fl4Spec.SEMonad Unit (Option (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :=
  if v = 0 then Fl4Spec.NonDetE.returnOk none else do
    let bc ← Fl4Spec.deriveCap (Z := Unit) e.2 e.1
    Fl4Spec.checkValidIpcBuffer v bc
    Fl4Spec.NonDetE.returnOk (some (bc, e.2))

theorem ipc_spec (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (ssl : Fl4Spec.CslotPtr) (y : Fl4Spec.Data)
    (rest : List Fl4Spec.Data) (e : Fl4Spec.Cap × Fl4Spec.CslotPtr) (erest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    (Fl4Spec.decodeSetIpcBuffer (Z := Unit) (y :: rest) (.threadCap p) ssl (e :: erest)).run σ =
      (bufSpec y e >>= fun nb => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p ssl none none
        none none (some (y, nb)))).run σ := by
  unfold Fl4Spec.decodeSetIpcBuffer bufSpec
  rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simp), retOk_bind, retOk_bind]
  simp only [List.getElem?_cons_zero, the_some, Fl4Spec.dataToVref, retOk_bind]
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's `derive_for_buffer` is the spec's buffer frame** (`bufSpec`):
FL4's buffer argument of `thread_control_caps` (`bufArg`), a new cap of an
install (`NewCapOK`) if a frame, or the same error. -/
theorem buf_rel (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (y : U64) (e : Fl4Spec.Cap × Fl4Spec.CslotPtr)
    (he1 : e.1 = absCap (capV (L.mem s) (cslotAddr e.2)))
    (hes : ∃ ps, th ps = some (.cnode e.2.2.length) ∧ e.2.1 = ps.bv)
    (hnc : isUt (capV (L.mem s) (cslotAddr e.2)) = true → NoChildrenRel (st := st) s σ (cslotAddr e.2) e.2) :
    ∃ r, tcb.derive_for_buffer st s y (cslotAddr e.2) = ok r ∧
      ((∃ bc0 bfr, r = .Ok (bufArg bc0 bfr) ∧ (bufSpec y.bv e).run σ = ({(.ok (frameOf bfr), σ)}, False) ∧
          ∀ c sl, bfr = some (c, sl) → NewCapOK th (L.mem s) c sl) ∨
       (∃ er er', r = .Err er ∧ (bufSpec y.bv e).run σ = ({(.error er', σ)}, False) ∧ ErrRel er er')) := by
  obtain ⟨ps, hps, hps1⟩ := hes
  obtain ⟨e1, e2⟩ := e
  simp only at he1 hps hps1 hnc ⊢
  subst he1
  have hcwf := slot_wf hDS.1.1 hps hps1
  have hcv0 : CapValid th (capV (L.mem s) (cslotAddr e2)) :=
    hDS.1.2.1.abs ⟨ps, hps1, Or.inl hps⟩ (capAt_capV _ _)
  unfold tcb.derive_for_buffer bufSpec
  by_cases hy : y = 0#u64
  · have hy' : y.bv = 0 := by rw [hy]; rfl
    simp only [hy, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok, show U64.bv 0#u64 = 0 from rfl]
    exact ⟨_, rfl, Or.inl ⟨_, none, rfl, rfl, fun _ _ h => by cases h⟩⟩
  have hy' : ¬ y.bv = 0 := fun h => hy (UScalar.eq_of_val_eq (by
    have := congrArg BitVec.toNat h; simpa using this))
  simp only [hy, hy', ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
  generalize hc0e : capV (L.mem s) (cslotAddr e2) = c0 at hcwf hcv0 hnc ⊢
  obtain ⟨r, hr, r', hr', hrel⟩ := derive_rel (Z := Unit) (st := st) s σ (cslotAddr e2) e2 c0
    hcwf.1 hcwf.2 (fun h => hnc (by cases c0 <;> simp_all [isUt]))
  rw [hr]
  cases r with
  | Err er =>
    cases r' with
    | ok _ => exact hrel.elim
    | error er' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact ⟨_, rfl, Or.inr ⟨er, er', rfl, run_bind_error hr' _, Or.inl hrel⟩⟩
  | Ok c' =>
    cases r' with
    | error _ => exact hrel.elim
    | ok a =>
      obtain ⟨hwf', ha, hev', hcv', -⟩ := hrel
      subst ha
      obtain ⟨rc, hrc', hcase⟩ := Vs.check_valid_ipc_buffer_rel y c' σ
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hrc']
      rcases hcase with ⟨rfl, hck⟩ | ⟨er, er', rfl, hmer, hck⟩
      · obtain ⟨q, sz, rr, m, ep, aa, va, rfl⟩ := check_ok_frame hrc'
        obtain ⟨rfl, m0, ep0, a0, va0, hc0⟩ := derive_frame_inv (fun h => ⟨_, hnc h⟩) hr
        subst hc0
        have hcvc : CapValid th (capability.Cap.Frame q sz rr false m false aa va) := hcv' th hcv0
        refine ⟨.Ok (bufArg .Null (some (.Frame q sz rr false m false aa va, e2))), by simp [bufArg],
          Or.inl ⟨.Null, some (.Frame q sz rr false m false aa va, e2), rfl, ?_, ?_⟩⟩
        · rw [run_bind_ok hr', run_bind_ok hck]; rfl
        · intro c sl h
          cases h
          refine ⟨ps, _, hps, hps1, rfl, hwf', hcvc, hev', fun _ => frame_so_refl hcvc, ?_, ?_, ?_, ?_⟩ <;>
            rw [hc0e] <;> first | rfl | exact Or.inl rfl | exact derive_vcap hr
      · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, bind_ok]
        exact ⟨_, rfl, Or.inr ⟨er, er', rfl, (run_bind_ok hr' _).trans (run_bind_error hck _), ErrRel.of_map hmer⟩⟩

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem decode_configure_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBConfigure p c = tcb.decode_configure st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSuspend_val, lbl_tcbResume_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBConfigure`** (`TcbOK`, the cap installs of l4v's
MCS `decode_tcb_configure`): the IPC buffer (`decode_set_ipc_buffer`), the
roots (`decode_cv_space`), the restart and `invoke_tcb ThreadControlCaps`
installing the roots and the buffer. -/
theorem tcb_configure_refinesW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th) (hH : DelHypsW (L := L) arI W th)
    (hKB : ∃ K : Nat, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧
      ∀ m G, MdbLinks th m G → psiD m G * (K + 1) + K < 2 ^ 64 - 1)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (p : U64) (hp : th p = some .tcb) (hBuf : ∀ v : U64, BufHypW (L := L) W th p v v.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hWr : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W s1 ar σ1 G) :
    tcb.decode st arI s ar fl4_abi.label.TCBConfigure p ⟨length, buf, call, cslotAddr ssl, extra⟩ ⦃ res =>
      TopPostW (L := L) W th σ blk call don (specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer) s ar res ⦄ := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeTcbConfigure (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  rw [decode_configure_eq arI s ar p _ hstall, hdec0]
  have htr : args.length < 3 ∨ excaps.length < 3 →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostW (L := L) W th σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeTcbConfigure (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps)) s ar res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeTcbConfigure
    by_cases ha : args.length < 3
    · rw [whenE_pos (by simpa using ha)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [whenE_neg (by simpa using ha), retOk_bind, whenE_pos (h.resolve_left ha)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
        Fl4Spec.SEMonad Unit Unit)) rfl _
  unfold tcb.decode_configure tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0, extra_eq _ 1#usize (by decide) hx1, extra_eq _ 2#usize (by decide) hx2]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have hx1' : [x0, x1, x2][1]? = some x1 := rfl
  have hx2' : [x0, x1, x2][2]? = some x2 := rfl
  have hge : (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 3#u64 ↔ 3 ≤ args.length := by
    show length >= 3#u64 ↔ _; rw [← hlen]; scalar_tac
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (by omega))
  by_cases hl : 3 ≤ args.length
  swap
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inl (by omega))
  by_cases h1 : x1 = 0#u64
  · have hl1 : excaps.length ≤ 1 := ((hX.2 1 x1 hx1').1).1 h1
    simp only [h0, h1, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  by_cases h2 : x2 = 0#u64
  · have hl2 : excaps.length ≤ 2 := ((hX.2 2 x2 hx2').1).1 h2
    simp only [h0, h1, h2, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, hge, hl]
    exact htr (Or.inr (by omega))
  simp only [h0, h1, h2, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hge, hl]
  obtain ⟨y0, y1, y2, rest, rfl⟩ : ∃ y0 y1 y2 rest, args = y0 :: y1 :: y2 :: rest := by
    match args, hl with
    | y0 :: y1 :: y2 :: rest, _ => exact ⟨_, _, _, _, rfl⟩
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  have ha2 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 2#u64 = ok y2 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 2#u64 y2 (by simp)
  rw [ha0, ha1, ha2]; simp only [bind_ok]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨e1, he1, hxe1, he11, ps1, hps1, hps11⟩ := hX.get hx1' h1
  obtain ⟨e2, he2, hxe2, he21, ps2, hps2, hps21⟩ := hX.get hx2' h2
  have hexc : excaps = [e0, e1, e2] := by
    have h3 := hX.1
    match excaps, he0, he1, he2, h3 with
    | [a, b, c], h0', h1', h2', _ => simp at h0' h1' h2'; rw [h0', h1', h2']
  subst hexc
  subst hxe0 hxe1 hxe2
  have hspec : (Fl4Spec.decodeTcbConfigure (Z := Unit) ((y0 :: y1 :: y2 :: rest).map UScalar.bv) (.threadCap p.bv)
      ssl [e0, e1, e2]).run σ =
      (Fl4Spec.decodeSetIpcBuffer (Z := Unit) [y2.bv] (.threadCap p.bv) ssl [e2] >>= fun sp =>
        Fl4Spec.decodeCvSpace (Z := Unit) [y0.bv, y1.bv] (.threadCap p.bv) ssl [e0, e1] >>= fun ss =>
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none
            ss.tcNewCroot ss.tcNewVroot sp.tcNewBuffer)).run σ := by
    unfold Fl4Spec.decodeTcbConfigure
    rw [whenE_neg (by simp), retOk_bind, whenE_neg (by simp), retOk_bind]
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.getElem?_cons_succ,
      List.getElem?_cons_zero, the_some, retOk_bind]
    rfl
  obtain ⟨rb, hrb, hbcase⟩ := buf_rel th s σ G hDS y2 e2 he21 ⟨ps2, hps2, hps21⟩ (hnc _ (by simp) e2.2 rfl)
  rw [hrb]
  rcases hbcase with ⟨bc0, bfr, rfl, hbs, hbok⟩ | ⟨er, er', rfl, hbs, herr⟩
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, er', ?_, herr⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error ((ipc_spec σ p.bv ssl y2.bv [] e2 []).trans (run_bind_error hbs _)) _
  simp only [bind_ok]
  have hip : (Fl4Spec.decodeSetIpcBuffer (Z := Unit) [y2.bv] (.threadCap p.bv) ssl [e2]).run σ =
      ({(.ok (Fl4Spec.TcbInvocation.threadControlCaps p.bv ssl none none none none (some (y2.bv, frameOf bfr))),
        σ)}, False) :=
    (ipc_spec σ p.bv ssl y2.bv [] e2 []).trans ((run_bind_ok hbs _).trans rfl)
  rw [run_bind_ok hip] at hspec
  obtain ⟨r, hr, hcase⟩ := roots_rel th hP s σ G hDS p hp y0 y1 e0 e1 he01 ⟨ps0, hps0, hps01⟩ he11
    ⟨ps1, hps1, hps11⟩ (hnc _ (by simp) e0.2 rfl) (hnc _ (by simp) e1.2 rfl) ssl
  rw [hr]
  rcases hcase with ⟨cc, vc, rfl, hcv, hokc, hokv⟩ | ⟨e, e', rfl, hcv, herr⟩
  · simp only [lift, bind_ok]
    rw [run_bind_ok hcv] at hspec
    obtain ⟨s1, σ1, hrc, hsts, hst1, hS1, hDS1, -, hkb1, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : W s1 ar σ1 G := hWr s1 σ1 hsts hS1 hst1
    rw [hrc]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeTcbConfigure (Z := Unit) ((y0 :: y1 :: y2 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
          [e0, e1, e2])).run σ =
        ({(.ok (tcInv p ssl (tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER) (.Null, (0, [])) (.Null, (0, []))
          (cc, e0.2) (vc, e1.2) y2.bv bfr), σ)}, False) := by
      apply run_liftME_ok
      rw [hspec]
      simp only [tcInv, optArg, flags_SB, ↓reduceIte]
      rfl
    have hT' := tc_refinesW arI W th hP hH hKB s1 ar σ1 G hDS1 hfr1 p hp ssl hAs (hfhE := fun _ h => absurd rfl h) (tcb.UPDATE_SPACE ||| tcb.UPDATE_IPC_BUFFER)
      (.Null, (0, [])) (.Null, (0, [])) (cc, e0.2) (vc, e1.2)
      (fun h => (Eq.mp flags_SB.1 h).elim) (fun h => (Eq.mp flags_SB.2.1 h).elim)
      (fun _ => hokc.of_same hS1) (fun _ => hokv.of_same hS1) y2 y2.bv (fun _ => hBuf y2) bc0 bfr
      (fun c sl h => (hbok c sl h).of_same hS1)
    simp only [cslot_zero] at hT'
    exact WP.spec_mono hT' (fun res h => top_of_instW (DecOut.of_eq hdec) hst1 h)
  · simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, rfl, e', ?_, herr⟩)
    apply run_liftME_err
    rw [hspec]
    exact run_bind_error hcv _


theorem tcb_configure_refines [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (hBuf : ∀ v : U64, BufHyp (L := L) (A := A) th p v v.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbConfigure)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBConfigure p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  obtain ⟨hO, hPP, hPD, hKB⟩ := hT
  exact WP.spec_mono (tcb_configure_refinesW arI (WQ (L := L) (MdbOKV (L.ksb s))) th hP (delHypsW_Q arI (MdbOKV.step _) hO hPP hPD) hKB
    s ar σ G hDS (hBuf := fun v => (hBuf v).w (MdbOKV.step _)) (hWr := fun _ _ _ hS _ => MdbOKV.of_same hDS.1.2.2.1 hS hFR) p hp slbl hlbl length buf ct hct args hlen hargs hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hnc blk don ci buffer)
    fun _ h => h.toM hP

end


/-! ## The register invocations -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- What a register invocation of FL4 (P1's and the scheduler's) does
against the spec's `m` from the restart's states: every slot word kept,
and an `Ok` outcome of `m` that keeps the CSpace (`StateRel` of any memory,
`cdt`, `is_original_cap`) and every CNode and TCB. -/
def RegPost (th : TypedHeap) (s1 : S) (σ1 : Fl4Spec.State Unit) (m : Fl4Spec.PMonad Unit (List Fl4Spec.Data))
    (s2 : S) : Prop :=
  SlotsSame th (L.mem s1) (L.mem s2) ∧ ∃ y ∈ (m.run σ1).1, (∃ rr, y.1 = .ok rr) ∧
    (∀ mm, StateRel th mm σ1 → StateRel th mm y.2) ∧ y.2.cdt = σ1.cdt ∧ y.2.isOriginalCap = σ1.isOriginalCap ∧
    KSub σ1 y.2

theorem top_of_regs {th : TypedHeap} (hP : Placed th) {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {i : Fl4Spec.TcbInvocation} {G : MdbGhost} {s s1 s2 : S}
    {a : A} (hdec : DecOut m σ (.invokeTCB i))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hDS1 : DState (L := L) th s1 σ1 G) (hfr : MdbOKV (L.ksb s) (L.mem s1) G)
    (h : RegPost (L := L) th s1 σ1 (Fl4Spec.invokeTcb i) s2) :
    TopPostM (L := L) σ blk call don m s (.Ok (), s2, a) := by
  obtain ⟨hS, y, hy, ⟨rr, hrr⟩, hR, hcdt, hio, hK⟩ := h
  obtain ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, -, hF1⟩ := hDS1
  refine Or.inr ⟨_, hdec, σ1, hst, y, hy, th, G, Or.inl ⟨rfl, rr, hrr⟩, hP,
    ⟨(hR _ hR1).of_caps (fun x hx => hS.capAt hx), hV1.of_caps (fun x hx => hS.capAt hx), hM1.of_same hS,
      hC1.of_same hS hcdt hio, MdbInv.of_same hM1 hI1 hS⟩, hF1.of_same hM1 hS hK, MdbOKV.of_same hM1 hS hfr⟩

end


theorem nregs_eq : tcb.N_FRAME + tcb.N_GP = ok 20#u64 := by simp only [tcb.N_FRAME, tcb.N_GP]; rfl

theorem nregs_spec : (Fl4Spec.frameRegisters.length + Fl4Spec.gpRegisters.length) = 20 := rfl

theorem range20_iff (y : U64) :
    (y.bv ≥ 1 ∧ y.bv ≤ BitVec.ofNat 64 20) ↔ (1 ≤ y.val ∧ y.val ≤ 20) := by
  have t1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [GE.ge, BitVec.le_def, BitVec.le_def, t1, BitVec.toNat_ofNat, UScalar.bv_toNat]

theorem tcb_eq_ct (p ct : U64) : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq p ct = ok (decide (p = ct)) := rfl

theorem bv_eq_iff' (p q : U64) : p.bv = q.bv ↔ p = q :=
  ⟨fun h => UScalar.eq_of_val_eq (by have := congrArg BitVec.toNat h; simpa using this), fun h => h ▸ rfl⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The register work of ReadRegisters** (P1's and the scheduler's):
FL4's `read_registers` after the restart, against the spec's
`invoke_tcb ReadRegisters`. -/
def ReadRegsHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64) : Prop :=
  ∀ s1 σ1 (flags n : U64) (call : Bool) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    tcb.read_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n call ⦃ r =>
      RegPost (L := L) th s1 σ1 (Fl4Spec.invokeTcb (Z := Unit) (.readRegisters p.bv (Fl4Spec.testBit flags.bv 0)
        n.bv Fl4Spec.ArchDefaultExtraRegisters)) r.1 ⦄

theorem decode_read_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBReadRegisters p c = tcb.decode_read_registers st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val]
  simp only [↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBReadRegisters`** (`TcbOK`): l4v's
`decode_read_registers` (the count's range, not the caller), the restart,
and the register work (`ReadRegsHyp`). -/
theorem tcb_read_regs_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbReadRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (hR : ReadRegsHyp (L := L) arI th s σ ct p)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBReadRegisters p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeReadRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF
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
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
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
      obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
      have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
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
      refine WP.spec_bind (hR s1 σ1 y0 y1 call ar hs1 (by rw [← hcur]; exact hst1)) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 (top_of_regs hP (DecOut.of_eq hdec) hst1 hDS1 hfr1 h2)
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

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The register work of WriteRegisters** (P1's and the scheduler's):
FL4's `write_registers` (reading the values from the message, `args` from
index 2) after the restart, against the spec's `invoke_tcb WriteRegisters`. -/
def WriteRegsHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p buf : U64) (args : List U64) : Prop :=
  ∀ s1 σ1 (flags n : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → n.val ≤ args.length - 2 →
    tcb.write_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n buf ⦃ r =>
      RegPost (L := L) th s1 σ1 (Fl4Spec.invokeTcb (Z := Unit) (.writeRegisters p.bv (Fl4Spec.testBit flags.bv 0)
        (((args.drop 2).map UScalar.bv).take n.val) Fl4Spec.ArchDefaultExtraRegisters)) r.1 ⦄

theorem decode_write_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBWriteRegisters p c = tcb.decode_write_registers st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBWriteRegisters`** (`TcbOK`): l4v's
`decode_write_registers` (enough values, not the caller), the restart, and
the register work (`WriteRegsHyp`). -/
theorem tcb_write_regs_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbWriteRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hW : WriteRegsHyp (L := L) arI th s σ ct p buf args)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBWriteRegisters p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeWriteRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF
  rw [decode_write_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_write_registers
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
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨i, hi, hiv⟩ := spec_exists (U64.sub_spec (x := length) (y := 2#u64) (by scalar_tac))
  have hrl : rest.length = length.val - 2 := by simp at hlen; scalar_tac
  have hiv' : i.val = length.val - 2 := by rw [hiv.1]; rfl
  have hl2 : 2 ≤ length.val := by have : ¬ length.val < (2#u64 : U64).val := h1; exact Nat.le_of_not_lt this
  rw [ha0, ha1]; simp only [bind_ok, hi]
  have hsp : (Fl4Spec.decodeWriteRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
        (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters)) := by
    simp only [Fl4Spec.decodeWriteRegisters, List.map_cons, retOk_bind]
  rw [hsp]
  have hun : Fl4Spec.unat y1.bv = y1.val := by simp [Fl4Spec.unat]
  by_cases hw : i < y1
  · simp only [hw, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    rw [whenE_pos (by rw [hun, List.length_map, hrl]; have h' : i.val < y1.val := hw; omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hw, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
  have hwh : (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
      (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) : Fl4Spec.SEMonad Unit Unit).run σ = ({(.ok (), σ)}, False) := by
    rw [whenE_neg (by rw [hun, List.length_map, hrl]; have h' : ¬ i.val < y1.val := hw; omega)]; rfl
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩
    apply run_liftME_err
    rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
      s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
    rw [hrc1]; simp only [bind_ok, lift]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
          (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
          let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
          Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
          Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
            ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((((y0 :: y1 :: rest).drop 2).map UScalar.bv).take y1.val) Fl4Spec.ArchDefaultExtraRegisters)), σ)},
          False) := by
      apply run_liftME_ok
      rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc),
        retOk_bind, hun]
      rfl
    refine WP.spec_bind (hW s1 σ1 y0 y1 ar hs1 (by rw [← hcur]; exact hst1) (by simp only [List.length_cons]; have h' : ¬ i.val < y1.val := hw; omega)) ?_
    rintro ⟨s2, a2⟩ h2
    exact (WP.spec_ok _).2 (top_of_regs hP (DecOut.of_eq hdec) hst1 hDS1 hfr1 h2)

end


theorem copy_trunc0 (σ : Fl4Spec.State Unit) (cap : Fl4Spec.Cap) (ex : List Fl4Spec.Cap) :
    (Fl4Spec.decodeCopyRegisters (Z := Unit) [] cap ex).run σ = ({(.error .truncatedMessage, σ)}, False) := rfl

theorem copy_trunc1 (σ : Fl4Spec.State Unit) (y : Fl4Spec.Data) (rest : List Fl4Spec.Data) (cap : Fl4Spec.Cap) :
    (Fl4Spec.decodeCopyRegisters (Z := Unit) (y :: rest) cap []).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold Fl4Spec.decodeCopyRegisters
  dsimp only
  rw [retOk_bind, retOk_bind, retOk_bind, retOk_bind, whenE_pos rfl]
  exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
    Fl4Spec.SEMonad Unit Unit)) rfl _

theorem copy_spec (y : Fl4Spec.Data) (rest : List Fl4Spec.Data) (p : Fl4Spec.ObjRef) (c : Fl4Spec.Cap)
    (cs : List Fl4Spec.Cap) :
    Fl4Spec.decodeCopyRegisters (Z := Unit) (y :: rest) (.threadCap p) (c :: cs) =
      ((match c :: cs with
        | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p q (Fl4Spec.testBit y 0)
          (Fl4Spec.testBit y 1) (Fl4Spec.testBit y 2) (Fl4Spec.testBit y 3) Fl4Spec.ArchDefaultExtraRegisters)) := by
  unfold Fl4Spec.decodeCopyRegisters
  dsimp only
  rw [retOk_bind, retOk_bind, retOk_bind, retOk_bind, whenE_neg (by simp), retOk_bind]
  congr 1
  funext q
  rw [retOk_bind]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The register work of CopyRegisters** (P1's and the scheduler's):
FL4's `copy_registers` (source `src`, a thread cap's in a slot) after the
restart, against the spec's `invoke_tcb CopyRegisters`. -/
def CopyRegsHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct p : U64) : Prop :=
  ∀ s1 σ1 (src flags : U64) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    (∃ x, IsSlot th x ∧ capV (L.mem s) x = .Thread src) →
    tcb.copy_registers st arI s1 a p src flags ⦃ r => r.1 = .Ok () ∧
      RegPost (L := L) th s1 σ1 (Fl4Spec.invokeTcb (Z := Unit) (.copyRegisters p.bv src.bv
        (Fl4Spec.testBit flags.bv 0) (Fl4Spec.testBit flags.bv 1) (Fl4Spec.testBit flags.bv 2)
        (Fl4Spec.testBit flags.bv 3) Fl4Spec.ArchDefaultExtraRegisters)) r.2.1 ⦄

theorem decode_copy_eq (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) :
    tcb.decode st arI s ar fl4_abi.label.TCBCopyRegisters p c = tcb.decode_copy_registers st arI s ar p c := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  rfl

/-- **`tcb::decode` at `TCBCopyRegisters`** (`TcbOK`): l4v's
`decode_copy_registers` (the source thread cap, `copy_src_rel`), the
source's stall (`hstall'`, a no-op on this core), the restart, and the
register work (`CopyRegsHyp`). -/
theorem tcb_copy_regs_refines (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbCopyRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hC : CopyRegsHyp (L := L) arI th s σ ct p)
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hX : XcRel th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBCopyRegisters p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call
      don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF
  rw [decode_copy_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_copy_registers tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : args = [] ∨ excaps = [] →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostM (L := L) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)))
        s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    rcases h with rfl | rfl
    · exact copy_trunc0 σ _ _
    · cases args with
      | nil => exact copy_trunc0 σ _ _
      | cons y0 rest => exact copy_trunc1 σ _ _ _
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hX.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (List.eq_nil_of_length_eq_zero (by omega)))
  by_cases hl : length < 1#u64
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, show ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by
        show ¬ length >= 1#u64; scalar_tac]
    exact htr (Or.inl (List.eq_nil_of_length_eq_zero (by scalar_tac)))
  simp only [h0, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    show (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by show length >= 1#u64; scalar_tac]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args, hlen with
    | y0 :: rest, _ => exact ⟨_, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  rw [ha0]; simp only [bind_ok, thread_arg_eq]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hX.get hx0' h0
  obtain ⟨erest, rfl⟩ : ∃ erest, excaps = e0 :: erest := by
    match excaps, he0 with
    | a :: r, h => simp at h; exact ⟨r, by rw [h]⟩
  have hsp : (Fl4Spec.decodeCopyRegisters (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv)
      ((e0 :: erest).map Prod.fst)) =
      ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
        | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
          (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    rw [List.map_cons, List.map_cons, copy_spec, he01]
  rw [hsp]
  rcases copy_src_rel (capV (L.mem s) x0) (erest.map Prod.fst) (σ := σ) with ⟨src, hsrc, hrun⟩ | ⟨hsrc, hrun⟩
  · rw [hsrc]
    simp only [hstall' src, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, hS1, hDS1, -, -, -⟩ := restart_dstate th hP s σ G hDS ct hct hcur htcb hact
    have hfr1 : MdbOKV (L.ksb s) (L.mem s1) G := MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
    refine let_pair2 s ar (fun s1 a1 => do let s2 ← tcb.restart_caller st s1; tcb.copy_registers st arI s2 a1 p src y0)
      _ ?_
    rw [hrc1]; simp only [bind_ok]
    have hthr : capV (L.mem s) x0 = .Thread src := by
      revert hsrc; cases capV (L.mem s) x0 <;> simp [threadArgF]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
          | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
          | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>=
          fun q => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
            (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
            Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.copyRegisters p.bv src.bv (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1)
          (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3) Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
      apply run_liftME_ok
      exact (run_bind_ok hrun _).trans rfl
    have hxs : IsSlot th x0 := by rw [hxe0]; exact AbsSlot.isSlot ⟨ps0, hps01, Or.inl hps0⟩
    refine WP.spec_mono (hC s1 σ1 src y0 ar hs1 (by rw [← hcur]; exact hst1) ⟨x0, hxs, hthr⟩) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, h2⟩
    simp only at hr2; subst hr2
    exact top_of_regs hP (DecOut.of_eq hdec) hst1 hDS1 hfr1 h2
  · rw [hsrc]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩)
    exact run_liftME_err (run_bind_error hrun _)

end


/-! ## Every label -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem lbl_of {slbl : Fl4Spec.Data} {lbl : U64} (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    {l : U64} {g : Fl4Spec.GenInvocationLabels} (h : lbl = l) (hg : tcbLabelOf l = g) :
    Fl4Spec.genInvocationType slbl = g := by rw [hlbl, h, hg]

/-- **`tcb::decode`, every label, the CSpace-side labels proved**:
`tcb_decode_refines` with SetTLSBase, SetTimeoutEndpoint, SetIPCBuffer,
SetSpace, Configure and Read/Write/CopyRegisters discharged here (their
scheduler and register work as `TlsResHyp`, `BufHyp`, `ReadRegsHyp`,
`WriteRegsHyp`, `CopyRegsHyp`); the scheduler-side labels (SetPriority,
SetMCPriority, SetSchedParams, Suspend, Resume, Bind/UnbindNotification)
SetFlags (FL4's FPU release and reply) and the FL4 extension labels
(breakpoints, single stepping, FPU, SetTimer) remain one hypothesis each. -/
theorem tcb_decode_cspace [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hT : TcHyps (L := L) arI th)
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
    (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    -- the scheduler and register work of the CSpace-side labels
    (hres : TlsResHyp (L := L) th s σ ct) (hBuf : ∀ v : U64, BufHyp (L := L) (A := A) th p v v.bv)
    (hRead : ReadRegsHyp (L := L) arI th s σ ct p) (hWrite : WriteRegsHyp (L := L) arI th s σ ct p buf args)
    (hCopy : CopyRegsHyp (L := L) arI th s σ ct p)
    -- the scheduler-side labels and the FL4 extensions
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
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hSetBreakpoint : lbl = fl4_abi.label.TCBSetBreakpoint → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hGetBreakpoint : lbl = fl4_abi.label.TCBGetBreakpoint → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hUnsetBreakpoint : lbl = fl4_abi.label.TCBUnsetBreakpoint → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hConfigureSingleStepping : lbl = fl4_abi.label.TCBConfigureSingleStepping → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hSetFlags : lbl = fl4_abi.label.TCBSetFlags → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hReadFPU : lbl = fl4_abi.label.TCBReadFPU → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hWriteFPU : lbl = fl4_abi.label.TCBWriteFPU → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer)
    (hSetTimer : lbl = fl4_abi.label.TCBSetTimer → TcbOKF (L := L) arI s ar σ lbl p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer) :
    TcbOKF (L := L) arI s ar σ lbl p ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci ssl excaps buffer := by
  have hstall := hstall' p
  refine tcb_decode_refinesF arI s ar σ lbl p _ blk call don slbl hlbl _ ci ssl excaps buffer hext hstall hNative
    ?_ ?_ ?_ ?_ hSetPriority hSetMCPriority hSetSchedParams ?_ ?_ ?_ hSuspend hResume hBindNotification
    hUnbindNotification hSetBreakpoint hGetBreakpoint hUnsetBreakpoint hConfigureSingleStepping ?_ hSetFlags
    hReadFPU hWriteFPU hSetTimer
  · rintro rfl
    exact tcb_read_regs_refines arI th hP s ar σ G hDS hFR p slbl (lbl_of hlbl rfl (by simp [tcbLabelOf])) length buf ct
      hct args hlen hargs hcur htcb hact hstall hRead call _ extra blk don ci ssl excaps buffer
  · rintro rfl
    exact tcb_write_regs_refines arI th hP s ar σ G hDS hFR p slbl (lbl_of hlbl rfl (by simp [tcbLabelOf])) length buf
      ct hct args hlen hargs hcur htcb hact hstall hWrite call _ extra blk don ci ssl excaps buffer
  · rintro rfl
    exact tcb_copy_regs_refines arI th hP s ar σ G hDS hFR p slbl (lbl_of hlbl rfl (by simp [tcbLabelOf])) length buf
      ct hct args hlen hargs hcur htcb hact hstall hstall' hCopy call ssl extra x0 x1 x2 hx0 excaps hX blk don ci
      buffer
  · rintro rfl
    exact tcb_configure_refines arI th hP hT s ar σ G hDS hFR p hp hBuf slbl (lbl_of hlbl rfl (by simp [tcbLabelOf]))
      length buf ct hct args hlen hargs hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hnc
      blk don ci buffer
  · rintro rfl
    exact tcb_set_timeout_refines arI th hP hT s ar σ G hDS hFR p hp slbl (lbl_of hlbl rfl (by simp [tcbLabelOf]))
      length buf ct hct hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 excaps hX _ blk don ci buffer
  · rintro rfl
    exact tcb_set_ipc_refines arI th hP hT s ar σ G hDS hFR p hp hBuf slbl (lbl_of hlbl rfl (by simp [tcbLabelOf]))
      length buf ct hct args hlen hargs hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 excaps hX
      (fun sl h hu => hnc x0 (by simp) sl h hu) blk don ci buffer
  · rintro rfl
    exact tcb_set_space_refines arI th hP hT s ar σ G hDS hFR p hp slbl (lbl_of hlbl rfl (by simp [tcbLabelOf]))
      length buf ct hct args hlen hargs hcur htcb hact hstall call ssl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hX hnc
      blk don ci buffer
  · rintro rfl
    exact tcb_set_tls_refines arI th hP s ar σ G hDS.1 hDS.2.2 hFR p hp slbl (lbl_of hlbl rfl (by simp [tcbLabelOf]))
      length buf ct hct args hlen hargs hcur htcb hact hcw hstall hres call _ extra blk don ci ssl excaps buffer

end

end

end Fl4Proofs.P3
