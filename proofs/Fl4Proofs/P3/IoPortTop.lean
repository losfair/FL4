/-
P3 (DESIGN.md §9), IO ports: **the whole of `ioport::decode` of an IO port
cap**, every label, against l4v's `decode_port_invocation`, then
`set_thread_state Restart` and `arch_perform_invocation`
(`ioport_decode_refines`), with the CSpace relation, `MdbInv` and `FinInv`
after the spec's outcome (`PortCPost`). The labels' theorems
(`port_in_refines`, `port_out_refines`, `port_other_refines`) relate FL4's
result to the spec's decode only; the spec's port access changes the
machine state alone (`port_perform_ex`), and FL4 changes no slot, so the
CSpace parts carry over from the state before.

FL4 answers an `In` called with `call` itself (`set_mr`, `set_msg_info`),
where the spec replies in `handle_invocation`: the `In` labels are covered
for `call = false` (as `port_in_refines`).
-/
import Fl4Proofs.P3.IoPortDecode
import Fl4Proofs.P3.IrqArch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

theorem ign_ex {σ : Type} (f : NonDet σ Unit) (s : σ) : ∃ s', ((), s') ∈ (ignoreFailure f s).1 := by
  unfold ignoreFailure
  split_ifs with h
  · exact ⟨s, rfl⟩
  · obtain ⟨⟨u, s'⟩, hx⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨s', hx⟩

theorem mol_ex (f : MachineRestMonad Unit) (ms : MachineState) : ∃ ms', ((), ms') ∈ (machineOpLift f ms).1 := by
  obtain ⟨mr', h⟩ := ign_ex f ms.machineStateRest
  refine ⟨{ ms with machineStateRest := mr' }, ?_⟩
  unfold machineOpLift machineRestLift
  refine mem_bind_nd (x := (ms.machineStateRest, ms)) rfl ?_
  refine mem_bind_nd (x := (((), mr'), ms)) ⟨h, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { ms with machineStateRest := mr' })) (by rfl) ?_
  rfl

theorem dmo_ex {α : Type} (mop : NonDet MachineState α) (σ : State Unit) {r : α} {ms' : MachineState}
    (h : (r, ms') ∈ (mop σ.machineState).1) :
    (r, { σ with machineState := ms' }) ∈ (doMachineOp (Z := Unit) mop σ).1 := by
  unfold doMachineOp
  refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
  refine mem_bind_nd (x := ((r, ms'), σ)) ⟨h, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { σ with machineState := ms' })) (Set.mem_singleton _) ?_
  rfl

theorem molGets_ex {β : Type} (f : MachineRestMonad Unit) (g : MachineState → β) (ms : MachineState) :
    ∃ r ms', (r, ms') ∈ ((machineOpLift f >>= fun _ => NonDet.gets g) ms).1 := by
  obtain ⟨ms', h⟩ := mol_ex f ms
  exact ⟨g ms', ms', mem_bind_nd h rfl⟩

/-- **The spec's port access has an outcome**, changing the machine state
alone. -/
theorem port_perform_ex (σ : State Unit) (port : IoPort) (d : IoPortInvocationData) :
    ∃ r ms, (.ok r, { σ with machineState := ms }) ∈
      ((archPerformInvocation (Z := Unit) (.invokeIOPort (.ioPortInvocation port d))).run σ).1 := by
  have key : ∃ r ms, (r, { σ with machineState := ms }) ∈
      (performIoPortInvocation (Z := Unit) (.ioPortInvocation port d) σ).1 := by
    cases d with
    | ioPortIn8 =>
      obtain ⟨r, ms, h⟩ := molGets_ex (in8Impl port) in8Val σ.machineState
      exact ⟨[r], ms, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    | ioPortIn16 =>
      obtain ⟨r, ms, h⟩ := molGets_ex (in16Impl port) in16Val σ.machineState
      exact ⟨[r], ms, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    | ioPortIn32 =>
      obtain ⟨r, ms, h⟩ := molGets_ex (in32Impl port) in32Val σ.machineState
      exact ⟨[r], ms, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    | ioPortOut8 w =>
      obtain ⟨ms, h⟩ := mol_ex (out8Impl port w) σ.machineState
      exact ⟨[], ms, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    | ioPortOut16 w =>
      obtain ⟨ms, h⟩ := mol_ex (out16Impl port w) σ.machineState
      exact ⟨[], ms, mem_bind_nd (dmo_ex _ σ h) rfl⟩
    | ioPortOut32 w =>
      obtain ⟨ms, h⟩ := mol_ex (out32Impl port w) σ.machineState
      exact ⟨[], ms, mem_bind_nd (dmo_ex _ σ h) rfl⟩
  obtain ⟨r, ms, h⟩ := key
  refine ⟨r, ms, ?_⟩
  unfold archPerformInvocation NonDetE.liftE
  rw [ExceptT.run_lift]
  exact mem_bind_nd h rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The result of an IO port invocation: the spec's error with the state
unchanged, or the spec's decode, `set_thread_state Restart` and an outcome
of the invocation, with the CSpace relation, `MdbInv` and `FinInv`. -/
def PortCPost (th : TypedHeap) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation)
    (s : S) : core.result.Result Unit error.Exc × S × A → Prop
  | (.Err e, s', _) => s' = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e'
  | (.Ok (), s', _) => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ∃ σ' G' r, (.ok r, σ') ∈ ((Fl4Spec.archPerformInvocation (Z := Unit) inv).run σ1).1 ∧
        CRel th (L.mem s') σ' G' ∧ FinInv th (L.mem s') σ' G'

/-- From the labels' `PortPost`: a port invocation that changed no slot. -/
theorem PortPost.toC {th : TypedHeap} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) {ct : U64} (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) {m : Fl4Spec.SEMonad Unit Fl4Spec.ArchInvocation} {Q : Fl4Spec.ArchInvocation → S → A → Prop}
    (hQ : ∀ inv s' a', Q inv s' a' → SlotsSame th (L.mem s) (L.mem s') ∧
      ∃ port d, inv = .invokeIOPort (.ioPortInvocation port d))
    {res : core.result.Result Unit error.Exc × S × A} (h : PortPost σ m s ar Q res) :
    PortCPost (L := L) th σ m s res := by
  obtain ⟨r, s', a'⟩ := res
  cases r with
  | Err e => obtain ⟨h1, -, e', h2, h3⟩ := h; exact ⟨h1, e', h2, h3⟩
  | Ok u =>
    obtain ⟨inv, hrun, hq⟩ := h
    obtain ⟨hS, port, d, rfl⟩ := hQ _ _ _ hq
    obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
    obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
    obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hS (t := ct.bv) hkt .restart
    obtain ⟨rr, ms, hmem⟩ := port_perform_ex σ1 port d
    refine ⟨_, hrun, σ1, by rw [hcur]; exact hst1, _, G, rr, hmem,
      ⟨hR1.of_kheap rfl, hV1, hM1, hC1.of_cdt rfl rfl, MdbInv.of_same hM hI hS⟩,
      hFI.of_same hM hS ((ksub_of_eq (setThreadState_nks _ _) hst1).trans (KSub.of_kheap rfl))⟩

/-- The FL4 labels of IO port accesses and the spec's. -/
def PortLabel (lbl : U64) (slbl : Fl4Spec.Data) : Prop :=
  (64 ≤ lbl.val ∧ lbl.val ≤ 66 → Fl4Spec.invocationType slbl = .archInvocationLabel (inLabel (portSz lbl))) ∧
  (67 ≤ lbl.val ∧ lbl.val ≤ 69 → Fl4Spec.invocationType slbl = .archInvocationLabel (outLabel (portSz lbl))) ∧
  (lbl.val < 64 ∨ 69 < lbl.val → ∀ l, Fl4Spec.invocationType slbl = .archInvocationLabel l →
      l ≠ .x64IOPortIn8 ∧ l ≠ .x64IOPortIn16 ∧ l ≠ .x64IOPortIn32 ∧ l ≠ .x64IOPortOut8 ∧ l ≠ .x64IOPortOut16 ∧
      l ≠ .x64IOPortOut32)

/-- **`ioport::decode` of an IO port cap, every label** (`In` not called). -/
theorem ioport_decode_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (first last : U64) (hfl : first.val ≤ last.val) (hl16 : last.val < 65536) (call : Bool)
    (hcall : 64 ≤ lbl.val ∧ lbl.val ≤ 66 → call = false)
    (hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a'))
    (hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a') :
    ioport.decode st arI s ar lbl length (.IoPort first last 0#u64) call buf ⦃ res =>
      PortCPost (L := L) th σ (Fl4Spec.decodePortInvocation slbl (args.map UScalar.bv)
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val))) s res ⦄ := by
  obtain ⟨hlI, hlO, hlX⟩ := hlbl
  by_cases hI : 64 ≤ lbl.val ∧ lbl.val ≤ 66
  · rw [hcall hI]
    refine WP.spec_mono (port_in_refines arI th hP s ar σ lbl hI slbl (hlI hI) length buf ct hct args hlen hargs
      htcb hact first last hfl hl16 hin) (fun res h => PortPost.toC hCR hFI hcur htcb ?_ h)
    rintro inv s' a' ⟨port, -, rfl, -, hS⟩
    exact ⟨hS, _, _, rfl⟩
  by_cases hO : 67 ≤ lbl.val ∧ lbl.val ≤ 69
  · refine WP.spec_mono (port_out_refines arI th hP s ar σ lbl hO slbl (hlO hO) length buf ct hct args hlen hargs
      htcb hact first last hfl hl16 call hout) (fun res h => PortPost.toC hCR hFI hcur htcb ?_ h)
    rintro inv s' a' ⟨port, data, raw, -, -, rfl, -, hS⟩
    exact ⟨hS, _, _, rfl⟩
  have hX : lbl.val < 64 ∨ 69 < lbl.val := by omega
  exact WP.spec_mono (port_other_refines arI s ar σ lbl hX slbl (hlX hX) length buf ct hct _ first last call)
    (fun res h => PortPost.toC hCR hFI hcur htcb (fun _ _ _ h => h.elim) h)

end

end

end Fl4Proofs.P3
