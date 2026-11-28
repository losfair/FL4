/-
P3x for virtualization (line virt, gen 19, item 1): **the V → F transport of the virt top on `NoRunVM` states,
without `NR`, `hvk` or a route scope** (gen 18's `fl4CallKernelVF_eq_nr` / `fl4KernelEntrySyscallVF_eq_nr`
composed the way VirtKEntryV3F composes VirtF13's `kentryVF_of_V`).

* `notVmEnter_of_unbound` (no VCPU bound to the current thread), `notVmEnter_of_vk` (`virtKind = none`),
  `notVmEnter_of_nvv` (no VCPU object): the three ways an event is not a VMEnter call at a state.
* **`evOutVF_of_V_nr`**, **`evOutVTF_of_V_nr`**, **`kentryVF_of_V_nr`**: an exit of the `V` step (`EvOutV`,
  `EvOutVT`, `fl4KernelEntrySyscallV`) from a `NoRunVM` state is one of FL4's step (`EvOutVF`, `EvOutVTF`,
  `fl4KernelEntrySyscallVF`), for every `onCore` / `remoteCur`; the event exits need `NotVmEnter` at the state the
  event is handled in. VCPU objects and virtualization caps are allowed; no `hvk`, no `NV`, no `ScopeE8`.
* **`v3OutF_of_v3Out_nr`**: the conclusion of `kernel_entry_reachV3` (`V3Out`, VirtWit10) gives that of
  `kernel_entry_reachV3F` (`V3OutF`, VirtWit13) at any `NoRunVM` state where no unknown syscall after the
  `FaultIP` write is a VMEnter call (`hnv`). This is the composition step of a V3F top on `NoRunVM` states: any
  V-side top with V3Out's exits moves to FL4's step by it, whatever the VCPU content of the state.
* `v3OutF_of_v3Out_NR` (the `NR` instance, `hnv` from `NVV`), **`kernel_entry_reachV3F_nr`**:
  `kernel_entry_reachV3F` re-derived through the NoRunVM transport. Unlike VirtKEntryV3F's proof it does not use
  `hvk` (or `scopeE8_of_hK`) in the composition; `hvk` and `hvirt` remain premises only because
  `kernel_entry_reachV3` (the V side) has them.

Not done (gen 19 handoff, item 1): a V-side top with VCPUs present. Every existing V-side top is
`kernel_entry_reachV3`, whose premise `hvk : virtKind = .none` [S] is false on every reachable state with a VCPU
(the VCPU retype gate: FL4 `untyped.rs` returns `InvalidArgument 0` for the VT-x types when `virtualization() ==
0`, the spec's `virtEnabled`), and whose state fact `NR` contains `NVV` (no VCPU object). So no VCPU-state
instance of the transport's `V3Out` antecedent is available yet; the transport itself has no VCPU restriction.

Named premises: none new. `kernel_entry_reachV3F_nr` has exactly `kernel_entry_reachV3F`'s premises (`hvk` [S],
`hvirt` [P], U36I's platform premises, `hNR`). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtWit13
import Fl4Proofs.P3.VirtNoRunStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtV3FNoRun
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtNoRunStep

noncomputable section

/-! ## Not a VMEnter call -/

theorem notVmEnter_of_unbound {σ : State Unit} (h : tcbVcpuOf σ σ.curThread = none) (ev : Event) :
    NotVmEnter ev σ := fun n _ => by unfold isVmEnterCall; simp [h]

theorem notVmEnter_of_vk (hvk : virtKind = .none) (ev : Event) (σ : State Unit) : NotVmEnter ev σ :=
  fun n _ => by unfold isVmEnterCall; simp [hvk]

theorem notVmEnter_of_nvv {σ : State Unit} (hv : NVV σ) (ev : Event) : NotVmEnter ev σ :=
  fun n _ => VirtR7eK.isVmEnterCall_nvv hv n

/-! ## The exits -/

/-- **An event exit of the `V` step from a `NoRunVM` state is one of FL4's step** (off VMEnter). -/
theorem evOutVF_of_V_nr (onCore remoteCur : ObjRef → Bool) {ev : Event} {σ σ' : State Unit} (hs : NoRunVM σ)
    (hv : NotVmEnter ev σ) (h : VirtExtTop.EvOutV onCore ev σ σ') : VirtF13.EvOutVF onCore remoteCur ev σ σ' := by
  show ((), σ') ∈ (fl4CallKernelVF (Z := Unit) onCore remoteCur true ev σ).1
  rw [fl4CallKernelVF_eq_nr onCore remoteCur true ev hs hv]
  exact h

/-- **An `EvOutVT` exit (after the `FaultIP` write) from a `NoRunVM` state is one of FL4's step.** -/
theorem evOutVTF_of_V_nr (onCore remoteCur : ObjRef → Bool) {ev : Event} {σ σ' : State Unit} (hs : NoRunVM σ)
    (hv : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, NotVmEnter ev w.2)
    (h : VirtKEntryV.EvOutVT onCore ev σ σ') : VirtF13.EvOutVTF onCore remoteCur ev σ σ' := by
  obtain ⟨w, hw, hO⟩ := h
  refine ⟨w, hw, ?_⟩
  rw [fl4CallKernelVF_eq_nr onCore remoteCur true ev (SInv.ns_fl4SyscallFaultIP _ σ hs w hw) (hv w hw)]
  exact hO

/-- **A syscall exit of the `V` step from a `NoRunVM` state is one of FL4's step** (no scope: a syscall event is
never a VMEnter call). -/
theorem kentryVF_of_V_nr (onCore remoteCur : ObjRef → Bool) {c : Syscall} {σ σ' : State Unit} (hs : NoRunVM σ)
    (h : ((), σ') ∈ (fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1) :
    ((), σ') ∈ (fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur true c σ).1 := by
  rw [fl4KernelEntrySyscallVF_eq_nr onCore remoteCur true c hs]
  exact h

end

end Fl4Proofs.P3.VirtV3FNoRun

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.VirtV3FNoRun

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **The V → F transport of the virt top's conclusion on `NoRunVM` states** (module docstring). -/
theorem v3OutF_of_v3Out_nr (onCore remoteCur : Fl4Spec.ObjRef → Bool) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hs : VirtR7d.NoRunVM σ)
    (hnv : ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ n,
      Fl4Spec.isVmEnterCall n w.2 = false)
    (h : V3Out (L := L) arI AR MR onCore s a σ) : V3OutF (L := L) arI AR MR onCore remoteCur s a σ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ := h
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', kentryVF_of_V_nr onCore remoteCur hs h1, h2⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', evOutVF_of_V_nr onCore remoteCur hs (fun n e => by cases e) h1, h2⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', evOutVF_of_V_nr onCore remoteCur hs (fun n e => by cases e) h1, h2⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', evOutVF_of_V_nr onCore remoteCur hs (fun n e => by cases e) h1, h2⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, h2⟩
    exact ⟨ev, σ', hK, evOutVTF_of_V_nr onCore remoteCur hs (fun w hw n _ => hnv w hw n) hO, h2⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, h2⟩
    exact ⟨ev, σ', hK, evOutVTF_of_V_nr onCore remoteCur hs (fun w hw n _ => hnv w hw n) hO, h2⟩

/-- The `NR` instance: `hnv` from `NVV` after the `FaultIP` write. -/
theorem v3OutF_of_v3Out_NR (onCore remoteCur : Fl4Spec.ObjRef → Bool) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hNR : VirtR7e.NR σ) (h : V3Out (L := L) arI AR MR onCore s a σ) :
    V3OutF (L := L) arI AR MR onCore remoteCur s a σ :=
  v3OutF_of_v3Out_nr arI AR MR onCore remoteCur hNR.2
    (fun w hw n => VirtR7eK.isVmEnterCall_nvv (VirtExtTop.nr_fl4SyscallFaultIP _ σ hNR w hw).1.2 n) h

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachV3F` through the `NoRunVM` transport** (module docstring): same premises as
`kernel_entry_reachV3F`; the composition uses neither `hvk` nor the route scope. -/
theorem kernel_entry_reachV3F_nr [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hvk : Fl4Spec.virtKind = .none) (hvirt : ∀ a : A, arI.virtualization a = ok 0#u64)
    (onCore remoteCur : Fl4Spec.ObjRef → Bool)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) (hNR : VirtR7e.NR σ) :
    V3OutF (L := L) arI AR MR onCore remoteCur s a σ :=
  v3OutF_of_v3Out_NR arI AR MR onCore remoteCur hNR
    (kernel_entry_reachV3_out arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hvk
      hvirt onCore hJ hNR)

end

end

end Fl4Proofs.P3.SInvR.G5
