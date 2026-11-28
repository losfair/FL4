/-
P3 (line p3J, gen 21): **`UtMem` discharged on `RunCK` runs**, so the `…Foot` premises of the four non-syscall
clauses are FL4 footprint statements only.

* **Finding.** On a `RunCK` run the spec holds no untyped cap at all (`CKI`, P3JCkW: every slot cap is `KW`, and an
  untyped cap is not). At a `JAtZ` state the CSpace relation (`StateRel`, `RelTopB`'s `CRel`) relates every slot of
  the typed heap to a spec slot cap by `CapRel`, i.e. `absCap`, which maps FL4's `Untyped` to the spec's
  `untypedCap`. So at a `JAtZ` state whose spec state is `CKI`, no typed-heap slot holds an FL4 untyped cap
  (**`no_untyped_of_cki`**), and `UtMem th s s'` holds vacuously at such an outcome `s'` (**`utMem_of_cki`**), for
  every `s`. The outcome's `JAtZ` and `CKI` are the stable-ghost run's (`irq_stabU45` etc.: `RunCK ∧ JStab`).
* Premises **`IrqFootW` / `UserFootW` / `VmfFootW` / `SysUFootW`** [J]: gen 20's `…FootK` with only
  `WritesIn s r.1 (ProjW H Cs s)` left (no `UtMem`, no `CnWF`). Tops **`kernel_entry_runMcWK_irqW` / `_userW` /
  `_vmfW` / `_sysUW`**: `RunMcWK` (P3JKtTop: `RunMcW ∧ KhWF`) to `RunMcWK`, U45nv's globals as gen 20's tops.

Named premises: `IrqFootW`, `UserFootW`, `VmfFootW`, `SysUFootW` [J] (above); U45nv's globals as in
`kernel_entry_runCK`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JKtTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ Fl4Proofs.P3.SInvKt

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **No FL4 untyped cap in a typed-heap slot at a `JAtZ` state whose spec state is `CKI`** (module docstring). -/
theorem no_untyped_of_cki {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {x : U64} (hx : IsSlot Z.th x) {p sb fi : U64} {d : Bool}
    (hc : capV (L.mem s) x = .Untyped p sb fi d) : False := by
  have hR : StateRel Z.th (L.mem s) σ := J.xtop.rel.2.1.1
  obtain ⟨q, i, hsa, rfl⟩ := hx
  rcases hsa with ⟨r, hq, hi⟩ | ⟨hq, hi⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode q r hq
    obtain ⟨c, ac, hca, hac, hrel⟩ := hs (bitsOf i r) (length_bitsOf i r)
    have e1 : slotAddr q.bv (Fl4Spec.ofBl (bitsOf i r)) = slotOf q i := by
      rw [slotAddr_ofBl, blVal_bitsOf, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hi]
    rw [e1, capAt_capV] at hca
    have ec := ok_inj_ff hca
    rw [hc] at ec; subst ec
    have hco : capOpt (σ.kheap q.bv) (bitsOf i r) = some ac := by
      simp only [capOpt, hk, if_pos hwf]; exact hac
    have hk2 := hC _ _ _ hco
    revert hk2; rw [← hrel.2]; simp [absCap, SInvCk.KW]
  · obtain ⟨tcb, hk, hs⟩ := hR.tcb q hq
    obtain ⟨c, ac, hca, hac, hrel⟩ := hs i hi
    have e1 : slotAddr q.bv (BitVec.ofNat 64 i) = slotOf q i := rfl
    rw [e1, capAt_capV] at hca
    have ec := ok_inj_ff hca
    rw [hc] at ec; subst ec
    have hco : capOpt (σ.kheap q.bv) (Fl4Spec.tcbCnodeIndex i) = some ac := by
      simp only [capOpt, hk]; exact hac
    have hk2 := hC _ _ _ hco
    revert hk2; rw [← hrel.2]; simp [absCap, SInvCk.KW]

/-- **`UtMem` at an outcome whose spec state is `CKI`, at the outcome's `JAtZ`** (module docstring). -/
theorem utMem_of_cki {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {th : TypedHeap}
    (J' : JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a' σ') (hth : Z.th = th) (hC : SInvCk.CKI σ') :
    UtMem (L := L) th s s' := by
  subst hth
  intro x hx p sb fi hc
  exact (no_untyped_of_cki J' hC hx hc).elim

theorem utMem_of_stab {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hSt : JStab (L := L) arI AR Z H Cs s' a' σ') (hC : SInvCk.CKI σ') : UtMem (L := L) Z.th s s' := by
  obtain ⟨G', V', Ac', Lst', D', J'⟩ := hSt
  exact utMem_of_cki J' rfl hC

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`IrqFootW` [J]**: the interrupt entry writes only the projection footprint (module docstring). -/
def IrqFootW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∀ σ', EvOut false .interrupt σ σ' →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

/-- **`UserFootW` [J]**: the user-exception entry writes only the projection footprint. -/
def UserFootW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∀ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

/-- **`VmfFootW` [J]**: the VM-fault entry writes only the projection footprint. -/
def VmfFootW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType),
      σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∀ σ', EvOut false (.vmFaultEvent ft) σ σ' →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

/-- **`SysUFootW` [J]**: the unknown-syscall entry writes only the projection footprint. -/
def SysUFootW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64), σ.curThread ≠ σ.idleThread →
      UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∀ ev σ', KEvSpec (.sysU n) true ev → EvOut true ev σ σ' →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

variable {arI AR MR}

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, `RunMcWK` to `RunMcWK`, with `IrqFootW`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcWK_irqW [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : IrqFootW (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  obtain ⟨⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩, hK⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (irq_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW hC J w a1 hw)
    (hFt Z H Cs Ac Lst D J hV w a1 hw)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hW⟩
  have hK' := khWF_evOut (fun c e => by cases e) hK hO
  exact ⟨σ', hO, runMcW_of_stK J hV hF hC' hSt (hW σ' hO) (utMem_of_stab hSt hC'.2) (cnWF_of_khWF hK'), hK'⟩

set_option maxHeartbeats 4000000 in
/-- **The user-exception entry on any core, `RunMcWK` to `RunMcWK`, with `UserFootW`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_userW [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : UserFootW (L := L) arI AR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c hct hu
  obtain ⟨⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩, hK⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (user_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J n c hct hu)
    (hFt Z H Cs Ac Lst D J hV n c hct hu)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hW⟩
  have hK' := khWF_evOut (fun c e => by cases e) hK hO
  exact ⟨σ', hO, runMcW_of_stK J hV hF hC' hSt (hW σ' hO) (utMem_of_stab hSt hC'.2) (cnWF_of_khWF hK'), hK'⟩

set_option maxHeartbeats 4000000 in
/-- **The VM-fault entry on any core, `RunMcWK` to `RunMcWK`, with `VmfFootW`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_vmfW [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : VmfFootW (L := L) arI AR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro ad c ft hct hv
  obtain ⟨⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩, hK⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (vmf_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J ad c ft hct hv)
    (hFt Z H Cs Ac Lst D J hV ad c ft hct hv)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hW⟩
  have hK' := khWF_evOut (fun c e => by cases e) hK hO
  exact ⟨σ', hO, runMcW_of_stK J hV hF hC' hSt (hW σ' hO) (utMem_of_stab hSt hC'.2) (cnWF_of_khWF hK'), hK'⟩

set_option maxHeartbeats 4000000 in
/-- **The unknown-syscall entry on any core, `RunMcWK` to `RunMcWK`, with `SysUFootW`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_sysUW [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : SysUFootW (L := L) arI AR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n hct hU hND
  obtain ⟨⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩, hK⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (sysU_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J n hct hU hND)
    (hFt Z H Cs Ac Lst D J hV n hct hU hND)) ?_
  rintro r ⟨⟨ev, σ', hKe, hO, hC', hSt⟩, hW⟩
  have hK' := khWF_evOut (KEvSpec.not_sys hKe) hK hO
  exact ⟨ev, σ', hKe, hO, runMcW_of_stK J hV hF hC' hSt (hW ev σ' hKe hO) (utMem_of_stab hSt hC'.2)
    (cnWF_of_khWF hK'), hK'⟩

end

end Fl4Proofs.P3.Mc
