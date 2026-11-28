/-
P3 (p3J gen 54): **the endpoint receive leaf at stable ghosts at a `chooseNewThread` mid state** (batch 4 of gen 51's
plan), **`MidRecvLvIC` proved, `DispStabFootLzx` discharged, and the native syscall top with no [J]**.

The `chooseNewThread` endpoint receive proofs (XTopJointRecvIpcC, RecvIpcLinkC, RecvIpcN, RecvIpcActDonD, RecvIpcBound,
RecvIpcPushDonD, RecvSendPC, RecvSendPDD: 26 declarations, the call closure of `jRecvIpcUC`, `jRecvIpcLinkC`,
`jRecvIpcUDD`, `jRecvIpcLinkDD` minus gen 53's batch 3) ended in `RJR` / `RJ`. This gen each was generalised in place
over its post exactly as gens 52–53: `…Q` takes `Pq` with `hPq` (every `JAtZR` resp. `JAtZ` at `Z.mv G V` with the
entry's `H`, `Cs` gives `Pq`) and ends in `RelTopM ∧ Pq`; calls of batch-3 leaves became their `…Q` forms; the
original (statement byte-identical up to `:=`) is the one-line instance. Every exit was already at `Z.mv _ _` with the
entry's `H`, `Cs`: nothing found false.

* **`ipcMidC`**: `RecvLvI.ipc` at a `JAtZ` state with `MidStF`, `chooseNewThread` and `CtOK`: with `CurInv` (`MidC`)
  by `jRecvIpcUCQ` / `jRecvIpcLinkCQ`, ct SC-less (`MidN`) by `jRecvIpcUDDQ` / `jRecvIpcLinkDDQ` (null or free reply
  vs. reply linked to another thread), at `Pq := JStabR Z H Cs`.
* **`midRecvLvIC_disp`**: `MidRecvLvIC` at a `VxE` `JAtZ` entry with `SInvX` and ct ≠ idle (`CtOK` of the first
  phase's outcome by `ctOK_disp`). So gen 53's `MidRecvLvIC` [J] is a theorem.
* **`dispStabFootLzx_disch`**: `DispStabFootLzx` from the globals (`hA`, `hnd`, `hT` (its `mb`), `hmax`, `htu`):
  `SInvX` from `RunMcWKR` by `jreach_invU3`, then `midRecvSw_of_IC`.
* Top **`kernel_entry_runMcWKR_sysLzz`**: `kernel_entry_runMcWKR_sysLzy` without `hLzx`; premises exactly
  `_sysLzy`'s globals (`hARI`, `hA`, `hnd`, `hM`, `hIp`, `hKD`, `hPAi`, `hIA`, `hT`, `hmax`, `htu`, `hRef`, `hSX`,
  `hDR`, `hFpu`, `hFW`, `PlainStore`) and the run state `hR : RunMcWKR`. **`kernel_entry_runMcWKR_sysLzy_of_Lzz`**
  (new → old: drop `hLzx`) and **`kernel_entry_runMcWKR_sysLzz_of_Lzy`** (old → new: `hLzx` by
  `dispStabFootLzx_disch`): equivalent under the globals.

Named premises: none new; `DispStabFootLzx` [J] and `MidRecvLvIC` [J] are now discharged (their definitions stay as
the statements the chain proves). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidIpcSt
import Fl4Proofs.P3.P3JLookFlat
import Fl4Proofs.P3.XTopJointRecvIpcLinkC
import Fl4Proofs.P3.XTopJointRecvIpcPushDonD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **The endpoint receive leaf at stable ghosts at a `chooseNewThread` mid state** (module docstring). -/
theorem ipcMidC (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {Z : XSets} [VxE Z] {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hF : MidStF σ)
    (hcn : σ.schedulerAction = .chooseNewThread) (hok : MidRun.CtOK σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
      ((rc = .Null ∧ rc' = .nullCap) ∨
        (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
      JHeld (L := L) Z.th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) →
      endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
          RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄ := by
  intro p b sd g gr rc rc' hpE hrc hHd hHr
  have hPq : ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ' →
      JStabR (L := L) arI AR Z H Cs s' a' σ' := fun G V Ac' Lst' D' _ _ _ J' => by
        unfold JStabR; exact ⟨G, V, Ac', Lst', D', J'⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  rcases hok with hC | ⟨x, hx, h0⟩
  · have hMC : MidC σ := ⟨hF.ni, hF.run, hcn, hC⟩
    by_cases hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64
    · exact jRecvIpcUCQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmax (htu a) J hctT hcur hMC hMC.nr hF.nq p b sd g
        gr rc rc' hpE hrc hHd hHr hun hPq
    · rcases hrc with ⟨rfl, -⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
      · exact absurd (Or.inl rfl) hun
      · exact jRecvIpcLinkCQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmax (htu a) J hctT hcur hMC hF.nq p b sd g
          gr q g' rc' hpE hcr hkr hHd (hHr q g' rfl) (fun h => hun (Or.inr ⟨q, g', rfl, h⟩)) hPq
  · have hN : MidN σ := ⟨hF.ni, hF.run, hcn, fun x' hx' => by rw [hx] at hx'; cases hx'; exact h0⟩
    by_cases hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64
    · exact jRecvIpcUDDQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmax hmb (htu a) J hctT hcur hN hF.nq p b sd g
        gr rc rc' hpE hrc hHd hHr hun hPq
    · rcases hrc with ⟨rfl, -⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
      · exact absurd (Or.inl rfl) hun
      · exact jRecvIpcLinkDDQ (Pq := JStabR (L := L) arI AR Z H Cs) hAT hmax hmb (htu a) J hctT hcur hN hF.nq p b sd
          g gr q g' rc' hpE hcr hkr hHd (hHr q g' rfl) (fun h => hun (Or.inr ⟨q, g', rfl, h⟩)) hPq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **`MidRecvLvIC` at a `VxE` dispatch entry** (gen 53's [J], now a theorem; module docstring). -/
theorem midRecvLvIC_disp (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {Z : XSets} [VxE Z]
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (n : I64) (c : Fl4Spec.Syscall) : MidRecvLvIC (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF hcn G V Ac1 Lst1 D1 s1 a1
    J1 ct1 hct1
  exact ⟨ipcMidC hA hmax htu hmb J1 hF hcn (ctOK_disp hnd J hX hni hBA J' _ y hy) hct1⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **`DispStabFootLzx` from the globals** (module docstring). -/
theorem dispStabFootLzx_disch (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} : DispStabFootLzx (L := L) arI AR MR s a σ where
  midRecvSw := fun hR Z H Cs Ac Lst D J hV n c hni _ _ _ => by
    haveI := hV
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midRecvSw_of_IC hA hnd (Sched.TimeAgree.mb hT) hmax htu J hX hni
      (midRecvLvIC_disp hA hnd (Sched.TimeAgree.mb hT) hmax htu J hX hni n c)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with no [J]**: `kernel_entry_runMcWKR_sysLzy`
with `hLzx` discharged (`dispStabFootLzx_disch`); premises: `_sysLzy`'s globals and `hR` (module docstring). -/
theorem kernel_entry_runMcWKR_sysLzz [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzy hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzx_disch hA hnd hT hmax htu)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **The new top gives the previous one** (`_sysLzy` = `_sysLzz` plus the now-proved `hLzx`). -/
theorem kernel_entry_runMcWKR_sysLzy_of_Lzz [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (_hLzx : DispStabFootLzx (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzz hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR

set_option maxHeartbeats 4000000 in
/-- (p3J gen 54) **The previous top gives the new one** (`hLzx` by `dispStabFootLzx_disch`). -/
theorem kernel_entry_runMcWKR_sysLzz_of_Lzy [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    (hLzy : ∀ {s : S} {a : A} {σ : Fl4Spec.State Unit}, RunMcWKR (L := L) arI AR MR s a σ →
      DispStabFootLzx (L := L) arI AR MR s a σ →
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
        (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  hLzy hR (dispStabFootLzx_disch hA hnd hT hmax htu)

end

end

end Fl4Proofs.P3.Mc
