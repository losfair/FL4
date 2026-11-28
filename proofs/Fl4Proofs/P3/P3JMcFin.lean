/-
P3 (p3J gen 26): **`FinFootJ` [J] discharged** — `syscall.finish` (`schedule`, `activate_thread`, `vcpu::check`)
writes only `ProjW H Cs s` at every `CKI` `JAtZ` state (the premise's full domain: no narrowing). Then the
interrupt top on `RunMcWKR` runs needs no footprint premise.

At a `JAtZ` state `s` (P1's sets of `H`: `T = H.tcbs`, `Sg = H.frame`, `Scs = H.scs`, `Z = H.scBits`, …) with
`CKI σ`:

* **Buffer placement at `U = ∅`** (`bufAt_empty_cki`): every TCB's IPC-buffer lookup is `0`
  (P3JMcFootC's `bufOK_empty_cki`, gen 23), so `P1.BufAt … ∅ s`. P1 / P2 carry it along their frames
  (`IbFr`: `schedule.ibFr`, `finish_old.ibx`), so the `send_signal`s of `timer::fire` and the final `vcpu::check`
  write no user word.
* **`schedule`** (`sched_projW`): P2's `sched.schedule.sN` over `Kp = ∅` (as P2's `schedule.vc`) gives `fire`'s
  P1 footprint `FootDU … ∅` (`KW ∨ DbgW`) and the rest an `SFootN ∅` step. `KW` allows other cores' node words at
  offsets 8 / 32 (`IDLE_THREAD` / `IDLE_SC`), which `ProjW` excludes; P3JFinW's `timer.fire.idlF` shows `fire`
  keeps them (`IdlK`, without `FCtx`), so `projW_of_footDU_idl` gives `ProjW` for `fire`. `SFootN ∅` words
  (`SchedWN`: `KW`, the heap's endpoints / notifications, the kernel-global area, minus `IdN False`) are `ProjW`
  words (`projW_of_sfootN`; the kernel-global area is `ProjW`'s second clause).
* **`activate_thread`** (`act_projW`): P3JFinW's `TWS` footprint (SC words of `H.scs`, the current thread's
  registers / `YIELD_TO` / `STATE`, `SCHED_ACTION`), all `ProjW` (`tws_projW`). Gen 25's worry (the IPC-buffer
  writes of `complete_yield_to`) does not arise: `set_consumed` writes message register 0, a CPU register.
* **`vcpu::check`**: P2's `vcpu.check.vckN` at `U = ∅`: its `hbuf` from the carried buffer placement, its `hpw`
  vacuous because every TCB's VCPU word is `0` at `s` (`JExt.vw`) and kept by `finish_old`
  (`syscall.finish_old.vc`). `VckN ∅` words are `ProjW` words (`vckN_projW`).
* **`finFootJ_holds`**: `FinFootJ` from `P0.ArchTotal arI` alone. **`kernel_entry_runMcWKR_irq`**: gen 25's
  `kernel_entry_runMcWKR_irqJ` with `hFn` discharged — the interrupt clause `RunMcWKR` → `RunMcWKR` with
  U45nv's globals only.

No premise beyond the stated hypotheses; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JFinW
import Fl4Proofs.P3.P3JMcIrqRQ
import Fl4Proofs.P3.P3JMcKwN
import Fl4Proofs.P3.P3JMcFootC
import Fl4Proofs.P3.BufAtJ
import Fl4Proofs.P3.ScJointFrame
import Fl4Proofs.P1.VcpuExitBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

/-! ## Glue: P1 / P2 footprints over `H`'s sets into `ProjW` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {H : P1.Heap} {Cs : Set U64}

theorem prW_empty_false {T Scs : Set U64} {s : S} {b : U64} :
    ¬ Fl4Proofs.P1.PrW st ∅ False T Cs Scs s b := by
  rintro (⟨y, -, -, hy, -⟩ | ⟨h, -⟩)
  · exact absurd hy (Set.notMem_empty y)
  · exact h

/-- `KW` minus `IdN False` over `H`'s sets is `ProjW`. -/
theorem kw_projW (hH : P1.HeapOK H) {s : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c) {b : U64}
    (hk : P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) s b)
    (hi : ¬ Fl4Proofs.P1.IdN st False Cs s b) : ProjW (L := L) H Cs s b :=
  kwN_projW hH hNP (Kp := ∅) (Nd := False) ⟨hk, fun hI => hI.elim hi prW_empty_false⟩

/-- **`fire`'s footprint into `ProjW`**: P1's `FootDU … ∅` plus the node identity words kept. -/
theorem projW_of_footDU_idl (hH : P1.HeapOK H) {s s' : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    (f : FootDU st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) ∅ s s')
    (k : Fl4Proofs.P2.Stall.IdlK st Cs s s') : P1.WritesIn st s s' (ProjW (L := L) H Cs s) := by
  refine ⟨f.1, f.2.1, fun b hal hb => ?_⟩
  by_cases hi : Fl4Proofs.P1.IdN st False Cs s b
  · obtain ⟨c, hc, o, ho, rfl⟩ := hi
    rcases ho with e | e | ⟨-, e⟩ | ⟨h, -⟩
    · exact k.2 c hc o (Or.inl e)
    · exact k.2 c hc o (Or.inr e)
    · exact absurd (node_projW (hNP c hc) hc (by omega) (by omega) (by omega)) hb
    · exact h.elim
  · refine f.2.2 b hal fun hw => hb ?_
    rcases hw with (hk | hd) | hu
    · exact kw_projW hH hNP hk hi
    · exact dbgW_projW hH hNP hd
    · exact absurd hu (Set.notMem_empty _)

/-- **`schedule`'s tail footprint (`SFootN ∅`) into `ProjW`.** -/
theorem projW_of_sfootN (hH : P1.HeapOK H) {s s' : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    (hfit : (L.ksb s).val + 13568 ≤ 2 ^ 64)
    (F : Fl4Proofs.P1.SFootN st ∅ (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) H s s') : P1.WritesIn st s s' (ProjW (L := L) H Cs s) := by
  refine (show P1.WritesIn st s s' _ from ⟨F.1, F.2.1, F.2.2.1⟩).mono fun b hb => ?_
  obtain ⟨hw, hi, -⟩ := hb
  rcases hw with hk | ⟨o, ho, rfl⟩
  · exact kw_projW hH hNP hk hi
  · have hv := wa_v (a := L.ksb s) (b := o) (by omega)
    exact Or.inr (Or.inl ⟨by rw [hv]; omega, by rw [hv]; omega⟩)

/-- `activate_thread`'s words (`TWS`) over `H`'s sets are `ProjW` words. -/
theorem tws_projW (hH : P1.HeapOK H) {s : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    (hc : L.cpu s ∈ Cs) {y b : U64} (hy : y ∈ P1.Heap.tcbs H)
    (hb : Fl4Proofs.P2.Stall.TWS st (P1.Heap.scs H) (P1.Heap.scBits H) y s b) : ProjW (L := L) H Cs s b := by
  have hyH : H y = some .tcb := hy
  rcases hb with (⟨c, ⟨z, hz⟩, hin⟩ | ⟨K, h1, h2, -, rfl⟩) | rfl | rfl | rfl
  · have e : P1.Heap.scBits H c = z := by simp only [P1.Heap.scBits, hz]
    rw [e] at hin
    exact Or.inl ⟨c, .sc z, hz, hin.1, hin.2⟩
  · exact obj_projW hH (k := .tcb) hyH (by simp only [P1.HKind.bits]; omega)
  · unfold yieldA; exact obj_projW hH (k := .tcb) hyH (by simp [P1.HKind.bits])
  · rw [Fl4Proofs.P1.stA_eq]; exact obj_projW hH (k := .tcb) hyH (by simp [P1.HKind.bits])
  · exact node_projW (hNP _ hc) hc (by rw [act_val]; omega) (by rw [act_val]; omega) (by rw [act_val]; omega)

/-- `vcpu::check`'s words at `U = ∅` (`VckN ∅`) over `H`'s sets are `ProjW` words. -/
theorem vckN_projW (hH : P1.HeapOK H) {s : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    (hc : L.cpu s ∈ Cs) {y b : U64} (hy : y ∈ P1.Heap.tcbs H)
    (hb : Fl4Proofs.P2.Stall.VckN st ∅ (P1.Heap.ntfns H) y s b) : ProjW (L := L) H Cs s b := by
  have hyH : H y = some .tcb := hy
  rcases hb with (⟨K, h1, h2, -, rfl⟩ | hu) | ⟨n, hn, rfl⟩ | rfl | rfl
  · exact obj_projW hH (k := .tcb) hyH (by simp only [P1.HKind.bits]; omega)
  · exact absurd hu (Set.notMem_empty _)
  · have hnH : H n = some .ntfn := hn
    unfold epTSA; exact obj_projW hH hnH (by simp [P1.HKind.bits])
  · rw [Fl4Proofs.P1.stA_eq]; exact obj_projW hH (k := .tcb) hyH (by simp [P1.HKind.bits])
  · exact node_projW (hNP _ hc) hc (by rw [act_val]; omega) (by rw [act_val]; omega) (by rw [act_val]; omega)

end

/-! ## `syscall.finish` at a `CKI` `JAtZ` state -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}
variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
  {σ : Fl4Spec.State Unit}

/-- **`BufAt` at `U = ∅` at a `CKI` `JAtZ` state** (module docstring). -/
theorem bufAt_empty_cki (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : SInvCk.CKI σ) :
    P1.BufAt st (P1.Heap.tcbs H) Cs H (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s :=
  ⟨fun b hb => absurd hb (Set.notMem_empty b), fun y hy =>
    bufOK_empty_cki J hC (J.thTcb (by rw [J.tcbs_eq.1]; exact hy)) true⟩

/-- Every TCB's VCPU word is `0` at a `JAtZ` state (`JExt.vw`). -/
theorem vcpuZ_of_J (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Fl4Proofs.P2.Stall.VcpuZ st (P1.Heap.tcbs H) s := fun t ht =>
  J.ext.vw t (J.thTcb (by rw [J.tcbs_eq.1]; exact ht))

/-- **`schedule` writes only `ProjW`** at a `CKI` `JAtZ` state (module docstring). -/
theorem sched_projW (hA : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) :
    sched.schedule st arI s a ⦃ s1 _ => P1.WritesIn st s s1 (ProjW (L := L) H Cs s) ⦄ := by
  have hblk := J.blk
  have hH := J.kern.heap
  have hBA := bufAt_empty_cki J hC
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun n hn => hn
  obtain ⟨Q, R, hq⟩ := J.blk.1
  refine WP.spec_mono (Fl4Proofs.P1.sched.schedule.sN (Kp := (∅ : Set U64)) hA (ibKeep_holds hA) hNt s a
    hblk hBA fun _ _ => ⟨fun y hy => absurd hy (Set.notMem_empty y), fun _ => Set.notMem_empty _,
      fun hk => absurd hk (Set.notMem_empty _)⟩) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨rf, hrf, Fd, F⟩ := hh
  have k0 := Fl4Proofs.P2.Stall.timer.fire.idlF hA (ibKeep_holds hA) hNt s a hblk hBA
  rw [hrf] at k0
  have K : Fl4Proofs.P2.Stall.IdlK st Cs s rf.1 := (WP.spec_ok rf).1 k0
  have t0 := Fl4Proofs.P1.timer.fire.tinvF hA (ibKeep_holds hA) hNt s a hblk hBA
  rw [hrf] at t0
  have T1 : P1.TInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac rf.1 ∧
      FootDU st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) ∅ s rf.1 :=
    (WP.spec_ok rf).1 t0
  obtain ⟨⟨⟨Q1, R1, q1⟩, -⟩, -⟩ := T1
  have A1 := projW_of_footDU_idl hH hq.nodes Fd K
  have B1 := projW_of_sfootN hH q1.nodes (by rw [Fd.1]; exact J.kern.ksbFit) F
  exact A1.projW_trans B1

/-- **`finish_old` (`schedule`, `activate_thread`) writes only `ProjW`, ends in `EntryInv`**, and keeps the
buffer lookups and the VCPU words. -/
theorem finOld_projW (hA : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) :
    syscall.finish_old st arI s a ⦃ s2 _ => P1.WritesIn st s s2 (ProjW (L := L) H Cs s) ∧
      P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s2 ∧
      P1.IbFr (L := L) (P1.Heap.tcbs H) s s2 ∧ Fl4Proofs.P2.Stall.VcpuWK st (P1.Heap.tcbs H) s s2 ⦄ := by
  have hblk := J.blk
  have hH := J.kern.heap
  have hBA := bufAt_empty_cki J hC
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun n hn => hn
  have core : syscall.finish_old st arI s a ⦃ s2 _ => P1.WritesIn st s s2 (ProjW (L := L) H Cs s) ∧
      P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s2 ⦄ := by
    unfold syscall.finish_old
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hblk
    refine WP.spec_bind (WP.spec_and
      (Fl4Proofs.P1.sched.schedule.entry hA (ibKeep_holds hA) hNt s a Q R h0 hB hS hX hSg hBA)
      (sched_projW hA J hC)) ?_
    rintro ⟨s1, a1⟩ hh
    try simp only [WP.uncurry'_pair] at hh ⊢
    obtain ⟨E1, W1⟩ := hh
    have hq1 := E1.1.choose_spec.choose_spec
    refine WP.spec_mono (WP.spec_and (Fl4Proofs.P1.sched.activate_thread.entry hA s1 a1 E1)
      (Fl4Proofs.P2.Stall.sched.activate_thread.tws hA s1 a1 (EntryInv.bxi E1).blk)) ?_
    rintro ⟨s2, a2⟩ hh
    try simp only [WP.uncurry'_pair] at hh ⊢
    obtain ⟨E2, W2⟩ := hh
    refine ⟨W1.projW_trans (W2.mono fun b hb => tws_projW hH hq1.nodes hq1.cur hq1.curT hb), E2⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and core
    (Fl4Proofs.P1.syscall.finish_old.ibx hA hNt s a (BlkOK.bxi hblk) hBA))
    (Fl4Proofs.P2.Stall.syscall.finish_old.vc hA hNt s a (BlkOK.bxi hblk) hBA)) ?_
  rintro ⟨s2, a2⟩ hh
  try simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨⟨W, E⟩, I⟩, V, -⟩ := hh
  exact ⟨W, E, I, V⟩

/-- **`FinFootJ` [J] holds** (module docstring): at every `CKI` `JAtZ` state, `syscall.finish` writes only
`ProjW H Cs s`. -/
theorem finFootJ_holds (hA : P0.ArchTotal arI) : FinFootJ (st := st) (L := L) arI AR := by
  intro Z H Cs Ac Lst D s a σ J _ hC
  have hH := J.kern.heap
  have hBA := bufAt_empty_cki J hC
  have hVz := vcpuZ_of_J J
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun n hn => hn
  rw [Fl4Proofs.P1.finish_eq_old]
  refine WP.spec_bind (finOld_projW hA J hC) ?_
  rintro ⟨s2, a2⟩ hh
  try simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨W2, E2, I2, V2⟩ := hh
  show (do let t ← sched.cur_thread st s2; vcpu.check st arI s2 a2 t) ⦃ _ ⦄
  rw [Fl4Proofs.P1.cur_thread_ok]; simp only [bind_ok]
  have hq2 := E2.1.choose_spec.choose_spec
  have hc2 : L.curW s2 ∈ P1.Heap.tcbs H := hq2.curT
  refine WP.spec_mono (Fl4Proofs.P2.Stall.vcpu.check.vckN (U := ∅) hA hNt s2 a2 E2
    (fun b hb => absurd hb (Set.notMem_empty b)) ((hBA.of_fr I2).2 _ hc2) fun hne => absurd ?_ hne) ?_
  · rw [V2 _ hc2]; exact hVz _ hc2
  rintro ⟨s3, a3⟩ hr
  try simp only [WP.uncurry'_pair] at hr ⊢
  exact W2.projW_trans (hr.mono fun b hb => vckN_projW hH hq2.nodes hq2.cur hc2 hb)

end

/-! ## The interrupt top without a footprint premise -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}
open Classical Fl4Spec Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5
  Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, `RunMcWKR` to `RunMcWKR`, with no footprint premise** (module
docstring): gen 25's `kernel_entry_runMcWKR_irqJ` with `FinFootJ` by `finFootJ_holds`. -/
theorem kernel_entry_runMcWKR_irq [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_irqJ hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW
    (finFootJ_holds hA) hR

end

end Fl4Proofs.P3.Mc
