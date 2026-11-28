/-
P3 (issue #16, jc3): **`kernel_entry_reachU20`** = jc2's `kernel_entry_reachU19`
without C4 `vsTyp` (INV-PLAN §1.U3L; KENTRY-PLAN g7b-4 step 4).

* `JAtZ.carry` (JCarryDefs' `JCarry`) carries `vsTyp : VsTyp Z s σ`: every slot's
  page-table / page-directory / PDPT cap (mapped or not) whose table is in no set of
  `Z` names a spec table of its level, and the table's frame misses core `Z.c`'s
  node, the kernel-state block's `OObj` part, the ASID-table area and every word of
  `Z.B` (`OffK`). Frame steps keep it through the `VsSlotsT` table part (`TabSlots`,
  at every predicate) and `IpcFrKeep.arch` (the spec's arch objects kept, of the same
  type); retypes and MakePool by `VsTyp.stepN` (new caps are no mapped table caps,
  an unmapped table cap's table is in its set); VSpace maps / unmaps keep the invoked
  slot's object key; the drops by `JAtZ.dropVsTyp` (a table cap's table misses a
  childless untyped cap's region, `JAtZ.tabOff`; a pruned table was a set table,
  `JAtZ.offK_of_set`).
* `JAtZ.offTabOK` derives XTopJointVsOff's `OffTabOK` at every slot of a `JAtZ`
  state: the rest of `OffFrame` (the other objects of the sets and the typed heap)
  from `H`: the table an `H` object of 4 KiB (`SpecCover.arch`, `ArchFitHyp`), the
  sets' objects `H`'s (`zH`, `JPlaced`, `vsFr_other`), `HeapOK.disj`.
* `KDispHypsKVU20` = `KDispHypsKVU19` with `JEntryAtR7` (= `JEntryAtR6` without
  `vsTyp`); `KDispHypsKVU20.toU19 J'` fills it from the dispatch state's own `JAtZ`.

Premises removed (relative to U19): C4 [J]. Added: none.
-/
import Fl4Proofs.P3.XTopJointKEntryU19
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs

noncomputable section

/-- An arch object of the page-table type is a page table (and so on). -/
theorem tabT_pt {ao : Fl4Spec.ArchKernelObj} (h : Fl4Spec.aaType ao = tabT 1) : ∃ f, ao = .pageTable f := by
  cases ao with
  | dataPage d sz => cases d <;> simp [Fl4Spec.aaType, tabT] at h
  | pageTable f => exact ⟨f, rfl⟩
  | _ => simp [Fl4Spec.aaType, tabT] at h

theorem tabT_pd {ao : Fl4Spec.ArchKernelObj} (h : Fl4Spec.aaType ao = tabT 2) : ∃ f, ao = .pageDirectory f := by
  cases ao with
  | dataPage d sz => cases d <;> simp [Fl4Spec.aaType, tabT] at h
  | pageDirectory f => exact ⟨f, rfl⟩
  | _ => simp [Fl4Spec.aaType, tabT] at h

theorem tabT_pdpt {ao : Fl4Spec.ArchKernelObj} (h : Fl4Spec.aaType ao = tabT 3) : ∃ f, ao = .pdPointerTable f := by
  cases ao with
  | dataPage d sz => cases d <;> simp [Fl4Spec.aaType, tabT] at h
  | pdPointerTable f => exact ⟨f, rfl⟩
  | _ => simp [Fl4Spec.aaType, tabT] at h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **A table off its set, at a `JAtZ` state: a spec table of its level, its
frame `OffFrame`** (`OffK` carried; the rest from `H`). -/
theorem JAtZ.offFrame (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {k : Nat} {q : U64}
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hq : q ∉ tabSet Z k) (hO : OffR (L := L) Z s σ k q) :
    (∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.aaType ao = tabT k) ∧ OffFrame (L := L) Z s σ q := by
  obtain ⟨⟨ao, h1, h2⟩, hK⟩ := hO hq
  refine ⟨⟨ao, h1, h2⟩, ?_⟩
  -- the table is a 4 KiB `other` object of `H`
  obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao h1
  have hn' : n ≤ 12 := by have := J.carry.archFit q.bv ao n h1 hH; rwa [objBits_tabT h2] at this
  have hHq : H q = some (.other 12) := by
    have e : n = 12 := by omega
    subst e; exact hH
  have hHO := J.kern.heap
  have hqa : q.val % 4096 = 0 := by have := hHO.align q _ hHq; simpa [P1.HKind.bits] using this
  have h4096 : (2 : Nat) ^ 12 = 4096 := by norm_num
  -- apart from every other `H` object
  have hap : ∀ p k', H p = some k' → p ≠ q → q.val + 4096 ≤ p.val ∨ p.val + 2 ^ k'.bits ≤ q.val := by
    intro p k' hp hne
    rcases hHO.disj q _ p k' hHq hp (Ne.symm hne) with h | h
    · left; simpa [P1.HKind.bits, h4096] using h
    · right; exact h
  have hneK : ∀ p k', H p = some k' → (∀ z, k' ≠ .other z) → p ≠ q := fun p k' hp hk' e => by
    subst e; rw [hHq] at hp; exact hk' 12 (Option.some.inj hp).symm
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hR := J.xtop.rel.2.1.1
  -- a typed-heap CNode is a spec CNode, so not at `q`
  have hcn : ∀ p r, Z.th p = some (.cnode r) → q.val + 4096 ≤ p.val ∨ p.val + 32 * 2 ^ r ≤ q.val := by
    intro p r hp
    have hne : p ≠ q := fun e => by
      subst e; obtain ⟨cs, hc, -⟩ := hR.cnode p r hp; rw [hc] at h1; cases h1
    have e32 : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; norm_num; ring
    have := hap p _ (hJ.cnode p r hp) hne
    simp only [P1.HKind.bits] at this; rw [e32] at this; exact this
  have htc : ∀ t, Z.th t = some .tcb → q.val + 4096 ≤ t.val ∨ t.val + 4096 ≤ q.val := by
    intro t ht
    have hHt := (hJ.tcb t).1 ht
    have := hap t _ hHt (hneK t _ hHt fun _ e => by cases e)
    simpa [P1.HKind.bits, h4096] using this
  -- the sets' tables are other spec tables
  have hF := J.xtop.fin
  have hnv : ¬ (q ∈ Z.P ∨ q ∈ Z.L4 ∨ q ∈ Z.L3 ∨ q ∈ Z.L2 ∨ q ∈ Z.L1) := by
    intro hv
    rcases hv with hv | hv | hv | hv | hv
    · obtain ⟨f, hf, -⟩ := hF.2.1.pool q hv; rw [hf] at h1; cases h1
      rcases hk with rfl | rfl | rfl <;> simp [Fl4Spec.aaType, tabT] at h2
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q hv; rw [hf] at h1; cases h1
      rcases hk with rfl | rfl | rfl <;> simp [Fl4Spec.aaType, tabT] at h2
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q hv; rw [hf] at h1; cases h1
      rcases hk with rfl | rfl | rfl <;> simp [Fl4Spec.aaType, tabT] at h2
      exact hq (by simpa [tabSet] using hv)
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q hv; rw [hf] at h1; cases h1
      rcases hk with rfl | rfl | rfl <;> simp [Fl4Spec.aaType, tabT] at h2
      exact hq (by simpa [tabSet] using hv)
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q hv; rw [hf] at h1; cases h1
      rcases hk with rfl | rfl | rfl <;> simp [Fl4Spec.aaType, tabT] at h2
      exact hq (by simpa [tabSet] using hv)
  have hvs : ∀ q', (q' ∈ Z.P ∨ q' ∈ Z.L4 ∨ q' ∈ Z.L3 ∨ q' ∈ Z.L2 ∨ q' ∈ Z.L1) →
      q.val + 4096 ≤ q'.val ∨ q'.val + 4096 ≤ q.val := by
    intro q' hq'
    obtain ⟨n', hn', hH'⟩ := J.vsFr_other hq'
    have hne : q' ≠ q := fun e => hnv (e ▸ hq')
    have h4 : 2 ^ 12 ≤ 2 ^ n' := Nat.pow_le_pow_right (by decide) hn'
    rcases hap q' _ hH' hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits] at h; right; omega
  refine ⟨hqa, fun b g1 g2 => ⟨fun ho => ?_, fun hv => ?_, fun p k' hp g => ?_⟩⟩
  · obtain ⟨a1, a2, -, a4⟩ := hK b g1 g2
    rcases ho with h | h | ⟨t, ht, c1, c2⟩ | ⟨e, he, c1, c2⟩ | ⟨r, hr, c1, c2⟩ | ⟨m, hm, c1, c2⟩ |
        ⟨sc, hsc, x, nn, hkx, c1, c2⟩ | ⟨wp, hw, c1, c2⟩
    · exact a1 h
    · exact a2 h
    · have hHt := J.zH.1 t ht
      have := hap t _ hHt (hneK t _ hHt fun _ e => by cases e)
      simp only [P1.HKind.bits, h4096] at this; omega
    · have hHe := J.zH.2.1 e he
      have := hap e _ hHe (hneK e _ hHe fun _ e => by cases e)
      simp only [P1.HKind.bits] at this; omega
    · have hHr := J.zH.2.2.1 r hr
      have := hap r _ hHr (hneK r _ hHr fun _ e => by cases e)
      simp only [P1.HKind.bits] at this; omega
    · have hHm := J.zH.2.2.2 m hm
      have := hap m _ hHm (hneK m _ hHm fun _ e => by cases e)
      simp only [P1.HKind.bits] at this; omega
    · have hHs := (hJ.sc sc x nn (J.c0 sc hsc) hkx).2
      have := hap sc _ hHs (hneK sc _ hHs fun _ e => by cases e)
      simp only [P1.HKind.bits] at this; omega
    · exact a4 wp hw ⟨c1, c2⟩
  · obtain ⟨-, -, a3, -⟩ := hK b g1 g2
    rcases hv with ⟨p, r, hp, c1, c2⟩ | ⟨t, ht, c1, c2⟩ | ⟨q', hq', c1, c2⟩ | h
    · have := hcn p r hp; omega
    · have := htc t ht; omega
    · have := hvs q' hq'; omega
    · exact a3 h
  · rcases J.thk p k' hp with rfl | ⟨r, rfl⟩
    · have := htc p hp; simp only [objSize] at g; omega
    · have := hcn p r hp; simp only [objSize] at g; omega

/-- **XTopJointVsOff's `OffTabOK` at every slot of a `JAtZ` state** (C4, from
`JAtZ.carry.vsTyp`, jc3). -/
theorem JAtZ.offTabOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y) := by
  intro y hy
  have hO := J.carry.vsTyp y hy
  cases hc : capV (L.mem s) y with
  | PageTable q mp a v =>
    rw [hc] at hO
    cases mp
    · trivial
    · intro hq
      obtain ⟨⟨ao, h1, h2⟩, hF⟩ := J.offFrame (Or.inl rfl) (by simpa [tabSet] using hq) hO
      obtain ⟨f, rfl⟩ := tabT_pt h2
      exact ⟨⟨f, h1⟩, hF⟩
  | PageDirectory q mp a v =>
    rw [hc] at hO
    cases mp
    · trivial
    · intro hq
      obtain ⟨⟨ao, h1, h2⟩, hF⟩ := J.offFrame (Or.inr (Or.inl rfl)) (by simpa [tabSet] using hq) hO
      obtain ⟨f, rfl⟩ := tabT_pd h2
      exact ⟨⟨f, h1⟩, hF⟩
  | Pdpt q mp a v =>
    rw [hc] at hO
    cases mp
    · trivial
    · intro hq
      obtain ⟨⟨ao, h1, h2⟩, hF⟩ := J.offFrame (Or.inr (Or.inr rfl)) (by simpa [tabSet] using hq) hO
      obtain ⟨f, rfl⟩ := tabT_pdpt h2
      exact ⟨⟨f, h1⟩, hF⟩
  | _ => trivial

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR6` without `vsTyp`** (C4, from `JAtZ.carry.vsTyp`, jc3). -/
structure JEntryAtR7 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall` (one core). -/
  stall : ∀ q ∈ Z.T, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ

/-- **`KDispHypsKVU19` with `JEntryAtR7`.** -/
structure KDispHypsKVU20 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7 (st := st) arI AR Z s a σ ∧
    JPathAtMU19 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7 (st := st) arI AR Z s a σ ∧
    JPathAtMU19 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

theorem JEntryAtR7.toR6 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (h : JEntryAtR7 (st := st) arI AR Z s a σ) :
    JEntryAtR6 (L := L) arI AR Z s a σ :=
  ⟨h.stall, h.ioapics, h.archIrq, J.offTabOK⟩

theorem KDispHypsKVU20.toU19 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (h : KDispHypsKVU20 (L := L) arI AR Z H Cs D s a σ n c) : KDispHypsKVU19 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi; ⟨e.toR6 J, p⟩,
    fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm; ⟨e.toR6 J, p⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **`kernel_entry_reachU19` without C4 `vsTyp`** (module docstring). -/
theorem kernel_entry_reachU20V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      VxE Z ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU20 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄)  := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU19V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU19 J') hDL hFin, hIrq, hUs, hVm, hTr, hSU⟩

end

end

end Fl4Proofs.P3.SInvR.G5
