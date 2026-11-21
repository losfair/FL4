/-
P3 (DESIGN.md §9), invariant line G2 (g2c): **`kernel_entryJ33`**, the newest
top. Its premise list is `kernel_entryJ32`'s, except that the bundles inside
`hK` no longer hold `JEntryAt.live` ([J], INV-PLAN E15): the liveness facts
`LiveDN` (XTopJointWJLRestart: `LiveJ` ∧ `DbgWF` ∧ `NullOrig`; l4v
`if_unsafe_then_cap`, `if_live_then_nonz_cap`, `zombies_final`,
`valid_nullcaps`) are asked ONCE, at the entry state and its own carried
ghosts (`hLv : LiveDN Z.th H Cs Z.G s σ`), and carried to the dispatch state.

g2c first re-scoped the field (XTopJointEntry's `JEntryAt.live`,
XTopJointKEntry27b's `JEntryAtR2.live`): it was `∀ H Cs Ac Lst D, JAtZ … →
LiveDN …` (a fact about every ghost choice that relates the state, INV-PLAN
§3), it is now `LiveDN Z.th H Cs Z.G s σ` at the structure's ghost parameters
`H`, `Cs`, which every reader instantiates at the `JAtZ` it decodes from (the
22 readers read it only there: the deletions at `WJL` and the installs).

* `LiveDN.of_keep`: a step keeping every slot (`SlotsSame`), the debug words
  (`DbgKeep`), every TCB's affinity / state / SC / bound-notification / yield
  words, the action and idle words and the original bits keeps `LiveDN` at the
  same ghosts (`LiveJ.of_sameZ`: a TCB zombie's object is a TCB, `ZOK`, so its
  `DeadP` reads only those words; `DbgWFL.of_keep`; `NullOrig.of_same`).
* `budget_ok_frT`: a passing `budget_ok` writes the current node's `CUR_TIME`
  and `CONSUMED` words only (XTopJointPP's `update_timestamp_fr`, P1's
  `check_budget_restart.same`).
* `front_writes`: the FL4 front `KFrontB` (the current thread's `FAULT_IP`
  register, then a passing `budget_ok`) writes those three words only.
* `BudgetAt.orig`: the spec's front (`FaultIP` write, `updateTimeStamp`, a
  passing `checkBudgetRestart`) keeps the original bits.
* `liveDN_front`: `LiveDN` at the entry state gives `LiveDN` at every
  dispatch state `hK` is asked at (`KFrontB`, `BudgetAt σ σb true`, the ghosts
  `Z.mv Z.G V'`, `H`, `Cs`).
* `JEntryAtR3` / `KDispHypsKV33`: `JEntryAtR2` / `KDispHypsKV32` without
  `live`; `.toR2` / `.to32` take `LiveDN`.
* `kernel_entryJ33`: `kernel_entryJ32` with `hK` giving `KDispHypsKV33` and the
  new per-state premise `hLv` [J]. J32 is kept (J33 is a wrapper over it).

Boot obligation ([W] for G4): for the initial joint state with ghosts
`Z0, H0, Cs0`, `LiveDN Z0.th H0 Cs0 Z0.G s0 σ0`: every slot in use of a CNode
or TCB is covered by a CNode / thread cap of the MDB naming its container; every
TCB on core 0's debug list is named by a thread cap; no zombie caps (so
`zslots` / `zdead` hold vacuously); the debug lists well formed; no null slot
original. Its carry from the dispatch state to the exit (the post of the top)
is the remaining G2c work (KENTRY-PLAN g2c).
-/
import Fl4Proofs.P3.XTopJointKEntry32
import Fl4Proofs.P1.FastDecline
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The spec's front keeps the original bits** (module docstring; as
`BudgetAt.shape27`). -/
theorem BudgetAt.orig (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (h : BudgetAt σ σb true) :
    σb.isOriginalCap = σ.isOriginalCap := by
  obtain ⟨σ0, h0, hb⟩ := h
  rw [fl4SyscallFaultIP_eq hk] at h0
  have e0 : σ0 = faultIPSt σ σ.curThread x := congrArg Prod.snd (Set.mem_singleton_iff.1 h0)
  subst e0
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hb
  cases u
  have hb' : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  rw [hb', e]
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`LiveDN` across a step keeping the words it reads** (module docstring). -/
theorem LiveDN.of_keep {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hL : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {s' : S} {σ' : Fl4Spec.State Unit} (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s')
    (hT : ∀ y ∈ P1.Heap.tcbs H, L.mem s' (P1.affA y) = L.mem s (P1.affA y) ∧
      L.mem s' (P1.stA y) = L.mem s (P1.stA y) ∧ L.mem s' (P1.scA y) = L.mem s (P1.scA y) ∧
      L.mem s' (P1.boundA y) = L.mem s (P1.boundA y) ∧ L.mem s' (P1.yieldA y) = L.mem s (P1.yieldA y))
    (hact : L.actionW s' = L.actionW s) (hidle : L.idleW s' = L.idleW s)
    (horig : σ'.isOriginalCap = σ.isOriginalCap) (hid : σ'.idleThread = σ.idleThread) :
    LiveDN (L := L) Z.th H Cs Z.G s' σ' := by
  obtain ⟨hLJ, ⟨lst, hDW⟩, hN⟩ := hL
  have hmem : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
    ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hdead : ∀ p ∈ ZTcb (L := L) Z.th s, DeadP (L := L) H s' p := by
    rintro p ⟨y, hy, zt, n, hz, h65⟩
    have hd := hLJ.zdead y hy p zt n hz h65
    have hth : Z.th p = some .tcb := by
      rcases J.del.zwf y hy p zt n hz with ⟨-, h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h65 h
    have hHp : H p = some .tcb := (hJ.tcb p).1 hth
    obtain ⟨e1, e2, e3, e4, e5⟩ := hT p hHp
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hHp
    refine ⟨fun _ => ⟨e2.trans d1, e3.trans d2, e4.trans d3, hact ▸ d4, hidle ▸ d5, e5.trans d6⟩,
      fun h => ?_, fun h => ?_, fun h => ?_, fun z h => ?_⟩
    all_goals (rw [hHp] at h; cases h)
  exact ⟨hLJ.of_sameZ hSS hmem horig hid hK J.kern.cs0 hTz hdead,
    ⟨lst, hDW.of_keep hK fun y hy => (hT y hy).1⟩, hN.of_same (fun y hy => hSS.capV hy) horig⟩

/-- **A passing `budget_ok` writes `CUR_TIME` and `CONSUMED` only** (module
docstring). -/
theorem budget_ok_frT (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) {T : Set U64} (s : S) (a : A)
    {c : Fl4Spec.Cr3} (hc : AR a c) (hN : P1.NodePlaced st T s (L.cpu s)) :
    syscall.budget_ok st arI s a ⦃ r => r.1 = true → P1.WritesIn st s r.2.1 (fun b =>
      b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨ b = L.nodeAt s (L.cpu s) layout.node.CONSUMED) ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (update_timestamp_fr arI hAK s a hc hN) ?_
  rintro ⟨s1, a1⟩ ⟨w1, -⟩
  try simp only [WP.uncurry'_pair] at w1 ⊢
  refine WP.spec_mono (P1.sched.check_budget_restart.same hA s1 a1) ?_
  rintro ⟨r, s2, a2⟩ e2 hr
  rw [e2 hr]; exact w1

/-- **The FL4 front writes the `FAULT_IP` register and two node words**
(module docstring). -/
theorem front_writes {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    {ct v : U64} {s' : S} {a' : A} (hct : sched.cur_thread st s = ok ct)
    (hb : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a = ok (true, s', a')) :
    P1.WritesIn st s s' (fun b => b = regA ct layout.reg.FAULT_IP ∨
      (b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨ b = L.nodeAt s (L.cpu s) layout.node.CONSUMED)) := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hta := J.ip.e.tcb ct hctT
  have hal : P1.Aligned (regA ct layout.reg.FAULT_IP) := by
    rw [← regIdx_faultIP]; exact (a_reg hta Fl4Spec.Register.faultIP).1
  have w1 : P1.WritesIn st s (L.wr s (regA ct layout.reg.FAULT_IP) v) (· = regA ct layout.reg.FAULT_IP) :=
    P1.writesIn_wr hal
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hN1 : P1.NodePlaced st Z.T (L.wr s (regA ct layout.reg.FAULT_IP) v)
      (L.cpu (L.wr s (regA ct layout.reg.FAULT_IP) v)) := by
    rw [L.cpu_wr]; exact hN.wr
  have h2 := budget_ok_frT hAK hA (L.wr s (regA ct layout.reg.FAULT_IP) v) a J.xtop.fin.1.1.2.2.2.2.2.2 hN1
  rw [hb, WP.spec_ok] at h2
  have w2 := h2 rfl
  refine (w1.trans w2).mono fun b hb => ?_
  rcases hb with e | e | e
  · exact Or.inl e
  · right; left; rw [e, L.cpu_wr, P1.nodeAt_of_ksb (L.ksb_wr _ _ _)]
  · right; right; rw [e, L.cpu_wr, P1.nodeAt_of_ksb (L.ksb_wr _ _ _)]

set_option maxHeartbeats 4000000 in
/-- **`LiveDN` from the entry state to the dispatch state** (module docstring). -/
theorem liveDN_front (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hL : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hS : SInvAll.SInvB σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) {s' : S} {a' : A}
    (hF : KFrontB (L := L) arI s a s' a') {σb : Fl4Spec.State Unit} (hBA : BudgetAt σ σb true) :
    LiveDN (L := L) Z.th H Cs Z.G s' σb := by
  obtain ⟨ct, v, hct, hb⟩ := hF
  have hw := front_writes J hAK hA hct hb
  obtain ⟨x, hk, -⟩ := hS.1.2
  have horig := BudgetAt.orig hnd hk hBA
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hta := J.ip.e.tcb ct hctT
  have h17 : layout.reg.FAULT_IP.val = 17 := by unfold layout.reg.FAULT_IP; rfl
  have hra : (regA ct layout.reg.FAULT_IP).val = ct.val + 392 := by
    rw [regA_val hta (by rw [h17]; omega), h17]
  have hctH : ct ∈ P1.Heap.tcbs H := hTe ▸ hctT
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hnv : ∀ o : U64, o.val < 4288 → (L.nodeAt s (L.cpu s) o).val = L.nodeBase s Z.c + o.val :=
    fun o ho => by rw [P1.nodeAt_val hN ho, hc.cur]
  have hdj : ∀ t ∈ Z.T, t.val + 4096 ≤ L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ t.val := fun t ht => by
    have := hN.disj t ht; rw [hc.cur] at this; exact this
  have hal4 : ∀ t ∈ Z.T, t.val % 4096 = 0 := fun t ht => (J.ip.e.tcb t ht).align
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have h40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have h16 : layout.node.SCHED_ACTION.val = 16 := by simp [layout.node.SCHED_ACTION]
  have h8 : layout.node.IDLE_THREAD.val = 8 := by simp [layout.node.IDLE_THREAD]
  have hCT := hnv _ (by rw [h48]; omega)
  have hCO := hnv _ (by rw [h40]; omega)
  rw [h48] at hCT; rw [h40] at hCO
  have hm : ∀ b, P1.Aligned b → ¬ (b = regA ct layout.reg.FAULT_IP ∨
      (b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨ b = L.nodeAt s (L.cpu s) layout.node.CONSUMED)) →
      L.mem s' b = L.mem s b := fun b hb hn => hw.mem_eq hb hn
  have hct4 := hal4 ct hctT
  have hctd := hdj ct hctT
  -- the slots
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := J.xtop.slotsSame_of hw fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨ct, hctT, by rw [hra]; omega, by rw [hra]; omega⟩))
    · exact Or.inl ⟨by rw [hCT]; omega, by rw [hCT]; omega⟩
    · exact Or.inl ⟨by rw [hCO]; omega, by rw [hCO]; omega⟩
  -- the debug words
  have hreq : regA ct layout.reg.FAULT_IP = core.num.U64.wrapping_add ct 392#u64 :=
    UScalar.eq_of_val_eq (by rw [hra, P1.field_val hta (by decide)]; rfl)
  have hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hw fun b hb => by
    rcases hb with rfl | rfl | rfl
    · exact P1.dbgW_not_kw J.blk (Or.inl ⟨ct, hctH, 392#u64, by decide, by decide, by decide, by decide, hreq⟩)
    · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, J.kern.cpuCs, layout.node.CUR_TIME,
        by simp [layout.node.CUR_TIME], by simp [layout.node.CUR_TIME], rfl⟩))
    · exact P1.dbgW_not_kw J.blk (Or.inr (Or.inl ⟨L.cpu s, J.kern.cpuCs, layout.node.CONSUMED,
        by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], rfl⟩))
  -- the TCB words
  have hfld : ∀ y ∈ P1.Heap.tcbs H, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK4 hK8 hne
    have hyT : y ∈ Z.T := hTe ▸ hy
    have htY := J.ip.e.tcb y hyT
    have hv : (core.num.U64.wrapping_add y K).val = y.val + K.val := P1.field_val htY hK4
    have hy4 := hal4 y hyT
    have hyd := hdj y hyT
    refine hm _ (P1.field_aligned htY hK4 hK8) ?_
    rintro (e | e | e)
    · have := congrArg UScalar.val e; rw [hv, hra] at this; omega
    · have := congrArg UScalar.val e; rw [hv, hCT] at this; omega
    · have := congrArg UScalar.val e; rw [hv, hCO] at this; omega
  have hT : ∀ y ∈ P1.Heap.tcbs H, L.mem s' (P1.affA y) = L.mem s (P1.affA y) ∧
      L.mem s' (P1.stA y) = L.mem s (P1.stA y) ∧ L.mem s' (P1.scA y) = L.mem s (P1.scA y) ∧
      L.mem s' (P1.boundA y) = L.mem s (P1.boundA y) ∧ L.mem s' (P1.yieldA y) = L.mem s (P1.yieldA y) :=
    fun y hy => ⟨hfld y hy 3520#u64 (by decide) (by decide) (by decide),
      by rw [P1.stA_eq]; exact hfld y hy 3328#u64 (by decide) (by decide) (by decide),
      hfld y hy 3464#u64 (by decide) (by decide) (by decide),
      hfld y hy 3368#u64 (by decide) (by decide) (by decide),
      hfld y hy 3472#u64 (by decide) (by decide) (by decide)⟩
  -- the action and idle words
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8o h48o h40o
    rw [hw.2.1, P1.nodeAt_of_ksb hw.1]
    have hv := hnv o ho
    refine hm _ (P1.nodeAt_aligned hN ho h8o) ?_
    rintro (e | e | e)
    · have := congrArg UScalar.val e; rw [hv, hra] at this; omega
    · have := congrArg UScalar.val e; rw [hv, hCT] at this; omega
    · have := congrArg UScalar.val e; rw [hv, hCO] at this; omega
  have hact : L.actionW s' = L.actionW s :=
    hnode _ (by rw [h16]; omega) (by rw [h16]) (by rw [h16]; omega) (by rw [h16]; omega)
  have hidle : L.idleW s' = L.idleW s :=
    hnode _ (by rw [h8]; omega) (by rw [h8]) (by rw [h8]; omega) (by rw [h8]; omega)
  exact LiveDN.of_keep J hL hSS hK hT hact hidle horig (BudgetAt.shape27 hnd hk hBA).2.2.2.2.1

end

/-! ## The bundles and the top -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR2` without `live`** (module docstring); every other field as
`JEntryAt`'s (same tags). -/
structure JEntryAtR3 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.stall`. -/
  stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)
  /-- [J] `JEntryAt.flags`. -/
  flags : FlagsRel Z.T (L.mem s) σ
  /-- [J] `JEntryAt.handlers`. -/
  handlers : HandlersActive (L.mem s) (L.ksb s) Z.G
  /-- [J] `JEntryAt.ports`. -/
  ports : IoPortsAlloc (L.mem s) (L.ksb s) Z.G
  /-- [P] `JEntryAt.ioapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `JEntryAt.archIrq`. -/
  archIrq : ArchIrqRel arI ar σ
  /-- [J] `JEntryAt.vsTyp`. -/
  vsTyp : ∀ y, IsSlot Z.th y → OffTabOK (L := L) Z s σ (capV (L.mem s) y)
  /-- [J] `JEntryAt.fnz`. -/
  fnz : FrNZ Z.th (L.mem s)
  /-- [J] `JEntryAt.urz`. -/
  urz : UtZero (L.mem s) Z.G σ
  /-- [J] `JEntryAt.utks`. -/
  utks : UtNodesJ (L.mem s) Z.G (L.ksb s)

/-- **`KDispHypsKV32` with `JEntryAtR3`** (module docstring). -/
structure KDispHypsKV33 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM32 arI AR Z.th ∧ JEntryAtR3 (L := L) arI AR Z s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM32 arI AR Z.th ∧ JEntryAtR3 (L := L) arI AR Z s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI}

theorem JEntryAtR3.toR2 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (E : JEntryAtR3 (L := L) arI AR Z s ar σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) :
    JEntryAtR2 (L := L) arI AR Z H Cs s ar σ where
  stall := E.stall
  flags := E.flags
  handlers := E.handlers
  ports := E.ports
  ioapics := E.ioapics
  archIrq := E.archIrq
  vsTyp := E.vsTyp
  live := hLv
  fnz := E.fnz
  urz := E.urz
  utks := E.utks

theorem KDispHypsKV33.to32 {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV33 (L := L) arI AR MR Z H Cs D s a σ n c) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) :
    KDispHypsKV32 (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hI => let ⟨g, e, p, v⟩ := h.inv ct call bl don hct hI; ⟨g, e.toR2 hLv, p, v⟩,
    fun ct rg sr cr hct hM => let ⟨g, e, p, v⟩ := h.mid ct rg sr cr hct hM; ⟨g, e.toR2 hLv, p, v⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- **No fast path off `SysReplyRecv`** (FL4 #56): with the trap flag clear
after the FaultIP write and a number in the native range, `handle_syscall`
can take a fast path only for `SysReplyRecv` (`fastpath.fault` sits behind
the trap flag and the out-of-range numbers), so elsewhere it is the general
path. -/
theorem handle_syscall_eq_general_of {s : S} {a : A} {n : I64}
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hr : ¬ n < fl4_abi.syscall.SYSCALL_MIN ∧ ¬ n > fl4_abi.syscall.SYSCALL_MAX)
    (hrr : n ≠ fl4_abi.syscall.SysReplyRecv) :
    syscall.handle_syscall st arI s a n = syscall.handle_syscall_general st arI s a n := by
  unfold syscall.handle_syscall syscall.handle_syscall_general syscall.syscall
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  rw [hct]; simp only [bind_ok]
  obtain ⟨nx, hnx, -⟩ := spec_exists (Endp.obj.Tcb.reg.spec (L := L) s ct layout.reg.NEXT_IP)
  rw [hnx]; simp only [lift, bind_ok]
  obtain ⟨s1, hs1, rfl⟩ := spec_exists (Endp.obj.Tcb.set_reg.spec (L := L) s ct layout.reg.FAULT_IP
    (core.num.U64.wrapping_sub nx 2#u64))
  rw [hs1]; simp only [bind_ok]
  obtain ⟨f, hf, hf0⟩ := spec_exists (hflag ct (core.num.U64.wrapping_sub nx 2#u64) hct)
  rw [hf]; simp only [bind_ok, hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [if_neg hr.1, if_neg hr.2]
  simp only [Std.bind_assoc]
  refine congrArg (Std.bind _) (funext fun r => ?_)
  obtain ⟨b, s2, a1⟩ := r
  cases b <;> (try simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, if_neg hrr, Std.bind_assoc,
    bind_ok]) <;> (try rfl)

/-- **[P] `SysReplyRecv`'s fast path keeps what the general path guarantees,
where it answers** (m57; `P1.FastAcc` narrowed for J33): at every dispatch
state of the entry (`KFrontB`: the `FAULT_IP` write, then a passing
`budget_ok`), a run of `fastpath.reply_recv` that answers (`true`) ends in a
state satisfying `P` whenever the general path's runs do. A declined
`fastpath.reply_recv` changes nothing (`P1.reply_recv_decline`), so it is
not asked about. l4v: `Fastpath_C` `fastpath_reply_recv` refines the slow
path where it does not fall back. -/
def FastRR (s : S) (a : A) (n : I64) (P : S × A → Prop) : Prop :=
  ∀ s2 a2 s' a', KFrontB (L := L) arI s a s2 a2 → fastpath.reply_recv st arI s2 a2 = ok (true, s', a') →
    syscall.handle_syscall_general st arI s a n ⦃ P ⦄ → P (s', a')

/-- With the trap flag clear after the `FAULT_IP` write and a native number
`SysReplyRecv`, a run of `handle_syscall_fast` that a fast path answered is
a run of `fastpath.reply_recv` from a dispatch state (`KFrontB`), so
`FastRR` gives `P1.FastAcc`. -/
theorem FastRR.acc {s : S} {a : A} {n : I64} {P : S × A → Prop}
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hr : ¬ n < fl4_abi.syscall.SYSCALL_MIN ∧ ¬ n > fl4_abi.syscall.SYSCALL_MAX)
    (hrr : n = fl4_abi.syscall.SysReplyRecv) (h : FastRR (L := L) (arI := arI) s a n P) :
    P1.FastAcc st arI s a n P := by
  intro hg s' a' e
  unfold syscall.handle_syscall_fast syscall.syscall at e
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  rw [hct] at e; simp only [bind_tc_eq, bind_ok] at e
  obtain ⟨nx, hnx, -⟩ := spec_exists (Endp.obj.Tcb.reg.spec (L := L) s ct layout.reg.NEXT_IP)
  rw [hnx] at e; simp only [lift, bind_tc_eq, bind_ok] at e
  obtain ⟨s1, hs1, rfl⟩ := spec_exists (Endp.obj.Tcb.set_reg.spec (L := L) s ct layout.reg.FAULT_IP
    (core.num.U64.wrapping_sub nx 2#u64))
  rw [hs1] at e; simp only [bind_tc_eq, bind_ok] at e
  obtain ⟨f, hf, hf0⟩ := spec_exists (hflag ct (core.num.U64.wrapping_sub nx 2#u64) hct)
  rw [hf] at e; simp only [bind_tc_eq, bind_ok, hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at e
  simp only [if_neg hr.1, if_neg hr.2] at e
  have e' := P1.spec_of_eq_fd e
  clear e
  obtain ⟨⟨b, s2, a1⟩, eb, e'⟩ := P1.spec_bind_inv e'
  try simp only [uncurry_apply_pair] at e'
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at e'
    obtain ⟨_, -, e'⟩ := P1.spec_bind_inv e'
    try simp only [P1.uncurry_eta_fd] at e'
    rw [WP.spec_ok] at e'
    simp at e'
  simp only [↓reduceIte, if_pos hrr] at e'
  obtain ⟨⟨b1, s3, a2⟩, er, e'⟩ := P1.spec_bind_inv e'
  try simp only [uncurry_apply_pair] at e'
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at e'
    obtain ⟨_, -, e'⟩ := P1.spec_bind_inv e'
    try simp only [P1.uncurry_eta_fd] at e'
    obtain ⟨_, -, e'⟩ := P1.spec_bind_inv e'
    try simp only [P1.uncurry_eta_fd] at e'
    rw [WP.spec_ok] at e'
    simp at e'
  simp only [↓reduceIte, WP.spec_ok, Prod.mk.injEq, true_and] at e'
  rw [← e'.1, ← e'.2]
  exact h s2 a1 s3 a2 ⟨ct, _, hct, eb⟩ er hg

set_option maxHeartbeats 4000000 in
/-- **The newest top on the general path** (module docstring):
`kernel_entryJ32`'s premises, with the bundles inside `hK`
(`KDispHypsKV33`) free of `JEntryAt.live`, which is asked once, at the entry
state and its carried ghosts (`hLv` [J]). It speaks of
`handle_syscall_old`, the pre-#56 entry, which is `handle_syscall_general`
(`P1.handle_syscall_general_eq`); `kernel_entryJ33` below is the entry
itself. -/
theorem kernel_entryJ33G [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ32 s a σ J hni hR hS hE hQ n c hn hflag hB
    (fun σb hBA V' Ac' Lst' D' s' a' hF J' => (hK σb hBA V' Ac' Lst' D' s' a' hF J').to32
      (liveDN_front hnd J hLv hS hARI.toARKeep hA hF hBA))
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring; since FL4 #56 about the entry
`handle_syscall`, which may take a fast path): `kernel_entryJ33G`'s
premises and one more, `hFast` [P]: for `SysReplyRecv` only (the one native
number whose entry has a fast path, `handle_syscall_eq_general_of`), the
fast path keeps what the general path guarantees where it answers (`FastRR`:
only runs of `fastpath.reply_recv` that end `true`, from a dispatch state;
m57 narrowed it from m56's `P1.FastAgree` with the decline lemmas of
P1.FastDecline). -/
theorem kernel_entryJ33 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPost (L := L) arI AR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hG := kernel_entryJ33G s a σ J hni hR hS hE hQ hLv n c hn hflag hB hK hFin hARI hA hnd hM hKD hPA hIA
    hmrt hmb hT hmax htu
  by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
  · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
      (FastRR.acc hflag hn.range hrr (hFast hrr))) hG
  · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG


/-- **`kernel_entryJ33` without `hLv`** (KENTRY-PLAN g2i batch 3, g2j): the
liveness bundle at the entry is the entry `JAtZ`'s own field (`JAtZ.live`). -/
theorem kernel_entryJ34 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPost (L := L) arI AR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ33 s a σ J hni hR hS hE hQ J.live n c hn hflag hB hK hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax
    htu hFast

end

end

end Fl4Proofs.P3
