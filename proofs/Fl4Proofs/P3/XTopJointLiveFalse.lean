/-
P3 (DESIGN.md §9), invariant line G2 (KENTRY-PLAN g2d, g2e): **the two
exemptions of `LiveJ`** and the corrected boot obligation of `LiveDN`.

KENTRY-PLAN g2d found `LiveDN` (`LiveJ` ∧ `DbgWF` ∧ `NullOrig`, the premise
`hLv` of `kernel_entryJ33` [J]) false in every FL4 state reachable from boot,
in two situations:
* the idle thread is on core 0's debug list since boot (`boot.rs`
  `init_core_state` appends every core's idle thread when
  `fl4_abi::config::DEBUG_BUILD`), and no cap names it (`SpecGlob.idle`);
* an IRQ node slot holds a notification cap after `SetIRQHandler`
  (`interrupt.rs` `decode_irq_handler`, spec `invokeIRQHandler`'s
  `capInsert`), and no cap names the radix-0 CNode it lies in
  (`SpecGlob.ref`).

g2e re-scoped `LiveJ` (XTopJointLive) as l4v does: `if_live_then_nonz_cap`
exempts the idle thread (`dbg` asks a thread cap only for a debug-listed TCB
other than the spec's idle thread), and an IRQ node slot is covered by the
kernel's IRQ state, not by a cap (`slots` also accepts a slot inside the
kernel-state block, `KsSlot`). This module checks that the refutations no
longer apply:

* `liveJ_dbg_idle`: at a `JAtZ` state, `LiveJ.dbg` asks nothing of a debug-list
  entry that is the idle word (its premise is false, `JAtZ.idleThread_bv`):
  core 0's idle thread may sit on the list.
* `irqNode_ksSlot`: every IRQ node slot lies in the kernel-state block, so
  `LiveJ.slots` holds there without a cap: the slot may hold a cap.
* `LiveJ.of_l4v`: `LiveJ` from l4v-shaped facts that say nothing about the
  idle thread nor about the IRQ node slots (a cap for each other slot in use,
  a thread cap for each other debug-listed TCB, the zombie facts). So `LiveJ`
  holds at states with the idle thread on the debug list and any IRQ node
  slots in use, as long as the rest is covered.
* `LiveBootW` / `liveDN_of_boot`: the corrected boot obligation [W] (for G4's
  `BootJ`, replacing g2c (4)): every slot in use outside the IRQ node has an
  MDB cap naming its container (at FL4's boot: the root CNode and the root
  TCB, named by the root caps; the IRQ node slots null as boot sets no
  handler, but they need no cover either way), every debug-listed TCB other
  than the idle thread is named by a thread cap (the root TCB), the zombie
  facts (no zombie at boot), `DbgWF` (the idle threads and the root TCB on
  their cores' lists) and `NullOrig`.
-/
import Fl4Proofs.P3.XTopJointWJLRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`LiveJ.dbg` asks nothing of the idle thread** (module docstring): at a
`JAtZ` state, a debug-list entry equal to the idle word fails `dbg`'s
premise. -/
theorem liveJ_dbg_idle {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (n : Nat)
    (e : dbgNth (L.mem s) n (dbgHead (L := L) s) = L.idleW s) :
    ¬ (dbgNth (L.mem s) n (dbgHead (L := L) s)).bv ≠ σ.idleThread := by
  rw [e, J.idleThread_bv]; exact fun h => h rfl

/-- **Every IRQ node slot lies in the kernel-state block** (module
docstring): `LiveJ.slots` holds there with no cap. -/
theorem irqNode_ksSlot {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (i : U64) (hi : i.val < 128) :
    IsSlotAt Z.th (nodeA (L.ksb s) i) 0 ∧ KsSlot (L.ksb s) (slotOf (nodeA (L.ksb s) i) 0) := by
  have hIS : IsSlotAt Z.th (nodeA (L.ksb s) i) 0 := Or.inl ⟨0, J.intL.node i hi, by norm_num⟩
  refine ⟨hIS, ?_⟩
  have hv := hIS.val J.xtop.rel.1
  have hn := nodeA_val J.intL.fit hi
  show (L.ksb s).val ≤ (slotOf (nodeA (L.ksb s) i) 0).val ∧
    (slotOf (nodeA (L.ksb s) i) 0).val < (L.ksb s).val + 13568
  omega

/-- **`LiveJ` from l4v-shaped facts** (module docstring): the IRQ node slots
and the idle thread need no cover. -/
theorem LiveJ.of_l4v {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hs : ∀ q i, IsSlotAt Z.th q i → InUse (L.mem s) σ (slotOf q i) →
      (∀ j : U64, j.val < 128 → q ≠ nodeA (L.ksb s) j) →
      ∃ y ∈ Z.G.chains.flatten, RefsObj q (capV (L.mem s) y))
    (hd : ∀ n, dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ 0#u64 →
      dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ L.idleW s →
      ∃ y ∈ Z.G.chains.flatten, capV (L.mem s) y = .Thread (dbgNth (L.mem s) n (dbgHead (L := L) s)))
    (hz : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n →
      ∀ i, IsSlotAt Z.th p i → n.val ≤ i → ¬ InUse (L.mem s) σ (slotOf p i))
    (hzd : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n → zt.val = 65 →
      DeadP (L := L) H s p) :
    LiveJ (L := L) Z.th H Z.G s σ := by
  refine ⟨fun q i hqi hu => ?_, fun n hn hni => hd n hn fun e => hni (by rw [e, J.idleThread_bv]), hz, hzd⟩
  by_cases hq : ∃ j : U64, j.val < 128 ∧ q = nodeA (L.ksb s) j
  · obtain ⟨j, hj, rfl⟩ := hq
    have hP := J.xtop.rel.1
    have h0 : i = 0 := by
      rcases hqi with ⟨r, hr, hlt⟩ | ⟨ht, -⟩
      · rw [J.intL.node j hj] at hr; cases hr; simpa using hlt
      · rw [J.intL.node j hj] at ht; cases ht
    subst h0
    exact Or.inr (irqNode_ksSlot J j hj).2
  · exact Or.inl (hs q i hqi hu fun j hj e => hq ⟨j, hj, e⟩)

/-- **The corrected boot obligation of `LiveDN`** [W] (G4's `BootJ`; module
docstring; replaces KENTRY-PLAN g2c (4)): the inputs of `LiveJ.of_l4v`, the
debug lists well formed and no null slot original. -/
structure LiveBootW (s : S) (σ : Fl4Spec.State Unit) : Prop where
  slots : ∀ q i, IsSlotAt Z.th q i → InUse (L.mem s) σ (slotOf q i) →
    (∀ j : U64, j.val < 128 → q ≠ nodeA (L.ksb s) j) →
    ∃ y ∈ Z.G.chains.flatten, RefsObj q (capV (L.mem s) y)
  dbg : ∀ n, dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ 0#u64 →
    dbgNth (L.mem s) n (dbgHead (L := L) s) ≠ L.idleW s →
    ∃ y ∈ Z.G.chains.flatten, capV (L.mem s) y = .Thread (dbgNth (L.mem s) n (dbgHead (L := L) s))
  zslots : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n →
    ∀ i, IsSlotAt Z.th p i → n.val ≤ i → ¬ InUse (L.mem s) σ (slotOf p i)
  zdead : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s) y = .Zombie p zt n → zt.val = 65 →
    DeadP (L := L) H s p
  dwf : DbgWF (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s)
  norig : NullOrig Z.th (L.mem s) σ

/-- **`LiveDN` from the boot obligation** (module docstring). -/
theorem liveDN_of_boot {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (h : LiveBootW (L := L) (Z := Z) (H := H) (Cs := Cs) s σ) :
    LiveDN (L := L) Z.th H Cs Z.G s σ :=
  ⟨LiveJ.of_l4v J h.slots h.dbg h.zslots h.zdead, h.dwf, h.norig⟩

end

end

end Fl4Proofs.P3
