/-
P3 (DESIGN.md §9): **the joint invariant at a state, `JAt`** (the fold plan's
§1, `/home/user/Projects/.fl4-fold-plan.md`). One structure over the ghosts
(the typed heap and sets `Z`, P1's heap `H`, cores `Cs`, active SCs `Ac`,
the ghost call stacks `Lst`, the dead set `D`), grouped as the plan's 1a–1e:

* 1a the refinement relation: `XTopAt`, the call stacks (`CallRel`,
  `RFree`), yield, MCP, IPC-buffer words;
* 1b placement: the ghost sets placed and exhaustive, P1's heap `H` over the
  typed heap (`JPlaced`, `SpecCover`, `ObjCover`), `SpecFree`, the dead set
  (`JCovD`), the kernel-global placement (`JKern`);
* 1c CSpace: `DelInv`, `UtInv`, the CNode-size and fuel bound (`DelBound`),
  the untyped caps' facts (`UtCapP3`);
* 1d scheduler: `NSC`, `Inv`, `CurInv`, `OffOK`, `ActIdle`, `BlockedScActive`
  ([J]), `SchedValid`, `IpcSorted`, `CurRun`;
* 1e P1: `BlkOK` over `H`'s sets.

Projections to each leaf bundle: `WX`, `DState`, `IpcZ`, `ScExtra`,
`UtJoint`/`UtP3Ok`, `RemoveOK`, `DonNCOK`, `DonOK`, `PushDonOK`, and the P1
placement facts (`JAtZ.capTyped`, `JAtZ.slotCapW`, `JAtZ.mpPlaced`).

No preservation is proved here. Fields marked **[carried]** are facts the
projections need that the plan's groups did not list; several are derivable
from the others (noted per field) and are to be dropped once derived.
Projection premises marked **[global]** are not state facts (the platform,
or "∀ related states" hypotheses that the fold re-scopes, plan §0).

Merges (plan §1): `ARIface` (`ARKeep` with `ARMask`), `DelBound.delE`
(CnodeAll's `K`, `hK`, `hK6` and `DelE` from `DelBound`), `SchedValid.toLink`
(`ScLinkHyp`, whose `scSpor` is `SchedValid.scSpor`).
-/
import Fl4Proofs.P3.XTopCnodeAll
import Fl4Proofs.P3.XTopTcbAll
import Fl4Proofs.P3.IpcSendDon
import Fl4Proofs.P3.ScXProd
import Fl4Proofs.P3.ScUtRetype
import Fl4Proofs.P3.ScIpcSorted
import Fl4Proofs.P3.ScRecvLinks
import Fl4Proofs.P3.VsCapW
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P3.LiveDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## Merges -/

section
variable {A : Type} (arI : machine.Arch A)

/-- **The arch relation's interface** (`ARKeep` with `ARMask`, one premise). -/
structure ARIface (AR : A → Fl4Spec.Cr3 → Prop) : Prop extends ARKeep arI AR where
  mask : ∀ a c a', AR a c → ArchIrqStep arI a a' → AR a' c

theorem ARIface.toMask {AR : A → Fl4Spec.Cr3 → Prop} (h : ARIface arI AR) : ARMask arI AR := h.mask

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`DelBound` gives the CNode deletions' bound and `DelE`** (CnodeAll's
`K`, `hK`, `hK6`, `hDE`), with `DelInv`, `KTyped` and `FinM` at every tree. -/
theorem DelBound.delE {th : TypedHeap} (hB : DelBound th) {s : S} {σ : Fl4Spec.State Unit}
    (hD : DelInv th (L.mem s)) (hK : KTyped th σ) (hF : ∀ G, MdbLinks th (L.mem s) G → FinM (L.mem s) G) :
    ∃ K, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧ DelE (L := L) th K s σ := by
  obtain ⟨K, h1, h2, h3⟩ := hB
  exact ⟨K, h1, h2, hD, fun G hG => h3 _ G hG, hK, hF⟩

end

/-- **`ScLinkHyp` is part of `SchedValid`** (its `scSpor` is `SchedValid.scSpor`). -/
theorem Sched.SchedValid.toLink {σ : Fl4Spec.State Unit} (h : Sched.SchedValid σ) : Sched.ScLinkHyp σ :=
  ⟨h.scTcb, h.scNtfn, h.tcbNtfn, h.scSpor⟩

/-! ## `JAt` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[carried] The kernel-global placement and the current thread** (what
`UtJoint` reads): the original caps' slots, the current thread (a TCB of
`th` and of `H`, the spec's), the current SC (an `H` object; live unless a reschedule is pending, derived: `JAtZ.cscLive`), the
scheduler-action word outside the objects, core 0's debug-list head and
word, the global PML4, and `H` well formed and off the kernel-global area
and the nodes. Several are derivable (`cur`, `curT`: `SchedRel`/`CurOK`;
`heap`, `h0`, `hks`, `hnd`: `BlkOK`/`JPlaced`). -/
structure JKern (H : P1.Heap) (Cs D : Set U64) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  orig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl
  cur : σ.curThread = (L.curW s).bv
  curT : th (L.curW s) = some .tcb
  act : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
  dwAl : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
  dwObj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32)
  dwNe : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s)).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val
  head : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
    (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
      TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))
  gpm : HasPm σ σ.archState.x64GlobalPml4
  ga : σ.archState.x64GlobalPml4.toNat % 4096 = 0
  gf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64
  heap : P1.HeapOK H
  h0 : H 0#u64 = none
  hks : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → p.val + 2 ^ k.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val
  hksIn : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
    ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568)
  hnd : ∀ p k, H p = some k → ∀ c ∈ Cs, p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val
  ksbFit : (L.ksb s).val + 13568 ≤ 2 ^ 64
  ksbAl : (L.ksb s).val % 8 = 0
  nodeFit : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64
  cpuCs : L.cpu s ∈ Cs
  curH : H (L.curW s) = some .tcb
  cscH : H (L.cscW s) ≠ none
  /-- [carried] The cores are numbered below 64 (boot; `Cs` never grows). -/
  csLt : ∀ c ∈ Cs, c.val < 64
  /-- [carried] Core 0, the boot core, is among the cores (boot; `Cs` never
  shrinks). -/
  cs0 : 0#u64 ∈ Cs

/-- **The joint extension** (INV-PLAN §4 G2; KENTRY-PLAN g2a): the facts
carried with `JAtZ` as one sub-structure `JAtZ.ext`, so that a new fact adds
one component to `JAtZ`'s anonymous constructions. Field so far:
* `nat` [S] (G2 `nativeScopeX`, VT-x out of scope; l4v: x64 has no VT-x
  objects, so no valid VCPU / EPT cap): every slot's cap is `Vs.NativeCap`
  (no VCPU or EPT cap, no EPT-mapped frame cap, no IO-port cap owned by a
  VCPU). Kept by every native step: slots kept (`of_eq`), stepped
  (`Vs.VsSlotsT`'s third part: emptied slots, copies of a native cap, native
  new caps), or a retype's new native caps. A VT-x invocation (`JVtxScope`)
  breaks it: its statement then asks `JAt` after a step outside the scope.
* `vw` [S] (G2 `nativeScopeX`, KENTRY-PLAN g2b; l4v: no counterpart, the
  spec has no TCB–VCPU binding): every TCB of the typed heap has its VCPU
  word (`tVcpuA t`, offset 3664) zero. FL4 writes that word only in
  `vcpu::detach` (writes 0) and the `X86VCPUSetTCB` invocation of a Vcpu cap
  (excluded by `nat`); a TCB retype zeroes it. So every native step keeps it:
  the frames below take `VKeep` (the word of every TCB kept), proved from
  each step's footprint (`TFoot` / `FinW` / `WideW` exclude it). -/
structure JExt (th : TypedHeap) (s : S) : Prop where
  nat : Vs.VsNat th (L.mem s)
  vw : ∀ t, th t = some .tcb → L.mem s (tVcpuA t) = 0#u64

/-- The VCPU words of the typed heap's TCBs kept from `s` to `s'`. -/
def VKeep (th : TypedHeap) (s s' : S) : Prop :=
  ∀ t, th t = some .tcb → L.mem s' (tVcpuA t) = L.mem s (tVcpuA t)

theorem VKeep.rfl' {th : TypedHeap} {s : S} : VKeep (L := L) th s s := fun _ _ => rfl

theorem VKeep.trans {th : TypedHeap} {s s1 s2 : S} (h1 : VKeep (L := L) th s s1) (h2 : VKeep (L := L) th s1 s2) :
    VKeep (L := L) th s s2 := fun t ht => (h2 t ht).trans (h1 t ht)

/-- `VKeep` from a `WritesIn` footprint missing every TCB's VCPU word. -/
theorem VKeep.of_writes {th : TypedHeap} {T : Set U64} (hT : P1.TcbPlaced T) (hth : ∀ t, th t = some .tcb → t ∈ T)
    {s s' : S} {W : U64 → Prop} (hW : P1.WritesIn st s s' W) (hWV : ∀ b, W b → ∀ t ∈ T, b ≠ tVcpuA t) :
    VKeep (L := L) th s s' := fun t ht =>
  hW.mem_eq (Sched.tVcpuA_aligned hT (hth t ht)) fun hb => hWV _ hb t (hth t ht) rfl

theorem JExt.vkeep {th : TypedHeap} {s s' : S} (E : JExt (L := L) th s) (hv : VKeep (L := L) th s s') :
    ∀ t, th t = some .tcb → L.mem s' (tVcpuA t) = 0#u64 := fun t ht => (hv t ht).trans (E.vw t ht)

theorem JExt.of_eq {th : TypedHeap} {s s' : S} (E : JExt (L := L) th s)
    (hc : ∀ y, IsSlot th y → capV (L.mem s') y = capV (L.mem s) y) (hv : VKeep (L := L) th s s') :
    JExt (L := L) th s' :=
  ⟨E.nat.of_eq hc, E.vkeep hv⟩

theorem JExt.step {th : TypedHeap} {s s' : S} (E : JExt (L := L) th s)
    (hT : Vs.VsSlotsT th (L.mem s) (L.mem s')) (hv : VKeep (L := L) th s s') : JExt (L := L) th s' :=
  ⟨E.nat.step hT, E.vkeep hv⟩

theorem JExt.ss {th : TypedHeap} {s s' : S} (E : JExt (L := L) th s)
    (hSS : SlotsSame th (L.mem s) (L.mem s')) (hv : VKeep (L := L) th s s') : JExt (L := L) th s' :=
  E.of_eq (fun _ hy => hSS.capV hy) hv

/-- `JExt` at the same memory. -/
theorem JExt.mem {th : TypedHeap} {s s' : S} (E : JExt (L := L) th s) (h : L.mem s' = L.mem s) :
    JExt (L := L) th s' :=
  E.of_eq (fun y _ => by rw [h]) fun t _ => by rw [h]

/-- **The joint invariant at the ghosts** (module docstring; plan §1). -/
structure JAtZ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  -- 1a: the refinement relation
  xtop : XTopAt (L := L) AR Z s a σ
  call : Sched.CallRel (L.mem s) Z.R Z.C σ Lst
  rfree : Sched.RFree (L.mem s) Z.R Z.C σ Lst
  /-- A reply bound to a thread blocked receiving has null links (ScRecvLinks;
  l4v `valid_replies`). -/
  rrecv : Sched.RRecv (L.mem s) Z.R σ
  yld : Sched.YieldRel Z.T Z.C (L.mem s) σ
  mcp : Sched.McpRel Z.T (L.mem s) σ
  buf : BufWordRel Z.T (L.mem s) σ
  -- 1b: placement
  ks : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)
  thT : ∀ t, Z.th t = some .tcb → t ∈ Z.T
  /-- [carried] `Z.th` holds TCBs and CNodes only (its one producer, the
  retype's `ThX`, adds `thKindN`'s kinds; deletions only drop entries). -/
  thk : ∀ q k, Z.th q = some k → k = .tcb ∨ ∃ r, k = .cnode r
  ip : IPlaced Z.N Z.T Z.E Z.R Z.B
  rp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s σ
  apart : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s σ
  nk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val
  /-- [carried] The IPC-buffer words miss every node slot of the kernel-state
  block (all 64 cores', not only `Cs`'s: the buffer words are user frames;
  kept by every step, `Z.B` grows only by a frame retype from an untyped
  region, which misses the block). -/
  nodeB : ∀ wp ∈ Z.B, ∀ c : U64, c.val < 64 → wp.1.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ wp.1.val
  jpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s σ
  cover : Sched.SpecCover H σ
  obj : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ
  /-- [carried] The sets' objects are `H`'s (derivable: `IpcRel`/`SchedRel`
  and `SpecCover`, `JPlaced`). -/
  zH : (∀ t ∈ Z.T, H t = some .tcb) ∧ (∀ e ∈ Z.E, H e = some .ep) ∧ (∀ r ∈ Z.R, H r = some .reply) ∧
    (∀ n ∈ Z.N, H n = some .ntfn)
  sfree : Sched.SpecFree (L.mem s) Z.G σ
  /-- [carried] `H`'s endpoints, notifications and replies are the sets'
  (the converse of `zH`; for the `SchedValid` rebuild). -/
  hset : (∀ e, H e = some .ep → e ∈ Z.E) ∧ (∀ n, H n = some .ntfn → n ∈ Z.N) ∧
    (∀ r, H r = some .reply → r ∈ Z.R)
  /-- [carried] `H`'s SCs are `Z.C`'s (the converse of `JPlaced.sc` with
  `ObjCover.sc`; l4v: an SC object of the heap is one the scheduler
  relation covers). Kept by every step at `J` (each keeps `H` and `Z.C`;
  a retype adds its new SCs to both). The idle SC, when the spec has one at
  a non-null address, is in both (`JPlaced.sc`, `ObjCover.sc`); a cap never
  names it (`CapObjH`). With `JPlaced.cobj` it gives an SC cap's spec SC
  (`JAtZ.scCap`). -/
  hscC : ∀ c z, H c = some (.sc z) → c ∈ Z.C
  jcov : Sched.JCovD (L := L) Z.th H Z.G D Cs s
  kern : JKern (L := L) H Cs D Z.th s σ
  -- 1c: CSpace
  del : DelInv Z.th (L.mem s)
  ut : UtInv (L.mem s) Z.G
  bound : DelBound Z.th
  /-- [carried] `FinM` at every tree of the slots (`FinInv` gives it at
  `Z.G`; `DelE` reads every `G`). -/
  finM : ∀ G, MdbLinks Z.th (L.mem s) G → FinM (L.mem s) G
  /-- [carried] The RAM untyped caps' facts (`UtCapP3`: l4v `valid_untyped`,
  `valid_cap`, the kernel's placement). Not asked of device untypeds: since
  losfair/FL4#34 a device untyped's pointer `paddr + PPTR_BASE` may lie in
  the kernel image, so its region may hold the kernel-state block with the
  IRQ node's CNodes (`IntLayout.node`, objects of `Z.th` with MDB slots) and
  the preemption point's word: `free`, `nostr`, `nsFree`, `ns` and `pp` are
  false of such a cap at boot. -/
  utc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := L) arI Z.th s σ Z.G sl p sb fi
  -- 1d: the scheduler
  nsc : Sched.NSC Z.N Z.C σ
  inv : Sched.Inv σ
  /-- `CurInv` unless a reschedule is pending (mid-entry, as `ScEntry`). -/
  cur : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ
  /-- The current SC's owner, or the current SC unowned (`CurOwnW`, what
  `schedule` from a mid-entry state reads; unowned after the current thread
  deleted itself or unbound its SC; `curOwn_of_curInv` where `CurInv`
  holds). -/
  own : Sched.CurOwnW Z.T Z.C σ
  off : Sched.OffOK σ
  act : Sched.ActIdle σ
  c0 : ∀ q ∈ Z.C, q ≠ 0#u64
  bsa : Sched.BlockedScActive σ
  sv : Sched.SchedValid σ
  /-- The spec's IPC queues sorted by priority (l4v `sorted_ipc_queues`). -/
  isorted : Sched.IpcSorted σ
  /-- The spec's SC, TCB and notification links (per-op; for the
  `SchedValid` rebuild). -/
  slink : Sched.ScLinkHyp σ
  /-- The current thread runnable, or the idle thread current (`CurRunW`:
  at kernel exit `schedule` may have chosen the idle thread), unless a
  reschedule or switch is pending (`CurRunM`: mid-entry after a blocking
  step, or after suspending the current thread with a switch pending). -/
  curRun : CurRunM σ
  -- 1e: P1
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s
  /-- [carried] The interrupt state and node layout (`IntLayout`, the boot's
  [P]; kept by every step: `Z.th` and the kernel-state base are kept). -/
  intL : IntLayout Z.th (L.ksb s)
  /-- [carried] **The VSpace caps placed in the relation's own sets**, weakened
  (VsCapW's `VsCapsW`: l4v `valid_cap` for the arch caps with
  `valid_table_caps`), at every slot of the typed heap: an unmapped page-table/directory/PDPT cap's table in
  its set, a PML4 or ASID pool cap's object in its set, the ASID and
  alignment facts; a mapped table may lie outside the sets (pruned by a
  detype). Kept by every step (`VsSlotsW.of_eq` for slots kept,
  `VsSlotsT` for the slot steps, `VCapW.transfer` for a copy), the sets kept
  or grown. -/
  vsc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s)
  /-- [carried] **Every IPC frame cap valid** (l4v `valid_ipc_buffer_cap`,
  from `valid_objs`; FL4's form `Endp.IpcBufCapOK`: the buffer's words in a
  user frame, so an alias inside a large page from `Page_DeriveSubframe`
  counts). Kept by every step not touching an IPC frame or a data page
  (`IpcFrKeep`), set by SetIPCBuffer/Configure (`IpcBufCapOK.setFrame`, the
  cap checked), dropped TCBs' frames by `IpcBufCapOK.sdrop`. -/
  bok : Endp.IpcBufCapOK σ
  /-- [carried] **`B` covers every word of every non-device user frame**
  (`FrameCover`; FL4's ghost `B` relates FL4 memory and the spec's
  `underlyingMemory` there, l4v's shared `machine_state`). Kept by every step
  keeping the data pages (`FrameCover.ipcFr`), grown with `B` at the frame
  retype, shrunk with `B` at the detype (`FrameCover.sdrop`). -/
  fcov : FrameCover Z.B σ
  /-- [carried] **Every non-device frame cap names user frames** (l4v
  `valid_cap` for frame caps: each byte of a slot's frame cap range lies in a
  non-device data page). Kept by every step keeping the data pages and moving
  frame caps within old ranges (`Vs.VsSlotsT`'s `FrSlots` part: copy, mint,
  move, swap, DeriveSubframe's sub-range), set at the frame retype for the new
  pages, released at the detype by `FrameOffJ`. -/
  fcap : Vs.FrSlots Z.th (UFr σ) (L.mem s)
  /-- [carried] **The joint extension** (`JExt`, G2). -/
  ext : JExt (L := L) Z.th s
  /-- [carried] **The liveness bundle at the ghosts** (KENTRY-PLAN g2i; INV-PLAN
  E15, the former `JEntryAt.live` / `kernel_entryJ33`'s `hLv` [J]): `LiveJ`
  (l4v `if_unsafe_then_cap`, `if_live_then_nonz_cap`, `zombies_final`; the idle
  thread and the kernel-state block exempt, KENTRY-PLAN g2e), `DbgWF` (FL4's
  debug lists) and `NullOrig` (l4v `valid_nullcaps`) at `Z.th`, `H`, `Cs`,
  `Z.G`. Each construction proves it where its frames are visible
  (`JAtZ.liveX` for a step keeping the slots). -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [carried] **The TCB zombies' TCBs are in the dead set** (so a frame step's
  dead-set carry keeps `LiveJ.zdead`; every TCB zombie's TCB is `DeadP` by
  `live`, so `D ∪ ZTcb` is always a dead set: `JAtZ.addDeadSet`). -/
  zD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D

/-- **`JAt`: the joint invariant at a state** (the ghosts existential). -/
def JAt (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ

/-! ## Projections -/

namespace JAtZ
variable {arI} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- `WX` (the deletions' bundle). -/
theorem wx (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : WX (L := L) AR Z.th s a σ Z.G :=
  ⟨Z, rfl, rfl, J.xtop, J.ks, J.thT⟩

/-- The MDB tree's links (`CRel`'s). -/
theorem mdbL (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : MdbLinks Z.th (L.mem s) Z.G :=
  J.xtop.rel.2.1.2.2.1

/-- `DState` (the CSpace deletions' state). -/
theorem dstate (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : DState (L := L) Z.th s σ Z.G :=
  ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩

/-- CnodeAll's bound and `DelE` (`DelBound.delE`). -/
theorem delE (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∃ K, (∀ p r, Z.th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧ DelE (L := L) Z.th K s σ :=
  J.bound.delE J.del J.xtop.rel.2.2.1.kt J.finM

/-- **No SC of `H` lies outside `Z.C`** (`hscC`): any statement about
`H`'s SCs outside `Z.C` holds vacuously (XTopJointFinVs's
`JVsApartHyp.scOut`). -/
theorem scOut (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {P : U64 → Nat → Prop} :
    ∀ p z, H p = some (.sc z) → p ∉ Z.C → P p z :=
  fun p z hp hpC => absurd (J.hscC p z hp) hpC

/-- `ScLinkHyp`. -/
theorem link (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : Sched.ScLinkHyp σ := J.sv.toLink

/-- `IpcZ`, given the IPC tails' [global] hypotheses (re-scoped by the fold); its
`TailOK` from `ActIdle` and `Inv` (`tailOK_of`). -/
theorem ipcZ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (cr : Fl4Spec.Cr3) {ct : U64}
    (hH : IpcSchedHyps st arI Z.N Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)))
    (hBf : EpBufHyps st Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)))
    (hBm : EpBufMapHyps st Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)))
    (hct : ct ∈ Z.T) :
    IpcZ (L := L) arI cr s σ ct Z :=
  ⟨J.ks, J.buf, hH, hBf, hBm, tailOK_of J.act.1 J.inv, J.ip, hct⟩

/-- `CurInv` when no reschedule is pending. -/
theorem curInv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (h : σ.schedulerAction ≠ .chooseNewThread) :
    Sched.CurInv σ := J.cur.resolve_left h

/-- **The current SC is live unless a reschedule is pending**: outside the
dead set, or `chooseNewThread`. Derived, not carried: under `CurInv` the
current thread is bound to the current SC, so (`Inv.back`) the SC's `TCB`
word names it, while a dead SC's `TCB` word is null (`DeadP`). A dead
current SC arises only when the current thread finalises the last cap to its
own SC, which unbinds it and asks for a reschedule. -/
theorem cscLive (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    L.cscW s ∉ D ∨ σ.schedulerAction = .chooseNewThread := by
  by_cases hcn : σ.schedulerAction = .chooseNewThread
  · exact Or.inr hcn
  refine Or.inl fun hD => ?_
  have hC := J.curInv hcn
  obtain ⟨xt, hkt, hsc, -⟩ := hC.tcb
  obtain ⟨y, n, hy, hyt⟩ := J.inv.back _ xt _ hkt hsc
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have ecs : L.cscW s = Sched.nodeW st s Z.c layout.node.CUR_SC := by
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA Sched.nodeW; rw [hc.cur]
  obtain ⟨q, hq, hqp⟩ := J.obj.sc _ y n hy
  have eq : q = L.cscW s := P1.eq_of_bv (by rw [hqp, hs.curSc, ecs])
  subst eq
  obtain ⟨y', n', hk', hx'⟩ := hs.scs _ hq
  have hk2 : σ.kheap σ.curSc = some (.schedContext y' n') := by rw [← hqp]; exact hk'
  have e : y' = y := by rw [hy] at hk2; cases hk2; rfl
  have hp0 : L.cscW s ≠ 0#u64 := J.c0 _ hq
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := (hJ.sc _ y' n' hp0 hk').2
  have d := (J.jcov.dead _ hD).2.2.2.2 _ hH
  have h0 : y'.scTcb = none := by rw [hx'.tcb, ← Sched.scTcbA_eq, d.1, Notif.optRef_zero]
  rw [e, hyt] at h0; cases h0

/-- `ScExtra` (the SC decodes' bundle), given the [global] platform facts and
no reschedule pending. -/
theorem scExtra (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread)
    (htm : Sched.TimeAgree arI)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmsg : Sched.MsgOK st Z.N Z.T Z.C Z.c) :
    Sched.ScExtra (L := L) arI Z s a σ :=
  ⟨J.nsc, J.inv, J.curInv hres, J.off, J.yld, J.act, J.mcp, J.c0, ⟨Lst, J.call, J.rfree⟩, J.rp, J.apart, J.ip, J.nk,
    htm, hmb, hmax, htu, hmsg⟩

/-- `RemoveOK` (`reply_remove`'s bundle) at `r` and its caller `t`, given the
reply's caller and the donation-back facts. -/
theorem removeOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : U64}
    (hrt : ∀ xr, σ.kheap r.bv = some (.reply xr) → xr.replyTcb = some t.bv)
    (hdr : ∀ xt, σ.kheap t.bv = some (.tcb xt) →
      (∀ sc ∈ Z.C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
        xt.tcbSchedContext = none → ∃ f, f ∈ Z.T ∧ y.scTcb = some f.bv ∧ f ≠ t) ∧
      (∀ sc ∈ Z.C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
        xt.tcbSchedContext = none → inClassR xt.tcbState xt.tcbFault → Fl4Spec.scActive y = true → released σ y)) :
    RemoveOK st Z.N Z.T Z.C Z.R Z.c s σ r t :=
  ⟨Lst, J.call, J.rp, J.nsc, J.inv, J.c0, J.obj.sc, hrt, hdr⟩

/-- `DonNCOK` (a donating send's bundle), given the sender's SC and the
receiver's release. -/
theorem donNCOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t d : U64} (hsc : L.mem s (P1.scA t) ≠ 0#u64)
    (hrel : ∀ y n, σ.kheap (L.mem s (P1.scA t)).bv = some (.schedContext y n) → ∀ x, σ.kheap d.bv = some (.tcb x) →
      inClassR x.tcbState x.tcbFault → Fl4Spec.scActive y = true → released σ y) :
    DonNCOK st Z.N Z.C s σ t d :=
  ⟨hsc, J.nsc, J.inv, hrel⟩

/-- `DonOK` (the wake donation's bundle), given the notification's SC among
the SCs and the thread out of its ready queue. -/
theorem donOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n : U64}
    (hn : L.mem s (nScA n) ≠ 0#u64 → L.mem s (nScA n) ∈ Z.C)
    (hq : L.mem s (P1.scA t) = 0#u64 → ∀ x, σ.kheap t.bv = some (.tcb x) →
      t.bv ∉ σ.readyQueues x.tcbDomain x.tcbPriority) :
    DonOK st Z.C s σ t n :=
  ⟨J.inv.relOK, hn, hq, J.inv.actReady⟩

/-- `PushDonOK` (a donating call's bundle), given the reply isolated and
detached and the callee's release. -/
theorem pushDonOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t d r : U64}
    (hiso : Sched.Isolated (L.mem s) Z.R r) (hdet : Sched.Detached Z.C Lst r)
    (hrel : ∀ y n x, σ.kheap (L.mem s (P1.scA t)).bv = some (.schedContext y n) → σ.kheap d.bv = some (.tcb x) →
      inClassR x.tcbState x.tcbFault → Fl4Spec.scActive y = true → released σ y) :
    PushDonOK st Z.N Z.T Z.C Z.R Z.c s σ t d r :=
  ⟨J.nsc, J.inv, J.rp, hiso, ⟨Lst, J.call, hdet, J.rfree⟩, hrel⟩

/-- `UtJoint` (the untyped decode's bundle) at an invoked CNode slot, no
reschedule pending (an invocation runs with `resume_cur_thread`: the current
SC live, `cscLive`). -/
theorem utJoint (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread) {slot : obj.Slot} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {pp : U64} {rs : Nat} {idx : List Bool}
    (hnode : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) (hslot : slot = cslotAddr (pp.bv, idx))
    (hcap : capAt (L.mem s) slot = ok cap)
    (hext : ∀ x ∈ extra.val, x ≠ 0#u64 → IsSlot Z.th x ∧ ∃ c a, capAt (L.mem s) x = ok c ∧ CapRel c a ∧ CapValid Z.th c) :
    Sched.UtJoint (L := L) arI H Cs s slot cap extra Z.th Z.G D σ pp rs idx := by
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hnode)⟩
  exact ⟨J.jcov, hSR, hV, hP, hM, hC, hI, J.ut, J.kern.orig, J.sfree, J.kern.cur, J.kern.curT, J.kern.act,
    hnode, hidx, hslot, hcap, hext,
    fun p sb fi dev e hd => J.utc _ p sb fi dev hAs (by rw [← hslot, hcap, e]) hd,
    J.kern.dwAl, J.kern.dwObj, J.kern.dwNe, J.kern.head, J.kern.gpm, J.kern.ga, J.kern.gf, J.kern.heap,
    J.kern.h0, J.kern.hks, J.kern.hksIn, J.kern.hnd, J.kern.ksbFit, J.kern.ksbAl, J.kern.nodeFit, J.kern.cpuCs,
    J.kern.curH, J.kern.cscH, J.cscLive.resolve_right hres, J.jpl⟩

/-- `UtP3Ok` (P1's `P3Ok` for the untyped retype), no reschedule pending. -/
theorem utP3Ok (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread) {slot : obj.Slot} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {pp : U64} {rs : Nat} {idx : List Bool}
    (hnode : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) (hslot : slot = cslotAddr (pp.bv, idx))
    (hcap : capAt (L.mem s) slot = ok cap)
    (hext : ∀ x ∈ extra.val, x ≠ 0#u64 → IsSlot Z.th x ∧ ∃ c a, capAt (L.mem s) x = ok c ∧ CapRel c a ∧ CapValid Z.th c) :
    Sched.UtP3Ok (L := L) arI H Cs s slot cap extra :=
  ⟨_, _, _, _, _, _, _, J.utJoint hres hnode hidx hslot hcap hext⟩

/-- Today's `JointInv` body at this state (P1's `BlkOK` with `JPlaced`,
`SpecCover`, `SpecFree`). -/
theorem joint (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∃ (H : P1.Heap) (Cs Ac Tr C : Set U64),
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s ∧ Sched.JPlaced (L := L) Z.th H Tr C s σ ∧ Sched.SpecCover H σ ∧
        Sched.SpecFree (L.mem s) Z.G σ := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨H, Cs, Ac, Tr, Cq, J.blk, hJ, J.cover, J.sfree⟩

/-- **P1's cap slots are cap-slot words** (`JPlaced.slotCapW`; P1's
`CdtHyps`/`XferHyps`/`DelPlace` slot fields). -/
theorem slotCapW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hTL : Sched.TLowSlots (P1.Heap.tcbs H)) :
    Sched.SlotCapW Z.th (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) :=
  by obtain ⟨_, _, hJ⟩ := J.jpl; exact hJ.slotCapW hTL

/-- **A slot's cap is typed in P1's sets** (`capTypedP1Hyp_of` at this state;
P1's `CdtHyps.slotcap`, `InvHyps.slotcap`, `P3Place`'s cap fields). -/
theorem capTyped (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hTL : Sched.TLowSlots (P1.Heap.tcbs H))
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hA : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) :
    ∃ X : P1Sets, P1Blk (st := st) X s ∧ Sched.SlotCapW Z.th X.T X.Ω X.Sg ∧ P1.CapTyped X.H X.Rp X.Nt c := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hty := hJ.typed _ hA.isSlot
  rw [capV_of_capAt hc] at hty
  exact ⟨⟨_, Cs, _, H, _, _, _, _, _, Ac⟩, J.blk, hJ.slotCapW hTL, hty⟩

/-- **`MpPlacedHyp`** (MakePool's placement) when no object is dead
(`JCovD` with `D = ∅` is `JCov`; with dead objects MakePool's region needs
`restrictTh`, to rework by its owner). -/
theorem mpPlaced (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hD : D = ∅) (hc : Z.c ∈ Cs)
    (hB : ∀ wp ∈ Z.B, Sched.Covered (L.mem s) Z.G wp.1.val (wp.1.val + 8)) :
    MpPlacedHyp st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s σ Z.G := by
  subst hD
  have hJC : Sched.JCov (L := L) Z.th H Z.G Cs s :=
    ⟨fun q k hq => (J.jcov.th q k hq).imp_right fun h => h.resolve_left (by simp),
      fun q k hq => (J.jcov.h q k hq).imp_right fun h => h.resolve_left (by simp), J.jcov.ks, J.jcov.idleOut⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨-, ⟨-, -, -, -, hI⟩, -⟩ := J.xtop.rel
  exact mpPlacedHyp_of hJC hJ J.ut hI hc J.zH.1 J.zH.2.1 J.zH.2.2.1 J.zH.2.2.2 J.c0 hB

/-- **A slot word is no TCB's VCPU word** (KENTRY-PLAN g2b; `SlotsApart`:
a TCB's own slots lie below its offset 256). -/
theorem inSlot_nv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : InSlot Z.th b) :
    ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  obtain ⟨x, hx, h1, h2⟩ := hb
  intro t ht e
  have h3 := (J.apart x hx).1 t ht
  rw [e, Sched.tVcpuA_val J.ip.e.tcb ht] at h1 h2
  omega

/-- **A step writing slot words only keeps the VCPU words.** -/
theorem vkeep_slot (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (InSlot Z.th)) : VKeep (L := L) Z.th s s' :=
  VKeep.of_writes J.ip.e.tcb J.thT hw fun _ hb => J.inSlot_nv hb

/-- **A kernel-state block word is no TCB's VCPU word** (P1's `ksOut`). -/
theorem ks_nv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (h1 : (L.ksb s).val ≤ b.val)
    (h2 : b.val < (L.ksb s).val + 13568) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  intro t ht e
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hv := Sched.tVcpuA_val J.ip.e.tcb ht
  rw [e] at h1 h2
  rcases hq.ksOut t (J.zH.1 t ht) with h | h <;> omega

theorem ksW_nv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : KsW (L.ksb s) b) :
    ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  obtain ⟨K, h1, h2, -, e, -⟩ := hb
  exact J.ks_nv (by omega) (by omega)

/-! ## The liveness bundle across a step (KENTRY-PLAN g2i) -/

/-- The spec's idle thread is the idle word at an `XTopAt` state. -/
theorem _root_.Fl4Proofs.P3.XTopAt.idleThread_bv {Z' : XSets} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z' s' a' σ') : σ'.idleThread = (L.idleW s').bv := by
  obtain ⟨Q, R, hc, hs⟩ := hX.fin.1.1.1.lists
  unfold P1.LawfulStore.idleW
  have h2 := hs.idleTh
  unfold Sched.nodeW at h2
  rw [hc.cur, ← h2]

/-- **`LiveJ` at another MDB tree of the same slots** (the trees' members are
the slots holding a non-null cap). -/
theorem _root_.Fl4Proofs.P3.LiveJ.regh {th : TypedHeap} {H : P1.Heap} {G G' : MdbGhost} {s : S}
    {σ : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hG : ∀ y ∈ G.chains.flatten, IsSlot th y)
    (hG' : ∀ y, IsSlot th y → capV (L.mem s) y ≠ .Null → y ∈ G'.chains.flatten) :
    LiveJ (L := L) th H G' s σ := by
  refine ⟨fun q i hqi hu => ?_, fun n hn hni => ?_, hL.zslots, hL.zdead⟩
  · rcases hL.slots q i hqi hu with ⟨y, hy, hr⟩ | hb
    · refine Or.inl ⟨y, hG' y (hG y hy) fun e => ?_, hr⟩
      rw [e] at hr; exact hr
    · exact Or.inr hb
  · obtain ⟨y, hy, hr⟩ := hL.dbg n hn hni
    exact ⟨y, hG' y (hG y hy) (by rw [hr]; intro e; cases e), hr⟩

/-- `ZTcb` across a step keeping the slots. -/
theorem _root_.Fl4Proofs.P3.ZTcb.of_same {th : TypedHeap} {s s' : S} (hSS : SlotsSame th (L.mem s) (L.mem s'))
    {p : U64} (hp : p ∈ ZTcb (L := L) th s') : p ∈ ZTcb (L := L) th s := by
  obtain ⟨y, hy, zt, n, hz, h65⟩ := hp
  exact ⟨y, hy, zt, n, by rw [← hSS.capV hy]; exact hz, h65⟩

/-- **`LiveDN` across a step keeping the slots** (KENTRY-PLAN g2i, the core of
the construction sites' frame, from the fields `JAtZ` and `JAtZR` share): the
slots (`SlotsSame`), the debug words (`DbgKeep`), the original bits and the
idle word kept, the dead set's objects dead after (the TCB zombies' TCBs among
them), the ghost tree `Z'.G` any tree of the sets after (`XTopAt`). -/
theorem _root_.Fl4Proofs.P3.liveDN_frame {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX0 : XTopAt (L := L) AR Z s a σ) (hL : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s) (hcs0 : 0#u64 ∈ Cs)
    (hTe : Z.T = P1.Heap.tcbs H)
    {Z' : XSets} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z' s' a' σ') (hth : Z'.th = Z.th) (hT : Z'.T = Z.T)
    (hc : Z'.c = Z.c) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hidl : L.idleW s' = L.idleW s) (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H s' p) :
    LiveDN (L := L) Z.th H Cs Z'.G s' σ' := by
  obtain ⟨hLJ, ⟨lst, hDW⟩, hN⟩ := hL
  have hmem : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((hX0.rel.2.1.2.2.1.members y).1 hy).1
  have hid : σ'.idleThread = σ.idleThread := by
    rw [XTopAt.idleThread_bv hX, XTopAt.idleThread_bv hX0, hidl]
  have hM' : MdbLinks Z.th (L.mem s') Z'.G := by rw [← hth]; exact hX.rel.2.1.2.2.1
  refine ⟨(hLJ.of_sameZ hSS hmem horig hid hK hcs0 hTz hdead).regh hmem
      fun y hy hne => (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hne⟩, ⟨lst, ?_⟩,
    hN.of_same (fun y hy => hSS.capV hy) horig⟩
  obtain ⟨Q0, R0, hc0, -⟩ := hX0.fin.1.1.1.lists
  obtain ⟨Q1, R1, hc1, -⟩ := hX.fin.1.1.1.lists
  refine hDW.of_keep hK fun y hy => ?_
  rw [hc1.aff y (by rw [hT, hTe]; exact hy), hc0.aff y (by rw [hTe]; exact hy), hc]

/-- **`LiveDN` across a step keeping the slots**, at `J` (`liveDN_frame`). -/
theorem liveX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Z' : XSets} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z' s' a' σ') (hth : Z'.th = Z.th) (hT : Z'.T = Z.T)
    (hc : Z'.c = Z.c) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hidl : L.idleW s' = L.idleW s) (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H s' p) :
    LiveDN (L := L) Z.th H Cs Z'.G s' σ' :=
  liveDN_frame J.xtop J.live ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩ J.kern.cs0
    (by obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩)
    hX hth hT hc hSS hK horig hidl hdead

/-- A TCB zombie's object is a TCB of the typed heap (`DelInv.zwf`). -/
theorem ztcb_tcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64}
    (hp : p ∈ ZTcb (L := L) Z.th s) : Z.th p = some .tcb := by
  obtain ⟨y, hy, zt, n, hz, h65⟩ := hp
  rcases J.del.zwf y hy p zt n hz with ⟨-, h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h65 h

/-- **An object named by a non-zombie cap of a slot is no TCB zombie's TCB**
(`FinInv.zombie_alone`). -/
theorem not_ztcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x)
    (hnz : ∀ p zt n, capV (L.mem s) x ≠ .Zombie p zt n) {p : U64}
    (hp : p.bv ∈ Fl4Spec.objRefs (absCap (capV (L.mem s) x))) : p ∉ ZTcb (L := L) Z.th s := by
  rintro ⟨y, hy, zt, n, hz, -⟩
  have hne : x ≠ y := fun e => hnz p zt n (by rw [e, hz])
  exact FinInv.zombie_alone J.xtop.rel.2.2.1 J.mdbL hy hz x hx hne hp

/-- **`JAtZ.zD` across a step keeping the slots**, the dead set grown. -/
theorem zDX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D' := fun p hp => hDD p (ZTcb.of_same hSS hp)

end JAtZ

end

end

end Fl4Proofs.P3
