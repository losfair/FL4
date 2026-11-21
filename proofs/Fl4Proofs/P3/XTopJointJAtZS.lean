/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch8 (2), lead decision option
(b)): **`JAtZS`, the joint invariant with a pending switch over a blocked
current thread**.

`JAtZS` is `JAtZ` (JointAt) with the field `cur` weakened by a third case
`SwBlk σ`: the action is `switchThread u` for some `u ≠ curThread` (l4v
`scheduler_act_sane`) and the current thread (not the idle thread) is not
runnable. It is what holds after NBSendRecv / NBSendWait whose send woke a
waiting receiver `u` (`possibleSwitchTo u` sets `switchThread u` from a
resumed action: Fl4Spec KHeap.lean:484) and whose receive then blocks the
current thread (`scheduleTcb` reschedules only from `resumeCurThread`,
KHeap.lean:500), where `JAtZ.cur` is false (KENTRY-PLAN sch8 (2)). JAtZ is
not edited.

* `JAtZ.toS`, `JAtZS.toJ` (given `JAtZ.cur`), `JAtZS.toJ_or` (a `JAtZS` state
  is a `JAtZ` state or `SwBlk`); `JAtS` (ghosts existential), `JAt.toS`.
-/
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- **A pending switch to another thread over a blocked current thread**
(module docstring). -/
def SwBlk (σ : Fl4Spec.State Unit) : Prop :=
  σ.curThread ≠ σ.idleThread ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = false) ∧
    ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ σ.curThread

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The joint invariant with `SwBlk` allowed** (module docstring). -/
structure JAtZS (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
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
  /-- `JAtZ.cur`, or a switch to another thread pending with the current
  thread not runnable (`SwBlk`, module docstring). -/
  cur : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ ∨ SwBlk σ
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
  /-- JAtZ's `ext` (`JExt`, G2). -/
  ext : JExt (L := L) Z.th s
  /-- [carried] As `JAtZ.live` (KENTRY-PLAN g2i). -/
  live : LiveDN (L := L) Z.th H Cs Z.G s σ
  /-- [carried] As `JAtZ.zD`. -/
  zD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D

/-- `JAtS`: `JAtZS` at a state (the ghosts existential). -/
def JAtS (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZS (L := L) arI AR Z H Cs Ac Lst D s a σ

variable {arI} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

theorem JAtZ.toS (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JAtZS (L := L) arI AR Z H Cs Ac Lst D s a σ where
  xtop := J.xtop
  call := J.call
  rfree := J.rfree
  rrecv := J.rrecv
  yld := J.yld
  mcp := J.mcp
  buf := J.buf
  ks := J.ks
  thT := J.thT
  thk := J.thk
  ip := J.ip
  rp := J.rp
  apart := J.apart
  nk := J.nk
  nodeB := J.nodeB
  jpl := J.jpl
  cover := J.cover
  obj := J.obj
  zH := J.zH
  sfree := J.sfree
  hset := J.hset
  hscC := J.hscC
  jcov := J.jcov
  kern := J.kern
  del := J.del
  ut := J.ut
  bound := J.bound
  finM := J.finM
  utc := J.utc
  nsc := J.nsc
  inv := J.inv
  cur := J.cur.imp_right Or.inl
  own := J.own
  off := J.off
  act := J.act
  c0 := J.c0
  bsa := J.bsa
  sv := J.sv
  isorted := J.isorted
  slink := J.slink
  curRun := J.curRun
  blk := J.blk
  intL := J.intL
  vsc := J.vsc
  bok := J.bok
  fcov := J.fcov
  fcap := J.fcap
  ext := J.ext
  live := J.live
  zD := J.zD

theorem JAtZS.toJ (J : JAtZS (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (h : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ) : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ where
  xtop := J.xtop
  call := J.call
  rfree := J.rfree
  rrecv := J.rrecv
  yld := J.yld
  mcp := J.mcp
  buf := J.buf
  ks := J.ks
  thT := J.thT
  thk := J.thk
  ip := J.ip
  rp := J.rp
  apart := J.apart
  nk := J.nk
  nodeB := J.nodeB
  jpl := J.jpl
  cover := J.cover
  obj := J.obj
  zH := J.zH
  sfree := J.sfree
  hset := J.hset
  hscC := J.hscC
  jcov := J.jcov
  kern := J.kern
  del := J.del
  ut := J.ut
  bound := J.bound
  finM := J.finM
  utc := J.utc
  nsc := J.nsc
  inv := J.inv
  cur := h
  own := J.own
  off := J.off
  act := J.act
  c0 := J.c0
  bsa := J.bsa
  sv := J.sv
  isorted := J.isorted
  slink := J.slink
  curRun := J.curRun
  blk := J.blk
  intL := J.intL
  vsc := J.vsc
  bok := J.bok
  fcov := J.fcov
  fcap := J.fcap
  ext := J.ext
  live := J.live
  zD := J.zD

/-- A `JAtZS` state is a `JAtZ` state, or `SwBlk` holds. -/
theorem JAtZS.toJ_or (J : JAtZS (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∨ SwBlk σ := by
  rcases J.cur with h | h | h
  · exact Or.inl (J.toJ (Or.inl h))
  · exact Or.inl (J.toJ (Or.inr h))
  · exact Or.inr h

theorem JAt.toS (h : JAt (L := L) arI AR s a σ) : JAtS (L := L) arI AR s a σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, J⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, J.toS⟩

/-- `JAtS` with the `JAtZ` case split off. -/
theorem JAtS.toJ_or (h : JAtS (L := L) arI AR s a σ) : JAt (L := L) arI AR s a σ ∨ SwBlk σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, J⟩ := h; J.toJ_or.imp (fun J => ⟨Z, H, Cs, Ac, Lst, D, J⟩) id

end

end

end Fl4Proofs.P3
