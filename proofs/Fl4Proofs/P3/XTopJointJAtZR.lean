/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch9 (1)): **`JAtZR`, the joint
invariant with `CurInv` asked only under a resumed scheduler action**.

`JAtZR` is `JAtZ` (JointAt) with the field `cur` weakened to `CurInvR σ`
(`schedulerAction = resumeCurThread → CurInv σ`). Both `JAtZ.cur`
(`chooseNewThread ∨ CurInv`) and `JAtZS.cur` (… `∨ SwBlk`, a pending switch)
imply it. It is what FL4's `schedule` needs before the scheduler action is
read: the spec's `schedule` reads `CurInv` of the old current thread only in
its resume branch (`newcur_of`); the switch and choose branches end at the idle
thread or a schedulable one (`newcur_of2F`). It is kept by the timers'
signals (a signal never sets `resumeCurThread`: `possibleSwitchTo` and
`rescheduleRequired` only move away from it), so the timer cone needs no
fact about a blocked current thread (KENTRY-PLAN sch9: with `SwBlk` it would,
since a timer signal may wake the current thread without changing a pending
switch). JAtZ and JAtZS are not edited.

* `CurInvR`, `JAtZR`, `JAtZ.toR`, `JAtZS.toR`, `JAtZR.toJ` (given `JAtZ.cur`).
* `JRestR`: `JRest` (XTopJointStep) with `cur : CurInvR`; `JRest.toR`.
-/
import Fl4Proofs.P3.XTopJointJAtZS
import Fl4Proofs.P3.XTopJointStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- **`CurInv` under a resumed action** (module docstring). -/
def CurInvR (σ : Fl4Spec.State Unit) : Prop :=
  σ.schedulerAction = .resumeCurThread → Sched.CurInv σ

theorem curInvR_of {σ : Fl4Spec.State Unit} (h : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ) :
    CurInvR σ := fun hr => h.resolve_left (by rw [hr]; intro e; cases e)

theorem curInvR_ofS {σ : Fl4Spec.State Unit} (h : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ ∨ SwBlk σ) :
    CurInvR σ := fun hr => by
  rcases h with h | h | ⟨-, -, u, hu, -⟩
  · rw [hr] at h; cases h
  · exact h
  · rw [hr] at hu; cases hu

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

structure JAtZR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
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
  /-- `CurInv` under a resumed action only (`CurInvR`, module docstring). -/
  cur : CurInvR σ
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

variable {arI} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

theorem JAtZ.toR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ where
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
  cur := curInvR_of J.cur
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

theorem JAtZS.toR (J : JAtZS (L := L) arI AR Z H Cs Ac Lst D s a σ) : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ where
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
  cur := curInvR_ofS J.cur
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

theorem JAtZR.toJ (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
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


/-- `JAtZ.liveX` at `JAtZR` (`liveDN_frame`). -/
theorem JAtZR.liveX (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {Z' : XSets} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z' s' a' σ') (hth : Z'.th = Z.th) (hT : Z'.T = Z.T)
    (hc : Z'.c = Z.c) (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hidl : L.idleW s' = L.idleW s) (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H s' p) :
    LiveDN (L := L) Z.th H Cs Z'.G s' σ' :=
  liveDN_frame J.xtop J.live ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩ J.kern.cs0
    (by obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩)
    hX hth hT hc hSS hK horig hidl hdead

/-- `JAtZ.zDX` at `JAtZR`. -/
theorem JAtZR.zDX (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D' := fun p hp => hDD p (ZTcb.of_same hSS hp)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

variable (arI) in
/-- `JRest` with `cur : CurInvR` (module docstring). -/
structure JRestR (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop where
  call : Sched.CallRel (L.mem s) Z.R Z.C σ Lst
  rfree : Sched.RFree (L.mem s) Z.R Z.C σ Lst
  rrecv : Sched.RRecv (L.mem s) Z.R σ
  yld : Sched.YieldRel Z.T Z.C (L.mem s) σ
  mcp : Sched.McpRel Z.T (L.mem s) σ
  buf : BufWordRel Z.T (L.mem s) σ
  rp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s σ
  apart : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s σ
  jpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s σ
  jcov : Sched.JCovD (L := L) Z.th H Z.G D Cs s
  kern : JKern (L := L) H Cs D Z.th s σ
  utc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := L) arI Z.th s σ Z.G sl p sb fi
  nsc : Sched.NSC Z.N Z.C σ
  inv : Sched.Inv σ
  cur : CurInvR σ
  own : Sched.CurOwnW Z.T Z.C σ
  off : Sched.OffOK σ
  act : Sched.ActIdle σ
  bsa : Sched.BlockedScActive σ
  isorted : Sched.IpcSorted σ
  curRun : CurRunM σ
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s

theorem JRest.toR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S}
    {σ : Fl4Spec.State Unit} (R : JRest (L := L) arI Z H Cs Ac Lst D s σ) : JRestR (L := L) arI Z H Cs Ac Lst D s σ where
  call := R.call
  rfree := R.rfree
  rrecv := R.rrecv
  yld := R.yld
  mcp := R.mcp
  buf := R.buf
  rp := R.rp
  apart := R.apart
  jpl := R.jpl
  jcov := R.jcov
  kern := R.kern
  utc := R.utc
  nsc := R.nsc
  inv := R.inv
  cur := curInvR_of R.cur
  own := R.own
  off := R.off
  act := R.act
  bsa := R.bsa
  isorted := R.isorted
  curRun := R.curRun
  blk := R.blk

end

end

end Fl4Proofs.P3
