/-
P3 (DESIGN.md §9), CSpace: **the deletion loop at `J`, by its steps**: the
loop run with a `JAtZ`-carrying invariant (`WJ`) and the readiness of the
slot to be emptied (`RdJ`, `EmptyReady`: the objects of the slot's cap dead
or covered by another cap), so that one cap's deletion at `J` (`JDelHyp`)
follows from premises about single steps of the loop (`DelHypsWR`, DelW),
some of them proved here.

* `WJ Z H Cs kb`: `JAtZ` at the sets `Z.mv G V` (the MDB ghost the loop's,
  the VSpace sets, the active SCs, the call stacks and the dead set chosen),
  P1's heap `H`, the cores `Cs` and the kernel-state base `kb` fixed, no
  switch pending (`NoSwitch`) and the spec-only invariants `SpecGlob`
  (SpecGlob: the IRQ node's slots null or notification caps, no cap but a
  frame naming an IRQ node CNode; kept by each step of the loop:
  `SpecGlob.fin`, `.empty`, `.setCap`, `.swap`, `.pp`, `.of_eq`);
  `EJ`: with `DelE`. `RdJ H`: `EmptyReady` (XTopJointEmpty).
* `WJR`: `WJ` and ScPPR's `PPR0` (what the loop's preemption points need of
  a zero consumed time), the loop's invariant; `EJ`: `WJR` with `DelE`.
* `JDelHyp`: one cap's deletion at `EJ` (`DelHypW`'s shape, the revoke's and
  the delete's premise); `JPreemptHyp`: the preemption point at `WJR`
  (proved, XTopJointPP's `jPreemptHyp_of`, from the platform's [P] facts).
* Proved steps: a notification cap's finalisation (`jFinAt_ntfn`: P3's
  `finNtfnJ`, P1's `fin_cap_ntfn.dead`, or `fin_idle` and another cap,
  `other_ntfn`); the readiness of the caps finalised without effect but
  zombies (`rdTrivJ`: the trivial caps cover nothing; a CNode cap's CNode is
  dead for `DeadP`, `cnode_ready`); the empty of a CNode slot
  (`emptyHypJ`: `emptyJR`, the untyped caps' facts after from the
  emptied slot's liveness readiness, `RdL`'s `ReadyLive`).
* The loop's readiness `RdL`: `RdJ` (`EmptyReady`) and `ReadyLive`
  (XTopJointLive: the other slots in use and the debug list's head live
  without the slot), asked only on the removable path (DelW's `RmOK`); at
  the loop's liveness invariant `WJL` (XTopJointWJL*: `delHypsJL`,
  `JDelHypL`, `delete_oneJL`), no longer here.
* Named premises [J] (`JDelParts`), each one step of the loop at `WJ`:
  (the final object caps' finalisation is proved for every kind,
  `finObjKind_covered`: no residual `JFinAtF` premise; a non-final one's is
  `jFin_nonfinal`: nothing, the slot ready by another cap alike it);
  `LiveJ` (XTopJointLive) is no premise here: carried by `WJL` from
  XTopJointEntry's `JEntryAt.live`.
* The frame and IO port caps' finalisation, final or not (`jFinAt_frio`,
  XTopJointFinFrIo): an unmapped frame's and an unowned IO port cap's do
  nothing; a VSpace-mapped frame's unmap by `jFrMap_of` (XTopJointFinVs's
  `JAtZ.finVsJb`, from `ArchRefines` [P], `JAtZ.vsc` and
  `jVsApartHyp`), the VT-x work (EPT-mapped frames, owned IO ports) by
  `jFrVt_of` (XTopJointFinVtJ's `JAtZ.frVtJ`, from `ARKeep` [P] and
  `JVtHyps` [J]); the slot ready after (a frame cap's memory holds no
  object of `H` but `other` ones: `JPlaced.cobj`, ScPlace's `CapObjH`; an
  IO port cap is not physical).
* A final VT-x object cap's finalisation (`jFinAt_vt`, XTopJointFinVtJ): an
  EPT cap but a mapped root's (`EptK`: nothing, or `ept::unmap` of a mapped
  non-root table's entry), a VCPU cap (`VcpuK`: `vcpu::finalise`, its unlink
  from the VCPU list); the spec keeps its state, FL4 writes VT-x words and the
  list's head word (`JAtZ.vtHJ`); the slot ready after (the object apart from
  `H`'s); from `ArchRefines` [P], `ARKeep` [P] and `JVtHyps` [J].
* A final mapped EPT root cap's finalisation (`jFinAt_eptRoot`, `EptRootK`):
  FL4's `delete_asid` of the root clears its guest-tagged ASID pool entry,
  as the spec's `arch_finalise_cap` of a mapped level-0 `EPTCap` does
  (`deleteAsid`); XTopJointFinVs's `JAtZ.finVsJb` (VsFin's `fin_ept_root`),
  the slot ready after (the EPT root apart from `H`'s objects,
  `JAtZ.ept_obj`); from `ArchRefines` [P], `JAtZ.vsc`, `jVsApartHyp`
  and `JVtHyps` [J] (the root non-null: `JAtZ.ept_ne0`).
* `JIrqSlotHyp` (the IRQ node's slots null or notification caps; proved,
  `jIrqSlotHyp`, from the spec's carried by `WJ`), for a final IRQ handler
  cap's finalisation at `WJL` (XTopJointWJLFinT's `jFinAtL_irq`).
* A final endpoint cap's finalisation (`jFinAt_ep`): XTopJointFinEp's
  `JAtZ.finEpJ` (`cancel_all_ipc`, `JAtZ` after), the endpoint dead after
  (P1's `fin_cap_ep.dead`, `JAtZ.ep_ready`); the replies it frees, of
  threads blocked receiving, are detached and unlinked by ScSignalBoundJ's
  `recvReplyHyp_holds` (`JAtZ.rrecv`, l4v `valid_replies`).
* A final reply cap's finalisation (`jFinAt_reply`): XTopJointFinReply's
  `JAtZ.finReplyJ` (none, or the receiver's `cancel_ipc`, proved; the
  `reply_remove` of a thread blocked on the reply, `jReplyRemoveHyp`:
  XTopJointRemove's `JAtZ.replyRemoveJ`),
  the reply dead after (P1's `fin_cap_reply.dead`, `JAtZ.reply_ready`); with
  `P0.ArchTotal` [P].
* A final native VSpace cap's finalisation (`jFinAt_vs`: page table, page
  directory, PDPT, PML4, ASID pool caps): XTopJointFinVs's `JAtZ.finVsJ`
  (`JAtZ` after at the same sets, the spec's frame `ArFr`), the slot ready
  (`JAtZ.vs_ready`: no object of `H` but `other` ones in the cap's frame);
  from `ArchRefines` [P] and `JAtZ.vsc` (l4v `valid_cap`; a table cap's
  readiness from `JPlaced.cobj`, mapped or not),
  `JDelParts` fields (`JVsApartHyp` by `jVsApartHyp`).
* A final SC cap's finalisation (`jFinAt_sc`): XTopJointFinSc's
  `JScFinHyp` (the finalisation at `J`, by `jScFin_of` from the proved SC
  steps and `jYieldToHyp_of` from the thread's [P] `ticks`), the SC dead after
  (P1's `fin_cap_sc.dead`, `JAtZ.sc_ready`); the cap's SC the spec's of its
  size, not the idle SC, by `JAtZ.scCap` (`jScCapHyp_of`). The SC
  may be the current SC (XTopJointFinSc's docstring).
* A final thread cap's finalisation (`jFinAt_thread`): XTopJointFinThread's
  `JAtZ.finThreadJ` (the notification unbind, timer removal, `unbind_tcb`,
  `complete_yield_to`, `suspend` (its `cancel_ipc`: send, notification and
  reply proved, receive by `recvReplyHyp_holds`), and
  debug-list removal proved; the narrow facts from `JThreadFinHyps` [J]/[P]), the slots by P1's
  `fin_cap_thread.slots`, the thread dead after (P1's `fin_cap_thread.dead`,
  `JAtZ.tcb_ready`).
* A zombie written over a cap alike it (`jZombieHyp`, XTopJointZombie's
  `JAtZ.zombieJCore`); a zombie swapped with its first slot (`jSwapHyp`,
  `JAtZ.swapJCore`, the zombie's first slot off the childless untyped
  regions by `ut_free`); a zombie's slot ready (`jRdTrivHyp_of`,
  `JAtZ.zombie_ready`: a CNode zombie's CNode dead for `DeadP`, a TCB
  zombie's TCB by `JZombieTcbHyp`).
* The empty of a ready slot (`emptyHypJ`): a CNode slot by `emptyJR`, a TCB
  slot by `emptyJRT` (a step changing the TCB's caps only, `KeepCT`), both
  with `RdL`'s `ReadyLive` for the untyped caps' facts after.
* `JPreemptHyp` from the platform (XTopJointPP's `jPreemptHyp_of`),
  `JPostDelHyp` from the kernel-state layout (XTopJointPost's
  `jPostDelHyp_of`); `PPR0` kept by the slot edits
  (`PPK.of_cnK`) and by the finalisations (`jFinPPHyp`: SpecPPR's
  `ppr0_finaliseCap`, the spec's `finalise_cap` keeps it from `Inv`).
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.XTopJointEmptyUt
import Fl4Proofs.P3.XTopJointFinEp
import Fl4Proofs.P3.XTopJointFinReply
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P3.XTopJointFinFrIo
import Fl4Proofs.P3.XTopJointFinVtJ
import Fl4Proofs.P3.XTopJointFinSc
import Fl4Proofs.P3.XTopJointFinThread
import Fl4Proofs.P3.XTopJointRemove
import Fl4Proofs.P3.IntInv
import Fl4Proofs.P3.XTopJointZombie
import Fl4Proofs.P3.XTopJointLive
import Fl4Proofs.P3.ScPPR
import Fl4Proofs.P3.SpecPPR
import Fl4Proofs.P3.SpecPPRC
import Fl4Proofs.P3.SpecPPRQ
import Fl4Proofs.P3.SpecGlob
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletion's invariant at `J`** (module docstring). -/
def WJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ ∧ L.ksb s = kb ∧ Vs.NoSwitch σ ∧ SpecGlob σ

/-- `WJ` and `PPR0` (the deletion loop's invariant at `J`, XTopJointPP). -/
def WJR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ ∧ L.ksb s = kb ∧ Vs.NoSwitch σ ∧ SpecGlob σ ∧ PPR0 σ

theorem WJR.wj {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (h : WJR (L := L) arI AR Z H Cs kb s a σ G) :
    WJ (L := L) arI AR Z H Cs kb s a σ G :=
  let ⟨V, Ac, Lst, D, J, hk, hn, hg, _⟩ := h; ⟨V, Ac, Lst, D, J, hk, hn, hg⟩

theorem WJ.wjr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (h : WJ (L := L) arI AR Z H Cs kb s a σ G) (hp : PPR0 σ) :
    WJR (L := L) arI AR Z H Cs kb s a σ G :=
  let ⟨V, Ac, Lst, D, J, hk, hn, hg⟩ := h; ⟨V, Ac, Lst, D, J, hk, hn, hg, hp⟩

theorem WJR.pp {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {kb : U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {G : MdbGhost} (h : WJR (L := L) arI AR Z H Cs kb s a σ G) : PPR0 σ :=
  let ⟨_, _, _, _, _, _, _, _, hp⟩ := h; hp

/-- `WJR` with `DelE` (the CSpace deletion's invariant and fuel bound). -/
abbrev EJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJR (L := L) arI AR Z H Cs kb s a σ G

/-- **The deletion's state after a preemption at `J`**: the post of a
preempting preemption point from `WJR` (FL4's `preemption_point` returning
`Preempted`, a preempting outcome of the spec's). Not `WJ` itself: the
preemption point updates the time, and the current SC's budget may then be
exhausted (`JAtZ`'s `OffOK` false), which the caller's
`mcs_preemption_point` charges before `schedule`. -/
def WJP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit), WJR (L := L) arI AR Z H Cs kb s0 a0 σ0 G ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1 ∧
    DomRel (L.mem s) (L.ksb s) σ ∧ MdbOKV (L.ksb s) (L.mem s) G

/-- `WJP` with `DelE`. -/
abbrev EJP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJP (L := L) arI AR Z H Cs kb s a σ G

/-- **The readiness at `J`** of a slot to be emptied: `EmptyReady`. -/
abbrev RdJ (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s _ _ G x => EmptyReady (L := L) H G s x

/-- **The deletion loop's readiness at `J`**: `RdJ` and the liveness
readiness `ReadyLive` (XTopJointLive: the other slots in use and the debug
list's head live without the slot). -/
abbrev RdL (th : TypedHeap) (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s _ σ G x => EmptyReady (L := L) H G s x ∧ ReadyLive (L := L) th s σ G x

/-- **One cap's deletion at `J`**: FL4's exposed `delete` of an MDB slot from
`EJ` (a `JAtZ` state at the sets `Z.mv G V`), a spec outcome of `cap_delete`
of the same kind, the CSpace relation, `EJ` after (`EJP` after a
preemption) and the ghost step (`DelHypW`). At `WJL` it is XTopJointWJLDel's
`JDelHypL` (from `JDelParts.jDelHypL`). -/
def JDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat), Z.th = th →
    (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) → 6 ≤ K →
    DelHypW (L := L) arI psiD th (EJ (L := L) arI AR Z H Cs kb K) (EJP (L := L) arI AR Z H Cs kb K)

/-- **The preemption point at `J`**: from `WJR` (a `JAtZ` state with
`PPR0`), the cap slots kept, a spec outcome of the same kind, the CSpace
relation and `WJR` after at the same MDB ghost, `WJP` after a preemption
(`PPHypDW`). FL4's preemption point runs `update_timestamp` (the SC and
time fields). Proved from the platform's [P] facts (XTopJointPP's
`jPreemptHyp_of`). -/
def JPreemptHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    PPHypDW (L := L) arI (WJR (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) th

/-- **A cap's finalisation keeps `PPR0`**: from a `JAtZ` state, every
outcome of the spec's `finalise_cap` of a cap in a slot keeps `PPR0`
(ScPPR: at a zero consumed time, the current SC's head ready when active,
its threads outside the release queue). Proved (`jFinPPHyp`, SpecPPR's
`ppr0_finaliseCap`, from `Inv`): `finalise_cap` keeps the time, the consumed
time and the current SC, changes the current SC's refills only by
`sched_context_set_inactive` (the SC then inactive), never enqueues a thread
for release, and binds a thread to the current SC only by `reply_remove`'s
donation to a caller blocked on the reply, hence outside the release queue
(`Inv.rel`: its members are runnable). -/
def JFinPPHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap), AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
      FinObjKind c → ∀ (x : Fl4Spec.Cap × Fl4Spec.Cap) (σ' : Fl4Spec.State Unit),
      (x, σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 →
      PPR0 σ → PPR0 σ'

/-- The endpoints' queue facts of a `JAtZ` state (SpecPPRC's `EpQB`). -/
theorem JAtZ.epQB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : PPS.EpQB σ := by
  intro e x hk
  obtain ⟨e', he', rfl⟩ := J.obj.ep _ x hk
  exact ⟨J.epFinPre.2.2.1 e' he', fun u hu => ep_queue_blocked J.ip (J.xtop.irelK J.ks J.buf) he' hk hu⟩

theorem jFinPPHyp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} : JFinPPHyp (L := L) arI AR th :=
  fun _ _ _ _ _ _ _ _ σ _ J _ _ _ _ _ x σ' hx hP => PPS.ppr0_finaliseCap (x := (x, σ')) J.inv hx hP
    ((Vs.dk_finaliseCap _ _).ct hx) ((Vs.gk_finaliseCap _ _).idle hx) (fun hn => Vs.ak_finaliseCap_ns hx hn)
    (PPS.chg_finaliseCap (x := (x, σ')) J.inv J.bsa J.sv J.epQB hP.1.2.2.2.1 hx)
    (PPNQ.ctnq_finaliseCap (x := (x, σ')) J.inv J.sv J.epQB hP hx)

/-! ## The named steps -/

/-- A notification cap. -/
def NtfnK (c : capability.Cap) : Prop := ∃ p b w r, c = .Notification p b w r

/-- **Hypothesis: the finalisation at `J` of the object caps of the kinds
`Kd`** [J]: `FinObjHypWR` at `WJ` with `RdJ` after, for those kinds (the
notification caps proved, `jFinAt_ntfn`). -/
def JFinAt (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th Kd

/-- **Hypothesis: a final cap's finalisation at `J`, for the object caps of
the kinds `Kd`** [J]: `JFinAt` for final caps only (a non-final cap's,
`jFin_nonfinal`, is proved for every object cap but frames and IO port caps). -/
def JFinAtF (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → WJ (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
    capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c → Kd c → Fl4Spec.isFinalCap' (absCap c) σ →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄

/-- A frame cap or an IO port cap (finalised with work when not final). -/
def FrIoK (c : capability.Cap) : Prop := isFrame c = true ∨ ∃ f l o, c = .IoPort f l o

/-- **A VSpace-mapped frame cap's finalisation at `J`** (`FrMapK`, final or
not: FL4's `vspace::unmap_page`, the spec's `unmap_page`), `WJ` after (the
readiness from `JPlaced.cobj`); proved, `jFrMap_of`. -/
def JFrMapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (fun _ _ _ _ _ => True) th FrMapK

/-- **The VT-x work of a finalisation at `J`** (`FrVtK`: an
EPT-mapped frame cap's `ept::unmap`, an owned IO port cap's
`vcpu::revoke_ports`; outside the semantic scope, DESIGN §5, as `XFinHyps.vm`
and `XFinHyps.io` at `XTop`), `WJ` after. Proved: `jFrVt_of`. -/
def JFrVtHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (fun _ _ _ _ _ => True) th FrVtK

/-- **A zombie's slot is ready at `J`** (`RdTrivHyp` for zombies; their
finalisation leaves the state as it is): the objects in the zombie's range
(its CNode, or its TCB) dead. Proved from `JZombieTcbHyp`
(`jRdTrivHyp_of`, XTopJointZombie's `JAtZ.zombie_ready`): a CNode zombie's
CNode is dead for `DeadP` (`H`'s `other`). -/
def JRdTrivHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p zt n : U64),
      DState (L := L) th s σ G → WJ (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.Zombie p zt n) →
      RdJ (L := L) (A := A) H s a σ G (cslotAddr sl)

/-- **A zombie written over a cap alike it keeps `WJ`** (`ZombieHypW` at
`WJ`). Proved, `jZombieHyp` (XTopJointZombie's `JAtZ.zombieJCore`, by
`jowes_slotD`: the written slot was linked before, so no `DestLive` is
read; the zombie covers what the cap it replaces covered). -/
def JZombieHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ZombieHypW (L := L) (A := A) (WJ (L := L) arI AR Z H Cs kb) th

/-- **Hypothesis: a TCB zombie's TCB is dead at `J`** [J]: at `WJ`, the TCB
of a zombie of type 65 in a slot is `DeadP` (inactive, no SC, no bound
notification, neither the scheduler action nor idle). The thread cap's
finalisation leaves it so (P1's `fin_cap_thread.dead`, `jFinAt_thread`), and
nothing names the TCB after, but `JAtZ` has no field on zombies' objects
(a zombie outlives a preempted deletion, so the fact must hold at every
kernel entry: an invariant beside `JAtZ`, kept by every kernel step). l4v:
`rec_del` relies on the zombie's TCB not being `live` (its `finalise_cap`
post for a thread cap; `if_live_then_nonz_cap` with the zombie the only
cap). The narrowing of `JRdTrivHyp`: a CNode zombie's slot is ready from
`JAtZ` alone. -/
def JZombieTcbHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), WJ (L := L) arI AR Z H Cs kb s a σ G →
      ∀ x, IsSlot th x → ∀ p zt n, capV (L.mem s) x = .Zombie p zt n → zt.val = 65 → DeadP (L := L) H s p

/-- **A zombie swapped with its first slot keeps `WJ`** (`SwapHypW` at
`WJ`). Proved (`jSwapHyp`, XTopJointZombie's
`JAtZ.swapJCore`, by `jowes_slotD`: no `DestLive` is read; the TCBs' slot 3
holds no zombie, `JPlaced.fh`, and is no object's first slot). -/
def JSwapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    SwapHypW (L := L) (A := A) (WJ (L := L) arI AR Z H Cs kb) th

/-- **A cleanup cap's `post_cap_deletion` keeps `WJR`** (`PostDelHypW` at
`WJR`; proved, XTopJointPost's `jPostDelHyp_of`). -/
def JPostDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    PostDelHypW (L := L) arI (WJR (L := L) arI AR Z H Cs kb) th

/-- **The spec's idle thread is the current core's `IDLE_THREAD` word**
(`SchedSpec.idleTh`). -/
theorem JAtZ.idleThread_eq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : σ.idleThread = (L.idleW s).bv := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  unfold P1.LawfulStore.idleW
  have h2 := hs.idleTh
  unfold nodeW at h2
  rw [hc.cur, ← h2]

/-- An IRQ handler cap. -/
def IrqK (c : capability.Cap) : Prop := ∃ i, c = .IrqHandler i

/-- **The IRQ node's slots hold null or notification caps at `J`** (as
XTopFinIrq's `IrqSlotOK` premise). Proved: `jIrqSlotHyp` (the spec's, carried
by `WJ`: `SpecGlob`). -/
def JIrqSlotHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), WJ (L := L) arI AR Z H Cs kb s a σ G →
      ∀ i : U64, i.val < 128 → IrqSlotOK (L.mem s) (nodeA (L.ksb s) i)

/-- **`JIrqSlotHyp` holds**: `irqSlotOK_of_spec` at `JAtZ`'s interrupt
layout `intL`, the CSpace relation and the IRQ relation, from the spec's
IRQ node slots (`WJ`'s `SpecGlob`, `SpecGlob.irqNode`: l4v
`valid_irq_node`, carried by the deletion loop, SpecGlob). -/
theorem jIrqSlotHyp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} : JIrqSlotHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G hW i hi
  obtain ⟨V, Ac, Lst, D, J, -, -, hsg⟩ := hW
  exact irqSlotOK_of_spec J.intL J.xtop.rel.2.1.1 J.xtop.fin.1.1.2.2.2.1 hsg.irqNode hi

/-- An endpoint cap. -/
def EpK (c : capability.Cap) : Prop := ∃ e b x1 x2 x3 x4, c = .Endpoint e b x1 x2 x3 x4

/-- A reply cap. -/
def RpK (c : capability.Cap) : Prop := ∃ p g, c = .Reply p g

/-- A native VSpace cap finalised with work when final: a page table, page
directory, PDPT, PML4 or ASID pool cap. -/
def VsK (c : capability.Cap) : Prop :=
  (∃ p m a v, c = .PageTable p m a v) ∨ (∃ p m a v, c = .PageDirectory p m a v) ∨
    (∃ p m a v, c = .Pdpt p m a v) ∨ (∃ p m a, c = .Pml4 p m a) ∨ ∃ p b, c = .AsidPool p b
/-- A mapped EPT root cap (its finalisation releases its ASID). -/
def EptRootK (c : capability.Cap) : Prop := ∃ p asid va, c = .Ept p 0#u64 true asid va
/-- A scheduling-context cap. -/
def ScK (c : capability.Cap) : Prop := ∃ p sb, c = .SchedContext p sb
/-- A thread (TCB) cap. -/
def TcbK (c : capability.Cap) : Prop := ∃ t, c = .Thread t

/-- **`reply_remove` at `J`** (the reply cap's finalisation of a thread
blocked on the reply): from `JAtZ`, FL4's `reply_remove` against the spec's
(deterministic), `JAtZ` after at fresh VSpace sets, the slots and the
kernel-state base kept. Proved: `jReplyRemoveHyp` (XTopJointRemove's
`JAtZ.replyRemoveJ`). -/
def JReplyRemoveHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (r t : U64) (x : Fl4Spec.Tcb), r ∈ Z.R → t ∈ Z.T → σ.kheap t.bv = some (.tcb x) →
      x.tcbState = .blockedOnReply r.bv → ipc.reply_remove st arI s a r t ⦃ res => res.2 = a ∧
        ∃ σ' V' Ac' Lst' D', Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' res.1 res.2 σ' ∧
          SlotsSame Z.th (L.mem s) (L.mem res.1) ∧ L.ksb res.1 = L.ksb s ⦄

/-- **`reply_remove` at `J`** (XTopJointRemove's `JAtZ.replyRemoveJ`). -/
theorem jReplyRemoveHyp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hT : P0.ArchTotal arI) :
    JReplyRemoveHyp (L := L) arI AR th :=
  fun _ _ _ _ _ _ _ _ _ _ J _ _ _ hr ht hk hst => J.replyRemoveJ hT hr ht hk hst

/-- `JThreadFinHyps` but `utTcb` (the latter from `LiveJ` at `WJL`:
XTopJointFinThreadU). -/
structure JThreadFinHypsU (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [scope] XTopJointFinThread's `JThreadFinHyps.obj` (a native thread's VCPU word zero). -/
  obj : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ →
    ∀ (x p : U64), IsSlot Z.th x → capV (L.mem s) x = .Thread p →
      L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64
  /-- [P] XTopJointFinThread's `JThreadFinHyps.ticks`. -/
  ticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
    ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄

/-- **The named steps of the deletion at `J`** (module docstring). -/
structure JDelParts (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- The x86 backend's obligations (VsArch's `ArchRefines` [P]), for a final
  native VSpace cap's finalisation. -/
  archRef : ArchRefines arI AR
  /-- The x86 backend's VCPU barrier keeps the arch relation (`ARKeep` [P]),
  for the VT-x finalisations (`jFrVt_of`, `jFinAt_vt`). -/
  arKeep : ARKeep arI AR
  /-- XTopJointFinVtJ's `JVtHyps` [J] (the VCPU list's and the EPT walks'
  placement, the EPT-mapped frames' ASIDs, the VT-x objects apart from
  `H`'s). -/
  vt : JVtHyps (L := L) arI AR th
  /-- The steps of a final thread cap's finalisation at `J` not proved
  (XTopJointFinThread's `JThreadFinHyps` but `utTcb`, which `LiveJ` at `WJL`
  gives: XTopJointFinThreadU). -/
  thr : JThreadFinHypsU (L := L) arI AR th

/-! ## The proved steps -/

variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

/-- **A notification cap's finalisation at `J`, every slot kept** (module
docstring): `jFinAt_ntfn`'s post with the cleanup null and every slot's cap
as it was (for XTopJointWJLFinT's `delete_oneJL`). -/
theorem jFinNtfnK [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool)
    (hDS : DState (L := L) th s σ G) (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r)) :
    objects.finalise_cap st arI s a (.Notification p b w r)
        (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) false ⦃ res =>
      res.1.1 = finRem (.Notification p b w r) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) ∧
      res.1.2 = .Null ∧ ∃ σ' G', ((absCap res.1.1, absCap res.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit)
          (absCap (.Notification p b w r)) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) σ).1 ∧
        DState (L := L) th res.2.1 σ' G' ∧ (∀ y, IsSlot th y → capV (L.mem res.2.1) y = capV (L.mem s) y) ∧
        MdbStep (L.mem s) G (L.mem res.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb res.2.1 res.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H res.2.1 res.2.2 σ' G' (cslotAddr sl) ⦄ := by
  subst hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have hP := J.xtop.rel.1
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b w r hcv).2
  have hpN : p ∈ (Z.mv G V).N := J.hset.2.1 p hHp
  by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ
  · rw [decide_eq_true hfin]
    refine WP.spec_mono (WP.spec_and (J.finNtfnJ hpN)
      (P1.fin_cap_ntfn.dead (ar := arI) s a p b w r false J.blk hHp hHp)) ?_
    rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, hmem1, J1, -, -, hSS1, hks1⟩, d1, d2, d3⟩
    simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 d2 d3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    subst e2
    have hdp : DeadP (L := L) H s1 p :=
      ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ => ⟨d1, d2, d3⟩,
        fun h => (by rw [hHp] at h; cases h), fun z h => (by rw [hHp] at h; cases h)⟩
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Notification p b w r := by
      rw [hSS1.capV hA.isSlot, hcv]
    refine ⟨rfl, rfl, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩,
      fun y hy => hSS1.capV hy, (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
      ⟨V1, Ac, Lst, D, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg⟩, J1.ntfn_ready hA.isSlot hcv1 (Or.inl hdp)⟩
  · rw [decide_eq_false hfin]
    obtain ⟨cl, he, hmem, -, -, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ (.Notification p b w r) trivial
      false (fun hw => by have := finWork_ntfn hw; cases this)
    have hcl0 : cl = .Null := hnio (fun f l e => by cases e)
    subst hcl0
    rw [he, WP.spec_ok]
    exact ⟨rfl, rfl, σ, G, hmem, hDS, fun y _ => rfl, MdbStep.refl hDS.1.2.2.1,
      ⟨V, Ac, Lst, D, J, hkb, ak_finaliseCap_ns hmem hns, SpecGlob.fin hmem hsg⟩, J.ntfn_ready hA.isSlot hcv (Or.inr (other_ntfn hP hDS hA hcv hfin))⟩

/-- **A notification cap's finalisation at `J`** (module docstring). -/
theorem jFinAt_ntfn [Fl4Proofs.P1.PlainStore st] : JFinAt (L := L) arI AR th NtfnK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hn
  obtain ⟨p, b, w, r, rfl⟩ := hn
  refine WP.spec_mono (jFinNtfnK arI Z H Cs kb hth s a σ G sl p b w r hDS hW hA hc) ?_
  rintro res ⟨h1, h2, σ', G', h4, h5, h6, h7, h8, h9⟩
  refine ⟨h1, by rw [h2]; trivial, by rw [h2]; trivial, σ', G', h4, h5, by rw [h6 _ hA.isSlot, capV_of_capAt hc],
    fun y hy _ => Or.inl (h6 y hy), h7, h8, h9⟩

/-- **An endpoint cap's slot is ready once the endpoint is dead** (as
XTopJointEmpty's `JAtZ.ntfn_ready`). -/
theorem JAtZ.ep_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) {p b : U64}
    {x1 x2 x3 x4 : Bool} (hcv : capV (L.mem s) x = .Endpoint p b x1 x2 x3 x4) (hd : DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ep := (hJ.typed _ hx).1 p b x1 x2 x3 x4 hcv
  have hpfit : p.val + 2 ^ 4 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  obtain ⟨e1, e2⟩ := range_ep p b x1 x2 x3 x4 hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ 4 ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p .ep hq hHp hne
    simpa only [show (P1.HKind.ep).bits = 4 from rfl] using this
  refine fun lo hi hlh h1 h2 => ?_
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **A final endpoint cap's finalisation at `J`** (XTopJointFinEp's
`JAtZ.finEpJ`, the endpoint dead after by P1's `fin_cap_ep.dead`), from
`RecvReplyHyp` (`recvReplyHyp_holds`). -/
theorem jFinAt_ep :
    JFinAtF (L := L) arI AR th EpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨e, b, x1, x2, x3, x4, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHe : H e = some .ep := (hJ.typed _ hA.isSlot).1 e b x1 x2 x3 x4 hcv
  have heE : e ∈ (Z.mv G V).E := J.hset.1 e hHe
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (J.finEpJ heE)
    (P1.fin_cap_ep.dead (ar := arI) s a e b x1 x2 x3 x4 false J.blk hHe)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, hmem1, J1, -, hSS1, hks1⟩, d1⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 e :=
    ⟨fun h => (by rw [hHe] at h; cases h), fun _ => d1, fun h => (by rw [hHe] at h; cases h),
      fun h => (by rw [hHe] at h; cases h), fun z h => (by rw [hHe] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Endpoint e b x1 x2 x3 x4 := by
    rw [hSS1.capV hA.isSlot, hcv]
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac, Lst, D, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg⟩, JAtZ.ep_ready arI J1 hA.isSlot hcv1 hdp⟩

/-- **A reply cap's slot is ready once the reply is dead** (as
`JAtZ.ep_ready`). -/
theorem JAtZ.reply_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) {p : U64} {g : Bool}
    (hcv : capV (L.mem s) x = .Reply p g) (hd : DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hx).2.2 p g hcv
  have hpfit : p.val + 2 ^ 5 ≤ 2 ^ 64 := J.kern.heap.fits p _ hHp
  obtain ⟨e1, e2⟩ := range_reply p g hpfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q k, H q = some k → q ≠ p → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ 5 ≤ q.val := by
    intro q k hq hne
    have := J.kern.heap.disj q k p .reply hq hHp hne
    simpa only [show (P1.HKind.reply).bits = 5 from rfl] using this
  refine fun lo hi hlh h1 h2 => ?_
  · right
    intro q hq
    by_cases e : q = p
    · subst e; exact hd
    · cases hk : H q with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q k hk e with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- **A final reply cap's finalisation at `J`** (XTopJointFinReply's
`JAtZ.finReplyJ`, the reply dead after by P1's `fin_cap_reply.dead`), from
`RecvReplyHyp` (`recvReplyHyp_holds`) and `JReplyRemoveHyp` [J]. -/
theorem jFinAt_reply [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI)
    (hRm : JReplyRemoveHyp (L := L) arI AR th) : JFinAtF (L := L) arI AR th RpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, g, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hA.isSlot).2.2 p g hcv
  have hpR : p ∈ (Z.mv G V).R := J.hset.2.2 p hHp
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (J.finReplyJ hT (hRm (Z.mv G V) H Cs Ac Lst D s a σ rfl J) hpR)
    (P1.fin_cap_reply.dead (ar := arI) hT s a p g false J.blk hHp)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, Ac1, Lst1, D1, hmem1, J1, hSS1, hks1⟩, d1⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun _ => d1, fun z h => (by rw [hHp] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Reply p g := by
    rw [hSS1.capV hA.isSlot, hcv]
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac1, Lst1, D1, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg⟩, JAtZ.reply_ready arI J1 hA.isSlot hcv1 hdp⟩

set_option maxHeartbeats 4000000 in
/-- **A final native VSpace cap's finalisation at `J`** (XTopJointFinVs's
`JAtZ.finVsJ`; the slot ready, `JAtZ.vs_ready`), from `ArchRefines` [P],
`JAtZ.vsc` (`JVsApartHyp` holds: `jVsApartHyp`). -/
theorem jFinAt_vs [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR)
    (hAp : JVsApartHyp (L := L) arI AR th) : JFinAtF (L := L) arI AR th VsK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hv hfin
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth
  have hcv := capV_of_capAt hc
  have hxm : cslotAddr sl ∈ G.chains.flatten := (hDS.1.2.2.1.members _).2 ⟨hA.isSlot, _, hc, fun h => by
    subst h
    rcases hv with ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> cases e⟩
  rw [decide_eq_true hfin]
  refine WP.spec_mono (J.finVsJ hAR Ap hDS hA hc hv) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ1, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac, Lst, D, J1, hks.trans hkb, ak_finaliseCap_ns hm hns, SpecGlob.fin hm hsg⟩, J.vs_ready hxm hcv hv hcv1⟩

set_option maxHeartbeats 4000000 in
/-- **A VSpace-mapped frame cap's finalisation at `J`** (XTopJointFinVs's
`JAtZ.finVsJb`, final or not), from `ArchRefines` [P], `JAtZ.vsc` and
`jVsApartHyp`. -/
theorem jFrMap_of [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR)
    (hAp : JVsApartHyp (L := L) arI AR th) : JFrMapHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, sz, r, d, asid, va, hce⟩
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth hce
  have hcv := capV_of_capAt hc
  refine WP.spec_mono (J.finVsJb hAR Ap hDS hA hc rfl ⟨_, rfl⟩ _
    (Or.inr ⟨p, sz, r, d, false, asid, va, rfl⟩)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Frame p sz r d true false asid va := by
    rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ1, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac, Lst, D, J1, hks.trans hkb, ak_finaliseCap_ns hm hns, SpecGlob.fin hm hsg⟩, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **The VT-x work of a finalisation at `J`** (XTopJointFinVtJ's
`JAtZ.frVtJ`: an EPT-mapped frame's `ept::unmap`, an owned IO port's
`revoke_ports`, the spec state kept): `JFrVtHyp` from `ArchRefines` [P],
`ARKeep` [P] and `JVtHyps` [J]. -/
theorem jFrVt_of [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) :
    JFrVtHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hk
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  subst hth
  have hcv := capV_of_capAt hc
  refine WP.spec_mono (J.frVtJ hAR hK hV hDS hA hc hk _) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, hm, ⟨Ac1, Lst1, D1, J1⟩, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac1, Lst1, D1, J1, hks.trans hkb, hns, hsg⟩, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **A final mapped EPT root cap's finalisation at `J`** (XTopJointFinVs's
`JAtZ.finVsJb` with VsFin's `fin_ept_root`: FL4's `delete_asid` of the root,
the spec's `deleteAsid`), the slot ready after (the root apart from `H`'s
objects but `other` ones, `JAtZ.ept_obj`); from `ArchRefines` [P],
`JAtZ.vsc`, `jVsApartHyp` and `JVtHyps` [J]. -/
theorem jFinAt_eptRoot [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR)
    (hAp : JVsApartHyp (L := L) arI AR th) (hV : JVtHyps (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th EptRootK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hk hfin
  obtain ⟨p, asid, va, hce⟩ := hk
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth hce
  have hcv := capV_of_capAt hc
  have hap0 := J.ept_obj hA.isSlot hcv
  have hp0 := J.ept_ne0 hA.isSlot hcv
  rw [decide_eq_true hfin]
  refine WP.spec_mono (J.finVsJb hAR Ap hDS hA hc ⟨rfl, rfl, hp0⟩ ⟨_, rfl⟩ true
    (Or.inl ⟨Or.inl rfl, rfl, fun f l e => by cases e⟩)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩
  simp only at h1 h2 h3 hm J1 hSS hks ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Ept p 0#u64 true asid va := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ1, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac, Lst, D, J1, hks.trans hkb, ak_finaliseCap_ns hm hns, SpecGlob.fin hm hsg⟩, EmptyReady.of_apartO (by rw [hcv1]; exact hap0)⟩

set_option maxHeartbeats 4000000 in
/-- **A final VT-x object cap's finalisation at `J`** (XTopJointFinVtJ's
`JAtZ.finEptJ`, an EPT cap but a mapped root's; `JAtZ.finVcpuJ`, a VCPU
cap), the slot ready after; from `ArchRefines` [P], `ARKeep` [P] and
`JVtHyps` [J]. -/
theorem jFinAt_vt (hAR : ArchRefines arI AR) (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th (fun c => EptK c ∨ VcpuK c) := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hk hfin
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  subst hth
  have hcv := capV_of_capAt hc
  rw [decide_eq_true hfin]
  have hsp : objects.finalise_cap st arI s a c true false ⦃ r =>
      VtPost (L := L) arI AR (Z.mv G V) H Cs s σ c true r ∧ EmptyReady (L := L) H G r.2.1 (cslotAddr sl) ⦄ := by
    rcases hk with he | hv
    · exact J.finEptJ hAR hV hA hc he
    · exact J.finVcpuJ hK hV hA hc hv
  refine WP.spec_mono hsp ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, hm, ⟨Ac1, Lst1, D1, J1⟩, hSS, hks⟩, hRd⟩
  simp only at h1 h2 h3 hm J1 hSS hks hRd ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  exact ⟨h1, h2, h3, σ, G, hm, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨V, Ac1, Lst1, D1, J1, hks.trans hkb, hns, hsg⟩, hRd⟩

/-- **The frame and IO port caps' finalisation at `J`**, final or not
(XTopJointFinFrIo's `finFrIo_of`): an unmapped frame's and an unowned IO
port cap's do nothing; a VSpace-mapped frame's from `JFrMapHyp` (`jFrMap_of`), the
VT-x work from `JFrVtHyp` [J]; the slot ready after (an IO port cap is not
physical; a frame's memory holds no object of `H` but `other` ones,
`JAtZ.cobj`, `EmptyReady.of_apartO`). -/
theorem jFinAt_frio [Fl4Proofs.P1.PlainStore st] (hM : JFrMapHyp (L := L) arI AR th) (hV : JFrVtHyp (L := L) arI AR th) :
    JFinAt (L := L) arI AR th FrIoK := by
  intro Z H Cs kb hth
  refine finFrIo_of arI (hM Z H Cs kb hth) (hV Z H Cs kb hth) ?_
  intro s a σ G sl c hW hA hcv hk
  rcases hk with hf | ⟨f, l, o, rfl⟩
  · cases c with
    | Frame p sz r d m ep a' va =>
      obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
      subst hth
      have hC := J.cobj hA.isSlot
      rw [hcv] at hC
      exact EmptyReady.of_apartO (by rw [hcv]; exact hC)
    | _ => cases hf
  · exact EmptyReady.of_nonphys (by rw [hcv]; exact physF_ioPort f l o)
/-- **A final SC cap's finalisation at `J`** (`JScFinHyp` [J], the SC dead
after by P1's `fin_cap_sc.dead`, `JAtZ.sc_ready`), the cap's SC by
`JAtZ.scCap`; the SC may be the current SC. -/
theorem jFinAt_sc (hT : P0.ArchTotal arI) (hF : JScFinHyp (L := L) arI AR th) :
    JFinAtF (L := L) arI AR th ScK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, sb, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have hcv := capV_of_capAt hc
  have hC' := J.scCap arI hA hc
  obtain ⟨hHp, -, hp0, hna, hidle, -⟩ :=
    JAtZ.scCapFacts arI J hA hc ⟨hC'.1, hC'.2, fun _ _ _ _ _ u hu => (hns u hu).elim⟩
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hHp⟩
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (hF (Z.mv G V) H Cs Ac Lst D s a σ rfl J hns sl p sb hA hc hfin)
    (P1.fin_cap_sc.dead (ar := arI) hT s a p sb false J.blk hpS hp0 hna hidle)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, σ1, V1, Ac1, Lst1, D1, hmem1, J1, hSS1, hks1, y1⟩, ⟨d1, d2, d3⟩⟩
  simp only at e1 hmem1 J1 hSS1 hks1 d1 d2 d3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ _ => ⟨d1, d2, d3, y1⟩⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .SchedContext p sb := by
    rw [hSS1.capV hA.isSlot, hcv]
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac1, Lst1, D1, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg⟩, JAtZ.sc_ready arI J1 hcv1 hHp hdp⟩
/-- **A final thread cap's finalisation at `J`** (XTopJointFinThread's
`JAtZ.finThreadJ`, from `JThreadFinHyps`), the slots kept and the kernel
base by P1's `fin_cap_thread.slots`, the thread dead after by P1's
`fin_cap_thread.dead` (`JAtZ.tcb_ready`). -/
theorem jFinAt_thread (hT : P0.ArchTotal arI) (hK : ARKeep arI AR) (hF : JThreadFinHyps (L := L) arI AR th)
    :
    JFinAtF (L := L) arI AR th TcbK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨p, hce⟩ hfin
  subst hce hth
  obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg⟩ := hW
  have hcv := capV_of_capAt hc
  have hthp : Z.th p = some .tcb := hDS.1.2.1.abs hA hc
  have hpT : p ∈ Z.T := J.thT p hthp
  have hpH : H p = some .tcb := J.zH.1 p hpT
  have hv0 := hF.obj (Z.mv G V) H Cs Ac Lst D s a σ rfl J _ p hA.isSlot hcv
  -- not the idle thread: no cap names it (the spec's, `SpecGlob.idle`)
  have hidle : L.idleW s ≠ p := by
    intro e
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hA
    rw [hc] at hc0; cases eq_of_ok_eq hc0
    rw [hca0.abs] at hg0
    have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
    apply hsg.idle sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap])
    rw [JAtZ.idleThread_eq arI J, e]; simp [absCap, Fl4Spec.objRefs]
  have hna : L.actionW s ≠ p := J.action_ne_of_noSwitch hpT hns
  rw [decide_eq_true hfin]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (JAtZ.finThreadJ (Z := Z.mv G V) hT hK hF J hpT hv0 hna hidle)
    (P1.fin_cap_thread.dead (ar := arI) hT s a p false J.blk hpH hna hidle hv0))
    (P1.fin_cap_thread.slots (ar := arI) hT s a p true false J.blk hpH hna hidle hv0)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨σ1, hm1, V1, Ac1, Lst1, D1, J1⟩, d1, d2, d3, d4, d5, d6⟩, e, -, f, hW1⟩
  simp only [ite_true, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  have hks1 : L.ksb s1 = L.ksb s := f.1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun _ => ⟨d1, d2, d3, Ne.symm d4, Ne.symm d5, d6⟩, fun h => (by rw [hpH] at h; cases h),
      fun h => (by rw [hpH] at h; cases h), fun h => (by rw [hpH] at h; cases h),
      fun z h => (by rw [hpH] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Thread p := by
    rw [hSS1.capV hA.isSlot, hcv]
  refine ⟨rfl, trivial, trivial, σ1, G, ?_, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨V1, Ac1, Lst1, D1, J1, hks1.trans hkb, ak_finaliseCap_ns hm1 hns, SpecGlob.fin hm1 hsg⟩, J1.tcb_ready hcv1 hpH hdp⟩
  rw [absCap_zombieTcb]
  exact hm1

theorem okey_of_finObj {c : capability.Cap} (hk : FinObjKind c) : okey c ≠ none := by
  cases c <;> simp_all [FinObjKind, okey]

theorem isUt_of_finObj {c : capability.Cap} (hk : FinObjKind c) : isUt c = false := by
  cases c <;> simp_all [FinObjKind, isUt]

/-- **A non-final cap's finalisation at `J`**, every object cap but frames
and IO port caps: nothing (`fin_idle`), the slot ready by another cap alike
it (`other_key`, `EmptyReady.of_cover`). -/
theorem jFin_nonfinal [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap)
    (hDS : DState (L := L) th s σ G) (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FinObjKind c) (hfi : ¬ FrIoK c)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄ := by
  subst hth
  have hP : Placed Z.th := by obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact J.xtop.rel.1
  have hcv := capV_of_capAt hc
  have hf : isFrame c = false := by
    cases h : isFrame c
    · rfl
    · exact absurd (Or.inl h) hfi
  have hio : ∀ f l o, c ≠ .IoPort f l o := fun f l o e => hfi (Or.inr ⟨f, l, o, e⟩)
  rw [decide_eq_false hfin]
  obtain ⟨cl, he, hmem, -, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk false (by
    rintro (⟨h | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩)
    · cases h
    · exact hio _ _ _ e
    · subst e; simp [isFrame] at hf)
  have hcl0 : cl = .Null := hnio (fun f l e => hio f l 0#u64 e)
  subst hcl0
  obtain ⟨y, hy, hne, hky⟩ := other_key hP hDS hA hcv hk hf hfin
  have hn : okey c ≠ none := okey_of_finObj hk
  have hsh : shape (capV (L.mem s) y) = shape c := shape_of_key hky (by rw [hky]; exact hn)
  obtain ⟨eb, et, ep⟩ := range_of_shape hsh
  have hut : isUt (capV (L.mem s) y) = false := by
    rw [isUt_of_shape hsh]; exact isUt_of_finObj hk
  rw [he, WP.spec_ok]
  exact ⟨hrem.symm, trivial, trivial, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
    hW, EmptyReady.of_cover (x := cslotAddr sl) hy hne (fun h => by rw [ep]; rw [hcv] at h; exact h) hut
      (by rw [eb, hcv]) (by rw [et, hcv])⟩

/-- **Every object cap kind has its final finalisation proved**: an object
cap (`FinObjKind`) is a notification, frame or IO port, IRQ handler,
endpoint, reply, native VSpace, SC, thread, VT-x (EPT or VCPU) or mapped EPT
root cap (the cases of XTopJointWJLDel's `finJLZ`). -/
theorem finObjKind_covered {c : capability.Cap} (hk : FinObjKind c) (hn : ¬ NtfnK c) (hfi : ¬ FrIoK c)
    (hq : ¬ IrqK c) (he : ¬ EpK c) (hr : ¬ RpK c) (hvs : ¬ VsK c) (hsc : ¬ ScK c) (ht : ¬ TcbK c)
    (hvt : ¬ (EptK c ∨ VcpuK c)) (hrt : ¬ EptRootK c) : False := by
  cases c with
  | Endpoint e b x1 x2 x3 x4 => exact he ⟨_, _, _, _, _, _, rfl⟩
  | Notification p b w r => exact hn ⟨_, _, _, _, rfl⟩
  | Reply p g => exact hr ⟨_, _, rfl⟩
  | Thread t => exact ht ⟨_, rfl⟩
  | SchedContext p sb => exact hsc ⟨_, _, rfl⟩
  | IrqHandler i => exact hq ⟨_, rfl⟩
  | PageTable p m a v => exact hvs (Or.inl ⟨_, _, _, _, rfl⟩)
  | PageDirectory p m a v => exact hvs (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | Pdpt p m a v => exact hvs (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))
  | Pml4 p m a => exact hvs (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))))
  | AsidPool p b => exact hvs (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))))
  | Vcpu v => exact hvt (Or.inr ⟨_, rfl⟩)
  | Ept p lv m asid va =>
    by_cases hm : m = true ∧ lv = 0#u64
    · obtain ⟨rfl, rfl⟩ := hm; exact hrt ⟨_, _, _, rfl⟩
    · exact hvt (Or.inl ⟨_, _, _, _, _, rfl, hm⟩)
  | IoPort f l o => exact hfi (Or.inr ⟨_, _, _, rfl⟩)
  | _ => first | exact hk | exact hfi (Or.inl rfl)

/-- The trivially finalised caps but untyped ones are not physical. -/
theorem physF_triv (c : capability.Cap) (ht : TrivFin c) (hu : isUt c = false) : physF c = false := by
  cases c <;> simp only [TrivFin] at ht <;> first | exact ok_inj (phys_eq _).symm | simp [isUt] at hu

/-- A CNode cap's range: its CNode's `2 ^ (r + 5)` bytes. -/
theorem range_cnodeR (q r gs g : U64) (hr : r.val + 5 < 64) (hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64) :
    baseF (.CNode q r gs g) = q.val ∧ topF (.CNode q r gs g) = q.val + 32 * 2 ^ r.val - 1 := by
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hsz : sizeF (.CNode q r gs g) = core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT :=
    ok_inj (size_eq _).symm
  have hs : (core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT).val = r.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits,
      fl4_abi.consts.bits.SLOT]
    omega
  have hm := maskF_val (b := core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT) (by rw [hs]; exact hr)
  rw [hs, e5] at hm
  have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine ⟨by unfold baseF; rw [ptrF_cnode], ?_⟩
  unfold topF
  rw [ptrF_cnode, hsz]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

/-- A word holding an `other` object of `H` (a CNode) is dead (`DeadP`
reads the TCB, endpoint, notification, reply and SC words only). -/
theorem deadP_other {H : P1.Heap} {s : S} {q : U64} {z : Nat} (h : H q = some (.other z)) :
    DeadP (L := L) H s q :=
  ⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e),
    fun e => (by rw [h] at e; cases e), fun z e => (by rw [h] at e; cases e)⟩

/-- **A CNode cap's slot is ready to be emptied**: the only object of `H`
in its range is its CNode (`other`, dead for `DeadP`). -/
theorem JAtZ.cnode_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {q r gs g : U64}
    (hcv : capV (L.mem s) x = .CNode q r gs g) (hth : Z.th q = some (.cnode r.val)) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHq : H q = some (.other (r.val + 5)) := hJ.cnode q r.val hth
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64 := by
    have := J.kern.heap.fits q _ hHq; rw [← e5]; exact this
  have hlt : r.val + 5 < 64 := J.kern.heap.lt64 q _ hHq
  obtain ⟨e1, e2⟩ := range_cnodeR q r gs g hlt hfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q' k, H q' = some k → q' ≠ q → q'.val + 2 ^ k.bits ≤ q.val ∨ q.val + 32 * 2 ^ r.val ≤ q'.val := by
    intro q' k hq' hne
    have := J.kern.heap.disj q' k q _ hq' hHq hne
    simpa only [show (P1.HKind.other (r.val + 5)).bits = r.val + 5 from rfl, e5] using this
  have h32 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine fun lo hi hlh h1 h2 => Or.inr fun q' hq' => ?_
  · by_cases e : q' = q
    · subst e; exact deadP_other hHq
    · cases hk : H q' with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q' k hk e with h | h <;> omega

/-- **The readiness at `J` of a cap finalised without effect** (`RdTrivHyp`
at `WJ`): the trivial caps cover nothing, a CNode cap's CNode is dead for
`DeadP` (`cnode_ready`); zombies by `JRdTrivHyp`. -/
theorem rdTrivJ [Fl4Proofs.P1.PlainStore st] (hRT : JRdTrivHyp (L := L) arI AR th) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) : RdTrivHyp (L := L) (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th := by
  intro s a σ G sl c hDS hW hA hc hcn hnk _ _
  rcases cap_cases c hcn with ht | hcn' | hz | ho
  · intro hp hu
    rw [capV_of_capAt hc] at hp hu
    rw [physF_triv c ht hu] at hp
    cases hp
  · obtain ⟨q, r, gs, g, rfl⟩ := hcn'
    have hcvd : CapValid th (.CNode q r gs g) := hDS.1.2.1.abs hA hc
    subst hth
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
    exact JAtZ.cnode_ready arI J (capV_of_capAt hc)
      (show Z.th q = some (.cnode r.val) ∧ r.val ≠ 0 from hcvd).1
  · obtain ⟨p, zt, n, rfl⟩ := hz
    exact hRT Z H Cs kb hth s a σ G sl p zt n hDS hW hA hc
  · exact absurd ho hnk

/-- **A zombie's slot is ready at `J`** (`JAtZ.zombie_ready`, a TCB zombie's
TCB dead by `JZombieTcbHyp`). -/
theorem jRdTrivHyp_of (hZT : JZombieTcbHyp (L := L) arI AR th) : JRdTrivHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G sl p zt n _ hW hA hc
  have hW' := hW
  subst hth
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
  exact J.zombie_ready hA.isSlot (capV_of_capAt hc)
    (hZT Z H Cs kb rfl s a σ G hW' _ hA.isSlot p zt n (capV_of_capAt hc))

/-- A cap but a frame cap is no spec frame cap. -/
theorem absCap_notPage {c : capability.Cap} (h : isFrame c = false) : ¬ IsPageCap (absCap c) := by
  cases c <;> simp_all [isFrame, absCap, IsPageCap]


end

end

end Fl4Proofs.P3
