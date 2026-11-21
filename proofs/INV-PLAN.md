# INV-PLAN: the entry premises of `kernel_entryJ7` as a carried invariant (inv1)

Base: FL4-audit `b2c1ab2d` (kp17 on int/j2). I edited no proof file. The only scratch file is
`proofs/scratch/inv1/nowFalse.lean` (untracked). I
checked it with `lake env lean` against the lead mirror's build on tokyo, read-only (tasks inv1-c2..c5); §0 has
the result.

Tags: [J] a joint or spec fact true in reachable states; [P] platform; [W] a proof gap (a whole sub-proof named);
[S] scope (VT-x, l4h trap mode, one core, native syscalls).
Kinds for [J] (task item 2): **(a)** derivable from `JAtZ` (plus the other carried facts) today;
**(b)** a field to carry (in `JAtZ` or in a carried bundle beside it); **(c)** true only at entry, so the previous
step's post must establish it.
Sizes: S < 300 lines, M 300–1500 lines, L > 1500 lines or a whole cone.

---------------------------------------------------------------------------------------------------------------

## 0. Blocking finding: `PPPlat` is uninhabited, so the top theorem is vacuous today

`PPPlat.now : ∀ a σ, NowAgree arI a σ` (XTopJointPP.lean:355-357). `NowAgree a σ` (XTopJointPP.lean:266) asks
`arI.now a` to return `r` with `doMachineOp getCurrentTime σ = {(r.bv, …)}` **and `σ.curTime ≤ r.bv`**, for
*every* spec state σ. `getCurrentTime` (Fl4Spec/Machine.lean:654) returns
`ofNat (min (unat (-(getCurrentTimeBuffer+1))) (last+passed))`, so its value is at most
`2^64 - getCurrentTimeBuffer - 1`, and `getCurrentTimeBuffer ≠ 0` (`getCurrentTime_buffer_pos`). Take any σ with
`curTime := allOnes`: the inequality fails. So `∀ a σ, NowAgree a σ` is false for every arch, and every theorem
that takes `hPP : PPPlat` is vacuously true. That includes `kernel_entryJ7`, `dispatch_allRI`,
`dispatch_invokeJEPZR`, `jPreemptRestHypC_of` and everything below that takes `JEntryGlob` (which has `pp : PPPlat`).

Scratch proof `nowAgree_all_false : ¬ ∀ σ, NowAgree arI a σ` is in `proofs/scratch/inv1/nowFalse.lean`.
**Checked:** `lake env lean` against the lead mirror's build on tokyo (task inv1-c5) reports no errors, and
`#print axioms nowAgree_all_false` gives propext, Classical.choice, Quot.sound. So
`PPPlat arI AR → ∀ a : A, False`: every theorem that has both an `a : A` and `hPP` in scope is vacuous.

The other ∀σ platform premises are not false, but they are degenerate. Each forces the platform to model "no
interrupts / one fixed oracle":
* `IrqPlat.take : ∀ a σ, take_pending_irq a ⦃ … getActiveIRQ σ = {(irq, …)} ∧ (r = NO_IRQ ↔ irq = none) … ⦄`
  (XTopJointPreempt.lean:297). Take σ with every `irqMasks` true: `getActiveIRQ` gives `none`, so
  `take_pending_irq a` returns `NO_IRQ` for every `a`. Then any σ whose oracle gives an unmasked line forces
  `irqOracle ≡ 0xFF`. This is consistent only because `irqOracle` is opaque, and every interrupt branch proved
  under it is vacuous.
* `PPPlat.irq` (XTopJointPP.lean:358): the same argument for `irq_pending`.
* `PortInVal` (XTopPortIn.lean:73, `JEntryGlob.portIn`): a ∀σ statement about the opaque `in8Impl` etc.,
  consistent but very strong.
* Dropping `curTime ≤ r` from NowAgree's ∀σ form does not fix it. The equation part forces `now a` to equal the
  oracle at every `timeState`/`lastMachineTime`, so the clock would be frozen at the cap.

**Required restatement before the invariant line (group G0):** a platform relation `MR : A → MachineState → Prop`
between the arch state and the spec's machine state (clock position and last time, IRQ oracle position, masks).
* It is carried in the bundle: true at boot [P].
* It is preserved pairwise [P]: `now` with `getCurrentTime`, `irq_pending`/`take_pending_irq` with
  `getActiveIRQ`, `mask_irq` with `maskInterrupt`, `set_deadline` with `setDeadline`, and `port_in`.
* It is kept by the arch ops that do not touch the machine, which is ARKeep-style.

Then `NowAgree`, `PPPlat.irq`, `IrqPlat.take` and `PortInVal` take `MR a σ.machineState →`, and
`σ.curTime ≤ r` comes from a spec invariant `ValidMachineTime σ` (l4v `valid_machine_time`:
`cur_time ≤ last_machine_time ≤ cap`), not from the platform. Every proof that uses `hPP.now`, `hPP.irq` or
`hIP.take` must thread `MR` from the J state: ~25 use sites (grep `hP.now\|hPP.now\|\.irq a\|hIP.take\|hIP.base.take`).
Size **L** (cross-cutting), but mechanical.

---------------------------------------------------------------------------------------------------------------

## 1. Inventory of the premises

`kernel_entryJ7` (XTopJointKEntry7.lean:128-151). "With `dispatch_invokeJEPZR` in place of the preemption premise"
means three things:
* `hRest : JPreemptRestHypE` is gone. `jPreemptRestHypEQ_ofC` + `jPreemptRestHypC_of` cover it
  (XTopJointPreemptR.lean:32,73).
* `KPreFinRestHypI` becomes removable, see item T8.
* `hIP` stays `IrqPlatI` (its `.base` feeds the JEPZR chain).

### 1.1 Top level

| # | premise | statement (short) | tag | l4v | consumed at |
|---|---|---|---|---|---|
| T1 | `J` | `JAtZ … s a σ` | carried | `invs ∧ state_relation` | everywhere |
| T2 | `hni` | `Entered σ` = `ct ≠ idle ∧ action = resume` (StepSem.lean:230) | [J] (c) + [S] | `ct_running`, `scheduler_action = resume_cur_thread` | `budgetOkF/T` (hni0), `dispatch_allRI` (recv/yield), `Entered σb` KEntry7:241 |
| T3 | `hn` | `NativeSys n c` | [S] event | — | KEntry7:187 |
| T4 | `hflag` | `∀ ct v, cur_thread = ct → flags(ct) at the FAULT_IP-written state &&& TRAP_SYSCALLS = 0` | [S] M2 | none (l4h) | KEntry7:184 |
| T5 | `hB` | `∀ x, kheap ct = tcb x → KBudget arI a (faultIPSt σ ct x)` (KEntry.lean:214) | see 1.2 | | KEntry7:182,202 |
| T6 | `hK` | `∀ σb, BudgetAt σ σb true → ∀ ghosts, JAtZ … σb → KDispHypsRI …` (KEntry7:30) | see 1.3 | | KEntry7:243 |
| T7 | `hFin` | `∀ x ∈ specFront c σ, ∀ ghosts, JAtZR … x.2 → KFinAtR …` (KEntry4.lean:40) | see 1.4 | | `kPreFinHypCI_of`, KEntry7:228,250 |
| T8 | `hPR` | `KPreFinRestHypI` (KEntry7:45): finish at a `RestE` hole with no `JAt` after the path | [W] | `he_invs`, `schedule_invs` | `kPreFinHypCI_of` |
| T9 | `hARI` | `ARIface` = `ARKeep` (9 arch ops keep `AR`) + `mask` | [P] | arch corres | everywhere |
| T10 | `hA` | `P0.ArchTotal arI` | [P] | — | everywhere |
| T11 | `hnd` | `numDomains = 1` | [P] | config | |
| T12 | `hPP` | `PPPlat`: `now` ∀σ (**FALSE**, §0), `irq` ∀σ (degenerate), `irqAR`, `minBudget` | [P] | machine ops | preemption path |
| T13 | `hmrt`, `hmb` | `max_release_time = MAX_RELEASE_TIME`, `min_budget = MIN_BUDGET` (∀ a) | [P] | constants | |
| T14 | `hIP` | `IrqPlatI` (IrqZI.lean:38): `base : IrqPlat` (`take` ∀σ degenerate; `takeAR`; `noIpi` [S] one core; `ackAR`), `act : ∀ s a σ, JAt s a σ → take_pending_irq a ⦃ getActiveIRQ σ = some i → interruptStates i ≠ inactive ⦄` | [P], `act` really [J] | `valid_irq_masks` | `handleIrqJI` (IrqZI:242,289) |
| T15 | `hNS` | `∀ s a σ, JHoleAt s a σ → NativeScope σ` | [S], ∀-pred | VT-x out | preemption path, `hvm_of_ns` |
| T16 | `hNSR` | `∀ ghosts s a σ, JAtZR … → NativeScope σ` | [S], ∀-pred | | `signalRestJHypZR_of_ns` in finish |
| T17 | `hT` | `TimeAgree` (max_period, us_to_ticks, wcet, timerUnit = 1) | [P] | constants | finish |
| T18 | `hmax`, `htu` | `maxTicksToUs = U64.MAX`, `ticks_to_us a v = ticksToUs v` | [P] | constants | |
| — | `hRest` | `JPreemptRestHypE` | REMOVED via `dispatch_invokeJEPZR` route | | |

### 1.2 `KBudget arI a σ0` (XTopJointKEntry.lean:214), at `σ0 = faultIPSt σ ct x`

| # | field | statement | tag | l4v | consumer |
|---|---|---|---|---|---|
| B1 | `now` | `NowAgree arI a σ0` | [P] (per state; needs `MR`, §0) | machine time | `budgetOkJ/F/T` |
| B2 | `cur` | `CurInv σ0` | [J] | `cur_tcb`, `cur_sc_tcb`, `ct_active` | `budgetOkJ` |
| B3 | `off` | `OffReady σ0` (head rTime + consumed ≤ curTime) | [J] | `cur_sc_offset_ready` | `budgetOkJ`; gives `rd0` |
| B4 | `tmo` | `NoTmoSend σ0 ∨ (ct ∉ rq ∧ ct running/restart ∧ endpoint handler p ∧ non-RR SC ∧ ∀ xe, kheap p = ep xe → CanBlock false xe)` | [J]/**[W] false in reachable states** | — | `budgetOkF` / `budgetOkT` (XTopJointBudgetT.lean:89) |

B4 is false in reachable states. With an endpoint timeout handler on which a receiver waits (`recvEP`), a non-RR SC
and an insufficient budget at entry, neither disjunct holds. kp17 proved exactly this case only on the preemption
path (`JTH.tmoRecvJ`). The entry needs a `budgetOkTR` (the same recv machinery at `budget_ok`), and B4 must become
`NoTmoSend ∨ (ct ∉ rq ∧ running/restart ∧ endpoint handler ∧ non-RR)` with the endpoint state free.

### 1.3 `KDispHypsRI` (XTopJointKEntry7.lean:30)

* `inv` (InvSys) gives `JEntryGlob`, `JEntryAt`, `JPathAt` at σb (the tables below).
* `recv` (RecvSys):
  * R1 `∀ d p, ct ∉ readyQueues` [J] (`ct_not_in_q`), consumed by `dispatch_recvJL` hnq (XTopJointRecvIpcLink.lean:679);
  * R2 `validFaultHandler (ct's handler)` [J] (`valid_fault_handler`), consumed there as hvfh.
* `mid` (MidSys) M1 [W]: the whole ReplyRecv/NBSendRecv/NBSendWait dispatch to `DispPostR PPQCI` (sch12 (2), not started).

**JEntryGlob** (XTopJointEntry.lean:302):

| # | field | statement | tag |
|---|---|---|---|
| G1 | `ari` | ARIface | [P] |
| G2 | `tot` | ArchTotal | [P] |
| G3 | `delParts.archRef` | `ArchRefines` (set_vspace, invalidations keep/set `AR`) (VsArch.lean:122) | [P] |
| G4 | `delParts.arKeep` | ARKeep | [P] |
| G5 | `delParts.vt.io/ept/eptFr/vcpu` | `∀ Z… with Z.th = th, JAtZ … → VtIoPlace / VtEptPlace / EPT frame ASID names no PML4 / VtVcpuPlace` (XTopJointFinVtJ.lean:91) | [J] ∀-pred, VT-x |
| G6 | `delParts.thr.obj` | `∀ JAtZ at th, a slot's Thread cap's TCB has VCPU word (p+3664) = 0` (XTopJointDelR.lean:414) | [S] ∀-pred |
| G7 | `delParts.thr.ticks` | maxTU / ticks_to_us | [P] |
| G8 | `nd` | numDomains = 1 | [P] |
| G9 | `pp` | PPPlat (**false**, §0) | [P] |
| G10 | `dom` | DomConfig | [P] |
| G11 | `portIn` | PortInVal ∀σ | [P] (strong, §0) |
| G12 | `sigRest` | `∀ H Cs, SignalRestJHyp H Cs` = `∀ JAtZ …, the notification's bound TCB is RunningVM → send_signal ⦃JAtZ⦄` (ScSignalJ.lean:194) | [J]/[S] ∀-pred |
| G13 | `timeAg` | TimeAgree | [P] |
| G14 | `maxTU`, `tu` | constants | [P] |

**JEntryAt** (XTopJointEntry.lean:338), all at σb (the state after a passing budget check):

| # | field | statement | tag | l4v | consumer |
|---|---|---|---|---|---|
| E1 | `ni` | Entered σ | [J] (c) | ct_running ∧ resume | invocation entry |
| E2 | `ctnq` | ct ∉ readyQueues | [J] | ct_not_in_q | `sendLeafJ`/`sendBlockJ`, `jUtRetHypR_of` hnq |
| E3 | `sg` | SpecGlob σ (IRQ node slots null/ntfn; no non-frame cap names an IRQ node CNode or the idle thread) | [J] spec | valid_irq_node, valid_global_refs | `decode_invocation_cnodeJ_steps` hsg, WJ |
| E4 | `rd0` | consumed = 0 → current SC's active head ready | [J] spec | cur_sc_offset_ready 0 | resets/retypes, SC decodes |
| E5 | `stall` | `remote_tcb_stall s a q = ok (s,a)` | [P] one core | — | Thread decode |
| E6 | `flags` | FlagsRel Z.T mem σ | [J] joint | tcb_relation tcbFlags | SetFlags (`hFl`) |
| E7 | `epQ` | ∀ e, EpQPre σ e | [J] spec | valid_ep / sym_refs | CNode decode `hQ` |
| E8 | `handlers` | HandlersActive mem ksb G (IrqControl.lean:30) | [J] FL4 | valid_irq_handlers | IRQ control `hHA` |
| E9 | `ports` | IoPortsAlloc mem ksb G | [J] FL4 | ioport_control_unique | IO port control `hPA` |
| E10 | `ioapics` | num_ioapics a = σ's count | [P] | | IRQ control |
| E11 | `archIrq` | ArchIrqRel ar σ (IrqArch.lean:377; `map`/`mapr`/`mask` ∀ a) | [P] | | IRQ control |
| E12 | `vfh` | ct's fault handler valid | [J] spec | valid_fault_handler | `faultHypJZ` |
| E13 | `cnf` | ct has no fault | [J] spec | fault_tcbs_valid_states | `sendLeafJ2` hnf |
| E14 | `vsTyp` | ∀ slot, OffTabOK Z s σ cap (mapped table outside the sets: spec table of that kind, 4 KiB aligned, apart) | [J] joint | valid_cap typ_at, pspace_aligned/distinct | `decode_invocation_page_tableJO` |
| E15 | `live` | `∀ H Cs Ac Lst D, JAtZ … → LiveDN Z.th H Cs Z.G s σ` (LiveJ, DbgWF, NullOrig) | [J] ∀-ghosts | if_unsafe_then_cap, if_live_then_nonz_cap, zombies_final, valid_nullcaps | all WJL deletions and installs |
| E16 | `fnz` | FrNZ Z.th mem (no non-device frame cap at 0) (TcbCtl.lean:1367) | [J] FL4 | cap_refs_in_kernel_window | `bokInstall` |
| E17 | `urz` | UtZero mem G σ (free parts read 0 in the spec) | [J] joint | untyped_ranges_zero | frame retype |
| E18 | `utks` | UtNodesJ mem G ksb (RAM untypeds miss the 64 nodes) | [J] FL4 | kernel_window | frame retype `nodeB` |

**JPathAt / JPath** (XTopJointDispatch.lean:123, XTopJointEntry.lean:652). The ∀ over the front-end outcomes is
harmless (they are unique, `frontEx`). Per cap:

| # | cap / field | statement | tag |
|---|---|---|---|
| P1 | Thread `hFr` | ReadFPU: FpuFrameJHyp Z s σ x0 (the first extra frame valid, distinct, off global refs) | [J] joint |
| P2 | Thread SetEPTRoot, IoPort z≠0, Vcpu, Ept, Frame ep, Untyped `vtx`, Pool `native` | JVtxScope / native extra cap | [S] VT-x |
| P3 | SchedContext `JSchedCtxPath.tm/mb/max/tu` | constants | [P] |
| P4 | `JSchedCtxPath.arch`, `JSchedCPath.arch` | decode at this (s,ar) keeps AR | [P] per state (derivable from ARKeep, S) |
| P5 | `JSchedCtxPath.rest`, `JSchedCPath.rest` | `∀ H Cs Ac Lst D, JAtZ → decode ⦃ScStepP1⦄` (debug word, BlkOK after) | [P] (really P1-provable), ∀-ghosts |
| P6 | `JSchedYieldPath` | constants | [P] |
| P7 | `JSchedCPath.core` | cpu = Z.c | [P] one core |
| P8 | Frame `JFramePath.hno` | a large non-device frame cap: disjoint/within every slot's frame cap | [J] FL4 (valid_cap, cap overlap) |
| P9 | AsidControl `heapH` | ArchFitHyp H σ ∧ RegionUnrefAt H Cs D s | [J] joint |
| P10 | AsidControl `vsReach` | VsReachMiss for childless pool-sized untyped regions at the restart state | [J] joint (valid_vs_lookup + untyped_children_in_mdb) |
| P11 | Untyped `fan`, `rcb` | 256, 16 | [P] |
| P12 | Untyped `core0` | Z.c = 0 | [P] one core |
| P13 | Untyped `bufObj` | BufObjHyp Z.B σ (every IPC buffer word inside a spec object) | [J] joint |
| P14 | Untyped `heapH` | as P9 | [J] |
| P15 | Untyped `vsReach` | VsReachMiss for the cap's region | [J] |
| P16 | Untyped RAM `ret` | JUtRetHypR2 (only VT-x types 14..18 left) | [W] = [S] |
| P17 | Device `devApart` | DevApart th H G Cs s (DevJ.lean:60) | [J] |
| P18 | Device `devFree` | DevFreeT mem G σ | [J] |
| P19 | Device `devGpm` | DevGpm mem G σ | [J] |
| P20 | Device `bufObj/heapH/vsReach` | as P13–P15 | [J] |

### 1.4 `KFinAtR` (XTopJointKEntry4.lean:40), at every `JAtZR` outcome of `specFront`

| # | field | statement | tag | l4v |
|---|---|---|---|---|
| F1 | `hd` | `domainTime ≠ 0 ∨ NdOK s σ` (DomRel ∧ DomListOK ∧ DOM_SCHED_IDX word = domainIndex) | [J] | valid_domain_list, FL4 index word |
| F2 | `vt` | `∀ V1 s1 a1 σ1 …, JAtZR (Z.mv Z.G V1) … → ∀ t ∈ Z.T, Z.th t = tcb ∧ mapped vtable PML4 asid ≠ 0` | [J] ∀-pred | valid_cap PML4 |
| F3 | `arch` | ArchSwF ∀ SchedRel ∧ NtfnStateRel ∧ FpuOwnOK states | [P] ∀-SchedRel | arch switch corres |
| F4 | `archNd` | ArchNdF (same shape) | [P] ∀-SchedRel | |
| F5 | `fo` | FpuOwnOK σ | [J] spec | valid_cur_fpu |
| F6 | `sni` | SniHyp ∀ SchedRel | [P] ∀-SchedRel | setNextInterrupt corres |
| F7 | `send` | SendHyp ∀ SchedRel | [P]/[S] SMP | |
| F8 | `tail` | FL4 `schedule s a ⦃ … → AR r.2 σ'.cr3 ⦄` (SchTailHypsR.ar) | [P]+[J] (CR3 after the switch) | set_vm_root corres, valid_vspace_objs |

`hd` and `tail` are per state. The [P] ∀-SchedRel statements quantify over a relation, not over reachable states.
They are fine only if the spec ops they mention have no assert that fails at an unreachable SchedRel state; §3
lists them to check.

---------------------------------------------------------------------------------------------------------------

## 2. Classification of the [J] items and preservation cost

The key structural point: **split the [J] facts into spec-only and joint.**
* Spec-only facts (a predicate on σ alone) are best carried as one structure `SInv σ`. It is preserved by a
  spec-level theorem `fl4KernelEntrySyscall`/`callKernel` ⦃SInv⦄ (l4v AInvs style). That theorem imports only
  Fl4Spec plus a handful of spec-lemma files, so it never touches the 5500-module JAtZ cone. sch12's
  `syscall_post`, `post_bindE` and `fv_auto` (XTopJointMidRunS) are exactly the shell for it.
* Joint facts need the FL4 frames of each J step, so they belong in JAtZ (or in a `JInv` beside it, with the step
  lemmas' posts extended).

| item | spec-only? | kind | what must re-prove preservation | size |
|---|---|---|---|---|
| T2/E1 Entered | spec | (c) | post: `schedule` then `activateThread` ends in `resumeCurThread` (jat_finishJR already gives `RJ` after activate; add `action = resume` to its post). `ct ≠ idle` is event scope: the idle thread never traps (state it in the step relation) | S |
| B2 CurInv | spec | (a) | `J.cur` + Entered (`J.curInv`), `faultIPSt` frame (one register) | S |
| B3 OffReady | spec | (b) SInv | schedule/switch_sched_context (refill_unblock_check, consumed := 0), every op that changes curTime/consumed/the head (charge, refill ops, SC config), timers | M |
| E4 rd0 | spec | (a) from B3 | `budget_ok_offReady` already | S |
| B4 tmo | spec | restate to drop CanBlock, then prove `JAtZ.budgetOkTR` (copy of kp17's `mcsPPJR`/`tmoRecvJ` at `budget_ok`) | — | M |
| R1/E2 ctnq | spec | (b) SInv: `action = resume → ct ∉ rq` | schedule (switch dequeues; resume keeps), possibleSwitchTo/tcbSchedEnqueue (other threads only, sch12 (2)(i) argument), the mid state (sch12 (2)) | M |
| R2/E12 vfh | spec | (b) SInv: every TCB's handler valid (l4v `valid_tcb` slice) | installs (SetSpace/Configure/SetSchedParams check), retype (null), deletion (null), copy into TCB slots | S–M |
| E13 cnf | spec | (b) SInv `fault_tcbs_valid_states`: fault ≠ none → not active | send_fault_ipc (blocks/Inactive), fault reply, cancel_ipc, restart | M |
| E3 sg | spec | (b) SInv (deletion loop already carries it in WJ) | retype (new caps), IRQ control issue, copy/mint | M |
| E7 epQ | spec | (b) SInv (`valid_ep`/sym_refs slice) | every queue op (send/recv/cancel/reply/restart) | M |
| F5 fo | spec | (b) SInv | lazyFpuRestore; TCB deletion fpu_release | S |
| F1 hd | mixed | DomRel (a) from `RelTopM`. DomListOK (b) SInv; IDX word (b) JAtZ | DomainSetStart, next_domain (ScNextDom) | S |
| ValidIrqMasks (new) | spec | (b) SInv: `interruptStates i = inactive → irqMasks i` | IRQ control issue, IRQ handler set/clear, deletion of IRQ handler caps | S–M |
| ValidMachineTime (new) | spec | (b) SInv | updateTimeStamp | S |
| NativeScope(+X) | spec + FL4 | (b): spec part (no `runningVM`; the spec never writes it, Fl4Spec/Ipc.lean:515 only reads) is mechanical; FL4 part (no VT-x caps/objects, VCPU words 0) is JAtZ-level | spec: one frame over every `tcbState` writer. FL4: retype types 14..18 excluded ([S]), copies | S (spec) + M (FL4) |
| T15/T16 hNS/hNSR | — | (a) once NativeScope is carried: JHole has the base's kheap (ScChargeH.lean:52 `spec`); JAtZR states come from posts, so restate consumers to take NativeScope of the state | SignalRestJHypZR consumers | S |
| G12 sigRest | — | (a) from NativeScope | — | S |
| G5 JVtHyps, G6 thr.obj | FL4 | (a) given NativeScopeX (no VCPU/EPT caps, no EPT-mapped frames, VCPU words 0); otherwise stay [S] | — | S |
| E6 flags | joint | (b) JAtZ | SetFlags, TCB retype (0), TCB word frames elsewhere | S–M |
| E8 handlers | FL4 | (b) JAtZ | IRQ control issue, handler set/clear, delete | S–M |
| E9 ports | FL4 | (b) JAtZ | IO port control issue, delete | S |
| E14 vsTyp | joint | (b) JAtZ | detype (the source of "mapped outside the sets"), map/unmap, retype | L |
| E15 live | joint | (b) JAtZ, at the carried ghosts (drop the ∀ H Cs Ac Lst D) | every cap op, TCB list ops, deletion (WJL already carries it inside a deletion) | L |
| E16 fnz | FL4 | probably (a) from `JAtZ.fcap` (FrSlots: frame bytes in non-device data pages) + no spec data page at 0 (`JKern.h0`/SpecCover); else (b) | — | S |
| E17 urz | joint | (b) JAtZ | retype/reset (zeroing), IPC-buffer and frame stores (`freeOut_of_obj`) | M |
| E18 utks | FL4 | (b) JAtZ (UtCapP3 has no node-slot field; `ns`/`nsFree` are MDB slots) | retype (children are sub-ranges) | S |
| P1 hFr | joint | (a/b): from `fcap` + `bok` + SpecGlob for the frame; check | — | S–M |
| P8 hno | FL4 | (b) JAtZ (frame-cap overlap discipline) | DeriveSubframe, retype, copy | M |
| P9/P14 heapH | joint | ArchFitHyp (b) S–M; RegionUnrefAt (b) L (untyped_children_in_mdb + live) | retype, every reference writer (debug/timer lists) | L |
| P10/P15 vsReach | joint | (b) JAtZ at the entry state; frame across set_thread_state | VSpace map/unmap, retype/detype | L |
| P13 bufObj | joint | (b) JAtZ (B ⊆ objects; B grows at frame retype, shrinks at detype) | retype, detype | S–M |
| P17–P19 dev* | joint | (b) JAtZ (DevApart.retype, DevFree.retype exist) | retype | S–M |
| F2 vt | FL4 | `thOfT` (a) + `VtAsidJ` (b) as a JAtZ field "mapped vtable PML4 asid ≠ 0"; then the ∀ is (a) | SetSpace/Configure install, copy/move | S–M |
| F8 tail CR3 | joint | (b) a vtable-to-CR3 relation (findVSpaceForAsid of the chosen thread's vtable = FL4's set_vm_root target) | VSpace/ASID ops, deletion | L |
| M1 mid [W] | — | proof gap (sch12 (2) (i)–(iv)) | — | L |
| T8 KPreFinRestHypI [W] | — | removable: build `dispatch_invokeJEPZRI` = JEPZR ending in `PPQCI`/`PPQJI` (use `afterInv_of_mcsI` instead of `afterInv_of_mcs` in `jPreemptRestHypC_of`/`jPreemptRestHypEQ_ofC`). Every RestE hole then has `JAt` after, so the ¬JAt hypothesis is absurd | — | S |
| T14 IrqPlatI.act | spec | (a) once ValidIrqMasks is carried (see §3) | — | S |

Counts:
* Premise items in §1: **83**. 18 top level including hRest; 4 KBudget; 3 KDispHypsRI; 16 JEntryGlob rows (G1–G14,
  with G5 counted as 4); 18 JEntryAt; 20 JPath; 8 KFinAtR.
* By tag: **[J] 37**, **[P] 30** (one of them false: PPPlat.now, appearing twice as T12/G9), **[W] 4**
  (B4 de facto, M1, T8, P16), **[S] 12** (T3, T4, T15, T16, G6, P2 group, P7, P12, E5, noIpi, F7, P16's VT-x part).
* [J] by kind: **(a) 11** (B2, E4, hNS, hNSR, G12, G5, G6, F1-DomRel, F2-thOfT, E16 likely, IrqPlatI.act after
  SInv); **(b) 24** (SInv 10: B3, ctnq, vfh, cnf, sg, epQ, fo, DomListOK, ValidIrqMasks, ValidMachineTime;
  JAtZ/JInv 14: flags, handlers, ports, vsTyp, live, urz, utks, hno, heapH, vsReach, bufObj, dev*×3 as one,
  VtAsidJ, IDX word, CR3 relation, NativeScopeX); **(c) 2** (Entered, and the idle-free event).
* Sizes: L 7 (MR redesign, live, vsTyp, heapH/RegionUnref, vsReach, CR3 tail, mid). M ~9. Everything else S.

---------------------------------------------------------------------------------------------------------------

## 3. ∀-over-a-predicate premises (task item 3)

| premise | quantifies | implied by the predicate today? | false at a non-reachable instance? | action |
|---|---|---|---|---|
| `PPPlat.now` | ∀ a σ | — | **false everywhere** (§0) | restate with MR + ValidMachineTime (G0) |
| `PPPlat.irq`, `IrqPlat.take` | ∀ a σ | — | degenerate (forces no IRQs) | restate with MR (G0) |
| `PortInVal` | ∀ a a' p z v σ | — | strong | restate with MR (G0) |
| `IrqPlatI.act` | ∀ JAt s a σ | no | **yes**: a JAt σ with line i inactive and unmasked in `machineState.irqMasks` whose oracle returns i. JAt relates no masks | see below |
| `hNS` | ∀ JHoleAt | no | yes: JAtZ admits a RunningVM TCB (VT-x) | carry NativeScope; then (a) |
| `hNSR` | ∀ JAtZR | no | yes (same) | carry; restate consumers per state |
| `JEntryGlob.sigRest` | ∀ H Cs, ∀ JAtZ | no | yes (RunningVM bound thread) | (a) from carried NativeScope |
| `JDelParts.vt` (JVtHyps ×4) | ∀ JAtZ at th | no | yes (any JAtZ with VCPU/EPT objects misplaced) | NativeScopeX or carry VT-x placement |
| `JThreadFinHypsU.obj` | ∀ JAtZ at th | no | yes | NativeScopeX |
| `KFinAtR.vt` / `VtAsidJ` | ∀ JAtZR at Z's sets | `th t = tcb` half yes (`thOfT`); asid half no | yes (a mapped vtable PML4 cap with asid 0) | JAtZ field |
| `JEntryAt.live` | ∀ ghosts H Cs Ac Lst D with JAtZ at (s,σ) | no | possibly: LiveDN at another heap H' that also satisfies JAtZ | restate at the carried ghosts |
| `JSched(C)Path.rest` | ∀ ghosts JAtZ | P1 facts | low risk (P1-true at every BlkOK) | prove from P1 (S) or keep |
| `hK`, `hFin` | ∀ ghosts at the budget/front outcome | — | same ghost issue | restate to the ghosts budget_ok/dispatch produce (`Z.mv Z.G V0, H, Cs, …`, KEntry7:198) |
| `ArchSwF`/`ArchNdF`/`SniHyp`/`SendHyp` | ∀ SchedRel states | — | check: an `assert`/`fail` in `archSwitchToThread`/`setNextInterrupt` at an unreachable SchedRel state would make them false; they state a single outcome | audit the spec defs (S); add `FpuOwnOK`-like guards if needed |
| `ArchIrqRel.map/mapr/mask`, `ARKeep`, `ArchRefines` | ∀ a (conditional on AR) | — | fine (pure arch) | keep |

**IrqPlatI.act in detail.** Its post never mentions FL4's returned line `r`. It says: at the JAt spec state σ,
whenever the spec's `getActiveIRQ true` returns `some i`, then `σ.interruptStates i ≠ .irqInactive`.
`getActiveIRQ` (Fl4Spec/Machine.lean:680) returns `some i` only if `¬ irqMasks i`. So `act` follows from
a spec-only invariant `ValidIrqMasks σ : ∀ i, σ.interruptStates i = .irqInactive → σ.machineState.irqMasks i = true`
(l4v `valid_irq_masks`), plus termination of `take_pending_irq` (from `IrqPlat.take`). No arch mask query and no
FL4 invariant are needed, contrary to sch12 (3)'s removal route. As stated (∀ JAt) it is false at JAt states that
violate valid_irq_masks, because JAt constrains no spec masks. Restate it as `ValidIrqMasks σ` in SInv, and prove
`act` per state (S).

Preservation of ValidIrqMasks:
* `setIRQState` is paired with `maskInterrupt` in IRQ control issue / handler clear / `deletingIRQHandler`
  (l4v `valid_irq_masks` lemmas);
* `getActiveIRQ` keeps the masks (it only bumps `irqState`).

`IrqPlat.take`'s own ∀σ problem (§0) remains and needs MR.

---------------------------------------------------------------------------------------------------------------

## 4. Order of work and target theorem

### Groups

**G0 (first, blocking; touches no JAtZ field):**
* (i) `MR` + `ValidMachineTime`. Restate PPPlat.now/irq, IrqPlat.take, PortInVal, NowAgree. Thread MR through
  the ~25 use sites. Until then every top theorem is vacuous. L, one line, single owner: it touches XTopJointPP,
  XTopJointPreempt and their cone.
* (ii) `dispatch_invokeJEPZRI` → drop `hRest` and `KPreFinRestHypI` (`kernel_entryJ8`). S, leaf modules only.

**G1 (spec-only SInv, parallel, no JAtZ cone):** new leaves `SpecInv*.lean` importing only Fl4Spec + SpecGlob/
ScCur/ScArchF definitions. One structure `SInv σ` with 10 fields:
* OffReady, CtNQR, VfhAll, FaultTcbs, SpecGlob, EpQAll, FpuOwnOK, DomListOK, ValidIrqMasks, ValidMachineTime,
* NativeScope (spec part).

It needs:
* per field, a boot lemma (Fl4Spec's init state);
* `kentry_sinv : SInv σ → ∀ y ∈ (fl4KernelEntrySyscall true c σ).1, SInv y.2`, via `syscall_post` / `fv_auto`
  shells per field;
* the same for `handleE` of interrupts and timer events if they are in the step relation.

Parallelisable into 3–4 agents by field:
* (vfh, cnf, NativeScope),
* (OffReady, ctnq, ValidMachineTime),
* (SpecGlob, epQ),
* (FpuOwnOK, DomListOK, ValidIrqMasks).

Size: L overall, M per agent. Builds are tiny (Fl4Spec cone only).

**G2 (one combined JAtZ extension, single owner, one cone rebuild):** add all joint (b) fields in ONE commit:
* flags, handlers, ports, vsTyp, liveDN (at its own ghosts), urz, utks, hno, bufObj, archFit, regionUnref,
  vsReach (at the state, for every RAM untyped region), devApart/devFree/devGpm, vtAsid, idxWord,
  nativeScopeX, cr3Rel.
* Make them a sub-structure `JAtZ.ext : JExt … s a σ`, so anonymous constructors change by ONE component.
  The ~hundreds of `⟨…⟩` JAtZ constructions get `J.ext.<keep lemma>` instead of 20 positional fields.
* JAtZR/JAtZS get the same single field.
* First commit: the field with a sorry-free frame lemma `JExt.frame` for steps that keep FL4 slots/objects and
  spec kheap (most steps). Then each producer site takes `J.ext.frame …`.

The 5500-module rebuild happens once for the field, then once per batch of leaf fixes. Preservation proofs for the
L items (live, vsTyp, regionUnref, vsReach, cr3Rel) go in new leaves that prove `JExt` keep lemmas per step. They
are parallel, split by step family:
* deletion loop (WJL already carries live: extend to the rest),
* retype/reset,
* VSpace,
* IPC/scheduler (frames only).

Rule for the lines: no one else edits JAtZ while G2 lands. Others work in leaves against the `JExt` interface
(fields + keep-lemma signatures), stubbed as hypotheses until G2 merges. Same pattern as `JDelParts`.

**G3 (wiring at the top; leaves):**
* replace every per-state [J] premise by a projection from `J.ext` / SInv (JEntryAt, KDispHypsRI.recv, KBudget.cur/off,
  KFinAtR.hd/vt/fo, hNS/hNSR/sigRest);
* `JAtZ.budgetOkTR` (B4 receiver case, M; reuse ScTmoCtRecv*);
* mid dispatch M1 (sch12 (2), L);
* CR3 tail F8 (L).

**G4: the induction.**
* Post of the top theorem: `RJ` (KPost) must give `JAtZ ∧ JExt` at the exit state. jat_finishJR already gives
  JAtZ after `activateJ`, so extend activateJ's post with JExt (frame) and `action = resume` (for Entered).
* SInv is kept by `kentry_sinv` and transported along the spec outcome chosen by KPost.

### Target statement

```lean
/-- Reachable states of the joint system: boot, then native syscalls. -/
inductive JReach (arI) (AR) : S → A → Fl4Spec.State Unit → Prop
  | boot : BootJ s a σ → JReach s a σ          -- JAtZ ∧ JExt ∧ SInv ∧ MR from the boot proof
  | step : JReach s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c → TrapClear s →
           (s', a') ∈ okOutcomes (syscall.handle_syscall st arI s a n) →
           ((), σ') ∈ (fl4KernelEntrySyscall true c σ).1 → RJ s' a' σ' → JReach s' a' σ'

/-- Invariant: every reachable state carries the bundle. -/
theorem jreach_inv : JReach s a σ → ∃ ghosts, JAtZ … s a σ ∧ JExt … s a σ ∧ SInv σ ∧ MR a σ.machineState

/-- Refinement at every reachable state. -/
theorem kernel_entry_reach (hPlat : PlatJ arI AR) :   -- the [P] facts, MR-relative, no ∀σ
    JReach s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c → TrapClear s →
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ∧ JInvAt r ⦄
```

`TrapClear` is the per-step [S] hflag (M2). `PlatJ` bundles T9–T13, T17–T18, the MR-relative IrqPlat/PPPlat,
ArchSwF/ArchNdF/Sni/Send and ArchIrqRel, all [P]. Boot (`BootJ`) is a separate L line: FL4 boot state vs the
spec's init state. It can start as a named [P]/[W] `BootJ` premise of `jreach_inv`.

### Top risks

1. **PPPlat.now is false (§0)**: everything above `XTopJointPP` that takes PPPlat is vacuous today. Fix in G0
   before anything else. The other ∀σ platform premises (IrqPlat.take, PPPlat.irq) silently make the IRQ paths
   vacuous.
2. **KBudget.tmo is false in reachable states** (receiver waiting on the timeout endpoint at entry): needs
   `budgetOkTR`.
3. **The JAtZ cone cost**: avoid by one `JExt` sub-structure (G2) plus spec-only SInv off-cone (G1). Do not add
   fields one at a time.
4. **L items with no existing machinery**: RegionUnrefAt/heapH, vsReach (valid_vs_lookup), vsTyp, the CR3 tail,
   and the mid dispatch (M1). These dominate the schedule.
5. **∀-ghost premises** (`live`, `hK`, `hFin`, `rest`): must be re-scoped to the carried ghosts, or the invariant
   cannot discharge them.
6. **SInv over the whole spec `callKernel`** is l4v-AInvs-sized. Use sch12's `syscall_post`/`fv_auto` frames so
   only the writers of each field need real proofs.

## Lead decision (2026-11-20, after ut1): the boot state and G4

ut1 found that the spec's boot state `initASt` holds only null caps, so no
state reachable from it has an untyped cap and every Untyped / AsidControl
MakePool invocation fails at the cap lookup. Reachability from `initASt` is
therefore too weak a base for G4 (it would make the Untyped paths vacuous).
Decision, following l4v (whose invariant proofs are stated over `invs`, with
the initial state an assumption): G4's induction starts from ANY spec state
satisfying the carried invariants `SInv` (plus `JExt` at J), not from
`initASt`. The `boot_*` lemmas against `initASt` stay as non-vacuity checks
of each field, nothing more. Every G1 field must be stated and proved for
arbitrary states (as ut1 did), never using facts that hold only because no
untyped caps exist. A concrete FL4 boot state (root task with its untyped
caps) satisfying `SInv` is a later non-vacuity task, [S] until then.
