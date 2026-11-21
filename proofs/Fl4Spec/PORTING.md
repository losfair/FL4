# Porting the seL4 abstract spec to Lean

`Fl4Spec` is the Lean port of seL4's Isabelle abstract specification, MCS
version (DESIGN.md §9, "The abstract spec"). Source: l4v branch `rt`,
checked out at `~/Projects/fl4-deps/l4v-rt` (commit f44de69), directories
`spec/abstract`, `spec/abstract/X64`, `spec/machine`, and the generated
executable-spec types these import (`spec/design/skel`, `spec/haskell`).

## Rules

- **Transliterate.** One Lean definition per Isabelle definition, in the
  same order, with the same structure. Do not optimise, merge or
  "improve". A reviewer must be able to compare the two side by side.
- **Cite the source.** Every definition's docstring starts with
  `l4v: <Theory>.<name>`. Every file starts with a comment naming the
  theories it ports.
- **Names.** Isabelle `snake_case` becomes Lean `camelCase` for functions
  (`set_thread_state` → `setThreadState`) and `UpperCamelCase` for types
  and constructors (`cap.EndpointCap` → `Cap.endpointCap`). Keep the
  Isabelle name recognisable.
- **Only what FL4 builds.** MCS paths only; x86_64 (X64) only. No IOMMU or
  IO page tables (`IOPageTable`, `IOSpace`, VT-d contexts), no VCPUs or
  EPT, no non-MCS definitions. Keep IO ports. Where an omission removes a
  case of a datatype, say so in a comment at the datatype.
- **FL4 differences** (per-core state, l4h extensions such as TCB timers,
  trapSyscalls, subframes) never go into ported modules. They go into
  `Fl4Spec/Ext/` later, on top of the port.
- **Monad.** `Fl4Spec.NonDet σ α` (l4v `nondet_monad`) and
  `Fl4Spec.NonDetE σ ε α` (l4v `('s, 'e + 'a) nondet_monad`), defined in
  `Fl4Spec/Monad.lean`. Add missing combinators there, each citing its
  l4v definition. `do` notation works for both.
- **Words.** `machine_word` / `word64` is `BitVec 64` (`Fl4Spec.Word`),
  `word32` is `BitVec 32`, etc. `nat` is `Nat`, `int` is `Int`. Isabelle
  `'a set` is `Set α`, `'a option` is `Option α`, partial maps
  `'a ⇀ 'b` are `α → Option β`, `'a list` is `List α`.
- **Underspecified machine operations** (l4v `MachineOps` with
  `machine_op_lift`, underlying machine state) stay underspecified: model
  them as nondeterministic or as fields of the machine state, as l4v does.
  Do not invent behaviour.
- **Records** become `structure`s; record update `s⦇f := v⦈` becomes
  `{ s with f := v }`.
- **Locales and arch overrides**: l4v's `Arch` locale and
  `arch_requalify` become plain definitions in the arch modules
  (`Fl4Spec/X64/*.lean`), imported where needed.
- **Every file must compile** with `lake env lean <file>` (after
  `lake build` of the modules it imports). No `sorry`, no `axiom`
  except for the underspecified machine (each such axiom/opaque with a
  comment saying which l4v constant it stands for).
- **Executable where deterministic.** Prefer computable definitions when
  the Isabelle one is deterministic and total; use `noncomputable` only
  when needed.

## Module map

| Lean module                  | l4v theories                                                         |
|------------------------------|----------------------------------------------------------------------|
| `Fl4Spec/Monad.lean`         | lib/Monads/nondet/Nondet_Monad                                       |
| `Fl4Spec/Machine.lean`       | Lib/Word_Lib helpers, Kernel_Config, spec/machine (X64/Platform, Time, MachineTypes, MachineMonad, X64/MachineOps), X64/Machine_A, MiscMachine_A |
| `Fl4Spec/Types.lean`         | CapRights_A, VMRights_A, ExceptionTypes_A, (Arch)InvocationLabels_H, InvocationLabels_A |
| `Fl4Spec/X64/Structs.lean`   | X64/ArchVMAttributes_A, Structs_B, X64/Arch_Structs_B, X64/Arch_Structs_A |
| `Fl4Spec/Structures.lean`    | Structures_A                                                         |
| `Fl4Spec/Deterministic.lean` | List_Lib helpers, Deterministic_A, Exceptions_A (KHeap_A imports them) |
| `Fl4Spec/KHeap.lean`         | KHeap_A, X64/ArchVSpaceAcc_A                                         |
| `Fl4Spec/CSpaceAcc.lean`     | CSpaceAcc_A, Sporadic_A                                              |
| `Fl4Spec/Invocations.lean`   | X64/ArchInvocation_A, Invocations_A                                  |
| `Fl4Spec/Retype.lean`        | X64/ArchRetype_A, X64/ArchIpcCancel_A, Retype_A                      |
| `Fl4Spec/X64/VSpace.lean`    | X64/FPU_A, X64/ArchVSpace_A, X64/ArchCSpace_A                        |
| `Fl4Spec/TcbAcc.lean`        | TcbAcc_A                                                             |
| `Fl4Spec/IpcCancel.lean`     | IpcCancel_A                                                          |
| `Fl4Spec/SchedContext.lean`  | SchedContext_A                                                       |
| `Fl4Spec/CSpace.lean`        | CSpace_A                                                             |
| `Fl4Spec/X64/Arch.lean`      | X64/Arch_A                                                           |
| `Fl4Spec/Schedule.lean`      | Schedule_A                                                           |
| `Fl4Spec/Tcb.lean`           | X64/ArchTcb_A, Tcb_A, X64/ArchFault_A                                |
| `Fl4Spec/Ipc.lean`           | Ipc_A                                                                |
| `Fl4Spec/Interrupt.lean`     | X64/ArchInterrupt_A, Interrupt_A                                     |
| `Fl4Spec/Decode.lean`        | X64/ArchDecode_A, Decode_A                                           |
| `Fl4Spec/Init.lean`          | X64/Init_A (MCS fields from RISCV64/Init_A); KernelInit_A not ported |
| `Fl4Spec/Syscall.lean`       | Event_H (`Event`, `Syscall`), X64/Hypervisor_A, Syscall_A            |

The single entry point of the port is `Fl4Spec.callKernel` (l4v Syscall_A
`call_kernel : event ⇒ (unit, 'z) s_monad`); the dummy initial state is
`Fl4Spec.initASt` (X64 Init_A `init_A_st`).

The order is the MCS import graph of l4v `rt` (taken from RISCV64, since
the X64 theories on `rt` still carry the non-MCS imports): KHeap_A →
CSpaceAcc_A → Sporadic_A → ArchInvocation_A/Invocations_A → ArchRetype_A,
ArchIpcCancel_A → Retype_A → FPU_A → ArchVSpace_A → ArchCSpace_A → TcbAcc_A
→ IpcCancel_A → SchedContext_A → CSpace_A → Arch_A → Schedule_A → ArchTcb_A
→ Tcb_A → ArchFault_A → Ipc_A → ArchInterrupt_A → Interrupt_A →
ArchDecode_A → Decode_A → Syscall_A (which also imports Event_H, Init_A and
Hypervisor_A). X64 Init_A only needs Retype_A; nothing up to Tcb needs it
(see Deviations).

Split a module into several files if it grows past about 1500 lines; keep
the theory order.

## Encodings

Conventions of the ported base layer that later modules rely on.

- **Namespace.** Everything is in `Fl4Spec`, flat: arch (`X64_A`, `X64_H`,
  `X64`) and generic names share it. Where a camelCase name would clash, the
  l4v name stays: `pptr_base` (Machine_A) vs `pptrBase` (Platform),
  `msg_info_register`, `msg_registers`, `cap_register`, `badge_register`,
  `frame_registers`, `gp_registers`, `exception_message`, `syscall_message`
  (Machine_A) vs the Haskell `msgInfoRegister` etc.; `Platform.Cr3`
  (Platform `cr3`) vs `Cr3` (Arch_Structs_A `cr3`); `parseTimeArgA`
  (Arch_Structs_A `parse_time_arg`) vs `parseTimeArg` (Arch_Structs_B).
  Datatype selectors that Isabelle generates (`acap_rights`, `pte_frame`,
  `ep_queue`, `the_arch_cap`, ...) are explicit functions in the type's
  namespace (`ArchCap.acapRights`, `Endpoint.epQueue`), `undefined` on the
  other constructors.
- **Decidability.** Every file has `open Classical` and `noncomputable
  section`; tests on `Set`s, `∃` and equality of caps use classical
  decidability. Isabelle `bool` functions are `Bool` when the spec computes
  with them (`runnable`, `schedulable`, `scActive`, `refillReady`,
  `isCnodeCap`, `inReleaseQueue`, `isCurDomainExpired`) and `Prop` when they
  are quantified statements (`isBlockedOnReceive`, `wellFormedCnodeN`,
  `validSchedContextSize`, `isSimpleType`, `validList2`).
- **Partiality.** Isabelle `undefined`, `the`, `THE`, `partial_inv`,
  nonexhaustive `primrec`/`case` are `Fl4Spec.undefined` (a fixed
  unspecified value, `Classical.choice`), `Fl4Spec.the`, `Fl4Spec.The`,
  `Fl4Spec.partialInv`, and an explicit `| _ => undefined` case. `hd`,
  `last` and `xs ! i` are `the xs.head?`, `the xs.getLast?`, `the xs[i]?`.
- **Maps.** Partial maps are `α → Option β`; `f(x := v)` is
  `Function.update f x v`; `dom`/`ran` are `Fl4Spec.dom`/`Fl4Spec.ran`.
  `opt_map` (`|>`), `opt_map_Some` (`||>`), `opt_pred` (`|<`) are `optMap`,
  `optMapSome`, `optPred` (Lean's `|>` is the pipe).
- **State.** `AbstractState` is l4v `abstract_state`; `State Z` extends it
  with `exst : Z` (`'z state`). `[StateExt Z]` is l4v `'z::state_ext`, with
  instances for `DetExt` (deterministic spec: `workUnitsCompletedInternal`,
  `cdtListInternal`) and `Unit`. MCS scheduler state is in `AbstractState`
  (`readyQueues : Domain → Priority → List ObjRef`, `releaseQueue`,
  `schedulerAction`, `curSc`, `curTime`, `consumedTime`, `reprogramTimer`,
  `domainList`, `domainIndex`, `domainStartIndex`, `curDomain`,
  `domainTime`); only the CDT sibling lists and the work units are in
  `DetExt`. `kheap : ObjRef → Option KernelObject`; `cdt : CslotPtr → Option
  CslotPtr`; `CslotPtr = ObjRef × List Bool`. CNode contents are
  `List Bool → Option Cap`; TCB slots are `tcbCnodeIndex n` (3-bit
  big-endian bit lists) via `tcbCnodeMap`.
- **Monads.** `SMonad Z α`, `FMonad`, `SEMonad`, `LFMonad`, `PMonad` (Exceptions_A)
  are `NonDet (State Z) α` and `NonDetE (State Z) ε α`. The reader option
  monad (`r_monad`, `lookup`) is `Lookup σ α = ReaderT σ Option α`
  (`RMonad Z α`). In `do` blocks write `x ← pure e` for l4v `x ← return e`
  and `pure ()` for a non-final `return ()`: Lean's `return` exits the whole
  block.
- **Words.** `mask`, `ucast`, `unat`, `testBit` (`!!`), `toBl`, `ofBl`,
  `wordRcat`, `wordRsplit`, `uptoEnum` (`[a .e. b]`), `uptoEnumStep`
  (`[a, b .e. c]`), `assocs`, `intUpto` (`[i..j]` on int) are in Machine.
- **Constructors and fields** are lowerCamelCase (`Cap.endpointCap`,
  `Register.rax`, `VMPageSize.x64SmallPage`, `Tcb.tcbSchedContext`,
  `AbstractState.curThread`).

- **Record updates.** Isabelle's generated `f_update` functions, passed as
  arguments to `set_tcb_obj_ref`, `set_sc_obj_ref`, `set_ntfn_obj_ref`,
  `set_reply_obj_ref` and `update_sched_context`, are explicit functions in
  Structures (`tcbSchedContextUpdate`, `scRefillsUpdate`, `ntfnScUpdate`,
  `replyScUpdate`, ...). Add more there as needed. A record update written
  inline in the spec (`s⦇reprogram_timer := True⦈`, `r⦇r_amount := x⦈`) is
  `{ s with ... }`.
- **Datatype discriminators** (`is_WaitingNtfn`) are `Bool` functions in the
  type's namespace (`Ntfn.isWaitingNtfn`); `is_ArchObjectCap` is the existing
  `isArchCap`. Datatypes holding caps (`Invocation`, `TcbInvocation`,
  `RecDelCall`, ...) derive only `Inhabited` (caps have no `DecidableEq`).
- **Prop vs Bool, continued.** Cap predicates that compare caps or
  quantify are `Prop`: `sameRegionAs`, `sameObjectAs`, `sameAobjectAs`,
  `archSameRegionAs`, `shouldBeParentOf`, `isCapRevocable`,
  `archIsCapRevocable`, `shouldBeArchParentOf`, `capRemoveable`,
  `capCyclicZombie`, `hasCancelSendRights`, `isValidVtableRoot`,
  `inUserFrame`, `isFinalCap'`, `isHighestPrio`, `isAligned`,
  `canMergeRefill`. Case functions are `Bool`: `isPhysical`,
  `archIsPhysical`, `isIrqControlDescendant`, `longRunningDelete`,
  `canFastFinalise`, `checkMappingPptr`, `isDeviceUntypedCap`. Monadic
  results the spec branches on are `Bool` (`isFinalCap`, `isRoundRobin`,
  `refillFull`, `noReplyInTs`, the `r_monad` readers); `cap_insert` turns its
  `Prop`s into `Bool` with `decide`.
- **Loops.** l4v `whileLoop (λ_ s. the (f s))` with an `r_monad` condition is
  `NonDet.whileLoop (fun _ s => the (f s) = true)`.
- **List idioms.** `[a ..< b]` is `List.range' a (b - a)`; `[a ..< Suc b]`
  is `List.range' a (b + 1 - a)`; `butlast` is `List.dropLast`; `removeAll`
  is `Fl4Spec.removeAll` (IpcCancel); `xs[i := v]` is `List.set`; the list
  comprehension `[i ← xs. P i]` is `xs.filter (decide ∘ P)`; prefix `≤` on
  lists (HOL-Library.Prefix_Order) is `<+:`; Isabelle `Max S` is
  `Fl4Spec.setMax S` (Machine); `the_index` is `theIndex`; `the_pred_option P`
  is `partialInv P true`; `ptr_add` is `ptrAdd`; `is_aligned` is
  `isAligned`.
- **Partial recursive functions.** Isabelle `function`s without a
  termination proof (`rec_del`, `cap_revoke`) are `NonDet.lfp` of a
  functional (`recDelF`, `capRevokeF`) that transliterates the equations with
  the recursive calls as a parameter. Terminating ones (`resolve_address_bits'`)
  use Lean well-founded recursion on the Isabelle measure; the `let` of the
  recursion argument replaces `← returnOk` so the measure proof can see it.
- **Nested `do` results.** Inside a nested `do` used as a value
  (`return_now ← do ...` in `sched_context_yield_to`) write `pure`, never
  `return`.
- **`mapME`** is `NonDetE.mapME` (Monad). Isabelle `undefined` at a monadic
  type (a nonexhaustive `case cap of ThreadCap p ⇒ returnOk p` in
  `decode_read_registers`) is `Fl4Spec.undefined` via the `Nonempty
  (NonDetE σ ε α)` instance (Monad); the witness is irrelevant.
- **Sum results.** Where the spec binds the `'e + 'a` result of an
  exception computation in the plain monad (`r_fault ← without_preemption $
  m_fault` in `syscall`, the `handle_event ev <handle> ...` statement of
  `call_kernel`), the Lean code binds `ExceptT.run m` and matches on
  `.error`/`.ok` (or discards it). `<handle>` is `NonDetE.handleE`.
- **Enumerations of labels.** `[CNodeRevoke .e. CNodeRotate]` on
  `gen_invocation_labels` is `GenInvocationLabels.uptoEnum` (Decode), defined
  as Enumeration's `map toEnum [fromEnum a ..< Suc (fromEnum b)]` over
  `GenInvocationLabels.enum` (l4v's order; see "Invocation label numbers"
  for FL4's).
- **Word intervals.** `{a..b}` on words is `{x | a ≤ x ∧ x ≤ b}` (unsigned
  `BitVec` order), as in `detype` and `is_ioport_range_free`.
- **Recursion arguments that change** (`transfer_caps_loop`'s `n`) go after
  the colon, so structural recursion on the list sees them; the partially
  applied recursive call is bound with `← returnOk` as in Isabelle.
- **Nested exception blocks** whose type Lean cannot infer (an `if` or
  `match` bound with `←`, a `doE` passed to `const_on_failure` or `<catch>`)
  carry a type ascription (`(... : SEMonad Z Cap)`, `show FMonad Z Unit
  from do ...`).
- **Match statements in `do`.** A non-final Isabelle `case ... ;` is a Lean
  `match` statement whose arms are `SMonad Z Unit` (`| none => pure ()`),
  followed by the rest of the block at the outer indentation. Put a
  multi-line argument on its own lines, indented past the function name, or
  Lean parses it as a new statement.

## Deviations

- **X64 is not MCS on l4v `rt`.** The X64 machine and arch theories on the
  `rt` branch are the non-MCS ones. Taken from RISCV64 on `rt` (the 64-bit
  architecture without hypervisor), with X64 values from the C kernel where
  they differ, each marked "rt X64 gap": `time_state` and
  `last_machine_time` in `machine_state`, `time_oracle`, `getCurrentTime`,
  `setDeadline`, `deadlineIRQ`, `ackDeadlineIRQ`, `timerIRQ` (= 125, C
  `irq_timer`), `replyRegister` (R12), `nbsendRecvDest` (R13),
  `timeoutMessage` (C `TIMEOUT_REPLY_MESSAGE`), `arch_cap_badge`,
  `reply_bits` (5), `parse_time_arg`, `words_from_time`; `ntfn_bits` is the
  MCS value 6, not X64's non-MCS 5.
- **FL4 extension, 20-bit ASIDs** (DESIGN.md §3): `asid_high_len` is 11
  (2048 ASID pools) and `asid_len` 20; l4v has 3 and 12. `cr3_addr_mask`
  keeps the 12-bit PCID field (l4v writes `asid_bits` for it), and
  `x64_asid_table` is indexed by `asid_high_index` (l4v writes `3 word`).
- **FL4 extension, the EPT-root TCB slot** (VT-x/AMD-V, README.md
  "x86 virtualization"): a TCB has six cap slots; the sixth, `tcbEpt`, holds
  the thread's EPT root, as in seL4's C with `CONFIG_VTX`. l4v's x64 TCB has
  five. `tcbCnodeMap` maps index 5 to it, and `finalise_cap` of a final
  thread cap returns a zombie of 6 slots (l4v: 5).
- **Kernel_Config** is generated from a C build; here `numDomains` is an
  unspecified constant (`opaque kernelConfig`) constrained by exactly the
  facts of `Kernel_Config_Lemmas`; `config_HAVE_FPU` is `true` (x86-64).
- **Time.thy's `consts` + `axiomatization`** (`kernelWCET_us`,
  `ticks_per_timer_unit`, `timer_unit` and their ten axioms) are one opaque
  structure `timeConsts`, inhabited by the witness of Time.thy's consistency
  `notepad`; the axioms are theorems projected from it. No Lean `axiom`.
- **FL4 extension/config: `MAX_PERIOD_US`** is a platform constant (a field
  `maxPeriodUs` of `timeConsts`), C's default `getMaxUsToTicks()/8`
  (`KernelStaticMaxPeriodUs = 0`, include/kernel/sporadic.h); l4v fixes it
  at 1 hour. The witness keeps the hour.
- **`typedecl machine_state_rest`** is an opaque nonempty type.
- **`next_not_child`** (`function (domintros)`, partial) is `THE` of its
  inductively defined graph, as Isabelle's function package defines it.
- **`upto_enum` on words** uses l4v's lemma `upto_enum_word`
  (`map of_nat [unat a ..< Suc (unat b)]`) as its definition.
- **Not ported:** lemmas, `translations`, the Haskell `FPUState` synonym
  (unused), `MiscMachine_A.ipa_size` (ARM-only config), the VT-d
  declarations left in X64 Arch_Structs_A and ArchVSpaceAcc_A (no IOMMU).
- **Module map:** Deterministic_A and Exceptions_A moved before KHeap
  (`Fl4Spec/Deterministic.lean`), since KHeap_A imports them.
- **Chunk A (CSpaceAcc_A … ArchFault_A) rt X64 gaps:**
  - X64 `Arch_A` on `rt` imports TcbAcc_A but uses `cap_insert` and
    `max_free_index_update` from CSpace_A, and `Schedule_A` uses
    SchedContext_A; the X64 import graph on `rt` is the non-MCS one and does
    not build. The MCS order of RISCV64 `rt` is used, so IpcCancel_A,
    SchedContext_A and CSpace_A are ported before Arch_A (module map).
  - `idle_sc_ptr` (RISCV64 Machine_A, `pptr_base + 0x3000`) is
    `idleScPtr = kernel_base + 0x7000` in Machine: X64 Init_A puts the 8KiB
    IRQ node at `kernel_base + 0x2000` and the global paging structures up to
    `kernel_base + 0x6000`. IpcCancel_A imports Init_A only for it, so
    X64/Init_A is not a prerequisite of IpcCancel here. **FL4 deviation:**
    the operations read the state field `idleSc` (next to `idleThread`)
    instead of the constant: FL4 is multi-core with one idle SC per core,
    placed at boot in a `.bss` array, and the spec is a per-core view, so
    `idleSc` is that core's idle SC; `idleScPtr` is only its initial value
    in `initASt`.
  - `timerPrecision` (RISCV64 Arch_Structs_B, Haskell `usToTicks 1`) is in
    X64/Structs; the C kernel's x86 `getTimerPrecision` is `usToTicks(1)`.
  - `make_arch_fault_msg` uses label 6 (C x86 `seL4_Fault_VMFault` with
    `CONFIG_KERNEL_MCS`, RISCV64 `rt`), not X64 `rt`'s non-MCS 5.
  - No other MCS-specific arch definition differs: RISCV64 `rt`'s
    ArchVSpace_A, ArchCSpace_A, ArchRetype_A, ArchIpcCancel_A, ArchTcb_A and
    Arch_A have the same set of definitions as X64's.
- **Kernel_Config `resetChunkBits`** is a field of `kernelConfig` (C default
  8, unspecified here; l4v states no lemmas about it).
- **`rec_del`, `cap_revoke`** (partial `function`s) are least fixed points
  (`NonDet.lfp`): equal to Isabelle's definition on its domain (where l4v's
  proofs use them); outside it Isabelle's value is unspecified and the lfp
  is the partial-correctness value (results of terminating runs, failure
  only if a terminating run fails). The monotonicity of the functionals is
  not proved.
- **`resolve_address_bits'`** drops the `'z itself` argument (it only fixes
  the state type) and binds `rest` with `let` (for the termination proof)
  instead of `← returnOk`.
- **`update_cap_data`**: Isabelle `size guard''` (the word length of a
  `data` word) is the literal 64.
- **Not ported:** lemmas (`fast_finalise_def2`, `rab_termination`,
  `sc_with_reply_def2`, `msg_align_bits`), Sporadic_A's `thm` checks, the
  CSpaceAcc_A notations (plain `parentOf`, `parentOfTrancl`,
  `parentOfRtrancl` instead). IOMMU: `PageIOMap`, `io_pt_invocation`,
  `InvokeIOPT`, and the IOSpace/IO page table cases of `arch_derive_cap`,
  `arch_finalise_cap`, `arch_same_region_as` (commented out in l4v).
- **Chunk C (Ipc_A … Syscall_A, Init_A):**
  - **Fix in chunk A, rt X64 gap:** X64 `rt` `lookup_ipc_buffer` reads the
    non-MCS slot `tcb_cnode_index 4`; in the MCS TCB that slot is the timeout
    handler and the IPC frame cap is at `tcb_cnode_index 2` (`tcb_cnode_map`,
    C MCS `tcbBuffer = 2`). `lookupIpcBuffer` (X64/VSpace) now uses 2, as
    RISCV64 `rt` does.
  - **X64 Init_A** on `rt` is non-MCS (idle TCB with `tcb_reply`,
    `tcb_caller`, `tcb_time_slice`, a `cap_ref` fault handler; no time or SC
    fields). `initKheap` and `initASt` take the idle TCB, the idle scheduling
    context at `idle_sc_ptr` and the MCS state fields from RISCV64 `rt`
    Init_A; the X64 layout and `init_arch_state` are X64's.
  - **`idle_sc_ptr`** stays `kernel_base + 0x7000` (Machine): the C kernel has
    no fixed address (`ksIdleSC = &ksIdleThreadSC`, a BSS array aligned to
    `seL4_MinSchedContextBits`), and l4v's MCS architectures all use
    `idle_thread_ptr + 0x2000`, which on X64 is inside the 8KiB IRQ node
    (`kernel_base + 0x2000 .. 0x3fff`); 0x7000 is the first free page after
    the global paging structures.
  - **KernelInit_A is not ported.** l4v marks it "FIXME: unused, out of
    date" and comments it out of `spec/ROOT` (it does not build); it is an
    ARM32/iMX31 boot model (32-bit words, `tcb_reply`, `tcb_caller`,
    `arm_global_pd`, `CPSR`, `ARMSection`) with no X64 or MCS counterpart.
    The proofs use Init_A's `init_A_st` instead (`KernelInit_AI`).
  - **Hypervisor_A**: X64 `handle_hypervisor_fault` (the only case,
    `X64NoHypFaults`, does nothing) is in Syscall; no VCPU code exists.
  - **Event_H**: `Event` and `Syscall` are ported from the Haskell
    (`#INCLUDE_HASKELL SEL4/API/Syscall.lhs ONLY Event Syscall`); Haskell
    `Int` (`UnknownSyscall`) is Isabelle `nat`.
  - **Kernel_Config `retypeFanOutLimit`** (C `CONFIG_RETYPE_FAN_OUT_LIMIT`,
    default 256, a `machine_word` in l4v's generated Kernel_Config) is a field
    of `kernelConfig`, unspecified. `alignUp` (Word_Lib More_Word_Operations)
    is in Machine.
  - **Omitted (no IOMMU):** ArchDecode_A's commented-out VT-d decoders
    (`pci_request_id_from_cap`, `decode_io_pt_invocation`,
    `decode_io_frame_map_invocation`, `decode_io_map_invocation`) and the
    cancelled `VMIOSpaceMap`/`X64PageMapIO` branches of
    `decode_page_invocation`. `decode_io_unmap_invocation` (an l4v `X64STUB`,
    `undefined`), `page_cap_set_vmmap_type` and `get_iovm_rights` are live
    l4v definitions and are ported.
  - **ArchInterrupt_A, ArchDecode_A** on X64 `rt` have no MCS-specific
    content (RISCV64 `rt` differs only in machine operations and in
    `arch_check_irq`'s range check), so they are ported as they are.

## FL4 differences

FL4's differences from l4v are modules of `Fl4Spec/Ext/` on top of the
port; the ported modules are not changed. Each module's header gives the
details.

- **`Ext/TcbSize`: 4 KiB TCBs.** `decodeUntypedInvocationWith`,
  `retypeRegionWith` and `invokeUntypedWith` are l4v's untyped functions
  with `obj_bits_api` as a parameter (`objBitsApi` gives l4v's, by `rfl`);
  FL4's are `fl4DecodeUntypedInvocation` and `fl4InvokeUntyped`
  (`fl4ObjBitsApi`, 12 bits for `TCBObject`).
- **`Ext/IrqControl`: IRQControl.** `IRQIssueIRQHandler` for the ISA IRQs
  without an IOAPIC (`fl4ArchCheckIrq`), and the l4h label
  `IRQIssueIRQHandlerIOAPICRemapped`: `decodeFl4IrqControl`,
  `invokeFl4IrqControl`, with the invocations `Fl4IrqControlInvocation`.
- **`Ext/VSpace`: l4h VSpace extensions** (PML4 flush, TestAndClearAccessed,
  DeriveSubframe), as separate decoders and invocations.
- **`Ext/Tcb`: FL4's TCB extensions**, modelled on FL4's Rust
  (`tcb.rs`): seL4's debug API (`TCBSetBreakpoint`, `TCBGetBreakpoint`,
  `TCBUnsetBreakpoint`, `TCBConfigureSingleStepping`; not in l4v), l4h's
  FPU transfer (`TCBReadFPU`, `TCBWriteFPU`) and timer (`TCBSetTimer`),
  and FL4's `TCBSetFlags`. The decoders are FL4's checks in FL4's order;
  FL4 reads these arguments whatever the message length, which
  `fl4GetMr` (FL4's `syscall_arg` on the spec's state) models. The debug
  registers, the FPU image and the l4h timer queue are not in the model:
  those invocations change no state but the frame ReadFPU writes (any
  machine state) and, for SetTimer, `reprogram_timer`, which may be set
  (never cleared): FL4 sets its reprogram flag when the new deadline is
  the core's earliest, and the queue that decides this is not modelled.
  ConfigureSingleStepping with an instruction count of 0 clears the
  target's trap flag (bit 8 of its `FLAGS` register), as FL4 and seL4's
  x86 `configureSingleStepping` do; the debug-register state is not
  modelled. Their replies are any value of the right shape.
  FL4's SetFlags differs from l4v's: the `TRAP_SYSCALLS` flag (l4h) is not
  an l4v `TcbFlag`, so it is not kept and the reply is any word of the new
  flags, and an enabled FPU is not restored lazily
  (`arch_post_set_flags`'s `lazy_fpu_restore`).
- **`Ext/ReplyError`: the error reply with seL4's
  `CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC`** (FL4's
  `KERNEL_INVOCATION_REPORT_ERROR_IPC`, set in the debug profile; l4v's
  verified configuration leaves it off). `fl4ReplyFromKernelError reportError`
  is l4v's `reply_from_kernel` when `reportError` is false (by `rfl`); when it
  is set and the caller has an IPC buffer, it also clears the low 8 bits of
  buffer word `DEBUG_MESSAGE_START + 1` (`debugMessageStart`, 6) and counts
  that word in the reply's length. `fl4HandleInvocationR reportError` is
  `fl4HandleInvocation` with this error reply (by `rfl` for `false`).
- **`Ext/Invocation`: the invocation dispatcher.** `fl4DecodeInvocation` and
  `fl4PerformInvocation` are `decode_invocation` (Decode_A) and
  `perform_invocation` (Syscall_A) with exactly four substitutions:
  untyped caps use `fl4DecodeUntypedInvocation` / `fl4InvokeUntyped`; the
  IRQControl cap uses `decodeFl4IrqControl` / `invokeFl4IrqControl`; arch
  caps use `fl4ArchDecodeInvocation` / `fl4ArchPerformInvocation`, which are
  `arch_decode_invocation` / `arch_perform_invocation` except that the l4h
  VSpace labels go to the `Ext/VSpace` decoders and invocations
  (`X64PML4Flush` on a PML4 cap; `Page_DeriveSubframe` and
  `Page_TestAndClearAccessed` on a frame cap). Their invocation type
  `Fl4Invocation` is l4v's `invocation` with `InvokeIRQControl` carrying an
  `Fl4IrqControlInvocation` and `InvokeArchObject` an `Fl4ArchInvocation`
  (l4v's arch invocations and the l4h ones); thread caps use
  `fl4DecodeTcbInvocation`, which is `decode_tcb_invocation` except that
  `TCBSetFlags` and the `Ext/Tcb` extension labels go to their decoders,
  with the invocation `InvokeFl4TCB` (`invokeFl4Tcb`). Every other cap goes
  to l4v's decoder and invocation, unchanged.
  `fl4HandleInvocation` is `handle_invocation` (Syscall_A) with this
  dispatcher, unchanged otherwise.
- **`Ext/Timer`: FL4's TCB timers** (l4h 0003, `TCBSetTimer`). At every
  kernel exit FL4's `sched::schedule` first fires the expired TCB timers
  (`sched::awaken` → `timer::fire`, at most 32 per entry): each signals its
  thread's bound notification, if any, with the timer's badge, and sets the
  reprogram flag. l4v has no such timers. The timer tree is not modelled (as
  for `TCBSetTimer`), so `fl4Awaken` is nondeterministic: any finite
  sequence (`fl4TimerFires`) of fired timers (`fl4TimerFire`: no signal or
  one l4v `send_signal` (`fl4TimerSignal`), then `reprogram_timer := true`).
  It does not fail. `Ext/Entry`'s `fl4CallKernel` runs it before `schedule`.
- **`Ext/Entry`: the kernel entry with FL4's dispatcher.**
  `fl4HandleEvent rep` is `handle_event` (Syscall_A) with
  `handle_invocation` replaced by `fl4HandleInvocationR rep` (the
  substitution of `Ext/Invocation` and `Ext/ReplyError` one level up); its
  `match` on the syscall is `fl4HandleSyscall rep`, and the non-syscall
  events are l4v's (`fl4HandleEvent_other`, by `rfl`). `fl4CallKernel rep`
  is `call_kernel` with `fl4HandleEvent rep` and `Ext/Timer`'s `fl4Awaken`
  before `schedule`. `fl4KernelEntrySyscall rep c`
  is the syscall entry: the current thread's `FaultIP` register :=
  `NextIP - 2` (`fl4SyscallFaultIP`; the `syscall` instruction is two bytes),
  then `fl4CallKernel rep (.syscallEvent c)`. l4v's `call_kernel` has no
  such write: ADT_A's `kernel_entry` installs a user context in which the
  C kernel's entry has already done it (`thread_set (tcb_arch :=
  arch_tcb_context_set tc)`); FL4's `handle_syscall` does it itself, and the
  register matters because `activate_thread` restarts a `Restart` thread at
  `FaultIP` (`getRestartPC`). FL4's `TRAP_SYSCALLS` flag (l4h) and its
  debug/TLS syscalls (`handle_unknown_syscall`) have no branch here yet.
- **`Ext/Virt*`: x86 virtualization** (VT-x and AMD-V, one spec with the
  backend `virtKind` as a platform constant; design and proof plan in
  `proofs/VIRT-PLAN.md`). `VirtBackend`: the backend and the
  underspecified capability words; `VirtFields`: per-backend VCPU field
  tables with readable / writable / guest-changed classes; `VirtSanitize`:
  FL4's sanitize policy as pure functions; `VirtState`: the abstract VCPU
  (`VcpuState`), the extension state `VirtExt` and `VState Z`, VCPU
  initialisation, VMEnter staging and its report; `VirtEpt`: the guest
  page-table entry format and walk; `VirtGuest`: the guest-execution
  oracle `GuestStep` (l4v `do_user_op` style), the trusted layer's [P]
  contract shapes and the P3x statement shape. The invocations follow in
  later modules.
- **Invocation label numbers** (a deliberate deviation from l4v). l4v's
  `invocation_type` numbers labels by the Haskell `Enum` of
  `invocation_label` (l4v's labels only, generic then arch). FL4's ABI
  (`fl4_abi::label`, generated by `crates/fl4-abi/build.rs` from
  `interfaces/object-api*.xml` in seL4's generator order, the x86-64
  configuration with the hardware debug API) has labels l4v does not: seL4's
  debug API (`TCBSetBreakpoint` .. `TCBConfigureSingleStepping`, 16..19),
  FL4's `TCBReadFPU`, `TCBWriteFPU`, `TCBSetTimer` (22..24), `X86PML4Flush`
  (46), the VCPU MSR labels (49, 50), `X86PageDeriveSubframe` and
  `X86PageTestAndClearAccessed` (57, 58), `X86PageMapEPT` (60), and from 72
  on `X86IRQIssueIRQHandlerIOAPICRemapped`, the VCPU and EPT labels,
  `TCBSetEPTRoot` and `UntypedRetypeShared`. So `InvocationLabel.fromEnum`
  and `toEnum` (Types) number by `InvocationLabel.fl4Numbering`, FL4's
  numbers, and `invocationType`'s text is l4v's. The label types
  (`GenInvocationLabels`, `ArchInvocationLabel`, `InvocationLabel`) and
  `InvocationLabel.enum` are l4v's: l4v's labels keep their relative order
  in FL4's numbering (with gaps), so `GenInvocationLabels.uptoEnum` (over
  `GenInvocationLabels.enum`) is unchanged; its two ranges,
  `[CNodeRevoke .e. CNodeRotate]` (FL4 25..32) and `[CNodeCopy .e.
  CNodeMutate]` (28..31), are contiguous in FL4's numbering too, so they
  name the same labels. The l4h labels are numbered as FL4 numbers them:
  `fl4RemappedLabel` (72), `fl4Pml4FlushLabel` (46),
  `fl4DeriveSubframeLabel` (57), `fl4TestAndClearLabel` (58),
  `fl4TcbExtLabelNum` (SetBreakpoint 16, GetBreakpoint 17, UnsetBreakpoint
  18, ConfigureSingleStepping 19, ReadFPU 22, WriteFPU 23, SetTimer 24).
  The other FL4-only labels decode as `InvalidInvocation`. P3's
  FrontEndLabel proves, for every `fl4_abi::label` constant, the label the
  spec decodes it to, so a renumbering of the ABI fails the proof build. A
  release build (no hardware debug API) numbers differently; the spec
  follows the extracted (debug) configuration.
## Platform constants

FL4 fixes some of Kernel_Config's unspecified constants at build time. The
refinements take them as hypotheses (nothing in `Fl4Spec` changes):

- **`numDomains` = 1** (`fl4_abi::config::NUM_DOMAINS`); `DomConfig` in
  `Fl4Proofs/P3/DomDecode.lean`.
- **The domain schedule has `NUM_DOMAIN_SCHEDULES` = 2 entries**: the
  length of `domain_list` (part of the domain relation `DomRel`).
- `timeArgLen` is 1 and `maxDomainDuration` is `2^56 - 1` (FL4's
  `domain::MAX_DURATION`) on x86-64 already, by their definitions.
