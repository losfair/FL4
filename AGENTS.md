# FL4 — agent rules

FL4 is a Rust re-implementation of the seL4 17.0 microkernel (MCS API) with SMP and fine-grained locking, with
Lean 4 proofs of its core. `README.md` has the layout, tasks and platform notes; `DESIGN.md` is the authoritative
design (§5 architecture, §6 the verified core, §7 locking, §9 proof plan, §12 testing); `TRUSTED` lists the trusted
base. This file holds what you must not get wrong.

## Layout

- `crates/fl4-core` — every kernel decision, safe Rust, extracted by Charon + Aeneas into `proofs/Fl4Core/`
  (`Funs.lean`, `Types.lean`; `FunsExternal.lean` is the hand-written trusted interface). Its AArch64 slice
  `crates/fl4-core/src/arch/aarch64` is not extracted (x86_64 only).
- `crates/fl4-abi` — ABI numbering generated from `interfaces/` (seL4's XML pruned to FL4's configuration plus FL4
  methods, `xtask/scripts/prune_interfaces.py`) and the build configuration.
- Kernels and boot: `crates/fl4-kernel` + `crates/fl4-arch-x86_64` (x86_64), `crates/fl4-kernel-aarch64` +
  `crates/fl4-arch-aarch64` (AArch64), `crates/fl4-efi` / `crates/fl4-bootinfo` (UEFI loader, boot protocol).
- `crates/fl4-sync`, `crates/fl4-store` (transaction runtime, object store), `crates/fl4-sim` (deterministic
  simulator).
- `proofs/` — Lean 4 + mathlib lake project: `Fl4Core/` (extracted), `Fl4Spec/` (l4v abstract spec ported),
  `Fl4Proofs/` (`P0` totality, `P1` invariants, `P2` transactions, `P3` refinement).
- `libsel4/`, `cmake/` (drop-in `kernel` dir for seL4 CMake projects), `fl4test/` (FL4's own tests),
  `vendor/seL4` (pinned upstream, a git submodule), `xtask/` (all tasks; scripts in `xtask/scripts/`).

## Rules for `fl4-core` (DESIGN.md §6)

- `#![no_std]`, no `alloc`, `#![forbid(unsafe_code)]`; no raw pointers, `Cell`/`RefCell`, atomics, `dyn` or stored
  closures. Objects are typed physical-address handles, never references held across calls.
- Every fallible path returns `Result`; arithmetic is explicitly checked or wrapping; loops are bounded by
  kernel-controlled data, with preemption points as in seL4.
- Hardware goes only through the `Store` and `Arch` traits.
- Anything Charon/Aeneas cannot translate breaks the extractability gate (`.github/workflows/gate.yml`).
- **Changing an `fl4-core` function's signature or body changes `proofs/Fl4Core/Funs.lean`** and its P0/P1/P3 users.
  For kernel fixes, do not re-run extraction or Lean builds unless asked; say in the PR that the change re-extracts
  in the gate.
- New trusted code goes in `TRUSTED` (`cargo xtask trusted` checks every path exists and reports sizes).

## Proof red lines

- Never `sorry`, `admit`, `bv_decide` or `native_decide`. Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Hypotheses not yet discharged are **named premises**, tagged `[J]`, `[P]` or `[W]` in their docstrings as the
  existing `proofs/Fl4Proofs/P3` files do, and listed in the module docstring.
- Extensions to the seL4 spec go in separate Lean modules on top of `Fl4Spec`, never as edits to the port; each
  ported definition names its Isabelle source.
- P0 must stay complete: `FL4_P0_STRICT=1 cargo xtask gate` fails if any extracted function is unproved
  (`proofs/Fl4Proofs/P0/status.json`).
- After extraction: `python3 xtask/scripts/gen_const_specs.py proofs` and `python3 xtask/scripts/gen_p0.py proofs`,
  then commit `proofs/Fl4Core/*` with the regenerated P0 files.

## Commands

```sh
cargo test -p fl4-abi -p fl4-core -p fl4-arch-x86_64 -p xtask -p fl4-store -p fl4-sync   # host tests
cargo xtask kernel [--release]            # build/kernel.elf
python3 xtask/scripts/check_vm_asm.py build/kernel.elf   # entry / VM-exit mitigation ordering
cargo xtask trusted                       # TRUSTED paths and sizes
cargo xtask extract                       # Charon + Aeneas -> proofs/Fl4Core (needs $FL4_DEPS)
(cd proofs && lake build)                 # full proof build: long, large memory; build one module first
cargo xtask sel4test|fl4test [--release] [--smp N] [--setup kvm|kvm-reduced|tcg|…] [--arch aarch64]
```

Other subcommands: `run`, `uefi`, `gate`, `sim`, `mutants`, `fuzz`, `bench`, `kbench`.

**Verification budget.** Day-to-day checks are the first four commands above. Do not run full sel4test /
fl4test / `sim` / `mutants` / `fuzz` locally; when a QEMU run is needed, target it with `FL4_TESTS='^FL4(...)'`
and `--timeout`, keeping each step under about three minutes. sel4test/fl4test need
`git submodule update --init --depth 1 vendor/seL4` and the sel4test host dependencies (`$FL4_DEPS`, `SEL4TEST`).
The gate workflow runs on a self-hosted runner and PRs from forks need the owner's approval: do not count on CI.

## Contributing

- Pull requests target `main` of `losfair/FL4`; contributors without write access push to a fork.
- Keep PRs focused; large work is split at points where the full build passes.
- Keep `README.md` and `DESIGN.md` §9 status in step with what a change actually proves or supports.
