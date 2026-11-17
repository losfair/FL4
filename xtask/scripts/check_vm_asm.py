#!/usr/bin/env python3
"""Check mitigation ordering in the linked kernel, not just assembly source.

After cargo xtask kernel: python3 xtask/scripts/check_vm_asm.py build/kernel.elf
This checks code generation and ordering; it cannot prove predictor isolation.
"""
import re
import subprocess
import sys

text = subprocess.check_output(
    ["objdump", "-d", "--no-show-raw-insn", sys.argv[1]], text=True
)
functions = {}
current = None
for line in text.splitlines():
    symbol = re.match(r"^[0-9a-f]+ <([^>]+)>:$", line)
    if symbol:
        current = symbol[1]
        functions[current] = []
    insn = re.match(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
    if insn and current:
        functions[current].append((int(insn[1], 16), insn[2], insn[3]))


def require(ok, message):
    if not ok:
        raise SystemExit("VM assembly check failed: " + message)


def barrier(name, instructions):
    by_address = {a: (op, arg) for a, op, arg in instructions}
    ops = [op for _, op, _ in instructions]
    ibpb = next((i for i, (_, op, arg) in enumerate(instructions)
                 if op == "mov" and arg == "$0x49,%ecx"), None)
    require(ibpb is not None, name + ": missing PRED_CMD write")
    require(ops[ibpb:ibpb + 5] == ["mov", "mov", "xor", "wrmsr", "lfence"],
            name + ": IBPB must end in WRMSR/LFENCE")
    require(instructions[ibpb + 1][2] == "$0x1,%eax"
            and instructions[ibpb + 2][2] == "%edx,%edx",
            name + ": wrong IBPB command")
    require("ret" not in ops[:ibpb] and "stgi" not in ops[:ibpb],
            name + ": return/interrupt enable before IBPB")
    require(not any(op in ("call", "jmp") and arg.startswith("*")
                    for _, op, arg in instructions),
            name + ": indirect branch in boundary")
    # Every conditional skip around a mitigation lands at LFENCE. The
    # guest can train branch directions, but cannot speculate past this.
    seen_flags = set()
    for i, (_, op, arg) in enumerate(instructions[:-1]):
        if op != "test" or not arg.endswith(",%r11d"):
            continue
        seen_flags.add(int(arg.split(",")[0][1:], 16))
        _, branch, target = instructions[i + 1]
        require(branch == "je", name + ": changed mitigation guard")
        target_op, _ = by_address[int(target.split()[0], 16)]
        require(target_op == "lfence", name + ": mitigation skip lacks fence")
    require(seen_flags == {1, 2, 4, 8, 16, 32}, name + ": missing mitigation guard")
    require(any(op == "mov" and arg == "$0x20,%ecx"
                for _, op, arg in instructions), name + ": missing 32-entry RAP fill")
    # The RSB/PBRSB calls have nonzero displacements and trapped returns.
    traps = 0
    for i, (addr, op, arg) in enumerate(instructions[:-1]):
        if op == "call" and instructions[i + 1][1] == "int3":
            require(int(arg.split()[0], 16) != instructions[i + 1][0],
                    name + ": zero-displacement mitigation CALL")
            traps += 1
    require(traps == 2, name + ": missing RAP/PBRSB trap")
    first_ret = ops.index("ret") if "ret" in ops else len(ops)
    require(first_ret > ibpb, name + ": unprotected BHB/host return")
    require(any(op == "mov" and arg == "$0xc,%ecx" for _, op, arg in instructions)
            and any(op == "mov" and arg == "$0x7,%eax" for _, op, arg in instructions),
            name + ": missing long BHB clearing sequence")


vmx = functions["fl4_vmx_exit"]
svm = functions["fl4_svm_run"]
native = functions["fl4_common_entry"]
barrier("VMX", vmx)
vmrun = next(i for i, (_, op, _) in enumerate(svm) if op == "vmrun")
barrier("SVM", svm[vmrun + 1:])
barrier("native", native)
svm_ops = [op for _, op, _ in svm]
require(svm_ops.index("clgi") < vmrun < svm_ops.index("stgi"),
        "SVM must keep GIF clear across the entry/exit boundary")
require(max(i for i, op in enumerate(svm_ops) if op == "wrmsr") < svm_ops.index("stgi"),
        "SVM enables interrupts before host protection")

for name, instructions in [
    ("VMX entry", functions["fl4_vmx_run"]), ("SVM entry", svm),
    ("native return", native), ("user return", functions["fl4_restore_user"]),
    ("idle", functions["fl4_idle"]),
]:
    for i, (_, op, _) in enumerate(instructions):
        if op in ("vmlaunch", "vmresume", "vmrun", "iretq", "sysretq", "sti"):
            # SVM's STI precedes VMRUN with GIF clear, not an idle entry.
            if op == "sti" and name != "idle":
                continue
            require(i >= 2 and instructions[i - 1][1] == "lfence"
                    and instructions[i - 2][1] == "verw",
                    name + ": missing final memory-form VERW/fence before " + op)
            require("(%rip)" in instructions[i - 2][2], name + ": VERW must use memory")
require(not any(n.startswith("fl4_test_") for n in functions), "test trampoline in kernel")
print("VM assembly: entry/exit barriers, fenced guards, RAP/PBRSB, BHB, VERW and GIF ordering verified")
