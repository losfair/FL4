#!/usr/bin/env python3
"""Check mitigation ordering in the linked kernel, not just assembly source.

After cargo xtask kernel: python3 xtask/scripts/check_vm_asm.py build/kernel.elf
This checks code generation and ordering; it cannot prove predictor isolation.
"""
from collections import Counter
import re
import subprocess
import sys

text = subprocess.check_output(
    [sys.argv[2] if len(sys.argv) > 2 else "objdump",
     "-d", "--no-show-raw-insn", sys.argv[1]], text=True
)
functions = {}
near_returns = Counter()
current = None
for line in text.splitlines():
    symbol = re.match(r"^[0-9a-f]+ <([^>]+)>:$", line)
    if symbol:
        current = symbol[1]
        functions[current] = []
    insn = re.match(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
    if insn and current:
        op, arg = insn[2], insn[3]
        functions[current].append((int(insn[1], 16), op, arg))
        if op in ("ret", "retq", "retl", "retn") or (
                op in ("rep", "repz") and re.match(r"ret[qnl]?\b", arg)):
            near_returns[current] += 1


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
# The user return takes SYSRET only for an untouched SYSCALL context
# (sysret.S): RCX = NextIP, R11 = FLAGS, no TF/RF, and leaves no CR3 on the
# entry stack.
user = functions["fl4_restore_user"]
user_ops = [op for _, op, _ in user]
sysret = user_ops.index("sysretq")
def before_sysret(pred):
    return any(pred(op, arg) for _, op, arg in user[:sysret])
require(before_sysret(lambda op, arg: op.startswith("cmp") and "0x98(%rdi)" in arg)
        and before_sysret(lambda op, arg: op.startswith("cmp") and "0x90(%rdi)" in arg),
        "user return: SYSRET without the RCX/R11 checks")
require(before_sysret(lambda op, arg: op.startswith("test") and arg.startswith("$0x10100,")),
        "user return: SYSRET without the TF/RF check")
require(sum(1 for _, op, arg in user if op.startswith("mov") and arg == "$0x0,(%rsp)") == 2,
        "user return: CR3 left on the entry stack")
# Every IDT stub goes through fl4_vector_entry, which clears RFLAGS (AC:
# SMAP) before the common entry: gates keep the interrupted AC.
stubs = functions["fl4_vectors"]
vector_entry = functions.get("fl4_vector_entry", [])
jumps = [arg for _, op, arg in stubs if op == "jmp"]
require(len(jumps) == 256 and all(a.endswith("<fl4_vector_entry>") for a in jumps),
        "IDT stub that bypasses fl4_vector_entry")
require([op for _, op, _ in vector_entry[:3]] == ["push", "popf", "jmp"]
        and vector_entry[0][2] == "$0x2"
        and vector_entry[2][2].endswith("<fl4_common_entry>"),
        "fl4_vector_entry must load RFLAGS = 2 before fl4_common_entry")
require(not any(n.startswith("fl4_test_") for n in functions), "test trampoline in kernel")
# All compiler-generated near returns, including core and compiler-builtins,
# must go through the thunk. The VM-entry code's returns are after its IBPB
# and the native entry's two raw returns are in the Intel-only BHB routine.
require(near_returns == {
    "fl4_safe_ret_insn": 1,
    "__x86_return_thunk": 1,
    "fl4_common_entry": 2,
    "fl4_vmx_exit": 3,
    "fl4_svm_run": 3,
}, f"unexpected near returns: {near_returns}")
untrain = functions["fl4_untrain_ret"]
safe = functions["fl4_safe_ret"]
require(untrain[0][0] & 0x1fffff == 0
        and untrain[0][0] ^ safe[0][0] == 0x104104,
        "Safe RET BTB addresses differ from the required alias")
require([op for _, op, _ in safe] == ["lea"]
        and safe[0][2] == "0x8(%rsp),%rsp"
        and [op for _, op, _ in functions["fl4_safe_ret_insn"][:2]] == ["ret", "int3"],
        "Safe RET must discard the speculative target and trap after RET")
fallback = functions["__x86_return_thunk"]
safe_thunk = functions["fl4_safe_ret_thunk"]
require([op for _, op, _ in fallback[:2]] == ["ret", "int3"]
        and fallback[1][0] == fallback[0][0] + 1,
        "return thunk must start with RET and a one-byte INT3")
require(fallback[0][0] + 2 - 52 == safe_thunk[0][0]
        and [op for _, op, _ in safe_thunk[:2]] == ["call", "ud2"]
        and safe_thunk[0][2].endswith("<fl4_safe_ret>"),
        "the patched short jump must land at the Safe RET thunk")
untrain_call = next(i for i, (_, op, arg) in enumerate(native)
                    if op == "call" and arg.endswith("<fl4_untrain_ret>"))
require(native[untrain_call - 1][1] == "lfence",
        "untraining call must be behind a fenced policy guard")

print("VM assembly: RFLAGS cleared on IDT entries, entry/exit barriers, fenced guards, RAP/PBRSB, BHB, Safe RET, VERW and GIF ordering verified")
