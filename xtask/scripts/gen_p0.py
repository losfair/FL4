#!/usr/bin/env python3
"""Generate proofs/Fl4Proofs/P0/Auto.lean: a P0 theorem for every function
Aeneas extracted from fl4-core.

P0 (DESIGN.md §9): the function never fails, given that the trusted
`Store` and `Arch` never fail. Each theorem is a `step` lemma, so callers'
proofs step over their callees. Proofs come from, in order of preference:

- Fl4Proofs/P0/Manual.lean.in: hand-written theorems, spliced in at the
  function's place in dependency order (they may use their callees' P0
  lemmas, and their callers use them);
- constants: the values proven in Consts.lean;
- loops: `loop.spec_decr_nat` with the first candidate measure (`v` or
  `u - v` over the loop's integer variables) for which the body steps;
- other functions: `unfold` and `p0_auto` (`step*`, then `scalar_tac`
  and `simp_all`), or `p0_split` for large matches.

Whatever fails becomes `sorry` and is listed in status.json with the goal
left over. Loop bodies are covered by their loop's theorem. The generator
reruns Lean, advancing failed attempts, until the file builds.

Usage: gen_p0.py PROOFS_DIR
"""
import json
import os
import re
import subprocess
import sys
from pathlib import Path

proofs = Path(sys.argv[1]).resolve()
funs = (proofs / "Fl4Core/Funs.lean").read_text()
INTS = ("Std.U64", "Std.Usize", "Std.U32")

# Hand-written proofs: blocks starting at `theorem NAME.p0`.
manual = {}
mpath = proofs / "Fl4Proofs/P0/Manual.lean.in"
if mpath.exists():
    text = mpath.read_text()
    starts = [m for m in re.finditer(r"^(?:@\[step\] )?theorem ([A-Za-z0-9_.']+)\.p0\b", text, re.M)]
    for i, m in enumerate(starts):
        end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
        block = text[m.start():end].rstrip() + "\n"
        if not block.startswith("@[step]"):
            block = "@[step] " + block
        manual[m.group(1)] = block

ctext = (proofs / "Fl4Proofs/P0/Consts.lean").read_text()
consts = set(re.findall(r"theorem ([A-Za-z0-9_.']+)\.spec :", ctext))
# Values of the Result-valued constants, for loop bounds.
const_vals = dict(re.findall(r"theorem ([A-Za-z0-9_.']+)\.spec : \S+ ⦃ v => v = (\d+)#\w+ ⦄", ctext))
# Functions with a precise step spec (Eq.lean, Specs.lean): their P0
# theorem follows from it and must not be a step lemma, or step would pick
# the weaker one.
specs = set()
for f in ("Eq.lean", "Specs.lean"):
    specs |= set(re.findall(r"theorem ([A-Za-z0-9_.']+)\.spec\b", (proofs / "Fl4Proofs/P0" / f).read_text()))

# Every `def NAME BINDERS : TYPE := BODY` in Funs.lean, in order.
defs = {}
order = []
for m in re.finditer(r"^def ([A-Za-z0-9_.']+)((?:[^\n]|\n(?!\n))*?)\s:=(?=\s)", funs, re.M):
    name, header = m.group(1), " ".join(m.group(2).split())
    end = funs.find("\n\n", m.end())
    body = funs[m.end():end if end >= 0 else len(funs)]
    defs[name] = (header, body)
    order.append(name)


def split_binders(h):
    """Binder groups and the result type of `BINDERS : TYPE`."""
    groups, i, depth, start = [], 0, 0, None
    while i < len(h):
        c = h[i]
        if c in "({[" and depth == 0:
            start = i
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
            if depth == 0:
                groups.append(h[start:i + 1])
        elif depth == 0 and c == ":":
            return groups, h[i + 1:].strip()
        i += 1
    return groups, ""


def explicit(groups):
    """(name, type) of every explicit binder."""
    out = []
    for g in groups:
        if g.startswith("("):
            names, ty = g[1:-1].split(":", 1)
            out += [(n, ty.strip()) for n in names.split()]
    return out


entries = []
for name in order:
    header, body = defs[name]
    groups, ret = split_binders(header)
    if not ret.startswith("Result"):
        continue
    args = explicit(groups)
    argnames = [a for a, _ in args]
    hyps = []
    if "machineStoreInst" in argnames:
        hyps.append("(hS : StoreTotal machineStoreInst)")
    if "machineArchInst" in argnames:
        hyps.append("(hA : ArchTotal machineArchInst)")
    e = dict(name=name, binders=" ".join(groups + hyps), call=f"{name} {' '.join(argnames)}".strip())
    if name.endswith(".body") and name[:-5] in defs:
        e["kind"] = "body"
    elif name in consts and not args:
        e["kind"] = "const"
    elif "partial_fixpoint" in body:
        e["kind"] = "rec"
    elif re.search(r"^\s*loop\b", body, re.M):
        m = re.search(r"loop\s*\(fun (\([^)]*\)|\w+) => ([A-Za-z0-9_.']+\.body)\b", body)
        if not m or m.group(2) not in defs:
            e["kind"] = "rec"
        else:
            pat = m.group(1).strip("()")
            k = len(pat.split(","))
            bargs = explicit(split_binders(defs[m.group(2)][0])[0])
            state = bargs[-k:]
            pv = [f"x{i}" for i in range(k)]
            scope = [a for a, t in args if t in INTS]
            cands = []
            # Bounds the body tests against (`if i < n`), tried first.
            names = {sn: pv[i] for i, (sn, _) in enumerate(state)}
            btext = defs[m.group(2)][1]
            # Locals bound to a slice's length (`let n := Slice.len xs`), or
            # to a computed constant (`let n ← C`).
            lens = dict(re.findall(r"let (\w+) := Slice\.len (\w+)", btext))
            cvals = {l: const_vals[c] for l, c in re.findall(r"let (\w+) ← ([\w.]+)\s*$", btext, re.M) if c in const_vals}
            for v, op, b in re.findall(r"\bif (\w+) (<=?) ([\w.#]+)\s*$", btext, re.M):
                if v not in names:
                    continue
                plus = " + 1" if op == "<=" else ""
                if b in lens:
                    if lens[b] not in argnames:
                        continue
                    c = f"{lens[b]}.length{plus} - {names[v]}.val"
                    if c not in cands:
                        cands.append(c)
                    continue
                if b in cvals:
                    c = f"{cvals[b]}{plus} - {names[v]}.val"
                    if c not in cands:
                        cands.append(c)
                    continue
                if re.fullmatch(r"\d+#\w+", b):
                    bound = b.split("#")[0]
                elif b in names:
                    bound = f"{names[b]}.val"
                elif b in [a for a, _ in args] or "." in b:
                    bound = f"{b}.val"
                else:
                    continue
                c = f"{bound}{plus} - {names[v]}.val"
                if c not in cands:
                    cands.append(c)
            for i, (_, t) in enumerate(state):
                if t not in INTS:
                    continue
                cands += [f"{u}.val - {pv[i]}.val" for u in scope]
                cands += [f"{pv[j]}.val - {pv[i]}.val" for j, (_, t2) in enumerate(state) if j != i and t2 in INTS]
                cands.append(f"{pv[i]}.val")
            e.update(kind="loop", body=m.group(2), pv=pv, cands=cands)
    else:
        e["kind"] = "fun"
    entries.append(e)

# Recheck previously generated proof scripts before searching again. This
# preserves successful loop measures across a source/proof port; Lean still
# checks every script against the current definitions and assumptions.
auto_path = proofs / "Fl4Proofs/P0/Auto.lean"
cached = {}
if auto_path.exists():
    old = auto_path.read_text()
    for e in entries:
        if e["kind"] == "body" or e["name"] in manual:
            continue
        head = f"theorem {e['name']}.p0 {e['binders']} :\n    {e['call']} ⦃ _ => True ⦄ := by\n"
        at = old.find(head)
        if at < 0:
            continue
        start = at + len(head)
        end = old.find("\n\n", start)
        body = old[start:end]
        if end >= 0 and not re.search(r"\b(?:sorry|admit)\b", body):
            cached[e["name"]] = body

print(f"gen_p0: rechecking {len(cached)} previous proof scripts", file=sys.stderr)

attempt = {}      # name -> index of the measure (loops) or tactic (functions) to try
# p0_auto, p0_split and p0_match are defined in Totality.lean.
FUN_TACTICS = ["p0_auto", "p0_split", "p0_match",
               "set_option maxHeartbeats 4000000 in p0_data",
               "set_option maxHeartbeats 4000000 in p0_structural"]
reasons = {}


def proof_of(e):
    n = e["name"]
    if n in cached:
        return cached[n]
    if e["kind"] == "const":
        return f"  exact WP.spec_mono Consts.{n}.spec (fun _ _ => trivial)"
    if n in specs:
        # A spec takes the function's explicit arguments.
        return f"  exact WP.spec_mono ({e['call'].replace(n, n + '.spec', 1)}) (fun _ _ => trivial)"
    if e["kind"] == "fun" and re.search(r"\.Insts\.CoreCmpPartialEq\w+\.eq$", n) and attempt.get(n, 0) == 0:
        # Derived `PartialEq` on an enum: split both sides; every branch
        # compares fields.
        a, b = e["call"].split()[1:3]
        return (f"  unfold {n}\n  cases {a} <;> cases {b} <;> simp [lift, core.cmp.impls.PartialEqBool.eq] <;>\n"
                f"    (repeat' split) <;> (try simp [lift, core.cmp.impls.PartialEqBool.eq]) <;> (try step*)")
    if e["kind"] == "fun":
        i = attempt.get(n, 0)
        if i < len(FUN_TACTICS):
            return f"  unfold {n}; {FUN_TACTICS[i]}"
    if e["kind"] == "loop":
        i = attempt.get(n, 0)
        if i < len(e["cands"]):
            tup = ", ".join(e["pv"])
            meas = f"fun x => match x with | ({tup}) => {e['cands'][i]}"
            pat = "⟨" + ", ".join(e["pv"]) + "⟩" if len(e["pv"]) > 1 else e["pv"][0]
            return "\n".join([
                f"  unfold {n}",
                f"  apply loop.spec_decr_nat (measure := {meas}) (inv := fun _ => True)",
                f"  · rintro {pat} -",
                f"    unfold {e['body']}",
                "    p0_body",
                "  · trivial",
            ])
    return "  sorry"


def render():
    out = [
        "-- GENERATED by xtask/scripts/gen_p0.py from Fl4Core/Funs.lean and",
        "-- Manual.lean.in. Do not edit: `cargo xtask gate` regenerates it.",
        "import Fl4Proofs.P0.Totality",
        "import Fl4Proofs.P0.Consts",
        "import Fl4Proofs.P0.Eq",
        "import Fl4Proofs.P0.Specs",
        "open Aeneas Aeneas.Std Result",
        "set_option maxHeartbeats 4000000",
        "set_option maxRecDepth 16384",
        "set_option linter.unusedVariables false",
        "",
        "namespace Fl4Proofs.P0",
        "open fl4_core Fl4Proofs.P0.Consts",
        "",
    ]
    spans = {}
    for e in entries:
        n = e["name"]
        if e["kind"] == "body":
            continue
        start = len(out) + 1
        if n in manual:
            out += manual[n].rstrip("\n").split("\n") + [""]
        else:
            # A theorem derived from a stronger spec (a constant's value,
            # Eq.lean, Specs.lean) is not a step lemma: step would pick it
            # over the spec.
            attr = "" if n in specs or e["kind"] == "const" else "@[step] "
            out += [
                f"{attr}theorem {n}.p0 {e['binders']} :",
                f"    {e['call']} ⦃ _ => True ⦄ := by",
                *proof_of(e).split("\n"),
                "",
            ]
        spans[n] = (start, len(out))
    out.append("end Fl4Proofs.P0")
    return "\n".join(out) + "\n", spans


auto_path = proofs / "Fl4Proofs/P0/Auto.lean"
subprocess.run(["lake", "build", "Fl4Proofs.P0.Totality", "Fl4Proofs.P0.Consts", "Fl4Proofs.P0.Eq", "Fl4Proofs.P0.Specs"], cwd=proofs, check=True)
by_name = {e["name"]: e for e in entries}
for round_ in range(40):
    text, spans = render()
    auto_path.write_text(text)
    # Build through Lake so successful checks also update the module cache
    # used by the complete proof build and by subsequent gate runs.
    r = subprocess.run(["lake", "build", "Fl4Proofs.P0.Auto"], cwd=proofs, capture_output=True, text=True)
    log = r.stdout + r.stderr
    if path := os.environ.get("FL4_P0_LOG"):
        Path(path).write_text(log)
    found = list(re.finditer(
        r"^(?:error: [^\n]*?Auto\.lean:(\d+):\d+:|[^\n]*?Auto\.lean:(\d+):\d+: error)", log, re.M))
    if not found:
        if r.returncode != 0:
            sys.exit("gen_p0: Lean failed outside a generated proof:\n" + log[:4000])
        break
    bad = set()
    pending_manual = set()
    hard_manual = set()
    for i, m in enumerate(found):
        line = int(m.group(1) or m.group(2))
        hit = [n for n, (a, b) in spans.items() if a <= line < b]
        if not hit:
            sys.exit("gen_p0: error outside generated proofs:\n" + log[:4000])
        n = hit[0]
        chunk = log[m.end():found[i + 1].start() if i + 1 < len(found) else len(log)]
        if n in manual and "unknown constant" in chunk:
            pending_manual.add(n)
        elif n in manual:
            hard_manual.add(n)
        goal = re.search(r"⊢ ((?:.|\n(?!\S))*)", chunk)
        reasons[n] = " ".join((goal.group(1) if goal else chunk.strip().split("\n")[0]).split())[:300]
        bad.add(n)
    # A missing callee may be retried after its automatic proof advances.
    # An independent failure in the same manual theorem must still be fatal.
    bad -= pending_manual - hard_manual
    if bad & set(manual):
        sys.exit("gen_p0: hand-written proofs fail: " + ", ".join(sorted(bad & set(manual))) + "\n" + log[:4000])
    progress = False
    for n in bad:
        e = by_name[n]
        if n in cached:
            del cached[n]
            progress = True
        elif e["kind"] == "loop":
            if attempt.get(n, 0) < len(e["cands"]):
                attempt[n] = attempt.get(n, 0) + 1
                progress = True
        elif e["kind"] == "fun" and attempt.get(n, 0) < len(FUN_TACTICS):
            attempt[n] = attempt.get(n, 0) + 1
            progress = True
    if not progress:
        sys.exit("gen_p0: no progress:\n" + log[:4000])
    print(f"gen_p0: round {round_}: {len(bad)} proofs failed", file=sys.stderr)

counted = [e for e in entries if e["kind"] != "body"]
sorry = sorted(e["name"] for e in counted if e["name"] not in manual and proof_of(e) == "  sorry")
loops_ok = sorted(e["name"] for e in counted if e["kind"] == "loop" and e["name"] not in manual and e["name"] not in sorry)
status = dict(
    functions=len(counted),
    proved=len(counted) - len(sorry),
    manual=sorted(manual),
    loops_automatic=loops_ok,
    sorry={n: (by_name[n]["kind"], reasons.get(n, "")) for n in sorry},
)
(proofs / "Fl4Proofs/P0/status.json").write_text(json.dumps(status, indent=1) + "\n")
print(f"gen_p0: {len(counted)} functions (loop bodies are covered by their loops): "
      f"{status['proved']} proved ({len(manual)} by hand, {len(loops_ok)} loops automatically), {len(sorry)} sorry")
