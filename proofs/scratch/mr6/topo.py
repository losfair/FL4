import re,sys
exec(open(sys.argv[1]).read().split('R=reach')[0])
R=reach(sys.argv[2:])
A=[n for n in R if '(machineArchInst : machine.Arch A)' in defs[n]]
order=[];seen=set()
def visit(n):
    if n in seen: return
    seen.add(n)
    for c in sorted(callees(n)):
        if c in A: visit(c)
    order.append(n)
for n in sorted(A): visit(n)
for n in order: print(n)
