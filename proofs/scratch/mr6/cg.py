import re,sys
s=open('Fl4Core/Funs.lean').read()
defs={}
for p in re.split(r'\n(?=(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(?:def|partial def|divergent def) )',s):
    m=re.match(r'(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(?:partial |divergent )?def ([\w.]+)',p)
    if m: defs[m.group(1)]=p
def callees(n):
    b=defs[n]; return set(w for w in re.findall(r'(?<![\w.])([a-z_][\w]*\.[\w.]+)',b) if w in defs and w!=n)
def reach(roots):
    seen=set(roots);todo=list(roots)
    while todo:
        n=todo.pop()
        for c in callees(n):
            if c not in seen: seen.add(c);todo.append(c)
    return seen
R=reach(sys.argv[1:])
ops=set()
for n in R:
    for o in re.findall(r'machineArchInst\.(\w+)',defs[n]): ops.add(o)
print(sorted(ops)); print(len(R))
for x in ['cdt.delete_one','objects.post_cap_deletion','interrupt.deleted_irq_handler']: print(x, x in R)
