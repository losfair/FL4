import sys
src=open('gen.py').read()
pre=src.split("R=reach(['fl4KernelEntrySyscall'])")[0]
exec(pre)
R=reach(['fl4KernelEntrySyscall'])
prim=set(open('prim.txt').read().split())
seed=set(open(sys.argv[1]).read().split())
extra=set(open(sys.argv[2]).read().split()) if len(sys.argv)>2 else set()
seed|=extra
# manual texts' deps
exec(open('manual_sl.py').read())
for k,v in DEPS.items(): callee.setdefault(k,set()).update(v)
S=set(seed);ch=True
while ch:
    ch=False
    for n in R:
        if n not in S and not (n in M and M[n] and n not in seed) and callee.get(n,set())&S: S.add(n);ch=True
print(' '.join(sorted(S|prim)))
sys.stderr.write('%d skipped of %d; added by closure: %s\n'%(len(S),len(R),' '.join(sorted(S-seed))))
