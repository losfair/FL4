import sys
sys.argv=['gen.py','x','/dev/null']
src=open('gen.py').read().split('# topo order')[0]
exec(src)
targets=set(sys.stdin.read().split())
# reverse reach within R
rev={}
for k in R:
    for c in callee.get(k,()):
        rev.setdefault(c,set()).add(k)
seen=set(targets);todo=list(targets)
while todo:
    n=todo.pop()
    for p in rev.get(n,()):
        if p not in seen: seen.add(p);todo.append(p)
print(len(seen)); print(' '.join(sorted(seen)))
