import sys
exec(open('gen.py').read().split("open('body.lean','w')")[0].replace("P=sys.argv[1]","P='x'"))
bad=set(sys.argv[3].split(','))
rev={}
for k,v in callee.items():
    for c in v: rev.setdefault(c,set()).add(k)
seen=set(bad);todo=list(bad)
while todo:
    n=todo.pop()
    for c in rev.get(n,()):
        if c in R and c not in seen: seen.add(c);todo.append(c)
print(sorted(seen))
