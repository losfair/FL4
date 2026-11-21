import json,sys,re
d=json.load(open(sys.argv[1]))
left=set(d['left']); mtk=set(d['mtk'])
cal={k:set(v) for k,v in d['callee'].items()}
roots=sys.argv[2].split(',')
excl=set(sys.argv[3].split(','))
seen=set();todo=list(roots)
while todo:
    n=todo.pop()
    if n in seen or n in excl or n in mtk: continue
    seen.add(n)
    todo+= list(cal.get(n,()))
S=seen&left
order=[];done=set()
def visit(n,stk=()):
    if n in done: return
    if n in stk: print('CYCLE',n,file=sys.stderr); return
    for c in sorted(cal.get(n,())):
        if c in seen: visit(c,stk+(n,))
    done.add(n)
    if n in S: order.append(n)
for n in sorted(seen): visit(n)
print(' '.join(order))
print('NONMON', ' '.join(sorted(seen-left-mtk)), file=sys.stderr)
