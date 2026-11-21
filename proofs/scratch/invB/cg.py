import os
import re,glob,sys
R=os.path.dirname(os.path.abspath(__file__))+'/../../'
defs={};sig={}
for f in glob.glob(R+'Fl4Spec/**/*.lean',recursive=True):
    ss=open(f).read()
    for p in re.split(r'\n(?=(?:private |noncomputable |partial |@\[[^\]]*\] )*(?:def|abbrev|theorem|structure|inductive|instance|class|opaque|/--) )',ss):
        m=re.match(r'(?:private |noncomputable |partial |@\[[^\]]*\] )*(def|abbrev) (\S+)',p)
        if m:
            defs.setdefault(m.group(2),p.split(':=',1)[-1] if ':=' in p.split('\n')[0] or True else p); sig.setdefault(m.group(2),p.split(':=',1)[0])
callee={k:set(w for w in re.findall(r"(?<![\w.])([a-z][A-Za-z0-9_']*)",v) if w in defs and w!=k) for k,v in defs.items()}
def monadic(k):
    s=sig[k]; return bool(re.search(r'(SMonad|PMonad|SEMonad|FMonad|NonDetE|NonDet |LFMonad|DetExtMonad|MachineMonad|KernelF|IMonad)',s))
mtk=set()
for f in ['MachFieldFamT.lean']:
    for n in re.findall(r"^theorem (?:mtk|mtke)_([A-Za-z0-9_]+)'?",open(R+'Fl4Proofs/P3/'+f).read(),re.M): mtk.add(n)
root=sys.argv[1] if len(sys.argv)>1 else 'fl4KernelEntrySyscall'
seen=set();todo=[root];stop=set(sys.argv[2:])
while todo:
    n=todo.pop()
    if n in mtk and n!=root: continue
    for c in callee.get(n,()):
        if c not in seen: seen.add(c); todo.append(c)
left=[x for x in seen if x not in mtk and monadic(x)]
print(len(seen),len(left))
print(' '.join(sorted(left)))
import json
out={}
for x in sorted(left):
    s=' '.join(sig[x].split())
    out[x]=s
json.dump({'left':sorted(left),'sig':out,'callee':{k:sorted(v) for k,v in callee.items()},'mtk':sorted(mtk)},open(os.path.dirname(os.path.abspath(__file__))+'/cg.json','w'))
for x in sorted(left): print(out[x][:220])
