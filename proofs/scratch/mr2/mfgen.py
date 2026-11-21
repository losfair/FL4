import re,sys
P='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-tcbj/proofs/Fl4Proofs/P3/'
G=sys.argv[1]
skip=set(x for x in open(G+'/skip.txt').read().split() if x)
def blocks(fn, stop=None):
    s=open(P+fn).read()
    if stop: s=s[:s.index(stop)]
    lines=s.split('\n'); out=[];cur=None
    for l in lines:
        if l.startswith('theorem '):
            if cur: out.append(cur)
            cur=[l]
        elif cur is not None:
            if l.startswith('macro_rules'):
                cur.append(l); out.append(cur); cur=None
            elif l.startswith(('/-','end','section','variable','namespace','open','noncomputable','set_option','macro ','syntax','abbrev','def ')):
                out.append(cur); cur=None
            else: cur.append(l)
    if cur: out.append(cur)
    return out
bs=blocks('VsDomOps.lean')+blocks('DomRecDel.lean')+blocks('TcbDom.lean','theorem dk_restart')+blocks('AllDom.lean','theorem dke_fl4Perform')
names=[re.match(r'theorem (\S+)',b[0]).group(1) for b in bs]
defined=set(names)|{'dk_setCap','dk_getCap','dk_doExtendedOp','dk_setObject'}
# closure of skip: drop any lemma whose text mentions a skipped (or missing) lemma
import glob
D='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-tcbj/proofs/Fl4Spec/'
defs={}
for f in glob.glob(D+'**/*.lean',recursive=True):
    ss=open(f).read()
    for p in re.split(r'\n(?=(?:private |noncomputable |partial |@\[[^\]]*\] )*(?:def|abbrev|theorem|structure|inductive|instance|class) )',ss):
        m=re.match(r'(?:private |noncomputable |partial |@\[[^\]]*\] )*(def|abbrev) (\S+)',p)
        if m: defs.setdefault(m.group(2),p.split(':=',1)[-1])
callee={k:set(w for w in re.findall(r"(?<![\w.])([a-z][A-Za-z0-9_']*)",v) if w in defs and w!=k) for k,v in defs.items()}
def reach(f):
    seen=set();todo=[f]
    while todo:
        n=todo.pop()
        for c in callee.get(n,()):
            if c not in seen: seen.add(c);todo.append(c)
    return seen
def fn(t):
    m=re.search(r":\s*DKE?\s*\(+\s*([A-Za-z0-9_']+)",t)
    return m.group(1) if m else None
badf=set(fn('\n'.join(b)) for b,n in zip(bs,names) if n in skip)|set(x[3:] for x in skip if x.startswith('fn:'))
badf.discard(None)
res=[];dropped=set(skip)
for b,n in zip(bs,names):
    t='\n'.join(b).rstrip()
    if 'DK' not in t: continue
    if n in dropped: continue
    f0=fn(t)
    if f0 and (reach(f0)&badf): dropped.add(n); continue
    used=set(re.findall(r"(?<![A-Za-z0-9_'.])(dke?_[A-Za-z0-9_']+)",t))-{n}
    if any(u in dropped for u in used): dropped.add(n); continue
    for d in sorted(defined,key=len,reverse=True):
        nn=d.replace('dke_','mfke_',1) if d.startswith('dke_') else d.replace('dk_','mfk_',1)
        t=re.sub(r"(?<![A-Za-z0-9_'.])"+re.escape(d)+r"(?![A-Za-z0-9_'])",nn,t)
    t=re.sub(r'\bDKE\b','MFKE',t); t=re.sub(r'\bDK\b','MFK',t); t=re.sub(r'\bschedF\b','msF',t)
    t=t.replace('exact dk_doMachineOp _','mfk_auto')
    t=t.replace('dk_auto0','dk_auto0').replace('dk_auto','mfk_auto').replace('dk_leaf','mfk_leaf')
    res.append(t)
open(G+'/body.lean','w').write('\n\n'.join(res)+'\n')
open(G+'/dropped.txt','w').write(' '.join(sorted(dropped)))
print(len(res), len(dropped))
