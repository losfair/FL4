import sys
sys.setrecursionlimit(10000)
import re,glob,json,sys
D='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-sc/proofs/Fl4Spec/'
defs={};kind={}
for f in sorted(glob.glob(D+'**/*.lean',recursive=True)):
    ss=open(f).read()
    for p in re.split(r'\n(?=(?:private |noncomputable |partial |@\[[^\]]*\] )*(?:def|abbrev|theorem|structure|inductive|instance|class|mutual|end|section|namespace|variable|open|/-|--) )|\n(?=/-)',ss):
        m=re.match(r'(?:private |noncomputable |partial |@\[[^\]]*\] )*(def|abbrev) (\S+)',p)
        if m and m.group(2) not in defs: defs[m.group(2)]=p; kind[m.group(2)]=m.group(1)
def body(n): return defs[n]
callee={k:set(w for w in re.findall(r"(?<![\w.])([a-z][A-Za-z0-9_']*)",v.split(':=',1)[-1] if ':=' in v else v) if w in defs and w!=k) for k,v in defs.items()}
def header(p):
    # up to first top-level ':=' or newline-'|'
    depth=0;i=0
    while i<len(p):
        c=p[i]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        elif depth==0 and p.startswith(':=',i): return p[:i],'eq'
        elif depth==0 and p.startswith('\n  |',i): return p[:i],'match'
        elif depth==0 and p.startswith('\n|',i): return p[:i],'match'
        i+=1
    return p,'?'
def split_top(s,sep):
    out=[];depth=0;cur=''
    i=0
    while i<len(s):
        c=s[i]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        if depth==0 and s.startswith(sep,i):
            out.append(cur);cur='';i+=len(sep);continue
        cur+=c;i+=1
    out.append(cur);return out
zs=lambda c: bool(re.search(r'\\bZ\\b|\\(State ',c))
def topgroups(b):
    out=[];d=0;st=None
    for i,c in enumerate(b):
        if c in '([{':
            if d==0 and c=='(': st=i
            d+=1
        elif c in ')]}':
            d-=1
            if d==0 and c==')' and st is not None: out.append(b[st:i+1]); st=None
    return out
def parse(n):
    h,_=header(defs[n])
    h=re.sub(r'--[^\n]*','',h)
    h=' '.join(h.split())
    m=re.match(r'(?:private |noncomputable |partial |@\[[^\]]*\] )*def '+re.escape(n)+r'(.*)$',h)
    if not m: return None
    rest=m.group(1)
    # split binders and type at the top-level ':'
    parts=split_top(rest,' : ')
    if len(parts)<2:
        parts=split_top(rest,':')
    if len(parts)<2: return None
    binders=re.sub(r'\{Z : Type\}\s*|\[StateExt Z\]\s*','',parts[0]).strip(); ty=' : '.join(parts[1:]).strip()
    arrows=split_top(ty,' → ')
    cod=arrows[-1].strip()
    zs=lambda c: bool(re.search(r'\bZ\b|\(State ',c))
    if re.match(r'(SMonad|NonDet) ',cod) and zs(cod): k='K'
    elif re.match(r'(SEMonad|PMonad|FMonad|LFMonad|NonDetE) ',cod) and zs(cod): k='KE'
    else: return None
    names=[]
    for g in re.findall(r'\(([^():]+?) :',binders):
        names+=g.split()
    # explicit binder groups at top-level only
    names=[];hyps=[]
    for b in topgroups(binders):
        inner=b[1:-1]
        if ':' in inner:
            ns_=inner.split(':')[0].split(); names+=ns_
            T=inner.split(':',1)[1].strip()
            ar=split_top(T,' → '); cd=ar[-1].strip()
            kk=None
            if re.match(r'(SMonad|NonDet) ',cd) and zs(cd): kk=''
            elif re.match(r'(SEMonad|PMonad|FMonad|LFMonad|NonDetE) ',cd) and zs(cd): kk='E'
            if kk is not None:
                for v in ns_:
                    xs=' '.join('x%d'%i for i in range(len(ar)-1))
                    if xs: hyps.append(('∀ %s, '%xs, '(%s %s)'%(v,xs), kk, v))
                    else: hyps.append(('', v, kk, v))
    extra=[]
    for j,a in enumerate(arrows[:-1]):
        nm='a%d'%j; extra.append('(%s : %s)'%(nm,a.strip())); names.append(nm)
    sub=lambda s: re.sub(r'\bZ\b','Unit',s)
    usesZ=bool(re.search(r'\bZ\b',h))
    return dict(binders=sub(binders+' '+' '.join(extra)).strip(), names=names, k=k, usesZ=usesZ, hyps=hyps)
def reach(fs):
    seen=set(fs);todo=list(fs)
    while todo:
        n=todo.pop()
        for c in callee.get(n,()):
            if c not in seen: seen.add(c);todo.append(c)
    return seen
R=reach(['fl4KernelEntrySyscall'])
skip=set(open(sys.argv[2]).read().split()) if len(sys.argv)>2 else set()
mon={}
import os
ONLY=set(os.environ.get('ONLY','').split())
for n in R:
    if kind.get(n)!='def' or n in skip: continue
    if ONLY and n not in ONLY: continue
    r=parse(n)
    if r: mon[n]=r
# topo order
order=[];state={}
exec(open(os.environ.get('MANUAL','manual.py')).read())
if os.environ.get('MANUAL2'): exec(open(os.environ['MANUAL2']).read())
for k,v in DEPS.items(): callee.setdefault(k,set()).update(v)
def visit(n,stack):
    if state.get(n): return
    state[n]=1
    for c in sorted(callee.get(n,())):
        visit(c,stack)
    state[n]=2
    if n in mon or (n in M and n not in skip and not ONLY): order.append(n)
for n in sorted(mon): visit(n,[])
P=sys.argv[1]
HYP=json.loads(os.environ.get('HYP','{}'))
AUTO=os.environ.get('AUTO',P)
AUTO2=set(os.environ.get('AUTO2','').split())
out=[]
FAM=sys.argv[3] if len(sys.argv)>3 else 'NSK'
FARG=sys.argv[4] if len(sys.argv)>4 else ''
for n in order:
    if n in M:
        out.append(M[n].replace('{P}',P).replace('{FE}',FAM+'E'+FARG).replace('{F}',FAM+FARG)); continue
    r=mon[n]
    z='(Z := Unit) ' if r['usesZ'] else ''
    app=('(%s %s%s)'%(n,z,' '.join(r['names']))).replace(' )',')')
    fam=(FAM if r['k']=='K' else FAM+'E')+FARG
    hb=''.join(' (h_%s : %s%s%s%s %s)'%(v,q,FAM,kk,FARG,a) for (q,a,kk,v) in r['hyps'])
    kh=HYP.get(n,[])
    hb+=''.join(' (hk_%s : %s ∈ Kq)'%(v,v) for v in kh)
    tac='exact' if not r['hyps'] else 'refine'
    fin=''
    if r['hyps']:
        alts=[]
        for (q,a,kk,v) in r['hyps']:
            n_=q.count('x')
            alts.append('exact h_%s%s'%(v,' _'*n_))
        fin='\n  all_goals first | '+' | '.join(alts)
    if kh:
        out.append('theorem %s_%s %s%s : %s %s := by\n  unfold %s; %s_auto' % (P,n,r['binders'],hb,fam,app,n,AUTO) + fin + '\nmacro_rules | `(tactic| %s_leaf) => `(tactic| ((with_reducible refine %s_%s%s%s%s) <;> nq_mem))\n' % (P,P,n,' _'*len(r['names']),''.join(' ?_' if not q else ' (fun%s => ?_)'%(' _'*q.count('x')) for (q,a,kk,v) in r['hyps']),' ?_'*len(kh)))
        continue
    out.append('theorem %s_%s %s%s : %s %s := by\n  unfold %s; %s_auto' % (P,n,r['binders'],hb,fam,app,n,(AUTO+'2' if n in AUTO2 else AUTO)) + fin + '\nmacro_rules | `(tactic| %s_leaf) => `(tactic| with_reducible %s %s_%s%s%s)\n' % (P,tac,P,n,' _'*len(r['names']),''.join(' ?_' if not q else ' (fun%s => ?_)'%(' _'*q.count('x')) for (q,a,kk,v) in r['hyps'])))
open(sys.argv[5] if len(sys.argv)>5 else 'body.lean','w').write('\n'.join(out))
print(len(order))
