import os
import json,re,sys
S=os.path.dirname(os.path.abspath(__file__))+'/'
d=json.load(open(S+'cg.json')); sig=d['sig']
order=open(S+'order.txt').read().split()
manual=set(open(S+'manual.txt').read().split())
extra={}  # name -> extra unfold list
for l in open(S+'extra.txt').read().splitlines():
    if l.strip():
        k,v=l.split(':',1); extra[k.strip()]=v.strip()
def split_binders(s):
    out=[];i=0
    while i<len(s):
        c=s[i]
        if c in '({[':
            close={'(':')','{':'}','[':']'}[c];dep=0;j=i
            while j<len(s):
                if s[j] in '({[': dep+=1
                elif s[j] in ')}]': dep-=1
                if dep==0: break
                j+=1
            out.append(s[i:j+1]); i=j+1
        elif c==' ': i+=1
        elif c==':': return out, s[i+1:].strip()
        else: return None
    return None
def top_arrows(t):
    parts=[];dep=0;cur=''
    i=0
    while i<len(t):
        c=t[i]
        if c in '({[': dep+=1
        if c in ')}]': dep-=1
        if dep==0 and t.startswith('→',i):
            parts.append(cur.strip()); cur=''; i+=1; continue
        cur+=c; i+=1
    parts.append(cur.strip()); return parts
res=[]
for n in order:
    if os.path.exists(S+'man/'+n+'.lean'):
        res.append(open(S+'man/'+n+'.lean').read()); continue
    if n in manual: continue
    s=sig[n]
    m=re.match(r'(?:def|abbrev) (\S+)\s*(.*)$',s,re.S)
    body=m.group(2).strip()
    r=split_binders(body)
    if r is None: print('SKIP-parse',n,file=sys.stderr); continue
    bs,ty=r
    ty=ty.split(' | ')[0].strip()
    parts=top_arrows(ty)
    ret=parts[-1]; argt=parts[:-1]
    names=[];binders=[]
    for b in bs:
        if b.startswith('('):
            inner=b[1:-1]; nm,tt=inner.split(':',1)
            for x in nm.split(): names.append(x)
            binders.append(b)
        elif b.startswith('{'):
            binders.append(b)
        else: binders.append(b)
    for k,a in enumerate(argt):
        x='x%d'%k; names.append(x); binders.append('(%s : %s)'%(x,a))
    E = bool(re.match(r'(PMonad|SEMonad|FMonad|LFMonad|NonDetE)',ret))
    if not re.match(r'(PMonad|SEMonad|FMonad|LFMonad|NonDetE|SMonad|NonDet \(State)',ret):
        print('SKIP-ret',n,ret,file=sys.stderr); continue
    fix=lambda t: re.sub(r'\bZ\b','Unit',t)
    binders=[fix(b) for b in binders]
    useZ = bool(re.search(r'\bZ\b',s))
    call=n+(' (Z := Unit)' if useZ else '')+''.join(' '+x for x in names)
    K='GKE' if E else 'GK'
    st=' '.join(binders)
    unf='unfold '+n+((' '+extra[n]) if n in extra else '')
    intro=('intro '+' '.join(names)+'; ') if False else ''
    res.append(f"theorem gk_{n} {st} : {K} ({call}) := by\n  {unf}; gk_auto\nmacro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_{n})\n")

print(len(res))

hdr=open(S+'hdr.lean').read()
for t in ['fl4HandleEvent','fl4CallKernel']: res.append(open(S+'man/'+t+'.lean').read())
R=S+'../../Fl4Proofs/P3/SpecInvValidMachineTimeGen.lean'
open(R,'w').write(hdr+'\n'.join(res)+'\nend\n\nend Fl4Proofs.P3.SInvV\n')
s=open(R).read(); s=s.replace("theorem gk_receiveIpc ","set_option maxHeartbeats 4000000 in\ntheorem gk_receiveIpc "); open(R,'w').write(s)
