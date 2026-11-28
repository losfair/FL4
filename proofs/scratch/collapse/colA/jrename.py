import re,sys,collections
exec(open('scratch/collapse/py/srcdecl.py').read())
R=open(sys.argv[1]).read().split('\n')
todo=[]
i=0
while i<len(R):
    if R[i].startswith('Fl4'):
        n,m=R[i].split(); plus=eval(R[i+1].split('+',1)[1]); minus=eval(R[i+2].split('-',1)[1])
        todo.append((n,m,plus,minus)); i+=3
    else: i+=1
bym=collections.defaultdict(list)
for n,m,p,mi in todo:
    if n=='Fl4Proofs.P3.MachPlat': continue
    ren=[]
    pm={'JDecMRLKQ':'JDecMRLK','JDecMRL2Q':'JDecMRL2','jVtxHypMU_ofQ':'jVtxHypMU_of','jDecMRL2_ofTQ':'jDecMRL2_ofT','jDecMRLK_ofUQ':'jDecMRLK_ofU'}
    for x in p:
        assert x in pm,(n,x); assert pm[x] in mi,(n,x); ren.append((pm[x],x))
    assert len(p)==len(mi),(n,p,mi)
    bym[m].append((n,ren))
tot=0
for m,xs in bym.items():
    path=m.replace('.','/')+'.lean'; text=open(path).read()
    lines,bl=blocks(text); loc={b['name']:b for b in bl}
    for n,ren in xs:
        b=loc[n]
        seg='\n'.join(lines[b['start']:b['end']])
        for a,c in ren:
            seg,k=re.subn(r'(?<![\w.])'+re.escape(a)+r'(?![\w\'])',c,seg)
            print(m.split('.')[-1],n.split('.')[-1],a,'->',c,k); tot+=k
            if k==0: print("   NOTEXT",n,a)
        lines[b['start']:b['end']]=seg.split('\n')
    open(path,'w').write('\n'.join(lines))
print('total',tot)
