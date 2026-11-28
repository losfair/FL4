"""grename.py FILES... : code-only (outside comments / docstrings) renames for collapse A, Q."""
import re,sys
W=[('MachPlatT','MachPlat'),('IrqPlatK','IrqPlatA'),('MaskMRF','MaskMR'),('invoke_mrMQ','invoke_mrM'),('issue_tailMQ','issue_tailM'),
   ('irq_issue_refinesMQ','irq_issue_refinesM'),('irq_msi_refinesMQ','irq_msi_refinesM'),('irq_ioapic_refinesMNQ','irq_ioapic_refinesM'),
   ('irq_remap_refinesMNQ','irq_remap_refinesM'),('afterInv_of_mcsIMNQ','afterInv_of_mcsIMN'),('afterInv_of_mcsIMNMQ','afterInv_of_mcsIMNM'),
   ('jDecMRL_ofQ','jDecMRL_of')]
P=[('Fl4ProofsKJQ.','Fl4ProofsKJ.'),('Fl4ProofsJQ.','Fl4ProofsJ.'),('Fl4ProofsKQ.','Fl4ProofsK.'),('Fl4ProofsQ.','Fl4Proofs.')]
def split(s):
    out=[];i=0;n=len(s);buf=[];code=True
    while i<n:
        if s.startswith('/-',i):
            out.append((True,''.join(buf)));buf=[]
            d=0;j=i
            while j<n:
                if s.startswith('/-',j): d+=1;j+=2;continue
                if s.startswith('-/',j):
                    d-=1;j+=2
                    if d==0: break
                    continue
                j+=1
            out.append((False,s[i:j]));i=j;continue
        if s.startswith('--',i):
            out.append((True,''.join(buf)));buf=[]
            j=s.find('\n',i); j=n if j<0 else j
            out.append((False,s[i:j]));i=j;continue
        if s[i]=='"':
            j=i+1
            while j<n and s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
            buf.append(s[i:j+1]);i=j+1;continue
        buf.append(s[i]);i+=1
    out.append((True,''.join(buf)))
    return out
tot={}
for f in sys.argv[1:]:
    s=open(f).read(); parts=split(s); res=[]
    for code,t in parts:
        if code:
            for a,b in P:
                t,k=re.subn(r'(?<![\w])'+re.escape(a),b,t); 
                if k: tot[(f,a)]=tot.get((f,a),0)+k
            for a,b in W:
                t,k=re.subn(r'(?<![\w])'+re.escape(a)+r'(?![\w\'])',b,t)
                if k: tot[(f,a)]=tot.get((f,a),0)+k
        res.append(t)
    r=''.join(res)
    assert len(s)==sum(len(t) for _,t in parts),f
    if r!=s: open(f,'w').write(r)
import collections
c=collections.Counter()
for (f,a),k in tot.items(): c[a]+=k
print(dict(c)); print('files',len({f for f,_ in tot}))
