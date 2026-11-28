"""collapse A, Q: stchg3 with the CHANGED headers classified. RENAME = equal after the Q renames
(MachPlatT->MachPlat, IrqPlatK->IrqPlatA, MaskMRF->MaskMR, Fl4Proofs{Q,KQ,JQ,KJQ}. -> base family, the in-place
lemma renames); otherwise REAL (the diff is printed)."""
import re,sys,subprocess,difflib
exec(open('proofs/scratch/collapse/colA/stchg3.py').read().split('for f in files:')[0])
NAMED=re.compile(r"\(\s*[\w.']+\s*$")
def cut(body):
  # stchg3 cuts at the first ':=', which is often a named argument `(L := L)`: skip those
  for m in re.finditer(r':=',body):
    if not NAMED.search(body[max(0,m.start()-40):m.start()]): return m.start()
  return len(body)
def decls(rev,f):
  t=subprocess.check_output(['git','show',f'{rev}:{f}'],text=True)
  out={}
  ms=list(pat.finditer(t))
  for i,m in enumerate(ms):
    end=ms[i+1].start() if i+1<len(ms) else len(t)
    body=t[m.start():end]
    if m.group(1)=='structure':
      ls=body.split('\n'); k=1
      while k<len(ls) and (ls[k].startswith(' ') or ls[k]==''): k+=1
      hdr='\n'.join(ls[:k])
    else:
      j=min([k for k in (cut(body),body.find('\n  where'),body.find(' where\n')) if k>=0] or [len(body)])
      hdr=body[:j]
    out[m.group(2)]=' '.join(hdr.split())
  return out
W=[('MachPlatT','MachPlat'),('IrqPlatK','IrqPlatA'),('MaskMRF','MaskMR'),('invoke_mrMQ','invoke_mrM'),('issue_tailMQ','issue_tailM'),
   ('irq_issue_refinesMQ','irq_issue_refinesM'),('irq_msi_refinesMQ','irq_msi_refinesM'),('irq_ioapic_refinesMNQ','irq_ioapic_refinesM'),
   ('irq_remap_refinesMNQ','irq_remap_refinesM'),('afterInv_of_mcsIMNQ','afterInv_of_mcsIMN'),('afterInv_of_mcsIMNMQ','afterInv_of_mcsIMNM'),('jDecMRL_ofQ','jDecMRL_of')]
def norm(s):
    for a,b in [('Fl4ProofsKJQ.','Fl4ProofsKJ.'),('Fl4ProofsJQ.','Fl4ProofsJ.'),('Fl4ProofsKQ.','Fl4ProofsK.'),('Fl4ProofsQ.','Fl4Proofs.')]: s=s.replace(a,b)
    for a,b in W: s=re.sub(r'(?<![\w.])'+a+r'(?![\w\'])',b,s)
    return s
nr=0
for f in files:
  if f.endswith('Fl4Proofs.lean'): continue
  a=decls(A,f); b=decls(B,f)
  for k in sorted(set(a)|set(b)):
    if k not in b: print('REMOVED',f,k)
    elif k not in a: print('ADDED',f,k)
    elif a[k]!=b[k]:
      if norm(a[k])==norm(b[k]): print('CHANGED-RENAME',f,k); nr+=1
      else:
        print('CHANGED-REAL',f,k)
        for l in difflib.ndiff([norm(a[k])],[b[k]]):
          if l[0] in '?': print('      ',l.rstrip()[:300])
