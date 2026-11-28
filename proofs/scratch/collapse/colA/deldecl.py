"""deldecl.py FILE name... : delete top-level declaration blocks (srcdecl ranges, docstring / set_option / variable-in prefixes included)."""
import re,sys
exec(open('scratch/collapse/py/srcdecl.py').read())
PFX_IN=re.compile(r'^(variable|open|omit|include|set_option)\b.*\bin\s*$')
f=sys.argv[1]; names=sys.argv[2:]
lines,bl=blocks(open(f).read())
loc={}
for b in bl:
    while b['start']>0 and PFX_IN.match(lines[b['start']-1]): b['start']-=1
    loc.setdefault(b['name'].split('.')[-1],[]).append(b); loc.setdefault(b['name'],[]).append(b)
rm=[]
for n in names:
    bs=loc.get(n,[])
    assert len(bs)==1,(f,n,len(bs))
    rm.append(bs[0])
for b in sorted(rm,key=lambda b:-b['start']):
    print('DEL',f,b['name'],b['start']+1,b['end'],'|',lines[b['start']][:60])
    del lines[b['start']:b['end']]
open(f,'w').write('\n'.join(lines))
