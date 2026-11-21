cd $(dirname $0); python3 gen.py oi skip.txt OIK ' N' bodyOI.lean || exit 1
D=/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-sc/proofs/Fl4Proofs/P3
python3 - "$D" <<'PY'
import sys,re
D=sys.argv[1]
head=open('oiHead.lean').read(); body=open('bodyOI.lean').read()
blocks=re.split(r'\n\n(?=theorem |/--|set_option)',body)
N=6; k=(len(blocks)+N-1)//N
parts=[ '\n\n'.join(blocks[i*k:(i+1)*k]) for i in range(N)]
pre='''import Fl4Proofs.P3.SpecInvAllO%s
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

'''
post='\nend\n\nend Fl4Proofs.P3.SInvAll\n'
open(D+'/SpecInvAllO1.lean','w').write(head+parts[0]+post)
for i in range(1,N):
    open(D+'/SpecInvAllO%d.lean'%(i+1),'w').write('/- g1c: OnlyIdle frame lemmas, part %d (generated; see SpecInvAllO1). -/\n'%(i+1)+pre%(i)+parts[i]+post)
PY
