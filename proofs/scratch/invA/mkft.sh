cd $(dirname $0); python3 gen.py ft skipFT.txt FTK ' L' bodyFT.lean >/dev/null || exit 1
D=/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-sc/proofs/Fl4Proofs/P3
python3 - "$D" <<'PY'
import sys,re
D=sys.argv[1]
head=open('ftHead.lean').read(); body=open('bodyFT.lean').read()
blocks=re.split(r'\n\n(?=theorem |/--|set_option)',body)
N=6; k=(len(blocks)+N-1)//N
parts=[ '\n\n'.join(blocks[i*k:(i+1)*k]) for i in range(N)]
pre='''import Fl4Proofs.P3.SpecInvFaultTcbs%s
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

'''
post='\nend\n\nend Fl4Proofs.P3.SInv\n'
open(D+'/SpecInvFaultTcbsF1.lean','w').write(head+parts[0]+post)
for i in range(1,N):
    open(D+'/SpecInvFaultTcbsF%d.lean'%(i+1),'w').write('/- invA2: FaultTcbsS frame lemmas, part %d (generated; see SpecInvFaultTcbsF1). -/\n'%(i+1)+pre%('F%d'%i)+parts[i]+post)
PY
