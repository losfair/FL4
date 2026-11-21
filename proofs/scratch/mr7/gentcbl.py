# XTopJointMRTcbL: XTopJointTcb's decode_invocation_threadJ_step at MachPlat (scripted copy). Run from proofs/.
import re
P='Fl4Proofs/P3/'
L=open(P+'XTopJointTcb.lean').read().split('\n')
def seg(a,b): return '\n'.join(L[a-1:b])
i0=next(i for i,l in enumerate(L) if l.startswith('theorem decode_invocation_threadJ_step '))
a=i0-3  # set_option x2 + docstring start
while not L[a].startswith('set_option'): a-=1
while L[a-1].startswith('set_option'): a-=1
b=next(i for i in range(i0,len(L)) if L[i]=='end')
body='\n'.join(L[a:b])
def R(s,x,y):
    assert x in s,(x[:80]); return s.replace(x,y)
body=R(body,'theorem decode_invocation_threadJ_step ','theorem decode_invocation_threadJ_stepM ')
body=R(body,'(hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)','(hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)\n    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)')
body=R(body,'JAtPre (L := L) arI AR)','JAtPreMV (L := L) arI AR MR)')
body=R(body,'have hHp := tcbInsW_wjl (L := L)','have hHp := tcbInsWM_wjl (L := L) (MR := MR)')
body=R(body,'hJDP.thr hnd hPP hARI.toMask','hJDP.thr hnd hMP hKD hPA hARI.toMask')
body=R(body,'have hR : RestartWJ (st := st) Z s ar σ (WJL (L := L) arI AR Z H Cs (L.ksb s)) :=\n    fun _ hct s1 σ1 h1 h2 => WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2',
 'have hR : RestartWJ (st := st) Z s ar σ (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) :=\n    fun _ hct s1 σ1 h1 h2 => ⟨WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2,\n      mrv_keep hMP hmv (MachT.mtk_setThreadState\' _ _ σ ((), σ1) (mem_of_single h2))⟩')
for n in ['tcb_set_timeoutJ','tcb_set_spaceJ','tcb_set_ipcJ','tcb_configureJ','tcb_set_sched_paramsJ']:
    body=R(body,n+' ',n+'M ')
body=R(body,'hPP.minBudget','hPA.minBudget')
assert 'hPP' not in body and 'JAtPre (L' not in body, [l for l in body.split('\n') if 'hPP' in l]
head=open('scratch/mr7/headTL.lean').read()
open(P+'XTopJointMRTcbL.lean','w').write(head+body+'\n\nend\n\nend\n\nend Fl4Proofs.P3\n')
