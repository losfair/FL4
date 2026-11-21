# XTopJointMRTcb: the TCB install chain (XTopJointTcbInstall/TcbSsp) at WJPM/JAtPreMV (scripted copy). Run from proofs/.
import re
P='Fl4Proofs/P3/'
I=open(P+'XTopJointTcbInstall.lean').read().split('\n')
S=open(P+'XTopJointTcbSsp.lean').read().split('\n')
def seg(L,a,b): return '\n'.join(L[a-1:b])
names=['install_tcb_capJ','install_okJ','install_bufferJ','thread_control_capsJ','top_of_instJ','TcbInsW','restartW',
  'tcb_set_timeoutJ','tcb_set_spaceJ','tcb_set_ipcJ','tcb_configureJ','install_fhJ','install_fhOkJ','ssp_tailJ',
  'tcb_set_sched_paramsJ']
def R(s,a,b,cnt=None):
    assert a in s,(a[:80])
    return s.replace(a,b)
def conv(b):
    for n in names: b=re.sub(r'\b'+n+r'\b',n+'M',b)
    n0=b.count('WJP (L := L) arI AR Z H Cs kb')
    b=b.replace('WJP (L := L) arI AR Z H Cs kb','WJPM (L := L) arI AR MR Z H Cs kb')
    b=b.replace('JAtPre (L := L) arI AR)','JAtPreMV (L := L) arI AR MR)')
    b=b.replace('structure TcbInsWM (AR : A → Fl4Spec.Cr3 → Prop)','structure TcbInsWM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)')
    b=b.replace('TcbInsWM (L := L) arI AR Z','TcbInsWM (L := L) arI AR MR Z')
    return b
V1='''variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {MR : A → Fl4Spec.MachineState → Prop}'''
V2='''variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}'''
a=conv(seg(I,734,1133))
# top_of_instJM: the preempted branch reads JAtPreMV off WJPM
a=R(a,"  · obtain ⟨s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hW'",
      "  · obtain ⟨⟨s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩, hPre⟩ := hW'")
a=R(a,"    exact ⟨s0, a0, σ0, ⟨⟨_, H, Cs, Ac', Lst', D', J0⟩, hns0, hp00⟩, hpp, hspp⟩","    exact hPre")
b=conv(seg(I,1248,1254)+'\n\n'+seg(I,1262,1929))
c=conv(seg(S,467,622))
d=conv(seg(S,742,1450))
d=R(d,"    obtain ⟨s0', a0', σ0', ⟨V0, Ac0, Lst0, D0, J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hWp",
      "    obtain ⟨⟨s0', a0', σ0', ⟨V0, Ac0, Lst0, D0, J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩, hPre⟩ := hWp")
d=R(d,"      exact ⟨s0', a0', σ0', ⟨⟨_, H, Cs, Ac0, Lst0, D0, J0⟩, hns0, hp00⟩, hpp, hspp⟩","      exact hPre")
body='section\n'+V1+'\n\n'+a+'\n\n'+c+'\n\nend\n\nsection\n'+V2+'\n\n'+b+'\n\n'+d+'\n\nend\n'
for l in body.split('\n'):
    assert not re.search(r'\bWJP\b|JAtPre\b(?!MV)',l) or l.lstrip().startswith(('/-','`','--')) or '`' in l, l
head=open('scratch/mr7/headT.lean').read()
open(P+'XTopJointMRTcb.lean','w').write(head+body+'\nend\n\nend Fl4Proofs.P3\n')
