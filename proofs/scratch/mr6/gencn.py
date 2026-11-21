# XTopJointMRCnode: XTopJointWJLRestart's CNode Revoke/Delete decode at MachPlat (scripted copy). Run from proofs/.
P='Fl4Proofs/P3/'
L=open(P+'XTopJointWJLRestart.lean').read().split('\n')
def seg(a,b): return '\n'.join(L[a-1:b])
var=seg(42,47)
body=seg(122,244)+'\n\n'+seg(257,323)
def R(s,a,b,cnt=None):
    assert a in s,(a[:60])
    return s.replace(a,b) if cnt is None else s.replace(a,b,cnt)
b=body
b=R(b,'theorem cn_del_topJL ','theorem cn_del_topJLM ')
b=R(b,'(EJL (L := L) arI AR Z H Cs kb K) (EJP (L := L) arI AR Z H Cs kb K)','(EJLM (L := L) arI AR MR Z H Cs kb K) (EJPM (L := L) arI AR MR Z H Cs kb K)')
b=R(b,'(JAtPre (L := L) arI AR)','(JAtPreMV (L := L) arI AR MR)')
b=R(b,"obtain ⟨-, ⟨V, Ac', Lst', D', J', -⟩, -⟩ := hE'","obtain ⟨-, ⟨⟨V, Ac', Lst', D', J', -⟩, -⟩, -⟩ := hE'")
b=R(b,"obtain ⟨-, s0, a0, σ0, ⟨V, Ac', Lst', D', J0, -, hns0, -, hp00⟩, hpp, hspp, hDom, hMO⟩ := hE'","obtain ⟨-, ⟨-, -, -, -, -, -, hDom, hMO⟩, hPre⟩ := hE'")
b=R(b,"exact ⟨s0, a0, σ0, ⟨⟨_, H, Cs, Ac', Lst', D', J0⟩, hns0, hp00⟩, hpp, hspp⟩","exact hPre")
for n in ['revoke','delete']:
    b=R(b,f'theorem decode_invocation_cnode_{n}JL ',f'theorem decode_invocation_cnode_{n}JLM ')
b=R(b,'(J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)\n    (hJD : JDelHypL (L := L) arI AR Z.th)',
      '(J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)\n    (hMP : MachPlat arI MR) (hmv : MRV MR ar σ) (hJD : JDelHypLM (L := L) arI AR MR Z.th)')
b=R(b,'PPHypDW (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) Z.th',
      'PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPM (L := L) arI AR MR Z H Cs kb) Z.th')
b=R(b,'(EJL (L := L) arI AR Z H Cs (L.ksb s) K)','(EJLM (L := L) arI AR MR Z H Cs (L.ksb s) K)')
b=R(b,'(EJP (L := L) arI AR Z H Cs (L.ksb s) K)','(EJPM (L := L) arI AR MR Z H Cs (L.ksb s) K)')
b=R(b,'rppHyp_fullW arI (WJL (L := L) arI AR Z H Cs (L.ksb s)) (WJP (L := L) arI AR Z H Cs (L.ksb s))',
      'rppHyp_fullW arI (WMR MR (WJL (L := L) arI AR Z H Cs (L.ksb s))) (WJPM (L := L) arI AR MR Z H Cs (L.ksb s))')
b=R(b,'EJL.restart arI J hni hsg hP0 hLv hDE hct','EJLM.restart arI J hni hMP hmv hsg hP0 hLv hDE hct')
b=R(b,'cn_del_topJL arI J h','cn_del_topJLM arI J h')
b=R(b,'theorem decode_invocation_cnodeJ_stepsL ','theorem decode_invocation_cnodeJ_stepsLM ')
b=R(b,'(hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)','(hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)\n    (hPA : PPPlatA arI AR) (hmv : MRV MR ar σ)')
b=R(b,'''    fun kb => jPreemptHypL arI hARI.toARKeep hT hnd hPP Z H Cs kb rfl''','''    fun kb => jPreemptHypLM arI hARI.toARKeep hT hnd hMP hPA Z H Cs kb rfl''')
b=R(b,'have hJP : ∀ kb, PPHypDW (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) Z.th :=',
      'have hJP : ∀ kb, PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPM (L := L) arI AR MR Z H Cs kb) Z.th :=') if 'have hJP : ∀ kb, PPHypDW (L := L) arI (WJL' in b else b
b=R(b,'have hJD := hJDP.jDelHypL arI hT hnd hPP hARI.toMask','have hJD := hJDP.jDelHypLM arI hT hnd hMP hKD hPA hARI.toMask')
b=R(b,'decode_invocation_cnode_revokeJL arI s ar σ J hni hJD hJP','decode_invocation_cnode_revokeJLM arI s ar σ J hni hMP hmv hJD hJP')
b=R(b,'decode_invocation_cnode_deleteJL arI s ar σ J hni hJD hsg','decode_invocation_cnode_deleteJLM arI s ar σ J hni hMP hmv hJD hsg')
assert 'JAtPre (L' not in b and 'EJL ' not in b and 'PPPlat arI' not in b, [l for l in b.split('\n') if 'JAtPre (L' in l or 'EJL ' in l or 'PPPlat arI' in l]
head=open('scratch/mr6/headCn.lean').read()
var=var.replace('{AR : A → Fl4Spec.Cr3 → Prop}','{AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}')
open(P+'XTopJointMRCnode.lean','w').write(head.replace('@VAR@',var)+b+'\n\nend\n\nend\n\nend Fl4Proofs.P3\n')
