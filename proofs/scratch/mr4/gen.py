# generates Fl4Proofs/P3/XTopJointKEntry13P.lean from the originals (run from proofs/)
import re,sys
P='Fl4Proofs/P3/'
def rd(f): return open(P+f).read()
def sl(src,a,b):
    i=src.index(a); j=src.index(b,i); return src[i:j]
def must(s,a,b,cnt=1):
    if s.count(a)!=cnt: sys.exit('MISSING %r count %d'%(a[:80],s.count(a)))
    return s.replace(a,b)
E=rd('XTopJointEntry.lean')
# ---------- decOK_JM
d=sl(E,'theorem decOK_J [','  all_goals exact hN\n')+'  all_goals exact hN\n'
d=must(d,'theorem decOK_J [','theorem decOK_JM [')
d=must(d,'    (hG : JEntryGlob (L := L) arI AR Z.th)','    (hG : JEntryGlobM (L := L) arI AR Z.th)')
d=must(d,'''    (hN : JPath (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR)''','''    (hN : JPath (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c)
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState) (hV : ValidMachineTime σ)
    (hVI : ValidIrqMasks σ) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR)''')
d=d.replace('hG.pp.minBudget','hG.ppA.minBudget')
pd='    exact hPD hR hV hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc (fun h => h)\n      excaps buffer hXO hXN hLb hA5 hN\n'
i=d.index('  case CNode p r gs g =>'); j=d.index('  case IoPort first last z =>')
d=d[:i]+'  case CNode p r gs g =>\n'+pd+'  case Thread p =>\n'+pd+d[j:]
i=d.index('  case Untyped p sb fi dev =>'); j=d.index('  all_goals exact hN\n')
d=d[:i]+'  case Untyped p sb fi dev =>\n'+pd+'  all_goals exact XCapP.reXP arI hN (specDec_noPreK (by trivial))\n'
d=must(d,'    · exact hOpen h0','    · exact XCapP.reXP arI (hOpen h0) (specDec_noPreK (by trivial))')
d=must(d,'      · exact hV (Or.inr hEP)','      · exact XCapP.reXP arI (hV (Or.inr hEP)) (specDec_noPreK (by trivial))')
d=must(d,'    · exact hV (Or.inl rfl)','    · exact XCapP.reXP arI (hV (Or.inl rfl)) (specDec_noPreK (by trivial))')
# Frame's local hV shadows our hV : rename ours
d=d.replace('hPD hR hV hVI','hPD hR hVT hVI').replace('(hV : ValidMachineTime σ)','(hVT : ValidMachineTime σ)')
# ---------- handle_invocation_entryJM (refinesJ body)
r=sl(E,'theorem handle_invocation_refinesJ [','\nend\n')
body=r[r.index(':= by\n')+len(':= by\n'):]
body=must(body,'(JAtPre (L := L) arI AR) true s ar σ Z.th Z.G','(JAtPreMV (L := L) arI AR MR) true s ar σ Z.th Z.G')
body=body.replace('hH.glob.tot','hG.tot').replace('hH.atE.','hE.')
body=must(body,'exact decOK_J arI s ar σ J hH.glob hH.atE ct','exact decOK_JM arI s ar σ J hG hE ct')
body=must(body,'(hH.path sl c e exs hsl hc hget h1 h2)','(hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs hsl hc hget h1 h2)\n    hPD hR hVT hVI')
if 'hH' in body: sys.exit('hH left')
hie='''set_option maxHeartbeats 4000000 in
/-- **One invocation at `J` under `MachPlat`** (module docstring):
`handle_invocation_entryJ` with `JEntryGlobM` and `JPreDecHyp`, `JAtPreMV` after
a preempted invocation. -/
theorem handle_invocation_entryJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct is_call blocking can_donate first_phase cptr)
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ) :
    syscall.handle_invocation st arI s ar is_call blocking can_donate first_phase cptr ⦃ res =>
      HIPostMXP (L := L) (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) true σ is_call blocking can_donate
        first_phase (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
'''+body
# ---------- invoke_afterJM, dispatch_invokeJM
Dp=rd('XTopJointDispatch.lean')
ia=sl(Dp,'theorem invoke_afterJ [','theorem regIdx_reply')
ia=must(ia,'theorem invoke_afterJ [','theorem invoke_afterJM [')
ia=must(ia,'    (hG : JEntryGlob (L := L) arI AR Z.th)','    (hG : JEntryGlobM (L := L) arI AR Z.th)')
ia=must(ia,'''(L.mem s (regA ct layout.reg.CAP)))
    (Q :''','''(L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
    (Q :''')
ia=must(ia,'      JAtPre (L := L) arI AR s1 a1 σ1 →','      JAtPreMV (L := L) arI AR MR s1 a1 σ1 →')
ia=must(ia,'(handle_invocation_entryJ arI s ar σ J ct hct call bl don false _ hG hE hP)','(handle_invocation_entryJM arI s ar σ J ct hct call bl don false _ hG hE hP hPD hR hVT hVI)')
di=sl(Dp,'theorem dispatch_invokeJ [','/-- FL4\'s receiving syscall numbers')
di=must(di,'theorem dispatch_invokeJ [','theorem dispatch_invokeJM [')
di=must(di,'    (hG : JEntryGlob (L := L) arI AR Z.th)','    (hG : JEntryGlobM (L := L) arI AR Z.th)')
di=must(di,'''(L.mem s (regA ct layout.reg.CAP)))
    (Q :''','''(L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
    (Q :''')
di=must(di,'      JAtPre (L := L) arI AR s1 a1 σ1 →','      JAtPreMV (L := L) arI AR MR s1 a1 σ1 →')
di=must(di,'invoke_afterJ arI s ar σ J ct hct call bl don hG hE hP Q hPre','invoke_afterJM arI s ar σ J ct hct call bl don hG hE hP hPD hR hVT hVI Q hPre')
# ---------- mid
K8=rd('XTopJointKEntry8.lean')
mi=sl(K8,'theorem mid_invRecvJ [','set_option maxHeartbeats 4000000 in\n/-- **`dispatch_syscall` for ReplyRecv')
dm=sl(K8,'theorem dispatch_midJ [','set_option maxHeartbeats 4000000 in\n/-- **Every native dispatch')
PLAT_OLD='''    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
'''
PLAT_NEW='''    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
'''
MRH='''    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR0 : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
'''
for nm in ['mi','dm']:
    t=locals()[nm]
    t=must(t,'    (hG : JEntryGlob (L := L) arI AR Z.th)','    (hG : JEntryGlobM (L := L) arI AR Z.th)')
    t=must(t,PLAT_OLD,MRH+PLAT_NEW)
    locals()[nm]=t
    if nm=='mi': mi=t
    else: dm=t
mi=must(mi,'theorem mid_invRecvJ [','theorem mid_invRecvJM [')
mi=must(mi,'''  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJ arI s ar σ J ct hct false false true true _ hG hE hP)
    fun res h => h.mid arI (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM⟩ | ⟨hr1, hy1, hrel, hX⟩⟩''','''  refine WP.spec_bind (WP.spec_mono (handle_invocation_entryJM arI s ar σ J ct hct false false true true _ hG hE hP
    hPD hR0 hVT hVI)
    fun res h => And.intro (h.toPreMV.mid arI (MidRun.jMidRunHyp_of hW) (J.midEntry hni hE.cnf)) h) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨⟨y1, σm⟩, hy, ⟨hr1, hy1, hM⟩ | ⟨hr1, hy1, hrel, hX⟩⟩, hMV⟩''')
mi=must(mi,'''  · dsimp only at hr1 hy1 hrel hX
    subst hr1 hy1''','''  · dsimp only at hr1
    subst hr1
    obtain ⟨⟨u', σm'⟩, hy', hc', hrel', hX'⟩ := hMV
    have hu' : u' = .error () := by
      rcases hc' with ⟨h1, -⟩ | ⟨-, h2⟩
      · cases h1
      · exact h2
    subst hu'
    rw [if_pos rfl] at hX\'''')
mi=must(mi,'refine WP.spec_bind (hPre_ofZQI hARI hA hnd hPP hmrt hIP hNS hG.maxTU hG.tu s1 a1 σm hrel hX) ?_','refine WP.spec_bind (hPre_ofZQIM hARI hA hnd hM hMK hPA hIA hmrt hNS hG.maxTU hG.tu s1 a1 σm\' hrel\' hX\') ?_')
mi=must(mi,'(mem_bindE_err hy), Or.inr ⟨rfl, hQ⟩⟩','(mem_bindE_err hy\'), Or.inr ⟨rfl, hQ⟩⟩')
dm=must(dm,'theorem dispatch_midJ [','theorem dispatch_midJM [')
dm=must(dm,'have h := mid_invRecvJ s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hARI hA hnd hPP hmrt hIP hNS','have h := mid_invRecvJM s ar σ J hni ct hct rg sr cr hn.reg hG hE hP hW hR hPD hR0 hVT hVI hARI hA hnd hM hMK hPA hIA hmrt hNS')
# ---------- kernel entry (9M body)
K9=rd('XTopJointKEntry9M.lean')
ke=sl(K9,'theorem kernel_entryJ9M [','\nend\n')
ke=must(ke,'theorem kernel_entryJ9M [','theorem kernel_entryJ13P [')
ke=must(ke,'(J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)','(J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)\n    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ)')
ke=must(ke,'        KDispHyps9M (L := L) arI AR Z\' H\' Cs\' D\' s\' a\' σb n c)','        KDispHyps13P (L := L) arI AR MR Z\' H\' Cs\' D\' s\' a\' σb n c)')
ke=must(ke,PLAT_OLD.replace('    (hmrt','    (hmrt').replace('    (hIP : IrqPlat arI AR)\n','')+'    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)\n    (hIP : IrqPlat arI AR)\n',
  PLAT_NEW+'    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)\n')
ke=must(ke,'  refine WP.spec_bind hBud ?_\n  rintro ⟨b, s2, a1⟩ ⟨hTr, hFa⟩','  refine WP.spec_bind (WP.spec_and hBud (budget_ok_mr hM hMK hA hR _)) ?_\n  rintro ⟨b, s2, a1⟩ ⟨⟨hTr, hFa⟩, hMRb⟩')
ke=must(ke,'''    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩''','''    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI''')
ke=must(ke,'''    refine WP.spec_bind (dispatch_all9M s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hARI hA hnd hPP hmrt hmb hIP hNS hmax htu) ?_''','''    refine WP.spec_bind (dispatch_all13P s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hMRσb hVIσb hARI hA hnd hM hMK hPA hIA hmrt hNS hmax htu) ?_''')
g=sl(E,'structure JEntryGlob (AR','/-- **The premises at the entry state**')
g=must(g,'structure JEntryGlob (AR','structure JEntryGlobM (AR')
g=must(g,'''  /-- [P] the preemption point's platform (`PPPlat`). -/
  pp : PPPlat arI AR''','''  /-- [P] the arch-only part of the preemption point's platform (`PPPlatA`:
  the IRQ read keeps `AR`, `min_budget`); the clock and the IRQ line are
  `MachPlat`'s, at the top. -/
  ppA : PPPlatA arI AR''')
head=open('scratch/mr4/head.lean').read().replace('@@GLOB@@',g)
mid=open('scratch/mr4/mid.lean').read()
tail=open('scratch/mr4/tail.lean').read()
out=head+'set_option maxHeartbeats 4000000 in\n'+d+'\n'+hie+'\nend\n\nsection\nvariable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)\nvariable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}\n  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}\n\nset_option maxHeartbeats 4000000 in\n'+ia+'set_option maxHeartbeats 4000000 in\n'+di+'\nend\n\nsection\nvariable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}\nvariable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}\n  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}\n\nset_option maxHeartbeats 4000000 in\n'+mi+'set_option maxHeartbeats 4000000 in\n'+dm+mid+'set_option maxHeartbeats 16000000 in\n'+ke+tail
open(P+'XTopJointKEntry13P.lean','w').write(out)
print('ok',len(out.splitlines()))
