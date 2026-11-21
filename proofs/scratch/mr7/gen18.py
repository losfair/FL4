# XTopJointKEntry18P: jPreDecHyp_of18's Thread case = XTopJointEntry decOK_J's Thread case at MachPlat. Run from proofs/.
P='Fl4Proofs/P3/'
L=open(P+'XTopJointEntry.lean').read().split('\n')
i=next(k for k,l in enumerate(L) if l=='  case Thread p =>')
j=next(k for k in range(i+1,len(L)) if L[k].startswith('  case '))
b='\n'.join(L[i:j])
def R(s,x,y):
    assert x in s,(x[:80]); return s.replace(x,y)
b=R(b,"""    by_cases hn : lbl = fl4_abi.label.TCBSetEPTRoot
    · exact hEpt hn
""","""    by_cases hn : lbl = fl4_abi.label.TCBSetEPTRoot
    · -- SetEPTRoot [scope] (`JVtxScope`, at `JAtPre`): no installing label, so no preemption (`XCapP.reXP`)
      have hx := hEpt hn
      subst hLb
      obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon lbl
      refine XCapP.reXP (arI := arI) hx fun inv hD => ?_
      rw [specDec_thread p hd] at hD
      have e : lbl.val = fl4_abi.label.TCBSetEPTRoot.val := by rw [hn]
      exact thread_noPre_of hlbl ⟨by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot],
        by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot], by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot],
        by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot], by rw [e]; simp [fl4_abi.label.TCBSetEPTRoot]⟩ inv hD
""")
b=R(b,'hG.pp.minBudget','hG.ppA.minBudget')
b=R(b,'decode_invocation_threadJ_step arI','decode_invocation_threadJ_stepM arI')
b=R(b,'hG.delParts hE.sg hLv hG.nd hG.pp hE.rd0 hE.ctnq hG.timeAg','hG.delParts hE.sg hLv hG.nd hM hKD hG.ppA ⟨hR, hVT, hVI⟩ hE.rd0 hE.ctnq hG.timeAg')
assert 'hG.pp ' not in b and 'hG.pp\n' not in b
t=open('scratch/mr7/t18.lean').read()
open(P+'XTopJointKEntry18P.lean','w').write(t.replace('@THREAD@',b))
