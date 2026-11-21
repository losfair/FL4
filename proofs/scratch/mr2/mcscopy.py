import re,sys
P3='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-tcbj/proofs/Fl4Proofs/P3/'
POST="      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by"
def copy(fn,name):
    s=open(P3+fn).read()
    i=s.index('theorem '+name+' ')
    j=re.search(r'\n(?=(set_option|/--|theorem |variable|def |end\b|section))',s[i:]).start()+i
    t=s[i:j].rstrip()
    k=t.index(POST)
    stmt=t[:k]; body=t[k+len(POST):]
    # statement: add hyps before the final ") :\n    syscall.mcs_preemption_point"
    m=stmt.rindex(') :\n    syscall.mcs_preemption_point')
    stmt=stmt[:m]+')\n    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :\n    syscall.mcs_preemption_point'+stmt[m+len(') :\n    syscall.mcs_preemption_point'):]
    stmt=stmt.replace('theorem '+name+' ','theorem '+name+'M ',1)
    q=stmt.index('syscall.mcs_preemption_point st arI s a ⦃ r =>')
    keypost=stmt[q:]+"      JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ⦄"
    # endpoints
    lines=body.split('\n'); n=0
    for ix,l in enumerate(lines):
        mm=re.search(r"(fail_pp_\w+ .*?) hy, (Z[^⟩]*J'?)⟩\s*$",l)
        if mm:
            if 'fail_pp_charge' in l: pf="MachF.mfk_chargeBudget _ _ σ ((), σ') (by rw [h1']; rfl)"
            elif 'checkBudget_suff' in l or 'fail_pp_inact' in l: pf='rfl'
            else: raise Exception('unknown endpoint '+l)
            lines[ix]=l[:mm.start(2)]+'⟨'+mm.group(2)+'⟩, '+pf+'⟩'; n+=1
        if l.rstrip().endswith('fail_pp_sched hsch hz hy,') and lines[ix+1].strip()=="Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩":
            lines[ix+1]="      ⟨Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩, MachF.mfk_checkBudget σ z hz⟩"; n+=1
    assert n>=1,(name,n)
    body='\n'.join('  '+x if x.strip() else x for x in lines)
    stmt_full=stmt+"      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ⦄ := by\n"
    return ('set_option maxHeartbeats 16000000 in\n/-- `'+name+'` with `MR` and `ValidIrqMasks` after (module docstring). -/\n'+stmt_full+
      '  have key : '+keypost.replace('\n','\n  ')+' := by'+body+
      "\n  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))\n    fun _ ⟨⟨σ', h1, h2, hJ, hF⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF⟩\n")
L=[x.split(':') for x in sys.argv[2].split(',')]
out=[copy(f,n) for f,n in L]
open(sys.argv[1],'w').write('\n'.join(out))
