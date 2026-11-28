"""Rule 2: qw_r2.py BRANCH OWNLIST -> lines of the branch's own files naming a deleted (DEL) or re-stated (RST) constant/module."""
import subprocess,re,sys
D=open('/tmp/removedhdr.txt').read().split()
ADD=set(open('/tmp/addedhdr.txt').read().split())
GEN={'Spec','mapName','isFixed','trE','stamp','transport','ours'}  # IrqFixXport's own (P3JXport / P3KXport keep same-named defs)
DEL=sorted(set(D)-ADD-GEN)+['IrqFixGenB','IrqFixGen','IrqFixXport','IrqFixA','IrqFixC','JBoot5GenB','JBoot5C','P3JStIrqQ','P3JStEvQ','P3JStTrapQ','P3JSysStQ','WitU34Gen','WitExec','WitUncond','IrqFix.Spec']
RST='MachPlat IrqPlatA MaskMR JDecMRLKQ JDecMRL2Q IrqAckU IrqAckU.of_bound IpiF MachPlatF MachPlatF.toT modelArch_machPlat archT_machPlat invoke_mrM issue_tailM irq_issue_refinesM irq_msi_refinesM irq_ioapic_refinesM irq_remap_refinesM afterInv_of_mcsIMN afterInv_of_mcsIMNM jDecMRL_of jDecMRL2_ofTQ jDecMRLK_ofUQ jVtxHypMU_ofQ sig_inact_false wit_locPlatK locPlatC_wit LocPlat'.split()
RST+=open(sys.argv[3]).read().split() if len(sys.argv)>3 else []
NS=re.compile(r'Fl4Proofs(Q|KQ|JQ|KJQ|QN|QI|JQN|JQI|KJQI)\.')
TOK=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
b,lst=sys.argv[1],sys.argv[2]
for f in open(lst).read().split():
    try: t=subprocess.check_output(['git','show',f'{b}:{f}'],text=True,stderr=subprocess.DEVNULL)
    except Exception: continue
    for i,l in enumerate(t.split('\n'),1):
        toks=set(TOK.findall(l)); last={x.split('.')[-1] for x in toks}|toks|{'.'.join(x.split('.')[-2:]) for x in toks}
        d=sorted(x for x in DEL if x in last); r=sorted(x for x in RST if x in last)
        if NS.search(l): d.append('Fl4ProofsQ-family')
        if d or r: print(f'{"DEL" if d else "RST"} {f}:{i}: {d or r} | {l.strip()[:150]}')
