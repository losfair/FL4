# MKD walks of the FL4 deletion functions (MachKeepD body). usage: python3 mkdgen.py order.txt > body
import re,sys
s=open('Fl4Core/Funs.lean').read()
order=[l.strip() for l in open(sys.argv[1]) if l.strip()]
SKIP={'interrupt.set_irq_state','interrupt.deleted_irq_handler','objects.post_cap_deletion','cdt.empty_slot',
      'vcpu.revoke_ports_loop.body','vspace.delete_asid_pool_loop.body','vcpu.revoke_ports_loop','vspace.delete_asid_pool_loop'}
def split_top(t,sep):
    out=[];d=0;cur=''
    i=0
    while i<len(t):
        if t[i] in '([{': d+=1
        if t[i] in ')]}': d-=1
        if d==0 and t.startswith(sep,i): out.append(cur.strip()); cur=''; i+=len(sep); continue
        cur+=t[i]; i+=1
    out.append(cur.strip()); return out
DEEP={'vspace.delete_asid'}
LOOPS=open('scratch/mr6/loops.lean').read().split('\n\n')
for n in order:
    if n=='vcpu.revoke_ports_loop': print(LOOPS[1]+'\n')
    if n=='vspace.delete_asid_pool_loop': print(LOOPS[0]+'\n')
    if n in SKIP: continue
    m=re.search(r'\ndef '+re.escape(n)+r'\n(.*?)\n  :=',s,re.S)
    hdr=' '.join(m.group(1).split())
    binders=re.findall(r'\(([^():]+) : ([^()]+(?:\([^()]*\))?[^()]*)\)',hdr.split(':\n')[0])
    # explicit binders in order
    bs=re.findall(r'\(([\w\s«»]+?) : ((?:[^()]|\([^()]*\))+?)\)',hdr)
    names=[];decl=[]
    for ns,ty in bs:
        for x in ns.split():
            if x in ('machineStoreInst','machineArchInst'): continue
            names.append(x)
            if x not in ('s','a'): decl.append('{%s : %s}'%(x,ty.strip()))
    ret=hdr.rsplit(':',1)[1].strip()
    assert ret.startswith('Result'),(n,ret)
    rt=ret[len('Result'):].strip()
    if rt.startswith('(') and rt.endswith(')'): rt=rt[1:-1]
    if "A" not in split_top(rt,"×"): print("--",n,rt,file=sys.stderr)
    comps=split_top(rt,'×')
    if "A" not in comps: continue
    k=comps.index('A'); proj='r'+'.2'*k+('' if k==len(comps)-1 else '.1')
    nm=n.replace('.','_')
    args=' '.join(names)
    print(("set_option maxRecDepth 8000 in\n" if n in DEEP else "")+f"theorem MKD.{nm} {{s : S}} {{a : A}} {' '.join(decl)} (h : AR a c₀) :\n    {n} st arI {args} ⦃ r => AR {proj} c₀ ⦄ := by\n  unfold {n}; mkd_walk{"\x27" if n in DEEP else ""}\n")
