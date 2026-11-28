"""swap.py DST SRC name_dst name_src [renames...]: replace DST's block of name_dst (theorem line .. block end) by SRC's block
of name_src, with word renames a=b applied to the inserted text."""
import sys,re
sys.path.insert(0,__file__.rsplit('/',1)[0]); from blk import block
def swap(dst,src,nd,ns,ren):
    a=block(dst,nd); b=block(src,ns)
    assert a and b,(nd,ns)
    txt='\n'.join(b[2])
    for x,y in ren: txt=re.sub(r'(?<![\w.])'+re.escape(x)+r'(?![\w])',y,txt)
    L=open(dst).read().split('\n')
    L[a[0]-1:a[1]]=txt.split('\n')
    open(dst,'w').write('\n'.join(L))
if __name__=='__main__':
    d,s,nd,ns=sys.argv[1:5]; ren=[tuple(r.split('=')) for r in sys.argv[5:]]
    swap(d,s,nd,ns,ren)
