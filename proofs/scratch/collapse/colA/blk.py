import sys,re
START=re.compile(r'^(theorem|def|structure|abbrev|lemma|instance|inductive|noncomputable def|private theorem|private def|/--|set_option|variable|section|end|namespace|open|@\[|#check|run_cmd|/-)')
def block(path,name):
    L=open(path).read().split('\n')
    pat=re.compile(r'^(private )?(theorem|def|structure|abbrev) '+re.escape(name)+r'(\s|$)')
    for i,l in enumerate(L):
        if pat.match(l):
            j=i+1
            while j<len(L) and not (L[j] and not L[j][0].isspace() and START.match(L[j])): j+=1
            while j>i+1 and L[j-1].strip()=='' : j-=1
            return i+1,j,L[i:j]
    return None
if __name__=='__main__':
    r=block(sys.argv[1],sys.argv[2]); print(r[0],r[1]); print('\n'.join(r[2]))
