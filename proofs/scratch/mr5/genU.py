# generates Fl4Proofs/P3/UtRetResetJM.lean (run from proofs/)
import sys
P='Fl4Proofs/P3/'
def rd(f): return open(P+f).read()
def sl(src,a,b):
    i=src.index(a); j=src.index(b,i); return src[i:j]
def must(s,a,b,cnt=1):
    if s.count(a)!=cnt: sys.exit('MISSING %r count %d'%(a[:90],s.count(a)))
    return s.replace(a,b)
T=rd('UtResetTopJ.lean')
r=sl(T,'set_option maxHeartbeats 16000000 in\n/-- **FL4\'s `reset_untyped` at `J`**','\nend\n')
r=must(r,'theorem JAtZ.reset_untypedJ ','theorem JAtZ.reset_untypedJM ')
r=must(r,'/-- **FL4\'s `reset_untyped` at `J`** (module docstring). -/','/-- **FL4\'s `reset_untyped` at `J` under `MachPlat`** (module docstring). -/')
r=must(r,'(hPP : PPPlat arI AR)','(hMP : MachPlat arI MR) (hPA : PPPlatA arI AR)')
r=must(r,'''(hXc : ∀ y, IsSlot Z.th y → ∀ k q, Vs.VNeed (capV (L.mem s) y) k q → q ∈ Vs.lvlSet XP X4 X3 X2 X1 k) :''',
 '''(hXc : ∀ y, IsSlot Z.th y → ∀ k q, Vs.VNeed (capV (L.mem s) y) k q → q ∈ Vs.lvlSet XP X4 X3 X2 X1 k)
    (hMR : MR a σ.machineState) (hVT : ValidMachineTime σ) (hVIM : ValidIrqMasks σ) :''')
r=must(r,'ResetJPost (L := L) arI AR (','ResetJPostM (L := L) arI AR MR (')
r=must(r,'JAtZ.reset_loopJ hAK hA hnd hPP hrcb','JAtZ.reset_loopJM hAK hA hnd hMP hPA hrcb')
r=must(r,'hRM hncD hR0D rfl hz (fun _ _ _ => rfl)','hRM hncD hR0D rfl hz (fun _ _ _ => rfl)\n      (hMP.frame a _ _ hMR rfl rfl rfl rfl) hVT hVIM')
R=rd('UtRetResetJ.lean')
u=sl(R,'set_option maxHeartbeats 8000000 in\n/-- **The retype with a reset at `J`**','\n\nvariable (arI) in')
u=must(u,'theorem JAtZ.utResetJ ','theorem JAtZ.utResetJM ')
u=must(u,'/-- **The retype with a reset at `J`** (module docstring). -/','/-- **The retype with a reset at `J` under `MachPlat`** (module docstring). -/')
u=must(u,'(hPP : PPPlat arI AR)','(hMP : MachPlat arI MR) (hPA : PPPlatA arI AR)')
u=must(u,'(hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv) (blk call don : Bool) :',
 '(hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv)\n    (hMR : MR ar σ.machineState) (hVT : ValidMachineTime σ) (hVIM : ValidIrqMasks σ) (blk call don : Bool) :')
u=must(u,'      UtRetPostJ (L := L) arI AR σ blk call don','      UtRetPostJM (L := L) arI AR MR σ blk call don')
u=must(u,'exact utRetPostJ_of_body hst1','exact utRetPostJM_of_body hst1')
u=must(u,'''  refine retype_reset_wp arI s1 ar _ _ nt us dest off win false
    (J1.reset_untypedJ hAK hA hnd hPP hrcb''','''  have hms1' : σ1.machineState = σ.machineState := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hcT1 : σ1.curTime = σ.curTime := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have his1 : σ1.interruptStates = σ.interruptStates := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hMR1 : MR ar σ1.machineState := hms1' ▸ hMR
  have hVT1 : ValidMachineTime σ1 := by unfold ValidMachineTime; rw [hms1', hcT1]; exact hVT
  have hVI1 : ValidIrqMasks σ1 := by unfold ValidIrqMasks; rw [hms1', his1]; exact hVIM
  refine retype_reset_wp arI s1 ar _ _ nt us dest off win false
    (J1.reset_untypedJM hAK hA hnd hMP hPA hrcb''')
u=must(u,'(hVM s1 hs1) Vs.needR_roots)','(hVM s1 hs1) Vs.needR_roots hMR1 hVT1 hVI1)')
u=must(u,'exact utRetPostJ_of_preempt hst1 hmem he hpre hX','exact utRetPostJM_of_preempt hst1 hmem he hpre hX')
u=must(u,'(fun res h => utRetPostJ_of_reset hst1 hmem h)','(fun res h => utRetPostJM_of_reset hst1 hmem h)')
V='''variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
  {MR : A → Fl4Spec.MachineState → Prop}
'''
V2='''variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}
'''
head=open('scratch/mr5/headU.lean').read()
tail=open('scratch/mr5/tailU.lean').read()
out=head+'section ResetM\n'+V+'\n'+r+'\nend ResetM\n\nsection UtResetM\nopen Fl4Proofs.P1\n'+V2+'\n'+u+'\n\nend UtResetM\n'+tail
open(P+'UtRetResetJM.lean','w').write(out)
print('ok',len(out.splitlines()))
