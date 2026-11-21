/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr6): **CNode Revoke and Delete
at `MachPlat`**: XTopJointWJLRestart's `decode_invocation_cnode_{revoke,
delete}JL` / `decode_invocation_cnodeJ_stepsL` with the deletion at
`WMR MR WJL` (XTopJointMRDel: `JDelHypLM`, `jPreemptHypLM`), so the CNode cap's
decode ends in `XCapP JAt (JAtPreMV MR)` (what mr4's `decOK_JM` asks of the
`JPreDecHyp` kinds) from `MRV MR ar σ` at the decode's state and `MachPlat`
[P] + `MRKeepD` [P] + `PPPlatA` [P]: no `PPPlat`. Generated:
scratch/mr6/gencn.py + headCn.lean (the copies differ from the originals only
in the invariant, `EJLM`/`EJPM`, the restart's `MRV` (`setThreadState` keeps
`msFT`: `mtk_setThreadState'`), and `cn_del_topJLM`'s preempted branch, which
reads `JAtPreMV` off `WJPM`).
-/
import Fl4Proofs.P3.XTopJointWJLRestart
import Fl4Proofs.P3.XTopJointMRDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

@VAR@

/-- **`DelE` and `WMR MR WJL`** (`JDelHypLM`'s invariant). -/
abbrev EJLM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (K : Nat) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WMR MR (WJL (L := L) arI AR Z H Cs kb) s a σ G

/-- **`DelE` and `WJPM`** (after a preemption). -/
abbrev EJPM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (K : Nat) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJPM (L := L) arI AR MR Z H Cs kb s a σ G

/-- **The caller's restart keeps `EJLM`**: `EJL.restart` and `MRV` (the
restart's `setThreadState` keeps `msFT`, the arch state is kept). -/
theorem EJLM.restart {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hM : MachPlat arI MR)
    (hmv : MRV MR ar σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {K : Nat} (hDE : DelE (L := L) Z.th K s σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame Z.th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      EJLM (L := L) arI AR MR Z H Cs (L.ksb s) K s1 ar σ1 Z.G := fun s1 σ1 hs1 hS hst =>
  let h := EJL.restart arI J hni hsg hP0 hLv hDE hct s1 σ1 hs1 hS hst
  ⟨h.1, h.2, mrv_keep hM hmv (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single hst))⟩

