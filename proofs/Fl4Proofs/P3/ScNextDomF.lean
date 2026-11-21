/-
P3 (DESIGN.md §9), scheduler: **the domain switch up to the FPU**
(KENTRY-PLAN.md sch4 (A)): ScNextDomB's `ArchNd` [P] is false whenever the
spec has an FPU owner (its `ArchKeeps` keeps the heap; l4v
`arch_prepare_next_domain = switch_local_fpu_owner None` saves the machine
FPU image into the owner's TCB and clears its `tcbCurFpu`). Restated:

* `ArchNdF` [P]: at a state whose FPU owner is a TCB (`FpuOwnOK` [J],
  ScArchF), the spec's `arch_prepare_next_domain` has one outcome, with
  `SchedRel`/`NtfnStateRel` kept at FL4's unchanged store, `ArchKeepsF`
  (the heap up to the old owner's saved FPU image and `tcbCurFpu`,
  registers kept), the domain list/index/start kept and no FPU owner after.
  True at reachable states (`valid_cur_fpu`; the opaque `enableFpu`/
  `disableFpu`/`readFpuState` machine operations with one outcome, as for
  every arch premise). FL4 has no FPU step at a domain switch (its lazy
  owner stays live; harmless with `numDomains = 1`, and no relation reads
  the spec's FPU fields).
* `scnt_refines0F`: ScNextDomB's `scnt_refines0` with `ArchSwF`, `ArchNdF`,
  `FpuOwnOK σ`, and `HeapEqUpToFpu σ σ'` in the post (supersedes it).
-/
import Fl4Proofs.P3.ScNextDomB
import Fl4Proofs.P3.ScScheduleF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **`arch_prepare_next_domain` up to the FPU** [P] (module docstring). -/
def ArchNdF (st : machine.Store S) [L : P1.LawfulStore st] (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ → FpuOwnOK σ →
    ∃ σ1, Fl4Spec.archPrepareNextDomain (Z := Unit) σ = ({((), σ1)}, False) ∧ SchedRel st N T C c s σ1 ∧
      NtfnStateRel N T (L.mem s) σ1 ∧ ArchKeepsF σ σ1 ∧ σ1.domainList = σ.domainList ∧
      σ1.domainIndex = σ.domainIndex ∧ σ1.domainStartIndex = σ.domainStartIndex ∧
      σ1.archState.x64CurrentFpuOwner = none

set_option maxHeartbeats 2000000 in
/-- **`schedule_choose_new_thread` refines l4v's, with the domain switch**:
as `schedule_choose_new_thread_refines` when the domain time is nonzero;
when it is 0, from `NdOK` (ScNextDom: `next_domain` back to entry 0 on both
sides) and `ArchNd` [P], `next_domain` then `choose_thread` at FL4's
`ndS s t` and the spec's `ndSt σa t'` (`σa` after
`arch_prepare_next_domain`). The post keeps `TK0` (not the domain time)
and widens the footprint by `NdW` (`SFootN`). -/
theorem scnt_refines0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) :
    sched.schedule_choose_new_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.scheduleChooseNewThread (Z := Unit) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧
      P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  by_cases hd0 : σ.domainTime ≠ 0
  · refine WP.spec_mono (schedule_choose_new_thread_refinesF s a σ hS hR hN hI (hA.1 s a σ hS hR hfo) (hA.2 s a σ hS hR)
      hd0) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, TK.tk0 h10, WritesIn.sfootN_of h11⟩
  have hnd := hdt.resolve_left hd0
  have hd0' : σ.domainTime = 0 := not_not.1 hd0
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hkf, hka⟩ := ks_fit hS
  obtain ⟨hD, hV, hidx⟩ := hnd
  obtain ⟨w24, w32, wd1, we0, hl0, hu⟩ := next_domain_words hD hV hidx
  have hNc : P1.NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  unfold sched.schedule_choose_new_thread
  step with Sched.sched.domain_time.spec2 as ⟨i, hi⟩
  have hi0 : i = 0#u64 := by
    apply UScalar.eq_of_val_eq
    have e := hs.domTime
    rw [hd0', ← hi] at e
    have := congrArg BitVec.toNat e
    simpa using this.symm
  simp only [hi0, ↓reduceIte, bind_ok]
  rw [next_domain_eq s hNc w24 w32 wd1 we0]
  simp only [bind_ok]
  set t := L.mem s (ksW (L.ksb s) (durOff 0#u64))
  -- the spec: `arch_prepare_next_domain`, then `next_domain`
  obtain ⟨σa, ha1, haS, haR, haK, hdl, hdi, hds, hown⟩ := hAN s σ hS hR hfo
  have hVa : DomListOK σa := hV.congr hdl hdi hds
  have hl : σa.domainList.length = 2 := by rw [hdl]; exact hD.1
  have hnx0 := nextDomain_eq (σ := σa) hl hVa (by rw [hdl]; exact hl0)
  have hnx : Fl4Spec.nextDomain (Z := Unit) σa = ({((), ndSt σa t.bv)}, False) := by rw [← hu]; exact hnx0
  set σn := ndSt σa t.bv
  have hSn : SchedRel st N T C c (ndS (L := L) s t) σn := schedRel_ndS haS t
  have hRn : NtfnStateRel N T (L.mem (ndS (L := L) s t)) σn := ntfnRel_ndS (σ' := σn) haR haS hNk rfl t
  have hNn : NSC N C σn := fun n hn x p hx hp => hN n hn x p ((haK.1.ntcb fun _ e => by cases e).1 hx) hp
  have hIn : Inv σn := Inv.fpu (σ' := σn) hI haK.1 haK.2.1 haK.2.2.1 haK.2.2.2.2.2.1
  have hfoN : FpuOwnOK σn := fun o e => by
    have e' : σa.archState.x64CurrentFpuOwner = some o := e
    rw [hown] at e'; cases e'
  refine WP.spec_mono (choose_thread_refinesF (ndS (L := L) s t) a σn hSn hRn hNn hIn (hA.1 _ a σn hSn hRn hfoN)
    (hA.2 _ a σn hSn hRn) (hSn.lists.choose_spec.choose_spec.2.idleTh).symm) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, h7.trans haK.2.2.2.2.1, h8.trans haK.2.2.1, HeapEqUpToFpu.trans (σ2 := σn) haK.1 h9, ?_, ?_⟩
  · unfold Fl4Spec.scheduleChooseNewThread
    rw [nd_gets_bind]
    unfold Fl4Spec.NonDet.when
    rw [if_pos hd0', nd_bind_one (show (do Fl4Spec.archPrepareNextDomain; Fl4Spec.nextDomain :
      Fl4Spec.SMonad Unit Unit) σ = ({((), σn)}, False) from by rw [nd_bind_one ha1]; exact hnx), nd_bind_one h1]
    rfl
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans haK.2.2.2.2.2.2.2.2.1)
    · exact Or.inr (by rw [← schedulable_fpu (σ' := σn) haK.1 haK.2.2.1]; exact h6)
  · exact (show TK0 σ σn from ⟨haK.2.2.2.2.2.1, haK.2.2.2.2.2.2.1, haK.2.2.2.2.2.2.2.2.1, hs.curDom.1.symm,
      haK.2.2.2.2.2.2.2.2.2.2.2⟩).trans (TK.tk0 h11)
  · have hRa : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) :=
      P1.nodeAt_aligned hNc (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
    have hRv := P1.nodeAt_val hNc (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
    have hf := hNc.fits
    simp only [P1.LawfulStore.nodeBase] at hf
    have hw0 := ndS_writes (st := st) hkf hka hRa (fun o ho => by
        rw [hRv, ksW_val (by omega)]; simp only [P1.LawfulStore.nodeBase]; simp [layout.node.REPROGRAM]; omega)
      (by have := hs.curDom.2; rwa [curDomA_ks] at this) t
    refine WritesIn.sfootN_trans (hw0.mono fun b hb => ?_) (WritesIn.sfootN_of h12)
    rcases hb with hb | rfl
    · exact Or.inr hb
    · refine Or.inl (Or.inr ⟨?_, ?_⟩) <;> rw [hRv, hc.cur] <;> simp [layout.node.REPROGRAM]

end

end

end Fl4Proofs.P3
