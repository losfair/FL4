/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch6 (B)): **`schedule` and
`finish` at `J` without `σ.domainTime ≠ 0`**, up to the FPU.

XTopJointSchedRF2's `jat_scheduleWP0F` ends at SchedRel level: `JAtZ` after
the timers at `rf`/`σ1`, FL4's writes from there in `KFootN` (KFoot plus
`next_domain`'s DOMAIN_TIME / DOM_SCHED_IDX / WORK_UNITS words), and the spec
outcome `schedule σ1 = {σ'}`. The tail of `jat_scheduleFRF` needs `JAtZ` at a
state from which the writes are in `KFoot`. Here that state is a *fake
pre-state*:

* FL4: `ndF rf.1 kb v16 v24 v40` = `rf.1` with the three `NdW` words set to
  their values in the final state; spec: `ndFSt σ1 v16.bv di` = `σ1` with
  the domain time and index replaced.
* `schedStep_dom2`: the DOMAIN_TIME / DOM_SCHED_IDX writes are a scheduler
  step (`SchedStep`, DomDecode's `schedStep_start` without the start word),
  so `JAtZ.schedJ` keeps `JAtZ`; WORK_UNITS by `JAtZ.workUnitsJD`
  (`JAtZ.ndFJ`).
* `ndF_writes`: from the fake state the writes are in `KFoot` (the `NdW`
  words agree with the final state by construction).
* Every spec fact of the tail (`SchS`, `LK`, the idle fields) reads neither
  the domain time nor the index, so the facts for `σ1 → σ'` are the facts
  for `ndFSt σ1 … → σ'` by definitional unfolding; `JAtZ.sch_tailS` is
  `JAtZ.sch_tail` taking them instead of `schedule σ = {σ'}`.

`jat_scheduleFR2` / `jat_scheduleSR2` / `jat_finishJ2`: `jat_scheduleFRF` /
`jat_scheduleSRF` / `jat_finishJF` with `hd : σ.domainTime ≠ 0 ∨ NdOK s σ`
(NdOK's [J] facts at the entry, sch2/sch3) and `ArchNdF` [P]; `hTail`'s
footprint is `KFootN`. They supersede the `F` versions.
-/
import Fl4Proofs.P3.XTopJointSchedRF2
import Fl4Proofs.P3.XTopJointCopyRegs
import Fl4Proofs.P3.XTopJointPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- FL4's DOMAIN_TIME / DOM_SCHED_IDX words written. -/
def ndF2 (s : S) (kb v16 v24 : U64) : S :=
  L.wr (L.wr s (ksW kb 16#u64) v16) (ksW kb 24#u64) v24

/-- The fake pre-state: the three `NdW` words written. -/
def ndF (s : S) (kb v16 v24 v40 : U64) : S :=
  L.wr (ndF2 (L := L) s kb v16 v24) (ksW kb 40#u64) v40

/-- The spec's fake pre-state: domain time and index replaced. -/
def ndFSt (σ : Fl4Spec.State Unit) (dt : BitVec 64) (di : Nat) : Fl4Spec.State Unit :=
  { σ with domainTime := dt, domainIndex := di }

/-- **The DOMAIN_TIME / DOM_SCHED_IDX writes as a scheduler step** (as
DomDecode's `schedStep_start`, without the start word). -/
theorem schedStep_dom2 (th : TypedHeap) (s1 : S) (σ1 : Fl4Spec.State Unit) {kb : U64} (v16 v24 : U64) (di : Nat)
    (hk1 : L.ksb s1 = kb) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    SchedStep (L := L) th s1 σ1 (ndF2 (L := L) s1 kb v16 v24) (ndFSt σ1 v16.bv di) := by
  subst hk1
  set kb := L.ksb s1
  have hw : P1.WritesIn st s1 (ndF2 (L := L) s1 kb v16 v24) (DomKW kb) :=
    wtrans (writesIn_ksW s1 v16 hkf hka (o := 16#u64) (by simp)) (writesIn_ksW _ v24 hkf hka (o := 24#u64) (by simp))
  have hw4 : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 24 →
      L.mem (ndF2 (L := L) s1 kb v16 v24) (ksW kb o) = L.mem s1 (ksW kb o) := by
    intro o ho h8 n16 n24
    rw [ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n24.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n16.symm)]
  have h16 : L.mem (ndF2 (L := L) s1 kb v16 v24) (ksW kb 16#u64) = v16 := by
    rw [ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_same _ _ hkf hka (by decide) (by decide)]
  refine ⟨by constructor <;> rfl, fun N T C c _ hS _ => ⟨hS.domW hw (by constructor <;> rfl) rfl rfl ?_,
    hw.mono fun b hb => Or.inr (Or.inr hb), fun hD => ?_⟩, ⟨fun d p _ hu => Or.inl ⟨d, p, hu⟩, Or.inr rfl⟩,
    blkKeep_domKW hw hka⟩
  · show v16.bv = (L.mem (ndF2 (L := L) s1 kb v16 v24) (ksW kb 16#u64)).bv
    rw [h16]
  · obtain ⟨hl1, hent1, hst1⟩ := domRel_iff.2 hD
    refine domRel_iff.1 ⟨hl1, fun i hi => ?_, by
      rw [hw4 _ (by decide) (by decide) (by decide) (by decide)]; exact hst1⟩
    obtain ⟨b1, b2, b3, b4, -, b6, b7, -, b9, b10⟩ := dur_off_bounds hi
    rw [hw4 _ b1 b2 b6 b7, hw4 _ b3 b4 b9 b10]
    exact hent1 i hi

theorem ndF_ksb (s : S) (kb v16 v24 v40 : U64) : L.ksb (ndF (L := L) s kb v16 v24 v40) = L.ksb s := by
  simp only [ndF, ndF2, P1.LawfulStore.ksb_wr]

theorem ndF_cpu (s : S) (kb v16 v24 v40 : U64) : L.cpu (ndF (L := L) s kb v16 v24 v40) = L.cpu s := by
  simp only [ndF, ndF2, P1.LawfulStore.cpu_wr]

/-- The fake state's words off the three `NdW` words. -/
theorem ndF_mem_ne (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    {b : U64} (hb : P1.Aligned b) (hn : ¬ NdW kb b) : L.mem (ndF (L := L) s kb v16 v24 v40) b = L.mem s b := by
  have hn' : ¬ (b = ksW kb 16#u64 ∨ b = ksW kb 24#u64 ∨ b = ksW kb 40#u64) := hn
  rw [ndF, ndF2, L.mem_wr _ _ _ _ (ksW_al hkf hka (by decide) (by decide)) hb,
    if_neg (fun e => hn' (Or.inr (Or.inr e.symm))),
    L.mem_wr _ _ _ _ (ksW_al hkf hka (by decide) (by decide)) hb, if_neg (fun e => hn' (Or.inr (Or.inl e.symm))),
    L.mem_wr _ _ _ _ (ksW_al hkf hka (by decide) (by decide)) hb, if_neg (fun e => hn' (Or.inl e.symm))]

theorem ndF_mem16 (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    L.mem (ndF (L := L) s kb v16 v24 v40) (ksW kb 16#u64) = v16 := by
  rw [ndF, ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_same _ _ hkf hka (by decide) (by decide)]

theorem ndF_mem24 (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    L.mem (ndF (L := L) s kb v16 v24 v40) (ksW kb 24#u64) = v24 := by
  rw [ndF, ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_same _ _ hkf hka (by decide) (by decide)]

theorem ndF_mem40 (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    L.mem (ndF (L := L) s kb v16 v24 v40) (ksW kb 40#u64) = v40 := by
  rw [ndF, mem_ks_same _ _ hkf hka (by decide) (by decide)]

/-- **From the fake state, FL4's writes are in `KFoot`** (module docstring). -/
theorem ndF_writes {T N C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit} (di : Nat)
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hw : P1.WritesIn st s s' (KFootN st T N C c s σ)) :
    P1.WritesIn st (ndF (L := L) s (L.ksb s) (L.mem s' (ksW (L.ksb s) 16#u64)) (L.mem s' (ksW (L.ksb s) 24#u64))
        (L.mem s' (ksW (L.ksb s) 40#u64))) s'
      (KFoot st T N C c (ndF (L := L) s (L.ksb s) (L.mem s' (ksW (L.ksb s) 16#u64))
        (L.mem s' (ksW (L.ksb s) 24#u64)) (L.mem s' (ksW (L.ksb s) 40#u64)))
        (ndFSt σ (L.mem s' (ksW (L.ksb s) 16#u64)).bv di)) := by
  have hk := ndF_ksb (L := L) s (L.ksb s) (L.mem s' (ksW (L.ksb s) 16#u64)) (L.mem s' (ksW (L.ksb s) 24#u64))
    (L.mem s' (ksW (L.ksb s) 40#u64))
  refine ⟨hw.1.trans hk.symm, hw.2.1.trans (ndF_cpu (L := L) _ _ _ _ _).symm, fun b hb hn => ?_⟩
  by_cases hN : NdW (L.ksb s) b
  · rcases hN with rfl | rfl | rfl
    · rw [ndF_mem16 _ _ _ _ hkf hka]
    · rw [ndF_mem24 _ _ _ _ hkf hka]
    · rw [ndF_mem40 _ _ _ _ hkf hka]
  · rw [ndF_mem_ne _ _ _ _ hkf hka hb hN]
    refine hw.2.2 b hb fun h => ?_
    rcases h with (h | h | h) | h
    · exact hn (Or.inl ((SFoot.ksb hk).2 h))
    · exact hn (Or.inr (Or.inl h))
    · exact hn (Or.inr (Or.inr h))
    · exact hN h

set_option maxHeartbeats 4000000 in
/-- The spec step's facts read neither the domain time nor the index. -/
theorem SchS.ndF {σ σ' : Fl4Spec.State Unit} (h : SchS σ σ') (dt : BitVec 64) (di : Nat) :
    SchS (ndFSt σ dt di) σ' :=
  ⟨⟨h.1.kh, h.1.um, h.1.cdt, h.1.orig, h.1.dl, h.1.dsi, h.1.io, h.1.gpml4, h.1.asid, h.1.ist, h.1.inode, h.1.isc⟩,
    ⟨h.2.kh, h.2.cdt, h.2.orig, h.2.dl, h.2.dsi, h.2.isc⟩⟩

/-- **`JAtZ` at the fake state** (module docstring). -/
theorem JAtZ.ndFJ {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (v16 v24 v40 : U64) (di : Nat) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' (ndF (L := L) s (L.ksb s) v16 v24 v40) a (ndFSt σ v16.bv di) := by
  have hkf := J.kern.ksbFit
  have hka := J.kern.ksbAl
  obtain ⟨Ac1, Lst1, D1, J1⟩ := J.schedJ (schedStep_dom2 Z.th s σ v16 v24 di rfl hkf hka)
  obtain ⟨Ac2, Lst2, J2⟩ := J1.workUnitsJD (arI := arI) v40
  have e : core.num.U64.wrapping_add (L.ksb (ndF2 (L := L) s (L.ksb s) v16 v24)) layout.ks.WORK_UNITS =
      ksW (L.ksb s) 40#u64 := by
    simp only [ndF2, P1.LawfulStore.ksb_wr, ksW]
    unfold layout.ks.WORK_UNITS; rfl
  rw [e] at J2
  exact ⟨Ac2, Lst2, D1, J2⟩

set_option maxHeartbeats 2000000 in
/-- **`JAtZ.sch_tail` from the spec step's facts** instead of `schedule σ =
{σ'}` (module docstring). -/
theorem JAtZ.sch_tailS {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    (hSch : SchS σ σ') (hik : σ'.idleThread = σ.idleThread ∧ σ'.idleSc = σ.idleSc)
    (hw : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ))
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hR' : NtfnStateRel Z.N Z.T (L.mem s') σ') (hN' : NSC Z.N Z.C σ')
    (hI' : Inv σ') (hC' : CurInv σ') (hA' : ActIdle σ') (hcr : CurRunW σ') (hoff : Sched.OffOK σ')
    (hbsa : Sched.BlockedScActive σ')
    (hT : SchTailHyps (L := L) AR Z H Cs D s s' a' σ' Ac') :
    ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a' σ' := by
  have hK : SchStep (fun _ => False) σ σ' := hSch.1
  have hKc : ∀ ct : Fl4Spec.ObjRef, SchStep (fun p => p = ct) σ σ' := fun ct =>
    { hK with kh := fun p => (hK.kh p).mono False.elim }
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hS := J.xtop.fin.1.1.1
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sched_step J.xtop J.ip J.nk hwT (hKc σ.curThread) hS' hR' hT.curOK hT.ar
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSch.2⟩
  refine ⟨Lst', J.sch_frame hwT hK hX' hCR' hRF' hY' hM' (J.sch_buf hwT hK) hRP' (J.sch_apart hwT hK)
    (J.sch_jpl hwT hK (J.idleW_keep hS' hik.1 hik.2).2) (J.sc_jcov hwT hT.dead (fun q hq hn => absurd hq hn)
      (J.idleW_keep hS' hik.1 hik.2))
    (J.sch_kern hwT hK hS' hT.dbg hT.dwNe (J.sch_csc hwT hK hS' hI' hC' hT.dead).1) (J.sch_utc hwT hK hT.dbg) hN' hI' (Or.inr hC')
    (Or.inl (curOwn_of_curInv hS' hI' hC')) hoff hA' hbsa (Or.inr hcr) hT.blk hT.dbgK (J.idleW_keep hS' hik.1 hik.2).1 J.zD⟩

set_option maxHeartbeats 4000000 in
/-- **FL4's `schedule` refines the spec's at `J`, with the domain switch**
(module docstring): `jat_scheduleFRF` without `σ.domainTime ≠ 0`. -/
theorem jat_scheduleFR2 {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hSig : SignalJHyp (L := L) arI AR H Cs)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ := by
  have h0Cs : 0#u64 ∈ Cs := J.kern.cs0
  have hB := J.blk
  obtain ⟨⟨Q, R, hq⟩, hBd, hXi, hSc, hSg⟩ := id hB
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hq.nodes 0#u64 h0Cs) (by simp) (by simp)
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (jat_scheduleWP0F s a σ J hd hnd hAT hSig hA hAN hFO hsni hsend hT)
    (P1.sched.schedule.kw hAT hNt s a hB)) (WP.spec_and (P1.sched.schedule.tinv hAT hNt s a Q R hq hBd hSc hXi hSg)
      hTail)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨V1, Ac1, Lst1, D1, J1⟩, hfr, hkf, -⟩, hw, hrun⟩,
    hkw⟩, ⟨htinv, hRest⟩⟩
  simp only [WP.uncurry'_pair] at hkw htinv
  obtain ⟨rf', hrf', -, hkw⟩ := hkw
  obtain rfl : rf = rf' := by simpa using (hrf'.symm.trans hfr).symm
  have hTl := hRest rf σ1 σ' D1 hF hsc hw hS' hI' hC' hA'
  obtain ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', -, -, -, -⟩ := htinv
  -- the fake pre-state
  have hkf1 := J1.kern.ksbFit
  have hka1 := J1.kern.ksbAl
  set kb := L.ksb rf.1 with hkb
  set s0 := ndF (L := L) rf.1 kb (L.mem s' (ksW kb 16#u64)) (L.mem s' (ksW kb 24#u64)) (L.mem s' (ksW kb 40#u64))
    with hs0
  set σ0 := ndFSt σ1 (L.mem s' (ksW kb 16#u64)).bv σ'.domainIndex with hσ0
  obtain ⟨Ac0, Lst0, D0, J0⟩ := J1.ndFJ (L.mem s' (ksW kb 16#u64)) (L.mem s' (ksW kb 24#u64))
    (L.mem s' (ksW kb 40#u64)) σ'.domainIndex
  have hw0 : P1.WritesIn st s0 s' (KFoot st Z.T Z.N Z.C Z.c s0 σ0) := ndF_writes σ'.domainIndex hkf1 hka1 hw
  have hk0 : L.ksb s0 = L.ksb rf.1 := ndF_ksb _ _ _ _ _
  have hks' : L.ksb s' = L.ksb s := hkw.1.trans hkf
  have hnA : L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb (hk0.trans hkf) _ _
  have hnA1 : L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hkf _ _
  have hN0 := hq.nodes 0#u64 h0Cs
  have hdv : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s 0#u64 + 88 := by
    rw [P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp), P1.debug_val]
  have hdbg0 : L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem rf.1 (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) := by
    rw [hnA, hnA1, hs0]
    refine ndF_mem_ne _ _ _ _ hkf1 hka1 hal fun hb => ?_
    have h16 := ksW_val (kb := kb) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := kb) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := kb) (o := 40#u64) (by simp; omega)
    have hkbs : kb.val = (L.ksb s).val := by rw [hkf]
    unfold P1.LawfulStore.nodeBase at hdv
    rcases hb with e | e | e <;> have := congrArg UScalar.val e <;> simp at h16 h24 h40 <;> omega
  have hdbg : L.mem s' (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [hdbg0, P1.nodeAt_of_ksb hk0]
    exact hkw.mem_eq (by rw [hnA1]; exact hal) (P1.dbg0_not_schedW J1.blk h0Cs)
  have hdw : (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val := by
    have hN0' := hq'.nodes 0#u64 h0Cs
    have hct : L.curW s' ∈ P1.Heap.tcbs H := hq'.curT
    have hv := P1.nodeAt_val hN0' (off := layout.node.DEBUG_TCBS) (by simp)
    have hsv := P1.field_val (hq'.tcbs _ hct) (K := 3328#u64) (by decide)
    have hdj := hN0'.disj _ hct
    have hv' : (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s' 0#u64 + 88 := by
      rw [hnA, ← P1.nodeAt_of_ksb hks' 0#u64 layout.node.DEBUG_TCBS, hv, P1.debug_val]
    have hsv' : (P1.stA (L.curW s')).val = (L.curW s').val + 3328 := by
      rw [P1.stA_eq, hsv]; rfl
    rw [hv', hsv']
    have e12 : (2 : Nat) ^ 12 = 4096 := rfl
    rw [e12] at hdj
    omega
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  have hSch1 : SchS σ1 σ' := schs_schedule.of_eq hsc
  have hSch0 : SchS σ0 σ' := SchS.ndF hSch1 _ _
  have hK1 : SchStep (fun _ => False) σ0 σ' := hSch0.1
  have hL1 : LK (fun _ => False) σ0 σ' := lkm_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hik : σ'.idleThread = σ0.idleThread ∧ σ'.idleSc = σ0.idleSc :=
    ik_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hwT := WritesIn.tfoot_of_kfoot hw0
  have hSS : SlotsSame Z.th (L.mem s0) (L.mem s') :=
    slotsSame_of_iw J0.xtop.rel.1 J0.xtop.rel.2.2.2.2.2.1 J0.xtop.rel.2.2.2.2.2.2 hwT
      fun b hb => tfoot_iw J0.xtop.fin.1.1.1 hb
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hS'.lists
  obtain ⟨hth, hvt⟩ := hVt _ _ _ _ _ _ _ J0 _ hcc.curT
  have hcur : Vs.CurOK st Z.th s' σ' :=
    ⟨_, hsc'.curThread.symm, hth, fun p asid h => hvt p asid (by
      rwa [hSS.capAt ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩] at h)⟩
  have hX' : XTopAt (L := L) AR (Z.mv Z.G V1) s' a' σ' :=
    xtop_sched_step J0.xtop J0.ip J0.nk hwT (ct := σ0.curThread)
      { hK1 with kh := fun p => (hK1.kh p).mono False.elim } hS' hR' hcur hTl.ar
  have hSOK0 := hSch0.2
  have hY1 : YieldRel Z.T Z.C (L.mem s') σ' :=
    (ScAll.of_k J0.xtop.fin.1.1.1 J0.rp J0.yld J0.mcp J0.call J0.rfree ⟨⟨hS', hR', hN', hI'⟩, hw0, hSOK0⟩).2.1
  have hdead : ∀ q ∈ D0, Sched.DeadP (L := L) H s' q := fun q hq =>
    J0.deadP_sch_step hX' hwT hK1 hL1 hA' (J0.ymd hS' hY1 ((hSOK0.ykeep rfl).dk q.bv)) (fun h => h)
      (J0.jcov.dead q hq)
  -- every debug word kept from the fake pre-state (`ndF` writes kernel-state words only)
  have hdk0 : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s' := by
    have h1 := P1.dbgKeep_schedW J1.blk J1.kern.ksbFit hkw
    obtain ⟨⟨Qk, Rk, hqk⟩, -⟩ := J1.blk
    refine ⟨hkw.1.trans hk0.symm, fun b hb => ?_⟩
    have hb1 : P1.DbgW st (P1.Heap.tcbs H) Cs rf.1 b := P1.DbgW.ksb hk0 hb
    rw [h1.2 b hb1]
    refine (ndF_mem_ne _ _ _ _ hkf1 hka1 (P1.dbgW_aligned J1.blk hb1) fun hn => ?_).symm
    have h16 := ksW_val (kb := kb) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := kb) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := kb) (o := 40#u64) (by simp; omega)
    simp at h16 h24 h40
    have hbv : b.val = kb.val + 16 ∨ b.val = kb.val + 24 ∨ b.val = kb.val + 40 := by
      rcases hn with e | e | e <;> rw [e] <;> omega
    rcases hb1 with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hv := P1.field_val (hqk.tcbs y hy) (K := 3576#u64) (by simp)
      have ho := hqk.ksOut y hy
      rw [← hkb] at ho
      have h35 : (3576#u64 : U64).val = 3576 := by simp
      have e' : b.val = y.val + 3576 := by
        rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, hv, h35]
      simp only [Nat.reducePow] at ho
      omega
    · have hv := P1.field_val (hqk.tcbs y hy) (K := 3584#u64) (by simp)
      have ho := hqk.ksOut y hy
      rw [← hkb] at ho
      have h35 : (3584#u64 : U64).val = 3584 := by simp
      have e' : b.val = y.val + 3584 := by
        rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, hv, h35]
      simp only [Nat.reducePow] at ho
      omega
    · have hN := hqk.nodes c hc
      have hv : b.val = L.nodeBase rf.1 c + 88 := by
        rw [e, P1.nodeAt_val hN (off := layout.node.DEBUG_TCBS) (by simp), P1.debug_val]
      have hnb : L.nodeBase rf.1 c = (L.ksb rf.1).val + 13568 + c.val * 4288 := rfl
      rw [← hkb] at hnb
      omega
  have hT2 : SchTailHyps (L := L) AR (Z.mv Z.G V1) H Cs D0 s0 s' a' σ' Ac :=
    ⟨hcur, hTl.ar, hdbg, hdw, hdead,
      ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', hSg.ksb' hks'⟩, hdk0⟩
  obtain ⟨Lst', J'⟩ := J0.sch_tailS hSch0 hik hw0 hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hT2
  exact ⟨σ1, σ', hF, hsc, ⟨J'.xtop.relTop, _, _, _, _, _, _, J'⟩, ⟨V1, Ac, Lst', D0, J'⟩, hC',
    RunW.scAndTimer (hr3 J1.curRun) he3⟩

/-- **`jat_scheduleFR2` with `SignalJHyp` reduced to the waking signals**
(`signalJHyp_of`, as `jat_scheduleSRF`). -/
theorem jat_scheduleSR2 {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ :=
  jat_scheduleFR2 s a σ J hd hnd hAT hVt (signalJHyp_of hAT hW hmb) hA hAN hFO hsni hsend hT hTail

set_option maxHeartbeats 4000000 in
/-- **FL4's `finish` at `J` with the domain switch** (`jat_finishJF` on
`jat_scheduleSR2`): no `σ.domainTime ≠ 0`; `NdOK`'s [J] facts in the other
case, `ArchNdF` [P]. -/
theorem jat_finishJ2 {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hvm : ∀ s1 a1 σ1, JAt (L := L) arI AR s1 a1 σ1 → ∀ x, σ1.kheap σ1.curThread = some (.tcb x) →
      x.tcbState ≠ .runningVM) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  unfold syscall.finish
  refine WP.spec_bind (jat_scheduleSR2 s a σ J hd hnd hAT hVt hW hmb hA hAN hFO hsni hsend hT hTail) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, hsc, -, ⟨V1, Ac1, Lst1, D1, J1⟩, -, hcr⟩
  refine WP.spec_mono (J1.activateJ hAT hmax (htu a1) hcr (hvm _ _ _ ⟨_, _, _, _, _, _, J1⟩)) ?_
  rintro r ⟨σ', ha, hRJ, V2, Ac2, Lst2, D2, J2⟩
  have hsa : (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) := by
    rw [Notif.nd_bind_one hsc]; exact ha
  refine ⟨σ1, σ', mem_fl4Awaken_of hF, hsa, ⟨((), σ1), mem_fl4Awaken_of hF, ?_⟩, hRJ, V2, Ac2, Lst2, D2, J2⟩
  show ((), σ') ∈ ((Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1).1
  rw [hsa]; exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
