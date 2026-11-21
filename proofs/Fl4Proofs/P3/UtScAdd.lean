/-
P3 (DESIGN.md §9), untyped: **fresh SCs into the composite relation** (the
SC half of the no-reset retype at `J`, handoff/utj.md "uttypes").

A no-reset retype of SCs (type 5) adds the window's objects to `C`: in the
spec `defaultSchedContext` of the window's size, at addresses that held no
object; in FL4 their header words zero (the window is the untyped's zero free
part, and the retype writes only slot words).

* `oobj_unionC`: an `OObj` word of the sets with `C ∪ Wc` (after the fresh
  SCs) is one of the old sets' (before) or in a new SC.
* `XTopAt.addStepC`: `XTopAt` at `C ∪ Wc` (and a new MDB ghost) across a
  step whose FL4 writes are slot words and whose spec change is `SpecAdd`
  of fresh SCs followed by a CNode-only change (as UtEpXTop's
  `XTopAt.addStep`, with ScFreshSc's `SchedRel.add_scs` for the scheduler
  relation; the old sets' SCs are old objects, `SchedRel.scs`).
-/
import Fl4Proofs.P3.UtEpXTop
import Fl4Proofs.P3.UtAddSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Add
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
variable {σ σ' : Fl4Spec.State Unit}

/-- The SCs of `C` after fresh SCs are the old ones (`SchedRel.scs`: each
SC of `C` is an object before, so not at a fresh address). -/
theorem Sched.SchedRel.scOld {s : S} {Wc : Set U64} {n : Nat} (hS : Sched.SchedRel st N T C c s σ)
    (hA : Sched.SpecAdd σ σ' (Sched.SWc Wc) (fun _ => .schedContext Fl4Spec.defaultSchedContext n))
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {m : Nat}
    (hx : σ'.kheap sc.bv = some (.schedContext x m)) : σ.kheap sc.bv = some (.schedContext x m) := by
  rcases hA.kback hx with h | ⟨hw, -⟩
  · exact h
  · obtain ⟨Q, R0, -, hs⟩ := hS.lists
    obtain ⟨x0, m0, hk0, -⟩ := hs.scs sc hsc
    rw [(hA.new _ hw).1] at hk0; cases hk0

/-- A fresh SC's object after `SpecAdd`, at its size. -/
theorem Sched.SpecAdd.scNew {Wc : Set U64} {n : Nat}
    (hA : Sched.SpecAdd σ σ' (Sched.SWc Wc) (fun _ => .schedContext Fl4Spec.defaultSchedContext n))
    {sc : U64} (hsc : sc ∈ Wc) {x : Fl4Spec.SchedContext} {m : Nat}
    (hx : σ'.kheap sc.bv = some (.schedContext x m)) : x = Fl4Spec.defaultSchedContext ∧ m = n := by
  rw [(hA.new _ ⟨sc, hsc, rfl⟩).2] at hx
  cases hx; exact ⟨rfl, rfl⟩

/-- **An `OObj` word of the sets with `C ∪ Wc`** after fresh SCs is one of
the old sets' before or a new SC's word. -/
theorem oobj_unionC {s : S} {Wc : Set U64} {n : Nat} (hS : Sched.SchedRel st N T C c s σ)
    (hA : Sched.SpecAdd σ σ' (Sched.SWc Wc) (fun _ => .schedContext Fl4Spec.defaultSchedContext n)) {b : U64}
    (h : OObj st N T (C ∪ Wc) E R B c s σ' b) :
    OObj st N T C E R B c s σ b ∨ ∃ sc ∈ Wc, Sched.ScObj sc n b := by
  unfold OObj at h
  rcases h with h | h | h | h | h | h | ⟨sc, hsc, x, m, hk, ho⟩ | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · rcases hsc with hsc | hsc
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨sc, hsc, x, m, hS.scOld hA hsc hk, ho⟩)))))))
    · obtain ⟨-, rfl⟩ := hA.scNew hsc hk
      exact Or.inr ⟨sc, hsc, ho⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

end Add

section Step
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {σ σ' : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` at `C ∪ Wc` across fresh SCs and a CNode-only step**
(module docstring): FL4 writes only slot words; the spec adds the fresh SCs
`Wc` (`defaultSchedContext` of size `n`, on core 0) and then changes only
CNodes; the new SCs are placed, their header words zero, not the idle SC,
their words apart from the scheduler relation's other words, the old SCs and
each other (`SchedRel.add_scs`), from the VSpace and CSpace code's words
(`VObj`) and the endpoint code's (`EWrite`). -/
theorem XTopAt.addStepC {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σB : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hw : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    {Wc : Set U64} {n : Nat}
    (hA : Sched.SpecAdd σ σB (Sched.SWc Wc) (fun _ => .schedContext Fl4Spec.defaultSchedContext n))
    (hcn : CnK σB σ') (hkc : KeepC σB σ') {G' : MdbGhost} (hCR : CRel Z.th (L.mem s') σ' G')
    (hFI : FinInv Z.th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTS : ∀ t, Z.th t = some .tcb → ∀ p asid, capAt (L.mem s') (slotOf t 1) = ok (.Pml4 p true asid) →
      capAt (L.mem s) (slotOf t 1) = ok (.Pml4 p true asid))
    (hc0 : Z.c = 0#u64)
    (hpl : ∀ sc ∈ Wc, Fl4Proofs.P1.Placed sc (n + Fl4Spec.minSchedContextBits))
    (hm : ∀ sc ∈ Wc, ∀ K : U64, K.val < 96 → K.val % 8 = 0 → L.mem s (Sched.scW sc K) = 0#u64)
    (hid : ∀ sc ∈ Wc, sc.bv ≠ σ.idleSc)
    (hout : ∀ sc ∈ Wc, ∀ a : U64, Sched.ScObj sc n a → ¬ Notif.NWrite Z.N Z.T a ∧
      (a.val < L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ a.val) ∧
      (∀ t ∈ Z.T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
      (a.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val))
    (hdo : ∀ sc ∈ Wc, ∀ sc' ∈ Z.C, ∀ x' n', σ.kheap sc'.bv = some (.schedContext x' n') → ∀ a : U64,
      Sched.ScObj sc n a → ¬ Sched.ScObj sc' n' a)
    (hdn : ∀ sc ∈ Wc, ∀ sc' ∈ Wc, sc ≠ sc' → ∀ a : U64, Sched.ScObj sc n a → ¬ Sched.ScObj sc' n a)
    (hnV : ∀ sc ∈ Wc, ∀ a : U64, Sched.ScObj sc n a → ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) a)
    (hnE : ∀ sc ∈ Wc, ∀ a : U64, Sched.ScObj sc n a → ¬ Endp.EWrite Z.T Z.E Z.R Z.B a) :
    XTopAt (L := L) AR { Z with G := G', C := Z.C ∪ Wc } s' a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, -, -, hD, -, hIA, -⟩, -, hE⟩ := hX
  obtain ⟨hO, hms, har⟩ := ostep_of_cnk hcn hkc
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hSch := hS.1.1
  -- `TopSR` at `C ∪ Wc` after the fresh SCs
  have hSB : TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T (Z.C ∪ Wc) Z.E Z.R Z.B Z.c AR s a σB := by
    obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
    have har := hA.arch
    have hist : σB.interruptStates = σ.interruptStates := by
      have e := congrArg Fl4Spec.AbstractState.interruptStates hA.abs; exact e
    have hin : σB.interruptIrqNode = σ.interruptIrqNode := by
      have e := congrArg Fl4Spec.AbstractState.interruptIrqNode hA.abs; exact e
    refine ⟨⟨Sched.SchedRel.add_scs hSch hc0 hpl hm hid hout hdo hdn hA, EpStateRel.specAdd hEp hA,
      NtfnStateRel.specAdd hNt hA,
      ⟨fun i hi => by rw [hist]; exact hIrq.st i hi, fun i hi => by rw [hin]; exact hIrq.node i hi⟩,
      fun p hp => by rw [har]; exact hIo p hp, ?_, by rw [har]; exact hAr⟩,
      { hP with disj := fun x hx => ?_ }⟩
    · unfold KRootRel globCr3 at hKr ⊢
      rw [har]; exact hKr
    · rcases oobj_unionC hSch hA hx with hx | ⟨sc, hsc, hb⟩
      · exact hP.disj x hx
      · exact hnV sc hsc x hb
  have hS' := TopSR.step0 hSB (fun b h => slotWd_vobj hPl h) hw hO hms (by rw [har])
  have har' : σ'.archState = σ.archState := har.trans hA.arch
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.2.2 b (hP.vo b hb).1 fun h => slotWd_inObj hPl h (hP.vo b hb)
  have hcur : σ'.curThread = σ.curThread := hO.ct.trans hA.f.2.2.1
  -- an old object other than a CNode is kept
  have hkeep : ∀ q k, σ.kheap q = some k → (∀ r cs, k ≠ .cnode r cs) → σ'.kheap q = σ.kheap q := by
    intro q k hq hnc
    rcases hkc q with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hA.kold hq, hq]
    · rw [hA.kold hq] at h1; cases h1; exact absurd rfl (hnc r cs)
  have hab : Fl4Spec.AbstractState.domainList σ'.toAbstractState = σ.domainList ∧
      Fl4Spec.AbstractState.domainStartIndex σ'.toAbstractState = σ.domainStartIndex := by
    refine ⟨?_, ?_⟩
    · have e1 := congrArg Fl4Spec.AbstractState.domainList hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainList hA.abs
      exact e1.trans e2
    · have e1 := congrArg Fl4Spec.AbstractState.domainStartIndex hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainStartIndex hA.abs
      exact e1.trans e2
  -- an SC after: an old one of `C` or a fresh one
  have hscB : ∀ sc ∈ Z.C ∪ Wc, ∀ x m, σ'.kheap sc.bv = some (.schedContext x m) →
      (sc ∈ Z.C ∧ ∃ x0, σ.kheap sc.bv = some (.schedContext x0 m)) ∨ (sc ∈ Wc ∧ m = n) := by
    intro sc hsc x m hx
    obtain ⟨x1, h1⟩ := SzKeep.of_keepC hkc sc.bv x m hx
    rcases hsc with hsc | hsc
    · exact Or.inl ⟨hsc, x1, hSch.scOld hA hsc h1⟩
    · exact Or.inr ⟨hsc, (hA.scNew hsc h1).2⟩
  have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [P1.LawfulStore.nodeBase, hk]
  refine ⟨⟨hS', ?_, ?_, fun q hq lo hl => ?_, ?_⟩, ⟨hPl, hCR, hFI, ?_, by rw [hk]; exact hMO,
    by rw [hk]; exact hIA, ScApart.of_top hS'.2⟩, IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1),
    ⟨fun a h1 h2 => hE.node a (hnb ▸ h1) (hnb ▸ h2), by rw [Sched.curDomA_ksb hk]; exact hE.dom,
      by rw [Sched.dtA_ksb hk]; exact hE.dt, fun sc hsc x m hx a ha => ?_⟩⟩
  · rw [hk]
    refine hR.frame hvw (by rw [har']) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact hkeep _ _ hf (fun r cs e => by cases e)
  · refine hPt.frame (fun b hb => hw.2.2 b (hP.po b hb).1 fun h => slotWd_inObj hPl h (hP.po b hb)) fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl
  · obtain ⟨t, h1, h2, h3⟩ := hCO
    exact ⟨t, h1.trans hcur.symm, h2, fun p asid hc => h3 p asid (hTS t h2 p asid hc)⟩
  · rw [hk]
    refine hD.frame (fun o ho => ?_) hab.1 hab.2
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) fun h => ?_
    obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
    exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩
  · rcases hscB sc hsc x m hx with ⟨hsc', x0, h0⟩ | ⟨hsc', rfl⟩
    · exact hE.sc sc hsc' x0 m h0 a ha
    · exact hnE sc hsc' a ha

end Step


/-! ## The spec's invariants across fresh SCs -/

section Spec
open Fl4Spec Sched Fl4Proofs.P1 Fl4Proofs.P3.Notif

variable {σ σ' σ'' : State Unit} {Wc : Set U64} {n : Nat}

/-- The ghost call stacks with the fresh SCs' empty: `Lst` on `C`, `[]` off it. -/
def LstC (C : Set U64) (Lst : U64 → List U64) : U64 → List U64 := fun sc => if sc ∈ C then Lst sc else []

theorem LstC_in {C : Set U64} {Lst : U64 → List U64} {sc : U64} (h : sc ∈ C) : LstC C Lst sc = Lst sc := by
  unfold LstC; rw [if_pos h]

theorem LstC_out {C : Set U64} {Lst : U64 → List U64} {sc : U64} (h : sc ∉ C) : LstC C Lst sc = [] := by
  unfold LstC; rw [if_neg h]

theorem detached_lstC {C Wc : Set U64} {Lst : U64 → List U64} {d : U64} :
    Detached (C ∪ Wc) (LstC C Lst) d ↔ Detached C Lst d := by
  constructor
  · intro h sc hsc hm; exact h sc (Or.inl hsc) (by rw [LstC_in hsc]; exact hm)
  · intro h sc hsc hm
    by_cases hc : sc ∈ C
    · exact h sc hc (by rw [LstC_in hc] at hm; exact hm)
    · rw [LstC_out hc] at hm; cases hm

/-- An object of another kind than an SC is looked up alike across fresh SCs. -/
theorem Sched.SpecAdd.lookS (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    {p : ObjRef} {ko : KernelObject} (hs : ∀ y k, ko ≠ .schedContext y k) :
    σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  refine ⟨fun hk => ?_, h.kold⟩
  rcases h.kback hk with e | ⟨-, rfl⟩
  · exact e
  · exact absurd rfl (hs _ _)

theorem Sched.SpecAdd.tcbS (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    {p : ObjRef} {x : Tcb} : σ'.kheap p = some (.tcb x) ↔ σ.kheap p = some (.tcb x) :=
  h.lookS (fun _ _ e => by cases e)

/-- An SC off the fresh addresses is looked up alike. -/
theorem Sched.SpecAdd.scS (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    {p : ObjRef} (hp : ∀ sc ∈ Wc, sc.bv ≠ p) : σ'.kheap p = σ.kheap p :=
  h.old p fun ⟨sc, hsc, e⟩ => hp sc hsc e

/-- An SC after at an address of `C ∪ Wc`: one before (at an address of `C`
or not) or a fresh one. -/
theorem Sched.SpecAdd.scB (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    {sc : U64} {y : SchedContext} {k : Nat} (hk : σ'.kheap sc.bv = some (.schedContext y k)) :
    σ.kheap sc.bv = some (.schedContext y k) ∨ (sc ∈ Wc ∧ y = defaultSchedContext ∧ k = n) := by
  rcases h.kback hk with e | ⟨⟨sc', hsc', e⟩, e2⟩
  · exact Or.inl e
  · have : sc' = sc := P1.eq_of_bv e
    subst this
    cases e2; exact Or.inr ⟨hsc', rfl, rfl⟩

theorem Sched.SpecAdd.schedS (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    {t : ObjRef} (hts : ∀ x scp, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some scp → ∀ sc ∈ Wc, sc.bv ≠ scp) :
    schedulable t σ' = schedulable t σ := by
  have hrel := h.f.2.1
  cases e : schedulable t σ with
  | true =>
    obtain ⟨x, scp, y, k, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e
    exact schedulable_of (h.tcbS.2 h1) h2 h3 (h.kold h4) h5 (by rw [hrel]; exact h6)
  | false =>
    cases e' : schedulable t σ' with
    | false => rfl
    | true =>
      obtain ⟨x, scp, y, k, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e'
      have h1' := h.tcbS.1 h1
      rw [h.scS (hts x scp h1' h2)] at h4
      rw [schedulable_of h1' h2 h3 h4 h5 (by rw [← hrel]; exact h6)] at e
      cases e

theorem Sched.ActIdle.addS (hA : ActIdle σ) (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    (hts : ∀ t x scp, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some scp → ∀ sc ∈ Wc, sc.bv ≠ scp) :
    ActIdle σ' := by
  obtain ⟨-, hrel, -, hact, -, -, -, -, -, -, hidle, hisc⟩ := h.f
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  refine ⟨fun t ht => ?_, x, by rw [hidle]; exact h.tcbS.2 hx, by rw [hisc]; exact h1, h2,
    by rw [hidle, hrel]; exact h3⟩
  rw [hact] at ht
  rw [h.schedS (hts t)]; exact hS t ht

theorem Sched.CurInv.addS (hI : CurInv σ) (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    (hcs : ∀ sc ∈ Wc, sc.bv ≠ σ.curSc) : CurInv σ' := by
  obtain ⟨-, hrel, hct, -, hcsc, -, -, -, -, -, -, hisc⟩ := h.f
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, k, hx⟩ := hI.sc
  have e := h.scS hcs
  refine ⟨⟨xt, by rw [hct]; exact h.tcbS.2 hkt, by rw [hcsc]; exact hxs, hnb⟩,
    ⟨x, k, by rw [hcsc, e]; exact hx⟩, fun hne y m hy => ?_, by rw [hct, hrel]; exact hI.notRel⟩
  rw [hcsc, hisc] at hne; rw [hcsc, e] at hy
  exact hI.active hne y m hy

theorem CurInvW.addS (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) (hcs : ∀ sc ∈ Wc, sc.bv ≠ σ.curSc) :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.f.2.2.2.1]; exact e
  · right; exact hI.addS h hcs

theorem Sched.OffOK.addS (hO : OffOK σ) (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    (hcs : ∀ sc ∈ Wc, sc.bv ≠ σ.curSc) : OffOK σ' := by
  obtain ⟨-, -, -, -, hcsc, htime, hcons, -, -, -, -, hisc⟩ := h.f
  intro hc y k hy ha
  rw [hcons] at hc ⊢; rw [htime]
  rw [hcsc, h.scS hcs] at hy; rw [hcsc, hisc] at ha
  exact hO hc y k hy ha

theorem Sched.CurOwnW.addS {T C : Set U64} (hO : CurOwnW T C σ)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) (hcs : ∀ sc ∈ Wc, sc.bv ≠ σ.curSc) :
    CurOwnW T (C ∪ Wc) σ' := by
  obtain ⟨-, hrel, -, -, hcsc, -, hcons, -, -, -, -, -⟩ := h.f
  have e := h.scS hcs
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨⟨sc, hsc, hb⟩, hun⟩
  · refine Or.inl ⟨u, hu, xt, h.tcbS.2 hkt, by rw [hcsc]; exact hxs, fun y k hy => ?_, fun h0 hm => ?_⟩
    · rw [hcsc, e] at hy; exact hown y k hy
    · rw [hcons] at h0; rw [hrel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨⟨sc, Or.inl hsc, by rw [hcsc]; exact hb⟩, fun y k hy => ?_⟩
    rw [hcsc, e] at hy; exact hun y k hy

theorem prioOf_addS (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) (u : ObjRef) :
    Sched.prioOf σ' u = Sched.prioOf σ u := by
  cases hk : σ.kheap u with
  | some k =>
    have hk' := h.kold hk
    unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [hk, hk']
  | none =>
    cases hk' : σ'.kheap u with
    | none => unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [hk, hk']
    | some k =>
      rcases h.kback hk' with e | ⟨hw, rfl⟩
      · rw [hk] at e; cases e
      · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [hk, hk']; rfl

theorem Sched.IpcSorted.addS (hS : IpcSorted σ) (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) :
    IpcSorted σ' := by
  refine ⟨fun p x hp => ?_, fun p x hp => ?_⟩
  · exact (hS.1 p x ((h.lookS (fun _ _ e => by cases e)).1 hp)).congr fun u _ => prioOf_addS h u
  · exact (hS.2 p x ((h.lookS (fun _ _ e => by cases e)).1 hp)).congr fun u _ => prioOf_addS h u

theorem CurRunM.addS (hR : CurRunM σ) (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) :
    CurRunM σ' := by
  obtain ⟨-, -, hct, hact, -, -, -, -, -, -, hidle, -⟩ := h.f
  rcases hR with e | e
  · left; rw [hact]; exact e
  · right
    rcases e with r | r
    · left; intro y hy; rw [hct] at hy; exact r y (h.tcbS.1 hy)
    · right; rw [hct, hidle]; exact r

theorem Sched.NSC.addS {N C : Set U64} (hN : NSC N C σ)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) : NSC N (C ∪ Wc) σ' := by
  intro m hm x p hx hp
  obtain ⟨sc, hsc, e⟩ := hN m hm x p ((h.lookS (fun _ _ e => by cases e)).1 hx) hp
  exact ⟨sc, Or.inl hsc, e⟩

theorem Sched.SpecAdd.recvBS (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) {d : U64}
    (hd : RecvB σ' d) : RecvB σ d := by
  obtain ⟨x, t, xt, h1, h2, h3, h4⟩ := hd
  exact ⟨x, t, xt, (h.lookS (fun _ _ e => by cases e)).1 h1, h2, h.tcbS.1 h3, h4⟩

/-- **The call-stack relation over fresh SCs** (empty stacks, `LstC`; the
reply head words zero). -/
theorem Sched.CallRel.addS {m : U64 → U64} {R C : Set U64} {Lst : U64 → List U64} (hC : CallRel m R C σ Lst)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    (hm : ∀ sc ∈ Wc, m (scReplyA sc) = 0#u64) :
    CallRel m R (C ∪ Wc) σ' (LstC C Lst) := by
  refine ⟨fun sc hsc => ?_, fun sc hsc sc' hsc' r hr hr' => ?_, fun r hr => ?_, fun d hd' hdet => ?_⟩
  · by_cases hc : sc ∈ C
    · rw [LstC_in hc]
      obtain ⟨⟨y, k, hk, e⟩, h2, h3, h4⟩ := hC.stack sc hc
      exact ⟨⟨y, k, h.kold hk, e⟩, h2, h3, h4⟩
    · rw [LstC_out hc]
      have hw : sc ∈ Wc := ((Set.mem_union _ _ _).1 hsc).resolve_left hc
      refine ⟨⟨defaultSchedContext, n, (h.new _ ⟨sc, hw, rfl⟩).2, rfl⟩, ?_, List.nodup_nil, ?_, ?_⟩
      · intro r hr; simp at hr
      · rw [hm sc hw]; rfl
      · intro i hi; simp at hi
  · by_cases hc : sc ∈ C
    · by_cases hc' : sc' ∈ C
      · rw [LstC_in hc] at hr; rw [LstC_in hc'] at hr'; exact hC.excl sc hc sc' hc' r hr hr'
      · rw [LstC_out hc'] at hr'; cases hr'
    · rw [LstC_out hc] at hr; cases hr
  · obtain ⟨x, hx, e⟩ := hC.reply r hr
    refine ⟨x, h.kold hx, fun p => (e p).trans ⟨fun ⟨sc, hsc, h1, h2⟩ => ⟨sc, Or.inl hsc, h1, by rw [LstC_in hsc]; exact h2⟩,
      fun ⟨sc, hsc, h1, h2⟩ => ?_⟩⟩
    by_cases hc : sc ∈ C
    · exact ⟨sc, hc, h1, by rw [LstC_in hc] at h2; exact h2⟩
    · rw [LstC_out hc] at h2; cases h2
  · obtain ⟨h1, h2, h3⟩ := hC.det d hd' (detached_lstC.1 hdet)
    exact ⟨h1, fun h0 => let ⟨a, b, c⟩ := h2 h0; ⟨a, detached_lstC.2 b, c⟩,
      fun h0 => let ⟨a, b, c⟩ := h3 h0; ⟨a, detached_lstC.2 b, c⟩⟩

theorem Sched.RFree.addS {m : U64 → U64} {R C : Set U64} {Lst : U64 → List U64} (hF : RFree m R C σ Lst)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) :
    RFree m R (C ∪ Wc) σ' (LstC C Lst) := by
  intro d hd ⟨x, hx, hn⟩
  obtain ⟨h1, h2, h3⟩ := hF d hd ⟨x, (h.lookS (fun _ _ e => by cases e)).1 hx, hn⟩
  exact ⟨detached_lstC.2 h1, h2, h3⟩

theorem Sched.YieldRel.addS {T C : Set U64} {m : U64 → U64} (hY : YieldRel T C m σ)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) : YieldRel T (C ∪ Wc) m σ' := by
  refine ⟨fun t ht => ?_, fun t ht h0 => ?_, fun sc hsc y k hy p hp => ?_⟩
  · obtain ⟨x, hx, e⟩ := hY.tcb t ht
    exact ⟨x, h.kold hx, e⟩
  · obtain ⟨h1, y, k, hy, e⟩ := hY.toSc t ht h0
    exact ⟨Or.inl h1, y, k, h.kold hy, e⟩
  · rcases h.scB hy with e | ⟨-, rfl, -⟩
    · rcases hsc with hsc | hsc
      · exact hY.frm sc hsc y k e p hp
      · rw [(h.new _ ⟨sc, hsc, rfl⟩).1] at e; cases e
    · cases hp

/-- `CKeep` of a CNode-only step. -/
theorem cnCKeep (hC : CnStep σ σ') : Sched.CKeep σ σ' :=
  ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq, rfl, rfl⟩,
    fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩

theorem cnYKeep (hC : CnStep σ σ') : YKeep σ σ' :=
  ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩,
    fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩

theorem addS_McpKeep (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) (hC : CnStep σ' σ'') :
    McpKeep σ σ'' :=
  fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF (h.kold hp); ⟨y, hy, hc.mcp⟩

theorem addS_BufKeep (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) (hC : CnStep σ' σ'') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ''.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF (h.kold hp); ⟨y, hy, hc.buf⟩

theorem addS_recvB (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n)) (hC : CnStep σ' σ'')
    {d : U64} (hd : RecvB σ'' d) : RecvB σ d :=
  h.recvBS (hC.toHStep.khrb.recvB hd)

theorem Sched.RRecv.addS {R : Set U64} {m m' : U64 → U64} (hR : RRecv m R σ)
    (h : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext defaultSchedContext n))
    (hC : CnStep σ' σ'') (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d)) :
    RRecv m' R σ'' := fun d hd hr => by
  obtain ⟨h1, h2⟩ := hR d hd (addS_recvB h hC hr)
  exact ⟨(hm d hd).2.trans h1, (hm d hd).1.trans h2⟩

theorem fresh_sc (k : Nat) : FreshOK (.schedContext defaultSchedContext k) := Or.inr (Or.inl ⟨k, rfl⟩)

end Spec


/-! ## `JAtZ` with `C` grown -/

section Frame
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` at sets with `C` grown by fresh SCs** (XTopJointUtEp's
`JAtZ.add_frame` with `Z'.C = Z.C ∪ Wc`, the new SCs not null). -/
theorem JAtZ.add_frameC {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {Wc : Set U64}
    (hth : Z'.th = Z.th) (hC : Z'.C = Z.C ∪ Wc) (hW0 : ∀ q ∈ Wc, q ≠ 0#u64) (hB : Z'.B = Z.B)
    (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR Z' s' a' σ') (hCs : JCs (L := L) Z' s' σ') (R : JRest (L := L) arI Z' H' Cs Ac' Lst' D' s' σ')
    (hKs : KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s')) (hthT : ∀ t, Z'.th t = some .tcb → t ∈ Z'.T)
    (hIp : IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hnk : ∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val)
    (hcov : Sched.SpecCover H' σ') (hobj : Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ')
    (hzH : (∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn))
    (hset : (∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R))
    (hscC : ∀ c z, H' c = some (.sc z) → c ∈ Z'.C)
    (hvc : Vs.VsSlotsW Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 (L.mem s'))
    (hbf : JBuf (L := L) Z' s' σ') (hext : JExt (L := L) Z'.th s')
    (hlv : LiveDN (L := L) Z'.th H' Cs Z'.G s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z'.th s', p ∈ D') :
    JAtZ (L := L) arI AR Z' H' Cs Ac' Lst' D' s' a' σ' := by
  have hTe : Z'.T = P1.Heap.tcbs H' := by
    obtain ⟨Tr, Cq, hJ⟩ := R.jpl
    exact Set.ext fun t => ⟨fun h => hzH.1 t h, fun h => hthT t ((hJ.tcb t).2 h)⟩
  have hRe : Z'.R = P1.Heap.replies H' := Set.ext fun r => ⟨fun h => hzH.2.2.1 r h, fun h => hset.2.2 r h⟩
  have hc0 : ∀ q ∈ Z'.C, q ≠ 0#u64 := by
    rw [hC]; rintro q (hq | hq)
    · exact J.c0 q hq
    · exact hW0 q hq
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX hTe hobj R.blk hset.2.1 R.jpl hc0
  exact ⟨hX, R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, hKs, hthT, by rw [hth]; exact J.thk, hIp, R.rp, R.apart,
    hnk, fun wp hw c hc => by
      simp only [P1.LawfulStore.nodeBase, hks]; rw [hB] at hw; exact J.nodeB wp hw c hc,
    R.jpl, hcov, hobj, hzH, hCs.sfree, hset, hscC, R.jcov,
    R.kern, hCs.del, hCs.ut, by rw [hth]; exact J.bound, hCs.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act,
    hc0, R.bsa, schedValid_rebuild hX hTe hRe hobj R.blk hset.1 hset.2.1 R.call R.yld hc0 R.inv hsl, R.isorted, hsl,
    R.curRun, R.blk, by rw [hth, hks]; exact J.intL, hvc, hbf.1, hbf.2.1, hbf.2.2, hext, hlv, hzD⟩

end Frame

end

end Fl4Proofs.P3
