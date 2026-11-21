/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch9 (1)): **the frame helpers of `JAtZ` at `JAtZR`** (`cs_frame*`, `deadP_*`, `kern_keep`, `sch_*`, `finW_*`, `deadP_nfr`, …)

Scripted copies (sch9 gen.py: the transitive closure of the `JAtZ`-taking
lemmas used by the roots, with `JAtZ` -> `JAtZR`, `JRest` -> `JRestR`, other
copied names suffixed `ZR`); the proofs are the originals' except where
`cur` (now `CurInvR`, XTopJointJAtZR) is framed. Each section is headed by
its origin module.
-/
import Fl4Proofs.P3.XTopJointJAtZR
import Fl4Proofs.P3.ScJointFrame
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.XTopJoint
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.DeadKeep
import Fl4Proofs.P3.XTopJointRest
import Fl4Proofs.P3.ScJointSchFrame
import Fl4Proofs.P3.ScJointSchTail
import Fl4Proofs.P3.ScDeadSch
import Fl4Proofs.P3.XTopJointFinW
import Fl4Proofs.P3.XTopJointFin
open Aeneas Aeneas.Std Result

-- ===== from ScJointFrame
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
noncomputable section
section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- The sets' TCBs and replies are `H`'s. -/
theorem JAtZR.tcbs_eq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) : Z.T = P1.Heap.tcbs H ∧ Z.R = P1.Heap.replies H := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩,
    Set.ext fun r => ⟨fun h => J.zH.2.2.1 r h, fun h => J.hset.2.2 r h⟩⟩


end
end
end Fl4Proofs.P3
-- ===== from ScJointRest
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- **The idle words kept**: both states relate the current core's
`IDLE_THREAD` and `IDLE_SC` words to the spec's `idle_thread` and `idle_sc`
(`SchedSpec.idleTh`, `SchedSpec.idleSc`), which the step keeps. -/
theorem JAtZR.idleW_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hid : σ'.idleThread = σ.idleThread)
    (hisc : σ'.idleSc = σ.idleSc) : Sched.IdleKeep (L := L) s s' := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  constructor
  · unfold P1.LawfulStore.idleW
    apply P1.eq_of_bv
    have h1 := hs'.idleTh; have h2 := hs.idleTh
    unfold nodeW at h1 h2
    rw [hc'.cur, hc.cur, ← h1, ← h2, hid]
  · unfold Sched.idleScW
    apply P1.eq_of_bv
    have h1 := hs'.idleSc; have h2 := hs.idleSc
    unfold nodeW at h1 h2
    rw [hc'.cur, hc.cur, h1, h2, hisc]


/-- **`JCovD` after an SC step**, the dead set shrinking to `D'`: the dead
of `D'` dead after (`hdead`), the others of `D` covered after (`hcov`). -/
theorem JAtZR.sc_jcov {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    (hdead : ∀ q ∈ D', Sched.DeadP (L := L) H s' q)
    (hcov : ∀ q ∈ D, q ∉ D' →
      (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)))
    (hidl : Sched.IdleKeep (L := L) s s') :
    Sched.JCovD (L := L) Z.th H Z.G D' Cs s' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hk : ∀ y ∈ Z.G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ Z.G.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y :=
    fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩
  have JC := J.jcov
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, hdead,
    JC.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩,
    JC.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩⟩
  · rcases JC.th q k hq with hc | hd | hi
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((hcov q hd h).1 k hq)
    · exact Or.inr (Or.inr ((Sched.exAt_of hidl hks).2 hi))
  · rcases JC.h q k hq with hc | hd | hi
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((hcov q hd h).2 k hq)
    · exact Or.inr (Or.inr ((Sched.exAt_of hidl hks).2 hi))


end
end
end Fl4Proofs.P3
-- ===== from ScDeadStep
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- **A dead thread's `YIELD_TO` word stays null** (`YieldRel` before and
after, the spec's field kept null). -/
theorem JAtZR.deadY_tcb {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64} (hYD : YDeadKeep σ σ' q.bv) (hqT : q ∈ Z.T)
    (h0 : L.mem s (P1.yieldA q) = 0#u64) : L.mem s' (P1.yieldA q) = 0#u64 := by
  obtain ⟨x, hx, e⟩ := J.yld.tcb q hqT
  obtain ⟨y, hy, e'⟩ := hY'.tcb q hqT
  exact optRef_eq_none (by rw [← e', hYD.1 x hx (by rw [e, h0, optRef_zero]) y hy])


/-- `YMemDead` from the spec (`YieldRel` and `ScRelW` before and after, the
spec's fields kept null). -/
theorem JAtZR.ymd {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64}
    (hYD : YDeadKeep σ σ' q.bv) : YMemDead (L := L) H Z.C s s' q := by
  refine ⟨fun hq h0 => J.deadY_tcb hY' hYD (by rw [J.tcbs_eq.1]; exact hq) h0, fun z hq hqC h0 => ?_⟩
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
  obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
  rw [scYieldFromA_eq]; refine optRef_eq_none ?_; rw [← hR'.yieldFrom]
  exact hYD.2 x _ hk (by rw [hR.yieldFrom, ← scYieldFromA_eq, h0, optRef_zero]) x' _ hk'


set_option maxHeartbeats 1000000 in
/-- **An SC of `H` outside `Z.C` keeps its words** across an SC step: its
`TCB`, `REPLY` and `NTFN` words are in no TCB, notification or SC of the
sets, nor in the node (`H`'s objects disjoint, `hnd`). -/
theorem JAtZR.sc_out_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases tfoot_tcb hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
    have := hH.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
    have := J.kern.hnd q _ hq Z.c hcC
    simp only [P1.HKind.bits] at this
    omega
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
    have := hH.disj q _ n _ hq hHn hne
    simp only [P1.HKind.bits] at this
    omega
  · have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
    have := hH.disj q _ sc _ hq hHs hne
    simp only [P1.HKind.bits] at this
    omega



end
end
end Fl4Proofs.P3
-- ===== from XTopJoint
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
/-- **The other cores' timer words on `JAt`** (`OtherTmOK`): each other
core's node misses `H`'s objects (`JKern.hnd`), which hold the slots' CNodes
and TCBs (`JPlaced`), the sets' objects (`zH`), the SCs (`JPlaced.sc`) and the
arch objects (`SpecCover.arch`); it lies below the ASID table (`JKern.csLt`)
and misses the IPC-buffer words (`nodeB`). -/
theorem JAtZR.otherTmOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    OtherTmOK (L := L) Z Cs s σ := by
  intro c' hc' e
  have hX := J.xtop
  have K := J.kern
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hTe : Z.T = P1.Heap.tcbs H :=
    Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
  have hNP : P1.NodePlaced st Z.T s c' := by rw [hTe]; exact P1.TInv.nodes J.blk c' hc'
  have hlt := K.csLt c' hc'
  have hnb : L.nodeBase s c' = (L.ksb s).val + 13568 + c'.val * 4288 := rfl
  have hout : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c' ∨ L.nodeBase s c' + 4288 ≤ p.val :=
    fun p k hp => K.hnd p k hp c' hc'
  refine ⟨hNP, fun o ho => ?_⟩
  have hv := P1.nodeAt_val hNP (off := o) (by omega)
  have hb : L.nodeBase s c' ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val + 8 ≤ L.nodeBase s c' + 4288 := by
    rw [hv]; omega
  -- a word in an object of `H` of `2 ^ k.bits` bytes is not in the node
  have miss : ∀ p k, H p = some k → ¬ (p.val ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val < p.val + 2 ^ k.bits) :=
    fun p k hp ⟨h1, h2⟩ => by rcases hout p k hp with h | h <;> omega
  have hVs := hX.fin.2.1
  have hPt := hX.fin.2.2.1
  have arch : ∀ q : U64, (∃ ao, σ.kheap q.bv = some (.archObj ao)) →
      ¬ (q.val ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val < q.val + 4096) := by
    rintro q ⟨ao, hq⟩ ⟨h1, h2⟩
    obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hq
    have : (4096 : Nat) ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn; simpa using this
    exact miss q _ hH ⟨h1, by simp only [P1.HKind.bits]; omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- no VSpace object
    rintro (⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, h1, h2⟩ | ⟨h1, h2⟩)
    · exact miss q _ (hJ.cnode q r hq) ⟨h1, by simp only [P1.HKind.bits]; rw [pow_add]; omega⟩
    · exact miss t _ ((hJ.tcb t).1 ht) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · refine arch q ?_ ⟨h1, h2⟩
      rcases hq with hq | hq | hq | hq | hq
      · obtain ⟨f, hf, -⟩ := hVs.pool q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact ⟨_, hf⟩
    · rw [hnb] at hb; omega
  · -- no endpoint-relation word
    rintro (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩)
    · exact miss e _ (J.zH.2.1 e he) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · exact miss r _ (J.zH.2.2.1 r hr) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · obtain ⟨h1, h2⟩ := h; unfold Endp.TOffN at h2
      exact miss t _ (J.zH.1 t ht) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · unfold Endp.TL at h
      exact miss t _ (J.zH.1 t ht) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · have := J.nodeB wp hwp c' (J.kern.csLt c' hc'); rw [← h] at this; omega
  · -- no notification-relation word
    rintro (⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩)
    · exact miss n _ (J.zH.2.2.2 n hn) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · have hv' := nfootT_val (hX.fin.1.1.1.placed.tcb t ht) h
      exact miss t _ (J.zH.1 t ht) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
  · -- no SC word
    intro sc hsc x n hk ⟨h1, h2⟩
    obtain ⟨-, hH⟩ := hJ.sc sc x n (J.c0 sc hsc) hk
    exact miss sc _ hH ⟨h1, by simp only [P1.HKind.bits]; omega⟩


end
end
end Fl4Proofs.P3
-- ===== from XTopJointStep
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
noncomputable section
section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- `JAtZR.bok`/`fcov`/`fcap` across an `IpcFrKeep` step (`B` kept) whose
slots step by `VsSlotsT`. -/
theorem JAtZR.bfK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} (hfk : IpcFrKeep σ σ')
    (hT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s')) : JBuf (L := L) Z s' σ' :=
  ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.keepU hT hfk.page⟩


/-- `JAtZ.ks_nv` at `JAtZR` (KENTRY-PLAN g2b). -/
theorem JAtZR.ks_nv {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (h1 : (L.ksb s).val ≤ b.val)
    (h2 : b.val < (L.ksb s).val + 13568) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  intro t ht e
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hv := Sched.tVcpuA_val J.ip.e.tcb ht
  rw [e] at h1 h2
  rcases hq.ksOut t (J.zH.1 t ht) with h | h <;> omega

theorem JAtZR.ksW_nv {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : KsW (L.ksb s) b) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  obtain ⟨K, h1, h2, -, e, -⟩ := hb
  exact J.ks_nv (by omega) (by omega)

theorem JAtZR.schW_nv {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (h : SchW (L := L) Z.T Z.c s b) : ∀ t ∈ Z.T, b ≠ tVcpuA t := by
  have hT : P1.TcbPlaced Z.T := J.ip.e.tcb
  intro u hu
  rcases h with ⟨y, hy, rfl | rfl | rfl⟩ | h | h
  · exact Sched.tVcpuA_ne (K := 3480) hT hy hu (tfield_val (hT y hy) (by simp)) (by omega) (by omega)
  · exact Sched.tVcpuA_ne (K := 3488) hT hy hu (tfield_val (hT y hy) (by simp)) (by omega) (by omega)
  · exact Sched.tVcpuA_ne (K := 3592) hT hy hu (tfield_val (hT y hy) (by simp)) (by omega) (by omega)
  · exact Sched.KFoot.ne_vcpu J.xtop.fin.1.1.1 (Sched.KFoot.of_sfoot (Or.inr ⟨h.1, h.2.1⟩)) hu
  · have := domKW_val h
    exact J.ks_nv (by omega) (by omega) u hu

set_option maxHeartbeats 1000000 in
/-- **`JAtZR` across a CSpace-shaped step** (module docstring). -/
theorem JAtZR.cs_frameV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : Set U64 × Set U64 × Set U64 × Set U64 × Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hkb : KBack σ σ') (hbf : JBuf (L := L) Z s' σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRestR (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hvc : Vs.VsSlotsW Z.th V'.1 V'.2.1 V'.2.2.1 V'.2.2.2.1 V'.2.2.2.2 (L.mem s')) (hext : JExt (L := L) Z.th s')
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D') :
    JAtZR (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' :=
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.kback hkb) R.blk J.hset.2.1 R.jpl J.c0
  ⟨hX, R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, R.rp, R.apart,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, R.jpl, J.cover.kback hkb, J.obj.kback hkb, J.zH, hC.sfree, J.hset, J.hscC, R.jcov,
    R.kern, hC.del, hC.ut, J.bound, hC.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act, J.c0, R.bsa,
    schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.kback hkb) R.blk J.hset.1 J.hset.2.1 R.call R.yld J.c0 R.inv
      hsl, R.isorted, hsl, R.curRun, R.blk, by rw [hks]; exact J.intL, hvc, hbf.1, hbf.2.1, hbf.2.2, hext, hlv, hzD⟩


/-- `cs_frameV` at the same VSpace sets. -/
theorem JAtZR.cs_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR { Z with G := G' } s' a' σ') (hkb : KBack σ σ') (hfk : IpcFrKeep σ σ')
    (hC : JCs (L := L) { Z with G := G' } s' σ') (R : JRestR (L := L) arI { Z with G := G' } H Cs Ac' Lst' D' s' σ')
    (hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s')) (hv : VKeep (L := L) Z.th s s')
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D') :
    JAtZR (L := L) arI AR { Z with G := G' } H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameV (V' := Z.vs) hks hX hkb (J.bfK hfk hvT) hC R (J.vsc.step hvT) (J.ext.step hvT hv) hlv hzD


/-- **`cs_frameV` with the VSpace sets put back** (`XTopAt` at `Z`'s sets
after; the CSpace fields and `JRestR` from a post at any sets `V'`, which they
do not mention). -/
theorem JAtZR.cs_frameB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : XVs} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ') (hkb : KBack σ σ') (hbf : JBuf (L := L) Z s' σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRestR (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s')) (hext : JExt (L := L) Z.th s')
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D') :
    JAtZR (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameV hks hX hkb hbf ⟨hC.del, hC.ut, hC.finM, hC.sfree⟩
    ⟨R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, R.rp, R.apart, R.jpl, R.jcov, R.kern, R.utc, R.nsc, R.inv,
      R.cur, R.own, R.off, R.act, R.bsa, R.isorted, R.curRun, R.blk⟩ hvc hext hlv hzD


/-- **`cs_frameV` after IPC work** (`IRel` after, VSpace sets `V'`): the
sets put back to `Z`'s (`XTopAt.vs_backO`: FL4 wrote only `OObj` words, the
spec kept the arch state, arch objects and SC sizes) and the slots kept
(`SlotsSame`, so `JAtZR.vsc` carries over). -/
theorem JAtZR.cs_frameI {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : XVs} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hWV : ∀ b, W b → ∀ t ∈ Z.T, b ≠ tVcpuA t)
    (har : σ'.archState = σ.archState)
    (hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao)) (hsz : Sched.SzKeep σ σ')
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hkb : KBack σ σ') (hfk : IpcFrKeep σ σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRestR (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZR (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameB hks (J.xtop.vs_backO hX hW hWO har hao hsz) hkb (J.bfK hfk (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy))
    hC R (J.vsc.of_eq fun y hy => hSS.capV hy) (J.ext.ss hSS (VKeep.of_writes J.ip.e.tcb J.thT hW hWV))
    (J.liveX hX rfl rfl rfl hSS hK horig hidl fun p hp => R.jcov.dead p (hDD p hp)) (J.zDX hSS hDD)


/-- **The CSpace fields across a step keeping every slot and the objects'
sizes** (module docstring). -/
theorem JCs.sameZR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hk : KSz σ σ') : JCs (L := L) Z s' σ' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  refine ⟨J.del.of_same hSS, UtInv.of_same hM J.ut hSS, fun G hG => ?_, ?_⟩
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hk
    rw [← hSS.capV (hsl x' hx')]; exact hc


end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
/-- **What a step keeping the MDB ghost owes** (the per-kind premise's
shape): at the step's post, for every `JAtZR` before at the typed heap and
`XTopAt` after at the same sets, `JRestR` after. -/
def JOwesZR (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
    JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR Z s' a' σ' →
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JRestR (L := L) arI Z H Cs Ac' Lst' D s' σ'


variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
end
end
end Fl4Proofs.P3
-- ===== from DeadKeep
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
set_option maxHeartbeats 4000000 in
/-- **The dead stay dead** (module docstring). -/
theorem JAtZR.deadP_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hI' : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s') σ')
    {q : U64}
    (hT : ∀ x, σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 → ∃ y, σ'.kheap q.bv = some (.tcb y) ∧
      y.tcbState = x.tcbState ∧ y.tcbBoundNotification = x.tcbBoundNotification ∧
      (y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none))
    (hE : ∀ x, σ.kheap q.bv = some (.endpoint x) → σ'.kheap q.bv = some (.endpoint x))
    (hN : ∀ x, σ.kheap q.bv = some (.notification x) → ∃ y, σ'.kheap q.bv = some (.notification y) ∧
      (y.ntfnObj = x.ntfnObj ∨ ∀ l, y.ntfnObj ≠ .waitingNtfn l) ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
      (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none))
    (hRp : ∀ x, σ.kheap q.bv = some (.reply x) → ∃ y, σ'.kheap q.bv = some (.reply y) ∧ y.replyTcb = x.replyTcb)
    (hSc : ∀ x n, σ.kheap q.bv = some (.schedContext x n) → ∃ y, σ'.kheap q.bv = some (.schedContext y n) ∧
      (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧ (y.scNtfn = x.scNtfn ∨ y.scNtfn = none))
    (hRW : q ∈ Z.C → L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q))
    (hOut : ∀ z, H q = some (.sc z) → q ∉ Z.C → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K))
    (hidle : σ'.idleThread = σ.idleThread) (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') (hYD : YDeadKeep σ σ' q.bv)
    (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    obtain ⟨y, hy, hstate, hso, e⟩ := hT x hk hst0
    rw [hk'] at hy; cases hy
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_, J.deadY_tcb hY' hYD hqT d6⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := hso
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW nodeW; rw [hc'.cur]
      rw [← ea, ← e] at hact
      revert hact
      cases hsa : σ'.schedulerAction with
      | resumeCurThread =>
        intro h; simp only [ActRel] at h; subst h
        rw [J.kern.h0] at hq; cases hq
      | chooseNewThread =>
        intro h; simp only [ActRel] at h; subst h
        have := J.kern.heap.align _ _ hq
        simp [P1.HKind.bits] at this
      | switchThread t =>
        intro h; simp only [ActRel] at h
        obtain ⟨-, -, ht⟩ := h
        obtain ⟨x2, scp, -, -, hk2, hsc2, -⟩ := schedulable_inv (hAS t hsa)
        rw [← ht, hk'] at hk2; cases hk2
        rw [hxs'] at hsc2; cases hsc2
    · have ei : L.idleW s' = L.idleW s := by
        unfold P1.LawfulStore.idleW
        apply P1.eq_of_bv
        have h1 := hs'.idleTh; have h2 := hs.idleTh
        unfold nodeW at h1 h2
        rw [hc'.cur, hc.cur, ← h1, ← h2, hidle]
      rw [ei]; exact d5
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    rw [hE x hk] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb, e⟩ := hN x hk
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rcases ho with ho | ho
      · rw [ho] at hO'
        rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
      · revert hO'
        cases hx' : x'.ntfnObj with
        | waitingNtfn l => exact absurd hx' (ho l)
        | idleNtfn => intro hO'; rw [hO'.1]; decide
        | activeNtfn b => intro hO'; rw [hO'.1]; decide
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hRp x hk
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3, d4⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hSc x n hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [hRW hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
      · rw [scYieldFromA_eq]; refine optRef_eq_none ?_; rw [← hR'.yieldFrom]
        exact hYD.2 x _ hk (by rw [hR.yieldFrom, ← scYieldFromA_eq, d4, optRef_zero]) x' _ hk'
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb, hOut z hq hqC _ (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', hOut z hq hqC _ (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, hOut z hq hqC _ (by decide) (by decide), scW_ntfn]; exact d3
      · rw [scYieldFromA_eq, hOut z hq hqC _ (by decide) (by decide), ← scYieldFromA_eq]; exact d4



/-- **An SC of `H`'s words**: within its object, aligned. -/
theorem JAtZR.scW_in {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64}
    (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    P1.Aligned (scW q K) ∧ (scW q K).val = q.val + K.val ∧ q.val + K.val + 8 ≤ q.val + 2 ^ z := by
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  exact ⟨by show (scW q K).val % 8 = 0; rw [hv]; omega, hv, by omega⟩


/-- **`H`'s SC words are kept by kernel-state writes** (`H` off the block). -/
theorem JAtZR.ksW_scKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s)))
    {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  obtain ⟨hal, hv, hf⟩ := J.scW_in hq hK8 hK
  have := J.kern.hks q _ hq (fun _ e => by cases e)
  simp only [P1.HKind.bits] at this
  refine hw.mem_eq hal fun h => ?_
  obtain ⟨K', h1, h2, -, e⟩ := h
  omega


/-- **`H`'s SC words are kept by scheduler writes** (`H`'s objects disjoint
from the TCBs, apart from the node and the kernel-state block). -/
theorem JAtZR.schW_scKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (SchW (L := L) Z.T Z.c s))
    {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  obtain ⟨hal, hv, hf⟩ := J.scW_in hq hK8 hK
  have hS := J.xtop.fin.1.1.1
  have hP := J.xtop.fin.1.2
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hks := J.kern.hks q _ hq (fun _ e => by cases e)
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hnd := J.kern.hnd q _ hq Z.c hcC
  simp only [P1.HKind.bits] at hks hnd
  refine hw.mem_eq hal fun hb => ?_
  rcases schW_val hc.tcbs hkf hb with ⟨y, hy, e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e' => by rw [e', hHy] at hq; cases hq
    have := J.kern.heap.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · omega
  · omega


/-- **The dead stay dead across a heap-keeping step** (`deadP_keep` with
every object but the CNodes kept, `HStep`). -/
theorem JAtZR.deadP_hstep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {G' : MdbGhost} (hX' : XTopAt (L := L) AR { Z with G := G' } s' a' σ') (hC : HStep σ σ')
    (hRW : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q))
    (hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K)) (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') (hYK : YKeep σ σ')
    {q : U64} (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_keep hX'.fin.1.1.1 hX'.ipc (fun x hx _ => let ⟨y, hy, hc⟩ := hC.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
    (fun x hx => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, hC.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ⟨x, hC.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (hRW q) (fun z hz _ => hOut q z hz) hC.idle hAS hY'
    (hYK.dk q.bv) hd


/-- **`JCovD` across a step keeping every slot and the dead dead**
(`JCovD.same`, the MDB kept). -/
theorem JAtZR.jcov_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hks : L.ksb s' = L.ksb s)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hdead : ∀ q ∈ D, DeadP (L := L) H s' q)
    (hidl : Sched.IdleKeep (L := L) s s') :
    JCovD (L := L) Z.th H Z.G D Cs s' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  refine J.jcov.same (fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
    (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩) hidl hks
    (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩)


/-- **`JKern` across a step** keeping the kernel-state base, the core, the
current thread and SC, the original bits (new ones only at `AbsSlot`s), the
global PML4 and the arch
objects (ScJointRest's `sc_kern` for any write set). -/
theorem JAtZR.kern_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {D' : Set U64}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hct : σ'.curThread = σ.curThread) (hcsc : σ'.curSc = σ.curSc)
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hao : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao))
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    JKern (L := L) H Cs D' Z.th s' σ' := by
  have K := J.kern
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hcsc]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => (horig sl h).elim (K.orig sl) id, by rw [ecw, hct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hgp]; exact hao _ _ hpt⟩, by rw [hgp]; exact K.ga, by rw [hgp]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head



end
end
end Fl4Proofs.P3
-- ===== from XTopJointRest
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
noncomputable section
section Spec
open Fl4Spec
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
/-- **The scheduler's words a slot step keeps** (from `SlotsApart`): the TCBs'
`MCP`, `YIELD_TO` and IPC-buffer words, the SCs' `REPLY` words, the replies'
links. -/
theorem inSlot_keepsZR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hA := J.apart
  have tw : ∀ t ∈ Z.T, ∀ b : U64, P1.Aligned b → t.val + 256 ≤ b.val → b.val < t.val + 4096 → L.mem s' b = L.mem s b :=
    fun t ht b hb h1 h2 => inSlot_keep hw hb fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega
  refine ⟨fun t ht => tw t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
    fun t ht => tw t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega),
    fun t ht => tw t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, -⟩ := (hS.lists.choose_spec.choose_spec.2).scs q hq
    have hf := hfit x n hk
    exact inSlot_keep hw hal fun y hy => by
      rcases (hA y hy).2.2.2.1 q hq x n hk with h | h <;> omega
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    refine ⟨inSlot_keep hw (J.rp.aligned hr (Or.inl h8)) fun y hy => ?_,
      inSlot_keep hw (J.rp.aligned hr (Or.inr h16)) fun y hy => ?_⟩
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega


/-- **The scheduler's words a kernel-state step keeps** (as `inSlot_keepsZR`):
the TCBs, the SCs and the replies lie outside the kernel-state block. -/
theorem ksW_keepsZR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s))) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  refine ⟨fun t ht => ksW_keep hw (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; rcases hko t ht with h | h <;> omega),
    fun t ht => ksW_keep hw (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; rcases hko t ht with h | h <;> omega),
    fun t ht => ksW_keep hw (tIpcBufA_aligned (hT t ht)) (by
      rw [tIpcBufA_val (hT t ht)]; rcases hko t ht with h | h <;> omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, hx⟩ := hs.scs q hq
    have := (hS.scOutIn hq (a := scReplyA q) ⟨by rw [hv]; omega, by rw [hv]; omega⟩).2.2.2
    exact ksW_keep hw hal (Sched.ksb_word_out hal J.kern.ksbAl this)
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have hk := J.rp.ksb r hr
    exact ⟨ksW_keep hw (J.rp.aligned hr (Or.inl h8)) (by omega), ksW_keep hw (J.rp.aligned hr (Or.inr h16)) (by omega)⟩


/-- **`JPlaced` across a step** keeping every slot, the kernel-state base,
the SCs' sizes and the IRQ node's caps (`JPlaced.same`). -/
theorem JAtZR.jpl_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hkh : σ'.kheap = σ.kheap) (hks : L.ksb s' = L.ksb s)
    (hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i))
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨Tr, Cq, hJ.same hSS (fun c y n _ hk => ⟨y, by rw [← hkh]; exact hk⟩) hks hI hiw⟩


set_option maxHeartbeats 4000000 in
/-- **`JStepHyps.ks`**, with no premise, the dead set kept: FL4 writes kernel-state words only
(`ksW_keepsZR`), the spec keeps the heap and the scheduler's fields (`KsStep`,
so `CnStep`); the untyped caps' facts kept (the caps and their free parts lie
outside the kernel-state block); P1's `BlkOK` kept (`blk_of_capw`: the
kernel-state words are in `Ω` and none is an SC word, `SgOK`). -/
theorem jowes_ksDZR {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit)
    (hw : P1.WritesIn st s s' (KsW (L.ksb s))) (hO : KsStep σ σ') :
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th →
      JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → XTopAt (L := L) AR Z s' a' σ' →
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JRestR (L := L) arI Z H Cs Ac' Lst' D s' σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  have hC : CnStep σ σ' := ⟨⟨fun p => Or.inl (by rw [hO.kh]), hO.rel, hO.ct, hO.csc, hO.ctime, hO.cons, hO.idle, hO.isc⟩,
    hO.rq, hO.act⟩
  obtain ⟨k1, k2, kb, k3, k4⟩ := ksW_keepsZR arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hC.toHStep.khrb
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    have hw' : P1.WritesIn st s s' (fun b => KsW (L.ksb s) b ∧ P1.Aligned b) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn ⟨h, hb⟩⟩
    have hSg := J.blk.2.2.2.2
    have h0 := J.blk.1.choose_spec.choose_spec
    refine (P1.blk_of_capw J.blk hw' fun b hb => ?_).1
    obtain ⟨⟨K, h1, h2, -, e, -⟩, hal⟩ := hb
    refine Or.inr ⟨?_, fun hm => ?_⟩
    · have hK8 : K.val % 8 = 0 := by
        have := J.kern.ksbAl; have hb8 : b.val % 8 = 0 := hal; omega
      have eb : b = core.num.U64.wrapping_add (L.ksb s) K :=
        UScalar.eq_of_val_eq (by rw [P1.ks_val h0 h2]; exact e)
      rw [eb]; exact hSg.ksΩ K h2 hK8
    · have := hSg.ks b hm; omega
  have hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw J.kern.ksbFit J.kern.ksbAl fun b hb => by
      obtain ⟨K, -, -, -, e, h⟩ := hb; omega
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hf := J.kern.nodeFit
    have hv := nodeAt_val' (st := st) (s := s) (c := 0#u64) (off := layout.node.DEBUG_TCBS) (by simp; omega)
      (by simp [layout.node.DEBUG_TCBS])
    exact ksW_keep hw J.kern.dwAl (by rw [hv]; omega)
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hO.ct hO.csc (fun sl h => Or.inl (by rw [← hO.orig]; exact h)) hO.gpml4 (fun p ao h => by rw [hO.kh]; exact h)
    hDbg (D' := D)
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC.toHStep k3 (fun q z hq K h8 hK => J.ksW_scKeep hw hq h8 hK) (J.act.cn hC).1
      (J.yld.frame k2 yk) yk (J.jcov.dead q hq)
  -- the untyped caps' facts: the caps kept, the free parts outside the kernel-state block
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have hks : L.ksb s' = L.ksb s := hw.1
    have hcpu : L.cpu s' = L.cpu s := hw.2.1
    have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
      rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
    have U := J.utc sl p sb fi dev hsl hcap0 hdv
    have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
    have hfi := U.fiLe
    have hk8 := J.kern.ksbAl
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, fun g w hal h1 h2 => ?_, U.sb4,
      U.nostr, U.nsFree, fun h0 => U.ns (by rw [hO.cdt] at h0; exact h0),
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [hO.gpml4]; exact U.gReg (B g)⟩
    · have hw8 : w.val % 8 = 0 := hal
      have hapart := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).1
      rw [ksW_keep hw hal (by omega)]
      exact U.zero (B g) w hal h1 h2
    · rw [hO.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← hO.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  exact ⟨Ac, Lst, ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_kheap hO.kh),
    J.jpl_keep arI hSS hO.kh hw.1 hI (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc).2, J.jcov_keep hw.1 hSS hdead (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc), hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, (fun e => (J.cur (by rw [← hC.act]; exact e)).cn hC.toHStep), J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep (Or.inr hC.act), hblk⟩⟩


/-- **The scheduler's words a scheduler step keeps** (as `inSlot_keepsZR`, for
`SchW`: the TCBs' queue words, the node, the domain words). -/
theorem schW_keepsZR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (SchW (L := L) Z.T Z.c s)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  have hP := J.xtop.fin.1.2
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hc.ksOut t ht with h | h <;> omega
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hnd := hc.node.disj
  -- a word apart from the TCBs' queue words, the node and the domain words
  have keep : ∀ b : U64, P1.Aligned b → (∀ y ∈ Z.T, b.val ≠ y.val + 3480 ∧ b.val ≠ y.val + 3488 ∧ b.val ≠ y.val + 3592) →
      (b.val < L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ b.val) →
      (b.val + 8 ≤ (L.ksb s).val + 16 ∨ (L.ksb s).val + 216 < b.val) → L.mem s' b = L.mem s b := by
    intro b hb h1 h2 h3
    refine hw.mem_eq hb fun hb' => ?_
    rcases schW_val hT hkf hb' with ⟨y, hy, e | e | e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
    · exact (h1 y hy).1 e
    · exact (h1 y hy).2.1 e
    · exact (h1 y hy).2.2 e
    · omega
    · omega
  have tw : ∀ t ∈ Z.T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := by
    intro t ht K h1 h8 n1 n2 n3
    have hv := Notif.tfield_val (hT t ht) h1 (K := K)
    refine keep _ (P1.field_aligned (hT t ht) h1 h8) (fun y hy => ?_) ?_ ?_
    · by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hP.ep ht hy e; omega
    · have := hnd t ht; omega
    · rcases hko t ht with h | h <;> omega
  refine ⟨fun t ht => tw t ht 3440#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
    fun t ht => tw t ht 3472#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
    fun t ht => tw t ht 3512#u64 (by simp) (by simp) (by simp) (by simp) (by simp), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, -⟩ := sc_reply_word hS hq
    obtain ⟨-, o1, o2, o3⟩ := hS.scOutIn hq (a := scReplyA q) ⟨by rw [hv]; omega, by rw [hv]; omega⟩
    refine keep _ hal (fun y hy => ?_) (by omega) (by omega)
    rcases o2 y hy with h | h <;> omega
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have hk := J.rp.ksb r hr
    have ht := J.rp.tcb r hr
    refine ⟨keep _ (J.rp.aligned hr (Or.inl h8)) (fun y hy => ?_) (by omega) (by omega),
      keep _ (J.rp.aligned hr (Or.inr h16)) (fun y hy => ?_) (by omega) (by omega)⟩
    · rcases ht y hy with h | h <;> omega
    · rcases ht y hy with h | h <;> omega


set_option maxHeartbeats 4000000 in
/-- **`JStepHyps.sched`**, with no premise: FL4 writes the scheduler's words
(`schW_keepsZR`), the spec keeps the heap (`SchedK`, so `HStep`); `Inv`, the
current thread's invariant and `ActIdle` after (`SchedQOK`: the ready queues
gain schedulable threads only, the action kept or `chooseNewThread`); P1's
`BlkOK` after (`BlkKeep`); the node-0 debug word and the untyped caps'
facts kept (the footprint `SchW` misses them). -/
theorem jowes_schedZR {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit)
    (hS : SchedStep (L := L) th s σ s' σ') :
    JOwesZR (L := L) arI AR th s a σ s' a σ' := by
  intro Z H Cs Ac Lst D hth J hX'
  subst hth
  obtain ⟨hK, hS2, hQ, hBK⟩ := hS
  have hw := (hS2 Z.N Z.T Z.C Z.c J.thT J.xtop.fin.1.1.1 J.xtop.fin.1.1.2.2.1).2.1
  have hC : HStep σ σ' := ⟨fun p => Or.inl (by rw [hK.kh]), hK.rel, hK.ct, hK.csc, hK.ctime, hK.cons, hK.idle, hK.isc⟩
  obtain ⟨k1, k2, kb, k3, k4⟩ := schW_keepsZR arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hC.khrb
  -- the spec's scheduler invariants after
  have hI' : Inv σ' := J.inv.congr' hK.kh (fun d p u hu => by
    rcases hQ.1 d p u hu with ⟨d', p', h'⟩ | hs
    · exact J.inv.rq d' p' u h'
    · obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
      exact ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩) hK.rel hK.ctime
  have hcur' : CurInvR σ' := fun e => by
    rcases hQ.2 with e' | e'
    · rw [e'] at e; cases e
    · exact (J.cur (by rw [← e']; exact e)).congr hK.kh hK.ct hK.csc hK.rel hK.isc
  have hA' : ActIdle σ' := by
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases hQ.2 with e | e
      · rw [e] at ht; cases ht
      · rw [e] at ht; rw [schedulable_heap hK.kh hK.rel]; exact J.act.1 t ht
    · obtain ⟨x, h1, h2, h3, h4⟩ := J.act.2
      exact ⟨x, by rw [hK.kh, hK.idle]; exact h1, by rw [hK.isc]; exact h2, h3, by rw [hK.idle, hK.rel]; exact h4⟩
  have hblk := hBK _ _ _ H _ _ _ _ _ Ac (fun t ht => J.zH.1 t (J.thT t ht)) J.blk
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hko : ∀ t ∈ Z.T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val := fun t ht => by
    rcases hcq.ksOut t ht with h | h <;> omega
  have h88 : (layout.node.DEBUG_TCBS).val = 88 := by simp [layout.node.DEBUG_TCBS]
  -- the node-0 debug word: no TCB queue word (the TCBs miss the kernel-state
  -- block), not core `c`'s node but its own debug word, no domain word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hf := J.kern.nodeFit
    have hv : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = (L.ksb s).val + 13568 + 88 := by
      rw [nodeAt_val' (st := st) (s := s) (c := 0#u64) (off := layout.node.DEBUG_TCBS) (by simp; omega)
        (by simp [layout.node.DEBUG_TCBS])]
      simp [layout.node.DEBUG_TCBS]
    refine hw.mem_eq J.kern.dwAl fun hb => ?_
    rcases hb with hb' | ⟨g1, g2, g3⟩ | hb'
    · obtain ⟨y, hy, e⟩ := hb'
      have e' := tfield3_val (hcq.tcbs y hy) e
      rw [hv] at e'
      rcases hko y hy with h | h <;> omega
    · rw [hv, hnb] at g1 g2 g3
      omega
    · have := domKW_val hb'
      rw [hv] at this; omega
  -- the untyped caps' facts: the caps, the CDT and the original bits kept, the
  -- free parts off the TCBs, the node and the kernel-state block
  have hSS0 : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => schW_oobj J.xtop.fin.1.1.1.placed.tcb hb
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have hks : L.ksb s' = L.ksb s := hw.1
    have hcpu : L.cpu s' = L.cpu s := hw.2.1
    have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
      rw [← hSS0.capV hsl.isSlot]; exact capV_of_capAt hcap
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
    have U := J.utc sl p sb fi dev hsl hcap0 hdv
    have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
    have hfi := U.fiLe
    have hcZ : Z.c ∈ Cs := by rw [← hcq.cur]; exact J.kern.cpuCs
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, fun g w hal h1 h2 => ?_, U.sb4,
      U.nostr, U.nsFree, fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [hK.arch]; exact U.gReg (B g)⟩
    · have hapart := J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))
      have hnd := hapart.2.1 Z.c hcZ
      rw [hw.mem_eq hal fun hb => ?_]
      · exact U.zero (B g) w hal h1 h2
      rcases schW_val hcq.tcbs hkf hb with ⟨y, hy, e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
      · have hty : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
        have := U.free y _ hty
        simp only [objSize] at this
        rcases e with e | e | e <;> omega
      · omega
      · have := hapart.1; omega
    · rw [hK.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  have hI : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw hkf J.kern.ksbAl fun b hb => by
      rcases schW_val hcq.tcbs hkf hb with ⟨y, hy, e | e | e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
      all_goals first
        | omega
        | (rcases hko y hy with h | h <;> omega)
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hK.ct hK.csc (fun sl h => Or.inl (by rw [← hK.orig]; exact h)) (by rw [hK.arch])
    (fun p ao h => by rw [hK.kh]; exact h) hDbg (D' := D)
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b hb => schW_oobj J.xtop.fin.1.1.1.placed.tcb hb
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC k3 (fun q z hq K h8 hK => J.schW_scKeep hw hq h8 hK) hA'.1 (J.yld.frame k2 yk) yk
      (J.jcov.dead q hq)
  exact ⟨Ac, Lst, ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_kheap hK.kh),
    J.jpl_keep arI hSS hK.kh hw.1 hI (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc).2, J.jcov_keep hw.1 hSS hdead (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc), hkern, hutc, J.nsc.cn hC, hI', hcur', J.own.cn hC, J.off.cn hC, hA', J.bsa.cn hC, J.isorted.cn hC,
    J.curRun.cn hC hQ.2, hblk⟩⟩



end
end
end Fl4Proofs.P3
-- ===== from ScJointSchFrame
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
set_option maxHeartbeats 1000000 in
/-- **`JAtZR` across a scheduler step** (module docstring). -/
theorem JAtZR.sch_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ')
    (hown : Sched.CurOwnW Z.T Z.C σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hcr : CurRunM σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZR (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hT := hK.toTK
  have hobj0 := J.obj.tkw hT
  have hobj : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ' :=
    ⟨hobj0.tcb, hobj0.ntfn, hobj0.ep, hobj0.reply, hobj0.sc⟩
  have hcov0 := J.cover.tkw hT
  have hcov : Sched.SpecCover H σ' := ⟨hcov0.ntfn, hcov0.ep, hcov0.reply, hcov0.sc0, hcov0.arch⟩
  have hsrt0 := J.isorted.tkw hT
  have hsrt : Sched.IpcSorted σ' := hsrt0
  have hksz0 := hT.ksz
  have hksz : KSz σ σ' := hksz0
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl' : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (hobj) hblk J.hset.2.1 hjpl J.c0
  have hsv : Sched.SchedValid σ' := schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (hobj) hblk J.hset.1
    J.hset.2.1 hcall hyl J.c0 hinv hsl
  refine ⟨hX, hcall, hrf,
    J.rrecv.frame (Sched.TFoot.keep J.xtop.fin.1.1.1 J.rp hw).2.2 (Sched.KhRB.of_otk hK.kh), hyl, hmcp, hbuf,
    by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, hjpl, hcov, hobj, J.zH, ?_, J.hset, J.hscC, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, curInvR_of hcur, hown, hoff, hact,
    J.c0, hbsa, hsv, hsrt, hsl, hcr, hblk, by rw [hks]; exact J.intL,
    J.vsc.of_eq fun y hy => hSS.capV hy,
    J.bok.keep (IpcFrKeep.of_otk hK.kh), J.fcov.ipcFr (IpcFrKeep.of_otk hK.kh),
    J.fcap.keepU (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (IpcFrKeep.of_otk hK.kh).page,
    J.ext.ss hSS (VKeep.of_tfoot J.xtop.fin.1.1.1 J.thT hw),
    J.liveX hX rfl rfl rfl hSS hKd hK.orig hidl (fun p hp => hjc.dead p (hDD p hp)), J.zDX hSS hDD⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hksz
    rw [← hSS.capV (hsl' x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)




/-- **`BufWordRel` after a scheduler step** (`sc_buf` through `toTK`). -/
theorem JAtZR.sch_buf {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ') :
    BufWordRel Z.T (L.mem s') σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hb0 := hK.toTK.bufKeep
  have hb : BufKeep σ σ' := hb0
  exact J.buf.frame (fun t ht => hw.mem_eq (tIpcBufA_aligned (hc.tcbs t ht)) fun hb => hb.ne_buf hS ht rfl) hb


/-- **`SlotsApart` after a scheduler step.** -/
theorem JAtZR.sch_apart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ') :
    Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ' := by
  have hz0 := hK.toTK.szKeep
  have hz : Sched.SzKeep σ σ' := hz0
  exact J.apart.sc_frame hw.1 hz


/-- **`JPlaced` after a scheduler step.** -/
theorem JAtZR.sch_jpl {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hz0 := hK.toTK.szKeep
  have hz : Sched.SzKeep σ σ' := hz0
  have hwU : P1.WritesIn st s s' (UFoot st Z.T Z.N Z.C Z.R Z.c s σ) := hw.mono fun b hb => Or.inl hb
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_of_ufoot hJ.pl hS J.rp J.apart hwU
  have hIA := hJ.irqApart (c := Z.c) J.zH.1 J.zH.2.2.2 J.c0 J.zH.2.2.1 J.kern.ksbFit
  exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hz q.bv y n hq) hw.1 (irq_of_ufoot hS J.rp hIA hwU) hiw⟩



set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a scheduler step** (`sc_utc`'s proof; the
global PML4 kept by `SchStep`): the caps kept (slots
apart), the free parts zero (no SC-step word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state and
the node-0 `DEBUG_TCBS` word (`hDbg`, P1-supplied). -/
theorem JAtZR.sch_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj hS h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [hK.gpml4]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases tfoot_tcb hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hK.cdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), by rw [hna, hDbg]; exact r3⟩


end
end
end Fl4Proofs.P3
-- ===== from ScJointSchTail
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- **`JKern` across a scheduler step** (module docstring): the current SC
word's heap object (`hcscH`), the node-0
`DEBUG_TCBS` word kept and apart from the new thread's state word (`hDbg`,
`hdw`) given. -/
theorem JAtZR.sch_kern {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hdw : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val)
    (hcscH : H (L.cscW s') ≠ none) : JKern (L := L) H Cs D Z.th s' σ' := by
  have K := J.kern
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have ecw : L.curW s' = nodeW st s' Z.c layout.node.CUR_THREAD := by
    unfold P1.LawfulStore.curW nodeW; rw [hc'.cur]
  have hcT : L.curW s' ∈ Z.T := ecw ▸ hc'.curT
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  have hT := hK.toTK
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => K.orig sl (by rw [← hK.orig]; exact h), by rw [ecw]; exact hs'.curThread,
    (hJ.tcb _).2 (J.zH.1 _ hcT), by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu]; exact ⟨hdw, K.dwNe.2⟩, ?_,
    ⟨pt, by rw [hK.gpml4]; exact hT.archObj hpt⟩, by rw [hK.gpml4]; exact K.ga, by rw [hK.gpml4]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, J.zH.1 _ hcT, hcscH, K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head


/-- **The new current SC after a scheduler step**: `H`'s (the spec's SC,
`JPlaced`) and not dead (bound to the current thread, `CurInv`: its `TCB`
word is not 0, as a dead SC's is). -/
theorem JAtZR.sch_csc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.SchStep P σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hI' : Inv σ') (hC' : CurInv σ')
    (hdead : ∀ q ∈ D, Sched.DeadP (L := L) H s' q) : H (L.cscW s') ≠ none ∧ L.cscW s' ∉ D := by
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecs : L.cscW s' = nodeW st s' Z.c layout.node.CUR_SC := by
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA nodeW; rw [hc'.cur]
  have hcv0 : σ'.curSc = (L.cscW s').bv := by rw [ecs]; exact hs'.curSc
  obtain ⟨x, n, hx⟩ := hC'.sc
  have hobj0 := J.obj.tkw hK.toTK
  obtain ⟨c, hcC, hcv⟩ := hobj0.sc _ _ _ hx
  have hcw : c = L.cscW s' := P1.eq_of_bv (hcv.trans hcv0)
  rw [← hcw]
  obtain ⟨Tr, Cq, hJ⟩ := J.sch_jpl hw hK (Sched.idleScW_keep_of J.xtop.fin.1.1.1 hS' hK.isc)
  have hxc : σ'.kheap c.bv = some (.schedContext x n) := by rw [hcv]; exact hx
  have hHc := (hJ.sc c x n (J.c0 c hcC) hxc).2
  refine ⟨(by rw [hHc]; exact fun h => by cases h), fun hD => ?_⟩
  have d := ((hdead c hD).2.2.2.2 _ hHc).1
  obtain ⟨x', n', hk', hR⟩ := hs'.scs c hcC
  rw [hxc] at hk'; cases hk'
  obtain ⟨u, -, xt, -, -, hown, -⟩ := curOwn_of_curInv hS' hI' hC'
  have h1 := hR.tcb
  rw [hown x n hx, show scW c 24#u64 = P1.scTcbA c from scW_tcb c, d, optRef_zero] at h1
  cases h1


set_option maxHeartbeats 2000000 in
/-- **`JAtZR` after FL4's `schedule`** from `JAtZR` after the TCB timers
(module docstring). -/
theorem JAtZR.sch_tail {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    (hsc : Fl4Spec.schedule (Z := Unit) σ = ({((), σ')}, False))
    (hw : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ))
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hR' : NtfnStateRel Z.N Z.T (L.mem s') σ') (hN' : NSC Z.N Z.C σ')
    (hI' : Inv σ') (hC' : CurInv σ') (hA' : ActIdle σ') (hcr : CurRunW σ') (hoff : Sched.OffOK σ')
    (hbsa : Sched.BlockedScActive σ')
    (hT : SchTailHyps (L := L) AR Z H Cs D s s' a' σ' Ac') :
    ∃ Lst' : U64 → List U64, JAtZR (L := L) arI AR Z H Cs Ac' Lst' D s' a' σ' := by
  have hSch : SchS σ σ' := schs_schedule.of_eq hsc
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
    (J.sch_jpl hwT hK (J.idleW_keep hS' (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).1
        (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).2).2) (J.sc_jcov hwT hT.dead (fun q hq hn => absurd hq hn)
      (J.idleW_keep hS' (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).1
        (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).2))
    (J.sch_kern hwT hK hS' hT.dbg hT.dwNe (J.sch_csc hwT hK hS' hI' hC' hT.dead).1) (J.sch_utc hwT hK hT.dbg) hN' hI' (Or.inr hC')
    (Or.inl (curOwn_of_curInv hS' hI' hC')) hoff hA' hbsa (Or.inr hcr) hT.blk hT.dbgK
    (J.idleW_keep hS' (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).1
      (ik_schedule σ ((), σ') (by rw [hsc]; exact Set.mem_singleton _)).2).1 J.zD⟩


end
end
end Fl4Proofs.P3
-- ===== from ScDeadSch
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a scheduler step** (`deadP_sc_step` for a
`SchStep`, the idle thread by `ActIdle` after). -/
theorem JAtZR.deadP_sch_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    (hK0 : SchStep (fun _ => False) σ σ')
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hAI : ActIdle σ')
    {q : U64} (hYm : YMemDead (L := L) H Z.C s s' q) (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) :
    DeadP (L := L) H s' q := by
  have hK := hK0.toTK
  have hAS := hAI.1
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hS' := hX'.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  have hI' := hX'.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    obtain ⟨y, hy, hso, hst⟩ := hK.tcb hk
    replace hy : σ'.kheap q.bv = some (.tcb y) := hy
    rw [hk'] at hy; cases hy
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    have hstate : x'.tcbState = x.tcbState := by
      rcases hst with e | ⟨hp, -, -⟩
      · exact e
      · exact hp.elim
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      obtain ⟨y2, hy2, e⟩ := hL.tcb hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_, hYm.1 hq d6⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := by rw [hso]
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW nodeW; rw [hc'.cur]
      rw [← ea, ← e] at hact
      revert hact
      cases hsa : σ'.schedulerAction with
      | resumeCurThread =>
        intro h; simp only [ActRel] at h; subst h
        rw [J.kern.h0] at hq; cases hq
      | chooseNewThread =>
        intro h; simp only [ActRel] at h; subst h
        have := J.kern.heap.align _ _ hq
        simp [P1.HKind.bits] at this
      | switchThread t =>
        intro h; simp only [ActRel] at h
        obtain ⟨-, -, ht⟩ := h
        obtain ⟨x2, scp, -, -, hk2, hsc2, -⟩ := schedulable_inv (hAS t hsa)
        rw [← ht, hk'] at hk2; cases hk2
        rw [hxs'] at hsc2; cases hsc2
    · intro e
      obtain ⟨xi, hki, -, hsti, -⟩ := hAI.2
      have h1 := hs'.idleTh
      have ei : σ'.idleThread = q.bv := by
        rw [h1, e]; unfold P1.LawfulStore.idleW nodeW; rw [hc'.cur]
      rw [ei, hk'] at hki; cases hki
      rw [hstate] at hsti
      rw [hsti] at hst0
      simp [tsCode] at hst0
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    have hke : σ'.kheap q.bv = some (.endpoint x) := hK.ep hk
    rw [hke] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb⟩ := hK.ntfn' hk
    replace hy : σ'.kheap q.bv = some (.notification y) := hy
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      obtain ⟨y2, hy2, e⟩ := hL.ntfn hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rw [ho] at hO'
      rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hK.reply hk
    replace hy : σ'.kheap q.bv = some (.reply y) := hy
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3, d4⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hL.sc hW hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_, hYm.2 z hq hqC d4⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [(TFoot.keep hS J.rp hw).2.1 q hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', J.sc_out_keep hw hq hqC (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_ntfn]; exact d3
      · rw [scYieldFromA_eq, J.sc_out_keep hw hq hqC (by decide) (by decide), ← scYieldFromA_eq]; exact d4



end
end
end Fl4Proofs.P3
-- ===== from XTopJointFinW
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
noncomputable section
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
end
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- **The frame words a finalisation keeps**: the TCBs' `MCP`, `YIELD_TO` and
IPC-buffer words, the SCs' `REPLY` words, the replies' links. -/
theorem JAtZR.finW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have tsw : ∀ b, Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ b → TSW Z.T Z.C b := fun b hb => Ipc.FinW.tsw hS hb
  refine ⟨fun t ht => hw.mem_eq (mcpA_aligned hT ht) fun hb => ((tsw _ hb).1 t ht).1 (mcpA_val hT ht),
    fun t ht => hw.mem_eq (yieldA_aligned hT ht) fun hb => ((tsw _ hb).1 t ht).2.1 (yieldA_val hT ht),
    fun t ht => hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => ((tsw _ hb).1 t ht).2.2 (tIpcBufA_val (hT t ht)),
    fun q hq => hw.mem_eq (sc_reply_word hS hq).1 fun hb => (tsw _ hb).2 q hq rfl, fun r hr => ?_⟩
  have hal := J.rp.align r hr
  have h8 := rPrevA_val hal
  have h16 := rNextA_val hal
  have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
    hw.mem_eq (J.rp.aligned hr ha) fun hb => by
      rcases hb with hb | ⟨y, hy, K, -, hK, -, -, -, e⟩
      · exact hb.ne_rword hS J.rp hr ha rfl
      · have := J.rp.tcb r hr y hy; omega
  exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩


/-- **The header words of `H`'s SCs outside `Z.C` are kept** by a
finalisation (`sc_out_keep`'s argument). -/
theorem JAtZR.finW_scOut {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
    have := hH.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
    have := J.kern.hnd q _ hq Z.c hcC
    simp only [P1.HKind.bits] at this
    omega
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
    have := hH.disj q _ n _ hq hHn hne
    simp only [P1.HKind.bits] at this
    omega
  · have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
    have := hH.disj q _ sc _ hq hHs hne
    simp only [P1.HKind.bits] at this
    omega


/-- **The IRQ node's caps are kept** by a finalisation (its words lie in the
kernel-state block; the TCBs, notifications and SCs outside it, the node
after it). -/
theorem JAtZR.finW_irq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  refine irqNode_keep hw hkf J.kern.ksbAl (fun b hb => ?_) i hi
  rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
  · simp only [P1.LawfulStore.nodeBase] at g1; omega
  · have := J.nk n hn; omega
  · have := (hS.scOut sc hsc x n hk b ⟨g1, g2⟩).2.2.2; omega


set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a finalisation**: the caps kept (the slots
same), the free parts zero (no `FinW` word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state, CDT,
original bits and the node-0 `DEBUG_TCBS` word (`hDbg`). -/
theorem JAtZR.finW_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩


/-- **Core 0's `DEBUG_TCBS` word is kept by P1's footprint** (`KW` leaves it
out; core 0 among the cores, `JKern.cs0`). -/
theorem JAtZR.kw_dbg {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s)) :
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
  hw.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW J.blk J.kern.cs0 (Or.inl hk)

/-- `JAtZ.kw_dbgKeep` at `JAtZR`. -/
theorem JAtZR.kw_dbgKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s)) : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
  P1.Foot.dbgKeep J.blk (fun _ h => h) hw


end
end
end Fl4Proofs.P3
-- ===== from XTopJointFin
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
noncomputable section
section Spec
open Fl4Spec
variable {q : Bool} {r : ObjRef} {σ σ' : State Unit}
end Spec
section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
/-- **A notification's SC is bound back to it** (P1's `ObjsOK.nsc` through
the notification and SC relations). -/
theorem JAtZR.ntfn_link {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) :
    ∀ xn q, σ.kheap n.bv = some (.notification xn) → xn.ntfnSc = some q →
      ∃ y m, σ.kheap q = some (.schedContext y m) ∧ y.scNtfn = some n.bv := by
  intro xn q hk hq
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hx := J.xtop.ipc.toN.at_ntfn hn hk
  obtain ⟨sc, hscC, hscv⟩ := J.nsc n hn xn q hk hq
  rw [hx.sc] at hq
  have h0 : L.mem s (nScA n) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hq; cases hq
  have hqv : q = (L.mem s (nScA n)).bv := by rw [Sched.optRef_ne h0] at hq; exact (Option.some.inj hq).symm
  have hsc : sc = L.mem s (nScA n) := P1.eq_of_bv (hscv.trans hqv)
  obtain ⟨-, hback⟩ := J.blk.2.2.1.2.2.nsc n (J.zH.2.2.2 n hn) h0
  obtain ⟨x, m, hkx, hR⟩ := hs.scs sc hscC
  refine ⟨x, m, by rw [← hscv]; exact hkx, ?_⟩
  rw [hR.ntfn, scW_ntfn, hsc]
  have hback' : L.mem s (scNtfnA (L.mem s (nScA n))) = n := hback
  have hn0 : n ≠ 0#u64 := fun e => by have := J.zH.2.2.2 n hn; rw [e, J.kern.h0] at this; cases this
  rw [hback', Sched.optRef_ne hn0]


set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a step with the spec frame `NFr`** and the
footprint `FinW` (`deadP_keep`'s facts: a dead TCB's state and null bound
notification kept, a dead notification not waiting and unbound). -/
theorem JAtZR.deadP_nfr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {qq : Bool} {r : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : Sched.NFr qq r σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_)
    (fun x hx => F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e))
    (fun x hx => ?_)
    (fun x hx => ⟨x, F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e), rfl⟩)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.finW_scOut hw hz hqC hK8 hK)
    F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state and (null) bound notification kept
    obtain ⟨t, ht, e⟩ := J.obj.tcb q.bv x hx
    have htq : t = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t ht)
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t ht
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t = P1.boundA t from rfl, d3, optRef_zero]
    obtain ⟨st', bn, ar, hk3, hs, hbb⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, Or.inl rfl⟩
    · show st' = x.tcbState
      rcases hs with ⟨e, -⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e] at h0; simp [tsCode] at h0
    · show bn = x.tcbBoundNotification
      rcases hbb with e | e
      · exact e
      · rw [e, hbn]
  · -- a dead notification: not waiting, unbound
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, d2, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, -, hobj, hbd, hsc'⟩ := F.ntfnF hx
    have hbn : x.ntfnBoundTcb = none := by
      rw [hR.bound, show nBoundA n' = P1.ntfnBtA n' from rfl, d2, optRef_zero]
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, (hobj hnw).imp id And.right, ?_, hsc'⟩
    rcases hbd with e | e
    · exact e
    · rw [e, hbn]
  · -- an SC: its thread kept, its notification kept or cut
    obtain ⟨rf, nt, hk3, -, hn⟩ := F.scF hx
    exact ⟨_, hk3, Or.inl rfl, hn⟩


end
end
end Fl4Proofs.P3
