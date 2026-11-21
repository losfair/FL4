/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of SCs at `J`**
(handoff/utj.md "uttypes"): FL4's restart and `untyped::retype` from a CNode
slot's RAM untyped cap, without a reset (the cap has a child), of SCs
(type 5), end in XTopJointUt's `UtRetPostJ`: the spec's outcome related, with
`JAtZ` after at the sets with `C` grown by the window's SCs (UtScAdd's
`XTopAt.addStepC`, `JAtZ.add_frameC`), P1's heap after the creation (`HOut`,
the window's `sc` objects) and the dead set without the new objects.

* `perf_ut_mem`, `cscW_of_sched`: the spec's `fl4PerformInvocation` of an
  untyped invocation returns `[]`; the current SC word kept (at any SC sets).
* `Sched.SpecAdd.congrW`: `SpecAdd` at an equivalent address set.
* `JAtZ.kern_keepC`, `JAtZ.idleW_keepC`: DeadKeep's `kern_keep` and
  ScJointRest's `idleW_keep` with the scheduler relation after at any SC set.
* `JAtZ.scRest`: `JRest`'s scheduler-side fields at `C ∪ Wc` across the
  spec's `SpecAdd` of fresh SCs, a CNode-only step and FL4's slot writes (the
  call stacks `LstC`, `RPlaced`, `SlotsApart`, `RFree`, `RRecv`, yield, MCP,
  buffer words, `NSC`, `Inv`, `CurInv`, `CurOwnW`, `OffOK`, `ActIdle`,
  `BlockedScActive`, `IpcSorted`, `CurRunM`); its side conditions: the new
  SCs' reply words zero and kept, the old replies and slots apart from them,
  the current SC and every TCB's SC no new address.
* `JAtZ.addSetsC`: `SpecCover`, `ObjCover` (at `C ∪ Wc`), `zH`, `hset`,
  `hscC` over `HOut` with the new `sc` objects.
* `JAtZ.utScJ`: the step (premises as `JAtZ.utEpJ`: `BufObjHyp`,
  `ArchFitHyp`, `RegionUnrefJ` [J], `Z.c = 0`; the new SCs' bytes miss the
  kernel-state block by `JCovD.ks`, `SchedRel.scOut` asking `a < ksb ∨ ksb +
  13568 ≤ a` of each byte). The side conditions above
  come from the window: the untyped's free part holds no spec object
  (`SpecFree`), no typed-heap object (`UtCapP3.free`), misses the kernel-state
  block, the node (`JCovD.ks`) and the idle SC (`JCovD.idleOut`); its words
  are zero (`WinZero`).
-/
import Fl4Proofs.P3.UtReplyAdd
import Fl4Proofs.P3.UtScAdd
import Fl4Proofs.P3.UtBodyJ
import Fl4Proofs.P3.UtRetLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The spec's `fl4PerformInvocation` of an untyped invocation: `[]` after
`invoke_untyped`'s outcome. -/
theorem perf_ut_mem {σ1 σ' : Fl4Spec.State Unit} {inv : Fl4Spec.UntypedInvocation} (blk call don : Bool)
    (h : (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi inv).run σ1 = ({(.ok (), σ')}, False)) :
    ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1 :=
  mem_bindE_ok (mem_of_run h) (mem_returnOk [])

/-- `SpecAdd` at an equivalent address set (and objects agreeing on it). -/
theorem Sched.SpecAdd.congrW {σ σ' : Fl4Spec.State Unit} {W W' : Fl4Spec.ObjRef → Prop}
    {o o' : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (h : SpecAdd σ σ' W o) (hW : ∀ p, W p ↔ W' p)
    (ho : ∀ p, W p → o p = o' p) : SpecAdd σ σ' W' o' :=
  ⟨h.exst, h.abs, fun p hp => by
    have e := h.new p ((hW p).2 hp)
    rw [← ho p ((hW p).2 hp)]; exact e, fun p hp => h.old p (fun h' => hp ((hW p).1 h'))⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The current SC word is kept by a step keeping the kernel-state base,
the core and the spec's current SC (`SchedRel`'s lists; the SC sets before
and after may differ). -/
theorem cscW_of_sched {N T C C' : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hS' : Sched.SchedRel st N T C' c s' σ')
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s) (hcsc : σ'.curSc = σ.curSc) : L.cscW s' = L.cscW s := by
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  apply P1.eq_of_bv
  have h1 := hs'.curSc; have h2 := hs.curSc
  unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
  rw [hcpu, hna, hc.cur]
  unfold nodeW at h1 h2
  rw [hna] at h1
  rw [← h1, ← h2, hcsc]

/-- DeadKeep's `JAtZ.kern_keep` with the scheduler relation after at any SC
set `C'`. -/
theorem JAtZ.kern_keepC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {D' C' : Set U64}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T C' Z.c s' σ')
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
  have ecs : L.cscW s' = L.cscW s := cscW_of_sched J.xtop.fin.1.1.1 hS' hks hcpu hcsc
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

/-- ScJointRest's `JAtZ.idleW_keep` with the scheduler relation after at any
SC set `C'`. -/
theorem JAtZ.idleW_keepC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {C' : Set U64}
    (hS' : Sched.SchedRel st Z.N Z.T C' Z.c s' σ') (hid : σ'.idleThread = σ.idleThread)
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

set_option maxHeartbeats 2000000 in
/-- **`JRest`'s scheduler-side fields at `C ∪ Wc`** across fresh SCs, a
CNode-only step and FL4's slot writes (module docstring). -/
theorem JAtZ.scRest {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th))
    {σB σ' : Fl4Spec.State Unit} {Wc : Set U64} {n : Nat}
    (hA : SpecAdd σ σB (SWc Wc) (fun _ => .schedContext Fl4Spec.defaultSchedContext n)) (hcn : CnK σB σ')
    (hrep0 : ∀ sc ∈ Wc, L.mem s (scReplyA sc) = 0#u64)
    (hrepK : ∀ sc ∈ Wc, L.mem s' (scReplyA sc) = L.mem s (scReplyA sc))
    (hRoff : ∀ r ∈ Z.R, ∀ sc ∈ Wc, r.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ r.val)
    (hSoff : ∀ x, IsSlot Z.th x → ∀ sc ∈ Wc,
      x.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ x.val)
    (hcs : ∀ sc ∈ Wc, sc.bv ≠ σ.curSc)
    (hts : ∀ t x scp, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some scp → ∀ sc ∈ Wc, sc.bv ≠ scp) :
    CallRel (L.mem s') Z.R (Z.C ∪ Wc) σ' (LstC Z.C Lst) ∧ RPlaced st Z.N Z.T (Z.C ∪ Wc) Z.R Z.c s' σ' ∧
    RFree (L.mem s') Z.R (Z.C ∪ Wc) σ' (LstC Z.C Lst) ∧
    RRecv (L.mem s') Z.R σ' ∧ YieldRel Z.T (Z.C ∪ Wc) (L.mem s') σ' ∧ McpRel Z.T (L.mem s') σ' ∧
    BufWordRel Z.T (L.mem s') σ' ∧ NSC Z.N (Z.C ∪ Wc) σ' ∧ Inv σ' ∧
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T (Z.C ∪ Wc) σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
    BlockedScActive σ' ∧ IpcSorted σ' ∧ CurRunM σ' ∧
    SlotsApart (st := st) Z.th Z.T Z.N (Z.C ∪ Wc) Z.R Z.c s' σ' := by
  have hC := CnStep.of_cnK hcn
  have hS := J.xtop.fin.1.1.1
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlot_keeps arI J hw
  have ck := cnCKeep hC
  -- reply placement at `C ∪ Wc` before the CNode step
  have hRPB : RPlaced st Z.N Z.T (Z.C ∪ Wc) Z.R Z.c s σB := by
    refine ⟨J.rp.align, J.rp.ksb, J.rp.tcb, J.rp.ntfn, fun r hr sc hsc x m hx => ?_⟩
    rcases hsc with hsc | hsc
    · exact J.rp.sc r hr sc hsc x m (hS.scOld hA hsc hx)
    · obtain ⟨-, rfl⟩ := hA.scNew hsc hx
      exact hRoff r hr sc hsc
  have hCRB := J.call.addS hA hrep0
  obtain ⟨hCR', hRP'⟩ := CallRel.carry hCRB hRPB ⟨fun q hq => by
      rcases hq with hq | hq
      · exact k3 q hq
      · exact hrepK q hq, k4⟩ hw.1 ck
  refine ⟨hCR', hRP', RFree.carry (J.rfree.addS hA) hCRB k4 ck, J.rrecv.addS hA hC k4,
    (J.yld.addS hA).frame k2 (cnYKeep hC), J.mcp.frame k1 (addS_McpKeep hA hC),
    J.buf.frame kb (addS_BufKeep hA hC), (J.nsc.addS hA).cn hC.toHStep,
    (Inv.add J.inv hA (fun _ _ => fresh_sc n)).cn hC, CurInvW.cn (CurInvW.addS J.cur hA hcs) hC,
    (J.own.addS hA hcs).cn hC.toHStep, (J.off.addS hA hcs).cn hC.toHStep, (J.act.addS hA hts).cn hC,
    (BlockedScActive.add J.bsa hA (fun _ _ => fresh_sc n)).cn hC.toHStep, (J.isorted.addS hA).cn hC.toHStep,
    (J.curRun.addS hA).cn hC.toHStep (Or.inr hC.act), fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := J.apart x hx
  have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hw.1]
  refine ⟨h1, by rw [hnb]; exact h2, h3, fun sc hsc y m hy => ?_, h5⟩
  have hyB := hC.sc.1 hy
  rcases hsc with hsc | hsc
  · exact h4 sc hsc y m (hS.scOld hA hsc hyB)
  · obtain ⟨-, rfl⟩ := hA.scNew hsc hyB
    exact hSoff x hx sc hsc

set_option maxHeartbeats 2000000 in
/-- **The cover and heap fields at `C ∪ Wc` over `HOut`** with the window's
new `sc` objects (module docstring): the spec's objects after are the old
ones, changed CNodes or the window's new SCs. -/
theorem JAtZ.addSetsC {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {lo hi : Nat} (hfree : RegionFree Z.th lo hi)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (harch : ArchFitHyp H σ) {A0 k w : Nat} (hlo : lo ≤ A0) (hhi : A0 + w * k ≤ hi) (hk1 : 1 ≤ k) (hA0 : 0 < A0)
    {z : Nat} {H' : Heap} (hout : HOut H H' A0 (A0 + w * k) A0 k w (some (.sc z))) {σ' : Fl4Spec.State Unit}
    {m : Nat}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ q, NewAt A0 k w q ∧ q.bv = o ∧ ko = .schedContext Fl4Spec.defaultSchedContext m)) :
    Sched.SpecCover H' σ' ∧ Sched.ObjCover Z.N Z.T Z.E Z.R (Z.C ∪ winSet A0 k w) σ' ∧
    ((∀ t ∈ Z.T, H' t = some .tcb) ∧ (∀ e ∈ Z.E, H' e = some .ep) ∧ (∀ r ∈ Z.R, H' r = some .reply) ∧
      (∀ n ∈ Z.N, H' n = some .ntfn)) ∧
    ((∀ e, H' e = some .ep → e ∈ Z.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ Z.C ∪ winSet A0 k w) := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have offT : ∀ t ∈ Z.T, t.val + 4096 ≤ lo ∨ hi ≤ t.val := by
    intro t ht
    have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
    have := hfree t .tcb hth
    simp only [objSize] at this; omega
  have offE : ∀ e ∈ Z.E, e.val + 16 ≤ lo ∨ hi ≤ e.val := by
    intro e he
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.ep e he
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, UScalar.bv_toNat] at this; omega
  have offR : ∀ r ∈ Z.R, r.val + 32 ≤ lo ∨ hi ≤ r.val := by
    intro r hr
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  have offN : ∀ n ∈ Z.N, n.val + 64 ≤ lo ∨ hi ≤ n.val := by
    intro n hn
    obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n hn
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this; omega
  have keep : ∀ {q : U64} {kd : HKind}, H q = some kd → (q.val + 2 ^ kd.bits ≤ lo ∨ hi ≤ q.val) → H' q = some kd :=
    fun hq hoff => hout_old hout rfl rfl hk1 hq (by omega)
  have obk : ∀ o ko, σ'.kheap o = some ko → (∀ r cs, ko ≠ .cnode r cs) → (∀ y n, ko ≠ .schedContext y n) →
      σ.kheap o = some ko := by
    intro o ko h h1 h2
    rcases hback o ko h with e | ⟨r, cs, cs', -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact e
    · exact absurd rfl (h1 r cs')
    · exact absurd rfl (h2 _ _)
  have hcov : Sched.SpecCover H' σ' := by
    refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun y k0 ho => ?_, fun o ao ho => ?_⟩
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      refine keep (J.cover.ntfn o x e) ?_
      have := hspec _ _ e
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, HKind.bits] at this ⊢; exact this
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      refine keep (J.cover.ep o x e) ?_
      have := hspec _ _ e
      simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, HKind.bits] at this ⊢; exact this
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      refine keep (J.cover.reply o x e) ?_
      have := hspec _ _ e
      simp only [Fl4Spec.objBits, Fl4Spec.replyBits, HKind.bits] at this ⊢; exact this
    · rcases hback _ _ ho with e | ⟨r, cs, cs', -, e⟩ | ⟨q, ⟨j, hj, hqv⟩, hq0, -⟩
      · exact J.cover.sc0 y k0 e
      · cases e
      · have : q = 0#u64 := P1.eq_of_bv hq0
        subst this
        simp at hqv; omega
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      obtain ⟨n, hn12, hHn⟩ := J.cover.arch o ao e
      refine ⟨n, hn12, keep hHn ?_⟩
      have h1 := hspec _ _ e
      have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) (harch o ao n e hHn)
      simp only [HKind.bits]
      show o.toNat + 2 ^ n ≤ lo ∨ hi ≤ o.toNat
      omega
  have hobj : Sched.ObjCover Z.N Z.T Z.E Z.R (Z.C ∪ winSet A0 k w) σ' := by
    refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o y k0 ho => ?_⟩
    · exact J.obj.tcb o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h))
    · exact J.obj.ntfn o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h))
    · exact J.obj.ep o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h))
    · exact J.obj.reply o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ _ h => by cases h))
    · rcases hback _ _ ho with e | ⟨r, cs, cs', -, e⟩ | ⟨q, hq, hq0, -⟩
      · obtain ⟨c, hc, h⟩ := J.obj.sc o y k0 e; exact ⟨c, Or.inl hc, h⟩
      · cases e
      · exact ⟨q, Or.inr hq, hq0⟩
  refine ⟨hcov, hobj, ⟨fun t ht => ?_, fun e he => ?_, fun r hr => ?_, fun n hn => ?_⟩,
    ⟨fun e he => ?_, fun n hn => ?_, fun r hr => ?_⟩, fun c z' hc => ?_⟩
  · exact keep (J.zH.1 t ht) (by simp only [HKind.bits]; have := offT t ht; omega)
  · exact keep (J.zH.2.1 e he) (by simp only [HKind.bits]; have := offE e he; omega)
  · exact keep (J.zH.2.2.1 r hr) (by simp only [HKind.bits]; have := offR r hr; omega)
  · exact keep (J.zH.2.2.2 n hn) (by simp only [HKind.bits]; have := offN n hn; omega)
  · rcases hout_back hout he with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hset.1 e h
  · rcases hout_back hout hn with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hset.2.1 n h
  · rcases hout_back hout hr with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hset.2.2 r h
  · rcases hout_back hout hc with ⟨hna, -⟩ | h
    · exact Or.inr hna
    · exact Or.inl (J.hscC c z' h)


variable (arI) in
/-- **The outcome of a retype body at `J`** (handoff/utj.md Round 13): the
spec's `invoke_untyped` from `σ` has the single outcome `ok` at `σ'`, FL4's is
`Ok`, related by the CSpace relations, `DomRel` and `MdbOKV`, `JAt` after.
`utRetPostJ_of_body`: after the restart, `UtRetPostJ`. -/
def UtBodyPost (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) (inv : Fl4Spec.UntypedInvocation)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ', (Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi inv).run σ = ({(.ok (), σ')}, False) ∧
    res.1 = .Ok () ∧
    (∃ th' G', Placed th' ∧ CRel th' (L.mem res.2.1) σ' G' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
    JAt (L := L) arI AR res.2.1 res.2.2 σ'

theorem utRetPostJ_of_body {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool} {inv : Fl4Spec.UntypedInvocation}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : UtBodyPost (L := L) arI AR σ1 inv res) : UtRetPostJ (L := L) arI AR σ blk call don inv res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  refine ⟨σ1, hst1, (.ok [], σ'), perf_ut_mem blk call don hrun, ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

set_option maxHeartbeats 16000000 in
/-- **The body of `JAtZ.utScJ`: the retype of SCs without a reset from a
`JAtZ` state** (handoff/utj.md Round 13; as UtEpRet's `JAtZ.utEpBodyJ`):
from the state itself (after the restart, or after the restart and the
reset), the arguments' `RetCtx` there (any `reset` flag, `fiv = fi`),
`Entered`, and the kept references to a range of the cap's free part (`hRU`),
FL4's `untyped::retype` without a reset ends in `UtBodyPost`. -/
theorem JAtZ.utScBodyJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hnt : nt.val = 5) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      UtBodyPost (L := L) arI AR σ (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hBF : BufFreeHyp Z.B (L.mem s) Z.G := bufFree_of_obj J.sfree hBO
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hU := J.utc _ p sb fi false hAs hcap rfl
  have hnd : Sched.NotDev (L.mem s) (cslotAddr (pp.bv, idx)) p sb fi := Sched.notDev_ram (capV_of_capAt hcap)
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI0, -, hMO0, -⟩ := J.xtop.rel
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hty := hctx.ty
  have ht : t = .schedContextObject := ((objTypeOf_some hty (by omega) us.val).2.2.2.2.2).2 hnt
  have htU : t ≠ .untyped := by rw [ht]; exact fun h => by cases h
  have htP : t ≠ .archObject .pml4Obj := by rw [ht]; exact fun h => by cases h
  have htT : t ≠ .tcbObject := by rw [ht]; exact fun h => by cases h
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hty us.val).2.1
  have hz : zOf nt.val us.val = us.val := by simp [zOf, hnt]
  have hus7 : 7 ≤ us.val := by have := hctx.size.2.2.2.2; omega
  have hus64 : us.val < 64 := hctx.size.1
  have hn7 : us.val - Fl4Spec.minSchedContextBits + Fl4Spec.minSchedContextBits = zOf nt.val us.val := by
    rw [hz]; unfold Fl4Spec.minSchedContextBits; omega
  subst hfiv
  -- no restart here: the state the body starts at
  have hksz : KSz σ σ := fun o ko h => ⟨ko, h, rfl⟩
  -- the window, against the source cap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by rw [hz]; exact hus64)
    hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
  refine WP.spec_mono (retype_body (L := L) arI ar Z.th s σ Z.G hSR hV hP hM hC hI J.ut J.kern.orig hpp hidx hcap
    hU.pal hU.pfit hU.fiLe (hU.high hnd) hU.free (hU.zero hnd) Fl4Spec.fl4ObjBitsApi nt us dest off win t r hty
    (by omega) hctx.size.1 hctx.size.2.1 (fun _ => hus7) (fun h => by omega) hctx.cnode.1 hctx.cnode.2.1
    hctx.window.2.2 hctx.window.1 hctx.memory hctx.empty hb) (fun res hRP => ?_)
  have hRPN := RetPostB.toNB hRP
  obtain ⟨hok, har, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, Aw, k, w, dslot, cj,
    hE, hbr, hRFu⟩ := hRP
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, -, -, -, -, ⟨n0, hn0, hThX, uu, -, hcj⟩, -,
    hW, hWZ, -⟩
  · rw [hok] at e; cases e
  have hsR : sR = s ∧ thR = Z.th := by
    rcases hor with ⟨h1, h2, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h1, h2⟩
    · cases hRB
  obtain ⟨e2, e3⟩ := hsR
  subst sR
  subst thR
  have hn0v : n0 = nt.val := objTypeOf_inj hn0 hty
  subst hn0v
  have hk0 : thKindN nt.val us.val = none := by
    unfold thKindN; rw [if_neg (by omega), if_neg (by omega)]
  have hth : th' = Z.th := funext fun q => by rw [hThX.1 q, hk0]; simp
  subst hth
  -- FL4's writes: slot words
  have hw : P1.WritesIn st s res.2.1 (Sched.SlotWd Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact Sched.slotSpan_wd hP hb h
    · exact absurd h1 htP))⟩
  -- the spec's outcome: the window's SCs added, then CNodes changed
  have hSR1 := J.xtop.rel.2.1.1
  have hlen : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  obtain ⟨-, σB, hA, hcnk, hkc⟩ := invokeUntyped_noreset_add Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ htU htP {pp.bv, dest.bv} (Or.inl rfl)
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Or.inr rfl)
    (by
      rintro q (rfl | hq)
      · obtain ⟨cs, h, -⟩ := hSR1.cnode pp rs hpp; exact ⟨rs, cs, h⟩
      · rw [Set.mem_singleton_iff.1 hq]; obtain ⟨cs, h, -⟩ := hSR1.cnode dest r hctx.cnode.1; exact ⟨r, cs, h⟩)
    (by
      intro q hq
      rw [hlen] at hq
      obtain ⟨j, hj, rfl⟩ := regionPtrs_mem hq
      rw [hb] at hq ⊢
      have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have hfit := hU.pfit
      have hqv := ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
        (n := j * 2 ^ zOf nt.val us.val) (by have := Nat.one_le_two_pow (n := zOf nt.val us.val); omega)
      cases hq1 : σ.kheap (Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          (j * 2 ^ zOf nt.val us.val)) with
      | none => rfl
      | some ko =>
        exfalso
        obtain ⟨ko0, hko0, -⟩ := hksz _ _ hq1
        have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
        have h1 := Nat.one_le_two_pow (n := Fl4Spec.objBits ko0)
        have hz1 := Nat.one_le_two_pow (n := zOf nt.val us.val)
        rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap) _ ko0 hko0 with h | ⟨h2, h3⟩
        · rw [hqv] at h; omega
        · rw [hqv] at h2 h3; omega)
    (.ok (), σ') (by rw [hrun]; rfl)
  have hcjne : ∀ j, j < w → ∀ p b a, cj j ≠ .Pml4 p b a := by
    intro j _ p b a
    rw [hcj]
    simp [cjOf, newCapOf, hnt]
  have hTS : ∀ t0, Z.th t0 = some .tcb → ∀ p0 asid, capAt (L.mem res.2.1) (slotOf t0 1) = ok (.Pml4 p0 true asid) →
      capAt (L.mem s) (slotOf t0 1) = ok (.Pml4 p0 true asid) := by
    intro t0 ht0 p0 asid hc
    have hxs : IsSlot Z.th (slotOf t0 1) := ⟨t0, 1, Or.inr ⟨ht0, by decide⟩, rfl⟩
    exact retExp_pml4_back hE hM hM' hcjne hxs hc
  have hksR : L.ksb res.2.1 = L.ksb s := hw.1
  have hnbR : L.nodeBase res.2.1 Z.c = L.nodeBase s Z.c := by simp only [P1.LawfulStore.nodeBase, hksR]
  have hfit := hU.pfit
  have hhigh := hU.high hnd
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨k1, k2, -⟩ := J.jcov.ks _ hxG p sb fiv (capV_of_capAt hcap)
  obtain ⟨Q0, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have k2c := k2 Z.c hcC
  obtain ⟨Tr, Cq, hJp⟩ := J.jpl
  have hwb : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), p.val + fiv.val ≤ q.val ∧ q.val + 2 ^ (zOf nt.val us.val) ≤ p.val + 2 ^ sb.val ∧ q.val % 2 ^ (zOf nt.val us.val) = 0 := by
    intro q hq
    obtain ⟨b1, b2, b3⟩ := winSet_bd hq
    exact ⟨by omega, by omega, b3 hA2⟩
  have hreg : ∀ q ∈ (winSet (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val), q.bv ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) := by
    intro q hq
    obtain ⟨j, hj, e⟩ := hq
    rw [hlen, hb]
    unfold regionPtrs
    refine List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩
    have hjk : (j + 1) * 2 ^ (zOf nt.val us.val) ≤ win.val * 2 ^ (zOf nt.val us.val) := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    apply BitVec.eq_of_toNat_eq
    beta_reduce
    rw [ptrAdd_toNat (rb := Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (n := j * 2 ^ (zOf nt.val us.val))
      (by omega)]
    simp only [UScalar.bv_toNat]
    omega
  have hWZ' : WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat (2 ^ (zOf nt.val us.val)) win.val (t = .tcbObject) := by
    have h0 := hWZ ⟨rfl, htP⟩
    rw [eA, ek, ew, hlen, hb] at h0
    exact h0
  have hTn : ¬ t = .tcbObject := htT
  have hT0 : ∀ t0 ∈ Z.T, t0.val + 4096 ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ t0.val := by
    intro t0 ht0
    have hth : Z.th t0 = some .tcb := (hJp.tcb t0).2 (J.zH.1 t0 ht0)
    have := hU.free t0 .tcb hth
    simp only [objSize] at this; omega
  have hpos : 0 < 2 ^ (zOf nt.val us.val) := Nat.two_pow_pos _
  -- the window, with short names
  have hwv : w = win.val := by rw [ew, hlen]
  have hkv : k = 2 ^ zOf nt.val us.val := by rw [ek, hb]
  subst hwv hkv
  replace hE : RetExp Z.th Z.th (L.mem s) (L.mem res.2.1) Z.G G' Aw (2 ^ zOf nt.val us.val) win.val dslot cj
      (cslotAddr (pp.bv, idx)) := hE
  rw [← eA] at hwb hreg hWZ' hA1 hA2 hA3
  have hrev : ∀ o, o ∈ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length (2 ^ Fl4Spec.fl4ObjBitsApi t us.val) →
      ∃ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q.bv = o := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := regionPtrs_mem ho
    rw [hlen] at hj
    rw [hb]
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have := Nat.one_le_two_pow (n := zOf nt.val us.val)
    refine ⟨⟨Fl4Spec.ptrAdd (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (j * 2 ^ zOf nt.val us.val)⟩,
      ⟨j, hj, ?_⟩, rfl⟩
    show (Fl4Spec.ptrAdd _ _).toNat = _
    rw [ptrAdd_toNat (by omega), ← eA]
  -- the fresh SCs `Wc` = the window, as `SpecAdd` of SCs
  have hAS : SpecAdd σ σB (SWc (winSet Aw (2 ^ zOf nt.val us.val) win.val))
      (fun _ => .schedContext Fl4Spec.defaultSchedContext (us.val - Fl4Spec.minSchedContextBits)) :=
    hA.congrW (fun o => ⟨fun h => hrev o h, fun ⟨q, hq, e⟩ => by subst e; exact hreg q hq⟩)
      (fun o _ => by rw [ht]; rfl)
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ.kheap o = σ.kheap o := fun _ _ => rfl
  have hσ1c : ∃ y, σ.kheap (L.curW s).bv = some (.tcb y) := by
    obtain ⟨-, x, hx, -⟩ := J.curRunnable hni hc2; exact ⟨x, hx⟩
  have hcap1 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fiv false) := hcap
  have hsc1 : ∀ (q : U64) y n, σ.kheap q.bv = some (.schedContext y n) →
      ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = n + Fl4Spec.minSchedContextBits := by
    intro q y n hq
    by_cases ho : q.bv = (L.curW s).bv
    · obtain ⟨y1, hy1⟩ := hσ1c; rw [ho, hy1] at hq; cases hq
    · exact ⟨_, hq, by simp only [Fl4Spec.objBits]; omega⟩
  have hfr1 := J.free_noObj hAs hcap hBF rfl hsc1
  have hspec1 : ∀ o ko, σ.kheap o = some ko →
      o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
    intro o ko hk
    rcases J.sfree _ hxG p sb fiv (capV_of_capAt hcap1) o ko hk with (h | h) | ⟨h3, h4⟩
    · left; omega
    · right; exact h
    · left; exact h4
  have hSoff0 : ∀ x, IsSlot Z.th x → x.val + 32 ≤ p.val + fiv.val ∨ p.val + 2 ^ sb.val ≤ x.val := by
    rintro x ⟨q, i, hpi, rfl⟩
    obtain ⟨k, hk, hs⟩ := hpi.size
    rw [hpi.val hP]
    have := hU.free q k hk; omega
  have hmem : ∀ b : U64, P1.Aligned b → p.val + fiv.val ≤ b.val → b.val < p.val + 2 ^ sb.val →
      L.mem res.2.1 b = L.mem s b := fun b hb h1 h2 => hw.2.2 b hb (fun h => by
    obtain ⟨y, hy, g1, g2⟩ := slotWd_range hP h
    rcases hSoff0 y hy with g | g <;> omega)
  have e128 : 2 ^ 7 * 2 ^ (us.val - 7) = 2 ^ zOf nt.val us.val := by
    rw [hz, ← Nat.pow_add]; congr 1; omega
  have hscw : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ K : U64, K.val < 96 → K.val % 8 = 0 →
      (scW sc K).val = sc.val + K.val ∧ P1.Aligned (scW sc K) ∧ p.val + fiv.val ≤ (scW sc K).val ∧
      (scW sc K).val < p.val + 2 ^ sb.val ∧ sc.val % 8 = 0 ∧ K.val + 8 ≤ 2 ^ zOf nt.val us.val := by
    intro sc hsc K hK hK8
    obtain ⟨b1, b2, b3⟩ := hwb sc hsc
    have h1 := Nat.one_le_two_pow (n := us.val - 7)
    have h128 : sc.val % 128 = 0 := by
      rw [← Nat.mod_mul_right_mod sc.val 128 (2 ^ (us.val - 7)), show 128 * 2 ^ (us.val - 7) = 2 ^ zOf nt.val us.val
        from e128, b3]
    have hv : (scW sc K).val = sc.val + K.val := by
      unfold scW; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine ⟨hv, by unfold P1.Aligned; rw [hv]; omega, by rw [hv]; omega, by rw [hv]; omega, by omega, by omega⟩
  have hm : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ K : U64, K.val < 96 → K.val % 8 = 0 →
      L.mem s (scW sc K) = 0#u64 := by
    intro sc hsc K hK hK8
    obtain ⟨-, hal, g1, g2, h8, hK'⟩ := hscw sc hsc K hK hK8
    rw [← hmem _ hal g1 g2]
    have := (hwb sc hsc).2.1
    exact winZero_field hWZ' hTn hsc h8 (by omega) hK' hK8
  have hpl : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val,
      Fl4Proofs.P1.Placed sc (us.val - Fl4Spec.minSchedContextBits + Fl4Spec.minSchedContextBits) := by
    intro sc hsc
    rw [hn7]
    obtain ⟨b1, b2, b3⟩ := hwb sc hsc
    exact ⟨by rw [hz]; exact hus64, b3, by omega⟩
  have hid : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, sc.bv ≠ σ.idleSc := fun sc hsc =>
    J.xtop.fin.1.1.1.ne_idleSc (fun e => by
      have hI0 := (J.jcov.idleOut _ hxG _ _ _ (capV_of_capAt hcap1) _ (Or.inr rfl)).1
      obtain ⟨b1, b2, -⟩ := hwb sc hsc
      rw [← e] at hI0; omega)
  have hwa : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ a : U64,
      Sched.ScObj sc (us.val - Fl4Spec.minSchedContextBits) a → p.val + fiv.val ≤ a.val ∧ a.val < p.val + 2 ^ sb.val := by
    intro sc hsc a ha
    obtain ⟨b1, b2, -⟩ := hwb sc hsc
    unfold Sched.ScObj at ha; rw [hn7] at ha
    omega
  have hout : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ a : U64,
      Sched.ScObj sc (us.val - Fl4Spec.minSchedContextBits) a → ¬ Notif.NWrite Z.N Z.T a ∧
      (a.val < L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ a.val) ∧
      (∀ t ∈ Z.T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
      (a.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val) := by
    intro sc hsc a ha
    obtain ⟨g1, g2⟩ := hwa sc hsc a ha
    refine ⟨fun hN => ?_, ?_, fun t0 ht0 => ?_, ?_⟩
    · rcases nwrite_range J.xtop.fin.1.1.1.placed hN with ⟨n0, hn0, c1, c2⟩ | ⟨t0, ht0, c1, c2⟩
      · obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n0 hn0
        have := hspec1 _ _ hx
        simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this; omega
      · have := hT0 t0 ht0; omega
    · rcases k2c with h | h <;> omega
    · have := hT0 t0 ht0; omega
    · rcases k1 with h | h <;> omega
  have hdo : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ sc' ∈ Z.C, ∀ x' n',
      σ.kheap sc'.bv = some (.schedContext x' n') → ∀ a : U64,
      Sched.ScObj sc (us.val - Fl4Spec.minSchedContextBits) a → ¬ Sched.ScObj sc' n' a := by
    intro sc hsc sc' _ x' n' hk' a ha ha'
    obtain ⟨g1, g2⟩ := hwa sc hsc a ha
    have := hspec1 _ _ hk'
    have e7 : 2 ^ Fl4Spec.objBits (.schedContext x' n') = 2 ^ (n' + Fl4Spec.minSchedContextBits) := by
      simp only [Fl4Spec.objBits]; rw [Nat.add_comm]
    rw [e7] at this
    unfold Sched.ScObj at ha'
    simp only [UScalar.bv_toNat] at this
    omega
  have hdn : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ sc' ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val,
      sc ≠ sc' → ∀ a : U64, Sched.ScObj sc (us.val - Fl4Spec.minSchedContextBits) a →
      ¬ Sched.ScObj sc' (us.val - Fl4Spec.minSchedContextBits) a := by
    intro sc hsc sc' hsc' hne a ha ha'
    obtain ⟨j, hj, e1⟩ := hsc
    obtain ⟨j', hj', e2⟩ := hsc'
    unfold Sched.ScObj at ha ha'
    rw [hn7] at ha ha'
    rcases Nat.lt_trichotomy j j' with h | h | h
    · have := Nat.mul_le_mul_right (2 ^ zOf nt.val us.val) (show j + 1 ≤ j' by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    · subst h; exact hne (UScalar.eq_of_val_eq (by rw [e1, e2]))
    · have := Nat.mul_le_mul_right (2 ^ zOf nt.val us.val) (show j' + 1 ≤ j by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hnV : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ a : U64,
      Sched.ScObj sc (us.val - Fl4Spec.minSchedContextBits) a →
      ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) a := fun sc hsc a ha => by
    obtain ⟨g1, g2⟩ := hwa sc hsc a ha
    exact (hfr1 a g1 g2).2
  have hnE : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, ∀ a : U64,
      Sched.ScObj sc (us.val - Fl4Spec.minSchedContextBits) a → ¬ Endp.EWrite Z.T Z.E Z.R Z.B a := by
    intro sc hsc a ha hEw
    obtain ⟨g1, g2⟩ := hwa sc hsc a ha
    have hO := (hfr1 a g1 g2).1
    rcases hEw with ⟨e, he, h⟩ | ⟨r0, hr0, h⟩ | ⟨t0, ht0, h | h⟩ | ⟨wp, hwp, h⟩
    · exact hO (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, by omega, by omega⟩))))
    · exact hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, hr0, by omega, by omega⟩)))))
    · unfold Endp.TWF Endp.TWOffN at h; have := hT0 t0 ht0; omega
    · unfold Endp.TL at h; have := hT0 t0 ht0; omega
    · subst h
      exact hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hwp, le_refl _, by omega⟩)))))))
  have hX' := XTopAt.addStepC J.xtop hw hAS hcnk hkc ⟨hR', hV', hM', hC', hI'⟩ (hFin hFI0)
    (hSt.okv hMO0) hTS hc0 hpl hm hid hout hdo hdn hnV hnE
  -- the spec side
  obtain ⟨hcdtK, horgK⟩ := invokeUntyped_noreset_co Fl4Spec.fl4ObjBitsApi (pp.bv, idx) p.bv _ t us.val
    (windowSlots dest r off.val win.val) false σ htU htP (.ok (), σ') (by rw [hrun]; rfl)
  have hC2 := CnStep.of_cnK hcnk
  have hctB : σB.curThread = σ.curThread := by
    have e := congrArg Fl4Spec.AbstractState.curThread hA.abs; exact e
  have hcscB : σB.curSc = σ.curSc := by
    have e := congrArg Fl4Spec.AbstractState.curSc hA.abs; exact e
  have hidB : σB.idleThread = σ.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hA.abs; exact e
  have hiscB : σB.idleSc = σ.idleSc := by
    have e := congrArg Fl4Spec.AbstractState.idleSc hA.abs; exact e
  have hgp' : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcnk.1
    exact e.trans (congrArg (fun a => a.x64GlobalPml4) hA.arch)
  have hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao) := fun q ao h => by
    have hB := hA.kold h
    rcases hkc q with e | ⟨r0, cs, cs', e1, -⟩
    · rw [e]; exact hB
    · rw [hB] at e1; cases e1
  -- the window's slots
  have hslA : ∀ d ∈ windowSlots dest r off.val win.val, AbsSlot Z.th d ∧
      ∃ i, off.val ≤ i ∧ i < off.val + win.val ∧ d = (dest.bv, Fl4Spec.natToCref r i) := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    rw [List.mem_range'_1] at hi
    refine ⟨⟨dest, rfl, Or.inl ?_⟩, i, hi.1, hi.2, rfl⟩
    rw [natToCref_length _ _ (by have := hctx.cnode.2.1; omega)]; exact hctx.cnode.1
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := fun sl h => by
    by_cases hs : sl ∈ windowSlots dest r off.val win.val
    · exact Or.inr (hslA sl hs).1
    · exact Or.inl (by rw [← horgK sl hs]; exact h)
  -- FL4's writes: inside slots
  have hwI : P1.WritesIn st s res.2.1 (InSlot Z.th) := ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun h => hn (by
    rcases h with (⟨h1, -⟩ | h) | ⟨h1, -⟩
    · exact absurd h1 htT
    · exact h
    · exact absurd h1 htP))⟩
  have hidl : IdleKeep (L := L) s res.2.1 :=
    J.idleW_keepC hX'.fin.1.1.1 (hC2.idle.trans hidB) (hC2.isc.trans hiscB)
  -- P1's creation: the heap after, `BlkOK`, `JCovD`
  have hcjU : ∀ j, j < win.val → isUt (cj j) = false := by
    intro j _; rw [hcj]; simp [cjOf, newCapOf, hnt, isUt]
  obtain ⟨H', Ac', hblk', hout0, hjc'⟩ := J.create_noresetB hni hpp hidx hcap hE
    (hRU _ _ hA1 hA3) (fun _ => hcjU) ⟨by omega, fun _ => hus7⟩
    (k := 2 ^ zOf nt.val us.val) rfl hAk htT hW (fun _ => hWZ ⟨rfl, htP⟩) hidl
  -- `JPlaced` after
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap false p.bv sb.val fiv.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hgc : ∀ y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) Fl4Spec.fl4ObjBitsApi (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
        false)).run σ).1,
      ∀ o sz cs y0 n0, σ.kheap o = some (.cnode sz cs) → ¬ Fl4Spec.wellFormedCnodeN sz cs →
        y.2.kheap o ≠ some (.schedContext y0 n0) := by
    intro y hy o sz cs y0 n0 h0 _ hk
    rw [hrun] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    dsimp only at hk
    have hk' : σB.kheap o = some (.schedContext y0 n0) := by
      rcases hkc o with e | ⟨r0, cs0, cs', -, e2⟩
      · exact e.symm.trans hk
      · rw [e2] at hk; cases hk
    have hno : σ.kheap o ≠ none := by
      by_cases ho : o = (L.curW s).bv
      · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1]; simp
      · rw [h0]; simp
    rcases hA.kback hk' with h1 | ⟨hW', -⟩
    · by_cases ho : o = (L.curW s).bv
      · subst ho; obtain ⟨y1, hy1⟩ := hσ1c; rw [hy1] at h1; cases h1
      · rw [h0] at h1; cases h1
    · exact hno (hA.new _ hW').1
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨th2, σ2, A2, k2', w2, lo2, hi2, eA2, ek2, ew2, -, -, hor2, hhas2, hthx2, hJP2⟩ :=
    Sched.JPlaced.retypeG (L := L) hJp J.jcov J.ut hI hM hksz hRPN hok nt.val hty (by omega)
      (fun kd h => by rw [newKind_bits h, hb]) (fun kd h => by rw [newKind_bits h]; have := hctx.size.2.1; omega)
      (fun z h => by rw [(newKind_sc h).2]; exact hus7) (fun h => absurd h hn1) (fun h => absurd h hn1)
      J.kern.ksbAl J.kern.nodeFit (fun ct h => by rw [hc2] at h; cases eq_of_ok_eq h; exact J.kern.curT) J.intL
      J.sfree hgc (capV_of_capAt hcap) rfl hg1
      (fun _ => by rw [← eA]; exact hA1) (fun h => rfl) hidl.2
  have e1' : Aw = A2 := eA.trans eA2.symm
  have e2' : k2' = 2 ^ zOf nt.val us.val := by rw [ek2, hb]
  have e3' : w2 = win.val := by rw [ew2, hlen]
  subst e1' e2' e3'
  have hlohi : Aw = lo2 ∧ Aw + win.val * 2 ^ zOf nt.val us.val = hi2 := by
    rcases hor2 with h | ⟨-, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact ⟨h.1.symm, h.2.symm⟩
    · cases hRB
  obtain ⟨rfl, rfl⟩ := hlohi
  have hth2 : th2 = Z.th := funext fun q => by rw [(hthx2 rfl).1 q, hk0]; simp
  subst hth2
  obtain ⟨y2, hy2, -, hKS⟩ := hhas2
  rw [hrun] at hy2
  obtain rfl := Set.mem_singleton_iff.1 hy2
  have hJPa := (hJP2 H' hout0).of_kheap hKS.1
  -- `JKern` after
  have hDbg : L.mem res.2.1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hwI.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have K1 := J.kern_keepC (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hwI.1 hwI.2.1
    hX'.fin.1.1.1 (hC2.ct.trans hctB) (hC2.csc.trans hcscB) horig hgp' hao hDbg
  have hRD := (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fiv, capV_of_capAt hcap⟩).1
  have hoffD : ∀ q kd, H q = some kd → q ∉ D → H' q = some kd := fun q kd hq hqD =>
    hout_old hout0 rfl rfl hE.k1 hq (by
      by_contra hm
      exact hqD (hRD q kd hq (by unfold MeetsW; omega)).1)
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have hcsR : L.cscW res.2.1 = L.cscW s :=
    cscW_of_sched J.xtop.fin.1.1.1 hX'.fin.1.1.1 hwI.1 hwI.2.1 (hC2.csc.trans hcscB)
  have hcscH : H' (L.cscW res.2.1) ≠ none := by
    rw [hcsR]
    obtain ⟨kd, hkd⟩ := Option.ne_none_iff_exists'.1 J.kern.cscH
    rw [hoffD _ kd hkd (J.cscLive.resolve_right hres)]; simp
  have hcurR : (L.curW res.2.1).val + 2 ^ 12 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ (L.curW res.2.1).val := by
    have := hU.free _ .tcb K1.curT; simp only [objSize] at this; omega
  have hTb : ∀ q, H q = some .tcb → q.val + 4096 ≤ Aw ∨ Aw + win.val * 2 ^ zOf nt.val us.val ≤ q.val :=
    fun q hq => by
      have := hU.free q .tcb ((hJp.tcb q).2 hq); simp only [objSize] at this; omega
  have hnewK : ∀ q kd, NewAt Aw (2 ^ zOf nt.val us.val) win.val q → newKind nt.val us.val = some kd →
      (q.val + 2 ^ kd.bits ≤ (L.ksb res.2.1).val ∨ (L.ksb res.2.1).val + 13568 ≤ q.val) ∧
      ∀ c ∈ Cs, q.val + 2 ^ kd.bits ≤ L.nodeBase res.2.1 c ∨ L.nodeBase res.2.1 c + 4288 ≤ q.val := by
    intro q kd hq hK
    obtain ⟨j, hj, hqv⟩ := hq
    have hjk : (j + 1) * 2 ^ zOf nt.val us.val ≤ win.val * 2 ^ zOf nt.val us.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hbk : 2 ^ kd.bits = 2 ^ zOf nt.val us.val := by rw [newKind_bits hK]
    have hnb : ∀ c, L.nodeBase res.2.1 c = L.nodeBase s c := fun c => by
      simp only [P1.LawfulStore.nodeBase, hksR]
    refine ⟨?_, fun c hc => ?_⟩
    · rw [hksR, hbk]; rcases k1 with h | h <;> omega
    · rw [hnb, hbk]; rcases k2 c hc with h | h <;> omega
  have hA0 : 0 < Aw := by omega
  have K2 := K1.hout (D' := {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q}) hJPa.heap hout0 hE.k1 hA0 hnewK hcurR hcscH
  -- the untyped caps' facts after
  obtain ⟨-, p0, sb0, fi0, fi1, d0, e0, e1u, -, hAf1, -, -, -⟩ := hE.usrc
  rw [capV_of_capAt hcap] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp0, hsb0, hfi0, hd0⟩ := e0
  subst p0 sb0 fi0 d0
  have hsrcG' : cslotAddr (pp.bv, idx) ∈ G'.chains.flatten :=
    (hM'.members _).2 ⟨hAs.isSlot, _, capAt_capV _ _, by rw [e1u]; simp⟩
  have hfi1 : fi1.val ≤ 2 ^ sb.val := hU'.fib _ hsrcG' p sb fi1 false e1u
  have hDn0 : ∀ d ∈ windowSlots dest r off.val win.val, capAt (L.mem s) (cslotAddr d) = ok .Null := by
    intro d hd
    obtain ⟨-, i, h1, h2, rfl⟩ := hslA d hd
    rw [cslotAddr_natToCref _ _ _ (by have := hctx.cnode.2.1; omega) (by have := hctx.window.2.2; omega)]
    exact hctx.empty i h1 h2
  have hnull0 : ∀ d ∈ windowSlots dest r off.val win.val, cslotAddr d ∉ Z.G.chains.flatten := fun d hd h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hDn0 d hd] at h0; exact hn (eq_of_ok_eq h0).symm
  have hDu : ∀ d ∈ windowSlots dest r off.val win.val, ∀ p1 sb1 fi2 dv,
      capV (L.mem res.2.1) (cslotAddr d) ≠ .Untyped p1 sb1 fi2 dv := by
    intro d hd p1 sb1 fi2 dv e
    have hm : cslotAddr d ∈ G'.chains.flatten :=
      (hM'.members _).2 ⟨(hslA d hd).1.isSlot, _, capAt_capV _ _, by rw [e]; simp⟩
    rcases hE.gmem _ hm with h0 | ⟨j, hj, ej⟩
    · exact hnull0 d hd h0
    · rw [ej] at e
      have h3 := (hE.newc j hj).symm.trans e
      have h2 := hcjU j hj
      rw [h3, isUt_untyped] at h2; cases h2
  have hcapK : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) →
      (∀ d ∈ windowSlots dest r off.val win.val, y ≠ cslotAddr d) →
      capV (L.mem res.2.1) y = capV (L.mem s) y := by
    intro y hy hyx hyd
    by_cases hyG : y ∈ Z.G.chains.flatten
    · cases hu : isUt (capV (L.mem s) y)
      · exact (hE.keep y hyG hu).2
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := hE.usrc
        exact h5 y hyG hu hyx
    · have h0 : capV (L.mem s) y = .Null := by
        by_contra hn
        exact hyG ((hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩)
      rw [h0]
      by_contra hn
      have hm : y ∈ G'.chains.flatten := (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
      rcases hE.gmem y hm with h1 | ⟨j, hj, rfl⟩
      · exact hyG h1
      · have hD : Mdb.Desc G'.par (dslot j) (cslotAddr (pp.bv, idx)) :=
          (hE.desc _ _).2 (Or.inr ⟨j, hj, rfl, Or.inl rfl⟩)
        obtain ⟨b, hb1, -⟩ := Relation.TransGen.head'_iff.1 hD
        obtain ⟨d, hdA, hdy⟩ := hC'.par_slot _ _ hb1
        have hcd := hC'.cdt d hdA
        rw [hdy, hb1] at hcd
        by_cases hdW : d ∈ windowSlots dest r off.val win.val
        · exact hyd d hdW hdy.symm
        · rw [hcdtK d hdW] at hcd
          have hcd0 := hC.cdt d hdA
          rw [hdy, hcd] at hcd0
          exact hyG (hM.tree.par_mem _ _ hcd0.symm).1
  have hDL : DestLive Z.th (L.mem s) (L.ksb s) dest := by
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact DestLive.same (Or.inl ⟨y, rr, gs, g, hy, capV_of_capAt hcy⟩) (SlotsSame.refl _ _) rfl
  have hutc := J.ret_utc (G' := G') hAs (capV_of_capAt hcap1) e1u (by omega) hfi1
    (· ∈ windowSlots dest r off.val win.val) (fun d hd => (hslA d hd).1)
    (fun d hd => hDn0 d hd) hDu hcapK hwI hcdtK horgK hgp' hM'
    (RetExp.src_child hE hctx.window.1 hP' hC' hAs)
    (fun d hd sl p1 sb1 fi2 dev hsl hcv hdv hnc => by
      obtain ⟨-, i, -, -, rfl⟩ := hslA d hd
      exact J.live_slot arI hsl hcv hdv hnc ⟨dest, r, rfl, hctx.cnode.1,
        natToCref_length _ _ (by have := hctx.cnode.2.1; omega), hDL⟩)
  -- the spec's invariants and the call stacks at `C ∪ Wc` (`scRest`)
  have hnone : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, σ.kheap sc.bv = none :=
    fun sc hsc => (hAS.new _ ⟨sc, hsc, rfl⟩).1
  have hscOld : ∀ q ∈ Z.C, σ.kheap q.bv ≠ none := by
    intro q hq
    obtain ⟨Q, R1, -, hs1''⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨x, n, hk, -⟩ := hs1''.scs q hq
    rw [hk]; simp
  have hts : ∀ t0 x scp, σ.kheap t0 = some (.tcb x) → x.tcbSchedContext = some scp →
      ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, sc.bv ≠ scp := by
    intro t0 x scp hx hxs sc hsc e
    obtain ⟨t1, ht1, rfl⟩ := J.obj.tcb t0 x hx
    obtain ⟨Q, R1, -, hs1''⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨x1', hkx, -, -, hsc1', -⟩ := hs1''.tcb t1 ht1
    rw [hx] at hkx; cases hkx
    rw [hsc1'] at hxs
    obtain ⟨hne0, hbv⟩ := optRef_some hxs
    have hmC := hs1''.scMem t1 ht1 hne0
    have h0 := hscOld _ hmC
    rw [hbv, ← e, hnone sc hsc] at h0; exact h0 rfl
  have hcs : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, sc.bv ≠ σ.curSc := by
    intro sc hsc e
    rcases J.own with ⟨u, hu, xt, hkt, hxs, -, -⟩ | ⟨⟨c, hc, hcb⟩, -⟩
    · exact hts _ xt _ hkt hxs sc hsc e
    · have h0 := hscOld c hc; rw [hcb, ← e, hnone sc hsc] at h0; exact h0 rfl
  have hrep0 : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, L.mem s (scReplyA sc) = 0#u64 :=
    fun sc hsc => by rw [scReplyA_eq]; exact hm sc hsc 32#u64 (by simp) (by simp)
  have hrepK : ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val,
      L.mem res.2.1 (scReplyA sc) = L.mem s (scReplyA sc) := fun sc hsc => by
    obtain ⟨-, hal, g1, g2, -⟩ := hscw sc hsc 32#u64 (by simp) (by simp)
    rw [scReplyA_eq]; exact hmem _ hal g1 g2
  have hRoff : ∀ r ∈ Z.R, ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val,
      r.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (us.val - Fl4Spec.minSchedContextBits + Fl4Spec.minSchedContextBits) ≤ r.val := by
    intro r0 hr0 sc hsc
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r0 hr0
    have := hspec1 _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this
    obtain ⟨b1, b2, -⟩ := hwb sc hsc
    rw [hn7]; omega
  have hSoff : ∀ x, IsSlot Z.th x → ∀ sc ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val,
      x.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (us.val - Fl4Spec.minSchedContextBits + Fl4Spec.minSchedContextBits) ≤ x.val := by
    intro x hx sc hsc
    have := hSoff0 x hx
    obtain ⟨b1, b2, -⟩ := hwb sc hsc
    rw [hn7]; omega
  obtain ⟨hCR1, hRP1, hRF1, hRR1, hY1, hMc1, hBw1, hNSC1, hInv1, hCur1, hOwn1, hOff1, hAct1, hBsa1, hIs1, hCRun1,
    hSA1⟩ := J.scRest hwI hAS hcnk hrep0 hrepK hRoff hSoff hcs hts
  -- the cover and heap fields (`addSetsC`)
  have hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧
        ko = .schedContext Fl4Spec.defaultSchedContext (us.val - Fl4Spec.minSchedContextBits)) := by
    intro o ko hk
    have hb1 : ∀ ko', σB.kheap o = some ko' → σ.kheap o = some ko' ∨
        (∃ q, NewAt Aw (2 ^ zOf nt.val us.val) win.val q ∧ q.bv = o ∧
          ko' = .schedContext Fl4Spec.defaultSchedContext (us.val - Fl4Spec.minSchedContextBits)) := by
      intro ko' h
      rcases hAS.kback h with h1 | ⟨⟨q, hq, hqo⟩, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, hq, hqo, h2⟩
    rcases hkc o with e | ⟨r0, cs, cs', e1, e2⟩
    · rcases hb1 ko (e.symm.trans hk) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)
    · rw [e2] at hk; cases hk
      rcases hb1 _ e1 with h1 | ⟨_, -, -, he⟩
      · exact Or.inr (Or.inl ⟨r0, cs, cs', h1, rfl⟩)
      · cases he
  have harch1 : ArchFitHyp H σ := hAF
  have hK5 : newKind nt.val us.val = some (.sc us.val) := by simp [newKind, hnt]
  have hout' := hout0
  rw [hK5] at hout'
  obtain ⟨hcov', hobj', hzH', hset', hscC'⟩ :=
    J.addSetsC (lo := p.val + fiv.val) (hi := p.val + 2 ^ sb.val) hU.free hspec1 harch1 hA1 hA3 hE.k1 hA0 hout' hback
  -- the CSpace fields (`JCs`)
  have hcjZ : ∀ j, j < win.val → ∀ p1 zt n1, cj j ≠ .Zombie p1 zt n1 := by
    intro j _ p1 zt n1; rw [hcj]; simp [cjOf, newCapOf, hnt]
  have hob : ∀ cd, Fl4Spec.objBits (Fl4Spec.defaultObject t false us.val cd) ≤ Fl4Spec.fl4ObjBitsApi t us.val := by
    intro cd
    rw [hb, hz, ht]; simp [Fl4Spec.defaultObject, Fl4Spec.objBits, Fl4Spec.minSchedContextBits]; omega
  have hSF' : SpecFree (L.mem res.2.1) G' σ' := SpecFree.retype J.sfree J.ut hksz (capV_of_capAt hcap) rfl hg1
    (fun _ => by rw [← eA]; exact hA1) (y := (.ok (), σ')) (by rw [hrun]; rfl) rfl hU' hI' hE
    (fun _ => ⟨eA, by rw [hb], by rw [hlen], hRFu hok⟩) hob
  have hCs : JCs (L := L) { Z with G := G', C := Z.C ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val } res.2.1 σ' :=
    JCs.retype rfl rfl J.del hE hM hP' hM' hcjZ (fun _ _ _ h => h) hU' (hFin hFI0).fm hSF'
  -- `JRest` and `JAtZ` after
  have hJR : JRest (L := L) arI { Z with G := G', C := Z.C ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val } H' Cs Ac'
      (LstC Z.C Lst) {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} res.2.1 σ' :=
    ⟨hCR1, hRF1, hRR1, hY1, hMc1, hBw1, hRP1, hSA1, ⟨_, _, hJPa⟩, hjc', K2, hutc, hNSC1, hInv1, hCur1, hOwn1,
      hOff1, hAct1, hBsa1, hIs1, hCRun1, hblk'⟩
  have hW0 : ∀ q ∈ winSet Aw (2 ^ zOf nt.val us.val) win.val, q ≠ 0#u64 := fun q hq e => by
    subst e; obtain ⟨j, -, e⟩ := hq; simp at e; omega
  -- the VSpace caps placed (`JAtZ.vsc`): an old cap kept or an untyped cap,
  -- a new cap (an SC cap) set-free
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem res.2.1) := by
    obtain ⟨-, hCRZ, -, -, hMOZ, -, -⟩ := hX'.rel
    obtain ⟨P', L4', L3', L2', L1', hVI⟩ := hMOZ.2.2.1
    refine Vs.VsCapsW.slots (G := G') ?_ hCRZ.2.2.1
    intro x hx
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hu : isUt (capV (L.mem s) x) = true
      · exact Vs.vcapW_ut (hE.utk x hx0 hu)
      · rw [(hE.keep x hx0 (by simpa using hu)).2]
        exact J.vsc x ((hM.members x).1 hx0).1
    · have h1 := hVI _ hx
      rw [hE.newc j hj] at h1 ⊢
      have hT : Vs.SetFree (cj j) := by rw [hcj]; simp [cjOf, newCapOf, hnt, Vs.SetFree]
      exact (Vs.VCapOK.setFree hT h1).toW
  -- the buffer fields (`JBuf`): fresh SCs, then CNode slots; the new caps SC caps
  have hfk : IpcFrKeep σ σ' :=
    (IpcFrKeep.of_specAdd hAS (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e)).trans
      (IpcFrKeep.of_keepC hkc)
  have hbf : JBuf (L := L) { Z with G := G', C := Z.C ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val } res.2.1 σ' :=
    by obtain ⟨-, hCRZ, -⟩ := hX'.rel
       exact ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, J.fcap.retype hE hM hCRZ.2.2.1 (fun _ => UFr.keep hfk.page)
         (fun j _ => by rw [hcj]; simp [cjOf, newCapOf, hnt, Vs.FrIn])⟩
  -- `LiveDN` and `zD` after (UtRetLive's `ret_liveN`)
  have hTH : P1.Heap.tcbs H' = P1.Heap.tcbs H :=
    tcbs_hout hout0 (newKind_ne_tcb (by omega)) hE.k1 hTb
  have hnewZ : ∀ q ∈ ZTcb (L := L) Z.th s,
      q ∈ {q | q ∈ D ∧ ¬ NewQ Aw (2 ^ zOf nt.val us.val) win.val cj q} :=
    fun q hq => ⟨J.zD q hq, not_newQ_of_off hE.k1 (hTb q (J.zH.1 q (J.thT q (J.ztcb_tcb hq))))⟩
  have hWd : ∀ sl ∈ windowSlots dest r off.val win.val, ∃ p r', sl.1 = p.bv ∧ Z.th p = some (.cnode r') ∧
      sl.2.length = r' ∧ DestCap Z.th (L.mem s) p := fun sl hsl => by
    obtain ⟨-, i, -, -, rfl⟩ := hslA sl hsl
    obtain ⟨-, -, -, y, rr, gs, g, hy, hcy⟩ := hctx.cnode
    exact ⟨dest, r, rfl, hctx.cnode.1, natToCref_length _ _ (by have := hctx.cnode.2.1; omega),
      y, rr, gs, g, hy, capV_of_capAt hcy⟩
  obtain ⟨hLvN, hzDN⟩ := J.ret_liveN hX' rfl rfl rfl (fun _ _ h => h) (NewEmpty.refl _ _ _) hTH
    (dbgKeep_of_writes J.blk hwI fun _ hb => J.inSlot_notDbg hb)
    (fun q hq => hjc'.dead q (hnewZ q hq)) hnewZ (hC2.idle.trans hidB) hE hcjZ
    (windowSlots dest r off.val win.val) hWd hAs.isSlot hcapK (fun d hd => capV_of_capAt (hDn0 d hd))
    (fun d hd => invokeUntyped_cdt_slots _ _ _ _ _ _ _ _ _ σ (.ok (), σ') (by rw [hrun]; rfl) rfl d hd)
    horgK
  have JZ := J.add_frameC (Z' := { Z with G := G', C := Z.C ∪ winSet Aw (2 ^ zOf nt.val us.val) win.val })
    rfl rfl hW0 rfl hwI.1 hX' hCs hJR (by rw [hwI.1]; exact J.ks) J.thT J.ip
    (fun n hn => by rw [hwI.1]; exact J.nk n hn) hcov' hobj' hzH' hset' hscC' hvc hbf
    ⟨J.ext.nat.retype hE hM hX'.rel.2.1.2.2.1 (fun j _ => by rw [hcj]; exact Vs.nativeCap_newCapOf _ _ _ _), J.ext.vkeep (J.vkeep_slot hwI)⟩ hLvN hzDN
  refine ⟨σ', hrun, hok, ⟨Z.th, G', ?_⟩, ?_⟩
  · obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX'.rel
    exact ⟨hPl, hCR, hFI, hD, hMO⟩
  · rw [har]
    exact ⟨_, H', Cs, Ac', LstC Z.C Lst, _, JZ⟩

set_option maxHeartbeats 4000000 in
/-- **The no-reset retype of SCs at `J`** (module docstring; one core,
`Z.c = 0`, the new SCs' `CORE` word): from `JAtZ` at the decode (no
reschedule pending), the decoded arguments (`RetCtx`, no reset: the source
cap has a child), the source a CNode slot's RAM untyped cap, FL4's restart
and `untyped::retype` of SCs end in `UtRetPostJ` (done, `JAt` after at the
sets with `C` grown by the window's SCs). -/
theorem JAtZ.utScJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 5) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r false fiv)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s)
    (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false)
        res ⦄ := by
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  -- the restart (`JAtZ.restartJ`), then the body from its state
  obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, -, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : σ1.kheap (L.curW s).bv = some (.tcb { x1 with tcbState := .restart }) := by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hni1 : Entered σ1 :=
    ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact J.restart_keeps_resume hni hkx hcur⟩
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hctx1 : RetCtx (L := L) Z.th s1 σ1 (pp.bv, idx) sb fi false nt us dest off win t r false fiv :=
    ⟨hctx.ty, hctx.size, ⟨hctx.cnode.1, hctx.cnode.2.1, hctx.cnode.2.2.1, by
        obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
        exact ⟨y, rr, gs, g, hy, (hSS1.capAt hy).trans hcy⟩⟩, hctx.window,
      fun i h1 h2 => (hSS1.capAt ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩).trans
        (hctx.empty i h1 h2),
      by rw [hσ1cdt]; exact hctx.resetEq, hctx.fidx, hctx.sizeBits, hctx.memory, hctx.device⟩
  have hBO1 : BufObjHyp Z.B σ1 := fun wp hw => by
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hw
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hkx] at hk; cases hk
      exact ⟨_, _, hσ1c, h1, by simpa [Fl4Spec.objBits] using h2⟩
    · exact ⟨o, ko, by rw [hσ1k o ho]; exact hk, h1, h2⟩
  have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hσ1c] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  have hRU1 : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s1 ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s1 :=
    fun lo hi h1 h2 => hRU s1 hs1 lo hi (J.free_dead hxG (capV_of_capAt hcap) h1 h2)
  have hfiv : fiv = fi := by rw [hctx.fidx]; rfl
  rw [hs1]; simp only [bind_ok]
  exact WP.spec_mono (J1.utScBodyJ hni1 hpp hidx hcap1 hnt hc0 hctx1 hfiv hBO1 hAF1 hRU1)
    (fun res h => utRetPostJ_of_body hst1 h)


end

end

end Fl4Proofs.P3
