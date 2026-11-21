/-
P3 (DESIGN.md §9), VSpace: **`JAt` after the Unmap of a mapped table cap
whose table is in no set** (toward removing XTopJointEntry's
`JEntryGlob.vsTab`, handoff/vsreach.md "vs17 HANDOFF").

A detype may prune a mapped page table, directory or PDPT `q` from its set
while its cap still says mapped (handoff/vsreach.md); its Unmap zeroes `q`'s
frame (VsPtUnmapOff's `pt_unmap_rel_off` and its PD/PDPT forms) and leaves an
unmapped cap naming `q`, which `JAtZ.vsc` asks in its set. So:

* `TabEmptied.split`: the set `q` joins (by the cap's kind), and the old
  cap's placement there.
* `JAtZ.vsPostOffJ`: `JAt` after such an Unmap (VsTopX's `VsJPostO`), as
  XTopJointVsMap's `JAtZ.vsPostJ`: FL4's writes after the restart also in
  `q`'s frame (`vsStepJX` with `X = {q}`, `TabsArch`), and `XTopAt` after at
  the sets with `q` added (UtTabAdd's `XTopAt.addTab`: `q`'s words zero, its
  spec table empty, its frame apart from `OObj`, `VObj` and the typed heap).
-/
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.UtTabAdd
import Fl4Proofs.P3.VsOffTop
import Fl4Proofs.P3.VsOffDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The set an emptied table joins** (VsTopX's `TabEmptied`): `q` into
`L1`, `L2` or `L3` by the cap's kind, the spec's empty table there, and the
old cap placed at the grown sets. -/
theorem TabEmptied.split {c : capability.Cap} {q : U64} {σ : Fl4Spec.State Unit} (h : TabEmptied c q σ) :
    ∃ W3 W2 W1 : Set U64,
      (∀ q' ∈ W3, σ.kheap q'.bv = some (.archObj (.pdPointerTable fun _ => .invalidPDPTE))) ∧
      (∀ q' ∈ W2, σ.kheap q'.bv = some (.archObj (.pageDirectory fun _ => .invalidPDE))) ∧
      (∀ q' ∈ W1, σ.kheap q'.bv = some (.archObj (.pageTable fun _ => .invalidPTE))) ∧
      (∀ q', (q' ∈ W3 ∨ q' ∈ W2 ∨ q' ∈ W1) → q' = q) ∧
      ∀ P L4 L3 L2 L1 : Set U64, VCapW P L4 L3 L2 L1 c → VCapOK P L4 (L3 ∪ W3) (L2 ∪ W2) (L1 ∪ W1) c := by
  cases c with
  | PageTable p mp a v =>
    cases mp
    · exact h.elim
    · obtain ⟨rfl, hk⟩ := h
      refine ⟨∅, ∅, {p}, fun _ h => h.elim, fun _ h => h.elim, fun q' h => by rw [Set.mem_singleton_iff.1 h]; exact hk,
        fun q' h => ?_, fun P L4 L3 L2 L1 hw => ⟨Or.inr (Set.mem_singleton p), hw.2⟩⟩
      rcases h with h | h | h
      · exact h.elim
      · exact h.elim
      · exact Set.mem_singleton_iff.1 h
  | PageDirectory p mp a v =>
    cases mp
    · exact h.elim
    · obtain ⟨rfl, hk⟩ := h
      refine ⟨∅, {p}, ∅, fun _ h => h.elim, fun q' h => by rw [Set.mem_singleton_iff.1 h]; exact hk, fun _ h => h.elim,
        fun q' h => ?_, fun P L4 L3 L2 L1 hw => ⟨Or.inr (Set.mem_singleton p), hw.2⟩⟩
      rcases h with h | h | h
      · exact h.elim
      · exact Set.mem_singleton_iff.1 h
      · exact h.elim
  | Pdpt p mp a v =>
    cases mp
    · exact h.elim
    · obtain ⟨rfl, hk⟩ := h
      refine ⟨{p}, ∅, ∅, fun q' h => by rw [Set.mem_singleton_iff.1 h]; exact hk, fun _ h => h.elim, fun _ h => h.elim,
        fun q' h => ?_, fun P L4 L3 L2 L1 hw => ⟨Or.inr (Set.mem_singleton p), hw.2⟩⟩
      rcases h with h | h | h
      · exact Set.mem_singleton_iff.1 h
      · exact h.elim
      · exact h.elim
  | _ => exact h.elim

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`JAt` after the Unmap of a mapped table cap whose table `q` is in no
set** (module docstring): `JAtZ.vsPostJ`'s argument with FL4 also writing
`q`'s frame, and `JAtZ` after at the sets with `q` added. `q`'s facts at the
entry: 4 KiB-aligned, a spec arch object of a page, and its frame no `OObj`,
`VObj` or typed-heap word (XTopJointEntry's `JEntryAt.vsTyp`). -/
theorem JAtZ.vsPostOffJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {pc : U64} {r : Nat} {idx : List Bool} {c : capability.Cap} {q : U64}
    (hqa : q.val % 4096 = 0) (hTy : ∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12)
    (hfr : ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hF : FinXR (L := L) AR Z s' a' σ')
    (hV : VsJPostO (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.G pc r idx c q s ar σ s' a' σ') :
    JAt (L := L) arI AR s' a' σ' := by
  rcases hV with ⟨rfl, rfl, rfl⟩ | ⟨hW0, hpc, hidx, hc0, hnu, ⟨hSF, hLk, hsp⟩, hCR', hFI', hMO', hz, hTE⟩
  · exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨s1, σ1, x1, -, hst1, hk, hcur, hσ1, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hP := J.xtop.rel.1
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hact := J.kern.act
  -- FL4's restart
  have hF2 : Frame2 (L := L) s s1 (P1.stA ct) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have h := set_thread_state_frame (L := L) s ct sched.TS_RESTART (stA_al hP htcb) hact.1
    rw [hs1, WP.spec_ok] at h; exact h
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s ct sched.TS_RESTART htcb hact
    rw [hs1, WP.spec_ok] at h; exact h
  have hkc1 : L.ksb s1 = L.ksb s ∧ L.cpu s1 = L.cpu s := by
    have h := set_thread_state_cases (L := L) s ct sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h
    rcases h with rfl | rfl <;> simp
  -- the spec's step and `XTopAt` after
  have F : VsSFr σ1 σ' := vsSFr_of_post hst1 hsp
  have hks' : L.ksb s' = L.ksb s := hW0.1
  have hX' : XTopAt (L := L) AR Z s' a' σ' := by
    obtain ⟨hFin, ⟨G0, hPl, -, -, hD, -, hIA, hSA⟩, hE⟩ := hF
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFin
    exact ⟨hFin, ⟨hPl, hCR', hFI', hD, by rw [hks']; exact hMO', hIA, hSA⟩, IpcRel.of hNt hEp (sched_sc hSch), hE⟩
  -- the TCBs' state words and the action word, pinned
  have pinS : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s1 (P1.stA t) := by
    intro t ht
    have htT := J.thT t ht
    obtain ⟨y1, hk1, hR1⟩ := J1.xtop.ipc.tcb t htT
    obtain ⟨y, hky, hRy⟩ := hX'.ipc.tcb t htT
    obtain ⟨y', hy', hc⟩ := F.tcbF hk1
    rw [hky] at hy'; cases hy'
    have h1 : (L.mem s' (tStA t)).val = (L.mem s1 (tStA t)).val := by rw [hRy.st, hR1.st, hc.st]
    rw [stA_tStA]; exact UScalar.eq_of_val_eq h1
  have pinA : L.mem s' (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) =
      L.mem s1 (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have a1 := J1.xtop.fin.1.1.1.act
    have a2 := hX'.fin.1.1.1.act
    rw [F.act] at a2
    have e := ActRel.det a2 a1
    obtain ⟨Q, R, hc, -⟩ := J.xtop.fin.1.1.1.lists
    unfold nodeW at e
    rw [P1.nodeAt_of_ksb hks', P1.nodeAt_of_ksb hkc1.1, ← hc.cur] at e
    exact e
  -- the slots
  have hSlot : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s1 (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s1 (wordOf y 24#u64) ∧
      (y ≠ cslotAddr (pc.bv, idx) → L.mem s' y = L.mem s1 y ∧ L.mem s' (wordOf y 8#u64) = L.mem s1 (wordOf y 8#u64)) := by
    intro y hy
    obtain ⟨a0, a8, a16, a24⟩ := hSS1 y hy
    obtain ⟨b16, b24, bx⟩ := hSF y hy
    exact ⟨by rw [b16, a16], by rw [b24, a24], fun hne => ⟨by rw [(bx hne).1, a0], by rw [(bx hne).2, a8]⟩⟩
  -- FL4's writes after the restart
  have hW : P1.WritesIn st s1 s' (fun b => VsXW Z (L.ksb s1) (cslotAddr (pc.bv, idx)) b ∨ PtW {q} b) := by
    refine ⟨hks'.trans hkc1.1.symm, hW0.2.1.trans hkc1.2.symm, fun b hb hn => ?_⟩
    have hslw : ∀ y, IsSlot Z.th y → ∀ k : U64, Off k → b = wordOf y k → L.mem s' b = L.mem s1 b := by
      intro y hy k hk e
      subst e
      obtain ⟨h16, h24, hne⟩ := hSlot y hy
      rcases hk with rfl | rfl | rfl | rfl
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inl (Or.inr (Or.inl (by rw [wordOf_zero, ex]))))).elim
        · rw [wordOf_zero]; exact (hne ex).1
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inl (Or.inr (Or.inr (by rw [ex]))))).elim
        · exact (hne ex).2
      · exact h16
      · exact h24
    by_cases hb0 : VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s b ∨ PtW {q} b
    · rcases hb0 with (⟨y, hy, e | e⟩ | ⟨y, k, hy, hk, e⟩ | hpt | hvw | ⟨t, ht, e⟩ | e) | hqw
      · exact hslw y hy 0#u64 (Or.inl rfl) (by rw [wordOf_zero]; exact e)
      · exact hslw y hy 8#u64 (Or.inr (Or.inl rfl)) e
      · exact hslw y hy k hk e
      · exact (hn (Or.inl (Or.inl (Or.inl hpt)))).elim
      · exact (hn (Or.inl (Or.inl (Or.inr (by rw [hkc1.1]; exact hvw))))).elim
      · subst e; exact pinS t ht
      · subst e; exact pinA
      · exact (hn (Or.inr hqw)).elim
    · have e0 : L.mem s' b = L.mem s b := hW0.2.2 b hb hb0
      have e1 : L.mem s1 b = L.mem s b := hF2 b hb (fun e => hb0 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ct, htcb, UScalar.eq_of_val_eq e⟩))))))) (fun e => hb0 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (UScalar.eq_of_val_eq e))))))))
      rw [e0, e1]
  -- the invoked slot's cap
  have hcv0 : capV (L.mem s) (cslotAddr (pc.bv, idx)) = c := capV_of_capAt hc0
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr (pc.bv, idx)) = c := by rw [hSS1.capV hA.isSlot]; exact hcv0
  have hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s1) y := by
    intro y hy hne
    obtain ⟨-, -, h⟩ := hSlot y hy
    unfold capV; rw [(h hne).1, (h hne).2]
  have Ap : VsApart (L := L) Z H Cs s1 := jVsApartHyp arI Z H Cs Ac1 Lst1 D1 s1 ar σ1 rfl J1
  -- the sets after: `q` added to its kind's set (`TabEmptied.split`)
  obtain ⟨W3, W2, W1, hk3, hk2, hk1, hWq, hok⟩ := TabEmptied.split hTE
  have hqW : ∀ q', (q' ∈ W3 ∨ q' ∈ W2 ∨ q' ∈ W1) → q' = q := hWq
  -- `q`'s frame after: no `OObj`, `VObj` or typed-heap word (the entry's, the
  -- kernel base, the SCs and the typed heap kept)
  have hscB : ∀ p y n, σ'.kheap p = some (.schedContext y n) → σ.kheap p = some (.schedContext y n) := by
    intro p y n hp
    have h1 : σ1.kheap p = some (.schedContext y n) :=
      (F.look (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).1 hp
    rw [hσ1, stsAct_kheap] at h1
    by_cases e : p = ct.bv
    · subst e; simp [updK] at h1
    · simpa [updK, e] using h1
  have hfr' : ∀ q', (q' ∈ W3 ∨ q' ∈ W2 ∨ q' ∈ W1) → ∀ b : U64, q'.val ≤ b.val → b.val < q'.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s') b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k) := by
    intro q' hq' b g1 g2
    obtain rfl := hqW q' hq'
    obtain ⟨n1, n2, n3⟩ := hfr b g1 g2
    refine ⟨fun hO => n1 (Vs.OObj.back hks' hscB hO), by rw [hks']; exact n2, n3⟩
  have hX'' : XTopAt (L := L) AR (Z.mv Z.G (Z.P, Z.L4, Z.L3 ∪ W3, Z.L2 ∪ W2, Z.L1 ∪ W1)) s' a' σ' :=
    hX'.addTab hk3 hk2 hk1 (fun q' h => by rw [hqW q' h]; exact hqa)
      (fun q' h i hi => by rw [hqW q' h]; exact hz i hi) hfr'
  -- the off-set frame: a spec arch object at `σ1`
  have hXa : TabsArch {q} σ1 := by
    intro q' hq'
    rw [Set.mem_singleton_iff.1 hq']
    obtain ⟨ao, hao, hb⟩ := hTy
    have hne : q.bv ≠ ct.bv := fun e => by rw [e, hk] at hao; cases hao
    refine ⟨hqa, ao, ?_, hb⟩
    rw [hσ1, stsAct_kheap]; simp [updK, hne, hao]
  -- the VSpace caps placed at the sets after: the invoked slot's new cap from
  -- its old one, placed there (`TabEmptied.split`), the other slots kept
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 (Z.L3 ∪ W3) (Z.L2 ∪ W2) (Z.L1 ∪ W1) (L.mem s') := by
    intro y hy
    by_cases e : y = cslotAddr (pc.bv, idx)
    · rw [e]
      have hok' : VCapOK Z.P Z.L4 (Z.L3 ∪ W3) (Z.L2 ∪ W2) (Z.L1 ∪ W1) c := by
        have := J.vsc _ hA.isSlot
        rw [hcv0] at this
        exact hok _ _ _ _ _ this
      exact (hLk.2 _ _ _ _ _ hok').toW
    · rw [hcap y hy e]
      exact VCapW.mono (subset_refl _) (subset_refl _) Set.subset_union_left Set.subset_union_left
        Set.subset_union_left (J1.vsc y hy)
  have Ap : VsApart (L := L) Z H Cs s1 := jVsApartHyp arI Z H Cs Ac1 Lst1 D1 s1 ar σ1 rfl J1
  have J' := J1.vsStepJX Ap hpc hidx hXa hX'' F hW hcap (by rw [hcv1]; exact hLk.1.1) (by rw [hcv1]; exact hLk.1.2.1)
    (by rw [hcv1]; exact hnu) (by rw [hcv1]; exact hLk.1.2.2.2)
    (fun y hy => ⟨(hSlot y hy).1, (hSlot y hy).2.1⟩) hvc
  exact ⟨_, H, Cs, Ac1, Lst1, D1, J'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A table frame apart from the sets' objects** at `Z`: 4 KiB-aligned, and
no word of it an `OObj` word, a `VObj` word or inside a typed-heap object
(`JAtZ.vsPostOffJ`'s `hqa`/`hfr`). -/
def OffFrame (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) (q : U64) : Prop :=
  q.val % 4096 = 0 ∧ ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 →
    ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
    ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k)

/-- **A mapped table cap whose table is in no set: what its decode reads**
(XTopJointEntry's `JEntryAt.vsTyp`): the spec's table of the cap's kind at
`q` (l4v `valid_cap`'s `typ_at`) and `q`'s frame apart from the sets'
objects (`OffFrame`; l4v `pspace_distinct`). Nothing for other caps. -/
def OffTabOK (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : capability.Cap → Prop
  | .PageTable q true _ _ => q ∉ Z.L1 →
      (∃ f, σ.kheap q.bv = some (.archObj (.pageTable f))) ∧ OffFrame (L := L) Z s σ q
  | .PageDirectory q true _ _ => q ∉ Z.L2 →
      (∃ f, σ.kheap q.bv = some (.archObj (.pageDirectory f))) ∧ OffFrame (L := L) Z s σ q
  | .Pdpt q true _ _ => q ∉ Z.L3 →
      (∃ f, σ.kheap q.bv = some (.archObj (.pdPointerTable f))) ∧ OffFrame (L := L) Z s σ q
  | _ => True

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A mapped page table cap whose table is in no set, at `JAt`**
(VsOffDec's `decode_invocation_page_table_offX`, then `JAtZ.vsPostOffJ`);
`q`'s facts as XTopJointEntry's `JEntryAt.vsTyp` gives them. -/
theorem decode_invocation_page_tableJO (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr true asid0 va0))
    (hok : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageTable ptr true asid0 va0))
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageTable f))) (hqa : ptr.val % 4096 = 0)
    (hfr : ∀ b : U64, ptr.val ≤ b.val → b.val < ptr.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr true asid0 va0)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hTy' : ∃ ao, σ.kheap ptr.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12 := by
    obtain ⟨f, hf⟩ := hTy
    exact ⟨_, hf, by first | rfl | decide | simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]⟩
  exact XCap.imp arI (decode_invocation_page_table_offX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap hok.2.2.1 hok.2.2.2 hTy hqa hfr extra excaps hex.hext
    blk call don fp ci buffer hX.esa hIA.dom) fun _ _ _ h => J.vsPostOffJ hni hct hqa hTy' hfr h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **A mapped page table cap whose table is in no set, at `JAt`**
(VsOffDec's `decode_invocation_page_directory_offX`, then `JAtZ.vsPostOffJ`);
`q`'s facts as XTopJointEntry's `JEntryAt.vsTyp` gives them. -/
theorem decode_invocation_page_directoryJO (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr true asid0 va0))
    (hok : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.PageDirectory ptr true asid0 va0))
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageDirectory f))) (hqa : ptr.val % 4096 = 0)
    (hfr : ∀ b : U64, ptr.val ≤ b.val → b.val < ptr.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr true asid0 va0)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hTy' : ∃ ao, σ.kheap ptr.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12 := by
    obtain ⟨f, hf⟩ := hTy
    exact ⟨_, hf, by first | rfl | decide | simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]⟩
  exact XCap.imp arI (decode_invocation_page_directory_offX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap hok.2.2.1 hok.2.2.2 hTy hqa hfr extra excaps hex.hext
    blk call don fp ci buffer hX.esa hIA.dom) fun _ _ _ h => J.vsPostOffJ hni hct hqa hTy' hfr h.1 h.2

set_option maxHeartbeats 4000000 in
/-- **A mapped PDPT cap whose table is in no set, at `JAt`**
(VsOffDec's `decode_invocation_pdpt_offX`, then `JAtZ.vsPostOffJ`);
`q`'s facts as XTopJointEntry's `JEntryAt.vsTyp` gives them. -/
theorem decode_invocation_pdptJO (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧
        Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr true asid0 va0))
    (hok : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (.Pdpt ptr true asid0 va0))
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pdPointerTable f))) (hqa : ptr.val % 4096 = 0)
    (hfr : ∀ b : U64, ptr.val ≤ b.val → b.val < ptr.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr true asid0 va0)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hTy' : ∃ ao, σ.kheap ptr.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12 := by
    obtain ⟨f, hf⟩ := hTy
    exact ⟨_, hf, by first | rfl | decide | simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]⟩
  exact XCap.imp arI (decode_invocation_pdpt_offX arI Z.th s ar σ Z.G hCR hFI hMO hDR hA hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 lbl slbl hlM hlU hlO length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap hok.2.2.1 hok.2.2.2 hTy hqa hfr extra excaps hex.hext
    blk call don fp ci buffer hX.esa hIA.dom) fun _ _ _ h => J.vsPostOffJ hni hct hqa hTy' hfr h.1 h.2

end

end

end Fl4Proofs.P3
