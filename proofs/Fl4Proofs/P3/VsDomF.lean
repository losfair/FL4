/-
P3 (DESIGN.md §9), VSpace: **the VSpace caps' domain-schedule frame**
(`DomFrame`, for `DecOKM.withDom`).

* `dom_not_foot`: at `TopSR`, the five domain-schedule words
  (`ksW (ksb) o`, `o ∈ domOffs`, in the kernel-global area) are outside
  `VsFootW`: the slot, table and ASID words are `VObj` words, apart from the
  kernel-global area (`TopPlaced.disj`); the TCB state words by
  `TopPlaced.tko`; the scheduler-action word is in the core's node.
* `dom_of_foot`: an outcome that keeps the state or writes in `VsFootW`
  keeps `ksb` and the five words.
* `dk_spec_arch`: the spec side, for an arch cap: the decoded invocation is
  an arch one, and `set_thread_state Restart` and `fl4ArchPerformInvocation`
  keep `domain_list` and `domain_start_index` (VsDomOps).
-/
import Fl4Proofs.P3.VsTopCap
import Fl4Proofs.P3.VsFootW
import Fl4Proofs.P3.VsDomOps
import Fl4Proofs.P3.TopF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs

noncomputable section

theorem domOffs_lt' {o : U64} (ho : o ∈ domOffs) : o.val < 256 ∧ o.val % 8 = 0 := by
  simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A word of a slot of the typed heap is a `VObj` word. -/
theorem vobj_slot {th : TypedHeap} (hPl : Placed th) (P L4 L3 L2 L1 : Set U64) (ksb : U64) {x : U64}
    (hx : IsSlot th x) {k : U64} (hk : k.val < 32) : VObj th P L4 L3 L2 L1 ksb (wordOf x k) := by
  obtain ⟨p, i, hi, rfl⟩ := hx
  have hv := hi.val hPl
  obtain ⟨k', hk', hs⟩ := hi.size
  have hf := hPl.fits p k' hk'
  have hw : (wordOf (slotOf p i) k).val = p.val + 32 * i + k.val := by
    rw [wordOf_val (by rw [hv]; omega), hv]
  rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
  · refine Or.inl ⟨p, r, hp, by rw [hw]; omega, ?_⟩
    rw [hw]
    generalize 2 ^ r = N at hir
    omega
  · refine Or.inr (Or.inl ⟨p, hp, by rw [hw]; omega, ?_⟩)
    rw [hw]; simp [tcbSlots] at hit; omega

variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
  {A : Type} {AR : A → Fl4Spec.Cr3 → Prop}

/-- **The domain-schedule words are outside the VSpace footprint.** -/
theorem dom_not_foot {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {o : U64} (ho : o ∈ domOffs) :
    ¬ VsFootW st th P L4 L3 L2 L1 s (ksW (L.ksb s) o) := by
  obtain ⟨ho1, -⟩ := domOffs_lt' ho
  have hfit := hS.2.vs.ksb_fit
  have hb : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by omega)
  have hO : OObj st N T C E R B c s σ (ksW (L.ksb s) o) := Or.inr (Or.inl ⟨by omega, by omega⟩)
  have hnv := hS.2.disj _ hO
  rintro (⟨x, hx, e | e⟩ | ⟨x, k, hx, hk, e⟩ | ⟨p, hp, i, hi, e⟩ | hv | ⟨t, ht, e⟩ | e)
  · apply hnv; rw [e, ← wordOf_zero x]; exact vobj_slot hS.2.pl P L4 L3 L2 L1 _ hx (by decide)
  · apply hnv; rw [e]; exact vobj_slot hS.2.pl P L4 L3 L2 L1 _ hx (k := 8#u64) (by decide)
  · apply hnv; rw [e]; exact vobj_slot hS.2.pl P L4 L3 L2 L1 _ hx hk.lt.1
  · apply hnv; rw [e]
    have hv := peA_val (tbl_fit (hS.2.pt p hp)) hi
    exact Or.inr (Or.inr (Or.inl ⟨p, Or.inr hp, by rw [hv]; omega, by rw [hv]; omega⟩))
  · apply hnv
    rcases hv with ⟨hi, hhi, e⟩ | ⟨p, hp, lo, hlo, e⟩
    · rw [e]; have hv := atA_val hS.2.vs.ksb_fit hhi
      exact Or.inr (Or.inr (Or.inr ⟨by rw [hv]; omega, by rw [hv]; omega⟩))
    · rw [e]; have hv := peA_val (hS.2.vs.pal p hp).2 hlo
      exact Or.inr (Or.inr (Or.inl ⟨p, Or.inl hp, by rw [hv]; omega, by rw [hv]; omega⟩))
  · have hf := hS.2.pl.fits t _ ht
    have hsv : (stA t).val = t.val + 3328 := by
      rw [stA_eq]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      simp [objSize] at hf; omega
    have := congrArg UScalar.val e
    rw [hb, hsv] at this
    rcases hS.2.tko t ht with h | h <;> omega
  · obtain ⟨Q, R', hc, -⟩ := hS.1.1.lists
    have hoff : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
    have hsa := P1.nodeAt_val (hc.cur ▸ hc.node) hoff
    have := congrArg UScalar.val e
    rw [hb, hsa] at this
    simp only [P1.LawfulStore.nodeBase] at this
    omega

/-- **An outcome keeping the state or writing in the footprint keeps the
domain-schedule words.** -/
theorem dom_of_foot {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (h : s' = s ∨ P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) :
    L.ksb s' = L.ksb s ∧ ∀ o ∈ domOffs, L.mem s' (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := by
  rcases h with rfl | hw
  · exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hw.1, fun o ho => hw.2.2 _ ?_ (dom_not_foot hS ho)⟩
    have := hS.2.vs.ksb_fit
    exact ksW_al (by omega) hS.2.vs.ksb_al (domOffs_lt' ho).1 (domOffs_lt' ho).2

end

/-- The outcome of a `liftME` is one of the inner decode's. -/
theorem decOut_liftME_inv {α β : Type} {f : α → β} {m : Fl4Spec.SEMonad Unit α} {σ : Fl4Spec.State Unit}
    {inv : β} (h : DecOut (Fl4Spec.NonDetE.liftME f m) σ inv) : ∃ i, inv = f i := by
  unfold DecOut Fl4Spec.NonDetE.liftME at h
  rw [ExceptT.run_bind] at h
  obtain ⟨⟨⟨r, σ'⟩, -, hm⟩, -⟩ := h
  cases r with
  | error e => exact absurd (Set.mem_singleton_iff.1 hm) (by simp)
  | ok i =>
    refine ⟨i, ?_⟩
    have := Set.mem_singleton_iff.1 hm
    simp only [Prod.mk.injEq, Except.ok.injEq] at this
    exact this.1

/-- **The spec side of an arch cap's `DomFrame`.** -/
theorem dk_spec_arch {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {cap : capability.Cap} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {blk call don : Bool} {σ : Fl4Spec.State Unit} {tcb : Fl4Spec.Tcb}
    (hac : ∃ ac, absCap cap = .archObjectCap ac) (hkt : σ.kheap σ.curThread = some (.tcb tcb)) :
    ∀ inv σ1, DecOut (specDec fp slbl args ci sl cap excaps buffer) σ inv →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1,
        y.2.domainList = σ.domainList ∧ y.2.domainStartIndex = σ.domainStartIndex := by
  intro inv σ1 hd he y hy
  obtain ⟨ac, hac⟩ := hac
  have e : specDec fp slbl args ci sl cap excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl args ci sl ac excaps) := by
    unfold specDec Fl4Spec.fl4DecodeInvocation; rw [hac]
  rw [e] at hd
  obtain ⟨i, rfl⟩ := decOut_liftME_inv hd
  have h1 := setThreadState_dom hkt he
  have h2 := Vs.DK.dom (dke_fl4ArchPerformInvocation i) hy
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of `decode_invocation_page_table_cap`** (`dom_of_foot`, `dk_spec_arch`). -/
theorem domFrame_page_table (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DomFrame (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20 := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4, fun p' a' e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (hxs x h1) h2 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨hv1, -, hv3⟩ := hv
      exact ⟨hv1, (hv3 rfl).1, (hv3 rfl).2⟩
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  refine ⟨?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  have h := decode_invocation_page_table arI th hS.2.pl s ar σ G hCR hFI hMO (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s)) (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2) (VsPtMapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsPtMapHyps_top hA)) (VsPtUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsPtUnmapHyps_top hA)) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hok.1 hok.2.1 hok.2.2 extra excaps hext' blk call don fp ci buffer
  exact WP.spec_mono h fun res hr => dom_of_foot hS hr.2

set_option maxHeartbeats 8000000 in
/-- **`decode_invocation_page_table_cap` with the domain schedule** (`DecOKDM`, `DecOKM.withDom`). -/
theorem decode_invocation_page_table_capD (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DecOKDM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKM.withDom arI hDR (decode_invocation_page_table_cap arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (extra := extra) (excaps := excaps) (hext := hext) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hxs := hxs))
    (domFrame_page_table arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (extra := extra) (excaps := excaps) (hext := hext) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hxs := hxs))

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of `decode_invocation_page_directory_cap`** (`dom_of_foot`, `dk_spec_arch`). -/
theorem domFrame_page_directory (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DomFrame (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20 := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4, fun p' a' e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (hxs x h1) h2 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨hv1, -, hv3⟩ := hv
      exact ⟨hv1, (hv3 rfl).1, (hv3 rfl).2⟩
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  refine ⟨?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  have h := decode_invocation_page_directory arI th hS.2.pl s ar σ G hCR hFI hMO (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s)) (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2) (VsPdMapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsPdMapHyps_top hA)) (VsPdUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsPdUnmapHyps_top hA)) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hok.1 hok.2.1 hok.2.2 extra excaps hext' blk call don fp ci buffer
  exact WP.spec_mono h fun res hr => dom_of_foot hS hr.2

set_option maxHeartbeats 8000000 in
/-- **`decode_invocation_page_directory_cap` with the domain schedule** (`DecOKDM`, `DecOKM.withDom`). -/
theorem decode_invocation_page_directory_capD (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DecOKDM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKM.withDom arI hDR (decode_invocation_page_directory_cap arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (extra := extra) (excaps := excaps) (hext := hext) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hxs := hxs))
    (domFrame_page_directory arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (extra := extra) (excaps := excaps) (hext := hext) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hxs := hxs))

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of `decode_invocation_pdpt_cap`** (`dom_of_foot`, `dk_spec_arch`). -/
theorem domFrame_pdpt (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DomFrame (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20 := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4, fun p' a' e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (hxs x h1) h2 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨hv1, -, hv3⟩ := hv
      exact ⟨hv1, (hv3 rfl).1, (hv3 rfl).2⟩
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  refine ⟨?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  have h := decode_invocation_pdpt arI th hS.2.pl s ar σ G hCR hFI hMO (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s)) (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2) (VsPdptMapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsPdptMapHyps_top hA)) (VsPdptUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsPdptUnmapHyps_top hA)) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hok.1 hok.2.1 hok.2.2 extra excaps hext' blk call don fp ci buffer
  exact WP.spec_mono h fun res hr => dom_of_foot hS hr.2

set_option maxHeartbeats 8000000 in
/-- **`decode_invocation_pdpt_cap` with the domain schedule** (`DecOKDM`, `DecOKM.withDom`). -/
theorem decode_invocation_pdpt_capD (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)  :
    DecOKDM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKM.withDom arI hDR (decode_invocation_pdpt_cap arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (extra := extra) (excaps := excaps) (hext := hext) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hxs := hxs))
    (domFrame_pdpt arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hA := hA) (hS := hS) (hPI := hPI) (hR := hR) (hPt := hPt) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlM := hlM) (hlU := hlU) (hlO := hlO) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (args := args) (hlen := hlen) (hargs := hargs) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hcap := hcap) (extra := extra) (excaps := excaps) (hext := hext) (blk := blk) (call := call) (don := don) (fp := fp) (ci := ci) (buffer := buffer) (hxs := hxs))

set_option maxHeartbeats 8000000 in
/-- **The domain-schedule frame of `decode_invocation_asid_pool_cap`** (`dom_of_foot`, `dk_spec_arch`). -/
theorem domFrame_asid_pool (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (ptr base : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hsl : IsSlot th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))  :
    DomFrame (L := L) arI s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest ∧
        ∀ p1 a1, vc = .Pml4 p1 false a1 → p1 ≠ 0#u64 := by
    rcases hext with h | ⟨pc, r, idx, vc, vc', rest, h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨pc, r, idx, vc, vc', rest, h1, h2, h3, h4, h5, h6, fun p1 a1 e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (AbsSlot.isSlot (th := th) (sl := (pc.bv, idx))
        ⟨pc, rfl, Or.inl (by simpa [h2] using h1)⟩) h4 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨-, hv2, -⟩ := hv
      exact hv2
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  refine ⟨?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  have h := decode_invocation_asid_pool arI th hS.2.pl s ar σ G hCR hFI hMO (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s)) (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2) (VsInvHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (fun _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) (vsInvHyps_top curT_top)) ⟨hS, P1.WritesIn.refl _ _⟩ hS.2.vs hS.2.sd hR hS.2.vo
    lbl slbl hlA length buf ct hct hcur htcb hact hrun ptr base hok.2.1 hok.2.2 extra excaps hNative hext' slot blk call don fp args ci sl
    buffer
  exact WP.spec_mono h fun res hr => dom_of_foot hS hr.2

set_option maxHeartbeats 8000000 in
/-- **`decode_invocation_asid_pool_cap` with the domain schedule** (`DecOKDM`, `DecOKM.withDom`). -/
theorem decode_invocation_asid_pool_capD (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (ptr base : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hsl : IsSlot th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))  :
    DecOKDM (L := L) arI s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps
      buffer :=
  DecOKM.withDom arI hDR (decode_invocation_asid_pool_cap arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hS := hS) (hR := hR) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlA := hlA) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (ptr := ptr) (base := base) (extra := extra) (excaps := excaps) (hNative := hNative) (hext := hext) (slot := slot) (blk := blk) (call := call) (don := don) (fp := fp) (args := args) (ci := ci) (sl := sl) (buffer := buffer) (hsl := hsl) (hcap := hcap))
    (domFrame_asid_pool arI (th := th) (s := s) (ar := ar) (σ := σ) (G := G) (hCR := hCR) (hFI := hFI) (hMO := hMO) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR) (hS := hS) (hR := hR) (hVC := hVC) (lbl := lbl) (slbl := slbl) (hlA := hlA) (length := length) (buf := buf) (ct := ct) (hct := hct) (hcur := hcur) (htcb := htcb) (hact := hact) (hrun := hrun) (ptr := ptr) (base := base) (extra := extra) (excaps := excaps) (hNative := hNative) (hext := hext) (slot := slot) (blk := blk) (call := call) (don := don) (fp := fp) (args := args) (ci := ci) (sl := sl) (buffer := buffer) (hsl := hsl) (hcap := hcap))

set_option maxHeartbeats 8000000 in
/-- **A frame cap, every label, with the domain schedule** (`DecOKDM`, or `DecOKR` for `GetAddress` and `TestAndClearAccessed`). -/
theorem decode_invocation_frame_capD [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (hno : sz = .Large → d = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (hxs : ∀ x, vspace.extra extra 0#usize = ok (some x) → IsSlot th x)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hga : GetAddrHyp (L := L) s σ ar ct p call) (htac : TacHyp (L := L) L4 L3 L2 L1 s σ ct call)  :
    DecOKDM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ∨
    DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (th := th) (sl := (pc.bv, idx)) ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hok := hVC.at hCR.2.2.1 hsl hcap (by simp)
  simp only [VCapOK] at hok
  have hext' : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20 := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4, fun p' a' e => ?_⟩
      have hv := hVC.at hCR.2.2.1 (hxs x h1) h2 (by rw [e]; simp)
      rw [e] at hv
      obtain ⟨hv1, -, hv3⟩ := hv
      exact ⟨hv1, (hv3 rfl).1, (hv3 rfl).2⟩
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  by_cases hlga : lbl = fl4_abi.label.X86PageGetAddress
  · right
    have := decode_invocation_frame_getaddr (L := L) arI s ar σ lbl slbl hlbl hlga length buf ct hct hcur hkt0
      (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d) (m := m)
      (cslotAddr (pc.bv, idx)) blk call don fp hga extra (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer
    exact this
  by_cases hltac : lbl = fl4_abi.label.X86PageTestAndClearAccessed
  · right
    have := decode_invocation_frame_tac (L := L) arI s ar σ hR hPt hS.2.pt hPI lbl slbl hlbl hltac length buf ct hct
      hcur hkt0 (p := p) (sz := sz) (rt := rt) (asid := asid) (va := va) (d := d) (m := m)
      (cslotAddr (pc.bv, idx)) blk call don fp htac extra (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer
    exact this
  left
  have hextS : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ y nc nc' nsl rest, vspace.extra extra 0#usize = ok (some y) ∧ capAt (L.mem s) y = ok nc ∧
        CapRel nc nc' ∧ CapValid th nc ∧ excaps = (nc', nsl) :: rest := by
    rcases hext with h | ⟨x, vc, vc', xsl, rest, h1, h2, h3, h4⟩
    · exact Or.inl h
    · have hv := Vs.capValid_slot hCR.2.1 (hxs x h1)
      rw [capAt_capV] at h2; cases eq_of_ok_eq h2
      exact Or.inr ⟨x, _, vc', xsl, rest, h1, capAt_capV _ _, h3, hv, h4⟩
  have hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKMQ (L := L) arI (fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) s ar σ lbl length (cslotAddr (pc.bv, idx))
        (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
        buffer := fun hl => by
    have := decode_invocation_frame_ds (L := L) arI th hS.2.pl s ar σ G hCR hFI hU
      (SR := FootSRc st th (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s))
      (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2.1)
      (VsSubHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl
        (Vs.vsSubHyps_top (st := st) (L := L) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1)
          (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) (AR := AR)))
      ⟨hS, P1.WritesIn.refl _ _, fun t ht => by
        have e := P1.eq_of_bv (ht.trans hcur); subst e; exact htcb, hact⟩
      hS.2.pt hS.2.vs hS.2.vo hS.2.po hR hPt lbl slbl hlbl hl length buf ct hct hcur htcb hact hkt (hrun _ hkt)
      args hlen hargs (pc := pc) (r := r) (idx := idx) hpc hidx (p := p) (sz := sz) (rt := rt) (asid := asid)
      (va := va) (d := d) (m := m) hcap hno hMO hVC extra excaps hextS blk call don fp ci buffer
    exact this
  have h := decode_invocation_frame arI th hS.2.pl s ar σ G hCR hFI hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (VsFootW st th P L4 L3 L2 L1 s))
    (Q := fun s' => P1.WritesIn st s s' (VsFootW st th P L4 L3 L2 L1 s)) (fun _ _ _ h => h.2)
    (VsFrameHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsFrameHyps_top hA))
    (VsFrameHypsL.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsFrameHypsL_top hA))
    (VsFrameUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hS.2.pl (vsFrameUnmapHyps_top hA)) ⟨hS, P1.WritesIn.refl _ _⟩
    hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlbl length buf ct hct hcur htcb hact hrun
    args hlen hargs hpc hidx hcap hok.1 (fun e => by subst e; exact hok.2) (fun e => by subst e; exact hok.2)
    (fun e => by subst e; exact hok.2) hAl extra excaps hext' blk call don fp ci buffer
    (fun h => absurd h hlga) (fun h => absurd h hltac) hDS
  rcases h with ⟨-, -, h⟩ | ⟨e, -⟩
  · exact DecOKM.withDom arI hDR (DecOKMQ.toM arI h)
      ⟨WP.spec_mono h fun res hr => dom_of_foot hS hr.2, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  · exact absurd e (by rintro (e | e) <;> contradiction)

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap with the domain schedule** (`DecOKDM`; the pool page apart from the kernel-global area, from the untyped placement `UtKsOut`). -/
theorem decode_invocation_asid_control_capD (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKTop (L := L) N T C E R B c s σ p)
    (hUK : Vs.UtKsOut (L.ksb s) (L.mem s) G)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKDM (L := L) arI s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excaps buffer := by
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hext0 := hext
  have hextK : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKF (RegOKTop (L := L) N T C E R B c) (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568)) s σ p := by
    rcases hext with h | ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hRg⟩
    · exact Or.inl h
    · exact Or.inr ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
        fun p fi e hc => ⟨(hRg p fi e hc).1, (hRg p fi e hc).2, fun b hb1 hb2 => Or.inr (by
          have hk := hUK.pool hCR.2.2.1 (AbsSlot.isSlot (th := th) (sl := (pp.bv, idx))
            ⟨pp, rfl, Or.inl (by simpa [h2] using h1)⟩) (by rw [h5, e])
          rcases hk with h | h <;> omega)⟩⟩
  have hF := Vs.decode_invocation_asid_control_top arI th s ar σ G hCR hFI hU hMO hS hR hPt lbl slbl hlM length buf ct
    hct hcur htcb hact hrun args hlen hargs extra excaps hext0 slot blk call don fp ci sl buffer
  have h := decode_invocation_asid_control arI th hS.2.pl s ar σ G hCR hFI hU hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568)))
    (Q := fun s' => P1.WritesIn st s s' (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568))) (fun _ _ _ h => h.2)
    (VsMpHyps.foot (s0 := s) (fun _ h => Or.inl h.toW) hS.2.pl (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))) vsMpHyps_top) ⟨hS, P1.WritesIn.refl _ _⟩ hR hPt hS.2.vs hS.2.pt
    hS.2.vo hS.2.po hS.2.pv lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hextK slot
    blk call don fp ci sl buffer
  refine DecOKM.withDom arI hDR hF ⟨WP.spec_mono h fun res hr => ?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  rcases hr.2 with e | hw
  · rw [e]; exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hw.1, fun o ho => hw.2.2 _ ?_ ?_⟩
    · have := hS.2.vs.ksb_fit
      exact ksW_al (by omega) hS.2.vs.ksb_al (domOffs_lt' ho).1 (domOffs_lt' ho).2
    · rintro (h | h)
      · exact dom_not_foot hS ho h
      · apply h
        have := hS.2.vs.ksb_fit
        have hb : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by have := (domOffs_lt' ho).1; omega)
        have := (domOffs_lt' ho).1
        rw [hb]; omega

set_option maxHeartbeats 8000000 in
/-- **A PML4 cap with the domain schedule** (`DecOKDM`; FL4 writes the TCB state
and scheduler-action words only). -/
theorem decode_invocation_pml4D (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hinv : ∀ (a : A) (asid : U64), ∃ a', arI.invalidate_asid a asid = ok a')
    (p asid : U64) (mp : Bool) (length slot buf : U64) (blk call don fp : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    DecOKDM (L := L) arI s ar σ lbl length slot (.Pml4 p mp asid) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  refine DecOKM.withDom arI hDR (decode_invocation_pml4 arI th hP s ar σ G hCR hFI hMO lbl slbl hlbl ct hct hcur htcb
    hact hinv p asid mp length slot buf blk call don fp extra args ci sl excaps buffer) ⟨?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  by_cases hl : lbl = fl4_abi.label.X86PML4Flush
  swap
  · rw [if_neg hl]
    simp only [error.illegal, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => trivial⟩
  rw [if_pos hl]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => trivial⟩
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (set_thread_state_frame s ct sched.TS_RESTART (Vs.stA_al hP htcb) hact.1)
    (set_thread_state_cpu s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨hF, hk, hc⟩
  obtain ⟨a', ha'⟩ := hinv ar asid
  rw [ha']; simp only [bind_ok, WP.spec_ok]
  refine dom_of_foot hS (Or.inr ⟨hk, hc, fun b hb hn => hF b hb (fun e => hn ?_) (fun e => hn ?_)⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ct, htcb, UScalar.eq_of_val_eq e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq e)))))


end

end

end Fl4Proofs.P3
