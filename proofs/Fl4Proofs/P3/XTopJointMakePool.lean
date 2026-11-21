/-
P3 (DESIGN.md §9), VSpace: **the ASID control cap's `MakePool` at `J`
when the region is clean** (XTopJointVsCap's `MpClean`, `MpSpecClean`;
the former `JAsidCPath.post` [W], removed).

The step from the restart's state `s1` (`JAtZ.restartJ`) to the outcome:
FL4 writes slot words (the untyped cap's free index, the pool cap's
insertion), zeroes the pool's frame `[p, p + 4096)` and writes one
ASID-table word (`MpW`); the spec's step is `MpFr` (two CNodes change, the
empty cell `p` gets the pool), the CDT and the original bits change at the
destination (VsMakePoolRel's `MpMid`; `MpFr` once the region holds no spec
object, `MpSpecClean`). `JAtZ` after at the sets with the
grown pool set and the new MDB ghost, P1's heap `H` grown by the pool's
page as an `other` object (`JAtZ.mpAddOK`, `JAtZ.mpBlk`):

* The written words split into slot words, the region (no object of `th`
  or `H` in it, `JAtZ.mpEmpty`) and the ASID-table word, which lies in no
  object of `H` but the `other` ones (`JAtZ.vsObjW`: the table's placement,
  `TopPlaced`) and in no RAM untyped region (`UtKsApart`'s third clause):
  so no premise is needed for it. Every word an object of `H` holds outside
  the slots is kept (`mp_keep`, `mp_keeps`).
* `JAtZ.mpBlkAfter`: P1's `BlkOK` at `H` grown by the page (slot words
  `CapW`, the region the new `other` object's `Ω` words, the table word
  untracked). `JPlaced`, `JKern`, `JCovD`, `SpecCover` with the page
  (`*.addP`; the pool cap covers it).
* `JAtZ.mp_utc`, `JAtZ.mp_sfree`: the untyped caps' facts and `SpecFree`
  after (the source full; the new pool inside it, off every other RAM
  untyped cap's free part by `UtInv.drange`/`inc`).
* `JAtZ.mpStepJ`: `JAtZ` after at `Z.mp G' p`, `hAddP H p`, from the
  restart's `JAtZ` (`JAtZ.add_frame`).
* `decode_invocation_asid_controlJC`: the cap at `JAt` when `MpClean` and
  `MpSpecClean` hold (VsDecFrame's `decode_invocation_asid_controlXG`);
  `decode_invocation_asid_controlJM`: XTopJointEntry's dispatch, the dirty
  case asked (`JAsidCPath.dirty` [W]).
-/
import Fl4Proofs.P3.XTopJointMakePoolSpec
import Fl4Proofs.P3.XTopJointVsCap
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P3.XTopJointUtEp
import Fl4Proofs.P3.XTopJointVsSub
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A word off the slots, the pool's frame and the ASID-table word is kept
by `MakePool`.** -/
theorem mp_keep {th : TypedHeap} (hP : Placed th) {s s' : S} {p kb hi : U64}
    (hw : ∀ b, P1.Aligned b → ¬ MpW th p kb hi b → L.mem s' b = L.mem s b) {b : U64} (hb : P1.Aligned b)
    (hsl : ∀ a, IsSlot th a → b.val < a.val ∨ a.val + 32 ≤ b.val) (hrg : b.val < p.val ∨ p.val + 4096 ≤ b.val)
    (htb : b ≠ atA kb hi) : L.mem s' b = L.mem s b := by
  refine hw b hb fun h => ?_
  rcases h with ⟨x, k, hx, hk, rfl⟩ | h | h
  · have hv := slot_word_val hP hx hk
    have := hk.lt
    rcases hsl x hx with e | e <;> omega
  · omega
  · exact htb h

/-- **The ASID-table word lies in no object of `H` but the `other` ones**
(`JAtZ.vsObjW`). -/
theorem JAtZ.atab_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {hi : U64} (hh : hi.val < 2048) {q : U64} {k : P1.HKind} (hq : H q = some k) (hk : ∀ z, k ≠ .other z) :
    (atA (L.ksb s) hi).val < q.val ∨ q.val + 2 ^ k.bits ≤ (atA (L.ksb s) hi).val :=
  J.vsObjW ⟨J.scOut⟩ (Or.inr (Or.inl ⟨hi, hh, rfl⟩)) hq hk

theorem JAtZ.atab_al {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {hi : U64} (hh : hi.val < 2048) : P1.Aligned (atA (L.ksb s) hi) :=
  J.vsW_al (Or.inr (Or.inl ⟨hi, hh, rfl⟩))

/-- **A slot lies in a TCB or an `other` object of `H`** (`JAtZ.slot_in_H`
with the kinds). -/
theorem JAtZ.slot_in_H' {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : IsSlot Z.th x) :
    ∃ p k, H p = some k ∧ (k = .tcb ∨ ∃ z, k = .other z) ∧ p.val ≤ x.val ∧ x.val + 32 ≤ p.val + 2 ^ k.bits := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨p, i, hi, rfl⟩ := hx
  have hv := hi.val hJ.pl
  rcases hi with ⟨r, hp, hlt⟩ | ⟨hp, hlt⟩
  · refine ⟨p, .other (r + 5), hJ.cnode p r hp, Or.inr ⟨_, rfl⟩, by omega, ?_⟩
    simp only [P1.HKind.bits]
    have : 32 * (i + 1) ≤ 32 * 2 ^ r := by
      have : i + 1 ≤ 2 ^ r := hlt; omega
    rw [pow_add]; omega
  · refine ⟨p, .tcb, (hJ.tcb p).1 hp, Or.inl rfl, by omega, ?_⟩
    simp only [P1.HKind.bits]
    have : i < tcbSlots := hlt
    simp [tcbSlots] at this; omega

/-- **A word of an object of `H` other than a TCB or an `other` object is
kept by `MakePool`** (slots lie in TCBs and CNodes, `JAtZ.slot_in_H`; the
region holds no object of `H`; the table word by `JAtZ.atab_obj`). -/
theorem JAtZ.mp_objK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {p hi : U64} (hh : hi.val < 2048)
    (hw : ∀ b, P1.Aligned b → ¬ MpW Z.th p (L.ksb s) hi b → L.mem s' b = L.mem s b)
    (hHo : ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val)
    {q : U64} {k : P1.HKind} (hq : H q = some k) (hko : ∀ z, k ≠ .other z) (hkt : k ≠ .tcb)
    {w : U64} (hal : P1.Aligned w) (g1 : q.val ≤ w.val) (g2 : w.val < q.val + 2 ^ k.bits) :
    L.mem s' w = L.mem s w := by
  have hP := J.xtop.rel.1
  refine mp_keep hP hw hal (fun x hx => ?_) ?_ ?_
  · obtain ⟨p', k', hp', hk', h1, h2⟩ := J.slot_in_H' hx
    have hne : q ≠ p' := by
      intro e; subst e; rw [hq] at hp'; cases hp'
      rcases hk' with e | ⟨z, e⟩
      · exact hkt e
      · exact hko z e
    have := J.kern.heap.disj q _ p' _ hq hp' hne
    omega
  · have := hHo q k hq; omega
  · intro e
    have := J.atab_obj hh hq hko
    rw [← e] at this; omega

/-- **The scheduler's words `MakePool` keeps**: the TCBs' `MCP`, `YIELD_TO`
and IPC-buffer words (off their slots, `SlotsApart`), the SCs' `REPLY`
words and every SC word below 128, the replies' links (`JAtZ.mp_objK`). -/
theorem JAtZ.mp_keeps {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {p hi : U64} (hh : hi.val < 2048)
    (hw : ∀ b, P1.Aligned b → ¬ MpW Z.th p (L.ksb s) hi b → L.mem s' b = L.mem s b)
    (hHo : ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t)) ∧ (∀ t ∈ Z.T, L.mem s' (P1.yieldA t) = L.mem s (P1.yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧ L.mem s' (P1.rNextA r) = L.mem s (P1.rNextA r)) ∧
    (∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K)) := by
  have hP := J.xtop.rel.1
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hA := J.apart
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have tw : ∀ t ∈ Z.T, ∀ b : U64, P1.Aligned b → t.val + 256 ≤ b.val → b.val < t.val + 4096 →
      L.mem s' b = L.mem s b := by
    intro t ht b hb h1 h2
    have hHt : H t = some .tcb := J.zH.1 t ht
    refine mp_keep hP hw hb (fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega) ?_ ?_
    · have := hHo t _ hHt; simp only [P1.HKind.bits] at this; omega
    · intro e
      have := J.atab_obj hh hHt (fun _ e => by cases e)
      rw [← e] at this; simp only [P1.HKind.bits] at this; omega
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s' w = L.mem s w := fun q z hq w hal g1 g2 =>
    J.mp_objK hh hw hHo hq (fun _ e => by cases e) (fun e => by cases e) hal g1 (by simpa only [P1.HKind.bits] using g2)
  refine ⟨fun t ht => tw t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
    fun t ht => tw t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega),
    fun t ht => tw t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega), fun q hq => ?_, fun r hr => ?_, fun q z hq K hK8 hK => ?_⟩
  · obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word hS hq).1 hin.1 hin.2
  · have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      J.mp_objK hh hw hHo hHr (fun _ e => by cases e) (fun e => by cases e) (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  · obtain ⟨hal, hv, hf⟩ := J.scW_in hq hK8 hK
    exact scw q z hq _ hal (by omega) (by omega)


/-- **`MakePool` keeps every TCB's VCPU word** (KENTRY-PLAN g2b; as
`mp_keeps`'s TCB words). -/
theorem JAtZ.mp_vkeep {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {p hi : U64} (hh : hi.val < 2048)
    (hw : ∀ b, P1.Aligned b → ¬ MpW Z.th p (L.ksb s) hi b → L.mem s' b = L.mem s b)
    (hHo : ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val) :
    VKeep (L := L) Z.th s s' := by
  have hP := J.xtop.rel.1
  have hA := J.apart
  have hT : P1.TcbPlaced Z.T := J.ip.e.tcb
  intro t htt
  have ht := J.thT t htt
  have hv := Sched.tVcpuA_val hT ht
  have hHt : H t = some .tcb := J.zH.1 t ht
  refine mp_keep hP hw (Sched.tVcpuA_aligned hT ht) (fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega) ?_ ?_
  · have := hHo t _ hHt; simp only [P1.HKind.bits] at this; omega
  · intro e
    have := J.atab_obj hh hHt (fun _ e => by cases e)
    rw [← e] at this; simp only [P1.HKind.bits] at this; omega
end


/-! ## `H` grown by the pool's page -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `H` with the pool's page. -/
abbrev hAddP (H : P1.Heap) (p : U64) : P1.Heap := H.add (· = p) (.other 12)

theorem hAddP_ne {H : P1.Heap} {p q : U64} (h : q ≠ p) : hAddP H p q = H q := P1.Heap.add_of_not h

theorem hAddP_self {H : P1.Heap} {p : U64} : hAddP H p p = some (.other 12) := P1.Heap.add_of_mem rfl

theorem hAddP_cases {H : P1.Heap} {p q : U64} {k : P1.HKind} (h : hAddP H p q = some k) :
    (q = p ∧ k = .other 12) ∨ (q ≠ p ∧ H q = some k) := P1.Heap.add_eq_some.1 h

theorem heapOK_addP {H : P1.Heap} {p : U64} {Cs : Set U64} {s : S}
    (A : P1.AddOKP st H (· = p) (.other 12) Cs s) (hH : P1.HeapOK H) : P1.HeapOK (hAddP H p) := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q k hq => ?_, fun q z hq => ?_,
    fun q k q' k' hq hq' hne => ?_⟩
  · rcases hAddP_cases hq with ⟨rfl, rfl⟩ | ⟨-, hq⟩
    · exact A.align _ rfl
    · exact hH.align q k hq
  · rcases hAddP_cases hq with ⟨rfl, rfl⟩ | ⟨-, hq⟩
    · exact A.fits _ rfl
    · exact hH.fits q k hq
  · rcases hAddP_cases hq with ⟨rfl, rfl⟩ | ⟨-, hq⟩
    · show 12 < 64; decide
    · exact hH.lt64 q k hq
  · rcases hAddP_cases hq with ⟨-, e⟩ | ⟨-, hq⟩
    · cases e
    · exact hH.scmin q z hq
  · rcases hAddP_cases hq with ⟨rfl, rfl⟩ | ⟨hn, hq0⟩ <;>
      rcases hAddP_cases hq' with ⟨rfl, rfl⟩ | ⟨hn', hq0'⟩
    · exact absurd rfl hne
    · exact A.disjH _ rfl q' k' hq0'
    · rcases A.disjH _ rfl q k hq0 with e | e
      · exact Or.inr e
      · exact Or.inl e
    · exact hH.disj q k q' k' hq0 hq0' hne

/-- The new object is no TCB, endpoint, notification, reply or SC: the
lookups of those kinds are `H`'s. -/
theorem hAddP_iff {H : P1.Heap} {p q : U64} {k : P1.HKind} (hk : ∀ z, k ≠ .other z) (hp : H p = none) :
    hAddP H p q = some k ↔ H q = some k := by
  constructor
  · intro h
    rcases hAddP_cases h with ⟨-, rfl⟩ | ⟨-, h⟩
    · exact absurd rfl (hk 12)
    · exact h
  · intro h
    have hq : q ≠ p := fun e => by subst e; rw [hp] at h; cases h
    rw [hAddP_ne hq]; exact h

theorem capTyped_addP {H : P1.Heap} {p : U64} (hp : H p = none) {Rp Nt : Set U64} {c : capability.Cap}
    (h : P1.CapTyped H Rp Nt c) : P1.CapTyped (hAddP H p) Rp Nt c :=
  ⟨fun a b x y z w e => (hAddP_iff (fun _ e => by cases e) hp).2 (h.1 a b x y z w e),
    fun a b x y e => ⟨(h.2.1 a b x y e).1, (hAddP_iff (fun _ e => by cases e) hp).2 (h.2.1 a b x y e).2⟩, h.2.2⟩

theorem frApartH_addP {H : P1.Heap} {p : U64} {c : capability.Cap} (h : FrApartH H c) : FrApartH (hAddP H p) c := by
  intro q k hq hk
  rcases hAddP_cases hq with ⟨-, rfl⟩ | ⟨-, hq⟩
  · exact absurd rfl (hk 12)
  · exact h q k hq hk

theorem capObjH_addP {H : P1.Heap} {p : U64} (hp : H p = none) {isc : U64} {c : capability.Cap}
    (h : CapObjH H isc c) : CapObjH (hAddP H p) isc c := by
  cases c with
  | Ept q lv m a va =>
    obtain ⟨⟨n, hn, h1, h2⟩, h3⟩ := h
    have hq : q ≠ p := fun e => by subst e; rw [hp] at hn; cases hn
    exact ⟨⟨n, by rw [hAddP_ne hq]; exact hn, h1, h2⟩, frApartH_addP h3⟩
  | Frame q sz r d m ep a va => exact frApartH_addP h
  | PageTable q m a v => exact frApartH_addP h
  | PageDirectory q m a v => exact frApartH_addP h
  | Pdpt q m a v => exact frApartH_addP h
  | SchedContext q sb => exact ⟨(hAddP_iff (fun _ e => by cases e) hp).2 h.1, h.2⟩
  | _ => trivial

/-- **`JPlaced` with the pool's page in `H`.** -/
theorem Sched.JPlaced.addP {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s : S} {σ : Fl4Spec.State Unit} {p : U64}
    {Cs : Set U64} (h : JPlaced (L := L) th H Tr C s σ) (A : P1.AddOKP st H (· = p) (.other 12) Cs s) :
    JPlaced (L := L) th (hAddP H p) Tr C s σ := by
  have hp : H p = none := A.fresh p rfl
  have hR : P1.Heap.replies (hAddP H p) = P1.Heap.replies H := A.replies_eq (by intro e; cases e)
  have hN : P1.Heap.ntfns (hAddP H p) = P1.Heap.ntfns H := A.ntfns_eq (by intro e; cases e)
  refine ⟨heapOK_addP A h.heap, h.pl, fun t => (h.tcb t).trans (hAddP_iff (fun _ e => by cases e) hp).symm,
    fun q r hq => ?_, h.tr, fun c y n hc hk => ⟨(h.sc c y n hc hk).1,
      (hAddP_iff (fun _ e => by cases e) hp).2 (h.sc c y n hc hk).2⟩, fun q k hq hk => ?_, fun q z hq => ?_,
    fun a ha => by rw [hR, hN]; exact capTyped_addP hp (h.typed a ha),
    fun i hi => by rw [hR, hN]; exact capTyped_addP hp (h.irq i hi), h.fh, h.bfs,
    fun a ha => capObjH_addP hp (h.cobj a ha)⟩
  · have e := h.cnode q r hq
    have hq' : q ≠ p := fun e' => by subst e'; rw [hp] at e; cases e
    rw [hAddP_ne hq']; exact e
  · exact h.ks q k ((hAddP_iff hk hp).1 hq) hk
  · rcases hAddP_cases hq with ⟨rfl, e⟩ | ⟨-, hq⟩
    · cases e
      rcases A.ks _ rfl with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · exact h.ksIn q z hq

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem range_ap (q b : U64) (hfit : q.val + 4096 ≤ 2 ^ 64) :
    baseF (.AsidPool q b) = q.val ∧ topF (.AsidPool q b) = q.val + 4095 := by
  refine ⟨by unfold baseF; rw [ptrF_ap], ?_⟩
  unfold topF
  rw [ptrF_ap, sizeF_ap]
  have hm := maskF_val (b := fl4_abi.consts.bits.ASID_POOL) (by unfold fl4_abi.consts.bits.ASID_POOL; decide)
  have h12 : (fl4_abi.consts.bits.ASID_POOL).val = 12 := by unfold fl4_abi.consts.bits.ASID_POOL; rfl
  rw [h12] at hm
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

/-- **`JKern` with the pool's page in `H`.** -/
theorem JKern.addP {th : TypedHeap} {H : P1.Heap} {Cs D : Set U64} {s : S} {σ : Fl4Spec.State Unit} {p : U64}
    (K : JKern (L := L) H Cs D th s σ) (A : P1.AddOKP st H (· = p) (.other 12) Cs s) :
    JKern (L := L) (hAddP H p) Cs D th s σ := by
  have hp : H p = none := A.fresh p rfl
  refine ⟨K.orig, K.cur, K.curT, K.act, K.dwAl, K.dwObj, K.dwNe, K.head, K.gpm, K.ga, K.gf, heapOK_addP A K.heap,
    by rw [hAddP_ne (Ne.symm (A.nz p rfl))]; exact K.h0, fun q k hq hk => K.hks q k ((hAddP_iff hk hp).1 hq) hk,
    fun q z hq => ?_, fun q k hq c hc => ?_, K.ksbFit, K.ksbAl, K.nodeFit, K.cpuCs,
    (hAddP_iff (fun _ e => by cases e) hp).2 K.curH, ?_, K.csLt, K.cs0⟩
  · rcases hAddP_cases hq with ⟨rfl, e⟩ | ⟨-, hq⟩
    · cases e
      rcases A.ks _ rfl with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · exact K.hksIn q z hq
  · rcases hAddP_cases hq with ⟨rfl, rfl⟩ | ⟨-, hq⟩
    · exact A.nodes _ rfl c hc
    · exact K.hnd q k hq c hc
  · by_cases e : L.cscW s = p
    · rw [e, hAddP_self]; exact fun h => by cases h
    · rw [hAddP_ne e]; exact K.cscH

theorem exAt_addP {th : TypedHeap} {H : P1.Heap} {s : S} {p q : U64} (hq : q ≠ p) :
    ExAt (L := L) th (hAddP H p) s q ↔ ExAt (L := L) th H s q := by
  unfold ExAt KsObj; rw [hAddP_ne hq]

/-- **`JCovD` with the pool's page in `H`**: the page covered by a cap of
the MDB (the pool cap), and not an idle object (it lies in a RAM untyped
region, `IdleOut`). -/
theorem Sched.JCovD.addP {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {D Cs : Set U64} {s : S} {p : U64}
    (h : JCovD (L := L) th H G D Cs s) (hp : H p = none) (hth : th p = none)
    (hcov : Covered (L.mem s) G p.val (p.val + 4096))
    (hni : ¬ IdleAt (L := L) s p) :
    JCovD (L := L) th (hAddP H p) G D Cs s := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => ?_, h.ks, fun x hx p' sb fi hc q hq => ?_⟩
  · have hqp : q ≠ p := fun e => by subst e; rw [hth] at hq; cases hq
    exact (h.th q k hq).imp_right (Or.imp_right (exAt_addP hqp).2)
  · rcases hAddP_cases hq with ⟨rfl, rfl⟩ | ⟨hqp, hq⟩
    · exact Or.inl hcov
    · exact (h.h q k hq).imp_right (Or.imp_right (exAt_addP hqp).2)
  · have hd := h.dead q hq
    by_cases hqp : q = p
    · subst hqp
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun z e => ?_⟩ <;> rw [hAddP_self] at e <;> cases e
    · unfold DeadP at hd ⊢; rw [hAddP_ne hqp]; exact hd
  · obtain ⟨g1, g2, g3⟩ := h.idleOut x hx p' sb fi hc q hq
    refine ⟨g1, g2, fun k hk => ?_⟩
    have hqp : q ≠ p := fun e => hni (e ▸ hq)
    rw [hAddP_ne hqp] at hk
    exact g3 k hk

/-- **The spec's objects in `H` with the pool's page** (`SpecCover`): every
object after an `MpFr` step is one before but the pool at `p`. -/
theorem Sched.SpecCover.addP {H : P1.Heap} {p : U64} {σ σ' : Fl4Spec.State Unit} (h : SpecCover H σ) (hp : H p = none)
    (F : MpFr σ σ') (hnew : ∀ o ao, σ'.kheap o = some (.archObj ao) → σ.kheap o = none → o = p.bv) :
    SpecCover (hAddP H p) σ' := by
  refine ⟨fun o x ho => (hAddP_iff (fun _ e => by cases e) hp).2 (h.ntfn o x (F.ntfn.1 ho)),
    fun o x ho => (hAddP_iff (fun _ e => by cases e) hp).2 (h.ep o x (F.ep.1 ho)),
    fun o x ho => (hAddP_iff (fun _ e => by cases e) hp).2 (h.reply o x (F.reply.1 ho)),
    fun y k ho => h.sc0 y k (F.sc.1 ho), fun o ao ho => ?_⟩
  rcases F.kh o with e | ⟨r, cs, cs', h1, h2⟩ | ⟨h1, a, h2⟩
  · rw [e] at ho
    obtain ⟨n, hn, hH⟩ := h.arch o ao ho
    have hq : (⟨o⟩ : U64) ≠ p := fun e' => by rw [e'] at hH; rw [hp] at hH; cases hH
    exact ⟨n, hn, by rw [hAddP_ne hq]; exact hH⟩
  · rw [h2] at ho; cases ho
  · have e := hnew o ao ho h1
    have hq : (⟨o⟩ : U64) = p := by rw [e]
    exact ⟨12, le_rfl, by rw [hq, hAddP_self]⟩

theorem Sched.ObjCover.mp {N T E R C : Set U64} {σ σ' : Fl4Spec.State Unit} (h : ObjCover N T E R C σ) (F : MpFr σ σ') :
    ObjCover N T E R C σ' :=
  ⟨fun o x ho => h.tcb o x (F.tcb.1 ho), fun o x ho => h.ntfn o x (F.ntfn.1 ho), fun o x ho => h.ep o x (F.ep.1 ho),
    fun o x ho => h.reply o x (F.reply.1 ho), fun o y k ho => h.sc o y k (F.sc.1 ho)⟩

end


/-! ## P1's sets and the placement after `MakePool` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem addOKP_ksb {H : P1.Heap} {N : U64 → Prop} {kd : P1.HKind} {Cs : Set U64} {s s' : S}
    (A : P1.AddOKP st H N kd Cs s) (hk : L.ksb s' = L.ksb s) : P1.AddOKP st H N kd Cs s' := by
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hk]
  exact ⟨A.fresh, A.align, A.fits, A.nz, A.disjH, A.disjN, fun q hq c hc => by rw [hnb]; exact A.nodes q hq c hc,
    fun q hq => by rw [hk]; exact A.ks q hq⟩

/-- **P1's `BlkOK` after `MakePool`** at `H` grown by the pool's page: the
slot words are cap-slot words (`JAtZ.slotCapW`), the region's words the new
`other` object's (`Ω`, no frame word: no object of `H` there), the
ASID-table word untracked (`JAtZ.vsObjW`, `JAtZ.vsNodeW`). -/
theorem JAtZ.mpBlkAfter {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {p : U64} (Ad : P1.AddOKP st H (· = p) (.other 12) Cs s)
    (hHo : ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val)
    {hi : U64} (hh : hi.val < 2048) {s' : S} (hw : P1.WritesIn st s s' (MpW Z.th p (L.ksb s) hi)) :
    P1.BlkOK st (P1.Heap.tcbs (hAddP H p)) Cs (P1.Heap.omega (hAddP H p)) (hAddP H p) (P1.Heap.frame (hAddP H p))
      (P1.Heap.replies (hAddP H p)) (P1.Heap.scs (hAddP H p)) (P1.Heap.ntfns (hAddP H p))
      (P1.Heap.scBits (hAddP H p)) Ac s' := by
  have B0 := P1.BlkOK.addOther Ad J.kern.heap J.blk
  have hw' : P1.WritesIn st s s' (fun b => P1.Aligned b ∧ MpW Z.th p (L.ksb s) hi b) :=
    ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn ⟨hb, h⟩⟩
  have hT : P1.Heap.tcbs (hAddP H p) = P1.Heap.tcbs H := Ad.tcbs_eq (by simp)
  have hF : P1.Heap.frame (hAddP H p) = P1.Heap.frame H := Ad.frame_eq_other
  have hp : H p = none := Ad.fresh p rfl
  have hHk := J.kern.heap
  refine (P1.blk_of_capw_untracked B0 hw' fun b ⟨hal, hb⟩ => ?_).1
  rw [hT, hF]
  rcases hb with ⟨x, k, hx, hk, rfl⟩ | ⟨h1, h2⟩ | rfl
  · rcases J.slotCapW P1.tlow_slots _ ⟨x, hx, k, hk, rfl⟩ with h | ⟨h1, h2⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨Ad.omega_sub h1, h2⟩)
  · refine Or.inl (Or.inr ⟨⟨hal, p, .other 12, hAddP_self, Or.inr (Or.inr (Or.inl ⟨12, rfl⟩)),
      ⟨h1, by simpa [P1.HKind.bits] using h2⟩⟩, fun hf => ?_⟩)
    obtain ⟨-, q, k, hq, -, g1, g2⟩ := hf
    rcases hHo q k hq with e | e <;> omega
  · have hb : VsW Z (L.ksb s) (atA (L.ksb s) hi) := Or.inr (Or.inl ⟨hi, hh, rfl⟩)
    have Ap : VsApart (L := L) Z H Cs s := ⟨J.scOut⟩
    refine Or.inr ⟨⟨J.vsW_al hb, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, fun hf => ?_⟩
    · rcases J.vsObjW Ap hb (p := t) (k := .tcb) ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · rcases J.vsNodeW hb hc with e | e <;> omega
    · have he' : H e = some .ep ∨ H e = some .ntfn := by
        rcases he with he | he
        · exact Or.inl ((hAddP_iff (fun _ e => by cases e) hp).1 he)
        · exact Or.inr ((hAddP_iff (fun _ e => by cases e) hp).1 he)
      have hb8 : (atA (L.ksb s) hi).val % 8 = 0 := J.vsW_al hb
      rcases he' with he' | he'
      · have ha := hHk.align e _ he'
        simp only [P1.HKind.bits] at ha
        rcases J.vsObjW Ap hb he' (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
      · have ha := hHk.align e _ he'
        simp only [P1.HKind.bits] at ha
        rcases J.vsObjW Ap hb he' (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
    · obtain ⟨-, q, k, hq, hk, hin⟩ := hf
      have hko : ∀ z, k ≠ .other z := by
        rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
      obtain ⟨g1, g2⟩ := hin
      rcases J.vsObjW Ap hb hq hko with e | e <;> omega

/-- **`JPlaced` after a slot step keeping the SCs** (`JPlaced.slotTFH` with
the SCs of the spec kept in place of `KeepCT`). -/
theorem Sched.JPlaced.slotTFHs {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ)
    (hsc : ∀ (c : U64) y n, σ'.kheap c.bv = some (.schedContext y n) → σ.kheap c.bv = some (.schedContext y n))
    (hk : L.ksb s' = L.ksb s) (hL : IntLayout th (L.ksb s))
    (hT : TypedKeptH th H (Sched.idleScW (L := L) s) (L.mem s) (L.mem s'))
    (hfh : ∀ t, th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbf : ∀ t, th t = some .tcb → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))))
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    JPlaced (L := L) th H Tr C s' σ' := by
  have hirqS : ∀ i : U64, i.val < 128 → IsSlot th (nodeA (L.ksb s) i) := fun i hi => by
    have hA : AbsSlot th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
    have := hA.isSlot; rwa [cslotAddr_nil] at this
  have hty' : ∀ a, IsSlot th a → P1.CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) (capV (L.mem s') a) := by
    intro a ha
    rcases hT a ha with hn | ⟨b, hb, hs⟩ | ⟨h1, -⟩
    · exact capTyped_of_tyObj hn
    · exact capTyped_of_shape hs (h.typed b hb)
    · exact h1
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk' => h.sc c y n hc (hsc c y n hk'),
    by rw [hk]; exact h.ks, by rw [hk]; exact h.ksIn,
    fun a ha => hty' a ha, fun i hi => by rw [hk]; exact hty' _ (hirqS i hi), hfh, hbf, fun a ha => ?_⟩
  rcases hT a ha with hn | ⟨b, hb, hs⟩ | ⟨-, h2⟩
  · exact capObjH_of_tyObj hn
  · rw [hiw]; exact capObjH_of_shape hs (h.cobj b hb)
  · rw [hiw]; exact h2


set_option maxHeartbeats 4000000 in
/-- **The untyped caps' facts after `MakePool`** (as `ins_utcG`): the
source's cap now full (free part empty; it has the new pool cap as its
child, so the childless facts are vacuous), every other untyped cap the
same, its free part missing every slot (`RegionFree`), the region (zero
after) and the ASID-table word (`UtKsApart`); the new MDB slot misses every
childless untyped region (the destination CNode live, `live_slot`). -/
theorem JAtZ.mp_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost} {p hi : U64} (hh : hi.val < 2048)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {fi0 : U64}
    (hsrc0 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx))
    {pd : U64} {rd : Nat} {idxd : List Bool} (hpd : Z.th pd = some (.cnode rd)) (hld : idxd.length = rd)
    (hnull : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null) (hDL : DestLive Z.th (L.mem s) (L.ksb s) pd)
    (hsrc : capV (L.mem s') (cslotAddr (pp.bv, idx)) = .Untyped p fl4_abi.consts.bits.ASID_POOL 4096#u64 false)
    (hdst : ∃ b, capV (L.mem s') (cslotAddr (pd.bv, idxd)) = .AsidPool p b)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → y ≠ cslotAddr (pd.bv, idxd) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hw : P1.WritesIn st s s' (MpW Z.th p (L.ksb s) hi))
    (hzero : ∀ w : U64, P1.Aligned w → p.val ≤ w.val → w.val < p.val + 4096 → L.mem s' w = 0#u64)
    (hcdt : σ'.cdt = Function.update σ.cdt (pd.bv, idxd) (some (pp.bv, idx)))
    (horig : ∀ sl, sl ≠ (pd.bv, idxd) → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl q sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped q sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl q sb fi := by
  intro sl q sb fi dev hsl hcap' hdF
  subst hdF
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsd : cslotAddr (pp.bv, idx) ≠ cslotAddr (pd.bv, idxd) := by
    intro e; rw [e, hnull] at hsrc0; cases eq_of_ok_eq hsrc0
  have hdnm : cslotAddr (pd.bv, idxd) ∉ Z.G.chains.flatten := fun h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hnull] at h0; exact hn (eq_of_ok_eq h0).symm
  have hsm : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hAs.isSlot, _, hsrc0, fun h => by cases h⟩
  have hdl := fun {sl0 : Fl4Spec.CslotPtr} {q0 sb0 fi0' : U64} (h1 : AbsSlot Z.th sl0)
      (h2 : capV (L.mem s) (cslotAddr sl0) = .Untyped q0 sb0 fi0' false) (h3 : ¬ ∃ x, σ.cdt x = some sl0) =>
    J.live_slot arI (w := (pd.bv, idxd)) h1 h2 rfl h3 ⟨pd, rd, rfl, hpd, hld, hDL⟩
  have hta : (atA (L.ksb s) hi).val = (L.ksb s).val + 288000 + 8 * hi.val := atA_val J.xtop.fin.1.2.vs.ksb_fit hh
  by_cases hs : cslotAddr sl = cslotAddr (pp.bv, idx)
  · -- the source: full now
    have e := hsl.isSlot
    have hsle : sl = (pp.bv, idx) := cslotAddr_inj hP hsl hAs hs
    subst hsle
    have hc := capV_of_capAt hcap'
    rw [hsrc] at hc
    simp only [capability.Cap.Untyped.injEq] at hc
    obtain ⟨e1, e2, e3, -⟩ := hc
    subst q; subst sb; subst fi
    have U := J.utc _ _ _ fi0 false hAs hsrc0 rfl
    have B : NotDev (L.mem s) (cslotAddr (pp.bv, idx)) p fl4_abi.consts.bits.ASID_POOL fi0 :=
      notDev_ram (capV_of_capAt hsrc0)
    have hch : ∃ x, σ'.cdt x = some (pp.bv, idx) := ⟨(pd.bv, idxd), by rw [hcdt, Function.update_self]⟩
    have h4 : (4096#u64 : U64).val = 4096 := rfl
    refine ⟨U.pal, U.pfit, by rw [two_pow_asidPool, h4], fun _ => U.high B, fun _ => by rw [hcpu, hna]; exact U.actZ B,
      fun q k hk => by
        have := U.nostr q k hk
        rw [two_pow_asidPool] at this; rw [two_pow_asidPool, h4]; omega, fun _ w _ h1 h2 => by rw [h4] at h1; rw [two_pow_asidPool] at h2; omega,
      U.sb4, U.nostr, fun y _ => by rw [two_pow_asidPool, h4]; omega, fun h0 => absurd hch h0,
      fun _ h0 => absurd hch h0,
      fun _ => by rw [hna]; exact U.dwReg B, fun _ => by rw [hgp]; exact U.gReg B⟩
  have hne : cslotAddr sl ≠ cslotAddr (pd.bv, idxd) := fun e => by
    obtain ⟨b, hb⟩ := hdst
    have hc := capV_of_capAt hcap'
    rw [e, hb] at hc; cases hc
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped q sb fi false := by
    rw [← hcap _ hsl.isSlot hs hne]; exact capV_of_capAt hcap'
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped q sb fi false) := by rw [capAt_capV, hcv]
  have U := J.utc sl q sb fi false hsl hcap0 rfl
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have hfi := U.fiLe
  have hKs := J.jcov.ks _ hxm q sb fi hcv
  -- a slot misses the free part
  have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ q.val + fi.val ∨ q.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q', i, hi', rfl⟩ := hy
    obtain ⟨k, hk, hs'⟩ := hi'.size
    have hv := hi'.val hP
    rcases U.free q' k hk with e | e <;> omega
  have hnc' : (¬ ∃ x, σ'.cdt x = some sl) → ¬ ∃ x, σ.cdt x = some sl := by
    rintro h0 ⟨x, hx⟩
    apply h0
    by_cases e : x = (pd.bv, idxd)
    · exfalso
      subst e
      have h1 := hC.cdt _ hAd
      rw [hx] at h1
      exact hdnm (hM.tree.par_mem _ _ h1.symm).1
    · exact ⟨x, by rw [hcdt, Function.update_of_ne e]; exact hx⟩
  have B := notDev_ram hcv
  refine ⟨U.pal, U.pfit, U.fiLe, fun _ => U.high B, fun _ => by rw [hcpu, hna]; exact U.actZ B, U.free,
    fun _ w hal h1 h2 => ?_, U.sb4,
    U.nostr, fun y hy => ?_, fun h0 y hy => ?_, 
    fun _ h0 hf0 => ?_, fun _ => by rw [hna]; exact U.dwReg B, fun _ => by rw [hgp]; exact U.gReg B⟩
  · by_cases hb : MpW Z.th p (L.ksb s) hi w
    · rcases hb with ⟨x, k, hx, hk, rfl⟩ | ⟨g1, g2⟩ | rfl
      · exfalso
        have hf := hx.fit hP
        have := hk.lt
        have hv := wordOf_val (a := x) (k := k) (by omega)
        rw [hv] at h1 h2
        rcases hobj x hx with e | e <;> omega
      · exact hzero w hal g1 g2
      · exfalso
        rw [hta] at h1 h2
        rcases hKs.2.2 with e | e <;> omega
    · rw [hw.2.2 w hal hb]; exact U.zero B w hal h1 h2
  · have := hobj y ((hM'.members y).1 hy).1
    omega
  · have hnc := hnc' h0
    by_cases e : y = cslotAddr (pd.bv, idxd)
    · subst e
      exact (hdl hsl hcv hnc).1
    · obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
      by_cases e2 : y = cslotAddr (pp.bv, idx)
      · subst e2; exact U.ns hnc _ hsm
      have hc0 : capAt (L.mem s) y = ok c0 := by
        rw [capAt_capV, ← hcap y hys e2 e, ← capAt_capV]; exact h0'
      have hym : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hys, c0, hc0, hn⟩
      exact U.ns hnc y hym
  · have hnc := hnc' h0
    obtain ⟨r1, r3⟩ := U.rst B hnc hf0
    refine ⟨fun sl' h => ?_, by rw [hna, hDbg]; exact r3⟩
    by_cases e : sl' = (pd.bv, idxd)
    · subst e
      exact (hdl hsl hcv hnc).2
    · exact r1 sl' (by rw [← horig sl' e]; exact h)


theorem objBits_pool : Fl4Spec.objBits (.archObj (.asidPool fun _ => none)) = 12 := rfl

set_option maxHeartbeats 4000000 in
/-- **`SpecFree` after `MakePool`**: every spec object after is one before
of the same size (`SpecFree` before, the free indices no lower: the
source's now full) but the pool at `p`, which lies in the source's region:
the source's own free part is empty, and any other RAM untyped cap's free
part misses it (`UtInv.drange`: the caps' ranges disjoint, or the source a
descendant of that cap, so in its used part, `UtInv.inc`; the source has no
descendant). -/
theorem JAtZ.mp_sfree {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost} {p : U64}
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {fi0 : U64}
    (hsrc0 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx))
    {pd : U64} {idxd : List Bool}
    (hsrc : capV (L.mem s') (cslotAddr (pp.bv, idx)) = .Untyped p fl4_abi.consts.bits.ASID_POOL 4096#u64 false)
    (hdst : ∃ b, capV (L.mem s') (cslotAddr (pd.bv, idxd)) = .AsidPool p b)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → y ≠ cslotAddr (pd.bv, idxd) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hM' : MdbLinks Z.th (L.mem s') G')
    (hkp : σ'.kheap p.bv = some (.archObj (.asidPool fun _ => none)))
    (hkh : ∀ o, o ≠ p.bv → σ'.kheap o = σ.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ σ'.kheap o = none) ∨
      ∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ σ'.kheap o = some (.cnode r cs')) :
    SpecFree (L.mem s') G' σ' := by
  intro x hx q sb fi hc o ko ho
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hxs := ((hM'.members x).1 hx).1
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hsm : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hAs.isSlot, _, hsrc0, fun h => by cases h⟩
  have hsv := capV_of_capAt hsrc0
  have Us := J.utc _ _ _ fi0 false hAs hsrc0 rfl
  have hfi0 : fi0.val ≤ 4096 := by have := Us.fiLe; rwa [two_pow_asidPool] at this
  have hold : o ≠ p.bv → ∃ ko0, σ.kheap o = some ko0 ∧ Fl4Spec.objBits ko0 = Fl4Spec.objBits ko := by
    intro hne
    rcases hkh o hne with e | ⟨-, e⟩ | ⟨r, cs, cs', h1, h2⟩
    · exact ⟨ko, by rw [← e]; exact ho, rfl⟩
    · rw [e] at ho; cases ho
    · rw [h2] at ho; cases ho; exact ⟨_, h1, rfl⟩
  -- the source's range
  have hsrng := ut_range (capV_ut_sb hsv) (by rw [← hsv]; exact J.ut.reg _ hsm (by rw [hsv]; exact physF_ut _ _ _ _))
  rw [two_pow_asidPool] at hsrng
  by_cases hxs1 : x = cslotAddr (pp.bv, idx)
  · subst hxs1
    rw [hsrc] at hc
    simp only [capability.Cap.Untyped.injEq] at hc
    obtain ⟨e1, e2, e3, -⟩ := hc
    subst q; subst sb; subst fi
    rw [two_pow_asidPool]
    have h4 : (4096#u64 : U64).val = 4096 := rfl
    rw [h4]
    by_cases hop : o = p.bv
    · subst hop
      rw [hkp] at ho; cases ho
      rw [objBits_pool, UScalar.bv_toNat]
      right; exact ⟨le_rfl, by norm_num⟩
    · obtain ⟨ko0, h0, hb⟩ := hold hop
      have := J.sfree _ hsm p _ fi0 hsv o ko0 h0
      rw [hb, two_pow_asidPool] at this
      omega
  by_cases hxd : x = cslotAddr (pd.bv, idxd)
  · exfalso
    obtain ⟨b, hb⟩ := hdst
    rw [hxd, hb] at hc; cases hc
  have hcv : capV (L.mem s) x = .Untyped q sb fi false := by rw [← hcap x hxs hxs1 hxd]; exact hc
  have hxm : x ∈ Z.G.chains.flatten := (hM.members x).2 ⟨hxs, _, by rw [capAt_capV, hcv], fun h => by cases h⟩
  by_cases hop : o = p.bv
  · subst hop
    rw [hkp] at ho; cases ho
    rw [objBits_pool, UScalar.bv_toNat]
    have hxr := ut_range (capV_ut_sb hcv) (by rw [← hcv]; exact J.ut.reg _ hxm (by rw [hcv]; exact physF_ut _ _ _ _))
    have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    rw [h12]
    by_cases hd : Disj (capV (L.mem s) x) (capV (L.mem s) (cslotAddr (pp.bv, idx)))
    · rw [hcv, hsv] at hd
      unfold Disj at hd
      left; omega
    · rcases J.ut.drange _ hsm p _ fi0 false hsv x hxm hxs1 (by rw [hcv]; exact physF_ut _ _ _ _) hd with h | h
      · exact absurd h (nodesc_of_cdt hP hC hAs hnch x)
      · obtain ⟨-, g1, g2⟩ := J.ut.inc x hxm q sb fi false hcv _ h
        rw [hsv] at g1 g2
        right; omega
  · obtain ⟨ko0, h0, hb⟩ := hold hop
    rw [← hb]; exact J.sfree x hxm q sb fi hcv o ko0 h0


/-- `Z` with the new MDB ghost and the pool added (the sets after `MakePool`). -/
abbrev XSets.mp (Z : XSets) (G' : MdbGhost) (p : U64) : XSets := { Z with G := G', P := insert p Z.P }

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` after `MakePool` when its region is clean** (module docstring),
from the restart's state `s`: FL4 writes the `MpW` words (slots, the
region, zero after, and one ASID-table word), the source's cap full and the
destination's the pool cap, the other slots kept; the spec's step is the
pool's creation, two CNodes' change and the CDT's and original bits' at the
destination (`MpFr` once the region holds no spec object, `hspec`).
`XTopAt` after at the new ghost and pool set given. -/
theorem JAtZ.mpStepJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {p hi : U64} (hh : hi.val < 2048)
    (hTh : ∀ q k, Z.th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 4096 ≤ q.val)
    (hHo : ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val)
    (Ad : P1.AddOKP st H (· = p) (.other 12) Cs s)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat < p.val ∨ p.val + 4096 ≤ o.toNat)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {fi0 : U64}
    (hsrc0 : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx))
    {pd : U64} {rd : Nat} {idxd : List Bool} (hpd : Z.th pd = some (.cnode rd)) (hld : idxd.length = rd)
    (hnull : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null) (hDL : DestCap Z.th (L.mem s) pd)
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    (hX' : XTopAt (L := L) AR (Z.mp G' p) s' a' σ')
    (hw : P1.WritesIn st s s' (MpW Z.th p (L.ksb s) hi))
    (hzero : ∀ w : U64, P1.Aligned w → p.val ≤ w.val → w.val < p.val + 4096 → L.mem s' w = 0#u64)
    (hMs : MpStep p σ σ')
    (hkp : σ'.kheap p.bv = some (.archObj (.asidPool fun _ => none)))
    (hkh : ∀ o, o ≠ p.bv → σ'.kheap o = σ.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ σ'.kheap o = none) ∨
      ∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ σ'.kheap o = some (.cnode r cs'))
    (hcdt : σ'.cdt = Function.update σ.cdt (pd.bv, idxd) (some (pp.bv, idx)))
    (horig : ∀ sl, sl ≠ (pd.bv, idxd) → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hsrc : capV (L.mem s') (cslotAddr (pp.bv, idx)) = .Untyped p fl4_abi.consts.bits.ASID_POOL 4096#u64 false)
    (hdst : ∃ b, capV (L.mem s') (cslotAddr (pd.bv, idxd)) = .AsidPool p b)
    (hdstb : ∀ b, capV (L.mem s') (cslotAddr (pd.bv, idxd)) = .AsidPool p b → b.val % 512 = 0 ∧ b.val < 2 ^ 20)
    (hp0 : p ≠ 0#u64)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → y ≠ cslotAddr (pd.bv, idxd) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hDel : DelInv Z.th (L.mem s')) (hU' : UtInv (L.mem s') G') :
    JAtZ (L := L) arI AR (Z.mp G' p) (hAddP H p) Cs Ac Lst D s' a' σ' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hPl := J.xtop.rel.1
  obtain ⟨-, ⟨-, -, hM, hC, -⟩, -⟩ := J.xtop.rel
  obtain ⟨-, ⟨-, -, hM', -, -⟩, hFI', -, -, -, -⟩ := hX'.rel
  have hfit : p.val + 4096 ≤ 2 ^ 64 := Ad.fits p rfl
  have hp : H p = none := Ad.fresh p rfl
  have hthp : Z.th p = none := by
    cases e : Z.th p with
    | none => rfl
    | some k => have := hTh p k e; omega
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsm : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hAs.isSlot, _, hsrc0, fun h => by cases h⟩
  have hsv := capV_of_capAt hsrc0
  have hnv := capV_of_capAt hnull
  -- the spec's frame
  have hσp : σ.kheap p.bv = none := by
    cases e : σ.kheap p.bv with
    | none => rfl
    | some ko => have := hspec _ ko e; rw [UScalar.bv_toNat] at this; omega
  have F : MpFr σ σ' := by
    refine ⟨fun o => ?_, hMs.1.ct, hMs.1.idle, hMs.1.cons, hMs.1.ctime, hMs.1.csc, hMs.1.isc, hMs.1.act, hMs.1.rq,
      hMs.1.rel, hMs.1.gpml4⟩
    by_cases hop : o = p.bv
    · subst hop; exact Or.inr (Or.inr ⟨hσp, _, hkp⟩)
    rcases hkh o hop with e | ⟨hin, e⟩ | h
    · exact Or.inl e
    · left
      rw [e]
      cases e' : σ.kheap o with
      | none => rfl
      | some ko =>
        have h1 := hspec o ko e'
        have h2 := (regionSet_iff p ⟨o⟩ 12 (by decide) (by simpa using hfit)).1 hin
        have h2' : p.val ≤ o.toNat ∧ o.toNat < p.val + 2 ^ 12 := h2
        omega
    · exact Or.inr (Or.inl h)
  -- the words kept
  obtain ⟨k1, k2, kb, k3, k4, hOut⟩ := J.mp_keeps hh hw.2.2 hHo
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩, fun q x hq => ⟨x, F.reply.2 hq, rfl, rfl⟩,
    fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' : Sched.RRecv (L.mem s') Z.R σ' := fun d hd hr => by
    obtain ⟨h1, h2⟩ := J.rrecv d hd (F.recvB hr)
    exact ⟨(k4 d hd).2.trans h1, (k4 d hd).1.trans h2⟩
  have hS' := hX'.fin.1.1.1
  have hidl : Sched.IdleKeep (L := L) s s' := J.idleW_keep hS' F.idle F.isc
  -- the debug word
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    refine hw.2.2 _ J.kern.dwAl fun hb => ?_
    rcases hb with ⟨x, k, hx, hk, e⟩ | ⟨g1, g2⟩ | e
    · have hf := hx.fit hPl
      have := hk.lt
      have hv := wordOf_val (a := x) (k := k) (by omega)
      exact J.kern.dwObj x hx ⟨by rw [e, hv]; omega, by rw [e, hv]; omega⟩
    · have := Ad.nodes p rfl _ J.kern.cs0
      simp only [P1.HKind.bits] at this
      have hnb : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 + (0#u64 : U64).val * 4288 := rfl
      omega
    · have hb : VsW Z (L.ksb s) (atA (L.ksb s) hi) := Or.inr (Or.inl ⟨hi, hh, rfl⟩)
      rw [← e] at hb
      rcases J.vsNodeW hb J.kern.cs0 with e' | e' <;> omega
  -- the dead stay dead
  have hAI : Sched.ActIdle σ' := J.act.mp F
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_keep hS' hX'.ipc
      (fun x hx _ => let ⟨y, hy, hc⟩ := F.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
      (fun x hx => F.ep.2 hx) (fun x hx => ⟨x, F.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, F.reply.2 hx, rfl⟩) (fun x n hx => ⟨x, F.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q)
      (fun z hz _ => hOut q z hz) F.idle hAI.1 (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- the slots
  have hTKH : TypedKeptH Z.th H (Sched.idleScW (L := L) s) (L.mem s) (L.mem s') := by
    intro y hy
    by_cases e1 : y = cslotAddr (pp.bv, idx)
    · left; rw [e1, hsrc]; rfl
    by_cases e2 : y = cslotAddr (pd.bv, idxd)
    · left; obtain ⟨b, hb⟩ := hdst; rw [e2, hb]; rfl
    · right; left; exact ⟨y, hy, by rw [hcap y hy e1 e2]⟩
  have hfh : ∀ t, Z.th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) =
        .Endpoint ep b0 b1 b2 b3 b4 := by
    intro t ht
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hi3 : IsSlotAt Z.th t 3 := Or.inr ⟨ht, by decide⟩
    rw [cslot_tcb3, hcap _ ⟨t, 3, hi3, rfl⟩ (slotOf_ne_cnV hPl hi3 ht hpp hidx) (slotOf_ne_cnV hPl hi3 ht hpd hld),
      ← cslot_tcb3]
    exact hJ.fh t ht
  have hbf : ∀ t, Z.th t = some .tcb →
      Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))) := by
    intro t ht
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hi2 : IsSlotAt Z.th t 2 := Or.inr ⟨ht, by decide⟩
    rw [cslot_tcb2, hcap _ ⟨t, 2, hi2, rfl⟩ (slotOf_ne_cnV hPl hi2 ht hpp hidx) (slotOf_ne_cnV hPl hi2 ht hpd hld),
      ← cslot_tcb2]
    exact hJ.bfs t ht
  have Ad' : P1.AddOKP st H (· = p) (.other 12) Cs s' := addOKP_ksb Ad hks
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th (hAddP H p) Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, (hJ.slotTFHs (fun c y n h => F.sc.1 h) hks J.intL hTKH hfh hbf hidl.2).addP Ad'⟩
  -- the cover
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := by
    intro y hy hph hu
    by_cases e1 : y = cslotAddr (pp.bv, idx)
    · rw [e1, hsv] at hu; cases hu
    by_cases e2 : y = cslotAddr (pd.bv, idxd)
    · rw [e2, hnv, physF_null] at hph; cases hph
    have e := hcap y hy e1 e2
    exact ⟨y, hy, by rw [e]; exact hph, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  have hUK : UtKept Z.th (L.mem s) (L.mem s') := by
    intro x hx q sb fi d hc
    by_cases e1 : x = cslotAddr (pp.bv, idx)
    · rw [e1, hsrc] at hc
      simp only [capability.Cap.Untyped.injEq] at hc
      obtain ⟨e1', e2', e3', e4'⟩ := hc
      subst q; subst sb; subst fi; subst d
      have h4 : (4096#u64 : U64).val = 4096 := rfl
      have := (J.utc _ _ _ fi0 false hAs hsrc0 rfl).fiLe
      rw [two_pow_asidPool] at this
      exact ⟨_, hAs.isSlot, fi0, hsv, Or.inl (by rw [h4]; exact this)⟩
    by_cases e2 : x = cslotAddr (pd.bv, idxd)
    · obtain ⟨b, hb⟩ := hdst; rw [e2, hb] at hc; cases hc
    exact ⟨x, hx, fi, by rw [← hcap x hx e1 e2]; exact hc, Or.inl le_rfl⟩
  have hdm' : cslotAddr (pd.bv, idxd) ∈ G'.chains.flatten := by
    obtain ⟨b, hb⟩ := hdst
    exact (hM'.members _).2 ⟨hAd.isSlot, .AsidPool p b, by rw [capAt_capV, hb], fun h => by cases h⟩
  have hcovp : Covered (L.mem s') G' p.val (p.val + 4096) := by
    obtain ⟨b, hb⟩ := hdst
    obtain ⟨r1, r2⟩ := range_ap p b hfit
    exact ⟨_, hdm', by rw [hb]; exact physF_ap p b, by rw [hb]; rfl, by rw [hb, r1], by rw [hb, r2] <;> omega⟩
  have hni : ¬ IdleAt (L := L) s' p := fun h => by
    have := (J.jcov.idleOut _ hsm p _ fi0 hsv p ((idleAt_of hidl).1 h)).1
    rw [two_pow_asidPool] at this; omega
  have hjc : JCovD (L := L) Z.th (hAddP H p) G' D Cs s' :=
    (J.jcov_cover hks hM' hCK hUK hdead hidl).addP hp hthp hcovp hni
  -- `JKern`
  have horig' : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := by
    intro sl h
    by_cases e : sl = (pd.bv, idxd)
    · right; rw [e]; exact hAd
    · left; rw [← horig sl e]; exact h
  have hkern : JKern (L := L) (hAddP H p) Cs D Z.th s' σ' :=
    (J.kern_keep hks hcpu hS' F.ct F.csc horig' F.gpml4 (fun _ _ h => F.arch h) hDbg).addP Ad'
  have hutc := J.mp_utc hh hpp hidx hsrc0 hnch hpd hld hnull (hDL.live _) hsrc hdst hcap hw hzero hcdt horig F.gpml4 hM' hDbg
  have hblk := J.mpBlkAfter Ad hHo hh hw
  have hJC : JCs (L := L) (Z.mp G' p) s' σ' :=
    ⟨hDel, hU', fun G hG => FinM.of_links J.xtop.rel.1 hM' hG hFI'.fm,
      J.mp_sfree hpp hidx hsrc0 hnch hsrc hdst hcap hM' hkp hkh⟩
  have R : JRest (L := L) arI (Z.mp G' p) (hAddP H p) Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
      J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.buf⟩), hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjc, hkern, hutc, J.nsc.mp F, J.inv.mp F, CurInvW.mp J.cur F,
      J.own.mp F, J.off.mp F, hAI, J.bsa.mp F, J.isorted.mp F, J.curRun.mp F, hblk⟩
  have hnew : ∀ o ao, σ'.kheap o = some (.archObj ao) → σ.kheap o = none → o = p.bv := by
    intro o ao h1 h2
    by_contra hne
    rcases hkh o hne with e | ⟨-, e⟩ | ⟨r, cs, cs', e1, e2⟩
    · rw [e, h2] at h1; cases h1
    · rw [e] at h1; cases h1
    · rw [e2] at h1; cases h1
  have hk' : ∀ {k : P1.HKind}, (∀ z, k ≠ .other z) → ∀ q, hAddP H p q = some k ↔ H q = some k :=
    fun hk q => hAddP_iff hk hp
  -- the VSpace caps placed: the source an untyped cap, the destination the
  -- new pool's cap (its pool in the grown `P`), the other slots kept
  have hvc : Vs.VsSlotsW Z.th (insert p Z.P) Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') := by
    intro y hy
    by_cases e1 : y = cslotAddr (pp.bv, idx)
    · rw [e1, hsrc]; trivial
    by_cases e2 : y = cslotAddr (pd.bv, idxd)
    · obtain ⟨b, hb⟩ := hdst
      obtain ⟨h1, h2⟩ := hdstb b hb
      rw [e2, hb]
      exact VCapOK.toW (by simp only [VCapOK]; exact ⟨⟨Set.mem_insert _ _, hp0⟩, h1, h2⟩)
    · rw [hcap y hy e1 e2]
      exact (J.vsc y hy).mono (Set.subset_insert _ _) subset_rfl subset_rfl subset_rfl subset_rfl
  -- the buffer fields (`JBuf`): the pool fresh, CNode slots changed, the
  -- region's (absent) objects gone; the source an untyped cap, the
  -- destination a pool cap
  have hfk : IpcFrKeep σ σ' := by
    refine ⟨fun t x' hx => ?_, fun q vms hq => ?_, fun q vms hq => ?_⟩
    · rcases F.kh t with e | ⟨r, cs, cs', -, e⟩ | ⟨-, a0, e⟩
      · exact Or.inr ⟨x', by rw [← e]; exact hx, rfl, rfl⟩
      · rw [hx] at e; cases e
      · rw [hx] at e; cases e
    · rcases F.kh q with e | ⟨r, cs, cs', e0, -⟩ | ⟨e0, -⟩
      · rw [e]; exact hq
      · rw [hq] at e0; cases e0
      · rw [hq] at e0; cases e0
    · by_cases hq0 : q = p.bv
      · subst hq0; rw [hkp] at hq; cases hq
      · rcases hkh q hq0 with e | ⟨-, e⟩ | ⟨r, cs, cs', -, e⟩
        · rw [← e]; exact hq
        · rw [hq] at e; cases e
        · rw [hq] at e; cases e
  have hbf : JBuf (L := L) (Z.mp G' p) s' σ' := by
    refine ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, fun y hy => ?_⟩
    by_cases e1 : y = cslotAddr (pp.bv, idx)
    · rw [e1, hsrc]; trivial
    by_cases e2 : y = cslotAddr (pd.bv, idxd)
    · obtain ⟨b, hb⟩ := hdst; rw [e2, hb]; trivial
    · rw [hcap y hy e1 e2]; exact (J.fcap y hy).mono fun _ => UFr.keep hfk.page
  -- `LiveDN` and `zD` after (LiveFrame's `wstepR`: the destination slot in a
  -- CNode named by a CNode cap, the source's free index changed)
  have hdkM : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    dbgKeep_of_writes J.blk hw fun b hb => by
      rcases hb with ⟨x, k, hx, hk, e⟩ | ⟨g1, g2⟩ | e
      · have hf := hx.fit hPl
        have := hk.lt
        have hv := wordOf_val (a := x) (k := k) (by omega)
        exact J.inSlot_notDbg ⟨x, hx, by rw [e, hv]; omega, by rw [e, hv]; omega⟩
      · refine J.notDbg' (fun q hq => ?_) (fun c hc => ?_)
        · have := hHo q .tcb hq; simp only [P1.HKind.bits] at this ⊢; omega
        · have := Ad.nodes p rfl c hc; simp only [P1.HKind.bits] at this; omega
      · have hb' : VsW Z (L.ksb s) (atA (L.ksb s) hi) := Or.inr (Or.inl ⟨hi, hh, rfl⟩)
        rw [← e] at hb'
        exact J.notDbg' (fun q hq => J.vsObjW ⟨J.scOut⟩ hb' hq (fun _ e => by cases e))
          (fun c hc => by rcases J.vsNodeW hb' hc with e' | e' <;> omega)
  have hTHM : P1.Heap.tcbs (hAddP H p) = P1.Heap.tcbs H := Set.ext fun q => hk' (fun _ e => by cases e) q
  have hZfM : ∀ y, IsSlot Z.th y → ∀ p' zt n, capV (L.mem s') y = .Zombie p' zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p' zt n := fun y hy p' zt n h => by
    by_cases e1 : y = cslotAddr (pp.bv, idx)
    · subst e1; rw [hsrc] at h; cases h
    by_cases e2 : y = cslotAddr (pd.bv, idxd)
    · subst e2; obtain ⟨b, hb⟩ := hdst; rw [hb] at h; cases h
    · exact ⟨y, hy, by rw [← hcap y hy e1 e2]; exact h⟩
  have hLvM : LiveDN (L := L) Z.th (hAddP H p) Cs G' s' σ' := by
    obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := J.live
    have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
    refine LiveDN.wstepR J ⟨hL, ⟨lst, hDW⟩, hN⟩ hM'
      ⟨lst, by rw [hTHM]; exact dbgWFL_step J.xtop hX' rfl rfl hTe hDW hdkM⟩
      (fun q hq => hjc.dead q (J.zD q hq)) F.idle hdkM [(pd.bv, idxd)]
      (fun sl hsl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
        subst hsl; exact ⟨pd, rd, rfl, hpd, hld, hDL⟩)
      (fun y hy hne => by
        have e2 : y ≠ cslotAddr (pd.bv, idxd) := hne _ (List.mem_singleton_self _)
        by_cases e1 : y = cslotAddr (pp.bv, idx)
        · subst e1; rw [hsrc, hsv]; exact LSim.of_shape rfl
        · rw [hcap y hy e1 e2]; exact LSim.rfl' _)
      (fun sl h => by
        by_cases e : sl = (pd.bv, idxd)
        · exact Or.inr (by simp [e])
        · exact Or.inl (by rw [← horig sl e]; exact h))
      (fun sl hsl h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
        subst hsl; obtain ⟨b, hb⟩ := hdst; rw [hb] at h; cases h)
      hZfM
      (fun y0 hy0 hn => by
        by_cases e2 : y0 = cslotAddr (pd.bv, idxd)
        · subst e2; exact absurd hnv hn
        by_cases e1 : y0 = cslotAddr (pp.bv, idx)
        · subst e1
          exact ⟨_, hAs.isSlot, (by rw [hsrc]; exact fun h => by cases h), (by rw [hsrc, hsv]; rfl)⟩
        · exact ⟨y0, hy0, by rw [hcap y0 hy0 e1 e2]; exact hn, by rw [hcap y0 hy0 e1 e2]⟩)
  exact J.add_frame rfl rfl rfl hks hX' hJC R (by rw [hks]; exact J.ks) J.thT J.ip
    (fun n hn => by rw [hks]; exact J.nk n hn) (J.cover.addP hp F hnew) (J.obj.mp F)
    ⟨fun t ht => (hk' (fun _ e => by cases e) t).2 (J.zH.1 t ht),
      fun e he => (hk' (fun _ e => by cases e) e).2 (J.zH.2.1 e he),
      fun r hr => (hk' (fun _ e => by cases e) r).2 (J.zH.2.2.1 r hr),
      fun n hn => (hk' (fun _ e => by cases e) n).2 (J.zH.2.2.2 n hn)⟩
    ⟨fun e he => J.hset.1 e ((hk' (fun _ e => by cases e) e).1 he),
      fun n hn => J.hset.2.1 n ((hk' (fun _ e => by cases e) n).1 hn),
      fun r hr => J.hset.2.2 r ((hk' (fun _ e => by cases e) r).1 hr)⟩
    (fun c z hc => J.hscC c z ((hk' (fun _ e => by cases e) c).1 hc)) hvc hbf
    ⟨fun y hy => by
      by_cases e1 : y = cslotAddr (pp.bv, idx)
      · rw [e1, hsrc]; trivial
      by_cases e2 : y = cslotAddr (pd.bv, idxd)
      · obtain ⟨b, hb⟩ := hdst; rw [e2, hb]; trivial
      · rw [hcap y hy e1 e2]; exact J.ext.nat y hy, J.ext.vkeep (J.mp_vkeep hh hw.2.2 hHo)⟩
    hLvM (fun q hq => J.zD q (ZTcb.of_zombies hZfM hq))


end


/-! ## The ASID control cap at `JAt` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem restrictTh_clean {th : TypedHeap} {p : U64}
    (hTh : ∀ q k, th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 4096 ≤ q.val) :
    restrictTh th p.val (p.val + 4096) = th := by
  funext q
  unfold restrictTh
  split
  · rename_i hq
    cases hk' : th q with
    | none => rfl
    | some k => have := hTh q k hk'; omega
  · rfl

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap at `JAt` when MakePool's regions are clean**
(`MpClean`, `MpSpecClean`): VsDecFrame's `decode_invocation_asid_controlXG`
at `TopSR` (`MpPlacedHyp` and the region facts from `JAtZ`,
`JAtZ.mpPlacedC`, `JAtZ.mpRegionC`), each outcome of `MakePool` at `JAt` by
`JAtZ.mpStepJ` from the restart's `JAtZ` (`JAtZ.restartJ`), with the domain
schedule (`domFrame_asid_control`). -/
theorem decode_invocation_asid_controlJC (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hcl : MpClean (L := L) Z H D s) (hsp : MpSpecClean (L := L) Z s σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : JMpExtra (L := L) Z s extra excaps)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hMP := J.mpPlacedC arI hcl
  have hext' : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        Z.th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid Z.th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
          (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
          MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p ∧
            RegOKTop (L := L) Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ p := by
    rcases hext.2 with h | ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact Or.inl h
    · exact Or.inr ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
        fun p fi e hn => J.mpRegionC arI hcl h1 h2 (by rw [← e]; exact h5) hn⟩
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨hPl, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hUK : UtKsOut (L.ksb s) (L.mem s) Z.G := fun x hx p sb fi h => (J.jcov.ks x hx p sb fi h).1
  have hrun := J.curRun.run hni
  refine Or.inl (DecOKMX.toXD arI
    (X₁ := fun s' a' σ' => DomRel (L.mem s') (L.ksb s') σ' → JAt (L := L) arI AR s' a' σ')
    (DecOKMQX.toX arI (decode_invocation_asid_controlXG arI Z.th hPl s ar σ Z.G hCR hFI J.ut hMO
      (fun _ _ _ _ => trivial) vsMpHyps_top hX.fin.1 hX.fin.2.1 hX.fin.2.2.1 hX.fin.1.2.vs hX.fin.1.2.pt
      hX.fin.1.2.vo hX.fin.1.2.po hX.fin.1.2.pv lbl slbl hlM length buf ct hct hcur htcb J.kern.act hrun args hlen hargs
      extra excaps hext' (X := fun s' a' σ' => DomRel (L.mem s') (L.ksb s') σ' → JAt (L := L) arI AR s' a' σ')
      (fun _ => ⟨Z, H, Cs, Ac, Lst, D, J⟩) ?_ slot blk call don fp ci sl buffer) (fun _ _ _ h => h))
    (domFrame_asid_control arI Z.th s ar σ Z.G hCR hFI J.ut hMO hX.fin.1 hX.fin.2.1 hX.fin.2.2.1 lbl slbl hlM length
      buf ct hct hcur htcb J.kern.act hrun args hlen hargs extra excaps hext' hUK slot blk call don fp ci sl buffer)
    (okAll_specDec_asidControl fp slbl (args.map UScalar.bv) ci sl excaps buffer) hDR (fun _ _ _ hx hd => hx hd))
  intro s' a' σ' p th' G' dest ps y rc hex1 hcy hSR hR' hPt' hcur' hPI' hCR' hFI' hMO' hth hk hsc hRg hxu hU' hMS
    hMid hDR'
  obtain ⟨s1, ct', hi, σ1, hs1, hct', hst', hh, hks1, hcpu1, hW, hzero, -, hMs, hkp, hkh, hcdt, horig, hsrc, hdst,
    hdstb, hcap, hDI, ⟨pp, rs, idx, fi0, rfl, hpp, hidx, hsrc0, hnch⟩, pd, rd, idxd, rfl, hpd, hld, hnull, hCn⟩ := hMid
  -- the region holds no object
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hsm : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hCR.2.2.1.members _).2 ⟨hAs.isSlot, _, hsrc0, fun h => by cases h⟩
  have hnd := nodesc_of_cdt hPl hCR.2.2.2.1 hAs hnch
  have hsv := capV_of_capAt hsrc0
  obtain ⟨hTh, hHo⟩ := J.mpEmpty arI hcl hsm hsv hnd
  have hrt := restrictTh_clean hTh
  rw [hrt] at hth
  subst hth
  have hTSR := hMP p Z.th s' a' σ' hrt.symm hk hsc hRg hxu
  -- `XTopAt` after
  have hF : FinX st Z.th (insert p Z.P) Z.L4 Z.L3 Z.L2 Z.L1
      (TopSR st Z.th (insert p Z.P) Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s' a' σ' := by
    refine ⟨hTSR.1 hSR, hR', hPt', hPI' Z.L4 hX.fin.2.2.2.1, ?_⟩
    obtain ⟨t, h1, h2, -⟩ := hX.fin.2.2.2.2
    obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hMO'.2.2
    have h2' := hTSR.2 t h2
    refine ⟨t, h1.trans hcur'.symm, h2', fun q asid h => ?_⟩
    have hv := hVC.at hCR'.2.2.1 ⟨t, 1, Or.inr ⟨h2', by decide⟩, rfl⟩ h (by simp)
    simp only [VCapOK] at hv
    exact (hv.2.2 trivial).1
  obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hF
  have hX' : XTopAt (L := L) AR (Z.mp G' p) s' a' σ' :=
    ⟨hF, ⟨hF.1.2.pl, hCR', hFI', hDR', by rw [hk]; exact hMO', IpcApart.of_topD hF.1.2 (by rw [hk]; exact hIA.dom),
      ScApart.of_top hF.1.2⟩, IpcRel.of hNt hEp (sched_sc hSch), hX.esa.mono hk (fun q y n hq => hsc ⟨q⟩ y n hq)⟩
  -- the restart's `JAtZ`
  obtain ⟨s1', σ1', x, -, hst1, -, hcurct, hσ1, -, -, -, hsts, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hcte : ct' = ct := P1.eq_of_bv (hct'.trans hcurct)
  subst ct'
  have e1 : s1 = s1' := by rw [hs1] at hsts; exact eq_of_ok_eq hsts
  have e2 : σ1 = σ1' := by
    have h := hst'.symm.trans hst1
    simp only [Prod.mk.injEq, and_true] at h
    have := Set.singleton_eq_singleton_iff.1 h
    simp only [Prod.mk.injEq, true_and] at this
    exact this
  subst e1 e2
  have hks1s : L.ksb s1 = L.ksb s := hks1.symm.trans hk
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots Z.th hPl s ct sched.TS_RESTART htcb J.kern.act
    rw [hs1, WP.spec_ok] at h; exact h
  have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrc1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false) := by
    rw [capAt_capV, hSS.capV hAs.isSlot, hsv]
  have hnull1 : capAt (L.mem s1) (cslotAddr (pd.bv, idxd)) = ok .Null := by
    rw [capAt_capV, hSS.capV hAd.isSlot, capV_of_capAt hnull]
  have hcdt1 : σ1.cdt = σ.cdt := by rw [hσ1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hnch1 : ¬ ∃ sl, σ1.cdt sl = some (pp.bv, idx) := by rw [hcdt1]; exact hnch
  have hDL1 : DestCap Z.th (L.mem s1) pd :=
    (DestCap.of_cnRef hCn ⟨y, hext.1 y hex1, capV_of_capAt hcy⟩).same hSS
  have hspec1 : ∀ o ko, σ1.kheap o = some ko → o.toNat < p.val ∨ p.val + 4096 ≤ o.toNat := by
    intro o ko ho
    rw [hσ1, stsAct_kheap, updK_kheap] at ho
    by_cases e : o = ct.bv
    · subst e
      have := hTh ct _ htcb
      simp only [objSize] at this
      rw [UScalar.bv_toNat]; omega
    · rw [Function.update_of_ne e] at ho
      exact hsp _ hsm p fi0 hsv hnd o ko ho
  obtain ⟨hpal, hpfit, hp0, -⟩ := hRg
  have Ad := addOKP_ksb (J.mpAddOK arI hcl hsm hsv hnd hpal hpfit hp0) hks1s
  have hcap1 : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → y ≠ cslotAddr (pd.bv, idxd) →
      capV (L.mem s') y = capV (L.mem s1) y := fun y hy h1 h2 => by rw [hcap y hy h1 h2, hSS.capV hy]
  exact ⟨_, _, Cs, Ac1, Lst1, D1, J1.mpStepJ hh hTh hHo Ad hspec1 hpp hidx hsrc1 hnch1 hpd hld hnull1 hDL1 hX'
    ⟨hks1, hcpu1, hW⟩ hzero hMs hkp hkh hcdt horig hsrc hdst hdstb hp0 hcap1 (hDI J.del) hU'⟩

/-- **The ASID control cap at `JAt`** (XTopJointEntry's dispatch): the
clean case proved (`decode_invocation_asid_controlJC`), the dirty one asked
(`JAsidCPath.dirty` [W]). -/
theorem decode_invocation_asid_controlJM (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : JMpExtra (L := L) Z s extra excaps)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef)
    (hdirty : ¬ (MpClean (L := L) Z H D s ∧ MpSpecClean (L := L) Z s σ) →
      XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .AsidControl
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases h : MpClean (L := L) Z H D s ∧ MpSpecClean (L := L) Z s σ
  · exact decode_invocation_asid_controlJC arI s ar σ J hni h.1 h.2 lbl slbl hlM length buf ct hct args hlen hargs
      extra excaps hext slot blk call don fp ci sl buffer
  · exact hdirty h

end

end

end Fl4Proofs.P3
