/-
P3 (DESIGN.md §9): **the Untyped cap's domain-schedule frame** (FL4's half,
`DecDomHyp`).

* `UtApart s p sb`: the one named premise, the untyped region misses the
  kernel-global block's first 13568 bytes; `JCovD.utApart` gives it for a cap
  of the MDB (`JCovD.ks`).
* `restart_ut`: the restart keeps the domain words, the base, the core, the
  debug-list head word and the slots.
* `reset_ut`: the reset (`reset_frame`, its preemption points by
  `pp_writes`) writes its region, the cap's slot and the preemption words,
  none a domain word nor the debug-list head word.
* `creation_dk4`: the creation's frame (`RetFrame`'s `WFrame`: slot words,
  the TCB loop's words, the PML4 window) misses the domain words, the window
  inside the untyped region.
* `retFrame_dk4`: the three together for `RetFrame`; `decDomHyp_untyped`:
  `DecDomHyp` for the Untyped cap, the window inside the cap's region by the
  decode's checks (`retype_region`).
-/
import Fl4Proofs.P3.DomCaps
import Fl4Proofs.P3.DomKeep
import Fl4Proofs.P3.UntypedFrame
import Fl4Proofs.P3.ScPlaceDead
import Fl4Proofs.P3.PPWrites
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **Untyped memory apart from the kernel-global block**: an untyped cap's
region misses the kernel-global area's first 13568 bytes. -/
def UtApart {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (s : S) (p sb : U64) : Prop :=
  p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `UtApart` from `JCovD`'s untyped-caps-miss-the-kernel-area field, for a
cap of the MDB. -/
theorem Sched.JCovD.utApart {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}
    (hJ : Sched.JCovD (L := L) th H G D Cs s) (hM : MdbLinks th (L.mem s) G) {x p sb fi : U64} {d : Bool}
    (hx : IsSlot th x) (hc : capAt (L.mem s) x = ok (.Untyped p sb fi d)) : UtApart (L := L) s p sb :=
  (hJ.ks x ((hM.members _).2 ⟨hx, _, hc, by simp⟩) p sb fi d (capV_of_capAt hc)).1

/-- A slot lies within an object of the typed heap. -/
theorem IsSlot.obj {th : TypedHeap} (hP : Placed th) {a : U64} (h : IsSlot th a) :
    ∃ q k, th q = some k ∧ q.val ≤ a.val ∧ a.val + 32 ≤ q.val + objSize k := by
  obtain ⟨q, i, hi, rfl⟩ := h
  obtain ⟨k, hk, hs⟩ := hi.size
  have hv := hi.val hP
  exact ⟨q, k, hk, by omega, by omega⟩

/-- A frame missing the domain schedule's words keeps them. -/
theorem DK4.of_wframe {s s' : S} {P : U64 → Prop} (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64)
    (ha : (L.ksb s).val % 8 = 0) (h : WFrame (L := L) s s' P)
    (hP : ∀ o ∈ domOffs0, ∀ w : U64, w.val = (L.ksb s).val + o.val → ¬ P w) : DK4 (L := L) s s' := by
  refine ⟨h.1, fun o ho => h.2.2 _ ?_ (hP o ho _ (dw_val hf ho))⟩
  have := domOffs0_lt ho
  unfold P1.Aligned; rw [dw_val hf ho]; omega

/-- A domain-schedule word is not in a range apart from the first 256 bytes. -/
theorem dom_not_in {kb lo hi : Nat} (h : hi ≤ kb ∨ kb + 256 ≤ lo) {o : U64} (ho : o ∈ domOffs0) {w : U64}
    (hw : w.val = kb + o.val) : ¬ (lo ≤ w.val ∧ w.val < hi) := by
  have := (domOffs0_lt ho).1; omega

/-- **The restart before the retype**: the domain words, the base, the core,
the debug-list head word and the slots kept. -/
theorem restart_ut {th : TypedHeap} (hP : Placed th) {s s0 : S} (hD : DomPlaced (L := L) th s) {ct : U64}
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hs0 : sched.set_thread_state st s ct sched.TS_RESTART = ok s0) {DW : U64} (hDWal : P1.Aligned DW)
    (hDWne : DW.val ≠ (stA ct).val ∧ DW.val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val) :
    DK4 (L := L) s s0 ∧ L.ksb s0 = L.ksb s ∧ L.cpu s0 = L.cpu s ∧ L.mem s0 DW = L.mem s DW ∧
      SlotsSame th (L.mem s) (L.mem s0) := by
  have h1 := sts_dk4 hP hD htcb sched.TS_RESTART
  rw [hs0, WP.spec_ok] at h1
  have h2 := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
  rw [hs0, WP.spec_ok] at h2
  have h3 := set_thread_state_cases (L := L) s ct sched.TS_RESTART
  rw [hs0, WP.spec_ok] at h3
  have htf := hP.fits ct _ htcb
  have hta := hP.align ct _ htcb
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at htf
  have h3328 : (3328#u64 : U64).val = 3328 := rfl
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by omega), h3328]
  have hsta : P1.Aligned (stA ct) := by unfold P1.Aligned; rw [hstv]; omega
  refine ⟨h1, ?_, ?_, ?_, h2⟩ <;> rcases h3 with rfl | rfl <;> try simp only [L.ksb_wr, L.cpu_wr]
  · exact L.mem_wr_ne hsta hDWal (Ne.symm hDWne.1)
  · rw [L.mem_wr_ne hD.actAl hDWal (Ne.symm hDWne.2), L.mem_wr_ne hsta hDWal (Ne.symm hDWne.1)]

theorem domOffs0_val {o : U64} (ho : o ∈ domOffs0) :
    o.val = 32 ∨ o.val = 192 ∨ o.val = 200 ∨ o.val = 208 ∨ o.val = 216 := by
  simp only [domOffs0, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp

/-- Node 0 placed, from the current core's node. -/
theorem nodePlaced_zero {s : S} (hN : P1.NodePlaced st ∅ s (L.cpu s)) : P1.NodePlaced st ∅ s 0#u64 := by
  have h1 := hN.align
  have h2 := hN.fits
  have e : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by simp [P1.LawfulStore.nodeBase]
  have e' : L.nodeBase s (L.cpu s) = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 := rfl
  rw [e'] at h1 h2
  refine ⟨?_, ?_, fun t ht => ht.elim⟩
  · rw [e]; omega
  · rw [e]; omega

/-- The preemption point's words, by value. -/
theorem ppw_val {s : S} (hN : P1.NodePlaced st ∅ s (L.cpu s)) {w : U64} (h : P1.PPW st s w) :
    w.val = (L.ksb s).val + 40 ∨ w.val = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + 48 ∨
      w.val = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + 40 := by
  have hf := hN.fits
  simp only [P1.LawfulStore.nodeBase] at hf
  rcases h with rfl | rfl | rfl
  · left; simp [core.num.U64.wrapping_add_val_eq, layout.ks.WORK_UNITS, U64.size_def, U64.numBits]; omega
  · right; left; unfold P1.LawfulStore.nodeA
    rw [P1.nodeAt_val hN (by simp [layout.node.CUR_TIME])]; simp [P1.LawfulStore.nodeBase, layout.node.CUR_TIME]
  · right; right; unfold P1.LawfulStore.nodeA
    rw [P1.nodeAt_val hN (by simp [layout.node.CONSUMED])]; simp [P1.LawfulStore.nodeBase, layout.node.CONSUMED]

/-- The debug-list head word, by value. -/
theorem dw_dbg_val {s : S} (hN : P1.NodePlaced st ∅ s (L.cpu s)) :
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = (L.ksb s).val + 13568 + 88 := by
  rw [P1.nodeAt_val (nodePlaced_zero hN) (by simp [layout.node.DEBUG_TCBS])]
  simp [P1.LawfulStore.nodeBase, layout.node.DEBUG_TCBS]

/-- **The reset's frame** (`reset_frame`, its preemption points by
`pp_writes`): the domain words, the base, the core and the debug-list head
word kept. -/
theorem reset_ut {A' : Type} (arI : machine.Arch A') (hA : P0.ArchTotal arI) {th : TypedHeap} (hP : Placed th)
    {s0 : S} (a : A') {x p sb fi : U64} {dev : Bool} (hx : IsSlot th x)
    (hcap : capAt (L.mem s0) x = ok (.Untyped p sb fi dev)) (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val)
    (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hK : KsbOK (L := L) th s0) (hN : P1.NodePlaced st ∅ s0 (L.cpu s0)) (hks : UtApart (L := L) s0 p sb)
    (hDWobj : ¬ (x.val ≤ (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val < x.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val)) :
    untyped.reset_untyped st arI s0 a x ⦃ r => DK4 (L := L) s0 r.2.1 ∧ L.ksb r.2.1 = L.ksb s0 ∧
      L.cpu r.2.1 = L.cpu s0 ∧
      L.mem r.2.1 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) = L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) ⦄ := by
  have hxa := hx.align hP
  have hxf := hx.fit hP
  have hp8 : p.val % 8 = 0 := by
    have := Nat.mod_mod_of_dvd p.val (Nat.pow_dvd_pow 2 (show 3 ≤ sb.val by omega))
    rw [hpal] at this; simpa using this.symm
  refine WP.spec_mono (reset_frame arI s0 a x hcap hp8 hsb4 hpfit hfi (by omega) (by omega)
    (Q := fun s1 => L.ksb s1 = L.ksb s0 ∧ L.cpu s1 = L.cpu s0) ⟨?_, ?_⟩ ⟨rfl, rfl⟩ (PW := P1.PPW st s0) ?_) ?_
  · intro s1 a n _ _ _ _ hq; simpa using hq
  · intro s1 c hq
    exact WP.spec_mono (set_cap_frame s1 x c (by omega) (by omega)) fun s' h => ⟨h.1.trans hq.1, h.2.1.trans hq.2⟩
  · intro s1 a1 hq
    have hN1 : P1.NodePlaced st ∅ s1 (L.cpu s1) := by rw [hq.2]; exact hN.ksb hq.1
    exact WP.spec_mono (pp_writes hA s1 a1 hN1) fun r h =>
      ⟨h.mono fun b hb => P1.PPW.of hq.1 hq.2 hb, h.1.trans hq.1, h.2.1.trans hq.2⟩
  rintro r ⟨hW, hq1, hq2⟩
  have hkf := hK.fits
  have hka := hK.align
  have hdv := dw_dbg_val hN
  obtain ⟨q, k, hq, hq1', hq2'⟩ := IsSlot.obj hP hx
  have hqa := hK.apart q k hq
  have hnot : ∀ w : U64, (w.val < (L.ksb s0).val + 256 ∧ w.val ≠ (L.ksb s0).val + 40) ∨
      w.val = (L.ksb s0).val + 13568 + 88 → (w.val < (L.ksb s0).val + 256 → (L.ksb s0).val ≤ w.val) →
      (w.val = (L.ksb s0).val + 13568 + 88 → ¬ (x.val ≤ w.val ∧ w.val < x.val + 32) ∧
        ¬ (p.val ≤ w.val ∧ w.val < p.val + 2 ^ sb.val)) →
      ¬ ResetW p sb x (P1.PPW st s0) w := by
    intro w hw hlo hd
    rintro (hr | hr | hr)
    · rcases hw with ⟨h1, -⟩ | h1
      · have := hlo h1; unfold UtApart at hks; omega
      · exact (hd h1).2 hr
    · rcases hw with ⟨h1, -⟩ | h1
      · have := hlo h1; omega
      · exact (hd h1).1 ⟨hr.1, by omega⟩
    · rcases ppw_val hN hr with e | e | e
      · rcases hw with ⟨h1, h2⟩ | h1 <;> omega
      · rcases hw with ⟨h1, h2⟩ | h1 <;> omega
      · rcases hw with ⟨h1, h2⟩ | h1 <;> omega
  refine ⟨DK4.of_wframe hkf hka hW fun o ho w hw => hnot w ?_ (fun _ => by omega) (fun h => by
      have := (domOffs0_lt ho).1; omega), hq1, hq2, hW.2.2 _ ?_ (hnot _ (Or.inr hdv) (fun h => by omega)
      fun _ => ⟨hDWobj, hDWreg⟩)⟩
  · left; have := (domOffs0_lt ho).1
    rcases domOffs0_val ho with e | e | e | e | e <;> constructor <;> omega
  · unfold P1.Aligned; rw [hdv]; omega

/-- **The creation's frame keeps the domain words**: the slot words, the
window (within the untyped region), the debug-list head word and the old
head's `debug_prev` word all lie apart from the first 256 bytes. -/
theorem creation_dk4 {th thR : TypedHeap} (hP : Placed th) {sR s' : S} {A k win : Nat} {T pml4 : Prop}
    (hW : WFrame (L := L) sR s' (fun v => ((T ∧ TcbLoopW thR A win (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
      (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan thR v) ∨
      (pml4 ∧ A ≤ v.val ∧ v.val < A + win * k)))
    (hK : KsbOK (L := L) th sR) (hN : P1.NodePlaced st ∅ sR (L.cpu sR)) (hsl : ∀ a, IsSlot thR a → IsSlot th a)
    {p sb : U64} (hks : UtApart (L := L) sR p sb) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hA1 : p.val ≤ A)
    (hA2 : A + win * k ≤ p.val + 2 ^ sb.val) (hTk : T → k = 4096)
    (hh0 : L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      th (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) = some .tcb) :
    DK4 (L := L) sR s' := by
  have hkf := hK.fits
  have hka := hK.align
  have hdv := dw_dbg_val hN
  unfold UtApart at hks
  refine DK4.of_wframe hkf hka hW fun o ho w hw => ?_
  have ho' := (domOffs0_lt ho).1
  have slotNot : ∀ a, IsSlot th a → ¬ (a.val ≤ w.val ∧ w.val < a.val + 32) := by
    intro a ha ⟨h1, h2⟩
    obtain ⟨q, kq, hq, hq1, hq2⟩ := IsSlot.obj hP ha
    rcases hK.apart q kq hq with h | h <;> omega
  have spanNot : ¬ SlotSpan thR w := fun ⟨a, ha, h1, h2⟩ => slotNot a (hsl a ha) ⟨h1, h2⟩
  rintro ((⟨hT, hL⟩ | hs) | ⟨-, h1, h2⟩)
  · rcases hL with hs | ⟨j, hj, hI⟩ | e | ⟨hne, he⟩
    · exact spanNot hs
    · have hk := hTk hT
      subst hk
      have hjw : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
      have hjv : (⟨BitVec.ofNat 64 (A + j * 4096)⟩ : U64).val = A + j * 4096 := by
        show (BitVec.ofNat 64 (A + j * 4096)).toNat = _; simp; omega
      obtain ⟨i1, i2, -⟩ := hI
      rw [hjv] at i1 i2
      omega
    · rw [e] at hw; omega
    · rcases hh0 with h0 | h0
      · exact hne h0
      · have e4 : objSize ObjKind.tcb = 4096 := rfl
        rcases hK.apart _ _ h0 with h | h <;> (try rw [e4] at h) <;> omega
  · exact spanNot hs
  · omega

/-- **`RetFrame` keeps the domain words** (module docstring): the restart
(`restart_ut`), the reset (`reset_ut`) and the creation (`creation_dk4`). -/
theorem retFrame_dk4 {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
    {th th' : TypedHeap} {G : MdbGhost} (hP : Placed th) {s : S} {x : U64} {A k win A0 k0 w0 us : Nat} {pml4 T Z : Prop}
    {tK : Nat → Prop} {cj : Nat → capability.Cap} {dv : Bool} {dslot : Nat → U64} {RB : Prop}
    {res : core.result.Result Unit error.Exc × S × A'}
    (hRF : RetFrame (L := L) arI ar th th' G s x A k win A0 k0 w0 pml4 T Z tK us cj dv dslot RB res)
    (hD : DomPlaced (L := L) th s) (hN : P1.NodePlaced st ∅ s (L.cpu s))
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {p sb fi : U64} {dev : Bool} (hx : IsSlot th x) (hcap : capAt (L.mem s) x = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hfi : fi.val ≤ 2 ^ sb.val) (hks : UtApart (L := L) s p sb)
    (hwin : p.val ≤ A0 ∧ A0 + w0 * k0 ≤ p.val + 2 ^ sb.val) (hTk : T → k0 = 4096)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb) :
    DK4 (L := L) s res.2.1 := by
  obtain ⟨ct', s0, hct', hs0, hc⟩ := hRF
  rw [hct] at hct'
  obtain rfl : ct' = ct := (ok_inj hct').symm
  obtain ⟨d1, k1, c1, m1, hS1⟩ := restart_ut hP hD htcb hact hs0 hDWal hDWne
  have hcap0 : capAt (L.mem s0) x = ok (.Untyped p sb fi dev) := by rw [hS1.capAt hx]; exact hcap
  have hK0 : KsbOK (L := L) th s0 := hD.toK.same k1
  have hN0 : P1.NodePlaced st ∅ s0 (L.cpu s0) := by rw [c1]; exact hN.ksb k1
  have hks0 : UtApart (L := L) s0 p sb := by unfold UtApart; rw [k1]; exact hks
  have eDW : L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb k1 _ _
  have hR := reset_ut arI hA hP ar hx hcap0 hpal hsb4 hpfit hfi hK0 hN0 hks0 (by rw [eDW]; exact hDWobj x hx)
    (by rw [eDW]; exact hDWreg)
  rcases hc with ⟨-, hres⟩ | ⟨-, ⟨rfl, rfl, rfl, -⟩, sR, thR, lo, hi, hcase, -, -, -, hsl, -, -, hWF, -, -⟩
  · rw [hres, WP.spec_ok] at hR; exact d1.trans hR.1
  have hRS : DK4 (L := L) s0 sR ∧ L.ksb sR = L.ksb s0 ∧ L.cpu sR = L.cpu s0 ∧
      L.mem sR (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) = L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rcases hcase with ⟨rfl, -, -, -⟩ | ⟨a1, -, -, -, -, hr, -⟩
    · exact ⟨DK4.refl _, rfl, rfl, rfl⟩
    · rw [hr, WP.spec_ok] at hR; exact hR
  obtain ⟨d2, k2, c2, m2⟩ := hRS
  have eDWR : L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb (k2.trans k1) _ _
  refine d1.trans (d2.trans (creation_dk4 hP hWF (hK0.same k2) (by rw [c2]; exact hN0.ksb k2) hsl
    (by unfold UtApart; rw [k2]; exact hks0) hpfit hwin.1 hwin.2 hTk ?_))
  rw [eDWR, ← eDW, m2, eDW, m1]; exact hhead

/-- **FL4's half of the Untyped cap's `DomFrame`**: `decode`'s errors leave
the state; a retype (restart, reset, creation) keeps the domain words by
`retFrame_dk4`, its window inside the cap's region by the decode's checks
(`retype_region`). Beyond `untyped_retype_refines_fl4P`'s hypotheses: the
domain schedule's placement (`DomPlaced`), the current core's node placed,
total arch operations (the reset's preemption points), and the one named
premise `UtApart`: the cap's region misses the kernel-global block
(`JCovD.utApart`). -/
theorem decDomHyp_untyped [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (th : TypedHeap) (s : S) (ar : A')
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hnt : ∀ x, args.head? = some x → x.val ≤ 13)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val))
    (hA : P0.ArchTotal arI) (hD : DomPlaced (L := L) th s) (hNP : P1.NodePlaced st ∅ s (L.cpu s))
    (hks : UtApart (L := L) s p sb) (blk call don fp : Bool) :
    DecDomHyp (L := L) arI s ar lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) blk call don fp buf extra := by
  apply decDomHyp_of_dk4
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hhd : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb := hhead.imp id And.left
  refine WP.spec_mono (untyped_decode_refines_fl4 arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct
    args hlen hargs (fun x hx => Or.inl (by have := hnt x hx; omega))
    _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan (fun _ res => DK4 (L := L) s res.2.1) ?_) ?_
  · intro nt us dest off win t r reset fiv hnt0 hctx
    have hn := hnt nt hnt0
    have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hctx.ty us.val).2.1
    have hsb : sb.val < 64 := hctx.sizeBits
    have hz : zOf nt.val us.val < 64 := by have := hctx.size.2.1; omega
    have hF : fiv.val ≤ 2 ^ sb.val := by
      rw [hctx.fidx]; split
      · simp
      · exact hfi
    obtain ⟨hA1, -, hA3, -⟩ := retype_region p fiv sb.val _ win.val hsb hz hpal hpfit hF hctx.window.1 hctx.memory
    have hlen' : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
    have hTk : t = .tcbObject → 2 ^ Fl4Spec.fl4ObjBitsApi t us.val = 4096 := by
      rintro rfl; rfl
    have key : ∀ res, RetPostN (L := L) th (L.mem s) G σ arI ar s Fl4Spec.fl4ObjBitsApi (L.ksb s)
        (.retype (pp.bv, idx) reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res → DK4 (L := L) s res.2.1 := by
      intro res hq
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRF⟩ := hq
      refine retFrame_dk4 arI ar hA hP hRF.1 hD hNP hct htcb hact hAs.isSlot hcap hpal hsb4 hpfit hfi hks
        ⟨by omega, by rw [hlen', hb]; omega⟩ hTk hDWal hDWobj hDWreg hDWne hhd
    by_cases h8 : nt.val = 8
    · exact WP.spec_mono (retype_cont_pml4N arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx
        hcap hpal hpfit hfi hhigh hactZ hfree hzero hsb4 hN hns hrcb hppS hPP hRst Fl4Spec.fl4ObjBitsApi nt us dest off
        win t r reset fiv h8 hb hDWal hDWobj hDWreg hDWne hhead hgpm hga hgf hgreg hctx) key
    · exact WP.spec_mono (retype_cont_allN arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx
        hcap hpal hpfit hfi hhigh hactZ hfree hzero hsb4 hN hns hrcb hppS hPP hRst Fl4Spec.fl4ObjBitsApi nt us dest off
        win t r reset fiv ⟨hn, h8⟩ hb hDWal hDWobj hDWreg hDWne hhead hctx) key
  · rintro res (⟨e, e', rfl, -, -⟩ | ⟨-, -, h⟩)
    · exact DK4.refl _
    · exact h

end

end

end Fl4Proofs.P3
