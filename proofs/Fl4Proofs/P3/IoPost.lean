/-
P3 (DESIGN.md §9), IO ports: **`post_cap_deletion` of an IO port cap**
(`PostIoHyp` discharged): FL4 clears the cap's ports in the bitmap
(`free_ioports`, words outside every object), the spec frees them
(`free_ioport_range`); the CSpace relation is kept, and so is `IoRel`
(`post_io_rel`, for a cap with `first ≤ last`). With the IRQ handler case
(DelPost), `PostDelHyp` holds (`postDelHyp_full`).
-/
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.DelPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem pattern_total (st en : U64) : ∃ P, ioport.pattern st en = ok P := by
  unfold ioport.pattern
  simp only [lift, bind_ok]
  split
  · exact ⟨_, rfl⟩
  · have h1 : (core.num.U64.wrapping_sub en st &&& 63#u64).val < 64 := by rw [and63_val]; omega
    obtain ⟨z, hz, -⟩ := spec_exists (U64.ShiftLeft_spec (x := 1#u64)
      (y := core.num.U64.wrapping_sub en st &&& 63#u64) h1)
    rw [hz]; simp only [bind_ok]
    have h2 : (st &&& 63#u64).val < 64 := by rw [and63_val]; omega
    obtain ⟨P, hP, -⟩ := spec_exists (U64.ShiftLeft_spec (x := core.num.U64.wrapping_sub z 1#u64)
      (y := st &&& 63#u64) h2)
    exact ⟨P, hP⟩

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_mask_loop_ge (s : S) (set : Bool) (hw w : U64) (h : hw.val ≤ w.val) :
    ioport.set_mask_loop st s set hw w = ok s := by
  have hn : ¬ (w < hw) := by scalar_tac
  unfold ioport.set_mask_loop
  rw [loop]
  simp only [ioport.set_mask_loop.body, hn, ↓reduceIte, bind_ok]

/-- `set_mask` writes bitmap words only, for any two ports. -/
theorem set_mask_frame {kb : U64} (hL : IoLayout th kb) (s : S) (hk : L.ksb s = kb) (low high : U64)
    (hl : low.val < 65536) (hh : high.val < 65536) (set : Bool) :
    ioport.set_mask st s low high set ⦃ s' => ∃ F, IoW (L := L) kb s s' F ⦄ := by
  unfold ioport.set_mask
  obtain ⟨lw, hlw, hlwv⟩ := shr6_spec low
  obtain ⟨hw, hhw, hhwv⟩ := shr6_spec high
  rw [hlw, hhw]; simp only [lift, bind_ok]
  have hlw1 : lw.val < 1024 := by omega
  have hhw1 : hw.val < 1024 := by omega
  split
  · obtain ⟨P, hP⟩ := pattern_total (low &&& 63#u64) (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64)
    rw [hP]; simp only [bind_ok]
    exact WP.spec_mono (apply_ioW hL s hk hlw1 P set) (fun s' h => ⟨_, h⟩)
  · obtain ⟨P1, hP1⟩ := pattern_total (low &&& 63#u64) 64#u64
    rw [hP1]; simp only [bind_ok]
    refine WP.spec_bind (apply_ioW hL s hk hlw1 P1 set) ?_
    intro s1 hW1
    obtain ⟨w0, hw0, hw0v⟩ := spec_exists (U64.add_spec (x := lw) (y := 1#u64) (by scalar_tac))
    rw [hw0]; simp only [bind_ok]
    obtain ⟨P2, hP2⟩ := pattern_total 0#u64 (core.num.U64.wrapping_add (high &&& 63#u64) 1#u64)
    by_cases hle : w0.val ≤ hw.val
    · refine WP.spec_bind (set_mask_loop_spec hL s1 (hW1.1.trans hk) set hw w0 hhw1 hle) ?_
      intro s2 hW2
      rw [hP2]; simp only [bind_ok]
      refine WP.spec_mono (apply_ioW hL s2 (hW2.1.trans (hW1.1.trans hk)) hhw1 P2 set) ?_
      intro s' hW3
      exact ⟨_, (hW1.trans hW2 hL.fit).trans hW3 hL.fit⟩
    · rw [set_mask_loop_ge s1 set hw w0 (by omega)]; simp only [bind_ok]
      rw [hP2]; simp only [bind_ok]
      refine WP.spec_mono (apply_ioW hL s1 (hW1.1.trans hk) hhw1 P2 set) ?_
      intro s' hW3
      exact ⟨_, hW1.trans hW3 hL.fit⟩

/-- Writes to bitmap words only keep the slot words. -/
theorem io_frame_slotsSame (hP : Placed th) {kb : U64} (hL : IoLayout th kb) {s s' : S}
    (h : ∀ b, P1.Aligned b → (∀ w : U64, w.val < 1024 → b ≠ ioA kb w) → L.mem s' b = L.mem s b) :
    SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have hk : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
    intro k hk
    refine h _ (slot_word_aligned hP ha hk) (fun w hw e => ?_)
    obtain ⟨p, kd, hkd, h1, h2, -⟩ := slot_in_object hP ha
    have := (hL.out w hw).2 p kd hkd
    have hv := slot_word_val hP ha hk
    have := hk.lt
    rw [e] at hv
    omega
  refine ⟨?_, hk _ off8, hk _ off16, hk _ off24⟩
  have := hk _ off0
  rwa [wordOf_zero] at this

/-- Bitmap writes keep the slot words. -/
theorem IoW.slotsSame (hP : Placed th) {kb : U64} (hL : IoLayout th kb) {s s' : S} {F : Nat → U64 → U64}
    (h : IoW (L := L) kb s s' F) : SlotsSame th (L.mem s) (L.mem s') :=
  io_frame_slotsSame hP hL h.2.1

end

/-! ## The spec's `free_ioport_range` -/

section
open Fl4Spec

/-- The spec's `set_ioport_mask f l v`. -/
def ioMaskSt (f l : IoPort) (v : Bool) (σ : State Unit) : State Unit :=
  { σ with archState := { σ.archState with
      x64AllocatedIoPorts := fun p => if p ≥ f ∧ p ≤ l then v else σ.archState.x64AllocatedIoPorts p } }

theorem setIoportMask_mem (f l : IoPort) (v : Bool) (σ : State Unit) :
    ((), ioMaskSt f l v σ) ∈ (setIoportMask (Z := Unit) f l v σ).1 := by
  unfold setIoportMask
  refine mem_bind_nd (x := (σ.archState.x64AllocatedIoPorts, σ)) rfl ?_
  exact mem_bind_nd (x := (_, σ)) rfl rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`PostIoHyp` holds**, the bitmap words being outside the objects. -/
theorem postIoHyp_of (th : TypedHeap) (hP : Placed th) (hio : ∀ s : S, IoLayout th (L.ksb s)) :
    PostIoHyp (L := L) arI th := by
  intro s a σ G f l owner hDS hwf
  obtain ⟨hf, hl⟩ := hwf
  unfold objects.post_cap_deletion ioport.free_ioports
  simp only
  refine WP.spec_bind (set_mask_frame (hio s) s rfl f l hf hl false) ?_
  rintro s1 ⟨F, hW⟩
  rw [WP.spec_ok]
  have hS := hW.slotsSame hP (hio s)
  refine ⟨hS, ioMaskSt (BitVec.ofNat 16 f.val) (BitVec.ofNat 16 l.val) false σ, ?_, ?_⟩
  · exact setIoportMask_mem _ _ _ _
  · exact crel_same hDS.1 hS rfl rfl rfl

/-- **`PostDelHyp` holds**, from the IRQ handler and IO port cases. -/
theorem postDelHyp_full (th : TypedHeap) (hP : Placed th)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hout : ∀ (s : S) (irq : U64), interrupt.state_off irq ⦃ off =>
      OutsideObjects th (core.num.U64.wrapping_add (L.ksb s) off) ⦄)
    (hio : ∀ s : S, IoLayout th (L.ksb s)) : PostDelHyp (L := L) arI th :=
  postDelHyp_of arI th hP hmask hout (postIoHyp_of arI th hP hio)

/-- `IoRel` after `set_mask low high set` and the spec's `set_ioport_mask`. -/
theorem IoRel.mask {kb : U64} {s s' : S} {σ : Fl4Spec.State Unit} (hI : IoRel (L.mem s) kb σ)
    {low high : U64} (hh : high.val < 65536) (hlh : low.val ≤ high.val) {set : Bool}
    (h : MaskPost (L := L) kb low high set s s') :
    IoRel (L.mem s') kb (ioMaskSt (BitVec.ofNat 16 low.val) (BitVec.ofNat 16 high.val) set σ) := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hb := h.2.2 (wI p) hw (p % 64) (by omega)
  rw [wI_val hp] at hb
  unfold bitOf
  rw [hb, show 64 * (p / 64) + p % 64 = p by omega]
  simp only [ioMaskSt]
  have e1 : (BitVec.ofNat 16 p ≥ BitVec.ofNat 16 low.val) ↔ low.val ≤ p := by
    rw [GE.ge, BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (by omega)]
  have e2 : (BitVec.ofNat 16 p ≤ BitVec.ofNat 16 high.val) ↔ p ≤ high.val := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hh]
  by_cases hc : low.val ≤ p ∧ p ≤ high.val
  · rw [if_pos (⟨e1.2 hc.1, e2.2 hc.2⟩ : _ ∧ _), if_pos hc]
  · rw [if_neg (fun h' => hc ⟨e1.1 h'.1, e2.1 h'.2⟩), if_neg hc]
    exact hI p hp

end

end

end Fl4Proofs.P3
