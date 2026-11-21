/-
P3 (DESIGN.md §9), VSpace: **the slot footprint of the VSpace
invocations**, low in the import order so that their refinements can
export it.

* `SlotFoot th m m' x`: every slot's link and bit words kept, and the cap
  words of every slot but `x` (the invoked cap's own slot, which `Map` and
  `Unmap` rewrite with a remapped cap). Built from `set_thread_state`
  (`SlotsSame`), one `set_cap` of `x`, and writes outside the objects.
* `KFoot σ σ'`: the spec's CDT and original bits kept, and its heap changed
  only at arch objects and, at the same size, CNodes and TCBs.
The CSpace relations, `MdbInv` and `FinInv` follow (VsMdb: `Recap.carry`).
-/
import Fl4Proofs.P3.VsAssign
import Fl4Proofs.P3.StateFrame
import Fl4Proofs.P3.MdbSem
import Fl4Proofs.P3.FinBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- FL4's memory across a VSpace invocation at the slots (see the module
docstring). -/
def SlotFoot (th : TypedHeap) (m m' : U64 → U64) (x : U64) : Prop :=
  ∀ y, IsSlot th y → m' (wordOf y 16#u64) = m (wordOf y 16#u64) ∧ m' (wordOf y 24#u64) = m (wordOf y 24#u64) ∧
    (y ≠ x → m' y = m y ∧ m' (wordOf y 8#u64) = m (wordOf y 8#u64))

/-- **The VT-x flag of a cap** (g2a, `NativeCap c ↔ vtF c = false`): a VCPU
or EPT cap, a frame cap mapped into an EPT (`e && m`, the EPT flag first so a
frame cap with the flag clear computes to `false` whatever its mapping), an
IO-port cap owned by a VCPU. -/
def vtF : capability.Cap → Bool
  | .Vcpu _ => true
  | .Ept .. => true
  | .Frame _ _ _ _ m e _ _ => e && m
  | .IoPort _ _ o => decide (o ≠ 0#u64)
  | _ => false

/-- Two caps alike for the MDB tests and finality: the same shape, object
key and badge (a remapped frame or table cap), and the same VT-x flag
(`vtF`, g2a: a remap keeps a native cap native). -/
def MdbLike (c' c : capability.Cap) : Prop :=
  shape c' = shape c ∧ okey c' = okey c ∧ badgeF c' = badgeF c ∧ vtF c' = vtF c

/-- The physical address of `p` in mask `m` (`paddr p & m = paddr p`). -/
def PaM (p m : U64) : Prop :=
  (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& m) = core.num.U64.wrapping_sub p layout.PPTR_BASE

/-- A frame size's address mask. -/
def frameMaskOf : capability.FrameSize → U64
  | .Small => 4503599627366400#u64
  | .Large => 4503599625273344#u64
  | .Huge => 4503598553628672#u64

/-- **A user virtual address**: at most FL4's `USER_TOP` (`0x7fff_ffff_ffff`;
l4v `wellformed_mapdata`'s `vref < pptr_base`, user half: PML4 index < 256). -/
def UserV (v : U64) : Prop := v.val ≤ 140737488355327

/-- **A VSpace cap well placed** in the ghost sets (see the module
docstring); the other caps impose nothing. A mapped PT/PD/PDPT/frame cap's
vaddr is a user address (`UserV`, l4v `wellformed_mapdata`). -/
def VCapOK (P L4 L3 L2 L1 : Set U64) : capability.Cap → Prop
  | .PageTable p mp a v => p ∈ L1 ∧ PaM p 4503599627366400#u64 ∧
      (mp = true → a ≠ 0#u64 ∧ v.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0) ∧
      (mp = true → UserV v)
  | .PageDirectory p mp a v => p ∈ L2 ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64) ∧
      (mp = true → UserV v)
  | .Pdpt p mp a v => p ∈ L3 ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64) ∧ (mp = true → UserV v)
  | .Pml4 p mp a => p ∈ L4 ∧ p ≠ 0#u64 ∧ (mp = true → a ≠ 0#u64 ∧ a.val < 2 ^ 20)
  | .Frame p sz _ _ m _ a v => (m = true → a ≠ 0#u64) ∧ PaM p (frameMaskOf sz) ∧ (m = true → UserV v)
  | .AsidPool p b => (p ∈ P ∧ p ≠ 0#u64) ∧ b.val % 512 = 0 ∧ b.val < 2 ^ 20
  | _ => True

/-- **A cap of the native scope** (G2 `nativeScopeX`, [S] VT-x out of scope):
no VCPU or EPT cap, no frame cap mapped into an EPT, no IO-port cap owned by
a VCPU. Every native step makes only such caps (a retype of a native type, an
IO-port control issue with no owner, a frame map into a native VSpace, the
copies, mints, moves and derivations of a native cap); only the VT-x
invocations (`JVtxScope`) make the others. -/
def NativeCap : capability.Cap → Prop
  | .Vcpu _ => False
  | .Ept .. => False
  | .Frame _ _ _ _ m e _ _ => ¬ (m = true ∧ e = true)
  | .IoPort _ _ o => o = 0#u64
  | _ => True

theorem NativeCap.null : NativeCap .Null := trivial

theorem nativeCap_iff (c : capability.Cap) : NativeCap c ↔ vtF c = false := by
  cases c with
  | Frame p sz r d m e a v => cases m <;> cases e <;> simp [NativeCap, vtF]
  | IoPort f l o => simp only [NativeCap, vtF, decide_eq_false_iff_not, not_not]
  | _ => simp [NativeCap, vtF]

/-- Nativeness is read off the VT-x flag (`MdbLike`'s last part). -/
theorem NativeCap.of_vtF {c c' : capability.Cap} (h : NativeCap c) (e : vtF c' = vtF c) : NativeCap c' :=
  (nativeCap_iff c').2 (e.trans ((nativeCap_iff c).1 h))

/-- **A remapped cap**: alike for the MDB, and well placed when the old one
was (the remaps' posts; `VsCapsIn.recap`). -/
def VsLike (c' c : capability.Cap) : Prop :=
  MdbLike c' c ∧ ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 c → VCapOK P L4 L3 L2 L1 c'

/-- The spec's state across a VSpace invocation (see the module docstring). -/
def KFoot (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap ∧
    (∀ o, σ'.kheap o ≠ σ.kheap o →
      (∃ ao ao', σ.kheap o = some (.archObj ao) ∧ σ'.kheap o = some (.archObj ao')) ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ Fl4Spec.wellFormedCnodeN r cs ∧
        σ'.kheap o = some (.cnode r cs')) ∨
      (∃ t t', σ.kheap o = some (.tcb t) ∧ σ'.kheap o = some (.tcb t'))) ∧
    σ'.curThread = σ.curThread

section
variable {th : TypedHeap}

theorem SlotFoot.refl (m : U64 → U64) (x : U64) : SlotFoot th m m x := fun _ _ => ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem SlotFoot.trans {m1 m2 m3 : U64 → U64} {x : U64} (h1 : SlotFoot th m1 m2 x) (h2 : SlotFoot th m2 m3 x) :
    SlotFoot th m1 m3 x := fun y hy =>
  ⟨(h2 y hy).1.trans (h1 y hy).1, (h2 y hy).2.1.trans (h1 y hy).2.1, fun hne =>
    ⟨((h2 y hy).2.2 hne).1.trans ((h1 y hy).2.2 hne).1, ((h2 y hy).2.2 hne).2.trans ((h1 y hy).2.2 hne).2⟩⟩

theorem SlotFoot.of_same {m m' : U64 → U64} (h : SlotsSame th m m') (x : U64) : SlotFoot th m m' x :=
  fun y hy => ⟨(h y hy).2.2.1, (h y hy).2.2.2, fun _ => ⟨(h y hy).1, (h y hy).2.1⟩⟩

/-- A write of `x`'s cap words only. -/
theorem SlotFoot.of_cap (hP : Placed th) {m m' : U64 → U64} {x : U64} (hx : IsSlot th x)
    (h : ∀ b, P1.Aligned b → b.val ≠ x.val → b.val ≠ x.val + 8 → m' b = m b) : SlotFoot th m m' x := by
  intro y hy
  have h16 := slot_word_val hP hy (k := 16#u64) (Or.inr (Or.inr (Or.inl rfl)))
  have h24 := slot_word_val hP hy (k := 24#u64) (Or.inr (Or.inr (Or.inr rfl)))
  have h8 := slot_word_val hP hy (k := 8#u64) (Or.inr (Or.inl rfl))
  have a16 := slot_word_aligned hP hy (k := 16#u64) (Or.inr (Or.inr (Or.inl rfl)))
  have a24 := slot_word_aligned hP hy (k := 24#u64) (Or.inr (Or.inr (Or.inr rfl)))
  have a8 := slot_word_aligned hP hy (k := 8#u64) (Or.inr (Or.inl rfl))
  have a0 : P1.Aligned y := by have := slot_word_aligned hP hy (k := 0#u64) (Or.inl rfl); rwa [wordOf_zero] at this
  have hap : ∀ (hne : y ≠ x), y.val + 32 ≤ x.val ∨ x.val + 32 ≤ y.val := fun hne => hy.apart hP hx hne
  have hfx := hx.fit hP
  have hfy := hy.fit hP
  by_cases e : y = x
  · subst e
    refine ⟨h _ a16 (by rw [h16]; simp) (by rw [h16]; simp), h _ a24 (by rw [h24]; simp) (by rw [h24]; simp),
      fun hne => absurd rfl hne⟩
  · have := hap e
    refine ⟨h _ a16 (by rw [h16]; simp; omega) (by rw [h16]; simp; omega),
      h _ a24 (by rw [h24]; simp; omega) (by rw [h24]; simp; omega),
      fun _ => ⟨h _ a0 (by omega) (by omega), h _ a8 (by rw [h8]; simp; omega) (by rw [h8]; simp; omega)⟩⟩

/-- Writes outside the objects (the memory kept inside every object). -/
theorem SlotFoot.of_out (hP : Placed th) {m m' : U64 → U64} (x : U64)
    (h : ∀ b, P1.Aligned b → (∃ p k, th p = some k ∧ p.val ≤ b.val ∧ b.val < p.val + objSize k) → m' b = m b) :
    SlotFoot th m m' x := by
  have key : ∀ y, IsSlot th y → ∀ k : U64, Off k → m' (wordOf y k) = m (wordOf y k) := by
    intro y hy k hk
    refine h _ (slot_word_aligned hP hy hk) ?_
    obtain ⟨o, kk, hkk, h1, h2, -⟩ := slot_in_object hP hy
    rw [slot_word_val hP hy hk]
    have := hk.lt
    exact ⟨o, kk, hkk, by omega, by omega⟩
  intro y hy
  refine ⟨key y hy _ (Or.inr (Or.inr (Or.inl rfl))), key y hy _ (Or.inr (Or.inr (Or.inr rfl))),
    fun _ => ⟨?_, key y hy _ (Or.inr (Or.inl rfl))⟩⟩
  have := key y hy _ (Or.inl rfl); rwa [wordOf_zero] at this

/-- One write outside the objects. -/
theorem SlotFoot.wr_out (hP : Placed th) {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (s : S)
    {b v : U64} (hb : OutsideObjects th b) (x : U64) : SlotFoot th (L.mem s) (L.mem (L.wr s b v)) x :=
  SlotFoot.of_out hP x (fun c hc ⟨p, k, hk, h1, h2⟩ => L.mem_wr_ne hb.1 hc (fun e => hb.2 p k hk ⟨by
    rw [e]; exact h1, by rw [e]; exact h2⟩))




/-- Writes outside the objects, as `WritesIn`. -/
theorem SlotFoot.of_writes {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (hP : Placed th) {s s' : S}
    {W : U64 → Prop} (hW : WritesIn st s s' W) (hWo : ∀ b, W b → OutsideObjects th b) (x : U64) :
    SlotFoot th (L.mem s) (L.mem s') x :=
  SlotFoot.of_out hP x (fun b hb ⟨p, k, hk, h1, h2⟩ => hW.2.2 b hb (fun hw => (hWo b hw).2 p k hk ⟨h1, h2⟩))

/-- A write outside the objects keeps every slot's cap. -/
theorem capV_wr_out {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (hP : Placed th) {x : U64}
    (hx : IsSlot th x) (s : S) {b v : U64} (hb : OutsideObjects th b) :
    capV (L.mem (L.wr s b v)) x = capV (L.mem s) x := by
  have hne : x ≠ core.num.U64.wrapping_add x 1#u64 := by
    intro e; have := congrArg UScalar.val e
    have hf := hx.fit hP
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this; omega
  have h := SlotFoot.wr_out (L := L) hP s (v := v) hb (core.num.U64.wrapping_add x 1#u64) x hx
  unfold capV; rw [(h.2.2 hne).1, (h.2.2 hne).2]

/-- **`set_cap` of slot `x`**: the footprint, and the cap written. -/
theorem set_cap_foot {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (hP : Placed th) {x : U64}
    (hx : IsSlot th x) (s : S) (c : capability.Cap) (hc : EncWf c) :
    obj.Slot.set_cap st x s c ⦃ s' => SlotFoot th (L.mem s) (L.mem s') x ∧ capV (L.mem s') x = c ⦄ := by
  refine WP.spec_mono (set_cap_spec x s c) ?_
  rintro s' rfl
  have hfx := hx.fit hP
  have ha : P1.Aligned x := by have := slot_word_aligned hP hx (k := 0#u64) (Or.inl rfl); rwa [wordOf_zero] at this
  have ha8 : P1.Aligned (core.num.U64.wrapping_add x 8#u64) := slot_word_aligned hP hx (k := 8#u64) (Or.inr (Or.inl rfl))
  have h8 : (core.num.U64.wrapping_add x 8#u64).val = x.val + 8 := wa8_val (by omega)
  refine ⟨SlotFoot.of_cap hP hx (fun b hb h1 h2 => ?_), ?_⟩
  · rw [mem_wr2 _ _ _ _ _ b ha ha8 hb, if_neg (by rw [h8]; exact fun e => h2 e.symm), if_neg (fun e => h1 e.symm)]
  · have := capAt_wr2_self (L := L) s x c hc ha ha8 (by rw [h8]; omega)
    rw [capAt_capV] at this; simpa using this

end

theorem KFoot.refl (σ : Fl4Spec.State Unit) : KFoot σ σ := ⟨rfl, rfl, fun _ h => absurd rfl h, rfl⟩

theorem KFoot.trans {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : KFoot σ1 σ2) (h2 : KFoot σ2 σ3) : KFoot σ1 σ3 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun o hne => ?_, h2.2.2.2.trans h1.2.2.2⟩
  by_cases e1 : σ2.kheap o = σ1.kheap o
  · have e2 : σ3.kheap o ≠ σ2.kheap o := by rw [e1]; exact hne
    rcases h2.2.2.1 o e2 with ⟨ao, ao', h, h'⟩ | ⟨r, cs, cs', h, hw, h'⟩ | ⟨t, t', h, h'⟩ <;> rw [e1] at h
    · exact Or.inl ⟨ao, ao', h, h'⟩
    · exact Or.inr (Or.inl ⟨r, cs, cs', h, hw, h'⟩)
    · exact Or.inr (Or.inr ⟨t, t', h, h'⟩)
  · rcases h1.2.2.1 o e1 with ⟨ao, ao', h, h'⟩ | ⟨r, cs, cs', h, hw, h'⟩ | ⟨t, t', h, h'⟩
    · by_cases e2 : σ3.kheap o = σ2.kheap o
      · exact Or.inl ⟨ao, ao', h, e2 ▸ h'⟩
      · rcases h2.2.2.1 o e2 with ⟨bo, bo', g, g'⟩ | ⟨r', ds, ds', g, gw, g'⟩ | ⟨u, u', g, g'⟩ <;> rw [h'] at g <;>
          cases g
        exact Or.inl ⟨ao, bo', h, g'⟩
    · by_cases e2 : σ3.kheap o = σ2.kheap o
      · exact Or.inr (Or.inl ⟨r, cs, cs', h, hw, e2 ▸ h'⟩)
      · rcases h2.2.2.1 o e2 with ⟨bo, bo', g, g'⟩ | ⟨r', ds, ds', g, gw, g'⟩ | ⟨u, u', g, g'⟩ <;> rw [h'] at g <;>
          cases g
        exact Or.inr (Or.inl ⟨r, cs, ds', h, hw, g'⟩)
    · by_cases e2 : σ3.kheap o = σ2.kheap o
      · exact Or.inr (Or.inr ⟨t, t', h, e2 ▸ h'⟩)
      · rcases h2.2.2.1 o e2 with ⟨bo, bo', g, g'⟩ | ⟨r', ds, ds', g, gw, g'⟩ | ⟨u, u', g, g'⟩ <;> rw [h'] at g <;>
          cases g
        exact Or.inr (Or.inr ⟨t, u', h, g'⟩)

/-- The spec's `set_thread_state` (as `stsAct (updK …)`). -/
theorem KFoot.sts {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x))
    (x' : Fl4Spec.Tcb) : KFoot σ (Notif.stsAct (Notif.updK σ t (.tcb x')) t) := by
  refine ⟨by unfold Notif.stsAct Notif.updK; split_ifs <;> rfl, by unfold Notif.stsAct Notif.updK; split_ifs <;> rfl,
    fun o hne => ?_, by unfold Notif.stsAct Notif.updK; split_ifs <;> rfl⟩
  rw [Notif.stsAct_kheap, Notif.updK_kheap] at hne ⊢
  by_cases e : o = t
  · subst e; exact Or.inr (Or.inr ⟨x, x', hk, by rw [Function.update_self]⟩)
  · rw [Function.update_of_ne e] at hne; exact absurd rfl hne

/-- A CNode slot set. -/
theorem KFoot.cnode {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    (hk : σ.kheap p = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs) (idx : List Bool) (a : Fl4Spec.Cap) :
    KFoot σ (setCnodeSlot σ p r cs idx a) := by
  refine ⟨rfl, rfl, fun o hne => ?_, rfl⟩
  by_cases e : o = p
  · subst e; exact Or.inr (Or.inl ⟨r, cs, Function.update cs idx (some a), hk, hwf, by simp [setCnodeSlot]⟩)
  · exact absurd (by simp [setCnodeSlot, e]) hne

/-- An arch object updated. -/
theorem KFoot.arch {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {ao : Fl4Spec.ArchKernelObj}
    (hk : σ.kheap p = some (.archObj ao)) (ao' : Fl4Spec.ArchKernelObj) :
    KFoot σ (Notif.updK σ p (.archObj ao')) := by
  refine ⟨rfl, rfl, fun o hne => ?_, rfl⟩
  rw [Notif.updK_kheap] at hne ⊢
  by_cases e : o = p
  · subst e; exact Or.inl ⟨ao, ao', hk, by rw [Function.update_self]⟩
  · rw [Function.update_of_ne e] at hne; exact absurd rfl hne

/-- The machine state changed. -/
theorem KFoot.ms (σ : Fl4Spec.State Unit) (ms : Fl4Spec.MachineState) : KFoot σ { σ with machineState := ms } :=
  ⟨rfl, rfl, fun _ h => absurd rfl h, rfl⟩

end

end Fl4Proofs.P3.Vs
