/-
P1: InvGaps' `vspace` family (frames, the paging structures, the ASID
control and ASID pool caps) keeps the invariants, from `DecPre`, the
deletion placement facts `DelPlace` (the looked-up paging entries are VSpace
words `V`), the CSpace placement facts `CdtHyps`, the invoked and extra
slots being cap slots (`CapSlotW`, `IrqPlace.extra`) and `VsPlace` (the
regions cleared by a table's unmap and by MakePool hold no tracked words;
the subframe destination slots are cap slots; and mapping a frame into an
EPT, named — VT-x: not yet refined (DESIGN §5)); a frame's EPT unmap is
proved from `EptPlace.find` (`ept.unmap.cur0`).  The work is within `Cur0` (after the caller's
restart): VSpace words (`Cur0.vs`), cap-slot words (`Cur0.capw`), cleared
regions (`Cur0.zr`) and kernel-global words (`Cur0.ks`).
-/
import Fl4Proofs.P1.QueueDecIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- A region holding no word P1 tracks: aligned, not wrapping, its words in
`Ω` and off the frame words. -/
def FreeRegion (Ω Sg : Set U64) (p n : U64) : Prop :=
  Aligned p ∧ n.val % 8 = 0 ∧ p.val + n.val ≤ 2 ^ 64 ∧
    ∀ b : U64, p.val ≤ b.val → b.val < p.val + n.val → b ∈ Ω ∧ b ∉ Sg

theorem writesIn_zr {s : S} {p n : U64} (ha : Aligned p) (hn : n.val % 8 = 0) (hw : p.val + n.val ≤ 2 ^ 64) :
    WritesIn st s (L.zr s p n) (fun b => p.val ≤ b.val ∧ b.val < p.val + n.val) :=
  ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hnb => by rw [L.mem_zr _ _ _ _ ha hn hw hb, if_neg hnb]⟩

/-- Clearing a free region. -/
theorem Cur0.zr {s0 s : S} {p n : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hR : FreeRegion Ω Sg p n) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.zr s p n) :=
  h.capw (writesIn_zr hR.1 hR.2.1 hR.2.2.1) fun b hb => Or.inr (hR.2.2.2 b hb.1 hb.2)

/-- A runnable thread set running. -/
theorem sched.set_thread_state.running_bxi' {s : S} {t : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : Runnable (L.mem s (stA t))) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨hnb, hnr⟩ := runnable_ok hr
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t :=
    hX.noref (h0.tcbs t ht) hnr (runnable_ne_recv hr)
  refine WP.spec_mono (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr hnb) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
  rintro s' ⟨h1, hB1, hX1, hS1, hSg1, -, -⟩
  exact ⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hSg1, hS1⟩

/-- An EPT table at `s`: every walk from it ends at an aligned untracked
object word. -/
def EptTbl (st : machine.Store S) (Ω Sg : Set U64) (s : S) (r : U64) : Prop :=
  ∀ gpa level, ept.lookup st s r gpa level ⦃ o => ∀ x, o = .Ok x → Aligned x ∧ x ∈ Ω ∧ x ∉ Sg ⦄

/-- **The EPT tables' placement** (P3's): a found EPT root is an EPT table,
and an invoked non-root EPT table cap's table holds no tracked word. -/
structure EptPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- At the caller's restart after the decode's start `s0` (its footprint `Foot`). -/
  find : ∀ (Ac : Set U64) (s0 s : S) (asid : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → EptTbl st Ω Sg s r1 ⦄
  tbl : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ ptr level m asid va,
      cap = .Ept ptr level m asid va → level ≠ 0#u64 → FreeRegion Ω Sg ptr 4096#u64

/-- **`ept.unmap`** from a found EPT table: at most one EPT entry cleared. -/
theorem ept.unmap.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A)
    (asid gpa ptr level : U64) (table : Bool)
    (hf : ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → EptTbl st Ω Sg s r1 ⦄)
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    ept.unmap st ar s a asid gpa ptr level table ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.unmap
  refine WP.spec_bind hf ?_
  rintro (r1 | e) hr
  swap
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (hr r1 rfl gpa level) ?_
  rintro (x | e) hx
  swap
  · exact (WP.spec_ok _).2 h
  obtain ⟨al, hΩ, hSg⟩ := hx x rfl
  try dsimp only
  refine WP.spec_bind (LawfulStore.read_spec s x) fun e _ => ?_
  have fin : (do
      let s1 ← st.write s x 0#u64
      ept.invalidate st ar s1 a r1) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
    refine WP.spec_bind (LawfulStore.write_spec s x 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (ept.invalidate.same hA _ a r1) fun r er => ?_
    rw [er]
    exact Cur0.capw h (writesIn_wr al) fun b hb => Or.inr (hb ▸ ⟨hΩ, hSg⟩)
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact (WP.spec_ok _).2 trivial
    split <;> exact (WP.spec_ok _).2 trivial) fun large _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · simp only [lift, bind_ok]
      step*
    · exact (WP.spec_ok _).2 trivial) fun mask _ => ?_
  simp only [lift, bind_ok, layout.paddr]
  split
  · exact (WP.spec_ok _).2 h
  split
  · split
    · exact (WP.spec_ok _).2 h
    split
    · exact (WP.spec_ok _).2 h
    · exact fin
  · split
    · exact (WP.spec_ok _).2 h
    · exact fin

/-- **The VSpace family's placement facts** (P3's): the regions a table's
unmap and MakePool clear and the ASID table's entries hold no tracked words,
the subframe destination slots are cap slots, and mapping a frame into an
EPT (VT-x: not yet refined, DESIGN §5). -/
structure VsPlace (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- A table cap's table (cleared by its unmap). -/
  tbl : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ ptr m asd va,
      (cap = .PageTable ptr m asd va ∨ cap = .PageDirectory ptr m asd va ∨ cap = .Pdpt ptr m asd va) →
      FreeRegion Ω Sg ptr 4096#u64
  /-- MakePool's untyped (its first page is cleared for the pool). -/
  pool : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ x ∈ extra.val, x ≠ 0#u64 →
      obj.Slot.cap st x s ⦃ c => ∀ ptr sb fi dev, c = .Untyped ptr sb fi dev → FreeRegion Ω Sg ptr 4096#u64 ⦄
  /-- The ASID table's entries hold no tracked words (MakePool's pool install). -/
  aset : ∀ (Ac : Set U64) (s0 s : S) (hi v : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi v ⦃ s1 => WritesIn st s s1 (fun b => b ∈ Ω ∧ b ∉ Sg) ⦄
  /-- The subframe destination slots. -/
  sub : ∀ (Ac : Set U64) (s : S) (x i d off cnt : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.subframe_dest st s x i d off cnt ⦃ r => ∀ dst, r = .Ok dst → ∀ j : U64, j.val < cnt.val →
      obj.Slot.index dst (core.num.U64.wrapping_add off j) ⦃ sl => CapW T Ω Sg sl ⦄ ⦄
  /-- EPT: mapping a frame into an EPT (VT-x: not yet refined, DESIGN §5). -/
  eptMap : ∀ (Ac : Set U64) (s : S) (a : A) (len : U64) (cap : capability.Cap) (slot buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize), EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra →
    ept.map_frame st ar s a len cap slot buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-! ## The paging lookups give VSpace words -/

theorem vspace.check_vspace.vs {V : U64 → Prop} {s0 : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {s : S}
    (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (vcap : capability.Cap) :
    vspace.check_vspace st s vcap ⦃ r => ∀ p, r = .Ok p → ∀ i : U64,
      V (core.num.U64.wrapping_add p.1 (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)) ⦄ := by
  unfold vspace.check_vspace
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp))
  rename_i ptr b asid
  split
  · refine WP.spec_bind (Pd.pml Ac s asid hf hb) fun r hr => ?_
    rcases r with r1 | lf
    · dsimp only
      split
      · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp)
      · rename_i hne
        have e : r1 = ptr := UScalar.eq_of_val_eq (by simpa using hne)
        subst e
        exact (WP.spec_ok _).2 (fun p hp => by cases hp; exact hr _ rfl)
    · exact (WP.spec_ok _).2 (fun p hp => by cases hp)
  · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 (fun p hp => by cases hp)

theorem vspace.table_entry_slot.vs {V : U64 → Prop} {s0 : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {s : S}
    (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) {root : U64}
    (hroot : ∀ i : U64, V (core.num.U64.wrapping_add root (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)))
    (vaddr level : U64) :
    vspace.table_entry_slot st s root vaddr level ⦃ r => ∀ x, r = .Ok x → V x ⦄ := by
  unfold vspace.table_entry_slot
  refine WP.spec_bind (Pₘ := fun r => ∀ x, r = .Ok x → V x) ?_ fun r hr => ?_
  · split
    · exact Pd.pd Ac s root vaddr hf hb
    split
    · exact Pd.pdpt Ac s root vaddr hf hb
    · refine WP.spec_bind (P0.vspace.idx.p0 vaddr _) fun ix _ => ?_
      unfold vspace.entry_addr
      simp only [lift, bind_ok, WP.spec_ok]
      exact fun x hx => by cases hx; exact hroot ix
  rcases r with x | lf
  · exact (WP.spec_ok _).2 fun x' hx => by cases hx; exact hr x rfl
  · simp only [vspace.failed_lookup]; exact (WP.spec_ok _).2 fun x' hx => by cases hx

theorem vspace.page_entry_slot.vs {V : U64 → Prop} {s0 : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {s : S}
    (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (root vaddr : U64) (fs : capability.FrameSize) :
    vspace.page_entry_slot st s root vaddr fs ⦃ r => ∀ x, r = .Ok x → V x ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.page_entry_slot
  refine WP.spec_bind (Pₘ := fun r => ∀ x, r = .Ok x → V x) ?_ fun r hr => ?_
  · cases fs
    · exact Pd.pt Ac s root vaddr hf hb
    · exact Pd.pd Ac s root vaddr hf hb
    · exact Pd.pdpt Ac s root vaddr hf hb
  rcases r with x | lf
  · have hx := hr x rfl
    dsimp only
    refine WP.spec_bind (Pₘ := fun _ => True) (by cases fs <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    split
    · exact (WP.spec_ok _).2 fun x' hx' => by cases hx'; exact hx
    refine WP.spec_bind (LawfulStore.read_spec s x) fun old _ => ?_
    repeat' (first
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'; exact hx
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'
      | (simp only [lift, bind_ok])
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_)
      | split)
  · simp only [vspace.failed_lookup]; exact (WP.spec_ok _).2 fun x' hx => by cases hx


theorem vspace.mapped_entry.vs {V : U64 → Prop} {s0 : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {s : S}
    (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (f : vspace.FrameCap) (root : U64) :
    vspace.mapped_entry st s f root ⦃ o => ∀ x, o = some x → V x ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.mapped_entry
  refine WP.spec_bind (P0.layout.paddr.p0 _) fun pa _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by cases f.size <;> exact (WP.spec_ok _).2 trivial) fun large _ => ?_
  refine WP.spec_bind (Pₘ := fun r => ∀ x, r = .Ok x → V x) ?_ fun r hr => ?_
  · split
    · exact Pd.pd Ac s root _ hf hb
    · exact Pd.pt Ac s root _ hf hb
  rcases r with x | lf
  · have hx := hr x rfl
    dsimp only
    refine WP.spec_bind (LawfulStore.read_spec s x) fun e _ => ?_
    repeat' (first
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'; exact hx
      | exact (WP.spec_ok _).2 fun x' hx' => by cases hx'
      | (simp only [lift, bind_ok])
      | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_)
      | split)
  · exact (WP.spec_ok _).2 fun x' hx => by cases hx

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errV" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg, vspace.failed_lookup]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

/-! ## The paging-structure caps -/

set_option maxHeartbeats 4000000 in
/-- **A table's unmap**: the restart, the unmap of its mapping (VSpace
words), the table's clearing, and the cap's update. -/
theorem vspace.decode_table_unmap.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (a : A) (slot : U64) (cap : capability.Cap) (level ptr : U64) (mapped : Bool) (masid mvaddr : U64)
    (hslot : CapSlotW T Ω Sg slot) (hz : FreeRegion Ω Sg ptr 4096#u64) :
    vspace.decode_table_unmap st ar s a slot cap level ptr mapped masid mvaddr ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.decode_table_unmap
  refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS) fun b _ => ?_
  split
  swap
  · errV
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  obtain ⟨Ac1, hb1⟩ := h1.bxi
  refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
  · split
    · refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
      · split
        · exact WP.spec_mono (vspace.unmap_page_table.vs hA s1 a masid mvaddr ptr Pd.vs
            fun r1 => Pd.pd Ac1 s1 r1 mvaddr h1.fr hb1) fun r w => h1.vs Pd.vs w
        split
        · exact WP.spec_mono (vspace.unmap_page_directory.vs hA s1 a masid mvaddr ptr Pd.vs
            fun r1 => Pd.pdpt Ac1 s1 r1 mvaddr h1.fr hb1) fun r w => h1.vs Pd.vs w
        · exact WP.spec_mono (vspace.unmap_pdpt.vs hA s1 a masid mvaddr ptr Pd.vs (Pd.pml Ac1 s1 masid h1.fr hb1))
            fun r w => h1.vs Pd.vs w
      rintro ⟨s3, a2⟩ h3
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (LawfulStore.zero_spec s3 ptr 4096#u64) fun s4 e4 => ?_
      subst e4
      exact (WP.spec_ok _).2 (Cur0.zr h3 hz)
    · exact (WP.spec_ok _).2 h1
  rintro ⟨s2, a1⟩ h2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.vspace.with_mapping.p0 cap false masid mvaddr) fun c _ => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (c := c) (s := s2) hslot) fun s3 w3 => ?_
  exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post

set_option maxHeartbeats 4000000 in
/-- **A table's map**: the restart, the cap's update and the table entry's
write (a VSpace word). -/
theorem vspace.decode_table_map.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (a : A) (len slot : U64) (cap : capability.Cap) (level ptr buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_table_map st ar s a len slot cap level ptr buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode_table_map
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
  rcases o with _ | x
  · errV
  try dsimp only
  split
  swap
  · errV
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i2 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun attr _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun vcap _ => ?_
  refine WP.spec_bind (P0.vspace.is_valid_vtable_root.p0 vcap) fun bv _ => ?_
  split
  swap
  · errV
  split
  · errV
  refine WP.spec_bind (vspace.check_vspace.vs Pd (WritesIn.refl _ _) hb vcap) fun r hr => ?_
  rcases r with ⟨root, asid⟩ | e
  swap
  · errV
  have hroot := hr _ rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (vspace.table_entry_slot.vs Pd (WritesIn.refl _ _) hb hroot _ level) fun r1 hr1 => ?_
  rcases r1 with v | e
  swap
  · errV
  have hv := hr1 v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s v) fun i5 _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i6 _ => ?_
  try simp only [lift, bind_ok]
  split
  · errV
  refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun i8 _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_table.p0 i8 attr) fun en _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (P0.vspace.with_mapping.p0 cap true asid _) fun c _ => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (c := c) (s := s1) hslot) fun s2 w2 => ?_
  have h2 := h1.capw w2 fun _ hb => hb
  refine WP.spec_bind (LawfulStore.write_spec s2 v en) fun s3 e3 => ?_
  subst e3
  have h3 := h2.vs Pd.vs (writesIn_wr_V (v := en) Pd.vs hv)
  refine WP.spec_bind (hA.invalidate_page_structures a asid) fun a1 _ => ?_
  exact (WP.spec_ok _).2 h3.post

set_option maxHeartbeats 4000000 in
/-- **The paging-structure caps' decode** (map, unmap). -/
theorem vspace.decode_table.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) 
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s)
    (a : A) (lbl len slot buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_table st ar s a lbl len slot cap buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  unfold vspace.decode_table
  cases cap
  all_goals simp only [vspace.as_table, bind_ok]
  all_goals try errV
  all_goals
    rename_i ptr m asd va
    try dsimp only
    split
    · exact vspace.decode_table_unmap.dec hA Pd D a slot _ _ ptr m asd va hslot
        (Vs.tbl _ _ _ _ hE D ptr m asd va (by simp))
    split
    swap
    · errV
    split
    · refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
      rcases o with _ | x
      · errV
      try dsimp only
      split <;> errV
    · exact vspace.decode_table_map.dec hA Pd D a len slot _ _ ptr buf hslot


/-! ## Frames -/

/-- **`write_mapping`** of a VSpace word. -/
theorem vspace.write_mapping.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (hV : VsOK Ω Sg V) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) {x : U64} (hx : V x)
    (e asid vaddr : U64) (defer : Bool) :
    vspace.write_mapping st ar s a x e asid vaddr defer ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  unfold vspace.write_mapping
  refine WP.spec_bind (LawfulStore.read_spec s x) fun old _ => ?_
  refine WP.spec_bind (LawfulStore.write_spec s x e) fun s1 e1 => ?_
  subst e1
  have h1 := h.vs hV (writesIn_wr_V (v := e) hV hx)
  repeat' (first
    | exact (WP.spec_ok _).2 h1
    | (simp only [lift, bind_ok])
    | (refine WP.spec_bind (hA.invalidate_page a _ _) fun _ _ => ?_)
    | (refine WP.spec_bind (hA.invalidate_asid a _) fun _ _ => ?_)
    | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_)
    | split)

theorem shl_and63 (x : U64) : (1#u64 <<< (x &&& 63#u64) : Result U64) ⦃ _ => True ⦄ := by
  p0_auto

set_option hygiene false in
/-- The page map's tail, from the frame size's match: the entry slot (a
VSpace word), the restart, the cap's update and the entry's write. -/
local macro "pmtail" : tactic => `(tactic| (
  try simp only [bind_ok, uncurry_apply_pair]
  refine WP.spec_bind (vspace.page_entry_slot.vs Pd (WritesIn.refl _ _) hb _ _ _) fun r3 hr3 => ?_
  rcases r3 with v | e
  swap
  · errV
  have hv := hr3 v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.vspace.frame_address.p0 st ar s a _ hS hA) fun _ _ => ?_
  refine WP.spec_bind (P0.vspace.make_user_page.p0 st s _ _ _ _ hS) fun en _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hslot) fun s2 w2 => ?_
  refine WP.spec_bind (vspace.write_mapping.cur0 hA Pd.vs (h1.capw w2 fun _ hb => hb) a hv en _ _ _) ?_
  rintro ⟨s3, a1⟩ h3
  exact (WP.spec_ok _).2 h3.post))

set_option hygiene false in
/-- The pure steps and error leaves before the page map's tail. -/
local macro "pmpre" : tactic => `(tactic| (
  repeat' (first
    | (refine WP.spec_bind (P0.vspace.check_vspace.p0 st s _ hS) fun r1 _ => ?_
       rcases r1 with _ | e
       swap
       · errV
       simp only [irq_branch_ok, bind_ok])
    | (simp only [lift, bind_ok])
    | (refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_)
    | (refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun _ _ => ?_)
    | (refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun _ _ => ?_)
    | (refine WP.spec_bind (shl_and63 _) fun _ _ => ?_)
    | (split; · errV))))

set_option maxHeartbeats 8000000 in
/-- **The page map**: the restart, the frame cap's update and the entry's
write (a VSpace word). -/
theorem vspace.decode_page_map.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (a : A) (len slot : U64) (f : vspace.FrameCap) (buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_page_map st ar s a len slot f buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  obtain ⟨fptr, fsize, frights, fdev, fmapped, fept, fasid, fva⟩ := f
  unfold vspace.decode_page_map
  cases fsize
  all_goals try dsimp only
  all_goals
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
    rcases o with _ | x
    · errV
    try dsimp only
    split
    swap
    · errV
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun vaddr _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    try simp only [lift, bind_ok]
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun vcap _ => ?_
    refine WP.spec_bind (P0.vspace.mapped_root.p0 vcap) fun o1 _ => ?_
    rcases o1 with _ | r
    · errV
    all_goals
      try dsimp only
      split
      · split
        · split
          · errV
          split
          · errV
          pmpre
          pmtail
        · pmpre
          pmtail
      · pmpre
        pmtail


/-- **`reply1`**: the reply's message registers (`XS`), then the thread set
running. -/
theorem vspace.reply1.bxi (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) {t : U64} (ht : t ∈ T)
    (hr : Runnable (L.mem s (stA t))) (call : Bool) (v : U64) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    vspace.reply1 st s t call v ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨Q, R, x1⟩ := BXI.xs h hU
  unfold vspace.reply1
  refine WP.spec_bind (Pₘ := fun s2 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s s2) ?_ ?_
  · split
    · refine WP.spec_bind (E.buf Ac ∅ Q R s _ hG x1.1 ht) fun b hb => ?_
      refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1 ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
        fun s3 x3 => ?_
      refine WP.spec_bind (msg.set_mr.xs x3 ht hb (by simp)) ?_
      rintro ⟨n, s4⟩ ⟨x4, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      unfold msg.set_msg_info
      exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
        obj.Tcb.set_reg.xs (v := w) x4 ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
    · exact (WP.spec_ok _).2 x1
  intro s2 x2
  have hst : L.mem s2 (stA t) = L.mem s (stA t) := by
    rw [stA_eq, x2.fr.2.2.2.2.1 _ ht _ (by simp) (by simp) (by simp), ← stA_eq]
  exact sched.set_thread_state.running_bxi' x2.bxi ht (hst ▸ hr)

set_option maxHeartbeats 4000000 in
/-- **TestAndClearAccessed**: the entry's accessed bit cleared (a VSpace
word), then the reply. -/
theorem vspace.decode_test_and_clear_accessed.dec {V : U64 → Prop} {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)  {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (f : vspace.FrameCap) (call : Bool) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    vspace.decode_test_and_clear_accessed st s f call ⦃ r =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  obtain ⟨fptr, fsize, frights, fdev, fmapped, fept, fasid, fva⟩ := f
  unfold vspace.decode_test_and_clear_accessed
  cases fsize
  all_goals simp only [bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
  all_goals try (simp only [error.illegal, bind_ok, ite_true]; exact (WP.spec_ok _).2 (D.err _))
  all_goals
    try dsimp only
    split
    swap
    · errV
    split
    · errV
    refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s _ hS) fun r _ => ?_
    rcases r with r1 | e
    swap
    · errV
    try dsimp only
    refine WP.spec_bind (vspace.mapped_entry.vs Pd (WritesIn.refl _ _) hb _ r1) fun o ho => ?_
    rcases o with _ | x
    · errV
    have hx := ho x rfl
    try dsimp only
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (LawfulStore.read_spec s x) fun old _ => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
    try simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.write_spec s x _) fun s1 e1 => ?_
    subst e1
    obtain ⟨h1, -, -, ec, -, fld, -, -⟩ := blk_of_vs hb.blk Pd.vs (writesIn_wr_V (v := old &&& ~~~i) Pd.vs hx)
    have hU1 : UserOK st T Cs Ω H U (L.wr s x (old &&& ~~~i)) := D.user.ksb (L.ksb_wr _ _ _)
    have hr1 : Runnable (L.mem (L.wr s x (old &&& ~~~i)) (stA (L.curW s))) := by
      rw [stA_eq, fld _ hct _ (by simp) (by simp) (by simp), ← stA_eq]; exact D.run
    have hG1 : XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s x (old &&& ~~~i)) :=
      hG.of_fr ((writesIn_wr_V (v := old &&& ~~~i) Pd.vs hx).mono fun b hb =>
        Or.inr (Or.inr (Or.inl (Or.inr (Pd.vs b hb).2))))
    split
    · exact WP.spec_bind (vspace.reply1.bxi E (BlkOK.bxi h1) hU1 hct hr1 call _ hG1) fun s2 h2 =>
        (WP.spec_ok _).2 (DecPost.ok_bxi h2)
    · exact WP.spec_bind (vspace.reply1.bxi E (BlkOK.bxi h1) hU1 hct hr1 call _ hG1) fun s2 h2 =>
        (WP.spec_ok _).2 (DecPost.ok_bxi h2)


/-- **`insert_subframes`**: the subframe caps' insertions under the source
slot, into cap slots. -/
theorem vspace.insert_subframes.cur0 (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s0 s : S}
    (hE : EntAt st P3Ok s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) {src dest first base count vm : U64} (hsrc : CapW T Ω Sg src)
    (hd : ∀ j : U64, j.val < count.val → obj.Slot.index dest (core.num.U64.wrapping_add first j) ⦃ sl =>
      CapW T Ω Sg sl ⦄) :
    vspace.insert_subframes st s src dest first base count vm ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.insert_subframes vspace.insert_subframes_loop
  apply loop.spec_decr_nat (measure := fun y : S × U64 => count.val - y.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s3, i3⟩ h3
    simp only at h3
    dsimp only
    unfold vspace.insert_subframes_loop.body
    split
    · rename_i hlt
      have hlt' : i3.val < count.val := by simpa using hlt
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
      try simp only [lift, bind_ok]
      refine WP.spec_bind (hd i3 hlt') fun sl hsl => ?_
      obtain ⟨Ac', hb⟩ := h3.bxi
      refine WP.spec_bind (Pₘ := fun s4 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s4) ?_ fun s4 h4 => ?_
      · unfold cdt.insert
        refine WP.spec_bind (P0.obj.Slot.cap.p0 st src s3 hS) fun c0 _ => ?_
        exact WP.spec_mono (C.ins Ac' s0 s3 _ c0 src sl hE h3.fr hb hsrc hsl) fun s5 w => h3.capw w fun _ hb => hb
      step as ⟨i4, hi4⟩
      exact ⟨h4, by scalar_tac⟩
    · exact (WP.spec_ok _).2 h3
  · exact h

set_option maxHeartbeats 4000000 in
/-- **DeriveSubframe**: the restart and the subframe caps' insertions. -/
theorem vspace.derive_subframe.dec {A : Type _} {ar : machine.Arch A} (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap0 : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap0 extra)
    (hE : EntAt st P3Ok s) (a : A) (len src : U64) (cap : capability.Cap) (buf : U64) (hsrc : CapSlotW T Ω Sg src) :
    vspace.derive_subframe st ar s a len src cap buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.derive_subframe
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.vspace.extra.p0 extra 0#usize) fun o _ => ?_
  rcases o with _ | x
  · errV
  try dsimp only
  split
  swap
  · errV
  refine WP.spec_bind (P0.vspace.large_ram_frame.p0 cap) fun o1 _ => ?_
  rcases o1 with _ | ⟨ptr, rights⟩
  · errV
  try dsimp only
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun ni _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun nd _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun no _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun off _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun cnt _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  split
  · errV
  try simp only [lift, bind_ok]
  split
  · errV
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  split
  · errV
  split
  · errV
  refine WP.spec_bind (Vs.sub Ac s x ni nd no cnt hE hb) fun r hr => ?_
  rcases r with dst | e
  swap
  · errV
  have hd := hr dst rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.vspace.ensure_empty_run.p0 st s dst no cnt hS) fun r1 _ => ?_
  rcases r1 with _ | e
  swap
  · errV
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun _ _ => ?_
  refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (vspace.insert_subframes.cur0 C hE h1 (SlotW.capw0 hsrc) hd) fun s2 h2 => ?_
  exact (WP.spec_ok _).2 h2.post


set_option maxHeartbeats 8000000 in
/-- **The frame caps' decode**. -/
theorem vspace.decode_frame.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pe : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) 
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (fp fsz : _) (fr : U64) (fd fm fe : Bool) (fa fv : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Frame fp fsz fr fd fm fe fa fv) extra) (hE : EntAt st P3Ok s)
    (a : A) (lbl len slot : U64) (call : Bool) (buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode_frame st ar s a lbl len slot (.Frame fp fsz fr fd fm fe fa fv) call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok]
  split
  · exact Vs.eptMap _ _ _ _ _ _ _ _ hE D
  split
  · split
    · split
      · errV
      · exact vspace.decode_page_map.dec hA Pd D a len slot _ buf hslot
    · exact vspace.decode_page_map.dec hA Pd D a len slot _ buf hslot
  split
  · step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1) ?_ ?_
    · split
      · split
        · split
          · refine WP.spec_bind (P0.capability.FrameSize.bits.p0 _) fun i _ => ?_
            exact ept.unmap.cur0 hA _ _ _ _ _ _ (Pe.find Ac1 s s1 _ hE h1.fr hb1) h1
          · exact WP.spec_mono (vspace.unmap_page.vs hA s1 a _ _ _ _ Pd.vs (fun r1 => Pd.pt Ac1 s1 r1 _ h1.fr hb1)
              (fun r1 => Pd.pd Ac1 s1 r1 _ h1.fr hb1) (fun r1 => Pd.pdpt Ac1 s1 r1 _ h1.fr hb1)) fun r w => h1.vs Pd.vs w
        · exact (WP.spec_ok _).2 h1
      · exact (WP.spec_ok _).2 h1
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (obj.Slot.set_cap.capw (s := s2) hslot) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post
  split
  · step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 _) fun i _ => ?_
    refine WP.spec_bind (vspace.reply1.bxi E (BlkOK.bxi h1) (D.user.ksb f1.1) hct (hst1 ▸ runnable_restart) call i (hE.xg.of_fr (Foot.cur0w f1 (Set.empty_subset _))))
      fun s2 h2 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h2)
  split
  · refine WP.spec_bind (vspace.decode_test_and_clear_accessed.dec Pd E D _ call hE.xg) ?_
    rintro ⟨r, s1⟩ hr
    exact (WP.spec_ok _).2 hr
  split
  · exact vspace.derive_subframe.dec C Vs D hE a len slot _ buf hslot
  · errV


theorem spec_exists' {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem vspace.extra.mem (ex : Aeneas.Std.Array obj.Slot 3#usize) (i : Usize) :
    vspace.extra ex i ⦃ o => ∀ x, o = some x → x ∈ ex.val ∧ x ≠ 0#u64 ⦄ := by
  unfold vspace.extra
  split
  · exact (WP.spec_ok _).2 fun x hx => by cases hx
  rename_i hi
  refine WP.spec_bind (idx_mem ex i (by simp at hi; scalar_tac)) fun x hx => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 fun x hx => by cases hx
  · rename_i h0
    exact (WP.spec_ok _).2 fun y hy => by cases hy; exact ⟨hx, by simpa using h0⟩

theorem mask511_mul8 (x : U64) (y : U64) (hy : y.val = (x &&& 511#u64).val * 8) :
    y = core.num.U64.wrapping_mul (x &&& 511#u64) 8#u64 := by
  have hb : (x &&& 511#u64).val < 512 := by
    rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  apply UScalar.eq_of_val_eq
  rw [core.num.U64.wrapping_mul_val_eq, hy]
  have h8 : (8#u64).val = 8 := rfl
  rw [h8]
  exact (Nat.mod_eq_of_lt (by first | (simp [UScalar.size, UScalarTy.numBits]; omega) | scalar_tac)).symm

set_option maxHeartbeats 16000000 in
/-- **`vspace.decode`** over the VSpace family's caps. -/
theorem vspace.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s : S} (Pd : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pe : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) 
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s)
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapSlotW T Ω Sg sl)
    (a : A) (lbl len slot : U64) (call : Bool) (buf : U64) (hslot : CapSlotW T Ω Sg slot) :
    vspace.decode st ar s a lbl len slot cap call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hb := D.bxi
  unfold vspace.decode
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  cases cap
  all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
  case Frame fp fsz fr fd fm fe fa fv =>
    exact vspace.decode_frame.dec hA Pd Vs Pe C E fp fsz fr fd fm fe fa fv D hE a lbl len slot call buf hslot
  case PageTable => exact vspace.decode_table.dec hA Pd Vs D hE a lbl len slot buf hslot
  case PageDirectory => exact vspace.decode_table.dec hA Pd Vs D hE a lbl len slot buf hslot
  case Pdpt => exact vspace.decode_table.dec hA Pd Vs D hE a lbl len slot buf hslot
  case Pml4 ptr mapped asid =>
    try dsimp only
    split
    swap
    · errV
    split
    swap
    · errV
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
    exact (WP.spec_ok _).2 h1.post
  case AsidControl =>
    try dsimp only
    split
    · errV
    refine WP.spec_bind (vspace.extra.mem extra 0#usize) fun o ho => ?_
    refine WP.spec_bind (vspace.extra.mem extra 1#usize) fun o1 ho1 => ?_
    rcases o with _ | x
    · errV
    obtain ⟨hxm, hx0⟩ := ho x rfl
    try dsimp only
    rcases o1 with _ | y
    · errV
    try dsimp only
    split
    swap
    · errV
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
    refine WP.spec_bind (WP.spec_and (P0.obj.Slot.cap.p0 st x s hS) (Vs.pool _ _ _ _ hE D x hxm hx0)) fun ut ⟨_, hut⟩ => ?_
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st y s hS) fun root _ => ?_
    refine WP.spec_bind (P0.vspace.decode_loop0.p0 st s 0#u64 hS) fun i _ => ?_
    split
    · errV
    refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun base _ => ?_
    cases ut
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    case Untyped uptr usb ufi udev =>
      have hz := hut _ _ _ _ rfl
      try dsimp only
      split
      · errV
      split
      swap
      · errV
      refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s x hS) fun r _ => ?_
      rcases r with _ | e
      swap
      · errV
      simp only [irq_branch_ok, bind_ok]
      refine WP.spec_bind (C.tgt Ac s root idx dep hE hb) fun r1 hr1 => ?_
      rcases r1 with v | e
      swap
      · errV
      have hv := hr1 v rfl
      simp only [irq_branch_ok, bind_ok]
      refine WP.spec_bind (P0.cdt.ensure_empty_slot.p0 st s v hS) fun r2 _ => ?_
      rcases r2 with _ | e
      swap
      · errV
      simp only [irq_branch_ok, bind_ok]
      refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
      try simp only [lift, bind_ok]
      refine WP.spec_bind (shl_and63 _) fun i2 _ => ?_
      have hxs := hx x hxm hx0
      refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hxs) fun s2 w2 => ?_
      have h2 := h1.capw w2 fun _ hb => hb
      refine WP.spec_bind (LawfulStore.clear_free_spec s2 _ 4096#u64) fun s3 e3 => ?_
      subst e3
      have h3 := Cur0.zr h2 hz
      obtain ⟨Ac3, hb3⟩ := h3.bxi
      refine WP.spec_bind (Pₘ := fun s4 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s4) ?_ fun s4 h4 => ?_
      · unfold cdt.insert
        refine WP.spec_bind (P0.obj.Slot.cap.p0 st x _ hS) fun c0 _ => ?_
        exact WP.spec_mono (C.ins Ac3 s _ _ c0 x v hE h3.fr hb3 (SlotW.capw0 hxs) hv) fun s5 w => h3.capw w fun _ hb => hb
      obtain ⟨Ac4, hb4⟩ := h4.bxi
      refine WP.spec_bind (Vs.aset Ac4 s s4 i _ hE h4.fr hb4) fun s5 w5 => ?_
      exact (WP.spec_ok _).2 (h4.capw w5 fun b hb => Or.inr hb).post
  case AsidPool pptr abase =>
    try dsimp only
    split
    · errV
    refine WP.spec_bind (vspace.extra.mem extra 0#usize) fun o ho => ?_
    rcases o with _ | x
    · errV
    obtain ⟨hxm, hx0⟩ := ho x rfl
    have hxs := hx x hxm hx0
    try dsimp only
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c _ => ?_
    cases c
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    case Pml4 ptr1 b1 _ =>
      try dsimp only
      split
      · errV
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
      obtain ⟨pool, epool, -⟩ := spec_exists' (P0.vspace.asid_table.p0 st s i hS)
      have hpool : ∀ asid, pool ≠ 0#u64 →
          V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) := by
        intro asid
        have := Pd.pool Ac s asid i (WritesIn.refl _ _) hb
        rw [epool] at this
        exact (WP.spec_ok _).1 this
      rw [epool]
      simp only [bind_ok]
      split
      · errV
      rename_i hp0
      split
      · errV
      refine WP.spec_bind (P0.vspace.decode_loop1.p0 st s abase pool 0#u64 hS) fun i1 _ => ?_
      split
      · errV
      try simp only [lift, bind_ok]
      refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
      refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hxs) fun s2 w2 => ?_
      have h2 := h1.capw w2 fun _ hb => hb
      step as ⟨i3, hi3⟩
      try simp only [lift, bind_ok]
      refine WP.spec_bind (LawfulStore.write_spec s2 _ ptr1) fun s3 e3 => ?_
      subst e3
      rw [mask511_mul8 _ i3 hi3]
      exact (WP.spec_ok _).2 (h2.vs Pd.vs (writesIn_wr_V (v := ptr1) Pd.vs (hpool _ hp0))).post
    case Ept ptr1 i b1 _ _ =>
      try dsimp only
      split
      · try dsimp only
        split
        · errV
        try simp only [lift, bind_ok]
        refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i1 _ => ?_
        obtain ⟨pool, epool, -⟩ := spec_exists' (P0.vspace.asid_table.p0 st s i1 hS)
        have hpool : ∀ asid, pool ≠ 0#u64 →
            V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) := by
          intro asid
          have := Pd.pool Ac s asid i1 (WritesIn.refl _ _) hb
          rw [epool] at this
          exact (WP.spec_ok _).1 this
        rw [epool]
        simp only [bind_ok]
        split
        · errV
        rename_i hp0
        split
        · errV
        refine WP.spec_bind (P0.vspace.decode_loop2.p0 st s abase pool 0#u64 hS) fun i2 _ => ?_
        split
        · errV
        try simp only [lift, bind_ok]
        refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
        try simp only [lift, bind_ok]
        refine WP.spec_bind (obj.Slot.set_cap.capw (s := s1) hxs) fun s2 w2 => ?_
        have h2 := h1.capw w2 fun _ hb => hb
        step as ⟨i6, hi6⟩
        try simp only [lift, bind_ok]
        refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
        subst e3
        rw [mask511_mul8 _ i6 hi6]
        exact (WP.spec_ok _).2 (h2.vs Pd.vs (writesIn_wr_V Pd.vs (hpool _ hp0))).post
      · errV


/-- **InvGaps' `vspace`, discharged** from the deletion and CSpace
placement facts, the transfer's (a reply's buffer), `IrqPlace.extra` (the
extra caps' slots) and `VsPlace`. -/
theorem decGap_vspace {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (Vs : VsPlace st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pe : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hE
  cases cap <;> simp [capFam] at hf
  all_goals
    unfold syscall.decode_invocation
    step with sched.cur_thread.spec as ⟨ct, _⟩
    try dsimp only
    exact vspace.decode.dec hA (Pd s hE) Vs Pe C E D hE (Pl.extra _ _ _ _ hE D) a lbl len slot call buf hslot

end

end Fl4Proofs.P1
