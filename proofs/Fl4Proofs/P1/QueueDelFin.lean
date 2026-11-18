/-
P1: the finalisation steps of CNode `Delete`/`Revoke`, by cap kind.  The
kinds with no state change (and CNode/Zombie, whose remainder is a zombie),
the VSpace kinds (page table, page directory, PDPT, non-EPT frame, PML4,
ASID pool: QueueVsFin's unmaps and `unmap_page_directory.vs`/`unmap_pdpt.vs`), `empty_slot` with `post_cap_deletion`, `cdt.swap` and
`delete_deferred` are proved; the other kinds are named, one shape
(`FinGap`, in `FinKinds`).  `delGaps_of` gives QueueDecDel's `DelGaps` from
`FinKinds` and the placement facts `DelPlace` (typed caps in cap slots, CDT
links naming cap slots, VSpace lookups naming VSpace words).
-/
import Fl4Proofs.P1.QueueEntryGaps3
import Fl4Proofs.P1.QueueYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The finalisation shape**: `finalise_cap` of a typed cap with `P`, from
`Cur0` to `Cur0`, with typed remainder and cleanup caps. -/
def FinGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) : Prop :=
  ∀ (Ac : Set U64) (s0 s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

/-- `FinGap` from one decode start `s0`. -/
def FinGapAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

theorem FinGap.at {A : Type _} {ar : machine.Arch A} {P : capability.Cap → Prop}
    (g : FinGap st ar T Cs Ω H Sg Rp Scs Nt Z P) (s0 : S) : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0 :=
  fun Ac s a c fin => g Ac s0 s a c fin

theorem fin_noop {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hc : c = .Null ∨ (∃ x y z w, c = .Untyped x y z w) ∨ c = .IrqControl ∨ c = .Domain ∨
      (∃ x, c = .SchedControl x) ∨ c = .AsidControl ∨ c = .IoPortControl) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  rcases hc with rfl | ⟨_, _, _, _, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl <;>
    simp [objects.finalise_cap, objects.finalise_cap_object, h, DelCapOK.null]

theorem fin_cnode {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {p r g b : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt (.CNode p r g b)) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin false ⦃ x => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt x.1.1 ∧ DelCapOK T Ω Sg H Rp Nt x.1.2 ⦄ := by
  obtain ⟨hp, hi⟩ := hc.2.2.2.1 p r g b rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  split
  · simp only [lift, bind_ok]
    step as ⟨n, hn⟩
    refine ⟨h, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, DelCapOK.null⟩ <;> try (intros; simp_all; done)
    intro p' t' n' e
    simp only [capability.Cap.Zombie.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨hp, fun i hlt => hi i ?_⟩
    have : (r &&& 63#u64).val = r.val % 64 := by
      simp [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod r.val 6
    rw [hn, this] at hlt; exact hlt
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩

theorem fin_zombie {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {p t n : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt (.Zombie p t n)) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin false ⦃ x => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt x.1.1 ∧ DelCapOK T Ω Sg H Rp Nt x.1.2 ⦄ := by
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  exact (WP.spec_ok _).2 ⟨h, hc, DelCapOK.null⟩

/-- The placement facts of a deletion (P3's): the caps in cap slots are typed
for their deletion (`DelCapOK`); the CDT links of a cap slot are cap slots
or null; the VSpace lookups of the unmaps name VSpace words `V` (aligned
words of the other objects outside `Sg`), and so do the ASID tables. -/
structure DelPlaceAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop where
  vs : VsOK Ω Sg V
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  prev : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → SlotW T Ω Sg x →
    obj.Slot.prev st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄
  pt : ∀ (Ac : Set U64) (s : S) (r1 v : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.lookup_pt_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄
  pd : ∀ (Ac : Set U64) (s : S) (r1 v : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.lookup_pd_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄
  pdpt : ∀ (Ac : Set U64) (s : S) (r1 v : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.lookup_pdpt_slot st s r1 v ⦃ r => ∀ x, r = .Ok x → V x ⦄
  pool : ∀ (Ac : Set U64) (s : S) (asid i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄
  aset : ∀ (Ac : Set U64) (s : S) (hi : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄
  /-- An IRQ's handler slot holds no cap or a notification cap
  (`deleting_irq_handler`). -/
  irq : ∀ (Ac : Set U64) (s : S) (i : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → i.val < 128 →
    obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => c = .Null ∨ ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ⦄
  /-- The PML4 entries of an ASID's root are VSpace words (`unmap_pdpt`). -/
  pml : ∀ (Ac : Set U64) (s : S) (asid : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → ∀ i : U64,
      V (core.num.U64.wrapping_add r1 (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)) ⦄

/-- **The deletion placement facts** (P3's), at every decode start reached
from a `P3Ok` entry, along the decode's frame (`Fr0`). -/
def DelPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0

/-- **`unmap_page_directory`** writes only the PDPT slot it looks up. -/
theorem vspace.unmap_page_directory.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pd : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hlk : ∀ r1, vspace.lookup_pdpt_slot st s r1 vaddr ⦃ r => ∀ x, r = .Ok x → V x ⦄) :
    vspace.unmap_page_directory st ar s a asid vaddr pd ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_asid
  have i2 := hA.invalidate_page_structures
  unfold vspace.unmap_page_directory
  refine WP.spec_bind (P0.vspace.find_vspace_for_asid.p0 st s asid hS) fun r _ => ?_
  rcases r with r1 | e
  · refine WP.spec_bind (hlk r1) fun r2 hr2 => ?_
    rcases r2 with x | e
    · have hx := hr2 x rfl
      step*
      all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV hx)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_pdpt`** writes only the PML4 slot of the ASID's root. -/
theorem vspace.unmap_pdpt.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pdpt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hpml : vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → ∀ i : U64,
      V (core.num.U64.wrapping_add r1 (core.num.U64.wrapping_mul (i &&& 511#u64) 8#u64)) ⦄) :
    vspace.unmap_pdpt st ar s a asid vaddr pdpt ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have i1 := hA.invalidate_asid
  unfold vspace.unmap_pdpt
  refine WP.spec_bind hpml fun r hr => ?_
  rcases r with r1 | e
  · have hx := hr r1 rfl
    refine WP.spec_bind (P0.vspace.idx.p0 vaddr 39#u64) fun i _ => ?_
    unfold vspace.entry_addr
    simp only [lift, bind_ok]
    step*
    all_goals first | exact WritesIn.refl _ _ | (subst_vars; exact writesIn_wr_V hV (hx i))
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

theorem Cur0.vs {s0 s s' : S} {V : U64 → Prop} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hV : VsOK Ω Sg V)
    (hw : WritesIn st s s' V) : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' :=
  h.capw hw fun b hb => Or.inr ⟨(hV b hb).2.1, (hV b hb).2.2⟩

set_option maxHeartbeats 2000000 in
/-- The VSpace kinds QueueVsFin covers. -/
theorem fin_vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hc : (∃ x y z w, c = .PageTable x y z w) ∨ (∃ x y z w m asid vaddr, c = .Frame x y z w m false asid vaddr) ∨
      (∃ x y z, c = .Pml4 x y z) ∨ (∃ x y, c = .AsidPool x y) ∨ (∃ x y z w, c = .PageDirectory x y z w) ∨
      (∃ x y z w, c = .Pdpt x y z w)) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  have hb := h.bxi
  obtain ⟨Ac', hb⟩ := hb
  have W : ∀ (m : Result (S × A)), m ⦃ r => WritesIn st s r.1 V ⦄ →
      (do let (s1, a1) ← m; ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ r =>
        Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := fun m hm =>
    WP.spec_bind hm fun r hr => by
      obtain ⟨s1, a1⟩ := r
      exact (WP.spec_ok _).2 ⟨h.vs P.vs hr, DelCapOK.null, DelCapOK.null⟩
  have K : (ok ((capability.Cap.Null, capability.Cap.Null), s, a) : Result _) ⦃ r =>
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  rcases hc with ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, m, asid, vaddr, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, rfl⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.unmap_page_table.vs hA s a z w x P.vs fun r1 => P.pd Ac' s r1 w h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (Pₘ := fun r => WritesIn st s r.1 V)
    · split
      · split
        · exact vspace.unmap_page.vs hA s a y asid vaddr x P.vs (fun r1 => P.pt Ac' s r1 vaddr h.fr hb)
            (fun r1 => P.pd Ac' s r1 vaddr h.fr hb) (fun r1 => P.pdpt Ac' s r1 vaddr h.fr hb)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rintro ⟨s1, a1⟩ hw
      cases fin <;> cases w <;> simp only [↓reduceIte, Bool.false_eq_true, uncurry_apply_pair]
      all_goals first
        | exact (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
        | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 x y L.total hA) fun _ _ =>
            (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.delete_asid.vs hA s a z x P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · exact W _ (vspace.delete_asid_pool.vs hA s a y x fun hi => P.aset Ac' s hi h.fr hb)
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.unmap_page_directory.vs hA s a z w x P.vs fun r1 => P.pdpt Ac' s r1 w h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W _ (vspace.unmap_pdpt.vs hA s a z w x P.vs (P.pml Ac' s z h.fr hb))
      · exact K
    · exact K

/-- The finalisations of the kinds this file does not prove, one shape
(`FinGap`): the endpoint, notification, reply, SC, thread and IRQ handler
kinds (QueueFinCur proves the endpoint, notification, reply and IRQ handler
ones), and the VCPU/EPT/I/O-port kinds (with EPT frames). -/
structure FinKindsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  ep : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3 x4 x5 x6, c = .Endpoint x1 x2 x3 x4 x5 x6) s0
  ntfn : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3 x4, c = .Notification x1 x2 x3 x4) s0
  reply : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .Reply x1 x2) s0
  sc : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .SchedContext x1 x2) s0
  thread : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .Thread x1) s0
  irq : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0
  ioPort : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3, c = .IoPort x1 x2 x3) s0
  /-- The VT-x kinds: VCPUs, EPTs and EPT frames. -/
  arch : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0

/-- **Every cap kind's finalisation**, from `FinKinds`. -/
theorem fin_all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0 := by
  intro Ac s a c fin h hc hpl _
  cases c with
  | Null => exact fin_noop h (Or.inl rfl)
  | Untyped => exact fin_noop h (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | IrqControl => exact fin_noop h (Or.inr (Or.inr (Or.inl rfl)))
  | Domain => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | SchedControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | AsidControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | IoPortControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  | CNode => exact fin_cnode h hc
  | Zombie => exact fin_zombie h hc
  | PageTable => exact fin_vs hA P h (Or.inl ⟨_, _, _, _, rfl⟩)
  | Pml4 => exact fin_vs hA P h (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | AsidPool => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | Frame x1 x2 x3 x4 x5 e x6 x7 =>
    cases e
    · exact fin_vs hA P h (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
    · exact G.arch _ _ _ _ _ h hc hpl (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))
  | Endpoint => exact G.ep _ _ _ _ _ h hc hpl ⟨_, _, _, _, _, _, rfl⟩
  | Notification => exact G.ntfn _ _ _ _ _ h hc hpl ⟨_, _, _, _, rfl⟩
  | Reply => exact G.reply _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | SchedContext => exact G.sc _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | Thread => exact G.thread _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | IrqHandler => exact G.irq _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | PageDirectory => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | Pdpt => exact fin_vs hA P h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩)))))
  | Vcpu => exact G.arch _ _ _ _ _ h hc hpl (Or.inl ⟨_, rfl⟩)
  | Ept => exact G.arch _ _ _ _ _ h hc hpl (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
  | IoPort => exact G.ioPort _ _ _ _ _ h hc hpl ⟨_, _, _, rfl⟩

/-! ## `empty_slot` and `post_cap_deletion` -/

/-- A kernel-global word write. -/
theorem Cur0.ks {s0 s : S} {o v : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ho : o.val < 13568)
    (h8 : o.val % 8 = 0) : obj.ks_set st s o v ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.bxi
  have q := hb.1.choose_spec.choose_spec
  have hSg := hb.2.2.2.1
  refine WP.spec_mono (obj.ks_set.spec s o v) fun s' e => ?_
  subst e
  exact h.capw (writesIn_wr (ks_aligned q ho h8)) fun b e => e ▸ Or.inr ⟨hSg.ksΩ o ho h8, fun hb' => by
    have := hSg.ks _ hb'; rw [ks_val q ho] at this; omega⟩

theorem ioport.apply.cur0 {s0 s : S} {w p : U64} {set : Bool} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hw : w.val < 1024) : ioport.apply st s w p set ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ioport.apply ioport.word_off
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 5344 + 8 * w.val) ?_ fun o ho => ?_
  · refine WP.spec_bind P0.Consts.layout.ks.IOPORT_BITMAP.spec fun b eb => ?_
    subst eb
    refine (WP.spec_ok _).2 ?_
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.obj.ks_get.p0 st s _ hS) fun v _ => ?_
  split
  · exact h.ks (by omega) (by omega)
  · exact h.ks (by omega) (by omega)

/-! ## Cap-slot word writes -/

theorem cte_next : layout.cte.NEXT = 24#u64 := by unfold layout.cte.NEXT; rfl
theorem cte_prev : layout.cte.PREV = 16#u64 := by unfold layout.cte.PREV; rfl

theorem slot_wr {s : S} {x o v : U64} (hx : SlotW T Ω Sg x) (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    st.write s (core.num.U64.wrapping_add x o) v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  refine WP.spec_mono (LawfulStore.write_spec _ _ _) fun s' e => ?_
  subst e
  have ha : Aligned (core.num.U64.wrapping_add x o) := by
    have := hx.1
    unfold Aligned at this ⊢; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact (writesIn_wr ha).mono fun b e => e ▸ hx.2 o ho h8

theorem slot_wr0 {s : S} {x v : U64} (hx : SlotW T Ω Sg x) :
    st.write s x v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  have h0 : core.num.U64.wrapping_add x 0#u64 = x := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have := slot_wr (st := st) (s := s) (v := v) (o := 0#u64) hx (by simp) (by simp)
  rwa [h0] at this

theorem obj.Slot.set_next.capw {s : S} {x n : U64} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_next st x s n ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_next obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_prev.capw {s : S} {x n : U64} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_prev st x s n ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_prev
  simp only [lift, bind_ok, cte_prev]
  exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_first_badged.capw {s : S} {x : U64} {v : Bool} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_first_badged st x s v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_first_badged obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_FIRST_BADGED.spec fun i1 _ => ?_
  split <;> exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_revocable.capw {s : S} {x : U64} {v : Bool} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_revocable st x s v ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_revocable obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_REVOCABLE.spec fun i1 _ => ?_
  split <;> exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.set_next_flags.capw {s : S} {x n : U64} {r f : Bool} (hx : SlotW T Ω Sg x) :
    obj.Slot.set_next_flags st x s n r f ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.set_next_flags obj.Slot.next_word
  simp only [lift, bind_ok, cte_next]
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun w _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_REVOCABLE.spec fun i1 _ => ?_
  refine WP.spec_bind P0.Consts.obj.MDB_FIRST_BADGED.spec fun i3 _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
  exact slot_wr hx (by simp) (by simp)

theorem obj.Slot.clear.capw {s : S} {x : U64} (hx : SlotW T Ω Sg x) :
    obj.Slot.clear st x s ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  unfold obj.Slot.clear
  simp only [lift, bind_ok]
  refine WP.spec_bind (slot_wr0 hx) fun s1 w1 => ?_
  refine WP.spec_bind (slot_wr hx (o := 8#u64) (by simp) (by simp)) fun s2 w2 => ?_
  refine WP.spec_bind (slot_wr hx (o := 16#u64) (by simp) (by simp)) fun s3 w3 => ?_
  exact WP.spec_mono (slot_wr hx (o := 24#u64) (by simp) (by simp)) fun s4 w4 =>
    ((w1.trans1 w2).trans1 w3).trans1 w4

/-! ## `post_cap_deletion` and `empty_slot` -/

theorem ioport.set_mask.cur0 {s0 s : S} {f l : U64} {set : Bool} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hl : l.val < 65536) (hfl : f.val ≤ l.val) :
    ioport.set_mask st s f l set ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold ioport.set_mask
  step as ⟨lw, hlw⟩
  step as ⟨hw, hhw⟩
  have b1 : lw.val ≤ hw.val := by
    rw [hlw, hhw, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_div_right hfl
  have b2 : hw.val < 1024 := by rw [hhw, Nat.shiftRight_eq_div_pow]; omega
  simp only [lift, bind_ok]
  split
  · refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
    exact ioport.apply.cur0 h (by omega)
  · rename_i hne
    have b3 : lw.val < hw.val := by
      rcases Nat.lt_or_eq_of_le b1 with e | e
      · exact e
      · exact absurd (UScalar.eq_of_val_eq e) hne
    refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
    refine WP.spec_bind (ioport.apply.cur0 h (by omega)) fun s1 h1 => ?_
    step as ⟨w, hw1⟩
    refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
    · unfold ioport.set_mask_loop
      apply loop.spec_decr_nat (measure := fun y : S × U64 => hw.val - y.2.val)
        (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
      · rintro ⟨s3, w3⟩ h3
        simp only at h3
        dsimp only
        unfold ioport.set_mask_loop.body
        split
        · rename_i hlt
          have hlt' : w3.val < hw.val := by simpa using hlt
          refine WP.spec_bind (ioport.apply.cur0 h3 (by omega)) fun s4 h4 => ?_
          step as ⟨w4, hw4⟩
          exact ⟨h4, by omega⟩
        · exact (WP.spec_ok _).2 h3
      · exact h1
    · refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
      exact ioport.apply.cur0 h2 b2

theorem objects.post_cap_deletion.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    {c : capability.Cap} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    objects.post_cap_deletion st ar s a c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  unfold objects.post_cap_deletion
  cases c
  all_goals try exact (WP.spec_ok _).2 h
  · rename_i irq
    have hi := hc.2.1 irq rfl
    unfold interrupt.deleted_irq_handler
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
    · unfold interrupt.set_irq_state interrupt.state_off
      simp only [lift, bind_ok]
      refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
      · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
        subst eb
        refine (WP.spec_ok _).2 ?_
        simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (h.ks (v := interrupt.IRQ_INACTIVE) (by omega) (by omega)) fun s1 h1 => ?_
      exact WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 h1
    rintro ⟨s1, a1⟩ h1
    exact WP.spec_bind (hA.irq_free a1 irq) fun a2 _ => (WP.spec_ok _).2 h1
  · rename_i f l o
    obtain ⟨hfl, hl⟩ := hc.2.2.1 f l o rfl
    unfold ioport.free_ioports
    exact WP.spec_bind (ioport.set_mask.cur0 h hl hfl) fun s1 h1 => (WP.spec_ok _).2 h1

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of a cap slot, its cleanup cap typed. -/
theorem cdt.empty_slot.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact objects.post_cap_deletion.cur0 hA (h2.capw w3 fun _ hb => hb) hc

/-! ## The deferred delete -/

theorem Cur0.cw {s0 s : S} {m : Result S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hm : m ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄) : m ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
  WP.spec_mono hm fun _ w => h.capw w fun _ hb => hb

set_option maxHeartbeats 2000000 in
/-- **`cdt.swap`** of two cap slots. -/
theorem cdt.swap.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {c1 c2 : capability.Cap} {x1 x2 : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.swap
  refine WP.spec_bind (h.cw (obj.Slot.set_cap.capw h1)) fun sa ha => ?_
  refine WP.spec_bind (ha.cw (obj.Slot.set_cap.capw h2)) fun sb hb => ?_
  obtain ⟨Acb, hbb⟩ := hb.bxi
  refine WP.spec_bind (P.prev Acb sb x1 hb.fr hbb h1) fun p1 hp1 => ?_
  refine WP.spec_bind (P.next Acb sb x1 hb.fr hbb h1) fun n1 hn1 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 sb hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 sb hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sc hc => ?_
  · split
    · exact (WP.spec_ok _).2 hb
    · rename_i e; exact hb.cw (obj.Slot.set_next.capw (hp1.resolve_left (by simpa using e)))
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sd hd => ?_
  · split
    · exact (WP.spec_ok _).2 hc
    · rename_i e; exact hc.cw (obj.Slot.set_prev.capw (hn1.resolve_left (by simpa using e)))
  obtain ⟨Acd, hbd⟩ := hd.bxi
  refine WP.spec_bind (P.prev Acd sd x2 hd.fr hbd h2) fun p2 hp2 => ?_
  refine WP.spec_bind (P.next Acd sd x2 hd.fr hbd h2) fun n2 hn2 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 sd hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 sd hS) fun f2 _ => ?_
  refine WP.spec_bind (hd.cw (obj.Slot.set_prev.capw h1)) fun s5 h5 => ?_
  refine WP.spec_bind (h5.cw (obj.Slot.set_next_flags.capw h1)) fun s6 h6 => ?_
  refine WP.spec_bind (h6.cw (obj.Slot.set_prev.capw h2)) fun s7 h7 => ?_
  refine WP.spec_bind (h7.cw (obj.Slot.set_next_flags.capw h2)) fun s12 h12 => ?_
  refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s13 h13 => ?_
  · split
    · exact (WP.spec_ok _).2 h12
    · rename_i e; exact h12.cw (obj.Slot.set_next.capw (hp2.resolve_left (by simpa using e)))
  split
  · exact (WP.spec_ok _).2 h13
  · rename_i e; exact h13.cw (obj.Slot.set_prev.capw (hn2.resolve_left (by simpa using e)))

theorem cdt.cap_swap_for_delete.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {x1 x2 : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete obj.Slot.Insts.CoreCmpPartialEqSlot.eq
  simp only [bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x1 s hS) fun c1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s hS) fun c2 _ => ?_
  exact cdt.swap.cur0 P h h1 h2

set_option hygiene false in
/-- The preemption-point tail of a deferred round (`Cur0` at `s3`). -/
local macro "dtail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h3) ?_
  rintro ⟨rr, s4, a4⟩ h4
  try simp only [uncurry_apply_pair] at h4 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h4, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred`** of a cap slot: `Cur0`, the cleanup cap typed. -/
theorem cdt.finalise_slot_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0)
    {a : A} {x : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (P.cap Acx s1 x h1.fr hbx hx) fun c ⟨hc, hpl⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (F Ac s1 a1 c fin h1 hc hpl trivial) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.cdt.cap_removable.p0 rem x) fun br _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (h2'.cw (obj.Slot.set_cap.capw (c := rem) hx)) fun s2 h2 => ?_
    refine WP.spec_bind (P0.cdt.cap_cyclic_zombie.p0 rem x) fun bz _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s3 h3 => ?_
    · split
      all_goals try exact (WP.spec_ok _).2 h2
      rename_i zp zt zn
      exact cdt.cap_swap_for_delete.cur0 P h2 (hrem.2.2.2.2.1 zp zt zn rfl).1 hx
    dtail
  · exact h

/-- **`delete_deferred`** of a cap slot. -/
theorem cdt.delete_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun _ => True) s0)
    {a : A} {x : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.cur0 hA P F h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (cdt.empty_slot.cur0 hA P h1 hx (hv1 v rfl)) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

/-- **`DelGaps`, discharged** from placement and the named finalisations. -/
theorem delGaps_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinKindsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 where
  cap := P.cap
  fin Ac s a c fin h hc hpl := fin_all hA P G Ac s a c fin h hc hpl trivial
  deferred _ _ _ _ h hx := cdt.delete_deferred.cur0 hA P (fin_all hA P G) h hx
  empty _ _ _ _ _ h hx hc := cdt.empty_slot.cur0 hA P h hx hc
  next := P.next

end

end Fl4Proofs.P1
