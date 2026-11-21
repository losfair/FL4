/-
P3 (DESIGN.md §9), invariant line G1 (il2): **IfLiveT across the arch performs**
(`PerfGapILA` proved; spec side only).

The arch performs write a cap only (i) at the start of a map, the decoded cap
over the invoked slot (ut8's `MapOK`: `RefEq` to the slot's cap, so a thread
cap is replaced by itself: `tcs_refEq`), (ii) after an unmap, the re-read arch
cap updated in place (the slot held the decoded arch cap, and the unmap writes
no cap: ut1's `UK` frames; `il_preRe`), (iii) the ASID pool assign over the
read PML4 cap, (iv) `cap_insert` (IOPort control, DeriveSubframe, the pool cap)
and (v) MakePool's free-index rewrite of the parent untyped after a detype of
a childless untyped's region (null slots, ut4's `RegNull`) and a retype at the
freed frame. **`perfGapILA : PerfGapILA`**; `perfGapIL : PerfGapIL`.
-/
import Fl4Proofs.P3.SpecInvNtfnQLU
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem tcs_refEq {K : List ObjRef} {σ : State Unit} {sl : CslotPtr} {c0 c : Cap}
    (hs : SInvU.capAt σ sl = some c0) (hr : RefEq c0 c) : TcSafe K σ sl c :=
  fun t ht => Or.inl (refEq_tc hr t (by rw [hs] at ht; injection ht))

/-- A map: the decoded cap over the invoked slot first, then no cap write. -/
theorem il_mapHead {α : Type} (c c0 : Cap) (sl : CslotPtr) (σ : State Unit) {k : Unit → NonDet (State Unit) α}
    (hs : SInvU.capAt σ sl = some c0) (hr : RefEq c0 c) (hk : ∀ u, ILK Kq (k u)) :
    IKp (IL Kq) σ (setCap (Z := Unit) c sl >>= k) :=
  ikp_bind (il_setCap_p c sl σ fun _ => tcs_refEq hs hr) (fun u => hk u)

/-- The re-read of an arch cap and its in-place update. -/
theorem il_reread (sl : CslotPtr) (f : ArchCap → ArchCap) (σ : State Unit) (hn : NTC σ sl) :
    IKp (IL Kq) σ (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (.archObjectCap (f cap)) sl) := by
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨z1, h1, hz⟩ := hz
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt h1
  rw [Set.mem_singleton_iff.1 hz] at hy
  have e : z1.2 = σ := e1
  rw [e] at hy
  exact il_setCap_nt _ _ σ hn hσ y hy

/-- A cap-keeping prefix, then the re-read update. -/
theorem il_preRe {α : Type} {m : NonDet (State Unit) α} (hL : ILK Kq m) (hU : ∀ v, UK v m) (sl : CslotPtr)
    (f : ArchCap → ArchCap) (σ : State Unit) (hn : NTC σ sl) :
    IKp (IL Kq) σ (m >>= fun _ => NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (.archObjectCap (f cap)) sl) := by
  intro hσ y ⟨z, hz, hy⟩
  have hv := hU _ σ rfl z hz
  exact il_reread sl f z.2 (fun t e => hn t (by rw [← capAt_view hv]; exact e)) (hL σ hσ z hz) y hy

theorem ntc_arch {σ : State Unit} {sl : CslotPtr} {a : ArchCap} (h : SInvU.capAt σ sl = some (.archObjectCap a)) :
    NTC σ sl := fun t e => by rw [h] at e; cases e

/-- The applied form of `il_preRe`. -/
theorem il_unmapGen {α : Type} {m : NonDet (State Unit) α} (hL : ILK Kq m) (hU : ∀ v, UK v m) {sl : CslotPtr}
    {f : ArchCap → ArchCap} {σ : State Unit} {x : Unit × State Unit} (hn : NTC σ sl) (hσ : IL Kq σ)
    (hx : x ∈ ((m >>= fun _ => NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (.archObjectCap (f cap)) sl) σ).1) : IL Kq x.2 :=
  il_preRe hL hU sl f σ hn hσ x hx

/-- The applied form, by destructuring the prefix's bind. -/
theorem il_unmapPre {α β : Type} {m : NonDet (State Unit) α} (hL : ILK Kq m) (hU : ∀ v, UK v m) {sl : CslotPtr}
    {k : α → NonDet (State Unit) β} {σ : State Unit} {x : β × State Unit} (hn : NTC σ sl) (hσ : IL Kq σ)
    (hk : ∀ a s, NTC s sl → IL Kq s → ∀ y ∈ (k a s).1, IL Kq y.2) (hx : x ∈ ((m >>= k) σ).1) : IL Kq x.2 := by
  obtain ⟨z, hz, hx⟩ := hx
  have hv := hU _ σ rfl z hz
  exact hk z.1 z.2 (fun t e => hn t (by rw [← capAt_view hv]; exact e)) (hL σ hσ z hz) x hx

/-- `perform_page_invocation_unmap` of the slot's own page cap. -/
theorem il_pageUnmapF (a : ArchCap) (sl : CslotPtr) (σ : State Unit) (hc : SInvU.capAt σ sl = some (.archObjectCap a)) :
    IKp (IL Kq) σ (performPageInvocationUnmap (Z := Unit) a sl) := by
  intro hσ x hx
  cases a
  case pageCap dev base r mt sz mapped =>
    cases mapped with
    | none =>
      unfold performPageInvocationUnmap at hx; dsimp only at hx
      exact il_reread _ _ σ (ntc_arch hc) hσ x hx
    | some av =>
      obtain ⟨as, va⟩ := av
      unfold performPageInvocationUnmap at hx; dsimp only at hx
      exact il_unmapPre (by il_auto) (fun _ => by uk_auto) (ntc_arch hc) hσ (fun _ s hs hs' y hy => il_reread _ _ s hs hs' y hy) hx
  all_goals unfold performPageInvocationUnmap at hx; exact (show False from hx).elim

/-! ## The x64 performs (one declaration per invocation) -/

theorem il_ptUnmapR (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (sl : CslotPtr) (σ : State Unit)
    (hn : NTC σ sl) : IKp (IL Kq) σ (performPageTableInvocation (Z := Unit) (.pageTableUnmap (.archObjectCap (.pageTableCap p ma)) sl)) := by
  intro hσ x hx
  unfold performPageTableInvocation at hx
  cases ma with
  | none =>
    dsimp only at hx
    exact il_reread _ _ σ hn hσ x hx
  | some av =>
    obtain ⟨as, va⟩ := av
    refine il_unmapPre (by il_auto) (fun _ => by uk_auto) hn hσ (fun _ s1 h1 h1' y1 hy1 => ?_) hx
    refine il_unmapPre (ik_pure _) (fun _ => ik_pure _) h1 h1' (fun _ s2 h2 h2' y2 hy2 => ?_) hy1
    refine il_unmapPre (ik_pure _) (fun _ => ik_pure _) h2 h2' (fun _ s3 h3 h3' y3 hy3 => ?_) hy2
    exact il_unmapPre (by il_auto) (fun _ => by uk_auto) h3 h3'
      (fun _ s4 h4 h4' y4 hy4 => il_reread _ _ s4 h4 h4' y4 hy4) hy3

theorem ptUnmap_fail (c : Cap) (sl : CslotPtr) (h : ∀ p ma, c ≠ .archObjectCap (.pageTableCap p ma)) :
    performPageTableInvocation (Z := Unit) (.pageTableUnmap c sl) = NonDet.fail := by
  unfold performPageTableInvocation
  split
  · rename_i heq; cases heq
  · rename_i heq; cases heq; exact absurd rfl (h _ _)
  · rfl

theorem il_ptInv (iv : PageTableInvocation) (σ : State Unit) (hσ : IL Kq σ) (hok : ArchSpecOKN (uV σ) (.invokePageTable iv)) :
    ∀ x ∈ (performPageTableInvocation (Z := Unit) iv σ).1, IL Kq x.2 := by
  intro x hx
  cases iv with
  | pageTableMap c sl e eSlot vs =>
    obtain ⟨c0, hs, hr, -⟩ := hok
    simp only [performPageTableInvocation] at hx
    exact il_mapHead c c0 sl σ hs hr (fun _ => by il_auto) hσ x hx
  | pageTableUnmap c sl =>
    have hc : SInvU.capAt σ sl = some c := hok
    by_cases hm : ∃ p ma, c = .archObjectCap (.pageTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hm
      exact il_ptUnmapR p ma sl σ (ntc_arch hc) hσ x hx
    · rw [ptUnmap_fail c sl (fun p ma e => hm ⟨p, ma, e⟩)] at hx
      exact (show False from hx).elim

theorem il_pdUnmapR (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (sl : CslotPtr) (σ : State Unit)
    (hn : NTC σ sl) : IKp (IL Kq) σ (performPageDirectoryInvocation (Z := Unit) (.pageDirectoryUnmap (.archObjectCap (.pageDirectoryCap p ma)) sl)) := by
  intro hσ x hx
  unfold performPageDirectoryInvocation at hx
  cases ma with
  | none =>
    dsimp only at hx
    exact il_reread _ _ σ hn hσ x hx
  | some av =>
    obtain ⟨as, va⟩ := av
    refine il_unmapPre (by il_auto) (fun _ => by uk_auto) hn hσ (fun _ s1 h1 h1' y1 hy1 => ?_) hx
    refine il_unmapPre (ik_pure _) (fun _ => ik_pure _) h1 h1' (fun _ s2 h2 h2' y2 hy2 => ?_) hy1
    refine il_unmapPre (ik_pure _) (fun _ => ik_pure _) h2 h2' (fun _ s3 h3 h3' y3 hy3 => ?_) hy2
    exact il_unmapPre (by il_auto) (fun _ => by uk_auto) h3 h3'
      (fun _ s4 h4 h4' y4 hy4 => il_reread _ _ s4 h4 h4' y4 hy4) hy3

theorem pdUnmap_fail (c : Cap) (sl : CslotPtr) (h : ∀ p ma, c ≠ .archObjectCap (.pageDirectoryCap p ma)) :
    performPageDirectoryInvocation (Z := Unit) (.pageDirectoryUnmap c sl) = NonDet.fail := by
  unfold performPageDirectoryInvocation
  split
  · rename_i heq; cases heq
  · rename_i heq; cases heq; exact absurd rfl (h _ _)
  · rfl

theorem il_pdInv (iv : PageDirectoryInvocation) (σ : State Unit) (hσ : IL Kq σ) (hok : ArchSpecOKN (uV σ) (.invokePageDirectory iv)) :
    ∀ x ∈ (performPageDirectoryInvocation (Z := Unit) iv σ).1, IL Kq x.2 := by
  intro x hx
  cases iv with
  | pageDirectoryMap c sl e eSlot vs =>
    obtain ⟨c0, hs, hr, -⟩ := hok
    simp only [performPageDirectoryInvocation] at hx
    exact il_mapHead c c0 sl σ hs hr (fun _ => by il_auto) hσ x hx
  | pageDirectoryUnmap c sl =>
    have hc : SInvU.capAt σ sl = some c := hok
    by_cases hm : ∃ p ma, c = .archObjectCap (.pageDirectoryCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hm
      exact il_pdUnmapR p ma sl σ (ntc_arch hc) hσ x hx
    · rw [pdUnmap_fail c sl (fun p ma e => hm ⟨p, ma, e⟩)] at hx
      exact (show False from hx).elim

theorem il_pdptUnmapR (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (sl : CslotPtr) (σ : State Unit)
    (hn : NTC σ sl) : IKp (IL Kq) σ (performPdptInvocation (Z := Unit) (.pdptUnmap (.archObjectCap (.pdPointerTableCap p ma)) sl)) := by
  intro hσ x hx
  unfold performPdptInvocation at hx
  cases ma with
  | none =>
    dsimp only at hx
    exact il_reread _ _ σ hn hσ x hx
  | some av =>
    obtain ⟨as, va⟩ := av
    refine il_unmapPre (by il_auto) (fun _ => by uk_auto) hn hσ (fun _ s1 h1 h1' y1 hy1 => ?_) hx
    refine il_unmapPre (ik_pure _) (fun _ => ik_pure _) h1 h1' (fun _ s2 h2 h2' y2 hy2 => ?_) hy1
    refine il_unmapPre (ik_pure _) (fun _ => ik_pure _) h2 h2' (fun _ s3 h3 h3' y3 hy3 => ?_) hy2
    exact il_unmapPre (by il_auto) (fun _ => by uk_auto) h3 h3'
      (fun _ s4 h4 h4' y4 hy4 => il_reread _ _ s4 h4 h4' y4 hy4) hy3

theorem pdptUnmap_fail (c : Cap) (sl : CslotPtr) (h : ∀ p ma, c ≠ .archObjectCap (.pdPointerTableCap p ma)) :
    performPdptInvocation (Z := Unit) (.pdptUnmap c sl) = NonDet.fail := by
  unfold performPdptInvocation
  split
  · rename_i heq; cases heq
  · rename_i heq; cases heq; exact absurd rfl (h _ _)
  · rfl

theorem il_pdptInv (iv : PdptInvocation) (σ : State Unit) (hσ : IL Kq σ) (hok : ArchSpecOKN (uV σ) (.invokePDPT iv)) :
    ∀ x ∈ (performPdptInvocation (Z := Unit) iv σ).1, IL Kq x.2 := by
  intro x hx
  cases iv with
  | pdptMap c sl e eSlot vs =>
    obtain ⟨c0, hs, hr, -⟩ := hok
    simp only [performPdptInvocation] at hx
    exact il_mapHead c c0 sl σ hs hr (fun _ => by il_auto) hσ x hx
  | pdptUnmap c sl =>
    have hc : SInvU.capAt σ sl = some c := hok
    by_cases hm : ∃ p ma, c = .archObjectCap (.pdPointerTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hm
      exact il_pdptUnmapR p ma sl σ (ntc_arch hc) hσ x hx
    · rw [pdptUnmap_fail c sl (fun p ma e => hm ⟨p, ma, e⟩)] at hx
      exact (show False from hx).elim

theorem il_pageInv (iv : PageInvocation) (σ : State Unit) (hσ : IL Kq σ) (hok : ArchSpecOKN (uV σ) (.invokePage iv)) :
    ∀ x ∈ (performPageInvocation (Z := Unit) iv σ).1, IL Kq x.2 := by
  intro x hx
  cases iv with
  | pageMap c sl ent vs =>
    obtain ⟨c0, hs, hr, -⟩ := hok
    obtain ⟨e, eslot⟩ := ent
    simp only [performPageInvocation] at hx
    obtain ⟨z, hz, hx⟩ := hx
    have hz1 : IL Kq z.2 := il_setCap_p c sl σ (fun _ => tcs_refEq hs hr) hσ z hz
    cases e <;> exact (show ILK Kq _ from by (try dsimp only); il_auto) z.2 hz1 x hx
  | pageUnmap a sl =>
    have hc : SInvU.capAt σ sl = some (.archObjectCap a) := hok
    unfold performPageInvocation at hx
    cases a
    case pageCap dev base r mt sz mapped =>
      dsimp only at hx
      cases mapped with
      | none => exact (show ILK Kq _ from by (try dsimp only); il_auto) σ hσ x hx
      | some av =>
        cases mt
        case vmVSpaceMap =>
          dsimp only at hx
          obtain ⟨z, hz, hx⟩ := hx
          exact ik_pure _ _ (il_pageUnmapF _ sl σ hc hσ z hz) x hx
        all_goals exact (show ILK Kq _ from by (try dsimp only); il_auto) σ hσ x hx
    all_goals exact (show False from hx).elim
  | pageGetAddr p =>
    unfold performPageInvocation at hx
    rw [Set.mem_singleton_iff.1 hx]; exact hσ

theorem il_asidPoolInv (iv : AsidPoolInvocation) : ILK Kq (performAsidPoolInvocation (Z := Unit) iv) := by
  cases iv with
  | assign asid pool sl =>
    unfold performAsidPoolInvocation
    refine ik_getCap_bind' (fun s c hc => ?_)
    split
    · exact ikp_bind (il_setCap_nt _ _ s (ntc_arch hc)) (fun _ => il_storeAsidPoolEntry _ _ _)
    · exact fun _ y hy => hy.elim

theorem il_archPerform (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a) (σ : State Unit)
    (hσ : IL Kq σ) (hok : ArchSpecOKN (uV σ) i) :
    ∀ y ∈ ((archPerformInvocation (Z := Unit) i).run σ).1, IL Kq y.2 := by
  intro y hy
  simp only [archPerformInvocation] at hy
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
  show IL Kq x.2
  cases i with
  | invokeASIDControl a => exact absurd rfl (hm a)
  | invokePageTable iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (il_ptInv iv σ hσ hok z hz) x hx
  | invokePageDirectory iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (il_pdInv iv σ hσ hok z hz) x hx
  | invokePDPT iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (il_pdptInv iv σ hσ hok z hz) x hx
  | invokePage iv => exact il_pageInv iv σ hσ hok x hx
  | invokeASIDPool iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (il_asidPoolInv iv σ hσ z hz) x hx
  | invokeIOPort iv => exact il_performIoPortInvocation iv σ hσ x hx
  | invokeIOPortControl iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (il_performIoportControlInvocation iv σ hσ z hz) x hx

/-! ## MakePool -/

theorem il_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hσ : IL Kq σ)
    (hU : UtInv'' σ) (hok : MpOKN (uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, IL Kq y.2 := by
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR frame page_bits → c = .nullCap :=
    fun p c hp hm => regNull_of hU.2.1 hU.2.2.1 parent dev frame page_bits fi hc hk p c hp hm
  have hfr : frame ∈ SInvU.delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc
    exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  intro y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨hb1, ht1⟩ := il_deleteObjects_p (Kq := Kq) frame page_bits σ hR hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := deleteObjects_out h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hfr]
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hp1 : NTC y1.2 parent := ntc_tcf ht1 (fun t e => by rw [hc'] at e; cases e)
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : IL Kq y3.2 := il_setCap_nt _ _ _ hp1 hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := (il_retypeRegionWith_p (Kq := Kq) objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'; exact hn3) hb3 y4 h4).1
  refine (?_ : ILK Kq _) y4.2 hb4 y hy
  il_auto

/-! ## `PerfGapILA` -/

theorem perfGapILA : PerfGapILA := by
  intro N K ai σ hσ hN hD y hy
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) (.invokeArchObject ai) :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
  have hok : ArchOKN (uV σ) ai := hf
  cases ai with
  | spec i =>
    by_cases hm : ∃ a, i = .invokeASIDControl a
    · obtain ⟨a, rfl⟩ := hm
      cases a with
      | makePool frame slot parent base =>
        simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
        obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
        obtain ⟨z, hz, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hx]
        exact il_makePool frame slot parent base σ hσ.1.1 hσ.2.1 hok z hz
    · simp only [fl4ArchPerformInvocation] at hy
      exact il_archPerform i (fun a e => hm ⟨a, e⟩) σ hσ.1.1 hok y hy
  | deriveSubframe iv =>
    simp only [fl4ArchPerformInvocation, archNoReturn, performDeriveSubframe] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    refine (?_ : ILK K _) σ hσ.1.1 x hx
    il_auto
  | _ =>
    refine (?_ : ILKE K _) σ hσ.1.1 y hy
    simp only [fl4ArchPerformInvocation, archNoReturn]
    il_auto

/-- **`PerfGapIL` proved** (no premise). -/
theorem perfGapIL : PerfGapIL := perfGapIL_of perfGapILA

end

end Fl4Proofs.P3.SInv
