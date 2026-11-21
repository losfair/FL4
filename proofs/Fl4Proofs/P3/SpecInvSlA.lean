/-
P3 (DESIGN.md §9), invariant line G1 (sl4): **`slGap : SlGap`** — the arch
performs keep `SL I K ∧ NtfnScB`, and with SpecInvSlU's untyped / MakePool
lemmas sl3's gap is closed (spec side only). il2's SpecInvNtfnQLA with `NCap`:

* **The map's invoked slot holds no thread / SC cap** (`MapNC`, decode fact
  `okv_archNC` / `okv_invANC`): ut8's `MapOK` gives only `RefEq` between the
  slot's cap and the written one, which does not separate an SC cap from an
  endpoint cap; the arch decode dispatches on the invoked slot's arch cap, and a
  map's slot is that slot.
* The unmaps re-read the slot's own arch cap (`sl_reread`, `sl_unmapPre`); the
  ASID-pool assign overwrites the read PML4 cap; `cap_insert` (IOPort control,
  DeriveSubframe) is sl1's `sl_capInsert`.
* NtfnScB: every arch perform but MakePool is a generated `nb_*` leaf.
* **`slGap`**.
-/
import Fl4Proofs.P3.SpecInvSlU
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {I : ObjRef × ObjRef} {K : List ObjRef}

/-! ## The decode fact -/

/-- No thread / SC cap in the view's slot `sl`. -/
def MapNC (w : UView) (sl : CslotPtr) : Prop := ∀ p c0, w.2.1 sl = some c0 → ¬ NCap p c0

/-- A map's invoked slot holds no thread / SC cap. -/
def ArchNCS (w : UView) : ArchInvocation → Prop
  | .invokePageTable (.pageTableMap _ sl _ _ _) => MapNC w sl
  | .invokePageDirectory (.pageDirectoryMap _ sl _ _ _) => MapNC w sl
  | .invokePDPT (.pdptMap _ sl _ _ _) => MapNC w sl
  | .invokePage (.pageMap _ sl _ _) => MapNC w sl
  | _ => True

def ArchNCF (w : UView) : Fl4ArchInvocation → Prop
  | .spec i => ArchNCS w i
  | _ => True

def InvANC (w : UView) : Fl4Invocation → Prop
  | .invokeArchObject ai => ArchNCF w ai
  | _ => True

set_option maxHeartbeats 8000000 in
theorem okv_archNC {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap cap)) (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) :
    OkV w (ArchNCS w) (archDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  have hcps : ∀ c ∈ ex.map Prod.fst, ∃ s, w.2.1 s = some c := by
    intro c h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    exact ⟨q.2, hex q hq⟩
  have hm : MapNC w cte := fun p c0 h => by rw [hc] at h; cases h; exact id
  cases cap
  case pdPointerTableCap p m =>
    simp only [archDecodeInvocation, decodePdptInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hm
  case pageDirectoryCap p m =>
    simp only [archDecodeInvocation, decodePageDirectoryInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hm
  case pageTableCap p m =>
    simp only [archDecodeInvocation, decodePageTableInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hm
  case pageCap dev p R mt sz m =>
    simp only [archDecodeInvocation, decodePageInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hm
  case ioPortControlCap =>
    simp only [archDecodeInvocation]
    exact okv_mono (okv_decodeIoportControlN label args cte _ _ hc hcps) fun i ⟨j, e, _⟩ => by subst e; trivial
  case ioPortCap f l =>
    simp only [archDecodeInvocation]
    unfold decodePortInvocation
    split <;> okv_noasid
  all_goals (simp only [archDecodeInvocation]; okv_noasid)

theorem okv_fl4ArchNC {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap cap)) (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) :
    OkV w (ArchNCF w) (fl4ArchDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  cases cap
  case pageCap dev p R mt sz m =>
    simp only [fl4ArchDecodeInvocation]
    exact okv_ite (okv_liftME (okv_triv fun _ => trivial))
      (okv_ite (okv_liftME (okv_triv fun _ => trivial)) (okv_liftME (okv_archNC label args xs cte _ ex hc hex)))
  case pml4Cap p m =>
    simp only [fl4ArchDecodeInvocation]
    exact okv_ite (okv_liftME (okv_triv fun _ => trivial)) (okv_liftME (okv_archNC label args xs cte _ ex hc hex))
  all_goals (simp only [fl4ArchDecodeInvocation]; exact okv_liftME (okv_archNC label args xs cte _ ex hc hex))

theorem okv_invANC {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : w.2.1 sl = some cap)
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (InvANC w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | archObjectCap ac =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_fl4ArchNC label args ci sl ac ex hc hex)
  | _ =>
    unfold fl4DecodeInvocation
    (try dsimp only)
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

theorem invANC_of {w : UView} {inv : Fl4Invocation} (hD : DecodedFrom w inv) : InvANC w inv := by
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  exact okv_invANC fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem

/-! ## The arch performs -/

theorem nnc_arch {σ : State Unit} {sl : CslotPtr} {a : ArchCap} (h : SInvU.capAt σ sl = some (.archObjectCap a)) :
    NNC σ sl := nnc_of h fun _ e => e

/-- The re-read of an arch cap and its in-place update. -/
theorem sl_reread (sl : CslotPtr) (f : ArchCap → ArchCap) (σ : State Unit) (hn : NNC σ sl) :
    IKp (SL I K) σ (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (.archObjectCap (f cap)) sl) := by
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨z1, h1, hz⟩ := hz
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt h1
  rw [Set.mem_singleton_iff.1 hz] at hy
  have e : z1.2 = σ := e1
  rw [e] at hy
  exact sl_setCap_nt _ _ σ hn hσ y hy

/-- A cap-keeping prefix, then a continuation given the slot still holds no name. -/
theorem sl_unmapPre {α β : Type} {m : NonDet (State Unit) α} (hL : SLK I K m) (hU : ∀ v, UK v m) {sl : CslotPtr}
    {k : α → NonDet (State Unit) β} {σ : State Unit} {x : β × State Unit} (hn : NNC σ sl) (hσ : SL I K σ)
    (hk : ∀ a s, NNC s sl → SL I K s → ∀ y ∈ (k a s).1, SL I K y.2) (hx : x ∈ ((m >>= k) σ).1) : SL I K x.2 := by
  obtain ⟨z, hz, hx⟩ := hx
  have hv := hU _ σ rfl z hz
  exact hk z.1 z.2 (nnc_view hv hn) (hL σ hσ z hz) x hx

theorem sl_pageUnmapF (a : ArchCap) (sl : CslotPtr) (σ : State Unit)
    (hc : SInvU.capAt σ sl = some (.archObjectCap a)) :
    IKp (SL I K) σ (performPageInvocationUnmap (Z := Unit) a sl) := by
  intro hσ x hx
  cases a
  case pageCap dev base r mt sz mapped =>
    cases mapped with
    | none =>
      unfold performPageInvocationUnmap at hx; dsimp only at hx
      exact sl_reread _ _ σ (nnc_arch hc) hσ x hx
    | some av =>
      obtain ⟨asd, va⟩ := av
      unfold performPageInvocationUnmap at hx; dsimp only at hx
      exact sl_unmapPre (by sl_auto) (fun _ => by uk_auto) (nnc_arch hc) hσ
        (fun _ s hs hs' y hy => sl_reread _ _ s hs hs' y hy) hx
  all_goals unfold performPageInvocationUnmap at hx; exact (show False from hx).elim

macro "sl_unmap4" hn:term:max hσ:term:max hx:term:max : tactic => `(tactic|
  refine sl_unmapPre (by sl_auto) (fun _ => by uk_auto) $hn $hσ (fun _ s1 h1 h1' y1 hy1 => ?_) $hx <;>
  refine sl_unmapPre (ik_pure _) (fun _ => ik_pure _) h1 h1' (fun _ s2 h2 h2' y2 hy2 => ?_) hy1 <;>
  refine sl_unmapPre (ik_pure _) (fun _ => ik_pure _) h2 h2' (fun _ s3 h3 h3' y3 hy3 => ?_) hy2 <;>
  exact sl_unmapPre (by sl_auto) (fun _ => by uk_auto) h3 h3'
    (fun _ s4 h4 h4' y4 hy4 => sl_reread _ _ s4 h4 h4' y4 hy4) hy3)

theorem sl_ptInv (iv : PageTableInvocation) (σ : State Unit) (hσ : SL I K σ)
    (hok : ArchSpecOKN (uV σ) (.invokePageTable iv)) (hnc : ArchNCS (uV σ) (.invokePageTable iv)) :
    ∀ x ∈ (performPageTableInvocation (Z := Unit) iv σ).1, SL I K x.2 := by
  intro x hx
  cases iv with
  | pageTableMap c sl e eSlot vs =>
    simp only [performPageTableInvocation] at hx
    exact ikp_bind (sl_setCap_nt c sl σ hnc) (fun _ => by sl_auto) hσ x hx
  | pageTableUnmap c sl =>
    have hc : SInvU.capAt σ sl = some c := hok
    by_cases hm : ∃ p ma, c = .archObjectCap (.pageTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hm
      unfold performPageTableInvocation at hx
      cases ma with
      | none => dsimp only at hx; exact sl_reread _ _ σ (nnc_arch hc) hσ x hx
      | some av =>
        obtain ⟨asd, va⟩ := av
        sl_unmap4 (nnc_arch hc) hσ hx
    · rw [ptUnmap_fail c sl (fun p ma e => hm ⟨p, ma, e⟩)] at hx
      exact (show False from hx).elim

theorem sl_pdInv (iv : PageDirectoryInvocation) (σ : State Unit) (hσ : SL I K σ)
    (hok : ArchSpecOKN (uV σ) (.invokePageDirectory iv)) (hnc : ArchNCS (uV σ) (.invokePageDirectory iv)) :
    ∀ x ∈ (performPageDirectoryInvocation (Z := Unit) iv σ).1, SL I K x.2 := by
  intro x hx
  cases iv with
  | pageDirectoryMap c sl e eSlot vs =>
    simp only [performPageDirectoryInvocation] at hx
    exact ikp_bind (sl_setCap_nt c sl σ hnc) (fun _ => by sl_auto) hσ x hx
  | pageDirectoryUnmap c sl =>
    have hc : SInvU.capAt σ sl = some c := hok
    by_cases hm : ∃ p ma, c = .archObjectCap (.pageDirectoryCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hm
      unfold performPageDirectoryInvocation at hx
      cases ma with
      | none => dsimp only at hx; exact sl_reread _ _ σ (nnc_arch hc) hσ x hx
      | some av =>
        obtain ⟨asd, va⟩ := av
        sl_unmap4 (nnc_arch hc) hσ hx
    · rw [pdUnmap_fail c sl (fun p ma e => hm ⟨p, ma, e⟩)] at hx
      exact (show False from hx).elim

theorem sl_pdptInv (iv : PdptInvocation) (σ : State Unit) (hσ : SL I K σ)
    (hok : ArchSpecOKN (uV σ) (.invokePDPT iv)) (hnc : ArchNCS (uV σ) (.invokePDPT iv)) :
    ∀ x ∈ (performPdptInvocation (Z := Unit) iv σ).1, SL I K x.2 := by
  intro x hx
  cases iv with
  | pdptMap c sl e eSlot vs =>
    simp only [performPdptInvocation] at hx
    exact ikp_bind (sl_setCap_nt c sl σ hnc) (fun _ => by sl_auto) hσ x hx
  | pdptUnmap c sl =>
    have hc : SInvU.capAt σ sl = some c := hok
    by_cases hm : ∃ p ma, c = .archObjectCap (.pdPointerTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hm
      unfold performPdptInvocation at hx
      cases ma with
      | none => dsimp only at hx; exact sl_reread _ _ σ (nnc_arch hc) hσ x hx
      | some av =>
        obtain ⟨asd, va⟩ := av
        sl_unmap4 (nnc_arch hc) hσ hx
    · rw [pdptUnmap_fail c sl (fun p ma e => hm ⟨p, ma, e⟩)] at hx
      exact (show False from hx).elim

theorem sl_pageInv (iv : PageInvocation) (σ : State Unit) (hσ : SL I K σ)
    (hok : ArchSpecOKN (uV σ) (.invokePage iv)) (hnc : ArchNCS (uV σ) (.invokePage iv)) :
    ∀ x ∈ (performPageInvocation (Z := Unit) iv σ).1, SL I K x.2 := by
  intro x hx
  cases iv with
  | pageMap c sl ent vs =>
    obtain ⟨e, eslot⟩ := ent
    simp only [performPageInvocation] at hx
    obtain ⟨z, hz, hx⟩ := hx
    have hz1 : SL I K z.2 := sl_setCap_nt c sl σ hnc hσ z hz
    cases e <;> exact (show SLK I K _ from by (try dsimp only); sl_auto) z.2 hz1 x hx
  | pageUnmap a sl =>
    have hc : SInvU.capAt σ sl = some (.archObjectCap a) := hok
    unfold performPageInvocation at hx
    cases a
    case pageCap dev base r mt sz mapped =>
      dsimp only at hx
      cases mapped with
      | none => exact (show SLK I K _ from by (try dsimp only); sl_auto) σ hσ x hx
      | some av =>
        cases mt
        case vmVSpaceMap =>
          dsimp only at hx
          obtain ⟨z, hz, hx⟩ := hx
          exact ik_pure _ _ (sl_pageUnmapF _ sl σ hc hσ z hz) x hx
        all_goals exact (show SLK I K _ from by (try dsimp only); sl_auto) σ hσ x hx
    all_goals exact (show False from hx).elim
  | pageGetAddr p =>
    unfold performPageInvocation at hx
    rw [Set.mem_singleton_iff.1 hx]; exact hσ

theorem sl_asidPoolInv (iv : AsidPoolInvocation) : SLK I K (performAsidPoolInvocation (Z := Unit) iv) := by
  cases iv with
  | assign asid pool sl =>
    unfold performAsidPoolInvocation
    refine ik_getCap_bind' (fun s c hc => ?_)
    split
    · exact ikp_bind (sl_setCap_nt _ _ s (nnc_arch hc)) (fun _ => sl_storeAsidPoolEntry _ _ _)
    · exact fun _ y hy => hy.elim

theorem sl_archPerform (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a) (σ : State Unit)
    (hσ : SL I K σ) (hok : ArchSpecOKN (uV σ) i) (hnc : ArchNCS (uV σ) i) :
    ∀ y ∈ ((archPerformInvocation (Z := Unit) i).run σ).1, SL I K y.2 := by
  intro y hy
  simp only [archPerformInvocation] at hy
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
  show SL I K x.2
  cases i with
  | invokeASIDControl a => exact absurd rfl (hm a)
  | invokePageTable iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (sl_ptInv iv σ hσ hok hnc z hz) x hx
  | invokePageDirectory iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (sl_pdInv iv σ hσ hok hnc z hz) x hx
  | invokePDPT iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (sl_pdptInv iv σ hσ hok hnc z hz) x hx
  | invokePage iv => exact sl_pageInv iv σ hσ hok hnc x hx
  | invokeASIDPool iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (sl_asidPoolInv iv σ hσ z hz) x hx
  | invokeIOPort iv => exact sl_performIoPortInvocation iv σ hσ x hx
  | invokeIOPortControl iv =>
    simp only [archNoReturn] at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact ik_pure _ _ (sl_performIoportControlInvocation iv σ hσ z hz) x hx

theorem nb_archPerform (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a) :
    NBKE (archPerformInvocation (Z := Unit) i) := by
  cases i with
  | invokeASIDControl a => exact absurd rfl (hm a)
  | _ => simp only [archPerformInvocation, archNoReturn]; nb_auto

/-! ## The gap -/

set_option maxHeartbeats 4000000 in
/-- **sl3's untyped / arch gap is closed.** -/
theorem slGap : SlGap := by
  intro I N K L d t blk call don inv σ hgap hσ hI1 hD y hy
  have hS : SL I K σ := hσ.1.1.1
  have hNB : NtfnScB σ := hσ.1.2.2
  have hU : UtInv'' σ := hσ.2.2.1.1
  have hI2 : IrqOutV (fun _ => I.2) (uV σ) := fun irq s c h => by
    have := hσ.2.2.2.2.2.2 irq s c h
    rwa [show σ.idleSc = I.2 from hσ.2.2.2.2.1] at this
  have hnc : InvANC (uV σ) inv := invANC_of hD
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) inv :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    have h := sln_invokeUntyped ui σ ⟨hS, hNB⟩ hU hI1 hI2 hf z hz
    rw [e]; exact h
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
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
          exact sln_makePool frame slot parent base σ ⟨hS, hNB⟩ hU hI1 hI2 hok z hz
      · simp only [fl4ArchPerformInvocation] at hy
        exact ⟨sl_archPerform i (fun a e => hm ⟨a, e⟩) σ hS hok hnc y hy,
          nb_archPerform i (fun a e => hm ⟨a, e⟩) σ hNB y hy⟩
    | deriveSubframe iv =>
      simp only [fl4ArchPerformInvocation, archNoReturn, performDeriveSubframe] at hy
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      refine sln_ik (?_ : SLK I K _) (?_ : NBK _) σ ⟨hS, hNB⟩ x hx
      · sl_auto
      · nb_auto
    | _ =>
      refine ⟨(?_ : SLKE I K _) σ hS y hy, (?_ : NBKE _) σ hNB y hy⟩
      all_goals simp only [fl4ArchPerformInvocation, archNoReturn]
      · sl_auto
      · nb_auto
  | _ => exact (hgap : False).elim

end

end Fl4Proofs.P3.SInvL
