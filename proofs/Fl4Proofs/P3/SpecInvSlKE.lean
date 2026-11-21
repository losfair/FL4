/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **`ScKindR` across the kernel
entries** (spec side only; sl4 handoff 3: the performs, the shell, the events).

* Arch performs (`ks_performPage*` / `PageTable` / `PageDirectory` / `Pdpt`: maps
  write the decoded `KOk` cap, unmaps the invoked cap with its mapping cleared;
  IO port control an IO port cap (empty range); DeriveSubframe 4 KiB page caps
  inside the source large frame (ut8's `DsOKN`, `refRel_sub`); ASID pool
  assignment re-reads its PML4 cap).
* The untyped retype without reset: SpecInvSlKU's `skr_invokeUntyped0`.
* `KrGap` (intermediate definition, sl3's `SlGap` pattern): the untyped retype
  WITH reset and MakePool keep `ScKindR` from `UtInv''` and ut8's decode facts. Every
  lemma below it is stated `(hG : KrGap) → …`.
* `ks_fl4Perform`: every perform keeps `ScKindR`, anchored at the decode state
  `σd` (`uV σ = uV σd`), from `KInv σd` (SpecInvSlKD) and ut8's `GapOKN`.
* The shell (`ks_handleInvocationR`, vfh3's `vfh_handleInvocationR` with
  `ScKindR`): `IKK m` keeps `ScKindR` from a state that also satisfies `UtInv''`
  (only the retype performs read it); the syscalls, the events, `fl4CallKernel`.
* Tops **`kentry_scKindR_of hG`** / **`kcall_scKindR_of hG`**.
-/
import Fl4Proofs.P3.SpecInvSlKU
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvV (hV hV_cap WLH)

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

macro "skr_auto" : tactic => `(tactic| first
  | exact ike_skr_of fun _ => by hv_auto
  | exact ik_skr_of fun _ => by hv_auto)

theorem skr_of_uV {σ σ' : State Unit} (e : uV σ' = uV σ) (h : ScKindR σ) : ScKindR σ' := by
  show ScKindRV (uV σ'); rw [e]; exact h

/-! ## Arch performs -/

theorem kok_ioPort {σ0 : State Unit} (f l : IoPort) : KOk σ0 (.archObjectCap (.ioPortCap f l)) :=
  kok_empty (by ext r; simp [capRng, acRng, aobjRef]) (fun _ _ e => by cases e)

/-- `KS` on the untyped view (for ut8's `HV` arch proofs). -/
def KSV (σ0 : State Unit) (w : UView) : Prop := ∀ sl c, w.2.1 sl = some c → KOk σ0 c

theorem ksv_of_ks {σ0 s : State Unit} (h : KS σ0 s) : KSV σ0 (uV s) := fun _ _ hc => h.cap hc

theorem ks_of_ksv {σ0 s : State Unit} (h : KSV σ0 (uV s)) : KS σ0 s :=
  fun sl c hc => h sl c (by show SInvU.capAt s sl = _; rw [vfh_capAt]; exact hc)

theorem ks_of_uV {σd σ : State Unit} (hK : ScKindR σd) (e : uV σ = uV σd) : KS σd σ :=
  ks_of_ksv (by rw [e]; exact ksv_of_ks (KS.refl hK))

theorem ksv_setCap {σ0 : State Unit} {c : Cap} (sl : CslotPtr) (hk : KOk σ0 c) :
    HV (KSV σ0) (KSV σ0) (setCap (Z := Unit) c sl) := by
  intro σ hσ y hy
  rw [hv_setCap c sl (uV σ) σ rfl y hy]
  intro s c' hs
  rw [vCap_cap] at hs
  split_ifs at hs
  · cases hs; exact hk
  · exact hσ s c' hs

theorem kd_arch_same {a a' : ArchCap} (e : acRng a' = acRng a) : KD (.archObjectCap a) (.archObjectCap a') :=
  kd_arch_rng fun r hr => e ▸ hr

/-- The unmap tail re-reads its slot's arch cap (ut8's `hv_reread`). -/
theorem ksv_reread {σ0 : State Unit} {a : ArchCap} (sl : CslotPtr) (g : ArchCap → ArchCap)
    (hr : acRng (g a) = acRng a) :
    HV (fun w => KSV σ0 w ∧ w.2.1 sl = some (.archObjectCap a)) (KSV σ0)
      (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap => setCap (.archObjectCap (g cap)) sl) := by
  refine hv_liftM_getCap_bind fun w c ⟨hw, hc0⟩ hc => ?_
  rw [hc0] at hc; cases hc
  exact hv_pre (ksv_setCap sl ((hw sl _ hc0).kd (kd_arch_same hr))) fun w' e => by subst e; exact hw

theorem ksv_performPageInvocationUnmap {σ0 : State Unit} (a : ArchCap) (sl : CslotPtr) :
    HV (fun w => KSV σ0 w ∧ w.2.1 sl = some (.archObjectCap a)) (KSV σ0) (performPageInvocationUnmap (Z := Unit) a sl) := by
  cases a with
  | pageCap dev p R mt sz mp =>
    have hR := ksv_reread (σ0 := σ0) (a := .pageCap dev p R mt sz mp) sl
      (fun c => updateMapData c none (some .vmNoMap)) rfl
    cases mp with
    | none =>
      simp only [performPageInvocationUnmap]
      first | exact hR | (refine hv_pure_bind ?_; exact hR) | exact hv_bind (hv_uk fun _ => by uk_auto) fun _ => hR
    | some x =>
      obtain ⟨asid, vaddr⟩ := x
      simp only [performPageInvocationUnmap]
      exact hv_bind (hv_uk fun _ => by uk_auto) fun _ => hR
  | _ => exact hv_fail'

macro "ks_chain" : tactic => `(tactic| repeat' (first
  | assumption
  | exact hv_fail'
  | (exact hv_bind hv_fail' fun _ => hv_uk fun _ => by ukc)
  | (exact hv_bind (ksv_performPageInvocationUnmap _ _) fun _ => hv_uk fun _ => by ukc)
  | (refine hv_pure_bind ?_)
  | (exact hv_mono (hv_uk fun _ => by ukc) fun _ h => h.1)))

/-- The predicate of the arch performs: `KSV`, the decode's `KArchS`, ut8's `ArchSpecOKN`. -/
abbrev KAP (σ0 : State Unit) (i : ArchInvocation) (w : UView) : Prop := KSV σ0 w ∧ KArchS σ0 i ∧ ArchSpecOKN w i

theorem ksv_performPageTableInvocation {σ0 : State Unit} (iv : PageTableInvocation) :
    HV (KAP σ0 (.invokePageTable iv)) (KSV σ0) (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap ctSlot pde pdSlot vspace =>
    intro σ ⟨hI, hk, _⟩ y hy
    simp only [performPageTableInvocation] at hy
    exact hv_bind (ksv_setCap ctSlot hk) (fun _ => hv_uk fun _ => by ukc) σ hI y hy
  | pageTableUnmap cap ctSlot =>
    cases cap with
    | archObjectCap a =>
      cases a with
      | pageTableCap p ma =>
        have hR := ksv_reread (σ0 := σ0) (a := .pageTableCap p ma) ctSlot (fun c => updateMapData c none none) rfl
        refine hv_pre (P := fun w => KSV σ0 w ∧ w.2.1 ctSlot = some (.archObjectCap (.pageTableCap p ma))) ?_ (fun _ h => ⟨h.1, h.2.2⟩)
        cases ma with
        | none =>
          simp only [performPageTableInvocation]
          first | exact hR | (refine hv_pure_bind ?_; exact hR)
        | some x =>
          obtain ⟨asid, vaddr⟩ := x
          simp only [performPageTableInvocation]
          refine hv_bind (hv_uk fun _ => by ukc) fun _ => ?_
          refine hv_pure_bind (hv_pure_bind (hv_bind (hv_uk fun _ => by ukc) fun _ => hR))
      | _ => exact hv_fail'
    | _ => exact hv_fail'

theorem ksv_performPageDirectoryInvocation {σ0 : State Unit} (iv : PageDirectoryInvocation) :
    HV (KAP σ0 (.invokePageDirectory iv)) (KSV σ0) (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap ctSlot pdpte pdptSlot vspace =>
    intro σ ⟨hI, hk, _⟩ y hy
    simp only [performPageDirectoryInvocation] at hy
    exact hv_bind (ksv_setCap ctSlot hk) (fun _ => hv_uk fun _ => by ukc) σ hI y hy
  | pageDirectoryUnmap cap ctSlot =>
    cases cap with
    | archObjectCap a =>
      cases a with
      | pageDirectoryCap p ma =>
        have hR := ksv_reread (σ0 := σ0) (a := .pageDirectoryCap p ma) ctSlot (fun c => updateMapData c none none) rfl
        refine hv_pre (P := fun w => KSV σ0 w ∧ w.2.1 ctSlot = some (.archObjectCap (.pageDirectoryCap p ma))) ?_ (fun _ h => ⟨h.1, h.2.2⟩)
        cases ma with
        | none =>
          simp only [performPageDirectoryInvocation]
          first | exact hR | (refine hv_pure_bind ?_; exact hR)
        | some x =>
          obtain ⟨asid, vaddr⟩ := x
          simp only [performPageDirectoryInvocation]
          refine hv_bind (hv_uk fun _ => by ukc) fun _ => ?_
          refine hv_pure_bind (hv_pure_bind (hv_bind (hv_uk fun _ => by ukc) fun _ => hR))
      | _ => exact hv_fail'
    | _ => exact hv_fail'

theorem ksv_performPdptInvocation {σ0 : State Unit} (iv : PdptInvocation) :
    HV (KAP σ0 (.invokePDPT iv)) (KSV σ0) (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap ctSlot pml4e pml4Slot vspace =>
    intro σ ⟨hI, hk, _⟩ y hy
    simp only [performPdptInvocation] at hy
    exact hv_bind (ksv_setCap ctSlot hk) (fun _ => hv_uk fun _ => by ukc) σ hI y hy
  | pdptUnmap cap ctSlot =>
    cases cap with
    | archObjectCap a =>
      cases a with
      | pdPointerTableCap p ma =>
        have hR := ksv_reread (σ0 := σ0) (a := .pdPointerTableCap p ma) ctSlot (fun c => updateMapData c none none) rfl
        refine hv_pre (P := fun w => KSV σ0 w ∧ w.2.1 ctSlot = some (.archObjectCap (.pdPointerTableCap p ma))) ?_ (fun _ h => ⟨h.1, h.2.2⟩)
        cases ma with
        | none =>
          simp only [performPdptInvocation]
          first | exact hR | (refine hv_pure_bind ?_; exact hR)
        | some x =>
          obtain ⟨asid, vaddr⟩ := x
          simp only [performPdptInvocation]
          refine hv_bind (hv_uk fun _ => by ukc) fun _ => ?_
          refine hv_pure_bind (hv_pure_bind (hv_bind (hv_uk fun _ => by ukc) fun _ => hR))
      | _ => exact hv_fail'
    | _ => exact hv_fail'

theorem ksv_performPageInvocation {σ0 : State Unit} (iv : PageInvocation) :
    HV (KAP σ0 (.invokePage iv)) (KSV σ0) (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap ctSlot entries vspace =>
    intro σ ⟨hI, hk, _⟩ y hy
    simp only [performPageInvocation] at hy
    exact hv_bind (ksv_setCap ctSlot hk) (fun _ => hv_uk fun _ => by ukc) σ hI y hy
  | pageUnmap a ctSlot =>
    cases a with
    | pageCap dev p R mt sz mp =>
      refine hv_pre (P := fun w => KSV σ0 w ∧ w.2.1 ctSlot = some (.archObjectCap (.pageCap dev p R mt sz mp))) ?_ (fun _ h => ⟨h.1, h.2.2⟩)
      cases mp with
      | none => simp only [performPageInvocation]; ks_chain
      | some x =>
        cases mt <;> (simp only [performPageInvocation]; ks_chain)
    | _ => exact hv_fail'
  | pageGetAddr ptr =>
    simp only [performPageInvocation]
    exact hv_mono (hv_uk fun _ => by ukc) fun _ h => h.1

/-- An `HV` arch perform at a pinned `KS` state. -/
theorem ikp_of_kap {α : Type} {σ0 σ : State Unit} {i : ArchInvocation} {m : NonDet (State Unit) α}
    (h : HV (KAP σ0 i) (KSV σ0) m) (hi : KArchS σ0 i) (hs : ArchSpecOKN (uV σ) i) : IKp (KS σ0) σ m :=
  fun hσ y hy => ks_of_ksv (h σ ⟨ksv_of_ks hσ, hi, hs⟩ y hy)

theorem ikp_liftE {P : State Unit → Prop} {ε α : Type} {σ : State Unit} {m : NonDet (State Unit) α}
    (h : IKp P σ m) : IKp P σ (ExceptT.run (NonDetE.liftE (ε := ε) m)) := by
  intro hσ x hx
  unfold NonDetE.liftE at hx
  rw [ExceptT.run_lift] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  exact h hσ y hy

theorem ks_performIoportControlInvocation {σ0 : State Unit} (i : IoPortControlInvocation) :
    IK (KS σ0) (performIoportControlInvocation (Z := Unit) i) := by
  cases i with
  | ioPortControlInvocation f l d c =>
    simp only [performIoportControlInvocation]
    refine ik_bind (by hv_auto) fun _ => ik_pure_bind ?_
    exact ks_capInsert _ _ (kok_ioPort _ _)

/-- **DeriveSubframe** (ut8's `DsOKN`: the source holds a large frame containing every new page). -/
theorem ks_performDeriveSubframe {σ0 : State Unit} (hK : ScKindR σ0) (iv : Fl4SubframeInvocation)
    (hd : DsOKN (uV σ0) iv) : IK (KS σ0) (performDeriveSubframe (Z := Unit) iv) := by
  obtain ⟨src, base, rights, dests⟩ := iv
  obtain ⟨p, r, mt, m, off, hsrc, hbase, hlen, -⟩ := hd
  dsimp only at hsrc hbase hlen
  subst hbase
  have hk0 := kok_of_slot hK hsrc
  unfold performDeriveSubframe
  refine vfh_ik_mapMx_mem _ fun x hx => ks_capInsert _ _ (hk0.kd (kd_arch_rng ?_))
  obtain ⟨i, d⟩ := x
  obtain ⟨hi, -⟩ := List.of_mem_zip hx
  have := List.mem_range.1 hi
  exact (refRel_sub (r := r) (r' := rights) (mt := mt) (m := m) (d := i) (by dsimp only at this ⊢; omega)).1

/-- ASID pool assignment re-reads its slot and rewrites the PML4 cap there. -/
theorem ks_performAsidPoolInvocation (i : AsidPoolInvocation) : KK (performAsidPoolInvocation (Z := Unit) i) := by
  intro σ0
  cases i with
  | assign asid pool sl =>
    simp only [performAsidPoolInvocation]
    intro σ
    refine ikp_getCap_bind fun c hc => ?_
    split
    · intro hσ x hx
      exact (ik_bind (ks_setCap _ ((hσ _ _ hc).kd (kd_arch_same (a' := .pml4Cap _ (some asid)) rfl))) fun _ => by hv_auto) σ hσ x hx
    · exact ikp_of_ik ik_fail σ

/-! ## The retype performs (intermediate) -/

/-- **The reset retype and MakePool keep `ScKindR`** (intermediate
definition, not an invariant premise: sl3's `SlGap` pattern). -/
def KrGap : Prop :=
  (∀ (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr) (dev : Bool)
    (σ : State Unit), ScKindR σ → UtInv'' σ → UtGapOK (uV σ) (.retype s true base rb ty sz slots dev) →
    ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) (.retype s true base rb ty sz slots dev)).run σ).1, ScKindR y.2) ∧
  (∀ (a : AsidControlInvocation) (σ : State Unit), ScKindR σ → UtInv'' σ → MpOKN (uV σ) a →
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, ScKindR y.2)

/-! ## The performs -/

set_option maxHeartbeats 8000000 in
/-- **Every perform keeps `ScKindR`** from the decode's facts at `σd`. -/
theorem ks_fl4Perform (hG : KrGap) (blk call don : Bool) (inv : Fl4Invocation) (σd σ : State Unit)
    (hK : ScKindR σd) (e : uV σ = uV σd) (hU : UtInv'' σ) (hgap : GapOKN (uV σ) inv) (hi : KInv σd inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, ScKindR y.2 := by
  have hS : KS σd σ := ks_of_uV hK e
  have hKs : ScKindR σ := skr_of_uV e hK
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e'⟩ := mem_ret_bindE hy
    rw [e']
    obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
    cases reset
    · exact skr_invokeUntyped0 hKs hU hgap z hz
    · exact hG.1 s base rb ty sz slots dev σ hKs hU hgap z hz
  | invokeCNode i =>
    refine ((show IKE (KS σd) (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) by
      simp only [fl4PerformInvocation]
      exact ike_bind (ks_invokeCnode i hi) fun _ => ike_returnOk _) σ hS y hy).cur
  | invokeTCB i =>
    refine ((show IKE (KS σd) (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) by
      simp only [fl4PerformInvocation]
      exact ks_invokeTcb i) σ hS y hy).cur
  | invokeIRQControl i =>
    refine ((show IKE (KS σd) (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQControl i)) by
      simp only [fl4PerformInvocation]
      exact ike_bind (ks_invokeFl4IrqControl i) fun _ => ike_returnOk _) σ hS y hy).cur
  | invokeIRQHandler i =>
    refine ((show IKE (KS σd) (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQHandler i)) by
      simp only [fl4PerformInvocation]
      exact ike_bind (ike_liftE (ks_invokeIrqHandler i hi)) fun _ => ike_returnOk _) σ hS y hy).cur
  | invokeArchObject ai =>
    cases ai with
    | spec i =>
      cases i with
      | invokeASIDControl a =>
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
        obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
        obtain ⟨z, hz, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hx]
        exact hG.2 a σ hKs hU hgap z hz
      | invokePageTable i' =>
        refine ((show IKp (KS σd) σ (ExceptT.run (fl4PerformInvocation (Z := Unit) blk call don
            (.invokeArchObject (.spec (.invokePageTable i'))))) by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ikp_liftE (ikp_bind (ikp_of_kap (ksv_performPageTableInvocation i') hi hgap) fun _ => ?_)
          hv_auto) hS y hy).cur
      | invokePageDirectory i' =>
        refine ((show IKp (KS σd) σ (ExceptT.run (fl4PerformInvocation (Z := Unit) blk call don
            (.invokeArchObject (.spec (.invokePageDirectory i'))))) by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ikp_liftE (ikp_bind (ikp_of_kap (ksv_performPageDirectoryInvocation i') hi hgap) fun _ => ?_)
          hv_auto) hS y hy).cur
      | invokePDPT i' =>
        refine ((show IKp (KS σd) σ (ExceptT.run (fl4PerformInvocation (Z := Unit) blk call don
            (.invokeArchObject (.spec (.invokePDPT i'))))) by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ikp_liftE (ikp_bind (ikp_of_kap (ksv_performPdptInvocation i') hi hgap) fun _ => ?_)
          hv_auto) hS y hy).cur
      | invokePage i' =>
        refine ((show IKp (KS σd) σ (ExceptT.run (fl4PerformInvocation (Z := Unit) blk call don
            (.invokeArchObject (.spec (.invokePage i'))))) by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          exact ikp_liftE (ikp_of_kap (ksv_performPageInvocation i') hi hgap)) hS y hy).cur
      | invokeIOPortControl i' =>
        refine ((show IKE (KS σd) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (ks_performIoportControlInvocation i') fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokeASIDPool i' =>
        refine ((show IKE (KS σd) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          refine ike_liftE (ik_bind (ks_performAsidPoolInvocation i' σd) fun _ => ?_)
          hv_auto) σ hS y hy).cur
      | invokeIOPort i' =>
        refine ((show IKE (KS σd) _ by
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
          hv_auto) σ hS y hy).cur
    | deriveSubframe iv =>
      have hds : DsOKN (uV σd) iv := by rw [← e]; exact hgap
      refine ((show IKE (KS σd) _ by
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
        refine ike_liftE (ik_bind (ks_performDeriveSubframe hK iv hds) fun _ => ?_)
        hv_auto) σ hS y hy).cur
    | _ =>
      refine ((show IKE (KS σd) _ by
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
        hv_auto) σ hS y hy).cur
  | _ =>
    refine ((show IKE (KS σd) _ by simp only [fl4PerformInvocation]; hv_auto) σ hS y hy).cur

/-! ## The invocation shell -/

/-- `ScKindR` kept from a state that also satisfies `UtInv''`. -/
def IKK {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, ScKindR σ → UtInv'' σ → ∀ y ∈ (m σ).1, ScKindR y.2

abbrev IKKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKK (ExceptT.run m)

theorem ikk_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IK ScKindR m) : IKK m :=
  fun σ hI _ y hy => h σ hI y hy

theorem ikke_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hm' : IKE ScKindR m) (hg : ∀ a, IKKE (g a)) : IKKE (m >>= g) := by
  intro σ hI hU y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm' σ hI z hz) (utInv''_of_view (hm (uV σ) σ rfl z hz) hU) y hy
  · exact hm' σ hI z hz

theorem ikke_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKKE m) (hg : ∀ a, IKE ScKindR (g a)) : IKKE (m >>= g) := by
  intro σ hI hU y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm σ hI hU z hz) y hy
  · exact hm σ hI hU z hz

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `ScKindR`**, from `UtInv''` at its start. -/
theorem ks_handleInvocationR (hG : KrGap) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKKE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikke_bind_uk (fun _ => by uk_auto) (by skr_auto) fun thread =>
    ikke_bind_uk (fun _ => by uk_auto) (by skr_auto) fun info => ?_
  intro σ hI hU y hy
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hOk : OkV (uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ).2.1 p.2 = some p.1) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCaps _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := fun s => ScKindR s ∧ uV s = uV σ) (Q := ScKindR)
    (fun w hw => ⟨skr_of_uV (hF _ σ rfl w hw) hI, hF _ σ rfl w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK ScKindR (NonDet.when blocking (handleFault thread f)) by skr_auto) s hs.1 v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hs : uV s = uV σ := hF _ σ rfl _ has
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have e := (hE _ s rfl w hw).trans hs
    exact ⟨skr_of_uV e hI, e⟩
  · intro e s hs v hv
    exact (by skr_auto : IK ScKindR _) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    have hKs : ScKindR s := skr_of_uV hvs hI
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    have hc' : (uV s).2.1 sl = some cap := by rw [hvs]; exact hc
    have hex' : ∀ p ∈ ex, (uV s).2.1 p.2 = some p.1 := by rw [hvs]; exact hex
    have hgap : GapOKN (uV σ) b :=
      okv_bind_uk (P := GapOKN (uV σ)) (fun _ => ike_liftE (uk_getMrs _ _ _)) (fun args =>
        okv_fl4DecodeG (w := uV σ) fp info.miLabel args cptr sl cap ex buf hc hex) s hvs b s' hbs
    have hki : KInv s b :=
      okv_bind_uk (P := KInv s) (fun _ => ike_liftE (uk_getMrs _ _ _)) (fun args =>
        kr_okv_fl4Decode s hKs fp info.miLabel args cptr sl cap ex buf hc' hex') s rfl b s' hbs
    have hU' : UtInv'' s' := utInv''_of_view hI'.2 hU
    have hTS : ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart)) := fun _ => by uk_auto
    have hTSv : IKE ScKindR (withoutPreemption (Z := Unit) (setThreadState thread .restart)) := by skr_auto
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := hTS _ s' rfl z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2
      have hgap1 : GapOKN (uV s1) b := by rw [hv1]; exact hgap
      have hv1s : uV s1 = uV s := hv1.trans hvs.symm
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := ks_fl4Perform hG blocking calling don b s s1 hKs hv1s (utInv''_of_view hz' hU') hgap1 hki _ hz2
        exact (by skr_auto : IKE ScKindR _) s2 hs2 y hy
      · exact ks_fl4Perform hG blocking calling don b s s1 hKs hv1s (utInv''_of_view hz' hU') hgap1 hki _ hz2
    · exact hTSv s' hI'.1 z hz

/-! ## The syscall paths -/

set_option maxHeartbeats 8000000 in
theorem ks_capRegL (r : Register) : IKE ScKindR (NonDetE.liftE (ε := Unit) (getCapReg (Z := Unit) r)) := by
  skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_capRegW (r : Register) : IKE ScKindR (withoutPreemption (Z := Unit) (getCapReg (Z := Unit) r)) := by
  skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_recvW (a b : Bool) : IKE ScKindR (withoutPreemption (Z := Unit) (handleRecv (Z := Unit) a b)) := by
  skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_yieldW : IKE ScKindR (withoutPreemption (Z := Unit) (handleYield (Z := Unit))) := by
  skr_auto

theorem ks_sysInv (hG : KrGap) (rep calling blocking don fp : Bool) (r : Register) :
    IKKE (do
      let cptr ← NonDetE.liftE <| getCapReg (Z := Unit) r
      fl4HandleInvocationR rep calling blocking don fp cptr) :=
  ikke_bind_uk (vfh_capRegLU r) (ks_capRegL r) fun _ => ks_handleInvocationR hG _ _ _ _ _ _

theorem ks_sysInvRecv (hG : KrGap) (rep calling blocking don fp a b : Bool) (r : Register) :
    IKKE (do
      let c ← withoutPreemption <| getCapReg (Z := Unit) r
      fl4HandleInvocationR rep calling blocking don fp c
      withoutPreemption <| handleRecv a b) :=
  ikke_bind_uk (vfh_capRegWU r) (ks_capRegW r) fun _ =>
    ikke_bind (ks_handleInvocationR hG _ _ _ _ _ _) fun _ => ks_recvW a b

theorem ks_fl4HandleSyscall (hG : KrGap) (rep : Bool) (c : Syscall) : IKKE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c
  · exact ks_sysInv hG rep true true true false cap_register
  · exact ks_sysInvRecv hG rep false false true true true true replyRegister
  · exact ks_sysInvRecv hG rep false false true true true true nbsendRecvDest
  · exact ks_sysInvRecv hG rep false false true true true false replyRegister
  · exact ks_sysInv hG rep false true false false cap_register
  · exact ks_sysInv hG rep false false false false cap_register
  · exact ikk_of_ik (ks_recvW true true)
  · exact ikk_of_ik ks_yieldW
  · exact ikk_of_ik (ks_recvW false true)
  · exact ikk_of_ik (ks_recvW true false)
  · exact ikk_of_ik (ks_recvW false false)

set_option maxHeartbeats 8000000 in
theorem ks_he_unknown (n : Nat) : IKE ScKindR (handleEvent (Z := Unit) (.unknownSyscall n)) := by
  simp only [handleEvent]; skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_he_ulf (w1 w2 : Word) : IKE ScKindR (handleEvent (Z := Unit) (.userLevelFault w1 w2)) := by
  simp only [handleEvent]; skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_he_interrupt : IKE ScKindR (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent]; skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_he_vm (t : VMFaultType) : IKE ScKindR (handleEvent (Z := Unit) (.vmFaultEvent t)) := by
  simp only [handleEvent]; skr_auto

set_option maxHeartbeats 8000000 in
theorem ks_he_hyp (t : HypFaultType) : IKE ScKindR (handleEvent (Z := Unit) (.hypervisorEvent t)) := by
  simp only [handleEvent]; skr_auto

theorem ks_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : IKE ScKindR (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | unknownSyscall n => exact ks_he_unknown n
  | userLevelFault w1 w2 => exact ks_he_ulf w1 w2
  | interrupt => exact ks_he_interrupt
  | vmFaultEvent t => exact ks_he_vm t
  | hypervisorEvent t => exact ks_he_hyp t

set_option maxHeartbeats 4000000 in
theorem ks_fl4HandleEvent (hG : KrGap) (rep : Bool) (ev : Event) : IKKE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikke_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (by skr_auto) fun _ => ?_
    intro σ hI hU y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : ScKindR x.2 := (by skr_auto : IK ScKindR (checkBudgetRestart (Z := Unit))) σ hI x hx
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        have hv := SInvU.checkBudgetRestart_true hx ht
        exact ks_fl4HandleSyscall hG rep c x.2 hIx (utInv''_of_view hv hU) y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hIx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikk_of_ik (ks_handleEvent_other ev fun c e => h ⟨c, e⟩)

theorem ikk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKK m) (hg : ∀ a, IK ScKindR (g a)) : IKK (m >>= g) := by
  intro σ hI hU y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm σ hI hU x hx) y hy

theorem ikk_bind_uk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ v, UK v m) (hm' : IK ScKindR m) (hg : ∀ a, IKK (g a)) : IKK (m >>= g) := by
  intro σ hI hU y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm' σ hI x hx) (utInv''_of_view (uk_mem hm hx) hU) y hy

set_option maxHeartbeats 4000000 in
theorem ks_fl4CallKernel (hG : KrGap) (rep : Bool) (ev : Event) : IKK (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikk_bind ?_ fun _ => by skr_auto
  intro σ hI hU y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := ks_fl4HandleEvent hG rep ev σ hI hU z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE ScKindR (withoutPreemption (Z := Unit) preemptionPath) by skr_auto) s hz' y hy

/-! ## Tops (given `KrGap`) -/

/-- **`ScKindR` across the syscall entry**, given the retype performs' `KrGap`. -/
theorem kentry_scKindR_of (hG : KrGap) (c : Syscall) {σ : State Unit} (hK : ScKindR σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScKindR y.2 := by
  intro y hy
  unfold fl4KernelEntrySyscall at hy
  exact ikk_bind_uk (fun _ => ik_gets _) (by skr_auto) (fun ct => ikk_bind_uk (fun _ => uk_fl4SyscallFaultIP ct)
    (by skr_auto) fun _ => ks_fl4CallKernel hG true _) σ hK hU.1 y hy

/-- **`ScKindR` across every kernel event**, given `KrGap`. -/
theorem kcall_scKindR_of (hG : KrGap) (rep : Bool) (ev : Event) {σ : State Unit} (hK : ScKindR σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScKindR y.2 :=
  fun y hy => ks_fl4CallKernel hG rep ev σ hK hU.1 y hy

end

end Fl4Proofs.P3.SInvL
