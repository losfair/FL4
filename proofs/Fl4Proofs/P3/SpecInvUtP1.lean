/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut8): **the arch performs
other than MakePool keep `P3 N`, from their decode facts** (spec side only;
imports SpecInvUtO6).

* `ArchSpecOKN` / `ArchOKN`: what the VSpace performs need from the decode. A map
  writes a cap `RefEq` to the invoked slot's cap (same object, same frame range,
  `MapOK`); an unmap re-reads the invoked slot, which holds the decoded VSpace
  cap; IO-port control as in SpecInvUtO5 (`IoCOKN`); DeriveSubframe (`DsOKN`):
  the source holds a non-device large frame cap `p`, the new caps' pages lie in
  `[p, p + 2 MiB)`, the destinations are null slots of a CNode cap held in a
  slot. **`okv_fl4ArchDecodeN`** establishes them.
* `hv_setCapRE` (a `RefEq` write keeps `P3`), `hv_liftM_getCap_bind`,
  `refEq_arch`; the performs `p3_performPageTableInvocation`,
  `p3_performPageDirectoryInvocation`, `p3_performPdptInvocation`,
  `p3_performPageInvocation`; **`p3_performDeriveSubframe`** (`refRel_sub`: a
  4 KiB page cap inside the large frame is `RefRel` to it; `hv_capInsert_keep`:
  a non-untyped insert keeps every other slot, so the source and the CNode cap
  stay and every destination stays `DestRefV`); **`p3_archPerform`** (every
  arch invocation but `invokeASIDControl`).
-/
import Fl4Proofs.P3.SpecInvUtO6
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-! ## Generic leaves -/

theorem hv_fail' {P Q : UView → Prop} {α : Type} : HV P Q (NonDet.fail : NonDet (State Unit) α) :=
  fun _ _ _ hy => hy.elim

theorem hv_and {P Q1 Q2 : UView → Prop} {α : Type} {m : NonDet (State Unit) α} (h1 : HV P Q1 m) (h2 : HV P Q2 m) :
    HV P (fun w => Q1 w ∧ Q2 w) m :=
  fun σ hσ y hy => ⟨h1 σ hσ y hy, h2 σ hσ y hy⟩

theorem hv_liftM_getCap_bind {P Q : UView → Prop} {α β : Type} {sl : CslotPtr} {f : Cap → β}
    {k : β → NonDet (State Unit) α}
    (h : ∀ w c, P w → w.2.1 sl = some c → HV (· = w) Q (k (f c))) :
    HV P Q (NonDet.liftM f (getCap (Z := Unit) sl) >>= k) := by
  intro σ hσ x ⟨y, ⟨z, hz, hy⟩, hx⟩
  obtain ⟨e, hc⟩ := getCap_capAt hz
  obtain rfl := Set.mem_singleton_iff.1 hy
  obtain ⟨c, s⟩ := z
  simp only at e hc; subst e
  exact h _ c hσ hc s rfl x hx

theorem refEq_arch {a a' : ArchCap} (ho : aobjRef a' = aobjRef a) (hr : acRng a' = acRng a) :
    RefEq (.archObjectCap a) (.archObjectCap a') := by
  refine Or.inr ⟨fun e => (by cases e), ?_, rfl, fun _ _ _ e => (by cases e), fun _ _ _ e => (by cases e),
    fun _ _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e), hr⟩
  show {r | aobjRef a' = some r} = {r | aobjRef a = some r}
  rw [ho]

theorem nnu_arch (a : ArchCap) : NNU (.archObjectCap a) := ⟨fun e => (by cases e), fun _ _ _ _ e => (by cases e)⟩

/-- **A write of a cap `RefEq` to the slot's cap keeps `P3 N`.** -/
theorem hv_setCapRE {c0 c : Cap} (hn : NNU c) (sl : CslotPtr) :
    HV (fun w => P3V N w ∧ w.2.1 sl = some c0 ∧ RefEq c0 c) (P3V N) (setCap (Z := Unit) c sl) :=
  hv_pin fun w ⟨hw, hc, hr⟩ => hv_mono (hv_setCap c sl w) fun w' e => by
    subst e
    exact ⟨⟨utInv'_vCap_nn hw.1.1 hn, utN_vCapEq hw.1.2 hc hr⟩,
      irqOut_vCap hw.2 (covBy_of hc (subset_of_eq (covR_of_refEq hr))) sl⟩

/-- The re-read of an unmap: `update_map_data` of the slot's own VSpace cap. -/
theorem hv_reread {a : ArchCap} (sl : CslotPtr) (g : ArchCap → ArchCap)
    (ho : aobjRef (g a) = aobjRef a) (hr : acRng (g a) = acRng a) :
    HV (fun w => P3V N w ∧ w.2.1 sl = some (.archObjectCap a)) (P3V N)
      (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap => setCap (.archObjectCap (g cap)) sl) := by
  refine hv_liftM_getCap_bind fun w c ⟨hw, hc0⟩ hc => ?_
  rw [hc0] at hc; cases hc
  exact hv_pre (hv_setCapRE (nnu_arch _) sl) fun w' e => by subst e; exact ⟨hw, hc0, refEq_arch ho hr⟩

/-! ## The decode facts -/

/-- A map's decoded cap: `RefEq` to the invoked slot's cap. -/
def MapOK (w : UView) (c : Cap) (sl : CslotPtr) : Prop := ∃ c0, w.2.1 sl = some c0 ∧ RefEq c0 c ∧ NNU c

/-- What DeriveSubframe needs from its decode. -/
def DsOKN (w : UView) (iv : Fl4SubframeInvocation) : Prop :=
  ∃ p r mt m off, w.2.1 iv.src = some (.archObjectCap (.pageCap false p r mt .x64LargePage m)) ∧
    iv.base = p + off ∧ off.toNat + 4096 * iv.dests.length ≤ 2097152 ∧
    ∃ s1 ptr bits g, w.2.1 s1 = some (.cnodeCap ptr bits g) ∧
      ∀ d ∈ iv.dests, d.1 = ptr ∧ (∃ i, d.2 = natToCref bits i) ∧ w.2.1 d = some .nullCap

/-- What MakePool needs from its decode. -/
def MpOKN (w : UView) : AsidControlInvocation → Prop
  | .makePool frame slot parent _ =>
    (∃ dev fi, w.2.1 parent = some (.untypedCap dev frame page_bits fi) ∧ ∀ c, w.2.2.1 c ≠ some parent) ∧
      DestRefV w slot ∧ w.2.1 slot = some .nullCap

/-- What the x64 arch performs need from the decode. -/
def ArchSpecOKN (w : UView) : ArchInvocation → Prop
  | .invokePageTable (.pageTableMap c sl _ _ _) => MapOK w c sl
  | .invokePageTable (.pageTableUnmap c sl) => w.2.1 sl = some c
  | .invokePageDirectory (.pageDirectoryMap c sl _ _ _) => MapOK w c sl
  | .invokePageDirectory (.pageDirectoryUnmap c sl) => w.2.1 sl = some c
  | .invokePDPT (.pdptMap c sl _ _ _) => MapOK w c sl
  | .invokePDPT (.pdptUnmap c sl) => w.2.1 sl = some c
  | .invokePage (.pageMap c sl _ _) => MapOK w c sl
  | .invokePage (.pageUnmap a sl) => w.2.1 sl = some (.archObjectCap a)
  | .invokeIOPortControl i => IoCOKN w i
  | .invokeASIDControl a => MpOKN w a
  | _ => True

def ArchOKN (w : UView) : Fl4ArchInvocation → Prop
  | .spec i => ArchSpecOKN w i
  | .deriveSubframe iv => DsOKN w iv
  | _ => True

macro "okva_step" : tactic => `(tactic| first
  | exact okv_throw _ | exact okv_throw' _ | exact okv_liftE_fail
  | (refine okv_returnOk_bind ?_) | (refine okv_pure_bind ?_)
  | (refine okv_whenE_bind fun _ => ?_) | (refine okv_unlessE_bind fun _ => ?_)
  | (dsimp only)
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_)
  | (refine okv_ite ?_ ?_)
  | contradiction
  | split | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | ik_unfold)


set_option maxHeartbeats 8000000 in
theorem okv_archDecodeN {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap cap)) (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) :
    OkV w (ArchSpecOKN w) (archDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  have hcps : ∀ c ∈ ex.map Prod.fst, ∃ s, w.2.1 s = some c := by
    intro c h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    exact ⟨q.2, hex q hq⟩
  cases cap
  case asidControlCap =>
    simp only [archDecodeInvocation]
    split
    · split
      · rename_i hlen
        have hroot : ∃ s, w.2.1 s = some (the ex[1]?).1 := by
          have h1 : ex[1]? = some ex[1] := List.getElem?_eq_getElem (by omega)
          rw [h1]; simp only [the]
          exact ⟨_, hex _ (List.getElem_mem _)⟩
        generalize hq : the ex[0]? = q
        obtain ⟨untyped, parentSlot⟩ := q
        dsimp only
        have hpu : w.2.1 parentSlot = some untyped := by
          have h0 : ex[0]? = some ex[0] := List.getElem?_eq_getElem (by omega)
          have hm : ex[0] ∈ ex := List.mem_iff_getElem?.2 ⟨0, h0⟩
          have := hex _ hm
          rw [h0] at hq; simp only [the] at hq
          rw [hq] at this; exact this
        refine okv_bind_uk (fun _ => by uk_auto) fun _ => okv_returnOk_bind (okv_whenE_bind fun _ =>
          okv_bind_uk (fun _ => by uk_auto) fun _ => okv_returnOk_bind ?_)
        split
        · rename_i p n f
          refine okv_returnOk_bind ?_
          dsimp only
          refine okv_bind (Q := fun fr : ObjRef => n = pageBits ∧ fr = p ∧ ∀ c, w.2.2.1 c ≠ some parentSlot)
            (fun _ => by uk_auto) ?_ fun fr hfr => ?_
          · split
            · rename_i hn
              exact okv_bind (fun _ => uk_ensureNoChildren _) (okv_ensureNoChildren _) fun _ hk => okv_returnOk ⟨hn, rfl, hk⟩
            · exact okv_throw _
          obtain ⟨hn, rfl, hk⟩ := hfr
          refine okv_bind (fun _ => uk_lookupTargetSlot _ _ _) (okv_lookupSlotForCnodeOpN false _ _ _ hroot)
            fun destSlot hdr => ?_
          refine okv_bind (fun _ => uk_ensureEmpty _) (okv_ensureEmpty _) fun _ hnull => okv_returnOk ?_
          refine ⟨⟨false, f, ?_, hk⟩, hdr, hnull⟩
          rw [hpu, hn]; rfl
        · exact okv_throw_bind _
      · exact okv_throw _
    · exact okv_throw _
  case ioPortControlCap =>
    simp only [archDecodeInvocation]
    exact okv_mono (okv_decodeIoportControlN label args cte _ _ hc hcps) fun i ⟨j, e, h⟩ => by subst e; exact h
  case pdPointerTableCap p m =>
    simp only [archDecodeInvocation, decodePdptInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hc | exact okv_returnOk ⟨_, hc, refEq_arch rfl rfl, nnu_arch _⟩
  case pageDirectoryCap p m =>
    simp only [archDecodeInvocation, decodePageDirectoryInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hc | exact okv_returnOk ⟨_, hc, refEq_arch rfl rfl, nnu_arch _⟩
  case pageTableCap p m =>
    simp only [archDecodeInvocation, decodePageTableInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hc | exact okv_returnOk ⟨_, hc, refEq_arch rfl rfl, nnu_arch _⟩
  case pageCap dev p R mt sz m =>
    simp only [archDecodeInvocation, decodePageInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk hc | exact okv_returnOk ⟨_, hc, refEq_arch rfl rfl, nnu_arch _⟩
  case ioPortCap f l =>
    simp only [archDecodeInvocation]
    unfold decodePortInvocation
    split <;> okv_noasid
  all_goals (simp only [archDecodeInvocation]; okv_noasid)

theorem okv_subframeNode {w : UView} (nc : Cap) (index depth : Data) (hn : ∃ s, w.2.1 s = some nc) :
    OkV w (fun c => ∃ s, w.2.1 s = some c) (subframeNode (Z := Unit) nc index depth) := by
  unfold subframeNode
  split
  · exact okv_returnOk hn
  · refine okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun sl => ?_
    intro σ hσ a s hs
    obtain ⟨x, hx, e⟩ := mem_liftE' hs
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨sl, by rw [← hσ]; exact (getCap_capAt hx).2⟩

set_option maxHeartbeats 8000000 in
theorem okv_decodeDeriveSubframeN {w : UView} (args : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef)
    (R : VMRights) (mt : VMMapType) (sz : VMPageSize) (m : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (hc : w.2.1 cte = some (.archObjectCap (.pageCap dev p R mt sz m)))
    (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) :
    OkV w (DsOKN w) (decodeDeriveSubframe (Z := Unit) args cte (.pageCap dev p R mt sz m) ex) := by
  unfold decodeDeriveSubframe
  by_cases hlen : ex.length = 0 ∨ args.length < 6
  · rw [if_pos hlen]; exact okv_throw _
  rw [if_neg hlen]
  have hn0 : ∃ s, w.2.1 s = some (the ex[0]?).1 := by
    have hl : 0 < ex.length := by
      rcases Nat.eq_zero_or_pos ex.length with h | h
      · exact absurd (Or.inl h) hlen
      · exact h
    have h0 : ex[0]? = some ex[0] := List.getElem?_eq_getElem hl
    rw [h0]
    exact ⟨_, hex _ (List.getElem_mem hl)⟩
  cases dev <;> cases sz
  all_goals (try exact okv_throw _)
  dsimp only
  refine okv_whenE_bind fun hoff => okv_whenE_bind fun hcnt => ?_
  refine okv_bind (fun _ => uk_subframeNode _ _ _) (okv_subframeNode _ _ _ hn0) fun nc ⟨s1, hs1⟩ => ?_
  cases nc with
  | cnodeCap ptr bits g =>
    try dsimp only
    refine okv_whenE_bind fun _ => okv_whenE_bind fun _ => ?_
    refine okv_bind (fun _ => ike_mapMEx (fun _ => uk_ensureEmpty _) _) (okv_mapMEx_ensureEmpty _) fun _ hnull => ?_
    refine okv_returnOk ⟨p, R, mt, m, _, hc, rfl, ?_, s1, ptr, bits, g, hs1, fun d hd => ?_⟩
    · simp only [List.length_map, List.length_range', unat] at *
      have h21 : (2 : Nat) ^ 21 = 2097152 := by decide
      rw [h21] at hoff hcnt
      omega
    · refine ⟨?_, ?_, hnull d hd⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd; rfl
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd; exact ⟨i, rfl⟩
  | _ => exact okv_throw _

set_option maxHeartbeats 8000000 in
theorem okv_fl4ArchDecodeN {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap cap)) (hex : ∀ q ∈ ex, w.2.1 q.2 = some q.1) :
    OkV w (ArchOKN w) (fl4ArchDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  have hcps : ∀ c ∈ ex.map Prod.fst, ∃ s, w.2.1 s = some c := by
    intro c h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    exact ⟨q.2, hex q hq⟩
  cases cap
  case pageCap dev p R mt sz m =>
    simp only [fl4ArchDecodeInvocation]
    refine okv_ite (okv_liftME (okv_decodeDeriveSubframeN args cte dev p R mt sz m ex hc hex))
      (okv_ite (okv_liftME (okv_triv fun _ => trivial)) (okv_liftME (okv_archDecodeN label args xs cte _ ex hc hex)))
  case pml4Cap p m =>
    simp only [fl4ArchDecodeInvocation]
    exact okv_ite (okv_liftME (okv_triv fun _ => trivial)) (okv_liftME (okv_archDecodeN label args xs cte _ ex hc hex))
  all_goals (simp only [fl4ArchDecodeInvocation]; exact okv_liftME (okv_archDecodeN label args xs cte _ ex hc hex))

/-! ## The VSpace performs -/

theorem p3_performPageInvocationUnmap (a : ArchCap) (sl : CslotPtr) :
    HV (fun w => P3V N w ∧ w.2.1 sl = some (.archObjectCap a)) (P3V N) (performPageInvocationUnmap (Z := Unit) a sl) := by
  cases a with
  | pageCap dev p R mt sz mp =>
    have hR := hv_reread (N := N) (a := .pageCap dev p R mt sz mp) sl (fun c => updateMapData c none (some .vmNoMap)) rfl rfl
    cases mp with
    | none =>
      simp only [performPageInvocationUnmap]
      first | exact hR | (refine hv_pure_bind ?_; exact hR) | exact hv_bind (hv_uk fun _ => by uk_auto) fun _ => hR
    | some x =>
      obtain ⟨asid, vaddr⟩ := x
      simp only [performPageInvocationUnmap]
      exact hv_bind (hv_uk fun _ => by uk_auto) fun _ => hR
  | _ => exact hv_fail'

macro "ukc" : tactic => `(tactic| (uk_auto; all_goals contradiction))

macro "vs_chain" : tactic => `(tactic| repeat' (first
  | assumption
  | exact hv_fail'
  | (exact hv_bind hv_fail' fun _ => hv_uk fun _ => by ukc)
  | (exact hv_bind (p3_performPageInvocationUnmap _ _) fun _ => hv_uk fun _ => by ukc)
  | (refine hv_pure_bind ?_)
  | (exact hv_mono (hv_uk fun _ => by ukc) fun _ h => h.1)))

theorem p3_performPageTableInvocation (iv : PageTableInvocation) :
    HV (fun w => P3V N w ∧ ArchSpecOKN w (.invokePageTable iv)) (P3V N) (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap ctSlot pde pdSlot vspace =>
    intro σ ⟨hI, c0, hc, hr, hn⟩ y hy
    simp only [performPageTableInvocation] at hy
    exact hv_bind (hv_setCapRE (N := N) hn ctSlot) (fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hc, hr⟩ y hy
  | pageTableUnmap cap ctSlot =>
    cases cap with
    | archObjectCap a =>
      cases a with
      | pageTableCap p ma =>
        have hR := hv_reread (N := N) (a := .pageTableCap p ma) ctSlot (fun c => updateMapData c none none) rfl rfl
        refine hv_pre (P := fun w => P3V N w ∧ w.2.1 ctSlot = some (.archObjectCap (.pageTableCap p ma))) ?_ fun _ h => h
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

theorem p3_performPageDirectoryInvocation (iv : PageDirectoryInvocation) :
    HV (fun w => P3V N w ∧ ArchSpecOKN w (.invokePageDirectory iv)) (P3V N)
      (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap ctSlot pdpte pdptSlot vspace =>
    intro σ ⟨hI, c0, hc, hr, hn⟩ y hy
    simp only [performPageDirectoryInvocation] at hy
    exact hv_bind (hv_setCapRE (N := N) hn ctSlot) (fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hc, hr⟩ y hy
  | pageDirectoryUnmap cap ctSlot =>
    cases cap with
    | archObjectCap a =>
      cases a with
      | pageDirectoryCap p ma =>
        have hR := hv_reread (N := N) (a := .pageDirectoryCap p ma) ctSlot (fun c => updateMapData c none none) rfl rfl
        refine hv_pre (P := fun w => P3V N w ∧ w.2.1 ctSlot = some (.archObjectCap (.pageDirectoryCap p ma))) ?_ fun _ h => h
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

theorem p3_performPdptInvocation (iv : PdptInvocation) :
    HV (fun w => P3V N w ∧ ArchSpecOKN w (.invokePDPT iv)) (P3V N) (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap ctSlot pml4e pml4Slot vspace =>
    intro σ ⟨hI, c0, hc, hr, hn⟩ y hy
    simp only [performPdptInvocation] at hy
    exact hv_bind (hv_setCapRE (N := N) hn ctSlot) (fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hc, hr⟩ y hy
  | pdptUnmap cap ctSlot =>
    cases cap with
    | archObjectCap a =>
      cases a with
      | pdPointerTableCap p ma =>
        have hR := hv_reread (N := N) (a := .pdPointerTableCap p ma) ctSlot (fun c => updateMapData c none none) rfl rfl
        refine hv_pre (P := fun w => P3V N w ∧ w.2.1 ctSlot = some (.archObjectCap (.pdPointerTableCap p ma))) ?_ fun _ h => h
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

theorem p3_performPageInvocation (iv : PageInvocation) :
    HV (fun w => P3V N w ∧ ArchSpecOKN w (.invokePage iv)) (P3V N) (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap ctSlot entries vspace =>
    intro σ ⟨hI, c0, hc, hr, hn⟩ y hy
    simp only [performPageInvocation] at hy
    exact hv_bind (hv_setCapRE (N := N) hn ctSlot) (fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hc, hr⟩ y hy
  | pageUnmap a ctSlot =>
    cases a with
    | pageCap dev p R mt sz mp =>
      refine hv_pre (P := fun w => P3V N w ∧ w.2.1 ctSlot = some (.archObjectCap (.pageCap dev p R mt sz mp))) ?_
        fun _ h => h
      cases mp with
      | none => simp only [performPageInvocation]; vs_chain
      | some x =>
        cases mt <;> (simp only [performPageInvocation]; vs_chain)
    | _ => exact hv_fail'
  | pageGetAddr ptr =>
    simp only [performPageInvocation]
    exact hv_mono (hv_uk fun _ => by ukc) fun _ h => h.1

/-! ## DeriveSubframe -/

theorem natToCref_len (r i : Nat) (h : r ≤ 64) : (natToCref r i).length = r := by
  simp [natToCref, toBl, wordBits]; omega

/-- A non-untyped `cap_insert` keeps every slot but the destination. -/
theorem hv_capInsert_keep (c : Cap) (hnu : ∀ d b n f, c ≠ .untypedCap d b n f) (src dest x : CslotPtr) (hx : x ≠ dest)
    (cx : Cap) : HV (fun w => w.2.1 x = some cx) (fun w => w.2.1 x = some cx) (capInsert (Z := Unit) c src dest) := by
  have hnu' : isUntypedCap c = false := by
    cases c <;> first | rfl | exact absurd rfl (hnu _ _ _ _)
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun _ => ?_
  unfold setUntypedCapAsFull
  rw [if_neg (fun h => by rw [hnu'] at h; exact Bool.false_ne_true h.2.1)]
  refine hv_pure_bind ?_
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
  subst w2
  refine hv_pure_bind ?_
  refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
  subst w3
  refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
  subst w4
  refine hv_bind (hv_updateCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
  subst e
  show (vCap dest c w).2.1 x = _
  rw [vCap_cap, if_neg hx]; exact hw

theorem small_add {p off : ObjRef} {d k : Nat} :
    p + off + BitVec.ofNat 64 (d * 4096) + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (off.toNat + d * 4096 + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
  congr 1; omega

/-- **A 4 KiB page cap inside a large frame** is `RefRel` to the large frame cap. -/
theorem refRel_sub {p off : ObjRef} {r r' : VMRights} {mt : VMMapType} {m : Option (Asid × VSpaceRef)} {d : Nat}
    (h : off.toNat + d * 4096 + 4096 ≤ 2097152) :
    RefRel (.archObjectCap (.pageCap false p r mt .x64LargePage m))
      (.archObjectCap (.pageCap false (p + off + BitVec.ofNat 64 (d * 4096)) r' .vmNoMap .x64SmallPage none)) := by
  refine ⟨?_, rfl, fun _ _ _ e => (by cases e), fun _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e)⟩
  rintro x ⟨k, hk, rfl⟩
  have hk' : k < 4096 := by simpa [pageBitsForSize, pageBits] using hk
  refine ⟨off.toNat + d * 4096 + k, ?_, small_add⟩
  simp only [pageBitsForSize, pageBits, ptTranslationBits]
  omega

theorem hv_mapMx_inv {α β : Type} {f : α → NonDet (State Unit) β} {I : UView → Prop} {S : α → Prop}
    (hf : ∀ x, S x → HV I I (f x)) : ∀ L : List α, (∀ x ∈ L, S x) → HV I I (NonDet.mapMx f L)
  | [], _ => fun σ hσ y hy => by rw [show y = ((), σ) from Set.mem_singleton_iff.1 hy]; exact hσ
  | a :: as, hS => hv_bind (hf a (hS a List.mem_cons_self))
      fun _ => hv_mapMx_inv hf as fun x hx => hS x (List.mem_cons_of_mem _ hx)

/-- **`DeriveSubframe` keeps `P3 N`.** -/
theorem p3_performDeriveSubframe (iv : Fl4SubframeInvocation) :
    HV (fun w => P3V N w ∧ DsOKN w iv) (P3V N) (performDeriveSubframe (Z := Unit) iv) := by
  obtain ⟨src, base, rights, dests⟩ := iv
  intro σ ⟨hI, p, r, mt, m, off, hsrc, hbase, hlen, s1, ptr, bits, g, hs1, hd⟩ y hy
  dsimp only at hsrc hbase hlen hd
  subst hbase
  have hB : bits ≤ 64 := hI.1.2.2.2.2.2.2.2 s1 _ hs1 bits rfl
  have hne : ∀ d ∈ dests, d ≠ src ∧ d ≠ s1 := by
    intro d hdm
    have hn := (hd d hdm).2.2
    refine ⟨fun e => ?_, fun e => ?_⟩
    · subst e; rw [hsrc] at hn; cases hn
    · subst e; rw [hs1] at hn; cases hn
  let I : UView → Prop := fun w => P3V N w ∧ w.2.1 src = some (.archObjectCap (.pageCap false p r mt .x64LargePage m)) ∧
    w.2.1 s1 = some (.cnodeCap ptr bits g)
  have hstep : ∀ x : Nat × CslotPtr, (off.toNat + x.1 * 4096 + 4096 ≤ 2097152 ∧ x.2 ∈ dests) →
      HV I I (capInsert (Z := Unit) (.archObjectCap (.pageCap false (p + off + BitVec.ofNat 64 (x.1 * 4096)) rights
        .vmNoMap .x64SmallPage none)) src x.2) := by
    rintro ⟨i, d⟩ ⟨hi, hdm⟩
    dsimp only at hi hdm ⊢
    obtain ⟨hd1, ⟨j, hd2⟩, -⟩ := hd d hdm
    obtain ⟨hns, hn1⟩ := hne d hdm
    refine hv_and ?_ (hv_and ?_ ?_)
    · refine hv_pre (hv_capInsert3 _ src d) fun w ⟨hw, hws, hw1⟩ => ⟨hw, ⟨_, hws, Or.inr (refRel_sub hi)⟩, ?_⟩
      refine posOK_of_destRef hw.1.2 ⟨s1, _, hw1, ?_, fun _ _ _ e => (by cases e), ?_⟩
      · show d.1 ∈ ({ptr} : Set ObjRef); rw [hd1]; rfl
      · show d.2.length = bits; rw [hd2]; exact natToCref_len bits j hB
    · exact hv_pre (hv_capInsert_keep _ (fun _ _ _ _ e => (by cases e)) src d src (Ne.symm hns) _) fun w h => h.2.1
    · exact hv_pre (hv_capInsert_keep _ (fun _ _ _ _ e => (by cases e)) src d s1 (Ne.symm hn1) _) fun w h => h.2.2
  have hL : ∀ x ∈ (List.range dests.length).zip dests, off.toNat + x.1 * 4096 + 4096 ≤ 2097152 ∧ x.2 ∈ dests := by
    rintro ⟨i, d⟩ hx
    obtain ⟨hi, hdm⟩ := List.of_mem_zip hx
    have := List.mem_range.1 hi
    refine ⟨?_, hdm⟩
    dsimp only
    omega
  exact (hv_mapMx_inv hstep _ hL) σ ⟨hI, hsrc, hs1⟩ y hy |>.1

/-! ## Every arch perform but MakePool -/

theorem p3_archPerform (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a) (σ : State Unit) (hI : P3 N σ)
    (hok : ArchSpecOKN (uV σ) i) : ∀ y ∈ ((archPerformInvocation (Z := Unit) i).run σ).1, P3 N y.2 := by
  intro y hy
  simp only [archPerformInvocation] at hy
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
  show P3V N (uV x.2)
  cases i with
  | invokePageTable iv =>
    exact (hv_bind (p3_performPageTableInvocation iv) fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hok⟩ x hx
  | invokePageDirectory iv =>
    exact (hv_bind (p3_performPageDirectoryInvocation iv) fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hok⟩ x hx
  | invokePDPT iv =>
    exact (hv_bind (p3_performPdptInvocation iv) fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hok⟩ x hx
  | invokePage iv => exact p3_performPageInvocation iv σ ⟨hI, hok⟩ x hx
  | invokeASIDControl a => exact absurd rfl (hm a)
  | invokeASIDPool iv =>
    exact (hv_bind (p3_performAsidPoolInvocation (N := N) iv) fun _ => hv_uk fun _ => by ukc) σ hI x hx
  | invokeIOPort iv => exact (hv_uk (P := P3V N) fun _ => uk_performIoPortInvocation iv) σ hI x hx
  | invokeIOPortControl iv =>
    obtain ⟨z, hz, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hx
    exact p3_performIoportControl iv σ hI hok z hz

/-- **Every arch invocation but `invokeASIDControl` keeps `P3 N`.** -/
theorem p3_fl4ArchPerform (ai : Fl4ArchInvocation) (hm : ∀ a, ai ≠ .spec (.invokeASIDControl a)) (σ : State Unit)
    (hI : P3 N σ) (hok : ArchOKN (uV σ) ai) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) ai).run σ).1, P3 N y.2 := by
  intro y hy
  cases ai with
  | spec i => exact p3_archPerform i (fun a e => hm a (by rw [e])) σ hI hok y hy
  | deriveSubframe iv =>
    simp only [fl4ArchPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (hv_bind (p3_performDeriveSubframe iv) fun _ => hv_uk fun _ => by ukc) σ ⟨hI, hok⟩ x hx
  | _ => exact (p3e_of_uk fun _ => by simp only [fl4ArchPerformInvocation]; uk_auto) σ hI y hy

end

end Fl4Proofs.P3.SInvU
