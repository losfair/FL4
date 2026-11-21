/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **the decode's carry for `ScKindR`**
(spec side only; sl4 handoff 2, decode half): every cap a perform will write is
`KD` to a cap read from a slot at the decode state.

* `kd_mask`, `kd_upd` (`mask_cap` / `update_cap_data` keep SC-ness and the range,
  or give null); `kd_deriveCap` is SpecInvSlKB's.
* `CnK w` and **`okv_cnK`** (CNode copy / mint / move / mutate / rotate; sl3's
  `okv_cnNF` with `KD` in place of `NF`, plus copy / mint through `derive_cap`).
* `KArchS σ1` / `KArch σ1` (page / table / directory / PDPT map: the written cap
  is the invoked arch cap with mapping data, same range; unmap: the invoked cap)
  and `kr_okd_archDecode` / `kr_okd_fl4ArchDecode` (`OkDAt`, from the invoked
  cap's `KOk`); `kr_okd_decodeIrqHandler` (the set-handler cap is an extra cap).
* **`KInv σ1`** (CNode `KCn`, IRQ handler `KIh`, arch `KArch`) and
  **`kr_okv_fl4Decode`**: at a `ScKindR` decode state `σd` whose invoked slot
  holds the invoked cap and whose extra caps sit in their slots, every decoded
  invocation satisfies `KInv σd`. DeriveSubframe's caps come from ut8's `DsOKN`
  (SpecInvUtP1) at the perform.
-/
import Fl4Proofs.P3.SpecInvSlKG
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvDom (OkDAt okdAt_bind okdAt_returnOk okdAt_throw okdAt_ite okdAt_liftME okdAt_returnOk_bind)

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## The cap transformations -/

theorem kd_mask (R : CapRights) (c : Cap) : KD c (maskCap R c) := by
  cases c with
  | archObjectCap a =>
    cases a <;> simp_all [KD, maskCap, capRightsUpdate, acapRightsUpdate, capRng, acRng, aobjRef]
  | _ => simp_all [KD, maskCap, capRightsUpdate, capRng, objRefs]

theorem kd_cnode {r : ObjRef} {b b' : Nat} {g g' : List Bool} : KD (.cnodeCap r b g) (.cnodeCap r b' g') :=
  ⟨(fun _ _ e => by cases e), fun _ h => Or.inr ⟨h, (fun _ e => by cases e)⟩⟩

theorem kd_ep {r : ObjRef} {b b' : Badge} {c c' : CapRights} : KD (.endpointCap r b c) (.endpointCap r b' c') :=
  ⟨(fun _ _ e => by cases e), fun _ h => Or.inr ⟨h, (fun _ e => by cases e)⟩⟩

theorem kd_ntfn {r : ObjRef} {b b' : Badge} {c c' : CapRights} :
    KD (.notificationCap r b c) (.notificationCap r b' c') :=
  ⟨(fun _ _ e => by cases e), fun _ h => Or.inr ⟨h, (fun _ e => by cases e)⟩⟩

/-- CNode mint / mutate: null or a CNode cap to the same object and radix. -/
theorem kd_cnode_ite {r : ObjRef} {bits : Nat} {g : List Bool} (P : Prop) [Decidable P] (g' : List Bool) :
    KD (.cnodeCap r bits g) (if P then .nullCap else .cnodeCap r bits g') := by
  by_cases h : P
  · rw [if_pos h]; exact kd_null _
  · rw [if_neg h]; exact kd_cnode

theorem kd_upd (b : Bool) (x : Data) (c : Cap) : KD c (updateCapData b x c) := by
  cases c with
  | archObjectCap a =>
    simp only [updateCapData, isEpCap, isNtfnCap, isCnodeCap, isArchCap, archUpdateCapData, Cap.theArchCap]
    exact kd_refl _
  | cnodeCap r bits g =>
    simp only [updateCapData, isEpCap, isNtfnCap, isCnodeCap, theCnodeCap, Bool.false_eq_true, ↓reduceIte]
    exact kd_cnode_ite _ _
  | _ =>
    simp only [updateCapData, isEpCap, isNtfnCap, isCnodeCap, isArchCap, theCnodeCap]
    (try split_ifs) <;> first | exact kd_null _ | exact kd_refl _ | exact kd_cnode | exact kd_ep | exact kd_ntfn |
      (split <;> first | exact kd_null _ | exact kd_cnode)

/-! ## CNode -/

/-- The caps a CNode invocation writes are `KD` to caps read from slots of `w`. -/
def CnK (w : UView) : CnodeInvocation → Prop
  | .insertCall c src _ => ∃ c0, w.2.1 src = some c0 ∧ KD c0 c
  | .moveCall c src _ => ∃ c0, w.2.1 src = some c0 ∧ KD c0 c
  | .rotateCall c1 c2 s1 s2 _ => (∃ c0, w.2.1 s1 = some c0 ∧ KD c0 c1) ∧ (∃ c0, w.2.1 s2 = some c0 ∧ KD c0 c2)
  | _ => True

set_option maxHeartbeats 4000000 in
theorem okv_cnK {w : UView} (label : Data) (args : List Data) (cap : Cap) (ex : List Cap) :
    OkV w (CnK w) (decodeCnodeInvocation (Z := Unit) label args cap ex) := by
  unfold decodeCnodeInvocation
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind
    (okv_returnOk_bind (okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun destSlot => ?_)))
  refine okv_ite ?_ (okv_ite (okv_returnOk (P := CnK w) trivial) (okv_ite (okv_returnOk (P := CnK w) trivial)
    (okv_ite ?_ (okv_ite ?_ (okv_throw _)))))
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))
    refine okv_bind_uk (fun _ => uk_ensureEmpty _) fun _ => ?_
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun hnn => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun x => ?_
    obtain ⟨rights, capData, isMove⟩ := x
    dsimp only
    refine okv_returnOk_bind ?_
    cases isMove
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine okv_bind (fun _ => uk_deriveCap _ _) (fun σ _ a s h => kd_deriveCap _ _ _ σ s h)
        fun nc hnc => okv_whenE_bind fun _ => okv_returnOk ⟨_, hsc, kd_trans ?_ hnc⟩
      cases capData with
      | none => exact kd_mask _ _
      | some x => exact kd_trans (kd_mask rights _) (kd_upd _ _ _)
    · simp only [↓reduceIte]
      refine okv_returnOk_bind (okv_whenE_bind fun _ => okv_returnOk ⟨_, hsc, ?_⟩)
      cases capData with
      | none => exact kd_mask _ _
      | some x => exact kd_trans (kd_mask rights _) (kd_upd _ _ _)
  · exact okv_bind_uk (fun _ => by uk_auto) fun _ => okv_bind_uk (fun _ => by uk_auto) fun _ => okv_returnOk trivial
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind
      (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))))))
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_bind_uk (fun _ => uk_lookupPivotSlot _ _ _) fun pivotSlot => ?_
    refine okv_whenE_bind fun _ => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_
    refine okv_liftE_getCap_bind fun srcCap hsc => okv_whenE_bind fun _ => ?_
    refine okv_liftE_getCap_bind fun pivCap hpc => okv_whenE_bind fun _ => ?_
    refine okv_returnOk_bind (okv_returnOk_bind (okv_whenE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk ?_))
    exact ⟨⟨_, hsc, kd_upd _ _ _⟩, ⟨_, hpc, kd_upd _ _ _⟩⟩

theorem kcn_of {σ : State Unit} (hK : ScKindR σ) (ci : CnodeInvocation) (h : CnK (uV σ) ci) : KCn σ ci := by
  cases ci with
  | insertCall c s d => obtain ⟨c0, h0, hd⟩ := h; exact (kok_of_slot hK h0).kd hd
  | moveCall c s d => obtain ⟨c0, h0, hd⟩ := h; exact (kok_of_slot hK h0).kd hd
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨⟨a, ha, hda⟩, ⟨b, hb, hdb⟩⟩ := h
    exact ⟨(kok_of_slot hK ha).kd hda, (kok_of_slot hK hb).kd hdb⟩
  | _ => trivial

/-! ## Arch and IRQ handler decodes -/

theorem okdAt_liftE_fail {ε α : Type} {σ : State Unit} {P : State Unit → α → Prop} :
    OkDAt σ P (NonDetE.liftE (ε := ε) (NonDet.fail : NonDet (State Unit) α)) := by
  intro a s h
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨_, h, _⟩ := h
  exact h.elim

/-- An arch cap whose range lies in a `KOk` arch cap's. -/
theorem kok_arch_rng {σ0 : State Unit} {a a' : ArchCap} (h : KOk σ0 (.archObjectCap a))
    (hr : ∀ r ∈ acRng a', r ∈ acRng a) : KOk σ0 (.archObjectCap a') :=
  h.kd (kd_arch_rng hr)

def KArchS (σ1 : State Unit) : ArchInvocation → Prop
  | .invokePage (.pageMap c _ _ _) => KOk σ1 c
  | .invokePage (.pageUnmap a _) => KOk σ1 (.archObjectCap a)
  | .invokePageTable (.pageTableMap c _ _ _ _) => KOk σ1 c
  | .invokePageTable (.pageTableUnmap c _) => KOk σ1 c
  | .invokePageDirectory (.pageDirectoryMap c _ _ _ _) => KOk σ1 c
  | .invokePageDirectory (.pageDirectoryUnmap c _) => KOk σ1 c
  | .invokePDPT (.pdptMap c _ _ _ _) => KOk σ1 c
  | .invokePDPT (.pdptUnmap c _) => KOk σ1 c
  | _ => True

def KArch (σ1 : State Unit) : Fl4ArchInvocation → Prop
  | .spec i => KArchS σ1 i
  | _ => True

set_option maxHeartbeats 16000000 in
theorem kr_okd_archDecode (σ1 : State Unit) (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr)
    (cap : ArchCap) (ex : List (Cap × CslotPtr)) (hk : KOk σ1 (.archObjectCap cap)) (s : State Unit) :
    OkDAt s (fun _ i => KArchS σ1 i) (archDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  cases cap <;> simp only [archDecodeInvocation, decodePageInvocation, decodePageTableInvocation,
    decodePageDirectoryInvocation, decodePdptInvocation, decodeIoportControlInvocation, decodePortInvocation]
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_liftE_fail
    | exact okdAt_returnOk trivial
    | exact okdAt_returnOk hk
    | (refine okdAt_returnOk_bind ?_)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | (apply okdAt_ite)
    | split)
  all_goals refine okdAt_returnOk ?_
  all_goals first
    | trivial
    | exact hk
    | (apply kok_arch_rng hk; intro r hr; simpa [acRng, aobjRef] using hr)

set_option maxHeartbeats 8000000 in
theorem kr_okd_fl4ArchDecode (σ1 : State Unit) (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr)
    (cap : ArchCap) (ex : List (Cap × CslotPtr)) (hk : KOk σ1 (.archObjectCap cap)) (s : State Unit) :
    OkDAt s (fun _ i => KArch σ1 i) (fl4ArchDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  unfold fl4ArchDecodeInvocation
  split
  all_goals repeat' (first
    | exact okdAt_liftME (kr_okd_archDecode σ1 label args xs cte _ ex hk _)
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | (apply okdAt_ite))

theorem kr_okd_decodeIrqHandler (σ1 : State Unit) (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr))
    (hex : ∀ p ∈ cps, KOk σ1 p.1) (s : State Unit) :
    OkDAt s (fun _ i => KIh σ1 i) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  split
  · exact okdAt_returnOk trivial
  · split
    · split
      · rename_i hne
        obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨cap, slot⟩ := q
        have hq := hex (cap, slot) List.mem_cons_self
        show OkDAt s _ (if isNtfnCap cap ∧ AllowSend ∈ capRights cap then _ else _)
        split
        · exact okdAt_returnOk hq
        · exact okdAt_throw _
      · exact okdAt_throw _
    · split
      · exact okdAt_returnOk trivial
      · exact okdAt_throw _

/-! ## The dispatcher -/

/-- **What a perform needs from its decode** (sl5). -/
def KInv (σ1 : State Unit) : Fl4Invocation → Prop
  | .invokeCNode i => KCn σ1 i
  | .invokeIRQHandler i => KIh σ1 i
  | .invokeArchObject a => KArch σ1 a
  | _ => True

theorem okv_of_okdAt {ε α : Type} {w : UView} {P : α → Prop} {m : NonDetE (State Unit) ε α}
    (h : ∀ s, OkDAt s (fun _ a => P a) m) : OkV w P m :=
  fun σ _ a s hs => h σ a s hs

set_option maxHeartbeats 8000000 in
/-- **Every decoded invocation satisfies `KInv σd`** at a `ScKindR` decode state
whose invoked slot holds the invoked cap and whose extra caps sit in their slots. -/
theorem kr_okv_fl4Decode (σd : State Unit) (hK : ScKindR σd) (fp : Bool) (label : Data) (args : List Data)
    (ci : CapRef) (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef)
    (hc : (uV σd).2.1 sl = some cap) (hex : ∀ p ∈ ex, (uV σd).2.1 p.2 = some p.1) :
    OkV (uV σd) (KInv σd) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  have hexk : ∀ p ∈ ex, KOk σd p.1 := fun p hp => kok_of_slot hK (hex p hp)
  cases cap with
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_mono (okv_cnK _ _ _ _) fun ci h => kcn_of hK ci h))
  | irqHandlerCap irq =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_of_okdAt fun s => kr_okd_decodeIrqHandler σd label irq ex hexk s)
  | archObjectCap ac =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_of_okdAt fun s => kr_okd_fl4ArchDecode σd label args ci sl ac ex (kok_of_slot hK hc) s)
  | _ =>
    unfold fl4DecodeInvocation
    (try dsimp only)
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | split)

end

end Fl4Proofs.P3.SInvL
