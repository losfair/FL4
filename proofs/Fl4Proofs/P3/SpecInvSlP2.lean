/-
P3 (DESIGN.md §9), invariant line G1 (sl3): **ScLive across `invoke_tcb`**
(sl2 handoff 3, second part; spec side only).

* `ScKind` across `cap_insert` under `check_cap_at`: `same_object_as` makes the
  inserted cap an SC cap exactly when the source cap is one, naming what it names
  (`so_facts`, `sk_setCap_g`, `sk_capInsert_so`, `sk_checkCapAt_ins`).
* `sdp_installTcbCap` / `sdp_installTcbFrameCap`: the deletion carrier `SDP I N :=
  ILP N [] ∧ DX I` (il2's / ut7's `ILP` with `DX`) across one install.
* `slk_capDelete_fh`: deleting a slot holding a null or endpoint cap keeps `SL I K`
  for any `K` (no recursion; sb2's `fh_step` pattern): `threadControlSched`'s
  fault-handler install keeps the names of its targets.
* **`sl_invokeTcb`**: one case per arm; `threadControlSched`'s bind by
  `sl_schedContextBindTcb`, both ends held (vi3's `TcbTg`).
-/
import Fl4Proofs.P3.SpecInvSlP
import Fl4Proofs.P3.SpecInvSbX3
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## `same_object_as` -/

set_option maxHeartbeats 16000000 in
theorem so_facts {c c' : Cap} (h : sameObjectAs c c') :
    (∀ r ∈ objRefs c, r ∈ objRefs c') ∧ (∀ r b, c = .schedContextCap r b → ∃ b', c' = .schedContextCap r b') ∧
      (∀ r b, c' = .schedContextCap r b → ∃ b', c = .schedContextCap r b') ∧ ¬ isUntypedCap c' ∧
      c' ≠ .nullCap := by
  cases c with
  | archObjectCap a =>
    cases c' with
    | archObjectCap a' =>
      simp only [sameObjectAs] at h
      refine ⟨fun r hr => ?_, (fun _ _ e => by cases e), (fun _ _ e => by cases e), (by simp [isUntypedCap]),
        (fun e => by cases e)⟩
      simp only [objRefs, Set.mem_setOf_eq] at hr ⊢
      cases a <;> cases a' <;> simp_all [sameAobjectAs, archSameRegionAs, aobjRef]
    | _ => simp [sameObjectAs, sameRegionAs] at h
  | _ =>
    cases c' <;>
      simp_all [sameObjectAs, sameRegionAs, objRefs, isEpCap, isNtfnCap, isCnodeCap, isThreadCap,
        isSchedContextCap, objRefOf, bitsOf, isUntypedCap, isArchCap]

/-! ## `ScKind` across a general cap write -/

theorem sk_setCap_g (c : Cap) (sl : CslotPtr) (σ : State Unit)
    (hc1 : ∀ r b, c = .schedContextCap r b → ∃ s0 b', s0 ≠ sl ∧ SInvU.capAt σ s0 = some (.schedContextCap r b'))
    (hc2 : ∀ r ∈ objRefs c, (∃ b, c = .schedContextCap r b) ∨
      ∃ s0 c0, SInvU.capAt σ s0 = some c0 ∧ r ∈ objRefs c0 ∧ ∀ r' b', c0 ≠ .schedContextCap r' b') :
    IKp ScKind σ (setCap (Z := Unit) c sl) := by
  intro hK y hy
  obtain ⟨-, hne, hsl, -, -⟩ := SInvU.setCap_out hy
  have key : ∀ x, SInvU.capAt y.2 x = SInvU.capAt σ x ∨ (x = sl ∧ SInvU.capAt y.2 x = some c) := by
    intro x
    by_cases e : x = sl
    · subst e
      rcases hsl with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl (hne x e)
  intro s r b s' c' hs hs' hrr
  change SInvU.capAt y.2 s = _ at hs
  change SInvU.capAt y.2 s' = _ at hs'
  rcases key s with h | ⟨es, h⟩
  · have hs0 : SInvU.capAt σ s = some (.schedContextCap r b) := by rw [← h]; exact hs
    rcases key s' with h' | ⟨rfl, h'⟩
    · exact hK s r b s' c' hs0 (by show SInvU.capAt σ s' = _; rw [← h']; exact hs') hrr
    · rw [h'] at hs'; cases hs'
      rcases hc2 r hrr with ⟨b', e⟩ | ⟨s0, c0, h0, hr0, hn0⟩
      · exact ⟨b', e⟩
      · obtain ⟨b', e⟩ := hK s r b s0 c0 hs0 h0 hr0
        exact absurd e (hn0 r b')
  · rw [h] at hs; cases hs
    obtain ⟨s0, b0, hs0n, hs0⟩ := hc1 r b rfl
    rcases key s' with h' | ⟨rfl, h'⟩
    · exact hK s0 r b0 s' c' hs0 (by show SInvU.capAt σ s' = _; rw [← h']; exact hs') hrr
    · rw [h'] at hs'; cases hs'; exact ⟨b, rfl⟩

/-- **`cap_insert`** of a cap `same_object_as` the source's cap. -/
theorem sk_capInsert_so (newCap : Cap) (src dest : CslotPtr) (σ : State Unit) (c' : Cap)
    (hc : SInvU.capAt σ src = some c') (hso : sameObjectAs newCap c') :
    IKp ScKind σ (capInsert (Z := Unit) newCap src dest) := by
  obtain ⟨hor, hsc, hsc', hnu, hnn⟩ := so_facts hso
  intro hσ x hx
  unfold capInsert at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨srcCap, s1⟩ := y1
  simp only at e1 hc1; subst s1
  have es : srcCap = c' := Option.some.inj (hc1.symm.trans hc)
  rw [es] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨e3, hc3⟩ := SInvU.getCap_capAt hy3
  obtain ⟨oldCap, s3⟩ := y3
  simp only at e3 hc3; subst s3
  obtain ⟨y4, ⟨ha, rfl⟩, hx⟩ := hx
  simp only at ha
  obtain ⟨y5, hy5, hx⟩ := hx
  have e5 : y5.2 = σ := by
    unfold setUntypedCapAsFull at hy5
    split at hy5
    · rename_i hu; exact absurd hu.1 hnu
    · rw [Set.mem_singleton_iff.1 hy5]
  obtain ⟨y6, hy6, hx⟩ := hx
  rw [e5] at hy6
  have hne : src ≠ dest := by
    intro e; subst e; rw [hc, ha] at hc3; cases hc3; exact hnn rfl
  have h6 : ScKind y6.2 := by
    refine sk_setCap_g newCap dest σ (fun r b e => ?_) (fun r hr => ?_) hσ y6 hy6
    · obtain ⟨b', e'⟩ := hsc r b e
      exact ⟨src, b', hne, by rw [hc, e']⟩
    · by_cases hs : ∃ b, newCap = .schedContextCap r b
      · exact Or.inl hs
      · refine Or.inr ⟨src, c', hc, hor r hr, fun r' b' e => ?_⟩
        obtain ⟨b'', e''⟩ := hsc' r' b' e
        subst e''
        simp [objRefs] at hr; subst hr
        exact hs ⟨b'', rfl⟩
  refine (?_ : IK ScKind _) y6.2 h6 x hx
  repeat' (first | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

theorem sk_checkCapAt_ins (nc : Cap) (src : CslotPtr) (cap2 : Cap) (slot2 dest : CslotPtr) :
    IK ScKind (checkCapAt (Z := Unit) nc src (checkCapAt cap2 slot2 (capInsert nc src dest))) := by
  unfold checkCapAt
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy
  obtain ⟨c', s1⟩ := y
  simp only at e1 hc1; subst s1
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · rename_i hso
    obtain ⟨y2, hy2, hx⟩ := hx
    obtain ⟨e2, -⟩ := SInvU.getCap_capAt hy2
    rw [e2] at hx
    dsimp only at hx
    split at hx
    · exact sk_capInsert_so nc src dest σ c' hc1 hso hσ x hx
    · rw [Set.mem_singleton_iff.1 hx]; exact hσ
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

/-! ## One install -/

/-- The deletion carrier with UtInv3 at the IRQ node. -/
def SDP (I : ObjRef × ObjRef) (N : Irq → ObjRef) (σ : State Unit) : Prop := ILP N [] σ ∧ DX I σ

section T
variable {I : ObjRef × ObjRef} {N : Irq → ObjRef}

theorem sdu_of_sdp {σ : State Unit} (h : SDP I N σ) : SDU I σ := ⟨ilp_ilu h.1, h.2⟩

theorem dx_checkIns (nc : Cap) (src : CslotPtr) (cap2 : Cap) (slot2 dest : CslotPtr) :
    IK (DX I) (checkCapAt (Z := Unit) nc src (checkCapAt cap2 slot2 (capInsert nc src dest))) :=
  dx_ik (sl_checkCapAt _ _ _ (sl_checkCapAt _ _ _ (sl_capInsert _ _ _)))
    (fun _ => SInvB.sb_checkCapAt _ _ _ (SInvB.sb_checkCapAt _ _ _ (SInvB.sb_capInsert _ _ _)))
    (isk_checkCapAt _ _ _ (isk_checkCapAt _ _ _ (isk_capInsert _ _ _))) (sk_checkCapAt_ins _ _ _ _ _)

theorem sdp_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) (hn : n < 6) :
    IKE (SDP I N) (installTcbCap (Z := Unit) target slot n o) := by
  intro σ hσ y hy
  refine ⟨ilp_installTcbCap N target slot n o hn σ hσ.1 y hy, ?_⟩
  revert y hy
  refine (?_ : HKE (SDP I N) (DX I) (installTcbCap (Z := Unit) target slot n o)) σ hσ
  cases o with
  | none => exact fun σ h y hy => ike_returnOk _ σ h.2 y hy
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine hke_bind (R := DX I) (fun σ h y hy => (sdu_capDelete _ σ (sdu_of_sdp h) y hy).2)
      (fun _ => hk_of_ik ?_) (fun _ h => h)
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (dx_checkIns _ _ _ _ _)

theorem sdp_installTcbFrameCap (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (SDP I N) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  intro σ hσ y hy
  refine ⟨ilp_installTcbFrameCap N target slot buffer σ hσ.1 y hy, ?_⟩
  revert y hy
  refine (?_ : HKE (SDP I N) (DX I) (installTcbFrameCap (Z := Unit) target slot buffer)) σ hσ
  cases buffer with
  | none => exact fun σ h y hy => ike_returnOk _ σ h.2 y hy
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    simp only [installTcbFrameCap]
    refine hke_bind (R := DX I) (fun σ h y hy => (sdu_capDelete _ σ (sdu_of_sdp h) y hy).2)
      (fun _ => hk_of_ik ?_) (fun _ h => h)
    refine ike_bind (ike_liftE (dx_ik (by sl_auto) (fun _ => by sb_auto) (by isk_auto)
      (sk_of_uk fun _ => by uk_auto))) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · cases frame with
      | none => exact ik_pure _
      | some q => obtain ⟨nc, src⟩ := q; exact dx_checkIns _ _ _ _ _
    · exact ike_bind (ike_liftE (ik_gets _)) fun _ => ike_liftE (dx_ik (by sl_auto) (fun _ => by sb_auto)
        (by isk_auto) (sk_of_uk fun _ => by uk_auto))

end T

/-! ## Deleting a fault-handler slot keeps `SL I K` -/

section F
variable {I : ObjRef × ObjRef} {K : List ObjRef}

def FPreL (I : ObjRef × ObjRef) (K : List ObjRef) : RecDelCall → State Unit → Prop
  | .cTEDeleteCall s _, σ => SL I K σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .finaliseSlotCall s _, σ => SL I K σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .reduceZombieCall _ _ _, _ => False

def FPostL (I : ObjRef × ObjRef) (K : List ObjRef) : RecDelCall → Except Unit (Bool × Cap) → State Unit → Prop
  | .cTEDeleteCall _ _, _, σ => SL I K σ
  | .finaliseSlotCall s _, _, σ => SL I K σ ∧ ∀ c, SInvU.capAt σ s = some c → SInvB.FhC c
  | .reduceZombieCall _ _ _, _, σ => SL I K σ

theorem fhC_nn {c : Cap} (h : SInvB.FhC c) (p : ObjRef) : ¬ NCap p c := by
  rcases h with rfl | ⟨r, b, rs, rfl⟩ <;> exact id

theorem flk_step (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (FPreL I K k) (FPostL I K k) (f k)) (k : RecDelCall) :
    HR (FPreL I K k) (FPostL I K k) (recDelF (Z := Unit) f k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩⟩ := mem_bindE' hy
    · have hp := hrec (.finaliseSlotCall s e) σ hσ z hz
      obtain ⟨b, info⟩ := a
      try dsimp only at hy
      obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz2
        rw [mem_ret_ok hy]
        show SL I K x.2
        unfold NonDet.when at hx
        split at hx
        · exact sl_emptySlot_p s info z.2 (fun p c0 h0 => fhC_nn (hp.2 c0 h0) p) (sl_postCapDeletion _) hp.1 x hx
        · rw [Set.mem_singleton_iff.1 hx]; exact hp.1
      · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
        rw [hx] at her; cases her
    · exact (hrec (.finaliseSlotCall s e) σ hσ z hz).1
  | finaliseSlotCall s e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := getCap_capAt hx
    simp only at e1 hc
    subst e1
    have hfc := hσ.2 cap hc
    try dsimp only at hy1
    split at hy1
    · rw [mem_ret_ok hy1]; exact hσ
    · rename_i hnn
      obtain ⟨r, b, rs, rfl⟩ : ∃ r b rs, cap = .endpointCap r b rs := hfc.resolve_left hnn
      obtain ⟨z, hz, H⟩ := mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hx2)
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨⟨u, σ3'⟩, hx3', e3⟩ := hx3
      have hb3 : SL I K σ3' := (ik_when _ (sl_cancelAllIpc _)) _ hσ.1 _ hx3'
      have hv3 := (ik_when _ (uk_cancelAllIpc _)) _ rfl _ hx3'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 e3)
      try dsimp only at hy3
      rw [if_pos (show capRemoveable Cap.nullCap s from trivial)] at hy3
      rw [mem_ret_ok hy3]
      refine ⟨hb3, fun c h => hσ.2 c ?_⟩
      have := congrArg (fun w : UView => w.2.1 s) hv3
      exact this.symm.trans h
  | reduceZombieCall c s e => intro σ hσ; exact hσ.elim

theorem flk_recDel (k : RecDelCall) :
    HR (FPreL I K k) (FPostL I K k) (recDel (Z := Unit) k : NonDet (State Unit) (Except Unit (Bool × Cap))) := by
  unfold recDel
  exact hr_lfp (FPreL I K) (FPostL I K) (fun f hf k => flk_step f hf k) k

/-- **`cap_delete` of a slot holding a null or endpoint cap keeps `SL I K`.** -/
theorem slk_capDelete_fh (sl : CslotPtr) (σ : State Unit) (hc : ∀ c, SInvU.capAt σ sl = some c → SInvB.FhC c)
    (hσ : SL I K σ) : ∀ y ∈ ((capDelete (Z := Unit) sl).run σ).1, SL I K y.2 := by
  intro y hy
  unfold capDelete at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨er, -, rfl⟩⟩ := mem_bindE' hy
  · rw [mem_ret_ok hy]
    exact flk_recDel (.cTEDeleteCall sl true) σ ⟨hσ, hc⟩ z hz
  · exact flk_recDel (.cTEDeleteCall sl true) σ ⟨hσ, hc⟩ z hz

/-- The fault-handler install over a null or endpoint cap keeps `SL I K`. -/
theorem slk_installTcbCap3 (t : ObjRef) (slot : CslotPtr) (fh : Option (Cap × CslotPtr)) (σ : State Unit)
    (hF : ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c) (hσ : SL I K σ) :
    ∀ y ∈ ((installTcbCap (Z := Unit) t slot 3 fh).run σ).1, SL I K y.2 := by
  intro y hy
  unfold installTcbCap at hy
  rcases fh with _ | ⟨nc, src⟩
  · rw [mem_ret_ok hy]; exact hσ
  · try dsimp only at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' := slk_capDelete_fh _ σ hF hσ z hz
      exact (ike_unlessE _ (ike_liftE (sl_checkCapAt _ _ _ (sl_checkCapAt _ _ _ (sl_capInsert _ _ _))))) z.2 hz' y hy
    · exact slk_capDelete_fh _ σ hF hσ z hz

end F

/-! ## `invoke_tcb` -/

section I
variable {I : ObjRef × ObjRef} {N : Irq → ObjRef}

/-- The fault-handler slot of `t` holds a null or endpoint cap. -/
def FhAt (t : ObjRef) (σ : State Unit) : Prop := ∀ c, SInvU.capAt σ (t, tcbCnodeIndex 3) = some c → SInvB.FhC c

/-- `threadControlSched`'s bind fact: its fault-handler slot is a valid handler's. -/
def TcbFh (σ : State Unit) : TcbInvocation → Prop
  | .threadControlSched t _ _ _ _ (some (some _)) => FhAt t σ
  | _ => True

theorem sl_tcSched (t : ObjRef) (slot : CslotPtr) (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef))
    (sc : Option (Option ObjRef)) (σ : State Unit) (hσ : SDP I N σ)
    (hT : SInvI.TcbTg (uV σ) (.threadControlSched t slot fh mcp prio sc))
    (hF : TcbFh σ (.threadControlSched t slot fh mcp prio sc)) :
    ∀ y ∈ ((invokeTcb (Z := Unit) (.threadControlSched t slot fh mcp prio sc)).run σ).1, SL I [] y.2 := by
  intro y hy
  simp only [invokeTcb] at hy
  rcases sc with _ | _ | c
  · obtain ⟨z1, hz1, ⟨u1, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    swap
    · exact (sdp_installTcbCap (N := N) t slot 3 fh (by decide) σ hσ z1 hz1).2.1
    have h1 : SL I [] z1.2 := (sdp_installTcbCap (N := N) t slot 3 fh (by decide) σ hσ z1 hz1).2.1
    refine (?_ : SLKE I [] _) z1.2 h1 y hy
    unfold NonDet.maybeM
    sl_auto
  · obtain ⟨z1, hz1, ⟨u1, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    swap
    · exact (sdp_installTcbCap (N := N) t slot 3 fh (by decide) σ hσ z1 hz1).2.1
    have h1 : SL I [] z1.2 := (sdp_installTcbCap (N := N) t slot 3 fh (by decide) σ hσ z1 hz1).2.1
    refine (?_ : SLKE I [] _) z1.2 h1 y hy
    unfold NonDet.maybeM
    (try dsimp only)
    sl_auto
  · have ht := hT.1
    obtain ⟨sz, hc⟩ := hT.2 c rfl
    have h0 : SL I [c, t] σ := sl_cons (sl_cons hσ.2.1 (Or.inl (hasN_of_held ht rfl))) (Or.inl (hasN_of_held hc rfl))
    have hcK : c ∈ [c, t] := List.mem_cons_self
    have htK : t ∈ [c, t] := List.mem_cons_of_mem _ List.mem_cons_self
    refine sl_mono (K := [c, t]) ?_ fun _ h => by cases h
    obtain ⟨z1, hz1, ⟨u1, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    swap
    · exact slk_installTcbCap3 t slot fh σ hF h0 z1 hz1
    have h1 : SL I [c, t] z1.2 := slk_installTcbCap3 t slot fh σ hF h0 z1 hz1
    refine (?_ : SLKE I [c, t] _) z1.2 h1 y hy
    refine ike_bind (ike_liftE (by sl_auto)) fun _ => ike_bind (ike_liftE (by sl_auto)) fun _ =>
      ike_bind (ike_liftE ?_) fun _ => ike_returnOk _
    unfold NonDet.maybeM
    exact sl_schedContextBindTcb c t hcK htK

/-- **`invoke_tcb` keeps `SL I []`** (one case per arm). -/
theorem sl_invokeTcb (ti : TcbInvocation) (σ : State Unit) (hσ : SDP I N σ) (hT : SInvI.TcbTg (uV σ) ti)
    (hF : TcbFh σ ti) : ∀ y ∈ ((invokeTcb (Z := Unit) ti).run σ).1, SL I [] y.2 := by
  cases ti
  case threadControlSched t slot fh mcp prio sc => exact sl_tcSched t slot fh mcp prio sc σ hσ hT hF
  case threadControlCaps t slot fh th cr vr buf =>
    intro y hy
    refine ((?_ : IKE (SDP I N) _) σ hσ y hy).2.1
    simp only [invokeTcb]
    exact ike_bind (sdp_installTcbCap _ _ 3 _ (by decide)) fun _ => ike_bind (sdp_installTcbCap _ _ 4 _ (by decide))
      fun _ => ike_bind (sdp_installTcbCap _ _ 0 _ (by decide)) fun _ =>
        ike_bind (sdp_installTcbCap _ _ 1 _ (by decide)) fun _ =>
          ike_bind (sdp_installTcbFrameCap _ _ _) fun _ => ike_returnOk _
  case notificationControl t n =>
    intro y hy
    refine (?_ : SLKE I [] _) σ hσ.2.1 y hy
    cases n <;> simp only [invokeTcb] <;> sl_auto
  all_goals
    intro y hy
    refine (?_ : SLKE I [] _) σ hσ.2.1 y hy
    simp only [invokeTcb]; sl_auto

end I

end

end Fl4Proofs.P3.SInvL
