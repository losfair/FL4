/-
P3 (DESIGN.md §9), invariant line G1 (vfh2): **lookups land in full CNode
slots** (spec side only, outside the JAtZ cone).

`CnDom` (SpecInvVfhK, l4v `valid_cap`'s `cap_table_at` of every CNode cap, a
carried invariant) makes every slot a CSpace lookup returns a slot of an object
holding every index of the slot's length (`CnFull`), so it is no TCB's
fault-handler slot (`vfh_notBad_full`):

* `OkV σ0 Pr m` (vih3's, SpecInvValidIrqHandlersY): from any state with the caps
  of `σ0`, every `.ok` outcome keeps them and its value satisfies `Pr`.
* `vfh_rab`: `resolve_address_bits'` from a `CnOk` root returns a slot
  `(oref, offset)` with `CnFull σ0 oref offset.length` (the offset has the
  radix's length; a root read on the way is a slot cap, `CnOk` by `CnDom`).
* `vfh_lookupSlotForCnodeOp` (target / source / pivot slots),
  `vfh_lookupSlotForThread` (root: the thread's `tcbCtable`, slot `(t, idx 0)`),
  `vfh_lookupCap` (the looked-up cap is a slot cap: `CnOk`).
-/
import Fl4Proofs.P3.SpecInvVfhP
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

theorem cnFull_view {σ σ' : State Unit} (e : hV σ' = hV σ) {p : ObjRef} {r : Nat} (h : CnFull σ p r) :
    CnFull σ' p r := fun l hl => by rw [hV_cap e]; exact h l hl

theorem cnOk_view {σ σ' : State Unit} (e : hV σ' = hV σ) {c : Cap} (h : CnOk σ c) : CnOk σ' c :=
  fun p r g hc => cnFull_view e (h p r g hc)

/-- A full slot is no fault-handler slot. -/
theorem vfh_notBad_cnFull {σ : State Unit} {sl : CslotPtr} (h : CnFull σ sl.1 sl.2.length) : ¬ vfh_Bad σ sl :=
  vfh_notBad_full h

/-! ## `OkV` combinators -/

section OkVs
variable {ε α β : Type} {σ0 : State Unit}

theorem vfh_okv_whenE_bind {Pr : β → Prop} (c : Prop) [Decidable c] (e : ε) {g : Unit → NonDetE (State Unit) ε β}
    (hg : ¬ c → OkV σ0 Pr (g ())) : OkV σ0 Pr (NonDetE.whenE c (NonDetE.throwError e) >>= g) :=
  fun s hs => okdAt_whenE_bind c e fun h => hg h s hs

theorem vfh_okdAt_handleE {ε' : Type} {P : State Unit → α → Prop} {σ : State Unit} {m : NonDetE (State Unit) ε α}
    {h : ε → NonDetE (State Unit) ε' α} (hm : OkDAt σ P m) (hh : ∀ e s0, OkDAt s0 (fun _ _ => False) (h e)) :
    OkDAt σ P (NonDetE.handleE m h) := by
  intro a s ha
  unfold NonDetE.handleE at ha
  rw [ExceptT.run_mk] at ha
  obtain ⟨⟨r, s1⟩, h1, h2⟩ := ha
  cases r with
  | ok b =>
    have e := Set.mem_singleton_iff.1 h2
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact hm _ _ h1
  | error e => exact (hh e s1 a s h2).elim

theorem vfh_okv_handleE {ε' : Type} {Pr : α → Prop} {m : NonDetE (State Unit) ε α}
    {h : ε → NonDetE (State Unit) ε' α} (hm : OkV σ0 Pr m) (hh : ∀ e s0, OkDAt s0 (fun _ _ => False) (h e)) :
    OkV σ0 Pr (NonDetE.handleE m h) := fun s hs => vfh_okdAt_handleE (hm s hs) hh

theorem vfh_okv_liftE_fail {Pr : α → Prop} : OkV σ0 Pr (NonDetE.liftE (ε := ε) (NonDet.fail : NonDet (State Unit) α)) := by
  intro s _ a s' h
  obtain ⟨x, hx, -⟩ := mem_liftE_inv' h
  exact hx.elim

/-- `get_cap` read as a slot fact of the anchor. -/
theorem vfh_okv_getCap (sl : CslotPtr) :
    OkV σ0 (fun c => capOpt (σ0.kheap sl.1) sl.2 = some c) (NonDetE.liftE (ε := ε) (getCap (Z := Unit) sl)) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨o, r⟩ := sl
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  rw [e1]
  exact ⟨hs, by rw [← hV_cap hs]; exact e2⟩

end OkVs

/-! ## `resolve_address_bits` -/

theorem vfh_offset_len (cref guard : List Bool) (r : Nat) (h : ¬ cref.length < r + guard.length) :
    ((cref.drop guard.length).take r).length = r := by
  simp only [List.length_take, List.length_drop]
  omega

/-- **`resolve_address_bits'` from a `CnOk` root lands in a full slot.** -/
theorem vfh_rab (σ0 : State Unit) (hd : CnDom σ0) (p : Cap × CapRef) (hc : CnOk σ0 p.1) :
    OkV σ0 (fun r : CslotPtr × CapRef => CnFull σ0 r.1.1 r.1.2.length) (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · rename_i oref radix guard heq
    have hfull : CnFull σ0 oref radix := hc oref radix guard heq
    split
    · exact vfh_okv_liftE_fail
    · refine vfh_okv_whenE_bind _ _ fun _ => vfh_okv_whenE_bind _ _ fun hlen => ?_
      refine okv_returnOk_bind ?_
      dsimp only
      split
      · exact okv_returnOk (by rw [vfh_offset_len _ _ _ hlen]; exact hfull)
      · refine okv_bind (vfh_okv_getCap _) fun nc hnc => ?_
        split
        · exact vfh_rab σ0 hd _ (hd _ _ hnc)
        · exact okv_returnOk (by dsimp only; rw [vfh_offset_len _ _ _ hlen]; exact hfull)
  · exact okv_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega

theorem vfh_resolveAddressBits (σ0 : State Unit) (hd : CnDom σ0) (p : Cap × CapRef) (hc : CnOk σ0 p.1) :
    OkV σ0 (fun r : CslotPtr × CapRef => CnFull σ0 r.1.1 r.1.2.length) (resolveAddressBits (Z := Unit) p) := by
  unfold resolveAddressBits; exact vfh_rab σ0 hd p hc

/-- **Target / source / pivot slots are full.** -/
theorem vfh_lookupSlotForCnodeOp (σ0 : State Unit) (hd : CnDom σ0) (isSource : Bool) (croot : Cap) (ptr : CapRef)
    (depth : Nat) (hc : CnOk σ0 croot) :
    OkV σ0 (fun sl : CslotPtr => CnFull σ0 sl.1 sl.2.length)
      (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp
  split
  · refine vfh_okv_whenE_bind _ _ fun _ => ?_
    unfold lookupErrorOnFailure
    refine vfh_okv_handleE ?_ (fun e s0 => okdAt_throw _)
    refine okv_returnOk_bind ?_
    refine okv_bind (vfh_resolveAddressBits σ0 hd _ hc) fun r hr => ?_
    obtain ⟨sl, rem⟩ := r
    dsimp only
    split
    · exact okv_returnOk hr
    · exact okv_throw _
  · exact okv_throw _

/-- The thread's CSpace root is a slot cap. -/
theorem vfh_okv_getTcb_ctable (σ0 : State Unit) (hd : CnDom σ0) (t : ObjRef) :
    OkV σ0 (fun tcb : Tcb => CnOk σ0 tcb.tcbCtable) (NonDetE.liftE (ε := LookupFailure) (NonDet.getsThe (getTcb (Z := Unit) t))) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  unfold NonDet.getsThe at hy
  cases ht : getTcb (Z := Unit) t s with
  | none => rw [ht] at hy; exact hy.elim
  | some x =>
    rw [ht] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    refine ⟨hs, ?_⟩
    have hk := getTcb_kheap ht
    have hc : capOpt (s.kheap t) (tcbCnodeIndex 0) = some x.tcbCtable := by
      rw [hk, capOpt_tcb]; unfold tcbCnodeMap
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
    rw [hV_cap hs] at hc
    exact hd (t, tcbCnodeIndex 0) _ hc

theorem vfh_lookupSlotForThread (σ0 : State Unit) (hd : CnDom σ0) (t : ObjRef) (c : CapRef) :
    OkV σ0 (fun r : CslotPtr × CapRef => CnFull σ0 r.1.1 r.1.2.length) (lookupSlotForThread (Z := Unit) t c) := by
  unfold lookupSlotForThread
  exact okv_bind (vfh_okv_getTcb_ctable σ0 hd t) fun tcb htcb => vfh_resolveAddressBits σ0 hd _ htcb

/-- A looked-up cap is a slot cap of the anchor: `CnOk`. -/
theorem vfh_lookupCap (σ0 : State Unit) (hd : CnDom σ0) (t : ObjRef) (c : CapRef) :
    OkV σ0 (fun cap => CnOk σ0 cap) (lookupCap (Z := Unit) t c) := by
  unfold lookupCap
  refine okv_bind (vfh_lookupSlotForThread σ0 hd t c) fun r _ => ?_
  obtain ⟨sl, _⟩ := r
  dsimp only
  exact okv_mono (vfh_okv_getCap sl) fun cap h => hd sl cap h

theorem vfh_lookupCapAndSlot (σ0 : State Unit) (hd : CnDom σ0) (t : ObjRef) (c : CapRef) :
    OkV σ0 (fun r : Cap × CslotPtr => CnOk σ0 r.1 ∧ capOpt (σ0.kheap r.2.1) r.2.2 = some r.1)
      (lookupCapAndSlot (Z := Unit) t c) := by
  unfold lookupCapAndSlot
  refine okv_bind (vfh_lookupSlotForThread σ0 hd t c) fun r _ => ?_
  obtain ⟨sl, _⟩ := r
  dsimp only
  exact okv_bind (vfh_okv_getCap sl) fun cap h => okv_returnOk ⟨hd sl cap h, h⟩

end

end Fl4Proofs.P3.SInv
