/-
P3 (DESIGN.md §9), CSpace: **the CNode cap at the composite relation**
(`CnodeXHyp`).

* `capMove_nko`, `capSwap_nko`, `invoke_cn`: the spec side of a copy, move
  or rotate: `CnK`, the heap changed at the invocation's slots' objects only.
* `Steps.cnTrace`: the restart and a CNode-only step (StepSem's `cslot`)
  from `CnTrace` (CnodeCopy), the CSpace relation after.
* `cnode_copyX`, `cnode_rotateX`: `cnode::decode` at the copy, mint, move,
  mutate and rotate labels, to `XTop` (`Steps.xtop`).
-/
import Fl4Proofs.P3.XTopCaps
import Fl4Proofs.P3.DomSched
import Fl4Proofs.P3.CnodeDecode
import Fl4Proofs.P3.SpecNKO
import Fl4Proofs.P3.XTopStepT
import Fl4Proofs.P3.SlotOrig
import Fl4Proofs.P3.SpecKSz
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- **`cap_move` changes the heap at the source's and the destination's
objects only.** -/
theorem capMove_nko (c : Cap) (src dest : CslotPtr) :
    NKO {src.1, dest.1} (capMove (Z := Unit) c src dest) := by
  unfold capMove setCdt setOriginal
  repeat (first | exact nko_getCap _ | exact nko_setCap _ _ (by simp) | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_fail | exact nko_gets _ | exact nko_get |
    exact nko_assert _ | exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)) |
    (apply nko_ite) | split)

/-- **`cap_swap` changes the heap at the two slots' objects only.** -/
theorem capSwap_nko (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) :
    NKO {s1.1, s2.1} (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt setOriginal
  repeat (first | exact nko_getCap _ | exact nko_setCap _ _ (by simp) | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_fail | exact nko_gets _ | exact nko_get |
    exact nko_assert _ | exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)) |
    (apply nko_ite) | split)

theorem nko_mono {α : Type} {Ps Ps' : Set ObjRef} {m : NonDet (State Unit) α} (h : Ps ⊆ Ps') (hm : NKO Ps m) :
    NKO Ps' m := fun σ x hx p hp => hm σ x hx p (fun h' => hp (h h'))

/-- **The spec side of a CNode copy, move or rotate**: `CnK`, and the heap
kept outside the invocation's slots' objects. -/
theorem invoke_cn {inv : CnodeInvocation} (hne : invSlots inv ≠ []) {σ σ' : State Unit}
    (h : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((invokeCnode (Z := Unit) inv).run σ).1) :
    CnK σ σ' ∧ ∀ p, (∀ sl ∈ invSlots inv, p ≠ sl.1) → σ'.kheap p = σ.kheap p := by
  cases inv with
  | insertCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    refine ⟨capInsert_nkn c a b σ x hx, fun p hp => capInsert_nko c a b σ x hx p ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hp _ (by simp [invSlots]), hp _ (by simp [invSlots])⟩
  | moveCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    refine ⟨capMove_nkn c a b σ x hx, fun p hp => capMove_nko c a b σ x hx p ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hp _ (by simp [invSlots]), hp _ (by simp [invSlots])⟩
  | rotateCall c1 c2 a b d =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    have hp3 : ∀ p, (∀ sl ∈ invSlots (.rotateCall c1 c2 a b d), p ≠ sl.1) → p ∉ ({a.1, b.1, d.1} : Set ObjRef) := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hp _ (by simp [invSlots]), hp _ (by simp [invSlots]), hp _ (by simp [invSlots])⟩
    split_ifs at hx with hs
    · refine ⟨capSwap_nkn c1 a c2 b σ x hx, fun p hp => ?_⟩
      refine nko_mono (Ps := {a.1, b.1}) (fun q hq => ?_) (capSwap_nko c1 a c2 b) σ x hx p (hp3 p hp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine ⟨nkn_bind (capMove_nkn c2 b d) (fun _ => capMove_nkn c1 a b) σ x hx, fun p hp => ?_⟩
      refine nko_bind (Ps := {a.1, b.1, d.1})
        (nko_mono (fun q hq => ?_) (capMove_nko c2 b d)) (fun _ => nko_mono (fun q hq => ?_) (capMove_nko c1 a b))
        σ x hx p (hp3 p hp)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        rcases hq with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        rcases hq with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  | revokeCall _ => exact absurd rfl hne
  | deleteCall _ => exact absurd rfl hne
  | cancelBadgedSendsCall _ => exact absurd rfl hne

/-- **The spec side of a CNode copy, move or rotate keeps the objects'
kinds** (`KSz`). -/
theorem invoke_ksz {inv : CnodeInvocation} (hne : invSlots inv ≠ []) {σ σ' : State Unit}
    (h : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((invokeCnode (Z := Unit) inv).run σ).1) : KSz σ σ' := by
  cases inv with
  | insertCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    exact capInsert_nkz c a b σ x hx
  | moveCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    exact capMove_nkz c a b σ x hx
  | rotateCall c1 c2 a b d =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    split_ifs at hx with hs
    · exact capSwap_nkz c1 a c2 b σ x hx
    · exact nkz_bind (capMove_nkz c2 b d) (fun _ => capMove_nkz c1 a b) σ x hx
  | revokeCall _ => exact absurd rfl hne
  | deleteCall _ => exact absurd rfl hne
  | cancelBadgedSendsCall _ => exact absurd rfl hne

/-- **The spec's original bits of a CNode copy, move or rotate** are kept
off the invocation's slots (`capInsert_orig`, `capMove_orig`,
`capSwap_orig`). -/
theorem invoke_orig {inv : CnodeInvocation} (hne : invSlots inv ≠ []) {σ σ' : State Unit}
    (h : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((invokeCnode (Z := Unit) inv).run σ).1) :
    ∀ sl, sl ∉ invSlots inv → σ'.isOriginalCap sl = σ.isOriginalCap sl := by
  intro sl hsl
  cases inv with
  | insertCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    exact capInsert_orig c a b σ x hx sl fun e => hsl (by simp [invSlots, e])
  | moveCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    exact capMove_orig c a b σ x hx sl fun e => hsl (by rcases e with e | e <;> simp [invSlots, e])
  | rotateCall c1 c2 a b d =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    have hn : ¬ (sl = a ∨ sl = b ∨ sl = d) := fun e => hsl (by rcases e with e | e | e <;> simp [invSlots, e])
    split_ifs at hx with hs
    · exact no_mono (d' := fun sl => sl = a ∨ sl = b ∨ sl = d) (fun q hq => by rcases hq with h | h <;> simp [h])
        (capSwap_orig c1 a c2 b) σ x hx sl hn
    · exact no_bind (d := fun sl => sl = a ∨ sl = b ∨ sl = d)
        (no_mono (fun q hq => by rcases hq with h | h <;> simp [h]) (capMove_orig c2 b d))
        (fun _ => no_mono (fun q hq => by rcases hq with h | h <;> simp [h]) (capMove_orig c1 a b)) σ x hx sl hn
  | revokeCall _ => exact absurd rfl hne
  | deleteCall _ => exact absurd rfl hne
  | cancelBadgedSendsCall _ => exact absurd rfl hne

/-- **`cap_move` clears its source's original bit** (its last step). -/
theorem capMove_orig_src (c : Cap) (src dest : CslotPtr) {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (capMove (Z := Unit) c src dest σ).1) : x.2.isOriginalCap src = false := by
  unfold capMove at hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  unfold setOriginal at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  simp

/-- **A slot a CNode move or rotate may leave null has no original bit**
(`NullSrc`, `capMove_orig_src`). -/
theorem invoke_nullOrig {inv : CnodeInvocation} {σ σ' : State Unit}
    (h : ((.ok (), σ') : Except Unit Unit × State Unit) ∈ ((invokeCnode (Z := Unit) inv).run σ).1)
    {sl : CslotPtr} (hn : NullSrc inv sl) : σ'.isOriginalCap sl = false := by
  cases inv with
  | moveCall c a b =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    simp only [NullSrc] at hn
    rw [hn]
    exact capMove_orig_src c a b hx
  | rotateCall c1 c2 a b d =>
    obtain ⟨x, hx, e⟩ := Sched.liftE_mem_inv h
    simp only at e; subst e
    obtain ⟨hsa, had⟩ := hn
    rw [hsa]
    split_ifs at hx with hs
    · exact absurd hs had
    · obtain ⟨_, _, hx⟩ := hx
      exact capMove_orig_src c1 a b hx
  | insertCall _ _ _ => exact hn.elim
  | revokeCall _ => exact hn.elim
  | deleteCall _ => exact hn.elim
  | cancelBadgedSendsCall _ => exact hn.elim

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A CNode copy, move or rotate as primitive steps**: the restart, then a
CNode-only step (`cslot`), from FL4's trace (`CnTrace`) and the spec's
outcome. -/
theorem Steps.cnTrace {th : TypedHeap} (hP : Placed th) {s s2 s' : S} {a : A}
    {σ σ1 σ' : Fl4Spec.State Unit} {G' : MdbGhost} {ct : U64} {x : Fl4Spec.Tcb}
    (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x)) (htcb : th ct = some .tcb)
    (hs2 : sched.set_thread_state st s ct sched.TS_RESTART = ok s2)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hC : CurRun σ) (hR1 : StateRel th (L.mem s2) σ1) (hks : L.ksb s2 = L.ksb s)
    {inv : Fl4Spec.CnodeInvocation} (hne : invSlots inv ≠ [])
    (hrun : (Fl4Spec.invokeCnode (Z := Unit) inv).run σ1 = ({(.ok (), σ')}, False))
    (hF : Vs.SlotFrame2 (L := L) th s2 s')
    (hsl : ∀ sl ∈ invSlots inv, ∃ p r, sl.1 = p.bv ∧ th p = some (.cnode r) ∧ sl.2.length = r)
    (hcap : ∀ y, IsSlot th y → (∀ sl ∈ invSlots inv, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s2) y)
    (hCK : CoverKept th (L.mem s2) (L.mem s')) (hUK : UtKept th (L.mem s2) (L.mem s'))
    (hCR : CRel th (L.mem s') σ' G') (hFI : FinInv th (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTK : TypedKept th (L.mem s2) (L.mem s')) (hDl : DelInv th (L.mem s2) → DelInv th (L.mem s'))
    (hDLs : ∀ sl ∈ invSlots inv, ∃ p, sl.1 = p.bv ∧ DestLive th (L.mem s2) (L.ksb s) p)
    (hUS : UtSrc th (L.mem s2) (L.mem s') σ1 σ') (hVT : Vs.VsSlotsT th (L.mem s2) (L.mem s'))
    (hLW : CnLive (L.mem s2) (L.mem s') (invSlots inv))
    (hNS : ∀ sl ∈ invSlots inv, capV (L.mem s') (cslotAddr sl) = .Null → NullSrc inv sl) :
    Steps (L := L) arI th s a σ s' a σ' := by
  refine (Steps.restart arI hcur hk htcb hs2 hst hC).trans arI fun Q hQ => ?_
  have hmem : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
      ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1 := by rw [hrun]; rfl
  obtain ⟨hcn, hO⟩ := invoke_cn hne hmem
  have hkc : KeepC σ1 σ' := keepC_of (Ps := {p | ∃ sl ∈ invSlots inv, p = sl.1}) hcn
    (fun p hp => hO p fun sl hs e => hp ⟨sl, hs, e⟩) (fun p ⟨sl, hs, e⟩ => by
      obtain ⟨q, r, h1, h2, -⟩ := hsl sl hs
      obtain ⟨cs, h, -⟩ := hR1.cnode q r h2
      exact ⟨r, cs, by rw [e, h1]; exact h⟩)
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ1.isOriginalCap sl = true ∨ AbsSlot th sl := fun sl h => by
    by_cases hs : sl ∈ invSlots inv
    · obtain ⟨p, r, h1, h2, h3⟩ := hsl sl hs
      exact Or.inr ⟨p, h1, Or.inl (by rw [h3]; exact h2)⟩
    · exact Or.inl (by rw [← invoke_orig hne hmem sl hs]; exact h)
  have hW : ∀ sl ∈ invSlots inv, ∃ p r, sl.1 = p.bv ∧ th p = some (.cnode r) ∧ sl.2.length = r ∧
      DestLive th (L.mem s2) (L.ksb s2) p := fun sl hs => by
    obtain ⟨p, r, h1, h2, h3⟩ := hsl sl hs
    obtain ⟨p', h1', hD⟩ := hDLs sl hs
    have e : p' = p := P1.eq_of_bv (h1'.symm.trans h1)
    subst e
    exact ⟨p', r, h1, h2, h3, by rw [hks]; exact hD⟩
  have hoW : ∀ sl, σ'.isOriginalCap sl = true → σ1.isOriginalCap sl = true ∨ sl ∈ invSlots inv := fun sl h => by
    by_cases hs : sl ∈ invSlots inv
    · exact Or.inr hs
    · exact Or.inl (by rw [← invoke_orig hne hmem sl hs]; exact h)
  refine hQ.cslot s2 s' a σ1 σ' G' hcn hkc hCK hUK horig
    ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨y, k, hy, hk', e⟩ => hn ⟨y, hy, ?_⟩⟩ hCR hFI
    (by rw [hks]; exact hMO) (fun t ht => ?_) hTK (fun t ht => ?_) (invoke_ksz hne hmem) hDl (invSlots inv) hW
    hcap hoW hUS hVT hLW fun sl hsl h => invoke_nullOrig hmem (hNS sl hsl h)
  · have hf := hy.fit hP
    have := hk'.lt
    have hv := wordOf_val (a := y) (k := k) (by omega)
    rw [e, hv]; omega
  · have h1 : IsSlot th (slotOf t 1) := ⟨t, 1, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne' : ∀ sl ∈ invSlots inv, slotOf t 1 ≠ cslotAddr sl := by
      intro sl hsl' e
      obtain ⟨q, r, hq1, hq2, hq3⟩ := hsl sl hsl'
      obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := sl) ⟨q, hq1, Or.inl (by rw [hq3]; exact hq2)⟩
      have hpp : p = q := P1.eq_of_bv (hp1.symm.trans hq1)
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt th t 1) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hq2] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hcap _ h1 hne']
  · have h1 : IsSlot th (slotOf t 3) := ⟨t, 3, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne' : ∀ sl ∈ invSlots inv, slotOf t 3 ≠ cslotAddr sl := by
      intro sl hsl' e
      obtain ⟨q, r, hq1, hq2, hq3⟩ := hsl sl hsl'
      obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := sl) ⟨q, hq1, Or.inl (by rw [hq3]; exact hq2)⟩
      have hpp : p = q := P1.eq_of_bv (hp1.symm.trans hq1)
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt th t 3) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hq2] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hcap _ h1 hne']

set_option maxHeartbeats 4000000 in
/-- **A copy, move or rotate's outcome at any `X` reached by the primitive
steps** (`cn_topX` generalised, as the IRQ caps' `XS` leaves): `X` at the
start, `X` after every run of primitive steps from it, `XTop` from `X`. -/
theorem cn_topXS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hstep : ∀ s' a' σ', Steps (L := L) arI Z.th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s' a' σ', X s' a' σ' → XTop (L := L) AR s' a' σ')
    {ct : U64} (hcur : σ.curThread = ct.bv) {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    {root : capability.Cap} (hroot : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = root)
    (hq : InvPost (L := L) Z.th σ Z.G m s (res.1, res.2.1) (CnTrace (L := L) Z.th ct σ root s) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) X σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, hX0⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hrunI, hR', hV', hM', hC', hI', hFI', hSt, s2, hne, hs2, hF, hsl, hcap, hDI,
      hTK, hDLs, hUS, hVT, ⟨hCK, hUK⟩, hLW, hNSr⟩ := hq
    obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
    have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
    obtain ⟨hX1, hks, -⟩ := hX.restart' hC hcur hs2 hst'
    have hstp : Steps (L := L) arI Z.th s a' σ s' a' σ' :=
      Steps.cnTrace arI hX.rel.1 hcur hk htcb hs2 hst hC hX1.rel.2.1.1 hks hne hrunI hF hsl hcap hCK hUK
        ⟨hR', hV', hM', hC', hI'⟩ hFI' (hSt.okv hX.rel.2.2.2.2.1) hTK hDI (hDLs hroot) (hUS σ1 σ' hst hrunI) hVT hLW hNSr
    have hXa := hstep _ _ _ hstp
    obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXa
    have hx : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1 := by rw [hrunI]; rfl
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, hXa⟩

set_option maxHeartbeats 4000000 in
/-- **A copy, move or rotate's outcome at `XTop`**: from `InvPost` with
FL4's trace (`CnTrace`) and the arch state kept, `TopPostDMX`. -/
theorem cn_topX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s ar σ) (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T) (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    {ct : U64} (hcur : σ.curThread = ct.bv) {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    {root : capability.Cap} (hroot : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = root)
    (hq : InvPost (L := L) Z.th σ Z.G m s (res.1, res.2.1) (CnTrace (L := L) Z.th ct σ root s) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m)
      s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, hX⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hrunI, hR', hV', hM', hC', hI', hFI', hSt, s2, hne, hs2, hF, hsl, hcap, hDI,
      hTK, hDLs, hUS, hVT, ⟨hCK, hUK⟩, hLW, hNSr⟩ := hq
    obtain ⟨htcb, x, hk⟩ := hX.curTcb hcur
    have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
    obtain ⟨hX1, hks, -⟩ := hX.restart' hC hcur hs2 hst'
    have hstp : Steps (L := L) arI Z.th s a' σ s' a' σ' :=
      Steps.cnTrace arI hX.rel.1 hcur hk htcb hs2 hst hC hX1.rel.2.1.1 hks hne hrunI hF hsl hcap hCK hUK
        ⟨hR', hV', hM', hC', hI'⟩ hFI' (hSt.okv hX.rel.2.2.2.2.1) hTK hDI (hDLs hroot) (hUS σ1 σ' hst hrunI) hVT hLW hNSr
    obtain ⟨Z', hZ'⟩ := hstp.xtop arI hAM hDel rfl hX hKA hTh
    have hx : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1 := by rw [hrunI]; rfl
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, ⟨Z', hZ'⟩⟩

/-- **`CnodeXHyp` at the copy, mint, move, mutate and rotate labels**
(28..32): `cnode_copy_refines`, `cnode_rotate_refines`, then `cn_topX`. -/
theorem decode_invocation_cnode_copyX {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (lbl : U64) (hl : 28 ≤ lbl.val ∧ lbl.val ≤ 32) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (hroot : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 31
    · exact WP.spec_mono (cnode_copy_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd lbl slbl hlbl hcp length buf
        ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 hx0 _ hex.one hI hFI hact hcur htcb)
        fun res h => cn_topX arI hAM hX hKA hC hTh hDel hcur hroot h
    · have e : lbl = fl4_abi.label.CNodeRotate := UScalar.eq_of_val_eq (by rw [lbl_rotate_val]; omega)
      subst e
      exact WP.spec_mono (cnode_rotate_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl
        (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 x1 hx0 hx1 _
        hex hI hFI hact hcur htcb) fun res h => cn_topX arI hAM hX hKA hC hTh hDel hcur hroot h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

/-- **`decode_invocation_cnode_copyX` at any `X` reached by the primitive
steps** (`cn_topXS`). -/
theorem decode_invocation_cnode_copyXS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    (hstep : ∀ s' a' σ', Steps (L := L) arI Z.th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s' a' σ', X s' a' σ' → XTop (L := L) AR s' a' σ')
    (lbl : U64) (hl : 28 ≤ lbl.val ∧ lbl.val ≤ 32) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (hroot : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI X s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 31
    · exact WP.spec_mono (cnode_copy_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd lbl slbl hlbl hcp length buf
        ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 hx0 _ hex.one hI hFI hact hcur htcb)
        fun res h => cn_topXS arI hX hC hX0 hstep hXX hcur hroot h
    · have e : lbl = fl4_abi.label.CNodeRotate := UScalar.eq_of_val_eq (by rw [lbl_rotate_val]; omega)
      subst e
      exact WP.spec_mono (cnode_rotate_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl
        (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra x0 x1 hx0 hx1 _
        hex hI hFI hact hcur htcb) fun res h => cn_topXS arI hX hC hX0 hstep hXX hcur hroot h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

/-- **Hypothesis: CancelBadgedSends at `XTop`** (the endpoint side, for the
IPC proofs; the plain `XLeaf` shape): from `XTop`, the caller's restart then
`cancel_badged_sends` of endpoint `p` and badge `b`, against the spec's
`cancel_badged_sends` from `σ1` (the state after the spec's restart). -/
def XCancelBadgedHyp (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (ct p b : U64) :
    Prop :=
  XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s2 ← endpoint.cancel_badged_sends st s1 p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, ar))
    (Fl4Spec.cancelBadgedSends (Z := Unit) p.bv b.bv σ1)

set_option maxHeartbeats 4000000 in
/-- **A CancelBadgedSends's outcome at `XTop`**: from `InvPost` with FL4's
trace (`CancelTrace`), the restart alone for badge 0 (`XTopAt.restart'`), the
named `XCancelBadgedHyp` otherwise. -/
theorem cn_cancel_topX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv)
    (hcan : ∀ σ1 p b sl, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Endpoint p b true true true true →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      b ≠ 0#u64 → XCancelBadgedHyp (L := L) AR s ar σ σ1 ct p b)
    {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : CancelDec (L := L) Z.th ct σ m s (res.1, res.2.1) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m)
      s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, hX⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, p, b, rfl, ⟨sl, hsl, hcV⟩, s2, hs2, h0, h1⟩ := hq
    have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
    by_cases hb : b = 0#u64
    · subst hb
      have e := h0 rfl
      subst e
      obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs2 hst'
      have hrun0 : (Fl4Spec.invokeCnode (Z := Unit)
          (.cancelBadgedSendsCall (absCap (.Endpoint p 0#u64 true true true true)))).run σ1 =
          ({(.ok (), σ1)}, False) := by
        show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv (0#u64 : U64).bv (rightsOf true true true true)))).run σ1 = _
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when]
        have : ¬ ((0#u64 : U64).bv ≠ 0) := by simp
        simp only [this, ↓reduceIte]
        exact run_liftE rfl
      have hx : ((.ok (), σ1) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p 0#u64 true true true true)))).run σ1).1 := by rw [hrun0]; rfl
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ1),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX1.rel.1, hX1.rel.2.1,
          hX1.rel.2.2.1, hX1.rel.2.2.2.1, hX1.rel.2.2.2.2.1⟩, ⟨Z, hX1⟩⟩
    · have hl := hcan σ1 p b sl hsl hcV hst hb ⟨Z, hX⟩
      rw [hs2] at hl
      simp only [bind_ok] at hl
      rw [h1 hb] at hl
      simp only [bind_ok, WP.spec_ok] at hl
      obtain ⟨-, z, hz, hRT, hXT⟩ := hl
      have hbv : b.bv ≠ 0 := by
        intro h; apply hb; apply UScalar.eq_of_val_eq
        have := congrArg BitVec.toNat h; simpa using this
      have hx : ((.ok (), z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p b true true true true)))).run σ1).1 := by
        show _ ∈ ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv b.bv (rightsOf true true true true)))).run σ1).1
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when, hbv, ne_eq, not_false_eq_true, ↓reduceIte]
        exact mem_liftE (x := ((), z.2)) hz
      obtain ⟨th', G2, hPl, hCR2, hFI2, hD2, hMO2⟩ := hRT
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], z.2),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨th', G2, Or.inl ⟨rfl, rfl⟩, hPl, hCR2, hFI2, hD2, hMO2⟩, hXT⟩

/-- **`CnodeXHyp` at the CancelBadgedSends label** (27): `cnode_cancel_refines`
(the decode, `cnode_cancel_dec`), then `cn_cancel_topX` (with
`XCancelBadgedHyp`). -/
theorem decode_invocation_cnode_cancelX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (hcan : ∀ σ1 p b sl, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Endpoint p b true true true true →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      b ≠ 0#u64 → XCancelBadgedHyp (L := L) AR s ar σ σ1 ct p b)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.CNodeCancelBadgedSends length slot (.CNode p r gs g)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_cancel_dec arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hFI hact hcur htcb)
      fun res h => cn_cancel_topX hX hC hcur hcan h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

include arI in
set_option maxHeartbeats 4000000 in
/-- **A Revoke, Delete or CancelBadgedSends in `cnode_other_refines`'s
scope, at `XTop`**: from `InvPost` with FL4's trace (`OtherTrace`): the
restart alone (`XTopAt.restart'`), or the restart and a trivially
finalised cap's deletion, a slot edit (`XTopAt.slotStepT`; the spec's
`cap_delete` is then `empty_slot`, `CnK`). -/
theorem cn_other_topX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : InvPost (L := L) Z.th σ Z.G m s (res.1, res.2.1) (OtherTrace (L := L) Z.th ct σ s) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (XTop (L := L) AR) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m)
      s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, hX⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hrunI, hR', hV', hM', hC', hI', hFI', hSt, s2, hs2, htr⟩ := hq
    have hst' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by rw [← hcur]; exact hst
    obtain ⟨hX1, hks, -⟩ := hX.restart' hC hcur hs2 hst'
    rcases htr with ⟨rfl, hnone⟩ | ⟨px, rx, idx, c, rfl, hpx, hl, hc, hcn, htk, hF, hcap⟩
    · have e : σ' = σ1 := by
        have := hrunI.symm.trans (hnone σ1 hst)
        simpa using this
      subst e
      have hx : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ').1 := by rw [hrunI]; rfl
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ', hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX1.rel.1, hX1.rel.2.1,
          hX1.rel.2.2.1, hX1.rel.2.2.2.1, hX1.rel.2.2.2.2.1⟩, ⟨Z, hX1⟩⟩
    · -- the spec's `cap_delete` is `empty_slot`
      have hP := hX.rel.1
      obtain ⟨hR1, hV1, hM1, hC1, hI1⟩ := hX1.rel.2.1
      obtain ⟨fin, htk1⟩ := htk σ1 hst
      obtain ⟨c', a1, hc', hca, hg⟩ := hR1.slot_cap (Z := Unit) (sl := (px.bv, idx)) rfl (by rw [hl]; exact hpx)
      rw [hc] at hc'
      have e : c' = c := by simpa using hc'.symm
      subst e
      rw [hca.abs] at hg
      obtain ⟨-, -, -, σ'', G'', hes, -⟩ := spec_exists
        (empty_full (ar := arI) Z.th s2 a' σ1 Z.G hR1 hV1 hP hM1 hC1 hI1 hpx hl hc hcn)
      have hcd := capDelete_triv (px.bv, idx) σ1 σ'' hg (Or.inr ⟨c', fin, rfl, hcn, htk1⟩) hes
      have e : σ' = σ'' := by
        have := hrunI.symm.trans hcd
        simpa using this
      subst e
      have hcn' : CnK σ1 σ' := emptySlot_null_nkn _ σ1 ((), σ') (by rw [hes]; rfl)
      -- FL4's slot edit
      have hw : P1.WritesIn st s2 s' (Sched.SlotWd Z.th) := by
        refine ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨y, k, hy, hk', e⟩ => hn (Sched.slotSpan_wd hP hb ⟨y, hy, ?_⟩)⟩
        have hf := hy.fit hP
        have := hk'.lt
        have hv := wordOf_val (a := y) (k := k) (by omega)
        rw [e, hv]; omega
      have hTS : ∀ t, Z.th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s2) (slotOf t 1) := by
        intro t ht
        have h1 : IsSlot Z.th (slotOf t 1) := ⟨t, 1, Or.inr ⟨ht, by decide⟩, rfl⟩
        have hne : slotOf t 1 ≠ cslotAddr (px.bv, idx) := by
          intro e
          obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := Z.th) (sl := (px.bv, idx))
            ⟨px, rfl, Or.inl (by rw [hl]; exact hpx)⟩
          have hpp : p = px := P1.eq_of_bv hp1.symm
          subst hpp
          have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt Z.th t 1) hi (fun hh => by
            obtain ⟨h, -⟩ := hh; subst h; rw [hpx] at ht; cases ht)
          rw [e, hp2] at this; omega
        rw [capAt_capV, capAt_capV, hcap _ h1 hne]
      have hX' := XTopAt.slotStepT hX1 hw hcn' ⟨hR', hV', hM', hC', hI'⟩ hFI'
        (by rw [hks]; exact hSt.okv hX.rel.2.2.2.2.1)
        (CurOK.of_slot1 hX1.fin.2.2.2.2 (by have e := congrArg Fl4Spec.AbstractState.curThread hcn'.1; exact e) hTS)
      have hx : ((.ok (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.deleteCall (px.bv, idx))).run σ1).1 := by rw [hrunI]; rfl
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩, hX'.rel.1, hX'.rel.2.1,
          hX'.rel.2.2.1, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, ⟨_, hX'⟩⟩

/-- **`CnodeXHyp` at the Revoke, Delete and CancelBadgedSends labels**
(25..27) within `cnode_other_refines`'s scope (`OtherTriv`: a childless
Revoke, the Delete of an empty or trivially finalised slot, a
CancelBadgedSends doing nothing): `cnode_other_refines`, then
`cn_other_topX`. -/
theorem decode_invocation_cnode_otherX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    (lbl : U64) (hl : 25 ≤ lbl.val ∧ lbl.val ≤ 27) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (hT : ∀ y0 y1 rest dsl, args = y0 :: y1 :: rest →
      (Fl4Spec.lookupTargetSlot (Z := Unit) (absCap (.CNode p r gs g)) (Fl4Spec.dataToCptr y0.bv)
        (Fl4Spec.dataToNat y1.bv)).run σ = ({(.ok dsl, σ)}, False) → OtherTriv (L := L) lbl s σ dsl)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_other_refines arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd lbl slbl hlbl hl length buf
      ct hct args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hFI hact hcur htcb hT)
      fun res h => cn_other_topX arI hX hC hcur h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

end

end

end Fl4Proofs.P3
