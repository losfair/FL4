/-
P3 (DESIGN.md §9), CSpace: **the untyped caps' facts after emptying a slot,
from liveness** (`DelUtFact`, the fact `JAtZ.emptyJR`/`emptyJRT` take for the
untyped parent left childless).

When the emptied slot `sl` held the only child of an untyped cap `u`, `u` is
childless after, and `UtCapP3`'s childless clauses (`ns`, `rst`) start to
apply to it. They follow (`JAtZ.delUtFact_of`) from:
* `SlotLiveAt`: every other slot holding a cap or an original bit lies in an
  object covered by a cap other than `sl`'s, or in the kernel-state block
  (l4v `if_unsafe_then_cap`: a slot in use has a cap to its container; and
  `cap_removeable`: a zombie is removed only once its slots are empty, so the
  removed cap is not the only cover of a slot in use);
* core 0's debug-list head, when not null and not the idle thread, covered
  by a cap other than `sl`'s (FL4's debug list holds the TCBs not finalised;
  the analogue of l4v `if_live_then_nonz_cap`, which exempts the idle
  thread); the idle head lies outside every RAM untyped region
  (`JCovD.idleOut`);
(`UtCapP3.rst` no longer asks that no CNode of the typed heap lie in the
region, which no invariant gives since `th` keeps a CNode after its last cap
goes: the reset derives its destination CNode off the region from that
CNode's cap, `RetCtx.cnode`, `cnode_off_childless`.)
The cover is moved to the state after (the covering cap is not `sl`'s) and
`ut_free` keeps the covered range off the childless region.

* `emptySlot_cdt_orig`: the spec's `empty_slot` of a slot holding a cap sets
  the CDT and the original bits as `emptySlotCdtState`.
-/
import Fl4Proofs.P3.XTopJointEmpty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **A slot in use is live, apart from the slot `x`** (module docstring):
its word covered by a cap at a slot other than `x`, or in the kernel-state
block `[kb, kb + 13568)`. -/
def SlotLiveAt (m : U64 → U64) (G : MdbGhost) (kb x y : U64) : Prop :=
  OtherCov m G x y.val (y.val + 1) ∨ (kb.val ≤ y.val ∧ y.val < kb.val + 13568)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The spec's `empty_slot` of a slot holding a cap: the CDT and the
original bits** (`emptySlotCdtState`'s; `setCap` keeps them). -/
theorem emptySlot_cdt_orig {th : TypedHeap} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hR : StateRel th (L.mem s) σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hcn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hes : ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1) :
    σ'.cdt = (emptySlotCdtState σ sl).cdt ∧ σ'.isOriginalCap = (emptySlotCdtState σ sl).isOriginalCap := by
  obtain ⟨c0, ac, hc0, hca, hg⟩ := hR.abs_cap hA
  rw [hca.abs] at hg
  have hcn0 : c0 ≠ .Null := fun h => hcn (by rw [capV_of_capAt hc0, h])
  obtain ⟨p, hp1, hp⟩ := hA
  obtain ⟨o, idx⟩ := sl
  simp only at hp1 hp
  subst hp1
  rcases hp with hp | ⟨ht, i, hi, hidx⟩
  · obtain ⟨cs, hkq, hwf, -⟩ := hR.cnode p _ hp
    have h3 : Fl4Spec.setCap (Z := Unit) .nullCap (p.bv, idx) (emptySlotCdtState σ (p.bv, idx)) =
        ({((), setCnodeSlot (emptySlotCdtState σ (p.bv, idx)) p.bv idx.length cs idx .nullCap)}, False) :=
      setCap_cnode (σ := emptySlotCdtState σ (p.bv, idx)) .nullCap hkq hwf rfl
    have he := emptySlot_eq hg (fun h => hcn0 (absCap_eq_null.1 h)) h3
    rw [he] at hes
    have e2 := mem_singleton_snd hes
    simp only at e2
    subst e2
    exact ⟨rfl, rfl⟩
  · obtain ⟨tcb, hk, -⟩ := hR.tcb p ht
    subst hidx
    have h3 : Fl4Spec.setCap (Z := Unit) .nullCap (p.bv, Fl4Spec.tcbCnodeIndex i)
        (emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) =
        ({((), setTcbSlot (emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) p.bv tcb i .nullCap)}, False) :=
      setCap_tcb (σ := emptySlotCdtState σ (p.bv, Fl4Spec.tcbCnodeIndex i)) .nullCap hk hi
    have he := emptySlot_eq hg (fun h => hcn0 (absCap_eq_null.1 h)) h3
    rw [he] at hes
    have e2 := mem_singleton_snd hes
    simp only at e2
    subst e2
    exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`DelUtFact` from liveness** (module docstring): the untyped cap `u`
whose only child was the emptied slot `sl` (itself childless) is childless
after; the slots in use, the original slots and the debug-list head, covered
by caps other than `sl`'s (or in the kernel block, which the untyped regions
miss, `JCovD.ks`), miss its region (`ut_free`). -/
theorem JAtZ.delUtFact_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl)
    (hDS2 : DState (L := L) Z.th s' σ' G') (hU2 : UtInv (L.mem s') G')
    (hnull : capV (L.mem s') (cslotAddr sl) = .Null)
    (hoth : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y)
    (hw : P1.WritesIn st s s' (InSlot Z.th))
    (hcdt : σ'.cdt = (emptySlotCdtState σ sl).cdt)
    (hor : σ'.isOriginalCap = (emptySlotCdtState σ sl).isOriginalCap)
    {u : Fl4Spec.CslotPtr} {up usb ufi : U64} {udev : Bool} (hu : AbsSlot Z.th u)
    (hcu : capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev))
    (hpar : σ.cdt sl = some u) (honly : ∀ x, σ.cdt x = some u → x = sl) (hleaf : ∀ x, σ.cdt x ≠ some sl)
    (hlive : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl →
      (capV (L.mem s) y ≠ .Null ∨ ∃ x, cslotAddr x = y ∧ σ.isOriginalCap x = true) →
      SlotLiveAt (L.mem s) Z.G (L.ksb s) (cslotAddr sl) y)
    (hdbg : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ L.idleW s →
      OtherCov (L.mem s) Z.G (cslotAddr sl) (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val
        ((L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val + 1)) :
    DelUtFact (L := L) Z.th s' σ' up usb ufi udev := by
  obtain ⟨hP, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  obtain ⟨⟨-, -, hM2, hC2, hI2⟩, -, -⟩ := hDS2
  have hune : u ≠ sl := fun e => by subst e; exact hleaf u hpar
  have hne : cslotAddr u ≠ cslotAddr sl := fun e => hune (cslotAddr_inj hP hu hA e)
  have hcv : capV (L.mem s) (cslotAddr u) = .Untyped up usb ufi udev := capV_of_capAt hcu
  have hcv2 : capV (L.mem s') (cslotAddr u) = .Untyped up usb ufi udev := by
    rw [hoth _ hu.isSlot hne]; exact hcv
  have hum2 : cslotAddr u ∈ G'.chains.flatten :=
    (hM2.members _).2 ⟨hu.isSlot, _, capAt_capV _ _, by rw [hcv2]; nofun⟩
  have hum : cslotAddr u ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hu.isSlot, _, hcu, fun h => by cases h⟩
  have hnc : ¬ ∃ x, σ'.cdt x = some u := by
    rintro ⟨x, hx⟩
    rw [hcdt] at hx
    simp only [emptySlotCdtState] at hx
    by_cases hxs : x = sl
    · subst hxs; simp at hx
    · rw [Function.update_of_ne hxs] at hx
      by_cases h1 : σ.cdt x = some sl
      · exact hleaf x h1
      · rw [if_neg h1] at hx; exact hxs (honly x hx)
  have hnd := nodesc_of_cdt hP hC2 hu hnc
  have ocov : ∀ lo hi, OtherCov (L.mem s) Z.G (cslotAddr sl) lo hi → Covered (L.mem s') G' lo hi := by
    rintro lo hi ⟨y, hy, hyx, hp, hut, hb, ht⟩
    obtain ⟨hys, -⟩ := (hM.members y).1 hy
    have e := hoth y hys hyx
    have hy' : y ∈ G'.chains.flatten := (hM2.members y).2 ⟨hys, _, capAt_capV _ _, by
      rw [e]; intro h; rw [h, physF_null] at hp; cases hp⟩
    exact ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hut, by rw [e]; exact hb, by rw [e]; exact ht⟩
  intro hd
  have hkb := (J.jcov.ks _ hum _ _ _ (by rw [hcv, hd])).1
  have out : ∀ y : U64, SlotLiveAt (L.mem s) Z.G (L.ksb s) (cslotAddr sl) y →
      y.val < up.val ∨ up.val + 2 ^ usb.val ≤ y.val := by
    rintro y (h | ⟨h1, h2⟩)
    · have := ut_free hU2 hI2 hum2 hcv2 hnd (Nat.lt_succ_self _) (ocov _ _ h)
      omega
    · omega
  have U := J.utc u up usb ufi udev hu hcu hd
  have hks : L.ksb s' = L.ksb s := hw.1
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  refine ⟨fun y hy hn => ?_, fun _ => ⟨fun x hx => ?_, ?_⟩⟩
  · have hyx : y ≠ cslotAddr sl := fun e => hn (by rw [e]; exact hnull)
    exact out y (hlive y hy hyx (Or.inl (by rw [← hoth y hy hyx]; exact hn)))
  · rw [hor] at hx
    simp only [emptySlotCdtState] at hx
    have hxs : x ≠ sl := fun e => by subst e; simp at hx
    rw [Function.update_of_ne hxs] at hx
    have hxa : AbsSlot Z.th x := J.kern.orig x hx
    exact AbsSlot.restrict hP U.nostr hxa
      (out _ (hlive _ hxa.isSlot (fun e => hxs (cslotAddr_inj hP hxa hA e)) (Or.inr ⟨x, rfl, hx⟩)))
  · rw [P1.nodeAt_of_ksb hks, hDbg]
    by_cases hz : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64
    · rw [hz]
      rintro ⟨h1, -⟩
      have hh := U.high (by unfold NotDev; rw [hcv, hd]; simp)
      have h0' : (0#u64 : U64).val = 0 := rfl
      have e64 : (2 : Nat) ^ 64 - 2 ^ 47 = 18446603336221196288 := by norm_num
      rw [h0'] at h1
      rw [e64] at hh
      omega
    · by_cases hi : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.idleW s
      · -- the idle head: outside every RAM untyped region (`JCovD.idleOut`)
        have := (J.jcov.idleOut _ hum _ _ _ (by rw [hcv, hd]) _ (Or.inl hi)).1
        omega
      · have := out _ (Or.inl (hdbg hz hi))
        omega

end

end

end Fl4Proofs.P3
