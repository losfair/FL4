/-
P3 (losfair/FL4#34), untyped: **the drop step of a device untyped cap's
reset at `J`** (handoff/devretype.md "dj4 line" item 1, "dj5 line"). At a
`JAtZ` state with a childless device untyped cap `Untyped p sb fi true` over
`[p, p + 2^sb)`, the spec's `delete_objects` of the region goes, at the same
FL4 state (FL4's device reset writes only the cap), to `JAtZ` at the dropped
sets, the restricted typed heap and P1's heap without the region's objects:
UtDropJ2's `JAtZ.dropA` with the source's RAM facts (`JAtZ.utc`, `SpecFree`,
`JCovD.ks`) replaced by the device ones:

* `DevGpm` [J] (l4v `valid_global_refs`: no untyped range covers a global
  kernel object): the spec's global PML4 lies off every device untyped's
  range. The global PML4 is a static of the kernel image (fl4-kernel
  paging.rs), and the boot check e408a625 skips device memory over the
  kernel image; `x64GlobalPml4` never changes and a device child is a
  sub-range. It names the spec state, so it is not a clause of `DevApart`
  (which is over FL4's state only).
* the region's `H` objects are dead: DevApart's `H` clause makes every `H`
  object meeting a device range a device frame (`.other`), trivially
  `DeadP`;
* the spec objects off the region miss it (`SpecOffR`) from `DevFreeT`;
* the typed heap has no object in the region (DevApart's `RegionFree`), so
  `NoStraddle`, the MDB's slots, the original caps' slots and the debug
  list head (`0 < p`, DevApart's `CanonR`) are off it;
* the kernel-state block apartness from DevApart.

* `JAtZ.dropAD`: the result (`JAtZ.dropA` for a device cap).
-/
import Fl4Proofs.P3.UtDevUt
import Fl4Proofs.P3.UtResetTopJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **[J] The global PML4 off every device untyped range** (module
docstring; l4v `valid_global_refs`). -/
def DevGpm (mem : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV mem x = .Untyped p sb fi true →
    ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val)

theorem deadP_otherD {q : U64} {z : Nat} (h : H q = some (.other z)) : DeadP (L := L) H s q :=
  ⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e),
    fun e => (by rw [h] at e; cases e), fun z e => (by rw [h] at e; cases e)⟩

set_option maxHeartbeats 4000000 in
/-- **`JAtZ` across the drop of a device untyped cap's region** (module
docstring; UtDropJ2's `JAtZ.dropA` for a device cap, with `DevApart`,
`DevFreeT` and `DevGpm` [J] for the source's facts). -/
theorem JAtZ.dropAD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread) {sl : Fl4Spec.CslotPtr} (hsl : AbsSlot Z.th sl)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi true))
    (hnc : ¬ ∃ y, σ.cdt y = some sl)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ) (hGP : DevGpm (L.mem s) Z.G σ)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s)
    (hAF : ArchFitHyp H σ)
    {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ')
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hrepr : σ'.reprogramTimer = σ.reprogramTimer) (hcdom : σ'.curDomain = σ.curDomain)
    (hdtime : σ'.domainTime = σ.domainTime) (hist : σ'.interruptStates = σ.interruptStates)
    (hinode : σ'.interruptIrqNode = σ.interruptIrqNode) (harch : σ'.archState = σ.archState)
    (hdl : σ'.domainList = σ.domainList) (hdsi : σ'.domainStartIndex = σ.domainStartIndex)
    (hum : ∀ x, ¬ RgOf p sb x → σ'.machineState.underlyingMemory x = σ.machineState.underlyingMemory x)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1)
    (hXc : ∀ y, IsSlot Z.th y → ∀ k q, Vs.VNeed (capV (L.mem s) y) k q → q ∈ Vs.lvlSet XP X4 X3 X2 X1 k) :
    JAtZ (L := L) arI AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs Ac Lst D s a σ' := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hPl, ⟨-, -, hML, hC, -⟩, -⟩ := J.xtop.rel
  have hx : cslotAddr sl ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hsl.isSlot, _, hcap, by simp⟩
  have hcx : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi true := capV_of_capAt hcap
  obtain ⟨hpal, hreg, -, -, -, hrf, hHo, hcan, -⟩ := hDA _ hx p sb fi hcx
  have hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := fit_of_al (show p.val < 2 ^ 64 from p.bv.isLt) hsb hpal
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl) := fun y =>
    Mdb.not_desc_of_no_child fun z hz => hnc ((hC.has_child_iff hPl hsl).2 ⟨z, hz⟩)
  -- the region's `H` objects: device frames, dead
  have hRD : ∀ q, P1.RegionD H p.val (p.val + 2 ^ sb.val) q → DeadP (L := L) H s q := by
    intro q hq
    cases e : H q with
    | none => exact DeadP.none e
    | some k =>
      unfold P1.RegionD P1.MeetsR at hq
      rw [e] at hq
      simp only [Option.elim] at hq
      rcases hHo q k e with h | h | ⟨-, -, z, rfl⟩
      · omega
      · omega
      · exact deadP_otherD e
  have hK := J.sKeep hsb hfit hRD hres hKR
  -- the typed heap off the region
  have hN : NoStraddle Z.th p.val (p.val + 2 ^ sb.val) := fun q k hq =>
    (hrf q k hq).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hns : ∀ y ∈ Z.G.chains.flatten, y.val < p.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hPl ((hML.members y).1 hy).1
    rcases hrf q kq hq with e | e <;> omega
  have hout : ∀ q k, Z.th q = some k → 0 < objSize k → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) := by
    intro q k hq hk hin
    rcases hrf q k hq with h | h <;> omega
  have hrst : ∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) sl := by
    intro sl' h
    obtain ⟨q, h1, h2⟩ := J.kern.orig sl' h
    refine ⟨q, h1, ?_⟩
    rcases h2 with h2 | ⟨h2, h3⟩
    · rw [restrictTh_out (hout q _ h2 (by simp only [objSize]; positivity))]; exact Or.inl h2
    · rw [restrictTh_out (hout q _ h2 (by simp only [objSize]; omega))]; exact Or.inr ⟨h2, h3⟩
  have hhd : ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val) := by
    rcases J.kern.head with h | ⟨h1, -⟩
    · rw [h]
      have hp0 := hcan.1
      rintro ⟨g1, -⟩
      have h0 : (0#u64 : U64).val = 0 := rfl
      rw [h0] at g1
      omega
    · exact hout _ _ h1 (by simp only [objSize]; omega)
  -- the spec objects off the region miss it (`DevFreeT`)
  have hSO : SpecOffR σ p sb := by
    intro o ko hk ho
    have := hDF _ hx p sb fi true hcx ⟨rfl, trivial⟩ o ko hk
    rcases this with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
      have hfi : fi.val ≤ 2 ^ sb.val := J.ut.fib _ hx p sb fi true hcx
      exact off_val hsb hfit (q := ⟨o⟩) ho ⟨h1, by show o.toNat < _; omega⟩
  obtain ⟨hcur, hcsc⟩ := J.curLive hsb hfit hres hRD
  obtain ⟨hks, hthT, hthk, hip, hrp, hap, hnk, hnB, hcov, hobj, hzH, hsf, hhs, hscC, hiL⟩ :=
    J.dropPlace hsb hfit hSO hreg hAF hN hD
  obtain ⟨hnsc, hinv, hcu, hown, hoff, hact, hc0, hbsa, hsv, hiso, hsl', hcr⟩ := J.dropSpecInv hK hD
  obtain ⟨hcall, hrf', hrr, hyl, hmcp, hbuf⟩ := J.dropMixed hsb hfit hRD hK hD
  obtain ⟨hdel, hfin, hbd⟩ := J.dropDel hsb hfit hx hcx hnd hN hns
  have hX : XTopAt (L := L) AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      s a σ' :=
    XTopAt.drop J.xtop (J.xKeep hsb hfit hRD hK) hsb hfit hD hK hcdt horig hrepr hcdom hdtime hist
      hinode harch hdl hdsi hum J.ut hx hcx hnd hN hns hXP hX4 hX3 hX2 hX1 hM
  have hjpl := J.dropJpl hsb hfit hx hcx hnd hSO hN hD
  have hjc := J.dropCov hsb hfit
  have hkn := J.dropKern hsb hfit hD horig harch hcur hcsc hrst hhd (hGP _ hx p sb fi hcx)
  have hutc := J.dropUtc hsb hfit hcdt horig harch hrst
  have hblk := J.dropBlk hres hRD hreg hKR hDT
  have hvc : Vs.VsSlotsW (restrictTh Z.th p.val (p.val + 2 ^ sb.val))
      (Vs.prP p.val (p.val + 2 ^ sb.val) (L.mem s) Z.P Z.L4 Z.L3 Z.L2 Z.L1)
      (Vs.pr4 p.val (p.val + 2 ^ sb.val) (L.mem s) Z.L4 Z.L3 Z.L2 Z.L1)
      (Vs.pr3 p.val (p.val + 2 ^ sb.val) (L.mem s) Z.L3 Z.L2 Z.L1)
      (Vs.pr2 p.val (p.val + 2 ^ sb.val) (L.mem s) Z.L2 Z.L1) (Vs.pr1 p.val (p.val + 2 ^ sb.val) Z.L1) (L.mem s) := by
    obtain ⟨-, hR, hPt, hPI, -⟩ := J.xtop.fin
    exact J.vsc.drop hR hPt hPI hXP hX4 hX3 hX2 hX1 hM hXc
  -- the buffer fields (`JAtZ.dropBuf`): spec objects in the region inside it (`DevFreeT`)
  have hIn : ∀ o ko, σ.kheap o = some ko → RgOf p sb o →
      p.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val + 2 ^ sb.val := by
    intro o ko hk hr
    have hr' := (rgOf_iff hsb hfit ⟨o⟩).1 hr
    have hv : (⟨o⟩ : U64).val = o.toNat := rfl
    rw [hv] at hr'
    have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
    have hfi : fi.val ≤ 2 ^ sb.val := J.ut.fib _ hx p sb fi true hcx
    rcases hDF _ hx p sb fi true hcx ⟨rfl, trivial⟩ o ko hk with (h | h) | ⟨h1, h2⟩
    · omega
    · omega
    · exact ⟨h1, by omega⟩
  have hp8 : p.val % 8 = 0 := by
    have h4 : 4 ≤ sb.val := (hDA _ hx p sb fi hcx).2.2.2.2.2.2.2.2
    have h1 : 8 ∣ 2 ^ sb.val := by
      have := Nat.pow_dvd_pow 2 (show 3 ≤ sb.val by omega)
      simpa using this
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 (Nat.dvd_of_mod_eq_zero hpal))
  have hbf := J.dropBuf hsb hfit hx hcx hSO hIn hnd hp8 hD
  -- `LiveDN` after (KENTRY-PLAN g2j): the same memory and ghost tree, the typed
  -- heap and `H` restricted; the debug lists' members kept (P1's `DbgTz` after)
  have hLvD : LiveDN (L := L) (restrictTh Z.th p.val (p.val + 2 ^ sb.val))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs Z.G s σ' := by
    obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := J.live
    have hIU : ∀ y, InUse (L.mem s) σ' y → InUse (L.mem s) σ y := fun y hu => by
      unfold InUse at hu ⊢; rw [horig] at hu; exact hu
    refine ⟨⟨fun q i hqi hu => hL.slots q i hqi.of_restrict (hIU _ hu),
      fun n hn hni => hL.dbg n hn (by rw [← hD.idle]; exact hni),
      fun y hy p' zt n hz i hpi hni hu => hL.zslots y (IsSlot.of_restrict hy) p' zt n hz i hpi.of_restrict hni
        (hIU _ hu),
      fun y hy p' zt n hz hzt => DeadP.drop (hL.zdead y (IsSlot.of_restrict hy) p' zt n hz hzt)⟩,
      ⟨lst, hDW.restrictT (fun y hy => (P1.Heap.mem_tcbs_drop.1 hy).1) hblk.2.2.1.2.2.tm.dn hblk.2.2.1.2.2.tm.dh⟩,
      fun sl hA h => by rw [horig]; exact hN sl hA.of_restrict h⟩
  exact ⟨hX, hcall, hrf', hrr, hyl, hmcp, hbuf, hks, hthT, hthk, hip, hrp, hap, hnk, hnB, hjpl, hcov, hobj, hzH, hsf,
    hhs, hscC, hjc, hkn, hdel, J.ut, hbd, hfin, hutc, hnsc, hinv, hcu, hown, hoff, hact, hc0, hbsa, hsv, hiso, hsl',
    hcr, hblk, hiL, hvc, hbf.1, hbf.2.1, hbf.2.2, ⟨fun y hy => J.ext.nat y (IsSlot.of_restrict hy), fun t ht => J.ext.vw t (restrictTh_some ht).1⟩,
    hLvD, fun q hq => J.zD q (by obtain ⟨y, hy, zt, n, hz, h65⟩ := hq; exact ⟨y, IsSlot.of_restrict hy, zt, n, hz, h65⟩)⟩

end

/-! ## The spec's reset of a used device cap -/

section DevSpec
open Fl4Spec

/-- **The spec's reset of a used device untyped cap** (`reset_untyped_cap`,
`dev`: `delete_objects`, no memory cleared, the free index 0; UtResetSpecJ's
`reset_smallX` for a device cap): the outcome from `delete_objects`'. -/
theorem reset_devX {σ : State Unit} {pu pb : ObjRef} {sz r fi : Nat} {idx : List Bool} {cs : CnodeContents}
    (hk : σ.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    (hg : getCap (Z := Unit) (pb, idx) σ = ({(.untypedCap true pu sz fi, σ)}, False)) (hfi : fi ≠ 0)
    (hp8 : pu.toNat % 8 = 0) (hpb : pb ∉ regionSet pu sz) (hrcb : resetChunkBits = 16)
    {yD : Unit × State Unit} (hyD : yD ∈ (deleteObjects (Z := Unit) pu sz σ).1)
    {csD : CnodeContents} (hkD : yD.2.kheap pb = some (.cnode r csD)) (hwfD : wellFormedCnodeN r csD) :
    ((.ok (), setCnodeSlot yD.2 pb r csD idx (.untypedCap true pu sz 0)) : Except Unit Unit × State Unit) ∈
      ((resetUntypedCap (Z := Unit) (pb, idx)).run σ).1 := by
  unfold resetUntypedCap
  refine memE_bind (by rw [top_get hk hwf hidx hg hfi hp8 hpb hrcb]; exact Set.mem_singleton _) rfl ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  refine memE_bind (memE_liftE hyD) rfl ?_
  dsimp only
  rw [if_pos (Or.inl trivial)]
  have hsc : (((), setCnodeSlot yD.2 pb r csD idx (.untypedCap true pu sz 0)) :
      Unit × State Unit) ∈ (setCap (Z := Unit) (.untypedCap true pu sz 0) (pb, idx) yD.2).1 := by
    rw [setCap_cnode _ hkD hwfD hidx]; exact Set.mem_singleton _
  have hm : (((), setCnodeSlot yD.2 pb r csD idx (.untypedCap true pu sz 0)) : Unit × State Unit) ∈
      ((NonDet.unless (true = true) (doMachineOp (clearMemory pu (2 ^ sz))) >>= fun _ =>
        setCap (Z := Unit) (.untypedCap true pu sz 0) (pb, idx)) yD.2).1 := by
    refine ⟨((), yD.2), ?_, hsc⟩
    unfold NonDet.unless; rw [if_pos rfl]; exact Set.mem_singleton _
  refine memE_bind (memE_liftE hm) rfl ?_
  exact memE_liftE (m := archPostResetUntyped (Z := Unit) true sz) (x := ((), _)) (Set.mem_singleton _)

end DevSpec

end

end Fl4Proofs.P3
