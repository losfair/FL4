/-
P3 (DESIGN.md §9), untyped: **the reset's free-index writes at `J`**
(handoff utj.md Round 12, item 3b).

After the drop step (UtDropJ2's `JAtZ.drop`) the source cap's region holds no
object of the typed heap (`RegionFree`) and no spec object meets it
(`RgMiss`); its MDB slots lie off it (`UtCapP3.ns`). FL4's
`slot.set_cap(Untyped p sb o)` lowering the free index to `o` (the region
zero above `o`) is then a slot step at `J` against the spec's
`set_cap (UntypedCap False p sb o)`: the CSpace relations by
UntypedResetRefine's `reset_set_step`, the MDB by `MdbStep.setFi` (no
descendants), the slot's shape kept (`shape` forgets the free index: the
cover, `TypedKept`, `DelInv`, `JPlaced`), the untyped caps' facts at the new
index from the cap's own (`RegionFree`, `ZeroRegion` above `o`, its MDB
slots off the region) and the others' unchanged (the written slot lies in an
object, off every free part).

* `RgMiss`: no spec object meets the region; kept by `setCnodeSlot` of a
  CNode slot and by the preemption point (UtResetSpecJ's `pp_ksm'`).
* `JAtZ.setFiJ`: `JAtZ` across the write, at the same sets.
-/
import Fl4Proofs.P3.UtResetZ
import Fl4Proofs.P3.UtResetSpecJ
import Fl4Proofs.P3.XTopJointGrant
import Fl4Proofs.P3.XTopJointVsMap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- No spec object meets the region `[p, p + 2 ^ sb)`. -/
def RgMiss (p sb : U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat

theorem RgMiss.setCn {p sb : U64} {σ : Fl4Spec.State Unit} (h : RgMiss p sb σ) {pb : Fl4Spec.ObjRef} {r : Nat}
    {cs : Fl4Spec.CnodeContents} (hk : σ.kheap pb = some (.cnode r cs)) (idx : List Bool) (c : Fl4Spec.Cap) :
    RgMiss p sb (setCnodeSlot σ pb r cs idx c) := by
  intro o ko ho
  simp only [setCnodeSlot] at ho
  by_cases e : o = pb
  · subst e
    rw [Function.update_self] at ho
    cases ho
    have := h o _ hk
    simpa [Fl4Spec.objBits] using this
  · rw [Function.update_of_ne e] at ho
    exact h o ko ho

theorem RgMiss.of_kheap {p sb : U64} {σ σ' : Fl4Spec.State Unit} (h : RgMiss p sb σ) (hk : σ'.kheap = σ.kheap) :
    RgMiss p sb σ' := fun o ko ho => h o ko (hk ▸ ho)

/-- `KSz` across a CNode slot write. -/
theorem ksz_setCn {σ : Fl4Spec.State Unit} {pb : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    (hk : σ.kheap pb = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs) {idx : List Bool}
    (hidx : idx.length = r) (c : Fl4Spec.Cap) :
    KSz σ (setCnodeSlot σ pb r cs idx c) := by
  intro o ko' ho
  simp only [setCnodeSlot] at ho
  by_cases e : o = pb
  · subst e
    rw [Function.update_self] at ho
    cases ho
    exact ⟨_, hk, by simp [Fl4Spec.aType, hwf, wf_update _ hwf hidx]⟩
  · rw [Function.update_of_ne e] at ho
    exact ⟨ko', ho, rfl⟩

/-- A restricted typed heap is its own restriction. -/
theorem restrictTh_idem (th : TypedHeap) (lo hi : Nat) :
    restrictTh (restrictTh th lo hi) lo hi = restrictTh th lo hi := by
  funext q
  unfold restrictTh
  split_ifs <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

theorem set_cap_cpu (sl : obj.Slot) (s : S) (c : capability.Cap) :
    obj.Slot.set_cap st sl s c ⦃ s' => L.cpu s' = L.cpu s ⦄ :=
  WP.spec_mono (set_cap_spec (L := L) sl s c) (by rintro _ rfl; simp)

set_option maxHeartbeats 16000000 in
/-- **The source cap's free index lowered at `J`** (module docstring): the
cap at a CNode slot `(pp, idx)` is `Untyped p sb f false` with `f ≠ 0`, no
CDT child, the region free in the typed heap and of spec objects, the
memory zero above the new index `f' ≤ 2 ^ sb`. -/
theorem JAtZ.setFiJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb f : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb f false))
    (hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx)) (hf0 : f.val ≠ 0)
    (hTh : restrictTh Z.th p.val (p.val + 2 ^ sb.val) = Z.th)
    (hfr : RegionFree Z.th p.val (p.val + 2 ^ sb.val)) (hRM : RgMiss p sb σ)
    (f' : U64) (hf' : f'.val ≤ 2 ^ sb.val) (hZ : ZeroRegion (L.mem s) (p.val + f'.val) (p.val + 2 ^ sb.val)) :
    obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s (.Untyped p sb f' false) ⦃ s' =>
      ∃ cs, σ.kheap pp.bv = some (.cnode rs cs) ∧ Fl4Spec.wellFormedCnodeN rs cs ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a
          (setCnodeSlot σ pp.bv rs cs idx (.untypedCap false p.bv sb.val f'.val)) ∧
        capAt (L.mem s') (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb f' false) ∧
        L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
        (∀ w : U64, P1.Aligned w → w.val ≠ (cslotAddr (pp.bv, idx)).val →
          w.val ≠ (cslotAddr (pp.bv, idx)).val + 8 → L.mem s' w = L.mem s w) ⦄ := by
  set x := cslotAddr (pp.bv, idx) with hxdef
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI, -, hMO, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot Z.th x := hAs.isSlot
  have hcx : capV (L.mem s) x = .Untyped p sb f false := capV_of_capAt hcap
  have hxm : x ∈ Z.G.chains.flatten := (hM.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x := fun y =>
    Mdb.not_desc_of_no_child fun z hz => hnc ((hC.has_child_iff hP hAs).2 ⟨z, hz⟩)
  have U := J.utc _ p sb f false hAs hcap rfl
  have hND : NotDev (L.mem s) x p sb f := by unfold NotDev; rw [hcx]; simp
  have heq : restrictTh Z.th p.val (p.val + 2 ^ sb.val) = Z.th := hTh
  have hRR : ResetRel (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) Z.G x p sb false (L.mem s) σ f := by
    rw [heq]; exact ⟨hSR, hV, hM, hC, hI, J.ut, hcx⟩
  have key := reset_set_step (L := L) (th := Z.th) hP (pp := pp) (by rw [heq]; exact hpp) hidx hRR hnd f' hf'
  rw [heq] at key
  obtain ⟨s', hs', cs, hk, hwf, hRR', hfr2, hco, hlk⟩ := spec_exists key
  rw [← hxdef] at hs' hRR' hfr2 hco
  obtain ⟨s2, hs2, hks⟩ := spec_exists (set_cap_ksb (L := L) x s (.Untyped p sb f' false))
  obtain ⟨s3, hs3, hcpu⟩ := spec_exists (set_cap_cpu (L := L) x s (.Untyped p sb f' false))
  rw [hs'] at hs2 hs3; cases eq_of_ok_eq hs2; cases eq_of_ok_eq hs3
  rw [hs', WP.spec_ok]
  set σ' := setCnodeSlot σ pp.bv rs cs idx (.untypedCap false p.bv sb.val f'.val) with hσ'
  refine ⟨cs, hk, hwf, ?_, by rw [capAt_capV, hRR'.cap], hks, hcpu, hfr2⟩
  -- FL4's writes: the slot's two words
  have hx8 := hxs.align hP
  have hxf := hxs.fit hP
  have hw : P1.WritesIn st s s' (InSlot Z.th) :=
    ⟨hks, hcpu, fun b hb hn => hfr2 b hb (fun e => hn ⟨x, hxs, by omega, by omega⟩)
      (fun e => hn ⟨x, hxs, by omega, by omega⟩)⟩
  have hcap' : capV (L.mem s') x = .Untyped p sb f' false := hRR'.cap
  have hshape : ∀ y, IsSlot Z.th y → shape (capV (L.mem s') y) = shape (capV (L.mem s) y) := by
    intro y hy
    by_cases e : y = x
    · subst e; rw [hcap', hcx]; rfl
    · rw [hco y hy e]
  -- the spec's step
  have hmem : ((), σ') ∈ (Fl4Spec.setCap (Z := Unit) (.untypedCap false p.bv sb.val f'.val) (pp.bv, idx) σ).1 := by
    rw [setCap_cnode _ hk hwf hidx]; exact Set.mem_singleton _
  have hcn : CnK σ σ' := nkn_setCap _ _ σ _ hmem
  have hkc : KeepC σ σ' := keepC_of hcn
    (nko_setCap (Ps := {pp.bv}) (.untypedCap false p.bv sb.val f'.val) (pp.bv, idx) (Set.mem_singleton _) σ _ hmem)
    (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact ⟨rs, cs, hk⟩)
  have hkz : KSz σ σ' := ksz_setCn hk hwf hidx _
  have hC' := CnStep.of_cnK hcn
  -- the MDB
  have hrev : ∀ z ∈ Z.G.chains.flatten, revOf (L.mem s') z = revOf (L.mem s) z := by
    intro z hz
    obtain ⟨sl, hA, rfl⟩ := isSlot_abs' ((hM.members _).1 hz).1
    rw [← hRR'.C.orig sl hA, ← hC.orig sl hA]
    rfl
  have hMS : MdbStep (L.mem s) Z.G (L.mem s') Z.G :=
    MdbStep.setFi hM hI hxm hcx hcap' hf' (Or.inr hnd) (fun z hz hzx => hco z ((hM.members z).1 hz).1 hzx) hrev
  have hMO' : MdbOKV (L.ksb s) (L.mem s') Z.G := hMS.okv hMO
  have hFI' : FinInv Z.th (L.mem s') σ' Z.G := by
    refine ⟨fun o => ⟨fun r cs1 h1 hw1 => ?_, fun t h1 => ?_⟩,
      hFI.fm.recap hM.tree.nodup x (CapSim.of_shape (by rw [hcap', hcx]; rfl) (by rw [hcap', hcx]; rfl))
        (fun z hz hzx => hco z ((hM.members z).1 hz).1 hzx)⟩
    · simp only [hσ', setCnodeSlot] at h1
      by_cases e : o = pp.bv
      · subst e
        rw [Function.update_self] at h1
        cases h1
        exact (hFI.kt _).1 rs cs hk hwf
      · rw [Function.update_of_ne e] at h1
        exact (hFI.kt o).1 r cs1 h1 hw1
    · simp only [hσ', setCnodeSlot] at h1
      by_cases e : o = pp.bv
      · subst e; rw [Function.update_self] at h1; cases h1
      · rw [Function.update_of_ne e] at h1
        exact (hFI.kt o).2 t h1
  have hTS : ∀ t, Z.th t = some .tcb → ∀ i, i < tcbSlots →
      capAt (L.mem s') (slotOf t i) = capAt (L.mem s) (slotOf t i) := by
    intro t ht i hi
    have hne : slotOf t i ≠ x := slotOf_ne_cn hP (Or.inr ⟨ht, hi⟩) ht hpp hidx
    rw [capAt_capV, capAt_capV, hco _ ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩ hne]
  have hX' : XTopAt (L := L) AR { Z with G := Z.G } s' a σ' :=
    J.xtop.slotStep ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hP hb h)⟩ hcn hkc
      ⟨hRR'.R, hRR'.V, hRR'.M, hRR'.C, hRR'.I⟩ hFI' hMO' (fun t ht => hTS t ht 1 (by decide))
  -- the CSpace fields
  have hSF : SpecFree (L.mem s') Z.G σ' := by
    intro x' hx' p2 sb2 fi2 hc2 o ko' ho
    by_cases e : x' = x
    · subst e
      rw [hcap'] at hc2
      cases hc2
      exact Or.inl ((hRM.setCn hk idx _) o ko' ho)
    · rw [hco x' ((hM.members x').1 hx').1 e] at hc2
      obtain ⟨ko, hko, hty⟩ := hkz o ko' ho
      rw [← objBits_of_aType hty]
      exact J.sfree x' hx' p2 sb2 fi2 hc2 o ko hko
  have hJC : JCs (L := L) { Z with G := Z.G } s' σ' :=
    ⟨DelInv.ofShape J.del hshape hlk, hRR'.U, fun G hG => FinM.of_links hP hRR'.M hG hFI'.fm, hSF⟩
  -- the rest (as XTopJointRest's `jowes_slotOf`)
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlot_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC'.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (hC'.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq, rfl, rfl⟩,
    fun p x n hp => ⟨x, hC'.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC'.tcbF hp; ⟨y, hy, hc.yld⟩,
    fun p x n hp => ⟨x, hC'.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, hC'.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC'.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR2 := J.rrecv.frame k4 hC'.toHStep.khrb
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hP hb h)⟩
    exact (P1.blk_of_capw J.blk hw' (J.slotCapW P1.tlow_slots)).1
  have hTK : TypedKept Z.th (L.mem s) (L.mem s') := fun y hy => Or.inr ⟨y, hy, hshape y hy⟩
  have hidl := J.idleW_keep hX'.fin.1.1.1 hC'.idle hC'.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    let ⟨Tr, Cq, hJ⟩ := J.jpl
    ⟨Tr, Cq, hJ.slot hkc hw.1 J.intL hTK (fun t ht => hTS t ht 3 (by decide)) (fun t ht => hTS t ht 2 (by decide)) hidl.2⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep hX' hC'.toHStep k3 (fun q z hq K h8 hK => J.inSlot_scKeep hw hq h8 hK) (J.act.cn hC').1
      (J.yld.frame k2 yk) yk (J.jcov.dead q hq)
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := coverKept_ofShape hshape
  have hUF : UtFrom Z.G Z.G (L.mem s) (L.mem s') := by
    intro z hz p2 sb2 fi2 d hc2
    by_cases e : z = x
    · subst e; rw [hcap'] at hc2; cases hc2; exact ⟨_, hxm, f, hcx⟩
    · exact ⟨z, hz, fi2, by rw [← hco z ((hM.members z).1 hz).1 e]; exact hc2⟩
  have hjc : JCovD (L := L) Z.th H Z.G D Cs s' :=
    ⟨fun q k hq => (J.jcov.th q k hq).imp (fun hc => covered_keepC hM hRR'.M hc hCK)
        (Or.imp_right (exAt_of hidl hks).2),
      fun q k hq => (J.jcov.h q k hq).imp (fun hc => covered_keepC hM hRR'.M hc hCK)
        (Or.imp_right (exAt_of hidl hks).2),
      hdead, J.jcov.ks.keep hks hUF, J.jcov.idleOut.keep hidl hUF⟩
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := rfl
  have hkern := J.kern_keep hks hcpu hX'.fin.1.1.1 hC'.ct hC'.csc (fun sl h => Or.inl h) hgp
    (fun p ao h => (hC'.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 h) hDbg (D' := D)
  -- the untyped caps' facts
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hP hy
    rcases hfr q kq hq with e | e <;> omega
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      dev = false → UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
    intro sl p2 sb2 fi2 dev hsl hc2 hdv
    subst hdv
    by_cases e : cslotAddr sl = x
    · have hsl' : sl = (pp.bv, idx) := cslotAddr_inj hP hsl hAs e
      subst hsl'
      rw [capAt_capV, hcap'] at hc2
      cases eq_of_ok_eq hc2
      refine ⟨U.pal, U.pfit, hf', fun _ => U.high hND, fun _ => by rw [hcpu, hna]; exact U.actZ hND,
        fun q k hq => by rcases hfr q k hq with h | h <;> omega, fun _ w hal h1 h2 => ?_, U.sb4, U.nostr,
        fun y hy => by have := U.ns hnc y hy; omega, fun _ => U.ns hnc,
        fun _ _ hf0' => ?_, fun _ => by rw [hna]; exact U.dwReg hND,
        fun _ => U.gReg hND⟩
      · rw [hfr2 w hal (by have := hobj x hxs; omega) (by have := hobj x hxs; omega)]
        exact hZ w hal h1 h2
      · obtain ⟨r1, r3⟩ := U.rst hND hnc hf0
        exact ⟨r1, by rw [hna, hDbg]; exact r3⟩
    · have hc0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p2 sb2 fi2 false) := by
        rw [capAt_capV, ← hco _ hsl.isSlot e, ← capAt_capV]; exact hc2
      have U2 := J.utc sl p2 sb2 fi2 false hsl hc0 rfl
      have hcv2 : capV (L.mem s') (cslotAddr sl) = capV (L.mem s) (cslotAddr sl) := hco _ hsl.isSlot e
      have B : NotDev (L.mem s') (cslotAddr sl) p2 sb2 fi2 → NotDev (L.mem s) (cslotAddr sl) p2 sb2 fi2 := by
        unfold NotDev; rw [hcv2]; exact id
      have hobj2 : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p2.val + fi2.val ∨ p2.val + 2 ^ sb2.val ≤ y.val := by
        intro y hy
        obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hP hy
        rcases U2.free q kq hq with e | e <;> omega
      refine ⟨U2.pal, U2.pfit, U2.fiLe, fun g => U2.high (B g), fun g => by rw [hcpu, hna]; exact U2.actZ (B g),
        U2.free, fun g w hal h1 h2 => ?_, U2.sb4, U2.nostr, U2.nsFree, fun h0 => U2.ns h0,
        fun g h0 hf0' => ?_,
        fun g => by rw [hna]; exact U2.dwReg (B g), fun g => U2.gReg (B g)⟩
      · rw [hfr2 w hal (by have := hobj2 x hxs; omega) (by have := hobj2 x hxs; omega)]
        exact U2.zero (B g) w hal h1 h2
      · obtain ⟨r1, r3⟩ := U2.rst (B g) h0 hf0'
        exact ⟨r1, by rw [hna, hDbg]; exact r3⟩
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR2, J.yld.frame k2 yk, J.mcp.frame k1 mk,
      J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := hC'.tcbF hp; ⟨y, hy, hc.buf⟩), hRP',
      J.apart.sc_frame hw.1 (SzKeep.of_keepC hkc), hjpl, hjc, hkern, hutc, J.nsc.cn hC'.toHStep, J.inv.cn hC',
      CurInvW.cn J.cur hC', J.own.cn hC'.toHStep, J.off.cn hC'.toHStep, J.act.cn hC', J.bsa.cn hC'.toHStep,
      J.isorted.cn hC'.toHStep, J.curRun.cn hC'.toHStep (Or.inr hC'.act), hblk⟩
  have hLS := LiveDN.simX J J.live hX' rfl rfl rfl (fun p hp => R.jcov.dead p (J.zD p hp)) hC'.idle
    (dbgKeep_of_writes J.blk hw fun _ hb => J.inSlot_notDbg hb) (fun sl h => h)
    (fun y hy => LSim.of_shape (hshape y hy))
  exact J.cs_frame (G' := Z.G) hks hX' (KBack.of_keepCT (KeepC.t hkc)) (IpcFrKeep.of_keepC hkc) hJC R
    (Vs.VsSlotsT.of_some (· = x) (fun y hy e => hco y hy e) (fun y _ e _ _ _ _ _ _ => by
      rw [e, hcap']; exact Vs.vcapW_ut rfl) (fun y _ e _ _ => by rw [e, hcap']; trivial) (fun y _ e _ => by rw [e, hcap']; trivial)) (J.vkeep_slot hw)
    hLS.1 (fun p hp => J.zD p (hLS.2 p hp))

end

end

end Fl4Proofs.P3
