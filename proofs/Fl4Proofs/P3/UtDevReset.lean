/-
P3 (losfair/FL4#34), untyped: **the retype with the reset of a used device
untyped cap at `J`** (handoff/devretype.md "dj5 line" items 1–5, "dj6 line").
FL4's `reset_untyped` of a device cap (`fi ≠ 0`) writes only the cap, with
free index 0 (P1 `reset_untyped_dev`: no memory clear, no preemption point);
the spec's `reset_untyped_cap` detypes the region (`delete_objects`) and sets
the cap's free index 0 (UtDevDrop's `reset_devX`).

* `JAtZ.setFiJD`: UtResetJ's `JAtZ.setFiJ` for a device cap (no
  `ZeroRegion`, no `RgMiss`: the RAM caps' `UtCapP3`/`SpecFree` say nothing
  of it).
* `devRegion_dead`: every `H` object meeting a childless device cap's range
  is in the dead set `D` (`DevApart`'s `H` clause puts it in the used part,
  `ut_free` keeps covered objects off the range, `DevApart`'s idle and
  kernel-state-block clauses the exempt ones), so `RegionUnrefAt` gives the
  kept references.
* `ResetJPostD`, `JAtZ.reset_untypedDJ`: FL4's `reset_untyped` against
  `reset_untyped_cap`: UtDevDrop's `JAtZ.dropAD` at the spec's
  `delete_objects` (`delSt`), then `JAtZ.setFiJD`; `DevApart`, `DevFreeT`
  and `DevGpm` re-established at the reset's state (the reset cap's range
  holds no `H` and no spec object, the other caps unchanged).
* `JAtZ.utDevResetJ`: the restart, the reset, then UtDevRet's
  `JAtZ.utDevBodyJ` / UtDevUt's `JAtZ.utUtDevBodyJ` at the reset's state
  (UtRetResetJ's `JAtZ.utResetJ` for a device cap).
* `JAtZ.jUtRetHypDev`: `JUtRetHypD … true` with no residual premise
  (UtDevUt's `JUtRetHypDevR` [W] is gone).

Premises: `DevApart`, `DevFreeT`, `DevGpm` [J] (as before),
`resetChunkBits = 16` [P] and `VsReachMiss` [J] at the restart's state (as the
RAM reset, UtRetResetJ), `RegionUnrefJ` [J], `ArchFitHyp`/`BufObjHyp`.
-/
import Fl4Proofs.P3.UtDevDrop
import Fl4Proofs.P3.UtRetResetJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

theorem RegionFree.of_restrictTh {th : TypedHeap} {lo hi lo' hi' : Nat} (h : RegionFree th lo hi) :
    RegionFree (restrictTh th lo' hi') lo hi := fun q kd hq => h q kd (restrictTh_some hq).1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **A device cap's free index lowered at `J`** (UtResetJ's `JAtZ.setFiJ`
for `Untyped p sb f true`): the cap at a CNode slot `(pp, idx)`, no CDT
child, the typed heap its own restriction to the range; no `ZeroRegion` and
no `RgMiss` (the RAM caps' `UtCapP3`/`SpecFree` say nothing of a device
cap). -/
theorem JAtZ.setFiJD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb f : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb f true))
    (hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx))
    (hTh : restrictTh Z.th p.val (p.val + 2 ^ sb.val) = Z.th)
    (f' : U64) (hf' : f'.val ≤ 2 ^ sb.val) :
    obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s (.Untyped p sb f' true) ⦃ s' =>
      ∃ cs, σ.kheap pp.bv = some (.cnode rs cs) ∧ Fl4Spec.wellFormedCnodeN rs cs ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a
          (setCnodeSlot σ pp.bv rs cs idx (.untypedCap true p.bv sb.val f'.val)) ∧
        capAt (L.mem s') (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb f' true) ∧
        L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
        (∀ w : U64, P1.Aligned w → w.val ≠ (cslotAddr (pp.bv, idx)).val →
          w.val ≠ (cslotAddr (pp.bv, idx)).val + 8 → L.mem s' w = L.mem s w) ⦄ := by
  set x := cslotAddr (pp.bv, idx) with hxdef
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, hFI, -, hMO, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot Z.th x := hAs.isSlot
  have hcx : capV (L.mem s) x = .Untyped p sb f true := capV_of_capAt hcap
  have hxm : x ∈ Z.G.chains.flatten := (hM.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x := fun y =>
    Mdb.not_desc_of_no_child fun z hz => hnc ((hC.has_child_iff hP hAs).2 ⟨z, hz⟩)
  have heq : restrictTh Z.th p.val (p.val + 2 ^ sb.val) = Z.th := hTh
  have hRR : ResetRel (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) Z.G x p sb true (L.mem s) σ f := by
    rw [heq]; exact ⟨hSR, hV, hM, hC, hI, J.ut, hcx⟩
  have key := reset_set_step (L := L) (th := Z.th) hP (pp := pp) (by rw [heq]; exact hpp) hidx hRR hnd f' hf'
  rw [heq] at key
  obtain ⟨s', hs', cs, hk, hwf, hRR', hfr2, hco, hlk⟩ := spec_exists key
  rw [← hxdef] at hs' hRR' hfr2 hco
  obtain ⟨s2, hs2, hks⟩ := spec_exists (set_cap_ksb (L := L) x s (.Untyped p sb f' true))
  obtain ⟨s3, hs3, hcpu⟩ := spec_exists (set_cap_cpu (L := L) x s (.Untyped p sb f' true))
  rw [hs'] at hs2 hs3; cases eq_of_ok_eq hs2; cases eq_of_ok_eq hs3
  rw [hs', WP.spec_ok]
  set σ' := setCnodeSlot σ pp.bv rs cs idx (.untypedCap true p.bv sb.val f'.val) with hσ'
  refine ⟨cs, hk, hwf, ?_, by rw [capAt_capV, hRR'.cap], hks, hcpu, hfr2⟩
  -- FL4's writes: the slot's two words
  have hx8 := hxs.align hP
  have hxf := hxs.fit hP
  have hw : P1.WritesIn st s s' (InSlot Z.th) :=
    ⟨hks, hcpu, fun b hb hn => hfr2 b hb (fun e => hn ⟨x, hxs, by omega, by omega⟩)
      (fun e => hn ⟨x, hxs, by omega, by omega⟩)⟩
  have hcap' : capV (L.mem s') x = .Untyped p sb f' true := hRR'.cap
  have hshape : ∀ y, IsSlot Z.th y → shape (capV (L.mem s') y) = shape (capV (L.mem s) y) := by
    intro y hy
    by_cases e : y = x
    · subst e; rw [hcap', hcx]; rfl
    · rw [hco y hy e]
  -- the spec's step
  have hmem : ((), σ') ∈ (Fl4Spec.setCap (Z := Unit) (.untypedCap true p.bv sb.val f'.val) (pp.bv, idx) σ).1 := by
    rw [setCap_cnode _ hk hwf hidx]; exact Set.mem_singleton _
  have hcn : CnK σ σ' := nkn_setCap _ _ σ _ hmem
  have hkc : KeepC σ σ' := keepC_of hcn
    (nko_setCap (Ps := {pp.bv}) (.untypedCap true p.bv sb.val f'.val) (pp.bv, idx) (Set.mem_singleton _) σ _ hmem)
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
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      dev = false → UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
    intro sl p2 sb2 fi2 dev hsl hc2 hdv
    subst hdv
    by_cases e : cslotAddr sl = x
    · have hsl' : sl = (pp.bv, idx) := cslotAddr_inj hP hsl hAs e
      subst hsl'
      rw [capAt_capV, hcap'] at hc2
      cases eq_of_ok_eq hc2
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
    (Vs.VsSlotsT.of_some (· = x) (fun y hy e => hco y hy e)
      (fun y _ e _ _ _ _ _ _ => by rw [e, hcap']; exact Vs.vcapW_ut rfl)
      (fun y _ e _ _ => by rw [e, hcap']; trivial) (fun y _ e _ => by rw [e, hcap']; trivial)) (J.vkeep_slot hw)
    hLS.1 (fun p hp => J.zD p (hLS.2 p hp))

/-- **The `H` objects meeting a childless device cap's range are dead**
(module docstring). -/
theorem devRegion_dead {th : TypedHeap} {G : MdbGhost} (hJ : JCovD (L := L) th H G D Cs s)
    (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G) (hDA : DevApart (L := L) th H G Cs s) {x : U64}
    (hx : x ∈ G.chains.flatten) {p sb fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi true)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x) :
    ∀ q k, H q = some k → P1.RegionD H p.val (p.val + 2 ^ sb.val) q → q ∈ D := by
  intro q k hq hr
  unfold P1.RegionD P1.MeetsR at hr
  rw [hq] at hr
  simp only [Option.elim] at hr
  obtain ⟨-, hks, -, -, hid, -, hHo, -, -⟩ := hDA x hx p sb fi hcx
  have hfi : fi.val ≤ 2 ^ sb.val := hU.fib x hx p sb fi true hcx
  have h1 := Nat.one_le_two_pow (n := k.bits)
  rcases hHo q k hq with h | h | ⟨g1, g2, -⟩
  · exact absurd (Or.inl h) hr
  · exact absurd (Or.inr h) hr
  rcases hJ.h q k hq with hc | hd | hi
  · rcases ut_free hU hI hx hcx hnd (by omega) hc with e | e <;> omega
  · exact hd
  · rcases hi with hi | hi
    · rcases hid q hi with e | e <;> omega
    · obtain ⟨k1, k2⟩ := hi.2 k hq
      omega

variable (arI) in
/-- **The device reset's outcome at `J`**: `Ok` (no preemption point), the
spec's `reset_untyped_cap` outcome `σ'`, `JAtZ` there at the sets `Z` and
heap `H` given (the dropped ones), the cap with free index 0, the kernel
base `kb`, no CDT child, `DevApart`/`DevFreeT`/`DevGpm` there, the other
slots of `Z.th` kept from `m0`. -/
def ResetJPostD (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (kb : U64) (σ0 : Fl4Spec.State Unit) (m0 : U64 → U64) (pp : U64) (idx : List Bool) (p sb : U64)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  res.1 = .Ok () ∧ ∃ σ' Ac Lst D, (.ok (), σ') ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ0).1 ∧
    JAtZ (L := L) arI AR Z H Cs Ac Lst D res.2.1 res.2.2 σ' ∧
    capAt (L.mem res.2.1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 true) ∧ L.ksb res.2.1 = kb ∧
    (¬ ∃ y, σ'.cdt y = some (pp.bv, idx)) ∧
    DevApart (L := L) Z.th H Z.G Cs res.2.1 ∧ DevFreeT (L.mem res.2.1) Z.G σ' ∧ DevGpm (L.mem res.2.1) Z.G σ' ∧
    ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → capAt (L.mem res.2.1) y = capAt m0 y

set_option maxHeartbeats 16000000 in
/-- **FL4's `reset_untyped` of a used device cap at `J`** (module
docstring). -/
theorem JAtZ.reset_untypedDJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hres : σ.schedulerAction ≠ .chooseNewThread)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true))
    (hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx)) (hfi0 : fi.val ≠ 0)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ) (hGP : DevGpm (L.mem s) Z.G σ)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s)
    (hAF : ArchFitHyp H σ)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1)
    (hXc : ∀ y, IsSlot Z.th y → ∀ k q, Vs.VNeed (capV (L.mem s) y) k q → q ∈ Vs.lvlSet XP X4 X3 X2 X1 k) :
    untyped.reset_untyped st arI s a (cslotAddr (pp.bv, idx)) ⦃ res =>
      ResetJPostD (L := L) arI AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
        (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs (L.ksb s) σ (L.mem s) pp idx p sb res ⦄ := by
  set x := cslotAddr (pp.bv, idx) with hxdef
  set Z' := (Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s) with hZ'
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot Z.th x := hAs.isSlot
  obtain ⟨hP, ⟨hSR, -, hML, -, -⟩, -⟩ := J.xtop.rel
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hxm : x ∈ Z.G.chains.flatten := (hML.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hcv : capV (L.mem s) x = .Untyped p sb fi true := capV_of_capAt hcap
  obtain ⟨hpal, hks0, hnd0, has0, hid0, hrf, -, hcan, hsb4⟩ := hDA _ hxm p sb fi hcv
  have hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := fit_of_al (show p.val < 2 ^ 64 from p.bv.isLt) hsb hpal
  have hfib : fi.val ≤ 2 ^ sb.val := J.ut.fib _ hxm p sb fi true hcv
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    have h0 : 0 < objSize (ObjKind.cnode rs) := by simp only [objSize]; positivity
    rcases hrf pp _ hpp with h | h <;> omega
  have hpp' : Z'.th pp = some (.cnode rs) := by
    show restrictTh Z.th _ _ pp = _; rw [restrictTh_out hppout]; exact hpp
  have hpb : pp.bv ∉ regionSet p.bv sb.val := by rw [regionSet_iff _ _ _ hsb hfit]; exact hppout
  obtain ⟨cs, hk, hwf, -⟩ := hSR.cnode pp rs hpp
  have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap true p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hSR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 hsb4; simpa using this
  have hp8 : p.bv.toNat % 8 = 0 := by
    have h8 : 8 ∣ 2 ^ sb.val := dvd_trans (by norm_num) h16
    have := Nat.mod_mod_of_dvd p.val h8; rw [hpal, Nat.zero_mod] at this; exact this.symm
  -- the spec's `delete_objects`
  obtain ⟨hSD, hcdt, horig, hrepr, hcdom, hdtime, hist, hinode, harch, hdl, hdsi, hum, hz⟩ :=
    delSt_facts p sb hsb hfit σ
  obtain ⟨⟨u, σD⟩, hyD⟩ := deleteObjects_has hp8 sb.val σ
  have hσD : σD = delSt p.bv sb.val σ := deleteObjects_delSt p sb hp8 (by omega) hsb hfit σ hyD
  subst hσD
  have J' := J.dropAD hres hAs hcap hnc hDA hDF hGP hKR hDT hAF hSD hcdt horig hrepr hcdom hdtime hist hinode harch
    hdl hdsi hum hXP hX4 hX3 hX2 hX1 hM hXc
  have hTh : restrictTh Z'.th p.val (p.val + 2 ^ sb.val) = Z'.th := restrictTh_idem _ _ _
  -- no spec object meets the region after the drop (`DevFreeT`)
  have hSO : SpecOffR σ p sb := by
    intro o ko hko ho
    rcases hDF _ hxm p sb fi true hcv ⟨rfl, trivial⟩ o ko hko with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
      exact off_val hsb hfit (q := ⟨o⟩) ho ⟨h1, by show o.toNat < _; omega⟩
  have hRM : RgMiss p sb (delSt p.bv sb.val σ) := fun o ko ho => by
    by_cases hr : RgOf p sb o
    · rw [hSD.kin o hr] at ho; cases ho
    · rw [hSD.kout o hr] at ho; exact hSO o ko ho hr
  have hncD : ¬ ∃ y, (delSt p.bv sb.val σ).cdt y = some (pp.bv, idx) := by rw [hcdt]; exact hnc
  have hP' : Placed Z'.th := J'.xtop.rel.1
  have hAs' : AbsSlot Z'.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp')⟩
  have hxs' : IsSlot Z'.th x := hAs'.isSlot
  have hML' : MdbLinks Z'.th (L.mem s) Z.G := J'.xtop.rel.2.1.2.2.1
  have e0 : (0#u64 : U64).val = 0 := rfl
  -- FL4: the device branch writes the cap with free index 0
  unfold untyped.reset_untyped
  rw [slot_cap_eq, hcap]
  have hfi0' : ¬ (fi = 0#u64) := fun e => hfi0 (by rw [e]; rfl)
  simp only [bind_ok, untyped.as_untyped, hfi0', ↓reduceIte]
  obtain ⟨s2, hs2, cs2, hk2, hwf2, J2, hcap2, hks2, -, hfr2⟩ := spec_exists
    (J'.setFiJD hpp' hidx hcap hncD hTh 0#u64 (by rw [e0]; omega))
  rw [← hxdef] at hs2 hcap2 hfr2
  rw [hs2]
  simp only [bind_ok]
  have hmem := reset_devX hk hwf hidx hg hfi0 hp8 hpb hrcb hyD hk2 hwf2
  rw [e0] at J2
  set σ2 := setCnodeSlot (delSt p.bv sb.val σ) pp.bv rs cs2 idx (.untypedCap true p.bv sb.val 0) with hσ2
  -- the device facts at the reset's state
  have hcapV2 : capV (L.mem s2) x = .Untyped p sb 0#u64 true := capV_of_capAt hcap2
  have hcapK : ∀ y ∈ Z.G.chains.flatten, y ≠ x → capV (L.mem s2) y = capV (L.mem s) y := by
    intro y hy hne
    exact capV_of_capAt ((capAt_frame2 hP' hxs' ((hML'.members y).1 hy).1 hne hfr2).trans (capAt_capV _ _))
  have hidK : IdleKeep (L := L) s s2 := J'.idleW_keep J2.xtop.fin.1.1.1 rfl rfl
  have hnb : ∀ c, L.nodeBase s2 c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks2]
  have hidb : ∀ q, IdleAt (L := L) s2 q → IdleAt (L := L) s q := fun q h => by
    unfold IdleAt at h ⊢; rw [hidK.1, hidK.2] at h; exact h
  have hDA2 : DevApart (L := L) Z'.th (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Z'.G Cs s2 := by
    intro y hy p0 sb0 fi0 hc
    by_cases e : y = x
    · rw [e, hcapV2] at hc
      cases hc
      refine ⟨hpal, by rw [hks2]; exact hks0, fun c hc => by rw [hnb]; exact hnd0 c hc, by rw [hks2]; exact has0,
        fun q hq => hid0 q (hidb q hq), RegionFree.of_restrictTh hrf, fun q kd hq => ?_, hcan, hsb4⟩
      rw [P1.Heap.drop_eq_some] at hq
      obtain ⟨hnr, hq⟩ := hq
      unfold P1.RegionD P1.MeetsR at hnr
      rw [hq] at hnr
      simp only [Option.elim, not_not] at hnr
      rcases hnr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hcapK y hy e] at hc
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hDA y hy p0 sb0 fi0 hc
      refine ⟨a1, by rw [hks2]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks2]; exact a4,
        fun q hq => a5 q (hidb q hq), RegionFree.of_restrictTh a6, fun q kd hq => a7 q kd ?_, a8⟩
      exact (P1.Heap.drop_eq_some.1 hq).2
  have hDF2 : DevFreeT (L.mem s2) Z'.G σ2 := by
    intro y hy p0 sb0 fi0 d hc hPd o ko ho
    by_cases e : y = x
    · rw [e, hcapV2] at hc
      cases hc
      exact Or.inl ((hRM.setCn hk2 idx _) o ko ho)
    · rw [hcapK y hy e] at hc
      obtain ⟨ko1, hko1, hty⟩ := ksz_setCn hk2 hwf2 hidx (Fl4Spec.Cap.untypedCap true p.bv sb.val 0) o ko ho
      by_cases hr : RgOf p sb o
      · rw [hSD.kin o hr] at hko1; cases hko1
      · rw [hSD.kout o hr] at hko1
        rw [← objBits_of_aType hty]
        exact hDF y hy p0 sb0 fi0 d hc hPd o ko1 hko1
  have hGP2 : DevGpm (L.mem s2) Z'.G σ2 := by
    intro y hy p0 sb0 fi0 hc
    have ha2 : σ2.archState = σ.archState := harch
    rw [ha2]
    by_cases e : y = x
    · rw [e, hcapV2] at hc
      cases hc
      exact hGP x hxm p sb fi hcv
    · rw [hcapK y hy e] at hc
      exact hGP y hy p0 sb0 fi0 hc
  refine (WP.spec_ok _).2 ⟨rfl, σ2, Ac, Lst, D, hmem, J2, hcap2, hks2, hncD, hDA2, hDF2, hGP2,
    fun y hy hne => capAt_frame2 hP' hxs' hy hne hfr2⟩

set_option maxHeartbeats 8000000 in
/-- **The retype with the reset of a used device cap at `J`** (module
docstring; UtRetResetJ's `JAtZ.utResetJ` for a device cap). -/
theorem JAtZ.utDevResetJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {fiv : U64}
    (hnt : nt.val = 0 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi true nt us dest off win t r true fiv) (hf0 : fi.val ≠ 0)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ) (hGP : DevGpm (L.mem s) Z.G σ)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (blk call don : Bool) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) true
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win true) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype (pp.bv, idx) true p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) true)
        res ⦄ := by
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, ⟨-, -, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have hcv := capV_of_capAt hcap
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hpal, -, -, -, -, hrf, -, -, -⟩ := hDA _ hxG p sb fi hcv
  have hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := fit_of_al (show p.val < 2 ^ 64 from p.bv.isLt) hsb hpal
  have hfib : fi.val ≤ 2 ^ sb.val := J.ut.fib _ hxG p sb fi true hcv
  have hN : NoStraddle Z.th p.val (p.val + 2 ^ sb.val) := fun q k hq =>
    (hrf q k hq).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hns : ∀ y ∈ Z.G.chains.flatten, y.val < p.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hP ((hM.members y).1 hy).1
    rcases hrf q kq hq with e | e <;> omega
  have hnc : ¬ ∃ y, σ.cdt y = some (pp.bv, idx) := by
    have e := hctx.resetEq; exact of_decide_eq_true e.symm
  have hfiv0 : fiv = 0#u64 := by rw [hctx.fidx]; rfl
  -- the restart
  obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hks1, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hσ1k : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := fun o ho => by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
  have hσ1c : σ1.kheap (L.curW s).bv = some (.tcb { x1 with tcbState := .restart }) := by
    rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
  have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hσ1a : σ1.archState = σ.archState := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
  have hni1 : Entered σ1 :=
    ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact J.restart_keeps_resume hni hkx hcur⟩
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hBO1 : BufObjHyp Z.B σ1 := fun wp hw => by
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO wp hw
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hkx] at hk; cases hk
      exact ⟨_, _, hσ1c, h1, by simpa [Fl4Spec.objBits] using h2⟩
    · exact ⟨o, ko, by rw [hσ1k o ho]; exact hk, h1, h2⟩
  have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
    by_cases ho : o = (L.curW s).bv
    · subst ho; rw [hσ1c] at h; cases h
    · rwa [hσ1k o ho] at h) hH
  have hnc1 : ¬ ∃ y, σ1.cdt y = some (pp.bv, idx) := by rw [hσ1cdt]; exact hnc
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
      ({(.untypedCap true p.bv sb.val fi.val, σ1)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp)
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  -- the device facts after the restart (as UtDevUt's `JAtZ.utDevJ`)
  have hcvK : ∀ x ∈ Z.G.chains.flatten, capV (L.mem s1) x = capV (L.mem s) x := fun x hx =>
    capV_of_capAt ((hSS1.capAt ((hM.members x).1 hx).1).trans (capAt_capV _ _))
  have hidK : IdleKeep (L := L) s s1 :=
    J.idleW_keep J1.xtop.fin.1.1.1 hid1 (by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl)
  have hDA1 : DevApart (L := L) Z.th H Z.G Cs s1 := by
    intro x hx p0 sb0 fi0 hc
    rw [hcvK x hx] at hc
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hDA x hx p0 sb0 fi0 hc
    have hnb : ∀ c, L.nodeBase s1 c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks1]
    refine ⟨a1, by rw [hks1]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks1]; exact a4,
      fun q hq => a5 q ?_, a6, a7, a8⟩
    unfold IdleAt at hq ⊢; rw [hidK.1, hidK.2] at hq; exact hq
  have hDF1 : DevFreeT (L.mem s1) Z.G σ1 := SpecFreeP.frame hDF
    (fun x hx p0 sb0 fi0 d hc => ⟨x, hx, fi0, by rw [← hcvK x hx]; exact hc, le_rfl⟩)
    (fun o ko h => by
      by_cases ho : o = (L.curW s).bv
      · subst ho; rw [hσ1c] at h; cases h; exact ⟨_, hkx, rfl⟩
      · exact ⟨ko, by rw [← hσ1k o ho]; exact h, rfl⟩)
  have hGP1 : DevGpm (L.mem s1) Z.G σ1 := by
    intro x hx p0 sb0 fi0 hc
    rw [hσ1a]
    rw [hcvK x hx] at hc
    exact hGP x hx p0 sb0 fi0 hc
  rw [hs1]; simp only [bind_ok]
  -- `reset_untyped` at the restart's state
  have hnd' : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr (pp.bv, idx)) := nodesc_of_cdt hP hC hAs hnc
  obtain ⟨hKR, hDT⟩ := hRU s1 hs1 p.val (p.val + 2 ^ sb.val) (devRegion_dead J.jcov J.ut hI hDA hxG hcv hnd')
  have hres1 : σ1.schedulerAction ≠ .chooseNewThread := by rw [hni1.2]; simp
  refine retype_reset_wp arI s1 ar _ _ nt us dest off win true
    (J1.reset_untypedDJ hrcb hres1 hpp hidx hcap1 hnc1 hf0 hDA1 hDF1 hGP1 hKR hDT hAF1
      J1.vsc.needR.1 J1.vsc.needR.2.1 J1.vsc.needR.2.2.1 J1.vsc.needR.2.2.2.1 J1.vsc.needR.2.2.2.2
      (hVM s1 hs1) Vs.needR_roots) ?_ ?_
  swap
  · intro e s2 a2 hpost
    exact absurd hpost.1 (by simp)
  intro s2 a2 hpost
  obtain ⟨-, σ2, Ac2, Lst2, D2, hmem, J2, hcap2, -, hnc2, hDA2, hDF2, -, hSl2⟩ := hpost
  -- the spec's reset kept the entry fields and the old objects' types off the region
  have he := ent_reset (pp.bv, idx) σ1 (.ok (), σ2) hmem
  simp only [entF, Prod.mk.injEq] at he
  obtain ⟨hct2, hid2, hsa2⟩ := he
  have hni2 : Entered σ2 := ⟨by rw [hct2, hid2]; exact hni1.1, by rw [hsa2]; exact hni1.2⟩
  have hkT := reset_khT hg1 hf0 (.ok (), σ2) hmem
  have hkT' : ∀ o, (σ2.kheap o).map Fl4Spec.aType =
      if o ∈ regionSet p.bv sb.val then none else (σ1.kheap o).map Fl4Spec.aType := by
    intro o
    have e := congrFun hkT o
    simp only [khT, Fl4Spec.detype] at e
    rw [e]; split_ifs <;> rfl
  -- the source CNode, the destination CNode and the node cap's slot: off the region
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    have h0 : 0 < objSize (ObjKind.cnode rs) := by simp only [objSize]; positivity
    rcases hrf pp _ hpp with h | h <;> omega
  have hpp2 : restrictTh Z.th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs) := by
    rw [restrictTh_out hppout]; exact hpp
  obtain ⟨y, rr, gs, g, hy, hcy⟩ := hctx.cnode.2.2.2
  have hyG : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, hcy, by simp⟩
  have hdo := cnode_off_childless J.ut hI hxG hcv hnd' hyG (capV_of_capAt hcy)
  have hdest2 : restrictTh Z.th p.val (p.val + 2 ^ sb.val) dest = some (.cnode r) := by
    rw [restrictTh_out hdo]; exact hctx.cnode.1
  have hy2 : IsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) y := IsSlot.restrict hP hN hy (hns y hyG)
  have hyx : y ≠ cslotAddr (pp.bv, idx) := by
    rintro rfl; exact absurd (hcap.symm.trans hcy) (by simp)
  have hcapy : capAt (L.mem s2) y = ok (.CNode dest rr gs g) :=
    (hSl2 y hy2 hyx).trans ((hSS1.capAt hy).trans hcy)
  have hwin2 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    have hi : IsSlot Z.th (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
      ⟨dest, i, Or.inl ⟨r, hctx.cnode.1, by have := hctx.window.2.2; omega⟩, rfl⟩
    have hi2 : IsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
      ⟨dest, i, Or.inl ⟨r, hdest2, by have := hctx.window.2.2; omega⟩, rfl⟩
    have hne : slotAddr dest.bv (BitVec.ofNat 64 i) ≠ cslotAddr (pp.bv, idx) := by
      intro e; have h0 := hctx.empty i h1 h2; rw [e, hcap] at h0; simp at h0
    exact (hSl2 _ hi2 hne).trans ((hSS1.capAt hi).trans (hctx.empty i h1 h2))
  have hctx2 : RetCtx (L := L) (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) s2 σ2 (pp.bv, idx) sb 0#u64 true nt us
      dest off win t r true fiv :=
    ⟨hctx.ty, hctx.size, ⟨hdest2, hctx.cnode.2.1, hctx.cnode.2.2.1, y, rr, gs, g, hy2, hcapy⟩, hctx.window, hwin2,
      (decide_eq_true hnc2).symm, by rw [hfiv0]; rfl, hctx.sizeBits, hctx.memory, hctx.device⟩
  -- the IPC-buffer words kept: in objects off the region (`DevFreeT`), kept with their type
  have hBO2 : BufObjHyp (KeepB (KBOf p sb) Z.B) σ2 := by
    intro wp hw
    obtain ⟨hwB, -, hw1⟩ := hw
    obtain ⟨o, ko, hk, h1, h2⟩ := hBO1 wp hwB
    have hoff : o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
      rcases hDF1 _ hxG p sb fi true (capV_of_capAt hcap1) ⟨rfl, trivial⟩ o ko hk with h | ⟨h3, h4⟩
      · exact h
      · exfalso; rcases hw1 with e | e <;> omega
    have hnr : o ∉ regionSet p.bv sb.val := by
      rw [regionSet_iff' p o sb.val hsb hfit]
      have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko); omega
    have e := hkT' o
    rw [if_neg hnr, hk] at e
    cases h2' : σ2.kheap o with
    | none => rw [h2'] at e; cases e
    | some ko' =>
      rw [h2'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨o, ko', h2', h1, by rw [objBits_of_aType e]; exact h2⟩
  -- the arch objects: the old ones, `H`'s kept
  have hAF2 : ArchFitHyp (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) σ2 := by
    intro o ao n h hH
    rw [P1.Heap.drop_eq_some] at hH
    have e := hkT' o
    rw [h] at e
    split_ifs at e with hr
    · cases e
    · cases h1 : σ1.kheap o with
      | none => rw [h1] at e; cases e
      | some ko1 =>
        rw [h1] at e
        simp only [Option.map_some, Option.some.injEq] at e
        obtain ⟨ao1, rfl⟩ := aType_arch e.symm
        rw [objBits_of_aType e]; exact hAF1 o ao1 n h1 hH.2
  -- the kept references: the dropped heap has no object in the region
  have hRU2 : ∀ lo hi : Nat, p.val + (0#u64 : U64).val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)))
        (P1.RegionD (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) lo hi) s2 ∧
      DbgTimerKept (L := L) (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)))
        (P1.RegionD (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) lo hi) Cs s2 := by
    intro lo hi h1 h2
    have e0 : (0#u64 : U64).val = 0 := rfl
    have hK : ∀ x, (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) x ≠ none →
        ¬ P1.RegionD (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) lo hi x := by
      intro x hx hr
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hx
      obtain ⟨hnr, hHx⟩ := P1.Heap.drop_eq_some.1 hk
      have hr' : P1.MeetsR lo hi x.val
          (x.val + 2 ^ ((H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)) x).elim 0 P1.HKind.bits)) := hr
      have hnr' : ¬ P1.MeetsR p.val (p.val + 2 ^ sb.val) x.val (x.val + 2 ^ ((H x).elim 0 P1.HKind.bits)) := hnr
      rw [hk] at hr'
      rw [hHx] at hnr'
      simp only [Option.elim, P1.MeetsR] at hr' hnr'
      omega
    exact ⟨⟨fun _ _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _,
      fun _ _ _ => hK _, fun _ _ _ => hK _, fun _ _ _ => hK _⟩,
      fun _ _ _ => ⟨hK _, hK _, hK _, hK _, hK _⟩, fun _ _ => ⟨hK _, hK _, hK _⟩⟩
  have hbody : untyped.retype st arI s2 a2 (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win true ⦃ res =>
      UtBodyPostD (L := L) arI AR σ2 (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) true)
        res ⦄ := by
    rcases hnt with h0 | hnt
    · exact J2.utUtDevBodyJ hni2 hpp2 hidx hcap2 h0 hc0 hctx2 hfiv0 hDA2 hDF2 hBO2 hAF2 hRU2
    · exact J2.utDevBodyJ hni2 hpp2 hidx hcap2 hnt hc0 hctx2 hfiv0 hDA2 hDF2 hBO2 hAF2 hRU2
  exact WP.spec_mono hbody (fun res h => utRetPostJ_of_reset hst1 hmem h.post)

/-- **`JUtRetHypD` of a device untyped cap** (handoff/devretype.md "dj6
line"): the no-reset retype and the reset of an unused cap by UtDevUt's
`JAtZ.utDevJ`, the reset of a used cap by `JAtZ.utDevResetJ` (the decode
admits only untypeds and frames for a device cap, `RetCtx.device`). Premises:
`DevApart`, `DevFreeT`, `DevGpm` [J]; the reset's `resetChunkBits = 16` [P]
and `VsReachMiss` [J] at the restart's state (as the RAM reset). -/
theorem JAtZ.jUtRetHypDev {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi true))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ) (hGP : DevGpm (L.mem s) Z.G σ)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    {blk call don : Bool} {argsU : List U64} :
    JUtRetHypD (L := L) arI AR Z.th s ar σ sl p sb fi true ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  -- a device cap's decode admits only untypeds and frames (`RetCtx.device`)
  have hnt : nt.val = 0 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11 := by
    have hT := objTypeOf_fl4 hctx.ty us.val
    rcases hctx.device rfl with h | h
    · exact Or.inr (hT.2.2.1.1 h)
    · exact Or.inl (hT.2.2.2.1.1 h)
  obtain ⟨sl1, idx⟩ := sl
  obtain ⟨pp, hp1, hpp⟩ := hsl
  dsimp only at hp1 hpp
  subst hp1
  by_cases hc : reset = true ∧ fi.val ≠ 0
  · obtain ⟨rfl, hf0⟩ := hc
    exact J.utDevResetJ hni hct hpp rfl hcap hnt hc0 hctx hf0 hBO hAF hRU hDA hDF hGP hrcb hVM blk call don
  have hrs : reset = false ∨ fi.val = 0 := by
    cases reset
    · exact Or.inl rfl
    · exact Or.inr (Classical.byContradiction fun h => hc ⟨rfl, h⟩)
  exact J.utDevJ hni hct hpp rfl hcap hnt hc0 hctx hrs hBO hAF hRU hDA hDF blk call don

end

end

end Fl4Proofs.P3
