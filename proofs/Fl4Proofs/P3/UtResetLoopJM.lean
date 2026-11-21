/-
P3 (DESIGN.md §9), untyped (KENTRY-PLAN mr4): **the reset's chunk loop under
`MachPlat`** (mr3 NEXT (b), the first invocation family): UtResetLoopJ's
`JAtZ.reset_loopJ` with no `PPPlat`.

* `JAtZ.ppJSM`: `JAtZ.ppJS` (the preemption point with FL4's frame) from
  XTopJointMRHole2's `JAtZ.ppJDMV` (`MachPlat` [P], `PPPlatA` [P], `MR`,
  `ValidMachineTime`, `ValidIrqMasks` at the pre-state; `NoSwitch` from
  `PPR0`): continuing with `JAtZ` (same dead set) and `PPR0`, or preempted at a
  `JAtPreMV` state; `MR`/VMT/VIM after either way.
* `ResetJPostM`: `ResetJPost` with `JAtPreMV` for `JAtPre` at a preempted reset.
* `JAtZ.reset_loopJM`: the loop with `MR a σk.ms ∧ ValidMachineTime σk ∧
  ValidIrqMasks σk` added to the invariant. The chunk clear (`L.zr`) and the
  free-index write (`setFiJ`) are store-only (the arch state is kept) and the
  spec's slot write `setCnodeSlot` changes only `kheap` (machine state, clock,
  interrupt table kept by definition), so the invariant reaches the preemption
  point unchanged; there `ppJSM` re-establishes it or ends in `JAtPreMV`
  (what `hPre_ofZQIM` consumes).
-/
import Fl4Proofs.P3.UtResetLoopJ
import Fl4Proofs.P3.XTopJointMRHole2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
  {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`JAtZ.ppJS` under `MachPlat`** (module docstring): `JAtZ.ppJDMV` with FL4's frame. -/
theorem JAtZ.ppJSM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hPA : PPPlatA arI AR)
    (hR : MR a σ.machineState) (hV : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hRd : PPR0 σ) :
    ∃ r, sched.preemption_point st arI s a = ok r ∧ ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          (∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.2.1 r.2.2 σ') ∧
          PPR0 σ') ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          JAtPreMV (L := L) arI AR MR r.2.1 r.2.2 σ')) ∧
      XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧ MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ∧ ValidIrqMasks σ' ∧ SlotsSame Z.th (L.mem s) (L.mem r.2.1) ∧ L.ksb r.2.1 = L.ksb s ∧ L.cpu r.2.1 = L.cpu s ∧
      (∀ b : U64, P1.Aligned b → ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568) →
        ¬ (L.nodeBase s Z.c ≤ b.val ∧ b.val < L.nodeBase s Z.c + 4288) → L.mem r.2.1 b = L.mem s b) := by
  obtain ⟨⟨r1, s', a'⟩, hr, σ', hcase, hX', hR', hV', hVI'⟩ :=
    J.ppJDMV hAK hA hnd hM hPA hR hV hVI hRd.1.2.1 hRd
  have hP1 := P1.sched.preemption_point.pp hA s a J.blk
  rw [hr, WP.spec_ok] at hP1
  obtain ⟨-, hw⟩ := hP1
  refine ⟨(r1, s', a'), hr, ?_⟩
  simp only at hcase hX' hw hR' hV' hVI' ⊢
  have hX := J.xtop
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hN : P1.NodePlaced st Z.T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ (hc.cur ▸ J.kern.cpuCs)
  have hloc : ∀ b, P1.PPW st s b → ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568) ∨
      (L.nodeBase s Z.c ≤ b.val ∧ b.val < L.nodeBase s Z.c + 4288) := by
    intro b hb
    have hf := J.kern.ksbFit
    rcases hb with rfl | rfl | rfl
    · have := workUnits_val hf; exact Or.inl ⟨by omega, by omega⟩
    · have e := P1.nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
      refine Or.inr ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
      refine Or.inr ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := hX.slotsSame_of hw fun b hb => by
    have hf := J.kern.ksbFit
    rcases hb with rfl | rfl | rfl
    · have := workUnits_val hf; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e := P1.nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
  exact ⟨σ', hcase.imp (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) id, hX', hR', hV', hVI', hSS, hw.1, hw.2.1, fun b hb h1 h2 => hw.mem_eq hb fun hb' => (hloc b hb').elim h1 h2⟩

/-- **What the reset at `J` ends with** (module docstring): done, the cap's
free index 0 and the region zero, `JAtZ` at the same sets and a spec `Ok`
outcome of the reset from `σ0`; or preempted, `JAtPre` and a spec `error`
outcome. -/
def ResetJPostM (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (kb : U64) (σ0 : Fl4Spec.State Unit) (m0 : U64 → U64) (pp : U64) (idx : List Bool) (p sb : U64)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (res.1 = .Ok () ∧ ∃ σ' Ac Lst D, (.ok (), σ') ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ0).1 ∧
    JAtZ (L := L) arI AR Z H Cs Ac Lst D res.2.1 res.2.2 σ' ∧
    capAt (L.mem res.2.1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 false) ∧ L.ksb res.2.1 = kb ∧
    ZeroRegion (L.mem res.2.1) p.val (p.val + 2 ^ sb.val) ∧ RgMiss p sb σ' ∧
    (¬ ∃ y, σ'.cdt y = some (pp.bv, idx)) ∧ PPR0 σ' ∧
    (∀ y : Fl4Spec.Word, p.val ≤ y.toNat → y.toNat < p.val + 2 ^ sb.val → σ'.machineState.underlyingMemory y = 0) ∧
    ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → capAt (L.mem res.2.1) y = capAt m0 y) ∨
  (res.1 = .Err .Preempted ∧ ∃ σ', (.error (), σ') ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ0).1 ∧
    JAtPreMV (L := L) arI AR MR res.2.1 res.2.2 σ' ∧ ∃ Z', XTopAt (L := L) AR Z' res.2.1 res.2.2 σ')

set_option maxHeartbeats 16000000 in
/-- **The reset's chunk loop at `J`** (module docstring), from offset `o`
(a multiple of the chunk; the region zero above `o` plus a chunk; the spec's
chunks `o / 2^16, .., 0` left, `RContX`). -/
theorem JAtZ.reset_loopJM (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hPA : PPPlatA arI AR) (hrcb : Fl4Spec.resetChunkBits = 16)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb kb : U64} (hTh : restrictTh Z.th p.val (p.val + 2 ^ sb.val) = Z.th)
    (hfr : RegionFree Z.th p.val (p.val + 2 ^ sb.val)) (hRC : RgClear Z H Cs kb p sb) (hc0 : Z.c = 0#u64)
    (hp16 : p.val % 65536 = 0) (hpf : p.val + 2 ^ sb.val ≤ 2 ^ 64) (σ0 : Fl4Spec.State Unit) (m0 : U64 → U64) :
    ∀ (s : S) (a : A) (o : U64) (σk : Fl4Spec.State Unit) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (f : U64),
      o.val % 65536 = 0 → o.val + 65536 ≤ 2 ^ sb.val →
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σk →
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb f false) → f.val ≠ 0 →
      ZeroRegion (L.mem s) (p.val + o.val + 65536) (p.val + 2 ^ sb.val) →
      RContX false p.bv sb.val pp.bv idx σ0 (o.val / 65536) σk → RgMiss p sb σk →
      (¬ ∃ y, σk.cdt y = some (pp.bv, idx)) → PPR0 σk → L.ksb s = kb →
      (∀ y : Fl4Spec.Word, p.val ≤ y.toNat → y.toNat < p.val + 2 ^ sb.val → σk.machineState.underlyingMemory y = 0) →
      (∀ y, IsSlot Z.th y → y ≠ cslotAddr (pp.bv, idx) → capAt (L.mem s) y = capAt m0 y) →
      MR a σk.machineState → ValidMachineTime σk → ValidIrqMasks σk →
      untyped.reset_untyped_loop st arI s a (cslotAddr (pp.bv, idx)) p sb false o ⦃ res =>
        ResetJPostM (L := L) arI AR MR Z H Cs kb σ0 m0 pp idx p sb res ⦄ := by
  intro s a o σk Ac Lst D f ho1 ho2 J hcap hf0 hZ hK hRM hnc hR0 hkb hum hSl hMR hVT hVI
  set xs := cslotAddr (pp.bv, idx) with hxsdef
  have hP := J.xtop.rel.1
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot Z.th xs := hAs.isSlot
  have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ y.val := by
    intro y hy
    obtain ⟨q, kq, hq, h1, h2, -⟩ := slot_in_object hP hy
    rcases hfr q kq hq with e | e <;> omega
  have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
  unfold untyped.reset_untyped_loop
  refine loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => x.2.2.val % 65536 = 0 ∧ x.2.2.val + 65536 ≤ 2 ^ sb.val ∧ ∃ σk Ac Lst D f,
      JAtZ (L := L) arI AR Z H Cs Ac Lst D x.1 x.2.1 σk ∧
      capAt (L.mem x.1) xs = ok (.Untyped p sb f false) ∧ f.val ≠ 0 ∧
      ZeroRegion (L.mem x.1) (p.val + x.2.2.val + 65536) (p.val + 2 ^ sb.val) ∧
      RContX false p.bv sb.val pp.bv idx σ0 (x.2.2.val / 65536) σk ∧ RgMiss p sb σk ∧
      (¬ ∃ y, σk.cdt y = some (pp.bv, idx)) ∧ PPR0 σk ∧ L.ksb x.1 = kb ∧
      (∀ y : Fl4Spec.Word, p.val ≤ y.toNat → y.toNat < p.val + 2 ^ sb.val → σk.machineState.underlyingMemory y = 0) ∧
      (∀ y, IsSlot Z.th y → y ≠ xs → capAt (L.mem x.1) y = capAt m0 y) ∧
      MR x.2.1 σk.machineState ∧ ValidMachineTime σk ∧ ValidIrqMasks σk)
    _ _ _ ?_ ?_
  rotate_left
  · exact ⟨ho1, ho2, σk, Ac, Lst, D, f, J, hcap, hf0, hZ, hK, hRM, hnc, hR0, hkb, hum, hSl, hMR, hVT, hVI⟩
  rintro ⟨s1, a1, o⟩ ⟨ho1, ho2, σk, Ac, Lst, D, f, J, hcap, hf0, hZ, hK, hRM, hnc, hR0, hkb, hum, hSl, hMR, hVT, hVI⟩
  simp only at ho1 ho2 J hcap hZ hK hkb hMR ⊢
  unfold untyped.reset_untyped_loop.body
  have hiv : (core.num.U64.wrapping_add p o).val = p.val + o.val := by
    rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  simp only [lift, bind_ok, L.clear_free_eq]
  set q := core.num.U64.wrapping_add p o with hqdef
  have hqal : P1.Aligned q := by unfold P1.Aligned; rw [hiv]; omega
  -- the clear
  have J1 := J.zeroRg (by rw [hkb]; exact hRC) hc0 hpf hqal (n := untyped.RESET_CHUNK) (by rw [hC])
    (by rw [hiv]; omega) (by rw [hiv, hC]; omega)
  set s1z := L.zr s1 q untyped.RESET_CHUNK with hs1z
  have hz1 : ∀ w : U64, P1.Aligned w → L.mem s1z w = if q.val ≤ w.val ∧ w.val < q.val + untyped.RESET_CHUNK.val
      then 0#u64 else L.mem s1 w := fun w hw => L.mem_zr s1 q _ w hqal (by rw [hC]) (by rw [hiv, hC]; omega) hw
  have hS1 : SlotsSame Z.th (L.mem s1) (L.mem s1z) :=
    slotsSame_out hP (fun b hb => by have := hobj b hb; omega) (fun w hw ho => by
      rw [hz1 w hw, if_neg (by rw [hiv, hC]; omega)])
  have hcap1 : capAt (L.mem s1z) xs = ok (.Untyped p sb f false) := by rw [hS1.capAt hxs]; exact hcap
  have hZ1 : ZeroRegion (L.mem s1z) (p.val + o.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hz1 w hw]
    split_ifs with hc
    · rfl
    · rw [hiv, hC] at hc; exact hZ w hw (by omega) h2
  have hks1 : L.ksb s1z = L.ksb s1 := L.ksb_zr _ _ _
  -- the free index
  obtain ⟨s2, hs2, cs, hk, hwf, J2, hcap2, hks2, hcpu2, hfr2⟩ := spec_exists
    (J1.setFiJ hpp hidx hcap1 hnc hf0 hTh hfr hRM o (by omega) hZ1)
  rw [← hxsdef] at hs2 hcap2 hfr2
  rw [hs2]
  simp only [bind_ok]
  set σk2 := setCnodeSlot σk pp.bv rs cs idx (.untypedCap false p.bv sb.val o.val) with hσk2
  have hZ2 : ZeroRegion (L.mem s2) (p.val + o.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hfr2 w hw (by have := hobj xs hxs; omega) (by have := hobj xs hxs; omega)]
    exact hZ1 w hw h1 h2
  have hRM2 : RgMiss p sb σk2 := hRM.setCn hk idx _
  have hR02 : PPR0 σk2 := hR0.setCn hk hwf hidx _
  have hum2 : ∀ y : Fl4Spec.Word, p.val ≤ y.toNat → y.toNat < p.val + 2 ^ sb.val →
      σk2.machineState.underlyingMemory y = 0 := hum
  have hnc2 : ¬ ∃ y, σk2.cdt y = some (pp.bv, idx) := hnc
  have hSl2 : ∀ y, IsSlot Z.th y → y ≠ xs → capAt (L.mem s2) y = capAt m0 y := fun y hy hne => by
    rw [capAt_frame2 hP hxs hy hne hfr2, hS1.capAt hy]; exact hSl y hy hne
  -- the spec's chunk
  set k := o.val / 65536 with hkdef
  have hko : k * 65536 = o.val := by omega
  have hbase : (p.bv + (BitVec.ofNat 64 k <<< Fl4Spec.resetChunkBits)).toNat = p.val + k * 65536 :=
    chunk_base hrcb (by omega)
  have hfi : k * 2 ^ Fl4Spec.resetChunkBits = o.val := by rw [hrcb]; omega
  have hchunk : ∀ y, y ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σk2).1 →
      y ∈ ((chunkF false p.bv sb.val pp.bv idx k).run σk).1 := by
    intro y hy
    refine chunk_memX (r := rs) hrcb (by show p.val % 8 = 0; omega) hidx k hk hwf
      (by rw [hbase, hrcb]; omega) (fun y h1 h2 => hum y (by rw [hbase] at h1; omega)
        (by rw [hbase, hrcb] at h2; omega)) ?_
    rw [hfi]; exact hy
  have hks2' : L.ksb s2 = kb := by rw [hks2, hks1, hkb]
  by_cases ho0 : o = 0#u64
  · -- the last chunk: no preemption point in FL4, the spec's keeping the state
    rw [if_pos ho0]
    have hov : o.val = 0 := by rw [ho0]; rfl
    have hk0 : k = 0 := by omega
    obtain ⟨y, hy, hye⟩ := pp_ok σk2
    subst hye
    have hmem : ((Except.ok (), σk2) : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ0).1 := by
      have h0 := hchunk _ hy
      rw [hk0] at h0 hK
      exact RContX.done hK h0
    refine (WP.spec_ok _).2 (Or.inl ⟨rfl, σk2, Ac, Lst, D, hmem, J2, ?_, hks2', ?_, hRM2, hnc2, hR02, hum2, hSl2⟩)
    · rw [hcap2, ho0]
    · intro w hw h1 h2; exact hZ2 w hw (by omega) h2
  · rw [if_neg ho0]
    have ho0' : o.val ≠ 0 := fun e => ho0 (UScalar.eq_of_val_eq e)
    -- #52: the cap just written reads back as the untyped cap, so the
    -- doomed-transaction exit (`as_untyped` = `none`) is not taken.
    have hcapS : obj.Slot.cap st xs s2 = ok (.Untyped p sb o false) := by rw [slot_cap_eq]; exact hcap2
    simp only [hcapS, bind_ok, untyped.as_untyped, core.option.Option.is_none, Bool.false_eq_true,
      ↓reduceIte]
    obtain ⟨⟨r, s3, a2⟩, hp3, σp, hcase, hXp, hRp, hVp, hVIp, hSS3, hks3, -, hfr3⟩ :=
      J2.ppJSM hAK hA hnd hM hPA (MR := MR) hMR hVT hVI hR02
    rw [hp3]
    simp only [bind_ok]
    simp only at hcase hXp hSS3 hks3 hfr3 hRp
    have hcap3 : capAt (L.mem s3) xs = ok (.Untyped p sb o false) := by rw [hSS3.capAt hxs]; exact hcap2
    have hZ3 : ZeroRegion (L.mem s3) (p.val + o.val) (p.val + 2 ^ sb.val) := by
      intro w hw h1 h2
      have hks := hRC.ks
      have hnd0 := hRC.nd Z.c (hc0 ▸ J2.kern.cs0)
      rw [hfr3 w hw (by rw [hks2']; omega) (by
        show ¬ ((L.ksb s2).val + 13568 + Z.c.val * 4288 ≤ w.val ∧ w.val < (L.ksb s2).val + 13568 + Z.c.val * 4288 + 4288)
        rw [hks2']; omega)]
      exact hZ2 w hw h1 h2
    rcases hcase with ⟨hok, hy, ⟨Ac', Lst', J3⟩, hR03⟩ | ⟨herr, hy, hPre⟩
    · subst hok
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
      have hk1 : k = (k - 1) + 1 := by omega
      have hcm := hchunk _ hy
      rw [hk1] at hcm hK
      have hK' := RContX.step hK hcm
      obtain ⟨hkh, hcdt, -, -, humq⟩ := pp_ksm' hy
      have hsv : (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val = o.val - 65536 := by
        show (BitVec.ofNat 64 (max 0 (o.val - untyped.RESET_CHUNK.val))).toNat = _
        rw [hC]; simp; omega
      refine (WP.spec_ok _).2 ⟨⟨by rw [hsv]; omega, by rw [hsv]; omega, σp, Ac', Lst', D, o, J3, hcap3, ho0', ?_, ?_,
        hRM2.of_kheap hkh, by rw [hcdt]; exact hnc2, hR03, by rw [hks3, hks2'], fun y h1 h2 => by rw [humq]; exact hum2 y h1 h2,
        fun y hy hne => by rw [hSS3.capAt hy]; exact hSl2 y hy hne, hRp, hVp, hVIp⟩, ?_⟩
      · rw [hsv, show p.val + (o.val - 65536) + 65536 = p.val + o.val by omega]; exact hZ3
      · rw [hsv, show (o.val - 65536) / 65536 = k - 1 by omega]; exact hK'
      · show (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val < o.val
        rw [hsv]; omega
    · subst herr
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      simp only [bind_tc_ok, bind_ok]
      have hmem := RContX.preempt hK (hchunk _ hy)
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, σp, hmem, hPre, Z, hXp⟩)

end

end

end Fl4Proofs.P3
