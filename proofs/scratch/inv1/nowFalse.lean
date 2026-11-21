import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.UtResetSpecJ
open Aeneas Aeneas.Std Result
open Fl4Proofs.P3 Fl4Spec

/-- Every clock read is at most the cap `-(getCurrentTimeBuffer + 1)`. -/
theorem gct_le (ms : MachineState) (v : Word64) (ms' : MachineState) (h : (v, ms') ∈ (getCurrentTime ms).1) :
    v.toNat ≤ (-(getCurrentTimeBuffer + 1)).toNat := by
  unfold getCurrentTime at h
  obtain ⟨x1, -, h⟩ := h
  obtain ⟨x2, -, h⟩ := h
  obtain ⟨x3, -, h⟩ := h
  obtain ⟨x4, -, h⟩ := h
  obtain ⟨x5, h5, h⟩ := h
  obtain ⟨x6, -, h⟩ := h
  have e := congrArg Prod.fst (Set.mem_singleton_iff.1 h)
  have e5 := congrArg Prod.fst (Set.mem_singleton_iff.1 h5)
  simp only at e e5
  rw [e, BitVec.toNat_ofNat, e5]
  exact (Nat.mod_le _ _).trans (Nat.min_le_left _ _)

/-- `PPPlat.now` (∀ a σ, NowAgree) is false: at a spec state whose
`curTime` is `allOnes`, the clock read is capped below it. -/
theorem nowAgree_all_false {A : Type} (arI : fl4_core.machine.Arch A) (a : A) :
    ¬ (∀ σ : Fl4Spec.State Unit, NowAgree arI a σ) := by
  intro h
  let σ0 : Fl4Spec.State Unit := Classical.choice inferInstance
  have h1 := h { σ0 with curTime := BitVec.allOnes 64 }
  unfold NowAgree at h1
  obtain ⟨r, -, ms, he, hle, -⟩ := Fl4Proofs.P3.spec_exists h1
  have hm : (r.1.bv, { ({ σ0 with curTime := BitVec.allOnes 64 } : Fl4Spec.State Unit) with machineState := ms })
      ∈ (doMachineOp (Z := Unit) getCurrentTime { σ0 with curTime := BitVec.allOnes 64 }).1 := by
    rw [he]; exact Set.mem_singleton _
  obtain ⟨ms', hms, -⟩ := dmo_mem hm
  have hv := gct_le _ _ _ hms
  have hb : getCurrentTimeBuffer ≠ 0 := by
    have := getCurrentTime_buffer_pos
    intro e; unfold getCurrentTimeBuffer timeBufferConst MAX_PERIOD at e; rw [e] at this
    exact (BitVec.lt_irrefl _) this
  have hc : (-(getCurrentTimeBuffer + 1)).toNat ≠ 2 ^ 64 - 1 := by
    intro e
    apply hb
    have e2 : -(getCurrentTimeBuffer + 1) = BitVec.allOnes 64 :=
      BitVec.eq_of_toNat_eq (by rw [e, BitVec.toNat_allOnes])
    have e3 : getCurrentTimeBuffer + 1 = 1 := by
      have := congrArg (fun x => -x) e2
      simp only [BitVec.neg_neg] at this
      rw [this]; decide
    have e4 := congrArg (fun x => x - 1) e3
    simpa using e4
  have hlt := (-(getCurrentTimeBuffer + 1)).isLt
  have hle' : (BitVec.allOnes 64).toNat ≤ r.1.bv.toNat := BitVec.le_def.1 hle
  have hv' : r.1.bv.toNat ≤ (-(getCurrentTimeBuffer + 1)).toNat := hv
  rw [BitVec.toNat_allOnes] at hle'
  omega

#print axioms nowAgree_all_false
