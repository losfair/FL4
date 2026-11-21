/-
P3 (DESIGN.md §9), TCB: **ReadRegisters' reply at `J`** (IpcReadRegs' steps
at `JAtZ` in place of VSpace's `RInv`; the label itself is XTopJointTcb's
`tcb_read_regsJ`).

* `JAtZ.mrRegJ`, `JAtZ.mrBufJ`: one message word of the caller at `J`, a
  message register (`JAtZ.regWrJ`, as `rr_regw`) or a buffer word
  (`JAtZ.userWrJ` with XTopJointData's `BufWordOK`, as `rr_bufw`), the
  spec's `set_mrs` state growing by the word.
* `rrJ_loop0`, `rrJ_loop1`, `rrJ_loopGB`: `read_registers`' copy loops (the
  frame registers into `MR0`..`MR3`, past `MR3` into the buffer, the integer
  registers into the buffer) with `JAtZ` as the loop invariant (as
  `rr_loop0`, `rr_loop1`, `rr_loopGB`; the source's registers by
  `rr_src_reg` at `JAtZ.xtop.toRInv`).
* `JAtZ.rrTailJ`: the message info then `Running` after the words (the
  badge written first): `JAt` at the spec's success tail with data, the
  caller no longer `Restart` and `RelTopM` (`sts_inv` at the same `J`).
-/
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.IpcReadRegs
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}

set_option maxHeartbeats 8000000 in
/-- **A message-register word of the caller at `J`** (as `rr_regw`). -/
theorem JAtZ.mrRegJ {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef}
    {ms : List Fl4Spec.Word} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 buf ms))
    (hct : ct ∈ Z.T) (j : Nat) (hj : j = ms.length) (h4 : ms.length < 4) (v : U64) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (regA ct (regIdx (mrIdx j))) v) a
      (MrS σ0 ct.bv x0 buf (ms ++ [v.bv])) := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  have hX := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hkx (Endp.mrIdx j) (mrIdx_ne_badge _) v
  obtain ⟨V, J1⟩ := J.regWrJ hct hkx (Endp.mrIdx j) v hX
  refine ⟨V, ?_⟩
  cases buf with
  | none =>
    have e := Endp.mrStateN_snoc_lt σ0 ct.bv x0 ms v.bv j hj h4
    simp only [MrS] at J1 ⊢; rw [← e]; exact J1
  | some p =>
    have e := Endp.mrState_snoc_lt σ0 ct.bv x0 p ms v.bv j hj h4
    simp only [MrS] at J1 ⊢; rw [← e]; exact J1

set_option maxHeartbeats 8000000 in
/-- **A message word in the caller's IPC buffer at `J`** (as `rr_bufw`). -/
theorem JAtZ.mrBufJ {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {p : Fl4Spec.ObjRef}
    {ms : List Fl4Spec.Word} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 (some p) ms))
    (hk0 : σ0.kheap ct.bv = some (.tcb x0)) (w : U64) (hbm : BufMap Z.B w p)
    (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ0) (k : U64) (hk : k.val = ms.length + 1)
    (h4 : 4 ≤ ms.length) (h120 : ms.length < 120) (hOK : BufWordOK H σ0 (fl4BufA w k)) (v : U64) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s (fl4BufA w k) v) a (MrS σ0 ct.bv x0 (some p) (ms ++ [v.bv])) := by
  have hwB := hbm k (by omega)
  have hBP' : BufPlaced (L := L) Z.N Z.C Z.B Z.c s (MrS σ0 ct.bv x0 (some p) ms) := hBP.mono rfl (MrS_sc hk0 _ _)
  obtain ⟨hAp, o, ko, hko, g1, g2⟩ := hOK
  have hObj : ∃ o ko, (MrS σ0 ct.bv x0 (some p) ms).kheap o = some ko ∧
      o.toNat ≤ (fl4BufA w k).val ∧ (fl4BufA w k).val < o.toNat + 2 ^ Fl4Spec.objBits ko := by
    by_cases e : o = ct.bv
    · subst e; rw [hk0] at hko; cases hko
      exact ⟨_, _, MrS_kheap_t _ _ _ _ _, g1, g2⟩
    · exact ⟨o, ko, by rw [MrS_kheap_ne _ _ _ _ _ e]; exact hko, g1, g2⟩
  have J1 := J.userWrJ hBP' hwB hAp hObj v
  simp only [hk] at J1
  simp only [MrS] at J1 ⊢
  rw [← Endp.mrState_snoc_ge _ _ _ _ _ _ h4 h120]
  exact J1

set_option maxHeartbeats 8000000 in
/-- **The frame registers into the caller's message registers at `J`**
(`MR0`..`MR3`; as `rr_loop0`). -/
theorem rrJ_loop0 {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 buf []))
    (hct : ct ∈ Z.T) {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ Z.T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) :
    tcb.read_registers_loop0 st s src n ct 0#u64 ⦃ r => r.2.val = min n.val 4 ∧
      (∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.1 a (MrS σ0 ct.bv x0 buf ((rrOf xs n).take r.2.val))) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.read_registers_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 4 ∧
      (∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D x.1 a
        (MrS σ0 ct.bv x0 buf ((rrOf xs n).take x.2.val))) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s)
  · rintro ⟨s', i⟩ ⟨hi, ⟨V', J'⟩, hk', hc'⟩
    unfold tcb.read_registers_loop0.body
    simp only at hi J' hk' hc' ⊢
    by_cases h1 : i < n
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 4 := by have := (P1.gt_iff_val).not.1 h1; omega
      exact ⟨this, ⟨V', J'⟩, hk', hc'⟩
    rw [if_pos h1]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    have h2 : i < tcb.N_FRAME := (P1.gt_iff_val).2 (by rw [hf]; omega)
    rw [if_pos h2]
    by_cases h3 : i < msg.N_MSG_REGISTERS
    swap
    · rw [if_neg h3, WP.spec_ok]
      have : i.val = min n.val 4 := by have := (P1.gt_iff_val).not.1 h3; rw [hN] at this; omega
      exact ⟨this, ⟨V', J'⟩, hk', hc'⟩
    rw [if_pos h3]
    have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rwa [hN] at this
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[i.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq frame_regs_val, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega), wrRegs, List.getElem_append_left (show i.val < Fl4Spec.frameRegisters.length by omega)]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r3 rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' ct _ _) ?_
    rintro s2 rfl
    obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hi4' : i4.val = i.val + 1 := by simpa using h4v
    have hlen : ((rrOf xs n).take i.val).length = i.val := by simp [List.length_take, rrOf_length]; omega
    obtain ⟨V2, J2⟩ := J'.mrRegJ hct i.val hlen.symm (by omega)
      (L.mem s' (regA src (regIdx (wrRegs[i.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks J'.xtop.toRInv, ← rrOf_take_succ xs n i.val (by omega)] at J2
    refine ⟨⟨by show i4.val ≤ min n.val 4; omega, ⟨V2, by rw [hi4']; exact J2⟩,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc'⟩,
      by show 4 - i4.val < 4 - i.val; omega⟩
  · exact ⟨by simp, ⟨Z.vs, by simpa using J⟩, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **The frame registers past `MR3` into the caller's IPC buffer at `J`**
(as `rr_loop1`). -/
theorem rrJ_loop1 {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap ct.bv = some (.tcb x0))
    (pb : Fl4Spec.ObjRef) (w : U64) (hbm : BufMap Z.B w pb)
    (hOK : ∀ i : U64, i.val < 128 → BufWordOK H σ0 (fl4BufA w i))
    {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ Z.T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) (i0 : U64)
    (hi0 : 4 ≤ i0.val) (hi0n : i0.val ≤ min n.val 18)
    (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ0)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take i0.val))) :
    tcb.read_registers_loop1 st s src n w i0 ⦃ r => r.2.val = min n.val 18 ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D r.1 a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take r.2.val)) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.read_registers_loop1
  apply loop.spec_decr_nat (measure := fun x => 18 - x.2.val)
    (inv := fun x => 4 ≤ x.2.val ∧ x.2.val ≤ min n.val 18 ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D x.1 a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take x.2.val)) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s)
  · rintro ⟨s', i⟩ ⟨hi4, hi, J', hk', hc'⟩
    unfold tcb.read_registers_loop1.body
    simp only at hi4 hi J' hk' hc' ⊢
    by_cases h1 : i < n
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h1; omega
      exact ⟨this, J', hk', hc'⟩
    rw [if_pos h1]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    by_cases h2 : i < tcb.N_FRAME
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h2; rw [hf] at this; omega
      exact ⟨this, J', hk', hc'⟩
    rw [if_pos h2]
    have hi18 : i.val < 18 := by have := (P1.gt_iff_val).1 h2; rwa [hf] at this
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[i.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq frame_regs_val, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega), wrRegs, List.getElem_append_left (show i.val < Fl4Spec.frameRegisters.length by omega)]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h3e, bind_ok]
    have hi3 : i3.val = i.val + 1 := by simpa using h3v
    refine WP.spec_bind (Endp.msg.buf_set.spec s' w i3 _) ?_
    rintro s2 rfl
    rw [WP.spec_ok]
    have hlen : ((rrOf xs n).take i.val).length = i.val := by simp [List.length_take, rrOf_length]; omega
    have hBP' : BufPlaced (L := L) Z.N Z.C Z.B Z.c s' σ0 := hBP.mono hk' (fun _ _ _ h => h)
    have J2 := J'.mrBufJ hk0 w hbm hBP' i3 (by rw [hlen]; exact hi3) (by omega) (by omega) (hOK i3 (by omega))
      (L.mem s' (regA src (regIdx (wrRegs[i.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks J'.xtop.toRInv, ← rrOf_take_succ xs n i.val (by omega)] at J2
    refine ⟨⟨by show 4 ≤ i3.val; omega, by show i3.val ≤ min n.val 18; omega, by rw [hi3]; exact J2,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc'⟩,
      by show 18 - i3.val < 18 - i.val; omega⟩
  · exact ⟨hi0, hi0n, J, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **The integer registers into the caller's IPC buffer at `J`** (as
`rr_loopGB`). -/
theorem rrJ_loopGB {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap ct.bv = some (.tcb x0))
    (pb : Fl4Spec.ObjRef) (w : U64) (hbm : BufMap Z.B w pb)
    (hOK : ∀ i : U64, i.val < 128 → BufWordOK H σ0 (fl4BufA w i))
    {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ Z.T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) (hn : 18 < n.val)
    (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ0)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take 18)))
    (body : S → U64 → Result (ControlFlow (S × U64) (S × U64)))
    (hbody : ∀ s k, body s k = if k < tcb.N_GP then (do
        let i ← k + tcb.N_FRAME
        if i < n then do
          let i1 ← lift (UScalar.cast .Usize k)
          let i2 ← Aeneas.Std.Array.index_usize regs.GP_REGISTERS i1
          let v ← obj.Tcb.reg st src s i2
          let i3 ← i + 1#u64
          let s1 ← msg.buf_set st s w i3 v
          let k1 ← k + 1#u64
          ok (ControlFlow.cont (s1, k1))
        else ok (ControlFlow.done (s, k)))
      else ok (ControlFlow.done (s, k))) :
    loop (fun (x : S × U64) => body x.1 x.2) (s, 0#u64) ⦃ r => 18 + r.2.val = min n.val 20 ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D r.1 a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take (18 + r.2.val))) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  apply loop.spec_decr_nat (measure := fun x => 2 - x.2.val)
    (inv := fun x => 18 + x.2.val ≤ min n.val 20 ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D x.1 a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take (18 + x.2.val))) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s)
  · rintro ⟨s', k⟩ ⟨hk, J', hk', hc'⟩
    simp only at hk J' hk' hc' ⊢
    rw [hbody]
    by_cases h1 : k < tcb.N_GP
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : 18 + k.val = min n.val 20 := by have := (P1.gt_iff_val).not.1 h1; rw [hg] at this; omega
      exact ⟨this, J', hk', hc'⟩
    rw [if_pos h1]
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rwa [hg] at this
    obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
    rw [hie, bind_ok]
    have hiv' : i.val = k.val + 18 := by rw [← hf]; simpa using hiv
    by_cases h2 : i < n
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : 18 + k.val = min n.val 20 := by have := (P1.gt_iff_val).not.1 h2; omega
      exact ⟨this, J', hk', hc'⟩
    rw [if_pos h2]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h2
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' k (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[18 + k.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq gp_regs_val, List.getElem_map]
      congr 1
      simp only [wrRegs, cast_to_us' k (by omega)]
      rw [List.getElem_append_right (by rw [hfl]; omega)]
      simp [hfl]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h3e, bind_ok]
    have hi3 : i3.val = i.val + 1 := by simpa using h3v
    refine WP.spec_bind (Endp.msg.buf_set.spec s' w i3 _) ?_
    rintro s2 rfl
    obtain ⟨k1, h4e, h4v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hk1 : k1.val = k.val + 1 := by simpa using h4v
    have hlen : ((rrOf xs n).take (18 + k.val)).length = 18 + k.val := by
      simp [List.length_take, rrOf_length]; omega
    have hBP' : BufPlaced (L := L) Z.N Z.C Z.B Z.c s' σ0 := hBP.mono hk' (fun _ _ _ h => h)
    have J2 := J'.mrBufJ hk0 w hbm hBP' i3 (by rw [hlen]; omega) (by omega) (by omega) (hOK i3 (by omega))
      (L.mem s' (regA src (regIdx (wrRegs[18 + k.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks J'.xtop.toRInv, ← rrOf_take_succ xs n (18 + k.val) (by omega)] at J2
    refine ⟨⟨by show 18 + k1.val ≤ min n.val 20; omega, by rw [hk1, ← Nat.add_assoc]; exact J2,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc'⟩,
      by show 2 - k1.val < 2 - k.val; omega⟩
  · exact ⟨by simp; omega, by simpa using J, rfl, rfl⟩

set_option maxHeartbeats 16000000 in
/-- **The message info and `Running` after the message words at `J`** (the
badge written first, as `rr_tail_xtop`): `JAt` at the spec's success tail
with data, the caller no longer `Restart` and `RelTopM` (`sts_inv` at the
same `J`'s `RInv`). -/
theorem JAtZ.rrTailJ {σy : Fl4Spec.State Unit} {ct : U64} {x : Fl4Spec.Tcb} {ms : List Fl4Spec.Word}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a
      (MrS (Notif.updK σy ct.bv (.tcb (Notif.setReg x Fl4Spec.badge_register 0))) ct.bv
        (Notif.setReg x Fl4Spec.badge_register 0) (Endp.ipcBufOf true x) ms))
    (hct : ct ∈ Z.T) (hcur : ct.bv = σy.curThread) (hk : σy.kheap ct.bv = some (.tcb x))
    (hrs : x.tcbState = .restart) (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σy)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x) ms.length) (hn128 : n.val < 128) :
    (do
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      let s6 ← msg.set_msg_info st s ct mi
      let s7 ← sched.set_thread_state st s6 ct sched.TS_RUNNING
      ok (s7, a)) ⦃ res =>
      L.mem res.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail true ct.bv ms σy).1, RelTopM (L := L) res.1 z.2 ∧ JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  set xA := Notif.setReg x Fl4Spec.badge_register 0 with hxA
  set buf := Endp.ipcBufOf true x
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_bind (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s3 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have hkA := MrS_kheap_t (Notif.updK σy ct.bv (.tcb xA)) ct.bv xA buf ms
  have hX2 := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hkA Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J.regWrJ hct hkA Fl4Spec.msg_info_register v hX2
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen buf ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  have eR : Notif.updK (MrS (Notif.updK σy ct.bv (.tcb xA)) ct.bv xA buf ms) ct.bv
      (.tcb (Notif.setReg (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))
        Fl4Spec.msg_info_register v.bv)) = replyStateB σy ct.bv x buf ms := by
    unfold replyStateB; rw [hvd]
  rw [eR] at J2
  have htcb : (Z.mv Z.G V2).th ct = some .tcb := (J2.xtop.curTcb (by rw [replyStateB_cur]; exact hcur.symm)).1
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_bind (WP.spec_and (sts_inv _ a _ J2.xtop.toRInv ct htcb (by rw [replyStateB_cur]; exact hcur)
    (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]; rfl) J2.kern.act .running (by decide) _ hcode)
    (J2.runJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]))) ?_
  rintro s5 ⟨⟨hI5, hst5, -⟩, Lst', D', J5⟩
  rw [WP.spec_ok]
  exact ⟨by rw [hst5]; exact run_ne_rst, _, by rw [specTail_data hk hrs ms hlen hfr]; exact Set.mem_singleton _,
    J5.xtop.relTop, _, _, _, _, _, _, J5⟩

set_option maxHeartbeats 64000000 in
/-- **ReadRegisters' leaf at `J`** (IpcReadRegsJ's `readRegsXHypJ` with
`JAtZ` carried): after the caller's restart, the source's suspend
(`JAtZ.suspendJ` with the four cancel steps, `recvReplyHyp_holds` for
`jCancel_recv`), then, called, the badge (`JAtZ.regWrJ`), the copy loops
(`rrJ_loop0`, `rrJ_loop1`, `rrJ_loopGB`; the buffer words by
`JAtZ.bufWord`) and the message info and `Running` (`JAtZ.rrTailJ`); not
called, `Running` (`JAtZ.runJ`, `XTop`'s facts by `nodata_tail_core`). -/
theorem JAtZ.readRegsJ {s1 : S} {σ1 : Fl4Spec.State Unit} {ct p : U64} {blk call don : Bool}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a σ1)
    (hns : ∀ u, σ1.schedulerAction = .switchThread u → False) (hidp : p.bv ≠ σ1.idleThread)
    (hcur1 : σ1.curThread = ct.bv) {x1 : Fl4Spec.Tcb} (hkc1 : σ1.kheap ct.bv = some (.tcb x1))
    (hrs1 : x1.tcbState = .restart) (hpne : p ≠ ct) (hpT : p ∈ Z.T) (flags n : U64) :
    tcb.read_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n call ⦃ r =>
      L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ rr σy,
        (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.readRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
        ∃ z ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  have hctT : ct ∈ Z.T := TopSR.cur_mem J1.xtop.fin.1 hcur1.symm
  have hne : p.bv ≠ ct.bv := fun e => hpne (P1.eq_of_bv e)
  unfold tcb.read_registers
  refine WP.spec_bind (cur_thread_bv hI1.2.2.1) ?_
  rintro ct' hct'
  obtain rfl : ct = ct' := (P1.eq_of_bv (hct'.trans hcur1)).symm
  rw [and1_ne0]
  -- the source's suspend
  have hsus : (if Fl4Spec.testBit flags.bv 0 = true then sched.suspend st arI s1 a p else ok (s1, a)) ⦃ r =>
      r.2 = a ∧ ∃ σy, Fl4Spec.NonDet.when (Fl4Spec.testBit flags.bv 0 = true) (Fl4Spec.suspend (Z := Unit) p.bv) σ1 =
        ({((), σy)}, False) ∧ StK.OSK p.bv σ1 σy ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σy ⦄ := by
    cases Fl4Spec.testBit flags.bv 0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, σ1, rfl, StK.OSK.refl _, Z.vs, Ac, Lst, D, J1⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (J1.suspendJ (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
        (jCancel_reply arI) hpT (fun u h => (hns u h).elim) hidp) ?_
      rintro ⟨s2, a2⟩ ⟨h1, σy, h2, V, Ac', Lst', D', J2⟩
      refine ⟨h1, σy, by simpa [Fl4Spec.NonDet.when] using h2, StK.st_suspend σ1 ((), σy) ?_, V, Ac', Lst', D', J2⟩
      rw [h2]; exact Set.mem_singleton _
  refine WP.spec_bind hsus ?_
  rintro ⟨s2, a2⟩ ⟨ha2, σy, hsy, hosk, V2, Ac2, Lst2, D2, J2⟩
  obtain rfl : a = a2 := ha2.symm
  simp only at J2
  -- the caller and the source after it
  have hXy := J2.xtop.irelK J2.ks J2.buf
  obtain ⟨xy, hky, -⟩ := hXy.1.tcb ct hctT
  obtain ⟨y0, hy0, hys⟩ := hosk.1 ct.bv xy (Ne.symm hne) hky
  rw [hkc1] at hy0; cases hy0
  have hrs : xy.tcbState = .restart := hys.trans hrs1
  have hcury : ct.bv = σy.curThread := (hosk.2.trans hcur1).symm
  obtain ⟨xs, hks, -⟩ := hXy.1.tcb p hpT
  have hXZ := J2.xtop
  have hOKb := J2.xferH.1
  have hBCy := J2.xferH.2.1
  have hBPy := J2.xferH.2.2
  have hact := J2.kern.act
  have htcb : (Z.mv Z.G V2).th ct = some .tcb := (hXZ.curTcb hcury.symm).1
  -- the spec's ReadRegisters
  have hmem : ((.ok (rrOf xs n) : Except Unit (List Fl4Spec.Data)), σy) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.readRegisters p.bv
        (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
    unfold Fl4Spec.invokeTcb
    refine mem_liftE (x := (rrOf xs n, σy)) (mem_bind_nd (x := ((), σy)) (by rw [hsy]; rfl)
      (mem_bind_nd (x := (σy.curThread, σy)) rfl (mem_bind_nd rfl ?_)))
    rw [asUser_mapM_get hks]
    exact Set.mem_singleton _
  cases call
  · -- not called: `Running`
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (WP.spec_and (nodata_tail_core hXZ hcury hky hrs hact (rrOf xs n))
      (J2.runJ hctT hky hrs)) ?_
    rintro s3 ⟨⟨hne3, z, hz, hRT, -⟩, Lst', D', J5⟩
    refine (WP.spec_ok _).2 ⟨hne3, rrOf xs n, σy, hmem, z, hz, hRT, ?_⟩
    unfold specTail at hz
    rw [nd_bind_one (Notif.getThreadState_eq hky)] at hz
    simp only [hrs] at hz
    rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind', Notif.setThreadState_eq .running hky] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J5⟩
  -- called: the caller's buffer, the badge, the words, the message info and `Running`
  simp only [↓reduceIte]
  obtain ⟨x', hk', hwx⟩ := J2.buf ct hctT
  rw [hky] at hk'; cases hk'
  refine WP.spec_bind (lookup_buf_full s2 σy hXZ.rel.2.1.1 hXZ.rel.2.1.2.1 htcb hky hOKb true) ?_
  rintro bf ⟨hw0, hwp⟩
  have hbm : ∀ q, Endp.ipcBufOf true xy = some q → Endp.BufMap Z.B bf q := fun q hq =>
    hBCy ct hctT xy true q hky hq bf (hwp hwx q hq)
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s2 ct _ 0#u64) ?_
  rintro s3 rfl
  rw [← Endp.regIdx_badge]
  set xb := Notif.setReg xy Fl4Spec.badge_register 0 with hxb
  set σb := Notif.updK σy ct.bv (.tcb xb) with hσb
  have hkb : σb.kheap ct.bv = some (.tcb xb) := by simp [hσb, Notif.updK]
  have hksb : σb.kheap p.bv = some (.tcb xs) := by simp [hσb, Notif.updK, hne, hks]
  have hXb := badge_wr_irel J2.ip hXy hctT hky 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V3, J3⟩ := J2.regWrJ hctT hky Fl4Spec.badge_register 0#u64 hXb
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J3
  have J0 : JAtZ (L := L) arI AR (Z.mv Z.G V3) H Cs Ac2 Lst2 D2
      (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) a (MrS σb ct.bv xb (Endp.ipcBufOf true xy) []) := by
    rw [MrS_nil hkb]; exact J3
  have hOK3 := J3.xferH.1
  have hWOK : ∀ q, Endp.ipcBufOf true xy = some q → ∀ i : U64, i.val < 128 →
      BufWordOK H σb (fl4BufA bf i) := fun q hq i hi =>
    J3.bufWord hOK3 htcb hkb hq i.val hi (by rw [fl4BufA_bv, hwp hwx q hq])
  have hks3 : L.ksb (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) = L.ksb s2 := L.ksb_wr _ _ _
  have hlenR := rrOf_length xs n
  have hfr : ∀ q, Endp.ipcBufOf true xy = some q → ∀ z ∈ Endp.mrPairs (rrOf xs n),
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σy :=
    fun q hq z hz => ⟨Endp.bufAddr_aligned hXZ.fin.1.2.ep (hbm q hq) z.1,
      buf_frame_of_ok hOKb hky hq z.1 (mrPairs_lt hz)⟩
  refine WP.spec_bind (rrJ_loop0 J0 hctT hne hpT hksb n) ?_
  rintro ⟨s4, i⟩ ⟨hiv, ⟨V4, J4⟩, hk4, hc4⟩
  simp only at hiv J4 hk4 hc4
  try simp only [uncurry_apply_pair]
  have fin : ∀ (s5 : S) (len : U64),
      JAtZ (L := L) arI AR (Z.mv Z.G V4) H Cs Ac2 Lst2 D2 s5 a
        (MrS σb ct.bv xb (Endp.ipcBufOf true xy) (rrOf xs n)) →
      len.val = mrLen (Endp.ipcBufOf true xy) (rrOf xs n).length →
      (do
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
        let s6 ← msg.set_msg_info st s5 ct mi
        let s7 ← sched.set_thread_state st s6 ct sched.TS_RUNNING
        ok (s7, a)) ⦃ r => L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ rr σy',
        (.ok rr, σy') ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk true don (.invokeTCB (.readRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
        ∃ z ∈ (specTail true ct.bv rr σy').1, RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
    intro s5 len J5 hl
    refine WP.spec_mono (J5.rrTailJ hctT hcury hky hrs
      (by rw [hlenR]; unfold Fl4Spec.msgMaxLength; omega) hfr len hl
      (by rw [hl]; cases Endp.ipcBufOf true xy <;> simp [mrLen, hlenR] <;> omega)) ?_
    rintro r ⟨hne5, z, hz, hRT, hJT⟩
    exact ⟨hne5, rrOf xs n, σy, hmem, z, hz, hRT, hJT⟩
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  by_cases hb : bf = 0#u64
  · -- no buffer: the message registers only
    have hbn : Endp.ipcBufOf true xy = none := hw0.1 hb
    have hbb : (bf != 0#u64) = false := by simp [hb]
    simp only [hbb, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (rr_loopGR n s4 _ (fun _ _ => rfl)) ?_
    rintro ⟨s5, k⟩ hk5
    obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk5).1.symm, (Prod.mk.inj hk5).2⟩
    try simp only [uncurry_apply_pair]
    simp only [lift, bind_ok]
    refine fin s4 _ ?_ ?_
    · rw [hbn] at J4 ⊢
      by_cases hn4 : n.val ≤ 4
      · rw [hiv, show min n.val 4 = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at J4; exact J4
      · rw [hiv, show min n.val 4 = 4 by omega] at J4
        simp only [MrS] at J4 ⊢
        rw [← List.take_append_drop 4 (rrOf xs n), Endp.mrStateN_append_ge _ _ _ _ _ (by simp [hlenR]; omega)]
        exact J4
    · rw [hbn, hlenR]
      simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · -- a buffer
    obtain ⟨q, hq⟩ : ∃ q, Endp.ipcBufOf true xy = some q := by
      cases h : Endp.ipcBufOf true xy with
      | none => exact absurd (hw0.2 h) hb
      | some q => exact ⟨q, rfl⟩
    have hbm' := hbm q hq
    have hWq := hWOK q hq
    have hbb : (bf != 0#u64) = true := by simp [hb]
    simp only [hbb, ↓reduceIte]
    rw [hq] at J4
    have hBP3 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s4 σb :=
      hBPy.mono (hk4.trans hks3) (fun r y n hr => by
        by_cases e : r = ct.bv
        · subst e; rw [hkb] at hr; cases hr
        · simpa [hσb, Notif.updK, e] using hr)
    by_cases hin : i < n
    · -- past `MR3`: the frame registers into the buffer
      rw [if_pos hin]
      have hin' : i.val < n.val := (P1.gt_iff_val).1 hin
      have hi4 : i.val = 4 := by omega
      have hi18 : i < tcb.N_FRAME := (P1.gt_iff_val).2 (by rw [hf]; omega)
      rw [if_pos hi18]
      refine WP.spec_bind (rrJ_loop1 (Z := (Z.mv Z.G V3).mv Z.G V4) hkb q bf hbm' hWq hne hpT hksb n i (by omega) (by omega) hBP3 J4) ?_
      rintro ⟨s5, i1⟩ ⟨hi1, J5, hk5, hc5⟩
      simp only at hi1 J5 hk5 hc5
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (rr_loopGR n s5 _ (fun _ _ => rfl)) ?_
      rintro ⟨s6, k⟩ hk6
      obtain ⟨rfl, rfl⟩ : s5 = s6 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk6).1.symm, (Prod.mk.inj hk6).2⟩
      try simp only [uncurry_apply_pair]
      try simp only [hbb, ↓reduceIte]
      have hk0 : (0#u64 : U64) < tcb.N_GP := (P1.gt_iff_val).2 (by rw [hg]; decide)
      rw [if_pos hk0]
      obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := 0#u64) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
      rw [h2e, bind_ok]
      have hi2 : i2.val = 18 := by rw [← hf]; simpa using h2v
      by_cases h18 : i2 < n
      · rw [if_pos h18]
        have hn18 : 18 < n.val := by have := (P1.gt_iff_val).1 h18; omega
        rw [show i1.val = 18 by omega] at J5
        have hBP5 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s5 σb := hBP3.mono hk5 (fun _ _ _ h => h)
        refine WP.spec_bind (rrJ_loopGB (Z := (Z.mv Z.G V3).mv Z.G V4) hkb q bf hbm' hWq hne hpT hksb n hn18 hBP5 J5 _ (fun _ _ => rfl)) ?_
        rintro ⟨s7, k1⟩ ⟨hk1, J7, hk7, hc7⟩
        simp only at hk1 J7 hk7 hc7
        try simp only [uncurry_apply_pair]
        simp only [lift, bind_ok]
        refine fin s7 _ ?_ ?_
        · rw [hq]; rw [show 18 + k1.val = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at J7
          exact J7
        · rw [hq, hlenR]
          simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      · rw [if_neg h18]
        have hn18 : n.val ≤ 18 := by have := (P1.gt_iff_val).not.1 h18; omega
        simp only [lift, bind_ok]
        refine fin s5 _ ?_ ?_
        · rw [hq]; rw [show i1.val = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at J5
          exact J5
        · rw [hq, hlenR]
          simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · -- up to `MR3`
      rw [if_neg hin]
      have hn4 : n.val ≤ 4 := by have := (P1.gt_iff_val).not.1 hin; omega
      refine WP.spec_bind (rr_loopGR n s4 _ (fun _ _ => rfl)) ?_
      rintro ⟨s5, k⟩ hk5
      obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk5).1.symm, (Prod.mk.inj hk5).2⟩
      try simp only [uncurry_apply_pair]
      try simp only [hbb, ↓reduceIte]
      have hk0 : (0#u64 : U64) < tcb.N_GP := (P1.gt_iff_val).2 (by rw [hg]; decide)
      rw [if_pos hk0]
      obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := 0#u64) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
      rw [h2e, bind_ok]
      have hi2 : i2.val = 18 := by rw [← hf]; simpa using h2v
      have h18 : ¬ i2 < n := fun h => by have := (P1.gt_iff_val).1 h; omega
      rw [if_neg h18]
      simp only [lift, bind_ok]
      refine fin s4 _ ?_ ?_
      · rw [hq]; rw [show i.val = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at J4
        exact J4
      · rw [hq, hlenR]
        simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

end

end

end Fl4Proofs.P3
