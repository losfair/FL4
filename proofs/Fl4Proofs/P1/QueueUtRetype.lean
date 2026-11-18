/-
P1: **the untyped family's retype** (`UtPlace.retype`, the premise
`decGap_untyped` leaves) from P1's `ResetP1Step` (`resetP1Step_holds`) and
`RetypeP1Step` (`retypeP1Step`), given P3's facts about the retype as one
structure (`UtRetypeP3`): the set tuple is the heap's, admissible heaps,
core `0`, and what `untyped.retype` does — an optional reset (`ResetOK`:
the untyped cap and its region droppable) and the creation (`CreateOK`: the
window, its region droppable, the write frame, the window's initial words,
the debug links and the window's placement) over the heap after the reset
(`utHeap`).
-/
import Fl4Proofs.P1.QueueRetypeTcb
import Fl4Proofs.P1.QueueDecUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The heap after the retype's optional reset of the untyped `Untyped p sb _ _`. -/
noncomputable def utHeap (H : Heap) (reset : Bool) (p sb : U64) : Heap :=
  if reset then H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) else H

/-- The set tuple of a heap. -/
def PSets.ofHeap (H : Heap) : PSets := ⟨H.tcbs, H.omega, H, H.frame, H.replies, H.scs, H.ntfns, H.scBits⟩

/-- **The reset's facts** (P3's `valid_untyped`, `valid_cap` and the dead
objects of the region): the slot holds the untyped cap, placed and sized,
with the objects meeting its region droppable and the region off the nodes. -/
def ResetOK (st : machine.Store S) [L : LawfulStore st] (H : Heap) (Cs : Set U64) (s : S) (slot p sb fi : U64)
    (dev : Bool) : Prop :=
  obj.Slot.cap st slot s = ok (.Untyped p sb fi dev) ∧ p.val % 2 ^ sb.val = 0 ∧ p.val + 2 ^ sb.val ≤ 2 ^ 64 ∧
    DropOK st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s ∧ RegionOffNodes st Cs s p.val (p.val + 2 ^ sb.val) ∧
    UtSize fi sb

/-- **The creation's facts** (P3's `RetPostN`/`RetFrame`, over the heap `H1`
after the reset, from the creation's start `sR` to its end `s'`): the
window `[A, A + w * k)` of slots `k` within the region `[lo, hi)`, the
objects meeting the region droppable, the region off the nodes, the writes
cap-slot, region and debug-list words, the region's words after, the debug
links after, and the window's placement. -/
def CreateOK (st : machine.Store S) [L : LawfulStore st] (H1 : Heap) (Cs : Set U64) (sR s' : S) : Prop :=
  ∃ lo hi A k w n us : Nat, lo ≤ A ∧ A + w * k ≤ hi ∧ (∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k) ∧
    DropOK st H1 (RegionD H1 lo hi) Cs sR ∧ RegionOffNodes st Cs sR lo hi ∧
    WritesIn st sR s' (fun b => CapW (Heap.tcbs H1) (Heap.omega H1) (Heap.frame H1) b ∨ (lo ≤ b.val ∧ b.val < hi) ∨
      DbgW st (Heap.tcbs H1) Cs sR b) ∧
    WinInit st s' lo hi A k w n us ∧ DbgLinksOK st H1 Cs s' lo hi A k w n ∧ WinPlaced A k w n us

/-- **P3's facts for the untyped family's retype** (`UtPlace.retype`): the
set tuple is the heap's; any well-formed heap without an object at null is
admissible; core `0` is a core; and, from P3's state fact `UtOk` at the
decode's start (e.g. `valid_untyped` of the joint state), after the restart,
the reset's facts (when it resets) and what `untyped.retype` does: the reset's
error, or the creation (`CreateOK`) after the reset's success or without a
reset. -/
structure UtRetypeP3 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64)
    (UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop) : Prop where
  shared : SharedUtPlace st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk
  sets : T = H.tcbs ∧ Ω = H.omega ∧ Sg = H.frame ∧ Rp = H.replies ∧ Scs = H.scs ∧ Nt = H.ntfns ∧ Z = H.scBits
  adm : ∀ H' : Heap, HeapOK H' → H' 0#u64 = none → Adm (PSets.ofHeap H')
  core0 : 0#u64 ∈ Cs
  run : ∀ (Ac : Set U64) (s0 s : S) (a : A) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slot ptr sb fi : U64) (dev reset : Bool) (aligned nt us dest off win : U64),
    UtOk s0 slot (.Untyped ptr sb fi dev) extra →
    sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s0 (.Untyped ptr sb fi dev) extra → CapSlotW T Ω Sg slot →
    UtArgs st s0 extra slot ptr sb fi dev reset aligned nt us dest off win →
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    (reset = true → ResetOK st H Cs s slot ptr sb fi dev) ∧
    untyped.retype st ar s a slot reset aligned nt us dest off win dev ⦃ r s' a' =>
      (reset = true ∧ r ≠ .Ok () ∧ untyped.reset_untyped st ar s a slot = ok (r, s', a')) ∨
      (r = .Ok () ∧ ∃ sR, ((reset = false ∧ sR = s) ∨
          (reset = true ∧ ∃ a1, untyped.reset_untyped st ar s a slot = ok (.Ok (), sR, a1))) ∧
        CreateOK st (utHeap H reset ptr sb) Cs sR s') ⦄

/-- **The heap after a retype is well formed**, from the heap before, the
retype's shape and the window. -/
theorem retype_heapOK {H1 H' : Heap} {lo hi A k w n us : Nat} (hH : HeapOK H1) (h0 : H1 0#u64 = none)
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k)
    (hwp : WinPlaced A k w n us)
    (hsh : ∀ q kd, H' q = some kd → (H1 q = some kd ∧ ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits)) ∨
      (NewAt A k w q ∧ newKind n us = some kd)) :
    HeapOK H' ∧ H' 0#u64 = none := by
  obtain ⟨hal, hfit, hA0, hus⟩ := hwp
  have pos : ∀ {q : U64}, NewAt A k w q → ∃ j, j < w ∧ q.val = A + j * k ∧ A + (j + 1) * k ≤ A + w * k := by
    rintro q ⟨j, hj, hq⟩; exact ⟨j, hj, hq, Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _⟩
  have nAl : ∀ {q : U64} {kd}, NewAt A k w q → newKind n us = some kd → q.val % 2 ^ kd.bits = 0 := by
    intro q kd hq hk
    obtain ⟨j, -, hv, -⟩ := pos hq
    obtain ⟨hA, hkk⟩ := hal kd hk
    rw [hv, Nat.add_mod, Nat.mul_mod, hkk, hA]; simp
  have nFit : ∀ {q : U64} {kd}, NewAt A k w q → newKind n us = some kd → q.val + 2 ^ kd.bits ≤ 2 ^ 64 := by
    intro q kd hq hk
    obtain ⟨j, -, hv, hj⟩ := pos hq
    have := hbits kd hk
    rw [Nat.add_mul, Nat.one_mul] at hj; omega
  refine ⟨⟨fun p kd hp => ?_, fun p kd hp => ?_, fun p kd hp => ?_, fun p z hp => ?_,
    fun p kd q kd' hp hq hne => ?_⟩, ?_⟩
  · rcases hsh p kd hp with ⟨h1, -⟩ | ⟨hn, hk⟩
    · exact hH.align p kd h1
    · exact nAl hn hk
  · rcases hsh p kd hp with ⟨h1, -⟩ | ⟨hn, hk⟩
    · exact hH.fits p kd h1
    · exact nFit hn hk
  · rcases hsh p kd hp with ⟨h1, -⟩ | ⟨hn, hk⟩
    · exact hH.lt64 p kd h1
    · obtain ⟨j, hj, hv, hjk⟩ := pos hn
      have hb := hbits kd hk
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have hlt : 2 ^ kd.bits < 2 ^ 64 := by omega
      exact (Nat.pow_lt_pow_iff_right (by decide)).1 hlt
  · rcases hsh p (.sc z) hp with ⟨h1, -⟩ | ⟨-, hk⟩
    · exact hH.scmin p z h1
    · have : n = 5 ∧ z = us := by
        unfold newKind at hk; split_ifs at hk <;> simp_all
      obtain ⟨h5, rfl⟩ := this
      exact hus h5
  · have hp1 := Nat.one_le_two_pow (n := kd.bits)
    have hq1 := Nat.one_le_two_pow (n := kd'.bits)
    rcases hsh p kd hp with ⟨h1, m1⟩ | ⟨n1, k1⟩ <;> rcases hsh q kd' hq with ⟨h2, m2⟩ | ⟨n2, k2⟩
    · exact hH.disj p kd q kd' h1 h2 hne
    · obtain ⟨j, -, hv, hjk⟩ := pos n2
      have := hbits kd' k2
      rw [Nat.add_mul, Nat.one_mul] at hjk
      unfold MeetsR at m1; omega
    · obtain ⟨j, -, hv, hjk⟩ := pos n1
      have := hbits kd k1
      rw [Nat.add_mul, Nat.one_mul] at hjk
      unfold MeetsR at m2; omega
    · rw [k1] at k2; cases k2
      obtain ⟨j, -, hv, -⟩ := pos n1
      obtain ⟨j', -, hv', -⟩ := pos n2
      have hb := hbits kd k1
      have hjj : j ≠ j' := fun e => hne (UScalar.eq_of_val_eq (by rw [hv, hv', e]))
      rcases Nat.lt_or_gt_of_ne hjj with h | h
      · have : (j + 1) * k ≤ j' * k := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      · have : (j' + 1) * k ≤ j * k := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul, Nat.one_mul] at this; omega
  · cases e : H' 0#u64 with
    | none => rfl
    | some kd =>
      rcases hsh _ kd e with ⟨h1, -⟩ | ⟨⟨j, -, hv⟩, -⟩
      · rw [h0] at h1; cases h1
      · simp at hv; omega

theorem spec_exists_u {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem HeapOK.drop0 {H : Heap} {D : U64 → Prop} (h0 : H 0#u64 = none) : H.drop D 0#u64 = none := by
  unfold Heap.drop; split_ifs <;> simp [h0]

open Classical in
/-- The reset's heap is `H` with the region's objects dropped. -/
theorem reset_heap_eq {H H' : Heap} {p sb : U64}
    (h : ∀ q, H' q = if MeetsR p.val (p.val + 2 ^ sb.val) q.val (q.val + 2 ^ ((H q).elim 0 HKind.bits))
      then none else H q) : H' = H.drop (RegionD H p.val (p.val + 2 ^ sb.val)) := by
  funext q; rw [h q]; rfl

variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`UtPlace` from P3's facts** (`UtRetypeP3`), P1's reset and retype. -/
theorem UtRetypeP3.utPlace {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    {UtOk : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop} (P : UtRetypeP3 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk) :
    UtPlace st ar Adm T Cs Ω H Sg Rp Scs Nt Z U UtOk := by
  obtain ⟨eT, eΩ, eSg, eRp, eScs, eNt, eZ⟩ := P.sets
  subst eT eΩ eSg eRp eScs eNt eZ
  refine ⟨P.shared,
    fun Ac s0 s a extra slot ptr sb fi dev reset aligned nt us dest off win hOk hrs D hslot hU hC => ?_⟩
  obtain ⟨hR, hrun⟩ := P.run Ac s0 s a extra slot ptr sb fi dev reset aligned nt us dest off win hOk hrs D hslot hU hC
  obtain ⟨hc0, Ac1, hX, ec, ecs, esc, na, nb, -⟩ := hC
  have hb := hX.blk
  have hcurT : L.curW s ∈ H.tcbs := hX.1.choose_spec.choose_spec.curT
  -- the reset, when it runs
  have RS : reset = true → ∀ (rr : core.result.Result Unit error.Exc × S × A),
      untyped.reset_untyped st ar s a slot = ok rr →
      ∃ Ac2, BlkOK st (utHeap H true ptr sb).tcbs Cs (utHeap H true ptr sb).omega (utHeap H true ptr sb)
          (utHeap H true ptr sb).frame (utHeap H true ptr sb).replies (utHeap H true ptr sb).scs
          (utHeap H true ptr sb).ntfns (utHeap H true ptr sb).scBits Ac2 rr.2.1 ∧
        ResetKeeps st s rr.2.1 ∧ HeapOK (utHeap H true ptr sb) ∧ utHeap H true ptr sb 0#u64 = none ∧
        utHeap H true ptr sb (L.curW s) = some .tcb := by
    intro hr rr heq
    obtain ⟨hcap, hpal, hfit, hdrop, hnode, hfi⟩ := hR hr
    obtain ⟨r', hr', H2, Ac2, hb2, hsh, -, hK⟩ :=
      spec_exists_u (resetP1Step_holds (st := st) hA H Cs Ac1 s a slot ptr sb fi dev hb hcap hslot hpal hfit hdrop
        hnode hfi)
    rw [heq] at hr'; obtain rfl : rr = r' := by simpa using hr'
    have e2 : H2 = utHeap H true ptr sb := by rw [reset_heap_eq hsh]; simp [utHeap]
    subst e2
    refine ⟨Ac2, hb2, hK, ?_, ?_, ?_⟩
    · simp only [utHeap, if_true]; exact hdrop.heap.drop
    · simp only [utHeap, if_true]; exact HeapOK.drop0 hdrop.h0
    · simp only [utHeap, if_true]; rw [Heap.drop_of_not hdrop.cur]; exact hcurT
  refine WP.spec_mono hrun fun ⟨r, s', a'⟩ hpost => ?_
  rcases hpost with ⟨hr, hne, heq⟩ | ⟨hok, sR, hsR, hcr⟩
  · -- the reset's error
    obtain ⟨Ac2, hb2, hK, hok2, h02, hcur2⟩ := RS hr _ heq
    refine ⟨PSets.ofHeap (utHeap H true ptr sb), P.adm _ hok2 h02, by rw [← ec]; exact hcur2, ?_⟩
    obtain ⟨k1, k2, k3, k4, k5⟩ := hK
    refine Cur0.postOf hc0 hb2.bxi (k1.trans ec) (k2.trans ecs) ?_ fun y hy => ?_
    · rw [← ec] at esc ⊢; rw [k4]; exact esc
    · rw [k3]; simp only [utHeap, if_true] at hy; exact na y (Heap.mem_tcbs_drop.1 hy).1
  · -- the creation
    have base : ∃ Ac2, BlkOK st (utHeap H reset ptr sb).tcbs Cs (utHeap H reset ptr sb).omega (utHeap H reset ptr sb)
        (utHeap H reset ptr sb).frame (utHeap H reset ptr sb).replies (utHeap H reset ptr sb).scs
        (utHeap H reset ptr sb).ntfns (utHeap H reset ptr sb).scBits Ac2 sR ∧
        L.curW sR = L.curW s ∧ utHeap H reset ptr sb (L.curW s) = some .tcb := by
      rcases hsR with ⟨rfl, rfl⟩ | ⟨rfl, a1, heq⟩
      · have e : utHeap H false ptr sb = H := by simp [utHeap]
        rw [e]; exact ⟨Ac1, hb, rfl, hcurT⟩
      · obtain ⟨Ac2, hb2, hK, -, -, hcur2⟩ := RS rfl _ heq
        exact ⟨Ac2, hb2, hK.1, hcur2⟩
    obtain ⟨Ac2, hb2, ecR, hc1⟩ := base
    obtain ⟨lo, hi, A, k, w, n, us', hlo, hhi, hbits, hdrop', hnode', hw, hwin, hdbg, hwp⟩ := hcr
    obtain ⟨H', Ac', hb', hkeep, hsh, -, -⟩ :=
      (retypeP1Step : RetypeP1Step st sR s' (utHeap H reset ptr sb) Cs Ac2 lo hi A k w n us') hb2 hlo hhi hbits
        hdrop' hnode' hw hwin hdbg hwp P.core0
    obtain ⟨hok', h0'⟩ := retype_heapOK hdrop'.heap hdrop'.h0 hlo hhi hbits hwp hsh
    have hcurK : H' (L.curW s0) = some .tcb := by
      have nm := hdrop'.cur
      rw [ecR] at nm
      simp only [RegionD, hc1, Option.elim] at nm
      rw [← ec]; exact hkeep _ _ hc1 nm
    exact ⟨PSets.ofHeap H', P.adm H' hok' h0', hcurK, Ac', hb'.bxi, fun h => by rw [hok] at h; cases h⟩

end

end Fl4Proofs.P1
