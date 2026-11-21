/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **`B` across the fault writes**
(spec side only). `send_fault_ipc t` writes the fault while `t` is exempt
(`t ∈ E`: active or in a fault state) and in no notification queue (`t ∈ K`),
then `send_ipc` ends the exemption; `t` leaves `L`. With no handler
(`handle_no_fault`), `t` becomes Inactive. `handle_timeout`'s handler check
fails only if the handler slot holds no endpoint, then nothing is written and
`t ∈ L` ends the exemption.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L E K : List ObjRef} {C : ObjRef → Prop}

theorem mem_filter_ne {t u : ObjRef} : u ∈ L.filter (· ≠ t) → u ∈ L ∧ u ≠ t := by
  intro h; simpa using h

/-- The fault write of `send_fault_ipc`. -/
theorem b_setFault (t : ObjRef) (f : Fault) (htE : t ∈ E) (htK : t ∈ K) :
    HK (B L E K C) (B (L.filter (· ≠ t)) E K C)
      (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some f }) t) := by
  intro σ hσ y hy
  have hσ' : B (L.filter (· ≠ t)) E K C σ := b_mono hσ (fun u hu => (mem_filter_ne hu).1) (fun _ h => h) id
  obtain ⟨hb1, hb2, hb3⟩ := hσ'
  have hq : ∀ u, queued y.2 u → queued σ u :=
    fun u hu => queued_of_opg (fg_threadSet (F := fq1) (fun tcb => { tcb with tcbFault := some f }) t (fun _ h => h) σ (opg_queued hb1.2) y hy) hu
  have hft : ∀ x : Tcb, (fqX (L.filter (· ≠ t)) E).R t x.tcbFault x.tcbState →
      (fqX (L.filter (· ≠ t)) E).R t (some f) x.tcbState := by
    intro x hR
    refine ⟨fun _ => ?_, fun h => absurd rfl (mem_filter_ne h).2, hR.2.2⟩
    rcases hR.2.2 htE with h | h
    · exact Or.inr ⟨htE, h⟩
    · exact Or.inl h
  refine ⟨fg_threadSet (F := fqX _ E) (S := Set.univ) (fun tcb => { tcb with tcbFault := some f }) t hft σ hb1 y hy, fun u hu => ?_,
    fun u hu => ⟨fun hq' => (hb3 u hu).1 (hq u hq'), ?_⟩⟩
  · have hu0 := hq u hu
    have hne : t ≠ u := fun e => (hb3 t htK).1 (e ▸ hu0)
    exact fun z hz => (fg_threadSet (F := fqT u) (S := Set.univ) (fun tcb => { tcb with tcbFault := some f }) t (fun x hR e => absurd e hne) σ
      (opg_fqT hb1.2 (hb2 u hu0)) y hy).1 u _ hz rfl
  · exact fun z hz => (fg_threadSet (F := fqN u) (S := Set.univ) (fun tcb => { tcb with tcbFault := some f }) t (fun x hR => hR) σ
      (opg_fqN hb1.2 (hb3 u hu).2) y hy).1 u _ hz rfl

/-- `handle_fault t`: `t` exempt (active or in a fault state) and in no queue. -/
theorem b_handleFault (t : ObjRef) (ex : Fault) (htK : t ∈ K) :
    HK (B L (t :: E) K C) (B (L.filter (· ≠ t)) E K C) (handleFault (Z := Unit) t ex) := by
  unfold handleFault
  refine hk_pure_bind (hk_bind (hk_of_ik (by b_auto)) fun cap => hk_bind (hk_of_ik (by b_auto)) fun sc => ?_)
  intro σ hσ y ⟨y1, h1, hy⟩
  unfold sendFaultIpc at h1
  split at h1
  · obtain ⟨y2, h2, h1⟩ := h1
    have hb2 := b_setFault (L := L) (E := t :: E) (K := K) (C := C) t ex (by simp) htK σ hσ y2 h2
    obtain ⟨y3, h3, h1⟩ := h1
    have hb3 := b_sendIpc true false _ _ _ _ t _ htK (Or.inl rfl) y2.2 hb2 y3 h3
    rw [Set.mem_singleton_iff.1 h1] at hy
    exact (by b_auto : BK (L.filter (· ≠ t)) E K C
      (NonDet.unless (true = true) (handleNoFault (Z := Unit) t) >>= fun _ => (pure () : NonDet (State Unit) Unit)))
      _ hb3 y hy
  · rw [Set.mem_singleton_iff.1 h1] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    simp only [NonDet.unless, Bool.false_eq_true, ↓reduceIte, handleNoFault] at h2
    have hb2 := b_sts_drop (L := L) (E := E) (K := K) (C := C) t .inactive trivial (fun _ h => h)
      (Or.inl fun h => h) σ hσ y2 h2
    rw [Set.mem_singleton_iff.1 hy]
    exact b_mono hb2 (fun u hu => (mem_filter_ne hu).1) (fun _ h => h) id
  · exact h1.elim

/-- `handle_timeout t`: `t` exempt, without fault (`t ∈ L`) and in no queue. -/
theorem b_handleTimeout (t : ObjRef) (ex : Fault) (htL : t ∈ L) (htK : t ∈ K) :
    HK (B L (t :: E) K C) (B (L.filter (· ≠ t)) E K C) (handleTimeout (Z := Unit) t ex) := by
  unfold handleTimeout
  refine hk_bind (hk_of_ik (by b_auto)) fun v => hk_bind (hk_of_ik (ik_assert _)) fun _ =>
    hk_pure_bind (hk_bind (hk_of_ik (by b_auto)) fun cap => ?_)
  intro σ hσ y ⟨y1, h1, hy⟩
  unfold sendFaultIpc at h1
  split at h1
  · obtain ⟨y2, h2, h1⟩ := h1
    have hb2 := b_setFault (L := L) (E := t :: E) (K := K) (C := C) t ex (by simp) htK σ hσ y2 h2
    obtain ⟨y3, h3, h1⟩ := h1
    have hb3 := b_sendIpc true false _ _ _ _ t _ htK (Or.inl rfl) y2.2 hb2 y3 h3
    rw [Set.mem_singleton_iff.1 h1] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact hb3
  · rw [Set.mem_singleton_iff.1 h1] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact b_mono (hk_dropL (ik_pure ()) htL σ hσ ((), σ) (Set.mem_singleton _)) (fun u hu => (mem_filter_ne hu).1)
      (fun _ h => h) id
  · exact h1.elim

/-- **NQB at boot**: the initial heap has no notification. -/
theorem boot_nqb : NQB (initASt (Z := Unit)) := by
  rintro t ⟨n, x, hn, -⟩
  simp only [initASt, initKheap, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)

/-- **The bundle at boot.** -/
theorem boot_B : B [] [] [] (fun _ => True) (initASt (Z := Unit)) :=
  (b_nil_iff _).2 ⟨boot_faultTcbsS, boot_nqb⟩

end

end Fl4Proofs.P3.SInv
