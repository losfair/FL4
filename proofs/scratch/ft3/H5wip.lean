/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **`B` across the budget charge**
(spec side only): `charge_budget` raises a timeout fault on the current thread
`c` only after reading it schedulable, so runnable: it has no fault then
(FaultTcbsS, or `c ∈ L` when exempt), joins `L` and `E` (`fqA c`: active, in
a fault state or runningVM, kept by the frame), and `end_timeslice` excludes
runningVM before `handle_timeout`. `check_budget(_restart)`: the post keeps `L`
when the result is `true` (no charge).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L E K : List ObjRef}

/-- At `c`: active, in a fault state, or runningVM. -/
def fqA (c : ObjRef) : FQ where
  R p _ s := p = c → activeSt s ∨ faultTcbSt s ∨ s = .runningVM
  clr _ _ _ h := h
  st _ _ _ _ _ := Or.inr (Or.inl trivial)
  dflt _ _ := Or.inr (Or.inl trivial)

theorem sched_runnable {σ : State Unit} {t : ObjRef} (h : schedulable (Z := Unit) t σ = true) :
    ∀ x, σ.kheap t = some (.tcb x) → runnable x.tcbState = true := by
  intro x hx
  unfold schedulable at h
  simp only [decide_eq_true_eq] at h
  have h1 := h.1
  simp only [optPred, optMapSome, optMap, tcbsOfKh, hx, tcbOf] at h1
  exact h1

theorem pa_gf {α : Type} {c : ObjRef} {m : NonDet (State Unit) α} (h : GF (· = c) m) {σ : State Unit}
    (hσ : B L E K (· = c) σ ∧ OPG (fqA c) Set.univ (· = c) σ) {y : α × State Unit} (hy : y ∈ (m σ).1) :
    B L E K (· = c) y.2 ∧ OPG (fqA c) Set.univ (· = c) y.2 :=
  ⟨b_of_gf h σ hσ.1 y hy, h (fqA c) _ σ hσ.2 y hy⟩

theorem mem_gets {β : Type} {g : State Unit → β} {σ : State Unit} {y : β × State Unit}
    (h : y ∈ (NonDet.gets g σ).1) : y = (g σ, σ) := Set.mem_singleton_iff.1 h

theorem b_endTimeslice (cto : Bool) (c : ObjRef) (hcL : c ∈ L) (hcK : c ∈ K) :
    HK (fun σ => B L E K (· = c) σ ∧ OPG (fqA c) Set.univ (· = c) σ) (B (L.filter (· ≠ c)) E K (· = c))
      (endTimeslice (Z := Unit) cto) := by
  intro σ hσ y hy
  unfold endTimeslice at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have p2 := pa_gf (fun _ _ => by fg_auto) hσ h2
  obtain ⟨y3, h3, hy⟩ := hy
  rw [mem_gets h3] at hy
  have hc : y2.2.curThread = c := p2.1.1.2
  obtain ⟨y4, h4, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h4
  simp only [hc] at hx hy
  obtain ⟨y5, h5, hy⟩ := hy
  have hfin : ∀ {σ'}, B L E K (· = c) σ' → B (L.filter (· ≠ c)) E K (· = c) σ' :=
    fun h => b_mono h (fun u hu => (mem_filter_ne hu).1) (fun _ h => h) id
  by_cases hv : x.tcbState = .runningVM
  · simp only [hv, ↓reduceIte] at h5
    rw [Set.mem_singleton_iff.1 h5] at hy
    split at hy
    · rename_i hcond; simp at hcond
    · exact hfin (b_of_gf (fun _ _ => by fg_auto) _ p2.1 y hy)
  · rw [if_neg hv] at h5
    have hE : B L (c :: E) K (· = c) y2.2 := b_addE p2.1 fun z hz => by
      rw [hx] at hz; cases hz
      rcases p2.2.1 c _ hx rfl with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hv
    have hb5 := b_of_gf (fun _ _ => by fg_auto) _ hE y5 h5
    split at hy
    · obtain ⟨y6, h6, hy⟩ := hy
      have hb6 := b_of_gf (fun _ _ => by fg_auto) _ hb5 y6 h6
      exact b_handleTimeout c _ hcL hcK y6.2 hb6 y hy
    · have hF := b_of_gf (fun _ _ => by fg_auto) _ hb5 y hy
      exact hfin (b_dropE hF fun z hz => Or.inl ((hF.1.1 c _ hz).2.1 hcL))

theorem b_chargeBudget (n : Ticks) (cto : Bool) (c : ObjRef) (hcK : c ∈ K) (hcEL : c ∈ E → c ∈ L) :
    HK (B L E K (· = c)) (B (L.filter (· ≠ c)) E K (· = c)) (chargeBudget (Z := Unit) n cto) := by
  intro σ hσ y hy
  unfold chargeBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 := b_of_gf (fun _ _ => by fg_auto) _ hσ y3 h3
  obtain ⟨y4, h4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h4] at hy
  have hb4 : B L E K (· = c) { y3.2 with consumedTime := 0 } := hb3
  obtain ⟨y5, h5, hy⟩ := hy
  rw [mem_gets h5] at hy
  obtain ⟨y6, h6, hy⟩ := hy
  rw [mem_gets h6] at hy
  have hc : ({ y3.2 with consumedTime := 0 } : State Unit).curThread = c := hb4.1.2
  simp only [hc] at hy
  have hfin : ∀ {σ'}, B L E K (· = c) σ' → B (L.filter (· ≠ c)) E K (· = c) σ' :=
    fun h => b_mono h (fun u hu => (mem_filter_ne hu).1) (fun _ h => h) id
  unfold NonDet.when at hy
  split at hy
  · rename_i hs
    have hrun := sched_runnable (by simpa using hs)
    have hnf : ∀ z, ({ y3.2 with consumedTime := 0 } : State Unit).kheap c = some (.tcb z) →
        z.tcbFault = none := by
      intro z hz
      by_cases hcE : c ∈ E
      · exact (hb4.1.1 c _ hz).2.1 (hcEL hcE)
      · by_contra hf
        rcases (hb4.1.1 c _ hz).1 hf with h | ⟨h, -⟩
        · have := hrun z hz; revert h this; cases z.tcbState <;> simp [faultTcbSt, runnable]
        · exact hcE h
    have hA : OPG (fqA c) Set.univ (· = c) ({ y3.2 with consumedTime := 0 } : State Unit) := by
      refine ⟨fun p o hp => ?_, hc⟩
      cases o with
      | tcb z =>
        intro e; subst e
        have := hrun z hp; revert this; cases z.tcbState <;> simp [activeSt, faultTcbSt, runnable]
      | notification _ => exact fun _ _ => Set.mem_univ _
      | _ => trivial
    obtain ⟨y7, h7, hy⟩ := hy
    have hb7 := b_endTimeslice (L := c :: L) (E := E) (K := K) cto c (by simp) hcK _ ⟨b_cons hb4 hnf, hA⟩ y7 h7
    have hb7' : B (L.filter (· ≠ c)) E K (· = c) y7.2 :=
      b_mono hb7 (fun u hu => by have := mem_filter_ne hu; simp_all) (fun _ h => h) id
    exact (by b_auto : BK (L.filter (· ≠ c)) E K (· = c) (rescheduleRequired (Z := Unit) >>= fun _ =>
      NonDet.modify fun s : State Unit => { s with reprogramTimer := true })) _ hb7' y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hfin hb4

end

end Fl4Proofs.P3.SInv
