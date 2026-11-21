import Fl4Spec.CSpace
namespace Fl4Spec
theorem capMove_orig_src' (c : Cap) (src dest : CslotPtr) {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (capMove (Z := Unit) c src dest σ).1) : x.2.isOriginalCap src = false := by
  unfold capMove at hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  obtain ⟨_, _, hx⟩ := hx
  unfold setOriginal at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  simp
end Fl4Spec
