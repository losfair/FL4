/-
P3 (DESIGN.md §9): **the MDB invariants along an `MdbStep`**
(`MdbStep.inv`): `Vs.FrameInv`, `UtInv` and `NoOverlap` are kept by every
constructor, from per-primitive lemmas (VsFrameInv's for the frame
invariant, UntypedUtOps / UntypedReset / UntypedUtInv / VsSubMdb /
VsMakePoolMdb's for `UtInv`, and `NoOverlap.*` here), and so by any step.
-/
import Fl4Proofs.P3.MdbStep
import Fl4Proofs.P3.VsFrameInv
import Fl4Proofs.P3.VsMakePoolMdb
import Fl4Proofs.P3.UntypedUtOps
import Fl4Proofs.P3.UntypedReset
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## Helpers -/

theorem renG_refl (G : MdbGhost) : renG G (Equiv.refl U64) = G := by
  cases G with
  | mk ch par =>
    unfold renG Mdb.conjPar
    simp only [Equiv.coe_refl, List.map_id_fun, id_eq, Equiv.refl_symm, Option.map_id_fun]

theorem CapAlike.utEq {c' c : capability.Cap} (h : CapAlike c' c) : UtEq c' c := ⟨h.base, h.top, h.phys, h.ut⟩

/-- A cap naming an object is physical, at its pointer. -/
theorem refs_phys {w : capability.Cap} {q : U64} (h : q.bv ∈ Fl4Spec.objRefs (absCap w)) :
    physF w = true ∧ ptrF w = q := by
  cases w <;> simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef] at h <;>
    refine ⟨ok_inj (phys_eq _).symm, ?_⟩ <;> have e := P1.eq_of_bv h <;>
    first | exact (ok_inj (ptr_eq _).symm).trans e.symm | exact (ok_inj (ptr_eq _).symm).trans e

theorem refs_base {w : capability.Cap} {q : U64} (h : q.bv ∈ Fl4Spec.objRefs (absCap w)) :
    physF w = true ∧ baseF w = q.val := by
  obtain ⟨h1, h2⟩ := refs_phys h; exact ⟨h1, by unfold baseF; rw [h2]⟩

/-- A large RAM frame's window is its range. -/
theorem large_window {p r a va : U64} {m ep : Bool}
    (hreg : baseF (.Frame p .Large r false m ep a va) ≤ topF (.Frame p .Large r false m ep a va)) :
    baseF (.Frame p .Large r false m ep a va) = p.val ∧ topF (.Frame p .Large r false m ep a va) = p.val + 2 ^ 21 - 1 :=
  ⟨(Vs.frame_range p .Large r false m a va ep).1, Vs.large_top hreg⟩

/-! ## `UtInv` -/

section
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost}

theorem UtInv.of_alike (hM : MdbLinks th mem G) (hU : UtInv mem G)
    (ha : ∀ z ∈ G.chains.flatten, UtEq (capV mem' z) (capV mem z)) : UtInv mem' G := by
  have := UtInv.rename hM hU (Equiv.refl U64) (fun z hz => ha z hz)
  rwa [renG_refl] at this

theorem UtInv.of_caps (hM : MdbLinks th mem G) (hU : UtInv mem G)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : UtInv mem' G :=
  hU.of_alike hM (fun z hz => by rw [hc z hz]; exact UtEq.refl _)

/-- **Raising an untyped cap's free index keeps `UtInv`.** -/
theorem UtInv.raise_fi (hM : MdbLinks th mem G) (hU : UtInv mem G) {x p sb fi f : U64} {dev : Bool}
    (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb fi dev)
    (hcx' : capV mem' x = .Untyped p sb f dev) (hf : f.val ≤ 2 ^ sb.val) (hle : fi.val ≤ f.val)
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) : UtInv mem' G := by
  have hsh : shape (capV mem' x) = shape (capV mem x) := by rw [hcx, hcx']; rfl
  obtain ⟨e1, e2, e3⟩ := range_of_shape hsh
  have rb : ∀ z ∈ G.chains.flatten, baseF (capV mem' z) = baseF (capV mem z) ∧ topF (capV mem' z) = topF (capV mem z) ∧
      physF (capV mem' z) = physF (capV mem z) ∧ isUt (capV mem' z) = isUt (capV mem z) := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; exact ⟨e1, e2, e3, isUt_of_shape hsh⟩
    · rw [hcap z hz hzx]; exact ⟨rfl, rfl, rfl, rfl⟩
  -- each untyped cap of the new state, read back
  have back : ∀ z ∈ G.chains.flatten, ∀ q b i d, capV mem' z = .Untyped q b i d →
      ∃ i0, capV mem z = .Untyped q b i0 d ∧ i0.val ≤ i.val ∧ (z ≠ x → i0 = i) := by
    intro z hz q b i d hc
    by_cases hzx : z = x
    · have hc' := hc; rw [hzx, hcx'] at hc'
      injection hc' with hq hb hi hdd
      subst hq hb hi hdd
      exact ⟨fi, by rw [hzx, hcx], hle, fun h => absurd hzx h⟩
    · exact ⟨i, by rw [← hcap z hz hzx]; exact hc, le_refl _, fun _ => rfl⟩
  refine ⟨fun z hz hp => ?_, fun z hz q b i d hc y hd => ?_, fun z hz q b i d hc y hy hp => ?_,
    fun z hz y hy hzy q b i i' d d' hcz hcy => ?_, fun z hz q b i d hc => ?_,
    fun z hz q b i d hc y hy hyz hp hd => ?_⟩
  · obtain ⟨r1, r2, r3, -⟩ := rb z hz
    rw [r3] at hp; rw [r1, r2]; exact hU.reg z hz hp
  · obtain ⟨i0, hc0, hle0, -⟩ := back z hz q b i d hc
    obtain ⟨r1, r2, r3, -⟩ := rb y (desc_mem hM hd).1
    obtain ⟨g1, g2, g3⟩ := hU.inc z hz q b i0 d hc0 y hd
    rw [r1, r2, r3]; exact ⟨g1, g2, by omega⟩
  · obtain ⟨i0, hc0, hle0, -⟩ := back z hz q b i d hc
    obtain ⟨r1, r2, r3, r4⟩ := rb y hy
    obtain ⟨s1, s2, -, -⟩ := rb z hz
    rw [r3] at hp
    rcases hU.noov z hz q b i0 d hc0 y hy hp with g | ⟨g1, g2⟩
    · left; unfold DisjR at g ⊢; rw [r1, r2]; omega
    · right; rw [r4]; refine ⟨g1, ?_⟩
      unfold Within at g2 ⊢; rw [r1, r2, s1, s2]; exact g2
  · obtain ⟨i0, hc0, hle0, -⟩ := back z hz q b i d hcz
    obtain ⟨i1, hc1, hle1, -⟩ := back y hy q b i' d' hcy
    rcases hU.excl z hz y hy hzy q b i0 i1 d d' hc0 hc1 with g | g
    · left; omega
    · right; omega
  · by_cases hzx : z = x
    · have hc' := hc; rw [hzx, hcx'] at hc'
      injection hc' with hq hb hi hdd
      rw [← hi, ← hb]; exact hf
    · rw [hcap z hz hzx] at hc; exact hU.fib z hz _ _ _ _ hc
  · obtain ⟨i0, hc0, -, -⟩ := back z hz q b i d hc
    obtain ⟨r1, r2, r3, -⟩ := rb y hy
    obtain ⟨s1, s2, -, -⟩ := rb z hz
    rw [r3] at hp
    exact hU.drange z hz q b i0 d hc0 y hy hyz hp (by unfold Disj at hd ⊢; rw [r1, r2, s1, s2] at hd; exact hd)

/-- **Inserting a non-physical cap after a non-physical cap keeps `UtInv`.** -/
theorem UtInv.nonphys (hM : MdbLinks th mem G) (hU : UtInv mem G) {src dest : U64} {c : capability.Cap}
    (b : Bool) (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten)
    (hsp : physF (capV mem src) = false) (hcd : capV mem' dest = c) (hcp : physF c = false)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : UtInv mem' (insG G src dest b) := by
  have hsd : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have memI : ∀ z, z ∈ (insG G src dest b).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
    fun z => mem_flatten_ins hsrc
  have desc := Vs.desc_insG hM hdest hsd b
  have hcu : isUt c = false := by
    cases hu : isUt c
    · rfl
    · rw [physF_of_ut hu] at hcp; cases hcp
  -- a new slot's cap is physical only if old
  have old : ∀ z ∈ (insG G src dest b).chains.flatten, physF (capV mem' z) = true →
      z ∈ G.chains.flatten ∧ capV mem' z = capV mem z := by
    intro z hz hp
    rcases (memI z).1 hz with rfl | hz0
    · rw [hcd, hcp] at hp; cases hp
    · exact ⟨hz0, hc z hz0⟩
  have oldU : ∀ z ∈ (insG G src dest b).chains.flatten, ∀ q sb fi d, capV mem' z = .Untyped q sb fi d →
      z ∈ G.chains.flatten ∧ capV mem z = .Untyped q sb fi d := by
    intro z hz q sb fi d hcz
    obtain ⟨h1, h2⟩ := old z hz (by rw [hcz]; exact physF_ut _ _ _ _)
    exact ⟨h1, by rw [← h2]; exact hcz⟩
  -- no untyped cap is above `src`
  have hnu : ∀ x, Mdb.Desc G.par src x → ∀ q sb fi d, capV mem x ≠ .Untyped q sb fi d := by
    intro x hd q sb fi d hx
    have := (hU.inc x (desc_mem hM hd).2 q sb fi d hx src hd).1
    rw [hsp] at this; cases this
  refine ⟨fun z hz hp => ?_, fun z hz q sb fi d hcz y hd => ?_, fun z hz q sb fi d hcz y hy hp => ?_,
    fun z hz y hy hzy q sb fi fi' d d' hcz hcy => ?_, fun z hz q sb fi d hcz => ?_,
    fun z hz q sb fi d hcz y hy hyz hp hd => ?_⟩
  · obtain ⟨h1, h2⟩ := old z hz hp; rw [h2] at hp ⊢; exact hU.reg z h1 hp
  · obtain ⟨hz0, hc0⟩ := oldU z hz q sb fi d hcz
    rcases (desc y z).1 hd with hd0 | ⟨rfl, (⟨-, rfl⟩ | hd0)⟩
    · rw [hc y (desc_mem hM hd0).1]; exact hU.inc z hz0 q sb fi d hc0 y hd0
    · rw [hc0, physF_ut] at hsp; exact absurd hsp (by decide)
    · exact absurd hc0 (hnu z hd0 q sb fi d)
  · obtain ⟨hz0, hc0⟩ := oldU z hz q sb fi d hcz
    obtain ⟨hy0, hcy⟩ := old y hy hp
    rw [hcy] at hp ⊢; rw [hc z hz0]; exact hU.noov z hz0 q sb fi d hc0 y hy0 hp
  · obtain ⟨hz0, hc0⟩ := oldU z hz q sb fi d hcz
    obtain ⟨hy0, hc1⟩ := oldU y hy q sb fi' d' hcy
    exact hU.excl z hz0 y hy0 hzy q sb fi fi' d d' hc0 hc1
  · obtain ⟨hz0, hc0⟩ := oldU z hz q sb fi d hcz; exact hU.fib z hz0 q sb fi d hc0
  · obtain ⟨hz0, hc0⟩ := oldU z hz q sb fi d hcz
    obtain ⟨hy0, hcy⟩ := old y hy hp
    have hzc := hc z hz0
    rw [hcy] at hp hd; rw [hzc] at hd
    rcases hU.drange z hz0 q sb fi d hc0 y hy0 hyz hp hd with e | e
    · exact Or.inl ((desc y z).2 (Or.inl e))
    · exact Or.inr ((desc z y).2 (Or.inl e))

end


/-! ## `Vs.FrameInv` -/

/-- Two caps alike for the frame invariant. -/
def FrA (c' c : capability.Cap) : Prop :=
  Fl4Spec.objRefs (absCap c') = Fl4Spec.objRefs (absCap c) ∧ isFrame c' = isFrame c ∧
    ∀ p r m ep a va, c' = .Frame p .Large r false m ep a va → ∃ r0 m0 ep0 a0 v0, c = .Frame p .Large r0 false m0 ep0 a0 v0

theorem CapAlike.frA {c' c : capability.Cap} (h : CapAlike c' c) : FrA c' c := ⟨h.refs, h.frame, h.large⟩

theorem FrA.refl (c : capability.Cap) : FrA c c := ⟨rfl, rfl, fun p r m ep a va h => ⟨r, m, ep, a, va, h⟩⟩

theorem FrA.ut {p sb fi f : U64} {d : Bool} : FrA (.Untyped p sb f d) (.Untyped p sb fi d) :=
  ⟨rfl, rfl, fun _ _ _ _ _ _ h => by cases h⟩

theorem not_ut_of_refs {w : capability.Cap} {q : U64} (h : q.bv ∈ Fl4Spec.objRefs (absCap w)) : isUt w = false := by
  cases hw : isUt w
  · rfl
  · obtain ⟨a, b, c, d, rfl⟩ := isUt_iff.1 hw; simp [absCap, Fl4Spec.objRefs] at h

section
variable {mem mem' : U64 → U64} {G : MdbGhost}

theorem Vs.FrameInv.of_fr (h : Vs.FrameInv mem G) (hk : ∀ z ∈ G.chains.flatten, FrA (capV mem' z) (capV mem z)) :
    Vs.FrameInv mem' G := by
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (hk x hx).2.2 p r m ep a va hcx
  rw [(hk w hw).1] at hq
  obtain ⟨hf, hch⟩ := h x hx p r0 m0 ep0 a0 v0 hcx0 w hw q h1 h2 hq
  exact ⟨by rw [(hk w hw).2.1]; exact hf, hch⟩

theorem Vs.FrameInv.rename' (h : Vs.FrameInv mem G) (e : U64 ≃ U64)
    (hk : ∀ z ∈ G.chains.flatten, FrA (capV mem' (e z)) (capV mem z)) : Vs.FrameInv mem' (renG G e) := by
  have hmem : ∀ z, z ∈ (renG G e).chains.flatten ↔ e.symm z ∈ G.chains.flatten := fun z => mem_renG e z
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  have hx0 := (hmem x).1 hx
  have hw0 := (hmem w).1 hw
  have lx := hk _ hx0; rw [Equiv.apply_symm_apply] at lx
  have lw := hk _ hw0; rw [Equiv.apply_symm_apply] at lw
  obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := lx.2.2 p r m ep a va hcx
  rw [lw.1] at hq
  obtain ⟨hf, ch, hch, hxc, hwc⟩ := h _ hx0 p r0 m0 ep0 a0 v0 hcx0 _ hw0 q h1 h2 hq
  refine ⟨by rw [lw.2.1]; exact hf, ch.map e, List.mem_map.2 ⟨ch, hch, rfl⟩, ?_, ?_⟩
  · exact List.mem_map.2 ⟨_, hxc, by simp⟩
  · exact List.mem_map.2 ⟨_, hwc, by simp⟩

end

section
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost}

theorem Vs.FrameInv.insertC {src dest : U64} {c c1 : capability.Cap} (h : InsCtx th mem mem' G src dest c c1)
    (hc1 : c1 = (fullF (capV mem src) c).getD (capV mem src))
    (hutc : isUt (capV mem src) = true → c = capV mem src) (hok : okey c = okey (capV mem src)) (b : Bool)
    (hF : Vs.FrameInv mem G) : Vs.FrameInv mem' (insG G src dest b) := by
  have ha := CapAlike.of_shape h.hsh hok hutc
  refine hF.insert_copy h.hsrc h.hdest b h.cd ⟨by rw [h.cs]; exact h.hsh1, by rw [h.cs, hc1]; exact okey_fullF _ _,
    by rw [h.cs]; exact h.hbd1⟩ (fun z hz hzs => by rw [h.hcap z (h.sl hz), if_neg (h.dne hz), if_neg hzs])
    (fun q hq => by rw [← ha.refs]; exact hq) ha.frame ha.large

theorem Vs.FrameInv.nonphys (hF : Vs.FrameInv mem G) {src dest : U64} {c : capability.Cap}
    (b : Bool) (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten)
    (hcd : capV mem' dest = c) (hcp : physF c = false) (hrefs : Fl4Spec.objRefs (absCap c) = ∅)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : Vs.FrameInv mem' (insG G src dest b) := by
  refine hF.insert_fresh hsrc hdest b hcd (by rw [hc src hsrc]; exact MdbLike.refl _) (fun z hz _ => hc z hz)
    (fun p r mm ep a va e => ?_) (fun x _ p r m ep a va _ q _ _ hq => by rw [hrefs] at hq; exact hq)
  have := not_frame_of_phys hcp; rw [e] at this; cases this

theorem Vs.FrameInv.pool (hM : MdbLinks th mem G) (hI : MdbInv mem G) (hU : UtInv mem G) (hF : Vs.FrameInv mem G)
    {x val p sb f q b : U64} {d : Bool} (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb f d)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x) (hval : val ∉ G.chains.flatten)
    (hcf : capV mem' val = .AsidPool q b) (hbA : baseF (.AsidPool q b) = baseF (capV mem x))
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : Vs.FrameInv mem' (insG G x val true) := by
  refine hF.insert_fresh hx hval true hcf (by rw [hc x hx]; exact MdbLike.refl _) (fun z hz _ => hc z hz)
    (fun _ _ _ _ _ _ e => by cases e) (fun y hy p0 r m ep a va hcy q0 h1 h2 hq => ?_)
  have hq0 : q0 = q := by
    simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef] at hq; exact P1.eq_of_bv hq
  subst hq0
  have hbq : baseF (.AsidPool q0 b) = q0.val := by unfold baseF; rw [ptrF_ap]
  have hry := hU.reg y hy (by rw [hcy]; exact physF_frame _ _ _ _ _ _ _ _)
  rw [hcy] at hry
  obtain ⟨y1, y2⟩ := large_window hry
  have hrx := hU.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
  have hyx : y ≠ x := by intro e; rw [e, hcx] at hcy; cases hcy
  have hnd' : ¬ Disj (capV mem y) (capV mem x) := by
    unfold Disj; rw [hcy, y1, y2, ← hbA, hbq]; rw [← hbA, hbq] at hrx; omega
  rcases hU.drange x hx p sb f d hcx y hy hyx (by rw [hcy]; exact physF_frame _ _ _ _ _ _ _ _) hnd' with e | e
  · exact hnd y e
  · have := hI.anc_ut e (by rw [hcx]; rfl); rw [hcy] at this; cases this

theorem Vs.FrameInv.alias' (hV : Vs.FrameInv mem G) {src dest : U64} (b : Bool) (hsrc : src ∈ G.chains.flatten)
    (hdest : dest ∉ G.chains.flatten) {ptr rt fa fv q0 vm : U64} {mm : Bool}
    (hsC : capV mem src = .Frame ptr .Large rt false mm false fa fv)
    (hcd : capV mem' dest = .Frame q0 .Small vm false false false 0#u64 0#u64)
    (hq1 : ptr.val ≤ q0.val) (hq2 : q0.val < ptr.val + 2 ^ 21)
    (halg : ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va → p.val % 2 ^ 21 = 0)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : Vs.FrameInv mem' (insG G src dest b) :=
  hV.insert_alias hsrc hdest b hsC hcd (hc src hsrc) (fun z hz _ => hc z hz) hq1 hq2 halg

end

/-- `j * k ≤ l * k < j * k + k` only for `l = j`. -/
theorem idx_eq_of_range {j l k : Nat} (hk : 1 ≤ k) (h1 : j * k ≤ l * k) (h2 : l * k < j * k + k) : l = j := by
  have a : j ≤ l := Nat.le_of_mul_le_mul_right h1 (by omega)
  have b : l < j + 1 := Nat.lt_of_mul_lt_mul_right (a := k) (by rw [Nat.add_mul, Nat.one_mul]; exact h2)
  omega

namespace RetypeDelta
variable {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hU : UtInv mem0 G0)
include h hU

/-- An old slot's cap after the retype: the source's untyped cap with its
new free index, or unchanged. -/
theorem oldF {x : U64} (hx : x ∈ G0.chains.flatten) : FrA (capV memf x) (capV mem0 x) := by
  rw [h.F2b x hx]
  by_cases hxs : x = src
  · subst hxs; rw [h.hcs1, h.hcs]; exact FrA.ut
  · rw [h.hc1 x hx hxs]; exact FrA.refl _

/-- An old physical non-untyped cap misses the source's free part. -/
theorem old_out {y : U64} (hy : y ∈ G0.chains.flatten) (hp : physF (capV mem0 y) = true)
    (hu : isUt (capV mem0 y) = false) : DisjR (capV mem0 y) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
  rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy hp with g | ⟨g, -⟩
  · exact g
  · rw [hu] at g; cases g

theorem new_rng {j : Nat} (hj : j < w) : p.val + fi.val ≤ baseF (cj j) ∧ topF (cj j) < p.val + 2 ^ sb.val ∧
    baseF (cj j) ≤ topF (cj j) := by
  have e1 := h.cbase j hj; have e2 := h.ctop j hj
  have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at this
  have := h.hA; have := h.hAw; have := h.hk
  refine ⟨by omega, by omega, by omega⟩

/-- **Retype keeps the frame invariant**, its chains growing. -/
theorem frameInv (hF : Vs.FrameInv mem0 G0) (hch : ∀ ch ∈ G0.chains, ∃ ch' ∈ Gf.chains, ∀ z ∈ ch, z ∈ ch') :
    Vs.FrameInv memf Gf := by
  intro x hx pp r m ep a va hcx w' hw q h1 h2 hq
  rcases h.F1 x hx with hx0 | ⟨j, hj, rfl⟩
  · obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (h.oldF hU hx0).2.2 pp r m ep a va hcx
    have hxp : physF (capV mem0 x) = true := by rw [hcx0]; exact physF_frame _ _ _ _ _ _ _ _
    have hrx := hU.reg x hx0 hxp
    rw [hcx0] at hrx
    obtain ⟨x1, x2⟩ := large_window hrx
    have hdx := h.old_out hU hx0 hxp (by rw [hcx0]; rfl)
    unfold DisjR at hdx
    rw [hcx0, x1, x2] at hdx
    rcases h.F1 w' hw with hw0 | ⟨l, hl, rfl⟩
    · have lw := h.oldF hU hw0
      rw [lw.1] at hq
      obtain ⟨hf, ch, hch0, hxc, hwc⟩ := hF x hx0 pp r0 m0 ep0 a0 v0 hcx0 w' hw0 q h1 h2 hq
      obtain ⟨ch', hch', hsub⟩ := hch ch hch0
      exact ⟨by rw [lw.2.1]; exact hf, ch', hch', hsub x hxc, hsub w' hwc⟩
    · rw [h.F2a l hl] at hq
      obtain ⟨-, hb⟩ := refs_base hq
      obtain ⟨n1, n2, n3⟩ := h.new_rng hU hl
      omega
  · rw [h.F2a j hj] at hcx
    obtain ⟨n1, n2, n3⟩ := h.new_rng hU hj
    have e1 := h.cbase j hj; have e2 := h.ctop j hj
    rw [hcx] at n3 e1 e2
    obtain ⟨x1, x2⟩ := large_window n3
    rcases h.F1 w' hw with hw0 | ⟨l, hl, rfl⟩
    · rw [(h.oldF hU hw0).1] at hq
      obtain ⟨hp, hb⟩ := refs_base hq
      have hdw := h.old_out hU hw0 hp (not_ut_of_refs hq)
      have hrw := hU.reg w' hw0 hp
      rw [hcx] at n1 n2
      unfold DisjR at hdw; omega
    · rw [h.F2a l hl] at hq
      obtain ⟨-, hb⟩ := refs_base hq
      have e3 := h.cbase l hl
      have hlj : l = j := idx_eq_of_range h.hk (by omega) (by have := h.hk; omega)
      subst hlj
      obtain ⟨ch, hch0, hxc⟩ := List.mem_flatten.1 hx
      exact ⟨by rw [h.F2a l hl, hcx]; rfl, ch, hch0, hxc, hxc⟩

end RetypeDelta


/-! ## `NoOverlap` -/

/-- The clause of `NoOverlap` for a pair of caps. -/
def NoC (cx cy : capability.Cap) (ry : Bool) : Prop :=
  Disj cy cx ∨ (isUt cy = true ∧ Within cx cy) ∨
    (isFrame cx = true ∧ isFrame cy = true ∧ (ry = false ∨ Within cx cy)) ∨
    (isFrame cx = false ∧ isFrame cy = false ∧ baseF cy = baseF cx ∧ topF cy = topF cx)

theorem noOverlap_iff {mem : U64 → U64} {G : MdbGhost} : NoOverlap mem G ↔
    ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, physF (capV mem x) = true → physF (capV mem y) = true →
      isUt (capV mem x) = false → NoC (capV mem x) (capV mem y) (revOf mem y) := Iff.rfl

/-- Two caps alike for `NoOverlap`. -/
structure NoA (c' c : capability.Cap) : Prop where
  base : baseF c' = baseF c
  top : topF c' = topF c
  phys : physF c' = physF c
  ut : isUt c' = isUt c
  frame : isFrame c' = isFrame c

theorem NoA.refl (c : capability.Cap) : NoA c c := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem CapAlike.noA {c' c : capability.Cap} (h : CapAlike c' c) : NoA c' c := ⟨h.base, h.top, h.phys, h.isUt', h.frame⟩
theorem NoA.of_shape {c' c : capability.Cap} (h : shape c' = shape c) : NoA c' c := by
  obtain ⟨h1, h2, h3⟩ := range_of_shape h
  exact ⟨h1, h2, h3, isUt_of_shape h, by cases c' <;> cases c <;> simp_all [shape, isFrame]⟩

theorem NoC.congr {cx cx' cy cy' : capability.Cap} {ry ry' : Bool} (hx : NoA cx' cx) (hy : NoA cy' cy)
    (hr : isFrame cy' = true → ry' = true → ry = true) (h : NoC cx cy ry) : NoC cx' cy' ry' := by
  rw [hy.frame] at hr
  unfold NoC Disj Within at *
  rw [hx.base, hx.top, hx.frame, hy.base, hy.top, hy.ut, hy.frame]
  rcases h with h | h | ⟨h1, h2, h3 | h3⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨h1, h2, Or.inl ?_⟩))
    cases e : ry' with
    | false => rfl
    | true => rw [hr h2 e] at h3; cases h3
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, Or.inr h3⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem NoC.self (c : capability.Cap) (r : Bool) : NoC c c r := by
  cases hf : isFrame c
  · exact Or.inr (Or.inr (Or.inr ⟨hf, hf, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hf, hf, Or.inr ⟨le_refl _, le_refl _⟩⟩))

section
variable {mem mem' : U64 → U64} {G G' : MdbGhost}

/-- **`NoOverlap` along a view**: each physical slot of the new MDB alike
an old one, revocable only if that is. -/
theorem NoOverlap.of_view (hN : NoOverlap mem G)
    (hv : ∀ z ∈ G'.chains.flatten, physF (capV mem' z) = true → ∃ z0 ∈ G.chains.flatten,
      NoA (capV mem' z) (capV mem z0) ∧
        (isFrame (capV mem' z) = true → revOf mem' z = true → revOf mem z0 = true)) : NoOverlap mem' G' := by
  intro x hx y hy hpx hpy hux
  obtain ⟨x0, hx0, ax, -⟩ := hv x hx hpx
  obtain ⟨y0, hy0, ay, ry⟩ := hv y hy hpy
  rw [ax.phys] at hpx; rw [ay.phys] at hpy; rw [ax.ut] at hux
  exact NoC.congr ax ay ry (hN x0 hx0 y0 hy0 hpx hpy hux)

/-- **`NoOverlap` gives `DeriveSubframe`'s `hno`** (for the physical caps). -/
theorem NoOverlap.hno (hN : NoOverlap mem G) {src : U64} (hsrc : src ∈ G.chains.flatten)
    (hsF : isFrame (capV mem src) = true) :
    ∀ x ∈ G.chains.flatten, physF (capV mem x) = true →
      Disj (capV mem x) (capV mem src) ∨ (isFrame (capV mem x) = true ∧ revOf mem x = false) ∨
        Within (capV mem src) (capV mem x) := by
  intro x hx hp
  rcases hN src hsrc x hx (Vs.physF_frame' hsF) hp (Vs.isUt_frame' hsF) with h | ⟨-, h⟩ | ⟨-, h1, h2 | h2⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr h2)
  · rw [hsF] at h; cases h

end

section
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost}

theorem NoOverlap.keep (hN : NoOverlap mem G) (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
    (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : NoOverlap mem' G :=
  hN.of_view (fun z hz _ => ⟨z, hz, by rw [hc z hz]; exact NoA.refl _, fun _ => by rw [hr z hz]; exact id⟩)

theorem NoOverlap.recap (hN : NoOverlap mem G) (x0 : U64) (ha : NoA (capV mem' x0) (capV mem x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z)
    (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : NoOverlap mem' G := by
  refine hN.of_view (fun z hz _ => ⟨z, hz, ?_, fun _ => by rw [hr z hz]; exact id⟩)
  by_cases e : z = x0
  · subst e; exact ha
  · rw [hc z hz e]; exact NoA.refl _

theorem NoOverlap.remove (hM : MdbLinks th mem G) (hN : NoOverlap mem G) (x : U64)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z)
    (hr : ∀ z ∈ G.chains.flatten, z ≠ x → revOf mem' z = revOf mem z) : NoOverlap mem' (remG G x) := by
  refine hN.of_view (fun z hz _ => ?_)
  obtain ⟨hz0, hzx⟩ := (Mdb.mem_removeChains hM.tree.nodup).1 hz
  exact ⟨z, hz0, by rw [hc z hz0 hzx]; exact NoA.refl _, fun _ => by rw [hr z hz0 hzx]; exact id⟩

theorem NoOverlap.rename (hN : NoOverlap mem G) (e : U64 ≃ U64)
    (ha : ∀ z ∈ G.chains.flatten, NoA (capV mem' (e z)) (capV mem z) ∧ revOf mem' (e z) = revOf mem z) :
    NoOverlap mem' (renG G e) := by
  refine hN.of_view (fun z hz _ => ?_)
  have hz0 := (mem_renG e z).1 hz
  obtain ⟨a1, a2⟩ := ha _ hz0
  rw [Equiv.apply_symm_apply] at a1 a2
  exact ⟨_, hz0, a1, fun _ => by rw [a2]; exact id⟩

theorem NoOverlap.insertC {src dest : U64} {c c1 : capability.Cap} (h : InsCtx th mem mem' G src dest c c1)
    (b : Bool) (hN : NoOverlap mem G) : NoOverlap mem' (insG G src dest b) := by
  refine hN.of_view (fun z hz _ => ?_)
  rcases (h.memI b z).1 hz with rfl | hz0
  · refine ⟨src, h.hsrc, by rw [h.cd]; exact NoA.of_shape h.hsh, fun hf hr => ?_⟩
    rw [h.rd, revF_frame (by rw [h.cd] at hf; exact hf)] at hr; cases hr
  · refine ⟨z, hz0, ?_, fun _ => by rw [h.rz hz0]; exact id⟩
    by_cases hzs : z = src
    · subst hzs; rw [h.cs]; exact NoA.of_shape h.hsh1
    · rw [h.hcap z (h.sl hz0), if_neg (h.dne hz0), if_neg hzs]; exact NoA.refl _

end


section
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost}

theorem NoOverlap.nonphys (hN : NoOverlap mem G) {src dest : U64} {c : capability.Cap}
    (b : Bool) (hsrc : src ∈ G.chains.flatten) (hcd : capV mem' dest = c) (hcp : physF c = false)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
    (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : NoOverlap mem' (insG G src dest b) := by
  refine hN.of_view (fun z hz hp => ?_)
  rcases (mem_flatten_ins hsrc).1 hz with rfl | hz0
  · rw [hcd, hcp] at hp; cases hp
  · exact ⟨z, hz0, by rw [hc z hz0]; exact NoA.refl _, fun _ => by rw [hr z hz0]; exact id⟩

/-- **The alias insertion keeps `NoOverlap`.** -/
theorem NoOverlap.alias (hN : NoOverlap mem G) {src dest : U64} (b : Bool) (hsrc : src ∈ G.chains.flatten)
    (hsF : isFrame (capV mem src) = true) (hcdF : isFrame (capV mem' dest) = true)
    (hcin : Within (capV mem' dest) (capV mem src))
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) (hrd : revOf mem' dest = false)
    (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : NoOverlap mem' (insG G src dest b) := by
  have hsp := Vs.physF_frame' hsF
  have hsu := Vs.isUt_frame' hsF
  intro x hx y hy hpx hpy hux
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0 <;> rcases (mem_flatten_ins hsrc).1 hy with rfl | hy0
  · exact NoC.self _ _
  · rw [hc y hy0] at hpy ⊢; rw [hr y hy0]
    unfold Within at hcin
    rcases hN src hsrc y hy0 hsp hpy hsu with g | ⟨g1, g2⟩ | ⟨-, g1, g2 | g2⟩ | ⟨g, -⟩
    · left; unfold Disj at g ⊢; omega
    · right; left; refine ⟨g1, ?_⟩; unfold Within at g2 ⊢; omega
    · right; right; left; exact ⟨hcdF, g1, Or.inl g2⟩
    · right; right; left; refine ⟨hcdF, g1, Or.inr ?_⟩; unfold Within at g2 ⊢; omega
    · rw [hsF] at g; cases g
  · rw [hc x hx0] at hpx hux ⊢
    unfold Within at hcin
    rcases hN x hx0 src hsrc hpx hsp hux with g | ⟨g, -⟩ | ⟨g1, -, -⟩ | ⟨-, g, -⟩
    · left; unfold Disj at g ⊢; omega
    · rw [hsu] at g; cases g
    · right; right; left; exact ⟨g1, hcdF, Or.inl hrd⟩
    · rw [hsF] at g; cases g
  · rw [hc x hx0] at hpx hux ⊢; rw [hc y hy0] at hpy ⊢; rw [hr y hy0]
    exact hN x hx0 y hy0 hpx hpy hux

/-- **The pool insertion keeps `NoOverlap`.** -/
theorem NoOverlap.pool (hM : MdbLinks th mem G) (hI : MdbInv mem G) (hU : UtInv mem G) (hN : NoOverlap mem G)
    {x val p sb f q b : U64} {d : Bool} (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb f d)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x) (hcf : capV mem' val = .AsidPool q b)
    (hbA : baseF (.AsidPool q b) = baseF (capV mem x)) (htA : topF (.AsidPool q b) = topF (capV mem x))
    (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
    (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : NoOverlap mem' (insG G x val true) := by
  have hux : isUt (capV mem x) = true := by rw [hcx]; rfl
  -- an old physical cap meeting the untyped cap is it or an untyped ancestor containing it
  have meet : ∀ y ∈ G.chains.flatten, physF (capV mem y) = true → ¬ Disj (capV mem y) (capV mem x) →
      isUt (capV mem y) = true ∧ Within (capV mem x) (capV mem y) := by
    intro y hy hp hd
    by_cases hyx : y = x
    · subst hyx; exact ⟨hux, le_refl _, le_refl _⟩
    rcases hU.drange x hx p sb f d hcx y hy hyx hp hd with e | e
    · exact absurd e (hnd y)
    · have huy := hI.anc_ut e hux
      obtain ⟨p', sb', fi', d', hy'⟩ := isUt_iff.1 huy
      obtain ⟨-, g2, g3⟩ := hU.inc y hy p' sb' fi' d' hy' x e
      have hry := hU.reg y hy hp
      rw [hy'] at hry
      obtain ⟨y1, y2, -⟩ := ut_range (capV_ut_sb hy') hry
      have hfb := hU.fib y hy _ _ _ _ hy'
      refine ⟨huy, ?_⟩
      unfold Within; rw [hy', y1, y2]; omega
  intro z hz y hy hpz hpy huz
  rcases (mem_flatten_ins hx).1 hz with rfl | hz0 <;> rcases (mem_flatten_ins hx).1 hy with rfl | hy0
  · exact NoC.self _ _
  · rw [hc y hy0] at hpy ⊢; rw [hcf]
    by_cases hd : Disj (capV mem y) (capV mem x)
    · left; unfold Disj at hd ⊢; rw [hbA, htA]; exact hd
    · obtain ⟨g1, g2⟩ := meet y hy0 hpy hd
      right; left; refine ⟨g1, ?_⟩; unfold Within at g2 ⊢; rw [hbA, htA]; exact g2
  · rw [hc z hz0] at hpz huz ⊢; rw [hcf]
    left
    by_contra hd
    have hd' : ¬ Disj (capV mem z) (capV mem x) := by
      intro e; apply hd; unfold Disj at e ⊢; rw [hbA, htA]; omega
    rw [(meet z hz0 hpz hd').1] at huz; cases huz
  · rw [hc z hz0] at hpz huz ⊢; rw [hc y hy0] at hpy ⊢; rw [hr y hy0]
    exact hN z hz0 y hy0 hpz hpy huz

end

namespace RetypeDelta
variable {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
  (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hU : UtInv mem0 G0)
include h hU

theorem oldN {x : U64} (hx : x ∈ G0.chains.flatten) : NoA (capV memf x) (capV mem0 x) := by
  rw [h.F2b x hx]
  by_cases hxs : x = src
  · subst hxs; rw [h.hcs1, h.hcs]; exact NoA.of_shape rfl
  · rw [h.hc1 x hx hxs]; exact NoA.refl _

/-- **Retype keeps `NoOverlap`.** -/
theorem noOverlap (hN : NoOverlap mem0 G0) (hr : ∀ z ∈ G0.chains.flatten, revOf memf z = revOf mem0 z) :
    NoOverlap memf Gf := by
  obtain ⟨s1, s2, -⟩ := h.srcR hU
  have hpsrc : p.val + 2 ^ sb.val - 1 = topF (capV mem0 src) := by rw [h.hcs, s2]
  have hbsrc : p.val = baseF (capV mem0 src) := by rw [h.hcs, s1]
  have hfsb := h.hfi
  intro x hx y hy hpx hpy hux
  rcases h.F1 x hx with hx0 | ⟨j, hj, rfl⟩ <;> rcases h.F1 y hy with hy0 | ⟨l, hl, rfl⟩
  · have ax := h.oldN hU hx0; have ay := h.oldN hU hy0
    rw [ax.phys] at hpx; rw [ay.phys] at hpy; rw [ax.ut] at hux
    exact NoC.congr ax ay (fun _ e => by rw [hr y hy0] at e; exact e) (hN x hx0 y hy0 hpx hpy hux)
  · have ax := h.oldN hU hx0
    rw [ax.phys] at hpx; rw [ax.ut] at hux
    have hd := h.old_out hU hx0 hpx hux
    obtain ⟨n1, n2, n3⟩ := h.new_rng hU hl
    rw [h.F2a l hl]
    left; unfold Disj; unfold DisjR at hd; rw [ax.base, ax.top]; omega
  · rw [h.F2a j hj] at hux ⊢
    obtain ⟨n1, n2, n3⟩ := h.new_rng hU hj
    have ay := h.oldN hU hy0
    rw [ay.phys] at hpy
    unfold Disj Within; rw [ay.base, ay.top, ay.ut]
    cases huy : isUt (capV mem0 y)
    · have hd := h.old_out hU hy0 hpy huy
      unfold DisjR at hd; left; omega
    · by_cases hys : y = src
      · subst hys; right; left; refine ⟨rfl, ?_⟩; omega
      · rcases hU.noov src h.hsrc p sb fi dev h.hcs y hy0 hpy with g | ⟨-, g⟩
        · unfold DisjR at g; left; omega
        · unfold Within at g; right; left; refine ⟨rfl, ?_⟩; omega
  · rw [h.F2a j hj, h.F2a l hl]
    by_cases hjl : j = l
    · subst hjl; exact NoC.self _ _
    · left; unfold Disj; rcases h.cj_disj hU hl hj (Ne.symm hjl) with g | g
      · exact Or.inl g
      · exact Or.inr g

end RetypeDelta

/-! ## Along a step -/

/-- **The MDB invariants along an `MdbStep`.** -/
theorem MdbStep.inv {mem mem' : U64 → U64} {G G' : MdbGhost} (hS : MdbStep mem G mem' G') :
    Vs.FrameInv mem G → UtInv mem G → NoOverlap mem G →
      Vs.FrameInv mem' G' ∧ UtInv mem' G' ∧ NoOverlap mem' G' := by
  induction hS with
  | keep hM hc hr => exact fun hF hU hN => ⟨hF.of_caps hc, hU.of_caps hM hc, hN.keep hc hr⟩
  | recap hM x0 ha _ hc hr =>
    intro hF hU hN
    have hk : ∀ z ∈ _, CapAlike _ _ := fun z hz => by
      by_cases e : z = x0
      · subst e; exact ha
      · rw [hc z hz e]; exact CapAlike.refl _
    exact ⟨hF.of_fr (fun z hz => (hk z hz).frA), hU.of_alike hM (fun z hz => (hk z hz).utEq),
      hN.recap x0 ha.noA hc hr⟩
  | @setFi th m m' g hM hI x p sb fi f dev hx hcx hcx' hf hdir hc hr =>
    intro hF hU hN
    refine ⟨hF.of_fr (fun z hz => ?_), ?_, hN.recap _ (NoA.of_shape (by rw [hcx, hcx']; rfl)) hc hr⟩
    · by_cases e : z = x
      · subst e; rw [hcx, hcx']; exact FrA.ut
      · rw [hc z hz e]; exact FrA.refl _
    · rcases hdir with hle | hnd
      · exact hU.raise_fi hM hx hcx hcx' hf hle hc
      · exact hU.reset_fi hM hI hx hcx hnd hcx' hf hc
  | insert h hc1 hutc hok b hb _ =>
    intro hF hU hN
    exact ⟨hF.insertC h hc1 hutc hok b, h.utinv hU hc1 hutc b hb, hN.insertC h b⟩
  | nonphys hM b hsrc hdest hsp hcd hcp hrefs hc hr =>
    intro hF hU hN
    exact ⟨hF.nonphys b hsrc hdest hcd hcp hrefs hc, hU.nonphys hM b hsrc hdest hsp hcd hcp hc,
      hN.nonphys b hsrc hcd hcp hc hr⟩
  | remove hM x hc hr =>
    intro hF hU hN
    exact ⟨hF.remove hM x hc, hU.remove hM hc, hN.remove hM x hc hr⟩
  | rename hM e ha _ =>
    intro hF hU hN
    exact ⟨hF.rename' e (fun z hz => (ha z hz).1.frA), hU.rename hM e (fun z hz => (ha z hz).1.utEq),
      hN.rename e (fun z hz => ⟨(ha z hz).1.noA, (ha z hz).2⟩)⟩
  | @frameAlias th m m' g hM hI src dest b hsrc hdest ptr rt fa fv q0 vm mm hsC hcd hq1 hq2 hcin hcr halg hc hrd hr _ _ =>
    intro hF hU hN
    have hsF : isFrame (capV m src) = true := by rw [hsC]; rfl
    have hcF : isFrame (capV m' dest) = true := by rw [hcd]; rfl
    exact ⟨hF.alias' b hsrc hdest hsC hcd hq1 hq2 halg hc,
      Vs.utinv_alias hM hI hU b hsrc hsF hdest hcF hcin hcr rfl hc,
      hN.alias b hsrc hsF hcF hcin hc hrd hr⟩
  | pool hM hI hx hcx hf hnd hval hcf hbA htA hc hr _ =>
    intro hF hU hN
    exact ⟨hF.pool hM hI hU hx hcx hnd hval hcf hbA hc, Vs.utinv_pool hM hU hx hcx hf hnd hval hcf hbA htA hc,
      hN.pool hM hI hU hx hcx hnd hcf hbA htA hc hr⟩
  | retype h hI hch hr _ =>
    intro hF hU hN
    exact ⟨h.frameInv hU hF hch, h.utinv hU, h.noOverlap hU hN hr⟩
  | trans _ _ ih1 ih2 =>
    intro hF hU hN
    obtain ⟨a, b, c⟩ := ih1 hF hU hN
    exact ih2 a b c


/-- **The MDB invariants** carried by the top-level relation: the frame
invariant, `UtInv` and `NoOverlap`. -/
def MdbOK (mem : U64 → U64) (G : MdbGhost) : Prop := Vs.FrameInv mem G ∧ UtInv mem G ∧ NoOverlap mem G

theorem MdbStep.ok {mem mem' : U64 → U64} {G G' : MdbGhost} (h : MdbStep mem G mem' G') (hO : MdbOK mem G) :
    MdbOK mem' G' := h.inv hO.1 hO.2.1 hO.2.2

theorem MdbOK.of_same {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (hS : SlotsSame th m m') (hO : MdbOK m G) : MdbOK m' G := (MdbStep.of_same hM hS).ok hO

end

end Fl4Proofs.P3
