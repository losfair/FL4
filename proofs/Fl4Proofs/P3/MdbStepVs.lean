/-
P3 (DESIGN.md §9), VSpace: **`MdbStep.vs`**, the VSpace MDB invariant
`Vs.VsMdbInv` kept along any `MdbStep`, from VsMdbInv's step lemmas and the
constructors' VSpace side facts (`hv`, `hq4`/`hqal`, `hb`, `hvc`), with
`UtWin` (the untyped regions in the kernel window, `MdbStep.win`) alongside.
The retype case's new untyped caps lie inside the parent's region by
`RetypeDelta` (`cut`, `cbase`, `hAw`).

`MdbOKV ksb`: the MDB invariants the M-side posts carry, `MdbOK` with
`UtWin` and `Vs.VsMdbInv ksb`; `MdbStep.okv` keeps it.
-/
import Fl4Proofs.P3.MdbStep
import Fl4Proofs.P3.VsMdbInv
import Fl4Proofs.P3.MdbStepInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- What `fullF` makes is an untyped cap. -/
theorem fullF_ut {a b c : capability.Cap} (h : fullF a b = some c) : ∃ p sb f d, c = .Untyped p sb f d := by
  unfold fullF at h
  split at h
  · split_ifs at h; cases h; exact ⟨_, _, _, _, rfl⟩
  · cases h

/-- The source's cap after an insertion is well placed when it was. -/
theorem vcap_fullF {P L4 L3 L2 L1 : Set U64} {s c : capability.Cap} (h : Vs.VCapOK P L4 L3 L2 L1 s) :
    Vs.VCapOK P L4 L3 L2 L1 ((fullF s c).getD s) := by
  cases hf : fullF s c with
  | none => exact h
  | some c' => obtain ⟨p, sb, f, d, rfl⟩ := fullF_ut hf; trivial

/-- Retype's new untyped caps lie inside the parent's region. -/
theorem RetypeDelta.hin {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64}
    {dev : Bool} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) :
    ∀ j, j < w → ∀ q us f d, cj j = .Untyped q us f d → p.val ≤ q.val ∧ q.val + 2 ^ us.val ≤ p.val + 2 ^ sb.val := by
  intro j hj q us f d hc
  obtain ⟨us', d', hc', hk⟩ := h.cut j hj (by rw [hc]; rfl)
  rw [hc] at hc'
  have hus : us = us' := by injection hc'
  subst hus
  have hb := h.cbase j hj
  rw [hc] at hb
  have hq : baseF (.Untyped q us f d) = q.val := by
    unfold baseF; rw [show ptrF (.Untyped q us f d) = q from ok_inj (ptr_eq _).symm]
  rw [hq] at hb
  have hm : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right k hj
  have hA := h.hA
  have hAw := h.hAw
  rw [Nat.add_mul, Nat.one_mul] at hm
  constructor <;> omega

/-! ## The untyped regions in the kernel window along a step -/

theorem utW_of_ut {c' c : capability.Cap}
    (hut : ∀ p sb fi d, c' = .Untyped p sb fi d ↔ c = .Untyped p sb fi d) (h : UtW c) : UtW c' := by
  cases hc' : c' with
  | Untyped p sb fi d => rw [hc'] at hut; rw [(hut p sb fi d).1 rfl] at h; exact h
  | _ => simp [UtW]

theorem utW_of_shape {c' c : capability.Cap} (hsh : shape c' = shape c) (h : UtW c) : UtW c' := by
  cases c' <;> cases c <;> simp_all [shape, UtW]

theorem utW_nonphys {c : capability.Cap} (h : physF c = false) : UtW c := by
  cases c <;> simp only [UtW]
  rw [show physF (.Untyped _ _ _ _) = true from ok_inj (phys_eq _).symm] at h; cases h

section
variable {mem mem' : U64 → U64} {G : MdbGhost}

theorem UtWin.of_caps (h : UtWin mem G) (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : UtWin mem' G :=
  fun x hx => by rw [hc x hx]; exact h x hx

theorem UtWin.insert (h : UtWin mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    (hcd : UtW (capV mem' dest)) (hcap : ∀ z ∈ G.chains.flatten, z ≠ dest → UtW (capV mem z) → UtW (capV mem' z)) :
    UtWin mem' (insG G src dest b) := by
  intro x hx
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · exact hcd
  · by_cases e : x = dest
    · subst e; exact hcd
    · exact hcap x hx0 e (h x hx0)

end

/-- **`UtWin` along an `MdbStep`.** -/
theorem MdbStep.win {mem mem' : U64 → U64} {G G' : MdbGhost} (h : MdbStep mem G mem' G') :
    UtWin mem G → UtWin mem' G' := by
  induction h with
  | keep _ hc _ => exact fun hW => hW.of_caps hc
  | recap _ x0 ha _ hc _ =>
    intro hW x hx
    by_cases e : x = x0
    · subst e; exact utW_of_ut ha.ut (hW x hx)
    · rw [hc x hx e]; exact hW x hx
  | @setFi th mem mem' G hM hI x p sb fi f dev hx hcx hcx' _ _ hc _ =>
    intro hW z hz
    by_cases e : z = x
    · subst e; have := hW z hz; rw [hcx] at this; rw [hcx']; exact this
    · rw [hc z hz e]; exact hW z hz
  | @insert th mem mem' G src dest c c1 h hc1 _ _ b _ _ =>
    intro hW
    have hs := h.sl h.hsrc
    have hsd : src ≠ dest := h.dne h.hsrc
    refine hW.insert h.hsrc b (by rw [h.hcap dest h.hd, if_pos rfl]; exact utW_of_shape h.hsh (hW src h.hsrc))
      fun z hz hzd hok => ?_
    rw [h.hcap z (h.sl hz), if_neg hzd]
    split_ifs with e
    · subst e; exact utW_of_shape h.hsh1 hok
    · exact hok
  | nonphys _ b hsrc _ _ hcd hcp _ hc _ =>
    exact fun hW => hW.insert hsrc b (by rw [hcd]; exact utW_nonphys hcp) fun z hz _ hok => by rw [hc z hz]; exact hok
  | remove hM x hc _ =>
    intro hW z hz
    obtain ⟨hz0, hzn⟩ := (Mdb.mem_removeChains hM.tree.nodup).1 hz
    rw [hc z hz0 hzn]; exact hW z hz0
  | rename _ e ha _ =>
    intro hW x hx
    have hx0 := (mem_renG e x).1 hx
    have := utW_of_ut (ha _ hx0).1.ut (hW _ hx0)
    rwa [Equiv.apply_symm_apply] at this
  | frameAlias _ _ b hsrc _ _ hcd _ _ _ _ _ hc _ _ _ _ =>
    exact fun hW => hW.insert hsrc b (by rw [hcd]; trivial) fun z hz _ hok => by rw [hc z hz]; exact hok
  | pool _ _ hx _ _ _ _ hcf _ _ hc _ _ =>
    exact fun hW => hW.insert hx true (by rw [hcf]; trivial) fun z hz _ hok => by rw [hc z hz]; exact hok
  | @retype th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj h _ _ _ _ =>
    intro hW x hx
    have hps := hW _ h.hsrc
    rw [h.hcs] at hps
    rcases h.F1 x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases e : x = src
      · subst e; rw [h.F2b _ h.hsrc, h.hcs1]; exact hps
      · rw [h.F2b x hx0, h.hc1 x hx0 e]; exact hW x hx0
    · rw [h.F2a j hj]
      cases hcj : cj j with
      | Untyped q us f d => exact le_trans hps (h.hin j hj q us f d hcj).1
      | _ => trivial
  | trans _ _ ih1 ih2 => exact fun hW => ih2 (ih1 hW)

/-! ## Retype's new caps well placed -/

theorem mask_huge_bits : ∀ i < 64, (4503598553628672#64 : BitVec 64).getLsbD i = decide (30 ≤ i ∧ i < 52) := by
  intro i hi; interval_cases i <;> decide

/-- An address at or above `PPTR_BASE`, aligned, in the mask. -/
theorem pam_win {p M : U64} {lo : Nat} (hlo : lo = 12 ∨ lo = 21 ∨ lo = 30)
    (hM : ∀ i < 64, M.bv.getLsbD i = decide (lo ≤ i ∧ i < 52))
    (hb : layout.PPTR_BASE.val ≤ p.val) (ha : p.val % 2 ^ lo = 0) : Vs.PaM p M := by
  rw [Vs.pam_iff (by omega) hM]
  have hb' := Fl4Proofs.P0.Consts.layout.PPTR_BASE.val_eq
  have hpv : (core.num.U64.wrapping_sub p layout.PPTR_BASE).val =
      (p.val + (2 ^ 64 - layout.PPTR_BASE.val)) % 2 ^ 64 := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]
  rw [hpv]
  have : p.val < 2 ^ 64 := p.hBounds
  rcases hlo with rfl | rfl | rfl <;> norm_num at ha ⊢ <;> omega

/-- A new cap of retype, well placed in any ghost sets holding its
pointer. -/
theorem vcap_of_newV {S : Set U64} {c : capability.Cap} (h : NewVPlaced c) (hS : ptrF c ∈ S) :
    Vs.VCapOK S S S S S c := by
  have hpS : ∀ q, ptrF c = q → q ∈ S := fun q e => e ▸ hS
  cases c with
  | PageTable p mp a v =>
    obtain ⟨rfl, hb, ha⟩ := h
    exact ⟨hpS p (ok_inj (ptr_eq _).symm), pam_win (Or.inl rfl) Vs.mask_small_bits hb ha, fun e => by cases e⟩
  | PageDirectory p mp a v =>
    obtain ⟨rfl, hb, ha⟩ := h
    exact ⟨hpS p (ok_inj (ptr_eq _).symm), pam_win (Or.inl rfl) Vs.mask_small_bits hb ha, fun e => by cases e⟩
  | Pdpt p mp a v =>
    obtain ⟨rfl, hb, ha⟩ := h
    exact ⟨hpS p (ok_inj (ptr_eq _).symm), pam_win (Or.inl rfl) Vs.mask_small_bits hb ha, fun e => by cases e⟩
  | Pml4 p mp a =>
    obtain ⟨rfl, hb⟩ := h
    refine ⟨hpS p (ok_inj (ptr_eq _).symm), fun e => ?_, fun e => by cases e⟩
    have := Fl4Proofs.P0.Consts.layout.PPTR_BASE.val_eq
    have : p.val = 0 := by rw [e]; rfl
    omega
  | Frame p sz r dv m ept a va =>
    obtain ⟨rfl, hb, ha⟩ := h
    refine ⟨(fun e => by cases e), ?_⟩
    cases sz
    · exact pam_win (Or.inl rfl) Vs.mask_small_bits hb ha
    · exact pam_win (Or.inr (Or.inl rfl)) Vs.mask_large_bits hb ha
    · exact pam_win (Or.inr (Or.inr rfl)) mask_huge_bits hb ha
  | AsidPool _ _ => exact h.elim
  | _ => trivial

/-- **`VsMdbInv` along an `MdbStep`**, the untyped regions in the kernel
window. -/
theorem MdbStep.vs {mem mem' : U64 → U64} {G G' : MdbGhost} (h : MdbStep mem G mem' G') :
    ∀ ksb, UtWin mem G → Vs.VsMdbInv ksb mem G → Vs.VsMdbInv ksb mem' G' := by
  induction h with
  | keep _ hc _ => exact fun _ _ hV => hV.keep hc
  | recap _ x0 ha hv hc _ => exact fun _ _ hV => hV.recap x0 ha.ut hv hc
  | setFi _ _ _ hcx hcx' _ _ hc _ => exact fun _ _ hV => hV.setFi hcx hcx' hc
  | @insert th mem mem' G src dest c c1 h hc1 _ _ b _ hv =>
    intro _ _ hV
    have hs := h.sl h.hsrc
    have hsd : src ≠ dest := h.dne h.hsrc
    refine hV.insert h.hsrc b (c := c) (c1 := c1) (by rw [h.hcap dest h.hd, if_pos rfl])
      (by rw [h.hcap src hs, if_neg hsd, if_pos rfl]) h.hsh h.hsh1 hv
      (fun P L4 L3 L2 L1 hok => by rw [hc1]; exact vcap_fullF hok) fun z hz h1 h2 => ?_
    rw [h.hcap z (h.sl hz), if_neg h2, if_neg h1]
  | nonphys _ b hsrc _ _ hcd hcp _ hc _ => exact fun _ _ hV => hV.nonphys hsrc b hcd hcp hc
  | remove hM x hc _ => exact fun _ _ hV => hV.remove hM x hc
  | rename _ e ha hv => exact fun _ _ hV => hV.rename e (fun z hz => (ha z hz).1.ut) hv
  | frameAlias _ _ b hsrc _ hsC hcd hq1 _ _ _ _ hc _ _ hq4 hqal =>
    exact fun _ _ hV => hV.frameAlias hsrc b hsC hcd hq1 hq4 hqal hc
  | pool _ _ hx _ _ _ _ hcf _ _ hc _ hb => exact fun _ _ hV => hV.pool hx hcf hb hc
  | @retype th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj h _ _ _ hvc =>
    intro _ hW hV
    have hps := hW _ h.hsrc
    rw [h.hcs] at hps
    let S : Set U64 := {q | ∃ j, j < w ∧ ptrF (cj j) = q}
    exact hV.retype (Pn := S) (L4n := S) (L3n := S) (L2n := S) (L1n := S) h.hsrc h.hcs
      (by rw [h.F2b _ h.hsrc]; exact h.hcs1) (fun x hx e => by rw [h.F2b x hx, h.hc1 x hx e]) h.F1 h.F2a
      (fun j hj => vcap_of_newV (hvc hps j hj) ⟨j, hj, rfl⟩) h.hin
  | trans a _ ih1 ih2 => exact fun k hW hV => ih2 k (a.win hW) (ih1 k hW hV)


/-- **The MDB invariants with the VSpace ones** (the M-side posts):
`MdbOK`, the untyped regions in the kernel window, and `Vs.VsMdbInv` at the
kernel-global base `ksb`. -/
def MdbOKV (ksb : U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  MdbOK mem G ∧ UtWin mem G ∧ Vs.VsMdbInv ksb mem G

theorem MdbStep.okv {ksb : U64} {mem mem' : U64 → U64} {G G' : MdbGhost} (h : MdbStep mem G mem' G')
    (hO : MdbOKV ksb mem G) : MdbOKV ksb mem' G' :=
  ⟨h.ok hO.1, h.win hO.2.1, h.vs ksb hO.2.1 hO.2.2⟩

theorem MdbOKV.of_same {ksb : U64} {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (hS : SlotsSame th m m') (hO : MdbOKV ksb m G) : MdbOKV ksb m' G := (MdbStep.of_same hM hS).okv hO

theorem MdbOKV.toOK {ksb : U64} {mem : U64 → U64} {G : MdbGhost} (h : MdbOKV ksb mem G) : MdbOK mem G := h.1

/-- `MdbOKV` along a step, in the form `TcbCaps`' generic installs take. -/
theorem MdbOKV.step (ksb : U64) : ∀ m G m' G', MdbStep m G m' G' → MdbOKV ksb m G → MdbOKV ksb m' G' :=
  fun _ _ _ _ h hO => h.okv hO

end

end Fl4Proofs.P3
