/-
P3 (DESIGN.md §9), CSpace: **the deletion loop at `J`, by its steps**: the
loop run with a `JAtZ`-carrying invariant (`WJ`) and the readiness of the
slot to be emptied (`RdJ`, `EmptyReady`: the objects of the slot's cap dead
or covered by another cap), so that one cap's deletion at `J` (`JDelHyp`)
follows from premises about single steps of the loop (`DelHypsWR`, DelW),
some of them proved here.

* `WJ Z H Cs kb`: `JAtZ` at the sets `Z.mv G V` (the MDB ghost the loop's,
  the VSpace sets, the active SCs, the call stacks and the dead set chosen),
  P1's heap `H`, the cores `Cs` and the kernel-state base `kb` fixed;
  `EJ`: with `DelE`. `RdJ H`: `EmptyReady` (XTopJointEmpty).
* `JDelHyp`: one cap's deletion at `EJ` (`DelHypW`'s shape, the revoke's and
  the delete's premise); `JPreemptHyp` [J]: the preemption point at `WJ`.
* Proved steps: a notification cap's finalisation (`jFinAt_ntfn`: P3's
  `finNtfnJ`, P1's `fin_cap_ntfn.dead`, or `fin_idle` and another cap,
  `other_ntfn`); the readiness of the caps finalised without effect but
  zombies (`rdTrivJ`: the trivial caps cover nothing; a CNode cap's CNode is
  dead for `DeadP`, `cnode_ready`); the empty of a CNode slot
  (`emptyHypJ`: `emptyJR`, the untyped caps' facts after from
  `JEmptyUtHyp`).
* Named premises [J] (`JDelParts`), each one step of the loop at `WJ`:
  `JFinAtF` (a final object cap's finalisation, but notification, frame and
  IO port caps, with `RdJ` after; a non-final one's is `jFin_nonfinal`:
  nothing, the slot ready by another cap alike it), `JFinAt FrIoK` (frame and
  IO port caps, finalised with work even when not final),
  `JRdTrivHyp` (`RdJ` at a zombie), `JZombieHyp` (a zombie
  written over a cap alike it), `JSwapHyp` (a zombie swapped with its first
  slot), `JEmptyUtHyp` (`DelUtFact` after emptying a ready slot: the known
  `valid_untyped` gap, as `DelUtHyp`).
* The empty of a ready slot (`emptyHypJ`): a CNode slot by `emptyJR`, a TCB
  slot by `emptyJRT` (a step changing the TCB's caps only, `KeepCT`), both
  with `JEmptyUtHyp`.
* `JDelHyp.of_parts`: `JDelHyp` from `JDelParts`, `JPreemptHyp` and
  `JPostDelHyp` (`delHyp_fullWR`; `JPreemptHyp` from the platform and
  `PPReady`, XTopJointPP's `jPreemptHyp_of`; `JPostDelHyp` from the
  kernel-state layout, XTopJointPost's `jPostDelHyp_of`).
-/
import Fl4Proofs.P3.XTopJointStep
import Fl4Proofs.P3.XTopJointEmpty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletion's invariant at `J`** (module docstring). -/
def WJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ ∧ L.ksb s = kb

/-- `WJ` with `DelE` (the CSpace deletion's invariant and fuel bound). -/
abbrev EJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJ (L := L) arI AR Z H Cs kb s a σ G

/-- **The deletion's state after a preemption at `J`**: the post of a
preempting preemption point from `WJ` (FL4's `preemption_point` returning
`Preempted`, a preempting outcome of the spec's). Not `WJ` itself: the
preemption point updates the time, and the current SC's budget may then be
exhausted (`JAtZ`'s `OffOK` false), which the caller's
`mcs_preemption_point` charges before `schedule`. -/
def WJP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit), WJ (L := L) arI AR Z H Cs kb s0 a0 σ0 G ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1 ∧
    DomRel (L.mem s) (L.ksb s) σ ∧ MdbOKV (L.ksb s) (L.mem s) G

/-- `WJP` with `DelE`. -/
abbrev EJP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  DelE (L := L) Z.th K s σ ∧ WJP (L := L) arI AR Z H Cs kb s a σ G

/-- **The readiness at `J`** of a slot to be emptied: `EmptyReady`. -/
abbrev RdJ (H : P1.Heap) : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop :=
  fun s _ _ G x => EmptyReady (L := L) H G s x

/-- **One cap's deletion at `J`**: FL4's exposed `delete` of an MDB slot from
`EJ` (a `JAtZ` state at the sets `Z.mv G V`), a spec outcome of `cap_delete`
of the same kind, the CSpace relation, `EJ` after (`EJP` after a
preemption) and the ghost step (`DelHypW`). Derived from `JDelParts`
(`JDelHyp.of_parts`). -/
def JDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat), Z.th = th →
    (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) → 6 ≤ K →
    DelHypW (L := L) arI psiD th (EJ (L := L) arI AR Z H Cs kb K) (EJP (L := L) arI AR Z H Cs kb K)

/-- **Hypothesis: the preemption point at `J`** [J]: from `WJ` (a `JAtZ`
state), the cap slots kept, a spec outcome of the same kind, the CSpace
relation and `WJ` after at the same MDB ghost, `WJP` after a preemption
(`PPHypDW`). FL4's preemption point runs `update_timestamp` (the SC and
time fields). -/
def JPreemptHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    PPHypDW (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) th

/-! ## The named steps -/

/-- A notification cap. -/
def NtfnK (c : capability.Cap) : Prop := ∃ p b w r, c = .Notification p b w r

/-- **Hypothesis: the finalisation at `J` of the object caps of the kinds
`Kd`** [J]: `FinObjHypWR` at `WJ` with `RdJ` after, for those kinds (the
notification caps proved, `jFinAt_ntfn`). -/
def JFinAt (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    FinObjHypWRK (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th Kd

/-- **Hypothesis: a final cap's finalisation at `J`, for the object caps of
the kinds `Kd`** [J]: `JFinAt` for final caps only (a non-final cap's,
`jFin_nonfinal`, is proved for every object cap but frames and IO port caps). -/
def JFinAtF (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → WJ (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
    capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c → Kd c → Fl4Spec.isFinalCap' (absCap c) σ →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄

/-- A frame cap or an IO port cap (finalised with work when not final). -/
def FrIoK (c : capability.Cap) : Prop := isFrame c = true ∨ ∃ f l o, c = .IoPort f l o

/-- **Hypothesis: a zombie's slot is ready at `J`** [J] (`RdTrivHyp` for
zombies; their finalisation leaves the state as it is): the objects in the
zombie's range (its CNode, or its TCB) dead or covered by another cap.
`JAtZ` has no fact on zombies' objects now (a zombie outlives a preempted
deletion): it needs an invariant "a zombie's TCB is `DeadP`". -/
def JRdTrivHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p zt n : U64),
      DState (L := L) th s σ G → WJ (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.Zombie p zt n) →
      RdJ (L := L) (A := A) H s a σ G (cslotAddr sl)

/-- **Hypothesis: a zombie written over a cap alike it keeps `WJ`** [J]
(`ZombieHypW` at `WJ`). Missing for a proof by `jowes_cn` (one slot written):
the written slot's container live (`DestLive`: a CNode cap to it, or the
kernel block). Inside a CNode being deleted the container's own cap is
already a zombie, so `DestLive` (and `cn_utc`, which reads it) must accept a
zombie over the container; and `WJ` must carry "a zombie's objects are dead
or covered" for the cover (`JCovD`). -/
def JZombieHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ZombieHypW (L := L) (A := A) (WJ (L := L) arI AR Z H Cs kb) th

/-- **Hypothesis: a zombie swapped with its first slot keeps `WJ`** [J]
(`SwapHypW` at `WJ`). Missing for a proof by `jowes_cn` (two slots
written, the caps and the CDT renamed): the first slot's container is the
zombie's own CNode or TCB, whose cap is the zombie, so `DestLive` fails
(as for `JZombieHyp`); and `JPlaced.slot` asks every TCB's slot 3 kept,
which needs the zombie's slot not to be one (not known at `WJ`). -/
def JSwapHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    SwapHypW (L := L) (A := A) (WJ (L := L) arI AR Z H Cs kb) th

/-- **Hypothesis: a cleanup cap's `post_cap_deletion` keeps `WJ`** [J]
(`PostDelHypW` at `WJ`). -/
def JPostDelHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    PostDelHypW (L := L) arI (WJ (L := L) arI AR Z H Cs kb) th

/-- **Hypothesis: the untyped caps a ready CNode slot's emptying leaves
childless** [J] (`DelUtFact` after, the known `valid_untyped` gap, as
`DelUtHyp`; the facts of `EmptyHypWR` at `WJ`). -/
def JEmptyUtHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
    ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G G' : MdbGhost) (sl : Fl4Spec.CslotPtr),
      WJ (L := L) arI AR Z H Cs kb s a σ G → RdJ (L := L) (A := A) H s a σ G (cslotAddr sl) →
      DState (L := L) th s σ G → DState (L := L) th s' σ' G' → Vs.SlotFrame2 (L := L) th s s' →
      ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1 → AbsSlot th sl →
      capV (L.mem s) (cslotAddr sl) ≠ .Null → capV (L.mem s') (cslotAddr sl) = .Null →
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y) →
      MdbStep (L.mem s) G (L.mem s') G' →
      ∀ u up usb ufi udev, AbsSlot th u → capAt (L.mem s) (cslotAddr u) = ok (.Untyped up usb ufi udev) →
        σ.cdt sl = some u → (∀ x, σ.cdt x = some u → x = sl) → (∀ x, σ.cdt x ≠ some sl) →
        DelUtFact (L := L) th s' σ' up usb ufi

/-- **The named steps of the deletion at `J`** (module docstring). -/
structure JDelParts (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  fin : JFinAtF (L := L) arI AR th (fun c => ¬ NtfnK c ∧ ¬ FrIoK c)
  finFrIo : JFinAt (L := L) arI AR th FrIoK
  triv : JRdTrivHyp (L := L) arI AR th
  zomb : JZombieHyp (L := L) arI AR th
  swap : JSwapHyp (L := L) arI AR th
  empUt : JEmptyUtHyp (L := L) arI AR th

/-! ## The proved steps -/

variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

/-- **A notification cap's finalisation at `J`** (module docstring). -/
theorem jFinAt_ntfn [Fl4Proofs.P1.PlainStore st] : JFinAt (L := L) arI AR th NtfnK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ hn
  obtain ⟨p, b, w, r, rfl⟩ := hn
  subst hth
  obtain ⟨V, Ac, Lst, D, J, hkb⟩ := hW
  have hP := J.xtop.rel.1
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b w r hcv).2
  have hpN : p ∈ (Z.mv G V).N := J.hset.2.1 p hHp
  by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ
  · rw [decide_eq_true hfin]
    refine WP.spec_mono (WP.spec_and (J.finNtfnJ hpN)
      (P1.fin_cap_ntfn.dead (ar := arI) s a p b w r false J.blk hHp hHp)) ?_
    rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨e1, e2, σ1, V1, hmem1, J1, -, hSS1, hks1⟩, d1, d2, d3⟩
    simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 d2 d3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    subst e2
    have hdp : DeadP (L := L) H s1 p :=
      ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ => ⟨d1, d2, d3⟩,
        fun h => (by rw [hHp] at h; cases h), fun z h => (by rw [hHp] at h; cases h)⟩
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Notification p b w r := by
      rw [hSS1.capV hA.isSlot, hcv]
    refine ⟨rfl, trivial, trivial, σ1, G, hmem1, ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩, hcv1,
      fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
      ⟨V1, Ac, Lst, D, J1, hks1.trans hkb⟩, J1.ntfn_ready hA.isSlot hcv1 (Or.inl hdp)⟩
  · rw [decide_eq_false hfin]
    obtain ⟨cl, he, hmem, -, -, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ (.Notification p b w r) trivial
      false (fun hw => by have := finWork_ntfn hw; cases this)
    have hcl0 : cl = .Null := hnio (fun f l e => by cases e)
    subst hcl0
    rw [he, WP.spec_ok]
    exact ⟨rfl, trivial, trivial, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
      ⟨V, Ac, Lst, D, J, hkb⟩, J.ntfn_ready hA.isSlot hcv (Or.inr (other_ntfn hP hDS hA hcv hfin))⟩

theorem okey_of_finObj {c : capability.Cap} (hk : FinObjKind c) : okey c ≠ none := by
  cases c <;> simp_all [FinObjKind, okey]

theorem isUt_of_finObj {c : capability.Cap} (hk : FinObjKind c) : isUt c = false := by
  cases c <;> simp_all [FinObjKind, isUt]

/-- **A non-final cap's finalisation at `J`**, every object cap but frames
and IO port caps: nothing (`fin_idle`), the slot ready by another cap alike
it (`other_key`, `EmptyReady.of_cover`). -/
theorem jFin_nonfinal [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap)
    (hDS : DState (L := L) th s σ G) (hW : WJ (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FinObjKind c) (hfi : ¬ FrIoK c)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJ (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        RdJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄ := by
  subst hth
  have hP : Placed Z.th := by obtain ⟨V, Ac, Lst, D, J, -⟩ := hW; exact J.xtop.rel.1
  have hcv := capV_of_capAt hc
  have hf : isFrame c = false := by
    cases h : isFrame c
    · rfl
    · exact absurd (Or.inl h) hfi
  have hio : ∀ f l o, c ≠ .IoPort f l o := fun f l o e => hfi (Or.inr ⟨f, l, o, e⟩)
  rw [decide_eq_false hfin]
  obtain ⟨cl, he, hmem, -, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk false (by
    rintro (⟨h | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩)
    · cases h
    · exact hio _ _ _ e
    · subst e; simp [isFrame] at hf)
  have hcl0 : cl = .Null := hnio (fun f l e => hio f l 0#u64 e)
  subst hcl0
  obtain ⟨y, hy, hne, hky⟩ := other_key hP hDS hA hcv hk hf hfin
  have hn : okey c ≠ none := okey_of_finObj hk
  have hsh : shape (capV (L.mem s) y) = shape c := shape_of_key hky (by rw [hky]; exact hn)
  obtain ⟨eb, et, ep⟩ := range_of_shape hsh
  have hut : isUt (capV (L.mem s) y) = false := by
    rw [isUt_of_shape hsh]; exact isUt_of_finObj hk
  rw [he, WP.spec_ok]
  exact ⟨hrem.symm, trivial, trivial, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
    hW, EmptyReady.of_cover (x := cslotAddr sl) hy hne (fun h => by rw [ep]; rw [hcv] at h; exact h) hut
      (by rw [eb, hcv]) (by rw [et, hcv])⟩

/-- The object caps' finalisation at `J`, from the notification caps'
(`jFinAt_ntfn`), the non-final caps' (`jFin_nonfinal`), the final caps'
(`JDelParts.fin`) and the frame and IO port caps' (`JDelParts.finFrIo`). -/
theorem finJ [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (kb : U64) (hth : Z.th = th) :
    FinObjHypWR (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th := by
  intro s a σ G sl c hDS hW hA hc hk _
  by_cases hn : NtfnK c
  · exact jFinAt_ntfn arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hn
  by_cases hfi : FrIoK c
  · exact h.finFrIo Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hfi
  by_cases hfin : Fl4Spec.isFinalCap' (absCap c) σ
  · exact h.fin Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨hn, hfi⟩ hfin
  · exact jFin_nonfinal arI Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hfi hfin

/-- The trivially finalised caps but untyped ones are not physical. -/
theorem physF_triv (c : capability.Cap) (ht : TrivFin c) (hu : isUt c = false) : physF c = false := by
  cases c <;> simp only [TrivFin] at ht <;> first | exact ok_inj (phys_eq _).symm | simp [isUt] at hu

/-- A CNode cap's range: its CNode's `2 ^ (r + 5)` bytes. -/
theorem range_cnodeR (q r gs g : U64) (hr : r.val + 5 < 64) (hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64) :
    baseF (.CNode q r gs g) = q.val ∧ topF (.CNode q r gs g) = q.val + 32 * 2 ^ r.val - 1 := by
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hsz : sizeF (.CNode q r gs g) = core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT :=
    ok_inj (size_eq _).symm
  have hs : (core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT).val = r.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits,
      fl4_abi.consts.bits.SLOT]
    omega
  have hm := maskF_val (b := core.num.U64.wrapping_add r fl4_abi.consts.bits.SLOT) (by rw [hs]; exact hr)
  rw [hs, e5] at hm
  have h1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine ⟨by unfold baseF; rw [ptrF_cnode], ?_⟩
  unfold topF
  rw [ptrF_cnode, hsz]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

/-- A word holding an `other` object of `H` (a CNode) is dead (`DeadP`
reads the TCB, endpoint, notification, reply and SC words only). -/
theorem deadP_other {H : P1.Heap} {s : S} {q : U64} {z : Nat} (h : H q = some (.other z)) :
    DeadP (L := L) H s q :=
  ⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e),
    fun e => (by rw [h] at e; cases e), fun z e => (by rw [h] at e; cases e)⟩

/-- **A CNode cap's slot is ready to be emptied**: the only object of `H`
in its range is its CNode (`other`, dead for `DeadP`). -/
theorem JAtZ.cnode_ready {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {q r gs g : U64}
    (hcv : capV (L.mem s) x = .CNode q r gs g) (hth : Z.th q = some (.cnode r.val)) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHq : H q = some (.other (r.val + 5)) := hJ.cnode q r.val hth
  have e5 : 2 ^ (r.val + 5) = 32 * 2 ^ r.val := by rw [pow_add]; ring
  have hfit : q.val + 32 * 2 ^ r.val ≤ 2 ^ 64 := by
    have := J.kern.heap.fits q _ hHq; rw [← e5]; exact this
  have hlt : r.val + 5 < 64 := J.kern.heap.lt64 q _ hHq
  obtain ⟨e1, e2⟩ := range_cnodeR q r gs g hlt hfit
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q' k, H q' = some k → q' ≠ q → q'.val + 2 ^ k.bits ≤ q.val ∨ q.val + 32 * 2 ^ r.val ≤ q'.val := by
    intro q' k hq' hne
    have := J.kern.heap.disj q' k q _ hq' hHq hne
    simpa only [show (P1.HKind.other (r.val + 5)).bits = r.val + 5 from rfl, e5] using this
  have h32 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  refine ⟨fun lo hi hlh h1 h2 => Or.inr fun q' hq' => ?_, fun z hz h1 h2 => ?_⟩
  · by_cases e : q' = q
    · subst e; exact deadP_other hHq
    · cases hk : H q' with
      | none => exact deadP_none hk
      | some k =>
        exfalso
        have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hout q' k hk e with h | h <;> omega
  · exfalso
    have hne : L.cscW s ≠ q := fun e => by rw [e, hHq] at hz; cases hz
    have : 1 ≤ 2 ^ (P1.HKind.sc z).bits := Nat.one_le_two_pow
    rcases hout _ _ hz hne with h | h <;> omega

/-- **The readiness at `J` of a cap finalised without effect** (`RdTrivHyp`
at `WJ`): the trivial caps cover nothing, a CNode cap's CNode is dead for
`DeadP` (`cnode_ready`); zombies by `JRdTrivHyp`. -/
theorem rdTrivJ (hRT : JRdTrivHyp (L := L) arI AR th) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) : RdTrivHyp (L := L) (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th := by
  intro s a σ G sl c hDS hW hA hc hcn hnk
  rcases cap_cases c hcn with ht | hcn' | hz | ho
  · intro hp hu
    rw [capV_of_capAt hc] at hp hu
    rw [physF_triv c ht hu] at hp
    cases hp
  · obtain ⟨q, r, gs, g, rfl⟩ := hcn'
    have hcvd : CapValid th (.CNode q r gs g) := hDS.1.2.1.abs hA hc
    subst hth
    obtain ⟨V, Ac, Lst, D, J, -⟩ := hW
    exact JAtZ.cnode_ready arI J (capV_of_capAt hc)
      (show Z.th q = some (.cnode r.val) ∧ r.val ≠ 0 from hcvd).1
  · obtain ⟨p, zt, n, rfl⟩ := hz
    exact hRT Z H Cs kb hth s a σ G sl p zt n hDS hW hA hc
  · exact absurd ho hnk

/-- **Emptying a ready slot at `J`** (`EmptyHypWR` at `WJ`): a CNode slot by
`emptyJR`, a TCB slot by `emptyJRT`, both with `JEmptyUtHyp`. -/
theorem emptyHypJ (hUt : JEmptyUtHyp (L := L) arI AR th) (Z : XSets)
    (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    EmptyHypWR (L := L) (WJ (L := L) arI AR Z H Cs kb) (RdJ (L := L) (A := A) H) th := by
  intro s s' a σ σ' G G' sl hW hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS
  have hU := hUt Z H Cs kb hth s s' a σ σ' G G' sl hW hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS
  subst hth
  obtain ⟨V, Ac, Lst, D, J, hkb⟩ := hW
  have hnk := emptySlot_null_nkn _ σ ((), σ') hes
  obtain ⟨⟨V2, hX2⟩, -, -, -⟩ := slotHypW_XZ AR (Z.mv G V) kb s s' a σ σ' G G'
    ⟨⟨V, J.xtop⟩, J.ks, J.thT, hkb⟩ hD1 hD2 hF hnk hmS
  obtain ⟨hks, hkb2, hR⟩ : L.ksb s' = L.ksb s ∧ KBack σ σ' ∧ _ := by
    by_cases hcn : ∃ q, sl.1 = q.bv ∧ Z.th q = some (.cnode sl.2.length)
    · exact J.emptyJR hA hcn hxn hRd hes hD2 hx0 hoth hX2 (SlotFrame2.writesIn hF) hnk
    · exact J.emptyJRT hA hcn hxn hRd hes hD2 hx0 hoth hX2 (SlotFrame2.writesIn hF) hnk
  obtain ⟨hC, Ac', Lst', D', R⟩ := hR hU
  exact ⟨V2, Ac', Lst', D', J.cs_frameV hks hX2 hkb2 hC R, hks.trans hkb⟩

/-- **`JDelHyp` from the named steps** (`delHyp_fullWR` at `WJ`, `RdJ`). -/
theorem JDelHyp.of_parts [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th) (hpp : JPreemptHyp (L := L) arI AR th)
    (hpost : JPostDelHyp (L := L) arI AR th) : JDelHyp (L := L) arI AR th := by
  intro Z H Cs kb K hth hK hK6 s a σ G c hCR hE hA hxm
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hE.2
  have hP : Placed th := hth ▸ J.xtop.rel.1
  have hH : DelHypsWR (L := L) arI (WJ (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb)
      (RdJ (L := L) (A := A) H) th :=
    ⟨finJ arI h Z H Cs kb hth, rdTrivJ arI h.triv Z H Cs kb hth, hpp Z H Cs kb hth, hpost Z H Cs kb hth,
      h.zomb Z H Cs kb hth, h.swap Z H Cs kb hth, emptyHypJ arI h.empUt Z H Cs kb hth⟩
  subst hth
  exact delHyp_fullWR arI _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 s a σ G c hCR hE hA hxm

end

end

end Fl4Proofs.P3
