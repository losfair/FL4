/-
P3 (DESIGN.md §9), CSpace: **finality, against the spec's**: the invariant
`FinInv` and what it gives (`final_iff`, `finF_iff`):

* `kt` (`KTyped`): the spec's CNodes and TCBs are objects of the typed heap,
  so every slot the spec reads is FL4's (`cov_of_kt`);
* `conn`: caps sharing an object are in one MDB chain (l4v `mdb_chunked`,
  the reachability half);
* `key`: caps sharing an object, neither a zombie, agree on it (`okey`:
  kind, pointer and the fields `same_object_as` compares; l4v: a valid cap
  fixes its object's type and size, and IO port ranges do not overlap);
* `fnest`: a frame cap's region holds no other frame (frames do not nest;
  l4v: objects do not overlap);
* `zfin`: zombies are final (l4v `zombies_final`).

The caps whose finalisation depends on finality (`NeedsFin`) are defined
here too. With `FinInv`, FL4's `is_final_capability` is `is_final_cap'`
for them, and zombies are final.
-/
import Fl4Proofs.P3.DelFin
import Fl4Proofs.P3.FinBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The caps whose finalisation is object-specific work. -/
def FinObjKind : capability.Cap → Prop
  | .Endpoint .. | .Notification .. | .Reply .. | .Thread _ | .SchedContext .. | .IrqHandler _
  | .Frame .. | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. | .Vcpu .. | .Ept .. | .AsidPool .. | .IoPort .. => True
  | _ => False

/-- The caps whose finalisation depends on finality: the object caps but
frames (whose finalisation, an unmap if mapped, ignores finality, as in l4v
`arch_finalise_cap`), CNode caps and zombies. (For untyped, domain, IRQ control, scheduling control and
the arch control caps, FL4's `is_final_capability` and the spec's
`is_final_cap` may differ: the spec's needs an object, FL4's does not; it
does not matter, their finalisation does nothing.) -/
def NeedsFin (c : capability.Cap) : Prop :=
  (FinObjKind c ∧ isFrame c = false) ∨ (∃ p r gs g, c = .CNode p r gs g) ∨ isZb c = true

theorem NeedsFin.nf {c : capability.Cap} (h : NeedsFin c) : isFrame c = false := by
  rcases h with ⟨-, h⟩ | ⟨p, r, gs, g, rfl⟩ | h
  · exact h
  · rfl
  · cases c <;> simp_all [isZb, isFrame]

theorem isFrame_of_key {a b : capability.Cap} (h : okey a = okey b) : isFrame a = isFrame b := by
  cases a <;> cases b <;> simp_all [okey, isFrame]

/-! ## `same_object_as` as a function -/

def fsB : capability.FrameSize → capability.FrameSize → Bool
  | .Small, .Small | .Large, .Large | .Huge, .Huge => true
  | _, _ => false

theorem fsB_iff (a b : capability.FrameSize) : fsB a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [fsB]

/-- `same_object_as a b`. -/
def soB : capability.Cap → capability.Cap → Bool
  | .Untyped .., _ => false
  | .IrqControl, _ => false
  | .IoPortControl, .IoPort .. => false
  | .Frame p sz _ d .., .Frame p' sz' _ d' .. => decide (p = p') && fsB sz sz' && (d == d')
  | a, b => srB a b

theorem soB_eq (a b : capability.Cap) : objects.same_object_as a b = ok (soB a b) := by
  cases a <;> cases b <;> simp only [objects.same_object_as, soB, srB_eq, bind_ok, Bool.false_eq_true,
    ↓reduceIte] <;> try rfl
  rename_i p sz _ d _ _ _ _ p' sz' _ d' _ _ _ _
  by_cases hp : p = p'
  · subst hp; cases sz <;> cases sz' <;>
      simp [capability.FrameSize.Insts.CoreCmpPartialEqFrameSize.eq, fsB,
        capability.FrameSize.read_discriminant] <;> cases d <;> cases d' <;> decide
  · simp [hp]


theorem soB_of_key {a b : capability.Cap} (h : okey a = okey b) (hn : okey a ≠ none) : soB a b = true := by
  cases a <;> cases b <;> simp only [okey, reduceCtorEq, Option.some.injEq, OKey.ep.injEq, OKey.ntfn.injEq,
    OKey.reply.injEq, OKey.cnode.injEq, OKey.thread.injEq, OKey.irq.injEq, OKey.sc.injEq, OKey.frame.injEq,
    OKey.pt.injEq, OKey.pd.injEq, OKey.pdpt.injEq, OKey.pml4.injEq, OKey.pool.injEq, OKey.io.injEq, OKey.vcpu.injEq, OKey.ept.injEq,
    ne_eq, not_true_eq_false] at h hn ⊢
  all_goals first
    | (obtain ⟨rfl, rfl, rfl⟩ := h; simp [soB, (fsB_iff _ _).2 rfl]; done)
    | (obtain ⟨rfl, rfl⟩ := h; simp only [soB]; apply srB_of_eq; simp [objects.same_region_as]; done)
    | (subst h; simp only [soB]; apply srB_of_eq; simp [objects.same_region_as]; done)
    | (simp only [soB]; apply srB_of_eq; simp [objects.same_region_as]; done)
    | (simp [soB, (fsB_iff _ _).2 rfl]; done)
    | (apply srB_of_eq; simp [objects.same_region_as]; done)

theorem shape_of_key {a b : capability.Cap} (h : okey a = okey b) (hn : okey a ≠ none) : shape a = shape b := by
  cases a <;> cases b <;> simp only [okey, reduceCtorEq, Option.some.injEq, OKey.ep.injEq, OKey.ntfn.injEq,
    OKey.reply.injEq, OKey.cnode.injEq, OKey.thread.injEq, OKey.irq.injEq, OKey.sc.injEq, OKey.frame.injEq,
    OKey.pt.injEq, OKey.pd.injEq, OKey.pdpt.injEq, OKey.pml4.injEq, OKey.pool.injEq, OKey.io.injEq, OKey.vcpu.injEq, OKey.ept.injEq,
    ne_eq, not_true_eq_false] at h hn ⊢
  all_goals first
    | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl; done)
    | (obtain ⟨rfl, rfl⟩ := h; rfl; done)
    | (subst h; rfl)
    | rfl

theorem sr_of_key {a b : capability.Cap} (h : okey a = okey b) (hn : okey a ≠ none) : srB a b = srB a a := by
  rw [srB_shape a b, srB_shape a a, shape_of_key h hn]

theorem key_of_sr {a b : capability.Cap} (h : srB a b = true) (hn : okey a ≠ none) (hf : isFrame a = false) :
    okey b = okey a := by
  have e := srB_eq a b
  rw [h] at e
  cases a <;> simp only [okey, isFrame, ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true] at hn hf ⊢ <;>
    cases b <;> simp [objects.same_region_as] at e ⊢
  all_goals first
    | exact UScalar.eq_of_val_eq e
    | (obtain ⟨e1, e2⟩ := e; exact ⟨UScalar.eq_of_val_eq e1, UScalar.eq_of_val_eq e2⟩)
    | (split_ifs at e with h1 h2 <;> simp_all)
    | skip


theorem sr_ok {a b : capability.Cap} (h : srB a b = true) : objects.same_region_as a b = ok true := by
  rw [srB_eq, h]

theorem key_of_so {a b : capability.Cap} (h : soB a b = true) (hb : NeedsFin b) (hz : isZb b = false) :
    okey a = okey b := by
  have hb' : FinObjKind b ∨ ∃ p r gs g, b = .CNode p r gs g := by
    rcases hb with ⟨hb, -⟩ | hb | hb
    · exact Or.inl hb
    · exact Or.inr hb
    · rw [hz] at hb; cases hb
  by_cases hfa : isFrame a = true
  · cases a <;> simp only [isFrame, reduceCtorEq, Bool.false_eq_true] at hfa
    cases b <;> simp only [soB] at h
    all_goals first
      | (simp only [Bool.and_eq_true, decide_eq_true_eq, fsB_iff, beq_iff_eq] at h
         obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl)
      | (have e := sr_ok h; simp [objects.same_region_as] at e; done)
      | (simp [FinObjKind] at hb'; done)
  · have hsr : srB a b = true ∧ okey a ≠ none := by
      cases a
      case Untyped => simp [soB] at h
      case IrqControl => simp [soB] at h
      case Frame => simp [isFrame] at hfa
      case IoPortControl =>
        exfalso
        cases b <;> simp only [soB, Bool.false_eq_true] at h <;> simp only [FinObjKind] at hb' <;>
          simp at hb' <;> (have e := sr_ok h; simp [objects.same_region_as] at e)
      case Null | Zombie | Domain | SchedControl | AsidControl =>
        exfalso
        simp only [soB] at h
        have e := sr_ok h
        cases b <;> simp only [FinObjKind] at hb' <;> simp at hb' <;> simp [objects.same_region_as] at e
      all_goals exact ⟨h, by simp [okey]⟩
    exact (key_of_sr hsr.1 hsr.2 (by simpa using hfa)).symm


/-! ## Generic object references of FL4 caps -/

/-- A generic object reference of a cap (the one `same_object_as` keys on). -/
def gref : capability.Cap → Option Fl4Spec.GenObjRef
  | .Endpoint p .. | .Notification p .. | .Reply p _ | .CNode p .. | .Thread p | .Zombie p .. | .SchedContext p _
  | .Frame p .. | .PageTable p .. | .PageDirectory p .. | .Pdpt p .. | .Pml4 p ..
  | .Vcpu p | .Ept p .. | .AsidPool p _ =>
    some (.objRef p.bv)
  | .IrqHandler i => some (.iRQRef (BitVec.ofNat 8 i.val))
  | .IoPort f _ _ => some (.archRef (.ioPortRef (BitVec.ofNat 16 f.val)))
  | _ => none

theorem gref_mem {c : capability.Cap} {r : Fl4Spec.GenObjRef} (h : gref c = some r) :
    r ∈ Fl4Spec.genObjRefs (absCap c) := by
  cases c <;> simp only [gref, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archGenRefs,
      Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef, absCap]

theorem gref_of_key {a b : capability.Cap} (h : okey a = okey b) (hn : okey a ≠ none) : gref a = gref b := by
  cases a <;> cases b <;> simp only [okey, ne_eq, not_true_eq_false, reduceCtorEq, Option.some.injEq, OKey.ep.injEq, OKey.ntfn.injEq,
    OKey.reply.injEq, OKey.cnode.injEq, OKey.thread.injEq, OKey.irq.injEq, OKey.sc.injEq, OKey.frame.injEq,
    OKey.pt.injEq, OKey.pd.injEq, OKey.pdpt.injEq, OKey.pml4.injEq, OKey.pool.injEq, OKey.io.injEq, OKey.vcpu.injEq, OKey.ept.injEq] at h hn ⊢ <;>
    simp [gref, h]

theorem gref_ne_none {a : capability.Cap} (h : okey a ≠ none) : gref a ≠ none := by
  cases a <;> simp [okey, gref] at h ⊢

theorem ovl_of_key {a b : capability.Cap} (h : okey a = okey b) (hn : okey a ≠ none) :
    Ovl (absCap a) (absCap b) := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 (gref_ne_none hn)
  intro he
  have : r ∈ Fl4Spec.genObjRefs (absCap a) ∩ Fl4Spec.genObjRefs (absCap b) :=
    ⟨gref_mem hr, gref_mem (by rw [← gref_of_key h hn]; exact hr)⟩
  rw [he] at this; exact this

theorem refs_ne {c : capability.Cap} (h : gref c ≠ none) : Fl4Spec.genObjRefs (absCap c) ≠ ∅ := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
  intro he; have := gref_mem hr; rw [he] at this; exact this

theorem needsFin_refs {c : capability.Cap} (h : NeedsFin c) : Fl4Spec.genObjRefs (absCap c) ≠ ∅ := by
  apply refs_ne
  rcases h with ⟨h, -⟩ | ⟨p, r, gs, g, rfl⟩ | h
  · cases c <;> simp [FinObjKind] at h <;> simp [gref]
  · simp [gref]
  · cases c <;> simp [isZb] at h; simp [gref]

theorem key_of_refs {a : capability.Cap} (h : Fl4Spec.genObjRefs (absCap a) ≠ ∅) (hz : isZb a = false) :
    okey a ≠ none := by
  intro hn
  apply h
  cases a <;> simp [okey, isZb] at hn hz <;>
    simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archGenRefs,
      Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef, absCap]

theorem soB_zombie_left (p zt n : U64) (b : capability.Cap) : soB (.Zombie p zt n) b = false := by
  simp only [soB]; apply srB_of_eq; simp [objects.same_region_as]

theorem soB_zombie_right (a : capability.Cap) (p zt n : U64) : soB a (.Zombie p zt n) = false := by
  cases a <;> simp only [soB] <;> apply srB_of_eq <;> simp [objects.same_region_as, objects.cap_is_physical]


theorem key_of_so_left {a b : capability.Cap} (h : soB a b = true) (ha : NeedsFin a) (hz : isZb a = false) :
    okey b = okey a := by
  have hk : okey a ≠ none := key_of_refs (needsFin_refs ha) hz
  by_cases hf : isFrame a = true
  · cases a <;> simp only [isFrame, reduceCtorEq, Bool.false_eq_true] at hf
    cases b <;> simp only [soB] at h
    all_goals first
      | (simp only [Bool.and_eq_true, decide_eq_true_eq, fsB_iff, beq_iff_eq] at h
         obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl)
      | (have e := sr_ok h; simp [objects.same_region_as] at e; done)
  · have hs : srB a b = true := by
      cases a <;> simp only [okey, ne_eq, not_true_eq_false, reduceCtorEq] at hk <;>
        simp only [isFrame, not_true_eq_false] at hf <;> simp only [soB] at h <;> exact h
    exact key_of_sr hs hk (by simpa using hf)

/-- FL4's finality test, from memory. -/
def finF (mem : U64 → U64) (x : U64) : Bool :=
  if prevOf mem x ≠ 0#u64 ∧ soB (capV mem (prevOf mem x)) (capV mem x) = true then false
  else if nextOf mem x = 0#u64 then true else !soB (capV mem x) (capV mem (nextOf mem x))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem is_final_eq (s : S) (x : U64) : cdt.is_final_capability st s x = ok (finF (L.mem s) x) := by
  unfold cdt.is_final_capability finF
  simp only [slot_cap_eq, capAt_capV, slot_prev_eq, slot_next_eq, is_null_eq, soB_eq, bind_ok]
  by_cases hp : prevOf (L.mem s) x = 0#u64
  · simp only [hp, decide_true, ↓reduceIte, ne_eq, not_true_eq_false, false_and]
    by_cases hn : nextOf (L.mem s) x = 0#u64 <;> simp [hn]
  · simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    by_cases hso : soB (capV (L.mem s) (prevOf (L.mem s) x)) (capV (L.mem s) x) = true
    · simp [hso]
    · by_cases hn : nextOf (L.mem s) x = 0#u64 <;> simp [hso, hn]

end

/-! ## The invariant -/

theorem tcbCnodeMap_some {t : Fl4Spec.Tcb} {c : Fl4Spec.CnodeIndex} {a : Fl4Spec.Cap}
    (h : Fl4Spec.tcbCnodeMap t c = some a) : ∃ i, i < tcbSlots ∧ c = Fl4Spec.tcbCnodeIndex i := by
  unfold Fl4Spec.tcbCnodeMap at h
  by_cases h5 : c = Fl4Spec.tcbCnodeIndex 5
  · exact ⟨5, by decide, h5⟩
  rw [Function.update_of_ne h5] at h
  by_cases h4 : c = Fl4Spec.tcbCnodeIndex 4
  · exact ⟨4, by decide, h4⟩
  rw [Function.update_of_ne h4] at h
  by_cases h3 : c = Fl4Spec.tcbCnodeIndex 3
  · exact ⟨3, by decide, h3⟩
  rw [Function.update_of_ne h3] at h
  by_cases h2 : c = Fl4Spec.tcbCnodeIndex 2
  · exact ⟨2, by decide, h2⟩
  rw [Function.update_of_ne h2] at h
  by_cases h1 : c = Fl4Spec.tcbCnodeIndex 1
  · exact ⟨1, by decide, h1⟩
  rw [Function.update_of_ne h1] at h
  by_cases h0 : c = Fl4Spec.tcbCnodeIndex 0
  · exact ⟨0, by decide, h0⟩
  rw [Function.update_of_ne h0] at h
  cases h

/-- Every slot the spec can read is a slot of the typed heap. -/
theorem cov_of_kt {th : TypedHeap} {σ : Fl4Spec.State Unit} (hK : KTyped th σ) {cref : Fl4Spec.CslotPtr}
    {cap' : Fl4Spec.Cap} (hg : ((Fl4Spec.getCap cref : Fl4Spec.SMonad Unit Fl4Spec.Cap) σ).1 = {(cap', σ)}) :
    AbsSlot th cref := by
  obtain ⟨o, c⟩ := cref
  rw [getCap_set_iff] at hg
  refine ⟨⟨o⟩, rfl, ?_⟩
  cases hk : σ.kheap o with
  | none => rw [hk] at hg; cases hg
  | some obj =>
    rw [hk] at hg
    cases obj with
    | cnode sz cn =>
      simp only [capOpt] at hg
      split_ifs at hg with hwf
      have hc : c ∈ Fl4Spec.dom cn := by simp [Fl4Spec.dom, hg]
      rw [hwf] at hc
      left
      rw [show c.length = sz from hc]
      exact (hK o).1 sz cn hk hwf
    | tcb t =>
      simp only [capOpt] at hg
      obtain ⟨i, hi, rfl⟩ := tcbCnodeMap_some hg
      exact Or.inr ⟨(hK o).2 t hk, i, hi, rfl⟩
    | _ => simp [capOpt] at hg

theorem MdbLinks.prev_eq_pred {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {P C : List U64} {w x : U64} (hch : P ++ w :: x :: C ∈ G.chains) : prevOf mem x = w := by
  have hc := hM.chain _ hch
  rw [List.isChain_append] at hc
  exact (List.isChain_cons_cons.1 hc.2.1).1.2

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **Spec finality, in related states**: no other slot of the MDB has a
cap sharing an object. -/
theorem final_iff {th : TypedHeap} (hP : Placed th) {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hM : MdbLinks th (L.mem s) G) (hF : FinInv th (L.mem s) σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hne : Fl4Spec.genObjRefs (absCap (capV (L.mem s) (cslotAddr sl))) ≠ ∅) :
    Fl4Spec.isFinalCap' (absCap (capV (L.mem s) (cslotAddr sl))) σ ↔
      ∀ y ∈ G.chains.flatten, y ≠ cslotAddr sl →
        ¬ Ovl (absCap (capV (L.mem s) (cslotAddr sl))) (absCap (capV (L.mem s) y)) := by
  obtain ⟨cx, ax, hcx, hax, hgx⟩ := hR.abs_cap hA
  rw [hax.abs, ← capV_of_capAt hcx] at hgx
  constructor
  · intro hfin y hy hyx
    obtain ⟨ysl, hys, rfl⟩ := ((hM.members y).1 hy).1.abs
    obtain ⟨cy, ay, hcy, hay, hgy⟩ := hR.abs_cap hys
    rw [hay.abs, ← capV_of_capAt hcy] at hgy
    have hne' : sl ≠ ysl := fun e => hyx (by rw [e])
    exact fun h => h (final_disjoint hgx hgy hne' hne hfin)
  · intro hno
    refine ⟨sl, Set.ext fun cref => ⟨fun ⟨cap', hg, hov⟩ => ?_, fun h => ?_⟩⟩
    · have hne2 : Fl4Spec.genObjRefs cap' ≠ ∅ := fun h => hov (by rw [h, Set.inter_empty])
      have hcr := cov_of_kt hF.kt hg
      obtain ⟨cy, ay, hcy, hay, hgy⟩ := hR.abs_cap hcr
      rw [hay.abs] at hgy
      rw [hgy] at hg
      have hcap : cap' = absCap cy := by
        have := (Set.singleton_eq_singleton_iff.1 hg); exact (Prod.mk.inj this).1.symm
      subst hcap
      by_cases he : cslotAddr cref = cslotAddr sl
      · exact Set.mem_singleton_iff.2 (cslotAddr_inj hP hcr hA he)
      · exfalso
        have hcn : cy ≠ .Null := by rintro rfl; exact hne2 (by
          simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archGenRefs,
            Fl4Spec.archCapSetMap, absCap])
        have hmem : cslotAddr cref ∈ G.chains.flatten := (hM.members _).2 ⟨hcr.isSlot, cy, hcy, hcn⟩
        refine hno _ hmem he ?_
        rw [capV_of_capAt hcy]; exact hov
    · rw [Set.mem_singleton_iff.1 h]
      refine ⟨_, by rw [hgx], ?_⟩
      rw [Set.inter_self]; exact hne

/-- **FL4's test is the spec's**, for a cap `NeedsFin` covers (not a
zombie). -/
theorem finF_iff {th : TypedHeap} (hP : Placed th) {mem : U64 → U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hM : MdbLinks th mem G) (hI : MdbInv mem G) (hF : FinInv th mem σ G) {x : U64} (hx : x ∈ G.chains.flatten)
    (hN : NeedsFin (capV mem x)) (hz : isZb (capV mem x) = false) :
    finF mem x = true ↔ ∀ y ∈ G.chains.flatten, y ≠ x → ¬ Ovl (absCap (capV mem x)) (absCap (capV mem y)) := by
  have hkx : okey (capV mem x) ≠ none := key_of_refs (needsFin_refs hN) hz
  have hslot : ∀ a ∈ G.chains.flatten, a ≠ 0#u64 := fun a ha => ((hM.members a).1 ha).1.ne_zero hP
  constructor
  · intro hf y hy hyx hov
    by_cases hzy : isZb (capV mem y) = true
    · exact hF.fm.zfin y hy x hx hyx hzy hov.symm
    have hk := hF.fm.key x hx y hy (Ne.symm hyx) hov hz (by simpa using hzy) (fun h => by rw [hN.nf] at h; exact absurd h.1 (by decide))
    obtain ⟨ch1, hch1, hx1⟩ := List.mem_flatten.1 hx
    obtain ⟨ch2, hch2, hy2⟩ := List.mem_flatten.1 hy
    obtain rfl := hF.fm.conn _ hch1 _ hch2 x hx1 y hy2 hov
    have hnd : ch1.Nodup := (List.nodup_flatten.1 hM.tree.nodup).1 _ hch1
    have hmem : ∀ v ∈ ch1, v ∈ G.chains.flatten := fun v hv => List.mem_flatten.2 ⟨_, hch1, hv⟩
    -- a slot of the chain with `x`'s object: `same_object_as` with `x`
    have hso : ∀ v ∈ ch1, v ≠ x → (okey (capV mem v) = okey (capV mem x)) →
        soB (capV mem v) (capV mem x) = true ∧ soB (capV mem x) (capV mem v) = true := by
      intro v _ _ hv
      exact ⟨soB_of_key hv (by rw [hv]; exact hkx), soB_of_key hv.symm hkx⟩
    -- `R`-related to a slot with `x`'s object, so with `x`'s object
    have hsr : ∀ u ∈ ch1, ∀ v ∈ ch1, u ≠ v → okey (capV mem u) = okey (capV mem x) → srM mem u v = true →
        okey (capV mem v) = okey (capV mem x) := by
      intro u hu v hv huv hku huvr
      by_cases hfu : isFrame (capV mem u) = true
      · exfalso; rw [isFrame_of_key hku, hN.nf] at hfu; cases hfu
      · rw [key_of_sr huvr (by rw [hku]; exact hkx) (by simpa using hfu), hku]
    obtain ⟨A, L, rfl⟩ := List.append_of_mem hx1
    have hxA := (Mdb.nodup_mid hnd).1
    have hxL := (Mdb.nodup_mid hnd).2
    rcases List.mem_append.1 hy2 with hyA | hyL'
    · -- `y` before `x`: `x`'s `prev` has the object
      obtain ⟨A', B, rfl⟩ := List.append_of_mem hyA
      have hch' : A' ++ y :: (B ++ x :: L) ∈ G.chains := by simpa using hch1
      have hca := ca_srM (Mdb.chunkL_ca (hI.chunk _ hch'))
        (Or.inl (by rw [isFrame_of_key hk.symm]; exact hN.nf))
      have hyx' : srM mem y x = true := by
        unfold srM; rw [sr_of_key hk.symm (by rw [← hk]; exact hkx)]
        exact hI.self y hy (by simpa using hzy)
      have hB := Mdb.ca_use hca hyx'
      rcases List.eq_nil_or_concat B with rfl | ⟨B', w, rfl⟩
      · have hpv : prevOf mem x = y := hM.prev_eq_pred (P := A') (by simpa using hch1)
        have := (hso y (by simp) hyx hk.symm).1
        simp only [finF, hpv, ne_eq, hslot y hy, not_false_eq_true, this, and_self, ↓reduceIte,
          Bool.false_eq_true] at hf
      · have hpv : prevOf mem x = w := hM.prev_eq_pred (P := A' ++ y :: B') (by simpa using hch1)
        have hw : w ∈ A' ++ y :: B'.concat w ++ x :: L := by simp
        have hwx : w ≠ x := fun e => hxA (by rw [← e]; simp)
        have hwy : y ≠ w := fun e => by
          subst e
          have := (Mdb.nodup_mid (A := A') (x := y) (B := B' ++ [y] ++ x :: L) (by simpa using hnd)).2
          exact this (by simp)
        have hkw := hsr y (by simp) w hw hwy hk.symm (hB w (by simp))
        have := (hso w hw hwx hkw).1
        simp only [finF, hpv, ne_eq, hslot w (hmem w hw), not_false_eq_true, this, and_self, ↓reduceIte,
          Bool.false_eq_true] at hf
    · -- `y` after `x`: `x`'s `next` has the object
      have hyL : y ∈ L := by
        rcases List.mem_cons.1 hyL' with h | h
        · exact absurd h hyx
        · exact h
      obtain ⟨B, C, rfl⟩ := List.append_of_mem hyL
      have hca := ca_srM (Mdb.chunkL_ca (hI.chunk _ hch1)) (Or.inl hN.nf)
      have hxy' : srM mem x y = true := by
        unfold srM; rw [sr_of_key hk hkx]
        exact hI.self x hx hz
      have hB := Mdb.ca_use hca hxy'
      have hnx := hM.next_eq_succ hch1
      have key2 : ∃ v ∈ B ++ y :: C, nextOf mem x = v ∧ okey (capV mem v) = okey (capV mem x) := by
        cases B with
        | nil => exact ⟨y, by simp, by simpa using hnx, hk.symm⟩
        | cons v B' =>
          refine ⟨v, by simp, by simpa using hnx, ?_⟩
          have hxv : x ≠ v := fun e => hxL (by rw [e]; simp)
          exact hsr x (by simp) v (by simp) hxv rfl (hB v (by simp))
      obtain ⟨v, hv, hnv, hkv⟩ := key2
      have hvx : v ≠ x := fun e => hxL (by rw [← e]; exact hv)
      have hvm : v ∈ G.chains.flatten := hmem v (by simp [hv])
      have := (hso v (by simp [hv]) hvx hkv).2
      have hn0 : nextOf mem x ≠ 0#u64 := by rw [hnv]; exact hslot v hvm
      unfold finF at hf
      split_ifs at hf with h1 h2 <;>
        first | exact hn0 ‹_› | (rw [hnv, this] at hf; simp at hf) | simp at hf
  · intro hno
    by_contra hf
    unfold finF at hf
    split_ifs at hf with h1 h2
    · obtain ⟨hp0, hpso⟩ := h1
      obtain ⟨hpm, hpn⟩ := hM.prev_link hx hp0
      have hpx : prevOf mem x ≠ x := by
        intro e
        rw [e] at hpn
        rcases hM.next_mem hx with h | ⟨-, h⟩
        · rw [hpn] at h; exact hslot x hx h
        · exact h hpn
      have hk := key_of_so hpso hN hz
      exact hno _ hpm hpx (ovl_of_key hk (by rw [hk]; exact hkx)).symm
    · simp at hf
    · have hn0 := h2
      have hso : soB (capV mem x) (capV mem (nextOf mem x)) = true := by simpa using hf
      rcases hM.next_mem hx with h | ⟨hnm, hnx⟩
      · exact h2 h
      have hk := key_of_so_left hso hN hz
      exact hno _ hnm hnx (ovl_of_key hk.symm hkx)

end

end

end Fl4Proofs.P3
