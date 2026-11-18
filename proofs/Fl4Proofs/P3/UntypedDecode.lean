/-
P3 (DESIGN.md §9), untyped: **`untyped::decode` against l4v
`decode_untyped_invocation`** (Fl4Spec/Decode.lean): the errors, and on
success the arguments `retype` gets.
-/
import Fl4Proofs.P3.UntypedSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The slots of a retype window, as the spec lists them. -/
def windowSlots (dest : U64) (r off win : Nat) : List Fl4Spec.CslotPtr :=
  (List.range' off win).map fun i => (dest.bv, Fl4Spec.natToCref r i)

/-- After `decode`, either FL4 returned the spec's error with nothing
changed, or the spec decodes an invocation and `Q` relates it to FL4's
result. -/
def UPost {A : Type} (σ : Fl4Spec.State Unit) (m : Fl4Spec.SEMonad Unit Fl4Spec.UntypedInvocation) (s : S) (ar : A)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e e', res = (.Err e, s, ar) ∧ m.run σ = ({(.error e', σ)}, False) ∧ SysErrRel e e') ∨
  (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ Q inv res)

theorem UPost.congr {A : Type} {σ : Fl4Spec.State Unit} {m m' : Fl4Spec.SEMonad Unit Fl4Spec.UntypedInvocation}
    (h : m.run σ = m'.run σ) {s : S} {ar : A} {Q} {prog : Result (core.result.Result Unit error.Exc × S × A)}
    (hp : prog ⦃ res => UPost σ m' s ar Q res ⦄) : prog ⦃ res => UPost σ m s ar Q res ⦄ := by
  refine WP.spec_mono hp ?_
  rintro res (⟨e, e', h1, h2, h3⟩ | ⟨inv, h2, h3⟩)
  · exact Or.inl ⟨e, e', h1, h.trans h2, h3⟩
  · exact Or.inr ⟨inv, h.trans h2, h3⟩

theorem UPost.err {A : Type} {σ : Fl4Spec.State Unit} {m : Fl4Spec.SEMonad Unit Fl4Spec.UntypedInvocation}
    {s : S} {ar : A} {Q} {e : error.Exc} {e' : Fl4Spec.SyscallError}
    (h : m.run σ = ({(.error e', σ)}, False)) (he : SysErrRel e e') :
    (ok ((.Err e, s, ar) : core.result.Result Unit error.Exc × S × A)) ⦃ res => UPost σ m s ar Q res ⦄ := by
  rw [WP.spec_ok]; exact Or.inl ⟨e, e', rfl, h, he⟩

theorem throw_run {α : Type} (e : Fl4Spec.SyscallError) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.NonDetE.throwError e : Fl4Spec.SEMonad Unit α).run σ = ({(.error e, σ)}, False) := rfl

theorem single_inj {α : Type} {σ : Fl4Spec.State Unit} {a b : α}
    (h : (({(a, σ)}, False) : Set (α × Fl4Spec.State Unit) × Prop) = ({(b, σ)}, False)) : a = b := by
  have := congrArg Prod.fst h
  simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq] at this
  exact this.1

/-- The spec's `ensure_empty` over a retype window, against FL4's slots. -/
theorem window_empty_run (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (hR : StateRel th (L.mem s) σ)
    (ptr : U64) (r : Nat) (hr : r < 64) (hth : th ptr = some (.cnode r)) (off win : Nat) (hw : off + win ≤ 2 ^ r) :
    (Fl4Spec.NonDetE.mapMEx (Fl4Spec.ensureEmpty (Z := Unit)) (windowSlots ptr r off win)).run σ =
      ({(if ∀ i : Nat, off ≤ i → i < off + win →
            capAt (L.mem s) (slotAddr ptr.bv (BitVec.ofNat 64 i)) = ok .Null
          then .ok () else .error .deleteFirst, σ)}, False) := by
  let capsOf : Fl4Spec.CslotPtr → Fl4Spec.Cap := fun sl =>
    if h : ∃ a, Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False) then h.choose else .nullCap
  have key : ∀ i, off ≤ i → i < off + win → ∃ c, capAt (L.mem s) (slotAddr ptr.bv (BitVec.ofNat 64 i)) = ok c ∧
      CapRel c (capsOf (ptr.bv, Fl4Spec.natToCref r i)) ∧
      Fl4Spec.getCap (Z := Unit) (ptr.bv, Fl4Spec.natToCref r i) σ = ({(capsOf (ptr.bv, Fl4Spec.natToCref r i), σ)}, False) := by
    intro i h1 h2
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (ptr.bv, Fl4Spec.natToCref r i)) (p := ptr) rfl
      (by rw [natToCref_length _ _ (by omega)]; exact hth)
    have hex : ∃ a, Fl4Spec.getCap (Z := Unit) (ptr.bv, Fl4Spec.natToCref r i) σ = ({(a, σ)}, False) := ⟨a, hg⟩
    have hcs : capsOf (ptr.bv, Fl4Spec.natToCref r i) = a := by
      simp only [capsOf, dif_pos hex]
      exact single_inj (hex.choose_spec.symm.trans hg)
    rw [hcs]
    refine ⟨c, ?_, hca, hg⟩
    rw [← cslotAddr_natToCref ptr.bv r i (by omega) (by omega)]; exact hc
  have hiff : (∀ sl ∈ windowSlots ptr r off win, capsOf sl = .nullCap) ↔
      (∀ i : Nat, off ≤ i → i < off + win → capAt (L.mem s) (slotAddr ptr.bv (BitVec.ofNat 64 i)) = ok .Null) := by
    simp only [windowSlots, List.mem_map, List.mem_range'_1, forall_exists_index, and_imp]
    constructor
    · intro h i h1 h2
      obtain ⟨c, hc, hca, -⟩ := key i h1 h2
      have := h _ i h1 h2 rfl
      rw [hc, (hca.null_iff).1 this]
    · rintro h _ i h1 h2 rfl
      obtain ⟨c, hc, hca, -⟩ := key i h1 h2
      rw [h i h1 h2, ok.injEq] at hc
      subst hc
      exact (hca.null_iff).2 rfl
  rw [mapMEx_ensureEmpty_run σ capsOf]
  · by_cases hb : ∀ i : Nat, off ≤ i → i < off + win → capAt (L.mem s) (slotAddr ptr.bv (BitVec.ofNat 64 i)) = ok .Null
    · rw [if_pos hb, if_pos (hiff.2 hb)]
    · rw [if_neg hb, if_neg (fun h => hb (hiff.1 h))]
  · simp only [windowSlots, List.mem_map, List.mem_range'_1, forall_exists_index, and_imp]
    rintro _ i h1 h2 rfl
    exact (key i h1 h2).choose_spec.2.2

/-- What `decode` has established when it calls `retype` (FL4 arguments:
type `nt`, size `us`, destination CNode `dest` of radix `r`, window
`off`..`off + win`, `reset`, the free index `fiv` it starts from). -/
structure RetCtx (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr)
    (sb fi : U64) (dev : Bool) (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat)
    (reset : Bool) (fiv : U64) : Prop where
  ty : objTypeOf nt.val = some t
  size : us.val < 64 ∧ zOf nt.val us.val ≤ 47 ∧ ¬ (nt.val = 4 ∧ us.val = 0) ∧ ¬ (nt.val = 0 ∧ us.val < 4) ∧
    ¬ (nt.val = 5 ∧ us.val < 7)
  cnode : th dest = some (.cnode r) ∧ r < 64 ∧ r ≠ 0
  window : 1 ≤ win.val ∧ win.val ≤ 256 ∧ off.val + win.val ≤ 2 ^ r
  empty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
    capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null
  resetEq : reset = decide (¬ ∃ x, σ.cdt x = some sl)
  fidx : fiv = if reset then 0#u64 else fi
  sizeBits : sb.val < 64
  memory : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fiv.bv).toNat >>> zOf nt.val us.val
  device : dev = true → Fl4Spec.isFrameType t = true ∨ t = .untyped

theorem ndE_exceptT_pure_bind {σ ε α β : Type} (a : α) (f : α → Fl4Spec.NonDetE σ ε β) :
    (ExceptT.pure a >>= f) = f a := ndE_pure_bind a f

theorem is_frame_type_eq (nt : U64) :
    objects.is_frame_type nt = ok (decide (nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11)) := by
  unfold objects.is_frame_type
  simp only [fl4_abi.consts.object.X86Page4K, fl4_abi.consts.object.X86LargePage,
    fl4_abi.consts.object.X64HugePage, u64_eq_iff]
  have h9 : (9#u64 : U64).val = 9 := rfl
  have h10 : (10#u64 : U64).val = 10 := rfl
  have h11 : (11#u64 : U64).val = 11 := rfl
  rw [h9, h10, h11]
  split_ifs <;> simp_all

/-- Simplify FL4's `?` on an error. -/
macro "fl4_break" : tactic => `(tactic| simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
  core.convert.FromSame.from, bind_tc_ok])

theorem untyped_decode_refines_with [Fl4Proofs.P1.PlainStore st] (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, args.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (hbits : ∀ (x : U64) t, args.head? = some x → objTypeOf x.val = some t → ∀ n, bitsApi t n = zOf x.val n)
    (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) (hsl : slot = cslotAddr sl) (hAs : AbsSlot th sl)
    (p sb fi : U64) (dev : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
      args.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar slot reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win
          dev) ⦃ res =>
        Q (.retype sl reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res ⦄) :
    untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.decodeUntypedInvocationWith bitsApi slbl (args.map UScalar.bv) sl (absCap (.Untyped p sb fi dev)) excaps)
        s ar Q res ⦄ := by
  rw [show absCap (.Untyped p sb fi dev) = .untypedCap dev p.bv sb.val fi.val from rfl]
  unfold untyped.decode Fl4Spec.decodeUntypedInvocationWith
  by_cases hl : lbl = fl4_abi.label.UntypedRetype
  swap
  · have : (lbl != fl4_abi.label.UntypedRetype) = true := by simpa using hl
    simp only [this, P1.plain_sharing, bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self, error.illegal]
    apply UPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation) _ trivial
    have : ¬ Fl4Spec.genInvocationType slbl = .untypedRetype := fun h => hl (hlbl.1 h)
    simp only [Fl4Spec.NonDetE.unlessE, this, ↓reduceIte]
    rw [show ∀ (f : Unit → Fl4Spec.SEMonad Unit Fl4Spec.UntypedInvocation),
      (Fl4Spec.NonDetE.throwError .illegalOperation >>= f) = Fl4Spec.NonDetE.throwError .illegalOperation from
      fun f => ndE_throw_bind _ f]
    rfl
  have hne : (lbl != fl4_abi.label.UntypedRetype) = false := by simpa using hl
  have hsl' : Fl4Spec.genInvocationType slbl = .untypedRetype := hlbl.2 hl
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDetE.unlessE, hsl', ndE_pure_bind]
  by_cases h6 : length < 6#u64
  · simp only [h6, ↓reduceIte, error.truncated, bind_ok]
    apply UPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ trivial
    have : (args.map UScalar.bv).length < 6 := by simp; scalar_tac
    simp only [Fl4Spec.NonDetE.whenE, this, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have h6' : ¬ (args.map UScalar.bv).length < 6 := by simp; scalar_tac
  simp only [h6, ↓reduceIte, Fl4Spec.NonDetE.whenE, h6', ndE_pure_bind, hx0, bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, -, c0, a0, rest0, hc0, hca0, hcv0, rfl⟩
  · simp only [↓reduceIte, error.truncated, bind_ok, decide_true]
    apply UPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ trivial
    simp only [List.length_nil, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.add_one_ne_zero,
    ndE_pure_bind, List.getElem?_cons_zero, Fl4Spec.the]
  obtain ⟨nt, us, idx, dep, off, win, rest, rfl⟩ : ∃ nt us idx dep off win rest,
      args = nt :: us :: idx :: dep :: off :: win :: rest := by
    match args with
    | nt :: us :: idx :: dep :: off :: win :: rest => exact ⟨nt, us, idx, dep, off, win, rest, rfl⟩
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => exfalso; simp at hlen; scalar_tac
  simp only [hct, hargs 0#u64 nt (by simp), hargs 1#u64 us (by simp), hargs 2#u64 idx (by simp),
    hargs 3#u64 dep (by simp), hargs 4#u64 off (by simp), hargs 5#u64 win (by simp), bind_ok,
    List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ, Fl4Spec.the]
  simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, Fl4Spec.dataToNat, Fl4Spec.unat, UScalar.bv_toNat]
  have hd := dataToObjType_run nt.bv σ
  have hnNative := hNative nt rfl
  have hcollapse (m k : Result (core.result.Result Unit error.Exc × S × A)) :
      (if nt ≥ 14#u64 then if nt < 19#u64 then m else k else k) = k := by
    by_cases hg : nt ≥ 14#u64
    · have hl : ¬ nt < 19#u64 := by scalar_tac
      simp only [hg, hl, ↓reduceIte]
    · simp only [hg, ↓reduceIte]
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.Count]
  rw [hcollapse]
  rw [retype_size_cases]
  simp only [bind_ok]
  by_cases h14 : nt.val ≥ 19
  · have hn : objTypeOf nt.bv.toNat = none := (objTypeOf_none _).2 (by simpa using h14)
    rw [hn] at hd
    simp only [h14, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok]
    exact UPost.err (run_bind_error hd _) (show (0 : Nat) = (0#u64 : U64).val from rfl)
  obtain ⟨t, ht⟩ : ∃ t, objTypeOf nt.val = some t := by
    cases h : objTypeOf nt.val with
    | none => exact absurd ((objTypeOf_none _).1 h) h14
    | some t => exact ⟨t, rfl⟩
  obtain ⟨-, -, hfr, hut, hct', hsc, -⟩ := objTypeOf_fl4 ht us.val
  have hz : bitsApi t us.val = zOf nt.val us.val := hbits nt t rfl ht us.val
  rw [UScalar.bv_toNat, ht] at hd
  simp only [h14, ↓reduceIte]
  refine UPost.congr (run_bind_ok hd _) ?_
  simp only [hz]
  by_cases hsA : us.val ≥ 64 ∨ zOf nt.val us.val > 47
  · rw [if_pos hsA]; fl4_break
    refine UPost.err (e' := .rangeError 0 (BitVec.ofNat 64 47)) ?_ ⟨rfl, rfl⟩
    have : ¬ (us.val < Fl4Spec.wordBits ∧ zOf nt.val us.val ≤ Fl4Spec.untypedMaxBits) := by
      simp only [Fl4Spec.wordBits, Fl4Spec.untypedMaxBits]; omega
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsA' : us.val < Fl4Spec.wordBits ∧ zOf nt.val us.val ≤ Fl4Spec.untypedMaxBits := by
    simp only [Fl4Spec.wordBits, Fl4Spec.untypedMaxBits]; omega
  simp only [hsA, hsA', and_self, ↓reduceIte, ndE_pure_bind]
  by_cases hsB : nt.val = 4 ∧ us.val = 0
  · rw [if_pos hsB]; fl4_break
    refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
    have : t = .capTableObject ∧ us.val = 0 := ⟨hct'.2 hsB.1, hsB.2⟩
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsB' : ¬ (t = .capTableObject ∧ us.val = 0) := fun h => hsB ⟨hct'.1 h.1, h.2⟩
  simp only [hsB, hsB', and_self, ↓reduceIte, ndE_pure_bind]
  by_cases hsC : nt.val = 0 ∧ us.val < 4
  · rw [if_pos hsC]; fl4_break
    refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
    have : t = .untyped ∧ us.val < Fl4Spec.untypedMinBits := ⟨hut.2 hsC.1, hsC.2⟩
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsC' : ¬ (t = .untyped ∧ us.val < Fl4Spec.untypedMinBits) := fun h => hsC ⟨hut.1 h.1, h.2⟩
  simp only [hsC, hsC', and_self, ↓reduceIte, ndE_pure_bind]
  by_cases hsD : nt.val = 5 ∧ us.val < 7
  · rw [if_pos hsD]; fl4_break
    refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
    have : t = .schedContextObject ∧ us.val < Fl4Spec.minSchedContextBits := ⟨hsc.2 hsD.1, hsD.2⟩
    simp only [this, and_self, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hsD' : ¬ (t = .schedContextObject ∧ us.val < Fl4Spec.minSchedContextBits) := fun h => hsD ⟨hsc.1 h.1, h.2⟩
  simp only [hsD, hsD', and_self, ↓reduceIte, ndE_pure_bind, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- the node cap
  have hnode : (∃ e e', untyped.retype_dest st s x0 idx dep off win = ok (.Err e) ∧
      (if dep.val = 0 then pure a0 else do
          let nodeSlot ← Fl4Spec.lookupTargetSlot a0 (Fl4Spec.dataToCptr idx.bv) dep.val
          Fl4Spec.NonDetE.liftE (Fl4Spec.getCap nodeSlot) : Fl4Spec.SEMonad Unit Fl4Spec.Cap).run σ =
        ({(.error e', σ)}, False) ∧ SysErrRel e e') ∨
      (∃ nc, CapWf nc ∧ CapValid th nc ∧ untyped.retype_dest st s x0 idx dep off win = ok (tailOf dep off win nc) ∧
      (if dep.val = 0 then pure a0 else do
          let nodeSlot ← Fl4Spec.lookupTargetSlot a0 (Fl4Spec.dataToCptr idx.bv) dep.val
          Fl4Spec.NonDetE.liftE (Fl4Spec.getCap nodeSlot) : Fl4Spec.SEMonad Unit Fl4Spec.Cap).run σ =
        ({(.ok (absCap nc), σ)}, False)) := by
    by_cases h0 : dep = 0#u64
    · subst h0
      refine Or.inr ⟨c0, hca0.1, hcv0, retype_dest_zero s x0 idx off win c0 hc0 hca0.1, ?_⟩
      simp only [show (0#u64 : U64).val = 0 from rfl, ↓reduceIte, ← hca0.abs]; rfl
    have h0' : dep.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq h)
    simp only [h0', ↓reduceIte]
    obtain ⟨r, hr, e1, he1, hrel⟩ := spec_exists
      (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false c0 a0 hca0 hcv0 idx dep)
    have hl' : cspace.lookup_target_slot st s c0 idx dep = ok r := hr
    have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) a0 (Fl4Spec.dataToCptr idx.bv) dep.val).run σ =
        ({(e1, σ)}, False) := he1
    cases r with
    | Err e =>
      cases e1 with
      | ok _ => exact hrel.elim
      | error e' =>
        exact Or.inl ⟨e, e', retype_dest_err s x0 idx dep off win h0 c0 hc0 e hl', run_bind_error hlt _, hrel⟩
    | Ok v =>
      cases e1 with
      | error _ => exact hrel.elim
      | ok sl' =>
        obtain ⟨rfl, pp, hpp1, hpp, -⟩ := hrel
        obtain ⟨c', a', hc', hca', hg⟩ := hR.slot_cap hpp1 hpp
        have hcv' : CapValid th c' := hV.abs ⟨pp, hpp1, Or.inl hpp⟩ hc'
        refine Or.inr ⟨c', hca'.1, hcv', retype_dest_ok s x0 idx dep off win h0 c0 hc0 _ hl' c' hc' hca'.1, ?_⟩
        rw [run_bind_ok hlt, run_liftE hg, ← hca'.abs]
  rcases hnode with ⟨e, e', hrd, hsn, hrel⟩ | ⟨nc, hncw, hncv, hrd, hsn⟩
  · rw [hrd]; fl4_break
    exact UPost.err (run_bind_error hsn _) hrel
  rw [hrd]
  refine UPost.congr (run_bind_ok hsn _) ?_
  simp only [bind_ok]
  by_cases hcn : ∃ ptr r gs g, nc = .CNode ptr r gs g
  swap
  · have ht' : tailOf dep off win nc = .Err (.Sys (.FailedLookup false (.MissingCapability dep))) := by
      cases nc <;> first | rfl | exact absurd ⟨_, _, _, _, rfl⟩ hcn
    have hi : Fl4Spec.isCnodeCap (absCap nc) = false := by
      cases nc <;> first | rfl | exact absurd ⟨_, _, _, _, rfl⟩ hcn
    rw [ht']; fl4_break
    refine UPost.err (e' := .failedLookup false (.missingCapability dep.val)) ?_ ⟨rfl, rfl⟩
    simp only [hi, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  obtain ⟨ptr, r, gs, g, rfl⟩ := hcn
  have hr64 : r.val < 64 := hncw.1
  obtain ⟨hthp, hr0⟩ := hncv
  have hpow : 2 ^ r.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
  have hpow1 : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
  rw [show absCap (.CNode ptr r gs g) = .cnodeCap ptr.bv r.val (bitsOf g.val gs.val) from rfl]
  simp only [Fl4Spec.isCnodeCap, ↓reduceIte, Fl4Spec.bitsOf, Fl4Spec.objRefOf, tailOf, destRes, ndE_pure_bind,
    hfan]
  by_cases e1 : off.val > 2 ^ r.val - 1
  · rw [if_pos e1]; fl4_break
    refine UPost.err (e' := .rangeError 0 (BitVec.ofNat 64 (2 ^ r.val - 1))) ?_ ⟨rfl, rfl⟩
    simp only [e1, or_true, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have e1' : ¬ (off.val < 0 ∨ off.val > 2 ^ r.val - 1) := by omega
  simp only [e1', ↓reduceIte, ndE_pure_bind]; rw [if_neg e1]
  have h256 : Fl4Spec.unat (256#64 : BitVec 64) = 256 := rfl
  by_cases e2 : win.val < 1 ∨ win.val > 256
  · rw [if_pos e2]; fl4_break
    refine UPost.err (e' := .rangeError 1 256#64) ?_ ⟨rfl, rfl⟩
    simp only [h256, e2, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [h256, e2, ↓reduceIte, ndE_pure_bind]
  by_cases e3 : win.val > 2 ^ r.val - off.val
  · rw [if_pos e3]; fl4_break
    refine UPost.err (e' := .rangeError 1 (BitVec.ofNat 64 (2 ^ r.val - off.val))) ?_ ⟨rfl, rfl⟩
    simp only [e3, or_true, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have e3' : ¬ (win.val < 1 ∨ win.val > 2 ^ r.val - off.val) := by omega
  simp only [e3', ↓reduceIte, ndE_pure_bind]; rw [if_neg e3]; simp only [bind_ok]
  -- the window is empty
  have hw1 : 1 ≤ win.val ∧ win.val ≤ 256 := by omega
  have hwin : off.val + win.val ≤ 2 ^ r.val := by omega
  have hsum : (core.num.U64.wrapping_add off win).val = off.val + win.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  simp only [lift, bind_ok]
  simp only [ensure_empty_slots_eq s ptr off _ (show off.val ≤ (core.num.U64.wrapping_add off win).val by omega), hsum,
    bind_ok]
  have hsl2 : List.map (fun cref => (ptr.bv, cref)) (List.map (Fl4Spec.natToCref r.val)
      (List.range' off.val (off.val + win.val - off.val))) = windowSlots ptr r.val off.val win.val := by
    simp [windowSlots, List.map_map]
  simp only [hsl2]
  have hwe := window_empty_run th s σ hR ptr r.val hr64 hthp off.val win.val hwin
  by_cases hemp : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr ptr.bv (BitVec.ofNat 64 i)) = ok .Null
  swap
  · rw [if_neg hemp] at hwe; simp only [hemp, ↓reduceIte]; fl4_break
    exact UPost.err (run_bind_error hwe _) trivial
  rw [if_pos hemp] at hwe; rw [if_pos hemp]
  refine UPost.congr (run_bind_ok hwe _) ?_
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, untyped.as_untyped]
  -- reset: no children
  have hnc : NoChildrenRel (st := st) s σ slot sl := by
    subst hsl
    exact noChildren_of_adj th hP s σ G hM hC (hI.parentAdj (th := th)) sl hAs
      ((hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩)
  unfold NoChildrenRel at hnc
  have hres := constOnFailure_run σ sl
  simp only [Fl4Spec.NonDetE.returnOk] at hres
  refine UPost.congr (run_bind_ok (run_liftE hres) _) ?_
  rw [hnc]; simp only [bind_ok]
  by_cases hch : ∃ x, σ.cdt x = some sl
  case' pos =>
    rw [if_pos hch]; dsimp only
    rw [show ((fi, false) : U64 × Bool) = (if (∃ x, σ.cdt x = some sl) then fi else 0#u64,
      decide (¬ ∃ x, σ.cdt x = some sl)) by simp [hch]]
  case' neg =>
    rw [if_neg hch]; dsimp only
    rw [show ((0#u64, true) : U64 × Bool) = (if (∃ x, σ.cdt x = some sl) then fi else 0#u64,
      decide (¬ ∃ x, σ.cdt x = some sl)) by simp [hch]]
  all_goals clear hch
  all_goals
    generalize hRv : decide (¬ ∃ x, σ.cdt x = some sl) = R
    obtain ⟨fiv, hfiv⟩ : ∃ fiv, fiv = (if (∃ x, σ.cdt x = some sl) then fi else 0#u64) := ⟨_, rfl⟩
    rw [← hfiv]
    have hfiv' : fiv = if R then 0#u64 else fi := by
      rw [hfiv, ← hRv]; by_cases h : ∃ x, σ.cdt x = some sl <;> simp [h]
    clear hfiv
    simp only [bind_ok, uncurry_apply_pair]
    have hsb : sb.val < 64 := capAt_untyped_inv hcap
    have hfivv : fiv.val = if R then 0 else fi.val := by rw [hfiv']; cases R <;> rfl
    have hspec_fi : (if R = true then 0 else Fl4Spec.freeIndexOf (Fl4Spec.Cap.untypedCap dev p.bv sb.val fi.val)) =
        fiv.val := by rw [hfivv]; cases R <;> rfl
    have hfb : BitVec.ofNat 64 fiv.val = fiv.bv := (bv_eq_ofNat fiv).symm
    simp only [hspec_fi, objSize_untyped, Fl4Spec.getFreeRef, hfb]
    have h63 : (sb &&& 63#u64).val = sb.val := by
      have : (sb &&& 63#u64).val = sb.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod sb.val 6
      omega
    have hz47 : zOf nt.val us.val ≤ 47 := by omega
    have hzv : (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val = zOf nt.val us.val := by
      show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat = _
      simp; omega
    have hz63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
      have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
          (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
        simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
      omega
    step as ⟨i2, hi2a, hi2b⟩
    have hp64 : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
    have hi2v : i2.val = 2 ^ sb.val := by
      rw [hi2a, h63, Nat.one_shiftLeft]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hi2 : i2.bv = 1#64 <<< sb.val := by
      apply BitVec.eq_of_toNat_eq
      show i2.val = _
      rw [hi2v]; simp [Nat.shiftLeft_eq]; omega
    step as ⟨i4, hi4a, hi4b⟩
    have hFB : (core.num.U64.wrapping_sub i2 fiv).bv = 1#64 <<< sb.val - fiv.bv := by
      rw [core.num.U64.wrapping_sub_bv_eq, hi2]
    have hi4 : i4.val = (1#64 <<< sb.val - fiv.bv).toNat >>> zOf nt.val us.val := by
      first | (rw [hi4b, hz63, ← hFB]; rfl) | (rw [hi4a, hz63, ← hFB]; rfl)
    by_cases hm : i4 < win
    · rw [if_pos hm]
      refine UPost.err (e' := .notEnoughMemory (1#64 <<< sb.val - fiv.bv)) ?_ hFB.symm
      have : ((1#64 <<< sb.val - fiv.bv) >>> zOf nt.val us.val).toNat < win.val := by
        simp only [BitVec.toNat_ushiftRight]; rw [← hi4]; exact hm
      simp only [this, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
    rw [if_neg hm]
    have hm' : ¬ ((1#64 <<< sb.val - fiv.bv) >>> zOf nt.val us.val).toNat < win.val := by
      simp only [BitVec.toNat_ushiftRight]; rw [← hi4]; exact hm
    simp only [hm', ↓reduceIte, ndE_pure_bind]
    have h64 : ¬ (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) ≥ 64#u64 := by
      intro h; have : (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val ≥ 64 := h; omega
    rw [if_neg h64]
    have hal : untyped.align_up (core.num.U64.wrapping_add p fiv) ⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ =
        ok ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ := by
      rw [align_up_eq _ _ (by omega), hzv, core.num.U64.wrapping_add_bv_eq]
    have hctx : ∀ (hdev : dev = true → Fl4Spec.isFrameType t = true ∨ t = .untyped),
        RetCtx (L := L) th s σ sl sb fi dev nt us ptr off win t r.val R fiv :=
      fun hdev => ⟨ht, ⟨by omega, hz47, hsB, hsC, hsD⟩, ⟨hthp, hr64, hr0⟩, ⟨hw1.1, hw1.2, hwin⟩, hemp,
        hRv.symm, hfiv', hsb, by rw [← hi4]; have : ¬ i4.val < win.val := hm; omega, hdev⟩
    have hsucc : ∀ (hdev : dev = true → Fl4Spec.isFrameType t = true ∨ t = .untyped),
        (do
          let aligned ← untyped.align_up (core.num.U64.wrapping_add p fiv) ⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩
          let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
          untyped.retype st arI s2 ar slot R aligned nt us ptr off win dev) ⦃ res =>
        UPost σ (pure (Fl4Spec.UntypedInvocation.retype sl R p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
          t us.val (windowSlots ptr r.val off.val win.val) dev)) s ar Q res ⦄ := by
      intro hdev
      rw [hal, bind_ok]
      exact WP.spec_mono (hQ nt us ptr off win t r.val R fiv rfl (hctx hdev)) (fun res h => Or.inr ⟨_, rfl, h⟩)
    simp only [ndE_exceptT_pure_bind]
    cases dev
    · rw [if_neg (by simp)]
      refine UPost.congr ?_ (hsucc (by simp))
      simp only [Bool.false_eq_true, false_and, ↓reduceIte, ndE_exceptT_pure_bind]; rfl
    rw [if_pos rfl, is_frame_type_eq, bind_ok]
    by_cases hfrm : nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11
    · rw [if_pos (by simpa using hfrm)]
      refine UPost.congr ?_ (hsucc (fun _ => Or.inl (hfr.2 hfrm)))
      simp only [hfr.2 hfrm, not_true_eq_false, false_and, and_false, ↓reduceIte, ndE_exceptT_pure_bind]; rfl
    rw [if_neg (by simpa using hfrm)]
    have hnf : ¬ Fl4Spec.isFrameType t = true := fun h => hfrm (hfr.1 h)
    by_cases hu : nt.val = 0
    · have : (nt != fl4_abi.consts.object.Untyped) = false := by
        simp only [fl4_abi.consts.object.Untyped, bne_eq_false_iff_eq]; exact UScalar.eq_of_val_eq hu
      rw [this, if_neg (by simp)]
      refine UPost.congr ?_ (hsucc (fun _ => Or.inr (hut.2 hu)))
      simp only [hut.2 hu, ne_eq, not_true_eq_false, and_false, ↓reduceIte, ndE_exceptT_pure_bind]; rfl
    · have : (nt != fl4_abi.consts.object.Untyped) = true := by
        simp only [fl4_abi.consts.object.Untyped, bne_iff_ne, ne_eq]
        intro h; exact hu (by rw [h]; rfl)
      rw [this, if_pos rfl]
      simp only [error.invalid_arg, bind_ok]
      refine UPost.err (e := .Sys (.InvalidArgument 1#u64)) (e' := .invalidArgument 1) ?_ rfl
      have : ¬ t = .untyped := fun h => hu (hut.1 h)
      simp only [hnf, this, ne_eq, true_and, Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte,
        Fl4Spec.NonDetE.throwError, ndE_throw_bind]
      rfl


/-- **FL4's `untyped::decode` refines l4v `decode_untyped_invocation`** for
native types except the TCB (whose size FL4 changes, Fl4Spec/Ext/TcbSize.lean). -/
theorem untyped_decode_refines [Fl4Proofs.P1.PlainStore st] {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, args.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (hntcb : ∀ x, args.head? = some x → x.val ≠ 1)
    (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) (hsl : slot = cslotAddr sl) (hAs : AbsSlot th sl)
    (p sb fi : U64) (dev : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
      args.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar slot reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win
          dev) ⦃ res =>
        Q (.retype sl reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res ⦄) :
    untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.decodeUntypedInvocation slbl (args.map UScalar.bv) sl (absCap (.Untyped p sb fi dev)) excaps)
        s ar Q res ⦄ :=
  untyped_decode_refines_with Fl4Spec.objBitsApi arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen hargs
    hNative (fun x t hx ht n => (objTypeOf_some ht (hntcb x hx) n).2.1) slot sl hsl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan Q hQ

/-- **FL4's `untyped::decode` refines FL4's `decode_untyped_invocation`**
(the spec's with 4 KiB TCBs, Fl4Spec/Ext/TcbSize.lean), for native types. -/
theorem untyped_decode_refines_fl4 [Fl4Proofs.P1.PlainStore st] {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, args.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) (hsl : slot = cslotAddr sl) (hAs : AbsSlot th sl)
    (p sb fi : U64) (dev : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
      args.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar slot reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win
          dev) ⦃ res =>
        Q (.retype sl reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res ⦄) :
    untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocation slbl (args.map UScalar.bv) sl (absCap (.Untyped p sb fi dev)) excaps)
        s ar Q res ⦄ :=
  untyped_decode_refines_with Fl4Spec.fl4ObjBitsApi arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen hargs
    hNative (fun _ _ _ ht n => (objTypeOf_fl4 ht n).2.1) slot sl hsl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan Q hQ
end
end
end Fl4Proofs.P3
